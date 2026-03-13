import AST.AST
import Semantics.SymbolTable

/-
  Type-checking pass for Chapter 11.

  This pass walks the AST (after VarResolution) and:
    1. Infers the type of every expression.
    2. Inserts explicit `Cast` nodes for all implicit widening and narrowing
       conversions that C mandates:
         - In a binary operation with mixed Int/Long operands, the narrower
           operand is widened to Long (usual arithmetic conversions).
         - In an assignment `x = expr`, the RHS is cast to the type of `x`.
         - In a function call, each argument is cast to the declared param type.
         - In a `return` statement, the expression is cast to the function's
           declared return type.
    3. Does NOT rename variables (VarResolution already did that).
    4. Does NOT validate linkage or scope (VarResolution already did that).

  After this pass every Binary node has operands of the same type, every
  Assignment has a correctly-typed RHS, and every Return has a correctly-typed
  expression.  The type of each AST expression can be computed deterministically
  from the AST structure and the symbol table.
-/

namespace Semantics

-- ---------------------------------------------------------------------------
-- Type helpers
-- ---------------------------------------------------------------------------

/-- Return the common type for a binary operation (C "usual arithmetic conversions").
    Chapter 13: `Double` is a floating-point type and outranks all integer types.
    Chapter 12: extends to 4 types (Int, Long, UInt, ULong).
    Rules (C §6.3.1.8):
      0. Double beats all integer types.  (Ch13)
      1. Same type → that type.
      2. Both signed or both unsigned → wider type.
         Int  + Long  → Long;   UInt + ULong → ULong.
      3. Same rank, mixed sign → unsigned wins.
         Int  + UInt  → UInt;   Long + ULong → ULong.
      4. Unsigned rank > signed rank → unsigned wins.
         Int  + ULong → ULong;  UInt + Long  is handled by rule 5.
      5. Signed rank > unsigned rank AND signed can represent all unsigned values → signed.
         UInt + Long  → Long (Long can represent all UInt values [0, 2^32−1]).
      (Rule 6, converting both to unsigned of the signed type, is not reachable here.) -/
private def commonType (t1 t2 : AST.Typ) : AST.Typ :=
  -- Chapter 13: Double outranks all integer types
  if t1 == .Double || t2 == .Double then .Double
  else if t1 == t2 then t1
  -- Same rank, mixed signedness: unsigned wins
  else if (t1 == .Int && t2 == .UInt) || (t1 == .UInt && t2 == .Int) then .UInt
  else if (t1 == .Long && t2 == .ULong) || (t1 == .ULong && t2 == .Long) then .ULong
  -- ULong is the widest integer type; wins over everything else
  else if t1 == .ULong || t2 == .ULong then .ULong
  -- Long beats Int and UInt (Long can represent all UInt values)
  else if t1 == .Long || t2 == .Long then .Long
  -- Remaining: Int + UInt handled above; shouldn't be reached
  else t1

/-- Wrap `e` in a `Cast` node only when the target type differs from `current`. -/
private def castTo (target : AST.Typ) (current : AST.Typ) (e : AST.Exp) : AST.Exp :=
  if target == current then e else .Cast target e

/-- Truncate an integer value `n` to the signed 32-bit range [−2^31, 2^31−1].
    Used when a `case` constant appears in an `int`-controlled switch. -/
private def truncToInt32 (n : Int) : Int :=
  let modulus : Int := 4294967296  -- 2^32
  let r := n % modulus
  if r >= 2147483648 then r - modulus
  else if r < -2147483648 then r + modulus
  else r

/-- Truncate an integer value `n` to the unsigned 32-bit range [0, 2^32−1].
    Used when a `case` constant appears in an `unsigned int`-controlled switch. -/
private def truncToUInt32 (n : Int) : Int :=
  let modulus : Int := 4294967296  -- 2^32
  let r := n % modulus
  if r < 0 then r + modulus else r

-- truncateSwitchCases and truncateSwitchCasesItem are mutually recursive:
-- truncateSwitchCases calls truncateSwitchCasesItem for Compound items,
-- and truncateSwitchCasesItem calls truncateSwitchCases for Statement items.
mutual

/-- Walk a statement and apply `truncFn` to every `Case` value within this switch level.
    Stops recursing into nested `Switch` statements (their cases belong to them). -/
private partial def truncateSwitchCases (truncFn : Int → Int) : AST.Statement → AST.Statement
  | .Case n body lbl    => .Case (truncFn n) body lbl
  | .Default body lbl   => .Default body lbl
  | .Compound items     => .Compound (items.map (truncateSwitchCasesItem truncFn))
  | .If cond t eOpt     => .If cond (truncateSwitchCases truncFn t) (eOpt.map (truncateSwitchCases truncFn))
  | .While cond b lbl   => .While cond (truncateSwitchCases truncFn b) lbl
  | .DoWhile b cond lbl => .DoWhile (truncateSwitchCases truncFn b) cond lbl
  | .For init c p b lbl => .For init c p (truncateSwitchCases truncFn b) lbl
  | .Labeled lbl s      => .Labeled lbl (truncateSwitchCases truncFn s)
  -- Nested switch: stop — its cases belong to that inner switch
  | s@(.Switch ..)      => s
  | s                   => s

private partial def truncateSwitchCasesItem (truncFn : Int → Int) : AST.BlockItem → AST.BlockItem
  | .S s => .S (truncateSwitchCases truncFn s)
  | item => item

end

-- ---------------------------------------------------------------------------
-- Type-checking monad
-- ---------------------------------------------------------------------------

/-- The symbol table is read-only in this pass; use a plain `Except` for errors
    and thread the symbol table as a parameter rather than through state. -/
private abbrev TcM := Except String

-- ---------------------------------------------------------------------------
-- Expression type inference and cast insertion
-- ---------------------------------------------------------------------------

/-- The return type of `typeCheckExp`: the rewritten expression plus its type. -/
private abbrev TcResult := TcM (AST.Exp × AST.Typ)

/-- Look up the declared type of a variable or function from the symbol table.
    Variables → `Obj(typ)` → return typ.
    Functions → use retTyp for calls. -/
private def lookupVarTyp (st : SymbolTable) (name : String) : TcM AST.Typ :=
  match lookupSym st name with
  | some { type := .Obj t, .. } => return t
  | some { type := .Fun _ _ _, .. } => throw s!"'{name}' is a function, not a variable"
  | none => throw s!"Undeclared identifier '{name}' in TypeCheck"

/-- Infer the type of an expression and insert implicit casts where needed.
    Returns the (possibly rewritten) expression and its type. -/
private def typeCheckExp (st : SymbolTable) : AST.Exp → TcResult
  -- Typed constants: preserve the constant's declared type
  | .Constant (.ConstInt n)    => return (.Constant (.ConstInt n),    .Int)
  | .Constant (.ConstLong n)   => return (.Constant (.ConstLong n),   .Long)
  | .Constant (.ConstUInt n)   => return (.Constant (.ConstUInt n),   .UInt)    -- Chapter 12
  | .Constant (.ConstULong n)  => return (.Constant (.ConstULong n),  .ULong)   -- Chapter 12
  | .Constant (.ConstDouble f) => return (.Constant (.ConstDouble f), .Double)  -- Chapter 13
  -- Variable reference: look up type
  | .Var v => do
      let t ← lookupVarTyp st v
      return (.Var v, t)
  -- Explicit cast: type-check inner, wrap in Cast (always, for code-gen clarity)
  | .Cast targetTyp inner => do
      let (inner', _innerTyp) ← typeCheckExp st inner
      return (.Cast targetTyp inner', targetTyp)
  -- Unary operators: the result type matches the operand type.
  -- Exception: logical NOT (!) always produces Int regardless of operand type.
  -- Chapter 13: bitwise complement (~) is not valid on Double.
  | .Unary .Not inner => do
      let (inner', _) ← typeCheckExp st inner
      -- Logical NOT always produces int (0 or 1)
      return (.Unary .Not inner', .Int)
  | .Unary .Complement inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- C §6.5.3.3: ~ requires integer operand; doubles are not allowed
      if innerTyp == .Double then
        throw s!"TypeCheck: bitwise complement (~) is not valid on a double"
      return (.Unary .Complement inner', innerTyp)
  | .Unary op inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      return (.Unary op inner', innerTyp)
  -- Binary operators: apply usual arithmetic conversions
  -- Exception: shift operators (<<, >>) use only the left operand's type.
  -- C §6.5.7: "The type of the result is that of the promoted left operand."
  -- The right operand is NOT subject to usual arithmetic conversions; the
  -- shift amount can have any integer type without affecting the result type.
  -- Chapter 13: shifts and bitwise ops (& | ^ %) are not valid on Double.
  | .Binary .ShiftLeft left right => do
      let (left',  leftTyp)  ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      if leftTyp == .Double then
        throw s!"TypeCheck: left operand of shift (<<) cannot be double"
      if rightTyp == .Double then
        throw s!"TypeCheck: right operand of shift (<<) cannot be double"
      return (.Binary .ShiftLeft left' right', leftTyp)
  | .Binary .ShiftRight left right => do
      let (left',  leftTyp)  ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      if leftTyp == .Double then
        throw s!"TypeCheck: left operand of shift (>>) cannot be double"
      if rightTyp == .Double then
        throw s!"TypeCheck: right operand of shift (>>) cannot be double"
      return (.Binary .ShiftRight left' right', leftTyp)
  -- Chapter 13: logical AND/OR — each operand is tested for truthiness
  -- independently; do NOT apply usual arithmetic conversions between them.
  -- The result is always Int (0 or 1).
  | .Binary .And left right => do
      let (left', _)  ← typeCheckExp st left
      let (right', _) ← typeCheckExp st right
      return (.Binary .And left' right', .Int)
  | .Binary .Or left right => do
      let (left', _)  ← typeCheckExp st left
      let (right', _) ← typeCheckExp st right
      return (.Binary .Or left' right', .Int)
  | .Binary op left right => do
      let (left', leftTyp)   ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      -- Usual arithmetic conversions: widen the narrower operand
      let common := commonType leftTyp rightTyp
      -- Chapter 13: reject bitwise operations and modulo on Double operands.
      -- These operations require integer types (C §6.5.10, §6.5.11, §6.5.12, §6.5.5).
      match op with
      | .Remainder =>
          if common == .Double then
            throw s!"TypeCheck: modulo (%) is not valid on double operands"
      | .BitAnd =>
          if common == .Double then
            throw s!"TypeCheck: bitwise AND (&) is not valid on double operands"
      | .BitOr =>
          if common == .Double then
            throw s!"TypeCheck: bitwise OR (|) is not valid on double operands"
      | .BitXor =>
          if common == .Double then
            throw s!"TypeCheck: bitwise XOR (^) is not valid on double operands"
      | _ => pure ()
      let left''  := castTo common leftTyp  left'
      let right'' := castTo common rightTyp right'
      -- Relational and equality operators always produce Int
      let resultTyp := match op with
        | .Equal | .NotEqual | .LessThan | .LessOrEqual
        | .GreaterThan | .GreaterOrEqual => .Int
        | _ => common
      return (.Binary op left'' right'', resultTyp)
  -- Assignment: RHS is cast to the type of the LHS variable
  | .Assignment (.Var lhsName) rhs => do
      let lhsTyp ← lookupVarTyp st lhsName
      let (rhs', rhsTyp) ← typeCheckExp st rhs
      let rhs'' := castTo lhsTyp rhsTyp rhs'
      return (.Assignment (.Var lhsName) rhs'', lhsTyp)
  | .Assignment lhs _ =>
      throw s!"TypeCheck: invalid lvalue in assignment (should have been caught by VarResolution)"
  -- Conditional: both branches are widened to the common type
  | .Conditional cond e1 e2 => do
      let (cond', _)    ← typeCheckExp st cond
      let (e1', t1)     ← typeCheckExp st e1
      let (e2', t2)     ← typeCheckExp st e2
      let common := commonType t1 t2
      let e1'' := castTo common t1 e1'
      let e2'' := castTo common t2 e2'
      return (.Conditional cond' e1'' e2'', common)
  -- Postfix increment/decrement: type of the variable
  | .PostfixIncr (.Var v) => do
      let t ← lookupVarTyp st v
      return (.PostfixIncr (.Var v), t)
  | .PostfixDecr (.Var v) => do
      let t ← lookupVarTyp st v
      return (.PostfixDecr (.Var v), t)
  | .PostfixIncr e | .PostfixDecr e =>
      throw s!"TypeCheck: invalid lvalue in postfix operator"
  -- Function call: cast each argument to the declared parameter type
  | .FunCall fname args => do
      match lookupSym st fname with
      | none => throw s!"Undeclared function '{fname}'"
      | some { type := .Obj _, .. } => throw s!"'{fname}' is a variable, not a function"
      | some { type := .Fun _ paramTypes retTyp, .. } => do
          -- Type-check each argument and cast to the corresponding param type
          let typedArgs ← args.mapM (typeCheckExp st)
          let castedArgs := (typedArgs.zip paramTypes).map fun ((arg, argTyp), paramTyp) =>
            castTo paramTyp argTyp arg
          -- Handle variadic-style (fewer params than args shouldn't happen after VarResolution)
          -- For extra args beyond paramTypes (shouldn't occur), keep as-is
          let allArgs := castedArgs ++ (typedArgs.drop paramTypes.length).map (·.1)
          return (.FunCall fname allArgs, retTyp)

-- ---------------------------------------------------------------------------
-- Statement type-checking
-- ---------------------------------------------------------------------------

/-
  `typeCheckStmt`, `typeCheckForInit`, and `typeCheckBlockItem` are mutually
  recursive: `Compound` statements contain block items (`typeCheckBlockItem`),
  which may themselves be statements (`typeCheckStmt`), and `For` statements
  contain a for-init (`typeCheckForInit`).  We put all three in a `mutual`
  block so Lean accepts the forward references.
-/
mutual

/-- Type-check a statement, threading the current function's return type for
    `return` statements. -/
private partial def typeCheckStmt (st : SymbolTable) (retTyp : AST.Typ) : AST.Statement → TcM AST.Statement
  | .Return e => do
      let (e', eTyp) ← typeCheckExp st e
      -- Cast return value to the function's declared return type
      let e'' := castTo retTyp eTyp e'
      return .Return e''
  | .Expression e => do
      let (e', _) ← typeCheckExp st e
      return .Expression e'
  | .If cond thenStmt elseOpt => do
      let (cond', _) ← typeCheckExp st cond
      let then' ← typeCheckStmt st retTyp thenStmt
      let else' ← elseOpt.mapM (typeCheckStmt st retTyp)
      return .If cond' then' else'
  | .Compound items => do
      let items' ← items.mapM (typeCheckBlockItem st retTyp)
      return .Compound items'
  | .While cond body lbl => do
      let (cond', _) ← typeCheckExp st cond
      let body' ← typeCheckStmt st retTyp body
      return .While cond' body' lbl
  | .DoWhile body cond lbl => do
      let body' ← typeCheckStmt st retTyp body
      let (cond', _) ← typeCheckExp st cond
      return .DoWhile body' cond' lbl
  | .For init cond post body lbl => do
      let init' ← typeCheckForInit st init
      let cond' ← cond.mapM (fun e => do let (e', _) ← typeCheckExp st e; return e')
      let post' ← post.mapM (fun e => do let (e', _) ← typeCheckExp st e; return e')
      let body' ← typeCheckStmt st retTyp body
      return .For init' cond' post' body' lbl
  | .Break lbl    => return .Break lbl
  | .Continue lbl => return .Continue lbl
  | .Switch exp body lbl cases => do
      let (exp', expTyp) ← typeCheckExp st exp
      -- C §6.8.4.2: the controlling expression must have integer type.
      -- Double is not a valid switch controlling expression type.
      if expTyp == .Double then
        throw s!"TypeCheck: switch controlling expression must have integer type, not double"
      let body' ← typeCheckStmt st retTyp body
      -- C §6.8.4.2: if the switch controlling expression has 32-bit type,
      -- truncate each case constant to that type's range.
      --   Int  switch → truncate to signed   int32 range.
      --   UInt switch → truncate to unsigned uint32 range.
      -- This must run BEFORE SwitchCollection validates for duplicates.
      let body'' := match expTyp with
        | .Int  => truncateSwitchCases truncToInt32  body'
        | .UInt => truncateSwitchCases truncToUInt32 body'
        | _     => body'   -- Long/ULong: no truncation needed
      return .Switch exp' body'' lbl cases
  | .Case n body lbl => do
      let body' ← typeCheckStmt st retTyp body
      return .Case n body' lbl
  | .Default body lbl => do
      let body' ← typeCheckStmt st retTyp body
      return .Default body' lbl
  | .Labeled lbl stmt => do
      let stmt' ← typeCheckStmt st retTyp stmt
      return .Labeled lbl stmt'
  | .Goto lbl => return .Goto lbl
  | .Null     => return .Null

/-- Type-check a `for` initializer: cast the initializer expression (if any)
    to match the declared variable type. -/
private partial def typeCheckForInit (st : SymbolTable) : AST.ForInit → TcM AST.ForInit
  | .InitExp eOpt => do
      let eOpt' ← eOpt.mapM (fun e => do let (e', _) ← typeCheckExp st e; return e')
      return .InitExp eOpt'
  | .InitDecl decl => do
      let init' ← decl.init.mapM fun e => do
        let (e', eTyp) ← typeCheckExp st e
        return castTo decl.typ eTyp e'
      return .InitDecl { decl with init := init' }

/-- Type-check a block item: statements are recursed into; declaration
    initializers are cast to match the declared variable type; local function
    declarations are passed through unchanged. -/
private partial def typeCheckBlockItem (st : SymbolTable) (retTyp : AST.Typ) : AST.BlockItem → TcM AST.BlockItem
  | .S stmt => do
      let stmt' ← typeCheckStmt st retTyp stmt
      return .S stmt'
  | .D decl => do
      -- Type-check/cast the initializer to match the variable's declared type
      let init' ← decl.init.mapM fun e => do
        let (e', eTyp) ← typeCheckExp st e
        return castTo decl.typ eTyp e'
      return .D { decl with init := init' }
  | .FD fd => return .FD fd   -- local function declarations need no type-checking here

end

-- ---------------------------------------------------------------------------
-- Top-level type-checking
-- ---------------------------------------------------------------------------

/-- Type-check a function definition: type-check the body with the function's
    return type so that `return` statements are correctly cast. -/
private def typeCheckFunctionDef (st : SymbolTable) (f : AST.FunctionDef) : TcM AST.FunctionDef := do
  let body' ← f.body.mapM (typeCheckBlockItem st f.retTyp)
  return { f with body := body' }

/-- Entry point for the type-checking pass.
    Walks all top-level function definitions; variable declarations at file scope
    are checked (initializer cast) but otherwise unchanged. -/
def typeCheckProgram (p : AST.Program) (st : SymbolTable) : Except String AST.Program := do
  let topLevels' ← p.topLevels.mapM fun tl =>
    match tl with
    | .FunDef fd  => do
        let fd' ← typeCheckFunctionDef st fd
        return .FunDef fd'
    | .VarDecl decl => do
        -- Type-check the file-scope initializer if present
        let init' ← decl.init.mapM fun e => do
          let (e', eTyp) ← typeCheckExp st e
          return castTo decl.typ eTyp e'
        return .VarDecl { decl with init := init' }
    | other => return other
  return { p with topLevels := topLevels' }

end Semantics
