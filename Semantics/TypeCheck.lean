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

/-- Return true iff `e` is an integer null pointer constant (integer constant with value 0).
    In C, only integer constant expressions with value 0 are null pointer constants.
    Double 0.0 and integer variables (even if their runtime value is 0) are NOT. -/
private def isNullPtrConstant : AST.Exp → Bool
  | .Constant (.ConstInt n)   => n == 0
  | .Constant (.ConstLong n)  => n == 0
  | .Constant (.ConstUInt n)  => n == 0
  | .Constant (.ConstULong n) => n == 0
  | _                         => false

/-- True iff a type is a pointer type. -/
private def isPointerType : AST.Typ → Bool
  | .Pointer _ => true
  | _          => false

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

/-- Implicit cast: like `castTo` but validates that the conversion is legal.
    Illegal implicit conversions (which require an explicit cast in C):
      - Double  → Pointer  (always illegal, even with explicit cast)
      - Pointer → Double   (always illegal, even with explicit cast)
      - Pointer A → Pointer B  (different pointee types)
      - Integer (non-null) → Pointer  (only integer constant 0 is a null pointer constant)
      - Pointer → Integer  (requires explicit cast) -/
private def implicitCastTo (target : AST.Typ) (current : AST.Typ) (e : AST.Exp) : TcM AST.Exp := do
  if target == current then return e
  else match target, current with
  | .Pointer _, .Double =>
      throw "TypeCheck: cannot convert double to pointer (even with implicit cast)"
  | .Double, .Pointer _ =>
      throw "TypeCheck: cannot convert pointer to double (even with implicit cast)"
  | .Pointer _, .Pointer _ =>
      -- Both are pointers but different pointee types: illegal implicit conversion
      throw "TypeCheck: cannot implicitly convert between different pointer types"
  | .Pointer _, _ =>
      -- Integer → pointer: only integer constant 0 (null pointer constant) is allowed
      if isNullPtrConstant e then return (.Cast target e)
      else throw "TypeCheck: cannot implicitly convert a non-null-pointer-constant to a pointer type (only integer constant 0 is a null pointer constant)"
  | _, .Pointer _ =>
      -- Pointer → integer: requires an explicit cast
      throw "TypeCheck: cannot implicitly convert a pointer to a non-pointer type"
  | _, _ =>
      -- Ordinary numeric conversions: delegate to castTo
      return (castTo target current e)

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
  -- Explicit cast: type-check inner, wrap in Cast.
  -- Chapter 14: casting between pointer and double is never allowed, even explicitly.
  | .Cast targetTyp inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      match targetTyp, innerTyp with
      | .Pointer _, .Double =>
          throw "TypeCheck: cannot cast double to pointer"
      | .Double, .Pointer _ =>
          throw "TypeCheck: cannot cast pointer to double"
      | _, _ => return (.Cast targetTyp inner', targetTyp)
  -- Unary operators: the result type matches the operand type.
  -- Exception: logical NOT (!) always produces Int regardless of operand type.
  -- Chapter 13: bitwise complement (~) is not valid on Double.
  | .Unary .Not inner => do
      let (inner', _) ← typeCheckExp st inner
      -- Logical NOT always produces int (0 or 1)
      return (.Unary .Not inner', .Int)
  | .Unary .Complement inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- C §6.5.3.3: ~ requires integer operand; doubles and pointers are not allowed
      if innerTyp == .Double then
        throw s!"TypeCheck: bitwise complement (~) is not valid on a double"
      if isPointerType innerTyp then
        throw s!"TypeCheck: bitwise complement (~) is not valid on a pointer"
      return (.Unary .Complement inner', innerTyp)
  -- Chapter 14: unary negation is not valid on a pointer
  | .Unary .Negate inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      if isPointerType innerTyp then
        throw s!"TypeCheck: unary negation (-) is not valid on a pointer"
      return (.Unary .Negate inner', innerTyp)
  -- (All UnaryOp constructors are handled above: Not, Complement, Negate)
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
      -- Chapter 14: pointers are not valid shift operands
      if isPointerType leftTyp then
        throw s!"TypeCheck: left operand of shift (<<) cannot be a pointer"
      if isPointerType rightTyp then
        throw s!"TypeCheck: right operand of shift (<<) cannot be a pointer"
      return (.Binary .ShiftLeft left' right', leftTyp)
  | .Binary .ShiftRight left right => do
      let (left',  leftTyp)  ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      if leftTyp == .Double then
        throw s!"TypeCheck: left operand of shift (>>) cannot be double"
      if rightTyp == .Double then
        throw s!"TypeCheck: right operand of shift (>>) cannot be double"
      -- Chapter 14: pointers are not valid shift operands
      if isPointerType leftTyp then
        throw s!"TypeCheck: left operand of shift (>>) cannot be a pointer"
      if isPointerType rightTyp then
        throw s!"TypeCheck: right operand of shift (>>) cannot be a pointer"
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
      let isLeftPtr  := isPointerType leftTyp
      let isRightPtr := isPointerType rightTyp
      -- Chapter 14: equality/inequality with a pointer operand.
      -- Rules:
      --   Both pointers → must be same pointer type (otherwise error).
      --   One pointer, one integer → integer must be a null pointer constant (value 0).
      --   One pointer, one double → always illegal.
      if (op == .Equal || op == .NotEqual) && (isLeftPtr || isRightPtr) then do
        if isLeftPtr && isRightPtr then
          -- Both are pointers: they must have the same type
          if leftTyp == rightTyp then
            return (.Binary op left' right', .Int)
          else
            throw "TypeCheck: cannot compare pointers to different types"
        else if isLeftPtr then do
          -- LHS is pointer, RHS must be null pointer constant
          if rightTyp == .Double then
            throw "TypeCheck: cannot compare a pointer to a double"
          if !isNullPtrConstant right' then
            throw "TypeCheck: cannot compare a pointer to a non-null-pointer-constant integer (only integer constant 0 is allowed)"
          return (.Binary op left' (.Cast leftTyp right'), .Int)
        else do
          -- RHS is pointer, LHS must be null pointer constant
          if leftTyp == .Double then
            throw "TypeCheck: cannot compare a pointer to a double"
          if !isNullPtrConstant left' then
            throw "TypeCheck: cannot compare a non-null-pointer-constant integer to a pointer (only integer constant 0 is allowed)"
          return (.Binary op (.Cast rightTyp left') right', .Int)
      -- Chapter 14: arithmetic and bitwise operations on pointers are illegal.
      -- Pointers may not appear as operands of *, /, %, &, |, ^, +, -.
      -- (Pointer arithmetic with + and - is a Chapter 15 feature; for now, both disallowed.)
      match op with
      | .Multiply | .Divide | .Remainder | .BitAnd | .BitOr | .BitXor
      | .Add | .Subtract =>
          if isLeftPtr then
            throw s!"TypeCheck: pointer type cannot be used as operand of this operator"
          if isRightPtr then
            throw s!"TypeCheck: pointer type cannot be used as operand of this operator"
      | _ => pure ()
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
      -- Chapter 14: use implicitCastTo to catch illegal pointer assignments
      let rhs'' ← implicitCastTo lhsTyp rhsTyp rhs'
      return (.Assignment (.Var lhsName) rhs'', lhsTyp)
  -- Chapter 14: assignment through a pointer dereference: `*ptr = rhs`
  | .Assignment (.Dereference ptrExp) rhs => do
      let (ptr', ptrTyp) ← typeCheckExp st ptrExp
      let (rhs', rhsTyp) ← typeCheckExp st rhs
      match ptrTyp with
      | .Pointer t =>
          -- Chapter 14: use implicitCastTo to catch illegal pointer assignments
          let rhs'' ← implicitCastTo t rhsTyp rhs'
          return (.Assignment (.Dereference ptr') rhs'', t)
      | _ => throw s!"TypeCheck: cannot assign through a non-pointer value"
  | .Assignment lhs _ =>
      throw s!"TypeCheck: invalid lvalue in assignment (should have been caught by VarResolution)"
  -- Conditional: both branches are widened to the common type.
  -- Chapter 14: if either branch is a pointer, both must be the same pointer type
  -- (or one must be a null pointer constant that can be cast to the other's type).
  | .Conditional cond e1 e2 => do
      let (cond', _)    ← typeCheckExp st cond
      let (e1', t1)     ← typeCheckExp st e1
      let (e2', t2)     ← typeCheckExp st e2
      let ptr1 := isPointerType t1
      let ptr2 := isPointerType t2
      if ptr1 || ptr2 then do
        if ptr1 && ptr2 then do
          -- Both are pointers: must be same type
          if t1 == t2 then
            let r : AST.Exp := .Conditional cond' e1' e2'
            return (r, t1)
          else throw "TypeCheck: ternary branches have incompatible pointer types"
        else if ptr1 then do
          -- e1 is pointer, e2 must be null pointer constant
          if !isNullPtrConstant e2' then
            throw "TypeCheck: cannot mix pointer and non-pointer types in ternary expression"
          let r : AST.Exp := .Conditional cond' e1' (.Cast t1 e2')
          return (r, t1)
        else do
          -- e2 is pointer, e1 must be null pointer constant
          if !isNullPtrConstant e1' then
            throw "TypeCheck: cannot mix pointer and non-pointer types in ternary expression"
          let r : AST.Exp := .Conditional cond' (.Cast t2 e1') e2'
          return (r, t2)
      else
        let common := commonType t1 t2
        let e1'' := castTo common t1 e1'
        let e2'' := castTo common t2 e2'
        let r : AST.Exp := .Conditional cond' e1'' e2''
        return (r, common)
  -- Postfix increment/decrement: type of the variable
  | .PostfixIncr (.Var v) => do
      let t ← lookupVarTyp st v
      return (.PostfixIncr (.Var v), t)
  | .PostfixDecr (.Var v) => do
      let t ← lookupVarTyp st v
      return (.PostfixDecr (.Var v), t)
  -- Chapter 14: postfix ++/-- through a pointer dereference: `(*p)++`
  | .PostfixIncr (.Dereference ptrExp) => do
      let (ptr', ptrTyp) ← typeCheckExp st ptrExp
      match ptrTyp with
      | .Pointer t => return (.PostfixIncr (.Dereference ptr'), t)
      | _ => throw s!"TypeCheck: postfix ++ requires a pointer dereference"
  | .PostfixDecr (.Dereference ptrExp) => do
      let (ptr', ptrTyp) ← typeCheckExp st ptrExp
      match ptrTyp with
      | .Pointer t => return (.PostfixDecr (.Dereference ptr'), t)
      | _ => throw s!"TypeCheck: postfix -- requires a pointer dereference"
  | .PostfixIncr e | .PostfixDecr e =>
      throw s!"TypeCheck: invalid lvalue in postfix operator"
  -- Chapter 14: address-of operator: `&e` has type `Pointer(typeOf e)`.
  -- The operand must be an lvalue (a Var or a Dereference expression).
  -- Note: &*e is valid (cancels out), handled in TackyGen as an optimization.
  | .AddrOf inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- Only Var and Dereference are lvalues; everything else is an rvalue
      match inner' with
      | .Var _         => return (.AddrOf inner', .Pointer innerTyp)
      | .Dereference _ => return (.AddrOf inner', .Pointer innerTyp)
      | _ => throw "TypeCheck: operand of address-of (&) must be an lvalue (a variable or *expr)"
  -- Chapter 14: dereference operator: `*e` has type `t` when `typeOf e = Pointer(t)`
  | .Dereference inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      match innerTyp with
      | .Pointer t => return (.Dereference inner', t)
      | _ => throw s!"TypeCheck: cannot dereference a non-pointer type"
  -- Function call: cast each argument to the declared parameter type
  | .FunCall fname args => do
      match lookupSym st fname with
      | none => throw s!"Undeclared function '{fname}'"
      | some { type := .Obj _, .. } => throw s!"'{fname}' is a variable, not a function"
      | some { type := .Fun _ paramTypes retTyp, .. } => do
          -- Type-check each argument and implicitly cast to the corresponding param type
          let typedArgs ← args.mapM (typeCheckExp st)
          -- Chapter 14: use implicitCastTo to catch illegal pointer/int conversions
          let castedArgs ← (typedArgs.zip paramTypes).mapM fun ((arg, argTyp), paramTyp) =>
            implicitCastTo paramTyp argTyp arg
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
      -- Chapter 14: use implicitCastTo to catch illegal pointer return type conversions
      let e'' ← implicitCastTo retTyp eTyp e'
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
      -- Double and pointer are not valid switch controlling expression types.
      if expTyp == .Double then
        throw s!"TypeCheck: switch controlling expression must have integer type, not double"
      if isPointerType expTyp then
        throw s!"TypeCheck: switch controlling expression must have integer type, not pointer"
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
        -- Chapter 14: use implicitCastTo to catch illegal pointer initializers
        implicitCastTo decl.typ eTyp e'
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
      -- Chapter 14: use implicitCastTo to catch illegal pointer initializers
      let init' ← decl.init.mapM fun e => do
        let (e', eTyp) ← typeCheckExp st e
        implicitCastTo decl.typ eTyp e'
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
        -- Chapter 14: use implicitCastTo to catch illegal pointer initializers
        let init' ← decl.init.mapM fun e => do
          let (e', eTyp) ← typeCheckExp st e
          implicitCastTo decl.typ eTyp e'
        return .VarDecl { decl with init := init' }
    | other => return other
  return { p with topLevels := topLevels' }

end Semantics
