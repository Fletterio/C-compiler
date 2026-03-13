import AST.AST
import Tacky.Tacky
import Semantics.SymbolTable

/-
  IR generation pass: converts AST.Program → Tacky.Program.

  Chapter 13 additions:
    - `emitExp` handles `Constant(.ConstDouble f)`: allocates a fresh name
      `.LfpC.N` for the float constant, records it in `floatConsts`, and
      returns `Val.Var ".LfpC.N"` (the constant lives in read-only data).
    - `Cast` now handles all conversions to/from `Double`:
        Int → Double  : `IntToDouble`
        Double → Int  : `DoubleToInt`
        UInt → Double : `UIntToDouble`
        Double → UInt : `DoubleToUInt`
        Long → Double : `IntToDouble` (via cvtsi2sdq — reused, CodeGen distinguishes by type)
        Double → Long : `DoubleToInt` (via cvttsd2siq — reused)
        ULong → Double: `ULongToDouble`
        Double → ULong: `DoubleToULong`
    - `GenState` gains `floatConsts` (name → value) and `needsNegZero`.
    - `emitProgram` returns `(Program, typeEnv, floatConsts, needsNegZero)`.

  Chapter 11 additions:
    - `emitExp` returns `(Val × AST.Typ × List Instruction)` so that each
      expression's type is available for inserting correct assembly instructions.
    - `makeTemporary` takes the type of the temporary being created and records
      it in the `typeEnv` map (name → type) threaded through generation.
    - Handles `AST.Exp.Cast`: emits `SignExtend` (Int→Long) or `Truncate`
      (Long→Int) as appropriate.
    - Handles typed constants: `ConstInt` → type `Int`, `ConstLong` → type `Long`.
    - `emitProgram` returns `(Program × List (String × AST.Typ))`, the second
      component being the `typeEnv` that the Driver uses to build the backend
      symbol table.
    - `StaticVariable` top-level items now carry the variable's AST.Typ.
    - The counter is global across all functions (unchanged).
-/

namespace Tacky

-- ---------------------------------------------------------------------------
-- Generation monad
-- ---------------------------------------------------------------------------

/-- State threaded through IR generation.
    `counter`:    unique name counter (same as before).
    `typeEnv`:    maps every temporary variable name (e.g. `"tmp.5"`) to its
                  scalar type, so the Driver can build the backend symbol table.
    `floatConsts`: (Chapter 13) maps float-constant labels (e.g. `".LfpC.5"`)
                  to their float values, for emission as read-only static data.
    `needsNegZero`: (Chapter 13) true when a double Negate instruction has been
                  emitted; the Driver will add the `.Lneg_zero` constant. -/
private structure GenState where
  counter     : Nat
  typeEnv     : List (String × AST.Typ)
  floatConsts : List (String × Float)
  needsNegZero : Bool

private abbrev GenM := StateM GenState

/-- Allocate a fresh temporary of the given type, recording it in typeEnv. -/
private def makeTemporary (t : AST.Typ) : GenM String := do
  let s ← get
  let name := s!"tmp.{s.counter}"
  modify (fun st => { st with counter := st.counter + 1, typeEnv := (name, t) :: st.typeEnv })
  return name

private def makeLabel (base : String) : GenM String := do
  let s ← get
  -- Use s.counter (the PRE-modification value) as the unique suffix.
  -- Importantly, do NOT subtract 1: that was an off-by-one bug where counter
  -- values 0 and 1 both produced the label "base.0" (since Nat 0-1 = 0).
  modify (fun st => { st with counter := st.counter + 1 })
  return s!"{base}.{s.counter}"

/-- (Chapter 13) Intern a float constant: allocate a unique read-only label.
    Returns the label name to use as `Val.Var label`. -/
private def internFloat (f : Float) : GenM String := do
  let s ← get
  let label := s!".LfpC.{s.counter}"
  modify (fun st => { st with counter := st.counter + 1,
                               typeEnv := (label, .Double) :: st.typeEnv,
                               floatConsts := (label, f) :: st.floatConsts })
  return label

-- ---------------------------------------------------------------------------
-- Operator translation
-- ---------------------------------------------------------------------------

private def convertUnop : AST.UnaryOp → UnaryOp
  | .Complement => .Complement
  | .Negate     => .Negate
  | .Not        => .Not

private def convertBinop : AST.BinaryOp → BinaryOp
  | .Add           => .Add
  | .Subtract      => .Subtract
  | .Multiply      => .Multiply
  | .Divide        => .Divide
  | .Remainder     => .Remainder
  | .BitAnd        => .BitAnd
  | .BitOr         => .BitOr
  | .BitXor        => .BitXor
  | .ShiftLeft     => .ShiftLeft
  | .ShiftRight    => .ShiftRight
  | .Equal         => .Equal
  | .NotEqual      => .NotEqual
  | .LessThan      => .LessThan
  | .LessOrEqual   => .LessOrEqual
  | .GreaterThan   => .GreaterThan
  | .GreaterOrEqual => .GreaterOrEqual
  | _              => .Add   -- unreachable: And/Or handled via jumps

-- ---------------------------------------------------------------------------
-- Expression lowering
-- ---------------------------------------------------------------------------

/-- Lower an AST expression to TACKY instructions.
    Returns `(result_val, result_type, instructions)`.

    Chapter 13:
    - `Constant(.ConstDouble f)` → intern `f` as a read-only static constant,
      return `Val.Var label` with type `Double`.
    - `Cast(.Double, e)` / `Cast(intTyp, doubleExpr)` → conversion instructions.
    - `Unary .Negate e` where `e : Double` → sets `needsNegZero` in state.

    Chapter 11:
    - `Constant(.ConstInt n)` → `(Constant n, Int, [])`
    - `Constant(.ConstLong n)` → `(Constant n, Long, [])`
    - `Cast(.Long, e)` where e : Int → emit `SignExtend`
    - `Cast(.Int, e)` where e : Long → emit `Truncate`
    - `Cast(t, e)` where e already has type t → identity (no instruction)
    - Binary relational operators always produce `Int` results (0 or 1).
    - Other binary operators produce the common type of their operands.
      (TypeCheck has already inserted Casts so operands have the same type.) -/
private def emitExp (st : Semantics.SymbolTable) : AST.Exp → GenM (Val × AST.Typ × List Instruction)
  | .Constant (.ConstInt n)   => return (.Constant n, .Int,   [])
  | .Constant (.ConstLong n)  => return (.Constant n, .Long,  [])
  | .Constant (.ConstUInt n)  => return (.Constant n, .UInt,  [])  -- Chapter 12
  | .Constant (.ConstULong n) => return (.Constant n, .ULong, [])  -- Chapter 12
  | .Constant (.ConstDouble f) => do
      -- Chapter 13: float constants cannot be immediates; intern as a static label.
      let label ← internFloat f
      return (.Var label, .Double, [])
  | .Var v => do
      let t : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      return (.Var v, t, [])
  | .Cast targetTyp inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      if targetTyp == srcTyp then
        return (src, targetTyp, instrs)
      else
        let dst := Val.Var (← makeTemporary targetTyp)
        match targetTyp, srcTyp with
        -- ---- integer ↔ integer conversions (Ch11/Ch12) ----
        -- Widening sign-extend (signed int → wider signed or unsigned type)
        | .Long,  .Int  => return (dst, .Long,  instrs ++ [.SignExtend src dst])
        | .ULong, .Int  => return (dst, .ULong, instrs ++ [.SignExtend src dst])
        -- Widening zero-extend (unsigned int → wider type)
        | .Long,  .UInt => return (dst, .Long,  instrs ++ [.ZeroExtend src dst])
        | .ULong, .UInt => return (dst, .ULong, instrs ++ [.ZeroExtend src dst])
        -- Narrowing truncation (64-bit → 32-bit: keep lower 32 bits)
        | .Int,  .Long  => return (dst, .Int,  instrs ++ [.Truncate src dst])
        | .UInt, .Long  => return (dst, .UInt, instrs ++ [.Truncate src dst])
        | .Int,  .ULong => return (dst, .Int,  instrs ++ [.Truncate src dst])
        | .UInt, .ULong => return (dst, .UInt, instrs ++ [.Truncate src dst])
        -- ---- double ↔ integer conversions (Ch13) ----
        -- Signed integer → Double
        | .Double, .Int   => return (dst, .Double, instrs ++ [.IntToDouble  src dst])
        | .Double, .Long  => return (dst, .Double, instrs ++ [.IntToDouble  src dst])
        -- Unsigned integer → Double
        | .Double, .UInt  => return (dst, .Double, instrs ++ [.UIntToDouble  src dst])
        | .Double, .ULong => return (dst, .Double, instrs ++ [.ULongToDouble src dst])
        -- Double → Signed integer
        | .Int,    .Double => return (dst, .Int,  instrs ++ [.DoubleToInt  src dst])
        | .Long,   .Double => return (dst, .Long, instrs ++ [.DoubleToInt  src dst])
        -- Double → Unsigned integer
        | .UInt,   .Double => return (dst, .UInt,  instrs ++ [.DoubleToUInt  src dst])
        | .ULong,  .Double => return (dst, .ULong, instrs ++ [.DoubleToULong src dst])
        -- Same-size reinterpret (int↔uint or long↔ulong): copy into a new typed temporary
        | _, _ => return (dst, targetTyp, instrs ++ [.Copy src dst])
  | .Unary .Not inner => do
      let (src, _, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary .Int)
      return (dst, .Int, instrs ++ [.Unary .Not src dst])
  | .Unary .Negate inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary srcTyp)
      -- Chapter 13: double negation needs the neg-zero constant in the assembly
      if srcTyp == .Double then
        modify (fun s => { s with needsNegZero := true })
      return (dst, srcTyp, instrs ++ [.Unary .Negate src dst])
  | .Unary op inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary srcTyp)
      return (dst, srcTyp, instrs ++ [.Unary (convertUnop op) src dst])
  | .Binary .And e1 e2 => do
      let falseLabel ← makeLabel "and_false"
      let endLabel   ← makeLabel "and_end"
      let (v1, _, instrs1) ← emitExp st e1
      let (v2, _, instrs2) ← emitExp st e2
      let result := Val.Var (← makeTemporary .Int)
      return (result, .Int,
        instrs1 ++ [.JumpIfZero v1 falseLabel] ++
        instrs2 ++ [.JumpIfZero v2 falseLabel,
                    .Copy (.Constant 1) result, .Jump endLabel,
                    .Label falseLabel, .Copy (.Constant 0) result,
                    .Label endLabel])
  | .Binary .Or e1 e2 => do
      let trueLabel  ← makeLabel "or_true"
      let endLabel   ← makeLabel "or_end"
      let (v1, _, instrs1) ← emitExp st e1
      let (v2, _, instrs2) ← emitExp st e2
      let result := Val.Var (← makeTemporary .Int)
      return (result, .Int,
        instrs1 ++ [.JumpIfNotZero v1 trueLabel] ++
        instrs2 ++ [.JumpIfNotZero v2 trueLabel,
                    .Copy (.Constant 0) result, .Jump endLabel,
                    .Label trueLabel, .Copy (.Constant 1) result,
                    .Label endLabel])
  | .Binary op e1 e2 => do
      let (src1, t1, instrs1) ← emitExp st e1
      let (src2, t2, instrs2) ← emitExp st e2
      let resultTyp : AST.Typ := match op with
        | .Equal | .NotEqual | .LessThan | .LessOrEqual
        | .GreaterThan | .GreaterOrEqual => .Int
        | .ShiftLeft | .ShiftRight => t1   -- type of left operand (C §6.5.7)
        | .And | .Or               => .Int
        | _                        => t1   -- arithmetic ops: t1 == t2 after TypeCheck
      let dst := Val.Var (← makeTemporary resultTyp)
      return (dst, resultTyp, instrs1 ++ instrs2 ++ [.Binary (convertBinop op) src1 src2 dst])
  | .Conditional cond e1 e2 => do
      let e2Label  ← makeLabel "ternary_else"
      let endLabel ← makeLabel "ternary_end"
      let (c,  _, condInstrs) ← emitExp st cond
      let (v1, t1, e1Instrs) ← emitExp st e1
      let (v2, _, e2Instrs)  ← emitExp st e2
      let result := Val.Var (← makeTemporary t1)
      return (result, t1,
        condInstrs ++ [.JumpIfZero c e2Label] ++
        e1Instrs ++ [.Copy v1 result, .Jump endLabel, .Label e2Label] ++
        e2Instrs ++ [.Copy v2 result, .Label endLabel])
  | .Assignment (.Var v) rhs => do
      let (result, _, instrs) ← emitExp st rhs
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      return (.Var v, varTyp, instrs ++ [.Copy result (.Var v)])
  | .Assignment _ _ => return (.Constant 0, .Int, [])
  | .PostfixIncr (.Var v) => do
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let tmp ← makeTemporary varTyp
      -- For doubles, add 1.0; for integers, add 1
      if varTyp == .Double then do
        let oneLabel ← internFloat 1.0
        return (.Var tmp, varTyp,
          [.Copy (.Var v) (.Var tmp),
           .Binary .Add (.Var v) (.Var oneLabel) (.Var v)])
      else
        return (.Var tmp, varTyp,
          [.Copy (.Var v) (.Var tmp),
           .Binary .Add (.Var v) (.Constant 1) (.Var v)])
  | .PostfixIncr _ => return (.Constant 0, .Int, [])
  | .PostfixDecr (.Var v) => do
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let tmp ← makeTemporary varTyp
      if varTyp == .Double then do
        let oneLabel ← internFloat 1.0
        return (.Var tmp, varTyp,
          [.Copy (.Var v) (.Var tmp),
           .Binary .Subtract (.Var v) (.Var oneLabel) (.Var v)])
      else
        return (.Var tmp, varTyp,
          [.Copy (.Var v) (.Var tmp),
           .Binary .Subtract (.Var v) (.Constant 1) (.Var v)])
  | .PostfixDecr _ => return (.Constant 0, .Int, [])
  | .FunCall name args => do
      let argResults ← args.mapM (emitExp st)
      let argInstrs := argResults.foldl (fun acc (_, _, instrs) => acc ++ instrs) []
      let argVals   := argResults.map   (fun (v, _, _) => v)
      let retTyp : AST.Typ := match Semantics.lookupSym st name with
        | some { type := .Fun _ _ rt, .. } => rt
        | _ => .Int
      let dst := Val.Var (← makeTemporary retTyp)
      return (dst, retTyp, argInstrs ++ [.FunCall name argVals dst])

-- ---------------------------------------------------------------------------
-- Statement and block-item lowering
-- ---------------------------------------------------------------------------

private def emitForInit (st : Semantics.SymbolTable) : AST.ForInit → GenM (List Instruction)
  | .InitExp none   => return []
  | .InitExp (some e) => do
      let (_, _, instrs) ← emitExp st e
      return instrs
  | .InitDecl decl =>
      match decl.init with
      | none   => return []
      | some e => do
          let (val, _, instrs) ← emitExp st e
          return instrs ++ [.Copy val (.Var decl.name)]

mutual

private partial def emitStatement (st : Semantics.SymbolTable) (funcName : String)
    : AST.Statement → GenM (List Instruction)
  | .Return e => do
      let (v, _, instrs) ← emitExp st e
      return instrs ++ [.Return v]
  | .Expression e => do
      let (_, _, instrs) ← emitExp st e
      return instrs
  | .If cond thenStmt none => do
      let endLabel ← makeLabel "if_end"
      let (c, _, condInstrs) ← emitExp st cond
      let thenInstrs ← emitStatement st funcName thenStmt
      return condInstrs ++ [.JumpIfZero c endLabel] ++ thenInstrs ++ [.Label endLabel]
  | .If cond thenStmt (some elseStmt) => do
      let elseLabel ← makeLabel "if_else"
      let endLabel  ← makeLabel "if_end"
      let (c, _, condInstrs) ← emitExp st cond
      let thenInstrs ← emitStatement st funcName thenStmt
      let elseInstrs ← emitStatement st funcName elseStmt
      return condInstrs ++ [.JumpIfZero c elseLabel] ++ thenInstrs ++
             [.Jump endLabel, .Label elseLabel] ++ elseInstrs ++ [.Label endLabel]
  | .Compound items => do
      let instrs ← items.foldlM (fun acc item => do
        return acc ++ (← emitBlockItem st funcName item)) []
      return instrs
  | .While cond body (some base) => do
      let cntLabel := "cnt_" ++ base
      let brkLabel := "brk_" ++ base
      let (c, _, condInstrs) ← emitExp st cond
      let bodyInstrs ← emitStatement st funcName body
      return [.Label cntLabel] ++ condInstrs ++ [.JumpIfZero c brkLabel] ++
             bodyInstrs ++ [.Jump cntLabel, .Label brkLabel]
  | .While _ _ none => return []
  | .DoWhile body cond (some base) => do
      let startLabel := "start_" ++ base
      let cntLabel   := "cnt_"   ++ base
      let brkLabel   := "brk_"   ++ base
      let bodyInstrs ← emitStatement st funcName body
      let (c, _, condInstrs) ← emitExp st cond
      return [.Label startLabel] ++ bodyInstrs ++ [.Label cntLabel] ++
             condInstrs ++ [.JumpIfNotZero c startLabel, .Label brkLabel]
  | .DoWhile _ _ none => return []
  | .For init cond post body (some base) => do
      let startLabel := "start_" ++ base
      let cntLabel   := "cnt_"   ++ base
      let brkLabel   := "brk_"   ++ base
      let initInstrs ← emitForInit st init
      let condInstrs ← match cond with
        | none   => pure []
        | some c => do
            let (v, _, instrs) ← emitExp st c
            pure (instrs ++ [.JumpIfZero v brkLabel])
      let bodyInstrs ← emitStatement st funcName body
      let postInstrs ← match post with
        | none   => pure []
        | some e => do
            let (_, _, instrs) ← emitExp st e
            pure instrs
      return initInstrs ++ [.Label startLabel] ++ condInstrs ++ bodyInstrs ++
             [.Label cntLabel] ++ postInstrs ++ [.Jump startLabel, .Label brkLabel]
  | .For _ _ _ _ none => return []
  | .Break (some base)    => return [.Jump ("brk_" ++ base)]
  | .Break none           => return []
  | .Continue (some base) => return [.Jump ("cnt_" ++ base)]
  | .Continue none        => return []
  | .Switch exp body (some base) cases => do
      let brkLabel := "brk_" ++ base
      let (v, vTyp, expInstrs) ← emitExp st exp
      let jumpTable ← cases.foldlM (fun acc (caseVal, caseLbl) => do
          match caseVal with
          | some n => do
              let caseConst := Val.Constant n
              let tmp := Val.Var (← makeTemporary .Int)
              pure (acc ++ [.Binary .Equal v caseConst tmp,
                            .JumpIfNotZero tmp caseLbl])
          | none => pure (acc ++ [.Jump caseLbl])) []
      let noDefault   := cases.all (fun (v, _) => v.isSome)
      let fallThrough := if noDefault then [Instruction.Jump brkLabel] else []
      let bodyInstrs ← emitStatement st funcName body
      return expInstrs ++ jumpTable ++ fallThrough ++ bodyInstrs ++ [.Label brkLabel]
  | .Switch _ _ none _ => return []
  | .Case _ body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement st funcName body)
  | .Case _ _ none => return []
  | .Default body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement st funcName body)
  | .Default _ none => return []
  | .Labeled label stmt => do
      let stmtInstrs ← emitStatement st funcName stmt
      return [.Label (funcName ++ "." ++ label)] ++ stmtInstrs
  | .Goto label =>
      return [.Jump (funcName ++ "." ++ label)]
  | .Null => return []

private partial def emitBlockItem (st : Semantics.SymbolTable) (funcName : String)
    : AST.BlockItem → GenM (List Instruction)
  | .S stmt => emitStatement st funcName stmt
  | .D decl =>
      match decl.init with
      | none   => return []
      | some e => do
          let (val, _, instrs) ← emitExp st e
          return instrs ++ [.Copy val (.Var decl.name)]
  | .FD _ => return []

end

-- ---------------------------------------------------------------------------
-- Function and program emission
-- ---------------------------------------------------------------------------

private def emitFunctionDef (st : Semantics.SymbolTable) (f : AST.FunctionDef)
    (isGlobal : Bool) : GenM FunctionDef := do
  let paramNames := f.params.map (·.2)
  let body ← f.body.foldlM (fun acc item => do
    return acc ++ (← emitBlockItem st f.name item)) []
  return { name := f.name, params := paramNames,
           body := body ++ [.Return (.Constant 0)],
           global := isGlobal }

/-- Helper: build the `AST.Const` zero initializer for a given type.
    Used for Tentative static variables. -/
private def zeroConstOf : AST.Typ → AST.Const
  | .Int    => .ConstInt 0
  | .Long   => .ConstLong 0
  | .UInt   => .ConstUInt 0
  | .ULong  => .ConstULong 0
  | .Double => .ConstDouble 0.0

/-- Collect static variable entries from the symbol table and emit them as
    TackyTopLevel.StaticVariable items.
    Chapter 13: init is now `AST.Const` (not `Int`). -/
private def emitStaticVars (symTable : Semantics.SymbolTable) : List TackyTopLevel :=
  symTable.filterMap fun (name, entry) =>
    match entry.type, entry.attrs with
    | .Obj t, .Static (.Initial n) isGlobal =>
        -- Integer static with an explicit initializer
        let c : AST.Const := match t with
          | .Int   => .ConstInt n
          | .Long  => .ConstLong n
          | .UInt  => .ConstUInt n
          | .ULong => .ConstULong n
          | .Double => .ConstDouble (Float.ofScientific n.toNat false 0)  -- fallback
        some (.StaticVariable name isGlobal t c)
    | .Obj t, .Static (.DoubleInitial f) isGlobal =>
        -- Chapter 13: static double with an explicit initializer
        some (.StaticVariable name isGlobal .Double (.ConstDouble f))
    | .Obj t, .Static .Tentative isGlobal =>
        -- Zero-initialised (goes to .bss)
        some (.StaticVariable name isGlobal t (zeroConstOf t))
    | _, _ => none

/-- Entry point for the IR generation pass.
    Returns `(Program, typeEnv, floatConsts, needsNegZero)`. -/
def emitProgram (p : AST.Program) (symTable : Semantics.SymbolTable)
    (initCounter : Nat := 0)
    : Program × List (String × AST.Typ) × List (String × Float) × Bool :=
  let astFuncs := p.topLevels.filterMap fun tl =>
    match tl with
    | .FunDef fd  => some fd
    | .FunDecl _  => none
    | .VarDecl _  => none
  let action : GenM (List TackyTopLevel) :=
    astFuncs.foldlM (fun acc fd => do
      let isGlobal : Bool := match Semantics.lookupSym symTable fd.name with
        | some { attrs := .FunAttr _ g, .. } => g
        | _ => true
      let tackyFd ← emitFunctionDef symTable fd isGlobal
      return acc ++ [.Function tackyFd]) []
  let initState : GenState :=
    { counter := initCounter, typeEnv := [], floatConsts := [], needsNegZero := false }
  let (funcItems, finalState) := action.run initState
  let staticItems := emitStaticVars symTable
  ({ topLevels := funcItems ++ staticItems },
   finalState.typeEnv,
   finalState.floatConsts,
   finalState.needsNegZero)

end Tacky
