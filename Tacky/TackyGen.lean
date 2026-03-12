import AST.AST
import Tacky.Tacky
import Semantics.SymbolTable

/-
  IR generation pass: converts AST.Program → Tacky.Program.

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
    `counter`:  unique name counter (same as before).
    `typeEnv`:  maps every temporary variable name (e.g. `"tmp.5"`) to its
                scalar type, so the Driver can build the backend symbol table. -/
private structure GenState where
  counter : Nat
  typeEnv : List (String × AST.Typ)

private abbrev GenM := StateM GenState

/-- Allocate a fresh temporary of the given type, recording it in typeEnv. -/
private def makeTemporary (t : AST.Typ) : GenM String := do
  let s ← get
  let name := s!"tmp.{s.counter}"
  modify (fun (st : GenState) => { st with counter := st.counter + 1, typeEnv := (name, t) :: st.typeEnv })
  return name

private def makeLabel (base : String) : GenM String := do
  let s ← get
  modify (fun s => { s with counter := s.counter + 1 })
  return s!"{base}.{s.counter - 1}"

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
  | .Constant (.ConstInt n)  => return (.Constant n, .Int,  [])
  | .Constant (.ConstLong n) => return (.Constant n, .Long, [])
  | .Var v => do
      -- Look up the variable's type from the symbol table
      let t : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int   -- default (temporaries are not in frontend sym table)
      return (.Var v, t, [])
  | .Cast targetTyp inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      if targetTyp == srcTyp then
        -- No conversion needed (same type): pass through
        return (src, targetTyp, instrs)
      else
        let dst := Val.Var (← makeTemporary targetTyp)
        match targetTyp, srcTyp with
        | .Long, .Int =>
            -- Sign-extend 32-bit int to 64-bit long
            return (dst, .Long, instrs ++ [.SignExtend src dst])
        | .Int, .Long =>
            -- Truncate 64-bit long to 32-bit int
            return (dst, .Int, instrs ++ [.Truncate src dst])
        | _, _ =>
            -- Same type (redundant cast): pass through
            return (src, targetTyp, instrs)
  | .Unary .Not inner => do
      -- Logical NOT: result is always Int (0 or 1)
      let (src, _, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary .Int)
      return (dst, .Int, instrs ++ [.Unary .Not src dst])
  | .Unary op inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary srcTyp)
      return (dst, srcTyp, instrs ++ [.Unary (convertUnop op) src dst])
  | .Binary .And e1 e2 => do
      -- Short-circuit logical AND; result is always Int
      let falseLabel ← makeLabel "and_false"
      let endLabel   ← makeLabel "and_end"
      let (v1, _, instrs1) ← emitExp st e1
      let (v2, _, instrs2) ← emitExp st e2
      let result := Val.Var (← makeTemporary .Int)
      return (result,
        .Int,
        instrs1 ++
        [.JumpIfZero v1 falseLabel] ++
        instrs2 ++
        [.JumpIfZero v2 falseLabel,
         .Copy (.Constant 1) result,
         .Jump endLabel,
         .Label falseLabel,
         .Copy (.Constant 0) result,
         .Label endLabel])
  | .Binary .Or e1 e2 => do
      -- Short-circuit logical OR; result is always Int
      let trueLabel  ← makeLabel "or_true"
      let endLabel   ← makeLabel "or_end"
      let (v1, _, instrs1) ← emitExp st e1
      let (v2, _, instrs2) ← emitExp st e2
      let result := Val.Var (← makeTemporary .Int)
      return (result,
        .Int,
        instrs1 ++
        [.JumpIfNotZero v1 trueLabel] ++
        instrs2 ++
        [.JumpIfNotZero v2 trueLabel,
         .Copy (.Constant 0) result,
         .Jump endLabel,
         .Label trueLabel,
         .Copy (.Constant 1) result,
         .Label endLabel])
  | .Binary op e1 e2 => do
      let (src1, t1, instrs1) ← emitExp st e1
      let (src2, t2, instrs2) ← emitExp st e2
      -- After TypeCheck, both operands have the same type (casts were inserted),
      -- EXCEPT for shift operators where the right operand keeps its own type.
      -- Relational operators always produce Int.
      -- Shift operators: result type is the type of the LEFT operand (C §6.5.7).
      -- Other arithmetic operators produce the common type of both operands.
      let resultTyp : AST.Typ := match op with
        | .Equal | .NotEqual | .LessThan | .LessOrEqual
        | .GreaterThan | .GreaterOrEqual => .Int
        | .ShiftLeft | .ShiftRight => t1   -- type of left operand, not common type
        | _ => if t1 == .Long || t2 == .Long then .Long else .Int
      let dst := Val.Var (← makeTemporary resultTyp)
      return (dst, resultTyp, instrs1 ++ instrs2 ++ [.Binary (convertBinop op) src1 src2 dst])
  | .Conditional cond e1 e2 => do
      let e2Label  ← makeLabel "ternary_else"
      let endLabel ← makeLabel "ternary_end"
      let (c,  _, condInstrs) ← emitExp st cond
      let (v1, t1, e1Instrs) ← emitExp st e1
      let (v2, _, e2Instrs)  ← emitExp st e2
      -- After TypeCheck, both branches have the same type
      let result := Val.Var (← makeTemporary t1)
      return (result, t1,
        condInstrs ++
        [.JumpIfZero c e2Label] ++
        e1Instrs ++
        [.Copy v1 result, .Jump endLabel, .Label e2Label] ++
        e2Instrs ++
        [.Copy v2 result, .Label endLabel])
  | .Assignment (.Var v) rhs => do
      let (result, _, instrs) ← emitExp st rhs
      -- After TypeCheck, rhs is already cast to match v's type
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
      -- Determine the right constant: 1 as Int or 1 as Long
      let one := Val.Constant 1
      return (.Var tmp, varTyp,
        [.Copy (.Var v) (.Var tmp),
         .Binary .Add (.Var v) one (.Var v)])
  | .PostfixIncr _ => return (.Constant 0, .Int, [])
  | .PostfixDecr (.Var v) => do
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let tmp ← makeTemporary varTyp
      let one := Val.Constant 1
      return (.Var tmp, varTyp,
        [.Copy (.Var v) (.Var tmp),
         .Binary .Subtract (.Var v) one (.Var v)])
  | .PostfixDecr _ => return (.Constant 0, .Int, [])
  | .FunCall name args => do
      let argResults ← args.mapM (emitExp st)
      let argInstrs := argResults.foldl (fun acc (_, _, instrs) => acc ++ instrs) []
      let argVals   := argResults.map   (fun (v, _, _) => v)
      -- Look up the function's return type
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
              -- Compare switch value against case constant (same type as v)
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

/-- Emit a TACKY function definition.
    Chapter 11: param names are still plain strings (types are in sym table). -/
private def emitFunctionDef (st : Semantics.SymbolTable) (f : AST.FunctionDef)
    (isGlobal : Bool) : GenM FunctionDef := do
  -- Extract just the renamed parameter names (types are in the sym table)
  let paramNames := f.params.map (·.2)
  let body ← f.body.foldlM (fun acc item => do
    return acc ++ (← emitBlockItem st f.name item)) []
  return { name := f.name, params := paramNames,
           body := body ++ [.Return (.Constant 0)],
           global := isGlobal }

/-- Collect static variable entries from the symbol table and emit them as
    TackyTopLevel.StaticVariable items.
    Chapter 11: includes the variable's type so the emitter can use .long/.quad. -/
private def emitStaticVars (symTable : Semantics.SymbolTable) : List TackyTopLevel :=
  symTable.filterMap fun (name, entry) =>
    match entry.type, entry.attrs with
    | .Obj t, .Static (.Initial n) isGlobal  => some (.StaticVariable name isGlobal t n)
    | .Obj t, .Static .Tentative   isGlobal  => some (.StaticVariable name isGlobal t 0)
    | _,      _                              => none

/-- Entry point for the IR generation pass.
    Returns `(Program, typeEnv)` where `typeEnv` maps each generated temporary
    name to its scalar type.  The Driver uses this to build the backend symbol
    table for CodeGen and PseudoReplace. -/
def emitProgram (p : AST.Program) (symTable : Semantics.SymbolTable)
    (initCounter : Nat := 0) : Program × List (String × AST.Typ) :=
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
  let initState : GenState := { counter := initCounter, typeEnv := [] }
  let (funcItems, finalState) := action.run initState
  let staticItems := emitStaticVars symTable
  ({ topLevels := funcItems ++ staticItems }, finalState.typeEnv)

end Tacky
