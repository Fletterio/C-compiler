import AST.AST
import Tacky.Tacky

/-
  IR generation pass: converts AST.Program → Tacky.Program.

  Each AST expression is flattened into a sequence of TACKY instructions
  that leave the result in a fresh temporary variable (or a named variable
  for Var nodes).  Constants are passed through directly without generating
  any instructions.

  Chapter 9: handles `FunCall` expressions and multiple function definitions.
  The TACKY program contains only FunctionDef entries; FunDecl top-level items
  are skipped (they carry no code).

  A single `Nat` counter is shared by `makeTemporary` and `makeLabel` to
  guarantee that every generated name is unique within the function.
  The initial counter value is supplied by the caller so that it does not
  overlap with the names produced by the variable resolution pass.
  Temporary variables are named "tmp.N" and labels are named "<base>.N",
  where N is the current counter value.  Periods are not valid in C
  identifiers, so these names cannot clash with any user-defined identifier.

  The counter is GLOBAL across all functions: it is threaded from one function
  to the next so that no two functions produce the same temporary name.
-/

namespace Tacky

/-- The monad used during IR generation: a state monad carrying a `Nat`
    counter that is incremented each time a new temporary or label is
    allocated. -/
private abbrev GenM := StateM Nat

/-- Allocate a fresh temporary variable name of the form `"tmp.N"`. -/
private def makeTemporary : GenM String := do
  let n ← get
  modify (· + 1)
  return s!"tmp.{n}"

/-- Allocate a fresh label with the given descriptive base name,
    returning `"<base>.N"` where N is the current counter value. -/
private def makeLabel (base : String) : GenM String := do
  let n ← get
  modify (· + 1)
  return s!"{base}.{n}"

/-- Translate an AST unary operator to its TACKY equivalent. -/
private def convertUnop : AST.UnaryOp → UnaryOp
  | .Complement => .Complement
  | .Negate     => .Negate
  | .Not        => .Not

/-- Translate an AST binary operator to its TACKY equivalent.
    Not called for `And` or `Or`; those are handled via conditional jumps
    in `emitExp` and never reach this function. -/
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
  | _              => .Add  -- unreachable: And/Or handled via jumps in emitExp

/-- Flatten an AST expression into a list of TACKY instructions, returning
    the `Val` that holds the expression's result.

    - `Constant(n)`: no instructions; value is `Tacky.Val.Constant n`.
    - `Var(v)`: no instructions; value is `Tacky.Val.Var v` directly.
    - `Unary(op, inner)`: flatten `inner`, allocate a temporary, emit `Unary`.
    - `Binary(And, e1, e2)`: short-circuit logical AND via `JumpIfZero`.
    - `Binary(Or, e1, e2)`: short-circuit logical OR via `JumpIfNotZero`.
    - `Binary(op, e1, e2)`: flatten both operands, allocate a temporary,
      emit a `Binary` instruction.
    - `Assignment(Var(v), rhs)`: flatten `rhs`, emit `Copy(result, Var(v))`,
      return `Var(v)` (the value of an assignment is the assigned value).
    - `PostfixIncr(Var(v))`: save the old value to a temporary, emit
      `Binary(Add, Var(v), 1, Var(v))` to increment in place, return old value.
    - `PostfixDecr(Var(v))`: same as `PostfixIncr` but subtracts 1.
    - `FunCall(name, args)`: flatten each argument, allocate a temporary for
      the return value, emit a `FunCall` instruction. -/
private def emitExp : AST.Exp → GenM (Val × List Instruction)
  | .Constant n     => return (.Constant n, [])
  | .Var v          => return (.Var v, [])
  | .Unary op inner => do
      let (src, innerInstrs) ← emitExp inner
      let dst := Val.Var (← makeTemporary)
      let instr := Instruction.Unary (convertUnop op) src dst
      return (dst, innerInstrs ++ [instr])
  | .Binary .And e1 e2 => do
      let falseLabel    ← makeLabel "and_false"
      let endLabel      ← makeLabel "and_end"
      let (v1, instrs1) ← emitExp e1
      let (v2, instrs2) ← emitExp e2
      let result        := Val.Var (← makeTemporary)
      return (result,
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
      let trueLabel     ← makeLabel "or_true"
      let endLabel      ← makeLabel "or_end"
      let (v1, instrs1) ← emitExp e1
      let (v2, instrs2) ← emitExp e2
      let result        := Val.Var (← makeTemporary)
      return (result,
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
      let (src1, instrs1) ← emitExp e1
      let (src2, instrs2) ← emitExp e2
      let dst := Val.Var (← makeTemporary)
      let instr := Instruction.Binary (convertBinop op) src1 src2 dst
      return (dst, instrs1 ++ instrs2 ++ [instr])
  | .Conditional cond e1 e2 => do
      let e2Label  ← makeLabel "ternary_else"
      let endLabel ← makeLabel "ternary_end"
      let (c,  condInstrs) ← emitExp cond
      let (v1, e1Instrs)   ← emitExp e1
      let (v2, e2Instrs)   ← emitExp e2
      let result := Val.Var (← makeTemporary)
      return (result,
        condInstrs ++
        [.JumpIfZero c e2Label] ++
        e1Instrs ++
        [.Copy v1 result, .Jump endLabel, .Label e2Label] ++
        e2Instrs ++
        [.Copy v2 result, .Label endLabel])
  | .Assignment (.Var v) rhs => do
      let (result, instrs) ← emitExp rhs
      return (.Var v, instrs ++ [.Copy result (.Var v)])
  | .Assignment _ _ => return (.Constant 0, [])  -- unreachable after var resolution
  | .PostfixIncr (.Var v) => do
      -- Save old value, then increment v in place, return old value.
      let tmp ← makeTemporary
      return (.Var tmp,
        [.Copy (.Var v) (.Var tmp),
         .Binary .Add (.Var v) (.Constant 1) (.Var v)])
  | .PostfixIncr _ => return (.Constant 0, [])   -- unreachable after var resolution
  | .PostfixDecr (.Var v) => do
      let tmp ← makeTemporary
      return (.Var tmp,
        [.Copy (.Var v) (.Var tmp),
         .Binary .Subtract (.Var v) (.Constant 1) (.Var v)])
  | .PostfixDecr _ => return (.Constant 0, [])   -- unreachable after var resolution
  | .FunCall name args => do
      -- Flatten each argument expression into instructions + values
      let argResults ← args.mapM emitExp
      -- Collect all argument instructions (in order)
      let argInstrs := argResults.foldl (fun acc (_, instrs) => acc ++ instrs) []
      let argVals   := argResults.map (fun (v, _) => v)
      -- Allocate a fresh temporary for the return value
      let dst := Val.Var (← makeTemporary)
      -- Emit all arg instructions, then the call, result in dst
      return (dst, argInstrs ++ [.FunCall name argVals dst])

/-- Translate a `for`-loop initial clause into TACKY instructions.
    A declaration initializer emits the expression and a `Copy` into the
    renamed variable.  An expression clause emits the expression and discards
    its result.  An absent clause emits nothing. -/
private def emitForInit : AST.ForInit → GenM (List Instruction)
  | .InitExp none   => return []
  | .InitExp (some e) => do
      let (_, instrs) ← emitExp e
      return instrs
  | .InitDecl decl =>
      match decl.init with
      | none   => return []
      | some e => do
          let (val, instrs) ← emitExp e
          return instrs ++ [.Copy val (.Var decl.name)]

/-
  `emitStatement` and `emitBlockItem` are mutually recursive through the
  `Compound` constructor: `emitStatement` calls `emitBlockItem` for each item
  in a compound body, while `emitBlockItem` calls `emitStatement` for
  statement items.  Both are declared `partial` so Lean does not require a
  structural termination proof.
-/
mutual

/-- Translate an AST statement into a flat list of TACKY instructions.
    `funcName` is the name of the enclosing function, used to make
    user-defined labels unique across functions (see `Labeled`/`Goto` below).

    Loop lowering (base derived from the annotation ID, e.g. `"loop.5"`):
      break label    = "brk_loop.5"   continue label = "cnt_loop.5"

    - `While`:   `Label(cnt)` → cond → `JumpIfZero(brk)` → body → `Jump(cnt)` → `Label(brk)`
    - `DoWhile`: `Label(start)` → body → `Label(cnt)` → cond → `JumpIfNotZero(start)` → `Label(brk)`
    - `For`:     init → `Label(start)` → cond → body → `Label(cnt)` → post → `Jump(start)` → `Label(brk)`
    - `Break`/`Continue`: single unconditional `Jump`.

    Switch lowering (annotation ID `"switch.5"`, break label `"brk_switch.5"`):
      For each case `(some n, lbl)`: compare exp == n and `JumpIfNotZero` to `lbl`.
      For `(none, lbl)` (default): unconditional `Jump` to `lbl`.
      If no default: fall through to break label.

    `Case`/`Default`: emit `Label(caseLbl)` then the body.
    `Labeled`/`Goto` (extra credit ch6): user labels are prefixed with `funcName ++ "."` so
      that same-named labels in different functions do not conflict in the object file.
      (The period is not a valid C identifier character, ensuring no clash with
       user code or system-generated names like "loop.0".) -/
private partial def emitStatement (funcName : String) : AST.Statement → GenM (List Instruction)
  | .Return e => do
      let (v, instrs) ← emitExp e
      return instrs ++ [.Return v]
  | .Expression e => do
      let (_, instrs) ← emitExp e
      return instrs
  | .If cond thenStmt none => do
      let endLabel ← makeLabel "if_end"
      let (c, condInstrs) ← emitExp cond
      let thenInstrs ← emitStatement funcName thenStmt
      return condInstrs ++ [.JumpIfZero c endLabel] ++ thenInstrs ++ [.Label endLabel]
  | .If cond thenStmt (some elseStmt) => do
      let elseLabel ← makeLabel "if_else"
      let endLabel  ← makeLabel "if_end"
      let (c, condInstrs) ← emitExp cond
      let thenInstrs ← emitStatement funcName thenStmt
      let elseInstrs ← emitStatement funcName elseStmt
      return condInstrs ++ [.JumpIfZero c elseLabel] ++ thenInstrs ++
             [.Jump endLabel, .Label elseLabel] ++ elseInstrs ++ [.Label endLabel]
  | .Compound items => do
      let instrs ← items.foldlM (fun acc item => do
        return acc ++ (← emitBlockItem funcName item)) []
      return instrs
  -- Chapter 8: while loop
  -- Label(cnt) → cond → JumpIfZero(brk) → body → Jump(cnt) → Label(brk)
  | .While cond body (some base) => do
      let cntLabel := "cnt_" ++ base
      let brkLabel := "brk_" ++ base
      let (c, condInstrs) ← emitExp cond
      let bodyInstrs ← emitStatement funcName body
      return [.Label cntLabel] ++ condInstrs ++ [.JumpIfZero c brkLabel] ++
             bodyInstrs ++ [.Jump cntLabel, .Label brkLabel]
  | .While _ _ none => return []   -- unreachable: loop labeling always sets label
  -- Chapter 8: do-while loop
  -- Label(start) → body → Label(cnt) → cond → JumpIfNotZero(start) → Label(brk)
  | .DoWhile body cond (some base) => do
      let startLabel := "start_" ++ base
      let cntLabel   := "cnt_"   ++ base
      let brkLabel   := "brk_"   ++ base
      let bodyInstrs ← emitStatement funcName body
      let (c, condInstrs) ← emitExp cond
      return [.Label startLabel] ++ bodyInstrs ++ [.Label cntLabel] ++
             condInstrs ++ [.JumpIfNotZero c startLabel, .Label brkLabel]
  | .DoWhile _ _ none => return []   -- unreachable
  -- Chapter 8: for loop
  -- init → Label(start) → [cond → JumpIfZero(brk)] → body →
  -- Label(cnt) → post → Jump(start) → Label(brk)
  | .For init cond post body (some base) => do
      let startLabel := "start_" ++ base
      let cntLabel   := "cnt_"   ++ base
      let brkLabel   := "brk_"   ++ base
      let initInstrs ← emitForInit init
      let condInstrs ← match cond with
        | none   => pure []
        | some c => do
            let (v, instrs) ← emitExp c
            pure (instrs ++ [.JumpIfZero v brkLabel])
      let bodyInstrs ← emitStatement funcName body
      let postInstrs ← match post with
        | none   => pure []
        | some e => do
            let (_, instrs) ← emitExp e
            pure instrs
      return initInstrs ++ [.Label startLabel] ++ condInstrs ++ bodyInstrs ++
             [.Label cntLabel] ++ postInstrs ++ [.Jump startLabel, .Label brkLabel]
  | .For _ _ _ _ none => return []   -- unreachable
  -- Chapter 8: break and continue — annotated with the enclosing loop/switch base
  | .Break (some base)    => return [.Jump ("brk_" ++ base)]
  | .Break none           => return []   -- unreachable after loop labeling
  | .Continue (some base) => return [.Jump ("cnt_" ++ base)]
  | .Continue none        => return []   -- unreachable after loop labeling
  -- Chapter 8 extra credit: switch statement
  -- exp → jump table (compare + conditional jumps) → [Jump(brk) if no default] →
  -- body (which contains Label instructions at Case/Default sites) → Label(brk)
  | .Switch exp body (some base) cases => do
      let brkLabel := "brk_" ++ base
      let (v, expInstrs) ← emitExp exp
      -- Emit one comparison+jump per case; for default, emit an unconditional jump.
      let jumpTable ← cases.foldlM (fun acc (caseVal, caseLbl) => do
          match caseVal with
          | some n => do
              let tmp := Val.Var (← makeTemporary)
              pure (acc ++ [.Binary .Equal v (.Constant n) tmp,
                            .JumpIfNotZero tmp caseLbl])
          | none => pure (acc ++ [.Jump caseLbl])) []
      -- If there is no default clause, fall through to the break label.
      let noDefault  := cases.all (fun (v, _) => v.isSome)
      let fallThrough := if noDefault then [Instruction.Jump brkLabel] else []
      let bodyInstrs ← emitStatement funcName body
      return expInstrs ++ jumpTable ++ fallThrough ++ bodyInstrs ++ [.Label brkLabel]
  | .Switch _ _ none _ => return []   -- unreachable
  -- Chapter 8 extra credit: case and default — emit jump target label then body
  | .Case _ body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement funcName body)
  | .Case _ _ none => return []   -- unreachable
  | .Default body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement funcName body)
  | .Default _ none => return []   -- unreachable
  -- Chapter 6 extra credit: labeled statement.
  -- Prefix the user label with funcName so same-named labels in different functions
  -- don't collide in the assembled object file (e.g. "foo.end" vs "bar.end").
  | .Labeled label stmt => do
      let stmtInstrs ← emitStatement funcName stmt
      return [.Label (funcName ++ "." ++ label)] ++ stmtInstrs
  -- Chapter 6 extra credit: goto — jump to the same prefixed label.
  | .Goto label =>
      return [.Jump (funcName ++ "." ++ label)]
  | .Null => return []

/-- Translate a single block item into a list of TACKY instructions.
    `funcName` is threaded through to `emitStatement` for user-label prefixing.
    Declarations with no initializer produce no instructions.
    Declarations with an initializer emit the initializer expression and
    a `Copy` to store the result in the variable.
    Local function declarations (FD) produce no instructions at all — they
    are only needed for semantic validation, not code generation. -/
private partial def emitBlockItem (funcName : String) : AST.BlockItem → GenM (List Instruction)
  | .S stmt => emitStatement funcName stmt
  | .D decl =>
      match decl.init with
      | none   => return []
      | some e => do
          let (val, instrs) ← emitExp e
          return instrs ++ [.Copy val (.Var decl.name)]
  | .FD _ =>
      -- Local function declarations carry no code; skip them.
      return []

end

/-- Translate an AST function definition to TACKY.
    Processes all block items in order and appends a final
    `Return(Constant(0))` so that functions without an explicit return
    statement return 0 (correct for `main`) and cleanly restore the caller's
    stack frame for other functions.
    Chapter 9: preserves the renamed parameter list so CodeGen can emit
    parameter-copy instructions at function entry. -/
private def emitFunctionDef (f : AST.FunctionDef) : GenM FunctionDef := do
  -- Pass f.name to emitBlockItem so user-defined labels (Labeled/Goto) are
  -- prefixed with the function name, preventing conflicts across functions.
  let body ← f.body.foldlM (fun acc item => do
    return acc ++ (← emitBlockItem f.name item)) []
  return { name := f.name, params := f.params, body := body ++ [.Return (.Constant 0)] }

/-- Entry point for the IR generation pass.
    Chapter 9: processes all top-level items; only FunDef entries produce TACKY
    FunctionDef nodes.  FunDecl entries are silently skipped.
    The counter is GLOBAL across all functions — each function picks up where
    the previous one left off, so no two functions produce the same tmp.N name.
    `initCounter` should be the final counter value from variable resolution. -/
def emitProgram (p : AST.Program) (initCounter : Nat := 0) : Program :=
  -- Collect only the FunDef top-levels (skip declarations)
  let astFuncs := p.topLevels.filterMap fun tl =>
    match tl with
    | .FunDef fd  => some fd
    | .FunDecl _  => none
  -- Emit each function sequentially, threading the counter through
  let action : GenM (List FunctionDef) :=
    astFuncs.foldlM (fun acc fd => do
      let tackyFd ← emitFunctionDef fd
      return acc ++ [tackyFd]) []
  let (funcs, _) := action.run initCounter
  { funcs }

end Tacky
