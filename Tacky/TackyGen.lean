import AST.AST
import Tacky.Tacky
import Semantics.SymbolTable

/-
  IR generation pass: converts AST.Program → Tacky.Program.

  Chapter 10 additions:
    - Takes a `SymbolTable` as an additional parameter.
    - For each function definition in the AST, emits a TACKY `Function` with
      the `global` flag derived from the symbol table.
    - After processing all AST function definitions, scans the symbol table and
      generates `StaticVariable` top-level items:
        - `Static(Initial(n), global)` → `StaticVariable(name, global, n)`
        - `Static(Tentative, global)`  → `StaticVariable(name, global, 0)`
        - `Static(NoInitializer, _)`   → skip (extern, not defined here)
        - `FunAttr(_, _)`              → skip (function, not a variable)
        - `Local`                      → skip (automatic variable, on the stack)
    - Local static variables (renamed to `<orig>.<n>`) appear in the symbol
      table under their renamed names and are emitted as non-global static vars.
    - File-scope static variables appear under their original names.

  The counter is GLOBAL across all functions (same as before), ensuring that
  every generated temporary and label name is unique program-wide.
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
      (v is already renamed — static vars use their unique name, which
       PseudoReplace will map to a Data/RIP-relative operand.)
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
      let argResults ← args.mapM emitExp
      let argInstrs := argResults.foldl (fun acc (_, instrs) => acc ++ instrs) []
      let argVals   := argResults.map (fun (v, _) => v)
      let dst := Val.Var (← makeTemporary)
      return (dst, argInstrs ++ [.FunCall name argVals dst])

/-- Translate a `for`-loop initial clause into TACKY instructions.
    A declaration initializer emits the expression and a `Copy` into the
    renamed variable.  An expression clause emits the expression and discards
    its result.  An absent clause emits nothing.

    Chapter 10: local-static declarations have no initializer in the AST body
    (the init was removed by VarResolution); `InitDecl` with `none` init → empty. -/
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
  `Compound` constructor.
-/
mutual

/-- Translate an AST statement into a flat list of TACKY instructions.
    `funcName` is the name of the enclosing function, used to make
    user-defined labels unique across functions.

    Chapter 10: no changes to statement lowering.  Static variables are
    addressed via `Var(uniqueName)` in expressions; PseudoReplace maps them
    to `Data` operands instead of `Stack` slots.  Initializers for static
    local variables are NOT emitted here (they are emitted as `StaticVariable`
    top-level items in TackyGen instead). -/
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
  | .While cond body (some base) => do
      let cntLabel := "cnt_" ++ base
      let brkLabel := "brk_" ++ base
      let (c, condInstrs) ← emitExp cond
      let bodyInstrs ← emitStatement funcName body
      return [.Label cntLabel] ++ condInstrs ++ [.JumpIfZero c brkLabel] ++
             bodyInstrs ++ [.Jump cntLabel, .Label brkLabel]
  | .While _ _ none => return []   -- unreachable: loop labeling always sets label
  -- Chapter 8: do-while loop
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
  -- Chapter 8: break and continue
  | .Break (some base)    => return [.Jump ("brk_" ++ base)]
  | .Break none           => return []   -- unreachable after loop labeling
  | .Continue (some base) => return [.Jump ("cnt_" ++ base)]
  | .Continue none        => return []   -- unreachable after loop labeling
  -- Chapter 8 extra credit: switch statement
  | .Switch exp body (some base) cases => do
      let brkLabel := "brk_" ++ base
      let (v, expInstrs) ← emitExp exp
      let jumpTable ← cases.foldlM (fun acc (caseVal, caseLbl) => do
          match caseVal with
          | some n => do
              let tmp := Val.Var (← makeTemporary)
              pure (acc ++ [.Binary .Equal v (.Constant n) tmp,
                            .JumpIfNotZero tmp caseLbl])
          | none => pure (acc ++ [.Jump caseLbl])) []
      let noDefault  := cases.all (fun (v, _) => v.isSome)
      let fallThrough := if noDefault then [Instruction.Jump brkLabel] else []
      let bodyInstrs ← emitStatement funcName body
      return expInstrs ++ jumpTable ++ fallThrough ++ bodyInstrs ++ [.Label brkLabel]
  | .Switch _ _ none _ => return []   -- unreachable
  -- Chapter 8 extra credit: case and default
  | .Case _ body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement funcName body)
  | .Case _ _ none => return []   -- unreachable
  | .Default body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement funcName body)
  | .Default _ none => return []   -- unreachable
  -- Chapter 6 extra credit: labeled statement and goto
  | .Labeled label stmt => do
      let stmtInstrs ← emitStatement funcName stmt
      return [.Label (funcName ++ "." ++ label)] ++ stmtInstrs
  | .Goto label =>
      return [.Jump (funcName ++ "." ++ label)]
  | .Null => return []

/-- Translate a single block item into a list of TACKY instructions.

    Chapter 10: local static variables (`static int x = n`) have their
    initializer removed by VarResolution (replaced with `none`).  So
    `InitDecl { init := none }` for a static var produces no instructions here
    — the variable is initialized via its `StaticVariable` top-level entry.
    The variable is still referenced by name in expressions; PseudoReplace
    will map the name to a `Data` operand. -/
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
    Chapter 10: the `global` flag is taken from the symbol table (passed in
    from the caller).  This flag controls whether the function's symbol is
    exported (`.globl` directive in the emitter). -/
private def emitFunctionDef (f : AST.FunctionDef) (isGlobal : Bool) : GenM FunctionDef := do
  let body ← f.body.foldlM (fun acc item => do
    return acc ++ (← emitBlockItem f.name item)) []
  return { name := f.name, params := f.params,
           body := body ++ [.Return (.Constant 0)],
           global := isGlobal }

/-- Scan the symbol table and collect all static variable entries as
    `TackyTopLevel.StaticVariable` items.

    Rules:
      - `Static(Initial(n), global)` → `StaticVariable(name, global, n)`
      - `Static(Tentative, global)`  → `StaticVariable(name, global, 0)`
      - `Static(NoInitializer, _)`   → skip (extern ref, no storage in this TU)
      - `FunAttr(_, _)`              → skip (function entry)
      - `Local`                      → skip (automatic variable, on the stack) -/
private def emitStaticVars (symTable : Semantics.SymbolTable) : List TackyTopLevel :=
  symTable.filterMap fun (name, entry) =>
    match entry.attrs with
    | .Static (.Initial n) isGlobal  => some (.StaticVariable name isGlobal n)
    | .Static .Tentative   isGlobal  => some (.StaticVariable name isGlobal 0)
    | .Static .NoInitializer _       => none   -- extern, not defined here
    | .FunAttr _ _                   => none   -- function entry
    | .Local                         => none   -- automatic variable

/-- Entry point for the IR generation pass.
    Chapter 10:
      - Takes a `SymbolTable` to determine function linkage (`global` flag) and
        to generate `StaticVariable` top-level items.
      - Processes all `FunDef` top-level items.
      - Skips `FunDecl` and `VarDecl` entries (no code to generate).
      - After emitting functions, scans the symbol table to emit static vars.
    The counter is GLOBAL across all functions. -/
def emitProgram (p : AST.Program) (symTable : Semantics.SymbolTable)
    (initCounter : Nat := 0) : Program :=
  -- Collect only the FunDef top-levels (skip FunDecl and VarDecl)
  let astFuncs := p.topLevels.filterMap fun tl =>
    match tl with
    | .FunDef fd  => some fd
    | .FunDecl _  => none
    | .VarDecl _  => none
  -- Emit each function sequentially, threading the counter through
  let action : GenM (List TackyTopLevel) :=
    astFuncs.foldlM (fun acc fd => do
      -- Determine global flag from symbol table
      let isGlobal : Bool := match Semantics.lookupSym symTable fd.name with
        | some { attrs := .FunAttr _ g, .. } => g
        | _ => true  -- default to global if not found (shouldn't happen)
      let tackyFd ← emitFunctionDef fd isGlobal
      return acc ++ [.Function tackyFd]) []
  let (funcItems, _) := action.run initCounter
  -- Append StaticVariable items from the symbol table
  let staticItems := emitStaticVars symTable
  -- Functions first, then static variables (order matters for readability)
  { topLevels := funcItems ++ staticItems }

end Tacky
