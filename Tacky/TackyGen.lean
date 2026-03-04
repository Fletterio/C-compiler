import AST.AST
import Tacky.Tacky

/-
  IR generation pass: converts AST.Program → Tacky.Program.

  Each AST expression is flattened into a sequence of TACKY instructions
  that leave the result in a fresh temporary variable. Constants are passed
  through directly without generating any instructions.

  A single `Nat` counter is shared by `makeTemporary` and `makeLabel` to
  guarantee that every generated name is unique within the function.
  Temporary variables are named "tmp.N" and labels are named "<base>.N",
  where N is the current counter value. Periods are not valid in C identifiers,
  so these names cannot clash with any user-defined identifier.
-/

namespace Tacky

/-- The monad used during IR generation: a state monad carrying a `Nat`
    counter that is incremented each time a new temporary variable is created.
    Using a monad lets every helper thread the counter implicitly rather than
    passing it as an explicit argument. -/
private abbrev GenM := StateM Nat

/-- Allocate a fresh temporary variable name.
    Reads the current counter value, increments it, and returns a name of the
    form `"tmp.N"`.  The period makes these names syntactically distinct from
    any user-defined C identifier. -/
private def makeTemporary : GenM String := do
  let n ← get
  modify (· + 1)
  return s!"tmp.{n}"

/-- Allocate a fresh label with the given descriptive base name.
    Returns a name of the form `"<base>.N"` where N is the current counter
    value; the counter is then incremented.  The same counter is shared with
    `makeTemporary` so all generated names are globally unique within the
    function.  The period satisfies the assembler's identifier rules while
    ensuring no clash with user-defined C identifiers. -/
private def makeLabel (base : String) : GenM String := do
  let n ← get
  modify (· + 1)
  return s!"{base}.{n}"

/-- Translate an AST unary operator to its TACKY equivalent.
    The operators have the same names in both IRs, so this is a direct
    one-to-one mapping. -/
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

    - `Constant(n)`: no instructions; value is `Tacky.Val.Constant n` directly.
    - `Unary(op, inner)`: flatten `inner`, allocate a temporary, emit `Unary`.
    - `Binary(And, e1, e2)`: short-circuit logical AND via `JumpIfZero`.
      Evaluates e1; if zero, jumps to `false_label` (skips e2).
      Evaluates e2; if zero, jumps to `false_label`.
      Otherwise copies 1 into result and jumps to `end_label`.
      At `false_label`, copies 0. Result is always 0 or 1.
    - `Binary(Or, e1, e2)`: short-circuit logical OR via `JumpIfNotZero`.
      Evaluates e1; if nonzero, jumps to `true_label` (skips e2).
      Evaluates e2; if nonzero, jumps to `true_label`.
      Otherwise copies 0 into result and jumps to `end_label`.
      At `true_label`, copies 1. Result is always 0 or 1.
    - `Binary(op, e1, e2)`: flatten both operands (left first), allocate a
      temporary, emit a `Binary` instruction.

    Labels and temporaries share the same counter so all generated names are
    unique.  Instructions accumulate in evaluation order so each source is
    defined before it is used. -/
private def emitExp : AST.Exp → GenM (Val × List Instruction)
  | .Constant n     => return (.Constant n, [])
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

/-- Translate an AST statement into a flat list of TACKY instructions.
    For `Return(e)`, calls `emitExp` to flatten the return value expression,
    then appends a `Return` instruction that returns the resulting `Val`. -/
private def emitStatement : AST.Statement → GenM (List Instruction)
  | .Return e => do
      let (v, instrs) ← emitExp e
      return instrs ++ [.Return v]

/-- Translate an AST function definition to TACKY.
    Runs the `GenM` action produced by `emitStatement` with an initial counter
    of 0 via `.run 0`, discarding the final counter value (we only need the
    emitted instructions, not what number the counter reached).  The counter
    resets to 0 for each function, so temporary names are unique within a
    function but may repeat across functions. -/
private def emitFunctionDef (f : AST.FunctionDef) : FunctionDef :=
  let (body, _) := (emitStatement f.body).run 0
  { name := f.name, body }

/-- Entry point for the IR generation pass.
    Wraps `emitFunctionDef` at the top-level `Program` node. -/
def emitProgram (p : AST.Program) : Program :=
  { func := emitFunctionDef p.func }

end Tacky
