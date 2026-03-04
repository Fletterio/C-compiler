import AssemblyAST.AssemblyAST

/-
  Pass 3 of assembly generation: fix up the instruction list.

  Two transformations are applied:

  1. Insert AllocateStack(stackBytes) at the front of the function body.
     This becomes `subq $stackBytes, %rsp` in the prologue.

  2. Rewrite invalid instructions:

     a. Mov(Stack(x), Stack(y)): movl can't use two memory operands.
          → Mov(Stack(x), Reg(R10))
            Mov(Reg(R10), Stack(y))

     b. Idiv(Imm(n)): idivl can't take an immediate operand.
          → Mov(Imm(n), Reg(R10))
            Idiv(Reg(R10))

     c. Binary(Add|Sub|And|Or|Xor, Stack(x), Stack(y)): these instructions
        can't use two memory operands.
          → Mov(Stack(x), Reg(R10))
            Binary(op, Reg(R10), Stack(y))

     d. Binary(Mult, src, Stack(y)): imull can't use a memory destination.
          → Mov(Stack(y), Reg(R11))
            Binary(Mult, src, Reg(R11))
            Mov(Reg(R11), Stack(y))

  R10 is used for source fix-ups and R11 for destination fix-ups, so both
  can be applied to the same instruction without clobbering each other.
-/

namespace AssemblyAST

/-- Rewrite a single instruction if it violates x64 encoding constraints.
    See the module header for a full list of rewrite rules.
    Returns a singleton for instructions that need no fix-up, or a two- or
    three-instruction sequence for those that do. -/
private def fixInstr : Instruction → List Instruction
  -- movl: source and destination cannot both be memory addresses
  | .Mov (.Stack x) (.Stack y) =>
      [.Mov (.Stack x) (.Reg .R10), .Mov (.Reg .R10) (.Stack y)]
  -- idivl: operand cannot be an immediate value; move it to R10D first
  | .Idiv (.Imm n) =>
      [.Mov (.Imm n) (.Reg .R10), .Idiv (.Reg .R10)]
  -- addl/subl/andl/orl/xorl: source and destination cannot both be memory addresses; use R10D
  | .Binary .Add (.Stack x) (.Stack y) =>
      [.Mov (.Stack x) (.Reg .R10), .Binary .Add (.Reg .R10) (.Stack y)]
  | .Binary .Sub (.Stack x) (.Stack y) =>
      [.Mov (.Stack x) (.Reg .R10), .Binary .Sub (.Reg .R10) (.Stack y)]
  | .Binary .And (.Stack x) (.Stack y) =>
      [.Mov (.Stack x) (.Reg .R10), .Binary .And (.Reg .R10) (.Stack y)]
  | .Binary .Or (.Stack x) (.Stack y) =>
      [.Mov (.Stack x) (.Reg .R10), .Binary .Or (.Reg .R10) (.Stack y)]
  | .Binary .Xor (.Stack x) (.Stack y) =>
      [.Mov (.Stack x) (.Reg .R10), .Binary .Xor (.Reg .R10) (.Stack y)]
  -- imull: destination cannot be a memory address; use R11D as a temporary
  | .Binary .Mult src (.Stack y) =>
      [.Mov (.Stack y) (.Reg .R11),
       .Binary .Mult src (.Reg .R11),
       .Mov (.Reg .R11) (.Stack y)]
  -- cmpl: second operand (AT&T dst) cannot be an immediate; move it to R11D
  | .Cmp src (.Imm n) =>
      [.Mov (.Imm n) (.Reg .R11), .Cmp src (.Reg .R11)]
  -- cmpl: source and destination cannot both be memory addresses; use R10D
  | .Cmp (.Stack x) (.Stack y) =>
      [.Mov (.Stack x) (.Reg .R10), .Cmp (.Reg .R10) (.Stack y)]
  | instr => [instr]

/-- Entry point for pass 3.
    Prepends `AllocateStack(stackBytes)` — which will emit `subq $n, %rsp` in
    the function prologue — then runs `fixInstr` over every instruction to
    eliminate any remaining invalid memory-to-memory moves.
    `stackBytes` comes from pass 2 and equals the total bytes reserved for
    temporary variables. -/
def fixUp (stackBytes : Nat) (p : Program) : Program :=
  let f := p.func
  let fixed := f.instructions.foldl (fun acc i => acc ++ fixInstr i) []
  { p with func := { f with instructions := .AllocateStack stackBytes :: fixed } }

end AssemblyAST
