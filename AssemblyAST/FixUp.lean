import AssemblyAST.AssemblyAST

/-
  Pass 3 of assembly generation: fix up the instruction list.

  Two transformations are applied per function:

  1. Insert AllocateStack(roundedStackBytes) at the front of the function body.
     This becomes `subq $roundedStackBytes, %rsp` in the prologue.
     The stack size is obtained from FunctionDef.stackSize (set by PseudoReplace).
     It is rounded UP to the nearest multiple of 16 so that RSP remains
     16-byte aligned after the prologue (as required by the System V ABI).

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

     e. Cmp(src, Imm(n)): cmpl's second operand (AT&T dst) can't be an immediate.
          → Mov(Imm(n), Reg(R11))
            Cmp(src, Reg(R11))

     f. Cmp(Stack(x), Stack(y)): cmpl can't use two memory operands.
          → Mov(Stack(x), Reg(R10))
            Cmp(Reg(R10), Stack(y))

  Chapter 9 additions:
    - DeallocateStack: no fix-up needed; returned as-is.
    - Push: no fix-up needed (CodeGen only emits Push(Reg) or Push(Imm);
      PseudoReplace may convert Push(Pseudo) → Push(Stack), but the x86-64
      instruction `pushq n(%rbp)` is valid so we allow it through).
    - Call: no fix-up needed; returned as-is.
    - The stack size is rounded to a multiple of 16.

  R10 is used for source fix-ups and R11 for destination fix-ups, so both
  can be applied to the same instruction without clobbering each other.
-/

namespace AssemblyAST

/-- Round `n` up to the nearest multiple of 16.
    Used to ensure the stack frame size keeps RSP 16-byte aligned after
    the prologue `subq $n, %rsp`. -/
private def roundUp16 (n : Int) : Int :=
  ((n + 15) / 16) * 16

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
  -- addl/subl/andl/orl/xorl: source and destination cannot both be memory addresses
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
  -- All other instructions need no fix-up
  | instr => [instr]

/-- Fix up a single function definition.
    1. Read the stack size from PseudoReplace (stored in `stackSize`).
    2. Round it up to a multiple of 16 for ABI alignment.
    3. Prepend `AllocateStack(rounded)` to the instruction list.
    4. Apply `fixInstr` to each instruction. -/
private def fixFunctionDef (f : FunctionDef) : FunctionDef :=
  -- Round the stack size up to maintain 16-byte alignment
  let rounded := roundUp16 f.stackSize
  -- Fix up each instruction (expanding invalid ones into multiple valid ones)
  let fixed := f.instructions.foldl (fun acc i => acc ++ fixInstr i) []
  -- Prepend AllocateStack at the front (it becomes the third prologue instruction)
  { f with instructions := .AllocateStack rounded :: fixed }

/-- Entry point for pass 3.
    Chapter 9: processes each function in the program independently.
    Each function gets its own AllocateStack based on its own pseudo count. -/
def fixUp (p : Program) : Program :=
  { p with funcs := p.funcs.map fixFunctionDef }

end AssemblyAST
