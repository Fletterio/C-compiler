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

     a. Mov(mem, mem): movl can't use two memory operands.
          → Mov(mem, Reg(R10))
            Mov(Reg(R10), mem)
        where `mem` is Stack(n) or Data(name).

     b. Idiv(Imm(n)): idivl can't take an immediate operand.
          → Mov(Imm(n), Reg(R10))
            Idiv(Reg(R10))

     c. Binary(Add|Sub|And|Or|Xor, mem, mem): these instructions
        can't use two memory operands.
          → Mov(mem, Reg(R10))
            Binary(op, Reg(R10), mem)

     d. Binary(Mult, src, mem): imull can't use a memory destination.
          → Mov(mem, Reg(R11))
            Binary(Mult, src, Reg(R11))
            Mov(Reg(R11), mem)

     e. Cmp(src, Imm(n)): cmpl's second operand (AT&T dst) can't be an immediate.
          → Mov(Imm(n), Reg(R11))
            Cmp(src, Reg(R11))

     f. Cmp(mem, mem): cmpl can't use two memory operands.
          → Mov(mem, Reg(R10))
            Cmp(Reg(R10), mem)

  Chapter 10 additions:
    - `Data(name)` is a memory operand (RIP-relative), subject to the same
      fix-up rules as `Stack(n)`.  Any combination of Stack or Data in a
      two-operand instruction is treated as mem-to-mem and split through a
      scratch register.
    - `AsmTopLevel.StaticVariable` items are passed through unchanged.
    - `AsmTopLevel.Function` items are processed by `fixFunctionDef` as before.

  R10 is used for source fix-ups and R11 for destination fix-ups, so both
  can be applied to the same instruction without clobbering each other.
-/

namespace AssemblyAST

/-- Round `n` up to the nearest multiple of 16.
    Used to ensure the stack frame size keeps RSP 16-byte aligned after
    the prologue `subq $n, %rsp`. -/
private def roundUp16 (n : Int) : Int :=
  ((n + 15) / 16) * 16

/-- Return true if an operand is a memory address (Stack or Data).
    Both Stack and Data operands require memory-to-memory fix-ups when
    used together in a single instruction. -/
private def isMem : Operand → Bool
  | .Stack _ => true
  | .Data _  => true
  | _        => false

/-- Rewrite a single instruction if it violates x64 encoding constraints.
    Chapter 10: Data operands are treated as memory operands throughout.
    See the module header for the full list of rewrite rules.
    Returns a singleton for instructions that need no fix-up, or a two- or
    three-instruction sequence for those that do. -/
private def fixInstr : Instruction → List Instruction
  -- movl: source and destination cannot both be memory addresses
  | .Mov src dst =>
      if isMem src && isMem dst then
        [.Mov src (.Reg .R10), .Mov (.Reg .R10) dst]
      else
        [.Mov src dst]
  -- idivl: operand cannot be an immediate value; move it to R10D first
  | .Idiv (.Imm n) =>
      [.Mov (.Imm n) (.Reg .R10), .Idiv (.Reg .R10)]
  -- addl/subl/andl/orl/xorl: source and destination cannot both be memory
  | .Binary .Add src dst =>
      if isMem src && isMem dst then
        [.Mov src (.Reg .R10), .Binary .Add (.Reg .R10) dst]
      else
        [.Binary .Add src dst]
  | .Binary .Sub src dst =>
      if isMem src && isMem dst then
        [.Mov src (.Reg .R10), .Binary .Sub (.Reg .R10) dst]
      else
        [.Binary .Sub src dst]
  | .Binary .And src dst =>
      if isMem src && isMem dst then
        [.Mov src (.Reg .R10), .Binary .And (.Reg .R10) dst]
      else
        [.Binary .And src dst]
  | .Binary .Or src dst =>
      if isMem src && isMem dst then
        [.Mov src (.Reg .R10), .Binary .Or (.Reg .R10) dst]
      else
        [.Binary .Or src dst]
  | .Binary .Xor src dst =>
      if isMem src && isMem dst then
        [.Mov src (.Reg .R10), .Binary .Xor (.Reg .R10) dst]
      else
        [.Binary .Xor src dst]
  -- imull: destination cannot be a memory address; use R11D as a temporary
  | .Binary .Mult src dst =>
      if isMem dst then
        [.Mov dst (.Reg .R11),
         .Binary .Mult src (.Reg .R11),
         .Mov (.Reg .R11) dst]
      else
        [.Binary .Mult src dst]
  -- cmpl: second operand (AT&T dst) cannot be an immediate; move it to R11D
  | .Cmp src (.Imm n) =>
      [.Mov (.Imm n) (.Reg .R11), .Cmp src (.Reg .R11)]
  -- cmpl: source and destination cannot both be memory addresses; use R10D
  | .Cmp src dst =>
      if isMem src && isMem dst then
        [.Mov src (.Reg .R10), .Cmp (.Reg .R10) dst]
      else
        [.Cmp src dst]
  -- All other instructions need no fix-up
  | instr => [instr]

/-- Fix up a single function definition.
    1. Read the stack size from PseudoReplace (stored in `stackSize`).
    2. Round it up to a multiple of 16 for ABI alignment.
    3. Prepend `AllocateStack(rounded)` to the instruction list.
    4. Apply `fixInstr` to each instruction. -/
private def fixFunctionDef (f : FunctionDef) : FunctionDef :=
  let rounded := roundUp16 f.stackSize
  let fixed := f.instructions.foldl (fun acc i => acc ++ fixInstr i) []
  { f with instructions := .AllocateStack rounded :: fixed }

/-- Entry point for pass 3.
    Chapter 10: processes each AsmTopLevel item:
    - `Function(fd)`: apply AllocateStack insertion and instruction fix-ups.
    - `StaticVariable(...)`: pass through unchanged (no instructions). -/
def fixUp (p : Program) : Program :=
  let topLevels := p.topLevels.map fun tl =>
    match tl with
    | .Function fd            => AsmTopLevel.Function (fixFunctionDef fd)
    | sv@(.StaticVariable ..) => sv
  { topLevels }

end AssemblyAST
