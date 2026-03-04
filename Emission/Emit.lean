import AssemblyAST.AssemblyAST

/-
  Code emission pass: converts AssemblyAST.Program to x64 AT&T-syntax assembly.

  Linux conventions:
  - Function labels are emitted as-is (no leading underscore).
  - A .section .note.GNU-stack directive is appended to mark the stack
    non-executable.

  Function prologue (emitted before the instruction list):
      pushq %rbp
      movq  %rsp, %rbp

  AllocateStack(n) emits the third prologue instruction:
      subq $n, %rsp          (64-bit; note the q suffix, not l)

  Ret emits the full epilogue:
      movq %rbp, %rsp
      popq %rbp
      ret

  Instruction formatting (Tables 3-8 and 3-9):
    Mov(src, dst)             →  movl  <src>, <dst>
    Unary(Neg, dst)           →  negl  <dst>
    Unary(Not, dst)           →  notl  <dst>
    Binary(Add, src, dst)     →  addl  <src>, <dst>
    Binary(Sub, src, dst)     →  subl  <src>, <dst>
    Binary(Mult, src, dst)    →  imull <src>, <dst>
    Idiv(operand)             →  idivl <operand>
    Cdq                       →  cdq
    AllocateStack(n)          →  subq  $n, %rsp

  Operand formatting (Table 3-10):
    Imm(n)     →  $n
    Reg(AX)    →  %eax
    Reg(DX)    →  %edx
    Reg(CX)    →  %ecx  (but %cl when used as a shift count — see emitShiftCount)
    Reg(R10)   →  %r10d
    Reg(R11)   →  %r11d
    Stack(n)   →  n(%rbp)
    Pseudo(_)  →  (illegal at this stage — should have been replaced)
-/

namespace Emission

open AssemblyAST

/-- Emit the 32-bit name of a hardware register.
    `AX`  → `%eax`  (return value; dividend low word for idiv).
    `DX`  → `%edx`  (remainder result; dividend high word for idiv).
    `R10` → `%r10d` (scratch register for source operand fix-ups).
    `R11` → `%r11d` (scratch register for destination operand fix-ups). -/
private def emitReg : Reg → String
  | .AX  => "%eax"
  | .DX  => "%edx"
  | .CX  => "%ecx"
  | .R10 => "%r10d"
  | .R11 => "%r11d"

/-- Emit an assembly operand in AT&T syntax.
    - `Imm(n)`: immediate value, prefixed with `$`.
    - `Reg(r)`: hardware register, delegated to `emitReg`.
    - `Stack(n)`: memory address at offset `n` from the frame base register
      `%rbp`, written as `n(%rbp)` (e.g. `-4(%rbp)`).
    - `Pseudo`: must never reach this stage; signals a compiler bug. -/
private def emitOperand : Operand → String
  | .Imm n    => s!"${n}"
  | .Reg r    => emitReg r
  | .Stack n  => s!"{n}(%rbp)"
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit a shift count operand.
    x64 shift instructions accept either an immediate byte (`$n`) or the
    single-byte register `%cl` (the low byte of ECX) as the count.
    When the count is `Reg(CX)` we therefore emit `%cl`, not `%ecx`. -/
private def emitShiftCount : Operand → String
  | .Reg .CX => "%cl"
  | other    => emitOperand other

/-- Emit the one-byte name of a hardware register.
    Used by `set<cc>` instructions, which write a single byte result. -/
private def emitByteReg : Reg → String
  | .AX  => "%al"
  | .DX  => "%dl"
  | .CX  => "%cl"
  | .R10 => "%r10b"
  | .R11 => "%r11b"

/-- Emit a byte-sized operand for `set<cc>` instructions.
    Only registers are valid byte operands at this stage (stack slots are
    handled by the fix-up pass via a register intermediary). -/
private def emitByteOperand : Operand → String
  | .Reg r    => emitByteReg r
  | .Stack n  => s!"{n}(%rbp)"
  | .Imm n    => s!"${n}"
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit a condition code suffix used in `j<cc>` and `set<cc>` mnemonics. -/
private def emitCondCode : CondCode → String
  | .E  => "e"
  | .NE => "ne"
  | .G  => "g"
  | .GE => "ge"
  | .L  => "l"
  | .LE => "le"

/-- Emit a single assembly instruction as an indented string.
    Binary arithmetic instructions all use 32-bit (`l`) suffixes; the sole
    exception is `AllocateStack`, which adjusts the 64-bit stack pointer and
    therefore uses a `q` suffix.
    `Ret` is emitted as a multi-line string (prologue teardown + `ret`) so that
    `String.intercalate` in `emitFunctionDef` joins it with surrounding
    instructions correctly. -/
private def emitInstruction : Instruction → String
  | .Mov src dst          => s!"    movl {emitOperand src}, {emitOperand dst}"
  | .Unary .Neg dst       => s!"    negl {emitOperand dst}"
  | .Unary .Not dst       => s!"    notl {emitOperand dst}"
  | .Binary .Add  src dst => s!"    addl {emitOperand src}, {emitOperand dst}"
  | .Binary .Sub  src dst => s!"    subl {emitOperand src}, {emitOperand dst}"
  | .Binary .Mult src dst => s!"    imull {emitOperand src}, {emitOperand dst}"
  | .Binary .And  src dst => s!"    andl {emitOperand src}, {emitOperand dst}"
  | .Binary .Or   src dst => s!"    orl {emitOperand src}, {emitOperand dst}"
  | .Binary .Xor  src dst => s!"    xorl {emitOperand src}, {emitOperand dst}"
  | .Binary .Sal  cnt dst => s!"    sall {emitShiftCount cnt}, {emitOperand dst}"
  | .Binary .Sar  cnt dst => s!"    sarl {emitShiftCount cnt}, {emitOperand dst}"
  | .Idiv operand         => s!"    idivl {emitOperand operand}"
  | .Cdq                  => "    cdq"
  | .Cmp src dst          => s!"    cmpl {emitOperand src}, {emitOperand dst}"
  | .Jmp name             => s!"    jmp .L{name}"
  | .JmpCC cc name        => s!"    j{emitCondCode cc} .L{name}"
  | .SetCC cc op          => s!"    set{emitCondCode cc} {emitByteOperand op}"
  | .Label name           => s!".L{name}:"
  | .AllocateStack n      => s!"    subq ${n}, %rsp"
  | .Ret                  => "    movq %rbp, %rsp\n    popq %rbp\n    ret"

/-- Emit a complete function definition.
    Produces the `.globl` directive, the label, the two fixed prologue
    instructions (`pushq %rbp` and `movq %rsp, %rbp`), and then all body
    instructions joined by newlines.  The `AllocateStack` instruction (if
    present) is the first body instruction and emits the `subq` that finishes
    the prologue. -/
private def emitFunctionDef (f : FunctionDef) : String :=
  let prologue := "    pushq %rbp\n    movq %rsp, %rbp"
  let instrs   := String.intercalate "\n" (f.instructions.map emitInstruction)
  s!"    .globl {f.name}\n{f.name}:\n{prologue}\n{instrs}"

/-- Entry point for the emission pass.
    Emits the single function definition followed by the GNU stack note
    section, which tells the Linux kernel that this object file does not
    require an executable stack. -/
def emitProgram (p : Program) : String :=
  let func := emitFunctionDef p.func
  s!"{func}\n    .section .note.GNU-stack,\"\",@progbits\n"

end Emission
