import AssemblyAST.AssemblyAST

/-
  Code emission pass: converts AssemblyAST.Program to x64 AT&T-syntax assembly.

  Linux conventions:
  - Function labels are emitted as-is (no leading underscore).
  - A .section .note.GNU-stack directive is appended to mark the stack
    non-executable.
  - External function calls use the `@PLT` suffix (Position-Independent Code
    compatible; required for functions not defined in this translation unit).

  Function prologue (emitted before the instruction list):
      pushq %rbp
      movq  %rsp, %rbp

  AllocateStack(n) emits the third prologue instruction:
      subq $n, %rsp          (64-bit; note the q suffix, not l)

  DeallocateStack(n) emits:
      addq $n, %rsp          (Chapter 9: reclaim space used for stack arguments)

  Push(operand) emits:
      pushq <64-bit operand> (Chapter 9: pass argument on stack)

  Call(name) emits:
      call name              (if name is locally defined)
      call name@PLT          (if name is external on Linux)

  Ret emits the full epilogue:
      movq %rbp, %rsp
      popq %rbp
      ret

  Instruction formatting:
    Mov(src, dst)             →  movl  <src>, <dst>
    Unary(Neg, dst)           →  negl  <dst>
    Unary(Not, dst)           →  notl  <dst>
    Binary(Add, src, dst)     →  addl  <src>, <dst>
    Binary(Sub, src, dst)     →  subl  <src>, <dst>
    Binary(Mult, src, dst)    →  imull <src>, <dst>
    Idiv(operand)             →  idivl <operand>
    Cdq                       →  cdq
    AllocateStack(n)          →  subq  $n, %rsp
    DeallocateStack(n)        →  addq  $n, %rsp
    Push(operand)             →  pushq <64-bit operand>
    Call(name)                →  call  name  or  call  name@PLT

  Operand formatting:
    Imm(n)     →  $n
    Reg(AX)    →  %eax  / %rax  / %al
    Reg(DX)    →  %edx  / %rdx  / %dl
    Reg(CX)    →  %ecx  / %rcx  / %cl
    Reg(DI)    →  %edi  / %rdi  / %dil
    Reg(SI)    →  %esi  / %rsi  / %sil
    Reg(R8)    →  %r8d  / %r8   / %r8b
    Reg(R9)    →  %r9d  / %r9   / %r9b
    Reg(R10)   →  %r10d / %r10  / %r10b
    Reg(R11)   →  %r11d / %r11  / %r11b
    Stack(n)   →  n(%rbp)
    Pseudo(_)  →  (illegal at this stage — should have been replaced)
-/

namespace Emission

open AssemblyAST

-- ---------------------------------------------------------------------------
-- Register name emission (three sizes)
-- ---------------------------------------------------------------------------

/-- Emit the 32-bit (4-byte) name of a hardware register.
    Used for `movl`, `addl`, `subl`, `imull`, `cmpl`, etc. (the default size). -/
private def emitReg4 : Reg → String
  | .AX  => "%eax"
  | .DX  => "%edx"
  | .CX  => "%ecx"
  | .DI  => "%edi"
  | .SI  => "%esi"
  | .R8  => "%r8d"
  | .R9  => "%r9d"
  | .R10 => "%r10d"
  | .R11 => "%r11d"

/-- Emit the 64-bit (8-byte) name of a hardware register.
    Used for `pushq`, `subq`, `addq`, `movq`, and other 64-bit operations.
    The System V AMD64 ABI requires pushing full 64-bit values. -/
private def emitReg8 : Reg → String
  | .AX  => "%rax"
  | .DX  => "%rdx"
  | .CX  => "%rcx"
  | .DI  => "%rdi"
  | .SI  => "%rsi"
  | .R8  => "%r8"
  | .R9  => "%r9"
  | .R10 => "%r10"
  | .R11 => "%r11"

/-- Emit the 8-bit (1-byte) name of a hardware register.
    Used by `set<cc>` instructions, which write a single byte result,
    and by `%cl` in shift instructions. -/
private def emitReg1 : Reg → String
  | .AX  => "%al"
  | .DX  => "%dl"
  | .CX  => "%cl"
  | .DI  => "%dil"
  | .SI  => "%sil"
  | .R8  => "%r8b"
  | .R9  => "%r9b"
  | .R10 => "%r10b"
  | .R11 => "%r11b"

-- ---------------------------------------------------------------------------
-- Operand emission
-- ---------------------------------------------------------------------------

/-- Emit an assembly operand in AT&T syntax using 32-bit register names.
    - `Imm(n)`: immediate value, prefixed with `$`.
    - `Reg(r)`: hardware register name (32-bit for normal instructions).
    - `Stack(n)`: memory address at offset `n` from the frame base register
      `%rbp`, written as `n(%rbp)` (e.g. `-4(%rbp)`).
    - `Pseudo`: must never reach this stage; signals a compiler bug. -/
private def emitOperand : Operand → String
  | .Imm n    => s!"${n}"
  | .Reg r    => emitReg4 r
  | .Stack n  => s!"{n}(%rbp)"
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit an operand using 64-bit register names.
    Used for `pushq` which operates on 64-bit values. -/
private def emitOperand8 : Operand → String
  | .Imm n    => s!"${n}"
  | .Reg r    => emitReg8 r
  | .Stack n  => s!"{n}(%rbp)"
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit a shift count operand.
    x64 shift instructions accept either an immediate byte (`$n`) or the
    single-byte register `%cl` (the low byte of ECX) as the count.
    When the count is `Reg(CX)` we therefore emit `%cl`, not `%ecx`. -/
private def emitShiftCount : Operand → String
  | .Reg .CX => "%cl"
  | other    => emitOperand other

/-- Emit a byte-sized operand for `set<cc>` instructions.
    Only registers are valid byte operands at this stage (stack slots are
    handled by the fix-up pass via a register intermediary). -/
private def emitByteOperand : Operand → String
  | .Reg r    => emitReg1 r
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

-- ---------------------------------------------------------------------------
-- Instruction emission
-- ---------------------------------------------------------------------------

/-- Emit a single assembly instruction as an indented string.
    Binary arithmetic instructions all use 32-bit (`l`) suffixes.
    `AllocateStack` and `DeallocateStack` use 64-bit (`q`) suffix since they
    adjust the 64-bit stack pointer.
    `Push` uses `pushq` (64-bit operand).
    `Call` uses `call name@PLT` if the function is external (not in localDefs),
    or `call name` if it is locally defined.
    `Ret` is emitted as a multi-line string (prologue teardown + `ret`). -/
private def emitInstruction (localDefs : List String) : Instruction → String
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
  | .DeallocateStack n    => s!"    addq ${n}, %rsp"
  | .Push operand         => s!"    pushq {emitOperand8 operand}"
  | .Call name            =>
      -- On Linux, use @PLT suffix for external functions.
      -- Functions defined in this translation unit are called directly.
      if localDefs.contains name then
        s!"    call {name}"
      else
        s!"    call {name}@PLT"
  | .Ret                  => "    movq %rbp, %rsp\n    popq %rbp\n    ret"

-- ---------------------------------------------------------------------------
-- Function and program emission
-- ---------------------------------------------------------------------------

/-- Emit a complete function definition.
    Produces the `.globl` directive, the label, the two fixed prologue
    instructions (`pushq %rbp` and `movq %rsp, %rbp`), and then all body
    instructions joined by newlines.  The `AllocateStack` instruction (if
    present) is the first body instruction and emits the `subq` that finishes
    the prologue. -/
private def emitFunctionDef (localDefs : List String) (f : FunctionDef) : String :=
  let prologue := "    pushq %rbp\n    movq %rsp, %rbp"
  let instrs   := String.intercalate "\n"
                    (f.instructions.map (emitInstruction localDefs))
  s!"    .globl {f.name}\n{f.name}:\n{prologue}\n{instrs}"

/-- Entry point for the emission pass.
    Chapter 9: emits all function definitions, separated by blank lines.
    The set of locally-defined function names is computed from the program so
    that `Call` instructions for local functions are emitted without `@PLT`,
    while calls to external functions (like printf, putchar, etc.) get `@PLT`.
    Appends the GNU stack note section at the end. -/
def emitProgram (p : Program) : String :=
  -- Collect the names of all locally-defined functions
  let localDefs := p.funcs.map (fun f => f.name)
  -- Emit each function definition, separated by blank lines
  let funcStrings := p.funcs.map (emitFunctionDef localDefs)
  let funcSection := String.intercalate "\n" funcStrings
  s!"{funcSection}\n    .section .note.GNU-stack,\"\",@progbits\n"

end Emission
