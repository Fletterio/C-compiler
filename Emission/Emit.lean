import AssemblyAST.AssemblyAST

/-
  Code emission pass: converts AssemblyAST.Program to x64 AT&T-syntax assembly.

  Chapter 10 additions:
    - `Data(name)` operands: emitted as `name(%rip)` (RIP-relative addressing).
    - `StaticVariable(name, global, init)`: emitted as a set of assembly
      directives in the `.data` (nonzero init) or `.bss` (zero init) section:
        global, nonzero:   .globl name / .data / .align 4 / name: / .long init
        global, zero:      .globl name / .bss  / .align 4 / name: / .zero 4
        local, nonzero:                  .data / .align 4 / name: / .long init
        local, zero:                     .bss  / .align 4 / name: / .zero 4
    - Function definitions:
        - A `.text` directive is emitted before each function (required now
          that other sections are also emitted by this pass).
        - The `.globl` directive is emitted only when `FunctionDef.global` is
          true (internal-linkage functions declared `static` omit it).

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
      subq $n, %rsp

  DeallocateStack(n) emits:
      addq $n, %rsp

  Push(operand) emits:
      pushq <64-bit operand>

  Call(name) emits:
      call name       (if name is locally defined)
      call name@PLT   (if name is external on Linux)

  Ret emits the full epilogue:
      movq %rbp, %rsp
      popq %rbp
      ret

  Operand formatting:
    Imm(n)       →  $n
    Reg(AX)      →  %eax  / %rax  / %al
    Stack(n)     →  n(%rbp)
    Data(name)   →  name(%rip)   [Chapter 10: RIP-relative]
    Pseudo(_)    →  (illegal at this stage — should have been replaced)
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
    Used for `pushq`, `subq`, `addq`, `movq`, and other 64-bit operations. -/
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
    - `Stack(n)`: memory address at offset `n` from `%rbp`.
    - `Data(name)`: Chapter 10 — RIP-relative address `name(%rip)`.
    - `Pseudo`: must never reach this stage; signals a compiler bug. -/
private def emitOperand : Operand → String
  | .Imm n    => s!"${n}"
  | .Reg r    => emitReg4 r
  | .Stack n  => s!"{n}(%rbp)"
  | .Data nm  => s!"{nm}(%rip)"   -- Chapter 10: RIP-relative static variable
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit an operand using 64-bit register names.
    Used for `pushq` which operates on 64-bit values. -/
private def emitOperand8 : Operand → String
  | .Imm n    => s!"${n}"
  | .Reg r    => emitReg8 r
  | .Stack n  => s!"{n}(%rbp)"
  | .Data nm  => s!"{nm}(%rip)"
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit a shift count operand.
    x64 shift instructions accept either an immediate byte (`$n`) or the
    single-byte register `%cl` (the low byte of ECX) as the count.
    When the count is `Reg(CX)` we therefore emit `%cl`, not `%ecx`. -/
private def emitShiftCount : Operand → String
  | .Reg .CX => "%cl"
  | other    => emitOperand other

/-- Emit a byte-sized operand for `set<cc>` instructions. -/
private def emitByteOperand : Operand → String
  | .Reg r    => emitReg1 r
  | .Stack n  => s!"{n}(%rbp)"
  | .Data nm  => s!"{nm}(%rip)"
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
    `localDefs` is the list of function names defined in this translation unit,
    used to decide whether to suffix `@PLT` on `call` instructions. -/
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
      if localDefs.contains name then
        s!"    call {name}"
      else
        s!"    call {name}@PLT"
  | .Ret                  => "    movq %rbp, %rsp\n    popq %rbp\n    ret"

-- ---------------------------------------------------------------------------
-- Top-level emission
-- ---------------------------------------------------------------------------

/-- Emit a complete function definition.
    Chapter 10:
    - Emits `.text` before the function label (required now that we also emit
      `.data`/`.bss` sections for static variables).
    - Emits `.globl name` only when `FunctionDef.global` is true (i.e. the
      function has external linkage).  Internal-linkage (`static`) functions
      omit this directive.
    - Then emits the label, prologue, and instruction list. -/
private def emitFunctionDef (localDefs : List String) (f : FunctionDef) : String :=
  let globalDirective := if f.global then s!"    .globl {f.name}\n" else ""
  let prologue := "    pushq %rbp\n    movq %rsp, %rbp"
  let instrs   := String.intercalate "\n"
                    (f.instructions.map (emitInstruction localDefs))
  s!"{globalDirective}    .text\n{f.name}:\n{prologue}\n{instrs}"

/-- Emit a static variable definition as assembly directives.
    Chapter 10: static variables are placed in `.data` (nonzero initializer) or
    `.bss` (zero initializer).  On Linux we use `.align 4` (2^2 = 4 bytes).

    `global = true, init ≠ 0`:
        .globl name
        .data
        .align 4
        name:
        .long init

    `global = true, init = 0`:
        .globl name
        .bss
        .align 4
        name:
        .zero 4

    `global = false, init ≠ 0`:
        .data
        .align 4
        name:
        .long init

    `global = false, init = 0`:
        .bss
        .align 4
        name:
        .zero 4
-/
private def emitStaticVariable (name : String) (global : Bool) (init : Int) : String :=
  let globalDirective := if global then s!"    .globl {name}\n" else ""
  if init != 0 then
    s!"{globalDirective}    .data\n    .align 4\n{name}:\n    .long {init}"
  else
    s!"{globalDirective}    .bss\n    .align 4\n{name}:\n    .zero 4"

/-- Entry point for the emission pass.
    Chapter 10: emits all top-level items (functions and static variables).
    - Collects locally-defined function names for `@PLT` decisions.
    - Emits each top-level item separated by blank lines.
    - Appends the GNU stack note section at the end. -/
def emitProgram (p : Program) : String :=
  -- Collect the names of all locally-defined functions (for @PLT decisions)
  let localDefs := p.topLevels.filterMap fun tl =>
    match tl with
    | .Function f          => some f.name
    | .StaticVariable ..   => none
  -- Emit each top-level item
  let topLevelStrings := p.topLevels.map fun tl =>
    match tl with
    | .Function f                   => emitFunctionDef localDefs f
    | .StaticVariable name glob init => emitStaticVariable name glob init
  let body := String.intercalate "\n" topLevelStrings
  s!"{body}\n    .section .note.GNU-stack,\"\",@progbits\n"

end Emission
