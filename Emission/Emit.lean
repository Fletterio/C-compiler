import AssemblyAST.AssemblyAST

/-
  Code emission pass: converts AssemblyAST.Program to x64 AT&T-syntax assembly.

  Chapter 13 additions:
    - XMM registers: `emitRegXmm` gives `%xmm0`..`%xmm15`.
    - `emitXmmOperand`: emits XMM/memory operands for SSE instructions.
    - `emitOperandForType` dispatches to `emitXmmOperand` for `.Double`.
    - New instructions emitted:
        `Movsd src, dst`           → `movsd src, dst`
        `Binary .Double .Add`      → `addsd`
        `Binary .Double .Sub`      → `subsd`
        `Binary .Double .Mult`     → `mulsd`
        `Binary .Double .DivDouble`→ `divsd`
        `Cvtsi2sd Longword src dst`→ `cvtsi2sdl src, dst`
        `Cvtsi2sd Quadword src dst`→ `cvtsi2sdq src, dst`
        `Cvttsd2si Longword src dst`→ `cvttsd2sil src, dst`
        `Cvttsd2si Quadword src dst`→ `cvttsd2siq src, dst`
        `Xorpd src dst`            → `xorpd src, dst`
        `Comisd src dst`           → `comisd src, dst`
    - `StaticVariable DoubleInit(f)`:
        `.data / .align 8 / name: / .double f`  (or `.bss / .zero 8` if 0)
    - `StaticConstant(name, align, init)`:
        `.section .rodata / .align N / name: / .double f`
        (read-only; never exported with `.globl`).

  Chapter 11 additions:
    - `emitReg4/8/1` extended with `SP`: `%esp` / `%rsp` / `%spl`.
    - `emitOperand` and `emitOperand8` unchanged (Data → `name(%rip)` etc.).
    - `emitInstruction` now pattern-matches on typed instructions:
        `Mov(Longword, ...)` → `movl`
        `Mov(Quadword, ...)` → `movq`
        `Movsx src, dst`     → `movslq`
        `Unary(Longword, Neg, ...)` → `negl`, `(Quadword, ...)` → `negq`, etc.
        `Binary(Longword, Add, ...)` → `addl`, `(Quadword, ...)` → `addq`, etc.
        `Idiv(Longword, ...)`  → `idivl`, `(Quadword, ...)` → `idivq`
        `Cdq(Longword)`        → `cdq`
        `Cdq(Quadword)`        → `cqo`
    - `StaticVariable(name, global, alignment, init)`:
        `IntInit(n != 0)`  → `.data / .align 4 / name: / .long n`
        `IntInit(0)`       → `.bss  / .align 4 / name: / .zero 4`
        `LongInit(n != 0)` → `.data / .align 8 / name: / .quad n`
        `LongInit(0)`      → `.bss  / .align 8 / name: / .zero 8`
    - `Push` still emits `pushq` (64-bit stack push; unchanged from Ch10).
    - `Ret` still emits the full epilogue.
    - The `subq $n, %rsp` for stack-frame allocation is now a regular
      `Binary(Quadword, Sub, Imm(n), Reg(SP))` instruction and is emitted
      by the general Binary case.
-/

namespace Emission

open AssemblyAST

-- ---------------------------------------------------------------------------
-- Register name emission
-- ---------------------------------------------------------------------------

/-- 32-bit (4-byte) register names.  XMM registers must not appear here. -/
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
  | .SP  => "%esp"   -- 32-bit stack pointer (not typically used)
  | .BP  => "%ebp"   -- 32-bit base pointer (Chapter 14)
  | r    => panic! s!"emitReg4: XMM register {repr r} has no 32-bit name"

/-- 64-bit (8-byte) register names.  XMM registers must not appear here. -/
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
  | .SP  => "%rsp"   -- 64-bit stack pointer
  | .BP  => "%rbp"   -- 64-bit base pointer (Chapter 14)
  | r    => panic! s!"emitReg8: XMM register {repr r} has no 64-bit integer name"

/-- 8-bit (1-byte) register names.  Used by `set<cc>` and shift `%cl`. -/
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
  | .SP  => "%spl"
  | .BP  => "%bpl"   -- 8-bit base pointer (Chapter 14)
  | r    => panic! s!"emitReg1: XMM register {repr r} has no 8-bit name"

/-- Chapter 13: XMM register names for SSE/AVX scalar-double instructions. -/
private def emitRegXmm : Reg → String
  | .XMM0  => "%xmm0"
  | .XMM1  => "%xmm1"
  | .XMM2  => "%xmm2"
  | .XMM3  => "%xmm3"
  | .XMM4  => "%xmm4"
  | .XMM5  => "%xmm5"
  | .XMM6  => "%xmm6"
  | .XMM7  => "%xmm7"
  | .XMM14 => "%xmm14"
  | .XMM15 => "%xmm15"
  | r      => panic! s!"emitRegXmm: {repr r} is not an XMM register"

/-- Emit a register name in either 32-bit or 64-bit form based on `AsmType`.
    For `Double`, use XMM names (should only reach this via emitRegForType). -/
private def emitRegForType (t : AsmType) (r : Reg) : String :=
  match t with
  | .Longword => emitReg4 r
  | .Quadword => emitReg8 r
  | .Double   => emitRegXmm r

-- ---------------------------------------------------------------------------
-- Operand emission
-- ---------------------------------------------------------------------------

/-- Emit an operand using 32-bit register names (for Longword instructions).
    Chapter 14: `Memory(r, offset)` emits `offset(%r64)` — the address register
    is always 64-bit even for 32-bit data operations. -/
private def emitOperand : Operand → String
  | .Imm n       => s!"${n}"
  | .Reg r       => emitReg4 r
  | .Memory r n  => s!"{n}({emitReg8 r})"   -- Chapter 14: offset(reg64)
  | .Data nm     => s!"{nm}(%rip)"
  | .Pseudo _    => panic! "Pseudo operand reached emission stage"

/-- Emit an operand using 64-bit register names (for Quadword instructions and pushq). -/
private def emitOperand8 : Operand → String
  | .Imm n       => s!"${n}"
  | .Reg r       => emitReg8 r
  | .Memory r n  => s!"{n}({emitReg8 r})"   -- Chapter 14: offset(reg64)
  | .Data nm     => s!"{nm}(%rip)"
  | .Pseudo _    => panic! "Pseudo operand reached emission stage"

/-- Chapter 13: emit an operand for SSE instructions.
    XMM registers use `%xmmN`; memory uses the standard form.
    Chapter 14: `Memory(r, offset)` emits `offset(%r64)`. -/
private def emitXmmOperand : Operand → String
  | .Reg r       => emitRegXmm r
  | .Memory r n  => s!"{n}({emitReg8 r})"   -- Chapter 14: offset(reg64)
  | .Data nm     => s!"{nm}(%rip)"
  | .Imm _       => panic! "Immediate cannot appear in XMM operand position"
  | .Pseudo _    => panic! "Pseudo operand reached emission stage"

/-- Emit an operand using the register size appropriate for the given `AsmType`.
    Chapter 13: `.Double` maps to `emitXmmOperand` (XMM registers / memory). -/
private def emitOperandForType (t : AsmType) : Operand → String :=
  match t with
  | .Longword => emitOperand
  | .Quadword => emitOperand8
  | .Double   => emitXmmOperand

/-- Emit a shift count: `Reg(CX)` → `%cl`, others use the 32-bit form. -/
private def emitShiftCount : Operand → String
  | .Reg .CX => "%cl"
  | other    => emitOperand other

/-- Emit a byte-sized operand for `set<cc>` instructions. -/
private def emitByteOperand : Operand → String
  | .Reg r       => emitReg1 r
  | .Memory r n  => s!"{n}({emitReg8 r})"   -- Chapter 14
  | .Data nm     => s!"{nm}(%rip)"
  | .Imm n       => s!"${n}"
  | .Pseudo _    => panic! "Pseudo operand reached emission stage"

/-- Emit a condition code suffix for `j<cc>` and `set<cc>`. -/
private def emitCondCode : CondCode → String
  | .E  => "e"
  | .NE => "ne"
  | .G  => "g"
  | .GE => "ge"
  | .L  => "l"
  | .LE => "le"
  -- Chapter 12: unsigned comparison condition codes
  | .A  => "a"
  | .AE => "ae"
  | .B  => "b"
  | .BE => "be"
  -- Chapter 13: parity flag (NaN detection after comisd)
  | .P  => "p"

-- ---------------------------------------------------------------------------
-- Instruction emission
-- ---------------------------------------------------------------------------

/-- Emit a single assembly instruction as an indented string.
    `localDefs` is the list of locally-defined function names, used to decide
    whether to append `@PLT` to external `call` instructions. -/
private def emitInstruction (localDefs : List String) : Instruction → String
  -- Chapter 13: Movsd (scalar double move)
  | .Movsd src dst =>
      s!"    movsd {emitXmmOperand src}, {emitXmmOperand dst}"
  -- Typed Mov: movl / movq (Double uses Movsd, not Mov)
  | .Mov .Longword src dst =>
      s!"    movl {emitOperand src}, {emitOperand dst}"
  | .Mov .Quadword src dst =>
      s!"    movq {emitOperand8 src}, {emitOperand8 dst}"
  | .Mov .Double _ _ =>
      panic! "Mov with Double asm type is invalid; use Movsd instead"
  -- Movsx: sign-extend 32-bit int to 64-bit long (movslq)
  | .Movsx src dst =>
      s!"    movslq {emitOperand src}, {emitOperand8 dst}"
  -- MovZeroExtend: zero-extend 32-bit uint to 64-bit (Chapter 12)
  -- On x86-64, writing to a 32-bit register name zeros the upper 32 bits.
  -- FixUp ensures dst is always a register here (memory dst was replaced in FixUp).
  | .MovZeroExtend src dst =>
      s!"    movl {emitOperand src}, {emitOperand dst}"
  -- Typed Unary (Double negation uses Xorpd, not Unary)
  | .Unary .Longword .Neg dst => s!"    negl {emitOperand dst}"
  | .Unary .Quadword .Neg dst => s!"    negq {emitOperand8 dst}"
  | .Unary .Longword .Not dst => s!"    notl {emitOperand dst}"
  | .Unary .Quadword .Not dst => s!"    notq {emitOperand8 dst}"
  | .Unary .Double _ _ => panic! "Unary with Double asm type is invalid; use Xorpd instead"
  -- Chapter 13: Double Binary operations (SSE2 scalar-double arithmetic)
  | .Binary .Double .Add       src dst => s!"    addsd {emitXmmOperand src}, {emitXmmOperand dst}"
  | .Binary .Double .Sub       src dst => s!"    subsd {emitXmmOperand src}, {emitXmmOperand dst}"
  | .Binary .Double .Mult      src dst => s!"    mulsd {emitXmmOperand src}, {emitXmmOperand dst}"
  | .Binary .Double .DivDouble src dst => s!"    divsd {emitXmmOperand src}, {emitXmmOperand dst}"
  | .Binary _ .DivDouble _ _  => panic! "DivDouble must be used with Double asm type"
  -- Chapter 13: Xorpd (double negation via -0.0 XOR)
  | .Xorpd src dst =>
      s!"    xorpd {emitXmmOperand src}, {emitXmmOperand dst}"
  -- Chapter 13: Comisd (double comparison; sets ZF/CF)
  | .Comisd src dst =>
      s!"    comisd {emitXmmOperand src}, {emitXmmOperand dst}"
  -- Chapter 13: integer ↔ double conversions
  -- cvtsi2sd[l/q]: integer (32/64-bit) → double; integer suffix specifies integer size
  | .Cvtsi2sd .Longword src dst =>
      s!"    cvtsi2sdl {emitOperand src}, {emitXmmOperand dst}"
  | .Cvtsi2sd .Quadword src dst =>
      s!"    cvtsi2sdq {emitOperand8 src}, {emitXmmOperand dst}"
  | .Cvtsi2sd .Double _ _ =>
      panic! "Cvtsi2sd with Double asm type is invalid"
  -- cvttsd2si[l/q]: double → integer (32/64-bit), truncated toward zero
  | .Cvttsd2si .Longword src dst =>
      s!"    cvttsd2sil {emitXmmOperand src}, {emitOperand dst}"
  | .Cvttsd2si .Quadword src dst =>
      s!"    cvttsd2siq {emitXmmOperand src}, {emitOperand8 dst}"
  | .Cvttsd2si .Double _ _ =>
      panic! "Cvttsd2si with Double asm type is invalid"
  -- Typed Binary (integer)
  | .Binary t .Add  src dst =>
      s!"    add{if t == .Longword then "l" else "q"} {emitOperandForType t src}, {emitOperandForType t dst}"
  | .Binary t .Sub  src dst =>
      s!"    sub{if t == .Longword then "l" else "q"} {emitOperandForType t src}, {emitOperandForType t dst}"
  | .Binary t .Mult src dst =>
      s!"    imul{if t == .Longword then "l" else "q"} {emitOperandForType t src}, {emitOperandForType t dst}"
  | .Binary t .And  src dst =>
      s!"    and{if t == .Longword then "l" else "q"} {emitOperandForType t src}, {emitOperandForType t dst}"
  | .Binary t .Or   src dst =>
      s!"    or{if t == .Longword then "l" else "q"} {emitOperandForType t src}, {emitOperandForType t dst}"
  | .Binary t .Xor  src dst =>
      s!"    xor{if t == .Longword then "l" else "q"} {emitOperandForType t src}, {emitOperandForType t dst}"
  | .Binary t .Sal  cnt dst =>
      s!"    sal{if t == .Longword then "l" else "q"} {emitShiftCount cnt}, {emitOperandForType t dst}"
  | .Binary t .Sar  cnt dst =>
      s!"    sar{if t == .Longword then "l" else "q"} {emitShiftCount cnt}, {emitOperandForType t dst}"
  -- Chapter 12: logical shift right (unsigned)
  | .Binary t .Shr  cnt dst =>
      s!"    shr{if t == .Longword then "l" else "q"} {emitShiftCount cnt}, {emitOperandForType t dst}"
  -- Typed Cmp (Double uses Comisd, not Cmp)
  | .Cmp .Longword src dst => s!"    cmpl {emitOperand src}, {emitOperand dst}"
  | .Cmp .Quadword src dst => s!"    cmpq {emitOperand8 src}, {emitOperand8 dst}"
  | .Cmp .Double _ _       => panic! "Cmp with Double asm type is invalid; use Comisd instead"
  -- Typed Idiv (signed division; Double uses divsd via Binary)
  | .Idiv .Longword op => s!"    idivl {emitOperand op}"
  | .Idiv .Quadword op => s!"    idivq {emitOperand8 op}"
  | .Idiv .Double _   => panic! "Idiv with Double asm type is invalid"
  -- Typed Div (unsigned division, Chapter 12)
  | .Div .Longword op => s!"    divl {emitOperand op}"
  | .Div .Quadword op => s!"    divq {emitOperand8 op}"
  | .Div .Double _    => panic! "Div with Double asm type is invalid"
  -- Cdq / Cqo (Double has no cdq equivalent)
  | .Cdq .Longword => "    cdq"
  | .Cdq .Quadword => "    cqo"
  | .Cdq .Double   => panic! "Cdq with Double asm type is invalid"
  -- Control flow (no size)
  | .Jmp name      => s!"    jmp .L{name}"
  | .JmpCC cc name => s!"    j{emitCondCode cc} .L{name}"
  | .SetCC cc op   => s!"    set{emitCondCode cc} {emitByteOperand op}"
  | .Label name    => s!".L{name}:"
  -- Push: always 64-bit
  | .Push operand  => s!"    pushq {emitOperand8 operand}"
  -- Call: @PLT for external functions on Linux
  | .Call name =>
      if localDefs.contains name then
        s!"    call {name}"
      else
        s!"    call {name}@PLT"
  -- Ret: full epilogue
  | .Ret => "    movq %rbp, %rsp\n    popq %rbp\n    ret"
  -- Chapter 14: leaq — compute address of memory operand into register
  | .Lea src dst =>
      s!"    leaq {emitOperand8 src}, {emitOperand8 dst}"

-- ---------------------------------------------------------------------------
-- Top-level emission
-- ---------------------------------------------------------------------------

/-- Emit a complete function definition. -/
private def emitFunctionDef (localDefs : List String) (f : FunctionDef) : String :=
  let globalDirective := if f.global then s!"    .globl {f.name}\n" else ""
  let prologue := "    pushq %rbp\n    movq %rsp, %rbp"
  let instrs   := String.intercalate "\n"
                    (f.instructions.map (emitInstruction localDefs))
  s!"{globalDirective}    .text\n{f.name}:\n{prologue}\n{instrs}"

/-- Emit a static variable definition as assembly directives.
    Chapter 11: emits `.long`/`.quad` or `.zero 4`/`.zero 8` based on `StaticInit`.
    Chapter 13: `DoubleInit(f)` emits `.double f` (or `.zero 8` for zero) in `.data`. -/
private def emitStaticVariable (name : String) (global : Bool) (alignment : Nat)
    (init : StaticInit) : String :=
  let globalDirective := if global then s!"    .globl {name}\n" else ""
  match init with
  | .IntInit n | .UIntInit n =>
      if n != 0 then
        s!"{globalDirective}    .data\n    .align {alignment}\n{name}:\n    .long {n}"
      else
        s!"{globalDirective}    .bss\n    .align {alignment}\n{name}:\n    .zero 4"
  | .LongInit n | .ULongInit n =>
      if n != 0 then
        s!"{globalDirective}    .data\n    .align {alignment}\n{name}:\n    .quad {n}"
      else
        s!"{globalDirective}    .bss\n    .align {alignment}\n{name}:\n    .zero 8"
  | .DoubleInit f =>
      -- Chapter 13: emit the raw 64-bit IEEE 754 bit pattern using .quad for exact fidelity.
      -- Float.toBits gives the UInt64 bit representation.
      if f == 0.0 || f == -0.0 then
        -- Distinguish +0.0 (bits = 0) from -0.0 (sign bit = 1)
        let bits : UInt64 := f.toBits
        if bits == 0 then
          s!"{globalDirective}    .bss\n    .align {alignment}\n{name}:\n    .zero 8"
        else
          -- -0.0: must store the bit pattern explicitly
          s!"{globalDirective}    .data\n    .align {alignment}\n{name}:\n    .quad {bits}"
      else
        let bits : UInt64 := f.toBits
        s!"{globalDirective}    .data\n    .align {alignment}\n{name}:\n    .quad {bits}"

/-- Chapter 13: emit a read-only constant (float literal or neg-zero mask) in `.rodata`.
    Never exported with `.globl` (constants are translation-unit-local labels).
    Uses `.quad` with the raw IEEE 754 bit pattern for exact round-trip fidelity. -/
private def emitStaticConstant (name : String) (alignment : Nat) (init : StaticInit) : String :=
  match init with
  | .DoubleInit f =>
      let bits : UInt64 := f.toBits
      s!"    .section .rodata\n    .align {alignment}\n{name}:\n    .quad {bits}"
  | .LongInit n | .ULongInit n =>
      -- Used for threshold constants (e.g. 2^63 for ULong↔Double conversion)
      s!"    .section .rodata\n    .align {alignment}\n{name}:\n    .quad {n}"
  | .IntInit n | .UIntInit n =>
      s!"    .section .rodata\n    .align {alignment}\n{name}:\n    .long {n}"

/-- Entry point for the emission pass. -/
def emitProgram (p : Program) : String :=
  -- Collect locally-defined function names (for @PLT decision)
  let localDefs := p.topLevels.filterMap fun tl =>
    match tl with
    | .Function f         => some f.name
    | .StaticVariable ..  => none
    | .StaticConstant ..  => none  -- Chapter 13: constants are not function defs
  let topLevelStrings := p.topLevels.map fun tl =>
    match tl with
    | .Function f                              => emitFunctionDef localDefs f
    | .StaticVariable name glob align init     => emitStaticVariable name glob align init
    | .StaticConstant name align init          => emitStaticConstant name align init
  let body := String.intercalate "\n" topLevelStrings
  s!"{body}\n    .section .note.GNU-stack,\"\",@progbits\n"

end Emission
