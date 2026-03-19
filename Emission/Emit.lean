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

/-- Emit a register name in the size appropriate for `AsmType`.
    Chapter 16: `.Byte` maps to 8-bit register names via `emitReg1`. -/
private def emitRegForType (t : AsmType) (r : Reg) : String :=
  match t with
  | .Byte          => emitReg1 r
  | .Longword      => emitReg4 r
  | .Quadword      => emitReg8 r
  | .Double        => emitRegXmm r
  | .ByteArray _ _ => panic! "ByteArray AsmType cannot appear in register emission"

-- ---------------------------------------------------------------------------
-- Operand emission
-- ---------------------------------------------------------------------------

/-- Emit an operand using 32-bit register names (for Longword instructions).
    Chapter 14: `Memory(r, offset)` emits `offset(%r64)` — the address register
    is always 64-bit even for 32-bit data operations.
    Chapter 15: `Indexed(base, idx, scale)` emits `(%base64, %idx64, scale)`. -/
private def emitOperand : Operand → String
  | .Imm n              => s!"${n}"
  | .Reg r              => emitReg4 r
  | .Memory r n         => s!"{n}({emitReg8 r})"
  | .Data nm            => s!"{nm}(%rip)"
  | .Indexed b i s      => s!"({emitReg8 b}, {emitReg8 i}, {s})"  -- Chapter 15
  | .Pseudo _           => panic! "Pseudo operand reached emission stage"
  | .PseudoMem _ _      => panic! "PseudoMem operand reached emission stage"

/-- Emit an operand using 64-bit register names (for Quadword instructions and pushq).
    Chapter 15: `Indexed` emits the same `(base, idx, scale)` form. -/
private def emitOperand8 : Operand → String
  | .Imm n              => s!"${n}"
  | .Reg r              => emitReg8 r
  | .Memory r n         => s!"{n}({emitReg8 r})"
  | .Data nm            => s!"{nm}(%rip)"
  | .Indexed b i s      => s!"({emitReg8 b}, {emitReg8 i}, {s})"  -- Chapter 15
  | .Pseudo _           => panic! "Pseudo operand reached emission stage"
  | .PseudoMem _ _      => panic! "PseudoMem operand reached emission stage"

/-- Chapter 13: emit an operand for SSE instructions.
    XMM registers use `%xmmN`; memory uses the standard form.
    Chapter 14: `Memory(r, offset)` emits `offset(%r64)`.
    Chapter 15: `Indexed` emits `(base, idx, scale)` (same as integer form). -/
private def emitXmmOperand : Operand → String
  | .Reg r              => emitRegXmm r
  | .Memory r n         => s!"{n}({emitReg8 r})"
  | .Data nm            => s!"{nm}(%rip)"
  | .Indexed b i s      => s!"({emitReg8 b}, {emitReg8 i}, {s})"  -- Chapter 15
  | .Imm _              => panic! "Immediate cannot appear in XMM operand position"
  | .Pseudo _           => panic! "Pseudo operand reached emission stage"
  | .PseudoMem _ _      => panic! "PseudoMem operand reached emission stage"

/-- Emit a byte-sized operand for `set<cc>` and `movb` instructions.
    Chapter 16: used for Byte (char) operands. -/
private def emitByteOperand : Operand → String
  | .Reg r          => emitReg1 r
  | .Memory r n     => s!"{n}({emitReg8 r})"            -- Chapter 14
  | .Data nm        => s!"{nm}(%rip)"
  | .Imm n          => s!"${n}"
  | .Indexed b i s  => s!"({emitReg8 b}, {emitReg8 i}, {s})"  -- Chapter 15
  | .Pseudo _       => panic! "Pseudo operand reached emission stage"
  | .PseudoMem _ _  => panic! "PseudoMem operand reached emission stage"

/-- Emit an operand using the register size appropriate for the given `AsmType`.
    Chapter 13: `.Double` maps to `emitXmmOperand` (XMM registers / memory).
    Chapter 16: `.Byte` maps to `emitByteOperand` (8-bit register names). -/
private def emitOperandForType (t : AsmType) : Operand → String :=
  match t with
  | .Byte          => emitByteOperand
  | .Longword      => emitOperand
  | .Quadword      => emitOperand8
  | .Double        => emitXmmOperand
  | .ByteArray _ _ => panic! "ByteArray AsmType cannot appear as instruction operand type"

/-- Emit a shift count: `Reg(CX)` → `%cl`, others use the 32-bit form. -/
private def emitShiftCount : Operand → String
  | .Reg .CX => "%cl"
  | other    => emitOperand other

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

-- ---------------------------------------------------------------------------
-- Instruction emission helpers
-- Breaking the large match into smaller helpers avoids Lean elaboration timeouts
-- caused by exhaustiveness checking across too many (Instruction × AsmType) combos.
-- ---------------------------------------------------------------------------

/-- Emit a type suffix letter: `b` for Byte, `l` for Longword, `q` for Quadword/Double/other. -/
private def typeSuffix (t : AsmType) : String :=
  match t with
  | .Byte     => "b"
  | .Longword => "l"
  | _         => "q"

/-- Emit Mov-family instructions.
    Chapter 16: Mov .Byte emits `movb`; typed Movsx and MovZeroExtend select the
    correct mnemonic based on (srcType, dstType). -/
private def emitMovInstr : Instruction → String
  | .Movsd src dst          => s!"    movsd {emitXmmOperand src}, {emitXmmOperand dst}"
  | .Mov .Byte s d          => s!"    movb {emitByteOperand s}, {emitByteOperand d}"
  | .Mov .Longword s d      => s!"    movl {emitOperand s}, {emitOperand d}"
  | .Mov .Quadword s d      => s!"    movq {emitOperand8 s}, {emitOperand8 d}"
  | .Mov _ _ _              => panic! "Mov with non-integer AsmType"
  -- Movsx: sign-extension mnemonics
  --   Byte→Longword  : movsbl (sign-extend byte to 32-bit)
  --   Byte→Quadword  : movsbq (sign-extend byte to 64-bit)
  --   Longword→Quadword : movslq (sign-extend 32-bit to 64-bit)
  | .Movsx .Byte .Longword s d    => s!"    movsbl {emitByteOperand s}, {emitOperand d}"
  | .Movsx .Byte .Quadword s d    => s!"    movsbq {emitByteOperand s}, {emitOperand8 d}"
  | .Movsx .Longword .Quadword s d => s!"    movslq {emitOperand s}, {emitOperand8 d}"
  | .Movsx _ _ _ _          => panic! "Movsx with unsupported srcType/dstType combination"
  -- MovZeroExtend: zero-extension mnemonics
  --   Byte→Longword  : movzbl (zero-extend byte to 32-bit; auto-zeros upper 32 bits)
  --   Byte→Quadword  : movzbl (same instruction; 32-bit write zeros upper 32 bits of 64-bit reg)
  --   Longword→Quadword : movl (32-bit write to register; auto-zeros upper 32 bits on x86-64)
  --   For Byte dst, use 32-bit (emitOperand) since movzbl always targets a 32-bit register.
  | .MovZeroExtend .Byte .Longword s d  => s!"    movzbl {emitByteOperand s}, {emitOperand d}"
  | .MovZeroExtend .Byte .Quadword s d  => s!"    movzbl {emitByteOperand s}, {emitOperand d}"
  | .MovZeroExtend .Longword .Quadword s d => s!"    movl {emitOperand s}, {emitOperand d}"
  | .MovZeroExtend _ _ _ _  => panic! "MovZeroExtend with unsupported srcType/dstType combination"
  | _                       => panic! "emitMovInstr: not a Mov instruction"

/-- Emit Unary instructions.
    Chapter 16: `.Byte` case added for `negb`/`notb` (unlikely in practice due to
    integer promotion, but needed for completeness). -/
private def emitUnaryInstr : Instruction → String
  | .Unary .Byte    .Neg d => s!"    negb {emitByteOperand d}"
  | .Unary .Longword .Neg d => s!"    negl {emitOperand d}"
  | .Unary .Quadword .Neg d => s!"    negq {emitOperand8 d}"
  | .Unary .Byte    .Not d => s!"    notb {emitByteOperand d}"
  | .Unary .Longword .Not d => s!"    notl {emitOperand d}"
  | .Unary .Quadword .Not d => s!"    notq {emitOperand8 d}"
  | .Unary _ _ _            => panic! "Unary with invalid AsmType"
  | _                       => panic! "emitUnaryInstr: not a Unary instruction"

/-- Emit Binary instructions (integer and double). -/
private def emitBinaryInstr : Instruction → String
  | .Binary .Double .Add       s d => s!"    addsd {emitXmmOperand s}, {emitXmmOperand d}"
  | .Binary .Double .Sub       s d => s!"    subsd {emitXmmOperand s}, {emitXmmOperand d}"
  | .Binary .Double .Mult      s d => s!"    mulsd {emitXmmOperand s}, {emitXmmOperand d}"
  | .Binary .Double .DivDouble s d => s!"    divsd {emitXmmOperand s}, {emitXmmOperand d}"
  | .Binary _ .DivDouble _ _       => panic! "DivDouble must use Double AsmType"
  | .Binary t .Add  s d => s!"    add{typeSuffix t} {emitOperandForType t s}, {emitOperandForType t d}"
  | .Binary t .Sub  s d => s!"    sub{typeSuffix t} {emitOperandForType t s}, {emitOperandForType t d}"
  | .Binary t .Mult s d => s!"    imul{typeSuffix t} {emitOperandForType t s}, {emitOperandForType t d}"
  | .Binary t .And  s d => s!"    and{typeSuffix t} {emitOperandForType t s}, {emitOperandForType t d}"
  | .Binary t .Or   s d => s!"    or{typeSuffix t} {emitOperandForType t s}, {emitOperandForType t d}"
  | .Binary t .Xor  s d => s!"    xor{typeSuffix t} {emitOperandForType t s}, {emitOperandForType t d}"
  | .Binary t .Sal  c d => s!"    sal{typeSuffix t} {emitShiftCount c}, {emitOperandForType t d}"
  | .Binary t .Sar  c d => s!"    sar{typeSuffix t} {emitShiftCount c}, {emitOperandForType t d}"
  | .Binary t .Shr  c d => s!"    shr{typeSuffix t} {emitShiftCount c}, {emitOperandForType t d}"
  | _ => panic! "emitBinaryInstr: not a Binary instruction"

/-- Emit double-specific SSE instructions. -/
private def emitDoubleInstr : Instruction → String
  | .Xorpd   s d => s!"    xorpd {emitXmmOperand s}, {emitXmmOperand d}"
  | .Comisd  s d => s!"    comisd {emitXmmOperand s}, {emitXmmOperand d}"
  | .Cvtsi2sd .Longword s d => s!"    cvtsi2sdl {emitOperand s}, {emitXmmOperand d}"
  | .Cvtsi2sd .Quadword s d => s!"    cvtsi2sdq {emitOperand8 s}, {emitXmmOperand d}"
  | .Cvtsi2sd _ _ _         => panic! "Cvtsi2sd with invalid AsmType"
  | .Cvttsd2si .Longword s d => s!"    cvttsd2sil {emitXmmOperand s}, {emitOperand d}"
  | .Cvttsd2si .Quadword s d => s!"    cvttsd2siq {emitXmmOperand s}, {emitOperand8 d}"
  | .Cvttsd2si _ _ _         => panic! "Cvttsd2si with invalid AsmType"
  | _ => panic! "emitDoubleInstr: not a double-specific instruction"

/-- Emit comparison and division instructions.
    Chapter 16: `Cmp .Byte` emits `cmpb` for byte comparisons. -/
private def emitCmpDivInstr : Instruction → String
  | .Cmp .Byte     s d => s!"    cmpb {emitByteOperand s}, {emitByteOperand d}"
  | .Cmp .Longword s d => s!"    cmpl {emitOperand s}, {emitOperand d}"
  | .Cmp .Quadword s d => s!"    cmpq {emitOperand8 s}, {emitOperand8 d}"
  | .Cmp _ _ _         => panic! "Cmp with invalid AsmType"
  | .Idiv .Longword op => s!"    idivl {emitOperand op}"
  | .Idiv .Quadword op => s!"    idivq {emitOperand8 op}"
  | .Idiv _ _          => panic! "Idiv with invalid AsmType"
  | .Div .Longword op  => s!"    divl {emitOperand op}"
  | .Div .Quadword op  => s!"    divq {emitOperand8 op}"
  | .Div _ _           => panic! "Div with invalid AsmType"
  | .Cdq .Longword     => "    cdq"
  | .Cdq .Quadword     => "    cqo"
  | .Cdq _             => panic! "Cdq with invalid AsmType"
  | _ => panic! "emitCmpDivInstr: not a cmp/div instruction"

/-- Emit a single assembly instruction as an indented string.
    `localDefs` is the list of locally-defined function names, used to decide
    whether to append `@PLT` to external `call` instructions.
    The large match is split into helper functions (above) to avoid Lean elaboration
    timeouts from exhaustiveness checking across many (Instruction × AsmType) combos. -/
private def emitInstruction (localDefs : List String) (instr : Instruction) : String :=
  match instr with
  -- Mov-family
  | .Movsd .. | .Mov .. | .Movsx .. | .MovZeroExtend .. => emitMovInstr instr
  -- Unary
  | .Unary .. => emitUnaryInstr instr
  -- Binary (integer and double)
  | .Binary .. => emitBinaryInstr instr
  -- Double-specific SSE
  | .Xorpd .. | .Comisd .. | .Cvtsi2sd .. | .Cvttsd2si .. => emitDoubleInstr instr
  -- Comparison and division
  | .Cmp .. | .Idiv .. | .Div .. | .Cdq .. => emitCmpDivInstr instr
  -- Control flow (no size)
  | .Jmp name      => s!"    jmp .L{name}"
  | .JmpCC cc name => s!"    j{emitCondCode cc} .L{name}"
  | .SetCC cc op   => s!"    set{emitCondCode cc} {emitByteOperand op}"
  | .Label name    => s!".L{name}:"
  -- Push: always 64-bit
  | .Push operand  => s!"    pushq {emitOperand8 operand}"
  -- Call: @PLT for external functions on Linux
  | .Call name =>
      if localDefs.contains name then s!"    call {name}"
      else s!"    call {name}@PLT"
  -- Ret: full epilogue
  | .Ret => "    movq %rbp, %rsp\n    popq %rbp\n    ret"
  -- Chapter 14: leaq — compute address of memory operand into register
  | .Lea src dst => s!"    leaq {emitOperand8 src}, {emitOperand8 dst}"

-- ---------------------------------------------------------------------------
-- String escaping helper (Chapter 16)
-- ---------------------------------------------------------------------------

/-- Escape a single character for use in an assembly string literal (GAS syntax).
    Non-printable characters (outside ASCII 32–126) are emitted as octal escapes `\ooo`.
    `"` and `\` are escaped as `\"` and `\\`. Common C escape sequences are used for
    `\n`, `\t`, `\r`. -/
private def escapeChar (c : Char) : String :=
  if c == '"'  then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\t' then "\\t"
  else if c == '\r' then "\\r"
  else if c.toNat >= 32 && c.toNat <= 126 then c.toString
  else
    -- Octal escape: backslash + three octal digits
    let n := c.toNat
    s!"\\{n / 64}{(n / 8) % 8}{n % 8}"

/-- Escape all characters in a string for assembly `.asciz`/`.ascii` directives. -/
private def escapeForAsm (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeChar c) ""

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

/-- Chapter 15+16: emit a single `StaticInit` element as an assembly directive string.
    Returns `(directive, isZero)` where `isZero` is true iff the element is all zeros
    (so the caller can decide whether to put it in `.data` or `.bss`). -/
private def emitOneStaticInit : StaticInit → String × Bool
  | .IntInit n | .UIntInit n =>
      if n != 0 then (s!"    .long {n}", false) else ("    .zero 4", true)
  | .LongInit n | .ULongInit n =>
      if n != 0 then (s!"    .quad {n}", false) else ("    .zero 8", true)
  | .DoubleInit f =>
      let bits : UInt64 := f.toBits
      if bits == 0 then ("    .zero 8", true)
      else (s!"    .quad {bits}", false)
  | .ZeroInit n =>
      -- Chapter 15: .zero n for a block of n zero bytes
      (s!"    .zero {n}", true)
  | .CharInit n | .UCharInit n =>
      -- Chapter 16: 1-byte signed/unsigned char (.byte n; .zero 1 if zero)
      if n != 0 then (s!"    .byte {n}", false) else ("    .zero 1", true)
  | .StringInit s true =>
      -- Chapter 16: null-terminated string (.asciz appends implicit '\0')
      (s!"    .asciz \"{escapeForAsm s}\"", false)
  | .StringInit s false =>
      -- Chapter 16: string bytes without null terminator (.ascii)
      (s!"    .ascii \"{escapeForAsm s}\"", false)
  | .PointerInit lbl =>
      -- Chapter 16: 8-byte pointer to a label (e.g. for `char *p = "hello";` in static storage)
      (s!"    .quad {lbl}", false)

/-- Emit a static variable definition as assembly directives.
    Chapter 15: `inits` is now `List StaticInit` (one entry per array element or one
    for a scalar).  If all entries are zero, uses `.bss`; otherwise uses `.data`. -/
private def emitStaticVariable (name : String) (global : Bool) (alignment : Nat)
    (inits : List StaticInit) : String :=
  let globalDirective := if global then s!"    .globl {name}\n" else ""
  let emitted    := inits.map emitOneStaticInit
  let allZero    := emitted.all (·.2)
  -- `section` is a Lean keyword; use `sectionDir` as the variable name
  let sectionDir := if allZero then "    .bss" else "    .data"
  let directives := String.intercalate "\n" (emitted.map (·.1))
  s!"{globalDirective}{sectionDir}\n    .align {alignment}\n{name}:\n{directives}"

/-- Chapter 13+16: emit a read-only constant in `.rodata`.
    Never exported with `.globl` (constants are translation-unit-local labels).
    Chapter 16: changed to accept `List StaticInit` to support string constants
    that may have a `StringInit` followed by a `ZeroInit` for padding. -/
private def emitStaticConstant (name : String) (alignment : Nat) (inits : List StaticInit) : String :=
  let emitted   := inits.map emitOneStaticInit
  let directives := String.intercalate "\n" (emitted.map (·.1))
  s!"    .section .rodata\n    .align {alignment}\n{name}:\n{directives}"

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
    | .StaticConstant name align inits         => emitStaticConstant name align inits
  let body := String.intercalate "\n" topLevelStrings
  s!"{body}\n    .section .note.GNU-stack,\"\",@progbits\n"

end Emission
