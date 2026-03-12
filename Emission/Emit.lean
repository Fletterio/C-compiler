import AssemblyAST.AssemblyAST

/-
  Code emission pass: converts AssemblyAST.Program to x64 AT&T-syntax assembly.

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

/-- 32-bit (4-byte) register names. -/
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

/-- 64-bit (8-byte) register names. -/
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

/-- Emit a register name in either 32-bit or 64-bit form based on `AsmType`. -/
private def emitRegForType (t : AsmType) (r : Reg) : String :=
  match t with
  | .Longword => emitReg4 r
  | .Quadword => emitReg8 r

-- ---------------------------------------------------------------------------
-- Operand emission
-- ---------------------------------------------------------------------------

/-- Emit an operand using 32-bit register names (for Longword instructions). -/
private def emitOperand : Operand → String
  | .Imm n    => s!"${n}"
  | .Reg r    => emitReg4 r
  | .Stack n  => s!"{n}(%rbp)"
  | .Data nm  => s!"{nm}(%rip)"
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit an operand using 64-bit register names (for Quadword instructions and pushq). -/
private def emitOperand8 : Operand → String
  | .Imm n    => s!"${n}"
  | .Reg r    => emitReg8 r
  | .Stack n  => s!"{n}(%rbp)"
  | .Data nm  => s!"{nm}(%rip)"
  | .Pseudo _ => panic! "Pseudo operand reached emission stage"

/-- Emit an operand using the register size appropriate for the given `AsmType`. -/
private def emitOperandForType (t : AsmType) : Operand → String :=
  match t with
  | .Longword => emitOperand
  | .Quadword => emitOperand8

/-- Emit a shift count: `Reg(CX)` → `%cl`, others use the 32-bit form. -/
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

/-- Emit a condition code suffix for `j<cc>` and `set<cc>`. -/
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
    `localDefs` is the list of locally-defined function names, used to decide
    whether to append `@PLT` to external `call` instructions. -/
private def emitInstruction (localDefs : List String) : Instruction → String
  -- Typed Mov: movl / movq
  | .Mov .Longword src dst =>
      s!"    movl {emitOperand src}, {emitOperand dst}"
  | .Mov .Quadword src dst =>
      s!"    movq {emitOperand8 src}, {emitOperand8 dst}"
  -- Movsx: sign-extend 32-bit int to 64-bit long (movslq)
  | .Movsx src dst =>
      s!"    movslq {emitOperand src}, {emitOperand8 dst}"
  -- Typed Unary
  | .Unary .Longword .Neg dst => s!"    negl {emitOperand dst}"
  | .Unary .Quadword .Neg dst => s!"    negq {emitOperand8 dst}"
  | .Unary .Longword .Not dst => s!"    notl {emitOperand dst}"
  | .Unary .Quadword .Not dst => s!"    notq {emitOperand8 dst}"
  -- Typed Binary
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
  -- Typed Cmp
  | .Cmp .Longword src dst => s!"    cmpl {emitOperand src}, {emitOperand dst}"
  | .Cmp .Quadword src dst => s!"    cmpq {emitOperand8 src}, {emitOperand8 dst}"
  -- Typed Idiv
  | .Idiv .Longword op => s!"    idivl {emitOperand op}"
  | .Idiv .Quadword op => s!"    idivq {emitOperand8 op}"
  -- Cdq / Cqo
  | .Cdq .Longword => "    cdq"
  | .Cdq .Quadword => "    cqo"
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
    Chapter 11: emits `.long`/`.quad` or `.zero 4`/`.zero 8` based on `StaticInit`. -/
private def emitStaticVariable (name : String) (global : Bool) (alignment : Nat)
    (init : StaticInit) : String :=
  let globalDirective := if global then s!"    .globl {name}\n" else ""
  match init with
  | .IntInit n =>
      if n != 0 then
        s!"{globalDirective}    .data\n    .align {alignment}\n{name}:\n    .long {n}"
      else
        s!"{globalDirective}    .bss\n    .align {alignment}\n{name}:\n    .zero 4"
  | .LongInit n =>
      if n != 0 then
        s!"{globalDirective}    .data\n    .align {alignment}\n{name}:\n    .quad {n}"
      else
        s!"{globalDirective}    .bss\n    .align {alignment}\n{name}:\n    .zero 8"

/-- Entry point for the emission pass. -/
def emitProgram (p : Program) : String :=
  let localDefs := p.topLevels.filterMap fun tl =>
    match tl with
    | .Function f         => some f.name
    | .StaticVariable ..  => none
  let topLevelStrings := p.topLevels.map fun tl =>
    match tl with
    | .Function f                      => emitFunctionDef localDefs f
    | .StaticVariable name glob align init => emitStaticVariable name glob align init
  let body := String.intercalate "\n" topLevelStrings
  s!"{body}\n    .section .note.GNU-stack,\"\",@progbits\n"

end Emission
