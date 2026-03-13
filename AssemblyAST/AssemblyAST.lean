namespace AssemblyAST

/-
  Assembly AST for Chapter 14.

  Chapter 14 additions:
    - `Reg.BP`: base pointer `%rbp`, used as the base of `Memory(BP, offset)` slots.
    - `Operand.Memory(reg, offset)`: replaces the old `Stack(offset)`.
        `Memory(BP, n)`  = `n(%rbp)` — local variable / parameter stack slot.
        `Memory(R10, 0)` = `(%r10)` — pointer-dereference source.
        `Memory(R11, 0)` = `(%r11)` — pointer-dereference destination.
        `Memory(SP, 0)`  = `(%rsp)` — top of stack (for double push).
    - `Instruction.Lea(src, dst)`: `leaq src, dst` — computes the address of
        a stack slot (for `GetAddress` / `&e`).

  Chapter 13 additions:

  Chapter 13 additions:
    - `AsmType`: adds `Double` (8-byte, scalar IEEE 754 double).
    - XMM registers: `XMM0`..`XMM7` for argument/return, `XMM14`/`XMM15` for scratch.
    - New instructions:
        `Cvtsi2sd(AsmType, src, dst)` — convert integer to double (l or q suffix).
        `Cvttsd2si(AsmType, src, dst)` — truncate double to integer (l or q suffix).
        `Xorpd(src, dst)` — XOR packed doubles (used for negation via -0.0).
        `Comisd(src, dst)` — compare doubles (sets ZF/CF; no overflow flag).
        `Movsd(src, dst)` — move scalar double (movsd; distinct from Mov).
    - `BinaryOp.DivDouble` — `divsd` (double division; can't reuse `Idiv`/`Div`).
    - `StaticInit`: adds `DoubleInit(Float)` — `.double` directive.
    - `AsmTopLevel`: adds `StaticConstant(name, align, init)` for read-only data
      (float constants, neg-zero, ULong↔Double threshold).
    - `BackendSymEntry.ObjEntry`: `Double` AsmType marks XMM-resident temporaries.
    - `FunEntry.retAsmType`: can now be `Double` for double-returning functions.

  Chapter 12 additions:
    - `AsmType`: `Longword` (4-byte) vs `Quadword` (8-byte).
    - Unsigned condition codes: `A`, `AE`, `B`, `BE`.
    - `Div(AsmType, Operand)` — unsigned division (divl/divq).
    - `MovZeroExtend(src, dst)` — zero-extend movl.
    - `BinaryOp.Shr` — logical shift right for unsigned types.

  ASDL definition:
    program            = Program(top_level*)
    top_level          = Function(function_definition)
                       | StaticVariable(identifier name, bool global,
                                        int alignment, static_init init)
                       | ★ StaticConstant(identifier name, int alignment, static_init init)
    static_init        = IntInit(int) | LongInit(int) | UIntInit(int) | ULongInit(int)
                       | ★ DoubleInit(float)
    function_definition = Function(identifier name, bool global,
                                   identifier* params,
                                   instruction* instructions, int stackSize)
    instruction        = Mov(asm_type, operand src, operand dst)
                       | ★ Movsd(operand src, operand dst)
                       | Movsx(operand src, operand dst)
                       | MovZeroExtend(operand src, operand dst)
                       | Unary(asm_type, unary_operator, operand)
                       | Binary(asm_type, binary_operator, operand src, operand dst)
                       | Cmp(asm_type, operand, operand)
                       | Idiv(asm_type, operand)
                       | Div(asm_type, operand)
                       | Cdq(asm_type)
                       | Jmp(identifier)
                       | JmpCC(cond_code, identifier)
                       | SetCC(cond_code, operand)
                       | Label(identifier)
                       | Push(operand)
                       | Call(identifier)
                       | Ret
                       | ★ Cvtsi2sd(asm_type, operand src, operand dst)
                       | ★ Cvttsd2si(asm_type, operand src, operand dst)
                       | ★ Xorpd(operand src, operand dst)
                       | ★ Comisd(operand src, operand dst)
                       | ★★ Lea(operand src, operand dst)
    asm_type           = Longword | Quadword | ★ Double
    unary_operator     = Neg | Not
    binary_operator    = Add | Sub | Mult | And | Or | Xor | Sal | Sar | Shr
                       | ★ DivDouble
    cond_code          = E | NE | G | GE | L | LE | A | AE | B | BE
    operand            = Imm(int) | Reg(reg) | Pseudo(identifier)
                       | ★★ Memory(reg, int) | Data(identifier)
    reg                = AX | DX | CX | DI | SI | R8 | R9 | R10 | R11 | SP | ★★ BP
                       | ★ XMM0 | XMM1 | XMM2 | XMM3 | XMM4 | XMM5 | XMM6 | XMM7
                       | ★ XMM14 | XMM15
-/

/-- The three assembly sizes used through Chapter 13.
    `Longword` = 4 bytes (32-bit, suffix `l`).
    `Quadword` = 8 bytes (64-bit, suffix `q`).
    `Double`   = 8 bytes (64-bit IEEE 754; uses XMM registers and `sd` instructions). -/
inductive AsmType where
  | Longword : AsmType   -- 4-byte, C `int` / `unsigned int`
  | Quadword : AsmType   -- 8-byte, C `long` / `unsigned long`
  | Double   : AsmType   -- 8-byte, C `double` (Chapter 13)
  deriving Repr, BEq

inductive Reg where
  | AX  : Reg   -- EAX / RAX  (integer return value)
  | DX  : Reg   -- EDX / RDX
  | CX  : Reg   -- ECX / RCX
  | DI  : Reg   -- EDI / RDI  (1st int arg)
  | SI  : Reg   -- ESI / RSI  (2nd int arg)
  | R8  : Reg   -- R8D / R8   (5th int arg)
  | R9  : Reg   -- R9D / R9   (6th int arg)
  | R10 : Reg   -- scratch for source fix-ups
  | R11 : Reg   -- scratch for destination fix-ups
  /-- Stack pointer `%rsp` — used in prologue/epilogue Binary instructions. -/
  | SP  : Reg
  /-- Base pointer `%rbp` — base of the stack frame; used in `Memory(BP, offset)`. -/
  | BP  : Reg   -- Chapter 14
  -- Chapter 13: XMM registers for floating-point and double arguments
  | XMM0  : Reg   -- 1st float arg / float return value
  | XMM1  : Reg   -- 2nd float arg
  | XMM2  : Reg   -- 3rd float arg
  | XMM3  : Reg   -- 4th float arg
  | XMM4  : Reg   -- 5th float arg
  | XMM5  : Reg   -- 6th float arg
  | XMM6  : Reg   -- 7th float arg
  | XMM7  : Reg   -- 8th float arg
  | XMM14 : Reg   -- scratch for double source fix-ups (analogous to R10)
  | XMM15 : Reg   -- scratch for double destination fix-ups (analogous to R11)
  deriving Repr, BEq

inductive Operand where
  | Imm    : Int → Operand
  | Reg    : Reg → Operand
  | Pseudo : String → Operand
  /-- `Memory(r, offset)` = `offset(%r)` in AT&T syntax.
      Replaces the old `Stack(offset)` (which was always `Memory(BP, offset)`).
      Also used for pointer dereferences: `Memory(R10, 0)` = `(%r10)`. -/
  | Memory : Reg → Int → Operand   -- Chapter 14 (replaces Stack)
  | Data   : String → Operand
  deriving Repr, BEq

inductive UnaryOp where
  | Neg : UnaryOp   -- negl / negq
  | Not : UnaryOp   -- notl / notq
  deriving Repr, BEq

/-- Binary operators that share the `op src, dst` encoding. -/
inductive BinaryOp where
  | Add      : BinaryOp   -- addl / addq / addsd
  | Sub      : BinaryOp   -- subl / subq / subsd
  | Mult     : BinaryOp   -- imull / imulq / mulsd
  | And      : BinaryOp   -- andl / andq
  | Or       : BinaryOp   -- orl  / orq
  | Xor      : BinaryOp   -- xorl / xorq
  | Sal      : BinaryOp   -- sall / salq  (arithmetic/logical shift left)
  | Sar      : BinaryOp   -- sarl / sarq  (arithmetic shift right — for signed)
  | Shr      : BinaryOp   -- shrl / shrq  (logical shift right — for unsigned)
  | DivDouble : BinaryOp  -- divsd        (double division, Chapter 13)
  deriving Repr, BEq

inductive CondCode where
  | E  : CondCode   -- equal
  | NE : CondCode   -- not equal
  | G  : CondCode   -- greater than (signed)
  | GE : CondCode   -- greater or equal (signed)
  | L  : CondCode   -- less than (signed)
  | LE : CondCode   -- less or equal (signed)
  -- Chapter 12: unsigned / double comparison condition codes
  | A  : CondCode   -- above (unsigned greater than / double GT after comisd)
  | AE : CondCode   -- above or equal
  | B  : CondCode   -- below (unsigned less than / double LT after comisd)
  | BE : CondCode   -- below or equal
  | P  : CondCode   -- parity even (PF=1); after comisd, set iff either operand was NaN
  deriving Repr, BEq

/-- Assembly instructions. -/
inductive Instruction where
  /-- Typed move: `movl` (Longword) or `movq` (Quadword). -/
  | Mov            : AsmType → Operand → Operand → Instruction
  /-- Chapter 13: scalar double move: `movsd src, dst`. -/
  | Movsd          : Operand → Operand → Instruction
  /-- Sign-extend 32-bit int to 64-bit long: `movslq src, dst`. -/
  | Movsx          : Operand → Operand → Instruction
  /-- Zero-extend 32-bit unsigned to 64-bit: `movl src32, dst32`. -/
  | MovZeroExtend  : Operand → Operand → Instruction
  | Unary          : AsmType → UnaryOp → Operand → Instruction
  | Binary         : AsmType → BinaryOp → Operand → Operand → Instruction
  | Cmp            : AsmType → Operand → Operand → Instruction
  | Idiv           : AsmType → Operand → Instruction
  /-- Unsigned division: `divl`/`divq`. -/
  | Div            : AsmType → Operand → Instruction
  /-- Sign-extend for division: Longword → `cdq`, Quadword → `cqo`. -/
  | Cdq            : AsmType → Instruction
  | Jmp            : String → Instruction
  | JmpCC          : CondCode → String → Instruction
  | SetCC          : CondCode → Operand → Instruction
  | Label          : String → Instruction
  /-- Push operand onto stack (always `pushq`). -/
  | Push           : Operand → Instruction
  | Call           : String → Instruction
  | Ret            : Instruction
  -- Chapter 13: floating-point conversion instructions --------
  /-- Convert integer to double: `cvtsi2sdl` (Longword) or `cvtsi2sdq` (Quadword). -/
  | Cvtsi2sd       : AsmType → Operand → Operand → Instruction
  /-- Truncate double to integer: `cvttsd2sil` (Longword) or `cvttsd2siq` (Quadword). -/
  | Cvttsd2si      : AsmType → Operand → Operand → Instruction
  /-- XOR packed doubles: `xorpd src, dst`. Used for double negation via `-0.0`. -/
  | Xorpd          : Operand → Operand → Instruction
  /-- Compare doubles: `comisd src, dst`. Sets ZF and CF; use B/BE/A/AE/E/NE. -/
  | Comisd         : Operand → Operand → Instruction
  /-- Load effective address: `leaq src, dst`.
      Computes the address of `src` (a memory location) and stores it in `dst`. -/
  | Lea            : Operand → Operand → Instruction   -- Chapter 14
  deriving Repr, BEq

/-- A typed static variable initializer. -/
inductive StaticInit where
  | IntInit    : Int   → StaticInit   -- 32-bit signed (.long)
  | LongInit   : Int   → StaticInit   -- 64-bit signed (.quad)
  | UIntInit   : Int   → StaticInit   -- 32-bit unsigned (.long)
  | ULongInit  : Int   → StaticInit   -- 64-bit unsigned (.quad)
  | DoubleInit : Float → StaticInit   -- 64-bit double (.double)  (Chapter 13)
  deriving Repr, BEq

structure FunctionDef where
  name         : String
  global       : Bool
  params       : List String
  instructions : List Instruction
  stackSize    : Int
  deriving Repr, BEq

/-- A top-level assembly item. -/
inductive AsmTopLevel where
  | Function       : FunctionDef → AsmTopLevel
  /-- Static variable: name, global flag, alignment (4 or 8), initializer. -/
  | StaticVariable : String → Bool → Nat → StaticInit → AsmTopLevel
  /-- Chapter 13: read-only constant: name, alignment, value.
      Emitted to `.section .rodata` (not .data/.bss). Never exported (no .globl). -/
  | StaticConstant : String → Nat → StaticInit → AsmTopLevel
  deriving Repr, BEq

structure Program where
  topLevels : List AsmTopLevel
  deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Backend symbol table
-- ---------------------------------------------------------------------------

/-- A backend symbol table entry.
    `ObjEntry(asmType, isSigned, isStatic)`: a scalar variable.
      - `asmType`:  Longword (int/uint), Quadword (long/ulong), Double (double).
      - `isSigned`: for integer types, true = signed; false = unsigned.
                    For Double, always false (not meaningful).
      - `isStatic`: true → `Data` (RIP-relative); false → stack slot.
    `FunEntry(isDefined, retAsmType)`: a function.
      - `isDefined`: true if the function body is in this translation unit.
      - `retAsmType`: determines the Mov source register after a call:
                      Longword/Quadword → %eax/%rax; Double → %xmm0. -/
inductive BackendSymEntry where
  | ObjEntry : AsmType → Bool → Bool → BackendSymEntry
  | FunEntry : Bool → AsmType → BackendSymEntry
  deriving Repr, BEq

abbrev BackendSymTable := List (String × BackendSymEntry)

def lookupBst (bst : BackendSymTable) (name : String) : Option BackendSymEntry :=
  match bst.find? (fun p => p.1 == name) with
  | some (_, e) => some e
  | none        => none

end AssemblyAST
