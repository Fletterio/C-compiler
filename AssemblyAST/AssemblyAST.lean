namespace AssemblyAST

/-
  Assembly AST for Chapter 11.

  Chapter 11 additions:
    - `AsmType`: `Longword` (4-byte, suffix `l`) vs `Quadword` (8-byte, suffix `q`).
    - All arithmetic/comparison instructions carry an `AsmType` parameter.
    - `Movsx`: sign-extend 32-bit to 64-bit (`movslq`).
    - `SP` register: `%rsp`, used for stack-pointer arithmetic.
    - `AllocateStack` and `DeallocateStack` removed; stack-frame manipulation
      is now expressed as `Binary(Quadword, Sub/Add, Imm(n), Reg(SP))`.
    - `StaticInit`: typed static initializer — `IntInit` (.long / .zero 4) or
      `LongInit` (.quad / .zero 8).
    - `StaticVariable` now carries an alignment (4 or 8) and a `StaticInit`.
    - `BackendSymEntry` / `BackendSymTable`: the backend symbol table consumed
      by CodeGen and PseudoReplace to determine instruction types and stack sizes.

  ASDL definition:
    program            = Program(top_level*)
    top_level          = Function(function_definition)
                       | StaticVariable(identifier name, bool global,
                                        int alignment, static_init init)
    static_init        = IntInit(int) | LongInit(int)
    function_definition = Function(identifier name, bool global,
                                   identifier* params,
                                   instruction* instructions, int stackSize)
    instruction        = Mov(asm_type, operand src, operand dst)
                       | Movsx(operand src, operand dst)   -- movslq (int→long)
                       | Unary(asm_type, unary_operator, operand)
                       | Binary(asm_type, binary_operator, operand src, operand dst)
                       | Cmp(asm_type, operand, operand)
                       | Idiv(asm_type, operand)
                       | Cdq(asm_type)                    -- Longword=cdq, Quadword=cqo
                       | Jmp(identifier)
                       | JmpCC(cond_code, identifier)
                       | SetCC(cond_code, operand)
                       | Label(identifier)
                       | Push(operand)                    -- always pushq
                       | Call(identifier)
                       | Ret
    asm_type           = Longword | Quadword
    unary_operator     = Neg | Not
    binary_operator    = Add | Sub | Mult | And | Or | Xor | Sal | Sar
    cond_code          = E | NE | G | GE | L | LE
    operand            = Imm(int) | Reg(reg) | Pseudo(identifier)
                       | Stack(int) | Data(identifier)
    reg                = AX | DX | CX | DI | SI | R8 | R9 | R10 | R11 | SP
-/

/-- The two assembly sizes used in Chapter 11.
    `Longword` = 4 bytes (32-bit, suffix `l`).
    `Quadword` = 8 bytes (64-bit, suffix `q`). -/
inductive AsmType where
  | Longword : AsmType   -- 4-byte, corresponds to C `int`
  | Quadword : AsmType   -- 8-byte, corresponds to C `long`
  deriving Repr, BEq

inductive Reg where
  | AX  : Reg   -- EAX / RAX
  | DX  : Reg   -- EDX / RDX
  | CX  : Reg   -- ECX / RCX
  | DI  : Reg   -- EDI / RDI  (1st arg)
  | SI  : Reg   -- ESI / RSI  (2nd arg)
  | R8  : Reg   -- R8D / R8   (5th arg)
  | R9  : Reg   -- R9D / R9   (6th arg)
  | R10 : Reg   -- scratch for source fix-ups
  | R11 : Reg   -- scratch for destination fix-ups
  /-- Stack pointer `%rsp` — used in prologue/epilogue Binary instructions. -/
  | SP  : Reg
  deriving Repr, BEq

inductive Operand where
  | Imm    : Int → Operand
  | Reg    : Reg → Operand
  | Pseudo : String → Operand
  | Stack  : Int → Operand
  | Data   : String → Operand
  deriving Repr, BEq

inductive UnaryOp where
  | Neg : UnaryOp   -- negl / negq
  | Not : UnaryOp   -- notl / notq
  deriving Repr, BEq

/-- Binary operators that share the `op src, dst` encoding. -/
inductive BinaryOp where
  | Add  : BinaryOp   -- addl / addq
  | Sub  : BinaryOp   -- subl / subq
  | Mult : BinaryOp   -- imull / imulq
  | And  : BinaryOp   -- andl / andq
  | Or   : BinaryOp   -- orl  / orq
  | Xor  : BinaryOp   -- xorl / xorq
  | Sal  : BinaryOp   -- sall / salq  (shift left)
  | Sar  : BinaryOp   -- sarl / sarq  (shift right)
  deriving Repr, BEq

inductive CondCode where
  | E  : CondCode
  | NE : CondCode
  | G  : CondCode
  | GE : CondCode
  | L  : CondCode
  | LE : CondCode
  deriving Repr, BEq

/-- Assembly instructions.
    Chapter 11: most instructions carry an `AsmType` to select `l` vs `q` suffix.
    `AllocateStack` and `DeallocateStack` are removed; use
    `Binary(Quadword, Sub/Add, Imm(n), Reg(SP))` instead. -/
inductive Instruction where
  /-- Typed move: `movl` (Longword) or `movq` (Quadword). -/
  | Mov            : AsmType → Operand → Operand → Instruction
  /-- Sign-extend 32-bit int to 64-bit long: `movslq src, dst`. -/
  | Movsx          : Operand → Operand → Instruction
  | Unary          : AsmType → UnaryOp → Operand → Instruction
  | Binary         : AsmType → BinaryOp → Operand → Operand → Instruction
  | Cmp            : AsmType → Operand → Operand → Instruction
  | Idiv           : AsmType → Operand → Instruction
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
  deriving Repr, BEq

/-- A typed static variable initializer.
    `IntInit(n)` → `.long n` / `.zero 4` (4-byte).
    `LongInit(n)` → `.quad n` / `.zero 8` (8-byte). -/
inductive StaticInit where
  | IntInit  : Int → StaticInit   -- 32-bit initializer
  | LongInit : Int → StaticInit   -- 64-bit initializer
  deriving Repr, BEq

structure FunctionDef where
  name         : String
  global       : Bool
  params       : List String
  instructions : List Instruction
  stackSize    : Int
  deriving Repr, BEq

/-- A top-level assembly item.
    Chapter 11: `StaticVariable` carries an alignment and typed initializer. -/
inductive AsmTopLevel where
  | Function       : FunctionDef → AsmTopLevel
  /-- Static variable: name, global flag, alignment (4 or 8), initializer. -/
  | StaticVariable : String → Bool → Nat → StaticInit → AsmTopLevel
  deriving Repr, BEq

structure Program where
  topLevels : List AsmTopLevel
  deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Backend symbol table
-- ---------------------------------------------------------------------------

/-- A backend symbol table entry.
    `ObjEntry(asmType, isStatic)`: a scalar variable.
      - `asmType`: determines instruction sizes (Longword for int, Quadword for long).
      - `isStatic`: true → mapped to a `Data` (RIP-relative) operand by PseudoReplace;
                    false → assigned a stack slot.
    `FunEntry(isDefined, retAsmType)`: a function.
      - `isDefined`: true if the function body is in this translation unit.
      - `retAsmType`: determines the size of the `Mov` from AX after a call. -/
inductive BackendSymEntry where
  | ObjEntry : AsmType → Bool → BackendSymEntry
  | FunEntry : Bool → AsmType → BackendSymEntry
  deriving Repr, BEq

/-- The backend symbol table: an association list used by CodeGen, PseudoReplace,
    and FixUp to resolve types and storage decisions. -/
abbrev BackendSymTable := List (String × BackendSymEntry)

/-- Look up an entry in the backend symbol table. -/
def lookupBst (bst : BackendSymTable) (name : String) : Option BackendSymEntry :=
  match bst.find? (fun p => p.1 == name) with
  | some (_, e) => some e
  | none        => none

end AssemblyAST
