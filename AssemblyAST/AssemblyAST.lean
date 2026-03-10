namespace AssemblyAST

/-
  Assembly AST for Chapter 10.

  Chapter 10 additions:
    - `Data(identifier)`: a new operand for RIP-relative access to static
      variables stored in the `.data` or `.bss` section.
    - `global : Bool` on `FunctionDef`: true when the function has external
      linkage and requires a `.globl` directive in the emitter.
    - `AsmTopLevel`: replaces the flat `List FunctionDef`; now a program
      consists of both function definitions and static variable definitions.
    - `StaticVariable(name, global, init)`: a top-level assembly construct
      that emits `.data`/`.bss` directives for a static variable.
    - `Program.topLevels : List AsmTopLevel` replaces `Program.funcs`.

  ASDL definition:
    program            = Program(top_level*)
    top_level          = Function(function_definition)
                       | StaticVariable(identifier name, bool global, int init)
    function_definition = Function(identifier name, bool global,
                                   instruction* instructions, int stackSize)
    instruction        = Mov(operand src, operand dst)
                       | Unary(unary_operator, operand)
                       | Binary(binary_operator, operand src, operand dst)
                       | Cmp(operand, operand)
                       | Idiv(operand)
                       | Cdq
                       | Jmp(identifier)
                       | JmpCC(cond_code, identifier)
                       | SetCC(cond_code, operand)
                       | Label(identifier)
                       | AllocateStack(int)
                       | DeallocateStack(int)     -- Chapter 9: addq $n, %rsp
                       | Push(operand)            -- Chapter 9: pushq operand
                       | Call(identifier)         -- Chapter 9: call function
                       | Ret
    unary_operator     = Neg | Not
    binary_operator    = Add | Sub | Mult | And | Or | Xor | Sal | Sar
    cond_code          = E | NE | G | GE | L | LE
    operand            = Imm(int) | Reg(reg) | Pseudo(identifier)
                       | Stack(int) | Data(identifier)
    reg                = AX | DX | CX | DI | SI | R8 | R9 | R10 | R11

  Chapter 10: `Data(identifier)` operands represent RIP-relative (PC-relative)
  accesses to static variables.  They are emitted as `name(%rip)` in AT&T
  syntax.  PseudoReplace maps static-variable pseudo operands to Data instead
  of Stack.  FixUp treats Data as a memory operand, subject to the same
  mem-to-mem split rules as Stack.
-/

inductive Reg where
  | AX  : Reg   -- EAX / RAX  — return value; holds dividend low word for idiv
  | DX  : Reg   -- EDX / RDX  — holds remainder after idiv; dividend high word for idiv
  | CX  : Reg   -- ECX / RCX  — holds shift count (via %cl, its low byte)
  | DI  : Reg   -- EDI / RDI  — 1st calling-convention argument register (Chapter 9)
  | SI  : Reg   -- ESI / RSI  — 2nd calling-convention argument register (Chapter 9)
  | R8  : Reg   -- R8D / R8   — 5th calling-convention argument register (Chapter 9)
  | R9  : Reg   -- R9D / R9   — 6th calling-convention argument register (Chapter 9)
  | R10 : Reg   -- R10D / R10 — scratch register for source operand fix-ups
  | R11 : Reg   -- R11D / R11 — scratch register for destination operand fix-ups
  deriving Repr, BEq

/-- Assembly operands.
    Chapter 10 adds `Data(identifier)` for RIP-relative access to static
    variables in the data/BSS section.  Emitted as `name(%rip)`. -/
inductive Operand where
  | Imm    : Int → Operand     -- immediate value $n
  | Reg    : Reg → Operand     -- hardware register
  | Pseudo : String → Operand  -- pseudoregister (temporary; replaced by PseudoReplace)
  | Stack  : Int → Operand     -- stack slot n(%rbp)
  | Data   : String → Operand  -- Chapter 10: RIP-relative static variable name(%rip)
  deriving Repr, BEq

inductive UnaryOp where
  | Neg : UnaryOp  -- negl
  | Not : UnaryOp  -- notl
  deriving Repr, BEq

/-- Binary operators that share the `op src, dst` encoding.
    Division and remainder are handled separately via `Idiv` and `Cdq`.
    Shift instructions (Sal/Sar) require the count in `%cl` or as an
    immediate; `Reg(CX)` in the source position of a shift is emitted
    as `%cl` (the low byte of ECX) rather than `%ecx`. -/
inductive BinaryOp where
  | Add  : BinaryOp  -- addl
  | Sub  : BinaryOp  -- subl
  | Mult : BinaryOp  -- imull
  | And  : BinaryOp  -- andl
  | Or   : BinaryOp  -- orl
  | Xor  : BinaryOp  -- xorl
  | Sal  : BinaryOp  -- sall  (shift arithmetic left;  count must be %cl or Imm)
  | Sar  : BinaryOp  -- sarl  (shift arithmetic right; count must be %cl or Imm)
  deriving Repr, BEq

inductive CondCode where
  | E  : CondCode  -- equal / zero        (ZF=1)
  | NE : CondCode  -- not equal / nonzero (ZF=0)
  | G  : CondCode  -- signed greater than (ZF=0 and SF=OF)
  | GE : CondCode  -- signed ≥            (SF=OF)
  | L  : CondCode  -- signed less than    (SF≠OF)
  | LE : CondCode  -- signed ≤            (ZF=1 or SF≠OF)
  deriving Repr, BEq

inductive Instruction where
  | Mov            : Operand → Operand → Instruction
  | Unary          : UnaryOp → Operand → Instruction
  | Binary         : BinaryOp → Operand → Operand → Instruction  -- op src, dst
  | Cmp            : Operand → Operand → Instruction  -- cmpl src, dst (computes dst−src, sets RFLAGS)
  | Idiv           : Operand → Instruction   -- idivl operand (divisor; dividend in EDX:EAX)
  | Cdq            : Instruction             -- cdq (sign-extend EAX into EDX:EAX)
  | Jmp            : String → Instruction    -- unconditional jump to label (mangled with .L prefix)
  | JmpCC          : CondCode → String → Instruction  -- conditional jump j<cc> .L<name>
  | SetCC          : CondCode → Operand → Instruction -- set<cc> using byte-register operand
  | Label          : String → Instruction    -- defines a local label (.L<name>:)
  | AllocateStack  : Int → Instruction       -- subq $n, %rsp  (stack frame allocation)
  | DeallocateStack : Int → Instruction      -- addq $n, %rsp  (Chapter 9: reclaim arg space)
  | Push           : Operand → Instruction   -- pushq operand  (Chapter 9: pass stack arg)
  | Call           : String → Instruction    -- call function  (Chapter 9: invoke function)
  | Ret            : Instruction
  deriving Repr, BEq

/-- An assembly function definition.
    Chapter 9 adds `params` and `stackSize`.
    Chapter 10 adds `global`: true if the function has external linkage and
    requires a `.globl` directive in the emitter. -/
structure FunctionDef where
  name         : String
  global       : Bool          -- Chapter 10: true = external linkage, emit .globl
  params       : List String   -- renamed parameter names (for codegen entry copies)
  instructions : List Instruction
  stackSize    : Int           -- bytes needed for locals (filled in by PseudoReplace)
  deriving Repr, BEq

/-- A top-level item in the assembly program.
    Chapter 10: a program can contain both function definitions and static
    variable definitions.
    `StaticVariable(name, global, init)`:
      - `name`:   identifier (original for file-scope; renamed for local-static)
      - `global`: true if the symbol has external linkage (emits `.globl` directive)
      - `init`:   initial integer value (0 for BSS, nonzero for data section) -/
inductive AsmTopLevel where
  | Function       : FunctionDef → AsmTopLevel
  | StaticVariable : String → Bool → Int → AsmTopLevel  -- name, global, init
  deriving Repr, BEq

/-- A complete assembly program.
    Chapter 10: holds a list of `AsmTopLevel` items (functions and static vars). -/
structure Program where
  topLevels : List AsmTopLevel
  deriving Repr, BEq

end AssemblyAST
