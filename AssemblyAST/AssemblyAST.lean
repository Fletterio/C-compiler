namespace AssemblyAST

/-
  Assembly AST for Chapter 4.

  ASDL definition:
    program            = Program(function_definition)
    function_definition = Function(identifier name, instruction* instructions)
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
                       | Ret
    unary_operator     = Neg | Not
    binary_operator    = Add | Sub | Mult | And | Or | Xor | Sal | Sar
    cond_code          = E | NE | G | GE | L | LE
    operand            = Imm(int) | Reg(reg) | Pseudo(identifier) | Stack(int)
    reg                = AX | DX | CX | R10 | R11

  Pseudo operands represent temporary variables and must be eliminated
  (replaced with Stack operands) before code emission.
  AllocateStack corresponds to `subq $n, %rsp`; the surrounding prologue and
  epilogue instructions are added during code emission.
  Labels in Jmp, JmpCC, and Label are auto-generated names; they are mangled
  with a `.L` prefix during emission to avoid clashing with user function names.
-/

inductive Reg where
  | AX  : Reg   -- EAX / RAX  — return value; holds dividend low word for idiv
  | DX  : Reg   -- EDX / RDX  — holds remainder after idiv; dividend high word for idiv
  | CX  : Reg   -- ECX / RCX  — holds shift count (via %cl, its low byte)
  | R10 : Reg   -- R10D / R10 — scratch register for source operand fix-ups
  | R11 : Reg   -- R11D / R11 — scratch register for destination operand fix-ups
  deriving Repr, BEq

inductive Operand where
  | Imm    : Int → Operand     -- immediate value $n
  | Reg    : Reg → Operand     -- hardware register
  | Pseudo : String → Operand  -- pseudoregister (temporary variable)
  | Stack  : Int → Operand     -- stack slot n(%rbp)
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
  | Mov           : Operand → Operand → Instruction
  | Unary         : UnaryOp → Operand → Instruction
  | Binary        : BinaryOp → Operand → Operand → Instruction  -- op src, dst
  | Cmp           : Operand → Operand → Instruction  -- cmpl src, dst (computes dst−src, sets RFLAGS)
  | Idiv          : Operand → Instruction   -- idivl operand (divisor; dividend in EDX:EAX)
  | Cdq           : Instruction             -- cdq (sign-extend EAX into EDX:EAX)
  | Jmp           : String → Instruction    -- unconditional jump to label (mangled with .L prefix)
  | JmpCC         : CondCode → String → Instruction  -- conditional jump j<cc> .L<name>
  | SetCC         : CondCode → Operand → Instruction -- set<cc> using byte-register operand
  | Label         : String → Instruction    -- defines a local label (.L<name>:)
  | AllocateStack : Int → Instruction
  | Ret           : Instruction
  deriving Repr, BEq

structure FunctionDef where
  name         : String
  instructions : List Instruction
  deriving Repr, BEq

structure Program where
  func : FunctionDef
  deriving Repr, BEq

end AssemblyAST
