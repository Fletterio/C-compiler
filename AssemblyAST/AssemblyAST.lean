namespace AssemblyAST

/-
  Assembly AST for Chapter 1.

  ASDL definition:
    program            = Program(function_definition)
    function_definition = Function(identifier name, instruction* instructions)
    instruction        = Mov(operand src, operand dst) | Ret
    operand            = Imm(int) | Register

  For now, Register refers exclusively to EAX.
  Additional registers will be added in later chapters.
-/

inductive Operand where
  | Imm      : Int → Operand  -- immediate (constant) value
  | Register : Operand        -- EAX
  deriving Repr, BEq

inductive Instruction where
  | Mov : Operand → Operand → Instruction  -- mov src, dst
  | Ret : Instruction
  deriving Repr, BEq

structure FunctionDef where
  name         : String
  instructions : List Instruction
  deriving Repr, BEq

structure Program where
  func : FunctionDef
  deriving Repr, BEq

end AssemblyAST
