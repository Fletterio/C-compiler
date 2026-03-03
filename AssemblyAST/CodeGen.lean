import AST.AST
import AssemblyAST.AssemblyAST

/-
  Assembly generation pass: converts AST.Program → AssemblyAST.Program.

  Conversion table (Table 1-2):
    AST node                      Assembly construct
    ─────────────────────────────────────────────────
    Program(function_definition)  Program(function_definition)
    Function(name, body)          Function(name, instructions)
    Return(exp)                   Mov(exp, Register) ; Ret
    Constant(int)                 Imm(int)
-/

namespace AssemblyAST

-- exp → operand
private def genExp : AST.Exp → Operand
  | .Constant n => .Imm n

-- statement → list of instructions
private def genStatement : AST.Statement → List Instruction
  | .Return e => [.Mov (genExp e) .Register, .Ret]

-- function definition → assembly function definition
private def genFunctionDef (f : AST.FunctionDef) : FunctionDef :=
  { name := f.name, instructions := genStatement f.body }

-- program → assembly program
def genProgram (p : AST.Program) : Program :=
  { func := genFunctionDef p.func }

end AssemblyAST
