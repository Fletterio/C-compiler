import AssemblyAST.AssemblyAST

/-
  Code emission pass: converts AssemblyAST.Program to x64 assembly text.

  Linux conventions:
  - Function labels are emitted as-is (no leading underscore).
  - A .section .note.GNU-stack line is appended to mark the stack
    non-executable (security hardening).

  Formatting (Tables 1-3, 1-4, 1-5):
    Operand   Register  →  %eax
              Imm(n)    →  $n
    Instr     Mov s d   →  movl <s>, <d>    (indented)
              Ret       →  ret              (indented)
    Function  name      →  .globl <name>
                            <name>:
                            <instructions>
    Program             →  <function>
                            .section .note.GNU-stack,"",@progbits
-/

namespace Emission

open AssemblyAST

private def emitOperand : Operand → String
  | .Imm n    => s!"${n}"
  | .Register => "%eax"

private def emitInstruction : Instruction → String
  | .Mov src dst => s!"    movl {emitOperand src}, {emitOperand dst}"
  | .Ret         => "    ret"

private def emitFunctionDef (f : FunctionDef) : String :=
  let instrs := String.intercalate "\n" (f.instructions.map emitInstruction)
  s!"    .globl {f.name}\n{f.name}:\n{instrs}"

def emitProgram (p : Program) : String :=
  let func := emitFunctionDef p.func
  s!"{func}\n    .section .note.GNU-stack,\"\",@progbits\n"

end Emission
