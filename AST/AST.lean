namespace AST

/-
  Abstract Syntax Tree for Chapter 1.

  ASDL definition:
    program            = Program(function_definition)
    function_definition = Function(identifier name, statement body)
    statement          = Return(exp)
    exp                = Constant(int)

  ASDL built-in types map to Lean as:
    identifier  →  String
    int         →  Int
-/

inductive Exp where
  | Constant : Int → Exp
  deriving Repr, BEq

inductive Statement where
  | Return : Exp → Statement
  deriving Repr, BEq

structure FunctionDef where
  name : String
  body : Statement
  deriving Repr, BEq

structure Program where
  func : FunctionDef
  deriving Repr, BEq

end AST
