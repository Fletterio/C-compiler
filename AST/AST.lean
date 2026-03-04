namespace AST

/-
  Abstract Syntax Tree for Chapter 4.

  ASDL definition:
    program            = Program(function_definition)
    function_definition = Function(identifier name, statement body)
    statement          = Return(exp)
    exp                = Constant(int)
                       | Unary(unary_operator, exp)
                       | Binary(binary_operator, exp, exp)
    unary_operator     = Complement | Negate | Not
    binary_operator    = Add | Subtract | Multiply | Divide | Remainder
                       | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
                       | And | Or
                       | Equal | NotEqual
                       | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

  ASDL built-in types map to Lean as:
    identifier  →  String
    int         →  Int
-/

inductive UnaryOp where
  | Complement : UnaryOp  -- ~
  | Negate     : UnaryOp  -- unary -
  | Not        : UnaryOp  -- logical ! (produces 0 or 1)
  deriving Repr, BEq

/-- All binary operators.  Arithmetic and bitwise from Chapters 3/3-EC;
    logical and relational operators added in Chapter 4. -/
inductive BinaryOp where
  | Add          : BinaryOp  -- +
  | Subtract     : BinaryOp  -- -
  | Multiply     : BinaryOp  -- *
  | Divide       : BinaryOp  -- /
  | Remainder    : BinaryOp  -- %
  | BitAnd       : BinaryOp  -- &
  | BitOr        : BinaryOp  -- |
  | BitXor       : BinaryOp  -- ^
  | ShiftLeft    : BinaryOp  -- <<
  | ShiftRight   : BinaryOp  -- >>
  | And          : BinaryOp  -- &&  (short-circuit logical AND)
  | Or           : BinaryOp  -- ||  (short-circuit logical OR)
  | Equal        : BinaryOp  -- ==
  | NotEqual     : BinaryOp  -- !=
  | LessThan     : BinaryOp  -- <
  | LessOrEqual  : BinaryOp  -- <=
  | GreaterThan  : BinaryOp  -- >
  | GreaterOrEqual : BinaryOp -- >=
  deriving Repr, BEq

inductive Exp where
  | Constant : Int → Exp
  | Unary    : UnaryOp → Exp → Exp
  | Binary   : BinaryOp → Exp → Exp → Exp
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
