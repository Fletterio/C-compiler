namespace Tacky

/-
  TACKY intermediate representation for Chapter 4.

  ASDL definition:
    program            = Program(function_definition)
    function_definition = Function(identifier, instruction* body)
    instruction        = Return(val)
                       | Unary(unary_operator, val src, val dst)
                       | Binary(binary_operator, val src1, val src2, val dst)
                       | Copy(val src, val dst)
                       | Jump(identifier target)
                       | JumpIfZero(val condition, identifier target)
                       | JumpIfNotZero(val condition, identifier target)
                       | Label(identifier)
    val                = Constant(int) | Var(identifier)
    unary_operator     = Complement | Negate | Not
    binary_operator    = Add | Subtract | Multiply | Divide | Remainder
                       | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
                       | Equal | NotEqual
                       | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

  Note: the dst of Unary, Binary, and Copy must always be a Var, never a Constant.
  Labels must be unique within a function (generated with a counter to guarantee this).

  ASDL built-in types map to Lean as:
    identifier  →  String
    int         →  Int
-/

inductive UnaryOp where
  | Complement : UnaryOp  -- bitwise ~
  | Negate     : UnaryOp  -- arithmetic unary -
  | Not        : UnaryOp  -- logical !  (produces 0 or 1)
  deriving Repr, BEq

/-- The arithmetic, bitwise, and relational binary operators in TACKY.
    Logical && and || are NOT represented here; they lower to conditional
    jumps in TackyGen. -/
inductive BinaryOp where
  | Add          : BinaryOp
  | Subtract     : BinaryOp
  | Multiply     : BinaryOp
  | Divide       : BinaryOp
  | Remainder    : BinaryOp
  | BitAnd       : BinaryOp
  | BitOr        : BinaryOp
  | BitXor       : BinaryOp
  | ShiftLeft    : BinaryOp
  | ShiftRight   : BinaryOp
  | Equal        : BinaryOp  -- ==  (result is 0 or 1)
  | NotEqual     : BinaryOp  -- !=  (result is 0 or 1)
  | LessThan     : BinaryOp  -- <   (result is 0 or 1)
  | LessOrEqual  : BinaryOp  -- <=  (result is 0 or 1)
  | GreaterThan  : BinaryOp  -- >   (result is 0 or 1)
  | GreaterOrEqual : BinaryOp -- >= (result is 0 or 1)
  deriving Repr, BEq

inductive Val where
  | Constant : Int → Val
  | Var      : String → Val
  deriving Repr, BEq

inductive Instruction where
  | Return       : Val → Instruction
  | Unary        : UnaryOp → Val → Val → Instruction         -- op, src, dst
  | Binary       : BinaryOp → Val → Val → Val → Instruction  -- op, src1, src2, dst
  | Copy         : Val → Val → Instruction                   -- src, dst
  | Jump         : String → Instruction                      -- unconditional jump to target
  | JumpIfZero   : Val → String → Instruction               -- jump to target if condition == 0
  | JumpIfNotZero : Val → String → Instruction              -- jump to target if condition != 0
  | Label        : String → Instruction                      -- defines a jump target
  deriving Repr, BEq

structure FunctionDef where
  name : String
  body : List Instruction
  deriving Repr, BEq

structure Program where
  func : FunctionDef
  deriving Repr, BEq

end Tacky
