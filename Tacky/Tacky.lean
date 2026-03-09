namespace Tacky

/-
  TACKY intermediate representation for Chapter 9.

  ASDL definition:
    program            = Program(function_definition*)
    function_definition = Function(identifier name, identifier* params, instruction* body)
    instruction        = Return(val)
                       | Unary(unary_operator, val src, val dst)
                       | Binary(binary_operator, val src1, val src2, val dst)
                       | Copy(val src, val dst)
                       | Jump(identifier target)
                       | JumpIfZero(val condition, identifier target)
                       | JumpIfNotZero(val condition, identifier target)
                       | Label(identifier)
                       | FunCall(identifier fun_name, val* args, val dst)  -- Chapter 9
    val                = Constant(int) | Var(identifier)
    unary_operator     = Complement | Negate | Not
    binary_operator    = Add | Subtract | Multiply | Divide | Remainder
                       | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
                       | Equal | NotEqual
                       | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

  Note: the dst of Unary, Binary, Copy, and FunCall must always be a Var, never a Constant.
  Labels must be unique within a function (generated with a counter to guarantee this).
  In Chapter 9, the Program holds a list of FunctionDef (only definitions, not declarations).

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

/-- TACKY instructions.
    `FunCall` is new in Chapter 9: call a function with a list of argument
    values and store the return value in `dst`. -/
inductive Instruction where
  | Return        : Val → Instruction
  | Unary         : UnaryOp → Val → Val → Instruction         -- op, src, dst
  | Binary        : BinaryOp → Val → Val → Val → Instruction  -- op, src1, src2, dst
  | Copy          : Val → Val → Instruction                   -- src, dst
  | Jump          : String → Instruction                      -- unconditional jump to target
  | JumpIfZero    : Val → String → Instruction               -- jump to target if condition == 0
  | JumpIfNotZero : Val → String → Instruction              -- jump to target if condition != 0
  | Label         : String → Instruction                      -- defines a jump target
  | FunCall       : String → List Val → Val → Instruction     -- Chapter 9: call fun(args) → dst
  deriving Repr, BEq

/-- A TACKY function definition.
    Chapter 9 adds `params`: the renamed parameter variable names produced by
    VarResolution.  Assembly code generation uses these names to know which
    pseudo-registers to copy from the calling-convention registers (DI, SI, etc.). -/
structure FunctionDef where
  name   : String           -- function name
  params : List String      -- renamed parameter variable names (from VarResolution)
  body   : List Instruction
  deriving Repr, BEq

/-- A complete TACKY program.
    Chapter 9: the program holds a list of function definitions only
    (declarations are omitted at this stage; they carry no code). -/
structure Program where
  funcs : List FunctionDef
  deriving Repr, BEq

end Tacky
