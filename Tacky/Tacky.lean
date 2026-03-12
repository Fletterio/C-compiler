import AST.AST

namespace Tacky

/-
  TACKY intermediate representation for Chapter 11.

  Chapter 11 additions:
    - `SignExtend(src, dst)`: sign-extend a 32-bit int value to 64-bit long.
      Lowers to `movslq` in the assembler.
    - `Truncate(src, dst)`: truncate a 64-bit long value to 32-bit int.
      Lowers to `movl` (upper bits are ignored).
    - `StaticVariable` now carries the variable's scalar type (`AST.Typ`) so
      that the assembly emitter can choose `.long`/`.zero 4` for Int and
      `.quad`/`.zero 8` for Long.

  ASDL definition:
    program            = Program(top_level*)
    top_level          = Function(function_definition)
                       | StaticVariable(identifier name, bool global,
                                        ★ type typ, int init)
    function_definition = Function(identifier name, identifier* params,
                                   instruction* body, bool global)
    instruction        = Return(val)
                       | Unary(unary_operator, val src, val dst)
                       | Binary(binary_operator, val src1, val src2, val dst)
                       | Copy(val src, val dst)
                       | Jump(identifier target)
                       | JumpIfZero(val condition, identifier target)
                       | JumpIfNotZero(val condition, identifier target)
                       | Label(identifier)
                       | FunCall(identifier fun_name, val* args, val dst)
                       | ★ SignExtend(val src, val dst)
                       | ★ Truncate(val src, val dst)
    val                = Constant(int) | Var(identifier)
    unary_operator     = Complement | Negate | Not
    binary_operator    = Add | Subtract | Multiply | Divide | Remainder
                       | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
                       | Equal | NotEqual
                       | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual
-/

inductive UnaryOp where
  | Complement : UnaryOp
  | Negate     : UnaryOp
  | Not        : UnaryOp
  deriving Repr, BEq

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
  | Equal        : BinaryOp
  | NotEqual     : BinaryOp
  | LessThan     : BinaryOp
  | LessOrEqual  : BinaryOp
  | GreaterThan  : BinaryOp
  | GreaterOrEqual : BinaryOp
  deriving Repr, BEq

inductive Val where
  | Constant : Int → Val
  | Var      : String → Val
  deriving Repr, BEq

/-- TACKY instructions.
    Chapter 11 adds `SignExtend` and `Truncate` for type conversions. -/
inductive Instruction where
  | Return        : Val → Instruction
  | Unary         : UnaryOp → Val → Val → Instruction
  | Binary        : BinaryOp → Val → Val → Val → Instruction
  | Copy          : Val → Val → Instruction
  | Jump          : String → Instruction
  | JumpIfZero    : Val → String → Instruction
  | JumpIfNotZero : Val → String → Instruction
  | Label         : String → Instruction
  | FunCall       : String → List Val → Val → Instruction
  /-- Sign-extend `src` (Int) into `dst` (Long): emits `movslq`. -/
  | SignExtend    : Val → Val → Instruction
  /-- Truncate `src` (Long) to `dst` (Int): emits `movl` (upper bits discarded). -/
  | Truncate      : Val → Val → Instruction
  deriving Repr, BEq

/-- A TACKY function definition. -/
structure FunctionDef where
  name   : String
  params : List String      -- renamed parameter names
  body   : List Instruction
  global : Bool
  deriving Repr, BEq

/-- A top-level item in the TACKY program.
    Chapter 11: `StaticVariable` carries the variable type for proper assembly
    section/directive selection (.long vs .quad, .zero 4 vs .zero 8). -/
inductive TackyTopLevel where
  | Function       : FunctionDef → TackyTopLevel
  /-- Static variable: name, global flag, scalar type, initial value. -/
  | StaticVariable : String → Bool → AST.Typ → Int → TackyTopLevel
  deriving Repr, BEq

/-- A complete TACKY program. -/
structure Program where
  topLevels : List TackyTopLevel
  deriving Repr, BEq

end Tacky
