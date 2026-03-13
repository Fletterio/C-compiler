import AST.AST

namespace Tacky

/-
  TACKY intermediate representation for Chapter 13.

  Chapter 13 additions:
    - Six new conversion instructions for double ↔ integer conversions:
        `IntToDouble`    (Int   → Double):  cvtsi2sdl
        `DoubleToInt`    (Double → Int):    cvttsd2sil (truncate toward zero)
        `UIntToDouble`   (UInt  → Double):  zero-extend to Long, then cvtsi2sdq
        `DoubleToUInt`   (Double → UInt):   convert to Long, truncate
        `ULongToDouble`  (ULong → Double):  two-step for values > LONG_MAX
        `DoubleToULong`  (Double → ULong):  two-step via 2^63 threshold
    - `StaticVariable` init changes from `Int` to `AST.Const` so that
      double-typed static variables carry `ConstDouble(f)` as their init.

  Chapter 12 additions:
    - `ZeroExtend(src, dst)`: zero-extend a 32-bit unsigned int to 64-bit.
      Lowers to `movl` (writing a 32-bit register zeros its upper 32 bits on x86-64).

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
                                        type typ, const init)
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
                       | SignExtend(val src, val dst)
                       | Truncate(val src, val dst)
                       | ZeroExtend(val src, val dst)
                       | ★ IntToDouble(val src, val dst)
                       | ★ DoubleToInt(val src, val dst)
                       | ★ UIntToDouble(val src, val dst)
                       | ★ DoubleToUInt(val src, val dst)
                       | ★ ULongToDouble(val src, val dst)
                       | ★ DoubleToULong(val src, val dst)
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
    Chapter 11 adds `SignExtend` and `Truncate` for type conversions.
    Chapter 12 adds `ZeroExtend`.
    Chapter 13 adds six double ↔ integer conversion instructions. -/
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
  /-- Sign-extend `src` (Int) into `dst` (Long/ULong): emits `movslq`. -/
  | SignExtend    : Val → Val → Instruction
  /-- Truncate `src` (Long/ULong) to `dst` (Int/UInt): emits `movl` (upper bits discarded). -/
  | Truncate      : Val → Val → Instruction
  /-- Zero-extend `src` (UInt, 32-bit) into `dst` (Long/ULong, 64-bit).
      On x86-64, movl to a 32-bit register zeroes the upper 32 bits. -/
  | ZeroExtend    : Val → Val → Instruction
  -- Chapter 13: double ↔ integer conversions ---------------------
  /-- Convert signed 32-bit `src` (Int) to 64-bit double `dst`: `cvtsi2sdl`. -/
  | IntToDouble    : Val → Val → Instruction
  /-- Truncate double `src` to signed 32-bit `dst` (Int): `cvttsd2sil`. -/
  | DoubleToInt    : Val → Val → Instruction
  /-- Convert unsigned 32-bit `src` (UInt) to double `dst`.
      Zero-extends to 64-bit first, then uses `cvtsi2sdq`. -/
  | UIntToDouble   : Val → Val → Instruction
  /-- Convert double `src` to unsigned 32-bit `dst` (UInt).
      Converts to Long first, then truncates. -/
  | DoubleToUInt   : Val → Val → Instruction
  /-- Convert unsigned 64-bit `src` (ULong) to double `dst`.
      Uses the two-step right-shift/OR trick for values > LONG_MAX. -/
  | ULongToDouble  : Val → Val → Instruction
  /-- Convert double `src` to unsigned 64-bit `dst` (ULong).
      Uses the 2^63 threshold trick. -/
  | DoubleToULong  : Val → Val → Instruction
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
    section/directive selection (.long vs .quad, .zero 4 vs .zero 8).
    Chapter 13: init is `AST.Const` (was `Int`) to support double inits. -/
inductive TackyTopLevel where
  | Function       : FunctionDef → TackyTopLevel
  /-- Static variable: name, global flag, scalar type, initial value. -/
  | StaticVariable : String → Bool → AST.Typ → AST.Const → TackyTopLevel
  deriving Repr, BEq

/-- A complete TACKY program. -/
structure Program where
  topLevels : List TackyTopLevel
  deriving Repr, BEq

end Tacky
