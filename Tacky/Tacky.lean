import AST.AST

namespace Tacky

/-
  TACKY intermediate representation for Chapter 15.

  Chapter 15 additions:
    - `CopyToOffset(src, dstName, offset)`: copy a scalar value into a byte
      offset within a named aggregate (array) variable.  Used for array
      initializers: `int arr[3] = {1,2,3}` → three CopyToOffset instructions.
    - `AddPtr(ptr, index, scale, dst)`: dst = ptr + index * scale.
      Used for pointer arithmetic and subscript operations (after TypeCheck
      desugars `a[i]` to `*(a + i)` and TackyGen detects the pointer add).
    - `StaticVariable` init changed from a single `AST.Const` to `List StaticInit`,
      enabling static arrays to carry an initializer list.
    - `StaticInit`: a new tagged union for static initializer elements, including
      `ZeroInit n` for emitting `.zero n` (a block of n zero bytes).

  Chapter 14 additions:
    - `Load(ptr, dst)`:       dst = *ptr  (load through pointer)
    - `Store(src, ptr)`:      *ptr = src  (store through pointer)
    - `GetAddress(src, dst)`: dst = &src  (take address of a variable)

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
                       | ★★ Load(val ptr, val dst)
                       | ★★ Store(val src, val ptr)
                       | ★★ GetAddress(val src, val dst)
                       | ★★★ CopyToOffset(val src, identifier dst, int offset)
                       | ★★★ AddPtr(val ptr, val index, int scale, val dst)
    val                = Constant(int) | Var(identifier)
    unary_operator     = Complement | Negate | Not
    binary_operator    = Add | Subtract | Multiply | Divide | Remainder
                       | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
                       | Equal | NotEqual
                       | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual
    static_init        = IntInit(int) | LongInit(int) | UIntInit(int) | ULongInit(int)
                       | DoubleInit(float) | ★★★ ZeroInit(int n)   -- .zero n bytes
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
  /-- Sign-extend `src` into `dst`.
      Chapter 16: now carries the source `AST.Typ` so CodeGen can determine the
      source AsmType even for constant operands (where valAsmType returns Longword
      regardless of whether the constant was a char, int, etc.).
      - Char/SChar:  Byte → Longword or Byte → Quadword (movsbl / movsbq)
      - Int:        Longword → Quadword (movslq) -/
  | SignExtend    : AST.Typ → Val → Val → Instruction
  /-- Truncate `src` (Long/ULong) to `dst` (Int/UInt/Char): emits `movl`/`movb`
      (upper bits discarded; dst AsmType determined from BST). -/
  | Truncate      : Val → Val → Instruction
  /-- Zero-extend `src` into `dst`.
      Chapter 16: now carries the source `AST.Typ` so CodeGen can determine the
      source AsmType even for constant operands.
      - UChar:  Byte → Longword or Byte → Quadword (movzbl / movzbq)
      - UInt:   Longword → Quadword (movl to 32-bit reg, auto-zeros upper 32 bits) -/
  | ZeroExtend    : AST.Typ → Val → Val → Instruction
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
  -- Chapter 14: pointer operations --------------------------------
  /-- Load value from pointer: emit `movX (*ptr), dst`. -/
  | Load       : Val → Val → Instruction
  /-- Store value through pointer: emit `movX src, (*ptr)`. -/
  | Store      : Val → Val → Instruction
  /-- Take address of a variable: emit `leaq src, dst`. -/
  | GetAddress : Val → Val → Instruction
  -- Chapter 15: array / pointer-arithmetic operations -----------
  /-- Copy scalar `src` into byte `offset` of aggregate variable `dstName`.
      Used for aggregate initialization: `int arr[3] = {1,2,3}` emits three
      `CopyToOffset` instructions, one per element. -/
  | CopyToOffset : Val → String → Int → Instruction
  /-- Pointer arithmetic: `dst = ptr + index * scale`.
      `scale` is the element size in bytes (always a positive constant).
      For `ptr - int`, TackyGen negates the index before emitting AddPtr. -/
  | AddPtr       : Val → Val → Int → Val → Instruction
  deriving Repr, BEq

/-- A TACKY function definition. -/
structure FunctionDef where
  name   : String
  params : List String      -- renamed parameter names
  body   : List Instruction
  global : Bool
  deriving Repr, BEq

/-- Chapter 15: A single element of a static variable's initializer list.
    A scalar variable has a one-element list; an array has one entry per element.
    `ZeroInit n` emits `.zero n` — an efficient block of n zero bytes.
    This mirrors the AssemblyAST.StaticInit type but lives in the TACKY layer.
    Chapter 16 adds:
      `CharInit(n)`           — 1-byte char value (`.byte n`).
      `UCharInit(n)`          — 1-byte unsigned char value (`.byte n`).
      `StringInit(s, null)`   — string bytes; `null=true` → `.asciz` (with `\0`);
                                 `null=false` → `.ascii` (without `\0`).
      `PointerInit(label)`    — 8-byte pointer to a label (`.quad label`). -/
inductive StaticInit where
  | IntInit    : Int   → StaticInit   -- 32-bit value  → .long
  | LongInit   : Int   → StaticInit   -- 64-bit value  → .quad
  | UIntInit   : Int   → StaticInit   -- 32-bit unsigned → .long
  | ULongInit  : Int   → StaticInit   -- 64-bit unsigned → .quad
  | DoubleInit : Float → StaticInit   -- 64-bit double → .quad (bit pattern)
  | ZeroInit   : Nat   → StaticInit   -- n zero bytes  → .zero n
  | CharInit   : Int   → StaticInit   -- Chapter 16: 1-byte char → .byte n
  | UCharInit  : Int   → StaticInit   -- Chapter 16: 1-byte uchar → .byte n
  | StringInit : String → Bool → StaticInit  -- Chapter 16: string bytes (.asciz/.ascii)
  | PointerInit : String → StaticInit -- Chapter 16: 8-byte pointer to label (.quad label)
  deriving Repr, BEq

/-- A top-level item in the TACKY program.
    Chapter 11: `StaticVariable` carries the variable type for proper assembly
    section/directive selection (.long vs .quad, .zero 4 vs .zero 8).
    Chapter 13: init was `AST.Const` (was `Int`) to support double inits.
    Chapter 15: init is `List StaticInit` to support array initializer lists.
    Chapter 16: `StaticConstant` holds read-only string data in `.rodata`. -/
inductive TackyTopLevel where
  | Function       : FunctionDef → TackyTopLevel
  /-- Static variable: name, global flag, type, list of static initializers.
      For scalar variables the list has exactly one element.
      For array variables the list has one element per array element.
      `ZeroInit n` can compact a run of zero-valued elements. -/
  | StaticVariable : String → Bool → AST.Typ → List StaticInit → TackyTopLevel
  /-- Chapter 16: Read-only constant in `.rodata`.  Used for string literals whose
      address is taken (e.g. `char *p = "hello"`).
      name = label (e.g. `.Lstr.0`), alignment = 1 for char arrays,
      inits = list of `StringInit`/`ZeroInit` etc. -/
  | StaticConstant : String → Nat → List StaticInit → TackyTopLevel
  deriving Repr, BEq

/-- A complete TACKY program. -/
structure Program where
  topLevels : List TackyTopLevel
  deriving Repr, BEq

end Tacky
