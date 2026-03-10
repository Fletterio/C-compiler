namespace Tacky

/-
  TACKY intermediate representation for Chapter 10.

  Chapter 10 additions:
    - `global : Bool` field on `FunctionDef`: true if the function has external
      linkage (not declared `static`).  Used by CodeGen to pass along the
      global flag to the assembly AST.
    - `TackyTopLevel`: replaces the flat list of FunctionDef values.  A top-level
      item is now either a function definition or a static variable definition.
    - `StaticVariable(name, global, init)`: a file-scope or local-static variable
      with static storage duration.  `name` is the unique identifier (original
      name for file-scope; renamed `<orig>.<n>` for local static).  `global`
      indicates external linkage.  `init` is the initial integer value (0 for
      tentative definitions).
    - `Program.topLevels : List TackyTopLevel` replaces `Program.funcs`.

  ASDL definition:
    program            = Program(top_level*)
    top_level          = Function(function_definition)
                       | StaticVariable(identifier name, bool global, int init)
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
    val                = Constant(int) | Var(identifier)
    unary_operator     = Complement | Negate | Not
    binary_operator    = Add | Subtract | Multiply | Divide | Remainder
                       | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
                       | Equal | NotEqual
                       | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

  Note: static variables are addressed via the `StaticVariable` top-level, not
  as stack-allocated pseudoregisters.  The `Var(name)` operand in TACKY
  instructions refers to the unique name; PseudoReplace will map it to a
  `Data(name)` (RIP-relative) operand for static variables.

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
    Chapter 9 adds `params`.
    Chapter 10 adds `global`: true if this function has external linkage
    (i.e. NOT declared with the `static` specifier).  The assembly emitter
    uses this flag to decide whether to emit a `.globl` directive. -/
structure FunctionDef where
  name   : String           -- function name
  params : List String      -- renamed parameter variable names (from VarResolution)
  body   : List Instruction
  global : Bool             -- Chapter 10: true = external linkage, false = internal (static)
  deriving Repr, BEq

/-- A top-level item in the TACKY program.
    Chapter 10 adds `StaticVariable` for file-scope and local-static variables.
    `StaticVariable(name, global, init)`:
      - `name`:   the unique identifier (original for file-scope; `<orig>.<n>` for local-static)
      - `global`: true if externally visible (external linkage)
      - `init`:   initial value (0 for tentative/zero-initialized definitions)
    Function definitions that are declared-but-not-defined in this TU are
    represented as `FunDecl` entries in the AST but produce nothing in TACKY. -/
inductive TackyTopLevel where
  | Function       : FunctionDef → TackyTopLevel
  | StaticVariable : String → Bool → Int → TackyTopLevel   -- name, global, initVal
  deriving Repr, BEq

/-- A complete TACKY program.
    Chapter 10: the program holds a list of `TackyTopLevel` items, which
    include both function definitions and static variable definitions. -/
structure Program where
  topLevels : List TackyTopLevel
  deriving Repr, BEq

end Tacky
