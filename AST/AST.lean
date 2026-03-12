namespace AST

/-
  Abstract Syntax Tree for Chapter 11.

  Chapter 11 additions:
    - `Typ`: the two scalar types supported: `Int` (32-bit) and `Long` (64-bit).
    - `Const`: typed integer constants — `ConstInt` vs `ConstLong` — so that the
       emitter can choose the correct assembly size for literal values.
    - `Exp.Constant` now wraps a `Const` instead of a raw `Int`.
    - `Exp.Cast(typ, exp)`: an explicit or implicit cast between `Int` and `Long`.
      Inserted by the parser for explicit `(long)e` / `(int)e` casts, and by the
      TypeCheck pass for implicit widening/narrowing conversions.
    - `Declaration.typ`: the declared type of the variable (default `Int`).
    - `FunctionDef.params` / `FunctionDecl.params` now carry `(Typ × String)` pairs
      so that each parameter's declared type is available for TypeCheck and CodeGen.
    - `FunctionDef.retTyp` / `FunctionDecl.retTyp`: the function's return type.

  ASDL definition (changes from Ch10 marked with ★):
    program            = Program(top_level*)
    top_level          = FunDef(function_def) | FunDecl(function_decl)
                       | VarDecl(declaration)
    ★ type             = Int | Long
    ★ const            = ConstInt(int) | ConstLong(int)
    function_def       = Function(identifier name,
                                  ★ (type × identifier)* params,
                                  ★ type retTyp,
                                  block_item* body,
                                  storage_class? storageClass)
    function_decl      = FunctionDecl(identifier name,
                                       ★ (type × identifier)* params,
                                       ★ type retTyp,
                                       storage_class? storageClass)
    block_item         = S(statement) | D(declaration) | FD(function_decl)
    declaration        = Declaration(identifier name, ★ type typ, exp? init,
                                     storage_class? storageClass)
    storage_class      = Static | Extern
    statement          = Return(exp)
                       | Expression(exp)
                       | If(exp condition, statement then, statement? else)
                       | Compound(block_item*)
                       | While(exp condition, statement, string? label)
                       | DoWhile(statement, exp condition, string? label)
                       | For(for_init, exp? condition, exp? post,
                               statement, string? label)
                       | Break(string? label)
                       | Continue(string? label)
                       | Switch(exp, statement, string? label,
                                 (int? × string)* cases)
                       | Case(int, statement, string? label)
                       | Default(statement, string? label)
                       | Labeled(identifier, statement)
                       | Goto(identifier)
                       | Null
    for_init           = InitExp(exp?) | InitDecl(declaration)
    exp                = ★ Constant(const)
                       | Var(identifier)
                       | ★ Cast(type, exp)
                       | Unary(unary_operator, exp)
                       | Binary(binary_operator, exp, exp)
                       | Assignment(exp, exp)
                       | Conditional(exp condition, exp, exp)
                       | PostfixIncr(exp)
                       | PostfixDecr(exp)
                       | FunCall(identifier, exp*)
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

/-- The two scalar integer types supported in Chapter 11.
    `Int`  is a 32-bit signed integer (C `int`).
    `Long` is a 64-bit signed integer (C `long`). -/
inductive Typ where
  | Int  : Typ   -- 32-bit signed integer
  | Long : Typ   -- 64-bit signed integer
  deriving Repr, BEq

/-- A typed integer constant.
    `ConstInt(n)`:  value fits in (or is explicitly typed as) 32-bit `int`.
    `ConstLong(n)`: value has the `l`/`L` suffix and is a 64-bit `long`. -/
inductive Const where
  | ConstInt  : Int → Const  -- 32-bit integer literal, e.g. 42
  | ConstLong : Int → Const  -- 64-bit long literal, e.g. 42L
  deriving Repr, BEq

/-- Storage-class specifier.  Chapter 10 introduces `static` and `extern`.
    `static` at file scope → internal linkage (not visible across TUs).
    `static` at block scope → static storage, no linkage.
    `extern` at file scope → external linkage, no definition in this TU.
    `extern` at block scope → refers to the file-scope variable of the same name. -/
inductive StorageClass where
  | Static : StorageClass   -- "static" specifier
  | Extern : StorageClass   -- "extern" specifier
  deriving Repr, BEq

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

/-- Expressions in the C subset.
    Chapter 11 adds `Cast` for explicit/implicit type conversions, and changes
    `Constant` to carry a typed `Const` instead of a raw `Int`. -/
inductive Exp where
  | Constant    : Const → Exp             -- Chapter 11: typed constant
  | Var         : String → Exp            -- variable reference
  | Cast        : Typ → Exp → Exp         -- Chapter 11: (type)expr cast
  | Unary       : UnaryOp → Exp → Exp
  | Binary      : BinaryOp → Exp → Exp → Exp
  | Assignment  : Exp → Exp → Exp         -- lvalue = rhs
  | Conditional : Exp → Exp → Exp → Exp  -- cond ? e1 : e2
  | PostfixIncr : Exp → Exp               -- extra credit: e++
  | PostfixDecr : Exp → Exp               -- extra credit: e--
  | FunCall     : String → List Exp → Exp -- Chapter 9: foo(a, b, c)
  deriving Repr, BEq

/-- A variable declaration with an optional initializer expression.
    Chapter 10 adds an optional storage-class specifier.
    Chapter 11 adds `typ` for the declared type of the variable. -/
structure Declaration where
  name         : String
  typ          : Typ := .Int               -- Chapter 11: variable type (default int)
  init         : Option Exp
  storageClass : Option StorageClass := none
  deriving Repr, BEq

/-- The initial clause of a `for` loop. -/
inductive ForInit where
  | InitExp  : Option Exp → ForInit
  | InitDecl : Declaration → ForInit
  deriving Repr

/-
  `Statement` and `BlockItem` are mutually recursive: `Compound` holds a
  `List BlockItem`, while each `BlockItem` may contain a `Statement`.
-/
mutual

/-- A statement in the C subset. -/
inductive Statement where
  | Return     : Exp → Statement
  | Expression : Exp → Statement
  | If         : Exp → Statement → Option Statement → Statement
  | Compound   : List BlockItem → Statement
  | While    : Exp → Statement → Option String → Statement
  | DoWhile  : Statement → Exp → Option String → Statement
  | For      : ForInit → Option Exp → Option Exp → Statement → Option String → Statement
  | Break    : Option String → Statement
  | Continue : Option String → Statement
  | Switch   : Exp → Statement → Option String → List (Option Int × String) → Statement
  | Case     : Int → Statement → Option String → Statement
  | Default  : Statement → Option String → Statement
  | Labeled  : String → Statement → Statement
  | Goto     : String → Statement
  | Null     : Statement

/-- A block item: statement, variable declaration, or local function declaration. -/
inductive BlockItem where
  | S  : Statement    → BlockItem
  | D  : Declaration  → BlockItem
  | FD : FunctionDecl → BlockItem

/-- A local function declaration (prototype only, no body).
    Chapter 11: params now carry type information. -/
structure FunctionDecl where
  name         : String
  params       : List (Typ × String)    -- Chapter 11: typed parameter list
  retTyp       : Typ := .Int             -- Chapter 11: return type
  storageClass : Option StorageClass := none

end

deriving instance Repr for Statement
deriving instance Repr for BlockItem
deriving instance Repr for FunctionDecl

/-- A complete function definition: name, typed parameter list, body, return type.
    Chapter 11: params carry types; retTyp records the declared return type. -/
structure FunctionDef where
  name         : String
  params       : List (Typ × String)    -- Chapter 11: typed parameter list
  retTyp       : Typ := .Int             -- Chapter 11: return type
  body         : List BlockItem
  storageClass : Option StorageClass := none
  deriving Repr

/-- Top-level item in a translation unit. -/
inductive TopLevel where
  | FunDef  : FunctionDef  → TopLevel
  | FunDecl : FunctionDecl → TopLevel
  | VarDecl : Declaration  → TopLevel
  deriving Repr

/-- A complete C program: a list of top-level declarations and definitions. -/
structure Program where
  topLevels : List TopLevel
  deriving Repr

end AST
