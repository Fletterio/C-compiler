namespace AST

/-
  Abstract Syntax Tree for Chapter 10.

  ASDL definition:
    program            = Program(top_level*)
    top_level          = FunDef(function_def) | FunDecl(function_decl)
                       | VarDecl(declaration)           -- Chapter 10: file-scope variable
    function_def       = Function(identifier name, identifier* params, block_item* body,
                                  storage_class? storageClass)
    function_decl      = FunctionDecl(identifier name, identifier* params,
                                      storage_class? storageClass)
    block_item         = S(statement) | D(declaration) | FD(function_decl)
    declaration        = Declaration(identifier name, exp? init,
                                     storage_class? storageClass)  -- Chapter 10: storage class
    storage_class      = Static | Extern                           -- Chapter 10
    statement          = Return(exp)
                       | Expression(exp)
                       | If(exp condition, statement then, statement? else)
                       | Compound(block_item*)               -- Chapter 7: "{ ... }"
                       | While(exp condition, statement, string? label)     -- Chapter 8
                       | DoWhile(statement, exp condition, string? label)   -- Chapter 8
                       | For(for_init, exp? condition, exp? post,           -- Chapter 8
                               statement, string? label)
                       | Break(string? label)                               -- Chapter 8
                       | Continue(string? label)                            -- Chapter 8
                       | Switch(exp, statement, string? label,              -- Chapter 8 EC
                                 (int? × string)* cases)
                       | Case(int, statement, string? label)                -- Chapter 8 EC
                       | Default(statement, string? label)                  -- Chapter 8 EC
                       | Labeled(identifier, statement)  -- extra credit ch6: "label: stmt"
                       | Goto(identifier)               -- extra credit ch6: "goto label;"
                       | Null
    for_init           = InitExp(exp?) | InitDecl(declaration)
    exp                = Constant(int)
                       | Var(identifier)
                       | Unary(unary_operator, exp)
                       | Binary(binary_operator, exp, exp)
                       | Assignment(exp, exp)
                       | Conditional(exp condition, exp, exp)
                       | PostfixIncr(exp)        -- extra credit: e++
                       | PostfixDecr(exp)        -- extra credit: e--
                       | FunCall(identifier, exp*)  -- Chapter 9: function call
    unary_operator     = Complement | Negate | Not
    binary_operator    = Add | Subtract | Multiply | Divide | Remainder
                       | BitAnd | BitOr | BitXor | ShiftLeft | ShiftRight
                       | And | Or
                       | Equal | NotEqual
                       | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

  Prefix ++ and -- and compound assignment operators (+=, -=, etc.) are
  desugared into Assignment nodes during parsing and never appear in the AST.
  Postfix ++ and -- require preserving the original value and so are kept
  as distinct AST nodes.

  ASDL built-in types map to Lean as:
    identifier  →  String
    int         →  Int
-/

/-- Storage-class specifier.  Chapter 10 introduces `static` and `extern`.
    `static` at file scope → internal linkage (not visible across TUs).
    `static` at block scope → static storage, no linkage.
    `extern` at file scope → external linkage, no definition in this TU (unless an initializer is given, which is an error).
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
    `FunCall` is new in Chapter 9: a function call `foo(a, b, c)`. -/
inductive Exp where
  | Constant    : Int → Exp
  | Var         : String → Exp              -- variable reference
  | Unary       : UnaryOp → Exp → Exp
  | Binary      : BinaryOp → Exp → Exp → Exp
  | Assignment  : Exp → Exp → Exp           -- lvalue = rhs
  | Conditional : Exp → Exp → Exp → Exp    -- cond ? e1 : e2
  | PostfixIncr : Exp → Exp                 -- extra credit: e++
  | PostfixDecr : Exp → Exp                 -- extra credit: e--
  | FunCall     : String → List Exp → Exp   -- Chapter 9: foo(a, b, c)
  deriving Repr, BEq

/-- A variable declaration with an optional initializer expression.
    Chapter 10 adds an optional storage-class specifier (`static` or `extern`).
    `storageClass = none` means the default storage class for the context
    (automatic for local variables, external linkage for file-scope). -/
structure Declaration where
  name         : String
  init         : Option Exp
  storageClass : Option StorageClass := none   -- Chapter 10
  deriving Repr, BEq

/-- The initial clause of a `for` loop.
    `InitExp none` represents an absent clause (`for (; ...)`)..
    `InitExp (some e)` represents an expression clause (`for (e; ...)`).
    `InitDecl d` represents a variable declaration (`for (int x = 0; ...)`),
    which introduces `x` into the loop's scope (visible in condition, post,
    and body, but not outside the loop). -/
inductive ForInit where
  | InitExp  : Option Exp → ForInit
  | InitDecl : Declaration → ForInit
  deriving Repr

/-
  `Statement` and `BlockItem` are mutually recursive: `Compound` holds a
  `List BlockItem`, while each `BlockItem` may contain a `Statement`.
  Lean 4 requires a `mutual` block for mutually recursive inductives; the
  `deriving` instances are applied after the block using `deriving instance`.
-/
mutual

/-- A statement in the C subset.
    The `Option String` fields on loop/break/continue/switch/case/default nodes
    carry an ID label injected by the loop-labeling semantic-analysis pass.
    After parsing all such fields are `none`; after loop labeling they hold a
    unique string like `"loop.5"` or `"case.3"`.  TACKY generation uses these
    IDs to derive the concrete break/continue/jump labels it emits. -/
inductive Statement where
  | Return     : Exp → Statement
  | Expression : Exp → Statement    -- expression statement: "e ;"
  | If         : Exp → Statement → Option Statement → Statement
  | Compound   : List BlockItem → Statement  -- Chapter 7: "{ ... }"
  -- Chapter 8: loops
  | While    : Exp → Statement → Option String → Statement
    -- while (cond) body; loop label
  | DoWhile  : Statement → Exp → Option String → Statement
    -- do body while (cond); loop label
  | For      : ForInit → Option Exp → Option Exp → Statement → Option String → Statement
    -- for (init; cond; post) body; loop label
  | Break    : Option String → Statement    -- break; loop/switch label
  | Continue : Option String → Statement    -- continue; loop label
  -- Chapter 8 extra credit: switch statements
  | Switch   : Exp → Statement → Option String → List (Option Int × String) → Statement
    -- switch (exp) body; switch label; collected case entries (val×caseLbl)
  | Case     : Int → Statement → Option String → Statement
    -- case n: body; case jump label
  | Default  : Statement → Option String → Statement
    -- default: body; default jump label
  -- Chapter 6 extra credit: labeled statements and goto
  | Labeled  : String → Statement → Statement  -- "label: stmt"
  | Goto     : String → Statement              -- "goto label;"
  | Null     : Statement                       -- null statement: ";"

/-- A block item is a statement, a variable declaration, or (Chapter 9) a
    local function declaration (no body allowed inside a function). -/
inductive BlockItem where
  | S  : Statement    → BlockItem  -- statement
  | D  : Declaration  → BlockItem  -- variable declaration
  | FD : FunctionDecl → BlockItem  -- local function declaration (Chapter 9)

/-- A local function declaration — name and parameters only, no body.
    Used as block items inside function bodies (Chapter 9).
    Chapter 10 adds an optional storage-class specifier.
    A `static` storage class on a block-scope function declaration is a
    semantic error (detected by VarResolution); the parser accepts it so
    that a clear error message can be reported. -/
structure FunctionDecl where
  name         : String        -- function name
  params       : List String   -- parameter names (for arity checking)
  storageClass : Option StorageClass := none   -- Chapter 10

end

deriving instance Repr for Statement
deriving instance Repr for BlockItem
deriving instance Repr for FunctionDecl

/-- A complete function definition: name, parameter list, and body.
    Chapter 9 adds `params`; Chapter 10 adds `storageClass`.
    `static` → internal linkage (symbol not visible outside this TU).
    no specifier or `extern` → external linkage. -/
structure FunctionDef where
  name         : String        -- function name
  params       : List String   -- parameter names (renamed by VarResolution)
  body         : List BlockItem
  storageClass : Option StorageClass := none   -- Chapter 10
  deriving Repr

/-- Top-level item in a translation unit.
    Chapter 9: multiple function definitions and declarations.
    Chapter 10: file-scope variable declarations (`VarDecl`). -/
inductive TopLevel where
  | FunDef  : FunctionDef  → TopLevel   -- function definition (has a body)
  | FunDecl : FunctionDecl → TopLevel   -- function declaration (prototype only)
  | VarDecl : Declaration  → TopLevel   -- Chapter 10: file-scope variable declaration
  deriving Repr

/-- A complete C program: a list of top-level declarations and definitions.
    Chapter 9 replaces the single `FunctionDef` with a list of `TopLevel` items. -/
structure Program where
  topLevels : List TopLevel
  deriving Repr

end AST
