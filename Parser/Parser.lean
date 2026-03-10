import Lexer.Token
import AST.AST

namespace Parser

open Lexer AST

-- ---------------------------------------------------------------------------
-- Token stream helpers
-- ---------------------------------------------------------------------------

/-- Remove and return the first token from the stream.
    Fails with an error if the token list is empty, since the parser should
    never call this when no input remains. -/
private def takeToken (tokens : List Token) : Except String (Token × List Token) :=
  match tokens with
  | []         => .error "Unexpected end of input"
  | t :: rest  => .ok (t, rest)

/-- Consume the next token and verify it matches `expected`.
    Uses `takeToken` to read the next token, then compares it to `expected`.
    On a mismatch, produces a human-readable error using `Token.describe` so
    the message names the token the parser needed and the one it actually saw. -/
private def expect (expected : Token) (tokens : List Token) : Except String (List Token) := do
  let (actual, rest) ← takeToken tokens
  if actual == expected then
    .ok rest
  else
    .error s!"Expected {expected.describe} but found {actual.describe}"

-- ---------------------------------------------------------------------------
-- Binary-operator helpers
-- ---------------------------------------------------------------------------

/-- Return the precedence level of a binary-operator token, or `none` if the
    token is not a binary operator.  Higher numbers bind more tightly.
    Used by the precedence-climbing loop to decide when to consume an operator.

    Precedence table (high to low):
      `*`  `/`  `%`  →  50   (multiplicative)
      `+`  `-`  →  45         (additive)
      `<<` `>>` →  40         (shift)
      `<`  `<=` `>` `>=` → 35 (relational)
      `==` `!=`    →  30      (equality)
      `&`          →  25      (bitwise AND; sits between equality and &&)
      `^`          →  20      (bitwise XOR)
      `|`          →  15      (bitwise OR)
      `&&`         →  10      (logical AND)
      `||`         →   5      (logical OR)

    Assignment operators (=, +=, etc.) are right-associative at precedence 1
    and are handled separately in `parseExpClimb`. -/
private def binopPrecedence : Token → Option Nat
  | .Star           => some 50
  | .Slash          => some 50
  | .Percent        => some 50
  | .Plus           => some 45
  | .Minus          => some 45
  | .LessLess       => some 40
  | .GreaterGreater => some 40
  | .Less           => some 35
  | .LessEqual      => some 35
  | .Greater        => some 35
  | .GreaterEqual   => some 35
  | .EqualEqual     => some 30
  | .BangEqual      => some 30
  | .Ampersand      => some 25
  | .Caret          => some 20
  | .Pipe           => some 15
  | .AmpAmp         => some 10
  | .PipePipe       => some 5
  | _               => none

/-- Convert a binary-operator token to the corresponding `BinaryOp` AST node,
    or `none` if the token is not a binary operator.
    Always agrees with `binopPrecedence`: a token returns `some` from both
    functions or from neither. -/
private def tokenToBinop : Token → Option BinaryOp
  | .Plus           => some .Add
  | .Minus          => some .Subtract
  | .Star           => some .Multiply
  | .Slash          => some .Divide
  | .Percent        => some .Remainder
  | .Ampersand      => some .BitAnd
  | .Pipe           => some .BitOr
  | .Caret          => some .BitXor
  | .LessLess       => some .ShiftLeft
  | .GreaterGreater => some .ShiftRight
  | .AmpAmp         => some .And
  | .PipePipe       => some .Or
  | .EqualEqual     => some .Equal
  | .BangEqual      => some .NotEqual
  | .Less           => some .LessThan
  | .LessEqual      => some .LessOrEqual
  | .Greater        => some .GreaterThan
  | .GreaterEqual   => some .GreaterOrEqual
  | _               => none

/-- Map an assignment-operator token to an optional compound binary op.
    Returns `some none` for plain `=` (no operation, just assign).
    Returns `some (some op)` for compound operators like `+=` (desugar to
    `Assignment(left, Binary(op, left, right))`).
    Returns `none` for any token that is not an assignment operator. -/
private def assignmentOp : Token → Option (Option BinaryOp)
  | .Equal               => some none
  | .PlusEqual           => some (some .Add)
  | .MinusEqual          => some (some .Subtract)
  | .StarEqual           => some (some .Multiply)
  | .SlashEqual          => some (some .Divide)
  | .PercentEqual        => some (some .Remainder)
  | .AmpEqual            => some (some .BitAnd)
  | .PipeEqual           => some (some .BitOr)
  | .CaretEqual          => some (some .BitXor)
  | .LessLessEqual       => some (some .ShiftLeft)
  | .GreaterGreaterEqual => some (some .ShiftRight)
  | _                    => none

-- ---------------------------------------------------------------------------
-- Parsing functions (one per non-terminal in the formal grammar)
-- ---------------------------------------------------------------------------

/-
  The three expression-parsing functions below are mutually recursive:
    - `parseFactor` may call `parseExp` for parenthesised sub-expressions.
    - `parseExp` calls `parseFactor` then `parseExpClimb`.
    - `parseExpClimb` calls `parseExp` when it finds an operator.
  All three are declared `partial` because the termination argument
  (each call receives a strictly shorter token list) is not visible to
  Lean's structural checker across function boundaries.
-/
mutual

/-- Parse a *factor*: the grammar's highest-priority expression form.
    A factor is one of:
      - An integer constant token                    → `Exp.Constant`
      - An identifier followed by `(`               → `Exp.FunCall` (function call)
      - An identifier not followed by `(`           → `Exp.Var` (or postfix ++ or --)
      - A prefix unary operator followed by a factor → `Exp.Unary` or desugared assignment
      - A parenthesised full expression             → the inner `Exp` node (no wrapper)

    Chapter 9: when we see `Identifier "("`, we parse it as a function call.
    The argument list is `(void)` (empty) or `(e1, e2, ...)`.
    Trailing commas in the argument list are a parse error.

    Prefix `++e` desugars to `Assignment(e, Binary(Add, e, 1))`.
    Prefix `--e` desugars to `Assignment(e, Binary(Subtract, e, 1))`.
    Postfix `e++` becomes `PostfixIncr(Var(e))`.
    Postfix `e--` becomes `PostfixDecr(Var(e))`.
    Lvalue validity (that the operand is a `Var`) is checked later during
    variable resolution, not here. -/
private partial def parseFactor (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | []                  => .error "Expected expression but reached end of input"
  | .Constant n :: rest => .ok (.Constant n, rest)
  | .Minus :: rest      => do let (e, rest') ← parseFactor rest; .ok (.Unary .Negate e, rest')
  | .Tilde :: rest      => do let (e, rest') ← parseFactor rest; .ok (.Unary .Complement e, rest')
  | .Bang  :: rest      => do let (e, rest') ← parseFactor rest; .ok (.Unary .Not e, rest')
  -- Prefix ++ and -- desugar to Assignment(e, Binary(Add/Sub, e, 1))
  | .PlusPlus :: rest   => do
      let (e, rest') ← parseFactor rest
      .ok (.Assignment e (.Binary .Add e (.Constant 1)), rest')
  | .MinusMinus :: rest => do
      let (e, rest') ← parseFactor rest
      .ok (.Assignment e (.Binary .Subtract e (.Constant 1)), rest')
  -- Identifier: check for function call (followed by '('), postfix ++/--, or plain variable
  | .Identifier v :: .OpenParen :: rest => do
      -- Function call: parse the argument list
      let (args, rest') ← parseArgList rest
      -- Check for postfix ++ or -- after a function call (unusual but valid C)
      match rest' with
      | .PlusPlus   :: rest'' => .ok (.PostfixIncr (.FunCall v args), rest'')
      | .MinusMinus :: rest'' => .ok (.PostfixDecr (.FunCall v args), rest'')
      | _                     => .ok (.FunCall v args, rest')
  | .Identifier v :: rest =>
      match rest with
      | .PlusPlus   :: rest' => .ok (.PostfixIncr (.Var v), rest')
      | .MinusMinus :: rest' => .ok (.PostfixDecr (.Var v), rest')
      | _                    => .ok (.Var v, rest)
  | .OpenParen :: rest  => do
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .CloseParen rest'
      -- Check for postfix ++ or -- after a parenthesised expression.
      match rest'' with
      | .PlusPlus   :: rest''' => .ok (.PostfixIncr e, rest''')
      | .MinusMinus :: rest''' => .ok (.PostfixDecr e, rest''')
      | _                      => .ok (e, rest'')
  | t :: _              => .error s!"Expected expression but found {t.describe}"

/-- Parse the argument list of a function call.
    Precondition: the opening `(` has already been consumed.
    Grammar: `)` (empty) | `exp { "," exp } ")"`.
    No trailing comma is allowed.
    Returns the list of argument expressions and the remaining tokens
    (after consuming the closing `)`). -/
private partial def parseArgList (tokens : List Token) : Except String (List Exp × List Token) :=
  match tokens with
  | .CloseParen :: rest =>
      -- Empty argument list: ()
      .ok ([], rest)
  | _ => do
      -- Parse first argument
      let (firstArg, rest) ← parseExp 0 tokens
      -- Parse additional arguments separated by commas
      let (moreArgs, rest') ← parseArgListTail rest
      .ok (firstArg :: moreArgs, rest')

/-- Parse zero or more additional arguments after the first, each preceded by a comma.
    Stops when `)` is found and consumes it. No trailing comma is allowed. -/
private partial def parseArgListTail (tokens : List Token) : Except String (List Exp × List Token) :=
  match tokens with
  | .CloseParen :: rest => .ok ([], rest)
  | .Comma :: rest => do
      let (arg, rest') ← parseExp 0 rest
      let (moreArgs, rest'') ← parseArgListTail rest'
      .ok (arg :: moreArgs, rest'')
  | [] => .error "Expected \")\" or \",\" in argument list but reached end of input"
  | t :: _ => .error s!"Expected \")\" or \",\" in argument list but found {t.describe}"

/-- Parse an expression using *precedence climbing*.
    `minPrec` is the minimum operator precedence level that this call is
    allowed to consume.  Callers pass `0` to allow all operators; recursive
    calls from `parseExpClimb` pass `prec + 1` for left-associative operators
    or `prec` for right-associative operators (assignment). -/
private partial def parseExp (minPrec : Nat) (tokens : List Token) : Except String (Exp × List Token) := do
  let (left, tokens) ← parseFactor tokens
  parseExpClimb minPrec left tokens

/-- Tail of the precedence-climbing loop.
    For regular binary operators: consumes the operator, parses the right-hand
    side at `prec + 1` (left-associative), folds into a `Binary` node, loops.
    For assignment operators (=, +=, etc.) at precedence 1: parses the
    right-hand side at precedence 1 (right-associative), builds an
    `Assignment` node (or `Assignment(l, Binary(op, l, r))` for compound),
    then loops. -/
private partial def parseExpClimb (minPrec : Nat) (left : Exp) (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | tok :: rest =>
    -- Assignment operators are right-associative at precedence 1.
    match assignmentOp tok with
    | some compoundOp =>
      if 1 >= minPrec then do
        let (right, rest') ← parseExp 1 rest  -- right-assoc: same precedence
        let rhs := match compoundOp with
                   | none    => right
                   | some op => .Binary op left right
        parseExpClimb minPrec (.Assignment left rhs) rest'
      else
        .ok (left, tokens)
    | none =>
      -- Conditional (ternary) operator: prec 3, right-associative.
      -- Parsed as: left "?" middle ":" right, where middle allows any expression.
      match tok with
      | .Question =>
        if 3 >= minPrec then do
          let (middle, rest')  ← parseExp 0 rest
          let rest''           ← expect .Colon rest'
          let (right, rest''') ← parseExp 3 rest''
          parseExpClimb minPrec (.Conditional left middle right) rest'''
        else
          .ok (left, tokens)
      | _ =>
        match binopPrecedence tok, tokenToBinop tok with
        | some prec, some op =>
          if prec >= minPrec then do
            let (right, rest') ← parseExp (prec + 1) rest
            parseExpClimb minPrec (.Binary op left right) rest'
          else
            .ok (left, tokens)
        | _, _ => .ok (left, tokens)
  | [] => .ok (left, tokens)

end

-- ---------------------------------------------------------------------------
-- Statement, declaration, and block-item parsing
-- ---------------------------------------------------------------------------

/-- Try to parse an optional storage-class specifier token at the front of
    `tokens`.  Returns `(some sc, rest)` when a `static` or `extern` keyword
    is found, or `(none, tokens)` when neither is present.

    Chapter 10 supports both orderings of the type and storage class:
      `static int x;`   — storage class before type (canonical C order)
      `int static x;`   — type before storage class (also accepted)
    The caller handles the ordering: it tries this function both before and
    after consuming the `int` keyword. -/
private def parseStorageClass (tokens : List Token) : Option StorageClass × List Token :=
  match tokens with
  | .KwStatic :: rest => (some .Static, rest)
  | .KwExtern :: rest => (some .Extern, rest)
  | _                 => (none, tokens)

/-- Parse a variable declaration: `[static|extern] int <identifier> [ = <exp> ] ;`
    Also handles `int [static|extern] <identifier> ...` for the type-before-
    storage-class ordering.
    `storageClassOpt` is the storage class parsed BEFORE the `int` keyword,
    if any (the caller parses it first, then calls this function with the
    remaining tokens that should start with `int`). -/
private def parseVarDecl (tokens : List Token) (storageClassOpt : Option StorageClass := none)
    : Except String (Declaration × List Token) := do
  -- Consume the mandatory `int` keyword
  let tokens ← expect .KwInt tokens
  -- Check for a storage class AFTER the `int` keyword (e.g. `int static x;`)
  let (sc2, tokens) := parseStorageClass tokens
  -- The effective storage class: prefer the one before `int` if given, else after
  let sc := storageClassOpt.orElse (fun () => sc2)
  let (name, tokens) ←
    match tokens with
    | .Identifier n :: rest => .ok (n, rest)
    | []                    => .error "Expected variable name but reached end of input"
    | t :: _                => .error s!"Expected variable name but found {t.describe}"
  match tokens with
  | .Equal :: rest => do
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .Semicolon rest'
      .ok ({ name, init := some e, storageClass := sc }, rest'')
  | _ => do
      let rest ← expect .Semicolon tokens
      .ok ({ name, init := none, storageClass := sc }, rest)

/-- Parse the initial clause of a `for` loop.
    The clause ends with a semicolon (which is consumed).
    - `[static|extern] int <id> [= <exp>] ;` → `ForInit.InitDecl`
      (storage-class specifiers are parsed and stored; semantic analysis will
       later reject them if present — storage class is illegal in a for-init)
    - `;`                    → `ForInit.InitExp none` (absent expression)
    - `<exp> ;`              → `ForInit.InitExp (some exp)` (expression, then `;`) -/
private def parseForInit (tokens : List Token) : Except String (ForInit × List Token) :=
  match tokens with
  | .KwInt :: _ => do
      let (decl, rest) ← parseVarDecl tokens   -- parseVarDecl already consumes ';'
      .ok (.InitDecl decl, rest)
  | .KwStatic :: _ => do
      -- Storage class before `int`: `static int x = ...;`
      let (sc, tokens') := parseStorageClass tokens
      let (decl, rest) ← parseVarDecl tokens' sc
      .ok (.InitDecl decl, rest)
  | .KwExtern :: _ => do
      let (sc, tokens') := parseStorageClass tokens
      let (decl, rest) ← parseVarDecl tokens' sc
      .ok (.InitDecl decl, rest)
  | .Semicolon :: rest =>
      .ok (.InitExp none, rest)                     -- absent: just consume ';'
  | _ => do
      let (e, rest)  ← parseExp 0 tokens
      let rest'      ← expect .Semicolon rest
      .ok (.InitExp (some e), rest')

/-- Parse an optional expression followed by a delimiter token (consuming it).
    Returns `(none, rest)` when the delimiter appears immediately.
    Returns `(some e, rest)` when an expression precedes the delimiter. -/
private def parseOptionalExp (delim : Token) (tokens : List Token)
    : Except String (Option Exp × List Token) :=
  match tokens with
  | [] => .error s!"Expected expression or {delim.describe} but reached end of input"
  | tok :: rest =>
      if tok == delim then .ok (none, rest)
      else do
        let (e, rest')  ← parseExp 0 (tok :: rest)
        let rest''      ← expect delim rest'
        .ok (some e, rest'')

/-
  `parseStatement`, `parseBlockItem`, and `parseBlockItems` are mutually
  recursive through the `Compound` statement constructor added in Chapter 7:
    - `parseStatement` calls `parseBlockItems` to parse `{ ... }` bodies.
    - `parseBlockItems` calls `parseBlockItem`.
    - `parseBlockItem` calls `parseStatement` for non-declaration items.
  All three are declared `partial` so the termination argument need not be
  proved structurally.
-/
mutual

/-- Parse a single statement.
    Supported forms:
      - `;`                                       → `Statement.Null`
      - `return <exp> ;`                          → `Statement.Return`
      - `if "(" <exp> ")" <stmt> [else <stmt>]`   → `Statement.If`
      - `{ <block-item>* }`                       → `Statement.Compound`  (Chapter 7)
      - `while "(" <exp> ")" <stmt>`              → `Statement.While`     (Chapter 8)
      - `do <stmt> while "(" <exp> ")" ";"`       → `Statement.DoWhile`   (Chapter 8)
      - `for "(" <for-init> [<exp>] ";" [<exp>] ")" <stmt>` → `Statement.For` (Ch 8)
      - `break ;`                                 → `Statement.Break`     (Chapter 8)
      - `continue ;`                              → `Statement.Continue`  (Chapter 8)
      - `switch "(" <exp> ")" <stmt>`             → `Statement.Switch`    (Ch 8 EC)
      - `case <int> ":" <stmt>`                   → `Statement.Case`      (Ch 8 EC)
      - `default ":" <stmt>`                      → `Statement.Default`   (Ch 8 EC)
      - `goto <label> ;`                          → `Statement.Goto`      (Ch 6 EC)
      - `<identifier> : <stmt>`                   → `Statement.Labeled`   (Ch 6 EC)
      - `<exp> ;`                                 → `Statement.Expression`

    Dangling-else is resolved greedily: an `else` always belongs to the
    nearest enclosing `if`. -/
private partial def parseStatement (tokens : List Token) : Except String (Statement × List Token) :=
  match tokens with
  | .Semicolon :: rest =>
      .ok (.Null, rest)
  | .KwReturn :: rest => do
      let (exp, rest') ← parseExp 0 rest
      let rest''       ← expect .Semicolon rest'
      .ok (.Return exp, rest'')
  | .KwIf :: rest => do
      let rest'          ← expect .OpenParen rest
      let (cond, rest'') ← parseExp 0 rest'
      let rest'''        ← expect .CloseParen rest''
      let (thenStmt, rest4) ← parseStatement rest'''
      match rest4 with
      | .KwElse :: rest5 => do
          let (elseStmt, rest6) ← parseStatement rest5
          .ok (.If cond thenStmt (some elseStmt), rest6)
      | _ => .ok (.If cond thenStmt none, rest4)
  -- Chapter 7: compound statement "{ block-item* }"
  | .OpenBrace :: rest => do
      let (items, rest') ← parseBlockItems rest
      let rest''         ← expect .CloseBrace rest'
      .ok (.Compound items, rest'')
  -- Chapter 8: while loop
  | .KwWhile :: rest => do
      let rest'          ← expect .OpenParen rest
      let (cond, rest'') ← parseExp 0 rest'
      let rest'''        ← expect .CloseParen rest''
      let (body, rest4)  ← parseStatement rest'''
      .ok (.While cond body none, rest4)
  -- Chapter 8: do-while loop
  | .KwDo :: rest => do
      let (body, rest')  ← parseStatement rest
      let rest''         ← expect .KwWhile rest'
      let rest'''        ← expect .OpenParen rest''
      let (cond, rest4)  ← parseExp 0 rest'''
      let rest5          ← expect .CloseParen rest4
      let rest6          ← expect .Semicolon rest5
      .ok (.DoWhile body cond none, rest6)
  -- Chapter 8: for loop
  | .KwFor :: rest => do
      let rest'            ← expect .OpenParen rest
      let (init, rest'')   ← parseForInit rest'
      let (cond, rest''')  ← parseOptionalExp .Semicolon rest''
      let (post, rest4)    ← parseOptionalExp .CloseParen rest'''
      let (body, rest5)    ← parseStatement rest4
      .ok (.For init cond post body none, rest5)
  -- Chapter 8: break and continue
  | .KwBreak :: rest => do
      let rest' ← expect .Semicolon rest
      .ok (.Break none, rest')
  | .KwContinue :: rest => do
      let rest' ← expect .Semicolon rest
      .ok (.Continue none, rest')
  -- Chapter 8 extra credit: switch statement
  | .KwSwitch :: rest => do
      let rest'          ← expect .OpenParen rest
      let (exp, rest'')  ← parseExp 0 rest'
      let rest'''        ← expect .CloseParen rest''
      let (body, rest4)  ← parseStatement rest'''
      .ok (.Switch exp body none [], rest4)
  -- Chapter 8 extra credit: case label (positive and negative integer constants)
  | .KwCase :: .Minus :: .Constant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (-(n : Int)) stmt none, rest')
  | .KwCase :: .Constant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (n : Int) stmt none, rest')
  | .KwCase :: _ => .error "case expression must be an integer constant"
  -- Chapter 8 extra credit: default label
  | .KwDefault :: rest => do
      let rest'         ← expect .Colon rest
      let (stmt, rest'') ← parseStatement rest'
      .ok (.Default stmt none, rest'')
  -- Chapter 6 extra credit: goto statement
  | .KwGoto :: .Identifier label :: rest => do
      let rest' ← expect .Semicolon rest
      .ok (.Goto label, rest')
  -- Chapter 6 extra credit: labeled statement (lookahead: identifier then ':')
  | .Identifier label :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Labeled label stmt, rest')
  | _ => do
      let (exp, rest) ← parseExp 0 tokens
      let rest'       ← expect .Semicolon rest
      .ok (.Expression exp, rest')

/-- Parse a local function declaration (no body) after the `int name (` prefix
    has been determined.  `sc` is the optional storage-class specifier that was
    already parsed.  The opening `(` has NOT yet been consumed when this helper
    is called; `rest` starts after `name`. -/
private partial def parseLocalFunDecl (name : String) (sc : Option StorageClass)
    (rest : List Token) : Except String (BlockItem × List Token) := do
  let rest' ← expect .OpenParen rest
  let (params, rest'') ← parseParamList rest'
  match rest'' with
  | .Semicolon :: rest''' =>
      .ok (.FD { name, params, storageClass := sc }, rest''')
  | .OpenBrace :: _ =>
      .error s!"Function definition for '{name}' inside a function is not allowed"
  | [] => .error "Expected \";\" after local function declaration but reached end of input"
  | t :: _ => .error s!"Expected \";\" after local function declaration but found {t.describe}"

/-- Parse a block item: either a variable declaration, a local function declaration,
    or a statement.

    Chapter 9 disambiguation:
    - `int <identifier> "(" ...` → local function declaration (parsed without body)
    - `int <identifier> [= ...]  ;` → variable declaration
    - anything else → statement

    Chapter 10: storage-class specifiers may appear before or after `int`.
    - `static int foo(void);` → local function declaration (SC error in semantic analysis)
    - `extern int x;`        → local extern variable declaration
    - `int static x;`        → same (type-before-SC ordering)

    When we see `int <name> (`, we parse a local function declaration.
    Local function *definitions* (with `{` body) inside other functions are
    rejected as a parse error. -/
private partial def parseBlockItem (tokens : List Token) : Except String (BlockItem × List Token) :=
  match tokens with
  -- Storage class BEFORE `int` (e.g. `static int foo(...)` or `extern int x`)
  | .KwStatic :: rest | .KwExtern :: rest => do
      -- Figure out which storage class token we're looking at
      let (sc, afterSC) := parseStorageClass tokens
      -- After the storage class we must see `int`
      match afterSC with
      | .KwInt :: .Identifier name :: .OpenParen :: rest' => do
          -- Function-like: `static int name(...)` — parse as local function decl.
          -- Pass `OpenParen :: rest'` directly (name is already known, don't re-parse it).
          parseLocalFunDecl name sc (.OpenParen :: rest')
      | .KwInt :: .Identifier _ :: _ => do
          -- Variable: `static int x = ...;` or `extern int x;`
          let (decl, rest') ← parseVarDecl afterSC sc
          .ok (.D decl, rest')
      | _ => do
          -- Unexpected; try parsing as statement for a better error message
          let (stmt, rest') ← parseStatement tokens
          .ok (.S stmt, rest')
  -- `int static name(...)` or `int extern name(...)`: type before storage class, function
  | .KwInt :: .KwStatic :: .Identifier name :: .OpenParen :: rest =>
      parseLocalFunDecl name (some .Static) (.OpenParen :: rest)
  | .KwInt :: .KwExtern :: .Identifier name :: .OpenParen :: rest =>
      parseLocalFunDecl name (some .Extern) (.OpenParen :: rest)
  -- `int name(...)`: plain function declaration (no storage class)
  | .KwInt :: .Identifier name :: .OpenParen :: rest =>
      parseLocalFunDecl name none (.OpenParen :: rest)
  -- `int [static|extern] name [= e] ;`: variable declaration (any ordering)
  | .KwInt :: _ => do
      let (decl, rest) ← parseVarDecl tokens
      .ok (.D decl, rest)
  | _ => do
      let (stmt, rest) ← parseStatement tokens
      .ok (.S stmt, rest)

/-- Parse a sequence of block items until a `}` is seen (but do not consume it). -/
private partial def parseBlockItems (tokens : List Token) : Except String (List BlockItem × List Token) :=
  match tokens with
  | .CloseBrace :: _ => .ok ([], tokens)
  | [] => .error "Expected \"}\" but reached end of input"
  | _ => do
      let (item, rest)   ← parseBlockItem tokens
      let (items, rest') ← parseBlockItems rest
      .ok (item :: items, rest')

/-- Parse a parameter list for a function declaration or definition.
    Precondition: the opening `(` has already been consumed.
    Grammar: `"void" ")"` (no parameters) | `"int" id { "," "int" id } ")"`.
    Returns the list of parameter names and the remaining tokens (after `)`). -/
private partial def parseParamList (tokens : List Token) : Except String (List String × List Token) :=
  match tokens with
  | .KwVoid :: .CloseParen :: rest =>
      -- (void) means no parameters
      .ok ([], rest)
  | .CloseParen :: rest =>
      -- () also means no parameters (some compilers accept this)
      .ok ([], rest)
  | _ => do
      -- Parse first parameter: `int <name>`
      let (firstName, rest) ← parseOneParam tokens
      let (moreNames, rest') ← parseParamListTail rest
      .ok (firstName :: moreNames, rest')

/-- Parse zero or more additional parameters after the first, each `"," "int" id`.
    Stops when `)` is found and consumes it. No trailing comma allowed. -/
private partial def parseParamListTail (tokens : List Token) : Except String (List String × List Token) :=
  match tokens with
  | .CloseParen :: rest => .ok ([], rest)
  | .Comma :: rest => do
      let (name, rest') ← parseOneParam rest
      let (names, rest'') ← parseParamListTail rest'
      .ok (name :: names, rest'')
  | [] => .error "Expected \")\" or \",\" in parameter list but reached end of input"
  | t :: _ => .error s!"Expected \")\" or \",\" in parameter list but found {t.describe}"

/-- Parse a single parameter: `int <identifier>`.
    Returns the parameter name and remaining tokens. -/
private partial def parseOneParam (tokens : List Token) : Except String (String × List Token) := do
  let tokens' ← expect .KwInt tokens
  match tokens' with
  | .Identifier name :: rest => .ok (name, rest)
  | []                       => .error "Expected parameter name but reached end of input"
  | t :: _                   => .error s!"Expected parameter name but found {t.describe}"

end

-- ---------------------------------------------------------------------------
-- Top-level declaration/definition parsing
-- ---------------------------------------------------------------------------

/-- Parse a top-level declaration or definition (function or variable).
    Grammar (Chapter 10):
      `[static|extern] int <name> "(" param-list ")" ";"` → `TopLevel.FunDecl`
      `[static|extern] int <name> "(" param-list ")" "{" body "}"` → `TopLevel.FunDef`
      `[static|extern] int <name> ["=" exp] ";"` → `TopLevel.VarDecl`

    The storage class may appear before OR after the `int` keyword (both orders
    are accepted per the C grammar, since type and storage-class specifiers may
    be interleaved).  After consuming both, we decide whether this is a variable
    or function declaration by looking for `(` after the name.

    Chapter 10: file-scope variable declarations are represented as
    `TopLevel.VarDecl`.  They are never renamed (they keep their original names
    so they can be matched across translation units by the linker). -/
private partial def parseTopLevel (tokens : List Token) : Except String (TopLevel × List Token) := do
  -- Optional storage-class specifier BEFORE `int`
  let (sc1, tokens) := parseStorageClass tokens
  -- Mandatory `int` keyword
  let tokens ← expect .KwInt tokens
  -- Optional storage-class specifier AFTER `int` (e.g. `int static x;`)
  let (sc2, tokens) := parseStorageClass tokens
  -- Reject multiple storage-class specifiers (e.g. `static int extern foo`)
  if sc1.isSome && sc2.isSome then
    throw "Multiple storage class specifiers"
  -- Effective storage class: prefer before-int if given, else after-int
  let sc := sc1.orElse (fun () => sc2)
  -- Parse the name
  let (name, tokens) ←
    match tokens with
    | .Identifier name :: rest => .ok (name, rest)
    | []                       => .error "Expected identifier but reached end of input"
    | t :: _                   => .error s!"Expected identifier but found {t.describe}"
  -- Decide: variable or function by peeking at next token
  match tokens with
  | .OpenParen :: rest => do
      -- Function: `int name ( params ) ; | { body }`
      let (params, tokens) ← parseParamList rest
      match tokens with
      | .Semicolon :: rest' =>
          .ok (.FunDecl { name, params, storageClass := sc }, rest')
      | .OpenBrace :: rest' => do
          let (body, rest'') ← parseBlockItems rest'
          let rest'''        ← expect .CloseBrace rest''
          .ok (.FunDef { name, params, body, storageClass := sc }, rest''')
      | [] => .error s!"Expected open-brace or semicolon after function header for {name} but reached end of input"
      | t :: _ => .error s!"Expected open-brace or semicolon after function header for {name} but found {t.describe}"
  | .Equal :: rest => do
      -- Variable with initializer: `[sc] int name = exp ;`
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .Semicolon rest'
      .ok (.VarDecl { name, init := some e, storageClass := sc }, rest'')
  | .Semicolon :: rest =>
      -- Variable without initializer: `[sc] int name ;`
      .ok (.VarDecl { name, init := none, storageClass := sc }, rest)
  | [] => .error s!"Expected open-brace, semicolon, or open-paren after name {name} but reached end of input"
  | t :: _ => .error s!"Expected open-brace, semicolon, or open-paren after name {name} but found {t.describe}"

/-- Parse a sequence of top-level items until the token list is exhausted.
    Each item must begin with an optional storage class followed by `int`. -/
private partial def parseTopLevels (tokens : List Token) : Except String (List TopLevel) :=
  match tokens with
  | []   => .ok []
  | _    => do
      let (item, rest) ← parseTopLevel tokens
      let items        ← parseTopLevels rest
      .ok (item :: items)

/-- Parse a complete program: one or more top-level function declarations
    or definitions until EOF.
    Returns an error if tokens remain after the last top-level item. -/
def parseProgram (tokens : List Token) : Except String Program := do
  let topLevels ← parseTopLevels tokens
  .ok { topLevels }

end Parser
