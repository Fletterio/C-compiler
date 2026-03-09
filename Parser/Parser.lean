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
      - An integer constant token             → `Exp.Constant`
      - An identifier                         → `Exp.Var` (or postfix ++ or --)
      - A prefix unary operator followed by a factor → `Exp.Unary` or desugared assignment
      - A parenthesised full expression       → the inner `Exp` node (no wrapper)

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
  -- Identifier: check for postfix ++ or --
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

/-- Parse a variable declaration: `int <identifier> [ = <exp> ] ;` -/
private def parseDeclaration (tokens : List Token) : Except String (Declaration × List Token) := do
  let tokens ← expect .KwInt tokens
  let (name, tokens) ←
    match tokens with
    | .Identifier n :: rest => .ok (n, rest)
    | []                    => .error "Expected variable name but reached end of input"
    | t :: _                => .error s!"Expected variable name but found {t.describe}"
  match tokens with
  | .Equal :: rest => do
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .Semicolon rest'
      .ok ({ name, init := some e }, rest'')
  | _ => do
      let rest ← expect .Semicolon tokens
      .ok ({ name, init := none }, rest)

/-- Parse the initial clause of a `for` loop.
    The clause ends with a semicolon (which is consumed).
    - `int <id> [= <exp>] ;` → `ForInit.InitDecl` (declaration, semicolon consumed by `parseDeclaration`)
    - `;`                    → `ForInit.InitExp none` (absent expression)
    - `<exp> ;`              → `ForInit.InitExp (some exp)` (expression, then `;`) -/
private def parseForInit (tokens : List Token) : Except String (ForInit × List Token) :=
  match tokens with
  | .KwInt :: _ => do
      let (decl, rest) ← parseDeclaration tokens   -- parseDeclaration already consumes ';'
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

/-- Parse a block item: either a declaration (starts with `int`) or a statement. -/
private partial def parseBlockItem (tokens : List Token) : Except String (BlockItem × List Token) :=
  match tokens with
  | .KwInt :: _ => do
      let (decl, rest) ← parseDeclaration tokens
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

end

-- ---------------------------------------------------------------------------
-- Function definition and program
-- ---------------------------------------------------------------------------

/-- Parse a function definition: `int <name> ( void ) { <block-item>* }` -/
private def parseFunctionDef (tokens : List Token) : Except String (FunctionDef × List Token) := do
  let tokens ← expect .KwInt tokens
  let (name, tokens) ←
    match tokens with
    | .Identifier name :: rest => .ok (name, rest)
    | []                       => .error "Expected function name but reached end of input"
    | t :: _                   => .error s!"Expected function name but found {t.describe}"
  let tokens ← expect .OpenParen  tokens
  let tokens ← expect .KwVoid     tokens
  let tokens ← expect .CloseParen tokens
  let tokens ← expect .OpenBrace  tokens
  let (body, tokens) ← parseBlockItems tokens
  let tokens ← expect .CloseBrace tokens
  .ok ({ name, body }, tokens)

/-- Parse a complete program: exactly one top-level function definition with
    no tokens left over afterwards.
    After `parseFunctionDef` succeeds, any remaining tokens indicate a syntax
    error — valid programs end after the closing brace of `main`. -/
def parseProgram (tokens : List Token) : Except String Program := do
  let (func, remaining) ← parseFunctionDef tokens
  match remaining with
  | []    => .ok { func }
  | t :: _ => .error s!"Unexpected token after end of program: {t.describe}"

end Parser
