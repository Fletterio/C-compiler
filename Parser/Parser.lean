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

    Precedence table (Table 4-1, updated to accommodate Chapter 3 bitwise ops):
      `*`  `/`  `%`  →  50   (multiplicative)
      `+`  `-`  →  45         (additive)
      `<<` `>>` →  40         (shift)
      `<`  `<=` `>` `>=` → 35 (relational)
      `==` `!=`    →  30      (equality)
      `&`          →  25      (bitwise AND; sits between equality and &&)
      `^`          →  20      (bitwise XOR)
      `|`          →  15      (bitwise OR)
      `&&`         →  10      (logical AND)
      `||`         →   5      (logical OR) -/
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

-- ---------------------------------------------------------------------------
-- Parsing functions (one per non-terminal in the formal grammar)
-- ---------------------------------------------------------------------------

/-
  The three parsing functions below are mutually recursive:
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
      - A unary operator followed by a factor → `Exp.Unary`
      - A parenthesised full expression       → the inner `Exp` node (no wrapper)

    Unary `-`, `~`, and `!` all recurse into another `parseFactor`, so they
    bind more tightly than any binary operator.
    The decrement operator `--` is not recognised here and falls through to the
    catch-all error arm. -/
private partial def parseFactor (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | []                  => .error "Expected expression but reached end of input"
  | .Constant n :: rest => .ok (.Constant n, rest)
  | .Minus :: rest      => do let (e, rest') ← parseFactor rest; .ok (.Unary .Negate e, rest')
  | .Tilde :: rest      => do let (e, rest') ← parseFactor rest; .ok (.Unary .Complement e, rest')
  | .Bang  :: rest      => do let (e, rest') ← parseFactor rest; .ok (.Unary .Not e, rest')
  | .OpenParen :: rest  => do
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .CloseParen rest'
      .ok (e, rest'')
  | t :: _              => .error s!"Expected expression but found {t.describe}"

/-- Parse an expression using *precedence climbing*.
    `minPrec` is the minimum operator precedence level that this call is
    allowed to consume.  Callers pass `0` to allow all operators; recursive
    calls from `parseExpClimb` pass `prec + 1` to enforce left-associativity.

    Algorithm:
      1. Parse a factor as the initial left-hand side.
      2. Hand off to `parseExpClimb` to repeatedly fold in any trailing
         binary operators whose precedence is at least `minPrec`. -/
private partial def parseExp (minPrec : Nat) (tokens : List Token) : Except String (Exp × List Token) := do
  let (left, tokens) ← parseFactor tokens
  parseExpClimb minPrec left tokens

/-- Tail of the precedence-climbing loop.
    Peeks at the next token: if it is a binary operator whose precedence is
    ≥ `minPrec`, the operator is consumed, the right-hand side is parsed at
    one level higher (making all operators left-associative), the two sides
    are folded into a `Binary` node, and the loop continues.  Otherwise the
    current `left` accumulator is returned unchanged.

    This function is the engine of precedence climbing: the `minPrec + 1`
    passed to the recursive `parseExp` call ensures that same-precedence
    operators associate to the left (e.g. `1 - 2 - 3` → `(1 - 2) - 3`). -/
private partial def parseExpClimb (minPrec : Nat) (left : Exp) (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | tok :: rest =>
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

/-- Parse a return statement: `return <exp> ;`
    Consumes the `return` keyword, delegates to `parseExp` for the value,
    then consumes the semicolon.  Returns the resulting `Statement.Return`
    node together with the remaining token stream. -/
private def parseStatement (tokens : List Token) : Except String (Statement × List Token) := do
  let tokens          ← expect .KwReturn tokens
  let (exp, tokens)   ← parseExp 0 tokens
  let tokens          ← expect .Semicolon tokens
  .ok (.Return exp, tokens)

/-- Parse a function definition: `int <name> ( void ) { <statement> }`
    Consumes the return-type keyword, identifier, parameter list, and braces
    one token at a time using `expect`.  The function name is extracted by
    matching directly on `Identifier`, which lets us both verify the token
    kind and bind its payload in one step. -/
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
  let (body, tokens) ← parseStatement tokens
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
