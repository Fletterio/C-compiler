import Lexer.Token
import AST.AST

namespace Parser

open Lexer AST

-- ---------------------------------------------------------------------------
-- Token stream helpers
-- ---------------------------------------------------------------------------

/-- Remove and return the first token, or fail at end of input. -/
private def takeToken (tokens : List Token) : Except String (Token × List Token) :=
  match tokens with
  | []         => .error "Unexpected end of input"
  | t :: rest  => .ok (t, rest)

/-- Consume a specific token, or emit an informative error. -/
private def expect (expected : Token) (tokens : List Token) : Except String (List Token) := do
  let (actual, rest) ← takeToken tokens
  if actual == expected then
    .ok rest
  else
    .error s!"Expected {expected.describe} but found {actual.describe}"

-- ---------------------------------------------------------------------------
-- Parsing functions (one per non-terminal in the formal grammar)
-- ---------------------------------------------------------------------------

-- <exp> ::= <int> | <unop> <exp> | "(" <exp> ")"
-- <unop> ::= "-" | "~"
private def parseExp (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | []                  => .error "Expected expression but reached end of input"
  | .Constant n :: rest => .ok (.Constant n, rest)
  | .Minus :: rest      => do let (e, rest') ← parseExp rest; .ok (.Unary .Negate e, rest')
  | .Tilde :: rest      => do let (e, rest') ← parseExp rest; .ok (.Unary .Complement e, rest')
  | .OpenParen :: rest  => do
      let (e, rest') ← parseExp rest
      let rest''     ← expect .CloseParen rest'
      .ok (e, rest'')
  | t :: _              => .error s!"Expected expression but found {t.describe}"

-- <statement> ::= "return" <exp> ";"
private def parseStatement (tokens : List Token) : Except String (Statement × List Token) := do
  let tokens          ← expect .KwReturn tokens
  let (exp, tokens)   ← parseExp tokens
  let tokens          ← expect .Semicolon tokens
  .ok (.Return exp, tokens)

-- <function> ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"
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

-- <program> ::= <function>
/-- Parse a full program from a token list.
    Fails if any tokens remain after the top-level function definition. -/
def parseProgram (tokens : List Token) : Except String Program := do
  let (func, remaining) ← parseFunctionDef tokens
  match remaining with
  | []    => .ok { func }
  | t :: _ => .error s!"Unexpected token after end of program: {t.describe}"

end Parser
