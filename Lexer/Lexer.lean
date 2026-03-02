import Lexer.Token

namespace Lexer

-- ---------------------------------------------------------------------------
-- Character predicates (ASCII only, per spec)
-- ---------------------------------------------------------------------------

private def isAlpha (c : Char) : Bool :=
  (c.val >= 'a'.val && c.val <= 'z'.val) || (c.val >= 'A'.val && c.val <= 'Z'.val)

private def isDigit (c : Char) : Bool :=
  c.val >= '0'.val && c.val <= '9'.val

/-- \w — letters, digits, and underscore. -/
private def isWordChar (c : Char) : Bool :=
  isAlpha c || isDigit c || c == '_'

/-- Valid first character of an identifier: letter or underscore. -/
private def isIdentStart (c : Char) : Bool :=
  isAlpha c || c == '_'

private def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

-- ---------------------------------------------------------------------------
-- List-of-char helpers
-- ---------------------------------------------------------------------------

/-- Collect the longest prefix of `chars` satisfying `p`, plus the remainder.
    Tail-recursive. -/
private def spanChars (p : Char → Bool) (chars : List Char) : List Char × List Char :=
  let rec go (acc : List Char) : List Char → List Char × List Char
    | []      => (acc.reverse, [])
    | c :: cs => if p c then go (c :: acc) cs else (acc.reverse, c :: cs)
  go [] chars

/-- True when the next character is not in \w (or we are at end of input),
    i.e. we are at a word boundary \b. -/
private def atWordBoundary (rest : List Char) : Bool :=
  match rest with
  | []     => true
  | c :: _ => !isWordChar c

-- ---------------------------------------------------------------------------
-- Keyword detection
-- ---------------------------------------------------------------------------

private def classifyWord (word : String) : Token :=
  match word with
  | "int"    => .KwInt
  | "void"   => .KwVoid
  | "return" => .KwReturn
  | _        => .Identifier word

-- ---------------------------------------------------------------------------
-- Single-token matcher
-- ---------------------------------------------------------------------------

/-- Try to consume one token from the front of `chars`.
    Returns `some (token, remaining)` or `none` if nothing matches. -/
private def nextToken (chars : List Char) : Option (Token × List Char) :=
  match chars with
  | [] => none
  | c :: rest =>
    -- Single-character punctuation (no word boundary required)
    if      c == '(' then some (.OpenParen,  rest)
    else if c == ')' then some (.CloseParen, rest)
    else if c == '{' then some (.OpenBrace,  rest)
    else if c == '}' then some (.CloseBrace, rest)
    else if c == ';' then some (.Semicolon,  rest)
    -- Identifier or keyword: [a-zA-Z_]\w*\b
    -- Keywords are recognised after the whole word is consumed (see spec).
    else if isIdentStart c then
      let (wordChars, remaining) := spanChars isWordChar chars
      if atWordBoundary remaining then
        some (classifyWord (String.ofList wordChars), remaining)
      else
        none
    -- Integer constant: [0-9]+\b
    else if isDigit c then
      let (digitChars, remaining) := spanChars isDigit chars
      if atWordBoundary remaining then
        match (String.ofList digitChars).toNat? with
        | some n => some (.Constant n, remaining)
        | none   => none   -- unreachable: digit string always parses as Nat
      else
        none   -- e.g. "123bar" — not a valid token
    else
      none

-- ---------------------------------------------------------------------------
-- Tokenizer loop
-- ---------------------------------------------------------------------------

/-- Recursive tokenizer. Uses `partial` because Lean's termination checker
    cannot see that each call strictly shrinks the input. -/
private partial def tokenizeAux : List Char → List Token → Except String (List Token)
  | [], acc => .ok acc.reverse
  | c :: rest, acc =>
    if isWhitespace c then
      tokenizeAux rest acc          -- skip whitespace, recurse
    else
      match nextToken (c :: rest) with
      | none            => .error s!"Unexpected character: '{c}'"
      | some (tok, rem) => tokenizeAux rem (tok :: acc)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

/-- Tokenize a preprocessed C source string.
    Returns a list of tokens, or an error message describing the first
    unrecognised character. -/
def tokenize (input : String) : Except String (List Token) :=
  tokenizeAux input.toList []

end Lexer
