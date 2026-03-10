import Lexer.Token

namespace Lexer

-- ---------------------------------------------------------------------------
-- Character predicates (ASCII only, per spec)
-- ---------------------------------------------------------------------------

/-- True if `c` is an ASCII letter (a–z or A–Z). -/
private def isAlpha (c : Char) : Bool :=
  (c.val >= 'a'.val && c.val <= 'z'.val) || (c.val >= 'A'.val && c.val <= 'Z'.val)

/-- True if `c` is an ASCII decimal digit (0–9). -/
private def isDigit (c : Char) : Bool :=
  c.val >= '0'.val && c.val <= '9'.val

/-- True if `c` is a word character: letter, digit, or underscore.
    Equivalent to the regex `\w`. Used to detect the end of identifiers
    and integer literals. -/
private def isWordChar (c : Char) : Bool :=
  isAlpha c || isDigit c || c == '_'

/-- True if `c` can legally start an identifier: letter or underscore.
    Digits are excluded so that e.g. `3foo` is not mistaken for an identifier. -/
private def isIdentStart (c : Char) : Bool :=
  isAlpha c || c == '_'

/-- True if `c` is ASCII whitespace (space, tab, newline, or carriage return). -/
private def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

-- ---------------------------------------------------------------------------
-- List-of-char helpers
-- ---------------------------------------------------------------------------

/-- Collect the longest prefix of `chars` satisfying `p`, plus the remainder.
    Returns `(matched, rest)`.  Tail-recursive via an accumulator that is
    reversed at the end. -/
private def spanChars (p : Char → Bool) (chars : List Char) : List Char × List Char :=
  let rec go (acc : List Char) : List Char → List Char × List Char
    | []      => (acc.reverse, [])
    | c :: cs => if p c then go (c :: acc) cs else (acc.reverse, c :: cs)
  go [] chars

/-- True when the next character is not a word character, or we are at end of
    input.  Used to enforce the word-boundary rule: `int` is a keyword but
    `integer` is an identifier, because in the latter case the `t` is followed
    by `e`, not a boundary. -/
private def atWordBoundary (rest : List Char) : Bool :=
  match rest with
  | []     => true
  | c :: _ => !isWordChar c

-- ---------------------------------------------------------------------------
-- Keyword detection
-- ---------------------------------------------------------------------------

/-- Given a fully-consumed word string, return the corresponding keyword token
    if the word is a reserved word, or an `Identifier` token otherwise.
    This is called after the whole word has been scanned, so keyword detection
    is a simple string comparison rather than a lookahead. -/
private def classifyWord (word : String) : Token :=
  match word with
  | "int"    => .KwInt
  | "void"   => .KwVoid
  | "return" => .KwReturn
  | "if"       => .KwIf
  | "else"     => .KwElse
  | "goto"     => .KwGoto
  | "while"    => .KwWhile
  | "do"       => .KwDo
  | "for"      => .KwFor
  | "break"    => .KwBreak
  | "continue" => .KwContinue
  | "switch"   => .KwSwitch
  | "case"     => .KwCase
  | "default"  => .KwDefault
  | "static"   => .KwStatic   -- Chapter 10: storage-class specifier
  | "extern"   => .KwExtern   -- Chapter 10: storage-class specifier
  | _          => .Identifier word

-- ---------------------------------------------------------------------------
-- Single-token matcher
-- ---------------------------------------------------------------------------

/-- Try to consume one token from the front of `chars`.
    Returns `some (token, remaining)` on success, or `none` if the first
    character does not start any valid token (triggering a lex error in the
    caller).

    Strategy:
    - Single-character punctuation is matched directly.
    - `-` uses a one-character lookahead to distinguish `-` from `--`.
    - Identifiers/keywords: scan the longest `\w+` run, require a word
      boundary after it, then classify the resulting string.
    - Integer constants: scan the longest digit run, require a word boundary
      after it, then parse the digit string as a `Nat`. -/
private def nextToken (chars : List Char) : Option (Token × List Char) :=
  match chars with
  | []                  => none
  -- Single-character punctuation (no word boundary required)
  | '(' :: rest         => some (.OpenParen,  rest)
  | ')' :: rest         => some (.CloseParen, rest)
  | '{' :: rest         => some (.OpenBrace,  rest)
  | '}' :: rest         => some (.CloseBrace, rest)
  | ';' :: rest         => some (.Semicolon,  rest)
  | '~' :: rest         => some (.Tilde,      rest)
  | '?' :: rest         => some (.Question,   rest)
  | ':' :: rest         => some (.Colon,      rest)
  | ',' :: rest         => some (.Comma,      rest)
  -- Longest match: multi-char operators before their single-char prefixes.
  -- + family: ++ and += before +
  | '+' :: '+' :: rest  => some (.PlusPlus,         rest)
  | '+' :: '=' :: rest  => some (.PlusEqual,        rest)
  | '+' :: rest         => some (.Plus,             rest)
  -- * family: *= before *
  | '*' :: '=' :: rest  => some (.StarEqual,        rest)
  | '*' :: rest         => some (.Star,             rest)
  -- / family: /= before /
  | '/' :: '=' :: rest  => some (.SlashEqual,       rest)
  | '/' :: rest         => some (.Slash,            rest)
  -- % family: %= before %
  | '%' :: '=' :: rest  => some (.PercentEqual,     rest)
  | '%' :: rest         => some (.Percent,          rest)
  -- ^ family: ^= before ^
  | '^' :: '=' :: rest  => some (.CaretEqual,       rest)
  | '^' :: rest         => some (.Caret,            rest)
  -- & family: && before &= before &
  | '&' :: '&' :: rest  => some (.AmpAmp,           rest)
  | '&' :: '=' :: rest  => some (.AmpEqual,         rest)
  | '&' :: rest         => some (.Ampersand,        rest)
  -- | family: || before |= before |
  | '|' :: '|' :: rest  => some (.PipePipe,         rest)
  | '|' :: '=' :: rest  => some (.PipeEqual,        rest)
  | '|' :: rest         => some (.Pipe,             rest)
  -- ! family: != before !
  | '!' :: '=' :: rest  => some (.BangEqual,        rest)
  | '!' :: rest         => some (.Bang,             rest)
  -- = family: == before =
  | '=' :: '=' :: rest  => some (.EqualEqual,       rest)
  | '=' :: rest         => some (.Equal,            rest)
  -- < family: <<= before << before <= before <
  | '<' :: '<' :: '=' :: rest => some (.LessLessEqual,      rest)
  | '<' :: '<' :: rest  => some (.LessLess,         rest)
  | '<' :: '=' :: rest  => some (.LessEqual,        rest)
  | '<' :: rest         => some (.Less,             rest)
  -- > family: >>= before >> before >= before >
  | '>' :: '>' :: '=' :: rest => some (.GreaterGreaterEqual, rest)
  | '>' :: '>' :: rest  => some (.GreaterGreater,   rest)
  | '>' :: '=' :: rest  => some (.GreaterEqual,     rest)
  | '>' :: rest         => some (.Greater,          rest)
  -- - family: -- before -= before -
  | '-' :: '-' :: rest  => some (.MinusMinus,       rest)
  | '-' :: '=' :: rest  => some (.MinusEqual,       rest)
  | '-' :: rest         => some (.Minus,            rest)
  -- Identifier/keyword and integer constant require predicate checks,
  -- so a catch-all arm with if/else handles them.
  | c :: _ =>
      if isIdentStart c then
        -- Identifier or keyword: [a-zA-Z_]\w*\b
        -- Keywords are recognised after the whole word is consumed (see spec).
        let (wordChars, remaining) := spanChars isWordChar chars
        if atWordBoundary remaining then
          some (classifyWord (String.ofList wordChars), remaining)
        else
          none
      else if isDigit c then
        -- Integer constant: [0-9]+\b
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

/-- Inner tokenizer loop.  Processes `chars` left to right, accumulating tokens
    in reverse order in `acc` for efficiency, then reverses at the end.
    Whitespace characters are silently skipped.  Any character that does not
    start a valid token causes an immediate error.
    Uses `partial` because Lean's termination checker cannot see that each
    recursive call receives a strictly shorter list (the proof would require
    showing that `nextToken` always consumes at least one character). -/
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
    Converts the string to a character list and delegates to `tokenizeAux`.
    Returns the complete token list on success, or an error message identifying
    the first unrecognised character. -/
def tokenize (input : String) : Except String (List Token) :=
  tokenizeAux input.toList []

end Lexer
