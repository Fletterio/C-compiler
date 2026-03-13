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
  | "long"     => .KwLong     -- Chapter 11: long type keyword
  | "unsigned" => .KwUnsigned -- Chapter 12: unsigned type keyword
  | "signed"   => .KwSigned   -- Chapter 12: signed type keyword
  | "double"   => .KwDouble   -- Chapter 13: double type keyword
  | _          => .Identifier word

-- ---------------------------------------------------------------------------
-- Floating-point literal helper (Chapter 13)
-- ---------------------------------------------------------------------------

/-- Correctly-rounded conversion of the exact positive rational `numer / denom`
    to the nearest IEEE 754 double (round-to-nearest-even).

    Uses pure Nat arithmetic (arbitrary precision) to avoid the double-rounding
    bug in `Float.ofScientific` for large mantissas: that function converts
    `m` to a Float first, losing precision, then divides by 10^e, causing a
    second rounding that can land on the wrong side of the midpoint.

    Algorithm:
      1. Scale the numerator by 2^K (K = 1200, large enough for subnormals).
      2. Divide exactly: q = ⌊numer · 2^K / denom⌋, r = remainder.
      3. Determine the binary exponent b = ⌊log₂(q)⌋ − K.
      4. Extract the top `keepBits` bits of q as the raw significand (53 for
         normal numbers, fewer for subnormals), using the remainder for
         round-to-nearest-even tie-breaking.
      5. Handle carry (significand overflow after rounding).
      6. Construct the Float from finalSig and finalBExp using the identity
             value = (finalSig / 2^52) × 2^finalBExp
         Both operations are exact (no further rounding). -/
private def correctlyRoundedDecimalToFloat (numer denom : Nat) : Float :=
  if numer == 0 then 0.0
  else
    -- K = 1200 ensures we have enough precision bits even for subnormals
    -- (which need up to ~1074 + 53 ≈ 1127 bits of scale).
    let K : Nat := 1200
    let q := (numer * (1 <<< K)) / denom
    let r := (numer * (1 <<< K)) % denom
    if q == 0 then 0.0   -- numer/denom < 2^(-K); underflows to 0
    else
      let qLog := q.log2                       -- ⌊log₂ q⌋
      let bExp : Int := (qLog : Int) - K       -- ⌊log₂(numer/denom)⌋
      if bExp > 1023 then                      -- overflow → +∞
        (1.0 : Float) / 0.0
      else if bExp < -1074 then 0.0            -- below smallest subnormal → 0
      else
        -- Significand width:
        --   Normal   (bExp ≥ -1022): 53 bits (implicit leading 1 included)
        --   Subnormal (bExp < -1022): (bExp + 1075) bits, in [1, 52]
        let keepBitsI : Int := if bExp >= -1022 then 53 else bExp + 1075
        let keepBits := keepBitsI.toNat
        -- Right-shift amount to isolate the top `keepBits` bits of q:
        --   q has (qLog + 1) bits total; drop the bottom (qLog + 1 - keepBits).
        let shiftI : Int := (qLog : Int) + 1 - keepBitsI
        let (sig, fracNum, fracDen) :=
          if shiftI > 0 then
            let s   := shiftI.toNat
            let sig0 := q >>> s
            let qRem := q &&& ((1 <<< s) - 1)
            -- Fractional part = (qRem · denom + r) / (denom · 2^s)
            (sig0, qRem * denom + r, denom * (1 <<< s))
          else if shiftI == 0 then
            (q, r, denom)
          else
            -- shiftI < 0: q has fewer bits than keepBits; left-shift (exact)
            let s := (-shiftI).toNat
            (q <<< s, 0, 1)
        -- Round-to-nearest-even using the fractional remainder:
        let sig' :=
          if fracNum * 2 > fracDen then sig + 1      -- strictly above midpoint
          else if fracNum * 2 < fracDen then sig      -- strictly below midpoint
          else if sig % 2 == 1 then sig + 1           -- tie: round to even
          else sig
        -- Handle significand carry (sig' = 2^keepBits):
        --   Normal carry:    keepBits = 53, sig' = 2^53 → halve and bump exponent.
        --   Subnormal carry: keepBits ≤ 52, sig' = 2^keepBits ≤ 2^52.
        --     Setting finalBExp = -1022 in all subnormal cases works because
        --     value = (finalSig / 2^52) × 2^(-1022) = finalSig × 2^(-1074),
        --     which is the correct subnormal formula even when sig' = 2^52
        --     (the smallest normal: 2^52 / 2^52 × 2^(-1022) = 2^(-1022)).
        let maxSig := 1 <<< keepBits
        let (finalSig, finalBExp) : Nat × Int :=
          if sig' < maxSig then
            if bExp >= -1022 then (sig', bExp)   -- normal, no carry
            else (sig', -1022)                    -- subnormal, no carry
          else
            -- Carry (sig' = maxSig = 2^keepBits)
            if keepBits == 53 then
              (sig' >>> 1, bExp + 1)              -- normal carry: 2^53 → 2^52, exp+1
            else
              -- Subnormal carry: sig' = 2^keepBits ≤ 2^52.
              -- finalBExp = -1022 covers both still-subnormal and the
              -- boundary case (sig' = 2^52 ↔ smallest normal = 2^(-1022)).
              (sig', -1022)
        -- Post-carry overflow check (normal carry can push bExp to 1024):
        if finalBExp > 1023 then (1.0 : Float) / 0.0
        else
          -- Construct the double via two exact operations:
          --   sigF = finalSig / 2^52  ∈ [0, 2)  (exact: ≤ 53 integer bits)
          --   powF = 2^finalBExp              (exact: power of 2)
          --   result = sigF × powF            (exact: just shifts the exponent)
          let sigF : Float := Float.ofNat finalSig / Float.ofNat (1 <<< 52)
          -- Compute 2^finalBExp as an exact Float.
          -- finalBExp ∈ [-1022, 1023] (normal) or -1022 (subnormal).
          -- 2^n for n ∈ [0, 1023] is always representable; 2^n for n ∈ [1, 1022]
          -- is also representable, so 1/2^|n| is exact for n ∈ [-1022, -1].
          -- We avoid `(2.0 : Float) ^ (n : Nat)` because HPow Float Nat Float
          -- is not available in Lean 4 core.
          let powF : Float :=
            if finalBExp >= 0 then Float.ofNat (1 <<< finalBExp.toNat)
            else 1.0 / Float.ofNat (1 <<< (-finalBExp).toNat)
          sigF * powF

/-- Attempt to parse a floating-point literal.

    `intChars` is the already-scanned integer-part digits (may be empty for
    literals like `.5`).  `remaining` is the rest of the input, starting at
    the `'.'` or `'e'`/`'E'` that triggered float detection.

    Supported formats:
      digits . fractdigits? exponent?   (e.g. `3.14`, `1.`, `2.5e10`)
      . fractdigits exponent?           (e.g. `.5`, `.125e-3`)
      digits exponent                   (e.g. `1e10`, `42E-2`)

    Returns `some (.DoubleConstant f, rest)` or `none`. -/
private def tryParseFloat (intChars : List Char) (remaining : List Char)
    : Option (Token × List Char) :=
  -- 1. Optional fractional part: '.' digit*
  let (hasDot, fracChars, rest1) :=
    match remaining with
    | '.' :: afterDot =>
        let (fc, r) := spanChars isDigit afterDot
        (true, fc, r)
    | _ => (false, [], remaining)
  -- 2. Optional exponent: ('e'|'E') ['+'|'-'] digit+
  let (hasExp, negExp, expChars, rest2) :=
    match rest1 with
    | 'e' :: rest | 'E' :: rest =>
        let (negSign, r) := match rest with
          | '-' :: r => (true,  r)
          | '+' :: r => (false, r)
          | r        => (false, r)
        let (ec, r2) := spanChars isDigit r
        if ec.isEmpty then (false, false, [], rest1)   -- 'e' with no digits → not an exp
        else (true, negSign, ec, r2)
    | _ => (false, false, [], rest1)
  -- Must have at least a dot or an exponent
  if !hasDot && !hasExp then none
  else if !atWordBoundary rest2 then none
  else
    let mantissaStr := String.ofList (intChars ++ fracChars)
    let m : Nat := mantissaStr.toNat?.getD 0
    let decShift : Int := fracChars.length
    let expVal : Int :=
      match (String.ofList expChars).toNat? with
      | some e => if negExp then -(e : Int) else (e : Int)
      | none   => 0
    let netExp : Int := expVal - decShift
    -- Use correctly-rounded conversion to avoid the double-rounding bug in
    -- `Float.ofScientific` for large mantissas (> 2^64): that function
    -- converts `m` to Float first (losing precision), then multiplies or
    -- divides by 10^e (a second rounding), yielding the wrong IEEE 754 result
    -- at tie-break points.  Our implementation uses exact Nat arithmetic.
    let f : Float :=
      if netExp >= 0 then
        correctlyRoundedDecimalToFloat (m * Nat.pow 10 netExp.toNat) 1
      else
        correctlyRoundedDecimalToFloat m (Nat.pow 10 (-netExp).toNat)
    some (.DoubleConstant f, rest2)

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
      after it, then parse the digit string as a `Nat`.
    - Floating-point constants (Chapter 13): detected when a digit run is
      followed by `'.'` or `'e'`/`'E'`, or when input starts with `'.'`
      followed by a digit.  Parsed via `tryParseFloat`. -/
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
  -- Chapter 13: floating-point constant starting with '.' (e.g. .5, .25e3)
  -- Must be checked before the catch-all so '.' isn't treated as unknown.
  | '.' :: c :: _ =>
      if isDigit c then tryParseFloat [] chars
      else none
  | '.' :: [] => none   -- lone '.' at end of input
  -- Identifier/keyword and integer/float constant require predicate checks,
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
        -- Integer or floating-point constant starting with a digit.
        -- Suffixes (Chapter 11–12):
        --   l / L            → LongConstant   (signed long)
        --   u / U            → UIntConstant   (unsigned int)
        --   ul / uL / Ul / UL / lu / lU / Lu / LU → ULongConstant (unsigned long)
        -- Chapter 13: digit run followed by '.' or 'e'/'E' → floating-point.
        let (digitChars, remaining) := spanChars isDigit chars
        let n? := (String.ofList digitChars).toNat?
        match remaining with
        -- Chapter 13: float detection — '.' or exponent follows the digit run
        | '.' :: _ | 'e' :: _ | 'E' :: _ =>
            tryParseFloat digitChars remaining
        -- unsigned-long suffixes: ul / uL / Ul / UL
        | 'u' :: 'l' :: rest | 'u' :: 'L' :: rest
        | 'U' :: 'l' :: rest | 'U' :: 'L' :: rest =>
            if atWordBoundary rest then
              match n? with
              | some n => some (.ULongConstant n, rest)
              | none   => none
            else none
        -- unsigned-long suffixes: lu / lU / Lu / LU
        | 'l' :: 'u' :: rest | 'l' :: 'U' :: rest
        | 'L' :: 'u' :: rest | 'L' :: 'U' :: rest =>
            if atWordBoundary rest then
              match n? with
              | some n => some (.ULongConstant n, rest)
              | none   => none
            else none
        -- signed-long suffix: l / L
        | 'l' :: rest | 'L' :: rest =>
            if atWordBoundary rest then
              match n? with
              | some n => some (.LongConstant n, rest)
              | none   => none
            else none   -- e.g. "123Lbar"
        -- unsigned-int suffix: u / U
        | 'u' :: rest | 'U' :: rest =>
            if atWordBoundary rest then
              match n? with
              | some n => some (.UIntConstant n, rest)
              | none   => none
            else none   -- e.g. "123ubar"
        -- No suffix: plain signed int constant
        | _ =>
            if atWordBoundary remaining then
              match n? with
              | some n => some (.Constant n, remaining)
              | none   => none
            else none   -- e.g. "123bar"
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
