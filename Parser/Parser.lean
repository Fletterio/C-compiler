import Lexer.Token
import AST.AST

namespace Parser

open Lexer AST

-- ---------------------------------------------------------------------------
-- Token stream helpers
-- ---------------------------------------------------------------------------

private def takeToken (tokens : List Token) : Except String (Token × List Token) :=
  match tokens with
  | []         => .error "Unexpected end of input"
  | t :: rest  => .ok (t, rest)

private def expect (expected : Token) (tokens : List Token) : Except String (List Token) := do
  let (actual, rest) ← takeToken tokens
  if actual == expected then
    .ok rest
  else
    .error s!"Expected {expected.describe} but found {actual.describe}"

-- ---------------------------------------------------------------------------
-- Binary-operator helpers
-- ---------------------------------------------------------------------------

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
-- Type specifier parsing (Chapter 11)
-- ---------------------------------------------------------------------------

/-- True if the token is a declaration specifier (type or storage class). -/
private def isDeclSpecToken : Token → Bool
  | .KwInt      => true
  | .KwLong     => true
  | .KwUnsigned => true   -- Chapter 12
  | .KwSigned   => true   -- Chapter 12
  | .KwDouble   => true   -- Chapter 13
  | .KwChar     => true   -- Chapter 16
  | .KwVoid     => true   -- Chapter 17: void type
  | .KwStatic   => true
  | .KwExtern   => true
  | _           => false

/-- Parse all declaration specifiers in any order (C allows intermixing).
    Collects `int`, `long`, `unsigned`, `static`, `extern` in any order, then
    returns the resolved type and storage class.

    Valid type combos (Chapter 12):
      `int`, `long`, `int long`, `long int` → Int / Long (signed)
      `unsigned`, `unsigned int`, `int unsigned` → UInt
      `unsigned long`, `long unsigned`, `unsigned long int`, … → ULong

    At most one storage class (`static` or `extern`).

    Used for top-level and block-scope declarations where C allows
    `int static long x` as equivalent to `static long x`. -/
private def parseDeclSpecs (tokens : List Token)
    : Except String (Typ × Option StorageClass × List Token) :=
  let rec loop (toks : List Token) (sawInt : Bool) (sawLong : Bool)
               (sawUnsigned : Bool) (sawSigned : Bool) (sawDouble : Bool)
               (sawChar : Bool) (sawVoid : Bool)
               (sc : Option StorageClass) : Except String (Typ × Option StorageClass × List Token) :=
    match toks with
    | .KwInt :: rest =>
        if sawInt then .error "Duplicate type specifier 'int'"
        else if sawDouble then .error "Cannot combine 'int' with 'double'"
        else if sawChar then .error "Cannot combine 'int' with 'char'"
        else if sawVoid then .error "Cannot combine 'int' with 'void'"
        else loop rest true sawLong sawUnsigned sawSigned false sawChar false sc
    | .KwLong :: rest =>
        if sawLong then .error "Duplicate type specifier 'long'"
        else if sawDouble then .error "Cannot combine 'long' with 'double'"
        else if sawChar then .error "Cannot combine 'long' with 'char'"
        else if sawVoid then .error "Cannot combine 'long' with 'void'"
        else loop rest sawInt true sawUnsigned sawSigned false sawChar false sc
    | .KwUnsigned :: rest =>
        if sawUnsigned then .error "Duplicate type specifier 'unsigned'"
        else if sawSigned then .error "Conflicting type specifiers 'signed' and 'unsigned'"
        else if sawDouble then .error "Cannot combine 'unsigned' with 'double'"
        else if sawVoid then .error "Cannot combine 'unsigned' with 'void'"
        else loop rest sawInt sawLong true sawSigned false sawChar false sc
    | .KwSigned :: rest =>
        if sawUnsigned then .error "Conflicting type specifiers 'unsigned' and 'signed'"
        else if sawDouble then .error "Cannot combine 'signed' with 'double'"
        else if sawVoid then .error "Cannot combine 'signed' with 'void'"
        else loop rest sawInt sawLong sawUnsigned true false sawChar false sc
    | .KwDouble :: rest =>
        -- Chapter 13: 'double' is a standalone type; cannot be combined with
        -- int/long/unsigned/signed (unlike C's 'long double' which we don't support).
        if sawDouble then .error "Duplicate type specifier 'double'"
        else if sawInt || sawLong || sawUnsigned || sawSigned || sawChar || sawVoid then
          .error "Cannot combine 'double' with other type specifiers"
        else loop rest sawInt sawLong sawUnsigned sawSigned true sawChar false sc
    | .KwChar :: rest =>
        -- Chapter 16: 'char' can only be combined with 'signed' or 'unsigned'.
        if sawChar then .error "Duplicate type specifier 'char'"
        else if sawInt || sawLong || sawDouble || sawVoid then
          .error "Cannot combine 'char' with other type specifiers"
        else loop rest sawInt sawLong sawUnsigned sawSigned sawDouble true false sc
    | .KwVoid :: rest =>
        -- Chapter 17: 'void' is a standalone type; cannot be combined with anything.
        if sawVoid then .error "Duplicate type specifier 'void'"
        else if sawInt || sawLong || sawUnsigned || sawSigned || sawDouble || sawChar then
          .error "Cannot combine 'void' with other type specifiers"
        else loop rest sawInt sawLong sawUnsigned sawSigned sawDouble sawChar true sc
    | .KwStatic :: rest =>
        match sc with
        | some _ => .error "Multiple storage class specifiers"
        | none   => loop rest sawInt sawLong sawUnsigned sawSigned sawDouble sawChar sawVoid (some .Static)
    | .KwExtern :: rest =>
        match sc with
        | some _ => .error "Multiple storage class specifiers"
        | none   => loop rest sawInt sawLong sawUnsigned sawSigned sawDouble sawChar sawVoid (some .Extern)
    | _ =>
        -- End of declaration specifiers; determine the type.
        let typ : Except String Typ :=
          if sawVoid then .ok .Void   -- Chapter 17: void
          else if sawDouble then .ok .Double  -- Chapter 13: double
          else if sawChar then
            -- Chapter 16: char types
            if sawUnsigned then .ok .UChar       -- unsigned char
            else if sawSigned then .ok .SChar    -- signed char
            else .ok .Char                       -- plain char (impl-defined sign)
          else if sawUnsigned then
            if sawLong then .ok .ULong   -- unsigned long [int]
            else .ok .UInt               -- unsigned [int]
          else if sawLong then .ok .Long  -- [signed] [int] long
          else if sawInt || sawSigned then .ok .Int  -- [signed] int
          else .error "Expected type specifier (int, long, unsigned, signed, double, char, void, etc.)"
        match typ with
        | .error e => .error e
        | .ok t    => .ok (t, sc, toks)
  loop tokens false false false false false false false none

/-- Consume trailing `*` tokens and wrap the base type in successive `Pointer` layers.
    Chapter 14: `int *` → `Pointer(Int)`, `int **` → `Pointer(Pointer(Int))`, etc. -/
private def consumeStars (baseTyp : Typ) (tokens : List Token) : Typ × List Token :=
  match tokens with
  | .Star :: rest => consumeStars (.Pointer baseTyp) rest
  | _             => (baseTyp, tokens)

/-- Chapter 15: Parse zero or more array dimension suffixes `[N]` after a declarator name.
    Returns a type-wrapping function and the remaining tokens.
    The outermost dimension is the first `[N]` from the left.
    e.g. `[3]`    → `fun t => .Array t 3`
         `[3][4]` → `fun t => .Array (.Array t 4) 3`   (array of 3 × array of 4)
    Accepts integer constants with any suffix (4, 4l, 4ul, 4u) as array sizes.
    This function is used by both `parseAbstractDeclarator` (for cast types like `int (*)[3]`)
    and `parseDeclaratorName` (for concrete declarators like `int arr[3]`). -/
private def parseArrayDimensions (tokens : List Token) : (Typ → Typ) × List Token :=
  -- Helper: extract a Nat from any integer constant token (ignoring signedness/width).
  -- Only plain integer constants without sign-extension issues are valid as array sizes,
  -- but C allows any integer constant expression, so we accept all constant token forms.
  let tryGetDim : Token → Option Nat
    | .Constant n      => some n
    | .LongConstant n  => some n
    | .UIntConstant n  => some n
    | .ULongConstant n => some n
    -- Chapter 16: char constant used as array size, e.g. `char arr['A']`.
    | .CharConstant n  => some n.toNat
    | _                => none
  match tokens with
  -- Chapter 16: `char arr[]` uses an empty `[]` as a sentinel (size = 0).
  -- VarResolution will fill in the actual size from the string initializer length + 1.
  | .OpenBracket :: .CloseBracket :: rest =>
      -- Consume `[]` and recurse to pick up any further dimensions.
      let (innerWrap, rest') := parseArrayDimensions rest
      (fun t => .Array (innerWrap t) 0, rest')
  | .OpenBracket :: tok :: .CloseBracket :: rest =>
      match tryGetDim tok with
      | some n =>
          -- Consume this `[n]` and recurse to pick up any further dimensions.
          let (innerWrap, rest') := parseArrayDimensions rest
          -- The inner wrap handles deeper dimensions; apply it to the element type first,
          -- then wrap with this dimension on the outside.
          (fun t => .Array (innerWrap t) n, rest')
      | none =>
          -- Token is not an integer constant — stop and don't consume.
          (id, tokens)
  | _ =>
      -- Not an array dimension suffix; stop and return the identity wrap.
      (id, tokens)

/-- Parse an abstract declarator (no identifier): zero or more `*` tokens and/or
    parenthesized groups.  Returns a type-wrapping function and the remaining tokens.
    Used for abstract declarators in cast expressions, e.g.:
      `(unsigned long (*))` → Pointer(ULong)
      `(double (*(**)))` → Pointer(Pointer(Pointer(Double)))
    Grammar: abstract-declarator ::= '*'* | '(' abstract-declarator ')' -/
private def parseAbstractDeclarator (tokens : List Token) : (Typ → Typ) × List Token :=
  match tokens with
  | .Star :: rest =>
      -- Consume a `*` and apply another Pointer level around whatever the inner decl produces
      let (innerWrap, rest') := parseAbstractDeclarator rest
      (fun t => innerWrap (.Pointer t), rest')
  | .OpenParen :: rest =>
      -- Parenthesized abstract declarator: recurse inside, then consume ')'
      let (innerWrap, rest') := parseAbstractDeclarator rest
      match expect .CloseParen rest' with
      | .ok rest'' =>
          -- Chapter 15: consume any array dimension suffixes after ')'.
          -- e.g. `int (*)[3]` — after parsing `(*)` we pick up `[3]`.
          -- Combined wrap: fun t => innerWrap (arrWrap t)  e.g. Pointer (Array Int 3)
          let (arrWrap, rest''') := parseArrayDimensions rest''
          (fun t => innerWrap (arrWrap t), rest''')
      | .error _   => (innerWrap, rest')  -- best-effort recovery
  | _ =>
      -- Not a star or paren: stop at base level.
      -- Chapter 17: also consume any trailing array dimension suffixes (e.g. `int[2]` in
      -- `sizeof(int[2])`). Without this, `parseType "int[2]"` would return type `Int`
      -- and leave `[2]` unconsumed, causing a parse error in `sizeof(int[2])`.
      parseArrayDimensions tokens

/-- Parse a type specifier for use in cast expressions and parameters.
    Delegates to `parseDeclSpecs` and strips storage-class info.
    Chapter 12: handles all combinations of int/long/unsigned/signed.
    Chapter 14: handles trailing `*` and parenthesized abstract declarators, e.g.:
      `(unsigned long (*))` and `(double (*(*(*)))))` -/
private def parseType (tokens : List Token) : Except String (Typ × List Token) := do
  match parseDeclSpecs tokens with
  | .ok (_, some _, _) => .error "Storage class specifier not allowed in type name"
  | .ok (baseTyp, none, rest) =>
      -- Use parseAbstractDeclarator (superset of consumeStars) for full abstract declarator support
      let (wrapFn, rest') := parseAbstractDeclarator rest
      .ok (wrapFn baseTyp, rest')
  | .error e => .error e

-- ---------------------------------------------------------------------------
-- Expression parsing (precedence climbing)
-- ---------------------------------------------------------------------------

mutual

/-- Parse a factor.
    Chapter 11 additions:
    - `LongConstant n` → `Exp.Constant(.ConstLong n)`
    - `Constant n`     → `Exp.Constant(.ConstInt n)` (auto-promote to Long if > INT_MAX)
    - `(int)  <factor>` → `Exp.Cast(.Int,  e)`
    - `(long) <factor>` → `Exp.Cast(.Long, e)`

    Chapter 12 additions:
    - `UIntConstant n`  → `Exp.Constant(.ConstUInt n)` (or ConstULong if > UINT_MAX)
    - `ULongConstant n` → `Exp.Constant(.ConstULong n)`
    - `(unsigned) <factor>` / `(unsigned int)` → `Exp.Cast(.UInt, e)`
    - `(unsigned long)` / `(long unsigned)` → `Exp.Cast(.ULong, e)`

    Prefix `++e` desugars to `Assignment(e, Binary(Add, e, ConstInt(1)))`.
    Prefix `--e` desugars to `Assignment(e, Binary(Subtract, e, ConstInt(1)))`. -/
private partial def parseFactor (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | []                       => .error "Expected expression but reached end of input"
  -- Chapter 16: character literal (e.g. 'a' → ConstChar 97)
  | .CharConstant n :: rest  => parsePostfixOps (.Constant (.ConstChar n)) rest
  -- Chapter 16: string literal (e.g. "hello" → StringLiteral "hello")
  | .StringLiteral s :: rest => parsePostfixOps (.StringLiteral s) rest
  -- Chapter 13: floating-point constant (e.g. 3.14, 1.5e10)
  -- Chapter 15: constants can be subscripted (`3[arr]` == `arr[3]` in C), so pass
  -- through parsePostfixOps.
  | .DoubleConstant f :: rest => parsePostfixOps (.Constant (.ConstDouble f)) rest
  -- Chapter 11: long integer constant (e.g. 100L — has l/L suffix)
  | .LongConstant n :: rest  => parsePostfixOps (.Constant (.ConstLong n)) rest
  -- Chapter 12: unsigned long constant (e.g. 100UL — has ul/lu suffix)
  | .ULongConstant n :: rest => parsePostfixOps (.Constant (.ConstULong (n : Int))) rest
  -- Chapter 12: unsigned int constant (e.g. 100U — has u/U suffix)
  -- Auto-promote to ULong if value exceeds UINT_MAX (4294967295)
  | .UIntConstant n :: rest =>
      if n > 4294967295 then
        parsePostfixOps (.Constant (.ConstULong (n : Int))) rest
      else
        parsePostfixOps (.Constant (.ConstUInt (n : Int))) rest
  -- Regular integer constant: auto-promote to Long if value exceeds INT_MAX.
  -- (C §6.4.4.1: a decimal constant without a suffix is promoted to the
  -- smallest type that can represent it — int, then long.)
  | .Constant n :: rest =>
      if n > 2147483647 then
        parsePostfixOps (.Constant (.ConstLong (n : Int))) rest
      else
        parsePostfixOps (.Constant (.ConstInt (n : Int))) rest
  | .Minus     :: rest => do let (e, rest') ← parseFactor rest; .ok (.Unary .Negate e, rest')
  | .Tilde     :: rest => do let (e, rest') ← parseFactor rest; .ok (.Unary .Complement e, rest')
  | .Bang      :: rest => do let (e, rest') ← parseFactor rest; .ok (.Unary .Not e, rest')
  -- Chapter 14: unary `*` (dereference) and `&` (address-of)
  | .Star      :: rest => do let (e, rest') ← parseFactor rest; .ok (.Dereference e, rest')
  | .Ampersand :: rest => do let (e, rest') ← parseFactor rest; .ok (.AddrOf e, rest')
  -- Chapter 17: sizeof operator.
  -- `sizeof(type)` is parsed when the token after `(` is a type specifier token.
  -- `sizeof expr`  is parsed as a unary operator on a factor (no parentheses needed).
  -- `sizeof(expr)` is also handled: the `(expr)` is a parenthesised factor.
  | .KwSizeof :: .OpenParen :: rest =>
      -- After `sizeof(`, peek: if a type specifier follows, it's sizeof(type).
      -- Otherwise it's sizeof(expr) where (expr) is a parenthesised factor.
      match parseType rest with
      | .ok (t, .CloseParen :: rest') => .ok (.SizeOfT t, rest')
      | _ =>
          -- Not a type — parse as `sizeof(expr)` where (expr) is a paren expression
          do
            let (e, rest') ← parseExp 0 rest
            let rest''     ← expect .CloseParen rest'
            .ok (.SizeOf e, rest'')
  | .KwSizeof :: rest => do
      let (e, rest') ← parseFactor rest
      .ok (.SizeOf e, rest')
  -- Prefix ++ and -- desugar to compound assignment
  | .PlusPlus :: rest   => do
      let (e, rest') ← parseFactor rest
      .ok (.Assignment e (.Binary .Add e (.Constant (.ConstInt 1))), rest')
  | .MinusMinus :: rest => do
      let (e, rest') ← parseFactor rest
      .ok (.Assignment e (.Binary .Subtract e (.Constant (.ConstInt 1))), rest')
  -- Explicit cast expressions: `(type)e`
  -- These must be checked BEFORE the generic `(expr)` case.
  -- Chapter 11: (int)e, (long)e, (int long)e, (long int)e
  -- Chapter 12: (unsigned)e, (unsigned int)e, (unsigned long)e, etc.
  | .OpenParen :: rest =>
      -- Try to parse a type specifier followed by CloseParen; if it matches,
      -- this is a cast expression.  Otherwise fall through to parenthesised exp.
      match parseType rest with
      | .ok (castTyp, .CloseParen :: afterParen) => do
          let (e, rest') ← parseFactor afterParen
          .ok (.Cast castTyp e, rest')
      | _ =>
          -- Not a cast; parse a parenthesised expression
          do
            let (e, rest')  ← parseExp 0 rest
            let rest''      ← expect .CloseParen rest'
            -- Chapter 15: delegate postfix ops (++, --, [idx]) to parsePostfixOps
            parsePostfixOps e rest''
  -- Function call: `identifier "(" args ")"`
  | .Identifier v :: .OpenParen :: rest => do
      let (args, rest') ← parseArgList rest
      -- Chapter 15: delegate postfix ops (++, --, [idx]) to parsePostfixOps
      parsePostfixOps (.FunCall v args) rest'
  | .Identifier v :: rest =>
      -- Chapter 15: delegate postfix ops (++, --, [idx]) to parsePostfixOps
      parsePostfixOps (.Var v) rest
  | t :: _  => .error s!"Expected expression but found {t.describe}"

/-- Chapter 15: Apply zero or more postfix operators to `e`.
    Handles (in chaining order):
      `[idx]`  → `Subscript(e, idx)`, then continue applying more postfix ops.
      `++`     → `PostfixIncr(e)` (terminal).
      `--`     → `PostfixDecr(e)` (terminal).
    This replaces the ad-hoc `++ / --` matches that were spread through `parseFactor`.
    Examples:
      `a[0][1]++` → PostfixIncr(Subscript(Subscript(Var a, 0), 1))
      `f()[2]`    → Subscript(FunCall f [], 2) -/
private partial def parsePostfixOps (e : Exp) (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | .OpenBracket :: rest => do
      -- Subscript: consume `[`, parse the index expression, then consume `]`.
      let (idx, rest') ← parseExp 0 rest
      let rest''       ← expect .CloseBracket rest'
      -- Recurse: `a[0][1]` chains to another subscript.
      parsePostfixOps (.Subscript e idx) rest''
  -- Chapter 15: postfix ++ and -- are NOT terminal — `ptr--[idx]` should parse as
  -- `(ptr--)[idx]`, so we recurse after applying the postfix op.
  | .PlusPlus   :: rest => parsePostfixOps (.PostfixIncr e) rest
  | .MinusMinus :: rest => parsePostfixOps (.PostfixDecr e) rest
  | _                   => .ok (e, tokens)              -- no more postfix ops

private partial def parseArgList (tokens : List Token) : Except String (List Exp × List Token) :=
  match tokens with
  | .CloseParen :: rest => .ok ([], rest)
  | _ => do
      let (firstArg, rest) ← parseExp 0 tokens
      let (moreArgs, rest') ← parseArgListTail rest
      .ok (firstArg :: moreArgs, rest')

private partial def parseArgListTail (tokens : List Token) : Except String (List Exp × List Token) :=
  match tokens with
  | .CloseParen :: rest => .ok ([], rest)
  | .Comma :: rest => do
      let (arg, rest') ← parseExp 0 rest
      let (moreArgs, rest'') ← parseArgListTail rest'
      .ok (arg :: moreArgs, rest'')
  | [] => .error "Expected \")\" or \",\" in argument list but reached end of input"
  | t :: _ => .error s!"Expected \")\" or \",\" in argument list but found {t.describe}"

private partial def parseExp (minPrec : Nat) (tokens : List Token) : Except String (Exp × List Token) := do
  let (left, tokens) ← parseFactor tokens
  parseExpClimb minPrec left tokens

private partial def parseExpClimb (minPrec : Nat) (left : Exp) (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | tok :: rest =>
    match assignmentOp tok with
    | some compoundOp =>
      if 1 >= minPrec then do
        let (right, rest') ← parseExp 1 rest
        let rhs := match compoundOp with
                   | none    => right
                   | some op => .Binary op left right
        parseExpClimb minPrec (.Assignment left rhs) rest'
      else
        .ok (left, tokens)
    | none =>
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
-- Storage class parsing
-- ---------------------------------------------------------------------------

private def parseStorageClass (tokens : List Token) : Option StorageClass × List Token :=
  match tokens with
  | .KwStatic :: rest => (some .Static, rest)
  | .KwExtern :: rest => (some .Extern, rest)
  | _                 => (none, tokens)

-- ---------------------------------------------------------------------------
-- Optional expression parsing (must be defined before parseStatement mutual block)
-- ---------------------------------------------------------------------------

/-- Parse an optional expression followed by the given delimiter.
    Returns `(none, rest)` if the delimiter appears immediately.
    Returns `(some e, rest)` if an expression is present. -/
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

-- ---------------------------------------------------------------------------
-- Declarator and parameter list parsing (Chapter 14: parenthesized declarators)
-- ---------------------------------------------------------------------------

/-
  `parseDeclaratorName`, `parseParamList`, `parseParamListTail`, and
  `parseOneParam` are mutually recursive.  `parseDeclaratorName` calls
  `parseParamList` (for inline function params in a declarator), and
  `parseParamList`/`parseParamListTail` call `parseOneParam`, which calls
  `parseDeclaratorName` for parameter declarators.  All four go in one `mutual`
  block, which must be defined BEFORE `parseVarDecl` so that `parseVarDecl`
  can call `parseDeclaratorName`.
-/

mutual

/-- Parse a concrete declarator (one that contains an identifier at its core).
    Chapter 14: handles parenthesized and pointer-qualified declarators such as
      `(*ptr)`, `(**ptr)`, `(name)`, `(*(name))`, `(name(params))`, etc.
    Grammar:
      declarator ::= '*' declarator
                   | '(' declarator ')'
                   | identifier [ '(' param-list ')' ]
    Returns `(name, wrapFn, paramsOpt, rest)`:
      - `name`:      the identifier at the core of the declarator.
      - `wrapFn`:    `Typ → Typ` — applies pointer levels from the declarator.
      - `paramsOpt`: `some params` if function params appeared inside this declarator.
      - `rest`:      remaining tokens after the declarator. -/
private partial def parseDeclaratorName (tokens : List Token)
    : Except String (String × (Typ → Typ) × Option (List (Typ × String)) × List Token) := do
  match tokens with
  | .Star :: rest =>
      -- Pointer star: one more Pointer level applied around inner wrap
      let (name, innerWrap, paramsOpt, rest') ← parseDeclaratorName rest
      return (name, fun t => innerWrap (.Pointer t), paramsOpt, rest')
  | .OpenParen :: rest =>
      -- Parenthesized declarator: recurse, then expect ')'
      let (name, innerWrap, paramsOpt, rest') ← parseDeclaratorName rest
      let rest'' ← expect .CloseParen rest'
      -- After closing ')', check for left-recursive function parameter application.
      -- e.g. `(name)(params)` or `(*name)(params)` or `((name))(params)`.
      -- This handles declarators like `(*(*((f)(int *(*p)))))` where params
      -- follow a parenthesized sub-declarator rather than immediately following
      -- the identifier.
      match paramsOpt, rest'' with
      | none, .OpenParen :: rest''' =>
          -- No inline params yet, but '(' follows: parse params here.
          let (params, rest4) ← parseParamList rest'''
          return (name, innerWrap, some params, rest4)
      | _, _ =>
          -- Either we already have params (from a deeper level) or no params follow.
          -- Chapter 15: consume any array dimension suffixes after the closing ')'.
          -- e.g. `int (*p)[3]` — the `[3]` after `)` means pointer-to-array.
          --   innerWrap = (Pointer) from the `*` inside the parens
          --   arrWrap   = (Array T 3) from the `[3]` after the parens
          --   Combined: fun t => innerWrap (arrWrap t)  →  Pointer (Array Int 3)
          let (arrWrap, rest''') := parseArrayDimensions rest''
          return (name, fun t => innerWrap (arrWrap t), paramsOpt, rest''')
  | .Identifier name :: .OpenParen :: rest =>
      -- Identifier followed immediately by '(' — function params inside the declarator
      -- (e.g., `return_3(void)` inside `(return_3(void))`)
      let (params, rest') ← parseParamList rest
      return (name, id, some params, rest')
  | .Identifier name :: rest =>
      -- Chapter 15: after a plain identifier, consume any `[N]` array dimension suffixes.
      -- e.g. `int arr[5]`   → wrapFn = fun t => .Array t 5
      --      `int arr[3][4]` → wrapFn = fun t => .Array (.Array t 4) 3
      let (arrWrap, rest') := parseArrayDimensions rest
      return (name, arrWrap, none, rest')
  | [] => .error "Expected declarator but reached end of input"
  | t :: _ => .error s!"Expected declarator but found {t.describe}"

/-- Parse a parameter list.
    Grammar: `void ")"` | `type id { "," type id } ")"`.
    Returns `List (Typ × String)` — typed parameter pairs. -/
private partial def parseParamList (tokens : List Token) : Except String (List (Typ × String) × List Token) :=
  match tokens with
  | .KwVoid :: .CloseParen :: rest => .ok ([], rest)
  | .CloseParen :: rest            => .ok ([], rest)
  | _ => do
      let (firstParam, rest) ← parseOneParam tokens
      let (moreParams, rest') ← parseParamListTail rest
      .ok (firstParam :: moreParams, rest')

/-- Parse the tail of a parameter list (after the first parameter). -/
private partial def parseParamListTail (tokens : List Token) : Except String (List (Typ × String) × List Token) :=
  match tokens with
  | .CloseParen :: rest => .ok ([], rest)
  | .Comma :: rest => do
      let (param, rest') ← parseOneParam rest
      let (params, rest'') ← parseParamListTail rest'
      .ok (param :: params, rest'')
  | [] => .error "Expected \")\" or \",\" in parameter list but reached end of input"
  | t :: _ => .error s!"Expected \")\" or \",\" in parameter list but found {t.describe}"

/-- Parse a single parameter: `type declarator`.
    Chapter 14: uses `parseDeclaratorName` so parenthesized parameter declarators
    such as `double(*d)` and `int(**p)` are accepted. -/
private partial def parseOneParam (tokens : List Token) : Except String ((Typ × String) × List Token) := do
  let (baseTyp, scOpt, tokens) ← parseDeclSpecs tokens
  -- Storage-class specifiers (static, extern) are not allowed in parameter declarations.
  if scOpt.isSome then
    throw "Storage class specifier not allowed in parameter declaration"
  let (name, wrapFn, _, tokens) ← parseDeclaratorName tokens
  -- wrapFn applies pointer levels and array dimensions from the declarator to the base type.
  let paramTyp := wrapFn baseTyp
  -- Chapter 17: C §6.7.6.3 requires array element types to be complete.
  -- Even though `void foo[3]` is adjusted to `void *`, it is illegal because
  -- void is an incomplete type.  Detect this BEFORE adjustment (we lose the
  -- original Array structure afterwards).
  let _ ← match paramTyp with
    | .Array .Void _ =>
        throw "Parameter declared as 'array of void': void is an incomplete type"
    | _ => pure ()
  -- C §6.7.6.3: "A declaration of a parameter as 'array of type' shall be adjusted to
  -- 'qualified pointer to type'."  The outermost Array wrapper is replaced by a Pointer.
  let adjustedTyp : AST.Typ := match paramTyp with
    | .Array elemTyp _ => .Pointer elemTyp
    | t => t
  return ((adjustedTyp, name), tokens)

end

-- ---------------------------------------------------------------------------
-- Initializer parsing (Chapter 15)
-- ---------------------------------------------------------------------------

/-
  `parseInitializer`, `parseCompoundInitTail`, and `parseCompoundInitListTail`
  are mutually recursive: each `{...}` invokes all three in a cycle.
  All three live in one `mutual` block so Lean accepts the forward references.
-/
mutual

/-- Chapter 15: Parse an initializer for a variable declaration.
    Grammar:
      initializer ::= '{' initializer-list '}'   -- compound (for arrays)
                    | exp                          -- scalar
    The compound form `{ e1, e2, e3 }` produces `CompoundInit [SingleInit e1, ...]`.
    Nested compound forms (for multi-dimensional arrays) are supported.
    A trailing comma before `}` is accepted for convenience. -/
private partial def parseInitializer (tokens : List Token) : Except String (Initializer × List Token) :=
  match tokens with
  | .OpenBrace :: rest =>
      -- Compound initializer: parse a brace-enclosed list of sub-initializers
      parseCompoundInitTail rest
  | _ => do
      -- Scalar initializer: parse an expression
      let (e, rest) ← parseExp 0 tokens
      .ok (.SingleInit e, rest)

/-- Parse the inside and closing `}` of a compound initializer. -/
private partial def parseCompoundInitTail (tokens : List Token) : Except String (Initializer × List Token) := do
  match tokens with
  | .CloseBrace :: _ =>
      -- Empty compound initializer `{}` — illegal in C89/C11 (valid only in C23).
      .error "Empty initializer list `{}` is not supported (C99/C11); use at least one element"
  | _ => do
      -- Parse first element, then the rest
      let (first, rest) ← parseInitializer tokens
      let (inits, rest') ← parseCompoundInitListTail rest
      .ok (.CompoundInit (first :: inits), rest')

/-- Parse the tail of a compound initializer list (after the first element). -/
private partial def parseCompoundInitListTail (tokens : List Token) : Except String (List Initializer × List Token) :=
  match tokens with
  | .CloseBrace :: rest =>
      -- End of list
      .ok ([], rest)
  | .Comma :: .CloseBrace :: rest =>
      -- Trailing comma before `}` — allowed
      .ok ([], rest)
  | .Comma :: rest => do
      -- Another element
      let (elem, rest')  ← parseInitializer rest
      let (more, rest'') ← parseCompoundInitListTail rest'
      .ok (elem :: more, rest'')
  | [] => .error "Expected \"}\" or \",\" in compound initializer but reached end of input"
  | t :: _ => .error s!"Expected \"}\" or \",\" in compound initializer but found {t.describe}"

end

-- ---------------------------------------------------------------------------
-- Declaration parsing (variables)
-- ---------------------------------------------------------------------------

/-- Parse a variable declaration: `<decl-specs> <identifier> [ = <exp> ] ;`
    Uses `parseDeclSpecs` so that `int`, `long`, `static`, `extern` may appear
    in any order (C allows `int static long x` etc.).
    `storageClassOpt` is a pre-parsed storage class from the caller; if the
    decl-specs also contain a storage class, the two must agree. -/
private def parseVarDecl (tokens : List Token) (storageClassOpt : Option StorageClass := none)
    : Except String (Declaration × List Token) := do
  -- Parse all declaration specifiers in any order
  let (baseTyp, scFromSpecs, tokens) ← parseDeclSpecs tokens
  let sc : Option StorageClass ←
    match storageClassOpt, scFromSpecs with
    | some a, some b =>
        if a == b then pure (some a)
        else throw "Multiple storage class specifiers"
    | some a, none  => pure (some a)
    | none,   some b => pure (some b)
    | none,   none   => pure none
  -- Chapter 14: use parseDeclaratorName to handle parenthesized declarators
  -- e.g. `int(*ptr)`, `double(d1)`, `long(*(l_ptr))`, etc.
  let (name, wrapFn, paramsOpt, tokens) ← parseDeclaratorName tokens
  -- A variable declaration cannot have function parameters embedded in its declarator.
  -- If parseDeclaratorName found inline params (e.g. `int f(void)`), this is actually
  -- a function declaration and is not valid in a variable-declaration context.
  if paramsOpt.isSome then
    throw s!"Unexpected function declarator for '{name}' in variable declaration context"
  let typ := wrapFn baseTyp
  match tokens with
  | .Equal :: rest => do
      -- Chapter 15: initializer may be a compound `{ e1, e2, ... }` or a scalar expression.
      let (init, rest') ← parseInitializer rest
      let rest''        ← expect .Semicolon rest'
      .ok ({ name, typ, init := some init, storageClass := sc }, rest'')
  | _ => do
      let rest ← expect .Semicolon tokens
      .ok ({ name, typ, init := none, storageClass := sc }, rest)

-- ---------------------------------------------------------------------------
-- For-loop init parsing
-- ---------------------------------------------------------------------------

/-- Parse the initial clause of a `for` loop.
    Chapter 11: handles both `int` and `long` variable declarations.
    Uses `isDeclSpecToken` so that any ordering of int/long/static/extern is accepted. -/
private def parseForInit (tokens : List Token) : Except String (ForInit × List Token) :=
  match tokens with
  | t :: _ =>
    if isDeclSpecToken t then do
      -- Declaration specifier starts a variable declaration
      let (decl, rest) ← parseVarDecl tokens
      .ok (.InitDecl decl, rest)
    else
      match tokens with
      | .Semicolon :: rest =>
          .ok (.InitExp none, rest)
      | _ => do
          let (e, rest)  ← parseExp 0 tokens
          let rest'      ← expect .Semicolon rest
          .ok (.InitExp (some e), rest')
  | [] =>
    .ok (.InitExp none, [])

-- ---------------------------------------------------------------------------
-- Statement and block-item parsing
-- ---------------------------------------------------------------------------

/-
  `parseStatement`, `parseLocalFunDecl`, `parseBlockItem`, and
  `parseBlockItems` are mutually recursive through `Compound` statements
  (which contain block items) and function bodies.  All four are put in a
  `mutual` block.  `parseOptionalExp` is defined earlier so it can be called
  from inside this block.
-/
mutual

private partial def parseStatement (tokens : List Token) : Except String (Statement × List Token) :=
  match tokens with
  | .Semicolon :: rest =>
      .ok (.Null, rest)
  | .KwReturn :: .Semicolon :: rest =>
      -- Chapter 17: `return;` for void functions — no expression
      .ok (.Return none, rest)
  | .KwReturn :: rest => do
      -- `return expr;` — parse expression then semicolon
      let (exp, rest') ← parseExp 0 rest
      let rest''       ← expect .Semicolon rest'
      .ok (.Return (some exp), rest'')
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
  | .OpenBrace :: rest => do
      let (items, rest') ← parseBlockItems rest
      let rest''         ← expect .CloseBrace rest'
      .ok (.Compound items, rest'')
  | .KwWhile :: rest => do
      let rest'          ← expect .OpenParen rest
      let (cond, rest'') ← parseExp 0 rest'
      let rest'''        ← expect .CloseParen rest''
      let (body, rest4)  ← parseStatement rest'''
      .ok (.While cond body none, rest4)
  | .KwDo :: rest => do
      let (body, rest')  ← parseStatement rest
      let rest''         ← expect .KwWhile rest'
      let rest'''        ← expect .OpenParen rest''
      let (cond, rest4)  ← parseExp 0 rest'''
      let rest5          ← expect .CloseParen rest4
      let rest6          ← expect .Semicolon rest5
      .ok (.DoWhile body cond none, rest6)
  | .KwFor :: rest => do
      let rest'            ← expect .OpenParen rest
      let (init, rest'')   ← parseForInit rest'
      let (cond, rest''')  ← parseOptionalExp .Semicolon rest''
      let (post, rest4)    ← parseOptionalExp .CloseParen rest'''
      let (body, rest5)    ← parseStatement rest4
      .ok (.For init cond post body none, rest5)
  | .KwBreak :: rest => do
      let rest' ← expect .Semicolon rest
      .ok (.Break none, rest')
  | .KwContinue :: rest => do
      let rest' ← expect .Semicolon rest
      .ok (.Continue none, rest')
  | .KwSwitch :: rest => do
      let rest'          ← expect .OpenParen rest
      let (exp, rest'')  ← parseExp 0 rest'
      let rest'''        ← expect .CloseParen rest''
      let (body, rest4)  ← parseStatement rest'''
      .ok (.Switch exp body none [], rest4)
  -- Case with plain integer constant
  | .KwCase :: .Minus :: .Constant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (-(n : Int)) stmt none, rest')
  | .KwCase :: .Constant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (n : Int) stmt none, rest')
  -- Chapter 11: case with long constant (e.g. `case 8589934592l:`)
  | .KwCase :: .Minus :: .LongConstant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (-(n : Int)) stmt none, rest')
  | .KwCase :: .LongConstant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (n : Int) stmt none, rest')
  -- Chapter 12: case with unsigned int constant (e.g. `case 42u:`)
  | .KwCase :: .UIntConstant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (n : Int) stmt none, rest')
  -- Chapter 12: case with unsigned long constant (e.g. `case 100ul:`)
  | .KwCase :: .ULongConstant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case (n : Int) stmt none, rest')
  -- Chapter 16: case with char constant (e.g. `case 'A':`)
  | .KwCase :: .CharConstant n :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Case n stmt none, rest')
  | .KwCase :: _ => .error "case expression must be an integer constant"
  | .KwDefault :: rest => do
      let rest'          ← expect .Colon rest
      let (stmt, rest'') ← parseStatement rest'
      .ok (.Default stmt none, rest'')
  | .KwGoto :: .Identifier label :: rest => do
      let rest' ← expect .Semicolon rest
      .ok (.Goto label, rest')
  | .Identifier label :: .Colon :: rest => do
      let (stmt, rest') ← parseStatement rest
      .ok (.Labeled label stmt, rest')
  | _ => do
      let (exp, rest) ← parseExp 0 tokens
      let rest'       ← expect .Semicolon rest
      .ok (.Expression exp, rest')

/-- Parse a local function declaration (no body) after the name token is known. -/
private partial def parseLocalFunDecl (name : String) (retTyp : Typ)
    (sc : Option StorageClass) (rest : List Token)
    : Except String (BlockItem × List Token) := do
  let rest' ← expect .OpenParen rest
  let (params, rest'') ← parseParamList rest'
  match rest'' with
  | .Semicolon :: rest''' =>
      .ok (.FD { name, params, retTyp, storageClass := sc }, rest''')
  | .OpenBrace :: _ =>
      .error s!"Function definition for '{name}' inside a function is not allowed"
  | [] => .error "Expected \";\" after local function declaration but reached end of input"
  | t :: _ => .error s!"Expected \";\" after local function declaration but found {t.describe}"

/-- Parse a block item: variable declaration, local function declaration, or statement.
    Chapter 11: handles both `int` and `long` type specifiers.

    The C grammar for block items requires distinguishing:
      `[sc] type name ( ...`  →  local function declaration
      `[sc] type name ...`    →  variable declaration
      `stmt`                  →  statement

    Since Lean 4 match does not support `when` guards on list patterns,
    we use nested `if`/`match` expressions to inspect the head token. -/
private partial def parseBlockItem (tokens : List Token) : Except String (BlockItem × List Token) :=
  match tokens with
  | t :: _ =>
      -- A block item is a declaration if it starts with any declaration specifier
      -- (int, long, static, extern — in any order).
      if isDeclSpecToken t then do
        -- Peek at all declaration specifiers to determine type, storage class, and name.
        -- This handles any ordering such as `int static long x`, `static int x`, etc.
        let (baseRetTyp, sc, afterSpecs) ← parseDeclSpecs tokens
        -- Chapter 14: use parseDeclaratorName for lookahead to handle parenthesized declarators
        -- like `int(*ptr)`, `long(*(l_ptr))`, etc.
        let (name, wrapFn, inlineParamsOpt, afterDecl) ← parseDeclaratorName afterSpecs
        let retTyp := wrapFn baseRetTyp
        match inlineParamsOpt with
        | some params =>
            -- parseDeclaratorName already consumed `name(params)` (e.g. `foo(void)`);
            -- afterDecl is the tokens following the closing ')'.
            -- Local function definitions with a body are not allowed inside a function.
            match afterDecl with
            | .Semicolon :: rest''' =>
                .ok (.FD { name, params, retTyp, storageClass := sc }, rest''')
            | .OpenBrace :: _ =>
                .error s!"Function definition for '{name}' inside a function is not allowed"
            | [] => .error "Expected \";\" after local function declaration but reached end of input"
            | t :: _ => .error s!"Expected \";\" after local function declaration but found {t.describe}"
        | none =>
            match afterDecl with
            | .OpenParen :: _ =>
                -- Name followed by '(': local function declaration with params outside
                parseLocalFunDecl name retTyp sc afterDecl
            | _ => do
                -- Variable declaration: re-parse from scratch using parseVarDecl
                let (decl, rest) ← parseVarDecl tokens
                .ok (.D decl, rest)
      else do
        -- Not a declaration specifier: must be a statement
        let (stmt, rest) ← parseStatement tokens
        .ok (.S stmt, rest)
  | _ => do
      let (stmt, rest) ← parseStatement tokens
      .ok (.S stmt, rest)

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
-- Top-level declaration/definition parsing
-- ---------------------------------------------------------------------------

/-- Parse a top-level declaration or definition.
    Grammar (Chapter 11):
      `[sc] type [sc] <name> "(" params ")" ";" | "{" body "}"` → FunDecl/FunDef
      `[sc] type [sc] <name> [ "=" exp ] ";"`                    → VarDecl

    Chapter 11: `type` is `int` or `long` (not just `int`).
    Both orderings of storage class and type are accepted. -/
private partial def parseTopLevel (tokens : List Token) : Except String (TopLevel × List Token) := do
  -- Parse all declaration specifiers in any order (int/long/static/extern may be intermixed)
  let (baseRetTyp, sc, tokens) ← parseDeclSpecs tokens
  -- Chapter 14: use parseDeclaratorName to handle parenthesized/pointer declarators.
  -- e.g. `int(return_3)(void)`, `long(*two_pointers(params))`, etc.
  let (name, wrapFn, inlineParamsOpt, tokens) ← parseDeclaratorName tokens
  let retTyp := wrapFn baseRetTyp
  -- inlineParamsOpt: Some params if function params appeared inside the declarator
  -- (e.g., `int(return_3(void))` or `long(*f(params))`).
  -- tokens: if it starts with '(' it's a function with params outside the declarator.
  match inlineParamsOpt with
  | some params =>
      -- Params were inside the declarator: decide function/variable from what follows
      match tokens with
      | .Semicolon :: rest' =>
          .ok (.FunDecl { name, params, retTyp, storageClass := sc }, rest')
      | .OpenBrace :: rest' => do
          let (body, rest'') ← parseBlockItems rest'
          let rest'''        ← expect .CloseBrace rest''
          .ok (.FunDef { name, params, retTyp, body, storageClass := sc }, rest''')
      | [] => .error s!"Expected open-brace or semicolon after function header for {name} but reached end of input"
      | t :: _ => .error s!"Expected open-brace or semicolon after function header for {name} but found {t.describe}"
  | none =>
      -- No inline params: check what follows to decide function vs variable
      match tokens with
      | .OpenParen :: rest => do
          -- '(' follows: function params outside the declarator
          let (params, tokens) ← parseParamList rest
          match tokens with
          | .Semicolon :: rest' =>
              .ok (.FunDecl { name, params, retTyp, storageClass := sc }, rest')
          | .OpenBrace :: rest' => do
              let (body, rest'') ← parseBlockItems rest'
              let rest'''        ← expect .CloseBrace rest''
              .ok (.FunDef { name, params, retTyp, body, storageClass := sc }, rest''')
          | [] => .error s!"Expected open-brace or semicolon after function header for {name} but reached end of input"
          | t :: _ => .error s!"Expected open-brace or semicolon after function header for {name} but found {t.describe}"
      | .Equal :: rest => do
          -- Chapter 15: initializer may be a compound `{ e1, e2, ... }` or a scalar expression.
          let (init, rest') ← parseInitializer rest
          let rest''        ← expect .Semicolon rest'
          .ok (.VarDecl { name, typ := retTyp, init := some init, storageClass := sc }, rest'')
      | .Semicolon :: rest =>
          .ok (.VarDecl { name, typ := retTyp, init := none, storageClass := sc }, rest)
      | [] => .error s!"Expected open-paren, semicolon, or equals after name {name} but reached end of input"
      | t :: _ => .error s!"Expected open-paren, semicolon, or equals after name {name} but found {t.describe}"

private partial def parseTopLevels (tokens : List Token) : Except String (List TopLevel) :=
  match tokens with
  | []   => .ok []
  | _    => do
      let (item, rest) ← parseTopLevel tokens
      let items        ← parseTopLevels rest
      .ok (item :: items)

def parseProgram (tokens : List Token) : Except String Program := do
  let topLevels ← parseTopLevels tokens
  .ok { topLevels }

end Parser
