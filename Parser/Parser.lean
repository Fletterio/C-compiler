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

/-- Parse a type specifier token or pair.
    Chapter 11: `int long` and `long int` are both equivalent to `long`.
    Used for cast expressions and parameter types (no storage class).
    Returns the `AST.Typ` and the remaining tokens. -/
private def parseType (tokens : List Token) : Except String (Typ × List Token) :=
  match tokens with
  -- Two-keyword combinations: `int long` and `long int` → Long
  | .KwInt  :: .KwLong :: rest => .ok (.Long, rest)
  | .KwLong :: .KwInt  :: rest => .ok (.Long, rest)
  -- Single keywords
  | .KwInt  :: rest => .ok (.Int,  rest)
  | .KwLong :: rest => .ok (.Long, rest)
  | []              => .error "Expected type specifier (int or long) but reached end of input"
  | t :: _          => .error s!"Expected type specifier (int or long) but found {t.describe}"

/-- True if the token is a type specifier (`int` or `long`). -/
private def isTypeToken : Token → Bool
  | .KwInt  => true
  | .KwLong => true
  | _       => false

/-- True if the token is a declaration specifier (type or storage class). -/
private def isDeclSpecToken : Token → Bool
  | .KwInt    => true
  | .KwLong   => true
  | .KwStatic => true
  | .KwExtern => true
  | _         => false

/-- Parse all declaration specifiers in any order (C allows intermixing).
    Collects `int`, `long`, `static`, `extern` in any order, then returns
    the resolved type and storage class.

    Valid type combos: `int`, `long`, `int long`, `long int` (all → Int or Long).
    At most one storage class (`static` or `extern`).

    Used for top-level and block-scope declarations where C allows
    `int static long x` as equivalent to `static long x`. -/
private def parseDeclSpecs (tokens : List Token)
    : Except String (Typ × Option StorageClass × List Token) :=
  let rec loop (toks : List Token) (sawInt : Bool) (sawLong : Bool)
               (sc : Option StorageClass) : Except String (Typ × Option StorageClass × List Token) :=
    match toks with
    | .KwInt :: rest =>
        if sawInt then .error "Duplicate type specifier 'int'"
        else loop rest true sawLong sc
    | .KwLong :: rest =>
        if sawLong then .error "Duplicate type specifier 'long'"
        else loop rest sawInt true sc
    | .KwStatic :: rest =>
        match sc with
        | some _ => .error "Multiple storage class specifiers"
        | none   => loop rest sawInt sawLong (some .Static)
    | .KwExtern :: rest =>
        match sc with
        | some _ => .error "Multiple storage class specifiers"
        | none   => loop rest sawInt sawLong (some .Extern)
    | _ =>
        -- End of declaration specifiers; determine the type
        if sawLong then .ok (.Long, sc, toks)
        else if sawInt then .ok (.Int, sc, toks)
        else .error "Expected type specifier (int or long)"
  loop tokens false false none

-- ---------------------------------------------------------------------------
-- Expression parsing (precedence climbing)
-- ---------------------------------------------------------------------------

mutual

/-- Parse a factor.
    Chapter 11 additions:
    - `LongConstant n` → `Exp.Constant(.ConstLong n)`
    - `Constant n`     → `Exp.Constant(.ConstInt n)` (was plain `Constant n`)
    - `(int)  <factor>` → `Exp.Cast(.Int,  e)` (explicit cast to int)
    - `(long) <factor>` → `Exp.Cast(.Long, e)` (explicit cast to long)

    Prefix `++e` desugars to `Assignment(e, Binary(Add, e, ConstInt(1)))`.
    Prefix `--e` desugars to `Assignment(e, Binary(Subtract, e, ConstInt(1)))`. -/
private partial def parseFactor (tokens : List Token) : Except String (Exp × List Token) :=
  match tokens with
  | []                       => .error "Expected expression but reached end of input"
  -- Chapter 11: long integer constant (e.g. 100L — has l/L suffix)
  | .LongConstant n :: rest  => .ok (.Constant (.ConstLong n), rest)
  -- Regular integer constant: auto-promote to Long if value exceeds INT_MAX.
  -- (C §6.4.4.1: a decimal constant without a suffix is promoted to the
  -- smallest type that can represent it — int, then long.)
  | .Constant n :: rest =>
      if n > 2147483647 then
        .ok (.Constant (.ConstLong (n : Int)), rest)
      else
        .ok (.Constant (.ConstInt (n : Int)), rest)
  | .Minus :: rest           => do let (e, rest') ← parseFactor rest; .ok (.Unary .Negate e, rest')
  | .Tilde :: rest           => do let (e, rest') ← parseFactor rest; .ok (.Unary .Complement e, rest')
  | .Bang  :: rest           => do let (e, rest') ← parseFactor rest; .ok (.Unary .Not e, rest')
  -- Prefix ++ and -- desugar to compound assignment
  | .PlusPlus :: rest   => do
      let (e, rest') ← parseFactor rest
      .ok (.Assignment e (.Binary .Add e (.Constant (.ConstInt 1))), rest')
  | .MinusMinus :: rest => do
      let (e, rest') ← parseFactor rest
      .ok (.Assignment e (.Binary .Subtract e (.Constant (.ConstInt 1))), rest')
  -- Chapter 11: explicit cast expressions `(int)e` or `(long)e`
  -- These must be checked BEFORE the generic `(expr)` case.
  | .OpenParen :: .KwInt  :: .CloseParen :: rest => do
      let (e, rest') ← parseFactor rest
      .ok (.Cast .Int e, rest')
  | .OpenParen :: .KwLong :: .CloseParen :: rest => do
      let (e, rest') ← parseFactor rest
      .ok (.Cast .Long e, rest')
  -- Function call: `identifier "(" args ")"`
  | .Identifier v :: .OpenParen :: rest => do
      let (args, rest') ← parseArgList rest
      match rest' with
      | .PlusPlus   :: rest'' => .ok (.PostfixIncr (.FunCall v args), rest'')
      | .MinusMinus :: rest'' => .ok (.PostfixDecr (.FunCall v args), rest'')
      | _                     => .ok (.FunCall v args, rest')
  | .Identifier v :: rest =>
      match rest with
      | .PlusPlus   :: rest' => .ok (.PostfixIncr (.Var v), rest')
      | .MinusMinus :: rest' => .ok (.PostfixDecr (.Var v), rest')
      | _                    => .ok (.Var v, rest)
  -- Parenthesised expression
  | .OpenParen :: rest  => do
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .CloseParen rest'
      match rest'' with
      | .PlusPlus   :: rest''' => .ok (.PostfixIncr e, rest''')
      | .MinusMinus :: rest''' => .ok (.PostfixDecr e, rest''')
      | _                      => .ok (e, rest'')
  | t :: _  => .error s!"Expected expression but found {t.describe}"

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
  let (typ, scFromSpecs, tokens) ← parseDeclSpecs tokens
  let sc : Option StorageClass ←
    match storageClassOpt, scFromSpecs with
    | some a, some b =>
        if a == b then pure (some a)
        else throw "Multiple storage class specifiers"
    | some a, none  => pure (some a)
    | none,   some b => pure (some b)
    | none,   none   => pure none
  let (name, tokens) ←
    match tokens with
    | .Identifier n :: rest => .ok (n, rest)
    | []                    => .error "Expected variable name but reached end of input"
    | t :: _                => .error s!"Expected variable name but found {t.describe}"
  match tokens with
  | .Equal :: rest => do
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .Semicolon rest'
      .ok ({ name, typ, init := some e, storageClass := sc }, rest'')
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
-- Parameter list parsing (typed params for Chapter 11)
-- ---------------------------------------------------------------------------

/-
  `parseParamList`, `parseParamListTail`, and `parseOneParam` are mutually
  recursive: `parseParamList` calls both helpers, and `parseParamListTail`
  calls `parseOneParam`.  We put all three in a `mutual` block.
-/
mutual

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

/-- Parse a single parameter: `type <identifier>`.
    Chapter 11: type is `int` or `long`. -/
private partial def parseOneParam (tokens : List Token) : Except String ((Typ × String) × List Token) := do
  let (typ, tokens) ← parseType tokens
  match tokens with
  | .Identifier name :: rest => .ok ((typ, name), rest)
  | []                       => .error "Expected parameter name but reached end of input"
  | t :: _                   => .error s!"Expected parameter name but found {t.describe}"

end

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
        let (retTyp, sc, afterSpecs) ← parseDeclSpecs tokens
        match afterSpecs with
        | .Identifier name :: .OpenParen :: rest =>
            -- `type name (` → local function declaration
            parseLocalFunDecl name retTyp sc (.OpenParen :: rest)
        | _ => do
            -- Variable declaration; parseDeclSpecs inside parseVarDecl handles specifiers
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
  let (retTyp, sc, tokens) ← parseDeclSpecs tokens
  -- Parse the name
  let (name, tokens) ←
    match tokens with
    | .Identifier name :: rest => .ok (name, rest)
    | []                       => .error "Expected identifier but reached end of input"
    | t :: _                   => .error s!"Expected identifier but found {t.describe}"
  -- Decide: variable or function by peeking at next token
  match tokens with
  | .OpenParen :: rest => do
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
      let (e, rest')  ← parseExp 0 rest
      let rest''      ← expect .Semicolon rest'
      .ok (.VarDecl { name, typ := retTyp, init := some e, storageClass := sc }, rest'')
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
