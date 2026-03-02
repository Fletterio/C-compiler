namespace Lexer

/-- A single token produced by the lexer. -/
inductive Token where
  | Identifier : String → Token  -- e.g. "main", "foo"
  | Constant   : Nat → Token     -- e.g. 2, 42
  | KwInt      : Token           -- int
  | KwVoid     : Token           -- void
  | KwReturn   : Token           -- return
  | OpenParen  : Token           -- (
  | CloseParen : Token           -- )
  | OpenBrace  : Token           -- {
  | CloseBrace : Token           -- }
  | Semicolon  : Token           -- ;
  deriving Repr, BEq

end Lexer
