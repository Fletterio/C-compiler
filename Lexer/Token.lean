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
  | Tilde      : Token           -- ~
  | Minus      : Token           -- -
  | MinusMinus : Token           -- --
  | Plus         : Token           -- +
  | Star         : Token           -- *
  | Slash        : Token           -- /
  | Percent      : Token           -- %
  | Ampersand      : Token           -- &
  | Pipe           : Token           -- |
  | Caret          : Token           -- ^
  | LessLess       : Token           -- <<
  | GreaterGreater : Token           -- >>
  | Bang           : Token           -- !
  | AmpAmp         : Token           -- &&
  | PipePipe       : Token           -- ||
  | EqualEqual     : Token           -- ==
  | BangEqual      : Token           -- !=
  | Less           : Token           -- <
  | Greater        : Token           -- >
  | LessEqual      : Token           -- <=
  | GreaterEqual   : Token           -- >=
  deriving Repr, BEq

/-- Human-readable description of a token, used in parser error messages. -/
def Token.describe : Token → String
  | .Identifier s => s!"identifier \"{s}\""
  | .Constant n   => s!"constant \"{n}\""
  | .KwInt        => "\"int\""
  | .KwVoid       => "\"void\""
  | .KwReturn     => "\"return\""
  | .OpenParen    => "\"(\""
  | .CloseParen   => "\")\""
  | .OpenBrace    => "\"{\""
  | .CloseBrace   => "\"}\""
  | .Semicolon    => "\";\""
  | .Tilde        => "\"~\""
  | .Minus        => "\"-\""
  | .MinusMinus   => "\"--\""
  | .Plus           => "\"+\""
  | .Star           => "\"*\""
  | .Slash          => "\"/\""
  | .Percent        => "\"%\""
  | .Ampersand      => "\"&\""
  | .Pipe           => "\"|\""
  | .Caret          => "\"^\""
  | .LessLess       => "\"<<\""
  | .GreaterGreater => "\">>\""
  | .Bang           => "\"!\""
  | .AmpAmp         => "\"&&\""
  | .PipePipe       => "\"||\""
  | .EqualEqual     => "\"==\""
  | .BangEqual      => "\"!=\""
  | .Less           => "\"<\""
  | .Greater        => "\">\""
  | .LessEqual      => "\"<=\""
  | .GreaterEqual   => "\">=\""

end Lexer
