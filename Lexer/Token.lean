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
  -- Chapter 5: assignment and compound assignment operators
  | Equal               : Token      -- =
  | PlusPlus            : Token      -- ++
  | PlusEqual           : Token      -- +=
  | MinusEqual          : Token      -- -=
  | StarEqual           : Token      -- *=
  | SlashEqual          : Token      -- /=
  | PercentEqual        : Token      -- %=
  | AmpEqual            : Token      -- &=
  | PipeEqual           : Token      -- |=
  | CaretEqual          : Token      -- ^=
  | LessLessEqual       : Token      -- <<=
  | GreaterGreaterEqual : Token      -- >>=
  -- Chapter 6: if/else, ternary operator, goto (extra credit)
  | KwIf    : Token   -- if
  | KwElse  : Token   -- else
  | KwGoto  : Token   -- goto (extra credit)
  | Question : Token  -- ?
  | Colon    : Token  -- :
  -- Chapter 8: loop keywords, break, continue
  | KwWhile    : Token   -- while
  | KwDo       : Token   -- do
  | KwFor      : Token   -- for
  | KwBreak    : Token   -- break
  | KwContinue : Token   -- continue
  -- Chapter 8 extra credit: switch/case/default
  | KwSwitch   : Token   -- switch
  | KwCase     : Token   -- case
  | KwDefault  : Token   -- default
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
  | .Equal               => "\"=\""
  | .PlusPlus            => "\"+\""
  | .PlusEqual           => "\"+=\""
  | .MinusEqual          => "\"-=\""
  | .StarEqual           => "\"*=\""
  | .SlashEqual          => "\"/=\""
  | .PercentEqual        => "\"%=\""
  | .AmpEqual            => "\"&=\""
  | .PipeEqual           => "\"|=\""
  | .CaretEqual          => "\"^=\""
  | .LessLessEqual       => "\"<<=\""
  | .GreaterGreaterEqual => "\">>=\""
  | .KwIf    => "\"if\""
  | .KwElse  => "\"else\""
  | .KwGoto  => "\"goto\""
  | .Question => "\"?\""
  | .Colon    => "\":\""
  | .KwWhile    => "\"while\""
  | .KwDo       => "\"do\""
  | .KwFor      => "\"for\""
  | .KwBreak    => "\"break\""
  | .KwContinue => "\"continue\""
  | .KwSwitch   => "\"switch\""
  | .KwCase     => "\"case\""
  | .KwDefault  => "\"default\""

end Lexer
