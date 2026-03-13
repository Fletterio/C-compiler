namespace Lexer

/-- A single token produced by the lexer. -/
inductive Token where
  | Identifier : String → Token  -- e.g. "main", "foo"
  | Constant      : Nat → Token   -- integer literal (no suffix), e.g. 2, 42
  | LongConstant  : Nat → Token   -- Chapter 11: integer literal with l/L suffix, e.g. 100L
  | UIntConstant  : Nat → Token   -- Chapter 12: unsigned int literal with u/U suffix, e.g. 42u
  | ULongConstant : Nat → Token   -- Chapter 12: unsigned long literal with ul/lu/UL/LU suffix
  | KwInt      : Token           -- int
  | KwLong     : Token           -- long  (Chapter 11)
  | KwUnsigned : Token           -- unsigned  (Chapter 12)
  | KwSigned   : Token           -- signed    (Chapter 12)
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
  -- Chapter 9: comma separator for argument lists and parameter lists
  | Comma      : Token   -- ,
  -- Chapter 10: storage-class specifiers
  | KwStatic   : Token   -- static
  | KwExtern   : Token   -- extern
  -- Chapter 13: double type keyword and floating-point constant
  | KwDouble       : Token           -- double
  | DoubleConstant : Float → Token   -- floating-point literal, e.g. 3.14
  deriving Repr, BEq

/-- Human-readable description of a token, used in parser error messages. -/
def Token.describe : Token → String
  | .Identifier s    => s!"identifier \"{s}\""
  | .Constant n       => s!"constant \"{n}\""
  | .LongConstant n   => s!"long constant \"{n}L\""    -- Chapter 11
  | .UIntConstant n   => s!"unsigned int constant \"{n}U\""   -- Chapter 12
  | .ULongConstant n  => s!"unsigned long constant \"{n}UL\"" -- Chapter 12
  | .KwInt           => "\"int\""
  | .KwLong          => "\"long\""                    -- Chapter 11
  | .KwUnsigned      => "\"unsigned\""                -- Chapter 12
  | .KwSigned        => "\"signed\""                  -- Chapter 12
  | .KwVoid          => "\"void\""
  | .KwReturn        => "\"return\""
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
  | .Comma      => "\",\""
  | .KwStatic      => "\"static\""
  | .KwExtern      => "\"extern\""
  | .KwDouble      => "\"double\""
  | .DoubleConstant f => s!"double constant \"{f}\""

end Lexer
