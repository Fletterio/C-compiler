{
-- At the top of the file, we define the module and its imports, similarly to Haskell.
module Lexer.Lexer
  ( -- * Invoking Alex
    Alex
  , AlexPosn (..)
  , alexGetInput
  , alexError
  , runAlex
  , alexMonadScan
  , lexProgram

  , Range (..)
  , RangedToken (..)
  , Token (..)
  ) where

import Data.ByteString.Lazy.Char8 (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
}
-- In the middle, we insert our definitions for the lexer, which will generate the lexemes for our grammar.
%wrapper "monadUserState-bytestring"

$digit = [0-9]
$lower = [a-z]
$upper = [A-Z]
$alpha = [A-Za-z]
$alphanum = [A-Za-z0-9]
$word = [A-Za-z0-9_]

-- Forbidden regexes
@numbersFollowedByWords = $digit+ $word+


-- Identifiers - trailing boundary dropped for now
@identifier = ($alpha | \_) $word*--\b  --[a-zA-Z_]\w*\b
-- Constants
@constant = ($digit)+
-- Keywords
@int = int
@void = void
@return = return
@lparen = \(
@rparen = \)
@lbrace = \{
@rbrace = \}
@semicolon = \;

tokens :-

<0> $white+ ;

-- Forbidden patterns
<0> @numbersFollowedByWords { \(_, _, str, _) len -> alexError ("Invalid constant: " ++ (BS.unpack $ BS.take len str)) }

<0> @constant   { tokenConstant }
<0> @int        { tokenInt }
<0> @void       { tokenVoid }
<0> @return     { tokenReturn }
<0> @lparen     { tokenLParen }
<0> @rparen     { tokenRParen }
<0> @lbrace     { tokenLBrace }
<0> @rbrace     { tokenRBrace }
<0> @semicolon  { tokenSemicolon }
<0> @identifier { tokenIdentifier }

{
-- At the bottom, we may insert more Haskell definitions, such as data structures, auxiliary functions, etc.
data AlexUserState = AlexUserState
  {
  }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState

alexEOF :: Alex RangedToken
alexEOF = do
  (pos, _, _, _) <- alexGetInput
  pure $ RangedToken EOF (Range pos pos)

data Range = Range
  { start :: AlexPosn
  , stop :: AlexPosn
  } deriving (Eq, Show)

data RangedToken = RangedToken
  { rtToken :: Token
  , rtRange :: Range
  } deriving (Eq, Show)

data Token
  -- Identifiers
  = Identifier ByteString
  -- Constants
  | Constant Int64
  -- Keywords
  | Int
  | Void
  | Return
  -- Parenthesis
  | LParen
  | RParen
  -- Braces
  | LBrace
  | RBrace
  -- Semicolon
  | Semicolon  
  -- EOF
  | EOF
  deriving (Eq, Show)

mkRange :: AlexInput -> Int64 -> Range
mkRange (start, _, str, _) len = Range{start = start, stop = stop}
  where
  stop = BS.foldl' alexMove start $ BS.take len str

-- Tokenizers

-- Errors

-- Valid tokens

tokenIdentifier :: AlexAction RangedToken
tokenIdentifier inp@(_, _, str, _) len =
  pure RangedToken
  { rtToken = Identifier $ BS.take len str
  , rtRange = mkRange inp len
  }

tokenConstant :: AlexAction RangedToken
tokenConstant inp@(_, _, str, _) len =
  pure RangedToken
  { rtToken = Constant $ read $ BS.unpack $ BS.take len str
  , rtRange = mkRange inp len
  }

tokenInt :: AlexAction RangedToken
tokenInt = \inp len -> pure RangedToken { rtToken = Int, rtRange = mkRange inp len }

tokenVoid :: AlexAction RangedToken
tokenVoid = \inp len -> pure RangedToken { rtToken = Void, rtRange = mkRange inp len }

tokenReturn :: AlexAction RangedToken
tokenReturn = \inp len -> pure RangedToken { rtToken = Return, rtRange = mkRange inp len }

tokenLParen :: AlexAction RangedToken
tokenLParen = \inp len -> pure RangedToken { rtToken = LParen, rtRange = mkRange inp len }

tokenRParen :: AlexAction RangedToken
tokenRParen = \inp len -> pure RangedToken { rtToken = RParen, rtRange = mkRange inp len }

tokenLBrace :: AlexAction RangedToken
tokenLBrace = \inp len -> pure RangedToken { rtToken = LBrace, rtRange = mkRange inp len }

tokenRBrace :: AlexAction RangedToken
tokenRBrace = \inp len -> pure RangedToken { rtToken = RBrace, rtRange = mkRange inp len }

tokenSemicolon :: AlexAction RangedToken
tokenSemicolon = \inp len -> pure RangedToken { rtToken = Semicolon, rtRange = mkRange inp len }

scanMany :: ByteString -> Either String [RangedToken]
scanMany input = runAlex input go
  where
    go = do
      output <- alexMonadScan
      if rtToken output == EOF
        then pure [output]
        else (output :) <$> go

lexProgram :: ByteString -> Either String [Token]
lexProgram input = fmap (map rtToken) $ scanMany input
}
