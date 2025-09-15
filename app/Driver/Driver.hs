module Driver.Driver where

import System.Process (callProcess)
import System.FilePath (replaceExtension)
import Control.Exception (finally)
import qualified Data.ByteString.Lazy as BL
import Lexer.Lexer (lexProgram, Token)

-- Used to stream file to lexer
readFileAsByteString :: FilePath -> IO BL.ByteString
readFileAsByteString path = BL.readFile path

preprocessCFile :: String -> IO String
preprocessCFile cFilePath = do
    let iFilePath = replaceExtension cFilePath "i"
    callProcess "gcc" ["-E", "-P", cFilePath, "-o", iFilePath]
    return iFilePath

compilePreprocessedCFile :: String -> IO (Either String [Token]) -- IO String
compilePreprocessedCFile iFilePath = do
    input <- readFileAsByteString iFilePath
    let tokensOrError = lexProgram input
    return tokensOrError
{-
    let sFilePath = replaceExtension iFilePath "s"
    let compile = callProcess "gcc" ["-S", "-O", "-fno-asynchronous-unwind-tables", "-fcf-protection=none", iFilePath, "-o", sFilePath]
    compile `finally` callProcess "rm" [iFilePath]
    return sFilePath
-}
assembleAndLink :: String -> IO ()
assembleAndLink sFilePath = do
    callProcess "gcc" [sFilePath, "-o", replaceExtension sFilePath ""]
    callProcess "rm" [sFilePath]

runCompilerDriver :: String -> IO ()
runCompilerDriver input = preprocessCFile input >>= compilePreprocessedCFile >>= \result -> putStrLn (show result) -- >>= assembleAndLink