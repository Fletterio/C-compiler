module Main where

import System.Environment (getArgs)
import System.Process (callProcess)
import System.FilePath (replaceExtension)
import System.Exit (exitSuccess, exitFailure)
import Control.Exception (finally)

preprocessCFile :: String -> IO String
preprocessCFile cFilePath = do
    let iFilePath = replaceExtension cFilePath "i"
    callProcess "gcc" ["-E", "-P", cFilePath, "-o", iFilePath]
    return iFilePath

compilePreprocessedCFile :: String -> IO String
compilePreprocessedCFile iFilePath = do
    let sFilePath = replaceExtension iFilePath "s"
    let compile = callProcess "gcc" ["-S", "-O", "-fno-asynchronous-unwind-tables", "-fcf-protection=none", iFilePath, "-o", sFilePath]
    compile `finally` callProcess "rm" [iFilePath]
    return sFilePath

assembleAndLink :: String -> IO ()
assembleAndLink sFilePath = do
    callProcess "gcc" [sFilePath, "-o", replaceExtension sFilePath ""]
    callProcess "rm" [sFilePath]

runCompilerDriver :: String -> IO ()
runCompilerDriver input = preprocessCFile input >>= compilePreprocessedCFile >>= assembleAndLink

main :: IO ()
main = do
    args <- getArgs
    let compilerArgs = parseArgs args
    case compilerArgs of
        Left err -> putStrLn err >> exitFailure
        Right (_, _, filename) ->
            if ".c" `isSuffixOf` filename
                then runCompilerDriver filename
                else putStrLn "Input file must have a .c extension." >> exitFailure
    where
    isSuffixOf :: Eq a => [a] -> [a] -> Bool
    isSuffixOf suf str = suf == reverse (take (length suf) (reverse str))

    -- Returns: (Maybe flag, S flag, filename)
    parseArgs :: [String] -> Either String (Maybe String, Bool, String)
    parseArgs [filename] = Right (Nothing, False, filename)
    parseArgs [flag, filename]
        | flag `elem` ["--lexer", "-l", "--parse", "-p", "--codegen", "-c"] = Right (Just flag, False, filename)
        | flag == "-S" = Right (Nothing, True, filename)
        | otherwise = Left "Unknown flag."
    parseArgs [flag1, flag2, filename]
        | flag1 == "-S" && flag2 `elem` ["--lexer", "-l", "--parse", "-p", "--codegen", "-c"] =
        Right (Just flag2, True, filename)
        | flag2 == "-S" && flag1 `elem` ["--lexer", "-l", "--parse", "-p", "--codegen", "-c"] =
        Right (Just flag1, True, filename)
        | otherwise = Left "Unknown flag combination."
    parseArgs _ = Left "Please provide an argument."
