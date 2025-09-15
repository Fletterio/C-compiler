module Main where

import Driver.Driver (runCompilerDriver)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Data.List (isSuffixOf)

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

    -- Returns: (Maybe flag, S flag, filename)
    where
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
