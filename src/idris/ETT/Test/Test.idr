module ETT.Test.Test

import Data.String
import Data.AVL

import System.File.ReadWrite
import System

import Text.Parser.CharUtil
import Text.Parser.Fork

import ETT.Core.Language
import ETT.Core.Monad
import ETT.Core.Substitution
import ETT.Core.Unification

import ETT.Surface.SemanticToken
import ETT.Surface.Language
import ETT.Surface.ParserUtil
import ETT.Surface.Parser
import ETT.Surface.Elaboration

{- runAssistant : Signature -> M ()
runAssistant sig = M.do
  io $ putStrLn "Enter command:"
  input <- io $ getLine
  -- Skip empty lines:
  let False = input == ""
       | True => runAssistant sig
  -- Skip comments:
  let False = isPrefixOf "--" (trim input)
       | True => runAssistant sig
  io $ putStrLn "Processing: \{input}"
  case input /= "exit" of
    True => do
      let Right (st, transformation) = parseFull' (MkParsingSt [<]) transformation input
        | Left err => M.do
            io $ putStrLn (show err)
            runAssistant sig
      Right sig' <- try $ compute sig transformation
        | Left err => M.do
            io $ putStrLn err
            runAssistant sig
      io $ putStrLn "✔"
      runAssistant sig'
    False => M.do
      io $ putStrLn "Bye!"
      return ()

assistantApp : IO ()
assistantApp = do
   Right () <- eval (runAssistant [<]) ()
     | Left err => die err
   pure () -}

parserTestApp : IO ()
parserTestApp = do
   Right contents <- readFile "src/proto0/ParserTest.proto0"
     | Left err => die (show err)
   let Right (st, parsed) = parseFull' (MkParsingSt [<]) surfaceFile contents
     | Left err => die (show err)
   putStrLn "Parsed successfully!"

checkElabApp : IO ()
checkElabApp = do
   Right contents <- readFile "src/proto0/ElabTest.proto0"
     | Left err => die (show err)
   let Right (st, parsed) = parseFull' (MkParsingSt [<]) surfaceFile contents
     | Left err => die (show err)
   putStrLn "Parsed successfully!"
   Right (sig, omega) <- eval (elabFile [<] empty parsed) initialUnifySt
     | Left err => die err
   putStrLn "Checked successfully!"

main : IO ()
main = checkElabApp
