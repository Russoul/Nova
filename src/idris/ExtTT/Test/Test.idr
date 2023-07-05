module ExtTT.Test.Test

import Control.Monad.FailSt

import System.File.ReadWrite
import System

import Text.Parser.CharUtil
import Text.Parser.Fork

import ExtTT.Core.Language
import ExtTT.Core.Substitution
import ExtTT.Core.Assistant

import ExtTT.Surface.SemanticToken
import ExtTT.Surface.Language
import ExtTT.Surface.ParserUtil
import ExtTT.Surface.Parser
import ExtTT.Surface.Check

runAssistant : Signature -> M ()
runAssistant sig = FailSt.do
  io $ putStrLn "Enter command:"
  input <- io $ getLine
  case input /= "exit" of
    True => do
      let Right (st, transformation) = parseFull' (MkParsingSt [<]) transformation input
        | Left err => FailSt.do
            io $ putStrLn (show err)
            runAssistant sig
      sig' <- compute sig transformation
      runAssistant sig'
    False => FailSt.do
      io $ putStrLn "Bye!"
      return ()

main : IO ()
main = do
   Right contents <- readFile "src/proto0/ParserTest.proto0"
     | Left err => die (show err)
   let Right (st, parsed) = parseFull' (MkParsingSt [<]) surfaceFile contents
     | Left err => die (show err)
   putStrLn "Parsed successfully!"
   {- Right sig <- eval (checkFile Empty parsed) ()
     | Left err => die err
   putStrLn "Checked successfully!" -}
   Right () <- eval (runAssistant Empty) ()
     | Left err => die err
   pure ()

