module Nova.Test.Test

import Data.String
import Data.AVL

import System.File.ReadWrite
import System

import Text.Parser.CharUtil
import Text.Parser.Fork

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Substitution
import Nova.Core.Unification
import Nova.Core.Pretty

import Nova.Surface.SemanticToken
import Nova.Surface.Language
import Nova.Surface.ParserUtil
import Nova.Surface.Parser
import Nova.Surface.Elaboration
import Nova.Surface.Operator

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
   Right (sig, omega) <- eval (elabFile [<] empty [<] parsed) initialUnifySt
     | Left err => die err
   putStrLn "------------ Named holes ---------------"
   for_ (List.inorder omega) $ \(x, e) => Prelude.do
     case e of
       MetaType ctx NoSolve => Prelude.do
         Right doc <- eval (prettyOmegaEntry sig omega x e) ()
           | Left err => die err
         putStrLn (renderDocTerm doc)
       MetaElem ctx ty NoSolve => Prelude.do
         Right doc <- eval (prettyOmegaEntry sig omega x e) ()
           | Left err => die err
         putStrLn (renderDocTerm doc)
       _ => pure ()
   putStrLn "----------------------------------------"
   putStrLn "Checked successfully!"

main : IO ()
main = checkElabApp
