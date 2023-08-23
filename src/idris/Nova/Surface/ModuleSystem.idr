module Nova.Surface.ModuleSystem

import Data.String
import Data.AVL
import Data.Location

import System.File
import System.Path
import System

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Substitution
import Nova.Core.Unification
import Nova.Core.Pretty

import Nova.Surface.Elaboration
import Nova.Surface.Language
import Nova.Surface.Operator
import Nova.Surface.Parser
import Nova.Surface.ParserUtil
import Nova.Surface.SemanticToken

||| A string is said to be a dash break if
||| it contains at least 3 symbols and each symbol is a dash '-'.
isDashBreak : String -> Bool
isDashBreak str = length str >= 3 && all (== '-') (unpack str)

isComment : String -> Bool
isComment str = isPrefixOf "--" str && not (isPrefixOf "---" str)

||| Reads an .npkg file, where
||| every line is a file name without extension ('--' comments are supported)
public export
readModuleDescription : (filename : String) -> IO (Maybe (List String))
readModuleDescription npkg = do
  Right content <- readFile npkg
    | Left err => pure Nothing
  let ls = lines content
  let ls = filter (not . isComment) ls
  pure (Just ls)

public export
checkModule : Signature
           -> Omega
           -> SnocList Operator
           -> (nextOmegaIdx : Nat)
           -> (novaDirectory : String)
           -> (modName : String)
           -> IO (Either String (Signature, Omega, SnocList Operator, Nat, String, SnocList SemanticToken))
checkModule sig omega ops nextOmegaIdx novaDirectory modName = Prelude.do
  let mod = novaDirectory </> (modName ++ ".nova")
  putStrLn "About to process file: \{mod}"
  Right source <- readFile mod
    | Left err => pure $ Left "Can't read module: \{mod}; reason: \{show err}"
  let Right (MkParsingSt toks, surfaceSyntax) = parseFull' (MkParsingSt [<]) surfaceFile source
    | Left err => pure $ Left ("Parsing error:\n" ++ show err)
  putStrLn "File parsed successfully!"
  Right (MkUnifySt nextOmegaIdx moreToks, sig, omega, ops) <- run (elabFile sig omega ops surfaceSyntax) (MkUnifySt nextOmegaIdx [<])
    | Left err => pure $ Left ("Elaboration error:\n" ++ err)
  putStrLn "File elaborated successfully!"
  putStrLn "------------ Named holes ---------------"
  for_ (List.inorder omega) $ \(x, e) => Prelude.do
    case e of
      MetaType ctx NoSolve => Prelude.do
        Right doc <- eval (prettyOmegaEntry sig omega x e) ()
          | Left err => die err -- Those should never fail
        putStrLn (renderDocTerm doc)
      MetaElem ctx ty NoSolve => Prelude.do
        Right doc <- eval (prettyOmegaEntry sig omega x e) ()
          | Left err => die err -- Those should never fail
        putStrLn (renderDocTerm doc)
      _ => Prelude.do
        pure ()
  putStrLn "----------------------------------------"
  pure $ Right (sig, omega, ops, nextOmegaIdx, source, toks ++ moreToks)


public export
checkModules : Signature
            -> Omega
            -> SnocList Operator
            -> (nextOmegaIdx : Nat) --   absolute filename   src     toks
            -> (toks : SnocList (String, String, SnocList SemanticToken))
            -> (novaDirectory : String)
            -> (modNames : List String)     --                                  absolute filename   src     toks
            -> IO (Either String (Signature, Omega, SnocList Operator, Nat, List (String, String, SnocList SemanticToken)))
checkModules sig omega ops nextOmegaIdx toks novaDirectory [] = pure $ Right (sig, omega, ops, nextOmegaIdx, cast toks)
checkModules sig omega ops nextOmegaIdx toks novaDirectory (n :: ns) = Prelude.do
  Right (sig, omega, ops, nextOmegaIdx, source, ntoks) <- checkModule sig omega ops nextOmegaIdx novaDirectory n
    | Left err => pure (Left err)
  let mod = novaDirectory </> (n ++ ".nova")
  checkModules sig omega ops nextOmegaIdx (toks :< (mod, source, ntoks)) novaDirectory ns

