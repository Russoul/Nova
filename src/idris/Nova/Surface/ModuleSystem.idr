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
           -> UnifySt
           -> (novaDirectory : String)
           -> (modName : String)
           -> IO (Signature, Omega, SnocList Operator, UnifySt, SnocList SemanticToken)
checkModule sig omega ops unifySt novaDirectory modName = Prelude.do
  let mod = novaDirectory </> (modName ++ ".nova")
  putStrLn "About to process file: \{mod}"
  Right source <- readFile mod
    | Left err => die "Can't read module: \{mod}; reason: \{show err}"
  let Right (MkParsingSt toks, surfaceSyntax) = parseFull' (MkParsingSt [<]) surfaceFile source
    | Left err => die ("Parsing error:\n" ++ show err)
  putStrLn "File parsed successfully!"
  Right (unifySt, sig, omega, ops) <- run (elabFile sig omega ops surfaceSyntax) unifySt
    | Left err => die ("Elaboration error:\n" ++ err)
  putStrLn "File elaborated successfully!"
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
      _ => Prelude.do
        pure ()
  putStrLn "----------------------------------------"
  pure (sig, omega, ops, unifySt, toks)


public export
checkModules : Signature
            -> Omega
            -> SnocList Operator
            -> UnifySt
            -> (toks : OrdTree (String, SnocList SemanticToken) ByFst)
            -> (novaDirectory : String)
            -> (modNames : List String)
            -> IO (Signature, Omega, SnocList Operator, UnifySt, OrdTree (String, SnocList SemanticToken) ByFst)
checkModules sig omega ops unifySt toks novaDirectory [] = pure (sig, omega, ops, unifySt, toks)
checkModules sig omega ops unifySt toks novaDirectory (n :: ns) = Prelude.do
  (sig, omega, ops, unifySt, ntoks) <- checkModule sig omega ops unifySt novaDirectory n
  checkModules sig omega ops unifySt (insert (n, ntoks) toks) novaDirectory ns

