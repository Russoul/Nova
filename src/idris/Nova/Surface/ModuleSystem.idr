module Nova.Surface.ModuleSystem

import Data.AVL
import Data.Fin
import Data.Location
import Data.String
import Data.SnocList

import System.File
import System.Path
import System

import Text.Lexing.Token
import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Pretty
import Nova.Core.Substitution
import Nova.Core.Unification

import Nova.Surface.Shunting
import Nova.Surface.Elaboration
import Nova.Surface.Language
import Nova.Surface.Operator
import Nova.Surface.Parser
import Nova.Surface.ParserGeneral
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

-- ||| For common Σ Ω:
-- ||| ε ⊦ ⟦?A, ?z, ?p, ?⟧ ⇝ _ : Comm-Monoid
public export
postProblem1 : Signature
            -> Omega
            -> SnocList Operator
            -> ElabM (Signature, Omega)
postProblem1 sig omega ops = M.do
  let tm = "?A, ?z, ?p, ?"
  let Right (_, tm) = parseFull' (MkParsingSt [<]) (term 0) tm
    | Left err => throw (show err)
  let params = MkParams Nothing {solveNamedHoles = True}
  commMonoidTy <- Elab.liftM $
    lookupSignatureIdxE sig "Comm-Monoid" `M.(<&>)` (\idx => Typ.SignatureVarElim idx Terminal)
  (omega, midx) <- liftUnifyM $ newElemMeta omega [<] commMonoidTy SolveByElaboration
  let prob = ElemElaboration [<] !(Elab.liftM $ shunt (cast ops) tm 0 >>= M.fromEither) midx commMonoidTy
  Success omega <- solve sig omega [prob]
    | _ => throw "postProblem1: Couldn't elaborate the term"
  write "Result of postProblem1:"
  write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] (OmegaVarElim midx Terminal) 0))
  return (sig, omega)

public export
checkModule : Signature
           -> Omega
           -> SnocList Operator
           -> (nextOmegaIdx : Nat)
           -> OrdTree (String, List (Range, String)) ByFst
           -> (novaDirectory : String)
           -> (modName : String)
           -> IO (Either (Maybe Range, Doc Ann) (Signature, Omega, SnocList Operator, Nat, OrdTree (String, List (Range, String)) ByFst, String, SnocList SemanticToken))
checkModule sig omega ops nextOmegaIdx namedHoles novaDirectory modName = Prelude.do
  let mod = novaDirectory </> (modName ++ ".nova")
  putStrLn "About to process file: \{mod}"
  Right source <- readFile mod
    | Left err => pure $ Left (Nothing, pretty $ "Can't read module: \{mod}; reason: \{show err}")
  let Right (MkParsingSt toks, surfaceSyntax) = parseFull' (MkParsingSt [<]) surfaceFile source
    | Left err => pure $ Left (Nothing, pretty $ "Parsing error:\n" ++ show err)
  putStrLn "File parsed successfully!"
  let params = MkParams (Just mod) {solveNamedHoles = False}
  Right (MkElabSt (MkUnifySt nextOmegaIdx) moreToks namedHoles, Right (sig, omega, ops)) <- run (elabFile @{params} sig omega ops surfaceSyntax) (MkElabSt (MkUnifySt nextOmegaIdx) [<] namedHoles)
    | Right (MkElabSt (MkUnifySt nextOmegaIdx) moreToks namedHoles, Left (x, range, sig, err)) => Prelude.do
       Right doc <- eval (pretty sig err) ()
         | Left err => pure $ Left (Just range, pretty ("Critical error:" ++ err))
       pure (Left (Just range, pretty "Error while elaborating top-level definition (#\{show (length sig)}) \{x}" <+> hardline <+> doc))
    | Left err => pure $ Left (Nothing, pretty ("Critical error:" ++ err))
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
  pure $ Right (sig, omega, ops, nextOmegaIdx, namedHoles, source, toks ++ moreToks)


public export
checkModules : Signature
            -> Omega
            -> SnocList Operator
            -> (nextOmegaIdx : Nat)
            -> OrdTree (String, List (Range, String)) ByFst
                  --   absolute filename   src     toks
            -> (toks : SnocList (String, String, SnocList SemanticToken))
            -> (novaDirectory : String)
            -> (modNames : List String)     --                                                                                  absolute filename   src     toks
            --             vvvvvvvvvvvv filename
            -> IO (Either (Maybe String, Maybe Range, Doc Ann) (Signature, Omega, SnocList Operator, Nat, OrdTree (String, List (Range, String)) ByFst, List (String, String, SnocList SemanticToken)))
checkModules sig omega ops nextOmegaIdx namedHoles toks novaDirectory [] = pure $ Right (sig, omega, ops, nextOmegaIdx, namedHoles, cast toks)
checkModules sig omega ops nextOmegaIdx namedHoles toks novaDirectory (n :: ns) = Prelude.do
  let mod = novaDirectory </> (n ++ ".nova")
  Right (sig, omega, ops, nextOmegaIdx, namedHoles, source, ntoks) <- checkModule sig omega ops nextOmegaIdx namedHoles novaDirectory n
    | Left (r, err) => pure (Left (Just mod, r, err))
  checkModules sig omega ops nextOmegaIdx namedHoles (toks :< (mod, source, ntoks)) novaDirectory ns

namespace IOEither
  public export
  (>>=) : IO (Either e a) -> (a -> IO (Either e b)) -> IO (Either e b)
  (f >>= g) = Prelude.do
    case !f of
      Left e => io_pure (Left e)
      Right x => g x

  public export
  pure : a -> IO (Either e a)
  pure x = io_pure (Right x)

public export
checkEverything : Signature
               -> Omega
               -> SnocList Operator
               -> (nextOmegaIdx : Nat)
               -> OrdTree (String, List (Range, String)) ByFst
                     --   absolute filename   src     toks
               -> (toks : SnocList (String, String, SnocList SemanticToken))
               -> (novaDirectory : String)
               -> (modNames : List String)     --                                                                                  absolute filename   src     toks
               --             vvvvvvvvvvvv filename
               -> IO (Either (Maybe String, Maybe Range, Doc Ann) (Signature, Omega, SnocList Operator, Nat, OrdTree (String, List (Range, String)) ByFst, List (String, String, SnocList SemanticToken)))
checkEverything sig omega ops nextOmegaIdx namedHoles toks novaDirectory modNames = IOEither.do
  (sig, omega, ops, nextOmegaIdx, namedHoles, ntoks) <- checkModules sig omega ops nextOmegaIdx namedHoles toks novaDirectory modNames
  (MkElabSt (MkUnifySt nextOmegaIdx) moreToks namedHoles, (sig, omega)) <-
    map (bimap (\x => (Nothing, Nothing, pretty x)) id) (run (postProblem1 sig omega ops) (MkElabSt (MkUnifySt nextOmegaIdx) [<] namedHoles))
  pure (sig, omega, ops, nextOmegaIdx, namedHoles, ntoks)

