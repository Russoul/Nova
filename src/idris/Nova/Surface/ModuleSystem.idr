module Nova.Surface.ModuleSystem

import Me.Russoul.Data.Location
import Me.Russoul.Text.Lexer.Token

import Control.Monad.IOEither

import Data.AVL
import Data.Fin
import Data.String
import Data.SnocList

import System.File
import System.Path
import System

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Pretty
import Nova.Core.Substitution
import Nova.Core.Unification
import Nova.Core.Evaluation

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
-- ||| ε ⊦ ⟦?A, ?z, ?p, ?⟧ ⇝ _ : Commut-Monoid
public export
postProblem1 : SnocList Operator
            -> Signature
            -> Omega
            -> ElabM (Signature, Omega)
postProblem1 ops sig omega = M.do
  let syntm0 = "?A, ?z, ?p, ?"
  let syntm1 = "ℕ-Commut-Monoid"
  let synty =
    """
      (A : 𝕌)
         ⨯ (z : A)
         ⨯ (_+_ : A → A → A)
         ⨯ ((x : A) → z + x ≡ x ∈ A)
         ⨯ ((x : A) → x + z ≡ x ∈ A)
         ⨯ ((x y z : A) → x + (y + z) ≡ (x + y) + z ∈ A)
         ⨯ ((x y : A) → x + y ≡ y + x ∈ A)
    """
  let Right (_, syntm0) = parseFull' (MkParsingSt [<]) (term 0) syntm0
    | Left err => criticalError (show err)
  let Right (_, syntm1) = parseFull' (MkParsingSt [<]) (term 0) syntm1
    | Left err => criticalError (show err)
  let Right (_, synty) = parseFull' (MkParsingSt [<]) (term 0) synty
    | Left err => criticalError (show err)
  let params = MkParams Nothing {solveNamedHoles = True}
  (omega, tymidx) <- liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  let ty = Typ.OmegaVarElim tymidx Terminal
  (omega, midx0) <- liftUnifyM $ newElemMeta omega [<] ty SolveByElaboration
  (omega, midx1) <- liftUnifyM $ newElemMeta omega [<] ty SolveByElaboration
  let prob1 = TypeElaboration [<] !(Elab.liftM $ asCriticalError $ shunt (cast ops) synty 0) tymidx
  let prob2 = ElemElaboration [<] !(Elab.liftM $ asCriticalError $ shunt (cast ops) syntm0 0) midx0 ty
  let prob3 = ElemElaboration [<] !(Elab.liftM $ asCriticalError$ shunt (cast ops) syntm1 0) midx1 ty
  let el0 = OmegaVarElim midx0 Terminal
  let el1 = OmegaVarElim midx1 Terminal
  omega <- liftUnifyM $ addConstraint omega (ElemConstraint [<] el0 el1 ty)
  Success omega <- solve ops sig omega [prob1, prob2, prob3]
    | Stuck omega stuckElab stuckCons => M.do
         write "Result of postProblem1 (stuck):"
         write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] el0 0))
         criticalError $ renderDocTerm !(Elab.liftM $ pretty sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => criticalError $ renderDocTerm !(Elab.liftM $ pretty sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => criticalError $ renderDocTerm !(Elab.liftM $ pretty sig (UnificationError omega (con, err)))
  write "Result of postProblem1:"
  write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] el0 0))
  return (sig, omega)

public export
postProblem2 : SnocList Operator
            -> Signature
            -> Omega
            -> ElabM (Signature, Omega)
postProblem2 ops sig omega = M.do
  let Right (_, syntm) = parseFull' (MkParsingSt [<]) (term 0) "four"
    | Left err => criticalError (show err)
  let params = MkParams Nothing {solveNamedHoles = True}
  (omega, midx) <- liftUnifyM $ newElemMeta omega [<] NatTy SolveByElaboration
  let myResult = Elem.OmegaVarElim midx Terminal
  let prob1 = ElemElaboration [<] !(Elab.liftM $ asCriticalError $ shunt (cast ops) syntm 0) midx NatTy
  Success omega <- solve ops sig omega [prob1]
    | Stuck omega stuckElab stuckCons => criticalError $ renderDocTerm !(Elab.liftM $ pretty sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => criticalError $ renderDocTerm !(Elab.liftM $ pretty sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => criticalError $ renderDocTerm !(Elab.liftM $ pretty sig (UnificationError omega (con, err)))
  write "Result of postProblem2:"
  write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] !(Elab.liftM $ closedNormalise sig omega myResult) 0))
  return (sig, omega)

public export
checkModule : SnocList Operator
           -> Signature
           -> Omega
           -> (nextOmegaIdx : Nat)
           -> OrdTree (String, List (Range, String)) ByFst
           -> (novaDirectory : String)
           -> (modName : String)
           -> IO (Either (Maybe Range, Doc Ann) (SnocList Operator, Signature, Omega, Nat, OrdTree (String, List (Range, String)) ByFst, String, SnocList SemanticToken))
checkModule ops sig omega nextOmegaIdx namedHoles novaDirectory modName = Prelude.do
  let mod = novaDirectory </> (modName ++ ".nova")
  putStrLn "About to process file: \{mod}"
  Right source <- readFile mod
    | Left err => Prelude.do
        pure $ Left (Nothing, pretty $ "Can't read module: \{mod}; reason: \{show err}")
  let Right (MkParsingSt toks, surfaceSyntax) = parseFull' (MkParsingSt [<]) surfaceFile source
    | Left err => Prelude.do
        pure $ Left (Nothing, pretty $ "Parsing error:\n" ++ show err)
  putStrLn "File parsed successfully!"
  let params = MkParams (Just mod) {solveNamedHoles = False}
  Right (MkElabSt (MkUnifySt nextOmegaIdx) moreToks namedHoles, Right (ops, sig, omega)) <- run (elabFile @{params} ops sig omega surfaceSyntax) (MkElabSt (MkUnifySt nextOmegaIdx) [<] namedHoles)
    | Right (MkElabSt (MkUnifySt nextOmegaIdx) moreToks namedHoles, Left (x, range, sig, err)) => Prelude.do
       Right doc <- eval (pretty sig err) ()
         | Left err => Prelude.do
             pure $ Left (Just range, pretty ("Critical error:" ++ show err))
       pure (Left (Just range, pretty "Error while elaborating top-level definition (#\{show (length sig)}) \{x}" <+> hardline <+> doc))
    | Left err => Prelude.do
        pure $ Left (Nothing, pretty ("Critical error:" ++ show err))
  putStrLn "File elaborated successfully!"
  putStrLn "------------ Named holes ---------------"
  for_ (List.inorder omega) $ \(x, e) => Prelude.do
    case e of
      MetaType ctx NoSolve => Prelude.do
        Right doc <- eval (prettyOmegaEntry sig omega x e) ()
          | Left err => die (show err) -- Those should never fail
        putStrLn (renderDocTerm doc)
      MetaElem ctx ty NoSolve => Prelude.do
        Right doc <- eval (prettyOmegaEntry sig omega x e) ()
          | Left err => die (show err) -- Those should never fail
        putStrLn (renderDocTerm doc)
      _ => Prelude.do
        pure ()
  putStrLn "----------------------------------------"
  pure $ Right (ops, sig, omega, nextOmegaIdx, namedHoles, source, toks ++ moreToks)


public export
checkModules : SnocList Operator
            -> Signature
            -> Omega
            -> (nextOmegaIdx : Nat)
            -> OrdTree (String, List (Range, String)) ByFst
                  --   absolute filename   src     toks
            -> (toks : SnocList (String, String, SnocList SemanticToken))
            -> (novaDirectory : String)
            -> (modNames : List String)     --                                                                                  absolute filename   src     toks
            --             vvvvvvvvvvvv filename
            -> IO (Either (Maybe String, Maybe Range, Doc Ann) (SnocList Operator, Signature, Omega, Nat, OrdTree (String, List (Range, String)) ByFst, List (String, String, SnocList SemanticToken)))
checkModules ops sig omega nextOmegaIdx namedHoles toks novaDirectory [] = Prelude.do
  pure $ Right (ops, sig, omega, nextOmegaIdx, namedHoles, cast toks)
checkModules ops sig omega nextOmegaIdx namedHoles toks novaDirectory (n :: ns) = Prelude.do
  let mod = novaDirectory </> (n ++ ".nova")
  Right (ops, sig, omega, nextOmegaIdx, namedHoles, source, ntoks) <- checkModule ops sig omega nextOmegaIdx namedHoles novaDirectory n
    | Left (r, err) => Prelude.do
        pure (Left (Just mod, r, err))
  checkModules ops sig omega nextOmegaIdx namedHoles (toks :< (mod, source, ntoks)) novaDirectory ns

public export
checkEverything : SnocList Operator
               -> Signature
               -> Omega
               -> (nextOmegaIdx : Nat)
               -> OrdTree (String, List (Range, String)) ByFst
                     --   absolute filename   src     toks
               -> (toks : SnocList (String, String, SnocList SemanticToken))
               -> (novaDirectory : String)
               -> (modNames : List String)     --                                                                                  absolute filename   src     toks
               --             vvvvvvvvvvvv filename
               -> IO (Either (Maybe String, Maybe Range, Doc Ann) (SnocList Operator, Signature, Omega, Nat, OrdTree (String, List (Range, String)) ByFst, List (String, String, SnocList SemanticToken)))
checkEverything ops sig omega nextOmegaIdx namedHoles toks novaDirectory modNames = IOEither.do
  (ops, sig, omega, nextOmegaIdx, namedHoles, ntoks) <- checkModules ops sig omega nextOmegaIdx namedHoles toks novaDirectory modNames
  (MkElabSt (MkUnifySt nextOmegaIdx) moreToks namedHoles, (sig, omega)) <-
    map (bimap (\x => (Nothing, Nothing, pretty (show x))) id) (run (postProblem2 ops sig omega) (MkElabSt (MkUnifySt nextOmegaIdx) [<] namedHoles))
  pure (ops, sig, omega, nextOmegaIdx, namedHoles, ntoks)


