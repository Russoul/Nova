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
postProblem1 : Signature
            -> Omega
            -> SnocList Operator
            -> ElabM (Signature, Omega)
postProblem1 sig omega ops = M.do
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
    | Left err => throw (show err)
  let Right (_, syntm1) = parseFull' (MkParsingSt [<]) (term 0) syntm1
    | Left err => throw (show err)
  let Right (_, synty) = parseFull' (MkParsingSt [<]) (term 0) synty
    | Left err => throw (show err)
  let params = MkParams Nothing {solveNamedHoles = True}
  (omega, tymidx) <- liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  let ty = Typ.OmegaVarElim tymidx Terminal
  (omega, midx0) <- liftUnifyM $ newElemMeta omega [<] ty SolveByElaboration
  (omega, midx1) <- liftUnifyM $ newElemMeta omega [<] ty SolveByElaboration
  let prob1 = TypeElaboration [<] !(Elab.liftM $ shunt (cast ops) synty 0 >>= M.fromEither) tymidx
  let prob2 = ElemElaboration [<] !(Elab.liftM $ shunt (cast ops) syntm0 0 >>= M.fromEither) midx0 ty
  let prob3 = ElemElaboration [<] !(Elab.liftM $ shunt (cast ops) syntm1 0 >>= M.fromEither) midx1 ty
  let el0 = OmegaVarElim midx0 Terminal
  let el1 = OmegaVarElim midx1 Terminal
  omega <- liftUnifyM $ addConstraint omega (ElemConstraint [<] el0 el1 ty)
  Success omega <- solve sig omega [prob1, prob2, prob3]
    | Stuck omega stuckElab stuckCons => M.do
         write "Result of postProblem1 (stuck):"
         write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] el0 0))
         throw $ renderDocTerm !(Elab.liftM $ pretty sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (UnificationError omega (con, err)))
  write "Result of postProblem1:"
  write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] el0 0))
  return (sig, omega)

public export
postProblem2 : Signature
            -> Omega
            -> SnocList Operator
            -> ElabM (Signature, Omega)
postProblem2 sig omega ops = M.do
  let Right (_, syntm) = parseFull' (MkParsingSt [<]) (term 0) "four"
    | Left err => throw (show err)
  let params = MkParams Nothing {solveNamedHoles = True}
  (omega, midx) <- liftUnifyM $ newElemMeta omega [<] NatTy SolveByElaboration
  let myResult = Elem.OmegaVarElim midx Terminal
  let prob1 = ElemElaboration [<] !(Elab.liftM $ shunt (cast ops) syntm 0 >>= M.fromEither) midx NatTy
  Success omega <- solve sig omega [prob1]
    | Stuck omega stuckElab stuckCons => throw $ renderDocTerm !(Elab.liftM $ pretty sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (UnificationError omega (con, err)))
  write "Result of postProblem2:"
  write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] !(Elab.liftM $ closedNormalise sig omega myResult) 0))
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
    map (bimap (\x => (Nothing, Nothing, pretty x)) id) (run (postProblem2 sig omega ops) (MkElabSt (MkUnifySt nextOmegaIdx) [<] namedHoles))
  pure (sig, omega, ops, nextOmegaIdx, namedHoles, ntoks)


