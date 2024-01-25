module Nova.Surface.Elaboration.Implementation.Tactic.NormaliseCommutativeMonoid

import Data.AVL
import Data.Fin
import Data.List1
import Data.Location
import Data.SnocList
import Data.Util
import Data.Either

import Text.PrettyPrint.Prettyprinter
import Text.Lexing.Token

import Nova.Core.Context
import Nova.Core.Conversion
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Pretty
import Nova.Core.Substitution
import Nova.Core.Unification
import Nova.Core.Util
import Nova.Core.Inference

import Nova.Surface.Elaboration.Implementation.Tactic.TermLens
import Nova.Surface.Elaboration.Interface
import Nova.Surface.Elaboration.Pretty
import Nova.Surface.Language
import Nova.Surface.Operator
import Nova.Surface.Parser
import Nova.Surface.ParserGeneral
import Nova.Surface.SemanticToken
import Nova.Surface.Shunting

import Solver.CommutativeMonoid

||| ε ⊦ T type
||| x̄
||| ----------
||| ⟦x̄⟧ T ctx
public export
interpContext : SnocList String -> Typ -> Context
interpContext [<] ty = [<]
interpContext (xs :< x) ty = interpContext xs ty :< (x, ty)

||| Given x̄ and a (Γ ctx) try constructing σ : Γ ⇒ ⟦x̄⟧ T
public export
mbSubst : Signature -> Omega -> Context -> SnocList String -> Typ -> M (Maybe SubstContext)
mbSubst sig omega ctx [<] ty = MMaybe.do return Terminal
mbSubst sig omega ctx (xs :< x) ty0 = MMaybe.do
  sigma <- mbSubst sig omega ctx xs ty0
  (tm, ty) <- fromMaybe $ lookupContext ctx x
  True <- liftM $ conv sig omega ty0 ty
    | _ => nothing
  return (Ext sigma tm)

||| ε ⊦ M type
||| ε ⊦ 0 : M
||| ε ⊦ _+_ : M → M → M
||| (M, 0, _+_) forms a commutative monoid
||| x̄ ⊦ e
||| ---------------
||| ⟦x̄⟧ M ⊦ ⟦e⟧ (M, 0, _+_) : M
||| (⟦x̄₀⟧ M) (x : M) (⟦x̄₁⟧ M) ⊦ ⟦x⟧ (M, 0, _+_) = x : M
||| ⟦x̄⟧ M ⊦ ⟦Zero⟧ (M, 0, _+_) = 0 : M
||| ⟦x̄⟧ M ⊦ ⟦Plus p q⟧ (M, 0, _+_) = ⟦p⟧ (M, 0, _+_) + ⟦q⟧ (M, 0, _+_) : M
public export
interpTerm : Signature -> Typ -> Elem -> Elem -> Term (Fin n) -> M Elem
interpTerm sig ty zero plus (Var x) = return $ ContextVarElim (finToNat x)
interpTerm sig ty zero plus Zero = return zero
interpTerm sig ty zero plus (Plus a b) = M.do
  a <- interpTerm sig ty zero plus a
  b <- interpTerm sig ty zero plus b
  -- ((_+_ : ℕ → ℕ → ℕ) a : ℕ → ℕ) b
  return $
    PiElim
      (PiElim plus "_" ty (funTy ty ty) a)
      "_"
      ty
      ty
      b

||| Assumes Σ Ω Γ ⊦ t : ℕ
||| And t is head-neutral w.r.t. evaluation
||| Parses a term of the form:
||| t ::= 0 | t + t | x
-- Is it possible to generalise this to arbitrary comm monoid?
public export
parseNatCommutativeMonoidNu : (plusIndex : Nat) -> (Nat -> Maybe (Fin n)) -> Elem -> M (Maybe (Term (Either Nat (Fin n))))
parseNatCommutativeMonoidNu plusIndex f NatVal0 = MMaybe.do
  return Zero
parseNatCommutativeMonoidNu plusIndex f (ContextVarElim k) = MMaybe.do
  let Just k = f k
    | Nothing => assert_total $ idris_crash "parseNatCommutativeMonoidNu"
  return (Var (Right k))
parseNatCommutativeMonoidNu plusIndex f (PiElim (PiElim (SignatureVarElim i _) _ _ _ a) _ _ _ b) = MMaybe.do
  guard (i == plusIndex)
  a <- parseNatCommutativeMonoidNu plusIndex f a
  b <- parseNatCommutativeMonoidNu plusIndex f b
  return (Plus a b)
parseNatCommutativeMonoidNu plusIndex f el = MMaybe.do
  nothing

||| Σ₀ ⊦ ? ⇛ Σ (Γ ⊦ x : A)
public export
elabNormaliseComm : Params
                 => SnocList Operator
                 -> Signature
                 -> Omega
                 -> Range
                 -> OpFreeTerm
                 -> (vars : SnocList String ** Term (Fin (length vars)))
                 -> OpFreeTerm
                 -> Signature
                 -> ElabM (Either (Range, Doc Ann) (Omega, Signature, SignatureInst -> SignatureInst))
elabNormaliseComm ops sig omega r path (vars ** monoidTm) monoidInst (target :< (x, ElemEntry ctx ty)) = MEither.do
  MkLens focusedR focusedCtx (Right (focused, setFocused)) <- Elab.liftM $ Typ.lens sig omega ctx ty path
    | _ => error (r, "Wrong focused term for 'normalise-commut-monoid'")
  focusedTy <- MEither.liftM $ Elab.liftM $ infer sig omega focusedCtx focused

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
  let Right (_, synty) = parseFull' (MkParsingSt [<]) (term 0) synty
    | Left err => throw (show err)
  (omega, tymidx) <- MEither.liftM $ liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  let commMonoidTy = Typ.OmegaVarElim tymidx Terminal
  let prob1 = TypeElaboration [<] !(MEither.liftM $ Elab.liftM $ shunt (cast ops) synty 0 `M.(>>=)` M.fromEither) tymidx
  Success omega <- MEither.liftM $ solve @{MkParams Nothing {solveNamedHoles = False}} ops sig omega [prob1]
    | Stuck omega stuckElab stuckCons => M.do
         write "(Unexpected error) Result elaborating expected monoid type in elabNormaliseComm (stuck):"
         write (renderDocTerm !(Elab.liftM $ prettyTyp sig omega [<] commMonoidTy 0))
         throw $ renderDocTerm !(Elab.liftM $ pretty sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (UnificationError omega (con, err)))


  (omega, monoidInstIdx) <- MEither.liftM $ liftUnifyM $ newElemMeta omega [<] commMonoidTy SolveByElaboration
  let monoidInstTm = Elem.OmegaVarElim monoidInstIdx Terminal
  let prob1 = ElemElaboration [<] monoidInst monoidInstIdx commMonoidTy
  Success omega <- MEither.liftM $ solve ops sig omega [prob1]
    | Stuck omega stuckElab stuckCons => M.do
         write "Result elaborating monoid type in elabNormaliseComm (stuck):"
         write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] monoidInstTm 0))
         throw $ renderDocTerm !(Elab.liftM $ pretty sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (UnificationError omega (con, err)))


  -- FIX: names must be unique every time
  let syntm0 = "?A, ?z, ?p, ?"
  let Right (_, syntm0) = parseFull' (MkParsingSt [<]) (term 0) syntm0
    | Left err => throw (show err)
  (omega, midx0) <- MEither.liftM $ liftUnifyM $ newElemMeta omega [<] commMonoidTy SolveByElaboration
  let prob2 = ElemElaboration [<] !(MEither.liftM $ Elab.liftM $ shunt (cast ops) syntm0 0 `M.(>>=)` M.fromEither) midx0 commMonoidTy
  let el0 = OmegaVarElim midx0 Terminal
  omega <- MEither.liftM $ liftUnifyM $ addConstraint omega (ElemConstraint [<] el0 monoidInstTm commMonoidTy)
  Success omega <- MEither.liftM $ solve @{MkParams Nothing {solveNamedHoles = True}} ops sig omega [prob2]
    | Stuck omega stuckElab stuckCons => M.do
         write "Result of postProblem1 (stuck):"
         write (renderDocTerm !(Elab.liftM $ prettyElem sig omega [<] el0 0))
         throw $ renderDocTerm !(Elab.liftM $ pretty sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => throw $ renderDocTerm !(Elab.liftM $ pretty sig (UnificationError omega (con, err)))
  let monoidTy = El (Elem.OmegaVarElim "A" Terminal)
  let monoidZero = Elem.OmegaVarElim "z" Terminal
  let monoidPlus = Elem.OmegaVarElim "p" Terminal
  subst <- mapResult (maybeToEither (r, "Can't find the given monoid variables in the context")) $
          Elab.liftM $ mbSubst sig omega focusedCtx vars monoidTy
  tmInterp <- MEither.liftM $ Elab.liftM $ interpTerm sig monoidTy monoidZero monoidPlus monoidTm
  omega <- MEither.liftM $ liftUnifyM $ addConstraint omega (TypeConstraint focusedCtx focusedTy monoidTy)
  omega <- MEither.liftM $ liftUnifyM $ addConstraint omega (ElemConstraint focusedCtx (ContextSubstElim tmInterp subst) focused monoidTy)
  Success omega <- MEither.liftM $ liftUnifyM $ Unification.solve sig omega
    | _ => error (r, "Failed to solve unification constraints")
  let monoidTm' = normaliseAlg monoidTm
  MEither.liftM $ write "Original monoid term: \{renderDocNoAnn {ann = Unit} $ CommutativeMonoid.Language.prettyTerm vars monoidTm}"
  MEither.liftM $ write "Normalised monoid term: \{renderDocNoAnn {ann = Unit} $ CommutativeMonoid.Language.prettyTerm vars monoidTm'}"
  tmInterp' <- MEither.liftM $ Elab.liftM $ interpTerm sig monoidTy monoidZero monoidPlus monoidTm'
  let ty' = setFocused (ContextSubstElim tmInterp' subst)
  return (omega, target :< (x, ElemEntry ctx ty'), id)
elabNormaliseComm ops sig omega r path monoidTm monoidInst _ = MEither.do
  error (r, "Wrong context for tactic 'normalise-commmut-monoid'")
