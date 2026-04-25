module Nova.Surface.Elaboration.Implementation.Tactic.NormaliseCommutativeMonoid

import Me.Russoul.Data.Location
import Me.Russoul.Text.Lexer.Token

import Nova.Control.Monad.Id
import Nova.Control.Monad.St
import Nova.Control.Monad.StEither

import Data.AVL
import Data.Fin
import Data.List1
import Data.SnocList
import Data.Util
import Data.Either

import Text.PrettyPrint.Prettyprinter

import Nova.Core.Context
import Nova.Core.Conversion
import Nova.Core.Evaluation
import Nova.Core.Language
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
mbSubst : Signature -> Omega -> Context -> SnocList String -> Typ -> Maybe SubstContext
mbSubst sig omega ctx [<] ty = Just Terminal
mbSubst sig omega ctx (xs :< x) ty0 = Prelude.do
  sigma <- mbSubst sig omega ctx xs ty0
  (tm, ty) <- lookupContext ctx x
  guard $ conv sig omega ty0 ty
  pure (Ext sigma tm)

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
interpTerm : Signature -> Typ -> Elem -> Elem -> Term (Fin n) -> Id Elem
interpTerm sig ty zero plus (Var x) = Id.pure $ ContextVarElim (finToNat x)
interpTerm sig ty zero plus Zero = Id.pure zero
interpTerm sig ty zero plus (Plus a b) = Id.do
  a <- interpTerm sig ty zero plus a
  b <- interpTerm sig ty zero plus b
  -- ((_+_ : ℕ → ℕ → ℕ) a : ℕ → ℕ) b
  pure $
    PiElim
      (PiElim plus "_" ty (funTy ty ty) a)
      "_"
      ty
      ty
      b

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
                 -> StEither (Range, Doc Ann) ElabSt (Omega, Signature, SignatureInst -> SignatureInst)
elabNormaliseComm ops sig omega r path (vars ** monoidTm) monoidInst (target :< (x, ElemEntry ctx ty)) = StEither.do
  MkLens focusedR focusedCtx (Right (focused, setFocused)) <- fromEither $ Typ.lens sig omega ctx ty path
    | _ => throw (r, "Wrong focused term for 'normalise-commut-monoid'")
  focusedTy <- liftId $ infer sig omega focusedCtx focused

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
    | Left err => assert_total $ idris_crash (show err)
  (omega, tymidx) <- liftSt $ liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  let commMonoidTy = Typ.OmegaVarElim tymidx Terminal
  let prob1 = TypeElaboration [<] !(StEither.mapError (\x => (r, pretty x)) $ StEither.fromEither $ shunt (cast ops) synty 0) tymidx
  Success omega <- StEither.liftSt $ solve @{MkParams Nothing {solveNamedHoles = False}} ops sig omega [prob1]
    | Stuck omega stuckElab stuckCons =>
         -- write "(Unexpected error) Result elaborating expected monoid type in elabNormaliseComm (stuck):"
         -- write (renderDocTerm !(Elab.liftM $ prettyTyp sig omega [<] commMonoidTy 0))
         assert_total $ idris_crash $ renderDocTerm (prettyDefault sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => StEither.do
      StEither.throw (r, prettyDefault sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => StEither.do
      StEither.throw (r, prettyDefault sig (UnificationError omega (con, err)))


  (omega, monoidInstIdx) <- StEither.liftSt $ liftUnifyM $ newElemMeta omega [<] commMonoidTy SolveByElaboration
  let monoidInstTm = Elem.OmegaVarElim monoidInstIdx Terminal
  let prob1 = ElemElaboration [<] monoidInst monoidInstIdx commMonoidTy
  Success omega <- StEither.liftSt $ solve ops sig omega [prob1]
    | Stuck omega stuckElab stuckCons => StEither.do
         -- StEither.liftM $ write "Result elaborating monoid type in elabNormaliseComm (stuck):"
         -- StEither.liftM $ write (renderDocTerm !(StEither.liftM $ Elab.liftM $ prettyElem sig omega [<] monoidInstTm 0))
         throw (r, prettyDefault sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => StEither.do
      throw (r, prettyDefault sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => StEither.do
      throw (r, prettyDefault sig (UnificationError omega (con, err)))

  -- FIX: I totally hate this. This will be fixed by nameless representation of Ω though. We should speed up the migration!
  aindex <- StEither.liftSt $ liftUnifyM $ Unification.nextOmegaIdx
  zindex <- StEither.liftSt $ liftUnifyM $ Unification.nextOmegaIdx
  pindex <- StEither.liftSt $ liftUnifyM $ Unification.nextOmegaIdx
  let syntm0 = "?Aₘ\{natToSubscript aindex}, ?zₘ\{natToSubscript zindex}, ?pₘ\{natToSubscript pindex}, ?"
  let Right (_, syntm0) = parseFull' (MkParsingSt [<]) (term 0) syntm0
    | Left err => assert_total $ idris_crash (show err)
  (omega, midx0) <- StEither.liftSt $ liftUnifyM $ newElemMeta omega [<] commMonoidTy SolveByElaboration
  let prob2 = ElemElaboration [<] !(StEither.mapError (\x => (r, pretty x)) $ StEither.fromEither $ shunt (cast ops) syntm0 0) midx0 commMonoidTy
  let el0 = OmegaVarElim midx0 Terminal
  omega <- StEither.liftSt $ liftUnifyM $ addConstraint omega (ElemConstraint [<] el0 monoidInstTm commMonoidTy)
  Success omega <- StEither.liftSt $ solve @{MkParams Nothing {solveNamedHoles = True}} ops sig omega [prob2]
    | Stuck omega stuckElab stuckCons => StEither.do
         -- StEither.liftM $ write "Result of postProblem1 (stuck):"
         -- StEither.liftM $ write (renderDocTerm !(StEither.liftM $ Elab.liftM $ prettyElem sig omega [<] el0 0))
         throw (r, prettyDefault sig (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => throw (r, prettyDefault sig (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => throw (r, prettyDefault sig (UnificationError omega (con, err)))
  let monoidTy = El (Elem.OmegaVarElim "Aₘ\{natToSubscript aindex}" Terminal)
  let monoidZero = Elem.OmegaVarElim "zₘ\{natToSubscript zindex}" Terminal
  let monoidPlus = Elem.OmegaVarElim "pₘ\{natToSubscript pindex}" Terminal
  subst <- fromEither $ maybeToEither (r, "Can't find the given monoid variables in the context") (mbSubst sig omega focusedCtx vars monoidTy)
  tmInterp <- StEither.liftId $ interpTerm sig monoidTy monoidZero monoidPlus monoidTm
  omega <- StEither.liftSt $ liftUnifyM $ addConstraint omega (TypeConstraint focusedCtx focusedTy monoidTy)
  omega <- StEither.liftSt $ liftUnifyM $ addConstraint omega (ElemConstraint focusedCtx (ContextSubstElim tmInterp subst) focused monoidTy)
  Success omega <- StEither.liftSt $ liftUnifyM $ Unification.solve sig omega
    | _ => throw (r, "Failed to solve unification constraints")
  let monoidTm' = normaliseAlg monoidTm
  -- StEither.liftM $ write "Original monoid term: \{renderDocNoAnn {ann = Unit} $ CommutativeMonoid.Language.prettyTerm vars monoidTm}"
  -- StEither.liftM $ write "Normalised monoid term: \{renderDocNoAnn {ann = Unit} $ CommutativeMonoid.Language.prettyTerm vars monoidTm'}"
  tmInterp' <- StEither.liftId $ interpTerm sig monoidTy monoidZero monoidPlus monoidTm'
  let ty' = setFocused (ContextSubstElim tmInterp' subst)
  pure (omega, target :< (x, ElemEntry ctx ty'), id)
elabNormaliseComm ops sig omega r path monoidTm monoidInst _ = StEither.do
  throw (r, "Wrong context for tactic 'normalise-commmut-monoid'")
