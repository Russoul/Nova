module Nova.Surface.Elaboration.Implementation.Tactic.NormaliseCommutativeMonoid

import Data.AVL
import Data.Fin
import Data.List1
import Data.Location
import Data.SnocList
import Data.Util
import Data.Either

import Text.PrettyPrint.Prettyprinter

import Nova.Core.Context
import Nova.Core.Conversion
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Pretty
import Nova.Core.Substitution
import Nova.Core.Unification
import Nova.Core.Util

import Nova.Surface.Language
import Nova.Surface.Elaboration.Interface
import Nova.Surface.Elaboration.Implementation.Tactic.TermLens

import Solver.CommutativeMonoid

public export
interpContext : SnocList String -> Context
interpContext [<] = [<]
interpContext (xs :< x) = interpContext xs :< (x, NatTy)

||| Given x̄ and a (Γ ctx) try constructing σ : Γ ⇒ ⟦x̄⟧
public export
mbSubst : Signature -> Omega -> Context -> SnocList String -> M (Maybe SubstContext)
mbSubst sig omega ctx [<] = MMaybe.do return Terminal
mbSubst sig omega ctx (xs :< x) = MMaybe.do
  sigma <- mbSubst sig omega ctx xs
  (tm, ty) <- fromMaybe $ lookupContext ctx x
  NatTy <- liftM $ openEval sig omega ty
    | _ => nothing
  return (Ext sigma tm)

public export
interpTerm : Signature -> Term (Fin n) -> M Elem
interpTerm sig (Var x) = return $ ContextVarElim (finToNat x)
interpTerm sig Zero = return NatVal0
interpTerm sig (Plus a b) = M.do
  idx <- lookupSignatureIdxE sig "_+_"
  a <- interpTerm sig a
  b <- interpTerm sig b
  -- ((_+_ : ℕ → ℕ → ℕ) a : ℕ → ℕ) b
  return $
    PiElim (PiElim (SignatureVarElim idx Terminal) "_" NatTy (funTy NatTy NatTy) a)
      "_"
      NatTy
      NatTy
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

-- ||| x̄ ⊦ m ∈ FreeCommMonoid
-- ||| σ : x̄ ⇒ Γ
-- ||| -----------------------
-- ||| Γ ⊦ ⟦m | σ⟧ : M
-- ||| Γ ⊦ ⟦x | σ⟧ = σ(x) : M
-- ||| Γ ⊦ ⟦a + b | σ⟧ = ⟦a | σ⟧ + [b | σ⟧ : M
-- ||| Γ ⊦ ⟦0 | σ⟧ = Z : M
--
-- ||| For common Σ Ω:
-- ||| Γ ⊦ E type
-- ||| Γ ⊦ e : E
-- ||| ε ⊦ t ∈ SurfaceTerm
-- ||| ---------------------
-- ||| ε ⊦ A : 𝕌
-- ||| ε ⊦ z : A
-- ||| ε ⊦ _+_ : A → A → A
-- ||| ε ⊦ t' = (A, z, _+_, ?) : Comm-Monoid
-- ||| ε ⊦ E = A type
-- ||| x̄
-- ||| σ : x̄ ⇒ Γ
-- ||| x̄ ⊦ m ∈ CommMonoid
-- ||| Γ ⊦ e = ⟦m | σ⟧ : A
public export
elab0 : Params => Signature -> Omega -> Context -> OpFreeTerm -> Typ -> Elem -> ElabM Elem
elab0 sig omega gamma monoidInstTerm ty tm = M.do
  commMonoidTy <- Elab.liftM $
    lookupSignatureIdxE sig "Commut-Monoid" `M.(<&>)` (\idx => Typ.SignatureVarElim idx Terminal)
  (omega, tidx) <- liftUnifyM $ newElemMeta omega [<] commMonoidTy SolveByElaboration
  let prob = ElemElaboration [<] monoidInstTerm tidx commMonoidTy
  case !(Elaboration.Interface.solve sig omega [prob]) of
    Success omega => M.do
     (omega, tyidx) <- liftUnifyM $ newElemMeta omega [<] UniverseTy SolveByUnification
     (omega, zidx) <- liftUnifyM $ newElemMeta omega [<] (El (Elem.OmegaVarElim tyidx Terminal)) SolveByUnification
     (omega, pidx) <- liftUnifyM $ newElemMeta omega [<]
            (funTyN1 $
              asList1 [ El (Elem.OmegaVarElim tyidx Terminal)
                      , El (Elem.OmegaVarElim tyidx Terminal)
                      , El (Elem.OmegaVarElim tyidx Terminal)
                      ]
            ) SolveByUnification
     (omega, holeIdx) <- liftUnifyM $ newElemMeta omega [<] ?holeTy SolveByUnification
     -- ε ⊦ ⟦A, z, _+_, ?⟧ ⇝ _ : Comm-Monoid
     -- ⟦A, z, _+_, ?⟧ = π 𝕌 (A. Is-Commut-Monoid A) A ⟦z, _+_, ?⟧
     -- = π 𝕌 (A. Is-Commut-Monoid A) A (π (El A) )
     ?af
    _ => throw "Couldn't check the commutative monoid instance"

||| Σ₀ ⊦ ? ⇛ Σ (Γ ⊦ x : A)
public export
elabNormaliseComm : Params
                 => Signature
                 -> Omega
                 -> Range
                 -> OpFreeTerm
                 -> (vars : SnocList String ** Term (Fin (length vars)))
                 -> OpFreeTerm
                 -> Signature
                 -> ElabM (Either (Range, Doc Ann) (Omega, Signature, SignatureInst -> SignatureInst))
elabNormaliseComm sig omega r path (vars ** monoidTm) monoidInst (target :< (x, ElemEntry ctx ty)) = MEither.do
  MkLens focusedR focusedCtx (Right (focused, setFocused)) <- Elab.liftM $ Typ.lens sig omega ctx ty path
    | _ => error (r, "Wrong focused term for 'normalise-commut-monoid'")
  subst <- mapResult (maybeToEither (r, "Can't find the given monoid variables in the context")) $
          Elab.liftM $ mbSubst sig omega focusedCtx vars
  tmInterp <- ElabEither.liftM $ interpTerm sig monoidTm
  -- omega <- addConstraint omega (ElemConstraint focusedCtx tmInterp )
  ?todo
elabNormaliseComm sig omega r path monoidTm monoidInst _ = MEither.do
  error (r, "Wrong context for tactic 'normalise-commmut-monoid'")
