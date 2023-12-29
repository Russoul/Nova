module Nova.Surface.Elaboration.Implementation.Tactic.NormaliseCommutativeMonoid

import Data.AVL
import Data.Fin
import Data.List1
import Data.Location
import Data.SnocList
import Data.Util

import Nova.Core.Context
import Nova.Core.Conversion
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Substitution
import Nova.Core.Unification
import Nova.Core.Util

import Nova.Surface.Language
import Nova.Surface.Elaboration.Interface

import Solver.CommutativeMonoid

||| TODO: Think about how to preserve naming
public export
interpContext : Nat -> Context
interpContext Z = [<]
interpContext (S k) = interpContext k :< ("_", NatTy)

||| For every Γ ctx
||| We get x̄
||| and |x̄| : Γ ⇒ ⟦x̄⟧
public export
Vars : Signature -> Omega -> Context -> M (Nat, SubstContext)
Vars sig omega [<] = return (0, Terminal)
Vars sig omega (gamma :< (_, ty)) = M.do
  (n, subst) <- Vars sig omega gamma
  NatTy <- openEval sig omega ty
    | _ => M.do
    return (n, Chain subst Wk)

  return (S n, Under subst)

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

