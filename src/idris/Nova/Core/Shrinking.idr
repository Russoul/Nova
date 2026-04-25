module Nova.Core.Shrinking

import Data.List
import Data.SnocList

import Nova.Core.Language
import Nova.Core.Substitution

-- FIX: Shrinking is semantically incorrect in extensional TT.

mutual
  namespace SubstContextNF
    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| σ : Γ₀ Γ₁ Γ₂ ⇒ Δ
    ||| shrink[σ] : Γ₀ Γ₂ ⇒ Δ
    public export
    shrink : SubstContextNF -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Maybe SubstContextNF
    shrink Terminal gamma1Len gamma2Len = Prelude.pure Terminal
    -- Γ₀ = Γ₀₀ Γ₀₁
    -- ↑ᵏ : Γ₀₀ Γ₀₁ Γ₁ Γ₂ ⇒ Γ₀₀
    -- shrink[↑ᵏ] : Γ₀₀ Γ₀₁ Γ₂ ⇒ Γ₀₀
    shrink (WkN k) gamma1Len gamma2Len =
      -- k = Γ₀₁ + Γ₁ + Γ₂
      -- Γ₀₁ = k - Γ₁ - Γ₂
      case k >= gamma2Len + gamma1Len of
        True => Just (WkN (k `minus` gamma1Len))
        False => Nothing
    shrink (Ext sigma t) gamma1Len gamma2Len = Prelude.do
      sigma <- shrink sigma gamma1Len gamma2Len
      t <- shrink t gamma1Len gamma2Len
      pure (Ext sigma t)

  namespace SubstContext
    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| σ : Γ₀ Γ₁ Γ₂ ⇒ Δ
    ||| shrink[σ] : Γ₀ Γ₂ ⇒ Δ
    public export
    shrink : SubstContext -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Maybe SubstContext
    shrink sigma gamma1Len gamma2Len = Prelude.do
      sigma <- shrink (eval sigma) gamma1Len gamma2Len
      pure (quote sigma)

  namespace Typ
    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₁ Γ₂ ⊦ A type
    ||| Γ₀ Γ₂ ⊦ shrink[A] type
    ||| A must be head-neutral w.r.t. substitution
    public export
    shrinkNu : Typ -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Maybe Typ
    shrinkNu (PiTy x a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (PiTy x a b)
    shrinkNu (ImplicitPiTy x a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (ImplicitPiTy x a b)
    shrinkNu (SigmaTy x a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (SigmaTy x a b)
    shrinkNu (El a) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      pure (El a)
    shrinkNu NatTy gamma1Len gamma2Len = Prelude.do
      pure NatTy
    shrinkNu ZeroTy gamma1Len gamma2Len = Prelude.do
      pure ZeroTy
    shrinkNu OneTy gamma1Len gamma2Len = Prelude.do
      pure OneTy
    shrinkNu UniverseTy gamma1Len gamma2Len = Prelude.do
      pure UniverseTy
    shrinkNu (ContextSubstElim x y) gamma1Len gamma2Len = assert_total $ idris_crash "shrink(ContextSubstElim)"
    shrinkNu (SignatureSubstElim x y) gamma1Len gamma2Len = assert_total $ idris_crash "shrink(SignatureSubstElim)"
    shrinkNu (OmegaVarElim k sigma) gamma1Len gamma2Len = Prelude.do
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ ⊦ σ : Δ ⇒ Γ
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ Δ ⊦ χ σ
      sigma <- shrink sigma gamma1Len gamma2Len
      pure (OmegaVarElim k sigma)
    shrinkNu (TyEqTy a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len gamma2Len
      pure (TyEqTy a b)
    shrinkNu (ElEqTy a b c) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len gamma2Len
      c <- shrink c gamma1Len gamma2Len
      pure (ElEqTy a b c)
    shrinkNu (SignatureVarElim k sigma) gamma1Len gamma2Len = Prelude.do
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ ⊦ σ : Δ ⇒ Γ
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ Δ ⊦ χ σ
      sigma <- shrink sigma gamma1Len gamma2Len
      pure (SignatureVarElim k sigma)

    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| Γ₀ Γ₁ Γ₂ ⊦ t : A
    ||| Γ₀ Γ₂ ⊦ shrink[t] : A
    public export
    shrink : Typ -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Maybe Typ
    shrink t gamma1Len gamma2Len = shrinkNu (runSubst t) gamma1Len gamma2Len

  namespace Elem
    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| Γ₀ Γ₁ Γ₂ ⊦ t : A
    ||| Γ₀ Γ₂ ⊦ shrink[t] : A
    ||| t must be head-neutral w.r.t. substitution
    public export
    shrinkNu : Elem -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Maybe Elem
    shrinkNu (PiTy x a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (PiTy x a b)
    shrinkNu (ImplicitPiTy x a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (ImplicitPiTy x a b)
    shrinkNu (SigmaTy x a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (SigmaTy x a b)
    shrinkNu (PiVal x a b f) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      f <- shrink f gamma1Len (S gamma2Len)
      pure (PiVal x a b f)
    shrinkNu (ImplicitPiVal x a b f) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      f <- shrink f gamma1Len (S gamma2Len)
      pure (ImplicitPiVal x a b f)
    shrinkNu (SigmaVal x a b p q) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      p <- shrink p gamma1Len gamma2Len
      q <- shrink q gamma1Len gamma2Len
      pure (SigmaVal x a b p q)
    shrinkNu (PiElim f x a b e) gamma1Len gamma2Len = Prelude.do
      f <- shrink f gamma1Len gamma2Len
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      e <- shrink e gamma1Len gamma2Len
      pure (PiElim f x a b e)
    shrinkNu (ImplicitPiElim f x a b e) gamma1Len gamma2Len = Prelude.do
      f <- shrink f gamma1Len gamma2Len
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      e <- shrink e gamma1Len gamma2Len
      pure (ImplicitPiElim f x a b e)
    shrinkNu (SigmaElim1 f x a b) gamma1Len gamma2Len = Prelude.do
      f <- shrink f gamma1Len gamma2Len
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (SigmaElim1 f x a b)
    shrinkNu (SigmaElim2 f x a b) gamma1Len gamma2Len = Prelude.do
      f <- shrink f gamma1Len gamma2Len
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      pure (SigmaElim2 f x a b)
    shrinkNu NatVal0 gamma1Len gamma2Len = Prelude.do
      pure NatVal0
    shrinkNu (NatVal1 t) gamma1Len gamma2Len = Prelude.do
      t <- shrink t gamma1Len gamma2Len
      pure (NatVal1 t)
    shrinkNu NatTy gamma1Len gamma2Len = Prelude.do
      pure NatTy
    shrinkNu ZeroTy gamma1Len gamma2Len = Prelude.do
      pure ZeroTy
    shrinkNu OneTy gamma1Len gamma2Len = Prelude.do
      pure OneTy
    shrinkNu OneVal gamma1Len gamma2Len = Prelude.do
      pure OneVal
    shrinkNu (NatElim x schema z y h s t) gamma1Len gamma2Len = Prelude.do
      schema <- shrink schema gamma1Len (S gamma2Len)
      z <- shrink z gamma1Len gamma2Len
      s <- shrink s gamma1Len (2 + gamma2Len)
      t <- shrink t gamma1Len gamma2Len
      pure (NatElim x schema z y h s t)
    shrinkNu (ZeroElim ty t) gamma1Len gamma2Len = Prelude.do
      ty <- shrink ty gamma1Len gamma2Len
      t <- shrink t gamma1Len gamma2Len
      pure (ZeroElim ty t)
    shrinkNu (ContextSubstElim x y) gamma1Len gamma2Len = assert_total $ idris_crash "shrink(ContextSubstElim)"
    shrinkNu (SignatureSubstElim x y) gamma1Len gamma2Len = assert_total $ idris_crash "shrink(SignatureSubstElim)"
    shrinkNu (ContextVarElim k) gamma1Len gamma2Len =
      case k < gamma2Len of
        True => pure (ContextVarElim k)
        False =>
          case (k `minus` gamma2Len) < gamma1Len of
            True => Nothing
            False => pure (ContextVarElim (k `minus` gamma1Len))
    shrinkNu (SignatureVarElim k sigma) gamma1Len gamma2Len = Prelude.do
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ ⊦ σ : Δ ⇒ Γ
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ Δ ⊦ χ σ
      sigma <- shrink sigma gamma1Len gamma2Len
      pure (SignatureVarElim k sigma)
    shrinkNu (OmegaVarElim k sigma) gamma1Len gamma2Len = Prelude.do
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ ⊦ σ : Δ ⇒ Γ
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ Δ ⊦ χ σ
      sigma <- shrink sigma gamma1Len gamma2Len
      pure (OmegaVarElim k sigma)
    shrinkNu (TyEqTy a b) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len gamma2Len
      pure (TyEqTy a b)
    shrinkNu (ElEqTy a b c) gamma1Len gamma2Len = Prelude.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len gamma2Len
      c <- shrink c gamma1Len gamma2Len
      pure (ElEqTy a b c)
    shrinkNu (TyEqVal ty) gamma1Len gamma2Len = Prelude.do
      ty <- shrink ty gamma1Len gamma2Len
      pure (TyEqVal ty)
    shrinkNu (ElEqVal ty e) gamma1Len gamma2Len = Prelude.do
      ty <- shrink ty gamma1Len gamma2Len
      e <- shrink e gamma1Len gamma2Len
      pure (ElEqVal ty e)

    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| Γ₀ Γ₁ Γ₂ ⊦ t : A
    ||| Γ₀ Γ₂ ⊦ shrink[t] : A
    public export
    shrink : Elem -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Maybe Elem
    shrink t gamma1Len gamma2Len = shrinkNu (runSubst t) gamma1Len gamma2Len
