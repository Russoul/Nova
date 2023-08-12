module ETT.Core.Shrinking

import Data.List
import Data.SnocList

import ETT.Core.Monad
import ETT.Core.Language
import ETT.Core.Substitution

mutual
  namespace SubstContextNF
    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| σ : Γ₀ Γ₁ Γ₂ ⇒ Δ
    ||| shrink[σ] : Γ₀ Γ₂ ⇒ Δ
    public export
    shrink : SubstContextNF -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Mb SubstContextNF
    shrink Terminal gamma1Len gamma2Len = Mb.do
      return Terminal
    -- Γ₀ = Γ₀₀ Γ₀₁
    -- ↑ᵏ : Γ₀₀ Γ₀₁ Γ₁ Γ₂ ⇒ Γ₀₀
    -- shrink[↑ᵏ] : Γ₀₀ Γ₀₁ Γ₂ ⇒ Γ₀₀
    shrink (WkN k) gamma1Len gamma2Len =
      -- k = Γ₀₁ + Γ₁ + Γ₂
      -- Γ₀₁ = k - Γ₁ - Γ₂
      case k >= gamma2Len + gamma1Len of
        True => return (WkN (k `minus` gamma1Len))
        False => nothing
    shrink (Ext sigma t) gamma1Len gamma2Len = Mb.do
      sigma <- shrink sigma gamma1Len gamma2Len
      t <- shrink t gamma1Len gamma2Len
      return (Ext sigma t)

  namespace SubstContext
    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| σ : Γ₀ Γ₁ Γ₂ ⇒ Δ
    ||| shrink[σ] : Γ₀ Γ₂ ⇒ Δ
    public export
    shrink : SubstContext -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Mb SubstContext
    shrink sigma gamma1Len gamma2Len = Mb.do
      sigma <- shrink (eval sigma) gamma1Len gamma2Len
      return (quote sigma)

  namespace Elem
    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| Γ₀ Γ₁ Γ₂ ⊦ t : A
    ||| Γ₀ Γ₂ ⊦ shrink[t] : A
    ||| t must be head-neutral w.r.t. substitution
    public export
    shrinkNu : Elem -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Mb Elem
    shrinkNu (PiTy x a b) gamma1Len gamma2Len = Mb.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      return (PiTy x a b)
    shrinkNu (SigmaTy x a b) gamma1Len gamma2Len = Mb.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      return (SigmaTy x a b)
    shrinkNu (PiVal x a b f) gamma1Len gamma2Len = Mb.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      f <- shrink f gamma1Len (S gamma2Len)
      return (PiVal x a b f)
    shrinkNu (SigmaVal a b) gamma1Len gamma2Len = Mb.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len gamma2Len
      return (SigmaVal a b)
    shrinkNu (PiElim f x a b e) gamma1Len gamma2Len = Mb.do
      f <- shrink f gamma1Len gamma2Len
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      e <- shrink e gamma1Len gamma2Len
      return (PiElim f x a b e)
    shrinkNu (SigmaElim1 f x a b) gamma1Len gamma2Len = Mb.do
      f <- shrink f gamma1Len gamma2Len
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      return (SigmaElim1 f x a b)
    shrinkNu (SigmaElim2 f x a b) gamma1Len gamma2Len = Mb.do
      f <- shrink f gamma1Len gamma2Len
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len (S gamma2Len)
      return (SigmaElim2 f x a b)
    shrinkNu Universe gamma1Len gamma2Len = Mb.do
      return Universe
    shrinkNu NatVal0 gamma1Len gamma2Len = Mb.do
      return NatVal0
    shrinkNu (NatVal1 t) gamma1Len gamma2Len = Mb.do
      t <- shrink t gamma1Len gamma2Len
      return (NatVal1 t)
    shrinkNu NatTy gamma1Len gamma2Len = Mb.do
      return NatTy
    shrinkNu (NatElim x schema z y h s t) gamma1Len gamma2Len = Mb.do
      schema <- shrink schema gamma1Len (S gamma2Len)
      z <- shrink z gamma1Len gamma2Len
      s <- shrink s gamma1Len (2 + gamma2Len)
      t <- shrink t gamma1Len gamma2Len
      return (NatElim x schema z y h s t)
    shrinkNu (ContextSubstElim x y) gamma1Len gamma2Len = throw "shrink(ContextSubstElim)"
    shrinkNu (SignatureSubstElim x y) gamma1Len gamma2Len = throw "shrink(SignatureSubstElim)"
    shrinkNu (ContextVarElim k) gamma1Len gamma2Len =
      case k < gamma2Len of
        True => return (ContextVarElim k)
        False =>
          case (k `minus` gamma2Len) < gamma1Len of
            True => nothing
            False => return (ContextVarElim (k `minus` gamma1Len))
    shrinkNu (SignatureVarElim k sigma) gamma1Len gamma2Len = Mb.do
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ ⊦ σ : Δ ⇒ Γ
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ Δ ⊦ χ σ
      sigma <- shrink sigma gamma1Len gamma2Len
      return (SignatureVarElim k sigma)
    shrinkNu (OmegaVarElim k sigma) gamma1Len gamma2Len = Mb.do
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ ⊦ σ : Δ ⇒ Γ
      -- Σ₀ (Γ ⊦ χ : A) Σ₁ Δ ⊦ χ σ
      sigma <- shrink sigma gamma1Len gamma2Len
      return (OmegaVarElim k sigma)
    shrinkNu (EqTy a b c) gamma1Len gamma2Len = Mb.do
      a <- shrink a gamma1Len gamma2Len
      b <- shrink b gamma1Len gamma2Len
      c <- shrink c gamma1Len gamma2Len
      return (EqTy a b c)
    shrinkNu EqVal gamma1Len gamma2Len = Mb.do
      return EqVal

    ||| Γ₀ ⊦ Γ₁ ctx
    ||| Γ₀ ⊦ Γ₂ ctx
    ||| Γ₀ Γ₂ ⊦ A type
    ||| Γ₀ Γ₁ Γ₂ ⊦ t : A
    ||| Γ₀ Γ₂ ⊦ shrink[t] : A
    public export
    shrink : Elem -> (gamma1Len : Nat) -> (gamma2Len : Nat) -> Mb Elem
    shrink t gamma1Len gamma2Len = shrinkNu (runSubst t) gamma1Len gamma2Len
