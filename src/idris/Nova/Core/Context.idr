module Nova.Core.Context

import Nova.Core.Language
import Nova.Core.Substitution

||| Σ = Σ₀ (Δ ⊦ x : A) Σ₁
||| -----------------
||| Σ ⊦ Δ(↑(x Σ₁))
||| Σ Δ(↑(x Σ₁)) ⊦ A(↑(x Σ₁)) type
public export
lookupSignature : Signature -> VarName -> Maybe (Context, Nat, Typ)
lookupSignature [<] x = Nothing
lookupSignature (sig :< (x, ElemEntry ctx ty)) y = M.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, LetElemEntry ctx _ ty)) y = M.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)

||| TODO: Factor this out
public export
lookupLetSignature : Signature -> VarName -> Maybe (Context, Nat, Elem, Typ)
lookupLetSignature [<] x = Nothing
lookupLetSignature (sig :< (x, ElemEntry ctx ty)) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetSignature (sig :< (x, LetElemEntry ctx rhs ty)) y = M.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)

namespace Index
  ||| Looks up a signature entry by index. Weakens the result to be typed in the original signature.
  public export
  lookupSignature : Signature -> Nat -> Maybe (VarName, SignatureEntry)
  lookupSignature [<] _ = Nothing
  lookupSignature (_ :< (x, t)) Z = Just (x, t)
  lookupSignature (sig :< _) (S k) = do
    (x, e) <- lookupSignature sig k
    pure (x, subst e Wk)
