module Nova.Core.Context

import Nova.Core.Language
import Nova.Core.Substitution

||| Σ = Σ₀ (Δ ⊦ x : A) Σ₁
||| -----------------
||| Σ ⊦ Δ(↑(x Σ₁))
||| Σ Δ(↑(x Σ₁)) ⊦ A(↑(x Σ₁)) type
public export
lookupElemSignature : Signature -> VarName -> Maybe (Context, Nat, Typ)
lookupElemSignature [<] x = Nothing
lookupElemSignature (sig :< (x, ElemEntry ctx ty)) y = do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupElemSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupElemSignature (sig :< (x, LetElemEntry ctx _ ty)) y = do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupElemSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupElemSignature (sig :< (x, TypeEntry {})) y = do
  (ctx, i, ty) <- lookupElemSignature sig y
  Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupElemSignature (sig :< (x, LetTypeEntry {})) y = do
  (ctx, i, ty) <- lookupElemSignature sig y
  Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)

public export
lookupTypeSignature : Signature -> VarName -> Maybe (Context, Nat)
lookupTypeSignature [<] x = Nothing
lookupTypeSignature (sig :< (x, ElemEntry ctx ty)) y = do
  (ctx, i) <- lookupTypeSignature sig y
  Just (subst ctx SubstSignature.Wk, S i)
lookupTypeSignature (sig :< (x, LetElemEntry ctx _ ty)) y = do
  (ctx, i) <- lookupTypeSignature sig y
  Just (subst ctx SubstSignature.Wk, S i)
lookupTypeSignature (sig :< (x, TypeEntry ctx)) y = do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0)
    False => do
      (ctx, i) <- lookupTypeSignature sig y
      Just (subst ctx SubstSignature.Wk, S i)
lookupTypeSignature (sig :< (x, LetTypeEntry ctx rhs)) y = do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0)
    False => do
      (ctx, i) <- lookupTypeSignature sig y
      Just (subst ctx SubstSignature.Wk, S i)

public export
lookupLetElemSignature : Signature -> VarName -> Maybe (Context, Nat, Elem, Typ)
lookupLetElemSignature [<] x = Nothing
lookupLetElemSignature (sig :< (x, ElemEntry ctx ty)) y = do
 (ctx, i, rhs, ty) <- lookupLetElemSignature sig y
 Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetElemSignature (sig :< (x, TypeEntry {})) y = do
 (ctx, i, rhs, ty) <- lookupLetElemSignature sig y
 Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetElemSignature (sig :< (x, LetTypeEntry {})) y = do
 (ctx, i, rhs, ty) <- lookupLetElemSignature sig y
 Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetElemSignature (sig :< (x, LetElemEntry ctx rhs ty)) y = do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, rhs, ty) <- lookupLetElemSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)

public export
lookupLetTypeSignature : Signature -> VarName -> Maybe (Context, Nat, Typ)
lookupLetTypeSignature [<] x = Nothing
lookupLetTypeSignature (sig :< (x, ElemEntry ctx ty)) y = do
 (ctx, i, rhs) <- lookupLetTypeSignature sig y
 Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk)
lookupLetTypeSignature (sig :< (x, TypeEntry {})) y = do
 (ctx, i, rhs) <- lookupLetTypeSignature sig y
 Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk)
lookupLetTypeSignature (sig :< (x, LetElemEntry {})) y = do
 (ctx, i, rhs) <- lookupLetTypeSignature sig y
 Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk)
lookupLetTypeSignature (sig :< (x, LetTypeEntry ctx rhs)) y = do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim rhs Wk)
    False => do
      (ctx, i, rhs) <- lookupLetTypeSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk)

namespace Index
  ||| Looks up a signature entry by index. Weakens the result to be typed in the original signature.
  public export
  lookupSignature : Signature -> Nat -> Maybe (VarName, SignatureEntry)
  lookupSignature [<] _ = Nothing
  lookupSignature (_ :< (x, t)) Z = Just (x, t)
  lookupSignature (sig :< _) (S k) = do
    (x, e) <- lookupSignature sig k
    pure (x, subst e Wk)
