module ExtTT.Surface.Check

import Data.Location
import Data.List1

import Control.Monad.FailSt

import ExtTT.Core.Language
import ExtTT.Core.Substitution
import ExtTT.Core.Conversion

import ExtTT.Surface.Language

-- Σ ⊦ Γ ctx
-- ----------------------
-- ⟦Σ | Γ ⊦ A ~> A' type⟧

-- Σ ⊦ Γ ctx
-- Σ | Γ ⊦ Δ tel
-- ----------------------
-- ⟦Σ | Γ ⊦ ē ~> ē' : Δ⟧



-- ⟦Σ₀ (Δ ⊦ X type) Σ₁ | Γ ⊦ ē ~> ē : Δ⟧
-- -------------------------------------------
-- ⟦Σ₀ (Δ ⊦ X type) Σ₁ | Γ ⊦ X ē ~> X ē' type⟧

-- ⟦Σ | Γ ⊦ 𝕌 ~> 𝕌 type⟧

-- ⟦Σ | Γ ⊦ ℕ ~> ℕ type⟧

-- ⟦Σ | Γ ⊦ A ~> A' type⟧
-- ⟦Σ | Γ (x : A') ⊦ B ~> B' type⟧
-- ------------------------------------------------
-- ⟦Σ | Γ ⊦ (x : A) → B ~> (x : A') → B' type⟧

-- ⟦Σ | Γ ⊦ A ~> A' type⟧
-- ⟦Σ | Γ ⊦ a₀ ~> a₀' : A'⟧
-- ⟦Σ | Γ ⊦ a₁ ~> a₁' : A'⟧
-- -------------------------------------------
-- ⟦Σ | Γ ⊦ a₀ ≡ a₁ ∈ A ~> a₀' ≡ a₁' ∈ A' type⟧

{- CoreTypE = ExtTT.Core.Language.C.TypE
CoreElem = ExtTT.Core.Language.D.Elem
SurfaceTerm = ExtTT.Surface.Language.Term
%hide ExtTT.Surface.Language.VarName


mkErrorMsg : Range -> String -> String
mkErrorMsg r msg = "\{msg}\n\{show r}"

||| Γ₀ (xᵢ : A) Γ₁ ⊦ xᵢ : A
lookupContext : Context -> VarName -> Maybe (CoreElem, CoreTypE)
lookupContext Empty x = Nothing
lookupContext (SignatureVarElim k) x = Nothing
lookupContext (Ext ctx x ty) y = FailSt.do
  case x == y of
    True => Just (ContextVarElim 0, ContextSubstElim ty Wk)
    False => do
      (t, ty) <- lookupContext ctx y
      Just (ContextSubstElim t Wk, ContextSubstElim ty Wk)


||| Σ = Σ₀ (Δ ⊦ x : A) Σ₁
||| -----------------
||| Σ ⊦ Δ(↑(x Σ₁))
||| Σ Δ(↑(x Σ₁)) ⊦ A(↑(x Σ₁)) type
lookupSignature : Signature -> VarName -> Maybe (Context, Nat, CoreTypE)
lookupSignature Empty x = Nothing
lookupSignature (ExtElem sig ctx x ty) y = FailSt.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (ExtLetElem sig ctx x _ ty) y = FailSt.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)

mutual
  ||| Γ ⊦ (f : F) ⟦ē⁺⟧ ⇝ t : B
  public export
  checkElimNu : Signature -> Context -> CoreElem -> CoreTypE -> Elim -> CoreTypE -> M CoreElem
  checkElimNu sig ctx f fTy [] exp = FailSt.do
    True <- conv fTy exp
      | False => throw "The term is non-checkable (0)"
    return f
  checkElimNu sig ctx f (PiTy x a b) (([], e) :: es) exp = FailSt.do
    e' <- checkElem sig ctx e a
    checkElim sig ctx (PiElim f x a b e') (ContextSubstElim b (Ext Id e')) es exp
  checkElimNu sig ctx f _ (([], e) :: xs) exp = throw "The term is non-checkable (1)"
  checkElimNu sig ctx f fTy ((_, e) :: xs) exp = throw "The term is non-checkable (2)"

  public export
  checkElim : Signature -> Context -> CoreElem -> CoreTypE -> Elim -> CoreTypE -> M CoreElem
  checkElim sig ctx f fTy es exp = checkElimNu sig ctx f !(runSubst fTy) es exp

  public export
  checkElemNu : Signature -> Context -> SurfaceTerm -> CoreTypE -> M CoreElem
  checkElemNu sig ctx (PiTy r x a b) UniverseTy = FailSt.do
    a' <- checkElem sig ctx a UniverseTy
    b' <- checkElem sig (Ext ctx x (El a')) b UniverseTy
    return (PiTy x a' b')
  checkElemNu sig ctx (PiTy r x a b) _ = FailSt.do
    throw (mkErrorMsg r "While checking (_ : _) → _: computed type doesn't match expected type")
  checkElemNu sig ctx (FunTy r a b) UniverseTy = FailSt.do
    a' <- checkElem sig ctx a UniverseTy
    b' <- checkElem sig ctx b UniverseTy
    return (PiTy "_" a' (ContextSubstElim b' Wk))
  checkElemNu sig ctx (FunTy r a b) _ = FailSt.do
    throw (mkErrorMsg r "While checking _ → _: computed type doesn't match expected type")
  checkElemNu sig ctx (EqTy r a b ty) UniverseTy = FailSt.do
    ty' <- checkElem sig ctx ty UniverseTy
    a' <- checkElem sig ctx a (El ty')
    b' <- checkElem sig ctx b (El ty')
    return (EqTy a' b' ty')
  checkElemNu sig ctx (EqTy r a b ty) _ = FailSt.do
    throw (mkErrorMsg r "While checking _ ≡ _ ∈ _: computed type doesn't match expected type")
  checkElemNu sig ctx (PiVal r x f) (PiTy _ a b) = FailSt.do
    f' <- checkElem sig (Ext ctx x a) f b
    return (PiVal x f')
  checkElemNu sig ctx (PiVal r x f) _ = FailSt.do
    throw (mkErrorMsg r "While checking _ ↦ _: computed type doesn't match expected type")
  checkElemNu sig ctx (App _ (Var r x) es) ty = FailSt.do
    let Just (v, vTy) = lookupContext ctx x
      | Nothing => FailSt.do
          -- Σ₀ (x : A) Σ₁ ⊦ x ē
          let Just (Empty, i, ty') = lookupSignature sig x
            | Just (_, _) => throw (mkErrorMsg r "non-empty signature context not supported yet")
            | Nothing => throw (mkErrorMsg r "Undefined name: \{x}")
          checkElim sig ctx (SignatureVarElim i [<]) ty' es ty
    checkElim sig ctx v vTy es ty
  checkElemNu sig ctx (App r (NatVal0 x) []) NatTy = return NatVal0
  checkElemNu sig ctx (App r (NatVal1 x) [([], e)]) NatTy = FailSt.do
    e' <- checkElem sig ctx e NatTy
    return (NatVal1 e')
  checkElemNu sig ctx (App r (NatElim _) [([x], schema), ([], z), ([y, h], s), ([], t)]) ty = FailSt.do
    schema' <- checkTypE sig (Ext ctx x NatTy) schema
    z' <- checkElem sig ctx z (ContextSubstElim schema' (Ext Id NatVal0))
    -- Γ (x : ℕ) ⊦ C type
    -- Γ (x : ℕ) (h : C) ⊦ C (↑², S x₁)
    s' <- checkElem sig (Ext (Ext ctx y NatTy) h schema') s (ContextSubstElim schema' (Ext (WkN 2) (NatVal1 (VarN 1))))
    t' <- checkElem sig ctx t NatTy
    let exp = ContextSubstElim schema' (Ext Id t')
    True <- conv exp ty
      | False => throw (mkErrorMsg r "While checking ℕ-elim: computed type doesn't match expected type")
    return (NatElim x schema' z' y h s' t')
  checkElemNu sig ctx (App r (EqVal x) []) (EqTy a b ty) =
    case !(conv a b) of
      True => return (EqVal a ty)
      False => throw (mkErrorMsg r "While checking Refl: computed type doesn't match expected type")
  checkElemNu sig ctx (App range (EqElim _) [([], ty), ([], a0), ([x, h], schema), ([], r), ([], a1), ([], a)]) exp = FailSt.do
    ty' <- checkTypE sig ctx ty
    a0' <- checkElem sig ctx a0 ty'
    a1' <- checkElem sig ctx a1 ty'
    a' <- checkElem sig ctx a (EqTy a0' a1' ty')
    -- Γ (x : A) (x ≡ a₀(↑) ∈ A(↑)) ⊦ B : 𝕌
    schema' <- checkTypE sig (Ext (Ext ctx x ty') h (EqTy Var (ContextSubstElim a0' Wk) (ContextSubstElim ty' Wk))) schema
    -- Γ ⊦ r : B(id, a₀, Refl a₀ A)
    r' <- checkElem sig ctx r (ContextSubstElim schema' (Ext (Ext Id a0') (EqVal a0' ty')))
    True <- conv (ContextSubstElim schema' (Ext (Ext Id a1') a')) exp
      | False => throw (mkErrorMsg range "While checking J: computed type doesn't match expected type")
    return (EqElim ty' a0' x h schema' r' a1' a')
  checkElemNu sig ctx (App _ (NatTy _) []) UniverseTy = return NatTy
  checkElemNu sig ctx tm ty = throw (mkErrorMsg (range tm) "While checking \{show tm}: can't check")

  -- Γ ⊦ (f : B) ⟦·⟧ ⇝ f : B

  -- Γ ⊦ ⟦e⟧ ⇝ e' : A
  -- Γ ⊦ (f e' : B[e'/x]) ⟦ē⟧ ⇝ t
  -- ------------------------------------
  -- Γ ⊦ (f : (x : A) → B) ⟦e ē⟧ ⇝ t : C

  -- Γ₀ (x : A) Γ₁ ⊦ (x : A) ⟦ē⁺⟧ ⇝ t : B
  -- ------------------------------------
  -- Γ₀ (x : A) Γ₁ ⊦ ⟦x ē⁺⟧ ⇝ t : B

  public export
  checkElem : Signature -> Context -> SurfaceTerm -> CoreTypE -> M CoreElem
  checkElem sig ctx tm ty = checkElemNu sig ctx tm !(runSubst ty)

  public export
  checkTypE : Signature -> Context -> SurfaceTerm -> M CoreTypE
  checkTypE sig ctx (PiTy _ x a b) = FailSt.do
    a' <- checkTypE sig ctx a
    b' <- checkTypE sig (Ext ctx x a') b
    return (PiTy x a' b')
  checkTypE sig ctx (FunTy _ a b) = FailSt.do
    a' <- checkTypE sig ctx a
    b' <- checkTypE sig ctx b
    return (PiTy "_" a' (ContextSubstElim b' Wk))
  checkTypE sig ctx (EqTy _ a0 a1 ty) = FailSt.do
    ty' <- checkTypE sig ctx ty
    a0' <- checkElem sig ctx a0 ty'
    a1' <- checkElem sig ctx a1 ty'
    return (EqTy a0' a1' ty')
  checkTypE sig ctx (PiVal r str y) = throw (mkErrorMsg r "Not a type")
  checkTypE sig ctx (App r (Var x str) es) = throw (mkErrorMsg r "TODO")
  checkTypE sig ctx (App r (NatVal0 x) es) = throw (mkErrorMsg r "Not a type")
  checkTypE sig ctx (App r (NatVal1 x) es) = throw (mkErrorMsg r "Not a type")
  checkTypE sig ctx (App r (NatElim x) es) = throw (mkErrorMsg r "Not a type")
  checkTypE sig ctx (App r (EqVal x) es) = throw (mkErrorMsg r "Not a type")
  checkTypE sig ctx (App r (EqElim x) es) = throw (mkErrorMsg r "Not a type")
  checkTypE sig ctx (App _ (NatTy x) es) = return NatTy
  checkTypE sig ctx (App _ (UniverseTy _) es) = return UniverseTy
  checkTypE sig ctx (App _ (El _) [([], t)]) = FailSt.do
    t' <- checkElem sig ctx t UniverseTy
    return (El t')
  checkTypE sig ctx (App r (El x) _) = throw (mkErrorMsg r "Bad term")

  public export
  checkTypingSignature : Signature -> Range -> VarName -> SurfaceTerm -> M (Context, VarName, CoreTypE)
  checkTypingSignature sig r x tm = FailSt.do
    print_ Debug "About to check: \{show tm}"
    tm' <- checkTypE sig Empty tm
    return (Empty, x, tm')

  public export
  checkTopLevel : Signature -> TopLevel -> M (Context, VarName, CoreTypE)
  checkTopLevel sig (TypingSignature r x ty) = checkTypingSignature sig r x ty

  public export
  checkFile : Signature -> List1 TopLevel -> M Signature
  checkFile sig (top ::: []) = FailSt.do
    (ctx, x, ty) <- checkTopLevel sig top
    return (ExtElem sig ctx x ty)
  checkFile sig (top ::: top' :: more) = FailSt.do
    (ctx, x, ty) <- checkTopLevel sig top
    checkFile (ExtElem sig ctx x ty) (top' ::: more)
 -}
