module ETT.Surface.Check

import Data.Location
import Data.List1
import Data.List
import Data.SnocList

import Control.Monad.FailSt

import ETT.Core.Language
import ETT.Core.Substitution
import ETT.Core.Conversion

import ETT.Surface.Language

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

CoreElem = ETT.Core.Language.D.Elem
SurfaceTerm = ETT.Surface.Language.Term

public export
record CheckSt where
  constructor MkCheckSt
  -- Γ ⊦ ?x : A
  holes : SnocList (Context, VarName, CoreElem)


public export
CheckM : Type -> Type
CheckM = FailStM String CheckSt

mkErrorMsg : Range -> String -> String
mkErrorMsg r msg = "\{msg}\n\{show r}"

public export
numberOfHoles : CheckM Nat
numberOfHoles = FailSt.do
  MkCheckSt holes <- get
  return (length holes)

||| Register a new hole with a unique name.
||| Ensures that the name is unique.
registerHole : Signature -> Range -> Context -> VarName -> CoreElem -> CheckM ()
registerHole sig r ctx x tm = FailSt.do
  MkCheckSt holes <- get
  let Nothing = find (\(n, _) => n == x) sig $> () <|> find (\(_, n, _) => n == x) holes $> ()
    | _ => throw $ mkErrorMsg r "Hole with that name already exists: \{x}"
  update {holes $= (:< (ctx, x, tm))}

||| Converts a hole postfix to a (contextual) contextual.
public export
toSignature : SnocList (Context, VarName, CoreElem) -> Signature
toSignature = map (\(ctx, x, ty) => (x, ElemEntry ctx ty))

||| Full signature is computed by appending registered holes to the prefix.
computeSignature : (prefix_ : Signature) -> CheckM Signature
computeSignature pr = FailSt.do
  MkCheckSt holes <- get
  return $ pr ++ toSignature holes

liftM : M a -> CheckM a
liftM f = FailSt.do
  st <- get
  mapState (const st) (const ()) f

||| Γ₀ (xᵢ : A) Γ₁ ⊦ xᵢ : A
lookupContext : Context -> VarName -> Maybe (CoreElem, CoreElem)
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
lookupSignature : Signature -> VarName -> Maybe (Context, Nat, CoreElem)
lookupSignature [<] x = Nothing
lookupSignature (sig :< (x, CtxEntry)) y = FailSt.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, TypeEntry {})) y = FailSt.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, EqTyEntry {})) y = FailSt.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, ElemEntry ctx ty)) y = FailSt.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, LetElemEntry ctx _ ty)) y = FailSt.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)

mutual
  ||| Γ ⊦ (f : F) ⟦ē⁺⟧ ⇝ t : B
  public export
  checkElimNu : Signature -> Context -> CoreElem -> CoreElem -> Elim -> CoreElem -> CheckM CoreElem
  checkElimNu sig ctx f fTy [] exp = FailSt.do
    True <- liftM $ conv fTy exp
      | False => throw "The term is non-checkable (0)"
    return f
  checkElimNu sig ctx f (PiTy x a b) (([], e) :: es) exp = FailSt.do
    d0 <- numberOfHoles
    e' <- checkElem sig ctx e a
    d1 <- numberOfHoles
    let f = SignatureSubstElim f (WkN $ d1 `minus` d0)
    let a = SignatureSubstElim a (WkN $ d1 `minus` d0)
    let b = SignatureSubstElim b (WkN $ d1 `minus` d0)
    let exp = SignatureSubstElim exp (WkN $ d1 `minus` d0)
    checkElim sig ctx (PiElim f x a b e') (ContextSubstElim b (Ext Id e')) es exp
  checkElimNu sig ctx f _ (([], e) :: xs) exp = throw "The term is non-checkable (1)"
  checkElimNu sig ctx f fTy ((_, e) :: xs) exp = throw "The term is non-checkable (2)"

  public export
  checkElim : Signature -> Context -> CoreElem -> CoreElem -> Elim -> CoreElem -> CheckM CoreElem
  checkElim sig ctx f fTy es exp = checkElimNu sig ctx f (runSubst fTy) es exp

  public export
  checkElemNu : Signature -> Context -> SurfaceTerm -> CoreElem -> CheckM CoreElem
  checkElemNu sig ctx (PiTy r x a b) Universe = FailSt.do
    a' <- checkElem sig ctx a Universe
    aNHoles <- numberOfHoles
    b' <- checkElem sig (Ext ctx x a') b Universe
    bNHoles <- numberOfHoles
    return (PiTy x (SignatureSubstElim a' (WkN $ bNHoles `minus` aNHoles)) b')
  checkElemNu sig ctx (PiTy r x a b) _ = FailSt.do
    throw (mkErrorMsg r "While checking (_ : _) → _: computed type doesn't match expected type")
  checkElemNu sig ctx (FunTy r a b) Universe = FailSt.do
    a' <- checkElem sig ctx a Universe
    aNHoles <- numberOfHoles
    b' <- checkElem sig ctx b Universe
    bNHoles <- numberOfHoles
    return (PiTy "_" (SignatureSubstElim a' (WkN $ bNHoles `minus` aNHoles)) (ContextSubstElim b' Wk))
  checkElemNu sig ctx (FunTy r a b) _ = FailSt.do
    throw (mkErrorMsg r "While checking _ → _: computed type doesn't match expected type")
  checkElemNu sig ctx (EqTy r a b ty) Universe = FailSt.do
    ty' <- checkElem sig ctx ty Universe
    tyNHoles <- numberOfHoles
    a' <- checkElem sig ctx a ty'
    aNHoles <- numberOfHoles
    b' <- checkElem sig ctx b (SignatureSubstElim ty' (WkN $ aNHoles `minus` tyNHoles))
    bNHoles <- numberOfHoles
    return (EqTy (SignatureSubstElim a' (WkN $ bNHoles `minus` aNHoles)) b' (SignatureSubstElim ty' (WkN $ bNHoles `minus` tyNHoles)))
  checkElemNu sig ctx (EqTy r a b ty) _ = FailSt.do
    throw (mkErrorMsg r "While checking _ ≡ _ ∈ _: computed type doesn't match expected type")
  checkElemNu sig ctx (PiVal r x f) (PiTy _ a b) = FailSt.do
    d0 <- numberOfHoles
    f' <- checkElem sig (Ext ctx x a) f b
    d1 <- numberOfHoles
    return (PiVal x (SignatureSubstElim a (WkN $ d1 `minus` d0)) (SignatureSubstElim b (WkN $ d1 `minus` d0)) f')
  checkElemNu sig ctx (PiVal r x f) _ = FailSt.do
    throw (mkErrorMsg r "While checking _ ↦ _: computed type doesn't match expected type")
  checkElemNu sig ctx (App _ (Var r x) es) ty = FailSt.do
    let Just (v, vTy) = lookupContext ctx x
      | Nothing => FailSt.do
          -- Σ₀ (x : A) Σ₁ ⊦ x ē
          let Just (Empty, i, ty') = lookupSignature !(computeSignature sig) x
            | Just (_, _) => throw (mkErrorMsg r "non-empty signature context not supported yet")
            | Nothing => throw (mkErrorMsg r "Undefined name: \{x}")
          checkElim sig ctx (SignatureVarElim i Terminal) ty' es ty
    checkElim sig ctx v vTy es ty
  checkElemNu sig ctx (App r (NatVal0 x) []) NatTy = return NatVal0
  checkElemNu sig ctx (App r (NatVal1 x) [([], e)]) NatTy = FailSt.do
    e' <- checkElem sig ctx e NatTy
    return (NatVal1 e')
  checkElemNu sig ctx (App r (NatElim _) [([x], schema), ([], z), ([y, h], s), ([], t)]) ty = FailSt.do
    d0 <- numberOfHoles
    schema' <- checkElem sig (Ext ctx x NatTy) schema Universe
    d1 <- numberOfHoles
    z' <- checkElem sig ctx z (ContextSubstElim schema' (Ext Id NatVal0))
    d2 <- numberOfHoles
    let schema' = SignatureSubstElim schema' (WkN $ d2 `minus` d1)
    -- Γ (x : ℕ) ⊦ C type
    -- Γ (x : ℕ) (h : C) ⊦ C (↑², S x₁)
    s' <- checkElem sig (Ext (Ext ctx y NatTy) h schema') s (ContextSubstElim schema' (Ext (WkN 2) (NatVal1 (VarN 1))))
    d3 <- numberOfHoles
    t' <- checkElem sig ctx t NatTy
    d4 <- numberOfHoles
    let schema' = SignatureSubstElim schema' (WkN $ d4 `minus` d2)
    let ty = SignatureSubstElim ty (WkN $ d4 `minus` d0)
    let z' = SignatureSubstElim z' (WkN $ d4 `minus` d2)
    let s' = SignatureSubstElim s' (WkN $ d4 `minus` d3)
    let exp = ContextSubstElim schema' (Ext Id t')
    True <- liftM $ conv exp ty
      | False => throw (mkErrorMsg r "While checking ℕ-elim: computed type doesn't match expected type")
    return (NatElim x schema' z' y h s' t')
  checkElemNu sig ctx (App r (EqVal x) []) (EqTy a b ty) =
    case !(liftM $ conv a b) of
      True => return EqVal
      False => throw (mkErrorMsg r "While checking Refl: computed type doesn't match expected type")
  checkElemNu sig ctx (App _ (NatTy _) []) Universe = return NatTy
  checkElemNu sig ctx (App _ (UniverseTy _) []) Universe = return Universe
  checkElemNu sig ctx (App _ (Hole r x) []) ty = FailSt.do
    registerHole sig r ctx x ty
    return $ SignatureVarElim 0 Id
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
  checkElem : Signature -> Context -> SurfaceTerm -> CoreElem -> CheckM CoreElem
  checkElem sig ctx tm ty = checkElemNu sig ctx tm (runSubst ty)

  public export
  checkTypingSignature : Signature -> Range -> VarName -> SurfaceTerm -> CheckM (Context, VarName, CoreElem)
  checkTypingSignature sig r x tm = FailSt.do
    print_ Debug "About to check \{x}: \{show tm}"
    tm' <- checkElem sig Empty tm Universe
    return (Empty, x, tm')

  public export
  checkLetSignature : Signature -> Range -> VarName -> SurfaceTerm -> SurfaceTerm -> CheckM (Context, VarName, CoreElem, CoreElem)
  checkLetSignature sig r x rhs tm = FailSt.do
    print_ Debug "About to check \{x}: \{show tm}"
    tm' <- checkElem sig Empty tm Universe
    d1 <- numberOfHoles
    rhs' <- checkElem sig Empty rhs tm'
    d2 <- numberOfHoles
    let tm' = SignatureSubstElim tm' (WkN $ d2 `minus` d1)
    return (Empty, x, rhs', tm')

  public export
  checkTopLevel : Signature -> TopLevel -> CheckM (VarName, SignatureEntry)
  checkTopLevel sig (TypingSignature r x ty) = FailSt.do
    (ctx, x, ty) <- checkTypingSignature sig r x ty
    return (x, ElemEntry ctx ty)
  checkTopLevel sig (LetSignature r x rhs ty) = FailSt.do
    (ctx, x, rhs, ty) <- checkLetSignature sig r x rhs ty
    return (x, LetElemEntry ctx rhs ty)

 --  FIX: This is illegal as is, because:
 --  *) checking a signature can create holes hence we can't append the checked definition to the signature prefix
 --  *) checking signature Y and signature X invalidates the the context of X (because more holes get added)
  {- public export
  checkFile : Signature -> List1 TopLevel -> CheckM Signature
  checkFile sig (top ::: []) = FailSt.do
    (x, e) <- checkTopLevel sig top
    return (sig :< (x, e))
  checkFile sig (top ::: top' :: more) = FailSt.do
    (x, e) <- checkTopLevel sig top
    checkFile (sig :< (x, e)) (top' ::: more) -}
