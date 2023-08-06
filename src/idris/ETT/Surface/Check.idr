module ETT.Surface.Check

import Data.Location
import Data.List1
import Data.List
import Data.SnocList
import Data.Fin
import Data.Location

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import ETT.Core.Conversion
import ETT.Core.Language
import ETT.Core.Monad
import ETT.Core.Substitution
import ETT.Core.Pretty
import ETT.Core.Pretty

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
CheckM = M String CheckSt

mkErrorMsg : Range -> String -> String
mkErrorMsg r msg = "\{msg}\n\{show r}"

public export
numberOfHoles : CheckM Nat
numberOfHoles = M.do
  MkCheckSt holes <- get
  return (length holes)

||| Register a new hole with a unique name.
||| Ensures that the name is unique.
registerHole : Signature -> Range -> Context -> VarName -> CoreElem -> CheckM ()
registerHole sig r ctx x tm = M.do
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
computeSignature pr = M.do
  MkCheckSt holes <- get
  return $ pr ++ toSignature holes

liftM : M a -> CheckM a
liftM f = M.do
  st <- get
  mapState (const st) (const ()) f

||| Γ₀ (xᵢ : A) Γ₁ ⊦ xᵢ : A
lookupContext : Context -> VarName -> Maybe (CoreElem, CoreElem)
lookupContext Empty x = Nothing
lookupContext (SignatureVarElim k) x = Nothing
lookupContext (Ext ctx x ty) y = M.do
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
lookupSignature (sig :< (x, CtxEntry)) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, TypeEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, EqTyEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
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

lookupLetSignature : Signature -> VarName -> Maybe (Context, Nat, CoreElem, CoreElem)
lookupLetSignature [<] x = Nothing
lookupLetSignature (sig :< (x, CtxEntry)) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetSignature (sig :< (x, TypeEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetSignature (sig :< (x, EqTyEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
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

mutual
  public export
  inferElimNu : Signature -> Context -> CoreElem -> CoreElem -> Elim -> CheckM (CoreElem, CoreElem)
  inferElimNu sig ctx f fTy [] = M.do
    return (f, fTy)
  inferElimNu sig ctx f (PiTy x a b) (([], e) :: es) = M.do
    d0 <- numberOfHoles
    e' <- checkElem sig ctx e a
    d1 <- numberOfHoles
    let f = SignatureSubstElim f (WkN $ d1 `minus` d0)
    let a = SignatureSubstElim a (WkN $ d1 `minus` d0)
    let b = SignatureSubstElim b (WkN $ d1 `minus` d0)
    inferElim sig ctx (PiElim f x a b e') (ContextSubstElim b (Ext Id e')) es
  inferElimNu sig ctx f fTy (([], e) :: xs) = M.do
    throw "The term is non-checkable (1) \{renderDocTerm !(liftM $ prettyElem (map fst sig) (map fst (tail ctx)) f 0)} : \{renderDocTerm !(liftM $ prettyElem (map fst sig) (map fst (tail ctx)) fTy 0)}"
  inferElimNu sig ctx f fTy ((_, e) :: xs) = throw "The term is non-checkable (2)"

  inferElim : Signature -> Context -> CoreElem -> CoreElem -> Elim -> CheckM (CoreElem, CoreElem)
  inferElim sig ctx f fTy es = inferElimNu sig ctx f (runSubst fTy) es

  public export
  checkElim : Signature -> Context -> CoreElem -> CoreElem -> Elim -> CoreElem -> CheckM CoreElem
  checkElim sig ctx f fTy es exp = M.do
    d0 <- numberOfHoles
    (tm, got) <- inferElim sig ctx f fTy es
    d1 <- numberOfHoles
    let exp = SignatureSubstElim exp (WkN $ d1 `minus` d0)
    True <- liftM $ conv got exp
      | False => throw "The term is non-checkable (expected type doesn't match the inferred)\nExpected: \{renderDocTerm !(liftM $ prettyElem (map fst sig) (map fst (tail ctx)) exp 0)}\nInferred: \{renderDocTerm !(liftM $ prettyElem (map fst sig) (map fst (tail ctx)) got 0)}"
    return tm

  public export
  inferElem : Signature -> Context -> SurfaceTerm -> CheckM (CoreElem, CoreElem)
  inferElem sig ctx pi@(PiTy r x dom cod) = M.do
    tm <- checkElem sig ctx pi Universe
    return (tm, Universe)
  inferElem sig ctx fun@(FunTy r dom cod) = M.do
    tm <- checkElem sig ctx fun Universe
    return (tm, Universe)
  inferElem sig ctx eq@(EqTy r a b ty) = M.do
    tm <- checkElem sig ctx eq Universe
    return (tm, Universe)
  inferElem sig ctx (PiVal r x f) = throw (mkErrorMsg r "Can't infer λ")
  inferElem sig ctx (App r (Var r0 x) es) = M.do
    let Just (v, vTy) = lookupContext ctx x
      | Nothing => M.do
          -- Σ₀ (x : A) Σ₁ ⊦ x ē
          let Just (Empty, i, ty') = lookupSignature !(computeSignature sig) x
            | Just (_, _) => throw (mkErrorMsg r "non-empty signature context not supported yet")
            | Nothing => throw (mkErrorMsg r "Undefined name: \{x}")
          inferElim sig ctx (SignatureVarElim i Terminal) ty' es
    inferElim sig ctx v vTy es
  inferElem sig ctx (App r (PiBeta _) (([x], f) :: ([], e) :: es)) = M.do
    d0 <- numberOfHoles
    (e', eTy) <- inferElem sig ctx e
    d1 <- numberOfHoles
    (f', fTy) <- inferElem sig (Ext ctx x eTy) f
    d2 <- numberOfHoles
    let e' = SignatureSubstElim e' (WkN $ d2 `minus` d1)
    let eTy = SignatureSubstElim eTy (WkN $ d2 `minus` d1)
    inferElim sig ctx EqVal (EqTy (PiElim (PiVal x eTy fTy f') x eTy fTy e') (ContextSubstElim f' (Ext Id e')) (ContextSubstElim fTy (Ext Id e'))) es
  -- ℕ-β-Z (x. A) z (x. h. s) : ℕ-elim (x. A) z (x. h. s) Z ≡ z ∈ A[Z/x]
  inferElem sig ctx (App r (NatBetaZ _) (([x], schema) :: ([], z) :: ([y, h], s) :: es)) = M.do
    schema <- checkElem sig (Ext ctx x NatTy) schema Universe
    d0 <- numberOfHoles
    z <- checkElem sig ctx z (ContextSubstElim schema (Ext Id NatVal0))
    d1 <- numberOfHoles
    let schema = SignatureSubstElim schema (WkN $ d1 `minus` d0)
    s <- checkElem sig (Ext (Ext ctx y NatTy) h schema) s (ContextSubstElim schema (Ext (WkN 2) (NatVal1 (VarN 1))))
    d2 <- numberOfHoles
    let schema = SignatureSubstElim schema (WkN $ d2 `minus` d1)
    let z = SignatureSubstElim z (WkN $ d2 `minus` d1)
    inferElim sig ctx EqVal (EqTy (NatElim x schema z y h s NatVal0) z (ContextSubstElim schema (Ext Id NatVal0))) es
  inferElem sig ctx (AnnotatedPiVal r x ty f) = M.do
    ty <- checkElem sig ctx ty Universe
    d0 <- numberOfHoles
    (f, fTy) <- inferElem sig (Ext ctx x ty) f
    d1 <- numberOfHoles
    let ty = SignatureSubstElim ty (WkN $ d1 `minus` d0)
    return (PiVal x ty fTy f, PiTy x ty fTy)
  inferElem sig ctx (App r (NatElim _) (([x], schema) :: ([], z) :: ([y, h], s) :: ([], t) :: es)) = M.do
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
    let z' = SignatureSubstElim z' (WkN $ d4 `minus` d2)
    let s' = SignatureSubstElim s' (WkN $ d4 `minus` d3)
    let exp = ContextSubstElim schema' (Ext Id t')
    inferElim sig ctx (NatElim x schema' z' y h s' t') exp es
  inferElem sig ctx (App r0 (EqElim _) (([x, h], schema) :: ([], r) :: ([], e) :: es)) = M.do
    (e', eTy) <- inferElem sig ctx e
    d0 <- numberOfHoles
    let EqTy a0 a1 ty = runSubst eTy
      | _ => throw (mkErrorMsg r0 "Last argument of J must be an instance of equality")
    schema' <- checkElem sig (Ext (Ext ctx x ty) h (EqTy (ContextSubstElim a0 Wk) CtxVar (ContextSubstElim ty Wk))) schema Universe
    d1 <- numberOfHoles
    let e' = SignatureSubstElim e' (WkN $ d1 `minus` d0)
    let a0 = SignatureSubstElim a0 (WkN $ d1 `minus` d0)
    let a1 = SignatureSubstElim a1 (WkN $ d1 `minus` d0)
    let ty = SignatureSubstElim ty (WkN $ d1 `minus` d0)
    r' <- checkElem sig ctx r (ContextSubstElim schema' (Ext (Ext Id a0) EqVal))
    d2 <- numberOfHoles
    let e' = SignatureSubstElim e' (WkN $ d2 `minus` d1)
    let a0 = SignatureSubstElim a0 (WkN $ d2 `minus` d1)
    let a1 = SignatureSubstElim a1 (WkN $ d2 `minus` d1)
    let ty = SignatureSubstElim ty (WkN $ d2 `minus` d1)
    inferElim sig ctx r' (ContextSubstElim schema' (Ext (Ext Id a1) e')) es
  inferElem sig ctx (App r (Unfold r0 x) es) = M.do
    let Just (Empty, i, rhs, ty') = lookupLetSignature !(computeSignature sig) x
      | Just (_, _) => throw (mkErrorMsg r "non-empty signature context not supported yet")
      | Nothing => throw (mkErrorMsg r "Undefined name: \{x}")
    inferElim sig ctx EqVal (EqTy (SignatureVarElim i Terminal) rhs ty') es
  inferElem sig ctx (App _ (Tm _ f) es) = M.do
    (f, fTy) <- inferElem sig ctx f
    inferElim sig ctx f fTy es
  inferElem sig ctx tm@(App _ (NatTy _) []) = M.do
    tm <- checkElem sig ctx tm Universe
    return (tm, Universe)
  inferElem sig ctx tm@(App _ (UniverseTy _) []) = M.do
    tm <- checkElem sig ctx tm Universe
    return (tm, Universe)
  inferElem sig ctx tm@(App r (NatVal0 x) []) = M.do
    tm <- checkElem sig ctx tm NatTy
    return (tm, NatTy)
  inferElem sig ctx tm@(App r (NatVal1 x) [([], e)]) = M.do
    tm <- checkElem sig ctx tm NatTy
    return (tm, NatTy)
  inferElem sig ctx tm@(App r head es) = throw (mkErrorMsg (range tm) "While inferring \{show tm}: can't infer")

  public export
  checkElemNu : Signature -> Context -> SurfaceTerm -> CoreElem -> CheckM CoreElem
  checkElemNu sig ctx (PiTy r x a b) Universe = M.do
    a' <- checkElem sig ctx a Universe
    aNHoles <- numberOfHoles
    b' <- checkElem sig (Ext ctx x a') b Universe
    bNHoles <- numberOfHoles
    return (PiTy x (SignatureSubstElim a' (WkN $ bNHoles `minus` aNHoles)) b')
  checkElemNu sig ctx (PiTy r x a b) _ = M.do
    throw (mkErrorMsg r "While checking (_ : _) → _: computed type doesn't match expected type")
  checkElemNu sig ctx (FunTy r a b) Universe = M.do
    a' <- checkElem sig ctx a Universe
    aNHoles <- numberOfHoles
    b' <- checkElem sig ctx b Universe
    bNHoles <- numberOfHoles
    return (PiTy "_" (SignatureSubstElim a' (WkN $ bNHoles `minus` aNHoles)) (ContextSubstElim b' Wk))
  checkElemNu sig ctx (FunTy r a b) _ = M.do
    throw (mkErrorMsg r "While checking _ → _: computed type doesn't match expected type")
  checkElemNu sig ctx (EqTy r a b ty) Universe = M.do
    ty' <- checkElem sig ctx ty Universe
    tyNHoles <- numberOfHoles
    a' <- checkElem sig ctx a ty'
    aNHoles <- numberOfHoles
    b' <- checkElem sig ctx b (SignatureSubstElim ty' (WkN $ aNHoles `minus` tyNHoles))
    bNHoles <- numberOfHoles
    return (EqTy (SignatureSubstElim a' (WkN $ bNHoles `minus` aNHoles)) b' (SignatureSubstElim ty' (WkN $ bNHoles `minus` tyNHoles)))
  checkElemNu sig ctx (EqTy r a b ty) _ = M.do
    throw (mkErrorMsg r "While checking _ ≡ _ ∈ _: computed type doesn't match expected type")
  checkElemNu sig ctx (PiVal r x f) (PiTy _ a b) = M.do
    d0 <- numberOfHoles
    f' <- checkElem sig (Ext ctx x a) f b
    d1 <- numberOfHoles
    return (PiVal x (SignatureSubstElim a (WkN $ d1 `minus` d0)) (SignatureSubstElim b (WkN $ d1 `minus` d0)) f')
  checkElemNu sig ctx (PiVal r x f) _ = M.do
    throw (mkErrorMsg r "While checking _ ↦ _: computed type doesn't match expected type")
  checkElemNu sig ctx (App _ (Var r x) es) ty = M.do
    let Just (v, vTy) = lookupContext ctx x
      | Nothing => M.do
          -- Σ₀ (x : A) Σ₁ ⊦ x ē
          let Just (Empty, i, ty') = lookupSignature !(computeSignature sig) x
            | Just (_, _) => throw (mkErrorMsg r "non-empty signature context not supported yet")
            | Nothing => throw (mkErrorMsg r "Undefined name: \{x}")
          checkElim sig ctx (SignatureVarElim i Terminal) ty' es ty
    checkElim sig ctx v vTy es ty
  checkElemNu sig ctx (App r (NatVal0 x) []) NatTy = return NatVal0
  checkElemNu sig ctx (App r (NatVal1 x) [([], e)]) NatTy = M.do
    e' <- checkElem sig ctx e NatTy
    return (NatVal1 e')
  -- e : A
  -- (x : A) ⊦ f : B
  -- ------------------------------------------
  -- Π-β (x. f) e : (x ↦ f) e ≡ f[e/x] ∈ B[e/x]
  checkElemNu sig ctx (App r (EqVal x) []) (EqTy a b ty) =
    case !(liftM $ conv a b) of
      True => return EqVal
      False => throw (mkErrorMsg r "While checking Refl: computed type doesn't match expected type")
  checkElemNu sig ctx (App _ (NatTy _) []) Universe = return NatTy
  checkElemNu sig ctx (App _ (UniverseTy _) []) Universe = return Universe
  checkElemNu sig ctx (App _ (Hole r x) []) ty = M.do
    registerHole sig r ctx x ty
    return $ SignatureVarElim 0 Id
  checkElemNu sig ctx tm exp = M.do
    d0 <- numberOfHoles
    (tm, got) <- inferElem sig ctx tm
    d1 <- numberOfHoles
    let exp = SignatureSubstElim exp (WkN $ d1 `minus` d0)
    True <- liftM $ conv got exp
      | False => throw "The term is non-checkable (expected type doesn't match the inferred)\nExpected: \{renderDocTerm !(liftM $ prettyElem (map fst sig) (map fst (tail ctx)) exp 0)}\nInferred: \{renderDocTerm !(liftM $ prettyElem (map fst sig) (map fst (tail ctx)) got 0)}"
    return tm

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
  checkTypingSignature sig r x tm = M.do
    print_ Debug STDOUT "About to check \{x}: \{show tm}"
    tm' <- checkElem sig Empty tm Universe
    return (Empty, x, tm')

  public export
  checkLetSignature : Signature -> Range -> VarName -> SurfaceTerm -> SurfaceTerm -> CheckM (Context, VarName, CoreElem, CoreElem)
  checkLetSignature sig r x rhs tm = M.do
    print_ Debug STDOUT "About to check \{x}: \{show tm}"
    tm' <- checkElem sig Empty tm Universe
    d1 <- numberOfHoles
    rhs' <- checkElem sig Empty rhs tm'
    d2 <- numberOfHoles
    let tm' = SignatureSubstElim tm' (WkN $ d2 `minus` d1)
    return (Empty, x, rhs', tm')

  public export
  checkTopLevel : Signature -> TopLevel -> CheckM (VarName, SignatureEntry)
  checkTopLevel sig (TypingSignature r x ty) = M.do
    (ctx, x, ty) <- checkTypingSignature sig r x ty
    return (x, ElemEntry ctx ty)
  checkTopLevel sig (LetSignature r x rhs ty) = M.do
    (ctx, x, rhs, ty) <- checkLetSignature sig r x rhs ty
    return (x, LetElemEntry ctx rhs ty)

 --  FIX: This is illegal as is, because:
 --  *) checking a signature can create holes hence we can't append the checked definition to the signature prefix
 --  *) checking signature Y and signature X invalidates the the context of X (because more holes get added)
  {- public export
  checkFile : Signature -> List1 TopLevel -> CheckM Signature
  checkFile sig (top ::: []) = M.do
    (x, e) <- checkTopLevel sig top
    return (sig :< (x, e))
  checkFile sig (top ::: top' :: more) = M.do
    (x, e) <- checkTopLevel sig top
    checkFile (sig :< (x, e)) (top' ::: more) -}
