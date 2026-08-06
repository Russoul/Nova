module Nova.Kernel.Derivation

-- Phase 1 of the derivation rework (docs/NovaDerivations.txt;
-- phasing and status in docs/NovaPipeline.txt): the trusted core.
-- A candidate DERIVATION of a Foundation judgement is checked by one
-- structural recursion, `conclude` — contexts threaded as inputs,
-- conclusions computed as outputs, no search and no reconstruction.
-- Every constructor below names the Foundation rule it replays (the
-- canonical <class>-<former>-<kind> names); the two admissible
-- schemas (presupposition projection; the nf oracle over the
-- kernel's fuel-bounded normalizer) are marked as such.
--
-- Constructor premise ORDER is delivery order (deliverers first) —
-- noted against Foundation's layout where the two differ. Side
-- conditions are α-comparisons via the derived syntactic equality of
-- the nameless core.
--
-- Phase-1 coverage: the element language WITHOUT the quotient
-- witness rules, the ν layer and the QIIT layer (those follow; the
-- pipeline status tracks the remainder). This module is not yet
-- wired into acceptance — that is phase 2's bridge.

import Data.List
import Data.SnocList

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel

%default covering

-- ===== Judgement bodies (contexts are inputs, never outputs) =====

public export
data Judg : Type where
  ||| Γ ⊦ A type
  JTy : Ty -> Judg
  ||| Γ ⊦ t : A
  JEl : Elem -> Ty -> Judg
  ||| Γ ⊦ A₀ ≐ A₁ type
  JTyEq : Ty -> Ty -> Judg
  ||| Γ ⊦ t₀ ≐ t₁ : A
  JElEq : Elem -> Elem -> Ty -> Judg
  ||| e˲ : Γ ⇒ Δ norm — Δ (the target telescope) is the output
  JSubN : SubNorm -> Ctx -> Judg

export covering
Show Judg where
  show (JTy a) = "⊦ \{show a} type"
  show (JEl t a) = "⊦ \{show t} : \{show a}"
  show (JTyEq a b) = "⊦ \{show a} ≐ \{show b} type"
  show (JElEq t u a) = "⊦ \{show t} ≐ \{show u} : \{show a}"
  show (JSubN es _) = "⊦ subst (\{show (length (toList es))} entries)"

-- ===== Derivations =====

public export
data Deriv : Type where
  -- ----- type formation -----
  DTyZero, DTyOne, DTyNat, DTyUniv, DTyProp : Deriv
  ||| ty-pi: Γ ⊦ A type;  Γ ▷ A ⊦ B type  ⊢  Γ ⊦ A → B type
  DTyPi : Deriv -> Deriv -> Deriv
  ||| ty-sigma
  DTySigma : Deriv -> Deriv -> Deriv
  ||| ty-sum (non-dependent: B over Γ)
  DTySum : Deriv -> Deriv -> Deriv
  ||| ty-el: Γ ⊦ A : 𝕌  ⊢  Γ ⊦ El A type
  DTyEl : Deriv -> Deriv
  ||| ty-prf: Γ ⊦ p : Ω  ⊢  Γ ⊦ Prf p type
  DTyPrf : Deriv -> Deriv
  ||| ty-quot: Γ ⊦ A type;  Γ ▷ A ▷ A[↑] ⊦ R : Ω  ⊢  Γ ⊦ A / R type
  DTyQuot : Deriv -> Deriv -> Deriv
  ||| ty-sig-var / ty-sig-decl (the Σ-lookup decides which): the atom
  ||| is the name; the premise is the normal substitution at the
  ||| entry's context
  DTySig : String -> Deriv -> Deriv

  -- ----- element typing -----
  ||| el-var: Γ ⊦ ☐ₙ : Γ‖ₙ (atom: the index)
  DElVar : Nat -> Deriv
  ||| el-sig-var / el-sig-decl (the Σ-lookup decides which)
  DElSig : String -> Deriv -> Deriv
  ||| code-zero / code-one / code-nat
  DCodeZero, DCodeOne, DCodeNat : Deriv
  ||| code-pi: Γ ⊦ A : 𝕌;  Γ ▷ El A ⊦ B : 𝕌  ⊢  Γ ⊦ A → B : 𝕌
  DCodePi : Deriv -> Deriv -> Deriv
  ||| code-sigma
  DCodeSigma : Deriv -> Deriv -> Deriv
  ||| code-sum (both over Γ)
  DCodeSum : Deriv -> Deriv -> Deriv
  ||| code-quot: Γ ⊦ A : 𝕌;  Γ ▷ El A ▷ (El A)[↑] ⊦ R : Ω
  DCodeQuot : Deriv -> Deriv -> Deriv
  ||| code-eq (the equality PROP): delivery order T, l, r —
  ||| Γ ⊦ T type;  Γ ⊦ l : T;  Γ ⊦ r : T  ⊢  Γ ⊦ (l ≡ r ∈ T) : Ω
  DCodeEq : Deriv -> Deriv -> Deriv -> Deriv
  ||| code-squash: Γ ⊦ A type  ⊢  Γ ⊦ ∥A∥ : Ω
  DCodeSquash : Deriv -> Deriv
  ||| el-zero-e: Γ ⊦ A type;  Γ ⊦ t : 𝟘  ⊢  Γ ⊦ 𝟘-elim t : A
  DElZeroE : Deriv -> Deriv -> Deriv
  ||| el-one-i
  DElOneI : Deriv
  ||| el-nat-z / el-nat-s
  DElNatZ : Deriv
  DElNatS : Deriv -> Deriv
  ||| el-nat-e (motive A is the retained formation premise):
  ||| Γ ▷ ℕ ⊦ A type;  Γ ⊦ z : A[id, Z];  Γ ▷ ℕ ▷ A ⊦ s : A[↑∘↑, S ☐₁];
  ||| Γ ⊦ t : ℕ  ⊢  Γ ⊦ ℕ-elim z s t : A[id, t]
  DElNatE : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-pi-i: Γ ⊦ A type (delivers A);  Γ ▷ A ⊦ f : B
  DElPiI : Deriv -> Deriv -> Deriv
  ||| el-pi-e — delivery order f, e, B (Foundation lists B first):
  ||| Γ ⊦ f : A → B;  Γ ⊦ e : A;  Γ ▷ A ⊦ B type
  DElPiE : Deriv -> Deriv -> Deriv -> Deriv
  ||| el-let: Γ ⊦ a : A;  Γ ▷ A ▷ Prf (☐₀ ≡ a[↑] ∈ A[↑]) ⊦ b : B
  DElLet : Deriv -> Deriv -> Deriv
  ||| el-sigma-i — delivery order a, B, b (Foundation lists B first):
  ||| Γ ⊦ a : A;  Γ ▷ A ⊦ B type;  Γ ⊦ b : B[id, a]
  DElSigmaI : Deriv -> Deriv -> Deriv -> Deriv
  ||| el-sigma-e₁ / el-sigma-e₂
  DElSigmaE1 : Deriv -> Deriv
  DElSigmaE2 : Deriv -> Deriv
  ||| el-sum-i₁: Γ ⊦ a : A (delivers A);  Γ ⊦ B type
  DElSumI1 : Deriv -> Deriv -> Deriv
  ||| el-sum-i₂: Γ ⊦ b : B;  Γ ⊦ A type
  DElSumI2 : Deriv -> Deriv -> Deriv
  ||| el-sum-e (motive C retained) — delivery order t, C, l, r:
  ||| Γ ⊦ t : A ⊎ B;  Γ ▷ A ⊎ B ⊦ C type;
  ||| Γ ▷ A ⊦ l : C[↑, inj₁ ☐₀];  Γ ▷ B ⊦ r : C[↑, inj₂ ☐₀]
  DElSumE : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-squash-i: Γ ⊦ t : A  ⊢  Γ ⊦ ⋆ : Prf ∥A∥
  DElSquashI : Deriv -> Deriv
  ||| el-eq-i: Γ ⊦ a₀ ≐ a₁ : A  ⊢  Γ ⊦ ⋆ : Prf (a₀ ≡ a₁ ∈ A)
  DElEqI : Deriv -> Deriv
  ||| el-ty-coe: Γ ⊦ A₀ ≐ A₁ type;  Γ ⊦ a : A₀  ⊢  Γ ⊦ a : A₁
  DElTyCoe : Deriv -> Deriv -> Deriv

  -- ----- equality: equivalence, coercion, reflection -----
  ||| el-refl (an equivalence-rule instance): from Γ ⊦ a : A
  DElRefl : Deriv -> Deriv
  ||| el-sym
  DElSym : Deriv -> Deriv
  ||| el-trans — the middle subject delivered by both premises,
  ||| α-compared
  DElTrans : Deriv -> Deriv -> Deriv
  ||| ty-refl / ty-sym / ty-trans
  DTyRefl : Deriv -> Deriv
  DTySym : Deriv -> Deriv
  DTyTrans : Deriv -> Deriv -> Deriv
  ||| el-eq-ty-coe: Γ ⊦ A₀ ≐ A₁ type;  Γ ⊦ a₀ ≐ a₁ : A₀
  DElEqTyCoe : Deriv -> Deriv -> Deriv
  ||| el-reflect: Γ ⊦ s : Prf (a₀ ≡ a₁ ∈ A)  ⊢  Γ ⊦ a₀ ≐ a₁ : A
  ||| (the premise must conclude at a literal equality prop — expose
  ||| a squashed or unreduced spelling with DElTyCoe + the oracle
  ||| first)
  DElReflect : Deriv -> Deriv
  ||| el-sig-eq: the atom is the POSITION of the (nameless)
  ||| constraint entry in Σ
  DElSigEq : Nat -> Deriv -> Deriv
  ||| ty-sig-eq
  DTySigEq : Nat -> Deriv -> Deriv

  -- ----- equality: props and η -----
  ||| el-zero-prop / el-one-prop / el-prf-prop
  DElZeroProp : Deriv -> Deriv -> Deriv
  DElOneProp : Deriv -> Deriv -> Deriv
  DElPrfProp : Deriv -> Deriv -> Deriv
  ||| code-prop-eq (propositional extensionality) — delivery order
  ||| p, q, then the two hypothetical proofs:
  ||| Γ ⊦ p : Ω;  Γ ⊦ q : Ω;
  ||| Γ ▷ Prf p ⊦ s : (Prf q)[↑];  Γ ▷ Prf q ⊦ t : (Prf p)[↑]
  DCodePropEq : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-pi-eta: Γ ⊦ f : A → B  ⊢  Γ ⊦ λ (f[↑] ☐₀) ≐ f : A → B
  DElPiEta : Deriv -> Deriv
  ||| el-sigma-eta: Γ ⊦ t : A ⨯ B  ⊢  Γ ⊦ (t.π₁ , t.π₂) ≐ t : A ⨯ B
  DElSigmaEta : Deriv -> Deriv

  -- ----- equality: congruence -----
  ||| el-lam-cong: Γ ⊦ A type (delivers the domain);  Γ ▷ A ⊦ f₀ ≐ f₁ : B
  DElLamCong : Deriv -> Deriv -> Deriv
  ||| el-app-cong — delivery order feq, aeq, B (Foundation lists B
  ||| first): Γ ⊦ f₀ ≐ f₁ : A → B;  Γ ⊦ a₀ ≐ a₁ : A;  Γ ▷ A ⊦ B type
  ||| ⊢  Γ ⊦ f₀ a₀ ≐ f₁ a₁ : B[id, a₁]
  DElAppCong : Deriv -> Deriv -> Deriv -> Deriv
  ||| el-suc-cong
  DElSucCong : Deriv -> Deriv
  ||| el-pair-cong — the family delivered by a formation premise:
  ||| Γ ⊦ a₀ ≐ a₁ : A;  Γ ▷ A ⊦ B type;  Γ ⊦ b₀ ≐ b₁ : B[id, a₁]
  DElPairCong : Deriv -> Deriv -> Deriv -> Deriv
  ||| el-proj₁-cong / el-proj₂-cong
  DElProj1Cong : Deriv -> Deriv
  DElProj2Cong : Deriv -> Deriv
  ||| ty-pi-cong: Γ ⊦ A₀ ≐ A₁ type;  Γ ▷ A₁ ⊦ B₀ ≐ B₁ type
  DTyPiCong : Deriv -> Deriv -> Deriv
  DTySigmaCong : Deriv -> Deriv -> Deriv
  DTySumCong : Deriv -> Deriv -> Deriv
  ||| ty-el-cong: Γ ⊦ a ≐ b : 𝕌
  DTyElCong : Deriv -> Deriv
  ||| ty-prf-cong: Γ ⊦ p ≐ q : Ω
  DTyPrfCong : Deriv -> Deriv

  -- ----- normal substitutions -----
  ||| sub-norm-empty
  DSubNEmpty : Deriv
  ||| sub-norm-ext — delivery order es (delivers the target prefix),
  ||| A (formation over the TARGET prefix), e (side-checked at
  ||| A[e˲]): extends the target telescope
  DSubNExt : Deriv -> Deriv -> Deriv -> Deriv

  -- ----- ADMISSIBLE: presupposition projection -----
  ||| from Γ ⊦ t₀ ≐ t₁ : A conclude Γ ⊦ t₀ : A
  DPresupElL : Deriv -> Deriv
  ||| … conclude Γ ⊦ t₁ : A
  DPresupElR : Deriv -> Deriv
  ||| from Γ ⊦ t : A conclude Γ ⊦ A type
  DPresupElTy : Deriv -> Deriv
  ||| from Γ ⊦ A₀ ≐ A₁ type conclude Γ ⊦ A₀ type
  DPresupTyL : Deriv -> Deriv
  DPresupTyR : Deriv -> Deriv

  -- ----- ADMISSIBLE: the nf oracle -----
  ||| nf-expand: Γ ⊦ t : A  ⊢  Γ ⊦ t ≐ nf(t) : A
  DNfExpand : Deriv -> Deriv
  ||| nf-expand-ty
  DNfExpandTy : Deriv -> Deriv
  ||| nf-eq: Γ ⊦ t₀ : A;  Γ ⊦ t₁ : A;  nf(t₀) = nf(t₁)
  DNfEq : Deriv -> Deriv -> Deriv
  ||| nf-eq-ty
  DNfEqTy : Deriv -> Deriv -> Deriv

-- ===== Premise-class extraction =====

needTy : Judg -> KM Ty
needTy (JTy a) = pure a
needTy j = kerr "derivation: expected a formation premise"

needEl : Judg -> KM (Elem, Ty)
needEl (JEl t a) = pure (t, a)
needEl j = kerr "derivation: expected a typing premise"

needTyEq : Judg -> KM (Ty, Ty)
needTyEq (JTyEq a b) = pure (a, b)
needTyEq j = kerr "derivation: expected a type-equation premise"

needElEq : Judg -> KM (Elem, Elem, Ty)
needElEq (JElEq t u a) = pure (t, u, a)
needElEq j = kerr "derivation: expected an element-equation premise"

needSubN : Judg -> KM (SubNorm, Ctx)
needSubN (JSubN es delta) = pure (es, delta)
needSubN j = kerr "derivation: expected a normal-substitution premise"

||| The side-condition α-comparison, with the rule named in the
||| rejection.
alphaTy : String -> Ty -> Ty -> KM ()
alphaTy rule a b =
  if a == b then pure ()
  else kerr "derivation: \{rule}: type mismatch [\{show a} VS \{show b}]"

alphaEl : String -> Elem -> Elem -> KM ()
alphaEl rule a b =
  if a == b then pure ()
  else kerr "derivation: \{rule}: element mismatch [\{show a} VS \{show b}]"

wkTy : Ty -> Ty
wkTy a = substTy a Wk

||| Γ‖ₙ (a private copy, disambiguated from the kernel's).
ctxAt : Ctx -> Nat -> Maybe Ty
ctxAt [<] _ = Nothing
ctxAt (rest :< ty) Z = Just (substTy ty Wk)
ctxAt (rest :< ty) (S n) = map (\t => substTy t Wk) (ctxAt rest n)

wkEl : Elem -> Elem
wkEl e = substElem e Wk

-- ===== The checker =====

export
conclude : Sig -> Ctx -> Deriv -> KM Judg

-- type formation
conclude sig ctx DTyZero = pure (JTy Ty.ZeroTy)
conclude sig ctx DTyOne = pure (JTy Ty.OneTy)
conclude sig ctx DTyNat = pure (JTy Ty.NatTy)
conclude sig ctx DTyUniv = pure (JTy Ty.UniverseTy)
conclude sig ctx DTyProp = pure (JTy Ty.PropTy)
conclude sig ctx (DTyPi dA dB) = do
  a <- conclude sig ctx dA >>= needTy
  b <- conclude sig (ctx :< a) dB >>= needTy
  pure (JTy (Ty.PiTy a b))
conclude sig ctx (DTySigma dA dB) = do
  a <- conclude sig ctx dA >>= needTy
  b <- conclude sig (ctx :< a) dB >>= needTy
  pure (JTy (Ty.SigmaTy a b))
conclude sig ctx (DTySum dA dB) = do
  a <- conclude sig ctx dA >>= needTy
  b <- conclude sig ctx dB >>= needTy
  pure (JTy (Ty.SumTy a b))
conclude sig ctx (DTyEl dA) = do
  (a, ty) <- conclude sig ctx dA >>= needEl
  alphaTy "ty-el" ty Ty.UniverseTy
  pure (JTy (El a))
conclude sig ctx (DTyPrf dP) = do
  (p, ty) <- conclude sig ctx dP >>= needEl
  alphaTy "ty-prf" ty Ty.PropTy
  pure (JTy (Prf p))
conclude sig ctx (DTyQuot dA dR) = do
  a <- conclude sig ctx dA >>= needTy
  (r, rty) <- conclude sig (ctx :< a :< wkTy a) dR >>= needEl
  alphaTy "ty-quot" rty Ty.PropTy
  pure (JTy (Ty.Quotient a r))
conclude sig ctx (DTySig x dSub) = do
  (es, delta) <- conclude sig ctx dSub >>= needSubN
  case sigLookup x sig of
    Just (SigTyDef gamma _ a) => do
      alphaCtx "ty-sig-var" delta gamma
      pure (JTy (substTy a (embed es)))
    Just (SigTyDecl gamma _) => do
      alphaCtx "ty-sig-decl" delta gamma
      pure (JTy (Ty.SigVar x es))
    _ => kerr "derivation: ty-sig: no type entry '\{x}'"
 where
  alphaCtx : String -> Ctx -> Ctx -> KM ()
  alphaCtx rule d g =
    if d == g then pure ()
    else kerr "derivation: \{rule}: entry context mismatch"

-- element typing
conclude sig ctx (DElVar n) =
  case ctxAt ctx n of
    Just a => pure (JEl (CtxVar n) a)
    Nothing => kerr "derivation: el-var: index out of range"
conclude sig ctx (DElSig x dSub) = do
  (es, delta) <- conclude sig ctx dSub >>= needSubN
  case sigLookup x sig of
    Just (SigDef gamma _ _ a) => do
      if delta == gamma then pure ()
        else kerr "derivation: el-sig-var: entry context mismatch"
      pure (JEl (Elem.SigVar x es) (substTy a (embed es)))
    Just (SigDecl gamma _ a) => do
      if delta == gamma then pure ()
        else kerr "derivation: el-sig-decl: entry context mismatch"
      pure (JEl (Elem.SigVar x es) (substTy a (embed es)))
    _ => kerr "derivation: el-sig: no term entry '\{x}'"
conclude sig ctx DCodeZero = pure (JEl Elem.ZeroTy Ty.UniverseTy)
conclude sig ctx DCodeOne = pure (JEl Elem.OneTy Ty.UniverseTy)
conclude sig ctx DCodeNat = pure (JEl Elem.NatTy Ty.UniverseTy)
conclude sig ctx (DCodePi dA dB) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  alphaTy "code-pi" aty Ty.UniverseTy
  (b, bty) <- conclude sig (ctx :< El a) dB >>= needEl
  alphaTy "code-pi" bty Ty.UniverseTy
  pure (JEl (Elem.PiTy a b) Ty.UniverseTy)
conclude sig ctx (DCodeSigma dA dB) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  alphaTy "code-sigma" aty Ty.UniverseTy
  (b, bty) <- conclude sig (ctx :< El a) dB >>= needEl
  alphaTy "code-sigma" bty Ty.UniverseTy
  pure (JEl (Elem.SigmaTy a b) Ty.UniverseTy)
conclude sig ctx (DCodeSum dA dB) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  alphaTy "code-sum" aty Ty.UniverseTy
  (b, bty) <- conclude sig ctx dB >>= needEl
  alphaTy "code-sum" bty Ty.UniverseTy
  pure (JEl (Elem.SumTy a b) Ty.UniverseTy)
conclude sig ctx (DCodeQuot dA dR) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  alphaTy "code-quot" aty Ty.UniverseTy
  (r, rty) <- conclude sig (ctx :< El a :< wkTy (El a)) dR >>= needEl
  alphaTy "code-quot" rty Ty.PropTy
  pure (JEl (Elem.QuotTy a r) Ty.UniverseTy)
conclude sig ctx (DCodeEq dT dL dR) = do
  t <- conclude sig ctx dT >>= needTy
  (l, lty) <- conclude sig ctx dL >>= needEl
  alphaTy "code-eq" lty t
  (r, rty) <- conclude sig ctx dR >>= needEl
  alphaTy "code-eq" rty t
  pure (JEl (Elem.EqTy l r t) Ty.PropTy)
conclude sig ctx (DCodeSquash dA) = do
  a <- conclude sig ctx dA >>= needTy
  pure (JEl (Squash a) Ty.PropTy)
conclude sig ctx (DElZeroE dA dT) = do
  a <- conclude sig ctx dA >>= needTy
  (t, tty) <- conclude sig ctx dT >>= needEl
  alphaTy "el-zero-e" tty Ty.ZeroTy
  pure (JEl (ZeroElim t) a)
conclude sig ctx DElOneI = pure (JEl OneIntro Ty.OneTy)
conclude sig ctx DElNatZ = pure (JEl NatIntro0 Ty.NatTy)
conclude sig ctx (DElNatS dT) = do
  (t, tty) <- conclude sig ctx dT >>= needEl
  alphaTy "el-nat-s" tty Ty.NatTy
  pure (JEl (NatIntro1 t) Ty.NatTy)
conclude sig ctx (DElNatE dMot dZ dS dT) = do
  mot <- conclude sig (ctx :< Ty.NatTy) dMot >>= needTy
  (z, zty) <- conclude sig ctx dZ >>= needEl
  alphaTy "el-nat-e (z)" zty (substTy mot (Ext Id NatIntro0))
  (s, sty) <- conclude sig (ctx :< Ty.NatTy :< mot) dS >>= needEl
  alphaTy "el-nat-e (s)" sty
    (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
  (t, tty) <- conclude sig ctx dT >>= needEl
  alphaTy "el-nat-e (t)" tty Ty.NatTy
  pure (JEl (NatElim z s t) (substTy mot (Ext Id t)))
conclude sig ctx (DElPiI dA dF) = do
  a <- conclude sig ctx dA >>= needTy
  (f, b) <- conclude sig (ctx :< a) dF >>= needEl
  pure (JEl (PiIntro f) (Ty.PiTy a b))
conclude sig ctx (DElPiE dF dE dB) = do
  (f, fty) <- conclude sig ctx dF >>= needEl
  case fty of
    Ty.PiTy a b => do
      (e, ety) <- conclude sig ctx dE >>= needEl
      alphaTy "el-pi-e (arg)" ety a
      b' <- conclude sig (ctx :< a) dB >>= needTy
      alphaTy "el-pi-e (cod)" b' b
      pure (JEl (PiApp f e) (substTy b (Ext Id e)))
    _ => kerr "derivation: el-pi-e: function premise not at a Π type"
conclude sig ctx (DElLet dA dB) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  let hyp = Prf (Elem.EqTy (CtxVar 0) (wkEl a) (wkTy aty))
  (b, bty) <- conclude sig (ctx :< aty :< hyp) dB >>= needEl
  pure (JEl (Let a b) (substTy bty (Ext (Ext Id a) Star)))
conclude sig ctx (DElSigmaI dA dB dV) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  b <- conclude sig (ctx :< aty) dB >>= needTy
  (v, vty) <- conclude sig ctx dV >>= needEl
  alphaTy "el-sigma-i" vty (substTy b (Ext Id a))
  pure (JEl (SigmaIntro a v) (Ty.SigmaTy aty b))
conclude sig ctx (DElSigmaE1 dT) = do
  (t, tty) <- conclude sig ctx dT >>= needEl
  case tty of
    Ty.SigmaTy a _ => pure (JEl (SigmaElim1 t) a)
    _ => kerr "derivation: el-sigma-e₁: premise not at a ⨯ type"
conclude sig ctx (DElSigmaE2 dT) = do
  (t, tty) <- conclude sig ctx dT >>= needEl
  case tty of
    Ty.SigmaTy _ b => pure (JEl (SigmaElim2 t) (substTy b (Ext Id (SigmaElim1 t))))
    _ => kerr "derivation: el-sigma-e₂: premise not at a ⨯ type"
conclude sig ctx (DElSumI1 dA dB) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  b <- conclude sig ctx dB >>= needTy
  pure (JEl (Inj1 a) (Ty.SumTy aty b))
conclude sig ctx (DElSumI2 dB dA) = do
  (b, bty) <- conclude sig ctx dB >>= needEl
  a <- conclude sig ctx dA >>= needTy
  pure (JEl (Inj2 b) (Ty.SumTy a bty))
conclude sig ctx (DElSumE dT dC dL dR) = do
  (t, tty) <- conclude sig ctx dT >>= needEl
  case tty of
    Ty.SumTy a b => do
      c <- conclude sig (ctx :< Ty.SumTy a b) dC >>= needTy
      (l, lty) <- conclude sig (ctx :< a) dL >>= needEl
      alphaTy "el-sum-e (l)" lty (substTy c (Ext Wk (Inj1 (CtxVar 0))))
      (r, rty) <- conclude sig (ctx :< b) dR >>= needEl
      alphaTy "el-sum-e (r)" rty (substTy c (Ext Wk (Inj2 (CtxVar 0))))
      pure (JEl (SumElim l r t) (substTy c (Ext Id t)))
    _ => kerr "derivation: el-sum-e: scrutinee not at a ⊎ type"
conclude sig ctx (DElSquashI dT) = do
  (_, a) <- conclude sig ctx dT >>= needEl
  pure (JEl Star (Prf (Squash a)))
conclude sig ctx (DElEqI dEq) = do
  (a0, a1, a) <- conclude sig ctx dEq >>= needElEq
  pure (JEl Star (Prf (Elem.EqTy a0 a1 a)))
conclude sig ctx (DElTyCoe dEq dA) = do
  (a0, a1) <- conclude sig ctx dEq >>= needTyEq
  (a, aty) <- conclude sig ctx dA >>= needEl
  alphaTy "el-ty-coe" aty a0
  pure (JEl a a1)

-- equality: equivalence, coercion, reflection
conclude sig ctx (DElRefl dT) = do
  (t, a) <- conclude sig ctx dT >>= needEl
  pure (JElEq t t a)
conclude sig ctx (DElSym d) = do
  (t0, t1, a) <- conclude sig ctx d >>= needElEq
  pure (JElEq t1 t0 a)
conclude sig ctx (DElTrans d01 d12) = do
  (t0, t1, a) <- conclude sig ctx d01 >>= needElEq
  (t1', t2, a') <- conclude sig ctx d12 >>= needElEq
  alphaEl "el-trans (middle)" t1' t1
  alphaTy "el-trans (type)" a' a
  pure (JElEq t0 t2 a)
conclude sig ctx (DTyRefl dT) = do
  a <- conclude sig ctx dT >>= needTy
  pure (JTyEq a a)
conclude sig ctx (DTySym d) = do
  (a0, a1) <- conclude sig ctx d >>= needTyEq
  pure (JTyEq a1 a0)
conclude sig ctx (DTyTrans d01 d12) = do
  (a0, a1) <- conclude sig ctx d01 >>= needTyEq
  (a1', a2) <- conclude sig ctx d12 >>= needTyEq
  alphaTy "ty-trans (middle)" a1' a1
  pure (JTyEq a0 a2)
conclude sig ctx (DElEqTyCoe dTyEq dEq) = do
  (a0, a1) <- conclude sig ctx dTyEq >>= needTyEq
  (t0, t1, a) <- conclude sig ctx dEq >>= needElEq
  alphaTy "el-eq-ty-coe" a a0
  pure (JElEq t0 t1 a1)
conclude sig ctx (DElReflect dS) = do
  (_, sty) <- conclude sig ctx dS >>= needEl
  case sty of
    Prf (Elem.EqTy a0 a1 a) => pure (JElEq a0 a1 a)
    _ => kerr "derivation: el-reflect: premise not at a literal equality prop"
conclude sig ctx (DElSigEq pos dSub) = do
  (es, delta) <- conclude sig ctx dSub >>= needSubN
  case getAt pos (toList sig) of
    Just (SigEq gamma a0 a1 a) => do
      if delta == gamma then pure ()
        else kerr "derivation: el-sig-eq: entry context mismatch"
      pure (JElEq (substElem a0 (embed es)) (substElem a1 (embed es))
                  (substTy a (embed es)))
    _ => kerr "derivation: el-sig-eq: no constraint entry at position \{show pos}"
conclude sig ctx (DTySigEq pos dSub) = do
  (es, delta) <- conclude sig ctx dSub >>= needSubN
  case getAt pos (toList sig) of
    Just (SigTyEq gamma a0 a1) => do
      if delta == gamma then pure ()
        else kerr "derivation: ty-sig-eq: entry context mismatch"
      pure (JTyEq (substTy a0 (embed es)) (substTy a1 (embed es)))
    _ => kerr "derivation: ty-sig-eq: no type constraint at position \{show pos}"

-- equality: props and η
conclude sig ctx (DElZeroProp d0 d1) = do
  (t0, ty0) <- conclude sig ctx d0 >>= needEl
  alphaTy "el-zero-prop" ty0 Ty.ZeroTy
  (t1, ty1) <- conclude sig ctx d1 >>= needEl
  alphaTy "el-zero-prop" ty1 Ty.ZeroTy
  pure (JElEq t0 t1 Ty.ZeroTy)
conclude sig ctx (DElOneProp d0 d1) = do
  (t0, ty0) <- conclude sig ctx d0 >>= needEl
  alphaTy "el-one-prop" ty0 Ty.OneTy
  (t1, ty1) <- conclude sig ctx d1 >>= needEl
  alphaTy "el-one-prop" ty1 Ty.OneTy
  pure (JElEq t0 t1 Ty.OneTy)
conclude sig ctx (DElPrfProp d0 d1) = do
  (t0, ty0) <- conclude sig ctx d0 >>= needEl
  case ty0 of
    Prf p => do
      (t1, ty1) <- conclude sig ctx d1 >>= needEl
      alphaTy "el-prf-prop" ty1 (Prf p)
      pure (JElEq t0 t1 (Prf p))
    _ => kerr "derivation: el-prf-prop: premise not at a Prf type"
conclude sig ctx (DCodePropEq dP dQ dS dT) = do
  (p, pty) <- conclude sig ctx dP >>= needEl
  alphaTy "code-prop-eq" pty Ty.PropTy
  (q, qty) <- conclude sig ctx dQ >>= needEl
  alphaTy "code-prop-eq" qty Ty.PropTy
  (_, sty) <- conclude sig (ctx :< Prf p) dS >>= needEl
  alphaTy "code-prop-eq (→)" sty (wkTy (Prf q))
  (_, tty) <- conclude sig (ctx :< Prf q) dT >>= needEl
  alphaTy "code-prop-eq (←)" tty (wkTy (Prf p))
  pure (JElEq p q Ty.PropTy)
conclude sig ctx (DElPiEta dF) = do
  (f, fty) <- conclude sig ctx dF >>= needEl
  case fty of
    Ty.PiTy a b =>
      pure (JElEq (PiIntro (PiApp (wkEl f) (CtxVar 0))) f (Ty.PiTy a b))
    _ => kerr "derivation: el-pi-eta: premise not at a Π type"
conclude sig ctx (DElSigmaEta dT) = do
  (t, tty) <- conclude sig ctx dT >>= needEl
  case tty of
    Ty.SigmaTy a b =>
      pure (JElEq (SigmaIntro (SigmaElim1 t) (SigmaElim2 t)) t (Ty.SigmaTy a b))
    _ => kerr "derivation: el-sigma-eta: premise not at a ⨯ type"

-- equality: congruence
conclude sig ctx (DElLamCong dA dF) = do
  a <- conclude sig ctx dA >>= needTy
  (f0, f1, b) <- conclude sig (ctx :< a) dF >>= needElEq
  pure (JElEq (PiIntro f0) (PiIntro f1) (Ty.PiTy a b))
conclude sig ctx (DElAppCong dF dA dB) = do
  (f0, f1, fty) <- conclude sig ctx dF >>= needElEq
  case fty of
    Ty.PiTy a b => do
      (a0, a1, aty) <- conclude sig ctx dA >>= needElEq
      alphaTy "el-app-cong (arg)" aty a
      b' <- conclude sig (ctx :< a) dB >>= needTy
      alphaTy "el-app-cong (cod)" b' b
      pure (JElEq (PiApp f0 a0) (PiApp f1 a1) (substTy b (Ext Id a1)))
    _ => kerr "derivation: el-app-cong: premise not at a Π type"
conclude sig ctx (DElSucCong d) = do
  (t0, t1, a) <- conclude sig ctx d >>= needElEq
  alphaTy "el-suc-cong" a Ty.NatTy
  pure (JElEq (NatIntro1 t0) (NatIntro1 t1) Ty.NatTy)
conclude sig ctx (DElPairCong dA dB dV) = do
  (a0, a1, aty) <- conclude sig ctx dA >>= needElEq
  b <- conclude sig (ctx :< aty) dB >>= needTy
  (b0, b1, vty) <- conclude sig ctx dV >>= needElEq
  alphaTy "el-pair-cong" vty (substTy b (Ext Id a1))
  pure (JElEq (SigmaIntro a0 b0) (SigmaIntro a1 b1) (Ty.SigmaTy aty b))
conclude sig ctx (DElProj1Cong d) = do
  (t0, t1, tty) <- conclude sig ctx d >>= needElEq
  case tty of
    Ty.SigmaTy a _ => pure (JElEq (SigmaElim1 t0) (SigmaElim1 t1) a)
    _ => kerr "derivation: el-proj₁-cong: premise not at a ⨯ type"
conclude sig ctx (DElProj2Cong d) = do
  (t0, t1, tty) <- conclude sig ctx d >>= needElEq
  case tty of
    Ty.SigmaTy _ b =>
      pure (JElEq (SigmaElim2 t0) (SigmaElim2 t1)
                  (substTy b (Ext Id (SigmaElim1 t1))))
    _ => kerr "derivation: el-proj₂-cong: premise not at a ⨯ type"
conclude sig ctx (DTyPiCong dD dC) = do
  (a0, a1) <- conclude sig ctx dD >>= needTyEq
  (b0, b1) <- conclude sig (ctx :< a1) dC >>= needTyEq
  pure (JTyEq (Ty.PiTy a0 b0) (Ty.PiTy a1 b1))
conclude sig ctx (DTySigmaCong dD dC) = do
  (a0, a1) <- conclude sig ctx dD >>= needTyEq
  (b0, b1) <- conclude sig (ctx :< a1) dC >>= needTyEq
  pure (JTyEq (Ty.SigmaTy a0 b0) (Ty.SigmaTy a1 b1))
conclude sig ctx (DTySumCong dL dR) = do
  (a0, a1) <- conclude sig ctx dL >>= needTyEq
  (b0, b1) <- conclude sig ctx dR >>= needTyEq
  pure (JTyEq (Ty.SumTy a0 b0) (Ty.SumTy a1 b1))
conclude sig ctx (DTyElCong d) = do
  (a, b, ty) <- conclude sig ctx d >>= needElEq
  alphaTy "ty-el-cong" ty Ty.UniverseTy
  pure (JTyEq (El a) (El b))
conclude sig ctx (DTyPrfCong d) = do
  (p, q, ty) <- conclude sig ctx d >>= needElEq
  alphaTy "ty-prf-cong" ty Ty.PropTy
  pure (JTyEq (Prf p) (Prf q))

-- normal substitutions
conclude sig ctx DSubNEmpty = pure (JSubN [<] [<])
conclude sig ctx (DSubNExt dEs dA dE) = do
  (es, delta) <- conclude sig ctx dEs >>= needSubN
  a <- conclude sig delta dA >>= needTy
  (e, ety) <- conclude sig ctx dE >>= needEl
  alphaTy "sub-norm-ext" ety (substTy a (embed es))
  pure (JSubN (es :< e) (delta :< a))

-- ADMISSIBLE: presupposition projection
conclude sig ctx (DPresupElL d) = do
  (t0, _, a) <- conclude sig ctx d >>= needElEq
  pure (JEl t0 a)
conclude sig ctx (DPresupElR d) = do
  (_, t1, a) <- conclude sig ctx d >>= needElEq
  pure (JEl t1 a)
conclude sig ctx (DPresupElTy d) = do
  (_, a) <- conclude sig ctx d >>= needEl
  pure (JTy a)
conclude sig ctx (DPresupTyL d) = do
  (a0, _) <- conclude sig ctx d >>= needTyEq
  pure (JTy a0)
conclude sig ctx (DPresupTyR d) = do
  (_, a1) <- conclude sig ctx d >>= needTyEq
  pure (JTy a1)

-- ADMISSIBLE: the nf oracle (the typing premise is load-bearing —
-- docs/NovaDerivations.txt)
conclude sig ctx (DNfExpand d) = do
  (t, a) <- conclude sig ctx d >>= needEl
  t' <- kElem sig t
  pure (JElEq t t' a)
conclude sig ctx (DNfExpandTy d) = do
  a <- conclude sig ctx d >>= needTy
  a' <- kTy sig a
  pure (JTyEq a a')
conclude sig ctx (DNfEq d0 d1) = do
  (t0, a) <- conclude sig ctx d0 >>= needEl
  (t1, a') <- conclude sig ctx d1 >>= needEl
  alphaTy "nf-eq" a' a
  n0 <- kElem sig t0
  n1 <- kElem sig t1
  alphaEl "nf-eq" n0 n1
  pure (JElEq t0 t1 a)
conclude sig ctx (DNfEqTy d0 d1) = do
  a0 <- conclude sig ctx d0 >>= needTy
  a1 <- conclude sig ctx d1 >>= needTy
  n0 <- kTy sig a0
  n1 <- kTy sig a1
  alphaTy "nf-eq-ty" n0 n1
  pure (JTyEq a0 a1)

-- ===== Entry point =====

||| Check a derivation in the empty context with the given fuel;
||| Left is the rejection reason (fuel exhaustion included).
export
concludeItem : Sig -> Nat -> Deriv -> Either KErr Judg
concludeItem sig fuel d = map fst (runKM (conclude sig [<] d) fuel)
