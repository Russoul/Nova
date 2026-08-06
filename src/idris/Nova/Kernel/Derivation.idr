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
import Nova.Kernel.QIIT
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
  ||| Δ ctx — the formed context is the output (the ambient input is
  ||| irrelevant to this class)
  JCtx : Ctx -> Judg
  ||| σ : Γ ⇒ Δ — Γ is the ambient input, Δ the output
  JSub : Sub -> Ctx -> Judg
  ||| Γ ⊦ 𝔽 poly
  JPoly : Poly -> Judg
  ||| Γ ⊦ 𝒮 qsig
  JQSig : QSig -> Judg

export covering
Show Judg where
  show (JTy a) = "⊦ \{show a} type"
  show (JEl t a) = "⊦ \{show t} : \{show a}"
  show (JTyEq a b) = "⊦ \{show a} ≐ \{show b} type"
  show (JElEq t u a) = "⊦ \{show t} ≐ \{show u} : \{show a}"
  show (JSubN es _) = "⊦ subst (\{show (length (toList es))} entries)"
  show (JCtx d) = "⊦ ctx (\{show (length d)} entries)"
  show (JSub s _) = "⊦ \{show s} sub"
  show (JPoly f) = "⊦ \{show f} poly"
  show (JQSig sg) = "⊦ qsig (\{show (length sg)} entries)"

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

  -- ----- quotients -----
  ||| el-quot-i — delivery order a (delivers A), R:
  ||| Γ ⊦ a : A;  Γ ▷ A ▷ A[↑] ⊦ R : Ω  ⊢  Γ ⊦ class a : A / R
  DElQuotI : Deriv -> Deriv -> Deriv
  ||| el-quot-eq — delivery order a, b, R, r:
  ||| Γ ⊦ r : Prf R[id, a, b]  ⊢  Γ ⊦ class a ≐ class b : A / R
  DElQuotEq : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-quot-e (motive B retained) — delivery order q (delivers
  ||| A / R), B, f, the well-definedness equation:
  ||| Γ ▷ (A/R) ⊦ B type;  Γ ▷ A ⊦ f : B[↑, class ☐₀];
  ||| Γ ▷ A ▷ A[↑] ▷ Prf R ⊦ f[↑∘↑∘↑, ☐₂] ≐ f[↑∘↑∘↑, ☐₁]
  |||   : B[↑∘↑∘↑, class ☐₂]
  DElQuotE : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-quot-eta — delivery order q, B, g, f, well-definedness,
  ||| agreement (Γ ▷ A ⊦ g[↑, class ☐₀] ≐ f : B[↑, class ☐₀]):
  ||| concludes g[id, q] ≐ quot-elim f q : B[id, q]
  DElQuotEta : Deriv -> Deriv -> Deriv -> Deriv -> Deriv -> Deriv -> Deriv

  -- ----- the remaining η rules (A5's retirement) -----
  ||| el-nat-eta (motive A) — premises in Foundation's order:
  ||| A; f₀; f₁ (over Γ ▷ ℕ); z; s; the Z-agreement
  ||| f₀[id,Z] ≐ f₁[id,Z]; the two S-agreements
  ||| fᵢ[↑, S ☐₀] ≐ s[id, fᵢ]; t  ⊢  f₀[id,t] ≐ f₁[id,t] : A[id,t]
  DElNatEta : Deriv -> Deriv -> Deriv -> Deriv -> Deriv ->
              Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-sum-eta (motive C) — delivery order t (delivers A ⊎ B), C,
  ||| g, l, r, the two agreements g[↑, injᵢ ☐₀] ≐ l/r:
  ||| concludes g[id, t] ≐ ⊎-elim l r t : C[id, t]
  DElSumEta : Deriv -> Deriv -> Deriv -> Deriv -> Deriv ->
              Deriv -> Deriv -> Deriv

  -- ----- contexts and substitutions -----
  ||| ctx-empty / ctx-ext (the formed context is the OUTPUT; the
  ||| formation premise runs under the prefix being extended)
  DCtxEmpty : Deriv
  DCtxExt : Deriv -> Deriv -> Deriv
  ||| sub-empty: · : Γ ⇒ ε
  DSubEmpty : Deriv
  ||| sub-id: id : Γ ⇒ Γ
  DSubId : Deriv
  ||| sub-wk: ↑ : Γ ▷ A ⇒ Γ (the ambient must be an extension)
  DSubWk : Deriv
  ||| sub-ext — delivery order σ (delivers Γ₁), A (over Γ₁), t
  ||| side-checked at A[σ]:  (σ, t) : Γ ⇒ Γ₁ ▷ A
  DSubExt : Deriv -> Deriv -> Deriv -> Deriv
  ||| sub-comp — delivery order σ : Γ ⇒ Γ₁ (ambient), τ : Γ₁ ⇒ Γ₂:
  ||| τ ∘ σ : Γ ⇒ Γ₂
  DSubComp : Deriv -> Deriv -> Deriv
  ||| el-sub-cong-fix (admissible in Foundation, adopted): σ delivers
  ||| Γ₁; the equation lives over Γ₁; concludes it substituted
  DElSubCongFix : Deriv -> Deriv -> Deriv
  ||| ty-sub-cong-fix
  DTySubCongFix : Deriv -> Deriv -> Deriv

  -- ----- the ν layer -----
  ||| poly formation: the polynomial is subject-atom data; the listed
  ||| derivations check its embedded pieces in binder order (codes at
  ||| 𝕌, the context growing under El-binders) — Foundation's poly-*
  ||| rules composed syntax-directedly
  DPolyK : Poly -> List Deriv -> Deriv
  ||| ty-nu / code-nu
  DTyNu : Deriv -> Deriv
  DCodeNu : Deriv -> Deriv
  ||| el-nu-e: Γ ⊦ 𝔽 poly;  Γ ⊦ t : ν 𝔽  ⊢  Γ ⊦ out t : El ⌊𝔽⌋(ν 𝔽)
  DElNuE : Deriv -> Deriv -> Deriv
  ||| el-nu-i: Γ ⊦ 𝔽 poly;  Γ ⊦ a : 𝕌;  Γ ▷ El a ⊦ f : El ⌊𝔽⌋(a)[↑];
  ||| Γ ⊦ x : El a  ⊢  Γ ⊦ corec 𝔽 a f x : ν 𝔽
  DElNuI : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-nu-coind — delivery order 𝔽, t₀, t₁, R (over ▷ν𝔽▷(ν𝔽)[↑]),
  ||| p : Prf R[id,t₀,t₁], q (the one-step closure at lift_𝔽(R)):
  ||| concludes t₀ ≐ t₁ : ν 𝔽
  DElNuCoind : Deriv -> Deriv -> Deriv -> Deriv -> Deriv -> Deriv -> Deriv

  -- ----- the QIIT layer -----
  ||| Γ ⊦ 𝒮 qsig — INTERIM: checked by the kernel's existing qctx
  ||| walk (kQSigCheck, itself in today's trusted base and mirroring
  ||| Foundation's qctx/qty/qtm rules; its embedded Nova pieces go
  ||| through the A4 tiny checker). The demand-driven walk — one
  ||| subderivation per embedded piece — is the outstanding phase-1
  ||| item (docs/NovaPipeline.txt status).
  DQSigK : QSig -> Deriv
  ||| sort-instance formation Γ ⊦ 𝒮.𝕤 ē type — the spine entrywise
  ||| at the reflected arity telescope
  DTyQSort : Nat -> Deriv -> List Deriv -> Deriv
  ||| code-qiit (small signatures only)
  DCodeQSort : Nat -> Deriv -> List Deriv -> Deriv
  ||| el-qiit-intro: the constructor spine entrywise; concludes at
  ||| the point's sort instance
  DQCtor : Nat -> Deriv -> List Deriv -> Deriv
  ||| el-qiit-elim — signature premise, then per sort a motive
  ||| formation (under its reflected telescope plus the sort's self
  ||| entry), per point a method typing (at its ᴰ method type), per
  ||| equation a COHERENCE EQUALITY DERIVATION (under the entry's
  ||| ᴰ-telescope — A4's β-only restriction retired), then the index
  ||| spine and the scrutinee
  DQElim : Nat -> Deriv -> List Deriv -> List Deriv -> List Deriv ->
           List Deriv -> Deriv -> Deriv
  ||| el-qiit-path: the imposed equation at the given spine
  DQPath : Nat -> Deriv -> List Deriv -> Deriv

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


needCtx : Judg -> KM Ctx
needCtx (JCtx g) = pure g
needCtx j = kerr "derivation: expected a context-formation premise"

needSub : Judg -> KM (Sub, Ctx)
needSub (JSub s d) = pure (s, d)
needSub j = kerr "derivation: expected a substitution premise"

needPoly : Judg -> KM Poly
needPoly (JPoly f) = pure f
needPoly j = kerr "derivation: expected a polynomial premise"

needQSig : Judg -> KM QSig
needQSig (JQSig sg) = pure sg
needQSig j = kerr "derivation: expected a signature premise"

liftQE : Either QErr a -> KM a
liftQE (Left e) = kerr "derivation: \{e}"
liftQE (Right x) = pure x

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

||| Declared ahead: the spine helper below recurses into it.
export
conclude : Sig -> Ctx -> Deriv -> KM Judg

||| A ToS entry's reflected binder telescope.
qArity : QSig -> Nat -> KM (QTy, List Ty)
qArity sg k = do
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: qiit position out of range"
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  pure (entry, tel)

||| A spine checked entrywise against a reflected telescope: each
||| entry's concluded type must match the telescope's, instantiated
||| by the earlier entries.
qSpine : String -> Sig -> Ctx -> List Deriv -> List Ty -> KM (List Elem)
qSpine rule sig ctx ds tel = do
  pairs <- traverse (\d => conclude sig ctx d >>= needEl) ds
  let args = map fst pairs
  if length args /= length tel
    then kerr "derivation: \{rule}: spine length mismatch"
    else pure ()
  goChk 0 pairs args
  pure args
 where
  goChk : Nat -> List (Elem, Ty) -> List Elem -> KM ()
  goChk i [] _ = pure ()
  goChk i ((e, ety) :: rest) args = do
    case telInst tel i args of
      Just want => alphaTy rule ety want
      Nothing => kerr "derivation: \{rule}: telescope instantiation failed"
    goChk (S i) rest args

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


-- quotients
conclude sig ctx (DElQuotI dA dR) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  (r, rty) <- conclude sig (ctx :< aty :< wkTy aty) dR >>= needEl
  alphaTy "el-quot-i" rty Ty.PropTy
  pure (JEl (Class a) (Ty.Quotient aty r))
conclude sig ctx (DElQuotEq dA dB dR dW) = do
  (a, aty) <- conclude sig ctx dA >>= needEl
  (b, bty) <- conclude sig ctx dB >>= needEl
  alphaTy "el-quot-eq" bty aty
  (r, rty) <- conclude sig (ctx :< aty :< wkTy aty) dR >>= needEl
  alphaTy "el-quot-eq" rty Ty.PropTy
  (_, wty) <- conclude sig ctx dW >>= needEl
  alphaTy "el-quot-eq (witness)" wty
    (Prf (substElem r (Ext (Ext Id a) b)))
  pure (JElEq (Class a) (Class b) (Ty.Quotient aty r))
conclude sig ctx (DElQuotE dQ dB dF dResp) = do
  (q, qty) <- conclude sig ctx dQ >>= needEl
  case qty of
    Ty.Quotient a r => do
      b <- conclude sig (ctx :< Ty.Quotient a r) dB >>= needTy
      (f, fty) <- conclude sig (ctx :< a) dF >>= needEl
      alphaTy "el-quot-e (case)" fty (substTy b (Ext Wk (Class (CtxVar 0))))
      let wk3 = Chain Wk (Chain Wk Wk)
      (l, r', ety) <- conclude sig (ctx :< a :< wkTy a :< Prf r) dResp >>= needElEq
      alphaEl "el-quot-e (wd l)" l (substElem f (Ext wk3 (CtxVar 2)))
      alphaEl "el-quot-e (wd r)" r' (substElem f (Ext wk3 (CtxVar 1)))
      alphaTy "el-quot-e (wd ty)" ety (substTy b (Ext wk3 (Class (CtxVar 2))))
      pure (JEl (QuotElim f q) (substTy b (Ext Id q)))
    _ => kerr "derivation: el-quot-e: scrutinee not at a quotient type"
conclude sig ctx (DElQuotEta dQ dB dG dF dResp dAg) = do
  (q, qty) <- conclude sig ctx dQ >>= needEl
  case qty of
    Ty.Quotient a r => do
      b <- conclude sig (ctx :< Ty.Quotient a r) dB >>= needTy
      (g, gty) <- conclude sig (ctx :< Ty.Quotient a r) dG >>= needEl
      alphaTy "el-quot-eta (g)" gty b
      (f, fty) <- conclude sig (ctx :< a) dF >>= needEl
      alphaTy "el-quot-eta (f)" fty (substTy b (Ext Wk (Class (CtxVar 0))))
      let wk3 = Chain Wk (Chain Wk Wk)
      (l, r', ety) <- conclude sig (ctx :< a :< wkTy a :< Prf r) dResp >>= needElEq
      alphaEl "el-quot-eta (wd l)" l (substElem f (Ext wk3 (CtxVar 2)))
      alphaEl "el-quot-eta (wd r)" r' (substElem f (Ext wk3 (CtxVar 1)))
      alphaTy "el-quot-eta (wd ty)" ety (substTy b (Ext wk3 (Class (CtxVar 2))))
      (gl, gr, aty') <- conclude sig (ctx :< a) dAg >>= needElEq
      alphaEl "el-quot-eta (ag l)" gl (substElem g (Ext Wk (Class (CtxVar 0))))
      alphaEl "el-quot-eta (ag r)" gr f
      alphaTy "el-quot-eta (ag ty)" aty' (substTy b (Ext Wk (Class (CtxVar 0))))
      pure (JElEq (substElem g (Ext Id q)) (QuotElim f q) (substTy b (Ext Id q)))
    _ => kerr "derivation: el-quot-eta: scrutinee not at a quotient type"

-- the remaining η rules
conclude sig ctx (DElNatEta dMot dF0 dF1 dZ dS dEqZ dEqS0 dEqS1 dT) = do
  mot <- conclude sig (ctx :< Ty.NatTy) dMot >>= needTy
  (f0, f0ty) <- conclude sig (ctx :< Ty.NatTy) dF0 >>= needEl
  alphaTy "el-nat-eta (f₀)" f0ty mot
  (f1, f1ty) <- conclude sig (ctx :< Ty.NatTy) dF1 >>= needEl
  alphaTy "el-nat-eta (f₁)" f1ty mot
  (z, zty) <- conclude sig ctx dZ >>= needEl
  alphaTy "el-nat-eta (z)" zty (substTy mot (Ext Id NatIntro0))
  (s, sty) <- conclude sig (ctx :< Ty.NatTy :< mot) dS >>= needEl
  alphaTy "el-nat-eta (s)" sty
    (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
  (zl, zr, zety) <- conclude sig ctx dEqZ >>= needElEq
  alphaEl "el-nat-eta (Z l)" zl (substElem f0 (Ext Id NatIntro0))
  alphaEl "el-nat-eta (Z r)" zr (substElem f1 (Ext Id NatIntro0))
  alphaTy "el-nat-eta (Z ty)" zety (substTy mot (Ext Id NatIntro0))
  let sSub = Ext Wk (NatIntro1 (CtxVar 0))
  (s0l, s0r, s0ty) <- conclude sig (ctx :< Ty.NatTy) dEqS0 >>= needElEq
  alphaEl "el-nat-eta (S₀ l)" s0l (substElem f0 sSub)
  alphaEl "el-nat-eta (S₀ r)" s0r (substElem s (Ext Id f0))
  alphaTy "el-nat-eta (S₀ ty)" s0ty (substTy mot sSub)
  (s1l, s1r, s1ty) <- conclude sig (ctx :< Ty.NatTy) dEqS1 >>= needElEq
  alphaEl "el-nat-eta (S₁ l)" s1l (substElem f1 sSub)
  alphaEl "el-nat-eta (S₁ r)" s1r (substElem s (Ext Id f1))
  alphaTy "el-nat-eta (S₁ ty)" s1ty (substTy mot sSub)
  (t, tty) <- conclude sig ctx dT >>= needEl
  alphaTy "el-nat-eta (t)" tty Ty.NatTy
  pure (JElEq (substElem f0 (Ext Id t)) (substElem f1 (Ext Id t))
              (substTy mot (Ext Id t)))
conclude sig ctx (DElSumEta dT dC dG dL dR dAgL dAgR) = do
  (t, tty) <- conclude sig ctx dT >>= needEl
  case tty of
    Ty.SumTy a b => do
      c <- conclude sig (ctx :< Ty.SumTy a b) dC >>= needTy
      (g, gty) <- conclude sig (ctx :< Ty.SumTy a b) dG >>= needEl
      alphaTy "el-sum-eta (g)" gty c
      let lSub = Ext Wk (Inj1 (CtxVar 0))
      let rSub = Ext Wk (Inj2 (CtxVar 0))
      (l, lty) <- conclude sig (ctx :< a) dL >>= needEl
      alphaTy "el-sum-eta (l)" lty (substTy c lSub)
      (r, rty) <- conclude sig (ctx :< b) dR >>= needEl
      alphaTy "el-sum-eta (r)" rty (substTy c rSub)
      (all', alr, alty) <- conclude sig (ctx :< a) dAgL >>= needElEq
      alphaEl "el-sum-eta (agl l)" all' (substElem g lSub)
      alphaEl "el-sum-eta (agl r)" alr l
      alphaTy "el-sum-eta (agl ty)" alty (substTy c lSub)
      (arl, arr, arty) <- conclude sig (ctx :< b) dAgR >>= needElEq
      alphaEl "el-sum-eta (agr l)" arl (substElem g rSub)
      alphaEl "el-sum-eta (agr r)" arr r
      alphaTy "el-sum-eta (agr ty)" arty (substTy c rSub)
      pure (JElEq (substElem g (Ext Id t)) (SumElim l r t) (substTy c (Ext Id t)))
    _ => kerr "derivation: el-sum-eta: scrutinee not at a ⊎ type"

-- contexts and substitutions
conclude sig ctx DCtxEmpty = pure (JCtx [<])
conclude sig ctx (DCtxExt dG dA) = do
  g <- conclude sig ctx dG >>= needCtx
  a <- conclude sig g dA >>= needTy
  pure (JCtx (g :< a))
conclude sig ctx DSubEmpty = pure (JSub Terminal [<])
conclude sig ctx DSubId = pure (JSub Id ctx)
conclude sig ctx DSubWk =
  case ctx of
    (rest :< _) => pure (JSub Wk rest)
    [<] => kerr "derivation: sub-wk: the ambient context is empty"
conclude sig ctx (DSubExt dS dA dT) = do
  (s, g1) <- conclude sig ctx dS >>= needSub
  a <- conclude sig g1 dA >>= needTy
  (t, tty) <- conclude sig ctx dT >>= needEl
  alphaTy "sub-ext" tty (substTy a s)
  pure (JSub (Ext s t) (g1 :< a))
conclude sig ctx (DSubComp dS dT) = do
  (s, g1) <- conclude sig ctx dS >>= needSub
  (t, g2) <- conclude sig g1 dT >>= needSub
  pure (JSub (Chain t s) g2)
conclude sig ctx (DElSubCongFix dS dEq) = do
  (s, g1) <- conclude sig ctx dS >>= needSub
  (t0, t1, a) <- conclude sig g1 dEq >>= needElEq
  pure (JElEq (substElem t0 s) (substElem t1 s) (substTy a s))
conclude sig ctx (DTySubCongFix dS dEq) = do
  (s, g1) <- conclude sig ctx dS >>= needSub
  (a0, a1) <- conclude sig g1 dEq >>= needTyEq
  pure (JTyEq (substTy a0 s) (substTy a1 s))

-- the ν layer
conclude sig ctx (DPolyK f ds) = do
  rest <- goPoly ctx f ds
  case rest of
    [] => pure (JPoly f)
    _ => kerr "derivation: poly: too many embedded-piece premises"
 where
  goPoly : Ctx -> Poly -> List Deriv -> KM (List Deriv)
  goPoly c PHole ds = pure ds
  goPoly c (PConst a) (d :: ds) = do
    (a', aty) <- conclude sig c d >>= needEl
    alphaTy "poly (K)" aty Ty.UniverseTy
    alphaEl "poly (K)" a' a
    pure ds
  goPoly c (PProd p q) ds = goPoly c p ds >>= goPoly c q
  goPoly c (PSum p q) ds = goPoly c p ds >>= goPoly c q
  goPoly c (PSigma a p) (d :: ds) = do
    (a', aty) <- conclude sig c d >>= needEl
    alphaTy "poly (⨯)" aty Ty.UniverseTy
    alphaEl "poly (⨯)" a' a
    goPoly (c :< El a) p ds
  goPoly c (PPi a p) (d :: ds) = do
    (a', aty) <- conclude sig c d >>= needEl
    alphaTy "poly (→)" aty Ty.UniverseTy
    alphaEl "poly (→)" a' a
    goPoly (c :< El a) p ds
  goPoly c _ [] = kerr "derivation: poly: missing an embedded-piece premise"
conclude sig ctx (DTyNu dF) = do
  f <- conclude sig ctx dF >>= needPoly
  pure (JTy (Ty.NuTy f))
conclude sig ctx (DCodeNu dF) = do
  f <- conclude sig ctx dF >>= needPoly
  pure (JEl (Elem.NuTy f) Ty.UniverseTy)
conclude sig ctx (DElNuE dF dT) = do
  f <- conclude sig ctx dF >>= needPoly
  (t, tty) <- conclude sig ctx dT >>= needEl
  alphaTy "el-nu-e" tty (Ty.NuTy f)
  pure (JEl (Out t) (El (reflectPoly f (Elem.NuTy f))))
conclude sig ctx (DElNuI dF dA dBody dX) = do
  f <- conclude sig ctx dF >>= needPoly
  (a, aty) <- conclude sig ctx dA >>= needEl
  alphaTy "el-nu-i (carrier)" aty Ty.UniverseTy
  (body, bty) <- conclude sig (ctx :< El a) dBody >>= needEl
  alphaTy "el-nu-i (coalgebra)" bty (wkTy (El (reflectPoly f a)))
  (x, xty) <- conclude sig ctx dX >>= needEl
  alphaTy "el-nu-i (seed)" xty (El a)
  pure (JEl (Corec f a body x) (Ty.NuTy f))
conclude sig ctx (DElNuCoind dF dT0 dT1 dR dP dQ) = do
  f <- conclude sig ctx dF >>= needPoly
  (t0, t0ty) <- conclude sig ctx dT0 >>= needEl
  alphaTy "el-nu-coind (t₀)" t0ty (Ty.NuTy f)
  (t1, t1ty) <- conclude sig ctx dT1 >>= needEl
  alphaTy "el-nu-coind (t₁)" t1ty (Ty.NuTy f)
  (r, rty) <- conclude sig (ctx :< Ty.NuTy f :< Ty.NuTy f) dR >>= needEl
  alphaTy "el-nu-coind (R)" rty Ty.PropTy
  (_, pty) <- conclude sig ctx dP >>= needEl
  alphaTy "el-nu-coind (endpoint)" pty
    (Prf (substElem r (Ext (Ext Id t0) t1)))
  (_, qty) <- conclude sig (ctx :< Ty.NuTy f :< Ty.NuTy f :< Prf r) dQ >>= needEl
  alphaTy "el-nu-coind (closure)" qty
    (Prf (liftPoly f r (Out (CtxVar 2)) (Out (CtxVar 1))))
  pure (JElEq t0 t1 (Ty.NuTy f))

-- the QIIT layer
conclude sig ctx (DQSigK sg) = do
  sg' <- kQSig sig sg
  kQSigCheck sig ctx sg'
  pure (JQSig sg')
conclude sig ctx (DTyQSort k dSig ds) = do
  sg <- conclude sig ctx dSig >>= needQSig
  (entry, tel) <- qArity sg k
  es <- qSpine "ty-qiit" sig ctx ds tel
  pure (JTy (QSort sg k (cast es)))
conclude sig ctx (DCodeQSort k dSig ds) = do
  sg <- conclude sig ctx dSig >>= needQSig
  if qSigSmall sg then pure ()
    else kerr "derivation: code-qiit: signature not small"
  (entry, tel) <- qArity sg k
  es <- qSpine "code-qiit" sig ctx ds tel
  pure (JEl (QSortC sg k (cast es)) Ty.UniverseTy)
conclude sig ctx (DQCtor k dSig ds) = do
  sg <- conclude sig ctx dSig >>= needQSig
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: el-qiit-intro: position out of range"
  case qEntryKind entry of
    QKPoint => pure ()
    _ => kerr "derivation: el-qiit-intro: not a point constructor"
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  es <- qSpine "el-qiit-intro" sig ctx ds tel
  (wEnd, hd) <- liftQE (walkVals sg (qwAt k) entry es)
  (srt, idx) <- liftQE (pointHead sg wEnd hd)
  pure (JEl (QCtor sg k (cast es)) (QSort sg srt idx))
conclude sig ctx (DQElim k dSig dMots dMths dCohs dSp dW) = do
  sg <- conclude sig ctx dSig >>= needQSig
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: el-qiit-elim: sort out of range"
  case qEntryKind entry of
    QKSort => pure ()
    _ => kerr "derivation: el-qiit-elim: not a sort position"
  let sortPs = qPositions QKSort sg
  let pointPs = qPositions QKPoint sg
  let eqPs = qPositions QKEq sg
  mots <- goMots sg sortPs dMots
  mths <- goMths sg mots pointPs dMths
  goCohs sg mots mths eqPs dCohs
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  es <- qSpine "el-qiit-elim" sig ctx dSp tel
  (w, wty) <- conclude sig ctx dW >>= needEl
  alphaTy "el-qiit-elim (scrutinee)" wty (QSort sg k (cast es))
  o <- case qOrdinal QKSort sg k of
         Just x => pure x
         Nothing => kerr "derivation: el-qiit-elim: sort ordinal"
  motK <- case getAt o mots of
            Just m => pure m
            Nothing => kerr "derivation: el-qiit-elim: motive missing"
  pure (JEl (QElim sg k mots mths (cast es) w)
            (substTy motK (Ext (foldl Ext Id es) w)))
 where
  goMots : QSig -> List Nat -> List Deriv -> KM (List Ty)
  goMots sg [] [] = pure []
  goMots sg (sj :: sjs) (d :: ds) = do
    sjE <- case qEntry sg sj of
             Just x => pure x
             Nothing => kerr "derivation: el-qiit-elim: sort out of range"
    (tel, wEnd, _) <- liftQE (reflTel sg (qwAt sj) sjE)
    let mctx = foldl (:<) ctx tel
    let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
    mot <- conclude sig (mctx :< selfTy) d >>= needTy
    rest <- goMots sg sjs ds
    pure (mot :: rest)
  goMots _ _ _ = kerr "derivation: el-qiit-elim: motive count mismatch"

  goMths : QSig -> List Ty -> List Nat -> List Deriv -> KM (List Elem)
  goMths sg mots [] [] = pure []
  goMths sg mots (cj :: cjs) (d :: ds) = do
    mty <- liftQE (methodTy sg mots cj)
    (m, mty') <- conclude sig ctx d >>= needEl
    alphaTy "el-qiit-elim (method)" mty' mty
    rest <- goMths sg mots cjs ds
    pure (m :: rest)
  goMths _ _ _ _ = kerr "derivation: el-qiit-elim: method count mismatch"

  goCohs : QSig -> List Ty -> List Elem -> List Nat -> List Deriv -> KM ()
  goCohs sg mots mths [] [] = pure ()
  goCohs sg mots mths (ej :: ejs) (d :: ds) = do
    (dtel, _, lhs, rhs, cty) <- liftQE (coherenceAt sg mots mths ej)
    let cctx = foldl (:<) ctx dtel
    (l, r, ety) <- conclude sig cctx d >>= needElEq
    alphaEl "el-qiit-elim (coherence l)" l lhs
    alphaEl "el-qiit-elim (coherence r)" r rhs
    alphaTy "el-qiit-elim (coherence ty)" ety cty
    goCohs sg mots mths ejs ds
  goCohs _ _ _ _ _ = kerr "derivation: el-qiit-elim: coherence count mismatch"
conclude sig ctx (DQPath k dSig ds) = do
  sg <- conclude sig ctx dSig >>= needQSig
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: el-qiit-path: position out of range"
  case qEntryKind entry of
    QKEq => pure ()
    _ => kerr "derivation: el-qiit-path: not an equation constructor"
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  es <- qSpine "el-qiit-path" sig ctx ds tel
  (wEnd, hd) <- liftQE (walkVals sg (qwAt k) entry es)
  (lq, rq, uq) <- liftQE (eqHead hd)
  l <- liftQE (reflTm sg wEnd lq)
  r <- liftQE (reflTm sg wEnd rq)
  t <- liftQE (reflCodeTy sg wEnd uq)
  pure (JElEq l r t)

-- ===== Entry point =====

||| Check a derivation in the empty context with the given fuel;
||| Left is the rejection reason (fuel exhaustion included).
export
concludeItem : Sig -> Nat -> Deriv -> Either KErr Judg
concludeItem sig fuel d = map fst (runKM (conclude sig [<] d) fuel)
