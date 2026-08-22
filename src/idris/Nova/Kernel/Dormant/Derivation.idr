module Nova.Kernel.Dormant.Derivation

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
import Nova.Kernel.Dormant.Beta
import Nova.Kernel.QIIT
import Nova.Kernel

%default covering

-- ===== The ToS substitution calculus (Foundation: 𝕚𝕕/⇑/∘/ext) =====
--
-- ς is first-class syntax here (the kernel had no need of it — its
-- walk instantiates on the fly); its ACTION is the meta-operation
-- Foundation defines one clause per former: an INDUCTIVE binder
-- lifts ς, an EXTERNAL binder Nova-weakens ς's embedded pieces (ToS
-- indices do not shift at a Nova binder).

public export
data QSub : Type where
  QSId : QSub
  QSWk : QSub
  QSComp : QSub -> QSub -> QSub
  QSExt : QSub -> QTm -> QSub

mutual
  ||| ς's value at index i (𝕥[τ ∘ ς] = 𝕥[τ][ς]).
  qsApply : QSub -> Nat -> QTm
  qsApply QSId i = QVar i
  qsApply QSWk i = QVar (S i)
  qsApply (QSComp tau sig) i = qSubTm sig (qsApply tau i)
  qsApply (QSExt sig t) Z = t
  qsApply (QSExt sig t) (S i) = qsApply sig i

  ||| Nova-weaken ς's embedded pieces (crossing an external binder).
  qsWkNova : QSub -> QSub
  qsWkNova QSId = QSId
  qsWkNova QSWk = QSWk
  qsWkNova (QSComp tau sig) = QSComp (qsWkNova tau) (qsWkNova sig)
  qsWkNova (QSExt sig t) = QSExt (qsWkNova sig) (substQTm t Wk)

  ||| ς⁺ ≜ (ς ∘ ⇑, ⬡₀) — the derived lift at an inductive binder.
  qsLift : QSub -> QSub
  qsLift sig = QSExt (QSComp sig QSWk) (QVar 0)

  export
  qSubTm : QSub -> QTm -> QTm
  qSubTm sig (QVar i) = qsApply sig i
  qSubTm sig (QAppE f e) = QAppE (qSubTm sig f) e
  qSubTm sig (QAppI f a) = QAppI (qSubTm sig f) (qSubTm sig a)
  qSubTm sig (QEqC l r u) = QEqC (qSubTm sig l) (qSubTm sig r) (qSubTm sig u)

  export
  qSubTy : QSub -> QTy -> QTy
  qSubTy sig QU = QU
  qSubTy sig (QEl t) = QEl (qSubTm sig t)
  qSubTy sig (QPiExt a b) = QPiExt a (qSubTy (qsWkNova sig) b)
  qSubTy sig (QPiInd t b) = QPiInd (qSubTm sig t) (qSubTy (qsLift sig) b)

||| ToS index shift (crossing inductive binders): add n to QVar
||| indices ≥ the cutoff. Nova pieces are untouched.
qShiftTm : (cutoff, n : Nat) -> QTm -> QTm
qShiftTm c n (QVar i) = if i >= c then QVar (i + n) else QVar i
qShiftTm c n (QAppE f e) = QAppE (qShiftTm c n f) e
qShiftTm c n (QAppI f a) = QAppI (qShiftTm c n f) (qShiftTm c n a)
qShiftTm c n (QEqC l r u) = QEqC (qShiftTm c n l) (qShiftTm c n r) (qShiftTm c n u)

qShiftTy : (cutoff, n : Nat) -> QTy -> QTy
qShiftTy c n QU = QU
qShiftTy c n (QEl t) = QEl (qShiftTm c n t)
qShiftTy c n (QPiExt a b) = QPiExt a (qShiftTy c n b)
qShiftTy c n (QPiInd t b) = QPiInd (qShiftTm c n t) (qShiftTy (S c) n b)

||| Φ‖ᵢ — the entry's type as seen at the current position (its ToS
||| indices shifted past the entries above it).
export
phiAt : SnocList QTy -> Nat -> Maybe QTy
phiAt [<] _ = Nothing
phiAt (rest :< a) Z = Just (qShiftTy 0 1 a)
phiAt (rest :< a) (S n) = map (qShiftTy 0 1) (phiAt rest n)

||| Φ[↑] — Nova-weakening the whole ToS zone (crossing an external
||| binder; ToS indices do not shift).
export
phiWkNova : SnocList QTy -> SnocList QTy
phiWkNova = map (\a => substQTy a Wk)

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
  ||| Γ₀ ≐ Γ₁ ctx (ambient-independent, like JCtx)
  JCtxEq : Ctx -> Ctx -> Judg
  ||| σ₀ ≐ σ₁ : Γ ⇒ Δ
  JSubEq : Sub -> Sub -> Ctx -> Judg
  ||| e˲₀ ≐ e˲₁ : Γ ⇒ Δ norm
  JSubNEq : SubNorm -> SubNorm -> Ctx -> Judg
  ||| Γ ⊦ Δ tel (the telescope's entries, outermost first)
  JTel : List Ty -> Judg
  ||| Γ ⊦ Δ₀ ≐ Δ₁ tel
  JTelEq : List Ty -> List Ty -> Judg
  ||| Γ ⊦ ē : Δ
  JSp : List Elem -> List Ty -> Judg
  ||| Γ ⊦ ē₀ ≐ ē₁ : Δ
  JSpEq : List Elem -> List Elem -> List Ty -> Judg
  ||| Γ ⊦ 𝒮 qsig
  JQSig : QSig -> Judg
  ||| Γ ⊦ Φ qctx — the formed ToS context (innermost LAST), an output
  JQCtx : SnocList QTy -> Judg
  ||| Γ ⊦ ς : Φ₀ ⇒ Φ₁ — Φ₀ the ambient ToS input, Φ₁ the output
  JQSub : QSub -> SnocList QTy -> Judg
  ||| Γ ⊦ C̄ : 𝒮 mot / Γ ⊦ ℰ : 𝒮 dalg / Γ ⊦ ℰ : 𝒮 eprob /
  ||| Γ ⊦ φ : C̄ sect
  JMot : QSig -> List Ty -> Judg
  JDalg : QSig -> List Ty -> List Elem -> Judg
  JEProb : QSig -> List Ty -> List Elem -> Judg
  JSect : QSig -> List Ty -> List Elem -> Judg

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
  show (JQCtx phi) = "⊦ qctx (\{show (length (toList phi))} entries)"
  show (JQSub _ _) = "⊦ qsub"
  show (JMot _ ms) = "⊦ mot (\{show (length ms)})"
  show (JDalg _ _ _) = "⊦ dalg"
  show (JEProb _ _ _) = "⊦ eprob"
  show (JSect _ _ _) = "⊦ sect"
  show (JCtxEq _ _) = "⊦ ctx ≐ ctx"
  show (JSubEq _ _ _) = "⊦ sub ≐ sub"
  show (JSubNEq _ _ _) = "⊦ norm ≐ norm"
  show (JTel d) = "⊦ tel (\{show (length d)} entries)"
  show (JTelEq _ _) = "⊦ tel ≐ tel"
  show (JSp es _) = "⊦ sp (\{show (length es)} entries)"
  show (JSpEq _ _ _) = "⊦ sp ≐ sp"

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
  ||| el-sig-var / el-sig-decl at a type entry (the Σ-lookup decides
  ||| which): the atom
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
  ||| el-squash-e-prf — delivery order q (the target prop), s, t:
  ||| Γ ⊦ q : Ω;  Γ ⊦ s : Prf ∥A∥;  Γ ▷ A ⊦ t : (Prf q)[↑]
  ||| ⊢  Γ ⊦ ⋆ : Prf q
  DElSquashEPrf : Deriv -> Deriv -> Deriv -> Deriv
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
  ||| el-sig-eq at a type constraint (A = 𝕍)
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
  ||| el-pi-eta, TWO-CANDIDATE (judgemental function extensionality):
  ||| f₀, f₁ : A → B;  Γ ▷ A ⊦ f₀[↑] ☐₀ ≐ f₁[↑] ☐₀ : B  ⊢  f₀ ≐ f₁
  DElPiEta : Deriv -> Deriv -> Deriv -> Deriv
  ||| el-sigma-eta, TWO-CANDIDATE: t₀, t₁ : A ⨯ B; the projections
  ||| pairwise equal (π₂ at B[id, t₀.π₁])  ⊢  t₀ ≐ t₁
  DElSigmaEta : Deriv -> Deriv -> Deriv -> Deriv -> Deriv

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
  ||| ty-quot-cong: Γ ⊦ A₀ ≐ A₁ type;  Γ ▷ A₁ ▷ A₁[↑] ⊦ R₀ ≐ R₁ : Ω
  DTyQuotCong : Deriv -> Deriv -> Deriv
  ||| el-nat-e-cong (motive A) / el-sum-e-cong (motive C; delivery
  ||| order teq, C, leq, req) / el-zero-e-cong (no t⁼ premise —
  ||| stronger than a congruence) / el-quot-e-cong (motive B;
  ||| delivery order qeq, B, f₀, f₁, wd₀, wd₁, feq)
  DElNatECong : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  DElSumECong : Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  DElZeroECong : Deriv -> Deriv -> Deriv -> Deriv
  DElQuotECong : Deriv -> Deriv -> Deriv -> Deriv -> Deriv -> Deriv -> Deriv -> Deriv
  ||| el-let-cong: aeq; beq under Γ ▷ A ▷ Prf (☐₀ ≡ a₁[↑] ∈ A[↑])
  DElLetCong : Deriv -> Deriv -> Deriv
  ||| el-class-cong (delivery order aeq, R) / el-inj₁-cong (aeq, B) /
  ||| el-inj₂-cong (beq, A)
  DElClassCong : Deriv -> Deriv -> Deriv
  DElInj1Cong : Deriv -> Deriv -> Deriv
  DElInj2Cong : Deriv -> Deriv -> Deriv
  ||| the universe-code congruences (bodies under El a₁)
  DCodePiCong : Deriv -> Deriv -> Deriv
  DCodeSigmaCong : Deriv -> Deriv -> Deriv
  DCodeSumCong : Deriv -> Deriv -> Deriv
  DCodeQuotCong : Deriv -> Deriv -> Deriv
  DCodeSquashCong : Deriv -> Deriv
  ||| code-eq-cong (delivery order tyeq, aeq at A₁, beq at A₁)
  DCodeEqCong : Deriv -> Deriv -> Deriv -> Deriv
  ||| INJECTIVITY (grouped conclusions split, one node per
  ||| conclusion; premises shared per Foundation's statements)
  DTyPiInjDom : Deriv -> Deriv -> Deriv -> Deriv
  DTyPiInjCod : Deriv -> Deriv -> Deriv -> Deriv
  DTySigmaInjDom : Deriv -> Deriv -> Deriv -> Deriv
  DTySigmaInjCod : Deriv -> Deriv -> Deriv -> Deriv
  DTySumInjL : Deriv -> Deriv
  DTySumInjR : Deriv -> Deriv
  DTyQuotInjDom : Deriv -> Deriv -> Deriv -> Deriv
  DTyQuotInjRel : Deriv -> Deriv -> Deriv -> Deriv
  DTyElInj : Deriv -> Deriv
  DCodePiInjDom : Deriv -> Deriv -> Deriv -> Deriv
  DCodePiInjCod : Deriv -> Deriv -> Deriv -> Deriv
  DCodeSigmaInjDom : Deriv -> Deriv -> Deriv -> Deriv
  DCodeSigmaInjCod : Deriv -> Deriv -> Deriv -> Deriv
  DCodeSumInjL : Deriv -> Deriv
  DCodeSumInjR : Deriv -> Deriv
  DCodeQuotInjDom : Deriv -> Deriv -> Deriv -> Deriv
  DCodeQuotInjRel : Deriv -> Deriv -> Deriv -> Deriv
  ||| QIIT code injectivity, indexwise (Foundation states the QIIT
  ||| congruence/injectivity block structurally): from
  ||| 𝒮.𝕤 ē₀ ≐ 𝒮.𝕤 ē₁ : 𝕌 with the spines α-agreeing before i,
  ||| conclude ē₀ᵢ ≐ ē₁ᵢ : Eᵢ (entry i of the reflected telescope,
  ||| instantiated by the shared prefix)
  DCodeQSortInjIdx : Nat -> Deriv -> Deriv
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

  -- ----- ADMISSIBLE: formation inversion -----
  ||| from Γ ⊦ Π A B type conclude Γ ⊦ A type
  DInvPiDom : Deriv -> Deriv
  ||| from Γ ⊦ Π A B type conclude Γ ▷ A ⊦ B type — replayed in the
  ||| extended context input, whose top binder must α-match A
  DInvPiCod : Deriv -> Deriv
  ||| the Σ instances
  DInvSigmaDom : Deriv -> Deriv
  DInvSigmaCod : Deriv -> Deriv
  ||| the Prf-equality instances: from Γ ⊦ Prf (a ≡ b ∈ A) type
  ||| conclude Γ ⊦ a : A (…b : A, …A type)
  DInvPrfEqL : Deriv -> Deriv
  DInvPrfEqR : Deriv -> Deriv
  DInvPrfEqTy : Deriv -> Deriv
  ||| from Γ ⊦ Prf p type conclude Γ ⊦ p : Ω
  DInvPrfCode : Deriv -> Deriv
  ||| from Γ ⊦ El a type conclude Γ ⊦ a : 𝕌
  DInvElCode : Deriv -> Deriv
  ||| typing inversion of the equality code (code-eq's premises):
  ||| from Γ ⊦ (l ≡ r ∈ t) : Ω conclude Γ ⊦ l : t (…r : t, …t type)
  DInvCodeEqL : Deriv -> Deriv
  DInvCodeEqR : Deriv -> Deriv
  DInvCodeEqTy : Deriv -> Deriv

  -- ----- ADMISSIBLE: the nf oracle -----
  ||| beta-at — ONE ≜ contraction at a path inside a TYPED term,
  ||| unidirectional, no typing premise for the subterm (subject
  ||| reduction; the oracle's own justification composes exactly
  ||| these): Γ ⊦ t : A  ⊢  Γ ⊦ t ≐ t′ : A  where t′ = t contracted
  ||| at p. The path is an atom naming the position, like a
  ||| variable's index.
  DBetaAt : List Nat -> Deriv -> Deriv
  ||| … and at the type level (El-decoding and type-level unfolding
  ||| included)
  DBetaAtTy : List Nat -> Deriv -> Deriv
  ||| nf-expand: Γ ⊦ t : A  ⊢  Γ ⊦ t ≐ nf(t) : A
  DNfExpand : Deriv -> Deriv
  ||| nf-expand-ty
  DNfExpandTy : Deriv -> Deriv
  ||| nf-eq: Γ ⊦ t₀ : A;  Γ ⊦ t₁ : A;  nf(t₀) = nf(t₁)
  DNfEq : Deriv -> Deriv -> Deriv
  ||| share Δ D₀ D₁ — let-bound subderivation (admissible addition 3,
  ||| docs/NovaDerivations.txt): D₀ concludes ONCE, under the carried
  ||| context Δ; within D₁ the binding is cited by DRef, legal exactly
  ||| at Δ. Sharing is explicit in the artifact — replay walks each
  ||| bound derivation once, and conclude stays cache-free.
  DShare : Ctx -> Deriv -> Deriv -> Deriv
  ||| ⟨i⟩ — cite the i-th share binding (absolute index, outermost
  ||| first)
  DRef : Nat -> Deriv
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
  ||| sub-ext-cong — delivery order σ₀ ≐ σ₁ (delivers Γ₁), A (over
  ||| Γ₁), the component equation side-checked at A[σ₁]:
  ||| (σ₀, t₀) ≐ (σ₁, t₁) : Γ ⇒ Γ₁ ▷ A
  DSubExtCong : Deriv -> Deriv -> Deriv -> Deriv
  ||| el-sub-cong-fix (admissible in Foundation, adopted): σ delivers
  ||| Γ₁; the equation lives over Γ₁; concludes it substituted
  DElSubCongFix : Deriv -> Deriv -> Deriv
  ||| el-sub-cong-fix at 𝕍 (formerly a separate type-judgement rule)
  DTySubCongFix : Deriv -> Deriv -> Deriv
  ||| the equivalence-rule instances for the remaining classes
  ||| (adopted once per class in Foundation)
  DCtxRefl : Deriv -> Deriv
  DCtxSym : Deriv -> Deriv
  DCtxTrans : Deriv -> Deriv -> Deriv
  DSubRefl : Deriv -> Deriv
  DSubSym : Deriv -> Deriv
  DSubTrans : Deriv -> Deriv -> Deriv
  DSubNRefl : Deriv -> Deriv
  DSubNSym : Deriv -> Deriv
  DSubNTrans : Deriv -> Deriv -> Deriv
  DTelRefl : Deriv -> Deriv
  DTelSym : Deriv -> Deriv
  DTelTrans : Deriv -> Deriv -> Deriv
  DSpRefl : Deriv -> Deriv
  DSpSym : Deriv -> Deriv
  DSpTrans : Deriv -> Deriv -> Deriv
  ||| ctx-ext-cong: Γ₀ ≐ Γ₁ ctx;  Γ₁ ⊦ A₀ ≐ A₁ type
  DCtxExtCong : Deriv -> Deriv -> Deriv
  ||| sub-norm-ext-cong — delivery order the norm equation (delivers
  ||| the target prefix), A over it, the entry equation at A[e˲₁]
  DSubNExtCong : Deriv -> Deriv -> Deriv -> Deriv
  ||| el-sub-cong, element and 𝕍 instances (the full forms; σ₀ ≐ σ₁ delivered
  ||| first, the equation over the target)
  DElSubCong : Deriv -> Deriv -> Deriv
  DTySubCong : Deriv -> Deriv -> Deriv
  ||| tel-empty / tel-ext / tel-ext-cong
  DTelEmpty : Deriv
  DTelExt : Deriv -> Deriv -> Deriv
  DTelExtCong : Deriv -> Deriv -> Deriv
  ||| sp-empty / sp-ext / sp-ext-cong (Δ instantiated at the head)
  DSpEmpty : Deriv
  DSpExt : Deriv -> Deriv -> Deriv -> Deriv
  DSpExtCong : Deriv -> Deriv -> Deriv -> Deriv
  ||| the context-coercion rules: el-coe-ctx / el-eq-coe-ctx (their
  ||| 𝕍 instances were separate type-judgement rules) — the ambient must α-match the
  ||| equation's RIGHT context; the judgement premise runs under the
  ||| LEFT
  DTyCoeCtx : Deriv -> Deriv -> Deriv
  DElCoeCtx : Deriv -> Deriv -> Deriv
  DTyEqCoeCtx : Deriv -> Deriv -> Deriv
  DElEqCoeCtx : Deriv -> Deriv -> Deriv

  -- ----- the ν layer -----
  ||| poly-hole / poly-const / poly-prod / poly-sum / poly-sigma /
  ||| poly-pi — one node per Foundation rule (the binding formers'
  ||| bodies under Γ ▷ El a)
  DPolyHole : Deriv
  DPolyConst : Deriv -> Deriv
  DPolyProd : Deriv -> Deriv -> Deriv
  DPolySum : Deriv -> Deriv -> Deriv
  DPolySigma : Deriv -> Deriv -> Deriv
  DPolyPi : Deriv -> Deriv -> Deriv
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
  -- the ToS layer, one node per Foundation rule. The qty/qtm/qsub
  -- judgements live in the dual zone Γ ; Φ — Φ is threaded as an
  -- INPUT by their own conclude family (concludeQTy/QTm/QSub below),
  -- exactly as Γ is; qctx formation OUTPUTS the zone it forms.
  ||| qctx-empty / qctx-ext (the entry premise checked in the zone
  ||| formed so far)
  DQCtxEmpty : Deriv
  DQCtxExt : Deriv -> Deriv -> Deriv
  ||| Γ ⊦ 𝒮 qsig ≜ Γ ⊦ 𝒮 qctx — the reading of a closed qctx as a
  ||| signature (kernel entry order: outermost first)
  DQSig : Deriv -> Deriv
  ||| qty-univ / qty-el / qty-pi-ext (binds a Nova variable: the Nova
  ||| zone grows, Φ Nova-weakens) / qty-pi-ind (binds a ToS variable)
  DQTyUniv : Deriv
  DQTyEl : Deriv -> Deriv
  DQTyPiExt : Deriv -> Deriv -> Deriv
  DQTyPiInd : Deriv -> Deriv -> Deriv
  ||| qtm-var: Γ ; Φ ⊦ ⬡ᵢ : Φ‖ᵢ
  DQTmVar : Nat -> Deriv
  ||| qtm-app-ext: 𝕥 : A ⇛ 𝔄;  Γ ⊦ t : A  ⊢  𝕥 t : 𝔄[t]
  DQTmAppExt : Deriv -> Deriv -> Deriv
  ||| qtm-app-ind: 𝕥 : El 𝕦 ⇛ 𝔄;  𝕥′ : El 𝕦  ⊢  𝕥 𝕥′ : 𝔄[𝕥′]
  DQTmAppInd : Deriv -> Deriv -> Deriv
  ||| qtm-eq: both sides at the same El 𝕦; the equation code lands
  ||| in U
  DQTmEq : Deriv -> Deriv -> Deriv
  ||| qsub-id / qsub-wk / qsub-comp (delivery order ς then τ) /
  ||| qsub-ext (delivery order ς, 𝔄 over the target, 𝕥 at 𝔄[ς])
  DQSubId : Deriv
  DQSubWk : Deriv
  DQSubComp : Deriv -> Deriv -> Deriv
  DQSubExt : Deriv -> Deriv -> Deriv -> Deriv
  ||| qtm-sub / qty-sub — delivery order ς (delivers Φ₁), the piece
  ||| over Φ₁
  DQTmSub : Deriv -> Deriv -> Deriv
  DQTySub : Deriv -> Deriv -> Deriv
  ||| sort-instance formation Γ ⊦ 𝒮.𝕤 ē type — the spine entrywise
  ||| at the reflected arity telescope
  DTyQSort : Nat -> Deriv -> List Deriv -> Deriv
  ||| the QSort formation congruence, spine-wise (Foundation's QIIT
  ||| congruence block, stated structurally): index equations each
  ||| checked at the telescope entry instantiated by the LEFT spine
  DTyQSortCong : Nat -> Deriv -> List Deriv -> Deriv
  ||| the point-constructor spine congruence (the same structural
  ||| block): argument equations each at the left instantiation;
  ||| concludes at the left spine's sort instance
  DQCtorCong : Nat -> Deriv -> List Deriv -> Deriv
  ||| code-qiit (small signatures only)
  DCodeQSort : Nat -> Deriv -> List Deriv -> Deriv
  ||| el-qiit-intro: the constructor spine entrywise; concludes at
  ||| the point's sort instance
  DQCtor : Nat -> Deriv -> List Deriv -> Deriv
  ||| the elimination-problem judgement classes, first-class:
  ||| mot (per-sort motive formation, each under its reflected
  ||| telescope plus the sort's self entry), dalg (a mot plus
  ||| per-point method typings at their ᴰ method types), eprob (a
  ||| dalg whose method-image equations hold — one COHERENCE EQUALITY
  ||| DERIVATION per equation entry, under its ᴰ-telescope; A4's
  ||| β-only restriction retired), sect (per-sort candidates typed at
  ||| the motives)
  DQMot : Deriv -> List Deriv -> Deriv
  DQDalg : Deriv -> List Deriv -> Deriv
  DQEProb : Deriv -> List Deriv -> Deriv
  DQSect : Deriv -> List Deriv -> Deriv
  ||| el-qiit-elim: an eprob premise, the index spine, the scrutinee
  DQElim : Nat -> Deriv -> List Deriv -> Deriv -> Deriv
  ||| el-qiit-eta: an eprob premise, a sect premise, per-point
  ||| AGREEMENT equations h_𝕤[⌊ī⌋, 𝒮.𝕔 θ] ≐ m_𝕔 θ⟨h⟩ (under the
  ||| constructor's reflected telescope), the index spine, the
  ||| scrutinee — concludes h_𝕤[ē, w] ≐ 𝒮.𝕤-elim ℰ ē w
  DQEta : Nat -> Deriv -> Deriv -> List Deriv -> List Deriv -> Deriv -> Deriv
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

needQCtx : Judg -> KM (SnocList QTy)
needQCtx (JQCtx phi) = pure phi
needQCtx j = kerr "derivation: expected a qctx premise"

needCtxEq : Judg -> KM (Ctx, Ctx)
needCtxEq (JCtxEq g0 g1) = pure (g0, g1)
needCtxEq j = kerr "derivation: expected a context-equation premise"

needSubEq : Judg -> KM (Sub, Sub, Ctx)
needSubEq (JSubEq s0 s1 d) = pure (s0, s1, d)
needSubEq j = kerr "derivation: expected a substitution-equation premise"

needSubNEq : Judg -> KM (SubNorm, SubNorm, Ctx)
needSubNEq (JSubNEq e0 e1 d) = pure (e0, e1, d)
needSubNEq j = kerr "derivation: expected a normal-substitution-equation premise"

needTel : Judg -> KM (List Ty)
needTel (JTel d) = pure d
needTel j = kerr "derivation: expected a telescope premise"

needTelEq : Judg -> KM (List Ty, List Ty)
needTelEq (JTelEq d0 d1) = pure (d0, d1)
needTelEq j = kerr "derivation: expected a telescope-equation premise"

needSp : Judg -> KM (List Elem, List Ty)
needSp (JSp es d) = pure (es, d)
needSp j = kerr "derivation: expected an element-list premise"

needSpEq : Judg -> KM (List Elem, List Elem, List Ty)
needSpEq (JSpEq e0 e1 d) = pure (e0, e1, d)
needSpEq j = kerr "derivation: expected an element-list-equation premise"

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

||| The share environment: judgments concluded by enclosing DShare
||| bindings, each with the context it was concluded under.
public export
ShareEnv : Type
ShareEnv = List (Ctx, Judg)

||| Declared ahead: the spine helper below recurses into it, and the
||| ToS family (dual zone Γ ; Φ — Φ threaded as an input, exactly as
||| Γ is) is mutual with it.
export
conclude : ShareEnv -> Sig -> Ctx -> Deriv -> KM Judg

||| Γ ; Φ ⊦ 𝔄 qty
export
concludeQTy : ShareEnv -> Sig -> Ctx -> SnocList QTy -> Deriv -> KM QTy

||| Γ ; Φ ⊦ 𝕥 : 𝔄
export
concludeQTm : ShareEnv -> Sig -> Ctx -> SnocList QTy -> Deriv -> KM (QTm, QTy)

||| Γ ⊦ ς : Φ₀ ⇒ Φ₁ (Φ₀ the input, Φ₁ the output)
export
concludeQSub : ShareEnv -> Sig -> Ctx -> SnocList QTy -> Deriv -> KM (QSub, SnocList QTy)


piProj : Ty -> Maybe (Ty, Ty)
piProj (PiTy a b) = Just (a, b)
piProj _ = Nothing

sgProj : Ty -> Maybe (Ty, Ty)
sgProj (SigmaTy a b) = Just (a, b)
sgProj _ = Nothing

piCProj : Elem -> Maybe (Elem, Elem)
piCProj (Elem.PiTy a b) = Just (a, b)
piCProj _ = Nothing

sgCProj : Elem -> Maybe (Elem, Elem)
sgCProj (Elem.SigmaTy a b) = Just (a, b)
sgCProj _ = Nothing

||| The shared premise pack of the binder-former injectivity rules
||| (grouped conclusions split into two nodes): the equation delivers
||| both spellings, the two formation premises are side-compared at
||| their own domains.
tyBinInj : ShareEnv -> Sig -> Ctx -> String -> (Ty -> Maybe (Ty, Ty)) ->
           Deriv -> Deriv -> Deriv -> KM (Ty, Ty, Ty, Ty)
tyBinInj env sig ctx rule proj dB0 dB1 dEq = do
  (l, r) <- conclude env sig ctx dEq >>= needTyEq
  case (proj l, proj r) of
    (Just (a0, b0), Just (a1, b1)) => do
      b0' <- conclude env sig (ctx :< a0) dB0 >>= needTy
      alphaTy rule b0' b0
      b1' <- conclude env sig (ctx :< a1) dB1 >>= needTy
      alphaTy rule b1' b1
      pure (a0, a1, b0, b1)
    _ => kerr "derivation: \{rule}: equation not between the right formers"

codeBinInj : ShareEnv -> Sig -> Ctx -> String -> (Elem -> Maybe (Elem, Elem)) ->
             Deriv -> Deriv -> Deriv -> KM (Elem, Elem, Elem, Elem)
codeBinInj env sig ctx rule proj dB0 dB1 dEq = do
  (l, r, ty) <- conclude env sig ctx dEq >>= needElEq
  alphaTy rule ty UniverseTy
  case (proj l, proj r) of
    (Just (a0, b0), Just (a1, b1)) => do
      (b0', b0ty) <- conclude env sig (ctx :< El a0) dB0 >>= needEl
      alphaTy rule b0ty UniverseTy
      alphaEl rule b0' b0
      (b1', b1ty) <- conclude env sig (ctx :< El a1) dB1 >>= needEl
      alphaTy rule b1ty UniverseTy
      alphaEl rule b1' b1
      pure (a0, a1, b0, b1)
    _ => kerr "derivation: \{rule}: equation not between the right formers"

tyQuotInj : ShareEnv -> Sig -> Ctx -> Deriv -> Deriv -> Deriv -> KM (Ty, Ty, Elem, Elem)
tyQuotInj env sig ctx dR0 dR1 dEq = do
  (l, r) <- conclude env sig ctx dEq >>= needTyEq
  case (l, r) of
    (QuotTy a0 r0, QuotTy a1 r1) => do
      (r0', r0ty) <- conclude env sig (ctx :< a0 :< wkTy a0) dR0 >>= needEl
      alphaTy "ty-quot-inj" r0ty PropTy
      alphaEl "ty-quot-inj" r0' r0
      (r1', r1ty) <- conclude env sig (ctx :< a1 :< wkTy a1) dR1 >>= needEl
      alphaTy "ty-quot-inj" r1ty PropTy
      alphaEl "ty-quot-inj" r1' r1
      pure (a0, a1, r0, r1)
    _ => kerr "derivation: ty-quot-inj: equation not between quotients"

codeQuotInj : ShareEnv -> Sig -> Ctx -> Deriv -> Deriv -> Deriv -> KM (Elem, Elem, Elem, Elem)
codeQuotInj env sig ctx dR0 dR1 dEq = do
  (l, r, ty) <- conclude env sig ctx dEq >>= needElEq
  alphaTy "code-quot-inj" ty UniverseTy
  case (l, r) of
    (Elem.QuotTy a0 r0, Elem.QuotTy a1 r1) => do
      (r0', r0ty) <- conclude env sig (ctx :< El a0 :< wkTy (El a0)) dR0 >>= needEl
      alphaTy "code-quot-inj" r0ty PropTy
      alphaEl "code-quot-inj" r0' r0
      (r1', r1ty) <- conclude env sig (ctx :< El a1 :< wkTy (El a1)) dR1 >>= needEl
      alphaTy "code-quot-inj" r1ty PropTy
      alphaEl "code-quot-inj" r1' r1
      pure (a0, a1, r0, r1)
    _ => kerr "derivation: code-quot-inj: equation not between quotient codes"


needMot : Judg -> KM (QSig, List Ty)
needMot (JMot sg ms) = pure (sg, ms)
needMot j = kerr "derivation: expected a mot premise"

needDalg : Judg -> KM (QSig, List Ty, List Elem)
needDalg (JDalg sg ms fs) = pure (sg, ms, fs)
needDalg j = kerr "derivation: expected a dalg premise"

needEProb : Judg -> KM (QSig, List Ty, List Elem)
needEProb (JEProb sg ms fs) = pure (sg, ms, fs)
needEProb j = kerr "derivation: expected an eprob premise"

needSect : Judg -> KM (QSig, List Ty, List Elem)
needSect (JSect sg ms hs) = pure (sg, ms, hs)
needSect j = kerr "derivation: expected a sect premise"


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
qSpine : ShareEnv -> String -> Sig -> Ctx -> List Deriv -> List Ty -> KM (List Elem)
qSpine env rule sig ctx ds tel = do
  pairs <- traverse (\d => conclude env sig ctx d >>= needEl) ds
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

||| A sort's motive/candidate context: the reflected telescope plus
||| the sort's self entry; also its sort ordinal.
qSortCtx : Sig -> Ctx -> QSig -> Nat -> KM (Ctx, List Ty, Nat)
qSortCtx sig ctx sg sj = do
  sjE <- case qEntry sg sj of
           Just x => pure x
           Nothing => kerr "derivation: sort out of range"
  (tel, wEnd, _) <- liftQE (reflTel sg (qwAt sj) sjE)
  let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
  so <- case qOrdinal QKSort sg sj of
          Just x => pure x
          Nothing => kerr "derivation: sort ordinal"
  pure ((foldl (:<) ctx tel) :< selfTy, tel, so)

||| The eliminator rules' shared tail: the index spine at the sort's
||| reflected arity, the scrutinee at the sort instance, the sort's
||| motive.
qElimEnd : ShareEnv -> Sig -> Ctx -> QSig -> List Ty -> Nat -> List Deriv -> Deriv ->
           KM (List Elem, Elem, Ty)
qElimEnd env sig ctx sg mots k dSp dW = do
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: el-qiit-elim: sort out of range"
  case qEntryKind entry of
    QKSort => pure ()
    _ => kerr "derivation: el-qiit-elim: not a sort position"
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  es <- qSpine env "el-qiit-elim" sig ctx dSp tel
  (w, wty) <- conclude env sig ctx dW >>= needEl
  alphaTy "el-qiit-elim (scrutinee)" wty (QSort sg k (cast es))
  o <- case qOrdinal QKSort sg k of
         Just x => pure x
         Nothing => kerr "derivation: el-qiit-elim: sort ordinal"
  motK <- case getAt o mots of
            Just m => pure m
            Nothing => kerr "derivation: el-qiit-elim: motive missing"
  pure (es, w, motK)

-- type formation
conclude env sig ctx DTyZero = pure (JTy ZeroTy)
conclude env sig ctx DTyOne = pure (JTy OneTy)
conclude env sig ctx DTyNat = pure (JTy NatTy)
conclude env sig ctx DTyUniv = pure (JTy UniverseTy)
conclude env sig ctx DTyProp = pure (JTy PropTy)
conclude env sig ctx (DTyPi dA dB) = do
  a <- conclude env sig ctx dA >>= needTy
  b <- conclude env sig (ctx :< a) dB >>= needTy
  pure (JTy (PiTy a b))
conclude env sig ctx (DTySigma dA dB) = do
  a <- conclude env sig ctx dA >>= needTy
  b <- conclude env sig (ctx :< a) dB >>= needTy
  pure (JTy (SigmaTy a b))
conclude env sig ctx (DTySum dA dB) = do
  a <- conclude env sig ctx dA >>= needTy
  b <- conclude env sig ctx dB >>= needTy
  pure (JTy (SumTy a b))
conclude env sig ctx (DTyEl dA) = do
  (a, ty) <- conclude env sig ctx dA >>= needEl
  alphaTy "ty-el" ty UniverseTy
  pure (JTy (El a))
conclude env sig ctx (DTyPrf dP) = do
  (p, ty) <- conclude env sig ctx dP >>= needEl
  alphaTy "ty-prf" ty PropTy
  pure (JTy (Prf p))
conclude env sig ctx (DTyQuot dA dR) = do
  a <- conclude env sig ctx dA >>= needTy
  (r, rty) <- conclude env sig (ctx :< a :< wkTy a) dR >>= needEl
  alphaTy "ty-quot" rty PropTy
  pure (JTy (QuotTy a r))
conclude env sig ctx (DTySig x dSub) = do
  (es, delta) <- conclude env sig ctx dSub >>= needSubN
  case sigLookup x sig of
    Just (SigDef gamma _ a TopTy) => do
      alphaCtx "el-sig-var (type entry)" delta gamma
      pure (JTy (SigVar x es))
    Just (SigDecl gamma _ TopTy) => do
      alphaCtx "el-sig-decl (type entry)" delta gamma
      pure (JTy (SigVar x es))
    _ => kerr "derivation: ty-sig: no type entry '\{x}'"
 where
  alphaCtx : String -> Ctx -> Ctx -> KM ()
  alphaCtx rule d g =
    if d == g then pure ()
    else kerr "derivation: \{rule}: entry context mismatch"

-- element typing
conclude env sig ctx (DElVar n) =
  case ctxAt ctx n of
    Just a => pure (JEl (CtxVar n) a)
    Nothing => kerr "derivation: el-var: index out of range"
conclude env sig ctx (DElSig x dSub) = do
  (es, delta) <- conclude env sig ctx dSub >>= needSubN
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
conclude env sig ctx DCodeZero = pure (JEl Elem.ZeroTy UniverseTy)
conclude env sig ctx DCodeOne = pure (JEl Elem.OneTy UniverseTy)
conclude env sig ctx DCodeNat = pure (JEl Elem.NatTy UniverseTy)
conclude env sig ctx (DCodePi dA dB) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "code-pi" aty UniverseTy
  (b, bty) <- conclude env sig (ctx :< El a) dB >>= needEl
  alphaTy "code-pi" bty UniverseTy
  pure (JEl (Elem.PiTy a b) UniverseTy)
conclude env sig ctx (DCodeSigma dA dB) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "code-sigma" aty UniverseTy
  (b, bty) <- conclude env sig (ctx :< El a) dB >>= needEl
  alphaTy "code-sigma" bty UniverseTy
  pure (JEl (Elem.SigmaTy a b) UniverseTy)
conclude env sig ctx (DCodeSum dA dB) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "code-sum" aty UniverseTy
  (b, bty) <- conclude env sig ctx dB >>= needEl
  alphaTy "code-sum" bty UniverseTy
  pure (JEl (Elem.SumTy a b) UniverseTy)
conclude env sig ctx (DCodeQuot dA dR) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "code-quot" aty UniverseTy
  (r, rty) <- conclude env sig (ctx :< El a :< wkTy (El a)) dR >>= needEl
  alphaTy "code-quot" rty PropTy
  pure (JEl (Elem.QuotTy a r) UniverseTy)
conclude env sig ctx (DCodeEq dT dL dR) = do
  t <- conclude env sig ctx dT >>= needTy
  (l, lty) <- conclude env sig ctx dL >>= needEl
  alphaTy "code-eq" lty t
  (r, rty) <- conclude env sig ctx dR >>= needEl
  alphaTy "code-eq" rty t
  pure (JEl (Elem.EqTy l r t) PropTy)
conclude env sig ctx (DCodeSquash dA) = do
  a <- conclude env sig ctx dA >>= needTy
  pure (JEl (Squash a) PropTy)
conclude env sig ctx (DElZeroE dA dT) = do
  a <- conclude env sig ctx dA >>= needTy
  (t, tty) <- conclude env sig ctx dT >>= needEl
  alphaTy "el-zero-e" tty ZeroTy
  pure (JEl (ZeroElim t) a)
conclude env sig ctx DElOneI = pure (JEl OneIntro OneTy)
conclude env sig ctx DElNatZ = pure (JEl NatIntro0 NatTy)
conclude env sig ctx (DElNatS dT) = do
  (t, tty) <- conclude env sig ctx dT >>= needEl
  alphaTy "el-nat-s" tty NatTy
  pure (JEl (NatIntro1 t) NatTy)
conclude env sig ctx (DElNatE dMot dZ dS dT) = do
  mot <- conclude env sig (ctx :< NatTy) dMot >>= needTy
  (z, zty) <- conclude env sig ctx dZ >>= needEl
  alphaTy "el-nat-e (z)" zty (substTy mot (Ext Id NatIntro0))
  (s, sty) <- conclude env sig (ctx :< NatTy :< mot) dS >>= needEl
  alphaTy "el-nat-e (s)" sty
    (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
  (t, tty) <- conclude env sig ctx dT >>= needEl
  alphaTy "el-nat-e (t)" tty NatTy
  pure (JEl (NatElim z s t) (substTy mot (Ext Id t)))
conclude env sig ctx (DElPiI dA dF) = do
  a <- conclude env sig ctx dA >>= needTy
  (f, b) <- conclude env sig (ctx :< a) dF >>= needEl
  pure (JEl (PiIntro f) (PiTy a b))
conclude env sig ctx (DElPiE dF dE dB) = do
  (f, fty) <- conclude env sig ctx dF >>= needEl
  case fty of
    PiTy a b => do
      (e, ety) <- conclude env sig ctx dE >>= needEl
      alphaTy "el-pi-e (arg)" ety a
      b' <- conclude env sig (ctx :< a) dB >>= needTy
      alphaTy "el-pi-e (cod)" b' b
      pure (JEl (PiApp f e) (substTy b (Ext Id e)))
    _ => kerr "derivation: el-pi-e: function premise not at a Π type"
conclude env sig ctx (DElLet dA dB) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  let hyp = Prf (Elem.EqTy (CtxVar 0) (wkEl a) (wkTy aty))
  (b, bty) <- conclude env sig (ctx :< aty :< hyp) dB >>= needEl
  pure (JEl (Let a b) (substTy bty (Ext (Ext Id a) Star)))
conclude env sig ctx (DElSigmaI dA dB dV) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  b <- conclude env sig (ctx :< aty) dB >>= needTy
  (v, vty) <- conclude env sig ctx dV >>= needEl
  alphaTy "el-sigma-i" vty (substTy b (Ext Id a))
  pure (JEl (SigmaIntro a v) (SigmaTy aty b))
conclude env sig ctx (DElSigmaE1 dT) = do
  (t, tty) <- conclude env sig ctx dT >>= needEl
  case tty of
    SigmaTy a _ => pure (JEl (SigmaElim1 t) a)
    _ => kerr "derivation: el-sigma-e₁: premise not at a ⨯ type"
conclude env sig ctx (DElSigmaE2 dT) = do
  (t, tty) <- conclude env sig ctx dT >>= needEl
  case tty of
    SigmaTy _ b => pure (JEl (SigmaElim2 t) (substTy b (Ext Id (SigmaElim1 t))))
    _ => kerr "derivation: el-sigma-e₂: premise not at a ⨯ type"
conclude env sig ctx (DElSumI1 dA dB) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  b <- conclude env sig ctx dB >>= needTy
  pure (JEl (Inj1 a) (SumTy aty b))
conclude env sig ctx (DElSumI2 dB dA) = do
  (b, bty) <- conclude env sig ctx dB >>= needEl
  a <- conclude env sig ctx dA >>= needTy
  pure (JEl (Inj2 b) (SumTy a bty))
conclude env sig ctx (DElSumE dT dC dL dR) = do
  (t, tty) <- conclude env sig ctx dT >>= needEl
  case tty of
    SumTy a b => do
      c <- conclude env sig (ctx :< SumTy a b) dC >>= needTy
      (l, lty) <- conclude env sig (ctx :< a) dL >>= needEl
      alphaTy "el-sum-e (l)" lty (substTy c (Ext Wk (Inj1 (CtxVar 0))))
      (r, rty) <- conclude env sig (ctx :< b) dR >>= needEl
      alphaTy "el-sum-e (r)" rty (substTy c (Ext Wk (Inj2 (CtxVar 0))))
      pure (JEl (SumElim l r t) (substTy c (Ext Id t)))
    _ => kerr "derivation: el-sum-e: scrutinee not at a ⊎ type"
conclude env sig ctx (DElSquashI dT) = do
  (_, a) <- conclude env sig ctx dT >>= needEl
  pure (JEl Star (Prf (Squash a)))
conclude env sig ctx (DElEqI dEq) = do
  (a0, a1, a) <- conclude env sig ctx dEq >>= needElEq
  pure (JEl Star (Prf (Elem.EqTy a0 a1 a)))
conclude env sig ctx (DElSquashEPrf dQ dS dT) = do
  (q, qty) <- conclude env sig ctx dQ >>= needEl
  alphaTy "el-squash-e-prf (q)" qty PropTy
  (_, sty) <- conclude env sig ctx dS >>= needEl
  case sty of
    Prf (Squash a) => do
      (_, tty) <- conclude env sig (ctx :< a) dT >>= needEl
      alphaTy "el-squash-e-prf (t)" tty (wkTy (Prf q))
      pure (JEl Star (Prf q))
    _ => kerr "derivation: el-squash-e-prf: premise not at a squash"
conclude env sig ctx (DElTyCoe dEq dA) = do
  (a0, a1) <- conclude env sig ctx dEq >>= needTyEq
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "el-ty-coe" aty a0
  pure (JEl a a1)

-- equality: equivalence, coercion, reflection
conclude env sig ctx (DElRefl dT) = do
  (t, a) <- conclude env sig ctx dT >>= needEl
  pure (JElEq t t a)
conclude env sig ctx (DElSym d) = do
  (t0, t1, a) <- conclude env sig ctx d >>= needElEq
  pure (JElEq t1 t0 a)
conclude env sig ctx (DElTrans d01 d12) = do
  (t0, t1, a) <- conclude env sig ctx d01 >>= needElEq
  (t1', t2, a') <- conclude env sig ctx d12 >>= needElEq
  alphaEl "el-trans (middle)" t1' t1
  alphaTy "el-trans (type)" a' a
  pure (JElEq t0 t2 a)
conclude env sig ctx (DTyRefl dT) = do
  a <- conclude env sig ctx dT >>= needTy
  pure (JTyEq a a)
conclude env sig ctx (DTySym d) = do
  (a0, a1) <- conclude env sig ctx d >>= needTyEq
  pure (JTyEq a1 a0)
conclude env sig ctx (DTyTrans d01 d12) = do
  (a0, a1) <- conclude env sig ctx d01 >>= needTyEq
  (a1', a2) <- conclude env sig ctx d12 >>= needTyEq
  alphaTy "ty-trans (middle)" a1' a1
  pure (JTyEq a0 a2)
conclude env sig ctx (DElEqTyCoe dTyEq dEq) = do
  (a0, a1) <- conclude env sig ctx dTyEq >>= needTyEq
  (t0, t1, a) <- conclude env sig ctx dEq >>= needElEq
  alphaTy "el-eq-ty-coe" a a0
  pure (JElEq t0 t1 a1)
conclude env sig ctx (DElReflect dS) = do
  (_, sty) <- conclude env sig ctx dS >>= needEl
  case sty of
    Prf (Elem.EqTy a0 a1 a) => pure (JElEq a0 a1 a)
    _ => kerr "derivation: el-reflect: premise not at a literal equality prop"
conclude env sig ctx (DElSigEq pos dSub) = do
  (es, delta) <- conclude env sig ctx dSub >>= needSubN
  case getAt pos (toList sig) of
    Just (SigEq gamma a0 a1 a) => do
      if delta == gamma then pure ()
        else kerr "derivation: el-sig-eq: entry context mismatch"
      pure (JElEq (substElem a0 (embed es)) (substElem a1 (embed es))
                  (substTy a (embed es)))
    _ => kerr "derivation: el-sig-eq: no constraint entry at position \{show pos}"
conclude env sig ctx (DTySigEq pos dSub) = do
  (es, delta) <- conclude env sig ctx dSub >>= needSubN
  case getAt pos (toList sig) of
    Just (SigEq gamma a0 a1 TopTy) => do
      if delta == gamma then pure ()
        else kerr "derivation: el-sig-eq (type constraint): entry context mismatch"
      pure (JTyEq (substTy a0 (embed es)) (substTy a1 (embed es)))
    _ => kerr "derivation: el-sig-eq: no type constraint at position \{show pos}"

-- equality: props and η
conclude env sig ctx (DElZeroProp d0 d1) = do
  (t0, ty0) <- conclude env sig ctx d0 >>= needEl
  alphaTy "el-zero-prop" ty0 ZeroTy
  (t1, ty1) <- conclude env sig ctx d1 >>= needEl
  alphaTy "el-zero-prop" ty1 ZeroTy
  pure (JElEq t0 t1 ZeroTy)
conclude env sig ctx (DElOneProp d0 d1) = do
  (t0, ty0) <- conclude env sig ctx d0 >>= needEl
  alphaTy "el-one-prop" ty0 OneTy
  (t1, ty1) <- conclude env sig ctx d1 >>= needEl
  alphaTy "el-one-prop" ty1 OneTy
  pure (JElEq t0 t1 OneTy)
conclude env sig ctx (DElPrfProp d0 d1) = do
  (t0, ty0) <- conclude env sig ctx d0 >>= needEl
  case ty0 of
    Prf p => do
      (t1, ty1) <- conclude env sig ctx d1 >>= needEl
      alphaTy "el-prf-prop" ty1 (Prf p)
      pure (JElEq t0 t1 (Prf p))
    _ => kerr "derivation: el-prf-prop: premise not at a Prf type"
conclude env sig ctx (DCodePropEq dP dQ dS dT) = do
  (p, pty) <- conclude env sig ctx dP >>= needEl
  alphaTy "code-prop-eq" pty PropTy
  (q, qty) <- conclude env sig ctx dQ >>= needEl
  alphaTy "code-prop-eq" qty PropTy
  (_, sty) <- conclude env sig (ctx :< Prf p) dS >>= needEl
  alphaTy "code-prop-eq (→)" sty (wkTy (Prf q))
  (_, tty) <- conclude env sig (ctx :< Prf q) dT >>= needEl
  alphaTy "code-prop-eq (←)" tty (wkTy (Prf p))
  pure (JElEq p q PropTy)
conclude env sig ctx (DElPiEta dF0 dF1 dEq) = do
  (f0, f0ty) <- conclude env sig ctx dF0 >>= needEl
  case f0ty of
    PiTy a b => do
      (f1, f1ty) <- conclude env sig ctx dF1 >>= needEl
      alphaTy "el-pi-eta (f₁)" f1ty (PiTy a b)
      (l, r, ety) <- conclude env sig (ctx :< a) dEq >>= needElEq
      alphaEl "el-pi-eta (l)" l (PiApp (wkEl f0) (CtxVar 0))
      alphaEl "el-pi-eta (r)" r (PiApp (wkEl f1) (CtxVar 0))
      alphaTy "el-pi-eta (ty)" ety b
      pure (JElEq f0 f1 (PiTy a b))
    _ => kerr "derivation: el-pi-eta: candidates not at a Π type"
conclude env sig ctx (DElSigmaEta dT0 dT1 dP1 dP2) = do
  (t0, t0ty) <- conclude env sig ctx dT0 >>= needEl
  case t0ty of
    SigmaTy a b => do
      (t1, t1ty) <- conclude env sig ctx dT1 >>= needEl
      alphaTy "el-sigma-eta (t₁)" t1ty (SigmaTy a b)
      (p1l, p1r, p1ty) <- conclude env sig ctx dP1 >>= needElEq
      alphaEl "el-sigma-eta (π₁ l)" p1l (SigmaElim1 t0)
      alphaEl "el-sigma-eta (π₁ r)" p1r (SigmaElim1 t1)
      alphaTy "el-sigma-eta (π₁ ty)" p1ty a
      (p2l, p2r, p2ty) <- conclude env sig ctx dP2 >>= needElEq
      alphaEl "el-sigma-eta (π₂ l)" p2l (SigmaElim2 t0)
      alphaEl "el-sigma-eta (π₂ r)" p2r (SigmaElim2 t1)
      alphaTy "el-sigma-eta (π₂ ty)" p2ty (substTy b (Ext Id (SigmaElim1 t0)))
      pure (JElEq t0 t1 (SigmaTy a b))
    _ => kerr "derivation: el-sigma-eta: candidates not at a ⨯ type"

-- equality: congruence
conclude env sig ctx (DElLamCong dA dF) = do
  a <- conclude env sig ctx dA >>= needTy
  (f0, f1, b) <- conclude env sig (ctx :< a) dF >>= needElEq
  pure (JElEq (PiIntro f0) (PiIntro f1) (PiTy a b))
conclude env sig ctx (DElAppCong dF dA dB) = do
  (f0, f1, fty) <- conclude env sig ctx dF >>= needElEq
  case fty of
    PiTy a b => do
      (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
      alphaTy "el-app-cong (arg)" aty a
      b' <- conclude env sig (ctx :< a) dB >>= needTy
      alphaTy "el-app-cong (cod)" b' b
      pure (JElEq (PiApp f0 a0) (PiApp f1 a1) (substTy b (Ext Id a1)))
    _ => kerr "derivation: el-app-cong: premise not at a Π type"
conclude env sig ctx (DElSucCong d) = do
  (t0, t1, a) <- conclude env sig ctx d >>= needElEq
  alphaTy "el-suc-cong" a NatTy
  pure (JElEq (NatIntro1 t0) (NatIntro1 t1) NatTy)
conclude env sig ctx (DElPairCong dA dB dV) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  b <- conclude env sig (ctx :< aty) dB >>= needTy
  (b0, b1, vty) <- conclude env sig ctx dV >>= needElEq
  alphaTy "el-pair-cong" vty (substTy b (Ext Id a1))
  pure (JElEq (SigmaIntro a0 b0) (SigmaIntro a1 b1) (SigmaTy aty b))
conclude env sig ctx (DElProj1Cong d) = do
  (t0, t1, tty) <- conclude env sig ctx d >>= needElEq
  case tty of
    SigmaTy a _ => pure (JElEq (SigmaElim1 t0) (SigmaElim1 t1) a)
    _ => kerr "derivation: el-proj₁-cong: premise not at a ⨯ type"
conclude env sig ctx (DElProj2Cong d) = do
  (t0, t1, tty) <- conclude env sig ctx d >>= needElEq
  case tty of
    SigmaTy _ b =>
      pure (JElEq (SigmaElim2 t0) (SigmaElim2 t1)
                  (substTy b (Ext Id (SigmaElim1 t1))))
    _ => kerr "derivation: el-proj₂-cong: premise not at a ⨯ type"
conclude env sig ctx (DTyPiCong dD dC) = do
  (a0, a1) <- conclude env sig ctx dD >>= needTyEq
  (b0, b1) <- conclude env sig (ctx :< a1) dC >>= needTyEq
  pure (JTyEq (PiTy a0 b0) (PiTy a1 b1))
conclude env sig ctx (DTySigmaCong dD dC) = do
  (a0, a1) <- conclude env sig ctx dD >>= needTyEq
  (b0, b1) <- conclude env sig (ctx :< a1) dC >>= needTyEq
  pure (JTyEq (SigmaTy a0 b0) (SigmaTy a1 b1))
conclude env sig ctx (DTySumCong dL dR) = do
  (a0, a1) <- conclude env sig ctx dL >>= needTyEq
  (b0, b1) <- conclude env sig ctx dR >>= needTyEq
  pure (JTyEq (SumTy a0 b0) (SumTy a1 b1))
conclude env sig ctx (DTyQuotCong dA dR) = do
  (a0, a1) <- conclude env sig ctx dA >>= needTyEq
  (r0, r1, rty) <- conclude env sig (ctx :< a1 :< wkTy a1) dR >>= needElEq
  alphaTy "ty-quot-cong" rty PropTy
  pure (JTyEq (QuotTy a0 r0) (QuotTy a1 r1))
conclude env sig ctx (DTyElCong d) = do
  (a, b, ty) <- conclude env sig ctx d >>= needElEq
  alphaTy "ty-el-cong" ty UniverseTy
  pure (JTyEq (El a) (El b))
conclude env sig ctx (DTyPrfCong d) = do
  (p, q, ty) <- conclude env sig ctx d >>= needElEq
  alphaTy "ty-prf-cong" ty PropTy
  pure (JTyEq (Prf p) (Prf q))


-- eliminator and remaining congruences
conclude env sig ctx (DElNatECong dMot dZ dS dT) = do
  mot <- conclude env sig (ctx :< NatTy) dMot >>= needTy
  (z0, z1, zty) <- conclude env sig ctx dZ >>= needElEq
  alphaTy "el-nat-e-cong (z)" zty (substTy mot (Ext Id NatIntro0))
  (s0, s1, sty) <- conclude env sig (ctx :< NatTy :< mot) dS >>= needElEq
  alphaTy "el-nat-e-cong (s)" sty
    (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
  (t0, t1, tty) <- conclude env sig ctx dT >>= needElEq
  alphaTy "el-nat-e-cong (t)" tty NatTy
  pure (JElEq (NatElim z0 s0 t0) (NatElim z1 s1 t1) (substTy mot (Ext Id t1)))
conclude env sig ctx (DElSumECong dT dC dL dR) = do
  (t0, t1, tty) <- conclude env sig ctx dT >>= needElEq
  case tty of
    SumTy a b => do
      c <- conclude env sig (ctx :< SumTy a b) dC >>= needTy
      (l0, l1, lty) <- conclude env sig (ctx :< a) dL >>= needElEq
      alphaTy "el-sum-e-cong (l)" lty (substTy c (Ext Wk (Inj1 (CtxVar 0))))
      (r0, r1, rty) <- conclude env sig (ctx :< b) dR >>= needElEq
      alphaTy "el-sum-e-cong (r)" rty (substTy c (Ext Wk (Inj2 (CtxVar 0))))
      pure (JElEq (SumElim l0 r0 t0) (SumElim l1 r1 t1) (substTy c (Ext Id t1)))
    _ => kerr "derivation: el-sum-e-cong: scrutinees not at a ⊎ type"
conclude env sig ctx (DElZeroECong dA d0 d1) = do
  a <- conclude env sig ctx dA >>= needTy
  (t0, t0ty) <- conclude env sig ctx d0 >>= needEl
  alphaTy "el-zero-e-cong" t0ty ZeroTy
  (t1, t1ty) <- conclude env sig ctx d1 >>= needEl
  alphaTy "el-zero-e-cong" t1ty ZeroTy
  pure (JElEq (ZeroElim t0) (ZeroElim t1) a)
conclude env sig ctx (DElQuotECong dQ dB dF0 dF1 dW0 dW1 dFeq) = do
  (q0, q1, qty) <- conclude env sig ctx dQ >>= needElEq
  case qty of
    QuotTy a r => do
      b <- conclude env sig (ctx :< QuotTy a r) dB >>= needTy
      let cse = substTy b (Ext Wk (Class (CtxVar 0)))
      (f0, f0ty) <- conclude env sig (ctx :< a) dF0 >>= needEl
      alphaTy "el-quot-e-cong (f₀)" f0ty cse
      (f1, f1ty) <- conclude env sig (ctx :< a) dF1 >>= needEl
      alphaTy "el-quot-e-cong (f₁)" f1ty cse
      let wk3 = Chain Wk (Chain Wk Wk)
      let wdCtx = ctx :< a :< wkTy a :< Prf r
      let wdTy = substTy b (Ext wk3 (Class (CtxVar 2)))
      (w0l, w0r, w0ty) <- conclude env sig wdCtx dW0 >>= needElEq
      alphaEl "el-quot-e-cong (wd₀ l)" w0l (substElem f0 (Ext wk3 (CtxVar 2)))
      alphaEl "el-quot-e-cong (wd₀ r)" w0r (substElem f0 (Ext wk3 (CtxVar 1)))
      alphaTy "el-quot-e-cong (wd₀ ty)" w0ty wdTy
      (w1l, w1r, w1ty) <- conclude env sig wdCtx dW1 >>= needElEq
      alphaEl "el-quot-e-cong (wd₁ l)" w1l (substElem f1 (Ext wk3 (CtxVar 2)))
      alphaEl "el-quot-e-cong (wd₁ r)" w1r (substElem f1 (Ext wk3 (CtxVar 1)))
      alphaTy "el-quot-e-cong (wd₁ ty)" w1ty wdTy
      (fl, fr, fety) <- conclude env sig (ctx :< a) dFeq >>= needElEq
      alphaEl "el-quot-e-cong (f⁼ l)" fl f0
      alphaEl "el-quot-e-cong (f⁼ r)" fr f1
      alphaTy "el-quot-e-cong (f⁼ ty)" fety cse
      pure (JElEq (QuotElim f0 q0) (QuotElim f1 q1) (substTy b (Ext Id q1)))
    _ => kerr "derivation: el-quot-e-cong: scrutinees not at a quotient type"
conclude env sig ctx (DElLetCong dA dB) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  let hyp = Prf (Elem.EqTy (CtxVar 0) (wkEl a1) (wkTy aty))
  (b0, b1, bty) <- conclude env sig (ctx :< aty :< hyp) dB >>= needElEq
  pure (JElEq (Let a0 b0) (Let a1 b1) (substTy bty (Ext (Ext Id a1) Star)))
conclude env sig ctx (DElClassCong dA dR) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  (r, rty) <- conclude env sig (ctx :< aty :< wkTy aty) dR >>= needEl
  alphaTy "el-class-cong" rty PropTy
  pure (JElEq (Class a0) (Class a1) (QuotTy aty r))
conclude env sig ctx (DElInj1Cong dA dB) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  b <- conclude env sig ctx dB >>= needTy
  pure (JElEq (Inj1 a0) (Inj1 a1) (SumTy aty b))
conclude env sig ctx (DElInj2Cong dB dA) = do
  (b0, b1, bty) <- conclude env sig ctx dB >>= needElEq
  a <- conclude env sig ctx dA >>= needTy
  pure (JElEq (Inj2 b0) (Inj2 b1) (SumTy a bty))
conclude env sig ctx (DCodePiCong dA dB) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  alphaTy "code-pi-cong" aty UniverseTy
  (b0, b1, bty) <- conclude env sig (ctx :< El a1) dB >>= needElEq
  alphaTy "code-pi-cong" bty UniverseTy
  pure (JElEq (Elem.PiTy a0 b0) (Elem.PiTy a1 b1) UniverseTy)
conclude env sig ctx (DCodeSigmaCong dA dB) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  alphaTy "code-sigma-cong" aty UniverseTy
  (b0, b1, bty) <- conclude env sig (ctx :< El a1) dB >>= needElEq
  alphaTy "code-sigma-cong" bty UniverseTy
  pure (JElEq (Elem.SigmaTy a0 b0) (Elem.SigmaTy a1 b1) UniverseTy)
conclude env sig ctx (DCodeSumCong dA dB) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  alphaTy "code-sum-cong" aty UniverseTy
  (b0, b1, bty) <- conclude env sig ctx dB >>= needElEq
  alphaTy "code-sum-cong" bty UniverseTy
  pure (JElEq (Elem.SumTy a0 b0) (Elem.SumTy a1 b1) UniverseTy)
conclude env sig ctx (DCodeQuotCong dA dR) = do
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  alphaTy "code-quot-cong" aty UniverseTy
  (r0, r1, rty) <- conclude env sig (ctx :< El a1 :< wkTy (El a1)) dR >>= needElEq
  alphaTy "code-quot-cong" rty PropTy
  pure (JElEq (Elem.QuotTy a0 r0) (Elem.QuotTy a1 r1) UniverseTy)
conclude env sig ctx (DCodeSquashCong dA) = do
  (a0, a1) <- conclude env sig ctx dA >>= needTyEq
  pure (JElEq (Squash a0) (Squash a1) PropTy)
conclude env sig ctx (DCodeEqCong dTy dA dB) = do
  (t0, t1) <- conclude env sig ctx dTy >>= needTyEq
  (a0, a1, aty) <- conclude env sig ctx dA >>= needElEq
  alphaTy "code-eq-cong (a)" aty t1
  (b0, b1, bty) <- conclude env sig ctx dB >>= needElEq
  alphaTy "code-eq-cong (b)" bty t1
  pure (JElEq (Elem.EqTy a0 b0 t0) (Elem.EqTy a1 b1 t1) PropTy)

-- injectivity (grouped conclusions split)
conclude env sig ctx (DTyPiInjDom dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- tyBinInj env sig ctx "ty-pi-inj" piProj dB0 dB1 dEq
  pure (JTyEq a0 a1)
conclude env sig ctx (DTyPiInjCod dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- tyBinInj env sig ctx "ty-pi-inj" piProj dB0 dB1 dEq
  pure (JTyEq b0 b1)
conclude env sig ctx (DTySigmaInjDom dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- tyBinInj env sig ctx "ty-sigma-inj" sgProj dB0 dB1 dEq
  pure (JTyEq a0 a1)
conclude env sig ctx (DTySigmaInjCod dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- tyBinInj env sig ctx "ty-sigma-inj" sgProj dB0 dB1 dEq
  pure (JTyEq b0 b1)
conclude env sig ctx (DTySumInjL dEq) = do
  (l, r) <- conclude env sig ctx dEq >>= needTyEq
  case (l, r) of
    (SumTy a0 _, SumTy a1 _) => pure (JTyEq a0 a1)
    _ => kerr "derivation: ty-sum-inj: not a ⊎ equation"
conclude env sig ctx (DTySumInjR dEq) = do
  (l, r) <- conclude env sig ctx dEq >>= needTyEq
  case (l, r) of
    (SumTy _ b0, SumTy _ b1) => pure (JTyEq b0 b1)
    _ => kerr "derivation: ty-sum-inj: not a ⊎ equation"
conclude env sig ctx (DTyQuotInjDom dR0 dR1 dEq) = do
  (a0, a1, r0, r1) <- tyQuotInj env sig ctx dR0 dR1 dEq
  pure (JTyEq a0 a1)
conclude env sig ctx (DTyQuotInjRel dR0 dR1 dEq) = do
  (a0, a1, r0, r1) <- tyQuotInj env sig ctx dR0 dR1 dEq
  pure (JElEq r0 r1 PropTy)
conclude env sig ctx (DTyElInj dEq) = do
  (l, r) <- conclude env sig ctx dEq >>= needTyEq
  case (l, r) of
    (El t0, El t1) => pure (JElEq t0 t1 UniverseTy)
    _ => kerr "derivation: ty-el-inj: not an El equation"
conclude env sig ctx (DCodePiInjDom dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- codeBinInj env sig ctx "code-pi-inj" piCProj dB0 dB1 dEq
  pure (JElEq a0 a1 UniverseTy)
conclude env sig ctx (DCodePiInjCod dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- codeBinInj env sig ctx "code-pi-inj" piCProj dB0 dB1 dEq
  pure (JElEq b0 b1 UniverseTy)
conclude env sig ctx (DCodeSigmaInjDom dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- codeBinInj env sig ctx "code-sigma-inj" sgCProj dB0 dB1 dEq
  pure (JElEq a0 a1 UniverseTy)
conclude env sig ctx (DCodeSigmaInjCod dB0 dB1 dEq) = do
  (a0, a1, b0, b1) <- codeBinInj env sig ctx "code-sigma-inj" sgCProj dB0 dB1 dEq
  pure (JElEq b0 b1 UniverseTy)
conclude env sig ctx (DCodeSumInjL dEq) = do
  (l, r, ty) <- conclude env sig ctx dEq >>= needElEq
  alphaTy "code-sum-inj" ty UniverseTy
  case (l, r) of
    (Elem.SumTy a0 _, Elem.SumTy a1 _) => pure (JElEq a0 a1 UniverseTy)
    _ => kerr "derivation: code-sum-inj: not a ⊎ code equation"
conclude env sig ctx (DCodeSumInjR dEq) = do
  (l, r, ty) <- conclude env sig ctx dEq >>= needElEq
  alphaTy "code-sum-inj" ty UniverseTy
  case (l, r) of
    (Elem.SumTy _ b0, Elem.SumTy _ b1) => pure (JElEq b0 b1 UniverseTy)
    _ => kerr "derivation: code-sum-inj: not a ⊎ code equation"
conclude env sig ctx (DCodeQuotInjDom dR0 dR1 dEq) = do
  (a0, a1, r0, r1) <- codeQuotInj env sig ctx dR0 dR1 dEq
  pure (JElEq a0 a1 UniverseTy)
conclude env sig ctx (DCodeQuotInjRel dR0 dR1 dEq) = do
  (a0, a1, r0, r1) <- codeQuotInj env sig ctx dR0 dR1 dEq
  pure (JElEq r0 r1 PropTy)

-- normal substitutions
conclude env sig ctx DSubNEmpty = pure (JSubN [<] [<])
conclude env sig ctx (DSubNExt dEs dA dE) = do
  (es, delta) <- conclude env sig ctx dEs >>= needSubN
  a <- conclude env sig delta dA >>= needTy
  (e, ety) <- conclude env sig ctx dE >>= needEl
  alphaTy "sub-norm-ext" ety (substTy a (embed es))
  pure (JSubN (es :< e) (delta :< a))


-- the remaining equivalence instances, ext-congruences, coercions
conclude env sig ctx (DCtxRefl d) = do
  g <- conclude env sig ctx d >>= needCtx
  pure (JCtxEq g g)
conclude env sig ctx (DCtxSym d) = do
  (g0, g1) <- conclude env sig ctx d >>= needCtxEq
  pure (JCtxEq g1 g0)
conclude env sig ctx (DCtxTrans d01 d12) = do
  (g0, g1) <- conclude env sig ctx d01 >>= needCtxEq
  (g1', g2) <- conclude env sig ctx d12 >>= needCtxEq
  if g1' == g1 then pure () else kerr "derivation: ctx-trans: middle mismatch"
  pure (JCtxEq g0 g2)
conclude env sig ctx (DCtxExtCong dG dA) = do
  (g0, g1) <- conclude env sig ctx dG >>= needCtxEq
  (a0, a1) <- conclude env sig g1 dA >>= needTyEq
  pure (JCtxEq (g0 :< a0) (g1 :< a1))
conclude env sig ctx (DSubRefl d) = do
  (s', d') <- conclude env sig ctx d >>= needSub
  pure (JSubEq s' s' d')
conclude env sig ctx (DSubSym d) = do
  (s0, s1, d') <- conclude env sig ctx d >>= needSubEq
  pure (JSubEq s1 s0 d')
conclude env sig ctx (DSubTrans d01 d12) = do
  (s0, s1, d') <- conclude env sig ctx d01 >>= needSubEq
  (s1', s2, d'') <- conclude env sig ctx d12 >>= needSubEq
  if s1' == s1 && d'' == d' then pure ()
    else kerr "derivation: sub-trans: middle mismatch"
  pure (JSubEq s0 s2 d')
conclude env sig ctx (DSubNRefl d) = do
  (es, d') <- conclude env sig ctx d >>= needSubN
  pure (JSubNEq es es d')
conclude env sig ctx (DSubNSym d) = do
  (e0, e1, d') <- conclude env sig ctx d >>= needSubNEq
  pure (JSubNEq e1 e0 d')
conclude env sig ctx (DSubNTrans d01 d12) = do
  (e0, e1, d') <- conclude env sig ctx d01 >>= needSubNEq
  (e1', e2, d'') <- conclude env sig ctx d12 >>= needSubNEq
  if e1' == e1 && d'' == d' then pure ()
    else kerr "derivation: sub-norm (trans): middle mismatch"
  pure (JSubNEq e0 e2 d')
conclude env sig ctx (DSubNExtCong dEs dA dT) = do
  (e0, e1, delta) <- conclude env sig ctx dEs >>= needSubNEq
  a <- conclude env sig delta dA >>= needTy
  (t0, t1, tty) <- conclude env sig ctx dT >>= needElEq
  alphaTy "sub-norm-ext-cong" tty (substTy a (embed e1))
  pure (JSubNEq (e0 :< t0) (e1 :< t1) (delta :< a))
conclude env sig ctx (DElSubCong dS dEq) = do
  (s0, s1, g1) <- conclude env sig ctx dS >>= needSubEq
  (t0, t1, a) <- conclude env sig g1 dEq >>= needElEq
  pure (JElEq (substElem t0 s0) (substElem t1 s1) (substTy a s1))
conclude env sig ctx (DTySubCong dS dEq) = do
  (s0, s1, g1) <- conclude env sig ctx dS >>= needSubEq
  (a0, a1) <- conclude env sig g1 dEq >>= needTyEq
  pure (JTyEq (substTy a0 s0) (substTy a1 s1))
conclude env sig ctx DTelEmpty = pure (JTel [])
conclude env sig ctx (DTelExt dA dD) = do
  a <- conclude env sig ctx dA >>= needTy
  d <- conclude env sig (ctx :< a) dD >>= needTel
  pure (JTel (a :: d))
conclude env sig ctx (DTelExtCong dA dD) = do
  (a0, a1) <- conclude env sig ctx dA >>= needTyEq
  (d0, d1) <- conclude env sig (ctx :< a1) dD >>= needTelEq
  pure (JTelEq (a0 :: d0) (a1 :: d1))
conclude env sig ctx (DTelRefl d) = do
  t <- conclude env sig ctx d >>= needTel
  pure (JTelEq t t)
conclude env sig ctx (DTelSym d) = do
  (d0, d1) <- conclude env sig ctx d >>= needTelEq
  pure (JTelEq d1 d0)
conclude env sig ctx (DTelTrans d01 d12) = do
  (d0, d1) <- conclude env sig ctx d01 >>= needTelEq
  (d1', d2) <- conclude env sig ctx d12 >>= needTelEq
  if d1' == d1 then pure () else kerr "derivation: tel-trans: middle mismatch"
  pure (JTelEq d0 d2)
conclude env sig ctx DSpEmpty = pure (JSp [] [])
conclude env sig ctx (DSpExt dE dD dEs) = do
  (e, a) <- conclude env sig ctx dE >>= needEl
  d <- conclude env sig (ctx :< a) dD >>= needTel
  (es, dInst) <- conclude env sig ctx dEs >>= needSp
  if dInst == map (\t => substTy t (Ext Id e)) d then pure ()
    else kerr "derivation: sp-ext: tail not at the instantiated telescope"
  pure (JSp (e :: es) (a :: d))
conclude env sig ctx (DSpExtCong dE dD dEs) = do
  (e0, e1, a) <- conclude env sig ctx dE >>= needElEq
  d <- conclude env sig (ctx :< a) dD >>= needTel
  (es0, es1, dInst) <- conclude env sig ctx dEs >>= needSpEq
  if dInst == map (\t => substTy t (Ext Id e1)) d then pure ()
    else kerr "derivation: sp-ext-cong: tails not at the instantiated telescope"
  pure (JSpEq (e0 :: es0) (e1 :: es1) (a :: d))
conclude env sig ctx (DSpRefl d) = do
  (es, d') <- conclude env sig ctx d >>= needSp
  pure (JSpEq es es d')
conclude env sig ctx (DSpSym d) = do
  (e0, e1, d') <- conclude env sig ctx d >>= needSpEq
  pure (JSpEq e1 e0 d')
conclude env sig ctx (DSpTrans d01 d12) = do
  (e0, e1, d') <- conclude env sig ctx d01 >>= needSpEq
  (e1', e2, d'') <- conclude env sig ctx d12 >>= needSpEq
  if e1' == e1 && d'' == d' then pure ()
    else kerr "derivation: sp-trans: middle mismatch"
  pure (JSpEq e0 e2 d')
conclude env sig ctx (DTyCoeCtx dG dA) = do
  (g0, g1) <- conclude env sig ctx dG >>= needCtxEq
  if ctx == g1 then pure ()
    else kerr "derivation: el-coe-ctx (at 𝕍): ambient is not the equation's right context"
  a <- conclude env sig g0 dA >>= needTy
  pure (JTy a)
conclude env sig ctx (DElCoeCtx dG dA) = do
  (g0, g1) <- conclude env sig ctx dG >>= needCtxEq
  if ctx == g1 then pure ()
    else kerr "derivation: el-coe-ctx: ambient is not the equation's right context"
  (a, aty) <- conclude env sig g0 dA >>= needEl
  pure (JEl a aty)
conclude env sig ctx (DTyEqCoeCtx dG dA) = do
  (g0, g1) <- conclude env sig ctx dG >>= needCtxEq
  if ctx == g1 then pure ()
    else kerr "derivation: el-eq-coe-ctx (at 𝕍): ambient is not the equation's right context"
  (a0, a1) <- conclude env sig g0 dA >>= needTyEq
  pure (JTyEq a0 a1)
conclude env sig ctx (DElEqCoeCtx dG dA) = do
  (g0, g1) <- conclude env sig ctx dG >>= needCtxEq
  if ctx == g1 then pure ()
    else kerr "derivation: el-eq-coe-ctx: ambient is not the equation's right context"
  (t0, t1, a) <- conclude env sig g0 dA >>= needElEq
  pure (JElEq t0 t1 a)

-- ADMISSIBLE: presupposition projection
conclude env sig ctx (DPresupElL d) = do
  (t0, _, a) <- conclude env sig ctx d >>= needElEq
  pure (JEl t0 a)
conclude env sig ctx (DPresupElR d) = do
  (_, t1, a) <- conclude env sig ctx d >>= needElEq
  pure (JEl t1 a)
conclude env sig ctx (DPresupElTy d) = do
  (_, a) <- conclude env sig ctx d >>= needEl
  pure (JTy a)
conclude env sig ctx (DPresupTyL d) = do
  (a0, _) <- conclude env sig ctx d >>= needTyEq
  pure (JTy a0)
conclude env sig ctx (DPresupTyR d) = do
  (_, a1) <- conclude env sig ctx d >>= needTyEq
  pure (JTy a1)

-- ADMISSIBLE: formation inversion (docs/NovaDerivations.txt) — the
-- cod instances replay their premise BELOW the top binder, which
-- must α-match the inverted domain
conclude env sig ctx (DInvPiDom d) = do
  t <- conclude env sig ctx d >>= needTy
  case t of
    PiTy a _ => pure (JTy a)
    _ => kerr "derivation: inv-pi-dom: premise not a Π formation"
conclude env sig ctx (DInvPiCod d) =
  case ctx of
    rest :< a' => do
      t <- conclude env sig rest d >>= needTy
      case t of
        PiTy a b => do
          alphaTy "inv-pi-cod (binder)" a a'
          pure (JTy b)
        _ => kerr "derivation: inv-pi-cod: premise not a Π formation"
    [<] => kerr "derivation: inv-pi-cod: empty context"
conclude env sig ctx (DInvSigmaDom d) = do
  t <- conclude env sig ctx d >>= needTy
  case t of
    SigmaTy a _ => pure (JTy a)
    _ => kerr "derivation: inv-sigma-dom: premise not a Σ formation"
conclude env sig ctx (DInvSigmaCod d) =
  case ctx of
    rest :< a' => do
      t <- conclude env sig rest d >>= needTy
      case t of
        SigmaTy a b => do
          alphaTy "inv-sigma-cod (binder)" a a'
          pure (JTy b)
        _ => kerr "derivation: inv-sigma-cod: premise not a Σ formation"
    [<] => kerr "derivation: inv-sigma-cod: empty context"
conclude env sig ctx (DInvPrfEqL d) = do
  t <- conclude env sig ctx d >>= needTy
  case t of
    Prf (Elem.EqTy a _ ty) => pure (JEl a ty)
    _ => kerr "derivation: inv-prf-eq-lhs: premise not a Prf-equality formation"
conclude env sig ctx (DInvPrfEqR d) = do
  t <- conclude env sig ctx d >>= needTy
  case t of
    Prf (Elem.EqTy _ b ty) => pure (JEl b ty)
    _ => kerr "derivation: inv-prf-eq-rhs: premise not a Prf-equality formation"
conclude env sig ctx (DInvPrfEqTy d) = do
  t <- conclude env sig ctx d >>= needTy
  case t of
    Prf (Elem.EqTy _ _ ty) => pure (JTy ty)
    _ => kerr "derivation: inv-prf-eq-ty: premise not a Prf-equality formation"
conclude env sig ctx (DInvPrfCode d) = do
  t <- conclude env sig ctx d >>= needTy
  case t of
    Prf p => pure (JEl p PropTy)
    _ => kerr "derivation: inv-prf-code: premise not a Prf formation"
conclude env sig ctx (DInvElCode d) = do
  t <- conclude env sig ctx d >>= needTy
  case t of
    El a => pure (JEl a UniverseTy)
    _ => kerr "derivation: inv-el-code: premise not an El formation"
conclude env sig ctx (DInvCodeEqL d) = do
  (c, cty) <- conclude env sig ctx d >>= needEl
  alphaTy "inv-code-eq-lhs" cty PropTy
  case c of
    Elem.EqTy l _ t => pure (JEl l t)
    _ => kerr "derivation: inv-code-eq-lhs: premise not an equality code"
conclude env sig ctx (DInvCodeEqR d) = do
  (c, cty) <- conclude env sig ctx d >>= needEl
  alphaTy "inv-code-eq-rhs" cty PropTy
  case c of
    Elem.EqTy _ r t => pure (JEl r t)
    _ => kerr "derivation: inv-code-eq-rhs: premise not an equality code"
conclude env sig ctx (DInvCodeEqTy d) = do
  (c, cty) <- conclude env sig ctx d >>= needEl
  alphaTy "inv-code-eq-ty" cty PropTy
  case c of
    Elem.EqTy _ _ t => pure (JTy t)
    _ => kerr "derivation: inv-code-eq-ty: premise not an equality code"

-- ADMISSIBLE: beta-at — replay is pure spelling surgery: descend the
-- path, demand a ≜ redex, contract (Nova.Kernel.Beta, one clause per
-- ≜ rule); the conclusion's right side is COMPUTED, and its typing
-- flows to consumers by presupposition
conclude env sig ctx (DBetaAt p d) = do
  (t, a) <- conclude env sig ctx d >>= needEl
  case contractAtE sig p t of
    Just t' => pure (JElEq t t' a)
    Nothing => kerr "derivation: beta-at: no ≜ redex at the path"
conclude env sig ctx (DBetaAtTy p d) = do
  a <- conclude env sig ctx d >>= needTy
  case contractAtT sig p a of
    Just a' => pure (JTyEq a a')
    Nothing => kerr "derivation: beta-at-ty: no ≜ redex at the path"

-- ADMISSIBLE: the nf oracle (the typing premise is load-bearing —
-- docs/NovaDerivations.txt)
conclude env sig ctx (DNfExpand d) = do
  (t, a) <- conclude env sig ctx d >>= needEl
  t' <- kElem sig t
  pure (JElEq t t' a)
conclude env sig ctx (DNfExpandTy d) = do
  a <- conclude env sig ctx d >>= needTy
  a' <- kTy sig a
  pure (JTyEq a a')
conclude env sig ctx (DShare cx d body) = do
  j <- conclude env sig cx d
  conclude (env ++ [(cx, j)]) sig ctx body
conclude env sig ctx (DRef i) =
  case inBounds' i env of
    Just (cx, j) =>
      if cx == ctx
        then pure j
        else kerr "derivation: share-ref cited outside its binding context"
    Nothing => kerr "derivation: share-ref out of range"
 where
  inBounds' : Nat -> List a -> Maybe a
  inBounds' _ [] = Nothing
  inBounds' Z (x :: _) = Just x
  inBounds' (S n) (_ :: rest) = inBounds' n rest
conclude env sig ctx (DNfEq d0 d1) = do
  (t0, a) <- conclude env sig ctx d0 >>= needEl
  (t1, a') <- conclude env sig ctx d1 >>= needEl
  alphaTy "nf-eq" a' a
  n0 <- kElem sig t0
  n1 <- kElem sig t1
  alphaEl "nf-eq" n0 n1
  pure (JElEq t0 t1 a)
conclude env sig ctx (DNfEqTy d0 d1) = do
  a0 <- conclude env sig ctx d0 >>= needTy
  a1 <- conclude env sig ctx d1 >>= needTy
  n0 <- kTy sig a0
  n1 <- kTy sig a1
  alphaTy "nf-eq-ty" n0 n1
  pure (JTyEq a0 a1)


-- quotients
conclude env sig ctx (DElQuotI dA dR) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  (r, rty) <- conclude env sig (ctx :< aty :< wkTy aty) dR >>= needEl
  alphaTy "el-quot-i" rty PropTy
  pure (JEl (Class a) (QuotTy aty r))
conclude env sig ctx (DElQuotEq dA dB dR dW) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  (b, bty) <- conclude env sig ctx dB >>= needEl
  alphaTy "el-quot-eq" bty aty
  (r, rty) <- conclude env sig (ctx :< aty :< wkTy aty) dR >>= needEl
  alphaTy "el-quot-eq" rty PropTy
  (_, wty) <- conclude env sig ctx dW >>= needEl
  alphaTy "el-quot-eq (witness)" wty
    (Prf (substElem r (Ext (Ext Id a) b)))
  pure (JElEq (Class a) (Class b) (QuotTy aty r))
conclude env sig ctx (DElQuotE dQ dB dF dResp) = do
  (q, qty) <- conclude env sig ctx dQ >>= needEl
  case qty of
    QuotTy a r => do
      b <- conclude env sig (ctx :< QuotTy a r) dB >>= needTy
      (f, fty) <- conclude env sig (ctx :< a) dF >>= needEl
      alphaTy "el-quot-e (case)" fty (substTy b (Ext Wk (Class (CtxVar 0))))
      let wk3 = Chain Wk (Chain Wk Wk)
      (l, r', ety) <- conclude env sig (ctx :< a :< wkTy a :< Prf r) dResp >>= needElEq
      alphaEl "el-quot-e (wd l)" l (substElem f (Ext wk3 (CtxVar 2)))
      alphaEl "el-quot-e (wd r)" r' (substElem f (Ext wk3 (CtxVar 1)))
      alphaTy "el-quot-e (wd ty)" ety (substTy b (Ext wk3 (Class (CtxVar 2))))
      pure (JEl (QuotElim f q) (substTy b (Ext Id q)))
    _ => kerr "derivation: el-quot-e: scrutinee not at a quotient type"
conclude env sig ctx (DElQuotEta dQ dB dG dF dResp dAg) = do
  (q, qty) <- conclude env sig ctx dQ >>= needEl
  case qty of
    QuotTy a r => do
      b <- conclude env sig (ctx :< QuotTy a r) dB >>= needTy
      (g, gty) <- conclude env sig (ctx :< QuotTy a r) dG >>= needEl
      alphaTy "el-quot-eta (g)" gty b
      (f, fty) <- conclude env sig (ctx :< a) dF >>= needEl
      alphaTy "el-quot-eta (f)" fty (substTy b (Ext Wk (Class (CtxVar 0))))
      let wk3 = Chain Wk (Chain Wk Wk)
      (l, r', ety) <- conclude env sig (ctx :< a :< wkTy a :< Prf r) dResp >>= needElEq
      alphaEl "el-quot-eta (wd l)" l (substElem f (Ext wk3 (CtxVar 2)))
      alphaEl "el-quot-eta (wd r)" r' (substElem f (Ext wk3 (CtxVar 1)))
      alphaTy "el-quot-eta (wd ty)" ety (substTy b (Ext wk3 (Class (CtxVar 2))))
      (gl, gr, aty') <- conclude env sig (ctx :< a) dAg >>= needElEq
      alphaEl "el-quot-eta (ag l)" gl (substElem g (Ext Wk (Class (CtxVar 0))))
      alphaEl "el-quot-eta (ag r)" gr f
      alphaTy "el-quot-eta (ag ty)" aty' (substTy b (Ext Wk (Class (CtxVar 0))))
      pure (JElEq (substElem g (Ext Id q)) (QuotElim f q) (substTy b (Ext Id q)))
    _ => kerr "derivation: el-quot-eta: scrutinee not at a quotient type"

-- the remaining η rules
conclude env sig ctx (DElNatEta dMot dF0 dF1 dZ dS dEqZ dEqS0 dEqS1 dT) = do
  mot <- conclude env sig (ctx :< NatTy) dMot >>= needTy
  (f0, f0ty) <- conclude env sig (ctx :< NatTy) dF0 >>= needEl
  alphaTy "el-nat-eta (f₀)" f0ty mot
  (f1, f1ty) <- conclude env sig (ctx :< NatTy) dF1 >>= needEl
  alphaTy "el-nat-eta (f₁)" f1ty mot
  (z, zty) <- conclude env sig ctx dZ >>= needEl
  alphaTy "el-nat-eta (z)" zty (substTy mot (Ext Id NatIntro0))
  (s, sty) <- conclude env sig (ctx :< NatTy :< mot) dS >>= needEl
  alphaTy "el-nat-eta (s)" sty
    (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
  (zl, zr, zety) <- conclude env sig ctx dEqZ >>= needElEq
  alphaEl "el-nat-eta (Z l)" zl (substElem f0 (Ext Id NatIntro0))
  alphaEl "el-nat-eta (Z r)" zr (substElem f1 (Ext Id NatIntro0))
  alphaTy "el-nat-eta (Z ty)" zety (substTy mot (Ext Id NatIntro0))
  let sSub = Ext Wk (NatIntro1 (CtxVar 0))
  (s0l, s0r, s0ty) <- conclude env sig (ctx :< NatTy) dEqS0 >>= needElEq
  alphaEl "el-nat-eta (S₀ l)" s0l (substElem f0 sSub)
  alphaEl "el-nat-eta (S₀ r)" s0r (substElem s (Ext Id f0))
  alphaTy "el-nat-eta (S₀ ty)" s0ty (substTy mot sSub)
  (s1l, s1r, s1ty) <- conclude env sig (ctx :< NatTy) dEqS1 >>= needElEq
  alphaEl "el-nat-eta (S₁ l)" s1l (substElem f1 sSub)
  alphaEl "el-nat-eta (S₁ r)" s1r (substElem s (Ext Id f1))
  alphaTy "el-nat-eta (S₁ ty)" s1ty (substTy mot sSub)
  (t, tty) <- conclude env sig ctx dT >>= needEl
  alphaTy "el-nat-eta (t)" tty NatTy
  pure (JElEq (substElem f0 (Ext Id t)) (substElem f1 (Ext Id t))
              (substTy mot (Ext Id t)))
conclude env sig ctx (DElSumEta dT dC dG dL dR dAgL dAgR) = do
  (t, tty) <- conclude env sig ctx dT >>= needEl
  case tty of
    SumTy a b => do
      c <- conclude env sig (ctx :< SumTy a b) dC >>= needTy
      (g, gty) <- conclude env sig (ctx :< SumTy a b) dG >>= needEl
      alphaTy "el-sum-eta (g)" gty c
      let lSub = Ext Wk (Inj1 (CtxVar 0))
      let rSub = Ext Wk (Inj2 (CtxVar 0))
      (l, lty) <- conclude env sig (ctx :< a) dL >>= needEl
      alphaTy "el-sum-eta (l)" lty (substTy c lSub)
      (r, rty) <- conclude env sig (ctx :< b) dR >>= needEl
      alphaTy "el-sum-eta (r)" rty (substTy c rSub)
      (all', alr, alty) <- conclude env sig (ctx :< a) dAgL >>= needElEq
      alphaEl "el-sum-eta (agl l)" all' (substElem g lSub)
      alphaEl "el-sum-eta (agl r)" alr l
      alphaTy "el-sum-eta (agl ty)" alty (substTy c lSub)
      (arl, arr, arty) <- conclude env sig (ctx :< b) dAgR >>= needElEq
      alphaEl "el-sum-eta (agr l)" arl (substElem g rSub)
      alphaEl "el-sum-eta (agr r)" arr r
      alphaTy "el-sum-eta (agr ty)" arty (substTy c rSub)
      pure (JElEq (substElem g (Ext Id t)) (SumElim l r t) (substTy c (Ext Id t)))
    _ => kerr "derivation: el-sum-eta: scrutinee not at a ⊎ type"

-- contexts and substitutions
conclude env sig ctx DCtxEmpty = pure (JCtx [<])
conclude env sig ctx (DCtxExt dG dA) = do
  g <- conclude env sig ctx dG >>= needCtx
  a <- conclude env sig g dA >>= needTy
  pure (JCtx (g :< a))
conclude env sig ctx DSubEmpty = pure (JSub Terminal [<])
conclude env sig ctx DSubId = pure (JSub Id ctx)
conclude env sig ctx DSubWk =
  case ctx of
    (rest :< _) => pure (JSub Wk rest)
    [<] => kerr "derivation: sub-wk: the ambient context is empty"
conclude env sig ctx (DSubExt dS dA dT) = do
  (s, g1) <- conclude env sig ctx dS >>= needSub
  a <- conclude env sig g1 dA >>= needTy
  (t, tty) <- conclude env sig ctx dT >>= needEl
  alphaTy "sub-ext" tty (substTy a s)
  pure (JSub (Ext s t) (g1 :< a))
conclude env sig ctx (DSubComp dS dT) = do
  (s, g1) <- conclude env sig ctx dS >>= needSub
  (t, g2) <- conclude env sig g1 dT >>= needSub
  pure (JSub (Chain t s) g2)
conclude env sig ctx (DSubExtCong dS dA dT) = do
  (s0, s1, g1) <- conclude env sig ctx dS >>= needSubEq
  a <- conclude env sig g1 dA >>= needTy
  (t0, t1, tty) <- conclude env sig ctx dT >>= needElEq
  alphaTy "sub-ext-cong" tty (substTy a s1)
  pure (JSubEq (Ext s0 t0) (Ext s1 t1) (g1 :< a))
conclude env sig ctx (DElSubCongFix dS dEq) = do
  (s, g1) <- conclude env sig ctx dS >>= needSub
  (t0, t1, a) <- conclude env sig g1 dEq >>= needElEq
  pure (JElEq (substElem t0 s) (substElem t1 s) (substTy a s))
conclude env sig ctx (DTySubCongFix dS dEq) = do
  (s, g1) <- conclude env sig ctx dS >>= needSub
  (a0, a1) <- conclude env sig g1 dEq >>= needTyEq
  pure (JTyEq (substTy a0 s) (substTy a1 s))

-- the ν layer
conclude env sig ctx DPolyHole = pure (JPoly PHole)
conclude env sig ctx (DPolyConst dA) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "poly-const" aty UniverseTy
  pure (JPoly (PConst a))
conclude env sig ctx (DPolyProd dF dG) = do
  f <- conclude env sig ctx dF >>= needPoly
  g <- conclude env sig ctx dG >>= needPoly
  pure (JPoly (PProd f g))
conclude env sig ctx (DPolySum dF dG) = do
  f <- conclude env sig ctx dF >>= needPoly
  g <- conclude env sig ctx dG >>= needPoly
  pure (JPoly (PSum f g))
conclude env sig ctx (DPolySigma dA dF) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "poly-sigma" aty UniverseTy
  f <- conclude env sig (ctx :< El a) dF >>= needPoly
  pure (JPoly (PSigma a f))
conclude env sig ctx (DPolyPi dA dF) = do
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "poly-pi" aty UniverseTy
  f <- conclude env sig (ctx :< El a) dF >>= needPoly
  pure (JPoly (PPi a f))
conclude env sig ctx (DTyNu dF) = do
  f <- conclude env sig ctx dF >>= needPoly
  pure (JTy (NuTy f))
conclude env sig ctx (DCodeNu dF) = do
  f <- conclude env sig ctx dF >>= needPoly
  pure (JEl (Elem.NuTy f) UniverseTy)
conclude env sig ctx (DElNuE dF dT) = do
  f <- conclude env sig ctx dF >>= needPoly
  (t, tty) <- conclude env sig ctx dT >>= needEl
  alphaTy "el-nu-e" tty (NuTy f)
  pure (JEl (Out t) (El (reflectPoly f (Elem.NuTy f))))
conclude env sig ctx (DElNuI dF dA dBody dX) = do
  f <- conclude env sig ctx dF >>= needPoly
  (a, aty) <- conclude env sig ctx dA >>= needEl
  alphaTy "el-nu-i (carrier)" aty UniverseTy
  (body, bty) <- conclude env sig (ctx :< El a) dBody >>= needEl
  alphaTy "el-nu-i (coalgebra)" bty (wkTy (El (reflectPoly f a)))
  (x, xty) <- conclude env sig ctx dX >>= needEl
  alphaTy "el-nu-i (seed)" xty (El a)
  pure (JEl (Corec f a body x) (NuTy f))
conclude env sig ctx (DElNuCoind dF dT0 dT1 dR dP dQ) = do
  f <- conclude env sig ctx dF >>= needPoly
  let nuT = NuTy f
  (t0, t0ty) <- conclude env sig ctx dT0 >>= needEl
  alphaTy "el-nu-coind (t₀)" t0ty nuT
  (t1, t1ty) <- conclude env sig ctx dT1 >>= needEl
  alphaTy "el-nu-coind (t₁)" t1ty nuT
  (r, rty) <- conclude env sig (ctx :< nuT :< substTy nuT Wk) dR >>= needEl
  alphaTy "el-nu-coind (R)" rty PropTy
  (_, pty) <- conclude env sig ctx dP >>= needEl
  alphaTy "el-nu-coind (endpoint)" pty
    (Prf (substElem r (Ext (Ext Id t0) t1)))
  let wk3 = Chain Wk (Chain Wk Wk)
  (_, qty) <- conclude env sig (ctx :< nuT :< substTy nuT Wk :< Prf r) dQ >>= needEl
  alphaTy "el-nu-coind (closure)" qty
    (Prf (liftPoly (substPoly f wk3) (substElem r (under (under wk3)))
            (Out (CtxVar 2)) (Out (CtxVar 1))))
  pure (JElEq t0 t1 nuT)

-- the ToS layer
conclude env sig ctx DQCtxEmpty = pure (JQCtx [<])
conclude env sig ctx (DQCtxExt dPhi dA) = do
  phi <- conclude env sig ctx dPhi >>= needQCtx
  a <- concludeQTy env sig ctx phi dA
  pure (JQCtx (phi :< a))
conclude env sig ctx (DQSig dPhi) = do
  phi <- conclude env sig ctx dPhi >>= needQCtx
  pure (JQSig (toList phi))
conclude env sig ctx d@DQTyUniv = kerr "derivation: qty node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTyEl _) = kerr "derivation: qty node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTyPiExt _ _) = kerr "derivation: qty node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTyPiInd _ _) = kerr "derivation: qty node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTmVar _) = kerr "derivation: qtm node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTmAppExt _ _) = kerr "derivation: qtm node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTmAppInd _ _) = kerr "derivation: qtm node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTmEq _ _) = kerr "derivation: qtm node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTmSub _ _) = kerr "derivation: qtm node outside the Γ;Φ zone"
conclude env sig ctx d@DQSubId = kerr "derivation: qsub node outside the Γ;Φ zone"
conclude env sig ctx d@DQSubWk = kerr "derivation: qsub node outside the Γ;Φ zone"
conclude env sig ctx d@(DQSubComp _ _) = kerr "derivation: qsub node outside the Γ;Φ zone"
conclude env sig ctx d@(DQSubExt _ _ _) = kerr "derivation: qsub node outside the Γ;Φ zone"
conclude env sig ctx d@(DQTySub _ _) = kerr "derivation: qty node outside the Γ;Φ zone"

-- the QIIT item layer
conclude env sig ctx (DCodeQSortInjIdx i d) = do
  (c0, c1, ty) <- conclude env sig ctx d >>= needElEq
  alphaTy "code-qiit-inj (universe)" ty UniverseTy
  case (c0, c1) of
    (QSort sg0 k0 es0, QSort sg1 k1 es1) => do
      if sg0 == sg1 && k0 == k1 then pure ()
        else kerr "derivation: code-qiit-inj: different signatures or sorts"
      let l0 = toList es0
      let l1 = toList es1
      if take i l0 == take i l1 then pure ()
        else kerr "derivation: code-qiit-inj: spines differ before i"
      (_, tel) <- qArity sg0 k0
      case (getAt i l0, getAt i l1, telInst tel i l0) of
        (Just a0, Just a1, Just e) => pure (JElEq a0 a1 e)
        _ => kerr "derivation: code-qiit-inj: index out of range"
    _ => kerr "derivation: code-qiit-inj: premise not between sort codes"
conclude env sig ctx (DTyQSort k dSig ds) = do
  sg <- conclude env sig ctx dSig >>= needQSig
  (entry, tel) <- qArity sg k
  es <- qSpine env "ty-qiit" sig ctx ds tel
  pure (JTy (QSort sg k (cast es)))
conclude env sig ctx (DTyQSortCong k dSig ds) = do
  sg <- conclude env sig ctx dSig >>= needQSig
  (_, tel) <- qArity sg k
  triples <- traverse (\d => conclude env sig ctx d >>= needElEq) ds
  let es0 = map (\(a, _, _) => a) triples
  let es1 = map (\(_, b, _) => b) triples
  if length es0 == length tel then pure ()
    else kerr "derivation: ty-qiit-cong: spine length mismatch"
  goChk tel 0 triples es0
  pure (JTyEq (QSort sg k (cast es0)) (QSort sg k (cast es1)))
 where
  goChk : List Ty -> Nat -> List (Elem, Elem, Ty) -> List Elem -> KM ()
  goChk tel i [] _ = pure ()
  goChk tel i ((_, _, ety) :: rest) es0 = do
    case telInst tel i es0 of
      Just want => alphaTy "ty-qiit-cong" ety want
      Nothing => kerr "derivation: ty-qiit-cong: telescope instantiation failed"
    goChk tel (S i) rest es0
conclude env sig ctx (DCodeQSort k dSig ds) = do
  sg <- conclude env sig ctx dSig >>= needQSig
  if qSigSmall sg then pure ()
    else kerr "derivation: code-qiit: signature not small"
  (entry, tel) <- qArity sg k
  es <- qSpine env "code-qiit" sig ctx ds tel
  pure (JEl (QSort sg k (cast es)) UniverseTy)
conclude env sig ctx (DQCtor k dSig ds) = do
  sg <- conclude env sig ctx dSig >>= needQSig
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: el-qiit-intro: position out of range"
  case qEntryKind entry of
    QKPoint => pure ()
    _ => kerr "derivation: el-qiit-intro: not a point constructor"
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  es <- qSpine env "el-qiit-intro" sig ctx ds tel
  (wEnd, hd) <- liftQE (walkVals sg (qwAt k) entry es)
  (srt, idx) <- liftQE (pointHead sg wEnd hd)
  pure (JEl (QCtor sg k (cast es)) (QSort sg srt idx))
conclude env sig ctx (DQCtorCong k dSig ds) = do
  sg <- conclude env sig ctx dSig >>= needQSig
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: el-qiit-intro-cong: position out of range"
  case qEntryKind entry of
    QKPoint => pure ()
    _ => kerr "derivation: el-qiit-intro-cong: not a point constructor"
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  triples <- traverse (\d => conclude env sig ctx d >>= needElEq) ds
  let es0 = map (\(a, _, _) => a) triples
  let es1 = map (\(_, b, _) => b) triples
  if length es0 == length tel then pure ()
    else kerr "derivation: el-qiit-intro-cong: spine length mismatch"
  goChk tel 0 triples es0
  (wEnd, hd) <- liftQE (walkVals sg (qwAt k) entry es0)
  (srt, idx) <- liftQE (pointHead sg wEnd hd)
  pure (JElEq (QCtor sg k (cast es0)) (QCtor sg k (cast es1)) (QSort sg srt idx))
 where
  goChk : List Ty -> Nat -> List (Elem, Elem, Ty) -> List Elem -> KM ()
  goChk tel i [] _ = pure ()
  goChk tel i ((_, _, ety) :: rest) es0 = do
    case telInst tel i es0 of
      Just want => alphaTy "el-qiit-intro-cong" ety want
      Nothing => kerr "derivation: el-qiit-intro-cong: telescope instantiation failed"
    goChk tel (S i) rest es0
conclude env sig ctx (DQMot dSig ds) = do
  sg <- conclude env sig ctx dSig >>= needQSig
  mots <- goMots sg (qPositions QKSort sg) ds
  pure (JMot sg mots)
 where
  goMots : QSig -> List Nat -> List Deriv -> KM (List Ty)
  goMots sg [] [] = pure []
  goMots sg (sj :: sjs) (d :: rest) = do
    (mctx, _, _) <- qSortCtx sig ctx sg sj
    mot <- conclude env sig mctx d >>= needTy
    more <- goMots sg sjs rest
    pure (mot :: more)
  goMots _ _ _ = kerr "derivation: mot: motive count mismatch"
conclude env sig ctx (DQDalg dMot ds) = do
  (sg, mots) <- conclude env sig ctx dMot >>= needMot
  mths <- goMths sg mots (qPositions QKPoint sg) ds
  pure (JDalg sg mots mths)
 where
  goMths : QSig -> List Ty -> List Nat -> List Deriv -> KM (List Elem)
  goMths sg mots [] [] = pure []
  goMths sg mots (cj :: cjs) (d :: rest) = do
    mty <- liftQE (methodTy sg mots cj)
    (m, mty') <- conclude env sig ctx d >>= needEl
    alphaTy "dalg (method)" mty' mty
    more <- goMths sg mots cjs rest
    pure (m :: more)
  goMths _ _ _ _ = kerr "derivation: dalg: method count mismatch"
conclude env sig ctx (DQEProb dDalg ds) = do
  (sg, mots, mths) <- conclude env sig ctx dDalg >>= needDalg
  goCohs sg mots mths (qPositions QKEq sg) ds
  pure (JEProb sg mots mths)
 where
  goCohs : QSig -> List Ty -> List Elem -> List Nat -> List Deriv -> KM ()
  goCohs sg mots mths [] [] = pure ()
  goCohs sg mots mths (ej :: ejs) (d :: rest) = do
    (dtel, _, lhs, rhs, cty) <- liftQE (coherenceAt sg mots mths ej)
    let cctx = foldl (:<) ctx dtel
    (l, r, ety) <- conclude env sig cctx d >>= needElEq
    alphaEl "eprob (coherence l)" l lhs
    alphaEl "eprob (coherence r)" r rhs
    alphaTy "eprob (coherence ty)" ety cty
    goCohs sg mots mths ejs rest
  goCohs _ _ _ _ _ = kerr "derivation: eprob: coherence count mismatch"
conclude env sig ctx (DQSect dMot ds) = do
  (sg, mots) <- conclude env sig ctx dMot >>= needMot
  hs <- goSects sg mots (qPositions QKSort sg) ds
  pure (JSect sg mots hs)
 where
  goSects : QSig -> List Ty -> List Nat -> List Deriv -> KM (List Elem)
  goSects sg mots [] [] = pure []
  goSects sg mots (sj :: sjs) (d :: rest) = do
    (mctx, _, so) <- qSortCtx sig ctx sg sj
    mot <- case getAt so mots of
             Just m => pure m
             Nothing => kerr "derivation: sect: motive missing"
    (h, hty) <- conclude env sig mctx d >>= needEl
    alphaTy "sect" hty mot
    more <- goSects sg mots sjs rest
    pure (h :: more)
  goSects _ _ _ _ = kerr "derivation: sect: candidate count mismatch"
conclude env sig ctx (DQElim k dEP dSp dW) = do
  (sg, mots, mths) <- conclude env sig ctx dEP >>= needEProb
  (es, w, motK) <- qElimEnd env sig ctx sg mots k dSp dW
  pure (JEl (QElim sg k mots mths (cast es) w)
            (substTy motK (Ext (foldl Ext Id es) w)))
conclude env sig ctx (DQEta k dEP dSect dAgs dSp dW) = do
  (sg, mots, mths) <- conclude env sig ctx dEP >>= needEProb
  (sg', mots', hs) <- conclude env sig ctx dSect >>= needSect
  if sg' == sg && mots' == mots then pure ()
    else kerr "derivation: el-qiit-eta: sect premise at a different problem"
  goAgrees sg mots mths hs (qPositions QKPoint sg) dAgs
  (es, w, motK) <- qElimEnd env sig ctx sg mots k dSp dW
  so <- case qOrdinal QKSort sg k of
          Just x => pure x
          Nothing => kerr "derivation: el-qiit-eta: sort ordinal"
  hK <- case getAt so hs of
          Just h => pure h
          Nothing => kerr "derivation: el-qiit-eta: candidate missing"
  pure (JElEq (substElem hK (Ext (foldl Ext Id es) w))
              (QElim sg k mots mths (cast es) w)
              (substTy motK (Ext (foldl Ext Id es) w)))
 where
  goAgrees : QSig -> List Ty -> List Elem -> List Elem -> List Nat -> List Deriv -> KM ()
  goAgrees sg mots mths hs [] [] = pure ()
  goAgrees sg mots mths hs (cj :: cjs) (d :: rest) = do
    cjE <- case qEntry sg cj of
             Just x => pure x
             Nothing => kerr "derivation: el-qiit-eta: ctor out of range"
    (tel, wEnd, hd) <- liftQE (reflTel sg (qwAt cj) cjE)
    let cctx = foldl (:<) ctx tel
    (srt, idx) <- liftQE (pointHead sg wEnd hd)
    so <- case qOrdinal QKSort sg srt of
            Just x => pure x
            Nothing => kerr "derivation: el-qiit-eta: sort ordinal"
    hS <- case getAt so hs of
            Just h => pure h
            Nothing => kerr "derivation: el-qiit-eta: candidate missing"
    motS <- case getAt so mots of
              Just m => pure m
              Nothing => kerr "derivation: el-qiit-eta: motive missing"
    let ctor = QCtor sg cj (varSpine (length tel))
    let inst = Ext (foldl Ext Id (toList idx)) ctor
    rhs <- liftQE (qSectRhs sg mots mths hs cj (varSpine (length tel)))
    (l, r, ety) <- conclude env sig cctx d >>= needElEq
    alphaEl "el-qiit-eta (agreement l)" l (substElem hS inst)
    alphaEl "el-qiit-eta (agreement r)" r rhs
    alphaTy "el-qiit-eta (agreement ty)" ety (substTy motS inst)
    goAgrees sg mots mths hs cjs rest
  goAgrees _ _ _ _ _ _ = kerr "derivation: el-qiit-eta: agreement count mismatch"
conclude env sig ctx (DQPath k dSig ds) = do
  sg <- conclude env sig ctx dSig >>= needQSig
  entry <- case qEntry sg k of
             Just e => pure e
             Nothing => kerr "derivation: el-qiit-path: position out of range"
  case qEntryKind entry of
    QKEq => pure ()
    _ => kerr "derivation: el-qiit-path: not an equation constructor"
  (tel, _, _) <- liftQE (reflTel sg (qwAt k) entry)
  es <- qSpine env "el-qiit-path" sig ctx ds tel
  (wEnd, hd) <- liftQE (walkVals sg (qwAt k) entry es)
  (lq, rq, uq) <- liftQE (eqHead hd)
  l <- liftQE (reflTm sg wEnd lq)
  r <- liftQE (reflTm sg wEnd rq)
  t <- liftQE (reflCodeTy sg wEnd uq)
  pure (JElEq l r t)

-- ===== The ToS family (dual zone Γ ; Φ) =====

concludeQTy env sig ctx phi DQTyUniv = pure QU
concludeQTy env sig ctx phi (DQTyEl dT) = do
  (t, tty) <- concludeQTm env sig ctx phi dT
  case tty of
    QU => pure (QEl t)
    _ => kerr "derivation: qty-el: code premise not at U"
concludeQTy env sig ctx phi (DQTyPiExt dA dB) = do
  a <- conclude env sig ctx dA >>= needTy
  b <- concludeQTy env sig (ctx :< a) (phiWkNova phi) dB
  pure (QPiExt a b)
concludeQTy env sig ctx phi (DQTyPiInd dT dB) = do
  (t, tty) <- concludeQTm env sig ctx phi dT
  case tty of
    QU => do
      b <- concludeQTy env sig ctx (phi :< QEl t) dB
      pure (QPiInd t b)
    _ => kerr "derivation: qty-pi-ind: domain code not at U"
concludeQTy env sig ctx phi (DQTySub dS dA) = do
  (sg, phi1) <- concludeQSub env sig ctx phi dS
  a <- concludeQTy env sig ctx phi1 dA
  pure (qSubTy sg a)
concludeQTy env sig ctx phi d = kerr "derivation: expected a qty node"

concludeQTm env sig ctx phi (DQTmVar i) =
  case phiAt phi i of
    Just a => pure (QVar i, a)
    Nothing => kerr "derivation: qtm-var: index out of range"
concludeQTm env sig ctx phi (DQTmAppExt dF dE) = do
  (f, fty) <- concludeQTm env sig ctx phi dF
  case fty of
    QPiExt a b => do
      (e, ety) <- conclude env sig ctx dE >>= needEl
      alphaTy "qtm-app-ext" ety a
      pure (QAppE f e, substQTy b (Ext Id e))
    _ => kerr "derivation: qtm-app-ext: not at an external ⇛"
concludeQTm env sig ctx phi (DQTmAppInd dF dA) = do
  (f, fty) <- concludeQTm env sig ctx phi dF
  case fty of
    QPiInd u b => do
      (a, aty) <- concludeQTm env sig ctx phi dA
      if aty == QEl u then pure ()
        else kerr "derivation: qtm-app-ind: argument not at the domain sort"
      pure (QAppI f a, qSubTy (QSExt QSId a) b)
    _ => kerr "derivation: qtm-app-ind: not at an inductive ⇛"
concludeQTm env sig ctx phi (DQTmEq dL dR) = do
  (l, lty) <- concludeQTm env sig ctx phi dL
  (r, rty) <- concludeQTm env sig ctx phi dR
  case (lty, rty) of
    (QEl u, QEl u') =>
      if u == u'
        then pure (QEqC l r u, QU)
        else kerr "derivation: qtm-eq: sides at different sorts"
    _ => kerr "derivation: qtm-eq: sides not at El of a sort"
concludeQTm env sig ctx phi (DQTmSub dS dT) = do
  (sg, phi1) <- concludeQSub env sig ctx phi dS
  (t, a) <- concludeQTm env sig ctx phi1 dT
  pure (qSubTm sg t, qSubTy sg a)
concludeQTm env sig ctx phi d = kerr "derivation: expected a qtm node"

concludeQSub env sig ctx phi DQSubId = pure (QSId, phi)
concludeQSub env sig ctx phi DQSubWk =
  case phi of
    (rest :< _) => pure (QSWk, rest)
    [<] => kerr "derivation: qsub-wk: the ToS zone is empty"
concludeQSub env sig ctx phi (DQSubComp dS dT) = do
  (sg, phi1) <- concludeQSub env sig ctx phi dS
  (tau, phi2) <- concludeQSub env sig ctx phi1 dT
  pure (QSComp tau sg, phi2)
concludeQSub env sig ctx phi (DQSubExt dS dA dT) = do
  (sg, phi1) <- concludeQSub env sig ctx phi dS
  a <- concludeQTy env sig ctx phi1 dA
  (t, tty) <- concludeQTm env sig ctx phi dT
  if tty == qSubTy sg a then pure ()
    else kerr "derivation: qsub-ext: entry not at 𝔄[ς]"
  pure (QSExt sg t, phi1 :< a)
concludeQSub env sig ctx phi d = kerr "derivation: expected a qsub node"

-- ===== Entry point =====

||| Check a derivation in the empty context with the given fuel;
||| Left is the rejection reason (fuel exhaustion included).
export
concludeItem : Sig -> Nat -> Deriv -> Either KErr Judg
concludeItem sig fuel d = map fst (runKM (conclude [] sig [<] d) fuel)

||| Check a derivation in a given context input (a solution's
||| telescope); the context's own formation is the caller's burden
||| (acceptSolItem replays it first).
export
concludeAt : Sig -> Nat -> Ctx -> Deriv -> Either KErr Judg
concludeAt sig fuel ctx d = map fst (runKM (conclude [] sig ctx d) fuel)

-- ===== ITEM ACCEPTANCE (docs/NovaDerivations.txt, "Items and
-- acceptance") — the seat's trusted half: replay the derivations the
-- elaborator EMITTED and demand they conclude EXACTLY the item's
-- stated judgements. =====

||| A def item: the type's formation and the body's typing, both in
||| the empty context.
export
acceptDefItem : Sig -> Nat -> (Deriv, Deriv) -> Ty -> Elem -> Either KErr ()
acceptDefItem sig fuel (dT, dt) ty body = do
  jT <- concludeItem sig fuel dT
  case jT of
    JTy t =>
      if t == ty then Right ()
      else Left "acceptance: type formation concluded [\{show t}] expected [\{show ty}]"
    _ => Left "acceptance: type derivation concluded a non-formation judgement"
  jt <- concludeItem sig fuel dt
  case jt of
    JEl b bty =>
      if b == body && bty == ty then Right ()
      else Left "acceptance: body typing concluded a different judgement"
    _ => Left "acceptance: body derivation concluded a non-typing judgement"

||| A type item: one formation derivation in the empty context.
export
acceptTyDefItem : Sig -> Nat -> Deriv -> Ty -> Either KErr ()
acceptTyDefItem sig fuel dT ty = do
  jT <- concludeItem sig fuel dT
  case jT of
    JTy t =>
      if t == ty then Right ()
      else Left "acceptance: type item concluded a different spelling"
    _ => Left "acceptance: type item concluded a non-formation judgement"

||| A hole solution: the telescope's formation replayed first (the
||| soundness reading's residual condition discharged at this root),
||| then the type and body in the telescope context.
||| CAVEAT (dormant): encodes the SOURCE branch's hole story — "a
||| solution is a later Σ item replayed against the final signature".
||| This branch removed hole support (Σ only ever extends); a revival
||| keeps conclude + acceptDefItem/acceptTyDefItem as-is and
||| re-derives this pair from whatever the metavariable redesign
||| lands on (ProvingFeedback E-1/E-1½).
export
acceptSolItem : Sig -> Nat -> (Deriv, Deriv, Deriv) -> Ctx -> Ty -> Elem -> Either KErr ()
acceptSolItem sig fuel (dCtx, dT, dt) delta ty body = do
  jC <- concludeItem sig fuel dCtx
  case jC of
    JCtx g =>
      if g == delta then Right ()
      else Left "acceptance: solution telescope concluded a different context"
    _ => Left "acceptance: solution telescope concluded a non-context judgement"
  jT <- concludeAt sig fuel delta dT
  case jT of
    JTy t =>
      if t == ty then Right ()
      else Left "acceptance: solution type concluded a different spelling"
    _ => Left "acceptance: solution type concluded a non-formation judgement"
  jt <- concludeAt sig fuel delta dt
  case jt of
    JEl b bty =>
      if b == body && bty == ty then Right ()
      else Left "acceptance: solution body concluded a different judgement"
    _ => Left "acceptance: solution body concluded a non-typing judgement"

||| A type-valued hole solution. Same dormancy caveat as
||| acceptSolItem above.
export
acceptTySolItem : Sig -> Nat -> (Deriv, Deriv) -> Ctx -> Ty -> Either KErr ()
acceptTySolItem sig fuel (dCtx, dT) delta ty = do
  jC <- concludeItem sig fuel dCtx
  case jC of
    JCtx g =>
      if g == delta then Right ()
      else Left "acceptance: solution telescope concluded a different context"
    _ => Left "acceptance: solution telescope concluded a non-context judgement"
  jT <- concludeAt sig fuel delta dT
  case jT of
    JTy t =>
      if t == ty then Right ()
      else Left "acceptance: solution type concluded a different spelling"
    _ => Left "acceptance: solution type concluded a non-formation judgement"
