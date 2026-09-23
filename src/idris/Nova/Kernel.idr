module Nova.Kernel

-- The TRUSTED side of the pipeline (docs/NovaPipeline.txt): certificate
-- replay for equality, over fuel-bounded beta.
--
-- Nothing here searches and nothing here chooses. The only ingredients:
--   * substitution (Nova.Kernel.Subst — the floor of every kernel);
--   * a fuel-bounded normalizer mirroring Foundation's ≜ rules clause
--     for clause (fuel exhaustion = REJECT, so every call terminates);
--   * mechanical replay of certificate steps: check a step's proof
--     element, derive the licensed equation from its type (reflection),
--     optionally take same-headed components (Foundation's injectivity
--     rules / derivable congruences), rewrite at the given path, and
--     compare normal forms;
--   * the type-directed finals: el-zero-prop/el-one-prop, quotient
--     witnesses (el-quot-eq), el-pi-eta/el-sigma-eta.
--
-- The discharge engine (untrusted) EMITS certificates; a discharge
-- counts only if it replays here. See Nova.Elaboration.

import Data.List
import Data.Maybe
import Data.SnocList
import Data.SortedMap

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT

%default covering

-- ===== Certificates =====

mutual
  ||| Component selectors: from a licensed equation between same-headed
  ||| terms, pass to a component equation. Justified by Foundation's
  ||| injectivity rules (codes) or derivable congruences (S via pred).
  ||| Binder components carry their instantiation (el-sub-cong-fix) as
  ||| a PROOF stating the element at the domain (a self or checked
  ||| leaf, ascribed where spelled otherwise).
  public export
  data Sel : Type where
    SelSuc : Sel                       -- S x ≐ S y ⇒ x ≐ y : ℕ
    SelDom : Sel                       -- (a₀→b₀) ≐ (a₁→b₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌 (also ×)
    SelCod : Prf -> Sel                -- ⇒ b₀[id,u] ≐ b₁[id,u] : 𝕌 (also ×)
    SelSumL : Sel                      -- (a₀⊎b₀) ≐ (a₁⊎b₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌
    SelSumR : Sel                      -- ⇒ b₀ ≐ b₁ : 𝕌 (non-dependent: no
                                       -- binder, no instantiation element)
    SelQDom : Sel                      -- (a₀/r₀) ≐ (a₁/r₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌
    SelQRel : Prf -> Prf -> Sel        -- ⇒ r₀[id,u,v] ≐ r₁[id,u,v] : 𝕌
    SelQIdx : Nat -> Sel               -- 𝒮.s ē₀ ≐ 𝒮.s ē₁ : 𝕌 ⇒ ē₀ᵢ ≐ ē₁ᵢ (QIIT
                                       -- code injectivity, indexwise; the spines
                                       -- must agree before i)

  public export
  data Payload : Type where
    ||| eliminator motive (ℕ-elim: over Γ ▷ ℕ; quot-elim: over Γ ▷ A/R)
    PMotive : Ty -> Skel -> Payload
    ||| expected type of an introduction form in inference position
    PIntroTy : Ty -> Skel -> Payload
    ||| conversion proof at a switch site (inferred ≐ expected)
    PSwitch : Prf -> Payload
    ||| the equation behind a ⋆ checked at an equality prop (el-eq-i)
    PReflEq : Prf -> Payload
    ||| quot-elim well-definedness (f respects R)
    PWD : Prf -> Payload
    ||| head exposure at a checked introduction form: the expected type
    ||| rewritten to expose its Π/Σ/quotient/≡ head, with the proof of
    ||| the conversion. The exposed type's own well-formedness follows
    ||| from the original's by subject reduction; the intro checks
    ||| against the exposed form and coercion transports the result.
    PExpose : Ty -> Prf -> Payload
    ||| head exposure of an ELIMINATION's scrutinee type (the function
    ||| of an application, the pair projected, the ⊎/quotient/ν
    ||| scrutinee): the inferred type rewritten to expose its head,
    ||| with the proof of the conversion — the inference-side twin of
    ||| PExpose
    PScrut : Ty -> Prf -> Payload
    ||| the witness behind a checked ⋆ : ∥A∥ (el-squash-i: an
    ||| inhabitant of the squashee)
    PSquashWit : Elem -> Skel -> Payload
    ||| the hypothetical proof behind a checked squash-elim
    ||| (el-squash-e-prf): scrutinee inhabiting ∥A∥, plus a body
    ||| proving q[↑] under the raw squashee A
    ||| The scrutinee's type may arrive EXPOSED (its ∥·∥ head, or the
    ||| squashee's head, reached by unfolding): the exposed type plus
    ||| the proof from the inferred one, as at PExpose — the body's
    ||| hypothesis is then the squashee in the spelling the producer
    ||| checked the body against
    ||| — and the GOAL's skeleton, for its prop-ness question (a
    ||| neutral goal infers at Ω through its skeleton)
    PSquashElim : Elem -> Skel -> Maybe (Ty, Prf) -> Elem -> Skel -> Skel -> Payload
    ||| QIIT eliminator MOTIVES — one type per sort entry of the carried
    ||| signature, over Γ·⌊𝔎⌋ᵗ ▷ 𝒮.𝕤 δ, each with its skeleton (the core
    ||| eliminator carries only the methods: what β reads)
    PQMotives : List Ty -> List Skel -> Payload
    ||| QIIT eliminator coherences — one proof per equation entry of
    ||| the carried signature, checked in the entry's ᴰ-context (the
    ||| QIIT generalization of quot-elim's wd)
    PQCoh : List Prf -> Payload
    ||| coinduction behind a ⋆ checked at an equality prop over a
    ||| ν-type (el-nu-coind): the invariant R (Ω-valued, two bound
    ||| variables), the proof that R holds at the equation's
    ||| endpoints, and the one-step closure — R implies the RELATOR
    ||| lift_𝔽(R) after one observation — each with its skeleton
    PNuCoind : Elem -> Skel -> Elem -> Skel -> Elem -> Skel -> Payload

  public export
  data Skel : Type where
    Nd : List Payload -> List Skel -> Skel

  ||| PROOF TERMS — the certificate of an equation Γ ⊦ l ≐ r : T
  ||| (docs/NovaKernelRewrite.txt: proofs are terms with proof leaves).
  ||| A proof is CHECKED against its goal: the sides are decomposed
  ||| along the proof's congruence nodes, each node one congruence rule
  ||| of the Foundation whose component types the node computes (from
  ||| the type flowing down, the inferred type of a neutral head, or a
  ||| carried motive), and the leaves justify the equation at their
  ||| position. Three readings of one proof:
  |||   ⇒ (synthesis)  a licence leaf, with selectors, symmetry and
  |||      transitivity over it, STATES its equation and type;
  |||   → (directional) given one side, the proof REWRITES it to the
  |||      other — this is how transitivity finds its middles: the
  |||      left proof run left-to-right, or the right one right-to-left;
  |||   ⇐ (checking)   given both sides, everything is verified — the
  |||      only reading the type-directed leaves (irrelevance, η,
  |||      quotient witnesses, propext) have.
  ||| Comparison is modulo β everywhere (the β join); δ happens only
  ||| where a δ leaf says so.
  public export
  data Prf : Type where
    -- ----- leaves that synthesise their equation -----
    ||| SELF: a variable or a signature reference as its own
    ||| reflexivity, at its DECLARED type — the base of a typed neutral
    ||| (a reference's spine is checked against its context; the
    ||| canonical closed forms Z, (), 𝟘, 𝟙, ℕ are included at theirs)
    PSelf : Elem -> Prf
    ||| CHECKED reflexivity: the term checked at the ascribed type with
    ||| its skeleton (an introduction form as a proof argument: a class,
    ||| a λ, a pair at the domain a lemma expects) — states t ≐ t : T
    PChk : Elem -> Ty -> Skel -> Prf
    ||| reflection: a proof STATED by a synthesising proof (a typed
    ||| spine over self leaves, ascribed where a shape hides) at an
    ||| equality prop l ≡ r ∈ A — the licensed equation l ≐ r : A
    PRefl : Prf -> Prf
    ||| el-qiit-path: an imposed equation of the carried signature at
    ||| entry k and argument spine θ — each entry a proof STATING the
    ||| element at the telescope's type
    PPath : QSig -> Nat -> List Prf -> Prf
    ||| x-δ: for the definition (Δ ⊦ x ≔ t : T), x[ē] ≐ t[ē] : T[ē],
    ||| each spine entry a proof stating the element at Δ's type. Run
    ||| left-to-right it is a plain unfolding of the occurrence x[ē']
    ||| (spines compared modulo β)
    PDelta : String -> List Prf -> Prf
    ||| a component of the equation below, by a selector
    PSel : Sel -> Prf -> Prf
    ||| the stated equation of π at type T′, by πᵀ ▷ A ≐ T′ at 𝕍 — the
    ||| ASCRIPTION (π : T′ by πᵀ): a conversion of a stated equation
    ||| (the positional match at a type spelled otherwise; a hidden Π
    ||| at a spine's head; a hidden ≡ at a proof's type)
    PAt : Prf -> Ty -> Prf -> Prf
    -- ----- structure -----
    ||| reflexivity: the sides join under β
    PReflx : Prf
    PSym : Prf -> Prf
    ||| transitivity with a COMPUTED middle: the left proof rewrites the
    ||| left side (or the right proof the right side, or a synthesising
    ||| child states it) — and the middle is β-joined before it passes
    ||| on
    PTrans : Prf -> Prf -> Prf
    ||| transitivity through a STATED middle (el-trans as written in a
    ||| chain, or a licence's raw side before its normalization)
    PTransAt : Prf -> Elem -> Prf -> Prf
    ||| conversion of the equation's type: a proof of T ≐ T' at 𝕍, the
    ||| type T', and the proof at T' (equal types have equal PERs)
    PConv : Prf -> Ty -> Prf -> Prf
    ||| every addressable occurrence of the named definitions unfolded
    ||| at once: the δ-round of a join. Left-to-right only (it is a
    ||| function of the term it acts on)
    PDeltaAll : List String -> Prf
    -- ----- type-directed leaves (checking only) -----
    ||| el-one-prop/el-zero-prop/el-prf-prop: the type is 𝟙, 𝟘 or a
    ||| proposition — with the type's skeleton, for a neutral prop's
    ||| judgemental question (it infers at Ω)
    PIrrel : Skel -> Prf
    ||| el-pi-eta: the proof compares the sides applied to the fresh
    ||| variable, under the domain
    PEtaPi : Prf -> Prf
    ||| el-sigma-eta: the proofs compare the projections
    PEtaSigma : Prf -> Prf -> Prf
    ||| el-quot-eq via the relation's SHAPE: R[id,a,b] ⇝ ∥T∥ with T ⇝ 𝟙
    ||| (no proof) or T ⇝ an ≡-type whose equation the proof establishes
    PQuotWit : Maybe Prf -> Prf
    ||| el-quot-eq with the witness SUPPLIED: a proof of R[id,a,b]
    ||| checked with its skeleton — the faithful route at an arbitrary
    ||| Ω-valued relation
    PQuotWitPrf : Elem -> Skel -> Prf
    ||| same-tag injections are equal when their payloads are; the
    ||| proof is at the branch type
    PInj : Prf -> Prf
    ||| code-prop-eq (propositional extensionality) at Ω: the two
    ||| implications as FUNCTIONS over Γ, with their skeletons
    PPropExt : Elem -> Skel -> Elem -> Skel -> Prf
    ||| prop-lift-eq for a TYPE equation: both sides are props (checked
    ||| — the side condition is load-bearing) and the proof equates
    ||| them at Ω
    PPrfCong : Skel -> Skel -> Prf -> Prf
    -- ----- congruences: one node per former, a proof per child -----
    -- Eliminators carry their motive when the constant-motive reading
    -- (the case positions at the node's own type) does not apply;
    -- Nothing = the constant reading. Carried heads (a signature
    -- variable's name, a QIIT signature, a polynomial) must match the
    -- sides'.
    CZeroElim : Prf -> Prf
    CNatIntro1 : Prf -> Prf
    CNatElim : Maybe Ty -> Prf -> Prf -> Prf -> Prf
    CPiIntro : Prf -> Prf
    CPiApp : Prf -> Prf -> Prf
    CSigmaIntro : Prf -> Prf -> Prf
    CSigmaElim1 : Prf -> Prf
    CSigmaElim2 : Prf -> Prf
    CInj1 : Prf -> Prf
    CInj2 : Prf -> Prf
    CSumElim : Maybe Ty -> Prf -> Prf -> Prf -> Prf
    CPiTy : Prf -> Prf -> Prf
    CSigmaTy : Prf -> Prf -> Prf
    CSumTy : Prf -> Prf -> Prf
    CEqTy : Prf -> Prf -> Prf -> Prf
    CQuotTy : Prf -> Prf -> Prf
    CSigVar : String -> List Prf -> Prf
    CClass : Prf -> Prf
    CQuotElim : Maybe Ty -> Prf -> Prf -> Prf
    CSquash : Prf -> Prf
    CQSort : QSig -> Nat -> List Prf -> Prf
    CQCtor : QSig -> Nat -> List Prf -> Prf
    ||| the QIIT eliminator: an optional motive list (Nothing: the
    ||| method positions are undetermined), a proof per METHOD, per
    ||| index-spine entry, and for the eliminee
    CQElim : QSig -> Nat -> Maybe (List Ty) -> List Prf -> List Prf -> Prf -> Prf
    COut : Prf -> Prf
    CCorec : Poly -> Prf -> Prf -> Prf -> Prf

||| Smart transitivity/symmetry: reflexivity is the unit.
public export
pTrans : Prf -> Prf -> Prf
pTrans PReflx q = q
pTrans p PReflx = p
pTrans p q = PTrans p q

public export
pSym : Prf -> Prf
pSym PReflx = PReflx
pSym (PSym p) = p
pSym p = PSym p

||| Substitution on a proof: acts on every element the proof carries
||| (proof elements, spines, stated middles, converted types, motives),
||| under the binders the congruence nodes cross.
public export
covering
substPrf : Prf -> Sub -> Prf
substPrf (PSelf t) s = PSelf (substElem t s)
substPrf (PChk t ty sk) s = PChk (substElem t s) (substTy ty s) sk
substPrf (PRefl p) s = PRefl (substPrf p s)
substPrf (PPath sg k th) s = PPath (substQSig sg s) k (map (\q => substPrf q s) th)
substPrf (PDelta x es) s = PDelta x (map (\q => substPrf q s) es)
substPrf (PAt q ty pt) s = PAt (substPrf q s) (substTy ty s) (substPrf pt s)
substPrf (PSel sel p) s = PSel (substSel sel) (substPrf p s)
 where
  substSel : Sel -> Sel
  substSel (SelCod u) = SelCod (substPrf u s)
  substSel (SelQRel u v) = SelQRel (substPrf u s) (substPrf v s)
  substSel x = x
substPrf PReflx s = PReflx
substPrf (PSym p) s = PSym (substPrf p s)
substPrf (PTrans p q) s = PTrans (substPrf p s) (substPrf q s)
substPrf (PTransAt p m q) s = PTransAt (substPrf p s) (substElem m s) (substPrf q s)
substPrf (PConv pt ty p) s = PConv (substPrf pt s) (substTy ty s) (substPrf p s)
substPrf (PDeltaAll ns) s = PDeltaAll ns
substPrf (PIrrel sk) s = PIrrel sk
substPrf (PEtaPi p) s = PEtaPi (substPrf p (under s))
substPrf (PEtaSigma p q) s = PEtaSigma (substPrf p s) (substPrf q s)
substPrf (PQuotWit mp) s = PQuotWit (map (\p => substPrf p s) mp)
substPrf (PQuotWitPrf w sk) s = PQuotWitPrf (substElem w s) sk
substPrf (PInj p) s = PInj (substPrf p s)
substPrf (PPropExt f fs g gs) s = PPropExt (substElem f s) fs (substElem g s) gs
substPrf (PPrfCong skl skr p) s = PPrfCong skl skr (substPrf p s)
substPrf (CZeroElim p) s = CZeroElim (substPrf p s)
substPrf (CNatIntro1 p) s = CNatIntro1 (substPrf p s)
substPrf (CNatElim m z st n) s =
  CNatElim (map (\t => substTy t (under s)) m) (substPrf z s) (substPrf st (under (under s))) (substPrf n s)
substPrf (CPiIntro p) s = CPiIntro (substPrf p (under s))
substPrf (CPiApp f a) s = CPiApp (substPrf f s) (substPrf a s)
substPrf (CSigmaIntro u v) s = CSigmaIntro (substPrf u s) (substPrf v s)
substPrf (CSigmaElim1 p) s = CSigmaElim1 (substPrf p s)
substPrf (CSigmaElim2 p) s = CSigmaElim2 (substPrf p s)
substPrf (CInj1 p) s = CInj1 (substPrf p s)
substPrf (CInj2 p) s = CInj2 (substPrf p s)
substPrf (CSumElim m l r t) s =
  CSumElim (map (\x => substTy x (under s)) m) (substPrf l (under s)) (substPrf r (under s)) (substPrf t s)
substPrf (CPiTy a b) s = CPiTy (substPrf a s) (substPrf b (under s))
substPrf (CSigmaTy a b) s = CSigmaTy (substPrf a s) (substPrf b (under s))
substPrf (CSumTy a b) s = CSumTy (substPrf a s) (substPrf b s)
substPrf (CEqTy l r t) s = CEqTy (substPrf l s) (substPrf r s) (substPrf t s)
substPrf (CQuotTy a r) s = CQuotTy (substPrf a s) (substPrf r (under (under s)))
substPrf (CSigVar x ps) s = CSigVar x (map (\p => substPrf p s) ps)
substPrf (CClass p) s = CClass (substPrf p s)
substPrf (CQuotElim m f q) s =
  CQuotElim (map (\x => substTy x (under s)) m) (substPrf f (under s)) (substPrf q s)
substPrf (CSquash p) s = CSquash (substPrf p s)
substPrf (CQSort sg k ps) s = CQSort (substQSig sg s) k (map (\p => substPrf p s) ps)
substPrf (CQCtor sg k ps) s = CQCtor (substQSig sg s) k (map (\p => substPrf p s) ps)
substPrf (CQElim sg k ms qs ps w) s =
  CQElim (substQSig sg s) k (map (map (\m => substTy m s)) ms)
         (map (\p => substPrf p s) qs) (map (\p => substPrf p s) ps) (substPrf w s)
substPrf (COut p) s = COut (substPrf p s)
substPrf (CCorec pf a f x) s = CCorec (substPoly pf s) (substPrf a s) (substPrf f (under s)) (substPrf x s)

covering
motive : Maybe Ty -> String
motive Nothing = ""
motive (Just m) = "{\{show m}}"

-- Proofs print in the CORE'S OWN SYNTAX: a congruence node prints as
-- the former it is the congruence of (α β for an application, α .π₂
-- for a projection, λ α, (α, β), inj₁ α, class α, α → β, …), the
-- leaves in brackets. A term-shaped proof reads like the term it
-- proves something about.
atomicPrf : Prf -> Bool
atomicPrf (PSelf _) = True
atomicPrf (PChk _ _ _) = True
atomicPrf (PRefl _) = True
atomicPrf PReflx = True
atomicPrf (PDeltaAll _) = True
atomicPrf (PIrrel _) = True
atomicPrf (PSym _) = True
atomicPrf (PSel _ _) = True
atomicPrf (PAt _ _ _) = True
atomicPrf (PConv _ _ _) = True
atomicPrf (PTransAt _ _ _) = True
atomicPrf (CSigmaElim1 _) = True
atomicPrf (CSigmaElim2 _) = True
atomicPrf (CSigmaIntro _ _) = True
atomicPrf (CSigVar _ _) = True
atomicPrf (CQSort _ _ _) = True
atomicPrf (CQCtor _ _ _) = True
atomicPrf (CSquash _) = True
atomicPrf (PEtaPi _) = True
atomicPrf (PEtaSigma _ _) = True
atomicPrf (PQuotWit _) = True
atomicPrf (PQuotWitPrf _ _) = True
atomicPrf (PInj _) = True
atomicPrf (PPropExt _ _ _ _) = True
atomicPrf (PPrfCong _ _ _) = True
atomicPrf _ = False

motiveP : Maybe Ty -> String
motiveP Nothing = ""
motiveP (Just m) = "{\{show m}}"

mutual
  ||| an argument position: atoms bare, anything else parenthesised
  covering
  argP : Prf -> String
  argP p = if atomicPrf p then showPrf p else "(" ++ showPrf p ++ ")"

  ||| a head position (the function of an application): applications
  ||| chain to the left without parentheses
  covering
  hdP : Prf -> String
  hdP p@(CPiApp _ _) = showPrf p
  hdP p = argP p

  covering
  argsP : List Prf -> String
  argsP ps = concat (intersperse ", " (map showPrf ps))

  covering
  showSel : Sel -> String
  showSel SelSuc = "suc"
  showSel SelDom = "dom"
  showSel (SelCod u) = "cod(\{showPrf u})"
  showSel SelSumL = "inl"
  showSel SelSumR = "inr"
  showSel SelQDom = "qdom"
  showSel (SelQRel u v) = "qrel(\{showPrf u},\{showPrf v})"
  showSel (SelQIdx i) = "idx\{show i}"

  export
  covering
  showPrf : Prf -> String
  -- leaves
  showPrf (PSelf t) = "[\{show t}]"
  showPrf (PChk t ty _) = "[\{show t} : \{show ty}]"
  showPrf (PRefl p) = "⟨\{showPrf p}⟩"
  showPrf (PPath _ k th) = "path \{show k} [\{argsP th}]"
  showPrf (PDelta x es) = "\{x}-δ [\{argsP es}]"
  showPrf (PDeltaAll ns) = "δ-all \{show ns}"
  showPrf PReflx = "refl"
  showPrf (PIrrel _) = "irrel"
  -- structure
  showPrf (PSel sel p) = "\{showSel sel}(\{showPrf p})"
  showPrf (PSym p) = "\{argP p}⁻¹"
  showPrf (PTrans p q) = "\{showPrf p} ; \{showPrf q}"
  showPrf (PTransAt p m q) = "(\{showPrf p} ; [\{show m}] ; \{showPrf q})"
  showPrf (PAt q ty pt) = "(\{showPrf q} : \{show ty} by \{showPrf pt})"
  showPrf (PConv pt ty p) = "(\{showPrf p} ∷ \{show ty} by \{showPrf pt})"
  -- type-directed leaves
  showPrf (PEtaPi p) = "η→(\{showPrf p})"
  showPrf (PEtaSigma p q) = "η×(\{showPrf p}, \{showPrf q})"
  showPrf (PQuotWit mp) = "quot-wit(\{maybe "" showPrf mp})"
  showPrf (PQuotWitPrf w _) = "quot-wit[\{show w}]"
  showPrf (PInj p) = "inj(\{showPrf p})"
  showPrf (PPropExt f _ g _) = "propext[\{show f}, \{show g}]"
  showPrf (PPrfCong _ _ p) = "prop-lift(\{showPrf p})"
  -- congruences, in the core's syntax
  showPrf (CZeroElim p) = "𝟘-elim \{argP p}"
  showPrf (CNatIntro1 p) = "S \{argP p}"
  showPrf (CNatElim m z st n) = "ℕ-elim\{motiveP m} \{argP z} \{argP st} \{argP n}"
  showPrf (CPiIntro p) = "λ \{showPrf p}"
  showPrf (CPiApp f a) = "\{hdP f} \{argP a}"
  showPrf (CSigmaIntro u v) = "(\{showPrf u}, \{showPrf v})"
  showPrf (CSigmaElim1 p) = "\{argP p} .π₁"
  showPrf (CSigmaElim2 p) = "\{argP p} .π₂"
  showPrf (CInj1 p) = "inj₁ \{argP p}"
  showPrf (CInj2 p) = "inj₂ \{argP p}"
  showPrf (CSumElim m l r t) = "⊎-elim\{motiveP m} \{argP l} \{argP r} \{argP t}"
  showPrf (CPiTy a b) = "\{argP a} → \{argP b}"
  showPrf (CSigmaTy a b) = "\{argP a} × \{argP b}"
  showPrf (CSumTy a b) = "\{argP a} ⊎ \{argP b}"
  showPrf (CEqTy l r t) = "\{argP l} ≡ \{argP r} ∈ \{argP t}"
  showPrf (CQuotTy a r) = "\{argP a} / \{argP r}"
  showPrf (CSigVar x ps) = "\{x}[\{argsP ps}]"
  showPrf (CClass p) = "class \{argP p}"
  showPrf (CQuotElim m f q) = "quot-elim\{motiveP m} \{argP f} \{argP q}"
  showPrf (CSquash p) = "∥\{showPrf p}∥"
  showPrf (CQSort _ k ps) = "𝒮.\{show k}[\{argsP ps}]"
  showPrf (CQCtor _ k ps) = "𝒮.\{show k}[\{argsP ps}]"
  showPrf (CQElim _ k m qs ps w) = "𝒮.\{show k}-elim\{if isJust m then "{…}" else ""} [\{argsP qs}] [\{argsP ps}] \{argP w}"
  showPrf (COut p) = "out \{argP p}"
  showPrf (CCorec _ a f x) = "corec \{argP a} \{argP f} \{argP x}"

export
covering
Show Prf where
  show = showPrf

export
covering
Show Sel where
  show = showSel

public export
KErr : Type
KErr = String

||| The kernel's own state: the fuel budget, and the normal forms it
||| has computed for signature definitions during THIS check.
|||
||| The memo is the kernel's own work, never anything handed to it —
||| NovaPipeline's trust boundary forbids believing a normal form
||| computed above the kernel, so this cannot be shared with the
||| elaborator's normaliser. It lives for one runKM call, which is where
||| the repetition is: a term mentions its dependencies many times over.
record KSt where
  constructor MkKSt
  fuel : Nat
  nfE : SortedMap String Elem
  ||| name → entry, built lazily during THIS check: Σ is fixed for the
  ||| lifetime of one runKM call, so a positive hit is stable, and the
  ||| linear sigLookup scan — measured at ~40% of all execution on the
  ||| hot paths — is paid once per name instead of once per mention.
  ||| Same per-call discipline as the nf memo above.
  sigIx : SortedMap String SigEntry
  ||| LIBERAL whnf: definitions unfold on the kernel's own initiative.
  ||| Never set on a verdict path — only by the engine-facing services
  ||| (kInferBare: typing a hole's value, where no skeleton exists)
  liberal : Bool

export
data KM : Type -> Type where
  MkKM : (KSt -> Either KErr (a, KSt)) -> KM a

runKMSt : KM a -> KSt -> Either KErr (a, KSt)
runKMSt (MkKM f) = f

export
runKM : KM a -> Nat -> Either KErr (a, Nat)
runKM m n = map (mapSnd fuel) (runKMSt m (MkKSt n empty empty False))

||| The engine-facing variant: whnf unfolds definitions freely.
runKMLiberal : KM a -> Nat -> Either KErr (a, Nat)
runKMLiberal m n = map (mapSnd fuel) (runKMSt m (MkKSt n empty empty True))

kLiberal : KM Bool
kLiberal = MkKM $ \st => Right (st.liberal, st)

||| Run a computation with liberal whnf (definitions unfold at the
||| head), restoring the flag after.
withLiberal : KM a -> KM a
withLiberal (MkKM f) = MkKM $ \st =>
  case f ({ liberal := True } st) of
    Left e => Left e
    Right (v, st') => Right (v, { liberal := st.liberal } st')

export
Functor KM where
  map f (MkKM g) = MkKM $ \n => map (mapFst f) (g n)

export
Applicative KM where
  pure x = MkKM $ \n => Right (x, n)
  (MkKM f) <*> (MkKM g) = MkKM $ \n => do
    (h, n') <- f n
    (x, n'') <- g n'
    Right (h x, n'')

export
Monad KM where
  (MkKM f) >>= k = MkKM $ \n => do
    (x, n') <- f n
    runKMSt (k x) n'

export
kerr : KErr -> KM a
kerr e = MkKM $ \_ => Left e

||| Run a sub-check, converting failure into False (state as of the
||| failure is discarded; success keeps the fuel spent).
||| The first computation, or — when it fails — the second (the
||| first's fuel is spent either way).
export
kOrElse : KM a -> KM a -> KM a
kOrElse (MkKM f) (MkKM g) = MkKM $ \st => case f st of
  Right v => Right v
  Left _ => g st

kTry : KM () -> KM Bool
kTry (MkKM f) = MkKM $ \st => case f st of
  Left _ => Right (False, st)
  Right ((), st') => Right (True, st')

||| One ≜-contraction's worth of fuel.
burn : KM ()
burn = MkKM $ \st => case st.fuel of
  Z => Left "kernel: out of fuel"
  S m => Right ((), { fuel := m } st)

kNfElemGet : String -> KM (Maybe Elem)
kNfElemGet x = MkKM $ \st => Right (lookup x st.nfE, st)

kNfElemPut : String -> Elem -> KM Elem
kNfElemPut x v = MkKM $ \st => Right (v, { nfE $= insert x v } st)

export
||| Name-indexed signature lookup (see KSt.sigIx). Negatives are never
||| cached — they cost one scan and stay correct by construction.
kSigLookup : Sig -> SigIdentifier -> KM (Maybe SigEntry)
kSigLookup sig x = MkKM $ \st =>
  case lookup x st.sigIx of
    Just e => Right (Just e, st)
    Nothing =>
      case sigLookup x sig of
        Just e => Right (Just e, { sigIx $= insert x e } st)
        Nothing => Right (Nothing, st)

-- ===== Fuel-bounded normalization (Foundation's ≜, clause for clause) =====

mutual
  kSubNorm : Sig -> SubNorm -> KM SubNorm
  kSubNorm sig [<] = pure [<]
  kSubNorm sig (es :< e) = [| kSubNorm sig es :< kElem sig e |]

  ||| Beta-normal form of an element, spending one fuel per contraction.
  export
  kElem : Sig -> Elem -> KM Elem
  kElem sig (CtxVar n) = pure (CtxVar n)
  kElem sig (ZeroElim t) = ZeroElim <$> kElem sig t
  kElem sig OneIntro = pure OneIntro
  kElem sig NatIntro0 = pure NatIntro0
  kElem sig (NatIntro1 t) = NatIntro1 <$> kElem sig t
  kElem sig (NatElim z s t) = do
    z' <- kElem sig z
    s' <- kElem sig s
    t' <- kElem sig t
    case t' of
      NatIntro0 => pure z'
      NatIntro1 n => do burn; kElem sig (substElem s' (Ext (Ext Id n) (NatElim z' s' n)))
      _ => pure (NatElim z' s' t')
  kElem sig (PiIntro f) = PiIntro <$> kElem sig f
  kElem sig (PiApp f e) = do
    e' <- kElem sig e
    f' <- kElem sig f
    case f' of
      PiIntro g => do burn; kElem sig (substElem g (Ext Id e'))
      _ => pure (PiApp f' e')
  -- el-let-beta: a let is ALWAYS a redex — let a b ≜ b[id, a, ⋆]
  -- (normal forms contain no let; one fuel unit, like every contraction)
  kElem sig (Let a b) = do
    burn
    kElem sig (substElem b (Ext (Ext Id a) Star))
  kElem sig (SigmaIntro a b) = [| SigmaIntro (kElem sig a) (kElem sig b) |]
  kElem sig (SigmaElim1 t) = do
    t' <- kElem sig t
    case t' of
      SigmaIntro a _ => do burn; pure a
      _ => pure (SigmaElim1 t')
  kElem sig (SigmaElim2 t) = do
    t' <- kElem sig t
    case t' of
      SigmaIntro _ b => do burn; pure b
      _ => pure (SigmaElim2 t')
  kElem sig (Inj1 t) = Inj1 <$> kElem sig t
  kElem sig (Inj2 t) = Inj2 <$> kElem sig t
  kElem sig (SumElim l r t) = do
    l' <- kElem sig l
    r' <- kElem sig r
    t' <- kElem sig t
    case t' of
      Inj1 a => do burn; kElem sig (substElem l' (Ext Id a))
      Inj2 b => do burn; kElem sig (substElem r' (Ext Id b))
      _ => pure (SumElim l' r' t')
  kElem sig Elem.ZeroTy = pure Elem.ZeroTy
  kElem sig Elem.OneTy = pure Elem.OneTy
  kElem sig Elem.NatTy = pure Elem.NatTy
  kElem sig UniverseTy = pure UniverseTy
  kElem sig PropTy = pure PropTy
  kElem sig TopTy = pure TopTy
  kElem sig (Elem.PiTy a b) = [| Elem.PiTy (kElem sig a) (kElem sig b) |]
  kElem sig (Elem.SigmaTy a b) = [| Elem.SigmaTy (kElem sig a) (kElem sig b) |]
  kElem sig (Elem.SumTy a b) = [| Elem.SumTy (kElem sig a) (kElem sig b) |]
  kElem sig (Elem.EqTy l r t) = [| Elem.EqTy (kElem sig l) (kElem sig r) (kTy sig t) |]
  kElem sig (QuotTy a r) = [| QuotTy (kElem sig a) (kElem sig r) |]
  kElem sig (SigVar x es) = do
    es' <- kSubNorm sig es
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef _ _ a _) => do
        burn
        -- nf(body) is recomputed on every mention otherwise; at a
        -- top-level item es' is empty and the substitution is the
        -- identity, so the cached form IS the answer
        cached <- kNfElemGet x
        nfa <- case cached of
                 Just v => pure v
                 Nothing => do v <- kElem sig a; kNfElemPut x v
        case es' of
          [<] => pure nfa
          _   => kElem sig (substElem nfa (embed es'))
      -- el-sig-decl: a declaration reference is stuck (no -beta)
      Just (SigDecl _ _ _) => pure (SigVar x es')
      Just _ => kerr "kernel: signature name '\{x}' names a constraint entry"
      Nothing => kerr "kernel: unknown signature name '\{x}'"
  kElem sig (Class a) = Class <$> kElem sig a
  kElem sig (QuotElim f q) = do
    q' <- kElem sig q
    f' <- kElem sig f
    case q' of
      Class a => do burn; kElem sig (substElem f' (Ext Id a))
      _ => pure (QuotElim f' q')
  kElem sig (Squash t) = do
    t' <- kTy sig t
    case t' of
      -- code-squash-idem, syntax-directed instances (≡-/∥·∥-headed
      -- types ARE props; Ω-neutrals stay stuck)
      p@(Elem.EqTy _ _ _) => do burn; pure p
      p@(Squash _) => do burn; pure p
      _ => pure (Squash t')
  kElem sig Star = pure Star
  kElem sig (QSort sg k es) = [| QSort (kQSig sig sg) (pure k) (kSubNorm sig es) |]
  kElem sig (QCtor sg k es) = [| QCtor (kQSig sig sg) (pure k) (kSubNorm sig es) |]
  kElem sig (QElim sg k fs es w) = do
    sg' <- kQSig sig sg
    fs' <- traverse (kElem sig) fs
    es' <- kSubNorm sig es
    w' <- kElem sig w
    case w' of
      -- el-qiit-beta: fires only when the carried signatures are
      -- IDENTICAL after normalization (structural identity, nameless)
      QCtor sgW c theta =>
        if sgW == sg'
          then do burn
                  case qElimBetaRhs sg' fs' c theta of
                    Right rhs => kElem sig rhs
                    Left err => kerr "kernel: \{err}"
          else pure (QElim sg' k fs' es' w')
      _ => pure (QElim sg' k fs' es' w')
  kElem sig (Elem.NuTy f) = [| Elem.NuTy (kPoly sig f) |]
  kElem sig (Out t) = do
    t' <- kElem sig t
    case t' of
      -- el-nu-beta: run the coalgebra one step, re-wrap the recursive
      -- positions (map_𝔽 hᵉˡ f[id, x])
      Corec p a f x => do burn
                          kElem sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      _ => pure (Out t')
  kElem sig (Corec p a f x) =
    [| Corec (kPoly sig p) (kElem sig a) (kElem sig f) (kElem sig x) |]

  kPoly : Sig -> Poly -> KM Poly
  kPoly sig PHole        = pure PHole
  kPoly sig (PConst a)   = [| PConst (kElem sig a) |]
  kPoly sig (PProd f g)  = [| PProd (kPoly sig f) (kPoly sig g) |]
  kPoly sig (PSum f g)   = [| PSum (kPoly sig f) (kPoly sig g) |]
  kPoly sig (PSigma a f) = [| PSigma (kElem sig a) (kPoly sig f) |]
  kPoly sig (PPi a f)    = [| PPi (kElem sig a) (kPoly sig f) |]

  kQTm : Sig -> QTm -> KM QTm
  kQTm sig (QVar i) = pure (QVar i)
  kQTm sig (QAppE f e) = [| QAppE (kQTm sig f) (kElem sig e) |]
  kQTm sig (QAppI f a) = [| QAppI (kQTm sig f) (kQTm sig a) |]
  kQTm sig (QEqC l r u) = [| QEqC (kQTm sig l) (kQTm sig r) (kQTm sig u) |]

  kQTy : Sig -> QTy -> KM QTy
  kQTy sig QU = pure QU
  kQTy sig (QEl t) = QEl <$> kQTm sig t
  kQTy sig (QPiExt a b) = [| QPiExt (kTy sig a) (kQTy sig b) |]
  kQTy sig (QPiInd u b) = [| QPiInd (kQTm sig u) (kQTy sig b) |]

  export
  kQSig : Sig -> QSig -> KM QSig
  kQSig sig = traverse (kQTy sig)

  ||| Beta-normal form of a type — one sort: types are terms, one
  ||| normalizer (El-decoding lives in kElem's El clause; signature
  ||| unfolding is el-sig-beta uniformly, type entries included).
  export
  kTy : Sig -> Ty -> KM Ty
  kTy = kElem

-- ===== The β join =====
--
-- The replay normalizer: α + every computation rule (β, ι, let,
-- ν-β, QIIT-β, code-squash-idem's instances) and NO δ. A definition
-- reference is STUCK here, like a declaration's: definitions unfold
-- during replay only through an explicit LUnfold step
-- (docs/NovaKernelRewrite.txt, CONVENTIONS — the kernel never
-- unfolds on its own initiative inside an equation, so the producer
-- never has to predict a strategy and its every δ is recorded).
-- Head matches at intro forms and licence types still use kWhnf*,
-- which unfolds freely: that is shape EXPOSURE, the next step of the
-- migration (ascription + certificate), not equation replay.

mutual
  ||| Weak-head normalization WITH δ: contract only at the head, one
  ||| fuel per contraction, subterms stay as written. Stuck or unknown
  ||| heads return unchanged — exposure never errors.
  kWhnfE : Sig -> Elem -> KM Elem
  kWhnfE sig (NatElim z s t) = do
    t' <- kWhnfE sig t
    case t' of
      NatIntro0 => do burn; kWhnfE sig z
      NatIntro1 n => do burn; kWhnfE sig (substElem s (Ext (Ext Id n) (NatElim z s n)))
      _ => pure (NatElim z s t')
  kWhnfE sig (PiApp f e) = do
    f' <- kWhnfE sig f
    case f' of
      PiIntro g => do burn; kWhnfE sig (substElem g (Ext Id e))
      _ => pure (PiApp f' e)
  kWhnfE sig (Let a b) = do burn; kWhnfE sig (substElem b (Ext (Ext Id a) Star))
  kWhnfE sig (SigmaElim1 t) = do
    t' <- kWhnfE sig t
    case t' of
      SigmaIntro a _ => do burn; kWhnfE sig a
      _ => pure (SigmaElim1 t')
  kWhnfE sig (SigmaElim2 t) = do
    t' <- kWhnfE sig t
    case t' of
      SigmaIntro _ b => do burn; kWhnfE sig b
      _ => pure (SigmaElim2 t')
  kWhnfE sig (SumElim l r t) = do
    t' <- kWhnfE sig t
    case t' of
      Inj1 a => do burn; kWhnfE sig (substElem l (Ext Id a))
      Inj2 b => do burn; kWhnfE sig (substElem r (Ext Id b))
      _ => pure (SumElim l r t')
  -- β-only: a definition reference is STUCK. Every shape a definition
  -- hides is exposed by a recorded conversion (PExpose / PScrut at
  -- the item level, PConv / an ascribed leaf inside a proof), never
  -- by the kernel's own unfolding — except under the engine-facing
  -- LIBERAL flag (kInferBare)
  kWhnfE sig (SigVar x es) = do
    lib <- kLiberal
    if lib
      then kSigLookup sig x >>= \entryX => case entryX of
             Just (SigDef _ _ a _) => do burn; kWhnfE sig (substElem a (embed es))
             _ => pure (SigVar x es)
      else pure (SigVar x es)
  kWhnfE sig (QuotElim f q) = do
    q' <- kWhnfE sig q
    case q' of
      Class a => do burn; kWhnfE sig (substElem f (Ext Id a))
      _ => pure (QuotElim f q')
  -- code-squash-idem's instances collapse a squash whose squashee
  -- exposes to a prop; otherwise the squashee stays AS WRITTEN — the
  -- head is Squash already, and exposing what it wraps would hand
  -- sub-checks a spelling their certificates were not made against
  kWhnfE sig (Squash t) = do
    t' <- kWhnfT sig t
    case t' of
      p@(Elem.EqTy _ _ _) => do burn; pure p
      p@(Squash _) => do burn; pure p
      _ => pure (Squash t)
  kWhnfE sig (QElim sg k fs es w) = do
    w' <- kWhnfE sig w
    case w' of
      QCtor sgW c theta =>
        if sgW == sg
          then do burn
                  case qElimBetaRhs sg fs c theta of
                    Right rhs => kWhnfE sig rhs
                    Left _ => pure (QElim sg k fs es (QCtor sgW c theta))
          else pure (QElim sg k fs es (QCtor sgW c theta))
      _ => pure (QElim sg k fs es w')
  kWhnfE sig (Out t) = do
    t' <- kWhnfE sig t
    case t' of
      Corec p a f x => do burn; kWhnfE sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      _ => pure (Out t')
  kWhnfE sig e = pure e

  ||| One sort: one weak-head normalizer.
  export
  kWhnfT : Sig -> Ty -> KM Ty
  kWhnfT = kWhnfE

mutual
  export
  kJoinSubNorm : Sig -> SubNorm -> KM SubNorm
  kJoinSubNorm sig [<] = pure [<]
  kJoinSubNorm sig (es :< e) = [| kJoinSubNorm sig es :< kJoinElem sig e |]

  export
  ||| The β-join normal form: every computation rule, no δ.
  kJoinElem : Sig -> Elem -> KM Elem
  kJoinElem sig (CtxVar n) = pure (CtxVar n)
  kJoinElem sig (ZeroElim t) = ZeroElim <$> kJoinElem sig t
  kJoinElem sig OneIntro = pure OneIntro
  kJoinElem sig NatIntro0 = pure NatIntro0
  kJoinElem sig (NatIntro1 t) = NatIntro1 <$> kJoinElem sig t
  kJoinElem sig (NatElim z s t) = do
    z' <- kJoinElem sig z
    s' <- kJoinElem sig s
    t' <- kJoinElem sig t
    case t' of
      NatIntro0 => do burn; pure z'
      NatIntro1 n => do burn; kJoinElem sig (substElem s' (Ext (Ext Id n) (NatElim z' s' n)))
      _ => pure (NatElim z' s' t')
  kJoinElem sig (PiIntro f) = PiIntro <$> kJoinElem sig f
  kJoinElem sig (PiApp f e) = do
    e' <- kJoinElem sig e
    f' <- kJoinElem sig f
    case f' of
      PiIntro g => do burn; kJoinElem sig (substElem g (Ext Id e'))
      _ => pure (PiApp f' e')
  kJoinElem sig (Let a b) = do
    burn
    kJoinElem sig (substElem b (Ext (Ext Id a) Star))
  kJoinElem sig (SigmaIntro a b) = [| SigmaIntro (kJoinElem sig a) (kJoinElem sig b) |]
  kJoinElem sig (SigmaElim1 t) = do
    t' <- kJoinElem sig t
    case t' of
      SigmaIntro a _ => do burn; pure a
      _ => pure (SigmaElim1 t')
  kJoinElem sig (SigmaElim2 t) = do
    t' <- kJoinElem sig t
    case t' of
      SigmaIntro _ b => do burn; pure b
      _ => pure (SigmaElim2 t')
  kJoinElem sig (Inj1 t) = Inj1 <$> kJoinElem sig t
  kJoinElem sig (Inj2 t) = Inj2 <$> kJoinElem sig t
  kJoinElem sig (SumElim l r t) = do
    l' <- kJoinElem sig l
    r' <- kJoinElem sig r
    t' <- kJoinElem sig t
    case t' of
      Inj1 a => do burn; kJoinElem sig (substElem l' (Ext Id a))
      Inj2 b => do burn; kJoinElem sig (substElem r' (Ext Id b))
      _ => pure (SumElim l' r' t')
  kJoinElem sig Elem.ZeroTy = pure Elem.ZeroTy
  kJoinElem sig Elem.OneTy = pure Elem.OneTy
  kJoinElem sig Elem.NatTy = pure Elem.NatTy
  kJoinElem sig UniverseTy = pure UniverseTy
  kJoinElem sig PropTy = pure PropTy
  kJoinElem sig TopTy = pure TopTy
  kJoinElem sig (Elem.PiTy a b) = [| Elem.PiTy (kJoinElem sig a) (kJoinElem sig b) |]
  kJoinElem sig (Elem.SigmaTy a b) = [| Elem.SigmaTy (kJoinElem sig a) (kJoinElem sig b) |]
  kJoinElem sig (Elem.SumTy a b) = [| Elem.SumTy (kJoinElem sig a) (kJoinElem sig b) |]
  kJoinElem sig (Elem.EqTy l r t) = [| Elem.EqTy (kJoinElem sig l) (kJoinElem sig r) (kJoinTy sig t) |]
  kJoinElem sig (QuotTy a r) = [| QuotTy (kJoinElem sig a) (kJoinElem sig r) |]
  -- x-β omitted: a definition reference is STUCK, whatever its
  -- classifier — δ is an LUnfold step
  kJoinElem sig (SigVar x es) = SigVar x <$> kJoinSubNorm sig es
  kJoinElem sig (Class a) = Class <$> kJoinElem sig a
  kJoinElem sig (QuotElim f q) = do
    q' <- kJoinElem sig q
    f' <- kJoinElem sig f
    case q' of
      Class a => do burn; kJoinElem sig (substElem f' (Ext Id a))
      _ => pure (QuotElim f' q')
  kJoinElem sig (Squash t) = do
    t' <- kJoinTy sig t
    case t' of
      p@(Elem.EqTy _ _ _) => do burn; pure p
      p@(Squash _) => do burn; pure p
      _ => pure (Squash t')
  kJoinElem sig Star = pure Star
  kJoinElem sig (QSort sg k es) = [| QSort (kJoinQSig sig sg) (pure k) (kJoinSubNorm sig es) |]
  kJoinElem sig (QCtor sg k es) = [| QCtor (kJoinQSig sig sg) (pure k) (kJoinSubNorm sig es) |]
  kJoinElem sig (QElim sg k fs es w) = do
    sg' <- kJoinQSig sig sg
    fs' <- traverse (kJoinElem sig) fs
    es' <- kJoinSubNorm sig es
    w' <- kJoinElem sig w
    case w' of
      QCtor sgW c theta =>
        if sgW == sg'
          then do burn
                  case qElimBetaRhs sg' fs' c theta of
                    Right rhs => kJoinElem sig rhs
                    Left err => kerr "kernel: \{err}"
          else pure (QElim sg' k fs' es' w')
      _ => pure (QElim sg' k fs' es' w')
  kJoinElem sig (Elem.NuTy f) = Elem.NuTy <$> kJoinPoly sig f
  kJoinElem sig (Out t) = do
    t' <- kJoinElem sig t
    case t' of
      Corec p a f x => do burn; kJoinElem sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      _ => pure (Out t')
  kJoinElem sig (Corec p a f x) =
    [| Corec (kJoinPoly sig p) (kJoinElem sig a) (kJoinElem sig f) (kJoinElem sig x) |]

  kJoinPoly : Sig -> Poly -> KM Poly
  kJoinPoly sig PHole = pure PHole
  kJoinPoly sig (PConst a) = [| PConst (kJoinElem sig a) |]
  kJoinPoly sig (PProd f g) = [| PProd (kJoinPoly sig f) (kJoinPoly sig g) |]
  kJoinPoly sig (PSum f g) = [| PSum (kJoinPoly sig f) (kJoinPoly sig g) |]
  kJoinPoly sig (PSigma a f) = [| PSigma (kJoinElem sig a) (kJoinPoly sig f) |]
  kJoinPoly sig (PPi a f) = [| PPi (kJoinElem sig a) (kJoinPoly sig f) |]

  kJoinQTm : Sig -> QTm -> KM QTm
  kJoinQTm sig (QVar i) = pure (QVar i)
  kJoinQTm sig (QAppE f e) = [| QAppE (kJoinQTm sig f) (kJoinElem sig e) |]
  kJoinQTm sig (QAppI f a) = [| QAppI (kJoinQTm sig f) (kJoinQTm sig a) |]
  kJoinQTm sig (QEqC l r t) = [| QEqC (kJoinQTm sig l) (kJoinQTm sig r) (kJoinQTm sig t) |]

  kJoinQTy : Sig -> QTy -> KM QTy
  kJoinQTy sig QU = pure QU
  kJoinQTy sig (QEl t) = QEl <$> kJoinQTm sig t
  kJoinQTy sig (QPiExt a b) = [| QPiExt (kJoinTy sig a) (kJoinQTy sig b) |]
  kJoinQTy sig (QPiInd t b) = [| QPiInd (kJoinQTm sig t) (kJoinQTy sig b) |]

  export
  kJoinQSig : Sig -> QSig -> KM QSig
  kJoinQSig sig = traverse (kJoinQTy sig)

  export
  ||| β-join normal form of a TYPE — one sort, one join.
  kJoinTy : Sig -> Ty -> KM Ty
  kJoinTy = kJoinElem

liftEither : Either KErr a -> KM a
liftEither (Left e) = kerr e
liftEither (Right x) = pure x

export
liftQ : Either QErr a -> KM a
liftQ (Left e) = kerr "kernel: \{e}"
liftQ (Right x) = pure x

-- ===== Context lookup =====

ctxLookup : Ctx -> Nat -> Maybe Ty
ctxLookup [<] _ = Nothing
ctxLookup (rest :< ty) Z = Just (substTy ty Wk)
ctxLookup (rest :< ty) (S n) = map (\t => substTy t Wk) (ctxLookup rest n)

-- ===== Proof readings (static) =====
--
-- Which readings a proof supports is a property of its SHAPE, decided
-- before any replay: the checker never guesses a direction.

||| The children of a congruence node (Nothing at a leaf or a
||| structural form).
congChildren : Prf -> Maybe (List Prf)
congChildren (CZeroElim p) = Just [p]
congChildren (CNatIntro1 p) = Just [p]
congChildren (CNatElim _ z s n) = Just [z, s, n]
congChildren (CPiIntro p) = Just [p]
congChildren (CPiApp f a) = Just [f, a]
congChildren (CSigmaIntro u v) = Just [u, v]
congChildren (CSigmaElim1 p) = Just [p]
congChildren (CSigmaElim2 p) = Just [p]
congChildren (CInj1 p) = Just [p]
congChildren (CInj2 p) = Just [p]
congChildren (CSumElim _ l r t) = Just [l, r, t]
congChildren (CPiTy a b) = Just [a, b]
congChildren (CSigmaTy a b) = Just [a, b]
congChildren (CSumTy a b) = Just [a, b]
congChildren (CEqTy l r t) = Just [l, r, t]
congChildren (CQuotTy a r) = Just [a, r]
congChildren (CSigVar _ ps) = Just ps
congChildren (CClass p) = Just [p]
congChildren (CQuotElim _ f q) = Just [f, q]
congChildren (CSquash p) = Just [p]
congChildren (CQSort _ _ ps) = Just ps
congChildren (CQCtor _ _ ps) = Just ps
congChildren (CQElim _ _ _ qs ps w) = Just (qs ++ ps ++ [w])
congChildren (COut p) = Just [p]
congChildren (CCorec _ a f x) = Just [a, f, x]
congChildren _ = Nothing

mutual
  ||| ⇒: does the proof state its own equation (sides and type)?
  synthP : Prf -> Bool
  synthP (PSelf _) = True
  synthP (PChk _ _ _) = True
  synthP (PRefl p) = synthP p
  synthP (PPath _ _ _) = True
  synthP (PDelta _ _) = True
  synthP (PAt _ _ _) = True
  synthP (PSel _ p) = synthP p
  synthP (PSym p) = synthP p
  synthP (PTrans p q) = (synthP p && dirP True q) || (synthP q && dirP False p)
  -- a TYPED SPINE: elimination nodes state their equation when their
  -- head is a typed neutral (and, for an application, its argument
  -- states an equation)
  synthP (CPiApp f a) = typedP f && synthP a
  synthP (CSigmaElim1 p) = typedP p
  synthP (CSigmaElim2 p) = typedP p
  synthP (COut p) = typedP p
  synthP (CNatIntro1 p) = synthP p
  synthP _ = False

  ||| A TYPED NEUTRAL: a self or checked leaf, an ascription, or an
  ||| elimination over one — a proof whose stated type has the shape
  ||| the elimination above it needs, or is ascribed to it. (A δ leaf
  ||| or a reflection also states an equation, but at a type nothing
  ||| has exposed: a spine over one is read by decomposition.)
  typedP : Prf -> Bool
  typedP (PSelf _) = True
  typedP (PChk _ _ _) = True
  typedP (PAt _ _ _) = True
  typedP (CPiApp f a) = typedP f && synthP a
  typedP (CSigmaElim1 p) = typedP p
  typedP (CSigmaElim2 p) = typedP p
  typedP (COut p) = typedP p
  typedP _ = False

  ||| →: given one side, can the proof produce the other? (True: the
  ||| left side is given, the right produced.)
  dirP : Bool -> Prf -> Bool
  dirP d PReflx = True
  dirP d (PDeltaAll _) = d
  dirP d (PSym p) = dirP (not d) p
  dirP d (PTrans p q) =
    if d then (dirP True p && dirP True q) || synthP q
         else (dirP False q && dirP False p) || synthP p
  dirP d (PTransAt p _ q) = if d then dirP True q else dirP False p
  dirP d (PConv _ _ p) = dirP d p
  dirP d p =
    if synthP p then True
      else case congChildren p of
             Just cs => all (dirP d) cs
             Nothing => False

||| Neutral inference (spines only, arguments unchecked): the type a
||| well-typed neutral has at its position, by typing inversion — a
||| neutral's typings all factor through its head's declared type. The
||| one way a position's type is read off the SIDE rather than the type
||| flowing down: at motive-dependent case positions the node carries
||| no motive for, and at the function of an application.
export
inferHead : Sig -> Ctx -> Elem -> KM (Maybe Ty)
inferHead sig ctx (CtxVar i) = pure (ctxLookup ctx i)
inferHead sig ctx (PiApp f e) = do
  mf <- inferHead sig ctx f
  case mf of
    Just fTy => do
      t <- kWhnfT sig fTy
      case t of
        PiTy _ b => pure (Just (substTy b (Ext Id e)))
        _ => pure Nothing
    Nothing => pure Nothing
inferHead sig ctx (SigmaElim1 t) = do
  mt <- inferHead sig ctx t
  case mt of
    Just tTy => do
      t' <- kWhnfT sig tTy
      case t' of
        SigmaTy a _ => pure (Just a)
        _ => pure Nothing
    Nothing => pure Nothing
inferHead sig ctx (SigmaElim2 t) = do
  mt <- inferHead sig ctx t
  case mt of
    Just tTy => do
      t' <- kWhnfT sig tTy
      case t' of
        SigmaTy _ b => pure (Just (substTy b (Ext Id (SigmaElim1 t))))
        _ => pure Nothing
    Nothing => pure Nothing
inferHead sig ctx (Out t) = do
  mt <- inferHead sig ctx t
  case mt of
    Just tTy => do
      t' <- kWhnfT sig tTy
      case t' of
        NuTy f => pure (Just (reflectPoly f (Elem.NuTy f)))
        _ => pure Nothing
    Nothing => pure Nothing
inferHead sig ctx (SigVar x es) =
  kSigLookup sig x >>= \entryX => case entryX of
    Just (SigDef _ _ _ ty) => pure (Just (substTy ty (embed es)))
    Just (SigDecl _ _ ty) => pure (Just (substTy ty (embed es)))
    _ => pure Nothing
inferHead sig ctx _ = pure Nothing

||| Expected type of the i-th spine entry of a former carrying 𝒮
||| (position k's reflected binder/arity telescope).
export
qSpineChildTy : QSig -> Nat -> SubNorm -> Nat -> Maybe Ty
qSpineChildTy sg k es i =
  case qEntry sg k of
    Nothing => Nothing
    Just entry =>
      case reflTel sg (qwAt k) entry of
        Left _ => Nothing
        Right (tel, _, _) => telInst tel i (toList es)

||| Every addressable occurrence of the named definitions, unfolded at
||| once (the δ-all leaf). Carried signatures, polynomials, motives and
||| methods are opaque.
traverseSN : (Elem -> KM Elem) -> SubNorm -> KM SubNorm
traverseSN f [<] = pure [<]
traverseSN f (es :< e) = [| traverseSN f es :< f e |]

export
unfoldAllK : Sig -> List String -> Elem -> KM Elem
unfoldAllK sig ns t = go t
 where
  go : Elem -> KM Elem
  go (SigVar x es) = do
    es' <- traverseSN go es
    if elem x ns
      then kSigLookup sig x >>= \entryX => case entryX of
             Just (SigDef _ _ body _) => pure (substElem body (embed es'))
             _ => pure (SigVar x es')
      else pure (SigVar x es')
  go (ZeroElim u) = ZeroElim <$> go u
  go (NatIntro1 u) = NatIntro1 <$> go u
  go (NatElim z st u) = [| NatElim (go z) (go st) (go u) |]
  go (PiIntro f) = PiIntro <$> go f
  go (PiApp f e) = [| PiApp (go f) (go e) |]
  go (Let a b) = [| Let (go a) (go b) |]
  go (SigmaIntro u v) = [| SigmaIntro (go u) (go v) |]
  go (SigmaElim1 u) = SigmaElim1 <$> go u
  go (SigmaElim2 u) = SigmaElim2 <$> go u
  go (Inj1 u) = Inj1 <$> go u
  go (Inj2 u) = Inj2 <$> go u
  go (SumElim l r u) = [| SumElim (go l) (go r) (go u) |]
  go (Elem.PiTy a c) = [| Elem.PiTy (go a) (go c) |]
  go (Elem.SigmaTy a c) = [| Elem.SigmaTy (go a) (go c) |]
  go (Elem.SumTy a c) = [| Elem.SumTy (go a) (go c) |]
  go (Elem.EqTy l r u) = [| Elem.EqTy (go l) (go r) (go u) |]
  go (QuotTy a r) = [| QuotTy (go a) (go r) |]
  go (Class a) = Class <$> go a
  go (QuotElim f q) = [| QuotElim (go f) (go q) |]
  go (Squash u) = Squash <$> go u
  -- carried signatures: their embedded Nova pieces unfold too
  go (QSort sg k es) = [| QSort (traverseQSig go sg) (pure k) (traverseSN go es) |]
  go (QCtor sg k es) = [| QCtor (traverseQSig go sg) (pure k) (traverseSN go es) |]
  go (QElim sg k fs es w) = [| QElim (traverseQSig go sg) (pure k) (pure fs) (traverseSN go es) (go w) |]
  go (Out u) = Out <$> go u
  go (Corec p a f x) = [| Corec (pure p) (go a) (go f) (go x) |]
  go u = pure u

weakenTyN : Nat -> Ty -> Ty
weakenTyN Z t = t
weakenTyN (S n) t = weakenTyN n (substTy t Wk)

||| The goal a proof is read against: one side (→, with its direction:
||| True = the left side is given) or both (⇐).
data Goal : Type where
  GDir : Bool -> Elem -> Goal
  GChk : Elem -> Elem -> Goal

goalLeft : Goal -> Elem
goalLeft (GDir _ x) = x
goalLeft (GChk l _) = l

||| Classifier of a shared former's components: 𝕍 when the parent is
||| expected at 𝕍 (a type), 𝕌 otherwise (a code).
export
compClassifier : Sig -> Maybe Ty -> KM Ty
compClassifier sig Nothing = pure UniverseTy
compClassifier sig (Just pe) = do
  t <- kWhnfT sig pe
  pure (case t of
          TopTy => TopTy
          _ => UniverseTy)
-- ===== Item-level checking over annotation skeletons =====
--
-- (The equation-replay functions kEqElem/kEqTy live in the same mutual
-- block as the item-level checkers below: the FPropExt final's
-- hypothetical premises are TYPING judgements checked by kCheckE.)
--
-- The kernel's item input is the core term plus a SKELETON: a tree
-- aligned with the term's path-children, whose nodes carry exactly
-- what bidirectional checking cannot invent — eliminator motives (with
-- their own skeletons), expected types at introduction forms appearing
-- in inference position (from ascriptions), conversion certificates at
-- switch sites, Refl equations, and quot-elim well-definedness. The
-- kernel re-establishes the item from ITS OWN Σ; the elaborator's
-- opinion of the same item is not consulted.

skelPayloads : Skel -> List Payload
skelPayloads (Nd ps _) = ps

skelChild : Nat -> Skel -> Skel
skelChild i (Nd _ cs) = fromMaybe (Nd [] []) (getAt i cs)

takeP : (Payload -> Maybe a) -> Skel -> Maybe (a, Skel)
takeP f (Nd ps cs) = go [] ps
 where
  go : List Payload -> List Payload -> Maybe (a, Skel)
  go _ [] = Nothing
  go acc (p :: rest) =
    case f p of
      Just x => Just (x, Nd (reverse acc ++ rest) cs)
      Nothing => go (p :: acc) rest

pMotive : Payload -> Maybe (Ty, Skel)
pMotive (PMotive t sk) = Just (t, sk)
pMotive _ = Nothing

pIntroTy : Payload -> Maybe (Ty, Skel)
pIntroTy (PIntroTy t sk) = Just (t, sk)
pIntroTy _ = Nothing

pSwitch : Payload -> Maybe Prf
pSwitch (PSwitch c) = Just c
pSwitch _ = Nothing

pReflEq : Payload -> Maybe Prf
pReflEq (PReflEq c) = Just c
pReflEq _ = Nothing

pWD : Payload -> Maybe Prf
pWD (PWD c) = Just c
pWD _ = Nothing

pExpose : Payload -> Maybe (Ty, Prf)
pExpose (PExpose t c) = Just (t, c)
pExpose _ = Nothing

pScrut : Payload -> Maybe (Ty, Prf)
pScrut (PScrut t c) = Just (t, c)
pScrut _ = Nothing

pSquashWit : Payload -> Maybe (Elem, Skel)
pSquashWit (PSquashWit e sk) = Just (e, sk)
pSquashWit _ = Nothing

pNuCoind : Payload -> Maybe (Elem, Skel, Elem, Skel, Elem, Skel)
pNuCoind (PNuCoind r skR pw skp qw skq) = Just (r, skR, pw, skp, qw, skq)
pNuCoind _ = Nothing

pSquashElim : Payload -> Maybe (Elem, Skel, Maybe (Ty, Prf), Elem, Skel, Skel)
pSquashElim (PSquashElim e esk ex b bsk gsk) = Just (e, esk, ex, b, bsk, gsk)
pSquashElim _ = Nothing

pQMotives : Payload -> Maybe (List Ty, List Skel)
pQMotives (PQMotives ms sks) = Just (ms, sks)
pQMotives _ = Nothing

pQCoh : Payload -> Maybe (List Prf)
pQCoh (PQCoh cs) = Just cs
pQCoh _ = Nothing

||| Wk composed n times (the weakening Γ·(n entries) ⇒ Γ).
wkSubN : Nat -> Sub
wkSubN Z = Id
wkSubN (S n) = Chain (wkSubN n) Wk

isIntro : Elem -> Bool
isIntro (PiIntro _) = True
isIntro (SigmaIntro _ _) = True
isIntro (Inj1 _) = True
isIntro (Inj2 _) = True
isIntro (Class _) = True
isIntro (ZeroElim _) = True
isIntro Star = True
isIntro _ = False

mutual
  ||| Check a proof of the element equation Γ ⊢ l ≐ r : ty: both sides
  ||| β-joined, then the proof read against them (⇐). No δ anywhere
  ||| but at a δ leaf.
  export
  kEqElem : Sig -> Ctx -> Prf -> Elem -> Elem -> Ty -> KM ()
  kEqElem sig ctx PReflx l r ty =
    if l == r then pure () else do
      l0 <- kJoinElem sig l
      r0 <- kJoinElem sig r
      if l0 == r0 then pure ()
        else kerr "kernel: sides differ under β (an unfolding the join needs is a δ leaf)\n  left:  \{show l0}\n  right: \{show r0}"
  kEqElem sig ctx prf l r ty = do
    l0 <- kJoinElem sig l
    r0 <- kJoinElem sig r
    annotP (ignore (kPrfGo sig ctx prf (GChk l0 r0) (Just ty)))
   where
    annotP : KM a -> KM a
    annotP (MkKM f) = MkKM $ \st => case f st of
      Left e => Left (e ++ " [proof: " ++ show prf ++ "]")
      Right v => Right v

  ||| A proof of the type equation Γ ⊢ A ≐ B: an element equation at
  ||| 𝕍 (one sort, one channel).
  export
  kEqTy : Sig -> Ctx -> Prf -> Ty -> Ty -> KM ()
  kEqTy sig ctx prf a b = kEqElem sig ctx prf a b TopTy

  ||| Both elements join to the same β-normal form.
  sameB : Sig -> Elem -> Elem -> KM ()
  sameB sig a b =
    if a == b then pure () else do
      a' <- kJoinElem sig a
      b' <- kJoinElem sig b
      if a' == b' then pure ()
        else kerr "kernel: sides differ under β\n  left:  \{show a'}\n  right: \{show b'}"

  ||| Two types agree: join-syntactically, or by cumulativity (a 𝕌
  ||| code at a 𝕍 position, code-lift-eq). No δ: a stated equation
  ||| whose type is spelled otherwise than its position's arrives
  ||| converted (PAt).
  tyAgree : Sig -> Ty -> Ty -> KM Bool
  tyAgree sig exp got = do
    expN <- kJoinTy sig exp
    gotN <- kJoinTy sig got
    if expN == gotN || (expN == TopTy && gotN == UniverseTy)
      then pure True
      else case (expN, gotN) of
        -- a CARRIED SIGNATURE is inert syntax compared after the
        -- β-join (structural identity, as el-qiit-beta fires): two
        -- sorts at one position and spine agree when their carried
        -- signatures join alike (A3, §9; no δ inside a carrier either)
        (QSort sg0 k0 es0, QSort sg1 k1 es1) =>
          if k0 == k1 && es0 == es1
            then do
              n0 <- kJoinQSig sig sg0
              n1 <- kJoinQSig sig sg1
              pure (n0 == n1)
            else pure False
        _ => pure False

  ||| POSITIONAL TYPE CHECK: a leaf's equation is at the type of the
  ||| position it sits at — the type flowing down, or, where the node
  ||| above determines none, the side's own inferred type (typing
  ||| inversion for neutrals).
  posTyCheck : Sig -> Ctx -> Maybe Ty -> Elem -> Ty -> KM ()
  posTyCheck sig ctx mty x t = do
    exp <- the (KM Ty) $ case mty of
      Just e => pure e
      Nothing => do
        mu <- inferHead sig ctx x
        case mu of
          Just u => pure u
          Nothing => kerr "kernel: proof at a type-undetermined position [not inferable: \{show x}]"
    ok <- tyAgree sig exp t
    if ok then pure ()
      else kerr "kernel: proof type does not match the position [position: \{show exp}; proof: \{show t}]"

  needTy : Maybe Ty -> String -> KM Ty
  needTy (Just t) _ = pure t
  needTy Nothing what = kerr "kernel: \{what} at a type-undetermined position"

  ||| Entry i of a definition's context, instantiated by the earlier
  ||| entries; likewise for a reflected telescope.
  deltaEntryTy : List Ty -> Nat -> List Elem -> KM Ty
  deltaEntryTy dl i pre = case getAt i dl of
    Just t => pure (substTy t (embed (cast pre)))
    Nothing => kerr "kernel: δ leaf spine out of range"

  telEntryTy : List Ty -> Nat -> List Elem -> KM Ty
  telEntryTy tel i pre = case telInst tel i pre of
    Just t => pure t
    Nothing => kerr "kernel: path leaf telescope mismatch"

  ||| A spine stated entrywise: proof i states its element (reflexively)
  ||| at the type the earlier entries determine.
  statedSpine : Sig -> Ctx -> (Nat -> List Elem -> KM Ty) -> List Prf -> KM (List Elem)
  statedSpine sig ctx entryTy qs = go 0 qs []
   where
    go : Nat -> List Prf -> List Elem -> KM (List Elem)
    go i [] acc = pure (reverse acc)
    go i (q :: rest) acc = do
      (u0, u1, uTy) <- kPrfS sig ctx q
      ty <- entryTy i (reverse acc)
      ok <- tyAgree sig ty uTy
      if ok && u0 == u1 then go (S i) rest (u0 :: acc)
        else kerr "kernel: spine entry \{show i} is not the required element at its type [stated \{show u0} : \{show uTy}; required \{show ty}]"

  applySel : Sig -> Ctx -> (Elem, Elem, Ty) -> Sel -> KM (Elem, Elem, Ty)
  applySel sig ctx (l, r, _) sel = do
    -- β-joined: a side whose head only δ exposes arrives exposed (the
    -- stated equation is transitivity over the exposure)
    l' <- kJoinElem sig l
    r' <- kJoinElem sig r
    case (sel, l', r') of
      (SelSuc, NatIntro1 x, NatIntro1 y) => pure (x, y, NatTy)
      (SelDom, Elem.PiTy a0 _, Elem.PiTy a1 _) => pure (a0, a1, UniverseTy)
      (SelDom, Elem.SigmaTy a0 _, Elem.SigmaTy a1 _) => pure (a0, a1, UniverseTy)
      -- binder-crossing selectors: the instantiation elements come from
      -- the (untrusted) certificate, so el-sub-cong-fix's premise is CHECKED
      (SelCod q, Elem.PiTy _ b0, Elem.PiTy a1 b1) => do
        u <- statedAt q a1
        pure (substElem b0 (Ext Id u), substElem b1 (Ext Id u), UniverseTy)
      (SelCod q, Elem.SigmaTy _ b0, Elem.SigmaTy a1 b1) => do
        u <- statedAt q a1
        pure (substElem b0 (Ext Id u), substElem b1 (Ext Id u), UniverseTy)
      -- code-sum-inj: non-dependent, both components at 𝕌 directly
      (SelSumL, Elem.SumTy a0 _, Elem.SumTy a1 _) => pure (a0, a1, UniverseTy)
      (SelSumR, Elem.SumTy _ b0, Elem.SumTy _ b1) => pure (b0, b1, UniverseTy)
      (SelQDom, QuotTy a0 _, QuotTy a1 _) => pure (a0, a1, UniverseTy)
      -- code-quot-inj: the relation components live at Ω
      (SelQRel qu qv, QuotTy _ r0, QuotTy a1 r1) => do
        u <- statedAt qu a1
        v <- statedAt qv a1
        pure (substElem r0 (Ext (Ext Id u) v), substElem r1 (Ext (Ext Id u) v), PropTy)
      -- QIIT code injectivity, indexwise: the signatures and sort must be
      -- nf-identical and the spines must AGREE before i (so the entry
      -- type is determined by the shared pre). NO selector passes from
      -- constructor equations to components: point constructors are not
      -- injective (equation constructors may merge them).
      (SelQIdx i, QSort sg0 k0 es0, QSort sg1 k1 es1) =>
        if sg0 == sg1 && k0 == k1
          then do
            let l0 = toList es0
            let l1 = toList es1
            if take i l0 /= take i l1
              then kerr "kernel: qidx selector at spines that differ before i"
              else case qEntry sg0 k0 of
                Nothing => kerr "kernel: qidx selector: sort out of range"
                Just entry => do
                  (tel, _, _) <- liftQ (reflTel sg0 (qwAt k0) entry)
                  case (getAt i l0, getAt i l1, telInst tel i l0) of
                    (Just a0, Just a1, Just ty) => pure (a0, a1, ty)
                    _ => kerr "kernel: qidx selector index out of range"
          else kerr "kernel: qidx selector at different signatures or sorts"
      _ => kerr "kernel: selector does not apply"
   where
    ||| the element a proof states (reflexively) at the required type
    statedAt : Prf -> Ty -> KM Elem
    statedAt q ty = do
      (u0, u1, uTy) <- kPrfS sig ctx q
      ok <- tyAgree sig ty uTy
      if ok && u0 == u1 then pure u0
        else kerr "kernel: selector instantiation is not the required element at its type"

  ||| ⇒: the equation (with its type) a synthesising proof states.
  export
  kPrfS : Sig -> Ctx -> Prf -> KM (Elem, Elem, Ty)
  -- self: the declared type, no unfolding (a reference's spine
  -- checked against its context, β-only, bare skeletons)
  kPrfS sig ctx (PSelf t) = case t of
    CtxVar i => case ctxLookup ctx i of
      Just ty => pure (t, t, ty)
      Nothing => kerr "kernel: self leaf: variable out of bounds"
    SigVar x es => kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ ty) => do
        kCheckSubstK sig ctx (toList es) (toList delta) (map (const (Nd [] [])) (toList es))
        pure (t, t, substTy ty (embed es))
      Just (SigDecl delta _ ty) => do
        kCheckSubstK sig ctx (toList es) (toList delta) (map (const (Nd [] [])) (toList es))
        pure (t, t, substTy ty (embed es))
      _ => kerr "kernel: self leaf: bad signature reference '\{x}'"
    NatIntro0 => pure (t, t, NatTy)
    OneIntro => pure (t, t, OneTy)
    Elem.ZeroTy => pure (t, t, UniverseTy)
    Elem.OneTy => pure (t, t, UniverseTy)
    Elem.NatTy => pure (t, t, UniverseTy)
    _ => kerr "kernel: self leaf at a term with no declared type [\{show t}]"
  -- checked reflexivity: the term at its ascribed type, with skeleton
  kPrfS sig ctx (PChk t ty sk) = do
    kCheckE sig ctx t ty sk
    pure (t, t, ty)
  -- reflection: the stated proof's type is (β-whnf) an equality prop
  kPrfS sig ctx (PRefl p) = do
    (_, _, pty) <- kPrfS sig ctx p
    pty' <- kWhnfT sig pty
    case pty' of
      Elem.EqTy l r t => pure (l, r, t)
      _ => kerr "kernel: reflected proof is not at an equality [\{show p} : \{show pty}]"
  -- typed spines: the head states its type, the elimination follows
  -- it (β-whnf for the shape — a hidden one arrives ascribed)
  kPrfS sig ctx (CPiApp qf qa) = do
    (f0, f1, fTy) <- kPrfS sig ctx qf
    fTy' <- kWhnfT sig fTy
    case fTy' of
      PiTy dom cod => do
        (a0, a1, aTy) <- kPrfS sig ctx qa
        ok <- tyAgree sig dom aTy
        if ok then pure (PiApp f0 a0, PiApp f1 a1, substTy cod (Ext Id a0))
          else kerr "kernel: spine argument at the wrong type [expected \{show dom}; stated \{show aTy}]"
      _ => kerr "kernel: spine applies a non-function [\{show f0} : \{show fTy'}]"
  kPrfS sig ctx (CSigmaElim1 q) = do
    (t0, t1, tTy) <- kPrfS sig ctx q
    tTy' <- kWhnfT sig tTy
    case tTy' of
      SigmaTy a _ => pure (SigmaElim1 t0, SigmaElim1 t1, a)
      _ => kerr "kernel: spine projects a non-pair [\{show t0} : \{show tTy'}]"
  kPrfS sig ctx (CSigmaElim2 q) = do
    (t0, t1, tTy) <- kPrfS sig ctx q
    tTy' <- kWhnfT sig tTy
    case tTy' of
      SigmaTy _ b => pure (SigmaElim2 t0, SigmaElim2 t1, substTy b (Ext Id (SigmaElim1 t0)))
      _ => kerr "kernel: spine projects a non-pair [\{show t0} : \{show tTy'}]"
  kPrfS sig ctx (COut q) = do
    (t0, t1, tTy) <- kPrfS sig ctx q
    tTy' <- kWhnfT sig tTy
    case tTy' of
      NuTy f => pure (Out t0, Out t1, reflectPoly f (Elem.NuTy f))
      _ => kerr "kernel: spine observes a non-ν element [\{show t0} : \{show tTy'}]"
  kPrfS sig ctx (CNatIntro1 q) = do
    (t0, t1, tTy) <- kPrfS sig ctx q
    ok <- tyAgree sig NatTy tTy
    if ok then pure (NatIntro1 t0, NatIntro1 t1, NatTy)
      else kerr "kernel: S of a non-numeral"
  -- x-δ, stated: each spine entry is stated by its proof at Δ's type
  -- (instantiated by the earlier entries), and the equation is
  -- x[ē] ≐ t[ē] at T[ē]
  kPrfS sig ctx (PDelta x qs) =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ body ty) => do
        let dl = toList delta
        if length qs /= length dl
          then kerr "kernel: δ leaf spine length mismatch for '\{x}'"
          else pure ()
        es <- statedSpine sig ctx (deltaEntryTy dl) qs
        let esN = the SubNorm (cast es)
        pure (SigVar x esN, substElem body (embed esN), substTy ty (embed esN))
      Just _ => kerr "kernel: δ leaf at a declaration '\{x}'"
      Nothing => kerr "kernel: δ leaf names unknown definition '\{x}'"
  kPrfS sig ctx (PPath sg k qs) = do
    sg' <- kJoinQSig sig sg
    entry <- case qEntry sg' k of
               Just e => pure e
               Nothing => kerr "kernel: path leaf entry out of range"
    case qEntryKind entry of
      QKEq => pure ()
      _ => kerr "kernel: path leaf at a non-equation entry"
    -- the spine stated entrywise at the reflected binder telescope
    (tel, _, _) <- liftQ (reflTel sg' (qwAt k) entry)
    if length qs /= length tel
      then kerr "kernel: path leaf spine length mismatch"
      else pure ()
    args <- statedSpine sig ctx (telEntryTy tel) qs
    -- the imposed equation, at the spine
    (wEnd, hd) <- liftQ (walkVals sg' (qwAt k) entry args)
    (lq, rq, uq) <- liftQ (eqHead hd)
    l <- liftQ (reflTm sg' wEnd lq)
    r <- liftQ (reflTm sg' wEnd rq)
    t <- liftQ (reflCodeTy sg' wEnd uq)
    pure (l, r, t)
  kPrfS sig ctx (PAt q ty pt) = do
    (l, r, t) <- kPrfS sig ctx q
    kEqTy sig ctx pt t ty
    pure (l, r, ty)
  kPrfS sig ctx (PSel sel p) = do
    e <- kPrfS sig ctx p
    applySel sig ctx e sel
  kPrfS sig ctx (PSym p) = do
    (l, r, t) <- kPrfS sig ctx p
    pure (r, l, t)
  kPrfS sig ctx (PTrans p q) =
    if synthP p && dirP True q
      then do
        (a, b, t) <- kPrfS sig ctx p
        bJ <- kJoinElem sig b
        c <- kPrfGo sig ctx q (GDir True bJ) (Just t)
        pure (a, c, t)
      else if synthP q && dirP False p
      then do
        (b, c, t) <- kPrfS sig ctx q
        bJ <- kJoinElem sig b
        a <- kPrfGo sig ctx p (GDir False bJ) (Just t)
        pure (a, c, t)
      else kerr "kernel: transitivity does not state its equation"
  kPrfS sig ctx p = kerr "kernel: proof does not state its equation: \{show p}"

  ||| A congruence node: the side(s) decompose by `shape` into the
  ||| children's parts, `kids` computes each child's context and
  ||| expected type from the LEFT parts, the children are read against
  ||| their parts, and `rebuild` reassembles (the produced side under
  ||| →; unused under ⇐).
  node : Sig -> Ctx -> Goal
      -> (Elem -> Maybe (List Elem))
      -> (List Elem -> Maybe Elem)
      -> (List Elem -> KM (List (Ctx, Maybe Ty)))
      -> List Prf -> KM Elem
  node sig ctx goal shape rebuild kids ps = do
    (ls, rs) <- the (KM (List Elem, Maybe (List Elem))) $ case goal of
      GDir d x => case shape x of
        Just xs => pure (xs, Nothing)
        Nothing => kerr "kernel: proof shape does not match the side [\{show x}]"
      GChk l r => case (shape l, shape r) of
        (Just ls, Just rs) => pure (ls, Just rs)
        _ => kerr "kernel: proof shape does not match the sides\n  left:  \{show l}\n  right: \{show r}"
    infos <- kids ls
    outs <- goKids ps ls rs infos
    case rebuild outs of
      Just e => pure e
      Nothing => kerr "kernel: proof node arity"
   where
    goKids : List Prf -> List Elem -> Maybe (List Elem) -> List (Ctx, Maybe Ty) -> KM (List Elem)
    goKids [] [] _ [] = pure []
    goKids (p :: ps') (l :: ls) rs ((c, t) :: is) = do
      (g, rs') <- the (KM (Goal, Maybe (List Elem))) $ case (goal, rs) of
        (GDir d _, _) => pure (GDir d l, rs)
        (GChk _ _, Just (r :: rest)) => pure (GChk l r, Just rest)
        _ => kerr "kernel: proof node arity"
      o <- kPrfGo sig c p g t
      os <- goKids ps' ls rs' is
      pure (o :: os)
    goKids _ _ _ _ = kerr "kernel: proof node arity"

  ||| One child: the shape has exactly one part.
  node1 : Sig -> Ctx -> Goal -> (Elem -> Maybe Elem) -> (Elem -> Elem) -> (Ctx, Maybe Ty) -> Prf -> KM Elem
  node1 sig ctx goal shape rebuild info p =
    node sig ctx goal (\x => map (\u => [u]) (shape x))
         (\xs => case xs of
                   [u] => Just (rebuild u)
                   _ => Nothing)
         (\_ => pure [info]) [p]

  ||| The expected type of spine entry i of a signature reference,
  ||| instantiated by the earlier entries.
  export
  sigChildTy : Sig -> String -> List Elem -> Nat -> KM (Maybe Ty)
  sigChildTy sig x es i =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ _) => pure (inst delta)
      Just (SigDecl delta _ _) => pure (inst delta)
      _ => pure Nothing
   where
    inst : SnocList Ty -> Maybe Ty
    inst delta = case getAt i (toList delta) of
      Just entryTy => Just (substTy entryTy (embed (cast (take i es))))
      Nothing => Nothing

  ||| The whole proof, read against its goal at the position's type
  ||| (Nothing: undetermined). Under → the produced side is returned
  ||| (unjoined); under ⇐ the return value is meaningless.
  kPrfGo : Sig -> Ctx -> Prf -> Goal -> Maybe Ty -> KM Elem
  -- a congruence node that runs left to right is read so under ⇐
  -- first — the produced side compared with the right one under β —
  -- so the right side need not have the node's shape (it may be the
  -- β-normal form of what the node produces: a δ exposure's result);
  -- a node whose children were built over the RIGHT side (a chain of
  -- δ leaves read backwards) falls back to decomposition
  kPrfGo sig ctx prf goal@(GChk l r) mty =
    if isJust (congChildren prf) && dirP True prf
      then kOrElse (do x <- kPrfGo sig ctx prf (GDir True l) mty
                       sameB sig x r
                       pure l)
                   (kPrfGoAt sig ctx prf goal mty)
      else kPrfGoAt sig ctx prf goal mty
  kPrfGo sig ctx prf goal mty = kPrfGoAt sig ctx prf goal mty

  kPrfGoAt : Sig -> Ctx -> Prf -> Goal -> Maybe Ty -> KM Elem
  kPrfGoAt sig ctx prf goal mty = case (prf, goal) of
    -- ----- structure -----
    (PReflx, GDir _ x) => pure x
    (PReflx, GChk l r) => do sameB sig l r; pure l
    (PDeltaAll ns, GDir True x) => unfoldAllK sig ns x
    (PDeltaAll ns, GDir False x) => kerr "kernel: δ-all runs left to right only"
    (PDeltaAll ns, GChk l r) => do
      l' <- unfoldAllK sig ns l
      sameB sig l' r
      pure l
    (PSym q, GDir d x) => kPrfGo sig ctx q (GDir (not d) x) mty
    (PSym q, GChk l r) => do
      ignore (kPrfGo sig ctx q (GChk r l) mty)
      pure l
    (PTrans q1 q2, GDir True x) =>
      if dirP True q1 && dirP True q2
        then do
          m <- kPrfGo sig ctx q1 (GDir True x) mty >>= kJoinElem sig
          kPrfGo sig ctx q2 (GDir True m) mty
        else if synthP q2
        then do
          (b, c, t) <- kPrfS sig ctx q2
          posTyCheck sig ctx mty x t
          bJ <- kJoinElem sig b
          ignore (kPrfGo sig ctx q1 (GChk x bJ) mty)
          pure c
        else kerr "kernel: transitivity with no computable middle (left to right)"
    (PTrans q1 q2, GDir False x) =>
      if dirP False q2 && dirP False q1
        then do
          m <- kPrfGo sig ctx q2 (GDir False x) mty >>= kJoinElem sig
          kPrfGo sig ctx q1 (GDir False m) mty
        else if synthP q1
        then do
          (a, b, t) <- kPrfS sig ctx q1
          posTyCheck sig ctx mty x t
          bJ <- kJoinElem sig b
          ignore (kPrfGo sig ctx q2 (GChk bJ x) mty)
          pure a
        else kerr "kernel: transitivity with no computable middle (right to left)"
    (PTrans q1 q2, GChk l r) =>
      if dirP True q1
        then do
          m <- kPrfGo sig ctx q1 (GDir True l) mty >>= kJoinElem sig
          kPrfGo sig ctx q2 (GChk m r) mty
        else if dirP False q2
        then do
          m <- kPrfGo sig ctx q2 (GDir False r) mty >>= kJoinElem sig
          kPrfGo sig ctx q1 (GChk l m) mty
        else kerr "kernel: transitivity with no computable middle"
    (PTransAt q1 m q2, GDir True x) => do
      mJ <- kJoinElem sig m
      ignore (kPrfGo sig ctx q1 (GChk x mJ) mty)
      kPrfGo sig ctx q2 (GDir True mJ) mty
    (PTransAt q1 m q2, GDir False x) => do
      mJ <- kJoinElem sig m
      ignore (kPrfGo sig ctx q2 (GChk mJ x) mty)
      kPrfGo sig ctx q1 (GDir False mJ) mty
    (PTransAt q1 m q2, GChk l r) => do
      mJ <- kJoinElem sig m
      ignore (kPrfGo sig ctx q1 (GChk l mJ) mty)
      ignore (kPrfGo sig ctx q2 (GChk mJ r) mty)
      pure l
    (PConv pt tyX q, _) => do
      ty <- needTy mty "type conversion"
      case ty of
        TopTy => kerr "kernel: a type equation cannot convert its type"
        _ => pure ()
      kEqTy sig ctx pt ty tyX
      kPrfGo sig ctx q goal (Just tyX)
    -- ----- type-directed leaves (⇐ only) -----
    (PIrrel sk, GChk l r) => do
      ty <- needTy mty "irrelevance"
      ty' <- kWhnfT sig ty
      case ty' of
        OneTy => pure l
        ZeroTy => pure l
        -- el-prf-prop: proof irrelevance — an ≡-/∥·∥-headed type IS
        -- a prop; a neutral takes the judgemental question at Ω,
        -- through the carried skeleton (the type AS WRITTEN first)
        _ => do
          ok <- kIsProp sig ctx ty sk
          if ok then pure l
            else kerr "kernel: irrelevance at a non-propositional type"
    (PEtaPi q, GChk l r) => do
      ty <- needTy mty "Π-η"
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy dom cod => do
          kEqElem sig (ctx :< dom) q
            (PiApp (substElem l Wk) (CtxVar 0))
            (PiApp (substElem r Wk) (CtxVar 0))
            cod
          pure l
        _ => kerr "kernel: Π-η at a non-Π type"
    (PEtaSigma q1 q2, GChk l r) => do
      ty <- needTy mty "Σ-η"
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy dom cod => do
          kEqElem sig ctx q1 (SigmaElim1 l) (SigmaElim1 r) dom
          kEqElem sig ctx q2 (SigmaElim2 l) (SigmaElim2 r)
            (substTy cod (Ext Id (SigmaElim1 l)))
          pure l
        _ => kerr "kernel: Σ-η at a non-Σ type"
    (PQuotWit mq, GChk l r) => do
      ty <- needTy mty "quotient witness"
      ty' <- kWhnfT sig ty
      case (l, r, ty') of
        (Class a, Class b, QuotTy dom rel) => do
          relInst <- kJoinElem sig (substElem rel (Ext (Ext Id a) b))
          case relInst of
            Squash sq => do
              sq' <- kWhnfT sig sq
              case sq' of
                OneTy => pure l
                _ => kerr "kernel: quotient witness does not apply"
            Elem.EqTy wl wr wt =>
              case mq of
                Just q => do kEqElem sig ctx q wl wr wt; pure l
                Nothing => kerr "kernel: quotient witness needs a proof at an equality relation"
            _ => kerr "kernel: quotient witness at a non-evident relation"
        _ => kerr "kernel: quotient witness at a non-class equation"
    -- el-quot-eq, faithful: the relation instance is inhabited by
    -- the supplied proof, whatever the relation's shape
    (PQuotWitPrf w skW, GChk l r) => do
      ty <- needTy mty "quotient witness"
      ty' <- kWhnfT sig ty
      case (l, r, ty') of
        (Class a, Class b, QuotTy _ rel) => do
          relInst <- kJoinElem sig (substElem rel (Ext (Ext Id a) b))
          kCheckE sig ctx w relInst skW
          pure l
        _ => kerr "kernel: supplied quotient witness at a non-class equation"
    (PInj q, GChk l r) => do
      ty <- needTy mty "injection"
      ty' <- kWhnfT sig ty
      case (l, r, ty') of
        (Inj1 x, Inj1 y, SumTy a _) => do kEqElem sig ctx q x y a; pure l
        (Inj2 x, Inj2 y, SumTy _ b) => do kEqElem sig ctx q x y b; pure l
        _ => kerr "kernel: injection proof at a non-matching equation"
    (PPropExt s skS t skT, GChk l r) => do
      -- code-prop-eq: the sides are prop codes; each direction is an
      -- implication between their decodings
      ty <- needTy mty "propext"
      ty' <- kWhnfT sig ty
      case ty' of
        PropTy => do
          kCheckE sig ctx s (PiTy l (substTy r Wk)) skS
          kCheckE sig ctx t (PiTy r (substTy l Wk)) skT
          pure l
        _ => kerr "kernel: propext at a non-Ω type"
    (PPrfCong skl skr q, GChk l r) => do
      -- prop-lift-eq: the sides MUST be props (the lift's side
      -- condition is load-bearing — without it a code equation
      -- could be smuggled through Ω's extensional discipline)
      ty <- needTy mty "prop-lift"
      ty' <- kWhnfT sig ty
      case ty' of
        TopTy => do
          okL <- kIsProp sig ctx l skl
          okR <- kIsProp sig ctx r skr
          if okL && okR
            then do kEqElem sig ctx q l r PropTy; pure l
            else kerr "kernel: prop-lift-eq at non-prop types"
        _ => kerr "kernel: prop-lift-eq on an element equation"
    (PIrrel _, GDir _ _) => needBoth
    (PEtaPi _, GDir _ _) => needBoth
    (PEtaSigma _ _, GDir _ _) => needBoth
    (PQuotWit _, GDir _ _) => needBoth
    (PQuotWitPrf _ _, GDir _ _) => needBoth
    (PInj _, GDir _ _) => needBoth
    (PPropExt _ _ _ _, GDir _ _) => needBoth
    (PPrfCong _ _ _, GDir _ _) => needBoth
    -- ----- synthesising leaves -----
    -- x-δ left to right: a plain unfolding of the occurrence — no
    -- positional check is needed, the occurrence is well-typed by the
    -- invariant and δ preserves its type; spines compared modulo β
    (PDelta x qs, GDir True u) =>
      case u of
        SigVar y es' =>
          if y /= x then kerr "kernel: δ leaf at a reference to '\{y}', stated for '\{x}'"
          else kSigLookup sig x >>= \entryX => case entryX of
            Just (SigDef _ _ body _) => do
              es <- traverse (\q => (\(e, _, _) => e) <$> kPrfS sig ctx q) qs
              esL <- kJoinSubNorm sig (cast es)
              esU <- kJoinSubNorm sig es'
              if esL == esU
                then pure (substElem body (embed es'))
                else kerr "kernel: δ leaf spine does not match the occurrence of '\{x}'"
            Just _ => kerr "kernel: δ leaf at a declaration '\{x}'"
            Nothing => kerr "kernel: δ leaf names unknown definition '\{x}'"
        _ => kerr "kernel: δ leaf at a non-reference [at \{show u}]"
    (PSelf _, _) => synthLeaf
    (PChk _ _ _, _) => synthLeaf
    (PRefl _, _) => synthLeaf
    (PAt _ _ _, _) => synthLeaf
    (PPath _ _ _, _) => synthLeaf
    (PDelta _ _, _) => synthLeaf
    (PSel _ _, _) => synthLeaf
    -- ----- congruences -----
    (CZeroElim q, _) =>
      node1 sig ctx goal (\x => case x of ZeroElim u => Just u; _ => Nothing) ZeroElim (ctx, Just ZeroTy) q
    (CNatIntro1 q, _) =>
      node1 sig ctx goal (\x => case x of NatIntro1 u => Just u; _ => Nothing) NatIntro1 (ctx, Just NatTy) q
    (CNatElim m qz qs qn, _) =>
      let kids : List Elem -> KM (List (Ctx, Maybe Ty))
          kids [z, s, n] = case m of
            -- the CONSTANT-MOTIVE reading: the case positions at the
            -- node's own type (a valid congruence instance whose
            -- premises are demanded at the constant type)
            Nothing =>
              pure [ (ctx, mty)
                   , (ctx :< NatTy :< fromMaybe TopTy (map (\t => substTy t Wk) mty), map (\t => substTy t (wkSubN 2)) mty)
                   , (ctx, Just NatTy) ]
            Just mot => do
              kCheckTyK sig (ctx :< NatTy) mot (Nd [] [])
              motiveAgrees (substTy mot (Ext Id n))
              pure [ (ctx, Just (substTy mot (Ext Id NatIntro0)))
                   , (ctx :< NatTy :< mot, Just (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)))
                   , (ctx, Just NatTy) ]
          kids _ = kerr "kernel: proof node arity"
      in node sig ctx goal (\x => case x of NatElim z s n => Just [z, s, n]; _ => Nothing)
              (\xs => case xs of [z, s, n] => Just (NatElim z s n); _ => Nothing) kids [qz, qs, qn]
    (CPiIntro q, _) => do
      ty <- needTy mty "λ-congruence"
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy a b => node1 sig ctx goal (\x => case x of PiIntro f => Just f; _ => Nothing) PiIntro (ctx :< a, Just b) q
        _ => kerr "kernel: λ-congruence at a non-Π type"
    (CPiApp qf qa, _) =>
      let kids : List Elem -> KM (List (Ctx, Maybe Ty))
          kids [f, a] = do
            fTy <- headTy qf f
            aTy <- the (KM (Maybe Ty)) $ case fTy of
              Just t => do
                t' <- kWhnfT sig t
                pure (case t' of
                        PiTy dom _ => Just dom
                        _ => Nothing)
              Nothing => pure Nothing
            pure [(ctx, fTy), (ctx, aTy)]
          kids _ = kerr "kernel: proof node arity"
      in node sig ctx goal (\x => case x of PiApp f a => Just [f, a]; _ => Nothing)
              (\xs => case xs of [f, a] => Just (PiApp f a); _ => Nothing) kids [qf, qa]
    (CSigmaIntro qu qv, _) => do
      ty <- needTy mty "pair congruence"
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy a b =>
          let kids : List Elem -> KM (List (Ctx, Maybe Ty))
              kids [u, v] = pure [(ctx, Just a), (ctx, Just (substTy b (Ext Id u)))]
              kids _ = kerr "kernel: proof node arity"
          in node sig ctx goal (\x => case x of SigmaIntro u v => Just [u, v]; _ => Nothing)
                  (\xs => case xs of [u, v] => Just (SigmaIntro u v); _ => Nothing) kids [qu, qv]
        _ => kerr "kernel: pair congruence at a non-Σ type"
    (CSigmaElim1 q, _) =>
      node sig ctx goal (\x => case x of SigmaElim1 u => Just [u]; _ => Nothing)
           (\xs => case xs of [u] => Just (SigmaElim1 u); _ => Nothing)
           (\xs => case xs of
                     [u] => do mt <- headTy q u; pure [(ctx, mt)]
                     _ => kerr "kernel: proof node arity") [q]
    (CSigmaElim2 q, _) =>
      node sig ctx goal (\x => case x of SigmaElim2 u => Just [u]; _ => Nothing)
           (\xs => case xs of [u] => Just (SigmaElim2 u); _ => Nothing)
           (\xs => case xs of
                     [u] => do mt <- headTy q u; pure [(ctx, mt)]
                     _ => kerr "kernel: proof node arity") [q]
    (CInj1 q, _) => do
      ty <- needTy mty "inj₁ congruence"
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy a _ => node1 sig ctx goal (\x => case x of Inj1 u => Just u; _ => Nothing) Inj1 (ctx, Just a) q
        _ => kerr "kernel: inj₁ congruence at a non-⊎ type"
    (CInj2 q, _) => do
      ty <- needTy mty "inj₂ congruence"
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy _ b => node1 sig ctx goal (\x => case x of Inj2 u => Just u; _ => Nothing) Inj2 (ctx, Just b) q
        _ => kerr "kernel: inj₂ congruence at a non-⊎ type"
    (CSumElim m ql qr qt, _) =>
      let kids : List Elem -> KM (List (Ctx, Maybe Ty))
          kids [l, r, t] = do
            tTy <- headTy qt t
            (a, b) <- the (KM (Ty, Ty)) $ case tTy of
              Just x => do
                x' <- kWhnfT sig x
                pure (case x' of
                        SumTy a b => (a, b)
                        _ => (TopTy, TopTy))
              Nothing => pure (TopTy, TopTy)
            case m of
              -- the case positions are motive-dependent: undetermined
              -- without a carried motive
              Nothing => pure [(ctx :< a, Nothing), (ctx :< b, Nothing), (ctx, tTy)]
              Just mot => do
                kCheckTyK sig (ctx :< SumTy a b) mot (Nd [] [])
                motiveAgrees (substTy mot (Ext Id t))
                pure [ (ctx :< a, Just (substTy mot (Ext Wk (Inj1 (CtxVar 0)))))
                     , (ctx :< b, Just (substTy mot (Ext Wk (Inj2 (CtxVar 0)))))
                     , (ctx, Just (SumTy a b)) ]
          kids _ = kerr "kernel: proof node arity"
      in node sig ctx goal (\x => case x of SumElim l r t => Just [l, r, t]; _ => Nothing)
              (\xs => case xs of [l, r, t] => Just (SumElim l r t); _ => Nothing) kids [ql, qr, qt]
    -- SHARED formers are typed at both 𝕌 (codes) and 𝕍 (types): the
    -- parent's expected type decides where the components sit. The
    -- binder-crossing component is under the RIGHT side's domain
    -- (ty-pi-cong / ty-sigma-cong): under → left to right that is the
    -- domain the domain proof produces
    (CPiTy qa qb, _) => binderTy (\x => case x of Elem.PiTy a b => Just (a, b); _ => Nothing) Elem.PiTy qa qb
    (CSigmaTy qa qb, _) => binderTy (\x => case x of Elem.SigmaTy a b => Just (a, b); _ => Nothing) Elem.SigmaTy qa qb
    (CSumTy qa qb, _) => do
      cls <- compClassifier sig mty
      node sig ctx goal (\x => case x of Elem.SumTy a b => Just [a, b]; _ => Nothing)
           (\xs => case xs of [a, b] => Just (Elem.SumTy a b); _ => Nothing)
           (\_ => pure [(ctx, Just cls), (ctx, Just cls)]) [qa, qb]
    -- child 2 of ≡ is its ∈-type — a term at 𝕍; children 0/1 sit at it
    (CEqTy ql qr qt, _) =>
      node sig ctx goal (\x => case x of Elem.EqTy l r t => Just [l, r, t]; _ => Nothing)
           (\xs => case xs of [l, r, t] => Just (Elem.EqTy l r t); _ => Nothing)
           (\xs => case xs of
                     [_, _, t] => pure [(ctx, Just t), (ctx, Just t), (ctx, Just TopTy)]
                     _ => kerr "kernel: proof node arity") [ql, qr, qt]
    (CQuotTy qa qr, _) => do
      cls <- compClassifier sig mty
      -- the relation lives under the domain twice; under → left to
      -- right that is the domain the domain proof produces
      case goal of
        GDir d x => case x of
          QuotTy a r => do
            a' <- kPrfGo sig ctx qa (GDir d a) (Just cls)
            let dom = if d then a' else a
            r' <- kPrfGo sig (ctx :< dom :< substTy dom Wk) qr (GDir d r) (Just PropTy)
            pure (QuotTy a' r')
          _ => kerr "kernel: proof shape does not match the side [\{show x}]"
        GChk l r => case (l, r) of
          (QuotTy a0 r0, QuotTy a1 r1) => do
            ignore (kPrfGo sig ctx qa (GChk a0 a1) (Just cls))
            ignore (kPrfGo sig (ctx :< a1 :< substTy a1 Wk) qr (GChk r0 r1) (Just PropTy))
            pure l
          _ => kerr "kernel: proof shape does not match the sides\n  left:  \{show l}\n  right: \{show r}"
    (CSigVar x qs, _) =>
      node sig ctx goal (\u => case u of
                                 SigVar y es => if y == x then Just (toList es) else Nothing
                                 _ => Nothing)
           (\xs => Just (SigVar x (cast xs)))
           (\es => traverse (\i => (\t => (ctx, t)) <$> sigChildTy sig x es i) (indices es)) qs
    (CClass q, _) => do
      ty <- needTy mty "class congruence"
      ty' <- kWhnfT sig ty
      case ty' of
        QuotTy dom _ => node1 sig ctx goal (\x => case x of Class u => Just u; _ => Nothing) Class (ctx, Just dom) q
        _ => kerr "kernel: class congruence at a non-quotient type"
    (CQuotElim m qf qq, _) =>
      let kids : List Elem -> KM (List (Ctx, Maybe Ty))
          kids [f, q] = do
            qTy <- headTy qq q
            (a, r) <- the (KM (Ty, Ty)) $ case qTy of
              Just x => do
                x' <- kWhnfT sig x
                pure (case x' of
                        QuotTy a r => (a, r)
                        _ => (TopTy, TopTy))
              Nothing => pure (TopTy, TopTy)
            case m of
              Nothing => pure [(ctx :< a, Nothing), (ctx, qTy)]
              Just mot => do
                kCheckTyK sig (ctx :< QuotTy a r) mot (Nd [] [])
                motiveAgrees (substTy mot (Ext Id q))
                pure [(ctx :< a, Just (substTy mot (Ext Wk (Class (CtxVar 0))))), (ctx, Just (QuotTy a r))]
          kids _ = kerr "kernel: proof node arity"
      in node sig ctx goal (\x => case x of QuotElim f q => Just [f, q]; _ => Nothing)
              (\xs => case xs of [f, q] => Just (QuotElim f q); _ => Nothing) kids [qf, qq]
    (CSquash q, _) =>
      node1 sig ctx goal (\x => case x of Squash u => Just u; _ => Nothing) Squash (ctx, Just TopTy) q
    (CQSort sg k qs, _) =>
      node sig ctx goal (\u => case u of
                                 QSort sg' k' es => if sg == sg' && k == k' then Just (toList es) else Nothing
                                 _ => Nothing)
           (\xs => Just (QSort sg k (cast xs)))
           (\es => pure (map (\i => (ctx, qSpineChildTy sg k (cast es) i)) (indices es))) qs
    (CQCtor sg k qs, _) =>
      node sig ctx goal (\u => case u of
                                 QCtor sg' k' es => if sg == sg' && k == k' then Just (toList es) else Nothing
                                 _ => Nothing)
           (\xs => Just (QCtor sg k (cast xs)))
           (\es => pure (map (\i => (ctx, qSpineChildTy sg k (cast es) i)) (indices es))) qs
    (CQElim sg k mm qm qs qw, _) =>
      -- children: the methods (typed by the carried motives, else
      -- undetermined), the index spine, the eliminee
      let nM = length qm
          split : List Elem -> Maybe (List Elem, List Elem, Elem)
          split xs = case reverse xs of
                       w :: rest => let ys = reverse rest in Just (take nM ys, drop nM ys, w)
                       _ => Nothing
          kids : List Elem -> KM (List (Ctx, Maybe Ty))
          kids xs = case split xs of
            Just (fs, es, w) => do
              mTys <- case mm of
                Nothing => pure (map (const Nothing) fs)
                Just mots => do
                  motiveAgrees (case qOrdinal QKSort sg k of
                                  Just o => fromMaybe TopTy (map (\m => substTy m (Ext (foldl Ext Id es) w)) (getAt o mots))
                                  Nothing => TopTy)
                  traverse (\cj => Just <$> liftQ (methodTy sg mots cj)) (qPositions QKPoint sg)
              pure (map (\t => (ctx, t)) mTys
                    ++ map (\i => (ctx, qSpineChildTy sg k (cast es) i)) (indices es)
                    ++ [(ctx, Just (QSort sg k (cast es)))])
            Nothing => kerr "kernel: proof node arity"
      in node sig ctx goal (\u => case u of
                                    QElim sg' k' fs es w =>
                                      if sg == sg' && k == k' && length fs == nM then Just (fs ++ toList es ++ [w]) else Nothing
                                    _ => Nothing)
              (\xs => case split xs of
                        Just (fs, es, w) => Just (QElim sg k fs (cast es) w)
                        Nothing => Nothing) kids (qm ++ qs ++ [qw])
    (COut q, _) =>
      node sig ctx goal (\x => case x of Out u => Just [u]; _ => Nothing)
           (\xs => case xs of [u] => Just (Out u); _ => Nothing)
           (\xs => case xs of
                     [u] => do mt <- headTy q u; pure [(ctx, mt)]
                     _ => kerr "kernel: proof node arity") [q]
    -- corec: the carrier is a code, the seed sits at it; the body is
    -- carrier-dependent (undetermined, like ⊎-elim's cases)
    (CCorec pf qa qf qx, _) =>
      node sig ctx goal (\u => case u of
                                 Corec pf' a f x => if pf == pf' then Just [a, f, x] else Nothing
                                 _ => Nothing)
           (\xs => case xs of [a, f, x] => Just (Corec pf a f x); _ => Nothing)
           (\xs => case xs of
                     [a, _, _] => pure [(ctx, Just UniverseTy), (ctx :< a, Nothing), (ctx, Just a)]
                     _ => kerr "kernel: proof node arity") [qa, qf, qx]
   where
    ||| the scrutinee's type: STATED by its proof when that proof
    ||| synthesises (a typed neutral: a spine over self leaves, ascribed
    ||| where a definition hides the shape), else the head's declared
    ||| type read off the side, β-only
    headTy : Prf -> Elem -> KM (Maybe Ty)
    headTy q u =
      if typedP q
        then do (_, _, t) <- kPrfS sig ctx q; pure (Just t)
        else inferHead sig ctx u

    needBoth : KM Elem
    needBoth = kerr "kernel: a type-directed proof needs both sides [\{show prf}]"

    ||| A synthesising leaf read against the goal: its stated equation
    ||| is at the position's type, and its sides meet the goal's under β.
    synthLeaf : KM Elem
    synthLeaf = do
      (a, b, t) <- kPrfS sig ctx prf
      case goal of
        GDir d x => do
          posTyCheck sig ctx mty x t
          sameB sig (if d then a else b) x
          pure (if d then b else a)
        GChk l r => do
          posTyCheck sig ctx mty l t
          sameB sig a l
          sameB sig b r
          pure l

    ||| A carried motive's instance at the scrutinee is the node's type.
    motiveAgrees : Ty -> KM ()
    motiveAgrees inst = case mty of
      Nothing => pure ()
      Just t => do
        ok <- tyAgree sig t inst
        if ok then pure ()
          else kerr "kernel: the carried motive does not instantiate to the position's type"

    indices : List a -> List Nat
    indices xs = go 0 xs
     where
      go : Nat -> List a -> List Nat
      go _ [] = []
      go i (_ :: rest) = i :: go (S i) rest

    ||| Π/Σ congruence: the domain at the classifier, the codomain under
    ||| the right side's domain.
    binderTy : (Elem -> Maybe (Elem, Elem)) -> (Elem -> Elem -> Elem) -> Prf -> Prf -> KM Elem
    binderTy shape rebuild qa qb = do
      cls <- compClassifier sig mty
      case goal of
        GDir d x => case shape x of
          Just (a, b) => do
            a' <- kPrfGo sig ctx qa (GDir d a) (Just cls)
            let dom = if d then a' else a
            b' <- kPrfGo sig (ctx :< dom) qb (GDir d b) (Just cls)
            pure (rebuild a' b')
          Nothing => kerr "kernel: proof shape does not match the side [\{show x}]"
        GChk l r => case (shape l, shape r) of
          (Just (a0, b0), Just (a1, b1)) => do
            ignore (kPrfGo sig ctx qa (GChk a0 a1) (Just cls))
            ignore (kPrfGo sig (ctx :< a1) qb (GChk b0 b1) (Just cls))
            pure l
          _ => kerr "kernel: proof shape does not match the sides\n  left:  \{show l}\n  right: \{show r}"
  ||| Is the type a PROPOSITION (a member of Ω)? Syntactically for the
  ||| Ω formers and the non-props among the formers; a neutral takes
  ||| the judgemental question: it infers at Ω (β-only, through the
  ||| given skeleton — the raw spelling first, since whnf can unfold a
  ||| prop spine into a stuck eliminator; a bare skeleton falls back to
  ||| the constant-motive Ω reading of an eliminator head).
  kIsProp : Sig -> Ctx -> Ty -> Skel -> KM Bool
  kIsProp sig ctx t sk =
    case t of
      Elem.EqTy _ _ _ => pure True
      Squash _ => pure True
      ZeroTy => pure False
      OneTy => pure False
      NatTy => pure False
      UniverseTy => pure False
      PropTy => pure False
      TopTy => pure False
      PiTy _ _ => pure False
      SigmaTy _ _ => pure False
      SumTy _ _ => pure False
      QuotTy _ _ => pure False
      NuTy _ => pure False
      _ => do
        ok <- atOmega t sk
        if ok then pure True else do
          t' <- kWhnfT sig t
          case t' of
            Elem.EqTy _ _ _ => pure True
            Squash _ => pure True
            _ => atOmega t' (Nd [] [])
   where
    -- an eliminator standing as a prop (a relator instance, a case
    -- split on a proposition) is read at the CONSTANT motive Ω (A1):
    -- its cases are props under their binders
    propSkel : Elem -> Skel
    propSkel (SumElim l r _) = Nd [PMotive PropTy (Nd [] [])] [propSkel l, propSkel r, Nd [] []]
    propSkel (NatElim z st _) = Nd [PMotive PropTy (Nd [] [])] [propSkel z, propSkel st, Nd [] []]
    propSkel (QuotElim f _) = Nd [PMotive PropTy (Nd [] []), PWD (PIrrel (Nd [] []))] [propSkel f, Nd [] []]
    propSkel _ = Nd [] []
    atOmega : Ty -> Skel -> KM Bool
    atOmega u usk = kTry (do
      ty <- kInferE sig ctx u (case usk of
                                 Nd [] [] => propSkel u
                                 _ => usk)
      ok <- tyAgree sig PropTy ty
      if ok then pure () else kerr "kernel: not at Ω")

  ||| The scrutinee exposure a node carries, applied to the inferred
  ||| type: the proof of inferred ≐ exposed is checked and the exposed
  ||| spelling continues (the kernel's whnf is β-only: a head hidden
  ||| behind a definition is reached only this way).
  scrutExpose : Sig -> Ctx -> Skel -> Ty -> KM Ty
  scrutExpose sig ctx sk ty = case takeP pScrut sk of
    Just ((tyX, c), _) => do kEqTy sig ctx c ty tyX; pure tyX
    Nothing => pure ty

  ||| Γ ⊢ e ⇐ A, kernel-side.
  export
  kCheckE : Sig -> Ctx -> Elem -> Ty -> Skel -> KM ()
  -- checking against 𝕍 IS type-formation checking (the dissolved
  -- type judgement)
  kCheckE sig ctx e TopTy sk = kCheckTyK sig ctx e sk
  kCheckE sig ctx e ty sk =
    case takeP pSwitch sk of
      Just (cert, sk') => do
        inferred <- kInferE sig ctx e sk'
        kEqTy sig ctx cert inferred ty
      Nothing => do
        -- head exposure: verified conversion to a rigid-headed type
        tyEff <- case takeP pExpose sk of
                   Just ((tyX, cert), _) => do kEqTy sig ctx cert ty tyX; pure tyX
                   Nothing => pure ty
        let ty = tyEff
        case e of
          PiIntro f => do
            ty' <- kWhnfT sig ty
            case ty' of
              PiTy a b => kCheckE sig (ctx :< a) f b (skelChild 0 sk)
              _ => kerr "kernel: λ checked at a non-Π type [\{show ty}]"
          SigmaIntro u v => do
            ty' <- kWhnfT sig ty
            case ty' of
              SigmaTy a b => do
                kCheckE sig ctx u a (skelChild 0 sk)
                kCheckE sig ctx v (substTy b (Ext Id u)) (skelChild 1 sk)
              _ => kerr "kernel: pair checked at a non-× type [\{show ty}]"
          Star =>
            -- el-eq-i over replay: ⋆ at an equality prop, the
            -- equation certified (refl-eq payload); otherwise the
            -- squash payloads below
            case takeP pReflEq sk of
              Just (cert, _) => do
                ty' <- kWhnfT sig ty
                case ty' of
                  Elem.EqTy l r t => kEqElem sig ctx cert l r t
                  _ => kerr "kernel: refl-eq payload at a non-equality prop"
              Nothing =>
               -- el-nu-coind: ⋆ at an equality prop over a ν-type,
               -- by COINDUCTION — invariant, endpoint proof, and
               -- one-step closure at the relator (the admissible
               -- rule; Foundation, coinductive NOTES)
               case takeP pNuCoind sk of
                Just ((r, skR, pw, skp, qw, skq), _) => do
                  ty' <- kWhnfT sig ty
                  case ty' of
                    Elem.EqTy l rhs ety => do
                      ety' <- kWhnfT sig ety
                      case ety' of
                        NuTy f => do
                          let nuT = NuTy f
                          -- the invariant is an Ω-relation
                          kCheckE sig (ctx :< nuT :< substTy nuT Wk) r PropTy skR
                          -- it holds at the endpoints (the prop is
                          -- the type — prop-lift)
                          kCheckE sig ctx pw (substElem r (Ext (Ext Id l) rhs)) skp
                          -- one-step closure under the generic hypotheses
                          let ctx3 = ctx :< nuT :< substTy nuT Wk :< r
                          let wk3 = Chain Wk (Chain Wk Wk)
                          let f3 = substPoly f wk3
                          let r3 = substElem r (under (under wk3))
                          kCheckE sig ctx3 qw
                            (liftPoly f3 r3 (Out (CtxVar 2)) (Out (CtxVar 1))) skq
                        _ => kerr "kernel: coinduction payload at an equation over a non-ν type"
                    _ => kerr "kernel: coinduction payload at a non-equality prop"
                Nothing =>
                -- el-squash-i: ⋆ : ∥A∥ carries its witness (an
                -- inhabitant of the squashee) as a payload
                 case takeP pSquashWit sk of
                  Just ((wit, witSk), _) => do
                    ty' <- kWhnfT sig ty
                    case ty' of
                      Squash sq => kCheckE sig ctx wit sq witSk
                      _ => kerr "kernel: ⋆ checked at a non-∥∥ type"
                  -- el-squash-e-prf: squash-elim carries its scrutinee
                  -- (inhabiting ∥A∥) and a body proving q[↑] under the
                  -- raw squashee A; the goal must be a PROP (the
                  -- rule's q : Ω premise)
                  Nothing => case takeP pSquashElim sk of
                    Just ((scrut, scrutSk, mexp, body, bodySk, goalSk), _) => do
                      scrutTy0 <- kInferE sig ctx scrut scrutSk
                      scrutTy <- case mexp of
                                   Nothing => pure scrutTy0
                                   Just (tyX, c) => do kEqTy sig ctx c scrutTy0 tyX; pure tyX
                      scrutTy' <- kWhnfT sig scrutTy
                      case scrutTy' of
                        Squash a => do
                          -- prop-ness of the goal AS WRITTEN (kIsProp
                          -- whnfs for itself; whnf-first would unfold
                          -- a ≤-spine into a stuck eliminator)
                          okQ <- kIsProp sig ctx ty goalSk
                          if okQ
                            then kCheckE sig (ctx :< a) body (substTy ty Wk) bodySk
                            else kerr "kernel: squash-elim checked at a non-prop goal"
                        _ => kerr "kernel: squash-elim scrutinee has a non-∥∥ type"
                    Nothing => kerr "kernel: ⋆ without its witness or squash-elim annotation"
          Inj1 a => do
            ty' <- kWhnfT sig ty
            case ty' of
              SumTy dom _ => kCheckE sig ctx a dom (skelChild 0 sk)
              _ => kerr "kernel: inj₁ checked at a non-⊎ type"
          Inj2 a => do
            ty' <- kWhnfT sig ty
            case ty' of
              SumTy _ cod => kCheckE sig ctx a cod (skelChild 0 sk)
              _ => kerr "kernel: inj₂ checked at a non-⊎ type"
          Class a => do
            ty' <- kWhnfT sig ty
            case ty' of
              QuotTy dom _ => kCheckE sig ctx a dom (skelChild 0 sk)
              _ => kerr "kernel: class checked at a non-quotient type [\{show e} : \{show ty}; skeleton \{show (length (skelPayloads sk))} payloads]"
          -- el-nu-i: the carried 𝔽 must be nf-identical to the
          -- expected ν-type's; carrier at 𝕌, coalgebra body over the
          -- carrier at the reflected observation type, seed at the
          -- carrier
          Corec p aC f x => do
            ty' <- kWhnfT sig ty
            case ty' of
              NuTy pT => do
                p' <- kJoinPoly sig p
                pT' <- kJoinPoly sig pT
                if p' == pT' then pure ()
                  else kerr "kernel: corec carries a different polynomial than its ν-type"
                kCheckE sig ctx aC UniverseTy (skelChild 0 sk)
                kCheckE sig (ctx :< aC) f (substTy (reflectPoly p aC) Wk) (skelChild 1 sk)
                kCheckE sig ctx x aC (skelChild 2 sk)
              _ => kerr "kernel: corec checked at a non-ν type"
          ZeroElim t => kCheckE sig ctx t ZeroTy (skelChild 0 sk)
          -- el-let (spec §8): definiens INFERRED (an intro-form
          -- definiens carries intro-ty on child 0), body under the
          -- value and its unfolding equation, checked at T[↑ ∘ ↑] —
          -- fully general, since T lives over Γ and the hypothesis
          -- makes (id, a, ⋆) ∘ (↑ ∘ ↑) ≐ id
          Let a b => do
            aTy <- kInferE sig ctx a (skelChild 0 sk)
            let hyp = Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk)
            kCheckE sig (ctx :< aTy :< hyp) b (weakenTyN 2 ty) (skelChild 1 sk)
          QCtor sgC c theta => do
            -- el-qiit-intro, SATURATED. The signature is the type's own —
            -- already validated where T was — and the term's must be
            -- identical to it under β. FULL β-join here (no δ: a
            -- carrier spelled through a definition arrives switched):
            -- the carried signature is compared structurally, so
            -- weak-head is not enough.
            ty' <- kJoinTy sig ty
            case ty' of
              QSort sgT srt es => do
                sgC' <- kJoinQSig sig sgC
                if sgC' /= sgT
                  then kerr "kernel: constructor of a different signature"
                  else pure ()
                entry <- case qEntry sgC' c of
                           Just x => pure x
                           Nothing => kerr "kernel: constructor position out of range"
                case qEntryKind entry of
                  QKPoint => pure ()
                  _ => kerr "kernel: not a point-constructor position"
                (tel, _, _) <- liftQ (reflTel sgC' (qwAt c) entry)
                let args = toList theta
                if length args /= length tel
                  then kerr "kernel: constructor spine not saturated"
                  else pure ()
                let goSpine : Nat -> List Elem -> KM ()
                    goSpine i [] = pure ()
                    goSpine i (a :: rest) = do
                      case telInst tel i (toList theta) of
                        Just aty => kCheckE sig ctx a aty (skelChild i sk)
                        Nothing => kerr "kernel: constructor spine out of range"
                      goSpine (S i) rest
                goSpine 0 args
                (wEnd, hd) <- liftQ (walkVals sgC' (qwAt c) entry args)
                (srt', idx) <- liftQ (pointHead sgC' wEnd hd)
                if srt' /= srt
                  then kerr "kernel: constructor of a different sort"
                  else pure ()
                idxN <- kJoinSubNorm sig idx
                esN <- kJoinSubNorm sig es
                if idxN == esN
                  then pure ()
                  else kerr "kernel: constructor indices do not match the type"
              _ => kerr "kernel: constructor checked at a non-QIIT type"
          _ => do
            -- no switch payload: inferred and expected agree under β
            -- (or by cumulativity). A δ-apart spelling arrives with a
            -- switch proof — from elaboration, from a reconstructed
            -- skeleton, or from the eliminator emission's method and
            -- eliminee binders
            inferred <- kInferE sig ctx e sk
            ok <- tyAgree sig ty inferred
            if ok then pure () else kerr "kernel: type mismatch without a switch certificate [\{show e}; skeleton payloads \{show (length (skelPayloads sk))}]\n  inferred: \{show inferred}\n  expected: \{show ty}"

  ||| Γ ⊢ e ⇒ A, kernel-side.
  export
  kInferE : Sig -> Ctx -> Elem -> Skel -> KM Ty
  kInferE sig ctx e sk =
    case takeP pIntroTy sk of
      Just ((ty, tySk), sk') => do
        kCheckTyK sig ctx ty tySk
        kCheckE sig ctx e ty sk'
        pure ty
      Nothing =>
        case e of
          CtxVar i =>
            case ctxLookup ctx i of
              Just ty => pure ty
              Nothing => kerr "kernel: variable out of bounds"
          SigVar x es =>
            kSigLookup sig x >>= \entryX => case entryX of
              Just (SigDef delta _ _ ty) => do
                kCheckSubstK sig ctx (toList es) (toList delta) (childSkels sk)
                pure (substTy ty (embed es))
              -- el-sig-decl: a declaration reference types like a def reference
              Just (SigDecl delta _ ty) => do
                kCheckSubstK sig ctx (toList es) (toList delta) (childSkels sk)
                pure (substTy ty (embed es))
              Just _ => kerr "kernel: signature name is not a term entry"
              -- the NAME is part of the message on purpose: a caller
              -- deciding whether this rejection is a missing
              -- dependency or a defect must be able to check the
              -- claim against its own Σ rather than trust the prose
              Nothing => kerr "kernel: unknown signature name '\{x}'"
          OneIntro => pure OneTy
          NatIntro0 => pure NatTy
          NatIntro1 t => do kCheckE sig ctx t NatTy (skelChild 0 sk); pure NatTy
          PiApp f a => do
            fTy <- kInferE sig ctx f (skelChild 0 sk) >>= scrutExpose sig ctx sk >>= kWhnfT sig
            case fTy of
              PiTy dom cod => do
                kCheckE sig ctx a dom (skelChild 1 sk)
                pure (substTy cod (Ext Id a))
              _ => kerr "kernel: applying a non-function [\{show e} : \{show fTy}]"
          SigmaElim1 t => do
            tTy <- kInferE sig ctx t (skelChild 0 sk) >>= scrutExpose sig ctx sk >>= kWhnfT sig
            case tTy of
              SigmaTy a _ => pure a
              _ => kerr "kernel: projecting a non-pair [\{show e} : \{show tTy}]"
          SigmaElim2 t => do
            tTy <- kInferE sig ctx t (skelChild 0 sk) >>= scrutExpose sig ctx sk >>= kWhnfT sig
            case tTy of
              SigmaTy _ b => pure (substTy b (Ext Id (SigmaElim1 t)))
              _ => kerr "kernel: projecting a non-pair [\{show e} : \{show tTy}]"
          -- el-nu-e: fully inference-driven, no motive payload
          Out t => do
            tTy <- kInferE sig ctx t (skelChild 0 sk) >>= scrutExpose sig ctx sk >>= kWhnfT sig
            case tTy of
              NuTy f => pure (reflectPoly f (Elem.NuTy f))
              _ => kerr "kernel: observing a non-ν element [\{show e} : \{show tTy}]"
          -- el-let (spec §8): let infers when its body does; the
          -- result substitutes the value and the ⋆-proof away
          Let a b => do
            aTy <- kInferE sig ctx a (skelChild 0 sk)
            let hyp = Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk)
            bTy <- kInferE sig (ctx :< aTy :< hyp) b (skelChild 1 sk)
            pure (substTy bTy (Ext (Ext Id a) Star))
          NatElim z st t =>
            case takeP pMotive sk of
              Just ((mot, motSk), _) => do
                kCheckTyK sig (ctx :< NatTy) mot motSk
                kCheckE sig ctx z (substTy mot (Ext Id NatIntro0)) (skelChild 0 sk)
                kCheckE sig (ctx :< NatTy :< mot) st
                  (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) (skelChild 1 sk)
                kCheckE sig ctx t NatTy (skelChild 2 sk)
                pure (substTy mot (Ext Id t))
              Nothing => kerr "kernel: ℕ-elim without a motive annotation"
          SumElim l r t =>
            -- el-sum-e: the motive arrives as a payload, the
            -- scrutinee's ⊎-type is inferred (like quot-elim's)
            case takeP pMotive sk of
              Just ((mot, motSk), _) => do
                tTy <- kInferE sig ctx t (skelChild 2 sk) >>= scrutExpose sig ctx sk >>= kWhnfT sig
                case tTy of
                  SumTy a b => do
                    kCheckTyK sig (ctx :< SumTy a b) mot motSk
                    kCheckE sig (ctx :< a) l
                      (substTy mot (Ext Wk (Inj1 (CtxVar 0)))) (skelChild 0 sk)
                    kCheckE sig (ctx :< b) r
                      (substTy mot (Ext Wk (Inj2 (CtxVar 0)))) (skelChild 1 sk)
                    pure (substTy mot (Ext Id t))
                  _ => kerr "kernel: ⊎-elim of a non-⊎ scrutinee"
              Nothing => kerr "kernel: ⊎-elim without a motive annotation"
          QuotElim f q =>
            case (takeP pMotive sk, takeP pWD sk) of
              (Just ((mot, motSk), _), Just (wd, _)) => do
                qTy <- kInferE sig ctx q (skelChild 1 sk) >>= scrutExpose sig ctx sk >>= kWhnfT sig
                case qTy of
                  QuotTy a r => do
                    kCheckTyK sig (ctx :< QuotTy a r) mot motSk
                    kCheckE sig (ctx :< a) f
                      (substTy mot (Ext Wk (Class (CtxVar 0)))) (skelChild 0 sk)
                    -- an Ω-VALUED motive closes well-definedness
                    -- outright: the equation's sides inhabit a prop
                    -- instance (el-prf-prop; the ElimP rationale).
                    -- Testing the MOTIVE, not its instantiation — the
                    -- instance can be a stuck eliminator prop-ness
                    -- cannot be read off (Prf's head used to carry it)
                    mIsP <- kIsProp sig (ctx :< QuotTy a r) mot motSk
                    if mIsP then pure () else do
                      let wk3 = Chain Wk (Chain Wk Wk)
                      kEqElem sig (ctx :< a :< substTy a Wk :< r) wd
                        (substElem f (Ext wk3 (CtxVar 2)))
                        (substElem f (Ext wk3 (CtxVar 1)))
                        (substTy mot (Ext wk3 (Class (CtxVar 2))))
                    pure (substTy mot (Ext Id q))
                  _ => kerr "kernel: quot-elim of a non-quotient"
              _ => kerr "kernel: quot-elim without motive/well-definedness annotations"
          QSort sg k es => do
            -- code-qiit: SMALL signatures only
            kQSigCheck sig ctx sg
            kQSigSmall sig ctx sg
            kQSortSpine sig ctx sg k es sk
            pure UniverseTy
          QElim sg k mths es w =>
            -- el-qiit-elim over mot/dalg/eprob: the methods are carried
            -- by the term (β reads them), the motives arrive in the
            -- skeleton (PQMotives) and the coherences as proofs (PQCoh)
            case (takeP pQMotives sk, takeP pQCoh sk) of
              (Nothing, _) => kerr "kernel: QIIT eliminator without motives"
              (_, Nothing) => kerr "kernel: QIIT eliminator without coherence certificates"
              (Just ((mots, motSks), _), Just (cohs, sk')) => do
                kQSigCheck sig ctx sg
                sortE <- case qEntry sg k of
                           Just x => pure x
                           Nothing => kerr "kernel: eliminator sort out of range"
                case qEntryKind sortE of
                  QKSort => pure ()
                  _ => kerr "kernel: eliminator at a non-sort position"
                let sortPs = qPositions QKSort sg
                let pointPs = qPositions QKPoint sg
                let eqPs = qPositions QKEq sg
                if length mots /= length sortPs
                  then kerr "kernel: motive count mismatch" else pure ()
                if length mths /= length pointPs
                  then kerr "kernel: method count mismatch" else pure ()
                if length cohs /= length eqPs
                  then kerr "kernel: coherence count mismatch" else pure ()
                let goMotives : List Nat -> List (Ty, Skel) -> KM ()
                    goMotives [] [] = pure ()
                    goMotives (sj :: sjs) ((mot, motSk) :: rest) = do
                      sjE <- case qEntry sg sj of
                               Just x => pure x
                               Nothing => kerr "kernel: sort out of range"
                      (tel, wEnd, _) <- liftQ (reflTel sg (qwAt sj) sjE)
                      let mctx = foldl (:<) ctx tel
                      let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
                      kCheckTyK sig (mctx :< selfTy) mot motSk
                      goMotives sjs rest
                    goMotives _ _ = kerr "kernel: motive count mismatch"
                -- the node's child skeletons: the methods, then the
                -- index spine, then the eliminee (a method that is a
                -- variable whose declared type spells the displayed
                -- type otherwise carries its switch there)
                let nM = length pointPs
                let goMethods : Nat -> List Nat -> List Elem -> KM ()
                    goMethods j [] [] = pure ()
                    goMethods j (cj :: cjs) (m :: rest) = do
                      mty <- liftQ (methodTy sg mots cj)
                      kCheckE sig ctx m mty (skelChild j sk')
                      goMethods (S j) cjs rest
                    goMethods _ _ _ = kerr "kernel: method count mismatch"
                let goCoherences : List Nat -> List Prf -> KM ()
                    goCoherences [] [] = pure ()
                    goCoherences (ej :: ejs) (coh :: rest) = do
                      (dtel, _, lhs, rhs, cty) <- liftQ (coherenceAt sg mots mths ej)
                      kEqElem sig (foldl (:<) ctx dtel) coh lhs rhs cty
                      goCoherences ejs rest
                    goCoherences _ _ = kerr "kernel: coherence count mismatch"
                goMotives sortPs (zip mots (motSks ++ replicate (length mots) (Nd [] [])))
                goMethods 0 pointPs mths
                goCoherences eqPs cohs
                let skRest = case sk' of
                               Nd ps cs => Nd ps (drop nM cs)
                kQSortSpine sig ctx sg k es skRest
                kCheckE sig ctx w (QSort sg k es) (skelChild (length (toList es)) skRest)
                o <- case qOrdinal QKSort sg k of
                       Just x => pure x
                       Nothing => kerr "kernel: eliminator sort ordinal"
                motK <- case getAt o mots of
                          Just m => pure m
                          Nothing => kerr "kernel: eliminator motive missing"
                pure (substTy motK (Ext (foldl Ext Id (toList es)) w))
          Elem.ZeroTy => pure UniverseTy
          Elem.OneTy => pure UniverseTy
          Elem.NatTy => pure UniverseTy
          Elem.PiTy a b => do
            kCheckE sig ctx a UniverseTy (skelChild 0 sk)
            kCheckE sig (ctx :< a) b UniverseTy (skelChild 1 sk)
            pure UniverseTy
          Elem.SigmaTy a b => do
            kCheckE sig ctx a UniverseTy (skelChild 0 sk)
            kCheckE sig (ctx :< a) b UniverseTy (skelChild 1 sk)
            pure UniverseTy
          Elem.SumTy a b => do
            kCheckE sig ctx a UniverseTy (skelChild 0 sk)
            kCheckE sig ctx b UniverseTy (skelChild 1 sk)
            pure UniverseTy
          -- code-nu: the polynomial's pieces, skeleton children in
          -- binder order (every polynomial is small)
          Elem.NuTy f => do
            _ <- kCheckPolyK sig ctx f 0 sk
            pure UniverseTy
          QuotTy a r => do
            kCheckE sig ctx a UniverseTy (skelChild 0 sk)
            kCheckE sig (ctx :< a :< substTy a Wk) r PropTy (skelChild 1 sk)
            pure UniverseTy
          Squash t => do
            kCheckTyK sig ctx t (skelChild 0 sk)
            pure PropTy
          Elem.EqTy l r t => do
            -- code-eq: the equality PROP — the ambient is an arbitrary
            -- TYPE or 𝕍 itself (type equality is a proposition; the
            -- sides then check as types via kCheckE's TopTy routing)
            case t of
              TopTy => pure ()
              _ => kCheckTyK sig ctx t (skelChild 2 sk)
            kCheckE sig ctx l t (skelChild 0 sk)
            kCheckE sig ctx r t (skelChild 1 sk)
            pure PropTy
          _ => kerr "kernel: term not inferable (missing ascription annotation)"
   where
    childSkels : Skel -> List Skel
    childSkels (Nd _ cs) = cs

  ||| Γ ⊦ 𝔽 poly, kernel-side (Foundation's poly-* rules): each
  ||| embedded code at 𝕌 with its skeleton child, children indexed in
  ||| binder order across the whole polynomial; returns the next child
  ||| index.
  kCheckPolyK : Sig -> Ctx -> Poly -> (i : Nat) -> Skel -> KM Nat
  kCheckPolyK sig ctx PHole        i sk = pure i
  kCheckPolyK sig ctx (PConst a)   i sk = do
    kCheckE sig ctx a UniverseTy (skelChild i sk)
    pure (S i)
  kCheckPolyK sig ctx (PProd f g)  i sk = do
    i' <- kCheckPolyK sig ctx f i sk
    kCheckPolyK sig ctx g i' sk
  kCheckPolyK sig ctx (PSum f g)   i sk = do
    i' <- kCheckPolyK sig ctx f i sk
    kCheckPolyK sig ctx g i' sk
  kCheckPolyK sig ctx (PSigma a f) i sk = do
    kCheckE sig ctx a UniverseTy (skelChild i sk)
    kCheckPolyK sig (ctx :< a) f (S i) sk
  kCheckPolyK sig ctx (PPi a f)    i sk = do
    kCheckE sig ctx a UniverseTy (skelChild i sk)
    kCheckPolyK sig (ctx :< a) f (S i) sk

  ||| SMALLNESS (code-qiit's side condition), kernel-side: judgemental
  ||| now that El and Prf are retired — every external Π domain typed
  ||| or typed at 𝕌, checked in its own external context.
  export
  kQSigSmall : Sig -> Ctx -> QSig -> KM ()
  kQSigSmall sig ctx sg = go sg
   where
    small : Ctx -> Ty -> KM Bool
    small ectx a = do
      u <- kTry (kCheckE sig ectx a UniverseTy (Nd [] []))
      if u then pure True else kTry (kCheckE sig ectx a PropTy (Nd [] []))
    walk : Ctx -> QTy -> KM ()
    walk ectx (QPiExt a rest) = do
      ok <- small ectx a
      if ok then walk (ectx :< a) rest
        else kerr "kernel: universe code for a LARGE signature (code-qiit requires smallness)"
    walk ectx (QPiInd _ rest) = walk ectx rest
    walk ectx _ = pure ()
    go : QSig -> KM ()
    go [] = pure ()
    go (e :: rest) = do walk ctx e; go rest

  ||| Γ ⊢ A type, kernel-side.
  export
  kCheckTyK : Sig -> Ctx -> Ty -> Skel -> KM ()
  kCheckTyK sig ctx ZeroTy _ = pure ()
  kCheckTyK sig ctx OneTy _ = pure ()
  kCheckTyK sig ctx NatTy _ = pure ()
  kCheckTyK sig ctx UniverseTy _ = pure ()
  kCheckTyK sig ctx (PiTy a b) sk = do
    kCheckTyK sig ctx a (skelChild 0 sk)
    kCheckTyK sig (ctx :< a) b (skelChild 1 sk)
  kCheckTyK sig ctx (SigmaTy a b) sk = do
    kCheckTyK sig ctx a (skelChild 0 sk)
    kCheckTyK sig (ctx :< a) b (skelChild 1 sk)
  kCheckTyK sig ctx (SumTy a b) sk = do
    kCheckTyK sig ctx a (skelChild 0 sk)
    kCheckTyK sig ctx b (skelChild 1 sk)
  kCheckTyK sig ctx PropTy _ = pure ()
  -- the Ω formers are types by prop-lift (code-eq / code-squash)
  kCheckTyK sig ctx t@(Elem.EqTy _ _ _) sk = kCheckE sig ctx t PropTy sk
  kCheckTyK sig ctx t@(Squash _) sk = kCheckE sig ctx t PropTy sk
  kCheckTyK sig ctx (QuotTy a r) sk = do
    kCheckTyK sig ctx a (skelChild 0 sk)
    kCheckE sig (ctx :< a :< substTy a Wk) r PropTy (skelChild 1 sk)
  kCheckTyK sig ctx (QSort sg k es) sk = do
    -- ty-qiit: the signature and the index spine against its arity
    kQSigCheck sig ctx sg
    kQSortSpine sig ctx sg k es sk
  kCheckTyK sig ctx (NuTy f) sk = do
    -- ty-nu: the polynomial's pieces, skeleton children in binder order
    _ <- kCheckPolyK sig ctx f 0 sk
    pure ()
  kCheckTyK sig ctx (SigVar x es) sk =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ TopTy) =>
        kCheckSubstK sig ctx (toList es) (toList delta) (childSkels' sk)
      Just (SigDecl delta _ TopTy) =>
        kCheckSubstK sig ctx (toList es) (toList delta) (childSkels' sk)
      -- CUMULATIVITY: a 𝕌- or Ω-classified reference is a code or a
      -- prop — a type either way (code-lift / prop-lift)
      _ => do
        ok <- kTry (kCheckE sig ctx (SigVar x es) UniverseTy sk)
        if ok then pure () else kCheckE sig ctx (SigVar x es) PropTy sk
   where
    childSkels' : Skel -> List Skel
    childSkels' (Nd _ cs) = cs
  -- CUMULATIVITY (code-lift / prop-lift): anything else in type
  -- position must be a CODE or a PROP — check at 𝕌, then at Ω
  -- (𝕍 itself still fails both)
  kCheckTyK sig ctx t sk = do
    ok <- kTry (kCheckE sig ctx t UniverseTy sk)
    if ok then pure () else kCheckE sig ctx t PropTy sk

  ||| Γ ⊦ 𝒮 qsig — Foundation's qctx/qty/qtm read as a syntax-directed
  ||| algorithm, for the fragment the elaborator emits: SORT entries
  ||| take EXTERNAL-only index arities; constructor entries take
  ||| external and inductive binders freely; codes are sort heads
  ||| applied to external arguments; no equation-code binders, no
  ||| external λ (first-order fragment). Rejecting the rest is
  ||| incompleteness, never unsoundness. Embedded Nova pieces are
  ||| checked with empty skeletons (neutral-checkable in the emitted
  ||| fragment).
  kQSigCheck : Sig -> Ctx -> QSig -> KM ()
  kQSigCheck sig ctx sg = goEntries 0 sg
   where
    goEntries : Nat -> List QTy -> KM ()
    goEntries k [] = pure ()
    goEntries k (e :: rest) = do kQEntry sig ctx sg k e; goEntries (S k) rest

  ||| Resolve a ToS entry reference at (scope k, b inductive binders).
  kQEntryOf : (k : Nat) -> (b : Nat) -> Nat -> KM Nat
  kQEntryOf k b i =
    if i < b then kerr "kernel: qiit binder used as an entry"
    else let j = minus i b in
         if j < k then pure (minus (minus k 1) j)
         else kerr "kernel: qiit entry reference out of scope"

  ||| Transport a ToS piece written inside entry `src` under `srcB`
  ||| inductive binders to the walk's current coordinates (scope k,
  ||| depth b): external pieces through `sub`, the src's inductive
  ||| binders through `ivals` (their instantiations, innermost first,
  ||| already at the current coordinates).
  kQRebase : QSig -> (k, b : Nat) -> (src, srcB : Nat) -> Sub -> List QTm -> QTm -> KM QTm
  kQRebase sg k b src srcB sub ivals (QEqC _ _ _) =
    kerr "kernel: equation code in a domain/argument position (first-order fragment)"
  kQRebase sg k b src srcB sub ivals c =
    case qChain c of
      Nothing => kerr "kernel: qiit code is not an application chain"
      Just (h, args) => do
        hd <- if h < srcB
                then case (args, getAt h ivals) of
                       ([], Just t) => pure t
                       ([], Nothing) => kerr "kernel: internal — rebase environment out of sync"
                       _ => kerr "kernel: applied qiit binder (first-order fragment)"
                else do
                  let j = minus h srcB
                  posAbs <- if j < src then pure (minus (minus src 1) j)
                            else kerr "kernel: qiit entry reference out of scope"
                  pure (QVar (b + minus (minus k 1) posAbs))
        args' <- traverse (\a => case a of
                   Left e => pure (Left (substElem e sub))
                   Right t2 => Right <$> kQRebase sg k b src srcB sub ivals t2) args
        let app : QTm -> Either Elem QTm -> QTm
            app f (Left e) = QAppE f e
            app f (Right t2) = QAppI f t2
        pure (foldl app hd args')

  ||| Check a sort-headed CODE at (scope k, external zone ectx with
  ||| extD external binders, b inductive binders with domain codes
  ||| benv): the sort's binder telescope is walked against the
  ||| arguments — external ones checked as Nova elements, INDUCTIVE
  ||| ones (inductive-inductive sort indices) checked at their rebased
  ||| domain codes.
  kQCode : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> List QTm -> QTm -> KM ()
  kQCode sig ctx sg k ectx extD b benv (QEqC _ _ _) =
    kerr "kernel: equation code in a binder position (first-order fragment)"
  kQCode sig ctx sg k ectx extD b benv code =
    case qChain code of
      Nothing => kerr "kernel: qiit code is not an application chain"
      Just (h, args) => do
        pos <- kQEntryOf k b h
        sortE <- case qEntry sg pos of
                   Just e => pure e
                   Nothing => kerr "kernel: qiit entry out of range"
        case qEntryKind sortE of
          QKSort => pure ()
          _ => kerr "kernel: qiit code head is not a sort"
        hd <- kQArgsWalk sig ctx sg k ectx extD b benv pos sortE args
        case hd of
          QU => pure ()
          _ => kerr "kernel: internal — sort entry with a non-U head"

  ||| Walk entry `src`'s binder telescope against an argument chain —
  ||| external arguments checked as Nova elements at their instantiated
  ||| domains, inductive arguments at their rebased domain codes —
  ||| returning the entry's HEAD rebased to the current coordinates
  ||| (QU for sorts, the result code for point constructors).
  kQArgsWalk : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> (benv : List QTm)
            -> (src : Nat) -> QTy -> List (Either Elem QTm) -> KM QTy
  kQArgsWalk sig ctx sg k ectx extD b benv src entry args0 =
    goArgs 0 (wkSubN extD) [] entry args0
   where
    goArgs : (srcB : Nat) -> Sub -> List QTm -> QTy -> List (Either Elem QTm) -> KM QTy
    goArgs srcB sub ivals (QPiExt a rest) (Left e :: as) = do
      kCheckE sig ectx e (substTy a sub) (Nd [] [])
      goArgs srcB (Ext sub e) ivals rest as
    goArgs srcB sub ivals (QPiInd u rest) (Right t' :: as) = do
      expected <- kQRebase sg k b src srcB sub ivals u
      kQTmAt sig ctx sg k ectx extD b benv expected t'
      goArgs (S srcB) sub (t' :: ivals) rest as
    goArgs srcB sub ivals (QEl code) [] =
      QEl <$> kQRebase sg k b src srcB sub ivals code
    goArgs srcB sub ivals QU [] = pure QU
    goArgs _ _ _ _ _ = kerr "kernel: qiit spine mismatch (kind or saturation)"

  ||| Infer the CODE of a qiit term (a binder, or a saturated point-
  ||| constructor chain), checking its arguments along the way.
  kQTmInfer : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> (benv : List QTm) -> QTm -> KM QTm
  kQTmInfer sig ctx sg k ectx extD b benv t =
    case qChain t of
      Nothing => kerr "kernel: qiit term is not an application chain (first-order fragment)"
      Just (h, args) =>
        if h < b
          then case (args, getAt h benv) of
                 ([], Just c) => pure c
                 ([], Nothing) => kerr "kernel: internal — qiit binder environment out of sync"
                 _ => kerr "kernel: applied qiit binder (first-order fragment)"
          else do
            pos <- kQEntryOf k b h
            ctorE <- case qEntry sg pos of
                       Just e => pure e
                       Nothing => kerr "kernel: qiit entry out of range"
            case qEntryKind ctorE of
              QKPoint => pure ()
              _ => kerr "kernel: qiit term headed by a non-constructor"
            hd <- kQArgsWalk sig ctx sg k ectx extD b benv pos ctorE args
            case hd of
              QEl code => pure code
              _ => kerr "kernel: internal — point entry with a non-El head"

  ||| Check a qiit term against an expected code (both at the current
  ||| coordinates); comparison is syntactic after normalizing the
  ||| embedded Nova pieces.
  kQTmAt : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> List QTm -> QTm -> QTm -> KM ()
  kQTmAt sig ctx sg k ectx extD b benv expected t = do
    inferred <- kQTmInfer sig ctx sg k ectx extD b benv t
    i' <- kQTm sig inferred
    e' <- kQTm sig expected
    if i' == e' then pure ()
      else kerr "kernel: qiit term at the wrong sort"

  ||| Check one signature entry (position k).
  kQEntry : Sig -> Ctx -> QSig -> (k : Nat) -> QTy -> KM ()
  kQEntry sig ctx sg k entry = walk ctx 0 0 [] entry
   where
    walk : Ctx -> (extD : Nat) -> (b : Nat) -> List QTm -> QTy -> KM ()
    walk ectx extD b benv (QPiExt a rest) = do
      kCheckTyK sig ectx a (Nd [] [])
      walk (ectx :< a) (S extD) b (map (\c => substQTm c Wk) benv) rest
    walk ectx extD b benv (QPiInd u rest) = do
      kQCode sig ctx sg k ectx extD b benv u
      walk ectx extD (S b) (qtmShift 1 u :: map (qtmShift 1) benv) rest
    walk ectx extD b benv QU = pure ()
    walk ectx extD b benv (QEl (QEqC l r u)) = do
      kQCode sig ctx sg k ectx extD b benv u
      kQTmAt sig ctx sg k ectx extD b benv u l
      kQTmAt sig ctx sg k ectx extD b benv u r
    walk ectx extD b benv (QEl code) = kQCode sig ctx sg k ectx extD b benv code

  ||| Check a sort application's index spine against the sort's arity.
  kQSortSpine : Sig -> Ctx -> QSig -> Nat -> SubNorm -> Skel -> KM ()
  kQSortSpine sig ctx sg k es sk = do
    sortE <- case qEntry sg k of
               Just e => pure e
               Nothing => kerr "kernel: sort position out of range"
    case qEntryKind sortE of
      QKSort => pure ()
      _ => kerr "kernel: not a sort position"
    (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
    let args = toList es
    if length args /= length tel
      then kerr "kernel: sort index spine length mismatch"
      else pure ()
    goIdx 0 args tel
   where
    goIdx : Nat -> List Elem -> List Ty -> KM ()
    goIdx i [] _ = pure ()
    goIdx i (e :: rest) tel = do
      case telInst tel i (toList es) of
        Just ty => kCheckE sig ctx e ty (skelChild i sk)
        Nothing => kerr "kernel: sort index out of range"
      goIdx (S i) rest tel

  kCheckSubstK : Sig -> Ctx -> List Elem -> List Ty -> List Skel -> KM ()
  kCheckSubstK sig ctx es delta sks =
    if length es /= length delta
      then kerr "kernel: substitution length mismatch"
      else go 0 es delta
   where
    go : Nat -> List Elem -> List Ty -> KM ()
    go i [] [] = pure ()
    go i (e :: erest) (ty :: tyrest) = do
      let pre = take i es
      kCheckE sig ctx e (substTy ty (embed (cast pre)))
        (fromMaybe (Nd [] []) (getAt i sks))
      go (S i) erest tyrest
    go _ _ _ = kerr "kernel: substitution length mismatch"

-- ===== Item entry points =====

public export
record KDefArt where
  constructor MkKDefArt
  dname : String
  tele : List (Ty, Skel)
  dty : Ty
  dtySkel : Skel
  body : Elem
  bodySkel : Skel

public export
record KTyDefArt where
  constructor MkKTyDefArt
  tname : String
  ttele : List (Ty, Skel)
  tty : Ty
  ttySkel : Skel

kTele : Sig -> Ctx -> List (Ty, Skel) -> KM Ctx
kTele sig ctx [] = pure ctx
kTele sig ctx ((ty, sk) :: rest) = do
  kCheckTyK sig ctx ty sk
  kTele sig (ctx :< ty) rest

||| Decidable prop-ness probe for callers outside the fuel monad
||| (the elaborator's preferPrf/isPropTy): True iff the type is a
||| PROPOSITION — kIsProp's discipline: the raw spelling inferred at
||| Ω through the given skeleton first (a bare one reads an eliminator
||| head at the constant motive Ω), then whnf.
export
kIsPropB : Sig -> Nat -> Ctx -> Ty -> Skel -> Bool
kIsPropB sig fuel ctx t sk =
  case runKM (kIsProp sig ctx t sk) fuel of
    Right (b, _) => b
    Left _ => False

||| Decidable smallness probe for callers outside the fuel monad
||| (the elaborator's data-item emitter): True iff every external Π
||| domain of the signature checks at 𝕌 or at Ω — over the
||| given ambient context (a parameterized literal's externals mention
||| the parameter variables).
export
kQSigSmallB : Sig -> Nat -> Ctx -> QSig -> Bool
kQSigSmallB sig fuel ctx sg =
  case runKM (kQSigSmall sig ctx sg) fuel of
    Right _ => True
    Left _ => False

||| Infer the type of a BARE (skeleton-free) core — recovery's
||| capture-typing source. Nothing when the core is an intro form
||| (not inferable) or fails to type against this Σ; the caller
||| treats absence as "no derived equation", never as an error.
export
kInferBare : Sig -> Nat -> Ctx -> Elem -> Maybe Ty
kInferBare sig fuel ctx e =
  case runKMLiberal (kInferE sig ctx e (Nd [] [])) fuel of
    Right (t, _) => Just t
    Left _ => Nothing

||| Check a definition item from the kernel's own Σ; return the entry
||| to extend it with.
export
kCheckDefItem : Sig -> Nat -> KDefArt -> Either KErr SigEntry
kCheckDefItem sig fuel art =
  map fst $ runKM (do
    ctx <- kTele sig [<] art.tele
    kCheckTyK sig ctx art.dty art.dtySkel
    kCheckE sig ctx art.body art.dty art.bodySkel
    pure (SigDef ctx art.dname art.body art.dty)) fuel

export
kCheckTyDefItem : Sig -> Nat -> KTyDefArt -> Either KErr SigEntry
kCheckTyDefItem sig fuel art =
  map fst $ runKM (do
    ctx <- kTele sig [<] art.ttele
    kCheckTyK sig ctx art.tty art.ttySkel
    -- a type definition is a definition at the classifier 𝕍 (sig-def
    -- at A = 𝕍)
    pure (SigDef ctx art.tname art.tty TopTy)) fuel

-- ===== Entry points =====

export
kCheckEqElem : Sig -> Ctx -> Nat -> Prf -> Elem -> Elem -> Ty -> Either KErr ()
kCheckEqElem sig ctx fuel cert l r ty =
  map fst (runKM (kEqElem sig ctx cert l r ty) fuel)

export
kCheckEqTy : Sig -> Ctx -> Nat -> Prf -> Ty -> Ty -> Either KErr ()
kCheckEqTy sig ctx fuel cert a b =
  map fst (runKM (kEqTy sig ctx cert a b) fuel)
