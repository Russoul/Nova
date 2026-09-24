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
import Control.Monad.State

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT
import Nova.Kernel.Derivation
import Nova.Profile

%default covering

-- ===== Proof terms =====

mutual
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
  |||   ⇒ (synthesis)  a licence leaf, with symmetry and
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

||| The first computation, or — when it fails — the second applied to
||| its error (a rethrow with context).
export
kCatch : KM a -> (KErr -> KM a) -> KM a
kCatch (MkKM f) h = MkKM $ \st => case f st of
  Right v => Right v
  Left e => case h e of
              MkKM g => g st

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
export
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
    -- cumulativity at 𝕍: a 𝕌 code (code-lift-eq) or an Ω code
    -- (prop-lift-eq — a stated Ω equation's sides ARE props, the
    -- lift's side condition established by the statement itself)
    if expN == gotN || (expN == TopTy && (gotN == UniverseTy || gotN == PropTy))
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
  -- A congruence node that STATES its equation (a spine over a typed
  -- head, §4) is also a leaf: when the goal's sides lack the node's
  -- shape, its stated sides meet them under β at the position's type
  -- — how a derived component equation is read (the predecessor
  -- congruence [pred] ⟨h⟩ at x ≐ y: pred (S x) joins to x)
  kPrfGo sig ctx prf goal@(GChk l r) mty =
    if isJust (congChildren prf)
      then let asNode = if dirP True prf
                          then kOrElse (do x <- kPrfGo sig ctx prf (GDir True l) mty
                                           sameB sig x r
                                           pure l)
                                       (kPrfGoAt sig ctx prf goal mty)
                          else kPrfGoAt sig ctx prf goal mty
           in if synthP prf then kOrElse asNode (stated sig ctx prf goal mty) else asNode
      else kPrfGoAt sig ctx prf goal mty
  kPrfGo sig ctx prf goal@(GDir _ _) mty =
    if isJust (congChildren prf) && synthP prf
      then kOrElse (kPrfGoAt sig ctx prf goal mty) (stated sig ctx prf goal mty)
      else kPrfGoAt sig ctx prf goal mty

  ||| A stating proof read against the goal: its equation is at the
  ||| position's type, and its sides meet the goal's under β.
  stated : Sig -> Ctx -> Prf -> Goal -> Maybe Ty -> KM Elem
  stated sig ctx prf goal mty = do
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

-- ===== Derivations (docs/NovaKernel.txt §10): the kernel on proof terms alone =====
--
-- A derivation is read in three ways: ⇒ (dInfer: the equation and
-- type it states), ⇐ T (dCheck: the type known, the sides
-- synthesized) and ▷ l ≐ r : T (dAt: the sides given — for a
-- derivation that synthesizes, checking followed by a β-join
-- comparison; for one that does not, the decomposition of the given
-- sides by shape, §10.5), with the directional run → (dDir) inside
-- transitivity. No term enters beside the derivation: the element is
-- its erasure, computed by the readings.

mutual
 ||| A derivation that STATES its equation and type (the ⇒ reading is
 ||| defined on it).
 dSynth : Drv -> Bool
 dSynth (DVar _) = True
 dSynth (DRef _ _) = True
 dSynth DUnit = True
 dSynth DZero = True
 dSynth DZeroTy = True
 dSynth DOneTy = True
 dSynth DNatTy = True
 dSynth DUniverse = True
 dSynth DProp = True
 dSynth DTop = True
 dSynth (DRefl _) = True
 dSynth (DPath _ _ _) = True
 dSynth (DDelta _ _) = True
 dSynth DReflx = False
 dSynth (DSym p) = dSynth p
 dSynth (DTrans p q) = (dSynth p && dDirable True q) || (dSynth q && dDirable False p)
 dSynth (DTransAt p _ q) = (dSynth p && dDirable True q) || (dSynth q && dDirable False p)
 dSynth (DDeltaAll _) = False
 dSynth (DIrrel _) = False
 dSynth (DEtaPi _) = False
 dSynth (DEtaSigma _ _) = False
 dSynth (DQuotWit _) = False
 dSynth (DQuotWitPrf _) = False
 dSynth (DInj _) = False
 dSynth (DPropExt _ _) = False
 dSynth (DPrfCong _ _ _) = False
 dSynth (DConv p (Just _) _) = dSynth p
 dSynth (DConv p Nothing _) = dSynth p
 dSynth (DAt _ _ _) = True
 -- an ascription states: its inner is CHECKED at the annotation (a
 -- checking-mode intro, a switch, a stating derivation), unless the
 -- inner is a proof that only reads against given sides
 dSynth (DAscribe p _ _) = dCheckable p
 dSynth (DSubst p _) = dSynth p
 dSynth (DLam (Just _) p) = dSynth p
 dSynth (DLam Nothing _) = False
 dSynth (DPair (Just _) u v) = dSynth u && dSynth v
 dSynth (DPair Nothing _ _) = False
 dSynth (DInj1 (Just _) p) = dSynth p
 dSynth (DInj1 Nothing _) = False
 dSynth (DInj2 (Just _) p) = dSynth p
 dSynth (DInj2 Nothing _) = False
 dSynth (DClass (Just _) p) = dSynth p
 dSynth (DClass Nothing _) = False
 dSynth (DSuc p) = dSynth p
 dSynth (DCtor _ _ ps) = all dSynth ps
 dSynth (DCorec _ a f x) = dSynth a && dSynth f && dSynth x
 dSynth (DLet a b) = dSynth a && dSynth b
 dSynth (DStar (Just _) _) = True
 dSynth (DStar Nothing _) = False
 dSynth (DSq p) = dSynth p
 dSynth (DSquashElim (Just _) e b) = dSynth e && dSynth b
 dSynth (DSquashElim Nothing _ _) = False
 dSynth (DCoind (Just _) _ _ _) = True
 dSynth (DCoind Nothing _ _ _) = False
 dSynth (DZeroElim (Just _) p) = dSynth p
 dSynth (DZeroElim Nothing _) = False
 dSynth (DNatElim (Just _) z s n) = dSynth z && dSynth s && dSynth n
 dSynth (DNatElim Nothing _ _ _) = False
 dSynth (DSumElim (Just _) l r t) = dSynth l && dSynth r && dSynth t
 dSynth (DSumElim Nothing _ _ _) = False
 dSynth (DQuotElim (Just _) _ f q) = dSynth f && dSynth q
 dSynth (DQuotElim Nothing _ _ _) = False
 dSynth (DQElim _ _ _ _ ms es w) = all dSynth ms && all dSynth es && dSynth w
 dSynth (DOut p) = dSynth p
 dSynth (DApp f a) = dSynth f && dSynth a
 dSynth (DProj1 p) = dSynth p
 dSynth (DProj2 p) = dSynth p
 dSynth (DPi a b) = dSynth a && dSynth b
 dSynth (DSigma a b) = dSynth a && dSynth b
 dSynth (DSum a b) = dSynth a && dSynth b
 dSynth (DEq l r t) = dSynth l && dSynth r && dSynth t
 dSynth (DQuot a r) = dSynth a && dSynth r
 dSynth (DSquash p) = dSynth p
 dSynth (DNu _) = True
 dSynth (DSort _ _ ps) = all dSynth ps

 ||| Can the derivation be CHECKED at a known type — it states, or it
 ||| is a checking-mode form (an intro without its annotation, an
 ||| eliminator without its motive, a switch, a type former)?
 dCheckable : Drv -> Bool
 dCheckable p = if dSynth p then True else case p of
   DLam Nothing q => dCheckable q
   DPair Nothing u v => dCheckable u && dCheckable v
   DInj1 Nothing q => dCheckable q
   DInj2 Nothing q => dCheckable q
   DClass Nothing q => dCheckable q
   DCtor _ _ qs => all dCheckable qs
   DStar Nothing _ => True
   DSq q => dCheckable q
   DSquashElim Nothing e b => dSynth e && dCheckable b
   DCoind Nothing r q1 q2 => dCheckable r && dCheckable q1 && dCheckable q2
   DZeroElim Nothing q => dCheckable q
   DNatElim Nothing z st n => dCheckable z && dCheckable st && dCheckable n
   DSumElim Nothing l r t => dCheckable l && dCheckable r && dSynth t
   DQuotElim Nothing _ f q => dCheckable f && dSynth q
   DConv q Nothing _ => dSynth q
   DAscribe q _ _ => dCheckable q
   DLet a b => dSynth a && dCheckable b
   DPi a b => dCheckable a && dCheckable b
   DSigma a b => dCheckable a && dCheckable b
   DSum a b => dCheckable a && dCheckable b
   DQuot a r => dCheckable a && dCheckable r
   DSquash q => dCheckable q
   DSym q => dCheckable q
   DTrans q r => (dCheckable q && dDirable True r) || (dCheckable r && dDirable False q)
   DTransAt q _ r => (dCheckable q && dDirable True r) || (dCheckable r && dDirable False q)
   _ => False

 ||| Can the derivation run DIRECTIONALLY (→) from the side d names
 ||| (True: the left side is given)? A stating derivation can (it
 ||| compares the given side and produces the other); refl and the
 ||| forward-only δ-all can; structure and nodes can when their parts
 ||| can.
 dDirable : Bool -> Drv -> Bool
 dDirable d p = if dSynth p then True else case p of
   DReflx => True
   DDeltaAll _ => d
   DSym q => dDirable (not d) q
   DTrans q r => dDirable d q && dDirable d r
   DTransAt q _ r => dDirable d q && dDirable d r
   DConv q _ _ => dDirable d q
   DAscribe q _ _ => dDirable d q
   DLam _ q => dDirable d q
   DPair _ u v => dDirable d u && dDirable d v
   DInj1 _ q => dDirable d q
   DInj2 _ q => dDirable d q
   DClass _ q => dDirable d q
   DSuc q => dDirable d q
   DCtor _ _ qs => all (dDirable d) qs
   DCorec _ a f x => dDirable d a && dDirable d f && dDirable d x
   DZeroElim _ q => dDirable d q
   DNatElim _ z s n => dDirable d z && dDirable d s && dDirable d n
   DSumElim _ l r t => dDirable d l && dDirable d r && dDirable d t
   DQuotElim _ _ f q => dDirable d f && dDirable d q
   DQElim _ _ _ _ ms es w => all (dDirable d) ms && all (dDirable d) es && dDirable d w
   DOut q => dDirable d q
   DApp f a => dDirable d f && dDirable d a
   DProj1 q => dDirable d q
   DProj2 q => dDirable d q
   DPi a b => dDirable d a && dDirable d b
   DSigma a b => dDirable d a && dDirable d b
   DSum a b => dDirable d a && dDirable d b
   DEq l r t => dDirable d l && dDirable d r && dDirable d t
   DQuot a r => dDirable d a && dDirable d r
   DSquash q => dDirable d q
   DSort _ _ qs => all (dDirable d) qs
   DRef _ qs => all (dDirable d) qs
   _ => False

||| Δ without its d newest entries (the substitution node's Δ↓d).
dropCtx : Nat -> Ctx -> Maybe Ctx
dropCtx Z ctx = Just ctx
dropCtx (S n) (ctx :< _) = dropCtx n ctx
dropCtx (S _) [<] = Nothing

||| A goal for the readings that decompose: one side given, with the
||| direction, or both.
data DGoal : Type where
  DGDir : Bool -> Elem -> DGoal
  DGChk : Elem -> Elem -> DGoal

mutual
  ||| ⇒ (10.3): the equation a derivation states, with its type.
  export
  dInfer : Sig -> Ctx -> Drv -> KM (Elem, Elem, Ty)
  dInfer sig ctx d = case d of
    -- ----- leaves -----
    DVar i => case ctxLookup ctx i of
      Just ty => pure (CtxVar i, CtxVar i, ty)
      Nothing => kerr "kernel: variable out of bounds"
    DRef x ps =>
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef delta _ _ ty) => dRefAt sig ctx x ps delta ty
        Just (SigDecl delta _ ty) => dRefAt sig ctx x ps delta ty
        Just _ => kerr "kernel: signature name is not a term entry"
        Nothing => kerr "kernel: unknown signature name '\{x}'"
    DUnit => pure (OneIntro, OneIntro, OneTy)
    DZero => pure (NatIntro0, NatIntro0, NatTy)
    DZeroTy => pure (ZeroTy, ZeroTy, UniverseTy)
    DOneTy => pure (OneTy, OneTy, UniverseTy)
    DNatTy => pure (NatTy, NatTy, UniverseTy)
    DUniverse => pure (UniverseTy, UniverseTy, TopTy)
    DProp => pure (PropTy, PropTy, TopTy)
    DTop => pure (TopTy, TopTy, TopTy)
    -- el-reflect read certificate-side: the proof element derives an
    -- equality prop; its sides are the licensed equation (β-whnf of
    -- the prop: an equality hidden behind a definition arrives
    -- ascribed, (π : π_T by β))
    DRefl p => do
      (u, u', pty) <- dInfer sig ctx p
      if u == u' then pure () else kerr "kernel: reflection of a proper equation"
      pty' <- kWhnfT sig pty
      case pty' of
        Elem.EqTy l r a => pure (l, r, a)
        Squash q => do
          q' <- kWhnfT sig q
          case q' of
            Elem.EqTy l r a => pure (l, r, a)
            _ => kerr "kernel: reflection at a squash that is not an equation"
        _ => kerr "kernel: reflection at a non-equation type [\{show pty'}]"
    DPath sg k ps => do
      sg' <- kJoinQSig sig sg
      entry <- case qEntry sg' k of
                 Just e => pure e
                 Nothing => kerr "kernel: path leaf entry out of range"
      case qEntryKind entry of
        QKEq => pure ()
        _ => kerr "kernel: path leaf at a non-equation entry"
      (tel, _, _) <- liftQ (reflTel sg' (qwAt k) entry)
      th <- dTele sig ctx tel ps
      -- the imposed equation, at the spine
      (wEnd, hd) <- liftQ (walkVals sg' (qwAt k) entry th)
      (lq, rq, uq) <- liftQ (eqHead hd)
      l <- liftQ (reflTm sg' wEnd lq)
      r <- liftQ (reflTm sg' wEnd rq)
      a <- liftQ (reflCodeTy sg' wEnd uq)
      pure (l, r, a)
    DDelta x ps =>
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef delta _ body ty) => do
          es <- dSpine sig ctx (toList delta) ps
          let esN = the SubNorm (cast es)
          pure (SigVar x esN, substElem body (embed esN), substTy ty (embed esN))
        Just _ => kerr "kernel: δ leaf at a declaration '\{x}'"
        Nothing => kerr "kernel: δ leaf names unknown definition '\{x}'"
    -- ----- structure -----
    DSym p => do (l, r, t) <- dInfer sig ctx p; pure (r, l, t)
    DTrans p q =>
      if dSynth p && dDirable True q
        then do
          (a, b, t) <- dInfer sig ctx p
          bJ <- kJoinElem sig b
          c <- dDir sig ctx q True bJ t
          pure (a, c, t)
        else if dSynth q && dDirable False p
        then do
          (b, c, t) <- dInfer sig ctx q
          bJ <- kJoinElem sig b
          a <- dDir sig ctx p False bJ t
          pure (a, c, t)
        else kerr "kernel: transitivity does not state its equation"
    DTransAt p m q =>
      if dSynth p && dDirable True q
        then do
          (a, b, t) <- dInfer sig ctx p
          mJ <- kJoinElem sig m
          sameB sig b mJ
          c <- dDir sig ctx q True mJ t
          pure (a, c, t)
        else if dSynth q && dDirable False p
        then do
          (b, c, t) <- dInfer sig ctx q
          mJ <- kJoinElem sig m
          sameB sig b mJ
          a <- dDir sig ctx p False mJ t
          pure (a, c, t)
        else kerr "kernel: transitivity does not state its equation"
    -- ----- conversion, ascription, substitution -----
    DConv p (Just pT) beta => do
      (l, r, t) <- dInfer sig ctx p
      t' <- dType sig ctx pT
      dAt sig ctx beta t t' TopTy
      pure (l, r, t')
    DConv p Nothing beta => kerr "kernel: a checking-mode conversion (π by β) in inference position"
    DAt p pT beta => do
      (l, r, t) <- dInfer sig ctx p
      t' <- dType sig ctx pT
      dAt sig ctx beta t t' TopTy
      pure (l, r, t')
    -- an ASCRIPTION: the derivation checked at the type the annotation
    -- derives (the inference form of a checking derivation); the
    -- optional conversion belongs to checking positions only
    DAscribe p pT Nothing => do
      t' <- dType sig ctx pT
      (l, r) <- dCheck sig ctx p t'
      pure (l, r, t')
    DAscribe p pT (Just _) => kerr "kernel: an ascription's conversion has no position type to convert in inference position"
    DSubst p (MkDSub dep es) => do
      base <- case dropCtx dep ctx of
                Just c => pure c
                Nothing => kerr "kernel: substitution weakens past the context"
      (gamma, sub) <- dSubEntries sig ctx base dep es
      (l, r, t) <- dInfer sig gamma p
      pure (substElem l sub, substElem r sub, substTy t sub)
    -- ----- intro forms (inference: annotated) -----
    DLam (Just pA) p => do
      a <- dType sig ctx pA
      (l, r, b) <- dInfer sig (ctx :< a) p
      pure (PiIntro l, PiIntro r, PiTy a b)
    DPair (Just pB) u v => do
      (ul, ur, a) <- dInfer sig ctx u
      b <- dType sig (ctx :< a) pB
      (vl, vr) <- dCheck sig ctx v (substTy b (Ext Id ul))
      pure (SigmaIntro ul vl, SigmaIntro ur vr, SigmaTy a b)
    DInj1 (Just pB) p => do
      (l, r, a) <- dInfer sig ctx p
      b <- dType sig ctx pB
      pure (Inj1 l, Inj1 r, SumTy a b)
    DInj2 (Just pA) p => do
      (l, r, b) <- dInfer sig ctx p
      a <- dType sig ctx pA
      pure (Inj2 l, Inj2 r, SumTy a b)
    DClass (Just pR) p => do
      (l, r, a) <- dInfer sig ctx p
      rel <- dElemAt sig (ctx :< a :< substTy a Wk) pR PropTy
      pure (Class l, Class r, QuotTy a rel)
    DSuc p => do
      (l, r) <- dCheck sig ctx p NatTy
      pure (NatIntro1 l, NatIntro1 r, NatTy)
    DCtor _ _ _ => kerr "kernel: a constructor in inference position (checked at its sort)"
    DCorec f a g x => do
      aC <- dElemAt sig ctx a UniverseTy
      g' <- dElemAt sig (ctx :< aC) g (substTy (reflectPoly f aC) Wk)
      x' <- dElemAt sig ctx x aC
      pure (Corec f aC g' x', Corec f aC g' x', NuTy f)
    DLet a b => do
      (av, _, aTy) <- dElemTy sig ctx a
      let hyp = Elem.EqTy (CtxVar 0) (substElem av Wk) (substTy aTy Wk)
      (bl, br, bTy) <- dInfer sig (ctx :< aTy :< hyp) b
      let inst = Ext (Ext Id av) Star
      pure (Let av bl, Let av br, substTy bTy inst)
    DStar (Just pP) p => do
      prop <- dElemAt sig ctx pP PropTy
      prop' <- kWhnfT sig prop
      case prop' of
        Elem.EqTy l r a => do dAt sig ctx p l r a; pure (Star, Star, prop)
        _ => kerr "kernel: ⋆ by π at a non-equality prop"
    DSq p => do
      (e, _, a) <- dElemTy sig ctx p
      pure (Star, Star, Squash a)
    DSquashElim (Just pQ) e b => do
      q <- dElemAt sig ctx pQ PropTy
      squashElimAt sig ctx q e b
      pure (Star, Star, q)
    DCoind (Just pP) r p q => do
      prop <- dElemAt sig ctx pP PropTy
      coindAt sig ctx prop r p q
      pure (Star, Star, prop)
    -- ----- eliminators -----
    DZeroElim (Just pT) p => do
      t <- dType sig ctx pT
      (l, r) <- dCheck sig ctx p ZeroTy
      pure (ZeroElim l, ZeroElim r, t)
    DNatElim (Just pM) z s n => do
      mot <- dType sig (ctx :< NatTy) pM
      natElimAt sig ctx mot z s n
    DSumElim (Just pM) l r t => do
      (tl, tr, tTy) <- dInfer sig ctx t
      tTy' <- kWhnfT sig tTy
      case tTy' of
        SumTy a b => do
          mot <- dType sig (ctx :< SumTy a b) pM
          sumElimAt sig ctx mot a b l r (tl, tr, tTy)
        _ => kerr "kernel: ⊎-elim of a non-⊎ scrutinee"
    DQuotElim (Just pM) wd f q => do
      (ql, qr, qTy) <- dInfer sig ctx q
      qTy' <- kWhnfT sig qTy
      case qTy' of
        QuotTy a rel => do
          mot <- dType sig (ctx :< QuotTy a rel) pM
          quotElimAt sig ctx mot a rel wd f (ql, qr, qTy)
        _ => kerr "kernel: quot-elim of a non-quotient"
    DQElim sg k cs cohs ms es w => qElimAt sig ctx sg k cs cohs ms es w
    DOut p => do
      (l, r, tTy) <- dInfer sig ctx p
      tTy' <- kWhnfT sig tTy
      case tTy' of
        NuTy f => pure (Out l, Out r, reflectPoly f (Elem.NuTy f))
        _ => kerr "kernel: observing a non-ν element"
    DApp f a => do
      (fl, fr, fTy) <- dInfer sig ctx f
      fTy' <- kWhnfT sig fTy
      case fTy' of
        PiTy dom cod => do
          (al, ar) <- dCheck sig ctx a dom
          pure (PiApp fl al, PiApp fr ar, substTy cod (Ext Id al))
        _ => kerr "kernel: applying a non-function [\{show fTy'}]"
    DProj1 p => do
      (l, r, tTy) <- dInfer sig ctx p
      tTy' <- kWhnfT sig tTy
      case tTy' of
        SigmaTy a _ => pure (SigmaElim1 l, SigmaElim1 r, a)
        _ => kerr "kernel: projecting a non-pair"
    DProj2 p => do
      (l, r, tTy) <- dInfer sig ctx p
      tTy' <- kWhnfT sig tTy
      case tTy' of
        SigmaTy _ b => pure (SigmaElim2 l, SigmaElim2 r, substTy b (Ext Id (SigmaElim1 l)))
        _ => kerr "kernel: projecting a non-pair"
    -- ----- types and codes: a shared former is a code when its
    -- ----- components are, a type otherwise (cumulativity)
    DPi a b => do
      (al, ar, ka) <- dInfer sig ctx a
      (bl, br, kb) <- dInfer sig (ctx :< al) b
      k <- classifierOf sig ka kb
      pure (Elem.PiTy al bl, Elem.PiTy ar br, k)
    DSigma a b => do
      (al, ar, ka) <- dInfer sig ctx a
      (bl, br, kb) <- dInfer sig (ctx :< al) b
      k <- classifierOf sig ka kb
      pure (Elem.SigmaTy al bl, Elem.SigmaTy ar br, k)
    DSum a b => do
      (al, ar, ka) <- dInfer sig ctx a
      (bl, br, kb) <- dInfer sig ctx b
      k <- classifierOf sig ka kb
      pure (Elem.SumTy al bl, Elem.SumTy ar br, k)
    DEq l r t => do
      tT <- dType sig ctx t
      (ll, lr) <- dCheck sig ctx l tT
      (rl, rr) <- dCheck sig ctx r tT
      pure (Elem.EqTy ll rl tT, Elem.EqTy lr rr tT, PropTy)
    DQuot a r => do
      (al, ar, ka) <- dInfer sig ctx a
      isCls sig ka
      (rl, rr) <- dCheck sig (ctx :< al :< substTy al Wk) r PropTy
      pure (QuotTy al rl, QuotTy ar rr, ka)
    DSquash p => do
      (l, r, k) <- dInfer sig ctx p
      isCls sig k
      pure (Squash l, Squash r, PropTy)
    DNu f => do
      -- the polynomial's embedded codes are bare terms, checked at 𝕌
      -- (neutral-checkable in the emitted fragment — A3's kin)
      _ <- kCheckPolyK sig ctx f 0 (Nd [] [])
      pure (NuTy f, NuTy f, UniverseTy)
    DSort sg k ps => do
      kQSigCheck sig ctx sg
      sortE <- case qEntry sg k of
                 Just e => pure e
                 Nothing => kerr "kernel: sort position out of range"
      case qEntryKind sortE of
        QKSort => pure ()
        _ => kerr "kernel: not a sort position"
      (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
      es <- dTele sig ctx tel ps
      small <- kTry (kQSigSmall sig ctx sg)
      pure (QSort sg k (cast es), QSort sg k (cast es), if small then UniverseTy else TopTy)
    _ => kerr "kernel: derivation in inference position needs its annotation [\{showDrv d}]"

  ||| ⇐ T (10.3): the sides a derivation states at a known type. An
  ||| intro node reads its children at the parts of nf(T); an
  ||| eliminator without a motive at the constant motive T[↑]; any
  ||| other node infers and its type must agree with T.
  export
  dCheck : Sig -> Ctx -> Drv -> Ty -> KM (Elem, Elem)
  dCheck sig ctx d ty = case d of
    DConv p Nothing beta => do
      (l, r, t) <- dInfer sig ctx p
      dAt sig ctx beta t ty TopTy
      pure (l, r)
    DConv p (Just pT) beta => do
      -- the inference form in a checking position: p infers, converts
      -- to the annotation, which must agree with the type flowing down
      (l, r, t) <- dInfer sig ctx p
      t' <- dType sig ctx pT
      dAt sig ctx beta t t' TopTy
      agree t'
      pure (l, r)
    DAscribe p pT mb => do
      -- the type flowing down converted (or agreeing) to what the
      -- annotation derives, and p checked at the result: exposure
      t' <- dType sig ctx pT
      case mb of
        Just b => dAt sig ctx b ty t' TopTy
        Nothing => agree t'
      dCheck sig ctx p t'
    DLam Nothing p => do
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy a b => do (l, r) <- dCheck sig (ctx :< a) p b; pure (PiIntro l, PiIntro r)
        _ => kerr "kernel: λ checked at a non-Π type [\{show ty}]"
    DPair Nothing u v => do
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy a b => do
          (ul, ur) <- dCheck sig ctx u a
          (vl, vr) <- dCheck sig ctx v (substTy b (Ext Id ul))
          pure (SigmaIntro ul vl, SigmaIntro ur vr)
        _ => kerr "kernel: pair checked at a non-× type [\{show ty}]"
    DInj1 Nothing p => do
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy a _ => do (l, r) <- dCheck sig ctx p a; pure (Inj1 l, Inj1 r)
        _ => kerr "kernel: inj₁ checked at a non-⊎ type"
    DInj2 Nothing p => do
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy _ b => do (l, r) <- dCheck sig ctx p b; pure (Inj2 l, Inj2 r)
        _ => kerr "kernel: inj₂ checked at a non-⊎ type"
    DClass Nothing p => do
      ty' <- kWhnfT sig ty
      case ty' of
        QuotTy a _ => do (l, r) <- dCheck sig ctx p a; pure (Class l, Class r)
        _ => kerr "kernel: class checked at a non-quotient type"
    DCtor sgC c ps => do
      -- el-qiit-intro, as §8: the type's carrier and the term's join
      -- alike; the spine at the reflected telescope; the head's sort
      -- and indices meet the type's
      ty' <- kJoinTy sig ty
      case ty' of
        QSort sgT srt es => do
          sgC' <- kJoinQSig sig sgC
          if sgC' /= sgT then kerr "kernel: constructor of a different signature" else pure ()
          entry <- case qEntry sgC' c of
                     Just x => pure x
                     Nothing => kerr "kernel: constructor position out of range"
          case qEntryKind entry of
            QKPoint => pure ()
            _ => kerr "kernel: not a point-constructor position"
          (tel, _, _) <- liftQ (reflTel sgC' (qwAt c) entry)
          args <- dTele sig ctx tel ps
          (wEnd, hd) <- liftQ (walkVals sgC' (qwAt c) entry args)
          (srt', idx) <- liftQ (pointHead sgC' wEnd hd)
          if srt' /= srt then kerr "kernel: constructor of a different sort" else pure ()
          idxN <- kJoinSubNorm sig idx
          esN <- kJoinSubNorm sig es
          if idxN == esN then pure () else kerr "kernel: constructor indices do not match the type"
          let t = QCtor sgC c (cast args)
          pure (t, t)
        _ => kerr "kernel: constructor checked at a non-QIIT type"
    DStar Nothing p => do
      ty' <- kWhnfT sig ty
      case ty' of
        Elem.EqTy l r a => do dAt sig ctx p l r a; pure (Star, Star)
        _ => kerr "kernel: ⋆ by π at a non-equality prop"
    DSq p => do
      ty' <- kWhnfT sig ty
      case ty' of
        Squash a => do _ <- dElemAt sig ctx p a; pure (Star, Star)
        _ => kerr "kernel: sq(π) at a non-∥∥ type"
    DSquashElim Nothing e b => do
      squashElimAt sig ctx ty e b
      pure (Star, Star)
    DCoind Nothing r p q => do
      coindAt sig ctx ty r p q
      pure (Star, Star)
    DZeroElim Nothing p => do
      (l, r) <- dCheck sig ctx p ZeroTy
      pure (ZeroElim l, ZeroElim r)
    -- an eliminator without its motive: the constant motive T[↑]
    DNatElim Nothing z s n => do
      (l, r, t) <- natElimAt sig ctx (substTy ty Wk) z s n
      agree t
      pure (l, r)
    DSumElim Nothing l r t => do
      (tl, tr, tTy) <- dInfer sig ctx t
      tTy' <- kWhnfT sig tTy
      case tTy' of
        SumTy a b => do
          (l', r', t') <- sumElimAt sig ctx (substTy ty Wk) a b l r (tl, tr, tTy)
          agree t'
          pure (l', r')
        _ => kerr "kernel: ⊎-elim of a non-⊎ scrutinee"
    DQuotElim Nothing wd f q => do
      (ql, qr, qTy) <- dInfer sig ctx q
      qTy' <- kWhnfT sig qTy
      case qTy' of
        QuotTy a rel => do
          (l', r', t') <- quotElimAt sig ctx (substTy ty Wk) a rel wd f (ql, qr, qTy)
          agree t'
          pure (l', r')
        _ => kerr "kernel: quot-elim of a non-quotient"
    DLet a b => do
      (av, _, aTy) <- dElemTy sig ctx a
      let hyp = Elem.EqTy (CtxVar 0) (substElem av Wk) (substTy aTy Wk)
      (bl, br) <- dCheck sig (ctx :< aTy :< hyp) b (weakenTyN 2 ty)
      pure (Let av bl, Let av br)
    -- a shared former at a classifier: its components at that
    -- classifier (codes at 𝕌, types at 𝕍 — cumulativity)
    DPi a b => atCls (\cls => do
      (al, ar) <- dCheck sig ctx a cls
      (bl, br) <- dCheck sig (ctx :< al) b cls
      pure (Elem.PiTy al bl, Elem.PiTy ar br))
    DSigma a b => atCls (\cls => do
      (al, ar) <- dCheck sig ctx a cls
      (bl, br) <- dCheck sig (ctx :< al) b cls
      pure (Elem.SigmaTy al bl, Elem.SigmaTy ar br))
    DSum a b => atCls (\cls => do
      (al, ar) <- dCheck sig ctx a cls
      (bl, br) <- dCheck sig ctx b cls
      pure (Elem.SumTy al bl, Elem.SumTy ar br))
    DQuot a r => atCls (\cls => do
      (al, ar) <- dCheck sig ctx a cls
      (rl, rr) <- dCheck sig (ctx :< al :< substTy al Wk) r PropTy
      pure (QuotTy al rl, QuotTy ar rr))
    DSquash p => do
      ty' <- kWhnfT sig ty
      case ty' of
        PropTy => do (l, r) <- dCheck sig ctx p TopTy; pure (Squash l, Squash r)
        TopTy => do (l, r) <- dCheck sig ctx p TopTy; pure (Squash l, Squash r)
        _ => kerr "kernel: ∥·∥ checked at a non-classifier"
    -- structure: the type flows down through it
    DSym p => do (l, r) <- dCheck sig ctx p ty; pure (r, l)
    DTrans p q =>
      if dCheckable p && dDirable True q
        then do
          (a, b) <- dCheck sig ctx p ty
          bJ <- kJoinElem sig b
          c <- dDir sig ctx q True bJ ty
          pure (a, c)
        else if dCheckable q && dDirable False p
        then do
          (b, c) <- dCheck sig ctx q ty
          bJ <- kJoinElem sig b
          a <- dDir sig ctx p False bJ ty
          pure (a, c)
        else kerr "kernel: transitivity does not state its equation"
    DTransAt p m q => do
      mJ <- kJoinElem sig m
      if dCheckable p && dDirable True q
        then do
          (a, b) <- dCheck sig ctx p ty
          sameB sig b mJ
          c <- dDir sig ctx q True mJ ty
          pure (a, c)
        else if dCheckable q && dDirable False p
        then do
          (b, c) <- dCheck sig ctx q ty
          sameB sig b mJ
          a <- dDir sig ctx p False mJ ty
          pure (a, c)
        else kerr "kernel: transitivity does not state its equation"
    _ => do
      (l, r, t) <- dInfer sig ctx d
      -- an ELEMENT's type must agree with the position's; a stating
      -- LEAF's equation is at the position's type (the positional
      -- check, §7); a spine NODE over a proper equation computes its
      -- children's types from its own head (§6) and the position's
      -- type is not compared — the sides' types are equal only
      -- through the equation itself (a dependent codomain moves with
      -- the argument)
      if l == r || posChecked d then agree t else pure ()
      pure (l, r)
   where
    posChecked : Drv -> Bool
    posChecked (DApp _ _) = False
    posChecked (DProj1 _) = False
    posChecked (DProj2 _) = False
    posChecked (DOut _) = False
    posChecked (DRef _ _) = False
    posChecked (DNatElim _ _ _ _) = False
    posChecked (DSumElim _ _ _ _) = False
    posChecked (DQuotElim _ _ _ _) = False
    posChecked (DQElim _ _ _ _ _ _ _) = False
    posChecked (DLet _ _) = False
    posChecked _ = True
    -- the classifier a shared former is checked at: 𝕌 or 𝕍 (Ω is not
    -- a classifier of formers)
    atCls : (Ty -> KM (Elem, Elem)) -> KM (Elem, Elem)
    atCls k = do
      ty' <- kWhnfT sig ty
      case ty' of
        UniverseTy => k UniverseTy
        TopTy => k TopTy
        _ => kerr "kernel: a type former checked at a non-classifier [\{show ty}]"
    agree : Ty -> KM ()
    agree t = do
      ok <- tyAgree sig ty t
      if ok then pure ()
        else kerr "kernel: type mismatch without a conversion\n  inferred: \{show t}\n  expected: \{show ty}"

  ||| ▷ l ≐ r : T (10.5): a proof read against given sides. A
  ||| derivation that synthesizes is checked at T and its sides meet
  ||| the given ones under β; one that does not decomposes them.
  export
  dAt : Sig -> Ctx -> Drv -> Elem -> Elem -> Ty -> KM ()
  dAt sig ctx d l r ty =
    if dSynth d
      then checked
      -- a proof that runs left to right is read so first — the
      -- produced side compared with the right one under β, so the
      -- right side need not have the shape the proof produces (it may
      -- be the β-normal form of it: a δ exposure's result); then a
      -- checkable proof is checked and compared; otherwise both sides
      -- decompose
      else if dDirable True d
        then kOrElse (do x <- dDir sig ctx d True l ty
                         sameB sig x r)
                     rest
        else rest
   where
    checked : KM ()
    checked = do
      (l', r') <- dCheck sig ctx d ty
      sameB sig l' l
      sameB sig r' r
    rest : KM ()
    rest = if dCheckable d then checked else ignore (dGo sig ctx d (DGChk l r) ty)

  ||| → : the directional run from the side d names (True: the left
  ||| side is given), producing the other, unjoined.
  export
  dDir : Sig -> Ctx -> Drv -> Bool -> Elem -> Ty -> KM Elem
  dDir sig ctx d dir x ty =
    if dSynth d
      then checked
      else if dDirable dir d
        then kOrElse (dGo sig ctx d (DGDir dir x) ty) (if dCheckable d then checked else dGo sig ctx d (DGDir dir x) ty)
        else if dCheckable d
          then checked
          else dGo sig ctx d (DGDir dir x) ty
   where
    checked : KM Elem
    checked = do
      (a, b) <- dCheck sig ctx d ty
      sameB sig (if dir then a else b) x
      pure (if dir then b else a)

  ||| The decomposing readings (▷ and →) of the derivations that do
  ||| not synthesize: refl, δ-all, structure, the type-directed
  ||| leaves, and nodes whose children read against the parts of the
  ||| given side(s), typed by the node above (§6). Under → the
  ||| produced side is returned; under ▷ the return is meaningless.
  dGo : Sig -> Ctx -> Drv -> DGoal -> Ty -> KM Elem
  dGo sig ctx d goal ty = case (d, goal) of
    -- ----- structure -----
    (DReflx, DGDir _ x) => pure x
    (DReflx, DGChk l r) => do sameB sig l r; pure l
    (DDeltaAll ns, DGDir True x) => unfoldAllK sig ns x
    (DDeltaAll ns, DGDir False x) => kerr "kernel: δ-all runs left to right only"
    (DDeltaAll ns, DGChk l r) => do
      l' <- unfoldAllK sig ns l
      sameB sig l' r
      pure l
    (DSym q, DGDir dir x) => dDir sig ctx q (not dir) x ty
    (DSym q, DGChk l r) => do dAt sig ctx q r l ty; pure l
    (DTrans q1 q2, DGDir True x) =>
      if dDirable True q1 && dDirable True q2
        then do
          m <- dDir sig ctx q1 True x ty >>= kJoinElem sig
          dDir sig ctx q2 True m ty
        else if dSynth q2
        then do
          (b, c, t) <- dInfer sig ctx q2
          agreeAt t
          bJ <- kJoinElem sig b
          dAt sig ctx q1 x bJ ty
          pure c
        else kerr "kernel: transitivity with no computable middle (left to right)"
    (DTrans q1 q2, DGDir False x) =>
      if dDirable False q2 && dDirable False q1
        then do
          m <- dDir sig ctx q2 False x ty >>= kJoinElem sig
          dDir sig ctx q1 False m ty
        else if dSynth q1
        then do
          (a, b, t) <- dInfer sig ctx q1
          agreeAt t
          bJ <- kJoinElem sig b
          dAt sig ctx q2 bJ x ty
          pure a
        else kerr "kernel: transitivity with no computable middle (right to left)"
    (DTrans q1 q2, DGChk l r) =>
      if dDirable True q1
        then do
          m <- dDir sig ctx q1 True l ty >>= kJoinElem sig
          dAt sig ctx q2 m r ty
          pure l
        else if dDirable False q2
        then do
          m <- dDir sig ctx q2 False r ty >>= kJoinElem sig
          dAt sig ctx q1 l m ty
          pure l
        else kerr "kernel: transitivity with no computable middle"
    (DTransAt q1 m q2, DGDir True x) => do
      mJ <- kJoinElem sig m
      dAt sig ctx q1 x mJ ty
      dDir sig ctx q2 True mJ ty
    (DTransAt q1 m q2, DGDir False x) => do
      mJ <- kJoinElem sig m
      dAt sig ctx q2 mJ x ty
      dDir sig ctx q1 False mJ ty
    (DTransAt q1 m q2, DGChk l r) => do
      mJ <- kJoinElem sig m
      dAt sig ctx q1 l mJ ty
      dAt sig ctx q2 mJ r ty
      pure l
    -- an ascription around a proof: the position's type converted to
    -- what the annotation derives, the proof read there
    (DAscribe q pT (Just beta), _) => do
      case ty of
        TopTy => kerr "kernel: a type equation cannot convert its type"
        _ => pure ()
      t' <- dType sig ctx pT
      dAt sig ctx beta ty t' TopTy
      dGo sig ctx q goal t'
    (DAscribe q pT Nothing, _) => do
      t' <- dType sig ctx pT
      agreeAt t'
      dGo sig ctx q goal t'
    (DConv q _ beta, _) => kerr "kernel: a switch around a non-stating proof"
    -- ----- type-directed leaves (both sides) -----
    (DIrrel pP, DGChk l r) => do
      ty' <- kWhnfT sig ty
      case ty' of
        OneTy => pure l
        ZeroTy => pure l
        _ => do
          (p, _, k) <- dElemTy sig ctx pP
          kPr <- kWhnfT sig k
          case kPr of
            PropTy => pure ()
            _ => kerr "kernel: irrelevance at a non-propositional type"
          ok <- tyAgree sig ty p
          if ok then pure l else kerr "kernel: irrelevance: the derived prop is not the position's type"
    (DEtaPi q, DGChk l r) => do
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy dom cod => do
          dAt sig (ctx :< dom) q (PiApp (substElem l Wk) (CtxVar 0)) (PiApp (substElem r Wk) (CtxVar 0)) cod
          pure l
        _ => kerr "kernel: Π-η at a non-Π type"
    (DEtaSigma q1 q2, DGChk l r) => do
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy dom cod => do
          dAt sig ctx q1 (SigmaElim1 l) (SigmaElim1 r) dom
          dAt sig ctx q2 (SigmaElim2 l) (SigmaElim2 r) (substTy cod (Ext Id (SigmaElim1 l)))
          pure l
        _ => kerr "kernel: Σ-η at a non-Σ type"
    (DQuotWit mq, DGChk l r) => do
      ty' <- kWhnfT sig ty
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      case (ty', lJ, rJ) of
        (QuotTy _ rel, Class a, Class b) => do
          inst <- kJoinElem sig (substElem rel (Ext (Ext Id a) b))
          case (inst, mq) of
            (Squash OneTy, _) => pure l
            (Elem.EqTy wl wr wt, Just q) => do dAt sig ctx q wl wr wt; pure l
            _ => kerr "kernel: quotient witness: the relation instance has no evident shape"
        _ => kerr "kernel: quotient witness at a non-class equation"
    (DQuotWitPrf w, DGChk l r) => do
      ty' <- kWhnfT sig ty
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      case (ty', lJ, rJ) of
        (QuotTy _ rel, Class a, Class b) => do
          _ <- dElemAt sig ctx w (substElem rel (Ext (Ext Id a) b))
          pure l
        _ => kerr "kernel: quotient witness at a non-class equation"
    (DInj q, DGChk l r) => do
      ty' <- kWhnfT sig ty
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      case (ty', lJ, rJ) of
        (SumTy a _, Inj1 x, Inj1 y) => do dAt sig ctx q x y a; pure l
        (SumTy _ b, Inj2 x, Inj2 y) => do dAt sig ctx q x y b; pure l
        _ => kerr "kernel: injection leaf at a non-matching equation"
    (DPropExt f g, DGChk l r) => do
      ty' <- kWhnfT sig ty
      case ty' of
        PropTy => do
          _ <- dElemAt sig ctx f (PiTy l (substTy r Wk))
          _ <- dElemAt sig ctx g (PiTy r (substTy l Wk))
          pure l
        _ => kerr "kernel: propext at a non-Ω type"
    (DPrfCong pP pQ q, DGChk l r) => do
      case ty of
        TopTy => pure ()
        _ => kerr "kernel: prop-lift on an element equation"
      p <- dElemAt sig ctx pP PropTy
      q' <- dElemAt sig ctx pQ PropTy
      sameB sig p l
      sameB sig q' r
      dAt sig ctx q l r PropTy
      pure l
    (DIrrel _, DGDir _ _) => needBoth
    (DEtaPi _, DGDir _ _) => needBoth
    (DEtaSigma _ _, DGDir _ _) => needBoth
    (DQuotWit _, DGDir _ _) => needBoth
    (DQuotWitPrf _, DGDir _ _) => needBoth
    (DInj _, DGDir _ _) => needBoth
    (DPropExt _ _, DGDir _ _) => needBoth
    (DPrfCong _ _ _, DGDir _ _) => needBoth
    -- ----- nodes: children read against the parts -----
    (DZeroElim _ q, _) =>
      node1 (\x => case x of ZeroElim u => Just u; _ => Nothing) ZeroElim (ctx, ZeroTy) q
    (DSuc q, _) =>
      node1 (\x => case x of NatIntro1 u => Just u; _ => Nothing) NatIntro1 (ctx, NatTy) q
    (DLam _ q, _) => do
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy a b => node1 (\x => case x of PiIntro u => Just u; _ => Nothing) PiIntro (ctx :< a, b) q
        _ => kerr "kernel: λ-congruence at a non-Π type"
    (DPair _ qu qv, _) => do
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy a b =>
          node (\x => case x of SigmaIntro u v => Just [u, v]; _ => Nothing)
               (\xs => case xs of [u, v] => Just (SigmaIntro u v); _ => Nothing)
               (\xs => case xs of
                         [u, _] => pure [(ctx, a), (ctx, substTy b (Ext Id u))]
                         _ => arity) [qu, qv]
        _ => kerr "kernel: pair congruence at a non-Σ type"
    (DInj1 _ q, _) => do
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy a _ => node1 (\x => case x of Inj1 u => Just u; _ => Nothing) Inj1 (ctx, a) q
        _ => kerr "kernel: inj₁ congruence at a non-⊎ type"
    (DInj2 _ q, _) => do
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy _ b => node1 (\x => case x of Inj2 u => Just u; _ => Nothing) Inj2 (ctx, b) q
        _ => kerr "kernel: inj₂ congruence at a non-⊎ type"
    (DClass _ q, _) => do
      ty' <- kWhnfT sig ty
      case ty' of
        QuotTy a _ => node1 (\x => case x of Class u => Just u; _ => Nothing) Class (ctx, a) q
        _ => kerr "kernel: class congruence at a non-quotient type"
    (DNatElim mM qz qs qn, _) => do
      mot <- case mM of
               Just pM => dType sig (ctx :< NatTy) pM
               Nothing => pure (substTy ty Wk)
      node (\x => case x of NatElim z s n => Just [z, s, n]; _ => Nothing)
           (\xs => case xs of [z, s, n] => Just (NatElim z s n); _ => Nothing)
           (\xs => case xs of
                     [_, _, n] => do
                       agreeAt (substTy mot (Ext Id n))
                       pure [ (ctx, substTy mot (Ext Id NatIntro0))
                            , (ctx :< NatTy :< mot, substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
                            , (ctx, NatTy) ]
                     _ => arity) [qz, qs, qn]
    (DSumElim mM ql qr qt, _) => do
      -- the scrutinee must DERIVE: its type gives the branches'
      -- contexts (a head or scrutinee child is never refl)
      (a, b, tTy) <- scrutOf qt (\t => case t of SumTy a b => Just (a, b); _ => Nothing) "⊎-elim"
      mot <- case mM of
               Just pM => dType sig (ctx :< SumTy a b) pM
               Nothing => pure (substTy ty Wk)
      node (\x => case x of SumElim l r t => Just [l, r, t]; _ => Nothing)
           (\xs => case xs of [l, r, t] => Just (SumElim l r t); _ => Nothing)
           (\xs => case xs of
                     [_, _, t] => do
                       agreeAt (substTy mot (Ext Id t))
                       pure [ (ctx :< a, substTy mot (Ext Wk (Inj1 (CtxVar 0))))
                            , (ctx :< b, substTy mot (Ext Wk (Inj2 (CtxVar 0))))
                            , (ctx, tTy) ]
                     _ => arity) [ql, qr, qt]
    (DQuotElim mM _ qf qq, _) => do
      (a, rel, qTy) <- scrutOf qq (\t => case t of QuotTy a r => Just (a, r); _ => Nothing) "quot-elim"
      mot <- case mM of
               Just pM => dType sig (ctx :< QuotTy a rel) pM
               Nothing => pure (substTy ty Wk)
      node (\x => case x of QuotElim f q => Just [f, q]; _ => Nothing)
           (\xs => case xs of [f, q] => Just (QuotElim f q); _ => Nothing)
           (\xs => case xs of
                     [_, q] => do
                       agreeAt (substTy mot (Ext Id q))
                       pure [(ctx :< a, substTy mot (Ext Wk (Class (CtxVar 0)))), (ctx, qTy)]
                     _ => arity) [qf, qq]
    (DOut q, _) => do
      (_, tTy) <- headOf q
      node1 (\x => case x of Out u => Just u; _ => Nothing) Out (ctx, tTy) q
    (DApp qf qa, _) => do
      (fTy', fTy) <- headOf qf
      case fTy' of
        PiTy dom cod =>
          node (\x => case x of PiApp f a => Just [f, a]; _ => Nothing)
               (\xs => case xs of [f, a] => Just (PiApp f a); _ => Nothing)
               (\xs => case xs of
                         [_, _] => pure [(ctx, fTy), (ctx, dom)]
                         _ => arity) [qf, qa]
        _ => kerr "kernel: application congruence: the head is not a function"
    (DProj1 q, _) => do
      (_, tTy) <- headOf q
      node1 (\x => case x of SigmaElim1 u => Just u; _ => Nothing) SigmaElim1 (ctx, tTy) q
    (DProj2 q, _) => do
      (_, tTy) <- headOf q
      node1 (\x => case x of SigmaElim2 u => Just u; _ => Nothing) SigmaElim2 (ctx, tTy) q
    (DCorec pf qa qf qx, _) =>
      node (\u => case u of
                    Corec pf' a f x => if pf == pf' then Just [a, f, x] else Nothing
                    _ => Nothing)
           (\xs => case xs of [a, f, x] => Just (Corec pf a f x); _ => Nothing)
           (\xs => case xs of
                     [a, _, _] => pure [(ctx, UniverseTy), (ctx :< a, substTy (reflectPoly pf a) Wk), (ctx, a)]
                     _ => arity) [qa, qf, qx]
    (DLet qa qb, _) => do
      (_, aTy) <- headOf qa
      node (\x => case x of Let a b => Just [a, b]; _ => Nothing)
           (\xs => case xs of [a, b] => Just (Let a b); _ => Nothing)
           (\xs => case xs of
                     [a, _] => pure [ (ctx, aTy)
                                    , (ctx :< aTy :< Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk), weakenTyN 2 ty) ]
                     _ => arity) [qa, qb]
    -- shared formers: components at the classifier the position gives;
    -- the binder-crossing component under the RIGHT side's domain
    (DPi qa qb, _) => binderTy (\x => case x of Elem.PiTy a b => Just (a, b); _ => Nothing) Elem.PiTy qa qb
    (DSigma qa qb, _) => binderTy (\x => case x of Elem.SigmaTy a b => Just (a, b); _ => Nothing) Elem.SigmaTy qa qb
    (DSum qa qb, _) => do
      cls <- compClassifier sig (Just ty)
      node (\x => case x of Elem.SumTy a b => Just [a, b]; _ => Nothing)
           (\xs => case xs of [a, b] => Just (Elem.SumTy a b); _ => Nothing)
           (\_ => pure [(ctx, cls), (ctx, cls)]) [qa, qb]
    (DEq ql qr qt, _) =>
      node (\x => case x of Elem.EqTy l r t => Just [l, r, t]; _ => Nothing)
           (\xs => case xs of [l, r, t] => Just (Elem.EqTy l r t); _ => Nothing)
           (\xs => case xs of
                     [_, _, t] => pure [(ctx, t), (ctx, t), (ctx, TopTy)]
                     _ => arity) [ql, qr, qt]
    (DQuot qa qr, _) => do
      cls <- compClassifier sig (Just ty)
      case goal of
        DGDir dir x => case x of
          QuotTy a r => do
            a' <- dDir sig ctx qa dir a cls
            let dom = if dir then a' else a
            r' <- dDir sig (ctx :< dom :< substTy dom Wk) qr dir r PropTy
            pure (QuotTy a' r')
          _ => kerr "kernel: proof shape does not match the side [\{show x}]"
        DGChk l r => case (l, r) of
          (QuotTy a0 r0, QuotTy a1 r1) => do
            dAt sig ctx qa a0 a1 cls
            dAt sig (ctx :< a1 :< substTy a1 Wk) qr r0 r1 PropTy
            pure l
          _ => kerr "kernel: proof shape does not match the sides\n  left:  \{show l}\n  right: \{show r}"
    (DSquash q, _) => node1 (\x => case x of Squash u => Just u; _ => Nothing) Squash (ctx, TopTy) q
    (DRef x qs, _) =>
      node (\u => case u of
                    SigVar y es => if y == x then Just (toList es) else Nothing
                    _ => Nothing)
           (\xs => Just (SigVar x (cast xs)))
           (\es => traverse (\i => do mt <- sigChildTy sig x es i
                                      case mt of
                                        Just t => pure (ctx, t)
                                        Nothing => kerr "kernel: spine entry out of range") (indices es)) qs
    (DSort sg k qs, _) =>
      node (\u => case u of
                    QSort sg' k' es => if sg == sg' && k == k' then Just (toList es) else Nothing
                    _ => Nothing)
           (\xs => Just (QSort sg k (cast xs)))
           (\es => traverse (\i => case qSpineChildTy sg k (cast es) i of
                                      Just t => pure (ctx, t)
                                      Nothing => kerr "kernel: spine entry out of range") (indices es)) qs
    (DCtor sg k qs, _) =>
      node (\u => case u of
                    QCtor sg' k' es => if sg == sg' && k == k' then Just (toList es) else Nothing
                    _ => Nothing)
           (\xs => Just (QCtor sg k (cast xs)))
           (\es => traverse (\i => case qSpineChildTy sg k (cast es) i of
                                      Just t => pure (ctx, t)
                                      Nothing => kerr "kernel: spine entry out of range") (indices es)) qs
    (DQElim sg k cs _ qm qs qw, _) => do
      -- motives derived in their sort contexts; the methods at their
      -- method types, the spine at the telescope, the eliminee at the
      -- sort (the coherences are a property of the carried problem,
      -- read under ⇒ — the sides share it syntactically)
      mots <- qMotives sig ctx sg cs
      let nM = length qm
      let split : List Elem -> Maybe (List Elem, List Elem, Elem)
          split xs = case reverse xs of
                       w :: rest => let ys = reverse rest in Just (take nM ys, drop nM ys, w)
                       _ => Nothing
      node (\u => case u of
                    QElim sg' k' fs es w =>
                      if sg == sg' && k == k' && length fs == nM then Just (fs ++ toList es ++ [w]) else Nothing
                    _ => Nothing)
           (\xs => case split xs of
                     Just (fs, es, w) => Just (QElim sg k fs (cast es) w)
                     Nothing => Nothing)
           (\xs => case split xs of
                     Just (fs, es, w) => do
                       o <- case qOrdinal QKSort sg k of
                              Just x => pure x
                              Nothing => kerr "kernel: eliminator sort ordinal"
                       motK <- case getAt o mots of
                                 Just m => pure m
                                 Nothing => kerr "kernel: eliminator motive missing"
                       agreeAt (substTy motK (Ext (foldl Ext Id es) w))
                       mTys <- traverse (\cj => liftQ (methodTy sg mots cj)) (qPositions QKPoint sg)
                       eTys <- traverse (\i => case qSpineChildTy sg k (cast es) i of
                                                 Just t => pure t
                                                 Nothing => kerr "kernel: spine entry out of range") (indices es)
                       pure (map (\t => (ctx, t)) mTys ++ map (\t => (ctx, t)) eTys ++ [(ctx, QSort sg k (cast es))])
                     Nothing => arity) (qm ++ qs ++ [qw])
    (_, DGChk l r) => kerr "kernel: derivation does not read against given sides [\{showDrv d}]"
    (_, DGDir _ _) => kerr "kernel: derivation does not run directionally [\{showDrv d}]"
   where
    arity : KM a
    arity = kerr "kernel: proof node arity"

    needBoth : KM Elem
    needBoth = kerr "kernel: a type-directed proof needs both sides [\{showDrv d}]"

    agreeAt : Ty -> KM ()
    agreeAt t = do
      ok <- tyAgree sig ty t
      if ok then pure ()
        else kerr "kernel: the node's type does not agree with the position's\n  node: \{show t}\n  position: \{show ty}"

    indices : List a -> List Nat
    indices xs = go 0 xs
     where
      go : Nat -> List a -> List Nat
      go _ [] = []
      go i (_ :: rest) = i :: go (S i) rest

    goalSide : Elem
    goalSide = case goal of
      DGDir _ x => x
      DGChk l _ => l

    -- the head's term on the given side (the left one under ▷)
    headTerm : Elem
    headTerm = case (d, goalSide) of
      (DApp _ _, PiApp f _) => f
      (DProj1 _, SigmaElim1 u) => u
      (DProj2 _, SigmaElim2 u) => u
      (DOut _, Out u) => u
      (DSumElim _ _ _ _, SumElim _ _ t) => t
      (DQuotElim _ _ _ _, QuotElim _ q) => q
      (DLet _ _, Let a _) => a
      (_, x) => x

    ||| A head or scrutinee child's type: STATED by the child when it
    ||| derives; else — a rewrite inside the head — read off the given
    ||| side's head by typing inversion (the neutral-subterm rule, §6:
    ||| a spine's head has a declared type, opened along the spine by
    ||| the β-whnf), never invented.
    headOf : Drv -> KM (Ty, Ty)
    headOf q =
      if dSynth q
        then do
          (_, _, t) <- dInfer sig ctx q
          t' <- kWhnfT sig t
          pure (t', t)
        else do
          mt <- inferHead sig ctx headTerm
          case mt of
            Just t => do t' <- kWhnfT sig t; pure (t', t)
            Nothing => kerr "kernel: a head or scrutinee child must derive its type [\{showDrv q}]"

    scrutOf : Drv -> (Ty -> Maybe (Ty, Ty)) -> String -> KM (Ty, Ty, Ty)
    scrutOf q pick what = do
      (t', t) <- headOf q
      case pick t' of
        Just (a, b) => pure (a, b, t)
        Nothing => kerr "kernel: \{what}: the scrutinee's type has no shape for it [\{show t'}]"

    ||| A node: the side(s) decompose by `shape` into the children's
    ||| parts, `kids` computes each child's context and expected type
    ||| from the LEFT parts, the children are read against their
    ||| parts, and `rebuild` reassembles.
    node : (Elem -> Maybe (List Elem)) -> (List Elem -> Maybe Elem)
        -> (List Elem -> KM (List (Ctx, Ty))) -> List Drv -> KM Elem
    node shape rebuild kids qs = do
      (ls, rs) <- the (KM (List Elem, Maybe (List Elem))) $ case goal of
        DGDir dir x => case shape x of
          Just xs => pure (xs, Nothing)
          Nothing => kerr "kernel: proof shape does not match the side [\{show x}]"
        DGChk l r => case (shape l, shape r) of
          (Just ls, Just rs) => pure (ls, Just rs)
          _ => kerr "kernel: proof shape does not match the sides\n  left:  \{show l}\n  right: \{show r}"
      infos <- kids ls
      outs <- goKids qs ls rs infos
      case goal of
        DGDir _ _ => case rebuild outs of
          Just e => pure e
          Nothing => arity
        DGChk l _ => pure l
     where
      goKids : List Drv -> List Elem -> Maybe (List Elem) -> List (Ctx, Ty) -> KM (List Elem)
      goKids [] [] _ [] = pure []
      goKids (q :: qs') (l :: ls') rs' ((cx, t) :: infos') = do
        out <- case (goal, rs') of
          (DGDir dir _, _) => dDir sig cx q dir l t
          (DGChk _ _, Just (r :: _)) => do dAt sig cx q l r t; pure l
          _ => arity
        outs <- goKids qs' ls' (map (drop 1) rs') infos'
        pure (out :: outs)
      goKids _ _ _ _ = arity

    node1 : (Elem -> Maybe Elem) -> (Elem -> Elem) -> (Ctx, Ty) -> Drv -> KM Elem
    node1 shape rebuild info q =
      node (\x => map (\u => [u]) (shape x))
           (\xs => case xs of
                     [u] => Just (rebuild u)
                     _ => Nothing)
           (\_ => pure [info]) [q]

    ||| Π/Σ congruence: the domain at the classifier, the codomain
    ||| under the RIGHT side's domain (under → left to right, the
    ||| domain the domain proof produces).
    binderTy : (Elem -> Maybe (Elem, Elem)) -> (Elem -> Elem -> Elem) -> Drv -> Drv -> KM Elem
    binderTy shape rebuild qa qb = do
      cls <- compClassifier sig (Just ty)
      case goal of
        DGDir dir x => case shape x of
          Just (a, b) => do
            a' <- dDir sig ctx qa dir a cls
            let dom = if dir then a' else a
            b' <- dDir sig (ctx :< dom) qb dir b cls
            pure (rebuild a' b')
          Nothing => kerr "kernel: proof shape does not match the side [\{show x}]"
        DGChk l r => case (shape l, shape r) of
          (Just (a0, b0), Just (a1, b1)) => do
            dAt sig ctx qa a0 a1 cls
            dAt sig (ctx :< a1) qb b0 b1 cls
            pure l
          _ => kerr "kernel: proof shape does not match the sides\n  left:  \{show l}\n  right: \{show r}"

  -- ----- shared pieces of the readings -----

  ||| An annotation derives a TYPE: an element derivation classified
  ||| at 𝕍, or at 𝕌 or Ω by cumulativity.
  dType : Sig -> Ctx -> Drv -> KM Ty
  dType sig ctx d = do
    (t, t', k) <- dInfer sig ctx d
    if t == t' then pure () else kerr "kernel: a type annotation states a proper equation"
    ok <- tyAgree sig TopTy k
    if ok then pure t else kerr "kernel: a type annotation derives no type [\{show t} : \{show k}]"

  ||| An ELEMENT derivation, inferred: its sides coincide.
  dElemTy : Sig -> Ctx -> Drv -> KM (Elem, Elem, Ty)
  dElemTy sig ctx d = do
    (t, t', ty) <- dInfer sig ctx d
    if t == t' then pure (t, t', ty) else kerr "kernel: an element position states a proper equation [\{showDrv d}]"

  ||| An ELEMENT derivation checked at a type.
  dElemAt : Sig -> Ctx -> Drv -> Ty -> KM Elem
  dElemAt sig ctx d ty = do
    (t, t') <- dCheck sig ctx d ty
    if t == t' then pure t else kerr "kernel: an element position states a proper equation [\{showDrv d}]"

  ||| Is the classifier 𝕍, 𝕌 or Ω?
  isCls : Sig -> Ty -> KM ()
  isCls sig k = do
    ok <- tyAgree sig TopTy k
    if ok then pure () else kerr "kernel: a type former's component is not a type [\{show k}]"

  ||| The classifier of a shared former from its components': a CODE
  ||| when both components are codes, a type otherwise.
  classifierOf : Sig -> Ty -> Ty -> KM Ty
  classifierOf sig ka kb = do
    isCls sig ka
    isCls sig kb
    ka' <- kWhnfT sig ka
    kb' <- kWhnfT sig kb
    pure (case (ka', kb') of
            (UniverseTy, UniverseTy) => UniverseTy
            _ => TopTy)

  ||| A signature reference at a stated spine.
  dRefAt : Sig -> Ctx -> String -> List Drv -> Ctx -> Ty -> KM (Elem, Elem, Ty)
  dRefAt sig ctx x ps delta ty = do
    es <- dSpine sig ctx (toList delta) ps
    let esN = the SubNorm (cast es)
    pure (SigVar x esN, SigVar x esN, substTy ty (embed esN))

  ||| A stated SPINE (§3): entry i an element derivation at the
  ||| telescope entry instantiated by the earlier entries.
  dSpine : Sig -> Ctx -> List Ty -> List Drv -> KM (List Elem)
  dSpine sig ctx delta qs =
    if length qs /= length delta
      then kerr "kernel: spine length mismatch"
      else go 0 qs []
   where
    go : Nat -> List Drv -> List Elem -> KM (List Elem)
    go i [] acc = pure (reverse acc)
    go i (q :: rest) acc = do
      ty <- case getAt i delta of
              Just t => pure (substTy t (embed (cast (reverse acc))))
              Nothing => kerr "kernel: spine entry type undetermined"
      e <- dElemAt sig ctx q ty
      go (S i) rest (e :: acc)

  ||| A stated spine at a reflected TELESCOPE (a constructor's, a
  ||| sort's, a path's).
  dTele : Sig -> Ctx -> List Ty -> List Drv -> KM (List Elem)
  dTele sig ctx tel qs =
    if length qs /= length tel
      then kerr "kernel: telescope spine length mismatch"
      else go 0 qs []
   where
    go : Nat -> List Drv -> List Elem -> KM (List Elem)
    go i [] acc = pure (reverse acc)
    go i (q :: rest) acc = do
      ty <- case telInst tel i (reverse acc) of
              Just t => pure t
              Nothing => kerr "kernel: telescope entry type undetermined"
      e <- dElemAt sig ctx q ty
      go (S i) rest (e :: acc)

  ||| The substitution node's entries (10.4): the telescope derived
  ||| over the growing Γ, each entry an element of Δ at the entry type
  ||| instantiated by the earlier entries; gives Γ and σ.
  dSubEntries : Sig -> Ctx -> Ctx -> Nat -> List (Drv, Drv) -> KM (Ctx, Sub)
  dSubEntries sig delta base dep es = go base (wkN dep) es
   where
    go : Ctx -> Sub -> List (Drv, Drv) -> KM (Ctx, Sub)
    go gamma sub [] = pure (gamma, sub)
    go gamma sub ((q, qT) :: rest) = do
      t <- dType sig gamma qT
      e <- dElemAt sig delta q (substTy t sub)
      go (gamma :< t) (Ext sub e) rest

  ||| ℕ-elim at a motive (over Γ ▷ ℕ): el-nat-e.
  natElimAt : Sig -> Ctx -> Ty -> Drv -> Drv -> Drv -> KM (Elem, Elem, Ty)
  natElimAt sig ctx mot z s n = do
    (zl, zr) <- dCheck sig ctx z (substTy mot (Ext Id NatIntro0))
    (sl, sr) <- dCheck sig (ctx :< NatTy :< mot) s (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
    (nl, nr) <- dCheck sig ctx n NatTy
    pure (NatElim zl sl nl, NatElim zr sr nr, substTy mot (Ext Id nl))

  ||| ⊎-elim at a motive (over Γ ▷ A ⊎ B), the scrutinee derived.
  sumElimAt : Sig -> Ctx -> Ty -> Ty -> Ty -> Drv -> Drv -> (Elem, Elem, Ty) -> KM (Elem, Elem, Ty)
  sumElimAt sig ctx mot a b l r (tl, tr, _) = do
    (ll, lr) <- dCheck sig (ctx :< a) l (substTy mot (Ext Wk (Inj1 (CtxVar 0))))
    (rl, rr) <- dCheck sig (ctx :< b) r (substTy mot (Ext Wk (Inj2 (CtxVar 0))))
    pure (SumElim ll rl tl, SumElim lr rr tr, substTy mot (Ext Id tl))

  ||| quot-elim at a motive (over Γ ▷ A/R), the scrutinee derived:
  ||| well-definedness demanded unless the motive is a prop.
  quotElimAt : Sig -> Ctx -> Ty -> Ty -> Elem -> Maybe Drv -> Drv -> (Elem, Elem, Ty) -> KM (Elem, Elem, Ty)
  quotElimAt sig ctx mot a rel wd f (ql, qr, _) = do
    (fl, fr) <- dCheck sig (ctx :< a) f (substTy mot (Ext Wk (Class (CtxVar 0))))
    mIsP <- kIsProp sig (ctx :< QuotTy a rel) mot (Nd [] [])
    if mIsP then pure () else case wd of
      Nothing => kerr "kernel: quot-elim without its well-definedness proof at a non-prop motive"
      Just w => do
        let wk3 = Chain Wk (Chain Wk Wk)
        dAt sig (ctx :< a :< substTy a Wk :< rel) w
          (substElem fl (Ext wk3 (CtxVar 2)))
          (substElem fl (Ext wk3 (CtxVar 1)))
          (substTy mot (Ext wk3 (Class (CtxVar 2))))
    pure (QuotElim fl ql, QuotElim fr qr, substTy mot (Ext Id ql))

  ||| The QIIT eliminator's motives, derived in their sort contexts.
  qMotives : Sig -> Ctx -> QSig -> List Drv -> KM (List Ty)
  qMotives sig ctx sg cs = do
    let sortPs = qPositions QKSort sg
    if length cs /= length sortPs then kerr "kernel: motive count mismatch" else pure ()
    traverse (\(sj, c) => do
      sjE <- case qEntry sg sj of
               Just x => pure x
               Nothing => kerr "kernel: sort out of range"
      (tel, wEnd, _) <- liftQ (reflTel sg (qwAt sj) sjE)
      let mctx = foldl (:<) ctx tel
      let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
      dType sig (mctx :< selfTy) c) (zip sortPs cs)

  ||| el-qiit-elim over mot/dalg/eprob (§8), the coherences as proofs.
  qElimAt : Sig -> Ctx -> QSig -> Nat -> List Drv -> List Drv -> List Drv -> List Drv -> Drv -> KM (Elem, Elem, Ty)
  qElimAt sig ctx sg k cs cohs qm qs qw = do
    kQSigCheck sig ctx sg
    sortE <- case qEntry sg k of
               Just x => pure x
               Nothing => kerr "kernel: eliminator sort out of range"
    case qEntryKind sortE of
      QKSort => pure ()
      _ => kerr "kernel: eliminator at a non-sort position"
    mots <- qMotives sig ctx sg cs
    let pointPs = qPositions QKPoint sg
    let eqPs = qPositions QKEq sg
    if length qm /= length pointPs then kerr "kernel: method count mismatch" else pure ()
    if length cohs /= length eqPs then kerr "kernel: coherence count mismatch" else pure ()
    mths <- traverse (\(cj, m) => do
              mty <- liftQ (methodTy sg mots cj)
              dElemAt sig ctx m mty) (zip pointPs qm)
    traverse_ (\(ej, coh) => do
      (dtel, _, lhs, rhs, cty) <- liftQ (coherenceAt sg mots mths ej)
      dAt sig (foldl (:<) ctx dtel) coh lhs rhs cty) (zip eqPs cohs)
    (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
    es <- dTele sig ctx tel qs
    w <- dElemAt sig ctx qw (QSort sg k (cast es))
    o <- case qOrdinal QKSort sg k of
           Just x => pure x
           Nothing => kerr "kernel: eliminator sort ordinal"
    motK <- case getAt o mots of
              Just m => pure m
              Nothing => kerr "kernel: eliminator motive missing"
    let t = QElim sg k mths (cast es) w
    pure (t, t, substTy motK (Ext (foldl Ext Id es) w))

  ||| el-squash-e-prf at a goal prop: the scrutinee derives ∥A∥, the
  ||| body proves the goal under A.
  squashElimAt : Sig -> Ctx -> Ty -> Drv -> Drv -> KM ()
  squashElimAt sig ctx goal e b = do
    (_, _, eTy) <- dElemTy sig ctx e
    eTy' <- kWhnfT sig eTy
    case eTy' of
      Squash a => do
        okQ <- kIsProp sig ctx goal (Nd [] [])
        if okQ then pure () else kerr "kernel: squash-elim at a non-prop goal"
        _ <- dElemAt sig (ctx :< a) b (substTy goal Wk)
        pure ()
      _ => kerr "kernel: squash-elim scrutinee has a non-∥∥ type"

  ||| el-nu-coind at an equation prop over a ν-type: the invariant,
  ||| the endpoint proof and the one-step closure at the relator.
  coindAt : Sig -> Ctx -> Ty -> Drv -> Drv -> Drv -> KM ()
  coindAt sig ctx prop r p q = do
    prop' <- kWhnfT sig prop
    case prop' of
      Elem.EqTy l rhs ety => do
        ety' <- kWhnfT sig ety
        case ety' of
          NuTy f => do
            let nuT = NuTy f
            rel <- dElemAt sig (ctx :< nuT :< substTy nuT Wk) r PropTy
            _ <- dElemAt sig ctx p (substElem rel (Ext (Ext Id l) rhs))
            let ctx3 = ctx :< nuT :< substTy nuT Wk :< rel
            let wk3 = Chain Wk (Chain Wk Wk)
            let f3 = substPoly f wk3
            let r3 = substElem rel (under (under wk3))
            _ <- dElemAt sig ctx3 q (liftPoly f3 r3 (Out (CtxVar 2)) (Out (CtxVar 1)))
            pure ()
          _ => kerr "kernel: coinduction at an equation over a non-ν type"
      _ => kerr "kernel: coinduction at a non-equality prop"

-- ----- entry points on derivations -----

||| A definition item as derivations: the telescope, the type, the
||| body; the entry extends Σ with their ERASURES.
export
kCheckDefDrv : Sig -> Nat -> String -> List Drv -> Drv -> Drv -> Either KErr SigEntry
kCheckDefDrv sig fuel name tele dty body =
  map fst $ runKM (do
    ctx <- tele' [<] tele
    ty <- dType sig ctx dty
    t <- dElemAt sig ctx body ty
    pure (SigDef ctx name t ty)) fuel
 where
  tele' : Ctx -> List Drv -> KM Ctx
  tele' ctx [] = pure ctx
  tele' ctx (d :: rest) = do
    t <- dType sig ctx d
    tele' (ctx :< t) rest

export
kCheckTyDefDrv : Sig -> Nat -> String -> List Drv -> Drv -> Either KErr SigEntry
kCheckTyDefDrv sig fuel name tele dty =
  map fst $ runKM (do
    ctx <- tele' [<] tele
    ty <- dType sig ctx dty
    pure (SigDef ctx name ty TopTy)) fuel
 where
  tele' : Ctx -> List Drv -> KM Ctx
  tele' ctx [] = pure ctx
  tele' ctx (d :: rest) = do
    t <- dType sig ctx d
    tele' (ctx :< t) rest

||| An equation proof read against its sides (the engine's check).
export
kCheckEqDrv : Sig -> Ctx -> Nat -> Drv -> Elem -> Elem -> Ty -> Either KErr ()
kCheckEqDrv sig ctx fuel d l r ty =
  map fst (runKM (do
    lJ <- kJoinElem sig l
    rJ <- kJoinElem sig r
    dAt sig ctx d lJ rJ ty) fuel)

-- ===== Re-derivation: a term with its skeleton, or a proof term, as a derivation =====
--
-- The bridge of the migration (§10.6, §10.8 step 3): what the
-- elaborator emits today — a core term aligned with a skeleton, and
-- proof terms — is re-derived into the grammar of §10 by the same
-- bidirectional walk the checker takes, building instead of
-- checking. It is what a solved hole's value will go through once the
-- elaborator emits derivations; until then it is the CANARY: every
-- item and every discharge the kernel accepts is re-derived and read
-- by the derivation readings, and a disagreement is audited.

zipWithIndex : Nat -> List a -> List (Nat, a)
zipWithIndex _ [] = []
zipWithIndex i (x :: xs) = (i, x) :: zipWithIndex (S i) xs

||| A telescope re-derived entry by entry (an item's parameters).
rdTeleItem : Sig -> Ctx -> List (Ty, Skel) -> KM (Ctx, List Drv)

dTrans : Drv -> Drv -> Drv
dTrans DReflx q = q
dTrans p DReflx = p
dTrans p q = DTrans p q

congOfD : Drv -> Drv -> Drv
congOfD DReflx _ = DReflx
congOfD _ node = node

mutual
  ||| Head exposure with its δ PROVED (the proof library's exposeK, on
  ||| derivations): the term taken to its β-whnf with every definition
  ||| unfolded on the way to the head as a δ leaf inside the node of
  ||| its position, and the proof of t ≐ exposed (refl when β alone
  ||| reached it).
  rdExpose : Sig -> Ctx -> Elem -> KM (Elem, Drv)
  rdExpose sig ctx t = go t
   where
    go : Elem -> KM (Elem, Drv)
    go (SigVar x es) =
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef delta _ a _) => do
          qs <- rdSpine sig ctx (toList delta) (toList es) (Nd [] [])
          (r, p) <- go (substElem a (embed es))
          pure (r, dTrans (DDelta x qs) p)
        _ => pure (SigVar x es, DReflx)
    go (PiApp f e) = do
      (f', p1) <- go f
      case f' of
        PiIntro g => do
          (r, p2) <- go (substElem g (Ext Id e))
          pure (r, dTrans (congOfD p1 (DApp p1 DReflx)) p2)
        _ => pure (PiApp f' e, congOfD p1 (DApp p1 DReflx))
    go (Let a b) = go (substElem b (Ext (Ext Id a) Star))
    go (NatElim z st u) = do
      (u', p1) <- go u
      let node = congOfD p1 (DNatElim Nothing DReflx DReflx p1)
      case u' of
        NatIntro0 => do (r, p2) <- go z; pure (r, dTrans node p2)
        NatIntro1 n => do (r, p2) <- go (substElem st (Ext (Ext Id n) (NatElim z st n))); pure (r, dTrans node p2)
        _ => pure (NatElim z st u', node)
    go (SigmaElim1 u) = do
      (u', p1) <- go u
      case u' of
        SigmaIntro a _ => do (r, p2) <- go a; pure (r, dTrans (congOfD p1 (DProj1 p1)) p2)
        _ => pure (SigmaElim1 u', congOfD p1 (DProj1 p1))
    go (SigmaElim2 u) = do
      (u', p1) <- go u
      case u' of
        SigmaIntro _ b => do (r, p2) <- go b; pure (r, dTrans (congOfD p1 (DProj2 p1)) p2)
        _ => pure (SigmaElim2 u', congOfD p1 (DProj2 p1))
    go (SumElim l r u) = do
      (u', p1) <- go u
      let node = congOfD p1 (DSumElim Nothing DReflx DReflx p1)
      case u' of
        Inj1 a => do (r', p2) <- go (substElem l (Ext Id a)); pure (r', dTrans node p2)
        Inj2 b => do (r', p2) <- go (substElem r (Ext Id b)); pure (r', dTrans node p2)
        _ => pure (SumElim l r u', node)
    go (QuotElim f q) = do
      (q', p1) <- go q
      case q' of
        Class a => do (r, p2) <- go (substElem f (Ext Id a)); pure (r, dTrans (congOfD p1 (DQuotElim Nothing Nothing DReflx p1)) p2)
        _ => pure (QuotElim f q', congOfD p1 (DQuotElim Nothing Nothing DReflx p1))
    go (Out u) = do
      (u', p1) <- go u
      case u' of
        Corec p a f x => do
          (r, p2) <- go (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
          pure (r, dTrans (congOfD p1 (DOut p1)) p2)
        _ => pure (Out u', congOfD p1 (DOut p1))
    go (QElim sg k fs es w) = do
      (w', p1) <- go w
      let node = congOfD p1 (DQElim sg k [] [] (map (const DReflx) fs) (map (const DReflx) (toList es)) p1)
      case w' of
        QCtor sgW c theta =>
          if sgW == sg
            then case qElimBetaRhs sg fs c theta of
                   Right rhs => do (r, p2) <- go rhs; pure (r, dTrans node p2)
                   Left _ => pure (QElim sg k fs es w', node)
            else pure (QElim sg k fs es w', node)
        _ => pure (QElim sg k fs es w', node)
    go (Squash u) = do
      (u', p1) <- go u
      let node = congOfD p1 (DSquash p1)
      pure (case u' of
              Elem.EqTy _ _ _ => (u', node)
              Squash _ => (u', node)
              _ => (Squash u', node))
    go e = pure (e, DReflx)

  ||| A term checked at a type whose SHAPE a definition may hide: the
  ||| type exposed by δ (proved) when the β-whnf lacks it, the term
  ||| checked at the exposed spelling under the ascription.
  rdShaped : Sig -> Ctx -> Ty -> (Ty -> Maybe a) -> (a -> KM Drv) -> KM Drv
  rdShaped sig ctx ty pick k = do
    ty' <- kWhnfT sig ty
    case pick ty' of
      Just parts => k parts
      Nothing => do
        (tyX, pt) <- rdExpose sig ctx ty
        tyW <- kWhnfT sig tyX
        case (pick tyW, pt) of
          (Just parts, DReflx) => k parts
          (Just parts, _) => do
            d <- k parts
            dX <- rdTypeBare sig ctx tyX
            pure (DAscribe d dX (Just pt))
          _ => kerr "re-derive: no shape at the type [\{show tyW}]"

  ||| A bare type re-derived as an annotation: β-joined first (an
  ||| annotation is a representative; a redex in it has no derivation
  ||| of its own).
  rdTypeBare : Sig -> Ctx -> Ty -> KM Drv
  rdTypeBare sig ctx t = do
    t' <- kJoinTy sig t
    rdType sig ctx t' (Nd [] [])

  ||| A term re-derived in CHECKING mode at ty, its skeleton read for
  ||| the payloads.
  rdCheck : Sig -> Ctx -> Elem -> Skel -> Ty -> KM Drv
  rdCheck sig ctx e sk ty =
    case takeP pSwitch sk of
      Just (cert, sk') => do
        (d, inferred) <- rdInfer sig ctx e sk'
        b <- rdPrfJ sig ctx cert inferred ty TopTy
        pure (DConv d Nothing b)
      Nothing => case takeP pExpose sk of
        Just ((tyX, cert), sk') => do
          b <- rdPrfJ sig ctx cert ty tyX TopTy
          dX <- rdTypeBare sig ctx tyX
          d <- rdCheck sig ctx e sk' tyX
          pure (DAscribe d dX (Just b))
        Nothing => rdCheckAt sig ctx e sk ty

  ||| Checking mode, the switch and exposure payloads consumed.
  rdCheckAt : Sig -> Ctx -> Elem -> Skel -> Ty -> KM Drv
  rdCheckAt sig ctx e sk ty = case e of
    PiIntro f => rdShaped sig ctx ty (\t => case t of PiTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      DLam Nothing <$> rdCheck sig (ctx :< a) f (skelChild 0 sk) b
    SigmaIntro u v => rdShaped sig ctx ty (\t => case t of SigmaTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      [| DPair (pure Nothing) (rdCheck sig ctx u (skelChild 0 sk) a)
               (rdCheck sig ctx v (skelChild 1 sk) (substTy b (Ext Id u))) |]
    Star => case takeP pReflEq sk of
      Just (cert, _) => do
        ty' <- kWhnfT sig ty
        case ty' of
          Elem.EqTy l r t => DStar Nothing <$> rdPrfJ sig ctx cert l r t
          _ => kerr "re-derive: refl-eq at a non-equality prop"
      Nothing => case takeP pNuCoind sk of
        Just ((r, skR, pw, skp, qw, skq), _) => do
          ty' <- kWhnfT sig ty
          case ty' of
            Elem.EqTy l rhs ety => do
              ety' <- kWhnfT sig ety
              case ety' of
                NuTy f => do
                  let nuT = NuTy f
                  dr <- rdCheck sig (ctx :< nuT :< substTy nuT Wk) r skR PropTy
                  dp <- rdCheck sig ctx pw skp (substElem r (Ext (Ext Id l) rhs))
                  let ctx3 = ctx :< nuT :< substTy nuT Wk :< r
                  let wk3 = Chain Wk (Chain Wk Wk)
                  dq <- rdCheck sig ctx3 qw skq (liftPoly (substPoly f wk3) (substElem r (under (under wk3))) (Out (CtxVar 2)) (Out (CtxVar 1)))
                  pure (DCoind Nothing dr dp dq)
                _ => kerr "re-derive: coinduction over a non-ν type"
            _ => kerr "re-derive: coinduction at a non-equality prop"
        Nothing => case takeP pSquashWit sk of
          Just ((wit, witSk), _) => do
            ty' <- kWhnfT sig ty
            case ty' of
              Squash sq => DSq <$> rdCheck sig ctx wit witSk sq
              _ => kerr "re-derive: ⋆ at a non-∥∥ type"
          Nothing => case takeP pSquashElim sk of
            Just ((scrut, scrutSk, mexp, body, bodySk, _), _) => do
              (de0, sTy0) <- rdInfer sig ctx scrut scrutSk
              (de, sTy) <- the (KM (Drv, Ty)) $ case mexp of
                Nothing => pure (de0, sTy0)
                Just (tyX, c) => do
                  b <- rdPrfJ sig ctx c sTy0 tyX TopTy
                  dX <- rdType sig ctx tyX (Nd [] [])
                  pure (DConv de0 (Just dX) b, tyX)
              sTy' <- kWhnfT sig sTy
              case sTy' of
                Squash a => do
                  db <- rdCheck sig (ctx :< a) body bodySk (substTy ty Wk)
                  pure (DSquashElim Nothing de db)
                _ => kerr "re-derive: squash-elim scrutinee has a non-∥∥ type"
            Nothing => kerr "re-derive: ⋆ without a payload"
    Inj1 a => rdShaped sig ctx ty (\t => case t of SumTy d _ => Just d; _ => Nothing) $ \dom =>
      DInj1 Nothing <$> rdCheck sig ctx a (skelChild 0 sk) dom
    Inj2 a => rdShaped sig ctx ty (\t => case t of SumTy _ c => Just c; _ => Nothing) $ \cod =>
      DInj2 Nothing <$> rdCheck sig ctx a (skelChild 0 sk) cod
    Class a => rdShaped sig ctx ty (\t => case t of QuotTy d _ => Just d; _ => Nothing) $ \dom =>
      DClass Nothing <$> rdCheck sig ctx a (skelChild 0 sk) dom
    -- an eliminator with no motive payload, checked at a type: the
    -- constant-motive instance (§10.3's checking sugar)
    NatElim z st t => if isJust (takeP pMotive sk) then fst <$> rdInfer sig ctx e sk else do
      dz <- rdCheck sig ctx z (skelChild 0 sk) ty
      ds <- rdCheck sig (ctx :< NatTy :< substTy ty Wk) st (skelChild 1 sk) (weakenTyN 2 ty)
      dt <- rdCheck sig ctx t (skelChild 2 sk) NatTy
      pure (DNatElim Nothing dz ds dt)
    SumElim l r t => if isJust (takeP pMotive sk) then fst <$> rdInfer sig ctx e sk else do
      (dt, tTy) <- rdInfer sig ctx t (skelChild 2 sk)
      (tTyX, pt) <- rdExpose sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      dt' <- case pt of
               DReflx => pure dt
               _ => do dX <- rdTypeBare sig ctx tTyX; pure (DConv dt (Just dX) pt)
      case tTy' of
        SumTy a b => do
          dl <- rdCheck sig (ctx :< a) l (skelChild 0 sk) (substTy ty Wk)
          dr <- rdCheck sig (ctx :< b) r (skelChild 1 sk) (substTy ty Wk)
          pure (DSumElim Nothing dl dr dt')
        _ => kerr "re-derive: ⊎-elim of a non-⊎ scrutinee"
    QuotElim f q => if isJust (takeP pMotive sk) then fst <$> rdInfer sig ctx e sk else do
      (dq, qTy) <- rdInfer sig ctx q (skelChild 1 sk)
      (qTyX, pq) <- rdExpose sig ctx qTy
      qTy' <- kWhnfT sig qTyX
      dq' <- case pq of
               DReflx => pure dq
               _ => do dX <- rdTypeBare sig ctx qTyX; pure (DConv dq (Just dX) pq)
      case qTy' of
        QuotTy a _ => do
          df <- rdCheck sig (ctx :< a) f (skelChild 0 sk) (substTy ty Wk)
          pure (DQuotElim Nothing Nothing df dq')
        _ => kerr "re-derive: quot-elim of a non-quotient"
    Corec p aC f x =>
      [| DCorec (pure p) (rdCheck sig ctx aC (skelChild 0 sk) UniverseTy)
                (rdCheck sig (ctx :< aC) f (skelChild 1 sk) (substTy (reflectPoly p aC) Wk))
                (rdCheck sig ctx x (skelChild 2 sk) aC) |]
    ZeroElim t => DZeroElim Nothing <$> rdCheck sig ctx t (skelChild 0 sk) ZeroTy
    Let a b => do
      (da, aTy) <- rdInfer sig ctx a (skelChild 0 sk)
      let hyp = Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk)
      db <- rdCheck sig (ctx :< aTy :< hyp) b (skelChild 1 sk) (weakenTyN 2 ty)
      pure (DLet da db)
    QCtor sgC c theta => rdShaped sig ctx ty (\t => case t of QSort _ _ _ => Just (); _ => Nothing) $ \_ => do
      sgC' <- kJoinQSig sig sgC
      entry <- case qEntry sgC' c of
                 Just x => pure x
                 Nothing => kerr "re-derive: constructor position out of range"
      (tel, _, _) <- liftQ (reflTel sgC' (qwAt c) entry)
      DCtor sgC c <$> rdTele sig ctx tel (toList theta) sk
    _ => do
      (d, t) <- rdInfer sig ctx e sk
      ok <- tyAgree sig ty t
      if ok then pure d else do
        -- a δ-apart spelling: the switch proof by δ-rounds on both
        -- sides (the proof library's deltaPrf)
        mp <- rdBridge sig t ty
        case mp of
          Just b => pure (DConv d Nothing b)
          Nothing => pure d

  ||| A proof of a ≐ b by δ-rounds on both sides: every definition
  ||| occurring unfolds at once, the sides β-join, repeat while new
  ||| names appear. Nothing when the sides never meet.
  rdBridge : Sig -> Elem -> Elem -> KM (Maybe Drv)
  rdBridge sig a0 b0 = do
    aJ <- kJoinElem sig a0
    bJ <- kJoinElem sig b0
    go 64 aJ bJ [] []
   where
    chain : List Drv -> Drv
    chain [] = DReflx
    chain (p :: ps) = DTrans p (chain ps)
    go : Nat -> Elem -> Elem -> List Drv -> List Drv -> KM (Maybe Drv)
    go k a b la lb =
      if a == b then pure (Just (dTrans (chain (reverse la)) (DSym (chain (reverse lb)))))
      else case k of
        Z => pure Nothing
        S k' => do
          na <- defNamesK sig a
          nb <- defNamesK sig b
          let ns = nub (na ++ nb)
          case ns of
            [] => pure Nothing
            _ => do
              a' <- unfoldAllK sig ns a >>= kJoinElem sig
              b' <- unfoldAllK sig ns b >>= kJoinElem sig
              if a' == a && b' == b then pure Nothing
                else go k' a' b' (DDeltaAll ns :: la) (DDeltaAll ns :: lb)

  ||| The definition names a term references (carried signatures
  ||| included).
  defNamesK : Sig -> Elem -> KM (List String)
  defNamesK sig t = do
    ns <- traverse isDef (nub (names t []))
    pure (catMaybes ns)
   where
    isDef : String -> KM (Maybe String)
    isDef x = kSigLookup sig x >>= \e => pure (case e of
                                                Just (SigDef _ _ _ _) => Just x
                                                _ => Nothing)
    pieces : QSig -> List Elem
    pieces g = fst (runState [] (traverseQSig (\e => do modify (e ::); pure e) g))
    names : Elem -> List String -> List String
    names (SigVar x es) acc = foldl (\a, e => names e a) (x :: acc) (toList es)
    names (ZeroElim u) acc = names u acc
    names (NatIntro1 u) acc = names u acc
    names (NatElim z st u) acc = names z (names st (names u acc))
    names (PiIntro f) acc = names f acc
    names (PiApp f e) acc = names f (names e acc)
    names (Let a b) acc = names a (names b acc)
    names (SigmaIntro u v) acc = names u (names v acc)
    names (SigmaElim1 u) acc = names u acc
    names (SigmaElim2 u) acc = names u acc
    names (Inj1 u) acc = names u acc
    names (Inj2 u) acc = names u acc
    names (SumElim l r u) acc = names l (names r (names u acc))
    names (Elem.PiTy a c) acc = names a (names c acc)
    names (Elem.SigmaTy a c) acc = names a (names c acc)
    names (Elem.SumTy a c) acc = names a (names c acc)
    names (Elem.EqTy l r u) acc = names l (names r (names u acc))
    names (QuotTy a r) acc = names a (names r acc)
    names (Class a) acc = names a acc
    names (QuotElim f q) acc = names f (names q acc)
    names (Squash u) acc = names u acc
    names (QSort sg _ es) acc = foldl (\a, e => names e a) acc (pieces sg ++ toList es)
    names (QCtor sg _ es) acc = foldl (\a, e => names e a) acc (pieces sg ++ toList es)
    names (QElim sg _ _ es w) acc = foldl (\a, e => names e a) (names w acc) (pieces sg ++ toList es)
    names (Out u) acc = names u acc
    names (Corec _ a f x) acc = names a (names f (names x acc))
    names _ acc = acc

  ||| A term re-derived in INFERENCE mode, with the type it derives.
  rdInfer : Sig -> Ctx -> Elem -> Skel -> KM (Drv, Ty)
  rdInfer sig ctx e sk =
    case takeP pIntroTy sk of
      Just ((ty, tySk), sk') => do
        d <- rdCheck sig ctx e sk' ty
        dT <- rdType sig ctx ty tySk
        pure (DAscribe d dT Nothing, ty)
      Nothing => case e of
        CtxVar i => case ctxLookup ctx i of
          Just ty => pure (DVar i, ty)
          Nothing => kerr "re-derive: variable out of bounds"
        SigVar x es =>
          kSigLookup sig x >>= \entryX => case entryX of
            Just (SigDef delta _ _ ty) => refAt delta ty
            Just (SigDecl delta _ ty) => refAt delta ty
            _ => kerr "re-derive: unknown or non-term signature name '\{x}'"
        OneIntro => pure (DUnit, OneTy)
        NatIntro0 => pure (DZero, NatTy)
        NatIntro1 t => do d <- rdCheck sig ctx t (skelChild 0 sk) NatTy; pure (DSuc d, NatTy)
        PiApp f a => do
          (df, fTy) <- scrut f (skelChild 0 sk)
          fTy' <- kWhnfT sig fTy
          case fTy' of
            PiTy dom cod => do
              da <- rdCheck sig ctx a (skelChild 1 sk) dom
              pure (DApp df da, substTy cod (Ext Id a))
            _ => kerr "re-derive: applying a non-function"
        SigmaElim1 t => do
          (dt, tTy) <- scrut t (skelChild 0 sk)
          tTy' <- kWhnfT sig tTy
          case tTy' of
            SigmaTy a _ => pure (DProj1 dt, a)
            _ => kerr "re-derive: projecting a non-pair"
        SigmaElim2 t => do
          (dt, tTy) <- scrut t (skelChild 0 sk)
          tTy' <- kWhnfT sig tTy
          case tTy' of
            SigmaTy _ b => pure (DProj2 dt, substTy b (Ext Id (SigmaElim1 t)))
            _ => kerr "re-derive: projecting a non-pair"
        Out t => do
          (dt, tTy) <- scrut t (skelChild 0 sk)
          tTy' <- kWhnfT sig tTy
          case tTy' of
            NuTy f => pure (DOut dt, reflectPoly f (Elem.NuTy f))
            _ => kerr "re-derive: observing a non-ν element"
        Let a b => do
          (da, aTy) <- rdInfer sig ctx a (skelChild 0 sk)
          let hyp = Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk)
          (db, bTy) <- rdInfer sig (ctx :< aTy :< hyp) b (skelChild 1 sk)
          pure (DLet da db, substTy bTy (Ext (Ext Id a) Star))
        NatElim z st t => case takeP pMotive sk of
          Just ((mot, motSk), _) => do
            dm <- rdType sig (ctx :< NatTy) mot motSk
            dz <- rdCheck sig ctx z (skelChild 0 sk) (substTy mot (Ext Id NatIntro0))
            ds <- rdCheck sig (ctx :< NatTy :< mot) st (skelChild 1 sk) (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
            dt <- rdCheck sig ctx t (skelChild 2 sk) NatTy
            pure (DNatElim (Just dm) dz ds dt, substTy mot (Ext Id t))
          -- no motive (a stuck eliminator in head position, produced by
          -- normalization): the CONSTANT motive, read off the base
          -- case's inferred type (A1's inference-position twin)
          Nothing => do
            (_, zTy) <- rdInfer sig ctx z (skelChild 0 sk)
            let mot = substTy zTy Wk
            dm <- rdTypeBare sig (ctx :< NatTy) mot
            dz <- rdCheck sig ctx z (skelChild 0 sk) zTy
            ds <- rdCheck sig (ctx :< NatTy :< mot) st (skelChild 1 sk) (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
            dt <- rdCheck sig ctx t (skelChild 2 sk) NatTy
            pure (DNatElim (Just dm) dz ds dt, zTy)
        SumElim l r t => case takeP pMotive sk of
          Just ((mot, motSk), _) => do
            (dt, tTy) <- scrut t (skelChild 2 sk)
            tTy' <- kWhnfT sig tTy
            case tTy' of
              SumTy a b => do
                dm <- rdType sig (ctx :< SumTy a b) mot motSk
                dl <- rdCheck sig (ctx :< a) l (skelChild 0 sk) (substTy mot (Ext Wk (Inj1 (CtxVar 0))))
                dr <- rdCheck sig (ctx :< b) r (skelChild 1 sk) (substTy mot (Ext Wk (Inj2 (CtxVar 0))))
                pure (DSumElim (Just dm) dl dr dt, substTy mot (Ext Id t))
              _ => kerr "re-derive: ⊎-elim of a non-⊎ scrutinee"
          Nothing => do
            -- constant motive from the left branch's type, when it does
            -- not mention the branch variable
            (dt, tTy) <- scrut t (skelChild 2 sk)
            tTy' <- kWhnfT sig tTy
            case tTy' of
              SumTy a b => do
                (_, lTy) <- rdInfer sig (ctx :< a) l (skelChild 0 sk)
                base <- case strengthenElem 0 lTy of
                          Just x => pure x
                          Nothing => kerr "re-derive: ⊎-elim without a motive, branch type depends on the branch variable"
                let mot = substTy base Wk
                dm <- rdTypeBare sig (ctx :< SumTy a b) mot
                dl <- rdCheck sig (ctx :< a) l (skelChild 0 sk) (substTy base Wk)
                dr <- rdCheck sig (ctx :< b) r (skelChild 1 sk) (substTy base Wk)
                pure (DSumElim (Just dm) dl dr dt, base)
              _ => kerr "re-derive: ⊎-elim of a non-⊎ scrutinee"
        QuotElim f q => case (takeP pMotive sk, takeP pWD sk) of
          (Just ((mot, motSk), _), Just (wd, _)) => do
            (dq, qTy) <- scrut q (skelChild 1 sk)
            qTy' <- kWhnfT sig qTy
            case qTy' of
              QuotTy a rel => do
                dm <- rdType sig (ctx :< QuotTy a rel) mot motSk
                df <- rdCheck sig (ctx :< a) f (skelChild 0 sk) (substTy mot (Ext Wk (Class (CtxVar 0))))
                let wk3 = Chain Wk (Chain Wk Wk)
                dwd <- rdPrfJ sig (ctx :< a :< substTy a Wk :< rel) wd
                         (substElem f (Ext wk3 (CtxVar 2))) (substElem f (Ext wk3 (CtxVar 1)))
                         (substTy mot (Ext wk3 (Class (CtxVar 2))))
                pure (DQuotElim (Just dm) (Just dwd) df dq, substTy mot (Ext Id q))
              _ => kerr "re-derive: quot-elim of a non-quotient"
          (Nothing, _) => do
            -- constant motive from the case's type; well-definedness
            -- only when the motive is a prop
            (dq, qTy) <- scrut q (skelChild 1 sk)
            qTy' <- kWhnfT sig qTy
            case qTy' of
              QuotTy a rel => do
                (_, fTy) <- rdInfer sig (ctx :< a) f (skelChild 0 sk)
                base <- case strengthenElem 0 fTy of
                          Just x => pure x
                          Nothing => kerr "re-derive: quot-elim without a motive, case type depends on the representative"
                let mot = substTy base Wk
                dm <- rdTypeBare sig (ctx :< QuotTy a rel) mot
                df <- rdCheck sig (ctx :< a) f (skelChild 0 sk) (substTy base Wk)
                pure (DQuotElim (Just dm) Nothing df dq, base)
              _ => kerr "re-derive: quot-elim of a non-quotient"
          _ => kerr "re-derive: quot-elim with a motive but no well-definedness"
        QSort sg k es => do
          sortE <- case qEntry sg k of
                     Just x => pure x
                     Nothing => kerr "re-derive: sort position out of range"
          (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
          ds <- rdTele sig ctx tel (toList es) sk
          small <- kTry (kQSigSmall sig ctx sg)
          pure (DSort sg k ds, if small then UniverseTy else TopTy)
        QElim sg k mths es w => case (takeP pQMotives sk, takeP pQCoh sk) of
          (Just ((mots, motSks), _), Just (cohs, sk')) => do
            let sortPs = qPositions QKSort sg
            let pointPs = qPositions QKPoint sg
            let eqPs = qPositions QKEq sg
            dcs <- traverse (\(sj, (mot, motSk)) => do
                     sjE <- case qEntry sg sj of
                              Just x => pure x
                              Nothing => kerr "re-derive: sort out of range"
                     (tel, wEnd, _) <- liftQ (reflTel sg (qwAt sj) sjE)
                     let mctx = foldl (:<) ctx tel
                     let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
                     rdType sig (mctx :< selfTy) mot motSk)
                   (zip sortPs (zip mots (motSks ++ replicate (length mots) (Nd [] []))))
            dms <- traverse (\(j, (cj, m)) => do
                     mty <- liftQ (methodTy sg mots cj)
                     rdCheck sig ctx m (skelChild j sk') mty) (zipWithIndex 0 (zip pointPs mths))
            dcohs <- traverse (\(ej, coh) => do
                       (dtel, _, lhs, rhs, cty) <- liftQ (coherenceAt sg mots mths ej)
                       rdPrfJ sig (foldl (:<) ctx dtel) coh lhs rhs cty) (zip eqPs cohs)
            let nM = length pointPs
            let skRest = case sk' of
                           Nd ps cs => Nd ps (drop nM cs)
            sortE <- case qEntry sg k of
                       Just x => pure x
                       Nothing => kerr "re-derive: eliminator sort out of range"
            (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
            des <- rdTele sig ctx tel (toList es) skRest
            dw <- rdCheck sig ctx w (skelChild (length (toList es)) skRest) (QSort sg k es)
            o <- case qOrdinal QKSort sg k of
                   Just x => pure x
                   Nothing => kerr "re-derive: eliminator sort ordinal"
            motK <- case getAt o mots of
                      Just m => pure m
                      Nothing => kerr "re-derive: eliminator motive missing"
            pure (DQElim sg k dcs dcohs dms des dw, substTy motK (Ext (foldl Ext Id (toList es)) w))
          _ => kerr "re-derive: QIIT eliminator without motives or coherences"
        Elem.ZeroTy => pure (DZeroTy, UniverseTy)
        Elem.OneTy => pure (DOneTy, UniverseTy)
        Elem.NatTy => pure (DNatTy, UniverseTy)
        Elem.PiTy a b => do
          da <- comp ctx a (skelChild 0 sk)
          db <- comp (ctx :< a) b (skelChild 1 sk)
          pure (DPi da db, UniverseTy)
        Elem.SigmaTy a b => do
          da <- comp ctx a (skelChild 0 sk)
          db <- comp (ctx :< a) b (skelChild 1 sk)
          pure (DSigma da db, UniverseTy)
        Elem.SumTy a b => do
          da <- comp ctx a (skelChild 0 sk)
          db <- comp ctx b (skelChild 1 sk)
          pure (DSum da db, UniverseTy)
        Elem.NuTy f => pure (DNu f, UniverseTy)
        QuotTy a r => do
          da <- comp ctx a (skelChild 0 sk)
          dr <- rdCheck sig (ctx :< a :< substTy a Wk) r (skelChild 1 sk) PropTy
          pure (DQuot da dr, UniverseTy)
        Squash t => do
          dt <- rdType sig ctx t (skelChild 0 sk)
          pure (DSquash dt, PropTy)
        Elem.EqTy l r t => do
          dt <- rdType sig ctx t (skelChild 2 sk)
          dl <- rdCheck sig ctx l (skelChild 0 sk) t
          dr <- rdCheck sig ctx r (skelChild 1 sk) t
          pure (DEq dl dr dt, PropTy)
        _ => kerr "re-derive: term not inferable [\{show e}]"
   where
    -- a code component in inference position: checked at 𝕌, ascribed
    comp : Ctx -> Elem -> Skel -> KM Drv
    comp cx a ask = do
      d <- rdCheck sig cx a ask UniverseTy
      pure (DAscribe d DUniverse Nothing)

    refAt : Ctx -> Ty -> KM (Drv, Ty)
    refAt delta ty = do
      ds <- rdSpine sig ctx (toList delta) (case e of
                                              SigVar _ es => toList es
                                              _ => []) sk
      pure (DRef (case e of SigVar x _ => x; _ => "") ds,
            substTy ty (embed (case e of SigVar _ es => es; _ => [<])))
    -- a scrutinee, its type exposed by the scrut payload, or by δ
    -- (proved) when the head's shape is still hidden
    scrut : Elem -> Skel -> KM (Drv, Ty)
    scrut t tsk = do
      (dt, tTy) <- rdInfer sig ctx t tsk
      (dt1, tTy1) <- the (KM (Drv, Ty)) $ case takeP pScrut sk of
        Just ((tyX, c), _) => do
          b <- rdPrfJ sig ctx c tTy tyX TopTy
          dX <- rdTypeBare sig ctx tyX
          pure (DConv dt (Just dX) b, tyX)
        Nothing => pure (dt, tTy)
      tW <- kWhnfT sig tTy1
      case tW of
        PiTy _ _ => pure (dt1, tTy1)
        SigmaTy _ _ => pure (dt1, tTy1)
        NuTy _ => pure (dt1, tTy1)
        SumTy _ _ => pure (dt1, tTy1)
        QuotTy _ _ => pure (dt1, tTy1)
        _ => do
          (tyX, pt) <- rdExpose sig ctx tTy1
          case pt of
            DReflx => pure (dt1, tTy1)
            _ => do dX <- rdTypeBare sig ctx tyX; pure (DConv dt1 (Just dX) pt, tyX)

  ||| A type term re-derived as an annotation (formation, §8).
  rdType : Sig -> Ctx -> Ty -> Skel -> KM Drv
  rdType sig ctx t sk = case t of
    ZeroTy => pure DZeroTy
    OneTy => pure DOneTy
    NatTy => pure DNatTy
    UniverseTy => pure DUniverse
    PropTy => pure DProp
    TopTy => pure DTop
    PiTy a b => [| DPi (rdType sig ctx a (skelChild 0 sk)) (rdType sig (ctx :< a) b (skelChild 1 sk)) |]
    SigmaTy a b => [| DSigma (rdType sig ctx a (skelChild 0 sk)) (rdType sig (ctx :< a) b (skelChild 1 sk)) |]
    SumTy a b => [| DSum (rdType sig ctx a (skelChild 0 sk)) (rdType sig ctx b (skelChild 1 sk)) |]
    Elem.EqTy l r u => [| DEq (rdCheck sig ctx l (skelChild 0 sk) u) (rdCheck sig ctx r (skelChild 1 sk) u) (rdType sig ctx u (skelChild 2 sk)) |]
    Squash u => DSquash <$> rdType sig ctx u (skelChild 0 sk)
    QuotTy a r => [| DQuot (rdType sig ctx a (skelChild 0 sk)) (rdCheck sig (ctx :< a :< substTy a Wk) r (skelChild 1 sk) PropTy) |]
    NuTy f => pure (DNu f)
    QSort _ _ _ => fst <$> rdInfer sig ctx t sk
    SigVar x es =>
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef delta _ _ TopTy) => DRef x <$> rdSpine sig ctx (toList delta) (toList es) sk
        Just (SigDecl delta _ TopTy) => DRef x <$> rdSpine sig ctx (toList delta) (toList es) sk
        _ => cumul
    _ => cumul
   where
    -- cumulativity: a code or a prop in type position, checked at 𝕌
    -- then at Ω (as kCheckTyK falls through), ascribed
    cumul : KM Drv
    cumul = kOrElse (at UniverseTy DUniverse) (at PropTy DProp)
     where
      -- built AND read at the classifier (the build alone cannot tell
      -- a code from a prop)
      at : Ty -> Drv -> KM Drv
      at cls dcls = do
        d <- rdCheck sig ctx t sk cls
        _ <- dCheck sig ctx d cls
        pure (DAscribe d dcls Nothing)

  ||| A reference's spine at its telescope, each entry with its
  ||| skeleton child.
  rdSpine : Sig -> Ctx -> List Ty -> List Elem -> Skel -> KM (List Drv)
  rdSpine sig ctx delta es sk =
    if length es /= length delta then kerr "re-derive: substitution length mismatch"
      else go 0 es delta
   where
    go : Nat -> List Elem -> List Ty -> KM (List Drv)
    go i [] [] = pure []
    go i (e :: erest) (ty :: tyrest) = do
      let pre = take i es
      d <- rdCheck sig ctx e (skelChild i sk) (substTy ty (embed (cast pre)))
      ds <- go (S i) erest tyrest
      pure (d :: ds)
    go _ _ _ = kerr "re-derive: substitution length mismatch"

  ||| A spine at a reflected telescope, each entry with its skeleton child.
  rdTele : Sig -> Ctx -> List Ty -> List Elem -> Skel -> KM (List Drv)
  rdTele sig ctx tel es sk =
    if length es /= length tel then kerr "re-derive: telescope spine length mismatch"
      else go 0 es
   where
    go : Nat -> List Elem -> KM (List Drv)
    go i [] = pure []
    go i (e :: rest) = do
      ty <- case telInst tel i es of
              Just t => pure t
              Nothing => kerr "re-derive: telescope entry type undetermined"
      d <- rdCheck sig ctx e (skelChild i sk) ty
      ds <- go (S i) rest
      pure (d :: ds)

  ||| A proof term re-derived against known sides, β-JOINED first (the
  ||| reader joins them before reading; a redex in a raw side is never
  ||| what a node meets).
  rdPrfJ : Sig -> Ctx -> Prf -> Elem -> Elem -> Ty -> KM Drv
  rdPrfJ sig ctx prf l r ty = do
    lJ <- kJoinElem sig l
    rJ <- kJoinElem sig r
    rdPrf sig ctx prf (Just lJ) (Just rJ) ty

  ||| A proof term re-derived, the goal's sides where known (Nothing
  ||| under a computed middle) and its type.
  rdPrf : Sig -> Ctx -> Prf -> Maybe Elem -> Maybe Elem -> Ty -> KM Drv
  rdPrf sig ctx prf ml mr ty = case prf of
    PSelf t => fst <$> rdInfer sig ctx t (Nd [] [])
    PChk t t' sk => do
      d <- rdCheck sig ctx t sk t'
      dT <- rdTypeBare sig ctx t'
      pure (DAscribe d dT Nothing)
    PRefl p => DRefl <$> rdPrf sig ctx p Nothing Nothing TopTy
    PPath sg k qs => DPath sg k <$> traverse (\q => rdPrf sig ctx q Nothing Nothing TopTy) qs
    PDelta x qs => DDelta x <$> traverse (\q => rdPrf sig ctx q Nothing Nothing TopTy) qs
    PAt q t pt => do
      dq <- rdPrf sig ctx q Nothing Nothing TopTy
      (_, _, qTy) <- dInfer sig ctx dq
      dt <- rdTypeBare sig ctx t
      b <- rdPrf sig ctx pt (Just qTy) (Just t) TopTy
      pure (DAt dq dt b)
    PReflx => pure DReflx
    PSym p => DSym <$> rdPrf sig ctx p mr ml ty
    PTrans p q => do
      -- the middle: computed by running a link directionally from a
      -- known side (the reader's own way), else unknown
      mL <- the (KM (Maybe Elem)) $ case ml of
              Just l => if dirP True p
                          then kOrElse (Just <$> (kPrfGo sig ctx p (GDir True l) (Just ty) >>= kJoinElem sig)) (pure Nothing)
                          else pure Nothing
              Nothing => pure Nothing
      mR <- the (KM (Maybe Elem)) $ case mL of
              Just m => pure (Just m)
              Nothing => case mr of
                Just r => if dirP False q
                            then kOrElse (Just <$> (kPrfGo sig ctx q (GDir False r) (Just ty) >>= kJoinElem sig)) (pure Nothing)
                            else pure Nothing
                Nothing => pure Nothing
      [| DTrans (rdPrf sig ctx p ml mR ty) (rdPrf sig ctx q mR mr ty) |]
    PTransAt p m q => do
      mJ <- kJoinElem sig m
      [| DTransAt (rdPrf sig ctx p ml (Just mJ) ty) (pure m) (rdPrf sig ctx q (Just mJ) mr ty) |]
    PConv pt tyX p => do
      b <- rdPrf sig ctx pt (Just ty) (Just tyX) TopTy
      dX <- rdTypeBare sig ctx tyX
      dp <- rdPrf sig ctx p ml mr tyX
      pure (DAscribe dp dX (Just b))
    PDeltaAll ns => pure (DDeltaAll ns)
    PIrrel sk => DIrrel <$> rdType sig ctx ty sk
    PEtaPi p => do
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy dom cod => DEtaPi <$> rdPrf sig (ctx :< dom) p (map (\l => PiApp (substElem l Wk) (CtxVar 0)) ml)
                                      (map (\r => PiApp (substElem r Wk) (CtxVar 0)) mr) cod
        _ => kerr "re-derive: Π-η at a non-Π type"
    PEtaSigma p q => do
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy dom cod => do
          lp <- need ml
          [| DEtaSigma (rdPrf sig ctx p (map SigmaElim1 ml) (map SigmaElim1 mr) dom)
                       (rdPrf sig ctx q (map SigmaElim2 ml) (map SigmaElim2 mr) (substTy cod (Ext Id (SigmaElim1 lp)))) |]
        _ => kerr "re-derive: Σ-η at a non-Σ type"
    PQuotWit Nothing => pure (DQuotWit Nothing)
    PQuotWit (Just p) => do
      (wl, wr, wt) <- witEq
      DQuotWit . Just <$> rdPrf sig ctx p (Just wl) (Just wr) wt
    PQuotWitPrf w sk => do
      (a, b, rel) <- classSides
      d <- rdCheck sig ctx w sk (substElem rel (Ext (Ext Id a) b))
      dT <- rdTypeBare sig ctx (substElem rel (Ext (Ext Id a) b))
      pure (DQuotWitPrf (DAscribe d dT Nothing))
    PInj p => do
      ty' <- kWhnfT sig ty
      l <- need ml
      r <- need mr
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      case (ty', lJ, rJ) of
        (SumTy a _, Inj1 x, Inj1 y) => DInj <$> rdPrf sig ctx p (Just x) (Just y) a
        (SumTy _ b, Inj2 x, Inj2 y) => DInj <$> rdPrf sig ctx p (Just x) (Just y) b
        _ => kerr "re-derive: injection leaf at a non-matching equation"
    PPropExt f fs g gs => do
      l <- need ml
      r <- need mr
      df <- rdCheck sig ctx f fs (PiTy l (substTy r Wk))
      dg <- rdCheck sig ctx g gs (PiTy r (substTy l Wk))
      pure (DPropExt df dg)
    PPrfCong skl skr p => do
      l <- need ml
      r <- need mr
      [| DPrfCong (rdType sig ctx l skl) (rdType sig ctx r skr) (rdPrf sig ctx p (Just l) (Just r) PropTy) |]
    -- congruence nodes: the children's goals are the parts of the
    -- sides where known, their types as the node computes them
    CZeroElim q => DZeroElim Nothing <$> rdPrf sig ctx q (part ml zeroElimP) (part mr zeroElimP) ZeroTy
    CNatIntro1 q => DSuc <$> rdPrf sig ctx q (part ml sucP) (part mr sucP) NatTy
    CNatElim mm qz qs qn => do
      mot <- case mm of
               Just m => pure m
               Nothing => pure (substTy ty Wk)
      dm <- case mm of
              Just m => Just <$> rdTypeBare sig (ctx :< NatTy) m
              Nothing => pure Nothing
      dz <- rdPrf sig ctx qz (part ml natElimZ) (part mr natElimZ) (substTy mot (Ext Id NatIntro0))
      ds <- rdPrf sig (ctx :< NatTy :< mot) qs (part ml natElimS) (part mr natElimS) (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
      dn <- rdPrf sig ctx qn (part ml natElimN) (part mr natElimN) NatTy
      pure (DNatElim dm dz ds dn)
    CPiIntro q => do
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy a b => DLam Nothing <$> rdPrf sig (ctx :< a) q (part ml lamP) (part mr lamP) b
        _ => kerr "re-derive: λ-congruence at a non-Π type"
    CPiApp qf qa => do
      df <- headDrv qf (part ml appF)
      dom <- headDom df (part ml appF)
      DApp df <$> rdPrf sig ctx qa (part ml appA) (part mr appA) dom
    CSigmaIntro qu qv => do
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy a b => do
          du <- rdPrf sig ctx qu (part ml pairU) (part mr pairU) a
          ul <- case part ml pairU of
                  Just u => pure u
                  Nothing => kerr "re-derive: pair congruence with unknown sides"
          dv <- rdPrf sig ctx qv (part ml pairV) (part mr pairV) (substTy b (Ext Id ul))
          pure (DPair Nothing du dv)
        _ => kerr "re-derive: pair congruence at a non-Σ type"
    CSigmaElim1 q => do
      dq <- headDrv q (part ml proj1P)
      pure (DProj1 dq)
    CSigmaElim2 q => do
      dq <- headDrv q (part ml proj2P)
      pure (DProj2 dq)
    CInj1 q => do
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy a _ => DInj1 Nothing <$> rdPrf sig ctx q (part ml inj1P) (part mr inj1P) a
        _ => kerr "re-derive: inj₁ congruence at a non-⊎ type"
    CInj2 q => do
      ty' <- kWhnfT sig ty
      case ty' of
        SumTy _ b => DInj2 Nothing <$> rdPrf sig ctx q (part ml inj2P) (part mr inj2P) b
        _ => kerr "re-derive: inj₂ congruence at a non-⊎ type"
    CSumElim mm ql qr qt => do
      dt0 <- headDrv qt (part ml sumElimT)
      (tTy, dt) <- scrutTyD dt0 (part ml sumElimT)
      tTy' <- kWhnfT sig tTy
      case tTy' of
        SumTy a b => do
          let mot = fromMaybe (substTy ty Wk) mm
          dm <- case mm of
                  Just m => Just <$> rdTypeBare sig (ctx :< SumTy a b) m
                  Nothing => pure Nothing
          dl <- rdPrf sig (ctx :< a) ql (part ml sumElimL) (part mr sumElimL) (substTy mot (Ext Wk (Inj1 (CtxVar 0))))
          dr <- rdPrf sig (ctx :< b) qr (part ml sumElimR) (part mr sumElimR) (substTy mot (Ext Wk (Inj2 (CtxVar 0))))
          pure (DSumElim dm dl dr dt)
        _ => kerr "re-derive: ⊎-elim congruence: scrutinee type"
    CPiTy qa qb => do
      cls <- compClassifier sig (Just ty)
      da <- rdPrf sig ctx qa (part ml piDom) (part mr piDom) cls
      dom <- case the (Maybe Elem) (part mr piDom <|> part ml piDom) of
               Just a => pure a
               Nothing => kerr "re-derive: Π congruence with unknown sides"
      db <- rdPrf sig (ctx :< dom) qb (part ml piCod) (part mr piCod) cls
      pure (DPi da db)
    CSigmaTy qa qb => do
      cls <- compClassifier sig (Just ty)
      da <- rdPrf sig ctx qa (part ml sigDom) (part mr sigDom) cls
      dom <- case the (Maybe Elem) (part mr sigDom <|> part ml sigDom) of
               Just a => pure a
               Nothing => kerr "re-derive: Σ congruence with unknown sides"
      db <- rdPrf sig (ctx :< dom) qb (part ml sigCod) (part mr sigCod) cls
      pure (DSigma da db)
    CSumTy qa qb => do
      cls <- compClassifier sig (Just ty)
      [| DSum (rdPrf sig ctx qa (part ml sumL) (part mr sumL) cls) (rdPrf sig ctx qb (part ml sumR) (part mr sumR) cls) |]
    CEqTy ql qr qt => do
      t <- case part ml eqT of
             Just t => pure t
             Nothing => kerr "re-derive: ≡ congruence with unknown sides"
      [| DEq (rdPrf sig ctx ql (part ml eqL) (part mr eqL) t) (rdPrf sig ctx qr (part ml eqR) (part mr eqR) t)
             (rdPrf sig ctx qt (part ml eqT) (part mr eqT) TopTy) |]
    CQuotTy qa qr => do
      cls <- compClassifier sig (Just ty)
      da <- rdPrf sig ctx qa (part ml quotA) (part mr quotA) cls
      dom <- case the (Maybe Elem) (part mr quotA <|> part ml quotA) of
               Just a => pure a
               Nothing => kerr "re-derive: quotient congruence with unknown sides"
      dr <- rdPrf sig (ctx :< dom :< substTy dom Wk) qr (part ml quotR) (part mr quotR) PropTy
      pure (DQuot da dr)
    CSigVar x qs => do
      es <- the (KM (List Elem)) $ case ml of
              Just (SigVar y es) => if y == x then pure (toList es) else kerr "re-derive: reference congruence at another head"
              _ => kerr "re-derive: reference congruence with unknown sides"
      let rs = case mr of
                 Just (SigVar _ es') => Just (toList es')
                 _ => Nothing
      ds <- traverse (\(i, q) => do
              mt <- sigChildTy sig x es i
              t <- case mt of
                     Just t => pure t
                     Nothing => kerr "re-derive: spine entry out of range"
              rdPrf sig ctx q (getAt i es) (rs >>= getAt i) t) (zipWithIndex 0 qs)
      pure (DRef x ds)
    CClass q => do
      ty' <- kWhnfT sig ty
      case ty' of
        QuotTy dom _ => DClass Nothing <$> rdPrf sig ctx q (part ml classP) (part mr classP) dom
        _ => kerr "re-derive: class congruence at a non-quotient type"
    CQuotElim mm qf qq => do
      dq0 <- headDrv qq (part ml quotElimQ)
      (qTy, dq) <- scrutTyD dq0 (part ml quotElimQ)
      qTy' <- kWhnfT sig qTy
      case qTy' of
        QuotTy a rel => do
          let mot = fromMaybe (substTy ty Wk) mm
          dm <- case mm of
                  Just m => Just <$> rdTypeBare sig (ctx :< QuotTy a rel) m
                  Nothing => pure Nothing
          df <- rdPrf sig (ctx :< a) qf (part ml quotElimF) (part mr quotElimF) (substTy mot (Ext Wk (Class (CtxVar 0))))
          pure (DQuotElim dm Nothing df dq)
        _ => kerr "re-derive: quot-elim congruence: scrutinee type"
    CSquash q => DSquash <$> rdPrf sig ctx q (part ml squashP) (part mr squashP) TopTy
    CQSort sg k qs => DSort sg k <$> spineDrv sg k qs
    CQCtor sg k qs => DCtor sg k <$> spineDrv sg k qs
    CQElim sg k mm qm qs qw => do
      let nM = length qm
      (fs, es, w) <- the (KM (List Elem, List Elem, Elem)) $ case ml of
        Just (QElim _ _ fs es w) => pure (fs, toList es, w)
        _ => kerr "re-derive: eliminator congruence with unknown sides"
      let rparts = the (Maybe (List Elem, List Elem, Elem)) $ case mr of
                     Just (QElim _ _ fs' es' w') => Just (fs', toList es', w')
                     _ => Nothing
      mots <- the (KM (List Ty)) $ case mm of
                Just ms => pure ms
                Nothing => kerr "re-derive: eliminator congruence without motives"
      let sortPs = qPositions QKSort sg
      dcs <- traverse (\(sj, m) => do
               sjE <- the (KM QTy) $ case qEntry sg sj of
                        Just x => pure x
                        Nothing => kerr "re-derive: sort out of range"
               (tel, wEnd, _) <- liftQ (reflTel sg (qwAt sj) sjE)
               let mctx = foldl (:<) ctx tel
               let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
               rdTypeBare sig (mctx :< selfTy) m) (zip sortPs mots)
      let eqPs = qPositions QKEq sg
      let pointPs = qPositions QKPoint sg
      dms <- traverse (\(j, (cj, q)) => do
               mty <- liftQ (methodTy sg mots cj)
               rdPrf sig ctx q (getAt j fs) (rparts >>= rFs j) mty) (zipWithIndex 0 (zip pointPs qm))
      des <- traverse (\(i, q) => do
               t <- case qSpineChildTy sg k (cast es) i of
                      Just t => pure t
                      Nothing => kerr "re-derive: spine entry out of range"
               rdPrf sig ctx q (getAt i es) (rparts >>= rEs i) t) (zipWithIndex 0 qs)
      dw <- rdPrf sig ctx qw (Just w) (map rW rparts) (QSort sg k (cast es))
      pure (DQElim sg k dcs (map (const DReflx) eqPs) dms des dw)
    COut q => DOut <$> headDrv q (part ml outP)
    CCorec pf qa qf qx => do
      da <- rdPrf sig ctx qa (part ml corecA) (part mr corecA) UniverseTy
      a <- case part ml corecA of
             Just a => pure a
             Nothing => kerr "re-derive: corec congruence with unknown sides"
      df <- rdPrf sig (ctx :< a) qf (part ml corecF) (part mr corecF) (substTy (reflectPoly pf a) Wk)
      dx <- rdPrf sig ctx qx (part ml corecX) (part mr corecX) a
      pure (DCorec pf da df dx)
   where
    rFs : Nat -> (List Elem, List Elem, Elem) -> Maybe Elem
    rFs j (fs', _, _) = getAt j fs'
    rEs : Nat -> (List Elem, List Elem, Elem) -> Maybe Elem
    rEs i (_, es', _) = getAt i es'
    rW : (List Elem, List Elem, Elem) -> Elem
    rW (_, _, w') = w'

    zeroElimP : Elem -> Maybe Elem
    zeroElimP (ZeroElim u) = Just u
    zeroElimP _ = Nothing
    sucP : Elem -> Maybe Elem
    sucP (NatIntro1 u) = Just u
    sucP _ = Nothing
    natElimZ, natElimS, natElimN : Elem -> Maybe Elem
    natElimZ (NatElim z _ _) = Just z
    natElimZ _ = Nothing
    natElimS (NatElim _ s _) = Just s
    natElimS _ = Nothing
    natElimN (NatElim _ _ n) = Just n
    natElimN _ = Nothing
    lamP : Elem -> Maybe Elem
    lamP (PiIntro f) = Just f
    lamP _ = Nothing
    appF, appA : Elem -> Maybe Elem
    appF (PiApp f _) = Just f
    appF _ = Nothing
    appA (PiApp _ a) = Just a
    appA _ = Nothing
    pairU, pairV : Elem -> Maybe Elem
    pairU (SigmaIntro u _) = Just u
    pairU _ = Nothing
    pairV (SigmaIntro _ v) = Just v
    pairV _ = Nothing
    proj1P, proj2P : Elem -> Maybe Elem
    proj1P (SigmaElim1 u) = Just u
    proj1P _ = Nothing
    proj2P (SigmaElim2 u) = Just u
    proj2P _ = Nothing
    inj1P, inj2P : Elem -> Maybe Elem
    inj1P (Inj1 u) = Just u
    inj1P _ = Nothing
    inj2P (Inj2 u) = Just u
    inj2P _ = Nothing
    sumElimL, sumElimR, sumElimT : Elem -> Maybe Elem
    sumElimL (SumElim l _ _) = Just l
    sumElimL _ = Nothing
    sumElimR (SumElim _ r _) = Just r
    sumElimR _ = Nothing
    sumElimT (SumElim _ _ t) = Just t
    sumElimT _ = Nothing
    piDom, piCod, sigDom, sigCod, sumL, sumR : Elem -> Maybe Elem
    piDom (Elem.PiTy a _) = Just a
    piDom _ = Nothing
    piCod (Elem.PiTy _ b) = Just b
    piCod _ = Nothing
    sigDom (Elem.SigmaTy a _) = Just a
    sigDom _ = Nothing
    sigCod (Elem.SigmaTy _ b) = Just b
    sigCod _ = Nothing
    sumL (Elem.SumTy a _) = Just a
    sumL _ = Nothing
    sumR (Elem.SumTy _ b) = Just b
    sumR _ = Nothing
    eqL, eqR, eqT : Elem -> Maybe Elem
    eqL (Elem.EqTy l _ _) = Just l
    eqL _ = Nothing
    eqR (Elem.EqTy _ r _) = Just r
    eqR _ = Nothing
    eqT (Elem.EqTy _ _ t) = Just t
    eqT _ = Nothing
    quotA, quotR : Elem -> Maybe Elem
    quotA (QuotTy a _) = Just a
    quotA _ = Nothing
    quotR (QuotTy _ r) = Just r
    quotR _ = Nothing
    classP : Elem -> Maybe Elem
    classP (Class u) = Just u
    classP _ = Nothing
    quotElimF, quotElimQ : Elem -> Maybe Elem
    quotElimF (QuotElim f _) = Just f
    quotElimF _ = Nothing
    quotElimQ (QuotElim _ q) = Just q
    quotElimQ _ = Nothing
    squashP : Elem -> Maybe Elem
    squashP (Squash u) = Just u
    squashP _ = Nothing
    outP : Elem -> Maybe Elem
    outP (Out u) = Just u
    outP _ = Nothing
    corecA, corecF, corecX : Elem -> Maybe Elem
    corecA (Corec _ a _ _) = Just a
    corecA _ = Nothing
    corecF (Corec _ _ f _) = Just f
    corecF _ = Nothing
    corecX (Corec _ _ _ x) = Just x
    corecX _ = Nothing

    need : Maybe Elem -> KM Elem
    need (Just x) = pure x
    need Nothing = kerr "re-derive: a type-directed leaf under a computed middle (sides unknown)"

    part : Maybe Elem -> (Elem -> Maybe Elem) -> Maybe Elem
    part m f = m >>= f

    -- the domain of a head: from its derivation when it states, else
    -- from the side's head by typing inversion
    headDom : Drv -> Maybe Elem -> KM Ty
    headDom df mh = do
      fTy <- if dSynth df
               then do (_, _, t) <- dInfer sig ctx df; pure t
               else case mh of
                      Just h => do
                        mt <- inferHead sig ctx h
                        case mt of
                          Just t => pure t
                          Nothing => kerr "re-derive: a head with no inferable type"
                      Nothing => kerr "re-derive: a rewritten head whose side is unknown"
      fTy' <- kWhnfT sig fTy
      case fTy' of
        PiTy dom _ => pure dom
        _ => kerr "re-derive: application congruence: the head is not a function"

    -- a scrutinee child's type, and the child under the exposure that
    -- shows its shape when a definition hides it
    scrutTyD : Drv -> Maybe Elem -> KM (Ty, Drv)
    scrutTyD dq mh = do
      t <- if dSynth dq
             then do (_, _, t) <- dInfer sig ctx dq; pure t
             else case mh of
                    Just h => do
                      mt <- inferHead sig ctx h
                      case mt of
                        Just t => pure t
                        Nothing => kerr "re-derive: a scrutinee with no inferable type"
                    Nothing => kerr "re-derive: a rewritten scrutinee whose side is unknown"
      t' <- kWhnfT sig t
      case t' of
        SumTy _ _ => pure (t, dq)
        QuotTy _ _ => pure (t, dq)
        _ => do
          (tX, pt) <- rdExpose sig ctx t
          case pt of
            DReflx => pure (t, dq)
            _ => if dSynth dq
                   then do dX <- rdTypeBare sig ctx tX; pure (tX, DConv dq (Just dX) pt)
                   else pure (tX, dq)

    scrutTy : Drv -> Maybe Elem -> KM Ty
    scrutTy dq mh = fst <$> scrutTyD dq mh

    -- a head or scrutinee child: refl at a known head is the head's
    -- derivation; a spine over one recurses; anything else is
    -- re-derived at the parts of the known side (a proper rewrite
    -- inside a head is typed by the kernel from the side)
    headDrv : Prf -> Maybe Elem -> KM Drv
    headDrv PReflx (Just h) = fst <$> rdInfer sig ctx h (Nd [] [])
    headDrv PReflx Nothing = kerr "re-derive: refl at a head whose side is unknown"
    headDrv (CPiApp f a) side = do
      df <- headDrv f (part side appF)
      dom <- headDom df (part side appF)
      da <- case (a, part side appA) of
              (PReflx, Just x) => rdCheck sig ctx x (Nd [] []) dom
              _ => rdPrf sig ctx a (part side appA) (part side appA) dom
      pure (DApp df da)
    headDrv (CSigmaElim1 q) side = DProj1 <$> headDrv q (part side proj1P)
    headDrv (CSigmaElim2 q) side = DProj2 <$> headDrv q (part side proj2P)
    headDrv (COut q) side = DOut <$> headDrv q (part side outP)
    headDrv q side = rdPrf sig ctx q side side TopTy

    spineDrv : QSig -> Nat -> List Prf -> KM (List Drv)
    spineDrv sg k qs = do
      es <- the (KM (List Elem)) $ case ml of
              Just (QSort _ _ es) => pure (toList es)
              Just (QCtor _ _ es) => pure (toList es)
              _ => kerr "re-derive: spine congruence with unknown sides"
      let rs = case mr of
                 Just (QSort _ _ es') => Just (toList es')
                 Just (QCtor _ _ es') => Just (toList es')
                 _ => Nothing
      traverse (\(i, q) => do
        t <- case qSpineChildTy sg k (cast es) i of
               Just t => pure t
               Nothing => kerr "re-derive: spine entry out of range"
        rdPrf sig ctx q (getAt i es) (rs >>= getAt i) t) (zipWithIndex 0 qs)

    classSides : KM (Elem, Elem, Elem)
    classSides = do
      l <- need ml
      r <- need mr
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      ty' <- kWhnfT sig ty
      case (ty', lJ, rJ) of
        (QuotTy _ rel, Class a, Class b) => pure (a, b, rel)
        _ => kerr "re-derive: quotient witness at a non-class equation"

    witEq : KM (Elem, Elem, Ty)
    witEq = do
      (a, b, rel) <- classSides
      inst <- kJoinElem sig (substElem rel (Ext (Ext Id a) b))
      case inst of
        Elem.EqTy wl wr wt => pure (wl, wr, wt)
        _ => kerr "re-derive: quotient witness: the relation instance is not an equation"

||| The canary: re-derive and read; a disagreement with the checker
||| that just accepted is audited (NOVA_AUDIT=1), never a verdict.
canary : String -> KM () -> Nat -> a -> a
canary what m fuel x =
  case runKM m fuel of
    Right _ => x
    Left e => audit "DRV-DISAGREE \{what} | \{e}" x

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
  let r = map fst $ runKM (do
            ctx <- kTele sig [<] art.tele
            kCheckTyK sig ctx art.dty art.dtySkel
            kCheckE sig ctx art.body art.dty art.bodySkel
            pure (SigDef ctx art.dname art.body art.dty)) fuel
  in case r of
       Left _ => r
       Right _ => canary "item \{art.dname}" (do
         (ctx, dtele) <- rdTeleItem sig [<] art.tele
         dty <- rdType sig ctx art.dty art.dtySkel
         dbody <- rdCheck sig ctx art.body art.bodySkel art.dty
         ty <- kCatch (dType sig ctx dty) (\e => kerr "\{e}\n  TYPE DERIVATION: \{showDrv dty}")
         t <- kCatch (dElemAt sig ctx dbody ty) (\e => kerr "\{e}\n  BODY DERIVATION: \{showDrv dbody}")
         if t == art.body then pure () else kerr "erasure differs from the body\n  erased: \{show t}"
         ok <- tyAgree sig art.dty ty
         if ok then pure () else kerr "erasure differs from the type\n  erased: \{show ty}") fuel r

export
kCheckTyDefItem : Sig -> Nat -> KTyDefArt -> Either KErr SigEntry
kCheckTyDefItem sig fuel art =
  let r = map fst $ runKM (do
            ctx <- kTele sig [<] art.ttele
            kCheckTyK sig ctx art.tty art.ttySkel
            -- a type definition is a definition at the classifier 𝕍 (sig-def
            -- at A = 𝕍)
            pure (SigDef ctx art.tname art.tty TopTy)) fuel
  in case r of
       Left _ => r
       Right _ => canary "type item \{art.tname}" (do
         (ctx, _) <- rdTeleItem sig [<] art.ttele
         dty <- rdType sig ctx art.tty art.ttySkel
         ty <- kCatch (dType sig ctx dty) (\e => kerr "\{e}\n  TYPE DERIVATION: \{showDrv dty}")
         if ty == art.tty then pure () else kerr "erasure differs from the type\n  erased: \{show ty}") fuel r

rdTeleItem sig ctx [] = pure (ctx, [])
rdTeleItem sig ctx ((ty, sk) :: rest) = do
  d <- rdType sig ctx ty sk
  t <- dType sig ctx d
  (ctx', ds) <- rdTeleItem sig (ctx :< t) rest
  pure (ctx', d :: ds)

-- ===== Entry points =====

export
kCheckEqElem : Sig -> Ctx -> Nat -> Prf -> Elem -> Elem -> Ty -> Either KErr ()
kCheckEqElem sig ctx fuel cert l r ty =
  let r0 = map fst (runKM (kEqElem sig ctx cert l r ty) fuel)
  in case r0 of
       Left _ => r0
       Right _ => canary "equation \{showPrf cert} | goal \{show l} ≐ \{show r} : \{show ty} | ctx \{show (length ctx)}" (do
         lJ <- kJoinElem sig l
         rJ <- kJoinElem sig r
         d <- rdPrf sig ctx cert (Just lJ) (Just rJ) ty
         dAt sig ctx d lJ rJ ty) fuel r0

export
kCheckEqTy : Sig -> Ctx -> Nat -> Prf -> Ty -> Ty -> Either KErr ()
kCheckEqTy sig ctx fuel cert a b =
  map fst (runKM (kEqTy sig ctx cert a b) fuel)
