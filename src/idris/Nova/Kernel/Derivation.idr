module Nova.Kernel.Derivation

-- DERIVATIONS: the kernel on proof terms alone (docs/NovaKernel.txt
-- §10, a draft under migration). A derivation is a proof term whose
-- readings synthesize the equation it states — for an element
-- derivation both sides are the same term, its ERASURE. The core term
-- is an output of the derivation, never an input beside it; nothing
-- here is a skeleton aligned with a term.
--
-- This module is the grammar and its erasure as data (§10.8, step 1).
-- The readings (§10.3–10.5) live in Nova.Kernel, beside the current
-- proof terms, until the migration retires those.

import Data.List
import Data.Maybe
import Data.SnocList

import Nova.Kernel.Syntax
import Nova.Kernel.Subst

%default covering

mutual
  ||| A substitution as the grammar spells it (§10.4): a weakening by
  ||| `depth` binders followed by a typed extension — entry i is a
  ||| derivation and the derivation of the telescope type it is checked
  ||| against, over Δ↓depth ▷ T₁ … Tᵢ₋₁. The only shape the engine
  ||| performs; general substitutions have no node.
  public export
  record DSub where
    constructor MkDSub
    depth : Nat
    entries : List (Drv, Drv)

  ||| A QIIT signature's ToS terms with their embedded Nova pieces as
  ||| DERIVATIONS (an external argument derived where it stands): the
  ||| carrier of a sort, constructor, eliminator or path node. Erasure
  ||| gives the QSig the computation rules read.
  public export
  data DQTm : Type where
    DQVar : Nat -> DQTm
    DQAppE : DQTm -> Drv -> DQTm
    DQAppI : DQTm -> DQTm -> DQTm
    DQEqC : DQTm -> DQTm -> DQTm -> DQTm

  ||| … and its ToS types: an external Π's domain a type derivation.
  public export
  data DQTy : Type where
    DQU : DQTy
    DQEl : DQTm -> DQTy
    DQPiExt : Drv -> DQTy -> DQTy
    DQPiInd : DQTm -> DQTy -> DQTy

  ||| A polynomial with its embedded codes as derivations (each at 𝕌,
  ||| under the binders before it): the carrier of ν and corec.
  public export
  data DPoly : Type where
    DPHole : DPoly
    DPConst : Drv -> DPoly
    DPProd : DPoly -> DPoly -> DPoly
    DPSum : DPoly -> DPoly -> DPoly
    DPSigma : Drv -> DPoly -> DPoly
    DPPi : Drv -> DPoly -> DPoly

  ||| The derivation grammar, spelled as §10.2 spells it. A node is the
  ||| former it derives, with derivations in the children's places; a
  ||| `Maybe Drv` annotation is the INFERENCE-mode form (what the type
  ||| flowing down would supply under checking), absent under checking.
  public export
  data Drv : Type where
    -- ----- leaves -----
    ||| ☐ᵢ                                                    (el-var)
    DVar : Nat -> Drv
    ||| x[π̄]: a signature reference, its spine stated entrywise (§3)
    DRef : String -> List Drv -> Drv
    ||| ()  Z  and the constant types 𝟘 𝟙 ℕ 𝕌 Ω 𝕍
    DUnit : Drv
    DZero : Drv
    DZeroTy : Drv
    DOneTy : Drv
    DNatTy : Drv
    DUniverse : Drv
    DProp : Drv
    DTop : Drv
    ||| ⟨π⟩ REFLECTION: π ⇒ p : (l ≡ r ∈ A) states l ≐ r : A
    DRefl : Drv -> Drv
    ||| qpath 𝕔 π̄: an imposed QIIT equation, its spine stated
    DPath : List DQTy -> Nat -> List Drv -> Drv
    ||| x-δ π̄: x[ū] ≐ t[ū] for (Δ ⊦ x ≔ t : T), ū stated by π̄
    DDelta : String -> List Drv -> Drv
    ||| refl: the sides join under β
    DReflx : Drv
    ||| π⁻¹
    DSym : Drv -> Drv
    ||| π ; π′, middle computed
    DTrans : Drv -> Drv -> Drv
    ||| π ; [m] ; π′, middle stated (an erasure: both proofs are read
    ||| against it, it needs no typing of its own)
    DTransAt : Drv -> Drv -> Drv -> Drv
    ||| δ-all x̄: every addressable occurrence of the named definitions
    ||| unfolded at once
    DDeltaAll : List String -> Drv
    -- ----- type-directed leaves (read ▷ only, §10.5) -----
    ||| irrel(π_P?): the position's type is 𝟙, 𝟘, or a prop — the one
    ||| π_P derives, or (the derivation absent) the position's type
    ||| itself, judged a prop by the kernel (a given type is
    ||| well-formed; its prop-ness is the kernel's own question on it)
    DIrrel : Maybe Drv -> Drv
    ||| η→(π)
    DEtaPi : Drv -> Drv
    ||| η×(π, π′)
    DEtaSigma : Drv -> Drv -> Drv
    ||| quot-wit(π?): class a ≐ class b by the relation's shape
    DQuotWit : Maybe Drv -> Drv
    ||| quot-wit[π_w]: the witness derived at the relation instance
    DQuotWitPrf : Drv -> Drv
    ||| inj(π): same-tag injections, the payloads equal
    DInj : Drv -> Drv
    ||| propext[π_f, π_g]: the two implications, derived as functions
    DPropExt : Drv -> Drv -> Drv
    ||| prop-lift(π_p?, π_q?, π): both sides props — derived at Ω, or,
    ||| a derivation absent, the given side judged a prop by the
    ||| kernel — and π at Ω
    DPrfCong : Maybe Drv -> Maybe Drv -> Drv -> Drv
    -- ----- conversion, ascription, substitution -----
    ||| π ∷ π_T by β (inference: the type converted to what π_T
    ||| derives) — π by β (checking at T, the annotation absent: the
    ||| skeleton's switch)
    DConv : Drv -> Maybe Drv -> Drv -> Drv
    ||| (π : π_T by β): a STATED equation ascribed to the type π_T
    ||| derives, β ▷ its type ≐ that
    DAt : Drv -> Drv -> Drv -> Drv
    ||| π[σ] (§10.4): the substitution lemma as a rule; inference only
    DSubst : Drv -> DSub -> Drv
    ||| (π : π_T? by β?): an ASCRIPTION — π checked at a type the
    ||| annotation derives, or, the annotation absent, at the type β
    ||| PRODUCES when run from the position's type (β → T ≐ T′: an
    ||| exposure names no target of its own — the target is what
    ||| unfolding reaches, well-formed because the run is a chain of
    ||| rule applications); with both present β ▷ T ≐ that type; with
    ||| neither the two agree; in inference position the type is what
    ||| π_T derives (the skeleton's intro-ty), β absent
    DAscribe : Drv -> Maybe Drv -> Maybe Drv -> Drv
    -- ----- intro forms -----
    ||| λ_{π_A} π
    DLam : Maybe Drv -> Drv -> Drv
    ||| (π, π′)_{π_B}: the Σ's family, over Γ ▷ A
    DPair : Maybe Drv -> Drv -> Drv -> Drv
    ||| inj₁_{π_B} π — the other summand
    DInj1 : Maybe Drv -> Drv -> Drv
    ||| inj₂_{π_A} π
    DInj2 : Maybe Drv -> Drv -> Drv
    ||| class_{π_R} π: the relation, over Γ ▷ A ▷ A[↑]
    DClass : Maybe Drv -> Drv -> Drv
    ||| S π
    DSuc : Drv -> Drv
    ||| 𝒮.𝕔 π̄: a constructor, the signature carried
    DCtor : List DQTy -> Nat -> List Drv -> Drv
    ||| corec_𝔽 π_a π_f π_x
    DCorec : DPoly -> Drv -> Drv -> Drv -> Drv
    ||| let π_a π_b: the core's let, definiens inferred
    DLet : Drv -> Drv -> Drv
    ||| ⋆_{π_P} by π (el-eq-i): π_P ⇒ (l ≡ r ∈ A) : Ω, π ▷ l ≐ r : A;
    ||| checking at the prop: ⋆ by π
    DStar : Maybe Drv -> Drv -> Drv
    ||| sq(π) (el-squash-i): π ⇒ e : A gives ⋆ : ∥A∥
    DSq : Drv -> Drv
    ||| squash-elim_{π_Q} π (x. π′) (el-squash-e-prf): the goal prop
    DSquashElim : Maybe Drv -> Drv -> Drv -> Drv
    ||| coind_{π_P} R π_p π_q (el-nu-coind): the equation prop, the
    ||| invariant R (a prop over ν𝔽 ▷ ν𝔽), the endpoint proof, the
    ||| one-step closure
    DCoind : Maybe Drv -> Drv -> Drv -> Drv -> Drv
    -- ----- eliminators: motives mandatory, absent only as the
    -- ----- checking sugar (the constant motive, §10.3) -----
    ||| 𝟘-elim_{π_T} π
    DZeroElim : Maybe Drv -> Drv -> Drv
    ||| ℕ-elim_{π_M} π_z π_s π_n
    DNatElim : Maybe Drv -> Drv -> Drv -> Drv -> Drv
    ||| ⊎-elim_{π_M} π_l π_r π_t
    DSumElim : Maybe Drv -> Drv -> Drv -> Drv -> Drv
    ||| quot-elim_{π_M ; wd} π_f π_q: wd absent when the motive is a prop
    DQuotElim : Maybe Drv -> Maybe Drv -> Drv -> Drv -> Drv
    ||| 𝒮.𝕤-elim_{π̄_C ; coh̄} π̄_m π̄ π_w: motives (one per sort),
    ||| coherences (one per equation entry), methods, index spine,
    ||| eliminee
    DQElim : List DQTy -> Nat -> Maybe (List Drv) -> List Drv -> List Drv -> List Drv -> Drv -> Drv
    ||| out π
    DOut : Drv -> Drv
    ||| π π′
    DApp : Drv -> Drv -> Drv
    ||| π .π₁  π .π₂
    DProj1 : Drv -> Drv
    DProj2 : Drv -> Drv
    -- ----- types and codes -----
    DPi : Drv -> Drv -> Drv
    DSigma : Drv -> Drv -> Drv
    DSum : Drv -> Drv -> Drv
    DEq : Drv -> Drv -> Drv -> Drv
    DQuot : Drv -> Drv -> Drv
    DSquash : Drv -> Drv
    DNu : DPoly -> Drv
    DSort : List DQTy -> Nat -> List Drv -> Drv

-- ===== Erasure =====

||| ↑ composed n times.
export
wkN : Nat -> Sub
wkN Z = Id
wkN (S n) = Chain (wkN n) Wk

||| A signature as a derivation carries it.
public export
DQSig : Type
DQSig = List DQTy

mutual
  ||| The ERASURE of an element derivation: drop the annotations, keep
  ||| the former; a witness node erases to ⋆, a substitution node to
  ||| the substituted erasure. Nothing at an equation form (a
  ||| reflection, a δ leaf, refl, …) in an element position: those
  ||| state equations and derive no element — they occur only where a
  ||| node takes a proof, which the erasure does not enter.
  export
  erase : Drv -> Maybe Elem
  erase (DVar i) = Just (CtxVar i)
  erase (DRef x ps) = SigVar x . cast <$> traverse erase ps
  erase DUnit = Just OneIntro
  erase DZero = Just NatIntro0
  erase DZeroTy = Just ZeroTy
  erase DOneTy = Just OneTy
  erase DNatTy = Just NatTy
  erase DUniverse = Just UniverseTy
  erase DProp = Just PropTy
  erase DTop = Just TopTy
  erase (DConv p _ _) = erase p
  erase (DAscribe p _ _) = erase p
  erase (DSubst p sg) = [| substElem (erase p) (eraseSub sg) |]
  erase (DLam _ p) = PiIntro <$> erase p
  erase (DPair _ u v) = [| SigmaIntro (erase u) (erase v) |]
  erase (DInj1 _ p) = Inj1 <$> erase p
  erase (DInj2 _ p) = Inj2 <$> erase p
  erase (DClass _ p) = Class <$> erase p
  erase (DSuc p) = NatIntro1 <$> erase p
  erase (DCtor sg k ps) = [| (\g, xs => QCtor g k (cast xs)) (eraseQSig sg) (traverse erase ps) |]
  erase (DCorec f a g x) = [| Corec (erasePoly f) (erase a) (erase g) (erase x) |]
  erase (DLet a b) = [| Let (erase a) (erase b) |]
  erase (DStar _ _) = Just Star
  erase (DSq _) = Just Star
  erase (DSquashElim _ _ _) = Just Star
  erase (DCoind _ _ _ _) = Just Star
  erase (DZeroElim _ p) = ZeroElim <$> erase p
  erase (DNatElim _ z s n) = [| NatElim (erase z) (erase s) (erase n) |]
  erase (DSumElim _ l r t) = [| SumElim (erase l) (erase r) (erase t) |]
  erase (DQuotElim _ _ f q) = [| QuotElim (erase f) (erase q) |]
  erase (DQElim sg k _ _ ms es w) =
    [| (\g, fs, xs, w' => QElim g k fs (cast xs) w') (eraseQSig sg) (traverse erase ms) (traverse erase es) (erase w) |]
  erase (DOut p) = Out <$> erase p
  erase (DApp f a) = [| PiApp (erase f) (erase a) |]
  erase (DProj1 p) = SigmaElim1 <$> erase p
  erase (DProj2 p) = SigmaElim2 <$> erase p
  erase (DPi a b) = [| PiTy (erase a) (erase b) |]
  erase (DSigma a b) = [| SigmaTy (erase a) (erase b) |]
  erase (DSum a b) = [| SumTy (erase a) (erase b) |]
  erase (DEq l r t) = [| EqTy (erase l) (erase r) (erase t) |]
  erase (DQuot a r) = [| QuotTy (erase a) (erase r) |]
  erase (DSquash p) = Squash <$> erase p
  erase (DNu f) = NuTy <$> erasePoly f
  erase (DSort sg k ps) = [| (\g, xs => QSort g k (cast xs)) (eraseQSig sg) (traverse erase ps) |]
  -- equation forms derive no element
  erase _ = Nothing

  ||| The erasure of a carried signature: each embedded piece erased.
  export
  eraseQTm : DQTm -> Maybe QTm
  eraseQTm (DQVar i) = Just (QVar i)
  eraseQTm (DQAppE f e) = [| QAppE (eraseQTm f) (erase e) |]
  eraseQTm (DQAppI f a) = [| QAppI (eraseQTm f) (eraseQTm a) |]
  eraseQTm (DQEqC l r u) = [| QEqC (eraseQTm l) (eraseQTm r) (eraseQTm u) |]

  export
  eraseQTy : DQTy -> Maybe QTy
  eraseQTy DQU = Just QU
  eraseQTy (DQEl t) = QEl <$> eraseQTm t
  eraseQTy (DQPiExt a b) = [| QPiExt (erase a) (eraseQTy b) |]
  eraseQTy (DQPiInd u b) = [| QPiInd (eraseQTm u) (eraseQTy b) |]

  export
  eraseQSig : List DQTy -> Maybe QSig
  eraseQSig = traverse eraseQTy

  ||| The erasure of a carried polynomial.
  export
  erasePoly : DPoly -> Maybe Poly
  erasePoly DPHole = Just PHole
  erasePoly (DPConst a) = PConst <$> erase a
  erasePoly (DPProd f g) = [| PProd (erasePoly f) (erasePoly g) |]
  erasePoly (DPSum f g) = [| PSum (erasePoly f) (erasePoly g) |]
  erasePoly (DPSigma a f) = [| PSigma (erase a) (erasePoly f) |]
  erasePoly (DPPi a f) = [| PPi (erase a) (erasePoly f) |]

  ||| The substitution a DSub denotes: ↑ᵈ extended by the entries'
  ||| erasures.
  export
  eraseSub : DSub -> Maybe Sub
  eraseSub (MkDSub d es) = foldl Ext (wkN d) <$> traverse (erase . fst) es

||| Is the derivation an ELEMENT derivation — does it erase?
export
derivesElem : Drv -> Bool
derivesElem = isJust . erase

-- ===== Printing, in the core's syntax =====

||| A node that prints without parentheses in argument position.
atomicD : Drv -> Bool
atomicD (DVar _) = True
atomicD (DRef _ _) = True
atomicD DUnit = True
atomicD DZero = True
atomicD DZeroTy = True
atomicD DOneTy = True
atomicD DNatTy = True
atomicD DUniverse = True
atomicD DProp = True
atomicD DTop = True
atomicD (DRefl _) = True
atomicD DReflx = True
atomicD (DSym _) = True
atomicD (DTransAt _ _ _) = True
atomicD (DIrrel _) = True
atomicD (DEtaPi _) = True
atomicD (DEtaSigma _ _) = True
atomicD (DQuotWit _) = True
atomicD (DQuotWitPrf _) = True
atomicD (DInj _) = True
atomicD (DPropExt _ _) = True
atomicD (DPrfCong _ _ _) = True
atomicD (DConv _ _ _) = True
atomicD (DAscribe _ _ _) = True
atomicD (DAt _ _ _) = True
atomicD (DSubst _ _) = True
atomicD (DPair _ _ _) = True
atomicD (DSq _) = True
atomicD (DProj1 _) = True
atomicD (DProj2 _) = True
atomicD (DSquash _) = True
atomicD (DSort _ _ _) = True
atomicD (DCtor _ _ _) = True
atomicD _ = False

mutual
  ||| Argument position: atoms bare, anything else parenthesised.
  argD : Drv -> String
  argD p = if atomicD p then showDrv p else "(" ++ showDrv p ++ ")"

  ||| Head position: applications chain to the left.
  hdD : Drv -> String
  hdD p@(DApp _ _) = showDrv p
  hdD p = argD p

  argsD : List Drv -> String
  argsD ps = concat (intersperse ", " (map showDrv ps))

  entryD : (Drv, Drv) -> String
  entryD (e, t) = " ▷ " ++ showDrv e ++ " : " ++ showDrv t

  wdD : Drv -> String
  wdD w = " ; " ++ showDrv w

  ||| An annotation in braces, or nothing (the checking form).
  annD : Maybe Drv -> String
  annD Nothing = ""
  annD (Just a) = "{" ++ showDrv a ++ "}"

  export
  covering
  showDrv : Drv -> String
  -- leaves
  showDrv (DVar i) = "☐\{show i}"
  showDrv (DRef x ps) = if null ps then x else "\{x}[\{argsD ps}]"
  showDrv DUnit = "()"
  showDrv DZero = "Z"
  showDrv DZeroTy = "𝟘"
  showDrv DOneTy = "𝟙"
  showDrv DNatTy = "ℕ"
  showDrv DUniverse = "𝕌"
  showDrv DProp = "Ω"
  showDrv DTop = "𝕍"
  showDrv (DRefl p) = "⟨\{showDrv p}⟩"
  showDrv (DPath _ k ps) = "path \{show k} [\{argsD ps}]"
  showDrv (DDelta x ps) = "\{x}-δ [\{argsD ps}]"
  showDrv DReflx = "refl"
  showDrv (DSym p) = "\{argD p}⁻¹"
  showDrv (DTrans p q) = "\{showDrv p} ; \{showDrv q}"
  showDrv (DTransAt p m q) = "(\{showDrv p} ; [\{showDrv m}] ; \{showDrv q})"
  showDrv (DDeltaAll ns) = "δ-all \{show ns}"
  -- type-directed leaves
  showDrv (DIrrel p) = "irrel(\{maybe "" showDrv p})"
  showDrv (DEtaPi p) = "η→(\{showDrv p})"
  showDrv (DEtaSigma p q) = "η×(\{showDrv p}, \{showDrv q})"
  showDrv (DQuotWit mp) = "quot-wit(\{maybe "" showDrv mp})"
  showDrv (DQuotWitPrf w) = "quot-wit[\{showDrv w}]"
  showDrv (DInj p) = "inj(\{showDrv p})"
  showDrv (DPropExt f g) = "propext[\{showDrv f}, \{showDrv g}]"
  showDrv (DPrfCong p q r) = "prop-lift(\{maybe "_" showDrv p}, \{maybe "_" showDrv q}, \{showDrv r})"
  -- conversion, ascription, substitution
  showDrv (DConv p Nothing b) = "(\{showDrv p} by \{showDrv b})"
  showDrv (DConv p (Just t) b) = "(\{showDrv p} ∷ \{showDrv t} by \{showDrv b})"
  showDrv (DAt p t b) = "(\{showDrv p} : \{showDrv t} by \{showDrv b})"
  showDrv (DAscribe p t Nothing) = "(\{showDrv p} : \{maybe "_" showDrv t})"
  showDrv (DAscribe p t (Just b)) = "(\{showDrv p} : \{maybe "_" showDrv t} by \{showDrv b})"
  showDrv (DSubst p (MkDSub d es)) =
    "\{argD p}[↑\{show d}\{concatMap entryD es}]"
  -- intro forms
  showDrv (DLam a p) = "λ\{annD a} \{showDrv p}"
  showDrv (DPair b u v) = "(\{showDrv u}, \{showDrv v})\{annD b}"
  showDrv (DInj1 b p) = "inj₁\{annD b} \{argD p}"
  showDrv (DInj2 a p) = "inj₂\{annD a} \{argD p}"
  showDrv (DClass r p) = "class\{annD r} \{argD p}"
  showDrv (DSuc p) = "S \{argD p}"
  showDrv (DCtor _ k ps) = "𝒮.\{show k}[\{argsD ps}]"
  showDrv (DCorec _ a f x) = "corec \{argD a} \{argD f} \{argD x}"
  showDrv (DLet a b) = "let \{argD a} \{argD b}"
  showDrv (DStar mp p) = "⋆\{annD mp} by \{argD p}"
  showDrv (DSq p) = "sq(\{showDrv p})"
  showDrv (DSquashElim mq e b) = "squash-elim\{annD mq} \{argD e} \{argD b}"
  showDrv (DCoind mp r p q) = "coind\{annD mp} \{argD r} \{argD p} \{argD q}"
  -- eliminators
  showDrv (DZeroElim mt p) = "𝟘-elim\{annD mt} \{argD p}"
  showDrv (DNatElim m z s n) = "ℕ-elim\{annD m} \{argD z} \{argD s} \{argD n}"
  showDrv (DSumElim m l r t) = "⊎-elim\{annD m} \{argD l} \{argD r} \{argD t}"
  showDrv (DQuotElim m wd f q) =
    "quot-elim\{case (m, wd) of
                 (Nothing, Nothing) => ""
                 (_, _) => "{" ++ maybe "" showDrv m ++ maybe "" wdD wd ++ "}"} \{argD f} \{argD q}"
  showDrv (DQElim _ k cs cohs ms es w) =
    "𝒮.\{show k}-elim{\{maybe "" argsD cs} ; \{argsD cohs}} [\{argsD ms}] [\{argsD es}] \{argD w}"
  showDrv (DOut p) = "out \{argD p}"
  showDrv (DApp f a) = "\{hdD f} \{argD a}"
  showDrv (DProj1 p) = "\{argD p} .π₁"
  showDrv (DProj2 p) = "\{argD p} .π₂"
  -- types and codes
  showDrv (DPi a b) = "\{argD a} → \{argD b}"
  showDrv (DSigma a b) = "\{argD a} × \{argD b}"
  showDrv (DSum a b) = "\{argD a} ⊎ \{argD b}"
  showDrv (DEq l r t) = "\{argD l} ≡ \{argD r} ∈ \{argD t}"
  showDrv (DQuot a r) = "\{argD a} / \{argD r}"
  showDrv (DSquash p) = "∥\{showDrv p}∥"
  showDrv (DNu f) = "ν \{maybe "?" show (erasePoly f)}"
  showDrv (DSort _ k ps) = "𝒮.\{show k}[\{argsD ps}]"

export
covering
Show Drv where
  show = showDrv

-- ===== Weakening a carrier under binders (a builder's tool) =====
--
-- A carried signature elaborated over a context Γ is placed by the
-- data-item emitter under n more binders. Its embedded pieces sit
-- under the external binders before them, so the weakening is UNDER
-- those binders — expressed within the grammar by the substitution
-- node alone: ↑ⁿ⁺ᵐ extended by the m external variables at their
-- (original) domain derivations, exactly §10.4's shape.

||| π over Γ ▷ T₁ … Tₘ (tele the domains' derivations, outermost
||| first) placed over Γ ▷ n entries ▷ T₁ … Tₘ.
export
wkUnder : Nat -> List Drv -> Drv -> Drv
wkUnder Z _ p = p
wkUnder n tele p =
  let m = length tele
  in DSubst p (MkDSub (n + m) (zipWith (\i, t => (DVar (minus (minus m 1) i), t)) [0 .. minus m 1] tele))

mutual
  export
  wkDQTm : Nat -> List Drv -> DQTm -> DQTm
  wkDQTm n tele (DQVar i) = DQVar i
  wkDQTm n tele (DQAppE f e) = DQAppE (wkDQTm n tele f) (wkUnder n tele e)
  wkDQTm n tele (DQAppI f a) = DQAppI (wkDQTm n tele f) (wkDQTm n tele a)
  wkDQTm n tele (DQEqC l r u) = DQEqC (wkDQTm n tele l) (wkDQTm n tele r) (wkDQTm n tele u)

  export
  wkDQTy : Nat -> List Drv -> DQTy -> DQTy
  wkDQTy n tele DQU = DQU
  wkDQTy n tele (DQEl t) = DQEl (wkDQTm n tele t)
  wkDQTy n tele (DQPiExt a b) = DQPiExt (wkUnder n tele a) (wkDQTy n (tele ++ [a]) b)
  wkDQTy n tele (DQPiInd u b) = DQPiInd (wkDQTm n tele u) (wkDQTy n tele b)

||| A carried signature under n more binders.
export
wkDQSig : Nat -> DQSig -> DQSig
wkDQSig Z sg = sg
wkDQSig n sg = map (wkDQTy n []) sg

export
wkDPoly : Nat -> List Drv -> DPoly -> DPoly
wkDPoly n tele DPHole = DPHole
wkDPoly n tele (DPConst a) = DPConst (wkUnder n tele a)
wkDPoly n tele (DPProd f g) = DPProd (wkDPoly n tele f) (wkDPoly n tele g)
wkDPoly n tele (DPSum f g) = DPSum (wkDPoly n tele f) (wkDPoly n tele g)
wkDPoly n tele (DPSigma a f) = DPSigma (wkUnder n tele a) (wkDPoly n (tele ++ [a]) f)
wkDPoly n tele (DPPi a f) = DPPi (wkUnder n tele a) (wkDPoly n (tele ++ [a]) f)

-- ===== The signature: an item is its derivations =====
--
-- Σ stores what the kernel READ: an item's type and body derivations
-- (§8), beside their ERASURES — the terms the computation rules read
-- (δ unfolds a stored erasure; β and the join run on erasures). The
-- erasures are a cache of the derivations, never a second source.

||| TWO entry kinds (Foundation: type definitions and type
||| declarations are the A = TopTy instances; an equation CONSTRAINT
||| is a hole at the equation's prop — a declaration at
||| (a₀ ≡ a₁ ∈ A) — used through el-sig-decl + el-reflect).
public export
data SigEntry : Type where
  ||| Γ ⊦ x ≔ π : π_T  (a definition; a TYPE definition when the
  ||| type is 𝕍 — then π derives the type and π_T is the leaf 𝕍),
  ||| with the erasures |π| and |π_T|
  SigDef : Ctx -> SigIdentifier -> (body : Elem) -> (ty : Ty) -> (bodyD : Drv) -> (tyD : Drv) -> SigEntry
  ||| Γ ⊦ x : π_T  (a declaration — a hole; references are stuck,
  ||| el-sig-decl; a TYPE declaration when the type is 𝕍; an
  ||| equation OBLIGATION when it is the equation's prop), with the
  ||| erasure |π_T|
  SigDecl : Ctx -> SigIdentifier -> (ty : Ty) -> (tyD : Drv) -> SigEntry

||| The name a signature entry binds.
public export
sigEntryName : SigEntry -> Maybe SigIdentifier
sigEntryName (SigDef _ x _ _ _ _) = Just x
sigEntryName (SigDecl _ x _ _) = Just x

||| Is this entry a definition? A signature all of whose entries are
||| definitions is DEFINITIONAL (Foundation: acceptance requires it).
public export
sigEntryIsDef : SigEntry -> Bool
sigEntryIsDef (SigDef _ _ _ _ _ _) = True
sigEntryIsDef _ = False

public export
Sig : Type
Sig = SnocList SigEntry

||| Find a signature entry by name (innermost/most-recent declaration wins).
export covering
sigLookup : SigIdentifier -> Sig -> Maybe SigEntry
sigLookup _ [<] = Nothing
sigLookup x (rest :< entry) =
  if sigEntryName entry == Just x then Just entry else sigLookup x rest

-- ===== Renaming the signature names a derivation mentions =====

mutual
  ||| Every signature name inside a derivation mapped (a reference, a
  ||| δ leaf, a δ-all leaf), the structure kept.
  export
  mapNamesD : (String -> String) -> Drv -> Drv
  mapNamesD f d = case d of
    DVar i => DVar i
    DRef x qs => DRef (f x) (map (mapNamesD f) qs)
    DUnit => DUnit
    DZero => DZero
    DZeroTy => DZeroTy
    DOneTy => DOneTy
    DNatTy => DNatTy
    DUniverse => DUniverse
    DProp => DProp
    DTop => DTop
    DRefl q => DRefl (mapNamesD f q)
    DPath sg k qs => DPath (map (mapNamesQTy f) sg) k (map (mapNamesD f) qs)
    DDelta x qs => DDelta (f x) (map (mapNamesD f) qs)
    DReflx => DReflx
    DSym q => DSym (mapNamesD f q)
    DTrans p q => DTrans (mapNamesD f p) (mapNamesD f q)
    DTransAt p m q => DTransAt (mapNamesD f p) (mapNamesD f m) (mapNamesD f q)
    DDeltaAll ns => DDeltaAll (map f ns)
    DIrrel mp => DIrrel (map (mapNamesD f) mp)
    DEtaPi q => DEtaPi (mapNamesD f q)
    DEtaSigma p q => DEtaSigma (mapNamesD f p) (mapNamesD f q)
    DQuotWit mq => DQuotWit (map (mapNamesD f) mq)
    DQuotWitPrf q => DQuotWitPrf (mapNamesD f q)
    DInj q => DInj (mapNamesD f q)
    DPropExt p q => DPropExt (mapNamesD f p) (mapNamesD f q)
    DPrfCong mp mq q => DPrfCong (map (mapNamesD f) mp) (map (mapNamesD f) mq) (mapNamesD f q)
    DConv q mT b => DConv (mapNamesD f q) (map (mapNamesD f) mT) (mapNamesD f b)
    DAt q pT b => DAt (mapNamesD f q) (mapNamesD f pT) (mapNamesD f b)
    DSubst q (MkDSub dp es) => DSubst (mapNamesD f q) (MkDSub dp (map (\(a, b) => (mapNamesD f a, mapNamesD f b)) es))
    DAscribe q mT mb => DAscribe (mapNamesD f q) (map (mapNamesD f) mT) (map (mapNamesD f) mb)
    DLam m q => DLam (map (mapNamesD f) m) (mapNamesD f q)
    DPair m u v => DPair (map (mapNamesD f) m) (mapNamesD f u) (mapNamesD f v)
    DInj1 m q => DInj1 (map (mapNamesD f) m) (mapNamesD f q)
    DInj2 m q => DInj2 (map (mapNamesD f) m) (mapNamesD f q)
    DClass m q => DClass (map (mapNamesD f) m) (mapNamesD f q)
    DSuc q => DSuc (mapNamesD f q)
    DCtor sg k qs => DCtor (map (mapNamesQTy f) sg) k (map (mapNamesD f) qs)
    DCorec dp a g x => DCorec (mapNamesP f dp) (mapNamesD f a) (mapNamesD f g) (mapNamesD f x)
    DLet a b => DLet (mapNamesD f a) (mapNamesD f b)
    DStar m q => DStar (map (mapNamesD f) m) (mapNamesD f q)
    DSq q => DSq (mapNamesD f q)
    DSquashElim m e b => DSquashElim (map (mapNamesD f) m) (mapNamesD f e) (mapNamesD f b)
    DCoind m r p q => DCoind (map (mapNamesD f) m) (mapNamesD f r) (mapNamesD f p) (mapNamesD f q)
    DZeroElim m q => DZeroElim (map (mapNamesD f) m) (mapNamesD f q)
    DNatElim m z st n => DNatElim (map (mapNamesD f) m) (mapNamesD f z) (mapNamesD f st) (mapNamesD f n)
    DSumElim m l r t => DSumElim (map (mapNamesD f) m) (mapNamesD f l) (mapNamesD f r) (mapNamesD f t)
    DQuotElim m wd g q => DQuotElim (map (mapNamesD f) m) (map (mapNamesD f) wd) (mapNamesD f g) (mapNamesD f q)
    DQElim sg k cs cohs ms es w =>
      DQElim (map (mapNamesQTy f) sg) k (map (map (mapNamesD f)) cs) (map (mapNamesD f) cohs)
             (map (mapNamesD f) ms) (map (mapNamesD f) es) (mapNamesD f w)
    DOut q => DOut (mapNamesD f q)
    DApp g a => DApp (mapNamesD f g) (mapNamesD f a)
    DProj1 q => DProj1 (mapNamesD f q)
    DProj2 q => DProj2 (mapNamesD f q)
    DPi a b => DPi (mapNamesD f a) (mapNamesD f b)
    DSigma a b => DSigma (mapNamesD f a) (mapNamesD f b)
    DSum a b => DSum (mapNamesD f a) (mapNamesD f b)
    DEq l r t => DEq (mapNamesD f l) (mapNamesD f r) (mapNamesD f t)
    DQuot a r => DQuot (mapNamesD f a) (mapNamesD f r)
    DSquash q => DSquash (mapNamesD f q)
    DNu dp => DNu (mapNamesP f dp)
    DSort sg k qs => DSort (map (mapNamesQTy f) sg) k (map (mapNamesD f) qs)

  mapNamesQTm : (String -> String) -> DQTm -> DQTm
  mapNamesQTm f (DQVar i) = DQVar i
  mapNamesQTm f (DQAppE t e) = DQAppE (mapNamesQTm f t) (mapNamesD f e)
  mapNamesQTm f (DQAppI t a) = DQAppI (mapNamesQTm f t) (mapNamesQTm f a)
  mapNamesQTm f (DQEqC l r u) = DQEqC (mapNamesQTm f l) (mapNamesQTm f r) (mapNamesQTm f u)

  mapNamesQTy : (String -> String) -> DQTy -> DQTy
  mapNamesQTy f DQU = DQU
  mapNamesQTy f (DQEl t) = DQEl (mapNamesQTm f t)
  mapNamesQTy f (DQPiExt a b) = DQPiExt (mapNamesD f a) (mapNamesQTy f b)
  mapNamesQTy f (DQPiInd u b) = DQPiInd (mapNamesQTm f u) (mapNamesQTy f b)

  mapNamesP : (String -> String) -> DPoly -> DPoly
  mapNamesP f DPHole = DPHole
  mapNamesP f (DPConst a) = DPConst (mapNamesD f a)
  mapNamesP f (DPProd g h) = DPProd (mapNamesP f g) (mapNamesP f h)
  mapNamesP f (DPSum g h) = DPSum (mapNamesP f g) (mapNamesP f h)
  mapNamesP f (DPSigma a g) = DPSigma (mapNamesD f a) (mapNamesP f g)
  mapNamesP f (DPPi a g) = DPPi (mapNamesD f a) (mapNamesP f g)

-- ===== Substitution nodes: lifting, pushing into carriers, layers =====
--
-- The β-whnf on derivations (Nova.Kernel, dWhnf) never substitutes
-- INTO a derivation: it pushes substitution NODES, one level at a
-- time, and a node pushed under a binder is LIFTED — the shape of
-- §10.4 again (the entries weakened by one, the bound variable added
-- at its domain's derivation). Everything here is pure bookkeeping
-- on that shape.

||| The weakening by one, as a substitution node.
export
wk1 : Drv -> Drv
wk1 p = DSubst p (MkDSub 1 [])

||| σ : Γ → Δ lifted under a binder whose domain derivation over Γ is
||| a:  σ↑ : Γ ▷ A → Δ ▷ A[σ], the entries weakened by one and the
||| bound variable ☐₀ added at a.
export
dLift : DSub -> Drv -> DSub
dLift (MkDSub d es) a = MkDSub (S d) (map (\(e, t) => (wk1 e, t)) es ++ [(DVar 0, a)])

mutual
  ||| A substitution node pushed into a carried signature's pieces
  ||| (under the external binders before each, lifted at their domains).
  export
  dSubstQTm : DSub -> DQTm -> DQTm
  dSubstQTm s (DQVar i) = DQVar i
  dSubstQTm s (DQAppE f e) = DQAppE (dSubstQTm s f) (DSubst e s)
  dSubstQTm s (DQAppI f a) = DQAppI (dSubstQTm s f) (dSubstQTm s a)
  dSubstQTm s (DQEqC l r u) = DQEqC (dSubstQTm s l) (dSubstQTm s r) (dSubstQTm s u)

  export
  dSubstQTy : DSub -> DQTy -> DQTy
  dSubstQTy s DQU = DQU
  dSubstQTy s (DQEl t) = DQEl (dSubstQTm s t)
  dSubstQTy s (DQPiExt a b) = DQPiExt (DSubst a s) (dSubstQTy (dLift s a) b)
  dSubstQTy s (DQPiInd u b) = DQPiInd (dSubstQTm s u) (dSubstQTy s b)

export
dSubstQSig : DSub -> DQSig -> DQSig
dSubstQSig s = map (dSubstQTy s)

||| … into a carried polynomial's codes.
export
dSubstPoly : DSub -> DPoly -> DPoly
dSubstPoly s DPHole = DPHole
dSubstPoly s (DPConst a) = DPConst (DSubst a s)
dSubstPoly s (DPProd f g) = DPProd (dSubstPoly s f) (dSubstPoly s g)
dSubstPoly s (DPSum f g) = DPSum (dSubstPoly s f) (dSubstPoly s g)
dSubstPoly s (DPSigma a f) = DPSigma (DSubst a s) (dSubstPoly (dLift s a) f)
dSubstPoly s (DPPi a f) = DPPi (DSubst a s) (dSubstPoly (dLift s a) f)

||| A value or a stuck head under its substitution layers (innermost
||| first), and the layers put back.
export
peel : Drv -> (Drv, List DSub)
peel (DSubst q s) = let (h, ls) = peel q in (h, ls ++ [s])
peel d = (d, [])

export
underLayers : Drv -> List DSub -> Drv
underLayers d [] = d
underLayers d (s :: ss) = underLayers (DSubst d s) ss

-- ===== The coinductive computation rule, on derivations =====

||| ⌊𝔽⌋(c): the code a polynomial decodes at a code c (reflectPoly on
||| derivations; c's derivation weakened under the binder forms).
export
dReflectPoly : DPoly -> Drv -> Drv
dReflectPoly DPHole c = c
dReflectPoly (DPConst a) c = a
dReflectPoly (DPProd f g) c = DSigma (dReflectPoly f c) (wk1 (dReflectPoly g c))
dReflectPoly (DPSum f g) c = DSum (dReflectPoly f c) (dReflectPoly g c)
dReflectPoly (DPSigma a f) c = DSigma a (dReflectPoly f (wk1 c))
dReflectPoly (DPPi a f) c = DPi a (dReflectPoly f (wk1 c))

||| hᵉˡ ≜ λ (corec 𝔽 a f[↑] ☐₀) — the corecursor as a function
||| derivation (annotated at a: it states).
export
dCorecFun : DPoly -> Drv -> Drv -> Drv
dCorecFun dp a f =
  DLam (Just a) (DCorec (wkDPoly 1 [] dp) (wk1 a) (DSubst f (dLift (MkDSub 1 []) a)) (DVar 0))

||| map_𝔽 g x at the target code nu (= ν 𝔽): mapPoly on derivations,
||| every intro form in inference position annotated as its rule
||| wants (the pair's family, the injection's other summand, the
||| sum-elim's constant motive), so the result STATES.
export
dMapPoly : DPoly -> (nu : Drv) -> (g : Drv) -> (x : Drv) -> Drv
dMapPoly DPHole nu g x = DApp g x
dMapPoly (DPConst a) nu g x = x
dMapPoly (DPProd f h) nu g x =
  DPair (Just (wk1 (dReflectPoly h nu))) (dMapPoly f nu g (DProj1 x)) (dMapPoly h nu g (DProj2 x))
dMapPoly (DPSum f h) nu g x =
  let fT = dReflectPoly f nu
      hT = dReflectPoly h nu
  in DSumElim (Just (wk1 (DSum fT hT)))
              (DInj1 (Just (wk1 hT)) (dMapPoly (wkDPoly 1 [] f) (wk1 nu) (wk1 g) (DVar 0)))
              (DInj2 (Just (wk1 fT)) (dMapPoly (wkDPoly 1 [] h) (wk1 nu) (wk1 g) (DVar 0)))
              x
dMapPoly (DPSigma a f) nu g x =
  DPair (Just (dReflectPoly f (wk1 nu)))
        (DProj1 x)
        (dMapPoly (dSubstPoly (MkDSub 0 [(DProj1 x, a)]) f) nu g (DProj2 x))
dMapPoly (DPPi a f) nu g x =
  DLam (Just a) (dMapPoly f (wk1 nu) (wk1 g) (DApp (wk1 x) (DVar 0)))
