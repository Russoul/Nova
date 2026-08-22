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

||| Component selectors: from a licensed equation between same-headed
||| terms, pass to a component equation. Justified by Foundation's
||| injectivity rules (codes) or derivable congruences (S via pred).
||| Binder components carry their instantiation (el-sub-cong-fix).
public export
data Sel : Type where
  SelSuc : Sel                       -- S x ≐ S y ⇒ x ≐ y : ℕ
  SelDom : Sel                       -- (a₀→b₀) ≐ (a₁→b₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌 (also ⨯)
  SelCod : Elem -> Sel               -- ⇒ b₀[id,u] ≐ b₁[id,u] : 𝕌 (also ⨯)
  SelSumL : Sel                      -- (a₀⊎b₀) ≐ (a₁⊎b₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌
  SelSumR : Sel                      -- ⇒ b₀ ≐ b₁ : 𝕌 (non-dependent: no
                                     -- binder, no instantiation element)
  SelQDom : Sel                      -- (a₀/r₀) ≐ (a₁/r₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌
  SelQRel : Elem -> Elem -> Sel      -- ⇒ r₀[id,u,v] ≐ r₁[id,u,v] : 𝕌
  SelQIdx : Nat -> Sel               -- 𝒮.s ē₀ ≐ 𝒮.s ē₁ : 𝕌 ⇒ ē₀ᵢ ≐ ē₁ᵢ (QIIT
                                     -- code injectivity, indexwise; the spines
                                     -- must agree before i)

||| A step's LICENSE: a proof element whose type exposes an ≡-type
||| (equality reflection read certificate-side), or a PATH LICENSE —
||| an imposed equation of a QIIT signature (el-qiit-path): entry
||| position plus the full argument spine. The carried signature is
||| validated by the descent's positional type check at the rewrite
||| site (the licensed equation's type embeds it syntactically).
public export
data StepLic : Type where
  LProof : Elem -> StepLic
  LPath : QSig -> Nat -> SubNorm -> StepLic

||| One replay step: at `path` (child indices; binders crossed are
||| counted by the walk itself) in the chosen side, rewrite by the
||| licensed equation, after applying `sels` and possibly flipping.
public export
record Step where
  constructor MkStep
  onLhs : Bool
  path : List Nat
  lic : StepLic
  sels : List Sel
  flip : Bool

mutual
  public export
  data Payload : Type where
    ||| eliminator motive (ℕ-elim: over Γ ▷ ℕ; quot-elim: over Γ ▷ A/R)
    PMotive : Ty -> Skel -> Payload
    ||| expected type of an introduction form in inference position
    PIntroTy : Ty -> Skel -> Payload
    ||| conversion certificate at a switch site (inferred ≐ expected)
    PSwitch : ECert -> Payload
    ||| the equation behind a ⋆ checked at an equality prop (el-eq-i)
    PReflEq : ECert -> Payload
    ||| quot-elim well-definedness (f respects R)
    PWD : ECert -> Payload
    ||| head exposure at a checked introduction form: the expected type
    ||| rewritten to expose its Π/Σ/quotient/≡/Prf head, with the
    ||| certificate for the conversion. The exposed type's own
    ||| well-formedness follows from the original's by subject
    ||| reduction; the intro checks against the exposed form and
    ||| coercion transports the result.
    PExpose : Ty -> ECert -> Payload
    ||| the witness behind a checked ⋆ : Prf ∥A∥ (el-squash-i: an
    ||| inhabitant of the squashee)
    PSquashWit : Elem -> Skel -> Payload
    ||| the hypothetical proof behind a checked squash-elim
    ||| (el-squash-e-prf): scrutinee inhabiting Prf ∥A∥, plus a body
    ||| proving (Prf q)[↑] under the raw squashee A
    PSquashElim : Elem -> Skel -> Elem -> Skel -> Payload
    ||| QIIT eliminator coherences — one certificate per equation entry
    ||| of the carried signature, replayed in the entry's ᴰ-context
    ||| (the QIIT generalization of quot-elim's wd)
    PQCoh : List ECert -> Payload
    ||| coinduction behind a ⋆ checked at an equality prop over a
    ||| ν-type (el-nu-coind): the invariant R (Ω-valued, two bound
    ||| variables), the proof that R holds at the equation's
    ||| endpoints, and the one-step closure — R implies the RELATOR
    ||| lift_𝔽(R) after one observation — each with its skeleton
    PNuCoind : Elem -> Skel -> Elem -> Skel -> Elem -> Skel -> Payload

  public export
  data Skel : Type where
    Nd : List Payload -> List Skel -> Skel

  public export
  data Final : Type where
    ||| compare beta-normal forms
    FBeta : Final
    ||| the equation's type normalizes to 𝟙 or 𝟘 (el-one-prop/
    ||| el-zero-prop) or to Prf p (el-prf-prop: proof irrelevance)
    FProp : Final
    ||| class a ≐ class b at A / R via the relation's shape:
    ||| R[id,a,b] ⇝ ∥T∥ with T ⇝ 𝟙 (witness ()) or T ⇝ an ≡-type whose
    ||| equation the nested certificate establishes (witness ⋆;
    ||| el-quot-eq)
    FWitness : Maybe ECert -> Final
    ||| el-quot-eq with the witness SUPPLIED: class a ≐ class b at
    ||| A / R by a proof of Prf R[id,a,b], checked with its skeleton.
    ||| FWitness above re-derives the witness from the relation's
    ||| SHAPE and so reaches only ∥𝟙∥ and equality props; this is the
    ||| faithful route, at an arbitrary Ω-valued relation — the
    ||| premise of el-quot-eq, presented.
    FWitnessPrf : Elem -> Skel -> Final
    ||| same-tag injections at A ⊎ B are equal when their payloads are
    ||| (congruence of ≐ at inj₁/inj₂); the nested certificate proves
    ||| the payload equation at the branch type
    FInj : ECert -> Final
    ||| el-pi-eta: compare applied to the fresh variable, under the domain
    FEtaPi : ECert -> Final
    ||| el-sigma-eta: compare the projections
    FEtaSigma : ECert -> ECert -> Final
    ||| code-prop-eq (propositional extensionality) at Ω: mutually
    ||| implied prop codes are equal. Carries the two implications as
    ||| FUNCTIONS over Γ — f : Prf p → Prf q and g : Prf q → Prf p —
    ||| with their checking skeletons. (Equivalent to carrying the
    ||| hypothetical proofs f ☐₀ / g ☐₀ under Γ ▷ Prf p / Γ ▷ Prf q,
    ||| by Π intro/elim; the function form is what a surface term can
    ||| hand over, since a checked term's variable indices are fixed
    ||| against the context it was written in.)
    FPropExt : Elem -> Skel -> Elem -> Skel -> Final
    ||| ty-prf-cong for a TYPE certificate: both sides are Prf-headed
    ||| and the nested certificate proves the codes equal at Ω
    FPrfCong : ECert -> Final
    ||| ty-quot-cong (reflexive domain) for a TYPE certificate: both
    ||| sides are quotients of the SAME domain and the nested
    ||| certificate proves the relations equal at Ω (under the domain
    ||| twice)
    FQuotCong : ECert -> Final
    ||| ty-pi-cong for a TYPE certificate: domain certificate, then
    ||| codomain certificate under the (right) domain — needed when a
    ||| component's equality is extensional (Ω-valued) and cannot be
    ||| flattened into steps
    FPiCong : ECert -> ECert -> Final
    ||| ty-sigma-cong, same shape
    FSigmaCong : ECert -> ECert -> Final
    ||| ty-sum-cong, componentwise — both components over Γ (no
    ||| binder to cross), needed when a component's equality is
    ||| extensional and cannot flatten into steps
    FSumCong : ECert -> ECert -> Final

  public export
  record ECert where
    constructor MkECertF
    ||| Type bridge: replay the equation at tyX instead of the site's
    ||| type, justified by a TYPE certificate for  site-ty ≐ tyX  (equal
    ||| types have equal PERs). This is the equation-level counterpart
    ||| of the item level's PExpose: it lets steps land at positions
    ||| whose structure only a lemma-normalized type exposes.
    tyEx : Maybe (Ty, ECert)
    steps : List Step
    final : Final
    ||| The site's cited `<def>.eq` unfold licenses (operator-authored,
    ||| via the using clause). The FAST replay tier joins the sides
    ||| under α + the computation rules + exactly these unfoldings —
    ||| the strict conversion subset. Soundness never depends on the
    ||| list (everything the licensed join equates is δβ-equal, and the
    ||| full-δβ tier remains the fallback); it only bounds the fast
    ||| tier's work to what the source names.
    unfolds : List String

public export
MkECert : List Step -> Final -> ECert
MkECert steps final = MkECertF Nothing steps final []

-- ===== Fuel monad =====

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

data KM : Type -> Type where
  MkKM : (KSt -> Either KErr (a, KSt)) -> KM a

runKMSt : KM a -> KSt -> Either KErr (a, KSt)
runKMSt (MkKM f) = f

runKM : KM a -> Nat -> Either KErr (a, Nat)
runKM m n = map (mapSnd fuel) (runKMSt m (MkKSt n empty empty))

Functor KM where
  map f (MkKM g) = MkKM $ \n => map (mapFst f) (g n)

Applicative KM where
  pure x = MkKM $ \n => Right (x, n)
  (MkKM f) <*> (MkKM g) = MkKM $ \n => do
    (h, n') <- f n
    (x, n'') <- g n'
    Right (h x, n'')

Monad KM where
  (MkKM f) >>= k = MkKM $ \n => do
    (x, n') <- f n
    runKMSt (k x) n'

kerr : KErr -> KM a
kerr e = MkKM $ \_ => Left e

||| One ≜-contraction's worth of fuel.
burn : KM ()
burn = MkKM $ \st => case st.fuel of
  Z => Left "kernel: out of fuel"
  S m => Right ((), { fuel := m } st)

kNfElemGet : String -> KM (Maybe Elem)
kNfElemGet x = MkKM $ \st => Right (lookup x st.nfE, st)

kNfElemPut : String -> Elem -> KM Elem
kNfElemPut x v = MkKM $ \st => Right (v, { nfE $= insert x v } st)

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
  kElem sig (Prf p) = Prf <$> kElem sig p
  -- El-decoding (ty-el-*), one fuel per decode step
  kElem sig (El e) = do
    e' <- kElem sig e
    case e' of
      Elem.ZeroTy => do burn; pure Elem.ZeroTy
      Elem.OneTy => do burn; pure Elem.OneTy
      Elem.NatTy => do burn; pure Elem.NatTy
      Elem.PiTy a b => do burn; kElem sig (Elem.PiTy (El a) (El b))
      Elem.SigmaTy a b => do burn; kElem sig (Elem.SigmaTy (El a) (El b))
      Elem.SumTy a b => do burn; kElem sig (Elem.SumTy (El a) (El b))
      QuotTy a r => do burn; kElem sig (QuotTy (El a) r)
      QSort sg k es => do burn; pure (QSort sg k es)   -- ty-el-qiit
      Elem.NuTy f => do burn; pure (Elem.NuTy f)       -- ty-el-nu
      _ => pure (El e')
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
      -- code-squash-prf: ∥Prf p∥ ≜ p (squash is idempotent on props)
      Prf p => do burn; pure p
      _ => pure (Squash t')
  kElem sig Star = pure Star
  kElem sig (QSort sg k es) = [| QSort (kQSig sig sg) (pure k) (kSubNorm sig es) |]
  kElem sig (QCtor sg k es) = [| QCtor (kQSig sig sg) (pure k) (kSubNorm sig es) |]
  kElem sig (QElim sg k ms fs es w) = do
    sg' <- kQSig sig sg
    ms' <- traverse (kTy sig) ms
    fs' <- traverse (kElem sig) fs
    es' <- kSubNorm sig es
    w' <- kElem sig w
    case w' of
      -- el-qiit-beta: fires only when the carried signatures are
      -- IDENTICAL after normalization (structural identity, nameless)
      QCtor sgW c theta =>
        if sgW == sg'
          then do burn
                  case qElimBetaRhs sg' ms' fs' c theta of
                    Right rhs => kElem sig rhs
                    Left err => kerr "kernel: \{err}"
          else pure (QElim sg' k ms' fs' es' w')
      _ => pure (QElim sg' k ms' fs' es' w')
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

  kQSig : Sig -> QSig -> KM QSig
  kQSig sig = traverse (kQTy sig)

  ||| Beta-normal form of a type — one sort: types are terms, one
  ||| normalizer (El-decoding lives in kElem's El clause; signature
  ||| unfolding is el-sig-beta uniformly, type entries included).
  export
  kTy : Sig -> Ty -> KM Ty
  kTy = kElem

-- ===== The strict-subset fast tier =====
--
-- The kernel's side of the αβ-conversion architecture (docs/
-- PerfNotes.md, "The αβ-conversion survey"): a certificate's cited
-- `<def>.eq` licenses bound a JOIN normalizer — α + the computation
-- rules + exactly the licensed term unfoldings, with TYPE heads
-- exposing freely (the head-exposure discipline; per-item type
-- whitelists are future surface syntax) — and head matches use fueled
-- weak-head normalization instead of full normalization. Replay tries
-- this tier first and falls back to the full-δβ path, so acceptance
-- only ever grows: everything the licensed join equates is δβ-equal.
-- The fallback keeps every pre-strict certificate replayable during
-- the migration; a fully migrated corpus lets it be deleted.

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
  kWhnfE sig (SigVar x es) =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef _ _ a _) => do burn; kWhnfE sig (substElem a (embed es))
      _ => pure (SigVar x es)
  kWhnfE sig (QuotElim f q) = do
    q' <- kWhnfE sig q
    case q' of
      Class a => do burn; kWhnfE sig (substElem f (Ext Id a))
      _ => pure (QuotElim f q')
  kWhnfE sig (Squash t) = do
    t' <- kWhnfT sig t
    case t' of
      Prf p => do burn; kWhnfE sig p
      _ => pure (Squash t')
  kWhnfE sig (QElim sg k ms fs es w) = do
    w' <- kWhnfE sig w
    case w' of
      QCtor sgW c theta =>
        if sgW == sg
          then do burn
                  case qElimBetaRhs sg ms fs c theta of
                    Right rhs => kWhnfE sig rhs
                    Left _ => pure (QElim sg k ms fs es (QCtor sgW c theta))
          else pure (QElim sg k ms fs es (QCtor sgW c theta))
      _ => pure (QElim sg k ms fs es w')
  kWhnfE sig (Out t) = do
    t' <- kWhnfE sig t
    case t' of
      Corec p a f x => do burn; kWhnfE sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      _ => pure (Out t')
  kWhnfE sig (El e) = do
    e' <- kWhnfE sig e
    case e' of
      Elem.ZeroTy => do burn; pure Elem.ZeroTy
      Elem.OneTy => do burn; pure Elem.OneTy
      Elem.NatTy => do burn; pure Elem.NatTy
      Elem.PiTy a b => do burn; pure (Elem.PiTy (El a) (El b))
      Elem.SigmaTy a b => do burn; pure (Elem.SigmaTy (El a) (El b))
      Elem.SumTy a b => do burn; pure (Elem.SumTy (El a) (El b))
      QuotTy a r => do burn; pure (QuotTy (El a) r)
      QSort sg k es => do burn; pure (QSort sg k es)
      Elem.NuTy f => do burn; pure (Elem.NuTy f)
      _ => pure (El e')
  kWhnfE sig e = pure e

  ||| One sort: one weak-head normalizer.
  export
  kWhnfT : Sig -> Ty -> KM Ty
  kWhnfT = kWhnfE

mutual
  kJoinSubNorm : List String -> Sig -> SubNorm -> KM SubNorm
  kJoinSubNorm u sig [<] = pure [<]
  kJoinSubNorm u sig (es :< e) = [| kJoinSubNorm u sig es :< kJoinElem u sig e |]

  ||| The licensed-join normal form: every computation rule, plus
  ||| unfolding of exactly the licensed term definitions. The strict
  ||| conversion subset's normalizer.
  kJoinElem : List String -> Sig -> Elem -> KM Elem
  kJoinElem u sig (CtxVar n) = pure (CtxVar n)
  kJoinElem u sig (ZeroElim t) = ZeroElim <$> kJoinElem u sig t
  kJoinElem u sig OneIntro = pure OneIntro
  kJoinElem u sig NatIntro0 = pure NatIntro0
  kJoinElem u sig (NatIntro1 t) = NatIntro1 <$> kJoinElem u sig t
  kJoinElem u sig (NatElim z s t) = do
    z' <- kJoinElem u sig z
    s' <- kJoinElem u sig s
    t' <- kJoinElem u sig t
    case t' of
      NatIntro0 => do burn; pure z'
      NatIntro1 n => do burn; kJoinElem u sig (substElem s' (Ext (Ext Id n) (NatElim z' s' n)))
      _ => pure (NatElim z' s' t')
  kJoinElem u sig (PiIntro f) = PiIntro <$> kJoinElem u sig f
  kJoinElem u sig (PiApp f e) = do
    e' <- kJoinElem u sig e
    f' <- kJoinElem u sig f
    case f' of
      PiIntro g => do burn; kJoinElem u sig (substElem g (Ext Id e'))
      _ => pure (PiApp f' e')
  kJoinElem u sig (Let a b) = do
    burn
    kJoinElem u sig (substElem b (Ext (Ext Id a) Star))
  kJoinElem u sig (SigmaIntro a b) = [| SigmaIntro (kJoinElem u sig a) (kJoinElem u sig b) |]
  kJoinElem u sig (SigmaElim1 t) = do
    t' <- kJoinElem u sig t
    case t' of
      SigmaIntro a _ => do burn; pure a
      _ => pure (SigmaElim1 t')
  kJoinElem u sig (SigmaElim2 t) = do
    t' <- kJoinElem u sig t
    case t' of
      SigmaIntro _ b => do burn; pure b
      _ => pure (SigmaElim2 t')
  kJoinElem u sig (Inj1 t) = Inj1 <$> kJoinElem u sig t
  kJoinElem u sig (Inj2 t) = Inj2 <$> kJoinElem u sig t
  kJoinElem u sig (SumElim l r t) = do
    l' <- kJoinElem u sig l
    r' <- kJoinElem u sig r
    t' <- kJoinElem u sig t
    case t' of
      Inj1 a => do burn; kJoinElem u sig (substElem l' (Ext Id a))
      Inj2 b => do burn; kJoinElem u sig (substElem r' (Ext Id b))
      _ => pure (SumElim l' r' t')
  kJoinElem u sig Elem.ZeroTy = pure Elem.ZeroTy
  kJoinElem u sig Elem.OneTy = pure Elem.OneTy
  kJoinElem u sig Elem.NatTy = pure Elem.NatTy
  kJoinElem u sig UniverseTy = pure UniverseTy
  kJoinElem u sig PropTy = pure PropTy
  kJoinElem u sig TopTy = pure TopTy
  kJoinElem u sig (Prf p) = Prf <$> kJoinElem u sig p
  -- El: TYPE heads expose freely (El-decoding through weak-head δ of
  -- the code) — the head-exposure discipline; the code position joins
  -- under the licenses only.
  kJoinElem u sig (El e) = do
    e' <- kJoinElem u sig e
    w <- kWhnfE sig e'
    case w of
      Elem.ZeroTy => do burn; pure Elem.ZeroTy
      Elem.OneTy => do burn; pure Elem.OneTy
      Elem.NatTy => do burn; pure Elem.NatTy
      Elem.PiTy a b => do burn; kJoinElem u sig (Elem.PiTy (El a) (El b))
      Elem.SigmaTy a b => do burn; kJoinElem u sig (Elem.SigmaTy (El a) (El b))
      Elem.SumTy a b => do burn; kJoinElem u sig (Elem.SumTy (El a) (El b))
      QuotTy a r => do burn; kJoinElem u sig (QuotTy (El a) r)
      QSort sg k es => do burn; [| QSort (kJoinQSig u sig sg) (pure k) (kJoinSubNorm u sig es) |]
      Elem.NuTy f => do burn; Elem.NuTy <$> kJoinPoly u sig f
      _ => pure (El e')
  kJoinElem u sig (Elem.PiTy a b) = [| Elem.PiTy (kJoinElem u sig a) (kJoinElem u sig b) |]
  kJoinElem u sig (Elem.SigmaTy a b) = [| Elem.SigmaTy (kJoinElem u sig a) (kJoinElem u sig b) |]
  kJoinElem u sig (Elem.SumTy a b) = [| Elem.SumTy (kJoinElem u sig a) (kJoinElem u sig b) |]
  kJoinElem u sig (Elem.EqTy l r t) = [| Elem.EqTy (kJoinElem u sig l) (kJoinElem u sig r) (kJoinTy u sig t) |]
  kJoinElem u sig (QuotTy a r) = [| QuotTy (kJoinElem u sig a) (kJoinElem u sig r) |]
  kJoinElem u sig (SigVar x es) = do
    es' <- kJoinSubNorm u sig es
    -- TYPE definitions (classifier TopTy) expose freely — the
    -- head-exposure discipline; other definitions unfold only when
    -- licensed. (The old kJoinTy/kJoinElem split dispatched this on
    -- POSITION; one sort dispatches it on the entry's classifier,
    -- which is what "type definition" always meant.)
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef _ _ a TopTy) => do
        burn
        nfa <- kJoinElem u sig a
        case es' of
          [<] => pure nfa
          _ => kJoinElem u sig (substElem nfa (embed es'))
      Just (SigDef _ _ a _) =>
        if elem x u
          then do
            burn
            nfa <- kJoinElem u sig a
            case es' of
              [<] => pure nfa
              _ => kJoinElem u sig (substElem nfa (embed es'))
          else pure (SigVar x es')
      _ => pure (SigVar x es')
  kJoinElem u sig (Class a) = Class <$> kJoinElem u sig a
  kJoinElem u sig (QuotElim f q) = do
    q' <- kJoinElem u sig q
    f' <- kJoinElem u sig f
    case q' of
      Class a => do burn; kJoinElem u sig (substElem f' (Ext Id a))
      _ => pure (QuotElim f' q')
  kJoinElem u sig (Squash t) = do
    t' <- kJoinTy u sig t
    case t' of
      Prf p => do burn; pure p
      _ => pure (Squash t')
  kJoinElem u sig Star = pure Star
  kJoinElem u sig (QSort sg k es) = [| QSort (kJoinQSig u sig sg) (pure k) (kJoinSubNorm u sig es) |]
  kJoinElem u sig (QCtor sg k es) = [| QCtor (kJoinQSig u sig sg) (pure k) (kJoinSubNorm u sig es) |]
  kJoinElem u sig (QElim sg k ms fs es w) = do
    sg' <- kJoinQSig u sig sg
    ms' <- traverse (kJoinTy u sig) ms
    fs' <- traverse (kJoinElem u sig) fs
    es' <- kJoinSubNorm u sig es
    w' <- kJoinElem u sig w
    case w' of
      QCtor sgW c theta =>
        if sgW == sg'
          then do burn
                  case qElimBetaRhs sg' ms' fs' c theta of
                    Right rhs => kJoinElem u sig rhs
                    Left err => kerr "kernel: \{err}"
          else pure (QElim sg' k ms' fs' es' w')
      _ => pure (QElim sg' k ms' fs' es' w')
  kJoinElem u sig (Elem.NuTy f) = Elem.NuTy <$> kJoinPoly u sig f
  kJoinElem u sig (Out t) = do
    t' <- kJoinElem u sig t
    case t' of
      Corec p a f x => do burn; kJoinElem u sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      _ => pure (Out t')
  kJoinElem u sig (Corec p a f x) =
    [| Corec (kJoinPoly u sig p) (kJoinElem u sig a) (kJoinElem u sig f) (kJoinElem u sig x) |]

  kJoinPoly : List String -> Sig -> Poly -> KM Poly
  kJoinPoly u sig PHole = pure PHole
  kJoinPoly u sig (PConst a) = [| PConst (kJoinElem u sig a) |]
  kJoinPoly u sig (PProd f g) = [| PProd (kJoinPoly u sig f) (kJoinPoly u sig g) |]
  kJoinPoly u sig (PSum f g) = [| PSum (kJoinPoly u sig f) (kJoinPoly u sig g) |]
  kJoinPoly u sig (PSigma a f) = [| PSigma (kJoinElem u sig a) (kJoinPoly u sig f) |]
  kJoinPoly u sig (PPi a f) = [| PPi (kJoinElem u sig a) (kJoinPoly u sig f) |]

  kJoinQTm : List String -> Sig -> QTm -> KM QTm
  kJoinQTm u sig (QVar i) = pure (QVar i)
  kJoinQTm u sig (QAppE f e) = [| QAppE (kJoinQTm u sig f) (kJoinElem u sig e) |]
  kJoinQTm u sig (QAppI f a) = [| QAppI (kJoinQTm u sig f) (kJoinQTm u sig a) |]
  kJoinQTm u sig (QEqC l r t) = [| QEqC (kJoinQTm u sig l) (kJoinQTm u sig r) (kJoinQTm u sig t) |]

  kJoinQTy : List String -> Sig -> QTy -> KM QTy
  kJoinQTy u sig QU = pure QU
  kJoinQTy u sig (QEl t) = QEl <$> kJoinQTm u sig t
  kJoinQTy u sig (QPiExt a b) = [| QPiExt (kJoinTy u sig a) (kJoinQTy u sig b) |]
  kJoinQTy u sig (QPiInd t b) = [| QPiInd (kJoinQTm u sig t) (kJoinQTy u sig b) |]

  kJoinQSig : List String -> Sig -> QSig -> KM QSig
  kJoinQSig u sig = traverse (kJoinQTy u sig)

  ||| Licensed-join normal form of a TYPE — one sort: one join
  ||| normalizer (the head-exposure discipline dispatches on the
  ||| entry's classifier at kJoinElem's SigVar clause).
  kJoinTy : List String -> Sig -> Ty -> KM Ty
  kJoinTy = kJoinElem

-- ===== Path rewriting =====
--
-- Child indexing (binders in parentheses):
--   Elem: ZeroElim t→0 | NatIntro1 t→0 | NatElim z s t→0,1(2),2
--       | PiIntro f→0(1) | PiApp f e→0,1 | SigmaIntro a b→0,1
--       | SigmaElim1/2 t→0 | PiTyᶜ a b→0,1(1) | SigmaTyᶜ a b→0,1(1)
--       | EqTy l r T→0,1,2ᵗ | QuotTyᶜ a r→0,1(2) | SigVar es→0.. (left
--         to right) | Class a→0 | QuotElim f q→0(1),1 | ∥T∥→0(t)
--   Ty:   PiTy a b→0,1(1) | SigmaTy a b→0,1(1)
--       | El e→0(e) | Prf p→0(e) | QuotTy a r→0,1(e)(2)
--       | SigVar es→0.. (e)
--   (e) marks descent into an Elem child, (t) into a Ty child.

subNormAt : Nat -> SubNorm -> Maybe Elem
subNormAt i es = getAt i (toList es)

subNormSet : Nat -> Elem -> SubNorm -> Maybe SubNorm
subNormSet i e es =
  let xs = toList es in
  case splitAt i xs of
    (pre, _ :: post) => Just (cast (pre ++ e :: post))
    _ => Nothing

mutual
  ||| Rewrite at a path in an element; the transformer receives the
  ||| number of binders crossed.
  pathE : List Nat -> Nat -> (Nat -> Elem -> Either KErr Elem) -> Elem -> Either KErr Elem
  pathE [] b f t = f b t
  pathE (i :: p) b f (ZeroElim t) = if i == 0 then ZeroElim <$> pathE p b f t else Left "kernel: bad path"
  pathE (i :: p) b f (NatIntro1 t) = if i == 0 then NatIntro1 <$> pathE p b f t else Left "kernel: bad path"
  pathE (i :: p) b f (NatElim z s t) =
    case i of
      0 => (\z' => NatElim z' s t) <$> pathE p b f z
      1 => (\s' => NatElim z s' t) <$> pathE p (2 + b) f s
      2 => (\t' => NatElim z s t') <$> pathE p b f t
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (PiIntro g) = if i == 0 then PiIntro <$> pathE p (1 + b) f g else Left "kernel: bad path"
  pathE (i :: p) b f (PiApp g e) =
    case i of
      0 => (\g' => PiApp g' e) <$> pathE p b f g
      1 => (\e' => PiApp g e') <$> pathE p b f e
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (SigmaIntro u v) =
    case i of
      0 => (\u' => SigmaIntro u' v) <$> pathE p b f u
      1 => (\v' => SigmaIntro u v') <$> pathE p b f v
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (SigmaElim1 t) = if i == 0 then SigmaElim1 <$> pathE p b f t else Left "kernel: bad path"
  pathE (i :: p) b f (SigmaElim2 t) = if i == 0 then SigmaElim2 <$> pathE p b f t else Left "kernel: bad path"
  pathE (i :: p) b f (Inj1 t) = if i == 0 then Inj1 <$> pathE p b f t else Left "kernel: bad path"
  pathE (i :: p) b f (Inj2 t) = if i == 0 then Inj2 <$> pathE p b f t else Left "kernel: bad path"
  pathE (i :: p) b f (SumElim l r t) =
    case i of
      0 => (\l' => SumElim l' r t) <$> pathE p (1 + b) f l
      1 => (\r' => SumElim l r' t) <$> pathE p (1 + b) f r
      2 => (\t' => SumElim l r t') <$> pathE p b f t
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (Elem.PiTy a c) =
    case i of
      0 => (\a' => Elem.PiTy a' c) <$> pathE p b f a
      1 => (\c' => Elem.PiTy a c') <$> pathE p (1 + b) f c
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (Elem.SigmaTy a c) =
    case i of
      0 => (\a' => Elem.SigmaTy a' c) <$> pathE p b f a
      1 => (\c' => Elem.SigmaTy a c') <$> pathE p (1 + b) f c
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (Elem.SumTy a c) =
    case i of
      0 => (\a' => Elem.SumTy a' c) <$> pathE p b f a
      1 => (\c' => Elem.SumTy a c') <$> pathE p b f c
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (Elem.EqTy l r t) =
    case i of
      0 => (\l' => Elem.EqTy l' r t) <$> pathE p b f l
      1 => (\r' => Elem.EqTy l r' t) <$> pathE p b f r
      2 => (\t' => Elem.EqTy l r t') <$> pathT p b f t
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (QuotTy a r) =
    case i of
      0 => (\a' => QuotTy a' r) <$> pathE p b f a
      1 => (\r' => QuotTy a r') <$> pathE p (2 + b) f r
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (SigVar x es) =
    case subNormAt i es of
      Just e => do e' <- pathE p b f e
                   case subNormSet i e' es of
                     Just es' => Right (SigVar x es')
                     Nothing => Left "kernel: bad path"
      Nothing => Left "kernel: bad path"
  pathE (i :: p) b f (Class a) = if i == 0 then Class <$> pathE p b f a else Left "kernel: bad path"
  pathE (i :: p) b f (QuotElim g q) =
    case i of
      0 => (\g' => QuotElim g' q) <$> pathE p (1 + b) f g
      1 => (\q' => QuotElim g q') <$> pathE p b f q
      _ => Left "kernel: bad path"
  pathE (i :: p) b f (Squash t) = if i == 0 then Squash <$> pathT p b f t else Left "kernel: bad path"
  pathE _ _ _ _ = Left "kernel: bad path"

  pathT : List Nat -> Nat -> (Nat -> Elem -> Either KErr Elem) -> Ty -> Either KErr Ty
  pathT [] b f t = Left "kernel: path must end at an element"
  pathT (i :: p) b f (PiTy a c) =
    case i of
      0 => (\a' => PiTy a' c) <$> pathT p b f a
      1 => (\c' => PiTy a c') <$> pathT p (1 + b) f c
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (SigmaTy a c) =
    case i of
      0 => (\a' => SigmaTy a' c) <$> pathT p b f a
      1 => (\c' => SigmaTy a c') <$> pathT p (1 + b) f c
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (SumTy a c) =
    case i of
      0 => (\a' => SumTy a' c) <$> pathT p b f a
      1 => (\c' => SumTy a c') <$> pathT p b f c
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (El e) = if i == 0 then El <$> pathE p b f e else Left "kernel: bad path"
  pathT (i :: p) b f (Prf e) = if i == 0 then Prf <$> pathE p b f e else Left "kernel: bad path"
  pathT (i :: p) b f (QuotTy a r) =
    case i of
      0 => (\a' => QuotTy a' r) <$> pathT p b f a
      1 => (\r' => QuotTy a r') <$> pathE p (2 + b) f r
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (SigVar x es) =
    case subNormAt i es of
      Just e => do e' <- pathE p b f e
                   case subNormSet i e' es of
                     Just es' => Right (SigVar x es')
                     Nothing => Left "kernel: bad path"
      Nothing => Left "kernel: bad path"
  pathT _ _ _ _ = Left "kernel: bad path"

liftEither : Either KErr a -> KM a
liftEither (Left e) = kerr e
liftEither (Right x) = pure x

liftQ : Either QErr a -> KM a
liftQ (Left e) = kerr "kernel: \{e}"
liftQ (Right x) = pure x

-- ===== Proof-element inference =====
--
-- Certificate proofs are elimination spines: context variables,
-- signature references, applications and projections. Checking an
-- argument: ⋆ is accepted at an evident Prf (a squashed 𝟙, or an
-- equality prop with beta-equal sides — el-eq-i); anything else is
-- inferred and its type compared by beta. This tiny checker is all
-- the "typing" replay needs.

ctxLookup : Ctx -> Nat -> Maybe Ty
ctxLookup [<] _ = Nothing
ctxLookup (rest :< ty) Z = Just (substTy ty Wk)
ctxLookup (rest :< ty) (S n) = map (\t => substTy t Wk) (ctxLookup rest n)

mutual
  inferP : Sig -> Ctx -> Elem -> KM Ty
  inferP sig ctx (CtxVar i) =
    case ctxLookup ctx i of
      Just ty => pure ty
      Nothing => kerr "kernel: proof variable out of bounds"
  inferP sig ctx (SigVar x es) =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ ty) => do
        checkSubstP sig ctx (toList es) (toList delta)
        pure (substTy ty (embed es))
      -- el-sig-decl: a declaration reference types like a def reference
      Just (SigDecl delta _ ty) => do
        checkSubstP sig ctx (toList es) (toList delta)
        pure (substTy ty (embed es))
      _ => kerr "kernel: bad signature reference in proof"
  inferP sig ctx (PiApp f e) = do
    fTy <- inferP sig ctx f >>= kWhnfT sig
    case fTy of
      PiTy a b => do checkP sig ctx e a; pure (substTy b (Ext Id e))
      _ => kerr "kernel: proof applies a non-function"
  inferP sig ctx (SigmaElim1 t) = do
    tTy <- inferP sig ctx t >>= kWhnfT sig
    case tTy of
      SigmaTy a _ => pure a
      _ => kerr "kernel: proof projects a non-pair"
  inferP sig ctx (SigmaElim2 t) = do
    tTy <- inferP sig ctx t >>= kWhnfT sig
    case tTy of
      SigmaTy _ b => pure (substTy b (Ext Id (SigmaElim1 t)))
      _ => kerr "kernel: proof projects a non-pair"
  -- el-nu-e: fully inference-driven, like the projections
  inferP sig ctx (Out t) = do
    tTy <- inferP sig ctx t >>= kWhnfT sig
    case tTy of
      NuTy f => pure (El (reflectPoly f (Elem.NuTy f)))
      _ => kerr "kernel: proof observes a non-ν element"
  inferP sig ctx OneIntro = pure OneTy
  inferP sig ctx NatIntro0 = pure NatTy
  inferP sig ctx (NatIntro1 t) = do checkP sig ctx t NatTy; pure NatTy
  -- universe codes as proof-spine arguments (a generic lemma's 𝕌
  -- parameter materialized at a concrete code, e.g. ℕc, when it
  -- discharges an instantiated goal)
  inferP sig ctx Elem.ZeroTy = pure UniverseTy
  inferP sig ctx Elem.OneTy = pure UniverseTy
  inferP sig ctx Elem.NatTy = pure UniverseTy
  inferP sig ctx (Elem.PiTy a b) = do
    checkP sig ctx a UniverseTy
    checkP sig (ctx :< El a) b UniverseTy
    pure UniverseTy
  inferP sig ctx (Elem.SigmaTy a b) = do
    checkP sig ctx a UniverseTy
    checkP sig (ctx :< El a) b UniverseTy
    pure UniverseTy
  inferP sig ctx (Elem.SumTy a b) = do
    checkP sig ctx a UniverseTy
    checkP sig ctx b UniverseTy
    pure UniverseTy
  inferP sig ctx (QuotTy a r) = do
    checkP sig ctx a UniverseTy
    checkP sig (ctx :< El a :< substTy (El a) Wk) r PropTy
    pure UniverseTy
  inferP sig ctx (Elem.EqTy l r t) = do
    -- code-eq: T an arbitrary type OR 𝕍 itself (type equality is a
    -- proposition; the endpoints then check as types via checkP's
    -- TopTy routing)
    case t of
      TopTy => pure ()
      _ => checkTyP sig ctx t
    checkP sig ctx l t
    checkP sig ctx r t
    pure PropTy
  -- code-squash: ∥A∥ : Ω for any type A
  inferP sig ctx (Squash t) = do
    checkTyP sig ctx t
    pure PropTy
  -- code-qiit as a proof-spine argument (a 𝕌 parameter materialized
  -- at a QIIT sort code)
  inferP sig ctx (QSort sg k es) = do
    sg' <- kQSig sig sg
    if qSigSmall sg' then pure ()
      else kerr "kernel: universe code for a LARGE signature (code-qiit requires smallness)"
    checkQSpineP sig ctx sg' k es
    pure UniverseTy
  -- el-qiit-elim as a proof-spine element (an unfolded recursive
  -- definition applied inside a lemma instantiation). Motives, methods,
  -- index spine and scrutinee are checked by this tiny checker; a
  -- proof-fragment eliminator carries no coherence certificates, so
  -- each imposed method-image equation is verified by PURE β — both
  -- sides must normalize to identical forms.
  inferP sig ctx (QElim sg k mots mths es w) = do
    sg' <- kQSig sig sg
    entry <- case qEntry sg' k of
               Just x => pure x
               Nothing => kerr "kernel: eliminator sort out of range"
    case qEntryKind entry of
      QKSort => pure ()
      _ => kerr "kernel: eliminator at a non-sort position"
    let sortPs = qPositions QKSort sg'
    let pointPs = qPositions QKPoint sg'
    let eqPs = qPositions QKEq sg'
    if length mots /= length sortPs
      then kerr "kernel: eliminator motive count mismatch" else pure ()
    if length mths /= length pointPs
      then kerr "kernel: eliminator method count mismatch" else pure ()
    let goMotives : List Nat -> List Ty -> KM ()
        goMotives [] [] = pure ()
        goMotives (sj :: sjs) (mot :: rest) = do
          sjE <- case qEntry sg' sj of
                   Just x => pure x
                   Nothing => kerr "kernel: sort out of range"
          (tel, wEnd, _) <- liftQ (reflTel sg' (qwAt sj) sjE)
          let mctx = foldl (:<) ctx tel
          let selfTy = QSort (substQSig sg' wEnd.ups) sj (varSpine (length tel))
          checkTyP sig (mctx :< selfTy) mot
          goMotives sjs rest
        goMotives _ _ = kerr "kernel: eliminator motive count mismatch"
    let goMethods : List Nat -> List Elem -> KM ()
        goMethods [] [] = pure ()
        goMethods (cj :: cjs) (m :: rest) = do
          mty <- liftQ (methodTy sg' mots cj)
          checkP sig ctx m mty
          goMethods cjs rest
        goMethods _ _ = kerr "kernel: eliminator method count mismatch"
    let goCoherences : List Nat -> KM ()
        goCoherences [] = pure ()
        goCoherences (ej :: ejs) = do
          (_, _, lhs, rhs, cty) <- liftQ (coherenceAt sg' mots mths ej)
          ctyN <- kTy sig cty
          case ctyN of
            -- a prop-flavored eliminator: its coherences hold outright
            -- by proof irrelevance (el-prf-prop)
            Prf _ => pure ()
            _ => do
              lhs' <- kElem sig lhs
              rhs' <- kElem sig rhs
              if lhs' == rhs' then pure ()
                else kerr "kernel: eliminator coherence does not hold by β"
          goCoherences ejs
    goMotives sortPs mots
    goMethods pointPs mths
    goCoherences eqPs
    checkQSpineP sig ctx sg' k es
    checkP sig ctx w (QSort sg' k es)
    o <- case qOrdinal QKSort sg' k of
           Just x => pure x
           Nothing => kerr "kernel: eliminator sort ordinal"
    motK <- case getAt o mots of
              Just m => pure m
              Nothing => kerr "kernel: eliminator motive missing"
    pure (substTy motK (Ext (foldl Ext Id (toList es)) w))
  inferP sig ctx e = kerr "kernel: proof element not inferable: \{show e}"

  checkP : Sig -> Ctx -> Elem -> Ty -> KM ()
  -- checking against 𝕍 IS type-formation checking (the dissolved
  -- type judgement): route before any element-directed clause, so
  -- e.g. 𝟘-elim/ℕ-elim at 𝕍 are correctly rejected (no motive at 𝕍)
  checkP sig ctx e TopTy = checkTyP sig ctx e
  checkP sig ctx (Class a) ty = do
    ty' <- kTy sig ty
    case ty' of
      QuotTy dom _ => checkP sig ctx a dom
      _ => kerr "kernel: class proof at non-quotient type"
  -- ⋆ as a proof argument: accepted at an EVIDENT Prf — a squashed 𝟙
  -- (el-squash-i with the evident witness), or an equality prop with
  -- beta-equal sides (el-eq-i)
  checkP sig ctx Star ty = do
    ty' <- kTy sig ty
    case ty' of
      Prf p => do
        p' <- kElem sig p
        case p' of
          Squash sq => do
            sq' <- kTy sig sq
            case sq' of
              OneTy => pure ()
              _ => kerr "kernel: ⋆ proof at a non-evident squash"
          Elem.EqTy l r _ => do
            l' <- kElem sig l
            r' <- kElem sig r
            if l' == r' then pure () else kerr "kernel: ⋆ proof at a non-evident equation"
          _ => kerr "kernel: ⋆ proof at a non-evident proposition"
      _ => kerr "kernel: ⋆ proof at a non-Prf type"
  checkP sig ctx (SigmaIntro u v) ty = do
    ty' <- kTy sig ty
    case ty' of
      SigmaTy a b => do checkP sig ctx u a; checkP sig ctx v (substTy b (Ext Id u))
      _ => kerr "kernel: pair proof at non-⨯ type"
  -- el-sum-i₁ / el-sum-i₂ as proof arguments
  checkP sig ctx (Inj1 a) ty = do
    ty' <- kTy sig ty
    case ty' of
      SumTy dom _ => checkP sig ctx a dom
      _ => kerr "kernel: inj₁ proof at non-⊎ type"
  checkP sig ctx (Inj2 b) ty = do
    ty' <- kTy sig ty
    case ty' of
      SumTy _ cod => checkP sig ctx b cod
      _ => kerr "kernel: inj₂ proof at non-⊎ type"
  -- ⊎-elim with a CONSTANT motive (approximation A1): the el-sum-e
  -- instance whose motive is T[↑]; the scrutinee's ⊎-type is inferred
  checkP sig ctx (SumElim l r t) ty = do
    tTy <- inferP sig ctx t >>= kWhnfT sig
    case tTy of
      SumTy a b => do
        checkP sig (ctx :< a) l (substTy ty Wk)
        checkP sig (ctx :< b) r (substTy ty Wk)
      _ => kerr "kernel: ⊎-elim proof scrutinee at non-⊎ type"
  -- el-nu-i as a proof argument: the carried 𝔽 must be nf-identical to
  -- the expected ν-type's
  checkP sig ctx (Corec p a f x) ty = do
    ty' <- kTy sig ty
    case ty' of
      NuTy pT => do
        p' <- kPoly sig p
        pT' <- kPoly sig pT
        if p' == pT' then pure () else kerr "kernel: corec proof carries a different polynomial than its ν-type"
        checkP sig ctx a UniverseTy
        checkP sig (ctx :< El a) f (substTy (El (reflectPoly p a)) Wk)
        checkP sig ctx x (El a)
      _ => kerr "kernel: corec proof at non-ν type"
  -- el-qiit-intro as a proof argument (spec §3): the saturated
  -- constructor at its sort, the term's signature nf-identical to the
  -- type's, spine checked entrywise, indices compared
  checkP sig ctx (QCtor sgC c theta) ty = do
    ty' <- kTy sig ty
    case ty' of
      QSort sgT srt es => do
        sgC' <- kQSig sig sgC
        if sgC' /= sgT then kerr "kernel: constructor proof at a different signature" else pure ()
        entry <- case qEntry sgC' c of
                   Just x => pure x
                   Nothing => kerr "kernel: constructor proof position out of range"
        case qEntryKind entry of
          QKPoint => pure ()
          _ => kerr "kernel: constructor proof at a non-point position"
        (tel, _, _) <- liftQ (reflTel sgC' (qwAt c) entry)
        let args = toList theta
        if length args /= length tel
          then kerr "kernel: constructor proof spine not saturated" else pure ()
        goSp 0 args tel
        (wEnd, hd) <- liftQ (walkVals sgC' (qwAt c) entry args)
        (srt', idx) <- liftQ (pointHead sgC' wEnd hd)
        if srt' /= srt then kerr "kernel: constructor proof of a different sort" else pure ()
        idxN <- kSubNorm sig idx
        esN <- kSubNorm sig es
        if idxN == esN then pure ()
          else kerr "kernel: constructor proof indices do not match"
      _ => kerr "kernel: constructor proof at a non-QIIT type"
   where
    goSp : Nat -> List Elem -> List Ty -> KM ()
    goSp i [] _ = pure ()
    goSp i (a :: rest) tel = do
      case telInst tel i (toList theta) of
        Just aty => checkP sig ctx a aty
        Nothing => kerr "kernel: constructor proof spine out of range"
      goSp (S i) rest tel
  checkP sig ctx (PiIntro f) ty = do
    ty' <- kTy sig ty
    case ty' of
      PiTy a b => checkP sig (ctx :< a) f b
      _ => kerr "kernel: λ proof at non-Π type"
  checkP sig ctx (ZeroElim t) ty = checkP sig ctx t ZeroTy
  -- ℕ-elim with a CONSTANT motive: sufficient (an instance of ℕ-elim
  -- with motive T[↑]), and exactly what recursive arithmetic arguments
  -- (plus-trees after normalization) need
  checkP sig ctx (NatElim z st t) ty = do
    checkP sig ctx t NatTy
    checkP sig ctx z ty
    checkP sig (ctx :< NatTy :< substTy ty Wk) st (substTy (substTy ty Wk) Wk)
  checkP sig ctx e ty = do
    inferred <- inferP sig ctx e
    i' <- kTy sig inferred
    t' <- kTy sig ty
    if i' == t' then pure () else kerr "kernel: proof argument type mismatch"

  checkSubstP : Sig -> Ctx -> List Elem -> List Ty -> KM ()
  checkSubstP sig ctx es delta =
    if length es /= length delta
      then kerr "kernel: proof substitution length mismatch"
      else go es delta
   where
    -- both lists outermost-first; entry i's type is instantiated by the
    -- previous entries
    go : List Elem -> List Ty -> KM ()
    go [] [] = pure ()
    go es' tys = tick es' tys
     where
      tick : List Elem -> List Ty -> KM ()
      tick [] [] = pure ()
      tick (e :: rest) (ty :: tysRest) = do
        let prefixEs = take (minus (length es) (length (e :: rest))) es
        checkP sig ctx e (substTy ty (embed (cast prefixEs)))
        tick rest tysRest
      tick _ _ = kerr "kernel: proof substitution length mismatch"

  ||| Positional index-spine check against a sort entry's reflected
  ||| binder telescope — the tiny-checker analogue of kQSortSpine.
  checkQSpineP : Sig -> Ctx -> QSig -> Nat -> SubNorm -> KM ()
  checkQSpineP sig ctx sg k es = do
    entry <- case qEntry sg k of
               Just x => pure x
               Nothing => kerr "kernel: sort out of range"
    case qEntryKind entry of
      QKSort => pure ()
      _ => kerr "kernel: index spine at a non-sort position"
    (tel, _, _) <- liftQ (reflTel sg (qwAt k) entry)
    let args = toList es
    if length args /= length tel
      then kerr "kernel: sort index spine arity mismatch" else pure ()
    goIdx 0 args tel
   where
    goIdx : Nat -> List Elem -> List Ty -> KM ()
    goIdx i [] _ = pure ()
    goIdx i (a :: rest) tel = do
      case telInst tel i (toList es) of
        Just aty => checkP sig ctx a aty
        Nothing => kerr "kernel: sort index spine out of range"
      goIdx (S i) rest tel

  ||| Γ ⊦ 𝔽 poly, tiny-checker side (Foundation's poly-* rules): each
  ||| embedded code at 𝕌, the context growing under the binding formers.
  checkPolyP : Sig -> Ctx -> Poly -> KM ()
  checkPolyP sig ctx PHole        = pure ()
  checkPolyP sig ctx (PConst a)   = checkP sig ctx a UniverseTy
  checkPolyP sig ctx (PProd f g)  = do checkPolyP sig ctx f; checkPolyP sig ctx g
  checkPolyP sig ctx (PSum f g)   = do checkPolyP sig ctx f; checkPolyP sig ctx g
  checkPolyP sig ctx (PSigma a f) = do checkP sig ctx a UniverseTy; checkPolyP sig (ctx :< El a) f
  checkPolyP sig ctx (PPi a f)    = do checkP sig ctx a UniverseTy; checkPolyP sig (ctx :< El a) f

  ||| Γ ⊢ A type, tiny-checker side (needed for eliminator motives that
  ||| arrive inside proof spines).
  checkTyP : Sig -> Ctx -> Ty -> KM ()
  checkTyP sig ctx ZeroTy = pure ()
  checkTyP sig ctx OneTy = pure ()
  checkTyP sig ctx NatTy = pure ()
  checkTyP sig ctx UniverseTy = pure ()
  checkTyP sig ctx PropTy = pure ()
  checkTyP sig ctx (PiTy a b) = do
    checkTyP sig ctx a
    checkTyP sig (ctx :< a) b
  checkTyP sig ctx (SigmaTy a b) = do
    checkTyP sig ctx a
    checkTyP sig (ctx :< a) b
  checkTyP sig ctx (SumTy a b) = do
    checkTyP sig ctx a
    checkTyP sig ctx b
  checkTyP sig ctx (El e) = checkP sig ctx e UniverseTy
  checkTyP sig ctx (Prf p) = checkP sig ctx p PropTy
  checkTyP sig ctx (QuotTy a r) = do
    checkTyP sig ctx a
    checkP sig (ctx :< a :< substTy a Wk) r PropTy
  checkTyP sig ctx (QSort sg k es) = do
    sg' <- kQSig sig sg
    checkQSpineP sig ctx sg' k es
  checkTyP sig ctx (NuTy f) = checkPolyP sig ctx f
  checkTyP sig ctx (SigVar x es) =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ TopTy) => checkSubstP sig ctx (toList es) (toList delta)
      Just (SigDecl delta _ TopTy) => checkSubstP sig ctx (toList es) (toList delta)
      _ => kerr "kernel: bad signature reference in proof type"
  -- one sort: everything else (element formers, and 𝕍 itself — no
  -- Γ ⊦ 𝕍 : 𝕍) is not a type former
  checkTyP sig ctx t = kerr "kernel: not a type former in type position"

-- ===== Selector application =====

applySel : Sig -> Ctx -> (Elem, Elem, Ty) -> Sel -> KM (Elem, Elem, Ty)
applySel sig ctx (l, r, _) sel = do
  l' <- kElem sig l
  r' <- kElem sig r
  case (sel, l', r') of
    (SelSuc, NatIntro1 x, NatIntro1 y) => pure (x, y, NatTy)
    (SelDom, Elem.PiTy a0 _, Elem.PiTy a1 _) => pure (a0, a1, UniverseTy)
    (SelDom, Elem.SigmaTy a0 _, Elem.SigmaTy a1 _) => pure (a0, a1, UniverseTy)
    -- binder-crossing selectors: the instantiation elements come from
    -- the (untrusted) certificate, so el-sub-cong-fix's premise is CHECKED
    (SelCod u, Elem.PiTy _ b0, Elem.PiTy a1 b1) => do
      checkP sig ctx u (El a1)
      pure (substElem b0 (Ext Id u), substElem b1 (Ext Id u), UniverseTy)
    (SelCod u, Elem.SigmaTy _ b0, Elem.SigmaTy a1 b1) => do
      checkP sig ctx u (El a1)
      pure (substElem b0 (Ext Id u), substElem b1 (Ext Id u), UniverseTy)
    -- code-sum-inj: non-dependent, both components at 𝕌 directly
    (SelSumL, Elem.SumTy a0 _, Elem.SumTy a1 _) => pure (a0, a1, UniverseTy)
    (SelSumR, Elem.SumTy _ b0, Elem.SumTy _ b1) => pure (b0, b1, UniverseTy)
    (SelQDom, QuotTy a0 _, QuotTy a1 _) => pure (a0, a1, UniverseTy)
    -- code-quot-inj: the relation components live at Ω
    (SelQRel u v, QuotTy _ r0, QuotTy a1 r1) => do
      checkP sig ctx u (El a1)
      checkP sig ctx v (El a1)
      pure (substElem r0 (Ext (Ext Id u) v), substElem r1 (Ext (Ext Id u) v), PropTy)
    -- QIIT code injectivity, indexwise: the signatures and sort must be
    -- nf-identical and the spines must AGREE before i (so the entry
    -- type is determined by the shared prefix). NO selector passes from
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

||| The equation a step licenses (with its type). For a PROOF license:
||| infer the proof, expose the ≡-type (a Prf ∥l ≡ r ∈ t∥ type licenses
||| the same equation — squashed reflection). For a PATH license: the
||| imposed equation of the carried signature at the given spine
||| (el-qiit-path read certificate-side) — the signature itself is
||| validated by the descent's positional type check, which compares
||| the licensed type (embedding 𝒮 syntactically) against the rewrite
||| site's own. Components and orientation apply to both.
licensed : (unfs : List String) -> Sig -> Ctx -> Step -> KM (Elem, Elem, Ty)
licensed pol sig ctx step = do
  (l, r, t) <- base step.lic
  (l', r', t') <- foldlM (applySel sig ctx) (l, r, t) step.sels
  lN <- kJoinElem pol sig l'
  rN <- kJoinElem pol sig r'
  pure (if step.flip then (rN, lN, t') else (lN, rN, t'))
 where
  -- equality is Ω-valued: the one license pathway is a Prf whose prop
  -- normalizes to an equality (squashed spellings converge here by
  -- code-squash-prf during nf)
  exposeEq : Ty -> KM (Elem, Elem, Ty)
  exposeEq (Prf p) = do
    p' <- kWhnfE sig p
    case p' of
      Elem.EqTy l r t => pure (l, r, t)
      _ => kerr "kernel: step proof is not an equality"
  exposeEq _ = kerr "kernel: step proof is not an equality"

  base : StepLic -> KM (Elem, Elem, Ty)
  base (LProof p) = do
    pty <- inferP sig ctx p >>= kWhnfT sig
    exposeEq pty
  base (LPath sg k theta) = do
    sg' <- kQSig sig sg
    entry <- case qEntry sg' k of
               Just e => pure e
               Nothing => kerr "kernel: path license entry out of range"
    case qEntryKind entry of
      QKEq => pure ()
      _ => kerr "kernel: path license at a non-equation entry"
    -- check the spine entrywise against the reflected binder telescope
    (tel, _, _) <- liftQ (reflTel sg' (qwAt k) entry)
    let args = toList theta
    if length args /= length tel
      then kerr "kernel: path license spine length mismatch"
      else pure ()
    checkTelArgs 0 args tel
    -- the imposed equation, at the spine
    (wEnd, hd) <- liftQ (walkVals sg' (qwAt k) entry args)
    (lq, rq, uq) <- liftQ (eqHead hd)
    l <- liftQ (reflTm sg' wEnd lq)
    r <- liftQ (reflTm sg' wEnd rq)
    t <- liftQ (reflCodeTy sg' wEnd uq)
    pure (l, r, t)
   where
    checkTelArgs : Nat -> List Elem -> List Ty -> KM ()
    checkTelArgs i [] _ = pure ()          -- lengths verified above
    checkTelArgs i (e :: rest) tel = do
      case telInst tel i (toList theta) of
        Just ty => checkP sig ctx e ty
        Nothing => kerr "kernel: path license telescope mismatch"
      checkTelArgs (S i) rest tel

  foldlM : (acc -> x -> KM acc) -> acc -> List x -> KM acc
  foldlM f a [] = pure a
  foldlM f a (y :: ys) = f a y >>= \a' => foldlM f a' ys

weakenN : Nat -> Elem -> Elem
weakenN Z e = e
weakenN (S n) e = weakenN n (substElem e Wk)

weakenTyN : Nat -> Ty -> Ty
weakenTyN Z t = t
weakenTyN (S n) t = weakenTyN n (substTy t Wk)

-- ===== Typed path descent =====
--
-- Rewriting a subterm by an equation is congruence — and Foundation's
-- congruences demand the component equation AT THE COMPONENT'S TYPE.
-- The descent below computes each position's expected type from the
-- side's root type, so the licensed equation's type can be verified
-- in situ. Two positions are motive-dependent and use the CONSTANT-
-- MOTIVE reading (a valid ℕ-elim/quot-elim congruence instance whose
-- premises are then demanded at the constant type): ℕ-elim's z/s
-- slots. This is the one acknowledged approximation of the equation
-- kernel; the item-level kernel's motive annotations remove it.

mutual
  ||| Expected type of the child at index i, given (maybe) the parent's
  ||| expected type. Nothing = undetermined there — harmless for path
  ||| positions being passed THROUGH (congruence needs no type at
  ||| intermediate hops), fatal only at the rewrite point itself.
  childTyE : Sig -> Ctx -> Maybe Ty -> Elem -> Nat -> KM (Maybe Ty)
  -- SINGLE-COLUMN matching, deliberately: one clause per former, the
  -- child index (a Nat — nested S-patterns!) and the expected-type
  -- Maybe dispatched in the BODY. The former ⨯ index ⨯ Maybe product
  -- pattern this replaces made the compile-time case tree and its
  -- coverage check the single most expensive item in the file
  -- (~23s / most of the peak RSS).
  childTyE sig ctx pexp (ZeroElim _) i =
    pure (if i == 0 then Just ZeroTy else Nothing)
  childTyE sig ctx pexp (NatIntro1 _) i =
    pure (if i == 0 then Just NatTy else Nothing)
  childTyE sig ctx pexp (NatElim _ _ _) i =
    case i of
      0 => pure pexp                    -- constant-motive reading
      1 => pure (map (weakenTyN 2) pexp)
      2 => pure (Just NatTy)
      _ => pure Nothing
  childTyE sig ctx pexp (PiIntro _) i =
    case (pexp, i) of
      (Just pe, 0) => do
        t <- kWhnfT sig pe
        case t of
          PiTy _ b => pure (Just b)
          _ => pure Nothing
      _ => pure Nothing
  childTyE sig ctx pexp (PiApp f _) i =
    case i of
      1 => do
        mf <- inferNeK sig ctx f
        case mf of
          Just fTy => do
            t <- kWhnfT sig fTy
            case t of
              PiTy a _ => pure (Just a)
              _ => pure Nothing
          Nothing => pure Nothing
      _ => pure Nothing
  childTyE sig ctx pexp (SigmaIntro u _) i =
    case (pexp, i) of
      (Just pe, 0) => do
        t <- kWhnfT sig pe
        case t of
          SigmaTy a _ => pure (Just a)
          _ => pure Nothing
      (Just pe, 1) => do
        t <- kWhnfT sig pe
        case t of
          SigmaTy _ b => pure (Just (substTy b (Ext Id u)))
          _ => pure Nothing
      _ => pure Nothing
  childTyE sig ctx pexp (SigmaElim1 u) i =
    if i == 0 then inferNeK sig ctx u else pure Nothing
  childTyE sig ctx pexp (SigmaElim2 u) i =
    if i == 0 then inferNeK sig ctx u else pure Nothing
  childTyE sig ctx pexp (Inj1 _) i =
    case (pexp, i) of
      (Just pe, 0) => do
        t <- kWhnfT sig pe
        case t of
          SumTy a _ => pure (Just a)
          _ => pure Nothing
      _ => pure Nothing
  childTyE sig ctx pexp (Inj2 _) i =
    case (pexp, i) of
      (Just pe, 0) => do
        t <- kWhnfT sig pe
        case t of
          SumTy _ b => pure (Just b)
          _ => pure Nothing
      _ => pure Nothing
  -- ⊎-elim: the case positions are motive-dependent (undetermined);
  -- the scrutinee's type is neutrally inferable
  childTyE sig ctx pexp (SumElim _ _ t) i =
    if i == 2 then inferNeK sig ctx t else pure Nothing
  -- SHARED formers are typed at both 𝕌 (codes) and 𝕍 (types): the
  -- parent's expected type decides where the components sit. Default
  -- 𝕌 — an element position met only codes before the merge.
  childTyE sig ctx pexp (Elem.SumTy _ _) i =
    if i == 0 || i == 1 then Just <$> compClassifier sig pexp else pure Nothing
  childTyE sig ctx pexp (Elem.PiTy _ _) i =
    if i == 0 || i == 1 then Just <$> compClassifier sig pexp else pure Nothing
  childTyE sig ctx pexp (Elem.SigmaTy _ _) i =
    if i == 0 || i == 1 then Just <$> compClassifier sig pexp else pure Nothing
  -- child 2 of ≡ is its ∈-type — a term at 𝕍 (or 𝕍 itself, which has
  -- no children); children 0/1 sit at it
  childTyE sig ctx pexp (Elem.EqTy _ _ t) i =
    case i of
      0 => pure (Just t)
      1 => pure (Just t)
      2 => pure (Just TopTy)
      _ => pure Nothing
  childTyE sig ctx pexp (QuotTy _ _) i =
    case i of
      0 => Just <$> compClassifier sig pexp
      1 => pure (Just PropTy)
      _ => pure Nothing
  childTyE sig ctx pexp (El _) i =
    pure (if i == 0 then Just UniverseTy else Nothing)
  childTyE sig ctx pexp (Prf _) i =
    pure (if i == 0 then Just PropTy else Nothing)
  childTyE sig ctx pexp (Squash _) i =
    pure (if i == 0 then Just TopTy else Nothing)
  childTyE sig ctx pexp (SigVar x es) i =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ _) =>
        case getAt i (toList delta) of
          Just entryTy =>
            pure (Just (substTy entryTy (embed (cast (take i (toList es))))))
          Nothing => pure Nothing
      Just (SigDecl delta _ _) =>
        case getAt i (toList delta) of
          Just entryTy =>
            pure (Just (substTy entryTy (embed (cast (take i (toList es))))))
          Nothing => pure Nothing
      _ => pure Nothing
  childTyE sig ctx pexp (Class _) i =
    case (pexp, i) of
      (Just pe, 0) => do
        t <- kWhnfT sig pe
        case t of
          QuotTy dom _ => pure (Just dom)
          _ => pure Nothing
      _ => pure Nothing
  childTyE sig ctx pexp (QuotElim _ q) i =
    if i == 1 then inferNeK sig ctx q else pure Nothing
  -- ν formers: out's scrutinee is neutrally inferable; corec's carrier
  -- is a code, its seed at the carrier's decoding (the body, child 1,
  -- is carrier-dependent — undetermined, like ⊎-elim's cases)
  childTyE sig ctx pexp (Out t) i =
    if i == 0 then inferNeK sig ctx t else pure Nothing
  childTyE sig ctx pexp (Corec _ a _ _) i =
    case i of
      0 => pure (Just UniverseTy)
      2 => pure (Just (El a))
      _ => pure Nothing
  -- QIIT formers: spine child i's type is the reflected telescope's
  -- entry i, instantiated by the earlier children — always determined
  childTyE sig ctx pexp (QSort sg k es) i = qSpineChildTy sg k es i
  childTyE sig ctx pexp (QCtor sg k es) i = qSpineChildTy sg k es i
  childTyE sig ctx pexp (QElim sg k _ _ es w) i =
    if i == length (toList es)
      then pure (Just (QSort sg k es))
      else qSpineChildTy sg k es i
  childTyE sig ctx pexp _ _ = pure Nothing

  ||| The classifier a shared former's components sit at: 𝕍 when the
  ||| parent is expected at 𝕍 (a type), 𝕌 otherwise (a code).
  compClassifier : Sig -> Maybe Ty -> KM Ty
  compClassifier sig Nothing = pure UniverseTy
  compClassifier sig (Just pe) = do
    t <- kWhnfT sig pe
    pure (case t of
            TopTy => TopTy
            _ => UniverseTy)

  ||| Expected type of the i-th spine entry of a former carrying 𝒮
  ||| (position k's reflected binder/arity telescope).
  qSpineChildTy : QSig -> Nat -> SubNorm -> Nat -> KM (Maybe Ty)
  qSpineChildTy sg k es i =
    case qEntry sg k of
      Nothing => pure Nothing
      Just entry =>
        case reflTel sg (qwAt k) entry of
          Left _ => pure Nothing
          Right (tel, _, _) => pure (telInst tel i (toList es))

  ||| Neutral inference inside the kernel (spines only).
  inferNeK : Sig -> Ctx -> Elem -> KM (Maybe Ty)
  inferNeK sig ctx (CtxVar i) = pure (ctxLookup ctx i)
  inferNeK sig ctx (PiApp f e) = do
    mf <- inferNeK sig ctx f
    case mf of
      Just fTy => do
        t <- kWhnfT sig fTy
        case t of
          PiTy _ b => pure (Just (substTy b (Ext Id e)))
          _ => pure Nothing
      Nothing => pure Nothing
  inferNeK sig ctx (SigmaElim1 t) = do
    mt <- inferNeK sig ctx t
    case mt of
      Just tTy => do
        t' <- kWhnfT sig tTy
        case t' of
          SigmaTy a _ => pure (Just a)
          _ => pure Nothing
      Nothing => pure Nothing
  inferNeK sig ctx (Out t) = do
    mt <- inferNeK sig ctx t
    case mt of
      Just tTy => do
        t' <- kWhnfT sig tTy
        case t' of
          NuTy f => pure (Just (El (reflectPoly f (Elem.NuTy f))))
          _ => pure Nothing
      Nothing => pure Nothing
  inferNeK sig ctx (SigVar x es) =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef _ _ _ ty) => pure (Just (substTy ty (embed es)))
      Just (SigDecl _ _ ty) => pure (Just (substTy ty (embed es)))
      _ => pure Nothing
  inferNeK sig ctx _ = pure Nothing

||| Typed descent through TYPE positions (declared ahead: goE needs it
||| to cross a ∥-∥ into its squashee): every element child's type is
||| structurally determined. Defined after goE below.
goTy : (unfs : List String) -> Sig -> Ctx -> (Elem, Elem, Ty) -> List Nat -> Nat -> Ty -> KM Ty

||| Typed descent: rewrite at the path, checking the licensed type
||| against each position's expected type.
goE : (unfs : List String) -> Sig -> Ctx -> (Elem, Elem, Ty) -> List Nat -> Nat -> Maybe Ty -> Elem -> KM Elem
goE pol sig ctx lic@(le, re, ltyN) [] b mexp u = do
  expN <- case mexp of
    Just expTy => kJoinTy pol sig expTy
    Nothing =>
      -- the NEUTRAL-SUBTERM rule (spec §6): at a type-undetermined
      -- rewrite point, the subterm's own ⇒ᴺ-type serves in the
      -- positional check — any type a neutral inhabits is
      -- judgementally equal to its synthesized type (typing
      -- inversion: a neutral's typings factor through its head's
      -- declared type plus conversion; the multi-typing the check
      -- guards against lives at INTRO forms, which ⇒ᴺ refuses).
      -- Binder-crossing paths are excluded: the crossed binders'
      -- types are untracked here, so the subterm's variables could
      -- not be resolved against ctx.
      if b == 0
        then do
          mu <- inferNeK sig ctx u
          case mu of
            Just uTy => kJoinTy pol sig uTy
            Nothing => kerr "kernel: step at a type-undetermined position [not inferable: \{show u}]"
        else kerr "kernel: step at a type-undetermined position [b=\{show b}, at \{show u}]"
  -- join-syntactic first; on mismatch, a PER-COMPONENT δβ conversion
  -- rescue — δβ-equal type/subterm pairs whose difference needs an
  -- unlicensed unfold (a lemma statement or type index outside the
  -- cited set) stay verifiable. Sound: δβ is a sub-relation of ≐, and
  -- the rescue widens only this one positional comparison, never the
  -- equation being replayed. DELIBERATELY full δβ, not
  -- license-bounded: bounding by names reachable from the compared
  -- terms is vacuous (that IS full δβ), and the principled bound —
  -- the transitive closure of cited items' acceptance-time license
  -- sets — needs Σ to record those sets and is not known to cover
  -- what the rescues absorb (type indices reach positions no
  -- citation names). Decision 2026-08: keep full δβ here; revisit
  -- together with kWhnf* exposure if the kernel ever goes
  -- fully license-bounded (docs/PerfNotes.md).
  tyOk <- if expN == weakenTyN b ltyN
            then pure True
            else do e1 <- kTy sig expN
                    e2 <- kTy sig (weakenTyN b ltyN)
                    pure (e1 == e2)
  if not tyOk
    then kerr "kernel: step type does not match the position"
    else if u == weakenN b le
      then pure (weakenN b re)
      else do
        u' <- kElem sig u
        le' <- kElem sig (weakenN b le)
        if u' == le'
          then pure (weakenN b re)
          else kerr "kernel: step does not match the subterm"
goE pol sig ctx lic (i :: p) b mexp u = do
  childTy <- childTyE sig ctx mexp u i
  let goQSpine : SubNorm -> (SubNorm -> Elem) -> KM Elem
      goQSpine es re =
        case subNormAt i es of
          Just e => do
            e' <- goE pol sig ctx lic p b childTy e
            case subNormSet i e' es of
              Just es' => pure (re es')
              Nothing => kerr "kernel: bad path"
          Nothing => kerr "kernel: bad path"
  case Just () of
    _ =>
      case (u, i) of
        (ZeroElim t', 0) => ZeroElim <$> goE pol sig ctx lic p b childTy t'
        (NatIntro1 t', 0) => NatIntro1 <$> goE pol sig ctx lic p b childTy t'
        (NatElim z st t', 0) => (\z' => NatElim z' st t') <$> goE pol sig ctx lic p b childTy z
        (NatElim z st t', 1) => (\s' => NatElim z s' t') <$> goE pol sig ctx lic p (2 + b) childTy st
        (NatElim z st t', 2) => (\t'' => NatElim z st t'') <$> goE pol sig ctx lic p b childTy t'
        (PiIntro f, 0) => PiIntro <$> goE pol sig ctx lic p (1 + b) childTy f
        (PiApp f e, 0) => (\f' => PiApp f' e) <$> goE pol sig ctx lic p b childTy f
        (PiApp f e, 1) => PiApp f <$> goE pol sig ctx lic p b childTy e
        (SigmaElim1 t', 0) => SigmaElim1 <$> goE pol sig ctx lic p b childTy t'
        (SigmaElim2 t', 0) => SigmaElim2 <$> goE pol sig ctx lic p b childTy t'
        (Inj1 t', 0) => Inj1 <$> goE pol sig ctx lic p b childTy t'
        (Inj2 t', 0) => Inj2 <$> goE pol sig ctx lic p b childTy t'
        (SumElim l r t', 0) => (\l' => SumElim l' r t') <$> goE pol sig ctx lic p (1 + b) childTy l
        (SumElim l r t', 1) => (\r' => SumElim l r' t') <$> goE pol sig ctx lic p (1 + b) childTy r
        (SumElim l r t', 2) => SumElim l r <$> goE pol sig ctx lic p b childTy t'
        (SigmaIntro x y, 0) => (\x' => SigmaIntro x' y) <$> goE pol sig ctx lic p b childTy x
        (SigmaIntro x y, 1) => SigmaIntro x <$> goE pol sig ctx lic p b childTy y
        (Elem.PiTy a c, 0) => (\a' => Elem.PiTy a' c) <$> goE pol sig ctx lic p b childTy a
        (Elem.PiTy a c, 1) => Elem.PiTy a <$> goE pol sig ctx lic p (1 + b) childTy c
        (Elem.SigmaTy a c, 0) => (\a' => Elem.SigmaTy a' c) <$> goE pol sig ctx lic p b childTy a
        (Elem.SigmaTy a c, 1) => Elem.SigmaTy a <$> goE pol sig ctx lic p (1 + b) childTy c
        (Elem.SumTy a c, 0) => (\a' => Elem.SumTy a' c) <$> goE pol sig ctx lic p b childTy a
        (Elem.SumTy a c, 1) => Elem.SumTy a <$> goE pol sig ctx lic p b childTy c
        (Elem.EqTy l r t', 0) => (\l' => Elem.EqTy l' r t') <$> goE pol sig ctx lic p b childTy l
        (Elem.EqTy l r t', 1) => (\r' => Elem.EqTy l r' t') <$> goE pol sig ctx lic p b childTy r
        (Elem.EqTy l r t', 2) => Elem.EqTy l r <$> goE pol sig ctx lic p b childTy t'
        (QuotTy a r, 0) => (\a' => QuotTy a' r) <$> goE pol sig ctx lic p b childTy a
        (QuotTy a r, 1) => QuotTy a <$> goE pol sig ctx lic p (2 + b) childTy r
        (SigVar x es, _) =>
          case subNormAt i es of
            Just e => do
              e' <- goE pol sig ctx lic p b childTy e
              case subNormSet i e' es of
                Just es' => pure (SigVar x es')
                Nothing => kerr "kernel: bad path"
            Nothing => kerr "kernel: bad path"
        (Class a, 0) => Class <$> goE pol sig ctx lic p b childTy a
        (Out t', 0) => Out <$> goE pol sig ctx lic p b childTy t'
        (Corec pf a f x, 0) => (\a' => Corec pf a' f x) <$> goE pol sig ctx lic p b childTy a
        (Corec pf a f x, 1) => (\f' => Corec pf a f' x) <$> goE pol sig ctx lic p (1 + b) childTy f
        (Corec pf a f x, 2) => Corec pf a f <$> goE pol sig ctx lic p b childTy x
        (QuotElim f q, 0) => (\f' => QuotElim f' q) <$> goE pol sig ctx lic p (1 + b) childTy f
        (QuotElim f q, 1) => QuotElim f <$> goE pol sig ctx lic p b childTy q
        (Squash t, 0) => Squash <$> goE pol sig ctx lic p b childTy t
        (El e2, 0) => El <$> goE pol sig ctx lic p b childTy e2
        (Prf p2, 0) => Prf <$> goE pol sig ctx lic p b childTy p2
        (QSort sg k es, _) => goQSpine es (\es' => QSort sg k es')
        (QCtor sg k es, _) => goQSpine es (\es' => QCtor sg k es')
        (QElim sg k ms fs es w, _) =>
          if i == length (toList es)
            then (\w' => QElim sg k ms fs es w') <$> goE pol sig ctx lic p b childTy w
            else goQSpine es (\es' => QElim sg k ms fs es' w)
        _ => kerr "kernel: bad or type-undetermined path"

||| Apply one step to an element known (by the replay invariant) to be
||| well-typed at tyRoot: descend the path computing expected types,
||| verify the licensed equation's type in situ, rewrite.
stepElem : (unfs : List String) -> Sig -> Ctx -> Step -> Ty -> Elem -> KM Elem
stepElem pol sig ctx step tyRoot t = do
  (le, re, lty) <- licensed pol sig ctx step
  ltyN <- kJoinTy pol sig lty
  goE pol sig ctx (le, re, ltyN) step.path 0 (Just tyRoot) t

goTy pol sig ctx lic p b t = goE pol sig ctx lic p b (Just TopTy) t
-- (one sort, one descent: a type position is an element position
-- expected at 𝕍 — component classifiers thread through childTyE, and
-- an empty path rewrites the type itself by an ≡-at-𝕍 license)

||| Steps inside types: type positions have no element type; every
||| element child's type is structurally determined.
stepTy : (unfs : List String) -> Sig -> Ctx -> Step -> Ty -> KM Ty
stepTy pol sig ctx step t = stepElem pol sig ctx step TopTy t

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

pSwitch : Payload -> Maybe ECert
pSwitch (PSwitch c) = Just c
pSwitch _ = Nothing

pReflEq : Payload -> Maybe ECert
pReflEq (PReflEq c) = Just c
pReflEq _ = Nothing

pWD : Payload -> Maybe ECert
pWD (PWD c) = Just c
pWD _ = Nothing

pExpose : Payload -> Maybe (Ty, ECert)
pExpose (PExpose t c) = Just (t, c)
pExpose _ = Nothing

pSquashWit : Payload -> Maybe (Elem, Skel)
pSquashWit (PSquashWit e sk) = Just (e, sk)
pSquashWit _ = Nothing

pNuCoind : Payload -> Maybe (Elem, Skel, Elem, Skel, Elem, Skel)
pNuCoind (PNuCoind r skR pw skp qw skq) = Just (r, skR, pw, skp, qw, skq)
pNuCoind _ = Nothing

pSquashElim : Payload -> Maybe (Elem, Skel, Elem, Skel)
pSquashElim (PSquashElim e esk b bsk) = Just (e, esk, b, bsk)
pSquashElim _ = Nothing

pQCoh : Payload -> Maybe (List ECert)
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

||| A bare compare-beta-normal-forms certificate: no bridge, no steps,
||| the FBeta final. At α-IDENTICAL sides its replay is a foregone
||| conclusion — the normalizer is a function, so nf(l) = nf(r) on the
||| nose — which licenses the REFLEXIVITY fast path below: same
||| acceptance set as running the replay, none of the normalization.
reflCert : ECert -> Bool
reflCert (MkECertF Nothing [] FBeta _) = True
reflCert _ = False

mutual
  ||| Replay a certificate for the element equation Γ ⊢ l ≐ r : ty,
  ||| in the strict-subset join bounded by the certificate's licenses
  ||| (plus any inherited from the enclosing certificate — sub-replays
  ||| run under the union, as one discharge produced them all).
  export
  kEqElem : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> KM ()
  kEqElem = kEqElemL []

  kEqElemL : (inh : List String) -> Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> KM ()
  kEqElemL inh sig ctx cert l r ty =
    if reflCert cert && l == r then pure ()
      else kEqElemGo (inh ++ cert.unfolds) sig ctx cert l r ty

  kEqElemGo : (unfs : List String) -> Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> KM ()
  kEqElemGo pol sig ctx cert l r ty = do
    -- resolve the type bridge first: the rest of the replay happens at
    -- the (certified-equal) exposed type
    tyU <- case cert.tyEx of
             Nothing => pure ty
             Just (tyX, c) => do
               case ty of
                 TopTy => kerr "kernel: a type equation cannot carry a type bridge"
                 _ => pure ()
               kEqTyL (pol) sig ctx c ty tyX
               pure tyX
    l0 <- kJoinElem pol sig l
    r0 <- kJoinElem pol sig r
    (l1, r1) <- goSteps tyU cert.steps l0 r0
    case cert.final of
      FBeta =>
        if l1 == r1 then pure () else do
          -- δβ rescue, as at the step checks: the replacement may have
          -- introduced vocabulary outside the cited set
          l2 <- kElem sig l1
          r2 <- kElem sig r1
          if l2 == r2 then pure () else kerr "kernel: sides differ after replay"
      FProp => do
        -- head exposure suffices for every final's type match below
        ty' <- kWhnfT sig tyU
        case ty' of
          OneTy => pure ()
          ZeroTy => pure ()
          Prf _ => pure ()      -- el-prf-prop: proof irrelevance
          _ => kerr "kernel: Prop final at a non-propositional type"
      FWitness mc => do
        ty' <- kWhnfT sig tyU
        case (l1, r1, ty') of
          (Class a, Class b, QuotTy dom rel) => do
            relInst <- kJoinElem pol sig (substElem rel (Ext (Ext Id a) b))
            case relInst of
              Squash sq => do
                sq' <- kWhnfT sig sq
                case sq' of
                  OneTy => pure ()
                  _ => kerr "kernel: witness final does not apply"
              Elem.EqTy wl wr wt =>
                case mc of
                  Just c => kEqElemL (pol) sig ctx c wl wr wt
                  Nothing => kerr "kernel: witness final needs a certificate at an equality relation"
              _ => kerr "kernel: witness final at a non-evident relation"
          _ => kerr "kernel: witness final at a non-class equation"
      -- el-quot-eq, faithful: the relation instance is inhabited by
      -- the supplied proof, whatever the relation's shape
      FWitnessPrf w skW => do
        ty' <- kWhnfT sig tyU
        case (l1, r1, ty') of
          (Class a, Class b, QuotTy _ rel) => do
            relInst <- kJoinElem pol sig (substElem rel (Ext (Ext Id a) b))
            kCheckE sig ctx w (Prf relInst) skW
          _ => kerr "kernel: supplied-witness final at a non-class equation"
      FInj c => do
        ty' <- kWhnfT sig tyU
        case (l1, r1, ty') of
          (Inj1 x, Inj1 y, SumTy a _) => kEqElemL (pol) sig ctx c x y a
          (Inj2 x, Inj2 y, SumTy _ b) => kEqElemL (pol) sig ctx c x y b
          _ => kerr "kernel: injection final at a non-matching equation"
      FEtaPi c => do
        ty' <- kWhnfT sig tyU
        case ty' of
          PiTy dom cod =>
            kEqElemL (pol) sig (ctx :< dom) c
              (PiApp (substElem l1 Wk) (CtxVar 0))
              (PiApp (substElem r1 Wk) (CtxVar 0))
              cod
          _ => kerr "kernel: Π-η final at a non-Π type"
      FEtaSigma c1 c2 => do
        ty' <- kWhnfT sig tyU
        case ty' of
          SigmaTy dom cod => do
            kEqElemL (pol) sig ctx c1 (SigmaElim1 l1) (SigmaElim1 r1) dom
            kEqElemL (pol) sig ctx c2 (SigmaElim2 l1) (SigmaElim2 r1)
              (substTy cod (Ext Id (SigmaElim1 l1)))
          _ => kerr "kernel: Σ-η final at a non-Σ type"
      FPropExt s skS t skT => do
        -- code-prop-eq: the sides are prop codes; each direction is an
        -- implication between their decodings
        ty' <- kWhnfT sig tyU
        case ty' of
          PropTy => do
            kCheckE sig ctx s (PiTy (Prf l1) (substTy (Prf r1) Wk)) skS
            kCheckE sig ctx t (PiTy (Prf r1) (substTy (Prf l1) Wk)) skT
          _ => kerr "kernel: propext final at a non-Ω type"
      -- TYPE-equation finals (ambient 𝕍): componentwise congruences
      -- whose component equality is extensional and cannot flatten
      -- into steps — formerly the separate kEqTy replay channel
      FPrfCong c => do
        ty' <- kWhnfT sig tyU
        case (ty', l1, r1) of
          (TopTy, Prf p, Prf q) => kEqElemL (pol) sig ctx c p q PropTy
          (TopTy, _, _) => kerr "kernel: Prf-congruence final at non-Prf types"
          _ => kerr "kernel: Prf-congruence final on an element equation"
      FQuotCong c => do
        ty' <- kWhnfT sig tyU
        case (ty', l1, r1) of
          (TopTy, QuotTy d0 r0, QuotTy d1 r1) =>
            if d0 == d1
              then kEqElemL (pol) sig (ctx :< d0 :< substTy d0 Wk) c r0 r1 PropTy
              else kerr "kernel: quotient-congruence final at unequal domains"
          (TopTy, _, _) => kerr "kernel: quotient-congruence final at non-quotient types"
          _ => kerr "kernel: quotient-congruence final on an element equation"
      FPiCong dc cc => do
        ty' <- kWhnfT sig tyU
        case (ty', l1, r1) of
          (TopTy, Elem.PiTy d0 c0, Elem.PiTy d1 c1) => do
            kEqElemL (pol) sig ctx dc d0 d1 TopTy
            kEqElemL (pol) sig (ctx :< d1) cc c0 c1 TopTy
          (TopTy, _, _) => kerr "kernel: Π-congruence final at non-Π types"
          _ => kerr "kernel: Π-congruence final on an element equation"
      FSigmaCong dc cc => do
        ty' <- kWhnfT sig tyU
        case (ty', l1, r1) of
          (TopTy, Elem.SigmaTy d0 c0, Elem.SigmaTy d1 c1) => do
            kEqElemL (pol) sig ctx dc d0 d1 TopTy
            kEqElemL (pol) sig (ctx :< d1) cc c0 c1 TopTy
          (TopTy, _, _) => kerr "kernel: Σ-congruence final at non-Σ types"
          _ => kerr "kernel: Σ-congruence final on an element equation"
      FSumCong lc rc => do
        ty' <- kWhnfT sig tyU
        case (ty', l1, r1) of
          (TopTy, Elem.SumTy l0 r0, Elem.SumTy l1' r1') => do
            kEqElemL (pol) sig ctx lc l0 l1' TopTy
            kEqElemL (pol) sig ctx rc r0 r1' TopTy
          (TopTy, _, _) => kerr "kernel: ⊎-congruence final at non-⊎ types"
          _ => kerr "kernel: ⊎-congruence final on an element equation"
   where
    annot : String -> KM a -> KM a
    annot tag (MkKM f) = MkKM $ \st => case f st of
      Left e => Left (e ++ " @" ++ tag)
      Right v => Right v

    goSteps : Ty -> List Step -> Elem -> Elem -> KM (Elem, Elem)
    goSteps tyU [] l' r' = pure (l', r')
    goSteps tyU (s :: rest) l' r' =
      if s.onLhs
        then do l'' <- annot "step \{show (length rest)}" (stepElem pol sig ctx s tyU l') >>= kJoinElem pol sig
                goSteps tyU rest l'' r'
        else do r'' <- annot "step \{show (length rest)}" (stepElem pol sig ctx s tyU r') >>= kJoinElem pol sig
                goSteps tyU rest l' r''

  ||| Replay a certificate for the type equation Γ ⊢ A ≐ B (licensed,
  ||| as at kEqElem).
  export
  kEqTy : Sig -> Ctx -> ECert -> Ty -> Ty -> KM ()
  kEqTy = kEqTyL []

  kEqTyL : (inh : List String) -> Sig -> Ctx -> ECert -> Ty -> Ty -> KM ()
  kEqTyL inh sig ctx cert a b = kEqElemL inh sig ctx cert a b TopTy
  -- (one sort, one replay channel: a type equation is an element
  -- equation at 𝕍 — the congruence finals above apply there, steps
  -- descend with expected classifier 𝕍)

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
              _ => kerr "kernel: λ checked at a non-Π type"
          SigmaIntro u v => do
            ty' <- kWhnfT sig ty
            case ty' of
              SigmaTy a b => do
                kCheckE sig ctx u a (skelChild 0 sk)
                kCheckE sig ctx v (substTy b (Ext Id u)) (skelChild 1 sk)
              _ => kerr "kernel: pair checked at a non-⨯ type"
          Star =>
            -- el-eq-i over replay: ⋆ at an equality prop, the
            -- equation certified (refl-eq payload); otherwise the
            -- squash payloads below
            case takeP pReflEq sk of
              Just (cert, _) => do
                ty' <- kWhnfT sig ty
                case ty' of
                  Prf p => do
                    p' <- kWhnfE sig p
                    case p' of
                      Elem.EqTy l r t => kEqElem sig ctx cert l r t
                      _ => kerr "kernel: refl-eq payload at a non-equality prop"
                  _ => kerr "kernel: ⋆ checked at a non-Prf type"
              Nothing =>
               -- el-nu-coind: ⋆ at an equality prop over a ν-type,
               -- by COINDUCTION — invariant, endpoint proof, and
               -- one-step closure at the relator (the admissible
               -- rule; Foundation, coinductive NOTES)
               case takeP pNuCoind sk of
                Just ((r, skR, pw, skp, qw, skq), _) => do
                  ty' <- kWhnfT sig ty
                  case ty' of
                    Prf pc => do
                      pc' <- kWhnfE sig pc
                      case pc' of
                        Elem.EqTy l rhs ety => do
                          ety' <- kWhnfT sig ety
                          case ety' of
                            NuTy f => do
                              let nuT = NuTy f
                              -- the invariant is an Ω-relation
                              kCheckE sig (ctx :< nuT :< substTy nuT Wk) r PropTy skR
                              -- it holds at the endpoints
                              kCheckE sig ctx pw (Prf (substElem r (Ext (Ext Id l) rhs))) skp
                              -- one-step closure under the generic hypotheses
                              let ctx3 = ctx :< nuT :< substTy nuT Wk :< Prf r
                              let wk3 = Chain Wk (Chain Wk Wk)
                              let f3 = substPoly f wk3
                              let r3 = substElem r (under (under wk3))
                              kCheckE sig ctx3 qw
                                (Prf (liftPoly f3 r3 (Out (CtxVar 2)) (Out (CtxVar 1)))) skq
                            _ => kerr "kernel: coinduction payload at an equation over a non-ν type"
                        _ => kerr "kernel: coinduction payload at a non-equality prop"
                    _ => kerr "kernel: ⋆ checked at a non-Prf type"
                Nothing =>
                -- el-squash-i: ⋆ : Prf ∥A∥ carries its witness (an
                -- inhabitant of the squashee) as a payload
                 case takeP pSquashWit sk of
                  Just ((wit, witSk), _) => do
                    ty' <- kWhnfT sig ty
                    case ty' of
                      Prf p => do
                        p' <- kWhnfE sig p
                        case p' of
                          Squash sq => kCheckE sig ctx wit sq witSk
                          _ => kerr "kernel: ⋆ checked at Prf of a non-∥∥ code"
                      _ => kerr "kernel: ⋆ checked at a non-Prf type"
                  -- el-squash-e-prf: squash-elim carries its scrutinee
                  -- (inhabiting Prf ∥A∥) and a body proving (Prf q)[↑]
                  -- under the raw squashee A
                  Nothing => case takeP pSquashElim sk of
                    Just ((scrut, scrutSk, body, bodySk), _) => do
                      scrutTy <- kInferE sig ctx scrut scrutSk
                      scrutTy' <- kWhnfT sig scrutTy
                      case scrutTy' of
                        Prf p => do
                          p' <- kWhnfE sig p
                          case p' of
                            Squash a => do
                              ty' <- kWhnfT sig ty
                              case ty' of
                                Prf _ => kCheckE sig (ctx :< a) body (substTy ty Wk) bodySk
                                _ => kerr "kernel: squash-elim checked at a non-Prf goal"
                            _ => kerr "kernel: squash-elim scrutinee at Prf of a non-∥∥ code"
                        _ => kerr "kernel: squash-elim scrutinee has non-Prf type"
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
              _ => kerr "kernel: class checked at a non-quotient type"
          -- el-nu-i: the carried 𝔽 must be nf-identical to the
          -- expected ν-type's; carrier at 𝕌, coalgebra body over the
          -- carrier at the reflected observation type, seed at the
          -- carrier
          Corec p aC f x => do
            ty' <- kWhnfT sig ty
            case ty' of
              NuTy pT => do
                p' <- kPoly sig p
                pT' <- kPoly sig pT
                if p' == pT' then pure ()
                  else kerr "kernel: corec carries a different polynomial than its ν-type"
                kCheckE sig ctx aC UniverseTy (skelChild 0 sk)
                kCheckE sig (ctx :< El aC) f (substTy (El (reflectPoly p aC)) Wk) (skelChild 1 sk)
                kCheckE sig ctx x (El aC) (skelChild 2 sk)
              _ => kerr "kernel: corec checked at a non-ν type"
          ZeroElim t => kCheckE sig ctx t ZeroTy (skelChild 0 sk)
          -- el-let (spec §8): definiens INFERRED (an intro-form
          -- definiens carries intro-ty on child 0), body under the
          -- value and its unfolding equation, checked at T[↑ ∘ ↑] —
          -- fully general, since T lives over Γ and the hypothesis
          -- makes (id, a, ⋆) ∘ (↑ ∘ ↑) ≐ id
          Let a b => do
            aTy <- kInferE sig ctx a (skelChild 0 sk)
            let hyp = Prf (Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk))
            kCheckE sig (ctx :< aTy :< hyp) b (weakenTyN 2 ty) (skelChild 1 sk)
          QCtor sgC c theta => do
            -- el-qiit-intro, SATURATED. The signature is nf(T)'s own —
            -- already validated where T was — and the term's must be
            -- nf-identical to it. FULL normalization here: the carried
            -- signature is compared structurally, so weak-head is not
            -- enough.
            ty' <- kTy sig ty
            case ty' of
              QSort sgT srt es => do
                sgC' <- kQSig sig sgC
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
                idxN <- kSubNorm sig idx
                esN <- kSubNorm sig es
                if idxN == esN
                  then pure ()
                  else kerr "kernel: constructor indices do not match the type"
              _ => kerr "kernel: constructor checked at a non-QIIT type"
          _ => do
            inferred <- kInferE sig ctx e sk
            i' <- kTy sig inferred
            t' <- kTy sig ty
            if i' == t' then pure () else kerr "kernel: type mismatch without a switch certificate\n  inferred: \{show i'}\n  expected: \{show t'}"

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
              Nothing => kerr "kernel: unknown signature name"
          OneIntro => pure OneTy
          NatIntro0 => pure NatTy
          NatIntro1 t => do kCheckE sig ctx t NatTy (skelChild 0 sk); pure NatTy
          PiApp f a => do
            fTy <- kInferE sig ctx f (skelChild 0 sk) >>= kWhnfT sig
            case fTy of
              PiTy dom cod => do
                kCheckE sig ctx a dom (skelChild 1 sk)
                pure (substTy cod (Ext Id a))
              _ => kerr "kernel: applying a non-function"
          SigmaElim1 t => do
            tTy <- kInferE sig ctx t (skelChild 0 sk) >>= kWhnfT sig
            case tTy of
              SigmaTy a _ => pure a
              _ => kerr "kernel: projecting a non-pair"
          SigmaElim2 t => do
            tTy <- kInferE sig ctx t (skelChild 0 sk) >>= kWhnfT sig
            case tTy of
              SigmaTy _ b => pure (substTy b (Ext Id (SigmaElim1 t)))
              _ => kerr "kernel: projecting a non-pair"
          -- el-nu-e: fully inference-driven, no motive payload
          Out t => do
            tTy <- kInferE sig ctx t (skelChild 0 sk) >>= kWhnfT sig
            case tTy of
              NuTy f => pure (El (reflectPoly f (Elem.NuTy f)))
              _ => kerr "kernel: observing a non-ν element"
          -- el-let (spec §8): let infers when its body does; the
          -- result substitutes the value and the ⋆-proof away
          Let a b => do
            aTy <- kInferE sig ctx a (skelChild 0 sk)
            let hyp = Prf (Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk))
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
                tTy <- kInferE sig ctx t (skelChild 2 sk) >>= kWhnfT sig
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
                qTy <- kInferE sig ctx q (skelChild 1 sk) >>= kWhnfT sig
                case qTy of
                  QuotTy a r => do
                    kCheckTyK sig (ctx :< QuotTy a r) mot motSk
                    kCheckE sig (ctx :< a) f
                      (substTy mot (Ext Wk (Class (CtxVar 0)))) (skelChild 0 sk)
                    let wk3 = Chain Wk (Chain Wk Wk)
                    kEqElem sig (ctx :< a :< substTy a Wk :< Prf r) wd
                      (substElem f (Ext wk3 (CtxVar 2)))
                      (substElem f (Ext wk3 (CtxVar 1)))
                      (substTy mot (Ext wk3 (Class (CtxVar 2))))
                    pure (substTy mot (Ext Id q))
                  _ => kerr "kernel: quot-elim of a non-quotient"
              _ => kerr "kernel: quot-elim without motive/well-definedness annotations"
          QSort sg k es => do
            -- code-qiit: SMALL signatures only
            kQSigCheck sig ctx sg
            if qSigSmall sg
              then pure ()
              else kerr "kernel: universe code for a LARGE signature (code-qiit requires smallness)"
            kQSortSpine sig ctx sg k es sk
            pure UniverseTy
          QElim sg k mots mths es w =>
            -- el-qiit-elim over mot/dalg/eprob; ℰ is carried by the
            -- term, the coherences arrive as certificates (PQCoh)
            case takeP pQCoh sk of
              Nothing => kerr "kernel: QIIT eliminator without coherence certificates"
              Just (cohs, sk') => do
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
                let goMotives : List Nat -> List Ty -> KM ()
                    goMotives [] [] = pure ()
                    goMotives (sj :: sjs) (mot :: rest) = do
                      sjE <- case qEntry sg sj of
                               Just x => pure x
                               Nothing => kerr "kernel: sort out of range"
                      (tel, wEnd, _) <- liftQ (reflTel sg (qwAt sj) sjE)
                      let mctx = foldl (:<) ctx tel
                      let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
                      kCheckTyK sig (mctx :< selfTy) mot (Nd [] [])
                      goMotives sjs rest
                    goMotives _ _ = kerr "kernel: motive count mismatch"
                let goMethods : List Nat -> List Elem -> KM ()
                    goMethods [] [] = pure ()
                    goMethods (cj :: cjs) (m :: rest) = do
                      mty <- liftQ (methodTy sg mots cj)
                      kCheckE sig ctx m mty (Nd [] [])
                      goMethods cjs rest
                    goMethods _ _ = kerr "kernel: method count mismatch"
                let goCoherences : List Nat -> List ECert -> KM ()
                    goCoherences [] [] = pure ()
                    goCoherences (ej :: ejs) (coh :: rest) = do
                      (dtel, _, lhs, rhs, cty) <- liftQ (coherenceAt sg mots mths ej)
                      kEqElem sig (foldl (:<) ctx dtel) coh lhs rhs cty
                      goCoherences ejs rest
                    goCoherences _ _ = kerr "kernel: coherence count mismatch"
                goMotives sortPs mots
                goMethods pointPs mths
                goCoherences eqPs cohs
                kQSortSpine sig ctx sg k es sk'
                kCheckE sig ctx w (QSort sg k es) (skelChild (length (toList es)) sk')
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
            kCheckE sig (ctx :< El a) b UniverseTy (skelChild 1 sk)
            pure UniverseTy
          Elem.SigmaTy a b => do
            kCheckE sig ctx a UniverseTy (skelChild 0 sk)
            kCheckE sig (ctx :< El a) b UniverseTy (skelChild 1 sk)
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
            kCheckE sig (ctx :< El a :< substTy (El a) Wk) r PropTy (skelChild 1 sk)
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
    kCheckPolyK sig (ctx :< El a) f (S i) sk
  kCheckPolyK sig ctx (PPi a f)    i sk = do
    kCheckE sig ctx a UniverseTy (skelChild i sk)
    kCheckPolyK sig (ctx :< El a) f (S i) sk

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
  kCheckTyK sig ctx (El e) sk = kCheckE sig ctx e UniverseTy (skelChild 0 sk)
  kCheckTyK sig ctx PropTy _ = pure ()
  kCheckTyK sig ctx (Prf p) sk = kCheckE sig ctx p PropTy (skelChild 0 sk)
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
      _ => kerr "kernel: bad signature type reference"
   where
    childSkels' : Skel -> List Skel
    childSkels' (Nd _ cs) = cs
  -- one sort: element formers, and 𝕍 itself (no Γ ⊦ 𝕍 : 𝕍), are not
  -- type formers
  kCheckTyK sig ctx t _ = kerr "kernel: not a type former in type position"

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

||| Infer the type of a BARE (skeleton-free) core — recovery's
||| capture-typing source. Nothing when the core is an intro form
||| (not inferable) or fails to type against this Σ; the caller
||| treats absence as "no derived equation", never as an error.
export
kInferBare : Sig -> Nat -> Ctx -> Elem -> Maybe Ty
kInferBare sig fuel ctx e =
  case runKM (kInferE sig ctx e (Nd [] [])) fuel of
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
kCheckEqElem : Sig -> Ctx -> Nat -> ECert -> Elem -> Elem -> Ty -> Either KErr ()
kCheckEqElem sig ctx fuel cert l r ty =
  map fst (runKM (kEqElem sig ctx cert l r ty) fuel)

export
kCheckEqTy : Sig -> Ctx -> Nat -> ECert -> Ty -> Ty -> Either KErr ()
kCheckEqTy sig ctx fuel cert a b =
  map fst (runKM (kEqTy sig ctx cert a b) fuel)
