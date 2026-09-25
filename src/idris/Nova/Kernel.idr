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
  ||| name → entry, built lazily during THIS check: Σ is fixed for the
  ||| lifetime of one runKM call, so a positive hit is stable, and the
  ||| linear sigLookup scan — measured at ~40% of all execution on the
  ||| hot paths — is paid once per name instead of once per mention.
  sigIx : SortedMap String SigEntry

export
data KM : Type -> Type where
  MkKM : (KSt -> Either KErr (a, KSt)) -> KM a

runKMSt : KM a -> KSt -> Either KErr (a, KSt)
runKMSt (MkKM f) = f

export
runKM : KM a -> Nat -> Either KErr (a, Nat)
runKM m n = map (mapSnd fuel) (runKMSt m (MkKSt n empty))


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

-- ===== The β join: the kernel's ONE normalizer =====
--
-- Fuel-bounded normalization (docs/NovaKernel.txt §1): α + every
-- computation rule (β, ι, let, ν-β, QIIT-β, code-squash-idem's
-- instances) and NO δ. A definition reference is STUCK, like a
-- declaration's: a definition unfolds only through a δ leaf or a
-- δ-all leaf of a derivation (the kernel never unfolds on its own
-- initiative, so the producer never has to predict a strategy and
-- its every δ is recorded). The weak-head form kWhnf* serves the
-- readings' shape tests and is β-only likewise.

mutual
  ||| Weak-head normalization (β-only): contract only at the head, one
  ||| fuel per contraction, subterms stay as written. Stuck or unknown
  ||| heads return unchanged.
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
  -- hides is exposed by a recorded conversion (an ascription or a
  -- conversion node, an ascribed leaf inside a proof), never by the
  -- kernel's own unfolding
  kWhnfE sig (SigVar x es) = pure (SigVar x es)
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
  go (QElim sg k fs es w) = [| QElim (traverseQSig go sg) (pure k) (traverse go fs) (traverseSN go es) (go w) |]
  go (Out u) = Out <$> go u
  go (Corec p a f x) = [| Corec (pure p) (go a) (go f) (go x) |]
  go u = pure u

weakenTyN : Nat -> Ty -> Ty
weakenTyN Z t = t
weakenTyN (S n) t = weakenTyN n (substTy t Wk)

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
-- ===== Shared readers: β-join comparison, type agreement, prop-ness, polynomials, signatures =====

||| Wk composed n times (the weakening Γ·(n entries) ⇒ Γ).
wkSubN : Nat -> Sub
wkSubN Z = Id
wkSubN (S n) = Chain (wkSubN n) Wk

||| Entry i of a reference's context, instantiated by the earlier
||| spine entries (Nothing: not a term entry, or out of range).
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

mutual
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
  tyAgree sig exp got = if exp == got then pure True else do
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

  ||| Is the type a PROPOSITION (a member of Ω)? By its SHAPE: the Ω
  ||| formers are, the other formers are not, and a neutral is one
  ||| exactly when its head's declared type inverts to Ω (inferHead,
  ||| β-only). Nothing else: an eliminator standing as a prop derives
  ||| its motive from the derivation that carries it, never from a
  ||| guess of the kernel's.
  kIsProp : Sig -> Ctx -> Ty -> KM Bool
  kIsProp sig ctx t = do
    t' <- kWhnfT sig t
    case t' of
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
      QSort _ _ _ => pure False
      _ => do
        mt <- inferHead sig ctx t'
        case mt of
          Just k => do
            k' <- kWhnfT sig k
            pure (k' == PropTy)
          Nothing => pure False

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


||| A carried signature's erasure (every piece an element derivation).
qsigE : DQSig -> KM QSig
qsigE dsg = maybe (kerr "kernel: a carried signature's piece derives no element") pure (eraseQSig dsg)

||| A carried polynomial's erasure.
polyE : DPoly -> KM Poly
polyE dp = maybe (kerr "kernel: a carried polynomial's piece derives no element") pure (erasePoly dp)

||| The application chain of a carried ToS term (qChain on derivations).
dqChain : DQTm -> Maybe (Nat, List (Either Drv DQTm))
dqChain t0 = go t0 []
 where
  go : DQTm -> List (Either Drv DQTm) -> Maybe (Nat, List (Either Drv DQTm))
  go (DQVar i) acc = Just (i, acc)
  go (DQAppE f e) acc = go f (Left e :: acc)
  go (DQAppI f a) acc = go f (Right a :: acc)
  go (DQEqC _ _ _) _ = Nothing

||| A ToS chain rebuilt from its erased pieces.
qApp : Nat -> List (Either Elem QTm) -> QTm
qApp h = foldl (\f, a => case a of
                          Left e => QAppE f e
                          Right t => QAppI f t) (QVar h)

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

||| A stating derivation whose RIGHT side is never a syntactic part
||| of a side: a δ leaf unfolds to a definition's body, an intro
||| form that β-reduces against the node above (an unfolded λ under
||| an application) — it runs left to right only under a node.
oneWay : Drv -> Bool
oneWay (DDelta _ _) = True
oneWay (DSubst q _) = oneWay q
oneWay (DConv q _ _) = oneWay q
oneWay (DAscribe q _ _) = oneWay q
oneWay (DAt q _ _) = oneWay q
oneWay _ = False

mutual
 ||| A derivation that STATES its equation and type (the ⇒ reading is
 ||| defined on it): a child the node's rule CHECKS (an argument at the
 ||| head's domain, a branch at the motive's instance, a spine entry
 ||| at its telescope type) need only be checkable there.
 export
 dSynth : Drv -> Bool
 dSynth (DVar _) = True
 dSynth (DRef _ ps) = all dCheckable ps
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
 dSynth (DTrans p q) = (dSynth p && dirable True q) || (dSynth q && dirable False p)
 dSynth (DTransAt p _ q) = (dSynth p && dirable True q) || (dSynth q && dirable False p)
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
 dSynth (DAscribe p (Just _) _) = dCheckable p
 dSynth (DAscribe p Nothing _) = False
 dSynth (DSubst p _) = dSynth p
 dSynth (DLam (Just _) p) = dSynth p
 dSynth (DLam Nothing _) = False
 dSynth (DPair (Just _) u v) = dSynth u && dCheckable v
 dSynth (DPair Nothing _ _) = False
 dSynth (DInj1 (Just _) p) = dSynth p
 dSynth (DInj1 Nothing _) = False
 dSynth (DInj2 (Just _) p) = dSynth p
 dSynth (DInj2 Nothing _) = False
 dSynth (DClass (Just _) p) = dSynth p
 dSynth (DClass Nothing _) = False
 dSynth (DSuc p) = dCheckable p
 dSynth (DCtor _ _ ps) = False
 dSynth (DCorec _ a f x) = dCheckable a && dCheckable f && dCheckable x
 dSynth (DLet a b) = dSynth a && dSynth b
 dSynth (DStar (Just _) _) = True
 dSynth (DStar Nothing _) = False
 dSynth (DSq p) = dSynth p
 dSynth (DSquashElim (Just _) e b) = dSynth e && dSynth b
 dSynth (DSquashElim Nothing _ _) = False
 dSynth (DCoind (Just _) _ _ _) = True
 dSynth (DCoind Nothing _ _ _) = False
 dSynth (DZeroElim (Just _) p) = dCheckable p
 dSynth (DZeroElim Nothing _) = False
 dSynth (DNatElim (Just _) z s n) = dCheckable z && dCheckable s && dCheckable n
 dSynth (DNatElim Nothing _ _ _) = False
 dSynth (DSumElim (Just _) l r t) = dCheckable l && dCheckable r && dSynth t
 dSynth (DSumElim Nothing _ _ _) = False
 dSynth (DQuotElim (Just _) _ f q) = dCheckable f && dSynth q
 dSynth (DQuotElim Nothing _ _ _) = False
 dSynth (DQElim _ _ (Just _) _ ms es w) = all dCheckable ms && all dCheckable es && dCheckable w
 dSynth (DQElim _ _ Nothing _ _ _ _) = False
 dSynth (DOut p) = dSynth p
 dSynth (DApp f a) = dSynth f && dCheckable a
 dSynth (DProj1 p) = dSynth p
 dSynth (DProj2 p) = dSynth p
 dSynth (DPi a b) = dSynth a && dSynth b
 dSynth (DSigma a b) = dSynth a && dSynth b
 dSynth (DSum a b) = dSynth a && dSynth b
 dSynth (DEq l r t) = dCheckable l && dCheckable r && dSynth t
 dSynth (DQuot a r) = dSynth a && dCheckable r
 dSynth (DSquash p) = dSynth p
 dSynth (DNu _) = True
 dSynth (DSort _ _ ps) = all dCheckable ps

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
   DRef _ qs => all dCheckable qs
   DSort _ _ qs => all dCheckable qs
   DStar Nothing _ => True
   DSq q => dCheckable q
   DSquashElim Nothing e b => dSynth e && dCheckable b
   DCoind Nothing r q1 q2 => dCheckable r && dCheckable q1 && dCheckable q2
   DZeroElim Nothing q => dCheckable q
   DNatElim Nothing z st n => dCheckable z && dCheckable st && dCheckable n
   DSumElim Nothing l r t => dCheckable l && dCheckable r && dSynth t
   DQuotElim Nothing _ f q => dCheckable f && dSynth q
   DQElim _ _ Nothing _ ms es w => all dCheckable ms && all dCheckable es && dCheckable w
   DConv q Nothing _ => dSynth q
   DAscribe q _ _ => dCheckable q
   DLet a b => dSynth a && dCheckable b
   DPi a b => dCheckable a && dCheckable b
   DSigma a b => dCheckable a && dCheckable b
   DSum a b => dCheckable a && dCheckable b
   DQuot a r => dCheckable a && dCheckable r
   DSquash q => dCheckable q
   DSym q => dCheckable q
   DTrans q r => (dCheckable q && dirable True r) || (dCheckable r && dirable False q)
   DTransAt q _ r => (dCheckable q && dirable True r) || (dCheckable r && dirable False q)
   _ => False

 ||| Can the derivation run DIRECTIONALLY (→) from the side d names
 ||| (True: the left side is given)? A stating derivation can (it
 ||| compares the given side and produces the other); refl and the
 ||| forward-only δ-all can; structure and nodes can when their parts
 ||| can.
 dDirable : Bool -> Drv -> Bool
 dDirable = dDirableW (\_, _ => True)

 ||| … with a test on the stating leaves (the reader's `runnable`
 ||| excludes the one-way ones from the wrong direction).
 dDirableW : (Bool -> Drv -> Bool) -> Bool -> Drv -> Bool
 dDirableW ok d p = if dSynth p then ok d p else case p of
   DReflx => True
   DDeltaAll _ => d
   DSym q => go (not d) q
   DTrans q r => go d q && go d r
   DTransAt q _ r => go d q && go d r
   DConv q _ _ => go d q
   DAscribe q _ _ => go d q
   DLam _ q => go d q
   DPair _ u v => go d u && go d v
   DInj1 _ q => go d q
   DInj2 _ q => go d q
   DClass _ q => go d q
   DSuc q => go d q
   DCtor _ _ qs => all (go d) qs
   DCorec _ a f x => go d a && go d f && go d x
   DZeroElim _ q => go d q
   DNatElim _ z s n => go d z && go d s && go d n
   DSumElim _ l r t => go d l && go d r && go d t
   DQuotElim _ _ f q => go d f && go d q
   DQElim _ _ _ _ ms es w => all (go d) ms && all (go d) es && go d w
   DOut q => go d q
   DApp f a => go d f && go d a
   DProj1 q => go d q
   DProj2 q => go d q
   DPi a b => go d a && go d b
   DSigma a b => go d a && go d b
   DSum a b => go d a && go d b
   DEq l r t => go d l && go d r && go d t
   DQuot a r => go d a && go d r
   DSquash q => go d q
   DSort _ _ qs => all (go d) qs
   DRef _ qs => all (go d) qs
   _ => False
  where
   go : Bool -> Drv -> Bool
   go = dDirableW ok

 ||| Directional by shape alone, one-way leaves excluded from the
 ||| wrong direction (a δ leaf's right side is a definition's body, an
 ||| intro form that β-reduces against the node above: it runs left to
 ||| right only) — what a chain's far link must be for the chain to
 ||| state through its near one.
 dirable : Bool -> Drv -> Bool
 dirable = dDirableW (\d, q => not (oneWay q) || d)


||| Δ without its d newest entries (the substitution node's Δ↓d).
dropCtx : Nat -> Ctx -> Maybe Ctx
dropCtx Z ctx = Just ctx
dropCtx (S n) (ctx :< _) = dropCtx n ctx
dropCtx (S _) [<] = Nothing

||| A goal for the readings that decompose: the side the derivation
||| runs FROM, its direction (True: that side is the left one), and
||| the other side when known — a HINT, consumed only by what cannot
||| read from one end alone (a chain whose link runs the other way, a
||| δ-all from the right, a type-directed leaf) and passed down to
||| children at its parts. The reading returns the produced other
||| side; the caller compares it with the hint under β.
data DGoal : Type where
  DGRun : Bool -> Elem -> Maybe Elem -> DGoal

mutual
  ||| Γ ⊦ 𝔽 poly, read off the carried polynomial's derivations
  ||| (Foundation's poly-* rules): each embedded code at 𝕌, the
  ||| context growing by the binders' domain codes; the erasure out.
  export
  dPoly : Sig -> Ctx -> DPoly -> KM Poly
  dPoly sig ctx DPHole = pure PHole
  dPoly sig ctx (DPConst da) = PConst <$> dElemAt sig ctx da UniverseTy
  dPoly sig ctx (DPProd f g) = [| PProd (dPoly sig ctx f) (dPoly sig ctx g) |]
  dPoly sig ctx (DPSum f g) = [| PSum (dPoly sig ctx f) (dPoly sig ctx g) |]
  dPoly sig ctx (DPSigma da f) = do
    a <- dElemAt sig ctx da UniverseTy
    PSigma a <$> dPoly sig (ctx :< a) f
  dPoly sig ctx (DPPi da f) = do
    a <- dElemAt sig ctx da UniverseTy
    PPi a <$> dPoly sig (ctx :< a) f

  ||| Γ ⊦ 𝒮 qsig, read off the carried signature's derivations —
  ||| Foundation's qctx/qty/qtm as a syntax-directed algorithm over
  ||| the fragment the elaborator emits (A6): the ToS structure walked
  ||| on the erasure, every embedded Nova piece READ where it stands
  ||| (an external domain as a type, an external argument at its
  ||| instantiated domain). Returns the erasure and SMALLNESS: every
  ||| external domain classifies at 𝕌 or Ω (code-qiit's side
  ||| condition), decided by the domain's own classifier — never tried.
  export
  dQSig : Sig -> Ctx -> DQSig -> KM (QSig, Bool)
  dQSig sig ctx dsg = do
    sg <- qsigE dsg
    smalls <- goEntries sg 0 dsg
    pure (sg, all id smalls)
   where
    goEntries : QSig -> Nat -> List DQTy -> KM (List Bool)
    goEntries sg k [] = pure []
    goEntries sg k (e :: rest) = do
      b <- dqEntry sig ctx sg k e
      bs <- goEntries sg (S k) rest
      pure (b :: bs)

  ||| One signature entry (position k): its external domains read as
  ||| types (their classifiers decide smallness), its codes checked.
  dqEntry : Sig -> Ctx -> QSig -> (k : Nat) -> DQTy -> KM Bool
  dqEntry sig ctx sg k entry = walk ctx 0 0 [] entry
   where
    walk : Ctx -> (extD : Nat) -> (b : Nat) -> List QTm -> DQTy -> KM Bool
    walk ectx extD b benv (DQPiExt aD rest) = do
      (a, kcls) <- dTypeK sig ectx aD
      k' <- kWhnfT sig kcls
      let small = case k' of
                    PropTy => True
                    UniverseTy => True
                    _ => False
      restSmall <- walk (ectx :< a) (S extD) b (map (\c => substQTm c Wk) benv) rest
      pure (small && restSmall)
    walk ectx extD b benv (DQPiInd u rest) = do
      uE <- dqCode sig ctx sg k ectx extD b benv u
      walk ectx extD (S b) (qtmShift 1 uE :: map (qtmShift 1) benv) rest
    walk ectx extD b benv DQU = pure True
    walk ectx extD b benv (DQEl (DQEqC l r u)) = do
      uE <- dqCode sig ctx sg k ectx extD b benv u
      _ <- dqTmAt sig ctx sg k ectx extD b benv uE l
      _ <- dqTmAt sig ctx sg k ectx extD b benv uE r
      pure True
    walk ectx extD b benv (DQEl code) = do
      _ <- dqCode sig ctx sg k ectx extD b benv code
      pure True

  ||| A sort-headed CODE at (scope k, external zone ectx with extD
  ||| external binders, b inductive binders with domain codes benv):
  ||| the sort's binder telescope walked against the arguments —
  ||| external ones READ at their instantiated domains, inductive ones
  ||| (inductive-inductive sort indices) at their rebased domain codes.
  ||| The erased code out.
  dqCode : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> List QTm -> DQTm -> KM QTm
  dqCode sig ctx sg k ectx extD b benv (DQEqC _ _ _) =
    kerr "kernel: equation code in a binder position (first-order fragment)"
  dqCode sig ctx sg k ectx extD b benv code =
    case dqChain code of
      Nothing => kerr "kernel: qiit code is not an application chain"
      Just (h, args) => do
        pos <- kQEntryOf k b h
        sortE <- case qEntry sg pos of
                   Just e => pure e
                   Nothing => kerr "kernel: qiit entry out of range"
        case qEntryKind sortE of
          QKSort => pure ()
          _ => kerr "kernel: qiit code head is not a sort"
        (hd, argsE) <- dqArgsWalk sig ctx sg k ectx extD b benv pos sortE args
        case hd of
          QU => pure (qApp h argsE)
          _ => kerr "kernel: internal — sort entry with a non-U head"

  ||| Entry `src`'s binder telescope walked against an argument chain
  ||| (as kQArgsWalk), the external arguments READ; the entry's head
  ||| rebased to the current coordinates and the erased arguments out.
  dqArgsWalk : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> (benv : List QTm)
            -> (src : Nat) -> QTy -> List (Either Drv DQTm) -> KM (QTy, List (Either Elem QTm))
  dqArgsWalk sig ctx sg k ectx extD b benv src entry args0 =
    goArgs 0 (wkSubN extD) [] entry args0
   where
    goArgs : (srcB : Nat) -> Sub -> List QTm -> QTy -> List (Either Drv DQTm) -> KM (QTy, List (Either Elem QTm))
    goArgs srcB sub ivals (QPiExt a rest) (Left pe :: as) = do
      e <- dElemAt sig ectx pe (substTy a sub)
      (hd, rest') <- goArgs srcB (Ext sub e) ivals rest as
      pure (hd, Left e :: rest')
    goArgs srcB sub ivals (QPiInd u rest) (Right t' :: as) = do
      expected <- kQRebase sg k b src srcB sub ivals u
      tE <- dqTmAt sig ctx sg k ectx extD b benv expected t'
      (hd, rest') <- goArgs (S srcB) sub (tE :: ivals) rest as
      pure (hd, Right tE :: rest')
    goArgs srcB sub ivals (QEl code) [] = do
      c <- kQRebase sg k b src srcB sub ivals code
      pure (QEl c, [])
    goArgs srcB sub ivals QU [] = pure (QU, [])
    goArgs _ _ _ _ _ = kerr "kernel: qiit spine mismatch (kind or saturation)"

  ||| The CODE of a qiit term (a binder, or a saturated point-
  ||| constructor chain), its arguments read along the way; with the
  ||| erased term.
  dqTmInfer : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> (benv : List QTm) -> DQTm -> KM (QTm, QTm)
  dqTmInfer sig ctx sg k ectx extD b benv t =
    case dqChain t of
      Nothing => kerr "kernel: qiit term is not an application chain (first-order fragment)"
      Just (h, args) =>
        if h < b
          then case (args, getAt h benv) of
                 ([], Just c) => pure (c, QVar h)
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
            (hd, argsE) <- dqArgsWalk sig ctx sg k ectx extD b benv pos ctorE args
            case hd of
              QEl code => pure (code, qApp h argsE)
              _ => kerr "kernel: internal — point entry with a non-El head"

  ||| A qiit term against an expected code (both at the current
  ||| coordinates); comparison is syntactic after β-JOINING the
  ||| embedded Nova pieces (no δ). The erased term out.
  dqTmAt : Sig -> Ctx -> QSig -> (k : Nat) -> Ctx -> (extD, b : Nat) -> List QTm -> QTm -> DQTm -> KM QTm
  dqTmAt sig ctx sg k ectx extD b benv expected t = do
    (inferred, tE) <- dqTmInfer sig ctx sg k ectx extD b benv t
    i' <- kJoinQTm sig inferred
    e' <- kJoinQTm sig expected
    if i' == e' then pure tE
      else kerr "kernel: qiit term at the wrong sort"

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
    DPath dsg k ps => do
      sg <- qsigE dsg
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
          mJ <- middleAt sig ctx m t
          sameB sig b mJ
          c <- dDir sig ctx q True mJ t
          pure (a, c, t)
        else if dSynth q && dDirable False p
        then do
          (b, c, t) <- dInfer sig ctx q
          mJ <- middleAt sig ctx m t
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
    -- the annotation absent in inference position: the proof RUN from
    -- the inferred type (an eliminator's scrutinee exposed)
    DConv p Nothing beta => do
      (l, r, t) <- dInfer sig ctx p
      tJ <- kJoinElem sig t
      t' <- dDir sig ctx beta True tJ TopTy
      pure (l, r, t')
    DAt p pT beta => do
      (l, r, t) <- dInfer sig ctx p
      t' <- dType sig ctx pT
      dAt sig ctx beta t t' TopTy
      pure (l, r, t')
    -- an ASCRIPTION: the derivation checked at the type the annotation
    -- derives (the inference form of a checking derivation); the
    -- optional conversion belongs to checking positions only
    DAscribe p (Just pT) Nothing => do
      t' <- dType sig ctx pT
      (l, r) <- dCheck sig ctx p t'
      pure (l, r, t')
    DAscribe p _ (Just _) => kerr "kernel: an ascription's conversion has no position type to convert in inference position"
    DAscribe p Nothing Nothing => kerr "kernel: an ascription without its type in inference position"
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
    DCorec df a g x => do
      f <- polyE df
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
      q <- dPropAt sig ctx pQ
      squashElimAtP sig ctx q e b
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
          motK <- dTypeK sig (ctx :< QuotTy a rel) pM
          quotElimAt sig ctx (map Just motK) a rel wd f (ql, qr, qTy)
        _ => kerr "kernel: quot-elim of a non-quotient"
    DQElim dsg k (Just cs) cohs ms es w => do
      (sg, _) <- dQSig sig ctx dsg
      qElimAt sig ctx sg k cs cohs ms es w
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
    DNu df => do
      f <- dPoly sig ctx df
      pure (NuTy f, NuTy f, UniverseTy)
    DSort dsg k ps => do
      (sg, small) <- dQSig sig ctx dsg
      sortE <- case qEntry sg k of
                 Just e => pure e
                 Nothing => kerr "kernel: sort position out of range"
      case qEntryKind sortE of
        QKSort => pure ()
        _ => kerr "kernel: not a sort position"
      (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
      esE <- dTeleE sig ctx tel ps
      pure (QSort sg k (cast (map fst esE)), QSort sg k (cast (map snd esE)), if small then UniverseTy else TopTy)
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
    DAscribe p mT mb => do
      -- the type flowing down converted (or agreeing) to what the
      -- annotation derives, and p checked at the result: exposure. No
      -- annotation: the target is what the proof PRODUCES run from
      -- the type flowing down (β → T ≐ T′)
      t' <- case (mT, mb) of
        (Just pT, Just b) => do t' <- dType sig ctx pT; dAt sig ctx b ty t' TopTy; pure t'
        (Just pT, Nothing) => do t' <- dType sig ctx pT; agree t'; pure t'
        (Nothing, Just b) => do tyJ <- kJoinElem sig ty; dDir sig ctx b True tyJ TopTy
        (Nothing, Nothing) => pure ty
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
    DCtor dsgC c ps => do
      -- el-qiit-intro, as §8: the type's carrier and the term's join
      -- alike (the term's read where the type's was: a node carries
      -- what nf(T) carries); the spine at the reflected telescope;
      -- the head's sort and indices meet the type's
      sgC <- qsigE dsgC
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
          argsE <- dTeleE sig ctx tel ps
          let args = map fst argsE
          (wEnd, hd) <- liftQ (walkVals sgC' (qwAt c) entry args)
          (srt', idx) <- liftQ (pointHead sgC' wEnd hd)
          if srt' /= srt then kerr "kernel: constructor of a different sort" else pure ()
          idxN <- kJoinSubNorm sig idx
          esN <- kJoinSubNorm sig es
          if idxN == esN then pure () else kerr "kernel: constructor indices do not match the type"
          pure (QCtor sgC c (cast args), QCtor sgC c (cast (map snd argsE)))
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
        _ => kerr "kernel: sq(π) at a non-∥∥ type [\{show ty'}]"
    DSquashElim mQ e b => do
      -- the goal a prop: by its derivation when carried (the annotated
      -- form in checking position: agreeing with the type flowing
      -- down), else by the kernel's prop-ness test on the type
      case mQ of
        Just pQ => do
          q <- dPropAt sig ctx pQ
          agree q
          squashElimAtP sig ctx q e b
        Nothing => squashElimAt sig ctx ty e b
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
          (l', r', t') <- quotElimAt sig ctx (substTy ty Wk, Nothing) a rel wd f (ql, qr, qTy)
          agree t'
          pure (l', r')
        _ => kerr "kernel: quot-elim of a non-quotient"
    -- the QIIT eliminator without motives: the constant motives at the
    -- type flowing down
    DQElim dsg k Nothing cohs qm qs qw => do
      (sg, _) <- dQSig sig ctx dsg
      mots <- constMotives sig ctx sg ty
      (l, r, t) <- qElimAtM sig ctx sg k mots cohs qm qs qw
      agree t
      pure (l, r)
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
      mJ <- middleAt sig ctx m ty
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
      -- check, §7); a SPINE node over a proper equation — an
      -- application, a projection, an observation, a reference — is
      -- not compared: its head is a variable or a reference, whose
      -- typings all factor through one declared type (inversion), so
      -- the equation's type and the position's are the same up to
      -- conversion (a dependent codomain moves with the argument).
      -- An ELIMINATOR node is compared: its type is the motive's
      -- instance, and the same term types at other motives
      if l == r || posChecked d then agree t else pure ()
      pure (l, r)
   where
    posChecked : Drv -> Bool
    posChecked (DApp _ _) = False
    posChecked (DProj1 _) = False
    posChecked (DProj2 _) = False
    posChecked (DOut _) = False
    posChecked (DRef _ _) = False
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
  dAt sig ctx d l0 r0 ty = do
    -- the sides β-joined first (the reader meets no redex: a type
    -- flowing down, an inferred type, a stated middle may carry one)
    l <- kJoinElem sig l0
    r <- kJoinElem sig r0
    dAtJ sig ctx d l r ty

  dAtJ : Sig -> Ctx -> Drv -> Elem -> Elem -> Ty -> KM ()
  dAtJ sig ctx d l r ty = do
    x <- dRun sig ctx d (DGRun True l (Just r)) ty
    sameB sig x r

  ||| Structure is read through even when it states: transitivity and
  ||| symmetry link by link, an ascription or conversion wrapper at the
  ||| type it converts to.
  structuralD : Drv -> Bool
  structuralD (DTrans _ _) = True
  structuralD (DTransAt _ _ _) = True
  structuralD (DSym _) = True
  structuralD (DAscribe _ _ _) = True
  structuralD (DConv _ Nothing _) = True
  structuralD _ = False

  ||| The children of a node paired with the parts of a side the node
  ||| decomposes it into (Nothing: the side lacks the node's shape).
  ||| The same alignment as the decomposing reading's `node`.
  nodeParts : Drv -> Elem -> Maybe (List (Drv, Elem))
  nodeParts d x = case (d, x) of
    (DApp f a, PiApp f' a') => Just [(f, f'), (a, a')]
    (DProj1 q, SigmaElim1 u) => Just [(q, u)]
    (DProj2 q, SigmaElim2 u) => Just [(q, u)]
    (DOut q, Out u) => Just [(q, u)]
    (DSuc q, NatIntro1 u) => Just [(q, u)]
    (DZeroElim _ q, ZeroElim u) => Just [(q, u)]
    (DNatElim _ z s t, NatElim z' s' t') => Just [(z, z'), (s, s'), (t, t')]
    (DSumElim _ l r t, SumElim l' r' t') => Just [(l, l'), (r, r'), (t, t')]
    (DQuotElim _ _ f q, QuotElim f' q') => Just [(f, f'), (q, q')]
    (DQElim sg k _ _ ms es w, QElim sg' k' fs es' w') =>
      if eraseQSig sg == Just sg' && k == k' && length ms == length fs && length es == length (toList es')
        then Just (zip ms fs ++ zip es (toList es') ++ [(w, w')]) else Nothing
    (DLam _ q, PiIntro f) => Just [(q, f)]
    (DPair _ u v, SigmaIntro u' v') => Just [(u, u'), (v, v')]
    (DInj1 _ q, Inj1 u) => Just [(q, u)]
    (DInj2 _ q, Inj2 u) => Just [(q, u)]
    (DClass _ q, Class u) => Just [(q, u)]
    (DCorec pf a f x', Corec pf' a' f' x'') => if erasePoly pf == Just pf' then Just [(a, a'), (f, f'), (x', x'')] else Nothing
    (DLet a b, Let a' b') => Just [(a, a'), (b, b')]
    (DPi a b, Elem.PiTy a' b') => Just [(a, a'), (b, b')]
    (DSigma a b, Elem.SigmaTy a' b') => Just [(a, a'), (b, b')]
    (DSum a b, Elem.SumTy a' b') => Just [(a, a'), (b, b')]
    (DEq l r t, Elem.EqTy l' r' t') => Just [(l, l'), (r, r'), (t, t')]
    (DQuot a r, QuotTy a' r') => Just [(a, a'), (r, r')]
    (DSquash q, Squash u) => Just [(q, u)]
    (DRef y qs, SigVar y' es) => if y == y' && length qs == length (toList es) then Just (zip qs (toList es)) else Nothing
    (DSort sg k qs, QSort sg' k' es) => if eraseQSig sg == Just sg' && k == k' && length qs == length (toList es) then Just (zip qs (toList es)) else Nothing
    (DCtor sg k qs, QCtor sg' k' es) => if eraseQSig sg == Just sg' && k == k' && length qs == length (toList es) then Just (zip qs (toList es)) else Nothing
    _ => Nothing


  ||| Can the derivation RUN from the given side (True: it is the left
  ||| one), decided by shape: a stating derivation can (compare, then
  ||| produce) unless it is one-way; refl can; δ-all runs left to
  ||| right; symmetry flips the direction; transitivity asks its first
  ||| link at the side and its second for the direction alone (its
  ||| side is the middle, unknown here); a conversion or ascription
  ||| asks its inner; a node asks its children at the side's parts —
  ||| which the side must have.
  runnable : Bool -> Drv -> Elem -> Bool
  runnable dir d x =
    if dSynth d && not (structuralD d) then not (oneWay d) || dir else case d of
      DReflx => True
      DDeltaAll _ => dir
      DSym q => runnable (not dir) q x
      DTrans q1 q2 => runnable dir (if dir then q1 else q2) x && dirable dir (if dir then q2 else q1)
      DTransAt q1 _ q2 => runnable dir (if dir then q1 else q2) x && dirable dir (if dir then q2 else q1)
      DConv q Nothing _ => runnable dir q x
      DAscribe q _ _ => runnable dir q x
      _ => case nodeParts d x of
             Just kids => all (\(q, y) => runnable dir q y) kids
             Nothing => False


  ||| → : the directional run from the side d names (True: the left
  ||| side is given), producing the other, unjoined.
  export
  dDir : Sig -> Ctx -> Drv -> Bool -> Elem -> Ty -> KM Elem
  dDir sig ctx d dir x ty = dRun sig ctx d (DGRun dir x Nothing) ty

  ||| The reading of a derivation at a goal — ONE per shape, never
  ||| retried: structure (transitivity, symmetry, the wrappers) is read
  ||| through; a stating or checkable derivation is checked at the type
  ||| and its given side compared; a derivation runnable from the given
  ||| side runs from it; else one runnable from the hint runs from the
  ||| hint, the given side compared with what that produces; else the
  ||| decomposition (a type-directed leaf at both sides, or the shape
  ||| mismatch reported).
  dRun : Sig -> Ctx -> Drv -> DGoal -> Ty -> KM Elem
  dRun sig ctx d goal@(DGRun dir x hint) ty =
    if structuralD d
      then dGo sig ctx d goal ty
      else if dSynth d || dCheckable d
        then checked
        else if runnable dir d x
          then dGo sig ctx d goal ty
          else case hint of
            Just h => if runnable (not dir) d h
              then do
                y <- dGo sig ctx d (DGRun (not dir) h (Just x)) ty
                sameB sig y x
                pure h
              else dGo sig ctx d goal ty
            Nothing => dGo sig ctx d goal ty
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
    (DReflx, DGRun _ x _) => pure x
    (DDeltaAll ns, DGRun True x _) => unfoldAllK sig ns x
    (DDeltaAll ns, DGRun False x (Just h)) => do
      h' <- unfoldAllK sig ns h
      sameB sig h' x
      pure h
    (DDeltaAll ns, DGRun False x Nothing) => kerr "kernel: δ-all runs left to right only"
    (DSym q, DGRun dir x hint) => dRun sig ctx q (DGRun (not dir) x hint) ty
    -- transitivity: the link at the given side runs from it (its
    -- neighbour then reads from the middle, with the hint); else,
    -- given the hint, the link at the hint runs from it and the other
    -- reads from the given side towards that middle; else a stating
    -- far link supplies the middle
    (DTrans q1 q2, DGRun True x hint) =>
      if runnable True q1 x
        then do
          m <- dRun sig ctx q1 (DGRun True x Nothing) ty >>= kJoinElem sig
          dRun sig ctx q2 (DGRun True m hint) ty
        else case hint of
          Just h => if runnable False q2 h
            then do
              m <- dRun sig ctx q2 (DGRun False h Nothing) ty >>= kJoinElem sig
              m' <- dRun sig ctx q1 (DGRun True x (Just m)) ty
              sameB sig m' m
              pure h
            else viaStated2
          Nothing => viaStated2
    (DTrans q1 q2, DGRun False x hint) =>
      if runnable False q2 x
        then do
          m <- dRun sig ctx q2 (DGRun False x Nothing) ty >>= kJoinElem sig
          dRun sig ctx q1 (DGRun False m hint) ty
        else case hint of
          Just h => if runnable True q1 h
            then do
              m <- dRun sig ctx q1 (DGRun True h Nothing) ty >>= kJoinElem sig
              m' <- dRun sig ctx q2 (DGRun False x (Just m)) ty
              sameB sig m' m
              pure h
            else viaStated1
          Nothing => viaStated1
    (DTransAt q1 m q2, DGRun True x hint) => do
      mJ <- middleAt sig ctx m ty
      y <- dRun sig ctx q1 (DGRun True x (Just mJ)) ty
      sameB sig y mJ
      dRun sig ctx q2 (DGRun True mJ hint) ty
    (DTransAt q1 m q2, DGRun False x hint) => do
      mJ <- middleAt sig ctx m ty
      y <- dRun sig ctx q2 (DGRun False x (Just mJ)) ty
      sameB sig y mJ
      dRun sig ctx q1 (DGRun False mJ hint) ty
    -- an ascription around a proof: the position's type converted to
    -- what the annotation derives, the proof read there
    (DAscribe q mT (Just beta), _) => do
      case ty of
        TopTy => kerr "kernel: a type equation cannot convert its type"
        _ => pure ()
      t' <- case mT of
        Just pT => do t' <- dType sig ctx pT; dAt sig ctx beta ty t' TopTy; pure t'
        Nothing => do tyJ <- kJoinElem sig ty; dDir sig ctx beta True tyJ TopTy
      readAt q t'
    (DAscribe q (Just pT) Nothing, _) => do
      t' <- dType sig ctx pT
      agreeAt t'
      readAt q t'
    (DAscribe q Nothing Nothing, _) => readAt q ty
    -- a conversion around a child (a rewritten head or scrutinee
    -- under an exposure, a leaf at a position spelled otherwise): the
    -- child's type is what it states or inverts to, the proof bridges
    -- it to the position's type
    (DConv q Nothing beta, _) => do
      (_, t) <- headOf q
      dAt sig ctx beta t ty TopTy
      readAt q t
    (DConv q (Just _) beta, _) => kerr "kernel: an annotated conversion around a non-stating proof"
    -- ----- type-directed leaves (both sides) -----
    (DIrrel mP, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      ty' <- kWhnfT sig ty
      case ty' of
        OneTy => pure h
        ZeroTy => pure h
        _ => case mP of
          Just pP => do
            (p, _, k) <- dElemTy sig ctx pP
            kPr <- kWhnfT sig k
            case kPr of
              PropTy => pure ()
              _ => kerr "kernel: irrelevance at a non-propositional type"
            ok <- tyAgree sig ty p
            if ok then pure h else kerr "kernel: irrelevance: the derived prop is not the position's type"
          -- no derivation: the position's type (given, well-formed)
          -- judged a prop by the kernel itself
          Nothing => do
            ok <- kIsProp sig ctx ty
            if ok then pure h else kerr "kernel: irrelevance at a non-propositional type [\{show ty}]"
    (DEtaPi q, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      ty' <- kWhnfT sig ty
      case ty' of
        PiTy dom cod => do
          dAt sig (ctx :< dom) q (PiApp (substElem l Wk) (CtxVar 0)) (PiApp (substElem r Wk) (CtxVar 0)) cod
          pure h
        _ => kerr "kernel: Π-η at a non-Π type"
    (DEtaSigma q1 q2, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      ty' <- kWhnfT sig ty
      case ty' of
        SigmaTy dom cod => do
          dAt sig ctx q1 (SigmaElim1 l) (SigmaElim1 r) dom
          dAt sig ctx q2 (SigmaElim2 l) (SigmaElim2 r) (substTy cod (Ext Id (SigmaElim1 l)))
          pure h
        _ => kerr "kernel: Σ-η at a non-Σ type"
    (DQuotWit mq, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      ty' <- kWhnfT sig ty
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      case (ty', lJ, rJ) of
        (QuotTy _ rel, Class a, Class b) => do
          inst <- kJoinElem sig (substElem rel (Ext (Ext Id a) b))
          case (inst, mq) of
            (Squash OneTy, _) => pure h
            (Elem.EqTy wl wr wt, Just q) => do dAt sig ctx q wl wr wt; pure h
            _ => kerr "kernel: quotient witness: the relation instance has no evident shape"
        _ => kerr "kernel: quotient witness at a non-class equation"
    (DQuotWitPrf w, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      ty' <- kWhnfT sig ty
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      case (ty', lJ, rJ) of
        (QuotTy _ rel, Class a, Class b) => do
          _ <- dElemAt sig ctx w (substElem rel (Ext (Ext Id a) b))
          pure h
        _ => kerr "kernel: quotient witness at a non-class equation"
    (DInj q, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      ty' <- kWhnfT sig ty
      lJ <- kJoinElem sig l
      rJ <- kJoinElem sig r
      case (ty', lJ, rJ) of
        (SumTy a _, Inj1 x, Inj1 y) => do dAtJ sig ctx q x y a; pure h
        (SumTy _ b, Inj2 x, Inj2 y) => do dAtJ sig ctx q x y b; pure h
        _ => kerr "kernel: injection leaf at a non-matching equation"
    (DPropExt f g, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      ty' <- kWhnfT sig ty
      case ty' of
        PropTy => do
          _ <- dElemAt sig ctx f (PiTy l (substTy r Wk))
          _ <- dElemAt sig ctx g (PiTy r (substTy l Wk))
          pure h
        _ => kerr "kernel: propext at a non-Ω type"
    (DPrfCong mP mQ q, DGRun dir x (Just h)) => do
      let (l, r) = ordered dir x h
      case ty of
        TopTy => pure ()
        _ => kerr "kernel: prop-lift on an element equation"
      propSide mP l
      propSide mQ r
      dAtJ sig ctx q l r PropTy
      pure h
    (DIrrel _, DGRun _ _ Nothing) => needBoth
    (DEtaPi _, DGRun _ _ Nothing) => needBoth
    (DEtaSigma _ _, DGRun _ _ Nothing) => needBoth
    (DQuotWit _, DGRun _ _ Nothing) => needBoth
    (DQuotWitPrf _, DGRun _ _ Nothing) => needBoth
    (DInj _, DGRun _ _ Nothing) => needBoth
    (DPropExt _ _, DGRun _ _ Nothing) => needBoth
    (DPrfCong _ _ _, DGRun _ _ Nothing) => needBoth
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
      node (\x => case x of SumElim l r t => Just [l, r, t]; _ => Nothing)
           (\xs => case xs of [l, r, t] => Just (SumElim l r t); _ => Nothing)
           (\xs => case xs of
                     [_, _, t] => do
                       (a, b, tTy) <- scrutOf qt (\t => case t of SumTy a b => Just (a, b); _ => Nothing) "⊎-elim"
                       mot <- case mM of
                                Just pM => dType sig (ctx :< SumTy a b) pM
                                Nothing => pure (substTy ty Wk)
                       agreeAt (substTy mot (Ext Id t))
                       pure [ (ctx :< a, substTy mot (Ext Wk (Inj1 (CtxVar 0))))
                            , (ctx :< b, substTy mot (Ext Wk (Inj2 (CtxVar 0))))
                            , (ctx, tTy) ]
                     _ => arity) [ql, qr, qt]
    (DQuotElim mM _ qf qq, _) => do
      node (\x => case x of QuotElim f q => Just [f, q]; _ => Nothing)
           (\xs => case xs of [f, q] => Just (QuotElim f q); _ => Nothing)
           (\xs => case xs of
                     [_, q] => do
                       (a, rel, qTy) <- scrutOf qq (\t => case t of QuotTy a r => Just (a, r); _ => Nothing) "quot-elim"
                       mot <- case mM of
                                Just pM => dType sig (ctx :< QuotTy a rel) pM
                                Nothing => pure (substTy ty Wk)
                       agreeAt (substTy mot (Ext Id q))
                       pure [(ctx :< a, substTy mot (Ext Wk (Class (CtxVar 0)))), (ctx, qTy)]
                     _ => arity) [qf, qq]
    (DOut q, _) =>
      node (\x => case x of Out u => Just [u]; _ => Nothing)
           (\xs => case xs of [u] => Just (Out u); _ => Nothing)
           (\_ => do (_, tTy) <- headOfU q; pure [(ctx, tTy)]) [q]
    (DApp qf qa, _) =>
      node (\x => case x of PiApp f a => Just [f, a]; _ => Nothing)
           (\xs => case xs of [f, a] => Just (PiApp f a); _ => Nothing)
           (\xs => case xs of
                     [_, _] => do
                       (fTy', fTy) <- headOfU qf
                       case fTy' of
                         PiTy dom cod => pure [(ctx, fTy), (ctx, dom)]
                         _ => kerr "kernel: application congruence: the head is not a function"
                     _ => arity) [qf, qa]
    (DProj1 q, _) =>
      node (\x => case x of SigmaElim1 u => Just [u]; _ => Nothing)
           (\xs => case xs of [u] => Just (SigmaElim1 u); _ => Nothing)
           (\_ => do (_, tTy) <- headOfU q; pure [(ctx, tTy)]) [q]
    (DProj2 q, _) =>
      node (\x => case x of SigmaElim2 u => Just [u]; _ => Nothing)
           (\xs => case xs of [u] => Just (SigmaElim2 u); _ => Nothing)
           (\_ => do (_, tTy) <- headOfU q; pure [(ctx, tTy)]) [q]
    (DCorec dpf qa qf qx, _) => do
      pf <- polyE dpf
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
        DGRun dir x hint => case x of
          QuotTy a r => do
            let hs = the (Maybe Elem, Maybe Elem) $ case hint of
                       Just (QuotTy a1 r1) => (Just a1, Just r1)
                       _ => (Nothing, Nothing)
            a' <- dRun sig ctx qa (DGRun dir a (fst hs)) cls
            let dom = if dir then a' else a
            r' <- dRun sig (ctx :< dom :< substTy dom Wk) qr (DGRun dir r (snd hs)) PropTy
            pure (QuotTy a' r')
          _ => kerr "kernel: proof shape does not match the side [\{show x}] at \{showDrv d}"
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
    (DSort dsg k qs, _) => do
      sg <- qsigE dsg
      node (\u => case u of
                    QSort sg' k' es => if sg == sg' && k == k' then Just (toList es) else Nothing
                    _ => Nothing)
           (\xs => Just (QSort sg k (cast xs)))
           (\es => traverse (\i => case qSpineChildTy sg k (cast es) i of
                                      Just t => pure (ctx, t)
                                      Nothing => kerr "kernel: spine entry out of range") (indices es)) qs
    (DCtor dsg k qs, _) => do
      sg <- qsigE dsg
      node (\u => case u of
                    QCtor sg' k' es => if sg == sg' && k == k' then Just (toList es) else Nothing
                    _ => Nothing)
           (\xs => Just (QCtor sg k (cast xs)))
           (\es => traverse (\i => case qSpineChildTy sg k (cast es) i of
                                      Just t => pure (ctx, t)
                                      Nothing => kerr "kernel: spine entry out of range") (indices es)) qs
    (DQElim dsg k cs _ qm qs qw, _) => do
      (sg, _) <- dQSig sig ctx dsg
      -- motives derived in their sort contexts (none given: the
      -- CONSTANT motives, every sort's the position's type weakened
      -- into the sort's context — the checking sugar); the methods at
      -- their method types, the spine at the telescope, the eliminee
      -- at the sort (the coherences are a property of the carried
      -- problem, read under ⇒ — the sides share it syntactically)
      mots <- maybe (constMotives sig ctx sg ty) (qMotives sig ctx sg) cs
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
    (_, DGRun _ _ _) => kerr "kernel: derivation does not read against given sides [\{showDrv d}]"
   where
    arity : KM a
    arity = kerr "kernel: proof node arity"

    needBoth : KM Elem
    needBoth = kerr "kernel: a type-directed proof needs both sides [\{showDrv d}]"

    -- the inner of a conversion or ascription read at the converted
    -- type, by the reading its shape decides (a stating inner is
    -- checked, not decomposed)
    readAt : Drv -> Ty -> KM Elem
    readAt q t = dRun sig ctx q goal t

    -- the sides in order, from the given side and the hint
    ordered : Bool -> Elem -> Elem -> (Elem, Elem)
    ordered dir x h = if dir then (x, h) else (h, x)


    agreeAt : Ty -> KM ()
    agreeAt t = do
      ok <- tyAgree sig ty t
      if ok then pure ()
        else kerr "kernel: the node's type does not agree with the position's\n  node: \{show t}\n  position: \{show ty}"

    -- transitivity with neither link runnable: a stating far link
    -- supplies the middle
    viaStated2 : KM Elem
    viaStated2 = case (d, goal) of
      (DTrans q1 q2, DGRun True x _) =>
        if dSynth q2
          then do
            (b, c, t) <- dInfer sig ctx q2
            agreeAt t
            bJ <- kJoinElem sig b
            m' <- dRun sig ctx q1 (DGRun True x (Just bJ)) ty
            sameB sig m' bJ
            pure c
          else kerr "kernel: transitivity with no computable middle (left to right)"
      _ => arity
    viaStated1 : KM Elem
    viaStated1 = case (d, goal) of
      (DTrans q1 q2, DGRun False x _) =>
        if dSynth q1
          then do
            (a, b, t) <- dInfer sig ctx q1
            agreeAt t
            bJ <- kJoinElem sig b
            m' <- dRun sig ctx q2 (DGRun False x (Just bJ)) ty
            sameB sig m' bJ
            pure a
          else kerr "kernel: transitivity with no computable middle (right to left)"
      _ => arity

    indices : List a -> List Nat
    indices xs = go 0 xs
     where
      go : Nat -> List a -> List Nat
      go _ [] = []
      go i (_ :: rest) = i :: go (S i) rest

    goalSide : Elem
    goalSide = case goal of
      DGRun _ x _ => x

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
    -- a prop-lift side: the derivation given derives it at Ω and meets
    -- the side under β; none given, the side (well-formed) is judged a
    -- prop by the kernel itself
    propSide : Maybe Drv -> Elem -> KM ()
    propSide (Just pP) side = do
      p <- dElemAt sig ctx pP PropTy
      sameB sig p side
    propSide Nothing side = do
      ok <- kIsProp sig ctx side
      if ok then pure () else kerr "kernel: prop-lift at a non-proposition [\{show side}]"

    ||| derives; else — a rewrite inside the head — read off the given
    ||| side's head by typing inversion (the neutral-subterm rule, §6:
    ||| a spine's head has a declared type, opened along the spine by
    ||| the β-whnf), never invented.

    -- typing by inversion STRUCTURALLY through the child's nodes, the
    -- given side's term alongside: an exposure inside the child is
    -- run where it sits (a stuck head whose scrutinee's type a
    -- definition hides), an application's codomain instantiated by
    -- the side's argument; a bare head inverts from its term
    headOfMT : Drv -> Elem -> KM (Maybe (Ty, Ty))
    headOfMT q term =
      if dSynth q
        then do
          (_, _, t) <- dInfer sig ctx q
          t' <- kWhnfT sig t
          pure (Just (t', t))
        else case (q, term) of
          -- a chain: its links share one type, the first link's left
          -- side is the term
          (DTrans q1 _, _) => headOfMT q1 term
          (DTransAt q1 _ _, _) => headOfMT q1 term
          -- an exposure around a non-stating head: the proof run from
          -- the type the head inverts to
          (DConv q' Nothing beta, _) => do
            m <- headOfMT q' term
            case m of
              Nothing => pure Nothing
              Just (_, t0) => do
                tJ <- kJoinElem sig t0
                t <- dDir sig ctx beta True tJ TopTy
                t' <- kWhnfT sig t
                pure (Just (t', t))
          (DOut q', Out t) => part q' t (\t' => case t' of
                                           NuTy f => Just (reflectPoly f (Elem.NuTy f))
                                           _ => Nothing)
          (DProj1 q', SigmaElim1 t) => part q' t (\t' => case t' of
                                                   SigmaTy a _ => Just a
                                                   _ => Nothing)
          (DProj2 q', SigmaElim2 t) => part q' t (\t' => case t' of
                                                   SigmaTy _ b => Just (substTy b (Ext Id (SigmaElim1 t)))
                                                   _ => Nothing)
          (DApp qf _, PiApp ft at) => part qf ft (\t' => case t' of
                                                   PiTy _ cod => Just (substTy cod (Ext Id at))
                                                   _ => Nothing)
          -- an eliminator node WITH its motive: the motive's instance
          -- at the side's scrutinee is its type, whatever its
          -- children state (the scrutinee's type from the scrutinee
          -- child, the same way)
          (DNatElim (Just pM) _ _ _, NatElim _ _ n) => do
            mot <- dType sig (ctx :< NatTy) pM
            done (substTy mot (Ext Id n))
          (DSumElim (Just pM) _ _ qt, SumElim _ _ t) => do
            m <- headOfMT qt t
            case m of
              Just (SumTy a b, _) => do
                mot <- dType sig (ctx :< SumTy a b) pM
                done (substTy mot (Ext Id t))
              _ => pure Nothing
          (DQuotElim (Just pM) _ _ qq, QuotElim _ q) => do
            m <- headOfMT qq q
            case m of
              Just (QuotTy a r, _) => do
                mot <- dType sig (ctx :< QuotTy a r) pM
                done (substTy mot (Ext Id q))
              _ => pure Nothing
          (DQElim dsg k (Just cs) _ _ _ _, QElim sg' k' _ es w) =>
            if eraseQSig dsg == Just sg' && k == k'
              then do
                mots <- qMotives sig ctx sg' cs
                case (qOrdinal QKSort sg' k >>= \o => getAt o mots) of
                  Just motK => done (substTy motK (Ext (foldl Ext Id (toList es)) w))
                  Nothing => pure Nothing
              else pure Nothing
          _ => do
            mt <- inferHead sig ctx term
            case mt of
              Just t => do t' <- kWhnfT sig t; pure (Just (t', t))
              Nothing => pure Nothing
     where
      done : Ty -> KM (Maybe (Ty, Ty))
      done t = do t' <- kWhnfT sig t; pure (Just (t', t))

      part : Drv -> Elem -> (Ty -> Maybe Ty) -> KM (Maybe (Ty, Ty))
      part q' t pick = do
        m <- headOfMT q' t
        case m of
          Nothing => pure Nothing
          Just (t', _) => case pick t' of
            Just ty => do ty' <- kWhnfT sig ty; pure (Just (ty', ty))
            Nothing => pure Nothing

    -- … Nothing exactly when the child states nothing and its side's
    -- head does not invert
    headOfM : Drv -> KM (Maybe (Ty, Ty))
    headOfM q = headOfMT q headTerm

    -- (a head whose type is neither stated nor inverted is REJECTED:
    -- every position is typed, there is no undetermined position)
    headOfU : Drv -> KM (Ty, Ty)
    headOfU q = do
      m <- headOfM q
      case m of
        Just r => pure r
        Nothing => kerr "kernel: a head child's type is neither stated nor inverted [\{showDrv q}]"

    headOf : Drv -> KM (Ty, Ty)
    headOf q = do
      m <- headOfM q
      case m of
        Just r => pure r
        Nothing => kerr "kernel: a head or scrutinee child must derive its type [\{showDrv q}]"

    scrutOf : Drv -> (Ty -> Maybe (Ty, Ty)) -> String -> KM (Ty, Ty, Ty)
    scrutOf q pick what = do
      m <- headOfM q
      case m of
        Just (t', t) => case pick t' of
          Just (a, b) => pure (a, b, t)
          Nothing => kerr "kernel: \{what}: the scrutinee's type has no shape for it [\{show t'}]"
        Nothing => kerr "kernel: \{what}: the scrutinee's type is neither stated nor inverted [\{showDrv q}]"

    ||| A node: the side(s) decompose by `shape` into the children's
    ||| parts, `kids` computes each child's context and expected type
    ||| from the LEFT parts, the children are read against their
    ||| parts, and `rebuild` reassembles.
    node : (Elem -> Maybe (List Elem)) -> (List Elem -> Maybe Elem)
        -> (List Elem -> KM (List (Ctx, Ty))) -> List Drv -> KM Elem
    node shape rebuild kids qs = case goal of
      DGRun dir x hint => do
        xs <- case shape x of
          Just xs => pure xs
          Nothing => kerr "kernel: proof shape does not match the side [\{show x}] at \{showDrv d}"
        -- the hint's parts, when it has the shape too
        let hs = the (List (Maybe Elem)) $ case the (Maybe (List Elem)) (maybe Nothing shape hint) of
                   Just hs => if length hs == length xs then map Just hs else map (const Nothing) xs
                   Nothing => map (const Nothing) xs
        infos <- kids xs
        outs <- goKids dir qs xs hs infos
        case rebuild outs of
          Just e => pure e
          Nothing => arity
     where
      goKids : Bool -> List Drv -> List Elem -> List (Maybe Elem) -> List (Ctx, Ty) -> KM (List Elem)
      goKids _ [] [] [] [] = pure []
      goKids dir (q :: qs') (l :: ls') (h :: hs') ((cx, t) :: infos') = do
        out <- dRun sig cx q (DGRun dir l h) t
        outs <- goKids dir qs' ls' hs' infos'
        pure (out :: outs)
      goKids _ _ _ _ _ = arity

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
        DGRun dir x hint => case shape x of
          Just (a, b) => do
            let hs = the (Maybe Elem, Maybe Elem) $ case the (Maybe (Elem, Elem)) (maybe Nothing shape hint) of
                       Just (a1, b1) => (Just a1, Just b1)
                       Nothing => (Nothing, Nothing)
            a' <- dRun sig ctx qa (DGRun dir a (fst hs)) cls
            let dom = if dir then a' else a
            b' <- dRun sig (ctx :< dom) qb (DGRun dir b (snd hs)) cls
            pure (rebuild a' b')
          Nothing => kerr "kernel: proof shape does not match the side [\{show x}] at \{showDrv d}"

  -- ----- shared pieces of the readings -----

  ||| An annotation derives a TYPE: an element derivation classified
  ||| at 𝕍, or at 𝕌 or Ω by cumulativity.
  export
  dType : Sig -> Ctx -> Drv -> KM Ty
  dType sig ctx d = fst <$> dTypeK sig ctx d

  ||| … with the classifier it derives at (𝕌, Ω or 𝕍).
  dTypeK : Sig -> Ctx -> Drv -> KM (Ty, Ty)
  dTypeK sig ctx d = do
    (t, t', k) <- dInfer sig ctx d
    if t == t' then pure () else kerr "kernel: a type annotation states a proper equation"
    ok <- tyAgree sig TopTy k
    if ok then pure (t, k) else kerr "kernel: a type annotation derives no type [\{show t} : \{show k}]"

  ||| An ELEMENT derivation, inferred: its sides coincide.
  export
  ||| A stated middle (10.2): an element derivation checked at the
  ||| chain's type, its erasure β-joined for the links to run from.
  middleAt : Sig -> Ctx -> Drv -> Ty -> KM Elem
  middleAt sig ctx m ty = dElemAt sig ctx m ty >>= kJoinElem sig

  dElemTy : Sig -> Ctx -> Drv -> KM (Elem, Elem, Ty)
  dElemTy sig ctx d = do
    (t, t', ty) <- dInfer sig ctx d
    if t == t' then pure (t, t', ty) else kerr "kernel: an element position states a proper equation [\{showDrv d}]"

  ||| An ELEMENT derivation checked at a type.
  export
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

  ||| A signature reference at a stated spine (each entry may state a
  ||| proper equation: the congruence at the reference, the entry types
  ||| instantiated by the LEFT entries).
  dRefAt : Sig -> Ctx -> String -> List Drv -> Ctx -> Ty -> KM (Elem, Elem, Ty)
  dRefAt sig ctx x ps delta ty = do
    es <- dSpineE sig ctx (toList delta) ps
    let lN = the SubNorm (cast (map fst es))
    let rN = the SubNorm (cast (map snd es))
    pure (SigVar x lN, SigVar x rN, substTy ty (embed lN))

  ||| A stated SPINE (§3): entry i an element derivation at the
  ||| telescope entry instantiated by the earlier entries.
  dSpine : Sig -> Ctx -> List Ty -> List Drv -> KM (List Elem)
  dSpine sig ctx delta qs = do
    es <- dSpineE sig ctx delta qs
    traverse (\(l, r) => if l == r then pure l else kerr "kernel: a spine entry states a proper equation") es

  ||| A spine whose entries may state proper equations, each at the
  ||| telescope entry instantiated by the earlier LEFT entries.
  dSpineE : Sig -> Ctx -> List Ty -> List Drv -> KM (List (Elem, Elem))
  dSpineE sig ctx delta qs =
    if length qs /= length delta
      then kerr "kernel: spine length mismatch"
      else go 0 qs []
   where
    go : Nat -> List Drv -> List (Elem, Elem) -> KM (List (Elem, Elem))
    go i [] acc = pure (reverse acc)
    go i (q :: rest) acc = do
      ty <- case getAt i delta of
              Just t => pure (substTy t (embed (cast (map fst (reverse acc)))))
              Nothing => kerr "kernel: spine entry type undetermined"
      lr <- dCheck sig ctx q ty
      go (S i) rest (lr :: acc)

  ||| A stated spine at a reflected TELESCOPE (a constructor's, a
  ||| sort's, a path's).
  dTele : Sig -> Ctx -> List Ty -> List Drv -> KM (List Elem)
  dTele sig ctx tel qs = do
    es <- dTeleE sig ctx tel qs
    traverse (\(l, r) => if l == r then pure l else kerr "kernel: a telescope entry states a proper equation") es

  ||| A telescope spine whose entries may state proper equations, each
  ||| at the entry type instantiated by the earlier LEFT entries.
  dTeleE : Sig -> Ctx -> List Ty -> List Drv -> KM (List (Elem, Elem))
  dTeleE sig ctx tel qs =
    if length qs /= length tel
      then kerr "kernel: telescope spine length mismatch"
      else go 0 qs []
   where
    go : Nat -> List Drv -> List (Elem, Elem) -> KM (List (Elem, Elem))
    go i [] acc = pure (reverse acc)
    go i (q :: rest) acc = do
      ty <- case telInst tel i (map fst (reverse acc)) of
              Just t => pure t
              Nothing => kerr "kernel: telescope entry type undetermined"
      lr <- dCheck sig ctx q ty
      go (S i) rest (lr :: acc)

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
  quotElimAt : Sig -> Ctx -> (Ty, Maybe Ty) -> Ty -> Elem -> Maybe Drv -> Drv -> (Elem, Elem, Ty) -> KM (Elem, Elem, Ty)
  quotElimAt sig ctx (mot, mcls) a rel wd f (ql, qr, _) = do
    (fl, fr) <- dCheck sig (ctx :< a) f (substTy mot (Ext Wk (Class (CtxVar 0))))
    -- the motive a prop: by its own derivation's classifier when it
    -- was derived (the motive annotation), else the kernel's question
    -- on the bare type
    mIsP <- case mcls of
      Just k => do k' <- kWhnfT sig k
                   case k' of
                     PropTy => pure True
                     _ => kIsProp sig (ctx :< QuotTy a rel) mot
      Nothing => kIsProp sig (ctx :< QuotTy a rel) mot
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
    mots <- qMotives sig ctx sg cs
    qElimAtM sig ctx sg k mots cohs qm qs qw

  ||| The CONSTANT motives at a type (the checking sugar, §10.3): every
  ||| sort's motive is the type weakened into the sort's context.
  constMotives : Sig -> Ctx -> QSig -> Ty -> KM (List Ty)
  constMotives sig ctx sg ty =
    traverse (\sj => do
      sjE <- case qEntry sg sj of
               Just x => pure x
               Nothing => kerr "kernel: sort out of range"
      (tel, _, _) <- liftQ (reflTel sg (qwAt sj) sjE)
      pure (substTy ty (wkN (S (length tel))))) (qPositions QKSort sg)

  ||| … at given motive TYPES.
  qElimAtM : Sig -> Ctx -> QSig -> Nat -> List Ty -> List Drv -> List Drv -> List Drv -> Drv -> KM (Elem, Elem, Ty)
  qElimAtM sig ctx sg k mots cohs qm qs qw = do
    sortE <- case qEntry sg k of
               Just x => pure x
               Nothing => kerr "kernel: eliminator sort out of range"
    case qEntryKind sortE of
      QKSort => pure ()
      _ => kerr "kernel: eliminator at a non-sort position"
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

  ||| A derivation of a PROP: an element derivation classified at Ω, or
  ||| whose erasure is ≡-/∥·∥-headed.
  dPropAt : Sig -> Ctx -> Drv -> KM Ty
  dPropAt sig ctx pQ = do
    (q, q', k) <- dInfer sig ctx pQ
    if q == q' then pure () else kerr "kernel: a prop annotation states a proper equation"
    k' <- kWhnfT sig k
    case k' of
      PropTy => pure q
      _ => do
        qW <- kWhnfT sig q
        case qW of
          Elem.EqTy _ _ _ => pure q
          Squash _ => pure q
          _ => kerr "kernel: the annotation derives no proposition [\{show q} : \{show k}]"

  ||| el-squash-e-prf at a goal prop: the scrutinee derives ∥A∥, the
  ||| body proves the goal under A.
  squashElimAt : Sig -> Ctx -> Ty -> Drv -> Drv -> KM ()
  squashElimAt sig ctx goal e b = do
    okQ <- kIsProp sig ctx goal
    if okQ then pure () else kerr "kernel: squash-elim at a non-prop goal"
    squashElimAtP sig ctx goal e b

  ||| … the goal's prop-ness already established.
  squashElimAtP : Sig -> Ctx -> Ty -> Drv -> Drv -> KM ()
  squashElimAtP sig ctx goal e b = do
    (_, _, eTy) <- dElemTy sig ctx e
    eTy' <- kWhnfT sig eTy
    case eTy' of
      Squash a => do
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

||| The rejected derivation, appended to the verdict under NOVA_DRV.
dump : String -> Drv -> String
dump what d = if drvCanary then "\n  \{what} DERIVATION: \{showDrv d}" else ""

||| A definition item as derivations: the telescope, the type, the
||| body; the entry extends Σ with their ERASURES.
export
kCheckDefDrv : Sig -> Nat -> String -> List Drv -> Drv -> Drv -> Either KErr SigEntry
kCheckDefDrv sig fuel name tele dty body =
  map fst $ runKM (do
    ctx <- tele' [<] tele
    ty <- kCatch (dType sig ctx dty) (\e => kerr (e ++ dump "TYPE" dty))
    t <- kCatch (dElemAt sig ctx body ty) (\e => kerr (e ++ dump "BODY" body))
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
    ty <- kCatch (dType sig ctx dty) (\e => kerr (e ++ dump "TYPE" dty))
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
    kCatch (dAt sig ctx d lJ rJ ty) (\e => kerr (e ++ dump "EQUATION" d))) fuel)

-- ===== Re-derivation: a bare term as a derivation =====
--
-- What the elaborator did not elaborate — a hole's solution, a
-- recovered motive, an inferred type standing as an annotation, an
-- engine leaf, an embedded code of a polynomial or a signature — is
-- DERIVED against its type by the same bidirectional walk the reader
-- takes, building instead of checking (§10.6). Nothing here is
-- trusted: every derivation built is read afterwards.

zipWithIndex : Nat -> List a -> List (Nat, a)
zipWithIndex _ [] = []
zipWithIndex i (x :: xs) = (i, x) :: zipWithIndex (S i) xs

export
dTrans : Drv -> Drv -> Drv
dTrans DReflx q = q
dTrans p DReflx = p
dTrans p q = DTrans p q

export
dSym : Drv -> Drv
dSym DReflx = DReflx
dSym (DSym p) = p
dSym p = DSym p

export
congOfD : Drv -> Drv -> Drv
congOfD DReflx _ = DReflx
congOfD _ node = node

mutual
  ||| Head exposure with its δ PROVED (the proof library's exposeK, on
  ||| derivations): the term taken to its β-whnf with every definition
  ||| unfolded on the way to the head as a δ leaf inside the node of
  ||| its position, and the proof of t ≐ exposed (refl when β alone
  ||| reached it).
  export
  rdExpose : Sig -> Ctx -> Elem -> KM (Elem, Drv)
  rdExpose = rdExposeW (const True)

  ||| … under a whitelist of the definitions that may unfold (the
  ||| engine's exposure at a site: what its citations license).
  export
  rdExposeW : (String -> Bool) -> Sig -> Ctx -> Elem -> KM (Elem, Drv)
  rdExposeW ok sig ctx = rdExposeWT ok sig ctx Nothing

  ||| … from a known type of the term (a type at 𝕍, an element at its
  ||| position's type): the eliminator nodes the walk writes at the
  ||| top carry the constant motive there.
  export
  rdExposeWT : (String -> Bool) -> Sig -> Ctx -> Maybe Ty -> Elem -> KM (Elem, Drv)
  rdExposeWT ok sig ctx mty0 t = do
    (r, p, _) <- go mty0 t
    pure (r, p)
   where
    -- the walk threads the TYPE of the term where it is free — a
    -- definition's declared type at its spine, the type of a β-reduct
    -- (the redex's), a scrutinee's shape — so that an eliminator node
    -- it writes around a scrutinee exposure carries its motive: such
    -- a node may stand in a HEAD position (a stuck eliminator that
    -- unfolding produced, scrutinee of another elimination), where no
    -- type flows down and the kernel types it by its motive alone
    go : Maybe Ty -> Elem -> KM (Elem, Drv, Maybe Ty)
    -- a rewritten head or scrutinee child under the exposure of its
    -- declared type when a definition hides the shape its node needs;
    -- with the shaped type (Nothing at refl: nothing computed)
    shapedChild : Elem -> Maybe Ty -> (Ty -> Bool) -> Drv -> KM (Drv, Maybe Ty)
    shapedChild orig mt want p1 = case p1 of
      DReflx => pure (DReflx, Nothing)
      _ => do
        mt' <- the (KM (Maybe Ty)) $ case mt of
                 Just t => pure (Just t)
                 Nothing => inferHead sig ctx orig
        case the (Maybe Ty) mt' of
          Nothing => pure (p1, Nothing)
          Just ty => do
            ty' <- kWhnfT sig ty
            if want ty' then pure (p1, Just ty') else do
              -- (the TYPE's exposure is the reader's own need, free of
              -- the site's whitelist, which governs the term)
              (tX, pt) <- rdExposeW (const True) sig ctx ty
              tW <- kWhnfT sig tX
              pure (case pt of
                      DReflx => (p1, Nothing)
                      _ => if want tW then (DConv p1 Nothing pt, Just tW) else (p1, Nothing))
    -- the constant motive at the node's type over the scrutinee's
    -- (both known), else the motive the eliminator's inference
    -- determines (Nothing when neither: the node then reads at the
    -- type flowing down, or is rejected)
    motiveInf : Elem -> KM (Maybe Drv)
    motiveInf e =
      kOrElse (do (d, _) <- rdInfer sig ctx e
                  pure (case d of
                          DNatElim m _ _ _ => m
                          DSumElim m _ _ _ => m
                          DQuotElim m _ _ _ => m
                          _ => Nothing))
              (pure Nothing)
    motiveOf : Drv -> Maybe Ty -> Maybe Ty -> Elem -> KM (Maybe Drv)
    motiveOf DReflx _ _ _ = pure Nothing
    motiveOf _ (Just t) (Just sTy) _ =
      kOrElse (Just <$> rdTypeBare sig (ctx :< sTy) (substTy t Wk)) (pure Nothing)
    motiveOf _ _ _ e = motiveInf e
    isPi, isSigma, isNu, isSum, isQuot : Ty -> Bool
    isPi (PiTy _ _) = True
    isPi _ = False
    isSigma (SigmaTy _ _) = True
    isSigma _ = False
    isNu (NuTy _) = True
    isNu _ = False
    isSum (SumTy _ _) = True
    isSum _ = False
    isQuot (QuotTy _ _) = True
    isQuot _ = False
    -- the type of a projection from the pair's (the shaped type the
    -- scrutinee child was exposed to, else the β-whnf of the known
    -- type when it shows the Σ)
    projTy : Maybe Ty -> Maybe Ty -> Maybe Ty -> (Ty -> Ty -> Ty) -> KM (Maybe Ty)
    projTy (Just t) _ _ _ = pure (Just t)
    projTy Nothing mu sTy pick = do
      st <- the (KM (Maybe Ty)) $ case sTy of
              Just t => pure (Just t)
              Nothing => case mu of
                Just t => Just <$> kWhnfT sig t
                Nothing => pure Nothing
      pure (case st of
              Just (SigmaTy a b) => Just (pick a b)
              _ => Nothing)
    -- the type of an application from its head's, when the head's
    -- β-whnf shows the Π (no exposure: a type is threaded only where
    -- it is free)
    appTy : Maybe Ty -> Maybe Ty -> Elem -> KM (Maybe Ty)
    appTy (Just t) _ _ = pure (Just t)
    appTy Nothing (Just fTy) e = do
      f' <- kWhnfT sig fTy
      pure (case f' of
              PiTy _ cod => Just (substTy cod (Ext Id e))
              _ => Nothing)
    appTy Nothing Nothing _ = pure Nothing
    -- a δ leaf states at the definition's declared type; where the
    -- position's type is spelled otherwise (a proof written at the
    -- exposed type of its equation) the leaf arrives ascribed to the
    -- position's spelling, the bridge read against both
    atPos' : Drv -> Ty -> Ty -> KM Drv
    atPos' leaf tyI t = do
      ok' <- tyAgree sig t tyI
      if ok' then pure leaf else do
        mb <- rdBridgeAny sig ctx tyI t
        case mb of
          Just b => do
            -- the target derived when it can be (the bridge then read
            -- against both spellings), else the bridge RUN from the
            -- declared spelling
            mT <- kOrElse (Just <$> rdTypeBare sig ctx t) (pure Nothing)
            pure (case mT of
                    Just dT => DAt leaf dT b
                    Nothing => DConv leaf Nothing b)
          Nothing => pure leaf
    atPos : Drv -> Ty -> Maybe Ty -> KM Drv
    atPos leaf _ Nothing = pure leaf
    atPos leaf tyI (Just t) = atPos' leaf tyI t
    go mty (SigVar x es) =
      if not (ok x) then pure (SigVar x es, DReflx, mty) else
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef delta _ a ty) => do
          qs <- rdSpine sig ctx (toList delta) (toList es)
          let tyI = substTy ty (embed es)
          leaf <- atPos (DDelta x qs) tyI mty
          (r, p, mt) <- go (Just tyI) (substElem a (embed es))
          pure (r, dTrans leaf p, mt)
        Just (SigDecl delta _ ty) => pure (SigVar x es, DReflx, Just (substTy ty (embed es)))
        _ => pure (SigVar x es, DReflx, mty)
    go mty (PiApp f e) = do
      (f', p0, mf) <- go Nothing f
      (p1, _) <- shapedChild f mf isPi p0
      rt <- appTy mty mf e
      case f' of
        PiIntro g => do
          (r, p2, mt) <- go rt (substElem g (Ext Id e))
          pure (r, dTrans (congOfD p1 (DApp p1 DReflx)) p2, mt)
        _ => pure (PiApp f' e, congOfD p1 (DApp p1 DReflx), rt)
    go mty (Let a b) = go mty (substElem b (Ext (Ext Id a) Star))
    go mty (NatElim z st u) = do
      (u', p1, _) <- go (Just NatTy) u
      mm <- motiveOf p1 mty (Just NatTy) (NatElim z st u)
      let node = congOfD p1 (DNatElim mm DReflx DReflx p1)
      case u' of
        NatIntro0 => do (r, p2, mt) <- go mty z; pure (r, dTrans node p2, mt)
        NatIntro1 n => do (r, p2, mt) <- go mty (substElem st (Ext (Ext Id n) (NatElim z st n))); pure (r, dTrans node p2, mt)
        _ => pure (NatElim z st u', node, mty)
    go mty (SigmaElim1 u) = do
      (u', p0, mu) <- go Nothing u
      (p1, sTy) <- shapedChild u mu isSigma p0
      rt <- projTy mty mu sTy (\a, _ => a)
      case u' of
        SigmaIntro a _ => do (r, p2, mt) <- go rt a; pure (r, dTrans (congOfD p1 (DProj1 p1)) p2, mt)
        _ => pure (SigmaElim1 u', congOfD p1 (DProj1 p1), rt)
    go mty (SigmaElim2 u) = do
      (u', p0, mu) <- go Nothing u
      (p1, sTy) <- shapedChild u mu isSigma p0
      rt <- projTy mty mu sTy (\_, b => substTy b (Ext Id (SigmaElim1 u)))
      case u' of
        SigmaIntro _ b => do (r, p2, mt) <- go rt b; pure (r, dTrans (congOfD p1 (DProj2 p1)) p2, mt)
        _ => pure (SigmaElim2 u', congOfD p1 (DProj2 p1), rt)
    go mty (SumElim l r u) = do
      (u', p0, mu) <- go Nothing u
      (p1, sTy) <- shapedChild u mu isSum p0
      mm <- motiveOf p1 mty sTy (SumElim l r u)
      let node = congOfD p1 (DSumElim mm DReflx DReflx p1)
      case u' of
        Inj1 a => do (r', p2, mt) <- go mty (substElem l (Ext Id a)); pure (r', dTrans node p2, mt)
        Inj2 b => do (r', p2, mt) <- go mty (substElem r (Ext Id b)); pure (r', dTrans node p2, mt)
        _ => pure (SumElim l r u', node, mty)
    go mty (QuotElim f q) = do
      (q', p0, mq) <- go Nothing q
      (p1, sTy) <- shapedChild q mq isQuot p0
      mm <- motiveOf p1 mty sTy (QuotElim f q)
      let node = congOfD p1 (DQuotElim mm Nothing DReflx p1)
      case q' of
        Class a => do (r, p2, mt) <- go mty (substElem f (Ext Id a)); pure (r, dTrans node p2, mt)
        _ => pure (QuotElim f q', node, mty)
    go mty (Out u) = do
      (u', p0, mu) <- go Nothing u
      (p1, _) <- shapedChild u mu isNu p0
      case u' of
        Corec p a f x => do
          (r, p2, mt) <- go mty (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
          pure (r, dTrans (congOfD p1 (DOut p1)) p2, mt)
        _ => pure (Out u', congOfD p1 (DOut p1), mty)
    go mty (QElim sg k fs es w) = do
      (w', p1, _) <- go (Just (QSort sg k es)) w
      -- the node carries the signature β-JOINED: the kernel's side
      -- has it so (its join enters carriers), and a node's carrier
      -- must match the side's syntactically (A3)
      sgJ <- kJoinQSig sig sg
      dsgJ <- case p1 of
                DReflx => pure []
                _ => rdQSig sig ctx sgJ
      let node = congOfD p1 (DQElim dsgJ k Nothing [] (map (const DReflx) fs) (map (const DReflx) (toList es)) p1)
      case w' of
        QCtor sgW c theta => do
          sgWJ <- kJoinQSig sig sgW
          if sgWJ == sgJ
            then case qElimBetaRhs sg fs c theta of
                   Right rhs => do (r, p2, mt) <- go mty rhs; pure (r, dTrans node p2, mt)
                   Left _ => pure (QElim sg k fs es w', node, mty)
            else pure (QElim sg k fs es w', node, mty)
        _ => pure (QElim sg k fs es w', node, mty)
    go mty (Squash u) = do
      (u', p1, _) <- go (Just TopTy) u
      let node = congOfD p1 (DSquash p1)
      pure (case u' of
              Elem.EqTy _ _ _ => (u', node, mty)
              Squash _ => (u', node, mty)
              _ => (Squash u', node, mty))
    go mty e = pure (e, DReflx, mty)

  ||| A bare signature's pieces re-derived (a builder): an external
  ||| domain as a type under the external binders before it, an
  ||| external argument by INFERENCE (neutral in the emitted fragment —
  ||| as the elaborator elaborates them; the reader checks it at the
  ||| arity).
  export
  rdQSig : Sig -> Ctx -> QSig -> KM DQSig
  rdQSig sig ctx sg = traverse (rdQTy sig ctx) sg

  rdQTy : Sig -> Ctx -> QTy -> KM DQTy
  rdQTy sig ectx QU = pure DQU
  rdQTy sig ectx (QEl t) = DQEl <$> rdQTm sig ectx t
  rdQTy sig ectx (QPiExt a b) = do
    aD <- rdType sig ectx a
    DQPiExt aD <$> rdQTy sig (ectx :< a) b
  rdQTy sig ectx (QPiInd u b) = [| DQPiInd (rdQTm sig ectx u) (rdQTy sig ectx b) |]

  rdQTm : Sig -> Ctx -> QTm -> KM DQTm
  rdQTm sig ectx (QVar i) = pure (DQVar i)
  rdQTm sig ectx (QAppE f e) = [| DQAppE (rdQTm sig ectx f) (fst <$> rdInfer sig ectx e) |]
  rdQTm sig ectx (QAppI f a) = [| DQAppI (rdQTm sig ectx f) (rdQTm sig ectx a) |]
  rdQTm sig ectx (QEqC l r u) = [| DQEqC (rdQTm sig ectx l) (rdQTm sig ectx r) (rdQTm sig ectx u) |]

  ||| A bare polynomial's codes re-derived, each at 𝕌 under the
  ||| binders before it.
  export
  rdPoly : Sig -> Ctx -> Poly -> KM DPoly
  rdPoly sig ctx PHole = pure DPHole
  rdPoly sig ctx (PConst a) = DPConst <$> rdCheck sig ctx a UniverseTy
  rdPoly sig ctx (PProd f g) = [| DPProd (rdPoly sig ctx f) (rdPoly sig ctx g) |]
  rdPoly sig ctx (PSum f g) = [| DPSum (rdPoly sig ctx f) (rdPoly sig ctx g) |]
  rdPoly sig ctx (PSigma a f) = [| DPSigma (rdCheck sig ctx a UniverseTy) (rdPoly sig (ctx :< a) f) |]
  rdPoly sig ctx (PPi a f) = [| DPPi (rdCheck sig ctx a UniverseTy) (rdPoly sig (ctx :< a) f) |]

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
            pure (DAscribe d Nothing (Just pt))
          _ => kerr "re-derive: no shape at the type [\{show tyW}]"

  ||| A bare type re-derived as an annotation: β-joined first (an
  ||| annotation is a representative; a redex in it has no derivation
  ||| of its own).
  export
  rdTypeBare : Sig -> Ctx -> Ty -> KM Drv
  rdTypeBare sig ctx t = do
    t' <- kJoinTy sig t
    rdType sig ctx t'

  ||| A term re-derived in CHECKING mode at ty.
  export
  rdCheck : Sig -> Ctx -> Elem -> Ty -> KM Drv
  rdCheck = rdCheckAt

  ||| Checking mode, by the term's shape at the type's.
  rdCheckAt : Sig -> Ctx -> Elem -> Ty -> KM Drv
  rdCheckAt sig ctx e ty = case e of
    PiIntro f => rdShaped sig ctx ty (\t => case t of PiTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      DLam Nothing <$> rdCheck sig (ctx :< a) f b
    SigmaIntro u v => rdShaped sig ctx ty (\t => case t of SigmaTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      [| DPair (pure Nothing) (rdCheck sig ctx u a)
               (rdCheck sig ctx v (substTy b (Ext Id u))) |]
    Star =>
              -- a witness at an equality prop: reflexivity — the kernel
              -- decides (the prop exposed when a definition hides it)
              rdShaped sig ctx ty (\t => case t of Elem.EqTy _ _ _ => Just (); _ => Nothing) $ \_ =>
                pure (DStar Nothing DReflx)
    Inj1 a => rdShaped sig ctx ty (\t => case t of SumTy d _ => Just d; _ => Nothing) $ \dom =>
      DInj1 Nothing <$> rdCheck sig ctx a dom
    Inj2 a => rdShaped sig ctx ty (\t => case t of SumTy _ c => Just c; _ => Nothing) $ \cod =>
      DInj2 Nothing <$> rdCheck sig ctx a cod
    Class a => rdShaped sig ctx ty (\t => case t of QuotTy d _ => Just d; _ => Nothing) $ \dom =>
      DClass Nothing <$> rdCheck sig ctx a dom
    -- an eliminator with no motive payload, checked at a type: the
    -- constant-motive instance (§10.3's checking sugar)
    NatElim z st t => do
      dz <- rdCheck sig ctx z ty
      ds <- rdCheck sig (ctx :< NatTy :< substTy ty Wk) st (weakenTyN 2 ty)
      dt <- rdCheck sig ctx t NatTy
      pure (DNatElim Nothing dz ds dt)
    SumElim l r t => do
      (dt, tTy) <- rdInfer sig ctx t
      (tTyX, pt) <- rdExpose sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      dt' <- case pt of
               DReflx => pure dt
               _ => pure (DConv dt Nothing pt)
      case tTy' of
        SumTy a b => do
          dl <- rdCheck sig (ctx :< a) l (substTy ty Wk)
          dr <- rdCheck sig (ctx :< b) r (substTy ty Wk)
          pure (DSumElim Nothing dl dr dt')
        _ => kerr "re-derive: ⊎-elim of a non-⊎ scrutinee"
    QuotElim f q => do
      (dq, qTy) <- rdInfer sig ctx q
      (qTyX, pq) <- rdExpose sig ctx qTy
      qTy' <- kWhnfT sig qTyX
      dq' <- case pq of
               DReflx => pure dq
               _ => pure (DConv dq Nothing pq)
      case qTy' of
        QuotTy a _ => do
          df <- rdCheck sig (ctx :< a) f (substTy ty Wk)
          pure (DQuotElim Nothing Nothing df dq')
        _ => kerr "re-derive: quot-elim of a non-quotient"
    -- a QIIT eliminator at a type: the CONSTANT-MOTIVE instance (every
    -- sort's motive the type weakened into the sort's context), the
    -- coherences by β (A4)
    QElim sg k mths es w => do
      mots <- constMotives sig ctx sg ty
      let pointPs = qPositions QKPoint sg
      let eqPs = qPositions QKEq sg
      dms <- traverse (\(cj, m) => do
               mty <- liftQ (methodTy sg mots cj)
               rdCheck sig ctx m mty) (zip pointPs mths)
      sortE <- case qEntry sg k of
                 Just x => pure x
                 Nothing => kerr "re-derive: eliminator sort out of range"
      (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
      des <- rdTele sig ctx tel (toList es)
      dw <- rdCheck sig ctx w (QSort sg k es)
      dsg <- rdQSig sig ctx sg
      pure (DQElim dsg k Nothing (map (const DReflx) eqPs) dms des dw)
    Corec p aC f x => rdShaped sig ctx ty (\t => case t of NuTy pf => Just pf; _ => Nothing) $ \_ =>
      [| DCorec (rdPoly sig ctx p) (rdCheck sig ctx aC UniverseTy)
                (rdCheck sig (ctx :< aC) f (substTy (reflectPoly p aC) Wk))
                (rdCheck sig ctx x aC) |]
    ZeroElim t => DZeroElim Nothing <$> rdCheck sig ctx t ZeroTy
    Let a b => do
      (da, aTy) <- rdInfer sig ctx a
      let hyp = Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk)
      db <- rdCheck sig (ctx :< aTy :< hyp) b (weakenTyN 2 ty)
      pure (DLet da db)
    QCtor sgC c theta => rdShaped sig ctx ty (\t => case t of QSort _ _ _ => Just (); _ => Nothing) $ \_ => do
      sgC' <- kJoinQSig sig sgC
      entry <- case qEntry sgC' c of
                 Just x => pure x
                 Nothing => kerr "re-derive: constructor position out of range"
      (tel, _, _) <- liftQ (reflTel sgC' (qwAt c) entry)
      dsg <- rdQSig sig ctx sgC
      DCtor dsg c <$> rdTele sig ctx tel (toList theta)
    _ => do
      (d, t) <- rdInfer sig ctx e
      ok <- tyAgree sig ty t
      if ok then pure d else do
        -- a δ-apart spelling: the switch proof by the head exposures
        -- (a definition against its unfolding), else by δ-rounds on
        -- both sides (the proof library's deltaPrf)
        mp <- rdBridgeAny sig ctx t ty
        case mp of
          Just b => pure (DConv d Nothing b)
          Nothing => pure d

  ||| A proof of a ≐ b: by the two HEAD exposures first (each side's
  ||| head definition unfolded to the β-whnf shape — the usual δ-apart
  ||| spelling, a definition against its unfolding — the exposures
  ||| stated, so the proof runs), else by δ-rounds.
  export
  rdBridgeAny : Sig -> Ctx -> Elem -> Elem -> KM (Maybe Drv)
  rdBridgeAny sig ctx a b = do
    (aX, pa) <- rdExpose sig ctx a
    (bX, pb) <- rdExpose sig ctx b
    ok <- tyAgree sig bX aX
    if ok
      then pure (Just (dTrans pa (case pb of
                                    DReflx => DReflx
                                    _ => DSym pb)))
      else rdBridge sig a b

  ||| A proof of a ≐ b by δ-rounds on both sides: every definition
  ||| occurring unfolds at once, the sides β-join, repeat while new
  ||| names appear. Nothing when the sides never meet.
  export
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
  export
  rdInfer : Sig -> Ctx -> Elem -> KM (Drv, Ty)
  rdInfer sig ctx e =
    case e of
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
        NatIntro1 t => do d <- rdCheck sig ctx t NatTy; pure (DSuc d, NatTy)
        PiApp f a => do
          (df, fTy) <- scrut f
          fTy' <- kWhnfT sig fTy
          case fTy' of
            PiTy dom cod => do
              da <- rdCheck sig ctx a dom
              pure (DApp df da, substTy cod (Ext Id a))
            _ => kerr "re-derive: applying a non-function"
        SigmaElim1 t => do
          (dt, tTy) <- scrut t
          tTy' <- kWhnfT sig tTy
          case tTy' of
            SigmaTy a _ => pure (DProj1 dt, a)
            _ => kerr "re-derive: projecting a non-pair"
        SigmaElim2 t => do
          (dt, tTy) <- scrut t
          tTy' <- kWhnfT sig tTy
          case tTy' of
            SigmaTy _ b => pure (DProj2 dt, substTy b (Ext Id (SigmaElim1 t)))
            _ => kerr "re-derive: projecting a non-pair"
        Out t => do
          (dt, tTy) <- scrut t
          tTy' <- kWhnfT sig tTy
          case tTy' of
            NuTy f => pure (DOut dt, reflectPoly f (Elem.NuTy f))
            _ => kerr "re-derive: observing a non-ν element"
        Let a b => do
          (da, aTy) <- rdInfer sig ctx a
          let hyp = Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aTy Wk)
          (db, bTy) <- rdInfer sig (ctx :< aTy :< hyp) b
          pure (DLet da db, substTy bTy (Ext (Ext Id a) Star))
        NatElim z st t => do
          -- no motive (a stuck eliminator in head position, produced by
          -- normalization): the CONSTANT motive, read off the base
          -- case's inferred type (A1's inference-position twin)
            (_, zTy) <- rdInfer sig ctx z
            let mot = substTy zTy Wk
            dm <- rdTypeBare sig (ctx :< NatTy) mot
            dz <- rdCheck sig ctx z zTy
            ds <- rdCheck sig (ctx :< NatTy :< mot) st (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
            dt <- rdCheck sig ctx t NatTy
            pure (DNatElim (Just dm) dz ds dt, zTy)
        SumElim l r t => do
            -- constant motive from the left branch's type, when it does
            -- not mention the branch variable
            (dt, tTy) <- scrut t
            tTy' <- kWhnfT sig tTy
            case tTy' of
              SumTy a b => do
                -- the constant motive: the left branch's inferred type,
                -- or — the branch an intro form (a map from the sum
                -- to itself, unfolded) — the scrutinee's own type,
                -- the branches CHECKED there
                let at : Ty -> KM (Drv, Ty)
                    at base = do
                      let mot = substTy base Wk
                      dm <- rdTypeBare sig (ctx :< SumTy a b) mot
                      dl <- rdCheck sig (ctx :< a) l (substTy base Wk)
                      dr <- rdCheck sig (ctx :< b) r (substTy base Wk)
                      pure (DSumElim (Just dm) dl dr dt, base)
                kOrElse
                  (do (_, lTy) <- rdInfer sig (ctx :< a) l
                      case strengthenElem 0 lTy of
                        Just x => at x
                        Nothing => kerr "re-derive: ⊎-elim without a motive, branch type depends on the branch variable")
                  (at tTy)
              _ => kerr "re-derive: ⊎-elim of a non-⊎ scrutinee"
        QuotElim f q => do
            -- constant motive from the case's type; well-definedness
            -- only when the motive is a prop
            (dq, qTy) <- scrut q
            qTy' <- kWhnfT sig qTy
            case qTy' of
              QuotTy a rel => do
                -- the constant motive: the case's inferred type, or —
                -- the case an intro form (a map from the quotient to
                -- itself, unfolded: abs, neg) — the scrutinee's own
                -- type, the case CHECKED there
                let at : Ty -> KM (Drv, Ty)
                    at base = do
                      let mot = substTy base Wk
                      dm <- rdTypeBare sig (ctx :< QuotTy a rel) mot
                      df <- rdCheck sig (ctx :< a) f (substTy base Wk)
                      pure (DQuotElim (Just dm) Nothing df dq, base)
                kOrElse
                  (do (_, fTy) <- rdInfer sig (ctx :< a) f
                      case strengthenElem 0 fTy of
                        Just x => at x
                        Nothing => kerr "re-derive: quot-elim without a motive, case type depends on the representative")
                  (at qTy)
              _ => kerr "re-derive: quot-elim of a non-quotient"
        QSort sg k es => do
          sortE <- case qEntry sg k of
                     Just x => pure x
                     Nothing => kerr "re-derive: sort position out of range"
          (tel, _, _) <- liftQ (reflTel sg (qwAt k) sortE)
          ds <- rdTele sig ctx tel (toList es)
          dsg <- rdQSig sig ctx sg
          (_, small) <- dQSig sig ctx dsg
          pure (DSort dsg k ds, if small then UniverseTy else TopTy)
        QElim sg k mths es w => kerr "re-derive: QIIT eliminator without motives or coherences"
        Elem.ZeroTy => pure (DZeroTy, UniverseTy)
        Elem.OneTy => pure (DOneTy, UniverseTy)
        Elem.NatTy => pure (DNatTy, UniverseTy)
        Elem.PiTy a b => do
          da <- comp ctx a
          db <- comp (ctx :< a) b
          pure (DPi da db, UniverseTy)
        Elem.SigmaTy a b => do
          da <- comp ctx a
          db <- comp (ctx :< a) b
          pure (DSigma da db, UniverseTy)
        Elem.SumTy a b => do
          da <- comp ctx a
          db <- comp ctx b
          pure (DSum da db, UniverseTy)
        Elem.NuTy f => do df <- rdPoly sig ctx f; pure (DNu df, UniverseTy)
        QuotTy a r => do
          da <- comp ctx a
          dr <- rdCheck sig (ctx :< a :< substTy a Wk) r PropTy
          pure (DQuot da dr, UniverseTy)
        Squash t => do
          dt <- rdType sig ctx t
          pure (DSquash dt, PropTy)
        Elem.EqTy l r t => do
          dt <- rdType sig ctx t
          dl <- rdCheck sig ctx l t
          dr <- rdCheck sig ctx r t
          pure (DEq dl dr dt, PropTy)
        _ => kerr "re-derive: term not inferable [\{show e}]"
   where
    -- a code component in inference position: checked at 𝕌, ascribed
    comp : Ctx -> Elem -> KM Drv
    comp cx a = do
      d <- rdCheck sig cx a UniverseTy
      pure (DAscribe d (Just DUniverse) Nothing)

    refAt : Ctx -> Ty -> KM (Drv, Ty)
    refAt delta ty = do
      ds <- rdSpine sig ctx (toList delta) (case e of
                                              SigVar _ es => toList es
                                              _ => [])
      pure (DRef (case e of SigVar x _ => x; _ => "") ds,
            substTy ty (embed (case e of SigVar _ es => es; _ => [<])))
    -- a scrutinee, its type exposed by δ (proved) when the head's
    -- shape is hidden
    scrut : Elem -> KM (Drv, Ty)
    scrut t = do
      (dt, tTy) <- rdInfer sig ctx t
      let (dt1, tTy1) = (dt, tTy)
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
            _ => pure (DConv dt1 Nothing pt, tyX)

  ||| A type term re-derived as an annotation (formation, §8).
  export
  rdType : Sig -> Ctx -> Ty -> KM Drv
  rdType sig ctx t = case t of
    ZeroTy => pure DZeroTy
    OneTy => pure DOneTy
    NatTy => pure DNatTy
    UniverseTy => pure DUniverse
    PropTy => pure DProp
    TopTy => pure DTop
    PiTy a b => [| DPi (rdType sig ctx a) (rdType sig (ctx :< a) b) |]
    SigmaTy a b => [| DSigma (rdType sig ctx a) (rdType sig (ctx :< a) b) |]
    SumTy a b => [| DSum (rdType sig ctx a) (rdType sig ctx b) |]
    Elem.EqTy l r u => [| DEq (rdCheck sig ctx l u) (rdCheck sig ctx r u) (rdType sig ctx u) |]
    Squash u => DSquash <$> rdType sig ctx u
    QuotTy a r => [| DQuot (rdType sig ctx a) (rdCheck sig (ctx :< a :< substTy a Wk) r PropTy) |]
    NuTy f => DNu <$> rdPoly sig ctx f
    QSort _ _ _ => fst <$> rdInfer sig ctx t
    SigVar x es =>
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef delta _ _ TopTy) => DRef x <$> rdSpine sig ctx (toList delta) (toList es)
        Just (SigDecl delta _ TopTy) => DRef x <$> rdSpine sig ctx (toList delta) (toList es)
        _ => cumul
    _ => cumul
   where
    -- cumulativity: a code or a prop in type position, checked at 𝕌
    -- then at Ω (as kCheckTyK falls through), ascribed
    cumul : KM Drv
    cumul = do
      -- the classifier is the term's OWN type: inferred, exposed to
      -- its head (a definition may hide Ω or 𝕌), and read off — never
      -- tried
      (d, k) <- rdInfer sig ctx t
      (kX, pk) <- rdExpose sig ctx k
      kW <- kWhnfT sig kX
      (cls, dk) <- the (KM (Ty, Drv)) $ case kW of
              PropTy => pure (PropTy, DProp)
              UniverseTy => pure (UniverseTy, DUniverse)
              _ => kerr "re-derive: a type stands at neither Ω nor 𝕌 [\{show t} : \{show kW}]"
      let d' = case pk of
                 DReflx => d
                 _ => DConv d Nothing pk
      -- built AND read at the classifier: a re-derivation that would
      -- not read is a failure, never a derivation
      _ <- dCheck sig ctx d' cls
      pure (DAscribe d' (Just dk) Nothing)

  ||| A reference's spine at its telescope, each entry with its
  ||| skeleton child.
  export
  rdSpine : Sig -> Ctx -> List Ty -> List Elem -> KM (List Drv)
  rdSpine sig ctx delta es =
    if length es /= length delta then kerr "re-derive: substitution length mismatch"
      else go 0 es delta
   where
    go : Nat -> List Elem -> List Ty -> KM (List Drv)
    go i [] [] = pure []
    go i (e :: erest) (ty :: tyrest) = do
      let pre = take i es
      d <- rdCheck sig ctx e (substTy ty (embed (cast pre)))
      ds <- go (S i) erest tyrest
      pure (d :: ds)
    go _ _ _ = kerr "re-derive: substitution length mismatch"

  ||| A spine at a reflected telescope, each entry with its skeleton child.
  export
  rdTele : Sig -> Ctx -> List Ty -> List Elem -> KM (List Drv)
  rdTele sig ctx tel es =
    if length es /= length tel then kerr "re-derive: telescope spine length mismatch"
      else go 0 es
   where
    go : Nat -> List Elem -> KM (List Drv)
    go i [] = pure []
    go i (e :: rest) = do
      ty <- case telInst tel i es of
              Just t => pure t
              Nothing => kerr "re-derive: telescope entry type undetermined"
      d <- rdCheck sig ctx e ty
      ds <- go (S i) rest
      pure (d :: ds)

-- ===== Probes for the elaborator =====

||| Decidable smallness probe for callers outside the fuel monad
||| (the elaborator's data-item emitter): True iff every external Π
||| domain of the signature classifies at 𝕌 or at Ω — read off the
||| signature's derivations over the given ambient context.
export
kQSigSmallD : Sig -> Nat -> Ctx -> DQSig -> Bool
kQSigSmallD sig fuel ctx dsg =
  case runKM (dQSig sig ctx dsg) fuel of
    Right ((_, b), _) => b
    Left _ => False

||| A bare polynomial's derivation (a corec's, taken from the ν-type
||| it is checked at): re-derived, then READ.
export
kReDerivePoly : Sig -> Nat -> Ctx -> Poly -> Either KErr DPoly
kReDerivePoly sig fuel ctx p = map fst (runKM (do
  d <- rdPoly sig ctx p
  p' <- dPoly sig ctx d
  if p' == p then pure d else kerr "re-derive: the erasure differs from the polynomial") fuel)

||| Infer the type of a BARE core — the elaborator's capture-typing
||| source (unification's hole solutions): re-derived, then READ.
||| Nothing when the core is an intro form (not inferable) or fails
||| to type against this Σ; the caller treats absence as "no derived
||| equation", never as an error.
export
kInferBare : Sig -> Nat -> Ctx -> Elem -> Maybe Ty
kInferBare sig fuel ctx e =
  case runKM (do (d, _) <- rdInfer sig ctx e
                 (_, _, t) <- dInfer sig ctx d
                 pure t) fuel of
    Right (t, _) => Just t
    Left _ => Nothing

-- ===== Re-derivation as the elaborator's service (§10.6) =====
--
-- What the elaborator did not elaborate — a hole's solution, a
-- recovered motive, an inferred type standing as an annotation, a
-- data item's expansion — is DERIVED against its type by the
-- re-derivation above, run over the elaborator's own Σ (the
-- derivation is read afterwards against the kernel's, so nothing
-- here is trusted).

-- Each result is READ before it is handed out (a re-derivation that
-- would not read is a failure, never a derivation).

||| … with the classifier the derivation derives at (𝕌, Ω or 𝕍): what
||| the kernel will conclude about the type from this derivation.
export
kReDeriveTyK : Sig -> Nat -> Ctx -> Ty -> Either KErr (Drv, Ty)
kReDeriveTyK sig fuel ctx t = map fst (runKM (do
  d <- rdType sig ctx t
  (t', k) <- dTypeK sig ctx d
  if t' == t then pure (d, k) else kerr "re-derive: the erasure differs from the type") fuel)

export
kReDeriveTy : Sig -> Nat -> Ctx -> Ty -> Either KErr Drv
kReDeriveTy sig fuel ctx t = map fst (kReDeriveTyK sig fuel ctx t)


export
kReDeriveChk : Sig -> Nat -> Ctx -> Elem -> Ty -> Either KErr Drv
kReDeriveChk sig fuel ctx e ty = map fst (runKM (do
  d <- rdCheck sig ctx e ty
  (e', _) <- dCheck sig ctx d ty
  if e' == e then pure d else kerr "re-derive: the erasure differs from the term") fuel)

export
kReDeriveInf : Sig -> Nat -> Ctx -> Elem -> Either KErr (Drv, Ty)
kReDeriveInf sig fuel ctx e = map fst (runKM (do
  (d, ty) <- rdInfer sig ctx e
  (e', _, ty') <- dInfer sig ctx d
  if e' == e then pure (d, ty') else kerr "re-derive: the erasure differs from the term") fuel)

||| Is the type a PROPOSITION — the kernel's own question on the bare
||| type, or, failing that, on its re-derivation at Ω (a δ-apart
||| binder meets its bridge there): what the kernel will conclude
||| about the motive derivation the elaborator hands it.
export
kIsPropD : Sig -> Nat -> Ctx -> Ty -> Bool
kIsPropD sig fuel ctx t =
  (case runKM (kIsProp sig ctx t) fuel of
     Right (b, _) => b
     Left _ => False) ||
  (case runKM (do d <- rdType sig ctx t
                  (_, k) <- dTypeK sig ctx d
                  k' <- kWhnfT sig k
                  case k' of
                    PropTy => pure ()
                    _ => kerr "not a prop") fuel of
     Right _ => True
     Left _ => False)
