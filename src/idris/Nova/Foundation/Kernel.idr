module Nova.Foundation.Kernel

-- The TRUSTED side of the pipeline (docs/NovaPipeline.txt): certificate
-- replay for equality, over fuel-bounded beta.
--
-- Nothing here searches and nothing here chooses. The only ingredients:
--   * substitution (Nova.Foundation.Subst — the floor of every kernel);
--   * a fuel-bounded normalizer mirroring Foundation's ≜ rules clause
--     for clause (fuel exhaustion = REJECT, so every call terminates);
--   * mechanical replay of certificate steps: check a step's proof
--     element, derive the licensed equation from its type (reflection),
--     optionally take same-headed components (Foundation's injectivity
--     rules / derivable congruences), rewrite at the given path, and
--     compare normal forms;
--   * the type-directed finals: 𝟘/𝟙-Prop, quotient witnesses
--     (el-quot-eq), Π/Σ-η.
--
-- The discharge engine (untrusted) EMITS certificates; a discharge
-- counts only if it replays here. See Nova.Foundation.Elaboration.

import Data.List
import Data.SnocList

import Nova.Foundation.Syntax
import Nova.Foundation.Subst

%default covering

-- ===== Certificates =====

||| Component selectors: from a licensed equation between same-headed
||| terms, pass to a component equation. Justified by Foundation's
||| injectivity rules (codes) or derivable congruences (S via pred).
||| Binder components carry their instantiation (el-eq-subst).
public export
data Sel : Type where
  SelSuc : Sel                       -- S x ≐ S y ⇒ x ≐ y : ℕ
  SelDom : Sel                       -- (a₀→b₀) ≐ (a₁→b₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌 (also ⨯)
  SelCod : Elem -> Sel               -- ⇒ b₀[id,u] ≐ b₁[id,u] : 𝕌 (also ⨯)
  SelQDom : Sel                      -- (a₀/r₀) ≐ (a₁/r₁) : 𝕌 ⇒ a₀ ≐ a₁ : 𝕌
  SelQRel : Elem -> Elem -> Sel      -- ⇒ r₀[id,u,v] ≐ r₁[id,u,v] : 𝕌
  SelEqT : Sel                       -- (l₀≡r₀∈t₀) ≐ (l₁≡r₁∈t₁) : 𝕌 ⇒ t₀ ≐ t₁ : 𝕌
  SelEqL : Sel                       -- ⇒ l₀ ≐ l₁ : El t₁
  SelEqR : Sel                       -- ⇒ r₀ ≐ r₁ : El t₁

||| One replay step: at `path` (child indices; binders crossed are
||| counted by the walk itself) in the chosen side, rewrite by the
||| equation licensed by `proof` (a core element whose type must expose
||| an ≡-type), after applying `sels` and possibly flipping.
public export
record Step where
  constructor MkStep
  onLhs : Bool
  path : List Nat
  prf : Elem
  sels : List Sel
  flip : Bool

mutual
  public export
  data Final : Type where
    ||| compare beta-normal forms
    FBeta : Final
    ||| the equation's type normalizes to 𝟙 or 𝟘 (Foundation 𝟙/𝟘-Prop)
    FProp : Final
    ||| class a ≐ class b at A / R via the relation's shape:
    ||| R[id,a,b] ⇝ 𝟙 (witness ()) or ⇝ an ≡-type whose equation the
    ||| nested certificate establishes (witness Refl; el-quot-eq)
    FWitness : Maybe ECert -> Final
    ||| Π-η: compare applied to the fresh variable, under the domain
    FEtaPi : ECert -> Final
    ||| Σ-η: compare the projections
    FEtaSigma : ECert -> ECert -> Final

  public export
  record ECert where
    constructor MkECert
    steps : List Step
    final : Final

-- ===== Fuel monad =====

public export
KErr : Type
KErr = String

data KM : Type -> Type where
  MkKM : (Nat -> Either KErr (a, Nat)) -> KM a

runKM : KM a -> Nat -> Either KErr (a, Nat)
runKM (MkKM f) = f

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
    runKM (k x) n'

kerr : KErr -> KM a
kerr e = MkKM $ \_ => Left e

||| One ≜-contraction's worth of fuel.
burn : KM ()
burn = MkKM $ \n => case n of
  Z => Left "kernel: out of fuel"
  S m => Right ((), m)

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
  kElem sig Elem.ZeroTy = pure Elem.ZeroTy
  kElem sig Elem.OneTy = pure Elem.OneTy
  kElem sig Elem.NatTy = pure Elem.NatTy
  kElem sig (Elem.PiTy a b) = [| Elem.PiTy (kElem sig a) (kElem sig b) |]
  kElem sig (Elem.SigmaTy a b) = [| Elem.SigmaTy (kElem sig a) (kElem sig b) |]
  kElem sig (Elem.EqTy l r t) = [| Elem.EqTy (kElem sig l) (kElem sig r) (kElem sig t) |]
  kElem sig (QuotTy a r) = [| QuotTy (kElem sig a) (kElem sig r) |]
  kElem sig Refl = pure Refl
  kElem sig (SigVar x es) = do
    es' <- kSubNorm sig es
    case sigLookup x sig of
      Just (SigDef _ _ a _) => do burn; kElem sig (substElem a (embed es'))
      Just (SigTyDef _ _ _) => kerr "kernel: type definition '\{x}' used as a term"
      Nothing => kerr "kernel: unknown signature name '\{x}'"
  kElem sig (Class a) = Class <$> kElem sig a
  kElem sig (QuotElim f q) = do
    q' <- kElem sig q
    f' <- kElem sig f
    case q' of
      Class a => do burn; kElem sig (substElem f' (Ext Id a))
      _ => pure (QuotElim f' q')

  ||| Beta-normal form of a type (incl. El-decoding and type-level x-β).
  export
  kTy : Sig -> Ty -> KM Ty
  kTy sig Ty.ZeroTy = pure Ty.ZeroTy
  kTy sig Ty.OneTy = pure Ty.OneTy
  kTy sig Ty.NatTy = pure Ty.NatTy
  kTy sig Ty.UniverseTy = pure Ty.UniverseTy
  kTy sig (Ty.PiTy a b) = [| Ty.PiTy (kTy sig a) (kTy sig b) |]
  kTy sig (Ty.SigmaTy a b) = [| Ty.SigmaTy (kTy sig a) (kTy sig b) |]
  kTy sig (EqTy l r ty) = [| EqTy (kElem sig l) (kElem sig r) (kTy sig ty) |]
  kTy sig (El e) = do
    e' <- kElem sig e
    case e' of
      Elem.ZeroTy => do burn; pure Ty.ZeroTy
      Elem.OneTy => do burn; pure Ty.OneTy
      Elem.NatTy => do burn; pure Ty.NatTy
      Elem.PiTy a b => do burn; kTy sig (Ty.PiTy (El a) (El b))
      Elem.SigmaTy a b => do burn; kTy sig (Ty.SigmaTy (El a) (El b))
      Elem.EqTy l r t => do burn; kTy sig (EqTy l r (El t))
      QuotTy a r => do burn; kTy sig (Quotient (El a) (El r))
      _ => pure (El e')
  kTy sig (Quotient a r) = [| Quotient (kTy sig a) (kTy sig r) |]
  kTy sig (Ty.SigVar x es) = do
    es' <- kSubNorm sig es
    case sigLookup x sig of
      Just (SigTyDef _ _ a) => do burn; kTy sig (substTy a (embed es'))
      Just (SigDef _ _ _ _) => kerr "kernel: term definition '\{x}' used as a type"
      Nothing => kerr "kernel: unknown signature name '\{x}'"

-- ===== Path rewriting =====
--
-- Child indexing (binders in parentheses):
--   Elem: ZeroElim t→0 | NatIntro1 t→0 | NatElim z s t→0,1(2),2
--       | PiIntro f→0(1) | PiApp f e→0,1 | SigmaIntro a b→0,1
--       | SigmaElim1/2 t→0 | PiTyᶜ a b→0,1(1) | SigmaTyᶜ a b→0,1(1)
--       | EqTyᶜ l r t→0,1,2 | QuotTyᶜ a r→0,1(2) | SigVar es→0.. (left
--         to right) | Class a→0 | QuotElim f q→0(1),1
--   Ty:   PiTy a b→0,1(1) | SigmaTy a b→0,1(1) | EqTy l r t→0(e),1(e),2
--       | El e→0(e) | Quotient a r→0,1(2) | SigVar es→0.. (e)
--   (e) marks descent into an Elem child.

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
  pathE (i :: p) b f (Elem.EqTy l r t) =
    case i of
      0 => (\l' => Elem.EqTy l' r t) <$> pathE p b f l
      1 => (\r' => Elem.EqTy l r' t) <$> pathE p b f r
      2 => (\t' => Elem.EqTy l r t') <$> pathE p b f t
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
  pathE _ _ _ _ = Left "kernel: bad path"

  pathT : List Nat -> Nat -> (Nat -> Elem -> Either KErr Elem) -> Ty -> Either KErr Ty
  pathT [] b f t = Left "kernel: path must end at an element"
  pathT (i :: p) b f (Ty.PiTy a c) =
    case i of
      0 => (\a' => Ty.PiTy a' c) <$> pathT p b f a
      1 => (\c' => Ty.PiTy a c') <$> pathT p (1 + b) f c
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (Ty.SigmaTy a c) =
    case i of
      0 => (\a' => Ty.SigmaTy a' c) <$> pathT p b f a
      1 => (\c' => Ty.SigmaTy a c') <$> pathT p (1 + b) f c
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (EqTy l r t) =
    case i of
      0 => (\l' => EqTy l' r t) <$> pathE p b f l
      1 => (\r' => EqTy l r' t) <$> pathE p b f r
      2 => (\t' => EqTy l r t') <$> pathT p b f t
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (El e) = if i == 0 then El <$> pathE p b f e else Left "kernel: bad path"
  pathT (i :: p) b f (Quotient a r) =
    case i of
      0 => (\a' => Quotient a' r) <$> pathT p b f a
      1 => (\r' => Quotient a r') <$> pathT p (2 + b) f r
      _ => Left "kernel: bad path"
  pathT (i :: p) b f (Ty.SigVar x es) =
    case subNormAt i es of
      Just e => do e' <- pathE p b f e
                   case subNormSet i e' es of
                     Just es' => Right (Ty.SigVar x es')
                     Nothing => Left "kernel: bad path"
      Nothing => Left "kernel: bad path"
  pathT _ _ _ _ = Left "kernel: bad path"

liftEither : Either KErr a -> KM a
liftEither (Left e) = kerr e
liftEither (Right x) = pure x

-- ===== Proof-element inference =====
--
-- Certificate proofs are elimination spines: context variables,
-- signature references, applications and projections. Checking an
-- argument: Refl is accepted when the (normalized) expected ≡-type's
-- sides are beta-equal; anything else is inferred and its type compared
-- by beta. This tiny checker is all the "typing" replay needs.

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
    case sigLookup x sig of
      Just (SigDef delta _ _ ty) => do
        checkSubstP sig ctx (toList es) (toList delta)
        pure (substTy ty (embed es))
      _ => kerr "kernel: bad signature reference in proof"
  inferP sig ctx (PiApp f e) = do
    fTy <- inferP sig ctx f >>= kTy sig
    case fTy of
      Ty.PiTy a b => do checkP sig ctx e a; pure (substTy b (Ext Id e))
      _ => kerr "kernel: proof applies a non-function"
  inferP sig ctx (SigmaElim1 t) = do
    tTy <- inferP sig ctx t >>= kTy sig
    case tTy of
      Ty.SigmaTy a _ => pure a
      _ => kerr "kernel: proof projects a non-pair"
  inferP sig ctx (SigmaElim2 t) = do
    tTy <- inferP sig ctx t >>= kTy sig
    case tTy of
      Ty.SigmaTy _ b => pure (substTy b (Ext Id (SigmaElim1 t)))
      _ => kerr "kernel: proof projects a non-pair"
  inferP sig ctx OneIntro = pure Ty.OneTy
  inferP sig ctx NatIntro0 = pure Ty.NatTy
  inferP sig ctx (NatIntro1 t) = do checkP sig ctx t Ty.NatTy; pure Ty.NatTy
  inferP sig ctx e = kerr "kernel: proof element not inferable: \{show e}"

  checkP : Sig -> Ctx -> Elem -> Ty -> KM ()
  checkP sig ctx Refl ty = do
    ty' <- kTy sig ty
    case ty' of
      EqTy l r _ => do
        l' <- kElem sig l
        r' <- kElem sig r
        if l' == r' then pure () else kerr "kernel: Refl proof at unequal sides"
      _ => kerr "kernel: Refl proof at non-≡ type"
  checkP sig ctx (Class a) ty = do
    ty' <- kTy sig ty
    case ty' of
      Ty.Quotient dom _ => checkP sig ctx a dom
      _ => kerr "kernel: class proof at non-quotient type"
  checkP sig ctx (SigmaIntro u v) ty = do
    ty' <- kTy sig ty
    case ty' of
      Ty.SigmaTy a b => do checkP sig ctx u a; checkP sig ctx v (substTy b (Ext Id u))
      _ => kerr "kernel: pair proof at non-⨯ type"
  checkP sig ctx (PiIntro f) ty = do
    ty' <- kTy sig ty
    case ty' of
      Ty.PiTy a b => checkP sig (ctx :< a) f b
      _ => kerr "kernel: λ proof at non-Π type"
  checkP sig ctx (ZeroElim t) ty = checkP sig ctx t Ty.ZeroTy
  -- ℕ-elim with a CONSTANT motive: sufficient (an instance of ℕ-elim
  -- with motive T[↑]), and exactly what recursive arithmetic arguments
  -- (plus-trees after normalization) need
  checkP sig ctx (NatElim z st t) ty = do
    checkP sig ctx t Ty.NatTy
    checkP sig ctx z ty
    checkP sig (ctx :< Ty.NatTy :< ty) st (substTy (substTy ty Wk) Wk)
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

-- ===== Selector application =====

applySel : Sig -> (Elem, Elem, Ty) -> Sel -> KM (Elem, Elem, Ty)
applySel sig (l, r, _) sel = do
  l' <- kElem sig l
  r' <- kElem sig r
  case (sel, l', r') of
    (SelSuc, NatIntro1 x, NatIntro1 y) => pure (x, y, Ty.NatTy)
    (SelDom, Elem.PiTy a0 _, Elem.PiTy a1 _) => pure (a0, a1, Ty.UniverseTy)
    (SelDom, Elem.SigmaTy a0 _, Elem.SigmaTy a1 _) => pure (a0, a1, Ty.UniverseTy)
    (SelCod u, Elem.PiTy _ b0, Elem.PiTy _ b1) =>
      pure (substElem b0 (Ext Id u), substElem b1 (Ext Id u), Ty.UniverseTy)
    (SelCod u, Elem.SigmaTy _ b0, Elem.SigmaTy _ b1) =>
      pure (substElem b0 (Ext Id u), substElem b1 (Ext Id u), Ty.UniverseTy)
    (SelQDom, QuotTy a0 _, QuotTy a1 _) => pure (a0, a1, Ty.UniverseTy)
    (SelQRel u v, QuotTy _ r0, QuotTy _ r1) =>
      pure (substElem r0 (Ext (Ext Id u) v), substElem r1 (Ext (Ext Id u) v), Ty.UniverseTy)
    (SelEqT, Elem.EqTy _ _ t0, Elem.EqTy _ _ t1) => pure (t0, t1, Ty.UniverseTy)
    (SelEqL, Elem.EqTy l0 _ _, Elem.EqTy l1 _ t1) => pure (l0, l1, El t1)
    (SelEqR, Elem.EqTy _ r0 _, Elem.EqTy _ r1 t1) => pure (r0, r1, El t1)
    _ => kerr "kernel: selector does not apply"

||| The equation a step licenses (with its type): infer the proof,
||| expose the ≡-type, take components, orient.
licensed : Sig -> Ctx -> Step -> KM (Elem, Elem, Ty)
licensed sig ctx step = do
  pty <- inferP sig ctx step.prf >>= kTy sig
  case pty of
    EqTy l r t => do
      (l', r', t') <- foldlM (applySel sig) (l, r, t) step.sels
      lN <- kElem sig l'
      rN <- kElem sig r'
      pure (if step.flip then (rN, lN, t') else (lN, rN, t'))
    _ => kerr "kernel: step proof is not an equality"
 where
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
  childTyE sig ctx pexp (ZeroElim _) 0 = pure (Just Ty.ZeroTy)
  childTyE sig ctx pexp (NatIntro1 _) 0 = pure (Just Ty.NatTy)
  childTyE sig ctx pexp (NatElim _ _ _) 0 = pure pexp                    -- constant-motive reading
  childTyE sig ctx pexp (NatElim _ _ _) 1 = pure (map (weakenTyN 2) pexp)
  childTyE sig ctx pexp (NatElim _ _ _) 2 = pure (Just Ty.NatTy)
  childTyE sig ctx (Just pe) (PiIntro _) 0 = do
    t <- kTy sig pe
    case t of
      Ty.PiTy _ b => pure (Just b)
      _ => pure Nothing
  childTyE sig ctx pexp (PiApp f _) 0 = pure Nothing
  childTyE sig ctx pexp (PiApp f _) 1 = do
    mf <- inferNeK sig ctx f
    case mf of
      Just fTy => do
        t <- kTy sig fTy
        case t of
          Ty.PiTy a _ => pure (Just a)
          _ => pure Nothing
      Nothing => pure Nothing
  childTyE sig ctx (Just pe) (SigmaIntro _ _) 0 = do
    t <- kTy sig pe
    case t of
      Ty.SigmaTy a _ => pure (Just a)
      _ => pure Nothing
  childTyE sig ctx (Just pe) (SigmaIntro u _) 1 = do
    t <- kTy sig pe
    case t of
      Ty.SigmaTy _ b => pure (Just (substTy b (Ext Id u)))
      _ => pure Nothing
  childTyE sig ctx pexp (SigmaElim1 u) 0 = inferNeK sig ctx u
  childTyE sig ctx pexp (SigmaElim2 u) 0 = inferNeK sig ctx u
  childTyE sig ctx pexp (Elem.PiTy _ _) 0 = pure (Just Ty.UniverseTy)
  childTyE sig ctx pexp (Elem.PiTy _ _) 1 = pure (Just Ty.UniverseTy)
  childTyE sig ctx pexp (Elem.SigmaTy _ _) 0 = pure (Just Ty.UniverseTy)
  childTyE sig ctx pexp (Elem.SigmaTy _ _) 1 = pure (Just Ty.UniverseTy)
  childTyE sig ctx pexp (Elem.EqTy _ _ t) 0 = pure (Just (El t))
  childTyE sig ctx pexp (Elem.EqTy _ _ t) 1 = pure (Just (El t))
  childTyE sig ctx pexp (Elem.EqTy _ _ _) 2 = pure (Just Ty.UniverseTy)
  childTyE sig ctx pexp (QuotTy _ _) 0 = pure (Just Ty.UniverseTy)
  childTyE sig ctx pexp (QuotTy _ _) 1 = pure (Just Ty.UniverseTy)
  childTyE sig ctx pexp (SigVar x es) i =
    case sigLookup x sig of
      Just (SigDef delta _ _ _) =>
        case getAt i (toList delta) of
          Just entryTy =>
            pure (Just (substTy entryTy (embed (cast (take i (toList es))))))
          Nothing => pure Nothing
      _ => pure Nothing
  childTyE sig ctx (Just pe) (Class _) 0 = do
    t <- kTy sig pe
    case t of
      Ty.Quotient dom _ => pure (Just dom)
      _ => pure Nothing
  childTyE sig ctx pexp (QuotElim _ q) 1 = inferNeK sig ctx q
  childTyE sig ctx pexp _ _ = pure Nothing

  ||| Neutral inference inside the kernel (spines only).
  inferNeK : Sig -> Ctx -> Elem -> KM (Maybe Ty)
  inferNeK sig ctx (CtxVar i) = pure (ctxLookup ctx i)
  inferNeK sig ctx (PiApp f e) = do
    mf <- inferNeK sig ctx f
    case mf of
      Just fTy => do
        t <- kTy sig fTy
        case t of
          Ty.PiTy _ b => pure (Just (substTy b (Ext Id e)))
          _ => pure Nothing
      Nothing => pure Nothing
  inferNeK sig ctx (SigmaElim1 t) = do
    mt <- inferNeK sig ctx t
    case mt of
      Just tTy => do
        t' <- kTy sig tTy
        case t' of
          Ty.SigmaTy a _ => pure (Just a)
          _ => pure Nothing
      Nothing => pure Nothing
  inferNeK sig ctx (SigVar x es) =
    case sigLookup x sig of
      Just (SigDef _ _ _ ty) => pure (Just (substTy ty (embed es)))
      _ => pure Nothing
  inferNeK sig ctx _ = pure Nothing

||| Typed descent: rewrite at the path, checking the licensed type
||| against each position's expected type.
goE : Sig -> Ctx -> (Elem, Elem, Ty) -> List Nat -> Nat -> Maybe Ty -> Elem -> KM Elem
goE sig ctx lic@(le, re, ltyN) [] b mexp u = do
  case mexp of
    Nothing => kerr "kernel: step at a type-undetermined position"
    Just expTy => do
      expN <- kTy sig expTy
      if expN /= weakenTyN b ltyN
        then kerr "kernel: step type does not match the position"
        else if u == weakenN b le
          then pure (weakenN b re)
          else kerr "kernel: step does not match the subterm"
goE sig ctx lic (i :: p) b mexp u = do
  childTy <- childTyE sig ctx mexp u i
  case Just () of
    _ =>
      case (u, i) of
        (ZeroElim t', 0) => ZeroElim <$> goE sig ctx lic p b childTy t'
        (NatIntro1 t', 0) => NatIntro1 <$> goE sig ctx lic p b childTy t'
        (NatElim z st t', 0) => (\z' => NatElim z' st t') <$> goE sig ctx lic p b childTy z
        (NatElim z st t', 1) => (\s' => NatElim z s' t') <$> goE sig ctx lic p (2 + b) childTy st
        (NatElim z st t', 2) => (\t'' => NatElim z st t'') <$> goE sig ctx lic p b childTy t'
        (PiIntro f, 0) => PiIntro <$> goE sig ctx lic p (1 + b) childTy f
        (PiApp f e, 0) => (\f' => PiApp f' e) <$> goE sig ctx lic p b childTy f
        (PiApp f e, 1) => PiApp f <$> goE sig ctx lic p b childTy e
        (SigmaElim1 t', 0) => SigmaElim1 <$> goE sig ctx lic p b childTy t'
        (SigmaElim2 t', 0) => SigmaElim2 <$> goE sig ctx lic p b childTy t'
        (SigmaIntro x y, 0) => (\x' => SigmaIntro x' y) <$> goE sig ctx lic p b childTy x
        (SigmaIntro x y, 1) => SigmaIntro x <$> goE sig ctx lic p b childTy y
        (Elem.PiTy a c, 0) => (\a' => Elem.PiTy a' c) <$> goE sig ctx lic p b childTy a
        (Elem.PiTy a c, 1) => Elem.PiTy a <$> goE sig ctx lic p (1 + b) childTy c
        (Elem.SigmaTy a c, 0) => (\a' => Elem.SigmaTy a' c) <$> goE sig ctx lic p b childTy a
        (Elem.SigmaTy a c, 1) => Elem.SigmaTy a <$> goE sig ctx lic p (1 + b) childTy c
        (Elem.EqTy l r t', 0) => (\l' => Elem.EqTy l' r t') <$> goE sig ctx lic p b childTy l
        (Elem.EqTy l r t', 1) => (\r' => Elem.EqTy l r' t') <$> goE sig ctx lic p b childTy r
        (Elem.EqTy l r t', 2) => Elem.EqTy l r <$> goE sig ctx lic p b childTy t'
        (QuotTy a r, 0) => (\a' => QuotTy a' r) <$> goE sig ctx lic p b childTy a
        (QuotTy a r, 1) => QuotTy a <$> goE sig ctx lic p (2 + b) childTy r
        (SigVar x es, _) =>
          case subNormAt i es of
            Just e => do
              e' <- goE sig ctx lic p b childTy e
              case subNormSet i e' es of
                Just es' => pure (SigVar x es')
                Nothing => kerr "kernel: bad path"
            Nothing => kerr "kernel: bad path"
        (Class a, 0) => Class <$> goE sig ctx lic p b childTy a
        (QuotElim f q, 0) => (\f' => QuotElim f' q) <$> goE sig ctx lic p (1 + b) childTy f
        (QuotElim f q, 1) => QuotElim f <$> goE sig ctx lic p b childTy q
        _ => kerr "kernel: bad or type-undetermined path"

||| Apply one step to an element known (by the replay invariant) to be
||| well-typed at tyRoot: descend the path computing expected types,
||| verify the licensed equation's type in situ, rewrite.
stepElem : Sig -> Ctx -> Step -> Ty -> Elem -> KM Elem
stepElem sig ctx step tyRoot t = do
  (le, re, lty) <- licensed sig ctx step
  ltyN <- kTy sig lty
  goE sig ctx (le, re, ltyN) step.path 0 (Just tyRoot) t

||| Steps inside types: type positions have no element type; every
||| element child's type is structurally determined.
stepTy : Sig -> Ctx -> Step -> Ty -> KM Ty
stepTy sig ctx step t = do
  (le, re, lty) <- licensed sig ctx step
  ltyN <- kTy sig lty
  goT (le, re, ltyN) step.path 0 t
 where
  goT : (Elem, Elem, Ty) -> List Nat -> Nat -> Ty -> KM Ty
  goT lic [] b u = kerr "kernel: type-path must end at an element"
  goT lic (i :: p) b (Ty.PiTy a c) =
    case i of
      0 => (\a' => Ty.PiTy a' c) <$> goT lic p b a
      1 => Ty.PiTy a <$> goT lic p (1 + b) c
      _ => kerr "kernel: bad path"
  goT lic (i :: p) b (Ty.SigmaTy a c) =
    case i of
      0 => (\a' => Ty.SigmaTy a' c) <$> goT lic p b a
      1 => Ty.SigmaTy a <$> goT lic p (1 + b) c
      _ => kerr "kernel: bad path"
  goT lic (i :: p) b (EqTy l r t') =
    case i of
      0 => (\l' => EqTy l' r t') <$> goE sig ctx lic p b (Just t') l
      1 => (\r' => EqTy l r' t') <$> goE sig ctx lic p b (Just t') r
      2 => EqTy l r <$> goT lic p b t'
      _ => kerr "kernel: bad path"
  goT lic (i :: p) b (El e) =
    if i == 0 then El <$> goE sig ctx lic p b (Just Ty.UniverseTy) e
    else kerr "kernel: bad path"
  goT lic (i :: p) b (Quotient a r) =
    case i of
      0 => (\a' => Quotient a' r) <$> goT lic p b a
      1 => Quotient a <$> goT lic p (2 + b) r
      _ => kerr "kernel: bad path"
  goT lic (i :: p) b (Ty.SigVar x es) =
    case sigLookup x sig of
      Just (SigTyDef delta _ _) =>
        case (subNormAt i es, getAt i (toList delta)) of
          (Just e, Just entryTy) => do
            e' <- goE sig ctx lic p b (Just (substTy entryTy (embed (cast (take i (toList es)))))) e
            case subNormSet i e' es of
              Just es' => pure (Ty.SigVar x es')
              Nothing => kerr "kernel: bad path"
          _ => kerr "kernel: bad path"
      _ => kerr "kernel: bad path"
  goT lic _ _ _ = kerr "kernel: bad path"

-- ===== Replay =====

mutual
  ||| Replay a certificate for the element equation Γ ⊢ l ≐ r : ty.
  export
  kEqElem : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> KM ()
  kEqElem sig ctx cert l r ty = do
    l0 <- kElem sig l
    r0 <- kElem sig r
    (l1, r1) <- goSteps cert.steps l0 r0
    case cert.final of
      FBeta =>
        if l1 == r1 then pure () else kerr "kernel: sides differ after replay"
      FProp => do
        ty' <- kTy sig ty
        case ty' of
          Ty.OneTy => pure ()
          Ty.ZeroTy => pure ()
          _ => kerr "kernel: Prop final at a non-Prop type"
      FWitness mc => do
        ty' <- kTy sig ty
        case (l1, r1, ty') of
          (Class a, Class b, Ty.Quotient dom rel) => do
            relInst <- kTy sig (substTy rel (Ext (Ext Id a) b))
            case (relInst, mc) of
              (Ty.OneTy, _) => pure ()
              (EqTy wl wr wt, Just c) => kEqElem sig ctx c wl wr wt
              _ => kerr "kernel: witness final does not apply"
          _ => kerr "kernel: witness final at a non-class equation"
      FEtaPi c => do
        ty' <- kTy sig ty
        case ty' of
          Ty.PiTy dom cod =>
            kEqElem sig (ctx :< dom) c
              (PiApp (substElem l1 Wk) (CtxVar 0))
              (PiApp (substElem r1 Wk) (CtxVar 0))
              cod
          _ => kerr "kernel: Π-η final at a non-Π type"
      FEtaSigma c1 c2 => do
        ty' <- kTy sig ty
        case ty' of
          Ty.SigmaTy dom cod => do
            kEqElem sig ctx c1 (SigmaElim1 l1) (SigmaElim1 r1) dom
            kEqElem sig ctx c2 (SigmaElim2 l1) (SigmaElim2 r1)
              (substTy cod (Ext Id (SigmaElim1 l1)))
          _ => kerr "kernel: Σ-η final at a non-Σ type"
   where
    goSteps : List Step -> Elem -> Elem -> KM (Elem, Elem)
    goSteps [] l' r' = pure (l', r')
    goSteps (s :: rest) l' r' =
      if s.onLhs
        then do l'' <- stepElem sig ctx s ty l' >>= kElem sig
                goSteps rest l'' r'
        else do r'' <- stepElem sig ctx s ty r' >>= kElem sig
                goSteps rest l' r''

  ||| Replay a certificate for the type equation Γ ⊢ A ≐ B.
  export
  kEqTy : Sig -> Ctx -> ECert -> Ty -> Ty -> KM ()
  kEqTy sig ctx cert a b = do
    a0 <- kTy sig a
    b0 <- kTy sig b
    (a1, b1) <- goSteps cert.steps a0 b0
    case cert.final of
      FBeta => if a1 == b1 then pure () else kerr "kernel: types differ after replay"
      _ => kerr "kernel: unsupported final for a type equation"
   where
    goSteps : List Step -> Ty -> Ty -> KM (Ty, Ty)
    goSteps [] a' b' = pure (a', b')
    goSteps (s :: rest) a' b' =
      if s.onLhs
        then do a'' <- stepTy sig ctx s a' >>= kTy sig
                goSteps rest a'' b'
        else do b'' <- stepTy sig ctx s b' >>= kTy sig
                goSteps rest a' b''

-- ===== Entry points =====

export
kCheckEqElem : Sig -> Ctx -> Nat -> ECert -> Elem -> Elem -> Ty -> Either KErr ()
kCheckEqElem sig ctx fuel cert l r ty =
  map fst (runKM (kEqElem sig ctx cert l r ty) fuel)

export
kCheckEqTy : Sig -> Ctx -> Nat -> ECert -> Ty -> Ty -> Either KErr ()
kCheckEqTy sig ctx fuel cert a b =
  map fst (runKM (kEqTy sig ctx cert a b) fuel)
