module Nova.Elaboration.Proof

-- The discharge ENGINE's proof library: how the engine writes
-- DERIVATIONS (Nova.Kernel.Derivation, docs/NovaKernel.txt §10) as
-- it searches.
--
-- The engine finds equations by rewriting and emits a derivation for
-- what it did AS it does it: a licence applied at a position becomes
-- its leaf inside the node skeleton of the position (wrapAt, typed as
-- the kernel's nodes type their children), a δ-round becomes a δ-all
-- leaf, a type-directed closing step becomes its leaf, and the
-- rewritten forms meet by transitivity. Nothing here is trusted: the
-- kernel reads the derivation and nothing else. A leaf is a
-- DERIVATION: a typed neutral is its own derivation (re-derived from
-- the term against Σ — the kernel module's rdInfer), an argument at a
-- domain is derived there (rdCheck), an exposure is the kernel's
-- (rdExposeW under the site's whitelist). The helpers run in the
-- kernel's monad because the skeleton around a leaf needs the
-- kernel's own typing of the position (a head's declared type opened
-- to the shape the next node needs); the engine, which is pure, runs
-- them through `runP`.

import Data.List
import Data.Maybe
import Data.SnocList
import Control.Monad.State

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT
import Nova.Kernel
import Nova.Kernel.Derivation
import Nova.Profile

%default covering

listAt : Nat -> List a -> Maybe a
listAt Z (x :: _) = Just x
listAt (S n) (_ :: xs) = listAt n xs
listAt _ [] = Nothing

listSet : Nat -> a -> List a -> Maybe (List a)
listSet Z y (_ :: xs) = Just (y :: xs)
listSet (S n) y (x :: xs) = map (x ::) (listSet n y xs)
listSet _ _ [] = Nothing

||| The skeleton (re-derivation reads no payloads from the engine).

||| A spine with one child rewritten: the derivations (reflexivity at
||| every other entry) and the new spine.
spineWrap : Nat -> SubNorm -> (Elem -> KM (Drv, Elem)) -> KM (List Drv, SubNorm)
spineWrap i es go = do
  let xs = toList es
  e <- case listAt i xs of
         Just e => pure e
         Nothing => kerr "proof: bad path (spine index)"
  (q, e') <- go e
  xs' <- case listSet i e' xs of
           Just v => pure v
           Nothing => kerr "proof: bad path (spine index)"
  pure (map (\j => if j == i then q else DReflx) (indices xs), cast xs')
 where
  indices : List a -> List Nat
  indices ys = go' 0 ys
   where
    go' : Nat -> List a -> List Nat
    go' _ [] = []
    go' k (_ :: rest) = k :: go' (S k) rest

||| A derivation under the EXPOSURE of the type it is read at: the
||| ascription whose target the proof produces run from the position's
||| type (nothing when β alone reached the shape).
export
convWrap : Drv -> Drv -> Drv
convWrap DReflx d = d
convWrap pt d = DAscribe d Nothing (Just pt)

||| The kernel's β-only type agreement (join, or cumulativity).
tyAgreeB : Sig -> Ty -> Ty -> KM Bool
tyAgreeB sig a b = do
  aN <- kJoinTy sig a
  bN <- kJoinTy sig b
  pure (aN == bN || (aN == TopTy && (bN == UniverseTy || bN == PropTy)))

||| The embedded Nova pieces of a carried signature.
export
piecesOf : QSig -> List Elem
piecesOf g = fst (runState [] (traverseQSig (\e => do modify (e ::); pure e) g))

||| A proof of a ≐ b (at 𝕍, or any type) by δ: the head exposures of
||| the two sides first (a definition against its unfolding, the
||| exposures stated), else δ-rounds on both sides — the engine's
||| widening δβ join as a derivation. Nothing when the sides never
||| meet.
export
deltaPrf : Sig -> Ctx -> Elem -> Elem -> KM (Maybe Drv)
deltaPrf = rdBridgeAny

||| Is the term a SPINE — typable from its head's declared type by
||| eliminations alone?
isSpine : Elem -> Bool
isSpine (CtxVar _) = True
isSpine (SigVar _ _) = True
isSpine (PiApp f _) = isSpine f
isSpine (SigmaElim1 t) = isSpine t
isSpine (SigmaElim2 t) = isSpine t
isSpine (Out t) = isSpine t
isSpine NatIntro0 = True
isSpine OneIntro = True
isSpine Elem.ZeroTy = True
isSpine Elem.OneTy = True
isSpine Elem.NatTy = True
isSpine _ = False

||| Head exposure under a whitelist, its δ RECORDED: the term taken to
||| its β-whnf with every licensed definition unfolded on the way to
||| the head as a δ leaf inside the node of its position — and the
||| derivation of t ≐ exposed (reflexivity when β alone reached it,
||| which the kernel's own whnf does).
export
exposeKW : (String -> Bool) -> Sig -> Ctx -> Elem -> KM (Elem, Drv)
exposeKW = rdExposeW

||| … from a known type of the term.
export
exposeKWT : (String -> Bool) -> Sig -> Ctx -> Maybe Ty -> Elem -> KM (Elem, Drv)
exposeKWT = rdExposeWT

||| Head exposure with every definition allowed (the kernel-facing
||| helpers below expose freely: a shape a node needs is reached).
export
exposeK : Sig -> Ctx -> Elem -> KM (Elem, Drv)
exposeK = rdExpose

||| A TYPED NEUTRAL (any term in inference position): its derivation,
||| re-derived against Σ — elimination nodes over the head, each
||| scrutinee under the exposure that shows the shape the next
||| elimination needs — and the type it states.
export
elemToDrv : Sig -> Ctx -> Elem -> KM (Drv, Ty)
elemToDrv sig ctx e = rdInfer sig ctx e

||| An ARGUMENT at the domain the head demands: derived in checking
||| mode there (a spine states its type and arrives converted when
||| spelled otherwise; an intro form is checked at the domain's parts).
export
argDrv : Sig -> Ctx -> Elem -> Ty -> KM Drv
argDrv sig ctx a dom = rdCheck sig ctx a dom

||| The spine of a path leaf stated entrywise at the reflected
||| telescope.
pathArgs : Sig -> Ctx -> QSig -> Nat -> SubNorm -> KM (List Drv)
pathArgs sig ctx sg k th = do
  sg' <- kJoinQSig sig sg
  entry <- case qEntry sg' k of
             Just e => pure e
             Nothing => kerr "proof: path leaf entry out of range"
  (tel, _, _) <- liftQ (reflTel sg' (qwAt k) entry)
  rdTele sig ctx tel (toList th)

||| The head of an elimination as a derivation child: reflexivity when
||| its declared type already shows the shape the node needs (β — the
||| reader inverts it from the side), else the typed neutral under the
||| exposure that shows it. Returns the (exposed) type as well.
export
headD : Sig -> Ctx -> Elem -> (Ty -> Bool) -> KM (Maybe Ty, Drv)
headD sig ctx hd want = do
  hTy <- inferHead sig ctx hd
  case hTy of
    Nothing =>
      if isSpine hd
        then do (d, t) <- elemToDrv sig ctx hd; shapedD d t
        else pure (Nothing, DReflx)
    Just t => do
      t' <- kWhnfT sig t
      if want t' then pure (Just t, DReflx)
        else do (d, t0) <- elemToDrv sig ctx hd; shapedD d t0
 where
  shapedD : Drv -> Ty -> KM (Maybe Ty, Drv)
  shapedD d t = do
    (tX, pt) <- rdExpose sig ctx t
    pure (Just tX, case pt of
                     DReflx => d
                     _ => DConv d Nothing pt)

isPiTy, isSigmaTy, isNuTy, isSumTy, isQuotTy : Ty -> Bool
isPiTy (PiTy _ _) = True
isPiTy _ = False
isSigmaTy (SigmaTy _ _) = True
isSigmaTy _ = False
isNuTy (NuTy _) = True
isNuTy _ = False
isSumTy (SumTy _ _) = True
isSumTy _ = False
isQuotTy (QuotTy _ _) = True
isQuotTy _ = False

||| A rewritten HEAD or SCRUTINEE child under the exposure of its
||| declared type when a definition hides the shape its node needs
||| (the reader types the child by the exposure run from what it
||| states or inverts to).
export
exposedChild : Sig -> Ctx -> Maybe Ty -> (Ty -> Bool) -> Drv -> KM Drv
exposedChild sig ctx Nothing want q = pure q
exposedChild sig ctx (Just t) want q = do
  t' <- kWhnfT sig t
  if want t' then pure q else do
    (tX, pt) <- rdExpose sig ctx t
    tW <- kWhnfT sig tX
    pure (case pt of
            DReflx => q
            _ => if want tW then DConv q Nothing pt else q)

||| The classifier a shared former's components sit at, as the kernel
||| reads it (compClassifier).
classifierOf : Sig -> Maybe Ty -> KM Ty
classifierOf sig mty = compClassifier sig mty

||| The domain of a function's type, as the kernel's app node reads it
||| (β-whnf only).
domOf : Sig -> Maybe Ty -> KM (Maybe Ty)
domOf sig Nothing = pure Nothing
domOf sig (Just t) = do
  t' <- kWhnfT sig t
  pure (case t' of
          PiTy dom _ => Just dom
          _ => Nothing)

||| The node skeleton along a path, TYPED: the position's context and
||| expected type are computed as the kernel's nodes compute them (the
||| type flowing down, a neutral head's inferred type, the
||| constant-motive reading), and a node that needs a shape the type
||| only exposes by δ is wrapped in the ascription that exposes it.
||| `leaf` acts at the path's end with the context, the type (Nothing:
||| undetermined), the binders crossed and the subterm there, giving
||| the leaf's derivation and the replacement; every sibling is
||| reflexivity. Child indexing as the engine's rewriter counts it.
export
wrapAt : Sig -> Ctx -> Maybe Ty -> Nat -> Elem -> List Nat
      -> (Ctx -> Maybe Ty -> Nat -> Elem -> KM (Drv, Elem)) -> KM (Drv, Elem)
||| The motive of an eliminator node written in a HEAD position (no
||| type flows down: the scrutinee of another elimination, the
||| function of an application): the constant motive its inferred
||| type determines, from the re-derivation of the eliminator. At a
||| checked position the kernel reads the constant motive itself and
||| the node carries none.
elimMotive : Sig -> Ctx -> Maybe Ty -> Elem -> KM (Maybe Drv)
elimMotive _ _ (Just _) _ = pure Nothing
elimMotive sig ctx Nothing u =
  kOrElse (do (d, _) <- rdInfer sig ctx u
              pure (case d of
                      DNatElim m _ _ _ => m
                      DSumElim m _ _ _ => m
                      DQuotElim m _ _ _ => m
                      _ => Nothing))
          (pure Nothing)

wrapAt sig ctx mty b u [] leaf = leaf ctx mty b u
wrapAt sig ctx mty b u (i :: p) leaf = do
  let go : Ctx -> Maybe Ty -> Nat -> Elem -> KM (Drv, Elem)
      go ctx' mty' b' x = wrapAt sig ctx' mty' b' x p leaf
  -- a shape the node needs from the type flowing down, with the
  -- exposure that shows it
  let shaped : String -> (Ty -> Maybe a) -> ((a, Drv -> Drv) -> KM (Drv, Elem)) -> KM (Drv, Elem)
      shaped what pick k = do
        ty <- case mty of
                Just t => pure t
                Nothing => kerr "proof: \{what} at a type-undetermined position"
        (tyX, pt) <- rdExpose sig ctx ty
        tyW <- kWhnfT sig tyX
        case pick tyW of
          Just parts => k (parts, convWrap pt)
          Nothing => kerr "proof: \{what} at a type without the shape [\{show tyW}]"
  case (u, i) of
    (ZeroElim t, 0) => (\(q, t') => (DZeroElim Nothing q, ZeroElim t')) <$> go ctx (Just ZeroTy) b t
    (NatIntro1 t, 0) => (\(q, t') => (DSuc q, NatIntro1 t')) <$> go ctx (Just NatTy) b t
    (NatElim z s t, 0) => (\(q, z') => (DNatElim Nothing q DReflx DReflx, NatElim z' s t)) <$> go ctx mty b z
    (NatElim z s t, 1) =>
      (\(q, s') => (DNatElim Nothing DReflx q DReflx, NatElim z s' t))
        <$> go (ctx :< NatTy :< fromMaybe TopTy (map (\x => substTy x Wk) mty)) (map (\x => substTy x (wkN 2)) mty) (2 + b) s
    (NatElim z s t, 2) => do
      mm <- elimMotive sig ctx mty u
      (\(q, t') => (DNatElim mm DReflx DReflx q, NatElim z s t')) <$> go ctx (Just NatTy) b t
    (PiIntro f, 0) =>
      shaped "λ-congruence" (\t => case t of PiTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, f') => (conv (DLam Nothing q), PiIntro f')) <$> go (ctx :< a) (Just c) (1 + b) f
    (PiApp f e, 0) => do
      fTy <- inferHead sig ctx f
      (q, f') <- go ctx fTy b f
      q' <- exposedChild sig ctx fTy isPiTy q
      pure (DApp q' DReflx, PiApp f' e)
    (PiApp f e, 1) => do
      (fTy, pf) <- headD sig ctx f isPiTy
      aTy <- domOf sig fTy
      (\(q, e') => (DApp pf q, PiApp f e')) <$> go ctx aTy b e
    (SigmaElim1 t, 0) => do
      tTy <- inferHead sig ctx t
      (q, t') <- go ctx tTy b t
      q' <- exposedChild sig ctx tTy isSigmaTy q
      pure (DProj1 q', SigmaElim1 t')
    (SigmaElim2 t, 0) => do
      tTy <- inferHead sig ctx t
      (q, t') <- go ctx tTy b t
      q' <- exposedChild sig ctx tTy isSigmaTy q
      pure (DProj2 q', SigmaElim2 t')
    (Inj1 t, 0) =>
      shaped "inj₁ congruence" (\ty => case ty of SumTy a _ => Just a; _ => Nothing) $ \(a, conv) =>
        (\(q, t') => (conv (DInj1 Nothing q), Inj1 t')) <$> go ctx (Just a) b t
    (Inj2 t, 0) =>
      shaped "inj₂ congruence" (\ty => case ty of SumTy _ c => Just c; _ => Nothing) $ \(c, conv) =>
        (\(q, t') => (conv (DInj2 Nothing q), Inj2 t')) <$> go ctx (Just c) b t
    (SumElim l r t, 0) => do
      ((a, _), pt) <- sumParts t
      (\(q, l') => (DSumElim Nothing q DReflx pt, SumElim l' r t)) <$> go (ctx :< a) (map (\x => substTy x Wk) mty) (1 + b) l
    (SumElim l r t, 1) => do
      ((_, c), pt) <- sumParts t
      (\(q, r') => (DSumElim Nothing DReflx q pt, SumElim l r' t)) <$> go (ctx :< c) (map (\x => substTy x Wk) mty) (1 + b) r
    (SumElim l r t, 2) => do
      tTy <- inferHead sig ctx t
      (q, t') <- go ctx tTy b t
      q' <- exposedChild sig ctx tTy isSumTy q
      mm <- elimMotive sig ctx mty u
      pure (DSumElim mm DReflx DReflx q', SumElim l r t')
    (SigmaIntro x y, 0) =>
      shaped "pair congruence" (\ty => case ty of SigmaTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, x') => (conv (DPair Nothing q DReflx), SigmaIntro x' y)) <$> go ctx (Just a) b x
    (SigmaIntro x y, 1) =>
      shaped "pair congruence" (\ty => case ty of SigmaTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, y') => (conv (DPair Nothing DReflx q), SigmaIntro x y')) <$> go ctx (Just (substTy c (Ext Id x))) b y
    (Elem.PiTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (DPi q DReflx, Elem.PiTy a' c)) <$> go ctx (Just cls) b a
    (Elem.PiTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (DPi DReflx q, Elem.PiTy a c')) <$> go (ctx :< a) (Just cls) (1 + b) c
    (Elem.SigmaTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (DSigma q DReflx, Elem.SigmaTy a' c)) <$> go ctx (Just cls) b a
    (Elem.SigmaTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (DSigma DReflx q, Elem.SigmaTy a c')) <$> go (ctx :< a) (Just cls) (1 + b) c
    (Elem.SumTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (DSum q DReflx, Elem.SumTy a' c)) <$> go ctx (Just cls) b a
    (Elem.SumTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (DSum DReflx q, Elem.SumTy a c')) <$> go ctx (Just cls) b c
    (Elem.EqTy l r t, 0) => (\(q, l') => (DEq q DReflx DReflx, Elem.EqTy l' r t)) <$> go ctx (Just t) b l
    (Elem.EqTy l r t, 1) => (\(q, r') => (DEq DReflx q DReflx, Elem.EqTy l r' t)) <$> go ctx (Just t) b r
    (Elem.EqTy l r t, 2) => (\(q, t') => (DEq DReflx DReflx q, Elem.EqTy l r t')) <$> go ctx (Just TopTy) b t
    (QuotTy a r, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (DQuot q DReflx, QuotTy a' r)) <$> go ctx (Just cls) b a
    (QuotTy a r, 1) =>
      (\(q, r') => (DQuot DReflx q, QuotTy a r')) <$> go (ctx :< a :< substTy a Wk) (Just PropTy) (2 + b) r
    (SigVar x es, _) => do
      cty <- sigChildTy sig x (toList es) i
      (\(qs, es') => (DRef x qs, SigVar x es')) <$> spineWrap i es (go ctx cty b)
    (Class a, 0) =>
      shaped "class congruence" (\ty => case ty of QuotTy dom _ => Just dom; _ => Nothing) $ \(dom, conv) =>
        (\(q, a') => (conv (DClass Nothing q), Class a')) <$> go ctx (Just dom) b a
    (Out t, 0) => do
      tTy <- inferHead sig ctx t
      (q, t') <- go ctx tTy b t
      q' <- exposedChild sig ctx tTy isNuTy q
      pure (DOut q', Out t')
    (Corec pf a f x, 0) => (\(q, a') => (DCorec pf q DReflx DReflx, Corec pf a' f x)) <$> go ctx (Just UniverseTy) b a
    (Corec pf a f x, 1) => (\(q, f') => (DCorec pf DReflx q DReflx, Corec pf a f' x)) <$> go (ctx :< a) Nothing (1 + b) f
    (Corec pf a f x, 2) => (\(q, x') => (DCorec pf DReflx DReflx q, Corec pf a f x')) <$> go ctx (Just a) b x
    (QuotElim f q0, 0) => do
      ((a, _), pq) <- quotParts q0
      (\(q, f') => (DQuotElim Nothing Nothing q pq, QuotElim f' q0)) <$> go (ctx :< a) (map (\x => substTy x Wk) mty) (1 + b) f
    (QuotElim f q0, 1) => do
      qTy <- inferHead sig ctx q0
      (q, q0') <- go ctx qTy b q0
      q' <- exposedChild sig ctx qTy isQuotTy q
      mm <- elimMotive sig ctx mty u
      pure (DQuotElim mm Nothing DReflx q', QuotElim f q0')
    (Squash t, 0) => (\(q, t') => (DSquash q, Squash t')) <$> go ctx (Just TopTy) b t
    (QSort sg k es, _) =>
      (\(qs, es') => (DSort sg k qs, QSort sg k es')) <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    (QCtor sg k es, _) =>
      (\(qs, es') => (DCtor sg k qs, QCtor sg k es')) <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    (QElim sg k fs es w, _) =>
      if i == length (toList es)
        then (\(q, w') => (DQElim sg k Nothing [] (map (const DReflx) fs) (map (const DReflx) (toList es)) q, QElim sg k fs es w'))
               <$> go ctx (Just (QSort sg k es)) b w
        else (\(qs, es') => (DQElim sg k Nothing [] (map (const DReflx) fs) qs DReflx, QElim sg k fs es' w))
               <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    _ => kerr "proof: bad path [i=\{show i}, at \{show u}]"
 where
  -- the scrutinee as a derivation child (a typed neutral under its
  -- exposure when its declared type hides the shape) and the shape's
  -- parts
  sumParts : Elem -> KM ((Ty, Ty), Drv)
  sumParts t = do
    (tTy, pt) <- headD sig ctx t isSumTy
    case tTy of
      Just x => do
        x' <- kWhnfT sig x
        pure (case x' of
                SumTy a c => ((a, c), pt)
                _ => ((TopTy, TopTy), pt))
      Nothing => pure ((TopTy, TopTy), pt)
  quotParts : Elem -> KM ((Ty, Ty), Drv)
  quotParts q = do
    (qTy, pq) <- headD sig ctx q isQuotTy
    case qTy of
      Just x => do
        x' <- kWhnfT sig x
        pure (case x' of
                QuotTy a r => ((a, r), pq)
                _ => ((TopTy, TopTy), pq))
      Nothing => pure ((TopTy, TopTy), pq)

||| A LICENCE: what a candidate emits — the construction of the stating
||| derivation of its equation, in the context it is built in (the
||| candidate's own pattern context, §10.4: the licence is built ONCE
||| there and instantiated by the substitution node at each use).
public export
Licence : Type
Licence = Sig -> Ctx -> KM Drv

||| The licence of a proof ELEMENT: the element as a typed neutral,
||| reflected at its equality prop (its type exposed to the ≡ by
||| recorded δ — a conversion the reader runs).
export
reflectElem : Elem -> Licence
reflectElem p sig ctx = do
  (d, pty) <- elemToDrv sig ctx p
  (_, pt) <- rdExpose sig ctx pty
  pure (DRefl (case pt of
                 DReflx => d
                 _ => DConv d Nothing pt))

||| S-INJECTIVITY, derived: from a licence for S x ≐ S y, the licence
||| for x ≐ y is the congruence with the predecessor — an ℕ-elim
||| retraction of S, inlined as an ascribed λ so the stated sides
||| pred (S x) ≐ pred (S y) join to x ≐ y by β alone. No rule is cited:
||| the foundation notes S-injectivity as derivable, and the kernel has
||| no injectivity node.
export
predCong : Licence -> Licence
predCong lic sig ctx = do
  q <- lic sig ctx
  pd <- argDrv sig ctx predFn (PiTy NatTy NatTy)
  pure (DApp (DAscribe pd (Just (DPi DNatTy DNatTy)) Nothing) q)
 where
  predFn : Elem
  predFn = PiIntro (NatElim NatIntro0 (CtxVar 1) (CtxVar 0))

||| A LICENCE LEAF: the licence's derivation, the licence's own
||| normalization proofs bridging its raw sides to the stored spelling
||| (pL ▷ lRaw ≐ lN, pR ▷ rRaw ≐ rN: a candidate stored normalized is
||| licensed from its raw type by transitivity over the leaf). States
||| lN ≐ rN — a leaf the kernel reads ⇒ (the normalization proofs run
||| from the stated sides).
export
licLeaf : Sig -> Ctx -> Licence -> Drv -> Drv -> KM Drv
licLeaf sig ctx lic pL pR = do
  base <- lic sig ctx
  pure (dTrans (dSym pL) (dTrans base pR))

||| One REWRITE on a side: the leaf (built by `mkLeaf` at the depth of
||| the position — the binders crossed) placed at `path` in `t` inside
||| the node skeleton of the position, converted where the position's
||| type is spelled otherwise than the leaf's — giving the derivation
||| of t ≐ t′ and t′.
export
rwPrf : Sig -> Ctx -> Maybe Ty -> Elem -> List Nat -> (Ctx -> Nat -> KM Drv) -> KM (Drv, Elem)
rwPrf sig ctx tyRoot t path mkLeaf =
  wrapAt sig ctx tyRoot 0 t path (\ctx', mty, b, _ => do
    leaf <- mkLeaf ctx' b
    (_, rN, lty) <- dInfer sig ctx' leaf
    -- the positional match: the stated equation's type meets the
    -- position's by β, or arrives converted
    leafP <- case mty of
      Nothing => pure leaf
      Just e => do
        ok <- tyAgreeB sig e lty
        if ok then pure leaf else do
          md <- deltaPrf sig ctx' lty e
          case md of
            Just pt => pure (DConv leaf Nothing pt)
            Nothing => kerr "proof: no δ-conversion between the stated type and the position's [stated: \{show lty}; position: \{show e}]"
    pure (leafP, rN))

||| A derivation of t ≐ t′ where t′ is t with ONE child rewritten: the
||| child's derivation placed at index i inside the node skeleton of
||| the position (the child is proved in its own context and type,
||| which wrapAt computes as the kernel's node does).
export
congAt : Sig -> Ctx -> Maybe Ty -> Elem -> Nat -> Drv -> KM Drv
congAt sig ctx mty t i q =
  fst <$> wrapAt sig ctx mty 0 t [i] (\_, _, _, u => pure (q, u))

||| A prop's derivation at Ω, when the type re-derives (an
||| eliminator standing as a prop reads at the constant motive Ω;
||| the kernel then reads the derivation — nothing is guessed there);
||| Nothing where it does not, leaving the kernel its own judgement by
||| shape.
export
propDrv : Sig -> Ctx -> Ty -> KM (Maybe Drv)
propDrv sig ctx ty = kOrElse (Just <$> rdType sig ctx ty) (pure Nothing)

||| A proof-irrelevance leaf at a type (exposed to its prop head by δ,
||| the exposure around the leaf), the prop derived when it re-derives.
export
irrelAt : Sig -> Ctx -> Ty -> KM Drv
irrelAt sig ctx ty = do
  (tyX, pt) <- rdExpose sig ctx ty
  d <- propDrv sig ctx tyX
  pure (convWrap pt (DIrrel d))

||| A type-directed leaf under the exposure of the type's head (the
||| leaf is built from the exposed, β-whnf'd type).
export
leafAt : Sig -> Ctx -> Ty -> (Ty -> KM Drv) -> KM Drv
leafAt sig ctx ty mk = do
  (tyX, pt) <- rdExpose sig ctx ty
  ty' <- kWhnfT sig tyX
  convWrap pt <$> mk ty'

||| Fuel for proof construction (the kernel's own budget).
export
certFuel : Nat
certFuel = 1000000

||| Run a proof construction from pure code: Nothing when it fails (the
||| same signal a kernel rejection gives — the engine then reports an
||| obligation).
export
runP : KM a -> Maybe a
runP m = case runKM m certFuel of
  Right (v, _) => Just v
  Left _ => Nothing

||| Run a proof construction, keeping the failure message (diagnostics).
export
runPE : KM a -> Either String a
runPE m = map fst (runKM m certFuel)

||| runP with the failure AUDITED under the label (NOVA_AUDIT=1): a
||| match the engine found but could not write the derivation of is an
||| engine-bug signal, reported as PROOF-FAIL and dropped (the search
||| goes on with its other routes).
export
runPA : Lazy String -> KM a -> Maybe a
runPA label m = case runKM m certFuel of
  Right (v, _) => Just v
  Left e => audit "PROOF-FAIL \{label} | \{e}" Nothing

||| Σ-lemma names a derivation relies on: the heads of its reflection
||| leaves' elements (hypothesis proofs are variable-headed and
||| contribute nothing). Display only.
export
hintNamesP : Drv -> List String
hintNamesP p = go p
 where
  headName : Drv -> List String
  headName (DRef x _) = [x]
  headName (DApp f _) = headName f
  headName (DAscribe q _ _) = headName q
  headName (DConv q _ _) = headName q
  headName (DSubst q _) = headName q
  headName _ = []
  go : Drv -> List String
  go (DRefl q) = headName q
  go (DSym q) = go q
  go (DTrans q r) = go q ++ go r
  go (DTransAt q m r) = go q ++ go m ++ go r
  go (DAscribe q _ mb) = go q ++ maybe [] go mb
  go (DConv q _ b) = go q ++ go b
  go (DAt q _ b) = go q ++ go b
  go (DSubst q _) = go q
  go (DEtaPi q) = go q
  go (DEtaSigma q r) = go q ++ go r
  go (DQuotWit (Just q)) = go q
  go (DQuotWitPrf q) = go q
  go (DInj q) = go q
  go (DPrfCong _ _ q) = go q
  go (DApp f a) = go f ++ go a
  go (DProj1 q) = go q
  go (DProj2 q) = go q
  go (DOut q) = go q
  go (DSuc q) = go q
  go (DZeroElim _ q) = go q
  go (DNatElim _ z s n) = go z ++ go s ++ go n
  go (DSumElim _ l r t) = go l ++ go r ++ go t
  go (DQuotElim _ _ f q) = go f ++ go q
  go (DQElim _ _ _ _ ms es w) = concatMap go ms ++ concatMap go es ++ go w
  go (DLam _ q) = go q
  go (DPair _ u v) = go u ++ go v
  go (DInj1 _ q) = go q
  go (DInj2 _ q) = go q
  go (DClass _ q) = go q
  go (DCorec _ a f x) = go a ++ go f ++ go x
  go (DPi a b) = go a ++ go b
  go (DSigma a b) = go a ++ go b
  go (DSum a b) = go a ++ go b
  go (DEq l r t) = go l ++ go r ++ go t
  go (DQuot a r) = go a ++ go r
  go (DSquash q) = go q
  go (DRef _ qs) = concatMap go qs
  go (DSort _ _ qs) = concatMap go qs
  go (DCtor _ _ qs) = concatMap go qs
  go _ = []

||| A path leaf's spine stated (for the elaborator's own path leaves).
export
pathArgsB : Sig -> Ctx -> QSig -> Nat -> SubNorm -> Maybe (List Drv)
pathArgsB sig ctx sg k th = runP (pathArgs sig ctx sg k th)
