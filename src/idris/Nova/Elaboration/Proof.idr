module Nova.Elaboration.Proof

-- The discharge ENGINE's proof library: how the engine writes the
-- kernel's proof terms (Nova.Kernel.Prf) as it searches.
--
-- The engine finds equations by rewriting and emits a proof term for
-- what it did AS it does it: a licence applied at a position becomes
-- its reflection leaf inside the congruence skeleton of the position
-- (wrapAt, typed as the kernel's nodes type their children), a δ-round
-- becomes a δ-all leaf, a type-directed closing step becomes its leaf,
-- and the rewritten forms meet by transitivity. Nothing here is
-- trusted: the kernel checks the proof term and nothing else. The
-- helpers run in the kernel's monad because the skeleton around a leaf
-- needs the kernel's own typing of the position (a head's declared
-- type opened to the shape the next node needs, an argument's checking
-- skeleton); the engine, which is pure, runs them through `runP`.

import Data.List
import Data.Maybe
import Data.SnocList
import Control.Monad.State

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT
import Nova.Kernel
import Nova.Profile

%default covering

||| Wk composed n times (the weakening Γ·(n entries) ⇒ Γ).
wkN : Nat -> Sub
wkN Z = Id
wkN (S n) = Chain (wkN n) Wk

listAt : Nat -> List a -> Maybe a
listAt Z (x :: _) = Just x
listAt (S n) (_ :: xs) = listAt n xs
listAt _ [] = Nothing

listSet : Nat -> a -> List a -> Maybe (List a)
listSet Z y (_ :: xs) = Just (y :: xs)
listSet (S n) y (x :: xs) = map (x ::) (listSet n y xs)
listSet _ _ [] = Nothing

||| A spine with one child rewritten: the proofs (reflexivity at every
||| other entry) and the new spine.
spineWrap : Nat -> SubNorm -> (Elem -> KM (Prf, Elem)) -> KM (List Prf, SubNorm)
spineWrap i es go = do
  let xs = toList es
  e <- case listAt i xs of
         Just e => pure e
         Nothing => kerr "proof: bad path (spine index)"
  (q, e') <- go e
  xs' <- case listSet i e' xs of
           Just v => pure v
           Nothing => kerr "proof: bad path (spine index)"
  pure (map (\j => if j == i then q else PReflx) (indices xs), cast xs')
 where
  indices : List a -> List Nat
  indices ys = go' 0 ys
   where
    go' : Nat -> List a -> List Nat
    go' _ [] = []
    go' k (_ :: rest) = k :: go' (S k) rest

||| A congruence node around a child proof that is reflexivity is
||| reflexivity.
congOf : Prf -> Prf -> Prf
congOf PReflx _ = PReflx
congOf _ node = node

||| Wrap a proof at a position whose type was exposed by δ in the
||| conversion to the exposed spelling.
convWrap : Prf -> Ty -> Prf -> Prf
convWrap PReflx _ p = p
convWrap pt tyX p = PConv pt tyX p

||| The kernel's β-only type agreement (join, or cumulativity).
tyAgreeB : Sig -> Ty -> Ty -> KM Bool
tyAgreeB sig a b = do
  aN <- kJoinTy sig a
  bN <- kJoinTy sig b
  pure (aN == bN || (aN == TopTy && bN == UniverseTy))

||| Definition names occurring in a term.
||| The embedded Nova pieces of a carried signature.
export
piecesOf : QSig -> List Elem
piecesOf g = fst (runState [] (traverseQSig (\e => do modify (e ::); pure e) g))

defNames : Sig -> Elem -> KM (List String)
defNames sig t = do
  ns <- traverse isDef (nub (names t []))
  pure (catMaybes ns)
 where
  isDef : String -> KM (Maybe String)
  isDef x = kSigLookup sig x >>= \e => pure (case e of
                                               Just (SigDef _ _ _ _) => Just x
                                               _ => Nothing)
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
  names (QSort sg _ es) acc = foldl (\a, e => names e a) acc (piecesOf sg ++ toList es)
  names (QCtor sg _ es) acc = foldl (\a, e => names e a) acc (piecesOf sg ++ toList es)
  names (QElim sg _ _ es w) acc = foldl (\a, e => names e a) (names w acc) (piecesOf sg ++ toList es)
  names (Out u) acc = names u acc
  names (Corec _ a f x) acc = names a (names f (names x acc))
  names _ acc = acc

||| A proof of a ≐ b (at 𝕍, or any type) by δ-rounds on both sides:
||| every definition occurring unfolds at once, the sides β-join,
||| repeat while new names appear — the engine's widening δβ join as
||| a proof. Nothing when the sides never meet.
deltaPrf : Sig -> Elem -> Elem -> KM (Maybe Prf)
deltaPrf sig a0 b0 = do
  aJ <- kJoinElem sig a0
  bJ <- kJoinElem sig b0
  go 64 [] aJ bJ [] []
 where
  chain : List Prf -> Prf
  chain [] = PReflx
  chain (p :: ps) = PTrans p (chain ps)
  -- every definition occurring on either side unfolds each round (a
  -- body may bring back a name an earlier round unfolded); stop at a
  -- fixed point
  go : Nat -> List String -> Elem -> Elem -> List Prf -> List Prf -> KM (Maybe Prf)
  go k seen a b la lb =
    if a == b then pure (Just (pTrans (chain (reverse la)) (pSym (chain (reverse lb)))))
    else case k of
      Z => pure Nothing
      S k' => do
        na <- defNames sig a
        nb <- defNames sig b
        let ns = nub (na ++ nb)
        case ns of
          [] => pure Nothing
          _ => do
            a' <- unfoldAllK sig ns a >>= kJoinElem sig
            b' <- unfoldAllK sig ns b >>= kJoinElem sig
            if a' == a && b' == b then pure Nothing
              else go k' (seen ++ ns) a' b' (PDeltaAll ns :: la) (PDeltaAll ns :: lb)

||| Is the term a SPINE — typable from its head's declared type by
||| eliminations alone (self leaves and elimination nodes)?
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

mutual
  ||| Head exposure with its δ RECORDED: the term taken to its β-whnf
  ||| with every definition unfolded on the way to the head as a δ leaf
  ||| inside the congruence skeleton of its position — and the proof of
  ||| t ≐ exposed (reflexivity when β alone reached it, which the
  ||| kernel's own whnf does).
  export
  exposeKW : (String -> Bool) -> Sig -> Ctx -> Elem -> KM (Elem, Prf)
  exposeKW ok sig ctx t = go t
   where
    go : Elem -> KM (Elem, Prf)
    go (SigVar x es) =
      if not (ok x) then pure (SigVar x es, PReflx) else
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef _ _ a _) => do
          qs <- deltaArgs sig ctx x es
          (r, p) <- go (substElem a (embed es))
          pure (r, pTrans (PDelta x qs) p)
        _ => pure (SigVar x es, PReflx)
    go (PiApp f e) = do
      (f', p1) <- go f
      case f' of
        PiIntro g => do
          (r, p2) <- go (substElem g (Ext Id e))
          pure (r, pTrans (congOf p1 (CPiApp p1 PReflx)) p2)
        _ => pure (PiApp f' e, congOf p1 (CPiApp p1 PReflx))
    go (Let a b) = go (substElem b (Ext (Ext Id a) Star))
    go (NatElim z s t) = do
      (t', p1) <- go t
      let node = congOf p1 (CNatElim Nothing PReflx PReflx p1)
      case t' of
        NatIntro0 => do (r, p2) <- go z; pure (r, pTrans node p2)
        NatIntro1 n => do (r, p2) <- go (substElem s (Ext (Ext Id n) (NatElim z s n))); pure (r, pTrans node p2)
        _ => pure (NatElim z s t', node)
    go (SigmaElim1 t) = do
      (t', p1) <- go t
      case t' of
        SigmaIntro a _ => do (r, p2) <- go a; pure (r, pTrans (congOf p1 (CSigmaElim1 p1)) p2)
        _ => pure (SigmaElim1 t', congOf p1 (CSigmaElim1 p1))
    go (SigmaElim2 t) = do
      (t', p1) <- go t
      case t' of
        SigmaIntro _ b => do (r, p2) <- go b; pure (r, pTrans (congOf p1 (CSigmaElim2 p1)) p2)
        _ => pure (SigmaElim2 t', congOf p1 (CSigmaElim2 p1))
    go (SumElim l r t) = do
      (t', p1) <- go t
      let node = congOf p1 (CSumElim Nothing PReflx PReflx p1)
      case t' of
        Inj1 a => do (r', p2) <- go (substElem l (Ext Id a)); pure (r', pTrans node p2)
        Inj2 b => do (r', p2) <- go (substElem r (Ext Id b)); pure (r', pTrans node p2)
        _ => pure (SumElim l r t', node)
    go (QuotElim f q) = do
      (q', p1) <- go q
      case q' of
        Class a => do (r, p2) <- go (substElem f (Ext Id a)); pure (r, pTrans (congOf p1 (CQuotElim Nothing PReflx p1)) p2)
        _ => pure (QuotElim f q', congOf p1 (CQuotElim Nothing PReflx p1))
    go (Out t) = do
      (t', p1) <- go t
      case t' of
        Corec p a f x => do
          (r, p2) <- go (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
          pure (r, pTrans (congOf p1 (COut p1)) p2)
        _ => pure (Out t', congOf p1 (COut p1))
    go (QElim sg k fs es w) = do
      (w', p1) <- go w
      let node = congOf p1 (CQElim sg k Nothing (map (const PReflx) fs) (map (const PReflx) (toList es)) p1)
      case w' of
        QCtor sgW c theta =>
          if sgW == sg
            then case qElimBetaRhs sg fs c theta of
                   Right rhs => do (r, p2) <- go rhs; pure (r, pTrans node p2)
                   Left _ => pure (QElim sg k fs es w', node)
            else pure (QElim sg k fs es w', node)
        _ => pure (QElim sg k fs es w', node)
    -- the squashee exposed inside its ∥·∥; a squashee that exposes to a
    -- prop collapses (code-squash-idem's instance, a β-rule of the join)
    go (Squash t) = do
      (t', p1) <- go t
      let node = congOf p1 (CSquash p1)
      pure (case t' of
              Elem.EqTy _ _ _ => (t', node)
              Squash _ => (t', node)
              _ => (Squash t', node))
    go e = pure (e, PReflx)

  ||| Head exposure with every definition allowed (the kernel-facing
  ||| helpers below expose freely: a shape a node needs is reached).
  exposeK : Sig -> Ctx -> Elem -> KM (Elem, Prf)
  exposeK = exposeKW (const True)

  ||| Expose a position's type, when known.
  exposeMaybe : Sig -> Ctx -> Maybe Ty -> KM (Maybe (Ty, Prf))
  exposeMaybe sig ctx Nothing = pure Nothing
  exposeMaybe sig ctx (Just t) = Just <$> exposeK sig ctx t

  ||| The spine of a δ leaf stated entrywise: proof i at Δ's entry type
  ||| instantiated by the earlier entries.
  deltaArgs : Sig -> Ctx -> String -> SubNorm -> KM (List Prf)
  deltaArgs sig ctx x es =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ _) =>
        let entryTy : Nat -> List Elem -> Maybe Ty
            entryTy i pre = case getAt i (toList delta) of
              Just t => Just (substTy t (embed (cast pre)))
              Nothing => Nothing
        in statedArgs entryTy (toList es)
      _ => kerr "proof: δ leaf at a non-definition '\{x}'"
   where
    statedArgs : (Nat -> List Elem -> Maybe Ty) -> List Elem -> KM (List Prf)
    statedArgs entryTy xs = go 0 xs []
     where
      go : Nat -> List Elem -> List Elem -> KM (List Prf)
      go i [] acc = pure []
      go i (e :: rest) acc = do
        ty <- case entryTy i (reverse acc) of
                Just t => pure t
                Nothing => kerr "proof: spine entry type undetermined"
        q <- argPrf sig ctx e ty
        qs <- go (S i) rest (e :: acc)
        pure (q :: qs)

  ||| The spine of a path leaf stated entrywise at the reflected
  ||| telescope.
  pathArgs : Sig -> Ctx -> QSig -> Nat -> SubNorm -> KM (List Prf)
  pathArgs sig ctx sg k th = do
    sg' <- kJoinQSig sig sg
    entry <- case qEntry sg' k of
               Just e => pure e
               Nothing => kerr "proof: path leaf entry out of range"
    (tel, _, _) <- liftQ (reflTel sg' (qwAt k) entry)
    go tel 0 (toList th) []
   where
    go : List Ty -> Nat -> List Elem -> List Elem -> KM (List Prf)
    go tel i [] acc = pure []
    go tel i (e :: rest) acc = do
      ty <- case telInst tel i (reverse acc) of
              Just t => pure t
              Nothing => kerr "proof: path leaf telescope mismatch"
      q <- argPrf sig ctx e ty
      qs <- go tel (S i) rest (e :: acc)
      pure (q :: qs)

  ||| A SKELETON for a term checked at a type, built from the kernel's
  ||| own exposure: the head exposures at intro forms (PExpose) and at
  ||| eliminations (PScrut) that a β-only checker cannot reach on its
  ||| own — the translator's twin of the elaborator's reconstruction.
  chkSkel : Sig -> Ctx -> Elem -> Ty -> KM Skel
  chkSkel sig ctx e ty = case e of
    PiIntro f => shaped (\t => case t of PiTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      (\sk => Nd [] [sk]) <$> chkSkel sig (ctx :< a) f b
    SigmaIntro u v => shaped (\t => case t of SigmaTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      [| (\su, sv => Nd [] [su, sv]) (chkSkel sig ctx u a) (chkSkel sig ctx v (substTy b (Ext Id u))) |]
    Inj1 a => shaped (\t => case t of SumTy d _ => Just d; _ => Nothing) $ \d =>
      (\sk => Nd [] [sk]) <$> chkSkel sig ctx a d
    Inj2 b => shaped (\t => case t of SumTy _ c => Just c; _ => Nothing) $ \c =>
      (\sk => Nd [] [sk]) <$> chkSkel sig ctx b c
    Class a => shaped (\t => case t of QuotTy d _ => Just d; _ => Nothing) $ \d =>
      (\sk => Nd [] [sk]) <$> chkSkel sig ctx a d
    Corec p a f x => shaped (\t => case t of NuTy pf => Just pf; _ => Nothing) $ \pf =>
      [| (\sa, sf, sx => Nd [] [sa, sf, sx]) (chkSkel sig ctx a UniverseTy)
                                              (chkSkel sig (ctx :< a) f (substTy (reflectPoly pf a) Wk))
                                              (chkSkel sig ctx x a) |]
    -- ⋆ at an EVIDENT prop: a squashed 𝟙, or an equation the join closes
    Star => do
      (tyX, pt) <- exposeK sig ctx ty
      ty' <- kWhnfT sig tyX
      case ty' of
        Squash sq => do
          sq' <- kWhnfT sig sq
          pure (case sq' of
                  OneTy => withExp pt tyX (Nd [PSquashWit OneIntro (Nd [] [])] [])
                  _ => withExp pt tyX (Nd [] []))
        Elem.EqTy _ _ _ => pure (withExp pt tyX (Nd [PReflEq PReflx] []))
        _ => pure (Nd [] [])
    ZeroElim t => (\sk => Nd [] [sk]) <$> chkSkel sig ctx t ZeroTy
    -- a constructor's or sort's spine, each entry at its telescope type
    QCtor sg k es => Nd [] <$> spineSkels sg k es
    QSort sg k es => Nd [] <$> spineSkels sg k es
    -- a QIIT eliminator checked at a type: the CONSTANT-MOTIVE instance
    -- (every sort's motive the expected type, weakened into the sort's
    -- context), the coherences by β (docs/NovaKernel.txt, A1/A4)
    QElim sg k mths es w => do
      sg' <- kJoinQSig sig sg
      let sortPs = qPositions QKSort sg'
      let pointPs = qPositions QKPoint sg'
      let eqPs = qPositions QKEq sg'
      mots <- traverse (\sj => do
                sjE <- case qEntry sg' sj of
                         Just x => pure x
                         Nothing => kerr "proof: sort out of range"
                (tel, _, _) <- liftQ (reflTel sg' (qwAt sj) sjE)
                pure (substTy ty (wkN (S (length tel))))) sortPs
      mSks <- traverse (\(cj, m) => do
                mty <- liftQ (methodTy sg' mots cj)
                chkSkel sig ctx m mty) (zip pointPs mths)
      let esL = toList es
      eSks <- traverse (\(i, x) => case qSpineChildTy sg' k es i of
                          Just t => chkSkel sig ctx x t
                          Nothing => pure (Nd [] [])) (zip (indices esL) esL)
      wSk <- chkSkel sig ctx w (QSort sg' k es)
      pure (Nd [PQMotives mots (map (const (Nd [] [])) mots), PQCoh (map (const PReflx) eqPs)]
               (mSks ++ eSks ++ [wSk]))
    -- an eliminator checked at a type: the CONSTANT-MOTIVE instance
    -- (A1) — the motive is the expected type weakened over the
    -- eliminated binder, the cases checked at it under theirs
    NatElim z st t => do
      let mot = substTy ty Wk
      motSk <- kOrElse (fst <$> infSkel sig (ctx :< NatTy) mot) (pure (Nd [] []))
      zSk <- chkSkel sig ctx z ty
      sSk <- chkSkel sig (ctx :< NatTy :< mot) st (substTy ty (wkN 2))
      tSk <- chkSkel sig ctx t NatTy
      pure (Nd [PMotive mot motSk] [zSk, sSk, tSk])
    SumElim l r t => do
      (tSk, mtTy) <- infSkel sig ctx t
      case mtTy of
        Just tTy => do
          (tX, pt) <- exposeK sig ctx tTy
          tW <- kWhnfT sig tX
          case tW of
            SumTy a b => do
              let mot = substTy ty Wk
              motSk <- kOrElse (fst <$> infSkel sig (ctx :< SumTy a b) mot) (pure (Nd [] []))
              lSk <- chkSkel sig (ctx :< a) l (substTy ty Wk)
              rSk <- chkSkel sig (ctx :< b) r (substTy ty Wk)
              let ps = the (List Payload) $ case pt of
                         PReflx => [PMotive mot motSk]
                         _ => [PScrut tX pt, PMotive mot motSk]
              pure (Nd ps [lSk, rSk, tSk])
            _ => bare
        Nothing => bare
    _ => bare
   where
    -- a non-intro term at a type spelled otherwise than the one it
    -- infers to: the switch proof (a δ bridge) rides along, since the
    -- kernel's switch-less fallthrough compares by β only
    bare : KM Skel
    bare = do
      (sk, mty) <- infSkel sig ctx e
      case mty of
        Just t => do
          ok <- tyAgreeB sig ty t
          if ok then pure sk else do
            md <- deltaPrf sig t ty
            pure (case (md, sk) of
                    (Just p, Nd ps cs) => Nd (PSwitch p :: ps) cs
                    (Nothing, _) => sk)
        Nothing => pure sk
    indices : List a -> List Nat
    indices xs = go 0 xs
     where
      go : Nat -> List a -> List Nat
      go _ [] = []
      go i (_ :: rest) = i :: go (S i) rest
    spineSkels : QSig -> Nat -> SubNorm -> KM (List Skel)
    spineSkels sg k es = do
      sg' <- kJoinQSig sig sg
      let esL = toList es
      traverse (\(i, x) => case qSpineChildTy sg' k es i of
                             Just t => chkSkel sig ctx x t
                             Nothing => fst <$> infSkel sig ctx x) (zip (indices esL) esL)
    withExp : Prf -> Ty -> Skel -> Skel
    withExp PReflx _ sk = sk
    withExp pt tyX (Nd ps cs) = Nd (PExpose tyX pt :: ps) cs
    shaped : (Ty -> Maybe a) -> (a -> KM Skel) -> KM Skel
    shaped pick k = do
      (tyX, pt) <- exposeK sig ctx ty
      ty' <- kWhnfT sig tyX
      case pick ty' of
        Just parts => withExp pt tyX <$> k parts
        Nothing => pure (Nd [] [])

  ||| Inference position: the skeleton and the type it infers to
  ||| (Nothing when structure alone does not determine it).
  infSkel : Sig -> Ctx -> Elem -> KM (Skel, Maybe Ty)
  infSkel sig ctx e = case e of
    PiApp f a => do
      (fSk, fTy) <- infSkel sig ctx f
      case fTy of
        Just t => do
          (tX, pt) <- exposeK sig ctx t
          t' <- kWhnfT sig tX
          case t' of
            PiTy dom cod => do
              aSk <- chkSkel sig ctx a dom
              pure (withScrutK pt tX (Nd [] [fSk, aSk]), Just (substTy cod (Ext Id a)))
            _ => pure (Nd [] [fSk, Nd [] []], Nothing)
        Nothing => pure (Nd [] [fSk, Nd [] []], Nothing)
    SigmaElim1 t => scrut t (\t' => case t' of SigmaTy a _ => Just a; _ => Nothing)
    SigmaElim2 t => scrut t (\t' => case t' of SigmaTy _ b => Just (substTy b (Ext Id (SigmaElim1 t))); _ => Nothing)
    Out t => scrut t (\t' => case t' of NuTy f => Just (reflectPoly f (Elem.NuTy f)); _ => Nothing)
    NatIntro1 t => (\sk => (Nd [] [sk], Just NatTy)) <$> chkSkel sig ctx t NatTy
    Elem.EqTy l r t => do
      sl <- chkSkel sig ctx l t
      sr <- chkSkel sig ctx r t
      (st, _) <- infSkel sig ctx t
      pure (Nd [] [sl, sr, st], Just PropTy)
    Squash t => (\(sk, _) => (Nd [] [sk], Just PropTy)) <$> infSkel sig ctx t
    _ => do
      mt <- inferHead sig ctx e
      pure (Nd [] [], mt)
   where
    withScrutK : Prf -> Ty -> Skel -> Skel
    withScrutK PReflx _ sk = sk
    withScrutK pt tyX (Nd ps cs) = Nd (PScrut tyX pt :: ps) cs
    scrut : Elem -> (Ty -> Maybe Ty) -> KM (Skel, Maybe Ty)
    scrut t pick = do
      (tSk, tTy) <- infSkel sig ctx t
      case tTy of
        Just x => do
          (xX, pt) <- exposeK sig ctx x
          x' <- kWhnfT sig xX
          pure (withScrutK pt xX (Nd [] [tSk]), pick x')
        Nothing => pure (Nd [] [tSk], Nothing)

  ||| A TYPED NEUTRAL: the spine as a synthesising proof — self leaves
  ||| at the head, elimination nodes above, an ascription (PAt with a
  ||| δ proof) wherever a definition hides the shape the next
  ||| elimination needs — and the type it states.
  elemToPrf : Sig -> Ctx -> Elem -> KM (Prf, Ty)
  elemToPrf sig ctx e = case e of
    PiApp f a => do
      (pf, fTy) <- elemToPrf sig ctx f
      (fTyX, pt) <- exposeK sig ctx fTy
      fTy' <- kWhnfT sig fTyX
      case fTy' of
        PiTy dom cod => do
          pa <- argPrf sig ctx a dom
          pure (CPiApp (ascribe pf fTyX pt) pa, substTy cod (Ext Id a))
        _ => kerr "proof: typed neutral applies a non-function [\{show f} : \{show fTy'}]"
    SigmaElim1 t => do
      (pt', tTy) <- elemToPrf sig ctx t
      (tTyX, pt) <- exposeK sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      case tTy' of
        SigmaTy a _ => pure (CSigmaElim1 (ascribe pt' tTyX pt), a)
        _ => kerr "proof: typed neutral projects a non-pair [\{show t} : \{show tTy'}]"
    SigmaElim2 t => do
      (pt', tTy) <- elemToPrf sig ctx t
      (tTyX, pt) <- exposeK sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      case tTy' of
        SigmaTy _ b => pure (CSigmaElim2 (ascribe pt' tTyX pt), substTy b (Ext Id (SigmaElim1 t)))
        _ => kerr "proof: typed neutral projects a non-pair [\{show t} : \{show tTy'}]"
    Out t => do
      (pt', tTy) <- elemToPrf sig ctx t
      (tTyX, pt) <- exposeK sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      case tTy' of
        NuTy f => pure (COut (ascribe pt' tTyX pt), reflectPoly f (Elem.NuTy f))
        _ => kerr "proof: typed neutral observes a non-ν element [\{show t} : \{show tTy'}]"
    _ => do
      (_, _, ty) <- kPrfS sig ctx (PSelf e)
      pure (PSelf e, ty)
   where
    ascribe : Prf -> Ty -> Prf -> Prf
    ascribe p _ PReflx = p
    ascribe p tyX pt = PAt p tyX pt

  ||| A proof ARGUMENT at the domain the head demands: a spine states
  ||| its type and is ascribed to the domain when spelled otherwise; any
  ||| other form is checked at the domain (PChk, with its skeleton).
  argPrf : Sig -> Ctx -> Elem -> Ty -> KM Prf
  argPrf sig ctx a dom =
    if isSpine a
      then do
        (pa, aTy) <- elemToPrf sig ctx a
        ok <- tyAgreeB sig dom aTy
        if ok then pure pa else do
          md <- deltaPrf sig aTy dom
          case md of
            Just pt => pure (PAt pa dom pt)
            Nothing => kerr "proof: proof argument at the wrong type [stated: \{show aTy}; expected: \{show dom}]"
      else do
        sk <- chkSkel sig ctx a dom
        pure (PChk a dom sk)

||| The head of an elimination as a proof child: reflexivity when its
||| declared type already shows the shape the node needs (β), else the
||| typed neutral that states it. Returns the (exposed) type as well.
headPrf : Sig -> Ctx -> Elem -> KM (Maybe Ty, Prf)
headPrf sig ctx hd = do
  hTy <- inferHead sig ctx hd
  case hTy of
    Nothing =>
      if isSpine hd
        then do (p, t) <- elemToPrf sig ctx hd; pure (Just t, p)
        else pure (Nothing, PReflx)
    Just t => do
      (tX, pt) <- exposeK sig ctx t
      case pt of
        PReflx => pure (Just t, PReflx)
        _ => do (p, t') <- elemToPrf sig ctx hd; pure (Just t', p)

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

||| The congruence skeleton along a path, TYPED: the position's context
||| and expected type are computed as the kernel's nodes compute them
||| (the type flowing down, a neutral head's inferred type, the
||| constant-motive reading), and a node that needs a shape the type
||| only exposes by δ is wrapped in the conversion. `leaf` acts at the
||| path's end with the context, the type (Nothing: undetermined), the
||| binders crossed and the subterm there, giving the leaf's proof and
||| the replacement; every sibling is reflexivity. Child indexing as
||| the engine's rewriter counts it.
wrapAt : Sig -> Ctx -> Maybe Ty -> Nat -> Elem -> List Nat
      -> (Ctx -> Maybe Ty -> Nat -> Elem -> KM (Prf, Elem)) -> KM (Prf, Elem)
wrapAt sig ctx mty b u [] leaf = leaf ctx mty b u
wrapAt sig ctx mty b u (i :: p) leaf = do
  let go : Ctx -> Maybe Ty -> Nat -> Elem -> KM (Prf, Elem)
      go ctx' mty' b' x = wrapAt sig ctx' mty' b' x p leaf
  -- a shape the node needs from the type flowing down, with the
  -- conversion that exposes it
  let shaped : String -> (Ty -> Maybe a) -> ((a, Prf -> Prf) -> KM (Prf, Elem)) -> KM (Prf, Elem)
      shaped what pick k = do
        ty <- case mty of
                Just t => pure t
                Nothing => kerr "proof: \{what} at a type-undetermined position"
        (tyX, pt) <- exposeK sig ctx ty
        tyW <- kWhnfT sig tyX
        case pick tyW of
          Just parts => k (parts, convWrap pt tyX)
          Nothing => kerr "proof: \{what} at a type without the shape [\{show tyW}]"
  case (u, i) of
    (ZeroElim t, 0) => (\(q, t') => (CZeroElim q, ZeroElim t')) <$> go ctx (Just ZeroTy) b t
    (NatIntro1 t, 0) => (\(q, t') => (CNatIntro1 q, NatIntro1 t')) <$> go ctx (Just NatTy) b t
    (NatElim z s t, 0) => (\(q, z') => (CNatElim Nothing q PReflx PReflx, NatElim z' s t)) <$> go ctx mty b z
    (NatElim z s t, 1) =>
      (\(q, s') => (CNatElim Nothing PReflx q PReflx, NatElim z s' t))
        <$> go (ctx :< NatTy :< fromMaybe TopTy (map (\x => substTy x Wk) mty)) (map (\x => substTy x (wkN 2)) mty) (2 + b) s
    (NatElim z s t, 2) => (\(q, t') => (CNatElim Nothing PReflx PReflx q, NatElim z s t')) <$> go ctx (Just NatTy) b t
    (PiIntro f, 0) =>
      shaped "λ-congruence" (\t => case t of PiTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, f') => (conv (CPiIntro q), PiIntro f')) <$> go (ctx :< a) (Just c) (1 + b) f
    (PiApp f e, 0) => do
      fTy <- inferHead sig ctx f
      (\(q, f') => (CPiApp q PReflx, PiApp f' e)) <$> go ctx fTy b f
    (PiApp f e, 1) => do
      (fTy, pf) <- headPrf sig ctx f
      aTy <- domOf sig fTy
      (\(q, e') => (CPiApp pf q, PiApp f e')) <$> go ctx aTy b e
    (SigmaElim1 t, 0) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (CSigmaElim1 q, SigmaElim1 t')) <$> go ctx tTy b t
    (SigmaElim2 t, 0) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (CSigmaElim2 q, SigmaElim2 t')) <$> go ctx tTy b t
    (Inj1 t, 0) =>
      shaped "inj₁ congruence" (\ty => case ty of SumTy a _ => Just a; _ => Nothing) $ \(a, conv) =>
        (\(q, t') => (conv (CInj1 q), Inj1 t')) <$> go ctx (Just a) b t
    (Inj2 t, 0) =>
      shaped "inj₂ congruence" (\ty => case ty of SumTy _ c => Just c; _ => Nothing) $ \(c, conv) =>
        (\(q, t') => (conv (CInj2 q), Inj2 t')) <$> go ctx (Just c) b t
    (SumElim l r t, 0) => do
      ((a, _), pt) <- sumParts t
      (\(q, l') => (CSumElim Nothing q PReflx pt, SumElim l' r t)) <$> go (ctx :< a) Nothing (1 + b) l
    (SumElim l r t, 1) => do
      ((_, c), pt) <- sumParts t
      (\(q, r') => (CSumElim Nothing PReflx q pt, SumElim l r' t)) <$> go (ctx :< c) Nothing (1 + b) r
    (SumElim l r t, 2) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (CSumElim Nothing PReflx PReflx q, SumElim l r t')) <$> go ctx tTy b t
    (SigmaIntro x y, 0) =>
      shaped "pair congruence" (\ty => case ty of SigmaTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, x') => (conv (CSigmaIntro q PReflx), SigmaIntro x' y)) <$> go ctx (Just a) b x
    (SigmaIntro x y, 1) =>
      shaped "pair congruence" (\ty => case ty of SigmaTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, y') => (conv (CSigmaIntro PReflx q), SigmaIntro x y')) <$> go ctx (Just (substTy c (Ext Id x))) b y
    (Elem.PiTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CPiTy q PReflx, Elem.PiTy a' c)) <$> go ctx (Just cls) b a
    (Elem.PiTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (CPiTy PReflx q, Elem.PiTy a c')) <$> go (ctx :< a) (Just cls) (1 + b) c
    (Elem.SigmaTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CSigmaTy q PReflx, Elem.SigmaTy a' c)) <$> go ctx (Just cls) b a
    (Elem.SigmaTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (CSigmaTy PReflx q, Elem.SigmaTy a c')) <$> go (ctx :< a) (Just cls) (1 + b) c
    (Elem.SumTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CSumTy q PReflx, Elem.SumTy a' c)) <$> go ctx (Just cls) b a
    (Elem.SumTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (CSumTy PReflx q, Elem.SumTy a c')) <$> go ctx (Just cls) b c
    (Elem.EqTy l r t, 0) => (\(q, l') => (CEqTy q PReflx PReflx, Elem.EqTy l' r t)) <$> go ctx (Just t) b l
    (Elem.EqTy l r t, 1) => (\(q, r') => (CEqTy PReflx q PReflx, Elem.EqTy l r' t)) <$> go ctx (Just t) b r
    (Elem.EqTy l r t, 2) => (\(q, t') => (CEqTy PReflx PReflx q, Elem.EqTy l r t')) <$> go ctx (Just TopTy) b t
    (QuotTy a r, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CQuotTy q PReflx, QuotTy a' r)) <$> go ctx (Just cls) b a
    (QuotTy a r, 1) =>
      (\(q, r') => (CQuotTy PReflx q, QuotTy a r')) <$> go (ctx :< a :< substTy a Wk) (Just PropTy) (2 + b) r
    (SigVar x es, _) => do
      cty <- sigChildTy sig x (toList es) i
      (\(qs, es') => (CSigVar x qs, SigVar x es')) <$> spineWrap i es (go ctx cty b)
    (Class a, 0) =>
      shaped "class congruence" (\ty => case ty of QuotTy dom _ => Just dom; _ => Nothing) $ \(dom, conv) =>
        (\(q, a') => (conv (CClass q), Class a')) <$> go ctx (Just dom) b a
    (Out t, 0) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (COut q, Out t')) <$> go ctx tTy b t
    (Corec pf a f x, 0) => (\(q, a') => (CCorec pf q PReflx PReflx, Corec pf a' f x)) <$> go ctx (Just UniverseTy) b a
    (Corec pf a f x, 1) => (\(q, f') => (CCorec pf PReflx q PReflx, Corec pf a f' x)) <$> go (ctx :< a) Nothing (1 + b) f
    (Corec pf a f x, 2) => (\(q, x') => (CCorec pf PReflx PReflx q, Corec pf a f x')) <$> go ctx (Just a) b x
    (QuotElim f q0, 0) => do
      ((a, _), pq) <- quotParts q0
      (\(q, f') => (CQuotElim Nothing q pq, QuotElim f' q0)) <$> go (ctx :< a) Nothing (1 + b) f
    (QuotElim f q0, 1) => do
      qTy <- inferHead sig ctx q0
      (\(q, q0') => (CQuotElim Nothing PReflx q, QuotElim f q0')) <$> go ctx qTy b q0
    (Squash t, 0) => (\(q, t') => (CSquash q, Squash t')) <$> go ctx (Just TopTy) b t
    (QSort sg k es, _) =>
      (\(qs, es') => (CQSort sg k qs, QSort sg k es')) <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    (QCtor sg k es, _) =>
      (\(qs, es') => (CQCtor sg k qs, QCtor sg k es')) <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    (QElim sg k fs es w, _) =>
      if i == length (toList es)
        then (\(q, w') => (CQElim sg k Nothing (map (const PReflx) fs) (map (const PReflx) (toList es)) q, QElim sg k fs es w'))
               <$> go ctx (Just (QSort sg k es)) b w
        else (\(qs, es') => (CQElim sg k Nothing (map (const PReflx) fs) qs PReflx, QElim sg k fs es' w))
               <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    _ => kerr "proof: bad path [i=\{show i}, at \{show u}]"
 where
  -- the scrutinee as a proof child (a typed neutral when its declared
  -- type hides the shape) and the shape's parts
  sumParts : Elem -> KM ((Ty, Ty), Prf)
  sumParts t = do
    (tTy, pt) <- headPrf sig ctx t
    case tTy of
      Just x => do
        x' <- kWhnfT sig x
        pure (case x' of
                SumTy a c => ((a, c), pt)
                _ => ((TopTy, TopTy), pt))
      Nothing => pure ((TopTy, TopTy), pt)
  quotParts : Elem -> KM ((Ty, Ty), Prf)
  quotParts q = do
    (qTy, pq) <- headPrf sig ctx q
    case qTy of
      Just x => do
        x' <- kWhnfT sig x
        pure (case x' of
                QuotTy a r => ((a, r), pq)
                _ => ((TopTy, TopTy), pq))
      Nothing => pure ((TopTy, TopTy), pq)


mutual
  ||| A type's reconstructed skeleton — for a prop-ness question the
  ||| kernel answers by inference (bare where nothing reconstructs).
  export
  tySkel : Sig -> Ctx -> Ty -> KM Skel
  tySkel sig ctx t = kOrElse (fst <$> infSkel sig ctx t) (pure (Nd [] []))


||| A LICENCE: what a candidate emits at complete match bindings — the
||| construction of the stating proof of its equation, in the context
||| it is used in.
public export
Licence : Type
Licence = Sig -> Ctx -> KM Prf

||| The licence of a proof ELEMENT: the element as a typed neutral,
||| reflected at its equality prop (its type exposed to the ≡ by
||| recorded δ — an ascription).
export
reflectElem : Elem -> Licence
reflectElem p sig ctx = do
  (pp, pty) <- elemToPrf sig ctx p
  (ptyX, pt) <- exposeK sig ctx pty
  pure (case pt of
          PReflx => PRefl pp
          _ => PRefl (PAt pp ptyX pt))

||| S-INJECTIVITY, derived: from a licence for S x ≐ S y, the licence
||| for x ≐ y is the congruence with the predecessor — an ℕ-elim
||| retraction of S, inlined as a checked λ so the stated sides
||| pred (S x) ≐ pred (S y) join to x ≐ y by β alone. No rule is cited:
||| the foundation notes S-injectivity as derivable, and the kernel has
||| no injectivity node.
export
predCong : Licence -> Licence
predCong lic sig ctx = do
  q <- lic sig ctx
  sk <- chkSkel sig ctx predFn (PiTy NatTy NatTy)
  pure (CPiApp (PChk predFn (PiTy NatTy NatTy) sk) q)
 where
  predFn : Elem
  predFn = PiIntro (NatElim NatIntro0 (CtxVar 1) (CtxVar 0))

||| A LICENCE LEAF: the licence's proof, the licence's own
||| normalization proofs bridging its raw sides to the stored spelling
||| (pL ▷ lRaw ≐ lN, pR ▷ rRaw ≐ rN: a candidate stored normalized is
||| licensed from its raw type by transitivity over the leaf), and the
||| orientation. States lN ≐ rN (rN ≐ lN when flipped) — a leaf the
||| kernel reads ⇒.
export
licLeaf : Sig -> Ctx -> Licence -> Prf -> Prf -> Bool -> KM Prf
licLeaf sig ctx lic pL pR flip = do
  base <- lic sig ctx
  let leaf = pTrans (pSym pL) (pTrans base pR)
  pure (if flip then pSym leaf else leaf)

||| One REWRITE on a side: the leaf (a licence leaf, spelled in the root
||| context) placed at `path` in `t` inside the congruence skeleton of
||| the position — weakened by the binders crossed, converted (PAt)
||| where the position's type is spelled otherwise than the leaf's —
||| giving the proof of t ≐ t′ and t′.
export
rwPrf : Sig -> Ctx -> Maybe Ty -> Elem -> List Nat -> Prf -> KM (Prf, Elem)
rwPrf sig ctx tyRoot t path leaf = do
  (_, rN, lty) <- kPrfS sig ctx leaf
  wrapAt sig ctx tyRoot 0 t path (\ctx', mty, b, _ => do
    let leafW = substPrf leaf (wkN b)
    let ltyW = substTy lty (wkN b)
    -- the positional match: the stated equation's type meets the
    -- position's by β, or arrives converted
    leafP <- case mty of
      Nothing => pure leafW
      Just e => do
        ok <- tyAgreeB sig e ltyW
        if ok then pure leafW else do
          md <- deltaPrf sig ltyW e
          case md of
            Just pt => pure (PAt leafW e pt)
            Nothing => kerr "proof: no δ-conversion between the stated type and the position's [stated: \{show ltyW}; position: \{show e}]"
    pure (leafP, substElem rN (wkN b)))

||| A proof of t ≐ t′ where t′ is t with ONE child rewritten: the
||| child's proof placed at index i inside the congruence skeleton of
||| the position (the child is proved in its own context and type,
||| which wrapAt computes as the kernel's node does).
export
congAt : Sig -> Ctx -> Maybe Ty -> Elem -> Nat -> Prf -> KM Prf
congAt sig ctx mty t i q =
  fst <$> wrapAt sig ctx mty 0 t [i] (\_, _, _, u => pure (q, u))

||| A proof-irrelevance leaf at a type (exposed to its prop head by δ,
||| the conversion around the leaf), with the type's skeleton.
export
irrelAt : Sig -> Ctx -> Ty -> KM Prf
irrelAt sig ctx ty = do
  (tyX, pt) <- exposeK sig ctx ty
  sk <- tySkel sig ctx tyX
  pure (convWrap pt tyX (PIrrel sk))

||| A type-directed leaf under the conversion that exposes the type's
||| head (the leaf is built from the exposed, β-whnf'd type).
export
leafAt : Sig -> Ctx -> Ty -> (Ty -> KM Prf) -> KM Prf
leafAt sig ctx ty mk = do
  (tyX, pt) <- exposeK sig ctx ty
  ty' <- kWhnfT sig tyX
  convWrap pt tyX <$> mk ty'

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
||| match the engine found but could not write the proof of is an
||| engine-bug signal, reported as PROOF-FAIL and dropped (the search
||| goes on with its other routes).
export
runPA : String -> KM a -> Maybe a
runPA label m = case runKM m certFuel of
  Right (v, _) => Just v
  Left e => audit "PROOF-FAIL \{label} | \{e}" Nothing

||| Σ-lemma names a proof relies on: the heads of its reflection
||| leaves' proof elements (hypothesis proofs are variable-headed and
||| contribute nothing). Display only.
export
hintNamesP : Prf -> List String
hintNamesP p = go p
 where
  headName : Prf -> List String
  headName (PSelf (SigVar x _)) = [x]
  headName (PSelf (PiApp f _)) = headName (PSelf f)
  headName (PChk (SigVar x _) _ _) = [x]
  headName (CPiApp f _) = headName f
  headName (PAt q _ _) = headName q
  headName _ = []
  go : Prf -> List String
  go (PRefl q) = headName q
  go (PSym q) = go q
  go (PTrans q r) = go q ++ go r
  go (PTransAt q _ r) = go q ++ go r
  go (PConv pt _ q) = go pt ++ go q
  go (PAt q _ pt) = go q ++ go pt
  go (PEtaPi q) = go q
  go (PEtaSigma q r) = go q ++ go r
  go (PQuotWit (Just q)) = go q
  go (PInj q) = go q
  go (PPrfCong _ _ q) = go q
  go q = case congChildren q of
           Just cs => concatMap go cs
           Nothing => []

||| A path leaf's spine stated (for the elaborator's own path leaves).
export
pathArgsB : Sig -> Ctx -> QSig -> Nat -> SubNorm -> Maybe (List Prf)
pathArgsB sig ctx sg k th =
  case runKM (pathArgs sig ctx sg k th) certFuel of
    Right (qs, _) => Just qs
    Left _ => Nothing

||| A proof element as a reflected typed neutral (for the elaborator's
||| own proof leaves).
export
prfOfElem : Sig -> Ctx -> Elem -> Maybe Prf
prfOfElem sig ctx p =
  case runKM (do (pp, pty) <- elemToPrf sig ctx p
                 (ptyX, pt) <- exposeK sig ctx pty
                 pure (case pt of
                         PReflx => PRefl pp
                         _ => PRefl (PAt pp ptyX pt))) certFuel of
    Right (q, _) => Just q
    Left _ => Nothing

