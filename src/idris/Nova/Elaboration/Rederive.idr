module Nova.Elaboration.Rederive

-- RE-DERIVATION: a bare term as a derivation (docs/NovaKernel.txt
-- §8). What the elaborator did not elaborate — a hole's solution, a
-- recovered motive, an inferred type standing as an annotation, an
-- engine leaf, a carrier's embedded piece — is DERIVED against its
-- type by the same bidirectional walk the kernel's reader takes,
-- BUILDING instead of checking. Nothing here is trusted: it is a
-- proposer beside the discharge engine, and every derivation it
-- builds is read by the kernel (Nova.Kernel) before it counts. The
-- kernel imports nothing from here.

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
        Just (SigDef delta _ a ty _ _) => do
          qs <- rdSpine sig ctx (toList delta) (toList es)
          let tyI = substTy ty (embed es)
          leaf <- atPos (DDelta x qs) tyI mty
          (r, p, mt) <- go (Just tyI) (substElem a (embed es))
          pure (r, dTrans leaf p, mt)
        Just (SigDecl delta _ ty _) => pure (SigVar x es, DReflx, Just (substTy ty (embed es)))
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
                                                Just (SigDef _ _ _ _ _ _) => Just x
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
            Just (SigDef delta _ _ ty _ _) => refAt delta ty
            Just (SigDecl delta _ ty _) => refAt delta ty
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
        Just (SigDef delta _ _ TopTy _ _) => DRef x <$> rdSpine sig ctx (toList delta) (toList es)
        Just (SigDecl delta _ TopTy _) => DRef x <$> rdSpine sig ctx (toList delta) (toList es)
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
