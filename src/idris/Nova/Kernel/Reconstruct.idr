module Nova.Kernel.Reconstruct

-- The elaborator's DERIVATION EMISSION pass (docs/NovaPipeline.txt,
-- "The derivation rework", phase 3): untrusted machinery that turns
-- the elaborator's artifacts (core terms plus annotation skeletons —
-- motives, expected types, discharge certificates) into
-- NovaDerivations.txt derivations, run by the elaborator itself at
-- item acceptance. The emitted derivations are what the seat hands
-- the trusted replay kernel (Nova.Kernel.Derivation, acceptDefItem
-- and kin); an emission failure (Nothing) drops the item to the
-- documented residue, where the old kernel's verdict stands alone —
-- incompleteness here is a coverage question, never a soundness one.
--
-- Historically this module was the phase-2 RECONSTRUCTOR, shadowing
-- the old kernel item by item until the seat flipped; the guessing
-- machinery (motive synthesis, endpoint bridges, instantiation
-- searches) remains because the artifacts still lose information the
-- elaborator once had — each consolidation slice that records more
-- at elaboration time retires a guess here.

import Data.List
import Data.Maybe
import Data.SnocList
import Data.SortedMap
import Data.IORef
import Debug.Trace
import System

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT
import Nova.Kernel
import Nova.Kernel.Derivation

%default covering

-- NOVA_RECON_DEBUG=1 prints the first-failure spine of a bailing
-- reconstruction (untrusted diagnostics; never touches replay)
reconDebug : Bool
reconDebug = unsafePerformIO (isJust <$> getEnv "NOVA_RECON_DEBUG")

dbg : Lazy String -> Maybe a -> Maybe a
dbg msg Nothing = if reconDebug then trace (force msg) Nothing else Nothing
dbg _ x = x

-- local copies of the kernel's (private) skeleton helpers
childAt : Nat -> Skel -> Skel
childAt i (Nd _ cs) = case getAt i cs of
  Just s => s
  Nothing => Nd [] []

payload : (Payload -> Maybe a) -> Skel -> Maybe a
payload f (Nd ps _) = go ps
 where
  go : List Payload -> Maybe a
  go [] = Nothing
  go (p :: rest) = case f p of
    Just x => Just x
    Nothing => go rest

emptySkel : Skel
emptySkel = Nd [] []

ctxAt : Ctx -> Nat -> Maybe Ty
ctxAt [<] _ = Nothing
ctxAt (rest :< ty) Z = Just (substTy ty Wk)
ctxAt (rest :< ty) (S n) = map (\t => substTy t Wk) (ctxAt rest n)

-- payload projections (local: the kernel's are private)
pMot : Payload -> Maybe (Ty, Skel)
pMot (PMotive t s) = Just (t, s)
pMot _ = Nothing

pSw : Payload -> Maybe ECert
pSw (PSwitch c) = Just c
pSw _ = Nothing

pExp : Payload -> Maybe (Ty, ECert)
pExp (PExpose t c) = Just (t, c)
pExp _ = Nothing

pRefl : Payload -> Maybe ECert
pRefl (PReflEq c) = Just c
pRefl _ = Nothing

e2m : Either e a -> Maybe a
e2m (Right x) = Just x
e2m (Left _) = Nothing

pQC : Payload -> Maybe (List ECert)
pQC (PQCoh cs) = Just cs
pQC _ = Nothing

pWDc : Payload -> Maybe ECert
pWDc (PWD c) = Just c
pWDc _ = Nothing

pIntro : Payload -> Maybe (Ty, Skel)
pIntro (PIntroTy t s) = Just (t, s)
pIntro _ = Nothing

isIntro : Payload -> Bool
isIntro (PIntroTy _ _) = True
isIntro _ = False

pSqE : Payload -> Maybe (Elem, Skel, Elem, Skel)
pSqE (PSquashElim e se b sb) = Just (e, se, b, sb)
pSqE _ = Nothing

pSqW : Payload -> Maybe (Elem, Skel)
pSqW (PSquashWit e s) = Just (e, s)
pSqW _ = Nothing

pNuC : Payload -> Maybe (Elem, Skel, Elem, Skel, Elem, Skel)
pNuC (PNuCoind r skR pw skp qw skq) = Just (r, skR, pw, skp, qw, skq)
pNuC _ = Nothing

isSw : Payload -> Bool
isSw (PSwitch _) = True
isSw _ = False

isExp : Payload -> Bool
isExp (PExpose _ _) = True
isExp _ = False

dropP : (Payload -> Bool) -> Skel -> Skel
dropP f (Nd ps cs) = Nd (filter (not . f) ps) cs

unsnocL : List a -> Maybe (List a, a)
unsnocL [] = Nothing
unsnocL [x] = Just ([], x)
unsnocL (x :: xs) = do (i, l) <- unsnocL xs; pure (x :: i, l)

||| A β-only certificate: no bridge, no steps, an FBeta final.
betaOnly : ECert -> Bool
betaOnly (MkECertF Nothing [] FBeta) = True
betaOnly _ = False

fuelR : Nat
fuelR = 1000000

-- ===== MEMOIZED EMISSION (docs/NovaPipeline.txt, phase 3) =====
-- The emission pass is a tree of alternatives, and every alternative
-- re-runs everything beneath it — identical sub-problems are solved
-- hundreds of times on a failing body (measured: millions of
-- normalizations on one item). The memo tables make each distinct
-- (context, subject, type) sub-problem cost one solution per item;
-- FAILURES are cached too, which is what stops the retry storms.
-- Keys are the spellings' Show output (structural, hence injective);
-- Σ is fixed within one item, so the tables clear at each emission
-- entry. Untrusted side only — replay never sees a cache, so a
-- cache bug is wasted work or incompleteness, never unsoundness.

%noinline
memoNfE : IORef (SortedMap String (Maybe Elem))
memoNfE = unsafePerformIO (newIORef empty)

%noinline
memoNfT : IORef (SortedMap String (Maybe Ty))
memoNfT = unsafePerformIO (newIORef empty)

%noinline
memoChk : IORef (SortedMap String (Maybe Deriv))
memoChk = unsafePerformIO (newIORef empty)

%noinline
memoInf : IORef (SortedMap String (Maybe (Deriv, Ty)))
memoInf = unsafePerformIO (newIORef empty)

%noinline
memoTy : IORef (SortedMap String (Maybe Deriv))
memoTy = unsafePerformIO (newIORef empty)

withMemo : IORef (SortedMap String (Maybe a)) -> String -> Lazy (Maybe a) -> Maybe a
withMemo ref k act = unsafePerformIO $ do
  m <- readIORef ref
  case lookup k m of
    Just v => pure v
    Nothing => do
      let v = force act
      modifyIORef ref (insert k v)
      pure v

%noinline
clearMemos : () -> Maybe ()
clearMemos _ = unsafePerformIO $ do
  writeIORef memoNfE empty
  writeIORef memoNfT empty
  writeIORef memoChk empty
  writeIORef memoInf empty
  writeIORef memoTy empty
  pure (Just ())

nfE : Sig -> Elem -> Maybe Elem
nfE sig e = withMemo memoNfE (show e)
  (case runKM (kElem sig e) fuelR of
     Right (x, _) => Just x
     Left _ => Nothing)

nfT : Sig -> Ty -> Maybe Ty
nfT sig t = withMemo memoNfT (show t)
  (case runKM (kTy sig t) fuelR of
     Right (x, _) => Just x
     Left _ => Nothing)

wkN : Nat -> Elem -> Elem
wkN Z e = e
wkN (S n) e = wkN n (substElem e Wk)

setAtL : Nat -> a -> List a -> Maybe (List a)
setAtL _ _ [] = Nothing
setAtL Z x (_ :: rest) = Just (x :: rest)
setAtL (S n) x (y :: rest) = (y ::) <$> setAtL n x rest

||| Certificate translation (the retirement map, executable): an
||| equality derivation for Γ ⊦ l ≐ r : ty from an ECert.
export
reEq : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> Maybe Deriv

||| … with optional pre-derived endpoint typings (formation-threaded
||| inversion at a ⋆ goal), each concluding at the raw equation type.
reEqEnds : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty ->
           Maybe (Deriv, Deriv) -> Maybe Deriv

||| … and for type equations Γ ⊦ a ≐ b — the ends are optional
||| endpoint FORMATIONS (presupposition-projected by the caller: a
||| switch's inferred side, an expose's checked side), replacing bare
||| re-derivation of spellings the certificate already speaks for.
reEqTyEnds : Sig -> Ctx -> ECert -> Ty -> Ty ->
             (Maybe Deriv, Maybe Deriv) -> Maybe Deriv

||| The pre-bridge variant that REPORTS WHERE IT REACHED: when the
||| far side is untouched by steps, the chain closes at its own
||| β-normal end — which may spell differently from the engine's
||| recorded target while meaning the same type — and the caller
||| carries on at the reached spelling.
reEqTyReach : Sig -> Ctx -> ECert -> Ty -> Ty -> Maybe (Deriv, Ty)

export
reEqTy : Sig -> Ctx -> ECert -> Ty -> Ty -> Maybe Deriv

closeE : Sig -> Ctx -> Ty -> Deriv -> Elem -> Deriv -> Elem -> Final -> Maybe Deriv
closeT : Sig -> Ctx -> Deriv -> Ty -> Deriv -> Ty -> Final -> Maybe Deriv

mutual
  ||| Expose a synthesized type's head by normalization, coercing the
  ||| derivation along the oracle when the spelling changes.
  expose : Sig -> (Deriv, Ty) -> Maybe (Deriv, Ty)
  expose sig (d, ty) = do
    tyN <- nfT sig ty
    if tyN == ty
      then Just (d, ty)
      else Just (DElTyCoe (DNfExpandTy (DPresupElTy d)) d, tyN)

  ||| Formation, skeleton-guided (pass emptySkel for spellings whose
  ||| skeleton is unavailable — anything needing a payload then bails).
  export
  reTy : Sig -> Ctx -> Ty -> Skel -> Maybe Deriv
  reTy sig ctx ty (Nd [] []) =
    withMemo memoTy "\{show ctx}|T|\{show ty}"
      (reTyB sig ctx ty emptySkel)
  reTy sig ctx ty sk = reTyB sig ctx ty sk

  reTyB : Sig -> Ctx -> Ty -> Skel -> Maybe Deriv
  reTyB sig ctx Ty.ZeroTy sk = Just DTyZero
  reTyB sig ctx Ty.OneTy sk = Just DTyOne
  reTyB sig ctx Ty.NatTy sk = Just DTyNat
  reTyB sig ctx Ty.UniverseTy sk = Just DTyUniv
  reTyB sig ctx Ty.PropTy sk = Just DTyProp
  reTyB sig ctx (Ty.PiTy a b) sk =
    [| DTyPi (reTy sig ctx a (childAt 0 sk)) (reTy sig (ctx :< a) b (childAt 1 sk)) |]
  reTyB sig ctx (Ty.SigmaTy a b) sk =
    [| DTySigma (reTy sig ctx a (childAt 0 sk)) (reTy sig (ctx :< a) b (childAt 1 sk)) |]
  reTyB sig ctx (Ty.SumTy a b) sk =
    [| DTySum (reTy sig ctx a (childAt 0 sk)) (reTy sig ctx b (childAt 1 sk)) |]
  reTyB sig ctx (El e) sk = DTyEl <$> reCheck sig ctx e Ty.UniverseTy (childAt 0 sk)
  reTyB sig ctx (Prf e) sk = DTyPrf <$> reCheck sig ctx e Ty.PropTy (childAt 0 sk)
  reTyB sig ctx (Ty.Quotient a r) sk = do
    da <- reTy sig ctx a (childAt 0 sk)
    dr <- reCheck sig (ctx :< a :< substTy a Wk) r Ty.PropTy (childAt 1 sk)
    pure (DTyQuot da dr)
  reTyB sig ctx (Ty.SigVar x es) sk =
    case sigLookup x sig of
      Just (SigTyDef delta _ _) => DTySig x <$> reSubN sig ctx es (toList delta)
      Just (SigTyDecl delta _) => DTySig x <$> reSubN sig ctx es (toList delta)
      _ => Nothing
  reTyB sig ctx (Ty.NuTy f) sk = DTyNu <$> rePoly sig ctx f
  reTyB sig ctx (QSort sg k es) sk = do
    dSig <- reQSig sig ctx sg
    ds <- reQSpine sig ctx sg k (toList es)
    pure (DTyQSort k dSig ds)

  ||| A signature's qctx formation, rebuilt from its spelling (the
  ||| ToS zone threaded to type the embedded pieces at their spelled
  ||| domains).
  reQSig : Sig -> Ctx -> QSig -> Maybe Deriv
  reQSig sig ctx sg = DQSig . fst <$> go (reverse sg)
   where
    go : List QTy -> Maybe (Deriv, SnocList QTy)
    go [] = Just (DQCtxEmpty, [<])
    go (e :: earlier) = do
      (dPhi, phi) <- go earlier
      dE <- reQTy sig ctx phi e
      pure (DQCtxExt dPhi dE, phi :< e)

  reQTy : Sig -> Ctx -> SnocList QTy -> QTy -> Maybe Deriv
  reQTy sig ctx phi QU = Just DQTyUniv
  reQTy sig ctx phi (QEl t) = DQTyEl . fst <$> reQTm sig ctx phi t
  reQTy sig ctx phi (QPiExt a b) =
    [| DQTyPiExt (reTy sig ctx a emptySkel)
                 (reQTy sig (ctx :< a) (phiWkNova phi) b) |]
  reQTy sig ctx phi (QPiInd t b) = do
    (dt, _) <- reQTm sig ctx phi t
    db <- reQTy sig ctx (phi :< QEl t) b
    pure (DQTyPiInd dt db)

  reQTm : Sig -> Ctx -> SnocList QTy -> QTm -> Maybe (Deriv, QTy)
  reQTm sig ctx phi (QVar i) = do
    a <- phiAt phi i
    pure (DQTmVar i, a)
  reQTm sig ctx phi (QAppE f e) = do
    (df, fty) <- reQTm sig ctx phi f
    case fty of
      QPiExt a b => do
        de <- reCheck sig ctx e a emptySkel
        pure (DQTmAppExt df de, substQTy b (Ext Id e))
      _ => Nothing
  reQTm sig ctx phi (QAppI f a) = do
    (df, fty) <- reQTm sig ctx phi f
    case fty of
      QPiInd u b => do
        (da, _) <- reQTm sig ctx phi a
        pure (DQTmAppInd df da, qSubTy (QSExt QSId a) b)
      _ => Nothing
  reQTm sig ctx phi (QEqC l r u) = do
    (dl, _) <- reQTm sig ctx phi l
    (dr, _) <- reQTm sig ctx phi r
    pure (DQTmEq dl dr, QU)

  ||| A constructor/sort spine, entrywise at the reflected telescope.
  reQSpine : Sig -> Ctx -> QSig -> Nat -> List Elem -> Maybe (List Deriv)
  reQSpine sig ctx sg k args = do
    entry <- qEntry sg k
    (tel, _, _) <- eitherToMaybe (reflTel sg (qwAt k) entry)
    goSp 0 tel args
   where
    eitherToMaybe : Either e a -> Maybe a
    eitherToMaybe (Right x) = Just x
    eitherToMaybe (Left _) = Nothing
    goSp : Nat -> List Ty -> List Elem -> Maybe (List Deriv)
    goSp i tel [] = Just []
    goSp i tel (a :: rest) = do
      want <- telInst tel i args
      d <- reCheck sig ctx a want emptySkel
      ds <- goSp (S i) tel rest
      pure (d :: ds)

  ||| Polynomial formation, structural (codes reconstructed bare).
  rePoly : Sig -> Ctx -> Poly -> Maybe Deriv
  rePoly sig ctx PHole = Just DPolyHole
  rePoly sig ctx (PConst a) =
    DPolyConst <$> reCheck sig ctx a Ty.UniverseTy emptySkel
  rePoly sig ctx (PProd f g) =
    [| DPolyProd (rePoly sig ctx f) (rePoly sig ctx g) |]
  rePoly sig ctx (PSum f g) =
    [| DPolySum (rePoly sig ctx f) (rePoly sig ctx g) |]
  rePoly sig ctx (PSigma a f) = do
    da <- reCheck sig ctx a Ty.UniverseTy emptySkel
    df <- rePoly sig (ctx :< El a) f
    pure (DPolySigma da df)
  rePoly sig ctx (PPi a f) = do
    da <- reCheck sig ctx a Ty.UniverseTy emptySkel
    df <- rePoly sig (ctx :< El a) f
    pure (DPolyPi da df)

  ||| A normal substitution against a target telescope (Σ-entry
  ||| contexts are outermost-first lists).
  reSubN : Sig -> Ctx -> SubNorm -> List Ty -> Maybe Deriv
  reSubN sig ctx es delta = go (toList es) delta
   where
    go : List Elem -> List Ty -> Maybe Deriv
    go [] [] = Just DSubNEmpty
    go args tys = do
      (initArgs, lastArg) <- unsnocL args
      (initTys, lastTy) <- unsnocL tys
      dRest <- go initArgs initTys
      -- the entry type's formation over the target prefix
      let prefixCtx = [<] <>< initTys
      dA <- reTy sig prefixCtx lastTy emptySkel
      dE <- reCheck sig ctx lastArg
              (substTy lastTy (embed ([<] <>< initArgs))) emptySkel
      pure (DSubNExt dRest dA dE)

  ||| Inference, mirroring kInferE's shape; returns the derivation
  ||| and its concluded type.
  export
  reInfer : Sig -> Ctx -> Elem -> Skel -> Maybe (Deriv, Ty)
  reInfer sig ctx e (Nd [] []) =
    withMemo memoInf "\{show ctx}|I|\{show e}"
      (reInferB sig ctx e emptySkel)
  reInfer sig ctx e sk = reInferB sig ctx e sk

  reInferB : Sig -> Ctx -> Elem -> Skel -> Maybe (Deriv, Ty)
  reInferB sig ctx e sk =
    case payload pIntro sk of
      Just (t, _) => do
        d <- reCheck sig ctx e t (dropP isIntro sk)
        pure (d, t)
      Nothing => reInferGo sig ctx e sk

  reInferGo : Sig -> Ctx -> Elem -> Skel -> Maybe (Deriv, Ty)
  reInferGo sig ctx (CtxVar i) sk = do
    ty <- ctxAt ctx i
    pure (DElVar i, ty)
  reInferGo sig ctx (Elem.SigVar x es) sk =
    case sigLookup x sig of
      Just (SigDef delta _ _ a) => do
        d <- reSubN sig ctx es (toList delta)
        pure (DElSig x d, substTy a (embed es))
      Just (SigDecl delta _ a) => do
        d <- reSubN sig ctx es (toList delta)
        pure (DElSig x d, substTy a (embed es))
      _ => Nothing
  reInferGo sig ctx (PiApp f e) sk =
    (do (df, fty) <- reInfer sig ctx f (childAt 0 sk) >>= expose sig
        case fty of
          Ty.PiTy a b => do
            de <- reCheck sig ctx e a (childAt 1 sk)
                  <|> reCheckF sig ctx e a (childAt 1 sk)
                        (DInvPiDom (DPresupElTy df))
            -- the retained codomain premise: re-derived when bare
            -- derivation is possible (cheap, no sharing), else by
            -- inv-pi-cod of the head's presupposed Π formation (a
            -- hole-carrying codomain is underivable bare)
            db <- reTy sig (ctx :< a) b emptySkel
                  <|> Just (DInvPiCod (DPresupElTy df))
            pure (DElPiE df de db, substTy b (Ext Id e))
          _ => Nothing)
    <|> (do
      -- the ENDO guess: an uninferable applied head (a normalized
      -- eliminator iterating a step) tried at a → a, the argument's
      -- own type — conclude arbitrates
      (de, a) <- reInfer sig ctx e (childAt 1 sk)
      df <- reCheck sig ctx f (Ty.PiTy a (substTy a Wk)) (childAt 0 sk)
      db <- reTy sig (ctx :< a) (substTy a Wk) emptySkel
            <|> Just (DInvPiCod (DPresupElTy df))
      pure (DElPiE df de db, a))
  reInferGo sig ctx (Corec pf a body x) sk = do
    d <- reCheckGo sig ctx (Corec pf a body x) (Ty.NuTy pf) sk
    pure (d, Ty.NuTy pf)
  reInferGo sig ctx (SigmaElim1 t) sk = do
    (dt, tty) <- reInfer sig ctx t (childAt 0 sk) >>= expose sig
    case tty of
      Ty.SigmaTy a _ => pure (DElSigmaE1 dt, a)
      _ => Nothing
  reInferGo sig ctx (SigmaElim2 t) sk = do
    (dt, tty) <- reInfer sig ctx t (childAt 0 sk) >>= expose sig
    case tty of
      Ty.SigmaTy _ b => pure (DElSigmaE2 dt, substTy b (Ext Id (SigmaElim1 t)))
      _ => Nothing
  reInferGo sig ctx (Let a b) sk = do
    (da, aty) <- reInfer sig ctx a (childAt 0 sk)
    let hyp = Prf (Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aty Wk))
    (db, bty) <- reInfer sig (ctx :< aty :< hyp) b (childAt 1 sk)
    pure (DElLet da db, substTy bty (Ext (Ext Id a) Star))
  reInferGo sig ctx (NatElim z s t) sk =
    case payload pMot sk of
      Nothing => do
        -- no motive annotation (a spelling arisen from normalization,
        -- not from the item body): the CONSTANT-MOTIVE guess — A1's
        -- de facto fragment, recovered bare
        (dz, zty) <- reInfer sig ctx z emptySkel
        let mot = substTy zty Wk
        dmot <- reTy sig (ctx :< Ty.NatTy) mot emptySkel
        ds <- reCheck sig (ctx :< Ty.NatTy :< mot) s
                (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) emptySkel
        dt <- reCheck sig ctx t Ty.NatTy emptySkel
        pure (DElNatE dmot dz ds dt, zty)
      Just (mot, motSk) => do
        dmot <- reTy sig (ctx :< Ty.NatTy) mot motSk
        -- branch goal formations: the motive instantiated along the
        -- branch's substitution (ty-sub via cong-fix over refl)
        let zF = DPresupTyL (DTySubCongFix
                   (DSubExt DSubId DTyNat DElNatZ) (DTyRefl dmot))
        let sSub = DSubComp DSubWk
                     (DSubExt DSubWk DTyNat (DElNatS (DElVar 0)))
        let sF = DPresupTyL (DTySubCongFix sSub (DTyRefl dmot))
        dz <- reCheckF sig ctx z (substTy mot (Ext Id NatIntro0)) (childAt 0 sk) zF
        ds <- reCheckF sig (ctx :< Ty.NatTy :< mot) s
                (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) (childAt 1 sk) sF
        dt <- reCheck sig ctx t Ty.NatTy (childAt 2 sk)
        pure (DElNatE dmot dz ds dt, substTy mot (Ext Id t))
  reInferGo sig ctx (SumElim l r t) sk = do
    (mot, motSk) <- payload pMot sk
    (dt, tty) <- reInfer sig ctx t (childAt 2 sk) >>= expose sig
    case tty of
      Ty.SumTy a b => do
        dmot <- reTy sig (ctx :< Ty.SumTy a b) mot motSk
        da <- reTy sig ctx a emptySkel
        db <- reTy sig ctx b emptySkel
        let wkOf = \d => DPresupTyL (DTySubCongFix DSubWk (DTyRefl d))
        let lF = DPresupTyL (DTySubCongFix
                   (DSubExt DSubWk (DTySum da db)
                     (DElSumI1 (DElVar 0) (wkOf db)))
                   (DTyRefl dmot))
        dl <- reCheckF sig (ctx :< a) l (substTy mot (Ext Wk (Inj1 (CtxVar 0)))) (childAt 0 sk) lF
        let rF = DPresupTyL (DTySubCongFix
                   (DSubExt DSubWk (DTySum da db)
                     (DElSumI2 (DElVar 0) (wkOf da)))
                   (DTyRefl dmot))
        dr <- reCheckF sig (ctx :< b) r (substTy mot (Ext Wk (Inj2 (CtxVar 0)))) (childAt 1 sk) rF
        pure (DElSumE dt dmot dl dr, substTy mot (Ext Id t))
      _ => Nothing
  reInferGo sig ctx NatIntro0 sk = Just (DElNatZ, Ty.NatTy)
  reInferGo sig ctx (NatIntro1 t) sk = do
    d <- reCheck sig ctx t Ty.NatTy (childAt 0 sk)
    pure (DElNatS d, Ty.NatTy)
  reInferGo sig ctx OneIntro sk = Just (DElOneI, Ty.OneTy)
  -- universe and Ω codes
  reInferGo sig ctx Elem.ZeroTy sk = Just (DCodeZero, Ty.UniverseTy)
  reInferGo sig ctx Elem.OneTy sk = Just (DCodeOne, Ty.UniverseTy)
  reInferGo sig ctx Elem.NatTy sk = Just (DCodeNat, Ty.UniverseTy)
  reInferGo sig ctx (Elem.PiTy a b) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    db <- reCheck sig (ctx :< El a) b Ty.UniverseTy (childAt 1 sk)
    pure (DCodePi da db, Ty.UniverseTy)
  reInferGo sig ctx (Elem.SigmaTy a b) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    db <- reCheck sig (ctx :< El a) b Ty.UniverseTy (childAt 1 sk)
    pure (DCodeSigma da db, Ty.UniverseTy)
  reInferGo sig ctx (Elem.SumTy a b) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    db <- reCheck sig ctx b Ty.UniverseTy (childAt 1 sk)
    pure (DCodeSum da db, Ty.UniverseTy)
  reInferGo sig ctx (Elem.QuotTy a r) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    dr <- reCheck sig (ctx :< El a :< substTy (El a) Wk) r Ty.PropTy (childAt 1 sk)
    pure (DCodeQuot da dr, Ty.UniverseTy)
  reInferGo sig ctx (Elem.EqTy l r t) sk = do
    dt <- reTy sig ctx t (childAt 2 sk)
    dl <- reCheck sig ctx l t (childAt 0 sk)
    dr <- reCheck sig ctx r t (childAt 1 sk)
    pure (DCodeEq dt dl dr, Ty.PropTy)
  reInferGo sig ctx (Squash a) sk = do
    da <- reTy sig ctx a (childAt 0 sk)
    pure (DCodeSquash da, Ty.PropTy)
  reInferGo sig ctx (QSortC sg k es) sk = do
    dSig <- reQSig sig ctx sg
    ds <- reQSpine sig ctx sg k (toList es)
    pure (DCodeQSort k dSig ds, Ty.UniverseTy)
  reInferGo sig ctx (QCtor sg k es) sk = do
    dSig <- reQSig sig ctx sg
    ds <- reQSpine sig ctx sg k (toList es)
    entry <- qEntry sg k
    (tel, _, _) <- e2m (reflTel sg (qwAt k) entry)
    (wEnd, hd) <- e2m (walkVals sg (qwAt k) entry (toList es))
    (srt, idx) <- e2m (pointHead sg wEnd hd)
    pure (DQCtor k dSig ds, QSort sg srt idx)
  reInferGo sig ctx (QElim sg k mots fs es w) sk = do
    dSig <- reQSig sig ctx sg
    let cohCerts = case payload pQC sk of
                     Just cs => cs
                     Nothing => []
    motDs <- goMots (qPositions QKSort sg) mots
    mthDs <- goMths (qPositions QKPoint sg) fs
    cohDs <- goCohs (qPositions QKEq sg) cohCerts
    let dEP = DQEProb (DQDalg (DQMot dSig motDs) mthDs) cohDs
    ds <- reQSpine sig ctx sg k (toList es)
    entry <- qEntry sg k
    o <- qOrdinal QKSort sg k
    motK <- getAt o mots
    dW <- reCheck sig ctx w (QSort sg k es) emptySkel
    pure (DQElim k dEP ds dW,
          substTy motK (Ext (foldl Ext Id (toList es)) w))
   where
    goMots : List Nat -> List Ty -> Maybe (List Deriv)
    goMots [] [] = Just []
    goMots (sj :: sjs) (m :: ms) = do
      sjE <- qEntry sg sj
      (tel, wEnd, _) <- e2m (reflTel sg (qwAt sj) sjE)
      let mctx = foldl (:<) ctx tel
      let selfTy = QSort (substQSig sg wEnd.ups) sj (varSpine (length tel))
      d <- reTy sig (mctx :< selfTy) m emptySkel
      ds <- goMots sjs ms
      pure (d :: ds)
    goMots _ _ = Nothing
    goMths : List Nat -> List Elem -> Maybe (List Deriv)
    goMths [] [] = Just []
    goMths (cj :: cjs) (m :: ms) = do
      mty <- e2m (methodTy sg mots cj)
      d <- reCheck sig ctx m mty emptySkel
      ds <- goMths cjs ms
      pure (d :: ds)
    goMths _ _ = Nothing
    goCohs : List Nat -> List ECert -> Maybe (List Deriv)
    goCohs [] _ = Just []
    goCohs (ej :: ejs) certs = do
      (c, rest) <- the (Maybe (ECert, List ECert)) $ case certs of
                     (c :: cs) => Just (c, cs)
                     [] => Nothing
      (dtel, _, lhs, rhs, cty) <- e2m (coherenceAt sg mots fs ej)
      let cctx = foldl (:<) ctx dtel
      d <- reEq sig cctx c lhs rhs cty
      ds <- goCohs ejs rest
      pure (d :: ds)
  reInferGo sig ctx (Elem.NuTy f) sk = do
    dp <- rePoly sig ctx f
    pure (DCodeNu dp, Ty.UniverseTy)
  reInferGo sig ctx (SigmaIntro u v) sk = do
    -- the CONSTANT-FAMILY guess (a pair in a normalized spelling
    -- carries no family, like an eliminator its motive)
    (du, uty) <- reInfer sig ctx u (childAt 0 sk)
    (dv, vty) <- reInfer sig ctx v (childAt 1 sk)
    let b = substTy vty Wk
    db <- reTy sig (ctx :< uty) b emptySkel
    pure (DElSigmaI du db dv, Ty.SigmaTy uty b)
  reInferGo sig ctx (Class a) sk = Nothing       -- intro: checking-only
  reInferGo sig ctx (Out t) sk = do
    (dt, tty) <- reInfer sig ctx t (childAt 0 sk) >>= expose sig
    case tty of
      Ty.NuTy f => do
        dp <- rePoly sig ctx f
        pure (DElNuE dp dt, El (reflectPoly f (Elem.NuTy f)))
      _ => Nothing
  reInferGo sig ctx (QuotElim f q) sk = do
    (mot, motSk) <- dbg "quotE: no motive payload" (payload pMot sk)
    wd <- dbg "quotE: no wd payload" (payload pWDc sk)
    (dq, qty) <- dbg "quotE: scrutinee" (reInfer sig ctx q (childAt 1 sk) >>= expose sig)
    case qty of
      Ty.Quotient a r => do
        dmot <- dbg "quotE: motive" (reTy sig (ctx :< Ty.Quotient a r) mot motSk)
        -- the body goal's formation: the motive instantiated along
        -- ⟨wk, class ☐₀⟩ — threaded so a ⋆ body's endpoints arrive
        -- by inversion instead of bare re-derivation
        let bodyTy = substTy mot (Ext Wk (Class (CtxVar 0)))
        let mBodyF = do
              dRelW <- reCheck sig
                         (ctx :< a :< substTy a Wk
                              :< substTy (substTy a Wk) Wk)
                         (substElem r (under (under Wk))) Ty.PropTy emptySkel
              let dCls = DElQuotI (DElVar 0) dRelW
              let dS = DSubExt DSubWk (DPresupElTy dq) dCls
              pure (DPresupTyL (DTySubCongFix dS (DTyRefl dmot)))
        df <- dbg "quotE: body"
                (reCheck sig (ctx :< a) f bodyTy (childAt 0 sk)
                 <|> (do bodyF <- mBodyF
                         reCheckF sig (ctx :< a) f bodyTy (childAt 0 sk) bodyF))
        let wk3 = Chain Wk (Chain Wk Wk)
        let wdCtx = ctx :< a :< substTy a Wk :< Prf r
        -- the well-definedness endpoints are SUBSTITUTION INSTANCES
        -- of the body derivation: the body's binder sent to ☐₂ (a
        -- weakening) and to ☐₁ (an extension)
        let wk3S = DSubComp (DSubComp DSubWk DSubWk) DSubWk
        let endL = DPresupElL (DElSubCongFix (DSubComp DSubWk DSubWk)
                     (DElRefl df))
        let bodyTyI1 = substTy mot (Ext wk3 (Class (CtxVar 1)))
        let bodyTyI2 = substTy mot (Ext wk3 (Class (CtxVar 2)))
        let mEndR = do
              dA <- reTy sig ctx a emptySkel
              let endR0 = DPresupElL (DElSubCongFix
                            (DSubExt wk3S dA (DElVar 1)) (DElRefl df))
              if bodyTyI1 == bodyTyI2 then Just endR0
                else do
                  -- endR sits at the ☐₁ instance; the equation is
                  -- stated at the ☐₂ instance — both Prfs are
                  -- inhabited by the two ends, so code-prop-eq
                  -- carries it across
                  let (Prf _, Prf _) = (bodyTyI1, bodyTyI2)
                    | _ => Nothing
                  let dP = DInvPrfCode (DPresupElTy endR0)
                  let dQ = DInvPrfCode (DPresupElTy endL)
                  let dS = DPresupElL (DElSubCongFix DSubWk (DElRefl endL))
                  let dT = DPresupElL (DElSubCongFix DSubWk (DElRefl endR0))
                  pure (DElTyCoe (DTyPrfCong (DCodePropEq dP dQ dS dT)) endR0)
        dresp <- reEqEnds sig wdCtx wd
                   (substElem f (Ext wk3 (CtxVar 2)))
                   (substElem f (Ext wk3 (CtxVar 1)))
                   (substTy mot (Ext wk3 (Class (CtxVar 2))))
                   (map (\dR => (endL, dR)) mEndR)
        pure (DElQuotE dq dmot df dresp, substTy mot (Ext Id q))
      _ => Nothing
  reInferGo sig ctx _ sk = Nothing

  ||| Checking: switch/expose payloads translated on the β-only
  ||| route; intro forms structurally; fallback infer-and-α-compare
  ||| (with a β coercion when spellings differ).
  export
  reCheck : Sig -> Ctx -> Elem -> Ty -> Skel -> Maybe Deriv
  reCheck sig ctx e ty (Nd [] []) =
    withMemo memoChk "\{show ctx}|C|\{show e}:\{show ty}"
      (reCheckB sig ctx e ty emptySkel)
  reCheck sig ctx e ty sk = reCheckB sig ctx e ty sk

  reCheckB : Sig -> Ctx -> Elem -> Ty -> Skel -> Maybe Deriv
  reCheckB sig ctx e ty sk =
    case payload pSw sk of
      Just cert => do
        (d, ity) <- reInfer sig ctx e (dropP isSw sk)
        if ity == ty
          then Just d
          else do
            dEq <- reEqTyEnds sig ctx cert ity ty
                     (Just (DPresupElTy d), Nothing)
            pure (DElTyCoe dEq d)
      Nothing =>
        case payload pExp sk of
          Just (tyX, cert) => do
            d <- reCheckGo sig ctx e tyX (dropP isExp sk)
            dEq <- reEqTyEnds sig ctx cert ty tyX
                     (Nothing, Just (DPresupElTy d))
            pure (DElTyCoe (DTySym dEq) d)
          Nothing => do
            tyN <- nfT sig ty
            if tyN == ty
              then reCheckGo sig ctx e ty sk
              else
                -- expose the expected type (the old kernel matches
                -- heads up to nf); conclude back at the raw spelling
                case reCheckGo sig ctx e tyN sk of
                  Just d => do
                    dT <- reTy sig ctx ty emptySkel
                    pure (DElTyCoe (DTySym (DNfExpandTy dT)) d)
                  Nothing => reCheckGo sig ctx e ty sk

  ||| Checking WITH the expected type's formation derivation in hand
  ||| (threaded down lambda spines and into ⋆ goals): where plain
  ||| reconstruction cannot re-type a goal's endpoints — normalized
  ||| eliminator spellings, hypothesis-sensitive holes — formation
  ||| INVERSION delivers them from the threaded derivation.
  export
  reCheckF : Sig -> Ctx -> Elem -> Ty -> Skel -> Deriv -> Maybe Deriv
  reCheckF sig ctx (PiIntro f) (Ty.PiTy a b) sk dF = do
    da <- reTy sig ctx a emptySkel <|> Just (DInvPiDom dF)
    df <- reCheckF sig (ctx :< a) f b (childAt 0 sk) (DInvPiCod dF)
    pure (DElPiI da df)
  reCheckF sig ctx Star ty sk dF =
    reCheck sig ctx Star ty sk
    <|> (case (payload pRefl sk, ty) of
          (Just cert, Prf (Elem.EqTy l r t)) =>
            dbg "star-inv: \{show l} EQ \{show r} AT \{show t}"
              (DElEqI <$> reEqEnds sig ctx cert l r t
                           (Just (DInvPrfEqL dF, DInvPrfEqR dF)))
          (Just cert, _) => do
            -- goal not a literal equality prop: expose by nf, ride
            -- the threaded formation both ways
            tyN <- nfT sig ty
            let Prf (Elem.EqTy l r t) = tyN
              | _ => Nothing
            let dFN = DPresupTyR (DNfExpandTy dF)
            d0 <- dbg "star-inv (nf): \{show l} EQ \{show r}"
                    (DElEqI <$> reEqEnds sig ctx cert l r t
                                 (Just (DInvPrfEqL dFN, DInvPrfEqR dFN)))
            pure (DElTyCoe (DTySym (DNfExpandTy dF)) d0)
          _ => Nothing)
  reCheckF sig ctx e ty sk dF =
    reCheck sig ctx e ty sk
    <|> (case payload pSw sk of
          Just cert => do
            (d, ity) <- reInfer sig ctx e (dropP isSw sk)
            dEq <- reEqTyEnds sig ctx cert ity ty
                     (Just (DPresupElTy d), Just dF)
            pure (DElTyCoe dEq d)
          Nothing => Nothing)

  reCheckGo : Sig -> Ctx -> Elem -> Ty -> Skel -> Maybe Deriv
  reCheckGo sig ctx (PiIntro f) ty sk =
    case ty of
      Ty.PiTy a b => do
        da <- dbg "lam: domain \{show a}" (reTy sig ctx a emptySkel)
        df <- dbg "lam: body AT \{show b}" (reCheck sig (ctx :< a) f b (childAt 0 sk))
        pure (DElPiI da df)
      _ => dbg "lam: goal not a Pi: \{show ty}" Nothing
  reCheckGo sig ctx (SigmaIntro u v) ty sk =
    case ty of
      Ty.SigmaTy a b => do
        du <- dbg "pair: fst \{show u} AT \{show a}" (reCheck sig ctx u a (childAt 0 sk))
        db <- dbg "pair: family" (reTy sig (ctx :< a) b emptySkel)
        dv <- dbg "pair: snd \{show v} AT \{show (substTy b (Ext Id u))}" (reCheck sig ctx v (substTy b (Ext Id u)) (childAt 1 sk))
        pure (DElSigmaI du db dv)
      _ => dbg "pair: goal not a Sigma: \{show ty}" Nothing
  reCheckGo sig ctx (Inj1 a) ty sk =
    case ty of
      Ty.SumTy l r => do
        da <- reCheck sig ctx a l (childAt 0 sk)
        dr <- reTy sig ctx r emptySkel
        pure (DElSumI1 da dr)
      _ => Nothing
  reCheckGo sig ctx (Inj2 b) ty sk =
    case ty of
      Ty.SumTy l r => do
        db <- reCheck sig ctx b r (childAt 0 sk)
        dl <- reTy sig ctx l emptySkel
        pure (DElSumI2 db dl)
      _ => Nothing
  reCheckGo sig ctx (Class a) ty sk =
    case ty of
      Ty.Quotient dom rel => do
        da <- reCheck sig ctx a dom (childAt 0 sk)
        dr <- reCheck sig (ctx :< dom :< substTy dom Wk) rel Ty.PropTy emptySkel
        pure (DElQuotI da dr)
      _ => Nothing
  reCheckGo sig ctx e@(QCtor _ _ _) ty sk = do
    (d, ity) <- reInfer sig ctx e sk
    coerce sig ctx d ity ty
  reCheckGo sig ctx (Corec pf a body x) ty sk =
    case ty of
      Ty.NuTy f =>
        if pf == f
          then do
            dp <- rePoly sig ctx f
            da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
            db <- reCheck sig (ctx :< El a) body
                    (substTy (El (reflectPoly f a)) Wk) (childAt 1 sk)
            dx <- reCheck sig ctx x (El a) (childAt 2 sk)
            pure (DElNuI dp da db dx)
          else Nothing
      _ => Nothing
  reCheckGo sig ctx (Let a b) ty sk = do
    (da, aty) <- reInfer sig ctx a (childAt 0 sk)
    let hyp = Prf (Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aty Wk))
    db <- reCheck sig (ctx :< aty :< hyp) b (substTy ty (Chain Wk Wk)) (childAt 1 sk)
    pure (DElLet da db)
  reCheckGo sig ctx (NatElim z st t) ty sk =
    case payload pMot sk of
      Just _ => do
        (d, ity) <- reInferGo sig ctx (NatElim z st t) sk
        coerce sig ctx d ity ty
      Nothing => do
        -- constant motive at the EXPECTED type
        let mot = substTy ty Wk
        dmot <- reTy sig (ctx :< Ty.NatTy) mot emptySkel
        dz <- reCheck sig ctx z ty (childAt 0 sk)
        ds <- reCheck sig (ctx :< Ty.NatTy :< mot) st
                (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) (childAt 1 sk)
        dt <- reCheck sig ctx t Ty.NatTy (childAt 2 sk)
        pure (DElNatE dmot dz ds dt)
  reCheckGo sig ctx (SumElim l r t) ty sk =
    case payload pMot sk of
      Just _ => do
        (d, ity) <- reInferGo sig ctx (SumElim l r t) sk
        coerce sig ctx d ity ty
      Nothing => do
        (dt, tty) <- reInfer sig ctx t (childAt 2 sk) >>= expose sig
        case tty of
          Ty.SumTy a b => do
            let mot = substTy ty Wk
            dmot <- reTy sig (ctx :< Ty.SumTy a b) mot emptySkel
            dl <- reCheck sig (ctx :< a) l (substTy ty Wk) (childAt 0 sk)
            dr <- reCheck sig (ctx :< b) r (substTy ty Wk) (childAt 1 sk)
            pure (DElSumE dt dmot dl dr)
          _ => Nothing
  reCheckGo sig ctx (ZeroElim t) ty sk = do
    dA <- reTy sig ctx ty emptySkel
    dt <- reCheck sig ctx t Ty.ZeroTy (childAt 0 sk)
    pure (DElZeroE dA dt)
  reCheckGo sig ctx Star ty sk =
    case payload pRefl sk of
      Just cert =>
        case ty of
          Prf (Elem.EqTy l r t) => dbg "star-cert: \{show l} EQ \{show r} AT \{show t}" (DElEqI <$> reEq sig ctx cert l r t)
          _ => dbg "star-cert: goal not an eq prop: \{show ty}" Nothing
      Nothing =>
       case payload pNuC sk of
        -- el-nu-coind: ⋆ at an equality prop over a ν type, by
        -- COINDUCTION — invariant, endpoint proof, one-step closure
        Just (r, skR, pw, skp, qw, skq) => do
          tyN <- nfT sig ty
          let Prf (Elem.EqTy l rhs ety) = tyN
            | _ => Nothing
          let Ty.NuTy f = ety
            | _ => Nothing
          let nuT = Ty.NuTy f
          dF <- dbg "coind: poly" (rePoly sig ctx f)
          dT0 <- dbg "coind: t0" (reCheck sig ctx l nuT emptySkel)
          dT1 <- dbg "coind: t1" (reCheck sig ctx rhs nuT emptySkel)
          dR <- dbg "coind: invariant" (reCheck sig (ctx :< nuT :< substTy nuT Wk) r Ty.PropTy skR)
          dP <- dbg "coind: endpoint" (reCheck sig ctx pw (Prf (substElem r (Ext (Ext Id l) rhs))) skp)
          let wk3 = Chain Wk (Chain Wk Wk)
          dQ <- reCheck sig (ctx :< nuT :< substTy nuT Wk :< Prf r) qw
                  (Prf (liftPoly (substPoly f wk3) (substElem r (under (under wk3)))
                          (Out (CtxVar 2)) (Out (CtxVar 1)))) skq
                <|> dbg "coind: closure" Nothing
          let d0 = DElEqI (DElNuCoind dF dT0 dT1 dR dP dQ)
          if ty == tyN then Just d0
            else do
              dTy <- reTy sig ctx ty emptySkel
              pure (DElTyCoe (DTySym (DNfExpandTy dTy)) d0)
        Nothing =>
         case payload pSqW sk of
          Just (w, wSk) =>
            case ty of
              Prf (Squash a) => do
                dw <- dbg "star-wit: \{show w} AT \{show a}" (reCheck sig ctx w a wSk)
                pure (DElSquashI dw)
              _ => dbg "star-wit: goal not a squash: \{show ty}" Nothing
          Nothing =>
            case payload pSqE sk of
              Just (e, ske, b, skb) =>
                case ty of
                  Prf q => do
                    dq <- reCheck sig ctx q Ty.PropTy emptySkel
                    (de, ety) <- reInfer sig ctx e ske
                    etyN <- nfT sig ety
                    de' <- if ety == etyN then Just de
                           else Just (DElTyCoe (DNfExpandTy (DPresupElTy de)) de)
                    case etyN of
                      Prf (Squash a) => do
                        db <- dbg "star-sqe: body" (reCheck sig (ctx :< a) b (substTy (Prf q) Wk) skb)
                        pure (DElSquashEPrf dq de' db)
                      _ => dbg "star-sqe: scrutinee not a squash" Nothing
                  _ => dbg "star-sqe: goal not Prf" Nothing
              -- the ASSUMPTION ROUTE: ⋆ at an equality prop justified
              -- by a hypothesis of that very equality — reflect the
              -- variable, reintroduce (el-eq-i), spellings by the nf
              -- oracle on both ends
              Nothing => do
                tyN <- nfT sig ty
                let Prf (Elem.EqTy a b t) = tyN
                  | _ => Nothing
                d0 <- dbg "star-bare: \{show a} EQ \{show b} AT \{show t}" (byRefl a b t <|> byAssum tyN 0)
                if ty == tyN then Just d0
                  else do
                    dTy <- reTy sig ctx ty emptySkel
                    pure (DElTyCoe (DTySym (DNfExpandTy dTy)) d0)
   where
    -- ⋆ at an equality prop whose sides agree up to nf: el-refl,
    -- the mismatched spellings closed by the nf oracle
    byRefl : Elem -> Elem -> Ty -> Maybe Deriv
    byRefl a b t = do
      aN <- nfE sig a
      bN <- nfE sig b
      let True = aN == bN
        | False => Nothing
      da <- reCheck sig ctx a t emptySkel
      db <- reCheck sig ctx b t emptySkel
      pure $ if a == b then DElEqI (DElRefl da)
                       else DElEqI (DNfEq da db)

    byAssum : Ty -> Nat -> Maybe Deriv
    byAssum tyN i = do
      vty <- ctxAt ctx i
      (do vN <- nfT sig vty
          let True = vN == tyN
            | False => Nothing
          let dv = DElVar i
          dvN <- if vty == vN then Just dv
                 else Just (DElTyCoe (DNfExpandTy (DPresupElTy dv)) dv)
          pure (DElEqI (DElReflect dvN)))
       <|> byAssum tyN (S i)
  reCheckGo sig ctx (PiApp f e) ty sk =
    case reInferGo sig ctx (PiApp f e) sk of
      Just (d, ity) => coerce sig ctx d ity ty
      Nothing => do
        -- the constant-codomain guess for an uninferable head (an
        -- applied eliminator from a normalized spelling)
        (_, a) <- reInfer sig ctx e (childAt 1 sk)
        let b = substTy ty Wk
        df <- reCheck sig ctx f (Ty.PiTy a b) (childAt 0 sk)
        de <- reCheck sig ctx e a (childAt 1 sk)
        db <- reTy sig (ctx :< a) b emptySkel
              <|> Just (DInvPiCod (DPresupElTy df))
        pure (DElPiE df de db)
  reCheckGo sig ctx e ty sk = do
    (d, ity) <- dbg "infer: \{show e}" (reInfer sig ctx e sk)
    coerce sig ctx d ity ty

  ||| α-equal: the derivation already concludes at the expected
  ||| spelling; otherwise coerce along a β equation.
  coerce : Sig -> Ctx -> Deriv -> Ty -> Ty -> Maybe Deriv
  coerce sig ctx d ity ty =
    if ity == ty
      then Just d
      else do
        -- only a β-bridge; a hypothesis-sensitive difference is
        -- outside this slice (bail, silent fallback)
        iN <- nfT sig ity
        tN <- nfT sig ty
        let True = iN == tN
          | False => dbg "coerce: \{show iN} VS \{show tN}" Nothing
        di <- reTy sig ctx ity emptySkel
        dt <- reTy sig ctx ty emptySkel
        pure (DElTyCoe (DNfEqTy di dt) d)

-- ===== Certificate translation (the retirement map) =====

||| Selector translation: each Sel maps to its injectivity node
||| (instantiating selectors compose with el-sub-cong-fix); SelSuc
||| rides the derivable predecessor route — el-nat-e-cong at the
||| constant motive, conjugated by nf-expand.
applySelR : Sig -> Ctx -> (Deriv, Elem, Elem, Ty) -> Sel -> Maybe (Deriv, Elem, Elem, Ty)
applySelR sig ctx (dEq, le, re, t) SelSuc =
  case (le, re) of
    (NatIntro1 a, NatIntro1 b) => do
      let predCong = DElNatECong DTyNat (DElRefl DElNatZ)
                       (DElRefl (DElVar 1)) dEq
      let d = DElTrans (DElSym (DNfExpand (DPresupElL predCong)))
                (DElTrans predCong (DNfExpand (DPresupElR predCong)))
      pure (d, a, b, Ty.NatTy)
    _ => Nothing
applySelR sig ctx (dEq, le, re, t) SelDom =
  case (le, re) of
    (Elem.PiTy a0 b0, Elem.PiTy a1 b1) => do
      d0 <- reCheck sig (ctx :< El a0) b0 Ty.UniverseTy emptySkel
      d1 <- reCheck sig (ctx :< El a1) b1 Ty.UniverseTy emptySkel
      pure (DCodePiInjDom d0 d1 dEq, a0, a1, Ty.UniverseTy)
    (Elem.SigmaTy a0 b0, Elem.SigmaTy a1 b1) => do
      d0 <- reCheck sig (ctx :< El a0) b0 Ty.UniverseTy emptySkel
      d1 <- reCheck sig (ctx :< El a1) b1 Ty.UniverseTy emptySkel
      pure (DCodeSigmaInjDom d0 d1 dEq, a0, a1, Ty.UniverseTy)
    _ => Nothing
applySelR sig ctx (dEq, le, re, t) (SelCod u) =
  case (le, re) of
    (Elem.PiTy a0 b0, Elem.PiTy a1 b1) => do
      d0 <- reCheck sig (ctx :< El a0) b0 Ty.UniverseTy emptySkel
      d1 <- reCheck sig (ctx :< El a1) b1 Ty.UniverseTy emptySkel
      inst sig ctx (DCodePiInjCod d0 d1 dEq) a1 u b0 b1
    (Elem.SigmaTy a0 b0, Elem.SigmaTy a1 b1) => do
      d0 <- reCheck sig (ctx :< El a0) b0 Ty.UniverseTy emptySkel
      d1 <- reCheck sig (ctx :< El a1) b1 Ty.UniverseTy emptySkel
      inst sig ctx (DCodeSigmaInjCod d0 d1 dEq) a1 u b0 b1
    _ => Nothing
 where
  inst : Sig -> Ctx -> Deriv -> Elem -> Elem -> Elem -> Elem ->
         Maybe (Deriv, Elem, Elem, Ty)
  inst sig ctx dC a1 u b0 b1 = do
    dA <- reTy sig ctx (El a1) emptySkel
    dU <- reCheck sig ctx u (El a1) emptySkel
    let d = DElSubCongFix (DSubExt DSubId dA dU) dC
    pure (d, substElem b0 (Ext Id u), substElem b1 (Ext Id u), Ty.UniverseTy)
applySelR sig ctx (dEq, le, re, t) SelSumL =
  case (le, re) of
    (Elem.SumTy a0 _, Elem.SumTy a1 _) =>
      pure (DCodeSumInjL dEq, a0, a1, Ty.UniverseTy)
    _ => Nothing
applySelR sig ctx (dEq, le, re, t) SelSumR =
  case (le, re) of
    (Elem.SumTy _ b0, Elem.SumTy _ b1) =>
      pure (DCodeSumInjR dEq, b0, b1, Ty.UniverseTy)
    _ => Nothing
applySelR sig ctx (dEq, le, re, t) SelQDom =
  case (le, re) of
    (Elem.QuotTy a0 r0, Elem.QuotTy a1 r1) => do
      d0 <- reCheck sig (ctx :< El a0 :< substTy (El a0) Wk) r0 Ty.PropTy emptySkel
      d1 <- reCheck sig (ctx :< El a1 :< substTy (El a1) Wk) r1 Ty.PropTy emptySkel
      pure (DCodeQuotInjDom d0 d1 dEq, a0, a1, Ty.UniverseTy)
    _ => Nothing
applySelR sig ctx (dEq, le, re, t) (SelQRel u v) =
  case (le, re) of
    (Elem.QuotTy a0 r0, Elem.QuotTy a1 r1) => do
      d0 <- reCheck sig (ctx :< El a0 :< substTy (El a0) Wk) r0 Ty.PropTy emptySkel
      d1 <- reCheck sig (ctx :< El a1 :< substTy (El a1) Wk) r1 Ty.PropTy emptySkel
      let dC = DCodeQuotInjRel d0 d1 dEq
      dA <- reTy sig ctx (El a1) emptySkel
      dU <- reCheck sig ctx u (El a1) emptySkel
      dA2 <- reTy sig (ctx :< El a1) (substTy (El a1) Wk) emptySkel
      dV <- reCheck sig ctx v (El a1) emptySkel
      let sub = DSubExt (DSubExt DSubId dA dU) dA2 dV
      let d = DElSubCongFix sub dC
      pure (d, substElem r0 (Ext (Ext Id u) v),
               substElem r1 (Ext (Ext Id u) v), Ty.PropTy)
    _ => Nothing
applySelR sig ctx (dEq, le, re, t) (SelQIdx i) =
  case (le, re) of
    (QSortC sg0 k0 es0, QSortC sg1 k1 es1) => do
      let True = sg0 == sg1 && k0 == k1
        | False => Nothing
      let l0 = toList es0
      let True = take i l0 == take i (toList es1)
        | False => Nothing
      entry <- qEntry sg0 k0
      (tel, _, _) <- either (const Nothing) Just (reflTel sg0 (qwAt k0) entry)
      a0 <- getAt i l0
      a1 <- getAt i (toList es1)
      e <- telInst tel i l0
      pure (DCodeQSortInjIdx i dEq, a0, a1, e)
    _ => Nothing

foldSels : Sig -> Ctx -> (Deriv, Elem, Elem, Ty) -> List Sel -> Maybe (Deriv, Elem, Elem, Ty)
foldSels sig ctx st [] = Just st
foldSels sig ctx st (sel :: rest) = do
  st' <- applySelR sig ctx st sel
  foldSels sig ctx st' rest

||| The licensed equation of a step at depth d (crossed binders),
||| reconstructed AT the leaf's context: the proof spelling is
||| weakened and re-inferred there, its type exposed to a literal
||| equality prop by the oracle when needed.
reLicensed : Sig -> Ctx -> Step -> Nat -> Maybe (Deriv, Elem, Elem, Ty)
reLicensed sig ctx step d =
  case step.lic of
    LProof p => do
      let pw = wkN d p
      (dp, pty) <- reInfer sig ctx pw emptySkel
      ptyN <- nfT sig pty
      dp' <- if pty == ptyN then Just dp
             else Just (DElTyCoe (DNfExpandTy (DPresupElTy dp)) dp)
      case ptyN of
        Prf (Elem.EqTy le0 re0 t0) => do
          (dSel, le, re, t) <- foldSels sig ctx
                                 (DElReflect dp', le0, re0, t0) step.sels
          -- normalize the licensed sides (replay compares nfs)
          leN <- nfE sig le
          reN <- nfE sig re
          let dEqN = DElTrans (DElSym (DNfExpand (DPresupElL dSel)))
                       (DElTrans dSel (DNfExpand (DPresupElR dSel)))
          let (dO, lO, rO) = if step.flip
                               then (DElSym dEqN, reN, leN)
                               else (dEqN, leN, reN)
          pure (dO, lO, rO, t)
        _ => Nothing
    LPath sg k theta => do
      let [] = step.sels
        | _ => Nothing
      let thetaW = map (wkN d) (toList theta)
      dSig <- reQSig sig ctx sg
      ds <- reQSpine sig ctx sg k thetaW
      entry <- qEntry sg k
      (tel, _, _) <- e2m (reflTel sg (qwAt k) entry)
      (wEnd, hd) <- e2m (walkVals sg (qwAt k) entry thetaW)
      (lq, rq, uq) <- e2m (eqHead hd)
      le <- e2m (reflTm sg wEnd lq)
      re <- e2m (reflTm sg wEnd rq)
      t <- e2m (reflCodeTy sg wEnd uq)
      let dEq = DQPath k dSig ds
      leN <- nfE sig le
      reN <- nfE sig re
      let dEqN = DElTrans (DElSym (DNfExpand (DPresupElL dEq)))
                   (DElTrans dEq (DNfExpand (DPresupElR dEq)))
      let (dO, lO, rO) = if step.flip
                           then (DElSym dEqN, reN, leN)
                           else (dEqN, leN, reN)
      pure (dO, lO, rO, t)

||| An application head's Π type: by inference when the head is
||| inferable, else the CONSTANT-CODOMAIN guess — domain from the
||| argument, codomain from the application's expected type (the
||| applied-eliminator fragment).
headPi : Sig -> Ctx -> Elem -> Elem -> Ty -> Maybe (Ty, Ty)
headPi sig ctx f e exp =
  case reInfer sig ctx f emptySkel of
    Just (_, Ty.PiTy a b) => Just (a, b)
    _ => do
      (_, a) <- reInfer sig ctx e emptySkel
      pure (a, substTy exp Wk)

-- one-level children of an element (the common formers), for the
-- candidate pools of the instantiation searches
kidsE : Elem -> List Elem
kidsE (ZeroElim u) = [u]
kidsE (NatIntro1 u) = [u]
kidsE (NatElim z st u) = [z, u]
kidsE (PiApp f u) = [f, u]
kidsE (SigmaIntro u v) = [u, v]
kidsE (SigmaElim1 u) = [u]
kidsE (SigmaElim2 u) = [u]
kidsE (Inj1 u) = [u]
kidsE (Inj2 u) = [u]
kidsE (SumElim _ _ u) = [u]
kidsE (Elem.EqTy l r _) = [l, r]
kidsE (Class u) = [u]
kidsE (QuotElim _ q) = [q]
kidsE (Out u) = [u]
kidsE (QCtor _ _ es) = toList es
kidsE (QSortC _ _ es) = toList es
kidsE _ = []

subterms : Nat -> Elem -> List Elem
subterms Z e = [e]
subterms (S d) e = e :: concatMap (subterms d) (kidsE e)

-- SUBTERM REWRITE: every occurrence of a target spelling replaced
-- by another (both weakened across binders) — the spelling-level
-- companion of the congruence walks, used to PROPOSE a rewritten
-- code whose bridge the walks then derive.
mutual
  replE : Elem -> Elem -> Nat -> Elem -> Elem
  replE t r b e =
    if e == wkN b t then wkN b r else
    case e of
      ZeroElim u => ZeroElim (replE t r b u)
      NatIntro1 u => NatIntro1 (replE t r b u)
      NatElim z st u => NatElim (replE t r b z) (replE t r (2 + b) st) (replE t r b u)
      PiIntro f => PiIntro (replE t r (S b) f)
      PiApp f u => PiApp (replE t r b f) (replE t r b u)
      Let a u => Let (replE t r b a) (replE t r (2 + b) u)
      SigmaIntro u v => SigmaIntro (replE t r b u) (replE t r b v)
      SigmaElim1 u => SigmaElim1 (replE t r b u)
      SigmaElim2 u => SigmaElim2 (replE t r b u)
      Inj1 u => Inj1 (replE t r b u)
      Inj2 u => Inj2 (replE t r b u)
      SumElim l rr u => SumElim (replE t r (S b) l) (replE t r (S b) rr) (replE t r b u)
      Elem.PiTy a c => Elem.PiTy (replE t r b a) (replE t r (S b) c)
      Elem.SigmaTy a c => Elem.SigmaTy (replE t r b a) (replE t r (S b) c)
      Elem.SumTy a c => Elem.SumTy (replE t r b a) (replE t r b c)
      Elem.EqTy l rr ty => Elem.EqTy (replE t r b l) (replE t r b rr) (replTy t r b ty)
      QuotTy a rr => QuotTy (replE t r b a) (replE t r (2 + b) rr)
      Elem.SigVar x es => Elem.SigVar x (cast (map (replE t r b) (toList es)))
      Class u => Class (replE t r b u)
      QuotElim f q => QuotElim (replE t r (S b) f) (replE t r b q)
      Squash ty => Squash (replTy t r b ty)
      QSortC sg k es => QSortC sg k (cast (map (replE t r b) (toList es)))
      QCtor sg k es => QCtor sg k (cast (map (replE t r b) (toList es)))
      Out u => Out (replE t r b u)
      _ => e

  replTy : Elem -> Elem -> Nat -> Ty -> Ty
  replTy t r b ty =
    case ty of
      Ty.PiTy a c => Ty.PiTy (replTy t r b a) (replTy t r (S b) c)
      Ty.SigmaTy a c => Ty.SigmaTy (replTy t r b a) (replTy t r (S b) c)
      Ty.SumTy a c => Ty.SumTy (replTy t r b a) (replTy t r b c)
      El e => El (replE t r b e)
      Prf e => Prf (replE t r b e)
      Ty.Quotient a rr => Ty.Quotient (replTy t r b a) (replE t r (2 + b) rr)
      Ty.SigVar x es => Ty.SigVar x (cast (map (replE t r b) (toList es)))
      QSort sg k es => QSort sg k (cast (map (replE t r b) (toList es)))
      _ => ty

-- MOTIVE ABSTRACTION: the expected type with occurrences of the
-- scrutinee's (weakened) spelling replaced by the fresh binder —
-- the indexed-motive guess for a normalized eliminator spelling.
-- Conservative: unhandled formers are left untouched (a missed
-- occurrence just means the guessed motive fails downstream).
mutual
  absE : Elem -> Nat -> Elem -> Elem
  absE t b e =
    if e == wkN b t then CtxVar b else
    case e of
      ZeroElim u => ZeroElim (absE t b u)
      NatIntro1 u => NatIntro1 (absE t b u)
      NatElim z st u => NatElim (absE t b z) (absE t (2 + b) st) (absE t b u)
      PiIntro f => PiIntro (absE t (S b) f)
      PiApp f u => PiApp (absE t b f) (absE t b u)
      Let a u => Let (absE t b a) (absE t (2 + b) u)
      SigmaIntro u v => SigmaIntro (absE t b u) (absE t b v)
      SigmaElim1 u => SigmaElim1 (absE t b u)
      SigmaElim2 u => SigmaElim2 (absE t b u)
      Inj1 u => Inj1 (absE t b u)
      Inj2 u => Inj2 (absE t b u)
      SumElim l r u => SumElim (absE t (S b) l) (absE t (S b) r) (absE t b u)
      Elem.PiTy a c => Elem.PiTy (absE t b a) (absE t (S b) c)
      Elem.SigmaTy a c => Elem.SigmaTy (absE t b a) (absE t (S b) c)
      Elem.SumTy a c => Elem.SumTy (absE t b a) (absE t b c)
      Elem.EqTy l r ty => Elem.EqTy (absE t b l) (absE t b r) (absTy t b ty)
      QuotTy a r => QuotTy (absE t b a) (absE t (2 + b) r)
      Elem.SigVar x es => Elem.SigVar x (cast (map (absE t b) (toList es)))
      Class u => Class (absE t b u)
      QuotElim f q => QuotElim (absE t (S b) f) (absE t b q)
      Squash ty => Squash (absTy t b ty)
      QSortC sg k es => QSortC sg k (cast (map (absE t b) (toList es)))
      QCtor sg k es => QCtor sg k (cast (map (absE t b) (toList es)))
      Out u => Out (absE t b u)
      _ => e

  absTy : Elem -> Nat -> Ty -> Ty
  absTy t b ty =
    case ty of
      Ty.PiTy a c => Ty.PiTy (absTy t b a) (absTy t (S b) c)
      Ty.SigmaTy a c => Ty.SigmaTy (absTy t b a) (absTy t (S b) c)
      Ty.SumTy a c => Ty.SumTy (absTy t b a) (absTy t b c)
      El e => El (absE t b e)
      Prf e => Prf (absE t b e)
      Ty.Quotient a r => Ty.Quotient (absTy t b a) (absE t (2 + b) r)
      Ty.SigVar x es => Ty.SigVar x (cast (map (absE t b) (toList es)))
      QSort sg k es => QSort sg k (cast (map (absE t b) (toList es)))
      _ => ty

rePlaceT : Sig -> Ctx -> Step -> Nat -> List Nat -> Ty -> Maybe Deriv -> Maybe (Deriv, Ty)

chkStep : Sig -> Ctx -> Step -> Nat -> Elem -> Ty -> Maybe Deriv

reBridgeTSearch : Sig -> Ctx -> Step -> Nat -> Ty -> Ty -> Maybe Deriv

||| Coerce an element-equation derivation from its own type spelling
||| to a target spelling, the two nf-equal (the oracle bridge).
eqAtNf : Sig -> Ctx -> Deriv -> Ty -> Ty -> Maybe Deriv
eqAtNf sig ctx dEq cur tgt =
  if cur == tgt then Just dEq
    else do
      cN <- nfT sig cur
      tN <- nfT sig tgt
      let True = cN == tN
        | False => Nothing
      dC <- reTy sig ctx cur emptySkel
      dT <- reTy sig ctx tgt emptySkel
      pure (DElEqTyCoe (DNfEqTy dC dT) dEq)

||| Placement: rewrite `cur` at `path` by the step's licensed
||| equation, emitting the congruence chain; returns the derivation
||| (cur ≐ cur′ at the expected type) and cur′.
rePlaceE : Sig -> Ctx -> Step -> Nat -> List Nat -> Ty -> Elem -> Maybe Deriv -> Maybe (Deriv, Elem, Ty)
rePlaceE sig ctx step d [] exp cur mty = do
  (dEq, le, re, t) <- dbg "leaf: license" (reLicensed sig ctx step d)
  let True = cur == le
    | False => dbg "leaf: cur \{show cur} /= licensed \{show le}" Nothing
  d' <- if t == exp then Just dEq
        else do
          -- only a β-bridge: a position whose type differs from the
          -- licensed type beyond nf (a dependent position shifted by
          -- an earlier rewrite) is outside this slice
          tN <- nfT sig t
          eN <- nfT sig exp
          let True = tN == eN
            | False => Nothing
          dt <- reTy sig ctx t emptySkel
          de <- reTy sig ctx exp emptySkel
          pure (DElEqTyCoe (DNfEqTy dt de) dEq)
  pure (d', re, if t == exp then t else exp)
rePlaceE sig ctx step d (i :: p) exp cur mty =
  case (cur, i) of
    (NatIntro1 t, 0) => do
      (dc0, t', chTy) <- rePlaceE sig ctx step d p Ty.NatTy t Nothing
      dc <- eqAtNf sig ctx dc0 chTy Ty.NatTy
      pure (DElSucCong dc, NatIntro1 t', Ty.NatTy)
    (PiApp f e, 0) => do
      (a, b) <- headPi sig ctx f e exp
      (dc0, f', chTy) <- rePlaceE sig ctx step d p (Ty.PiTy a b) f Nothing
      dc <- eqAtNf sig ctx dc0 chTy (Ty.PiTy a b)
      de <- reCheck sig ctx e a emptySkel
      db <- reTy sig (ctx :< a) b emptySkel
            <|> Just (DInvPiCod (DPresupElTy (DPresupElL dc)))
      pure (DElAppCong dc (DElRefl de) db, PiApp f' e, substTy b (Ext Id e))
    (PiApp f e, 1) => do
      (a, b) <- headPi sig ctx f e exp
      df <- reCheck sig ctx f (Ty.PiTy a b) emptySkel
      (dc0, e', chTy) <- rePlaceE sig ctx step d p a e Nothing
      dc <- eqAtNf sig ctx dc0 chTy a
      db <- reTy sig (ctx :< a) b emptySkel
            <|> Just (DInvPiCod (DPresupElTy df))
      -- the congruence concludes at the POST-instance B[id,e′]; the
      -- child equation itself bridges it back to the PRE-instance
      -- the surrounding chain speaks (sub-ext-cong on ⟨id,·⟩, then
      -- ty-sub-cong at the fixed family) — the dependent shift is
      -- neutralized at source, no search
      let dA = reTy sig ctx a emptySkel
               <|> Just (DInvPiDom (DPresupElTy df))
      case dA of
        Nothing => pure (DElAppCong (DElRefl df) dc db,
                         PiApp f e', substTy b (Ext Id e'))
        Just dA' => do
          let dS = DSubExtCong (DSubRefl DSubId) dA' (DElSym dc)
          let bridge = DTySubCong dS (DTyRefl db)
          pure (DElEqTyCoe bridge (DElAppCong (DElRefl df) dc db),
                PiApp f e', substTy b (Ext Id e))
    (SigmaIntro u v, 0) => do
      expN <- nfT sig exp
      let Ty.SigmaTy a b = expN
        | _ => Nothing
      (dc0, u', chTy) <- rePlaceE sig ctx step d p a u Nothing
      dc <- eqAtNf sig ctx dc0 chTy a
      db <- reTy sig (ctx :< a) b emptySkel
      dv <- reCheck sig ctx v (substTy b (Ext Id u')) emptySkel
      pure (DElPairCong dc db (DElRefl dv), SigmaIntro u' v, expN)
    (SigmaIntro u v, 1) => do
      expN <- nfT sig exp
      let Ty.SigmaTy a b = expN
        | _ => Nothing
      du <- reCheck sig ctx u a emptySkel
      db <- reTy sig (ctx :< a) b emptySkel
      (dc0, v', chTy) <- rePlaceE sig ctx step d p (substTy b (Ext Id u)) v Nothing
      dc <- eqAtNf sig ctx dc0 chTy (substTy b (Ext Id u))
      pure (DElPairCong (DElRefl du) db dc, SigmaIntro u v', expN)
    (Inj1 a, 0) =>
      case exp of
        Ty.SumTy l r => do
          (dc0, a', chTy) <- rePlaceE sig ctx step d p l a Nothing
          dc <- eqAtNf sig ctx dc0 chTy l
          dr <- reTy sig ctx r emptySkel
          pure (DElInj1Cong dc dr, Inj1 a', Ty.SumTy l r)
        _ => Nothing
    (Inj2 b, 0) =>
      case exp of
        Ty.SumTy l r => do
          (dc0, b', chTy) <- rePlaceE sig ctx step d p r b Nothing
          dc <- eqAtNf sig ctx dc0 chTy r
          dl <- reTy sig ctx l emptySkel
          pure (DElInj2Cong dc dl, Inj2 b', Ty.SumTy l r)
        _ => Nothing
    (NatElim z st t, 2) => do
      (dc0, t', chTy) <- rePlaceE sig ctx step d p Ty.NatTy t Nothing
      dc <- eqAtNf sig ctx dc0 chTy Ty.NatTy
      let tryMot = \mot => do
            dmot <- dbg "natEmot: motive \{show mot}" (reTy sig (ctx :< Ty.NatTy) mot emptySkel)
            dz <- dbg "natEmot: z" (chkStep sig ctx step d z (substTy mot (Ext Id NatIntro0)))
            dst <- dbg "natEmot: st" (chkStep sig (ctx :< Ty.NatTy :< mot) step (2 + d) st
                     (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)))
            -- shift neutralized at source: the scrutinee equation
            -- bridges mot[id,t′] back to mot[id,t]
            let dS = DSubExtCong (DSubRefl DSubId) DTyNat (DElSym dc)
            let bridge = DTySubCong dS (DTyRefl dmot)
            pure (DElEqTyCoe bridge
                    (DElNatECong dmot (DElRefl dz) (DElRefl dst) dc),
                  NatElim z st t', substTy mot (Ext Id t))
      tryMot (substTy exp Wk)
        -- the expected type is the motive INSTANCE — at the original
        -- scrutinee if the surroundings kept its spelling, at the
        -- REWRITTEN one if the equation's type already speaks the
        -- other side — so try abstracting both
        <|> tryMot (absTy (substElem t Wk) 0 (substTy exp Wk))
        <|> tryMot (absTy (substElem t' Wk) 0 (substTy exp Wk))
    (NatElim z st t, 0) => do
      let mot = substTy exp Wk
      dmot <- reTy sig (ctx :< Ty.NatTy) mot emptySkel
      (dc, z', _) <- rePlaceE sig ctx step d p exp z Nothing
      dst <- reCheck sig (ctx :< Ty.NatTy :< mot) st
               (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) emptySkel
      dt <- reCheck sig ctx t Ty.NatTy emptySkel
      pure (DElNatECong dmot dc (DElRefl dst) (DElRefl dt),
            NatElim z' st t, exp)
    (NatElim z st t, 1) => do
      let mot = substTy exp Wk
      dmot <- reTy sig (ctx :< Ty.NatTy) mot emptySkel
      dz <- reCheck sig ctx z exp emptySkel
      let sctx = ctx :< Ty.NatTy :< mot
      (dc, st', _) <- rePlaceE sig sctx step (2 + d) p
                        (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) st Nothing
      dt <- reCheck sig ctx t Ty.NatTy emptySkel
      pure (DElNatECong dmot (DElRefl dz) dc (DElRefl dt),
            NatElim z st' t, exp)
    (SumElim l r t, 2) => do
      (dt, tty) <- reInfer sig ctx t emptySkel >>= expose sig
      case tty of
        Ty.SumTy a b => do
          let mot = substTy exp Wk
          dmot <- reTy sig (ctx :< Ty.SumTy a b) mot emptySkel
          dl <- reCheck sig (ctx :< a) l (substTy exp Wk) emptySkel
          dr <- reCheck sig (ctx :< b) r (substTy exp Wk) emptySkel
          (dc0, t', chTy) <- rePlaceE sig ctx step d p (Ty.SumTy a b) t Nothing
          dc <- eqAtNf sig ctx dc0 chTy (Ty.SumTy a b)
          pure (DElSumECong dc dmot (DElRefl dl) (DElRefl dr),
                SumElim l r t', exp)
        _ => Nothing
    (Class a, 0) =>
      case exp of
        Ty.Quotient dom rel => do
          (dc, a', _) <- rePlaceE sig ctx step d p dom a Nothing
          dr <- reCheck sig (ctx :< dom :< substTy dom Wk) rel Ty.PropTy emptySkel
          pure (DElClassCong dc dr, Class a', Ty.Quotient dom rel)
        _ => Nothing
    (Out t, 0) => do
      -- Foundation's spine route: out ☐₀ over Γ ▷ ν𝔽, the component
      -- equation pushed in by sub-ext-cong + el-sub-cong
      (dt, tty) <- reInfer sig ctx t emptySkel
      ttyN <- nfT sig tty
      let Ty.NuTy f = ttyN
        | _ => Nothing
      let nuT = Ty.NuTy f
      (dc0, t', chTy) <- rePlaceE sig ctx step d p nuT t Nothing
      dc <- eqAtNf sig ctx dc0 chTy nuT
      dNu <- reTy sig ctx nuT emptySkel
      (dSp, spTy) <- reInfer sig (ctx :< nuT) (Out (CtxVar 0)) emptySkel
      let dS = DSubExtCong (DSubRefl DSubId) dNu dc
      pure (DElSubCong dS (DElRefl dSp), Out t',
            substTy spTy (Ext Id t'))
    (SigmaElim1 t, 0) => do
      (dt, tty) <- reInfer sig ctx t emptySkel
      ttyN <- nfT sig tty
      let Ty.SigmaTy a _ = ttyN
        | _ => Nothing
      (dc0, t', chTy) <- rePlaceE sig ctx step d p ttyN t Nothing
      dc <- eqAtNf sig ctx dc0 chTy ttyN
      pure (DElProj1Cong dc, SigmaElim1 t', a)
    (SigmaElim2 t, 0) => do
      (dt, tty) <- reInfer sig ctx t emptySkel
      ttyN <- nfT sig tty
      let Ty.SigmaTy a b = ttyN
        | _ => Nothing
      (dc0, t', chTy) <- rePlaceE sig ctx step d p ttyN t Nothing
      dc <- eqAtNf sig ctx dc0 chTy ttyN
      -- shift neutralized at source, as at PiApp-1: the first
      -- projections' equation bridges B[id, π₁ t′] back to
      -- B[id, π₁ t]
      let mPieces = do
            dTy <- reTy sig ctx ttyN emptySkel
                   <|> Just (DPresupElTy dt)
            da <- reTy sig ctx a emptySkel
                  <|> Just (DInvSigmaDom dTy)
            db <- reTy sig (ctx :< a) b emptySkel
                  <|> Just (DInvSigmaCod dTy)
            pure (da, db)
      case mPieces of
        Nothing => pure (DElProj2Cong dc, SigmaElim2 t',
                         substTy b (Ext Id (SigmaElim1 t')))
        Just (da, db) => do
          let dS = DSubExtCong (DSubRefl DSubId) da
                     (DElSym (DElProj1Cong dc))
          let bridge = DTySubCong dS (DTyRefl db)
          pure (DElEqTyCoe bridge (DElProj2Cong dc), SigmaElim2 t',
                substTy b (Ext Id (SigmaElim1 t)))
    (Elem.EqTy l r t, 0) => do
      dt <- reTy sig ctx t emptySkel
            <|> (DInvCodeEqTy <$> mty)
      (dc, l', _) <- rePlaceE sig ctx step d p t l
                       (DInvCodeEqL <$> mty)
      dr <- reCheck sig ctx r t emptySkel
            <|> (DInvCodeEqR <$> mty)
      pure (DCodeEqCong (DTyRefl dt) dc (DElRefl dr), Elem.EqTy l' r t, Ty.PropTy)
    (Elem.EqTy l r t, 1) => do
      dt <- reTy sig ctx t emptySkel
            <|> (DInvCodeEqTy <$> mty)
      dl <- reCheck sig ctx l t emptySkel
            <|> (DInvCodeEqL <$> mty)
      (dc, r', _) <- rePlaceE sig ctx step d p t r
                       (DInvCodeEqR <$> mty)
      pure (DCodeEqCong (DTyRefl dt) (DElRefl dl) dc, Elem.EqTy l r' t, Ty.PropTy)
    (Elem.EqTy l r t, 2) => do
      -- a rewrite in the ∈-slot: the sides ride the CHILD TYPE
      -- EQUATION itself into the new type — the hypothesis-sensitive
      -- bridge, derived rather than oracled
      (dc, t') <- rePlaceT sig ctx step d p t (DInvCodeEqTy <$> mty)
      dl <- reCheck sig ctx l t emptySkel
            <|> (DInvCodeEqL <$> mty)
      dr <- reCheck sig ctx r t emptySkel
            <|> (DInvCodeEqR <$> mty)
      pure (DCodeEqCong dc
              (DElEqTyCoe dc (DElRefl dl))
              (DElEqTyCoe dc (DElRefl dr)),
            Elem.EqTy l r t', Ty.PropTy)
    (QCtor sg k es, _) => do
      entry <- qEntry sg k
      (tel, _, _) <- either (const Nothing) Just (reflTel sg (qwAt k) entry)
      let ls = toList es
      e0 <- getAt i ls
      ety <- telInst tel i ls
      (dc0, e', chTy) <- rePlaceE sig ctx step d p ety e0 Nothing
      dc <- eqAtNf sig ctx dc0 chTy ety
      dSig <- reQSig sig ctx sg
      ds <- traverse (\(j, ej) =>
              if j == i then Just dc
              else do etj <- telInst tel j ls
                      DElRefl <$> reCheck sig ctx ej etj emptySkel)
            (zip [0 .. minus (length ls) 1] ls)
      ls' <- setAtL i e' ls
      (wEnd, hd) <- either (const Nothing) Just (walkVals sg (qwAt k) entry ls)
      (srt, idx) <- either (const Nothing) Just (pointHead sg wEnd hd)
      pure (DQCtorCong k dSig ds, QCtor sg k (cast ls'), QSort sg srt idx)
    (Elem.SumTy a b, 0) => do
      (dc, a', _) <- rePlaceE sig ctx step d p Ty.UniverseTy a Nothing
      db <- reCheck sig ctx b Ty.UniverseTy emptySkel
      pure (DCodeSumCong dc (DElRefl db), Elem.SumTy a' b, Ty.UniverseTy)
    (Elem.SumTy a b, 1) => do
      da <- reCheck sig ctx a Ty.UniverseTy emptySkel
      (dc, b', _) <- rePlaceE sig ctx step d p Ty.UniverseTy b Nothing
      pure (DCodeSumCong (DElRefl da) dc, Elem.SumTy a b', Ty.UniverseTy)
    _ => Nothing

rePlaceT sig ctx step d (0 :: p) (El e) mtf = do
  (dc, e', _) <- rePlaceE sig ctx step d p Ty.UniverseTy e
                   (DInvElCode <$> mtf)
  pure (DTyElCong dc, El e')
rePlaceT sig ctx step d (0 :: p) (Prf e) mtf = do
  (dc, e', _) <- rePlaceE sig ctx step d p Ty.PropTy e
                   (DInvPrfCode <$> mtf)
  pure (DTyPrfCong dc, Prf e')
rePlaceT sig ctx step d (0 :: p) (Ty.PiTy a b) mtf = do
  (dc, a') <- rePlaceT sig ctx step d p a (DInvPiDom <$> mtf)
  db <- reTy sig (ctx :< a') b emptySkel
        <|> (DInvPiCod <$> mtf)
  pure (DTyPiCong dc (DTyRefl db), Ty.PiTy a' b)
rePlaceT sig ctx step d (1 :: p) (Ty.PiTy a b) mtf = do
  da <- reTy sig ctx a emptySkel
        <|> (DInvPiDom <$> mtf)
  (dc, b') <- rePlaceT sig (ctx :< a) step (S d) p b (DInvPiCod <$> mtf)
  pure (DTyPiCong (DTyRefl da) dc, Ty.PiTy a b')
rePlaceT sig ctx step d (0 :: p) (Ty.SigmaTy a b) mtf = do
  (dc, a') <- rePlaceT sig ctx step d p a (DInvSigmaDom <$> mtf)
  db <- reTy sig (ctx :< a') b emptySkel
        <|> (DInvSigmaCod <$> mtf)
  pure (DTySigmaCong dc (DTyRefl db), Ty.SigmaTy a' b)
rePlaceT sig ctx step d (1 :: p) (Ty.SigmaTy a b) mtf = do
  da <- reTy sig ctx a emptySkel
        <|> (DInvSigmaDom <$> mtf)
  (dc, b') <- rePlaceT sig (ctx :< a) step (S d) p b (DInvSigmaCod <$> mtf)
  pure (DTySigmaCong (DTyRefl da) dc, Ty.SigmaTy a b')
rePlaceT sig ctx step d (0 :: p) (Ty.SumTy a b) mtf = do
  (dc, a') <- rePlaceT sig ctx step d p a Nothing
  db <- reTy sig ctx b emptySkel
  pure (DTySumCong dc (DTyRefl db), Ty.SumTy a' b)
rePlaceT sig ctx step d (1 :: p) (Ty.SumTy a b) mtf = do
  da <- reTy sig ctx a emptySkel
  (dc, b') <- rePlaceT sig ctx step d p b Nothing
  pure (DTySumCong (DTyRefl da) dc, Ty.SumTy a b')
rePlaceT sig ctx step d (i :: p) (QSort sg k es) mtf = do
  entry <- qEntry sg k
  (tel, _, _) <- either (const Nothing) Just (reflTel sg (qwAt k) entry)
  let l = toList es
  e <- getAt i l
  ety <- telInst tel i l
  (dc0, e', chTy) <- rePlaceE sig ctx step d p ety e Nothing
  dc <- eqAtNf sig ctx dc0 chTy ety
  dSig <- reQSig sig ctx sg
  ds <- traverse (\(j, ej) =>
          if j == i then Just dc
          else do etj <- telInst tel j l
                  DElRefl <$> reCheck sig ctx ej etj emptySkel)
        (zip [0 .. minus (length l) 1] l)
  l' <- maybe Nothing Just (setAtL i e' l)
  pure (DTyQSortCong k dSig ds, QSort sg k (cast l'))
rePlaceT sig ctx step d path ty mtf = Nothing

||| A path-constructor equation with a SEARCHED instantiation: for
||| each equation entry of the signature, candidate spines are built
||| slot by slot from the mismatched pair's own constructor arguments
||| and the context's variables, type-filtered; the first
||| instantiation whose reflected endpoints match the pair (either
||| orientation) wins. Conclude arbitrates, as with every guess.
qPathLeaf : Sig -> Ctx -> Elem -> Elem -> Maybe (Deriv, Ty)
qPathLeaf sig ctx x y = do
  sg <- case (x, y) of
          (QCtor sg _ _, _) => Just sg
          (_, QCtor sg _ _) => Just sg
          _ => Nothing
  xN <- nfE sig x
  yN <- nfE sig y
  let cands = map CtxVar [0 .. minus (length (toList ctx)) 1]
              ++ collect 2 x ++ collect 2 y
  tryEntries sg xN yN cands (eqPositions sg 0)
 where
  collect : Nat -> Elem -> List Elem
  collect Z _ = []
  collect (S k) (QCtor _ _ es) =
    let l = toList es in l ++ concatMap (collect k) l
  collect _ _ = []

  eqPositions : QSig -> Nat -> List Nat
  eqPositions [] _ = []
  eqPositions (e :: rest) i =
    case qEntryKind e of
      QKEq => i :: eqPositions rest (S i)
      _ => eqPositions rest (S i)

  spines : List Ty -> List Elem -> List Elem -> List (List Elem)
  spines tel cands acc =
    case getAt (length acc) tel of
      Nothing => [acc]
      Just _ =>
        case telInst tel (length acc) acc of
          Nothing => []
          Just want =>
            concatMap (\c => case reCheck sig ctx c want emptySkel of
                                Just _ => spines tel cands (acc ++ [c])
                                Nothing => [])
              cands

  tryTheta : QSig -> Elem -> Elem -> Nat -> List Elem -> Maybe (Deriv, Ty)
  tryTheta sg xN yN j theta = do
    dSig <- reQSig sig ctx sg
    ds <- reQSpine sig ctx sg j theta
    entry <- qEntry sg j
    (wEnd, hd) <- either (const Nothing) Just (walkVals sg (qwAt j) entry theta)
    (lq, rq, uq) <- either (const Nothing) Just (eqHead hd)
    le <- either (const Nothing) Just (reflTm sg wEnd lq)
    re <- either (const Nothing) Just (reflTm sg wEnd rq)
    t <- either (const Nothing) Just (reflCodeTy sg wEnd uq)
    let dEq = DQPath j dSig ds
    leN <- nfE sig le
    reN <- nfE sig re
    let dEqN = DElTrans (DElSym (DNfExpand (DPresupElL dEq)))
                 (DElTrans dEq (DNfExpand (DPresupElR dEq)))
    if leN == xN && reN == yN then Just (dEqN, t)
      else if leN == yN && reN == xN then Just (DElSym dEqN, t)
      else Nothing

  firstJust : (a -> Maybe b) -> List a -> Maybe b
  firstJust f [] = Nothing
  firstJust f (v :: rest) = f v <|> firstJust f rest

  tryEntries : QSig -> Elem -> Elem -> List Elem -> List Nat -> Maybe (Deriv, Ty)
  tryEntries _ _ _ _ [] = Nothing
  tryEntries sg xN yN cands (j :: rest) =
    (do entry <- qEntry sg j
        (tel, _, _) <- either (const Nothing) Just (reflTel sg (qwAt j) entry)
        firstJust (tryTheta sg xN yN j) (take 64 (spines tel cands [])))
    <|> tryEntries sg xN yN cands rest

||| A step's ∀-lemma RE-INSTANTIATED: the licensed proof is an
||| application tower; the mismatched pair may be the lemma's
||| equation at DIFFERENT arguments (a type instance shifted along
||| the rewrite). Candidate arguments from the pair's own subterms
||| and the context, type-filtered along the lemma's Π tower.
-- a coarse head tag, for prefiltering store lemmas against a
-- code's subterms
headTag : Elem -> String
headTag (CtxVar _) = "var"
headTag (Elem.SigVar q _) = "sig:" ++ q
headTag (PiApp f _) = headTag f
headTag (NatElim z _ _) = "natelim:" ++ headTag z
headTag (SumElim _ _ _) = "sumelim"
headTag (QuotElim _ _) = "quotelim"
headTag (QElim _ _ _ _ _ _) = "qelim"
headTag (SigmaElim1 _) = "proj1"
headTag (SigmaElim2 _) = "proj2"
headTag (NatIntro1 _) = "suc"
headTag NatIntro0 = "zero"
headTag (Class _) = "class"
headTag (QCtor _ k _) = "qctor" ++ show k
headTag (Out _) = "out"
headTag _ = "other"

||| Every well-typed instantiation of a step's ∀-lemma over a
||| candidate pool: the licensed proof's application spine (PiApp
||| tower or signature spine) re-built at searched arguments,
||| type-filtered along the Π tower or telescope; each result is the
||| reflected equation (conjugated to nf) with its endpoints and
||| type.
lemmaInsts : Sig -> Ctx -> Step -> Nat -> List Elem -> List (Deriv, Elem, Elem, Ty, Elem)
lemmaInsts sig ctx step d pool0 =
  let pool = nub pool0 in
  case step.lic of
    LProof p =>
      let (h0, appArgs) = peel (wkN d p) [] in
      case the (Maybe (List Ty, List Elem -> Maybe Elem, Nat)) $
        (case h0 of
          Elem.SigVar nm es => do
            delta <- the (Maybe (List Ty)) $ case sigLookup nm sig of
                       Just (SigDef dctx _ _ _) => Just (toList dctx)
                       Just (SigDecl dctx _ _) => Just (toList dctx)
                       _ => Nothing
            let nSpine = length (toList es)
            let True = nSpine == length delta
              | False => Nothing
            pure (delta,
                  \newArgs =>
                    let (sp, aps) = splitAt nSpine newArgs in
                    Just (applyE (Elem.SigVar nm (cast sp)) aps),
                  nSpine + length appArgs)
          _ => do
            let False = length appArgs == 0
              | True => Nothing
            pure ([], \newArgs => Just (applyE h0 newArgs), length appArgs)) of
        Nothing => []
        Just (spineTys, rebuild, arity) =>
          mapMaybe (instOf rebuild)
            (take 24 (tuples spineTys rebuild pool arity []))
    _ => []
 where
  peel : Elem -> List Elem -> (Elem, List Elem)
  peel (PiApp f u) acc = peel f (u :: acc)
  peel h acc = (h, acc)

  applyE : Elem -> List Elem -> Elem
  applyE h [] = h
  applyE h (u :: rest) = applyE (PiApp h u) rest

  slotTy : List Ty -> (List Elem -> Maybe Elem) -> List Elem -> Maybe Ty
  slotTy spineTys rebuild acc =
    let i = length acc in
    case getAt i spineTys of
      Just dTy => Just (substTy dTy (foldl Ext Id (take i acc)))
      Nothing => do
        partial0 <- rebuild acc
        (_, hty) <- reInfer sig ctx partial0 emptySkel
        htyN <- nfT sig hty
        let Ty.PiTy a _ = htyN
          | _ => Nothing
        pure a

  tuples : List Ty -> (List Elem -> Maybe Elem) -> List Elem -> Nat -> List Elem -> List (List Elem)
  tuples spineTys rebuild pool Z acc = [acc]
  tuples spineTys rebuild pool (S k) acc =
    case slotTy spineTys rebuild acc of
      Nothing => []
      Just want =>
        concatMap (\c => case reCheck sig ctx c want emptySkel of
                            Just _ => tuples spineTys rebuild pool k (acc ++ [c])
                            Nothing => [])
          pool

  instOf : (List Elem -> Maybe Elem) -> List Elem -> Maybe (Deriv, Elem, Elem, Ty, Elem)
  instOf rebuild theta = do
    p' <- rebuild theta
    (dp, pty) <- reInfer sig ctx p' emptySkel
    ptyN <- nfT sig pty
    dp' <- if pty == ptyN then Just dp
           else Just (DElTyCoe (DNfExpandTy (DPresupElTy dp)) dp)
    let Prf (Elem.EqTy le re t) = ptyN
      | _ => Nothing
    let dR = DElReflect dp'
    leN <- nfE sig le
    reN <- nfE sig re
    let dRN = DElTrans (DElSym (DNfExpand (DPresupElL dR)))
                (DElTrans dR (DNfExpand (DPresupElR dR)))
    pure (dRN, leN, reN, t, p')

||| A step's ∀-lemma re-instantiated to MATCH a mismatched pair.
lemmaLeaf : Sig -> Ctx -> Step -> Nat -> Elem -> Elem -> Maybe (Deriv, Ty)
lemmaLeaf sig ctx step d x y = do
  -- enumerate only when the pair's rigid heads overlap the
  -- license's — typed enumeration on a hopeless pair is what blows
  -- the budget
  (_, le, re, _) <- reLicensed sig ctx step d
  let licTags = filter (/= "var") [headTag le, headTag re]
  let pairTags = filter (/= "var") [headTag x, headTag y]
  let True = any (\t => elem t licTags) pairTags
             || (null pairTags && null licTags)
    | False => Nothing
  xN <- nfE sig x
  yN <- nfE sig y
  let pool = map CtxVar [0 .. minus (length (toList ctx)) 1]
             ++ subterms 3 x ++ subterms 3 y
  pick xN yN (lemmaInsts sig ctx step d pool)
 where
  pick : Elem -> Elem -> List (Deriv, Elem, Elem, Ty, Elem) -> Maybe (Deriv, Ty)
  pick xN yN [] = dbg "lemma: none matched for \{show xN} / \{show yN}" Nothing
  pick xN yN ((dEq, leN, reN, t, _) :: rest) =
    if leN == xN && reN == yN then Just (dEq, t)
      else if leN == yN && reN == xN then Just (DElSym dEq, t)
      else pick xN yN rest

||| The HYPOTHESIS-SENSITIVE TYPE BRIDGE: a placement at a dependent
||| position shifts the equation's type by the step's own licensed
||| equation. Walk the two type spellings in parallel — α-equal parts
||| by refl, elements at the licensed pair by the licensed equation
||| itself (coerced to the position), congruence in between.
reBridgeE : Sig -> Ctx -> Maybe Step -> Nat -> Elem -> Elem -> Ty -> Maybe Deriv

reBridgeT : Sig -> Ctx -> Maybe Step -> Nat -> Ty -> Ty -> Maybe Deriv
reBridgeT sig ctx step d a b =
  if a == b
    then DTyRefl <$> reTy sig ctx a emptySkel
    else case (a, b) of
      (El x, El y) => DTyElCong <$> reBridgeE sig ctx step d x y Ty.UniverseTy
      (Prf x, Prf y) => DTyPrfCong <$> reBridgeE sig ctx step d x y Ty.PropTy
      (Ty.PiTy a0 b0, Ty.PiTy a1 b1) =>
        [| DTyPiCong (reBridgeT sig ctx step d a0 a1)
                     (reBridgeT sig (ctx :< a1) step (S d) b0 b1) |]
      (Ty.SigmaTy a0 b0, Ty.SigmaTy a1 b1) =>
        [| DTySigmaCong (reBridgeT sig ctx step d a0 a1)
                        (reBridgeT sig (ctx :< a1) step (S d) b0 b1) |]
      (Ty.SumTy a0 b0, Ty.SumTy a1 b1) =>
        [| DTySumCong (reBridgeT sig ctx step d a0 a1)
                      (reBridgeT sig ctx step d b0 b1) |]
      (Ty.Quotient a0 r0, Ty.Quotient a1 r1) => do
        da <- reBridgeT sig ctx step d a0 a1
        dr <- reBridgeE sig (ctx :< a1 :< substTy a1 Wk) step (2 + d) r0 r1 Ty.PropTy
        pure (DTyQuotCong da dr)
      _ =>
        -- shapes disagree only up to β: meet at nf, conjugated by
        -- the oracle
        (do aN <- nfT sig a
            bN <- nfT sig b
            let False = aN == a && bN == b
              | True => Nothing
            dBr <- reBridgeT sig ctx step d aN bN
            da <- reTy sig ctx a emptySkel
            db <- reTy sig ctx b emptySkel
            pure (DTyTrans (DNfExpandTy da)
                    (DTyTrans dBr (DTySym (DNfExpandTy db)))))
        -- or an INDEX REWRITE inside a code changes its shape only
        -- after β: propose the rewritten code (the licensed pair
        -- replaced throughout), derive its bridge by the congruence
        -- walk, β-meet the remainder
        <|> (byRewrite a b <|> (DTySym <$> byRewrite b a))
        <|> dbg "bridgeT shape (step? \{show (maybe False (const True) step)}): \{show a} VS \{show b}" Nothing
 where
  byRewrite : Ty -> Ty -> Maybe Deriv
  byRewrite src tgt = do
    stp <- step
    let El x = src
      | _ => Nothing
    (dEq0, le, re, t) <- reLicensed sig ctx stp 0
    goRw x le re tgt <|> goRw x re le tgt
   where
    goRw : Elem -> Elem -> Elem -> Ty -> Maybe Deriv

    goRw x le re tgt = do
      let x' = replE le re 0 x
      let False = x' == x
        | True => Nothing
      dc <- reBridgeE sig ctx step d x x' Ty.UniverseTy
      dEx' <- reTy sig ctx (El x') emptySkel
      exN <- nfT sig (El x')
      dBr2 <- if exN == tgt
                then do
                  dTgt <- reTy sig ctx tgt emptySkel
                  pure (DTyRefl dTgt)
                else reBridgeT sig ctx step d exN tgt
      pure (DTyTrans (DTyElCong dc)
              (DTyTrans (DNfExpandTy dEx') dBr2))

reBridgeE sig ctx step d x y exp =
  if x == y
    then DElRefl <$> reCheck sig ctx x exp emptySkel
    else
      (do stp <- step
          (dEq0, le, re, t) <- dbg "bridgeE: no license" (reLicensed sig ctx stp d)
          dEq <- if x == le && y == re then Just dEq0
                 else if x == re && y == le then Just (DElSym dEq0)
                 else dbg "bridgeE leaf: \{show x} / \{show y} VS licensed \{show le} / \{show re}" Nothing
          atExp dEq t)
      <|> (do (dEq, t) <- qPathLeaf sig ctx x y
              atExp dEq t)
      <|> (do stp <- step
              (dEq, t) <- lemmaLeaf sig ctx stp d x y
              atExp dEq t)
      <|> byHyp 0
      <|> byQuotHyp
      <|> (case (x, y) of
             (NatIntro1 u, NatIntro1 v) =>
               DElSucCong <$> reBridgeE sig ctx step d u v Ty.NatTy
             (NatElim z0 s0 t0, NatElim z1 s1 t1) => do
               -- same step branch; z and the index bridged, the
               -- constant motive at the position's own type
               let True = s0 == s1
                 | False => Nothing
               let mot = substTy exp Wk
               dmot <- reTy sig (ctx :< Ty.NatTy) mot emptySkel
               dzq <- reBridgeE sig ctx step d z0 z1 exp
               dst <- reCheck sig (ctx :< Ty.NatTy :< mot) s0
                        (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) emptySkel
               dtq <- reBridgeE sig ctx step d t0 t1 Ty.NatTy
               pure (DElNatECong dmot dzq (DElRefl dst) dtq)
             (PiApp f u, PiApp g v) => do
               let True = f == g
                 | False => Nothing
               (a, b) <- headPi sig ctx f u exp
               df <- reCheck sig ctx f (Ty.PiTy a b) emptySkel
               dc <- reBridgeE sig ctx step d u v a
               db <- reTy sig (ctx :< a) b emptySkel
                     <|> Just (DInvPiCod (DPresupElTy df))
               pure (DElAppCong (DElRefl df) dc db)
             (Elem.EqTy l0 r0 t0, Elem.EqTy l1 r1 t1) => do
               dt <- reBridgeT sig ctx step d t0 t1
               dl <- reBridgeE sig ctx step d l0 l1 t1
               dr <- reBridgeE sig ctx step d r0 r1 t1
               pure (DCodeEqCong dt dl dr)
             (QCtor sg0 k0 es0, QCtor sg1 k1 es1) => do
               let True = sg0 == sg1 && k0 == k1
                 | False => Nothing
               entry <- qEntry sg0 k0
               (tel, _, _) <- either (const Nothing) Just
                                (reflTel sg0 (qwAt k0) entry)
               let l0 = toList es0
               let l1 = toList es1
               let True = length l0 == length l1
                 | False => Nothing
               dSig <- reQSig sig ctx sg0
               ds <- traverse (\(j, e0, e1) => do
                       etj <- telInst tel j l0
                       reBridgeE sig ctx step d e0 e1 etj)
                     (zipWith3 (\j,a,b => (j,a,b))
                        [0 .. minus (length l0) 1] l0 l1)
               pure (DQCtorCong k0 dSig ds)
             _ => Nothing)
 where
  atExp : Deriv -> Ty -> Maybe Deriv
  atExp dEq t =
    if t == exp then Just dEq
      else do
        tN <- nfT sig t
        eN <- nfT sig exp
        let True = tN == eN
          | False => Nothing
        dt <- reTy sig ctx t emptySkel
        de <- reTy sig ctx exp emptySkel
        pure (DElEqTyCoe (DNfEqTy dt de) dEq)

  -- classes of related representatives: el-quot-eq with the witness
  -- found among the context's hypotheses
  byQuotHyp : Maybe Deriv
  byQuotHyp = do
    expN <- nfT sig exp
    let Ty.Quotient dom rel = expN
      | _ => Nothing
    let (Class x0, Class y0) = (x, y)
      | _ => Nothing
    da <- reCheck sig ctx x0 dom emptySkel
    db <- reCheck sig ctx y0 dom emptySkel
    dR <- reCheck sig (ctx :< dom :< substTy dom Wk) rel Ty.PropTy emptySkel
    let want = Prf (substElem rel (Ext (Ext Id x0) y0))
    wantN <- nfT sig want
    dh <- findHyp want wantN 0
    atExp (DElQuotEq da db dR dh) expN
   where
    findHyp : Ty -> Ty -> Nat -> Maybe Deriv
    findHyp want wantN i = do
      vty <- ctxAt ctx i
      (do let dv = DElVar i
          if vty == want then Just dv
            else do
              vN <- nfT sig vty
              let True = vN == wantN
                | False => Nothing
              dW <- reTy sig ctx want emptySkel
              pure (DElTyCoe (DNfEqTy (DPresupElTy dv) dW) dv))
       <|> findHyp want wantN (S i)

  -- a context hypothesis of the very equality, reflected (the pair
  -- being bridged is already normalized, so match at nf)
  byHyp : Nat -> Maybe Deriv
  byHyp i = do
    vty <- ctxAt ctx i
    (do vN <- nfT sig vty
        let Prf (Elem.EqTy le re t) = vN
          | _ => Nothing
        let dv = DElVar i
        dvN <- if vty == vN then Just dv
               else Just (DElTyCoe (DNfExpandTy (DPresupElTy dv)) dv)
        let dR = DElReflect dvN
        leN <- nfE sig le
        reN <- nfE sig re
        let dRN = DElTrans (DElSym (DNfExpand (DPresupElL dR)))
                    (DElTrans dR (DNfExpand (DPresupElR dR)))
        dEq <- if x == leN && y == reN then Just dRN
               else if x == reN && y == leN then Just (DElSym dRN)
               else Nothing
        atExp dEq t)
     <|> byHyp (S i)

-- Checking through lambdas with the step's bridges at the leaf: a
-- branch of an INDEXED motive placement may type only through the
-- step's own lemma (the nil case's vec k against vec (Z+k)).
chkStep sig ctx step d (PiIntro f) ty = do
  tyN <- nfT sig ty
  let Ty.PiTy a b = tyN
    | _ => Nothing
  da <- reTy sig ctx a emptySkel
  df <- chkStep sig (ctx :< a) step (S d) f b
  let d0 = DElPiI da df
  if tyN == ty then Just d0
    else do
      dT <- reTy sig ctx ty emptySkel
      pure (DElTyCoe (DTySym (DNfExpandTy dT)) d0)
chkStep sig ctx step d e ty =
  reCheck sig ctx e ty emptySkel
  <|> (do (de, ity) <- reInfer sig ctx e emptySkel
          iN <- nfT sig ity
          tN <- nfT sig ty
          dBr <- reBridgeTSearch sig ctx step d iN tN
          let deN = DElTyCoe (DNfExpandTy (DPresupElTy de)) de
          dT <- reTy sig ctx ty emptySkel
          pure (DElTyCoe (DTySym (DNfExpandTy dT))
                  (DElTyCoe dBr deN)))

-- The SEARCH-ENABLED bridge, for the step sites only (a dependent
-- shift whose lemma composite the certificate never recorded): the
-- step's own lemma re-instantiated, and the Σ-recoverable store's
-- lemmas whose generic heads match the code's subterms — two
-- proposal rounds (a dependent shift may compose two lemmas: the
-- element step's and the index law the shift exposes), the inner
-- walks always the plain bridge.
reBridgeTSearchN : Nat -> Sig -> Ctx -> Step -> Nat -> Ty -> Ty -> Maybe Deriv
reBridgeTSearchN Z sig ctx stp d a b = reBridgeT sig ctx (Just stp) d a b
reBridgeTSearchN (S fuel) sig ctx stp d a b =
  reBridgeT sig ctx (Just stp) d a b
  <|> (propose a b <|> (DTySym <$> propose b a))
 where
  goProp : Elem -> Elem -> Elem -> Elem -> Ty -> Maybe Deriv
  goProp pf x leN reN tgt = do
    let x' = replE leN reN 0 x
    let False = x' == x
      | True => Nothing
    -- the walk closes its changed leaves with the PROPOSING
    -- instance's own equation, carried as a synthesized license
    let instStp = MkStep True [] (LProof pf) [] False
    dc <- reBridgeE sig ctx (Just instStp) 0 x x' Ty.UniverseTy
    dEx' <- reTy sig ctx (El x') emptySkel
    exN <- nfT sig (El x')
    dBr2 <- if exN == tgt
              then DTyRefl <$> reTy sig ctx tgt emptySkel
              else reBridgeTSearchN fuel sig ctx stp d exN tgt
    pure (DTyTrans (DTyElCong dc)
            (DTyTrans (DNfExpandTy dEx') dBr2))

  firstProp : Elem -> Ty -> List (Deriv, Elem, Elem, Ty, Elem) -> Maybe Deriv
  firstProp x tgt [] = Nothing
  firstProp x tgt ((_, leN, reN, _, pf) :: rest) =
    goProp pf x leN reN tgt <|> goProp pf x reN leN tgt
    <|> firstProp x tgt rest

  -- a cheap syntactic pool filter: the instantiation slots of the
  -- current store's index lemmas are ℕ-shaped, and typed filtering
  -- of code-sized candidates is what blew the budget
  natish : Elem -> Bool
  natish (CtxVar _) = True
  natish NatIntro0 = True
  natish (NatIntro1 _) = True
  natish e@(NatElim _ _ _) =
    let t = headTag e in
    t /= "natelim:other"
  natish _ = False

  propose : Ty -> Ty -> Maybe Deriv
  propose src tgt = do
    let El x = src
      | _ => Nothing
    let pool = nub (filter natish
                      (map CtxVar [0 .. minus (length (toList ctx)) 1]
                       ++ subterms 4 x))
    firstProp x tgt (take 12 (lemmaInsts sig ctx stp d pool))

reBridgeTSearch sig ctx stp d a b = reBridgeTSearchN 2 sig ctx stp d a b

||| One side's rolling chain: side₀ ≐ cur, extended by a step.
stepChainE : Sig -> Ctx -> Ty -> (Deriv, Elem) -> Step -> Maybe (Deriv, Elem)
stepChainE sig ctx ty (chain, cur) step = do
  curN <- nfE sig cur
  chain2 <- if curN == cur then Just chain
            else Just (DElTrans chain (DNfExpand (DPresupElR chain)))
  (dPl, cur', plTy) <- dbg "step: place \{show step.path} in \{show curN}"
                         (rePlaceE sig ctx step 0 step.path ty curN
                            (Just (DPresupElR chain2)))
  -- the placement congruence concludes at its own computed spelling
  -- of the type; bridge back to the chain's spelling when nf-equal
  -- (a dependent position shifted beyond nf is outside this slice)
  dPl' <- if plTy == ty
            then Just dPl
            else do
              pN <- nfT sig plTy
              tN <- nfT sig ty
              if pN == tN
                then do
                  dTy <- reTy sig ctx ty emptySkel
                  pure (DElEqTyCoe (DNfEqTy (DPresupElTy (DPresupElL dPl)) dTy) dPl)
                else do
                  -- the dependent shift: bridge by the step's own
                  -- licensed equation, walked through the two types
                  dBr <- reBridgeTSearch sig ctx step 0 pN tN
                  dPlN <- do
                    dP <- reTy sig ctx pN emptySkel
                    pure (DElEqTyCoe (DNfEqTy (DPresupElTy (DPresupElL dPl)) dP) dPl)
                  dTy <- reTy sig ctx ty emptySkel
                  let atN = DElEqTyCoe dBr dPlN
                  pure (DElEqTyCoe (DTySym (DNfExpandTy dTy)) atN)
  pure (DElTrans chain2 dPl', cur')

stepChainT : Sig -> Ctx -> (Deriv, Ty) -> Step -> Maybe (Deriv, Ty)
stepChainT sig ctx (chain, cur) step = do
  curN <- nfT sig cur
  chain2 <- if curN == cur then Just chain
            else Just (DTyTrans chain (DNfExpandTy (DPresupTyR chain)))
  (dPl, cur') <- dbg "stepT: place \{show step.path} in \{show curN}"
                    (rePlaceT sig ctx step 0 step.path curN
                       (Just (DPresupTyR chain2)))
  pure (DTyTrans chain2 dPl, cur')

reEq sig ctx cert l r ty = reEqEnds sig ctx cert l r ty Nothing

reEqEnds sig ctx (MkECertF tyEx steps final) l r ty ends =
  (if reconDebug then trace "reqe: \{show l} EQ \{show r} nsteps \{show (length steps)} tyEx \{show (maybe False (const True) tyEx)}" (Just ()) else Just ()) >>= \_ => do
  (ty', pre) <- the (Maybe (Ty, Maybe Deriv)) $ case tyEx of
                  Nothing => Just (ty, Nothing)
                  Just (tyX, certT) => do
                    (dBr, tyR) <- reEqTyReach sig ctx certT ty tyX
                    Just (tyR, Just dBr)
  dl0 <- dbg "req: endpoint L \{show l} AT \{show ty'}" (endpoint l ty' pre (fst <$> ends))
  dr0 <- dbg "req: endpoint R \{show r} AT \{show ty'}" (endpoint r ty' pre (snd <$> ends))
  (chL, curL) <- dbg "req: chain L" (goSide ty' (DElRefl dl0, l) (filter (.onLhs) steps))
  (chR, curR) <- dbg "req: chain R" (goSide ty' (DElRefl dr0, r) (filter (not . (.onLhs)) steps))
  mid <- dbg "req: close, curL \{show curL} curR \{show curR}" (closeE sig ctx ty' chL curL chR curR final)
  let whole = DElTrans chL (DElTrans mid (DElSym chR))
  pure $ case pre of
    Nothing => whole
    Just dBr => DElEqTyCoe (DTySym dBr) whole
 where
  ||| An endpoint whose typing is hypothesis-sensitive rides the
  ||| bridge over one of the certificate's own steps; one that types
  ||| only at the equation's raw spelling rides the pre-bridge.
  checkBridged : Elem -> Ty -> Maybe Deriv

  endpoint : Elem -> Ty -> Maybe Deriv -> Maybe Deriv -> Maybe Deriv
  endpoint e t pre end =
    checkBridged e t
    <|> (do dBr <- pre
            d <- reCheck sig ctx e ty emptySkel
            pure (DElTyCoe dBr d))
    <|> (do d <- end
            case pre of
              Nothing => Just d
              Just dBr => Just (DElTyCoe dBr d))

  checkBridged e t =
    reCheck sig ctx e t emptySkel
    <|> (do (de, ety) <- reInfer sig ctx e emptySkel
            eN <- nfT sig ety
            tN <- nfT sig t
            dBr <- firstStep steps eN tN
            deN <- do dP <- reTy sig ctx eN emptySkel
                      pure (DElTyCoe (DNfExpandTy (DPresupElTy de)) de)
            dT <- reTy sig ctx t emptySkel
            pure (DElTyCoe (DTySym (DNfExpandTy dT))
                    (DElTyCoe dBr deN)))
    <|> byLicense steps
    <|> byPropExt
   where
    firstStep : List Step -> Ty -> Ty -> Maybe Deriv
    firstStep [] a b = reBridgeT sig ctx Nothing 0 a b
    firstStep (stp :: rest) a b =
      reBridgeT sig ctx (Just stp) 0 a b <|> firstStep rest a b

    -- both props hold — the target by reflexivity, the endpoint's own
    -- by the endpoint itself — so their Prfs are equal by
    -- code-prop-eq (propositional extensionality)
    byPropExt : Maybe Deriv
    byPropExt = do
      (de, ety) <- reInfer sig ctx e emptySkel
      etyN <- nfT sig ety
      tN <- nfT sig t
      let Prf psi = etyN
        | _ => Nothing
      let Prf phi = tN
        | _ => Nothing
      -- e at its nf'd Prf
      let deN = if ety == etyN then de
                else DElTyCoe (DNfExpandTy (DPresupElTy de)) de
      let dP = DInvPrfCode (DPresupElTy deN)
      dQ <- reCheck sig ctx phi Ty.PropTy emptySkel
      -- Prf phi inhabited under Prf psi: phi an equality whose sides
      -- agree up to nf
      dS <- do let Elem.EqTy a b t' = substElem phi Wk
                 | _ => Nothing
               let ctxS = ctx :< Prf psi
               aN <- nfE sig a
               bN <- nfE sig b
               let True = aN == bN
                 | False => Nothing
               da <- reCheck sig ctxS a t' emptySkel
               db <- reCheck sig ctxS b t' emptySkel
               pure $ if a == b then DElEqI (DElRefl da)
                                else DElEqI (DNfEq da db)
      -- Prf psi inhabited under Prf phi: the endpoint itself, weakened
      dT <- do let ctxT = ctx :< Prf phi
               (deW, etyW) <- reInfer sig ctxT (substElem e Wk) emptySkel
               let dPsiW = DPresupTyL (DTySubCongFix DSubWk
                             (DTyRefl (DTyPrf dP)))
               if etyW == substTy (Prf psi) Wk then Just deW
                 else do
                   wN <- nfT sig etyW
                   pN <- nfT sig (substTy (Prf psi) Wk)
                   let True = wN == pN
                     | False => Nothing
                   pure (DElTyCoe (DNfEqTy (DPresupElTy deW) dPsiW) deW)
      let dBr = DTyPrfCong (DCodePropEq dP dQ dS dT)
      -- e at Prf psi, ridden over the bridge, then back to raw t
      dTgt <- reTy sig ctx t emptySkel
      pure (DElTyCoe (DTySym (DNfExpandTy dTgt))
              (DElTyCoe dBr deN))

    -- the endpoint IS a side of some step's licensed equation: its
    -- typing is that equation's presupposition
    byLicense : List Step -> Maybe Deriv
    byLicense [] = Nothing
    byLicense (stp :: rest) =
      (do (dEq, le, re, lt) <- reLicensed sig ctx stp 0
          dp <- if e == le then Just (DPresupElL dEq)
                else if e == re then Just (DPresupElR dEq)
                else Nothing
          if lt == t then Just dp
            else do
              lN <- nfT sig lt
              tN <- nfT sig t
              let True = lN == tN
                | False => Nothing
              dT <- reTy sig ctx t emptySkel
              pure (DElTyCoe (DNfEqTy (DPresupElTy dp) dT) dp))
      <|> byLicense rest

  goSide : Ty -> (Deriv, Elem) -> List Step -> Maybe (Deriv, Elem)
  goSide t st [] = Just st
  goSide t st (stp :: rest) = do
    st' <- stepChainE sig ctx t st stp
    goSide t st' rest

reEqTy sig ctx cert a b = reEqTyEnds sig ctx cert a b (Nothing, Nothing)

reEqTyReach sig ctx cert@(MkECertF tyEx steps final) a b = do
  let Nothing = tyEx
    | _ => Nothing
  reach <|> ((\d => (d, b)) <$> reEqTy sig ctx cert a b)
 where
  goSideR : (Deriv, Ty) -> List Step -> Maybe (Deriv, Ty)

  reach : Maybe (Deriv, Ty)
  reach = do
    let [] = filter (not . (.onLhs)) steps
      | _ => Nothing
    let FBeta = final
      | _ => Nothing
    da0 <- reTy sig ctx a emptySkel
    (chA, curA) <- goSideR (DTyRefl da0, a) (filter (.onLhs) steps)
    curAN <- nfT sig curA
    pure (DTyTrans chA (DNfExpandTy (DPresupTyR chA)), curAN)

  goSideR st [] = Just st
  goSideR st (stp :: rest) = do
    st' <- stepChainT sig ctx st stp
    goSideR st' rest

reEqTyEnds sig ctx (MkECertF tyEx steps final) a b (endA, endB) = do
  let Nothing = tyEx
    | _ => dbg "reqty: nested tyEx" Nothing
  oneSidedR <|> (do
    da0 <- dbg "reqty: endpoint L \{show a}"
             (reTy sig ctx a emptySkel <|> endA)
    (chA, curA) <- dbg "reqty: chain L" (goSide (DTyRefl da0, a) (filter (.onLhs) steps))
    oneSided chA curA <|> twoSided chA curA)
 where
  goSide : (Deriv, Ty) -> List Step -> Maybe (Deriv, Ty)
  goSide st [] = Just st
  goSide st (stp :: rest) = do
    st' <- stepChainT sig ctx st stp
    goSide st' rest

  -- the far side untouched by steps and β-equal to where the chain
  -- landed: close by nf-expansion — its formation arrives FREE as
  -- the conclusion's presupposition, never re-derived
  oneSided : Deriv -> Ty -> Maybe Deriv
  oneSided chA curA = do
    let [] = filter (not . (.onLhs)) steps
      | _ => dbg "oneSided: b-side has steps" Nothing
    let FBeta = final
      | _ => dbg "oneSided: non-beta final" Nothing
    curAN <- nfT sig curA
    let True = curAN == b
      | False => dbg "oneSided: nf(curA) \{show curAN} /= b \{show b}" Nothing
    pure (DTyTrans chA (DNfExpandTy (DPresupTyR chA)))

  -- …and mirrored: the a side untouched, the b chain closing at a's
  -- spelling — a's formation likewise never re-derived
  oneSidedR : Maybe Deriv
  oneSidedR = do
    let [] = filter (.onLhs) steps
      | _ => Nothing
    let FBeta = final
      | _ => Nothing
    db0 <- reTy sig ctx b emptySkel <|> endB
    (chB, curB) <- goSide (DTyRefl db0, b) (filter (not . (.onLhs)) steps)
    curBN <- nfT sig curB
    let True = curBN == a
      | False => Nothing
    pure (DTySym (DTyTrans chB (DNfExpandTy (DPresupTyR chB))))

  twoSided : Deriv -> Ty -> Maybe Deriv
  twoSided chA curA = do
    db0 <- dbg "reqty: endpoint R \{show b}"
             (reTy sig ctx b emptySkel <|> endB)
    (chB, curB) <- dbg "reqty: chain R" (goSide (DTyRefl db0, b) (filter (not . (.onLhs)) steps))
    mid <- dbg "reqty: close, curA \{show curA} curB \{show curB}" (closeT sig ctx chA curA chB curB final)
    pure (DTyTrans chA (DTyTrans mid (DTySym chB)))

-- the final, elem side
closeE sig ctx ty chL curL chR curR FBeta =
  Just (DNfEq (DPresupElR chL) (DPresupElR chR))
closeE sig ctx ty chL curL chR curR FProp = do
  tyN <- nfT sig ty
  let coeIf : Deriv -> Deriv
      coeIf d = if tyN == ty then d
                else DElTyCoe (DNfExpandTy (DPresupElTy d)) d
  -- the prop rule concludes at nf(ty); the chains sit at ty — ride
  -- the chain's own presupposed formation back to the raw spelling
  let backIf : Deriv -> Deriv
      backIf d = if tyN == ty then d
                 else DElEqTyCoe
                        (DTySym (DNfExpandTy (DPresupElTy (DPresupElL chL)))) d
  case tyN of
    Prf _ => Just (backIf (DElPrfProp (coeIf (DPresupElR chL)) (coeIf (DPresupElR chR))))
    Ty.OneTy => Just (backIf (DElOneProp (coeIf (DPresupElR chL)) (coeIf (DPresupElR chR))))
    Ty.ZeroTy => Just (backIf (DElZeroProp (coeIf (DPresupElR chL)) (coeIf (DPresupElR chR))))
    _ => dbg "closeE: prop final at non-prop nf: \{show tyN}" Nothing
closeE sig ctx ty chL curL chR curR (FEtaPi c) = do
  tyN <- nfT sig ty
  case tyN of
    Ty.PiTy a b => do
      let coeIf : Deriv -> Deriv
          coeIf d = if tyN == ty then d
                    else DElTyCoe (DNfExpandTy (DPresupElTy d)) d
      let dl = coeIf (DPresupElR chL)
      let dr = coeIf (DPresupElR chR)
      dApp <- reEq sig (ctx :< a) c
                (PiApp (substElem curL Wk) (CtxVar 0))
                (PiApp (substElem curR Wk) (CtxVar 0)) b
      let two = DElPiEta dl dr dApp
      if tyN == ty then Just two
        else do
          dtN <- reTy sig ctx tyN emptySkel
          dt <- reTy sig ctx ty emptySkel
          pure (DElEqTyCoe (DNfEqTy dtN dt) two)
    _ => Nothing
closeE sig ctx ty chL curL chR curR (FPropExt fs fsk bs bsk) = do
  tyN <- nfT sig ty
  let True = tyN == Ty.PropTy
    | False => Nothing
  dP <- Just (DPresupElR chL)
  dQ <- Just (DPresupElR chR)
  dS <- reCheck sig (ctx :< Prf curL) fs (substTy (Prf curR) Wk) fsk
  dT <- reCheck sig (ctx :< Prf curR) bs (substTy (Prf curL) Wk) bsk
  dP' <- if ty == Ty.PropTy then Just dP
         else Just (DElTyCoe (DNfExpandTy (DPresupElTy dP)) dP)
  dQ' <- if ty == Ty.PropTy then Just dQ
         else Just (DElTyCoe (DNfExpandTy (DPresupElTy dQ)) dQ)
  pure (DCodePropEq dP' dQ' dS dT)
closeE sig ctx ty chL curL chR curR (FEtaSigma c1 c2) = do
  tyN <- nfT sig ty
  case tyN of
    Ty.SigmaTy a b => do
      let coeIf : Deriv -> Deriv
          coeIf d = if tyN == ty then d
                    else DElTyCoe (DNfExpandTy (DPresupElTy d)) d
      let dl = coeIf (DPresupElR chL)
      let dr = coeIf (DPresupElR chR)
      dP1 <- reEq sig ctx c1 (SigmaElim1 curL) (SigmaElim1 curR) a
      dP2 <- reEq sig ctx c2 (SigmaElim2 curL) (SigmaElim2 curR)
               (substTy b (Ext Id (SigmaElim1 curL)))
      let two = DElSigmaEta dl dr dP1 dP2
      if tyN == ty then Just two
        else do
          dtN <- reTy sig ctx tyN emptySkel
          dt <- reTy sig ctx ty emptySkel
          pure (DElEqTyCoe (DNfEqTy dtN dt) two)
    _ => Nothing
closeE sig ctx ty chL curL chR curR (FWitness mc) = do
  tyN <- nfT sig ty
  let Ty.Quotient dom rel = tyN
    | _ => dbg "closeE: witness final at a non-quotient" Nothing
  (case (curL, curR) of
     (Class x, Class y) => witClass tyN dom rel x y False
     _ => do
       -- the chains may end at un-β-reduced spellings of the
       -- classes: meet them at nf
       lN <- nfE sig curL
       rN <- nfE sig curR
       let (Class x, Class y) = (lN, rN)
         | _ => dbg "closeE: witness final, ends not classes" Nothing
       witClass tyN dom rel x y True)
 where
  witClass : Ty -> Ty -> Elem -> Elem -> Elem -> Bool -> Maybe Deriv
  witClass tyN dom rel x y bridge = do
      dx <- reCheck sig ctx x dom emptySkel
      dy <- reCheck sig ctx y dom emptySkel
      drel <- reCheck sig (ctx :< dom :< substTy dom Wk) rel Ty.PropTy emptySkel
      relInst <- nfE sig (substElem rel (Ext (Ext Id x) y))
      dw <- case (relInst, mc) of
              (Squash Ty.OneTy, _) => do
                let dstar = DElSquashI DElOneI
                dPrf <- reTy sig ctx (Prf (substElem rel (Ext (Ext Id x) y))) emptySkel
                pure (DElTyCoe (DTySym (DNfExpandTy dPrf)) dstar)
              (Elem.EqTy wl wr wt, Just c) => do
                dweq <- reEq sig ctx c wl wr wt
                let dstar = DElEqI dweq
                dPrf <- reTy sig ctx (Prf (substElem rel (Ext (Ext Id x) y))) emptySkel
                pure (DElTyCoe (DTySym (DNfExpandTy dPrf)) dstar)
              _ => Nothing
      let two = DElQuotEq dx dy drel dw
      twoAt <- if tyN == ty then Just two
                 else do
                   dtN <- reTy sig ctx tyN emptySkel
                   dt <- reTy sig ctx ty emptySkel
                   pure (DElEqTyCoe (DNfEqTy dtN dt) two)
      pure $ if bridge
               then DElTrans (DNfExpand (DPresupElR chL))
                      (DElTrans twoAt (DElSym (DNfExpand (DPresupElR chR))))
               else twoAt
closeE sig ctx ty chL curL chR curR _ = dbg "closeE: untranslated final" Nothing

-- the final, type side
closeT sig ctx chA curA chB curB FBeta =
  Just (DNfEqTy (DPresupTyR chA) (DPresupTyR chB))
closeT sig ctx chA curA chB curB (FPrfCong c) =
  case (curA, curB) of
    (Prf p, Prf q) =>
      -- the codes' Ω-typings arrive by inversion of the chains' own
      -- presupposed formations — an unfolded code (a quot-elim'd Ω)
      -- is never re-derived bare
      DTyPrfCong <$> reEqEnds sig ctx c p q Ty.PropTy
                       (Just (DInvPrfCode (DPresupTyR chA),
                              DInvPrfCode (DPresupTyR chB)))
    _ => Nothing
closeT sig ctx chA curA chB curB (FQuotCong c) =
  case (curA, curB) of
    (Ty.Quotient d0 r0, Ty.Quotient d1 r1) => do
      let True = d0 == d1
        | False => Nothing
      dr <- reEq sig (ctx :< d0 :< substTy d0 Wk) c r0 r1 Ty.PropTy
      dd <- reTy sig ctx d0 emptySkel
      pure (DTyQuotCong (DTyRefl dd) dr)
    _ => Nothing
closeT sig ctx chA curA chB curB (FPiCong dc cc) =
  case (curA, curB) of
    (Ty.PiTy a0 b0, Ty.PiTy a1 b1) => do
      -- component formations by inversion of the chains' presupposed
      -- formations — unfolded spellings never re-derived bare
      let fA = DPresupTyR chA
      let fB = DPresupTyR chB
      dd <- reEqTyEnds sig ctx dc a0 a1
              (Just (DInvPiDom fA), Just (DInvPiDom fB))
      dcc <- reEqTyEnds sig (ctx :< a1) cc b0 b1
               (Nothing, Just (DInvPiCod fB))
      pure (DTyPiCong dd dcc)
    _ => Nothing
closeT sig ctx chA curA chB curB (FSigmaCong dc cc) =
  case (curA, curB) of
    (Ty.SigmaTy a0 b0, Ty.SigmaTy a1 b1) => do
      let fA = DPresupTyR chA
      let fB = DPresupTyR chB
      dd <- reEqTyEnds sig ctx dc a0 a1
              (Just (DInvSigmaDom fA), Just (DInvSigmaDom fB))
      dcc <- reEqTyEnds sig (ctx :< a1) cc b0 b1
               (Nothing, Just (DInvSigmaCod fB))
      pure (DTySigmaCong dd dcc)
    _ => Nothing
closeT sig ctx chA curA chB curB (FSumCong lc rc) =
  case (curA, curB) of
    (Ty.SumTy a0 b0, Ty.SumTy a1 b1) => do
      dl <- reEqTy sig ctx lc a0 a1
      dr <- reEqTy sig ctx rc b0 b1
      pure (DTySumCong dl dr)
    _ => Nothing
closeT sig ctx chA curA chB curB _ = Nothing

-- ===== The EMISSION entry points (called by the elaborator's seat) =====

||| A type item's formation derivation.
export
emitTyDef : Sig -> KTyDefArt -> Maybe Deriv
emitTyDef sig art =
  case art.ttele of
    [] => do
      _ <- clearMemos ()
      reTy sig [<] art.tty art.ttySkel
    _ => Nothing

||| A body's typing at its stated type, with the fallbacks: plain
||| reconstruction, formation-threaded (the type derivation rides
||| down the spelling), and the nf route (solved holes unfolded, the
||| result ridden back on the type derivation).
emitBody : Sig -> Ctx -> Elem -> Ty -> Skel -> Deriv -> Maybe Deriv
emitBody sig ctx body ty bodySk dT =
  reCheck sig ctx body ty bodySk
  <|> reCheckF sig ctx body ty bodySk dT
  <|> (do tyN <- nfT sig ty
          let False = tyN == ty
            | True => Nothing
          let dTN = DPresupTyR (DNfExpandTy dT)
          d <- dbg "emit: body"
                 (reCheck sig ctx body tyN bodySk
                  <|> reCheckF sig ctx body tyN bodySk dTN)
          pure (DElTyCoe (DTySym (DNfExpandTy dT)) d))

||| A def item's two derivations (the type's formation and the
||| body's typing). Nothing = emission does not cover the item (the
||| residue).
export
emitDef : Sig -> KDefArt -> Maybe (Deriv, Deriv)
emitDef sig art =
  case art.tele of
    [] => do
      _ <- clearMemos ()
      dT <- dbg "emit: type" (reTy sig [<] art.dty art.dtySkel)
      dt <- emitBody sig [<] art.body art.dty art.bodySkel dT
      pure (dT, dt)
    _ => Nothing

||| A solution telescope's formation derivation plus the context's
||| entrywise type derivations — solutions carry no skeletons, so
||| everything is emitted bare.
emitTele : Sig -> Ctx -> Maybe Deriv
emitTele sig [<] = Just DCtxEmpty
emitTele sig (rest :< a) = do
  dG <- emitTele sig rest
  dA <- reTy sig rest a emptySkel
  pure (DCtxExt dG dA)

||| A hole solution's derivations: the telescope's formation, the
||| type's formation and the body's typing in the telescope context.
export
emitSol : Sig -> Ctx -> Elem -> Ty -> Maybe (Deriv, Deriv, Deriv)
emitSol sig delta body ty = do
  _ <- clearMemos ()
  dCtx <- emitTele sig delta
  dT <- reTy sig delta ty emptySkel
  dt <- emitBody sig delta body ty emptySkel dT
  pure (dCtx, dT, dt)

||| A type-valued hole solution's derivations.
export
emitTySol : Sig -> Ctx -> Ty -> Maybe (Deriv, Deriv)
emitTySol sig delta ty = do
  _ <- clearMemos ()
  dCtx <- emitTele sig delta
  dT <- reTy sig delta ty emptySkel
  pure (dCtx, dT)
