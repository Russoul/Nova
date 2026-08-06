module Nova.Kernel.Reconstruct

-- Phase 2 of the derivation rework (docs/NovaPipeline.txt, "The
-- derivation rework"): the RECONSTRUCTOR — untrusted machinery
-- rebuilding NovaDerivations.txt derivations from the elaborator's
-- current artifacts (core terms plus annotation skeletons). During
-- the bridge it SHADOWS the old kernel: wherever it produces a
-- derivation, conclude's verdict must agree with the old kernel's
-- (a mismatch is loud); where it cannot yet, it returns Nothing and
-- the old kernel's verdict stands alone. Its incompleteness is a
-- coverage ratchet, never a soundness question.
--
-- Coverage of this first slice: the structural core — formation,
-- the element formers with their skeleton motives, sig references —
-- with conversion sites translated on the β-ONLY route (a switch or
-- expose certificate with no steps and an FBeta final becomes
-- el-ty-coe over nf-eq-ty; a refl-eq ⋆ becomes el-eq-i over nf-eq).
-- Step-carrying certificates (the rewrite traces) translate in a
-- later slice via the retirement map.

import Data.List
import Data.Maybe
import Data.SnocList
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

nfE : Sig -> Elem -> Maybe Elem
nfE sig e = case runKM (kElem sig e) fuelR of
  Right (x, _) => Just x
  Left _ => Nothing

nfT : Sig -> Ty -> Maybe Ty
nfT sig t = case runKM (kTy sig t) fuelR of
  Right (x, _) => Just x
  Left _ => Nothing

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

||| … and for type equations Γ ⊦ a ≐ b.
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
  reTy sig ctx Ty.ZeroTy sk = Just DTyZero
  reTy sig ctx Ty.OneTy sk = Just DTyOne
  reTy sig ctx Ty.NatTy sk = Just DTyNat
  reTy sig ctx Ty.UniverseTy sk = Just DTyUniv
  reTy sig ctx Ty.PropTy sk = Just DTyProp
  reTy sig ctx (Ty.PiTy a b) sk =
    [| DTyPi (reTy sig ctx a (childAt 0 sk)) (reTy sig (ctx :< a) b (childAt 1 sk)) |]
  reTy sig ctx (Ty.SigmaTy a b) sk =
    [| DTySigma (reTy sig ctx a (childAt 0 sk)) (reTy sig (ctx :< a) b (childAt 1 sk)) |]
  reTy sig ctx (Ty.SumTy a b) sk =
    [| DTySum (reTy sig ctx a (childAt 0 sk)) (reTy sig ctx b (childAt 1 sk)) |]
  reTy sig ctx (El e) sk = DTyEl <$> reCheck sig ctx e Ty.UniverseTy (childAt 0 sk)
  reTy sig ctx (Prf e) sk = DTyPrf <$> reCheck sig ctx e Ty.PropTy (childAt 0 sk)
  reTy sig ctx (Ty.Quotient a r) sk = do
    da <- reTy sig ctx a (childAt 0 sk)
    dr <- reCheck sig (ctx :< a :< substTy a Wk) r Ty.PropTy (childAt 1 sk)
    pure (DTyQuot da dr)
  reTy sig ctx (Ty.SigVar x es) sk =
    case sigLookup x sig of
      Just (SigTyDef delta _ _) => DTySig x <$> reSubN sig ctx es (toList delta)
      Just (SigTyDecl delta _) => DTySig x <$> reSubN sig ctx es (toList delta)
      _ => Nothing
  reTy sig ctx (Ty.NuTy f) sk = DTyNu <$> rePoly sig ctx f
  reTy sig ctx (QSort sg k es) sk = do
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
  reInfer sig ctx e sk =
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
    (mot, motSk) <- payload pMot sk
    wd <- payload pWDc sk
    (dq, qty) <- reInfer sig ctx q (childAt 1 sk) >>= expose sig
    case qty of
      Ty.Quotient a r => do
        dmot <- reTy sig (ctx :< Ty.Quotient a r) mot motSk
        df <- reCheck sig (ctx :< a) f
                (substTy mot (Ext Wk (Class (CtxVar 0)))) (childAt 0 sk)
        let wk3 = Chain Wk (Chain Wk Wk)
        let wdCtx = ctx :< a :< substTy a Wk :< Prf r
        dresp <- reEq sig wdCtx wd
                   (substElem f (Ext wk3 (CtxVar 2)))
                   (substElem f (Ext wk3 (CtxVar 1)))
                   (substTy mot (Ext wk3 (Class (CtxVar 2))))
        pure (DElQuotE dq dmot df dresp, substTy mot (Ext Id q))
      _ => Nothing
  reInferGo sig ctx _ sk = Nothing

  ||| Checking: switch/expose payloads translated on the β-only
  ||| route; intro forms structurally; fallback infer-and-α-compare
  ||| (with a β coercion when spellings differ).
  export
  reCheck : Sig -> Ctx -> Elem -> Ty -> Skel -> Maybe Deriv
  reCheck sig ctx e ty sk =
    case payload pSw sk of
      Just cert => do
        (d, ity) <- reInfer sig ctx e (dropP isSw sk)
        if ity == ty
          then Just d
          else do
            dEq <- reEqTy sig ctx cert ity ty
            pure (DElTyCoe dEq d)
      Nothing =>
        case payload pExp sk of
          Just (tyX, cert) => do
            d <- reCheckGo sig ctx e tyX (dropP isExp sk)
            dEq <- reEqTy sig ctx cert ty tyX
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
  reCheckF sig ctx e ty sk dF = reCheck sig ctx e ty sk

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

rePlaceT : Sig -> Ctx -> Step -> Nat -> List Nat -> Ty -> Maybe (Deriv, Ty)

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
rePlaceE : Sig -> Ctx -> Step -> Nat -> List Nat -> Ty -> Elem -> Maybe (Deriv, Elem, Ty)
rePlaceE sig ctx step d [] exp cur = do
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
rePlaceE sig ctx step d (i :: p) exp cur =
  case (cur, i) of
    (NatIntro1 t, 0) => do
      (dc0, t', chTy) <- rePlaceE sig ctx step d p Ty.NatTy t
      dc <- eqAtNf sig ctx dc0 chTy Ty.NatTy
      pure (DElSucCong dc, NatIntro1 t', Ty.NatTy)
    (PiApp f e, 0) => do
      (a, b) <- headPi sig ctx f e exp
      (dc0, f', chTy) <- rePlaceE sig ctx step d p (Ty.PiTy a b) f
      dc <- eqAtNf sig ctx dc0 chTy (Ty.PiTy a b)
      de <- reCheck sig ctx e a emptySkel
      db <- reTy sig (ctx :< a) b emptySkel
            <|> Just (DInvPiCod (DPresupElTy (DPresupElL dc)))
      pure (DElAppCong dc (DElRefl de) db, PiApp f' e, substTy b (Ext Id e))
    (PiApp f e, 1) => do
      (a, b) <- headPi sig ctx f e exp
      df <- reCheck sig ctx f (Ty.PiTy a b) emptySkel
      (dc0, e', chTy) <- rePlaceE sig ctx step d p a e
      dc <- eqAtNf sig ctx dc0 chTy a
      db <- reTy sig (ctx :< a) b emptySkel
            <|> Just (DInvPiCod (DPresupElTy df))
      pure (DElAppCong (DElRefl df) dc db, PiApp f e', substTy b (Ext Id e'))
    (Inj1 a, 0) =>
      case exp of
        Ty.SumTy l r => do
          (dc0, a', chTy) <- rePlaceE sig ctx step d p l a
          dc <- eqAtNf sig ctx dc0 chTy l
          dr <- reTy sig ctx r emptySkel
          pure (DElInj1Cong dc dr, Inj1 a', Ty.SumTy l r)
        _ => Nothing
    (Inj2 b, 0) =>
      case exp of
        Ty.SumTy l r => do
          (dc0, b', chTy) <- rePlaceE sig ctx step d p r b
          dc <- eqAtNf sig ctx dc0 chTy r
          dl <- reTy sig ctx l emptySkel
          pure (DElInj2Cong dc dl, Inj2 b', Ty.SumTy l r)
        _ => Nothing
    (NatElim z st t, 2) => do
      let mot = substTy exp Wk
      dmot <- reTy sig (ctx :< Ty.NatTy) mot emptySkel
      dz <- reCheck sig ctx z exp emptySkel
      dst <- reCheck sig (ctx :< Ty.NatTy :< mot) st
               (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) emptySkel
      (dc0, t', chTy) <- rePlaceE sig ctx step d p Ty.NatTy t
      dc <- eqAtNf sig ctx dc0 chTy Ty.NatTy
      pure (DElNatECong dmot (DElRefl dz) (DElRefl dst) dc,
            NatElim z st t', exp)
    (NatElim z st t, 0) => do
      let mot = substTy exp Wk
      dmot <- reTy sig (ctx :< Ty.NatTy) mot emptySkel
      (dc, z', _) <- rePlaceE sig ctx step d p exp z
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
                        (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) st
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
          (dc0, t', chTy) <- rePlaceE sig ctx step d p (Ty.SumTy a b) t
          dc <- eqAtNf sig ctx dc0 chTy (Ty.SumTy a b)
          pure (DElSumECong dc dmot (DElRefl dl) (DElRefl dr),
                SumElim l r t', exp)
        _ => Nothing
    (Class a, 0) =>
      case exp of
        Ty.Quotient dom rel => do
          (dc, a', _) <- rePlaceE sig ctx step d p dom a
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
      (dc0, t', chTy) <- rePlaceE sig ctx step d p nuT t
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
      (dc0, t', chTy) <- rePlaceE sig ctx step d p ttyN t
      dc <- eqAtNf sig ctx dc0 chTy ttyN
      pure (DElProj1Cong dc, SigmaElim1 t', a)
    (SigmaElim2 t, 0) => do
      (dt, tty) <- reInfer sig ctx t emptySkel
      ttyN <- nfT sig tty
      let Ty.SigmaTy _ b = ttyN
        | _ => Nothing
      (dc0, t', chTy) <- rePlaceE sig ctx step d p ttyN t
      dc <- eqAtNf sig ctx dc0 chTy ttyN
      pure (DElProj2Cong dc, SigmaElim2 t',
            substTy b (Ext Id (SigmaElim1 t')))
    (Elem.EqTy l r t, 0) => do
      dt <- reTy sig ctx t emptySkel
      (dc, l', _) <- rePlaceE sig ctx step d p t l
      dr <- reCheck sig ctx r t emptySkel
      pure (DCodeEqCong (DTyRefl dt) dc (DElRefl dr), Elem.EqTy l' r t, Ty.PropTy)
    (Elem.EqTy l r t, 1) => do
      dt <- reTy sig ctx t emptySkel
      dl <- reCheck sig ctx l t emptySkel
      (dc, r', _) <- rePlaceE sig ctx step d p t r
      pure (DCodeEqCong (DTyRefl dt) (DElRefl dl) dc, Elem.EqTy l r' t, Ty.PropTy)
    (Elem.EqTy l r t, 2) => do
      -- a rewrite in the ∈-slot: the sides ride the CHILD TYPE
      -- EQUATION itself into the new type — the hypothesis-sensitive
      -- bridge, derived rather than oracled
      (dc, t') <- rePlaceT sig ctx step d p t
      dl <- reCheck sig ctx l t emptySkel
      dr <- reCheck sig ctx r t emptySkel
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
      (dc0, e', chTy) <- rePlaceE sig ctx step d p ety e0
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
      (dc, a', _) <- rePlaceE sig ctx step d p Ty.UniverseTy a
      db <- reCheck sig ctx b Ty.UniverseTy emptySkel
      pure (DCodeSumCong dc (DElRefl db), Elem.SumTy a' b, Ty.UniverseTy)
    (Elem.SumTy a b, 1) => do
      da <- reCheck sig ctx a Ty.UniverseTy emptySkel
      (dc, b', _) <- rePlaceE sig ctx step d p Ty.UniverseTy b
      pure (DCodeSumCong (DElRefl da) dc, Elem.SumTy a b', Ty.UniverseTy)
    _ => Nothing

rePlaceT sig ctx step d (0 :: p) (El e) = do
  (dc, e', _) <- rePlaceE sig ctx step d p Ty.UniverseTy e
  pure (DTyElCong dc, El e')
rePlaceT sig ctx step d (0 :: p) (Prf e) = do
  (dc, e', _) <- rePlaceE sig ctx step d p Ty.PropTy e
  pure (DTyPrfCong dc, Prf e')
rePlaceT sig ctx step d (0 :: p) (Ty.PiTy a b) = do
  (dc, a') <- rePlaceT sig ctx step d p a
  db <- reTy sig (ctx :< a') b emptySkel
  pure (DTyPiCong dc (DTyRefl db), Ty.PiTy a' b)
rePlaceT sig ctx step d (1 :: p) (Ty.PiTy a b) = do
  da <- reTy sig ctx a emptySkel
  (dc, b') <- rePlaceT sig (ctx :< a) step (S d) p b
  pure (DTyPiCong (DTyRefl da) dc, Ty.PiTy a b')
rePlaceT sig ctx step d (0 :: p) (Ty.SigmaTy a b) = do
  (dc, a') <- rePlaceT sig ctx step d p a
  db <- reTy sig (ctx :< a') b emptySkel
  pure (DTySigmaCong dc (DTyRefl db), Ty.SigmaTy a' b)
rePlaceT sig ctx step d (1 :: p) (Ty.SigmaTy a b) = do
  da <- reTy sig ctx a emptySkel
  (dc, b') <- rePlaceT sig (ctx :< a) step (S d) p b
  pure (DTySigmaCong (DTyRefl da) dc, Ty.SigmaTy a b')
rePlaceT sig ctx step d (0 :: p) (Ty.SumTy a b) = do
  (dc, a') <- rePlaceT sig ctx step d p a
  db <- reTy sig ctx b emptySkel
  pure (DTySumCong dc (DTyRefl db), Ty.SumTy a' b)
rePlaceT sig ctx step d (1 :: p) (Ty.SumTy a b) = do
  da <- reTy sig ctx a emptySkel
  (dc, b') <- rePlaceT sig ctx step d p b
  pure (DTySumCong (DTyRefl da) dc, Ty.SumTy a b')
rePlaceT sig ctx step d (i :: p) (QSort sg k es) = do
  entry <- qEntry sg k
  (tel, _, _) <- either (const Nothing) Just (reflTel sg (qwAt k) entry)
  let l = toList es
  e <- getAt i l
  ety <- telInst tel i l
  (dc0, e', chTy) <- rePlaceE sig ctx step d p ety e
  dc <- eqAtNf sig ctx dc0 chTy ety
  dSig <- reQSig sig ctx sg
  ds <- traverse (\(j, ej) =>
          if j == i then Just dc
          else do etj <- telInst tel j l
                  DElRefl <$> reCheck sig ctx ej etj emptySkel)
        (zip [0 .. minus (length l) 1] l)
  l' <- maybe Nothing Just (setAtL i e' l)
  pure (DTyQSortCong k dSig ds, QSort sg k (cast l'))
rePlaceT sig ctx step d path ty = Nothing

||| A path-constructor equation with a SEARCHED instantiation: for
||| each equation entry of the signature, candidate spines are built
||| slot by slot from the mismatched pair's own constructor arguments
||| and the context's variables, type-filtered; the first
||| instantiation whose reflected endpoints match the pair (either
||| orientation) wins. Conclude arbitrates, as with every guess.
qPathLeaf : Sig -> Ctx -> Elem -> Elem -> Maybe (Deriv, Ty)
qPathLeaf sig ctx x y = do
  let QCtor sg _ xs = x
    | _ => Nothing
  let QCtor sg' _ ys = y
    | _ => Nothing
  let True = sg == sg'
    | False => Nothing
  xN <- nfE sig x
  yN <- nfE sig y
  let cands = map CtxVar [0 .. minus (length (toList ctx)) 1]
              ++ toList xs ++ toList ys
  tryEntries sg xN yN cands (eqPositions sg 0)
 where
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
      _ => dbg "bridgeT shape: \{show a} VS \{show b}" Nothing

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
      <|> byHyp 0
      <|> (case (x, y) of
             (NatIntro1 u, NatIntro1 v) =>
               DElSucCong <$> reBridgeE sig ctx step d u v Ty.NatTy
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

||| One side's rolling chain: side₀ ≐ cur, extended by a step.
stepChainE : Sig -> Ctx -> Ty -> (Deriv, Elem) -> Step -> Maybe (Deriv, Elem)
stepChainE sig ctx ty (chain, cur) step = do
  curN <- nfE sig cur
  chain2 <- if curN == cur then Just chain
            else Just (DElTrans chain (DNfExpand (DPresupElR chain)))
  (dPl, cur', plTy) <- dbg "step: place \{show step.path} in \{show curN}" (rePlaceE sig ctx step 0 step.path ty curN)
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
                  dBr <- reBridgeT sig ctx (Just step) 0 pN tN
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
  (dPl, cur') <- dbg "stepT: place \{show step.path} in \{show curN}" (rePlaceT sig ctx step 0 step.path curN)
  pure (DTyTrans chain2 dPl, cur')

reEq sig ctx cert l r ty = reEqEnds sig ctx cert l r ty Nothing

reEqEnds sig ctx (MkECertF tyEx steps final) l r ty ends =
  (if reconDebug then trace "reqe: \{show l} EQ \{show r} nsteps \{show (length steps)} tyEx \{show (maybe False (const True) tyEx)}" (Just ()) else Just ()) >>= \_ => do
  (ty', pre) <- the (Maybe (Ty, Maybe Deriv)) $ case tyEx of
                  Nothing => Just (ty, Nothing)
                  Just (tyX, certT) => do
                    dBr <- reEqTy sig ctx certT ty tyX
                    Just (tyX, Just dBr)
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
   where
    firstStep : List Step -> Ty -> Ty -> Maybe Deriv
    firstStep [] a b = reBridgeT sig ctx Nothing 0 a b
    firstStep (stp :: rest) a b =
      reBridgeT sig ctx (Just stp) 0 a b <|> firstStep rest a b

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

reEqTy sig ctx (MkECertF tyEx steps final) a b = do
  let Nothing = tyEx
    | _ => dbg "reqty: nested tyEx" Nothing
  da0 <- dbg "reqty: endpoint L \{show a}" (reTy sig ctx a emptySkel)
  db0 <- dbg "reqty: endpoint R \{show b}" (reTy sig ctx b emptySkel)
  (chA, curA) <- dbg "reqty: chain L" (goSide (DTyRefl da0, a) (filter (.onLhs) steps))
  (chB, curB) <- dbg "reqty: chain R" (goSide (DTyRefl db0, b) (filter (not . (.onLhs)) steps))
  mid <- dbg "reqty: close, curA \{show curA} curB \{show curB}" (closeT sig ctx chA curA chB curB final)
  pure (DTyTrans chA (DTyTrans mid (DTySym chB)))
 where
  goSide : (Deriv, Ty) -> List Step -> Maybe (Deriv, Ty)
  goSide st [] = Just st
  goSide st (stp :: rest) = do
    st' <- stepChainT sig ctx st stp
    goSide st' rest

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
    _ => Nothing
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
  case (curL, curR, tyN) of
    (Class x, Class y, Ty.Quotient dom rel) => do
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
      if tyN == ty then Just two
        else do
          dtN <- reTy sig ctx tyN emptySkel
          dt <- reTy sig ctx ty emptySkel
          pure (DElEqTyCoe (DNfEqTy dtN dt) two)
    _ => Nothing
closeE sig ctx ty chL curL chR curR _ = Nothing

-- the final, type side
closeT sig ctx chA curA chB curB FBeta =
  Just (DNfEqTy (DPresupTyR chA) (DPresupTyR chB))
closeT sig ctx chA curA chB curB (FPrfCong c) =
  case (curA, curB) of
    (Prf p, Prf q) => DTyPrfCong <$> reEq sig ctx c p q Ty.PropTy
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
      dd <- reEqTy sig ctx dc a0 a1
      dcc <- reEqTy sig (ctx :< a1) cc b0 b1
      pure (DTyPiCong dd dcc)
    _ => Nothing
closeT sig ctx chA curA chB curB (FSigmaCong dc cc) =
  case (curA, curB) of
    (Ty.SigmaTy a0 b0, Ty.SigmaTy a1 b1) => do
      dd <- reEqTy sig ctx dc a0 a1
      dcc <- reEqTy sig (ctx :< a1) cc b0 b1
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

-- ===== The shadow entry point =====

||| A type item's formation derivation.
export
shadowTyDef : Sig -> Nat -> KTyDefArt -> Maybe (Either KErr ())
shadowTyDef sig fuel art =
  case art.ttele of
    [] => do
      dT <- reTy sig [<] art.tty art.ttySkel
      pure $ do
        jT <- concludeItem sig fuel dT
        case jT of
          JTy t => if t == art.tty then Right ()
                   else Left "shadow: type item concluded a different spelling"
          _ => Left "shadow: type item concluded a non-formation judgement"
    _ => Nothing

||| Reconstruct a def item's two derivations (the type's formation
||| and the body's typing). Nothing = outside this slice's coverage.
export
reDefArt : Sig -> KDefArt -> Maybe (Deriv, Deriv)
reDefArt sig art =
  case art.tele of
    [] => do
      dT <- dbg "defart: type" (reTy sig [<] art.dty art.dtySkel)
      -- when the raw spelling carries solved holes whose re-derivation
      -- is hypothesis-sensitive, check at nf (holes unfolded) and ride
      -- dT back to the spelling
      dt <- reCheck sig [<] art.body art.dty art.bodySkel
            <|> reCheckF sig [<] art.body art.dty art.bodySkel dT
            <|> (do tyN <- nfT sig art.dty
                    let False = tyN == art.dty
                      | True => Nothing
                    let dTN = DPresupTyR (DNfExpandTy dT)
                    d <- dbg "defart: body"
                           (reCheck sig [<] art.body tyN art.bodySkel
                            <|> reCheckF sig [<] art.body tyN art.bodySkel dTN)
                    pure (DElTyCoe (DTySym (DNfExpandTy dT)) d))
      pure (dT, dt)
    _ => Nothing

||| The shadow verdict: Nothing = not covered (silent); Just (Left e)
||| = the reconstructor produced a derivation that conclude REJECTED
||| or that concluded a different judgement (loud); Just (Right ())
||| = agreement.
export
shadowDef : Sig -> Nat -> KDefArt -> Maybe (Either KErr ())
shadowDef sig fuel art = do
  (dT, dt) <- reDefArt sig art
  pure $ do
    jT <- concludeItem sig fuel dT
    case jT of
      JTy t => if t == art.dty then Right ()
               else Left "shadow: type formation concluded [\{show t}] expected [\{show art.dty}]"
      _ => Left "shadow: type derivation concluded a non-formation judgement"
    jt <- concludeItem sig fuel dt
    case jt of
      JEl b ty =>
        if b == art.body && ty == art.dty then Right ()
        else Left "shadow: body typing concluded a different judgement"
      _ => Left "shadow: body derivation concluded a non-typing judgement"
