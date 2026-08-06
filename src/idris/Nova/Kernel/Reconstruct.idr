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
import Data.SnocList

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel
import Nova.Kernel.Derivation

%default covering

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

pSqW : Payload -> Maybe (Elem, Skel)
pSqW (PSquashWit e s) = Just (e, s)
pSqW _ = Nothing

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

mutual
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
  reTy sig ctx (Ty.NuTy f) sk = Nothing        -- later slice
  reTy sig ctx (QSort sg k es) sk = Nothing    -- later slice

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
  reInfer sig ctx (CtxVar i) sk = do
    ty <- ctxAt ctx i
    pure (DElVar i, ty)
  reInfer sig ctx (Elem.SigVar x es) sk =
    case sigLookup x sig of
      Just (SigDef delta _ _ a) => do
        d <- reSubN sig ctx es (toList delta)
        pure (DElSig x d, substTy a (embed es))
      Just (SigDecl delta _ a) => do
        d <- reSubN sig ctx es (toList delta)
        pure (DElSig x d, substTy a (embed es))
      _ => Nothing
  reInfer sig ctx (PiApp f e) sk = do
    (df, fty) <- reInfer sig ctx f (childAt 0 sk)
    case fty of
      Ty.PiTy a b => do
        de <- reCheck sig ctx e a (childAt 1 sk)
        db <- reTy sig (ctx :< a) b emptySkel
        pure (DElPiE df de db, substTy b (Ext Id e))
      _ => Nothing
  reInfer sig ctx (SigmaElim1 t) sk = do
    (dt, tty) <- reInfer sig ctx t (childAt 0 sk)
    case tty of
      Ty.SigmaTy a _ => pure (DElSigmaE1 dt, a)
      _ => Nothing
  reInfer sig ctx (SigmaElim2 t) sk = do
    (dt, tty) <- reInfer sig ctx t (childAt 0 sk)
    case tty of
      Ty.SigmaTy _ b => pure (DElSigmaE2 dt, substTy b (Ext Id (SigmaElim1 t)))
      _ => Nothing
  reInfer sig ctx (Let a b) sk = do
    (da, aty) <- reInfer sig ctx a (childAt 0 sk)
    let hyp = Prf (Elem.EqTy (CtxVar 0) (substElem a Wk) (substTy aty Wk))
    (db, bty) <- reInfer sig (ctx :< aty :< hyp) b (childAt 1 sk)
    pure (DElLet da db, substTy bty (Ext (Ext Id a) Star))
  reInfer sig ctx (NatElim z s t) sk = do
    (mot, motSk) <- payload pMot sk
    dmot <- reTy sig (ctx :< Ty.NatTy) mot motSk
    dz <- reCheck sig ctx z (substTy mot (Ext Id NatIntro0)) (childAt 0 sk)
    ds <- reCheck sig (ctx :< Ty.NatTy :< mot) s
            (substTy mot (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk)) (childAt 1 sk)
    dt <- reCheck sig ctx t Ty.NatTy (childAt 2 sk)
    pure (DElNatE dmot dz ds dt, substTy mot (Ext Id t))
  reInfer sig ctx (SumElim l r t) sk = do
    (mot, motSk) <- payload pMot sk
    (dt, tty) <- reInfer sig ctx t (childAt 2 sk)
    case tty of
      Ty.SumTy a b => do
        dmot <- reTy sig (ctx :< Ty.SumTy a b) mot motSk
        dl <- reCheck sig (ctx :< a) l (substTy mot (Ext Wk (Inj1 (CtxVar 0)))) (childAt 0 sk)
        dr <- reCheck sig (ctx :< b) r (substTy mot (Ext Wk (Inj2 (CtxVar 0)))) (childAt 1 sk)
        pure (DElSumE dt dmot dl dr, substTy mot (Ext Id t))
      _ => Nothing
  reInfer sig ctx NatIntro0 sk = Just (DElNatZ, Ty.NatTy)
  reInfer sig ctx (NatIntro1 t) sk = do
    d <- reCheck sig ctx t Ty.NatTy (childAt 0 sk)
    pure (DElNatS d, Ty.NatTy)
  reInfer sig ctx OneIntro sk = Just (DElOneI, Ty.OneTy)
  -- universe and Ω codes
  reInfer sig ctx Elem.ZeroTy sk = Just (DCodeZero, Ty.UniverseTy)
  reInfer sig ctx Elem.OneTy sk = Just (DCodeOne, Ty.UniverseTy)
  reInfer sig ctx Elem.NatTy sk = Just (DCodeNat, Ty.UniverseTy)
  reInfer sig ctx (Elem.PiTy a b) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    db <- reCheck sig (ctx :< El a) b Ty.UniverseTy (childAt 1 sk)
    pure (DCodePi da db, Ty.UniverseTy)
  reInfer sig ctx (Elem.SigmaTy a b) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    db <- reCheck sig (ctx :< El a) b Ty.UniverseTy (childAt 1 sk)
    pure (DCodeSigma da db, Ty.UniverseTy)
  reInfer sig ctx (Elem.SumTy a b) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    db <- reCheck sig ctx b Ty.UniverseTy (childAt 1 sk)
    pure (DCodeSum da db, Ty.UniverseTy)
  reInfer sig ctx (Elem.QuotTy a r) sk = do
    da <- reCheck sig ctx a Ty.UniverseTy (childAt 0 sk)
    dr <- reCheck sig (ctx :< El a :< substTy (El a) Wk) r Ty.PropTy (childAt 1 sk)
    pure (DCodeQuot da dr, Ty.UniverseTy)
  reInfer sig ctx (Elem.EqTy l r t) sk = do
    dt <- reTy sig ctx t (childAt 2 sk)
    dl <- reCheck sig ctx l t (childAt 0 sk)
    dr <- reCheck sig ctx r t (childAt 1 sk)
    pure (DCodeEq dt dl dr, Ty.PropTy)
  reInfer sig ctx (Squash a) sk = do
    da <- reTy sig ctx a (childAt 0 sk)
    pure (DCodeSquash da, Ty.PropTy)
  reInfer sig ctx (Class a) sk = Nothing       -- intro: checking-only
  reInfer sig ctx _ sk = Nothing

  ||| Checking: switch/expose payloads translated on the β-only
  ||| route; intro forms structurally; fallback infer-and-α-compare
  ||| (with a β coercion when spellings differ).
  export
  reCheck : Sig -> Ctx -> Elem -> Ty -> Skel -> Maybe Deriv
  reCheck sig ctx e ty sk =
    case payload pSw sk of
      Just cert =>
        if betaOnly cert
          then do
            (d, ity) <- reInfer sig ctx e (dropP isSw sk)
            coerce sig ctx d ity ty
          else Nothing
      Nothing =>
        case payload pExp sk of
          Just (tyX, cert) =>
            if betaOnly cert
              then do
                d <- reCheckGo sig ctx e tyX (dropP isExp sk)
                dX <- reTy sig ctx tyX emptySkel
                dT <- reTy sig ctx ty emptySkel
                pure (DElTyCoe (DTySym (DNfEqTy dT dX)) d)
              else Nothing
          Nothing => reCheckGo sig ctx e ty sk

  reCheckGo : Sig -> Ctx -> Elem -> Ty -> Skel -> Maybe Deriv
  reCheckGo sig ctx (PiIntro f) ty sk =
    case ty of
      Ty.PiTy a b => do
        da <- reTy sig ctx a emptySkel
        df <- reCheck sig (ctx :< a) f b (childAt 0 sk)
        pure (DElPiI da df)
      _ => Nothing
  reCheckGo sig ctx (SigmaIntro u v) ty sk =
    case ty of
      Ty.SigmaTy a b => do
        du <- reCheck sig ctx u a (childAt 0 sk)
        db <- reTy sig (ctx :< a) b emptySkel
        dv <- reCheck sig ctx v (substTy b (Ext Id u)) (childAt 1 sk)
        pure (DElSigmaI du db dv)
      _ => Nothing
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
  reCheckGo sig ctx (ZeroElim t) ty sk = do
    dA <- reTy sig ctx ty emptySkel
    dt <- reCheck sig ctx t Ty.ZeroTy (childAt 0 sk)
    pure (DElZeroE dA dt)
  reCheckGo sig ctx Star ty sk =
    case payload pRefl sk of
      Just cert =>
        if betaOnly cert
          then case ty of
            Prf (Elem.EqTy l r t) => do
              dl <- reCheck sig ctx l t emptySkel
              dr <- reCheck sig ctx r t emptySkel
              pure (DElEqI (DNfEq dl dr))
            _ => Nothing
          else Nothing
      Nothing =>
        case payload pSqW sk of
          Just (w, wSk) =>
            case ty of
              Prf (Squash a) => do
                dw <- reCheck sig ctx w a wSk
                pure (DElSquashI dw)
              _ => Nothing
          Nothing => Nothing
  reCheckGo sig ctx e ty sk = do
    (d, ity) <- reInfer sig ctx e sk
    coerce sig ctx d ity ty

  ||| α-equal: the derivation already concludes at the expected
  ||| spelling; otherwise coerce along a β equation.
  coerce : Sig -> Ctx -> Deriv -> Ty -> Ty -> Maybe Deriv
  coerce sig ctx d ity ty =
    if ity == ty
      then Just d
      else do
        di <- reTy sig ctx ity emptySkel
        dt <- reTy sig ctx ty emptySkel
        pure (DElTyCoe (DNfEqTy di dt) d)

-- ===== The shadow entry point =====

||| Reconstruct a def item's two derivations (the type's formation
||| and the body's typing). Nothing = outside this slice's coverage.
export
reDefArt : Sig -> KDefArt -> Maybe (Deriv, Deriv)
reDefArt sig art =
  case art.tele of
    [] => do
      dT <- reTy sig [<] art.dty art.dtySkel
      dt <- reCheck sig [<] art.body art.dty art.bodySkel
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
