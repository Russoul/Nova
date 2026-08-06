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

pWDc : Payload -> Maybe ECert
pWDc (PWD c) = Just c
pWDc _ = Nothing

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

||| Certificate translation (the retirement map, executable): an
||| equality derivation for Γ ⊦ l ≐ r : ty from an ECert.
export
reEq : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> Maybe Deriv

||| … and for type equations Γ ⊦ a ≐ b.
export
reEqTy : Sig -> Ctx -> ECert -> Ty -> Ty -> Maybe Deriv

closeE : Sig -> Ctx -> Ty -> Deriv -> Elem -> Deriv -> Elem -> Final -> Maybe Deriv
closeT : Sig -> Ctx -> Deriv -> Ty -> Deriv -> Ty -> Final -> Maybe Deriv

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
  reTy sig ctx (Ty.NuTy f) sk = DTyNu <$> rePoly sig ctx f
  reTy sig ctx (QSort sg k es) sk = Nothing    -- later slice

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
  reInfer sig ctx (Out t) sk = do
    (dt, tty) <- reInfer sig ctx t (childAt 0 sk)
    case tty of
      Ty.NuTy f => do
        dp <- rePoly sig ctx f
        pure (DElNuE dp dt, El (reflectPoly f (Elem.NuTy f)))
      _ => Nothing
  reInfer sig ctx (QuotElim f q) sk = do
    (mot, motSk) <- payload pMot sk
    wd <- payload pWDc sk
    (dq, qty) <- reInfer sig ctx q (childAt 1 sk)
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
  reInfer sig ctx _ sk = Nothing

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
  reCheckGo sig ctx (ZeroElim t) ty sk = do
    dA <- reTy sig ctx ty emptySkel
    dt <- reCheck sig ctx t Ty.ZeroTy (childAt 0 sk)
    pure (DElZeroE dA dt)
  reCheckGo sig ctx Star ty sk =
    case payload pRefl sk of
      Just cert =>
        case ty of
          Prf (Elem.EqTy l r t) => DElEqI <$> reEq sig ctx cert l r t
          _ => Nothing
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

-- ===== Certificate translation (the retirement map) =====

||| The licensed equation of a step at depth d (crossed binders),
||| reconstructed AT the leaf's context: the proof spelling is
||| weakened and re-inferred there, its type exposed to a literal
||| equality prop by the oracle when needed.
reLicensed : Sig -> Ctx -> Step -> Nat -> Maybe (Deriv, Elem, Elem, Ty)
reLicensed sig ctx step d =
  case step.lic of
    LProof p => do
      let [] = step.sels
        | _ => Nothing
      let pw = wkN d p
      (dp, pty) <- reInfer sig ctx pw emptySkel
      ptyN <- nfT sig pty
      dp' <- if pty == ptyN then Just dp
             else Just (DElTyCoe (DNfExpandTy (DPresupElTy dp)) dp)
      case ptyN of
        Prf (Elem.EqTy le re t) => do
          let dEq = DElReflect dp'
          -- normalize the licensed sides (replay compares nfs)
          leN <- nfE sig le
          reN <- nfE sig re
          let dEqN = DElTrans (DElSym (DNfExpand (DPresupElL dEq)))
                       (DElTrans dEq (DNfExpand (DPresupElR dEq)))
          let (dO, lO, rO) = if step.flip
                               then (DElSym dEqN, reN, leN)
                               else (dEqN, leN, reN)
          pure (dO, lO, rO, t)
        _ => Nothing
    LPath _ _ _ => Nothing

||| Placement: rewrite `cur` at `path` by the step's licensed
||| equation, emitting the congruence chain; returns the derivation
||| (cur ≐ cur′ at the expected type) and cur′.
rePlaceE : Sig -> Ctx -> Step -> Nat -> List Nat -> Ty -> Elem -> Maybe (Deriv, Elem, Ty)
rePlaceE sig ctx step d [] exp cur = do
  (dEq, le, re, t) <- reLicensed sig ctx step d
  let True = cur == le
    | False => Nothing
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
      (dc, t', _) <- rePlaceE sig ctx step d p Ty.NatTy t
      pure (DElSucCong dc, NatIntro1 t', Ty.NatTy)
    (PiApp f e, 0) => do
      (df, fty) <- reInfer sig ctx f emptySkel
      case fty of
        Ty.PiTy a b => do
          (dc, f', _) <- rePlaceE sig ctx step d p (Ty.PiTy a b) f
          de <- reCheck sig ctx e a emptySkel
          db <- reTy sig (ctx :< a) b emptySkel
          pure (DElAppCong dc (DElRefl de) db, PiApp f' e, substTy b (Ext Id e))
        _ => Nothing
    (PiApp f e, 1) => do
      (df, fty) <- reInfer sig ctx f emptySkel
      case fty of
        Ty.PiTy a b => do
          (dc, e', _) <- rePlaceE sig ctx step d p a e
          db <- reTy sig (ctx :< a) b emptySkel
          pure (DElAppCong (DElRefl df) dc db, PiApp f e', substTy b (Ext Id e'))
        _ => Nothing
    (Inj1 a, 0) =>
      case exp of
        Ty.SumTy l r => do
          (dc, a', _) <- rePlaceE sig ctx step d p l a
          dr <- reTy sig ctx r emptySkel
          pure (DElInj1Cong dc dr, Inj1 a', Ty.SumTy l r)
        _ => Nothing
    (Inj2 b, 0) =>
      case exp of
        Ty.SumTy l r => do
          (dc, b', _) <- rePlaceE sig ctx step d p r b
          dl <- reTy sig ctx l emptySkel
          pure (DElInj2Cong dc dl, Inj2 b', Ty.SumTy l r)
        _ => Nothing
    (Class a, 0) =>
      case exp of
        Ty.Quotient dom rel => do
          (dc, a', _) <- rePlaceE sig ctx step d p dom a
          dr <- reCheck sig (ctx :< dom :< substTy dom Wk) rel Ty.PropTy emptySkel
          pure (DElClassCong dc dr, Class a', Ty.Quotient dom rel)
        _ => Nothing
    (SigmaElim1 t, 0) => do
      (dt, tty) <- reInfer sig ctx t emptySkel
      (dc, t', _) <- rePlaceE sig ctx step d p tty t
      case tty of
        Ty.SigmaTy a _ => pure (DElProj1Cong dc, SigmaElim1 t', a)
        _ => Nothing
    (SigmaElim2 t, 0) => do
      (dt, tty) <- reInfer sig ctx t emptySkel
      (dc, t', _) <- rePlaceE sig ctx step d p tty t
      case tty of
        Ty.SigmaTy _ b => pure (DElProj2Cong dc, SigmaElim2 t',
                                substTy b (Ext Id (SigmaElim1 t')))
        _ => Nothing
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
    (Elem.SumTy a b, 0) => do
      (dc, a', _) <- rePlaceE sig ctx step d p Ty.UniverseTy a
      db <- reCheck sig ctx b Ty.UniverseTy emptySkel
      pure (DCodeSumCong dc (DElRefl db), Elem.SumTy a' b, Ty.UniverseTy)
    (Elem.SumTy a b, 1) => do
      da <- reCheck sig ctx a Ty.UniverseTy emptySkel
      (dc, b', _) <- rePlaceE sig ctx step d p Ty.UniverseTy b
      pure (DCodeSumCong (DElRefl da) dc, Elem.SumTy a b', Ty.UniverseTy)
    _ => Nothing

rePlaceT : Sig -> Ctx -> Step -> Nat -> List Nat -> Ty -> Maybe (Deriv, Ty)
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
rePlaceT sig ctx step d path ty = Nothing

||| One side's rolling chain: side₀ ≐ cur, extended by a step.
stepChainE : Sig -> Ctx -> Ty -> (Deriv, Elem) -> Step -> Maybe (Deriv, Elem)
stepChainE sig ctx ty (chain, cur) step = do
  curN <- nfE sig cur
  chain2 <- if curN == cur then Just chain
            else Just (DElTrans chain (DNfExpand (DPresupElR chain)))
  (dPl, cur', plTy) <- rePlaceE sig ctx step 0 step.path ty curN
  -- the placement congruence concludes at its own computed spelling
  -- of the type; bridge back to the chain's spelling when nf-equal
  -- (a dependent position shifted beyond nf is outside this slice)
  dPl' <- if plTy == ty
            then Just dPl
            else do
              pN <- nfT sig plTy
              tN <- nfT sig ty
              let True = pN == tN
                | False => Nothing
              dTy <- reTy sig ctx ty emptySkel
              pure (DElEqTyCoe (DNfEqTy (DPresupElTy (DPresupElL dPl)) dTy) dPl)
  pure (DElTrans chain2 dPl', cur')

stepChainT : Sig -> Ctx -> (Deriv, Ty) -> Step -> Maybe (Deriv, Ty)
stepChainT sig ctx (chain, cur) step = do
  curN <- nfT sig cur
  chain2 <- if curN == cur then Just chain
            else Just (DTyTrans chain (DNfExpandTy (DPresupTyR chain)))
  (dPl, cur') <- rePlaceT sig ctx step 0 step.path curN
  pure (DTyTrans chain2 dPl, cur')

reEq sig ctx (MkECertF tyEx steps final) l r ty = do
  (ty', pre) <- the (Maybe (Ty, Maybe Deriv)) $ case tyEx of
                  Nothing => Just (ty, Nothing)
                  Just (tyX, certT) => do
                    dBr <- reEqTy sig ctx certT ty tyX
                    Just (tyX, Just dBr)
  dl0 <- reCheck sig ctx l ty' emptySkel
  dr0 <- reCheck sig ctx r ty' emptySkel
  (chL, curL) <- goSide (DElRefl dl0, l) (filter (.onLhs) steps)
  (chR, curR) <- goSide (DElRefl dr0, r) (filter (not . (.onLhs)) steps)
  mid <- closeE sig ctx ty' chL curL chR curR final
  let whole = DElTrans chL (DElTrans mid (DElSym chR))
  pure $ case pre of
    Nothing => whole
    Just dBr => DElEqTyCoe (DTySym dBr) whole
 where
  goSide : (Deriv, Elem) -> List Step -> Maybe (Deriv, Elem)
  goSide st [] = Just st
  goSide st (stp :: rest) = do
    st' <- stepChainE sig ctx ty st stp
    goSide st' rest

reEqTy sig ctx (MkECertF tyEx steps final) a b = do
  let Nothing = tyEx
    | _ => Nothing
  da0 <- reTy sig ctx a emptySkel
  db0 <- reTy sig ctx b emptySkel
  (chA, curA) <- goSide (DTyRefl da0, a) (filter (.onLhs) steps)
  (chB, curB) <- goSide (DTyRefl db0, b) (filter (not . (.onLhs)) steps)
  mid <- closeT sig ctx chA curA chB curB final
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
  case tyN of
    Prf _ => Just (DElPrfProp (coeIf (DPresupElR chL)) (coeIf (DPresupElR chR)))
    Ty.OneTy => Just (DElOneProp (coeIf (DPresupElR chL)) (coeIf (DPresupElR chR)))
    Ty.ZeroTy => Just (DElZeroProp (coeIf (DPresupElR chL)) (coeIf (DPresupElR chR)))
    _ => Nothing
 where
  x : ()
  x = ()
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
