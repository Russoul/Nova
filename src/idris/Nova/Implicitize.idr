module Nova.Implicitize

-- The IMPLICITIZE distiller mode — Phase 3c of
-- docs/NovaPerfectSurface.txt: rewrite a corpus so that
-- survey-approved binder positions become {x : A} implicits and the
-- arguments at those positions disappear from every use site,
-- verified end to end.
--
-- The pipeline, elide-then-verify at corpus scale:
--
--   1. elaborate the original closure (must be accepted); survey its
--      Σ for the CANDIDATE table (Nova.Recovery.implicitizables),
--      restricted to names defined by plain def/declaration items;
--   2. transform to the OVERRIDE FORM — candidate types get their
--      {}-binders, every use-site argument at a candidate position
--      is wrapped as a {t} override. Semantically identical by
--      construction; its elaboration runs with the TRIAL hook
--      (ElabSt.impTrialOn), which replays the hypothetical elided
--      recovery at every override and records whether it reproduces
--      the written value α-exactly;
--   3. fold the trial: a position survives iff EVERY site recovered
--      it (the intersection policy — the final corpus carries no
--      overrides); the rest revert to explicit binders;
--   4. transform the ORIGINAL units again, dropping arguments at the
--      surviving positions, and write the result;
--   5. verify: the written files re-parse to the transformed ASTs
--      (the printer identity), the closure re-elaborates ACCEPTED,
--      and the final kernel Σ is entrywise α-identical to the
--      original run's (the erasure contract — implicitness never
--      reaches the core, so the Σs must agree exactly).
--
-- Name resolution is replicated per module (own items shadow opened
-- imports; qualified names pass through) — a mismatch here cannot
-- corrupt anything, only mis-transform, and the Σ gate catches it.

import Data.Either
import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.SnocList

import Me.Russoul.Text.Range

import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Loader
import Nova.Kernel.Syntax
import Nova.Recovery
import Nova.Distill

import System.File

%default covering

-- ===== Per-module name resolution =====

qualify : (mname : String) -> String -> String
qualify "" x = x
qualify m x = "\{m}.\{x}"

||| surface name → Σ name: the module's own items shadow its opened
||| imports; a name matching neither is already a Σ path.
unitResolver : ModUnit -> (String -> String)
unitResolver u =
  let own = mapMaybe (\(_, it) => case it of
              SDef x _ _ _ => Just (x, qualify u.mname x)
              SDeclDef _ x _ => Just (x, qualify u.mname x)
              STypeDef x _ => Just (x, qualify u.mname x)
              _ => Nothing) u.mitems
      opened = concatMap (\i => map (\o => (o, "\{i.mname}.\{o}")) i.opens) u.mimports
  in \x => case lookup x own of
             Just q => q
             Nothing => fromMaybe x (lookup x opened)

-- ===== The transformers =====

||| Wrap: candidate-position arguments become {t} overrides (the
||| trial form). Drop: they disappear (the final form); a site whose
||| every argument would disappear keeps them as overrides instead —
||| a bare reference is not an application (defensive: the trial fold
||| already reverts such positions).
public export
data IMode = MWrap | MDrop

||| Mark the candidate positions of a leading Π-telescope implicit.
impTy : List Nat -> STy -> STy
impTy poss = go 0
 where
  go : Nat -> STy -> STy
  go i (STyPi x a b) =
    if i `elem` poss then STyImpPi x a (go (S i) b) else STyPi x a (go (S i) b)
  go i (STyImpPi x a b) = STyImpPi x a (go (S i) b)
  go i ty = ty

parameters (resolve : String -> String, cands : List (String, List Nat), mode : IMode)
  ||| Rebuild one application spine: arguments at the head's candidate
  ||| positions wrap or drop (children already transformed).
  xfSpine : SElem -> List SElem -> SElem
  xfSpine hd args =
    case hd of
      SSig _ x =>
        case lookup (resolve x) cands of
          Just poss =>
            let idxd = zip [0 .. minus (length args) 1] args
                keepers = filter (\(i, _) => not (i `elem` poss)) idxd
            in case (mode, keepers) of
                 (MWrap, _) => foldl SApp hd (map (mk MWrap poss) idxd)
                 (MDrop, []) => foldl SApp hd (map (mk MWrap poss) idxd)
                 (MDrop, _) => foldl SApp hd (mapMaybe (mkDrop poss) idxd)
          Nothing => foldl SApp hd args
      _ => foldl SApp hd args
   where
    mk : IMode -> List Nat -> (Nat, SElem) -> SElem
    mk _ poss (i, a) = if i `elem` poss then SImpArg a else a

    mkDrop : List Nat -> (Nat, SElem) -> Maybe SElem
    mkDrop poss (i, a) = if i `elem` poss then Nothing else Just a

  mutual
    xfE : SElem -> SElem
    xfE e = case e of
      SApp _ _ =>
        let (hd, args) = spine e []
        in xfSpine (xfE hd) (map xfE args)
      SVar _ _ _ => e
      SSig _ _ => e
      SUnitI => e
      SZeroN => e
      SSuc t => SSuc (xfE t)
      SLam x b => SLam x (xfE b)
      SLet x d b => SLet x (xfE d) (xfE b)
      SPair a b => SPair (xfE a) (xfE b)
      SProj1 t => SProj1 (xfE t)
      SProj2 t => SProj2 (xfE t)
      SZeroC => e
      SOneC => e
      SNatC => e
      SPiC x a b => SPiC x (xfE a) (xfE b)
      SSigmaC x a b => SSigmaC x (xfE a) (xfE b)
      SSumC a b => SSumC (xfE a) (xfE b)
      SQuotC a x y r => SQuotC (xfE a) x y (xfE r)
      SEqC l r t => SEqC (xfE l) (xfE r) (xfT t)
      SZeroElim t => SZeroElim (xfE t)
      SNatElim n mot z n2 ih s t => SNatElim n (xfT mot) (xfE z) n2 ih (xfE s) (xfE t)
      SInj1 t => SInj1 (xfE t)
      SInj2 t => SInj2 (xfE t)
      SSumElim z mot a l b r t => SSumElim z (xfT mot) a (xfE l) b (xfE r) (xfE t)
      SClass t => SClass (xfE t)
      SQuotElim z mot a f qq => SQuotElim z (xfT mot) a (xfE f) (xfE qq)
      SNuC f => SNuC (xfP f)
      SOut t => SOut (xfE t)
      SCorec x a f u => SCorec x (xfE a) (xfE f) (xfE u)
      SCoind nx ny r pw mx my mh w => SCoind nx ny (xfE r) (xfE pw) mx my mh (xfE w)
      SSquash t => SSquash (xfT t)
      SStar => e
      SStarWit w => SStarWit (xfE w)
      SStarUsing ns => e
      SSquashElim s x b => SSquashElim (xfE s) x (xfE b)
      SChain h links => SChain (xfE h) (map (\(j, m) => (xfE j, xfE m)) links)
      SAnn t ty => SAnn (xfE t) (xfT ty)
      SImpArg t => SImpArg (xfE t)
     where
      spine : SElem -> List SElem -> (SElem, List SElem)
      spine (SApp f a) acc = spine f (a :: acc)
      spine h acc = (h, acc)

    xfT : STy -> STy
    xfT ty = case ty of
      STyPi x a b => STyPi x (xfT a) (xfT b)
      STyImpPi x a b => STyImpPi x (xfT a) (xfT b)
      STySigma x a b => STySigma x (xfT a) (xfT b)
      STySum a b => STySum (xfT a) (xfT b)
      STyQuot a x y r => STyQuot (xfT a) x y (xfE r)
      STyEq l r t => STyEq (xfE l) (xfE r) (xfT t)
      STyEl t => STyEl (xfE t)
      STyPrf t => STyPrf (xfE t)
      STyNu f => STyNu (xfP f)
      _ => ty

    xfP : SPoly -> SPoly
    xfP p = case p of
      SPHole => p
      SPConst a => SPConst (xfE a)
      SPProd f g => SPProd (xfP f) (xfP g)
      SPSum f g => SPSum (xfP f) (xfP g)
      SPSigma x a f => SPSigma x (xfE a) (xfP f)
      SPPi x a f => SPPi x (xfE a) (xfP f)

  xfQTm : SQTm -> SQTm
  xfQTm (SQVar n i) = SQVar n i
  xfQTm (SQAppE f e) = SQAppE (xfQTm f) (xfE e)
  xfQTm (SQAppI f a) = SQAppI (xfQTm f) (xfQTm a)

  xfQDecl : SQDecl -> SQDecl
  xfQDecl (MkSQDecl n bs res) =
    MkSQDecl n (map (\(x, d) => (x, case d of
                                     Left t => Left (xfT t)
                                     Right qt => Right (xfQTm qt))) bs)
      (case res of
         SQResU => SQResU
         SQResEl t => SQResEl (xfQTm t)
         SQResEq l r u => SQResEq (xfQTm l) (xfQTm r) (xfQTm u))

  ||| Transform one item: a candidate def's own type gets its
  ||| {}-binders; every embedded element and type gets the use-site
  ||| rewrite. Clausal and data items are never implicitized
  ||| themselves — their embedded pieces are use sites like any other.
  xfItem : (ownQ : String -> String) -> SItem -> SItem
  xfItem ownQ (SDef x ty body mu) =
    let ty' = case lookup (ownQ x) cands of
                Just poss => impTy poss (xfT ty)
                Nothing => xfT ty
    in SDef x ty' (xfE body) mu
  xfItem ownQ (SDeclDef r x ty) =
    let ty' = case lookup (ownQ x) cands of
                Just poss => impTy poss (xfT ty)
                Nothing => xfT ty
    in SDeclDef r x ty'
  xfItem ownQ (STypeDef x ty) = STypeDef x (xfT ty)
  xfItem ownQ (SData params ds) =
    SData (map (\(x, t) => (x, xfT t)) params) (map xfQDecl ds)
  xfItem ownQ (SClausalDef r x ty eta wit cls) =
    SClausalDef r x (xfT ty) eta (map xfE wit)
      (map (\c => { crhs $= xfE } c) cls)

||| Transform a whole module.
xfUnit : List (String, List Nat) -> IMode -> ModUnit -> ModUnit
xfUnit cands mode u =
  let resolve = unitResolver u
      ownQ = qualify u.mname
      body' = map (map (\(r, it) => (r, xfItem resolve cands mode ownQ it))) u.mbody
  in { mbody := body', mitems := mapMaybe (\e => case e of
                                             Right ri => Just ri
                                             Left _ => Nothing) body' } u

-- ===== The driver =====

-- ===== Drift attribution =====
--
-- The Σ gate can fail HONESTLY: a recovered argument may be a
-- convertible-but-different spelling of what the author wrote (the
-- trial measures each site against its written override, but nested
-- elisions cascade — a recovered inner spelling changes the outer
-- inferred types the outer holes bind from). When that happens, the
-- parallel tree diff below attributes the drift to the nearest
-- enclosing def-headed spines whose arguments differ, those defs
-- revert to explicit binders, and the final stage re-runs — a
-- fixpoint on the α-gate itself.

mutual
  dhE : Elem -> Elem -> List String
  dhE o n =
    if show o == show n then [] else
      case (spineOf o [], spineOf n []) of
        ((SigVar h [<], oargs), (SigVar h' [<], nargs)) =>
          if h == h' && length oargs == length nargs && not (null oargs)
            then let inner = concat (zipWith dhE oargs nargs) in
                 case inner of
                   [] => [h]
                   _ => inner
            else []
        _ => structE o n
   where
    spineOf : Elem -> List Elem -> (Elem, List Elem)
    spineOf (PiApp f a) acc = spineOf f (a :: acc)
    spineOf h acc = (h, acc)

  ||| Componentwise descent through equal constructors (λ bodies,
  ||| pairs, eliminators…), gathering spine-attributed drift.
  structE : Elem -> Elem -> List String
  structE (ZeroElim a) (ZeroElim b) = dhE a b
  structE (NatIntro1 a) (NatIntro1 b) = dhE a b
  structE (NatElim z s t) (NatElim z' s' t') = dhE z z' ++ dhE s s' ++ dhE t t'
  structE (PiIntro a) (PiIntro b) = dhE a b
  structE (PiApp f a) (PiApp f' a') = dhE f f' ++ dhE a a'
  structE (Let d b) (Let d' b') = dhE d d' ++ dhE b b'
  structE (SigmaIntro u v) (SigmaIntro u' v') = dhE u u' ++ dhE v v'
  structE (SigmaElim1 a) (SigmaElim1 b) = dhE a b
  structE (SigmaElim2 a) (SigmaElim2 b) = dhE a b
  structE (Inj1 a) (Inj1 b) = dhE a b
  structE (Inj2 a) (Inj2 b) = dhE a b
  structE (SumElim l r t) (SumElim l' r' t') = dhE l l' ++ dhE r r' ++ dhE t t'
  structE (PiTy a b) (PiTy a' b') = dhE a a' ++ dhE b b'
  structE (SigmaTy a b) (SigmaTy a' b') = dhE a a' ++ dhE b b'
  structE (SumTy a b) (SumTy a' b') = dhE a a' ++ dhE b b'
  structE (EqTy l r t) (EqTy l' r' t') = dhE l l' ++ dhE r r' ++ dhT t t'
  structE (QuotTy a r) (QuotTy a' r') = dhE a a' ++ dhE r r'
  structE (Class a) (Class b) = dhE a b
  structE (QuotElim f q) (QuotElim f' q') = dhE f f' ++ dhE q q'
  structE (Squash a) (Squash b) = dhT a b
  structE (Out a) (Out b) = dhE a b
  structE (Corec _ a f x) (Corec _ a' f' x') = dhE a a' ++ dhE f f' ++ dhE x x'
  structE _ _ = []

  dhT : Ty -> Ty -> List String
  dhT o n =
    if show o == show n then [] else case (o, n) of
      (Ty.PiTy a b, Ty.PiTy a' b') => dhT a a' ++ dhT b b'
      (Ty.SigmaTy a b, Ty.SigmaTy a' b') => dhT a a' ++ dhT b b'
      (Ty.SumTy a b, Ty.SumTy a' b') => dhT a a' ++ dhT b b'
      (El a, El b) => dhE a b
      (Prf a, Prf b) => dhE a b
      (Quotient a r, Quotient a' r') => dhT a a' ++ dhE r r'
      _ => []

||| The drift culprits across two Σs' entries (empty = unattributable).
driftCulprits : Sig -> Sig -> List String
driftCulprits a b = nub (go (toList a) (toList b))
 where
  go : List SigEntry -> List SigEntry -> List String
  go (SigDef _ _ body ty :: xs) (SigDef _ _ body' ty' :: ys) =
    dhE body body' ++ dhT ty ty' ++ go xs ys
  go (SigTyDef _ _ ty :: xs) (SigTyDef _ _ ty' :: ys) = dhT ty ty' ++ go xs ys
  go (_ :: xs) (_ :: ys) = go xs ys
  go _ _ = []

||| Entrywise α-comparison of two kernel Σs (core is nameless, so
||| structural equality is α-equality; Show is the comparator).
sigCompare : Sig -> Sig -> Maybe String
sigCompare a b = go (toList a) (toList b)
 where
  showEntry : SigEntry -> String
  showEntry (SigDef ctx n body ty) = "def \{n} : \{show ty} ≔ \{show body} [\{show ctx}]"
  showEntry (SigTyDef ctx n ty) = "type \{n} ≔ \{show ty} [\{show ctx}]"
  showEntry (SigDecl ctx n ty) = "decl \{n} : \{show ty} [\{show ctx}]"
  showEntry (SigTyDecl ctx n) = "tydecl \{n} [\{show ctx}]"
  showEntry (SigEq ctx l r ty) = "eq \{show l} ≐ \{show r} : \{show ty} [\{show ctx}]"
  showEntry (SigTyEq ctx x y) = "tyeq \{show x} ≐ \{show y} [\{show ctx}]"

  go : List SigEntry -> List SigEntry -> Maybe String
  go [] [] = Nothing
  go (x :: xs) (y :: ys) =
    if showEntry x == showEntry y then go xs ys
    else Just ("Σ entry differs after implicitize:\n  original: \{showEntry x}\n  new:      \{showEntry y}")
  go _ _ = Just "Σ length differs after implicitize"

defItemNames : List ModUnit -> List String
defItemNames = concatMap (\u => mapMaybe (\(_, it) => case it of
    SDef x _ _ _ => Just (qualify u.mname x)
    SDeclDef _ x _ => Just (qualify u.mname x)
    _ => Nothing) u.mitems)

||| Fold the trial records: a position survives iff it has records
||| and every one is ok.
foldTrial : List (String, List Nat) -> List (String, Nat, Nat) -> List (String, List Nat)
foldTrial cands trial =
  mapMaybe (\(q, poss) =>
      let keep = filter (\p =>
                    let recs = filter (\(q', p', _) => q' == q && p' == p) trial
                    in not (null recs) && all (\(_, _, v) => v == 0) recs) poss
      in case keep of
           [] => Nothing
           _ => Just (q, keep)) cands

export
implicitizePath : (rootPath : String) -> (outDir : String) -> IO (Either String String)
implicitizePath rootPath outDir = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left err.lmsg)
  let Right sigOrig = elabProgramSig units
    | Left err => pure (Left ("input is not accepted; implicitize only transforms accepted programs:\n" ++ err))
  let defNames = defItemNames units
  let cands0 = filter (\(q, _) => q `elem` defNames) (implicitizables sigOrig)
  -- the trial, on the override form
  let wrapUnits = map (xfUnit cands0 MWrap) units
  let Right (_, trial) = elabProgramTrial wrapUnits
    | Left err => pure (Left ("override form failed to elaborate (transformer defect):\n" ++ err))
  let trialCands = foldTrial cands0 trial
  -- the final form, iterated to the α-gate's fixpoint: an in-memory
  -- drop-transform is re-elaborated and its Σ compared; drift reverts
  -- its culprit defs and the stage re-runs (nested elisions can shift
  -- recovered SPELLINGS in ways the per-site trial cannot exhibit)
  case fixpoint units sigOrig 10 trialCands [] of
    Left err => pure (Left err)
    Right (final, culpritLog) => do
      let dropUnits = map (xfUnit final MDrop) units
      Right () <- writeUnits outDir (baseName rootPath) dropUnits
        | Left err => pure (Left err)
      Right units' <- loadProgram (outDir ++ "/" ++ baseName rootPath)
        | Left err => pure (Left ("implicitized output failed to load: " ++ err.lmsg))
      let Nothing = verifyUnits dropUnits units'
        | Just err => pure (Left err)
      let Right sigNew = elabProgramSig units'
        | Left err => pure (Left ("implicitized corpus failed to elaborate after write:\n" ++ err))
      let Nothing = sigCompare sigOrig sigNew
        | Just err => pure (Left err)
      let nDefs = length final
      let nPoss = sum (map (length . snd) final)
      let dropped = length (filter (\(q, p, v) => v == 0 && maybe False (elem p) (lookup q final))
                            trial)
      let why = \v => length (filter (\(_, _, v') => v' == v) trial)
      let trialReverts = minus (sum (map (length . snd) cands0))
                               (sum (map (length . snd) trialCands))
      pure (Right ("trial verdicts: \{show (why 0)} elidable, \{show (why 1)} trailing, " ++
                   "\{show (why 2)} stuck-at-intro, \{show (why 3)} unsolved, \{show (why 4)} spelling-drift\n" ++
                   "implicitized \{show nDefs} defs (\{show nPoss} binder positions; " ++
                   "\{show trialReverts} positions reverted by the trial" ++
                   (case culpritLog of
                      [] => ""
                      cs => ", \{show (length cs)} defs reverted by the α-gate: \{joinBy ", " cs}") ++ ")\n" ++
                   "elided \{show dropped} argument occurrences\n" ++
                   "verified: re-parse identical, elaboration accepted, kernel Σ α-identical."))
 where
  fixpoint : List ModUnit -> Sig -> Nat -> List (String, List Nat) -> List String ->
             Either String (List (String, List Nat), List String)
  fixpoint units sigOrig Z cands log =
    Left "implicitize: α-gate fixpoint did not converge in 10 rounds"
  fixpoint units sigOrig (S fuel) cands log =
    let dropUnits = map (xfUnit cands MDrop) units in
    case elabProgramSig dropUnits of
      Left err => Left ("implicitized corpus failed to elaborate:\n" ++ err)
      Right sigNew =>
        case sigCompare sigOrig sigNew of
          Nothing => Right (cands, log)
          Just msg =>
            case driftCulprits sigOrig sigNew of
              [] => Left ("implicitize: unattributable α-drift\n" ++ msg)
              culprits =>
                fixpoint units sigOrig fuel
                         (filter (\(q, _) => not (q `elem` culprits)) cands)
                         (log ++ culprits)
