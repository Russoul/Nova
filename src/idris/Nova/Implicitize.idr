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

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Loader
import Nova.Kernel.Syntax
import Nova.Recovery
import Nova.Distill

import System.File

import Nova.Elaboration.Beta

%default covering

-- ===== Per-module name resolution =====

export
qualify : (mname : String) -> String -> String
qualify "" x = x
qualify m x = "\{m}.\{x}"

||| surface name → Σ name: the module's own items shadow its opened
||| imports; a name matching neither is already a Σ path.
export
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
||| The telescope ↔ surface mapping at a site of a PARTIALLY-IMPLICIT
||| def: elided implicit positions consume no item and {t} overrides
||| pair with implicit positions, so the i-th NON-OVERRIDE item
||| stands at the def's i-th EXPLICIT telescope position. Given the
||| def's explicit positions (sorted) and a site's items, each entry
||| is (telescope position, item index in the full list, the item).
explicitSlots : List Nat -> List SElem -> List (Nat, Nat, SElem)
explicitSlots eps items = go eps (withIndex 0 items)
 where
  withIndex : Nat -> List SElem -> List (Nat, SElem)
  withIndex i [] = []
  withIndex i (x :: xs) = (i, x) :: withIndex (S i) xs
  go : List Nat -> List (Nat, SElem) -> List (Nat, Nat, SElem)
  go [] _ = []
  go _ [] = []
  go (p :: ps) ((j, SImpArg t) :: rest) = go (p :: ps) rest
  go (p :: ps) ((j, it) :: rest) = (p, j, it) :: go ps rest

public export
data IMode : Type where
  MWrap : IMode
  MDrop : IMode
  ||| the TARGETED-migration form (docs/NovaPerfectSurface.txt): at a
  ||| candidate position, a site in the drop set loses its argument
  ||| (recovery is per-site verified), any other site KEEPS it as a
  ||| {t} override — the graceful middle the intersection policy
  ||| lacks. Carries the def's PRE-MIGRATION explicit positions (the
  ||| telescope ↔ surface mapping at partially-implicit sites) and
  ||| the (head range, telescope position) drop keys, per module.
  MDropSited : List Nat -> List (Range, Nat) -> IMode

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
      SSig mrng x =>
        case lookup (resolve x) cands of
          Just poss =>
            let idxd = zip [0 .. minus (length args) 1] args
            in case mode of
                 MWrap => foldl SApp hd (mapMaybe (mkWrap poss) idxd)
                 -- a fully-elided site is legal: checking-position
                 -- insertion covers it (the trial verdicts guarantee
                 -- every surviving position was insertable)
                 MDrop => foldl SApp hd (mapMaybe (mkDrop poss) idxd)
                 MDropSited eps drops => foldl SApp hd (mapMaybe (mkSited poss eps drops mrng (explicitSlots eps args)) idxd)
          Nothing => foldl SApp hd args
      _ => foldl SApp hd args
   where
    -- a BLANK at a candidate position is already per-site elided —
    -- in every mode it simply disappears (an implicit position
    -- inserts the same hole the blank stood for)
    mkWrap : List Nat -> (Nat, SElem) -> Maybe SElem
    mkWrap poss (i, a) =
      if i `elem` poss
        then case a of
               SBlank _ => Nothing
               _ => Just (SImpArg a)
        else Just a

    mkDrop : List Nat -> (Nat, SElem) -> Maybe SElem
    mkDrop poss (i, a) = if i `elem` poss then Nothing else Just a

    mkSited : List Nat -> List Nat -> List (Range, Nat) -> Maybe Range ->
              List (Nat, Nat, SElem) -> (Nat, SElem) -> Maybe SElem
    mkSited poss eps drops mrng slots (j, a) =
      case head' (mapMaybe (\(p2, j2, _) => if j2 == j then Just p2 else Nothing) slots) of
        -- an override or a leftover past the telescope: keep as is
        Nothing => Just a
        Just p2 =>
          if not (p2 `elem` poss) then Just a
          else case a of
            SBlank _ => Nothing
            _ => case mrng of
              Just r => if any (\(r2, pp) => pp == p2 && show r2 == show r) drops
                          then Nothing else Just (SImpArg a)
              Nothing => Just (SImpArg a)

  mutual
    xfE : SElem -> SElem
    xfE e = case e of
      SApp _ _ =>
        let (hd, args) = spine e []
            hd' = case hd of
                    SSig _ _ => hd   -- spine heads are never marker-wrapped
                    _ => xfE hd
        in xfSpine hd' (map xfE args)
      SVar _ _ _ => e
      -- a standalone reference of an implicitized def is FUNCTION
      -- PASSING (the original corpus is fully explicit, so a bare
      -- reference always denotes the function): mark it {} so
      -- checking-position insertion stays off and the erasure is
      -- unchanged
      SSig _ x =>
        case lookup (resolve x) cands of
          Just poss => if 0 `elem` poss then SNoIns e else e
          Nothing => e
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
      SEqC rng l r t => SEqC rng (xfE l) (xfE r) (map xfT t)
      SZeroElim t => SZeroElim (xfE t)
      SNatElim mot z n2 ih s t => SNatElim (map (\(n, m) => (n, xfT m)) mot) (xfE z) n2 ih (xfE s) (xfE t)
      SInj1 t => SInj1 (xfE t)
      SInj2 t => SInj2 (xfE t)
      SSumElim mot a l b r t => SSumElim (map (\(z, m) => (z, xfT m)) mot) a (xfE l) b (xfE r) (xfE t)
      SClass t => SClass (xfE t)
      SQuotElim mot a f qq => SQuotElim (map (\(z, m) => (z, xfT m)) mot) a (xfE f) (xfE qq)
      SNuC f => SNuC (xfP f)
      SOut t => SOut (xfE t)
      SCorec x a f u => SCorec x (xfE a) (xfE f) (xfE u)
      SCoind nx ny r pw mx my mh w => SCoind nx ny (xfE r) (xfE pw) mx my mh (xfE w)
      SSquash t => SSquash (xfT t)
      SStar _ => e
      SStarWit w => SStarWit (xfE w)
      SStarUsing _ _ => e
      SSquashElim s x b => SSquashElim (xfE s) x (xfE b)
      SChain h links => SChain (xfE h) (map (\(j, m) => (xfE j, xfE m)) links)
      SAnn t ty => SAnn (xfE t) (xfT ty)
      SImpArg t => SImpArg (xfE t)
      SNoIns t => SNoIns (xfE t)
      SBlank _ => e
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
      STyEq rng l r t => STyEq rng (xfE l) (xfE r) (map xfT t)
      STyEl t => STyEl (xfE t)
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
export
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
      (PiTy a b, PiTy a' b') => dhT a a' ++ dhT b b'
      (SigmaTy a b, SigmaTy a' b') => dhT a a' ++ dhT b b'
      (SumTy a b, SumTy a' b') => dhT a a' ++ dhT b b'
      (QuotTy a r, QuotTy a' r') => dhT a a' ++ dhE r r'
      -- code types (El retired): attribute drift as elements
      _ => dhE o n

||| The drift culprits across two Σs' entries (empty = unattributable).
driftCulprits : Sig -> Sig -> List String
driftCulprits a b = nub (go (toList a) (toList b))
 where
  go : List SigEntry -> List SigEntry -> List String
  go (SigDef _ _ body ty :: xs) (SigDef _ _ body' ty' :: ys) =
    dhE body body' ++ dhT ty ty' ++ go xs ys
  go (_ :: xs) (_ :: ys) = go xs ys
  go _ _ = []

defItemNames : List ModUnit -> List String
defItemNames = concatMap (\u => mapMaybe (\(_, it) => case it of
    SDef x _ _ _ => Just (qualify u.mname x)
    SDeclDef _ x _ => Just (qualify u.mname x)
    _ => Nothing) u.mitems)

||| Fold the trial records: a position survives iff it has records
||| and every one is ok.
foldTrial : List (String, List Nat) -> List (String, Nat, Nat, Maybe (String, Range)) -> List (String, List Nat)
foldTrial cands trial =
  mapMaybe (\(q, poss) =>
      let keep = filter (\p =>
                    let recs = filter (\(q', p', _, _) => q' == q && p' == p) trial
                    in not (null recs) && all (\(_, _, v, _) => v == 0) recs) poss
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
  () <- clearSigEntryIx
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
      () <- clearSigEntryIx
      let Right sigNew = elabProgramSig units'
        | Left err => pure (Left ("implicitized corpus failed to elaborate after write:\n" ++ err))
      let Nothing = sigCompare sigOrig sigNew
        | Just err => pure (Left err)
      let nDefs = length final
      let nPoss = sum (map (length . snd) final)
      let dropped = length (filter (\(q, p, v, _) => v == 0 && maybe False (elem p) (lookup q final))
                            trial)
      let why = \v => length (filter (\(_, _, v', _) => v' == v) trial)
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

-- ===== The TARGETED pipeline: census, then migrate one def =====
--
-- The cong migration, as a tool (docs/NovaPerfectSurface.txt): pick a
-- def and a set of its explicit binder positions; the CENSUS reports,
-- per position, how many sites recover the argument (the Phase-3c
-- override trial, site-keyed) and how many would need a {t} override;
-- MIGRATE then makes the positions implicit, drops the argument at
-- every site whose verdict is positive (or that already wrote a
-- blank), keeps a {t} override everywhere else, and iterates the
-- Σ-α-gate to its fixpoint, reverting drops inside drifted defs.

||| every spine headed by `q`, anywhere in a unit: (head range, args)
sitesOfUnit : (resolve : String -> String) -> (q : String) -> ModUnit -> List (Maybe Range, List SElem)
sitesOfUnit resolve q u = concatMap (\(_, it) => goItem it) u.mitems
 where
  mutual
    goE : SElem -> List (Maybe Range, List SElem)
    goE e = case e of
      SApp _ _ =>
        let (hd, args) = spine e []
            own = case hd of
                    SSig mrng x => if resolve x == q then [(mrng, args)] else []
                    _ => goE hd
        in own ++ concatMap goE args
      SVar _ _ _ => []
      SSig _ _ => []
      SUnitI => []
      SZeroN => []
      SSuc t => goE t
      SLam _ b => goE b
      SLet _ d b => goE d ++ goE b
      SPair a b => goE a ++ goE b
      SProj1 t => goE t
      SProj2 t => goE t
      SZeroC => []
      SOneC => []
      SNatC => []
      SPiC _ a b => goE a ++ goE b
      SSigmaC _ a b => goE a ++ goE b
      SSumC a b => goE a ++ goE b
      SQuotC a _ _ r => goE a ++ goE r
      SEqC _ l r t => goE l ++ goE r ++ concatMap goT (toList t)
      SZeroElim t => goE t
      SNatElim mot z _ _ st t => concatMap (goT . snd) (toList mot) ++ goE z ++ goE st ++ goE t
      SInj1 t => goE t
      SInj2 t => goE t
      SSumElim mot _ l _ r t => concatMap (goT . snd) (toList mot) ++ goE l ++ goE r ++ goE t
      SClass t => goE t
      SQuotElim mot _ f qq => concatMap (goT . snd) (toList mot) ++ goE f ++ goE qq
      SNuC f => goP f
      SOut t => goE t
      SCorec _ a f uu => goE a ++ goE f ++ goE uu
      SCoind _ _ r pw _ _ _ w => goE r ++ goE pw ++ goE w
      SSquash t => goT t
      SStar _ => []
      SStarWit w => goE w
      SStarUsing _ _ => []
      SSquashElim sc _ b => goE sc ++ goE b
      SChain h links => goE h ++ concatMap (\(j, m) => goE j ++ goE m) links
      SAnn t ty => goE t ++ goT ty
      SImpArg t => goE t
      SNoIns t => goE t
      SBlank _ => []
     where
      spine : SElem -> List SElem -> (SElem, List SElem)
      spine (SApp f a) acc = spine f (a :: acc)
      spine h acc = (h, acc)

    goT : STy -> List (Maybe Range, List SElem)
    goT ty = case ty of
      STyPi _ a b => goT a ++ goT b
      STyImpPi _ a b => goT a ++ goT b
      STySigma _ a b => goT a ++ goT b
      STySum a b => goT a ++ goT b
      STyQuot a _ _ r => goT a ++ goE r
      STyEq _ l r t => goE l ++ goE r ++ concatMap goT (toList t)
      STyEl t => goE t
      STyNu f => goP f
      _ => []

    goP : SPoly -> List (Maybe Range, List SElem)
    goP pl = case pl of
      SPHole => []
      SPConst a => goE a
      SPProd f g => goP f ++ goP g
      SPSum f g => goP f ++ goP g
      SPSigma _ a f => goE a ++ goP f
      SPPi _ a f => goE a ++ goP f

  goItem : SItem -> List (Maybe Range, List SElem)
  goItem (SDef _ ty body _) = goT ty ++ goE body
  goItem (SDeclDef _ _ ty) = goT ty
  goItem (STypeDef _ ty) = goT ty
  goItem (SData params ds) = concatMap (goT . snd) params
  goItem (SClausalDef _ _ ty _ wit cls) =
    goT ty ++ concatMap goE wit ++ concatMap (\c => goE c.crhs) cls

||| find a def by bare or qualified name: (qualified, surface type)
findDef : List ModUnit -> String -> Either String (String, STy)
findDef units name =
  case concatMap (\u => mapMaybe (\(_, it) => case it of
         SDef x ty _ _ => hit u x ty
         SDeclDef _ x ty => hit u x ty
         _ => Nothing) u.mitems) units of
    [one] => Right one
    [] => Left "unknown def '\{name}'"
    many => Left "'\{name}' is ambiguous: \{joinBy ", " (map fst many)} — qualify it"
 where
  hit : ModUnit -> String -> STy -> Maybe (String, STy)
  hit u x ty =
    let q = qualify u.mname x in
    if q == name || x == name then Just (q, ty) else Nothing

||| the def's leading Π binders: (position, implicit?)
leadingBinders : STy -> List (Nat, Bool)
leadingBinders = go 0
 where
  go : Nat -> STy -> List (Nat, Bool)
  go i (STyPi _ _ b) = (i, False) :: go (S i) b
  go i (STyImpPi _ _ b) = (i, True) :: go (S i) b
  go i _ = []

||| run the override-form trial for the given candidates; returns the
||| trial records (site-keyed)
runTrial : List ModUnit -> List (String, List Nat) ->
           IO (Either String (List (String, Nat, Nat, Maybe (String, Range))))
runTrial units cands = do
  let wrapUnits = map (xfUnit cands MWrap) units
  () <- clearSigEntryIx
  case elabProgramTrial wrapUnits of
    Left err => pure (Left ("override form failed to elaborate (transformer defect):\n" ++ err))
    Right (_, trial) => pure (Right trial)

||| is the site ITEM verdicted blankable? (svBlank keys are item
||| indices among the consumed items, in written order)
verdicted : List (String, Range, Nat) -> String -> Maybe Range -> Nat -> Bool
verdicted bl mn mrng j = case mrng of
  Just r => any (\(mn2, r2, j2) => mn2 == mn && j2 == j && show r2 == show r) bl
  Nothing => False

||| The CENSUS, on the SUGAR PASS alone (no transformation): per named
||| def and explicit leading position — applied sites, already-blank,
||| blankable (the emission trial's verdicts), and the rest, which a
||| migration would keep as {…} overrides.
export
censusPath : (rootPath : String) -> List String -> IO (Either String String)
censusPath rootPath names = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left err.lmsg)
  let Right (_, _, blanks, _) = elabProgramSugar units
    | Left err => pure (Left ("input is not accepted; census needs an accepted program:\n" ++ err))
  case the (Either String (List (String, STy))) (traverse (findDef units) names) of
    Left err => pure (Left err)
    Right defs => pure (Right (joinBy "\n" (concatMap (report units blanks) defs)))
 where
  report : List ModUnit -> List (String, Range, Nat) -> (String, STy) -> List String
  report units bl (q, ty) =
    let poss = map fst (filter (not . snd) (leadingBinders ty))
        sites = concatMap (\u => map (\(mr, args) => (u.mname, mr, args)) (sitesOfUnit (unitResolver u) q u)) units in
    ("\{q}: \{show (length sites)} sites" ::
     map (\p =>
       let slotted = mapMaybe (\(mn, mr, args) =>
                       map (\(_, j, it) => (mn, mr, j, it))
                           (find (\(p2, _, _) => p2 == p) (explicitSlots poss args))) sites
           blanksN = filter (\(_, _, _, it) => case it of
                              SBlank _ => True
                              _ => False) slotted
           elid = filter (\(mn, mr, j, it) =>
                    (case it of
                       SBlank _ => False
                       _ => True) && verdicted bl mn mr j) slotted
           needOv = minus (length slotted) (length blanksN + length elid)
       in "  #\{show p}: \{show (length slotted)} applied, " ++
          "\{show (length blanksN)} already blank, \{show (length elid)} blankable, " ++
          "\{show needOv} need {…}")
       poss)

||| TARGETED migration: make the given explicit positions of one def
||| implicit; per-site, drop the argument (verdict-positive or already
||| blank) or keep it as a {t} override; α-gate to a fixpoint.
export
migrateDefPath : (rootPath : String) -> (outDir : String) ->
                 (name : String) -> List Nat -> IO (Either String String)
migrateDefPath rootPath outDir name poss = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left err.lmsg)
  let Right sigOrig = elabProgramSig units
    | Left err => pure (Left ("input is not accepted; migrate needs an accepted program:\n" ++ err))
  case findDef units name of
    Left err => pure (Left err)
    Right (q, sty) => do
      let lead = leadingBinders sty
      let bad = filter (\p => lookup p lead /= Just False) poss
      let True = null bad
        | False => pure (Left "positions \{show bad} of '\{q}' are not explicit leading Π binders")
      let cands = [(q, poss)]
      -- the SUGAR PASS supplies per-site verdicts (no wrap needed):
      -- an argument is droppable when it is already a blank or the
      -- emission trial proves it blankable
      let Right (_, _, blanks, risks) = elabProgramSugar units
        | Left err => pure (Left ("sugar pass failed (input was accepted?):\n" ++ err))
      let sites = concatMap (\u => map (\(mr, args) => (u.mname, mr, args)) (sitesOfUnit (unitResolver u) q u)) units
      let eps = map fst (filter (not . snd) lead)
      let imps0 = map fst (filter snd lead)
      -- per-site plan with PREFIX CLOSURE: {t} overrides fill a run
      -- of consecutive implicit positions in order, so an override
      -- can stand at position p only if every position before it IN
      -- THE SAME POST-MIGRATION RUN also writes an override —
      -- droppable written arguments are forced back to overrides
      -- where needed; a blank OR an already-implicit position (whose
      -- argument is elided — nothing to wrap) before an override is
      -- INEXPRESSIBLE
      -- a blank whose implicit-mode solve would differ (join-tier
      -- capture) cannot convert: collect those as blockers up front
      let risky = filter (\(mn, r, pp) => pp `elem` poss)
                    (filter (\(mn, r, _) => any (\(mn2, mr2, args) =>
                        mn == mn2 && maybe False (\r2 => show r2 == show r) mr2) sites) risks)
      let True = null risky
        | False => pure (Left ("migration blocked: these blanks solve DIFFERENTLY as implicits (join-tier capture) — spell them first:\n  " ++
                               joinBy "\n  " (map (\(mn, r, pp) => "\{mn} L\{show r.start.line} position \{show pp}") risky)))
      let plans = map (planSite blanks poss eps imps0) sites
      let blocked = mapMaybe (\pl => case pl of
                                        Left site => Just site
                                        Right _ => Nothing) plans
      let True = null blocked
        | False => pure (Left ("migration blocked: a blank precedes a {…} override inside one implicit run at:\n  " ++
                               joinBy "\n  " blocked ++
                               "\nspell those blanks (or choose different positions) first"))
      let drop0 = concat (mapMaybe (\pl => case pl of
                                              Right ks => Just ks
                                              Left _ => Nothing) plans)
      let nSitesTotal = length sites
      () <- clearSigEntryIx
      let Right (dropSet, reverts) = fixLoop units sigOrig cands eps 10 drop0 []
        | Left err => pure (Left err)
      let finalUnits = map (\u => xfUnit cands (MDropSited eps (unitKeys u.mname dropSet)) u) units
      Right () <- writeUnits outDir (baseName rootPath) finalUnits
        | Left err => pure (Left err)
      Right units2 <- loadProgram (outDir ++ "/" ++ baseName rootPath)
        | Left err => pure (Left ("migrated output failed to load: " ++ err.lmsg))
      let Nothing = verifyUnits finalUnits units2
        | Just err => pure (Left err)
      () <- clearSigEntryIx
      let Right sigNew = elabProgramSig units2
        | Left err => pure (Left ("migrated corpus failed to elaborate after write:\n" ++ err))
      let Nothing = sigCompare sigOrig sigNew
        | Just err => pure (Left err)
      pure (Right ("migrated '\{q}': positions \{show poss} now implicit (\{show nSitesTotal} sites)\n" ++
                   "\{show (length dropSet)} written arguments dropped (per-site verified), " ++
                   "\{show (minus (length drop0) (length dropSet))} α-gate-reverted to overrides" ++
                   (case reverts of
                      [] => ""
                      cs => " (in \{joinBy ", " (nub cs)})") ++ "\n" ++
                   "verified: re-parse identical, elaboration accepted, kernel Σ α-identical."))
 where
  ||| the POST-MIGRATION implicit positions (chosen ∪ pre-existing)
  ||| grouped into runs of CONSECUTIVE telescope positions (a
  ||| position staying explicit in between re-anchors override
  ||| pairing)
  runsOf : List Nat -> List (List Nat)
  runsOf [] = []
  runsOf (p :: ps) = go [p] ps
   where
    go : List Nat -> List Nat -> List (List Nat)
    go acc [] = [reverse acc]
    go acc@(prev :: _) (x :: xs) =
      if x == S prev then go (x :: acc) xs else reverse acc :: go [x] xs
    go [] _ = []

  ||| a run's plan over POST-MIGRATION implicit positions. Per
  ||| position: pre-existing implicit (elided, unoverridable), chosen
  ||| with a blank item (droppable, unoverridable), chosen written
  ||| (droppable when verdicted, overridable). An override forces
  ||| every earlier run position to be written — an unoverridable one
  ||| there blocks the site.
  planRun : List (String, Range, Nat) -> String -> Maybe Range ->
            List (Nat, Nat, SElem) -> List Nat -> List Nat ->
            List Nat -> Either String (List Nat)
  planRun bl mn mrng slots poss imps0 run =
    let itemOf = \p => head' (mapMaybe (\(p2, j, it) => if p2 == p then Just (j, it) else Nothing) slots)
        isBlankP = \p => case itemOf p of
                           Just (_, SBlank _) => True
                           _ => False
        applied = filter (\p => (p `elem` imps0) || isJust (itemOf p)) run
        chosenIn = filter (\p => p `elem` poss) applied
        droppable = \p => isBlankP p ||
                          (case itemOf p of
                             Just (j, _) => verdicted bl mn mrng j
                             Nothing => False)
        ovs = filter (\p => not (droppable p)) chosenIn
    in case ovs of
         [] => Right (filter (\p => not (isBlankP p)) chosenIn)
         _ =>
           let m = foldl max 0 ovs
               before = filter (\p => p <= m) applied
               blockers = filter (\p => isBlankP p || ((p `elem` imps0) && p < m)) before
           in case blockers of
                [] => Right (filter (\p => p > m && not (isBlankP p)) chosenIn)
                (b :: _) => Left "position \{show b} (elided) precedes an override at position \{show m}"

  ||| one site's plan: Left = blocked, Right = this site's DROP keys
  ||| (telescope positions; written args only — blanks drop in the
  ||| transform unconditionally)
  planSite : List (String, Range, Nat) -> List Nat -> List Nat -> List Nat ->
             (String, Maybe Range, List SElem) -> Either String (List (String, Range, Nat))
  planSite bl poss eps imps0 (mn, mrng, args) =
    let slots = explicitSlots eps args
        runs = runsOf (sort (nub (poss ++ imps0)))
        perRun = map (planRun bl mn mrng slots poss imps0) runs
    in case (the (Maybe String) (head' (mapMaybe blockOf perRun)), mrng) of
         (Just why, Just r) => Left "\{mn} L\{show r.start.line}: \{why}"
         (Just why, Nothing) => Left "\{mn}: \{why}"
         (Nothing, Just r) => Right (map (\p => (mn, r, p)) (concatMap keysOf perRun))
         (Nothing, Nothing) => Right []
   where
    blockOf : Either String (List Nat) -> Maybe String
    blockOf (Left why) = Just why
    blockOf (Right _) = Nothing

    keysOf : Either String (List Nat) -> List Nat
    keysOf (Right ds) = ds
    keysOf (Left _) = []

  unitKeys : String -> List (String, Range, Nat) -> List (Range, Nat)
  unitKeys mn ds = mapMaybe (\(mn', r, p) => if mn' == mn then Just (r, p) else Nothing) ds

  ||| item spans per module, for α-gate culprit reversion
  spanOf : List ModUnit -> String -> Maybe (String, Int, Int)
  spanOf units cq = head' (concatMap (\u => mapMaybe (\(mr, it) =>
      if qualify u.mname (itemName it) == cq
        then map (\r => (u.mname, r.start.line, r.end.line)) mr
        else Nothing) u.mitems) units)

  ||| the drifted Σ entry's name, from sigCompare's message: the line
  ||| "  original: def NAME : …" (or type/decl/tydecl)
  entryNameOfMsg : String -> Maybe String
  entryNameOfMsg msg =
    case filter (isInfixOf "original: ") (lines msg) of
      (l :: _) => case words (snd (break (== ':') l)) of
                    (_ :: _ :: nm :: _) => Just nm
                    _ => Nothing
      _ => Nothing

  ||| the failing def's bare name, when the error carries one — the
  ||| revert unit for elaboration failures (a drop set is verified
  ||| against the ACTUAL mixed form: the per-override trial replays
  ||| the all-holes hypothetical, and a mix of drops and kept
  ||| overrides is a different joint solve)
  defNameOfErr : String -> Maybe String
  defNameOfErr err =
    if isPrefixOf "def " err
      then case break (== ':') (pack (drop 4 (unpack err))) of
             (nm, rest) => if rest == "" then Nothing else Just nm
      else Nothing

  spansOfBare : List ModUnit -> String -> List (String, Int, Int)
  spansOfBare units bare = concatMap (\u => mapMaybe (\(mr, it) =>
      if itemName it == bare
        then map (\r => (u.mname, r.start.line, r.end.line)) mr
        else Nothing) u.mitems) units

  revertIn : List ModUnit -> List String -> List (String, Range, Nat) -> List (String, Range, Nat)
  revertIn units bares ds =
    let spans = concatMap (spansOfBare units) bares in
    filter (\(mn, r, _) =>
      not (any (\(mn2, sl, el) => mn == mn2 && r.start.line >= sl && r.start.line <= el) spans)) ds

  fixLoop : List ModUnit -> Sig -> List (String, List Nat) -> (eps : List Nat) -> Nat ->
            List (String, Range, Nat) -> List String ->
            Either String (List (String, Range, Nat), List String)
  fixLoop units sigOrig cands eps Z ds log = Left "migrate: α-gate fixpoint did not converge in 10 rounds"
  fixLoop units sigOrig cands eps (S fuel) ds log =
    let dropUnits = map (\u => xfUnit cands (MDropSited eps (unitKeys u.mname ds)) u) units in
    case elabProgramSig dropUnits of
      Left err =>
        case defNameOfErr err of
          Nothing => Left ("migrated corpus failed to elaborate:\n" ++ err)
          Just bare =>
            let ds2 = revertIn units [bare] ds in
            if length ds2 == length ds
              then Left ("migrated corpus failed to elaborate (no revertible drops):\n" ++ err)
              else fixLoop units sigOrig cands eps fuel ds2 (log ++ [bare])
      Right sigNew =>
        case sigCompare sigOrig sigNew of
          Nothing => Right (ds, log)
          Just msg =>
            -- the DRIFTED ENTRY (from the gate's own message) is the
            -- def CONTAINING the drifted site — driftCulprits names
            -- the head of the drifted spine instead, which for a
            -- targeted migration is just the migrated def itself
            case entryNameOfMsg msg of
              Nothing => Left ("migrate: unattributable α-drift\n" ++ msg)
              Just qn =>
                let bare = List1.last (split (== '.') qn)
                    ds2 = revertIn units [bare] ds
                in if length ds2 == length ds
                     then Left ("migrate: α-drift with no revertible drops in '\{qn}'\n" ++ msg)
                     else fixLoop units sigOrig cands eps fuel ds2 (log ++ [qn])
