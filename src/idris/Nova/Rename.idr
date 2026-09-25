module Nova.Rename

-- Σ-NAME RENAMING across a module closure — the corpus
-- OPERATORIZATION tool (docs/NovaPerfectSurface.txt, Phase 4:
-- operator overloading): `nova rename <root> <out-dir> old=new …`
-- renames each fully-qualified def `old` to the bare name `new`
-- within its own module, rewriting definition headers, every
-- reference (bare and qualified — qualified spellings and
-- using-clause citations stay qualified under the new name), import
-- opens, and license citations (`old.eq`/`.unfold`/`.rw`).
--
-- Verification: the renamed closure must elaborate ACCEPTED, and its
-- kernel Σ must be entrywise α-identical to the ORIGINAL Σ with the
-- renaming applied to it (entry names and every SigVar occurrence) —
-- renaming is meaning-preserving by construction, and the gate
-- proves it per run.

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
import Nova.Kernel
import Nova.Kernel.Syntax
import Nova.Kernel.Derivation
import Nova.Distill
import Nova.Implicitize

import System.File

import Nova.Elaboration.Beta

%default covering

||| old fully-qualified Σ name → new BARE name (module unchanged).
public export
RenameMap : Type
RenameMap = List (String, String)

modOf : String -> Maybe String
modOf q = case reverse (forget (split (== '.') q)) of
  (_ :: []) => Nothing
  (_ :: ms) => Just (joinBy "." (reverse ms))
  [] => Nothing

||| The renamed QUALIFIED form of a mapped Σ name.
newQualified : RenameMap -> String -> Maybe String
newQualified rm q = do
  nw <- lookup q rm
  pure (case modOf q of
          Just m => "\{m}.\{nw}"
          Nothing => nw)

parameters (rm : RenameMap, resolve : String -> String)
  ||| A surface reference: bare spellings stay bare (under the new
  ||| name), qualified spellings stay qualified.
  refName : String -> String
  refName n =
    let q = resolve n in
    case lookup q rm of
      Nothing => n
      Just nw => if '.' `elem` unpack n
                   then fromMaybe nw (newQualified rm q)
                   else nw

  ||| A using-clause citation: a dotted path whose last segment may be
  ||| a license suffix. A renamed citation comes out FULLY QUALIFIED —
  ||| overloaded bare citations would be ambiguous.
  citeName : String -> String
  citeName u =
    let segs = forget (split (== '.') u)
        (base, suf) = case reverse segs of
          (s :: rest) => if s == "eq" || s == "unfold" || s == "rw"
                           then (reverse rest, Just s)
                           else (segs, Nothing)
          [] => (segs, Nothing)
        baseName' = joinBy "." base
        q = case base of
              [_] => resolve baseName'
              _ => baseName'
    in case newQualified rm q of
         Nothing => u
         Just nq => case suf of
                      Nothing => nq
                      Just s => "\{nq}.\{s}"

  mutual
    rnE : SElem -> SElem
    rnE e = case e of
      SVar _ _ _ => e
      SSig r n => SSig r (refName n)
      SUnitI => e
      SZeroN => e
      SSuc t => SSuc (rnE t)
      SLam x b => SLam x (rnE b)
      SLet x d b => SLet x (rnE d) (rnE b)
      SApp f a => SApp (rnE f) (rnE a)
      SPair a b => SPair (rnE a) (rnE b)
      SProj1 t => SProj1 (rnE t)
      SProj2 t => SProj2 (rnE t)
      SZeroC => e
      SOneC => e
      SNatC => e
      SUnivC => e
      SPropC => e
      SPiC x a b => SPiC x (rnE a) (rnE b)
      SImpPiC x a b => SImpPiC x (rnE a) (rnE b)
      SSigmaC x a b => SSigmaC x (rnE a) (rnE b)
      SSumC a b => SSumC (rnE a) (rnE b)
      SQuotC a x y r => SQuotC (rnE a) x y (rnE r)
      SEqC rng l r t => SEqC rng (rnE l) (rnE r) (map rnT t)
      SZeroElim t => SZeroElim (rnE t)
      SNatElim mot z n2 ih s t =>
        SNatElim (map (\(n, m) => (n, rnT m)) mot) (rnE z) n2 ih (rnE s) (rnE t)
      SInj1 t => SInj1 (rnE t)
      SInj2 t => SInj2 (rnE t)
      SSumElim mot a l b r t =>
        SSumElim (map (\(z, m) => (z, rnT m)) mot) a (rnE l) b (rnE r) (rnE t)
      SClass t => SClass (rnE t)
      SQuotElim mot a f q =>
        SQuotElim (map (\(z, m) => (z, rnT m)) mot) a (rnE f) (rnE q)
      SSigmaElim nx ny b w => SSigmaElim nx ny (rnE b) (rnE w)
      SSumSplit na l nb r w => SSumSplit na (rnE l) nb (rnE r) (rnE w)
      SUnsquash nx b w => SUnsquash nx (rnE b) (rnE w)
      SEqElim p x w => SEqElim (rnE p) (rnE x) (rnE w)
      SNuC f => SNuC (rnP f)
      SOut t => SOut (rnE t)
      SCorec x a f u => SCorec x (rnE a) (rnE f) (rnE u)
      SCoind nx ny r pw mx my mh w => SCoind nx ny (rnE r) (rnE pw) mx my mh (rnE w)
      SSquash t => SSquash (rnT t)
      SStar _ => e
      SStarWit w => SStarWit (rnE w)
      SStarUsing r ns => SStarUsing r (map citeName ns)
      SSquashElim sc x b => SSquashElim (rnE sc) x (rnE b)
      SChain h links => SChain (rnE h) (map (\(j, m) => (rnE j, rnE m)) links)
      SAnn t ty => SAnn (rnE t) (rnT ty)
      SImpArg t => SImpArg (rnE t)
      SNoIns t => SNoIns (rnE t)
      SBlank _ => e
      SHole _ _ => e
      -- spans stop here: the renamed tree goes straight to the printer
      SPos _ t => rnE t

    rnT : STy -> STy
    rnT = rnE

    rnP : SPoly -> SPoly
    rnP p = case p of
      SPHole => p
      SPConst a => SPConst (rnE a)
      SPProd f g => SPProd (rnP f) (rnP g)
      SPSum f g => SPSum (rnP f) (rnP g)
      SPSigma x a f => SPSigma x (rnE a) (rnP f)
      SPPi x a f => SPPi x (rnE a) (rnP f)

  rnQDecl : SQDecl -> SQDecl
  rnQDecl (MkSQDecl n r bs res) =
    MkSQDecl n r (map (\(x, d) => (x, case d of
                                     Left t => Left (rnT t)
                                     Right qt => Right (rnQTm qt))) bs)
      (case res of
         SQResU => SQResU
         SQResEl t => SQResEl (rnQTm t)
         SQResEq l r u => SQResEq (rnQTm l) (rnQTm r) (rnQTm u))
   where
    rnQTm : SQTm -> SQTm
    rnQTm (SQVar n i) = SQVar n i
    rnQTm (SQAppE f e) = SQAppE (rnQTm f) (rnE e)
    rnQTm (SQAppI f a) = SQAppI (rnQTm f) (rnQTm a)

  defName : (String -> String) -> String -> String
  defName ownQ x = fromMaybe x (lookup (ownQ x) rm)

  rnItem : (ownQ : String -> String) -> SItem -> SItem
  rnItem ownQ (SDef r x ty body mu) =
    SDef r (defName ownQ x) (rnT ty) (rnE body) (map (map citeName) mu)
  rnItem ownQ (SDeclDef r x ty) = SDeclDef r (defName ownQ x) (rnT ty)
  rnItem ownQ (SData params ds) =
    SData (map (\(x, t) => (x, rnT t)) params) (map rnQDecl ds)
  rnItem ownQ (SClausalDef r x ty mu eta er wit cls) =
    SClausalDef r (defName ownQ x) (rnT ty) mu eta er (map rnE wit)
      (map ({ crhs $= rnE }) cls)


rnImport : RenameMap -> SImport -> SImport
rnImport rm (MkSImport m os r) =
  MkSImport m (map (\o => fromMaybe o (lookup "\{m}.\{o}" rm)) os) r

rnUnit : (fixesOf : String -> FixTable) -> RenameMap -> ModUnit -> ModUnit
rnUnit fixesOf rm u =
  let resolve = unitResolver u
      ownQ = qualify u.mname
      body' = map (map (\(r, it) => (r, rnItem rm resolve ownQ it))) u.mbody
      imports' = map (rnImport rm) u.mimports
      -- a rename can turn an opened name into an OPERATOR: its
      -- defining module's fixity must reach this unit's print table
      -- (the loader recomputes it from the renamed opens on reload)
      opened = concatMap (\i => mapMaybe (\o => lookup o (fixesOf i.mname)
                                                 >>= \f => Just (o, f)) i.opens) imports'
      mfix' = u.mfix ++ filter (\(op, _) => isNothing (lookup op u.mfix)) opened
  in { mbody := body'
     , mimports := imports'
     , mfix := mfix'
     , mitems := mapMaybe (\e => case e of
                             Right ri => Just ri
                             Left _ => Nothing) body' } u

renameSig : (String -> String) -> Sig -> Sig
renameSig f = map (renameEntry f)

-- ===== The driver =====

export
renamePath : (rootPath : String) -> (outDir : String) -> RenameMap -> IO (Either String String)
renamePath rootPath outDir rm = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left (showLoadErr err))
  let Right sigOrig = elabProgramSig units
    | Left err => pure (Left ("input is not accepted; rename only transforms accepted programs:\n" ++ err))
  let ownFixes = map (\u => (u.mname, map snd (lefts u.mbody))) units
  let fixesOf = \m => fromMaybe [] (lookup m ownFixes)
  let renamed = map (rnUnit fixesOf rm) units
  Right () <- writeUnits outDir (baseName rootPath) renamed
    | Left err => pure (Left err)
  Right units' <- loadProgram (outDir ++ "/" ++ baseName rootPath)
    | Left err => pure (Left ("renamed output failed to load: " ++ showLoadErr err))
  let Nothing = verifyUnits renamed units'
    | Just err => pure (Left err)
  () <- clearSigEntryIx
  let Right sigNew = elabProgramSig units'
    | Left err => pure (Left ("renamed corpus failed to elaborate:\n" ++ err))
  let f = \n => fromMaybe n (newQualified rm n)
  let Nothing = sigCompare (renameSig f sigOrig) sigNew
    | Just err => pure (Left err)
  pure (Right ("renamed \{show (length rm)} definitions across \{show (length units)} modules\n" ++
               "verified: re-parse identical, elaboration accepted, kernel Σ α-identical modulo the renaming."))
