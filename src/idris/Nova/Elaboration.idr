module Nova.Elaboration

-- The bidirectional elaborator of docs/NovaElaboration.txt (hole-free).
--
-- Independent of the derivation machinery (no Truth, no TypingRule): it
-- shares only the core syntax, substitution, and beta-normalization.
-- Every rule mirrors a docs/NovaFoundation.txt rule; the conversion
-- judgements never fail — an equation that cannot be discharged
-- algorithmically is ASSUMED and reported as an obligation. A file is
-- accepted exactly when a run's final signature is DEFINITIONAL: the
-- run's assumptions live in Σ itself as constraint entries (sig-eq/
-- at A = 𝕍), so "zero obligations" and "no non-definition entries"
-- are the same check.
--
-- Discharge machinery ("E" of the spec), in the order tried:
--   * beta-normalization (beta, El-decoding, signature unfolding);
--   * fuel-bounded REWRITING with the equation store: accepted Eq-typed
--     lemmas from Σ (their leading Πs peeled into pattern parameters)
--     and Eq-typed hypotheses of the local context (likewise peeled),
--     each oriented left-to-right as stated, applied at any subterm —
--     this gives single-lemma discharge, transitivity chains, and
--     congruence positioning in one mechanism;
--   * type-directed comparison: el-pi-eta/el-sigma-eta,
--     el-zero-prop/el-one-prop, and quotient
--     class-equations (a 𝟙-shaped relation is inhabited outright, an
--     Eq-shaped relation reduces the witness to its equation);
--   * congruence decomposition in the sufficient direction, with the
--     composite retained for the report;
--   * assumption (dedup by normalized statement, symmetric).
--
-- Soundness of rewriting: a candidate's instance l[σ] ≐ r[σ] is
-- Foundation-derivable by (el-sub-cong-fix) from the reflected lemma or
-- hypothesis; σ's well-typedness follows by inversion from the matched
-- instance occurring inside an elaborated (well-typed) term. Replacing
-- a subterm by a judgementally equal one is congruence.

import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.String

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Recovery
import Nova.Elaboration.Beta
import Nova.Kernel.QIIT
import Nova.Kernel.Parser
import Nova.Kernel

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range
import Nova.Elaboration.Named
import Nova.Diagnostic
import Nova.Elaboration.Surface
import Nova.Elaboration.Clauses
import Nova.Elaboration.Parser
import Nova.Profile

%default covering

-- ===== State =====

||| A rewrite candidate: an equation whose context splits into a fixed
||| base (rigid — the ambient Γ for hypothesis candidates, ε for Σ-level
||| lemmas) and `params` innermost parametric entries (matchable).
||| lhs/rhs are stored beta-normalized, in base ▷ p_{k-1} ▷ ... ▷ p₀.
||| paramTys lists the parametric entries' types OUTERMOST FIRST (i.e.
||| index (k-1) first), each in its own prefix of the pattern context —
||| needed for conditional matching (an unbound ≡-typed parameter is a
||| side condition to discharge, not a term to find).
||| A step over the candidate's parametric context: instantiated with
||| the match bindings at emission time (proofs live over the pattern
||| context; substElem with the instantiating Sub moves them to the
||| site). Records the lemma-normalization of a candidate's sides so
||| the kernel — which derives licensed equations from RAW types by
||| beta only — can bridge to the normalized pattern.
record PStep where
  constructor MkPStep
  ppath : List Nat
  pprf : Elem          -- over the candidate's parametric context
  psels : List Sel
  pflip : Bool

record Cand where
  constructor MkCand
  candName : String
  params : Nat
  paramTys : List Ty
  lhs : Elem
  rhs : Elem
  ||| build (proof element, selectors) from complete match bindings;
  ||| the proof lives in the query context Γ. The Nat is the WEAKENING
  ||| DEPTH: how many binders the query context has been extended by
  ||| since the candidate was built (extendCS wraps it) — the closure
  ||| shifts its Γ-fixed parts by it, while bindings (already
  ||| extended-context elements) pass through untouched.
  emit : Nat -> List (Nat, Elem) -> Maybe (Elem, List Sel)
  ||| lemma-normalization steps for the lhs (to be INVERTED at replay:
  ||| they turned the raw side into the stored pattern) and the rhs
  preL : List PStep
  postR : List PStep

||| WHERE elaboration currently is: the item that owns the work (the
||| "def foo" every message is prefixed with) and the span of the
||| innermost surface node descended into that recorded one. Most
||| surface nodes record no range, so the span is the narrowest one
||| SEEN so far, not necessarily the node being elaborated — a
||| conservative over-approximation, never a wrong file or item.
|||
||| `Interpolation` yields just the name, so every "\{site}: …"
||| message reads exactly as it did when a site was a bare String.
public export
record Site where
  constructor MkSite
  sname : String
  srange : Maybe Range

public export
Interpolation Site where
  interpolate s = s.sname

||| Narrow a site to a surface node's own span; a node without one
||| leaves the site where it was.
at : Site -> Maybe Range -> Site
at s Nothing = s
at s r = { srange := r } s

||| A derived site: the same span, said more specifically.
sub : Site -> String -> Site
sub s n = { sname := n } s

data Stmt : Type where
  StElem : Ctx -> NameEnv -> Elem -> Elem -> Ty -> Stmt
  StTy : Ctx -> NameEnv -> Ty -> Ty -> Stmt

record Obligation where
  constructor MkObl
  stmt : Stmt
  site : Site
  ||| the file `site`'s span belongs to
  file : String
  composite : Maybe Stmt
  ||| advisory (docs/SearchlessElaboration.md §5.4): what a one-shot
  ||| GLOBAL-store probe found when this SCOPED site failed — search
  ||| as feedback, never as acceptance
  hint : Maybe String

||| Display metadata of one assumed constraint — outside the theory,
||| consumed only by the report printer. The statement itself lives in
||| Σ as a constraint entry (docs/NovaElaboration.txt: there is no
||| separate obligation store); this record is aligned with Σ's
||| constraint entries in surfacing order.
record OblMeta where
  constructor MkOblMeta
  oenv : NameEnv
  osite : Site
  ||| the file the site's span belongs to — obligations outlive the
  ||| module that minted them
  ofile : String
  ocomposite : Maybe Stmt
  ||| advisory hint recorded at assume time (§5.4) — display only
  ohint : Maybe String

||| Display metadata of one declaration — same discipline as OblMeta:
||| the declaration itself is a sig-decl entry of Σ; this record is
||| aligned with Σ's declaration entries in minting order.
record DeclMeta where
  constructor MkDeclMeta
  dname : String
  denv : NameEnv
  dsite : String
  ||| the file `drange` belongs to
  dfile : String
  ||| the declaring item's source span (LSP diagnostics)
  drange : Maybe Range

||| One argument of a QIIT constructor: the name the `data` item wrote
||| for it, and whether it is INDUCTIVE — an inductive argument is
||| followed in the method's telescope by its induction hypothesis (the
||| ᴰ-walk's order, Nova.Kernel.QIIT.dispWalk).
public export
record QIITArg where
  constructor MkQIITArg
  qaName      : String
  qaInductive : Bool

public export
record QIITCtor where
  constructor MkQIITCtor
  qcName : String
  qcArgs : List QIITArg

||| One SORT of a `data` item, with everything APPLYING its generated
||| eliminator needs (docs/NovaElaboration.txt, In-place elimination) —
||| the shapes are in the carried signature, but the NAMES the item
||| minted are not, and neither are the binder names it wrote.
public export
record QIITInfo where
  constructor MkQIITInfo
  ||| the sort's own def name, qualified as Σ has it
  qiSort    : String
  ||| parameters the generated defs Π-bind before everything else, so a
  ||| use site applies them first
  qiParams  : Nat
  ||| this sort's own index arity
  qiIndices : Nat
  ||| every sort of the signature, in entry order — one MOTIVE each —
  ||| and this one's ordinal among them
  qiSorts   : List String
  qiPos     : Nat
  ||| one METHOD per point constructor, one COHERENCE per equation
  ||| constructor (the code-valued eliminator only)
  qiPoints  : List QIITCtor
  qiEqs     : List QIITCtor

record ElabSt where
  constructor MkElabSt
  sig : Sig
  ||| the KERNEL's signature: extended only by kernel-accepted items —
  ||| the authoritative Σ (docs/NovaPipeline.txt)
  kernelSig : Sig
  lemmas : List Cand
  ||| the Σ-level candidate partition, derived from `lemmas` and
  ||| recomputed only when a lemma is added: all (degenerates dropped),
  ||| the two `ordered` blocks, and the hop-only set
  candCs : List Cand
  candShrink : List Cand
  candRest : List Cand
  candHops : List Cand
  ||| candShrink ++ candRest, precomputed: the whole rewrite list when
  ||| Γ contributes nothing
  candRw : List Cand
  ||| the CURRENT module's own lemmas, newest first (archived under its
  ||| name when the module finishes)
  ownLemmas : List Cand
  ||| finished modules' own lemmas, newest MODULE first
  modLemmas : List (String, List Cand)
  ||| finished modules' direct imports, for the transitive closure
  modImports : List (String, List String)
  ||| the module being elaborated, and its direct imports
  curImports : List String
  assumedE : List (Nat, Ctx, Elem, Elem, Ty)   -- normalized keys of assumed elem equations, size-prefixed (cheap dedup prefilter)
  assumedT : List (Ctx, Ty, Ty)           -- normalized keys of assumed type equations
  ||| display metadata for Σ's constraint entries, in surfacing order
  ||| (invariant: one per SigEq/SigTyEq of `sig`, appended together)
  oblMeta : SnocList OblMeta
  ||| display metadata for Σ's declaration entries, in minting order
  ||| (invariant: one per SigDecl/SigTyDecl of `sig`)
  declMeta : SnocList DeclMeta
  ||| binder occurrences with their elaborated types (module, span,
  ||| binding context/env, name, type) — LSP hover ascription
  binderTypes : SnocList (String, Range, Ctx, NameEnv, String, Ty, List Nat)
  ||| solved BLANK occurrences (docs/NovaPerfectSurface.txt, the
  ||| blank tier): the value the spine oracle recovered at a written
  ||| `_`, with its instantiated domain and the SOURCE that bound it
  ||| (Nothing — the expected type; Just a — the type of argument a)
  ||| — the LSP hover for blanks
  blankVals : SnocList (String, Range, NameEnv, Elem, Ty, Maybe Elem)
  ||| dotted name of the module being elaborated; "" = the root file,
  ||| whose entries stay unqualified
  modPrefix : String
  ||| the file that module was read from — the location prefix an
  ||| obligation or declaration is reported at (they outlive the
  ||| module that minted them: the root's report lists every module's)
  modFile : String
  ||| the module's effective fixity table — an error that names a TYPE
  ||| renders it the way the user writes it, infix and all
  modFix : FixTable
  ||| the item currently elaborating (surface name; "" between items) —
  ||| exposure-survey attribution
  curItem : String
  ||| surface-name → Σ-name aliases: the module's own entries plus the
  ||| opened names of its imports (last entry wins; locals were already
  ||| resolved by the parser and never reach this table)
  vis : SnocList (String, String)
  ||| when Just, the Σ-level candidate SCOPE of the current discharge
  ||| site: only the lemmas named here participate in matching and
  ||| rewriting (hypotheses of Γ always do). Set transiently around a
  ||| `⋆ using (…)` site (docs/SearchlessElaboration.md §5.3); Nothing
  ||| = the full store, the historical behavior.
  scope : Maybe (List String)
  ||| Σ-names of definitions whose UNFOLDING the current item/site has
  ||| licensed for equation joins, by citing `<name>.eq` in its using
  ||| clause — the explicit, named form of δ for equational reasoning
  ||| (the defining-equation lemma family). Consulted only by the
  ||| strict-conversion join.
  eqScope : List String
  ||| SITE-LOCAL candidates, merged into every candidate set while
  ||| set: the reflected link justifications of a calc chain (§5.2).
  ||| Ground, at the site's own context — set transiently, like scope.
  localCands : List Cand
  ||| transient override of the engine's match/hop depth budget: a
  ||| chain needs one hop per link, so its composite discharge runs at
  ||| depth links + spDepth instead of the fixed spDepth
  depthOv : Maybe Nat
  ||| Σ-name → the IMPLICIT positions of its leading Π-telescope
  ||| (docs/NovaPerfectSurface.txt, Phase 3): the {x : A} binders of
  ||| the def's surface type, recorded at acceptance, consulted at
  ||| application spines. Metadata only — nothing of it reaches the
  ||| core or the kernel.
  impls : List (String, List Nat)
  ||| the implicitize TRIAL (Phase 3c): when on, every {t}-override at
  ||| an implicit position also runs the hypothetical elided recovery
  ||| and records whether it would reproduce the written value
  ||| α-exactly — the measurement the implicitize distiller folds
  impTrialOn : Bool
  ||| verdicts: 0 = elidable; 1 = trailing; 2 = stuck at an
  ||| intro-form argument; 3 = unsolved (no source matched); 4 =
  ||| solved but α-differs from the written value (spelling drift)
  impTrial : SnocList (String, Nat, Nat, Maybe (String, Range))
  ||| the Phase-4 SUGAR TRIAL: at every written ∈-annotation and
  ||| inline motive, record whether the elided form would recover it
  ||| α-exactly — (module, site range, verdict); the distiller's
  ||| elision map
  svSugarOn : Bool
  svSugar : SnocList (String, Range, Bool)
  ||| the BLANK-EMISSION trial (Phase 4): per applied-definition site,
  ||| which written explicit arguments the distiller may replace with
  ||| `_` — (module, head range, ITEM index among the consumed
  ||| arguments), the whole set verified as ONE joint hypothetical
  ||| solve, closed to a fixpoint for byte-idempotence
  svBlank : SnocList (String, Range, Nat)
  ||| blanks whose implicit-mode solve would DIFFER (suppressed
  ||| join-tier binding α-differs from the solution) — per-site
  ||| blockers for a blank → implicit migration
  svBlankRisk : SnocList (String, Range, Nat)
  ||| inside an overload PROBE: state is discarded and the verdict is
  ||| the obligation delta alone, so the expensive per-assume work —
  ||| the whole-store hint probe, rewrite normalization of the keys —
  ||| is skipped
  probing : Bool
  ||| inside the elaboration of a SPINE ARGUMENT (transitively): only
  ||| such sites can FLIP from checking to inference when an
  ||| enclosing position is blanked, so only their blank verdicts
  ||| must hold in both modes
  inArg : Bool
  ||| SOLVED synthetic holes, from the refinement pass (`refineHoles`).
  ||| DISPLAY ONLY, and computed only when a report is rendered: the
  ||| pass runs after elaboration is over, reads the run's own
  ||| constraint entries, and never touches Σ — so this is a
  ||| metacontext in the sense the removed solver's flips were not.
  ||| Empty on every run that has no holes, which is what keeps
  ||| `resugarElem`'s lookup free.
  holeSols : List (String, Elem)
  ||| surface names visible with TWO OR MORE distinct Σ targets — the
  ||| OVERLOADED names (docs/NovaPerfectSurface.txt, Phase 4:
  ||| operator overloading). A reference to one resolves
  ||| TYPE-DIRECTEDLY at the site: the unique candidate whose spine
  ||| elaborates with zero new obligations wins; none or several is a
  ||| structural error naming the qualification remedy.
  dupNames : List String
  ||| one per SORT of every `data` item the run elaborated, in item
  ||| order. What in-place elimination reads to apply a generated
  ||| eliminator: the signature says the shapes, this says the names.
  qiits : SnocList QIITInfo

initSt : ElabSt
initSt = MkElabSt [<] [<] [] [] [] [] [] [] [] [] [] [] [] [] [<] [<] [<] [<] "" "" [] "" [<] Nothing [] [] Nothing [] False [<] False [<] [<] [<] False False [] [] [<]

||| Is the surface term an INFERENCE form — its type known without an
||| expected type? Mirrors the mode inventory
||| (docs/NovaElaboration.txt); erased-proof forms and intros carry
||| nothing.
export
sInferForm : SElem -> Bool
sInferForm e0 = case unPos e0 of
  SHole _ _ => False
  SLam _ _ => False
  SLet _ _ _ => False
  SPair _ _ => False
  SInj1 _ => False
  SInj2 _ => False
  SClass _ => False
  SStar _ => False
  SStarWit _ => False
  SStarUsing _ _ => False
  SChain _ _ => False
  SCoind _ _ _ _ _ _ _ _ => False
  SSquashElim _ _ _ => False
  SCorec _ _ _ _ => False
  SZeroElim _ => False
  SImpArg _ => False
  -- a blank carries nothing: its value comes from the spine's solve
  SBlank _ => False
  -- a motive-less eliminator is CHECKING-ONLY (Phase 4): its motive
  -- comes from the expected type
  SNatElim Nothing _ _ _ _ _ => False
  SSumElim Nothing _ _ _ _ _ => False
  SQuotElim Nothing _ _ _ => False
  _ => True

||| Resolve a surface signature reference: aliases first (own module,
||| opened imports), else the name itself (qualified references reach
||| Σ directly).
resolveSigName : ElabSt -> String -> String
resolveSigName st x = go st.vis
 where
  go : SnocList (String, String) -> String
  go [<] = x
  go (rest :< (a, full)) = if a == x then full else go rest

||| EVERY distinct Σ target the surface name is visible as, newest
||| first ([x] itself when unaliased) — the overload candidate set.
resolveSigAll : ElabSt -> String -> List String
resolveSigAll st x =
  case nub (go st.vis) of
    [] => [x]
    qs => qs
 where
  go : SnocList (String, String) -> List String
  go [<] = []
  go (rest :< (a, full)) = if a == x then full :: go rest else go rest

-- ===== Elaboration monad =====

||| An elaboration failure. `erange` is the span the elaborator was
||| working on when it gave up — refined as `checkElem`/`inferElem`/
||| `elabTy` descend past a surface node that records one (see `Site`)
||| — and Nothing where nothing narrower than the item is known; the
||| caller widens it to the item's own span then.
public export
record Err where
  constructor MkErr
  erange : Maybe Range
  emsg : String

||| The failure channel carries the state AS OF THE THROW alongside
||| the error. It is SALVAGE MATERIAL, not a resumption point: the
||| item folds render the holes and obligations that state records
||| and then discard it, continuing from the state BEFORE the item
||| (docs/NovaElaboration.txt, item recovery). Nothing salvaged ever
||| reaches Σ, so a broken item cannot contribute a definition — it
||| only gets to say what it had learned before it broke.
data ElabM : Type -> Type where
  MkElabM : (ElabSt -> Either (ElabSt, Err) (ElabSt, a)) -> ElabM a

runElabM : ElabM a -> ElabSt -> Either (ElabSt, Err) (ElabSt, a)
runElabM (MkElabM f) = f

||| Run an action for its RESULT only: state is restored afterwards
||| and a failure becomes Nothing — the sugar trial's probe (an extra
||| inference whose effects must not leak into the run).
probeM : ElabM a -> ElabM (Maybe a)
probeM act = MkElabM $ \st => case runElabM act ({ probing := True } st) of
  Left _ => Right (st, Nothing)
  Right (_, x) => Right (st, Just x)

||| Run an action, KEEPING its state on success and restoring the
||| original on failure — the fail-deferral probe: unlike probeM the
||| successful path IS the real elaboration.
attemptM : ElabM a -> ElabM (Maybe a)
attemptM act = MkElabM $ \st => case runElabM act st of
  Left _ => Right (st, Nothing)
  Right (st2, x) => Right (st2, Just x)

||| Run an action as the elaboration of a SPINE ARGUMENT: the flag
||| marks every site inside as mode-flippable (blank verdicts there
||| must hold with and without the expected type), restored after.
asArg : ElabM a -> ElabM a
asArg act = MkElabM $ \st => case runElabM act ({ inArg := True } st) of
  Left e => Left e
  Right (st2, x) => Right ({ inArg := st.inArg } st2, x)


Functor ElabM where
  map f (MkElabM g) = MkElabM $ \st => map (mapSnd f) (g st)

Applicative ElabM where
  pure x = MkElabM $ \st => Right (st, x)
  (MkElabM f) <*> (MkElabM g) = MkElabM $ \st => do
    (st', h) <- f st
    (st'', x) <- g st'
    Right (st'', h x)

Monad ElabM where
  (MkElabM f) >>= k = MkElabM $ \st => do
    (st', x) <- f st
    runElabM (k x) st'

getSt : ElabM ElabSt
getSt = MkElabM $ \st => Right (st, st)

modifySt : (ElabSt -> ElabSt) -> ElabM ()
modifySt f = MkElabM $ \st => Right (f st, ())

putSt : ElabSt -> ElabM ()
putSt st = modifySt (const st)

||| Fail with no span of its own: the caller places it at the
||| enclosing item.
throw : String -> ElabM a
throw e = MkElabM $ \st => Left (st, MkErr Nothing e)

||| Fail AT a span — the surface node the message is about.
throwAt : Maybe Range -> String -> ElabM a
throwAt r e = MkElabM $ \st => Left (st, MkErr r e)

||| Install a visibility alias, tracking OVERLOADS: a name gaining a
||| second distinct target joins dupNames.
addVis : (String, String) -> ElabM ()
addVis (a, q) = do
  st <- getSt
  let others = nub [full | (a', full) <- toList st.vis, a' == a, full /= q]
  let ds' = if not (null others) && not (a `elem` st.dupNames)
              then a :: st.dupNames else st.dupNames
  modifySt $ { vis $= (:< (a, q)), dupNames := ds' }

||| Run an action with the discharge scope set (docs/
||| SearchlessElaboration.md §5.3), restoring the previous scope after.
||| An error aborts the run outright (the state is discarded on Left),
||| so no restore is needed on that path.
withScope : Maybe (List String) -> ElabM a -> ElabM a
withScope Nothing act = act
withScope sc act = do
  st <- getSt
  let old = st.scope
  modifySt { scope := sc }
  r <- act
  modifySt { scope := old }
  pure r

||| Run an action with the eq-unfold scope set (the `<name>.eq`
||| citations of a using clause), restoring after — the equation-side
||| twin of withScope.
withEqScope : List String -> ElabM a -> ElabM a
withEqScope [] act = act
withEqScope ns act = do
  st <- getSt
  let old = st.eqScope
  modifySt { eqScope := ns }
  r <- act
  modifySt { eqScope := old }
  pure r

||| A using-clause name of the form `<def>.eq` cites the DEFINING
||| EQUATION of `<def>`: it licenses unfolding that definition in the
||| site's equation joins. Returns the cited definition's Σ-name.
||| Resolve a using-clause name against Σ, tolerating a module
||| qualifier that does not apply in the current run shape (a ROOT
||| file's own entries are bare, an aggregate's are qualified): the
||| alias/raw resolution first, then progressively stripped leading
||| segments.
resolveFlex : ElabSt -> String -> String
resolveFlex st n = pick (n :: strips n)
 where
  strips : String -> List String
  strips m = case break (== '.') (unpack m) of
               (_, '.' :: rest) => let r = pack rest in r :: strips r
               _ => []
  pick : List String -> String
  pick [] = resolveSigName st n
  pick (m :: ms) =
    let q = resolveSigName st m in
    case sigLookup q st.sig of
      Just _ => q
      Nothing => pick ms

||| `<lemma>.rw` cites a store lemma as a REWRITE rule for the site's
||| discharges — the named form of the removed store rewriting, one
||| rule at a time.
resolveRwName : ElabSt -> String -> Maybe String
resolveRwName st n = do
  let True = isSuffixOf ".rw" n
    | False => Nothing
  let base = substr 0 (minus (length n) 3) n
  let q = resolveFlex st base
  if any (\c => c.candName == q) st.lemmas
    then Just q
    else Nothing

||| `<def>.unfold` licenses HEAD EXPOSURE of the named definition
||| (term or type) at this site — the type-exposure whitelist. An
||| `.eq` citation subsumes it for its definition.
resolveExpName : ElabSt -> String -> Maybe String
resolveExpName st n = do
  let True = isSuffixOf ".unfold" n
    | False => Nothing
  let base = substr 0 (minus (length n) 7) n
  let q = resolveFlex st base
  case sigLookup q st.sig of
    Just (SigDef _ _ _ _) => Just q
    _ => Nothing

resolveEqName : ElabSt -> String -> Maybe String
resolveEqName st n = do
  let True = isSuffixOf ".eq" n
    | False => Nothing
  let base = substr 0 (minus (length n) 3) n
  let q = resolveFlex st base
  case sigLookup q st.sig of
    Just (SigDef _ _ _ _) => Just q
    _ => Nothing

||| Resolve and validate a `using` clause's names (term- or
||| item-level): aliases first, then the name itself; a name that is
||| absent from Σ, or present but not an equation lemma of the visible
||| store, is a structural error — it could only scope the site to
||| nothing. `<def>.eq` names resolve to eq-unfold licenses (snd).
resolveUsingNames : Site -> List String -> ElabM (List String, List String)
resolveUsingNames site ns = do
  st <- getSt
  -- builtin licenses (`pi.eta`/`sigma.eta`/`hyp.rw`) and `<def>.eq`
  -- unfold licenses go to the eq-scope; `<lemma>.rw` cites a store
  -- lemma as a rewrite rule — it enters BOTH the eq-scope (as an
  -- rw: marker) and the ordinary lemma scope
  let sorted = map (\n =>
        if n == "pi.eta" || n == "sigma.eta" || n == "hyp.rw" then ([n], the (List String) []) else
        case resolveExpName st n of
          Just q => (["exp:" ++ q], the (List String) [])
          Nothing =>
           case resolveRwName st n of
            Just q => (["rw:" ++ q], [q])
            Nothing =>
             case resolveEqName st n of
              Just q => ([q], the (List String) [])
              Nothing => (the (List String) [], [n])) ns
  let eqNs = concatMap fst sorted
  let lemNs = concatMap snd sorted
  let rs = map (resolveFlex st) lemNs
  traverse_ (\x =>
    case sigLookup x st.sig of
      Nothing => throwAt site.srange "\{site}: using: unknown name '\{x}'"
      Just _ =>
        if any (\c => c.candName == x) st.lemmas
          then pure ()
          else throwAt site.srange "\{site}: using: '\{x}' is not an equation lemma in the visible store") rs
  pure (rs, eqNs)

||| Run an action with site-local candidates, an EMPTY Σ-scope (a
||| chain never consults the global store) and a depth budget sized to
||| the chain — restoring all three after. Used by the calc-chain rule
||| (docs/SearchlessElaboration.md §5.2).
withLocal : List Cand -> Nat -> ElabM a -> ElabM a
withLocal cs d act = do
  st <- getSt
  let (oldC, oldD, oldS) = (st.localCands, st.depthOv, st.scope)
  modifySt { localCands := cs, depthOv := Just d, scope := Just [] }
  r <- act
  modifySt { localCands := oldC, depthOv := oldD, scope := oldS }
  pure r

-- ===== Small core utilities =====

||| Rewriting-recorded steps are always proof-licensed (path licenses
||| are only ever EMITTED, for the data item's eq-lemmas).
licProof : StepLic -> Elem
licProof (LProof p) = p
licProof (LPath _ _ _) = assert_total $ idris_crash "licProof: path license in a rewrite trace"

||| Strengthen a type away from the k innermost binders
||| (Nothing if any of them is mentioned).
strengthenKTy : Nat -> Ty -> Maybe Ty
strengthenKTy Z t = Just t
strengthenKTy (S k) t = strengthenTy 0 t >>= strengthenKTy k

||| The AMBIENT embedded Nova type pieces of two same-shape QIIT
||| signatures, paired entrywise — the external Π-domains that stand
||| at (or strengthen to) the ambient context, which is where an
||| instantiated parameter lands no matter how deep the entry buries
||| it (vcons : (n : El ℕ) (x : El a) → …). Nothing on any
||| ToS-structural mismatch (entry count, binder shapes, ToS codes).
||| Domains that genuinely use their local ToS binders are skipped:
||| their equality follows from the ambient pieces, via the composite
||| retry.
qsigDom0Pieces : QSig -> QSig -> Maybe (List (Ty, Ty))
qsigDom0Pieces sg0 sg1 =
  if length sg0 /= length sg1 then Nothing
  else map concat (traverse (uncurry (goTy 0)) (zip sg0 sg1))
 where
  goTm : QTm -> QTm -> Maybe ()
  goTm (QVar i) (QVar j) = if i == j then Just () else Nothing
  goTm (QAppE f e) (QAppE g e') = goTm f g   -- embedded elems: typeless here, skipped
  goTm (QAppI f a) (QAppI g b) = do goTm f g; goTm a b
  goTm (QEqC l r u) (QEqC l' r' u') = do goTm l l'; goTm r r'; goTm u u'
  goTm _ _ = Nothing

  goTy : Nat -> QTy -> QTy -> Maybe (List (Ty, Ty))
  goTy d QU QU = Just []
  goTy d (QEl t) (QEl t') = map (const []) (goTm t t')
  goTy d (QPiExt a b) (QPiExt a' b') =
    let piece = if a == a' then []
                else case (strengthenKTy d a, strengthenKTy d a') of
                       (Just s0, Just s1) => [(s0, s1)]
                       _ => []
    in map (piece ++) (goTy (S d) b b')
  goTy d (QPiInd u b) (QPiInd u' b') = do ignore (goTm u u'); goTy (S d) b b'
  goTy _ _ _ = Nothing

||| ν identity is STRUCTURAL on the carried polynomial: same shape, the
||| embedded codes compared pairwise. Depth-0 pieces (not under a
||| polynomial binder) come back for decomposition, strengthened;
||| deeper mismatches make the whole comparison conservative (Nothing).
polyDom0Pieces : Poly -> Poly -> Maybe (List (Elem, Elem))
polyDom0Pieces = goP 0
 where
  piece0 : Nat -> Elem -> Elem -> Maybe (List (Elem, Elem))
  piece0 d a a' =
    if a == a' then Just []
    else if d == 0 then Just [(a, a')]
    else case (strengthenElem d a, strengthenElem d a') of
           (Just s0, Just s1) => Just [(s0, s1)]
           _ => Nothing
  goP : Nat -> Poly -> Poly -> Maybe (List (Elem, Elem))
  goP d PHole PHole = Just []
  goP d (PConst a) (PConst a') = piece0 d a a'
  goP d (PProd f g) (PProd f' g') = [| goP d f f' ++ goP d g g' |]
  goP d (PSum f g) (PSum f' g') = [| goP d f f' ++ goP d g g' |]
  goP d (PSigma a f) (PSigma a' f') = [| piece0 d a a' ++ goP (S d) f f' |]
  goP d (PPi a f) (PPi a' f') = [| piece0 d a a' ++ goP (S d) f f' |]
  goP _ _ _ = Nothing


||| Γ‖ᵢ (same as the derivation checker's private helper).
ctxLookup : Ctx -> Nat -> Maybe Ty
ctxLookup [<]          _     = Nothing
ctxLookup (rest :< ty) Z     = Just (substTy ty Wk)
ctxLookup (rest :< ty) (S n) = map (\t => substTy t Wk) (ctxLookup rest n)

||| The substitution weakening by n (↑ⁿ): x[wkN n] = ☐_{x+n}.
wkN : Nat -> Sub
wkN Z = Id
wkN (S n) = Chain (wkN n) Wk

weakenElemN : Nat -> Elem -> Elem
weakenElemN n e = substElem e (wkN n)

||| Strengthen away the n innermost variables (fails if used).
strengthenElemN : Nat -> Elem -> Maybe Elem
strengthenElemN Z e = Just e
strengthenElemN (S n) e = strengthenElem 0 e >>= strengthenElemN n

-- ===== First-order matching (rewriting) =====
--
-- Pattern lives in base ▷ p_{k-1} ▷ ... ▷ p₀; the match site sits at
-- depth `d` below the ambient context Γ (= the candidate's base for
-- hypotheses; lemmas have base ε so any Γ works). Inside the pattern we
-- track the local binder depth `b`. Pattern variable j:
--   * j < b            — pattern-local: target must be ☐_j;
--   * b ≤ j < b + k    — parametric: bind p_{j-b}; the bound term is
--                        canonicalized to Γ by strengthening away the
--                        d + b local variables (fail = would capture);
--   * j ≥ b + k        — base-rigid: target must be ☐_{j - k + d}.

codeOf : Ty -> Maybe Elem
codeOf UniverseTy = Nothing
codeOf PropTy = Nothing
codeOf TopTy = Nothing
codeOf (Elem.EqTy _ _ _) = Nothing
codeOf (Squash _) = Nothing
-- everything else IS its own code (El retired); the large formers
-- above are the only exclusions the syntax can see — smallness of
-- the rest is the kernel gate's question
codeOf t = Just t

Bindings : Type
Bindings = List (Nat, Elem)

bindParam : Nat -> Elem -> Bindings -> Maybe Bindings
bindParam p e bs =
  case lookup p bs of
    Nothing => Just ((p, e) :: bs)
    Just e' => if e == e' then Just bs else Nothing

||| Type-level matching (declared ahead: matchElemP needs it to cross a
||| ∥-∥ into its squashee; defined below). No type-level pattern
||| variables — parameters are elements.
matchTyP : (k : Nat) -> (d : Nat) -> (b : Nat) -> (pat : Ty) -> (tgt : Ty) -> Bindings -> Maybe Bindings

matchSpineP : (k : Nat) -> (d : Nat) -> (b : Nat) -> SubNorm -> SubNorm -> Bindings -> Maybe Bindings

matchQSigP : (k : Nat) -> (d : Nat) -> (b : Nat) -> QSig -> QSig -> Bindings -> Maybe Bindings

matchQTyP : (k : Nat) -> (d : Nat) -> (b : Nat) -> QTy -> QTy -> Bindings -> Maybe Bindings

matchQTmP : (k : Nat) -> (d : Nat) -> (b : Nat) -> QTm -> QTm -> Bindings -> Maybe Bindings

matchPolyP : (k : Nat) -> (d : Nat) -> (b : Nat) -> Poly -> Poly -> Bindings -> Maybe Bindings

matchElemP : (k : Nat) -> (d : Nat) -> (b : Nat) -> (pat : Elem) -> (tgt : Elem) -> Bindings -> Maybe Bindings
matchElemP k d b (CtxVar j) tgt =
  if j < b
    then case tgt of
           CtxVar m => if m == j then Just else const Nothing
           _ => const Nothing
    else if j < b + k
      then \bs => do e <- strengthenElemN (d + b) tgt
                     bindParam (minus j b) e bs
      else case tgt of
             CtxVar m => if m == minus j k + d then Just else const Nothing
             _ => const Nothing
matchElemP k d b (ZeroElim t) (ZeroElim t') = matchElemP k d b t t'
matchElemP k d b OneIntro OneIntro = Just
matchElemP k d b NatIntro0 NatIntro0 = Just
matchElemP k d b (NatIntro1 t) (NatIntro1 t') = matchElemP k d b t t'
matchElemP k d b (NatElim z s t) (NatElim z' s' t') =
  \bs => matchElemP k d b z z' bs >>= matchElemP k d (2 + b) s s' >>= matchElemP k d b t t'
matchElemP k d b (PiIntro f) (PiIntro f') = matchElemP k d (1 + b) f f'
matchElemP k d b (PiApp f e) (PiApp f' e') =
  \bs => matchElemP k d b f f' bs >>= matchElemP k d b e e'
matchElemP k d b (SigmaIntro u v) (SigmaIntro u' v') =
  \bs => matchElemP k d b u u' bs >>= matchElemP k d b v v'
matchElemP k d b (SigmaElim1 t) (SigmaElim1 t') = matchElemP k d b t t'
matchElemP k d b (SigmaElim2 t) (SigmaElim2 t') = matchElemP k d b t t'
matchElemP k d b (Inj1 t) (Inj1 t') = matchElemP k d b t t'
matchElemP k d b (Inj2 t) (Inj2 t') = matchElemP k d b t t'
matchElemP k d b (SumElim l r t) (SumElim l' r' t') =
  \bs => matchElemP k d (1 + b) l l' bs >>= matchElemP k d (1 + b) r r' >>= matchElemP k d b t t'
matchElemP k d b Elem.ZeroTy Elem.ZeroTy = Just
matchElemP k d b Elem.OneTy Elem.OneTy = Just
matchElemP k d b Elem.NatTy Elem.NatTy = Just
matchElemP k d b (Elem.PiTy a c) (Elem.PiTy a' c') =
  \bs => matchElemP k d b a a' bs >>= matchElemP k d (1 + b) c c'
matchElemP k d b (Elem.SigmaTy a c) (Elem.SigmaTy a' c') =
  \bs => matchElemP k d b a a' bs >>= matchElemP k d (1 + b) c c'
matchElemP k d b (Elem.SumTy a c) (Elem.SumTy a' c') =
  \bs => matchElemP k d b a a' bs >>= matchElemP k d b c c'
matchElemP k d b (Elem.EqTy l r t) (Elem.EqTy l' r' t') =
  \bs => matchElemP k d b l l' bs >>= matchElemP k d b r r' >>= matchTyP k d b t t'
matchElemP k d b (QuotTy a r) (QuotTy a' r') =
  \bs => matchElemP k d b a a' bs >>= matchElemP k d (2 + b) r r'
matchElemP k d b (SigVar x es) (SigVar x' es') =
  if x == x' then goSubNorm es es' else const Nothing
 where
  goSubNorm : SubNorm -> SubNorm -> Bindings -> Maybe Bindings
  goSubNorm [<] [<] = Just
  goSubNorm (es :< e) (es' :< e') = \bs => goSubNorm es es' bs >>= matchElemP k d b e e'
  goSubNorm _ _ = const Nothing
matchElemP k d b (Class a) (Class a') = matchElemP k d b a a'
matchElemP k d b (QuotElim f q) (QuotElim f' q') =
  \bs => matchElemP k d (1 + b) f f' bs >>= matchElemP k d b q q'
matchElemP k d b (Squash t) (Squash t') = matchTyP k d b t t'
matchElemP k d b Star Star = Just
-- QIIT formers: the carried signature is MATCHED through its embedded
-- Nova pieces (a parameterized data item's signature mentions the
-- lemma's parameters); ToS structure and positions compare rigidly,
-- spines componentwise. Eliminators likewise, motives/methods included
-- (motives cross arity+1 binders).
matchElemP k d b (QSort sg j es) (QSort sg' j' es') =
  if j == j' then \bs => matchQSigP k d b sg sg' bs >>= matchSpineP k d b es es'
  else const Nothing
matchElemP k d b (QCtor sg j es) (QCtor sg' j' es') =
  if j == j' then \bs => matchQSigP k d b sg sg' bs >>= matchSpineP k d b es es'
  else const Nothing
matchElemP k d b (QElim sg j ms fs es w) (QElim sg' j' ms' fs' es' w') =
  if j == j'
    then \bs => matchQSigP k d b sg sg' bs
             >>= matchMots (qPositions QKSort sg) ms ms'
             >>= matchList fs fs' >>= matchSpineP k d b es es' >>= matchElemP k d b w w'
    else const Nothing
 where
  matchMots : List Nat -> List Ty -> List Ty -> Bindings -> Maybe Bindings
  matchMots _ [] [] = Just
  matchMots (sj :: sjs) (m :: rest) (m' :: rest') =
    \bs => matchTyP k d (b + S (qArityLen sg sj)) m m' bs >>= matchMots sjs rest rest'
  matchMots _ _ _ = const Nothing
  matchList : List Elem -> List Elem -> Bindings -> Maybe Bindings
  matchList [] [] = Just
  matchList (x :: xs) (y :: ys) = \bs => matchElemP k d b x y bs >>= matchList xs ys
  matchList _ _ = const Nothing
matchElemP k d b UniverseTy UniverseTy = Just
matchElemP k d b PropTy PropTy = Just
matchElemP k d b TopTy TopTy = Just
-- coinductive formers: the carried polynomial is matched through its
-- embedded Nova pieces (former shapes rigid, binders crossed), like
-- the QIIT formers' carried signatures above
matchElemP k d b (Out t) (Out t') = matchElemP k d b t t'
matchElemP k d b (Corec p a f x) (Corec p' a' f' x') =
  \bs => matchPolyP k d b p p' bs >>= matchElemP k d b a a'
      >>= matchElemP k d (1 + b) f f' >>= matchElemP k d b x x'
matchElemP k d b (Elem.NuTy p) (Elem.NuTy p') = matchPolyP k d b p p'
matchElemP _ _ _ _ _ = const Nothing

matchPolyP k d b PHole PHole = Just
matchPolyP k d b (PConst a) (PConst a') = matchElemP k d b a a'
matchPolyP k d b (PProd f g) (PProd f' g') =
  \bs => matchPolyP k d b f f' bs >>= matchPolyP k d b g g'
matchPolyP k d b (PSum f g) (PSum f' g') =
  \bs => matchPolyP k d b f f' bs >>= matchPolyP k d b g g'
matchPolyP k d b (PSigma a f) (PSigma a' f') =
  \bs => matchElemP k d b a a' bs >>= matchPolyP k d (1 + b) f f'
matchPolyP k d b (PPi a f) (PPi a' f') =
  \bs => matchElemP k d b a a' bs >>= matchPolyP k d (1 + b) f f'
matchPolyP _ _ _ _ _ = const Nothing

matchSpineP k d b [<] [<] = Just
matchSpineP k d b (es :< e) (es' :< e') = \bs => matchSpineP k d b es es' bs >>= matchElemP k d b e e'
matchSpineP _ _ _ _ _ = const Nothing

matchQSigP k d b [] [] = Just
matchQSigP k d b (e :: rest) (e' :: rest') =
  \bs => matchQTyP k d b e e' bs >>= matchQSigP k d b rest rest'
matchQSigP _ _ _ _ _ = const Nothing

matchQTyP k d b QU QU = Just
matchQTyP k d b (QEl t) (QEl t') = matchQTmP k d b t t'
matchQTyP k d b (QPiExt a c) (QPiExt a' c') =
  \bs => matchTyP k d b a a' bs >>= matchQTyP k d (1 + b) c c'
matchQTyP k d b (QPiInd u c) (QPiInd u' c') =
  \bs => matchQTmP k d b u u' bs >>= matchQTyP k d b c c'
matchQTyP _ _ _ _ _ = const Nothing

matchQTmP k d b (QVar i) (QVar i') = if i == i' then Just else const Nothing
matchQTmP k d b (QAppE f e) (QAppE f' e') =
  \bs => matchQTmP k d b f f' bs >>= matchElemP k d b e e'
matchQTmP k d b (QAppI f a) (QAppI f' a') =
  \bs => matchQTmP k d b f f' bs >>= matchQTmP k d b a a'
matchQTmP k d b (QEqC l r u) (QEqC l' r' u') =
  \bs => matchQTmP k d b l l' bs >>= matchQTmP k d b r r' >>= matchQTmP k d b u u'
matchQTmP _ _ _ _ _ = const Nothing

matchTyP k d b ZeroTy ZeroTy = Just
matchTyP k d b OneTy OneTy = Just
matchTyP k d b NatTy NatTy = Just
matchTyP k d b UniverseTy UniverseTy = Just
matchTyP k d b PropTy PropTy = Just
matchTyP k d b TopTy TopTy = Just
matchTyP k d b (PiTy a c) (PiTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d (1 + b) c c'
matchTyP k d b (SigmaTy a c) (SigmaTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d (1 + b) c c'
matchTyP k d b (SumTy a c) (SumTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d b c c'
matchTyP k d b (QuotTy a r) (QuotTy a' r') =
  \bs => matchTyP k d b a a' bs >>= matchElemP k d (2 + b) r r'
matchTyP k d b (SigVar x es) (SigVar x' es') =
  if x == x' then goSubNorm es es' else const Nothing
 where
  goSubNorm : SubNorm -> SubNorm -> Bindings -> Maybe Bindings
  goSubNorm [<] [<] = Just
  goSubNorm (es :< e) (es' :< e') = \bs => goSubNorm es es' bs >>= matchElemP k d b e e'
  goSubNorm _ _ = const Nothing
matchTyP k d b (QSort sg j es) (QSort sg' j' es') =
  if j == j' then \bs => matchQSigP k d b sg sg' bs >>= matchSpineP k d b es es'
  else const Nothing
-- El retired: a non-former pattern in type position is a CODE
-- pattern (possibly parameter-headed) — match it against the ground
-- as a code
matchTyP k d b t tgt = \bs => codeOf tgt >>= \c => matchElemP k d b t c bs

||| Build the instantiating substitution: pattern context base ▷ p_{k-1}
||| ▷ ... ▷ p₀ into the match site (Γ + d). Base part is ↑ᵈ; each bound
||| term (canonical in Γ) is weakened by d.
instSub : (k : Nat) -> (d : Nat) -> Bindings -> Maybe Sub
instSub k d bs = go k (wkN d)
 where
  go : Nat -> Sub -> Maybe Sub
  go Z acc = Just acc
  go (S p) acc = do
    e <- lookup p bs
    go p (Ext acc (weakenElemN d e))

-- ===== Candidates =====

peelPis : Ctx -> Ty -> (Ctx, Ty)
peelPis ctx ty =
  case ty of
    PiTy a b => peelPis (ctx :< a) b
    _ => (ctx, ty)

lastEntries : Nat -> Ctx -> List Ty
lastEntries n ctx = drop (minus (length ctx) n) (toList ctx)

||| Instantiating substitution for a parameter's own type: param p's
||| type lives in base ▷ p_{k-1} ▷ ... ▷ p_{p+1}.
condSub : (k : Nat) -> (p : Nat) -> Bindings -> Maybe Sub
condSub k p bs =
  let idxs = if S p <= minus k 1 then reverse [S p .. minus k 1] else [] in
  foldl (\acc, j => [| Ext acc (lookup j bs) |]) (Just Id) idxs

||| Size of a type (declared ahead: elemSize needs it for ∥T∥; defined
||| below).
tySize : Ty -> Nat

polySize : Poly -> Nat

elemSize : Elem -> Nat
elemSize (CtxVar _) = 1
elemSize (ZeroElim t) = S (elemSize t)
elemSize OneIntro = 1
elemSize NatIntro0 = 1
elemSize (NatIntro1 t) = S (elemSize t)
elemSize (NatElim z s t) = S (elemSize z + elemSize s + elemSize t)
elemSize (PiIntro f) = S (elemSize f)
elemSize (PiApp f e) = S (elemSize f + elemSize e)
elemSize (Let a b) = S (elemSize a + elemSize b)
elemSize (SigmaIntro u v) = S (elemSize u + elemSize v)
elemSize (SigmaElim1 t) = S (elemSize t)
elemSize (SigmaElim2 t) = S (elemSize t)
elemSize (Inj1 t) = S (elemSize t)
elemSize (Inj2 t) = S (elemSize t)
elemSize (SumElim l r t) = S (elemSize l + elemSize r + elemSize t)
elemSize Elem.ZeroTy = 1
elemSize Elem.OneTy = 1
elemSize Elem.NatTy = 1
elemSize UniverseTy = 1
elemSize PropTy = 1
elemSize TopTy = 1
elemSize (Elem.PiTy a b) = S (elemSize a + elemSize b)
elemSize (Elem.SigmaTy a b) = S (elemSize a + elemSize b)
elemSize (Elem.SumTy a b) = S (elemSize a + elemSize b)
elemSize (Elem.EqTy l r t) = S (elemSize l + elemSize r + tySize t)
elemSize (QuotTy a r) = S (elemSize a + elemSize r)
elemSize (SigVar _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
elemSize (Class a) = S (elemSize a)
elemSize (QuotElim f q) = S (elemSize f + elemSize q)
elemSize (Squash t) = S (tySize t)
elemSize Star = 1
-- QIIT formers: the signature counts as head material (a constant),
-- the spines as arguments
elemSize (QSort _ _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
elemSize (QCtor _ _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
elemSize (QElim _ _ ms fs es w) =
  S (foldl (\acc, m => acc + tySize m) 0 ms +
     foldl (\acc, f => acc + elemSize f) 0 fs +
     foldl (\acc, e => acc + elemSize e) 0 es + elemSize w)
elemSize (Elem.NuTy p) = S (polySize p)
elemSize (Out t) = S (elemSize t)
elemSize (Corec p a f x) = S (polySize p + elemSize a + elemSize f + elemSize x)

tySize = elemSize

polySize PHole = 1
polySize (PConst a) = S (elemSize a)
polySize (PProd f g) = S (polySize f + polySize g)
polySize (PSum f g) = S (polySize f + polySize g)
polySize (PSigma a f) = S (elemSize a + polySize f)
polySize (PPi a f) = S (elemSize a + polySize f)

||| Equal up to a bijective renaming of the parametric variables
||| (commutativity-shaped) — such equations loop as rewrite rules.
permutative : Cand -> Bool
permutative c = isJust (go 0 c.lhs c.rhs [])
 where
  bij : Nat -> Nat -> List (Nat, Nat) -> Maybe (List (Nat, Nat))
  bij i j m =
    case (lookup i m, find (\(_, y) => y == j) m) of
      (Nothing, Nothing) => Just ((i, j) :: m)
      (Just j', _) => if j' == j then Just m else Nothing
      (Nothing, Just _) => Nothing

  goT : Nat -> Ty -> Ty -> List (Nat, Nat) -> Maybe (List (Nat, Nat))

  goSp : Nat -> SubNorm -> SubNorm -> List (Nat, Nat) -> Maybe (List (Nat, Nat))

  go : Nat -> Elem -> Elem -> List (Nat, Nat) -> Maybe (List (Nat, Nat))
  go b (CtxVar i) (CtxVar j) m =
    if i < b || j < b
      then if i == j then Just m else Nothing
      else if i < b + c.params && j < b + c.params
        then bij (minus i b) (minus j b) m
        else if i == j then Just m else Nothing
  go b (ZeroElim t) (ZeroElim t') m = go b t t' m
  go b OneIntro OneIntro m = Just m
  go b NatIntro0 NatIntro0 m = Just m
  go b (NatIntro1 t) (NatIntro1 t') m = go b t t' m
  go b (NatElim z s t) (NatElim z' s' t') m = go b z z' m >>= go (2+b) s s' >>= go b t t'
  go b (PiIntro f) (PiIntro f') m = go (1+b) f f' m
  go b (PiApp f e) (PiApp f' e') m = go b f f' m >>= go b e e'
  go b (SigmaIntro u v) (SigmaIntro u' v') m = go b u u' m >>= go b v v'
  go b (SigmaElim1 t) (SigmaElim1 t') m = go b t t' m
  go b (SigmaElim2 t) (SigmaElim2 t') m = go b t t' m
  go b (Inj1 t) (Inj1 t') m = go b t t' m
  go b (Inj2 t) (Inj2 t') m = go b t t' m
  go b (SumElim l r t) (SumElim l' r' t') m = go (1+b) l l' m >>= go (1+b) r r' >>= go b t t'
  go b Elem.ZeroTy Elem.ZeroTy m = Just m
  go b Elem.OneTy Elem.OneTy m = Just m
  go b Elem.NatTy Elem.NatTy m = Just m
  go b (Elem.PiTy a d) (Elem.PiTy a' d') m = go b a a' m >>= go (1+b) d d'
  go b (Elem.SigmaTy a d) (Elem.SigmaTy a' d') m = go b a a' m >>= go (1+b) d d'
  go b (Elem.SumTy a d) (Elem.SumTy a' d') m = go b a a' m >>= go b d d'
  go b (Elem.EqTy l r t) (Elem.EqTy l' r' t') m = go b l l' m >>= go b r r' >>= goT b t t'
  go b (QuotTy a r) (QuotTy a' r') m = go b a a' m >>= go (2+b) r r'
  go b (SigVar x es) (SigVar x' es') m =
    if x == x' then goSN es es' m else Nothing
   where
    goSN : SubNorm -> SubNorm -> List (Nat, Nat) -> Maybe (List (Nat, Nat))
    goSN [<] [<] m = Just m
    goSN (es :< e) (es' :< e') m = goSN es es' m >>= go b e e'
    goSN _ _ _ = Nothing
  go b (Class a) (Class a') m = go b a a' m
  go b (QuotElim f q) (QuotElim f' q') m = go (1+b) f f' m >>= go b q q'
  go b (Squash t) (Squash t') m = goT b t t' m
  go b Star Star m = Just m
  go b (QSort sg j es) (QSort sg' j' es') m =
    if sg == sg' && j == j' then goSp b es es' m else Nothing
  go b (QCtor sg j es) (QCtor sg' j' es') m =
    if sg == sg' && j == j' then goSp b es es' m else Nothing
  go b UniverseTy UniverseTy m = Just m
  go b PropTy PropTy m = Just m
  go b TopTy TopTy m = Just m
  go _ _ _ _ = Nothing

  goSp b [<] [<] m = Just m
  goSp b (es :< e) (es' :< e') m = goSp b es es' m >>= go b e e'
  goSp _ _ _ _ = Nothing

  goT b ZeroTy ZeroTy m = Just m
  goT b OneTy OneTy m = Just m
  goT b NatTy NatTy m = Just m
  goT b UniverseTy UniverseTy m = Just m
  goT b PropTy PropTy m = Just m
  goT b (PiTy a d) (PiTy a' d') m = goT b a a' m >>= goT (1+b) d d'
  goT b (SigmaTy a d) (SigmaTy a' d') m = goT b a a' m >>= goT (1+b) d d'
  goT b (SumTy a d) (SumTy a' d') m = goT b a a' m >>= goT b d d'
  goT b (QuotTy a r) (QuotTy a' r') m = goT b a a' m >>= go (2+b) r r'
  goT b (SigVar x es) (SigVar x' es') m =
    if x == x' then goSNT es es' m else Nothing
   where
    goSNT : SubNorm -> SubNorm -> List (Nat, Nat) -> Maybe (List (Nat, Nat))
    goSNT [<] [<] m = Just m
    goSNT (es :< e) (es' :< e') m = goSNT es es' m >>= go b e e'
    goSNT _ _ _ = Nothing
  goT b (QSort sg j es) (QSort sg' j' es') m =
    if sg == sg' && j == j' then goSp b es es' m else Nothing
  -- a non-former type pair is a CODE pair (El retired): compare as
  -- elements — a Nothing here would misclassify code-typed lemmas
  goT b x y m = go b x y m

||| Candidates usable as REWRITE rules (strictly-shrinking first;
||| permutative and growing equations never rewrite).
orderedParts : List Cand -> (List Cand, List Cand)
orderedParts cs =
  let usable = filter (\c => (elemSize c.rhs <= elemSize c.lhs || varDef c || clauseShaped c) && not (permutative c)) cs
      shrinking = filter (\c => elemSize c.rhs < elemSize c.lhs) usable
      rest = filter (\c => not (elemSize c.rhs < elemSize c.lhs)) usable
  in (shrinking, rest)
 where
  -- EXPERIMENT (searchless research): a CLAUSE-SHAPED candidate — a
  -- SigVar-headed application spine with a constructor-headed argument
  -- — is admitted as a rewrite rule even when size-increasing: each
  -- firing consumes a constructor the pattern demands, so it plays the
  -- role of one ι-step of computation stated in the abstraction's own
  -- vocabulary (the clause lemmas of a clausal def are exactly this).
  ctorHeaded : Elem -> Bool
  ctorHeaded NatIntro0 = True
  ctorHeaded (NatIntro1 _) = True
  ctorHeaded (Inj1 _) = True
  ctorHeaded (Inj2 _) = True
  ctorHeaded (Class _) = True
  ctorHeaded (QCtor _ _ _) = True
  ctorHeaded _ = False

  spineArgs : Elem -> (Elem, List Elem)
  spineArgs (PiApp f x) = let (h, as) = spineArgs f in (h, as ++ [x])
  spineArgs e = (e, [])

  clauseShaped : Cand -> Bool
  clauseShaped c =
    case spineArgs c.lhs of
      (SigVar _ _, args) => any ctorHeaded args
      -- an OBSERVATION equation — out at a definition- or
      -- fixed-variable-headed spine — is one el-nu-beta ι-step stated
      -- in the abstraction's own vocabulary: the observation lemma of
      -- a copattern def, and the g-clause hypothesis of its
      -- uniqueness proof, are exactly this. (A parameter-headed
      -- scrutinee would match ANY observation — excluded.)
      (Out t, _) => case spineArgs t of
                      (SigVar _ _, _) => True
                      (CtxVar j, _) => j >= c.params
                      _ => False
      _ => False
  -- a VARIABLE-DEFINITION rule — ground, ☐ₙ ⇝ t with ☐ₙ not in t —
  -- terminates regardless of size (each application strictly removes
  -- an occurrence), so it is usable as a rewrite rule even when
  -- growing: the "the hypothesis defines this variable" pattern that
  -- coinduction invariants produce
  varDef : Cand -> Bool
  varDef c =
    c.params == 0 &&
    (case c.lhs of
       CtxVar n => isJust (strengthenElem n c.rhs)
       _ => False)

-- ===== Step materialization =====
--
-- A logical rewrite (site path π, candidate, bindings) becomes kernel
-- steps: the candidate's lhs-normalization INVERTED at π (bridging the
-- raw licensed equation to the stored pattern), the main step, then the
-- rhs-normalization at π. PStep proofs live over the candidate's
-- parametric context and are instantiated here.

kernelFuel : Nat
kernelFuel = 1000000

materialize : Cand -> Bindings -> (onLhs : Bool) -> (sitePath : List Nat) -> Maybe (List Step)
materialize c bs side pi = do
  (prfMain, selsMain) <- c.emit 0 bs
  sigma <- instSub c.params 0 bs
  let instStep = \ps : PStep => MkStep side (pi ++ ps.ppath) (LProof (substElem ps.pprf sigma)) ps.psels ps.pflip
  let pre = map (\ps => { flip $= not } (instStep ps)) (reverse c.preL)
  let post = map instStep c.postR
  pure (pre ++ [MkStep side pi (LProof prfMain) selsMain False] ++ post)

materializeFlip : Cand -> Bindings -> (onLhs : Bool) -> Maybe (List Step)
materializeFlip c bs side = do
  (prfMain, selsMain) <- c.emit 0 bs
  sigma <- instSub c.params 0 bs
  let instStep = \ps : PStep => MkStep side ps.ppath (LProof (substElem ps.pprf sigma)) ps.psels ps.pflip
  -- flipped whole-equation use at the root: post-normalization is
  -- inverted (it now bridges INTO the stored rhs pattern), pre applies
  let pre = map (\ps => { flip $= not } (instStep ps)) (reverse c.postR)
  let post = map instStep c.preL
  pure (pre ++ [MkStep side [] (LProof prfMain) selsMain True] ++ post)

-- ===== Rewriting with step recording =====

||| Rewrites inside TYPE positions (declared ahead: element descent
||| crosses ∥-∥ into its squashee; defined below).
rewriteTyS : (side : Bool) -> Cand -> (path : List Nat) -> (d : Nat) -> Ty -> Maybe (Ty, List Step)

||| One rewrite anywhere in the term: returns the rewritten term and
||| the kernel steps that justify it. Only fires if materializable.
rewriteElemS : (side : Bool) -> Cand -> (path : List Nat) -> (d : Nat) -> Elem -> Maybe (Elem, List Step)
rewriteElemS side c pi d t =
  (do bs <- matchElemP c.params d 0 c.lhs t []
      guard (isJust (instSub c.params d bs))
      steps <- materialize c bs side (reverse pi)
      sigma <- instSub c.params d bs
      Just (substElem c.rhs sigma, steps))
  <|> descend t
 where
  first : List (Maybe a) -> Maybe a
  first [] = Nothing
  first (Just x :: _) = Just x
  first (Nothing :: rest) = first rest

  at : Nat -> Nat -> Elem -> (Elem -> Elem) -> Maybe (Elem, List Step)
  at i db u re = (\(u', st) => (re u', st)) <$> rewriteElemS side c (i :: pi) (db + d) u

  spineAt : SubNorm -> (SubNorm -> Elem) -> Maybe (Elem, List Step)
  spineAt es re =
    let xs = toList es in
    first (map (\i =>
      case getAt i xs of
        Just e => (\(e', st) =>
                     case splitAt i xs of
                       (pre, _ :: post) => (re (cast (pre ++ e' :: post)), st)
                       _ => (re es, st))
                  <$> rewriteElemS side c (i :: pi) d e
        Nothing => Nothing) [0 .. minus (length xs) 1])

  -- Certificate-bearing rewriting (this engine feeds kernel-replayed
  -- steps) does not descend into children whose positional TYPE the
  -- kernel's typed descent cannot determine while crossing binders
  -- (childTyE: an eliminator's cases, a λ's body, a corecursor's
  -- coalgebra): a step there would be rejected at replay ("step at a
  -- type-undetermined position"). The same subterm is reached after
  -- the enclosing eliminator computes — so scrutinees rewrite FIRST
  -- and the collapse surfaces the branch at depth 0 (the relator's
  -- ⊎-elim at rewritten observations is the motivating case).
  descend : Elem -> Maybe (Elem, List Step)
  descend (ZeroElim u)       = at 0 0 u ZeroElim
  descend (NatIntro1 u)      = at 0 0 u NatIntro1
  descend (NatElim z s u)    =
    first [ at 2 0 u (\u' => NatElim z s u')
          , at 0 0 z (\z' => NatElim z' s u) ]
  descend (PiIntro f)        = Nothing
  descend (PiApp f e)        =
    first [ at 0 0 f (\f' => PiApp f' e)
          , at 1 0 e (\e' => PiApp f e') ]
  descend (SigmaIntro u v)   =
    first [ at 0 0 u (\u' => SigmaIntro u' v)
          , at 1 0 v (\v' => SigmaIntro u v') ]
  descend (SigmaElim1 u)     = at 0 0 u SigmaElim1
  descend (SigmaElim2 u)     = at 0 0 u SigmaElim2
  descend (Inj1 u)           = at 0 0 u Inj1
  descend (Inj2 u)           = at 0 0 u Inj2
  descend (SumElim l r u)    = at 2 0 u (\u' => SumElim l r u')
  descend (Elem.PiTy a c')   =
    first [ at 0 0 a (\a' => Elem.PiTy a' c')
          , at 1 1 c' (\c'' => Elem.PiTy a c'') ]
  descend (Elem.SigmaTy a c') =
    first [ at 0 0 a (\a' => Elem.SigmaTy a' c')
          , at 1 1 c' (\c'' => Elem.SigmaTy a c'') ]
  descend (Elem.SumTy a c')  =
    first [ at 0 0 a (\a' => Elem.SumTy a' c')
          , at 1 0 c' (\c'' => Elem.SumTy a c'') ]
  descend (Elem.EqTy l r u)  =
    first [ at 0 0 l (\l' => Elem.EqTy l' r u)
          , at 1 0 r (\r' => Elem.EqTy l r' u) ]
    <|> ((\(u', st) => (Elem.EqTy l r u', st)) <$> rewriteTyS side c (2 :: pi) d u)
  descend (QuotTy a r)       =
    first [ at 0 0 a (\a' => QuotTy a' r)
          , at 1 2 r (\r' => QuotTy a r') ]
  descend (SigVar x es)      = goSN 0 es
   where
    goSN : Nat -> SubNorm -> Maybe (Elem, List Step)
    goSN _ [<] = Nothing
    goSN _ _ =
      let xs = toList es in
      first (map (\i =>
        case getAt i xs of
          Just e => (\(e', st) =>
                       case splitAt i xs of
                         (pre, _ :: post) => (SigVar x (cast (pre ++ e' :: post)), st)
                         _ => (SigVar x es, st))
                    <$> rewriteElemS side c (i :: pi) d e
          Nothing => Nothing) [0 .. minus (length xs) 1])
  descend (Class a)          = at 0 0 a Class
  descend (QuotElim f q)     = at 1 0 q (\q' => QuotElim f q')
  descend (Squash t)         =
    (\(t', st) => (Squash t', st)) <$> rewriteTyS side c (0 :: pi) d t
  -- QIIT formers: spines and the eliminee are addressable; the carried
  -- signature and eliminator problem are OPAQUE (NovaKernel.txt, A3)
  descend (QSort sg k es)  = spineAt es (\es' => QSort sg k es')
  descend (QCtor sg k es)   = spineAt es (\es' => QCtor sg k es')
  descend (QElim sg k ms fs es w) =
    spineAt es (\es' => QElim sg k ms fs es' w)
      <|> at (length (toList es)) 0 w (\w' => QElim sg k ms fs es w')
  -- ν formers: out's scrutinee and corec's carrier/body/seed are
  -- addressable; the carried polynomial is OPAQUE, like a signature
  descend (Out t) = at 0 0 t Out
  descend (Corec p a f x) =
    at 0 0 a (\a' => Corec p a' f x)
      <|> at 2 0 x (\x' => Corec p a f x')
  descend _ = Nothing

rewriteTyS side c pi d ZeroTy = Nothing
rewriteTyS side c pi d OneTy = Nothing
rewriteTyS side c pi d NatTy = Nothing
rewriteTyS side c pi d UniverseTy = Nothing
rewriteTyS side c pi d PropTy = Nothing
rewriteTyS side c pi d (PiTy a b) =
  ((\(a', st) => (PiTy a' b, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(b', st) => (PiTy a b', st)) <$> rewriteTyS side c (1 :: pi) (1 + d) b)
rewriteTyS side c pi d (SigmaTy a b) =
  ((\(a', st) => (SigmaTy a' b, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(b', st) => (SigmaTy a b', st)) <$> rewriteTyS side c (1 :: pi) (1 + d) b)
rewriteTyS side c pi d (SumTy a b) =
  ((\(a', st) => (SumTy a' b, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(b', st) => (SumTy a b', st)) <$> rewriteTyS side c (1 :: pi) d b)
rewriteTyS side c pi d (QuotTy a r) =
  ((\(a', st) => (QuotTy a' r, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(r', st) => (QuotTy a r', st)) <$> rewriteElemS side c (1 :: pi) (2 + d) r)
-- a ν type has no child indices: the carried polynomial is OPAQUE to
-- paths, like a carried signature (NovaKernel.txt, child indexing)
rewriteTyS side c pi d (NuTy f) = Nothing
-- QIIT sort application: rewriting reaches the INDEX SPINE; the carried
-- signature is OPAQUE to paths (NovaKernel.txt, A3)
rewriteTyS side c pi d (QSort sg k es) =
  let xs = toList es in
  firstJQ (map (\i =>
    case getAt i xs of
      Just e => (\(e', st) =>
                   case splitAt i xs of
                     (pre, _ :: post) => (QSort sg k (cast (pre ++ e' :: post)), st)
                     _ => (QSort sg k es, st))
                <$> rewriteElemS side c (i :: pi) d e
      Nothing => Nothing) [0 .. minus (length xs) 1])
 where
  firstJQ : List (Maybe a) -> Maybe a
  firstJQ [] = Nothing
  firstJQ (Just x' :: _) = Just x'
  firstJQ (Nothing :: rest) = firstJQ rest
rewriteTyS side c pi d (SigVar x es) =
  let xs = toList es in
  firstJ (map (\i =>
    case getAt i xs of
      Just e => (\(e', st) =>
                   case splitAt i xs of
                     (pre, _ :: post) => (SigVar x (cast (pre ++ e' :: post)), st)
                     _ => (SigVar x es, st))
                <$> rewriteElemS side c (i :: pi) d e
      Nothing => Nothing) [0 .. minus (length xs) 1])
 where
  firstJ : List (Maybe a) -> Maybe a
  firstJ [] = Nothing
  firstJ (Just x' :: _) = Just x'
  firstJ (Nothing :: rest) = firstJ rest
-- a non-former type is a CODE (El retired): rewrite through it as an
-- element — the kernel replays type steps via stepElem at 𝕍, so the
-- element child indexing is the type child indexing
rewriteTyS side c pi d t = rewriteElemS side c pi d t

-- ===== Normalize-and-rewrite (step-recording) =====

rwFuel : Nat
rwFuel = 40

tryCands : List Cand -> (Cand -> Maybe a) -> Maybe a
tryCands [] f = Nothing
tryCands (c :: cs) f = f c <|> tryCands cs f

-- ===== whitelisted δ for equation joins (`<def>.eq` citations) =====
--
-- unfElem/unfTy replace every SigVar reference to a LICENSED term
-- definition by its body — recursively (a body may cite another
-- licensed name; Σ is a DAG, so this terminates) — leaving everything
-- else as written. The strict join is then compElem/compTy of the
-- result: α + computation + exactly the cited unfoldings. Type-level
-- SigVars stay stuck here: type-abbreviation exposure is the
-- (separate) head-exposure whitelist's domain.

mutual
  unfSubNorm : Sig -> List String -> SubNorm -> SubNorm
  unfSubNorm sig unfs [<] = [<]
  unfSubNorm sig unfs (es :< e) = unfSubNorm sig unfs es :< unfElem sig unfs e

  unfElem : Sig -> List String -> Elem -> Elem
  unfElem sig unfs e@(CtxVar _)      = e
  unfElem sig unfs (ZeroElim t)      = ZeroElim (unfElem sig unfs t)
  unfElem sig unfs OneIntro          = OneIntro
  unfElem sig unfs NatIntro0         = NatIntro0
  unfElem sig unfs (NatIntro1 t)     = NatIntro1 (unfElem sig unfs t)
  unfElem sig unfs (NatElim z s t)   = NatElim (unfElem sig unfs z) (unfElem sig unfs s) (unfElem sig unfs t)
  unfElem sig unfs (PiIntro f)       = PiIntro (unfElem sig unfs f)
  unfElem sig unfs (PiApp f e)       = PiApp (unfElem sig unfs f) (unfElem sig unfs e)
  unfElem sig unfs (Let a b)         = Let (unfElem sig unfs a) (unfElem sig unfs b)
  unfElem sig unfs (SigmaIntro a b)  = SigmaIntro (unfElem sig unfs a) (unfElem sig unfs b)
  unfElem sig unfs (SigmaElim1 t)    = SigmaElim1 (unfElem sig unfs t)
  unfElem sig unfs (SigmaElim2 t)    = SigmaElim2 (unfElem sig unfs t)
  unfElem sig unfs (Inj1 t)          = Inj1 (unfElem sig unfs t)
  unfElem sig unfs (Inj2 t)          = Inj2 (unfElem sig unfs t)
  unfElem sig unfs (SumElim l r t)   = SumElim (unfElem sig unfs l) (unfElem sig unfs r) (unfElem sig unfs t)
  unfElem sig unfs Elem.ZeroTy       = Elem.ZeroTy
  unfElem sig unfs Elem.OneTy        = Elem.OneTy
  unfElem sig unfs Elem.NatTy        = Elem.NatTy
  unfElem sig unfs (Elem.PiTy a b)   = Elem.PiTy (unfElem sig unfs a) (unfElem sig unfs b)
  unfElem sig unfs (Elem.SigmaTy a b) = Elem.SigmaTy (unfElem sig unfs a) (unfElem sig unfs b)
  unfElem sig unfs (Elem.SumTy a b)  = Elem.SumTy (unfElem sig unfs a) (unfElem sig unfs b)
  unfElem sig unfs UniverseTy        = UniverseTy
  unfElem sig unfs PropTy            = PropTy
  unfElem sig unfs TopTy             = TopTy
  unfElem sig unfs (Elem.EqTy l r t) = Elem.EqTy (unfElem sig unfs l) (unfElem sig unfs r) (unfTy sig unfs t)
  unfElem sig unfs (QuotTy a r)      = QuotTy (unfElem sig unfs a) (unfElem sig unfs r)
  unfElem sig unfs (SigVar x es) =
    let es' = unfSubNorm sig unfs es in
    if elem x unfs
      then case cachedSigLookup sig x of
             Just (SigDef _ _ a _) => unfElem sig unfs (substElem a (embed es'))
             _ => SigVar x es'
      else SigVar x es'
  unfElem sig unfs (Class a)         = Class (unfElem sig unfs a)
  unfElem sig unfs (QuotElim f q)    = QuotElim (unfElem sig unfs f) (unfElem sig unfs q)
  unfElem sig unfs (Squash t)        = Squash (unfTy sig unfs t)
  unfElem sig unfs Star              = Star
  unfElem sig unfs (QSort sg k es)  = QSort (unfQSig sig unfs sg) k (unfSubNorm sig unfs es)
  unfElem sig unfs (QCtor sg k es)   = QCtor (unfQSig sig unfs sg) k (unfSubNorm sig unfs es)
  unfElem sig unfs (QElim sg k ms fs es w) =
    QElim (unfQSig sig unfs sg) k (map (unfTy sig unfs) ms) (map (unfElem sig unfs) fs)
      (unfSubNorm sig unfs es) (unfElem sig unfs w)
  unfElem sig unfs (Elem.NuTy f)     = Elem.NuTy (unfPoly sig unfs f)
  unfElem sig unfs (Out t)           = Out (unfElem sig unfs t)
  unfElem sig unfs (Corec p a f x)   =
    Corec (unfPoly sig unfs p) (unfElem sig unfs a) (unfElem sig unfs f) (unfElem sig unfs x)

  unfPoly : Sig -> List String -> Poly -> Poly
  unfPoly sig unfs PHole        = PHole
  unfPoly sig unfs (PConst a)   = PConst (unfElem sig unfs a)
  unfPoly sig unfs (PProd f g)  = PProd (unfPoly sig unfs f) (unfPoly sig unfs g)
  unfPoly sig unfs (PSum f g)   = PSum (unfPoly sig unfs f) (unfPoly sig unfs g)
  unfPoly sig unfs (PSigma a f) = PSigma (unfElem sig unfs a) (unfPoly sig unfs f)
  unfPoly sig unfs (PPi a f)    = PPi (unfElem sig unfs a) (unfPoly sig unfs f)

  unfQTm : Sig -> List String -> QTm -> QTm
  unfQTm sig unfs (QVar i)     = QVar i
  unfQTm sig unfs (QAppE f e)  = QAppE (unfQTm sig unfs f) (unfElem sig unfs e)
  unfQTm sig unfs (QAppI f a)  = QAppI (unfQTm sig unfs f) (unfQTm sig unfs a)
  unfQTm sig unfs (QEqC l r u) = QEqC (unfQTm sig unfs l) (unfQTm sig unfs r) (unfQTm sig unfs u)

  unfQTy : Sig -> List String -> QTy -> QTy
  unfQTy sig unfs QU           = QU
  unfQTy sig unfs (QEl t)      = QEl (unfQTm sig unfs t)
  unfQTy sig unfs (QPiExt a b) = QPiExt (unfTy sig unfs a) (unfQTy sig unfs b)
  unfQTy sig unfs (QPiInd u b) = QPiInd (unfQTm sig unfs u) (unfQTy sig unfs b)

  unfQSig : Sig -> List String -> QSig -> QSig
  unfQSig sig unfs = map (unfQTy sig unfs)

  unfTy : Sig -> List String -> Ty -> Ty
  unfTy = unfElem

||| The join normal form of a side — comp plus the site's licensed
||| unfoldings — extended, under a cited `hyp.rw` / `<lemma>.rw`
||| license, by the rewrite loop RESTRICTED to the licensed rules
||| (hypotheses, chain links, named Σ-lemmas; never the whole store).
rwNfElemS : Sig -> (unfs : List String) -> List Cand -> (side : Bool) -> Elem -> (Elem, List Step)
rwNfElemS sig unfs cands side e =
  let start = compElem (unfElem sig unfs e) in
  if elem "hyp.rw" unfs || any (isPrefixOf "rw:") unfs
    then goS rwFuel [start] start []
    else (start, [])
 where
  hypCs : List Cand
  hypCs = filter (\c => (elem "hyp.rw" unfs && (c.candName == "hypothesis" || c.candName == "chain link"))
                      || elem ("rw:" ++ c.candName) unfs) cands
  goS : Nat -> List Elem -> Elem -> List Step -> (Elem, List Step)
  goS Z seen t acc = (t, acc)
  goS (S fuel) seen t acc =
    case tryCands hypCs (\c => rewriteElemS side c [] 0 t) of
      Just (t', st) =>
        let t'' = compElem (unfElem sig unfs t') in
        if elem t'' seen then (t, acc) else goS fuel (t'' :: seen) t'' (acc ++ st)
      Nothing => (t, acc)

rwNfTyS : Sig -> (unfs : List String) -> List Cand -> (side : Bool) -> Ty -> (Ty, List Step)
rwNfTyS sig unfs cands side ty =
  let start = compTy (unfTy sig unfs ty) in
  if elem "hyp.rw" unfs || any (isPrefixOf "rw:") unfs
    then goS rwFuel [start] start []
    else (start, [])
 where
  hypCs : List Cand
  hypCs = filter (\c => (elem "hyp.rw" unfs && (c.candName == "hypothesis" || c.candName == "chain link"))
                      || elem ("rw:" ++ c.candName) unfs) cands
  goS : Nat -> List Ty -> Ty -> List Step -> (Ty, List Step)
  goS Z seen t acc = (t, acc)
  goS (S fuel) seen t acc =
    case tryCands hypCs (\c => rewriteTyS side c [] 0 t) of
      Just (t', st) =>
        let t'' = compTy (unfTy sig unfs t') in
        if elem t'' seen then (t, acc) else goS fuel (t'' :: seen) t'' (acc ++ st)
      Nothing => (t, acc)

-- ===== Head exposure and its whitelist =====
--
-- Weak-head exposure with LOGGED δ-unfolds: semantics of whnfE/whnfT,
-- plus a `unf <module>|<name>` profile bump per definition unfolded —
-- the survey stream for the future per-item `using`-unfold whitelist.
-- Used wherever conversion or checking needs a TYPE head; equation
-- SIDES never δ-expand.

||| May head exposure unfold `x` at this site? Under an `<x>.unfold` (or subsuming
||| `<x>.eq`) citation — or with NOVA_EXPOSE_OPEN=1, the survey escape
||| hatch that logs what a whitelist would need without enforcing one.
expOK : ElabSt -> String -> Bool
expOK st x =
  surveyMode
    || elem "exp:*" st.eqScope
    || elem x st.eqScope || elem ("exp:" ++ x) st.eqScope

mutual
  exposeE : ElabSt -> Elem -> Elem
  exposeE st (NatElim z s t) =
    case exposeE st t of
      NatIntro0   => exposeE st z
      NatIntro1 n => exposeE st (substElem s (Ext (Ext Id n) (NatElim z s n)))
      t'          => NatElim z s t'
  exposeE st (PiApp f e) =
    case exposeE st f of
      PiIntro g => exposeE st (substElem g (Ext Id e))
      f'        => PiApp f' e
  exposeE st (Let a b) = exposeE st (substElem b (Ext (Ext Id a) Star))
  exposeE st (SigmaElim1 t) =
    case exposeE st t of
      SigmaIntro a _ => exposeE st a
      t'             => SigmaElim1 t'
  exposeE st (SigmaElim2 t) =
    case exposeE st t of
      SigmaIntro _ b => exposeE st b
      t'             => SigmaElim2 t'
  exposeE st (SumElim l r t) =
    case exposeE st t of
      Inj1 a => exposeE st (substElem l (Ext Id a))
      Inj2 b => exposeE st (substElem r (Ext Id b))
      t'     => SumElim l r t'
  exposeE st (SigVar x es) =
    if not (expOK st x) then bump "expblock \{st.modPrefix}:\{st.curItem}|\{x}" 1
                               (noteBlocked x
                                 (audit "EXPOSE-BLOCKED \{st.modPrefix}:\{st.curItem} \{x} — cite \{x}.unfold" (SigVar x es))) else
    case cachedSigLookup st.sig x of
      Just (SigDef _ _ a _) => bump "unf \{st.modPrefix}:\{st.curItem}|\{x}" 1 (exposeE st (substElem a (embed es)))
      _ => SigVar x es
  exposeE st (QuotElim f q) =
    case exposeE st q of
      Class a => exposeE st (substElem f (Ext Id a))
      q'      => QuotElim f q'
  exposeE st (Squash t) =
    case exposeT st t of
      -- code-squash-idem's syntax-directed instances
      p@(Elem.EqTy _ _ _) => exposeE st p
      p@(Squash _)        => exposeE st p
      t'    => Squash t'
  exposeE st (QElim sg k ms fs es w) =
    case exposeE st w of
      QCtor sgW c theta =>
        if sgW == sg
          then case qElimBetaRhs sg ms fs c theta of
                 Right rhs => exposeE st rhs
                 Left _ => QElim sg k ms fs es (QCtor sgW c theta)
          else QElim sg k ms fs es (QCtor sgW c theta)
      w' => QElim sg k ms fs es w'
  exposeE st (Out t) =
    case exposeE st t of
      Corec p a f x => exposeE st (mapPoly p (corecCopair p a f) (substElem f (Ext Id x)))
      t'            => Out t'
  exposeE st e = e

  exposeT : ElabSt -> Ty -> Ty
  -- El retired: a type head is exposed whatever its entry's
  -- classifier — TYPE POSITION is the license (the old El clause's
  -- free code exposure, now direct); non-former heads (applications,
  -- eliminations) expose through exposeE
  exposeT st (SigVar x es) =
    if not (expOK st x) then bump "expblock \{st.modPrefix}:\{st.curItem}|\{x}" 1
                               (noteBlocked x
                                 (audit "EXPOSE-BLOCKED \{st.modPrefix}:\{st.curItem} \{x} — cite \{x}.unfold" (SigVar x es))) else
    case cachedSigLookup st.sig x of
      Just (SigDef _ _ a _) => bump "unf \{st.modPrefix}:\{st.curItem}|\{x}" 1 (exposeT st (substTy a (embed es)))
      _ => SigVar x es
  exposeT st t@(PiApp _ _) = case exposeE st t of
    t'@(PiApp _ _) => t'
    t' => exposeT st t'
  exposeT st t@(SigmaElim1 _) = case exposeE st t of
    t'@(SigmaElim1 _) => t'
    t' => exposeT st t'
  exposeT st t@(SigmaElim2 _) = case exposeE st t of
    t'@(SigmaElim2 _) => t'
    t' => exposeT st t'
  exposeT st t@(NatElim _ _ _) = case exposeE st t of
    t'@(NatElim _ _ _) => t'
    t' => exposeT st t'
  exposeT st t = t

||| The engine normalizer for EQUATION-SIDE positions: δ-free
||| computation only. Type-HEAD positions use exposeT instead.
engNfE : ElabSt -> Elem -> Elem
engNfE st e = compElem e

||| The engine's JOIN normal form at the current site: comp plus the
||| site's licensed unfoldings — for positions that must stay in the
||| join vocabulary (hop residues).
engJoinE : ElabSt -> Elem -> Elem
engJoinE st e = compElem (unfElem st.sig st.eqScope e)

engNfT : ElabSt -> Ty -> Ty
engNfT st t = compTy t

||| Is this type a PROPOSITION? Syntax-directed at the Ω formers
||| (≡/∥·∥ — the head marks it, the role the retired Prf head used to
||| play), through exposure; a NEUTRAL type is a prop exactly when
||| its kernel-inferred type is Ω. UNTRUSTED like everything here —
||| the kernel's kIsProp re-establishes prop-ness at replay.
isPropTy : ElabSt -> Ctx -> Ty -> Bool
isPropTy st ctx t = case t of
  Elem.EqTy _ _ _ => True
  Squash _ => True
  -- the RAW spelling first: a neutral spine (≤ x y) checks at Ω AS
  -- WRITTEN, while its exposure may be a stuck eliminator whose type
  -- nothing can recover (kIsPropB also covers ⊎-elim's
  -- constant-motive checking — the relator's stuck props)
  _ => kIsPropB st.kernelSig kernelFuel ctx t
       || (case exposeT st t of
             Elem.EqTy _ _ _ => True
             Squash _ => True
             t' => kIsPropB st.kernelSig kernelFuel ctx t')

||| Blocked head exposures as an obligation hint (peeked, not drained —
||| an item's obligations share the notes).
||| Only a DEFINITION has an `.unfold` to cite. A DECLARATION — an
||| abstract interface's axiom, or a hole — reaches the same blocked
||| branch of `exposeE`, being equally stuck there, but naming it
||| would advertise a remedy that cannot exist. Filtered HERE, at
||| render time, and not in `exposeE`: that branch is hot, and
||| classifying every blocked head just to phrase a note nobody may
||| read measured at +1.5% on the corpus's elaborate phase.
citable : Sig -> List String -> List String
citable sig = filter (\x => case sigLookup x sig of
                              Just (SigDef _ _ _ _) => True
                              _ => False)

blockedHint : Sig -> Maybe String
blockedHint sig =
  case citable sig (peekBlocked ()) of
    [] => Nothing
    ns => Just ("head exposure blocked for " ++ joinBy ", " ns
                ++ " — cite " ++ joinBy ", " (map (++ ".unfold") ns))


||| CHECKING-position head exposure: swaps the historical full
||| normalization for the logged whnf-δ exposure — same head, and the
||| per-module `unf` labels record exactly the names a future
||| `using`-unfold whitelist would carry.
exposeHead : ElabSt -> Ty -> Ty
exposeHead st ty = exposeT st ty

||| Prop-code exposure at checking positions (⋆, squash-elim, chains).
exposeCode : ElabSt -> Elem -> Elem
exposeCode st p = exposeE st p

||| Leading-Π exposure for telescope peeling (domains stay as
||| written, each codomain head exposed in turn).
exposePisT : ElabSt -> Ty -> Ty
exposePisT st ty = case exposeT st ty of
  PiTy a b => PiTy a (exposePisT st b)
  t => t

||| Telescope-peeling normalization: leading-Π exposure.
peelNf : ElabSt -> Ty -> Ty
peelNf st ty = exposePisT st ty

-- ===== Candidates in scope =====

selArity : Sel -> Nat
selArity (SelCod _) = 1
selArity (SelQRel _ _) = 2
selArity _ = 0

ordered : List Cand -> List Cand
ordered cs = let (a, b) = orderedParts cs in a ++ b

||| A REWRITE rule needs a RIGID symbol at its lhs head: a bare
||| parameter spine (v, v .π₁, v x) matches every same-shaped term
||| first-order, and with matching type-blind such a rule fires at
||| arbitrarily ill-typed positions — the certificate then dies at
||| replay and takes the whole discharge down with it (id.nova's
||| onlyZIsZ, v .π₁ ≡ Z at El OnlyZ, was the observed shape: in
||| global-store mode it rewrote a .π₁ at El (IsNatAlgebra A)).
||| Whole-equation and hop use are unaffected: there the FULL
||| statement must match, and replay still guards. A Γ-variable head
||| (i ≥ params) IS rigid — a hypothesis about a fixed context
||| element is a legitimate rule.
rigidLhs : Cand -> Bool
rigidLhs c = go c.lhs
 where
  go : Elem -> Bool
  go (CtxVar i) = i >= c.params
  go (PiApp f _) = go f
  go (SigmaElim1 t) = go t
  go (SigmaElim2 t) = go t
  go _ = True

||| The Σ-level partition of a lemma store: what mkCandSet used to
||| recompute on every attempt.
sigCandParts : List Cand -> (List Cand, List Cand, List Cand, List Cand)
sigCandParts ls =
  let cs = filter (\c => c.lhs /= c.rhs) ls
      (sh, re) = orderedParts (filter rigidLhs cs)
      hp = filter (\c => permutative c || elemSize c.rhs > elemSize c.lhs) cs
  in (cs, sh, re, hp)

||| Close a candidate under component decomposition (code injectivity;
||| S via a derivable predecessor). Only un-normalized candidates are
||| closed: a component of a lemma-rewritten side would not match the
||| raw licensed equation's components.
closeCand : Cand -> List Cand
closeCand c =
  if not (null c.preL) || not (null c.postR)
    then [c]
    else c :: go c.lhs c.rhs
 where
  child : (mk : Bindings -> Maybe Sel) -> (n : Nat) -> List Ty -> Elem -> Elem -> Cand
  child mk n tys l r =
    { params $= (+ n)
    , paramTys $= (++ tys)
    , lhs := l, rhs := r
    , emit := \wk, bs => do
        let parentBs = mapMaybe (\(i, e) => if i >= n then Just (minus i n, e) else Nothing) bs
        (p, sels) <- c.emit wk parentBs
        sel <- mk bs
        pure (p, sels ++ [sel])
    } c

  comp : Sel -> Elem -> Elem -> List Cand
  comp s l r = closeCand (child (\_ => Just s) 0 [] l r)

  go : Elem -> Elem -> List Cand
  go (NatIntro1 x) (NatIntro1 y) = comp SelSuc x y
  go (Elem.PiTy a0 b0) (Elem.PiTy a1 b1) =
    comp SelDom a0 a1
    ++ closeCand (child (\bs => SelCod <$> lookup 0 bs) 1 [a1] b0 b1)
  go (Elem.SigmaTy a0 b0) (Elem.SigmaTy a1 b1) =
    comp SelDom a0 a1
    ++ closeCand (child (\bs => SelCod <$> lookup 0 bs) 1 [a1] b0 b1)
  go (Elem.SumTy a0 b0) (Elem.SumTy a1 b1) =
    -- code-sum-inj: both components at 𝕌, neither under a binder
    comp SelSumL a0 a1 ++ comp SelSumR b0 b1
  go (QuotTy a0 r0) (QuotTy a1 r1) =
    comp SelQDom a0 a1
    ++ closeCand (child (\bs => [| SelQRel (lookup 1 bs) (lookup 0 bs) |]) 2
                        [a1, substTy a1 Wk] r0 r1)
  go _ _ = []

||| Eq-typed hypotheses of Γ (leading Πs peeled) as candidates with base
||| Γ. Ground hypotheses (no peeled binders) are additionally normalized
||| against the lemma store, RECORDING the normalization so the kernel
||| can bridge from the raw reflected equation. The rewrite set is a
||| parameter so a SCOPED site normalizes its hypotheses against the
||| scoped rules only.
hypCands : ElabSt -> (rw : List Cand) -> Ctx -> List Cand
hypCands st rw ctx = concatMap closeCand (concatMap candsAt [0 .. minus (length ctx) 1])
 where
  lemmaRw : List Cand
  lemmaRw = rw

  toPSteps : List Step -> List PStep
  toPSteps = map (\s => MkPStep s.path (licProof s.lic) s.sels s.flip)

  -- a hypothesis licenses an equation when its (peeled) type IS an
  -- equality prop (the prop is the type — Prf retired; squashed
  -- spellings converge by code-squash-idem during normalization)
  eqShape : Ty -> Maybe (Elem, Elem, Ty)
  eqShape t =
    case exposeCode st t of
      Elem.EqTy l r ty => Just (l, r, ty)
      _ => Nothing

  candAt : Nat -> Maybe Cand
  candAt i = do
    tyI <- ctxLookup ctx i
    let (ctx', peeled) = peelPis ctx (peelNf st tyI)
    let k = minus (length ctx') (length ctx)
    case eqShape peeled of
      Just (l, r, t) =>
        let mk : Nat -> Bindings -> Maybe (Elem, List Sel)
            mk = \wk, bs => do
              args <- traverse (\p => lookup p bs)
                        (the (List Nat) (if k == 0 then [] else reverse [0 .. minus k 1]))
              pure (foldl PiApp (CtxVar (i + wk)) args, the (List Sel) [])
        in if k == 0
             then let (l1, lSteps) = rwNfElemS st.sig st.eqScope lemmaRw True (engNfE st l)
                      (r1, rSteps) = rwNfElemS st.sig st.eqScope lemmaRw True (engNfE st r)
                  in Just (MkCand "hypothesis" 0 [] l1 r1 mk (toPSteps lSteps) (toPSteps rSteps))
             else Just (MkCand "hypothesis" k (lastEntries k ctx')
                          (engNfE st l) (engNfE st r) mk [] [])
      Nothing => Nothing

  -- a GROUND hypothesis whose type is a (nested, non-dependent) Σ of
  -- equality props licenses one candidate per component, the proof
  -- element being the projection chain (el-reflect takes any term at
  -- an equality prop, so a projection is a legitimate witness). This is
  -- the shape squash-elim binds when an invariant is a conjunction.
  groundEqCand : Elem -> (Elem, Elem, Ty) -> Cand
  groundEqCand prf (l, r, t) =
    let (l1, lSteps) = rwNfElemS st.sig st.eqScope lemmaRw True (engNfE st l)
        (r1, rSteps) = rwNfElemS st.sig st.eqScope lemmaRw True (engNfE st r)
    in MkCand "hypothesis" 0 [] l1 r1 (\wk, _ => Just (weakenElemN wk prf, [])) (toPSteps lSteps) (toPSteps rSteps)

  pairEqs : Nat -> (proj : Elem) -> Ty -> List (Elem, (Elem, Elem, Ty))
  pairEqs fuel proj ty =
    case fuel of
      Z => []
      S fuel' =>
        case exposeT st ty of
          SigmaTy a b =>
            -- dependent Σs instantiate the body at the projection —
            -- existential invariants (Σ of data and equations) land here
            pairEqs fuel' (SigmaElim1 proj) a ++
            pairEqs fuel' (SigmaElim2 proj) (substTy b (Ext Id (SigmaElim1 proj)))
          -- an equality prop AS the component type (Prf retired)
          tyX => case exposeCode st tyX of
                   Elem.EqTy l r t => [(proj, (l, r, t))]
                   _ => []

  candsAt : Nat -> List Cand
  candsAt i =
    case candAt i of
      Just c => [c]
      Nothing =>
        case ctxLookup ctx i of
          Just tyI =>
            case exposeHead st tyI of
              tyB@(SigmaTy _ _) => map (uncurry groundEqCand) (pairEqs 8 (CtxVar i) tyB)
              _ => []
          Nothing => []

record CandSet where
  constructor MkCandSet
  all : List Cand
  rw : List Cand
  hops : List Cand

mkCandSet : ElabSt -> Ctx -> CandSet
mkCandSet st ctx =
  -- degenerate candidates (sides identical after normalization) carry
  -- no content beyond beta and — with a bare-parameter lhs — would
  -- match ANYTHING as a hop, emitting ill-typed junk steps.
  -- The Σ-level part is cached in ElabSt (sigCandParts); only the
  -- Γ-level hypotheses are computed here, and at a top-level item
  -- there are none.
  --
  -- A SCOPE (a `⋆ using` site) restricts the Σ-level part to the named
  -- lemmas — the partition is recomputed over the filtered store, and
  -- the hypotheses normalize against the scoped rules. Candidate SIDES
  -- were normalized against the store as of their acceptance (a global
  -- property of the stored form, unchanged by scoping); scoping
  -- controls which equations PARTICIPATE.
  let (sCs, sShrink, sRest, sHops) =
        the (List Cand, List Cand, List Cand, List Cand) $
        case st.scope of
          Nothing => (st.candCs, st.candShrink, st.candRest, st.candHops)
          Just names => sigCandParts (filter (\c => elem c.candName names) st.lemmas)
      sRw = case st.scope of
              Nothing => st.candRw
              Just _ => sShrink ++ sRest
  -- LOCALS (a chain adjacency's link) come FIRST — both their rule
  -- blocks, ahead of every hypothesis and store rule: a link's rule
  -- must act before a sibling hypothesis's can corrupt the sides away
  -- from the link's shape (a hypothesis k ≡ Z rewriting inside
  -- a + k ≐ b leaves the link a + k ≡ b nothing to match, and a
  -- SHRINK hypothesis outranks a size-preserving link in the merged
  -- blocks, so the blocks must not be merged).
      -- hops for chain links always; for hypotheses under
      -- a hyp.rw license; for Σ-lemmas under their <lemma>.rw license
      sHopsStrict = filter (\c => elem ("rw:" ++ c.candName) st.eqScope) sHops
      hypLicensed = elem "hyp.rw" st.eqScope
  in case (st.localCands, hypCands st sRw ctx) of
       ([], []) => MkCandSet sCs sRw sHopsStrict
       (ls, hs) =>
         let (lcs, lsh, lre, lhp) = sigCandParts ls
             (hcs, hsh, hre, hhp) = sigCandParts hs
         in MkCandSet (lcs ++ sCs ++ hcs)
                      (lsh ++ lre ++ sShrink ++ hsh ++ sRest ++ hre)
                      (lhp ++ sHopsStrict ++ (if hypLicensed then hhp else []))

rwNfElem : ElabSt -> Ctx -> Elem -> Elem
rwNfElem st ctx e = fst (rwNfElemS st.sig st.eqScope (mkCandSet st ctx).rw True e)

rwNfTy : ElabSt -> Ctx -> Ty -> Ty
rwNfTy st ctx ty = fst (rwNfTyS st.sig st.eqScope (mkCandSet st ctx).rw True ty)

-- ===== Neutral type inference =====

||| Head exposure for neutral inference: logged whnf-δ,
||| full normalization otherwise.
neExpose : ElabSt -> Ty -> Ty
neExpose st ty = exposeT st ty

inferNe : ElabSt -> Ctx -> Elem -> Maybe Ty
inferNe st ctx (CtxVar i) = ctxLookup ctx i
inferNe st ctx (PiApp f x) =
  case neExpose st <$> inferNe st ctx f of
    Just (PiTy a b) => Just (substTy b (Ext Id x))
    _ => Nothing
inferNe st ctx (SigmaElim1 t) =
  case neExpose st <$> inferNe st ctx t of
    Just (SigmaTy a b) => Just a
    _ => Nothing
inferNe st ctx (SigmaElim2 t) =
  case neExpose st <$> inferNe st ctx t of
    Just (SigmaTy a b) => Just (substTy b (Ext Id (SigmaElim1 t)))
    _ => Nothing
inferNe st ctx (SigVar x es) =
  -- cachedSigLookup: the name index (below trust — inferNe only feeds
  -- the engine, and its output is validated at replay)
  case cachedSigLookup st.sig x of
    Just (SigDef _ _ _ ty) => Just (substTy ty (embed es))
    Just (SigDecl _ _ ty) => Just (substTy ty (embed es))
    _ => Nothing
inferNe _ _ _ = Nothing

-- ===== Certificate-emitting speculative equality =====
--
-- Every discharge now RETURNS its evidence: a Kernel.ECert. The
-- committing conversion validates the certificate by kernel replay
-- before believing it (docs/NovaPipeline.txt) — a discharge whose
-- certificate does not replay is no discharge at all.


extendCS : CandSet -> CandSet
extendCS cs = MkCandSet (map wk cs.all) (map wk cs.rw) (map wk cs.hops)
 where
  liftK : Nat -> Sub
  liftK Z = Wk
  liftK (S n) = under (liftK n)

  wkSel : Nat -> Sel -> Sel
  wkSel n (SelCod u) = SelCod (substElem u (liftK n))
  wkSel n s = s

  wkP : Nat -> PStep -> PStep
  wkP n = { pprf $= (\e => substElem e (liftK n))
          , psels $= map (wkSel n) }

  wk : Cand -> Cand
  wk c = { lhs $= (\e => substElem e (liftK c.params))
         , rhs $= (\e => substElem e (liftK c.params))
         , paramTys := snd (foldl (\(j, acc), ty =>
             (S j, acc ++ [substTy ty (liftK j)])) (the (Nat, List Ty) (Z, [])) c.paramTys)
         , emit $= (\f, w => f (S w))
         , preL $= map (wkP c.params)
         , postR $= map (wkP c.params) } c

spDepth : Nat
spDepth = 3

||| Measurement scaffolding: time a pure computation against a label.
||| Sequential lets pin the evaluation order (the attemptE pattern).
timed : String -> (() -> a) -> a
timed label f =
  let t0 = nowNs ()
      r = f ()
  in bump label (nowNs () - t0) r

||| Monadic sibling of `timed` for ElabM actions.
timedM : String -> ElabM a -> ElabM a
timedM label act = do
  let t0 = nowNs ()
  r <- act
  pure (bump label (nowNs () - t0) r)

prefixSteps : Nat -> List Step -> List Step
prefixSteps i = map ({ path $= (i ::) })

||| Steps of a certificate that is pure steps + beta (flattenable into
||| a parent at a path); Nothing when the final is type-directed.
flatSteps : ECert -> Maybe (List Step)
flatSteps (MkECertF Nothing steps FBeta _) = Just steps
flatSteps _ = Nothing

||| ... and with no proofs needed at all (safe under binders, where a
||| Γ-level proof reference would go out of scope).
stepFree : ECert -> Bool
stepFree (MkECertF Nothing [] FBeta _) = True
stepFree _ = False

mutual
  ||| Γ ⊢ a ≐ b : A, speculatively; Just cert = dischargeable with this
  ||| evidence.
  spEqElemC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Maybe ECert
  spEqElemC dep st cs ctx a b ty =
    -- TIER 0 (↓ step 0): α-identical as written — reflexivity, before
    -- any normalization; nested speculative comparisons (congruence
    -- children, side conditions, hop residues) hit this constantly
    if a == b then Just (MkECert [] FBeta) else
    -- TIER 1 (↓ step ½): the computational join — δ-free, so it costs
    -- surface-sized work and never opens a definition
    if timed "tier1" (\_ => compElem a == compElem b) then Just (MkECert [] FBeta) else
    -- expose the equation's type by lemma normalization; when that
    -- takes steps, the certificate carries them as a TYPE BRIDGE and
    -- the whole replay happens at the exposed type (where positions
    -- the steps land on are structurally determined)
    let t0 = nowNs ()
        (tyX, tySteps) = rwNfTyS st.sig st.eqScope cs.rw True ty
        bridge = case tySteps of
                   [] => Nothing
                   _ => Just (tyX, MkECert tySteps FBeta)
        (a', aSteps) = rwNfElemS st.sig st.eqScope cs.rw True a
        (b', bSteps) = rwNfElemS st.sig st.eqScope cs.rw False b
        base = aSteps ++ bSteps
        tyN = exposeT st tyX
        eqFast = bump "rwnf-elem" (nowNs () - t0)
                   (bump "sz-in" (cast (elemSize a + elemSize b))
                     (bump "sz-nf" (cast (elemSize a' + elemSize b'))
                       (a' == b'))) in
    if eqFast
      then Just (MkECertF bridge base FBeta [])
      else
        (do rest <- timed "sp-match" (\_ => candMatchC dep st cs ctx a' b' tyN) >>= unbridged
            pure (MkECertF bridge (base ++ rest.steps) rest.final []))
        <|> (do rest <- timed "sp-struct" (\_ => spEqStructC dep st cs ctx a' b' tyN) >>= unbridged
                pure (MkECertF bridge (base ++ rest.steps) rest.final []))
        -- syntactic congruence: one deterministic descent of the two
        -- sides' common structure, children discharged strictly — the
        -- certificate-assembly twin of the decompose splitting (allowed
        -- here; the banned automation is the rwNf positional
        -- candidate search, not this)
        <|> (do congSteps <- timed "sp-cong" (\_ => spCongC dep st cs ctx a' b')
                pure (MkECertF bridge (base ++ congSteps) FBeta []))
   where
    unbridged : ECert -> Maybe ECert
    unbridged c@(MkECertF Nothing _ _ _) = Just c
    unbridged _ = Nothing

  spEqStructC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Maybe ECert
  spEqStructC dep st cs ctx a b OneTy = Just (MkECert [] FProp)
  spEqStructC dep st cs ctx a b ZeroTy = Just (MkECert [] FProp)
  -- el-pi-eta, UNCONDITIONALLY: even two neutral sides may be joined
  -- pointwise (funext-via-reflection — a hypothesis (x : A) → Prf
  -- (f x ≡ g x) becomes a whole-equation candidate for the body once
  -- the context is extended). Terminates: recursion is on cod.
  spEqStructC dep st cs ctx a b (PiTy dom cod) =
    -- η: outside the strict subset unless the site cites `pi.eta`
    do guard (elem "pi.eta" st.eqScope)
       sub <- spEqElemC dep st (extendCS cs) (ctx :< dom)
                (engNfE st (PiApp (substElem a Wk) (CtxVar 0)))
                (engNfE st (PiApp (substElem b Wk) (CtxVar 0)))
                cod
       pure (MkECert [] (FEtaPi sub))
  -- same-tag injections at a sum: decompose to the payloads at the
  -- branch type (≐-congruence at inj; el-one-prop then closes 𝟙
  -- payloads, which is how a three-valued sign's cases discharge)
  spEqStructC dep st cs ctx (Inj1 x) (Inj1 y) (SumTy domL _) =
    do sub <- spEqElemC dep st cs ctx (engNfE st x) (engNfE st y) domL
       pure (MkECert [] (FInj sub))
  spEqStructC dep st cs ctx (Inj2 x) (Inj2 y) (SumTy _ domR) =
    do sub <- spEqElemC dep st cs ctx (engNfE st x) (engNfE st y) domR
       pure (MkECert [] (FInj sub))
  spEqStructC dep st cs ctx a b (SigmaTy dom cod) =
    -- pair-η: outside the strict subset unless the site cites `sigma.eta`
    if elem "sigma.eta" st.eqScope && (isPair a || isPair b)
      then do c1 <- spEqElemC dep st cs ctx (engNfE st (SigmaElim1 a)) (engNfE st (SigmaElim1 b)) dom
              c2 <- spEqElemC dep st cs ctx (engNfE st (SigmaElim2 a)) (engNfE st (SigmaElim2 b))
                      (substTy cod (Ext Id (SigmaElim1 a)))
              pure (MkECert [] (FEtaSigma c1 c2))
      else Nothing
   where
    isPair : Elem -> Bool
    isPair (SigmaIntro _ _) = True
    isPair _ = False
  spEqStructC dep st cs ctx (Class x) (Class y) (QuotTy dom rel) =
    case engNfE st (substElem rel (Ext (Ext Id x) y)) of
      Squash OneTy => Just (MkECert [] (FWitness Nothing))
      Elem.EqTy l r t => do sub <- spEqElemC dep st cs ctx l r t
                            pure (MkECert [] (FWitness (Just sub)))
      _ => Nothing
  -- el-prf-prop: proof irrelevance — any two elements of a PROP are
  -- equal (≡-/∥·∥-headed types ARE props; a NEUTRAL prop is caught by
  -- the judgemental catch-all below)
  spEqStructC dep st cs ctx a b (Elem.EqTy _ _ _) = Just (MkECert [] FProp)
  spEqStructC dep st cs ctx a b (Squash _) = Just (MkECert [] FProp)
  -- code-prop-eq: mutually implied prop codes are equal; each direction
  -- is ⋆ with a synthesized witness under the other side's hypothesis
  spEqStructC dep st cs ctx a b PropTy = do
    (fe, fsk) <- mkImpl a b
    (be, bsk) <- mkImpl b a
    pure (MkECert [] (FPropExt fe fsk be bsk))
   where
    -- src → tgt (props are types — prop-lift), as a λ whose body is a
    -- proof of tgt[↑] under ctx ▷ src: 𝟙-shaped squashes outright,
    -- equality props by a nested discharge (which may use the
    -- hypothesis as a rewrite candidate)
    mkImpl : Elem -> Elem -> Maybe (Elem, Skel)
    mkImpl src tgt =
      let ctx' = ctx :< src in
      case engNfE st (substElem tgt Wk) of
        Squash sq => case engNfT st sq of
          OneTy => Just (lam (Nd [PSquashWit OneIntro (Nd [] [])] []))
          _ => Nothing
        Elem.EqTy l r t => do
          c <- spEqElemC dep st (mkCandSet st ctx') ctx' l r t
          Just (lam (Nd [PReflEq c] []))
        _ => Nothing
     where
      lam : Skel -> (Elem, Skel)
      lam bodySk = (PiIntro Star, Nd [] [bodySk])
  -- a NEUTRAL prop type: the judgemental question (el-prf-prop's
  -- p : Ω premise); the kernel's kIsProp re-checks at replay
  spEqStructC dep st cs ctx a b ty =
    audit "SPEQSTRUCT-NEUTRAL ty=\{show ty} isProp=\{show (isPropTy st ctx ty)} inf=\{show (kInferBare st.kernelSig kernelFuel ctx ty)}"
      (if isPropTy st ctx ty then Just (MkECert [] FProp) else Nothing)

  ||| Syntactic congruence descent: same-headed sides compared
  ||| componentwise; children flattened as path-prefixed steps.
  ||| Binder-crossing components only when no steps are needed there
  ||| (a Γ-level proof would go out of scope).
  spCongC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Maybe (List Step)
  spCongC dep st cs ctx (NatIntro1 x) (NatIntro1 y) =
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y NatTy >>= flatSteps)
  spCongC dep st cs ctx (NatElim z s t) (NatElim z' s' t') =
    if z == z' && s == s'
      then prefixSteps 2 <$> (spEqElemC dep st cs ctx t t' NatTy >>= flatSteps)
      else Nothing
  spCongC dep st cs ctx (PiApp f x) (PiApp g y) =
    if f == g
      then case neExpose st <$> inferNe st ctx f of
             Just (PiTy dom _) =>
               prefixSteps 1 <$> (spEqElemC dep st cs ctx x y dom >>= flatSteps)
             _ =>
               -- the shared head is a stuck eliminator: bare core
               -- carries no motive, so the argument's type is not
               -- inferable. Compare the arguments at an UNKNOWN type
               -- anyway — rewriting is type-blind, and the kernel
               -- validates every emitted step against its position
               -- (the neutral-subterm rule, NovaKernel.txt §6), so a
               -- wrong guess is a failed replay, never a wrong
               -- acceptance.
               prefixSteps 1 <$> (spEqElemC dep st cs ctx x y NatTy >>= flatSteps)
      else Nothing
  spCongC dep st cs ctx (SigmaElim1 u) (SigmaElim1 v) =
    case inferNe st ctx u of
      Just tyU => prefixSteps 0 <$> (spEqElemC dep st cs ctx u v tyU >>= flatSteps)
      Nothing => Nothing
  spCongC dep st cs ctx (SigmaElim2 u) (SigmaElim2 v) =
    case inferNe st ctx u of
      Just tyU => prefixSteps 0 <$> (spEqElemC dep st cs ctx u v tyU >>= flatSteps)
      Nothing => Nothing
  spCongC dep st cs ctx (QuotElim f q) (QuotElim g q') =
    if f == g
      then case inferNe st ctx q of
             Just tyQ => prefixSteps 1 <$> (spEqElemC dep st cs ctx q q' tyQ >>= flatSteps)
             _ => Nothing
      else Nothing
  spCongC dep st cs ctx (Class x) (Class y) =
    -- class-congruence: components equal (the witness route lives in
    -- spEqStructC, which is tried first)
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y NatTy >>= natFree)
   where
    -- the component type is unknown here; only proof-free evidence
    -- (pure computation) is safe to accept
    natFree : ECert -> Maybe (List Step)
    natFree c = if stepFree c then Just [] else Nothing
  spCongC dep st cs ctx (Inj1 x) (Inj1 y) =
    -- injection congruence: the component type is unknown here, so
    -- only proof-free evidence (pure computation) is safe to accept —
    -- like class above
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y NatTy >>= natFree)
   where
    natFree : ECert -> Maybe (List Step)
    natFree c = if stepFree c then Just [] else Nothing
  spCongC dep st cs ctx (Inj2 x) (Inj2 y) =
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y NatTy >>= natFree)
   where
    natFree : ECert -> Maybe (List Step)
    natFree c = if stepFree c then Just [] else Nothing
  spCongC dep st cs ctx (SumElim l r t) (SumElim l' r' t') =
    -- ⊎-elim congruence at the scrutinee (like quot-elim's)
    if l == l' && r == r'
      then case inferNe st ctx t of
             Just tyT => prefixSteps 2 <$> (spEqElemC dep st cs ctx t t' tyT >>= flatSteps)
             _ => Nothing
      else Nothing
  spCongC dep st cs ctx (Elem.PiTy a b) (Elem.PiTy a' b') = do
    stA <- spEqElemC dep st cs ctx a a' UniverseTy >>= flatSteps
    cB <- spEqElemC dep st (extendCS cs) (ctx :< a') b b' UniverseTy
    if stepFree cB then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (Elem.SigmaTy a b) (Elem.SigmaTy a' b') = do
    stA <- spEqElemC dep st cs ctx a a' UniverseTy >>= flatSteps
    cB <- spEqElemC dep st (extendCS cs) (ctx :< a') b b' UniverseTy
    if stepFree cB then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (Elem.SumTy a b) (Elem.SumTy a' b') = do
    -- non-dependent: BOTH components may carry steps (no binder to
    -- take a Γ-level proof out of scope)
    stA <- spEqElemC dep st cs ctx a a' UniverseTy >>= flatSteps
    stB <- spEqElemC dep st cs ctx b b' UniverseTy >>= flatSteps
    pure (prefixSteps 0 stA ++ prefixSteps 1 stB)
  spCongC dep st cs ctx (QuotTy a r) (QuotTy a' r') = do
    stA <- spEqElemC dep st cs ctx a a' UniverseTy >>= flatSteps
    cR <- spEqElemC dep st (extendCS (extendCS cs)) (ctx :< a' :< substTy a' Wk) r r' PropTy
    if stepFree cR then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (Squash x) (Squash y) =
    prefixSteps 0 <$> (spEqTyC dep st cs ctx x y >>= flatSteps)
  spCongC dep st cs ctx (Elem.EqTy l r t) (Elem.EqTy l' r' t') =
    -- code-eq-cong (sides only; a type-component mismatch routes
    -- through propext instead — steps cannot enter a type child here)
    if engNfT st t == engNfT st t'
      then do
        st2 <- spEqElemC dep st cs ctx l l' t' >>= flatSteps
        st3 <- spEqElemC dep st cs ctx r r' t' >>= flatSteps
        pure (prefixSteps 0 st2 ++ prefixSteps 1 st3)
      else Nothing
  spCongC _ _ _ _ _ _ = Nothing

  ||| Whole-equation matching, conditions included, hops included —
  ||| every acceptance materializes its steps.
  candMatchC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Maybe ECert
  candMatchC Z _ _ _ _ _ _ = Nothing
  candMatchC (S dep) st cs ctx a b ty =
    -- hops: only CHAIN LINKS hop (mkCandSet filters) —
    -- walking the operator's own listed adjacencies is the chain's
    -- explicit trans semantics, not search
    firstJ (map direct cs.all)
      <|> firstJ (map hop cs.hops)
   where
    firstJ : List (Maybe x) -> Maybe x
    firstJ [] = Nothing
    firstJ (Just v :: _) = Just v
    firstJ (Nothing :: rest) = firstJ rest

    noBridge : ECert -> Maybe ECert
    noBridge c@(MkECertF Nothing _ _ _) = Just c
    noBridge _ = Nothing

    paramTy : Cand -> Nat -> Maybe Ty
    paramTy c p = getAt (minus (minus c.params 1) p) c.paramTys

    hypWitness : Elem -> Elem -> Maybe Elem
    hypWitness lN rN =
      firstJ (map (\i =>
        case engNfT st <$> ctxLookup ctx i of
          Just (Elem.EqTy hl hr _) =>
            if (engNfE st hl == lN && engNfE st hr == rN)
              then Just (CtxVar i)
              else Nothing
          _ => Nothing) [0 .. minus (length ctx) 1])

    ||| A hypothesis whose (normalized) type is exactly this prop.
    hypPrfWitness : Ty -> Maybe Elem
    hypPrfWitness want =
      firstJ (map (\i =>
        case engNfT st <$> ctxLookup ctx i of
          Just h => if h == want then Just (CtxVar i) else Nothing
          Nothing => Nothing) [0 .. minus (length ctx) 1])

    ||| An element witnessing an unbound ≡-, 𝟙- or prop-typed parameter.
    condElem : Cand -> Bindings -> Nat -> Maybe Elem
    condElem c bs p =
      case lookup p bs of
        Just e => Just e
        Nothing => do
          tp <- paramTy c p
          sigma <- condSub c.params p bs
          let tpI = substTy tp sigma
          -- a hypothesis stated in the parameter's own (UNEXPOSED)
          -- spelling wins first — exposure below only classifies the
          -- shape (the retired Prf head used to keep the two apart)
          case exposeT st tpI of
            OneTy => Just OneIntro
            tpX@(Squash sq) =>
              hypPrfWitness (engNfT st tpI)
              <|> hypPrfWitness (engNfT st tpX)
              <|> (case engNfT st sq of
                     OneTy => Just Star
                     _ => Nothing)
            tpX@(Elem.EqTy l r _) =>
              hypPrfWitness (engNfT st tpI)
              <|> hypPrfWitness (engNfT st tpX)
              <|> (let lN = engNfE st l
                       rN = engNfE st r in
                   hypWitness lN rN
                   <|> (if lN == rN then Just Star else Nothing))
            -- a NEUTRAL prop-typed parameter: witnessed by a
            -- same-typed hypothesis (proof irrelevance makes the
            -- choice canonical — data-typed parameters stay unbound)
            tpX => do
              guard (isPropTy st ctx tpX)
              hypPrfWitness (engNfT st tpI)
                <|> hypPrfWitness (engNfT st tpX)

    complete : Cand -> Bindings -> Maybe Bindings
    complete c bs =
      if c.params == 0 then Just bs
      else foldl step (Just bs) (reverse [0 .. minus c.params 1])
     where
      step : Maybe Bindings -> Nat -> Maybe Bindings
      step acc p = do
        bs' <- acc
        e <- condElem c bs' p
        pure ((p, e) :: filter (\(i, _) => i /= p) bs')

    direct : Cand -> Maybe ECert
    direct c =
      (do bs <- matchElemP c.params 0 0 c.lhs a []
          bs' <- matchElemP c.params 0 0 c.rhs b bs
          full <- complete c bs'
          steps <- materialize c full True []
          pure (MkECert steps FBeta))
      <|> (do bs <- matchElemP c.params 0 0 c.lhs b []
              bs' <- matchElemP c.params 0 0 c.rhs a bs
              full <- complete c bs'
              steps <- materializeFlip c full True
              pure (MkECert steps FBeta))

    hop : Cand -> Maybe ECert
    hop c =
      (do bs <- matchElemP c.params 0 0 c.lhs a []
          full <- complete c bs
          steps <- materialize c full True []
          sigma <- instSub c.params 0 full
          let a' = engJoinE st (substElem c.rhs sigma)
          rest <- spEqElemC dep st cs ctx a' b ty >>= noBridge
          pure (MkECert (steps ++ rest.steps) rest.final))
      <|> (do bs <- matchElemP c.params 0 0 c.lhs b []
              full <- complete c bs
              steps <- materialize c full False []
              sigma <- instSub c.params 0 full
              let b' = engJoinE st (substElem c.rhs sigma)
              rest <- spEqElemC dep st cs ctx a b' ty >>= noBridge
              pure (MkECert (steps ++ rest.steps) rest.final))

  ||| Γ ⊢ A ≐ B, speculatively, with evidence.
  spEqTyC : Nat -> ElabSt -> CandSet -> Ctx -> Ty -> Ty -> Maybe ECert
  spEqTyC dep st cs ctx tyA tyB =
    -- TIER 0, as at spEqElemC
    if tyA == tyB then Just (MkECert [] FBeta) else
    -- TIER 1, as at spEqElemC
    if timed "tier1" (\_ => compTy tyA == compTy tyB) then Just (MkECert [] FBeta) else
    let t0 = nowNs ()
        (a0, aSteps) = rwNfTyS st.sig st.eqScope cs.rw True tyA
        (b0, bSteps) = rwNfTyS st.sig st.eqScope cs.rw False tyB
        -- strict: sides get HEAD exposure (logged δ at type heads);
        -- recursion through go/congFinal re-exposes per level
        a = exposeT st a0
        b = exposeT st b0
        base = bump "rwnf-ty" (nowNs () - t0) (aSteps ++ bSteps) in
    ((\rest => MkECert (base ++ rest) FBeta) <$> go a b)
      <|> congFinal a b base
      <|> codeFall a b base
   where
    -- El retired: a type equation whose sides are CODES is the 𝕌
    -- element equation (code-lift-eq / code-restrict) — delegate to
    -- the element engine, where the scope's candidates, rewriting
    -- and the injectivity selectors live. Untrusted, like everything
    -- here: the certificate replays through the shared channel.
    codeFall : Ty -> Ty -> List Step -> Maybe ECert
    codeFall a b base = do
      -- props are NOT 𝕌-codes (no prop-resize) — codeOf excludes the
      -- Ω formers; neutral props slip through and fail 𝕌-replay
      -- harmlessly
      _ <- codeOf a
      _ <- codeOf b
      MkECertF tyEx ss f unfs <- spEqElemC dep st cs ctx a b UniverseTy
      case tyEx of
        -- a bridged element certificate cannot absorb the type-side
        -- normalization steps soundly — keep only the unbridged shape
        Just _ => if null base then Just (MkECertF tyEx ss f unfs) else Nothing
        Nothing => Just (MkECertF Nothing (base ++ ss) f unfs)
    -- head-level congruence finals: extensional components (Ω-valued)
    -- cannot be flattened into steps, so prop-lift-eq / ty-quot-cong
    -- carry a nested certificate instead
    congFinal : Ty -> Ty -> List Step -> Maybe ECert
    -- ty-pi-cong / ty-sigma-cong: an Ω-valued component (a Prf
    -- codomain, say) cannot flatten into steps — carry component
    -- certificates instead
    congFinal (PiTy a0 b0) (PiTy a1 b1) base = do
      dc <- spEqTyC dep st cs ctx a0 a1
      cc <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
      pure (MkECert base (FPiCong dc cc))
    congFinal (SigmaTy a0 b0) (SigmaTy a1 b1) base = do
      dc <- spEqTyC dep st cs ctx a0 a1
      cc <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
      pure (MkECert base (FSigmaCong dc cc))
    congFinal (SumTy a0 b0) (SumTy a1 b1) base = do
      lc <- spEqTyC dep st cs ctx a0 a1
      rc <- spEqTyC dep st cs ctx b0 b1
      pure (MkECert base (FSumCong lc rc))
    congFinal (QuotTy a0 r0) (QuotTy a1 r1) base =
      if a0 == a1
        then do
          sub <- spEqElemC dep st (extendCS (extendCS cs))
                   (ctx :< a0 :< substTy a0 Wk) r0 r1 PropTy
          pure (MkECert base (FQuotCong sub))
        else Nothing
    -- prop-lift-eq (Prf retired): a type equation between PROPS is
    -- the Ω equation, where code-prop-eq's extensional discipline
    -- lives — mixed Ω-former pairs included (∥𝟙∥ ≐ a true equation).
    -- The kernel re-checks prop-ness at the FPrfCong final.
    congFinal p q base = do
      guard (isPropTy st ctx p && isPropTy st ctx q)
      sub <- spEqElemC dep st cs ctx p q PropTy
      pure (MkECert base (FPrfCong sub))
    flatE : Bool -> Nat -> Ctx -> Elem -> Elem -> Ty -> Maybe (List Step)
    flatE lhsOnly i ctx' x y t = do
      c <- spEqElemC dep st cs ctx' x y t
      steps <- flatSteps c
      if lhsOnly && any (\s => not s.onLhs) steps
        then Nothing
        else Just (prefixSteps i steps)

    go : Ty -> Ty -> Maybe (List Step)
    go a b =
      if a == b then Just [] else
      case (a, b) of
        (PiTy a0 b0, PiTy a1 b1) => do
          stA <- go a0 a1
          sub <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
          if stepFree sub then Just (prefixSteps 0 stA) else Nothing
        (SigmaTy a0 b0, SigmaTy a1 b1) => do
          stA <- go a0 a1
          sub <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
          if stepFree sub then Just (prefixSteps 0 stA) else Nothing
        (SumTy a0 b0, SumTy a1 b1) => do
          -- non-dependent: both components may carry steps
          stA <- go a0 a1
          stB <- go b0 b1
          pure (prefixSteps 0 stA ++ prefixSteps 1 stB)
        (QuotTy a0 r0, QuotTy a1 r1) => do
          stA <- go a0 a1
          sub <- spEqElemC dep st (extendCS (extendCS cs)) (ctx :< a1 :< substTy a1 Wk) r0 r1 PropTy
          if stepFree sub then Just (prefixSteps 0 stA) else Nothing
        -- prop pairs at the same Ω former flatten at Ω (Prf retired:
        -- the prop IS the type, so the steps' paths stand UNPREFIXED —
        -- there is no wrapper child to descend); mixed pairs go
        -- through congFinal
        (x@(Elem.EqTy _ _ _), y@(Elem.EqTy _ _ _)) =>
          spEqElemC dep st cs ctx x y PropTy >>= flatSteps
        (x@(Squash _), y@(Squash _)) =>
          spEqElemC dep st cs ctx x y PropTy >>= flatSteps
        -- El retired: mixed decoded-vs-code shapes no longer exist —
        -- a code in type position IS its own spelling
        _ => Nothing

||| Dedup-only matching against already-assumed obligations (dirty runs;
||| never counts as discharge).
assumedMatchE : ElabSt -> Ctx -> Elem -> Elem -> Ty -> Bool
assumedMatchE st ctx a b ty =
  let a' = rwNfElem st ctx a
      b' = rwNfElem st ctx b
      tyN = engNfT st ty
      sz = elemSize a' + elemSize b' in
  any (\(s, c, x, y, t) => s == sz && c == ctx && t == tyN && ((x == a' && y == b') || (x == b' && y == a')))
      st.assumedE

-- ===== Committing conversion (the ↓ judgements) =====

||| The number of constraint entries so far. Distinct from oblCount:
||| the decompose bookkeeping counts CONSTRAINTS only — a declaration
||| minted mid-item must not read as "children surfaced something".
constraintCountM : ElabM Nat
constraintCountM = do
  st <- getSt
  pure (length (toList st.oblMeta))

||| Record a binder occurrence's elaborated type, with the referent's
||| IMPLICIT binder positions when it is a signature reference (the
||| hover braces those — the kernel type itself carries no
||| implicitness). Nothing without a span — core-built or wildcard
||| binders.
recordBinderImps : Maybe Range -> Ctx -> NameEnv -> String -> Ty -> List Nat -> ElabM ()
recordBinderImps Nothing _ _ _ _ _ = pure ()
recordBinderImps (Just r) ctx env x ty imps = do
  st <- getSt
  modifySt $ { binderTypes $= (:< (st.modPrefix, r, ctx, env, x, ty, imps)) }

recordBinder : Maybe Range -> Ctx -> NameEnv -> String -> Ty -> ElabM ()
recordBinder mrng ctx env x ty = recordBinderImps mrng ctx env x ty []

||| The number of OPEN entries so far — constraints AND declarations:
||| either makes Σ non-definitional, so either dirties the run.
oblCount : ElabM Nat
oblCount = do
  st <- getSt
  pure (length (filter (not . sigEntryIsDef) (toList st.sig)))

||| DISPLAY resugaring: a QIIT sort (or constructor) printed through
||| the Σ entry that NAMES it. The data macro emits, per sort and
||| constructor, a def whose body is the saturated former under the
||| parameter λs — so matching each such body against the concrete
||| occurrence (first-order, the discharge engine's matcher, which
||| descends into carried signatures) recovers the instantiated
||| parameters, and the display form is the name applied to them:
||| El (Bag ℕ) instead of 𝒮{U; …}.0[]. Best effort — no hit, no harm.
resugarQ : ElabSt -> Elem -> Maybe Elem
resugarQ st occ = go (toList st.sig)
 where
  peel : Elem -> (Nat, Elem)
  peel (PiIntro f) = let (n, c) = peel f in (S n, c)
  peel e = (Z, e)

  headMatch : Elem -> Elem -> Bool
  headMatch (QSort _ kP _) (QSort _ k _) = kP == k
  headMatch (QCtor _ cP _) (QCtor _ c _) = cP == c
  -- an eliminator occurrence: the emitted def's motive/method
  -- positions are λ-binders, i.e. pure pattern variables — the
  -- Elim/ElimP twins stay disjoint because their motives are
  -- differently-typed terms (𝕌- vs Ω-valued C), never α-equal
  headMatch (QElim _ jP _ _ _ _) (QElim _ j _ _ _ _) = jP == j
  headMatch _ _ = False

  go : List SigEntry -> Maybe Elem
  go [] = Nothing
  go (SigDef [<] name body _ :: rest) =
    let (n, core) = peel body in
    if not (headMatch core occ) then go rest else
    case matchElemP n 0 0 core occ [] of
      Nothing => go rest
      Just bs =>
        case traverse (\prm => lookup prm bs)
               (the (List Nat) (if n == 0 then [] else reverse [0 .. minus n 1])) of
          Just args => Just (foldl PiApp (SigVar name [<]) args)
          Nothing => go rest
  go (_ :: rest) = go rest

-- DISPLAY normalization: reported statements, obligation sides and
-- declaration types are shown with every β-redex contracted (λ,
-- projections, eliminators at constructors, El-decoding,
-- code-squash-idem) while DEFINITIONS stay folded — δ is the one
-- contraction display never takes, so terms keep the user's names.
-- The contraction is exactly the tier-½ normalizer
-- (Nova.Elaboration.Beta), reused; on top of it, QIIT formers are
-- resugared through the Σ entries that name them (resugarQ above).
mutual
  resugarElem : ElabSt -> Elem -> Elem
  resugarElem st e@(QSort sg k es) =
    let z = QSort (map (resugarQTy st) sg) k (resugarSub st es) in
    fromMaybe z (resugarQ st z)
  resugarElem st e@(QCtor sg k es) =
    let z = QCtor (map (resugarQTy st) sg) k (resugarSub st es) in
    fromMaybe z (resugarQ st z)
  resugarElem st (QElim sg k ms fs es w) =
    QElim (map (resugarQTy st) sg) k (map (resugarTy st) ms)
          (map (resugarElem st) fs) (resugarSub st es) (resugarElem st w)
  resugarElem st (ZeroElim t) = ZeroElim (resugarElem st t)
  resugarElem st (NatIntro1 t) = NatIntro1 (resugarElem st t)
  resugarElem st (NatElim z f t) = NatElim (resugarElem st z) (resugarElem st f) (resugarElem st t)
  resugarElem st (PiIntro f) = PiIntro (resugarElem st f)
  resugarElem st (PiApp f e) = PiApp (resugarElem st f) (resugarElem st e)
  resugarElem st (Let a b) = Let (resugarElem st a) (resugarElem st b)
  resugarElem st (SigmaIntro a b) = SigmaIntro (resugarElem st a) (resugarElem st b)
  resugarElem st (SigmaElim1 t) = SigmaElim1 (resugarElem st t)
  resugarElem st (SigmaElim2 t) = SigmaElim2 (resugarElem st t)
  resugarElem st (Inj1 t) = Inj1 (resugarElem st t)
  resugarElem st (Inj2 t) = Inj2 (resugarElem st t)
  resugarElem st (SumElim l r t) = SumElim (resugarElem st l) (resugarElem st r) (resugarElem st t)
  resugarElem st (Elem.PiTy a b) = Elem.PiTy (resugarElem st a) (resugarElem st b)
  resugarElem st (Elem.SigmaTy a b) = Elem.SigmaTy (resugarElem st a) (resugarElem st b)
  resugarElem st (Elem.SumTy a b) = Elem.SumTy (resugarElem st a) (resugarElem st b)
  resugarElem st (Elem.EqTy l r t) = Elem.EqTy (resugarElem st l) (resugarElem st r) (resugarTy st t)
  resugarElem st (QuotTy a r) = QuotTy (resugarElem st a) (resugarElem st r)
  resugarElem st (Class a) = Class (resugarElem st a)
  resugarElem st (QuotElim f q) = QuotElim (resugarElem st f) (resugarElem st q)
  resugarElem st (Squash t) = Squash (resugarTy st t)
  resugarElem st (SigVar x es) =
    -- a SOLVED synthetic hole shows its value, not its name: that is
    -- the whole point of the refinement pass. `holeSols` is empty on
    -- every run without holes, and this is the display path anyway,
    -- so no elaboration ever pays for the lookup. Solutions are
    -- hole-free by construction (`refineHoles` rejects any that is
    -- not), so the recursion terminates in one step.
    case lookup x st.holeSols of
      Just t => resugarElem st (substElem t (embed es))
      Nothing => SigVar x (resugarSub st es)
  resugarElem st (Elem.NuTy f) = Elem.NuTy (resugarPoly st f)
  resugarElem st (Out t) = Out (resugarElem st t)
  resugarElem st (Corec f a g x) =
    Corec (resugarPoly st f) (resugarElem st a) (resugarElem st g) (resugarElem st x)
  resugarElem st e = e

  resugarTy : ElabSt -> Ty -> Ty
  resugarTy st (QSort sg k es) =
    let zsg = map (resugarQTy st) sg
        zes = resugarSub st es in
    case resugarQ st (QSort zsg k zes) of
      Just code => code
      Nothing => QSort zsg k zes
  resugarTy st (PiTy a b) = PiTy (resugarTy st a) (resugarTy st b)
  resugarTy st (SigmaTy a b) = SigmaTy (resugarTy st a) (resugarTy st b)
  resugarTy st (SumTy a b) = SumTy (resugarTy st a) (resugarTy st b)
  resugarTy st (QuotTy a r) = QuotTy (resugarTy st a) (resugarElem st r)
  resugarTy st (SigVar x es) =
    -- the type-position twin of the element clause above
    case lookup x st.holeSols of
      Just t => resugarTy st (substTy t (embed es))
      Nothing => SigVar x (resugarSub st es)
  resugarTy st (NuTy f) = NuTy (resugarPoly st f)
  -- a non-former type is a CODE (El retired) — resugar as an element
  resugarTy st t = resugarElem st t

  resugarSub : ElabSt -> SubNorm -> SubNorm
  resugarSub st [<] = [<]
  resugarSub st (es :< e) = resugarSub st es :< resugarElem st e

  resugarQTy : ElabSt -> QTy -> QTy
  resugarQTy st QU = QU
  resugarQTy st (QEl t) = QEl t
  resugarQTy st (QPiExt a b) = QPiExt (resugarTy st a) (resugarQTy st b)
  resugarQTy st (QPiInd u b) = QPiInd u (resugarQTy st b)

  resugarPoly : ElabSt -> Poly -> Poly
  resugarPoly st PHole = PHole
  resugarPoly st (PConst a) = PConst (resugarElem st a)
  resugarPoly st (PProd f g) = PProd (resugarPoly st f) (resugarPoly st g)
  resugarPoly st (PSum f g) = PSum (resugarPoly st f) (resugarPoly st g)
  resugarPoly st (PSigma a f) = PSigma (resugarElem st a) (resugarPoly st f)
  resugarPoly st (PPi a f) = PPi (resugarElem st a) (resugarPoly st f)

displayElem : ElabSt -> Elem -> Elem
displayElem st = resugarElem st . compElem

displayTy : ElabSt -> Ty -> Ty
displayTy st = resugarTy st . compTy

displayCtx : ElabSt -> Ctx -> Ctx
displayCtx st [<] = [<]
displayCtx st (rest :< ty) = displayCtx st rest :< displayTy st ty

displayStmt : ElabSt -> Stmt -> Stmt
displayStmt st (StElem ctx env a b ty) =
  StElem (displayCtx st ctx) env (displayElem st a) (displayElem st b) (displayTy st ty)
displayStmt st (StTy ctx env a b) =
  StTy (displayCtx st ctx) env (displayTy st a) (displayTy st b)
-- ===== Hole refinement =====
--
-- A run with holes carries constraints that SAY what its synthetic
-- holes are: `?p/imp3 ≐ x`, `?p/imp0 ≐ stream a`. Reading them back
-- turns an unhelpful `?p : ?p/imp3 ≡ ?p/imp4 ∈ ?p/imp0` into the goal
-- the operator actually faces, `?p : x ≡ y ∈ stream a`, and retires
-- the constraints that said so.
--
-- This is NOT the removed solver, and the difference is the whole
-- design (PerfNotes "The cost of a hole"). It runs ONCE, after
-- elaboration is over, at the moment a report is rendered. It reads Σ
-- and never writes it — no declaration-to-definition flip, no cache
-- invalidation, no re-attempt, no whole-item rerun. It cannot change
-- what anything elaborates to, because nothing elaborates afterwards.
-- And it cannot change ACCEPTANCE: a synthetic hole exists only
-- because a WRITTEN one does, and written holes are never solved, so
-- Σ stays non-definitional either way.

||| The shift of a spine that is the identity of a length-`n` context
||| weakened past `k` inner binders — `☐ₙ₊ₖ₋₁, …, ☐ₖ`. This is the
||| only spine shape `mintHole` produces (the identity at the hole's
||| own context) and the only one substitution then weakens it into,
||| so recognising it is recognising a solvable occurrence. Anything
||| else — a spine substitution turned it into real terms — is left
||| alone.
spineShift : (n : Nat) -> SubNorm -> Maybe Nat
spineShift n sp =
  let es = toList sp in
  if length es /= n then Nothing else
  case last' es of
    Nothing => Just 0
    Just (CtxVar k) => if es == map CtxVar (reverse [k .. k + minus n 1])
                         then Just k else Nothing
    Just _ => Nothing

||| Strengthen past `k` inner binders: the partial inverse of the
||| weakening `spineShift` measured. Fails exactly when the term
||| mentions one of them — the SCOPE check, which is what stops a
||| solution from escaping the context its hole was declared at.
strengthenBy : Nat -> Elem -> Maybe Elem
strengthenBy Z t = Just t
strengthenBy (S k) t = strengthenElem 0 t >>= strengthenBy k

||| Read one constraint side as a solution for a synthetic hole.
||| Every condition here is a restriction, and each earns its place:
||| the name must be SYNTHETIC (a written hole is the operator's
||| question); the spine must be a weakened identity (else the
||| occurrence is not a variable pattern and the solution is not
||| unique); the term must strengthen into the hole's own context
||| (scope); and it must mention no synthetic hole at all, which makes
||| the solution set trivially acyclic — so `resugarElem` expands it
||| in one step and the OCCURS check comes free with it.
trySolveSide : Sig -> (lhs : Elem) -> (rhs : Elem) -> Maybe (String, Elem)
trySolveSide sig (SigVar h sp) t =
  if not (isSyntheticHole h) then Nothing else
  case sigLookup h sig of
    Just (SigDecl dctx _ _) => do
      k <- spineShift (length dctx) sp
      t' <- strengthenBy k t
      if anySigNameE isSyntheticHole t' then Nothing else Just (h, t')
    _ => Nothing
trySolveSide _ _ _ = Nothing

||| The run's synthetic-hole solutions, read off its own constraint
||| entries. One pass: a solution's right-hand side is hole-free, so
||| substituting it can never expose a new solvable side, and a second
||| round could not find anything the first did not. First solution
||| for a name wins.
solveHoles : Sig -> List (String, Elem)
solveHoles sig = go (toList sig) []
 where
  add : List (String, Elem) -> Maybe (String, Elem) -> List (String, Elem)
  add acc Nothing = acc
  add acc (Just (h, t)) = if isJust (lookup h acc) then acc else (h, t) :: acc

  go : List SigEntry -> List (String, Elem) -> List (String, Elem)
  go [] acc = acc
  go (SigDecl ctx n (Elem.EqTy a b _) :: rest) acc =
    if not (isOblName n) then go rest acc
    else
      -- COMP-NORMALIZE both sides first, exactly as the report does
      -- before printing them. A stored side is raw: `(λ_. A) v` is
      -- what the elaborator built where the reader sees `A`, and the
      -- redex mentions the very binder the scope check must not see.
      -- Solving the term the reader is shown is also the only honest
      -- thing — the solution appears in their goals.
      let a' = compElem a
          b' = compElem b in
      go rest (add (add acc (trySolveSide sig a' b')) (trySolveSide sig b' a'))
  go (_ :: rest) acc = go rest acc

||| Install the refinement for a report. Skipped outright when the run
||| minted no hole, so an ordinary run walks Σ once and stops.
refineHoles : ElabSt -> ElabSt
refineHoles st =
  if not (any (maybe False isHoleName . sigEntryName) (toList st.sig))
    then st
    else { holeSols := solveHoles st.sig } st

||| The report view: Σ's constraint entries — the run's obligations,
||| in surfacing order — zipped with their display metadata.
oblView : ElabSt -> List Obligation
oblView st = go (toList st.sig) (toList st.oblMeta)
 where
  go : List SigEntry -> List OblMeta -> List Obligation
  go (SigDecl ctx n (Elem.EqTy a b TopTy) :: rest) (m :: ms) =
    if isOblName n
      then MkObl (displayStmt st (StTy ctx m.oenv a b)) m.osite m.ofile (map (displayStmt st) m.ocomposite) m.ohint :: go rest ms
      else go rest (m :: ms)
  go (SigDecl ctx n (Elem.EqTy a b ty) :: rest) (m :: ms) =
    if isOblName n
      then MkObl (displayStmt st (StElem ctx m.oenv a b ty)) m.osite m.ofile (map (displayStmt st) m.ocomposite) m.ohint :: go rest ms
      else go rest (m :: ms)
  go (_ :: rest) ms = go rest ms
  go [] _ = []

||| One declaration for the report: its Σ-name, context (with binder
||| names), type (Nothing for a type declaration) and declaring item.
||| PUBLIC because a hole is one of these, and in-place elimination
||| (docs/NovaElaboration.txt) reads a hole's context, type and span
||| to build the term that fills it.
public export
record DeclView where
  constructor MkDeclView
  dvname : String
  dvctx : Ctx
  dvenv : NameEnv
  dvty : Maybe Ty
  dvsite : String
  dvfile : String
  dvrange : Maybe Range

||| One hole, as a type-directed transformation needs it: its module,
||| that module's fixity table (the printer's), the view the report
||| renders — and the context with each entry's HEAD EXPOSED.
|||
||| The two contexts differ, and both are needed. A type is usually
||| WRITTEN as a definition (`bisim s t`), and its former appears only
||| after exposure, so classifying on the display form would see a
||| signature reference and offer nothing. The display form is what the
||| operator READS, so that is what gets printed back.
public export
record HoleView where
  constructor MkHoleView
  hvModule : String
  hvFix    : FixTable
  hvDecl   : DeclView
  hvCtxX   : Ctx

||| The declaration report view: Σ's declaration entries zipped with
||| their display metadata, in minting order.
declView : ElabSt -> List DeclView
declView st = mapMaybe view (toList st.sig)
 where
  metaFor : String -> Maybe DeclMeta
  metaFor x = find (\m => m.dname == x) (toList st.declMeta)
  view : SigEntry -> Maybe DeclView
  view (SigDecl ctx x TopTy) = map (\m => MkDeclView x (displayCtx st ctx) m.denv Nothing m.dsite m.dfile m.drange) (metaFor x)
  view (SigDecl ctx x ty) = map (\m => MkDeclView x (displayCtx st ctx) m.denv (Just (displayTy st ty)) m.dsite m.dfile m.drange) (metaFor x)
  view _ = Nothing

||| Σ-lemma names a certificate's steps rely on: heads of LProof
||| elements (hypothesis proofs are CtxVar-headed and contribute
||| nothing), nested certificates included. Display only.
hintNamesC : ECert -> List String
hintNamesC (MkECertF tyEx steps final _) =
  (case tyEx of
     Nothing => []
     Just (_, c) => hintNamesC c)
    ++ concatMap fromStep steps
    ++ fromFinal final
 where
  headName : Elem -> List String
  headName (PiApp f _) = headName f
  headName (SigVar x _) = [x]
  headName _ = []

  fromStep : Step -> List String
  fromStep s = case s.lic of
                 LProof e => headName e
                 LPath _ _ _ => []

  fromFinal : Final -> List String
  fromFinal (FWitness (Just c)) = hintNamesC c
  fromFinal (FInj c) = hintNamesC c
  fromFinal (FEtaPi c) = hintNamesC c
  fromFinal (FEtaSigma c1 c2) = hintNamesC c1 ++ hintNamesC c2
  fromFinal (FPrfCong c) = hintNamesC c
  fromFinal (FQuotCong c) = hintNamesC c
  fromFinal (FPiCong c1 c2) = hintNamesC c1 ++ hintNamesC c2
  fromFinal (FSigmaCong c1 c2) = hintNamesC c1 ++ hintNamesC c2
  fromFinal (FSumCong c1 c2) = hintNamesC c1 ++ hintNamesC c2
  fromFinal _ = []

mutual
  ||| Signature references of a term, accumulated — the unfold hint's
  ||| candidate pool (one traversal, no rendering).
  refsE : Elem -> SnocList String -> SnocList String
  refsE (CtxVar _) acc = acc
  refsE (ZeroElim t) acc = refsE t acc
  refsE OneIntro acc = acc
  refsE NatIntro0 acc = acc
  refsE (NatIntro1 t) acc = refsE t acc
  refsE (NatElim z s t) acc = refsE t (refsE s (refsE z acc))
  refsE (PiIntro f) acc = refsE f acc
  refsE (PiApp f e) acc = refsE e (refsE f acc)
  refsE (Let a b) acc = refsE b (refsE a acc)
  refsE (SigmaIntro a b) acc = refsE b (refsE a acc)
  refsE (SigmaElim1 t) acc = refsE t acc
  refsE (SigmaElim2 t) acc = refsE t acc
  refsE (Inj1 t) acc = refsE t acc
  refsE (Inj2 t) acc = refsE t acc
  refsE (SumElim l r t) acc = refsE t (refsE r (refsE l acc))
  refsE Elem.ZeroTy acc = acc
  refsE Elem.OneTy acc = acc
  refsE Elem.NatTy acc = acc
  refsE UniverseTy acc = acc
  refsE PropTy acc = acc
  refsE TopTy acc = acc
  refsE (Elem.PiTy a b) acc = refsE b (refsE a acc)
  refsE (Elem.SigmaTy a b) acc = refsE b (refsE a acc)
  refsE (Elem.SumTy a b) acc = refsE b (refsE a acc)
  refsE (Elem.EqTy l r t) acc = refsT t (refsE r (refsE l acc))
  refsE (QuotTy a r) acc = refsE r (refsE a acc)
  refsE (SigVar x es) acc = foldl (\a, e => refsE e a) (acc :< x) es
  refsE (Class a) acc = refsE a acc
  refsE (QuotElim f q) acc = refsE q (refsE f acc)
  refsE (Squash t) acc = refsT t acc
  refsE Star acc = acc
  refsE (QSort _ _ es) acc = foldl (\a, e => refsE e a) acc es
  refsE (QCtor _ _ es) acc = foldl (\a, e => refsE e a) acc es
  refsE (QElim _ _ ms fs es w) acc =
    refsE w (foldl (\a, e => refsE e a)
              (foldl (\a, e => refsE e a)
                (foldl (\a, t => refsT t a) acc ms) fs) es)
  refsE (Elem.NuTy _) acc = acc
  refsE (Out t) acc = refsE t acc
  refsE (Corec _ a f x) acc = refsE x (refsE f (refsE a acc))

  refsT : Ty -> SnocList String -> SnocList String
  refsT = refsE

||| The term-definition names among a collected reference pool.
defNamesOf : ElabSt -> SnocList String -> List String
defNamesOf st acc = nub (filter isDef (toList acc))
 where
  isDef : String -> Bool
  isDef x = case cachedSigLookup st.sig x of
              Just (SigDef _ _ _ _) => True
              _ => False

||| §5.4 (docs/SearchlessElaboration.md): when a SCOPED site is about
||| to assume, probe the GLOBAL store once. A discharge the kernel
||| replays becomes a hint on the obligation — search as feedback,
||| never as acceptance (the site stays assumed either way). In strict
||| mode a second stream reports the `<def>.eq` citations that would
||| close the equation.
hintE : ElabSt -> Ctx -> Elem -> Elem -> Ty -> Maybe String
hintE st ctx a b ty = lemmaHint <|> eqHint
 where
  lemmaHint : Maybe String
  lemmaHint =
    case st.scope of
      Nothing => Nothing
      Just _ =>
        let stG = { scope := Nothing } st in
        case spEqElemC spDepth stG (mkCandSet stG ctx) ctx a b ty of
          Nothing => Nothing
          Just cert =>
            case kCheckEqElem stG.sig ctx kernelFuel cert a b ty of
              Left _ => Nothing
              Right () =>
                case nub (hintNamesC cert) of
                  [] => Nothing
                  ns => Just "closes with \{joinBy ", " ns}"
  eqHint : Maybe String
  eqHint =
    go 5 (defNamesOf st (refsE b (refsE a [<])))
   where
    go : Nat -> List String -> Maybe String
    go Z ns = Nothing
    go (S k) ns =
      if null ns then Nothing else
      let a' = compElem (unfElem st.sig ns a)
          b' = compElem (unfElem st.sig ns b) in
      if a' == b'
        then Just "closes by citing \{joinBy ", " (map (++ ".eq") ns)}"
        else
          let ns' = nub (ns ++ defNamesOf st (refsE b' (refsE a' [<]))) in
          if length ns' == length ns then Nothing else go k ns'

hintT : ElabSt -> Ctx -> Ty -> Ty -> Maybe String
hintT st ctx x y = lemmaHint <|> eqHint
 where
  lemmaHint : Maybe String
  lemmaHint =
    case st.scope of
      Nothing => Nothing
      Just _ =>
        let stG = { scope := Nothing } st in
        case spEqTyC spDepth stG (mkCandSet stG ctx) ctx x y of
          Nothing => Nothing
          Just cert =>
            case kCheckEqTy stG.sig ctx kernelFuel cert x y of
              Left _ => Nothing
              Right () =>
                case nub (hintNamesC cert) of
                  [] => Nothing
                  ns => Just "closes with \{joinBy ", " ns}"
  eqHint : Maybe String
  eqHint =
    go 5 (defNamesOf st (refsT y (refsT x [<])))
   where
    go : Nat -> List String -> Maybe String
    go Z ns = Nothing
    go (S k) ns =
      if null ns then Nothing else
      let x' = compTy (unfTy st.sig ns x)
          y' = compTy (unfTy st.sig ns y) in
      if x' == y'
        then Just "closes by citing \{joinBy ", " (map (++ ".eq") ns)}"
        else
          let ns' = nub (ns ++ defNamesOf st (refsT y' (refsT x' [<]))) in
          if length ns' == length ns then Nothing else go k ns'

||| ASSUME (docs/NovaElaboration.txt, ↓ step 8): append the equation to
||| Σ as a constraint entry — sig-eq (type constraints at A = 𝕍); the signature is OPEN
||| from here until a rerun stops minting the entry — and record its
||| display metadata alongside.
assume : Stmt -> Site -> Maybe Stmt -> ElabM ()
assume stmt site comp = do
  st <- getSt
  -- inside an overload PROBE with no standing assumptions (the clean
  -- run's invariant), the record is pure counting: state is
  -- discarded, dedup cannot fire on empty lists, and neither the
  -- rewrite-normalized keys nor the hint are ever read — skip them
  let cheap = st.probing && null st.assumedE && null st.assumedT
  case stmt of
    -- an obligation enters Σ as a HOLE at the equation's prop
    -- (sig-decl; Foundation's constraint entry is retired), machine-
    -- named by the per-run counter — oblMeta stays in lockstep
    StElem ctx env a b ty => do
      if cheap
        then modifySt $ \s =>
          { sig $= (:< SigDecl ctx (oblName (length (toList s.oblMeta))) (Elem.EqTy a b ty))
          , oblMeta $= (:< MkOblMeta env site st.modFile comp Nothing) } s
        else if assumedMatchE st ctx a b ty
        then pure ()
        else modifySt $ \s =>
          let aK = rwNfElem st ctx a
              bK = rwNfElem st ctx b in
          { assumedE $= ((elemSize aK + elemSize bK, ctx, aK, bK, engNfT st ty) ::)
          , sig $= (:< SigDecl ctx (oblName (length (toList s.oblMeta))) (Elem.EqTy a b ty))
          , oblMeta $= (:< MkOblMeta env site st.modFile comp (if st.probing then Nothing else hintOf st <|> blockedHint st.sig)) } s
    StTy ctx env x y => do
      if cheap
        then modifySt $ \s =>
          { sig $= (:< SigDecl ctx (oblName (length (toList s.oblMeta))) (Elem.EqTy x y TopTy))
          , oblMeta $= (:< MkOblMeta env site st.modFile comp Nothing) } s
        else do
       let x' = rwNfTy st ctx x
       let y' = rwNfTy st ctx y
       if any (\(c, u, v) => c == ctx && ((u == x' && v == y') || (u == y' && v == x'))) st.assumedT
        then pure ()
        else modifySt $ \s =>
          { assumedT $= ((ctx, x', y') ::)
          , sig $= (:< SigDecl ctx (oblName (length (toList s.oblMeta))) (Elem.EqTy x y TopTy))
          , oblMeta $= (:< MkOblMeta env site st.modFile comp (if st.probing then Nothing else hintOf st <|> blockedHint st.sig)) } s
 where
  hintFor : ElabSt -> Stmt -> Maybe String
  hintFor st (StElem ctx _ a b ty) = hintE st ctx a b ty
  hintFor st (StTy ctx _ x y) = hintT st ctx x y

  ||| the statement's own hint, else the COMPOSITE's — a decomposed
  ||| child may be unprovable while the composite it descended from
  ||| closes wholesale (the report prints the composite alongside)
  hintOf : ElabSt -> Maybe String
  hintOf st =
    hintFor st stmt
      <|> (comp >>= \c => map ("composite " ++) (hintFor st c))
 where
  fst4 : (a, b, c, d) -> a
  fst4 (x, _, _, _) = x
  snd4 : (a, b, c, d) -> b
  snd4 (_, x, _, _) = x
  thd4 : (a, b, c, d) -> c
  thd4 (_, _, x, _) = x
  fth4 : (a, b, c, d) -> d
  fth4 (_, _, _, x) = x

mutual
  ||| One discharge attempt: engine + eager kernel replay. Right =
  ||| replayed certificate; Left = the site string, annotated when the
  ||| engine produced a certificate that failed replay (engine bug
  ||| signal, reported on the obligation).
  attemptE : Ctx -> Site -> Elem -> Elem -> Ty -> ElabM (Either Site ECert)
  attemptE ctx site a b ty =
    -- TIER 0 (↓ step 0): α-identical sides discharge by REFLEXIVITY —
    -- no candidate assembly, no engine, and no eager replay: kernel
    -- replay of the empty FBeta certificate at identical sides cannot
    -- fail (its normalizer is deterministic), and the item-level
    -- check still replays it
    if a == b
      then pure (Right (bump "syn-eq-elem" 1 (MkECert [] FBeta)))
      else do
        st <- getSt
        -- TIER 1 (↓ step ½): the sides join under the COMPUTATIONAL
        -- normaliser — every ≜ rule except definition unfolding — so
        -- the equation is trivial: no candidate assembly, no store.
        -- The eager kernel replay is KEPT here (unlike tier 0, the
        -- sides differ as written, and the replay is the canary for
        -- any engine/kernel normaliser disagreement).
        if timed "tier1" (\_ => compElem a == compElem b)
          then do
            let cert = bump "comp-eq-elem" 1 (MkECert [] FBeta)
            case kCheckEqElem st.sig ctx kernelFuel cert a b ty of
              Right () => pure (Right cert)
              Left kerrMsg => pure (Left (sub site "\{site} [replay failed: \{kerrMsg}]"))
          else do
            let t0 = nowNs ()
            let cs0 = mkCandSet st ctx
            let t1 = bump "cands" (nowNs () - t0) (nowNs ())
            let cs = bump "candN" (cast (length cs0.all)) cs0
            let tyM = bump "sz-att-in" (cast (elemSize a + elemSize b)) ty
            let tyM2 = tyM
            let mcert = map ({ unfolds := st.eqScope }) (spEqElemC (fromMaybe spDepth st.depthOv) st cs ctx a b tyM2)
            let t2 = bump "engine" (nowNs () - t1) (nowNs ())
            case mcert of
              Nothing => pure (Left site)
              Just cert =>
                let kres = kCheckEqElem st.sig ctx kernelFuel cert a b ty in
                case bump "kernel" (nowNs () - t2) kres of
                  Right () =>
                    let cert1 = if stepFree cert then bump "triv-stepless-elem" 1 cert else cert in
                    let names = nub (hintNamesC cert1) in
                    pure (Right (if null names then cert1
                                   else audit "AUDIT elem | \{st.modPrefix} | \{site} | \{joinBy ", " names}" cert1))
                  Left kerrMsg =>
                    -- the engine's route overreached (a step the
                    -- kernel's positional rules reject) — before
                    -- giving up, retry with the BARE compare-beta-
                    -- normal-forms certificate: an equation that holds
                    -- by plain δβ must not be lost to an overzealous
                    -- rewrite (this rescue lived in the removed
                    -- item-end deletion pass; it belongs at the site)
                    case kCheckEqElem st.sig ctx kernelFuel (MkECertF Nothing [] FBeta st.eqScope) a b ty of
                      Right () => pure (Right (MkECertF Nothing [] FBeta st.eqScope))
                      Left _ => pure (Left (sub site "\{site} [replay failed: \{kerrMsg}]"))

  attemptT : Ctx -> Site -> Ty -> Ty -> ElabM (Either Site ECert)
  attemptT ctx site tyA tyB =
    -- TIER 0, as at attemptE: identical types are equal by reflexivity
    if tyA == tyB
      then pure (Right (bump "syn-eq-ty" 1 (MkECert [] FBeta)))
      else do
        st <- getSt
        -- TIER 1, as at attemptE (eager replay kept — the canary)
        if timed "tier1" (\_ => compTy tyA == compTy tyB)
          then do
            let cert = bump "comp-eq-ty" 1 (MkECert [] FBeta)
            case kCheckEqTy st.sig ctx kernelFuel cert tyA tyB of
              Right () => pure (Right cert)
              Left kerrMsg => pure (Left (sub site "\{site} [replay failed: \{kerrMsg}]"))
          else do
            let t0 = nowNs ()
            let cs = mkCandSet st ctx
            let t1 = bump "cands" (nowNs () - t0) (nowNs ())
            let mcert = map ({ unfolds := st.eqScope }) (spEqTyC (fromMaybe spDepth st.depthOv) st cs ctx tyA tyB)
            let t2 = bump "engine" (nowNs () - t1) (nowNs ())
            case mcert of
              Nothing => pure (Left site)
              Just cert =>
                let kres = kCheckEqTy st.sig ctx kernelFuel cert tyA tyB in
                case bump "kernel" (nowNs () - t2) kres of
                  Right () =>
                    let names = nub (hintNamesC cert) in
                    pure (Right (if null names then cert
                                   else audit "AUDIT ty | \{st.modPrefix} | \{site} | \{joinBy ", " names}" cert))
                  Left kerrMsg =>
                    -- bare-beta rescue, as at attemptE
                    case kCheckEqTy st.sig ctx kernelFuel (MkECertF Nothing [] FBeta st.eqScope) tyA tyB of
                      Right () => pure (Right (MkECertF Nothing [] FBeta st.eqScope))
                      Left _ => pure (Left (sub site "\{site} [replay failed: \{kerrMsg}]"))

  ||| Γ ⊢ a ≐ b : A ↓ — always succeeds; assumes what it cannot discharge.
  convElem : Ctx -> NameEnv -> Site -> Maybe Stmt -> Elem -> Elem -> Ty -> ElabM (Maybe ECert)
  convElem ctx env site comp a b ty = do
    r <- attemptE ctx site a b ty
    case r of
      Right cert => pure (Just cert)
      Left site2 => do
            st <- getSt
            let cur = StElem ctx env a b ty
            let comp' = comp <|> Just cur
            -- decompose WEAK-HEAD sides first: children then keep the
            -- user's own spellings — full beta would macro-expand
            -- every definition into them. Structure that only lemma
            -- normalization exposes still decomposes: the final
            -- fallback retries with the rewritten sides.
            -- sides decompose δ-FREE (comp), keeping the user's
            -- vocabulary; the type still gets head exposure
            let aB = compElem a
            let bB = compElem b
            let a' = rwNfElem st ctx a
            let b' = rwNfElem st ctx b
            let again = if (aB, bB) == (a', b') then Nothing else Just (a', b')
            n0 <- constraintCountM
            decompose site2 cur comp' aB bB again (exposeT st ty)
            n1 <- constraintCountM
            if n1 == n0
              then do
                -- children all discharged: the composite may now hold
                -- outright — retry once before assuming it
                r3 <- attemptE ctx site a b ty
                case r3 of
                  Right cert => pure (Just cert)
                  Left site3 => do assume cur site3 comp; pure Nothing
              else pure Nothing
   where
    decompose : Site -> Stmt -> Maybe Stmt -> Elem -> Elem -> Maybe (Elem, Elem) -> Ty -> ElabM ()
    decompose site cur comp' a' b' again tyW = do
        st <- getSt
        case (a', b', tyW) of
          -- congruence decomposition — faithful (an equivalence) for
          -- the type formers and universe codes, per Foundation's
          -- injectivity rules; merely sufficient for class (quotients
          -- are not injective — the witness path is the faithful
          -- route) and for neutral-spine congruence
          (NatIntro1 x, NatIntro1 y, _) =>
            ignore $ convElem ctx env site comp' x y NatTy
          (PiIntro f, PiIntro g, PiTy dom cod) =>
            ignore $ convElem (ctx :< dom) (env :< "x") site comp' f g cod
          (SigmaIntro u v, SigmaIntro u' v', SigmaTy dom cod) => do
            ignore $ convElem ctx env site comp' u u' dom
            ignore $ convElem ctx env site comp' v v' (substTy cod (Ext Id u'))
          -- injection decomposition — faithful (injection injectivity
          -- is derivable); an inj₁/inj₂ HEAD MISMATCH falls through
          -- and stays an obligation like every rigid mismatch
          (Inj1 x, Inj1 y, SumTy dom _) =>
            ignore $ convElem ctx env site comp' x y dom
          (Inj2 x, Inj2 y, SumTy _ cod) =>
            ignore $ convElem ctx env site comp' x y cod
          (Class x, Class y, QuotTy dom rel) =>
            -- witness path: an ∥≡∥-shaped relation reduces the class
            -- equation to its underlying equation (el-quot-eq after
            -- reflection); other shapes keep the composite.
            (do st' <- getSt
                case rwNfElem st' ctx (substElem rel (Ext (Ext Id x) y)) of
                  Elem.EqTy l r t => ignore $ convElem ctx env site comp' l r t
                  _ => assume cur site comp)
          (Elem.PiTy x c, Elem.PiTy x' c', UniverseTy) => do
            ignore $ convElem ctx env site comp' x x' UniverseTy
            ignore $ convElem (ctx :< x') (env :< "x") site comp' c c' UniverseTy
          (Elem.SigmaTy x c, Elem.SigmaTy x' c', UniverseTy) => do
            ignore $ convElem ctx env site comp' x x' UniverseTy
            ignore $ convElem (ctx :< x') (env :< "x") site comp' c c' UniverseTy
          (Elem.SumTy x c, Elem.SumTy x' c', UniverseTy) => do
            -- code-sum-inj: both components at 𝕌 over Γ (no binder)
            ignore $ convElem ctx env site comp' x x' UniverseTy
            ignore $ convElem ctx env site comp' c c' UniverseTy
          (QuotTy x r, QuotTy x' r', UniverseTy) => do
            ignore $ convElem ctx env site comp' x x' UniverseTy
            ignore $ convElem (ctx :< x' :< substTy x' Wk) (env :< "x" :< "y") site comp' r r' PropTy
          -- code-qiit identity: structural, like ty-qiit (the code and
          -- the type decode to the same former)
          (QSort sg0 k0 es0, QSort sg1 k1 es1, UniverseTy) =>
            if k0 == k1 && es0 == es1
              then case qsigDom0Pieces sg0 sg1 of
                     Just pieces => traverse_ (\(t0, t1) => ignore $ convTy ctx env site comp' t0 t1) pieces
                     Nothing => assume cur site comp
              else assume cur site comp
          -- sufficient direction at Ω: equal squashees give equal props
          -- (the faithful iff route lives in spEqStructC's propext)
          (Squash tA, Squash tB, PropTy) =>
            ignore $ convTy ctx env site comp' tA tB
          -- code-eq-cong at Ω — merely sufficient (≐ at Ω is iff; the
          -- faithful route is propext)
          (Elem.EqTy l r t, Elem.EqTy l' r' t', PropTy) => do
            ignore $ convTy ctx env site comp' t t'
            ignore $ convElem ctx env site comp' l l' t'
            ignore $ convElem ctx env site comp' r r' t'
          -- ℕ-elim congruence, componentwise like the Π/Σ cases:
          -- differing components each get their own equation instead
          -- of gating on syntactic equality of the others — an
          -- equation may differ in SEVERAL components at once
          -- (vect k A ≐ vect _k _a puts one in the step and one in
          -- the target), and gating on the not-yet-solved ones
          -- deadlocks the solvable ones. z and s are typed by the
          -- constant-motive reading (the kernel's own discipline for
          -- elim equations, approximation A1); a genuinely dependent
          -- motive just fails to solve and assumes its piece.
          (NatElim z s t0, NatElim z' s' t1, tyW') => do
            when (z /= z') $
              ignore $ convElem ctx env site comp' z z' tyW'
            when (s /= s') $
              ignore $ convElem (ctx :< NatTy :< substTy tyW' Wk) (env :< "i" :< "ih")
                                site comp' s s' (substTy tyW' (wkN 2))
            when (t0 /= t1) $
              ignore $ convElem ctx env site comp' t0 t1 NatTy
          (PiApp f x, PiApp g y, _) =>
            if f == g
              then do st' <- getSt
                      case exposeT st' <$> inferNe st' ctx f of
                        Just (PiTy dom _) => ignore $ convElem ctx env site comp' x y dom
                        _ => assume cur site comp
              else assume cur site comp
          _ => case again of
                 -- the beta-normal sides matched no case: retry with
                 -- the lemma-normalized ones before assuming
                 Just (aR, bR) => decompose site cur comp' aR bR Nothing tyW
                 Nothing => assume cur site comp

  ||| Γ ⊢ A ≐ B type ↓
  convTy : Ctx -> NameEnv -> Site -> Maybe Stmt -> Ty -> Ty -> ElabM (Maybe ECert)
  convTy ctx env site comp tyA tyB = do
    r <- attemptT ctx site tyA tyB
    case r of
      Right cert => pure (Just cert)
      Left site2 => do
            st <- getSt
            let cur = StTy ctx env tyA tyB
            let comp' = comp <|> Just cur
            let aB = exposeT st tyA
            let bB = exposeT st tyB
            let aR = rwNfTy st ctx tyA
            let bR = rwNfTy st ctx tyB
            let again = if (aB, bB) == (aR, bR) then Nothing else Just (aR, bR)
            n0 <- constraintCountM
            decomposeT site2 cur comp' aB bB again
            n1 <- constraintCountM
            if n1 == n0
              then do
                r3 <- attemptT ctx site tyA tyB
                case r3 of
                  Right cert => pure (Just cert)
                  Left site3 => do assume cur site3 comp; pure Nothing
              else pure Nothing
   where
    decomposeT : Site -> Stmt -> Maybe Stmt -> Ty -> Ty -> Maybe (Ty, Ty) -> ElabM ()
    decomposeT site cur comp' tyA' tyB' again = do
        st <- getSt
        case (tyA', tyB') of
          (PiTy a0 b0, PiTy a1 b1) => do
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convTy (ctx :< a1) (env :< "x") site comp' b0 b1
          (SigmaTy a0 b0, SigmaTy a1 b1) => do
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convTy (ctx :< a1) (env :< "x") site comp' b0 b1
          (SumTy a0 b0, SumTy a1 b1) => do
            -- ty-sum-inj: both components over Γ — faithful
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convTy ctx env site comp' b0 b1
          (QuotTy a0 r0, QuotTy a1 r1) => do
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convElem (ctx :< a1 :< substTy a1 Wk) (env :< "x" :< "y") site comp' r0 r1 PropTy
          -- ty-qiit identity is STRUCTURAL (Foundation, IDENTITY):
          -- signatures, sort position, indices. Decompose the
          -- signatures' depth-0 embedded domains — instantiated
          -- parameters land there
          (QSort sg0 k0 es0, QSort sg1 k1 es1) =>
            if k0 == k1 && es0 == es1
              then case qsigDom0Pieces sg0 sg1 of
                     Just pieces => traverse_ (\(t0, t1) => ignore $ convTy ctx env site comp' t0 t1) pieces
                     Nothing => assume cur site comp
              else assume cur site comp
          -- ν identity is STRUCTURAL (Foundation, coinductive IDENTITY):
          -- same polynomial shape, embedded codes decomposed pairwise
          (NuTy f0, NuTy f1) =>
            case polyDom0Pieces f0 f1 of
              Just pieces => traverse_ (\(e0, e1) => ignore $ convElem ctx env site comp' e0 e1 UniverseTy) pieces
              Nothing => assume cur site comp
          -- prop pairs (Prf retired): decompose to the Ω equation —
          -- mixed Ω-former pairs included (propext equates them)
          (x@(Elem.EqTy _ _ _), y@(Elem.EqTy _ _ _)) => ignore $ convElem ctx env site comp' x y PropTy
          (x@(Squash _), y@(Squash _)) => ignore $ convElem ctx env site comp' x y PropTy
          (x@(Elem.EqTy _ _ _), y@(Squash _)) => ignore $ convElem ctx env site comp' x y PropTy
          (x@(Squash _), y@(Elem.EqTy _ _ _)) => ignore $ convElem ctx env site comp' x y PropTy
          _ => case again of
                 Just (aR, bR) => decomposeT site cur comp' aR bR Nothing
                 Nothing => assume cur site comp

-- ===== Bidirectional elaboration =====

||| The remedy for an INFERENCE failure, and only for one: the form
||| has no type of its own, and an ascription is exactly what puts it
||| back into checking mode. A CHECKING failure — the expected type
||| was the wrong shape — is not helped by re-ascribing the term with
||| the type that was already expected, so those say nothing here;
||| naming the type they got is the whole diagnosis (`throwShape`).
structuralHint : () -> String
structuralHint () = " — ascribe it: `(t : T)`"

||| Mint a HOLE: a sig-decl at the given context and type, with its
||| report metadata, returning the stuck reference. The entry is
||| declared at its OWN context, so the reference's spine is the
||| identity (and prints bare).
|||
||| The single place a hole enters Σ. Two callers: e-hole itself, for
||| the `?x` the operator wrote, and the shape-demanding positions,
||| for the DERIVED type holes a demanded former needs at each
||| component the position does not determine. A derived hole is
||| labelled `<hole>/<role>` — `/` cannot occur in a written label, so
||| a derived name can never collide with one.
mintHole : Ctx -> NameEnv -> Site -> Maybe Range -> (label : String) -> Ty -> ElabM Elem
mintHole ctx env site hrng label ty = do
  st <- getSt
  let item = if st.modPrefix == "" then st.curItem else "\{st.modPrefix}.\{st.curItem}"
  let q = holeName item label
  case sigLookup q st.sig of
    Just _ => throwAt (hrng <|> site.srange)
                "\{site}: duplicate hole ?\{label} — every hole of an item needs its own name"
    Nothing => pure ()
  modifySt $ { sig $= (:< SigDecl ctx q ty)
             , declMeta $= (:< MkDeclMeta q env "\{site}" st.modFile (hrng <|> site.srange)) }
  pure (SigVar q (varSpine (length ctx)))

||| The first argument of a written spine that is a HOLE, with its
||| span and label. A hole infers nothing, so a spine carrying one
||| cannot offer the implicit sources an ordinary argument would —
||| which is what makes an unsolved implicit there a hole rather than
||| an error (see `resolveArgs`).
holeArg : List SElem -> Maybe (Maybe Range, String)
holeArg [] = Nothing
holeArg (e :: rest) = case unPos e of
  SHole hrng x => Just (hrng, x)
  _ => holeArg rest

||| A SHAPE rejection: the term is well-formed, the type it met is the
||| wrong SHAPE. What that type WAS is the whole diagnosis, so these
||| say it — rendered the way the module writes it (its own fixities),
||| display-normalized like every other reported type.
throwShape : Site -> NameEnv -> (lead : String) -> Ty -> (wanted : String) -> ElabM a
throwShape site env lead ty wanted = do
  st <- getSt
  let shown = prettyTyN st.modFix env (displayTy st ty)
  -- A type that IS an undetermined part of a hole needs saying so.
  -- `?f (λx. …)`: the λ has no type of its own and `?f`'s domain has
  -- no source, so neither side can start — and "which is not a Π
  -- type" alone reads like a mistake in the term rather than a gap
  -- the operator left open.
  let note = case ty of
               SigVar h _ => if isSyntheticHole h
                               then " — \{holeLabel h} is an undetermined part of \{holeOwner h}, so nothing here fixes it: ascribe this argument, or spell \{holeOwner h}"
                               else ""
               _ => ""
  throwAt site.srange "\{site}: \{lead} \{shown}, which is not \{wanted}\{note}"

||| Annotate an item-level error with any head exposures the strict
||| whitelist blocked during the item — drained HERE, after every
||| discharge attempt has run, so ordering games inside the item
||| cannot hide them.
export
withBlockedHint : Sig -> String -> String
withBlockedHint sig err =
  case citable sig (drainBlocked ()) of
    [] => err
    ns => err ++ "\n  note: head exposure blocked for " ++ joinBy ", " ns
              ++ " — cite " ++ joinBy ", " (map (++ ".unfold") ns)

||| Attach a payload to a skeleton node.
addPayload : Payload -> Skel -> Skel
addPayload p (Nd ps cs) = Nd (p :: ps) cs

||| The certificate of a validated discharge; an assumed (dirty-run)
||| site carries an empty stub — the item is not kernel-checked then.
certOr : Maybe ECert -> ECert
certOr (Just c) = c
certOr Nothing = MkECert [] FBeta

||| Expose a type's Π/Σ/quotient head: as written if already rigid
||| (no annotation needed), else by normalization — in which case the
||| exposure ships to the kernel as a PExpose payload (exposed type +
||| conversion certificate).
exposeCert : ElabSt -> Ctx -> Ty -> Ty -> Maybe (Ty, ECert)
exposeCert st ctx ty tyX =
  -- "expose" is the head-exposure engine entry — speculative
  -- conversion OUTSIDE the committed attempts (which carry "engine").
  -- The certificate ships INSIDE the skeleton with no committed
  -- replay of its own, so it is VALIDATED here: an exposure whose
  -- steps the kernel rejects (a hypothesis rewriting under a code
  -- binder, say) must not poison the item.
  timed "expose" $ \_ =>
    let cs = mkCandSet st ctx in
    case spEqTyC spDepth st cs ctx ty tyX of
      Nothing => audit "EXPOSECERT no-cert" Nothing
      Just c0 =>
        let c = { unfolds := st.eqScope } c0 in
        case kCheckEqTy st.sig ctx kernelFuel c ty tyX of
          Right () => Just (tyX, c)
          Left err => audit "EXPOSECERT kernel-reject: \{err} [paths \{show (map (.path) c.steps)}]" Nothing

preferPi : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferPi st ctx (PiTy a b) = Just (a, b, Nothing)
preferPi st ctx ty = case exposeHead st ty of
                       tyX@(PiTy a b) => Just (a, b, Just (tyX, MkECert [] FBeta))
                       _ => case rwNfTy st ctx ty of
                              tyX@(PiTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                              _ => Nothing

preferSigma : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferSigma st ctx (SigmaTy a b) = Just (a, b, Nothing)
preferSigma st ctx ty = case exposeHead st ty of
                          tyX@(SigmaTy a b) => Just (a, b, Just (tyX, MkECert [] FBeta))
                          _ => case rwNfTy st ctx ty of
                                 tyX@(SigmaTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                                 _ => Nothing

preferSum : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferSum st ctx (SumTy a b) = Just (a, b, Nothing)
preferSum st ctx ty = case exposeHead st ty of
                        tyX@(SumTy a b) => Just (a, b, Just (tyX, MkECert [] FBeta))
                        _ => case rwNfTy st ctx ty of
                               tyX@(SumTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                               _ => Nothing

||| A prop stuck only up to hypothesis rewriting (e.g. the relator's
||| ⊎-elim at neutral observations, unstuck by a variable-definition
||| hypothesis): rewrite it and bridge with an exposure certificate
||| from the ORIGINAL expected type.
exposeProp : ElabSt -> Ctx -> Ty -> Elem -> (Elem, Maybe (Ty, ECert))
exposeProp st ctx ty p =
  let pR = rwNfElem st ctx p in
  if pR == p then audit "EXPOSEPROP no-rewrite (eqScope \{show st.eqScope})" (p, Nothing)
  else case exposeCert st ctx ty pR of
         Just e2 => (pR, Just e2)
         Nothing => audit "EXPOSEPROP bridge-fail" (p, Nothing)

preferNu : ElabSt -> Ctx -> Ty -> Maybe (Poly, Maybe (Ty, ECert))
preferNu st ctx (NuTy f) = Just (f, Nothing)
preferNu st ctx ty = case exposeHead st ty of
                       tyX@(NuTy f) => Just (f, Just (tyX, MkECert [] FBeta))
                       _ => case rwNfTy st ctx ty of
                              tyX@(NuTy f) => (\e => (f, Just e)) <$> exposeCert st ctx ty tyX
                              _ => Nothing

preferQuot : ElabSt -> Ctx -> Ty -> Maybe (Ty, Elem, Maybe (Ty, ECert))
preferQuot st ctx (QuotTy a r) = Just (a, r, Nothing)
preferQuot st ctx ty = case exposeHead st ty of
                         tyX@(QuotTy a r) => Just (a, r, Just (tyX, MkECert [] FBeta))
                         _ => case rwNfTy st ctx ty of
                                tyX@(QuotTy a r) => (\e => (a, r, Just e)) <$> exposeCert st ctx ty tyX
                                _ => Nothing

||| The expected type AS a proposition (Prf retired: the prop IS the
||| type). Syntax-directed at the Ω formers, through exposure; a
||| NEUTRAL type is a prop exactly when its kernel-inferred type is Ω
||| — with no exposure certificate, since nothing is unwrapped.
preferPrf : ElabSt -> Ctx -> Ty -> Maybe (Elem, Maybe (Ty, ECert))
preferPrf st ctx p@(Elem.EqTy _ _ _) = Just (p, Nothing)
preferPrf st ctx p@(Squash _) = Just (p, Nothing)
preferPrf st ctx ty = if kIsPropB st.kernelSig kernelFuel ctx ty
  -- a kernel-checkable Ω-neutral stays AS WRITTEN (no exposure — the
  -- callers expose for themselves exactly where a shape is needed,
  -- and downstream types keep the user's spelling)
  then Just (ty, Nothing)
  else case exposeHead st ty of
         tyX@(Elem.EqTy _ _ _) => Just (tyX, Just (tyX, MkECert [] FBeta))
         tyX@(Squash _) => Just (tyX, Just (tyX, MkECert [] FBeta))
         _ => case rwNfTy st ctx ty of
                tyX@(Elem.EqTy _ _ _) => (\e => (tyX, Just e)) <$> exposeCert st ctx ty tyX
                tyX@(Squash _) => (\e => (tyX, Just e)) <$> exposeCert st ctx ty tyX
                _ => Nothing

||| Attach a PExpose payload when exposure happened by normalization.
withExpose : Maybe (Ty, ECert) -> Skel -> Skel
withExpose Nothing sk = sk
withExpose (Just (tyX, c)) sk = addPayload (PExpose tyX c) sk

mutual
  export
  ||| Γ ⊢ F ⇝ 𝔽 poly (e-poly-*): each embedded piece a code at 𝕌, the
  ||| context growing under the binder forms; skeleton children
  ||| accumulate in binder order (the kernel's kCheckPolyK order).
  elabPoly : Ctx -> NameEnv -> Site -> SPoly -> ElabM (Poly, List Skel)
  elabPoly ctx env site SPHole = pure (PHole, [])
  elabPoly ctx env site (SPConst a) = do
    (a', aSk) <- checkElem ctx env site a UniverseTy
    pure (PConst a', [aSk])
  elabPoly ctx env site (SPProd f g) = do
    (f', fSks) <- elabPoly ctx env site f
    (g', gSks) <- elabPoly ctx env site g
    pure (PProd f' g', fSks ++ gSks)
  elabPoly ctx env site (SPSum f g) = do
    (f', fSks) <- elabPoly ctx env site f
    (g', gSks) <- elabPoly ctx env site g
    pure (PSum f' g', fSks ++ gSks)
  elabPoly ctx env site (SPSigma (xn, xr) a f) = do
    (a', aSk) <- checkElem ctx env site a UniverseTy
    recordBinder xr ctx env xn a'
    (f', fSks) <- elabPoly (ctx :< a') (env :< xn) site f
    pure (PSigma a' f', aSk :: fSks)
  elabPoly ctx env site (SPPi (xn, xr) a f) = do
    (a', aSk) <- checkElem ctx env site a UniverseTy
    recordBinder xr ctx env xn a'
    (f', fSks) <- elabPoly (ctx :< a') (env :< xn) site f
    pure (PPi a' f', aSk :: fSks)

  -- Each of the three narrows the reported site to the node's own
  -- head span before dispatching (`Nova.Elaboration.Surface.headRange`),
  -- so an error names the sub-expression it is about rather than the
  -- whole item. `*At` is the clause group; the wrapper is what
  -- everything (including the clauses, recursively) calls.
  elabTy : Ctx -> NameEnv -> Site -> STy -> ElabM (Ty, Skel)
  elabTy ctx env site t = elabTyAt ctx env (at site (headRangeTy t)) t

  elabTyAt : Ctx -> NameEnv -> Site -> STy -> ElabM (Ty, Skel)
  elabTyAt ctx env site STyZero = pure (ZeroTy, Nd [] [])
  elabTyAt ctx env site STyOne = pure (OneTy, Nd [] [])
  elabTyAt ctx env site STyNat = pure (NatTy, Nd [] [])
  elabTyAt ctx env site STyUniv = pure (UniverseTy, Nd [] [])
  elabTyAt ctx env site (STySig x0) = do
    st <- getSt
    let x = resolveSigName st x0
    case sigLookup x st.sig of
      -- items are always declared in ε, so the reference carries the
      -- empty substitution
      Just (SigDef [<] _ _ TopTy) => pure (SigVar x [<], Nd [] [])
      Just (SigDef _ _ _ TopTy) => throwAt site.srange "\{site}: '\{x}' has a non-empty declaration context"
      Just (SigDecl [<] _ TopTy) => pure (SigVar x [<], Nd [] [])
      -- CUMULATIVITY (El and Prf retired): a 𝕌- or Ω-classified
      -- reference is a code or a prop — a type either way
      Just (SigDef [<] _ _ UniverseTy) => pure (SigVar x [<], Nd [] [])
      Just (SigDecl [<] _ UniverseTy) => pure (SigVar x [<], Nd [] [])
      Just (SigDef [<] _ _ PropTy) => pure (SigVar x [<], Nd [] [])
      Just (SigDecl [<] _ PropTy) => pure (SigVar x [<], Nd [] [])
      -- anything else: elaborate as a term at the classifier the
      -- probe reads off (covers entries whose 𝕌/Ω-classification is
      -- behind a definition)
      Just _ => do
        mty <- probeM (inferElem ctx env site (SSig Nothing x))
        st2 <- getSt
        let cls = the Ty $ case mty of
                    Just (_, ty, _) => case engNfT st2 ty of
                                         PropTy => PropTy
                                         _ => UniverseTy
                    Nothing => UniverseTy
        (e', eSk) <- checkElem ctx env site (SSig Nothing x) cls
        pure (e', eSk)
      Nothing => throwAt site.srange "\{site}: unknown signature name '\{x}'"
  elabTyAt ctx env site (STyPi x a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy (ctx :< a') (env :< x) site b
    pure (PiTy a' b', Nd [] [aSk, bSk])
  -- an implicit binder elaborates exactly as an explicit one: the
  -- core is bare, implicitness is per-def METADATA (ElabSt.impls)
  elabTyAt ctx env site (STyImpPi x a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy (ctx :< a') (env :< x) site b
    pure (PiTy a' b', Nd [] [aSk, bSk])
  elabTyAt ctx env site (STySigma x a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy (ctx :< a') (env :< x) site b
    pure (SigmaTy a' b', Nd [] [aSk, bSk])
  elabTyAt ctx env site (STySum a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy ctx env site b
    pure (SumTy a' b', Nd [] [aSk, bSk])
  elabTyAt ctx env site (STyQuot a (nx, nxr) (ny, nyr) r) = do
    (a', aSk) <- elabTy ctx env site a
    recordBinder nxr ctx env nx a'
    recordBinder nyr (ctx :< a') (env :< nx) ny (substTy a' Wk)
    (r', rSk) <- checkElem (ctx :< a' :< substTy a' Wk) (env :< nx :< ny) site r PropTy
    pure (QuotTy a' r', Nd [] [aSk, rSk])
  elabTyAt ctx env site (STyNu f) = do
    -- e-ty-nu
    (f', fSks) <- elabPoly ctx env site f
    pure (NuTy f', Nd [] fSks)
  elabTyAt ctx env site (STyEq rng l r (Just t)) = do
    -- e-ty-eq: the surface ≡-TYPE IS the equality prop, standing as
    -- a type (prop-lift; equality is Ω-valued)
    (t', tSk) <- elabTy ctx env site t
    (l', lSk) <- checkElem ctx env site l t'
    (r', rSk) <- checkElem ctx env site r t'
    -- the ∈-elision trial (docs/NovaPerfectSurface.txt, Phase 4):
    -- would the elided form recover t' α-exactly by inferring a side?
    sugarTrial rng (eqElideVerdict ctx env site l r t')
    pure (Elem.EqTy l' r' t', Nd [] [lSk, rSk, tSk])
  elabTyAt ctx env site (STyEq rng l r Nothing) = do
    -- the ELIDED ≡-type: the domain is the inferred type of a side,
    -- LEFT first (a deterministic rule, not a search)
    (l', r', t', lSk, rSk) <- elabEqSides ctx env site l r
    pure (Elem.EqTy l' r' t', Nd [] [lSk, rSk, Nd [] []])
  -- a CODE in type position (El retired: the code is the type)
  -- a CODE or a PROP in type position (El and Prf retired: the code
  -- / the prop is the type). The classifier is read off a DISCARDED
  -- inference probe — Ω-formers and Ω-valued spines land at Ω,
  -- everything else (blanks included) checks at 𝕌, the overwhelmingly
  -- common classifier
  elabTyAt ctx env site (STyEl e) = do
    mty <- probeM (inferElem ctx env site e)
    st <- getSt
    let cls = the Ty $ case mty of
                Just (_, ty, _) => case engNfT st ty of
                                     PropTy => PropTy
                                     _ => UniverseTy
                Nothing => UniverseTy
    (e', eSk) <- checkElem ctx env site e cls
    pure (e', eSk)
  elabTyAt ctx env site STyProp = pure (PropTy, Nd [] [])
  -- The site is ALREADY this node's span (the wrapper installed it),
  -- so dispatch to the worker: going back through `elabTy` would
  -- re-narrow to the child's head and throw the exact span away.
  elabTyAt ctx env site (STyPos _ t) = elabTyAt ctx env site t
  export
  inferElem : Ctx -> NameEnv -> Site -> SElem -> ElabM (Elem, Ty, Skel)
  inferElem ctx env site e = inferElemAt ctx env (at site (headRange e)) e

  ||| `inferElem` at a position that DEMANDS A SHAPE — an
  ||| eliminator's scrutinee, an application's head. An ordinary term
  ||| infers as usual and the caller checks its shape as before.
  |||
  ||| A HOLE there has no type to infer, but it does not need one:
  ||| the position's own rule already fixes the type's FORMER. So the
  ||| hole is minted AT that former, with a fresh type hole standing
  ||| for each component the position leaves undetermined (e-hole,
  ||| "shape-demanding positions"). Nothing is searched for, nothing
  ||| is solved, and Σ stays monotone — the shape is READ OFF the
  ||| rule, not recovered from anything, and the components stay open
  ||| and get reported like every other hole.
  |||
  ||| The former is minted DIRECTLY rather than by refining an
  ||| unshaped hole afterwards, which is what keeps this free of the
  ||| in-place Σ mutation PerfNotes "The cost of a hole" indicts.
  inferShaped : Ctx -> NameEnv -> Site -> SElem
             -> (mkShape : (label : String) -> ElabM Ty) -> ElabM (Elem, Ty, Skel)
  inferShaped ctx env site e mkShape = case unPos e of
    SHole _ x => do
      ty <- mkShape x
      (e', sk) <- checkElem ctx env site e ty
      pure (e', ty, sk)
    _ => inferElem ctx env site e

  ||| The Π a bare `?f` is applied at: domain and codomain both open.
  piShape : Ctx -> NameEnv -> Site -> Maybe Range -> String -> ElabM Ty
  piShape ctx env site hrng x = do
    a <- mintHole ctx env site hrng "\{x}/dom" TopTy
    b <- mintHole (ctx :< a) (env :< wildcard) site hrng "\{x}/cod" TopTy
    pure (PiTy a b)

  ||| The × a bare hole is projected from.
  sigmaShape : Ctx -> NameEnv -> Site -> Maybe Range -> String -> ElabM Ty
  sigmaShape ctx env site hrng x = do
    a <- mintHole ctx env site hrng "\{x}/fst" TopTy
    b <- mintHole (ctx :< a) (env :< wildcard) site hrng "\{x}/snd" TopTy
    pure (SigmaTy a b)

  ||| The ⊎ a bare hole is eliminated at (non-dependent: no binder).
  sumShape : Ctx -> NameEnv -> Site -> Maybe Range -> String -> ElabM Ty
  sumShape ctx env site hrng x = do
    a <- mintHole ctx env site hrng "\{x}/left" TopTy
    b <- mintHole ctx env site hrng "\{x}/right" TopTy
    pure (SumTy a b)

  ||| The quotient a bare hole is eliminated at: the carrier, and the
  ||| Ω-valued relation two levels deeper (one binder per side).
  quotShape : Ctx -> NameEnv -> Site -> Maybe Range -> String -> ElabM Ty
  quotShape ctx env site hrng x = do
    a <- mintHole ctx env site hrng "\{x}/carrier" TopTy
    r <- mintHole (ctx :< a :< substTy a Wk) (env :< wildcard :< wildcard) site hrng
           "\{x}/rel" PropTy
    pure (QuotTy a r)

  ||| The ∥-∥ a bare hole is squash-eliminated at.
  squashShape : Ctx -> NameEnv -> Site -> Maybe Range -> String -> ElabM Ty
  squashShape ctx env site hrng x = do
    a <- mintHole ctx env site hrng "\{x}/squashee" TopTy
    pure (Squash a)

  inferElemAt : Ctx -> NameEnv -> Site -> SElem -> ElabM (Elem, Ty, Skel)
  inferElemAt ctx env site (SVar mrng n i) =
    case ctxLookup ctx i of
      Just ty => do
        recordBinder mrng ctx env n ty
        pure (CtxVar i, ty, Nd [] [])
      Nothing => throwAt site.srange "\{site}: variable index out of bounds"
  inferElemAt ctx env site (SSig mrng x0) = do
    st <- getSt
    let True = not (x0 `elem` st.dupNames)
      | False => throwAt site.srange "\{site}: '\{x0}' is overloaded (\{joinBy ", " (resolveSigAll st x0)}) and nothing here selects one — qualify it"
    let x = resolveSigName st x0
    -- cachedSigLookup: positive-only name index; the unknown-name
    -- error path below always re-scans (negatives are never cached)
    case cachedSigLookup st.sig x of
      Just (SigDef [<] _ _ ty) => do
        recordBinderImps mrng ctx env x0 ty (fromMaybe [] (lookup x st.impls))
        pure (SigVar x [<], ty, Nd [] [])
      Just (SigDef _ _ _ _) => throwAt site.srange "\{site}: '\{x}' has a non-empty declaration context"
      Just (SigDecl [<] _ ty) => do
        recordBinderImps mrng ctx env x0 ty (fromMaybe [] (lookup x st.impls))
        pure (SigVar x [<], ty, Nd [] [])
      Just _ => throwAt site.srange "\{site}: '\{x}' is not usable as a term here"
      Nothing => throwAt site.srange "\{site}: unknown name '\{x}'"
  inferElemAt ctx env site SUnitI = pure (OneIntro, OneTy, Nd [] [])
  inferElemAt ctx env site SZeroN = pure (NatIntro0, NatTy, Nd [] [])
  inferElemAt ctx env site (SSuc t) = do
    (t', tSk) <- checkElem ctx env site t NatTy
    pure (NatIntro1 t', NatTy, Nd [] [tSk])
  inferElemAt ctx env site sapp@(SApp f e) = do
    st <- getSt
    case overloadOf st sapp of
      Just (x0, mrng, items, cands) =>
        resolveOverload ctx env site Nothing x0 mrng items cands
      Nothing => case impSpineOf st sapp of
        Just (noIns, q, x0, mrng, items) => elabImpSpine ctx env site Nothing False noIns q x0 mrng items
        Nothing => do
          (f', fTy, fSk) <- inferShaped ctx env site f (piShape ctx env site (headRange f))
          st <- getSt
          case preferPi st ctx fTy of
            Just (a, b, _) => do
              (e', eSk) <- checkElem ctx env site e a
              pure (PiApp f' e', substTy b (Ext Id e'), Nd [] [fSk, eSk])
            Nothing => throwShape site env "cannot apply a term of type" fTy "a Π type"
  inferElemAt ctx env site (SImpArg _) =
    throwAt site.srange "\{site}: a {…} override is only legal at an implicit binder position of an applied definition"
  inferElemAt ctx env site (SBlank mrng) =
    throwAt site.srange "\{site}: a blank (_) is only legal at an explicit binder position of an applied definition — spell the term"
  inferElemAt ctx env site (SHole mrng x) =
    -- e-hole is CHECKING-ONLY: a hole is minted at the expected type,
    -- and an inference position supplies none. Nothing is guessed —
    -- the remedy is the same lever every checking-only form uses
    throwAt (mrng <|> site.srange) "\{site}: the hole ?\{x} stands where no type is expected — ascribe it: `(?\{x} : T)`"
  inferElemAt ctx env site (SNoIns e) = inferElem ctx env site e
  inferElemAt ctx env site (SPos _ e) = inferElemAt ctx env site e
  inferElemAt ctx env site (SProj1 t) = do
    (t', tTy, tSk) <- inferShaped ctx env site t (sigmaShape ctx env site (headRange t))
    st <- getSt
    case preferSigma st ctx tTy of
      Just (a, b, _) => pure (SigmaElim1 t', a, Nd [] [tSk])
      Nothing => throwShape site env "cannot project from a term of type" tTy "a × type"
  inferElemAt ctx env site (SProj2 t) = do
    (t', tTy, tSk) <- inferShaped ctx env site t (sigmaShape ctx env site (headRange t))
    st <- getSt
    case preferSigma st ctx tTy of
      Just (a, b, _) => pure (SigmaElim2 t', substTy b (Ext Id (SigmaElim1 t')), Nd [] [tSk])
      Nothing => throwShape site env "cannot project from a term of type" tTy "a × type"
  inferElemAt ctx env site (SAnn t ty) = do
    (ty', tySk) <- elabTy ctx env site ty
    (t', tSk) <- checkElem ctx env site t ty'
    pure (t', ty', addPayload (PIntroTy ty' tySk) tSk)
  inferElemAt ctx env site (SLet (x, xr) e b) = do
    -- e-let: the definiens is INFERRED (an annotated surface let
    -- arrives as an ascribed definiens); the body is elaborated under
    -- the value AND its unfolding hypothesis — an equality prop, so
    -- E's HYPOTHESIS source reflects x ≐ e into discharge
    -- automatically: the definition is transparent inside the body
    (e', eTy, eSk) <- inferElem ctx env site e
    recordBinder xr ctx env x eTy
    let hyp = Elem.EqTy (CtxVar 0) (substElem e' Wk) (substTy eTy Wk)
    (b', bTy, bSk) <- inferElem (ctx :< eTy :< hyp) (env :< x :< wildcard) site b
    pure (Let e' b', substTy bTy (Ext (Ext Id e') Star), Nd [] [eSk, bSk])
  inferElemAt ctx env site (SNatElim Nothing _ _ _ _ _) =
    throwAt site.srange "\{site}: ℕ-elim without a motive infers nothing — write (n. T), or use it in checking position"
  inferElemAt ctx env site (SSumElim Nothing _ _ _ _ _) =
    throwAt site.srange "\{site}: ⊎-elim without a motive infers nothing — write (z. T), or use it in checking position"
  inferElemAt ctx env site (SQuotElim Nothing _ _ _) =
    throwAt site.srange "\{site}: quot-elim without a motive infers nothing — write (z. T), or use it in checking position"
  inferElemAt ctx env site (SNatElim (Just ((n, nr), mot)) z (n2, n2r) (ih, ihr) s t) = do
    recordBinder nr ctx env n NatTy
    (motTy, motSk) <- elabTy (ctx :< NatTy) (env :< n) site mot
    (z', zSk) <- checkElem ctx env site z (substTy motTy (Ext Id NatIntro0))
    recordBinder n2r ctx env n2 NatTy
    recordBinder ihr (ctx :< NatTy) (env :< n2) ih motTy
    (s', sSk) <- checkElem (ctx :< NatTy :< motTy) (env :< n2 :< ih) site s
                   (substTy motTy (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
    (t', tSk) <- checkElem ctx env site t NatTy
    pure (NatElim z' s' t', substTy motTy (Ext Id t'),
          Nd [PMotive motTy motSk] [zSk, sSk, tSk])
  inferElemAt ctx env site (SSumElim (Just ((zn, zr), mot)) (an, ar) l (bn, br) r t) = do
    (t', tTy, tSk) <- inferShaped ctx env site t (sumShape ctx env site (headRange t))
    st <- getSt
    case preferSum st ctx tTy of
      Just (a, b, _) => do
        recordBinder zr ctx env zn (SumTy a b)
        (motTy, motSk) <- elabTy (ctx :< SumTy a b) (env :< zn) site mot
        recordBinder ar ctx env an a
        (l', lSk) <- checkElem (ctx :< a) (env :< an) site l
                       (substTy motTy (Ext Wk (Inj1 (CtxVar 0))))
        recordBinder br ctx env bn b
        (r', rSk) <- checkElem (ctx :< b) (env :< bn) site r
                       (substTy motTy (Ext Wk (Inj2 (CtxVar 0))))
        pure (SumElim l' r' t', substTy motTy (Ext Id t'),
              Nd [PMotive motTy motSk] [lSk, rSk, tSk])
      Nothing => throwShape site env "⊎-elim scrutinee has type" tTy "a ⊎ type"
  inferElemAt ctx env site (SQuotElim (Just ((zn, zr), mot)) (an, ar) f q) = do
    (q', qTy, qSk) <- inferShaped ctx env site q (quotShape ctx env site (headRange q))
    st <- getSt
    case preferQuot st ctx qTy of
      Just (a, r, _) => do
        recordBinder zr ctx env zn (QuotTy a r)
        (motTy, motSk) <- elabTy (ctx :< QuotTy a r) (env :< zn) site mot
        recordBinder ar ctx env an a
        (f', fSk) <- checkElem (ctx :< a) (env :< an) site f
                       (substTy motTy (Ext Wk (Class (CtxVar 0))))
        -- well-definedness: f respects R (Foundation's f⁼ premise; the
        -- hypothesis binds the relation instance directly — prop-lift).
        -- An Ω-VALUED motive closes it outright: the sides inhabit a
        -- prop instance (el-prf-prop — tested on the MOTIVE, whose
        -- spine shape survives where the stuck instance's prop-ness
        -- is unreadable)
        let wk3 = Chain Wk (Chain Wk Wk)
        st2 <- getSt
        wd <- if isPropTy st2 (ctx :< QuotTy a r) motTy
          then pure (Just (MkECert [] FProp))
          else convElem (ctx :< a :< substTy a Wk :< r) (env :< an :< (an ++ "'") :< "h")
            (sub site "\{site}: well-definedness of quot-elim case") Nothing
            (substElem f' (Ext wk3 (CtxVar 2)))
            (substElem f' (Ext wk3 (CtxVar 1)))
            (substTy motTy (Ext wk3 (Class (CtxVar 2))))
        pure (QuotElim f' q', substTy motTy (Ext Id q'),
              Nd [PMotive motTy motSk, PWD (certOr wd)] [fSk, qSk])
      Nothing => throwShape site env "quot-elim scrutinee has type" qTy "a quotient type"
  inferElemAt ctx env site SZeroC = pure (Elem.ZeroTy, UniverseTy, Nd [] [])
  inferElemAt ctx env site SOneC = pure (Elem.OneTy, UniverseTy, Nd [] [])
  inferElemAt ctx env site SNatC = pure (Elem.NatTy, UniverseTy, Nd [] [])
  inferElemAt ctx env site (SPiC x a b) = do
    (a', aSk) <- checkElem ctx env site a UniverseTy
    (b', bSk) <- checkElem (ctx :< a') (env :< x) site b UniverseTy
    pure (Elem.PiTy a' b', UniverseTy, Nd [] [aSk, bSk])
  inferElemAt ctx env site (SSigmaC x a b) = do
    (a', aSk) <- checkElem ctx env site a UniverseTy
    (b', bSk) <- checkElem (ctx :< a') (env :< x) site b UniverseTy
    pure (Elem.SigmaTy a' b', UniverseTy, Nd [] [aSk, bSk])
  inferElemAt ctx env site (SSumC a b) = do
    (a', aSk) <- checkElem ctx env site a UniverseTy
    (b', bSk) <- checkElem ctx env site b UniverseTy
    pure (Elem.SumTy a' b', UniverseTy, Nd [] [aSk, bSk])
  inferElemAt ctx env site (SQuotC a (nx, nxr) (ny, nyr) r) = do
    (a', aSk) <- checkElem ctx env site a UniverseTy
    recordBinder nxr ctx env nx a'
    recordBinder nyr (ctx :< a') (env :< nx) ny (substTy a' Wk)
    (r', rSk) <- checkElem (ctx :< a' :< substTy a' Wk) (env :< nx :< ny) site r PropTy
    pure (QuotTy a' r', UniverseTy, Nd [] [aSk, rSk])
  inferElemAt ctx env site (SSquash t) = do
    (t', tSk) <- elabTy ctx env site t
    pure (Squash t', PropTy, Nd [] [tSk])
  inferElemAt ctx env site (SStar mrng) =
    throwAt site.srange "\{site}: cannot infer the type of ⋆\{structuralHint ()}"
  inferElemAt ctx env site (SStarWit _) =
    throwAt site.srange "\{site}: cannot infer the type of ⋆ ⟨witness⟩\{structuralHint ()}"
  inferElemAt ctx env site (SStarUsing mrng _) =
    throwAt site.srange "\{site}: cannot infer the type of ⋆ using (…)\{structuralHint ()}"
  inferElemAt ctx env site (SChain _ _) =
    throwAt site.srange "\{site}: cannot infer the type of a chain (its equality comes from the expected prop)\{structuralHint ()}"
  inferElemAt ctx env site (SSquashElim _ _ _) =
    throwAt site.srange "\{site}: cannot infer the type of squash-elim\{structuralHint ()}"
  inferElemAt ctx env site (SEqC rng l r (Just t)) = do
    -- e-eq: the equality PROP — the ambient is a TYPE (large types
    -- included); there is no 𝕌-code for equality
    (t', tSk) <- elabTy ctx env site t
    (l', lSk) <- checkElem ctx env site l t'
    (r', rSk) <- checkElem ctx env site r t'
    sugarTrial rng (eqElideVerdict ctx env site l r t')
    pure (Elem.EqTy l' r' t', PropTy, Nd [] [lSk, rSk, tSk])
  inferElemAt ctx env site (SEqC rng l r Nothing) = do
    -- the elided equality prop: domain inferred from a side
    (l', r', t', lSk, rSk) <- elabEqSides ctx env site l r
    pure (Elem.EqTy l' r' t', PropTy, Nd [] [lSk, rSk, Nd [] []])
  inferElemAt ctx env site (SNuC f) = do
    -- e-code-nu
    (f', fSks) <- elabPoly ctx env site f
    pure (Elem.NuTy f', UniverseTy, Nd [] fSks)
  inferElemAt ctx env site (SOut t) = do
    -- e-out: fully inference-driven, the polynomial read off the
    -- scrutinee's type
    (t', tTy, tSk) <- inferElem ctx env site t
    st <- getSt
    case preferNu st ctx tTy of
      Just (p, _) => pure (Out t', reflectPoly p (Elem.NuTy p), Nd [] [tSk])
      Nothing => throwShape site env "out scrutinee has type" tTy "a ν type"
  inferElemAt ctx env site (SCorec _ _ _ _) =
    throwAt site.srange "\{site}: cannot infer the type of corec (the polynomial comes from the expected ν-type)\{structuralHint ()}"
  inferElemAt ctx env site (SCoind _ _ _ _ _ _ _ _) =
    throwAt site.srange "\{site}: cannot infer the type of coind (the equation comes from the expected prop)\{structuralHint ()}"
  inferElemAt ctx env site (SInj1 _) =
    throwAt site.srange "\{site}: cannot infer the type of inj₁ (the other summand is undetermined)\{structuralHint ()}"
  inferElemAt ctx env site (SInj2 _) =
    throwAt site.srange "\{site}: cannot infer the type of inj₂ (the other summand is undetermined)\{structuralHint ()}"
  inferElemAt ctx env site (SLam _ _) =
    throwAt site.srange "\{site}: cannot infer the type of a λ\{structuralHint ()}"
  inferElemAt ctx env site (SPair _ _) =
    throwAt site.srange "\{site}: cannot infer the type of a pair\{structuralHint ()}"
  inferElemAt ctx env site (SClass _) =
    throwAt site.srange "\{site}: cannot infer the type of class\{structuralHint ()}"
  inferElemAt ctx env site (SZeroElim _) =
    throwAt site.srange "\{site}: cannot infer the type of 𝟘-elim\{structuralHint ()}"

  export
  checkElem : Ctx -> NameEnv -> Site -> SElem -> Ty -> ElabM (Elem, Skel)
  checkElem ctx env site e ty = checkElemAt ctx env (at site (headRange e)) e ty

  checkElemAt : Ctx -> NameEnv -> Site -> SElem -> Ty -> ElabM (Elem, Skel)
  checkElemAt ctx env site (SHole hrng x) ty = do
    -- e-hole. The goal enters Σ as a SIG-DECL at the ambient context
    -- and the expected type — the same entry kind an obligation is
    -- (an obligation is a hole at an equation's prop), so the report,
    -- the acceptance gate (`oblCount` counts every non-definition
    -- entry) and the LSP diagnostic all come for free.
    --
    -- The hole is INERT: nothing ever solves it, nothing flips it to
    -- a definition. That is the whole design. PerfNotes "The cost of
    -- a hole" measured the SOLVER — the doomed pre-solve discharge
    -- attempt, the cache demolition on every non-monotone flip, the
    -- per-solve kernel work, the whole-item rerun — not the hole; an
    -- inert hole pays none of it, Σ still only ever extends, and a
    -- hole-free file meets not one new instruction.
    --
    -- The reference is the entry at its OWN context, so the spine is
    -- the identity (and prints bare, `?f.a` not `?f.a[…]`).
    h <- mintHole ctx env site hrng x ty
    pure (h, Nd [] [])
  checkElemAt ctx env site (SLam (x, xr) t) ty = do
    st <- getSt
    case preferPi st ctx ty of
      Just (a, b, exp) => do
        recordBinder xr ctx env x a
        (t', tSk) <- checkElem (ctx :< a) (env :< x) site t b
        pure (PiIntro t', withExpose exp (Nd [] [tSk]))
      Nothing => throwShape site env "λ checked against" ty "a Π type"
  checkElemAt ctx env site (SPair u v) ty = do
    st <- getSt
    case preferSigma st ctx ty of
      Just (a, b, exp) => do
        (u', uSk) <- checkElem ctx env site u a
        (v', vSk) <- checkElem ctx env site v (substTy b (Ext Id u'))
        pure (SigmaIntro u' v', withExpose exp (Nd [] [uSk, vSk]))
      Nothing => throwShape site env "pair checked against" ty "a × type"
  checkElemAt ctx env site (SInj1 a) ty = do
    st <- getSt
    case preferSum st ctx ty of
      Just (dom, _, exp) => do
        (a', aSk) <- checkElem ctx env site a dom
        pure (Inj1 a', withExpose exp (Nd [] [aSk]))
      Nothing => throwShape site env "inj₁ checked against" ty "a ⊎ type"
  checkElemAt ctx env site (SInj2 b) ty = do
    st <- getSt
    case preferSum st ctx ty of
      Just (_, cod, exp) => do
        (b', bSk) <- checkElem ctx env site b cod
        pure (Inj2 b', withExpose exp (Nd [] [bSk]))
      Nothing => throwShape site env "inj₂ checked against" ty "a ⊎ type"
  checkElemAt ctx env site (SCorec (xn, xr) a f u) ty = do
    -- e-corec: checking-only, like λ and class
    st <- getSt
    case preferNu st ctx ty of
      Just (p, exp) => do
        (a', aSk) <- checkElem ctx env site a UniverseTy
        recordBinder xr ctx env xn a'
        (f', fSk) <- checkElem (ctx :< a') (env :< xn) site f
                       (substTy (reflectPoly p (Elem.SumTy (Elem.NuTy p) a')) Wk)
        (u', uSk) <- checkElem ctx env site u a'
        pure (Corec p a' f' u', withExpose exp (Nd [] [aSk, fSk, uSk]))
      Nothing => throwShape site env "corec checked against" ty "a ν type"
  checkElemAt ctx env site (SCoind (xn, xr) (yn, yr) rS pS (mxn, mxr) (myn, myr) (mhn, mhr) qS) ty = do
    -- e-coind: el-nu-coind's surface form, at (l ≡ r ∈ ν F) —
    -- invariant, endpoint proof, one-step closure at the relator
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throwShape site env "coind checked against" ty "a proposition"
      Just (pc, exp) => do
        let pcUse = case pc of
                      Elem.EqTy _ _ _ => pc
                      _ => exposeCode st pc
        case pcUse of
          Elem.EqTy l rhs ety => do
            let fM = case exposeT st ety of
                       NuTy f => Just f
                       _ => case rwNfTy st ctx ety of
                              NuTy f => Just f
                              _ => Nothing
            case fM of
              Nothing => throwShape site env "coind proves an equation over" ety "a ν type"
              Just f => do
                let nuT = NuTy f
                recordBinder xr ctx env xn nuT
                recordBinder yr (ctx :< nuT) (env :< xn) yn (substTy nuT Wk)
                (r', skR) <- checkElem (ctx :< nuT :< substTy nuT Wk) (env :< xn :< yn) site rS PropTy
                (p', skp) <- checkElem ctx env site pS (substElem r' (Ext (Ext Id l) rhs))
                let ctx3 = ctx :< nuT :< substTy nuT Wk :< r'
                let wk3 = Chain Wk (Chain Wk Wk)
                let f3 = substPoly f wk3
                let r3 = substElem r' (under (under wk3))
                recordBinder mxr ctx env mxn nuT
                recordBinder myr (ctx :< nuT) (env :< mxn) myn (substTy nuT Wk)
                recordBinder mhr (ctx :< nuT :< substTy nuT Wk) (env :< mxn :< myn) mhn r'
                (q', skq) <- checkElem ctx3 (env :< mxn :< myn :< mhn) site qS
                               (liftPoly f3 (Elem.NuTy f3) r3 (Out (CtxVar 2)) (Out (CtxVar 1)))
                pure (Star, withExpose exp (Nd [PNuCoind r' skR p' skp q' skq] []))
          _ => throwShape site env "coind checked against" ty "an equality proposition"
  checkElemAt ctx env site (SClass a) ty = do
    st <- getSt
    case preferQuot st ctx ty of
      Just (dom, rel, exp) => do
        (a', aSk) <- checkElem ctx env site a dom
        pure (Class a', withExpose exp (Nd [] [aSk]))
      Nothing => throwShape site env "class checked against" ty "a quotient type"
  checkElemAt ctx env site (SZeroElim t) ty = do
    (t', tSk) <- checkElem ctx env site t ZeroTy
    pure (ZeroElim t', Nd [] [tSk])
  checkElemAt ctx env site (SStar mrng) ty = do
    -- the LSP hover for a ⋆: ascribe the PROVED PROPOSITION — the
    -- expected type at the site, display-resugared by the same
    -- table that ascribes binders
    recordBinder mrng ctx env "⋆" ty
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throwShape site env "⋆ checked against" ty "a proposition"
      Just (p, exp) => do
        -- el-eq-i / el-squash-i: an equality prop is THE payment rule
        -- (checking ⋆ emits its equation into ↓); a squashed 𝟙 is
        -- witnessed outright. Prefer the prop as written for readable
        -- obligation statements; fall back to its normal form.
        let pN = exposeCode st p
        let pUse0 = case p of
                      Elem.EqTy _ _ _ => p
                      _ => pN
        (pUse, exp) <- pure $ case pUse0 of
          Elem.EqTy _ _ _ => (pUse0, exp)
          Squash _ => (pUse0, exp)
          _ => case exposeProp st ctx ty pUse0 of
                 (pR, Just e2) => (pR, Just e2)
                 (pR, Nothing) => (pR, exp)
        case pUse of
          Elem.EqTy l r t => do
            c <- convElem ctx env (sub site "\{site}: checking ⋆") Nothing l r t
            pure (Star, withExpose exp (Nd [PReflEq (certOr c)] []))
          Squash sq =>
            case exposeHead st sq of
              OneTy => pure (Star, withExpose exp (Nd [PSquashWit OneIntro (Nd [] [])] []))
              _ => throwAt site.srange "\{site}: ⋆ can prove only equality props and 𝟙-shaped squashes automatically (write `⋆ ⟨witness⟩` to supply one directly)"
          _ => throwShape site env "⋆ checked against" ty "an evident proposition"
  -- ⋆ using (…): the SStar rule verbatim, under a discharge scope —
  -- only the named lemmas (plus hypotheses) participate, so the site
  -- is deterministic and module-local (SearchlessElaboration.md §5.3).
  -- Names resolve like any signature reference (aliases first); a name
  -- that is absent, or present but not an equation lemma of the
  -- visible store, is a structural error — it could only scope the
  -- site to nothing.
  checkElemAt ctx env site (SStarUsing mrng ns) ty = do
    (rs, eqs) <- resolveUsingNames site ns
    withScope (Just rs) (withEqScope eqs (checkElem ctx env site (SStar mrng) ty))
  -- e-chain (docs/SearchlessElaboration.md §5.2): x ≡⟨ e ⟩ y … at
  -- Prf (l ≡ r ∈ A). Midpoints check at A; each justification INFERS
  -- and must prove an equation, which becomes a site-local ground
  -- candidate (its reflected equation, exactly a hypothesis's shape).
  -- Each ADJACENCY discharges against its own link's candidate plus
  -- hypotheses — never the global store — so a failed link surfaces
  -- as its own obligation, at its own step. The COMPOSITE l ≐ r then
  -- discharges once with every link in scope and one hop of depth per
  -- link; the certificate composition (bridging, positional steps,
  -- flips) is the engine's ordinary step materialization. Erases to ⋆.
  checkElemAt ctx env site (SChain x0 links) ty = do
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throwShape site env "a chain proves an equality, but is checked against" ty "a proposition"
      Just (p, exp) => do
        let pUse = case p of
                     Elem.EqTy _ _ _ => p
                     _ => exposeCode st p
        case pUse of
          Elem.EqTy l r tA => do
            (x0', _) <- checkElem ctx env site x0 tA
            mids <- traverse (\(_, x) => map fst (checkElem ctx env site x tA)) links
            cands <- traverse (\(j, _) => linkCand j) links
            adjCerts <- adjacencies tA 1 x0'
                          (zipWith (\(_, mx), (cs, nx) => (headRange mx, cs, nx))
                                   links (zip cands mids))
            cert <- composite tA l r cands adjCerts
            pure (Star, withExpose exp (Nd [PReflEq (certOr cert)] []))
          _ => throwShape site env "chain checked against" ty "an equality proposition"
   where
    ||| a link justification, inferred and reflected into a ground
    ||| candidate (closed under component decomposition, like a
    ||| hypothesis)
    linkCand : SElem -> ElabM (List Cand)
    linkCand j = do
      (j', jTy, _) <- inferElem ctx env site j
      st <- getSt
      case exposeCode st jTy of
        Elem.EqTy u v _ =>
          pure (closeCand (MkCand "chain link" 0 []
                  (engNfE st u) (engNfE st v)
                  (\wk, _ => Just (weakenElemN wk j', [])) [] []))
        _ => throwAt site.srange "\{site}: a chain justification must prove an equation"

    ||| discharge each adjacency against ITS link only; a failure is
    ||| an ordinary obligation sited at its step (and, being scoped,
    ||| gets a global-store hint if one exists)
    adjacencies : Ty -> Nat -> Elem -> List (Maybe Range, List Cand, Elem) -> ElabM (List (Maybe ECert))
    adjacencies tA i prev [] = pure []
    adjacencies tA i prev ((rng, cs, next) :: rest) = do
      -- the step reports at ITS OWN midpoint, not at the chain
      m <- withLocal cs spDepth $
             convElem ctx env (at (sub site "\{site}: chain, step \{show i}") rng)
                      Nothing prev next tA
      ms <- adjacencies tA (S i) next rest
      pure (m :: ms)

    ||| TRANSITIVITY STITCHING of one adjacency certificate (xᵢ ≐ xᵢ₊₁,
    ||| flattenable: bridge-free steps + FBeta) into the composite's
    ||| lhs walk: the lhs steps forward (they start from nf(xᵢ), which
    ||| is where the previous segment ended), then the rhs steps
    ||| REVERSED and INVERTED — walking the common normal form back out
    ||| to xᵢ₊₁ (the flip-toggle is materialize's own inversion
    ||| discipline; the kernel re-normalizes after every step, so the
    ||| segments meet on the nose)
    stitchOne : List Step -> List Step
    stitchOne steps =
      filter (\s => s.onLhs) steps
        ++ map (\s => { flip $= not, onLhs := True } s)
               (reverse (filter (\s => not s.onLhs) steps))

    ||| the composite certificate for l ≐ r: stitch the adjacency
    ||| certificates and validate by kernel replay; when stitching is
    ||| unavailable (a failed adjacency keeps the run honest without a
    ||| second obligation; an exotic final falls back to one scoped
    ||| engine call over all the links), degrade exactly as ⋆ does
    composite : Ty -> Elem -> Elem -> List (List Cand) -> List (Maybe ECert) -> ElabM (Maybe ECert)
    composite tA l r cands adjCerts = do
      st <- getSt
      if not (all isJust adjCerts)
        then pure Nothing   -- the failed step already carries the obligation
        else do
          let stitched = map (map stitchOne . flatSteps) (catMaybes adjCerts)
          case traverse id stitched of
            Just segs =>
              let cert = MkECertF Nothing (concat segs) FBeta st.eqScope in
              case kCheckEqElem st.sig ctx kernelFuel cert l r tA of
                Right () => pure (Just cert)
                Left kerr => audit "CHAIN-COMPOSITE-FAIL \{site}: \{kerr}" fallback
            Nothing => fallback
     where
      fallback : ElabM (Maybe ECert)
      fallback =
        withLocal (concat cands) (length links + spDepth) $
          convElem ctx env (sub site "\{site}: checking chain") Nothing l r tA
  checkElemAt ctx env site (SStarWit w) ty = do
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throwShape site env "⋆ checked against" ty "a proposition"
      Just (p, exp) =>
        -- el-squash-i, general form: w proves the squashee directly,
        -- whatever its shape. At an equality prop, any proof will do
        -- (el-prf-prop): w becomes a proof license for the equation.
        let pB = exposeCode st p in
        let (pUse, exp) = the (Elem, Maybe (Ty, ECert)) $ case pB of
              Squash _ => (pB, exp)
              Elem.EqTy _ _ _ => (pB, exp)
              _ => case exposeProp st ctx ty pB of
                     (pR, Just e2) => (pR, Just e2)
                     (pR, Nothing) => (pR, exp)
        in case pUse of
          Squash sq => do
            (w', wSk) <- checkElem ctx env site w sq
            pure (Star, withExpose exp (Nd [PSquashWit w' wSk] []))
          pN@(Elem.EqTy pl pr qty) => do
            -- The two FAITHFUL routes at an equation no automatic shape
            -- reaches. code-prop-eq at Ω (e-star-propext): the witness
            -- is the PAIR of implications, each an ordinary function
            -- between the decodings. el-quot-eq at a quotient
            -- (e-star-quot-wit): the witness proves the relation at the
            -- two representatives, whatever the relation's shape.
            -- Anything else keeps the license reading — w proves this
            -- very equation.
            mcert <- case (exposeHead st qty, pl, pr, unPos w) of
              (PropTy, _, _, SPair f g) => do
                (f', fSk) <- checkElem ctx env site f (PiTy pl (substTy pr Wk))
                (g', gSk) <- checkElem ctx env site g (PiTy pr (substTy pl Wk))
                pure (Just (MkECert [] (FPropExt f' fSk g' gSk)))
              (QuotTy _ rel, Class a, Class b, _) => do
                (w', wSk) <- checkElem ctx env site w
                               (substElem rel (Ext (Ext Id a) b))
                pure (Just (MkECert [] (FWitnessPrf w' wSk)))
              _ => pure Nothing
            case mcert of
              Just cert => pure (Star, withExpose exp (Nd [PReflEq cert] []))
              Nothing => do
                (w', _) <- checkElem ctx env site w pN
                let cert = MkECertF Nothing [MkStep True [] (LProof w') [] False] FBeta st.eqScope
                pure (Star, withExpose exp (Nd [PReflEq cert] []))
          _ => throwShape site env "⋆ ⟨witness⟩ checked against" ty "an evident proposition"
  checkElemAt ctx env site (SSquashElim e xn body) ty = do
    st <- getSt
    (e', eTy, eSk) <- inferShaped ctx env site e (squashShape ctx env site (headRange e))
    case preferPrf st ctx eTy of
      Nothing => throwShape site env "squash-elim scrutinee has type" eTy "a ∥∥ proposition"
      Just (p, _) =>
        case exposeCode st p of
          Squash a =>
            -- el-squash-e-prf: body proves q[↑] under a hypothetical
            -- inhabitant of the raw squashee a; the goal must itself
            -- be a PROP — no elimination into arbitrary types
            case preferPrf st ctx ty of
              Nothing => throwShape site env "squash-elim checked against" ty "a proposition (el-squash-e-prf reaches only further propositions)"
              Just (q, exp) => do
                recordBinder (snd xn) ctx env (fst xn) a
                (body', bodySk) <- checkElem (ctx :< a) (env :< fst xn) site body (substTy q Wk)
                pure (Star, withExpose exp (Nd [PSquashElim e' eSk body' bodySk] []))
          _ => throwShape site env "squash-elim scrutinee has type" eTy "a ∥∥ proposition"
  checkElemAt ctx env site (SLet (x, xr) e b) ty = do
    -- e-let-check: let PROPAGATES the ambient mode to its body (a
    -- checking-only body form works under a let without ascription).
    -- The expected type lives over Γ, so the body checks at its double
    -- weakening — fully general, not an approximation (docs/
    -- NovaKernel.txt §8, el-let)
    (e', eTy, eSk) <- inferElem ctx env site e
    recordBinder xr ctx env x eTy
    let hyp = Elem.EqTy (CtxVar 0) (substElem e' Wk) (substTy eTy Wk)
    (b', bSk) <- checkElem (ctx :< eTy :< hyp) (env :< x :< wildcard) site b
                   (substTy (substTy ty Wk) Wk)
    pure (Let e' b', Nd [] [eSk, bSk])
  -- an implicit-headed spine in CHECKING position: the expected type
  -- is the recovery oracle's FIRST source (it must run before any
  -- argument whose domain mentions an unsolved implicit — a λ
  -- argument cannot infer); trailing implicits INSERT here (the
  -- expected type solves them; `f {}` suppresses — the
  -- function-passing form); the ordinary e-switch conversion still
  -- closes the site
  checkElemAt ctx env site sapp@(SApp _ _) ty = do
    st <- getSt
    case overloadOf st sapp of
      Just (x0, mrng, items, cands) => do
        (t', inferred, tSk) <- resolveOverload ctx env site (Just ty) x0 mrng items cands
        c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
        pure (t', addPayload (PSwitch (certOr c)) tSk)
      Nothing => case impSpineOf st sapp of
        Just (noIns, q, x0, mrng, items) => do
          (t', inferred, tSk) <- elabImpSpine ctx env site (Just ty) (not noIns) noIns q x0 mrng items
          c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
          pure (t', addPayload (PSwitch (certOr c)) tSk)
        Nothing => do
          -- the SAME node: `inferElemAt` keeps the span the site holds
          (t', inferred, tSk) <- inferElemAt ctx env site sapp
          c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
          pure (t', addPayload (PSwitch (certOr c)) tSk)
  -- a BARE reference of an implicit-binder def in checking position
  -- inserts its leading implicit run, solved from the expected type
  checkElemAt ctx env site sref@(SSig mrng x0) ty = do
    st <- getSt
    if x0 `elem` st.dupNames
      then do
        (t', inferred, tSk) <- resolveOverload ctx env site (Just ty) x0 mrng [] (resolveSigAll st x0)
        c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
        pure (t', addPayload (PSwitch (certOr c)) tSk)
      else case impSpineOf st (SApp sref SUnitI) of   -- reuse the head test
      Just (_, q, _, _, _) =>
        if maybe False (\ps => 0 `elem` ps) (lookup q st.impls)
          then do
            (t', inferred, tSk) <- elabImpSpine ctx env site (Just ty) True False q x0 mrng []
            c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
            pure (t', addPayload (PSwitch (certOr c)) tSk)
          else do
            (t', inferred, tSk) <- inferElemAt ctx env site sref
            c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
            pure (t', addPayload (PSwitch (certOr c)) tSk)
      Nothing => do
        (t', inferred, tSk) <- inferElemAt ctx env site sref
        c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
        pure (t', addPayload (PSwitch (certOr c)) tSk)
  -- {} — the NO-INSERT marker: elaborate the wrapped reference/spine
  -- without trailing insertion (implicit positions BETWEEN written
  -- arguments still recover as usual)
  checkElemAt ctx env site (SNoIns e) ty = do
    st <- getSt
    case impSpineOf st e of
      Just (_, q, x0, mrng, items) => do
        (t', inferred, tSk) <- elabImpSpine ctx env site (Just ty) False False q x0 mrng items
        c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
        pure (t', addPayload (PSwitch (certOr c)) tSk)
      Nothing => do
        (t', inferred, tSk) <- inferElem ctx env site e
        c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
        pure (t', addPayload (PSwitch (certOr c)) tSk)
  -- ELIDED-MOTIVE eliminators (docs/NovaPerfectSurface.txt, Phase
  -- 4): checking-only — the motive is recovered by ABSTRACTING the
  -- scrutinee in the expected type (absT), so instantiating it back
  -- at the scrutinee reproduces the expected type exactly and the
  -- switch is α-trivial
  checkElemAt ctx env site (SNatElim Nothing z (n2, n2r) (ih, ihr) s t) cTy = do
    (t', tSk) <- checkElem ctx env site t NatTy
    let motTy = absT 0 t' cTy
    unless (skelFreeT motTy) $
      throwAt site.srange "\{site}: the recovered motive contains a stuck eliminator — write the motive: (n. T)"
    (z', zSk) <- checkElem ctx env site z (substTy motTy (Ext Id NatIntro0))
    recordBinder n2r ctx env n2 NatTy
    recordBinder ihr (ctx :< NatTy) (env :< n2) ih motTy
    (s', sSk) <- checkElem (ctx :< NatTy :< motTy) (env :< n2 :< ih) site s
                   (substTy motTy (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
    c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing (substTy motTy (Ext Id t')) cTy
    pure (NatElim z' s' t',
          addPayload (PSwitch (certOr c)) (Nd [PMotive motTy (Nd [] [])] [zSk, sSk, tSk]))
  checkElemAt ctx env site (SSumElim Nothing (an, ar) l (bn, br) r t) cTy = do
    (t', tTy, tSk) <- inferShaped ctx env site t (sumShape ctx env site (headRange t))
    st <- getSt
    case preferSum st ctx tTy of
      Just (a, b, _) => do
        let motTy = absT 0 t' cTy
        unless (skelFreeT motTy) $
          throwAt site.srange "\{site}: the recovered motive contains a stuck eliminator — write the motive: (z. T)"
        recordBinder ar ctx env an a
        (l', lSk) <- checkElem (ctx :< a) (env :< an) site l
                       (substTy motTy (Ext Wk (Inj1 (CtxVar 0))))
        recordBinder br ctx env bn b
        (r', rSk) <- checkElem (ctx :< b) (env :< bn) site r
                       (substTy motTy (Ext Wk (Inj2 (CtxVar 0))))
        c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing (substTy motTy (Ext Id t')) cTy
        pure (SumElim l' r' t',
              addPayload (PSwitch (certOr c)) (Nd [PMotive motTy (Nd [] [])] [lSk, rSk, tSk]))
      Nothing => throwShape site env "⊎-elim scrutinee has type" tTy "a ⊎ type"
  checkElemAt ctx env site (SQuotElim Nothing (an, ar) f q) cTy = do
    (q', qTy, qSk) <- inferShaped ctx env site q (quotShape ctx env site (headRange q))
    st <- getSt
    case preferQuot st ctx qTy of
      Just (a, rel, _) => do
        let motTy = absT 0 q' cTy
        unless (skelFreeT motTy) $
          throwAt site.srange "\{site}: the recovered motive contains a stuck eliminator — write the motive: (z. T)"
        recordBinder ar ctx env an a
        (f', fSk) <- checkElem (ctx :< a) (env :< an) site f
                       (substTy motTy (Ext Wk (Class (CtxVar 0))))
        let wk3 = Chain Wk (Chain Wk Wk)
        st2 <- getSt
        wd <- if isPropTy st2 (ctx :< QuotTy a rel) motTy
          then pure (Just (MkECert [] FProp))
          else convElem (ctx :< a :< substTy a Wk :< rel) (env :< an :< (an ++ "'") :< "h")
            (sub site "\{site}: well-definedness of quot-elim case") Nothing
            (substElem f' (Ext wk3 (CtxVar 2)))
            (substElem f' (Ext wk3 (CtxVar 1)))
            (substTy motTy (Ext wk3 (Class (CtxVar 2))))
        c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing (substTy motTy (Ext Id q')) cTy
        pure (QuotElim f' q',
              addPayload (PSwitch (certOr c)) (Nd [PMotive motTy (Nd [] []), PWD (certOr wd)] [fSk, qSk]))
      Nothing => throwShape site env "quot-elim scrutinee has type" qTy "a quotient type"
  -- as in `elabTyAt`: the site is already this node's own span
  checkElemAt ctx env site (SPos _ e) ty = checkElemAt ctx env site e ty
  -- `inferElemAt`, not `inferElem`: this is the SAME node, whose span
  -- the site already holds. Re-entering through the wrapper would
  -- re-derive a span from the node's head and report the application
  -- at its function, the projection at its scrutinee.
  checkElemAt ctx env site t ty = do
    (t', inferred, tSk) <- inferElemAt ctx env site t
    motiveTrial ctx env site t t' tSk ty
    c <- convTy ctx env (sub site "\{site}: inferred vs expected type") Nothing inferred ty
    pure (t', addPayload (PSwitch (certOr c)) tSk)

  ||| Record the sugar trial's verdict at a ranged site (Phase 4).
  sugarTrial : Maybe Range -> ElabM Bool -> ElabM ()
  sugarTrial mrng verdict = do
    st <- getSt
    when st.svSugarOn $ case mrng of
      Nothing => pure ()
      Just rng => do
        v <- verdict
        modifySt $ { svSugar $= (:< (st.modPrefix, rng, v)) }

  ||| Would the elided ≡ recover the written domain α-exactly?
  ||| Mirrors elabEqSides exactly: the left side first.
  eqElideVerdict : Ctx -> NameEnv -> Site -> SElem -> SElem -> Ty -> ElabM Bool
  eqElideVerdict ctx env site l r t' =
    if sInferForm l
      then do res <- probeM (inferElem ctx env site l)
              pure (case res of
                      Just (_, lTy, _) => show lTy == show t' && skelFreeT lTy
                      Nothing => False)
      else if sInferForm r
        then do res <- probeM (inferElem ctx env site r)
                pure (case res of
                        Just (_, rTy, _) => show rTy == show t' && skelFreeT rTy
                        Nothing => False)
        else pure False

  ||| The elided ≡'s sides: the domain is the inferred type of the
  ||| LEFT side (right as fallback when the left is an intro form) —
  ||| a deterministic rule, not a search. Both sides intro is a
  ||| structural error whose remedy is the ∈-annotation.
  elabEqSides : Ctx -> NameEnv -> Site -> SElem -> SElem -> ElabM (Elem, Elem, Ty, Skel, Skel)
  elabEqSides ctx env site l r =
    if sInferForm l
      then do
        (l', t', lSk) <- inferElem ctx env site l
        unless (skelFreeT t') $
          throwAt site.srange "\{site}: the inferred equality domain contains a stuck eliminator — annotate it: l ≡ r ∈ T"
        (r', rSk) <- checkElem ctx env site r t'
        pure (l', r', t', lSk, rSk)
      else if sInferForm r
        then do
          (r', t', rSk) <- inferElem ctx env site r
          unless (skelFreeT t') $
            throwAt site.srange "\{site}: the inferred equality domain contains a stuck eliminator — annotate it: l ≡ r ∈ T"
          (l', lSk) <- checkElem ctx env site l t'
          pure (l', r', t', lSk, rSk)
        else throwAt site.srange "\{site}: cannot infer the equality's domain — annotate it: l ≡ r ∈ T"

  ||| The MOTIVE trial: at a checking-position eliminator with a
  ||| written motive, record whether abstracting the scrutinee in the
  ||| expected type reproduces it α-exactly.
  motiveTrial : Ctx -> NameEnv -> Site -> SElem -> Elem -> Skel -> Ty -> ElabM ()
  motiveTrial ctx env site surf core sk cTy = do
    st <- getSt
    when st.svSugarOn $ case (motRangeOf surf, motPayload sk, scrutOf core) of
      (Just rng, Just motTy, Just scrut) =>
        modifySt $ { svSugar $= (:< (st.modPrefix, rng,
                                     show (absT 0 scrut cTy) == show motTy
                                       && skelFreeT motTy)) }
      _ => pure ()
   where
    motRangeOf : SElem -> Maybe Range
    motRangeOf (SNatElim (Just ((_, mr), _)) _ _ _ _ _) = mr
    motRangeOf (SSumElim (Just ((_, mr), _)) _ _ _ _ _) = mr
    motRangeOf (SQuotElim (Just ((_, mr), _)) _ _ _) = mr
    motRangeOf _ = Nothing

    motPayload : Skel -> Maybe Ty
    motPayload (Nd ps _) =
      head' (mapMaybe (\pl => case pl of
                         PMotive m _ => Just m
                         _ => Nothing) ps)

    scrutOf : Elem -> Maybe Elem
    scrutOf (NatElim _ _ t) = Just t
    scrutOf (SumElim _ _ t) = Just t
    scrutOf (QuotElim _ q) = Just q
    scrutOf _ = Nothing

  ||| The OVERLOAD view: the whole application chain, when its head
  ||| is a surface name visible with several distinct Σ targets.
  ||| Guarded by `null st.dupNames` first — a run without overloads
  ||| pays one comparison per application node.
  overloadOf : ElabSt -> SElem -> Maybe (String, Maybe Range, List SElem, List String)
  overloadOf st e =
    if null st.dupNames then Nothing else
      case unPos e of
        SApp _ _ =>
          let (h, items) = surfSpine e [] in
          case h of
            SSig mrng x0 =>
              if x0 `elem` st.dupNames
                then Just (x0, mrng, items, resolveSigAll st x0)
                else Nothing
            _ => Nothing
        _ => Nothing
   where
    -- spine arguments are inspected by SHAPE all through the
    -- implicit machinery (a blank, a {…} override, an ordinary
    -- term), so the walk hands back BARE nodes. No position is lost:
    -- an argument keeps the spans of its own children, which is what
    -- `checkElem` narrows to when it elaborates one.
    surfSpine : SElem -> List SElem -> (SElem, List SElem)
    surfSpine e acc = case unPos e of
      SApp f a => surfSpine f (unPos a :: acc)
      h => (h, acc)

  ||| TYPE-DIRECTED overload resolution (docs/NovaPerfectSurface.txt,
  ||| Phase 4): probe each candidate — the whole spine, isolated and
  ||| state-discarded — and demand that the winner elaborate with
  ||| ZERO NEW OBLIGATIONS (the ↓ judgements never fail, so plain
  ||| success cannot discriminate: a wrong candidate would simply
  ||| assume absurd equations). Exactly one clean fit commits and
  ||| re-elaborates for real; none or several is a structural error
  ||| whose remedy is qualification (the mention form (M.op), or
  ||| opening only one candidate).
  resolveOverload : Ctx -> NameEnv -> Site -> Maybe Ty -> (x0 : String) ->
                    Maybe Range -> List SElem -> List String -> ElabM (Elem, Ty, Skel)
  resolveOverload ctx env site mexp x0 mrng items cands0 = do
    -- pre-elaborate the INFERENCE-FORM arguments once — candidates
    -- are then tried on TYPES alone and the winner reuses the work,
    -- so nested overloaded spines stay LINEAR (probing whole
    -- argument subtrees per candidate would be exponential in
    -- nesting depth). Intro-form arguments and overrides defer to
    -- the winner (their elaboration needs its domains).
    pres <- traverse (\it => case it of
              SImpArg _ => pure Nothing
              _ => if sInferForm it
                     then map Just (asArg (inferElem ctx env site it))
                     else pure Nothing) items
    let cands = nub cands0
    -- STAGE 1, the quick filter: match the pre-elaborated argument
    -- types against each candidate's domains (α, δ-free comp, the
    -- site's licensed join — the matcher, no engine machinery). A
    -- unique survivor commits directly — the real run's own
    -- conversions still verify it. STAGE 2 (ties, or an empty
    -- filter): the obligation-free conversion probes.
    st <- getSt
    let jn = \t => compTy (unfTy st.sig st.eqScope t)
    let quick = filter (quickFit st jn pres) cands
    case quick of
      [q] => run pres q
      survivors => do
        let pool = case survivors of
                     [] => cands
                     _ => survivors
        verdicts <- traverse (\q => map (\v => (q, v)) (probeFit pres q)) pool
        let fits = map fst (filter (\(_, v) => v == Just 0) verdicts)
        case fits of
          [q] => run pres q
          [] => throw ("\{site}: no visible '\{x0}' fits here without assumptions " ++
                       "(candidates: \{joinBy ", " cands}) — qualify one, e.g. the mention form")
          qs => throw ("\{site}: '\{x0}' is ambiguous here — \{joinBy ", " qs} all fit; " ++
                       "qualify one, e.g. the mention form")
   where
    matches3 : (Ty -> Ty) -> Ty -> Ty -> Bool
    matches3 jn pat g =
      isJust (mTy 0 pat g []) ||
      isJust (mTy 0 (compTy pat) (compTy g) []) ||
      isJust (mTy 0 (jn pat) (jn g) [])

    argsMatch : (Ty -> Ty) -> List Ty -> List (Maybe (Elem, Ty, Skel)) -> Bool
    argsMatch jn doms pres = go 0 doms pres
     where
      go : Nat -> List Ty -> List (Maybe (Elem, Ty, Skel)) -> Bool
      go i _ [] = True
      go i [] _ = True
      go i (d :: ds) (p :: ps) =
        let pat = substTy d (prefixSub (map (\k => holeE (2000000 + k)) [0 .. i]))
            ok = case p of
                   Nothing => True
                   Just (_, ty, _) => matches3 jn pat ty
        in ok && go (S i) ds ps

    quickFit : ElabSt -> (Ty -> Ty) -> List (Maybe (Elem, Ty, Skel)) -> String -> Bool
    quickFit st jn pres q =
      case cachedSigLookup st.sig q of
        Just (SigDef [<] _ _ ty) => argsMatch jn (fst (teleOf ty)) pres
        Just (SigDecl [<] _ ty) => argsMatch jn (fst (teleOf ty)) pres
        _ => True   -- let the conversion probes judge the unusual


    run : List (Maybe (Elem, Ty, Skel)) -> String -> ElabM (Elem, Ty, Skel)
    run pres q = elabImpSpineP pres ctx env site mexp (isJust mexp) False q x0 mrng items

    probeFit : List (Maybe (Elem, Ty, Skel)) -> String -> ElabM (Maybe Nat)
    probeFit pres q = probeM $ do
      -- CONSTRAINTS, not every open entry: the question is whether
      -- this candidate fits without ASSUMING an equation. A hole the
      -- operator wrote inside the spine is not evidence against any
      -- candidate — counting it would make every branch look unclean
      -- and turn `1 + ?x` into a bogus ambiguity error
      before <- constraintCountM
      (_, ty', _) <- run pres q
      case mexp of
        Just c => ignore (convTy ctx env (sub site "\{site}: overload fit") Nothing ty' c)
        Nothing => pure ()
      after <- constraintCountM
      pure (minus after before)

  ||| The implicit-spine view: the whole application chain, when its
  ||| head is a signature reference whose def carries implicit binder
  ||| positions. Guarded by `null st.impls` first, so an implicit-free
  ||| run pays one boolean per application node.
  impSpineOf : ElabSt -> SElem -> Maybe (Bool, String, String, Maybe Range, List SElem)
  impSpineOf st e =
    let (h, items) = surfSpine e [] in
    case h of
      SSig mrng x0 =>
        let q = resolveSigName st x0 in
        case lookup q st.impls of
          Just (_ :: _) => Just (False, q, x0, mrng, items)
          -- a BLANK routes the spine here even without implicit
          -- binders — `_` is solved by the same oracle, from the
          -- same telescope. So does EVERY Σ-headed spine during the
          -- sugar pass: the blank-emission trial needs the
          -- telescope view (the spine elaborator produces the same
          -- core and the same skeleton shape as the generic rule).
          -- ORDINARY telescopes only: a QIIT constructor's type
          -- carries QSort-internal Π-structure that teleOf cannot
          -- split and the matcher cannot see through (its relation
          -- to the surface-level PiApp form is conversion, not α) —
          -- those spines stay on the generic rule, blankless
          _ => if (any isBlankArg items || st.svSugarOn) && ordinaryHead st q
                 then Just (False, q, x0, mrng, items)
                 else Nothing
      -- an APPLIED no-insert head — `f {} a b …` — is POSITIONAL
      -- application over the FULL telescope: insertion is off, every
      -- position is explicit, and a blank may stand at any of them,
      -- solved by the same oracle (the manual-implicitization form:
      -- homAp {} _ g _ (qIsGroup …) qProj a)
      SNoIns h2 => case unPos h2 of
        SSig mrng x0 =>
          let q = resolveSigName st x0 in
          if (any isBlankArg items || st.svSugarOn) && ordinaryHead st q
            then Just (True, q, x0, mrng, items)
            else Nothing
        _ => Nothing
      _ => Nothing
   where
    isBlankArg : SElem -> Bool
    isBlankArg e = case unPos e of
      SBlank _ => True
      _ => False

    isQSort : Ty -> Bool
    isQSort (QSort _ _ _) = True
    isQSort _ = False

    ordinaryHead : ElabSt -> String -> Bool
    ordinaryHead st q = case cachedSigLookup st.sig q of
      Just (SigDef [<] _ _ ty) => let (doms, res) = teleOf ty in
                                  not (any isQSort (res :: doms))
      Just (SigDecl [<] _ ty) => let (doms, res) = teleOf ty in
                                 not (any isQSort (res :: doms))
      _ => False

    -- bare nodes out, as in `overloadOf` above
    surfSpine : SElem -> List SElem -> (SElem, List SElem)
    surfSpine e acc = case unPos e of
      SApp f a => surfSpine f (unPos a :: acc)
      h => (h, acc)

  ||| Elaborate an application spine of an implicit-binder definition
  ||| (docs/NovaPerfectSurface.txt, Phase 3): implicit positions up to
  ||| the last written argument are INSERTED and solved by the rigid
  ||| first-order oracle — sources are the expected type (when given)
  ||| and the inferred types of explicit inference-form arguments —
  ||| in ONE deterministic pass: no metavariable ever reaches a
  ||| conversion site, no state survives the spine, Σ is never
  ||| touched. An unsolved position is a STRUCTURAL error naming the
  ||| remedy ({…}). Matching is syntactic first, then both sides
  ||| under the δ-free computational normalizer — never the store.
  elabImpSpine : Ctx -> NameEnv -> Site -> Maybe Ty -> (insertTrailing : Bool) ->
                 (noIns : Bool) ->
                 (q : String) -> (x0 : String) -> Maybe Range -> List SElem ->
                 ElabM (Elem, Ty, Skel)
  elabImpSpine = elabImpSpineP []

  ||| elabImpSpine with PRE-ELABORATED arguments (overload
  ||| resolution): `pres` aligns with the written items — a Just is
  ||| an argument already elaborated once at the site, consumed by
  ||| the walk instead of re-elaborating.
  elabImpSpineP : List (Maybe (Elem, Ty, Skel)) ->
                 Ctx -> NameEnv -> Site -> Maybe Ty -> (insertTrailing : Bool) ->
                 (noIns : Bool) ->
                 (q : String) -> (x0 : String) -> Maybe Range -> List SElem ->
                 ElabM (Elem, Ty, Skel)
  elabImpSpineP presIn ctx env site mexp insertTrailing noIns q x0 mrng items = do
    st <- getSt
    defTy <- case cachedSigLookup st.sig q of
      Just (SigDef [<] _ _ ty) => pure ty
      Just (SigDecl [<] _ ty) => pure ty
      Just _ => throwAt site.srange "\{site}: '\{q}' is not usable as a term here"
      Nothing => throwAt site.srange "\{site}: unknown name '\{q}'"
    let imps = if noIns then [] else fromMaybe [] (lookup q st.impls)
    recordBinderImps mrng ctx env x0 defTy imps
    -- the site's LICENSED JOIN (comp ∘ unfold[cited]) — recovery's
    -- third matching tier (docs/NovaPerfectSurface.txt, Phase 3d):
    -- sees through definitional scaffolding the site itself licensed;
    -- captured bindings are still α-verified downstream, so value
    -- spelling drift keeps getting rejected
    let jn = \t => compTy (unfTy st.sig st.eqScope t)
    let (doms, res) = teleOf defTy
    (slots, leftover) <- assign imps 0 doms items
    let m = length slots
    let tailTy = rebuildTail (drop m doms) res
    -- source 1: the expected type (throwaway holes stand at written
    -- positions — their bindings are discarded by position)
    let patArgs = map (\(i, mt) => case mt of
                                     Nothing => holeE i
                                     -- a written BLANK is a hole here too: its
                                     -- binding from the expected type must
                                     -- SURVIVE (throwaway holes are for written
                                     -- arguments, whose bindings are discarded
                                     -- by position)
                                     Just (SBlank _) => holeE i
                                     Just _ => holeE (throwaway + i)) slots
    let blankPoss = mapMaybe (\(pos, mt) => case mt of
                       Just (SBlank _) => Just pos
                       _ => Nothing) slots
    let (sols0, jnSup) = the (Sols, Sols) $ case mexp of
                  Nothing => ([], [])
                  Just c => matchTySplit jn blankPoss (substTy tailTy (prefixSub patArgs)) c
    -- phase 1: walk the written spine left to right, solving from
    -- inference-form arguments as they elaborate
    (sols, revArgs, revSks, pending, srcs, attrs, defers) <- walk presIn jn ((st.impTrialOn || st.svSugarOn) && not st.probing) doms slots sols0 [] [] [] [] [] []
    -- resolve every inserted hole; unsolved is a structural error
    -- the MILLER-PATTERN tier, STRICTLY ADDITIVELY: only holes the
    -- classic walk left unsolved may gain bindings (each source is
    -- re-matched in pattern mode at its domain, with entries
    -- refreshed to the joint solution so far), so every site that
    -- already solved solves identically — committed corpora stay
    -- valid by construction
    let unsolvedKs = mapMaybe (\(pos, mt) => case mt of
                        Just (SBlank _) => if isNothing (lookup pos sols) then Just pos else Nothing
                        Nothing => if isNothing (lookup pos sols) then Just pos else Nothing
                        Just _ => Nothing) slots
    -- the pass's join also opens .unfold-cited (exposure-licensed)
    -- heads: it fills only otherwise-unsolved holes, so the wider
    -- join cannot disturb an existing solution
    let jnX = \t => compTy (unfTy st.sig
                     (st.eqScope ++ mapMaybe expName st.eqScope) t)
    let argsNow = reverse revArgs
    let passSrcs = (case mexp of
                      Nothing => []
                      Just c => [(Nothing, c)]) ++
                   map (\(sp, t) => (Just sp, t)) (pending ++ srcs)
    let sols = if null unsolvedKs then sols
               else patternPass jnX doms tailTy argsNow unsolvedKs passSrcs sols
    -- CAPTURE-TYPING sources, to a fixpoint: a solved hole's value
    -- is a bare inferable core, and final instantiation will demand
    -- its type CONVERT with the hole's instantiated domain — so the
    -- pair (declared domain, inferred type) is a real equation of
    -- the site, matched like any source. At a Σ-typed hole the
    -- second component sits under the Σ's own binder, where the
    -- Miller tier solves it UNIQUELY — pairextD's {B} from the
    -- pair's actual type, dependent or not; the constant tier this
    -- replaces guessed from an instance and was withdrawn
    let sols = solveDerived st.kernelSig ctx jnX doms tailTy argsNow passSrcs
                 (S (length unsolvedKs)) unsolvedKs sols
    (finalArgs, dPatches) <- resolveArgs sols defers doms (zip slots (reverse revArgs)) [] []
    -- a blank whose SUPPRESSED join binding α-differs from its
    -- final solution would solve differently as an implicit — the
    -- migration's per-site blocker signal
    when (st.svSugarOn && not st.probing) $ case mrng of
      Nothing => pure ()
      Just rng =>
        traverse_ (\(pos, mt) => case mt of
            Just (SBlank _) =>
              case (lookup pos jnSup, getAt pos finalArgs) of
                (Just jv, Just fv) =>
                  when (show jv /= show fv) $
                    modifySt $ { svBlankRisk $= (:< (st.modPrefix, rng, pos)) }
                _ => pure ()
            _ => pure ()) slots
    -- solved blanks feed the LSP hover: the recovered value at the
    -- written `_`, ascribed with its instantiated domain and the
    -- source that bound it — an argument's inferred type (by the
    -- walk's attribution) or, failing that, the expected type
    -- (sols0's bindings are the only other entry point)
    traverse_ (\(pos, mt) => case mt of
        Just (SBlank (Just brng)) =>
          case (getAt pos finalArgs, getAt pos doms) of
            (Just v, Just d) =>
              let msrc = the (Maybe Elem) (lookup pos attrs >>= \apos => getAt apos finalArgs) in
              modifySt $ { blankVals $= (:< (st.modPrefix, brng, env, v,
                             substTy d (prefixSub (take pos finalArgs)), msrc)) }
            _ => pure ()
        _ => pure ()) slots
    -- pending switch conversions, at the FINAL instantiations
    sks0 <- patchPending doms finalArgs (reverse revSks) pending
    let sks = foldl (\ss, (dpos, dsk) => mapAt dpos (const dsk) ss) sks0 dPatches
    -- the implicitize TRIAL (docs/NovaPerfectSurface.txt, Phase 3c):
    -- for every {t}-override at an implicit position, replay the
    -- HYPOTHETICAL elided recovery — implicit positions as holes,
    -- sources exactly what elision would have (the expected type
    -- with throwaway holes at explicit positions; then the inferred
    -- types of explicit inference-form arguments, in walk order) —
    -- and record whether it reproduces the written value α-exactly.
    -- A site whose every written argument sits at an implicit
    -- position records failure outright (elided it would be a BARE
    -- reference, not an application), as does a site where an
    -- intro-form argument meets a hole-bearing hypothetical domain
    -- (real elision errors there before any later source can fire).
    when st.impTrialOn $ do
      let impOvers = mapMaybe (\(pos, mt) => case mt of
                                 Just _ => if pos `elem` imps then Just pos else Nothing
                                 Nothing => Nothing) slots
      case impOvers of
        [] => pure ()
        _ => do
          -- a position is elidable only if the elided spine still
          -- WRITES something after it: an implicit position past the
          -- last surviving explicit argument would be TRAILING, and
          -- trailing implicits are not inserted (the elided site
          -- would be a partial application — a different erasure)
          let expPoss = mapMaybe (\(pos, mt) => case mt of
                          Just _ => if pos `elem` imps then Nothing else Just pos
                          Nothing => Nothing) slots
          -- a trailing position is fine when the site is CHECKED:
          -- insertion reaches it (the consumed positions past the
          -- last explicit are all implicit by construction)
          let notTrailing = \pos => isJust mexp ||
                                    (not (null leftover)) ||
                                    any (\p => p > pos) expPoss
          let hypPat = map (\(i, _) => if i `elem` imps then holeE i
                                                        else holeE (throwaway + i)) slots
          let hyp0 = case mexp of
                       Nothing => []
                       Just c => matchTy jn (substTy tailTy (prefixSub hypPat)) c
          let srcsX = filter (\(p, _) => not (p `elem` imps)) (pending ++ srcs)
          let (hypSols, hypDefs, eagerStuck) = trialSolve jn doms imps (deferPossOf st slots) srcsX finalArgs 0 m hyp0 [] []
          let stuck = eagerStuck || trialStuck doms slots imps hypSols finalArgs hypDefs
          traverse_ (\pos =>
              let verdict = if not (notTrailing pos) then 1
                            else if stuck then 2
                            else case (lookup pos hypSols, getAt pos finalArgs) of
                              (Just v, Just w) => if show v == show w then 0 else 4
                              _ => 3
              in modifySt $ { impTrial $= (:< (q, pos, verdict,
                                                 map (\r => (st.modPrefix, r)) mrng)) })
            impOvers
    -- the BLANK-EMISSION trial (docs/NovaPerfectSurface.txt): which
    -- written EXPLICIT arguments could the distiller replace with
    -- `_`? The hypothetical mirrors re-elaboration of the blanked
    -- spine — blanked positions join the hole set, their inferred
    -- types leave the source pool — and the JOINT solve must
    -- reproduce every hole α-exactly, the implicit insertions
    -- included (their own sources may be the ones blanked away).
    -- The set grows greedily left to right, each addition verified
    -- jointly, then sweeps to a fixpoint: a position stays written
    -- exactly when it fails against the FINAL set — the same test a
    -- re-distill of the emitted file runs, so the canonical form is
    -- byte-idempotent.
    when (st.svSugarOn && not st.probing) $ case mrng of
      Just rng => blankTrial jn rng imps doms tailTy m slots sks finalArgs (pending ++ srcs)
      Nothing => pure ()
    let core = foldl PiApp (SigVar q [<]) finalArgs
    let coreTy = substTy tailTy (prefixSub finalArgs)
    let sk = foldl (\acc, s => Nd [] [acc, s]) (Nd [] []) sks
    continueApp (core, coreTy, sk) leftover
   where
    throwaway : Nat
    throwaway = 1000000

    matchTy : (jn : Ty -> Ty) -> Ty -> Ty -> Sols
    matchTy jn pat g = case mTy 0 pat g [] of
      Just s => s
      Nothing => case mTy 0 (compTy pat) (compTy g) [] of
        Just s => s
        Nothing => fromMaybe [] (mTy 0 (jn pat) (jn g) [])

    ||| The expected-type match, tier-aware per hole kind: a
    ||| licensed-join capture carries the JOIN's spelling — unfolded,
    ||| possibly stuck-eliminator-bearing — safe for IMPLICIT holes
    ||| (historically verified; some corpus sites NEED it) but not
    ||| for BLANKS (value-like, no verdict to catch drift). Join-tier
    ||| bindings for blank holes are dropped — and returned
    ||| SEPARATELY: a blank whose suppressed join binding α-differs
    ||| from its final solution would solve DIFFERENTLY as an
    ||| implicit, which the targeted implicitize migration must know
    ||| (such a site blocks a blank → implicit conversion).
    matchTySplit : (jn : Ty -> Ty) -> List Nat -> Ty -> Ty -> (Sols, Sols)
    matchTySplit jn blankPoss pat g = case mTy 0 pat g [] of
      Just s => (s, [])
      Nothing => case mTy 0 (compTy pat) (compTy g) [] of
        Just s => (s, [])
        Nothing =>
          let full = fromMaybe [] (mTy 0 (jn pat) (jn g) [])
          in (filter (\(k, _) => not (k `elem` blankPoss)) full,
              filter (\(k, _) => k `elem` blankPoss) full)

    ||| A bare reference to an implicit-binder def is NEVER a usable
    ||| source at a holey domain: its inference-mode type is the
    ||| UN-INSERTED Π (checking would have inserted the implicit run),
    ||| so the matcher would bind from a core the checked run does not
    ||| have. Like an intro form, it defers — and checks later, at a
    ||| hole-free domain, with its insertion intact.
    bareImplicitRef : ElabSt -> SElem -> Bool
    bareImplicitRef st e = case unPos e of
      SSig _ x0 => case lookup (resolveSigName st x0) st.impls of
                     Just (_ :: _) => True
                     _ => False
      _ => False

    ||| the written positions the walk DEFERS: intro forms, and bare
    ||| implicit-headed references (blank slots are holes, not
    ||| written arguments)
    deferPossOf : ElabSt -> List (Nat, Maybe SElem) -> List Nat
    deferPossOf st slots = mapMaybe (\(pos, mt) => case mt of
        Just (SBlank _) => Nothing
        Just se => if sInferForm se && not (bareImplicitRef st se)
                     then Nothing else Just pos
        Nothing => Nothing) slots

    ||| Assign telescope positions to written spine items: an implicit
    ||| position takes an override if one is next, else a HOLE (no item
    ||| consumed); an explicit position takes the next non-override
    ||| item. Insertion stops with the written items (trailing
    ||| implicits are not inserted); items beyond the syntactic
    ||| telescope are LEFTOVER, applied generically after.
    assign : List Nat -> Nat -> List Ty -> List SElem ->
             ElabM (List (Nat, Maybe SElem), List SElem)
    assign imps pos (d :: ds) [] =
      -- written items exhausted: INSERT the trailing implicit run
      -- (checking position, unmarked — the expected type is the
      -- solver), stopping at the first explicit position
      if insertTrailing && (pos `elem` imps)
        then do
          (more, left) <- assign imps (S pos) ds []
          pure ((pos, Nothing) :: more, left)
        else pure ([], [])
    assign imps pos [] rest = pure ([], rest)
    assign imps pos [] [] = pure ([], [])
    assign imps pos (d :: ds) (it :: rest) =
      if pos `elem` imps
        then case it of
          SImpArg t => do
            (more, left) <- assign imps (S pos) ds rest
            -- BARE: the slot's term is inspected by shape further
            -- down (is it a blank?), like every spine argument
            pure ((pos, Just (unPos t)) :: more, left)
          -- a blank, like any non-override item, DEFERS past the
          -- implicit position (the hole is inserted; the blank
          -- stands for the next EXPLICIT position — the only place
          -- `_` may bind)
          _ => do
            (more, left) <- assign imps (S pos) ds (it :: rest)
            pure ((pos, Nothing) :: more, left)
        else case it of
          SImpArg _ => throwAt site.srange "\{site}: {…} override at an explicit binder position of '\{q}'"
          _ => do
            (more, left) <- assign imps (S pos) ds rest
            pure ((pos, Just it) :: more, left)

    ||| One pass over the slots: elaborated core arguments accumulate
    ||| (holes as placeholders until solved); a written argument whose
    ||| domain still carries holes must INFER, its type feeding the
    ||| matcher, its domain conversion deferred to the final
    ||| instantiation.
    walk : List (Maybe (Elem, Ty, Skel)) ->
           (jn : Ty -> Ty) -> (trialOn : Bool) -> List Ty -> List (Nat, Maybe SElem) -> Sols ->
           List Elem -> List Skel -> List (Nat, Ty) -> List (Nat, Ty) -> List (Nat, Nat) ->
           List (Nat, SElem) ->
           ElabM (Sols, List Elem, List Skel, List (Nat, Ty), List (Nat, Ty), List (Nat, Nat), List (Nat, SElem))
    walk pres jn trialOn doms [] sols revArgs revSks pending srcs attrs defers =
      pure (sols, revArgs, revSks, pending, srcs, attrs, defers)
    walk pres jn trialOn doms ((pos, mt) :: rest) sols revArgs revSks pending srcs attrs defers = case mt of
      Nothing =>
        let arg = fromMaybe (holeE pos) (lookup pos sols) in
        walk pres jn trialOn doms rest sols (arg :: revArgs) (Nd [] [] :: revSks) pending srcs attrs defers
      -- a written BLANK is a hole at its (explicit) position: same
      -- placeholder, same joint solve, same resolution — an inserted
      -- implicit that happens to be spelled `_`
      Just (SBlank _) =>
        let arg = fromMaybe (holeE pos) (lookup pos sols) in
        let pres' = the (List (Maybe (Elem, Ty, Skel))) (case pres of { (_ :: ps) => ps; [] => [] }) in
        walk pres' jn trialOn doms rest sols (arg :: revArgs) (Nd [] [] :: revSks) pending srcs attrs defers
      Just surfE => do
        let (pre, pres') = the (Maybe (Elem, Ty, Skel), List (Maybe (Elem, Ty, Skel))) $
                             case pres of
                               (p :: ps) => (p, ps)
                               [] => (Nothing, [])
        dInst <- case getAt pos doms of
                   Just d => pure (substTy d (prefixSub (reverse revArgs)))
                   Nothing => throwAt site.srange "\{site}: internal — slot beyond the telescope"
        case pre of
          -- a PRE-ELABORATED argument (overload resolution): use its
          -- inferred type, defer the domain conversion like the
          -- hole-bearing route (the domain may still carry holes)
          Just (e', eTy, eSk) => do
            let sols2 = if hasHolesT dInst
                          then case mTy 0 dInst eTy sols of
                                 Just s => s
                                 Nothing => case mTy 0 (compTy dInst) (compTy eTy) sols of
                                   Just s => s
                                   Nothing => fromMaybe sols (mTy 0 (jn dInst) (jn eTy) sols)
                          else sols
            let attrs2 = attrs ++ map (\(k, _) => (k, pos))
                           (filter (\(k, _) => isNothing (lookup k sols)) sols2)
            walk pres' jn trialOn doms rest sols2 (e' :: revArgs) (eSk :: revSks) ((pos, eTy) :: pending) srcs attrs2 defers
          Nothing =>
            if hasHolesT dInst
              then do
                st2 <- getSt
                if sInferForm surfE && not (bareImplicitRef st2 surfE)
                  then do
                    mres <- attemptM (asArg (inferElem ctx env site surfE))
                    case mres of
                      Just (e', eTy, eSk) => do
                        let sols2 = case mTy 0 dInst eTy sols of
                                      Just s => s
                                      Nothing => case mTy 0 (compTy dInst) (compTy eTy) sols of
                                        Just s => s
                                        Nothing => fromMaybe sols (mTy 0 (jn dInst) (jn eTy) sols)
                        let attrs2 = attrs ++ map (\(k, _) => (k, pos))
                                       (filter (\(k, _) => isNothing (lookup k sols)) sols2)
                        walk pres' jn trialOn doms rest sols2 (e' :: revArgs) (eSk :: revSks) ((pos, eTy) :: pending) srcs attrs2 defers
                      -- FAIL-DEFERRAL: an inference that fails at a
                      -- holey domain was never going to be a source —
                      -- defer it like an intro and check it after the
                      -- joint solve, at its final (hole-free) domain
                      Nothing =>
                        walk pres' jn trialOn doms rest sols (holeE pos :: revArgs) (Nd [] [] :: revSks) pending srcs attrs ((pos, surfE) :: defers)
                  else
                    -- DEFER an intro form, or a bare implicit-headed
                    -- reference, at a still-holey domain: neither is
                    -- a usable source (no type to mine / the
                    -- un-inserted Π), so checking waits for the joint
                    -- solve to fill the domain — resolved in position
                    -- order after the walk
                    walk pres' jn trialOn doms rest sols (holeE pos :: revArgs) (Nd [] [] :: revSks) pending srcs attrs ((pos, surfE) :: defers)
              else if trialOn && sInferForm surfE
                then do
                  -- the trials need the argument's INFERRED type as a
                  -- recovery source, but the argument itself must
                  -- elaborate exactly as the plain pass does (its own
                  -- solving may need the checking context — e.g. its
                  -- trailing implicits come from dInst). So: commit
                  -- via checkElem, and take the source type from a
                  -- DISCARDED inference probe — a probe failure just
                  -- means no source, which is faithful: the elided
                  -- form's recovery would face the same failure
                  (e', eSk) <- asArg (checkElem ctx env site surfE dInst)
                  mty <- probeM (asArg (inferElem ctx env site surfE))
                  -- the source is admissible only when inference
                  -- commits the SAME core as checking did: blanking
                  -- an earlier position flips this argument to
                  -- inference at re-elaboration, and an argument
                  -- whose core depends on its checking context
                  -- (trailing insertion, expectation-solved
                  -- implicits, overload choice) must block that flip
                  -- — no source means the hypothetical sticks
                  let srcs' = case mty of
                                Just (pe, eTy, _) => if show pe == show e'
                                                       then (pos, eTy) :: srcs
                                                       else srcs
                                Nothing => srcs
                  walk pres' jn trialOn doms rest sols (e' :: revArgs) (eSk :: revSks) pending srcs' attrs defers
                else do
                  (e', eSk) <- asArg (checkElem ctx env site surfE dInst)
                  walk pres' jn trialOn doms rest sols (e' :: revArgs) (eSk :: revSks) pending srcs attrs defers

    expName : String -> Maybe String
    expName n = if isPrefixOf "exp:" n then Just (pack (drop 4 (unpack n))) else Nothing

    refreshHole : Sols -> Elem -> Elem
    refreshHole sols e = case e of
      SigVar nm [<] => case holeView nm of
        Just i => fromMaybe e (lookup i sols)
        Nothing => e
      _ => e

    ||| the end-stage pattern pass: the EXPECTED TYPE first (matched
    ||| against the instantiated tail — where funextD's endpoint
    ||| holes ?f, ?g live), then the recorded sources in order; each
    ||| matched in PATTERN mode (α, comp, widened licensed join) at
    ||| its refreshed pattern, keeping only bindings for the still-
    ||| unsolved keys
    patternPass : (jn : Ty -> Ty) -> List Ty -> Ty -> List Elem -> List Nat ->
                  List (Maybe Nat, Ty) -> Sols -> Sols
    patternPass jn doms tailT argsNow ks [] sols = sols
    patternPass jn doms tailT argsNow ks ((msp, eTy) :: more) sols =
      let mpat = the (Maybe Ty) $ case msp of
                   Nothing => Just (substTy tailT (prefixSub (map (refreshHole sols) argsNow)))
                   Just sp => map (\d => substTy d (prefixSub (map (refreshHole sols) (take sp argsNow))))
                                  (getAt sp doms)
      in case mpat of
           Nothing => patternPass jn doms tailT argsNow ks more sols
           Just dHyp =>
             let found = the (Maybe Sols) $ case mTyP True 0 dHyp eTy sols of
                           Just s2 => Just s2
                           Nothing => case mTyP True 0 (compTy dHyp) (compTy eTy) sols of
                             Just s2 => Just s2
                             Nothing => mTyP True 0 (jn dHyp) (jn eTy) sols
                 sols2 = case found of
                           Nothing => sols
                           Just s2 => sols ++ filter (\(k2, _) =>
                                        (k2 `elem` ks) && isNothing (lookup k2 sols)) s2
             in patternPass jn doms tailT argsNow ks more sols2

    ||| the capture-typing fixpoint: each round derives (Just pos,
    ||| inferred type of pos's solution) sources from every solved
    ||| hole whose value the kernel can infer (against the kernel Σ,
    ||| which may lag on obligation-bearing items — absence just
    ||| skips the source), and re-runs the pass for the still-
    ||| unsolved keys. Productive rounds solve at least one hole, so
    ||| the round count is bounded by the unsolved-key count.
    solveDerived : Sig -> Ctx -> (jn : Ty -> Ty) -> List Ty -> Ty -> List Elem ->
                   List (Maybe Nat, Ty) -> Nat -> List Nat -> Sols -> Sols
    solveDerived ksig kctx jn doms tailT argsNow passSrcs Z ks sols = sols
    solveDerived ksig kctx jn doms tailT argsNow passSrcs (S n) ks sols =
      let un = filter (\pos => isNothing (lookup pos sols)) ks in
      if null un then sols else
      let dsrcs = mapMaybe (\(pos, v) =>
                    if pos < length doms
                      then map (\t => (Just pos, t)) (kInferBare ksig kernelFuel kctx v)
                      else Nothing) sols
          sols2 = patternPass jn doms tailT argsNow un (passSrcs ++ dsrcs) sols
      in if length sols2 == length sols then sols
         else solveDerived ksig kctx jn doms tailT argsNow passSrcs n ks sols2

    ||| Resolve the walked slots to the final argument list, in
    ||| position order: a hole takes its joint solution (a structural
    ||| error names the remedy when there is none); a DEFERRED intro
    ||| form checks NOW, at its domain instantiated with everything
    ||| already resolved — hole-free by construction or the argument
    ||| must be spelled. Deferred skeletons replace their placeholders
    ||| by position.
    resolveArgs : Sols -> List (Nat, SElem) -> List Ty ->
                  List ((Nat, Maybe SElem), Elem) -> List Elem -> List (Nat, Skel) ->
                  ElabM (List Elem, List (Nat, Skel))
    resolveArgs sols defers doms [] acc patches = pure (reverse acc, patches)
    resolveArgs sols defers doms (((pos, mt), arg) :: rest) acc patches =
      case lookup pos defers of
        Just surfE => do
          d <- case getAt pos doms of
                 Just d => pure d
                 Nothing => throwAt site.srange "\{site}: internal — deferred slot beyond the telescope"
          let dFinal = substTy d (prefixSub (reverse acc))
          when (hasHolesT dFinal) $
            throwAt site.srange "\{site}: argument #\{show pos} of '\{q}' has an undetermined domain — a blank it depends on found no source; spell the blank"
          (e', eSk) <- asArg (checkElem ctx env site surfE dFinal)
          resolveArgs sols defers doms rest (e' :: acc) ((pos, eSk) :: patches)
        Nothing =>
          if hasHolesE arg
            then case lookup pos sols of
              Just v => resolveArgs sols defers doms rest (v :: acc) patches
              Nothing => case mt of
                -- at the blank ITSELF, when it was written with one
                Just (SBlank brng) => throwAt (brng <|> site.srange) "\{site}: cannot infer the blank at argument #\{show pos} of '\{q}' — spell the argument"
                _ => case holeArg items of
                  -- An implicit that NO SOURCE determined, in a spine
                  -- one of whose arguments is a HOLE. The hole infers
                  -- nothing, so the source that would have fixed this
                  -- implicit is exactly the one the operator declined
                  -- to write — the implicit is as unknown as the hole
                  -- and becomes one too, at its own declared domain.
                  -- e-hole-shape one level up: `cong B f ?p` reports
                  -- `?p : ?p/imp3 ≡ ?p/imp4 ∈ ?p/imp0` instead of
                  -- failing, and the goals downstream of it survive.
                  --
                  -- Only reachable once the oracle has exhausted every
                  -- source, so a hole-free spine never comes here.
                  Just (hrng, label) =>
                    case getAt pos doms of
                      Nothing => throwAt site.srange "\{site}: internal — implicit slot beyond the telescope"
                      Just d =>
                        let dFinal = substTy d (prefixSub (reverse acc)) in
                        -- a domain still carrying the oracle's own
                        -- placeholders is not a type to declare
                        -- anything at; that is the honest error
                        if hasHolesT dFinal
                          then throwAt site.srange "\{site}: cannot infer implicit argument #\{show pos} of '\{q}' — supply it with {…}, or pass the bare function with \{q} {}"
                          else do
                            v <- mintHole ctx env site hrng "\{label}/imp\{show pos}" dFinal
                            resolveArgs sols defers doms rest (v :: acc) patches
                  Nothing => throwAt site.srange "\{site}: cannot infer implicit argument #\{show pos} of '\{q}' — supply it with {…}, or pass the bare function with \{q} {}"
            else resolveArgs sols defers doms rest (arg :: acc) patches

    ||| The hypothetical elided solve, replaying `walk`'s discipline
    ||| over the recorded sources: at an implicit position the entry
    ||| is its hole or solution-so-far; at an explicit position the
    ||| real core argument; a hole-bearing hypothetical domain
    ||| consumes its position's recorded source, or — when the
    ||| argument was an intro form, with no inferred type — STICKS
    ||| (real elision errors there).
    trialSolve : (jn : Ty -> Ty) -> List Ty -> List Nat -> (introPoss : List Nat) ->
                 List (Nat, Ty) -> List Elem ->
                 (pos, m : Nat) -> Sols -> List Elem -> List Nat -> (Sols, List Nat, Bool)
    trialSolve jn doms imps introPoss srcsX finalArgs pos m sols hypRev defs =
      if pos >= m then (sols, defs, False) else
        let entry = if pos `elem` imps
                      then fromMaybe (holeE pos) (lookup pos sols)
                      else fromMaybe (holeE pos) (getAt pos finalArgs)
        in if pos `elem` imps
             then trialSolve jn doms imps introPoss srcsX finalArgs (S pos) m sols (entry :: hypRev) defs
             else
               let dHyp = case getAt pos doms of
                            Just d => substTy d (prefixSub (reverse hypRev))
                            Nothing => NatTy
               in if hasHolesT dHyp
                    then case lookup pos srcsX of
                      Just eTy =>
                        let sols' = case mTy 0 dHyp eTy sols of
                                      Just s => s
                                      Nothing => case mTy 0 (compTy dHyp) (compTy eTy) sols of
                                        Just s => s
                                        Nothing => fromMaybe sols (mTy 0 (jn dHyp) (jn eTy) sols)
                        in trialSolve jn doms imps introPoss srcsX finalArgs (S pos) m sols' (entry :: hypRev) defs
                      Nothing =>
                        if pos `elem` introPoss
                          -- an INTRO form mirrors the walk's deferral —
                          -- INCLUDING its placeholder: the real walk
                          -- pushes a hole for a deferred slot, so later
                          -- domains must see the hole here too (the
                          -- value would let comp-tier matches fire that
                          -- re-elaboration never sees). Whether it
                          -- sticks is an END-state question (trialStuck)
                          then trialSolve jn doms imps introPoss srcsX finalArgs (S pos) m sols (holeE pos :: hypRev) (pos :: defs)
                          -- an INFERENCE form at a holey domain INFERS
                          -- at re-elaboration — and without an
                          -- ADMISSIBLE source its inferred core is not
                          -- the checked one (trailing insertion,
                          -- expectation-solved implicits, overload
                          -- choice): the flip would change the
                          -- argument, so the set is rejected outright
                          else (sols, defs, True)
                    else trialSolve jn doms imps introPoss srcsX finalArgs (S pos) m sols (entry :: hypRev) defs

    ||| The deferral end-check, the trial's mirror of resolveArgs: a
    ||| deferred position sticks exactly when its domain, instantiated
    ||| with the FINAL joint entries, still carries holes.
    trialStuck : List Ty -> List (Nat, Maybe SElem) -> List Nat -> Sols -> List Elem -> List Nat -> Bool
    trialStuck doms slots hs solsF finalArgs defs =
      case defs of
        [] => False
        _ =>
          let es = map (\(i, _) => if i `elem` hs
                                     then fromMaybe (holeE i) (lookup i solsF)
                                     else fromMaybe (holeE i) (getAt i finalArgs)) slots
          in any (\dp => case getAt dp doms of
                           Just d => hasHolesT (substTy d (prefixSub (take dp es)))
                           Nothing => True) defs

    blankTrial : (Ty -> Ty) -> Range -> List Nat -> List Ty -> Ty -> Nat ->
                 List (Nat, Maybe SElem) -> List Skel -> List Elem -> List (Nat, Ty) -> ElabM ()
    blankTrial jn rng imps doms tailTy m slots sks finalArgs sources = do
      st <- getSt
      let final = iter (deferPossOf st slots) st.inArg (S (length cands)) []
      traverse_ (\p => modifySt $ { svBlank $= (:< (st.modPrefix, rng, itemIdx p)) }) final
     where
      ||| the current hole set: inserted implicits plus written blanks
      holes0 : List Nat
      holes0 = mapMaybe (\(pos, mt) => case mt of
                 Nothing => Just pos
                 Just (SBlank _) => Just pos
                 Just _ => Nothing) slots

      ||| Is the payload one the kernel re-derives on its own? A
      ||| blank slot hands the kernel a BARE skeleton, so the whole
      ||| committed derivation of a candidate must carry nothing but
      ||| trivial switches — a licensed conversion (its certificate
      ||| lives in the skeleton), a motive, an intro-in-inference
      ||| type: any of those, anywhere inside, and the value is
      ||| α-recoverable yet kernel-unREcheckable — the uip lesson
      ||| (refl a x checks at Id a x y only through hyp.rw)
      payloadBare : Payload -> Bool
      payloadBare (PSwitch c) = stepFree c
      -- a TRIVIAL exposure (El-code head opened by computation
      -- alone) is re-derived by the kernel bare — it is licensed
      -- exposure (a lemma-rewritten head) that must keep its
      -- skeleton
      payloadBare (PExpose _ c) = stepFree c
      payloadBare _ = False

      skelBare : Skel -> Bool
      skelBare (Nd ps cs) = all payloadBare ps && all skelBare cs

      ||| the candidates: written explicit non-blank positions whose
      ||| committed skeleton is kernel-rederivable when dropped
      cands : List Nat
      cands = mapMaybe (\((pos, mt), sk) => case mt of
                Just (SBlank _) => Nothing
                Just _ => if (pos `elem` imps) || not (skelBare sk)
                            then Nothing else Just pos
                Nothing => Nothing) (zip slots sks)

      ||| the recorded index is the argument's rank among the CONSUMED
      ||| items — the count the distiller can reproduce on the surface
      ||| spine without knowing the telescope
      itemIdx : Nat -> Nat
      itemIdx p = length (filter (\(pos, mt) => pos < p && isJust mt) slots)

      solve : List Nat -> Maybe Ty -> List Nat -> (Sols, Bool)
      solve dps mc hs =
        let hypPat = map (\(i, _) => if i `elem` hs then holeE i else holeE (throwaway + i)) slots
            hyp0 = the Sols $ case mc of
                     Nothing => []
                     Just c => fst (matchTySplit jn (filter (\hp => not (hp `elem` imps)) hs)
                                      (substTy tailTy (prefixSub hypPat)) c)
            srcsX = filter (\(sp, _) => not (sp `elem` hs)) sources
            (solsF, defs, eagerStuck) = trialSolve jn doms hs dps srcsX finalArgs 0 m hyp0 [] []
        in (solsF, eagerStuck || trialStuck doms slots hs solsF finalArgs defs)

      okAt : List Nat -> Maybe Ty -> List Nat -> Bool
      okAt dps mc hs = let (hypSols, stuck) = solve dps mc hs in
        not stuck && all (\hp => case (lookup hp hypSols, getAt hp finalArgs) of
                                  (Just v, Just w) => show v == show w
                                  _ => False) hs

      ||| a blank at a FLIPPABLE site — a spine argument, whose
      ||| checking context an enclosing blank can take away at
      ||| re-elaboration — must recover in BOTH modes, so its verdict
      ||| may not lean on the expected type (nor be broken by its
      ||| extra bindings). Everywhere else (def bodies, signature
      ||| types, eliminator branches, let bindings) the mode is
      ||| fixed and the actual mode alone decides.
      ok : List Nat -> Bool -> List Nat -> Bool
      ok dps flip hs = okAt dps mexp hs && (case (flip, mexp) of
                                              (True, Just _) => okAt dps Nothing hs
                                              _ => True)

      step : List Nat -> Bool -> List Nat -> Nat -> List Nat
      step dps flip b p = if p `elem` b then b
                          else if ok dps flip (holes0 ++ b ++ [p]) then b ++ [p] else b

      iter : List Nat -> Bool -> Nat -> List Nat -> List Nat
      iter dps flip Z b = b
      iter dps flip (S fuel) b =
        let b' = foldl (step dps flip) b cands in
        if length b' == length b then b else iter dps flip fuel b'

    mapAt : Nat -> (Skel -> Skel) -> List Skel -> List Skel
    mapAt _ _ [] = []
    mapAt Z f (x :: xs) = f x :: xs
    mapAt (S n) f (x :: xs) = x :: mapAt n f xs

    ||| Emit the deferred domain conversions (the ordinary ↓ of
    ||| e-switch, certificate in the argument's skeleton payload), at
    ||| domains instantiated with the FINAL argument list.
    patchPending : List Ty -> List Elem -> List Skel -> List (Nat, Ty) -> ElabM (List Skel)
    patchPending doms finalArgs sks [] = pure sks
    patchPending doms finalArgs sks ((pos, eTy) :: more) = do
      dFinal <- case getAt pos doms of
                  Just d => pure (substTy d (prefixSub (take pos finalArgs)))
                  Nothing => throwAt site.srange "\{site}: internal — pending position out of range"
      when (hasHolesT dFinal) $ throwAt site.srange "\{site}: INTERNAL imp-leak dFinal pos=\{show pos} q=\{q}"
      when (hasHolesT eTy) $ throwAt site.srange "\{site}: INTERNAL imp-leak eTy pos=\{show pos} q=\{q}"
      -- INFERRED ≐ EXPECTED, the e-switch orientation: the kernel
      -- replays the switch certificate in that direction, and a
      -- licensed (step-carrying) certificate is direction-sensitive
      -- (α/comp-closed ones are symmetric, which is why the deferred
      -- route could pass reversed arguments unnoticed until a blank
      -- first deferred a hyp.rw-needing conversion)
      c <- convTy ctx env (sub site "\{site}: implicit-spine argument type") Nothing eTy dFinal
      patchPending doms finalArgs (mapAt pos (addPayload (PSwitch (certOr c))) sks) more


    ||| Apply leftover items past the syntactic telescope through the
    ||| generic application rule (overrides are illegal there).
    continueApp : (Elem, Ty, Skel) -> List SElem -> ElabM (Elem, Ty, Skel)
    continueApp acc [] = pure acc
    continueApp (f', fTy, fSk) (it :: rest) = case it of
      SImpArg _ => throwAt site.srange "\{site}: {…} override beyond the Π-telescope of '\{q}'"
      _ => do
        st <- getSt
        case preferPi st ctx fTy of
          Just (a, b, _) => do
            (e', eSk) <- asArg (checkElem ctx env site it a)
            continueApp (PiApp f' e', substTy b (Ext Id e'), Nd [] [fSk, eSk]) rest
          Nothing => throwShape site env "cannot apply a term of type" fTy "a Π type"

-- ===== Items =====

||| Register a just-accepted definition's equation (if its type peels
||| to an equality prop) as a rewrite candidate: the WHOLE context
||| (telescope + peeled Πs) is parametric, so the lemma applies in
||| any context.
addLemma : String -> Ctx -> Ty -> ElabM ()
addLemma name delta ty = withEqScope ["exp:*"] $ do
  st <- getSt
  let (delta', peeled) = peelPis delta (peelNf st ty)
  -- equality is Ω-valued: a lemma registers when its peeled type IS
  -- an equality prop (squashed spellings converge here by
  -- code-squash-idem)
  let meq : Maybe (Elem, Elem, Ty) =
        case exposeCode st peeled of
          Elem.EqTy l r t => Just (l, r, t)
          _ => Nothing
  case meq of
    Just (l, r, t) =>
      -- Sides normalized against the store as of this point (recording
      -- the normalization so the kernel can bridge from the raw
      -- reflected equation); closed under component decomposition.
      let lemmaRw = st.candRw
          k = length delta'
          teleLen = length delta
          peeledN = minus k teleLen
          mk : Nat -> Bindings -> Maybe (Elem, List Sel)
          mk = \wk, bs => do
            teleArgs <- traverse (\p => lookup p bs)
                          (the (List Nat) (if teleLen == 0 then [] else reverse [peeledN .. minus k 1]))
            peeledArgs <- traverse (\p => lookup p bs)
                            (the (List Nat) (if peeledN == 0 then [] else reverse [0 .. minus peeledN 1]))
            pure (foldl PiApp (SigVar name (cast teleArgs)) peeledArgs, the (List Sel) [])
          lRes = rwNfElemS st.sig [] lemmaRw True (engNfE st l)
          rRes = rwNfElemS st.sig [] lemmaRw True (engNfE st r)
          toP : List Step -> List PStep
          toP = map (\s => MkPStep s.path (licProof s.lic) s.sels s.flip)
      in modifySt $ \st' =>
           let ls = closeCand (MkCand name k (toList delta') (fst lRes) (fst rRes)
                                      mk (toP (snd lRes)) (toP (snd rRes))) ++ st'.lemmas
               (cs, sh, re, hp) = sigCandParts ls
               new = closeCand (MkCand name k (toList delta') (fst lRes) (fst rRes)
                                       mk (toP (snd lRes)) (toP (snd rRes)))
           in { lemmas := ls, ownLemmas := new ++ st'.ownLemmas
              , candCs := cs, candShrink := sh
              , candRest := re, candHops := hp, candRw := sh ++ re } st'
    _ => pure ()

||| they cannot be accepted anyway.
kernelAccept : String -> (Sig -> Either KErr SigEntry) -> Bool -> ElabM ()
kernelAccept name check clean = do
  st <- getSt
  if not clean
    then pure ()
    else
      let t0 = nowNs () in
      let res = check st.kernelSig in
      case bump "kitem" (nowNs () - t0) res of
        Right entry => modifySt $ { kernelSig $= (:< entry) }
        Left err => throw "\{name}: KERNEL REJECTED the elaborated item: \{err}"

liftQE : Site -> Either QErr a -> ElabM a
liftQE site (Left e) = throwAt site.srange "\{site}: \{e}"
liftQE site (Right x) = pure x

||| Emit one core definition item: kernel-check, extend Σ, register a
||| lemma if it is ≡-typed. Mirrors elabItem's tail for surface defs.
emitCoreDef : Site -> String -> Ty -> Skel -> Elem -> Skel -> ElabM ()
emitCoreDef site x ty tySk body bodySk = do
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throwAt site.srange "\{site}: duplicate signature name '\{x}'"
    Nothing => pure ()
  after <- oblCount
  kernelAccept "\{site} \{x}"
    (\ksig => kCheckDefItem ksig kernelFuel (MkKDefArt q [] ty tySk body bodySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q body ty) }
  addVis (x, q)
  addLemma q [<] ty

emitCoreTyDef : Site -> String -> Ty -> Skel -> ElabM ()
emitCoreTyDef site x ty tySk = do
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throwAt site.srange "\{site}: duplicate signature name '\{x}'"
    Nothing => pure ()
  after <- oblCount
  kernelAccept "\{site} \{x}"
    (\ksig => kCheckTyDefItem ksig kernelFuel (MkKTyDefArt q [] ty tySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q ty TopTy) }
  addVis (x, q)

wrapLams : Nat -> Elem -> Elem
wrapLams Z e = e
wrapLams (S n) e = PiIntro (wrapLams n e)

||| A skeleton nested under n λ-binders (child 0 each time).
nestSkel : Nat -> Skel -> Skel
nestSkel Z sk = sk
nestSkel (S n) sk = Nd [] [nestSkel n sk]

||| A skeleton nested under n Π-binders on the CODOMAIN side (child 1
||| each time, empty domains).
nestPiSkel : Nat -> Skel -> Skel
nestPiSkel Z sk = sk
nestPiSkel (S n) sk = Nd [] [Nd [] [], nestPiSkel n sk]

||| The skeleton of a right-nested Π-chain, given each DOMAIN's skeleton
||| (the result type gets an empty node).
piChainSkel : List Skel -> Skel
piChainSkel [] = Nd [] []
piChainSkel (d :: ds) = Nd [] [d, piChainSkel ds]

applyChain : Elem -> List Elem -> Elem
applyChain = foldl PiApp

||| Σ's open-entry census: (constraints, declarations).
openCensus : ElabM (Nat, Nat)
openCensus = do
  st <- getSt
  pure (length (oblView st), length (declView st))

||| The per-item echo suffix: what this item left OPEN — the ⋆-payment
||| and declarations a reader would otherwise only discover in the
||| end-of-run report. "defined boom [+1 declaration]" is an honest receipt;
||| a bare "defined boom" for an item that just assumed ¬⊤'s realizer
||| reads like success.
opensSuffix : (before : (Nat, Nat)) -> ElabM String
opensSuffix (ob, hb) = do
  (o', h') <- openCensus
  let o = minus o' ob
  let h = minus h' hb
  let parts = the (List String)
                ((if o == 0 then [] else ["+\{show o} obligation\{plural o}"]) ++
                 (if h == 0 then [] else ["+\{show h} declaration\{plural h}"]))
  pure (case parts of
          [] => ""
          _ => " [" ++ joinBy ", " parts ++ "]")
 where
  plural : Nat -> String
  plural 1 = ""
  plural _ = "s"

||| The IMPLICIT positions of an item type's leading Π-telescope: the
||| {x : A} binders (docs/NovaPerfectSurface.txt, Phase 3). Positions
||| index the syntactic telescope, matching the core teleOf 1:1 (both
||| e-ty-pi cases are structural).
impPositions : STy -> List Nat
impPositions = go 0
 where
  go : Nat -> STy -> List Nat
  go i ty = case unPosTy ty of
    STyPi _ _ b => go (S i) b
    STyImpPi _ _ b => i :: go (S i) b
    _ => []

||| Register an accepted item's implicit positions, if any.
registerImps : String -> STy -> ElabM ()
registerImps q ty = case impPositions ty of
  [] => pure ()
  ps => modifySt $ { impls $= ((q, ps) ::) }

||| One-shot elaboration of an item (the body of elabItem below).
elabItemGo : (irng : Maybe Range) -> SItem -> ElabM String

||| Elaborate an item under the searchless default scope: hypotheses
||| and computation only, unless the def's using-clause overrides it
||| (the SDef handler installs the resolved names over this).
||| NOVA_GLOBAL_STORE=1 restores the historical whole-store search.
export
elabItem : (irng : Maybe Range) -> SItem -> ElabM String
elabItem irng item = withScope (if scopedMode then Just [] else Nothing) $ do
  modifySt { curItem := clearBlocked (itemName item) }
  pre <- getSt
  timedM "item \{pre.modPrefix}.\{itemName item}" (elabItemGo irng item)

elabItemGo irng (SDef x ty body muses) = do
  census <- openCensus
  st <- getSt
  -- the Σ-name is qualified by the module; the root file's entries
  -- stay bare
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throwAt irng "def \{x}: duplicate signature name"
    Nothing => pure ()
  -- the item's discharge scope: its using-clause if it has one; under
  -- NOVA_SCOPED, an unannotated item sees hypotheses and computation
  -- only (the searchless default — SearchlessElaboration.md §5.3);
  -- otherwise the full store (the historical behavior)
  scEqs <- the (ElabM (Maybe (List String), List String)) $ case muses of
          Just ns => do
            (rs, eqs) <- resolveUsingNames (MkSite "def \{x}" irng) ns
            pure (Just rs, eqs)
          Nothing => pure (if scopedMode then Just [] else Nothing, [])
  let (sc, eqs) = scEqs
  -- items live in the EMPTY context: parameters are Π-binders in the
  -- item's type, references are bare names
  (ty', tySk) <- withScope sc (withEqScope eqs (elabTy [<] [<] (MkSite "def \{x}" irng) ty))
  (body', bodySk) <- withScope sc (withEqScope eqs (checkElem [<] [<] (MkSite "def \{x}" irng) body ty'))
  -- clean means the RUN is clean: an earlier item's assumption poisons
  -- everything after it (the kernel Σ cannot contain the earlier item,
  -- so references to it are unresolvable anyway)
  after <- oblCount
  kernelAccept "def \{x}"
    (\ksig => kCheckDefItem ksig kernelFuel (MkKDefArt q [] ty' tySk body' bodySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q body' ty') }
  addVis (x, q)
  addLemma q [<] ty'
  registerImps q ty
  suffix <- opensSuffix census
  pure "defined \{x}\{suffix}"
elabItemGo irng (SDeclDef nrng x ty) = do
  -- a DECLARATION (docs/NovaFoundation.txt, sig-decl at ε): a stuck
  -- named entry — reported as open, blocking acceptance; references
  -- type by el-sig-decl. The remedy is supplying the definiens (or importing a
  -- module that will, once such a mechanism exists).
  census <- openCensus
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throwAt irng "def \{x}: duplicate signature name"
    Nothing => pure ()
  (ty', tySk) <- elabTy [<] [<] (MkSite "def \{x}" irng) ty
  modifySt $ { sig $= (:< SigDecl [<] q ty')
             , declMeta $= (:< MkDeclMeta q [<] "def \{x}" st.modFile nrng) }
  addVis (x, q)
  -- a DECLARED equation is a lemma like any accepted one: its stuck
  -- reference is a proof element (el-sig-decl), so el-reflect makes
  -- the equation judgementally available — that is what an abstract
  -- interface's equational axioms are FOR
  addLemma q [<] ty'
  registerImps q ty
  suffix <- opensSuffix census
  pure "declared \{x}\{suffix}"
elabItemGo irng (STypeDef x ty) = do
  census <- openCensus
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throwAt irng "type \{x}: duplicate signature name"
    Nothing => pure ()
  (ty', tySk) <- elabTy [<] [<] (MkSite "type \{x}" irng) ty
  after <- oblCount
  kernelAccept "type \{x}"
    (\ksig => kCheckTyDefItem ksig kernelFuel (MkKTyDefArt q [] ty' tySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q ty' TopTy) }
  addVis (x, q)
  suffix <- opensSuffix census
  pure "defined type \{x}\{suffix}"
elabItemGo irng (SData params decls) = do
  census <- openCensus
  let site = MkSite ("data " ++ (case decls of
                                   (d :: _) => d.dqname
                                   [] => "")) irng
  case decls of
    [] => throwAt site.srange "\{site}: empty data literal"
    _ => pure ()
  -- 0. the ambient PARAMETER telescope (Foundation's Γ ⊦ 𝒮 qsig): the
  --    signature is elaborated OVER it, and every emitted def is
  --    Π-abstracted over it
  (pctx, penv, ptys) <- elabParams site [<] [<] params
  -- 1. elaborate the literal to a core signature, entry by entry; the
  --    parser already resolved names to ⬡-indices and classified the
  --    domains, so the only content is the embedded Nova pieces
  sg <- traverse (elabDecl site pctx penv) decls
  -- 2. EXPANSION: the batch of ordinary defs (docs/NovaElaboration.txt,
  --    QIIT section) — code-valued sorts, saturated constructors,
  --    ⋆ path-lemmas, one eliminator per sort with coherences as
  --    ≡-typed hypotheses. `sgAt d` is the signature under d binders
  --    ABOVE the parameters (its free parameter references weakened).
  let pre = (length params, ptys)
  let named = zipWithIndex 0 decls
  ignore $ traverse (\(k, d) =>
    case qEntryKind (fromMaybe QU (qEntry sg k)) of
      QKSort => do emitSort site pre sg k d.dqname
                   emitElim site pre sg k False d.dqname
                   emitElim site pre sg k True d.dqname
      QKPoint => emitCtor site pre sg k d.dqname
      QKEq => emitEq site pre sg k d.dqname) named
  -- 3. RECORD what the expansion named, per sort: the shapes are in
  --    the carried signature, but the names this item minted — and the
  --    binder names it wrote — are nowhere else. In-place elimination
  --    reads them to apply the generated eliminator.
  st <- getSt
  let qual : String -> String
      qual x = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  let kindOf : Nat -> QEntryKind
      kindOf k = qEntryKind (fromMaybe QU (qEntry sg k))
  let atKind : QEntryKind -> (SQDecl -> a) -> List a
      atKind want f = mapMaybe (\(k, d) => case (kindOf k, want) of
                                             (QKSort, QKSort)   => Just (f d)
                                             (QKPoint, QKPoint) => Just (f d)
                                             (QKEq, QKEq)       => Just (f d)
                                             _ => Nothing) named
  let sortNames = atKind QKSort (\d => qual d.dqname)
  let points = atKind QKPoint ctorOf
  let eqs = atKind QKEq ctorOf
  let sorts = atKind QKSort id
  modifySt $ { qiits $= \acc => foldl (:<) acc
                 (map (\(i, d) =>
                    MkQIITInfo (qual d.dqname) (length params) (length d.dqbinders)
                               sortNames i points eqs)
                      (zipWithIndex 0 sorts)) }
  suffix <- opensSuffix census
  pure ("defined data (" ++ joinBy ", " (map (.dqname) decls) ++ ")" ++ suffix)
 where
  ||| A constructor's arguments, in order: an inductive one (a code
  ||| domain) is followed by its induction hypothesis in the method's
  ||| telescope, so the two are recorded as one entry.
  ctorOf : SQDecl -> QIITCtor
  ctorOf d = MkQIITCtor d.dqname
               (map (\(x, dom) => MkQIITArg x (either (const False) (const True) dom)) d.dqbinders)

  zipWithIndex : Nat -> List a -> List (Nat, a)
  zipWithIndex _ [] = []
  zipWithIndex i (x :: xs) = (i, x) :: zipWithIndex (S i) xs

  elabParams : Site -> Ctx -> NameEnv -> List (String, STy)
            -> ElabM (Ctx, NameEnv, List Ty)
  elabParams site ctx env [] = pure (ctx, env, [])
  elabParams site ctx env ((x, t) :: rest) = do
    (t', _) <- elabTy ctx env site t
    (ctx', env', tys) <- elabParams site (ctx :< t') (env :< x) rest
    pure (ctx', env', t' :: tys)

  sgAt : QSig -> Nat -> QSig
  sgAt sg d = substQSig sg (wkN d)

  wrapParams : List Ty -> Ty -> Ty
  wrapParams ptys ty = foldr PiTy ty ptys

  elabSQTm : Site -> Ctx -> NameEnv -> SQTm -> ElabM QTm
  elabSQTm site ectx env (SQVar _ i) = pure (QVar i)
  elabSQTm site ectx env (SQAppE f e) = do
    f' <- elabSQTm site ectx env f
    -- external arguments elaborate by INFERENCE (they are neutral in
    -- the emitted fragment); the kernel re-checks them at the arity
    (e', _, _) <- inferElem ectx env site e
    pure (QAppE f' e')
  elabSQTm site ectx env (SQAppI f a) =
    [| QAppI (elabSQTm site ectx env f) (elabSQTm site ectx env a) |]

  elabDecl : Site -> Ctx -> NameEnv -> SQDecl -> ElabM QTy
  elabDecl site pctx penv d = go pctx penv d.dqbinders
   where
    go : Ctx -> NameEnv -> List (String, Either STy SQTm) -> ElabM QTy
    go ectx env ((x, Left t) :: rest) = do
      (t', _) <- elabTy ectx env site t
      QPiExt t' <$> go (ectx :< t') (env :< x) rest
    go ectx env ((x, Right q) :: rest) = do
      q' <- elabSQTm site ectx env q
      QPiInd q' <$> go ectx env rest
    go ectx env [] = case d.dqres of
      SQResU => pure QU
      SQResEl q => QEl <$> elabSQTm site ectx env q
      SQResEq l r u => do
        l' <- elabSQTm site ectx env l
        r' <- elabSQTm site ectx env r
        u' <- elabSQTm site ectx env u
        pure (QEl (QEqC l' r' u'))

  entryAt : Site -> QSig -> Nat -> ElabM QTy
  entryAt site sg k = case qEntry sg k of
    Just e => pure e
    Nothing => throwAt site.srange "\{site}: internal — entry out of range"

  ||| A sort: a code-valued def when the signature is SMALL; for a
  ||| LARGE signature, a type item (nullary sorts only — an indexed
  ||| large family has no closed-item spelling).
  emitSort : Site -> (Nat, List Ty) -> QSig -> Nat -> String -> ElabM ()
  emitSort site (np, ptys) sg k nm = do
    entry <- entryAt site sg k
    (tel, _, _) <- liftQE site (reflTel sg (qwAt k) entry)
    let n = length tel
    st <- getSt
    let isSmall = kQSigSmallB st.sig kernelFuel ([<] <>< ptys) sg
    if isSmall
      then do
        let ty = wrapParams ptys (foldr PiTy UniverseTy tel)
        let body = wrapLams (np + n) (QSort (sgAt sg n) k (varSpine n))
        emitCoreDef site nm ty (Nd [] []) body (Nd [] [])
      else if n == 0 && np == 0
        then emitCoreTyDef site nm (QSort sg k [<]) (Nd [] [])
        else throwAt site.srange "\{site}: an indexed or parameterized sort of a LARGE signature has no closed-item spelling (make the signature small)"

  ||| A point constructor: the saturated former, η-expanded once.
  emitCtor : Site -> (Nat, List Ty) -> QSig -> Nat -> String -> ElabM ()
  emitCtor site (np, ptys) sg k nm = do
    entry <- entryAt site sg k
    ty0 <- liftQE site (reflQTy sg (qwAt k) entry)
    let n = qtyBinders entry
    let body = wrapLams (np + n) (QCtor (sgAt sg n) k (varSpine n))
    emitCoreDef site nm (wrapParams ptys ty0) (Nd [] []) body (Nd [] [])

  ||| An equation constructor: a ⋆-lemma (typed at the equality
  ||| prop), licensed by
  ||| el-qiit-path (a qpath step behind the ⋆'s equation certificate).
  ||| On later
  ||| items this def is an accepted lemma, so the QIIT's imposed
  ||| equations feed discharge through the standard store.
  emitEq : Site -> (Nat, List Ty) -> QSig -> Nat -> String -> ElabM ()
  emitEq site (np, ptys) sg k nm = do
    entry <- entryAt site sg k
    (tel, wEnd, hd) <- liftQE site (reflTel sg (qwAt k) entry)
    (lq, rq, uq) <- liftQE site (eqHead hd)
    lE <- liftQE site (reflTm sg wEnd lq)
    rE <- liftQE site (reflTm sg wEnd rq)
    uT <- liftQE site (reflCodeTy sg wEnd uq)
    let n = length tel
    let ty = wrapParams ptys (foldr PiTy (Elem.EqTy lE rE uT) tel)
    let body = wrapLams (np + n) Star
    let cert = MkECert [MkStep True [] (LPath (sgAt sg n) k (varSpine n)) [] False] FBeta
    emitCoreDef site nm ty (Nd [] []) body (nestSkel (np + n) (Nd [PReflEq cert] []))

  ||| The eliminator def for sort s: motives (code-valued), methods,
  ||| COHERENCES AS HYPOTHESES (≡-typed arguments — extensionality's
  ||| dividend), then the indices and the eliminee. The body is the
  ||| core eliminator; its qcoh certificates replay from the coherence
  ||| binders by el-reflect.
  ||| The eliminator def for sort s. Two flavors: prop=False is the
  ||| code-valued one (motives … → 𝕌, coherences as prop-typed
  ||| hypothesis binders); prop=True is the Ω-valued one (motives
  ||| … → Ω, results the props themselves) — by proof irrelevance its
  ||| coherences hold outright (el-prf-prop), so it takes NO
  ||| coherence arguments and its qcoh certificates are bare FProp.
  emitElim : Site -> (Nat, List Ty) -> QSig -> Nat -> (prop : Bool) -> String -> ElabM ()
  emitElim site (np, ptys) sg s prop nm = do
    let sortPs = qPositions QKSort sg
    let pointPs = qPositions QKPoint sg
    let eqPs = qPositions QKEq sg
    let nS = length sortPs
    let nM = length pointPs
    let nH = if prop then 0 else length eqPs
    sEntry <- entryAt site sg s
    (sTel0, _, _) <- liftQE site (reflTel sg (qwAt s) sEntry)
    let nI = length sTel0
    -- Prf retired: 𝕌- and Ω-valued motives alike stand bare (a code
    -- or a prop is its type)
    let wrapMot : Elem -> Ty
        wrapMot = id
    let motEnd : Ty
        motEnd = if prop then PropTy else UniverseTy
    -- motive TYPES as seen `extra` binders after the LAST motive
    -- binder: C_j's index there is (nS-1-j) + extra, plus (arity_j + 1)
    -- inside the motive's own context (arity binders then the eliminee)
    let motTysAt : Nat -> ElabM (List Ty)
        motTysAt extra = traverse (\p =>
            case p of
              (j, sj) => do
                sjE <- entryAt site sg sj
                (telJ, _, _) <- liftQE site (reflTel sg (qwAt sj) sjE)
                let aj = length telJ
                let cIdx = minus nS (S j) + extra + aj + 1
                let idxVars = toList (substSubNorm (varSpine aj) Wk)
                pure (wrapMot (PiApp (applyChain (CtxVar cIdx) idxVars) (CtxVar 0))))
          (zipWithIndex 0 sortPs)
    -- method binder i, seen `extra` binders after the last motive:
    let mVarsAt : Nat -> List Elem
        mVarsAt extra = map (\i => CtxVar (minus extra (S i))) (upto nM)
    -- 1. motive binder types (closed but for the signature)
    cTys <- traverse (\p => case p of
              (j, sj) => do
                -- the j-th motive binder sits j binders above the
                -- parameters: the carried signature weakens along —
                -- and the ENTRY must be read from the weakened
                -- signature, or its embedded Nova pieces (an index
                -- domain mentioning a parameter) keep raw indices
                let sgJ = sgAt sg j
                sjE <- entryAt site sgJ sj
                (telJ, wEndJ, _) <- liftQE site (reflTel sgJ (qwAt sj) sjE)
                let aj = length telJ
                pure (foldr PiTy
                        (PiTy (QSort (substQSig sgJ wEndJ.ups) sj (varSpine aj)) motEnd)
                        telJ))
            (zipWithIndex 0 sortPs)
    -- 2. method binder types (at extra = j)
    mTys <- traverse (\p => case p of
              (j, cj) => do
                mots <- motTysAt j
                liftQE site (methodTy (sgAt sg (nS + j)) mots cj))
            (zipWithIndex 0 pointPs)
    -- 3. coherence binder types (code flavor only; at extra = nM + j).
    -- The two sides of the coherence ≡ have types equal only
    -- JUDGEMENTALLY (C[⌊l⌋] ≐ C[⌊r⌋] by el-qiit-path), so the rhs
    -- position carries a SWITCH certificate whose single step is a
    -- path license rewriting ⌊r⌋ back to ⌊l⌋ inside the inferred type.
    hTysSk <- if prop then pure (the (List (Ty, Skel)) []) else
              traverse (\p => case p of
              (j, ej) => do
                mots <- motTysAt (nM + j)
                let sgJ = sgAt sg (nS + nM + j)
                (dtel, spineArgs, lhs, rhs, cty) <- liftQE site (coherenceAt sgJ mots (mVarsAt (nM + j)) ej)
                let dlen = length dtel
                -- path [1]: the rhs argument of the (bare, El retired)
                -- motive application C ī ⌊r⌋
                let swc = MkECert [MkStep True [1] (LPath (sgAt sgJ dlen) ej spineArgs) [] True] FBeta
                -- the ≡-TYPE IS the eq-prop (Prf retired): children
                -- l, r and the carried type
                let eqSk = Nd [] [Nd [] [], Nd [PSwitch swc] [], Nd [] []]
                pure (foldr PiTy (Elem.EqTy lhs rhs cty) dtel, nestPiSkel dlen eqSk))
            (zipWithIndex 0 eqPs)
    let hTys = map (\x => fst {a=Ty} {b=Skel} x) hTysSk
    let hSks = map (\x => snd {a=Ty} {b=Skel} x) hTysSk
    -- 4. indices (the target sort's arity, at their depth above the
    --    parameters) and the eliminee
    sEntryW <- entryAt site (sgAt sg (nS + nM + nH)) s
    (sTel, _, _) <- liftQE site (reflTel (sgAt sg (nS + nM + nH)) (qwAt s) sEntryW)
    let wTy = QSort (sgAt sg (nS + nM + nH + nI)) s (varSpine nI)
    -- result: C_s idx w through the flavor's decoding — C_s under
    -- everything
    ordS <- case qOrdinal QKSort sg s of
              Just o => pure o
              Nothing => throwAt site.srange "\{site}: internal — sort ordinal"
    let cS = minus nS (S ordS) + nM + nH + nI + 1
    let idxAtEnd = toList (substSubNorm (varSpine nI) Wk)
    let resTy = wrapMot (PiApp (applyChain (CtxVar cS) idxAtEnd) (CtxVar 0))
    let defTy = wrapParams ptys
                  (foldr PiTy resTy (cTys ++ mTys ++ hTys ++ sTel ++ [wTy]))
    let emptySk = the Skel (Nd [] [])
    let defTySk = nestPiSkel np (piChainSkel
                    (map (const emptySk) cTys ++ map (const emptySk) mTys ++
                     hSks ++ map (const emptySk) sTel ++ [emptySk]))
    -- body: λ^N (𝒮.s-elim ℰ ē w)
    let endExtra = nM + nH + nI + 1
    motsEnd <- motTysAt endExtra
    let mthsEnd = mVarsAt endExtra
    let bigN = nS + nM + nH + nI + 1
    let body = wrapLams (np + bigN)
                 (QElim (sgAt sg bigN) s motsEnd mthsEnd (cast idxAtEnd) (CtxVar 0))
    -- coherence certificates. Code flavor: each replays from its
    -- hypothesis binder, applied to the ᴰ-context's variables (one
    -- step, then FBeta). Prop flavor: the coherence sides live at an
    -- Ω-valued motive, so proof irrelevance closes them outright
    -- (FProp).
    cohCerts <- if prop
      then pure (map (const (MkECert [] FProp)) eqPs)
      else traverse (\p => case p of
                  (j, ej) => do
                    (dtel, _, _, _, _) <- liftQE site (coherenceAt (sgAt sg bigN) motsEnd mthsEnd ej)
                    let dlen = length dtel
                    let hIdx = minus nH (S j) + nI + 1 + dlen
                    let dVars = map CtxVar (reverse (upto dlen))
                    pure (MkECert [MkStep True [] (LProof (applyChain (CtxVar hIdx) dVars)) [] False] FBeta))
                (zipWithIndex 0 eqPs)
    let bodySk = nestSkel (np + bigN) (Nd [PQCoh cohCerts] [])
    emitCoreDef site (nm ++ (if prop then "ElimP" else "Elim")) defTy defTySk body bodySk
   where
    upto : Nat -> List Nat
    upto Z = []
    upto (S n) = upto n ++ [n]

elabItemGo irng (SCopatternDef nrng x ty muses etaName witness cargs crhs cname) = do
  -- a def with a DEFINING OBSERVATION (docs/NovaElaboration.txt,
  -- "Defining observations"): the clausal def's dual. Stage 1 is
  -- pure ALIGNMENT (Nova.Elaboration.Clauses): LHS arguments against
  -- the item's columns per the term-syntax placement conventions.
  -- Stage 2 is the PROBE, against a state snapshot so it leaves no
  -- trace: the type elaborated and its head exposed to ν 𝔽 under the
  -- item's own using licenses (the shape is the one input the
  -- surface cannot provide), and — when the body's calls carry
  -- ELIDED implicit arguments — the clause RHS elaborated once with
  -- the item pre-declared, so the analysis reads the
  -- insertion-RESOLVED spines: an elided argument that resolved away
  -- from its ambient column variable has no surface spelling for the
  -- seed, and the expansion degrades with a spell-it remedy. Stage 3
  -- is the pure expansion; the batch elaborates through the ordinary
  -- item pipeline.
  census <- openCensus
  al <- either (\e => throwAt irng "def \{x}: \{e}") pure (copatternAlign x ty cargs crhs)
  let k = length al.ccols
  st0 <- getSt
  scEqs <- the (ElabM (Maybe (List String), List String)) $ case muses of
          Just ns => do
            (rs, eqs) <- resolveUsingNames (MkSite "def \{x}" irng) ns
            pure (Just rs, eqs)
          Nothing => pure (if scopedMode then Just [] else Nothing, [])
  let (sc, eqs) = scEqs
  (pol, elidedBad) <- withScope sc (withEqScope eqs (do
           (ty', _) <- elabTy [<] [<] (MkSite "def \{x}" irng) ty
           (pol, ctxK) <- nuHead [<] k ty'
           bad <- probeElided al k ty' pol ctxK
           pure (pol, bad)))
  modifySt (const st0)
  case expandCopattern nrng x ty muses etaName witness al cname pol elidedBad of
    Left err => throwAt irng "def \{x}: \{err}"
    Right (MkExpansion items echo) => do
      -- the batch elaborates under the item's scope so the
      -- DECLARATION tier's types see its exposure licenses (an SDef
      -- of the batch installs its own generated scope over this);
      -- each batch item is its OWN item for anything keyed by the
      -- item name, exactly as at the clausal def below
      ignore $ withScope sc (withEqScope eqs (traverse (\(r, it) => do
        modifySt { curItem := clearBlocked (itemName it) }
        elabItemGo (r <|> irng) it) items))
      suffix <- opensSuffix census
      pure (echo ++ suffix)
 where
  ||| Peel the copattern's columns off the elaborated type (returning
  ||| the column context), then expose the head to its ν 𝔽 (whnf
  ||| through cited unfold licenses — the corpus idiom of naming the
  ||| head type's definition in the item's using clause).
  nuHead : Ctx -> Nat -> Ty -> ElabM (Poly, Ctx)
  nuHead ctx Z headTy = do
    st <- getSt
    case preferNu st ctx headTy of
      Just (p, _) => pure (p, ctx)
      Nothing => throwAt irng ("def \{x}: the copattern's head type does not expose a ν-type"
                        ++ " (cite the type definition's .unfold name in the item's using clause)")
  nuHead ctx (S n) piTy = do
    st <- getSt
    case preferPi st ctx piTy of
      Just (a, b, _) => nuHead (ctx :< a) n b
      Nothing => throwAt irng ("def \{x}: the copattern spells more argument positions"
                        ++ " than the item's type shows Π-columns")

  ||| Verify the ELIDED implicit call arguments against the
  ||| insertion-resolved core body: each must be its ambient column
  ||| variable. Runs only for fragment-shaped bodies whose calls
  ||| elide something; runs under probeM, so a failing elaboration
  ||| leaves no trace and no verdict (the real pipeline reports it).
  probeElided : CoAligned -> Nat -> Ty -> Poly -> Ctx -> ElabM (Maybe String)
  probeElided al k ty' pol ctxK =
    case copatternProbeCalls x al.ccols pol al.crhsFull of
      Nothing => pure Nothing
      Just masks =>
        if not (any (\(_, m) => any id m) masks) then pure Nothing else do
          r <- probeM (do
                 -- the item is pre-declared under a MACHINE name
                 -- (aliased for the body's bare references), never its
                 -- real one: the global Σ-entry name index caches
                 -- positively on first lookup, and a cached probe
                 -- DECLARATION under the real name would shadow the
                 -- batch's later definition for every unfold
                 -- (sigEntryIx's stability invariant — Σ only extends)
                 let pq = "probe#" ++ x
                 modifySt $ { sig $= (:< SigDecl [<] pq ty') }
                 addVis (x, pq)
                 registerImps pq ty
                 let env = [<] <>< map (fst . cnm) al.ccols
                 (rhsC, _) <- checkElem ctxK env (MkSite "def \{x}" irng) al.crhsFull
                                (reflectPoly pol (Elem.NuTy pol))
                 pure (pq, rhsC))
          pure $ case r of
            Nothing => Nothing
            Just (pq, rhsC) =>
              case coreHoleCalls pq pol 0 rhsC of
                Nothing => Just "internal: the elaborated body's shape disagrees with the analysis"
                Just cores => checkPairs masks cores
   where
    badAt : (d : Nat) -> Nat -> List Bool -> List Elem -> Maybe Nat
    badAt d c [] _ = Nothing
    badAt d c (True :: ms) (a :: as) =
      if a == CtxVar (d + minus k c) then badAt d (S c) ms as else Just c
    badAt d c (False :: ms) (_ :: as) = badAt d (S c) ms as
    badAt d c _ [] = Just c
    checkPairs : List (Nat, List Bool) -> List (Nat, List Elem) -> Maybe String
    checkPairs [] [] = Nothing
    checkPairs ((d, m) :: ms) ((d', args) :: cs) =
      if d /= d' || length args /= k
        then Just "internal: the elaborated body's calls disagree with the analysis"
        else case badAt d 1 m args of
               Just c =>
                 let nm = maybe "?" (fst . cnm) (getAt (minus c 1) al.ccols)
                 in Just ("the elided implicit argument {\{nm}} of a corecursive call varies — spell it at the call")
               Nothing => checkPairs ms cs
    checkPairs _ _ = Just "internal: the elaborated body's calls disagree with the analysis"

elabItemGo irng (SClausalDef nrng x ty muses etaName witness clauses) = do
  -- a def with DEFINING EQUATIONS (docs/NovaElaboration.txt,
  -- "Defining equations"): an ITEM MACRO. The expansion is pure
  -- surface-level synthesis (Nova.Elaboration.Clauses); the batch —
  -- the definition, the Π-closed clause lemmas, the uniqueness
  -- lemma — elaborates through the ordinary item pipeline, so
  -- obligations, lemma registration, kernel checking and the report
  -- need no clause awareness at all. A Left is a STRUCTURAL error;
  -- everything non-structural degrades inside the expansion (witness
  -- tier / declaration tier) rather than failing. Unlike the
  -- copattern macro, no probe runs: elided implicit call arguments
  -- read as the ambient columns, VERIFIED by the clause lemmas'
  -- β-discharge (a wrong reading is an obligation, never a wrong
  -- acceptance).
  census <- openCensus
  scEqs <- the (ElabM (Maybe (List String), List String)) $ case muses of
          Just ns => do
            (rs, eqs) <- resolveUsingNames (MkSite "def \{x}" irng) ns
            pure (Just rs, eqs)
          Nothing => pure (if scopedMode then Just [] else Nothing, [])
  let (sc, eqs) = scEqs
  case expandClausal nrng x ty muses etaName witness clauses of
    Left err => throwAt irng "def \{x}: \{err}"
    Right (MkExpansion items echo) => do
      -- each batch item is its OWN item for anything keyed by the
      -- item name: the profile labels, and the Σ names a hole is
      -- minted under (a `?x` written in a clause RHS is elaborated
      -- once in the definition body and once in that clause's
      -- equation lemma — two goals, so two entries, not a name
      -- collision). `elabItem` re-sets this at the next real item.
      -- The batch also elaborates under the ITEM's scope, so the
      -- DECLARATION tier's types see its exposure licenses (an SDef
      -- of the batch installs its own generated scope over this)
      ignore $ withScope sc (withEqScope eqs (traverse (\(r, it) => do
        modifySt { curItem := clearBlocked (itemName it) }
        elabItemGo (r <|> irng) it) items))
      suffix <- opensSuffix census
      pure (echo ++ suffix)

-- ===== Report =====

prettyTelescope : FixTable -> Ctx -> NameEnv -> String
prettyTelescope tbl ctx env = go (toList ctx) (toList env)
 where
  -- A LET leaves TWO entries behind (el-let: the value, then its
  -- unfolding equation ☐₀ ≡ e[↑] ∈ A[↑], minted anonymous by
  -- e-let). The source wrote ONE binding, so the report prints one:
  -- the definiens is read back off the equation and shown in the
  -- annotated-let order. Recognized by SHAPE, so a hand-written
  -- hypothesis of that shape folds too — it says the same thing.
  -- Without this a nested let, or an in-place Σ split, doubles the
  -- context of every goal after it.
  letFold : (bnd : Ty) -> (hyp : Ty) -> (hypName : String) -> Maybe Elem
  letFold bnd (Elem.EqTy (CtxVar 0) rhs hty) hypName =
    if hypName == wildcard && hty == substTy bnd Wk then Just rhs else Nothing
  letFold _ _ _ = Nothing

  -- print left-to-right; each entry's type prints under the env prefix
  go' : SnocList String -> List Ty -> List String -> List String
  go' pfx [] _ = []
  go' pfx (ty :: hyp :: tys) (n :: h :: ns) =
    case letFold ty hyp h of
      -- the definiens lives one binder in (e[↑]), so it prints under
      -- the prefix the BOUND name extends — the same env the
      -- equation entry itself would have printed under
      Just rhs =>
        "(\{n} : \{prettyTyN tbl pfx ty} ≔ \{prettyElemN tbl (pfx :< n) rhs})"
          :: go' (pfx :< n :< h) tys ns
      Nothing =>
        "(\{n} : \{prettyTyN tbl pfx ty})" :: go' (pfx :< n) (hyp :: tys) (h :: ns)
  go' pfx (ty :: tys) (n :: ns) =
    "(\{n} : \{prettyTyN tbl pfx ty})" :: go' (pfx :< n) tys ns
  go' pfx (ty :: tys) [] =
    "(_ : \{prettyTyN tbl pfx ty})" :: go' (pfx :< "_") tys []

  go : List Ty -> List String -> String
  go tys ns = joinBy " " (go' [<] tys ns)

prettyStmt : FixTable -> Stmt -> String
prettyStmt tbl (StElem ctx env a b ty) =
  let tele = prettyTelescope tbl ctx env in
  (if tele == "" then "" else tele ++ " ") ++
  "⊢ \{prettyElemN tbl env a} ≐ \{prettyElemN tbl env b} : \{prettyTyN tbl env ty}"
prettyStmt tbl (StTy ctx env a b) =
  let tele = prettyTelescope tbl ctx env in
  (if tele == "" then "" else tele ++ " ") ++
  "⊢ \{prettyTyN tbl env a} ≐ \{prettyTyN tbl env b} type"

||| Exported (unlike the rest of this obligation-printing family) so
||| an LSP consumer can render one `Obligation` from `ElabReport`
||| without needing `Obligation`/`Stmt` themselves to be public.
export
prettyObligation : FixTable -> Nat -> Obligation -> String
prettyObligation tbl i obl =
  "  [\{show (S i)}] \{prettyStmt tbl obl.stmt}\n" ++
  "      at: \{oblLoc}\{obl.site}" ++
  (case obl.composite of
     Nothing => ""
     Just c => "\n      from composite: \{prettyStmt tbl c}") ++
  (case obl.hint of
     Nothing => ""
     Just h => "\n      hint: \{h}")
 where
  -- an obligation the elaborator localized inside its item gets a
  -- jumpable "file:line:col: " prefix; one it could not stays bare
  oblLoc : String
  oblLoc = case obl.site.srange of
    Just r => "\{showLoc obl.file r}: "
    Nothing => ""

||| One module of a program: its dotted name ("" for the root file,
||| whose entries stay unqualified), its import lines, its items.
public export
record ModUnit where
  constructor MkModUnit
  mname : String
  ||| the file the module was read from, spelled as the loader
  ||| resolved it — a diagnostic's location prefix
  mpath : String
  mimports : List SImport
  ||| the module's EFFECTIVE fixity table (opened imports' + own
  ||| declarations) — the printer's, for faithful infix layout
  mfix : FixTable
  ||| each item paired with its source range (item-level granularity —
  ||| see `Nova.Elaboration.Parser.parseSFile`), for LSP diagnostics
  mitems : List (Maybe Range, SItem)
  ||| every classified token span in the module's source, for LSP
  ||| semantic tokens (see `Nova.Elaboration.Parser.runSurfaceParser`)
  mtokens : SnocList (Range, TokenKind)
  ||| the file body in source order — fixity declarations and items
  ||| interleaved, exactly as written. The DISTILL printer's input
  ||| (docs/NovaPerfectSurface.txt); elaboration never reads it
  mbody : List SBodyEntry
  ||| the module's SOURCE TEXT — comments never reach the AST (the
  ||| lexer strips them), so the distiller re-slices them from here by
  ||| the ranges mtokens records; elaboration never reads it
  msrc : String

oblReport : FixTable -> List Obligation -> String
oblReport tbl os =
  "open obligations (\{show (length os)}):\n" ++
  joinBy "\n" (zipWith (prettyObligation tbl) [0 .. minus (length os) 1] os)

||| The JUDGEMENT alone — context, turnstile, goal — with no label
||| bracket and no location. What a HOVER shows, since the operator is
||| already standing at the thing and the label is the token under the
||| cursor. `prettyDecl` is this plus the report's framing.
export
prettyGoal : FixTable -> DeclView -> String
prettyGoal tbl h =
  let tele = prettyTelescope tbl h.dvctx h.dvenv in
  (if tele == "" then "" else tele ++ " ") ++
  (case h.dvty of
     Just ty => "⊢ \{goalName h} : \{prettyTyN tbl h.dvenv ty}"
     Nothing => "⊢ \{goalName h} type")
 where
  -- a HOLE shows the label the operator wrote (`?a`), not the
  -- run-unique Σ name it was minted under (`?mod.item.a`); a
  -- declaration shows an anonymous `?` goal
  goalName : DeclView -> String
  goalName d = if isHoleName d.dvname then holeLabel d.dvname else "?"

||| Render one declaration for the report (exported for LSP consumers,
||| like prettyObligation).
export
prettyDecl : FixTable -> DeclView -> String
prettyDecl tbl h =
  "  [\{label}] " ++ prettyGoal tbl h ++ "\n      at: \{declLoc}\{h.dvsite}"
 where
  label : String
  label = if isHoleName h.dvname then holeLabel h.dvname else h.dvname

  declLoc : String
  declLoc = case h.dvrange of
    Just r => "\{showLoc h.dvfile r}: "
    Nothing => ""

declReport : FixTable -> List DeclView -> String
declReport tbl hs =
  "open declarations (\{show (length hs)}):\n" ++
  joinBy "\n" (map (prettyDecl tbl) hs)

||| Holes are declarations too (same Σ entry kind), but they are the
||| operator's OWN markers rather than an abstract interface's — they
||| get their own block so a hole-driven session reads its goals
||| without the axioms in the way.
holeReport : FixTable -> List DeclView -> String
holeReport tbl hs =
  "open holes (\{show (length hs)}):\n" ++
  joinBy "\n" (map (prettyDecl tbl) hs)

||| An obligation the refinement DISCHARGED: filling in the synthetic
||| holes the run's own constraints determine made both sides the same
||| term. It said what a hole was, the hole now says it, and repeating
||| it as an open obligation would be noise.
oblDischarged : Obligation -> Bool
oblDischarged o = case o.stmt of
  StElem _ _ a b _ => a == b
  StTy _ _ a b => a == b

||| A synthetic hole the refinement FILLED IN is no longer open — its
||| value is what the goals that mention it now show.
declSolved : ElabSt -> DeclView -> Bool
declSolved st h = isSyntheticHole h.dvname && isJust (lookup h.dvname st.holeSols)

||| The composed end-of-run report of everything keeping Σ
||| non-definitional; empty exactly when the run is accepted.
openReport : FixTable -> ElabSt -> Maybe String
openReport tbl st0 =
  let st = refineHoles st0 in
  case ( filter (not . oblDischarged) (oblView st)
       , partition (isHoleName . dvname)
           (filter (not . declSolved st) (declView st))) of
    ([], ([], [])) => Nothing
    (os, (holes, ds)) => Just $ joinBy "\n"
      ((case holes of [] => []; _ => [holeReport tbl holes]) ++
       (case os of [] => []; _ => [oblReport tbl os]) ++
       (case ds of [] => []; _ => [declReport tbl ds]))

||| Install a module's import aliases: each opened name must exist in
||| the imported module's Σ segment.
||| Transitive import closure over the finished modules' import lists.
modClosure : List (String, List String) -> List String -> List String
modClosure imps = go (S (length imps)) []
 where
  -- fuel bounds ADDITIONS (at most one per known module, so |imps|+1
  -- suffices); a duplicate skip shrinks the frontier structurally and
  -- must not spend fuel — the frontier holds one entry per MENTION,
  -- and charging skips truncated deep closures (the store-visibility
  -- bug a root with many shared dependencies exposed)
  go : Nat -> List String -> List String -> List String
  go Z acc _ = acc
  go fuel acc [] = acc
  go fuel@(S fuel') acc (m :: ms) =
    if m `elem` acc
      then go fuel acc ms
      else go fuel' (m :: acc) (fromMaybe [] (lookup m imps) ++ ms)

||| Archive the module that just finished and scope the store to the
||| next module's import closure. The visible list is the closure's
||| archives concatenated in newest-module-first order — exactly the
||| flattened order a standalone run of that module produces.
enterModule : (name : String) -> (file : String) -> (fix : FixTable) -> List String -> ElabM ()
enterModule name file fix imps = do
  st <- getSt
  let archived = if st.modPrefix == "" && isNil st.ownLemmas
                   then st.modLemmas
                   else (st.modPrefix, st.ownLemmas) :: st.modLemmas
  let archivedI = (st.modPrefix, st.curImports) :: st.modImports
  let closure = modClosure archivedI imps
  let visible = concatMap (\(_, ls) => ls) (filter (\(m, _) => m `elem` closure) archived)
  let (cs, sh, re, hp) = sigCandParts visible
  putSt $ { modPrefix := name, modFile := file, modFix := fix, vis := [<], dupNames := []
          , lemmas := visible, ownLemmas := []
          , modLemmas := archived, modImports := archivedI
          , curImports := imps
          , candCs := cs, candShrink := sh, candRest := re
          , candHops := hp, candRw := sh ++ re } st

installImports : List SImport -> ElabM ()
installImports [] = pure ()
installImports (MkSImport m opens irng :: rest) = do
  go opens
  installImports rest
 where
  go : List String -> ElabM ()
  go [] = pure ()
  go (o :: os) = do
    st <- getSt
    let q = "\{m}.\{o}"
    case sigLookup q st.sig of
      Just _ => do addVis (o, q); go os
      Nothing => throwAt irng "import \{m}: it defines no '\{o}'"

||| The verdict line of a run that recovered from item failures: the
||| diagnostics themselves are already rendered in place, at their
||| items — this is what stops the run reading as accepted.
failedLine : Nat -> String
failedLine n = "Error: \{show n} item\{if n == 1 then "" else "s"} failed to elaborate"

||| ITEM RECOVERY (docs/NovaElaboration.txt, "Recovery"). An item
||| that fails to elaborate is retried as a bare DECLARATION of its
||| own signature: later items' references to it still resolve, so
||| one broken proof no longer hides every goal after it. The
||| declaration is reported as open and blocks acceptance exactly as
||| a written `def x : T` does, so a failed def can never pass for a
||| definition. Items with no signature to declare (a `data` literal,
||| a declaration that failed on its own type) recover nothing and
||| are simply skipped.
declFallback : Maybe Range -> SItem -> Maybe (Maybe Range, SItem)
declFallback irng (SDef x ty _ _) = Just (irng, SDeclDef irng x ty)
declFallback irng (SClausalDef nrng x ty _ _ _ _) = Just (irng, SDeclDef (nrng <|> irng) x ty)
declFallback irng (SCopatternDef nrng x ty _ _ _ _ _ _) = Just (irng, SDeclDef (nrng <|> irng) x ty)
declFallback _ _ = Nothing

||| The holes a FAILED item had already minted, as report views. Its
||| state never survives — nothing a broken item built reaches Σ —
||| but the goals it reached before it broke are exactly what writing
||| holes is for, so they are rendered at the failure and discarded
||| with everything else. Display only: `before` is what elaboration
||| continues from.
salvagedHoles : (before, after : ElabSt) -> List DeclView
salvagedHoles before after =
  filter (isHoleName . dvname)
    (drop (length (toList before.declMeta)) (declView after))

||| Elaborate a dependency-ordered list of modules (the loader's
||| output; the last unit is the root). Every non-root module must be
||| ACCEPTED — clean and fully kernel-checked — before anything may
||| import it; the root reports its obligations as usual.
export
elabProgram : List ModUnit -> String
elabProgram units = go initSt units [] Z
 where
  finish : FixTable -> ElabSt -> List String -> Nat -> String
  finish tbl st echoes nerrs =
    joinBy "\n" echoes ++ "\n" ++
    (case openReport tbl st of
       Nothing => if nerrs == Z then "Accepted." else failedLine nerrs
       Just rep => if nerrs == Z then rep else rep ++ "\n" ++ failedLine nerrs)

  -- an item's failure is reported AT the item: the diagnostic carries
  -- the file, the item's span and a source excerpt (item-level
  -- granularity — that is as fine as `mitems` records). The run then
  -- CONTINUES (item recovery): the failure is rendered in place,
  -- whatever goals the item reached are rendered with it, the item
  -- falls back to a declaration of its signature, and the next item
  -- elaborates. Errors are counted so acceptance still fails.
  goItems : FixTable -> (path : String) -> (src : String) -> ElabSt
         -> List (Maybe Range, SItem) -> (ElabSt, List String, Nat)
  goItems tbl path src st [] = (st, [], Z)
  goItems tbl path src st ((rng, item) :: rest) =
    case runElabM (elabItem rng item) st of
      -- the elaborator's own span when it narrowed one, the item's
      -- otherwise
      Left (stFail, err) =>
        let diag = render (MkDiag Err (Just path) (Just src)
                             (err.erange <|> rng) (withBlockedHint stFail.sig err.emsg) [])
            salv = case salvagedHoles st stFail of
                     [] => []
                     hs => ["holes reached before the failure (\{show (length hs)}):\n" ++
                            joinBy "\n" (map (prettyDecl tbl) hs)]
            -- the fallback runs from the PRE-item state: nothing the
            -- broken item built is kept
            (stNext, declEcho) =
              case declFallback rng item >>= \(r, it) =>
                     either (const Nothing) Just (runElabM (elabItem r it) st) of
                Just (st2, echo) => (st2, [echo])
                Nothing => (st, [])
            (st'', echoes, n) = goItems tbl path src stNext rest in
        (st'', (diag :: salv) ++ declEcho ++ echoes, S n)
      Right (st', echo) =>
        let (st'', echoes, n) = goItems tbl path src st' rest in
        (st'', echo :: echoes, n)

  go : ElabSt -> List ModUnit -> List String -> Nat -> String
  go st [] echoes nerrs = joinBy "\n" (echoes ++ ["Error: empty program"])
  go st (MkModUnit name path imps tbl items _ _ src :: rest) echoes nerrs = do
    -- a fresh visibility table per module: its own imports only, and a
    -- lemma store scoped to its import closure
    case runElabM (enterModule name path tbl (map mname imps) >> installImports imps) st of
      -- an import failure is NOT item-recoverable: nothing after it
      -- has a signature to elaborate against
      Left (_, err) =>
        if surveyMode && not (null rest)
          -- SURVEY MODE: an import of a dropped module cascades — drop too
          then go st rest (echoes ++ ["warning: module \{name} DROPPED (strict survey): \{err.emsg}"]) (S nerrs)
          else joinBy "\n" (echoes ++ [render (MkDiag Err (Just path) (Just src) err.erange err.emsg [])])
      Right (st, ()) =>
        let hdr = if name == "" then [] else ["module \{name}:"]
            (st', itemEchoes, itemErrs) = goItems tbl path src st items
            nerrs' = nerrs + itemErrs in
        case rest of
          [] => finish tbl st' (echoes ++ hdr ++ itemEchoes) nerrs'
          _ =>
            -- only ACCEPTED modules are importable: a module's
            -- signature segment must be DEFINITIONAL, and no item of
            -- it may have failed (a failed `data` literal leaves no
            -- open entry behind to catch it)
            if surveyMode
              -- SURVEY MODE: continue past the gate so ONE run maps
              -- the whole corpus's fallout. COUNT open entries
              -- instead of rendering the report — the report renders
              -- every accumulated obligation and is quadratic across
              -- modules (the root still renders the full report once)
              then let opens = \s => length (filter (not . sigEntryIsDef) (toList s))
                       d = minus (opens st'.sig) (opens st.sig) in
                   go st' rest (echoes ++ hdr ++ itemEchoes ++
                     (if d == 0 then []
                      else ["warning: module \{name}: +\{show d} open entries (strict survey)"])) nerrs'
              else case (openReport tbl st', itemErrs) of
                (Nothing, Z) => go st' rest (echoes ++ hdr ++ itemEchoes) nerrs'
                (mrep, _) => joinBy "\n" (echoes ++ hdr ++ itemEchoes) ++ "\n" ++
                      (case mrep of Nothing => ""; Just rep => rep ++ "\n") ++
                      "Error: module \{name} has open obligations and cannot be imported"

||| Elaborate a dependency-ordered program to its final kernel Σ,
||| requiring the ENTIRE program — root included — to be accepted with
||| zero obligations: a consumer of the resulting Σ (Nova.Compute, via
||| Nova.Elaboration.Loader.runPath) assumes closed, well-typed input,
||| never a provisional signature built on assumed equations. Same fold
||| as elabProgram/elabProgramReport, shaped for that different
||| consumer instead of a display report.
||| elabProgramSig generalized: run from a SEEDED state (the
||| implicitize trial sets impTrialOn) and return the full final
||| state (kernel Σ, trial records) — same acceptance discipline.
export
elabProgramSt : ElabSt -> List ModUnit -> Either String ElabSt
elabProgramSt st0 units = go st0 units
 where
  goItems : (path : String) -> (src : String) -> ElabSt -> List (Maybe Range, SItem)
         -> Either String ElabSt
  goItems path src st [] = Right st
  goItems path src st ((rng, item) :: rest) =
    case runElabM (elabItem rng item) st of
      Left (stFail, err) => Left (render (MkDiag Err (Just path) (Just src)
                                       (err.erange <|> rng) (withBlockedHint stFail.sig err.emsg) []))
      Right (st', _) => goItems path src st' rest

  go : ElabSt -> List ModUnit -> Either String ElabSt
  go st [] = Left "empty program"
  go st (MkModUnit name path imps tbl items _ _ src :: rest) =
    let st = either (const st) fst (runElabM (enterModule name path tbl (map mname imps)) st) in
    case runElabM (installImports imps) st of
      Left (_, err) => Left (render (MkDiag Err (Just path) (Just src) err.erange err.emsg []))
      Right (st, ()) =>
        case goItems path src st items of
          Left err => Left err
          Right st' =>
            case openReport tbl st' of
              Just rep => Left (rep ++ "\nmodule \{name} has open obligations")
              Nothing  => case rest of
                            [] => Right st'
                            _  => go st' rest

||| Run the program with the implicitize TRIAL on (Phase 3c): on full
||| acceptance, the kernel Σ and the trial records — per
||| {t}-override at an implicit position, whether the hypothetical
||| elided recovery reproduces the written value α-exactly.
export
elabProgramTrial : List ModUnit -> Either String (Sig, List (String, Nat, Nat, Maybe (String, Range)))
elabProgramTrial units =
  map (\st => (st.kernelSig, toList st.impTrial))
      (elabProgramSt ({ impTrialOn := True } initSt) units)

||| Run the program with the Phase-4 SUGAR TRIAL on: on full
||| acceptance, the kernel Σ and the per-site elision verdicts —
||| (module, range of the ∈-annotation or motive binder, elidable).
export
elabProgramSugar : List ModUnit -> Either String (Sig, List (String, Range, Bool), List (String, Range, Nat), List (String, Range, Nat))
elabProgramSugar units =
  map (\st => (st.kernelSig, toList st.svSugar, toList st.svBlank, toList st.svBlankRisk))
      (elabProgramSt ({ svSugarOn := True } initSt) units)

export
elabProgramSig : List ModUnit -> Either String Sig
elabProgramSig units = go initSt units
 where
  goItems : (path : String) -> (src : String) -> ElabSt -> List (Maybe Range, SItem)
         -> Either String ElabSt
  goItems path src st [] = Right st
  goItems path src st ((rng, item) :: rest) =
    case runElabM (elabItem rng item) st of
      Left (stFail, err) => Left (render (MkDiag Err (Just path) (Just src)
                                       (err.erange <|> rng) (withBlockedHint stFail.sig err.emsg) []))
      Right (st', _) => goItems path src st' rest

  go : ElabSt -> List ModUnit -> Either String Sig
  go st [] = Left "empty program"
  go st (MkModUnit name path imps tbl items _ _ src :: rest) =
    let st = either (const st) fst (runElabM (enterModule name path tbl (map mname imps)) st) in
    case runElabM (installImports imps) st of
      Left (_, err) => Left (render (MkDiag Err (Just path) (Just src) err.erange err.emsg []))
      Right (st, ()) =>
        case goItems path src st items of
          Left err => Left err
          Right st' =>
            case openReport tbl st' of
              Just rep => Left (rep ++ "\nmodule \{name} has open obligations")
              Nothing  => case rest of
                            [] => Right st'.kernelSig
                            _  => go st' rest

||| Elaborate a single surface file (no imports — resolving them needs
||| the module loader); the returned string is the complete report.
export
elabFile : String -> String
elabFile content =
  case runSurfaceParser (parseSFile []) content of
    Left pf => render (MkDiag Err Nothing (Just content) pf.pfrange pf.pfmsg pf.pfnotes)
    Right (toks, ([], decls, items, body)) => elabProgram [MkModUnit "" "<input>" [] decls items toks body content]
    Right (_, (_, _, _, _)) => "Error: this entry point resolves no imports (use the module-aware loader)"

||| Structured, range-aware counterpart to `elabProgram` for LSP
||| consumers. `elabProgram`/`elabPath`/`Nova.Application`'s CLI output
||| is untouched by this — same fold, but instead of collapsing to one
||| string, each hard error and each newly-produced `Obligation` is
||| attributed to the enclosing item's range AND its module (item-level
||| granularity, same caveat as `ModUnit.mitems`: no sub-expression
||| precision) — the module name lets an LSP tell "this range belongs
||| to the open document" (mname == "", the root — see
||| `Nova.Elaboration.Loader.loadProgram`) from "this came from an
||| imported file, don't paint this range in MY document".
||| The LSP binder table: the ROOT module's binder occurrences,
||| rendered display-normalized.
||| the leading Π prefix with the referent's implicit positions
||| BRACED — the kernel type has no implicitness, so the hover
||| reintroduces the surface's, binder by binder up to the last
||| implicit, then hands the tail to the ordinary printer
prettyTyImpsN : FixTable -> NameEnv -> List Nat -> Ty -> String
prettyTyImpsN tbl env imps ty = go 0 env ty
 where
  lastImp : Nat
  lastImp = foldl max 0 imps

  go : Nat -> NameEnv -> Ty -> String
  go i env t = case t of
    PiTy a b =>
      if i > lastImp then prettyTyN tbl env t
      else let x = freshForTy a env
               brL = the String (if i `elem` imps then "{" else "(")
               brR = the String (if i `elem` imps then "}" else ")")
           in brL ++ x ++ ":" ++ prettyTyN tbl env a ++ brR ++ " → " ++ go (S i) (env :< x) b
    _ => prettyTyN tbl env t

binderInfos : FixTable -> ElabSt -> List (Range, String)
binderInfos tbl st =
  [ (r, "\{x} : " ++ (case imps of
                        [] => prettyTyN tbl env (displayTy st ty)
                        _ => prettyTyImpsN tbl env imps (displayTy st ty)))
  | (m, r, ctx, env, x, ty, imps) <- toList st.binderTypes, m == "" ]
  ++
  -- blanks ascribe in the language's own def shape — domain, then
  -- the value the oracle recovered — with the binding source as a
  -- comment line
  [ (r, "_ : \{prettyTyN tbl env (displayTy st ty)} ≔ \{prettyElemN tbl env (displayElem st v)}"
        ++ "\n-- " ++ (case msrc of
              Nothing => "solved from the expected type"
              Just sv => "solved from the type of \{prettyElemN tbl env (displayElem st sv)}"))
  | (m, r, env, v, ty, msrc) <- toList st.blankVals, m == "" ]

public export
record ElabReport where
  constructor MkElabReport
  obligations : List (String, Maybe Range, Obligation)
  ||| open declarations, pre-rendered (module, range, report text) —
  ||| the range is the declaring item's
  decls : List (String, Maybe Range, String)
  ||| every HOLE of the run, STRUCTURED. `decls` renders these for
  ||| display; this is what in-place elimination READS (docs/
  ||| NovaElaboration.txt, In-place elimination), which needs the
  ||| context and goal as terms, not as report text.
  holes : List HoleView
  ||| one per SORT of every `data` item the run elaborated: what
  ||| applying a generated eliminator needs, which the carried
  ||| signature does not say (the names).
  qiits : List QIITInfo
  ||| the ROOT module's binder occurrences with rendered types —
  ||| hover ascription for λ/eliminator binders
  binderTable : List (Range, String)
  ||| one per FAILED ITEM (item recovery: a broken item is reported,
  ||| falls back to a declaration of its signature, and the run goes
  ||| on), plus at most one module-level failure — an unresolvable
  ||| import or a module that cannot be imported open
  errors : List (String, Maybe Range, String)

export
elabProgramReport : List ModUnit -> ElabReport
elabProgramReport units = go initSt units [] [] [] []
 where
  -- newly-appended obligations/declarations since `before`: both only
  -- ever grow by `:<` (see `assume` and the SDeclDef handler), so
  -- `before` is always a prefix of `after`.
  newObls : (before, after : ElabSt) -> List Obligation
  newObls before after =
    drop (length (toList before.oblMeta)) (oblView after)

  newDecls : (before, after : ElabSt) -> List DeclView
  newDecls before after =
    drop (length (toList before.declMeta)) (declView after)

  Tagged : Type
  Tagged = ( List (String, Maybe Range, Obligation)
           , List (String, Maybe Range, FixTable, DeclView)
           , List HoleView )

  ||| The HOLES among a batch of new declarations, kept structured —
  ||| with each one's context HEAD-EXPOSED alongside the display form.
  ||| Exposure is normalization, so it is paid here, per hole, and not
  ||| in `declView`, which every module boundary calls just to ask
  ||| whether anything is open.
  holesOf : ElabSt -> FixTable -> String -> List DeclView -> List HoleView
  holesOf st tbl mname hs =
    -- exposure with the whitelist OPEN. `expOK`'s licence governs what
    -- a PROOF may unfold, and it is the surfacing item's, spent by the
    -- time a report is rendered; what this needs is only the SHAPE, to
    -- decide which elimination a variable has. Whether the elaborator
    -- may then see that shape is the trial's question, and the remedy
    -- is the item's own `using` clause. Opening it here also keeps
    -- report-time classification out of the blocked-exposure log.
    let stX = { eqScope $= ("exp:*" ::) } st in
    [ MkHoleView mname tbl h (map (exposeHead stX) h.dvctx)
    | h <- hs, isHoleName h.dvname ]

  -- an obligation or declaration the elaborator localized reports at
  -- ITS span, not at the whole item (same narrowing the CLI shows)
  tag : FixTable -> String -> Maybe Range -> (before, after : ElabSt) -> Tagged
  tag tbl mname rng before after =
    let ds = newDecls before after in
    ( map (\o => (mname, o.site.srange <|> rng, o)) (newObls before after)
    , map (\h => (mname, h.dvrange <|> rng, tbl, h)) ds
    , holesOf after tbl mname ds )

  ||| Same item recovery as the CLI fold: a failed item is reported,
  ||| its holes are salvaged as diagnostics of their own spans, it
  ||| falls back to a declaration of its signature, and the run
  ||| continues — so an editor shows every goal of a file, not just
  ||| those before its first broken proof.
  goItems : FixTable -> String -> ElabSt -> List (Maybe Range, SItem)
          -> (ElabSt, Tagged, List (String, Maybe Range, String))
  goItems tbl mname st [] = (st, ([], [], []), [])
  goItems tbl mname st ((rng, item) :: rest) =
    case runElabM (elabItem rng item) st of
      Left (stFail, err) =>
        let salvaged = salvagedHoles st stFail
            salv = map (\h => (mname, h.dvrange <|> rng, tbl, h)) salvaged
            (stNext, (dObls, dHs, dSt)) =
              case declFallback rng item >>= \(r, it) =>
                     either (const Nothing) Just (runElabM (elabItem r it) st) of
                Just (st2, _) => (st2, tag tbl mname rng st st2)
                Nothing => (st, ([], [], []))
            (st'', (obls, hs, sts), errs) = goItems tbl mname stNext rest in
        (st'', (dObls ++ obls, salv ++ dHs ++ hs,
                holesOf stFail tbl mname salvaged ++ dSt ++ sts),
         (mname, err.erange <|> rng, withBlockedHint stFail.sig err.emsg) :: errs)
      Right (st', _) =>
        let (tObls, tHs, tSt) = tag tbl mname rng st st'
            (st'', (obls, hs, sts), errs) = goItems tbl mname st' rest in
        (st'', (tObls ++ obls, tHs ++ hs, tSt ++ sts), errs)

  ||| A declaration re-displayed through the refined state: the
  ||| synthetic holes its context and goal mention become their values.
  refineDecl : ElabSt -> DeclView -> DeclView
  refineDecl st d = { dvctx $= map (displayTy st), dvty $= map (displayTy st) } d

  ||| REFINEMENT reaches this report too. It is a whole-run pass —
  ||| it reads the run's own constraints back and says what its
  ||| SYNTHETIC holes are — so it can only run once everything has
  ||| elaborated, which is after the per-item tagging above has
  ||| happened. `openReport` (the CLI's) applies it by rebuilding its
  ||| views from the final state; this one applies it to what it
  ||| accumulated, and the two must agree: a goal an editor shows and
  ||| a goal the command prints are one goal.
  |||
  ||| Solutions are substituted by re-DISPLAYING each stored form
  ||| through the refined state (`resugarElem` consults holeSols by Σ
  ||| name), and what refinement retired is then dropped: an
  ||| obligation whose sides became the same term, a synthetic hole
  ||| that got a value.
  finish : ElabSt -> List (String, Maybe Range, Obligation)
        -> List (String, Maybe Range, FixTable, DeclView) -> List HoleView
        -> List (Range, String) -> List (String, Maybe Range, String)
        -> ElabReport
  finish st0 obls hs sts binders errs =
    let st = refineHoles st0
        obls' = [ (m, r, o') | (m, r, o) <- obls
                             , let o' = { stmt := displayStmt st o.stmt
                                        , composite $= map (displayStmt st) } o
                             , not (oblDischarged o') ]
        hs' = [ (m, r, prettyDecl tbl (refineDecl st d))
              | (m, r, tbl, d) <- hs, not (declSolved st d) ]
        -- the EXPOSED context is refined alongside the display one:
        -- an entry that mentions a synthetic hole must say the same
        -- thing in both, or classification and printing disagree
        sts' = [ { hvDecl $= refineDecl st, hvCtxX $= map (displayTy st) } v
               | v <- sts, not (declSolved st v.hvDecl) ]
    in MkElabReport obls' hs' sts' (toList st.qiits) binders errs

  go : ElabSt -> List ModUnit -> List (String, Maybe Range, Obligation) -> List (String, Maybe Range, FixTable, DeclView) -> List HoleView -> List (String, Maybe Range, String) -> ElabReport
  go st [] obls hs sts errs = finish st obls hs sts [] errs
  go st (MkModUnit name path imps tbl items _ _ _ :: rest) obls hs sts errs =
    let st = either (const st) fst (runElabM (enterModule name path tbl (map mname imps)) st) in
    case runElabM (installImports imps) st of
      Left (_, err) => finish st obls hs sts (binderInfos tbl st) (errs ++ [(name, err.erange, err.emsg)])
      Right (st, ()) =>
        let (st', (itemObls, itemHs, itemSts), itemErrs) = goItems tbl name st items
            obls = obls ++ itemObls
            hs = hs ++ itemHs
            sts = sts ++ itemSts
            errs = errs ++ itemErrs in
        case rest of
              [] => finish st' obls hs sts (binderInfos tbl st') errs
              _ =>
                -- only ACCEPTED modules are importable: a module's
                -- signature segment must be DEFINITIONAL
                case (oblView st', declView st', itemErrs) of
                  ([], [], []) => go st' rest obls hs sts errs
                  _ => finish st' obls hs sts (binderInfos tbl st')
                         (errs ++ [(name, Nothing, "module \{name} has open obligations and cannot be imported")])
