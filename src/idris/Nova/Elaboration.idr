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
-- sig-ty-eq), so "zero obligations" and "no non-definition entries"
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
import Nova.Elaboration.Beta
import Nova.Kernel.QIIT
import Nova.Kernel.Parser
import Nova.Kernel

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range
import Nova.Elaboration.Named
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

data Stmt : Type where
  StElem : Ctx -> NameEnv -> Elem -> Elem -> Ty -> Stmt
  StTy : Ctx -> NameEnv -> Ty -> Ty -> Stmt

record Obligation where
  constructor MkObl
  stmt : Stmt
  site : String
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
  osite : String
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
  ||| the declaring item's source span (LSP diagnostics)
  drange : Maybe Range

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
  binderTypes : SnocList (String, Range, Ctx, NameEnv, String, Ty)
  ||| dotted name of the module being elaborated; "" = the root file,
  ||| whose entries stay unqualified
  modPrefix : String
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
  ||| strict-conversion mode's join; default mode has δ ambient anyway.
  eqScope : List String
  ||| SITE-LOCAL candidates, merged into every candidate set while
  ||| set: the reflected link justifications of a calc chain (§5.2).
  ||| Ground, at the site's own context — set transiently, like scope.
  localCands : List Cand
  ||| transient override of the engine's match/hop depth budget: a
  ||| chain needs one hop per link, so its composite discharge runs at
  ||| depth links + spDepth instead of the fixed spDepth
  depthOv : Maybe Nat

initSt : ElabSt
initSt = MkElabSt [<] [<] [] [] [] [] [] [] [] [] [] [] [] [] [<] [<] [<] "" [<] Nothing [] [] Nothing

||| Resolve a surface signature reference: aliases first (own module,
||| opened imports), else the name itself (qualified references reach
||| Σ directly).
resolveSigName : ElabSt -> String -> String
resolveSigName st x = go st.vis
 where
  go : SnocList (String, String) -> String
  go [<] = x
  go (rest :< (a, full)) = if a == x then full else go rest

-- ===== Elaboration monad =====

Err : Type
Err = String

data ElabM : Type -> Type where
  MkElabM : (ElabSt -> Either Err (ElabSt, a)) -> ElabM a

runElabM : ElabM a -> ElabSt -> Either Err (ElabSt, a)
runElabM (MkElabM f) = f

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

throw : Err -> ElabM a
throw e = MkElabM $ \_ => Left e

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
||| site's equation joins (strict mode; ambient δ subsumes it
||| otherwise). Returns the cited definition's Σ-name.
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
resolveUsingNames : String -> List String -> ElabM (List String, List String)
resolveUsingNames site ns = do
  st <- getSt
  let (eqNs, lemNs) = partitionEithers (map (\n =>
        case resolveEqName st n of
          Just q => Left q
          Nothing => Right n) ns)
  let rs = map (resolveFlex st) lemNs
  traverse_ (\x =>
    case sigLookup x st.sig of
      Nothing => throw "\{site}: using: unknown name '\{x}'"
      Just _ =>
        if any (\c => c.candName == x) st.lemmas
          then pure ()
          else throw "\{site}: using: '\{x}' is not an equation lemma in the visible store") rs
  pure (rs, eqNs)
 where
  partitionEithers : List (Either a b) -> (List a, List b)
  partitionEithers [] = ([], [])
  partitionEithers (Left x :: rest) = mapFst (x ::) (partitionEithers rest)
  partitionEithers (Right y :: rest) = mapSnd (y ::) (partitionEithers rest)

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
codeOf Ty.ZeroTy = Just Elem.ZeroTy
codeOf Ty.OneTy = Just Elem.OneTy
codeOf Ty.NatTy = Just Elem.NatTy
codeOf (Ty.PiTy a b) = Elem.PiTy <$> codeOf a <*> codeOf b
codeOf (Ty.SigmaTy a b) = Elem.SigmaTy <$> codeOf a <*> codeOf b
codeOf (Ty.SumTy a b) = Elem.SumTy <$> codeOf a <*> codeOf b
-- the relation is an Ω-element in BOTH the type former and the code:
-- El (A / R) ≜ El A / R, so it passes through unchanged
codeOf (Quotient a r) = QuotTy <$> codeOf a <*> Just r
codeOf (Ty.NuTy f) = Just (Elem.NuTy f)
codeOf (El e) = Just e
-- code-qiit: a sort's code is the sort former itself (smallness is
-- enforced wherever the code is USED — inferP rejects large ones)
codeOf (QSort sg k es) = Just (QSortC sg k es)
-- Ω and Prf p deliberately have NO codes in 𝕌 (the load-bearing
-- prohibition of the Ω design — see docs/NovaFoundation.txt)
codeOf _ = Nothing

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
matchElemP k d b (QSortC sg j es) (QSortC sg' j' es') =
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
matchElemP _ _ _ _ _ = const Nothing

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

matchTyP k d b Ty.ZeroTy Ty.ZeroTy = Just
matchTyP k d b Ty.OneTy Ty.OneTy = Just
matchTyP k d b Ty.NatTy Ty.NatTy = Just
matchTyP k d b Ty.UniverseTy Ty.UniverseTy = Just
matchTyP k d b Ty.PropTy Ty.PropTy = Just
matchTyP k d b (Ty.PiTy a c) (Ty.PiTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d (1 + b) c c'
matchTyP k d b (Ty.SigmaTy a c) (Ty.SigmaTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d (1 + b) c c'
matchTyP k d b (Ty.SumTy a c) (Ty.SumTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d b c c'
matchTyP k d b (El e) (El e') = matchElemP k d b e e'
-- normalization El-decodes codes inside carried signatures (El ℕc ≜ ℕ),
-- so a pattern `El e` whose e is parameter-headed can face the DECODED
-- rigid type: match e against the target's code instead
matchTyP k d b (El e) tgt = \bs => codeOf tgt >>= \c => matchElemP k d b e c bs
matchTyP k d b (Prf e) (Prf e') = matchElemP k d b e e'
matchTyP k d b (Quotient a r) (Quotient a' r') =
  \bs => matchTyP k d b a a' bs >>= matchElemP k d (2 + b) r r'
matchTyP k d b (Ty.SigVar x es) (Ty.SigVar x' es') =
  if x == x' then goSubNorm es es' else const Nothing
 where
  goSubNorm : SubNorm -> SubNorm -> Bindings -> Maybe Bindings
  goSubNorm [<] [<] = Just
  goSubNorm (es :< e) (es' :< e') = \bs => goSubNorm es es' bs >>= matchElemP k d b e e'
  goSubNorm _ _ = const Nothing
matchTyP k d b (QSort sg j es) (QSort sg' j' es') =
  if j == j' then \bs => matchQSigP k d b sg sg' bs >>= matchSpineP k d b es es'
  else const Nothing
matchTyP _ _ _ _ _ = const Nothing

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
    Ty.PiTy a b => peelPis (ctx :< a) b
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
elemSize (QSortC _ _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
elemSize (QCtor _ _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
elemSize (QElim _ _ ms fs es w) =
  S (foldl (\acc, m => acc + tySize m) 0 ms +
     foldl (\acc, f => acc + elemSize f) 0 fs +
     foldl (\acc, e => acc + elemSize e) 0 es + elemSize w)
elemSize (Elem.NuTy p) = S (polySize p)
elemSize (Out t) = S (elemSize t)
elemSize (Corec p a f x) = S (polySize p + elemSize a + elemSize f + elemSize x)

tySize Ty.ZeroTy = 1
tySize Ty.OneTy = 1
tySize Ty.NatTy = 1
tySize Ty.UniverseTy = 1
tySize Ty.PropTy = 1
tySize (Ty.PiTy a b) = S (tySize a + tySize b)
tySize (Ty.SigmaTy a b) = S (tySize a + tySize b)
tySize (Ty.SumTy a b) = S (tySize a + tySize b)
tySize (El e) = S (elemSize e)
tySize (Prf e) = S (elemSize e)
tySize (Quotient a r) = S (tySize a + elemSize r)
tySize (Ty.SigVar _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
tySize (QSort _ _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
tySize (Ty.NuTy p) = S (polySize p)

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
  go b (QSortC sg j es) (QSortC sg' j' es') m =
    if sg == sg' && j == j' then goSp b es es' m else Nothing
  go b (QCtor sg j es) (QCtor sg' j' es') m =
    if sg == sg' && j == j' then goSp b es es' m else Nothing
  go _ _ _ _ = Nothing

  goSp b [<] [<] m = Just m
  goSp b (es :< e) (es' :< e') m = goSp b es es' m >>= go b e e'
  goSp _ _ _ _ = Nothing

  goT b Ty.ZeroTy Ty.ZeroTy m = Just m
  goT b Ty.OneTy Ty.OneTy m = Just m
  goT b Ty.NatTy Ty.NatTy m = Just m
  goT b Ty.UniverseTy Ty.UniverseTy m = Just m
  goT b Ty.PropTy Ty.PropTy m = Just m
  goT b (Ty.PiTy a d) (Ty.PiTy a' d') m = goT b a a' m >>= goT (1+b) d d'
  goT b (Ty.SigmaTy a d) (Ty.SigmaTy a' d') m = goT b a a' m >>= goT (1+b) d d'
  goT b (Ty.SumTy a d) (Ty.SumTy a' d') m = goT b a a' m >>= goT b d d'
  goT b (El e) (El e') m = go b e e' m
  goT b (Prf e) (Prf e') m = go b e e' m
  goT b (Quotient a r) (Quotient a' r') m = goT b a a' m >>= go (2+b) r r'
  goT b (Ty.SigVar x es) (Ty.SigVar x' es') m =
    if x == x' then goSNT es es' m else Nothing
   where
    goSNT : SubNorm -> SubNorm -> List (Nat, Nat) -> Maybe (List (Nat, Nat))
    goSNT [<] [<] m = Just m
    goSNT (es :< e) (es' :< e') m = goSNT es es' m >>= go b e e'
    goSNT _ _ _ = Nothing
  goT b (QSort sg j es) (QSort sg' j' es') m =
    if sg == sg' && j == j' then goSp b es es' m else Nothing
  goT _ _ _ _ = Nothing

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

  descend : Elem -> Maybe (Elem, List Step)
  descend (ZeroElim u)       = at 0 0 u ZeroElim
  descend (NatIntro1 u)      = at 0 0 u NatIntro1
  descend (NatElim z s u)    =
    first [ at 0 0 z (\z' => NatElim z' s u)
          , at 1 2 s (\s' => NatElim z s' u)
          , at 2 0 u (\u' => NatElim z s u') ]
  descend (PiIntro f)        = at 0 1 f PiIntro
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
  descend (SumElim l r u)    =
    first [ at 0 1 l (\l' => SumElim l' r u)
          , at 1 1 r (\r' => SumElim l r' u)
          , at 2 0 u (\u' => SumElim l r u') ]
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
  descend (QuotElim f q)     =
    first [ at 0 1 f (\f' => QuotElim f' q)
          , at 1 0 q (\q' => QuotElim f q') ]
  descend (Squash t)         =
    (\(t', st) => (Squash t', st)) <$> rewriteTyS side c (0 :: pi) d t
  -- QIIT formers: spines and the eliminee are addressable; the carried
  -- signature and eliminator problem are OPAQUE (NovaKernel.txt, A3)
  descend (QSortC sg k es)  = spineAt es (\es' => QSortC sg k es')
  descend (QCtor sg k es)   = spineAt es (\es' => QCtor sg k es')
  descend (QElim sg k ms fs es w) =
    spineAt es (\es' => QElim sg k ms fs es' w)
      <|> at (length (toList es)) 0 w (\w' => QElim sg k ms fs es w')
  -- ν formers: out's scrutinee and corec's carrier/body/seed are
  -- addressable; the carried polynomial is OPAQUE, like a signature
  descend (Out t) = at 0 0 t Out
  descend (Corec p a f x) =
    at 0 0 a (\a' => Corec p a' f x)
      <|> at 1 1 f (\f' => Corec p a f' x)
      <|> at 2 0 x (\x' => Corec p a f x')
  descend _ = Nothing

rewriteTyS side c pi d Ty.ZeroTy = Nothing
rewriteTyS side c pi d Ty.OneTy = Nothing
rewriteTyS side c pi d Ty.NatTy = Nothing
rewriteTyS side c pi d Ty.UniverseTy = Nothing
rewriteTyS side c pi d Ty.PropTy = Nothing
rewriteTyS side c pi d (Prf e) =
  (\(e', st) => (Prf e', st)) <$> rewriteElemS side c (0 :: pi) d e
rewriteTyS side c pi d (Ty.PiTy a b) =
  ((\(a', st) => (Ty.PiTy a' b, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(b', st) => (Ty.PiTy a b', st)) <$> rewriteTyS side c (1 :: pi) (1 + d) b)
rewriteTyS side c pi d (Ty.SigmaTy a b) =
  ((\(a', st) => (Ty.SigmaTy a' b, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(b', st) => (Ty.SigmaTy a b', st)) <$> rewriteTyS side c (1 :: pi) (1 + d) b)
rewriteTyS side c pi d (Ty.SumTy a b) =
  ((\(a', st) => (Ty.SumTy a' b, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(b', st) => (Ty.SumTy a b', st)) <$> rewriteTyS side c (1 :: pi) d b)
rewriteTyS side c pi d (El e) =
  (\(e', st) => (El e', st)) <$> rewriteElemS side c (0 :: pi) d e
rewriteTyS side c pi d (Quotient a r) =
  ((\(a', st) => (Quotient a' r, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(r', st) => (Quotient a r', st)) <$> rewriteElemS side c (1 :: pi) (2 + d) r)
-- a ν type has no child indices: the carried polynomial is OPAQUE to
-- paths, like a carried signature (NovaKernel.txt, child indexing)
rewriteTyS side c pi d (Ty.NuTy f) = Nothing
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
rewriteTyS side c pi d (Ty.SigVar x es) =
  let xs = toList es in
  firstJ (map (\i =>
    case getAt i xs of
      Just e => (\(e', st) =>
                   case splitAt i xs of
                     (pre, _ :: post) => (Ty.SigVar x (cast (pre ++ e' :: post)), st)
                     _ => (Ty.SigVar x es, st))
                <$> rewriteElemS side c (i :: pi) d e
      Nothing => Nothing) [0 .. minus (length xs) 1])
 where
  firstJ : List (Maybe a) -> Maybe a
  firstJ [] = Nothing
  firstJ (Just x' :: _) = Just x'
  firstJ (Nothing :: rest) = firstJ rest

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
  unfElem sig unfs (QSortC sg k es)  = QSortC (unfQSig sig unfs sg) k (unfSubNorm sig unfs es)
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
  unfTy sig unfs Ty.ZeroTy        = Ty.ZeroTy
  unfTy sig unfs Ty.OneTy         = Ty.OneTy
  unfTy sig unfs Ty.NatTy         = Ty.NatTy
  unfTy sig unfs Ty.UniverseTy    = Ty.UniverseTy
  unfTy sig unfs (Ty.PiTy a b)    = Ty.PiTy (unfTy sig unfs a) (unfTy sig unfs b)
  unfTy sig unfs (Ty.SigmaTy a b) = Ty.SigmaTy (unfTy sig unfs a) (unfTy sig unfs b)
  unfTy sig unfs (Ty.SumTy a b)   = Ty.SumTy (unfTy sig unfs a) (unfTy sig unfs b)
  unfTy sig unfs (El e)           = El (unfElem sig unfs e)
  unfTy sig unfs PropTy           = PropTy
  unfTy sig unfs (Prf e)          = Prf (unfElem sig unfs e)
  unfTy sig unfs (Quotient a r)   = Quotient (unfTy sig unfs a) (unfElem sig unfs r)
  unfTy sig unfs (Ty.SigVar x es) = Ty.SigVar x (unfSubNorm sig unfs es)
  unfTy sig unfs (QSort sg k es)  = QSort (unfQSig sig unfs sg) k (unfSubNorm sig unfs es)
  unfTy sig unfs (Ty.NuTy f)      = Ty.NuTy (unfPoly sig unfs f)

rwNfElemS : Sig -> (unfs : List String) -> List Cand -> (side : Bool) -> Elem -> (Elem, List Step)
rwNfElemS sig unfs cands side e =
  if strictConv then (compElem (unfElem sig unfs e), []) else
  let start = betaElem sig e in go rwFuel [start] start []
 where
  go : Nat -> List Elem -> Elem -> List Step -> (Elem, List Step)
  go Z seen t acc = (t, acc)
  go (S fuel) seen t acc =
    case tryCands cands (\c => rewriteElemS side c [] 0 t) of
      Just (t', st) =>
        let t'' = betaElem sig t' in
        if elem t'' seen then (t, acc) else go fuel (t'' :: seen) t'' (acc ++ st)
      Nothing => (t, acc)

rwNfTyS : Sig -> (unfs : List String) -> List Cand -> (side : Bool) -> Ty -> (Ty, List Step)
rwNfTyS sig unfs cands side ty =
  if strictConv then (compTy (unfTy sig unfs ty), []) else
  let start = betaTy sig ty in go rwFuel [start] start []
 where
  go : Nat -> List Ty -> Ty -> List Step -> (Ty, List Step)
  go Z seen t acc = (t, acc)
  go (S fuel) seen t acc =
    case tryCands cands (\c => rewriteTyS side c [] 0 t) of
      Just (t', st) =>
        let t'' = betaTy sig t' in
        if elem t'' seen then (t, acc) else go fuel (t'' :: seen) t'' (acc ++ st)
      Nothing => (t, acc)

-- ===== Strict-conversion survey mode (NOVA_STRICT_CONV=1) =====
--
-- Weak-head exposure with LOGGED δ-unfolds: semantics of whnfE/whnfT,
-- plus a `unf <module>|<name>` profile bump per definition unfolded —
-- the survey stream for the future per-item `using`-unfold whitelist.
-- Used (in strict mode) wherever conversion or checking needs a TYPE
-- head; equation SIDES never δ-expand in strict mode.

mutual
  exposeE : (pre : String) -> Sig -> Elem -> Elem
  exposeE pre sig (NatElim z s t) =
    case exposeE pre sig t of
      NatIntro0   => exposeE pre sig z
      NatIntro1 n => exposeE pre sig (substElem s (Ext (Ext Id n) (NatElim z s n)))
      t'          => NatElim z s t'
  exposeE pre sig (PiApp f e) =
    case exposeE pre sig f of
      PiIntro g => exposeE pre sig (substElem g (Ext Id e))
      f'        => PiApp f' e
  exposeE pre sig (Let a b) = exposeE pre sig (substElem b (Ext (Ext Id a) Star))
  exposeE pre sig (SigmaElim1 t) =
    case exposeE pre sig t of
      SigmaIntro a _ => exposeE pre sig a
      t'             => SigmaElim1 t'
  exposeE pre sig (SigmaElim2 t) =
    case exposeE pre sig t of
      SigmaIntro _ b => exposeE pre sig b
      t'             => SigmaElim2 t'
  exposeE pre sig (SumElim l r t) =
    case exposeE pre sig t of
      Inj1 a => exposeE pre sig (substElem l (Ext Id a))
      Inj2 b => exposeE pre sig (substElem r (Ext Id b))
      t'     => SumElim l r t'
  exposeE pre sig (SigVar x es) =
    case cachedSigLookup sig x of
      Just (SigDef _ _ a _) => bump "unf \{pre}|\{x}" 1 (exposeE pre sig (substElem a (embed es)))
      _ => SigVar x es
  exposeE pre sig (QuotElim f q) =
    case exposeE pre sig q of
      Class a => exposeE pre sig (substElem f (Ext Id a))
      q'      => QuotElim f q'
  exposeE pre sig (Squash t) =
    case exposeT pre sig t of
      Prf p => exposeE pre sig p
      t'    => Squash t'
  exposeE pre sig (QElim sg k ms fs es w) =
    case exposeE pre sig w of
      QCtor sgW c theta =>
        if sgW == sg
          then case qElimBetaRhs sg ms fs c theta of
                 Right rhs => exposeE pre sig rhs
                 Left _ => QElim sg k ms fs es (QCtor sgW c theta)
          else QElim sg k ms fs es (QCtor sgW c theta)
      w' => QElim sg k ms fs es w'
  exposeE pre sig (Out t) =
    case exposeE pre sig t of
      Corec p a f x => exposeE pre sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      t'            => Out t'
  exposeE pre sig e = e

  exposeT : (pre : String) -> Sig -> Ty -> Ty
  exposeT pre sig (El e) =
    case exposeE pre sig e of
      Elem.ZeroTy      => Ty.ZeroTy
      Elem.OneTy       => Ty.OneTy
      Elem.NatTy       => Ty.NatTy
      Elem.PiTy a b    => Ty.PiTy (El a) (El b)
      Elem.SigmaTy a b => Ty.SigmaTy (El a) (El b)
      Elem.SumTy a b   => Ty.SumTy (El a) (El b)
      QuotTy a r       => Quotient (El a) r
      QSortC sg k es   => QSort sg k es
      Elem.NuTy f      => Ty.NuTy f
      e'               => El e'
  exposeT pre sig (Ty.SigVar x es) =
    case cachedSigLookup sig x of
      Just (SigTyDef _ _ a) => bump "unf \{pre}|\{x}" 1 (exposeT pre sig (substTy a (embed es)))
      _ => Ty.SigVar x es
  exposeT pre sig t = t

||| Strict-gated engine normalizers: δ-free in strict mode, full δβ
||| otherwise. For the engine's EQUATION-SIDE positions only — checking
||| machinery keeps betaTy, and type-HEAD positions use exposeT.
engNfE : ElabSt -> Elem -> Elem
engNfE st e = if strictConv then compElem e else betaElem st.sig e

engNfT : ElabSt -> Ty -> Ty
engNfT st t = if strictConv then compTy t else betaTy st.sig t

||| CHECKING-position head exposure: strict mode swaps the full
||| normalization for the logged whnf-δ exposure — same head, and the
||| per-module `unf` labels record exactly the names a future
||| `using`-unfold whitelist would carry.
exposeHead : ElabSt -> Ty -> Ty
exposeHead st ty = if strictConv then exposeT st.modPrefix st.sig ty else betaTy st.sig ty

||| Prop-code exposure at checking positions (⋆, squash-elim, chains).
exposeCode : ElabSt -> Elem -> Elem
exposeCode st p = if strictConv then exposeE st.modPrefix st.sig p else betaElem st.sig p

||| Leading-Π exposure for telescope peeling (strict mode only —
||| domains stay as written, each codomain head exposed in turn).
exposePisT : ElabSt -> Ty -> Ty
exposePisT st ty = case exposeT st.modPrefix st.sig ty of
  Ty.PiTy a b => Ty.PiTy a (exposePisT st b)
  t => t

||| Telescope-peeling normalization: full betaTy outside strict mode.
peelNf : ElabSt -> Ty -> Ty
peelNf st ty = if strictConv then exposePisT st ty else betaTy st.sig ty

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
    ++ closeCand (child (\bs => SelCod <$> lookup 0 bs) 1 [El a1] b0 b1)
  go (Elem.SigmaTy a0 b0) (Elem.SigmaTy a1 b1) =
    comp SelDom a0 a1
    ++ closeCand (child (\bs => SelCod <$> lookup 0 bs) 1 [El a1] b0 b1)
  go (Elem.SumTy a0 b0) (Elem.SumTy a1 b1) =
    -- code-sum-inj: both components at 𝕌, neither under a binder
    comp SelSumL a0 a1 ++ comp SelSumR b0 b1
  go (QuotTy a0 r0) (QuotTy a1 r1) =
    comp SelQDom a0 a1
    ++ closeCand (child (\bs => [| SelQRel (lookup 1 bs) (lookup 0 bs) |]) 2
                        [El a1, substTy (El a1) Wk] r0 r1)
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

  -- a hypothesis licenses an equation when its (peeled) type is a Prf
  -- whose prop normalizes to an equality (the one pathway — squashed
  -- spellings converge by code-squash-prf during normalization)
  eqShape : Ty -> Maybe (Elem, Elem, Ty)
  eqShape (Prf p) =
    case exposeCode st p of
      Elem.EqTy l r t => Just (l, r, t)
      _ => Nothing
  eqShape _ = Nothing

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
  -- Prf-equalities licenses one candidate per component, the proof
  -- element being the projection chain (el-reflect takes any
  -- Prf-typed term, so a projection is a legitimate witness). This is
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
        case (if strictConv then exposeT st.modPrefix st.sig ty else betaTy st.sig ty) of
          Prf p =>
            case exposeCode st p of
              Elem.EqTy l r t => [(proj, (l, r, t))]
              _ => []
          Ty.SigmaTy a b =>
            -- dependent Σs instantiate the body at the projection —
            -- existential invariants (Σ of data and equations) land here
            pairEqs fuel' (SigmaElim1 proj) a ++
            pairEqs fuel' (SigmaElim2 proj) (substTy b (Ext Id (SigmaElim1 proj)))
          _ => []

  candsAt : Nat -> List Cand
  candsAt i =
    case candAt i of
      Just c => [c]
      Nothing =>
        case ctxLookup ctx i of
          Just tyI =>
            case exposeHead st tyI of
              tyB@(Ty.SigmaTy _ _) => map (uncurry groundEqCand) (pairEqs 8 (CtxVar i) tyB)
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
  in case (st.localCands, hypCands st sRw ctx) of
       ([], []) => MkCandSet sCs sRw sHops
       (ls, hs) =>
         let (lcs, lsh, lre, lhp) = sigCandParts ls
             (hcs, hsh, hre, hhp) = sigCandParts hs
         in MkCandSet (lcs ++ sCs ++ hcs)
                      (lsh ++ lre ++ sShrink ++ hsh ++ sRest ++ hre)
                      (lhp ++ sHops ++ hhp)

rwNfElem : ElabSt -> Ctx -> Elem -> Elem
rwNfElem st ctx e = fst (rwNfElemS st.sig st.eqScope (mkCandSet st ctx).rw True e)

rwNfTy : ElabSt -> Ctx -> Ty -> Ty
rwNfTy st ctx ty = fst (rwNfTyS st.sig st.eqScope (mkCandSet st ctx).rw True ty)

-- ===== Neutral type inference =====

||| Head exposure for neutral inference: logged whnf-δ in strict mode,
||| full normalization otherwise.
neExpose : ElabSt -> Ty -> Ty
neExpose st ty = if strictConv then exposeT st.modPrefix st.sig ty else betaTy st.sig ty

inferNe : ElabSt -> Ctx -> Elem -> Maybe Ty
inferNe st ctx (CtxVar i) = ctxLookup ctx i
inferNe st ctx (PiApp f x) =
  case neExpose st <$> inferNe st ctx f of
    Just (Ty.PiTy a b) => Just (substTy b (Ext Id x))
    _ => Nothing
inferNe st ctx (SigmaElim1 t) =
  case neExpose st <$> inferNe st ctx t of
    Just (Ty.SigmaTy a b) => Just a
    _ => Nothing
inferNe st ctx (SigmaElim2 t) =
  case neExpose st <$> inferNe st ctx t of
    Just (Ty.SigmaTy a b) => Just (substTy b (Ext Id (SigmaElim1 t)))
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
        tyN = if strictConv then exposeT st.modPrefix st.sig tyX else betaTy st.sig tyX
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
        -- in strict mode; the banned automation is the rwNf positional
        -- candidate search, not this)
        <|> (do congSteps <- timed "sp-cong" (\_ => spCongC dep st cs ctx a' b')
                pure (MkECertF bridge (base ++ congSteps) FBeta []))
   where
    unbridged : ECert -> Maybe ECert
    unbridged c@(MkECertF Nothing _ _ _) = Just c
    unbridged _ = Nothing

  spEqStructC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Maybe ECert
  spEqStructC dep st cs ctx a b Ty.OneTy = Just (MkECert [] FProp)
  spEqStructC dep st cs ctx a b Ty.ZeroTy = Just (MkECert [] FProp)
  -- el-pi-eta, UNCONDITIONALLY: even two neutral sides may be joined
  -- pointwise (funext-via-reflection — a hypothesis (x : A) → Prf
  -- (f x ≡ g x) becomes a whole-equation candidate for the body once
  -- the context is extended). Terminates: recursion is on cod.
  spEqStructC dep st cs ctx a b (Ty.PiTy dom cod) =
    -- η: outside the strict subset
    do guard (not strictConv)
       sub <- spEqElemC dep st (extendCS cs) (ctx :< dom)
                (betaElem st.sig (PiApp (substElem a Wk) (CtxVar 0)))
                (betaElem st.sig (PiApp (substElem b Wk) (CtxVar 0)))
                cod
       pure (MkECert [] (FEtaPi sub))
  -- same-tag injections at a sum: decompose to the payloads at the
  -- branch type (≐-congruence at inj; el-one-prop then closes 𝟙
  -- payloads, which is how a three-valued sign's cases discharge)
  spEqStructC dep st cs ctx (Inj1 x) (Inj1 y) (Ty.SumTy domL _) =
    do sub <- spEqElemC dep st cs ctx (engNfE st x) (engNfE st y) domL
       pure (MkECert [] (FInj sub))
  spEqStructC dep st cs ctx (Inj2 x) (Inj2 y) (Ty.SumTy _ domR) =
    do sub <- spEqElemC dep st cs ctx (engNfE st x) (engNfE st y) domR
       pure (MkECert [] (FInj sub))
  spEqStructC dep st cs ctx a b (Ty.SigmaTy dom cod) =
    -- pair-η: outside the strict subset
    if not strictConv && (isPair a || isPair b)
      then do c1 <- spEqElemC dep st cs ctx (betaElem st.sig (SigmaElim1 a)) (betaElem st.sig (SigmaElim1 b)) dom
              c2 <- spEqElemC dep st cs ctx (betaElem st.sig (SigmaElim2 a)) (betaElem st.sig (SigmaElim2 b))
                      (substTy cod (Ext Id (SigmaElim1 a)))
              pure (MkECert [] (FEtaSigma c1 c2))
      else Nothing
   where
    isPair : Elem -> Bool
    isPair (SigmaIntro _ _) = True
    isPair _ = False
  spEqStructC dep st cs ctx (Class x) (Class y) (Quotient dom rel) =
    case engNfE st (substElem rel (Ext (Ext Id x) y)) of
      Squash Ty.OneTy => Just (MkECert [] (FWitness Nothing))
      Elem.EqTy l r t => do sub <- spEqElemC dep st cs ctx l r t
                            pure (MkECert [] (FWitness (Just sub)))
      _ => Nothing
  -- el-prf-prop: proof irrelevance — any two elements of Prf p are equal
  spEqStructC dep st cs ctx a b (Prf _) = Just (MkECert [] FProp)
  -- code-prop-eq: mutually implied prop codes are equal; each direction
  -- is ⋆ with a synthesized witness under the other side's hypothesis
  spEqStructC dep st cs ctx a b Ty.PropTy = do
    (fe, fsk) <- mkImpl a b
    (be, bsk) <- mkImpl b a
    pure (MkECert [] (FPropExt fe fsk be bsk))
   where
    -- Prf src → Prf tgt, as a λ whose body is a proof of (Prf tgt)[↑]
    -- under ctx ▷ Prf src: 𝟙-shaped squashes outright, equality props
    -- by a nested discharge (which may use the hypothesis as a rewrite
    -- candidate)
    mkImpl : Elem -> Elem -> Maybe (Elem, Skel)
    mkImpl src tgt =
      let ctx' = ctx :< Prf src in
      case engNfE st (substElem tgt Wk) of
        Squash sq => case engNfT st sq of
          Ty.OneTy => Just (lam (Nd [PSquashWit OneIntro (Nd [] [])] []))
          _ => Nothing
        Elem.EqTy l r t => do
          c <- spEqElemC dep st (mkCandSet st ctx') ctx' l r t
          Just (lam (Nd [PReflEq c] []))
        _ => Nothing
     where
      lam : Skel -> (Elem, Skel)
      lam bodySk = (PiIntro Star, Nd [] [bodySk])
  spEqStructC _ _ _ _ _ _ _ = Nothing

  ||| Syntactic congruence descent: same-headed sides compared
  ||| componentwise; children flattened as path-prefixed steps.
  ||| Binder-crossing components only when no steps are needed there
  ||| (a Γ-level proof would go out of scope).
  spCongC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Maybe (List Step)
  spCongC dep st cs ctx (NatIntro1 x) (NatIntro1 y) =
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y Ty.NatTy >>= flatSteps)
  spCongC dep st cs ctx (NatElim z s t) (NatElim z' s' t') =
    if z == z' && s == s'
      then prefixSteps 2 <$> (spEqElemC dep st cs ctx t t' Ty.NatTy >>= flatSteps)
      else Nothing
  spCongC dep st cs ctx (PiApp f x) (PiApp g y) =
    if f == g
      then case neExpose st <$> inferNe st ctx f of
             Just (Ty.PiTy dom _) =>
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
               prefixSteps 1 <$> (spEqElemC dep st cs ctx x y Ty.NatTy >>= flatSteps)
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
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y Ty.NatTy >>= natFree)
   where
    -- the component type is unknown here; only proof-free evidence
    -- (pure computation) is safe to accept
    natFree : ECert -> Maybe (List Step)
    natFree c = if stepFree c then Just [] else Nothing
  spCongC dep st cs ctx (Inj1 x) (Inj1 y) =
    -- injection congruence: the component type is unknown here, so
    -- only proof-free evidence (pure computation) is safe to accept —
    -- like class above
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y Ty.NatTy >>= natFree)
   where
    natFree : ECert -> Maybe (List Step)
    natFree c = if stepFree c then Just [] else Nothing
  spCongC dep st cs ctx (Inj2 x) (Inj2 y) =
    prefixSteps 0 <$> (spEqElemC dep st cs ctx x y Ty.NatTy >>= natFree)
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
    stA <- spEqElemC dep st cs ctx a a' Ty.UniverseTy >>= flatSteps
    cB <- spEqElemC dep st (extendCS cs) (ctx :< El a') b b' Ty.UniverseTy
    if stepFree cB then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (Elem.SigmaTy a b) (Elem.SigmaTy a' b') = do
    stA <- spEqElemC dep st cs ctx a a' Ty.UniverseTy >>= flatSteps
    cB <- spEqElemC dep st (extendCS cs) (ctx :< El a') b b' Ty.UniverseTy
    if stepFree cB then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (Elem.SumTy a b) (Elem.SumTy a' b') = do
    -- non-dependent: BOTH components may carry steps (no binder to
    -- take a Γ-level proof out of scope)
    stA <- spEqElemC dep st cs ctx a a' Ty.UniverseTy >>= flatSteps
    stB <- spEqElemC dep st cs ctx b b' Ty.UniverseTy >>= flatSteps
    pure (prefixSteps 0 stA ++ prefixSteps 1 stB)
  spCongC dep st cs ctx (QuotTy a r) (QuotTy a' r') = do
    stA <- spEqElemC dep st cs ctx a a' Ty.UniverseTy >>= flatSteps
    cR <- spEqElemC dep st (extendCS (extendCS cs)) (ctx :< El a' :< substTy (El a') Wk) r r' Ty.PropTy
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
    -- hops (automated lemma chaining): outside the strict subset
    firstJ (map direct cs.all)
      <|> (if strictConv then Nothing else firstJ (map hop cs.hops))
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
          Just (Prf p) => case engNfE st p of
            Elem.EqTy hl hr _ =>
              if (engNfE st hl == lN && engNfE st hr == rN)
                then Just (CtxVar i)
                else Nothing
            _ => Nothing
          _ => Nothing) [0 .. minus (length ctx) 1])

    ||| A hypothesis whose (normalized) type is exactly this Prf type.
    hypPrfWitness : Ty -> Maybe Elem
    hypPrfWitness want =
      firstJ (map (\i =>
        case engNfT st <$> ctxLookup ctx i of
          Just h => if h == want then Just (CtxVar i) else Nothing
          Nothing => Nothing) [0 .. minus (length ctx) 1])

    ||| An element witnessing an unbound ≡-, 𝟙- or Prf-typed parameter.
    condElem : Cand -> Bindings -> Nat -> Maybe Elem
    condElem c bs p =
      case lookup p bs of
        Just e => Just e
        Nothing => do
          tp <- paramTy c p
          sigma <- condSub c.params p bs
          case (if strictConv then exposeT st.modPrefix st.sig (substTy tp sigma)
                              else betaTy st.sig (substTy tp sigma)) of
            Ty.OneTy => Just OneIntro
            Prf pr =>
              hypPrfWitness (Prf (engNfE st pr))
              <|> (case engNfE st pr of
                     Squash Ty.OneTy => Just Star
                     Elem.EqTy l r _ =>
                       let lN = engNfE st l
                           rN = engNfE st r in
                       hypWitness lN rN
                       <|> (if lN == rN then Just Star else Nothing)
                     _ => Nothing)
            _ => Nothing

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
          let a' = betaElem st.sig (substElem c.rhs sigma)
          rest <- spEqElemC dep st cs ctx a' b ty >>= noBridge
          pure (MkECert (steps ++ rest.steps) rest.final))
      <|> (do bs <- matchElemP c.params 0 0 c.lhs b []
              full <- complete c bs
              steps <- materialize c full False []
              sigma <- instSub c.params 0 full
              let b' = betaElem st.sig (substElem c.rhs sigma)
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
        a = if strictConv then exposeT st.modPrefix st.sig a0 else a0
        b = if strictConv then exposeT st.modPrefix st.sig b0 else b0
        base = bump "rwnf-ty" (nowNs () - t0) (aSteps ++ bSteps) in
    ((\rest => MkECert (base ++ rest) FBeta) <$> go a b)
      <|> congFinal a b base
   where
    -- head-level congruence finals: extensional components (Ω-valued)
    -- cannot be flattened into steps, so ty-prf-cong / ty-quot-cong
    -- carry a nested certificate instead
    congFinal : Ty -> Ty -> List Step -> Maybe ECert
    congFinal (Prf p) (Prf q) base = do
      sub <- spEqElemC dep st cs ctx p q Ty.PropTy
      pure (MkECert base (FPrfCong sub))
    -- ty-pi-cong / ty-sigma-cong: an Ω-valued component (a Prf
    -- codomain, say) cannot flatten into steps — carry component
    -- certificates instead
    congFinal (Ty.PiTy a0 b0) (Ty.PiTy a1 b1) base = do
      dc <- spEqTyC dep st cs ctx a0 a1
      cc <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
      pure (MkECert base (FPiCong dc cc))
    congFinal (Ty.SigmaTy a0 b0) (Ty.SigmaTy a1 b1) base = do
      dc <- spEqTyC dep st cs ctx a0 a1
      cc <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
      pure (MkECert base (FSigmaCong dc cc))
    congFinal (Ty.SumTy a0 b0) (Ty.SumTy a1 b1) base = do
      lc <- spEqTyC dep st cs ctx a0 a1
      rc <- spEqTyC dep st cs ctx b0 b1
      pure (MkECert base (FSumCong lc rc))
    congFinal (Ty.Quotient a0 r0) (Ty.Quotient a1 r1) base =
      if a0 == a1
        then do
          sub <- spEqElemC dep st (extendCS (extendCS cs))
                   (ctx :< a0 :< substTy a0 Wk) r0 r1 Ty.PropTy
          pure (MkECert base (FQuotCong sub))
        else Nothing
    congFinal _ _ _ = Nothing
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
        (Ty.PiTy a0 b0, Ty.PiTy a1 b1) => do
          stA <- go a0 a1
          sub <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
          if stepFree sub then Just (prefixSteps 0 stA) else Nothing
        (Ty.SigmaTy a0 b0, Ty.SigmaTy a1 b1) => do
          stA <- go a0 a1
          sub <- spEqTyC dep st (extendCS cs) (ctx :< a1) b0 b1
          if stepFree sub then Just (prefixSteps 0 stA) else Nothing
        (Ty.SumTy a0 b0, Ty.SumTy a1 b1) => do
          -- non-dependent: both components may carry steps
          stA <- go a0 a1
          stB <- go b0 b1
          pure (prefixSteps 0 stA ++ prefixSteps 1 stB)
        (Ty.Quotient a0 r0, Ty.Quotient a1 r1) => do
          stA <- go a0 a1
          sub <- spEqElemC dep st (extendCS (extendCS cs)) (ctx :< a1 :< substTy a1 Wk) r0 r1 Ty.PropTy
          if stepFree sub then Just (prefixSteps 0 stA) else Nothing
        (Prf x, Prf y) => flatE False 0 ctx x y Ty.PropTy
        (El x, El y) => flatE False 0 ctx x y Ty.UniverseTy
        (El x, rigid) => do c <- codeOf rigid
                            flatE True 0 ctx x c Ty.UniverseTy
        (rigid, El y) => do c <- codeOf rigid
                            -- rewrite the El side (the rhs here)
                            cE <- spEqElemC dep st cs ctx c y Ty.UniverseTy
                            steps <- flatSteps cE
                            if any (\s => s.onLhs) steps
                              then Nothing
                              else Just (prefixSteps 0 steps)
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

||| Record a binder occurrence's elaborated type (nothing without a
||| span — core-built or wildcard binders).
recordBinder : Maybe Range -> Ctx -> NameEnv -> String -> Ty -> ElabM ()
recordBinder Nothing _ _ _ _ = pure ()
recordBinder (Just r) ctx env x ty = do
  st <- getSt
  modifySt $ { binderTypes $= (:< (st.modPrefix, r, ctx, env, x, ty)) }

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
  headMatch (QSortC _ kP _) (QSortC _ k _) = kP == k
  headMatch (QCtor _ cP _) (QCtor _ c _) = cP == c
  -- an eliminator occurrence: the emitted def's motive/method
  -- positions are λ-binders, i.e. pure pattern variables — and the
  -- El-/Prf-wrapped motive shapes keep the Elim/ElimP twins disjoint
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
-- code-squash-prf) while DEFINITIONS stay folded — δ is the one
-- contraction display never takes, so terms keep the user's names.
-- The contraction is exactly the tier-½ normalizer
-- (Nova.Elaboration.Beta), reused; on top of it, QIIT formers are
-- resugared through the Σ entries that name them (resugarQ above).
mutual
  resugarElem : ElabSt -> Elem -> Elem
  resugarElem st e@(QSortC sg k es) =
    let z = QSortC (map (resugarQTy st) sg) k (resugarSub st es) in
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
  resugarElem st (SigVar x es) = SigVar x (resugarSub st es)
  resugarElem st (Elem.NuTy f) = Elem.NuTy (resugarPoly st f)
  resugarElem st (Out t) = Out (resugarElem st t)
  resugarElem st (Corec f a g x) =
    Corec (resugarPoly st f) (resugarElem st a) (resugarElem st g) (resugarElem st x)
  resugarElem st e = e

  resugarTy : ElabSt -> Ty -> Ty
  resugarTy st (QSort sg k es) =
    let zsg = map (resugarQTy st) sg
        zes = resugarSub st es in
    case resugarQ st (QSortC zsg k zes) of
      Just code => El code
      Nothing => QSort zsg k zes
  resugarTy st (Ty.PiTy a b) = Ty.PiTy (resugarTy st a) (resugarTy st b)
  resugarTy st (Ty.SigmaTy a b) = Ty.SigmaTy (resugarTy st a) (resugarTy st b)
  resugarTy st (Ty.SumTy a b) = Ty.SumTy (resugarTy st a) (resugarTy st b)
  resugarTy st (El e) = El (resugarElem st e)
  resugarTy st (Prf e) = Prf (resugarElem st e)
  resugarTy st (Quotient a r) = Quotient (resugarTy st a) (resugarElem st r)
  resugarTy st (Ty.SigVar x es) = Ty.SigVar x (resugarSub st es)
  resugarTy st (Ty.NuTy f) = Ty.NuTy (resugarPoly st f)
  resugarTy st t = t

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
||| The report view: Σ's constraint entries — the run's obligations,
||| in surfacing order — zipped with their display metadata.
oblView : ElabSt -> List Obligation
oblView st = go (toList st.sig) (toList st.oblMeta)
 where
  go : List SigEntry -> List OblMeta -> List Obligation
  go (SigEq ctx a b ty :: rest) (m :: ms) =
    MkObl (displayStmt st (StElem ctx m.oenv a b ty)) m.osite (map (displayStmt st) m.ocomposite) m.ohint :: go rest ms
  go (SigTyEq ctx x y :: rest) (m :: ms) =
    MkObl (displayStmt st (StTy ctx m.oenv x y)) m.osite (map (displayStmt st) m.ocomposite) m.ohint :: go rest ms
  go (_ :: rest) ms = go rest ms
  go [] _ = []

||| One declaration for the report: its Σ-name, context (with binder
||| names), type (Nothing for a type declaration) and declaring item.
record DeclView where
  constructor MkDeclView
  dvname : String
  dvctx : Ctx
  dvenv : NameEnv
  dvty : Maybe Ty
  dvsite : String
  dvrange : Maybe Range

||| The declaration report view: Σ's declaration entries zipped with
||| their display metadata, in minting order.
declView : ElabSt -> List DeclView
declView st = mapMaybe view (toList st.sig)
 where
  metaFor : String -> Maybe DeclMeta
  metaFor x = find (\m => m.dname == x) (toList st.declMeta)
  view : SigEntry -> Maybe DeclView
  view (SigDecl ctx x ty) = map (\m => MkDeclView x (displayCtx st ctx) m.denv (Just (displayTy st ty)) m.dsite m.drange) (metaFor x)
  view (SigTyDecl ctx x) = map (\m => MkDeclView x (displayCtx st ctx) m.denv Nothing m.dsite m.drange) (metaFor x)
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

||| §5.4 (docs/SearchlessElaboration.md): when a SCOPED site is about
||| to assume, probe the GLOBAL store once. A discharge the kernel
||| replays becomes a hint on the obligation — search as feedback,
||| never as acceptance (the site stays assumed either way).
||| Names of Σ term-definitions occurring in a rendered core term (the
||| core Show is constructor-style, so `SigVar "name"` is scannable) —
||| a survey-mode convenience feeding the unfold hint.
scanDefNames : ElabSt -> String -> List String
scanDefNames st s = nub (filter isDef (go (unpack s)))
 where
  isDef : String -> Bool
  isDef x = case cachedSigLookup st.sig x of
              Just (SigDef _ _ _ _) => True
              _ => False
  go : List Char -> List String
  go [] = []
  go cs@(_ :: rest) =
    if isPrefixOf (unpack "SigVar \"") cs
      then let cs' = drop 8 cs
               nm = pack (takeWhile (/= '"') cs')
           in nm :: go (drop (length nm) cs')
      else go rest

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
    if not strictConv then Nothing else
    go 5 (scanDefNames st (show a ++ show b))
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
          let ns' = nub (ns ++ scanDefNames st (show a' ++ show b')) in
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
    if not strictConv then Nothing else
    go 5 (scanDefNames st (show x ++ show y))
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
          let ns' = nub (ns ++ scanDefNames st (show x' ++ show y')) in
          if length ns' == length ns then Nothing else go k ns'

||| ASSUME (docs/NovaElaboration.txt, ↓ step 8): append the equation to
||| Σ as a constraint entry — sig-eq/sig-ty-eq; the signature is OPEN
||| from here until a rerun stops minting the entry — and record its
||| display metadata alongside.
assume : Stmt -> String -> Maybe Stmt -> ElabM ()
assume stmt site comp = do
  st <- getSt
  case stmt of
    StElem ctx env a b ty => do
      if assumedMatchE st ctx a b ty
        then pure ()
        else modifySt $ \s =>
          let aK = rwNfElem st ctx a
              bK = rwNfElem st ctx b in
          { assumedE $= ((elemSize aK + elemSize bK, ctx, aK, bK, engNfT st ty) ::)
          , sig $= (:< SigEq ctx a b ty)
          , oblMeta $= (:< MkOblMeta env site comp (hintOf st)) } s
    StTy ctx env x y => do
      let x' = rwNfTy st ctx x
          y' = rwNfTy st ctx y
      if any (\(c, u, v) => c == ctx && ((u == x' && v == y') || (u == y' && v == x'))) st.assumedT
        then pure ()
        else modifySt $ \s =>
          { assumedT $= ((ctx, x', y') ::)
          , sig $= (:< SigTyEq ctx x y)
          , oblMeta $= (:< MkOblMeta env site comp (hintOf st)) } s
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
  attemptE : Ctx -> String -> Elem -> Elem -> Ty -> ElabM (Either String ECert)
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
              Left kerrMsg => pure (Left (site ++ " [replay failed: " ++ kerrMsg ++ "]"))
          else do
            let t0 = nowNs ()
            let cs0 = mkCandSet st ctx
            let t1 = bump "cands" (nowNs () - t0) (nowNs ())
            let cs = bump "candN" (cast (length cs0.all)) cs0
            let tyM = bump "sz-att-in" (cast (elemSize a + elemSize b)) ty
            -- measurement only — a δβ pass per attempt, skipped in strict mode
            let tyM2 = if strictConv then tyM
                         else bump "sz-att-nf" (cast (elemSize (betaElem st.sig a) + elemSize (betaElem st.sig b))) tyM
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
                      Left _ => pure (Left (site ++ " [replay failed: " ++ kerrMsg ++ "]"))

  attemptT : Ctx -> String -> Ty -> Ty -> ElabM (Either String ECert)
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
              Left kerrMsg => pure (Left (site ++ " [replay failed: " ++ kerrMsg ++ "]"))
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
                      Left _ => pure (Left (site ++ " [replay failed: " ++ kerrMsg ++ "]"))

  ||| Γ ⊢ a ≐ b : A ↓ — always succeeds; assumes what it cannot discharge.
  convElem : Ctx -> NameEnv -> String -> Maybe Stmt -> Elem -> Elem -> Ty -> ElabM (Maybe ECert)
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
            -- strict: sides decompose δ-FREE (comp), keeping the
            -- user's vocabulary; the type still gets head exposure
            let aB = if strictConv then compElem a else whnfE st.sig a
            let bB = if strictConv then compElem b else whnfE st.sig b
            let a' = rwNfElem st ctx a
            let b' = rwNfElem st ctx b
            let again = if (aB, bB) == (a', b') then Nothing else Just (a', b')
            n0 <- constraintCountM
            decompose site2 cur comp' aB bB again
              (if strictConv then exposeT st.modPrefix st.sig ty else rwNfTy st ctx ty)
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
    decompose : String -> Stmt -> Maybe Stmt -> Elem -> Elem -> Maybe (Elem, Elem) -> Ty -> ElabM ()
    decompose site cur comp' a' b' again tyW = do
        st <- getSt
        case (a', b', tyW) of
          -- congruence decomposition — faithful (an equivalence) for
          -- the type formers and universe codes, per Foundation's
          -- injectivity rules; merely sufficient for class (quotients
          -- are not injective — the witness path is the faithful
          -- route) and for neutral-spine congruence
          (NatIntro1 x, NatIntro1 y, _) =>
            ignore $ convElem ctx env site comp' x y Ty.NatTy
          (PiIntro f, PiIntro g, Ty.PiTy dom cod) =>
            ignore $ convElem (ctx :< dom) (env :< "x") site comp' f g cod
          (SigmaIntro u v, SigmaIntro u' v', Ty.SigmaTy dom cod) => do
            ignore $ convElem ctx env site comp' u u' dom
            ignore $ convElem ctx env site comp' v v' (substTy cod (Ext Id u'))
          -- injection decomposition — faithful (injection injectivity
          -- is derivable); an inj₁/inj₂ HEAD MISMATCH falls through
          -- and stays an obligation like every rigid mismatch
          (Inj1 x, Inj1 y, Ty.SumTy dom _) =>
            ignore $ convElem ctx env site comp' x y dom
          (Inj2 x, Inj2 y, Ty.SumTy _ cod) =>
            ignore $ convElem ctx env site comp' x y cod
          (Class x, Class y, Ty.Quotient dom rel) =>
            -- witness path: an ∥≡∥-shaped relation reduces the class
            -- equation to its underlying equation (el-quot-eq after
            -- reflection); other shapes keep the composite.
            (do st' <- getSt
                case rwNfElem st' ctx (substElem rel (Ext (Ext Id x) y)) of
                  Elem.EqTy l r t => ignore $ convElem ctx env site comp' l r t
                  _ => assume cur site comp)
          (Elem.PiTy x c, Elem.PiTy x' c', Ty.UniverseTy) => do
            ignore $ convElem ctx env site comp' x x' Ty.UniverseTy
            ignore $ convElem (ctx :< El x') (env :< "x") site comp' c c' Ty.UniverseTy
          (Elem.SigmaTy x c, Elem.SigmaTy x' c', Ty.UniverseTy) => do
            ignore $ convElem ctx env site comp' x x' Ty.UniverseTy
            ignore $ convElem (ctx :< El x') (env :< "x") site comp' c c' Ty.UniverseTy
          (Elem.SumTy x c, Elem.SumTy x' c', Ty.UniverseTy) => do
            -- code-sum-inj: both components at 𝕌 over Γ (no binder)
            ignore $ convElem ctx env site comp' x x' Ty.UniverseTy
            ignore $ convElem ctx env site comp' c c' Ty.UniverseTy
          (QuotTy x r, QuotTy x' r', Ty.UniverseTy) => do
            ignore $ convElem ctx env site comp' x x' Ty.UniverseTy
            ignore $ convElem (ctx :< El x' :< substTy (El x') Wk) (env :< "x" :< "y") site comp' r r' Ty.PropTy
          -- code-qiit identity: structural, like ty-qiit (the code and
          -- the type decode to the same former)
          (QSortC sg0 k0 es0, QSortC sg1 k1 es1, Ty.UniverseTy) =>
            if k0 == k1 && es0 == es1
              then case qsigDom0Pieces sg0 sg1 of
                     Just pieces => traverse_ (\(t0, t1) => ignore $ convTy ctx env site comp' t0 t1) pieces
                     Nothing => assume cur site comp
              else assume cur site comp
          -- sufficient direction at Ω: equal squashees give equal props
          -- (the faithful iff route lives in spEqStructC's propext)
          (Squash tA, Squash tB, Ty.PropTy) =>
            ignore $ convTy ctx env site comp' tA tB
          -- code-eq-cong at Ω — merely sufficient (≐ at Ω is iff; the
          -- faithful route is propext)
          (Elem.EqTy l r t, Elem.EqTy l' r' t', Ty.PropTy) => do
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
              ignore $ convElem (ctx :< Ty.NatTy :< substTy tyW' Wk) (env :< "i" :< "ih")
                                site comp' s s' (substTy tyW' (wkN 2))
            when (t0 /= t1) $
              ignore $ convElem ctx env site comp' t0 t1 Ty.NatTy
          (PiApp f x, PiApp g y, _) =>
            if f == g
              then do st' <- getSt
                      case (if strictConv then exposeT st'.modPrefix st'.sig else betaTy st'.sig)
                             <$> inferNe st' ctx f of
                        Just (Ty.PiTy dom _) => ignore $ convElem ctx env site comp' x y dom
                        _ => assume cur site comp
              else assume cur site comp
          _ => case again of
                 -- the beta-normal sides matched no case: retry with
                 -- the lemma-normalized ones before assuming
                 Just (aR, bR) => decompose site cur comp' aR bR Nothing tyW
                 Nothing => assume cur site comp

  ||| Γ ⊢ A ≐ B type ↓
  convTy : Ctx -> NameEnv -> String -> Maybe Stmt -> Ty -> Ty -> ElabM (Maybe ECert)
  convTy ctx env site comp tyA tyB = do
    r <- attemptT ctx site tyA tyB
    case r of
      Right cert => pure (Just cert)
      Left site2 => do
            st <- getSt
            let cur = StTy ctx env tyA tyB
            let comp' = comp <|> Just cur
            let aB = if strictConv then exposeT st.modPrefix st.sig tyA else whnfT st.sig tyA
            let bB = if strictConv then exposeT st.modPrefix st.sig tyB else whnfT st.sig tyB
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
    decomposeT : String -> Stmt -> Maybe Stmt -> Ty -> Ty -> Maybe (Ty, Ty) -> ElabM ()
    decomposeT site cur comp' tyA' tyB' again = do
        st <- getSt
        case (tyA', tyB') of
          (Ty.PiTy a0 b0, Ty.PiTy a1 b1) => do
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convTy (ctx :< a1) (env :< "x") site comp' b0 b1
          (Ty.SigmaTy a0 b0, Ty.SigmaTy a1 b1) => do
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convTy (ctx :< a1) (env :< "x") site comp' b0 b1
          (Ty.SumTy a0 b0, Ty.SumTy a1 b1) => do
            -- ty-sum-inj: both components over Γ — faithful
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convTy ctx env site comp' b0 b1
          (Ty.Quotient a0 r0, Ty.Quotient a1 r1) => do
            ignore $ convTy ctx env site comp' a0 a1
            ignore $ convElem (ctx :< a1 :< substTy a1 Wk) (env :< "x" :< "y") site comp' r0 r1 Ty.PropTy
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
          (Ty.NuTy f0, Ty.NuTy f1) =>
            case polyDom0Pieces f0 f1 of
              Just pieces => traverse_ (\(e0, e1) => ignore $ convElem ctx env site comp' e0 e1 Ty.UniverseTy) pieces
              Nothing => assume cur site comp
          (El x, El y) => ignore $ convElem ctx env site comp' x y Ty.UniverseTy
          (Prf x, Prf y) => ignore $ convElem ctx env site comp' x y Ty.PropTy
          (El x, rigid) => case codeOf rigid of
                             Just c => ignore $ convElem ctx env site comp' x c Ty.UniverseTy
                             Nothing => assume cur site comp
          (rigid, El y) => case codeOf rigid of
                             Just c => ignore $ convElem ctx env site comp' c y Ty.UniverseTy
                             Nothing => assume cur site comp
          _ => case again of
                 Just (aR, bR) => decomposeT site cur comp' aR bR Nothing
                 Nothing => assume cur site comp

-- ===== Bidirectional elaboration =====

structuralHint : String
structuralHint = " (ascribe the term: `(t : T)`)"

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
    do c <- map ({ unfolds := st.eqScope }) (spEqTyC spDepth st cs ctx ty tyX)
       case kCheckEqTy st.sig ctx kernelFuel c ty tyX of
         Right () => Just (tyX, c)
         Left _ => Nothing

preferPi : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferPi st ctx (Ty.PiTy a b) = Just (a, b, Nothing)
preferPi st ctx ty = case exposeHead st ty of
                       tyX@(Ty.PiTy a b) => Just (a, b, Just (tyX, MkECert [] FBeta))
                       _ => case rwNfTy st ctx ty of
                              tyX@(Ty.PiTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                              _ => Nothing

preferSigma : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferSigma st ctx (Ty.SigmaTy a b) = Just (a, b, Nothing)
preferSigma st ctx ty = case exposeHead st ty of
                          tyX@(Ty.SigmaTy a b) => Just (a, b, Just (tyX, MkECert [] FBeta))
                          _ => case rwNfTy st ctx ty of
                                 tyX@(Ty.SigmaTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                                 _ => Nothing

preferSum : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferSum st ctx (Ty.SumTy a b) = Just (a, b, Nothing)
preferSum st ctx ty = case exposeHead st ty of
                        tyX@(Ty.SumTy a b) => Just (a, b, Just (tyX, MkECert [] FBeta))
                        _ => case rwNfTy st ctx ty of
                               tyX@(Ty.SumTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                               _ => Nothing

||| A prop stuck only up to hypothesis rewriting (e.g. the relator's
||| ⊎-elim at neutral observations, unstuck by a variable-definition
||| hypothesis): rewrite it and bridge with an exposure certificate
||| from the ORIGINAL expected type.
exposeProp : ElabSt -> Ctx -> Ty -> Elem -> (Elem, Maybe (Ty, ECert))
exposeProp st ctx ty p =
  let pR = rwNfElem st ctx p in
  if pR == p then (p, Nothing)
  else case exposeCert st ctx ty (Prf pR) of
         Just e2 => (pR, Just e2)
         Nothing => (p, Nothing)

preferNu : ElabSt -> Ctx -> Ty -> Maybe (Poly, Maybe (Ty, ECert))
preferNu st ctx (Ty.NuTy f) = Just (f, Nothing)
preferNu st ctx ty = case exposeHead st ty of
                       tyX@(Ty.NuTy f) => Just (f, Just (tyX, MkECert [] FBeta))
                       _ => case rwNfTy st ctx ty of
                              tyX@(Ty.NuTy f) => (\e => (f, Just e)) <$> exposeCert st ctx ty tyX
                              _ => Nothing

preferQuot : ElabSt -> Ctx -> Ty -> Maybe (Ty, Elem, Maybe (Ty, ECert))
preferQuot st ctx (Ty.Quotient a r) = Just (a, r, Nothing)
preferQuot st ctx ty = case exposeHead st ty of
                         tyX@(Ty.Quotient a r) => Just (a, r, Just (tyX, MkECert [] FBeta))
                         _ => case rwNfTy st ctx ty of
                                tyX@(Ty.Quotient a r) => (\e => (a, r, Just e)) <$> exposeCert st ctx ty tyX
                                _ => Nothing

preferPrf : ElabSt -> Ctx -> Ty -> Maybe (Elem, Maybe (Ty, ECert))
preferPrf st ctx (Prf p) = Just (p, Nothing)
preferPrf st ctx ty = case exposeHead st ty of
                        tyX@(Prf p) => Just (p, Just (tyX, MkECert [] FBeta))
                        _ => case rwNfTy st ctx ty of
                               tyX@(Prf p) => (\e => (p, Just e)) <$> exposeCert st ctx ty tyX
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
  elabPoly : Ctx -> NameEnv -> String -> SPoly -> ElabM (Poly, List Skel)
  elabPoly ctx env site SPHole = pure (PHole, [])
  elabPoly ctx env site (SPConst a) = do
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
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
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
    recordBinder xr ctx env xn (El a')
    (f', fSks) <- elabPoly (ctx :< El a') (env :< xn) site f
    pure (PSigma a' f', aSk :: fSks)
  elabPoly ctx env site (SPPi (xn, xr) a f) = do
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
    recordBinder xr ctx env xn (El a')
    (f', fSks) <- elabPoly (ctx :< El a') (env :< xn) site f
    pure (PPi a' f', aSk :: fSks)

  elabTy : Ctx -> NameEnv -> String -> STy -> ElabM (Ty, Skel)
  elabTy ctx env site STyZero = pure (Ty.ZeroTy, Nd [] [])
  elabTy ctx env site STyOne = pure (Ty.OneTy, Nd [] [])
  elabTy ctx env site STyNat = pure (Ty.NatTy, Nd [] [])
  elabTy ctx env site STyUniv = pure (Ty.UniverseTy, Nd [] [])
  elabTy ctx env site (STySig x0) = do
    st <- getSt
    let x = resolveSigName st x0
    case sigLookup x st.sig of
      -- items are always declared in ε, so the reference carries the
      -- empty substitution
      Just (SigTyDef [<] _ _) => pure (Ty.SigVar x [<], Nd [] [])
      Just (SigTyDef _ _ _) => throw "\{site}: '\{x}' has a non-empty declaration context"
      Just (SigTyDecl [<] _) => pure (Ty.SigVar x [<], Nd [] [])
      Just _ => throw "\{site}: '\{x}' is not usable as a type here"
      Nothing => throw "\{site}: unknown signature name '\{x}'"
  elabTy ctx env site (STyPi x a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy (ctx :< a') (env :< x) site b
    pure (Ty.PiTy a' b', Nd [] [aSk, bSk])
  elabTy ctx env site (STySigma x a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy (ctx :< a') (env :< x) site b
    pure (Ty.SigmaTy a' b', Nd [] [aSk, bSk])
  elabTy ctx env site (STySum a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy ctx env site b
    pure (Ty.SumTy a' b', Nd [] [aSk, bSk])
  elabTy ctx env site (STyQuot a (nx, nxr) (ny, nyr) r) = do
    (a', aSk) <- elabTy ctx env site a
    recordBinder nxr ctx env nx a'
    recordBinder nyr (ctx :< a') (env :< nx) ny (substTy a' Wk)
    (r', rSk) <- checkElem (ctx :< a' :< substTy a' Wk) (env :< nx :< ny) site r Ty.PropTy
    pure (Ty.Quotient a' r', Nd [] [aSk, rSk])
  elabTy ctx env site (STyNu f) = do
    -- e-ty-nu
    (f', fSks) <- elabPoly ctx env site f
    pure (Ty.NuTy f', Nd [] fSks)
  elabTy ctx env site (STyEq l r t) = do
    -- e-ty-eq: the surface ≡-TYPE elaborates to Prf of the equality
    -- prop (equality is Ω-valued)
    (t', tSk) <- elabTy ctx env site t
    (l', lSk) <- checkElem ctx env site l t'
    (r', rSk) <- checkElem ctx env site r t'
    pure (Prf (Elem.EqTy l' r' t'), Nd [] [Nd [] [lSk, rSk, tSk]])
  elabTy ctx env site (STyEl e) = do
    (e', eSk) <- checkElem ctx env site e Ty.UniverseTy
    pure (El e', Nd [] [eSk])
  elabTy ctx env site STyProp = pure (Ty.PropTy, Nd [] [])
  elabTy ctx env site (STyPrf e) = do
    (e', eSk) <- checkElem ctx env site e Ty.PropTy
    pure (Prf e', Nd [] [eSk])
  export
  inferElem : Ctx -> NameEnv -> String -> SElem -> ElabM (Elem, Ty, Skel)
  inferElem ctx env site (SVar mrng n i) =
    case ctxLookup ctx i of
      Just ty => do
        recordBinder mrng ctx env n ty
        pure (CtxVar i, ty, Nd [] [])
      Nothing => throw "\{site}: variable index out of bounds"
  inferElem ctx env site (SSig mrng x0) = do
    st <- getSt
    let x = resolveSigName st x0
    -- cachedSigLookup: positive-only name index; the unknown-name
    -- error path below always re-scans (negatives are never cached)
    case cachedSigLookup st.sig x of
      Just (SigDef [<] _ _ ty) => do
        recordBinder mrng ctx env x0 ty
        pure (SigVar x [<], ty, Nd [] [])
      Just (SigDef _ _ _ _) => throw "\{site}: '\{x}' has a non-empty declaration context"
      Just (SigDecl [<] _ ty) => do
        recordBinder mrng ctx env x0 ty
        pure (SigVar x [<], ty, Nd [] [])
      Just _ => throw "\{site}: '\{x}' is not usable as a term here"
      Nothing => throw "\{site}: unknown name '\{x}'"
  inferElem ctx env site SUnitI = pure (OneIntro, Ty.OneTy, Nd [] [])
  inferElem ctx env site SZeroN = pure (NatIntro0, Ty.NatTy, Nd [] [])
  inferElem ctx env site (SSuc t) = do
    (t', tSk) <- checkElem ctx env site t Ty.NatTy
    pure (NatIntro1 t', Ty.NatTy, Nd [] [tSk])
  inferElem ctx env site (SApp f e) = do
    (f', fTy, fSk) <- inferElem ctx env site f
    st <- getSt
    case preferPi st ctx fTy of
      Just (a, b, _) => do
        (e', eSk) <- checkElem ctx env site e a
        pure (PiApp f' e', substTy b (Ext Id e'), Nd [] [fSk, eSk])
      Nothing => throw "\{site}: cannot apply a term of non-Π type\{structuralHint}"
  inferElem ctx env site (SProj1 t) = do
    (t', tTy, tSk) <- inferElem ctx env site t
    st <- getSt
    case preferSigma st ctx tTy of
      Just (a, b, _) => pure (SigmaElim1 t', a, Nd [] [tSk])
      Nothing => throw "\{site}: cannot project from a term of non-⨯ type\{structuralHint}"
  inferElem ctx env site (SProj2 t) = do
    (t', tTy, tSk) <- inferElem ctx env site t
    st <- getSt
    case preferSigma st ctx tTy of
      Just (a, b, _) => pure (SigmaElim2 t', substTy b (Ext Id (SigmaElim1 t')), Nd [] [tSk])
      Nothing => throw "\{site}: cannot project from a term of non-⨯ type\{structuralHint}"
  inferElem ctx env site (SAnn t ty) = do
    (ty', tySk) <- elabTy ctx env site ty
    (t', tSk) <- checkElem ctx env site t ty'
    pure (t', ty', addPayload (PIntroTy ty' tySk) tSk)
  inferElem ctx env site (SLet (x, xr) e b) = do
    -- e-let: the definiens is INFERRED (an annotated surface let
    -- arrives as an ascribed definiens); the body is elaborated under
    -- the value AND its unfolding hypothesis — a Prf of an equality
    -- prop, so E's HYPOTHESIS source reflects x ≐ e into discharge
    -- automatically: the definition is transparent inside the body
    (e', eTy, eSk) <- inferElem ctx env site e
    recordBinder xr ctx env x eTy
    let hyp = Prf (Elem.EqTy (CtxVar 0) (substElem e' Wk) (substTy eTy Wk))
    (b', bTy, bSk) <- inferElem (ctx :< eTy :< hyp) (env :< x :< wildcard) site b
    pure (Let e' b', substTy bTy (Ext (Ext Id e') Star), Nd [] [eSk, bSk])
  inferElem ctx env site (SNatElim (n, nr) mot z (n2, n2r) (ih, ihr) s t) = do
    recordBinder nr ctx env n Ty.NatTy
    (motTy, motSk) <- elabTy (ctx :< Ty.NatTy) (env :< n) site mot
    (z', zSk) <- checkElem ctx env site z (substTy motTy (Ext Id NatIntro0))
    recordBinder n2r ctx env n2 Ty.NatTy
    recordBinder ihr (ctx :< Ty.NatTy) (env :< n2) ih motTy
    (s', sSk) <- checkElem (ctx :< Ty.NatTy :< motTy) (env :< n2 :< ih) site s
                   (substTy motTy (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
    (t', tSk) <- checkElem ctx env site t Ty.NatTy
    pure (NatElim z' s' t', substTy motTy (Ext Id t'),
          Nd [PMotive motTy motSk] [zSk, sSk, tSk])
  inferElem ctx env site (SSumElim (zn, zr) mot (an, ar) l (bn, br) r t) = do
    (t', tTy, tSk) <- inferElem ctx env site t
    st <- getSt
    case preferSum st ctx tTy of
      Just (a, b, _) => do
        recordBinder zr ctx env zn (Ty.SumTy a b)
        (motTy, motSk) <- elabTy (ctx :< Ty.SumTy a b) (env :< zn) site mot
        recordBinder ar ctx env an a
        (l', lSk) <- checkElem (ctx :< a) (env :< an) site l
                       (substTy motTy (Ext Wk (Inj1 (CtxVar 0))))
        recordBinder br ctx env bn b
        (r', rSk) <- checkElem (ctx :< b) (env :< bn) site r
                       (substTy motTy (Ext Wk (Inj2 (CtxVar 0))))
        pure (SumElim l' r' t', substTy motTy (Ext Id t'),
              Nd [PMotive motTy motSk] [lSk, rSk, tSk])
      Nothing => throw "\{site}: ⊎-elim scrutinee has non-⊎ type\{structuralHint}"
  inferElem ctx env site (SQuotElim (zn, zr) mot (an, ar) f q) = do
    (q', qTy, qSk) <- inferElem ctx env site q
    st <- getSt
    case preferQuot st ctx qTy of
      Just (a, r, _) => do
        recordBinder zr ctx env zn (Ty.Quotient a r)
        (motTy, motSk) <- elabTy (ctx :< Ty.Quotient a r) (env :< zn) site mot
        recordBinder ar ctx env an a
        (f', fSk) <- checkElem (ctx :< a) (env :< an) site f
                       (substTy motTy (Ext Wk (Class (CtxVar 0))))
        -- well-definedness: f respects R (Foundation's f⁼ premise; the
        -- hypothesis is the DECODED relation, Prf R)
        let wk3 = Chain Wk (Chain Wk Wk)
        wd <- convElem (ctx :< a :< substTy a Wk :< Prf r) (env :< an :< (an ++ "'") :< "h")
          "\{site}: well-definedness of quot-elim case" Nothing
          (substElem f' (Ext wk3 (CtxVar 2)))
          (substElem f' (Ext wk3 (CtxVar 1)))
          (substTy motTy (Ext wk3 (Class (CtxVar 2))))
        pure (QuotElim f' q', substTy motTy (Ext Id q'),
              Nd [PMotive motTy motSk, PWD (certOr wd)] [fSk, qSk])
      Nothing => throw "\{site}: quot-elim scrutinee has non-quotient type\{structuralHint}"
  inferElem ctx env site SZeroC = pure (Elem.ZeroTy, Ty.UniverseTy, Nd [] [])
  inferElem ctx env site SOneC = pure (Elem.OneTy, Ty.UniverseTy, Nd [] [])
  inferElem ctx env site SNatC = pure (Elem.NatTy, Ty.UniverseTy, Nd [] [])
  inferElem ctx env site (SPiC x a b) = do
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
    (b', bSk) <- checkElem (ctx :< El a') (env :< x) site b Ty.UniverseTy
    pure (Elem.PiTy a' b', Ty.UniverseTy, Nd [] [aSk, bSk])
  inferElem ctx env site (SSigmaC x a b) = do
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
    (b', bSk) <- checkElem (ctx :< El a') (env :< x) site b Ty.UniverseTy
    pure (Elem.SigmaTy a' b', Ty.UniverseTy, Nd [] [aSk, bSk])
  inferElem ctx env site (SSumC a b) = do
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
    (b', bSk) <- checkElem ctx env site b Ty.UniverseTy
    pure (Elem.SumTy a' b', Ty.UniverseTy, Nd [] [aSk, bSk])
  inferElem ctx env site (SQuotC a (nx, nxr) (ny, nyr) r) = do
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
    recordBinder nxr ctx env nx (El a')
    recordBinder nyr (ctx :< El a') (env :< nx) ny (substTy (El a') Wk)
    (r', rSk) <- checkElem (ctx :< El a' :< substTy (El a') Wk) (env :< nx :< ny) site r Ty.PropTy
    pure (QuotTy a' r', Ty.UniverseTy, Nd [] [aSk, rSk])
  inferElem ctx env site (SSquash t) = do
    (t', tSk) <- elabTy ctx env site t
    pure (Squash t', Ty.PropTy, Nd [] [tSk])
  inferElem ctx env site SStar =
    throw "\{site}: cannot infer the type of ⋆\{structuralHint}"
  inferElem ctx env site (SStarWit _) =
    throw "\{site}: cannot infer the type of ⋆ ⟨witness⟩\{structuralHint}"
  inferElem ctx env site (SStarUsing _) =
    throw "\{site}: cannot infer the type of ⋆ using (…)\{structuralHint}"
  inferElem ctx env site (SChain _ _) =
    throw "\{site}: cannot infer the type of a chain (its equality comes from the expected Prf type)\{structuralHint}"
  inferElem ctx env site (SSquashElim _ _ _) =
    throw "\{site}: cannot infer the type of squash-elim\{structuralHint}"
  inferElem ctx env site (SEqC l r t) = do
    -- e-eq: the equality PROP — the ambient is a TYPE (large types
    -- included); there is no 𝕌-code for equality
    (t', tSk) <- elabTy ctx env site t
    (l', lSk) <- checkElem ctx env site l t'
    (r', rSk) <- checkElem ctx env site r t'
    pure (Elem.EqTy l' r' t', Ty.PropTy, Nd [] [lSk, rSk, tSk])
  inferElem ctx env site (SNuC f) = do
    -- e-code-nu
    (f', fSks) <- elabPoly ctx env site f
    pure (Elem.NuTy f', Ty.UniverseTy, Nd [] fSks)
  inferElem ctx env site (SOut t) = do
    -- e-out: fully inference-driven, the polynomial read off the
    -- scrutinee's type
    (t', tTy, tSk) <- inferElem ctx env site t
    st <- getSt
    case preferNu st ctx tTy of
      Just (p, _) => pure (Out t', El (reflectPoly p (Elem.NuTy p)), Nd [] [tSk])
      Nothing => throw "\{site}: out scrutinee has non-ν type\{structuralHint}"
  inferElem ctx env site (SCorec _ _ _ _) =
    throw "\{site}: cannot infer the type of corec (the polynomial comes from the expected ν-type)\{structuralHint}"
  inferElem ctx env site (SCoind _ _ _ _ _ _ _ _) =
    throw "\{site}: cannot infer the type of coind (the equation comes from the expected Prf type)\{structuralHint}"
  inferElem ctx env site (SInj1 _) =
    throw "\{site}: cannot infer the type of inj₁ (the other summand is undetermined)\{structuralHint}"
  inferElem ctx env site (SInj2 _) =
    throw "\{site}: cannot infer the type of inj₂ (the other summand is undetermined)\{structuralHint}"
  inferElem ctx env site (SLam _ _) =
    throw "\{site}: cannot infer the type of a λ\{structuralHint}"
  inferElem ctx env site (SPair _ _) =
    throw "\{site}: cannot infer the type of a pair\{structuralHint}"
  inferElem ctx env site (SClass _) =
    throw "\{site}: cannot infer the type of class\{structuralHint}"
  inferElem ctx env site (SZeroElim _) =
    throw "\{site}: cannot infer the type of 𝟘-elim\{structuralHint}"

  export
  checkElem : Ctx -> NameEnv -> String -> SElem -> Ty -> ElabM (Elem, Skel)
  checkElem ctx env site (SLam (x, xr) t) ty = do
    st <- getSt
    case preferPi st ctx ty of
      Just (a, b, exp) => do
        recordBinder xr ctx env x a
        (t', tSk) <- checkElem (ctx :< a) (env :< x) site t b
        pure (PiIntro t', withExpose exp (Nd [] [tSk]))
      Nothing => throw "\{site}: λ checked against a non-Π type\{structuralHint}"
  checkElem ctx env site (SPair u v) ty = do
    st <- getSt
    case preferSigma st ctx ty of
      Just (a, b, exp) => do
        (u', uSk) <- checkElem ctx env site u a
        (v', vSk) <- checkElem ctx env site v (substTy b (Ext Id u'))
        pure (SigmaIntro u' v', withExpose exp (Nd [] [uSk, vSk]))
      Nothing => throw "\{site}: pair checked against a non-⨯ type\{structuralHint}"
  checkElem ctx env site (SInj1 a) ty = do
    st <- getSt
    case preferSum st ctx ty of
      Just (dom, _, exp) => do
        (a', aSk) <- checkElem ctx env site a dom
        pure (Inj1 a', withExpose exp (Nd [] [aSk]))
      Nothing => throw "\{site}: inj₁ checked against a non-⊎ type\{structuralHint}"
  checkElem ctx env site (SInj2 b) ty = do
    st <- getSt
    case preferSum st ctx ty of
      Just (_, cod, exp) => do
        (b', bSk) <- checkElem ctx env site b cod
        pure (Inj2 b', withExpose exp (Nd [] [bSk]))
      Nothing => throw "\{site}: inj₂ checked against a non-⊎ type\{structuralHint}"
  checkElem ctx env site (SCorec (xn, xr) a f u) ty = do
    -- e-corec: checking-only, like λ and class
    st <- getSt
    case preferNu st ctx ty of
      Just (p, exp) => do
        (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
        recordBinder xr ctx env xn (El a')
        (f', fSk) <- checkElem (ctx :< El a') (env :< xn) site f
                       (substTy (El (reflectPoly p a')) Wk)
        (u', uSk) <- checkElem ctx env site u (El a')
        pure (Corec p a' f' u', withExpose exp (Nd [] [aSk, fSk, uSk]))
      Nothing => throw "\{site}: corec checked against a non-ν type\{structuralHint}"
  checkElem ctx env site (SCoind (xn, xr) (yn, yr) rS pS (mxn, mxr) (myn, myr) (mhn, mhr) qS) ty = do
    -- e-coind: el-nu-coind's surface form, at Prf (l ≡ r ∈ El (ν F)) —
    -- invariant, endpoint proof, one-step closure at the relator
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throw "\{site}: coind checked against a non-Prf type\{structuralHint}"
      Just (pc, exp) => do
        let pcUse = case pc of
                      Elem.EqTy _ _ _ => pc
                      _ => exposeCode st pc
        case pcUse of
          Elem.EqTy l rhs ety => do
            let fM = case whnfT st.sig ety of
                       Ty.NuTy f => Just f
                       _ => case rwNfTy st ctx ety of
                              Ty.NuTy f => Just f
                              _ => Nothing
            case fM of
              Nothing => throw "\{site}: coind at an equation over a non-ν type\{structuralHint}"
              Just f => do
                let nuT = Ty.NuTy f
                recordBinder xr ctx env xn nuT
                recordBinder yr (ctx :< nuT) (env :< xn) yn (substTy nuT Wk)
                (r', skR) <- checkElem (ctx :< nuT :< substTy nuT Wk) (env :< xn :< yn) site rS Ty.PropTy
                (p', skp) <- checkElem ctx env site pS (Prf (substElem r' (Ext (Ext Id l) rhs)))
                let ctx3 = ctx :< nuT :< substTy nuT Wk :< Prf r'
                let wk3 = Chain Wk (Chain Wk Wk)
                let f3 = substPoly f wk3
                let r3 = substElem r' (under (under wk3))
                recordBinder mxr ctx env mxn nuT
                recordBinder myr (ctx :< nuT) (env :< mxn) myn (substTy nuT Wk)
                recordBinder mhr (ctx :< nuT :< substTy nuT Wk) (env :< mxn :< myn) mhn (Prf r')
                (q', skq) <- checkElem ctx3 (env :< mxn :< myn :< mhn) site qS
                               (Prf (liftPoly f3 r3 (Out (CtxVar 2)) (Out (CtxVar 1))))
                pure (Star, withExpose exp (Nd [PNuCoind r' skR p' skp q' skq] []))
          _ => throw "\{site}: coind checked against a non-equality proposition\{structuralHint}"
  checkElem ctx env site (SClass a) ty = do
    st <- getSt
    case preferQuot st ctx ty of
      Just (dom, rel, exp) => do
        (a', aSk) <- checkElem ctx env site a dom
        pure (Class a', withExpose exp (Nd [] [aSk]))
      Nothing => throw "\{site}: class checked against a non-quotient type\{structuralHint}"
  checkElem ctx env site (SZeroElim t) ty = do
    (t', tSk) <- checkElem ctx env site t Ty.ZeroTy
    pure (ZeroElim t', Nd [] [tSk])
  checkElem ctx env site SStar ty = do
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throw "\{site}: ⋆ checked against a non-Prf type\{structuralHint}"
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
            c <- convElem ctx env "\{site}: checking ⋆" Nothing l r t
            pure (Star, withExpose exp (Nd [PReflEq (certOr c)] []))
          Squash sq =>
            case exposeHead st sq of
              Ty.OneTy => pure (Star, withExpose exp (Nd [PSquashWit OneIntro (Nd [] [])] []))
              _ => throw "\{site}: ⋆ can prove only equality props and 𝟙-shaped squashes automatically (write `⋆ ⟨witness⟩` to supply one directly)"
          _ => throw "\{site}: ⋆ checked against a non-evident proposition\{structuralHint}"
  -- ⋆ using (…): the SStar rule verbatim, under a discharge scope —
  -- only the named lemmas (plus hypotheses) participate, so the site
  -- is deterministic and module-local (SearchlessElaboration.md §5.3).
  -- Names resolve like any signature reference (aliases first); a name
  -- that is absent, or present but not an equation lemma of the
  -- visible store, is a structural error — it could only scope the
  -- site to nothing.
  checkElem ctx env site (SStarUsing ns) ty = do
    (rs, eqs) <- resolveUsingNames site ns
    withScope (Just rs) (withEqScope eqs (checkElem ctx env site SStar ty))
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
  checkElem ctx env site (SChain x0 links) ty = do
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throw "\{site}: a chain proves an equality — checked against a non-Prf type\{structuralHint}"
      Just (p, exp) => do
        let pUse = case p of
                     Elem.EqTy _ _ _ => p
                     _ => exposeCode st p
        case pUse of
          Elem.EqTy l r tA => do
            (x0', _) <- checkElem ctx env site x0 tA
            mids <- traverse (\(_, x) => map fst (checkElem ctx env site x tA)) links
            cands <- traverse (\(j, _) => linkCand j) links
            adjCerts <- adjacencies tA 1 x0' (zip cands mids)
            cert <- composite tA l r cands adjCerts
            pure (Star, withExpose exp (Nd [PReflEq (certOr cert)] []))
          _ => throw "\{site}: chain checked against a non-equality proposition\{structuralHint}"
   where
    ||| a link justification, inferred and reflected into a ground
    ||| candidate (closed under component decomposition, like a
    ||| hypothesis)
    linkCand : SElem -> ElabM (List Cand)
    linkCand j = do
      (j', jTy, _) <- inferElem ctx env site j
      st <- getSt
      case exposeHead st jTy of
        Prf pj => case exposeCode st pj of
          Elem.EqTy u v _ =>
            pure (closeCand (MkCand "chain link" 0 []
                    (engNfE st u) (engNfE st v)
                    (\wk, _ => Just (weakenElemN wk j', [])) [] []))
          _ => throw "\{site}: a chain justification must prove an equation"
        _ => throw "\{site}: a chain justification must prove an equation"

    ||| discharge each adjacency against ITS link only; a failure is
    ||| an ordinary obligation sited at its step (and, being scoped,
    ||| gets a global-store hint if one exists)
    adjacencies : Ty -> Nat -> Elem -> List (List Cand, Elem) -> ElabM (List (Maybe ECert))
    adjacencies tA i prev [] = pure []
    adjacencies tA i prev ((cs, next) :: rest) = do
      m <- withLocal cs spDepth $
             convElem ctx env "\{site}: chain, step \{show i}" Nothing prev next tA
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
              let cert = MkECert (concat segs) FBeta in
              case kCheckEqElem st.sig ctx kernelFuel cert l r tA of
                Right () => pure (Just cert)
                Left _ => fallback
            Nothing => fallback
     where
      fallback : ElabM (Maybe ECert)
      fallback =
        withLocal (concat cands) (length links + spDepth) $
          convElem ctx env "\{site}: checking chain" Nothing l r tA
  checkElem ctx env site (SStarWit w) ty = do
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throw "\{site}: ⋆ checked against a non-Prf type\{structuralHint}"
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
            mcert <- case (exposeHead st qty, pl, pr, w) of
              (Ty.PropTy, _, _, SPair f g) => do
                let pTy = Prf pl
                let qTy = Prf pr
                (f', fSk) <- checkElem ctx env site f (Ty.PiTy pTy (substTy qTy Wk))
                (g', gSk) <- checkElem ctx env site g (Ty.PiTy qTy (substTy pTy Wk))
                pure (Just (MkECert [] (FPropExt f' fSk g' gSk)))
              (Ty.Quotient _ rel, Class a, Class b, _) => do
                (w', wSk) <- checkElem ctx env site w
                               (Prf (substElem rel (Ext (Ext Id a) b)))
                pure (Just (MkECert [] (FWitnessPrf w' wSk)))
              _ => pure Nothing
            case mcert of
              Just cert => pure (Star, withExpose exp (Nd [PReflEq cert] []))
              Nothing => do
                (w', _) <- checkElem ctx env site w (Prf pN)
                let cert = MkECertF Nothing [MkStep True [] (LProof w') [] False] FBeta st.eqScope
                pure (Star, withExpose exp (Nd [PReflEq cert] []))
          _ => throw "\{site}: ⋆ checked against Prf of a non-∥∥ code\{structuralHint}"
  checkElem ctx env site (SSquashElim e xn body) ty = do
    st <- getSt
    (e', eTy, eSk) <- inferElem ctx env site e
    case preferPrf st ctx eTy of
      Nothing => throw "\{site}: squash-elim scrutinee has non-Prf type\{structuralHint}"
      Just (p, _) =>
        case exposeCode st p of
          Squash a =>
            -- el-squash-e-prf: body proves (Prf q)[↑] under a
            -- hypothetical inhabitant of the raw squashee a; the goal
            -- must itself be Prf q — no elimination into arbitrary types
            case preferPrf st ctx ty of
              Nothing => throw "\{site}: squash-elim checked against a non-Prf goal (el-squash-e-prf reaches only further propositions)\{structuralHint}"
              Just (q, exp) => do
                recordBinder (snd xn) ctx env (fst xn) a
                (body', bodySk) <- checkElem (ctx :< a) (env :< fst xn) site body (substTy (Prf q) Wk)
                pure (Star, withExpose exp (Nd [PSquashElim e' eSk body' bodySk] []))
          _ => throw "\{site}: squash-elim scrutinee checked against Prf of a non-∥∥ code\{structuralHint}"
  checkElem ctx env site (SLet (x, xr) e b) ty = do
    -- e-let-check: let PROPAGATES the ambient mode to its body (a
    -- checking-only body form works under a let without ascription).
    -- The expected type lives over Γ, so the body checks at its double
    -- weakening — fully general, not an approximation (docs/
    -- NovaKernel.txt §8, el-let)
    (e', eTy, eSk) <- inferElem ctx env site e
    recordBinder xr ctx env x eTy
    let hyp = Prf (Elem.EqTy (CtxVar 0) (substElem e' Wk) (substTy eTy Wk))
    (b', bSk) <- checkElem (ctx :< eTy :< hyp) (env :< x :< wildcard) site b
                   (substTy (substTy ty Wk) Wk)
    pure (Let e' b', Nd [] [eSk, bSk])
  checkElem ctx env site t ty = do
    (t', inferred, tSk) <- inferElem ctx env site t
    c <- convTy ctx env "\{site}: inferred vs expected type" Nothing inferred ty
    pure (t', addPayload (PSwitch (certOr c)) tSk)

-- ===== Items =====

||| Register a just-accepted definition's equation (if its type peels to
||| a Prf of an equality prop) as a rewrite candidate: the WHOLE
||| context (telescope + peeled Πs) is parametric, so the lemma
||| applies in any context.
addLemma : String -> Ctx -> Ty -> ElabM ()
addLemma name delta ty = do
  st <- getSt
  let (delta', peeled) = peelPis delta (peelNf st ty)
  -- equality is Ω-valued: a lemma registers when its peeled type is a
  -- Prf whose prop normalizes to an equality (squashed spellings
  -- converge here by code-squash-prf)
  let meq : Maybe (Elem, Elem, Ty) =
        case peeled of
          Prf p => case exposeCode st p of
                     Elem.EqTy l r t => Just (l, r, t)
                     _ => Nothing
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

liftQE : String -> Either QErr a -> ElabM a
liftQE site (Left e) = throw "\{site}: \{e}"
liftQE site (Right x) = pure x

||| Emit one core definition item: kernel-check, extend Σ, register a
||| lemma if it is ≡-typed. Mirrors elabItem's tail for surface defs.
emitCoreDef : String -> String -> Ty -> Skel -> Elem -> Skel -> ElabM ()
emitCoreDef site x ty tySk body bodySk = do
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "\{site}: duplicate signature name '\{x}'"
    Nothing => pure ()
  after <- oblCount
  kernelAccept "\{site} \{x}"
    (\ksig => kCheckDefItem ksig kernelFuel (MkKDefArt q [] ty tySk body bodySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q body ty), vis $= (:< (x, q)) }
  addLemma q [<] ty

emitCoreTyDef : String -> String -> Ty -> Skel -> ElabM ()
emitCoreTyDef site x ty tySk = do
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "\{site}: duplicate signature name '\{x}'"
    Nothing => pure ()
  after <- oblCount
  kernelAccept "\{site} \{x}"
    (\ksig => kCheckTyDefItem ksig kernelFuel (MkKTyDefArt q [] ty tySk))
    (after == 0)
  modifySt $ { sig $= (:< SigTyDef [<] q ty), vis $= (:< (x, q)) }

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

||| One-shot elaboration of an item (the body of elabItem below).
elabItemGo : SItem -> ElabM String

||| Elaborate an item under the searchless default scope: hypotheses
||| and computation only, unless the def's using-clause overrides it
||| (the SDef handler installs the resolved names over this).
||| NOVA_GLOBAL_STORE=1 restores the historical whole-store search.
export
elabItem : SItem -> ElabM String
elabItem item = withScope (if scopedMode then Just [] else Nothing) $ do
  pre <- getSt
  timedM "item \{pre.modPrefix}.\{itemName item}" (elabItemGo item)

elabItemGo (SDef x ty body muses) = do
  census <- openCensus
  st <- getSt
  -- the Σ-name is qualified by the module; the root file's entries
  -- stay bare
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "def \{x}: duplicate signature name"
    Nothing => pure ()
  -- the item's discharge scope: its using-clause if it has one; under
  -- NOVA_SCOPED, an unannotated item sees hypotheses and computation
  -- only (the searchless default — SearchlessElaboration.md §5.3);
  -- otherwise the full store (the historical behavior)
  scEqs <- the (ElabM (Maybe (List String), List String)) $ case muses of
          Just ns => do
            (rs, eqs) <- resolveUsingNames "def \{x}" ns
            pure (Just rs, eqs)
          Nothing => pure (if scopedMode then Just [] else Nothing, [])
  let (sc, eqs) = scEqs
  -- items live in the EMPTY context: parameters are Π-binders in the
  -- item's type, references are bare names
  (ty', tySk) <- withScope sc (withEqScope eqs (elabTy [<] [<] "def \{x}" ty))
  (body', bodySk) <- withScope sc (withEqScope eqs (checkElem [<] [<] "def \{x}" body ty'))
  -- clean means the RUN is clean: an earlier item's assumption poisons
  -- everything after it (the kernel Σ cannot contain the earlier item,
  -- so references to it are unresolvable anyway)
  after <- oblCount
  kernelAccept "def \{x}"
    (\ksig => kCheckDefItem ksig kernelFuel (MkKDefArt q [] ty' tySk body' bodySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q body' ty'), vis $= (:< (x, q)) }
  addLemma q [<] ty'
  suffix <- opensSuffix census
  pure "defined \{x}\{suffix}"
elabItemGo (SDeclDef nrng x ty) = do
  -- a DECLARATION (docs/NovaFoundation.txt, sig-decl at ε): a stuck
  -- named entry — reported as open, blocking acceptance; references
  -- type by el-sig-decl. The remedy is supplying the definiens (or importing a
  -- module that will, once such a mechanism exists).
  census <- openCensus
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "def \{x}: duplicate signature name"
    Nothing => pure ()
  (ty', tySk) <- elabTy [<] [<] "def \{x}" ty
  modifySt $ { sig $= (:< SigDecl [<] q ty')
             , declMeta $= (:< MkDeclMeta q [<] "def \{x}" nrng)
             , vis $= (:< (x, q)) }
  -- a DECLARED equation is a lemma like any accepted one: its stuck
  -- reference is a proof element (el-sig-decl), so el-reflect makes
  -- the equation judgementally available — that is what an abstract
  -- interface's equational axioms are FOR
  addLemma q [<] ty'
  suffix <- opensSuffix census
  pure "declared \{x}\{suffix}"
elabItemGo (STypeDef x ty) = do
  census <- openCensus
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "type \{x}: duplicate signature name"
    Nothing => pure ()
  (ty', tySk) <- elabTy [<] [<] "type \{x}" ty
  after <- oblCount
  kernelAccept "type \{x}"
    (\ksig => kCheckTyDefItem ksig kernelFuel (MkKTyDefArt q [] ty' tySk))
    (after == 0)
  modifySt $ { sig $= (:< SigTyDef [<] q ty'), vis $= (:< (x, q)) }
  suffix <- opensSuffix census
  pure "defined type \{x}\{suffix}"
elabItemGo (SData params decls) = do
  census <- openCensus
  let site = "data " ++ (case decls of
                           (d :: _) => d.dqname
                           [] => "")
  case decls of
    [] => throw "\{site}: empty data literal"
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
  suffix <- opensSuffix census
  pure ("defined data (" ++ joinBy ", " (map (.dqname) decls) ++ ")" ++ suffix)
 where
  zipWithIndex : Nat -> List a -> List (Nat, a)
  zipWithIndex _ [] = []
  zipWithIndex i (x :: xs) = (i, x) :: zipWithIndex (S i) xs

  elabParams : String -> Ctx -> NameEnv -> List (String, STy)
            -> ElabM (Ctx, NameEnv, List Ty)
  elabParams site ctx env [] = pure (ctx, env, [])
  elabParams site ctx env ((x, t) :: rest) = do
    (t', _) <- elabTy ctx env site t
    (ctx', env', tys) <- elabParams site (ctx :< t') (env :< x) rest
    pure (ctx', env', t' :: tys)

  sgAt : QSig -> Nat -> QSig
  sgAt sg d = substQSig sg (wkN d)

  wrapParams : List Ty -> Ty -> Ty
  wrapParams ptys ty = foldr Ty.PiTy ty ptys

  elabSQTm : String -> Ctx -> NameEnv -> SQTm -> ElabM QTm
  elabSQTm site ectx env (SQVar _ i) = pure (QVar i)
  elabSQTm site ectx env (SQAppE f e) = do
    f' <- elabSQTm site ectx env f
    -- external arguments elaborate by INFERENCE (they are neutral in
    -- the emitted fragment); the kernel re-checks them at the arity
    (e', _, _) <- inferElem ectx env site e
    pure (QAppE f' e')
  elabSQTm site ectx env (SQAppI f a) =
    [| QAppI (elabSQTm site ectx env f) (elabSQTm site ectx env a) |]

  elabDecl : String -> Ctx -> NameEnv -> SQDecl -> ElabM QTy
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

  entryAt : String -> QSig -> Nat -> ElabM QTy
  entryAt site sg k = case qEntry sg k of
    Just e => pure e
    Nothing => throw "\{site}: internal — entry out of range"

  ||| A sort: a code-valued def when the signature is SMALL; for a
  ||| LARGE signature, a type item (nullary sorts only — an indexed
  ||| large family has no closed-item spelling).
  emitSort : String -> (Nat, List Ty) -> QSig -> Nat -> String -> ElabM ()
  emitSort site (np, ptys) sg k nm = do
    entry <- entryAt site sg k
    (tel, _, _) <- liftQE site (reflTel sg (qwAt k) entry)
    let n = length tel
    if qSigSmall sg
      then do
        let ty = wrapParams ptys (foldr Ty.PiTy Ty.UniverseTy tel)
        let body = wrapLams (np + n) (QSortC (sgAt sg n) k (varSpine n))
        emitCoreDef site nm ty (Nd [] []) body (Nd [] [])
      else if n == 0 && np == 0
        then emitCoreTyDef site nm (QSort sg k [<]) (Nd [] [])
        else throw "\{site}: an indexed or parameterized sort of a LARGE signature has no closed-item spelling (make the signature small)"

  ||| A point constructor: the saturated former, η-expanded once.
  emitCtor : String -> (Nat, List Ty) -> QSig -> Nat -> String -> ElabM ()
  emitCtor site (np, ptys) sg k nm = do
    entry <- entryAt site sg k
    ty0 <- liftQE site (reflQTy sg (qwAt k) entry)
    let n = qtyBinders entry
    let body = wrapLams (np + n) (QCtor (sgAt sg n) k (varSpine n))
    emitCoreDef site nm (wrapParams ptys ty0) (Nd [] []) body (Nd [] [])

  ||| An equation constructor: a ⋆-lemma (Prf-typed), licensed by
  ||| el-qiit-path (a qpath step behind the ⋆'s equation certificate).
  ||| On later
  ||| items this def is an accepted lemma, so the QIIT's imposed
  ||| equations feed discharge through the standard store.
  emitEq : String -> (Nat, List Ty) -> QSig -> Nat -> String -> ElabM ()
  emitEq site (np, ptys) sg k nm = do
    entry <- entryAt site sg k
    (tel, wEnd, hd) <- liftQE site (reflTel sg (qwAt k) entry)
    (lq, rq, uq) <- liftQE site (eqHead hd)
    lE <- liftQE site (reflTm sg wEnd lq)
    rE <- liftQE site (reflTm sg wEnd rq)
    uT <- liftQE site (reflCodeTy sg wEnd uq)
    let n = length tel
    let ty = wrapParams ptys (foldr Ty.PiTy (Prf (Elem.EqTy lE rE uT)) tel)
    let body = wrapLams (np + n) Star
    let cert = MkECert [MkStep True [] (LPath (sgAt sg n) k (varSpine n)) [] False] FBeta
    emitCoreDef site nm ty (Nd [] []) body (nestSkel (np + n) (Nd [PReflEq cert] []))

  ||| The eliminator def for sort s: motives (code-valued), methods,
  ||| COHERENCES AS HYPOTHESES (≡-typed arguments — extensionality's
  ||| dividend), then the indices and the eliminee. The body is the
  ||| core eliminator; its qcoh certificates replay from the coherence
  ||| binders by el-reflect.
  ||| The eliminator def for sort s. Two flavors: prop=False is the
  ||| code-valued one (motives … → 𝕌, coherences as Prf-typed
  ||| hypothesis binders); prop=True is the Ω-valued one (motives
  ||| … → Ω, results through Prf) — by proof irrelevance its
  ||| coherences hold outright (el-prf-prop), so it takes NO
  ||| coherence arguments and its qcoh certificates are bare FProp.
  emitElim : String -> (Nat, List Ty) -> QSig -> Nat -> (prop : Bool) -> String -> ElabM ()
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
    let wrapMot : Elem -> Ty
        wrapMot = if prop then Prf else El
    let motEnd : Ty
        motEnd = if prop then Ty.PropTy else Ty.UniverseTy
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
                pure (foldr Ty.PiTy
                        (Ty.PiTy (QSort (substQSig sgJ wEndJ.ups) sj (varSpine aj)) motEnd)
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
                let swc = MkECert [MkStep True [0, 1] (LPath (sgAt sgJ dlen) ej spineArgs) [] True] FBeta
                -- the ≡-TYPE became Prf (eq-prop): one more skeleton
                -- level (Prf's child 0 is the prop; its children are
                -- l, r and the carried type)
                let eqSk = Nd [] [Nd [] [Nd [] [], Nd [PSwitch swc] [], Nd [] []]]
                pure (foldr Ty.PiTy (Prf (Elem.EqTy lhs rhs cty)) dtel, nestPiSkel dlen eqSk))
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
              Nothing => throw "\{site}: internal — sort ordinal"
    let cS = minus nS (S ordS) + nM + nH + nI + 1
    let idxAtEnd = toList (substSubNorm (varSpine nI) Wk)
    let resTy = wrapMot (PiApp (applyChain (CtxVar cS) idxAtEnd) (CtxVar 0))
    let defTy = wrapParams ptys
                  (foldr Ty.PiTy resTy (cTys ++ mTys ++ hTys ++ sTel ++ [wTy]))
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
    -- step, then FBeta). Prop flavor: the coherence sides live at a
    -- Prf motive, so proof irrelevance closes them outright (FProp).
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

elabItemGo (SClausalDef nrng x ty etaName witness clauses) = do
  -- a def with DEFINING EQUATIONS (docs/NovaElaboration.txt,
  -- "Defining equations"): an ITEM MACRO. The expansion is pure
  -- surface-level synthesis (Nova.Elaboration.Clauses); the batch —
  -- the definition, the Π-closed clause lemmas, the uniqueness
  -- lemma — elaborates through the ordinary item pipeline, so
  -- obligations, lemma registration, kernel checking and the report
  -- need no clause awareness at all. A Left is a STRUCTURAL error;
  -- everything non-structural degrades inside the expansion (witness
  -- tier / declaration tier) rather than failing.
  census <- openCensus
  case expandClausal nrng x ty etaName witness clauses of
    Left err => throw "def \{x}: \{err}"
    Right (MkExpansion items echo) => do
      ignore $ traverse elabItemGo items
      suffix <- opensSuffix census
      pure (echo ++ suffix)

-- ===== Report =====

prettyTelescope : FixTable -> Ctx -> NameEnv -> String
prettyTelescope tbl ctx env = go (toList ctx) (toList env)
 where
  -- print left-to-right; each entry's type prints under the env prefix
  go' : SnocList String -> List Ty -> List String -> List String
  go' pfx [] _ = []
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
  "      at: \{obl.site}" ++
  (case obl.composite of
     Nothing => ""
     Just c => "\n      from composite: \{prettyStmt tbl c}") ++
  (case obl.hint of
     Nothing => ""
     Just h => "\n      hint: \{h}")

||| One module of a program: its dotted name ("" for the root file,
||| whose entries stay unqualified), its import lines, its items.
public export
record ModUnit where
  constructor MkModUnit
  mname : String
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

oblReport : FixTable -> List Obligation -> String
oblReport tbl os =
  "open obligations (\{show (length os)}):\n" ++
  joinBy "\n" (zipWith (prettyObligation tbl) [0 .. minus (length os) 1] os)

||| Render one declaration for the report (exported for LSP consumers,
||| like prettyObligation).
export
prettyDecl : FixTable -> DeclView -> String
prettyDecl tbl h =
  let tele = prettyTelescope tbl h.dvctx h.dvenv in
  "  [\{h.dvname}] " ++ (if tele == "" then "" else tele ++ " ") ++
  (case h.dvty of
     Just ty => "⊢ ? : \{prettyTyN tbl h.dvenv ty}"
     Nothing => "⊢ ? type") ++
  "\n      at: \{h.dvsite}"

declReport : FixTable -> List DeclView -> String
declReport tbl hs =
  "open declarations (\{show (length hs)}):\n" ++
  joinBy "\n" (map (prettyDecl tbl) hs)

||| The composed end-of-run report of everything keeping Σ
||| non-definitional; empty exactly when the run is accepted.
openReport : FixTable -> ElabSt -> Maybe String
openReport tbl st =
  case (oblView st, declView st) of
    ([], []) => Nothing
    (os, hs) => Just $ joinBy "\n"
      ((case os of [] => []; _ => [oblReport tbl os]) ++
       (case hs of [] => []; _ => [declReport tbl hs]))

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
enterModule : String -> List String -> ElabM ()
enterModule name imps = do
  st <- getSt
  let archived = if st.modPrefix == "" && isNil st.ownLemmas
                   then st.modLemmas
                   else (st.modPrefix, st.ownLemmas) :: st.modLemmas
  let archivedI = (st.modPrefix, st.curImports) :: st.modImports
  let closure = modClosure archivedI imps
  let visible = concatMap (\(_, ls) => ls) (filter (\(m, _) => m `elem` closure) archived)
  let (cs, sh, re, hp) = sigCandParts visible
  putSt $ { modPrefix := name, vis := [<]
          , lemmas := visible, ownLemmas := []
          , modLemmas := archived, modImports := archivedI
          , curImports := imps
          , candCs := cs, candShrink := sh, candRest := re
          , candHops := hp, candRw := sh ++ re } st

installImports : List SImport -> ElabM ()
installImports [] = pure ()
installImports (MkSImport m opens :: rest) = do
  go opens
  installImports rest
 where
  go : List String -> ElabM ()
  go [] = pure ()
  go (o :: os) = do
    st <- getSt
    let q = "\{m}.\{o}"
    case sigLookup q st.sig of
      Just _ => do modifySt $ { vis $= (:< (o, q)) }; go os
      Nothing => throw "import \{m}: it defines no '\{o}'"

||| Elaborate a dependency-ordered list of modules (the loader's
||| output; the last unit is the root). Every non-root module must be
||| ACCEPTED — clean and fully kernel-checked — before anything may
||| import it; the root reports its obligations as usual.
export
elabProgram : List ModUnit -> String
elabProgram units = go initSt units []
 where
  finish : FixTable -> ElabSt -> List String -> String
  finish tbl st echoes =
    joinBy "\n" echoes ++ "\n" ++
    (case openReport tbl st of
       Nothing => "Accepted."
       Just rep => rep)

  goItems : ElabSt -> List (Maybe Range, SItem) -> Either (List String, String) (ElabSt, List String)
  goItems st [] = Right (st, [])
  goItems st ((_, item) :: rest) =
    case runElabM (elabItem item) st of
      Left err => Left ([], err)
      Right (st', echo) =>
        case goItems st' rest of
          Left (echoes, err) => Left (echo :: echoes, err)
          Right (st'', echoes) => Right (st'', echo :: echoes)

  go : ElabSt -> List ModUnit -> List String -> String
  go st [] echoes = joinBy "\n" (echoes ++ ["Error: empty program"])
  go st (MkModUnit name imps tbl items _ :: rest) echoes = do
    -- a fresh visibility table per module: its own imports only, and a
    -- lemma store scoped to its import closure
    case runElabM (enterModule name (map mname imps) >> installImports imps) st of
      Left err =>
        if strictConv && not (null rest)
          -- SURVEY MODE: an import of a dropped module cascades — drop too
          then go st rest (echoes ++ ["warning: module \{name} DROPPED (strict survey): \{err}"])
          else joinBy "\n" (echoes ++ ["Error: \{err}"])
      Right (st, ()) =>
        let hdr = if name == "" then [] else ["module \{name}:"] in
        case goItems st items of
          Left (itemEchoes, err) =>
            if strictConv && not (null rest)
              -- SURVEY MODE: a hard failure (automation the strict
              -- subset removed, mid-checking) drops the module and
              -- continues — its importers cascade into the same path
              then go st rest (echoes ++ hdr ++ itemEchoes ++
                     ["warning: module \{name} DROPPED (strict survey): \{err}"])
              else joinBy "\n" (echoes ++ hdr ++ itemEchoes ++ ["Error: \{err}"])
          Right (st', itemEchoes) =>
            case rest of
              [] => finish tbl st' (echoes ++ hdr ++ itemEchoes)
              _ =>
                -- only ACCEPTED modules are importable: a module's
                -- signature segment must be DEFINITIONAL
                if strictConv
                  -- SURVEY MODE: continue past the gate so ONE run maps
                  -- the whole corpus's fallout. COUNT open entries
                  -- instead of rendering the report — the report renders
                  -- every accumulated obligation and is quadratic across
                  -- modules (the root still renders the full report once)
                  then let opens = \s => length (filter (not . sigEntryIsDef) (toList s))
                           d = minus (opens st'.sig) (opens st.sig) in
                       go st' rest (echoes ++ hdr ++ itemEchoes ++
                         (if d == 0 then []
                          else ["warning: module \{name}: +\{show d} open entries (strict survey)"]))
                  else case openReport tbl st' of
                    Nothing => go st' rest (echoes ++ hdr ++ itemEchoes)
                    Just rep => joinBy "\n" (echoes ++ hdr ++ itemEchoes) ++ "\n" ++
                          rep ++ "\n" ++
                          "Error: module \{name} has open obligations and cannot be imported"

||| Elaborate a dependency-ordered program to its final kernel Σ,
||| requiring the ENTIRE program — root included — to be accepted with
||| zero obligations: a consumer of the resulting Σ (Nova.Compute, via
||| Nova.Elaboration.Loader.runPath) assumes closed, well-typed input,
||| never a provisional signature built on assumed equations. Same fold
||| as elabProgram/elabProgramReport, shaped for that different
||| consumer instead of a display report.
export
elabProgramSig : List ModUnit -> Either String Sig
elabProgramSig units = go initSt units
 where
  goItems : ElabSt -> List (Maybe Range, SItem) -> Either String ElabSt
  goItems st [] = Right st
  goItems st ((_, item) :: rest) =
    case runElabM (elabItem item) st of
      Left err => Left err
      Right (st', _) => goItems st' rest

  go : ElabSt -> List ModUnit -> Either String Sig
  go st [] = Left "empty program"
  go st (MkModUnit name imps tbl items _ :: rest) =
    let st = either (const st) fst (runElabM (enterModule name (map mname imps)) st) in
    case runElabM (installImports imps) st of
      Left err => Left err
      Right (st, ()) =>
        case goItems st items of
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
    Left (_, err) => "Parse error: \{err}"
    Right (toks, ([], decls, items)) => elabProgram [MkModUnit "" [] decls items toks]
    Right (_, (_, _, _)) => "Error: this entry point resolves no imports (use the module-aware loader)"

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
binderInfos : FixTable -> ElabSt -> List (Range, String)
binderInfos tbl st =
  [ (r, "\{x} : \{prettyTyN tbl env (displayTy st ty)}")
  | (m, r, ctx, env, x, ty) <- toList st.binderTypes, m == "" ]

public export
record ElabReport where
  constructor MkElabReport
  obligations : List (String, Maybe Range, Obligation)
  ||| open declarations, pre-rendered (module, range, report text) —
  ||| the range is the declaring item's
  decls : List (String, Maybe Range, String)
  ||| the ROOT module's binder occurrences with rendered types —
  ||| hover ascription for λ/eliminator binders
  binderTable : List (Range, String)
  ||| at most one per run — elaboration of a dependency-ordered program
  ||| stops at the first hard failure, same as `elabProgram`
  errors : List (String, Maybe Range, String)

export
elabProgramReport : List ModUnit -> ElabReport
elabProgramReport units = go initSt units [] [] []
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
  Tagged = (List (String, Maybe Range, Obligation), List (String, Maybe Range, String))

  goItems : FixTable -> String -> ElabSt -> List (Maybe Range, SItem)
          -> Either (Tagged, Maybe Range, String)
                    (ElabSt, Tagged)
  goItems tbl mname st [] = Right (st, ([], []))
  goItems tbl mname st ((rng, item) :: rest) =
    case runElabM (elabItem item) st of
      Left err => Left (([], []), rng, err)
      Right (st', _) =>
        let tagged = map (\o => (mname, rng, o)) (newObls st st')
            -- a declaration diagnostic lands on the declaring item
            taggedH = map (\h => (mname, h.dvrange <|> rng, prettyDecl tbl h)) (newDecls st st') in
        case goItems tbl mname st' rest of
          Left ((obls, hs), r, err) => Left ((tagged ++ obls, taggedH ++ hs), r, err)
          Right (st'', (obls, hs)) => Right (st'', (tagged ++ obls, taggedH ++ hs))

  go : ElabSt -> List ModUnit -> List (String, Maybe Range, Obligation) -> List (String, Maybe Range, String) -> List (String, Maybe Range, String) -> ElabReport
  go st [] obls hs errs = MkElabReport obls hs [] errs
  go st (MkModUnit name imps tbl items _ :: rest) obls hs errs =
    let st = either (const st) fst (runElabM (enterModule name (map mname imps)) st) in
    case runElabM (installImports imps) st of
      Left err => MkElabReport obls hs (binderInfos tbl st) (errs ++ [(name, Nothing, err)])
      Right (st, ()) =>
        case goItems tbl name st items of
          Left ((itemObls, itemHs), rng, err) => MkElabReport (obls ++ itemObls) (hs ++ itemHs) [] (errs ++ [(name, rng, err)])
          Right (st', (itemObls, itemHs)) =>
            case rest of
              [] => MkElabReport (obls ++ itemObls) (hs ++ itemHs) (binderInfos tbl st') errs
              _ =>
                -- only ACCEPTED modules are importable: a module's
                -- signature segment must be DEFINITIONAL
                case (oblView st', declView st') of
                  ([], []) => go st' rest (obls ++ itemObls) (hs ++ itemHs) errs
                  _ => MkElabReport (obls ++ itemObls) (hs ++ itemHs) (binderInfos tbl st')
                         (errs ++ [(name, Nothing, "module \{name} has open obligations and cannot be imported")])
