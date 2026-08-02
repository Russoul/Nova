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
import Data.Maybe
import Data.SnocList
import Data.String

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.Beta
import Nova.Kernel.QIIT
import Nova.Kernel.Parser
import Nova.Kernel

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range
import Nova.Elaboration.Named
import Nova.Elaboration.Surface
import Nova.Elaboration.Parser

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
  ||| the proof lives in the query context Γ
  emit : List (Nat, Elem) -> Maybe (Elem, List Sel)
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

||| Display metadata of one hole — same discipline as OblMeta: the
||| hole itself is a declaration entry of Σ; this record is aligned
||| with Σ's declaration entries in minting order.
record HoleMeta where
  constructor MkHoleMeta
  hname : String
  henv : NameEnv
  hsite : String
  ||| may the elaborator instantiate this hole? (surface `_x`; a rigid
  ||| `?x` is never solved) — policy, not theory: both are sig-decls
  hsolvable : Bool
  ||| the minting occurrence's source span (LSP hover/diagnostics)
  hrange : Maybe Range

record ElabSt where
  constructor MkElabSt
  sig : Sig
  ||| the KERNEL's signature: extended only by kernel-accepted items —
  ||| the authoritative Σ (docs/NovaPipeline.txt)
  kernelSig : Sig
  lemmas : List Cand
  assumedE : List (Ctx, Elem, Elem, Ty)   -- normalized keys of assumed elem equations
  assumedT : List (Ctx, Ty, Ty)           -- normalized keys of assumed type equations
  ||| display metadata for Σ's constraint entries, in surfacing order
  ||| (invariant: one per SigEq/SigTyEq of `sig`, appended together)
  oblMeta : SnocList OblMeta
  ||| display metadata for Σ's declaration entries (holes), in minting
  ||| order (invariant: one per SigDecl/SigTyDecl of `sig`)
  holeMeta : SnocList HoleMeta
  ||| every hole occurrence's source span (minting AND reuse sites),
  ||| for LSP position lookup
  holeOccs : SnocList (String, Range)
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

initSt : ElabSt
initSt = MkElabSt [<] [<] [] [] [] [<] [<] [<] [<] "" [<]

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

-- ===== Small core utilities =====

||| Rewriting-recorded steps are always proof-licensed (path licenses
||| are only ever EMITTED, for the data item's eq-lemmas).
licProof : StepLic -> Elem
licProof (LProof p) = p
licProof (LPath _ _ _) = assert_total $ idris_crash "licProof: path license in a rewrite trace"

||| The identity NORMAL substitution over a context of length n:
||| ☐ₙ₋₁, ..., ☐₀ (outermost first) — how a hole minted at the ambient
||| context is referenced at its own site.
idSpine : Nat -> SubNorm
idSpine Z = [<]
idSpine (S n) = cast (map CtxVar (reverse [0 .. n]))

||| The identity spine of a length-n entry context, weakened under k
||| further binders: ☐ₖ₊ₙ₋₁, ..., ☐ₖ — how a hole minted at Γ is
||| referenced at Γ ▷ Δ (|Δ| = k).
wkSpine : (n : Nat) -> (k : Nat) -> SubNorm
wkSpine Z k = [<]
wkSpine (S n) k = cast (map CtxVar (reverse [k .. k + n]))

||| Rewrite every signature reference through `f` (Nothing = keep):
||| the workhorse of prefix-legalization — inlining a later def's
||| definiens, or renaming a later hole to its inserted twin.
mapRefsT : (String -> SubNorm -> Maybe Elem) -> Ty -> Ty
mapRefsSub : (String -> SubNorm -> Maybe Elem) -> SubNorm -> SubNorm
mapRefsQTm : (String -> SubNorm -> Maybe Elem) -> QTm -> QTm
mapRefsQTy : (String -> SubNorm -> Maybe Elem) -> QTy -> QTy
mapRefsQSig : (String -> SubNorm -> Maybe Elem) -> QSig -> QSig

mapRefsE : (String -> SubNorm -> Maybe Elem) -> Elem -> Elem
mapRefsE f (SigVar x es) =
  let es2 = mapRefsSub f es in
  fromMaybe (SigVar x es2) (f x es2)
mapRefsE f (CtxVar n) = CtxVar n
mapRefsE f (ZeroElim t) = ZeroElim (mapRefsE f t)
mapRefsE f OneIntro = OneIntro
mapRefsE f NatIntro0 = NatIntro0
mapRefsE f (NatIntro1 t) = NatIntro1 (mapRefsE f t)
mapRefsE f (NatElim z s t) = NatElim (mapRefsE f z) (mapRefsE f s) (mapRefsE f t)
mapRefsE f (PiIntro g) = PiIntro (mapRefsE f g)
mapRefsE f (PiApp g e) = PiApp (mapRefsE f g) (mapRefsE f e)
mapRefsE f (SigmaIntro a b) = SigmaIntro (mapRefsE f a) (mapRefsE f b)
mapRefsE f (SigmaElim1 t) = SigmaElim1 (mapRefsE f t)
mapRefsE f (SigmaElim2 t) = SigmaElim2 (mapRefsE f t)
mapRefsE f Elem.ZeroTy = Elem.ZeroTy
mapRefsE f Elem.OneTy = Elem.OneTy
mapRefsE f Elem.NatTy = Elem.NatTy
mapRefsE f (Elem.PiTy a b) = Elem.PiTy (mapRefsE f a) (mapRefsE f b)
mapRefsE f (Elem.SigmaTy a b) = Elem.SigmaTy (mapRefsE f a) (mapRefsE f b)
mapRefsE f (Elem.EqTy l r t) = Elem.EqTy (mapRefsE f l) (mapRefsE f r) (mapRefsT f t)
mapRefsE f (QuotTy a r) = QuotTy (mapRefsE f a) (mapRefsE f r)
mapRefsE f (Class a) = Class (mapRefsE f a)
mapRefsE f (QuotElim g q) = QuotElim (mapRefsE f g) (mapRefsE f q)
mapRefsE f (Squash t) = Squash (mapRefsT f t)
mapRefsE f Star = Star
mapRefsE f (QSortC sg k es) = QSortC (mapRefsQSig f sg) k (mapRefsSub f es)
mapRefsE f (QCtor sg k es) = QCtor (mapRefsQSig f sg) k (mapRefsSub f es)
mapRefsE f (QElim sg k ms fs es w) =
  QElim (mapRefsQSig f sg) k (map (mapRefsT f) ms) (map (mapRefsE f) fs)
        (mapRefsSub f es) (mapRefsE f w)

mapRefsT f Ty.ZeroTy = Ty.ZeroTy
mapRefsT f Ty.OneTy = Ty.OneTy
mapRefsT f Ty.NatTy = Ty.NatTy
mapRefsT f Ty.UniverseTy = Ty.UniverseTy
mapRefsT f (Ty.PiTy a b) = Ty.PiTy (mapRefsT f a) (mapRefsT f b)
mapRefsT f (Ty.SigmaTy a b) = Ty.SigmaTy (mapRefsT f a) (mapRefsT f b)
mapRefsT f (El e) = El (mapRefsE f e)
mapRefsT f PropTy = PropTy
mapRefsT f (Prf e) = Prf (mapRefsE f e)
mapRefsT f (Quotient a r) = Quotient (mapRefsT f a) (mapRefsE f r)
mapRefsT f (Ty.SigVar x es) = Ty.SigVar x (mapRefsSub f es)
mapRefsT f (QSort sg k es) = QSort (mapRefsQSig f sg) k (mapRefsSub f es)

mapRefsSub f [<] = [<]
mapRefsSub f (es :< e) = mapRefsSub f es :< mapRefsE f e

mapRefsQTm f (QVar i) = QVar i
mapRefsQTm f (QAppE g e) = QAppE (mapRefsQTm f g) (mapRefsE f e)
mapRefsQTm f (QAppI g a) = QAppI (mapRefsQTm f g) (mapRefsQTm f a)
mapRefsQTm f (QEqC l r u) = QEqC (mapRefsQTm f l) (mapRefsQTm f r) (mapRefsQTm f u)

mapRefsQTy f QU = QU
mapRefsQTy f (QEl t) = QEl (mapRefsQTm f t)
mapRefsQTy f (QPiExt a b) = QPiExt (mapRefsT f a) (mapRefsQTy f b)
mapRefsQTy f (QPiInd u b) = QPiInd (mapRefsQTm f u) (mapRefsQTy f b)

mapRefsQSig f = map (mapRefsQTy f)

||| Every signature name an element references (with duplicates).
collectRefsE : Elem -> List String
collectRefsE e = go e
 where
  goT : Ty -> List String
  goQTm : QTm -> List String
  goQTy : QTy -> List String
  go : Elem -> List String
  go (SigVar x es) = x :: concatMap go (toList es)
  go (CtxVar _) = []
  go (ZeroElim t) = go t
  go OneIntro = []
  go NatIntro0 = []
  go (NatIntro1 t) = go t
  go (NatElim z s t) = go z ++ go s ++ go t
  go (PiIntro f) = go f
  go (PiApp f x) = go f ++ go x
  go (SigmaIntro a b) = go a ++ go b
  go (SigmaElim1 t) = go t
  go (SigmaElim2 t) = go t
  go Elem.ZeroTy = []
  go Elem.OneTy = []
  go Elem.NatTy = []
  go (Elem.PiTy a b) = go a ++ go b
  go (Elem.SigmaTy a b) = go a ++ go b
  go (Elem.EqTy l r t) = go l ++ go r ++ goT t
  go (QuotTy a r) = go a ++ go r
  go (Class a) = go a
  go (QuotElim f q) = go f ++ go q
  go (Squash t) = goT t
  go Star = []
  go (QSortC sg k es) = concatMap goQTy sg ++ concatMap go (toList es)
  go (QCtor sg k es) = concatMap goQTy sg ++ concatMap go (toList es)
  go (QElim sg k ms fs es w) =
    concatMap goQTy sg ++ concatMap goT ms ++ concatMap go fs ++
    concatMap go (toList es) ++ go w

  goQTm (QVar _) = []
  goQTm (QAppE f e) = goQTm f ++ go e
  goQTm (QAppI f a) = goQTm f ++ goQTm a
  goQTm (QEqC l r u) = goQTm l ++ goQTm r ++ goQTm u

  goQTy QU = []
  goQTy (QEl t) = goQTm t
  goQTy (QPiExt a b) = goT a ++ goQTy b
  goQTy (QPiInd u b) = goQTm u ++ goQTy b

  goT Ty.ZeroTy = []
  goT Ty.OneTy = []
  goT Ty.NatTy = []
  goT Ty.UniverseTy = []
  goT (Ty.PiTy a b) = goT a ++ goT b
  goT (Ty.SigmaTy a b) = goT a ++ goT b
  goT (El x) = go x
  goT PropTy = []
  goT (Prf x) = go x
  goT (Quotient a r) = goT a ++ go r
  goT (Ty.SigVar x es) = x :: concatMap go (toList es)
  goT (QSort sg k es) = concatMap goQTy sg ++ concatMap go (toList es)

||| ONE δ-step at the head: a definition reference unfolds to its
||| definiens under the spine; anything else is left alone. Used to
||| walk a hole solution back INTO the declaration's prefix (a later
||| def's body may be prefix-legal even when its name is not) without
||| beta-normalizing the whole term.
unfoldHead : Sig -> Elem -> Maybe Elem
unfoldHead sig (SigVar x es) =
  case sigLookup x sig of
    Just (SigDef _ _ a _) => Just (substElem a (embed es))
    _ => Nothing
unfoldHead sig (PiApp f e) = map (\f' => PiApp f' e) (unfoldHead sig f)
unfoldHead sig _ = Nothing

||| Strengthen away the k innermost binders (Nothing if any of them
||| is mentioned) — how a solution found at a binder-extended
||| occurrence moves back to the hole's own context.
strengthenK : Nat -> Elem -> Maybe Elem
strengthenK Z t = Just t
strengthenK (S k) t = strengthenElem 0 t >>= strengthenK k

strengthenKTy : Nat -> Ty -> Maybe Ty
strengthenKTy Z t = Just t
strengthenKTy (S k) t = strengthenTy 0 t >>= strengthenKTy k

||| The AMBIENT embedded Nova type pieces of two same-shape QIIT
||| signatures, paired entrywise — the external Π-domains that stand
||| at (or strengthen to) the ambient context, which is where an
||| instantiated parameter lands (`El _nat` vs `El ℕ`) no matter how
||| deep the entry buries it (vcons : (n : El ℕ) (x : El a) → …).
||| Nothing on any ToS-structural mismatch (entry count, binder
||| shapes, ToS codes). Domains that genuinely use their local ToS
||| binders are skipped: their equality follows from the ambient
||| pieces once solved, via the composite retry.
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

||| Position of the entry binding a name (leftmost/oldest first).
sigIndexOf : String -> List SigEntry -> Maybe Nat
sigIndexOf q = go 0
 where
  go : Nat -> List SigEntry -> Maybe Nat
  go i [] = Nothing
  go i (e :: rest) = if sigEntryName e == Just q then Just i else go (S i) rest

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
-- the relation is an Ω-element in BOTH the type former and the code:
-- El (A / R) ≜ El A / R, so it passes through unchanged
codeOf (Quotient a r) = QuotTy <$> codeOf a <*> Just r
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
matchElemP k d b Elem.ZeroTy Elem.ZeroTy = Just
matchElemP k d b Elem.OneTy Elem.OneTy = Just
matchElemP k d b Elem.NatTy Elem.NatTy = Just
matchElemP k d b (Elem.PiTy a c) (Elem.PiTy a' c') =
  \bs => matchElemP k d b a a' bs >>= matchElemP k d (1 + b) c c'
matchElemP k d b (Elem.SigmaTy a c) (Elem.SigmaTy a' c') =
  \bs => matchElemP k d b a a' bs >>= matchElemP k d (1 + b) c c'
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

elemSize : Elem -> Nat
elemSize (CtxVar _) = 1
elemSize (ZeroElim t) = S (elemSize t)
elemSize OneIntro = 1
elemSize NatIntro0 = 1
elemSize (NatIntro1 t) = S (elemSize t)
elemSize (NatElim z s t) = S (elemSize z + elemSize s + elemSize t)
elemSize (PiIntro f) = S (elemSize f)
elemSize (PiApp f e) = S (elemSize f + elemSize e)
elemSize (SigmaIntro u v) = S (elemSize u + elemSize v)
elemSize (SigmaElim1 t) = S (elemSize t)
elemSize (SigmaElim2 t) = S (elemSize t)
elemSize Elem.ZeroTy = 1
elemSize Elem.OneTy = 1
elemSize Elem.NatTy = 1
elemSize (Elem.PiTy a b) = S (elemSize a + elemSize b)
elemSize (Elem.SigmaTy a b) = S (elemSize a + elemSize b)
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

tySize Ty.ZeroTy = 1
tySize Ty.OneTy = 1
tySize Ty.NatTy = 1
tySize Ty.UniverseTy = 1
tySize Ty.PropTy = 1
tySize (Ty.PiTy a b) = S (tySize a + tySize b)
tySize (Ty.SigmaTy a b) = S (tySize a + tySize b)
tySize (El e) = S (elemSize e)
tySize (Prf e) = S (elemSize e)
tySize (Quotient a r) = S (tySize a + elemSize r)
tySize (Ty.SigVar _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
tySize (QSort _ _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)

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
  go b Elem.ZeroTy Elem.ZeroTy m = Just m
  go b Elem.OneTy Elem.OneTy m = Just m
  go b Elem.NatTy Elem.NatTy m = Just m
  go b (Elem.PiTy a d) (Elem.PiTy a' d') m = go b a a' m >>= go (1+b) d d'
  go b (Elem.SigmaTy a d) (Elem.SigmaTy a' d') m = go b a a' m >>= go (1+b) d d'
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
ordered : List Cand -> List Cand
ordered cs =
  let usable = filter (\c => elemSize c.rhs <= elemSize c.lhs && not (permutative c)) cs
      shrinking = filter (\c => elemSize c.rhs < elemSize c.lhs) usable
      rest = filter (\c => not (elemSize c.rhs < elemSize c.lhs)) usable
  in shrinking ++ rest

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
  (prfMain, selsMain) <- c.emit bs
  sigma <- instSub c.params 0 bs
  let instStep = \ps : PStep => MkStep side (pi ++ ps.ppath) (LProof (substElem ps.pprf sigma)) ps.psels ps.pflip
  let pre = map (\ps => { flip $= not } (instStep ps)) (reverse c.preL)
  let post = map instStep c.postR
  pure (pre ++ [MkStep side pi (LProof prfMain) selsMain False] ++ post)

materializeFlip : Cand -> Bindings -> (onLhs : Bool) -> Maybe (List Step)
materializeFlip c bs side = do
  (prfMain, selsMain) <- c.emit bs
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
  descend (Elem.PiTy a c')   =
    first [ at 0 0 a (\a' => Elem.PiTy a' c')
          , at 1 1 c' (\c'' => Elem.PiTy a c'') ]
  descend (Elem.SigmaTy a c') =
    first [ at 0 0 a (\a' => Elem.SigmaTy a' c')
          , at 1 1 c' (\c'' => Elem.SigmaTy a c'') ]
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
rewriteTyS side c pi d (El e) =
  (\(e', st) => (El e', st)) <$> rewriteElemS side c (0 :: pi) d e
rewriteTyS side c pi d (Quotient a r) =
  ((\(a', st) => (Quotient a' r, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(r', st) => (Quotient a r', st)) <$> rewriteElemS side c (1 :: pi) (2 + d) r)
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

rwNfElemS : Sig -> List Cand -> (side : Bool) -> Elem -> (Elem, List Step)
rwNfElemS sig cands side e =
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

rwNfTyS : Sig -> List Cand -> (side : Bool) -> Ty -> (Ty, List Step)
rwNfTyS sig cands side ty =
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

-- ===== Candidates in scope =====

selArity : Sel -> Nat
selArity (SelCod _) = 1
selArity (SelQRel _ _) = 2
selArity _ = 0

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
    , emit := \bs => do
        let parentBs = mapMaybe (\(i, e) => if i >= n then Just (minus i n, e) else Nothing) bs
        (p, sels) <- c.emit parentBs
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
  go (QuotTy a0 r0) (QuotTy a1 r1) =
    comp SelQDom a0 a1
    ++ closeCand (child (\bs => [| SelQRel (lookup 1 bs) (lookup 0 bs) |]) 2
                        [El a1, substTy (El a1) Wk] r0 r1)
  go _ _ = []

||| Eq-typed hypotheses of Γ (leading Πs peeled) as candidates with base
||| Γ. Ground hypotheses (no peeled binders) are additionally normalized
||| against the lemma store, RECORDING the normalization so the kernel
||| can bridge from the raw reflected equation.
hypCands : ElabSt -> Ctx -> List Cand
hypCands st ctx = concatMap closeCand (mapMaybe candAt [0 .. minus (length ctx) 1])
 where
  lemmaRw : List Cand
  lemmaRw = ordered st.lemmas

  toPSteps : List Step -> List PStep
  toPSteps = map (\s => MkPStep s.path (licProof s.lic) s.sels s.flip)

  -- a hypothesis licenses an equation when its (peeled) type is a Prf
  -- whose prop normalizes to an equality (the one pathway — squashed
  -- spellings converge by code-squash-prf during normalization)
  eqShape : Ty -> Maybe (Elem, Elem, Ty)
  eqShape (Prf p) =
    case betaElem st.sig p of
      Elem.EqTy l r t => Just (l, r, t)
      _ => Nothing
  eqShape _ = Nothing

  candAt : Nat -> Maybe Cand
  candAt i = do
    tyI <- ctxLookup ctx i
    let (ctx', peeled) = peelPis ctx (betaTy st.sig tyI)
    let k = minus (length ctx') (length ctx)
    case eqShape peeled of
      Just (l, r, t) =>
        let mk : Bindings -> Maybe (Elem, List Sel)
            mk = \bs => do
              args <- traverse (\p => lookup p bs)
                        (the (List Nat) (if k == 0 then [] else reverse [0 .. minus k 1]))
              pure (foldl PiApp (CtxVar i) args, the (List Sel) [])
        in if k == 0
             then let (l1, lSteps) = rwNfElemS st.sig lemmaRw True (betaElem st.sig l)
                      (r1, rSteps) = rwNfElemS st.sig lemmaRw True (betaElem st.sig r)
                  in Just (MkCand "hypothesis" 0 [] l1 r1 mk (toPSteps lSteps) (toPSteps rSteps))
             else Just (MkCand "hypothesis" k (lastEntries k ctx')
                          (betaElem st.sig l) (betaElem st.sig r) mk [] [])
      Nothing => Nothing

record CandSet where
  constructor MkCandSet
  all : List Cand
  rw : List Cand
  hops : List Cand

mkCandSet : ElabSt -> Ctx -> CandSet
mkCandSet st ctx =
  -- degenerate candidates (sides identical after normalization) carry
  -- no content beyond beta and — with a bare-parameter lhs — would
  -- match ANYTHING as a hop, emitting ill-typed junk steps
  let cs = filter (\c => c.lhs /= c.rhs) (st.lemmas ++ hypCands st ctx)
      rws = ordered cs
      hopsOnly = filter (\c => permutative c || elemSize c.rhs > elemSize c.lhs) cs
  in MkCandSet cs rws hopsOnly

rwNfElem : ElabSt -> Ctx -> Elem -> Elem
rwNfElem st ctx e = fst (rwNfElemS st.sig (mkCandSet st ctx).rw True e)

rwNfTy : ElabSt -> Ctx -> Ty -> Ty
rwNfTy st ctx ty = fst (rwNfTyS st.sig (mkCandSet st ctx).rw True ty)

-- ===== Neutral type inference =====

inferNe : ElabSt -> Ctx -> Elem -> Maybe Ty
inferNe st ctx (CtxVar i) = ctxLookup ctx i
inferNe st ctx (PiApp f x) =
  case betaTy st.sig <$> inferNe st ctx f of
    Just (Ty.PiTy a b) => Just (substTy b (Ext Id x))
    _ => Nothing
inferNe st ctx (SigmaElim1 t) =
  case betaTy st.sig <$> inferNe st ctx t of
    Just (Ty.SigmaTy a b) => Just a
    _ => Nothing
inferNe st ctx (SigmaElim2 t) =
  case betaTy st.sig <$> inferNe st ctx t of
    Just (Ty.SigmaTy a b) => Just (substTy b (Ext Id (SigmaElim1 t)))
    _ => Nothing
inferNe st ctx (SigVar x es) =
  case sigLookup x st.sig of
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

  wk : Cand -> Cand
  wk c = { lhs $= (\e => substElem e (liftK c.params))
         , rhs $= (\e => substElem e (liftK c.params)) } c

spDepth : Nat
spDepth = 3

prefixSteps : Nat -> List Step -> List Step
prefixSteps i = map ({ path $= (i ::) })

||| Steps of a certificate that is pure steps + beta (flattenable into
||| a parent at a path); Nothing when the final is type-directed.
flatSteps : ECert -> Maybe (List Step)
flatSteps (MkECertF Nothing steps FBeta) = Just steps
flatSteps _ = Nothing

||| ... and with no proofs needed at all (safe under binders, where a
||| Γ-level proof reference would go out of scope).
stepFree : ECert -> Bool
stepFree (MkECertF Nothing [] FBeta) = True
stepFree _ = False

mutual
  ||| Γ ⊢ a ≐ b : A, speculatively; Just cert = dischargeable with this
  ||| evidence.
  spEqElemC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Maybe ECert
  spEqElemC dep st cs ctx a b ty =
    -- expose the equation's type by lemma normalization; when that
    -- takes steps, the certificate carries them as a TYPE BRIDGE and
    -- the whole replay happens at the exposed type (where positions
    -- the steps land on are structurally determined)
    let (tyX, tySteps) = rwNfTyS st.sig cs.rw True ty
        bridge = case tySteps of
                   [] => Nothing
                   _ => Just (tyX, MkECert tySteps FBeta)
        (a', aSteps) = rwNfElemS st.sig cs.rw True a
        (b', bSteps) = rwNfElemS st.sig cs.rw False b
        base = aSteps ++ bSteps
        tyN = betaTy st.sig tyX in
    if a' == b'
      then Just (MkECertF bridge base FBeta)
      else
        (do rest <- candMatchC dep st cs ctx a' b' tyN >>= unbridged
            pure (MkECertF bridge (base ++ rest.steps) rest.final))
        <|> (do rest <- spEqStructC dep st cs ctx a' b' tyN >>= unbridged
                pure (MkECertF bridge (base ++ rest.steps) rest.final))
        <|> (do congSteps <- spCongC dep st cs ctx a' b'
                pure (MkECertF bridge (base ++ congSteps) FBeta))
   where
    unbridged : ECert -> Maybe ECert
    unbridged c@(MkECertF Nothing _ _) = Just c
    unbridged _ = Nothing

  spEqStructC : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Maybe ECert
  spEqStructC dep st cs ctx a b Ty.OneTy = Just (MkECert [] FProp)
  spEqStructC dep st cs ctx a b Ty.ZeroTy = Just (MkECert [] FProp)
  spEqStructC dep st cs ctx a b (Ty.PiTy dom cod) =
    if isPiIntro a || isPiIntro b
      then do sub <- spEqElemC dep st (extendCS cs) (ctx :< dom)
                        (betaElem st.sig (PiApp (substElem a Wk) (CtxVar 0)))
                        (betaElem st.sig (PiApp (substElem b Wk) (CtxVar 0)))
                        cod
              pure (MkECert [] (FEtaPi sub))
      else Nothing
   where
    isPiIntro : Elem -> Bool
    isPiIntro (PiIntro _) = True
    isPiIntro _ = False
  spEqStructC dep st cs ctx a b (Ty.SigmaTy dom cod) =
    if isPair a || isPair b
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
    case betaElem st.sig (substElem rel (Ext (Ext Id x) y)) of
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
    -- under ctx ▷ Prf src, a proof of (Prf tgt)[↑]: 𝟙-shaped squashes
    -- outright, equality props by a nested discharge (which may use
    -- the hypothesis as a rewrite candidate)
    mkImpl : Elem -> Elem -> Maybe (Elem, Skel)
    mkImpl src tgt =
      let ctx' = ctx :< Prf src in
      case betaElem st.sig (substElem tgt Wk) of
        Squash sq => case betaTy st.sig sq of
          Ty.OneTy => Just (Star, Nd [PSquashWit OneIntro (Nd [] [])] [])
          _ => Nothing
        Elem.EqTy l r t => do
          c <- spEqElemC dep st (mkCandSet st ctx') ctx' l r t
          Just (Star, Nd [PReflEq c] [])
        _ => Nothing
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
      then case betaTy st.sig <$> inferNe st ctx f of
             Just (Ty.PiTy dom _) =>
               prefixSteps 1 <$> (spEqElemC dep st cs ctx x y dom >>= flatSteps)
             _ => Nothing
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
  spCongC dep st cs ctx (Elem.PiTy a b) (Elem.PiTy a' b') = do
    stA <- spEqElemC dep st cs ctx a a' Ty.UniverseTy >>= flatSteps
    cB <- spEqElemC dep st (extendCS cs) (ctx :< El a') b b' Ty.UniverseTy
    if stepFree cB then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (Elem.SigmaTy a b) (Elem.SigmaTy a' b') = do
    stA <- spEqElemC dep st cs ctx a a' Ty.UniverseTy >>= flatSteps
    cB <- spEqElemC dep st (extendCS cs) (ctx :< El a') b b' Ty.UniverseTy
    if stepFree cB then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (QuotTy a r) (QuotTy a' r') = do
    stA <- spEqElemC dep st cs ctx a a' Ty.UniverseTy >>= flatSteps
    cR <- spEqElemC dep st (extendCS (extendCS cs)) (ctx :< El a' :< substTy (El a') Wk) r r' Ty.PropTy
    if stepFree cR then Just (prefixSteps 0 stA) else Nothing
  spCongC dep st cs ctx (Squash x) (Squash y) =
    prefixSteps 0 <$> (spEqTyC dep st cs ctx x y >>= flatSteps)
  spCongC dep st cs ctx (Elem.EqTy l r t) (Elem.EqTy l' r' t') =
    -- code-eq-cong (sides only; a type-component mismatch routes
    -- through propext instead — steps cannot enter a type child here)
    if betaTy st.sig t == betaTy st.sig t'
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
    firstJ (map direct cs.all) <|> firstJ (map hop cs.hops)
   where
    firstJ : List (Maybe x) -> Maybe x
    firstJ [] = Nothing
    firstJ (Just v :: _) = Just v
    firstJ (Nothing :: rest) = firstJ rest

    noBridge : ECert -> Maybe ECert
    noBridge c@(MkECertF Nothing _ _) = Just c
    noBridge _ = Nothing

    paramTy : Cand -> Nat -> Maybe Ty
    paramTy c p = getAt (minus (minus c.params 1) p) c.paramTys

    hypWitness : Elem -> Elem -> Maybe Elem
    hypWitness lN rN =
      firstJ (map (\i =>
        case betaTy st.sig <$> ctxLookup ctx i of
          Just (Prf p) => case betaElem st.sig p of
            Elem.EqTy hl hr _ =>
              if (betaElem st.sig hl == lN && betaElem st.sig hr == rN)
                then Just (CtxVar i)
                else Nothing
            _ => Nothing
          _ => Nothing) [0 .. minus (length ctx) 1])

    ||| A hypothesis whose (normalized) type is exactly this Prf type.
    hypPrfWitness : Ty -> Maybe Elem
    hypPrfWitness want =
      firstJ (map (\i =>
        case betaTy st.sig <$> ctxLookup ctx i of
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
          case betaTy st.sig (substTy tp sigma) of
            Ty.OneTy => Just OneIntro
            Prf pr =>
              hypPrfWitness (Prf (betaElem st.sig pr))
              <|> (case betaElem st.sig pr of
                     Squash Ty.OneTy => Just Star
                     Elem.EqTy l r _ =>
                       let lN = betaElem st.sig l
                           rN = betaElem st.sig r in
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
    let (a, aSteps) = rwNfTyS st.sig cs.rw True tyA
        (b, bSteps) = rwNfTyS st.sig cs.rw False tyB
        base = aSteps ++ bSteps in
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
      tyN = betaTy st.sig ty in
  any (\(c, x, y, t) => c == ctx && t == tyN && ((x == a' && y == b') || (x == b' && y == a')))
      st.assumedE

-- ===== Committing conversion (the ↓ judgements) =====

||| The number of constraint entries so far. Distinct from oblCount:
||| the decompose bookkeeping must count CONSTRAINTS only — a hole
||| flip during child conversion SHRINKS the open-entry census, and
||| must not read as "children surfaced something".
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
||| Derived from Σ itself: hole flips (decl→def) and item-end
||| constraint deletions must be reflected immediately.
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

mutual
  ||| DISPLAY zonking: unfold references to SOLVED HOLES — their
  ||| entries are elaborator-minted defs — so reported statements and
  ||| hole types read through the run's own inventions (`Prf _3 →
  ||| Prf _4` says nothing; `Prf ⊤ → Prf ⊥` says absurdity), and
  ||| contract EVERY β-redex (λ, projections, eliminators at
  ||| constructors, El-decoding, code-squash-prf): an instantiated
  ||| motive `(λx. P x) zero` reads as `P zero`. DEFINITIONS stay
  ||| folded — δ is the one contraction display never takes, so terms
  ||| keep the user's names.
  zonkElem : ElabSt -> Elem -> Elem
  zonkElem st (SigVar x es) =
    let es' = zonkSubNorm st es in
    if any (\m => m.hname == x) (toList st.holeMeta)
      then case sigLookup x st.sig of
             Just (SigDef _ _ a _) => zonkElem st (substElem a (embed es'))
             _ => SigVar x es'
      else SigVar x es'
  zonkElem st (CtxVar n) = CtxVar n
  zonkElem st (ZeroElim t) = ZeroElim (zonkElem st t)
  zonkElem st OneIntro = OneIntro
  zonkElem st NatIntro0 = NatIntro0
  zonkElem st (NatIntro1 t) = NatIntro1 (zonkElem st t)
  zonkElem st (NatElim z s' t) =
    case zonkElem st t of
      NatIntro0 => zonkElem st z
      NatIntro1 n => zonkElem st (substElem s' (Ext (Ext Id n) (NatElim z s' n)))
      t2 => NatElim (zonkElem st z) (zonkElem st s') t2
  zonkElem st (PiIntro f) = PiIntro (zonkElem st f)
  zonkElem st (PiApp f e) =
    case zonkElem st f of
      PiIntro g => zonkElem st (substElem g (Ext Id e))
      f2 => PiApp f2 (zonkElem st e)
  zonkElem st (SigmaIntro a b) = SigmaIntro (zonkElem st a) (zonkElem st b)
  zonkElem st (SigmaElim1 t) =
    case zonkElem st t of
      SigmaIntro a _ => a
      t2 => SigmaElim1 t2
  zonkElem st (SigmaElim2 t) =
    case zonkElem st t of
      SigmaIntro _ b => b
      t2 => SigmaElim2 t2
  zonkElem st Elem.ZeroTy = Elem.ZeroTy
  zonkElem st Elem.OneTy = Elem.OneTy
  zonkElem st Elem.NatTy = Elem.NatTy
  zonkElem st (Elem.PiTy a b) = Elem.PiTy (zonkElem st a) (zonkElem st b)
  zonkElem st (Elem.SigmaTy a b) = Elem.SigmaTy (zonkElem st a) (zonkElem st b)
  zonkElem st (Elem.EqTy l r t) = Elem.EqTy (zonkElem st l) (zonkElem st r) (zonkTy st t)
  zonkElem st (QuotTy a r) = QuotTy (zonkElem st a) (zonkElem st r)
  zonkElem st (Class a) = Class (zonkElem st a)
  zonkElem st (QuotElim f q) =
    case zonkElem st q of
      Class a => zonkElem st (substElem f (Ext Id a))
      q2 => QuotElim (zonkElem st f) q2
  zonkElem st (Squash t) =
    case zonkTy st t of
      Prf p => p          -- code-squash-prf
      t2 => Squash t2
  zonkElem st Star = Star
  zonkElem st (QSortC sg k es) =
    let z = QSortC (zonkQSig st sg) k (zonkSubNorm st es) in
    fromMaybe z (resugarQ st z)
  zonkElem st (QCtor sg k es) =
    let z = QCtor (zonkQSig st sg) k (zonkSubNorm st es) in
    fromMaybe z (resugarQ st z)
  zonkElem st (QElim sg k ms fs es w) =
    case zonkElem st w of
      QCtor sgW c theta =>
        -- el-qiit-beta at nf-identical signatures
        if zonkQSig st sg == sgW
          then case qElimBetaRhs (zonkQSig st sg) (map (zonkTy st) ms) (map (zonkElem st) fs) c theta of
                 Right rhs => zonkElem st rhs
                 Left _ => zonkElimStuck st sg k ms fs es (QCtor sgW c theta)
          else zonkElimStuck st sg k ms fs es (QCtor sgW c theta)
      w2 => zonkElimStuck st sg k ms fs es w2

  zonkTy : ElabSt -> Ty -> Ty
  zonkTy st (Ty.SigVar x es) =
    let es' = zonkSubNorm st es in
    if any (\m => m.hname == x) (toList st.holeMeta)
      then case sigLookup x st.sig of
             Just (SigTyDef _ _ a) => zonkTy st (substTy a (embed es'))
             _ => Ty.SigVar x es'
      else Ty.SigVar x es'
  zonkTy st Ty.ZeroTy = Ty.ZeroTy
  zonkTy st Ty.OneTy = Ty.OneTy
  zonkTy st Ty.NatTy = Ty.NatTy
  zonkTy st Ty.UniverseTy = Ty.UniverseTy
  zonkTy st (Ty.PiTy a b) = Ty.PiTy (zonkTy st a) (zonkTy st b)
  zonkTy st (Ty.SigmaTy a b) = Ty.SigmaTy (zonkTy st a) (zonkTy st b)
  zonkTy st (El e) =
    case zonkElem st e of
      Elem.ZeroTy      => Ty.ZeroTy
      Elem.OneTy       => Ty.OneTy
      Elem.NatTy       => Ty.NatTy
      Elem.PiTy a b    => Ty.PiTy (zonkTy st (El a)) (zonkTy st (El b))
      Elem.SigmaTy a b => Ty.SigmaTy (zonkTy st (El a)) (zonkTy st (El b))
      QuotTy a r       => Quotient (zonkTy st (El a)) r
      e2 => El e2
  zonkTy st PropTy = PropTy
  zonkTy st (Prf e) = Prf (zonkElem st e)
  zonkTy st (Quotient a r) = Quotient (zonkTy st a) (zonkElem st r)
  zonkTy st (QSort sg k es) =
    let zsg = zonkQSig st sg
        zes = zonkSubNorm st es in
    case resugarQ st (QSortC zsg k zes) of
      Just code => El code
      Nothing => QSort zsg k zes

  zonkElimStuck : ElabSt -> QSig -> Nat -> List Ty -> List Elem -> SubNorm -> Elem -> Elem
  zonkElimStuck st sg k ms fs es w2 =
    let z = QElim (zonkQSig st sg) k (map (zonkTy st) ms) (map (zonkElem st) fs)
                  (zonkSubNorm st es) w2 in
    fromMaybe z (resugarQ st z)

  zonkSubNorm : ElabSt -> SubNorm -> SubNorm
  zonkSubNorm st [<] = [<]
  zonkSubNorm st (es :< e) = zonkSubNorm st es :< zonkElem st e

  zonkQTm : ElabSt -> QTm -> QTm
  zonkQTm st (QVar i) = QVar i
  zonkQTm st (QAppE f e) = QAppE (zonkQTm st f) (zonkElem st e)
  zonkQTm st (QAppI f a) = QAppI (zonkQTm st f) (zonkQTm st a)
  zonkQTm st (QEqC l r u) = QEqC (zonkQTm st l) (zonkQTm st r) (zonkQTm st u)

  zonkQTy : ElabSt -> QTy -> QTy
  zonkQTy st QU = QU
  zonkQTy st (QEl t) = QEl (zonkQTm st t)
  zonkQTy st (QPiExt a b) = QPiExt (zonkTy st a) (zonkQTy st b)
  zonkQTy st (QPiInd u b) = QPiInd (zonkQTm st u) (zonkQTy st b)

  zonkQSig : ElabSt -> QSig -> QSig
  zonkQSig st = map (zonkQTy st)

zonkCtx : ElabSt -> Ctx -> Ctx
zonkCtx st [<] = [<]
zonkCtx st (rest :< ty) = zonkCtx st rest :< zonkTy st ty

zonkStmt : ElabSt -> Stmt -> Stmt
zonkStmt st (StElem ctx env a b ty) =
  StElem (zonkCtx st ctx) env (zonkElem st a) (zonkElem st b) (zonkTy st ty)
zonkStmt st (StTy ctx env a b) =
  StTy (zonkCtx st ctx) env (zonkTy st a) (zonkTy st b)

||| The report view: Σ's constraint entries — the run's obligations,
||| in surfacing order — zipped with their display metadata.
oblView : ElabSt -> List Obligation
oblView st = go (toList st.sig) (toList st.oblMeta)
 where
  go : List SigEntry -> List OblMeta -> List Obligation
  go (SigEq ctx a b ty :: rest) (m :: ms) =
    MkObl (zonkStmt st (StElem ctx m.oenv a b ty)) m.osite (map (zonkStmt st) m.ocomposite) :: go rest ms
  go (SigTyEq ctx x y :: rest) (m :: ms) =
    MkObl (zonkStmt st (StTy ctx m.oenv x y)) m.osite (map (zonkStmt st) m.ocomposite) :: go rest ms
  go (_ :: rest) ms = go rest ms
  go [] _ = []

||| One hole for the report: its Σ-name, context (with binder names),
||| type (Nothing for a type hole) and surfacing site.
record HoleView where
  constructor MkHoleView
  hvname : String
  hvctx : Ctx
  hvenv : NameEnv
  hvty : Maybe Ty
  hvsite : String
  hvrange : Maybe Range

||| The hole report view: Σ's declaration entries zipped with their
||| display metadata, in minting order.
holeView : ElabSt -> List HoleView
holeView st = mapMaybe view (toList st.sig)
 where
  -- matched BY NAME, not positionally: a solved hole's declaration
  -- becomes a definition (its meta goes stale harmlessly), so zip
  -- order is not stable under flips
  metaFor : String -> Maybe HoleMeta
  metaFor x = find (\m => m.hname == x) (toList st.holeMeta)
  view : SigEntry -> Maybe HoleView
  view (SigDecl ctx x ty) = map (\m => MkHoleView x (zonkCtx st ctx) m.henv (Just (zonkTy st ty)) m.hsite m.hrange) (metaFor x)
  view (SigTyDecl ctx x) = map (\m => MkHoleView x (zonkCtx st ctx) m.henv Nothing m.hsite m.hrange) (metaFor x)
  view _ = Nothing

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
          { assumedE $= ((ctx, rwNfElem st ctx a, rwNfElem st ctx b, betaTy st.sig ty) ::)
          , sig $= (:< SigEq ctx a b ty)
          , oblMeta $= (:< MkOblMeta env site comp) } s
    StTy ctx env x y => do
      let x' = rwNfTy st ctx x
          y' = rwNfTy st ctx y
      if any (\(c, u, v) => c == ctx && ((u == x' && v == y') || (u == y' && v == x'))) st.assumedT
        then pure ()
        else modifySt $ \s =>
          { assumedT $= ((ctx, x', y') ::)
          , sig $= (:< SigTyEq ctx x y)
          , oblMeta $= (:< MkOblMeta env site comp) } s
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
  attemptE ctx site a b ty = do
    st <- getSt
    let cs = mkCandSet st ctx
    let mcert = spEqElemC spDepth st cs ctx a b ty
    case map (\cert => (cert, kCheckEqElem st.sig ctx kernelFuel cert a b ty)) mcert of
      Just (cert, Right ()) => pure (Right cert)
      Just (_, Left kerrMsg) => pure (Left (site ++ " [replay failed: " ++ kerrMsg ++ "]"))
      Nothing => pure (Left site)

  attemptT : Ctx -> String -> Ty -> Ty -> ElabM (Either String ECert)
  attemptT ctx site tyA tyB = do
    st <- getSt
    let cs = mkCandSet st ctx
    let mcert = spEqTyC spDepth st cs ctx tyA tyB
    case map (\cert => (cert, kCheckEqTy st.sig ctx kernelFuel cert tyA tyB)) mcert of
      Just (cert, Right ()) => pure (Right cert)
      Just (_, Left kerrMsg) => pure (Left (site ++ " [replay failed: " ++ kerrMsg ++ "]"))
      Nothing => pure (Left site)

  ||| One side is an UNSOLVED SOLVABLE hole at its own context: flip
  ||| its declaration to a definition whose body is the other side —
  ||| the INSTANTIATION refinement, kernel-checked against the PREFIX
  ||| preceding the declaration (a name minted later is absent from
  ||| the prefix, so scope and occurs violations fail the lookup).
  ||| After a flip the reference unfolds by el-sig-beta, so the
  ||| equation that forced it discharges by plain beta on retry.
  ||| Returns True iff a flip happened.
  patternSolveE : Ctx -> NameEnv -> String -> Elem -> Elem -> Ty -> ElabM Bool
  patternSolveE ctx env site a b ty = do
    st <- getSt
    let aN = betaElem st.sig a
    let bN = betaElem st.sig b
    -- beta only ever EXPOSES the hole side; the solution is taken
    -- from the other side AS WRITTEN when the kernel accepts it —
    -- the intended, syntactic filling (beta-normalizing it could
    -- leave the tiny checker's fragment, e.g. unfold a def into a
    -- quot-elim) — falling back to its beta-normal form
    r <- bothHoles st aN bN
    r <- if r then pure True else go st aN b
    r <- if r then pure True else go st aN bN
    r <- if r then pure True else go st bN a
    if r then pure True else go st bN aN
   where
    ||| The candidate body, walked into the prefix by single δ-steps:
    ||| the first spelling the kernel accepts wins (as written when
    ||| possible — the intended, syntactic filling).
    trySolutions : Nat -> Sig -> Elem -> Sig -> Ctx -> Ty -> Maybe Elem
    trySolutions Z full t pre delta dty = Nothing
    trySolutions (S fuel) full t pre delta dty =
      case kCheckSolution pre kernelFuel delta t dty of
        Right () => Just t
        -- unfold against the FULL signature: the offending name is a
        -- LATER def, absent from the prefix by construction
        Left _ => case unfoldHead full t of
                    Just t' => trySolutions fuel full t' pre delta dty
                    Nothing => Nothing

    holeDecl : ElabSt -> Elem -> Maybe (String, Ty)
    holeDecl st (SigVar q es) =
      case sigLookup q st.sig of
        Just (SigDecl delta _ dty) =>
          if delta == ctx && es == idSpine (length ctx)
             && any (\m => m.hname == q && m.hsolvable) (toList st.holeMeta)
            then Just (q, dty)
            else Nothing
        _ => Nothing
    holeDecl _ _ = Nothing
    flipDecl : String -> Elem -> ElabM Bool

    ||| PREFIX-LEGALIZE a candidate solution for the declaration at
    ||| position qPos: a reference to a LATER definition INLINES its
    ||| definiens (indices strictly decrease, so this terminates); a
    ||| reference to a later unsolved SOLVABLE hole at the same
    ||| context is IMITATED — a fresh hole of the same type is
    ||| inserted before the target, the later hole is aliased to it,
    ||| and the reference renamed. This is what closes the
    ||| minted-out-of-order graphs application chains produce
    ||| (impIntro _ _ (constP _ _ …): the outer prop hole's solution
    ||| mentions the inner holes).
    legalize : Nat -> String -> Ctx -> Elem -> ElabM (Maybe Elem)
    legalize Z q ctxQ t = pure Nothing
    legalize (S fuel) q ctxQ t = do
      st <- getSt
      let ls = toList st.sig
      case sigIndexOf q ls of
        Nothing => pure Nothing
        Just qPos => do
          let laters = nub [ n | n <- collectRefsE t
                           , maybe False (> qPos) (sigIndexOf n ls) ]
          if null laters then pure (Just t) else do
            r <- processOne st ls qPos t laters
            case r of
              Nothing => pure Nothing
              Just t' => legalize fuel q ctxQ t'
     where
      processOne : ElabSt -> List SigEntry -> Nat -> Elem -> List String -> ElabM (Maybe Elem)
      processOne st ls qPos t [] = pure (Just t)
      processOne st ls qPos t (n :: _) =
        case sigLookup n st.sig of
          -- a later DEF: inline its definiens at every reference
          Just (SigDef _ _ body _) =>
            pure (Just (mapRefsE (\x, es => if x == n then Just (substElem body (embed es)) else Nothing) t))
          -- a later unsolved SOLVABLE hole at the same context:
          -- imitate with a fresh earlier twin
          Just (SigDecl deltaN _ dtyN) =>
            if not (any (\m => m.hname == n && m.hsolvable) (toList st.holeMeta))
               || deltaN /= ctxQ
               -- the twin's type must itself be prefix-legal
               || not (null [ x | x <- collectRefsE (Squash dtyN)
                            , maybe False (>= qPos) (sigIndexOf x ls) ])
              then pure Nothing
              else do
                let fresh = "_i\{show (length (toList st.holeMeta))}"
                modifySt $ { sig := cast (take qPos ls ++ [SigDecl deltaN fresh dtyN] ++ drop qPos ls)
                           , holeMeta $= (:< MkHoleMeta fresh [<] "legalize" True Nothing) }
                aliased <- flipDecl n (SigVar fresh (idSpine (length deltaN)))
                if aliased
                  then pure (Just (mapRefsE (\x, es => if x == n then Just (SigVar fresh es) else Nothing) t))
                  else pure Nothing
          _ => pure Nothing

    flipDecl q t = do
      st <- getSt
      let ls = toList st.sig
      case sigIndexOf q ls of
        Nothing => pure False
        Just i =>
          case getAt i ls of
            Just (SigDecl delta _ dty) =>
              case trySolutions 8 st.sig t (cast (take i ls)) delta dty of
                Nothing => do
                  mt <- legalize 8 q delta t
                  case mt of
                    Nothing => pure False
                    Just t2 => do
                      st2 <- getSt
                      let ls2 = toList st2.sig
                      case sigIndexOf q ls2 of
                        Nothing => pure False
                        Just i2 =>
                          case getAt i2 ls2 of
                            Just (SigDecl delta2 _ dty2) =>
                              case trySolutions 8 st2.sig t2 (cast (take i2 ls2)) delta2 dty2 of
                                Nothing => pure False
                                Just tOk2 => do
                                  let def2 = SigDef delta2 q tOk2 dty2
                                  modifySt $ { sig := cast (take i2 ls2 ++ [def2] ++ drop (S i2) ls2) }
                                  pure True
                            _ => pure False
                Just tOk => do
                  -- the kernel-Σ mirror happens once, at item end
                  -- (mirrorHoleDefs): mirroring here would be
                  -- order-fragile — the solution may mention a hole
                  -- that is itself solved only later
                  let def = SigDef delta q tOk dty
                  modifySt $ { sig := cast (take i ls ++ [def] ++ drop (S i) ls) }
                  pure True
            _ => pure False

    ||| Peel a variable-applied head: `h ☐_{j₁} … ☐_{jₘ}` gives the
    ||| head and the applied indices in APPLICATION order. Nothing if
    ||| any argument is not a bare context variable.
    peelVars : Elem -> Maybe (Elem, List Nat)
    peelVars (PiApp f (CtxVar i)) = map (mapSnd (++ [i])) (peelVars f)
    peelVars (PiApp _ _) = Nothing
    peelVars e = Just (e, [])

    wrapPis : Nat -> Elem -> Elem
    wrapPis Z e = e
    wrapPis (S n) e = wrapPis n (PiIntro e)

    idxIn : Nat -> List Nat -> Maybe Nat
    idxIn x = go' 0
     where
      go' : Nat -> List Nat -> Maybe Nat
      go' _ [] = Nothing
      go' i (y :: ys) = if x == y then Just i else go' (S i) ys

    ||| Miller-pattern INVERSION: `t` stands at Γ ▷ Δ (|Γ| = n hole
    ||| context, |Δ| = k local binders) and becomes the body of the
    ||| m-ary λ-solution at Γ. The i-th applied local (application
    ||| order) becomes the i-th λ binder; ambient variables shift from
    ||| depth k to depth m; any OTHER local is mapped to an
    ||| out-of-range index — a poison the flip's kernel check refuses,
    ||| which is exactly the non-pattern case (the target genuinely
    ||| uses a binder the hole is not applied to).
    invert : (n : Nat) -> (k : Nat) -> (m : Nat) -> List Nat -> Elem -> Elem
    invert n k m args t =
      let nk = n + k
          spine = cast {to = SubNorm} (map termFor (reverse [0 .. minus nk 1]))
      in substElem t (embed spine)
     where
      termFor : Nat -> Elem
      termFor j =
        case idxIn j args of
          Just i => CtxVar (minus (minus m 1) i)
          Nothing => if j < k
                       then CtxVar (n + m + k + 1)  -- poison: out of range
                       else CtxVar (minus j k + m)

    go : ElabSt -> Elem -> Elem -> ElabM Bool
    go st (SigVar q es) t =
      case sigLookup q st.sig of
        Just (SigDecl delta _ dty) =>
          let n = length delta
              k = minus (length ctx) n in
          if not (any (\m => m.hname == q && m.hsolvable) (toList st.holeMeta))
            then pure False
            else if delta == ctx && es == idSpine (length ctx)
              then flipDecl q t
              -- a WEAKENED occurrence (under k more binders, the
              -- weakened identity spine): the solution moves to the
              -- hole's own context by strengthening — refused if it
              -- mentions any of the k binders
              else if n + k == length ctx && take n (toList ctx) == toList delta
                      && es == wkSpine n k && k /= 0
                then case strengthenK k t of
                       Just t' => flipDecl q t'
                       Nothing => pure False
                else pure False
        _ => pure False
    -- a VARIABLE-APPLIED occurrence (Miller pattern): the hole,
    -- weakened below k binders and applied to distinct LOCAL binders
    -- (`_h[wkⁿ] v w ≐ t`, the shape Π-domain decomposition emits) —
    -- the applied binders become the solution's λs by inversion.
    -- Only strictly-local, pairwise-distinct variable arguments
    -- qualify: an ambient argument is already in the hole's support
    -- (no unique solution), and a repeated one is ambiguous.
    go st e@(PiApp _ _) t =
      case peelVars e of
        Just (SigVar q es, args@(_ :: _)) =>
          case sigLookup q st.sig of
            Just (SigDecl delta _ dty) =>
              let n = length delta
                  k = minus (length ctx) n
                  m = length args in
              if any (\mt => mt.hname == q && mt.hsolvable) (toList st.holeMeta)
                 && n + k == length ctx && take n (toList ctx) == toList delta
                 && es == wkSpine n k
                 && all (< k) args && nub args == args
                then flipDecl q (wrapPis m (invert n k m args t))
                else pure False
            _ => pure False
        _ => pure False
    go st _ _ = pure False

    ||| Both sides are unsolved solvable holes: ALIAS — align the two
    ||| declared types first (their own holes pattern-solve in the
    ||| process), then flip the LATER declaration to a reference to
    ||| the earlier (the prefix direction; the flip's kernel check
    ||| normalizes through the just-solved type holes).
    bothHoles : ElabSt -> Elem -> Elem -> ElabM Bool
    bothHoles st x y =
      case (holeDecl st x, holeDecl st y) of
        (Just (q1, ty1), Just (q2, ty2)) =>
          if q1 == q2 then pure False else do
            ignore $ convTy ctx env site Nothing ty1 ty2
            st' <- getSt
            let ls = toList st'.sig
            case (sigIndexOf q1 ls, sigIndexOf q2 ls) of
              (Just i1, Just i2) =>
                if i1 < i2 then flipDecl q2 x else flipDecl q1 y
              _ => pure False
        _ => pure False

  ||| Type-hole counterpart: a stuck type declaration reference
  ||| equated with a type — flip sig-ty-decl to sig-ty-def.
  patternSolveT : Ctx -> NameEnv -> String -> Ty -> Ty -> ElabM Bool
  patternSolveT ctx env site tyA tyB = do
    st <- getSt
    let aN = betaTy st.sig tyA
    let bN = betaTy st.sig tyB
    -- as-written solution preferred; see patternSolveE
    r <- bothHolesT st aN bN
    r <- if r then pure True else go st aN tyB
    r <- if r then pure True else go st aN bN
    r <- if r then pure True else go st bN tyA
    r <- if r then pure True else go st bN aN
    -- an ELEMENT-code hole under El: `El _c ≐ T` pins _c to T's code
    -- (e-eq's ∈-slot `El _`, say) — taken from the RAW side when it
    -- has one, so the solution stays as written (Bag ℕ, not the
    -- expanded sort former)
    r <- if r then pure True else elHole aN tyB bN
    if r then pure True else elHole bN tyA aN
   where
    elHole : Ty -> Ty -> Ty -> ElabM Bool
    elHole (El e@(SigVar q es)) rawOther betaOther =
      case the (Maybe Elem) (codeOf rawOther <|> codeOf betaOther) of
        Just c => patternSolveE ctx env site e c Ty.UniverseTy
        Nothing => pure False
    elHole _ _ _ = pure False
    holeTyDecl : ElabSt -> Ty -> Maybe String
    holeTyDecl st (Ty.SigVar q es) =
      case sigLookup q st.sig of
        Just (SigTyDecl delta _) =>
          if delta == ctx && es == idSpine (length ctx)
             && any (\m => m.hname == q && m.hsolvable) (toList st.holeMeta)
            then Just q
            else Nothing
        _ => Nothing
    holeTyDecl _ _ = Nothing
    flipTyDecl : String -> Ty -> ElabM Bool
    flipTyDecl q t = do
      st <- getSt
      let ls = toList st.sig
      case sigIndexOf q ls of
        Nothing => pure False
        Just i =>
          case getAt i ls of
            Just (SigTyDecl delta _) =>
              case kCheckTySolution (cast (take i ls)) kernelFuel delta t of
                Left _ => pure False
                Right () => do
                  let def = SigTyDef delta q t
                  modifySt $ { sig := cast (take i ls ++ [def] ++ drop (S i) ls) }
                  pure True
            _ => pure False

    go : ElabSt -> Ty -> Ty -> ElabM Bool
    go st (Ty.SigVar q es) t =
      case sigLookup q st.sig of
        Just (SigTyDecl delta _) =>
          let n = length delta
              k = minus (length ctx) n in
          if not (any (\m => m.hname == q && m.hsolvable) (toList st.holeMeta))
            then pure False
            else if delta == ctx && es == idSpine (length ctx)
              then flipTyDecl q t
              else if n + k == length ctx && take n (toList ctx) == toList delta
                      && es == wkSpine n k && k /= 0
                then case strengthenKTy k t of
                       Just t' => flipTyDecl q t'
                       Nothing => pure False
                else pure False
        _ => pure False
    go st _ _ = pure False

    bothHolesT : ElabSt -> Ty -> Ty -> ElabM Bool
    bothHolesT st x y =
      case (holeTyDecl st x, holeTyDecl st y) of
        (Just q1, Just q2) =>
          if q1 == q2 then pure False else do
            let ls = toList st.sig
            case (sigIndexOf q1 ls, sigIndexOf q2 ls) of
              (Just i1, Just i2) =>
                if i1 < i2 then flipTyDecl q2 x else flipTyDecl q1 y
              _ => pure False
        _ => pure False

  ||| FIRST-ORDER SPINE SOLVING: both sides are application chains
  ||| with syntactically EQUAL heads (after aligning by a few δ-steps
  ||| on either head) — run the pattern solver argwise. Heads are not
  ||| injective (EqN 0 0 ≐ EqN 1 1 both hold), so this is merely
  ||| sufficient and its picks are not unique — the standing contract:
  ||| it runs only after direct discharge failed, every flip is
  ||| kernel-checked against the prefix, and a wrong pick surfaces as
  ||| a precise obligation instead of an opaque composite. Flips only,
  ||| no assumes — safe as an item-end re-solve too.
  spineSolveE : Ctx -> NameEnv -> String -> Elem -> Elem -> ElabM Bool
  spineSolveE ctx env site a b = do
    st <- getSt
    tryPairs (variants st a) (variants st b)
   where
    peel : Elem -> (Elem, List Elem)
    peel (PiApp f e) = let (h, as) = peel f in (h, as ++ [e])
    peel e = (e, [])

    variants : ElabSt -> Elem -> List Elem
    variants st e =
      -- the beta-normal spelling matters when the head is a SOLVED
      -- hole reference: unfoldHead alone leaves the redex unreduced
      -- ((\x.\y. R x y)[..] a b), so its head never aligns with the
      -- other side's
      nub (e :: betaElem st.sig e ::
           (case unfoldHead st.sig e of
              Just e' => e' :: (case unfoldHead st.sig e' of
                                  Just e'' => [e'']
                                  Nothing => [])
              Nothing => []))

    argSolve : List (Elem, Elem) -> ElabM Bool
    argSolve [] = pure False
    argSolve ((x, y) :: rest) = do
      r1 <- patternSolveE ctx env site x y Ty.UniverseTy
      r2 <- argSolve rest
      pure (r1 || r2)

    try1 : Elem -> Elem -> ElabM Bool
    try1 x y =
      let (h1, as1) = peel x
          (h2, as2) = peel y in
      if h1 == h2 && length as1 == length as2 && not (null as1)
        then argSolve (zip as1 as2)
        else pure False

    tryPairs : List Elem -> List Elem -> ElabM Bool
    tryPairs [] _ = pure False
    tryPairs (x :: xs) ys = do
      r <- go1 x ys
      if r then pure True else tryPairs xs ys
     where
      go1 : Elem -> List Elem -> ElabM Bool
      go1 x [] = pure False
      go1 x (y :: ys') = do
        r <- try1 x y
        if r then pure True else go1 x ys'

  ||| CANDIDATE-DIRECTED SOLVING — rewrite-then-unify: one side is an
  ||| instance of a lemma's lhs (or rhs), and the OTHER side then
  ||| unifies with the instantiated rhs (lhs) by hole-flipping. This
  ||| composes the engine's two halves — lemma matching and hole
  ||| solving — and is the only way a size-INCREASING law can pin
  ||| holes: vectS (vect (suc n) a ≡ ∥El a∥ ∧ vect n a) has no
  ||| rewrite orientation, but `vect (suc k) A ≐ _51 ∧ _52` matches
  ||| its lhs and the rhs instance ∥El A∥ ∧ vect k A pins _51/_52
  ||| argwise. Flips only, no assumes; the caller's retry produces
  ||| the actual certificate through the standard path.
  lemmaSolveE : Ctx -> NameEnv -> String -> Elem -> Elem -> ElabM Bool
  lemmaSolveE ctx env site a b = do
    st <- getSt
    let cs = mkCandSet st ctx
    let aN = betaElem st.sig a
    let bN = betaElem st.sig b
    go cs.all aN bN
   where
    or2 : ElabM Bool -> ElabM Bool -> ElabM Bool
    or2 mx my = do
      x <- mx
      y <- my
      pure (x || y)

    mutual
      ||| Structural first-order UNIFICATION, flips only: descend
      ||| through constructors in parallel — extending the context at
      ||| binders, so weakened hole occurrences keep solving — with a
      ||| pattern-solve at hole leaves; stop quietly on mismatch
      ||| (sound either way — the caller's retry decides). The second
      ||| side is the lemma INSTANCE: concrete, so it supplies binder
      ||| types.
      uniE : Ctx -> Elem -> Elem -> ElabM Bool
      uniE uctx x y = do
        st <- getSt
        let xB = betaElem st.sig x
        let yB = betaElem st.sig y
        r <- patternSolveE uctx env site xB yB Ty.UniverseTy
        if r then pure True else do
          r <- spineSolveE uctx env site xB yB
          if r then pure True else
            case (xB, yB) of
              (Squash u, Squash v) => uniT uctx u v
              (Elem.PiTy u c, Elem.PiTy v c') =>
                or2 (uniE uctx u v) (uniE (uctx :< El v) c c')
              (Elem.SigmaTy u c, Elem.SigmaTy v c') =>
                or2 (uniE uctx u v) (uniE (uctx :< El v) c c')
              (Elem.EqTy l r t, Elem.EqTy l' r' t') =>
                or2 (uniT uctx t t') (or2 (uniE uctx l l') (uniE uctx r r'))
              (QuotTy u r1, QuotTy v r2) =>
                or2 (uniE uctx u v) (uniE (uctx :< El v :< substTy (El v) Wk) r1 r2)
              (NatIntro1 u, NatIntro1 v) => uniE uctx u v
              (SigmaIntro u c, SigmaIntro v c') => or2 (uniE uctx u v) (uniE uctx c c')
              (Class u, Class v) => uniE uctx u v
              _ => pure False

      uniT : Ctx -> Ty -> Ty -> ElabM Bool
      uniT uctx x y = do
        st <- getSt
        let xB = betaTy st.sig x
        let yB = betaTy st.sig y
        case (xB, yB) of
          (Prf u, Prf v) => uniE uctx u v
          (El u, El v) => uniE uctx u v
          (Ty.PiTy u c, Ty.PiTy v c') => or2 (uniT uctx u v) (uniT (uctx :< v) c c')
          (Ty.SigmaTy u c, Ty.SigmaTy v c') => or2 (uniT uctx u v) (uniT (uctx :< v) c c')
          (Quotient u r1, Quotient v r2) =>
            or2 (uniT uctx u v) (uniE (uctx :< v :< substTy v Wk) r1 r2)
          (El u, v) => case codeOf v of
                         Just c => uniE uctx u c
                         Nothing => pure False
          (u, El v) => case codeOf u of
                         Just c => uniE uctx c v
                         Nothing => pure False
          _ => pure False

    solveWith : Elem -> Elem -> ElabM Bool
    solveWith inst target = uniE ctx target inst

    tryRhs : Elem -> Elem -> Cand -> ElabM Bool
    tryRhs x y c =
      case matchElemP c.params 0 0 c.rhs x [] >>= instSub c.params 0 of
        Just sigma => solveWith (substElem c.lhs sigma) y
        Nothing => pure False

    tryCand : Elem -> Elem -> Cand -> ElabM Bool
    tryCand x y c =
      case matchElemP c.params 0 0 c.lhs x [] >>= instSub c.params 0 of
        Just sigma => do
          r <- solveWith (substElem c.rhs sigma) y
          if r then pure True else tryRhs x y c
        Nothing => tryRhs x y c

    go : List Cand -> Elem -> Elem -> ElabM Bool
    go [] _ _ = pure False
    go (c :: rest) x y = do
      r <- tryCand x y c
      r <- if r then pure True else tryCand y x c
      if r then pure True else go rest x y

  ||| Γ ⊢ a ≐ b : A ↓ — always succeeds; assumes what it cannot discharge.
  convElem : Ctx -> NameEnv -> String -> Maybe Stmt -> Elem -> Elem -> Ty -> ElabM (Maybe ECert)
  convElem ctx env site comp a b ty = do
    r <- attemptE ctx site a b ty
    case r of
      Right cert => pure (Just cert)
      Left site1 => do
        solved <- patternSolveE ctx env site1 a b ty
        solved <- if solved then pure True else spineSolveE ctx env site1 a b
        solved <- if solved then pure True else lemmaSolveE ctx env site1 a b
        r2 <- the (ElabM (Either String ECert)) $
                if solved then attemptE ctx site1 a b ty else pure (Left site1)
        case r2 of
          Right cert => pure (Just cert)
          Left site2 => do
            st <- getSt
            let cur = StElem ctx env a b ty
            let comp' = comp <|> Just cur
            -- decompose WEAK-HEAD sides first: children then keep the
            -- user's own spellings — full beta would macro-expand
            -- every definition, and hypothesis REWRITING (a → b under
            -- p : a ≡ b) canonicalizes straight through a hole's
            -- spine, masking the solvable pattern. Structure that
            -- only lemma normalization exposes still decomposes: the
            -- final fallback retries with the rewritten sides.
            let aB = whnfE st.sig a
            let bB = whnfE st.sig b
            let a' = rwNfElem st ctx a
            let b' = rwNfElem st ctx b
            let again = if (aB, bB) == (a', b') then Nothing else Just (a', b')
            n0 <- constraintCountM
            decompose site2 cur comp' aB bB again (rwNfTy st ctx ty)
            n1 <- constraintCountM
            if n1 == n0
              then do
                -- children all discharged — or SOLVED a hole, in which
                -- case the composite may now hold by beta: retry once
                -- before assuming it. An assumed composite keeps the
                -- acceptance semantics honest (the site still has no
                -- certificate; the remedy is a lemma that makes it
                -- directly matchable).
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
          -- equation may carry holes in SEVERAL components at once
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
                      case betaTy st'.sig <$> inferNe st' ctx f of
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
      Left site1 => do
        solved <- patternSolveT ctx env site1 tyA tyB
        r2 <- the (ElabM (Either String ECert)) $
                if solved then attemptT ctx site1 tyA tyB else pure (Left site1)
        case r2 of
          Right cert => pure (Just cert)
          Left site2 => do
            st <- getSt
            let cur = StTy ctx env tyA tyB
            let comp' = comp <|> Just cur
            let aB = whnfT st.sig tyA
            let bB = whnfT st.sig tyB
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
  let cs = mkCandSet st ctx in
  map (\c => (tyX, c)) (spEqTyC spDepth st cs ctx ty tyX)

preferPi : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferPi st ctx (Ty.PiTy a b) = Just (a, b, Nothing)
preferPi st ctx ty = case rwNfTy st ctx ty of
                       tyX@(Ty.PiTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                       _ => Nothing

preferSigma : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty, Maybe (Ty, ECert))
preferSigma st ctx (Ty.SigmaTy a b) = Just (a, b, Nothing)
preferSigma st ctx ty = case rwNfTy st ctx ty of
                          tyX@(Ty.SigmaTy a b) => (\e => (a, b, Just e)) <$> exposeCert st ctx ty tyX
                          _ => Nothing

preferQuot : ElabSt -> Ctx -> Ty -> Maybe (Ty, Elem, Maybe (Ty, ECert))
preferQuot st ctx (Ty.Quotient a r) = Just (a, r, Nothing)
preferQuot st ctx ty = case rwNfTy st ctx ty of
                         tyX@(Ty.Quotient a r) => (\e => (a, r, Just e)) <$> exposeCert st ctx ty tyX
                         _ => Nothing

preferPrf : ElabSt -> Ctx -> Ty -> Maybe (Elem, Maybe (Ty, ECert))
preferPrf st ctx (Prf p) = Just (p, Nothing)
preferPrf st ctx ty = case rwNfTy st ctx ty of
                        tyX@(Prf p) => (\e => (p, Just e)) <$> exposeCert st ctx ty tyX
                        _ => Nothing

||| Attach a PExpose payload when exposure happened by normalization.
withExpose : Maybe (Ty, ECert) -> Skel -> Skel
withExpose Nothing sk = sk
withExpose (Just (tyX, c)) sk = addPayload (PExpose tyX c) sk

mutual
  export
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
  elabTy ctx env site (STyQuot a (nx, nxr) (ny, nyr) r) = do
    (a', aSk) <- elabTy ctx env site a
    recordBinder nxr ctx env nx a'
    recordBinder nyr (ctx :< a') (env :< nx) ny (substTy a' Wk)
    (r', rSk) <- checkElem (ctx :< a' :< substTy a' Wk) (env :< nx :< ny) site r Ty.PropTy
    pure (Ty.Quotient a' r', Nd [] [aSk, rSk])
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
  elabTy ctx env site (STyHole mrng solvable x) = do
    -- a TYPE hole: a type declaration entry at the ambient context
    -- (sig-ty-decl); references are stuck (ty-sig-decl). Solvable
    -- type holes are instantiated by type pattern equations
    -- (patternSolveT).
    st <- getSt
    let q0 = the String $ if solvable
               then (case (x, mrng) of
                       ("", Just r) => case r.start of MkPosition ln cl => "_r\{show ln}c\{show cl}"
                       ("", Nothing) => "_\{show (length (toList st.holeMeta))}"
                       _ => "_\{x}")
               else "?\{x}"
    let q = if st.modPrefix == "" then q0 else "\{st.modPrefix}.\{q0}"
    let baseSk = Nd [] (replicate (length ctx) (Nd [] []))
    whenJust mrng (\r => modifySt $ { holeOccs $= (:< (q, r)) })
    let reuseT : Ctx -> ElabM (Ty, Skel)
        reuseT = \delta =>
          let n = length delta
              k = minus (length ctx) n in
          if take n (toList ctx) == toList delta && n + k == length ctx
            then pure (Ty.SigVar q (wkSpine n k), Nd [] (replicate n (Nd [] [])))
            else throw "\{site}: hole \{q0} reused in a context that does not extend its own — use a fresh hole name"
    case sigLookup q st.sig of
      -- repeat occurrence: a reference to the same (possibly solved)
      -- type declaration, at its own context or an extension
      Just (SigTyDecl delta _) => reuseT delta
      Just (SigTyDef delta _ _) => reuseT delta
      Just _ => throw "\{site}: '\{q0}' names a non-type signature entry"
      Nothing => do
        modifySt $ { sig $= (:< SigTyDecl ctx q)
                   , holeMeta $= (:< MkHoleMeta q env site solvable mrng) }
        pure (Ty.SigVar q (idSpine (length ctx)), baseSk)

  export
  inferElem : Ctx -> NameEnv -> String -> SElem -> ElabM (Elem, Ty, Skel)
  inferElem ctx env site (SVar mrng n i) =
    case ctxLookup ctx i of
      Just ty => do
        recordBinder mrng ctx env n ty
        pure (CtxVar i, ty, Nd [] [])
      Nothing => throw "\{site}: variable index out of bounds"
  inferElem ctx env site (SHole _ solvable x) =
    let pre = the String (if solvable then "_" else "?") in
    throw "\{site}: hole \{pre}\{x} in inference position — its type is undetermined here\{structuralHint}"
  inferElem ctx env site (SSig mrng x0) = do
    st <- getSt
    let x = resolveSigName st x0
    case sigLookup x st.sig of
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
  inferElem ctx env site (SSquashElim _ _ _) =
    throw "\{site}: cannot infer the type of squash-elim\{structuralHint}"
  inferElem ctx env site (SEqC l r t) = do
    -- e-eq: the equality PROP — the ambient is a TYPE (large types
    -- included); there is no 𝕌-code for equality
    (t', tSk) <- elabTy ctx env site t
    (l', lSk) <- checkElem ctx env site l t'
    (r', rSk) <- checkElem ctx env site r t'
    pure (Elem.EqTy l' r' t', Ty.PropTy, Nd [] [lSk, rSk, tSk])
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
        -- ⋆ against a SOLVABLE-HOLE-headed prop: pin it to ∥𝟙∥, THE
        -- canonical true proposition. ⋆ forces the prop true, and at
        -- Ω all true props are judgementally EQUAL (code-prop-eq), so
        -- the pick is canonical up to ≐ — a later pinning equation
        -- ∥𝟙∥ ≐ q discharges via the propext synthesis when q is
        -- provable, and surfaces honestly otherwise.
        solvedP <- case betaElem st.sig p of
                     hp@(SigVar _ _) => patternSolveE ctx env site hp (Squash Ty.OneTy) Ty.PropTy
                     _ => pure False
        st <- getSt
        -- el-eq-i / el-squash-i: an equality prop is THE payment rule
        -- (checking ⋆ emits its equation into ↓); a squashed 𝟙 is
        -- witnessed outright. Prefer the prop as written for readable
        -- obligation statements; fall back to its normal form.
        let pN = betaElem st.sig p
        let pUse = case p of
                     Elem.EqTy _ _ _ => p
                     _ => pN
        case pUse of
          Elem.EqTy l r t => do
            c <- convElem ctx env "\{site}: checking ⋆" Nothing l r t
            pure (Star, withExpose exp (Nd [PReflEq (certOr c)] []))
          Squash sq =>
            case betaTy st.sig sq of
              Ty.OneTy => pure (Star, withExpose exp (Nd [PSquashWit OneIntro (Nd [] [])] []))
              _ => throw "\{site}: ⋆ can prove only equality props and 𝟙-shaped squashes automatically (write `⋆ ⟨witness⟩` to supply one directly)"
          _ => throw "\{site}: ⋆ checked against a non-evident proposition\{structuralHint}"
  checkElem ctx env site (SStarWit w) ty = do
    st <- getSt
    -- ⋆ w against a solvable-hole-headed prop: the witness's inferred
    -- type pins it — the hole becomes ∥A∥ for w : A
    case preferPrf st ctx ty of
      Just (hp@(SigVar _ _), _) => do
        st <- getSt
        case betaElem st.sig hp of
          SigVar _ _ => do
            (w', wTy, wSk) <- inferElem ctx env site w
            solved <- patternSolveE ctx env site hp (Squash wTy) Ty.PropTy
            if solved
              then pure (Star, Nd [PSquashWit w' wSk] [])
              else checkStarWitAt ctx env site w ty
          _ => checkStarWitAt ctx env site w ty
      _ => checkStarWitAt ctx env site w ty
   where
    checkStarWitAt : Ctx -> NameEnv -> String -> SElem -> Ty -> ElabM (Elem, Skel)
    checkStarWitAt ctx env site w ty = do
    st <- getSt
    case preferPrf st ctx ty of
      Nothing => throw "\{site}: ⋆ checked against a non-Prf type\{structuralHint}"
      Just (p, exp) =>
        -- el-squash-i, general form: w proves the squashee directly,
        -- whatever its shape. At an equality prop, any proof will do
        -- (el-prf-prop): w becomes a proof license for the equation.
        case betaElem st.sig p of
          Squash sq => do
            (w', wSk) <- checkElem ctx env site w sq
            pure (Star, withExpose exp (Nd [PSquashWit w' wSk] []))
          pN@(Elem.EqTy _ _ _) => do
            (w', _) <- checkElem ctx env site w (Prf pN)
            let cert = MkECert [MkStep True [] (LProof w') [] False] FBeta
            pure (Star, withExpose exp (Nd [PReflEq cert] []))
          _ => throw "\{site}: ⋆ checked against Prf of a non-∥∥ code\{structuralHint}"
  checkElem ctx env site (SSquashElim e xn body) ty = do
    st <- getSt
    (e', eTy, eSk) <- inferElem ctx env site e
    case preferPrf st ctx eTy of
      Nothing => throw "\{site}: squash-elim scrutinee has non-Prf type\{structuralHint}"
      Just (p, _) =>
        case betaElem st.sig p of
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
  checkElem ctx env site (SHole mrng solvable x) ty = do
    -- a hole: a declaration entry at the AMBIENT context (sig-decl);
    -- the reference carries the identity spine and is stuck
    -- (el-sig-decl). A rigid `?x` is reported and never solved; a
    -- solvable `_x`/`_` may be instantiated by pattern equations
    -- (the decl→def flip in patternSolveE). Either blocks acceptance
    -- while it remains a declaration.
    st <- getSt
    -- anonymous holes are named by POSITION, not by a mint counter:
    -- the internal rerun must find the previous pass's solved twin
    -- under the same name
    let q0 = the String $ if solvable
               then (case (x, mrng) of
                       ("", Just r) => case r.start of MkPosition ln cl => "_r\{show ln}c\{show cl}"
                       ("", Nothing) => "_\{show (length (toList st.holeMeta))}"
                       _ => "_\{x}")
               else "?\{x}"
    let q = if st.modPrefix == "" then q0 else "\{st.modPrefix}.\{q0}"
    let baseSk = Nd [] (replicate (length ctx) (Nd [] []))
    -- a REPEAT occurrence is a reference to the same entry — the
    -- still-open declaration, or the definition a solve flipped it
    -- to. Valid at the entry's own context or any binder EXTENSION of
    -- it (the weakened identity spine); the occurrence's expected
    -- type converts against the (weakened) declared one — a switch,
    -- like any reference.
    whenJust mrng (\r => modifySt $ { holeOccs $= (:< (q, r)) })
    let reuse : Ctx -> Ty -> ElabM (Elem, Skel)
        reuse = \delta, dty =>
          let n = length delta
              k = minus (length ctx) n in
          if take n (toList ctx) == toList delta && n + k == length ctx
            then do
              let es = wkSpine n k
              let dtyW = substTy dty (embed es)
              c <- convTy ctx env "\{site}: hole \{q0} reused at a different type" Nothing dtyW ty
              pure (SigVar q es, addPayload (PSwitch (certOr c)) (Nd [] (replicate n (Nd [] []))))
            else throw "\{site}: hole \{q0} reused in a context that does not extend its own — use a fresh hole name"
    case sigLookup q st.sig of
      Just (SigDecl delta _ dty) => reuse delta dty
      Just (SigDef delta _ _ dty) => reuse delta dty
      Just _ => throw "\{site}: '\{q0}' names a non-element signature entry"
      Nothing => do
        modifySt $ { sig $= (:< SigDecl ctx q ty)
                   , holeMeta $= (:< MkHoleMeta q env site solvable mrng) }
        pure (SigVar q (idSpine (length ctx)), baseSk)
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
  let (delta', peeled) = peelPis delta (betaTy st.sig ty)
  -- equality is Ω-valued: a lemma registers when its peeled type is a
  -- Prf whose prop normalizes to an equality (squashed spellings
  -- converge here by code-squash-prf)
  let meq : Maybe (Elem, Elem, Ty) =
        case peeled of
          Prf p => case betaElem st.sig p of
                     Elem.EqTy l r t => Just (l, r, t)
                     _ => Nothing
          _ => Nothing
  case meq of
    Just (l, r, t) =>
      -- Sides normalized against the store as of this point (recording
      -- the normalization so the kernel can bridge from the raw
      -- reflected equation); closed under component decomposition.
      let lemmaRw = ordered st.lemmas
          k = length delta'
          teleLen = length delta
          peeledN = minus k teleLen
          mk : Bindings -> Maybe (Elem, List Sel)
          mk = \bs => do
            teleArgs <- traverse (\p => lookup p bs)
                          (the (List Nat) (if teleLen == 0 then [] else reverse [peeledN .. minus k 1]))
            peeledArgs <- traverse (\p => lookup p bs)
                            (the (List Nat) (if peeledN == 0 then [] else reverse [0 .. minus peeledN 1]))
            pure (foldl PiApp (SigVar name (cast teleArgs)) peeledArgs, the (List Sel) [])
          lRes = rwNfElemS st.sig lemmaRw True (betaElem st.sig l)
          rRes = rwNfElemS st.sig lemmaRw True (betaElem st.sig r)
          toP : List Step -> List PStep
          toP = map (\s => MkPStep s.path (licProof s.lic) s.sels s.flip)
      in modifySt $ { lemmas $= (closeCand (MkCand name k (toList delta') (fst lRes) (fst rRes)
                                                   mk (toP (snd lRes)) (toP (snd rRes))) ++) }
    _ => pure ()

||| Item-end constraint deletion (docs/NovaFoundation.txt, DISCHARGE):
||| a hole instantiated mid-item unfolds from then on, which can make
||| an earlier-assumed constraint OF THE SAME ITEM derivable by plain
||| beta. Each such constraint is re-attempted against ITS OWN PREFIX
||| with the exact certificate its site already embeds (the bare
||| compare-beta-normal-forms dummy) — so deletion never claims more
||| than the kernel replay of the item will deliver — and deleted on
||| success, with its display metadata (kept positionally aligned).
||| `keep` is the constraint count at ITEM START: constraints of
||| EARLIER items are never deleted — their items' kernel admission
||| was already decided, and deleting their record would let a run
||| end "definitional" with a skipped item inside it.
resolveConstraints : Nat -> ElabM ()
resolveConstraints keep = do
  sweep 4
  st <- getSt
  let (sig', meta') = go 0 [<] (toList st.sig) (toList st.oblMeta)
  modifySt $ { sig := sig', oblMeta := cast meta' }
 where
  ||| RE-SOLVE before deleting: an equation assumed mid-item may have
  ||| become solvable — a later argument pinned the hole it could not
  ||| legally define (the 3rd-arg/4th-arg ordering of an iffIntro
  ||| application), or a spine head became δ-alignable after a flip.
  ||| Flips only (no assumes); iterate while progress.
  stmts : ElabSt -> List (Nat, SigEntry, OblMeta)
  stmts st = go2 0 (toList st.sig) (toList st.oblMeta)
   where
    go2 : Nat -> List SigEntry -> List OblMeta -> List (Nat, SigEntry, OblMeta)
    go2 k (e@(SigEq _ _ _ _) :: rest) (m :: ms) = (k, e, m) :: go2 (S k) rest ms
    go2 k (e@(SigTyEq _ _ _) :: rest) (m :: ms) = (k, e, m) :: go2 (S k) rest ms
    go2 k (_ :: rest) ms = go2 k rest ms
    go2 _ [] _ = []

  solveOne : (Nat, SigEntry, OblMeta) -> ElabM Bool
  solveOne (k, SigEq ctx a b ty, m) =
    if k < keep then pure False else do
      r1 <- patternSolveE ctx m.oenv m.osite a b ty
      r2 <- spineSolveE ctx m.oenv m.osite a b
      r3 <- lemmaSolveE ctx m.oenv m.osite a b
      pure (r1 || r2 || r3)
  solveOne (k, SigTyEq ctx x y, m) =
    if k < keep then pure False else patternSolveT ctx m.oenv m.osite x y
  solveOne _ = pure False

  sweep : Nat -> ElabM ()
  sweep Z = pure ()
  sweep (S fuel) = do
    st <- getSt
    rs <- traverse solveOne (stmts st)
    when (any id rs) (sweep fuel)
  go : Nat -> Sig -> List SigEntry -> List OblMeta -> (Sig, List OblMeta)
  go k acc [] ms = (acc, [])
  go k acc (e@(SigEq ctx a b ty) :: rest) (m :: ms) =
    if k >= keep && kCheckEqElem acc ctx kernelFuel (MkECert [] FBeta) a b ty == Right ()
      then go (S k) acc rest ms
      else let (s', ms') = go (S k) (acc :< e) rest ms in (s', m :: ms')
  go k acc (e@(SigTyEq ctx x y) :: rest) (m :: ms) =
    if k >= keep && kCheckEqTy acc ctx kernelFuel (MkECert [] FBeta) x y == Right ()
      then go (S k) acc rest ms
      else let (s', ms') = go (S k) (acc :< e) rest ms in (s', m :: ms')
  go k acc (e :: rest) ms =
    let (s', ms') = go k (acc :< e) rest ms in (s', ms')

||| The number of constraint entries so far (the resolveConstraints
||| marker).
constraintCount : ElabM Nat
constraintCount = do
  st <- getSt
  pure (length (toList st.oblMeta))

||| Mirror solved holes into the kernel's Σ — ONCE, at item end, in
||| minting order (each solution is prefix-legal, so earlier mirrors
||| carry later ones). Eager per-flip mirroring is order-fragile: a
||| solution may mention a hole that is itself solved only later in
||| the same item. A mirror that still fails (the solution mentions a
||| dirty-run entry) is skipped — the run is dirty in that case and
||| the kernel copy is never consulted.
mirrorHoleDefs : ElabM ()
mirrorHoleDefs = do
  st <- getSt
  -- Σ ORDER, not minting order: legalize inserts imitation twins
  -- BEFORE the holes whose solutions reference them, so walking the
  -- signature mirrors each body after its dependencies
  let holeNames = map hname (toList st.holeMeta)
  let entries = [ e | e <- toList st.sig
                , maybe False (`elem` holeNames) (sigEntryName e) ]
  modifySt $ { kernelSig := go entries st.kernelSig }
 where
  go : List SigEntry -> Sig -> Sig
  go [] ks = ks
  go (e :: rest) ks =
    case sigEntryName e of
      Nothing => go rest ks
      Just q =>
        case sigLookup q ks of
          Just _ => go rest ks
          Nothing =>
            case e of
              SigDef delta _ t dty =>
                if kCheckSolution ks kernelFuel delta t dty == Right ()
                  then go rest (ks :< e)
                  else go rest ks
              SigTyDef delta _ t =>
                if kCheckTySolution ks kernelFuel delta t == Right ()
                  then go rest (ks :< e)
                  else go rest ks
              _ => go rest ks

||| Kernel-check a clean item against the kernel's own Σ; extend it on
||| acceptance. Items elaborated under assumptions (dirty) are skipped —
||| they cannot be accepted anyway.
kernelAccept : String -> (Sig -> Either KErr SigEntry) -> Bool -> ElabM ()
kernelAccept name check clean = do
  st <- getSt
  if not clean
    then pure ()
    else case check st.kernelSig of
      Right entry => modifySt $ { kernelSig $= (:< entry) }
      Left err => throw "\{name}: KERNEL REJECTED the elaborated item: \{err}"

liftQE : String -> Either QErr a -> ElabM a
liftQE site (Left e) = throw "\{site}: \{e}"
liftQE site (Right x) = pure x

||| Emit one core definition item: kernel-check, extend Σ, register a
||| lemma if it is ≡-typed. Mirrors elabItem's tail for surface defs.
emitCoreDef : String -> String -> Ty -> Skel -> Elem -> Skel -> ElabM ()
emitCoreDef site x ty tySk body bodySk = do
  oblsAtStart <- constraintCount
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "\{site}: duplicate signature name '\{x}'"
    Nothing => pure ()
  resolveConstraints oblsAtStart
  mirrorHoleDefs
  after <- oblCount
  kernelAccept "\{site} \{x}"
    (\ksig => kCheckDefItem ksig kernelFuel (MkKDefArt q [] ty tySk body bodySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q body ty), vis $= (:< (x, q)) }
  addLemma q [<] ty

emitCoreTyDef : String -> String -> Ty -> Skel -> ElabM ()
emitCoreTyDef site x ty tySk = do
  oblsAtStart <- constraintCount
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "\{site}: duplicate signature name '\{x}'"
    Nothing => pure ()
  resolveConstraints oblsAtStart
  mirrorHoleDefs
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
  pure (length (oblView st), length (holeView st))

||| The per-item echo suffix: what this item left OPEN — the ⋆-payment
||| and hole assumptions a reader would otherwise only discover in the
||| end-of-run report. "defined boom [+1 hole]" is an honest receipt;
||| a bare "defined boom" for an item that just assumed ¬⊤'s realizer
||| reads like success.
opensSuffix : (before : (Nat, Nat)) -> ElabM String
opensSuffix (ob, hb) = do
  (o', h') <- openCensus
  let o = minus o' ob
  let h = minus h' hb
  let parts = the (List String)
                ((if o == 0 then [] else ["+\{show o} obligation\{plural o}"]) ++
                 (if h == 0 then [] else ["+\{show h} hole\{plural h}"]))
  pure (case parts of
          [] => ""
          _ => " [" ++ joinBy ", " parts ++ "]")
 where
  plural : Nat -> String
  plural 1 = ""
  plural _ = "s"

||| One-shot elaboration of an item (the body of elabItem below).
elabItemGo : SItem -> ElabM String

||| Elaborate an item; if the ITEM-END sweep solved holes that were
||| still declarations when their use sites were checked (minted out
||| of order, pinned late — a lemma-directed solve at the last
||| moment), the sites carry dummy certificates that can never be
||| repaired in place. The INTERNAL RERUN closes the loop: reset to
||| the pre-item state, KEEP the solved holes as definitions, and
||| elaborate the item once more — each hole occurrence now hits the
||| reuse path as a reference to a solved def, every conversion sees
||| concrete values, and the sites get real certificates.
export
elabItem : SItem -> ElabM String
elabItem item = do
  pre <- getSt
  echo <- elabItemGo item
  st <- getSt
  after <- oblCount
  let preHoles = length (toList pre.holeMeta)
  let newHoles = drop preHoles (toList st.holeMeta)
  let newNames = map hname newHoles
  let newEntries = [ e | e <- toList st.sig
                   , maybe False (`elem` newNames) (sigEntryName e) ]
  -- the carried set is the item's SOLVED holes plus the reference
  -- CLOSURE of their solutions among the item's other new entries: a
  -- solution may mention a twin that never got a value of its own
  -- (legalize's inserted imitations), and dropping the twin decl
  -- would leave a dangling name and crash the rerun's normalizer.
  -- Nothing else travels — in particular an item's own declaration
  -- entry (a `def x : T` declaration IS a hole) must be re-minted by
  -- the rerun, not carried into a duplicate-name error. Σ order is
  -- preserved, keeping every carried body's prefix intact.
  let solvedNames = mapMaybe sigEntryName (filter sigEntryIsDef newEntries)
  let keepNames = closeRefs newEntries (length newEntries) solvedNames solvedNames
  let keepEntries = [ e | e <- newEntries
                    , maybe False (`elem` keepNames) (sigEntryName e) ]
  let keepMetas = [ m | m <- newHoles, m.hname `elem` keepNames ]
  preOpen <- pure (length (filter (not . sigEntryIsDef) (toList pre.sig)))
  if after == preOpen || null solvedNames
    then pure echo
    else do
      putSt ({ sig := pre.sig <>< keepEntries
             , holeMeta := pre.holeMeta <>< keepMetas } pre)
      elabItemGo item
 where
  ||| Every Σ-name an entry's context, type, and body reference (Ty
  ||| pieces go through Squash to reuse the Elem collector).
  entryRefs : SigEntry -> List String
  entryRefs (SigDef delta _ t dty) =
    concatMap (collectRefsE . Squash) (toList delta) ++ collectRefsE (Squash dty) ++ collectRefsE t
  entryRefs (SigTyDef delta _ t) =
    concatMap (collectRefsE . Squash) (toList delta) ++ collectRefsE (Squash t)
  entryRefs (SigDecl delta _ dty) =
    concatMap (collectRefsE . Squash) (toList delta) ++ collectRefsE (Squash dty)
  entryRefs _ = []

  ||| Fixpoint of `entryRefs` over `pool`, seeded by `frontier`; the
  ||| fuel (|pool| suffices — each round adds at least one pool name)
  ||| is only there for totality.
  closeRefs : List SigEntry -> Nat -> List String -> List String -> List String
  closeRefs pool Z acc _ = acc
  closeRefs pool (S fuel) acc frontier =
    let step = nub [ n | e <- pool
                   , maybe False (`elem` frontier) (sigEntryName e)
                   , n <- entryRefs e
                   , any (\e' => sigEntryName e' == Just n) pool
                   , not (n `elem` acc) ]
    in if null step then acc else closeRefs pool fuel (acc ++ step) step

elabItemGo (SDef x ty body) = do
  oblsAtStart <- constraintCount
  census <- openCensus
  st <- getSt
  -- the Σ-name is qualified by the module; the root file's entries
  -- stay bare
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "def \{x}: duplicate signature name"
    Nothing => pure ()
  -- items live in the EMPTY context: parameters are Π-binders in the
  -- item's type, references are bare names
  (ty', tySk) <- elabTy [<] [<] "def \{x}" ty
  (body', bodySk) <- checkElem [<] [<] "def \{x}" body ty'
  -- clean means the RUN is clean: an earlier item's assumption poisons
  -- everything after it (the kernel Σ cannot contain the earlier item,
  -- so references to it are unresolvable anyway)
  resolveConstraints oblsAtStart
  mirrorHoleDefs
  after <- oblCount
  kernelAccept "def \{x}"
    (\ksig => kCheckDefItem ksig kernelFuel (MkKDefArt q [] ty' tySk body' bodySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q body' ty'), vis $= (:< (x, q)) }
  addLemma q [<] ty'
  suffix <- opensSuffix census
  pure "defined \{x}\{suffix}"
elabItemGo (SDeclDef nrng x ty) = do
  -- a DECLARATION (docs/NovaFoundation.txt, sig-decl at ε): exactly a
  -- rigid hole with a user-facing name — same Σ entry, same report,
  -- same acceptance wall; references type by el-sig-decl and are
  -- stuck. The remedy is supplying the definiens (or importing a
  -- module that will, once such a mechanism exists).
  census <- openCensus
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "def \{x}: duplicate signature name"
    Nothing => pure ()
  (ty', tySk) <- elabTy [<] [<] "def \{x}" ty
  modifySt $ { sig $= (:< SigDecl [<] q ty')
             , holeMeta $= (:< MkHoleMeta q [<] "def \{x}" False nrng)
             , vis $= (:< (x, q)) }
  -- a DECLARED equation is a lemma like any accepted one: its stuck
  -- reference is a proof element (el-sig-decl), so el-reflect makes
  -- the equation judgementally available — that is what an abstract
  -- interface's equational axioms are FOR
  addLemma q [<] ty'
  suffix <- opensSuffix census
  pure "declared \{x}\{suffix}"
elabItemGo (STypeDef x ty) = do
  oblsAtStart <- constraintCount
  census <- openCensus
  st <- getSt
  let q = if st.modPrefix == "" then x else "\{st.modPrefix}.\{x}"
  case sigLookup q st.sig of
    Just _ => throw "type \{x}: duplicate signature name"
    Nothing => pure ()
  (ty', tySk) <- elabTy [<] [<] "type \{x}" ty
  resolveConstraints oblsAtStart
  mirrorHoleDefs
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
     Just c => "\n      from composite: \{prettyStmt tbl c}")

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

||| Render one hole for the report (exported for LSP consumers, like
||| prettyObligation).
export
prettyHole : FixTable -> HoleView -> String
prettyHole tbl h =
  let tele = prettyTelescope tbl h.hvctx h.hvenv in
  "  [\{h.hvname}] " ++ (if tele == "" then "" else tele ++ " ") ++
  (case h.hvty of
     Just ty => "⊢ ? : \{prettyTyN tbl h.hvenv ty}"
     Nothing => "⊢ ? type") ++
  "\n      at: \{h.hvsite}"

holeReport : FixTable -> List HoleView -> String
holeReport tbl hs =
  "open holes (\{show (length hs)}):\n" ++
  joinBy "\n" (map (prettyHole tbl) hs)

||| The composed end-of-run report of everything keeping Σ
||| non-definitional; empty exactly when the run is accepted.
openReport : FixTable -> ElabSt -> Maybe String
openReport tbl st =
  case (oblView st, holeView st) of
    ([], []) => Nothing
    (os, hs) => Just $ joinBy "\n"
      ((case os of [] => []; _ => [oblReport tbl os]) ++
       (case hs of [] => []; _ => [holeReport tbl hs]))

||| Install a module's import aliases: each opened name must exist in
||| the imported module's Σ segment.
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
    -- a fresh visibility table per module: its own imports only
    let st = { modPrefix := name, vis := [<] } st
    case runElabM (installImports imps) st of
      Left err => joinBy "\n" (echoes ++ ["Error: \{err}"])
      Right (st, ()) =>
        let hdr = if name == "" then [] else ["module \{name}:"] in
        case goItems st items of
          Left (itemEchoes, err) => joinBy "\n" (echoes ++ hdr ++ itemEchoes ++ ["Error: \{err}"])
          Right (st', itemEchoes) =>
            case rest of
              [] => finish tbl st' (echoes ++ hdr ++ itemEchoes)
              _ =>
                -- only ACCEPTED modules are importable: a module's
                -- signature segment must be DEFINITIONAL
                case openReport tbl st' of
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
    let st = { modPrefix := name, vis := [<] } st in
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
||| One hole of the ROOT module, for LSP consumers: every occurrence's
||| span, and the rendered judgement — the hole's context and type
||| while open, its solution once solved. All display strings are
||| zonked (solved holes unfolded).
public export
record HoleInfo where
  constructor MkHoleInfo
  hiName : String
  hiSolvable : Bool
  ||| Nothing while open; Just (rendered solution) once solved
  hiSolution : Maybe String
  ||| the rendered judgement: `(ctx) ⊢ ? : T`, or `(ctx) ⊢ x ≔ t : T`
  hiText : String
  ||| the minting occurrence first, then reuse occurrences
  hiOccs : List Range

||| The LSP hole table: one row per hole of the ROOT module (module
||| prefix "" — hole names of imported modules are dot-qualified),
||| solved and open alike, in minting order.
holeInfos : FixTable -> ElabSt -> List HoleInfo
holeInfos tbl st = mapMaybe row (toList st.holeMeta)
 where
  occsOf : String -> List Range
  occsOf q = [r | (n, r) <- toList st.holeOccs, n == q]

  judge : NameEnv -> Ctx -> String -> String
  judge env ctx rhs =
    let tele = prettyTelescope tbl ctx env in
    (if tele == "" then "" else tele ++ " ") ++ "⊢ " ++ rhs

  row : HoleMeta -> Maybe HoleInfo
  row m =
    if isInfixOf "." m.hname then Nothing else
    case sigLookup m.hname st.sig of
      Just (SigDecl ctx _ ty) => Just $ MkHoleInfo m.hname m.hsolvable Nothing
        (judge m.henv (zonkCtx st ctx) "? : \{prettyTyN tbl m.henv (zonkTy st ty)}")
        (occsOf m.hname)
      Just (SigTyDecl ctx _) => Just $ MkHoleInfo m.hname m.hsolvable Nothing
        (judge m.henv (zonkCtx st ctx) "? type")
        (occsOf m.hname)
      Just (SigDef ctx _ t ty) =>
        let sol = prettyElemN tbl m.henv (zonkElem st t) in
        Just $ MkHoleInfo m.hname m.hsolvable (Just sol)
          (judge m.henv (zonkCtx st ctx) "\{m.hname} ≔ \{sol} : \{prettyTyN tbl m.henv (zonkTy st ty)}")
          (occsOf m.hname)
      Just (SigTyDef ctx _ ty) =>
        let sol = prettyTyN tbl m.henv (zonkTy st ty) in
        Just $ MkHoleInfo m.hname m.hsolvable (Just sol)
          (judge m.henv (zonkCtx st ctx) "\{m.hname} ≔ \{sol} type")
          (occsOf m.hname)
      _ => Nothing

||| The LSP binder table: the ROOT module's binder occurrences,
||| rendered zonked.
binderInfos : FixTable -> ElabSt -> List (Range, String)
binderInfos tbl st =
  [ (r, "\{x} : \{prettyTyN tbl env (zonkTy st ty)}")
  | (m, r, ctx, env, x, ty) <- toList st.binderTypes, m == "" ]

public export
record ElabReport where
  constructor MkElabReport
  obligations : List (String, Maybe Range, Obligation)
  ||| open holes, pre-rendered (module, range, report text) — the
  ||| range is the hole token's own when the parser recorded one,
  ||| the enclosing item's otherwise
  holes : List (String, Maybe Range, String)
  ||| the LSP hole table: the ROOT module's holes, solved and open
  ||| alike (hover, inlay hints)
  holeTable : List HoleInfo
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
  -- newly-appended obligations/holes since `before`: both only ever
  -- grow by `:<` (see `assume` and the hole minting sites), so
  -- `before` is always a prefix of `after`.
  newObls : (before, after : ElabSt) -> List Obligation
  newObls before after =
    drop (length (toList before.oblMeta)) (oblView after)

  newHoles : (before, after : ElabSt) -> List HoleView
  newHoles before after =
    drop (length (toList before.holeMeta)) (holeView after)

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
            -- a hole diagnostic lands on the hole TOKEN when the
            -- parser recorded its span, on the item otherwise
            taggedH = map (\h => (mname, h.hvrange <|> rng, prettyHole tbl h)) (newHoles st st') in
        case goItems tbl mname st' rest of
          Left ((obls, hs), r, err) => Left ((tagged ++ obls, taggedH ++ hs), r, err)
          Right (st'', (obls, hs)) => Right (st'', (tagged ++ obls, taggedH ++ hs))

  go : ElabSt -> List ModUnit -> List (String, Maybe Range, Obligation) -> List (String, Maybe Range, String) -> List (String, Maybe Range, String) -> ElabReport
  go st [] obls hs errs = MkElabReport obls hs [] [] errs
  go st (MkModUnit name imps tbl items _ :: rest) obls hs errs =
    let st = { modPrefix := name, vis := [<] } st in
    case runElabM (installImports imps) st of
      Left err => MkElabReport obls hs (holeInfos tbl st) (binderInfos tbl st) (errs ++ [(name, Nothing, err)])
      Right (st, ()) =>
        case goItems tbl name st items of
          Left ((itemObls, itemHs), rng, err) => MkElabReport (obls ++ itemObls) (hs ++ itemHs) [] [] (errs ++ [(name, rng, err)])
          Right (st', (itemObls, itemHs)) =>
            case rest of
              [] => MkElabReport (obls ++ itemObls) (hs ++ itemHs) (holeInfos tbl st') (binderInfos tbl st') errs
              _ =>
                -- only ACCEPTED modules are importable: a module's
                -- signature segment must be DEFINITIONAL
                case (oblView st', holeView st') of
                  ([], []) => go st' rest (obls ++ itemObls) (hs ++ itemHs) errs
                  _ => MkElabReport (obls ++ itemObls) (hs ++ itemHs) (holeInfos tbl st') (binderInfos tbl st')
                         (errs ++ [(name, Nothing, "module \{name} has open obligations and cannot be imported")])
