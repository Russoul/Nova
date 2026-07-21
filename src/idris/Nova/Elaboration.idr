module Nova.Elaboration

-- The bidirectional elaborator of docs/NovaElaboration.txt (hole-free).
--
-- Independent of the derivation machinery (no Truth, no TypingRule): it
-- shares only the core syntax, substitution, and beta-normalization.
-- Every rule mirrors a docs/NovaFoundation.txt rule; the conversion
-- judgements never fail — an equation that cannot be discharged
-- algorithmically is ASSUMED and reported as an obligation. A file is
-- accepted exactly when a run ends with zero obligations.
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
import Nova.Kernel.Parser
import Nova.Kernel
import Nova.Elaboration.Named
import Nova.Elaboration.Surface
import Nova.Elaboration.Parser

%default covering

-- ===== State =====

||| A rewrite candidate: an equation whose context splits into a fixed
||| base (rigid — the ambient Γ for hypothesis candidates, ε for Σ-level
||| lemmas) and `params` innermost parametric entries (matchable).
||| lhs/rhs are stored beta-normalized, in base ᐅ p_{k-1} ᐅ ... ᐅ p₀.
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

record ElabSt where
  constructor MkElabSt
  sig : Sig
  ||| the KERNEL's signature: extended only by kernel-accepted items —
  ||| the authoritative Σ (docs/NovaPipeline.txt)
  kernelSig : Sig
  lemmas : List Cand
  assumedE : List (Ctx, Elem, Elem, Ty)   -- normalized keys of assumed elem equations
  assumedT : List (Ctx, Ty, Ty)           -- normalized keys of assumed type equations
  obls : SnocList Obligation
  ||| dotted name of the module being elaborated; "" = the root file,
  ||| whose entries stay unqualified
  modPrefix : String
  ||| surface-name → Σ-name aliases: the module's own entries plus the
  ||| opened names of its imports (last entry wins; locals were already
  ||| resolved by the parser and never reach this table)
  vis : SnocList (String, String)

initSt : ElabSt
initSt = MkElabSt [<] [<] [] [] [] [<] "" [<]

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

throw : Err -> ElabM a
throw e = MkElabM $ \_ => Left e

-- ===== Small core utilities =====

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
-- Pattern lives in base ᐅ p_{k-1} ᐅ ... ᐅ p₀; the match site sits at
-- depth `d` below the ambient context Γ (= the candidate's base for
-- hypotheses; lemmas have base ε so any Γ works). Inside the pattern we
-- track the local binder depth `b`. Pattern variable j:
--   * j < b            — pattern-local: target must be ☐_j;
--   * b ≤ j < b + k    — parametric: bind p_{j-b}; the bound term is
--                        canonicalized to Γ by strengthening away the
--                        d + b local variables (fail = would capture);
--   * j ≥ b + k        — base-rigid: target must be ☐_{j - k + d}.

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
  \bs => matchElemP k d b l l' bs >>= matchElemP k d b r r' >>= matchElemP k d b t t'
matchElemP k d b (QuotTy a r) (QuotTy a' r') =
  \bs => matchElemP k d b a a' bs >>= matchElemP k d (2 + b) r r'
matchElemP k d b Refl Refl = Just
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
matchElemP _ _ _ _ _ = const Nothing

matchTyP k d b Ty.ZeroTy Ty.ZeroTy = Just
matchTyP k d b Ty.OneTy Ty.OneTy = Just
matchTyP k d b Ty.NatTy Ty.NatTy = Just
matchTyP k d b Ty.UniverseTy Ty.UniverseTy = Just
matchTyP k d b Ty.PropTy Ty.PropTy = Just
matchTyP k d b (Ty.PiTy a c) (Ty.PiTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d (1 + b) c c'
matchTyP k d b (Ty.SigmaTy a c) (Ty.SigmaTy a' c') =
  \bs => matchTyP k d b a a' bs >>= matchTyP k d (1 + b) c c'
matchTyP k d b (EqTy l r t) (EqTy l' r' t') =
  \bs => matchElemP k d b l l' bs >>= matchElemP k d b r r' >>= matchTyP k d b t t'
matchTyP k d b (El e) (El e') = matchElemP k d b e e'
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
matchTyP _ _ _ _ _ = const Nothing

||| Build the instantiating substitution: pattern context base ᐅ p_{k-1}
||| ᐅ ... ᐅ p₀ into the match site (Γ + d). Base part is ↑ᵈ; each bound
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
||| type lives in base ᐅ p_{k-1} ᐅ ... ᐅ p_{p+1}.
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
elemSize (Elem.EqTy l r t) = S (elemSize l + elemSize r + elemSize t)
elemSize (QuotTy a r) = S (elemSize a + elemSize r)
elemSize Refl = 1
elemSize (SigVar _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)
elemSize (Class a) = S (elemSize a)
elemSize (QuotElim f q) = S (elemSize f + elemSize q)
elemSize (Squash t) = S (tySize t)
elemSize Star = 1

tySize Ty.ZeroTy = 1
tySize Ty.OneTy = 1
tySize Ty.NatTy = 1
tySize Ty.UniverseTy = 1
tySize Ty.PropTy = 1
tySize (Ty.PiTy a b) = S (tySize a + tySize b)
tySize (Ty.SigmaTy a b) = S (tySize a + tySize b)
tySize (EqTy l r t) = S (elemSize l + elemSize r + tySize t)
tySize (El e) = S (elemSize e)
tySize (Prf e) = S (elemSize e)
tySize (Quotient a r) = S (tySize a + elemSize r)
tySize (Ty.SigVar _ es) = S (foldl (\acc, e => acc + elemSize e) 0 es)

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
  go b (Elem.EqTy l r t) (Elem.EqTy l' r' t') m = go b l l' m >>= go b r r' >>= go b t t'
  go b (QuotTy a r) (QuotTy a' r') m = go b a a' m >>= go (2+b) r r'
  go b Refl Refl m = Just m
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
  go _ _ _ _ = Nothing

  goT b Ty.ZeroTy Ty.ZeroTy m = Just m
  goT b Ty.OneTy Ty.OneTy m = Just m
  goT b Ty.NatTy Ty.NatTy m = Just m
  goT b Ty.UniverseTy Ty.UniverseTy m = Just m
  goT b Ty.PropTy Ty.PropTy m = Just m
  goT b (Ty.PiTy a d) (Ty.PiTy a' d') m = goT b a a' m >>= goT (1+b) d d'
  goT b (Ty.SigmaTy a d) (Ty.SigmaTy a' d') m = goT b a a' m >>= goT (1+b) d d'
  goT b (EqTy l r t) (EqTy l' r' t') m = go b l l' m >>= go b r r' >>= goT b t t'
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
  let instStep = \ps : PStep => MkStep side (pi ++ ps.ppath) (substElem ps.pprf sigma) ps.psels ps.pflip
  let pre = map (\ps => { flip $= not } (instStep ps)) (reverse c.preL)
  let post = map instStep c.postR
  pure (pre ++ [MkStep side pi prfMain selsMain False] ++ post)

materializeFlip : Cand -> Bindings -> (onLhs : Bool) -> Maybe (List Step)
materializeFlip c bs side = do
  (prfMain, selsMain) <- c.emit bs
  sigma <- instSub c.params 0 bs
  let instStep = \ps : PStep => MkStep side ps.ppath (substElem ps.pprf sigma) ps.psels ps.pflip
  -- flipped whole-equation use at the root: post-normalization is
  -- inverted (it now bridges INTO the stored rhs pattern), pre applies
  let pre = map (\ps => { flip $= not } (instStep ps)) (reverse c.postR)
  let post = map instStep c.preL
  pure (pre ++ [MkStep side [] prfMain selsMain True] ++ post)

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
          , at 1 0 r (\r' => Elem.EqTy l r' u)
          , at 2 0 u (\u' => Elem.EqTy l r u') ]
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
rewriteTyS side c pi d (EqTy l r t) =
  ((\(l', st) => (EqTy l' r t, st)) <$> rewriteElemS side c (0 :: pi) d l)
    <|> ((\(r', st) => (EqTy l r' t, st)) <$> rewriteElemS side c (1 :: pi) d r)
    <|> ((\(t', st) => (EqTy l r t', st)) <$> rewriteTyS side c (2 :: pi) d t)
rewriteTyS side c pi d (El e) =
  (\(e', st) => (El e', st)) <$> rewriteElemS side c (0 :: pi) d e
rewriteTyS side c pi d (Quotient a r) =
  ((\(a', st) => (Quotient a' r, st)) <$> rewriteTyS side c (0 :: pi) d a)
    <|> ((\(r', st) => (Quotient a r', st)) <$> rewriteElemS side c (1 :: pi) (2 + d) r)
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
  go (Elem.EqTy l0 r0 t0) (Elem.EqTy l1 r1 t1) =
    comp SelEqT t0 t1 ++ comp SelEqL l0 l1 ++ comp SelEqR r0 r1
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
  toPSteps = map (\s => MkPStep s.path s.prf s.sels s.flip)

  -- a hypothesis licenses an equation when its (peeled) type is an
  -- ≡-type OR a squashed one, Prf ∥l ≡ r ∈ t∥ — squashed reflection
  -- (the kernel's `licensed` accepts both proof shapes)
  eqShape : Ty -> Maybe (Elem, Elem, Ty)
  eqShape (EqTy l r t) = Just (l, r, t)
  eqShape (Prf p) =
    case betaElem st.sig p of
      Squash (EqTy l r t) => Just (l, r, t)
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
    _ => Nothing
inferNe _ _ _ = Nothing

-- ===== Certificate-emitting speculative equality =====
--
-- Every discharge now RETURNS its evidence: a Kernel.ECert. The
-- committing conversion validates the certificate by kernel replay
-- before believing it (docs/NovaPipeline.txt) — a discharge whose
-- certificate does not replay is no discharge at all.

codeOf : Ty -> Maybe Elem
codeOf Ty.ZeroTy = Just Elem.ZeroTy
codeOf Ty.OneTy = Just Elem.OneTy
codeOf Ty.NatTy = Just Elem.NatTy
codeOf (Ty.PiTy a b) = Elem.PiTy <$> codeOf a <*> codeOf b
codeOf (Ty.SigmaTy a b) = Elem.SigmaTy <$> codeOf a <*> codeOf b
codeOf (EqTy l r t) = (Elem.EqTy l r) <$> codeOf t
-- the relation is an Ω-element in BOTH the type former and the code:
-- El (A / R) ≜ El A / R, so it passes through unchanged
codeOf (Quotient a r) = QuotTy <$> codeOf a <*> Just r
codeOf (El e) = Just e
-- Ω and Prf p deliberately have NO codes in 𝕌 (the load-bearing
-- prohibition of the Ω design — see docs/NovaFoundation.txt)
codeOf _ = Nothing

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
      Squash (EqTy l r t) => do sub <- spEqElemC dep st cs ctx l r t
                                pure (MkECert [] (FWitness (Just sub)))
      _ => Nothing
  -- el-prf-prop: proof irrelevance — any two elements of Prf p are equal
  spEqStructC dep st cs ctx a b (Prf _) = Just (MkECert [] FProp)
  -- code-prop-eq: mutually implied prop codes are equal; each direction
  -- is ⋆ with a synthesized witness under the other side's hypothesis
  spEqStructC dep st cs ctx a b Ty.PropTy =
    case (a, b) of
      (Squash tA, Squash tB) => do
        (fe, fsk) <- mkImpl tA tB
        (be, bsk) <- mkImpl tB tA
        pure (MkECert [] (FPropExt fe fsk be bsk))
      _ => Nothing
   where
    -- under ctx ᐅ Prf ∥src∥, a proof of (Prf ∥tgt∥)[↑]: 𝟙-shaped
    -- squashees outright, ≡-shaped ones by a nested discharge (which
    -- may use the unsquashed hypothesis as a rewrite candidate)
    mkImpl : Ty -> Ty -> Maybe (Elem, Skel)
    mkImpl src tgt =
      let ctx' = ctx :< Prf (Squash src) in
      case betaTy st.sig (substTy tgt Wk) of
        Ty.OneTy => Just (Star, Nd [PSquashWit OneIntro (Nd [] [])] [])
        EqTy l r t => do
          c <- spEqElemC dep st (mkCandSet st ctx') ctx' l r t
          Just (Star, Nd [PSquashWit Refl (Nd [PReflEq c] [])] [])
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
  spCongC dep st cs ctx (Elem.EqTy l r t) (Elem.EqTy l' r' t') = do
    st1 <- spEqElemC dep st cs ctx t t' Ty.UniverseTy >>= flatSteps
    st2 <- spEqElemC dep st cs ctx l l' (El t') >>= flatSteps
    st3 <- spEqElemC dep st cs ctx r r' (El t') >>= flatSteps
    pure (prefixSteps 2 st1 ++ prefixSteps 0 st2 ++ prefixSteps 1 st3)
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
          Just (EqTy hl hr _) =>
            if (betaElem st.sig hl == lN && betaElem st.sig hr == rN)
              then Just (CtxVar i)
              else Nothing
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
            EqTy l r t =>
              let lN = betaElem st.sig l
                  rN = betaElem st.sig r in
              hypWitness lN rN
              <|> (if lN == rN then Just Refl else Nothing)
              <|> (do cert <- candMatchC dep st cs ctx lN rN (betaTy st.sig t)
                      -- only a bare, proof-carrying single acceptance can
                      -- be turned into an element; steps cannot
                      Nothing)
            Prf pr =>
              hypPrfWitness (Prf (betaElem st.sig pr))
              <|> (case betaElem st.sig pr of
                     Squash Ty.OneTy => Just Star
                     Squash (EqTy l r _) =>
                       if betaElem st.sig l == betaElem st.sig r
                         then Just Star
                         else Nothing
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
        (EqTy l0 r0 t0, EqTy l1 r1 t1) => do
          stT <- prefixSteps 2 <$> go t0 t1
          stL <- flatE False 0 ctx l0 l1 t1
          stR <- flatE False 1 ctx r0 r1 t1
          pure (stT ++ stL ++ stR)
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

oblCount : ElabM Nat
oblCount = do
  st <- getSt
  pure (length (toList st.obls))

assume : Stmt -> String -> Maybe Stmt -> ElabM ()
assume stmt site comp = do
  st <- getSt
  case stmt of
    StElem ctx env a b ty => do
      if assumedMatchE st ctx a b ty
        then pure ()
        else modifySt $ \s =>
          { assumedE $= ((ctx, rwNfElem st ctx a, rwNfElem st ctx b, betaTy st.sig ty) ::)
          , obls $= (:< MkObl stmt site comp) } s
    StTy ctx env x y => do
      let x' = rwNfTy st ctx x
          y' = rwNfTy st ctx y
      if any (\(c, u, v) => c == ctx && ((u == x' && v == y') || (u == y' && v == x'))) st.assumedT
        then pure ()
        else modifySt $ \s =>
          { assumedT $= ((ctx, x', y') ::)
          , obls $= (:< MkObl stmt site comp) } s
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
  ||| Γ ⊢ a ≐ b : A ↓ — always succeeds; assumes what it cannot discharge.
  convElem : Ctx -> NameEnv -> String -> Maybe Stmt -> Elem -> Elem -> Ty -> ElabM (Maybe ECert)
  convElem ctx env site comp a b ty = do
    st <- getSt
    let cs = mkCandSet st ctx
    -- a discharge counts only if its certificate replays in the kernel;
    -- a replay failure is reported on the obligation (engine bug signal)
    let mcert = spEqElemC spDepth st cs ctx a b ty
    let attempt = map (\cert => kCheckEqElem st.sig ctx kernelFuel cert a b ty) mcert
    let site = case attempt of
                 Just (Left kerrMsg) => site ++ " [replay failed: " ++ kerrMsg ++ "]"
                 _ => site
    if attempt == Just (Right ())
      then pure mcert
      else map (const Nothing) $ do
        let cur = StElem ctx env a b ty
        let comp' = comp <|> Just cur
        let a' = rwNfElem st ctx a
        let b' = rwNfElem st ctx b
        n0 <- oblCount
        decompose site cur comp' a' b' (rwNfTy st ctx ty)
        -- a decomposition that surfaced no obligation discharged all
        -- children — but the COMPOSITE site still has no certificate,
        -- so the item could never be kernel-accepted. Keep the
        -- acceptance semantics honest: the composite is assumed (the
        -- remedy is a lemma that makes it directly matchable).
        n1 <- oblCount
        when (n1 == n0) $ assume cur site comp
   where
    decompose : String -> Stmt -> Maybe Stmt -> Elem -> Elem -> Ty -> ElabM ()
    decompose site cur comp' a' b' tyW = do
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
                  Squash (EqTy l r t) => ignore $ convElem ctx env site comp' l r t
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
          -- sufficient direction at Ω: equal squashees give equal props
          -- (the faithful iff route lives in spEqStructC's propext)
          (Squash tA, Squash tB, Ty.PropTy) =>
            ignore $ convTy ctx env site comp' tA tB
          (Elem.EqTy l r t, Elem.EqTy l' r' t', Ty.UniverseTy) => do
            ignore $ convElem ctx env site comp' t t' Ty.UniverseTy
            ignore $ convElem ctx env site comp' l l' (El t')
            ignore $ convElem ctx env site comp' r r' (El t')
          (NatElim z s t0, NatElim z' s' t1, _) =>
            if z == z' && s == s'
              then ignore $ convElem ctx env site comp' t0 t1 Ty.NatTy
              else assume cur site comp
          (PiApp f x, PiApp g y, _) =>
            if f == g
              then do st' <- getSt
                      case betaTy st'.sig <$> inferNe st' ctx f of
                        Just (Ty.PiTy dom _) => ignore $ convElem ctx env site comp' x y dom
                        _ => assume cur site comp
              else assume cur site comp
          _ => assume cur site comp

  ||| Γ ⊢ A ≐ B type ↓
  convTy : Ctx -> NameEnv -> String -> Maybe Stmt -> Ty -> Ty -> ElabM (Maybe ECert)
  convTy ctx env site comp tyA tyB = do
    st <- getSt
    let cs = mkCandSet st ctx
    let mcert = spEqTyC spDepth st cs ctx tyA tyB
    let attempt = map (\cert => kCheckEqTy st.sig ctx kernelFuel cert tyA tyB) mcert
    let site = case attempt of
                 Just (Left kerrMsg) => site ++ " [replay failed: " ++ kerrMsg ++ "]"
                 _ => site
    if attempt == Just (Right ())
      then pure mcert
      else map (const Nothing) $ do
        let cur = StTy ctx env tyA tyB
        let comp' = comp <|> Just cur
        n0 <- oblCount
        decomposeT site cur comp' (rwNfTy st ctx tyA) (rwNfTy st ctx tyB)
        n1 <- oblCount
        when (n1 == n0) $ assume cur site comp
   where
    decomposeT : String -> Stmt -> Maybe Stmt -> Ty -> Ty -> ElabM ()
    decomposeT site cur comp' tyA' tyB' = do
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
          (EqTy l0 r0 t0, EqTy l1 r1 t1) => do
            ignore $ convTy ctx env site comp' t0 t1
            ignore $ convElem ctx env site comp' l0 l1 t1
            ignore $ convElem ctx env site comp' r0 r1 t1
          (El x, El y) => ignore $ convElem ctx env site comp' x y Ty.UniverseTy
          (Prf x, Prf y) => ignore $ convElem ctx env site comp' x y Ty.PropTy
          (El x, rigid) => case codeOf rigid of
                             Just c => ignore $ convElem ctx env site comp' x c Ty.UniverseTy
                             Nothing => assume cur site comp
          (rigid, El y) => case codeOf rigid of
                             Just c => ignore $ convElem ctx env site comp' c y Ty.UniverseTy
                             Nothing => assume cur site comp
          _ => assume cur site comp

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
      Just (SigDef _ _ _ _) => throw "\{site}: '\{x}' is a term definition, used as a type"
      Nothing => throw "\{site}: unknown signature name '\{x}'"
  elabTy ctx env site (STyPi x a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy (ctx :< a') (env :< x) site b
    pure (Ty.PiTy a' b', Nd [] [aSk, bSk])
  elabTy ctx env site (STySigma x a b) = do
    (a', aSk) <- elabTy ctx env site a
    (b', bSk) <- elabTy (ctx :< a') (env :< x) site b
    pure (Ty.SigmaTy a' b', Nd [] [aSk, bSk])
  elabTy ctx env site (STyQuot a nx ny r) = do
    (a', aSk) <- elabTy ctx env site a
    (r', rSk) <- checkElem (ctx :< a' :< substTy a' Wk) (env :< nx :< ny) site r Ty.PropTy
    pure (Ty.Quotient a' r', Nd [] [aSk, rSk])
  elabTy ctx env site (STyEq l r t) = do
    (t', tSk) <- elabTy ctx env site t
    (l', lSk) <- checkElem ctx env site l t'
    (r', rSk) <- checkElem ctx env site r t'
    pure (EqTy l' r' t', Nd [] [lSk, rSk, tSk])
  elabTy ctx env site (STyEl e) = do
    (e', eSk) <- checkElem ctx env site e Ty.UniverseTy
    pure (El e', Nd [] [eSk])
  elabTy ctx env site STyProp = pure (Ty.PropTy, Nd [] [])
  elabTy ctx env site (STyPrf e) = do
    (e', eSk) <- checkElem ctx env site e Ty.PropTy
    pure (Prf e', Nd [] [eSk])

  export
  inferElem : Ctx -> NameEnv -> String -> SElem -> ElabM (Elem, Ty, Skel)
  inferElem ctx env site (SVar n i) =
    case ctxLookup ctx i of
      Just ty => pure (CtxVar i, ty, Nd [] [])
      Nothing => throw "\{site}: variable index out of bounds"
  inferElem ctx env site (SSig x0) = do
    st <- getSt
    let x = resolveSigName st x0
    case sigLookup x st.sig of
      Just (SigDef [<] _ _ ty) => pure (SigVar x [<], ty, Nd [] [])
      Just (SigDef _ _ _ _) => throw "\{site}: '\{x}' has a non-empty declaration context"
      Just (SigTyDef _ _ _) => throw "\{site}: '\{x}' is a type definition, used as a term"
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
  inferElem ctx env site (SNatElim n mot z n2 ih s t) = do
    (motTy, motSk) <- elabTy (ctx :< Ty.NatTy) (env :< n) site mot
    (z', zSk) <- checkElem ctx env site z (substTy motTy (Ext Id NatIntro0))
    (s', sSk) <- checkElem (ctx :< Ty.NatTy :< motTy) (env :< n2 :< ih) site s
                   (substTy motTy (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
    (t', tSk) <- checkElem ctx env site t Ty.NatTy
    pure (NatElim z' s' t', substTy motTy (Ext Id t'),
          Nd [PMotive motTy motSk] [zSk, sSk, tSk])
  inferElem ctx env site (SQuotElim zn mot an f q) = do
    (q', qTy, qSk) <- inferElem ctx env site q
    st <- getSt
    case preferQuot st ctx qTy of
      Just (a, r, _) => do
        (motTy, motSk) <- elabTy (ctx :< Ty.Quotient a r) (env :< zn) site mot
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
  inferElem ctx env site (SQuotC a nx ny r) = do
    (a', aSk) <- checkElem ctx env site a Ty.UniverseTy
    (r', rSk) <- checkElem (ctx :< El a' :< substTy (El a') Wk) (env :< nx :< ny) site r Ty.PropTy
    pure (QuotTy a' r', Ty.UniverseTy, Nd [] [aSk, rSk])
  inferElem ctx env site (SSquash t) = do
    (t', tSk) <- elabTy ctx env site t
    pure (Squash t', Ty.PropTy, Nd [] [tSk])
  inferElem ctx env site SStar =
    throw "\{site}: cannot infer the type of ⋆\{structuralHint}"
  inferElem ctx env site (SEqC l r t) = do
    (t', tSk) <- checkElem ctx env site t Ty.UniverseTy
    (l', lSk) <- checkElem ctx env site l (El t')
    (r', rSk) <- checkElem ctx env site r (El t')
    pure (Elem.EqTy l' r' t', Ty.UniverseTy, Nd [] [lSk, rSk, tSk])
  inferElem ctx env site (SLam _ _) =
    throw "\{site}: cannot infer the type of a λ\{structuralHint}"
  inferElem ctx env site (SPair _ _) =
    throw "\{site}: cannot infer the type of a pair\{structuralHint}"
  inferElem ctx env site SRefl =
    throw "\{site}: cannot infer the type of Refl\{structuralHint}"
  inferElem ctx env site (SClass _) =
    throw "\{site}: cannot infer the type of class\{structuralHint}"
  inferElem ctx env site (SZeroElim _) =
    throw "\{site}: cannot infer the type of 𝟘-elim\{structuralHint}"

  export
  checkElem : Ctx -> NameEnv -> String -> SElem -> Ty -> ElabM (Elem, Skel)
  checkElem ctx env site (SLam x t) ty = do
    st <- getSt
    case preferPi st ctx ty of
      Just (a, b, exp) => do
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
  checkElem ctx env site SRefl ty = do
    st <- getSt
    -- Prefer the type as written (readable obligation statements); fall
    -- back to its normal form when the ≡ only appears after unfolding.
    case ty of
      EqTy l r t => do
        c <- convElem ctx env "\{site}: checking Refl" Nothing l r t
        pure (Refl, Nd [PReflEq (certOr c)] [])
      _ => case rwNfTy st ctx ty of
             tyX@(EqTy l r t) => do
               c <- convElem ctx env "\{site}: checking Refl" Nothing l r t
               let sk = Nd [PReflEq (certOr c)] []
               pure (Refl, maybe sk (\e => withExpose (Just e) sk) (exposeCert st ctx ty tyX))
             _ => throw "\{site}: Refl checked against a non-≡ type\{structuralHint}"
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
    let mPrf : Maybe (Elem, Maybe (Ty, ECert)) =
          case ty of
            Prf p => Just (p, Nothing)
            _ => case rwNfTy st ctx ty of
                   tyX@(Prf p) => (\e => (p, Just e)) <$> exposeCert st ctx ty tyX
                   _ => Nothing
    case mPrf of
      Nothing => throw "\{site}: ⋆ checked against a non-Prf type\{structuralHint}"
      Just (p, exp) =>
        -- el-squash-i: synthesize the witness of the squashee —
        -- 𝟙-shaped outright, ≡-shaped via the conversion judgement
        case betaElem st.sig p of
          Squash sq =>
            case betaTy st.sig sq of
              Ty.OneTy => pure (Star, withExpose exp (Nd [PSquashWit OneIntro (Nd [] [])] []))
              EqTy l r t => do
                c <- convElem ctx env "\{site}: ⋆ witness equation" Nothing l r t
                pure (Star, withExpose exp (Nd [PSquashWit Refl (Nd [PReflEq (certOr c)] [])] []))
              _ => throw "\{site}: ⋆ can witness only 𝟙- and ≡-shaped squashes automatically (define the inhabitant and squash it)"
          _ => throw "\{site}: ⋆ checked against Prf of a non-∥∥ code\{structuralHint}"
  checkElem ctx env site t ty = do
    (t', inferred, tSk) <- inferElem ctx env site t
    c <- convTy ctx env "\{site}: inferred vs expected type" Nothing inferred ty
    pure (t', addPayload (PSwitch (certOr c)) tSk)

-- ===== Items =====

||| Register a just-accepted definition's equation (if its type peels to
||| an ≡-type) as a rewrite candidate: the WHOLE context (telescope +
||| peeled Πs) is parametric, so the lemma applies in any context.
addLemma : String -> Ctx -> Ty -> ElabM ()
addLemma name delta ty = do
  st <- getSt
  let (delta', peeled) = peelPis delta (betaTy st.sig ty)
  -- squashed equations register too (Prf ∥l ≡ r ∈ t∥ — the kernel's
  -- `licensed` accepts the squashed proof shape)
  let meq : Maybe (Elem, Elem, Ty) =
        case peeled of
          EqTy l r t => Just (l, r, t)
          Prf p => case betaElem st.sig p of
                     Squash (EqTy l r t) => Just (l, r, t)
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
          toP = map (\s => MkPStep s.path s.prf s.sels s.flip)
      in modifySt $ { lemmas $= (closeCand (MkCand name k (toList delta') (fst lRes) (fst rRes)
                                                   mk (toP (snd lRes)) (toP (snd rRes))) ++) }
    _ => pure ()

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

export
elabItem : SItem -> ElabM String
elabItem (SDef x ty body) = do
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
  after <- oblCount
  kernelAccept "def \{x}"
    (\ksig => kCheckDefItem ksig kernelFuel (MkKDefArt q [] ty' tySk body' bodySk))
    (after == 0)
  modifySt $ { sig $= (:< SigDef [<] q body' ty'), vis $= (:< (x, q)) }
  addLemma q [<] ty'
  pure "defined \{x}"
elabItem (STypeDef x ty) = do
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
  pure "defined type \{x}"

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
  mitems : List SItem

oblReport : FixTable -> List Obligation -> String
oblReport tbl os =
  "open obligations (\{show (length os)}):\n" ++
  joinBy "\n" (zipWith (prettyObligation tbl) [0 .. minus (length os) 1] os)

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
    let oblList = toList st.obls in
    joinBy "\n" echoes ++ "\n" ++
    (case oblList of
       [] => "Accepted."
       os => oblReport tbl os)

  goItems : ElabSt -> List SItem -> Either (List String, String) (ElabSt, List String)
  goItems st [] = Right (st, [])
  goItems st (item :: rest) =
    case runElabM (elabItem item) st of
      Left err => Left ([], err)
      Right (st', echo) =>
        case goItems st' rest of
          Left (echoes, err) => Left (echo :: echoes, err)
          Right (st'', echoes) => Right (st'', echo :: echoes)

  go : ElabSt -> List ModUnit -> List String -> String
  go st [] echoes = joinBy "\n" (echoes ++ ["Error: empty program"])
  go st (MkModUnit name imps tbl items :: rest) echoes = do
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
                -- only ACCEPTED modules are importable
                case toList st'.obls of
                  [] => go st' rest (echoes ++ hdr ++ itemEchoes)
                  os => joinBy "\n" (echoes ++ hdr ++ itemEchoes) ++ "\n" ++
                        oblReport tbl os ++ "\n" ++
                        "Error: module \{name} has open obligations and cannot be imported"

||| Elaborate a single surface file (no imports — resolving them needs
||| the module loader); the returned string is the complete report.
export
elabFile : String -> String
elabFile content =
  case runSurfaceParser (parseSFile []) content of
    Left err => "Parse error: \{err}"
    Right ([], decls, items) => elabProgram [MkModUnit "" [] decls items]
    Right (_, _, _) => "Error: this entry point resolves no imports (use the module-aware loader)"
