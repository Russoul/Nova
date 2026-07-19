module Nova.Foundation.Elaboration

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
--   * beta-normalization (β, El-decoding, x-β signature unfolding);
--   * fuel-bounded REWRITING with the equation store: accepted Eq-typed
--     lemmas from Σ (their leading Πs peeled into pattern parameters)
--     and Eq-typed hypotheses of the local context (likewise peeled),
--     each oriented left-to-right as stated, applied at any subterm —
--     this gives single-lemma discharge, transitivity chains, and
--     congruence positioning in one mechanism;
--   * type-directed comparison: Π/Σ-η, 𝟘/𝟙-Prop, and quotient
--     class-equations (a 𝟙-shaped relation is inhabited outright, an
--     Eq-shaped relation reduces the witness to its equation);
--   * congruence decomposition in the sufficient direction, with the
--     composite retained for the report;
--   * assumption (dedup by normalized statement, symmetric).
--
-- Soundness of rewriting: a candidate's instance l[σ] ≐ r[σ] is
-- Foundation-derivable by (el-eq-subst) from the reflected lemma or
-- hypothesis; σ's well-typedness follows by inversion from the matched
-- instance occurring inside an elaborated (well-typed) term. Replacing
-- a subterm by a judgementally equal one is congruence.

import Data.List
import Data.Maybe
import Data.SnocList
import Data.String

import Nova.Foundation.Syntax
import Nova.Foundation.Subst
import Nova.Foundation.Beta
import Nova.Foundation.Parser
import Nova.Foundation.Elaboration.Surface
import Nova.Foundation.Elaboration.Parser
import Nova.Foundation.Derivation.NamedParser
import Nova.Foundation.Derivation.NamedPretty

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
record Cand where
  constructor MkCand
  candName : String
  params : Nat
  paramTys : List Ty
  lhs : Elem
  rhs : Elem

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
  lemmas : List Cand
  assumedE : List (Ctx, Elem, Elem, Ty)   -- normalized keys of assumed elem equations
  assumedT : List (Ctx, Ty, Ty)           -- normalized keys of assumed type equations
  obls : SnocList Obligation

initSt : ElabSt
initSt = MkElabSt [<] [] [] [] [<]

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
matchElemP _ _ _ _ _ = const Nothing

||| Build the instantiating substitution: pattern context base ᐅ p_{k-1}
||| ᐅ ... ᐅ p₀ into the match site (Γ + d). Base part is ↑ᵈ; each bound
||| term (canonical in Γ) is weakened by d.
instSub : (k : Nat) -> (d : Nat) -> Bindings -> Maybe Sub
instSub k d bs = go k (wkN d)
 where
  -- Ext binds index 0 last: fold from p_{k-1} down to p₀.
  go : Nat -> Sub -> Maybe Sub
  go Z acc = Just acc
  go (S p) acc = do
    e <- lookup p bs
    go p (Ext acc (weakenElemN d e))

||| One rewrite step with `cand` anywhere in `t` (t at depth d below Γ).
rewriteElem : Cand -> (d : Nat) -> Elem -> Maybe Elem
rewriteElem cand d t =
  case matchElemP cand.params d 0 cand.lhs t [] of
    Just bs => do sigma <- instSub cand.params d bs
                  Just (substElem cand.rhs sigma)
    Nothing => descend t
 where
  first : List (Maybe a) -> Maybe a
  first [] = Nothing
  first (Just x :: _) = Just x
  first (Nothing :: rest) = first rest

  descend : Elem -> Maybe Elem
  descend (ZeroElim u)       = ZeroElim <$> rewriteElem cand d u
  descend (NatIntro1 u)      = NatIntro1 <$> rewriteElem cand d u
  descend (NatElim z s u)    =
    first [ (\z' => NatElim z' s u) <$> rewriteElem cand d z
          , (\s' => NatElim z s' u) <$> rewriteElem cand (2 + d) s
          , (\u' => NatElim z s u') <$> rewriteElem cand d u ]
  descend (PiIntro f)        = PiIntro <$> rewriteElem cand (1 + d) f
  descend (PiApp f e)        =
    first [ (\f' => PiApp f' e) <$> rewriteElem cand d f
          , (\e' => PiApp f e') <$> rewriteElem cand d e ]
  descend (SigmaIntro u v)   =
    first [ (\u' => SigmaIntro u' v) <$> rewriteElem cand d u
          , (\v' => SigmaIntro u v') <$> rewriteElem cand d v ]
  descend (SigmaElim1 u)     = SigmaElim1 <$> rewriteElem cand d u
  descend (SigmaElim2 u)     = SigmaElim2 <$> rewriteElem cand d u
  descend (Elem.PiTy a c)    =
    first [ (\a' => Elem.PiTy a' c) <$> rewriteElem cand d a
          , (\c' => Elem.PiTy a c') <$> rewriteElem cand (1 + d) c ]
  descend (Elem.SigmaTy a c) =
    first [ (\a' => Elem.SigmaTy a' c) <$> rewriteElem cand d a
          , (\c' => Elem.SigmaTy a c') <$> rewriteElem cand (1 + d) c ]
  descend (Elem.EqTy l r u)  =
    first [ (\l' => Elem.EqTy l' r u) <$> rewriteElem cand d l
          , (\r' => Elem.EqTy l r' u) <$> rewriteElem cand d r
          , (\u' => Elem.EqTy l r u') <$> rewriteElem cand d u ]
  descend (QuotTy a r)       =
    first [ (\a' => QuotTy a' r) <$> rewriteElem cand d a
          , (\r' => QuotTy a r') <$> rewriteElem cand (2 + d) r ]
  descend (SigVar x es)      = SigVar x <$> goSubNorm es
   where
    goSubNorm : SubNorm -> Maybe SubNorm
    goSubNorm [<] = Nothing
    goSubNorm (es :< e) =
      first [ (:< e) <$> goSubNorm es
            , (es :<) <$> rewriteElem cand d e ]
  descend (Class a)          = Class <$> rewriteElem cand d a
  descend (QuotElim f q)     =
    first [ (\f' => QuotElim f' q) <$> rewriteElem cand (1 + d) f
          , (\q' => QuotElim f q') <$> rewriteElem cand d q ]
  descend _ = Nothing

rewriteTy : Cand -> (d : Nat) -> Ty -> Maybe Ty
rewriteTy cand d Ty.ZeroTy = Nothing
rewriteTy cand d Ty.OneTy = Nothing
rewriteTy cand d Ty.NatTy = Nothing
rewriteTy cand d Ty.UniverseTy = Nothing
rewriteTy cand d (Ty.PiTy a b) =
  ((\a' => Ty.PiTy a' b) <$> rewriteTy cand d a)
    <|> ((\b' => Ty.PiTy a b') <$> rewriteTy cand (1 + d) b)
rewriteTy cand d (Ty.SigmaTy a b) =
  ((\a' => Ty.SigmaTy a' b) <$> rewriteTy cand d a)
    <|> ((\b' => Ty.SigmaTy a b') <$> rewriteTy cand (1 + d) b)
rewriteTy cand d (EqTy l r t) =
  ((\l' => EqTy l' r t) <$> rewriteElem cand d l)
    <|> ((\r' => EqTy l r' t) <$> rewriteElem cand d r)
    <|> ((\t' => EqTy l r t') <$> rewriteTy cand d t)
rewriteTy cand d (El e) = El <$> rewriteElem cand d e
rewriteTy cand d (Quotient a r) =
  ((\a' => Quotient a' r) <$> rewriteTy cand d a)
    <|> ((\r' => Quotient a r') <$> rewriteTy cand (2 + d) r)
rewriteTy cand d (Ty.SigVar x es) = Ty.SigVar x <$> goSubNorm es
 where
  goSubNorm : SubNorm -> Maybe SubNorm
  goSubNorm [<] = Nothing
  goSubNorm (es :< e) =
    ((:< e) <$> goSubNorm es) <|> ((es :<) <$> rewriteElem cand d e)

-- ===== Candidates in scope =====

||| Peel leading Πs off a (normalized) type, extending the context.
peelPis : Ctx -> Ty -> (Ctx, Ty)
peelPis ctx ty =
  case ty of
    Ty.PiTy a b => peelPis (ctx :< a) b
    _ => (ctx, ty)

||| The last n entries of a context, outermost first.
lastEntries : Nat -> Ctx -> List Ty
lastEntries n ctx = drop (minus (length ctx) n) (toList ctx)

-- ===== Normalize-and-rewrite =====

rwFuel : Nat
rwFuel = 40

tryCands : List Cand -> (Cand -> Maybe a) -> Maybe a
tryCands [] f = Nothing
tryCands (c :: cs) f = f c <|> tryCands cs f

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

||| Whether lhs and rhs are equal up to a bijective renaming of the
||| parametric variables (e.g. commutativity: plus m n vs plus n m).
||| Such "permutative" equations loop as rewrite rules — they are kept
||| for whole-equation matching only.
permutative : Cand -> Bool
permutative c = isJust (go 0 c.lhs c.rhs [])
 where
  bij : Nat -> Nat -> List (Nat, Nat) -> Maybe (List (Nat, Nat))
  bij i j m =
    case (lookup i m, find (\(_, y) => y == j) m) of
      (Nothing, Nothing) => Just ((i, j) :: m)
      (Just j', _) => if j' == j then Just m else Nothing
      (Nothing, Just _) => Nothing

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
  go _ _ _ _ = Nothing

||| Candidates usable as REWRITE rules: strictly-shrinking rules first
||| (e.g. `plus n Z → n`), then size-preserving non-permutative ones
||| (e.g. `plus n (S m) → S (plus n m)`, an induction hypothesis).
||| Permutative and growing equations never rewrite — they remain
||| available to whole-equation matching (candMatch).
ordered : List Cand -> List Cand
ordered cs =
  let usable = filter (\c => elemSize c.rhs <= elemSize c.lhs && not (permutative c)) cs
      shrinking = filter (\c => elemSize c.rhs < elemSize c.lhs) usable
      rest = filter (\c => not (elemSize c.rhs < elemSize c.lhs)) usable
  in shrinking ++ rest

rwNfElemWith : Sig -> List Cand -> Elem -> Elem
rwNfElemWith sig cands e =
  let start = betaElem sig e in go rwFuel [start] start
 where
  go : Nat -> List Elem -> Elem -> Elem
  go Z seen t = t
  go (S fuel) seen t =
    case tryCands cands (\c => rewriteElem c 0 t) of
      Just t' =>
        let t'' = betaElem sig t' in
        if elem t'' seen then t else go fuel (t'' :: seen) t''
      Nothing => t

rwNfTyWith : Sig -> List Cand -> Ty -> Ty
rwNfTyWith sig cands ty =
  let start = betaTy sig ty in go rwFuel [start] start
 where
  go : Nat -> List Ty -> Ty -> Ty
  go Z seen t = t
  go (S fuel) seen t =
    case tryCands cands (\c => rewriteTy c 0 t) of
      Just t' =>
        let t'' = betaTy sig t' in
        if elem t'' seen then t else go fuel (t'' :: seen) t''
      Nothing => t

||| Close a candidate under component decomposition: an equation between
||| same-headed universe codes also contributes its component equations
||| (licensed by Foundation's code-injectivity rules — →-inj-𝕌 etc.; a
||| binder component becomes an extra parametric entry). The S component
||| is included too (derivable via a ℕ-elim predecessor, no rule
||| needed). class is NOT decomposed: quotients are not injective.
closeCand : Cand -> List Cand
closeCand c = c :: go c.lhs c.rhs
 where
  comp : Elem -> Elem -> List Cand
  comp l r = closeCand ({ lhs := l, rhs := r } c)

  -- a component under n extra binders: those binders become the new
  -- innermost parameters (their indices in the component are already
  -- 0..n-1, with the old parameters shifted up — exactly the Cand
  -- convention); tys lists their types innermost-last
  compUnder : List Ty -> Elem -> Elem -> List Cand
  compUnder tys l r =
    closeCand ({ params := c.params + length tys
               , paramTys := c.paramTys ++ tys
               , lhs := l, rhs := r } c)

  go : Elem -> Elem -> List Cand
  go (NatIntro1 x) (NatIntro1 y) = comp x y
  go (Elem.PiTy a0 b0) (Elem.PiTy a1 b1) =
    comp a0 a1 ++ compUnder [El a1] b0 b1
  go (Elem.SigmaTy a0 b0) (Elem.SigmaTy a1 b1) =
    comp a0 a1 ++ compUnder [El a1] b0 b1
  go (QuotTy a0 r0) (QuotTy a1 r1) =
    comp a0 a1 ++ compUnder [El a1, substTy (El a1) Wk] r0 r1
  go (Elem.EqTy l0 r0 t0) (Elem.EqTy l1 r1 t1) =
    comp t0 t1 ++ comp l0 l1 ++ comp r0 r1
  go _ _ = []

||| Eq-typed hypotheses of Γ (leading Πs peeled), as rewrite candidates
||| with base Γ. Justified by Foundation (reflect ☐ᵢ e₁ ... eₖ). Their
||| sides are normalized against the LEMMA store, so that a hypothesis
||| stated in one spelling (e.g. an induction hypothesis in the
||| original association) still matches goals the lemma rewrites have
||| already canonicalized. Each candidate is closed under component
||| decomposition (closeCand).
hypCands : ElabSt -> Ctx -> List Cand
hypCands st ctx = concatMap closeCand (mapMaybe candAt [0 .. minus (length ctx) 1])
 where
  lemmaRw : List Cand
  lemmaRw = ordered st.lemmas

  candAt : Nat -> Maybe Cand
  candAt i = do
    tyI <- ctxLookup ctx i
    let (ctx', peeled) = peelPis ctx (betaTy st.sig tyI)
    let k = minus (length ctx') (length ctx)
    case peeled of
      EqTy l r t =>
        Just (MkCand "hypothesis" k (lastEntries k ctx')
                     (rwNfElemWith st.sig lemmaRw l)
                     (rwNfElemWith st.sig lemmaRw r))
      _ => Nothing

||| The candidate store, computed ONCE per conversion entry and
||| threaded through the speculative machinery (recomputing it per
||| normalization call is quadratic in practice: every hypothesis is
||| itself lemma-normalized on construction).
record CandSet where
  constructor MkCandSet
  all : List Cand   -- everything (for whole-equation matching)
  rw : List Cand    -- usable as rewrite rules, ordered
  hops : List Cand  -- ONLY those rewriting cannot apply (permutative /
                    -- growing) — the non-redundant transitivity hops

mkCandSet : ElabSt -> Ctx -> CandSet
mkCandSet st ctx =
  let cs = st.lemmas ++ hypCands st ctx
      rws = ordered cs
      hopsOnly = filter (\c => permutative c || elemSize c.rhs > elemSize c.lhs) cs
  in MkCandSet cs rws hopsOnly

||| Weaken a candidate set into an extended context: candidates' terms
||| live in base ᐅ params, so the base grows under the params. (A new
||| binder of ≡-type is NOT added as a candidate here — a documented
||| completeness limitation of speculative descent under binders.)
extendCS : CandSet -> CandSet
extendCS cs = MkCandSet (map wk cs.all) (map wk cs.rw) (map wk cs.hops)
 where
  liftK : Nat -> Sub
  liftK Z = Wk
  liftK (S n) = under (liftK n)

  wk : Cand -> Cand
  wk c = { lhs $= (\e => substElem e (liftK c.params))
         , rhs $= (\e => substElem e (liftK c.params)) } c

rwNfElem : ElabSt -> Ctx -> Elem -> Elem
rwNfElem st ctx e = rwNfElemWith st.sig (mkCandSet st ctx).rw e

rwNfTy : ElabSt -> Ctx -> Ty -> Ty
rwNfTy st ctx ty = rwNfTyWith st.sig (mkCandSet st ctx).rw ty

||| Instantiating substitution for a parameter's own type: param p's
||| type lives in base ᐅ p_{k-1} ᐅ ... ᐅ p_{p+1}; every outer parameter
||| must already be bound. Base part is the identity (queries live in
||| the candidate's base context).
condSub : (k : Nat) -> (p : Nat) -> Bindings -> Maybe Sub
condSub k p bs =
  -- NB: Idris ranges descend when from > to; guard explicitly.
  let idxs = if S p <= minus k 1 then reverse [S p .. minus k 1] else [] in
  foldl (\acc, j => [| Ext acc (lookup j bs) |]) (Just Id) idxs

-- ===== Neutral type inference (for spine decomposition) =====

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

-- ===== Speculative (non-committing) equality =====

||| Universe code of a (normalized) type, when it has one.
codeOf : Ty -> Maybe Elem
codeOf Ty.ZeroTy = Just Elem.ZeroTy
codeOf Ty.OneTy = Just Elem.OneTy
codeOf Ty.NatTy = Just Elem.NatTy
codeOf (Ty.PiTy a b) = Elem.PiTy <$> codeOf a <*> codeOf b
codeOf (Ty.SigmaTy a b) = Elem.SigmaTy <$> codeOf a <*> codeOf b
codeOf (EqTy l r t) = (Elem.EqTy l r) <$> codeOf t
codeOf (Quotient a r) = QuotTy <$> codeOf a <*> codeOf r
codeOf (El e) = Just e
codeOf _ = Nothing

||| Recursion budget for conditional matching (a lemma's unbound
||| ≡-typed parameter is discharged by a nested speculative equality).
spDepth : Nat
spDepth = 3

mutual
  ||| Γ ⊢ a ≐ b : A, speculatively: normalize+rewrite both sides, then
  ||| compare type-directed (η at Π/Σ, Prop at 𝟘/𝟙, witnesses at
  ||| quotients), by syntactic congruence descent, or against a whole
  ||| candidate equation (with bounded transitivity hops). No state
  ||| mutation; used before committing. `dep` bounds the search.
  spEqElem : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Bool
  spEqElem dep st cs ctx a b ty =
    let a' = rwNfElemWith st.sig cs.rw a
        b' = rwNfElemWith st.sig cs.rw b
        ty' = rwNfTyWith st.sig cs.rw ty in
    a' == b'
    || candMatch dep st cs ctx a' b' ty'
    || spEqStruct dep st cs ctx a' b' ty'
    || spCong dep st cs ctx a' b'
    || assumedMatchE st ctx a' b' (betaTy st.sig ty)

  spEqStruct : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Bool
  spEqStruct dep st cs ctx a b Ty.OneTy = True
  spEqStruct dep st cs ctx a b Ty.ZeroTy = True
  spEqStruct dep st cs ctx a b (Ty.PiTy dom cod) =
    -- Π-η: compare applied to the fresh variable — but ONLY when a side
    -- is a literal λ. Two neutrals gain nothing from η, and η-expanding
    -- them regenerates the very application spCong descends from — an
    -- infinite η/congruence loop.
    (isPiIntro a || isPiIntro b)
    && spEqElem dep st (extendCS cs) (ctx :< dom)
         (betaElem st.sig (PiApp (substElem a Wk) (CtxVar 0)))
         (betaElem st.sig (PiApp (substElem b Wk) (CtxVar 0)))
         cod
   where
    isPiIntro : Elem -> Bool
    isPiIntro (PiIntro _) = True
    isPiIntro _ = False
  spEqStruct dep st cs ctx a b (Ty.SigmaTy dom cod) =
    -- Σ-η, same guard: only when a side is a literal pair.
    (isPair a || isPair b)
    && spEqElem dep st cs ctx (betaElem st.sig (SigmaElim1 a)) (betaElem st.sig (SigmaElim1 b)) dom
    && spEqElem dep st cs ctx (betaElem st.sig (SigmaElim2 a)) (betaElem st.sig (SigmaElim2 b))
         (substTy cod (Ext Id (SigmaElim1 a)))
   where
    isPair : Elem -> Bool
    isPair (SigmaIntro _ _) = True
    isPair _ = False
  spEqStruct dep st cs ctx (Class x) (Class y) (Quotient dom rel) =
    spEqElem dep st cs ctx x y dom
    || (case rwNfTyWith st.sig cs.rw (substTy rel (Ext (Ext Id x) y)) of
          Ty.OneTy => True
          EqTy l r t => spEqElem dep st cs ctx l r t
          _ => False)
  spEqStruct _ _ _ _ _ _ _ = False

  assumedMatchE : ElabSt -> Ctx -> Elem -> Elem -> Ty -> Bool
  assumedMatchE st ctx a b ty =
    any (\(c, x, y, t) => c == ctx && t == ty && ((x == a && y == b) || (x == b && y == a)))
        st.assumedE

  ||| Syntactic congruence descent on same-headed (already normalized)
  ||| sides — the speculative mirror of the committing decomposition,
  ||| letting an inner mismatch reach the candidate store (e.g. a
  ||| commuted tail under an outer sum).
  spCong : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Bool
  spCong dep st cs ctx (NatIntro1 x) (NatIntro1 y) = spEqElem dep st cs ctx x y Ty.NatTy
  spCong dep st cs ctx (NatElim z s t) (NatElim z' s' t') =
    z == z' && s == s' && spEqElem dep st cs ctx t t' Ty.NatTy
  spCong dep st cs ctx (PiApp f x) (PiApp g y) =
    f == g && (case betaTy st.sig <$> inferNe st ctx f of
                 Just (Ty.PiTy dom _) => spEqElem dep st cs ctx x y dom
                 _ => False)
  spCong dep st cs ctx (SigmaElim1 u) (SigmaElim1 v) =
    case inferNe st ctx u of
      Just tyU => spEqElem dep st cs ctx u v tyU
      Nothing => False
  spCong dep st cs ctx (SigmaElim2 u) (SigmaElim2 v) =
    case inferNe st ctx u of
      Just tyU => spEqElem dep st cs ctx u v tyU
      Nothing => False
  spCong dep st cs ctx (QuotElim f q) (QuotElim g q') =
    f == g && (case inferNe st ctx q of
                 Just tyQ => spEqElem dep st cs ctx q q' tyQ
                 _ => False)
  spCong dep st cs ctx (Elem.PiTy a b) (Elem.PiTy a' b') =
    spEqElem dep st cs ctx a a' Ty.UniverseTy
    && spEqElem dep st (extendCS cs) (ctx :< El a') b b' Ty.UniverseTy
  spCong dep st cs ctx (Elem.SigmaTy a b) (Elem.SigmaTy a' b') =
    spEqElem dep st cs ctx a a' Ty.UniverseTy
    && spEqElem dep st (extendCS cs) (ctx :< El a') b b' Ty.UniverseTy
  spCong dep st cs ctx (QuotTy a r) (QuotTy a' r') =
    spEqElem dep st cs ctx a a' Ty.UniverseTy
    && spEqElem dep st (extendCS (extendCS cs)) (ctx :< El a' :< substTy (El a') Wk) r r' Ty.UniverseTy
  spCong dep st cs ctx (Elem.EqTy l r t) (Elem.EqTy l' r' t') =
    spEqElem dep st cs ctx t t' Ty.UniverseTy
    && spEqElem dep st cs ctx l l' (El t')
    && spEqElem dep st cs ctx r r' (El t')
  spCong _ _ _ _ _ _ = False

  ||| Whole-equation matching against candidates: a ≐ b discharges when
  ||| some candidate's lhs/rhs match a/b under one consistent
  ||| instantiation (either orientation), with every parameter either
  ||| bound by the match or — CONDITIONAL matching — carrying an ≡-type
  ||| (or 𝟙) whose instance discharges speculatively. Additionally, a
  ||| candidate that rewriting cannot apply (permutative / growing) may
  ||| be used as a depth-bounded transitivity HOP: rewrite one side
  ||| wholesale and recurse — e.g. middle-four exchange, a hypothesis,
  ||| middle-four exchange again.
  candMatch : Nat -> ElabSt -> CandSet -> Ctx -> Elem -> Elem -> Ty -> Bool
  candMatch Z _ _ _ _ _ _ = False
  candMatch (S dep) st cs ctx a b ty =
    any direct cs.all || any hop cs.hops
   where
    -- paramTys is outermost-first: param p's type is at index (k-1-p).
    paramTy : Cand -> Nat -> Maybe Ty
    paramTy c p = getAt (minus (minus c.params 1) p) c.paramTys

    condOk : Cand -> Bindings -> Nat -> Bool
    condOk c bs p =
      case lookup p bs of
        Just _ => True
        Nothing =>
          case (paramTy c p, condSub c.params p bs) of
            (Just tp, Just sigma) =>
              case rwNfTyWith st.sig cs.rw (substTy tp sigma) of
                Ty.OneTy => True
                -- side conditions get a FLAT budget (no nested hops or
                -- conditions): in practice they discharge directly
                -- against a hypothesis; a deeper budget multiplies the
                -- whole search tree
                EqTy l r t => spEqElem (min dep 1) st cs ctx l r t
                _ => False
            _ => False

    allCondsOk : Cand -> Bindings -> Bool
    allCondsOk c bs =
      c.params == 0 || all (condOk c bs) (reverse [0 .. minus c.params 1])

    oriented : Cand -> Elem -> Elem -> Bool
    oriented c x y =
      case matchElemP c.params 0 0 c.lhs x [] of
        Nothing => False
        Just bs => case matchElemP c.params 0 0 c.rhs y bs of
                     Nothing => False
                     Just bs' => allCondsOk c bs'

    direct : Cand -> Bool
    direct c = oriented c a b || oriented c b a

    -- Rewrite one whole side by a candidate and recurse with the
    -- budget decremented (a bounded transitivity step).
    hopWith : Cand -> Elem -> (Elem -> Bool) -> Bool
    hopWith c side k =
      case matchElemP c.params 0 0 c.lhs side [] of
        Nothing => False
        Just bs =>
          case instSub c.params 0 bs of
            Nothing => False
            Just sigma =>
              allCondsOk c bs
              && k (rwNfElemWith st.sig cs.rw (substElem c.rhs sigma))

    hop : Cand -> Bool
    hop c =
      hopWith c a (\a' => spEqElem dep st cs ctx a' b ty)
      || hopWith c b (\b' => spEqElem dep st cs ctx a b' ty)

  spEqTy : Nat -> ElabSt -> CandSet -> Ctx -> Ty -> Ty -> Bool
  spEqTy dep st cs ctx tyA tyB =
    let a = rwNfTyWith st.sig cs.rw tyA
        b = rwNfTyWith st.sig cs.rw tyB in
    go a b || assumedMatchT a b
   where
    go : Ty -> Ty -> Bool
    go a b =
      a == b
      || case (a, b) of
           (Ty.PiTy a0 b0, Ty.PiTy a1 b1) =>
             go a0 a1 && spEqTy dep st (extendCS cs) (ctx :< a1) b0 b1
           (Ty.SigmaTy a0 b0, Ty.SigmaTy a1 b1) =>
             go a0 a1 && spEqTy dep st (extendCS cs) (ctx :< a1) b0 b1
           (Ty.Quotient a0 r0, Ty.Quotient a1 r1) =>
             go a0 a1 && spEqTy dep st (extendCS (extendCS cs)) (ctx :< a1 :< substTy a1 Wk) r0 r1
           (EqTy l0 r0 t0, EqTy l1 r1 t1) =>
             spEqTy dep st cs ctx t0 t1 && spEqElem dep st cs ctx l0 l1 t1 && spEqElem dep st cs ctx r0 r1 t1
           (El x, El y) => spEqElem dep st cs ctx x y Ty.UniverseTy
           (El x, rigid) => case codeOf rigid of
                              Just c => spEqElem dep st cs ctx x c Ty.UniverseTy
                              Nothing => False
           (rigid, El y) => case codeOf rigid of
                              Just c => spEqElem dep st cs ctx c y Ty.UniverseTy
                              Nothing => False
           _ => False

    assumedMatchT : Ty -> Ty -> Bool
    assumedMatchT a b =
      any (\(c, x, y) => c == ctx && ((x == a && y == b) || (x == b && y == a)))
          st.assumedT

-- ===== Committing conversion (the ↓ judgements) =====

assume : Stmt -> String -> Maybe Stmt -> ElabM ()
assume stmt site comp = do
  st <- getSt
  case stmt of
    StElem ctx env a b ty => do
      let key = (ctx, rwNfElem st ctx a, rwNfElem st ctx b, betaTy st.sig ty)
      if assumedMatchE st (fst4 key) (snd4 key) (thd4 key) (fth4 key)
        then pure ()
        else modifySt $ \s =>
          { assumedE $= (key ::)
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
  convElem : Ctx -> NameEnv -> String -> Maybe Stmt -> Elem -> Elem -> Ty -> ElabM ()
  convElem ctx env site comp a b ty = do
    st <- getSt
    let cs = mkCandSet st ctx
    if spEqElem spDepth st cs ctx a b ty
      then pure ()
      else do
        let cur = StElem ctx env a b ty
        let comp' = comp <|> Just cur
        let a' = rwNfElem st ctx a
        let b' = rwNfElem st ctx b
        case (a', b', rwNfTy st ctx ty) of
          -- congruence decomposition — faithful (an equivalence) for
          -- the type formers and universe codes, per Foundation's
          -- injectivity rules; merely sufficient for class (quotients
          -- are not injective — the witness path is the faithful
          -- route) and for neutral-spine congruence
          (NatIntro1 x, NatIntro1 y, _) =>
            convElem ctx env site comp' x y Ty.NatTy
          (PiIntro f, PiIntro g, Ty.PiTy dom cod) =>
            convElem (ctx :< dom) (env :< "x") site comp' f g cod
          (SigmaIntro u v, SigmaIntro u' v', Ty.SigmaTy dom cod) => do
            convElem ctx env site comp' u u' dom
            convElem ctx env site comp' v v' (substTy cod (Ext Id u'))
          (Class x, Class y, Ty.Quotient dom rel) =>
            -- witness path: an Eq-shaped relation reduces the class
            -- equation to its underlying equation (class⁼ Refl after
            -- reflection); other shapes keep the composite.
            (do st' <- getSt
                case rwNfTy st' ctx (substTy rel (Ext (Ext Id x) y)) of
                  EqTy l r t => convElem ctx env site comp' l r t
                  _ => assume cur site comp)
          (Elem.PiTy x c, Elem.PiTy x' c', Ty.UniverseTy) => do
            convElem ctx env site comp' x x' Ty.UniverseTy
            convElem (ctx :< El x') (env :< "x") site comp' c c' Ty.UniverseTy
          (Elem.SigmaTy x c, Elem.SigmaTy x' c', Ty.UniverseTy) => do
            convElem ctx env site comp' x x' Ty.UniverseTy
            convElem (ctx :< El x') (env :< "x") site comp' c c' Ty.UniverseTy
          (QuotTy x r, QuotTy x' r', Ty.UniverseTy) => do
            convElem ctx env site comp' x x' Ty.UniverseTy
            convElem (ctx :< El x' :< substTy (El x') Wk) (env :< "x" :< "y") site comp' r r' Ty.UniverseTy
          (Elem.EqTy l r t, Elem.EqTy l' r' t', Ty.UniverseTy) => do
            convElem ctx env site comp' t t' Ty.UniverseTy
            convElem ctx env site comp' l l' (El t')
            convElem ctx env site comp' r r' (El t')
          (NatElim z s t0, NatElim z' s' t1, _) =>
            if z == z' && s == s'
              then convElem ctx env site comp' t0 t1 Ty.NatTy
              else assume cur site comp
          (PiApp f x, PiApp g y, _) =>
            if f == g
              then do st' <- getSt
                      case betaTy st'.sig <$> inferNe st' ctx f of
                        Just (Ty.PiTy dom _) => convElem ctx env site comp' x y dom
                        _ => assume cur site comp
              else assume cur site comp
          _ => assume cur site comp

  ||| Γ ⊢ A ≐ B type ↓
  convTy : Ctx -> NameEnv -> String -> Maybe Stmt -> Ty -> Ty -> ElabM ()
  convTy ctx env site comp tyA tyB = do
    st <- getSt
    let cs = mkCandSet st ctx
    if spEqTy spDepth st cs ctx tyA tyB
      then pure ()
      else do
        let cur = StTy ctx env tyA tyB
        let comp' = comp <|> Just cur
        case (rwNfTy st ctx tyA, rwNfTy st ctx tyB) of
          (Ty.PiTy a0 b0, Ty.PiTy a1 b1) => do
            convTy ctx env site comp' a0 a1
            convTy (ctx :< a1) (env :< "x") site comp' b0 b1
          (Ty.SigmaTy a0 b0, Ty.SigmaTy a1 b1) => do
            convTy ctx env site comp' a0 a1
            convTy (ctx :< a1) (env :< "x") site comp' b0 b1
          (Ty.Quotient a0 r0, Ty.Quotient a1 r1) => do
            convTy ctx env site comp' a0 a1
            convTy (ctx :< a1 :< substTy a1 Wk) (env :< "x" :< "y") site comp' r0 r1
          (EqTy l0 r0 t0, EqTy l1 r1 t1) => do
            convTy ctx env site comp' t0 t1
            convElem ctx env site comp' l0 l1 t1
            convElem ctx env site comp' r0 r1 t1
          (El x, El y) => convElem ctx env site comp' x y Ty.UniverseTy
          (El x, rigid) => case codeOf rigid of
                             Just c => convElem ctx env site comp' x c Ty.UniverseTy
                             Nothing => assume cur site comp
          (rigid, El y) => case codeOf rigid of
                             Just c => convElem ctx env site comp' c y Ty.UniverseTy
                             Nothing => assume cur site comp
          _ => assume cur site comp

-- ===== Bidirectional elaboration =====

structuralHint : String
structuralHint = " (ascribe the term: `(t : T)`)"

||| Expose a type's Π/Σ/quotient head: as written if already rigid,
||| else by normalization.
preferPi : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty)
preferPi st ctx (Ty.PiTy a b) = Just (a, b)
preferPi st ctx ty = case rwNfTy st ctx ty of
                       Ty.PiTy a b => Just (a, b)
                       _ => Nothing

preferSigma : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty)
preferSigma st ctx (Ty.SigmaTy a b) = Just (a, b)
preferSigma st ctx ty = case rwNfTy st ctx ty of
                          Ty.SigmaTy a b => Just (a, b)
                          _ => Nothing

preferQuot : ElabSt -> Ctx -> Ty -> Maybe (Ty, Ty)
preferQuot st ctx (Ty.Quotient a r) = Just (a, r)
preferQuot st ctx ty = case rwNfTy st ctx ty of
                         Ty.Quotient a r => Just (a, r)
                         _ => Nothing

mutual
  export
  elabTy : Ctx -> NameEnv -> String -> STy -> ElabM Ty
  elabTy ctx env site STyZero = pure Ty.ZeroTy
  elabTy ctx env site STyOne = pure Ty.OneTy
  elabTy ctx env site STyNat = pure Ty.NatTy
  elabTy ctx env site STyUniv = pure Ty.UniverseTy
  elabTy ctx env site (STySig x es) = do
    st <- getSt
    case sigLookup x st.sig of
      Just (SigTyDef delta _ _) => do
        es' <- checkSubst ctx env site es delta
        pure (Ty.SigVar x es')
      Just (SigDef _ _ _ _) => throw "\{site}: '\{x}' is a term definition, used as a type"
      Nothing => throw "\{site}: unknown signature name '\{x}'"
  elabTy ctx env site (STyPi x a b) = do
    a' <- elabTy ctx env site a
    b' <- elabTy (ctx :< a') (env :< x) site b
    pure (Ty.PiTy a' b')
  elabTy ctx env site (STySigma x a b) = do
    a' <- elabTy ctx env site a
    b' <- elabTy (ctx :< a') (env :< x) site b
    pure (Ty.SigmaTy a' b')
  elabTy ctx env site (STyQuot a nx ny r) = do
    a' <- elabTy ctx env site a
    r' <- elabTy (ctx :< a' :< substTy a' Wk) (env :< nx :< ny) site r
    pure (Ty.Quotient a' r')
  elabTy ctx env site (STyEq l r t) = do
    t' <- elabTy ctx env site t
    l' <- checkElem ctx env site l t'
    r' <- checkElem ctx env site r t'
    pure (EqTy l' r' t')
  elabTy ctx env site (STyEl e) = do
    e' <- checkElem ctx env site e Ty.UniverseTy
    pure (El e')

  checkSubst : Ctx -> NameEnv -> String -> List SElem -> Ctx -> ElabM SubNorm
  checkSubst ctx env site es delta = go (reverse es) delta
   where
    -- es is given left-to-right (outermost first); delta is a snoc-list.
    go : List SElem -> Ctx -> ElabM SubNorm
    go [] [<] = pure [<]
    go (e :: rest) (d :< ty) = do
      es' <- go rest d
      e' <- checkElem ctx env site e (substTy ty (embed es'))
      pure (es' :< e')
    go _ _ = throw "\{site}: substitution length does not match the definition's telescope"

  export
  inferElem : Ctx -> NameEnv -> String -> SElem -> ElabM (Elem, Ty)
  inferElem ctx env site (SVar n i) =
    case ctxLookup ctx i of
      Just ty => pure (CtxVar i, ty)
      Nothing => throw "\{site}: variable index out of bounds"
  inferElem ctx env site (SSig x es) = do
    st <- getSt
    case sigLookup x st.sig of
      Just (SigDef delta _ _ ty) => do
        es' <- checkSubst ctx env site es delta
        pure (SigVar x es', substTy ty (embed es'))
      Just (SigTyDef _ _ _) => throw "\{site}: '\{x}' is a type definition, used as a term"
      Nothing => throw "\{site}: unknown signature name '\{x}'"
  inferElem ctx env site SUnitI = pure (OneIntro, Ty.OneTy)
  inferElem ctx env site SZeroN = pure (NatIntro0, Ty.NatTy)
  inferElem ctx env site (SSuc t) = do
    t' <- checkElem ctx env site t Ty.NatTy
    pure (NatIntro1 t', Ty.NatTy)
  inferElem ctx env site (SApp f e) = do
    (f', fTy) <- inferElem ctx env site f
    st <- getSt
    case rwNfTy st ctx fTy of
      Ty.PiTy a b => do
        e' <- checkElem ctx env site e a
        pure (PiApp f' e', substTy b (Ext Id e'))
      _ => throw "\{site}: cannot apply a term of non-Π type\{structuralHint}"
  inferElem ctx env site (SProj1 t) = do
    (t', tTy) <- inferElem ctx env site t
    st <- getSt
    case rwNfTy st ctx tTy of
      Ty.SigmaTy a b => pure (SigmaElim1 t', a)
      _ => throw "\{site}: cannot project from a term of non-⨯ type\{structuralHint}"
  inferElem ctx env site (SProj2 t) = do
    (t', tTy) <- inferElem ctx env site t
    st <- getSt
    case rwNfTy st ctx tTy of
      Ty.SigmaTy a b => pure (SigmaElim2 t', substTy b (Ext Id (SigmaElim1 t')))
      _ => throw "\{site}: cannot project from a term of non-⨯ type\{structuralHint}"
  inferElem ctx env site (SAnn t ty) = do
    ty' <- elabTy ctx env site ty
    t' <- checkElem ctx env site t ty'
    pure (t', ty')
  inferElem ctx env site (SNatElim n mot z n2 ih s t) = do
    motTy <- elabTy (ctx :< Ty.NatTy) (env :< n) site mot
    z' <- checkElem ctx env site z (substTy motTy (Ext Id NatIntro0))
    s' <- checkElem (ctx :< Ty.NatTy :< motTy) (env :< n2 :< ih) site s
            (substTy motTy (Chain (Ext Wk (NatIntro1 (CtxVar 0))) Wk))
    t' <- checkElem ctx env site t Ty.NatTy
    pure (NatElim z' s' t', substTy motTy (Ext Id t'))
  inferElem ctx env site (SQuotElim zn mot an f q) = do
    (q', qTy) <- inferElem ctx env site q
    st <- getSt
    case preferQuot st ctx qTy of
      Just (a, r) => do
        motTy <- elabTy (ctx :< Ty.Quotient a r) (env :< zn) site mot
        f' <- checkElem (ctx :< a) (env :< an) site f
                (substTy motTy (Ext Wk (Class (CtxVar 0))))
        -- well-definedness: f respects R (Foundation's f⁼ premise)
        let wk3 = Chain Wk (Chain Wk Wk)
        convElem (ctx :< a :< substTy a Wk :< r) (env :< an :< (an ++ "'") :< "r")
          "\{site}: well-definedness of quot-elim case" Nothing
          (substElem f' (Ext wk3 (CtxVar 2)))
          (substElem f' (Ext wk3 (CtxVar 1)))
          (substTy motTy (Ext wk3 (Class (CtxVar 2))))
        pure (QuotElim f' q', substTy motTy (Ext Id q'))
      Nothing => throw "\{site}: quot-elim scrutinee has non-quotient type\{structuralHint}"
  inferElem ctx env site SZeroC = pure (Elem.ZeroTy, Ty.UniverseTy)
  inferElem ctx env site SOneC = pure (Elem.OneTy, Ty.UniverseTy)
  inferElem ctx env site SNatC = pure (Elem.NatTy, Ty.UniverseTy)
  inferElem ctx env site (SPiC x a b) = do
    a' <- checkElem ctx env site a Ty.UniverseTy
    b' <- checkElem (ctx :< El a') (env :< x) site b Ty.UniverseTy
    pure (Elem.PiTy a' b', Ty.UniverseTy)
  inferElem ctx env site (SSigmaC x a b) = do
    a' <- checkElem ctx env site a Ty.UniverseTy
    b' <- checkElem (ctx :< El a') (env :< x) site b Ty.UniverseTy
    pure (Elem.SigmaTy a' b', Ty.UniverseTy)
  inferElem ctx env site (SQuotC a nx ny r) = do
    a' <- checkElem ctx env site a Ty.UniverseTy
    r' <- checkElem (ctx :< El a' :< substTy (El a') Wk) (env :< nx :< ny) site r Ty.UniverseTy
    pure (QuotTy a' r', Ty.UniverseTy)
  inferElem ctx env site (SEqC l r t) = do
    t' <- checkElem ctx env site t Ty.UniverseTy
    l' <- checkElem ctx env site l (El t')
    r' <- checkElem ctx env site r (El t')
    pure (Elem.EqTy l' r' t', Ty.UniverseTy)
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
  checkElem : Ctx -> NameEnv -> String -> SElem -> Ty -> ElabM Elem
  -- Intro forms prefer the expected type's syntactic head (keeps
  -- signature references folded in contexts and reports); normalization
  -- is the fallback that exposes a head hidden under definitions.
  checkElem ctx env site (SLam x t) ty = do
    st <- getSt
    case preferPi st ctx ty of
      Just (a, b) => do
        t' <- checkElem (ctx :< a) (env :< x) site t b
        pure (PiIntro t')
      Nothing => throw "\{site}: λ checked against a non-Π type\{structuralHint}"
  checkElem ctx env site (SPair u v) ty = do
    st <- getSt
    case preferSigma st ctx ty of
      Just (a, b) => do
        u' <- checkElem ctx env site u a
        v' <- checkElem ctx env site v (substTy b (Ext Id u'))
        pure (SigmaIntro u' v')
      Nothing => throw "\{site}: pair checked against a non-⨯ type\{structuralHint}"
  checkElem ctx env site SRefl ty = do
    st <- getSt
    -- Prefer the type as written (readable obligation statements); fall
    -- back to its normal form when the ≡ only appears after unfolding.
    case ty of
      EqTy l r t => do
        convElem ctx env "\{site}: checking Refl" Nothing l r t
        pure Refl
      _ => case rwNfTy st ctx ty of
             EqTy l r t => do
               convElem ctx env "\{site}: checking Refl" Nothing l r t
               pure Refl
             _ => throw "\{site}: Refl checked against a non-≡ type\{structuralHint}"
  checkElem ctx env site (SClass a) ty = do
    st <- getSt
    case preferQuot st ctx ty of
      Just (dom, rel) => do
        a' <- checkElem ctx env site a dom
        pure (Class a')
      Nothing => throw "\{site}: class checked against a non-quotient type\{structuralHint}"
  checkElem ctx env site (SZeroElim t) ty = do
    t' <- checkElem ctx env site t Ty.ZeroTy
    pure (ZeroElim t')
  checkElem ctx env site t ty = do
    (t', inferred) <- inferElem ctx env site t
    convTy ctx env "\{site}: inferred vs expected type" Nothing inferred ty
    pure t'

-- ===== Items =====

||| Register a just-accepted definition's equation (if its type peels to
||| an ≡-type) as a rewrite candidate: the WHOLE context (telescope +
||| peeled Πs) is parametric, so the lemma applies in any context.
addLemma : String -> Ctx -> Ty -> ElabM ()
addLemma name delta ty = do
  st <- getSt
  let (delta', peeled) = peelPis delta (betaTy st.sig ty)
  case peeled of
    EqTy l r t =>
      -- Sides normalized against the store as of this point, so later
      -- queries (already canonicalized by earlier lemmas) still match;
      -- closed under component decomposition (closeCand).
      let lemmaRw = ordered st.lemmas in
      modifySt $ { lemmas $= (closeCand (MkCand name (length delta') (toList delta')
                                                (rwNfElemWith st.sig lemmaRw l)
                                                (rwNfElemWith st.sig lemmaRw r)) ++) }
    _ => pure ()

elabTelescope : Ctx -> NameEnv -> String -> List (String, STy) -> ElabM (Ctx, NameEnv)
elabTelescope ctx env site [] = pure (ctx, env)
elabTelescope ctx env site ((x, ty) :: rest) = do
  ty' <- elabTy ctx env site ty
  elabTelescope (ctx :< ty') (env :< x) site rest

export
elabItem : SItem -> ElabM String
elabItem (SDef x tel ty body) = do
  st <- getSt
  case sigLookup x st.sig of
    Just _ => throw "def \{x}: duplicate signature name"
    Nothing => pure ()
  (ctx, env) <- elabTelescope [<] [<] "def \{x}" tel
  ty' <- elabTy ctx env "def \{x}" ty
  body' <- checkElem ctx env "def \{x}" body ty'
  modifySt $ { sig $= (:< SigDef ctx x body' ty') }
  addLemma x ctx ty'
  pure "defined \{x}"
elabItem (STypeDef x tel ty) = do
  st <- getSt
  case sigLookup x st.sig of
    Just _ => throw "type \{x}: duplicate signature name"
    Nothing => pure ()
  (ctx, env) <- elabTelescope [<] [<] "type \{x}" tel
  ty' <- elabTy ctx env "type \{x}" ty
  modifySt $ { sig $= (:< SigTyDef ctx x ty') }
  pure "defined type \{x}"

-- ===== Report =====

prettyTelescope : Ctx -> NameEnv -> String
prettyTelescope ctx env = go (toList ctx) (toList env)
 where
  -- print left-to-right; each entry's type prints under the env prefix
  go' : SnocList String -> List Ty -> List String -> List String
  go' pfx [] _ = []
  go' pfx (ty :: tys) (n :: ns) =
    "(\{n} : \{prettyTyN pfx ty})" :: go' (pfx :< n) tys ns
  go' pfx (ty :: tys) [] =
    "(_ : \{prettyTyN pfx ty})" :: go' (pfx :< "_") tys []

  go : List Ty -> List String -> String
  go tys ns = joinBy " " (go' [<] tys ns)

prettyStmt : Stmt -> String
prettyStmt (StElem ctx env a b ty) =
  let tele = prettyTelescope ctx env in
  (if tele == "" then "" else tele ++ " ") ++
  "⊢ \{prettyElemN env a} ≐ \{prettyElemN env b} : \{prettyTyN env ty}"
prettyStmt (StTy ctx env a b) =
  let tele = prettyTelescope ctx env in
  (if tele == "" then "" else tele ++ " ") ++
  "⊢ \{prettyTyN env a} ≐ \{prettyTyN env b} type"

prettyObligation : Nat -> Obligation -> String
prettyObligation i obl =
  "  [\{show (S i)}] \{prettyStmt obl.stmt}\n" ++
  "      at: \{obl.site}" ++
  (case obl.composite of
     Nothing => ""
     Just c => "\n      from composite: \{prettyStmt c}")

||| Elaborate a whole surface file; the returned string is the complete
||| report (per-item echoes, then acceptance or the obligation list).
export
elabFile : String -> String
elabFile content =
  case runSurfaceParser parseSFile content of
    Left err => "Parse error: \{err}"
    Right items => go initSt items []
 where
  finish : ElabSt -> List String -> String
  finish st echoes =
    let oblList = toList st.obls in
    joinBy "\n" echoes ++ "\n" ++
    (case oblList of
       [] => "Accepted."
       os => "open obligations (\{show (length os)}):\n" ++
             joinBy "\n" (zipWith prettyObligation [0 .. minus (length os) 1] os))

  go : ElabSt -> List SItem -> List String -> String
  go st [] echoes = finish st echoes
  go st (item :: rest) echoes =
    case runElabM (elabItem item) st of
      Left err => joinBy "\n" (echoes ++ ["Error: \{err}"])
      Right (st', echo) => go st' rest (echoes ++ [echo])
