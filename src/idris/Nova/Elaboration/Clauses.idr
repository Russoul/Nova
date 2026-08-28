module Nova.Elaboration.Clauses

-- The clausal def ITEM MACRO (docs/NovaElaboration.txt, "Defining
-- equations"): fragment analysis and expansion into a batch of
-- ordinary surface items, elaborated by the ordinary item pipeline
-- in Nova.Elaboration — which is where discharge, obligations,
-- certificates, lemma registration and the report all happen. No
-- Foundation rule and no kernel capability is involved.
--
-- The expansion names the three pieces of the contractibility
-- contract:
--   * EXISTENCE — def f ≔ ρ: a synthesized eliminator body (the
--     structural fragment), the user's witness, or a declaration;
--   * one Π-CLOSED EQUATION LEMMA per clause, body λ…. ⋆ —
--     discharged by pure computation in the fragment, an ordinary
--     obligation otherwise;
--   * UNIQUENESS — nEta, stated POINTWISE, its body the eliminator
--     at the equality motive whenever the clauses are
--     fragment-shaped (the A5 route, docs/NovaKernel.txt: η rules
--     have no kernel finals and need none), a bare λ…. ⋆ otherwise.
--
-- Everything below is pure surface-level term surgery. The generated
-- items reference each other by Σ-name, so batch ORDER is semantic:
-- the definition first, the clause lemmas next (their ⋆-bodies
-- unfold f), the uniqueness lemma last (its ⋆-cases rewrite by the
-- clause lemmas — never by unfolding ρ, which keeps eta synthesis
-- independent of where the witness came from).

import Data.List
import Data.Maybe
import Data.SnocList
import Data.String

import Me.Russoul.Text.Range

import Nova.Kernel.Syntax

import Nova.Elaboration.Named
import Nova.Elaboration.Surface

%default covering

-- ===== Surface de Bruijn surgery =====
--
-- The expansion rebuilds user subterms (column types, clause RHSs)
-- under binder stacks the user never wrote: lemma telescopes and
-- eliminator motives/cases. All of it is index remapping over the
-- indexed surface AST; signature references are names and pass
-- through untouched (except where a traversal deliberately targets
-- them — replaceSig below).

mutual
  mapRefsE : (onVar : Nat -> Maybe Range -> String -> Nat -> SElem) ->
             (onSig : Nat -> Maybe Range -> String -> SElem) ->
             Nat -> SElem -> SElem
  mapRefsE f g d (SPos r e) = SPos r (mapRefsE f g d e)
  mapRefsE f g d e@(SHole _ _) = e
  mapRefsE f g d (SVar r n i) = if i < d then SVar r n i else f d r n i
  mapRefsE f g d (SSig r x) = g d r x
  mapRefsE f g d SUnitI = SUnitI
  mapRefsE f g d SZeroN = SZeroN
  mapRefsE f g d (SSuc t) = SSuc (mapRefsE f g d t)
  mapRefsE f g d (SLam x t) = SLam x (mapRefsE f g (S d) t)
  mapRefsE f g d (SLet x e b) = SLet x (mapRefsE f g d e) (mapRefsE f g (S (S d)) b)
  mapRefsE f g d (SApp h e) = SApp (mapRefsE f g d h) (mapRefsE f g d e)
  mapRefsE f g d (SPair a b) = SPair (mapRefsE f g d a) (mapRefsE f g d b)
  mapRefsE f g d (SProj1 t) = SProj1 (mapRefsE f g d t)
  mapRefsE f g d (SProj2 t) = SProj2 (mapRefsE f g d t)
  mapRefsE f g d SZeroC = SZeroC
  mapRefsE f g d SOneC = SOneC
  mapRefsE f g d SNatC = SNatC
  mapRefsE f g d (SPiC x a b) = SPiC x (mapRefsE f g d a) (mapRefsE f g (S d) b)
  mapRefsE f g d (SSigmaC x a b) = SSigmaC x (mapRefsE f g d a) (mapRefsE f g (S d) b)
  mapRefsE f g d (SSumC a b) = SSumC (mapRefsE f g d a) (mapRefsE f g d b)
  mapRefsE f g d (SQuotC a x y r) = SQuotC (mapRefsE f g d a) x y (mapRefsE f g (S (S d)) r)
  mapRefsE f g d (SEqC rng l r t) = SEqC rng (mapRefsE f g d l) (mapRefsE f g d r) (map (mapRefsTy f g d) t)
  mapRefsE f g d (SZeroElim t) = SZeroElim (mapRefsE f g d t)
  mapRefsE f g d (SNatElim mot z n2 ih s t) =
    SNatElim (map (\(n, m) => (n, mapRefsTy f g (S d) m)) mot) (mapRefsE f g d z) n2 ih
             (mapRefsE f g (S (S d)) s) (mapRefsE f g d t)
  mapRefsE f g d (SInj1 t) = SInj1 (mapRefsE f g d t)
  mapRefsE f g d (SInj2 t) = SInj2 (mapRefsE f g d t)
  mapRefsE f g d (SSumElim mot a l b r t) =
    SSumElim (map (\(z, m) => (z, mapRefsTy f g (S d) m)) mot) a (mapRefsE f g (S d) l) b
             (mapRefsE f g (S d) r) (mapRefsE f g d t)
  mapRefsE f g d (SClass t) = SClass (mapRefsE f g d t)
  mapRefsE f g d (SQuotElim mot a h q) =
    SQuotElim (map (\(z, m) => (z, mapRefsTy f g (S d) m)) mot) a (mapRefsE f g (S d) h) (mapRefsE f g d q)
  mapRefsE f g d (SNuC p) = SNuC (mapRefsP f g d p)
  mapRefsE f g d (SOut e) = SOut (mapRefsE f g d e)
  mapRefsE f g d (SCorec x a h u) =
    SCorec x (mapRefsE f g d a) (mapRefsE f g (S d) h) (mapRefsE f g d u)
  mapRefsE f g d (SCoind nx ny r pw mx my mh q) =
    SCoind nx ny (mapRefsE f g (S (S d)) r) (mapRefsE f g d pw) mx my mh
           (mapRefsE f g (S (S (S d))) q)
  mapRefsE f g d (SSquash t) = SSquash (mapRefsTy f g d t)
  mapRefsE f g d e@(SStar _) = e
  -- using-names are Σ references outside the term grammar (never the
  -- item's own recursive occurrence), so they pass through unchanged
  mapRefsE f g d e@(SStarUsing _ _) = e
  mapRefsE f g d (SStarWit e) = SStarWit (mapRefsE f g d e)
  mapRefsE f g d (SSquashElim e x body) =
    SSquashElim (mapRefsE f g d e) x (mapRefsE f g (S d) body)
  mapRefsE f g d (SChain x ls) =
    SChain (mapRefsE f g d x)
           (map (\(j, y) => (mapRefsE f g d j, mapRefsE f g d y)) ls)
  mapRefsE f g d (SAnn e ty) = SAnn (mapRefsE f g d e) (mapRefsTy f g d ty)
  mapRefsE f g d (SImpArg e) = SImpArg (mapRefsE f g d e)
  mapRefsE f g d (SNoIns e) = SNoIns (mapRefsE f g d e)
  mapRefsE f g d e@(SBlank _) = e

  mapRefsTy : (onVar : Nat -> Maybe Range -> String -> Nat -> SElem) ->
              (onSig : Nat -> Maybe Range -> String -> SElem) ->
              Nat -> STy -> STy
  mapRefsTy f g d (STyPos r t) = STyPos r (mapRefsTy f g d t)
  mapRefsTy f g d STyZero = STyZero
  mapRefsTy f g d STyOne = STyOne
  mapRefsTy f g d STyNat = STyNat
  mapRefsTy f g d STyUniv = STyUniv
  mapRefsTy f g d (STySig x) = STySig x
  mapRefsTy f g d (STyPi x a b) = STyPi x (mapRefsTy f g d a) (mapRefsTy f g (S d) b)
  mapRefsTy f g d (STyImpPi x a b) = STyImpPi x (mapRefsTy f g d a) (mapRefsTy f g (S d) b)
  mapRefsTy f g d (STySigma x a b) = STySigma x (mapRefsTy f g d a) (mapRefsTy f g (S d) b)
  mapRefsTy f g d (STySum a b) = STySum (mapRefsTy f g d a) (mapRefsTy f g d b)
  mapRefsTy f g d (STyQuot a x y r) = STyQuot (mapRefsTy f g d a) x y (mapRefsE f g (S (S d)) r)
  mapRefsTy f g d (STyEq rng l r t) = STyEq rng (mapRefsE f g d l) (mapRefsE f g d r) (map (mapRefsTy f g d) t)
  mapRefsTy f g d (STyEl e) = STyEl (mapRefsE f g d e)
  mapRefsTy f g d STyProp = STyProp
  mapRefsTy f g d (STyNu p) = STyNu (mapRefsP f g d p)

  mapRefsP : (onVar : Nat -> Maybe Range -> String -> Nat -> SElem) ->
             (onSig : Nat -> Maybe Range -> String -> SElem) ->
             Nat -> SPoly -> SPoly
  mapRefsP f g d SPHole = SPHole
  mapRefsP f g d (SPConst a) = SPConst (mapRefsE f g d a)
  mapRefsP f g d (SPProd p q) = SPProd (mapRefsP f g d p) (mapRefsP f g d q)
  mapRefsP f g d (SPSum p q) = SPSum (mapRefsP f g d p) (mapRefsP f g d q)
  mapRefsP f g d (SPSigma x a p) = SPSigma x (mapRefsE f g d a) (mapRefsP f g (S d) p)
  mapRefsP f g d (SPPi x a p) = SPPi x (mapRefsE f g d a) (mapRefsP f g (S d) p)

keepSig : Nat -> Maybe Range -> String -> SElem
keepSig _ r x = SSig r x

||| Add `amt` to every free variable whose top-level index is ≥ cutoff.
shiftE : (cutoff, amt : Nat) -> SElem -> SElem
shiftE c a = mapRefsE (\d, r, n, i => if i >= d + c then SVar r n (i + a) else SVar r n i) keepSig 0

shiftTy : (cutoff, amt : Nat) -> STy -> STy
shiftTy c a = mapRefsTy (\d, r, n, i => if i >= d + c then SVar r n (i + a) else SVar r n i) keepSig 0

||| Remap free variables by their top-level index, keeping display data.
remapIdxE : (Nat -> Nat) -> SElem -> SElem
remapIdxE f = mapRefsE (\d, r, n, i => SVar r n (d + f (minus i d))) keepSig 0

||| Substitute every free variable by a term over the target context
||| (σ receives the top-level index; its result is weakened under the
||| binders crossed).
remapFreeE : (Nat -> SElem) -> SElem -> SElem
remapFreeE sig = mapRefsE (\d, r, n, i => shiftE 0 d (sig (minus i d))) keepSig 0

remapFreeTy : (Nat -> SElem) -> STy -> STy
remapFreeTy sig = mapRefsTy (\d, r, n, i => shiftE 0 d (sig (minus i d))) keepSig 0

||| Replace every reference to the signature name `f` by the variable
||| whose top-level index is `base` (the uniqueness lemma states its
||| hypotheses about the candidate g).
replaceSigTy : (f : String) -> (gname : String) -> (base : Nat) -> STy -> STy
replaceSigTy f gname base =
  mapRefsTy (\_, r, n, i => SVar r n i)
            (\d, r, x => if x == f then SVar r gname (base + d) else SSig r x) 0

-- ===== Occurrence check =====

mutual
  occursE : String -> SElem -> Bool
  occursE f (SPos _ e) = occursE f e
  occursE f (SHole _ _) = False
  occursE f (SVar _ _ _) = False
  occursE f (SSig _ x) = x == f
  occursE f SUnitI = False
  occursE f SZeroN = False
  occursE f (SSuc t) = occursE f t
  occursE f (SLam _ t) = occursE f t
  occursE f (SLet _ e b) = occursE f e || occursE f b
  occursE f (SApp g e) = occursE f g || occursE f e
  occursE f (SPair a b) = occursE f a || occursE f b
  occursE f (SProj1 t) = occursE f t
  occursE f (SProj2 t) = occursE f t
  occursE f SZeroC = False
  occursE f SOneC = False
  occursE f SNatC = False
  occursE f (SPiC _ a b) = occursE f a || occursE f b
  occursE f (SSigmaC _ a b) = occursE f a || occursE f b
  occursE f (SSumC a b) = occursE f a || occursE f b
  occursE f (SQuotC a _ _ r) = occursE f a || occursE f r
  occursE f (SEqC _ l r t) = occursE f l || occursE f r || maybe False (occursTy f) t
  occursE f (SZeroElim t) = occursE f t
  occursE f (SNatElim mot z _ _ s t) =
    maybe False (occursTy f . snd) mot || occursE f z || occursE f s || occursE f t
  occursE f (SInj1 t) = occursE f t
  occursE f (SInj2 t) = occursE f t
  occursE f (SSumElim mot _ l _ r t) =
    maybe False (occursTy f . snd) mot || occursE f l || occursE f r || occursE f t
  occursE f (SClass t) = occursE f t
  occursE f (SQuotElim mot _ g q) = maybe False (occursTy f . snd) mot || occursE f g || occursE f q
  occursE f (SNuC p) = occursP f p
  occursE f (SOut e) = occursE f e
  occursE f (SCorec _ a g u) = occursE f a || occursE f g || occursE f u
  occursE f (SCoind _ _ r pw _ _ _ q) = occursE f r || occursE f pw || occursE f q
  occursE f (SSquash t) = occursTy f t
  occursE f (SStar _) = False
  occursE f (SStarUsing _ _) = False
  occursE f (SStarWit e) = occursE f e
  occursE f (SSquashElim e _ body) = occursE f e || occursE f body
  occursE f (SChain x ls) =
    occursE f x || any (\(j, y) => occursE f j || occursE f y) ls
  occursE f (SAnn e ty) = occursE f e || occursTy f ty
  occursE f (SImpArg e) = occursE f e
  occursE f (SNoIns e) = occursE f e
  occursE f (SBlank _) = False

  occursTy : String -> STy -> Bool
  occursTy f (STyPos _ t) = occursTy f t
  occursTy f STyZero = False
  occursTy f STyOne = False
  occursTy f STyNat = False
  occursTy f STyUniv = False
  occursTy f (STySig x) = x == f
  occursTy f (STyPi _ a b) = occursTy f a || occursTy f b
  occursTy f (STyImpPi _ a b) = occursTy f a || occursTy f b
  occursTy f (STySigma _ a b) = occursTy f a || occursTy f b
  occursTy f (STySum a b) = occursTy f a || occursTy f b
  occursTy f (STyQuot a _ _ r) = occursTy f a || occursE f r
  occursTy f (STyEq _ l r t) = occursE f l || occursE f r || maybe False (occursTy f) t
  occursTy f (STyEl e) = occursE f e
  occursTy f STyProp = False
  occursTy f (STyNu p) = occursP f p

  occursP : String -> SPoly -> Bool
  occursP f SPHole = False
  occursP f (SPConst a) = occursE f a
  occursP f (SPProd p q) = occursP f p || occursP f q
  occursP f (SPSum p q) = occursP f p || occursP f q
  occursP f (SPSigma _ a p) = occursE f a || occursP f p
  occursP f (SPPi _ a p) = occursE f a || occursP f p

-- ===== Spine rewriting =====

||| Application spine, head-first.
unwind : SElem -> (SElem, List SElem)
unwind e = case unPos e of
  SApp g a => let (h, as) = unwind g in (h, as ++ [a])
  h => (h, [])

spine : SElem -> List SElem -> SElem
spine = foldl SApp

mutual
  ||| Rewrite application SPINES: at each spine (head, arguments) at
  ||| binder depth d the callback may replace the whole spine — the
  ||| replacement is NOT revisited, so a callback wanting its
  ||| arguments rewritten recurses itself — and a declining callback
  ||| lets the walk recurse into the head and the arguments. Bare
  ||| heads are offered with an empty argument list.
  mapSpinesE : (repl : Nat -> SElem -> List SElem -> Maybe SElem) -> Nat -> SElem -> SElem
  mapSpinesE repl d (SPos r e) = SPos r (mapSpinesE repl d e)
  mapSpinesE repl d e@(SHole _ _) = e
  mapSpinesE repl d e@(SApp _ _) =
    let (h, args) = unwind e in
    case repl d h args of
      Just r => r
      Nothing => spine (mapSpinesE repl d h) (map (mapSpinesE repl d) args)
  mapSpinesE repl d e@(SVar _ _ _) = fromMaybe e (repl d e [])
  mapSpinesE repl d e@(SSig _ _) = fromMaybe e (repl d e [])
  mapSpinesE repl d SUnitI = SUnitI
  mapSpinesE repl d SZeroN = SZeroN
  mapSpinesE repl d (SSuc t) = SSuc (mapSpinesE repl d t)
  mapSpinesE repl d (SLam x t) = SLam x (mapSpinesE repl (S d) t)
  mapSpinesE repl d (SLet x e b) = SLet x (mapSpinesE repl d e) (mapSpinesE repl (S (S d)) b)
  mapSpinesE repl d (SPair a b) = SPair (mapSpinesE repl d a) (mapSpinesE repl d b)
  mapSpinesE repl d (SProj1 t) = SProj1 (mapSpinesE repl d t)
  mapSpinesE repl d (SProj2 t) = SProj2 (mapSpinesE repl d t)
  mapSpinesE repl d SZeroC = SZeroC
  mapSpinesE repl d SOneC = SOneC
  mapSpinesE repl d SNatC = SNatC
  mapSpinesE repl d (SPiC x a b) = SPiC x (mapSpinesE repl d a) (mapSpinesE repl (S d) b)
  mapSpinesE repl d (SSigmaC x a b) = SSigmaC x (mapSpinesE repl d a) (mapSpinesE repl (S d) b)
  mapSpinesE repl d (SSumC a b) = SSumC (mapSpinesE repl d a) (mapSpinesE repl d b)
  mapSpinesE repl d (SQuotC a x y r) = SQuotC (mapSpinesE repl d a) x y (mapSpinesE repl (S (S d)) r)
  mapSpinesE repl d (SEqC rng l r t) =
    SEqC rng (mapSpinesE repl d l) (mapSpinesE repl d r) (map (mapSpinesT repl d) t)
  mapSpinesE repl d (SZeroElim t) = SZeroElim (mapSpinesE repl d t)
  mapSpinesE repl d (SNatElim mot z n2 ih s t) =
    SNatElim (map (\(n, m) => (n, mapSpinesT repl (S d) m)) mot) (mapSpinesE repl d z) n2 ih
             (mapSpinesE repl (S (S d)) s) (mapSpinesE repl d t)
  mapSpinesE repl d (SInj1 t) = SInj1 (mapSpinesE repl d t)
  mapSpinesE repl d (SInj2 t) = SInj2 (mapSpinesE repl d t)
  mapSpinesE repl d (SSumElim mot a l b r t) =
    SSumElim (map (\(z, m) => (z, mapSpinesT repl (S d) m)) mot) a (mapSpinesE repl (S d) l) b
             (mapSpinesE repl (S d) r) (mapSpinesE repl d t)
  mapSpinesE repl d (SClass t) = SClass (mapSpinesE repl d t)
  mapSpinesE repl d (SQuotElim mot a f q) =
    SQuotElim (map (\(z, m) => (z, mapSpinesT repl (S d) m)) mot) a (mapSpinesE repl (S d) f)
              (mapSpinesE repl d q)
  mapSpinesE repl d (SNuC p) = SNuC (mapSpinesP repl d p)
  mapSpinesE repl d (SOut e) = SOut (mapSpinesE repl d e)
  mapSpinesE repl d (SCorec x a f u) =
    SCorec x (mapSpinesE repl d a) (mapSpinesE repl (S d) f) (mapSpinesE repl d u)
  mapSpinesE repl d (SCoind nx ny r pw mx my mh q) =
    SCoind nx ny (mapSpinesE repl (S (S d)) r) (mapSpinesE repl d pw) mx my mh
           (mapSpinesE repl (S (S (S d))) q)
  mapSpinesE repl d (SSquash t) = SSquash (mapSpinesT repl d t)
  mapSpinesE repl d e@(SStar _) = e
  mapSpinesE repl d e@(SStarUsing _ _) = e
  mapSpinesE repl d (SStarWit e) = SStarWit (mapSpinesE repl d e)
  mapSpinesE repl d (SSquashElim e x body) =
    SSquashElim (mapSpinesE repl d e) x (mapSpinesE repl (S d) body)
  mapSpinesE repl d (SChain x ls) =
    SChain (mapSpinesE repl d x)
           (map (\(j, y) => (mapSpinesE repl d j, mapSpinesE repl d y)) ls)
  mapSpinesE repl d (SAnn e ty) = SAnn (mapSpinesE repl d e) (mapSpinesT repl d ty)
  mapSpinesE repl d (SImpArg e) = SImpArg (mapSpinesE repl d e)
  mapSpinesE repl d (SNoIns e) = SNoIns (mapSpinesE repl d e)
  mapSpinesE repl d e@(SBlank _) = e

  mapSpinesT : (repl : Nat -> SElem -> List SElem -> Maybe SElem) -> Nat -> STy -> STy
  mapSpinesT repl d (STyPos r t) = STyPos r (mapSpinesT repl d t)
  mapSpinesT repl d STyZero = STyZero
  mapSpinesT repl d STyOne = STyOne
  mapSpinesT repl d STyNat = STyNat
  mapSpinesT repl d STyUniv = STyUniv
  mapSpinesT repl d t@(STySig _) = t
  mapSpinesT repl d (STyPi x a b) = STyPi x (mapSpinesT repl d a) (mapSpinesT repl (S d) b)
  mapSpinesT repl d (STyImpPi x a b) = STyImpPi x (mapSpinesT repl d a) (mapSpinesT repl (S d) b)
  mapSpinesT repl d (STySigma x a b) = STySigma x (mapSpinesT repl d a) (mapSpinesT repl (S d) b)
  mapSpinesT repl d (STySum a b) = STySum (mapSpinesT repl d a) (mapSpinesT repl d b)
  mapSpinesT repl d (STyQuot a x y r) = STyQuot (mapSpinesT repl d a) x y (mapSpinesE repl (S (S d)) r)
  mapSpinesT repl d (STyEq rng l r t) =
    STyEq rng (mapSpinesE repl d l) (mapSpinesE repl d r) (map (mapSpinesT repl d) t)
  mapSpinesT repl d (STyEl e) = STyEl (mapSpinesE repl d e)
  mapSpinesT repl d STyProp = STyProp
  mapSpinesT repl d (STyNu p) = STyNu (mapSpinesP repl d p)

  mapSpinesP : (repl : Nat -> SElem -> List SElem -> Maybe SElem) -> Nat -> SPoly -> SPoly
  mapSpinesP repl d SPHole = SPHole
  mapSpinesP repl d (SPConst a) = SPConst (mapSpinesE repl d a)
  mapSpinesP repl d (SPProd p q) = SPProd (mapSpinesP repl d p) (mapSpinesP repl d q)
  mapSpinesP repl d (SPSum p q) = SPSum (mapSpinesP repl d p) (mapSpinesP repl d q)
  mapSpinesP repl d (SPSigma x a p) = SPSigma x (mapSpinesE repl d a) (mapSpinesP repl (S d) p)
  mapSpinesP repl d (SPPi x a p) = SPPi x (mapSpinesE repl d a) (mapSpinesP repl (S d) p)

-- ===== Call alignment (term-syntax conventions) =====

||| Align a call's SPELLED arguments to the item's columns: an
||| implicit column consumes a {t} override if one is next and is
||| otherwise ELIDED — its value the column's own variable in the
||| clause telescope (colFill, weakened by the depth; verified
||| downstream by the clause lemma's β-discharge) — an explicit
||| column consumes the next plain argument. Exhausted arguments stop
||| the walk (a PARTIAL application — legal past the split column);
||| arguments beyond the columns stay applied (Π's past the k-th
||| live inside B). Nothing = misaligned ({t} at an explicit column,
||| or an elided implicit at a constructor-pattern column).
alignCallP : (colImps : List Bool) -> (colFill : List (Maybe (SName, Nat))) ->
             (d : Nat) -> List SElem -> Maybe (List SElem, List SElem)
alignCallP colImps colFill d args = go colImps colFill args
 where
  consA : SElem -> (List SElem, List SElem) -> (List SElem, List SElem)
  consA v (vs, ex) = (v :: vs, ex)
  go : List Bool -> List (Maybe (SName, Nat)) -> List SElem -> Maybe (List SElem, List SElem)
  go _ _ [] = Just ([], [])
  go [] _ rest = Just ([], rest)
  go (True :: is) (mf :: fs) (a0 :: as) =
    case unPos a0 of
      SImpArg t => consA t <$> go is fs as
      _ => do (nm, top) <- mf
              consA (SVar (snd nm) (fst nm) (d + top)) <$> go is fs (a0 :: as)
  go (True :: is) (mf :: fs) [] = do
    (nm, top) <- mf
    consA (SVar (snd nm) (fst nm) (d + top)) <$> go is fs []
  go (False :: is) (_ :: fs) (a0 :: as) =
    case unPos a0 of
      SImpArg _ => Nothing
      _ => consA a0 <$> go is fs as
  go _ [] _ = Nothing

-- ===== Structural-recursion rewriting =====

||| Replace every application spine of `f` whose ALIGNED leading
||| arguments are exactly the required variables — the clause's
||| earlier column variables, then the predecessor — by the MARKER
||| variable (top-level index `mk`) applied to the remaining
||| (rewritten) aligned arguments. Nothing if any occurrence of f
||| survives in another shape (a misaligned or unguarded call is left
||| in place and fails the final occurrence check): the recursion is
||| not structural.
rwCalls : (f : String) -> (mk : Nat) -> (lead : List Nat) ->
          (colImps : List Bool) -> (colFill : List (Maybe (SName, Nat))) ->
          SElem -> Maybe SElem
rwCalls fname mk lead colImps colFill e0 =
  let r = mapSpinesE repl 0 e0 in
  if occursE fname r then Nothing else Just r
 where
  isReqVar : Nat -> SElem -> Bool
  isReqVar want e = case unPos e of
    SVar _ _ i => i == want
    _ => False
  repl : Nat -> SElem -> List SElem -> Maybe SElem
  repl d (SSig _ x) args =
    if x /= fname then Nothing else do
      (aligned, extras) <- alignCallP colImps colFill d args
      let (las, rest) = splitAt (length lead) aligned
      let True = length las == length lead
        | False => Nothing
      let True = all (\(want, got) => isReqVar (want + d) got) (zip lead las)
        | False => Nothing
      -- nested calls inside the remaining arguments rewrite too; a
      -- failure there survives as an f-occurrence and fails the
      -- final check
      pure (spine (SVar Nothing "ih" (mk + d))
                  (map (mapSpinesE repl d) (rest ++ extras)))
  repl _ _ _ = Nothing


-- ===== Columns and patterns =====

nth : Nat -> List a -> Maybe a
nth _ [] = Nothing
nth Z (x :: _) = Just x
nth (S n) (_ :: xs) = nth n xs

||| Peel exactly k leading Π's off the item's SURFACE type: the
||| COLUMNS the clauses pattern, plus the rest (which may itself be a
||| Π-type — the generated equations then sit at a function type).
peelPis : Nat -> STy -> Maybe (List (String, STy), STy)
peelPis Z ty = Just ([], ty)
peelPis (S n) ty = case unPosTy ty of
  STyPi x a b => do
    (cols, rest) <- peelPis n b
    pure ((x, a) :: cols, rest)
  _ => Nothing

||| Syntactic ℕ-recognition (the spec reads whnf(Aⱼ); the syntactic
||| approximation only narrows the FRAGMENT — unrecognized split
||| types degrade, which is always sound).
tyNat : STy -> Bool
tyNat ty = case unPosTy ty of
  STyNat => True
  STyEl e => case unPos e of
    SNatC => True
    _ => False
  _ => False

tySumParts : STy -> Maybe (STy, STy)
tySumParts ty = case unPosTy ty of
  STySum a b => Just (a, b)
  STyEl e => case unPos e of
    SSumC a b => Just (STyEl a, STyEl b)
    _ => Nothing
  _ => Nothing

||| A pattern with its variable's telescope SLOT resolved (0-based,
||| outermost first) and whether this occurrence BINDS the slot (a
||| repeated name reuses an earlier slot — nonlinear LHS).
data PatSk : Type where
  KVar : SName -> (slot : Nat) -> (binds : Bool) -> PatSk
  KZero : PatSk
  KSuc : PatSk -> PatSk
  KInj1 : PatSk -> PatSk
  KInj2 : PatSk -> PatSk

indexOf : Eq a => a -> List a -> Maybe Nat
indexOf x [] = Nothing
indexOf x (y :: ys) = if x == y then Just 0 else map S (indexOf x ys)

||| Slot assignment, mirroring the parser's patVarsOf exactly: one
||| slot per variable in order of first appearance, wildcards always
||| fresh.
assignSlots : List SPat -> (List PatSk, Nat)
assignSlots pats =
  let (sks, slots) = go [] pats in (sks, length slots)
 where
  goP : List String -> SPat -> (PatSk, List String)
  goP seen (SPVar x) =
    case (fst x /= wildcard, indexOf (fst x) seen) of
      (True, Just i) => (KVar x i False, seen)
      _ => (KVar x (length seen) True, seen ++ [fst x])
  goP seen (SPImpVar x) =
    case (fst x /= wildcard, indexOf (fst x) seen) of
      (True, Just i) => (KVar x i False, seen)
      _ => (KVar x (length seen) True, seen ++ [fst x])
  goP seen SPZero = (KZero, seen)
  goP seen (SPSuc p) = let (sk, seen') = goP seen p in (KSuc sk, seen')
  goP seen (SPInj1 p) = let (sk, seen') = goP seen p in (KInj1 sk, seen')
  goP seen (SPInj2 p) = let (sk, seen') = goP seen p in (KInj2 sk, seen')
  go : List String -> List SPat -> (List PatSk, List String)
  go seen [] = ([], seen)
  go seen (p :: ps) =
    let (sk, seen') = goP seen p
        (sks, seen'') = go seen' ps
    in (sk :: sks, seen'')

||| The pattern as a surface element over a context of `n` binders
||| whose innermost `slots` entries are the telescope.
patTerm : (ctxSize : Nat) -> PatSk -> SElem
patTerm n (KVar x s _) = SVar (snd x) (fst x) (minus n (S s))
patTerm n KZero = SZeroN
patTerm n (KSuc p) = SSuc (patTerm n p)
patTerm n (KInj1 p) = SInj1 (patTerm n p)
patTerm n (KInj2 p) = SInj2 (patTerm n p)

||| The telescope entries a pattern binds, given its (transported)
||| column type. Fails when the pattern's constructors do not match
||| the column type's syntactic shape — a STRUCTURAL error (the
||| clause's statement would be untypable).
typePat : STy -> PatSk -> Either String (List (SName, STy))
typePat a (KVar x _ True) = Right [(x, a)]
typePat a (KVar x _ False) = Right []
typePat a KZero =
  if tyNat a then Right [] else Left "pattern Z at a column whose type is not ℕ"
typePat a (KSuc p) =
  if tyNat a then typePat STyNat p
             else Left "pattern S … at a column whose type is not ℕ"
typePat a (KInj1 p) =
  case tySumParts a of
    Just (l, _) => typePat l p
    Nothing => Left "pattern inj₁ … at a column whose type is not a ⊎"
typePat a (KInj2 p) =
  case tySumParts a of
    Just (_, r) => typePat r p
    Nothing => Left "pattern inj₂ … at a column whose type is not a ⊎"

||| Per-clause data: the pattern telescope (outermost first) with the
||| per-entry implicitness of its binders (an implicit column's
||| variable — spelled {x} or elided — binds implicitly in the
||| generated lemma), the resolved pattern skeletons, and the LHS
||| argument spine over the full telescope.
record ClauseData where
  constructor MkClauseData
  csks : List PatSk
  ctele : List (SName, STy)
  cimps : List Bool
  cargs : List SElem

buildClauseData : List (String, STy) -> List Bool -> SClause -> Either String ClauseData
buildClauseData cols colImps clause = do
  let (sks, nslots) = assignSlots clause.cpats
  (tele, imps) <- go 0 [] (map snd cols) colImps sks
  let args = map (patTerm nslots) sks
  if length tele == length clause.cvars
    then Right (MkClauseData sks tele imps args)
    else Left "internal: pattern telescope disagrees with the parser's"
 where
  -- position by position: transport the column type to the telescope
  -- context (substituting the EARLIER positions' pattern terms — kept
  -- in `past`, most recent first — for the earlier column variables),
  -- then read the position's binder off the pattern
  go : (bound : Nat) -> (past : List PatSk) -> List STy -> List Bool -> List PatSk ->
       Either String (List (SName, STy), List Bool)
  go bound past [] _ [] = Right ([], [])
  go bound past (a :: as) imps (sk :: sks) = do
    let a' = remapFreeTy (\d => maybe SUnitI (patTerm bound) (nth d past)) a
    binds <- typePat a' sk
    let imp = case imps of { (i :: _) => i ; [] => False }
    (rest, rimps) <- go (bound + length binds) (sk :: past) as (drop 1 imps) sks
    pure (binds ++ rest, map (const imp) binds ++ rimps)
  go _ _ _ _ _ = Left "internal: column/pattern arity mismatch"

||| The clause telescope's variables, mirroring the parser's
||| patVarsOf: one slot per variable in order of first appearance,
||| wildcards always fresh.
patVarsC : List SPat -> List SName
patVarsC = foldl goP []
 where
  goP : List SName -> SPat -> List SName
  goP acc (SPVar x) =
    if fst x /= wildcard && elem (fst x) (map fst acc) then acc else acc ++ [x]
  goP acc (SPImpVar x) =
    if fst x /= wildcard && elem (fst x) (map fst acc) then acc else acc ++ [x]
  goP acc SPZero = acc
  goP acc (SPSuc p) = goP acc p
  goP acc (SPInj1 p) = goP acc p
  goP acc (SPInj2 p) = goP acc p

-- ===== Column alignment (term-syntax conventions) =====

||| Does a pattern contain a {…} below its top level?
hasNestedImp : SPat -> Bool
hasNestedImp (SPVar _) = False
hasNestedImp (SPImpVar _) = True
hasNestedImp SPZero = False
hasNestedImp (SPSuc p) = hasNestedImp p
hasNestedImp (SPInj1 p) = hasNestedImp p
hasNestedImp (SPInj2 p) = hasNestedImp p

||| Align one clause's SPELLED patterns against the item's leading
||| Π-columns, per the term syntax's conventions: an implicit column
||| consumes a {x} pattern if one is next and is otherwise ELIDED (a
||| fresh variable named by the type's own binder); an explicit
||| column consumes the next pattern, which must not be {…}-marked
||| (at the top or nested — constructor patterns never sit at
||| implicit columns). The walk stops when the spelled patterns are
||| exhausted: trailing columns stay inside B, as before. Returns the
||| consumed columns (implicitness, binder name, type), the EXPANDED
||| pattern list with per-pattern elision flags, and the remainder
||| type.
alignClausePats : STy -> List SPat ->
                  Either String (List (Bool, String, STy), List (SPat, Bool), STy)
alignClausePats ty pats = go [] ty pats
 where
  taken : List String
  taken = map fst (patVarsC pats)
  fresh : List String -> String -> String
  fresh used n = if elem n (taken ++ used) then fresh used (n ++ "'") else n
  go : (used : List String) -> STy -> List SPat ->
       Either String (List (Bool, String, STy), List (SPat, Bool), STy)
  go used (STyPos _ t) ps@(_ :: _) = go used t ps
  go used t [] = Right ([], [], t)
  go used (STyImpPi x a b) (SPImpVar v :: ps) =
    (\(cs, es, r) => ((True, x, a) :: cs, (SPImpVar v, False) :: es, r)) <$> go used b ps
  go used (STyImpPi x a b) ps =
    let x' = fresh used x in
    (\(cs, es, r) => ((True, x, a) :: cs, (SPImpVar (x', Nothing), True) :: es, r))
      <$> go (x' :: used) b ps
  go used (STyPi x a b) (SPImpVar _ :: _) =
    Left "a {…} pattern at an explicit column"
  go used (STyPi x a b) (p :: ps) =
    if hasNestedImp p
      then Left "a {…} pattern inside a constructor pattern"
      else (\(cs, es, r) => ((False, x, a) :: cs, (p, False) :: es, r)) <$> go used b ps
  go used _ (_ :: _) =
    Left "the clauses spell more pattern positions than the item's type shows Π-columns"

||| Reindex a clause RHS from the SPELLED patterns' slot environment
||| (what the parser bound) to the EXPANDED one — the elided implicit
||| binders' slots interleave, order-preserving.
remapClauseRhs : (expanded : List (SPat, Bool)) -> SElem -> SElem
remapClauseRhs expanded rhs =
  let flags = slotFlags [] expanded
      n = length flags
      spelledSlots = map fst (filter (not . snd) (tag 0 flags))
      m = length spelledSlots
  in mapRefsE (\dd, r, nm, i =>
       case nth (minus m (S (minus i dd))) spelledSlots of
         Just s' => SVar r nm (dd + minus n (S s'))
         Nothing => SVar r nm i)
     keepSig 0 rhs
 where
  tag : Nat -> List Bool -> List (Nat, Bool)
  tag i [] = []
  tag i (b :: bs) = (i, b) :: tag (S i) bs
  extSeen : List String -> SPat -> List String
  extSeen seen (SPVar x) =
    if fst x /= wildcard && elem (fst x) seen then seen else seen ++ [fst x]
  extSeen seen (SPImpVar x) =
    if fst x /= wildcard && elem (fst x) seen then seen else seen ++ [fst x]
  extSeen seen SPZero = seen
  extSeen seen (SPSuc p) = extSeen seen p
  extSeen seen (SPInj1 p) = extSeen seen p
  extSeen seen (SPInj2 p) = extSeen seen p
  ||| per expanded slot, in slot order: does it come from an ELIDED
  ||| pattern?
  slotFlags : List String -> List (SPat, Bool) -> List Bool
  slotFlags seen [] = []
  slotFlags seen ((p, el) :: rest) =
    let seen' = extSeen seen p
    in replicate (minus (length seen') (length seen)) el ++ slotFlags seen' rest

||| The per-column FILL data of one (expanded) clause: for a
||| variable-pattern column, its binder and top-level telescope index
||| — what an elided implicit call argument aligns to.
colFillOf : (sks : List PatSk) -> (nslots : Nat) -> List (Maybe (SName, Nat))
colFillOf sks nslots =
  map (\sk => case sk of
                KVar nm s _ => Just (nm, minus nslots (S s))
                _ => Nothing) sks

-- ===== The structural fragment =====

||| The clause shapes the v1 splitter compiles (docs/NovaElaboration.txt,
||| "THE STRUCTURAL FRAGMENT"): one split column at ℕ or ⊎, depth-1
||| patterns, everything else variables, linear LHSs. The recursion
||| condition is checked separately (it gates ρ, not the uniqueness
||| synthesis).
data Shape : Type where
  ||| single all-variable clause
  ShNone : SClause -> Shape
  ||| split at 1-based column j: the Z-clause, the S-clause and its
  ||| predecessor variable
  ShNat : (j : Nat) -> (zc, sc : SClause) -> (mvar : SName) -> Shape
  ||| split at 1-based column j: the payload types and the two clauses
  ||| with their payload variables
  ShSum : (j : Nat) -> (lc : SClause) -> (avar : SName) ->
          (rc : SClause) -> (bvar : SName) -> Shape

isVarPat : SPat -> Bool
isVarPat (SPVar _) = True
isVarPat (SPImpVar _) = True
isVarPat _ = False

||| Linear: no non-wildcard variable occurs twice in one clause's LHS.
linearClause : SClause -> Bool
linearClause c =
  let occs = concatMap patNames c.cpats in
  length (filter (/= wildcard) occs) == length (nub (filter (/= wildcard) occs))
 where
  patNames : SPat -> List String
  patNames (SPVar x) = [fst x]
  patNames (SPImpVar x) = [fst x]
  patNames SPZero = []
  patNames (SPSuc p) = patNames p
  patNames (SPInj1 p) = patNames p
  patNames (SPInj2 p) = patNames p

analyzeShape : List (String, STy) -> List SClause -> Maybe Shape
analyzeShape cols clauses =
  if not (all linearClause clauses) then Nothing else
  let pmat = map (.cpats) clauses
      cands = findAll 0 (transpose pmat)
  in case (cands, clauses) of
       ([], [c]) => Just (ShNone c)
       ([i], [c1, c2]) =>
         case nth i (map snd cols) of
           Nothing => Nothing
           Just a =>
             if tyNat a
               then natShape i c1 c2 <|> natShape i c2 c1
               else case tySumParts a of
                      Just _ => sumShape i c1 c2 <|> sumShape i c2 c1
                      Nothing => Nothing
       _ => Nothing
 where
  findAll : Nat -> List (List SPat) -> List Nat
  findAll i [] = []
  findAll i (ps :: rest) =
    (if any (not . isVarPat) ps then [i] else []) ++ findAll (S i) rest
  natShape : Nat -> SClause -> SClause -> Maybe Shape
  natShape i zc sc =
    case (nth i zc.cpats, nth i sc.cpats) of
      (Just SPZero, Just (SPSuc (SPVar m))) => Just (ShNat (S i) zc sc m)
      _ => Nothing
  sumShape : Nat -> SClause -> SClause -> Maybe Shape
  sumShape i lc rc =
    case (nth i lc.cpats, nth i rc.cpats) of
      (Just (SPInj1 (SPVar a)), Just (SPInj2 (SPVar b))) =>
        Just (ShSum (S i) lc a rc b)
      _ => Nothing

-- ===== Synthesis =====

wrapSLams : List SName -> SElem -> SElem
wrapSLams xs e = foldr SLam e xs

wrapSPis : List (SName, STy) -> STy -> STy
wrapSPis xs t = foldr (\(x, a), r => STyPi (fst x) a r) t xs

||| The Π-closure of the trailing columns over the split variable:
||| the eliminator motive's chain. Piece d of the chain (0-based)
||| shifts +1 for indices ≥ d+1 — the λ-bound split column interposes
||| between the motive binder and the leading columns.
motChain : (trailing : List (String, STy)) -> STy -> STy
motChain trailing result = go 0 trailing
 where
  go : Nat -> List (String, STy) -> STy
  go d [] = result
  go d ((x, a) :: rest) = STyPi x (shiftTy (S d) 1 a) (go (S d) rest)

||| λ-binders for the leading j columns (display names from the type's
||| own binders).
leadLams : (cols : List (String, STy)) -> (j : Nat) -> SElem -> SElem
leadLams cols j e = wrapSLams (map (\(x, _) => (x, Nothing)) (take j cols)) e

||| The display binder for a column: its Π-binder name from the
||| item's own type.
colBinder : List (String, STy) -> (i : Nat) -> SName
colBinder cols i =
  case nth i cols of
    Just (x, _) => (x, Nothing)
    Nothing => ("x", Nothing)

||| The witness ρ for an ℕ split at 1-based column j of k: eliminate
||| the split variable at the Π-motive over the trailing columns.
||| Nothing when the recursion is not structural.
rhoNat : (fname : String) -> (cols : List (String, STy)) -> (colImps : List Bool) ->
         (b : STy) ->
         (j, k : Nat) -> (zc, sc : SClause) -> (mvar : SName) -> Maybe SElem
rhoNat fname cols colImps b j k zc sc mvar = do
  let kj = minus k j
  -- the Z-clause must not mention f at all
  let False = occursE fname zc.crhs
    | True => Nothing
  -- required leading arguments of a recursive call: the clause's own
  -- column variables (top-level indices k−1 … k−j+1), then the
  -- predecessor (k−j) — calls align by the term-syntax conventions
  -- (elided implicit arguments read as the ambient columns)
  let lead = map (\i => minus k i) [1 .. j]
  let (ssks, snslots) = assignSlots sc.cpats
  sBody <- rwCalls fname k lead colImps (colFillOf ssks snslots) sc.crhs
  let zBody = wrapSLams (drop (minus j 1) zc.cvars) (shiftE kj 1 zc.crhs)
  let sBody' = wrapSLams (drop j sc.cvars) (remapIdxE (msMap kj) sBody)
  let mot = motChain (drop j cols) (shiftTy (S kj) 1 b)
  let xname = colBinder cols (minus j 1)
  pure (leadLams cols j
         (SNatElim (Just (xname, mot)) zBody mvar ("ih", Nothing) sBody' (SVar Nothing (fst xname) 0)))
 where
  -- clause context [x₁…x_{j−1}, m, trailing] (size k, marker at k) to
  -- case context [x₁…x_j (λ), m, ih, trailing]
  msMap : Nat -> Nat -> Nat
  msMap kj e =
    if e < kj then e
    else if e == kj then S kj
    else if e == k then kj
    else e + 2

||| The witness ρ for a ⊎ split: no recursion (⊎-elim has no
||| induction hypothesis), so neither clause may mention f.
rhoSum : (fname : String) -> (cols : List (String, STy)) -> (b : STy) ->
         (j, k : Nat) -> (lc : SClause) -> (avar : SName) ->
         (rc : SClause) -> (bvar : SName) -> Maybe SElem
rhoSum fname cols b j k lc avar rc bvar = do
  let False = occursE fname lc.crhs
    | True => Nothing
  let False = occursE fname rc.crhs
    | True => Nothing
  let kj = minus k j
  -- clause context [x₁…x_{j−1}, payload, trailing] to case context
  -- [x₁…x_j (λ), payload, trailing]: the λ-bound split column
  -- interposes above the payload
  let lBody = wrapSLams (drop j lc.cvars) (shiftE (S kj) 1 lc.crhs)
  let rBody = wrapSLams (drop j rc.cvars) (shiftE (S kj) 1 rc.crhs)
  let mot = motChain (drop j cols) (shiftTy (S kj) 1 b)
  let xname = colBinder cols (minus j 1)
  pure (leadLams cols j
         (SSumElim (Just (xname, mot)) avar lBody bvar rBody (SVar Nothing (fst xname) 0)))

||| The no-split witness: λ-abstraction alone.
rhoNone : (fname : String) -> SClause -> Maybe SElem
rhoNone fname c = do
  let False = occursE fname c.crhs
    | True => Nothing
  pure (wrapSLams c.cvars c.crhs)

||| The pointwise uniqueness STATEMENT:
|||   (g : T) → (h₁ : clause₁-for-g) → … → (x₁:A₁) → … → g x̄ ≡ f x̄ ∈ B
||| The h-binders reuse the clause lemmas' names (display only) and
||| their types arrive PRE-BUILT for the variable head (a variable
||| never inserts, so the g-spines apply fully and plainly while f's
||| carry its {…} overrides); the trailing binders are the columns,
||| so the equation's sides determine them — the h's are SIDE
||| CONDITIONS in E's documented sense.
etaType : (fname : String) -> (ty : STy) -> (cols : List (String, STy)) ->
          (colImps : List Bool) -> (b : STy) ->
          (lemNames : List String) -> (hypTys : List STy) -> STy
etaType fname ty cols colImps b lemNames hypTys =
  let k = length cols
      m = length hypTys
      hyps = the (List (SName, STy))
               (zipWith (\n, t => ((n, Nothing), t)) lemNames hypTys)
      colBinds = the (List (SName, STy)) (map (\(x, a) => ((x, Nothing), a)) cols)
      args = map (\i => SVar Nothing (colName i) (minus k i)) [1 .. k]
      fargs = zipWith (\imp, a => if imp then SImpArg a else a) colImps args
      concl = STyEq Nothing (spine (SVar Nothing "g" (k + m)) args)
                    (spine (SSig Nothing fname) fargs) (Just b)
  in STyPi "g" ty (wrapSPis hyps (wrapSPis colBinds concl))
 where
  colName : Nat -> String
  colName i = maybe "_" fst (nth (minus i 1) cols)

||| The uniqueness PROOF for a fragment-shaped item: the eliminator at
||| the pointwise equality motive, both cases ⋆ — discharged from the
||| g-clause hypotheses, the induction hypothesis, and the clause
||| lemmas (docs/NovaKernel.txt caveat A5: no η finals exist or are
||| needed). For the no-split shape (and as the unshaped fallback) the
||| body is the bare λ…. ⋆.
etaBodyStar : (m, k : Nat) -> (lemNames : List String) ->
              (cols : List (String, STy)) -> SElem
etaBodyStar m k lemNames cols =
  SLam ("g", Nothing)
    (wrapSLams (map (\n => (n, Nothing)) lemNames)
      (wrapSLams (map (\(x, _) => (x, Nothing)) cols) (SStar Nothing)))

etaBodyElim : (fname : String) -> (cols : List (String, STy)) ->
              (colImps : List Bool) -> (b : STy) ->
              (j, k, m : Nat) -> (lemNames : List String) ->
              (isNat : Bool) -> (v1, v2 : SName) -> SElem
etaBodyElim fname cols colImps b j k m lemNames isNat v1 v2 =
  let kj = minus k j
      trailing = drop j cols
      -- context at the motive's equation: [g, h's, x₁…x_j, x, trailing]
      args = map (\i => SVar Nothing (colName i)
                    (if i < j then (minus k i) + 1
                     else if i == j then kj
                     else minus k i)) [1 .. k]
      fargs = zipWith (\imp, a => if imp then SImpArg a else a) colImps args
      concl = STyEq Nothing (spine (SVar Nothing "g" (m + k + 1)) args)
                    (spine (SSig Nothing fname) fargs)
                    (Just (shiftTy (S kj) 1 b))
      mot = motChain trailing concl
      trailLams = wrapSLams (map (\(x, _) => (x, Nothing)) trailing) (SStar Nothing)
      xname = colBinder cols (minus j 1)
      scrut = SVar Nothing (fst xname) 0
      elim = if isNat
               then SNatElim (Just (xname, mot)) trailLams v1 ("ih", Nothing) trailLams scrut
               else SSumElim (Just (xname, mot)) v1 trailLams v2 trailLams scrut
  in SLam ("g", Nothing)
       (wrapSLams (map (\n => (n, Nothing)) lemNames)
         (leadLams cols j elim))
 where
  colName : Nat -> String
  colName i = maybe "_" fst (nth (minus i 1) cols)

-- ===== Naming =====

defaultTag : SClause -> String
defaultTag c = go c.cpats
 where
  tag : SPat -> Maybe String
  tag (SPVar _) = Nothing
  tag (SPImpVar _) = Nothing
  tag SPZero = Just "Z"
  tag (SPSuc _) = Just "S"
  tag (SPInj1 _) = Just "Inl"
  tag (SPInj2 _) = Just "Inr"
  go : List SPat -> String
  go [] = "Eq"
  go (p :: ps) = fromMaybe (go ps) (tag p)

||| Every Σ-name a clausal item mints (the definition, the clause
||| lemmas, the uniqueness lemma) — a pure function of the source, per
||| the reproducibility invariant. Used by the expansion and by the
||| LSP's symbol listing.
export
clausalNames : String -> Maybe String -> List SClause -> List String
clausalNames fname etaName cls =
  fname :: map (\c => fromMaybe (fname ++ defaultTag c) c.cname) cls
        ++ [fromMaybe (fname ++ "Eta") etaName]

-- ===== The expansion =====

public export
record Expansion where
  constructor MkExpansion
  ||| each generated item with the source it is ABOUT: a clause lemma
  ||| is about its clause, the definition and the uniqueness lemma
  ||| about the item as a whole. That range is what the elaborator
  ||| reports the item's failures and obligations at.
  items : List (Maybe Range, SItem)
  echo : String

||| Expand a clausal def into its batch (docs/NovaElaboration.txt,
||| "Defining equations"). Left = STRUCTURAL error (malformed clauses:
||| arity mismatch, unpeelable columns, untypable patterns, missing
||| name overrides on an operator-named item). Everything else
||| degrades through the tiers: full synthesis / witness-supplied /
||| declarations — one semantics, three labor divisions.
export
expandClausal : (nrng : Maybe Range) -> (fname : String) -> STy ->
                (muses : Maybe (List String)) ->
                (etaName : Maybe String) -> (witness : Maybe SElem) ->
                List SClause -> Either String Expansion
expandClausal nrng fname ty muses etaName witness clauses = do
  -- ALIGNMENT: each clause's spelled patterns against the item's
  -- leading Π-columns (implicit columns {x}-spelled or elided, per
  -- the term syntax); all clauses must consume the same columns
  let True = not (null clauses)
    | False => Left "at least one clause is required"
  aligned <- traverse (\c => alignClausePats ty c.cpats) clauses
  (cols3, b) <- the (Either String (List (Bool, String, STy), STy)) $
    case aligned of
      ((cs, _, r) :: rest) =>
        if all (\(cs', _, _) => length cs' == length cs) rest
          then Right (cs, r)
          else Left "clauses disagree on the number of pattern positions"
      [] => Left "at least one clause is required"
  let k = length cols3
  let True = k >= 1
    | False => Left "a clause must spell at least one pattern position"
  let colImps = map (\(i, _, _) => i) cols3
  let cols = map (\(_, x, a) => (x, a)) cols3
  -- the EXPANDED clauses: elided implicit binders inserted, RHSs
  -- reindexed from the spelled to the full telescope
  let eclauses = zipWith (\c, al => case al of
        (_, eps, _) => MkSClause (map fst eps) (patVarsC (map fst eps))
                                 (remapClauseRhs eps c.crhs) c.cname c.crange) clauses aligned
  -- names: deterministic defaults; an operator-named item has no
  -- identifier to prefix, so every override is mandatory
  lemNames <-
    if isOpName fname
      then traverse (\c => maybe (Left "an operator-named item requires a [name] override on every clause")
                                 Right c.cname) clauses
      else Right (map (\c => fromMaybe (fname ++ defaultTag c) c.cname) clauses)
  etaN <-
    if isOpName fname
      then maybe (Left "an operator-named item requires a [name] override (after the type) for the uniqueness lemma")
                 Right etaName
      else Right (fromMaybe (fname ++ "Eta") etaName)
  -- per-clause telescopes and lemma statements
  cds <- traverse (buildClauseData cols colImps) eclauses
  let lemTys = zipWith (mkLemTy colImps b k) eclauses cds
  -- the λ's here are pure scaffolding over a ⋆ — their binders reuse
  -- the pattern variables' SPANS, which would pull the lemma's
  -- obligations onto a variable inside a pattern: keep the display
  -- names, drop the ranges (the Π-binders of mkLemTy keep theirs)
  let lemBodies = map (\cd => wrapSLams (map (\(n, _) => (n, Nothing)) (map fst cd.ctele))
                                        (SStar Nothing)) cds
  let m = length clauses
  let hypTys = zipWith3 (mkLemTyG colImps b k) (rangeFrom0 m) eclauses cds
  let eTy = etaType fname ty cols colImps b lemNames hypTys
  let shape = analyzeShape cols eclauses
  let eBodySynth = map (shapedEtaBody cols colImps b k m lemNames) shape
  let eBodyStar = etaBodyStar m k lemNames cols
  let names = fname :: lemNames ++ [etaN]
  let musesL = fromMaybe [] muses
  let lemUses = nub (musesL ++ [fname ++ ".eq"])
  let etaUses = nub (musesL ++ lemNames ++ map (++ ".rw") lemNames ++ [fname ++ ".eq", "hyp.rw"])
  case witness of
    Just w =>
      -- WITNESS TIER: existence is the user's; the clause lemmas pay
      -- with ⋆ (undischarged ⋆'s are ordinary obligations), and the
      -- uniqueness proof is still synthesized whenever the clauses
      -- are fragment-shaped — it rewrites by the clause lemmas, never
      -- by unfolding the witness
      Right (MkExpansion
               ((nrng, SDef fname ty w muses)
                  -- the clause lemmas hold by the definition's own
                  -- computation: cite its defining equation explicitly
                  -- (the join needs the license to unfold the definition
                  -- it otherwise), and the uniqueness proof cites the
                  -- clause lemmas it rewrites by; the item's own
                  -- using-clause rides along on every generated item
                  :: atClauses (zipWith3 (\n, t, bo => SDef n t bo (Just lemUses)) lemNames lemTys lemBodies)
                  ++ [(nrng, SDef etaN eTy (fromMaybe eBodyStar eBodySynth) (Just etaUses))])
               "defined \{fname} by clauses via witness (\{joinBy ", " names})")
    Nothing =>
      case (shape, shape >>= shapedRho cols colImps b k) of
        (Just _, Just rho) =>
          -- THE FRAGMENT: everything synthesized
          Right (MkExpansion
                   ((nrng, SDef fname ty rho muses)
                      -- as at the witness tier: clause lemmas cite the
                      -- defining equation, uniqueness cites the clause
                      -- lemmas
                      :: atClauses (zipWith3 (\n, t, bo => SDef n t bo (Just lemUses)) lemNames lemTys lemBodies)
                      ++ [(nrng, SDef etaN eTy (fromMaybe eBodyStar eBodySynth) (Just etaUses))])
                   "defined \{fname} by clauses (\{joinBy ", " names})")
        _ =>
          -- DECLARATION TIER: the whole batch demotes to named rigid
          -- holes; the equation lemmas register in the lemma store as
          -- declared equations (the abstract-interface idiom), so the
          -- file downstream elaborates against the interface
          Right (MkExpansion
                   ((nrng, SDeclDef nrng fname ty)
                      :: zipWith3 (\r, n, t => (r, SDeclDef r n t))
                                  (map crange clauses) lemNames lemTys
                      ++ [(nrng, SDeclDef nrng etaN eTy)])
                   ("declared \{fname} and its equations (\{joinBy ", " names})"
                    ++ " — clauses outside the structural fragment"))
 where
  atClauses : List SItem -> List (Maybe Range, SItem)
  atClauses = zip (map crange clauses)

  rangeFrom0 : Nat -> List Nat
  rangeFrom0 Z = []
  rangeFrom0 (S n) = rangeFrom0 n ++ [n]

  ||| Π-closure MIRRORING the columns' implicitness (a generated
  ||| lemma reads and applies like a hand-written one).
  wrapSPisM : List (Bool, (SName, STy)) -> STy -> STy
  wrapSPisM xs t =
    foldr (\p, r => case p of
             (True, (x, a)) => STyImpPi (fst x) a r
             (False, (x, a)) => STyPi (fst x) a r) t xs

  ||| Π(Γᵢ). f p̄ᵢ ≡ tᵢ ∈ B[p̄ᵢ] — the clause, Π-closed over its pattern
  ||| telescope (implicitness mirrored); recursive occurrences in tᵢ
  ||| stay references to f, and f's implicit positions ride as {…}
  ||| overrides in the LHS spine.
  mkLemTy : List Bool -> STy -> Nat -> SClause -> ClauseData -> STy
  mkLemTy colImps b k clause cd =
    let bigL = length cd.ctele
        fargs = zipWith (\imp, a => if imp then SImpArg a else a) colImps cd.cargs
        lhs = spine (SSig Nothing fname) fargs
        bC = remapFreeTy (\d => maybe SUnitI (patTerm bigL) (nth d (reverse cd.csks))) b
    in wrapSPisM (zip cd.cimps cd.ctele) (STyEq Nothing lhs clause.crhs (Just bC))

  ||| The clause FOR A CANDIDATE VARIABLE g — the uniqueness lemma's
  ||| hypothesis at position `base` (that many binders sit between g
  ||| and this hypothesis's own Π). A variable never inserts, so the
  ||| g-spines apply fully and plainly: the LHS over the pattern
  ||| telescope, and every recursive call in the RHS respelled with
  ||| its ALIGNED argument values (elided implicits filled by their
  ||| column variables).
  mkLemTyG : List Bool -> STy -> Nat -> (base : Nat) -> SClause -> ClauseData -> STy
  mkLemTyG colImps b k base clause cd =
    let bigL = length cd.ctele
        cfill = colFillOf cd.csks bigL
        lhs = spine (SVar Nothing "g" (base + bigL)) cd.cargs
        rhs = mapSpinesE (replG cfill bigL) 0 clause.crhs
        bC = remapFreeTy (\d => maybe SUnitI (patTerm bigL) (nth d (reverse cd.csks))) b
    in wrapSPisM (zip cd.cimps cd.ctele) (STyEq Nothing lhs rhs (Just bC))
   where
    replG : List (Maybe (SName, Nat)) -> Nat -> Nat -> SElem -> List SElem -> Maybe SElem
    replG cfill bigL d (SSig _ x) args =
      if x /= fname then Nothing else do
        (as, extras) <- alignCallP colImps cfill d args
        pure (spine (SVar Nothing "g" (base + bigL + d))
                    (map (mapSpinesE (replG cfill bigL) d) (as ++ extras)))
    replG _ _ _ _ _ = Nothing

  shapedRho : List (String, STy) -> List Bool -> STy -> Nat -> Shape -> Maybe SElem
  shapedRho cols colImps b k (ShNone c) = rhoNone fname c
  shapedRho cols colImps b k (ShNat j zc sc mvar) = rhoNat fname cols colImps b j k zc sc mvar
  shapedRho cols colImps b k (ShSum j lc avar rc bvar) = rhoSum fname cols b j k lc avar rc bvar

  shapedEtaBody : List (String, STy) -> List Bool -> STy -> Nat -> Nat -> List String -> Shape -> SElem
  shapedEtaBody cols colImps b k m lemNames (ShNone _) = etaBodyStar m k lemNames cols
  shapedEtaBody cols colImps b k m lemNames (ShNat j _ sc mvar) =
    etaBodyElim fname cols colImps b j k m lemNames True mvar ("ih", Nothing)
  shapedEtaBody cols colImps b k m lemNames (ShSum j _ avar _ bvar) =
    etaBodyElim fname cols colImps b j k m lemNames False avar bvar

-- ===== The copattern def item =====
--
-- The DUAL macro (docs/NovaElaboration.txt, "Defining observations"):
-- a def into a ν-type whose single clause specifies its OBSERVATION,
--
--   def f : (x₁ : A₁) → … → (xₖ : Aₖ) → B      -- whnf(B) = ν 𝔽
--     | out (f x̄) ≔ t
--
-- asserts contractibility of
--
--   (ρ : Π…B) ⨯ (Π x̄. out (ρ x̄) ≡ t[ρ/f] ∈ ⌊𝔽⌋(B))
--
-- and expands into the batch naming that assertion's pieces:
--   * EXISTENCE — f ≔ λx̄. corec (s : σ. t̂) ⟨seeds⟩: the body READ
--     AGAINST THE POLYNOMIAL'S SHAPE (constructors move from the
--     pattern LHS to the copattern RHS — literal pairs, injections
--     and λ's down to the hole positions), each hole either a
--     saturated corecursive call (CONTINUE — inj₂ at the varying
--     columns' seed tuple) or an f-free element (STOP — inj₁,
--     released bare by el-nu-beta). The columns split into the
--     longest PREFIX passed unchanged by every call (λ-bound outside
--     the corecursor, so parameters never enter the seed) and the
--     varying suffix (the seed, a Σ-code — the smallness condition
--     of the fragment);
--   * the OBSERVATION LEMMA fOut : Π x̄. out (f x̄) ≡ t, body λ…. ⋆ —
--     β in EVERY case, primitive corecursion's payoff (a stop's
--     ⊎-elim meets its injection; a continue re-wraps to the same
--     corec the unfolded recursive reference β-reduces to);
--   * UNIQUENESS fEta — pointwise, by coind at the pure GRAPH
--     invariant ∥(ȳ : varying) ⨯ (u ≡ g x̄ₚ ȳ) ⨯ (v ≡ f x̄ₚ ȳ)∥: the
--     closure rewrites the observations by the g-clause hypothesis
--     and fOut, landing literal constructors (the fragment's shape
--     discipline is exactly what un-sticks the relator), K-positions
--     closing by reflexivity, calls re-entering the graph (inj₁),
--     stops closing in the relator's up-to-equality leg (inj₂ ⋆).
--
-- IMPLICIT COLUMNS follow the term-syntax conventions everywhere: an
-- implicit column's LHS binder is spelled {x} or elided (named by the
-- item's type); a corecursive call's implicit argument is spelled
-- {t} or elided; the generated statements apply the item's own name
-- through {…} overrides (insertion consumes them positionally) and a
-- candidate VARIABLE g with every argument plain (variables never
-- insert). PLACEMENT is resolved here, syntactically — which
-- positions are implicit is a pure function of the item's own type —
-- while the VALUES of elided call arguments are read off the
-- elaborated (insertion-resolved) body by the caller's probe: an
-- elided argument that resolved to anything but its ambient column
-- variable has no surface spelling for the seed, so the item
-- degrades with a spell-it remedy (expandCopattern's elidedBad).
--
-- The polynomial arrives from the caller as its SHAPE only
-- (elabItemGo exposes the item's head type to ν 𝔽 under the item's
-- using licenses); its embedded pieces are never consulted — every
-- generated statement spells types the user's source already spells
-- (the ∈-annotations of the generated equations are elided, inferred
-- from their out-headed left sides). Tiers degrade exactly as at the
-- clausal def: witness-supplied existence keeps the lemma ⋆'s as
-- ordinary obligations; outside the fragment without a witness the
-- batch demotes to declarations.

||| [1 .. k] that is empty at k = 0 (Idris ranges descend).
range1 : Nat -> List Nat
range1 Z = []
range1 (S n) = range1 n ++ [S n]

||| A column type as a universe CODE — the syntactic conversion
||| behind the seed-smallness condition. Nothing (degrade) where no
||| code spelling exists (𝕌, Ω, ≡, an implicit Π, a type-def
||| reference).
tyToCode : STy -> Maybe SElem
tyToCode (STyPos _ t) = tyToCode t
tyToCode STyZero = Just SZeroC
tyToCode STyOne = Just SOneC
tyToCode STyNat = Just SNatC
tyToCode (STyEl e) = Just e
tyToCode (STyPi x a b) = [| SPiC (pure x) (tyToCode a) (tyToCode b) |]
tyToCode (STySigma x a b) = [| SSigmaC (pure x) (tyToCode a) (tyToCode b) |]
tyToCode (STySum a b) = [| SSumC (tyToCode a) (tyToCode b) |]
tyToCode (STyQuot a x y r) = (\a' => SQuotC a' x y r) <$> tyToCode a
tyToCode (STyNu p) = Just (SNuC p)
tyToCode _ = Nothing

||| Nested pair spelling of a seed tuple (𝟙's element at zero
||| components).
mkTuple : List SElem -> SElem
mkTuple [] = SUnitI
mkTuple [e] = e
mkTuple (e :: es) = SPair e (mkTuple es)

||| Peel ALL leading Π-columns, implicit and explicit — a copattern
||| item's columns (the observation is of the fully applied item;
||| every leading Π is a column since the head must be the ν-type).
peelAllPis : STy -> (List (Bool, String, STy), STy)
peelAllPis (STyPos _ t) = peelAllPis t
peelAllPis (STyPi x a b) = let (cs, r) = peelAllPis b in ((False, x, a) :: cs, r)
peelAllPis (STyImpPi x a b) = let (cs, r) = peelAllPis b in ((True, x, a) :: cs, r)
peelAllPis t = ([], t)

||| One ALIGNED copattern column: its binder (the LHS spelling, or
||| the type's own binder name when an implicit column is elided),
||| implicitness, whether the LHS spelled it, and its type.
public export
record CoCol where
  constructor MkCoCol
  cnm : SName
  cimp : Bool
  cspelled : Bool
  cty : STy

public export
record CoAligned where
  constructor MkCoAligned
  ccols : List CoCol
  ||| the clause RHS reindexed from the SPELLED-variable environment
  ||| the parser bound to the FULL column telescope
  crhsFull : SElem

||| Stage 1 — ALIGNMENT, pure and total over the surface: LHS
||| arguments against the item's columns (an implicit column takes a
||| {x} if one is next and is elided otherwise; an explicit column
||| takes the next plain variable), then the RHS reindexed to the
||| full telescope. Left = structural error.
export
copatternAlign : (fname : String) -> STy -> (cargs : List (SName, Bool)) ->
                 (crhs : SElem) -> Either String CoAligned
copatternAlign fname ty cargs crhs = do
  let (rawCols, _) = peelAllPis ty
  cols <- go rawCols cargs
  let nms = filter (/= wildcard) (map (fst . cnm) (filter (.cspelled) cols))
  let True = length nms == length (nub nms)
    | False => Left "the copattern's argument variables must be distinct"
  let k = length cols
  -- spelled columns in order, as 1-based column numbers
  let spelled = the (List Nat)
                  (map Builtin.fst (filter (\p => (snd p).cspelled) (zip (range1 k) cols)))
  let m = length spelled
  -- spelled de Bruijn slot s (innermost = 0) sits at column
  -- spelled_(m−s); its full-telescope index is k − that column
  let rhs = mapRefsE (\dd, r, n, i =>
              case nth (minus m (S (minus i dd))) spelled of
                Just c => SVar r n (dd + minus k c)
                Nothing => SVar r n i)   -- unreachable: parser bound m vars
              keepSig 0 crhs
  pure (MkCoAligned cols rhs)
 where
  go : List (Bool, String, STy) -> List (SName, Bool) -> Either String (List CoCol)
  go [] [] = Right []
  go [] (_ :: _) = Left "the copattern spells more arguments than the item's type shows Π-columns"
  go ((True, tn, a) :: cols) ((n, True) :: as) = (MkCoCol n True True a ::) <$> go cols as
  go ((True, tn, a) :: cols) as = (MkCoCol (tn, Nothing) True False a ::) <$> go cols as
  go ((False, tn, a) :: cols) ((n, False) :: as) = (MkCoCol n False True a ::) <$> go cols as
  go ((False, tn, a) :: cols) ((n, True) :: as) =
    Left "a {…} argument at an explicit column of the copattern"
  go ((False, tn, a) :: cols) [] = Left "the copattern leaves an explicit column unspelled"

||| Align a corecursive call's SPELLED arguments to the columns —
||| the placement rule of the term syntax: an implicit column
||| consumes a {t} override if one is next and is otherwise ELIDED
||| (its value the ambient column variable, subject to the probe's
||| verification); an explicit column consumes the next plain
||| argument. Nothing = the call is not saturated (or misspelled).
||| Returns the FULL k argument values and the elided mask.
alignCall : List CoCol -> (k, d : Nat) -> List SElem -> Maybe (List SElem, List Bool)
alignCall cols k d args = go 1 cols args
 where
  cons2 : SElem -> Bool -> (List SElem, List Bool) -> (List SElem, List Bool)
  cons2 v e (vs, es) = (v :: vs, e :: es)
  go : Nat -> List CoCol -> List SElem -> Maybe (List SElem, List Bool)
  go c [] [] = Just ([], [])
  go c [] (_ :: _) = Nothing
  go c (col :: rest) (a0 :: as) =
    case (col.cimp, unPos a0) of
      (True, SImpArg t) => cons2 t False <$> go (S c) rest as
      (True, _) =>
        cons2 (SVar Nothing (fst col.cnm) (d + minus k c)) True
          <$> go (S c) rest (a0 :: as)
      (False, SImpArg _) => Nothing
      (False, _) => cons2 a0 False <$> go (S c) rest as
  go c (col :: rest) [] =
    if col.cimp
      then cons2 (SVar Nothing (fst col.cnm) (d + minus k c)) True <$> go (S c) rest []
      else Nothing

||| A hole position's classification: STOP at an f-free element, or
||| CONTINUE through a saturated corecursive call (every column
||| covered per the placement rule, no argument mentioning f — a
||| nested call is not guarded).
data CoHole = CoStop SElem | CoCall (List SElem) (List Bool)

classifyHole : (fname : String) -> (cols : List CoCol) -> (d : Nat) ->
               SElem -> Either String CoHole
classifyHole fname cols d e =
  let (h, args) = unwind e
      k = length cols in
  case unPos h of
    SSig _ x =>
      if x /= fname then stop
      else if any (occursE fname) args
        then Left "a corecursive call's arguments must not themselves mention \{fname}"
      else case alignCall cols k d args of
        Just (vals, mask) => Right (CoCall vals mask)
        Nothing => Left "a corecursive call must be saturated (every column covered)"
    _ => stop
 where
  stop : Either String CoHole
  stop = if occursE fname e
           then Left "an occurrence of \{fname} at a hole position must head a saturated corecursive call"
           else Right (CoStop e)

||| Phase 1 — read the body against the polynomial's shape,
||| collecting every corecursive call with its binder depth, aligned
||| argument values and elided mask. The shape demands literal
||| constructors down to the holes; anything else is outside the
||| fragment (a degrade, not an error).
analyzeBody : (fname : String) -> (cols : List CoCol) -> Poly -> Nat -> SElem ->
              Either String (List (Nat, List SElem, List Bool))
analyzeBody fname cols = go
 where
  free : Nat -> SElem -> Either String ()
  free d e = if occursE fname e
               then Left "an external (non-hole) component must not mention \{fname}"
               else Right ()
  go : Poly -> Nat -> SElem -> Either String (List (Nat, List SElem, List Bool))
  go p d (SPos _ e) = go p d e
  go PHole d e = classifyHole fname cols d e >>= \h => case h of
      CoStop _ => Right []
      CoCall vals mask => Right [(d, vals, mask)]
  go (PConst _) d e = free d e $> []
  go (PProd f g) d (SPair a b) = (++) <$> go f d a <*> go g d b
  go (PProd _ _) d _ = Left "the body at a product position must be a literal pair"
  go (PSum f g) d (SInj1 a) = go f d a
  go (PSum f g) d (SInj2 b) = go g d b
  go (PSum _ _) d _ = Left "the body at a sum position must be a literal injection"
  go (PSigma _ f) d (SPair a b) = do free d a; go f d b
  go (PSigma _ _) d _ = Left "the body at a dependent-pair position must be a literal pair"
  go (PPi _ f) d (SLam _ b) = go f (S d) b
  go (PPi _ _) d _ = Left "the body at an exponent position must be a literal λ"

||| The per-call elided masks of a fragment-shaped body — the probe's
||| worklist (Nothing when the body is outside the fragment, where
||| the tiers take over).
export
copatternProbeCalls : (fname : String) -> List CoCol -> Poly -> SElem ->
                      Maybe (List (Nat, List Bool))
copatternProbeCalls fname cols pol rhs =
  case analyzeBody fname cols pol 0 rhs of
    Left _ => Nothing
    Right calls => Just (map (\(d, _, m) => (d, m)) calls)

||| The CORE-side hole calls: the same shape walk over the
||| elaborated (insertion-resolved) body, collecting each corecursive
||| spine's depth and full argument list — what the probe compares
||| the elided masks against. Nothing on a shape mismatch (degrade
||| safely).
export
coreHoleCalls : (fq : String) -> Poly -> Nat -> Elem -> Maybe (List (Nat, List Elem))
coreHoleCalls fq = go
 where
  spineOf : Elem -> (Elem, List Elem)
  spineOf (PiApp f e) = let (h, as) = spineOf f in (h, as ++ [e])
  spineOf e = (e, [])
  go : Poly -> Nat -> Elem -> Maybe (List (Nat, List Elem))
  go PHole d e = case spineOf e of
      (SigVar x _, args) => Just (if x == fq then [(d, args)] else [])
      _ => Just []
  go (PConst _) d e = Just []
  go (PProd f g) d (SigmaIntro a b) = (++) <$> go f d a <*> go g d b
  go (PSum f g) d (Inj1 a) = go f d a
  go (PSum f g) d (Inj2 b) = go g d b
  go (PSigma _ f) d (SigmaIntro a b) = go f d b
  go (PPi _ f) d (PiIntro b) = go f (S d) b
  go _ _ _ = Nothing

||| How many leading columns a call passes unchanged (its aligned
||| value the column's own variable).
callPrefix : (k : Nat) -> (Nat, List SElem, List Bool) -> Nat
callPrefix k (d, vals, _) = go 1 vals
 where
  go : Nat -> List SElem -> Nat
  go i (a :: rest) = case unPos a of
    SVar _ _ v => if v == d + minus k i then S (go (S i) rest) else 0
    _ => 0
  go i [] = 0

||| Seed projection: the i-th (1-based) of nv varying components of
||| the seed variable at index `base` — the last component carries no
||| .π₁ (the tuple is right-nested).
seedProj : (sv : String) -> (base, i, nv : Nat) -> SElem
seedProj sv base i nv =
  let s = SVar Nothing sv base in
  if nv == 1 then s
  else if i == nv then pi2s (minus i 1) s
  else SProj1 (pi2s (minus i 1) s)
 where
  pi2s : Nat -> SElem -> SElem
  pi2s Z acc = acc
  pi2s (S m) acc = pi2s m (SProj2 acc)

||| Phase 2a — the coalgebra body: the full-telescope environment
||| [x̄] (+ d locals) remapped to [x̄, s] (+ d locals): prefix columns
||| to their λ-binders (one binder, s, interposes), varying columns
||| to seed projections; each hole tagged inj₁ (stop, remapped
||| element) or inj₂ (continue, the call's varying values as a seed
||| tuple).
walkCoalg : (fname : String) -> (cols : List CoCol) -> (j, nv : Nat) -> (sv : String) ->
            Poly -> Nat -> SElem -> Either String SElem
walkCoalg fname cols j nv sv = go
 where
  k : Nat
  k = length cols
  rm : Nat -> SElem -> SElem
  rm d e = mapRefsE (\dd, r, n, i =>
             let c = minus k (minus i dd) in
             if c <= j then SVar r n (S i)
                       else seedProj sv dd (minus c j) nv)
           keepSig d e
  go : Poly -> Nat -> SElem -> Either String SElem
  go p d (SPos _ e) = go p d e
  go PHole d e = classifyHole fname cols d e >>= \h => case h of
      CoStop v => Right (SInj1 (rm d v))
      CoCall vals _ => Right (SInj2 (mkTuple (map (rm d) (drop j vals))))
  go (PConst _) d e = Right (rm d e)
  go (PProd f g) d (SPair a b) = [| SPair (go f d a) (go g d b) |]
  go (PSigma _ f) d (SPair a b) = SPair (rm d a) <$> go f d b
  go (PSum f g) d (SInj1 a) = SInj1 <$> go f d a
  go (PSum f g) d (SInj2 b) = SInj2 <$> go g d b
  go (PPi _ f) d (SLam x b) = SLam x <$> go f (S d) b
  go _ d _ = Left "internal: copattern shape mismatch after analysis"

||| Phase 2b — the uniqueness closure's payload: a proof of the
||| relator at the two rewritten observation bodies, read off the
||| same shape. Environment [g, h, x̄, u, v, hb, w] (+ d locals): the
||| clause environment remaps prefix columns to the λ-binders (u, v,
||| hb, w interpose) and varying columns to projections of the graph
||| witness w (uniformly .π₁ ∘ .π₂ⁱ⁻¹ — the equation pair follows the
||| seed components).
walkPayload : (fname : String) -> (cols : List CoCol) -> (j : Nat) ->
              Poly -> Nat -> SElem -> Either String SElem
walkPayload fname cols j = go
 where
  k : Nat
  k = length cols
  star : SElem
  star = SStar Nothing
  cloProj : (base, i : Nat) -> SElem
  cloProj base i = SProj1 (pi2s (minus i 1) (SVar Nothing "w" base))
   where
    pi2s : Nat -> SElem -> SElem
    pi2s Z acc = acc
    pi2s (S m) acc = pi2s m (SProj2 acc)
  rm : Nat -> SElem -> SElem
  rm d e = mapRefsE (\dd, r, n, i =>
             let c = minus k (minus i dd) in
             if c <= j then SVar r n (4 + i)
                       else cloProj dd (minus c j))
           keepSig d e
  go : Poly -> Nat -> SElem -> Either String SElem
  go p d (SPos _ e) = go p d e
  go PHole d e = classifyHole fname cols d e >>= \h => case h of
      CoStop _ => Right (SStarWit (SInj2 star))
      CoCall vals _ =>
        Right (SStarWit (SInj1 (SStarWit
          (foldr SPair (SPair star star) (map (rm d) (drop j vals))))))
  go (PConst _) d e = Right star
  go (PProd f g) d (SPair a b) =
    (\l, r => SStarWit (SPair l r)) <$> go f d a <*> go g d b
  go (PSigma _ f) d (SPair a b) = (\r => SStarWit (SPair star r)) <$> go f d b
  go (PSum f g) d (SInj1 a) = go f d a
  go (PSum f g) d (SInj2 b) = go g d b
  go (PPi _ f) d (SLam x b) = (\r => SStarWit (SLam x r)) <$> go f (S d) b
  go _ d _ = Left "internal: copattern shape mismatch after analysis"

||| Every Σ-name a copattern item mints — a pure function of the
||| source, per the reproducibility invariant. Used by the expansion
||| and the LSP's symbol listing.
export
copatternNames : String -> (cname : Maybe String) -> (etaName : Maybe String) -> List String
copatternNames fname cname etaName =
  [fname, fromMaybe (fname ++ "Out") cname, fromMaybe (fname ++ "Eta") etaName]

||| Expand a copattern def into its batch, given the aligned columns
||| and RHS, the head polynomial's shape, and the probe's verdict on
||| elided call arguments (Just = an elided implicit resolved away
||| from its ambient column — a degrade with a spell-it remedy).
||| Left = STRUCTURAL error; everything else degrades through the
||| tiers, as at expandClausal.
export
expandCopattern : (nrng : Maybe Range) -> (fname : String) -> STy ->
                  (muses : Maybe (List String)) ->
                  (etaName : Maybe String) -> (witness : Maybe SElem) ->
                  (al : CoAligned) -> (cname : Maybe String) ->
                  (pol : Poly) -> (elidedBad : Maybe String) ->
                  Either String Expansion
expandCopattern nrng fname ty muses etaName witness al cname pol elidedBad = do
  let cols = al.ccols
  let crhs = al.crhsFull
  let k = length cols
  lemN <- if isOpName fname
            then maybe (Left "an operator-named item requires a [name] override on its observation clause")
                       Right cname
            else Right (fromMaybe (fname ++ "Out") cname)
  etaN <- if isOpName fname
            then maybe (Left "an operator-named item requires a [name] override (after the type) for the uniqueness lemma")
                       Right etaName
            else Right (fromMaybe (fname ++ "Eta") etaName)
  -- the item's own spine: {…} overrides at the implicit positions
  -- (insertion consumes them); a VARIABLE candidate's spine: every
  -- argument plain (variables never insert)
  let fArgsAt = the ((Nat -> Nat) -> List SElem) $ \ix =>
                  map (\(c, col) =>
                        let v = SVar Nothing (fst col.cnm) (ix c) in
                        if col.cimp then SImpArg v else v)
                      (zip (range1 k) cols)
  let gArgsAt = the ((Nat -> Nat) -> List SElem) $ \ix =>
                  map (\(c, col) => SVar Nothing (fst col.cnm) (ix c))
                      (zip (range1 k) cols)
  let lemTy = wrapSPisI cols
                (STyEq Nothing (SOut (spine (SSig Nothing fname) (fArgsAt (\c => minus k c))))
                       crhs Nothing)
  let lemBody = wrapSLams (map (.cnm) cols) (SStar Nothing)
  let eTy = etaCoType cols k fArgsAt gArgsAt lemN
  let musesL = fromMaybe [] muses
  let lemUses = nub (musesL ++ [fname ++ ".eq"])
  let etaUses = nub (musesL ++ [lemN, lemN ++ ".rw", fname ++ ".eq", "hyp.rw"])
  let names = [fname, lemN, etaN]
  let synth = fragmentSynth cols k lemN fArgsAt
  case witness of
    Just w =>
      -- WITNESS TIER: existence is the user's; the observation lemma
      -- pays with ⋆ (an undischarged ⋆ is an ordinary obligation);
      -- uniqueness is still synthesized whenever the body is
      -- fragment-shaped — it rewrites by the lemma, never by
      -- unfolding the witness
      Right (MkExpansion
               [ (nrng, SDef fname ty w muses)
               , (nrng, SDef lemN lemTy lemBody (Just lemUses))
               , (nrng, SDef etaN eTy (either (const (etaCoStar cols lemN)) snd synth) (Just etaUses)) ]
               "defined \{fname} by copattern via witness (\{joinBy ", " names})")
    Nothing =>
      case synth of
        Right (rho, eBody) =>
          -- THE FRAGMENT: everything synthesized
          Right (MkExpansion
                   [ (nrng, SDef fname ty rho muses)
                   , (nrng, SDef lemN lemTy lemBody (Just lemUses))
                   , (nrng, SDef etaN eTy eBody (Just etaUses)) ]
                   "defined \{fname} by copattern (\{joinBy ", " names})")
        Left why =>
          -- DECLARATION TIER: the batch demotes; the observation
          -- lemma registers as a declared equation (the
          -- abstract-interface idiom)
          Right (MkExpansion
                   [ (nrng, SDeclDef nrng fname ty)
                   , (nrng, SDeclDef Nothing lemN lemTy)
                   , (nrng, SDeclDef Nothing etaN eTy) ]
                   ("declared \{fname} and its observation (\{joinBy ", " names})"
                    ++ " — outside the corecursive fragment: \{why}"))
 where
  colNm : List CoCol -> Nat -> String
  colNm cs c = maybe "_" (fst . cnm) (nth (minus c 1) cs)

  ||| Π-closure MIRRORING the columns' implicitness (the generated
  ||| lemma reads and applies like a hand-written one).
  wrapSPisI : List CoCol -> STy -> STy
  wrapSPisI cs t =
    foldr (\c, r => (if c.cimp then STyImpPi else STyPi) (fst c.cnm) c.cty r) t cs

  ||| The clause RHS respelled for the VARIABLE candidate g: each
  ||| corecursive call becomes g applied to its FULL aligned values,
  ||| all plain (g never inserts; elided implicits are their column
  ||| variables — the fragment's verified reading). Environment
  ||| [g, x̄] (+ locals): column indices unchanged, g at depth + k.
  walkG : List CoCol -> Poly -> Nat -> SElem -> Either String SElem
  walkG cols pl d0 e0 = go pl d0 e0
   where
    k : Nat
    k = length cols
    go : Poly -> Nat -> SElem -> Either String SElem
    go p d (SPos _ e) = go p d e
    go PHole d e = classifyHole fname cols d e >>= \h => case h of
        CoStop v => Right v
        CoCall vals _ => Right (spine (SVar Nothing "g" (d + k)) vals)
    go (PConst _) d e = Right e
    go (PProd f g') d (SPair a b) = [| SPair (go f d a) (go g' d b) |]
    go (PSigma _ f) d (SPair a b) = SPair a <$> go f d b
    go (PSum f g') d (SInj1 a) = SInj1 <$> go f d a
    go (PSum f g') d (SInj2 b) = SInj2 <$> go g' d b
    go (PPi _ f) d (SLam x b) = SLam x <$> go f (S d) b
    go _ d _ = Left "shape"

  ||| Fallback g-respell for non-fragment bodies (degrade tiers):
  ||| every f-reference becomes the variable, arguments kept as
  ||| written (a surviving {…} mark under the now-variable head is
  ||| rejected by elaboration — acceptable in a tier that is already
  ||| outside the fragment).
  gFallback : Nat -> SElem -> SElem
  gFallback base e =
    mapRefsE (\_, r, n, i => SVar r n i)
             (\d, r, x => if x == fname then SVar r "g" (base + d) else SSig r x)
             0 e

  ||| (g : T) → (h : the observation clause FOR g) → (x̄) →
  ||| g x̄ ≡ f x̄ — pointwise, the h a SIDE CONDITION in E's
  ||| documented sense. h's statement applies g fully and plainly.
  etaCoType : (cols : List CoCol) -> (k : Nat) ->
              (fArgsAt : (Nat -> Nat) -> List SElem) ->
              (gArgsAt : (Nat -> Nat) -> List SElem) ->
              (lemN : String) -> STy
  etaCoType cols k fArgsAt gArgsAt lemN =
    let rhsG = either (const (gFallback k al.crhsFull)) id (walkG cols pol 0 al.crhsFull)
        hTy = wrapSPisI cols
                (STyEq Nothing (SOut (spine (SVar Nothing "g" k) (gArgsAt (\c => minus k c))))
                       rhsG Nothing)
        concl = STyEq Nothing (spine (SVar Nothing "g" (k + 1)) (gArgsAt (\c => minus k c)))
                       (spine (SSig Nothing fname) (fArgsAt (\c => minus k c))) Nothing
    in STyPi "g" ty (STyPi lemN hTy
         (foldr (\c, r => STyPi (fst c.cnm) c.cty r) concl cols))

  etaCoStar : (cols : List CoCol) -> (lemN : String) -> SElem
  etaCoStar cols lemN =
    SLam ("g", Nothing) (SLam (lemN, Nothing)
      (wrapSLams (map (.cnm) cols) (SStar Nothing)))

  ||| The seed carrier: the varying columns' types as a right-nested
  ||| Σ-code (𝟙 at zero components). The i-th component's type crosses
  ||| the earlier varying binders unchanged (they re-bind the same
  ||| columns); its prefix-column references shift past the seed
  ||| binder's displacement.
  mkCarrier : (j, nv : Nat) -> List CoCol -> Either String SElem
  mkCarrier j nv [] = Right SOneC
  mkCarrier j nv varying = go 0 varying
   where
    conv : Nat -> STy -> Either String SElem
    conv i a = maybe (Left "a varying argument's type spells no universe code (the corecursion seed must be small)")
                     Right (tyToCode (shiftTy i nv a))
    go : Nat -> List CoCol -> Either String SElem
    go i [c] = conv i c.cty
    go i (c :: rest) = [| SSigmaC (pure (fst c.cnm)) (conv i c.cty) (go (S i) rest) |]
    go i [] = Left "internal: empty varying telescope"

  ||| The uniqueness proof: coind at the graph invariant
  ||| ∥(ȳ : varying) ⨯ (u ≡ g x̄ₚ ȳ) ⨯ (v ≡ f x̄ₚ ȳ)∥, endpoints by the
  ||| λ-bound varying columns, closure by squash-elim on the
  ||| hypothesis and the shape-directed payload.
  etaCoBody : (cols : List CoCol) -> (k, j, nv : Nat) ->
              (varying : List CoCol) -> (lemN : String) -> (qpay : SElem) -> SElem
  etaCoBody cols k j nv varying lemN qpay =
    let rTy = graphTy 0 varying
        p = SStarWit (foldr SPair (SPair (SStar Nothing) (SStar Nothing))
              (map (\c => SVar Nothing (colNm cols c) (minus k c))
                   (drop j (range1 k))))
    in SLam ("g", Nothing) (SLam (lemN, Nothing)
         (wrapSLams (map (.cnm) cols)
           (SCoind ("u", Nothing) ("v", Nothing) (SSquash rTy) p
                   ("u", Nothing) ("v", Nothing) ("hb", Nothing)
                   (SSquashElim (SVar Nothing "hb" 0) ("w", Nothing) qpay))))
   where
    impAt : Nat -> Bool
    impAt c = maybe False (.cimp) (nth (minus c 1) cols)
    ||| The graph's Σ-tree: the varying binders, then the two
    ||| equations. The i-th (0-based) varying type's source
    ||| environment is [cols₁..j+i]: earlier-varying references are
    ||| innermost-aligned in the target (the graph re-binds the same
    ||| columns), prefix references sit nv + 2 deeper (u, v — cutoff
    ||| i, amount nv + 2). The f-spine carries its {…} overrides;
    ||| the g-spine is plain.
    graphTy : Nat -> List CoCol -> STy
    graphTy i [] =
      let gArgs = map (\c => SVar Nothing (colNm cols c)
                        (if c <= j then nv + 2 + minus k c
                                   else minus nv (minus c j)))
                      (range1 k)
          fArgs = map (\c =>
                    let v = SVar Nothing (colNm cols c)
                              (if c <= j then nv + 3 + minus k c
                                         else minus (S nv) (minus c j)) in
                    if impAt c then SImpArg v else v)
                      (range1 k)
      in STySigma "_"
           (STyEq Nothing (SVar Nothing "u" (nv + 1))
                  (spine (SVar Nothing "g" (nv + 3 + k)) gArgs) Nothing)
           (STyEq Nothing (SVar Nothing "v" (nv + 1))
                  (spine (SSig Nothing fname) fArgs) Nothing)
    graphTy i (c :: rest) =
      STySigma (fst c.cnm) (shiftTy i (nv + 2) c.cty) (graphTy (S i) rest)

  ||| The fragment analysis and full synthesis: (ρ, eta body).
  fragmentSynth : (cols : List CoCol) -> (k : Nat) -> (lemN : String) ->
                  (fArgsAt : (Nat -> Nat) -> List SElem) ->
                  Either String (SElem, SElem)
  fragmentSynth cols k lemN fArgsAt = do
    calls <- analyzeBody fname cols pol 0 al.crhsFull
    case elidedBad of
      Just why => Left why
      Nothing => do
        let j = foldl (\acc, c => min acc (callPrefix k c)) k calls
        let nv = minus k j
        let varying = drop j cols
        carrier <- mkCarrier j nv varying
        cbody <- walkCoalg fname cols j nv "s" pol 0 al.crhsFull
        let seed = mkTuple (map (\c => SVar Nothing (colNm cols c) (minus k c))
                                (drop j (range1 k)))
        let rho = wrapSLams (map (.cnm) cols) (SCorec ("s", Nothing) carrier cbody seed)
        qpay <- walkPayload fname cols j pol 0 al.crhsFull
        pure (rho, etaCoBody cols k j nv varying lemN qpay)
