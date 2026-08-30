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
  mapRefsE f g d (SPos r e) = SPos r (mapRefsE f g d e)

  mapRefsTy : (onVar : Nat -> Maybe Range -> String -> Nat -> SElem) ->
              (onSig : Nat -> Maybe Range -> String -> SElem) ->
              Nat -> STy -> STy
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
  mapRefsTy f g d (STyPos r t) = STyPos r (mapRefsTy f g d t)

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
  occursE f (SPos _ e) = occursE f e

  occursTy : String -> STy -> Bool
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
  occursTy f (STyPos _ t) = occursTy f t

  occursP : String -> SPoly -> Bool
  occursP f SPHole = False
  occursP f (SPConst a) = occursE f a
  occursP f (SPProd p q) = occursP f p || occursP f q
  occursP f (SPSum p q) = occursP f p || occursP f q
  occursP f (SPSigma _ a p) = occursE f a || occursP f p
  occursP f (SPPi _ a p) = occursE f a || occursP f p

-- ===== Structural-recursion rewriting =====

||| Application spine, head-first.
unwind : SElem -> (SElem, List SElem)
unwind e = case unPos e of
  SApp g a => let (h, as) = unwind g in (h, as ++ [a])
  h => (h, [])

spine : SElem -> List SElem -> SElem
spine = foldl SApp

mutual
  ||| Replace every application spine `f a₁ … aₙ` (n ≥ |lead|) whose
  ||| leading arguments are exactly the required variables — the
  ||| clause's earlier column variables, then the predecessor — by the
  ||| MARKER variable (top-level index `mk`) applied to the remaining
  ||| (rewritten) arguments. Nothing if any occurrence of f survives
  ||| in another shape: the recursion is not structural.
  rwE : (f : String) -> (mk : Nat) -> (lead : List Nat) -> Nat -> SElem -> Maybe SElem
  rwE f mk lead d e@(SApp _ _) =
    let (h, args) = unwind e in
    case unPos h of
      SSig r x =>
        if x == f
          then do
            let (las, rest) = splitAt (length lead) args
            if length las == length lead && all (\(want, got) => isReqVar (want + d) got) (zip lead las)
              then do
                rest' <- traverse (rwE f mk lead d) rest
                pure (spine (SVar Nothing "ih" (mk + d)) rest')
              else Nothing
          else do
            args' <- traverse (rwE f mk lead d) args
            pure (spine (SSig r x) args')
      _ => do
        h' <- rwE f mk lead d h
        args' <- traverse (rwE f mk lead d) args
        pure (spine h' args')
   where
    isReqVar : Nat -> SElem -> Bool
    isReqVar want e = case unPos e of
      SVar _ _ i => i == want
      _ => False
  rwE f mk lead d (SVar r n i) = Just (SVar r n i)
  rwE f mk lead d (SSig r x) = if x == f then Nothing else Just (SSig r x)
  rwE f mk lead d SUnitI = Just SUnitI
  rwE f mk lead d SZeroN = Just SZeroN
  rwE f mk lead d (SSuc t) = SSuc <$> rwE f mk lead d t
  rwE f mk lead d (SLam x t) = SLam x <$> rwE f mk lead (S d) t
  rwE f mk lead d (SLet x e b) = [| SLet (pure x) (rwE f mk lead d e) (rwE f mk lead (S (S d)) b) |]
  rwE f mk lead d (SPair a b) = [| SPair (rwE f mk lead d a) (rwE f mk lead d b) |]
  rwE f mk lead d (SProj1 t) = SProj1 <$> rwE f mk lead d t
  rwE f mk lead d (SProj2 t) = SProj2 <$> rwE f mk lead d t
  rwE f mk lead d SZeroC = Just SZeroC
  rwE f mk lead d SOneC = Just SOneC
  rwE f mk lead d SNatC = Just SNatC
  rwE f mk lead d (SPiC x a b) = [| SPiC (pure x) (rwE f mk lead d a) (rwE f mk lead (S d) b) |]
  rwE f mk lead d (SSigmaC x a b) = [| SSigmaC (pure x) (rwE f mk lead d a) (rwE f mk lead (S d) b) |]
  rwE f mk lead d (SSumC a b) = [| SSumC (rwE f mk lead d a) (rwE f mk lead d b) |]
  rwE f mk lead d (SQuotC a x y r) =
    do a' <- rwE f mk lead d a; r' <- rwE f mk lead (S (S d)) r; pure (SQuotC a' x y r')
  rwE f mk lead d (SEqC rng l r t) =
    do l' <- rwE f mk lead d l
       r' <- rwE f mk lead d r
       t' <- traverse (rwTy f mk lead d) t
       pure (SEqC rng l' r' t')
  rwE f mk lead d (SZeroElim t) = SZeroElim <$> rwE f mk lead d t
  rwE f mk lead d (SNatElim mot z n2 ih s t) = do
    mot' <- traverse (\(n, m) => map (\m' => (n, m')) (rwTy f mk lead (S d) m)) mot
    z' <- rwE f mk lead d z
    s' <- rwE f mk lead (S (S d)) s
    t' <- rwE f mk lead d t
    pure (SNatElim mot' z' n2 ih s' t')
  rwE f mk lead d (SInj1 t) = SInj1 <$> rwE f mk lead d t
  rwE f mk lead d (SInj2 t) = SInj2 <$> rwE f mk lead d t
  rwE f mk lead d (SSumElim mot a l b r t) = do
    mot' <- traverse (\(z, m) => map (\m' => (z, m')) (rwTy f mk lead (S d) m)) mot
    l' <- rwE f mk lead (S d) l
    r' <- rwE f mk lead (S d) r
    t' <- rwE f mk lead d t
    pure (SSumElim mot' a l' b r' t')
  rwE f mk lead d (SClass t) = SClass <$> rwE f mk lead d t
  rwE f mk lead d (SQuotElim mot a g q) = do
    mot' <- traverse (\(z, m) => map (\m' => (z, m')) (rwTy f mk lead (S d) m)) mot
    g' <- rwE f mk lead (S d) g
    q' <- rwE f mk lead d q
    pure (SQuotElim mot' a g' q')
  rwE f mk lead d (SNuC p) = SNuC <$> rwP f mk lead d p
  rwE f mk lead d (SOut e) = SOut <$> rwE f mk lead d e
  rwE f mk lead d (SCorec x a g u) =
    do a' <- rwE f mk lead d a; g' <- rwE f mk lead (S d) g; u' <- rwE f mk lead d u
       pure (SCorec x a' g' u')
  rwE f mk lead d (SCoind nx ny r pw mx my mh q) =
    do r' <- rwE f mk lead (S (S d)) r; pw' <- rwE f mk lead d pw
       q' <- rwE f mk lead (S (S (S d))) q
       pure (SCoind nx ny r' pw' mx my mh q')
  rwE f mk lead d (SSquash t) = SSquash <$> rwTy f mk lead d t
  rwE f mk lead d e@(SStar _) = Just e
  rwE f mk lead d e@(SStarUsing _ _) = Just e
  rwE f mk lead d (SStarWit e) = SStarWit <$> rwE f mk lead d e
  rwE f mk lead d (SChain x ls) =
    do x' <- rwE f mk lead d x
       ls' <- traverse (\(j, y) => do j' <- rwE f mk lead d j
                                      y' <- rwE f mk lead d y
                                      pure (j', y')) ls
       pure (SChain x' ls')
  rwE f mk lead d (SSquashElim e x body) =
    do e' <- rwE f mk lead d e; body' <- rwE f mk lead (S d) body
       pure (SSquashElim e' x body')
  rwE f mk lead d (SAnn e ty) = [| SAnn (rwE f mk lead d e) (rwTy f mk lead d ty) |]
  rwE f mk lead d (SImpArg e) = [| SImpArg (rwE f mk lead d e) |]
  rwE f mk lead d (SNoIns e) = [| SNoIns (rwE f mk lead d e) |]
  rwE f mk lead d e@(SBlank _) = Just e
  rwE f mk lead d (SPos r e) = SPos r <$> rwE f mk lead d e

  rwTy : (f : String) -> (mk : Nat) -> (lead : List Nat) -> Nat -> STy -> Maybe STy
  rwTy f mk lead d STyZero = Just STyZero
  rwTy f mk lead d STyOne = Just STyOne
  rwTy f mk lead d STyNat = Just STyNat
  rwTy f mk lead d STyUniv = Just STyUniv
  rwTy f mk lead d (STySig x) = if x == f then Nothing else Just (STySig x)
  rwTy f mk lead d (STyPi x a b) = [| STyPi (pure x) (rwTy f mk lead d a) (rwTy f mk lead (S d) b) |]
  rwTy f mk lead d (STyImpPi x a b) = [| STyImpPi (pure x) (rwTy f mk lead d a) (rwTy f mk lead (S d) b) |]
  rwTy f mk lead d (STySigma x a b) = [| STySigma (pure x) (rwTy f mk lead d a) (rwTy f mk lead (S d) b) |]
  rwTy f mk lead d (STySum a b) = [| STySum (rwTy f mk lead d a) (rwTy f mk lead d b) |]
  rwTy f mk lead d (STyQuot a x y r) =
    do a' <- rwTy f mk lead d a; r' <- rwE f mk lead (S (S d)) r; pure (STyQuot a' x y r')
  rwTy f mk lead d (STyEq rng l r t) =
    do l' <- rwE f mk lead d l
       r' <- rwE f mk lead d r
       t' <- traverse (rwTy f mk lead d) t
       pure (STyEq rng l' r' t')
  rwTy f mk lead d (STyEl e) = STyEl <$> rwE f mk lead d e
  rwTy f mk lead d (STyPos r t) = STyPos r <$> rwTy f mk lead d t
  rwTy f mk lead d STyProp = Just STyProp
  rwTy f mk lead d (STyNu p) = STyNu <$> rwP f mk lead d p

  rwP : (f : String) -> (mk : Nat) -> (lead : List Nat) -> Nat -> SPoly -> Maybe SPoly
  rwP f mk lead d SPHole = Just SPHole
  rwP f mk lead d (SPConst a) = SPConst <$> rwE f mk lead d a
  rwP f mk lead d (SPProd p q) = [| SPProd (rwP f mk lead d p) (rwP f mk lead d q) |]
  rwP f mk lead d (SPSum p q) = [| SPSum (rwP f mk lead d p) (rwP f mk lead d q) |]
  rwP f mk lead d (SPSigma x a p) = [| SPSigma (pure x) (rwE f mk lead d a) (rwP f mk lead (S d) p) |]
  rwP f mk lead d (SPPi x a p) = [| SPPi (pure x) (rwE f mk lead d a) (rwP f mk lead (S d) p) |]

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

||| Per-clause data: the pattern telescope (outermost first), the
||| resolved pattern skeletons, and the LHS argument spine over the
||| full telescope.
record ClauseData where
  constructor MkClauseData
  csks : List PatSk
  ctele : List (SName, STy)
  cargs : List SElem

buildClauseData : List (String, STy) -> SClause -> Either String ClauseData
buildClauseData cols clause = do
  let (sks, nslots) = assignSlots clause.cpats
  tele <- go 0 [] (map snd cols) sks
  let args = map (patTerm nslots) sks
  if length tele == length clause.cvars
    then Right (MkClauseData sks tele args)
    else Left "internal: pattern telescope disagrees with the parser's"
 where
  -- position by position: transport the column type to the telescope
  -- context (substituting the EARLIER positions' pattern terms — kept
  -- in `past`, most recent first — for the earlier column variables),
  -- then read the position's binder off the pattern
  go : (bound : Nat) -> (past : List PatSk) -> List STy -> List PatSk ->
       Either String (List (SName, STy))
  go bound past [] [] = Right []
  go bound past (a :: as) (sk :: sks) = do
    let a' = remapFreeTy (\d => maybe SUnitI (patTerm bound) (nth d past)) a
    binds <- typePat a' sk
    rest <- go (bound + length binds) (sk :: past) as sks
    pure (binds ++ rest)
  go _ _ _ _ = Left "internal: column/pattern arity mismatch"

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
isVarPat _ = False

||| Linear: no non-wildcard variable occurs twice in one clause's LHS.
linearClause : SClause -> Bool
linearClause c =
  let occs = concatMap patNames c.cpats in
  length (filter (/= wildcard) occs) == length (nub (filter (/= wildcard) occs))
 where
  patNames : SPat -> List String
  patNames (SPVar x) = [fst x]
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
rhoNat : (fname : String) -> (cols : List (String, STy)) -> (b : STy) ->
         (j, k : Nat) -> (zc, sc : SClause) -> (mvar : SName) -> Maybe SElem
rhoNat fname cols b j k zc sc mvar = do
  let kj = minus k j
  -- the Z-clause must not mention f at all
  let False = occursE fname zc.crhs
    | True => Nothing
  -- required leading arguments of a recursive call: the clause's own
  -- column variables (top-level indices k−1 … k−j+1), then the
  -- predecessor (k−j)
  let lead = map (\i => minus k i) [1 .. j]
  sBody <- rwE fname k lead 0 sc.crhs
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
|||   (g : T) → (h₁ : clause₁[g/f]) → … → (x₁:A₁) → … → g x̄ ≡ f x̄ ∈ B
||| The h-binders reuse the clause lemmas' names (display only); the
||| trailing binders are the columns, so the equation's sides
||| determine them — the h's are SIDE CONDITIONS in E's documented
||| sense.
etaType : (fname : String) -> (ty : STy) -> (cols : List (String, STy)) ->
          (b : STy) -> (lemNames : List String) -> (lemTys : List STy) -> STy
etaType fname ty cols b lemNames lemTys =
  let k = length cols
      m = length lemTys
      hyps = the (List (SName, STy))
               (zipWith (\i, nt => ((fst nt, Nothing), replaceSigTy fname "g" i (snd nt)))
                        [0 .. minus m 1] (zip lemNames lemTys))
      colBinds = the (List (SName, STy)) (map (\(x, a) => ((x, Nothing), a)) cols)
      args = map (\i => SVar Nothing (colName i) (minus k i)) [1 .. k]
      concl = STyEq Nothing (spine (SVar Nothing "g" (k + m)) args)
                    (spine (SSig Nothing fname) args) (Just b)
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

etaBodyElim : (fname : String) -> (cols : List (String, STy)) -> (b : STy) ->
              (j, k, m : Nat) -> (lemNames : List String) ->
              (isNat : Bool) -> (v1, v2 : SName) -> SElem
etaBodyElim fname cols b j k m lemNames isNat v1 v2 =
  let kj = minus k j
      trailing = drop j cols
      -- context at the motive's equation: [g, h's, x₁…x_j, x, trailing]
      args = map (\i => SVar Nothing (colName i)
                    (if i < j then (minus k i) + 1
                     else if i == j then kj
                     else minus k i)) [1 .. k]
      concl = STyEq Nothing (spine (SVar Nothing "g" (m + k + 1)) args)
                    (spine (SSig Nothing fname) args)
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
                (etaName : Maybe String) -> (witness : Maybe SElem) ->
                List SClause -> Either String Expansion
expandClausal nrng fname ty etaName witness clauses = do
  -- arity and columns
  k <- case map (length . cpats) clauses of
         [] => Left "at least one clause is required"
         (n :: ns) =>
           if not (all (== n) ns)
             then Left "clauses disagree on the number of pattern positions"
             else if n == 0
               then Left "a clause must spell at least one pattern position"
               else Right n
  (cols, b) <- maybe (Left ("the clauses spell \{show k} pattern positions, "
                            ++ "but the item's type does not show \{show k} leading Π-columns"))
                     Right (peelPis k ty)
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
  cds <- traverse (buildClauseData cols) clauses
  let lemTys = zipWith (mkLemTy cols b k) clauses cds
  -- the λ's here are pure scaffolding over a ⋆ — their binders reuse
  -- the pattern variables' SPANS, which would pull the lemma's
  -- obligations onto a variable inside a pattern. The lemma is about
  -- the CLAUSE, so the scaffolding keeps the display names and drops
  -- the ranges (the Π-binders of `mkLemTy` keep theirs, which is what
  -- ascribes a type to the written pattern variable on hover).
  let lemBodies = map (\cd => wrapSLams (map (\(n, _) => (n, Nothing)) (map fst cd.ctele))
                                        (SStar Nothing)) cds
  let m = length clauses
  let eTy = etaType fname ty cols b lemNames lemTys
  let shape = analyzeShape cols clauses
  let eBodySynth = map (shapedEtaBody cols b k m lemNames) shape
  let eBodyStar = etaBodyStar m k lemNames cols
  let names = fname :: lemNames ++ [etaN]
  case witness of
    Just w =>
      -- WITNESS TIER: existence is the user's; the clause lemmas pay
      -- with ⋆ (undischarged ⋆'s are ordinary obligations), and the
      -- uniqueness proof is still synthesized whenever the clauses
      -- are fragment-shaped — it rewrites by the clause lemmas, never
      -- by unfolding the witness
      Right (MkExpansion
               ((nrng, SDef fname ty w Nothing)
                  -- the clause lemmas hold by the definition's own
                  -- computation: cite its defining equation explicitly
                  -- (the join needs the license to unfold the definition
                  -- it otherwise), and the uniqueness proof cites the
                  -- clause lemmas it rewrites by
                  :: atClauses (zipWith3 (\n, t, b => SDef n t b (Just [fname ++ ".eq"])) lemNames lemTys lemBodies)
                  ++ [(nrng, SDef etaN eTy (fromMaybe eBodyStar eBodySynth) (Just (lemNames ++ map (++ ".rw") lemNames ++ [fname ++ ".eq", "hyp.rw"])))])
               "defined \{fname} by clauses via witness (\{joinBy ", " names})")
    Nothing =>
      case (shape, shape >>= shapedRho cols b k) of
        (Just _, Just rho) =>
          -- THE FRAGMENT: everything synthesized
          Right (MkExpansion
                   ((nrng, SDef fname ty rho Nothing)
                      -- as at the witness tier: clause lemmas cite the
                      -- defining equation, uniqueness cites the clause
                      -- lemmas
                      :: atClauses (zipWith3 (\n, t, b => SDef n t b (Just [fname ++ ".eq"])) lemNames lemTys lemBodies)
                      ++ [(nrng, SDef etaN eTy (fromMaybe eBodyStar eBodySynth) (Just (lemNames ++ map (++ ".rw") lemNames ++ [fname ++ ".eq", "hyp.rw"])))])
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
  ||| The generated per-clause items, each paired with its clause's
  ||| own span (the lists are built by zipping over `clauses`, so they
  ||| are in clause order and of the same length).
  atClauses : List SItem -> List (Maybe Range, SItem)
  atClauses = zip (map crange clauses)

  ||| Π(Γᵢ). f p̄ᵢ ≡ tᵢ ∈ B[p̄ᵢ] — the clause, Π-closed over its pattern
  ||| telescope; recursive occurrences in tᵢ stay references to f.
  mkLemTy : List (String, STy) -> STy -> Nat -> SClause -> ClauseData -> STy
  mkLemTy cols b k clause cd =
    let bigL = length cd.ctele
        lhs = spine (SSig Nothing fname) cd.cargs
        bC = remapFreeTy (\d => maybe SUnitI (patTerm bigL) (nth d (reverse cd.csks))) b
    in wrapSPis cd.ctele (STyEq Nothing lhs clause.crhs (Just bC))

  shapedRho : List (String, STy) -> STy -> Nat -> Shape -> Maybe SElem
  shapedRho cols b k (ShNone c) = rhoNone fname c
  shapedRho cols b k (ShNat j zc sc mvar) = rhoNat fname cols b j k zc sc mvar
  shapedRho cols b k (ShSum j lc avar rc bvar) = rhoSum fname cols b j k lc avar rc bvar

  shapedEtaBody : List (String, STy) -> STy -> Nat -> Nat -> List String -> Shape -> SElem
  shapedEtaBody cols b k m lemNames (ShNone _) = etaBodyStar m k lemNames cols
  shapedEtaBody cols b k m lemNames (ShNat j _ sc mvar) =
    etaBodyElim fname cols b j k m lemNames True mvar ("ih", Nothing)
  shapedEtaBody cols b k m lemNames (ShSum j _ avar _ bvar) =
    etaBodyElim fname cols b j k m lemNames False avar bvar
