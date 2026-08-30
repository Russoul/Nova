module Nova.Elaboration.Surface

-- The INDEXED SURFACE AST of docs/NovaElaboration.txt.
--
-- This is what the elaboration parser produces and what the elaborator
-- consumes: variables are already de Bruijn indices (name resolution is
-- a front-end concern, done during parsing), but the tree is still
-- surface, not core — it carries ascriptions `(t : T)` and inline
-- eliminator motives, which core syntax (Nova.Kernel.Syntax) lacks.
-- Elaboration erases those. Binder names are retained purely as display
-- metadata for the obligation report; no rule ever consults them.

import Data.SnocList
import Data.String

import Me.Russoul.Text.Range

%default total

||| A binder-position name with its source span (display metadata —
||| the LSP ascribes elaborated types to binder occurrences).
public export
SName : Type
SName = (String, Maybe Range)

mutual
  public export
  data STy : Type where
    STyZero : STy
    STyOne : STy
    STyNat : STy
    STyUniv : STy
    ||| x — reference to a signature type definition
    STySig : String -> STy
    ||| (x:T) → U
    STyPi : (name : String) -> STy -> STy -> STy
    ||| {x:T} → U — an IMPLICIT Π-binder (docs/NovaPerfectSurface.txt,
    ||| Phase 3): elaborates exactly as STyPi (the core is bare — no
    ||| implicitness reaches the theory), but a def whose type carries
    ||| leading-telescope implicit binders has those argument positions
    ||| INSERTED at application sites, recovered by the rigid
    ||| first-order oracle; `f {t}` overrides the next implicit
    ||| position explicitly
    STyImpPi : (name : String) -> STy -> STy -> STy
    ||| (x:T) × U
    STySigma : (name : String) -> STy -> STy -> STy
    ||| T ⊎ U — non-dependent, no binder
    STySum : STy -> STy -> STy
    ||| T / (x y. r) — r is an Ω-valued element
    STyQuot : STy -> (nx, ny : SName) -> SElem -> STy
    ||| t ≡ t (∈ T)? — the ∈-annotation is OPTIONAL
    ||| (docs/NovaPerfectSurface.txt, Phase 4): when absent, the
    ||| domain is recovered by INFERRING a side (left first); the
    ||| range keys the distiller's elision trial
    STyEq : Maybe Range -> SElem -> SElem -> Maybe STy -> STy
    ||| El t
    STyEl : SElem -> STy
    ||| Ω
    STyProp : STy
    ||| ν F — the coinductive type at a surface polynomial
    STyNu : SPoly -> STy
    ||| T@r — a source span on a type; transparent, like `SPos`
    STyPos : Range -> STy -> STy

  ||| Surface polynomials — the one-hole codes of Foundation's
  ||| coinductive section. External pieces are element-level CODES; a
  ||| left-hand (x:t) binds x in the body.
  public export
  data SPoly : Type where
    ||| 𝕏 — the hole
    SPHole : SPoly
    ||| K t — constant at a code
    SPConst : SElem -> SPoly
    ||| F × G — product (non-binding)
    SPProd : SPoly -> SPoly -> SPoly
    ||| F ⊎ G — sum
    SPSum : SPoly -> SPoly -> SPoly
    ||| (x:t) × F — dependent pair over external data (binds)
    SPSigma : (x : SName) -> SElem -> SPoly -> SPoly
    ||| (x:t) → F — exponent with external domain (binds)
    SPPi : (x : SName) -> SElem -> SPoly -> SPoly

  public export
  data SElem : Type where
    ||| ☐ᵢ — a resolved local variable (the parser resolved the name)
    SVar : Maybe Range -> (name : String) -> Nat -> SElem
    ||| x — an identifier that resolved to no local binder: a
    ||| signature reference (locals shadow the signature)
    SSig : Maybe Range -> String -> SElem
    SUnitI : SElem
    SZeroN : SElem
    SSuc : SElem -> SElem
    ||| λx. t
    SLam : (name : SName) -> SElem -> SElem
    ||| let x ≔ e in b — the body binds x (the definiens' value); the
    ||| unfolding-equation binder of the core form (el-let) is inserted
    ||| by elaboration and has no surface spelling. An annotated
    ||| definiens (let x : T ≔ e in b) is parse-level sugar for
    ||| let x ≔ (e : T) in b.
    SLet : (name : SName) -> SElem -> SElem -> SElem
    SApp : SElem -> SElem -> SElem
    SPair : SElem -> SElem -> SElem
    SProj1 : SElem -> SElem
    SProj2 : SElem -> SElem
    ||| universe codes 𝟘 𝟙 ℕ
    SZeroC : SElem
    SOneC : SElem
    SNatC : SElem
    ||| (x:t) → u  (code)
    SPiC : (name : String) -> SElem -> SElem -> SElem
    ||| (x:t) × u  (code)
    SSigmaC : (name : String) -> SElem -> SElem -> SElem
    ||| t ⊎ u  (code — non-dependent, no binder)
    SSumC : SElem -> SElem -> SElem
    ||| t / (x y. r)  (code)
    SQuotC : SElem -> (nx, ny : SName) -> SElem -> SElem
    ||| t ≡ t (∈ T)? — the equality PROP (an Ω-element; the ∈-slot
    ||| embeds a TYPE, like ∥-∥); the ∈-annotation is optional, as at
    ||| the type level
    SEqC : Maybe Range -> SElem -> SElem -> Maybe STy -> SElem
    SZeroElim : SElem -> SElem
    ||| ℕ-elim (n. T)? z (n ih. s) t — motive-first; the motive is
    ||| OPTIONAL in checking position (docs/NovaPerfectSurface.txt,
    ||| Phase 4): when absent it is recovered by abstracting the
    ||| scrutinee in the expected type
    SNatElim : Maybe (SName, STy) -> SElem -> (n2, ih : SName) -> SElem -> SElem -> SElem
    ||| inj₁ t / inj₂ t — sum introductions
    SInj1 : SElem -> SElem
    SInj2 : SElem -> SElem
    ||| ⊎-elim (z. T)? (a. l) (b. r) t — motive, left case, right
    ||| case, scrutinee; motive optional in checking position
    SSumElim : Maybe (SName, STy) -> (a : SName) -> SElem -> (b : SName) -> SElem -> SElem -> SElem
    SClass : SElem -> SElem
    ||| quot-elim (z. T)? (a. f) q — motive-first; motive optional in
    ||| checking position
    SQuotElim : Maybe (SName, STy) -> (a : SName) -> SElem -> SElem -> SElem
    ||| ν F — the ν CODE (infers at 𝕌)
    SNuC : SPoly -> SElem
    ||| out t — the coinductive observation (infers, like the
    ||| projections)
    SOut : SElem -> SElem
    ||| corec (x : a. f) u — carrier code inline as a binder
    ||| annotation; checking-only (the polynomial comes from the
    ||| expected ν-type)
    SCorec : (x : SName) -> SElem -> SElem -> SElem -> SElem
    ||| coind (x y. R) p (x y h. q) — COINDUCTION (el-nu-coind),
    ||| checked at (l ≡ r ∈ ν F): invariant R (Ω-valued,
    ||| over the two sides), p a proof of R l r, q the one-step
    ||| closure — under generic x y and h : R x y, a proof
    ||| that the observations are lift_𝔽(R)-related
    SCoind : (nx, ny : SName) -> SElem -> SElem ->
             (mx, my, mh : SName) -> SElem -> SElem
    ||| ∥T∥ — squash: proposition from an arbitrary type
    SSquash : STy -> SElem
    ||| ⋆ — the canonical proof of a true proposition (evident 𝟙-/
    ||| ≡-shaped squashees only; the witness is auto-synthesized)
    ||| the range (when source-written) feeds the LSP hover: a ⋆
    ||| ascribed with the proposition it proved. Show ignores it, like
    ||| every other carried range
    SStar : Maybe Range -> SElem
    ||| ⋆ e — el-squash-i with an explicit witness: e proves the
    ||| squashee directly, for squashees of any shape
    SStarWit : SElem -> SElem
    ||| ⋆ using n / ⋆ using (n, …) — the canonical proof with a SCOPED
    ||| discharge: only the named Σ lemmas (plus the hypotheses of Γ)
    ||| participate in the equation's discharge, so acceptance of the
    ||| site depends on nothing else in the store — deterministic and
    ||| module-local (docs/SearchlessElaboration.md §5.3). Names are
    ||| surface spellings, resolved against Σ at elaboration time.
    SStarUsing : Maybe Range -> List String -> SElem
    ||| squash-elim e (x. body) — el-squash-e-prf: eliminate a proof of
    ||| a squashed proposition into a further proposition, via a
    ||| hypothetical inhabitant x of the raw squashee
    SSquashElim : SElem -> (name : SName) -> SElem -> SElem
    ||| x ≡⟨ e ⟩ y ≡⟨ e' ⟩ z — a CALC CHAIN
    ||| (docs/SearchlessElaboration.md §5.2), checking-only at
    ||| (l ≡ r ∈ A): the head and each subsequent term are
    ||| midpoints (each stated once), and each link's justification e
    ||| is an INFERABLE proof of some equation; the adjacency between
    ||| consecutive midpoints is discharged by computation plus that
    ||| one reflected equation (plus hypotheses) — never the global
    ||| store. Erases to ⋆, like every equality proof.
    SChain : SElem -> List (SElem, SElem) -> SElem
    ||| (t : T) — ascription; the lever into inference mode
    SAnn : SElem -> STy -> SElem
    ||| {t} — an explicit override for the next IMPLICIT binder
    ||| position of the applied definition; legal only as an
    ||| application argument (elaboration rejects it anywhere else)
    SImpArg : SElem -> SElem
    ||| _ — a BLANK: a per-site elided argument at an EXPLICIT Π
    ||| position of an applied definition, recovered by the same
    ||| oracle as an inserted implicit (docs/NovaPerfectSurface.txt,
    ||| Phase 4). Legal only as a direct application argument; at an
    ||| implicit position it is a structural error (those are elided
    ||| by default — {t} overrides them)
    SBlank : Maybe Range -> SElem
    ||| t@r — a SOURCE SPAN on a term. Transparent: it carries no
    ||| meaning, `Show` skips it, and every structural test goes
    ||| through `unPos`. The parser attaches one at every grammar
    ||| level, so an elaboration error can name the exact
    ||| sub-expression it is about rather than the whole item
    SPos : Range -> SElem -> SElem
    ||| f {} — the NO-INSERT marker: suppress trailing-implicit
    ||| insertion at this reference/spine (the function-passing form:
    ||| a checking-position reference of an implicit-binder def
    ||| otherwise inserts its implicit run and solves it from the
    ||| expected type — docs/NovaPerfectSurface.txt, Phase 3d)
    SNoIns : SElem -> SElem

-- ===== Source spans =====
--
-- `SPos`/`STyPos` are TRANSPARENT: they carry a source range and
-- nothing else. The parser attaches one at every grammar level (so
-- every sub-expression has an exact span, from a bare `Z` to a whole
-- application chain), the elaborator narrows the reported site to
-- them as it descends, and everything else strips them — `Show` skips
-- them, so the distiller's AST-identity contract is unaffected, and
-- every structural test on a term goes through `unPos`.

||| Attach a span. A level of the grammar that adds no node of its own
||| hands its child straight back, so re-wrapping REPLACES rather than
||| nests — the two spans coincide there anyway.
public export
atPos : Maybe Range -> SElem -> SElem
atPos Nothing e = e
atPos (Just r) (SPos _ e) = SPos r e
atPos (Just r) e = SPos r e

public export
atPosTy : Maybe Range -> STy -> STy
atPosTy Nothing t = t
atPosTy (Just r) (STyPos _ t) = STyPos r t
atPosTy (Just r) t = STyPos r t

||| Peel the spans off the front of a term. EVERY structural test on a
||| surface term goes through this: a span is metadata, never part of
||| a term's shape.
public export
unPos : SElem -> SElem
unPos (SPos _ e) = unPos e
unPos e = e

public export
unPosTy : STy -> STy
unPosTy (STyPos _ t) = unPosTy t
unPosTy t = t

public export
posOf : SElem -> Maybe Range
posOf (SPos r _) = Just r
posOf _ = Nothing

public export
posOfTy : STy -> Maybe Range
posOfTy (STyPos r _) = Just r
posOfTy _ = Nothing

-- The printer and the AST rewriters have no use for spans and inspect
-- term SHAPES freely, including a child's; rather than teach every
-- one of them to look through a wrapper, they take a stripped tree.

mutual
  ||| Remove every span, at every depth.
  public export
  covering
  stripPos : SElem -> SElem
  stripPos (SPos _ e) = stripPos e
  stripPos e@(SVar _ _ _) = e
  stripPos e@(SSig _ _) = e
  stripPos SUnitI = SUnitI
  stripPos SZeroN = SZeroN
  stripPos (SSuc t) = SSuc (stripPos t)
  stripPos (SLam x b) = SLam x (stripPos b)
  stripPos (SLet x d b) = SLet x (stripPos d) (stripPos b)
  stripPos (SApp f a) = SApp (stripPos f) (stripPos a)
  stripPos (SPair a b) = SPair (stripPos a) (stripPos b)
  stripPos (SProj1 t) = SProj1 (stripPos t)
  stripPos (SProj2 t) = SProj2 (stripPos t)
  stripPos SZeroC = SZeroC
  stripPos SOneC = SOneC
  stripPos SNatC = SNatC
  stripPos (SPiC x a b) = SPiC x (stripPos a) (stripPos b)
  stripPos (SSigmaC x a b) = SSigmaC x (stripPos a) (stripPos b)
  stripPos (SSumC a b) = SSumC (stripPos a) (stripPos b)
  stripPos (SQuotC a x y r) = SQuotC (stripPos a) x y (stripPos r)
  stripPos (SEqC rng l r t) = SEqC rng (stripPos l) (stripPos r) (map stripPosTy t)
  stripPos (SZeroElim t) = SZeroElim (stripPos t)
  stripPos (SNatElim mot z n2 ih st t) =
    SNatElim (map (\(n, m) => (n, stripPosTy m)) mot) (stripPos z) n2 ih (stripPos st) (stripPos t)
  stripPos (SInj1 t) = SInj1 (stripPos t)
  stripPos (SInj2 t) = SInj2 (stripPos t)
  stripPos (SSumElim mot a l b r t) =
    SSumElim (map (\(z, m) => (z, stripPosTy m)) mot) a (stripPos l) b (stripPos r) (stripPos t)
  stripPos (SClass t) = SClass (stripPos t)
  stripPos (SQuotElim mot a f q) =
    SQuotElim (map (\(z, m) => (z, stripPosTy m)) mot) a (stripPos f) (stripPos q)
  stripPos (SNuC f) = SNuC (stripPosPoly f)
  stripPos (SOut t) = SOut (stripPos t)
  stripPos (SCorec x a f u) = SCorec x (stripPos a) (stripPos f) (stripPos u)
  stripPos (SCoind nx ny r pw mx my mh q) =
    SCoind nx ny (stripPos r) (stripPos pw) mx my mh (stripPos q)
  stripPos (SSquash t) = SSquash (stripPosTy t)
  stripPos e@(SStar _) = e
  stripPos (SStarWit e) = SStarWit (stripPos e)
  stripPos e@(SStarUsing _ _) = e
  stripPos (SSquashElim e x b) = SSquashElim (stripPos e) x (stripPos b)
  stripPos (SChain h ls) = SChain (stripPos h) (map (\(j, m) => (stripPos j, stripPos m)) ls)
  stripPos (SAnn t ty) = SAnn (stripPos t) (stripPosTy ty)
  stripPos (SImpArg t) = SImpArg (stripPos t)
  stripPos (SNoIns t) = SNoIns (stripPos t)
  stripPos e@(SBlank _) = e

  public export
  covering
  stripPosTy : STy -> STy
  stripPosTy (STyPos _ t) = stripPosTy t
  stripPosTy STyZero = STyZero
  stripPosTy STyOne = STyOne
  stripPosTy STyNat = STyNat
  stripPosTy STyUniv = STyUniv
  stripPosTy t@(STySig _) = t
  stripPosTy (STyPi x a b) = STyPi x (stripPosTy a) (stripPosTy b)
  stripPosTy (STyImpPi x a b) = STyImpPi x (stripPosTy a) (stripPosTy b)
  stripPosTy (STySigma x a b) = STySigma x (stripPosTy a) (stripPosTy b)
  stripPosTy (STySum a b) = STySum (stripPosTy a) (stripPosTy b)
  stripPosTy (STyQuot a x y r) = STyQuot (stripPosTy a) x y (stripPos r)
  stripPosTy (STyEq rng l r t) = STyEq rng (stripPos l) (stripPos r) (map stripPosTy t)
  stripPosTy (STyEl e) = STyEl (stripPos e)
  stripPosTy STyProp = STyProp
  stripPosTy (STyNu f) = STyNu (stripPosPoly f)

  public export
  covering
  stripPosPoly : SPoly -> SPoly
  stripPosPoly SPHole = SPHole
  stripPosPoly (SPConst e) = SPConst (stripPos e)
  stripPosPoly (SPProd f g) = SPProd (stripPosPoly f) (stripPosPoly g)
  stripPosPoly (SPSum f g) = SPSum (stripPosPoly f) (stripPosPoly g)
  stripPosPoly (SPSigma x a f) = SPSigma x (stripPos a) (stripPosPoly f)
  stripPosPoly (SPPi x a f) = SPPi x (stripPos a) (stripPosPoly f)


--
-- Only a handful of nodes record a range of their own: the leaves a
-- name resolves at (SVar/SSig), the elided-sugar keys (SEqC/STyEq),
-- the proof atoms (SStar/SStarUsing/SBlank) and every binder name.
-- That is enough to place an error INSIDE an item without giving
-- every node a span of its own: a compound's position is its HEAD's —
-- the leftmost leaf of an application or projection spine, the binder
-- of an abstraction, the scrutinee of an eliminator. `headRange`
-- reads it off, and the elaborator narrows the reported site to it as
-- it descends (see `Nova.Elaboration.Site`).
--
-- Nothing means "no better idea than the enclosing item" — never a
-- wrong position.

mutual
  public export
  headRange : SElem -> Maybe Range
  headRange (SPos r _) = Just r
  headRange (SVar r _ _) = r
  headRange (SSig r _) = r
  headRange (SStar r) = r
  headRange (SStarUsing r _) = r
  headRange (SBlank r) = r
  headRange (SEqC r _ _ _) = r
  headRange SUnitI = Nothing
  headRange SZeroN = Nothing
  headRange SZeroC = Nothing
  headRange SOneC = Nothing
  headRange SNatC = Nothing
  -- spines and wrappers: the head carries the position
  -- an argument's span is better than none: a head with no range
  -- of its own (a numeral, say) still places the spine
  headRange (SApp f e) = headRange f <|> headRange e
  headRange (SProj1 t) = headRange t
  headRange (SProj2 t) = headRange t
  headRange (SNoIns t) = headRange t
  headRange (SImpArg t) = headRange t
  headRange (SAnn t _) = headRange t
  headRange (SSuc t) = headRange t
  headRange (SInj1 t) = headRange t
  headRange (SInj2 t) = headRange t
  headRange (SClass t) = headRange t
  headRange (SZeroElim t) = headRange t
  headRange (SOut t) = headRange t
  headRange (SStarWit e) = headRange e
  headRange (SPair a b) = headRange a <|> headRange b
  headRange (SChain h _) = headRange h
  headRange (SSquash t) = headRangeTy t
  headRange (SSquashElim e _ _) = headRange e
  headRange (SNuC f) = headRangePoly f
  headRange (SSumC a b) = headRange a <|> headRange b
  headRange (SPiC _ a _) = headRange a
  headRange (SSigmaC _ a _) = headRange a
  headRange (SQuotC a _ _ _) = headRange a
  -- binders: the bound name's own span
  headRange (SLam (_, r) _) = r
  headRange (SLet (_, r) _ _) = r
  headRange (SCorec (_, r) _ _ _) = r
  headRange (SCoind (_, r) _ _ _ _ _ _ _) = r
  -- eliminators: the motive binder when written, the scrutinee's head
  -- otherwise (a motive-less eliminator is checking-position sugar)
  headRange (SNatElim (Just ((_, r), _)) _ _ _ _ _) = r
  headRange (SNatElim Nothing _ _ _ _ t) = headRange t
  headRange (SSumElim (Just ((_, r), _)) _ _ _ _ _) = r
  headRange (SSumElim Nothing _ _ _ _ t) = headRange t
  headRange (SQuotElim (Just ((_, r), _)) _ _ _) = r
  headRange (SQuotElim Nothing _ _ q) = headRange q

  public export
  headRangeTy : STy -> Maybe Range
  headRangeTy (STyPos r _) = Just r
  headRangeTy (STyEq r _ _ _) = r
  headRangeTy (STyEl e) = headRange e
  headRangeTy (STyPi _ a _) = headRangeTy a
  headRangeTy (STyImpPi _ a _) = headRangeTy a
  headRangeTy (STySigma _ a _) = headRangeTy a
  headRangeTy (STySum a b) = headRangeTy a <|> headRangeTy b
  headRangeTy (STyQuot a _ _ _) = headRangeTy a
  headRangeTy (STyNu f) = headRangePoly f
  headRangeTy STyZero = Nothing
  headRangeTy STyOne = Nothing
  headRangeTy STyNat = Nothing
  headRangeTy STyUniv = Nothing
  headRangeTy STyProp = Nothing
  headRangeTy (STySig _) = Nothing

  public export
  headRangePoly : SPoly -> Maybe Range
  headRangePoly SPHole = Nothing
  headRangePoly (SPConst e) = headRange e
  headRangePoly (SPProd f g) = headRangePoly f <|> headRangePoly g
  headRangePoly (SPSum f g) = headRangePoly f <|> headRangePoly g
  headRangePoly (SPSigma (_, r) _ _) = r
  headRangePoly (SPPi (_, r) _ _) = r

-- ===== Weakening =====
--
-- Shift every variable index ≥ the cutoff up by one. This is how a
-- multi-name binder group desugars — `(x y : A) → B` binds y at the
-- SAME written domain, which sits one binder deeper, so its indices
-- shift (the group's names never scope over each other's domains) —
-- and how the printer recognizes a groupable telescope (the domains
-- are shift-equal). Binder arities mirror the parser's environment
-- pushes exactly (a let pushes TWO slots: the value and the unfolding
-- hypothesis).

mutual
  public export
  covering
  shiftElem : (c : Nat) -> SElem -> SElem
  shiftElem c (SVar r x i) = SVar r x (if i >= c then S i else i)
  shiftElem c e@(SSig _ _) = e
  shiftElem c SUnitI = SUnitI
  shiftElem c SZeroN = SZeroN
  shiftElem c (SSuc t) = SSuc (shiftElem c t)
  shiftElem c (SLam x b) = SLam x (shiftElem (S c) b)
  shiftElem c (SLet x d b) = SLet x (shiftElem c d) (shiftElem (S (S c)) b)
  shiftElem c (SApp f a) = SApp (shiftElem c f) (shiftElem c a)
  shiftElem c (SPair a b) = SPair (shiftElem c a) (shiftElem c b)
  shiftElem c (SProj1 t) = SProj1 (shiftElem c t)
  shiftElem c (SProj2 t) = SProj2 (shiftElem c t)
  shiftElem c SZeroC = SZeroC
  shiftElem c SOneC = SOneC
  shiftElem c SNatC = SNatC
  shiftElem c (SPiC x a b) = SPiC x (shiftElem c a) (shiftElem (S c) b)
  shiftElem c (SSigmaC x a b) = SSigmaC x (shiftElem c a) (shiftElem (S c) b)
  shiftElem c (SSumC a b) = SSumC (shiftElem c a) (shiftElem c b)
  shiftElem c (SQuotC a x y r) = SQuotC (shiftElem c a) x y (shiftElem (S (S c)) r)
  shiftElem c (SEqC rng l r t) = SEqC rng (shiftElem c l) (shiftElem c r) (map (shiftTy c) t)
  shiftElem c (SZeroElim t) = SZeroElim (shiftElem c t)
  shiftElem c (SNatElim mot z n2 ih s t) =
    SNatElim (map (\(n, m) => (n, shiftTy (S c) m)) mot) (shiftElem c z) n2 ih (shiftElem (S (S c)) s) (shiftElem c t)
  shiftElem c (SInj1 t) = SInj1 (shiftElem c t)
  shiftElem c (SInj2 t) = SInj2 (shiftElem c t)
  shiftElem c (SSumElim mot a l b r t) =
    SSumElim (map (\(z, m) => (z, shiftTy (S c) m)) mot) a (shiftElem (S c) l) b (shiftElem (S c) r) (shiftElem c t)
  shiftElem c (SClass t) = SClass (shiftElem c t)
  shiftElem c (SQuotElim mot a f q) =
    SQuotElim (map (\(z, m) => (z, shiftTy (S c) m)) mot) a (shiftElem (S c) f) (shiftElem c q)
  shiftElem c (SNuC f) = SNuC (shiftPoly c f)
  shiftElem c (SOut t) = SOut (shiftElem c t)
  shiftElem c (SCorec x a f u) = SCorec x (shiftElem c a) (shiftElem (S c) f) (shiftElem c u)
  shiftElem c (SCoind nx ny r pw mx my mh q) =
    SCoind nx ny (shiftElem (S (S c)) r) (shiftElem c pw) mx my mh (shiftElem (S (S (S c))) q)
  shiftElem c (SSquash t) = SSquash (shiftTy c t)
  shiftElem c e@(SStar _) = e
  shiftElem c (SStarWit e) = SStarWit (shiftElem c e)
  shiftElem c e@(SStarUsing _ _) = e
  shiftElem c (SSquashElim e x b) = SSquashElim (shiftElem c e) x (shiftElem (S c) b)
  shiftElem c (SChain h links) =
    SChain (shiftElem c h) (map (\(j, m) => (shiftElem c j, shiftElem c m)) links)
  shiftElem c (SAnn t ty) = SAnn (shiftElem c t) (shiftTy c ty)
  shiftElem c (SImpArg t) = SImpArg (shiftElem c t)
  shiftElem c (SNoIns t) = SNoIns (shiftElem c t)
  shiftElem c e@(SBlank _) = e
  shiftElem c (SPos r e) = SPos r (shiftElem c e)

  public export
  covering
  shiftTy : (c : Nat) -> STy -> STy
  shiftTy c STyZero = STyZero
  shiftTy c STyOne = STyOne
  shiftTy c STyNat = STyNat
  shiftTy c STyUniv = STyUniv
  shiftTy c t@(STySig _) = t
  shiftTy c (STyPi x a b) = STyPi x (shiftTy c a) (shiftTy (S c) b)
  shiftTy c (STyImpPi x a b) = STyImpPi x (shiftTy c a) (shiftTy (S c) b)
  shiftTy c (STySigma x a b) = STySigma x (shiftTy c a) (shiftTy (S c) b)
  shiftTy c (STySum a b) = STySum (shiftTy c a) (shiftTy c b)
  shiftTy c (STyQuot a x y r) = STyQuot (shiftTy c a) x y (shiftElem (S (S c)) r)
  shiftTy c (STyEq rng l r t) = STyEq rng (shiftElem c l) (shiftElem c r) (map (shiftTy c) t)
  shiftTy c (STyEl e) = STyEl (shiftElem c e)
  shiftTy c STyProp = STyProp
  shiftTy c (STyNu f) = STyNu (shiftPoly c f)
  shiftTy c (STyPos r t) = STyPos r (shiftTy c t)

  public export
  covering
  shiftPoly : (c : Nat) -> SPoly -> SPoly
  shiftPoly c SPHole = SPHole
  shiftPoly c (SPConst e) = SPConst (shiftElem c e)
  shiftPoly c (SPProd f g) = SPProd (shiftPoly c f) (shiftPoly c g)
  shiftPoly c (SPSum f g) = SPSum (shiftPoly c f) (shiftPoly c g)
  shiftPoly c (SPSigma x a f) = SPSigma x (shiftElem c a) (shiftPoly (S c) f)
  shiftPoly c (SPPi x a f) = SPPi x (shiftElem c a) (shiftPoly (S c) f)

-- ===== Operators are names =====
--
-- An operator token (+, *, ⊕, ...) IS a Σ-name: `def + : ... ≔ ...`
-- defines it, `infixl 6 +` gives it fixity, and infix use desugars to
-- application of that name. There is no notation-to-name mapping and
-- therefore no resugaring problem — the printer prints the name, and
-- the name is the operator.

public export
data Assoc = AssocL | AssocR

public export
Eq Assoc where
  AssocL == AssocL = True
  AssocR == AssocR = True
  _ == _ = False

||| operator token ↦ (associativity, binding level 0..9); higher binds
||| tighter
public export
FixTable : Type
FixTable = List (String, Assoc, Nat)

||| The operator alphabet. Excludes the reserved theory tokens
||| (→ × ≡ ∈ ≔ / . , : parens) — and `|`, the clause marker of the
||| clausal def item — and comment dashes are eaten by the lexer, so
||| no operator may contain "--".
public export
opChar : Char -> Bool
opChar c = c `elem` unpack "+-*<>=&!?%^~@#⊕⊗⊙⊞⊟∙∘·≤≥∸⧺⊥⊤∧∨⊃¬↔"

||| Is the (possibly qualified) name operator-shaped? Decided by its
||| final segment.
public export
isOpName : String -> Bool
isOpName x = any opChar (lastSegment (unpack x))
 where
  lastSegment : List Char -> List Char
  lastSegment [] = []
  lastSegment ('.' :: rest) = lastSegment rest
  lastSegment (c :: rest) = if elem '.' rest then lastSegment rest else c :: rest

||| import M            — M's names accessible qualified (M.x) only
||| import M (a, b)     — additionally, a and b accessible bare
public export
record SImport where
  constructor MkSImport
  mname : String
  opens : List String
  ||| the import line's own span — a load failure blamed on this
  ||| import (unreadable module, missing opened name, cycle) points
  ||| HERE rather than at the importing file as a whole
  irange : Maybe Range

-- ===== QIIT signature literals (the data item) =====

public export
data SQTm : Type where
  ||| a ToS reference, resolved by the parser to a ⬡-index (relative to
  ||| the surrounding entry's inductive binders + the literal's earlier
  ||| entries); the name is display metadata
  SQVar : String -> Nat -> SQTm
  ||| application to an EXTERNAL argument (an ordinary surface element
  ||| over the external binders in scope)
  SQAppE : SQTm -> SElem -> SQTm
  ||| application to an INDUCTIVE argument
  SQAppI : SQTm -> SQTm -> SQTm

public export
data SQRes : Type where
  ||| … → U — a SORT
  SQResU : SQRes
  ||| … → El q — a POINT constructor
  SQResEl : SQTm -> SQRes
  ||| … → l ≡ r ∈ El q — an EQUATION constructor
  SQResEq : SQTm -> SQTm -> SQTm -> SQRes

public export
record SQDecl where
  constructor MkSQDecl
  dqname : String
  ||| binders in order: Left = EXTERNAL domain (a surface type over the
  ||| external zone), Right = INDUCTIVE domain (a sort code)
  dqbinders : List (String, Either STy SQTm)
  dqres : SQRes

-- ===== Defining equations (the clausal def item) =====

||| A clause LHS pattern (docs/NovaElaboration.txt, "Defining
||| equations"): constructor spellings and variables, any depth — the
||| structural FRAGMENT demands depth 1, the grammar does not.
public export
data SPat : Type where
  SPVar : SName -> SPat
  SPZero : SPat
  SPSuc : SPat -> SPat
  SPInj1 : SPat -> SPat
  SPInj2 : SPat -> SPat

||| One defining equation: `| lhs ≔ rhs [name]?`. The LHS patterns
||| cover the leading columns of the item's type; `cvars` is the
||| binder telescope the patterns spell — one slot per variable in
||| order of first appearance (a wildcard is always a fresh slot, a
||| repeated name reuses its slot — nonlinear LHSs are expressible,
||| the fragment rejects them). The RHS is parsed in exactly that
||| environment.
public export
record SClause where
  constructor MkSClause
  cpats : List SPat
  cvars : List SName
  crhs : SElem
  ||| the [name] override for this clause's equation lemma
  cname : Maybe String
  ||| the clause's own source span. The item macro expands each clause
  ||| into an equation lemma of its own, and that lemma is ABOUT this
  ||| clause — it is where its obligations and failures belong
  crange : Maybe Range

public export
data SItem : Type where
  ||| def x : T (using (n, …))? ≔ t — always in the empty context.
  ||| The optional using-clause scopes EVERY discharge of the item to
  ||| the named Σ lemmas plus hypotheses
  ||| (docs/SearchlessElaboration.md §5.3)
  SDef : String -> STy -> SElem -> Maybe (List String) -> SItem
  ||| def x : T — a DECLARATION: a def without a definiens, entering Σ
  ||| as a sig-decl and reported as an open declaration (the name's
  ||| span is kept for diagnostics)
  SDeclDef : (nrng : Maybe Range) -> String -> STy -> SItem
  ||| type x ≔ T — always in the empty context
  STypeDef : String -> STy -> SItem
  ||| data [x : T]* ( n : Q ; … ) — a QIIT signature literal over an
  ||| ambient PARAMETER telescope (Foundation's Γ ⊦ 𝒮 qsig); an ITEM
  ||| MACRO that expands into a batch of ordinary defs, each
  ||| Π-abstracted over the parameters (docs/NovaElaboration.txt,
  ||| QIIT section)
  SData : List (String, STy) -> List SQDecl -> SItem
  ||| def x : T [eta]? (≔ t)? clause+ — a def with DEFINING EQUATIONS
  ||| (docs/NovaElaboration.txt, "Defining equations"): an ITEM MACRO
  ||| expanding into the definition proper (a synthesized eliminator
  ||| body, the user's witness t, or a declaration), one Π-closed
  ||| equation lemma per clause, and the pointwise uniqueness lemma
  ||| (named by the [eta] override)
  SClausalDef : (nrng : Maybe Range) -> String -> STy ->
                (etaName : Maybe String) -> (witness : Maybe SElem) ->
                List SClause -> SItem

||| One fixity declaration as written: (operator, associativity, level).
public export
SFixity : Type
SFixity = (String, Assoc, Nat)

||| A file-body entry in source order: a fixity declaration or an item
||| (with its item-level source range). Fixities take effect for the
||| rest of the file, so faithful re-printing must preserve the
||| interleaving — a hoisted fixity could re-classify an earlier
||| prefix use of its operator as infix-only
||| (docs/NovaPerfectSurface.txt, Phase 1).
public export
SBodyEntry : Type
SBodyEntry = Either (Maybe Range, SFixity) (Maybe Range, SItem)

||| An item with every span removed. The PRINTER takes one: it
||| inspects term shapes freely, a child's included, and a span
||| between a node and its parent would defeat those tests. Stripping
||| once at the boundary keeps every one of them written against bare
||| syntax (`Nova.Distill`).
export
covering
stripPosItem : SItem -> SItem
stripPosItem (SDef n ty body mu) = SDef n (stripPosTy ty) (stripPos body) mu
stripPosItem (SDeclDef r n ty) = SDeclDef r n (stripPosTy ty)
stripPosItem (STypeDef n ty) = STypeDef n (stripPosTy ty)
stripPosItem (SData ps ds) =
  SData (map (\(x, t) => (x, stripPosTy t)) ps) (map stripQDecl ds)
 where
  stripQDecl : SQDecl -> SQDecl
  stripQDecl d =
    { dqbinders := map (\(x, b) => (x, mapFst stripPosTy b)) d.dqbinders } d
stripPosItem (SClausalDef r n ty eta wit cls) =
  SClausalDef r n (stripPosTy ty) eta (map stripPos wit)
              (map (\c => { crhs := stripPos c.crhs } c) cls)

export
itemName : SItem -> String
itemName (SDef n _ _ _) = n
itemName (SDeclDef _ n _) = n
itemName (STypeDef n _) = n
itemName (SData _ ds) = case ds of
  (d :: _) => d.dqname
  [] => "data"
itemName (SClausalDef _ n _ _ _ _) = n

-- ===== Show instances (parser golden tests) =====

mutual
  export covering
  Show STy where
    -- a span is metadata, not structure: SKIPPING it here is what
    -- makes `show` the distiller's range-insensitive comparator
    show (STyPos _ t) = show t
    show STyZero = "𝟘"
    show STyOne = "𝟙"
    show STyNat = "ℕ"
    show STyUniv = "𝕌"
    show (STySig x) = "\{x}"
    show (STyPi x a b) = "Pi \{x} (\{show a}) (\{show b})"
    show (STyImpPi x a b) = "ImpPi \{x} (\{show a}) (\{show b})"
    show (STySigma x a b) = "Sigma \{x} (\{show a}) (\{show b})"
    show (STySum a b) = "Sum (\{show a}) (\{show b})"
    show (STyQuot a x y r) = "Quot (\{show a}) \{fst x} \{fst y} (\{show r})"
    show (STyEq _ l r t) = "Eq (\{show l}) (\{show r}) (\{maybe "_" show t})"
    show (STyEl e) = "El (\{show e})"
    show (STyNu f) = "Nu (\{show f})"
    show STyProp = "Ω"

  export covering
  Show SElem where
    show (SPos _ e) = show e
    show (SVar _ n i) = "\{n}@\{show i}"
    show (SSig _ x) = "\{x}@sig"
    show SUnitI = "()"
    show SZeroN = "Z"
    show (SSuc t) = "S (\{show t})"
    show (SLam x t) = "Lam \{fst x} (\{show t})"
    show (SLet x e b) = "Let \{fst x} (\{show e}) (\{show b})"
    show (SApp f e) = "App (\{show f}) (\{show e})"
    show (SPair a b) = "Pair (\{show a}) (\{show b})"
    show (SProj1 t) = "P1 (\{show t})"
    show (SProj2 t) = "P2 (\{show t})"
    show SZeroC = "𝟘c"
    show SOneC = "𝟙c"
    show SNatC = "ℕc"
    show (SPiC x a b) = "PiC \{x} (\{show a}) (\{show b})"
    show (SSigmaC x a b) = "SigmaC \{x} (\{show a}) (\{show b})"
    show (SSumC a b) = "SumC (\{show a}) (\{show b})"
    show (SQuotC a x y r) = "QuotC (\{show a}) \{fst x} \{fst y} (\{show r})"
    show (SEqC _ l r t) = "EqC (\{show l}) (\{show r}) (\{maybe "_" show t})"
    show (SZeroElim t) = "ZeroElim (\{show t})"
    show (SNatElim mot z n2 ih s t) =
      "NatElim \{maybe "_" (fst . fst) mot} (\{maybe "_" (show . snd) mot}) (\{show z}) \{fst n2} \{fst ih} (\{show s}) (\{show t})"
    show (SInj1 t) = "Inj1 (\{show t})"
    show (SInj2 t) = "Inj2 (\{show t})"
    show (SSumElim mot a l b r t) =
      "SumElim \{maybe "_" (fst . fst) mot} (\{maybe "_" (show . snd) mot}) \{fst a} (\{show l}) \{fst b} (\{show r}) (\{show t})"
    show (SClass t) = "Class (\{show t})"
    show (SQuotElim mot a f q) =
      "QuotElim \{maybe "_" (fst . fst) mot} (\{maybe "_" (show . snd) mot}) \{fst a} (\{show f}) (\{show q})"
    show (SNuC f) = "NuC (\{show f})"
    show (SOut e) = "Out (\{show e})"
    show (SCorec x a f u) =
      "Corec \{fst x} (\{show a}) (\{show f}) (\{show u})"
    show (SCoind nx ny r pw mx my mh q) =
      "Coind \{fst nx} \{fst ny} (\{show r}) (\{show pw}) \{fst mx} \{fst my} \{fst mh} (\{show q})"
    show (SSquash t) = "Squash (\{show t})"
    show (SStar _) = "⋆"
    show (SStarWit e) = "⋆ (\{show e})"
    show (SStarUsing _ ns) = "⋆ using (\{joinBy ", " ns})"
    show (SChain x ls) =
      "\{show x}" ++ concat (map (\(j, y) => " ≡⟨ \{show j} ⟩ \{show y}") ls)
    show (SSquashElim e x body) = "SquashElim (\{show e}) \{fst x} (\{show body})"
    show (SAnn t ty) = "Ann (\{show t}) (\{show ty})"
    show (SImpArg t) = "Imp (\{show t})"
    show (SNoIns t) = "NoIns (\{show t})"
    show (SBlank _) = "_"

  public export
  covering
  Show SPoly where
    show SPHole = "𝕏"
    show (SPConst a) = "K (\{show a})"
    show (SPProd f g) = "PProd (\{show f}) (\{show g})"
    show (SPSum f g) = "PSum (\{show f}) (\{show g})"
    show (SPSigma x a f) = "PSigma \{fst x} (\{show a}) (\{show f})"
    show (SPPi x a f) = "PPi \{fst x} (\{show a}) (\{show f})"

export
Show SImport where
  show (MkSImport m [] _) = "import \{m}"
  show (MkSImport m os _) = "import \{m} (\{joinBy ", " os})"

export covering
Show SPat where
  show (SPVar x) = fst x
  show SPZero = "Z"
  show (SPSuc p) = "S (\{show p})"
  show (SPInj1 p) = "Inj1 (\{show p})"
  show (SPInj2 p) = "Inj2 (\{show p})"

export covering
Show SClause where
  show (MkSClause ps _ rhs mn _) =
    "| " ++ joinBy " " (map show ps) ++ " := " ++ show rhs
      ++ maybe "" (\n => " [\{n}]") mn

export covering
Show SQTm where
  show (SQVar n i) = "\{n}@⬡\{show i}"
  show (SQAppE f e) = "AppE (\{show f}) (\{show e})"
  show (SQAppI f a) = "AppI (\{show f}) (\{show a})"

export covering
Show SQRes where
  show SQResU = "U"
  show (SQResEl q) = "El (\{show q})"
  show (SQResEq l r u) = "Eq (\{show l}) (\{show r}) (\{show u})"

export covering
Show SQDecl where
  show (MkSQDecl n bs res) =
    "\{n} : " ++ concatMap showB bs ++ show res
   where
    showB : (String, Either STy SQTm) -> String
    showB (x, Left t) = "(\{x} : ext \{show t}) → "
    showB (x, Right q) = "(\{x} : El \{show q}) → "

export covering
Show SItem where
  show (SDef x ty body mu) =
    "def \{x} : \{show ty}" ++
    (case mu of
       Nothing => ""
       Just ns => " using (\{joinBy ", " ns})") ++
    " := \{show body}"
  show (SDeclDef _ x ty) = "def \{x} : \{show ty}"
  show (STypeDef x ty) = "type \{x} := \{show ty}"
  show (SData ps ds) =
    "data " ++ concatMap (\p => case p of (x, t) => "[\{x} : \{show t}] ") ps
      ++ "(" ++ joinBy " ; " (map show ds) ++ ")"
  show (SClausalDef _ x ty eta w cls) =
    "def \{x} : \{show ty}"
      ++ maybe "" (\n => " [\{n}]") eta
      ++ maybe "" (\t => " := \{show t}") w
      ++ concatMap (\c => " \{show c}") cls
