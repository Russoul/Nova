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

import Data.Maybe
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
    ||| 𝕌 and Ω AS TERMS. They are typed at 𝕍, not at 𝕌 — the kernel
    ||| accepts them as types (checkTyP) and gives them no inference
    ||| rule of their own — so they reach a code position only to be
    ||| REJECTED there, which is the point: `K 𝕌` becomes a type error
    ||| instead of a parse error (docs/NovaElaboration.txt, THE TERM
    ||| GRAMMAR MERGE)
    SUnivC : SElem
    SPropC : SElem
    ||| (x:t) → u  (code)
    SPiC : (name : String) -> SElem -> SElem -> SElem
    ||| {x:t} → u  (code) — an IMPLICIT Π-binder, elaborating exactly
    ||| as SPiC (the core is bare; implicitness is per-def metadata).
    ||| The former type level's implicit binder, needed here for
    ||| for the same reason every other former has one
    SImpPiC : (name : String) -> SElem -> SElem -> SElem
    ||| (x:t) × u  (code)
    SSigmaC : (name : String) -> SElem -> SElem -> SElem
    ||| t ⊎ u  (code — non-dependent, no binder)
    SSumC : SElem -> SElem -> SElem
    ||| t / (x y. r)  (code)
    SQuotC : SElem -> (nx, ny : SName) -> SElem -> SElem
    ||| t ≡ t (∈ T)? — the equality PROP (an Ω-element; the ∈-slot
    ||| embeds a TYPE, like ∥-∥); the ∈-annotation is optional, as at
    ||| the type level
    SEqC : Maybe Range -> SElem -> SElem -> Maybe SElem -> SElem
    SZeroElim : SElem -> SElem
    ||| ℕ-elim (n. T)? z (n ih. s) t — motive-first; the motive is
    ||| OPTIONAL in checking position (docs/NovaPerfectSurface.txt,
    ||| Phase 4): when absent it is recovered by abstracting the
    ||| scrutinee in the expected type
    SNatElim : Maybe (SName, SElem) -> SElem -> (n2, ih : SName) -> SElem -> SElem -> SElem
    ||| inj₁ t / inj₂ t — sum introductions
    SInj1 : SElem -> SElem
    SInj2 : SElem -> SElem
    ||| ⊎-elim (z. T)? (a. l) (b. r) t — motive, left case, right
    ||| case, scrutinee; motive optional in checking position
    SSumElim : Maybe (SName, SElem) -> (a : SName) -> SElem -> (b : SName) -> SElem -> SElem -> SElem
    SClass : SElem -> SElem
    ||| quot-elim (z. T)? (a. f) q — motive-first; motive optional in
    ||| checking position
    SQuotElim : Maybe (SName, SElem) -> (a : SName) -> SElem -> SElem -> SElem
    ||| ≡-elim p x w — the EQUALITY variable elimination
    ||| (docs/NovaElaboration.txt, e-eqelim). x is a VARIABLE and w a
    ||| variable of an equation with x on one side and a term t on the
    ||| other, t standing OUTSIDE x's own entry; p is elaborated in the
    ||| context that pair's elimination gives: x and w both gone, every
    ||| entry between and after them refined at t (and at refl for w),
    ||| as is the goal. No motive: substituting t for x IS the motive.
    |||
    ||| Like SSigmaElim, p's indices are counted against THAT context —
    ||| the parser reindexes it once it has read the two variables
    ||| (Parser.eqElimProof).
    SEqElim : (prf : SElem) -> (evar : SElem) -> (eqvar : SElem) -> SElem
    ||| sigma-elim (x y. t) w — the Σ VARIABLE elimination
    ||| (docs/NovaElaboration.txt, e-sigmaelim). w is a VARIABLE of a
    ||| × type, and t is elaborated in the context that variable's
    ||| ELIMINATION gives: w gone, its two components x and y standing
    ||| where it stood, every entry after it (and the goal) refined at
    ||| the pair they form. No motive: abstracting w in the expected
    ||| type IS the motive, and the substitution recovers it.
    |||
    ||| The body's indices are counted against THAT context, not
    ||| against the site's — the parser reindexes it once it has read
    ||| the scrutinee (Parser.sigmaElimBody).
    SSigmaElim : (nx, ny : SName) -> (body : SElem) -> (scrutinee : SElem) -> SElem
    ||| sum-elim (a. l) (b. r) w — the ⊎ VARIABLE elimination
    ||| (docs/NovaElaboration.txt, e-sumsplit). w is a VARIABLE of a ⊎
    ||| type, and each branch is elaborated in the context that
    ||| variable's ELIMINATION gives it: w gone, the branch's own
    ||| binder standing where it stood, every entry after it — and the
    ||| goal — refined at the injection.
    |||
    ||| Two contexts, one per branch, and neither is the site's: like
    ||| SSigmaElim's body, each branch's indices are counted against
    ||| ITS context, and the parser reindexes them once it has read the
    ||| scrutinee (Parser.sumSplitBranch).
    SSumSplit : (na : SName) -> (left : SElem) ->
                (nb : SName) -> (right : SElem) -> (scrutinee : SElem) -> SElem
    ||| unsquash (x. t) w — the ∥∥ VARIABLE elimination
    ||| (docs/NovaElaboration.txt, e-unsquash). w is a VARIABLE of a
    ||| squash type, and t is elaborated where w is GONE and a witness
    ||| of the squashee stands INNERMOST instead.
    |||
    ||| The witness cannot take w's slot, and that is forced rather
    ||| than chosen: el-squash-e-prf binds it innermost, so putting it
    ||| earlier would mean Π-closing the entries after it into the
    ||| goal, and a Π is never a proposition. Nothing is lost by it —
    ||| no entry could mention the witness, which did not exist.
    |||
    ||| Like the rest of the family, t's indices are counted against
    ||| THAT context, and the parser reindexes them once it has read
    ||| the scrutinee (Parser.unsquashBody).
    SUnsquash : (nx : SName) -> (body : SElem) -> (scrutinee : SElem) -> SElem
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
    SSquash : SElem -> SElem
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
    SAnn : SElem -> SElem -> SElem
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
    ||| ?x — a named HOLE: a goal the operator left open, minted as a
    ||| sig-decl at the ambient context and the expected type
    ||| (docs/NovaElaboration.txt, e-hole). CHECKING-ONLY and INERT —
    ||| nothing ever solves it, so Î£ stays monotone and the discharge
    ||| engine is untouched (PerfNotes "The cost of a hole": the
    ||| measured cost was the SOLVER, not the hole). The range is the
    ||| `?x` token's, for the report and the LSP diagnostic
    SHole : Maybe Range -> (name : String) -> SElem
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
-- `SPos` is TRANSPARENT: they carry a source range and
-- nothing else. The parser attaches one at every grammar level (so
-- every sub-expression has an exact span, from a bare `Z` to a whole
-- application chain), the elaborator narrows the reported site to
-- them as it descends, and everything else strips them — `Show` skips
-- them, so the distiller's AST-identity contract is unaffected, and
-- every structural test on a term goes through `unPos`.

||| TYPES ARE TERMS. Foundation dissolved the type judgement into
||| typing at 𝕍 and merged the two grammars into one term sort; the
||| kernel says the same in its own signature (`Ty = Elem`). STy is
||| that alias here — the name survives as a reading aid, marking a
||| position whose term stands as a type (docs/NovaElaboration.txt,
||| THE TERM GRAMMAR MERGE).
public export
STy : Type
STy = SElem

||| Attach a span. A level of the grammar that adds no node of its own
||| hands its child straight back, so re-wrapping REPLACES rather than
||| nests — the two spans coincide there anyway.
public export
atPos : Maybe Range -> SElem -> SElem
atPos Nothing e = e
atPos (Just r) (SPos _ e) = SPos r e
atPos (Just r) e = SPos r e

||| ONE SORT, ONE WALK: every Ty-suffixed helper below is its SElem
||| twin under another name, kept so the call sites still say which
||| positions stand as types.
public export
atPosTy : Maybe Range -> STy -> STy
atPosTy = atPos

||| Peel the spans off the front of a term. EVERY structural test on a
||| surface term goes through this: a span is metadata, never part of
||| a term's shape.
public export
unPos : SElem -> SElem
unPos (SPos _ e) = unPos e
unPos e = e

public export
unPosTy : STy -> STy
unPosTy = unPos

public export
posOf : SElem -> Maybe Range
posOf (SPos r _) = Just r
posOf _ = Nothing

public export
posOfTy : STy -> Maybe Range
posOfTy = posOf

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
  stripPos SUnivC = SUnivC
  stripPos SPropC = SPropC
  stripPos (SPiC x a b) = SPiC x (stripPos a) (stripPos b)
  stripPos (SImpPiC x a b) = SImpPiC x (stripPos a) (stripPos b)
  stripPos (SSigmaC x a b) = SSigmaC x (stripPos a) (stripPos b)
  stripPos (SSumC a b) = SSumC (stripPos a) (stripPos b)
  stripPos (SQuotC a x y r) = SQuotC (stripPos a) x y (stripPos r)
  stripPos (SEqC rng l r t) = SEqC rng (stripPos l) (stripPos r) (map stripPos t)
  stripPos (SZeroElim t) = SZeroElim (stripPos t)
  stripPos (SNatElim mot z n2 ih st t) =
    SNatElim (map (\(n, m) => (n, stripPos m)) mot) (stripPos z) n2 ih (stripPos st) (stripPos t)
  stripPos (SInj1 t) = SInj1 (stripPos t)
  stripPos (SInj2 t) = SInj2 (stripPos t)
  stripPos (SSumElim mot a l b r t) =
    SSumElim (map (\(z, m) => (z, stripPos m)) mot) a (stripPos l) b (stripPos r) (stripPos t)
  stripPos (SClass t) = SClass (stripPos t)
  stripPos (SQuotElim mot a f q) =
    SQuotElim (map (\(z, m) => (z, stripPos m)) mot) a (stripPos f) (stripPos q)
  stripPos (SSigmaElim nx ny b w) = SSigmaElim nx ny (stripPos b) (stripPos w)
  stripPos (SUnsquash nx b w) = SUnsquash nx (stripPos b) (stripPos w)
  stripPos (SSumSplit na l nb r w) =
    SSumSplit na (stripPos l) nb (stripPos r) (stripPos w)
  stripPos (SEqElim p x w) = SEqElim (stripPos p) (stripPos x) (stripPos w)
  stripPos (SNuC f) = SNuC (stripPosPoly f)
  stripPos (SOut t) = SOut (stripPos t)
  stripPos (SCorec x a f u) = SCorec x (stripPos a) (stripPos f) (stripPos u)
  stripPos (SCoind nx ny r pw mx my mh q) =
    SCoind nx ny (stripPos r) (stripPos pw) mx my mh (stripPos q)
  stripPos (SSquash t) = SSquash (stripPos t)
  stripPos e@(SStar _) = e
  stripPos (SStarWit e) = SStarWit (stripPos e)
  stripPos e@(SStarUsing _ _) = e
  stripPos (SSquashElim e x b) = SSquashElim (stripPos e) x (stripPos b)
  stripPos (SChain h ls) = SChain (stripPos h) (map (\(j, m) => (stripPos j, stripPos m)) ls)
  stripPos (SAnn t ty) = SAnn (stripPos t) (stripPos ty)
  stripPos (SImpArg t) = SImpArg (stripPos t)
  stripPos (SNoIns t) = SNoIns (stripPos t)
  stripPos e@(SBlank _) = e
  stripPos e@(SHole _ _) = e

  public export
  covering
  stripPosPoly : SPoly -> SPoly
  stripPosPoly SPHole = SPHole
  stripPosPoly (SPConst e) = SPConst (stripPos e)
  stripPosPoly (SPProd f g) = SPProd (stripPosPoly f) (stripPosPoly g)
  stripPosPoly (SPSum f g) = SPSum (stripPosPoly f) (stripPosPoly g)
  stripPosPoly (SPSigma x a f) = SPSigma x (stripPos a) (stripPosPoly f)
  stripPosPoly (SPPi x a f) = SPPi x (stripPos a) (stripPosPoly f)


-- ===== Free-variable reindexing =====
--
-- The indexed surface AST is de Bruijn, so a term written against one
-- binder stack can be READ against another by remapping its free
-- indices. One traversal serves it, `Maybe`-valued: a map that
-- declines an index (the target context has no such entry) aborts the
-- whole rewrite rather than fabricating a reference.
--
-- The callers are the VARIABLE-ELIMINATING forms — sigma-elim,
-- ≡-elim, sum-elim — whose sub-terms are parsed against the site's
-- binders and then reindexed against the ELIMINATION context, where
-- the eliminated variable is gone (docs/NovaElaboration.txt).
--
-- THE MAP IS A FUNCTION, NOT A DEPTH, and that is load-bearing. A
-- depth can only describe a context EXTENDED innermost; these forms
-- REPLACE an entry in the middle of one — sigma-elim's body sits in a
-- context one longer, sum-elim's branch in one the same length,
-- ≡-elim's proof in one two shorter. So the traversal transports the
-- map through each node it descends (sigmaUnder/sumUnder/eqUnder),
-- using the index the node's own scrutinee carries. Nesting one of
-- these inside another's branch depends on it: with a fixed depth the
-- outer variables an inner branch names are silently mis-shifted, and
-- the kernel accepts the result — a WRONG term, not a rejected one
-- (tests/nova/elaboration/elab-elim-nesting pins the values).

||| Lift a remap under one binder the term itself introduces.
public export
underM : (Nat -> Maybe Nat) -> Nat -> Maybe Nat
underM f Z = Just Z
underM f (S k) = map S (f k)

||| The remap transported into a Σ-elimination BODY. That environment
||| has the eliminated entry replaced by the two components, so it is
||| one LONGER than the site's, with y at i and x at i+1 — and the
||| target's is one longer than the target's site, split at i'.
public export
sigmaUnder : (Nat -> Maybe Nat) -> (i, i' : Nat) -> Nat -> Maybe Nat
sigmaUnder f i i' k =
  if k == i then Just i'
  else if k == S i then Just (S i')
  else map (\m => if m > i' then S m else m) (f (if k < i then k else minus k 1))

||| … into an ∥∥-elimination BODY. The same length as the site's too,
||| but for a different reason: one entry goes and one arrives. The
||| witness is bound INNERMOST, so it takes index 0 and pushes the
||| entries that stood after the variable up by one, while those before
||| it keep their indices.
public export
unsquashUnder : (Nat -> Maybe Nat) -> (i, i' : Nat) -> Nat -> Maybe Nat
unsquashUnder f i i' k =
  if k == 0 then Just 0
  else if k <= i then map S (f (minus k 1))
  else f k

||| … into a ⊎-elimination BRANCH. Same length as the site's: the
||| branch's own binder stands exactly where the variable stood, and
||| every other entry keeps its index.
public export
sumUnder : (Nat -> Maybe Nat) -> (i, i' : Nat) -> Nat -> Maybe Nat
sumUnder f i i' k = if k == i then Just i' else f k

||| … into an ≡-elimination PROOF. TWO entries shorter — the variable
||| at i and the equation at j (j < i) are both gone — so an index
||| there enumerates the survivors, and the result re-enumerates them
||| in the target.
public export
eqUnder : (Nat -> Maybe Nat) -> (i, j, i', j' : Nat) -> Nat -> Maybe Nat
eqUnder f i j i' j' k =
  let e = if k < j then k else if S k < i then S k else S (S k) in
  map (\m => minus m ((if m > j' then 1 else 0) + (if m > i' then 1 else 0))) (f e)

mutual
  ||| Remap the FREE variable indices of a term: `f` maps an index of
  ||| the term's own environment to one of the target's, and declining
  ||| an index aborts the whole rewrite. Binders the term introduces
  ||| lift it (`underM`); the VARIABLE-ELIMINATING forms transport it
  ||| through their own reindexing instead — see below.
  public export
  covering
  mapVarsE : (f : Nat -> Maybe Nat) -> SElem -> Maybe SElem
  mapVarsE f (SVar r n i) = SVar r n <$> f i
  mapVarsE f e@(SSig _ _) = Just e
  mapVarsE f SUnitI = Just SUnitI
  mapVarsE f SZeroN = Just SZeroN
  mapVarsE f (SSuc t) = SSuc <$> mapVarsE f t
  mapVarsE f (SLam x b) = SLam x <$> mapVarsE (underM f) b
  mapVarsE f (SLet x e b) = [| SLet (pure x) (mapVarsE f e) (mapVarsE (underM (underM f)) b) |]
  mapVarsE f (SApp h a) = [| SApp (mapVarsE f h) (mapVarsE f a) |]
  mapVarsE f (SPair a b) = [| SPair (mapVarsE f a) (mapVarsE f b) |]
  mapVarsE f (SProj1 t) = SProj1 <$> mapVarsE f t
  mapVarsE f (SProj2 t) = SProj2 <$> mapVarsE f t
  mapVarsE f SZeroC = Just SZeroC
  mapVarsE f SOneC = Just SOneC
  mapVarsE f SNatC = Just SNatC
  mapVarsE f SUnivC = Just SUnivC
  mapVarsE f SPropC = Just SPropC
  mapVarsE f (SPiC x a b) = [| SPiC (pure x) (mapVarsE f a) (mapVarsE (underM f) b) |]
  mapVarsE f (SImpPiC x a b) = [| SImpPiC (pure x) (mapVarsE f a) (mapVarsE (underM f) b) |]
  mapVarsE f (SSigmaC x a b) = [| SSigmaC (pure x) (mapVarsE f a) (mapVarsE (underM f) b) |]
  mapVarsE f (SSumC a b) = [| SSumC (mapVarsE f a) (mapVarsE f b) |]
  mapVarsE f (SQuotC a x y r) =
    [| SQuotC (mapVarsE f a) (pure x) (pure y) (mapVarsE (underM (underM f)) r) |]
  mapVarsE f (SEqC rng l r t) =
    [| SEqC (pure rng) (mapVarsE f l) (mapVarsE f r) (traverse (mapVarsE f) t) |]
  mapVarsE f (SZeroElim t) = SZeroElim <$> mapVarsE f t
  mapVarsE f (SNatElim mot z n2 ih s t) =
    [| SNatElim (traverse (\(n, m) => (n,) <$> mapVarsE (underM f) m) mot) (mapVarsE f z)
                (pure n2) (pure ih) (mapVarsE (underM (underM f)) s) (mapVarsE f t) |]
  mapVarsE f (SInj1 t) = SInj1 <$> mapVarsE f t
  mapVarsE f (SInj2 t) = SInj2 <$> mapVarsE f t
  mapVarsE f (SSumElim mot a l b r t) =
    [| SSumElim (traverse (\(z, m) => (z,) <$> mapVarsE (underM f) m) mot) (pure a)
                (mapVarsE (underM f) l) (pure b) (mapVarsE (underM f) r) (mapVarsE f t) |]
  mapVarsE f (SClass t) = SClass <$> mapVarsE f t
  mapVarsE f (SQuotElim mot a g q) =
    [| SQuotElim (traverse (\(z, m) => (z,) <$> mapVarsE (underM f) m) mot) (pure a)
                 (mapVarsE (underM f) g) (mapVarsE f q) |]
  -- THE VARIABLE-ELIMINATING FORMS do not extend the context, they
  -- REPLACE an entry of it — so a sub-term's environment is not the
  -- ambient one plus binders, and no depth describes it. Each node
  -- knows the index it eliminates (the scrutinee carries it), so the
  -- remap descends COMPOSED with that node's own reindexing. Without
  -- this, nesting one of these inside another's branch silently
  -- mis-shifts the outer variables — a wrong term, not a rejected one.
  mapVarsE f (SSigmaElim nx ny b w) = case unPos w of
    SVar _ _ i => do
      i' <- f i
      [| SSigmaElim (pure nx) (pure ny) (mapVarsE (sigmaUnder f i i') b) (mapVarsE f w) |]
    -- not a variable: the elaborator rejects it, and the body's
    -- indices are never read
    _ => [| SSigmaElim (pure nx) (pure ny) (mapVarsE f b) (mapVarsE f w) |]
  mapVarsE f (SUnsquash nx b w) = case unPos w of
    SVar _ _ i => do
      i' <- f i
      [| SUnsquash (pure nx) (mapVarsE (unsquashUnder f i i') b) (mapVarsE f w) |]
    _ => [| SUnsquash (pure nx) (mapVarsE f b) (mapVarsE f w) |]
  mapVarsE f (SSumSplit na l nb r w) = case unPos w of
    SVar _ _ i => do
      i' <- f i
      [| SSumSplit (pure na) (mapVarsE (sumUnder f i i') l)
                   (pure nb) (mapVarsE (sumUnder f i i') r) (mapVarsE f w) |]
    _ => [| SSumSplit (pure na) (mapVarsE f l) (pure nb) (mapVarsE f r) (mapVarsE f w) |]
  mapVarsE f (SEqElim p x w) = case (unPos x, unPos w) of
    (SVar _ _ i, SVar _ _ j) => do
      i' <- f i
      j' <- f j
      [| SEqElim (mapVarsE (eqUnder f i j i' j') p) (mapVarsE f x) (mapVarsE f w) |]
    _ => [| SEqElim (mapVarsE f p) (mapVarsE f x) (mapVarsE f w) |]
  mapVarsE f (SNuC p) = SNuC <$> mapVarsPoly f p
  mapVarsE f (SOut t) = SOut <$> mapVarsE f t
  mapVarsE f (SCorec x a g u) =
    [| SCorec (pure x) (mapVarsE f a) (mapVarsE (underM f) g) (mapVarsE f u) |]
  mapVarsE f (SCoind nx ny r pw mx my mh q) =
    [| SCoind (pure nx) (pure ny) (mapVarsE (underM (underM f)) r) (mapVarsE f pw)
              (pure mx) (pure my) (pure mh) (mapVarsE (underM (underM (underM f))) q) |]
  mapVarsE f (SSquash t) = SSquash <$> mapVarsE f t
  mapVarsE f e@(SStar _) = Just e
  mapVarsE f (SStarWit e) = SStarWit <$> mapVarsE f e
  mapVarsE f e@(SStarUsing _ _) = Just e
  mapVarsE f (SSquashElim e x b) =
    [| SSquashElim (mapVarsE f e) (pure x) (mapVarsE (underM f) b) |]
  mapVarsE f (SChain h ls) =
    [| SChain (mapVarsE f h)
              (traverse (\(j, m) => [| MkPair (mapVarsE f j) (mapVarsE f m) |]) ls) |]
  mapVarsE f (SAnn t ty) = [| SAnn (mapVarsE f t) (mapVarsE f ty) |]
  mapVarsE f (SImpArg t) = SImpArg <$> mapVarsE f t
  mapVarsE f (SNoIns t) = SNoIns <$> mapVarsE f t
  mapVarsE f e@(SBlank _) = Just e
  mapVarsE f e@(SHole _ _) = Just e
  mapVarsE f (SPos r t) = SPos r <$> mapVarsE f t

  public export
  covering
  mapVarsPoly : (f : Nat -> Maybe Nat) -> SPoly -> Maybe SPoly
  mapVarsPoly f SPHole = Just SPHole
  mapVarsPoly f (SPConst e) = SPConst <$> mapVarsE f e
  mapVarsPoly f (SPProd p q) = [| SPProd (mapVarsPoly f p) (mapVarsPoly f q) |]
  mapVarsPoly f (SPSum p q) = [| SPSum (mapVarsPoly f p) (mapVarsPoly f q) |]
  mapVarsPoly f (SPSigma x a p) =
    [| SPSigma (pure x) (mapVarsE f a) (mapVarsPoly (underM f) p) |]
  mapVarsPoly f (SPPi x a p) =
    [| SPPi (pure x) (mapVarsE f a) (mapVarsPoly (underM f) p) |]


--


||| ONE SORT, ONE WALK: a term in TYPE position is a term, so the
||| Ty-suffixed remap is its Elem twin under another name.
public export
covering
mapVarsTy : (f : Nat -> Maybe Nat) -> STy -> Maybe STy
mapVarsTy = mapVarsE
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
  headRange (SHole r _) = r
  headRange (SEqC r _ _ _) = r
  headRange SUnitI = Nothing
  headRange SZeroN = Nothing
  headRange SZeroC = Nothing
  headRange SOneC = Nothing
  headRange SNatC = Nothing
  headRange SUnivC = Nothing
  headRange SPropC = Nothing
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
  headRange (SSquash t) = headRange t
  headRange (SSquashElim e _ _) = headRange e
  headRange (SNuC f) = headRangePoly f
  headRange (SSumC a b) = headRange a <|> headRange b
  headRange (SPiC _ a _) = headRange a
  headRange (SImpPiC _ a _) = headRange a
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
  -- sigma-elim has no motive: the scrutinee's head places it (the
  -- variable it eliminates is what every message here is about)
  headRange (SSigmaElim _ _ _ w) = headRange w
  headRange (SSumSplit _ _ _ _ w) = headRange w
  headRange (SUnsquash _ _ w) = headRange w
  -- the VARIABLE being eliminated places it: every message here is
  -- about it or the equation that specialises it
  headRange (SEqElim _ x w) = headRange x <|> headRange w

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

||| The shift as a `mapVars` instance: at depth d the cutoff has moved
||| to c + d, and an index at or past it goes up by one. Total — the
||| map declines nothing — so the Nothing branch is unreachable.
public export
covering
shiftElem : (c : Nat) -> SElem -> SElem
shiftElem c e = fromMaybe e (mapVarsE (\i => Just (if i >= c then S i else i)) e)

public export
covering
shiftPoly : (c : Nat) -> SPoly -> SPoly
shiftPoly c p = fromMaybe p (mapVarsPoly (\i => Just (if i >= c then S i else i)) p)

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

||| ONE SORT, ONE WALK: the Ty-suffixed traversals are their SElem
||| twins under another name, kept so that call sites still say which
||| positions stand as types.
public export
covering
stripPosTy : STy -> STy
stripPosTy = stripPos

public export
covering
headRangeTy : STy -> Maybe Range
headRangeTy = headRange

public export
covering
shiftTy : (c : Nat) -> STy -> STy
shiftTy = shiftElem

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
stripPosItem (SDef n ty body mu) = SDef n (stripPos ty) (stripPos body) mu
stripPosItem (SDeclDef r n ty) = SDeclDef r n (stripPos ty)
stripPosItem (STypeDef n ty) = STypeDef n (stripPos ty)
stripPosItem (SData ps ds) =
  SData (map (\(x, t) => (x, stripPos t)) ps) (map stripQDecl ds)
 where
  stripQDecl : SQDecl -> SQDecl
  stripQDecl d =
    { dqbinders := map (\(x, b) => (x, mapFst stripPos b)) d.dqbinders } d
stripPosItem (SClausalDef r n ty eta wit cls) =
  SClausalDef r n (stripPos ty) eta (map stripPos wit)
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
    show SUnivC = "𝕌"
    show SPropC = "Ω"
    show (SPiC x a b) = "PiC \{x} (\{show a}) (\{show b})"
    show (SImpPiC x a b) = "ImpPiC \{x} (\{show a}) (\{show b})"
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
    show (SEqElim p x w) = "EqElim (\{show p}) (\{show x}) (\{show w})"
    show (SUnsquash nx b w) = "Unsquash \{fst nx} (\{show b}) (\{show w})"
    show (SSumSplit na l nb r w) =
      "SumSplit \{fst na} (\{show l}) \{fst nb} (\{show r}) (\{show w})"
    show (SSigmaElim nx ny b w) =
      "SigmaElim \{fst nx} \{fst ny} (\{show b}) (\{show w})"
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
    show (SHole _ n) = "?\{n}"

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
