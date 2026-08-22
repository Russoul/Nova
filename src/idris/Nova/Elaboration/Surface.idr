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
    ||| (x:T) ⨯ U
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
    ||| Prf t
    STyPrf : SElem -> STy
    ||| ν F — the coinductive type at a surface polynomial
    STyNu : SPoly -> STy

  ||| Surface polynomials — the one-hole codes of Foundation's
  ||| coinductive section. External pieces are element-level CODES; a
  ||| left-hand (x:t) binds x in the body.
  public export
  data SPoly : Type where
    ||| 𝕏 — the hole
    SPHole : SPoly
    ||| K t — constant at a code
    SPConst : SElem -> SPoly
    ||| F ⨯ G — product (non-binding)
    SPProd : SPoly -> SPoly -> SPoly
    ||| F ⊎ G — sum
    SPSum : SPoly -> SPoly -> SPoly
    ||| (x:t) ⨯ F — dependent pair over external data (binds)
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
    ||| (x:t) ⨯ u  (code)
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
    ||| checked at Prf (l ≡ r ∈ El (ν F)): invariant R (Ω-valued,
    ||| over the two sides), p a proof of R l r, q the one-step
    ||| closure — under generic x y and h : Prf (R x y), a proof
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
    ||| Prf (l ≡ r ∈ A): the head and each subsequent term are
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
    ||| f {} — the NO-INSERT marker: suppress trailing-implicit
    ||| insertion at this reference/spine (the function-passing form:
    ||| a checking-position reference of an implicit-binder def
    ||| otherwise inserts its implicit run and solves it from the
    ||| expected type — docs/NovaPerfectSurface.txt, Phase 3d)
    SNoIns : SElem -> SElem

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
  shiftTy c (STyPrf e) = STyPrf (shiftElem c e)
  shiftTy c (STyNu f) = STyNu (shiftPoly c f)

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
data Assoc = AssocL | AssocR | Postfix

public export
Eq Assoc where
  AssocL == AssocL = True
  AssocR == AssocR = True
  Postfix == Postfix = True
  _ == _ = False

||| operator token ↦ (associativity, binding level 0..9); higher binds
||| tighter
public export
FixTable : Type
FixTable = List (String, Assoc, Nat)

||| The operator alphabet. Excludes the reserved theory tokens
||| (→ ⨯ ≡ ∈ ≔ / . , : parens) — and `|`, the clause marker of the
||| clausal def item — and comment dashes are eaten by the lexer, so
||| no operator may contain "--".
public export
opChar : Char -> Bool
opChar c = c `elem` unpack "+-*<>=&!?%^~@#⊕⊗⊙⊞⊟∙∘·≤≥∸⧺⊥⊤∧∨⊃¬↔⁻¹ᴳᴴ"

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

||| An instantiation argument of a parameterized import — a name, or
||| a name applied to further arguments: `import (groupTheory g)`,
||| `import (groupTheory (raddGroup r))`. Resolved at ELABORATION
||| (module params by name first, then the visibility table): the
||| module header whose binders it references comes LATER in the
||| file than the import line, so parse-time resolution is
||| impossible by design.
public export
data SInstArg : Type where
  IArg : String -> List SInstArg -> SInstArg

showInstArg : SInstArg -> String
showInstArg (IArg n []) = n
showInstArg (IArg n as) =
  "(" ++ n ++ " " ++ joinBy " " (map (\z => assert_total (showInstArg z)) as) ++ ")"

export
Show SInstArg where
  show = showInstArg

||| import M              — M's names accessible qualified (M.x) only
||| import M (a, b)       — additionally, a and b accessible bare
||| import M (a as x, b)  — a opened RENAMED: the importer's surface
|||                         name for it is x (its fixity, if any,
|||                         does not travel with a rename)
||| import (M a…) (b, …)  — a PARAMETERIZED module instantiated at
|||                         the given arguments: each opened name
|||                         stands for the def with its module-
|||                         parameter prefix pre-applied at a…
public export
record SImport where
  constructor MkSImport
  mname : String
  iargs : List SInstArg
  opens : List (String, Maybe String)

||| A parameterized module's header telescope, as written:
||| (implicit?, name, domain), left to right.
public export
SModParams : Type
SModParams = List (Bool, String, STy)

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

||| One fixity declaration as written: (operator, associativity,
||| level). `postfix 9 ⁻¹` is the unary suffix class, parsed at the
||| projection tier.
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
    show (STyPrf e) = "Prf (\{show e})"

  export covering
  Show SElem where
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
  show (MkSImport m args os) =
    let hd = case args of
               [] => "import \{m}"
               _ => "import (\{m} \{joinBy " " (map show args)})"
        one = the ((String, Maybe String) -> String) $ \(o, ml) => case ml of
                Nothing => o
                Just l => "\{o} as \{l}"
    in case os of
         [] => hd
         _ => "\{hd} (\{joinBy ", " (map one os)})"

export covering
Show SPat where
  show (SPVar x) = fst x
  show SPZero = "Z"
  show (SPSuc p) = "S (\{show p})"
  show (SPInj1 p) = "Inj1 (\{show p})"
  show (SPInj2 p) = "Inj2 (\{show p})"

export covering
Show SClause where
  show (MkSClause ps _ rhs mn) =
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
