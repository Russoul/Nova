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
    ||| (x:T) ⨯ U
    STySigma : (name : String) -> STy -> STy -> STy
    ||| T ⊎ U — non-dependent, no binder
    STySum : STy -> STy -> STy
    ||| T / (x y. r) — r is an Ω-valued element
    STyQuot : STy -> (nx, ny : SName) -> SElem -> STy
    ||| t ≡ t ∈ T
    STyEq : SElem -> SElem -> STy -> STy
    ||| El t
    STyEl : SElem -> STy
    ||| Ω
    STyProp : STy
    ||| Prf t
    STyPrf : SElem -> STy
    ||| ν F — the coinductive type at a surface polynomial
    STyNu : SPoly -> STy
    ||| ?x (rigid) or _x/_ (solvable) — a hole in type position: a
    ||| type declaration in Σ, stuck until (if solvable) instantiated;
    ||| blocks acceptance while it remains a declaration. The range is
    ||| the token's source span (display metadata, for the LSP).
    STyHole : Maybe Range -> (solvable : Bool) -> String -> STy

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
    ||| t ≡ t ∈ T — the equality PROP (an Ω-element; the ∈-slot
    ||| embeds a TYPE, like ∥-∥)
    SEqC : SElem -> SElem -> STy -> SElem
    SZeroElim : SElem -> SElem
    ||| ℕ-elim (n. T) z (n ih. s) t — motive-first
    SNatElim : (n : SName) -> STy -> SElem -> (n2, ih : SName) -> SElem -> SElem -> SElem
    ||| inj₁ t / inj₂ t — sum introductions
    SInj1 : SElem -> SElem
    SInj2 : SElem -> SElem
    ||| ⊎-elim (z. T) (a. l) (b. r) t — motive, left case, right
    ||| case, scrutinee
    SSumElim : (z : SName) -> STy -> (a : SName) -> SElem -> (b : SName) -> SElem -> SElem -> SElem
    SClass : SElem -> SElem
    ||| quot-elim (z. T) (a. f) q — motive-first
    SQuotElim : (z : SName) -> STy -> (a : SName) -> SElem -> SElem -> SElem
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
    SStar : SElem
    ||| ⋆ e — el-squash-i with an explicit witness: e proves the
    ||| squashee directly, for squashees of any shape
    SStarWit : SElem -> SElem
    ||| squash-elim e (x. body) — el-squash-e-prf: eliminate a proof of
    ||| a squashed proposition into a further proposition, via a
    ||| hypothetical inhabitant x of the raw squashee
    SSquashElim : SElem -> (name : SName) -> SElem -> SElem
    ||| (t : T) — ascription; the lever into inference mode
    SAnn : SElem -> STy -> SElem
    ||| ?x (rigid) or _x/_ (solvable) — a hole: a term declaration in
    ||| Σ at the ambient context, stuck until (if solvable)
    ||| instantiated by a pattern equation; reported with its type
    ||| while open. Checking position only — a hole has no type of its
    ||| own to infer. The range is the token's source span (display
    ||| metadata, for the LSP).
    SHole : Maybe Range -> (solvable : Bool) -> String -> SElem

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
||| (→ ⨯ ≡ ∈ ≔ / . , : parens) and comment dashes are eaten by the
||| lexer, so no operator may contain "--".
public export
opChar : Char -> Bool
opChar c = c `elem` unpack "+-*<>=&|!?%^~@#⊕⊗⊙⊞⊟∙∘·≤≥∸⧺⊥⊤∧∨⊃¬↔"

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

public export
data SItem : Type where
  ||| def x : T ≔ t — always in the empty context
  SDef : String -> STy -> SElem -> SItem
  ||| def x : T — a DECLARATION: a def without a definiens, entering Σ
  ||| as a sig-decl and reported as an open hole (the name's span is
  ||| kept for hover)
  SDeclDef : (nrng : Maybe Range) -> String -> STy -> SItem
  ||| type x ≔ T — always in the empty context
  STypeDef : String -> STy -> SItem
  ||| data [x : T]* ( n : Q ; … ) — a QIIT signature literal over an
  ||| ambient PARAMETER telescope (Foundation's Γ ⊦ 𝒮 qsig); an ITEM
  ||| MACRO that expands into a batch of ordinary defs, each
  ||| Π-abstracted over the parameters (docs/NovaElaboration.txt,
  ||| QIIT section)
  SData : List (String, STy) -> List SQDecl -> SItem

export
itemName : SItem -> String
itemName (SDef n _ _) = n
itemName (SDeclDef _ n _) = n
itemName (STypeDef n _) = n
itemName (SData _ ds) = case ds of
  (d :: _) => d.dqname
  [] => "data"

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
    show (STySigma x a b) = "Sigma \{x} (\{show a}) (\{show b})"
    show (STySum a b) = "Sum (\{show a}) (\{show b})"
    show (STyQuot a x y r) = "Quot (\{show a}) \{fst x} \{fst y} (\{show r})"
    show (STyEq l r t) = "Eq (\{show l}) (\{show r}) (\{show t})"
    show (STyEl e) = "El (\{show e})"
    show (STyNu f) = "Nu (\{show f})"
    show STyProp = "Ω"
    show (STyPrf e) = "Prf (\{show e})"
    show (STyHole _ solvable x) = if solvable then "_\{x}" else "?\{x}"

  export covering
  Show SElem where
    show (SVar _ n i) = "\{n}@\{show i}"
    show (SSig _ x) = "\{x}@sig"
    show SUnitI = "()"
    show SZeroN = "Z"
    show (SSuc t) = "S (\{show t})"
    show (SLam x t) = "Lam \{fst x} (\{show t})"
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
    show (SEqC l r t) = "EqC (\{show l}) (\{show r}) (\{show t})"
    show (SZeroElim t) = "ZeroElim (\{show t})"
    show (SNatElim n mot z n2 ih s t) =
      "NatElim \{fst n} (\{show mot}) (\{show z}) \{fst n2} \{fst ih} (\{show s}) (\{show t})"
    show (SInj1 t) = "Inj1 (\{show t})"
    show (SInj2 t) = "Inj2 (\{show t})"
    show (SSumElim z mot a l b r t) =
      "SumElim \{fst z} (\{show mot}) \{fst a} (\{show l}) \{fst b} (\{show r}) (\{show t})"
    show (SClass t) = "Class (\{show t})"
    show (SQuotElim z mot a f q) =
      "QuotElim \{fst z} (\{show mot}) \{fst a} (\{show f}) (\{show q})"
    show (SNuC f) = "NuC (\{show f})"
    show (SOut e) = "Out (\{show e})"
    show (SCorec x a f u) =
      "Corec \{fst x} (\{show a}) (\{show f}) (\{show u})"
    show (SCoind nx ny r pw mx my mh q) =
      "Coind \{fst nx} \{fst ny} (\{show r}) (\{show pw}) \{fst mx} \{fst my} \{fst mh} (\{show q})"
    show (SSquash t) = "Squash (\{show t})"
    show SStar = "⋆"
    show (SStarWit e) = "⋆ (\{show e})"
    show (SSquashElim e x body) = "SquashElim (\{show e}) \{fst x} (\{show body})"
    show (SAnn t ty) = "Ann (\{show t}) (\{show ty})"
    show (SHole _ solvable x) = if solvable then "_\{x}" else "?\{x}"

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
  show (MkSImport m []) = "import \{m}"
  show (MkSImport m os) = "import \{m} (\{joinBy ", " os})"

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
  show (SDef x ty body) = "def \{x} : \{show ty} := \{show body}"
  show (SDeclDef _ x ty) = "def \{x} : \{show ty}"
  show (STypeDef x ty) = "type \{x} := \{show ty}"
  show (SData ps ds) =
    "data " ++ concatMap (\p => case p of (x, t) => "[\{x} : \{show t}] ") ps
      ++ "(" ++ joinBy " ; " (map show ds) ++ ")"
