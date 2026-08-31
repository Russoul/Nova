module Nova.Kernel.Syntax

import Data.List
import Data.SnocList
import Data.String

mutual
  namespace Sub
    public export
    data Sub : Type where
      ||| ·  (unique substitution into the empty context)
      Terminal : Sub
      ||| σ, t  (substitution into an extended context)
      Ext : Sub -> Elem -> Sub
      ||| σ ∘ τ  (composition of substitutions)
      Chain : Sub -> Sub -> Sub
      ||| id  (identity substitution)
      Id : Sub
      ||| ↑  (weakening substitution)
      Wk : Sub

  namespace Elem
    ||| ONE term sort (Foundation: the type and element grammars are
    ||| merged; a term is a TYPE when it is typed at 𝕍 — TopTy). The
    ||| shared formers (𝟘 𝟙 ℕ → × ⊎ /, QSort, NuTy) are one
    ||| constructor each, typed both at 𝕌 (as codes) and at 𝕍 (as
    ||| types).
    public export
    data Elem : Type where
      ||| ☐ₙ (n-th element in the typing context)
      CtxVar : Nat -> Elem
      ||| 𝟘-elim t (empty type elimination)
      ZeroElim : Elem -> Elem
      ||| ()  (unit introduction)
      OneIntro : Elem
      ||| Z  (zero)
      NatIntro0 : Elem
      ||| S t  (successor)
      NatIntro1 : Elem -> Elem
      ||| ℕ-elim z s t (natural number elimination)
      NatElim : Elem -> Elem -> Elem -> Elem
      ||| λ t (pi introduction)
      PiIntro : Elem -> Elem
      ||| f e
      PiApp : Elem -> Elem -> Elem
      ||| let a b  (let-expression: definiens, then body. The body
      ||| binds the definiens' VALUE and its UNFOLDING EQUATION —
      ||| Γ ▷ A ▷ (☐₀ ≡ a[↑] ∈ A[↑]), el-let — so the definiendum
      ||| unfolds judgementally inside it. Always a redex: el-let-beta
      ||| contracts to b[id, a, ⋆], so normal forms contain no let.)
      Let : Elem -> Elem -> Elem
      ||| t , t (sigma introduction / pair)
      SigmaIntro : Elem -> Elem -> Elem
      ||| t .π₁  (sigma elimination, first projection)
      SigmaElim1 : Elem -> Elem
      ||| t .π₂  (sigma elimination, second projection)
      SigmaElim2 : Elem -> Elem
      ||| inj₁ t  (sum type introduction, left)
      Inj1 : Elem -> Elem
      ||| inj₂ t  (sum type introduction, right)
      Inj2 : Elem -> Elem
      ||| ⊎-elim l r t  (sum type elimination: the left case — one
      ||| bound variable over the left summand — then the right case
      ||| — one bound variable over the right summand — then the
      ||| eliminee)
      SumElim : Elem -> Elem -> Elem -> Elem
      ||| 𝟘  (code and type)
      ZeroTy : Elem
      ||| 𝟙  (code and type)
      OneTy : Elem
      ||| ℕ  (code and type)
      NatTy : Elem
      ||| 𝕌  (the predicative universe — a type, not a code)
      UniverseTy : Elem
      ||| Ω  (the universe of mere propositions — a type, not a code;
      ||| anti-structural: its codes are compared by inhabitation,
      ||| code-prop-eq)
      PropTy : Elem
      ||| 𝕍  (THE TOP UNIVERSE — the one term with NO typing rule: it
      ||| stands only in the type slot of judgements and in the ∈-slot
      ||| of ≡; 𝕍[σ] ≜ 𝕍 is a meta-clause)
      TopTy : Elem
      ||| t → t  (dependent product, Π — code and type)
      PiTy : Elem -> Elem -> Elem
      ||| t × t  (dependent sum, Σ — code and type)
      SigmaTy : Elem -> Elem -> Elem
      ||| t ⊎ t  (non-dependent sum — code and type; no binder in
      ||| either component)
      SumTy : Elem -> Elem -> Elem
      ||| t ≡ t ∈ T  (the equality PROPOSITION — an Ω-element; the
      ||| third component is an arbitrary TYPE — OR TopTy, so type
      ||| equality is a proposition. code-eq; no 𝕌-code for equality
      ||| exists, and equality inherits Ω's anti-structural
      ||| discipline: no injectivity)
      EqTy : Elem -> Elem -> Ty -> Elem
      ||| t / t  (quotient — code and type; the second Elem is the
      ||| Ω-valued relation, living two levels deeper —
      ||| Γ ▷ A ▷ A[↑] — one bound variable per side)
      QuotTy : Elem -> Elem -> Elem
      ||| x[σ]  (signature variable, applied to a (normal) substitution to its
      ||| declaration context)
      SigVar : String -> SubNorm -> Elem
      ||| class t (quotient type introduction)
      Class : Elem -> Elem
      ||| quot-elim t t (quotient type elimination: the recursion function,
      ||| then the eliminee)
      QuotElim : Elem -> Elem -> Elem
      ||| ∥T∥  (squash: the proposition of an arbitrary type)
      Squash : Ty -> Elem
      ||| ⋆  (the canonical proof of a true proposition)
      Star : Elem
      ||| 𝒮.k ē  (the sort at entry position k of the carried QIIT
      ||| signature, at index spine ē — a type (ty-qiit), and a code
      ||| when 𝒮 is SMALL (code-qiit))
      QSort : QSig -> Nat -> SubNorm -> Elem
      ||| 𝒮.k θ  (POINT constructor at entry position k, SATURATED: θ is
      ||| the full argument spine — a bare curried constructor would be a
      ||| non-λ inhabitant of a Π-type, breaking Π-canonicity)
      QCtor : QSig -> Nat -> SubNorm -> Elem
      ||| 𝒮.k-elim ℰ ē w  (the eliminator at sort position k; carries
      ||| ℰ = (C̄ ; m̄): motives — one per SORT entry in entry order, each
      ||| a type over Γ·⌊𝔎⌋ᵗ ▷ 𝒮.k δ — and methods — one per POINT entry
      ||| in entry order, terms over Γ; then the index spine and the
      ||| eliminee. Coherences are CHECKED (kernel PQCoh), not stored.)
      QElim : QSig -> Nat -> List Ty -> List Elem -> SubNorm -> Elem -> Elem
      ||| ν 𝔽  (the coinductive type at the carried polynomial — a type
      ||| (ty-nu) and a code (code-nu; every polynomial is small, the
      ||| grammar enforces it); 𝔽 is carried, so ν-equality is
      ||| structural, like a QIIT's 𝒮)
      NuTy : Poly -> Elem
      ||| out t  (the coinductive observation — el-nu-e, the ELIMINATOR;
      ||| lazy: computes only at a corec head, el-nu-beta)
      Out : Elem -> Elem
      ||| corec 𝔽 a f x  (the corecursor — el-nu-i, the INTRODUCTION:
      ||| carried polynomial, carrier code, coalgebra body — one bound
      ||| variable over the carrier a — and seed. 𝔽 and a are CARRIED, like ℰ at
      ||| QElim: el-nu-beta consumes map_𝔽, so the redex is
      ||| self-contained)
      Corec : Poly -> Elem -> Elem -> Elem -> Elem

  namespace QTm
    ||| Theory-of-signatures terms (docs/NovaFoundation.txt, QIIT
    ||| section) — NAMELESS, the FIRST-ORDER fragment: no external λ
    ||| (infinitary recursive arguments have no surface spelling today;
    ||| the kernel rejects signatures needing one).
    public export
    data QTm : Type where
      ||| ⬡ᵢ — ToS variable: inductive Π-binders innermost-first, then
      ||| the signature's entries LAST-to-FIRST
      QVar : Nat -> QTm
      ||| 𝕥 t — application to a Nova term (an EXTERNAL argument)
      QAppE : QTm -> Elem -> QTm
      ||| 𝕥 𝕥′ — application to a ToS term (an INDUCTIVE argument)
      QAppI : QTm -> QTm -> QTm
      ||| 𝕥₀ ≡ 𝕥₁ — equation CODE in U. The third component is the
      ||| sides' common sort code (Foundation leaves it implicit; the
      ||| kernel stores it)
      QEqC : QTm -> QTm -> QTm -> QTm

  namespace QTy
    ||| Theory-of-signatures types: U, El, and the two Π's — the
    ||| external Π binds a NOVA variable, the inductive Π a ToS one.
    public export
    data QTy : Type where
      ||| U — the ToS universe of codes (a SORT's kind ends here)
      QU : QTy
      ||| El 𝕥 — decoding of a code (a constructor's type ends here)
      QEl : QTm -> QTy
      ||| A ⇛ 𝔄 — EXTERNAL Π (A a Nova type; binds a Nova variable)
      QPiExt : Ty -> QTy -> QTy
      ||| El 𝕥 ⇛ 𝔄 — INDUCTIVE Π (𝕥 a sort code; binds a ToS variable)
      QPiInd : QTm -> QTy -> QTy

  namespace Poly
    ||| One-hole polynomial codes (docs/NovaFoundation.txt, coinductive
    ||| section): the hole 𝕏, external CODE pieces, products, sums, and
    ||| the two binding formers (a left-hand El a binds a Nova variable
    ||| in the body's embedded pieces). Strict positivity is
    ||| grammatical: the hole never sits left of an exponent.
    public export
    data Poly : Type where
      ||| 𝕏 — the hole
      PHole : Poly
      ||| K a — constant at a code
      PConst : Elem -> Poly
      ||| 𝔽 × 𝔾 — product (non-binding)
      PProd : Poly -> Poly -> Poly
      ||| 𝔽 ⊎ 𝔾 — sum
      PSum : Poly -> Poly -> Poly
      ||| El a × 𝔽 — dependent pair over external data (binds)
      PSigma : Elem -> Poly -> Poly
      ||| El a → 𝔽 — exponent with external domain (binds)
      PPi : Elem -> Poly -> Poly

  ||| Ty is an ALIAS: with the type judgement dissolved into typing at
  ||| 𝕍 (TopTy), types are terms — the name survives purely as a
  ||| reading aid in signatures ("this term stands in type position").
  public export
  Ty : Type
  Ty = Elem

  ||| A QIIT signature IS a closed qiit-context: entries in declaration
  ||| order (position 0 first), ANONYMOUS — a signature mints no names.
  public export
  QSig : Type
  QSig = List QTy

  ||| SubNorm: e˲ ::= · | e˲, e
  public export
  SubNorm : Type
  SubNorm = SnocList Elem

||| Tying context: Γ ::= ε | Γ ▷ T
public export
Ctx : Type
Ctx = SnocList Ty

public export
SigIdentifier : Type
SigIdentifier = String

||| TWO entry kinds (Foundation: type definitions and type
||| declarations are the A = TopTy instances; an equation CONSTRAINT
||| is a hole at the equation's prop — a declaration at
||| (a₀ ≡ a₁ ∈ A) — used through el-sig-decl + el-reflect and
||| closed by INSTANTIATION with ⋆).
public export
data SigEntry : Type where
  ||| Γ ⊦ x ≔ a : A  (definition; a TYPE definition when A = TopTy)
  SigDef : Ctx -> SigIdentifier -> Elem -> Ty -> SigEntry
  ||| Γ ⊦ x : A  (declaration — a hole; references are stuck,
  ||| el-sig-decl; a TYPE declaration when A = TopTy; an equation
  ||| OBLIGATION when A is the equation's prop)
  SigDecl : Ctx -> SigIdentifier -> Ty -> SigEntry

||| The name a signature entry binds.
public export
sigEntryName : SigEntry -> Maybe SigIdentifier
sigEntryName (SigDef _ x _ _) = Just x
sigEntryName (SigDecl _ x _) = Just x

||| Is this entry a definition? A signature all of whose entries are
||| definitions is DEFINITIONAL (Foundation: acceptance requires it).
public export
sigEntryIsDef : SigEntry -> Bool
sigEntryIsDef (SigDef _ _ _ _) = True
sigEntryIsDef _ = False

||| Machine names for equation-obligation holes — a spelling no
||| surface identifier can take, so views can tell an obligation from
||| a user declaration. Deterministic (a per-run counter), so reruns
||| and the distill Σ-gate see stable names.
public export
oblName : Nat -> SigIdentifier
oblName n = "≐#" ++ show n

public export
isOblName : SigIdentifier -> Bool
isOblName x = isPrefixOf "≐#" x

||| Machine names for user HOLES (`?x` in a surface term) — like
||| `oblName`, a spelling no surface identifier can take, so a view
||| can tell a hole from a user declaration. The suffix is the
||| enclosing item plus the operator's own label
||| (`?streamBisim.bisimHd.a`): unique across a run and stable
||| between reruns, since it is written, not counted.
public export
holeName : (item : String) -> (label : String) -> SigIdentifier
holeName item label = if item == "" then "?" ++ label else "?" ++ item ++ "." ++ label

public export
isHoleName : SigIdentifier -> Bool
isHoleName x = isPrefixOf "?" x

||| Is this hole SYNTHETIC — minted by the elaborator for a part the
||| operator did not write (a demanded shape's component, an implicit
||| no source determined), rather than written as `?x`? A synthetic
||| label carries `/`, which a WRITTEN label cannot: the parser reads
||| a hole label as an identifier.
|||
||| The distinction is what the refinement pass is allowed to act on.
||| A synthetic hole stands for something the elaborator itself made
||| up, so determining it from the run's own constraints returns
||| information the operator never supplied. A WRITTEN hole is the
||| operator's question; answering it for them would be a guess, and
||| is never done.
public export
isSyntheticHole : SigIdentifier -> Bool
isSyntheticHole x = isHoleName x && elem '/' (unpack x)

||| The label the operator wrote, recovered from a hole's Σ name —
||| what the report shows (`?a`, not `?mod.item.a`).
public export
holeLabel : SigIdentifier -> String
holeLabel x = "?" ++ pack (reverse (takeWhile (/= '.') (reverse (unpack x))))

||| The WRITTEN hole a synthetic one belongs to: `?a/squashee` is a
||| part of `?a`. Everything before the first `/` of the label.
public export
holeOwner : SigIdentifier -> String
holeOwner x = pack (takeWhile (/= '/') (unpack (holeLabel x)))

public export
Sig : Type
Sig = SnocList SigEntry

||| Find a signature entry by name (innermost/most-recent declaration wins).
export covering
sigLookup : SigIdentifier -> Sig -> Maybe SigEntry
sigLookup _ [<] = Nothing
sigLookup x (rest :< entry) =
  if sigEntryName entry == Just x then Just entry else sigLookup x rest

||| σ⁺ ≜ σ∘↑, ☐₀
public export
under : Sub -> Sub
under sigma = Ext (Chain sigma Wk) (CtxVar 0)

-- ===== QIIT signature structure (pure syntax helpers) =====

||| Number of Π-binders of a ToS type.
public export
qtyBinders : QTy -> Nat
qtyBinders (QPiExt _ b) = S (qtyBinders b)
qtyBinders (QPiInd _ b) = S (qtyBinders b)
qtyBinders _ = Z

||| The head (result) of a ToS type, past its binders.
public export
qtyHead : QTy -> QTy
qtyHead (QPiExt _ b) = qtyHead b
qtyHead (QPiInd _ b) = qtyHead b
qtyHead h = h

||| Head variable and arguments of a ToS application chain (first-order:
||| the head is a variable; an eq-code has no chain reading).
public export
qChain : QTm -> Maybe (Nat, List (Either Elem QTm))
qChain t0 = go t0 []
 where
  go : QTm -> List (Either Elem QTm) -> Maybe (Nat, List (Either Elem QTm))
  go (QVar i) acc = Just (i, acc)
  go (QAppE f e) acc = go f (Left e :: acc)
  go (QAppI f a) acc = go f (Right a :: acc)
  go (QEqC _ _ _) _ = Nothing

||| Entry classification, by the head of the entry's type alone
||| (exhaustive: every ToS type ends in U or El).
public export
data QEntryKind = QKSort | QKPoint | QKEq

public export
Eq QEntryKind where
  QKSort == QKSort = True
  QKPoint == QKPoint = True
  QKEq == QKEq = True
  _ == _ = False

public export
qEntryKind : QTy -> QEntryKind
qEntryKind t = case qtyHead t of
  QEl (QEqC _ _ _) => QKEq
  QEl _ => QKPoint
  _ => QKSort

||| Entry positions of a given kind, in declaration order.
public export
qPositions : QEntryKind -> QSig -> List Nat
qPositions k sg = go 0 sg
 where
  go : Nat -> QSig -> List Nat
  go _ [] = []
  go i (e :: rest) =
    if qEntryKind e == k then i :: go (S i) rest else go (S i) rest

||| Position of entry k within the list of entries of its kind (e.g. a
||| sort's index into the motive vector). Nothing if k is out of range.
public export
qOrdinal : QEntryKind -> QSig -> Nat -> Maybe Nat
qOrdinal kind sg k = findIndex (== k) (qPositions kind sg)
 where
  findIndex : (Nat -> Bool) -> List Nat -> Maybe Nat
  findIndex p [] = Nothing
  findIndex p (x :: xs) = if p x then Just Z else map S (findIndex p xs)

||| Look up an entry by position.
public export
qEntry : QSig -> Nat -> Maybe QTy
qEntry sg k = getAt k sg

||| SMALLNESS (code-qiit's side condition) is JUDGEMENTAL now that El
||| and Prf are retired: every external Π domain must be typed at 𝕌
||| or at Ω. The kernel checks it (kQSigSmall); this module keeps
||| only the external-domain enumeration the checkers walk.
public export
qSigExtDomains : QSig -> List (Nat, Ty)
qSigExtDomains sg = concatMap entryDoms sg
 where
  entryDoms : QTy -> List (Nat, Ty)
  entryDoms = go 0
   where
    go : Nat -> QTy -> List (Nat, Ty)
    go d (QPiExt a b) = (d, a) :: go (S d) b
    go d (QPiInd _ b) = go d b
    go d _ = []

||| Number of binders of the sort at position k (its index arity).
public export
qArityLen : QSig -> Nat -> Nat
qArityLen sg k = maybe 0 qtyBinders (qEntry sg k)

||| Bump every ToS variable by n (the first-order fragment has no ToS
||| binders inside terms, so every QVar is free).
public export
qtmShift : Nat -> QTm -> QTm
qtmShift n (QVar i) = QVar (n + i)
qtmShift n (QAppE f e) = QAppE (qtmShift n f) e
qtmShift n (QAppI f a) = QAppI (qtmShift n f) (qtmShift n a)
qtmShift n (QEqC l r u) = QEqC (qtmShift n l) (qtmShift n r) (qtmShift n u)

mutual
  public export
  covering
  Eq Sub where
    Terminal   == Terminal   = True
    Ext s e    == Ext s' e'  = s == s' && e == e'
    Chain s t  == Chain s' t' = s == s' && t == t'
    Id         == Id         = True
    Wk         == Wk         = True
    _          == _          = False

  public export
  covering
  Eq Elem where
    CtxVar n         == CtxVar n'          = n == n'
    ZeroElim e       == ZeroElim e'        = e == e'
    OneIntro         == OneIntro           = True
    NatIntro0        == NatIntro0          = True
    NatIntro1 e      == NatIntro1 e'       = e == e'
    NatElim z s t    == NatElim z' s' t'   = z == z' && s == s' && t == t'
    PiIntro e        == PiIntro e'         = e == e'
    PiApp f e        == PiApp f' e'         = f == f' && e == e'
    Let a b          == Let a' b'           = a == a' && b == b'
    SigmaIntro e1 e2 == SigmaIntro e1' e2' = e1 == e1' && e2 == e2'
    SigmaElim1 e     == SigmaElim1 e'      = e == e'
    SigmaElim2 e     == SigmaElim2 e'      = e == e'
    Inj1 e           == Inj1 e'            = e == e'
    Inj2 e           == Inj2 e'            = e == e'
    SumElim l r t    == SumElim l' r' t'   = l == l' && r == r' && t == t'
    Elem.ZeroTy      == Elem.ZeroTy        = True
    Elem.OneTy       == Elem.OneTy         = True
    Elem.NatTy       == Elem.NatTy         = True
    UniverseTy       == UniverseTy         = True
    PropTy           == PropTy             = True
    TopTy            == TopTy              = True
    Elem.PiTy a b    == Elem.PiTy a' b'    = a == a' && b == b'
    Elem.SigmaTy a b == Elem.SigmaTy a' b' = a == a' && b == b'
    Elem.SumTy a b   == Elem.SumTy a' b'   = a == a' && b == b'
    Elem.EqTy l r t  == Elem.EqTy l' r' t' = l == l' && r == r' && t == t'
    QuotTy a r       == QuotTy a' r'       = a == a' && r == r'
    SigVar x s       == SigVar x' s'        = x == x' && s == s'
    Class a          == Class a'           = a == a'
    QuotElim f q     == QuotElim f' q'     = f == f' && q == q'
    Squash t         == Squash t'          = t == t'
    Star             == Star               = True
    QSort s k es     == QSort s' k' es'    = s == s' && k == k' && es == es'
    QCtor s k es     == QCtor s' k' es'    = s == s' && k == k' && es == es'
    QElim s k ms fs es w == QElim s' k' ms' fs' es' w' =
      s == s' && k == k' && ms == ms' && fs == fs' && es == es' && w == w'
    Elem.NuTy f      == Elem.NuTy f'       = f == f'
    Out t            == Out t'             = t == t'
    Corec p a f x    == Corec p' a' f' x'  = p == p' && a == a' && f == f' && x == x'
    _                == _                  = False

  public export
  covering
  Eq QTm where
    QVar i      == QVar i'        = i == i'
    QAppE f e   == QAppE f' e'    = f == f' && e == e'
    QAppI f a   == QAppI f' a'    = f == f' && a == a'
    QEqC l r u  == QEqC l' r' u'  = l == l' && r == r' && u == u'
    _           == _              = False

  public export
  covering
  Eq QTy where
    QU          == QU             = True
    QEl t       == QEl t'         = t == t'
    QPiExt a b  == QPiExt a' b'   = a == a' && b == b'
    QPiInd u b  == QPiInd u' b'   = u == u' && b == b'
    _           == _              = False

  public export
  covering
  Eq Poly where
    PHole       == PHole          = True
    PConst a    == PConst a'      = a == a'
    PProd f g   == PProd f' g'    = f == f' && g == g'
    PSum f g    == PSum f' g'     = f == f' && g == g'
    PSigma a f  == PSigma a' f'   = a == a' && f == f'
    PPi a f     == PPi a' f'      = a == a' && f == f'
    _           == _              = False

mutual
  public export
  covering
  Ord Sub where
    compare Terminal    Terminal    = EQ
    compare Terminal    _           = LT
    compare _           Terminal    = GT
    compare (Ext s e)   (Ext s' e') = compare s s' <+> compare e e'
    compare (Ext _ _)   _           = LT
    compare _           (Ext _ _)   = GT
    compare (Chain s t) (Chain s' t') = compare s s' <+> compare t t'
    compare (Chain _ _) _           = LT
    compare _           (Chain _ _) = GT
    compare Id          Id          = EQ
    compare Id          _           = LT
    compare _           Id          = GT
    compare Wk          Wk          = EQ

  public export
  covering
  Ord Elem where
    compare (CtxVar n)         (CtxVar n')          = compare n n'
    compare (CtxVar _)         _                    = LT
    compare _                  (CtxVar _)           = GT
    compare (ZeroElim e)       (ZeroElim e')        = compare e e'
    compare (ZeroElim _)       _                    = LT
    compare _                  (ZeroElim _)         = GT
    compare OneIntro           OneIntro             = EQ
    compare OneIntro           _                    = LT
    compare _                  OneIntro             = GT
    compare NatIntro0          NatIntro0            = EQ
    compare NatIntro0          _                    = LT
    compare _                  NatIntro0            = GT
    compare (NatIntro1 e)      (NatIntro1 e')       = compare e e'
    compare (NatIntro1 _)      _                    = LT
    compare _                  (NatIntro1 _)        = GT
    compare (NatElim z s t)    (NatElim z' s' t')   = compare z z' <+> compare s s' <+> compare t t'
    compare (NatElim _ _ _)    _                    = LT
    compare _                  (NatElim _ _ _)      = GT
    compare (PiIntro e)        (PiIntro e')         = compare e e'
    compare (PiIntro _)        _                    = LT
    compare _                  (PiIntro _)          = GT
    compare (PiApp f e)        (PiApp f' e')         = compare f f' <+> compare e e'
    compare (PiApp _ _)        _                    = LT
    compare _                  (PiApp _ _)          = GT
    compare (Let a b)          (Let a' b')          = compare a a' <+> compare b b'
    compare (Let _ _)          _                    = LT
    compare _                  (Let _ _)            = GT
    compare (SigmaIntro e1 e2) (SigmaIntro e1' e2') = compare e1 e1' <+> compare e2 e2'
    compare (SigmaIntro _ _)   _                    = LT
    compare _                  (SigmaIntro _ _)     = GT
    compare (SigmaElim1 e)     (SigmaElim1 e')      = compare e e'
    compare (SigmaElim1 _)     _                    = LT
    compare _                  (SigmaElim1 _)       = GT
    compare (SigmaElim2 e)     (SigmaElim2 e')      = compare e e'
    compare (SigmaElim2 _)     _                    = LT
    compare _                  (SigmaElim2 _)       = GT
    compare (Inj1 e)           (Inj1 e')            = compare e e'
    compare (Inj1 _)           _                    = LT
    compare _                  (Inj1 _)             = GT
    compare (Inj2 e)           (Inj2 e')            = compare e e'
    compare (Inj2 _)           _                    = LT
    compare _                  (Inj2 _)             = GT
    compare (SumElim l r t)    (SumElim l' r' t')   = compare l l' <+> compare r r' <+> compare t t'
    compare (SumElim _ _ _)    _                    = LT
    compare _                  (SumElim _ _ _)      = GT
    compare Elem.ZeroTy        Elem.ZeroTy          = EQ
    compare Elem.ZeroTy        _                    = LT
    compare _                  Elem.ZeroTy          = GT
    compare Elem.OneTy         Elem.OneTy           = EQ
    compare Elem.OneTy         _                    = LT
    compare _                  Elem.OneTy           = GT
    compare Elem.NatTy         Elem.NatTy           = EQ
    compare Elem.NatTy         _                    = LT
    compare _                  Elem.NatTy           = GT
    compare UniverseTy         UniverseTy           = EQ
    compare UniverseTy         _                    = LT
    compare _                  UniverseTy           = GT
    compare PropTy             PropTy               = EQ
    compare PropTy             _                    = LT
    compare _                  PropTy               = GT
    compare TopTy              TopTy                = EQ
    compare TopTy              _                    = LT
    compare _                  TopTy                = GT
    compare (Elem.PiTy a b)    (Elem.PiTy a' b')    = compare a a' <+> compare b b'
    compare (Elem.PiTy _ _)    _                    = LT
    compare _                  (Elem.PiTy _ _)      = GT
    compare (Elem.SigmaTy a b) (Elem.SigmaTy a' b') = compare a a' <+> compare b b'
    compare (Elem.SigmaTy _ _) _                    = LT
    compare _                  (Elem.SigmaTy _ _)   = GT
    compare (Elem.SumTy a b)   (Elem.SumTy a' b')   = compare a a' <+> compare b b'
    compare (Elem.SumTy _ _)   _                    = LT
    compare _                  (Elem.SumTy _ _)     = GT
    compare (Elem.EqTy l r t)  (Elem.EqTy l' r' t') = compare l l' <+> compare r r' <+> compare t t'
    compare (Elem.EqTy _ _ _)  _                    = LT
    compare _                  (Elem.EqTy _ _ _)    = GT
    compare (QuotTy a r)       (QuotTy a' r')       = compare a a' <+> compare r r'
    compare (QuotTy _ _)       _                    = LT
    compare _                  (QuotTy _ _)         = GT
    compare (SigVar x s)       (SigVar y t)         = compare x y <+> compare s t
    compare (SigVar _ _)       _                    = LT
    compare _                  (SigVar _ _)         = GT
    compare (Class a)          (Class a')           = compare a a'
    compare (Class _)          _                    = LT
    compare _                  (Class _)            = GT
    compare (QuotElim f q)     (QuotElim f' q')     = compare f f' <+> compare q q'
    compare (QuotElim _ _)     _                    = LT
    compare _                  (QuotElim _ _)       = GT
    compare (Squash t)         (Squash t')          = compare t t'
    compare (Squash _)         _                    = LT
    compare _                  (Squash _)           = GT
    compare Star               Star                 = EQ
    compare Star               _                    = LT
    compare _                  Star                 = GT
    compare (QSort s k es)     (QSort s' k' es')    = compare s s' <+> compare k k' <+> compare es es'
    compare (QSort _ _ _)      _                    = LT
    compare _                  (QSort _ _ _)        = GT
    compare (QCtor s k es)     (QCtor s' k' es')    = compare s s' <+> compare k k' <+> compare es es'
    compare (QCtor _ _ _)      _                    = LT
    compare _                  (QCtor _ _ _)        = GT
    compare (QElim s k ms fs es w) (QElim s' k' ms' fs' es' w') =
      compare s s' <+> compare k k' <+> compare ms ms' <+> compare fs fs' <+> compare es es' <+> compare w w'
    compare (QElim _ _ _ _ _ _) _                   = LT
    compare _                  (QElim _ _ _ _ _ _)  = GT
    compare (Elem.NuTy f)      (Elem.NuTy f')       = compare f f'
    compare (Elem.NuTy _)      _                    = LT
    compare _                  (Elem.NuTy _)        = GT
    compare (Out t)            (Out t')             = compare t t'
    compare (Out _)            _                    = LT
    compare _                  (Out _)              = GT
    compare (Corec p a f x)    (Corec p' a' f' x')  =
      compare p p' <+> compare a a' <+> compare f f' <+> compare x x'

  public export
  covering
  Ord QTm where
    compare (QVar i)     (QVar i')      = compare i i'
    compare (QVar _)     _              = LT
    compare _            (QVar _)       = GT
    compare (QAppE f e)  (QAppE f' e')  = compare f f' <+> compare e e'
    compare (QAppE _ _)  _              = LT
    compare _            (QAppE _ _)    = GT
    compare (QAppI f a)  (QAppI f' a')  = compare f f' <+> compare a a'
    compare (QAppI _ _)  _              = LT
    compare _            (QAppI _ _)    = GT
    compare (QEqC l r u) (QEqC l' r' u') = compare l l' <+> compare r r' <+> compare u u'

  public export
  covering
  Ord QTy where
    compare QU            QU              = EQ
    compare QU            _               = LT
    compare _             QU              = GT
    compare (QEl t)       (QEl t')        = compare t t'
    compare (QEl _)       _               = LT
    compare _             (QEl _)         = GT
    compare (QPiExt a b)  (QPiExt a' b')  = compare a a' <+> compare b b'
    compare (QPiExt _ _)  _               = LT
    compare _             (QPiExt _ _)    = GT
    compare (QPiInd u b)  (QPiInd u' b')  = compare u u' <+> compare b b'

  public export
  covering
  Ord Poly where
    compare PHole         PHole           = EQ
    compare PHole         _               = LT
    compare _             PHole           = GT
    compare (PConst a)    (PConst a')     = compare a a'
    compare (PConst _)    _               = LT
    compare _             (PConst _)      = GT
    compare (PProd f g)   (PProd f' g')   = compare f f' <+> compare g g'
    compare (PProd _ _)   _               = LT
    compare _             (PProd _ _)     = GT
    compare (PSum f g)    (PSum f' g')    = compare f f' <+> compare g g'
    compare (PSum _ _)    _               = LT
    compare _             (PSum _ _)      = GT
    compare (PSigma a f)  (PSigma a' f')  = compare a a' <+> compare f f'
    compare (PSigma _ _)  _               = LT
    compare _             (PSigma _ _)    = GT
    compare (PPi a f)     (PPi a' f')     = compare a a' <+> compare f f'

mutual
  public export
  covering
  Show Sub where
    show Terminal = "Terminal"
    show (Ext s e) = "Ext (\{show s}) (\{show e})"
    show (Chain s t) = "Chain (\{show s}) (\{show t})"
    show Id = "Id"
    show Wk = "Wk"

  public export
  covering
  Show Elem where
    show (CtxVar n) = "CtxVar \{show n}"
    show (ZeroElim e) = "ZeroElim (\{show e})"
    show OneIntro = "OneIntro"
    show NatIntro0 = "NatIntro0"
    show (NatIntro1 e) = "NatIntro1 (\{show e})"
    show (NatElim z s t) = "NatElim (\{show z}) (\{show s}) (\{show t})"
    show (PiIntro e) = "PiIntro (\{show e})"
    show (PiApp f e) = "PiApp (\{show f}) (\{show e})"
    show (Let a b) = "Let (\{show a}) (\{show b})"
    show (SigmaIntro e1 e2) = "SigmaIntro (\{show e1}) (\{show e2})"
    show (SigmaElim1 e) = "SigmaElim1 (\{show e})"
    show (SigmaElim2 e) = "SigmaElim2 (\{show e})"
    show (Inj1 e) = "Inj1 (\{show e})"
    show (Inj2 e) = "Inj2 (\{show e})"
    show (SumElim l r t) = "SumElim (\{show l}) (\{show r}) (\{show t})"
    show Elem.ZeroTy = "ZeroTy"
    show Elem.OneTy = "OneTy"
    show Elem.NatTy = "NatTy"
    show UniverseTy = "UniverseTy"
    show PropTy = "PropTy"
    show TopTy = "TopTy"
    show (Elem.PiTy e1 e2) = "PiTy (\{show e1}) (\{show e2})"
    show (Elem.SigmaTy e1 e2) = "SigmaTy (\{show e1}) (\{show e2})"
    show (Elem.SumTy e1 e2) = "SumTy (\{show e1}) (\{show e2})"
    show (Elem.EqTy e0 e1 t) = "EqTy (\{show e0}) (\{show e1}) (\{show t})"
    show (QuotTy a r) = "QuotTy (\{show a}) (\{show r})"
    show (SigVar x s) = "SigVar \{show x} (\{show s})"
    show (Class a) = "Class (\{show a})"
    show (QuotElim f q) = "QuotElim (\{show f}) (\{show q})"
    show (Squash t) = "Squash (\{show t})"
    show Star = "Star"
    show (QSort s k es) = "QSort (\{show s}) \{show k} (\{show es})"
    show (QCtor s k es) = "QCtor (\{show s}) \{show k} (\{show es})"
    show (QElim s k ms fs es w) =
      "QElim (\{show s}) \{show k} (\{show ms}) (\{show fs}) (\{show es}) (\{show w})"
    show (Elem.NuTy f) = "NuTy (\{show f})"
    show (Out t) = "Out (\{show t})"
    show (Corec p a f x) = "Corec (\{show p}) (\{show a}) (\{show f}) (\{show x})"

  public export
  covering
  Show QTm where
    show (QVar i) = "QVar \{show i}"
    show (QAppE f e) = "QAppE (\{show f}) (\{show e})"
    show (QAppI f a) = "QAppI (\{show f}) (\{show a})"
    show (QEqC l r u) = "QEqC (\{show l}) (\{show r}) (\{show u})"

  public export
  covering
  Show QTy where
    show QU = "QU"
    show (QEl t) = "QEl (\{show t})"
    show (QPiExt a b) = "QPiExt (\{show a}) (\{show b})"
    show (QPiInd u b) = "QPiInd (\{show u}) (\{show b})"

  public export
  covering
  Show Poly where
    show PHole = "PHole"
    show (PConst a) = "PConst (\{show a})"
    show (PProd f g) = "PProd (\{show f}) (\{show g})"
    show (PSum f g) = "PSum (\{show f}) (\{show g})"
    show (PSigma a f) = "PSigma (\{show a}) (\{show f})"
    show (PPi a f) = "PPi (\{show a}) (\{show f})"
