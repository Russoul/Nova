module Nova.Kernel.Syntax

import Data.List
import Data.SnocList

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

  namespace Ty
    public export
    data Ty : Type where
      ||| 𝟘
      ZeroTy : Ty
      ||| 𝟙
      OneTy : Ty
      ||| ℕ
      NatTy : Ty
      ||| 𝕌
      UniverseTy : Ty
      ||| T → T  (dependent product type, Π)
      PiTy : Ty -> Ty -> Ty
      ||| T ⨯ T  (dependent sum type, Σ)
      SigmaTy : Ty -> Ty -> Ty
      ||| t ≡ t ∈ T  (extensional equality type)
      EqTy : Elem -> Elem -> Ty -> Ty
      ||| El t  (every element of the universe is a type)
      El : Elem -> Ty
      ||| Ω  (the universe of mere propositions — anti-structural: its
      ||| codes are compared by inhabitation, see code-prop-eq)
      PropTy : Ty
      ||| Prf t  (decoding of a proposition; deliberately not El — it
      ||| shares none of El's rules: not structural, not injective, no
      ||| decoding computation)
      Prf : Elem -> Ty
      ||| T / t  (quotient type: the Elem is the Ω-valued relation,
      ||| living two levels deeper — Γ ▷ A ▷ A[↑] — one bound variable
      ||| per side)
      Quotient : Ty -> Elem -> Ty
      ||| x[e˲]  (signature type variable, applied to a (normal)
      ||| substitution to its declaration context)
      SigVar : String -> SubNorm -> Ty
      ||| 𝒮.k ē  (the sort at entry position k of the carried QIIT
      ||| signature, at index spine ē — ty-qiit)
      QSort : QSig -> Nat -> SubNorm -> Ty

  namespace Elem
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
      ||| t , t (sigma introduction / pair)
      SigmaIntro : Elem -> Elem -> Elem
      ||| t .π₁  (sigma elimination, first projection)
      SigmaElim1 : Elem -> Elem
      ||| t .π₂  (sigma elimination, second projection)
      SigmaElim2 : Elem -> Elem
      ||| 𝟘  (universe element)
      ZeroTy : Elem
      ||| 𝟙  (universe element)
      OneTy : Elem
      ||| ℕ  (universe element)
      NatTy : Elem
      ||| t → t  (universe element encoding Π)
      PiTy : Elem -> Elem -> Elem
      ||| t ⨯ t  (universe element encoding Σ)
      SigmaTy : Elem -> Elem -> Elem
      ||| t ≡ t ∈ t  (universe element encoding equality)
      EqTy : Elem -> Elem -> Elem -> Elem
      ||| t / t  (universe element encoding quotient: the second Elem is the
      ||| relation code, living two levels deeper — Γ ▷ El a ▷ (El a)[↑] —
      ||| one bound variable per side)
      QuotTy : Elem -> Elem -> Elem
      ||| Refl  (reflexivity)
      Refl : Elem
      ||| x[σ]  (signature variable, applied to a (normal) substitution to its
      ||| declaration context)
      SigVar : String -> SubNorm -> Elem
      ||| class t (quotient type introduction)
      Class : Elem -> Elem
      ||| quot-elim t t (quotient type elimination: the recursion function,
      ||| then the eliminee)
      QuotElim : Elem -> Elem -> Elem
      ||| ∥T∥  (squash: the proposition of an arbitrary type — an element
      ||| form embedding a type, the converse direction of El)
      Squash : Ty -> Elem
      ||| ⋆  (the canonical proof of a true proposition)
      Star : Elem
      ||| 𝒮.k ē  (universe code for the sort at entry position k of the
      ||| carried signature — SMALL signatures only, code-qiit)
      QSortC : QSig -> Nat -> SubNorm -> Elem
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

public export
data SigEntry : Type where
  ||| Γ ⊦ x ≔ a : A  (term definition)
  SigDef : Ctx -> SigIdentifier -> Elem -> Ty -> SigEntry
  ||| Γ ⊦ x ≔ A type  (type definition)
  SigTyDef : Ctx -> SigIdentifier -> Ty -> SigEntry

||| The name a signature entry binds.
public export
sigEntryName : SigEntry -> SigIdentifier
sigEntryName (SigDef _ x _ _) = x
sigEntryName (SigTyDef _ x _) = x

public export
Sig : Type
Sig = SnocList SigEntry

||| Find a signature entry by name (innermost/most-recent declaration wins).
export covering
sigLookup : SigIdentifier -> Sig -> Maybe SigEntry
sigLookup _ [<] = Nothing
sigLookup x (rest :< entry) =
  if sigEntryName entry == x then Just entry else sigLookup x rest

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

||| SMALLNESS scan (code-qiit's side condition): every external Π domain
||| anywhere in the signature is El- or Prf-headed — codable, so the
||| universe's PER construction never consults its own totality.
public export
qSigSmall : QSig -> Bool
qSigSmall = all smallEntry
 where
  smallDom : Ty -> Bool
  smallDom (El _) = True
  smallDom (Prf _) = True
  smallDom _ = False
  smallEntry : QTy -> Bool
  smallEntry (QPiExt a b) = smallDom a && smallEntry b
  smallEntry (QPiInd _ b) = smallEntry b
  smallEntry _ = True

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
  Eq Ty where
    ZeroTy         == ZeroTy           = True
    OneTy          == OneTy            = True
    NatTy          == NatTy            = True
    UniverseTy     == UniverseTy       = True
    PiTy a b       == PiTy a' b'       = a == a' && b == b'
    SigmaTy a b    == SigmaTy a' b'    = a == a' && b == b'
    EqTy l r ty    == EqTy l' r' ty'   = l == l' && r == r' && ty == ty'
    El e           == El e'            = e == e'
    PropTy         == PropTy           = True
    Prf e          == Prf e'           = e == e'
    Quotient a r   == Quotient a' r'   = a == a' && r == r'
    Ty.SigVar x s  == Ty.SigVar x' s'  = x == x' && s == s'
    QSort s k es   == QSort s' k' es'  = s == s' && k == k' && es == es'
    _              == _                = False

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
    SigmaIntro e1 e2 == SigmaIntro e1' e2' = e1 == e1' && e2 == e2'
    SigmaElim1 e     == SigmaElim1 e'      = e == e'
    SigmaElim2 e     == SigmaElim2 e'      = e == e'
    Elem.ZeroTy      == Elem.ZeroTy        = True
    Elem.OneTy       == Elem.OneTy         = True
    Elem.NatTy       == Elem.NatTy         = True
    Elem.PiTy a b    == Elem.PiTy a' b'    = a == a' && b == b'
    Elem.SigmaTy a b == Elem.SigmaTy a' b' = a == a' && b == b'
    Elem.EqTy l r t  == Elem.EqTy l' r' t' = l == l' && r == r' && t == t'
    QuotTy a r       == QuotTy a' r'       = a == a' && r == r'
    Refl             == Refl               = True
    SigVar x s       == SigVar x' s'        = x == x' && s == s'
    Class a          == Class a'           = a == a'
    QuotElim f q     == QuotElim f' q'     = f == f' && q == q'
    Squash t         == Squash t'          = t == t'
    Star             == Star               = True
    QSortC s k es    == QSortC s' k' es'   = s == s' && k == k' && es == es'
    QCtor s k es     == QCtor s' k' es'    = s == s' && k == k' && es == es'
    QElim s k ms fs es w == QElim s' k' ms' fs' es' w' =
      s == s' && k == k' && ms == ms' && fs == fs' && es == es' && w == w'
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
  Ord Ty where
    compare ZeroTy           ZeroTy             = EQ
    compare ZeroTy           _                  = LT
    compare _                ZeroTy             = GT
    compare OneTy            OneTy              = EQ
    compare OneTy            _                  = LT
    compare _                OneTy              = GT
    compare NatTy            NatTy              = EQ
    compare NatTy            _                  = LT
    compare _                NatTy              = GT
    compare UniverseTy       UniverseTy         = EQ
    compare UniverseTy       _                  = LT
    compare _                UniverseTy         = GT
    compare (PiTy a b)       (PiTy a' b')       = compare a a' <+> compare b b'
    compare (PiTy _ _)       _                  = LT
    compare _                (PiTy _ _)         = GT
    compare (SigmaTy a b)    (SigmaTy a' b')    = compare a a' <+> compare b b'
    compare (SigmaTy _ _)    _                  = LT
    compare _                (SigmaTy _ _)      = GT
    compare (EqTy l r ty)    (EqTy l' r' ty')   = compare l l' <+> compare r r' <+> compare ty ty'
    compare (EqTy _ _ _)     _                  = LT
    compare _                (EqTy _ _ _)       = GT
    compare (El e)           (El e')            = compare e e'
    compare (El _)           _                  = LT
    compare _                (El _)             = GT
    compare PropTy           PropTy             = EQ
    compare PropTy           _                  = LT
    compare _                PropTy             = GT
    compare (Prf e)          (Prf e')           = compare e e'
    compare (Prf _)          _                  = LT
    compare _                (Prf _)            = GT
    compare (Quotient a r)   (Quotient a' r')   = compare a a' <+> compare r r'
    compare (Quotient _ _)   _                  = LT
    compare _                (Quotient _ _)     = GT
    compare (Ty.SigVar x s)  (Ty.SigVar y t)    = compare x y <+> compare s t
    compare (Ty.SigVar _ _)  _                  = LT
    compare _                (Ty.SigVar _ _)    = GT
    compare (QSort s k es)   (QSort s' k' es')  = compare s s' <+> compare k k' <+> compare es es'

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
    compare (SigmaIntro e1 e2) (SigmaIntro e1' e2') = compare e1 e1' <+> compare e2 e2'
    compare (SigmaIntro _ _)   _                    = LT
    compare _                  (SigmaIntro _ _)     = GT
    compare (SigmaElim1 e)     (SigmaElim1 e')      = compare e e'
    compare (SigmaElim1 _)     _                    = LT
    compare _                  (SigmaElim1 _)       = GT
    compare (SigmaElim2 e)     (SigmaElim2 e')      = compare e e'
    compare (SigmaElim2 _)     _                    = LT
    compare _                  (SigmaElim2 _)       = GT
    compare Elem.ZeroTy        Elem.ZeroTy          = EQ
    compare Elem.ZeroTy        _                    = LT
    compare _                  Elem.ZeroTy          = GT
    compare Elem.OneTy         Elem.OneTy           = EQ
    compare Elem.OneTy         _                    = LT
    compare _                  Elem.OneTy           = GT
    compare Elem.NatTy         Elem.NatTy           = EQ
    compare Elem.NatTy         _                    = LT
    compare _                  Elem.NatTy           = GT
    compare (Elem.PiTy a b)    (Elem.PiTy a' b')    = compare a a' <+> compare b b'
    compare (Elem.PiTy _ _)    _                    = LT
    compare _                  (Elem.PiTy _ _)      = GT
    compare (Elem.SigmaTy a b) (Elem.SigmaTy a' b') = compare a a' <+> compare b b'
    compare (Elem.SigmaTy _ _) _                    = LT
    compare _                  (Elem.SigmaTy _ _)   = GT
    compare (Elem.EqTy l r t)  (Elem.EqTy l' r' t') = compare l l' <+> compare r r' <+> compare t t'
    compare (Elem.EqTy _ _ _)  _                    = LT
    compare _                  (Elem.EqTy _ _ _)    = GT
    compare (QuotTy a r)       (QuotTy a' r')       = compare a a' <+> compare r r'
    compare (QuotTy _ _)       _                    = LT
    compare _                  (QuotTy _ _)         = GT
    compare Refl               Refl                 = EQ
    compare Refl               _                    = LT
    compare _                  Refl                 = GT
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
    compare (QSortC s k es)    (QSortC s' k' es')   = compare s s' <+> compare k k' <+> compare es es'
    compare (QSortC _ _ _)     _                    = LT
    compare _                  (QSortC _ _ _)       = GT
    compare (QCtor s k es)     (QCtor s' k' es')    = compare s s' <+> compare k k' <+> compare es es'
    compare (QCtor _ _ _)      _                    = LT
    compare _                  (QCtor _ _ _)        = GT
    compare (QElim s k ms fs es w) (QElim s' k' ms' fs' es' w') =
      compare s s' <+> compare k k' <+> compare ms ms' <+> compare fs fs' <+> compare es es' <+> compare w w'

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
  Show Ty where
    show ZeroTy = "ZeroTy"
    show OneTy = "OneTy"
    show NatTy = "NatTy"
    show UniverseTy = "UniverseTy"
    show (PiTy a b) = "PiTy (\{show a}) (\{show b})"
    show (SigmaTy a b) = "SigmaTy (\{show a}) (\{show b})"
    show (EqTy e0 e1 a) = "EqTy (\{show e0}) (\{show e1}) (\{show a})"
    show (El e) = "El (\{show e})"
    show PropTy = "PropTy"
    show (Prf e) = "Prf (\{show e})"
    show (Quotient a r) = "Quotient (\{show a}) (\{show r})"
    show (Ty.SigVar x s) = "SigVar \{show x} (\{show s})"
    show (QSort s k es) = "QSort (\{show s}) \{show k} (\{show es})"

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
    show (SigmaIntro e1 e2) = "SigmaIntro (\{show e1}) (\{show e2})"
    show (SigmaElim1 e) = "SigmaElim1 (\{show e})"
    show (SigmaElim2 e) = "SigmaElim2 (\{show e})"
    show Elem.ZeroTy = "ZeroTy"
    show Elem.OneTy = "OneTy"
    show Elem.NatTy = "NatTy"
    show (Elem.PiTy e1 e2) = "PiTy (\{show e1}) (\{show e2})"
    show (Elem.SigmaTy e1 e2) = "SigmaTy (\{show e1}) (\{show e2})"
    show (Elem.EqTy e0 e1 e2) = "EqTy (\{show e0}) (\{show e1}) (\{show e2})"
    show (QuotTy a r) = "QuotTy (\{show a}) (\{show r})"
    show Refl = "Refl"
    show (SigVar x s) = "SigVar \{show x} (\{show s})"
    show (Class a) = "Class (\{show a})"
    show (QuotElim f q) = "QuotElim (\{show f}) (\{show q})"
    show (Squash t) = "Squash (\{show t})"
    show Star = "Star"
    show (QSortC s k es) = "QSortC (\{show s}) \{show k} (\{show es})"
    show (QCtor s k es) = "QCtor (\{show s}) \{show k} (\{show es})"
    show (QElim s k ms fs es w) =
      "QElim (\{show s}) \{show k} (\{show ms}) (\{show fs}) (\{show es}) (\{show w})"

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
