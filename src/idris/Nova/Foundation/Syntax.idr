module Nova.Foundation.Syntax

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
      ||| T / T  (quotient type: the second Ty is the relation, living two
      ||| levels deeper — Γ ᐅ A ᐅ A[↑] — one bound variable per side)
      Quotient : Ty -> Ty -> Ty
      ||| x[e˲]  (signature type variable, applied to a (normal)
      ||| substitution to its declaration context)
      SigVar : String -> SubNorm -> Ty

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
      ||| relation code, living two levels deeper — Γ ᐅ El a ᐅ (El a)[↑] —
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

  ||| SubNorm: e˲ ::= · | e˲, e
  public export
  SubNorm : Type
  SubNorm = SnocList Elem

||| Tying context: Γ ::= ε | Γ ᐅ T
public export
Ctx : Type
Ctx = SnocList Ty

||| Tye telescope: Δ ::= ε | T ◁ Δ
public export
Tel : Type
Tel = List Ty

||| Spine: ē ::= · | e, ē
public export
Spine : Type
Spine = List Elem

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
    Quotient a r   == Quotient a' r'   = a == a' && r == r'
    Ty.SigVar x s  == Ty.SigVar x' s'  = x == x' && s == s'
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
    _                == _                  = False

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
    compare (Quotient a r)   (Quotient a' r')   = compare a a' <+> compare r r'
    compare (Quotient _ _)   _                  = LT
    compare _                (Quotient _ _)     = GT
    compare (Ty.SigVar x s)  (Ty.SigVar y t)    = compare x y <+> compare s t

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
    show (Quotient a r) = "Quotient (\{show a}) (\{show r})"
    show (Ty.SigVar x s) = "SigVar \{show x} (\{show s})"

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
