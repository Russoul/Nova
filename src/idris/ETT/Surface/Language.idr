module ETT.Surface.Language

import Data.Location
import Data.List1

import ETT.Core.Name

-- h ::= Z | Refl | x | S | ℕ-elim | J | ℕ | 𝕌 | !x | ?x | Π-β | Π-η | Π⁼ | ℕ-β-Z | ℕ-β-S

-- e{0} = x ↦ e{≥0} | (x : e{≥0}) → e{≥0} | (x : {≥0}) ⨯ e{≥0} | (x : e{≥0}) ↦ e{≥0}
-- e{1} = e{≥3} ≡ e{≥3} ∈ e{≥0} | e{≥3} ⨯ e{≥3}
-- e{2} = e{≥3} → e{≥2}
-- e{3} = h ē⁺ where |ē⁺| > 0
-- e{4} = h | (e{≥0}) | (e{≥0}, e{≥0})

-- e⁺{0} = x̅.̅ e{≥0}
-- e⁺{1} = e{≥4} | (e⁺{≥0}) | .π₁ | .π₂
-- ē⁺ ::= ␣ e⁺{1} ē⁺ | ·

-- top-level ::= assume x : e{≥0} | let x : e{≥0} ≔ e{≥0}

mutual
  public export
  data Head : Type where
    Var : Range -> VarName -> Head
    NatVal0 : Range -> Head
    NatVal1 : Range -> Head
    NatElim : Range -> Head
    EqElim : Range -> Head
    EqVal : Range -> Head
    NatTy : Range -> Head
    UniverseTy : Range -> Head
    Hole : Range -> VarName -> Maybe (List VarName) -> Head
    UnnamedHole : Range -> Maybe (List VarName) -> Head
    Unfold : Range -> VarName -> Head
    PiBeta : Range -> Head
    PiEta : Range -> Head
    NatBetaZ : Range -> Head
    NatBetaS : Range -> Head
    PiEq : Range -> Head
    Tm : Range -> Term -> Head

  public export
  data Term : Type where
    PiTy : Range -> VarName -> Term -> Term -> Term
    SigmaTy : Range -> VarName -> Term -> Term -> Term
    FunTy : Range -> Term -> Term -> Term
    ProdTy : Range -> Term -> Term -> Term
    EqTy : Range -> Term -> Term -> Term -> Term
    PiVal : Range -> VarName -> Term -> Term
    SigmaVal : Range -> Term -> Term -> Term
    AnnotatedPiVal : Range -> VarName -> Term -> Term -> Term
    App : Range -> Head -> Elim -> Term

  public export
  TermArg : Type
  TermArg = (List VarName, Term)

  namespace ElimEntry
    public export
    data ElimEntry : Type where
      Arg : TermArg -> ElimEntry
      Pi1 : ElimEntry
      Pi2 : ElimEntry

  public export
  Elim : Type
  Elim = List ElimEntry

public export
range : Term -> Range
range (PiTy r str y z) = r
range (SigmaTy r str y z) = r
range (FunTy r y z) = r
range (ProdTy r a b) = r
range (EqTy r y z w) = r
range (PiVal r str y) = r
range (SigmaVal r a b) = r
range (AnnotatedPiVal r str y _) = r
range (App r y xs) = r

mutual
  partial
  public export
  Show ElimEntry where
    show (Arg arg) = "Arg(\{show arg})"
    show Pi1 = ".π₁"
    show Pi2 = ".π₂"

  public export
  partial
  Show Head where
    show (PiBeta _) = "Π-β"
    show (PiEta _) = "Π-η"
    show (NatBetaZ _) = "ℕ-β-Z"
    show (NatBetaS _) = "ℕ-β-S"
    show (Unfold _ x) = "Unfold(\{x})"
    show (Hole _ x ls) = "Hole(\{x}, \{show ls})"
    show (UnnamedHole _ ls) = "UnnamedHole(\{show ls})"
    show (Var _ x) = "Var(\{x})"
    show (NatVal0 x) = "Z"
    show (NatVal1 x) = "S"
    show (NatElim x) = "ℕ-elim"
    show (EqElim x) = "J"
    show (EqVal x) = "Refl"
    show (NatTy x) = "ℕ"
    show (UniverseTy x) = "𝕌"
    show (PiEq x) = "PiEq"
    show (Tm x tm) = "Tm(\{show tm})"

  public export
  partial
  Show Term where
    show (PiTy _ x a b) = "PiTy(\{show a}, \{show b})"
    show (FunTy _ a b) = "FunTy(\{show a}, \{show b})"
    show (EqTy _ a b ty) = "EqTy(\{show a}, \{show b}, \{show ty})"
    show (PiVal _ x f) = "PiVal(\{x}, \{show f})"
    show (AnnotatedPiVal _ x ty f) = "AnnotatedPiVal(\{x}, \{show ty}, \{show f})"
    show (App _ x spine) = "App(\{show x}, \{show spine})"

public export
data TopLevel : Type where
  ||| assume x : T
  TypingSignature : Range -> VarName -> Term -> TopLevel
  ||| let x : T
  |||       ≔ t
  LetSignature : Range -> VarName -> Term -> Term -> TopLevel
