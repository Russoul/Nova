module ETT.Surface.Elaboration

import ETT.Core.Monad
import ETT.Core.Language

import ETT.Surface.Language

CoreElem = ETT.Core.Language.D.Elem
SurfaceTerm = ETT.Surface.Language.Term

public export
data MetaKind = SolveByUnification | SolveByElaboration

public export
data ElaborationEntry : Type where
  ||| Γ ⊦ ?x : T
  Meta : Context -> (ty : CoreElem) -> MetaKind -> ElaborationEntry
  ||| Γ ⊦ ?x ≔ t : T
  MetaInst : Context -> (rhs : CoreElem) -> (ty : CoreElem) -> MetaKind -> ElaborationEntry
  ||| Γ ⊦ ⟦t⟧ ⇝ p : T
  ElemElaboration : Context -> SurfaceTerm -> Nat -> CoreElem -> ElaborationEntry
  ||| Γ ⊦ (t : T) ⟦ē⟧ ⇝ p : C
  ElemElimElaboration : Context -> CoreElem -> CoreElem -> Elim -> Nat -> CoreElem -> ElaborationEntry
  ||| Γ ⊦ A ~ B type
  TypeConstraint : Context -> CoreElem -> CoreElem -> ElaborationEntry

||| Σ Ω ⊦ Ξ₀ (Γ ⊦ p : A) Ξ₁ (Γ(↑(1 + Ξ₁)) ⊦ ⟦t⟧ ⇝ p : A(↑(1 + Ξ₁))) Ξ₂
public export
elabElem : Signature
        -> Constraints
        -> List ElaborationEntry
        -> (gamma : Context)
        -> CoreElem
        -> List ElaborationEntry
        -> SurfaceTerm
        -> Nat
        -> List ElaborationEntry
        -> M (List ElaborationEntry)
elabElem sig cs xi0 gamma ty xi1 t p xi2 = ?ff
