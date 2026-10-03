(* The SURFACE syntax: the proof language, the one input of the checker
   (docs/NovaKernel.txt). Every node is a proof of an equation; a proof
   with no equational leaf proves a reflexive one, and that is how
   motives, carriers, annotation types and definienda are written. A
   sort named by an eliminator is an input; a polynomial or signature
   embedded here has proofs for its Nova pieces. *)

open Core

type t =
  (* Π *)
  | Lam of t (* λ α *)
  | App of t * t (* α β *)
  | Pi of t * t (* α → β *)
  (* Σ *)
  | Fst of t (* α .π₁ *)
  | Snd of t (* α .π₂ *)
  | Pair of t * t (* [α, β] *)
  | Sigma of t * t (* α × β *)
  (* records: label and proof per entry, a SNOC list *)
  | Rec of (name * t) list
    (* Rec l̄ ᾱ: each entry proof over the entries before it *)
  | Record of (name * t) list (* ⟨l̄ ↪ ᾱ⟩ *)
  | Field of t * name (* ρ .l *)
  (* ⊎ *)
  | Inl of t
  | Inr of t
  | Sum of t * t (* α ⊎ β *)
  | SumElim of sort * t * t * t * t (* ⊎-elim U C λ ρ τ *)
  (* quotients *)
  | Class of t
  | QuotEq of t * t * t (* quot-eq α β ρ *)
  | Quot of t * t (* α / ρ *)
  | QuotElim of sort * t * t * t * t (* quot-elim U B φ ω κ *)
  (* 𝟘, 𝟙, ℕ *)
  | Zero
  | ZeroElim of t
  | One
  | Unit (* () *)
  | Nat
  | Z
  | S of t
  | NatElim of sort * t * t * t * t (* ℕ-elim U A α β τ *)
  (* ≡ *)
  | Refl of t
  | Reflect of t
  | Eq of t * t * t (* α ≡ β ∈ τ *)
  (* sorts as terms *)
  | Sort of sort
  (* ∥·∥ and the propositions *)
  | SquashTy of t (* ∥α∥ *)
  | Squash of t (* squash α *)
  | Unsquash of t * t * t (* unsquash γ α β *)
  | Irrel of t * t (* irrel α β: at 𝟙 or 𝟘 *)
  | PropIrrel of t * t * t (* prop-irrel γ α β *)
  | Propext of t * t * t * t (* propext ρ θ γ ι *)
  (* modal *)
  | Lift of t
  | Restrict of t * t * t (* restrict γ₀ γ₁ α *)
  | Conv of t * t (* conv α β *)
  | Annot of t * t (* (α : T) *)
  (* contextual *)
  | Var of int (* ☐ᵢ *)
  | Item of name * t list (* x ᾱ *)
  | Delta of name * t list (* δ x ē *)
  | Trans of t * t (* α ; β *)
  | Sym of t (* α ⁻¹ *)
  | Let of t * t (* let α β *)
  (* η *)
  | EtaPi of t (* η→ φ *)
  | EtaSigma of t (* η× π *)
  | EtaRec of t (* ηRec ρ *)
  (* ν *)
  | Nu of t poly (* ν φ *)
  | Out of t
  | Corec of t poly * t * t * t (* corec 𝔽 (s : a. φ) χ *)
  | EtaNu of t poly * t * t * t * t * t (* ην 𝔽 (s : a. f) (s. h) α x *)
  | Coind of t * t * t * t * t (* coind t₀ t₁ (x y. R) p (x y h. q) *)
  (* QIITs *)
  | QSort of t signature * int * t list (* ϑ.𝕤 ᾱ *)
  | QCon of t signature * int * t list (* ϑ.𝕔 ᾱ *)
  | QElim of t signature * int * sort list * t list * t list * t
(* 𝒮.𝕤-elim Ū δ̄ ᾱ κ: the target sorts, one per sort entry; the whole
   displayed spine (motives, methods, coherences); the index spine;
   the scrutinee *)
