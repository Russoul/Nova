(* The CORE syntax: what the checker produces and compares
   (docs/NovaKernel.txt). Terms and types are one grammar — a type is a
   term at a sort — in de Bruijn form. Eliminators carry no motive and
   name no sort: those are surface, read by the checker and dropped.

   TWO list shapes, after the foundation. A context Γ, a normal
   substitution e˲ (the arguments of a reference x[e˲]), the signature
   Σ and a qiit-context Φ are SNOC lists: the head is the newest entry,
   the one ☐₀ (or ⬡₀) names. A telescope Δ, a spine ē against one and a
   label list l̄ are CONS lists: the head is the FIRST entry, and the
   entry at position i is under the i entries before it.
   "t under A" means t is over the current context extended by A. *)

exception Reject of string

let reject fmt = Printf.ksprintf (fun s -> raise (Reject s)) fmt

(* A number in SUBSCRIPT digits — how an index (☐₀, ⬡₂) and a universe
   level (𝕌₁) are written, in reports as in the document. *)
let subscript (n : int) : string =
  let digits = [| "₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉" |] in
  String.concat ""
    (List.map
       (fun c -> digits.(Char.code c - Char.code '0'))
       (List.of_seq (String.to_seq (string_of_int n))))

type sort = Omega | U of int

(* |Ω| = 0, |𝕌ℓ| = ℓ *)
let level = function Omega -> 0 | U l -> l

(* Ω ≤ 𝕌₀ ≤ 𝕌₁ ≤ … *)
let sort_le a b =
  match (a, b) with
  | Omega, _ -> true
  | U _, Omega -> false
  | U l, U l' -> l <= l'

type name = string

type tm =
  (* contextual *)
  | Var of int (* ☐ᵢ *)
  | Item of name * tm list (* x[e˲]: a normal substitution, snoc *)
  (* Π *)
  | Pi of tm * tm (* A → B, B under A *)
  | Lam of tm
  | App of tm * tm
  (* Σ *)
  | Sigma of tm * tm (* A × B, B under A *)
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  (* records: a telescope with a label per entry. Labels and telescope
     are parallel CONS lists — the head is the first entry — and the
     entry at position i is under the i entries before it. A label is
     inert: compared as a string, never bound. *)
  | Rec of name list * tm list (* Rec l̄ Δ *)
  | Record of name list * tm list (* ⟨l̄ ↪ ē⟩: a spine of Δ, labelled *)
  | Field of tm * name (* t.l *)
  (* ⊎ *)
  | Sum of tm * tm
  | Inl of tm
  | Inr of tm
  | SumElim of tm * tm * tm (* l r t; l under A, r under B *)
  (* quotients *)
  | Quot of tm * tm (* A / R; R under A, A[↑] *)
  | Class of tm
  | QuotElim of tm * tm (* f q; f under A *)
  (* 𝟘, 𝟙 *)
  | Zero
  | ZeroElim of tm
  | One
  | Unit (* () *)
  (* ℕ *)
  | Nat
  | Z
  | S of tm
  | NatElim of tm * tm * tm (* z s t; s under ℕ, A *)
  (* ≡ and the propositions *)
  | Eq of tm * tm * tm (* a ≡ b ∈ T *)
  | Star (* ⋆ *)
  | Squash of tm (* ∥A∥ *)
  (* sorts as terms *)
  | Sort of sort
  (* let *)
  | Let of tm * tm (* let a b; b under A, (☐₀ ≡ a ∈ A) *)
  (* ν *)
  | Nu of tm poly
  | Out of tm
  | Corec of tm poly * tm * tm (* corec 𝔽 f x; f under the carrier *)
  (* QIITs: the signature is carried literally; 𝕤 and 𝕔 are ToS
     indices into it, counted like ⬡ᵢ *)
  | QSort of tm signature * int * tm list (* 𝒮.𝕤 ē, ē a spine (cons) *)
  | QCon of tm signature * int * tm list
    (* 𝒮.𝕔 θ, always SATURATED: θ is the constructor's whole arity. The
         spine judgement admits nothing shorter, ι builds it under exactly
         its arity's λs, and its type is a sort, so nothing applies it
         further; a partial constructor is not a term. *)
  | QElim of tm signature * int * tm list * tm list * tm
(* 𝒮.𝕤-elim m̄ ē w: the methods, one per point entry in signature
   order from the first; the index spine; the scrutinee *)

(* A polynomial, generic in its Nova leaves: tm for the core, a proof
   for the surface. *)
and 'a poly =
  | PX (* 𝕏 *)
  | PK of 'a (* K a *)
  | PProd of 'a poly * 'a poly (* 𝔽 × 𝔾 *)
  | PSum of 'a poly * 'a poly (* 𝔽 ⊎ 𝔾 *)
  | PSigma of 'a * 'a poly (* a × 𝔽, 𝔽 under a *)
  | PPi of 'a * 'a poly (* a → 𝔽, 𝔽 under a *)

(* The theory of signatures, generic in its Nova pieces. A signature is
   a closed ToS context Φ ▷ 𝔄 checked at a LEVEL, its bound; the
   entries are a snoc list and ⬡ᵢ counts from its end. *)
and 'a signature = { level : int; entries : 'a qty list }

and 'a qty =
  | QU (* U *)
  | QEl of 'a qtm (* El 𝕥 *)
  | QExt of 'a * 'a qty (* A ⇛ 𝔄: 𝔄's Nova pieces under A *)
  | QInt of 'a qtm * 'a qty (* El 𝕥 ⇛ 𝔄: binds a ToS variable *)

and 'a qtm =
  | QVar of int (* ⬡ᵢ *)
  | QAppExt of 'a qtm * 'a (* 𝕥 t *)
  | QApp of 'a qtm * 'a qtm (* 𝕥 𝕥′ *)
  | QLam of
      'a qtm (* λ 𝕥: the body's Nova pieces under the bound Nova variable *)
  | QEq of 'a qtm * 'a qtm (* 𝕥 ≡ 𝕥′ *)

(* Generic maps over the Nova pieces, threading the number of Nova
   binders the piece sits under. *)
let rec map_poly (f : int -> 'a -> 'b) (d : int) : 'a poly -> 'b poly = function
  | PX -> PX
  | PK a -> PK (f d a)
  | PProd (p, q) -> PProd (map_poly f d p, map_poly f d q)
  | PSum (p, q) -> PSum (map_poly f d p, map_poly f d q)
  | PSigma (a, p) -> PSigma (f d a, map_poly f (d + 1) p)
  | PPi (a, p) -> PPi (f d a, map_poly f (d + 1) p)

let rec map_qtm (f : int -> 'a -> 'b) (d : int) : 'a qtm -> 'b qtm = function
  | QVar i -> QVar i
  | QAppExt (t, a) -> QAppExt (map_qtm f d t, f d a)
  | QApp (t, u) -> QApp (map_qtm f d t, map_qtm f d u)
  | QLam t -> QLam (map_qtm f (d + 1) t)
  | QEq (t, u) -> QEq (map_qtm f d t, map_qtm f d u)

let rec map_qty (f : int -> 'a -> 'b) (d : int) : 'a qty -> 'b qty = function
  | QU -> QU
  | QEl t -> QEl (map_qtm f d t)
  | QExt (a, k) -> QExt (f d a, map_qty f (d + 1) k)
  | QInt (t, k) -> QInt (map_qtm f d t, map_qty f d k)

let map_signature (f : int -> 'a -> 'b) (d : int) (s : 'a signature) :
    'b signature =
  { level = s.level; entries = List.map (map_qty f d) s.entries }
