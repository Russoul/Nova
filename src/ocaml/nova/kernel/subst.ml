(* Substitution is a FUNCTION on core syntax, not a calculus. A
   substitution sends ☐ᵢ to the i-th entry of `under` when there is one
   and to ☐_(i - |under| + shift) otherwise. *)

open Core

type t = { under : tm list; shift : int }

let id = { under = []; shift = 0 }

(* ↑ⁿ *)
let wk n = { under = []; shift = n }

(* (id, ē): the spine ē instantiates the telescope it is against; ē is
   a snoc list, its head goes to ☐₀ *)
let inst es = { under = es; shift = 0 }

(* [id, t] *)
let single t = inst [ t ]

(* The exchange ξ: from Γ ▷ A · Δ′ (n entries of Δ, weakened past A)
   to Γ · Δ ▷ A′. The Δ entries move up by one, A comes to the top. *)
let exchange n =
  { under = List.init n (fun i -> Var (i + 1)) @ [ Var 0 ]; shift = n + 1 }

let var s i =
  match List.nth_opt s.under i with
  | Some t -> t
  | None -> Var (i - List.length s.under + s.shift)

(* Push a substitution under one binder. *)
let rec lift s =
  { under = Var 0 :: List.map (apply (wk 1)) s.under; shift = s.shift + 1 }

and lift_n n s = if n = 0 then s else lift_n (n - 1) (lift s)

and apply s t =
  match t with
  | Var i -> var s i
  | Item (x, es) -> Item (x, List.map (apply s) es)
  | Pi (a, b) -> Pi (apply s a, apply (lift s) b)
  | Lam b -> Lam (apply (lift s) b)
  | App (f, a) -> App (apply s f, apply s a)
  | Sigma (a, b) -> Sigma (apply s a, apply (lift s) b)
  | Pair (a, b) -> Pair (apply s a, apply s b)
  | Fst p -> Fst (apply s p)
  | Snd p -> Snd (apply s p)
  | Sum (a, b) -> Sum (apply s a, apply s b)
  | Inl a -> Inl (apply s a)
  | Inr b -> Inr (apply s b)
  | SumElim (l, r, t) -> SumElim (apply (lift s) l, apply (lift s) r, apply s t)
  | Quot (a, r) -> Quot (apply s a, apply (lift_n 2 s) r)
  | Class a -> Class (apply s a)
  | QuotElim (f, q) -> QuotElim (apply (lift s) f, apply s q)
  | Zero -> Zero
  | ZeroElim t -> ZeroElim (apply s t)
  | One -> One
  | Unit -> Unit
  | Nat -> Nat
  | Z -> Z
  | S n -> S (apply s n)
  | NatElim (z, st, t) -> NatElim (apply s z, apply (lift_n 2 s) st, apply s t)
  | Eq (a, b, ty) -> Eq (apply s a, apply s b, apply s ty)
  | Star -> Star
  | Squash a -> Squash (apply s a)
  | Sort u -> Sort u
  | Let (a, b) -> Let (apply s a, apply (lift_n 2 s) b)
  | Nu p -> Nu (poly s p)
  | Out t -> Out (apply s t)
  | Corec (p, f, x) -> Corec (poly s p, apply (lift s) f, apply s x)
  | QSort (sg, i, es) -> QSort (signature s sg, i, List.map (apply s) es)
  | QCon (sg, i, es) -> QCon (signature s sg, i, List.map (apply s) es)
  | QElim (sg, i, ms, es, w) ->
      QElim
        ( signature s sg,
          i,
          List.map (apply s) ms,
          List.map (apply s) es,
          apply s w )

(* The embedded Nova pieces of a polynomial or a signature sit under
   the Nova binders the grammar opened above them. *)
and at_depth s d t = apply (lift_n d s) t
and poly s p = map_poly (at_depth s) 0 p
and signature s sg = map_signature (at_depth s) 0 sg

let weaken n t = if n = 0 then t else apply (wk n) t
