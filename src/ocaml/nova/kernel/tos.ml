(* The theory of signatures on CORE signatures: ToS index shifts, ToS
   substitution, the kind and arity of an entry, and type inference of
   ToS terms (docs/NovaKernel.txt, the QIIT section). A ToS context is
   a snoc list of entries, each over the ones before it; a Nova piece
   inside an entry is over Γ extended by the external binders opened
   above it. *)

open Core

(* shift the ToS variables at or above the cutoff *)
let rec shift_qtm c n = function
  | QVar i -> QVar (if i >= c then i + n else i)
  | QAppExt (t, a) -> QAppExt (shift_qtm c n t, a)
  | QApp (t, u) -> QApp (shift_qtm c n t, shift_qtm c n u)
  | QLam t -> QLam (shift_qtm c n t)
  | QEq (t, u) -> QEq (shift_qtm c n t, shift_qtm c n u)

let rec shift_qty c n = function
  | QU -> QU
  | QEl t -> QEl (shift_qtm c n t)
  | QExt (a, k) -> QExt (a, shift_qty c n k)
  | QInt (t, k) -> QInt (shift_qtm c n t, shift_qty (c + 1) n k)

(* substitute the ToS variable ⬡c by u (a term over the context outside
   the c binders); crossing an external binder weakens u's Nova pieces *)
let rec subst_qtm c d u = function
  | QVar i ->
      if i = c then shift_qtm 0 c (Subst.qtm (Subst.wk d) u)
      else if i > c then QVar (i - 1)
      else QVar i
  | QAppExt (t, a) -> QAppExt (subst_qtm c d u t, a)
  | QApp (t, t') -> QApp (subst_qtm c d u t, subst_qtm c d u t')
  | QLam t -> QLam (subst_qtm c (d + 1) u t)
  | QEq (t, t') -> QEq (subst_qtm c d u t, subst_qtm c d u t')

let rec subst_qty c d u = function
  | QU -> QU
  | QEl t -> QEl (subst_qtm c d u t)
  | QExt (a, k) -> QExt (a, subst_qty c (d + 1) u k)
  | QInt (t, k) -> QInt (subst_qtm c d u t, subst_qty (c + 1) d u k)

(* the entry ⬡ᵢ's type, brought to the context of ⬡₀ *)
let lookup (phi : tm qty list) i =
  match List.nth_opt phi i with
  | Some k -> shift_qty 0 (i + 1) k
  | None -> reject "⬡%d: no such ToS variable" i

(* A binder of an arity, and the kind of an entry. *)
type binder = BExt of tm | BInt of tm qtm (* the domain's code *)

type kind =
  | KSort
  | KPoint of tm qtm
  (* the end 𝕤 ī *)
  | KEq of tm qtm * tm qtm

let rec arity (k : tm qty) : binder list * kind =
  match k with
  | QU -> ([], KSort)
  | QEl (QEq (l, r)) -> ([], KEq (l, r))
  | QEl t -> ([], KPoint t)
  | QExt (a, k) ->
      let bs, e = arity k in
      (BExt a :: bs, e)
  | QInt (t, k) ->
      let bs, e = arity k in
      (BInt t :: bs, e)

(* the head variable of a sort code 𝕤 ī, and its argument count *)
let rec head = function
  | QVar i -> (i, 0)
  | QAppExt (t, _) | QApp (t, _) ->
      let i, n = head t in
      (i, n + 1)
  | QLam _ | QEq _ -> reject "a sort code has a variable at its head"

(* Type inference for ToS terms over a ToS context phi whose entries
   are over the current Nova context. Applications substitute; a λ or
   an equation only checks. *)
let rec infer (phi : tm qty list) (t : tm qtm) : tm qty =
  match t with
  | QVar i -> lookup phi i
  | QAppExt (t, a) -> (
      match infer phi t with
      | QExt (_, k) -> Subst.qty (Subst.single a) k
      | _ -> reject "ToS application: the head's type is not an external Π")
  | QApp (t, u) -> (
      match infer phi t with
      | QInt (_, k) -> subst_qty 0 0 u k
      | _ -> reject "ToS application: the head's type is not an internal Π")
  | QEq _ -> QU
  | QLam _ -> reject "a ToS λ only checks"

(* is the ToS term at an equation code? *)
let at_equation phi t =
  match infer phi t with QEl (QEq _) -> true | _ -> false

(* the code an element's type decodes: t ⇒ El 𝕦 *)
let code_of phi t =
  match infer phi t with
  | QEl u -> u
  | _ -> reject "a ToS term at U where an element was expected"

(* The entries of a signature in order from the first, each paired
   with its ToS prefix (its own context). *)
let entries_in_order (sg : tm signature) : (int * tm qty list * tm qty) list =
  let rec go k acc = function
    | [] -> []
    | e :: rest -> (k, acc, e) :: go (k + 1) (e :: acc) rest
  in
  go 0 [] (List.rev sg.entries)

(* entry i counted like ⬡ᵢ, from the end *)
let entry (sg : tm signature) i =
  match List.nth_opt sg.entries i with
  | Some e -> e
  | None -> reject "the signature has no entry ⬡%d" i

let n_entries (sg : tm signature) = List.length sg.entries

(* the position of ⬡ᵢ among the point entries, in order from the
   first: which method serves its constructor *)
let point_position (sg : tm signature) i =
  let from_start = n_entries sg - 1 - i in
  List.fold_left
    (fun n (k, _, e) ->
      if k < from_start then
        match snd (arity e) with KPoint _ -> n + 1 | _ -> n
      else n)
    0 (entries_in_order sg)

let is_point (sg : tm signature) i =
  match snd (arity (entry sg i)) with KPoint _ -> true | _ -> false

let is_sort (sg : tm signature) i =
  match snd (arity (entry sg i)) with KSort -> true | _ -> false
