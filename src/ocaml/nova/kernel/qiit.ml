(* The readings of a signature (docs/NovaKernel.txt, the QIIT section):
   a signature as a telescope over the algebra context, the arity of
   an entry, the initial algebra ι, the displayed reading over the
   displayed context, and the displayed spine. Each is a function from
   a core signature to core syntax.

   A READING POINT records what is in scope above Γ: the algebra
   entries (n_alg), the displayed entries (n_disp, either 0 or the
   entry's own prefix length k), and the binders opened by the walk,
   innermost first. The foundation's exchange ξ is thereby an index
   computation: a Nova piece is over Γ and the external binders, a ToS
   variable over the entry's prefix and the internal binders, and each
   is sent to its position at the point. *)

open Core

type tag =
  | Ext (* an external binder: a Nova variable *)
  | IntV (* an internal binder at a sort: the value *)
  | IntD (* its displayed value, opened right after it *)
  | IntE (* an internal binder at an equation code: a proof *)

type point = {
  sg : tm signature;
  n_alg : int;
  k : int;
  n_disp : int;
  binders : tag list;
  phi : (int * tm qty) list;
      (* the ToS context for inference — the entry's prefix, then the
         internal binders — each with the number of external binders
         open when it was bound *)
  n_ext : int;
}

let n_entries (sg : tm signature) = List.length sg.entries

(* the point at the start of entry k's walk *)
let start sg ~n_alg ~k ~n_disp =
  let n = n_entries sg in
  {
    sg;
    n_alg;
    k;
    n_disp;
    binders = [];
    phi =
      List.filteri (fun i _ -> i >= n - k) sg.entries
      |> List.map (fun e -> (0, e));
    n_ext = 0;
  }

let n_binders p = List.length p.binders
let is_internal = function IntV | IntE -> true | Ext | IntD -> false

(* the position of the j-th binder with the property, innermost first *)
let nth_position p pred j =
  let rec go i j = function
    | [] -> reject "reading: a binder index out of range"
    | t :: rest ->
        if pred t then if j = 0 then i else go (i + 1) (j - 1) rest
        else go (i + 1) j rest
  in
  go 0 j p.binders

let n_internal p = List.length (List.filter is_internal p.binders)

(* a Nova piece, over Γ and the external binders, at the point *)
let piece p (t : tm) : tm =
  let exts =
    List.init p.n_ext (fun j -> Var (nth_position p (fun t -> t = Ext) j))
  in
  Subst.apply { Subst.under = exts; shift = n_binders p + p.n_disp + p.n_alg } t

(* the ToS context at the point, each entry over the current Nova scope *)
let phi_now p =
  List.map (fun (d, k) -> Subst.qty (Subst.wk (p.n_ext - d)) k) p.phi

(* the algebra value of ⬡ᵢ *)
let value_index p i =
  let n_int = n_internal p in
  if i < n_int then nth_position p is_internal i
  else n_binders p + p.n_disp + (p.n_alg - p.k) + (i - n_int)

(* the displayed value of ⬡ᵢ *)
let disp_index p i =
  let n_int = n_internal p in
  if i < n_int then nth_position p is_internal i - 1
  else n_binders p + (i - n_int)

let open_ext p = { p with binders = Ext :: p.binders; n_ext = p.n_ext + 1 }

let open_int p (t : tm qtm) =
  let tag = match t with QEq _ -> IntE | _ -> IntV in
  { p with binders = tag :: p.binders; phi = (p.n_ext, QEl t) :: p.phi }

let open_disp p = { p with binders = IntD :: p.binders }

(* ----- the reading ⟦_⟧ ----- *)

let rec read_qtm p (t : tm qtm) : tm =
  match t with
  | QVar i -> Var (value_index p i)
  | QAppExt (t, a) -> App (read_qtm p t, piece p a)
  | QApp (t, u) -> App (read_qtm p t, read_qtm p u)
  | QLam t -> Lam (read_qtm (open_ext p) t)
  | QEq (t, u) ->
      Eq (read_qtm p t, read_qtm p u, read_qtm p (Tos.code_of (phi_now p) t))

let rec read_qty p (k : tm qty) : tm =
  match k with
  | QU -> Sort (U p.sg.level)
  | QEl t -> read_qtm p t
  | QExt (a, k) -> Pi (piece p a, read_qty (open_ext p) k)
  | QInt (t, k) -> Pi (read_qtm p t, read_qty (open_int p t) k)

(* the arity telescope of an entry, ACCUMULATED from its far end (the
   foundation's derived snoc: the head is the last domain, each over
   the ones before it), the point past its binders, and its end *)
let rec arity_tele p acc (k : tm qty) =
  match k with
  | QExt (a, k) -> arity_tele (open_ext p) (piece p a :: acc) k
  | QInt (t, k) -> arity_tele (open_int p t) (read_qtm p t :: acc) k
  | e -> (acc, p, e)

(* ----- the initial algebra ι ----- *)

let rec lams n t = if n = 0 then t else Lam (lams (n - 1) t)

(* Γ ⊦ ι ⇐ ⟦𝒮⟧ over Γ, as the SUBSTITUTION it is used as: a snoc list,
   its head the last entry's. The formers inside take cons spines. *)
let iota (sg : tm signature) : tm list =
  let n = n_entries sg in
  Tos.entries_in_order sg
  |> List.map (fun (k, _, e) ->
      let bs, kind = Tos.arity e in
      let m = List.length bs in
      let sg' = Subst.signature (Subst.wk m) sg in
      let spine = List.init m (fun i -> Var (m - 1 - i)) in
      let i = n - 1 - k in
      lams m
        (match kind with
        | Tos.KSort -> QSort (sg', i, spine)
        | Tos.KPoint _ -> QCon (sg', i, spine)
        | Tos.KEq _ -> Star))
  |> List.rev

(* X over Γ·⟦Φ⟧·(m binders), instantiated at ι and at θ for the first
   |θ| of the binders (θ over Γ, given as a substitution: a snoc list;
   |θ| ≤ m, and the innermost m - |θ| binders stay) *)
let at_iota sg ?(theta = []) ~m x =
  let extra = m - List.length theta in
  Subst.apply (Subst.lift_n extra (Subst.inst (theta @ iota sg))) x

(* the prefix length of entry i (counted like ⬡ᵢ) *)
let prefix_of sg i = n_entries sg - 1 - i

(* the arity telescope of entry i over Γ, at ι: a telescope, from its
   first domain *)
let arity_at_iota sg i : tm list =
  let p = start sg ~n_alg:(n_entries sg) ~k:(prefix_of sg i) ~n_disp:0 in
  let doms, _, _ = arity_tele p [] (Tos.entry sg i) in
  List.rev
    (List.mapi (fun j d -> at_iota sg ~m:(List.length doms - 1 - j) d) doms)

(* the type of a point constructor 𝒮.𝕔 θ: its end at ι and the spine θ *)
let con_type sg c (theta : tm list) : tm =
  let p = start sg ~n_alg:(n_entries sg) ~k:(prefix_of sg c) ~n_disp:0 in
  let doms, p', e = arity_tele p [] (Tos.entry sg c) in
  at_iota sg ~theta:(List.rev theta) ~m:(List.length doms) (read_qty p' e)

(* the path leaf 𝒮.𝕔 θ at an equation entry, θ a spine: the sides and
   their type *)
let path sg c (theta : tm list) : tm * tm * tm =
  let theta = List.rev theta in
  let p = start sg ~n_alg:(n_entries sg) ~k:(prefix_of sg c) ~n_disp:0 in
  let doms, p', e = arity_tele p [] (Tos.entry sg c) in
  let m = List.length doms in
  match e with
  | QEl (QEq (l, r)) ->
      let u = Tos.code_of (phi_now p') l in
      ( at_iota sg ~theta ~m (read_qtm p' l),
        at_iota sg ~theta ~m (read_qtm p' r),
        at_iota sg ~theta ~m (read_qtm p' u) )
  | _ -> reject "the entry is not an equation"

(* ----- the displayed reading _ᴰ ----- *)

let rec disp_qtm p (t : tm qtm) : tm =
  match t with
  | QVar i -> Var (disp_index p i)
  | QAppExt (t, a) -> App (disp_qtm p t, piece p a)
  | QApp (t, u) ->
      if Tos.at_equation (phi_now p) u then App (disp_qtm p t, read_qtm p u)
      else App (App (disp_qtm p t, read_qtm p u), disp_qtm p u)
  | QLam t -> Lam (disp_qtm (open_ext p) t)
  | QEq _ -> reject "an equation code has no displayed term"

(* 𝔄ᴰ x at the point, for the algebra value x (a term at the point) and
   the target sort of the entry when it is a sort *)
let rec disp_qty p (target : sort) (k : tm qty) (x : tm) : tm =
  match k with
  | QU -> Pi (x, Sort target)
  | QEl (QEq (l, r)) ->
      let u = Tos.code_of (phi_now p) l in
      Eq (disp_qtm p l, disp_qtm p r, App (disp_qtm p u, read_qtm p r))
  | QEl t -> App (disp_qtm p t, x)
  | QExt (a, k) ->
      Pi
        ( piece p a,
          disp_qty (open_ext p) target k (App (Subst.weaken 1 x, Var 0)) )
  | QInt ((QEq _ as t), k) ->
      Pi
        ( read_qtm p t,
          disp_qty (open_int p t) target k (App (Subst.weaken 1 x, Var 0)) )
  | QInt (t, k) ->
      let dom = read_qtm p t in
      let p1 = open_int p t in
      let dom_d = App (disp_qtm p1 (Tos.shift_qtm 0 1 t), Var 0) in
      let p2 = open_disp p1 in
      Pi (dom, Pi (dom_d, disp_qty p2 target k (App (Subst.weaken 2 x, Var 1))))

(* the target sort of each entry: the sorts in signature order of the
   sort entries, from the first *)
let targets sg (sorts : sort list) : sort list =
  let rec go sorts = function
    | [] -> []
    | (_, _, e) :: rest -> (
        match snd (Tos.arity e) with
        | Tos.KSort -> (
            match sorts with
            | s :: sorts' -> s :: go sorts' rest
            | [] ->
                reject "the eliminator names fewer sorts than the signature has"
            )
        | _ -> Omega :: go sorts rest)
  in
  let ts = go sorts (Tos.entries_in_order sg) in
  if
    List.length sorts
    > List.length
        (List.filter
           (fun (_, _, e) -> snd (Tos.arity e) = Tos.KSort)
           (Tos.entries_in_order sg))
  then reject "the eliminator names more sorts than the signature has";
  ts

(* ⟦𝒮⟧ᴰ[ι]: the displayed telescope over Γ, from its first entry *)
let disp_tele_at_iota sg (sorts : sort list) : tm list =
  let n = n_entries sg in
  let ts = targets sg sorts in
  Tos.entries_in_order sg
  |> List.map2
       (fun target (k, _, e) ->
         let p = start sg ~n_alg:n ~k ~n_disp:k in
         let d = disp_qty p target e (Var (n - 1)) in
         Subst.apply (Subst.lift_n k (Subst.inst (iota sg))) d)
       ts

(* the arguments of a sort code 𝕤 ī: the head's index and the indices,
   in order *)
let rec args_of = function
  | QVar i -> (i, [])
  | QAppExt (t, a) ->
      let i, xs = args_of t in
      (i, xs @ [ `Ext a ])
  | QApp (t, u) ->
      let i, xs = args_of t in
      (i, xs @ [ `Tos u ])
  | QLam _ | QEq _ -> reject "a sort code has a variable at its head"

(* the entry (from the end) a ToS variable at the point names, when it
   is an entry of the signature rather than a binder *)
let entry_of p i =
  let e = i - n_internal p in
  if e < 0 then reject "an index sort must be an entry of the signature";
  n_entries p.sg - 1 - (p.k - 1 - e)

(* θᴰ: the displayed spine of the spine θ (over Γ) at entry i, with the
   eliminator's methods ms supplying the images. Built from its far
   end (acc) and returned from its first entry; prefix is the part of θ
   already passed, as a substitution (snoc). *)
let disp_spine sg i (theta : tm list) (ms : tm list) : tm list =
  let p0 = start sg ~n_alg:(n_entries sg) ~k:(prefix_of sg i) ~n_disp:0 in
  let bs, _ = Tos.arity (Tos.entry sg i) in
  let values = theta in
  if List.length bs <> List.length values then
    reject "displayed spine: arity mismatch";
  let rec go p acc prefix bs values =
    match (bs, values) with
    | [], [] -> List.rev acc
    | Tos.BExt _ :: bs, x :: values ->
        go (open_ext p) (x :: acc) (x :: prefix) bs values
    | Tos.BInt t :: bs, x :: values -> (
        match t with
        | QEq _ -> go (open_int p t) (x :: acc) (x :: prefix) bs values
        | _ ->
            let hd, args = args_of t in
            let s = entry_of p hd in
            let m = List.length prefix in
            let indices =
              List.map
                (fun a ->
                  let r =
                    match a with `Ext a -> piece p a | `Tos u -> read_qtm p u
                  in
                  at_iota sg ~theta:prefix ~m r)
                args
            in
            let image = QElim (sg, s, ms, indices, x) in
            go (open_int p t) (image :: x :: acc) (x :: prefix) bs values)
    | _ -> reject "displayed spine: arity mismatch"
  in
  go p0 [] [] bs values

(* the eliminator's type: d̄(𝕤) ēᴰ w *)
let elim_type sg s (d : tm list) (e : tm list) (w : tm) (ms : tm list) : tm =
  let motive =
    (* d is a spine in signature order; s counts from the end, like ⬡ *)
    match List.nth_opt d (n_entries sg - 1 - s) with
    | Some m -> m
    | None -> reject "the eliminator's spine is short"
  in
  let ed = disp_spine sg s e ms in
  App (List.fold_left (fun f a -> App (f, a)) motive ed, w)

(* the point entries of a spine over ⟦𝒮⟧ᴰ: the methods, in signature
   order *)
let methods sg (d : tm list) : tm list =
  let n = n_entries sg in
  List.filteri (fun i _ -> Tos.is_point sg (n - 1 - i)) d

(* the sort of a point constructor's end: the entry from the end *)
let sort_of_point sg c =
  let p = start sg ~n_alg:(n_entries sg) ~k:(prefix_of sg c) ~n_disp:0 in
  let _, p', e = arity_tele p [] (Tos.entry sg c) in
  match e with
  | QEl t ->
      let hd, _ = args_of t in
      entry_of p' hd
  | _ -> reject "not a point entry"
