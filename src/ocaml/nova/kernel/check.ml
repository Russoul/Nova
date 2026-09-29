(* The checker: a surface proof to a core equation, rule by rule after
   docs/NovaKernel.txt. `infer` is Γ ⊦ [α] t₀ ≐ t₁ ⇒ T, `check` is
   Γ ⊦ [α] t₀ ≐ t₁ ⇐ T. Types are built from the RIGHT side of the
   equations, as the rules write them. A pattern input is matched after
   weak-head β only; a stuck head is a rejection, never an unfolding.

   This iteration covers the structural fragment; the ν and QIIT forms
   reject. *)

open Core
module P = Proof

type st = { sg : Sig.t; fuel : Beta.fuel }

(* Γ: a snoc list of types, the head ☐₀'s, each over the ones below. *)
type ctx = tm list

let whnf st t = Beta.whnf st.fuel t
let conv st t u = t = u || Beta.conv st.fuel t u

let need_conv st what t u =
  if not (conv st t u) then reject "%s do not agree" what

(* Run a sub-check and name its place in a rejection. *)
let within what f = try f () with Reject msg -> reject "%s: %s" what msg

(* Γ∥ᵢ, brought over Γ *)
let lookup (ctx : ctx) i =
  match List.nth_opt ctx i with
  | Some a -> Subst.weaken (i + 1) a
  | None -> reject "☐%d: no such variable" i

let as_sort st what t =
  match whnf st t with
  | Sort u -> u
  | _ -> reject "%s: its type is not a sort" what

let sort_of_pi u u' =
  match u' with Omega -> Omega | U l -> U (max (level u) l)

let join_sorts u u' = U (max (level u) (level u'))

let rec infer st (ctx : ctx) (p : P.t) : tm * tm * tm =
  match p with
  (* ------ Π ------ *)
  | P.App (a, b) ->
      let f0, f1, t = infer st ctx a in
      let dom, cod =
        match whnf st t with
        | Pi (dom, cod) -> (dom, cod)
        | _ -> reject "application: the head's type is not a Π-type"
      in
      let e0, e1 = check st ctx dom b in
      (App (f0, e0), App (f1, e1), Subst.apply (Subst.single e1) cod)
  | P.Pi (a, b) ->
      let a0, a1, u = infer_sort st "Π: the domain" ctx a in
      let b0, b1, u' = infer_sort st "Π: the codomain" (a1 :: ctx) b in
      (Pi (a0, b0), Pi (a1, b1), Sort (sort_of_pi u u'))
  (* ------ Σ ------ *)
  | P.Fst a ->
      let p0, p1, t = infer st ctx a in
      let dom, _ = as_sigma st ".π₁" t in
      (Fst p0, Fst p1, dom)
  | P.Snd a ->
      let p0, p1, t = infer st ctx a in
      let _, cod = as_sigma st ".π₂" t in
      (Snd p0, Snd p1, Subst.apply (Subst.single (Fst p1)) cod)
  | P.Sigma (a, b) ->
      let a0, a1, u = infer_sort st "Σ: the first component" ctx a in
      let b0, b1, u' = infer_sort st "Σ: the second component" (a1 :: ctx) b in
      (Sigma (a0, b0), Sigma (a1, b1), Sort (join_sorts u u'))
  (* ------ ⊎ ------ *)
  | P.Sum (a, b) ->
      let a0, a1, u = infer_sort st "⊎: the left summand" ctx a in
      let b0, b1, u' = infer_sort st "⊎: the right summand" ctx b in
      (Sum (a0, b0), Sum (a1, b1), Sort (join_sorts u u'))
  | P.SumElim (u, c, l, r, tau) ->
      let t0, t1, t = infer st ctx tau in
      let dom_l, dom_r =
        match whnf st t with
        | Sum (a, b) -> (a, b)
        | _ -> reject "⊎-elim: the scrutinee's type is not a ⊎-type"
      in
      let c1 =
        within "⊎-elim: the motive" (fun () ->
            check1 st (Sum (dom_l, dom_r) :: ctx) (Sort u) c)
      in
      let at inj =
        Subst.apply { Subst.under = [ inj (Var 0) ]; shift = 1 } c1
      in
      let l0, l1 = check st (dom_l :: ctx) (at (fun x -> Inl x)) l in
      let r0, r1 = check st (dom_r :: ctx) (at (fun x -> Inr x)) r in
      ( SumElim (l0, r0, t0),
        SumElim (l1, r1, t1),
        Subst.apply (Subst.single t1) c1 )
  (* ------ quotients ------ *)
  | P.Quot (a, rho) ->
      let a0, a1, u = infer_sort st "/: the carrier" ctx a in
      let r0, r1 = check st (Subst.weaken 1 a1 :: a1 :: ctx) (Sort Omega) rho in
      (Quot (a0, r0), Quot (a1, r1), Sort (U (level u)))
  | P.QuotElim (u, b, phi, omega, kappa) ->
      let q0, q1, t = infer st ctx kappa in
      let carrier, rel =
        match whnf st t with
        | Quot (a, r) -> (a, r)
        | _ -> reject "quot-elim: the scrutinee's type is not a quotient"
      in
      let b1 =
        within "quot-elim: the motive" (fun () ->
            check1 st (Quot (carrier, rel) :: ctx) (Sort u) b)
      in
      let f0, f1 =
        check st (carrier :: ctx)
          (Subst.apply { Subst.under = [ Class (Var 0) ]; shift = 1 } b1)
          phi
      in
      (* well-definedness over Γ ▷ A ▷ A[↑] ▷ R *)
      let ctx_wd = rel :: Subst.weaken 1 carrier :: carrier :: ctx in
      let ty_wd =
        Subst.apply { Subst.under = [ Class (Var 2) ]; shift = 3 } b1
      in
      let side i = Subst.apply { Subst.under = [ Var i ]; shift = 3 } f1 in
      let w0, w1 =
        within "quot-elim: the well-definedness proof" (fun () ->
            check st ctx_wd ty_wd omega)
      in
      need_conv st "quot-elim: the well-definedness proof's left side and f" w0
        (side 2);
      need_conv st "quot-elim: the well-definedness proof's right side and f" w1
        (side 1);
      (QuotElim (f0, q0), QuotElim (f1, q1), Subst.apply (Subst.single q1) b1)
  (* ------ 𝟘, 𝟙, ℕ ------ *)
  | P.Zero -> (Zero, Zero, Sort (U 0))
  | P.One -> (One, One, Sort (U 0))
  | P.Nat -> (Nat, Nat, Sort (U 0))
  | P.NatElim (u, a, z, s, tau) ->
      let a1 =
        within "ℕ-elim: the motive" (fun () ->
            check1 st (Nat :: ctx) (Sort u) a)
      in
      let z0, z1 = check st ctx (Subst.apply (Subst.single Z) a1) z in
      let s0, s1 =
        check st (a1 :: Nat :: ctx)
          (Subst.apply { Subst.under = [ S (Var 1) ]; shift = 2 } a1)
          s
      in
      let t0, t1 = check st ctx Nat tau in
      ( NatElim (z0, s0, t0),
        NatElim (z1, s1, t1),
        Subst.apply (Subst.single t1) a1 )
  (* ------ ≡ ------ *)
  | P.Refl a ->
      let t0, t1, t = infer st ctx a in
      (Star, Star, Eq (t0, t1, t))
  | P.Reflect a -> (
      let _, _, t = infer st ctx a in
      match whnf st t with
      | Eq (t0, t1, a) -> (t0, t1, a)
      | _ -> reject "reflect: the proof's type is not an equality")
  | P.Eq (a, b, tau) ->
      let ty0, ty1, _ = infer_sort st "≡: the type" ctx tau in
      let a0, a1 = check st ctx ty1 a in
      let b0, b1 = check st ctx ty1 b in
      (Eq (a0, b0, ty0), Eq (a1, b1, ty1), Sort Omega)
  (* ------ sorts as terms ------ *)
  | P.Sort Omega -> (Sort Omega, Sort Omega, Sort (U 1))
  | P.Sort (U l) -> (Sort (U l), Sort (U l), Sort (U (l + 1)))
  (* ------ ∥·∥ and the propositions ------ *)
  | P.SquashTy a ->
      let a0, a1, _ = infer_sort st "∥·∥: the type" ctx a in
      (Squash a0, Squash a1, Sort Omega)
  | P.Unsquash (g, a, b) ->
      let target =
        within "unsquash: the target" (fun () -> check1 st ctx (Sort Omega) g)
      in
      let _, _, t = infer st ctx b in
      let inner =
        match whnf st t with
        | Squash inner -> inner
        | _ -> reject "unsquash: the proof's type is not a squash"
      in
      ignore (check st (inner :: ctx) (Subst.weaken 1 target) a);
      (Star, Star, target)
  | P.PropIrrel (g, a, b) ->
      let t =
        within "prop-irrel: the witness" (fun () ->
            check1 st ctx (Sort Omega) g)
      in
      let a1 = check1 st ctx t a in
      let b1 = check1 st ctx t b in
      (a1, b1, t)
  | P.Propext (rho, theta, gamma, iota) ->
      let p =
        within "propext: the left proposition" (fun () ->
            check1 st ctx (Sort Omega) rho)
      in
      let q =
        within "propext: the right proposition" (fun () ->
            check1 st ctx (Sort Omega) theta)
      in
      ignore (check st (p :: ctx) (Subst.weaken 1 q) gamma);
      ignore (check st (q :: ctx) (Subst.weaken 1 p) iota);
      (p, q, Sort Omega)
  (* ------ modal ------ *)
  | P.Annot (a, ty) ->
      let ty0, ty1, _ = infer_sort st "the annotation's type" ctx ty in
      need_conv st "the annotation type's sides" ty0 ty1;
      let t0, t1 = check st ctx ty1 a in
      (t0, t1, ty1)
  (* ------ contextual ------ *)
  | P.Var i -> (Var i, Var i, lookup ctx i)
  | P.Item (x, ps) ->
      let it = Sig.find st.sg x in
      let e0, e1 = spine st ctx it.tele ps in
      (Item (x, e0), Item (x, e1), Subst.apply (Subst.inst e1) it.ty)
  | P.Delta (x, ps) ->
      let it = Sig.find st.sg x in
      let body =
        match it.def with
        | Some t -> t
        | None -> reject "x-δ: '%s' is a declaration, it has no definiens" x
      in
      let e = spine1 st ctx it.tele ps in
      let at = Subst.inst e in
      (Item (x, e), Subst.apply at body, Subst.apply at it.ty)
  | P.Let (a, b) ->
      let a0, a1, ty = infer st ctx a in
      let hyp = Eq (Var 0, Subst.weaken 1 a1, Subst.weaken 1 ty) in
      let b0, b1, bty = infer st (hyp :: ty :: ctx) b in
      (Let (a0, b0), Let (a1, b1), Subst.apply (Subst.inst [ Star; a1 ]) bty)
  (* ------ ν, QIITs: the second iteration ------ *)
  | P.Nu _ | P.Out _ | P.Corec _ | P.EtaNu _ ->
      reject "ν: not implemented in this iteration"
  | P.QSort _ | P.QCon _ | P.QElim _ ->
      reject "QIIT: not implemented in this iteration"
  (* ------ forms that only check ------ *)
  | P.Lam _ | P.Pair _ | P.Inl _ | P.Inr _ | P.Class _ | P.QuotEq _
  | P.ZeroElim _ | P.Unit | P.Z | P.S _ | P.Squash _ | P.Irrel _ | P.Switch _
  | P.Lift _ | P.Restrict _ | P.Conv _ | P.Trans _ | P.Sym _ | P.EtaPi _
  | P.EtaSigma _ | P.Coind _ ->
      reject "this proof only checks; annotate it to synthesise"

and check st (ctx : ctx) (ty : tm) (p : P.t) : tm * tm =
  match p with
  (* ------ Π ------ *)
  | P.Lam a ->
      let dom, cod =
        match whnf st ty with
        | Pi (dom, cod) -> (dom, cod)
        | _ -> reject "λ: the type is not a Π-type"
      in
      let f0, f1 = check st (dom :: ctx) cod a in
      (Lam f0, Lam f1)
  (* ------ Σ ------ *)
  | P.Pair (a, b) ->
      let dom, cod = as_sigma st "pair" ty in
      let a0, a1 = check st ctx dom a in
      let b0, b1 = check st ctx (Subst.apply (Subst.single a1) cod) b in
      (Pair (a0, b0), Pair (a1, b1))
  (* ------ ⊎ ------ *)
  | P.Inl a ->
      let dom, _ = as_sum st "inj₁" ty in
      let a0, a1 = check st ctx dom a in
      (Inl a0, Inl a1)
  | P.Inr b ->
      let _, dom = as_sum st "inj₂" ty in
      let b0, b1 = check st ctx dom b in
      (Inr b0, Inr b1)
  (* ------ quotients ------ *)
  | P.Class a ->
      let carrier, _ = as_quot st "class" ty in
      let a0, a1 = check st ctx carrier a in
      (Class a0, Class a1)
  | P.QuotEq (a, b, rho) ->
      let carrier, rel = as_quot st "quot-eq" ty in
      let a1 = check1 st ctx carrier a in
      let b1 = check1 st ctx carrier b in
      ignore (check st ctx (Subst.apply (Subst.inst [ b1; a1 ]) rel) rho);
      (Class a1, Class b1)
  (* ------ 𝟘, 𝟙, ℕ ------ *)
  | P.ZeroElim a ->
      let t0, t1 = check st ctx Zero a in
      (ZeroElim t0, ZeroElim t1)
  | P.Unit -> (
      match whnf st ty with
      | One -> (Unit, Unit)
      | _ -> reject "(): the type is not 𝟙")
  | P.Z -> (
      match whnf st ty with Nat -> (Z, Z) | _ -> reject "Z: the type is not ℕ")
  | P.S a -> (
      match whnf st ty with
      | Nat ->
          let t0, t1 = check st ctx Nat a in
          (S t0, S t1)
      | _ -> reject "S: the type is not ℕ")
  (* ------ ∥·∥ and the propositions ------ *)
  | P.Squash a ->
      let inner =
        match whnf st ty with
        | Squash inner -> inner
        | _ -> reject "squash: the type is not a squash"
      in
      ignore (check st ctx inner a);
      (Star, Star)
  | P.Irrel (a, b) ->
      (match whnf st ty with
      | One | Zero -> ()
      | _ -> reject "irrel: the type is neither 𝟙 nor 𝟘");
      let a1 = check1 st ctx ty a in
      let b1 = check1 st ctx ty b in
      (a1, b1)
  (* ------ modal ------ *)
  | P.Switch a ->
      let t0, t1, t = infer st ctx a in
      need_conv st "switch: the synthesised and the expected type" ty t;
      (t0, t1)
  | P.Lift a ->
      let target = as_sort st "lift: the target" ty in
      let t0, t1, t = infer st ctx a in
      let source = as_sort st "lift: the source" t in
      if not (sort_le source target) then
        reject "lift: the source sort is not below the target";
      (t0, t1)
  | P.Restrict (g0, g1, a) ->
      let target = as_sort st "restrict: the target" ty in
      let t0, t1, t = infer st ctx a in
      let source = as_sort st "restrict: the source" t in
      if not (sort_le target source) then
        reject "restrict: the target sort is not below the source";
      let w0 =
        within "restrict: the left witness" (fun () -> check1 st ctx ty g0)
      in
      let w1 =
        within "restrict: the right witness" (fun () -> check1 st ctx ty g1)
      in
      need_conv st "restrict: the left witness and the left side" t0 w0;
      need_conv st "restrict: the right witness and the right side" t1 w1;
      (t0, t1)
  | P.Conv (a, b) ->
      let from, into, _ = infer_sort st "conv: the type equation" ctx b in
      need_conv st "conv: the target and the expected type" ty into;
      check st ctx from a
  (* ------ contextual ------ *)
  | P.Trans (a, b) ->
      let a0, a1 = check st ctx ty a in
      let b0, b1 = check st ctx ty b in
      need_conv st "the chain's middles" a1 b0;
      (a0, b1)
  | P.Sym a ->
      let a0, a1 = check st ctx ty a in
      (a1, a0)
  (* ------ η ------ *)
  | P.EtaPi phi ->
      ignore (as_pi st "η→" ty);
      let f = check1 st ctx ty phi in
      (f, Lam (App (Subst.weaken 1 f, Var 0)))
  | P.EtaSigma pi ->
      ignore (as_sigma st "η×" ty);
      let p = check1 st ctx ty pi in
      (p, Pair (Fst p, Snd p))
  (* ------ ν: the second iteration ------ *)
  | P.Coind _ -> reject "ν: not implemented in this iteration"
  (* ------ everything else synthesises ------ *)
  | _ ->
      let t0, t1, t = infer st ctx p in
      need_conv st "the synthesised and the expected type" ty t;
      (t0, t1)

(* One-sided forms: the sides must β-join, and the right one stands. *)
and check1 st ctx ty p =
  let t0, t1 = check st ctx ty p in
  need_conv st "the sides of a one-sided proof" t0 t1;
  t1

and infer_sort st what ctx p =
  let t0, t1, t = within what (fun () -> infer st ctx p) in
  (t0, t1, as_sort st what t)

and as_pi st what t =
  match whnf st t with
  | Pi (a, b) -> (a, b)
  | _ -> reject "%s: the type is not a Π-type" what

and as_sigma st what t =
  match whnf st t with
  | Sigma (a, b) -> (a, b)
  | _ -> reject "%s: the type is not a Σ-type" what

and as_sum st what t =
  match whnf st t with
  | Sum (a, b) -> (a, b)
  | _ -> reject "%s: the type is not a ⊎-type" what

and as_quot st what t =
  match whnf st t with
  | Quot (a, r) -> (a, r)
  | _ -> reject "%s: the type is not a quotient" what

(* Γ ⊦ [ᾱ] ē₀ ≐ ē₁ ⇐ Δ: entrywise at the type instantiated by ē₁'s
   prefix. Telescopes and spines are snoc lists; the fold runs from
   the deepest entry. *)
and spine st ctx (tele : tm list) (ps : P.t list) : tm list * tm list =
  if List.length tele <> List.length ps then
    reject "spine: %d arguments against a telescope of %d" (List.length ps)
      (List.length tele);
  List.fold_left2
    (fun (acc0, acc1) entry p ->
      let e0, e1 = check st ctx (Subst.apply (Subst.inst acc1) entry) p in
      (e0 :: acc0, e1 :: acc1))
    ([], []) (List.rev tele) (List.rev ps)

and spine1 st ctx tele ps =
  let e0, e1 = spine st ctx tele ps in
  List.iter2 (need_conv st "the sides of a one-sided spine entry") e0 e1;
  e1

(* ------ the entry points ------ *)

(* Γ ctx: each entry a type at some sort over the ones below. The
   input is a snoc list of proofs. *)
let check_ctx st (ps : P.t list) : ctx =
  List.fold_left
    (fun ctx p ->
      let a0, a1, _ = infer_sort st "a context entry" ctx p in
      need_conv st "the sides of a context entry" a0 a1;
      a1 :: ctx)
    [] (List.rev ps)

(* Σ ⊢ (Δ ⊦ x : T) item, and Σ ⊢ (Δ ⊦ x ≔ t : T) item: the accepted
   item, to be appended to Σ by the caller. *)
let check_item ~fuel (sg : Sig.t) ~(tele : P.t list) ~(ty : P.t)
    ~(def : P.t option) : Sig.item =
  let st = { sg; fuel = Beta.fuel fuel } in
  let ctx = check_ctx st tele in
  let ty0, ty1, _ = infer_sort st "the type" ctx ty in
  need_conv st "the sides of an item's type" ty0 ty1;
  let def =
    Option.map
      (fun p -> within "the definiens" (fun () -> check1 st ctx ty1 p))
      def
  in
  { Sig.tele = ctx; ty = ty1; def }
