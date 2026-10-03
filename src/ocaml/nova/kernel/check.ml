(* The checker: a surface proof to a core equation, rule by rule after
   docs/NovaKernel.txt. `infer` is Γ ⊦ [α] t₀ ≐ t₁ ⇒ T, `check` is
   Γ ⊦ [α] t₀ ≐ t₁ ⇐ T. Types are built from the RIGHT side of the
   equations, as the rules write them. A pattern input is matched after
   weak-head β only; a stuck head is a rejection, never an unfolding.

   ν: the polynomial judgement infers the least level; corec, out, the
   η leaf and coinduction after the document. QIITs: a surface signature
   is checked to a core one (its Nova pieces elaborated, two-sided), the
   readings of Qiit supply the types, and the three forms dispatch on
   the entry's kind. *)

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
  (* ------ records ------ *)
  | P.Rec entries ->
      (* ty-rec in full: ONE label list on both sides, distinct; the
         record is at the level of its telescope *)
      let ls = List.map fst entries in
      distinct "Rec" ls;
      let d0, d1, l = tele_eq st ctx (List.map snd entries) in
      (Rec (ls, d0), Rec (ls, d1), Sort (U l))
  | P.Field (rho, l) ->
      (* el-rec-e: Δ's entry at l over r₁'s projections at the earlier
         labels *)
      let r0, r1, t = infer st ctx rho in
      let ls, d = as_rec st ("." ^ l) t in
      let entry, earlier =
        match field ls d l with
        | Some x -> x
        | None -> reject ".%s: the record type has no such label" l
      in
      let projs = List.map (fun l' -> Field (r1, l')) earlier in
      (Field (r0, l), Field (r1, l), Subst.apply (Subst.inst projs) entry)
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
        | None -> reject "δ: '%s' is a declaration, it has no definiens" x
      in
      let e = spine1 st ctx it.tele ps in
      let at = Subst.inst e in
      (Item (x, e), Subst.apply at body, Subst.apply at it.ty)
  | P.Let (a, b) ->
      let a0, a1, ty = infer st ctx a in
      let hyp = Eq (Var 0, Subst.weaken 1 a1, Subst.weaken 1 ty) in
      let b0, b1, bty = infer st (hyp :: ty :: ctx) b in
      (Let (a0, b0), Let (a1, b1), Subst.apply (Subst.inst [ Star; a1 ]) bty)
  (* ------ ν ------ *)
  | P.Nu phi ->
      let f0, f1, l = poly_eq st ctx phi in
      (Nu f0, Nu f1, Sort (U l))
  | P.Out a -> (
      let t0, t1, t = infer st ctx a in
      match whnf st t with
      | Nu p -> (Out t0, Out t1, Poly.fill p (Nu p))
      | _ -> reject "out: the type is not a ν-type")
  | P.Corec (phi, a, body, chi) ->
      let p, l = poly1 st ctx phi in
      let carrier =
        within "corec: the carrier" (fun () -> check1 st ctx (Sort (U l)) a)
      in
      let f0, f1 =
        within "corec: the coalgebra" (fun () ->
            check st (carrier :: ctx)
              (Subst.weaken 1 (Poly.fill p carrier))
              body)
      in
      let x0, x1 = check st ctx carrier chi in
      (Corec (p, f0, x0), Corec (p, f1, x1), Nu p)
  | P.EtaNu (phi, a, body, h, alpha, chi) ->
      let p, l = poly1 st ctx phi in
      let carrier =
        within "ην: the carrier" (fun () -> check1 st ctx (Sort (U l)) a)
      in
      let ctx' = carrier :: ctx in
      let f =
        within "ην: the coalgebra" (fun () ->
            check1 st ctx' (Subst.weaken 1 (Poly.fill p carrier)) body)
      in
      let hh =
        within "ην: the candidate" (fun () ->
            check1 st ctx' (Subst.weaken 1 (Nu p)) h)
      in
      let o0, o1 =
        within "ην: the commutation" (fun () ->
            check st ctx' (Subst.weaken 1 (Poly.fill p (Nu p))) alpha)
      in
      need_conv st "ην: the commutation's left side and out h" o0 (Out hh);
      need_conv st "ην: the commutation's right side and the coalgebra's image"
        o1
        (Poly.map (Subst.poly (Subst.wk 1) p) (Subst.weaken 1 (Lam hh)) f);
      let x = check1 st ctx carrier chi in
      (Subst.apply (Subst.single x) hh, Corec (p, f, x), Nu p)
  (* ------ QIITs ------ *)
  | P.QSort (sg, s, es) ->
      let sg0, sg1 = sig_eq st ctx sg in
      if not (Tos.is_sort sg1 s) then reject "𝒮.𝕤: the entry is not a sort";
      let e0, e1 = spine st ctx (Qiit.arity_at_iota sg1 s) es in
      (QSort (sg0, s, e0), QSort (sg1, s, e1), Sort (U sg1.level))
  | P.QCon (sg, c, es) -> (
      let sg0, sg1 = sig_eq st ctx sg in
      match snd (Tos.arity (Tos.entry sg1 c)) with
      | Tos.KPoint _ ->
          let e0, e1 = spine st ctx (Qiit.arity_at_iota sg1 c) es in
          ( QCon (sg0, c, e0),
            QCon (sg1, c, e1),
            whnf st (Qiit.con_type sg1 c e1) )
      | Tos.KEq _ ->
          (* the path leaf: the imposed equation *)
          need_conv_signature st sg0 sg1;
          let e = spine1 st ctx (Qiit.arity_at_iota sg1 c) es in
          Qiit.path sg1 c e
      | Tos.KSort -> reject "𝒮.𝕔: the entry is a sort")
  | P.QElim (sg, s, sorts, ds, es, w) ->
      let sg0, sg1 = sig_eq st ctx sg in
      need_conv_signature st sg0 sg1;
      if not (Tos.is_sort sg1 s) then reject "𝒮.𝕤-elim: the entry is not a sort";
      let d0, d1 =
        within "𝒮.𝕤-elim: the displayed spine" (fun () ->
            spine st ctx (Qiit.disp_tele_at_iota sg1 sorts) ds)
      in
      List.iteri
        (fun i (a, b) ->
          if Tos.is_sort sg1 i then
            need_conv st "𝒮.𝕤-elim: a motive's sides" a b)
        (List.combine d0 d1);
      let e0, e1 = spine st ctx (Qiit.arity_at_iota sg1 s) es in
      let w0, w1 = check st ctx (QSort (sg1, s, e1)) w in
      let ms0 = Qiit.methods sg1 d0 and ms1 = Qiit.methods sg1 d1 in
      ( QElim (sg1, s, ms0, e0, w0),
        QElim (sg1, s, ms1, e1, w1),
        Qiit.elim_type sg1 s d1 e1 w1 ms1 )
  (* ------ forms that only check ------ *)
  | P.Lam _ | P.Pair _ | P.Inl _ | P.Inr _ | P.Class _ | P.QuotEq _
  | P.ZeroElim _ | P.Unit | P.Z | P.S _ | P.Squash _ | P.Irrel _ | P.Lift _
  | P.Restrict _ | P.Conv _ | P.Trans _ | P.Sym _ | P.EtaPi _ | P.EtaSigma _
  | P.Record _ | P.EtaRec _ | P.Coind _ ->
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
  (* ------ records ------ *)
  | P.Record fields ->
      (* el-rec-i: the labels are the TYPE's, in its order; the body is
         a spine of its telescope *)
      let ls, d = as_rec st "record" ty in
      let given = List.map fst fields in
      if given <> ls then
        reject "record: the labels are%s, the type's are%s" (labels given)
          (labels ls);
      let e0, e1 = spine st ctx d (List.map snd fields) in
      (Record (ls, e0), Record (ls, e1))
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
  | P.EtaRec rho ->
      (* el-rec-eta: the element is the record of its projections *)
      let ls, _ = as_rec st "ηRec" ty in
      let r = check1 st ctx ty rho in
      (r, Record (ls, List.map (fun l -> Field (r, l)) ls))
  (* ------ ν: coinduction ------ *)
  | P.Coind (a, b, r, p, q) ->
      let poly =
        match whnf st ty with
        | Nu p -> p
        | _ -> reject "coind: the type is not a ν-type"
      in
      let nu = Nu poly in
      let t0 = check1 st ctx nu a in
      let t1 = check1 st ctx nu b in
      let ctx_r = Subst.weaken 1 nu :: nu :: ctx in
      let rel =
        within "coind: the relation" (fun () -> check1 st ctx_r (Sort Omega) r)
      in
      ignore
        (within "coind: the endpoints" (fun () ->
             check st ctx (Subst.apply (Subst.inst [ t1; t0 ]) rel) p));
      let ctx_q = rel :: ctx_r in
      let rel' = Subst.apply (Subst.lift_n 2 (Subst.wk 3)) rel in
      let goal =
        Poly.relator
          (Subst.poly (Subst.wk 3) poly)
          rel' (Out (Var 2)) (Out (Var 1))
      in
      ignore (within "coind: the closure" (fun () -> check st ctx_q goal q));
      (t0, t1)
  (* ------ THE SILENT SWITCH: everything else synthesises ------ *)
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

and as_rec st what t =
  match whnf st t with
  | Rec (ls, d) -> (ls, d)
  | _ -> reject "%s: the type is not a record type" what

(* The entry of Δ at a label, with the labels before it (a snoc list,
   the nearest first): what instantiates the entry. *)
and field ls d l =
  match (ls, d) with
  | l' :: ls', a :: d' -> if l' = l then Some (a, ls') else field ls' d' l
  | _ -> None

and labels ls =
  if ls = [] then " none" else " " ^ String.concat " " (List.rev ls)

and distinct what ls =
  match ls with
  | [] -> ()
  | l :: rest ->
      if List.mem l rest then reject "%s: the label %s is repeated" what l;
      distinct what rest

(* Γ ⊦ [ᾱ] Δ₀ ≐ Δ₁ tel ℓ: entry by entry from the deepest, each a type
   equation over the RIGHT-hand entries before it; the least level is
   the join of the sorts the entries infer, 0 at the empty telescope. *)
and tele_eq st ctx (ps : P.t list) : tm list * tm list * int =
  List.fold_left
    (fun (acc0, acc1, l) p ->
      let a0, a1, u = infer_sort st "a telescope entry" (acc1 @ ctx) p in
      (a0 :: acc0, a1 :: acc1, max l (level u)))
    ([], [], 0) (List.rev ps)

and as_sum st what t =
  match whnf st t with
  | Sum (a, b) -> (a, b)
  | _ -> reject "%s: the type is not a ⊎-type" what

and as_quot st what t =
  match whnf st t with
  | Quot (a, r) -> (a, r)
  | _ -> reject "%s: the type is not a quotient" what

(* Γ ⊦ [φ] 𝔽₀ ≐ 𝔽₁ poly ℓ: the least level is the join of the sorts the
   embedded codes infer. *)
and poly_eq st ctx (phi : P.t poly) : tm poly * tm poly * int =
  match phi with
  | PX -> (PX, PX, 0)
  | PK a ->
      let a0, a1, u = infer_sort st "K: the code" ctx a in
      (PK a0, PK a1, level u)
  | PProd (f, g) ->
      let f0, f1, l = poly_eq st ctx f in
      let g0, g1, l' = poly_eq st ctx g in
      (PProd (f0, g0), PProd (f1, g1), max l l')
  | PSum (f, g) ->
      let f0, f1, l = poly_eq st ctx f in
      let g0, g1, l' = poly_eq st ctx g in
      (PSum (f0, g0), PSum (f1, g1), max l l')
  | PSigma (a, f) ->
      let a0, a1, u = infer_sort st "×: the code" ctx a in
      let f0, f1, l = poly_eq st (a1 :: ctx) f in
      (PSigma (a0, f0), PSigma (a1, f1), max (level u) l)
  | PPi (a, f) ->
      let a0, a1, u = infer_sort st "→: the code" ctx a in
      let f0, f1, l = poly_eq st (a1 :: ctx) f in
      (PPi (a0, f0), PPi (a1, f1), max (level u) l)

and poly1 st ctx phi =
  let f0, f1, l = poly_eq st ctx phi in
  if not (Beta.conv_poly st.fuel f0 f1) then
    reject "the sides of a one-sided polynomial do not agree";
  (f1, l)

(* ----- signatures: Γ ⊦ [ϑ] 𝒮₀ ≐ 𝒮₁ qsig ℓ ----- *)

and need_conv_signature st a b =
  if not (Beta.conv_signature st.fuel a b) then
    reject "the two signatures do not agree"

(* phi: the ToS context so far, its entries over ctx (side 1) *)
and sig_eq st ctx (sg : P.t signature) : tm signature * tm signature =
  let l = sg.level in
  let e0, e1, _ =
    List.fold_left
      (fun (acc0, acc1, phi) e ->
        let k0, k1 =
          within "a signature entry" (fun () -> qty_eq st ctx l phi e)
        in
        (k0 :: acc0, k1 :: acc1, k1 :: phi))
      ([], [], []) (List.rev sg.entries)
  in
  ({ level = l; entries = e0 }, { level = l; entries = e1 })

and qty_eq st ctx l (phi : tm qty list) (k : P.t qty) : tm qty * tm qty =
  match k with
  | QU -> (QU, QU)
  | QEl t ->
      let t0, t1 = qtm_check st ctx l phi QU t in
      (QEl t0, QEl t1)
  | QExt (a, k) ->
      let a0, a1 =
        within "an external domain" (fun () -> check st ctx (Sort (U l)) a)
      in
      let phi' = List.map (Subst.qty (Subst.wk 1)) phi in
      let k0, k1 = qty_eq st (a1 :: ctx) l phi' k in
      (QExt (a0, k0), QExt (a1, k1))
  | QInt (t, k) ->
      let t0, t1 = qtm_check st ctx l phi QU t in
      let k0, k1 = qty_eq st ctx l (QEl t1 :: phi) k in
      (QInt (t0, k0), QInt (t1, k1))

and qtm_infer st ctx l phi (t : P.t qtm) : tm qtm * tm qtm * tm qty =
  match t with
  | QVar i -> (QVar i, QVar i, Tos.lookup phi i)
  | QAppExt (t, a) -> (
      let t0, t1, k = qtm_infer st ctx l phi t in
      match k with
      | QExt (dom, k') ->
          let a0, a1 = check st ctx dom a in
          (QAppExt (t0, a0), QAppExt (t1, a1), Subst.qty (Subst.single a1) k')
      | _ -> reject "ToS application: the head's type is not an external Π")
  | QApp (t, u) -> (
      let t0, t1, k = qtm_infer st ctx l phi t in
      match k with
      | QInt (c, k') ->
          let u0, u1 = qtm_check st ctx l phi (QEl c) u in
          (QApp (t0, u0), QApp (t1, u1), Tos.subst_qty 0 0 u1 k')
      | _ -> reject "ToS application: the head's type is not an internal Π")
  | QLam _ -> reject "a ToS λ only checks"
  | QEq _ -> reject "an equation code only checks, at U"

and qtm_check st ctx l phi (k : tm qty) (t : P.t qtm) : tm qtm * tm qtm =
  match (t, k) with
  | QLam body, QExt (dom, k') ->
      let phi' = List.map (Subst.qty (Subst.wk 1)) phi in
      let b0, b1 = qtm_check st (dom :: ctx) l phi' k' body in
      (QLam b0, QLam b1)
  | QLam _, _ -> reject "a ToS λ against a type that is not an external Π"
  | QEq (a, b), QU -> (
      let a0, a1, ka = qtm_infer st ctx l phi a in
      match ka with
      | QEl u ->
          let b0, b1 = qtm_check st ctx l phi (QEl u) b in
          (QEq (a0, b0), QEq (a1, b1))
      | _ -> reject "an equation code's sides must be elements")
  | QEq _, _ -> reject "an equation code against a type that is not U"
  | _ ->
      let t0, t1, k' = qtm_infer st ctx l phi t in
      if not (Beta.conv_qty st.fuel k k') then
        reject "a ToS term's synthesised and expected types do not agree";
      (t0, t1)

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
