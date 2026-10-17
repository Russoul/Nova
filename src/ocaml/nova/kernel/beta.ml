(* β, and nothing else: the computation rules the checker runs under a
   FUEL budget (docs/NovaKernel.nspec, CONVENTIONS). β proper, the
   ι-rules of ⊎, /, ℕ, let-β, record-β, ν-β and QIIT-β; never δ — an item
   reference is stuck. Exhaustion is rejection, so every comparison
   terminates. *)

open Core

type fuel = { mutable left : int }

let fuel n = { left = n }

let step f =
  if f.left <= 0 then reject "fuel exhausted" else f.left <- f.left - 1

(* Weak-head β-normal form. *)
let rec whnf f t =
  match t with
  | App (g, a) -> (
      match whnf f g with
      | Lam b ->
          step f;
          whnf f (Subst.apply (Subst.single a) b)
      | g' -> App (g', a))
  | Fst p -> (
      match whnf f p with
      | Pair (a, _) ->
          step f;
          whnf f a
      | p' -> Fst p')
  | Snd p -> (
      match whnf f p with
      | Pair (_, b) ->
          step f;
          whnf f b
      | p' -> Snd p')
  | Field (r, l) -> (
      (* el-rec-beta: ⟨l̄ ↪ ē⟩.l ⇝ the component at l, by lookup in the
         literal; no type is consulted. A label the literal lacks is
         stuck. *)
      match whnf f r with
      | Record (ls, es) as r' -> (
          match component ls es l with
          | Some e ->
              step f;
              whnf f e
          | None -> Field (r', l))
      | r' -> Field (r', l))
  | SumElim (l, r, t) -> (
      match whnf f t with
      | Inl a ->
          step f;
          whnf f (Subst.apply (Subst.single a) l)
      | Inr b ->
          step f;
          whnf f (Subst.apply (Subst.single b) r)
      | t' -> SumElim (l, r, t'))
  | QuotElim (g, q) -> (
      match whnf f q with
      | Class a ->
          step f;
          whnf f (Subst.apply (Subst.single a) g)
      | q' -> QuotElim (g, q'))
  | NatElim (z, s, t) -> (
      match whnf f t with
      | Z ->
          step f;
          whnf f z
      | S n ->
          step f;
          (* s under ℕ, A: ☐₁ = n, ☐₀ = the recursive result *)
          whnf f (Subst.apply (Subst.inst [ NatElim (z, s, n); n ]) s)
      | t' -> NatElim (z, s, t'))
  | Let (a, b) ->
      step f;
      (* b under A, (☐₀ ≡ a ∈ A): ☐₁ = a, ☐₀ = ⋆ *)
      whnf f (Subst.apply (Subst.inst [ Star; a ]) b)
  | Out t -> (
      match whnf f t with
      | Corec (p, g, x) ->
          step f;
          (* out (corec 𝔽 f x) ⇝ map_𝔽 hᵉˡ (f[id, x]), hᵉˡ the corecursor as
             a function *)
          let h =
            Lam
              (Corec
                 ( Subst.poly (Subst.wk 1) p,
                   Subst.apply (Subst.lift (Subst.wk 1)) g,
                   Var 0 ))
          in
          whnf f (Poly.map p h (Subst.apply (Subst.single x) g))
      | t' -> Out t')
  | QElim (sg, i, ms, es, w) -> (
      match whnf f w with
      | QCon (sg', c, theta)
        when conv_signature f sg sg' && Qiit.sort_of_point sg c = i ->
          step f;
          (* 𝒮.𝕤-elim m̄ ī (𝒮.𝕔 θ) ⇝ m_𝕔 θᴰ *)
          let m =
            match List.nth_opt ms (Tos.point_position sg c) with
            | Some m -> m
            | None -> reject "QIIT-β: no method for the constructor"
          in
          let theta_d = Qiit.disp_spine sg c theta ms in
          whnf f (List.fold_left (fun g a -> App (g, a)) m theta_d)
      | w' -> QElim (sg, i, ms, es, w'))
  | _ -> t

(* (l̄ ↪ ē)(l): the component at a label, the two lists read in
   parallel *)
and component ls es l =
  match (ls, es) with
  | l' :: ls', e :: es' -> if l' = l then Some e else component ls' es' l
  | _ -> None

(* Full β-conversion: whnf both sides, then compare the heads and
   recurse into the parts. No η anywhere — the η's are proof leaves. *)
and conv f t u =
  match (whnf f t, whnf f u) with
  | Var i, Var j -> i = j
  | Item (x, es), Item (y, es') -> x = y && convs f es es'
  | Pi (a, b), Pi (a', b')
  | Sigma (a, b), Sigma (a', b')
  | Sum (a, b), Sum (a', b') ->
      conv f a a' && conv f b b'
  | Lam b, Lam b' -> conv f b b'
  | App (g, a), App (g', a') -> conv f g g' && conv f a a'
  | Pair (a, b), Pair (a', b') -> conv f a a' && conv f b b'
  | Fst p, Fst p' | Snd p, Snd p' -> conv f p p'
  (* records: ONE label list, compared as syntax *)
  | Rec (ls, d), Rec (ls', d') -> ls = ls' && convs f d d'
  | Record (ls, es), Record (ls', es') -> ls = ls' && convs f es es'
  | Field (r, l), Field (r', l') -> l = l' && conv f r r'
  | Inl a, Inl a' | Inr a, Inr a' -> conv f a a'
  | SumElim (l, r, t), SumElim (l', r', t') ->
      conv f l l' && conv f r r' && conv f t t'
  | Quot (a, r), Quot (a', r') -> conv f a a' && conv f r r'
  | Class a, Class a' -> conv f a a'
  | QuotElim (g, q), QuotElim (g', q') -> conv f g g' && conv f q q'
  | Zero, Zero | One, One | Unit, Unit | Nat, Nat | Z, Z | Star, Star -> true
  | ZeroElim t, ZeroElim t' -> conv f t t'
  | S n, S n' -> conv f n n'
  | NatElim (z, s, t), NatElim (z', s', t') ->
      conv f z z' && conv f s s' && conv f t t'
  | Eq (a, b, ty), Eq (a', b', ty') ->
      conv f a a' && conv f b b' && conv f ty ty'
  | Squash a, Squash a' -> conv f a a'
  | Sort s, Sort s' -> s = s'
  | Let (a, b), Let (a', b') -> conv f a a' && conv f b b'
  | Nu p, Nu p' -> conv_poly f p p'
  | Out t, Out t' -> conv f t t'
  | Corec (p, g, x), Corec (p', g', x') ->
      conv_poly f p p' && conv f g g' && conv f x x'
  | QSort (sg, i, es), QSort (sg', i', es')
  | QCon (sg, i, es), QCon (sg', i', es') ->
      i = i' && conv_signature f sg sg' && convs f es es'
  | QElim (sg, i, ms, es, w), QElim (sg', i', ms', es', w') ->
      i = i' && conv_signature f sg sg' && convs f ms ms' && convs f es es'
      && conv f w w'
  | _ -> false

and convs f ts us =
  List.length ts = List.length us && List.for_all2 (conv f) ts us

(* A polynomial or a signature is compared structurally, its embedded
   Nova pieces modulo β. *)
and conv_poly f p q =
  match (p, q) with
  | PX, PX -> true
  | PK a, PK a' -> conv f a a'
  | PProd (p, q), PProd (p', q') | PSum (p, q), PSum (p', q') ->
      conv_poly f p p' && conv_poly f q q'
  | PSigma (a, p), PSigma (a', p') | PPi (a, p), PPi (a', p') ->
      conv f a a' && conv_poly f p p'
  | _ -> false

and conv_signature f sg sg' =
  sg.level = sg'.level
  && List.length sg.entries = List.length sg'.entries
  && List.for_all2 (conv_qty f) sg.entries sg'.entries

and conv_qty f k k' =
  match (k, k') with
  | QU, QU -> true
  | QEl t, QEl t' -> conv_qtm f t t'
  | QExt (a, k), QExt (a', k') -> conv f a a' && conv_qty f k k'
  | QInt (t, k), QInt (t', k') -> conv_qtm f t t' && conv_qty f k k'
  | _ -> false

and conv_qtm f t t' =
  match (t, t') with
  | QVar i, QVar j -> i = j
  | QAppExt (t, a), QAppExt (t', a') -> conv_qtm f t t' && conv f a a'
  | QApp (t, u), QApp (t', u') -> conv_qtm f t t' && conv_qtm f u u'
  | QLam t, QLam t' -> conv_qtm f t t'
  | QEq (t, u), QEq (t', u') -> conv_qtm f t t' && conv_qtm f u u'
  | _ -> false
