(* The polynomial meta-operations of the foundation's coinductive
   section (docs/NovaFoundation.txt): hole filling ⌊𝔽⌋(c), the
   functorial action map_𝔽 and the relator lift_𝔽(R). Each is defined
   by recursion on the polynomial; a bound piece sits under the binder
   its former opens, and the hole's argument weakens past it. *)

open Core

(* ⌊𝔽⌋(c): the code with the hole filled by c *)
let rec fill (f : tm poly) (c : tm) : tm =
  match f with
  | PX -> c
  | PK a -> a
  | PProd (f, g) -> Sigma (fill f c, Subst.weaken 1 (fill g c))
  | PSum (f, g) -> Sum (fill f c, fill g c)
  | PSigma (a, f) -> Sigma (a, fill f (Subst.weaken 1 c))
  | PPi (a, f) -> Pi (a, fill f (Subst.weaken 1 c))

(* map_𝔽 g x for Γ ⊦ g : c₀ → c₁ and x : ⌊𝔽⌋(c₀): a term of ⌊𝔽⌋(c₁) *)
let rec map (f : tm poly) (g : tm) (x : tm) : tm =
  match f with
  | PX -> App (g, x)
  | PK _ -> x
  | PProd (f, f') -> Pair (map f g (Fst x), map f' g (Snd x))
  | PSum (f, f') ->
      let under = Subst.weaken 1 in
      SumElim (Inl (map f (under g) (Var 0)), Inr (map f' (under g) (Var 0)), x)
  | PSigma (_, f) ->
      Pair (Fst x, map (Subst.poly (Subst.single (Fst x)) f) g (Snd x))
  | PPi (_, f) -> Lam (map f (Subst.weaken 1 g) (App (Subst.weaken 1 x, Var 0)))

(* lift_𝔽(R) u v: the relation lifting, for R over Γ ▷ ν 𝔽 ▷ (ν 𝔽)[↑]
   and u, v : ⌊𝔽⌋(ν 𝔽). R keeps its two binders on top; crossing a
   binder weakens its base. *)
let rec relator (f : tm poly) (r : tm) (u : tm) (v : tm) : tm =
  let base_under n = Subst.apply (Subst.lift_n 2 (Subst.wk n)) in
  let bot = Squash Zero in
  match f with
  | PX -> Subst.apply (Subst.inst [ v; u ]) r
  | PK a -> Eq (u, v, a)
  | PProd (f, f') ->
      Squash
        (Sigma
           ( relator f r (Fst u) (Fst v),
             Subst.weaken 1 (relator f' r (Snd u) (Snd v)) ))
  | PSum (f, f') ->
      (* ⊎-elim on u, then on v: diagonal branches lift the payloads,
         the others are ⊥ *)
      let v1 = Subst.weaken 1 v in
      let r2 = base_under 2 r in
      SumElim
        ( SumElim (relator f r2 (Var 1) (Var 0), bot, v1),
          SumElim (bot, relator f' r2 (Var 1) (Var 0), v1),
          u )
  | PSigma (a, f) ->
      let f' = Subst.poly (Subst.single (Fst u)) f in
      Squash
        (Sigma
           (Eq (Fst u, Fst v, a), Subst.weaken 1 (relator f' r (Snd u) (Snd v))))
  | PPi (a, f) ->
      Squash
        (Pi
           ( a,
             relator f (base_under 1 r)
               (App (Subst.weaken 1 u, Var 0))
               (App (Subst.weaken 1 v, Var 0)) ))
