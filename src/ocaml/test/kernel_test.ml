(* Unit tests for the kernel's syntax-level machinery: substitution and
   the β engine. The checker's tests are golden tests over the proof
   language. *)

open Nova
open Core

let failures = ref 0

let check name cond =
  if not cond then (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let conv t u = Beta.conv (Beta.fuel 1000) t u
let whnf t = Beta.whnf (Beta.fuel 1000) t

let () =
  (* --- substitution --- *)
  (* (λ. ☐₀ ☐₁) [id, a]  =  λ. ☐₀ a[↑] *)
  let a = Item ("a", []) in
  check "single under binder"
    (Subst.apply (Subst.single a) (Lam (App (Var 0, Var 1)))
    = Lam (App (Var 0, a)));
  (* weakening skips the bound variable *)
  check "weaken under binder"
    (Subst.weaken 1 (Lam (App (Var 0, Var 1))) = Lam (App (Var 0, Var 2)));
  (* C[↑, inj₁ ☐₀]: ☐₀ ↦ inj₁ ☐₀, ☐₁ ↦ ☐₁ *)
  let s = { Subst.under = [ Inl (Var 0) ]; shift = 1 } in
  check "shifted instantiation"
    (Subst.apply s (Pair (Var 0, Var 1)) = Pair (Inl (Var 0), Var 1));
  (* the exchange moves A to the top and Δ up by one *)
  let xi = Subst.exchange 2 in
  check "exchange"
    (List.map (Subst.var xi) [ 0; 1; 2; 3 ] = [ Var 1; Var 2; Var 0; Var 3 ]);
  (* pieces of a signature sit under the grammar's Nova binders *)
  let sg = [ QExt (Var 0, QEl (QAppExt (QVar 0, Var 0))) ] in
  check "signature pieces under external binder"
    (Subst.signature (Subst.wk 1) sg
    = [ QExt (Var 1, QEl (QAppExt (QVar 0, Var 0))) ]);

  (* --- β --- *)
  check "β" (whnf (App (Lam (Var 0), Nat)) = Nat);
  check "ι ℕ, S" (conv (NatElim (Z, S (Var 0), S (S Z))) (S (S Z)));
  check "ι ⊎" (conv (SumElim (Var 0, Nat, Inl One)) One);
  check "ι /" (conv (QuotElim (S (Var 0), Class Z)) (S Z));
  check "π₁" (conv (Fst (Pair (Nat, Zero))) Nat);
  check "let-β" (conv (Let (Nat, Pair (Var 1, Var 0))) (Pair (Nat, Star)));
  check "no δ" (conv (Item ("x", [ Z ])) (Item ("x", [ Z ])));
  check "no δ, distinct" (not (conv (Item ("x", [ Z ])) (Item ("x", [ S Z ]))));
  check "no η" (not (conv (Lam (App (Var 1, Var 0))) (Var 0)));
  check "stuck head compared"
    (conv (App (Var 3, Z)) (App (Var 3, NatElim (Z, S (Var 0), Z))));
  (* (λx. x x)(λx. x x) exhausts the budget rather than looping *)
  let omega = Lam (App (Var 0, Var 0)) in
  check "fuel"
    (match Beta.whnf (Beta.fuel 50) (App (omega, omega)) with
    | exception Reject "fuel exhausted" -> true
    | _ -> false);

  (* --- the checker --- *)
  let module P = Proof in
  let sg = ref Sig.empty in
  let item name ?(tele = []) ty def =
    match Check.check_item ~fuel:1000 !sg ~tele ~ty ~def with
    | it ->
        sg := Sig.add !sg name it;
        it
    | exception Reject msg -> failwith (Printf.sprintf "item %s: %s" name msg)
  in
  let rejects name f =
    check name
      (match f () with exception (Reject _ | Failure _) -> true | _ -> false)
  in
  (* id : ℕ → ℕ ≔ λx. x *)
  let id_nat = item "id" (P.Pi (P.Nat, P.Nat)) (Some (P.Lam (P.Var 0))) in
  check "id : ℕ → ℕ"
    (id_nat.ty = Pi (Nat, Nat) && id_nat.def = Some (Lam (Var 0)));
  (* plus : ℕ → ℕ → ℕ ≔ λn m. ℕ-elim 𝕌₀ (_. ℕ) n (k ih. S ih) m — ℕ-elim
     synthesises, so the body switches *)
  let plus_body =
    P.Lam (P.Lam (P.NatElim (U 0, P.Nat, P.Var 1, P.S (P.Var 0), P.Var 0)))
  in
  let plus = item "plus" (P.Pi (P.Nat, P.Pi (P.Nat, P.Nat))) (Some plus_body) in
  check "plus accepted" (Option.is_some plus.def);
  (* two : ℕ ≔ plus (S Z) (S Z), and 2 ≡ S (S Z) by unfolding: the δ
     leaf then β *)
  let two =
    item "two" P.Nat
      (Some (P.App (P.App (P.Item ("plus", []), P.S P.Z), P.S P.Z)))
  in
  check "two's definiens is the application"
    (two.def = Some (App (App (Item ("plus", []), S Z), S Z)));
  let lemma =
    item "two-is-SSZ"
      (P.Eq (P.Item ("two", []), P.S (P.S P.Z), P.Nat))
      (Some
         (P.Refl
            (P.Annot
               ( P.Trans
                   ( P.Delta ("two", []),
                     P.App (P.App (P.Delta ("plus", []), P.S P.Z), P.S P.Z) ),
                 P.Nat ))))
  in
  check "two ≡ S (S Z) by δ then β" (lemma.def = Some Star);
  (* the same without the δ leaves: two is stuck against S (S Z) *)
  rejects "no δ without the leaf" (fun () ->
      item "bad"
        (P.Eq (P.Item ("two", []), P.S (P.S P.Z), P.Nat))
        (Some (P.Refl (P.Annot (P.Item ("two", []), P.Nat)))));
  (* a hypothesis reflected: (h : n ≡ Z ∈ ℕ) ⊦ S n ≡ S Z, via congruence *)
  let cong =
    item "S-cong"
      ~tele:[ P.Eq (P.Var 0, P.Z, P.Nat); P.Nat ]
      (P.Eq (P.S (P.Var 1), P.S P.Z, P.Nat))
      (Some (P.Refl (P.Annot (P.S (P.Reflect (P.Var 0)), P.Nat))))
  in
  check "reflect + congruence"
    (cong.def = Some Star && List.length cong.tele = 2);
  (* the impredicative arrow: ℕ → (Z ≡ Z ∈ ℕ) is a proposition *)
  let prop =
    item "p" (P.Sort Omega) (Some (P.Pi (P.Nat, P.Eq (P.Z, P.Z, P.Nat))))
  in
  check "→ into Ω is at Ω" (prop.def = Some (Pi (Nat, Eq (Z, Z, Nat))));
  (* ℕ → 𝕌₀ lives at 𝕌₁, and lift takes it to 𝕌₂ but not down *)
  let fam = item "fam" (P.Sort (U 1)) (Some (P.Pi (P.Nat, P.Sort (U 0)))) in
  check "→ into 𝕌₀ is at 𝕌₁" (fam.ty = Sort (U 1));
  ignore (item "fam-up" (P.Sort (U 2)) (Some (P.Lift (P.Item ("fam", [])))));
  rejects "lift never descends" (fun () ->
      item "fam-down" (P.Sort (U 0)) (Some (P.Lift (P.Item ("fam", [])))));
  (* Ω is not at 𝕌₀ *)
  rejects "Ω ⇏ 𝕌₀" (fun () ->
      item "omega0" (P.Sort (U 0)) (Some (P.Sort Omega)));
  ignore (item "omega1" (P.Sort (U 1)) (Some (P.Sort Omega)));
  (* a mode error: a λ as a head needs an annotation *)
  rejects "λ as a head" (fun () ->
      item "app-lam" P.Nat (Some (P.App (P.Lam (P.Var 0), P.Z))));
  ignore
    (item "app-lam-annot" P.Nat
       (Some (P.App (P.Annot (P.Lam (P.Var 0), P.Pi (P.Nat, P.Nat)), P.Z))));
  (* a chain whose middles do not join *)
  rejects "chain middles" (fun () ->
      item "bad-chain"
        (P.Eq (P.Z, P.Z, P.Nat))
        (Some (P.Refl (P.Annot (P.Trans (P.Z, P.S P.Z), P.Nat)))));
  (* quotient: ℕ / (x y. 𝟙) with quot-elim into ℕ at 𝕌₀ needs
     well-definedness; the constant function is well defined *)
  let q = item "Q" (P.Sort (U 0)) (Some (P.Quot (P.Nat, P.SquashTy P.One))) in
  check "quotient formed" (q.def = Some (Quot (Nat, Squash One)));
  (* a variable of type Q is STUCK: expose the quotient by the δ leaf
     and conversion, then annotate so the eliminator can synthesise *)
  let scrut =
    P.Annot
      (P.Conv (P.Var 0, P.Delta ("Q", [])), P.Quot (P.Nat, P.SquashTy P.One))
  in
  let const =
    item "const"
      ~tele:[ P.Item ("Q", []) ]
      P.Nat
      (Some
         (P.QuotElim
            ( U 0,
              P.Nat,
              P.Z,
              (* ω: Z ≐ Z at ℕ over Γ ▷ ℕ ▷ ℕ ▷ ∥𝟙∥ *)
              P.Z,
              scrut )))
  in
  check "quot-elim, constant" (const.def = Some (QuotElim (Z, Var 0)));
  rejects "quot-elim, not well defined" (fun () ->
      item "rep"
        ~tele:[ P.Item ("Q", []) ]
        P.Nat
        (Some (P.QuotElim (U 0, P.Nat, P.Var 0, P.Var 2, scrut))));
  (* at Ω the motive is a proposition and well-definedness closes by
     irrelevance: Q ⊦ ∥𝟙∥ by eliminating into Ω *)
  ignore
    (item "q-prop"
       ~tele:[ P.Item ("Q", []) ]
       (P.SquashTy P.One)
       (Some
          (P.QuotElim
             ( Omega,
               P.SquashTy P.One,
               P.Squash P.Unit,
               P.PropIrrel (P.SquashTy P.One, P.Squash P.Unit, P.Squash P.Unit),
               scrut ))));
  (* a motive Ω is a 𝕌₁ family, not a proposition *)
  rejects "motive Ω at Ω" (fun () ->
      item "q-fam"
        ~tele:[ P.Item ("Q", []) ]
        (P.Sort Omega)
        (Some
           (P.QuotElim
              ( Omega,
                P.Sort Omega,
                P.SquashTy P.One,
                P.PropIrrel (P.Sort Omega, P.SquashTy P.One, P.SquashTy P.One),
                scrut ))));
  (* squash: from ∥ℕ∥ to ∥ℕ∥ by unsquash, and 𝟙's elements are irrelevant *)
  ignore
    (item "unsq" ~tele:[ P.SquashTy P.Nat ] (P.SquashTy P.Nat)
       (Some (P.Unsquash (P.SquashTy P.Nat, P.Squash (P.Var 0), P.Var 0))));
  ignore
    (item "unit-irrel" ~tele:[ P.One; P.One ]
       (P.Eq (P.Var 1, P.Var 0, P.One))
       (Some (P.Refl (P.Annot (P.Irrel (P.Var 1, P.Var 0), P.One)))));
  (* let: the hypothesis names the value *)
  ignore
    (item "let-hyp" P.Nat
       (Some (P.Let (P.Annot (P.S P.Z, P.Nat), P.Reflect (P.Var 0)))));
  (* fuel: 0 + 3 by unfolding plus needs two β and four ι steps *)
  let three = P.S (P.S (P.S P.Z)) in
  let plus_3_0 ~fuel =
    Check.check_item ~fuel !sg ~tele:[]
      ~ty:(P.Eq (P.App (P.App (P.Item ("plus", []), P.Z), three), three, P.Nat))
      ~def:
        (Some
           (P.Refl
              (P.Annot (P.App (P.App (P.Delta ("plus", []), P.Z), three), P.Nat))))
  in
  check "plus 0 3 ≡ 3 by δ and computation"
    ((plus_3_0 ~fuel:1000).def = Some Star);
  rejects "fuel exhausted" (fun () -> plus_3_0 ~fuel:3);

  if !failures = 0 then print_endline "kernel_test: ok"
  else (
    Printf.printf "kernel_test: %d failures\n" !failures;
    exit 1)
