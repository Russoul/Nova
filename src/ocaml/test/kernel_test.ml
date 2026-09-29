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

  if !failures = 0 then print_endline "kernel_test: ok"
  else (
    Printf.printf "kernel_test: %d failures\n" !failures;
    exit 1)
