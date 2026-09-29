(* The parser of the proof language: a hand-written recursive descent
   over the lexer's tokens, producing surface proofs. It is UNTRUSTED,
   so it affords conveniences the kernel does not: binders are NAMED
   and resolved to de Bruijn indices here; keyword forms take their
   arguments as atoms in the document's spine style.

   Layout: an item starts with an identifier at column 0; a token at
   column 0 therefore ends the expression before it.

   Grammar (precedence from loose to tight):
     item   ::= NAME ('(' NAME ':' expr ')')* ':' expr [':=' expr]
     expr   ::= arrow (';' arrow)*
     arrow  ::= prod ['→' arrow]                     (x : A) → B binds x
     prod   ::= eq ['×' prod | '⊎' prod | '/' (x y. expr)]
     eq     ::= app ['≡' app '∈' app]
     app    ::= (form | atom) atom*
     atom   ::= NAME ['[' expr, … ']'] | 'δ' NAME ['[' … ']'] | sort
              | '(' expr ')' | '(' expr ',' expr ')' | '(' expr ':' expr ')'
              | 'λ' NAME+ '.' expr | '∥' expr '∥' | 'let' NAME NAME ':=' expr 'in' expr
              | atom '.π₁' | atom '.π₂' | atom '⁻¹'
     form   ::= keyword args, a binder argument written (x y. expr) *)

open Core
module P = Proof
open Lexer

type item = {
  name : string;
  line : int;
  params : (string * P.t) list; (* in order of binding *)
  ty : P.t;
  def : P.t option;
}

exception Error of int * int * string

type state = { toks : tok array; mutable pos : int; mutable squash : int }
(* squash > 0 while inside ∥…∥ and not inside parentheses: there a ∥
   closes rather than opening an argument *)

let peek st = st.toks.(st.pos)
let peek_at st k = st.toks.(min (st.pos + k) (Array.length st.toks - 1))
let advance st = if (peek st).kind <> EOF then st.pos <- st.pos + 1

let err st msg =
  let t = peek st in
  raise (Error (t.line, t.col, msg))

let expect st kind what =
  if (peek st).kind = kind then advance st else err st ("expected " ^ what)

let ident st =
  match (peek st).kind with
  | ID x ->
      advance st;
      x
  | _ -> err st "expected a name"

(* A token at column 0 belongs to the next item. *)
let continues st = (peek st).col > 1

(* ----- names ----- *)

let rec index_of x = function
  | [] -> None
  | y :: rest -> if x = y then Some 0 else Option.map succ (index_of x rest)

let subscript_digit c =
  if c >= 0x30 && c <= 0x39 then Some (c - 0x30)
  else if c >= 0x2080 && c <= 0x2089 then Some (c - 0x2080)
  else None

let sort_of_id (s : string) : sort option =
  let cps = Array.to_list (Array.map (fun (c, _, _) -> c) (Lexer.decode s)) in
  match cps with
  | [ 0x3A9 ] -> Some Omega
  | _ -> (
      if s = "Omega" then Some Omega
      else
        let digits = function
          | [] -> None
          | ds ->
              List.fold_left
                (fun acc d ->
                  match (acc, subscript_digit d) with
                  | Some n, Some k -> Some ((n * 10) + k)
                  | _ -> None)
                (Some 0) ds
        in
        match cps with
        | 0x1D54C :: ds | 0x55 :: ds -> Option.map (fun l -> U l) (digits ds)
        | _ -> None)

(* ----- expressions ----- *)

let rec expr st env : P.t =
  let l = arrow st env in
  let rec loop l =
    if (peek st).kind = SEMI && continues st then (
      advance st;
      let r = arrow st env in
      loop (P.Trans (l, r)))
    else l
  in
  loop l

and arrow st env =
  let l = prod st env in
  if (peek st).kind = ARROW && continues st then (
    advance st;
    let r = arrow st ("_" :: env) in
    P.Pi (l, r))
  else l

and prod st env =
  let l = eq st env in
  match (peek st).kind with
  | TIMES when continues st ->
      advance st;
      let r = prod st ("_" :: env) in
      P.Sigma (l, r)
  | SUM when continues st ->
      advance st;
      let r = prod st env in
      P.Sum (l, r)
  | SLASH when continues st ->
      advance st;
      let r = bound st env 2 in
      P.Quot (l, r)
  | _ -> l

and eq st env =
  let l = app st env in
  if (peek st).kind = EQUIV && continues st then (
    advance st;
    let r = app st env in
    expect st MEMBER "∈";
    let t = app st env in
    P.Eq (l, r, t))
  else l

and starts_atom st =
  continues st
  &&
  match (peek st).kind with
  | ID "in" -> false
  | ID _ | LPAREN | UNIT | LAM -> true
  | BAR2 -> st.squash = 0
  | _ -> false

and app st env =
  let head =
    match (peek st).kind with
    | ID s when is_form s ->
        advance st;
        form st env s
    | _ -> atom st env
  in
  let rec loop h =
    if starts_atom st then loop (P.App (h, atom st env)) else h
  in
  loop head

and is_form = function
  | "refl" | "reflect" | "switch" | "lift" | "S" | "class" | "squash" | "inj₁"
  | "inj1" | "inj₂" | "inj2" | "𝟘-elim" | "Void-elim" | "η→" | "eta->" | "η×"
  | "eta*" | "conv" | "irrel" | "quot-eq" | "prop-irrel" | "restrict"
  | "unsquash" | "propext" | "ℕ-elim" | "Nat-elim" | "⊎-elim" | "Sum-elim"
  | "quot-elim" ->
      true
  | _ -> false

and form st env s : P.t =
  let a () = atom st env in
  let b n = bound st env n in
  let sort () =
    match (peek st).kind with
    | ID x -> (
        match sort_of_id x with
        | Some u ->
            advance st;
            u
        | None -> err st "expected a sort")
    | _ -> err st "expected a sort"
  in
  match s with
  | "refl" -> P.Refl (a ())
  | "reflect" -> P.Reflect (a ())
  | "switch" -> P.Switch (a ())
  | "lift" -> P.Lift (a ())
  | "S" -> P.S (a ())
  | "class" -> P.Class (a ())
  | "squash" -> P.Squash (a ())
  | "inj₁" | "inj1" -> P.Inl (a ())
  | "inj₂" | "inj2" -> P.Inr (a ())
  | "𝟘-elim" | "Void-elim" -> P.ZeroElim (a ())
  | "η→" | "eta->" -> P.EtaPi (a ())
  | "η×" | "eta*" -> P.EtaSigma (a ())
  | "conv" ->
      let x = a () in
      let y = a () in
      P.Conv (x, y)
  | "irrel" ->
      let x = a () in
      let y = a () in
      P.Irrel (x, y)
  | "quot-eq" ->
      let x = a () in
      let y = a () in
      let z = a () in
      P.QuotEq (x, y, z)
  | "prop-irrel" ->
      let x = a () in
      let y = a () in
      let z = a () in
      P.PropIrrel (x, y, z)
  | "restrict" ->
      let x = a () in
      let y = a () in
      let z = a () in
      P.Restrict (x, y, z)
  | "unsquash" ->
      let g = a () in
      let x = b 1 in
      let y = a () in
      P.Unsquash (g, x, y)
  | "propext" ->
      let r = a () in
      let t = a () in
      let g = b 1 in
      let i = b 1 in
      P.Propext (r, t, g, i)
  | "ℕ-elim" | "Nat-elim" ->
      let u = sort () in
      let m = b 1 in
      let z = a () in
      let s = b 2 in
      let t = a () in
      P.NatElim (u, m, z, s, t)
  | "⊎-elim" | "Sum-elim" ->
      let u = sort () in
      let m = b 1 in
      let l = b 1 in
      let r = b 1 in
      let t = a () in
      P.SumElim (u, m, l, r, t)
  | "quot-elim" ->
      let u = sort () in
      let m = b 1 in
      let f = b 1 in
      let w = b 3 in
      let q = a () in
      P.QuotElim (u, m, f, w, q)
  | _ -> err st ("not a form: " ^ s)

(* A binder argument (x₁ … xₙ. e) with exactly n names; n = 0 is an
   atom. *)
and bound st env n : P.t =
  if n = 0 then atom st env
  else (
    expect st LPAREN "a binder (x. …)";
    let names = List.init n (fun _ -> ident st) in
    expect st DOT "'.' after the binder's names";
    let env' = List.fold_left (fun e x -> x :: e) env names in
    let e = expr st env' in
    expect st RPAREN "')'";
    e)

and spine st env : P.t list =
  (* [e₀, …, eₙ] in order; returned as a snoc list *)
  if (peek st).kind = LBRACK then (
    advance st;
    let rec items acc =
      if (peek st).kind = RBRACK then (
        advance st;
        acc)
      else
        let e = expr st env in
        let acc = e :: acc in
        match (peek st).kind with
        | COMMA ->
            advance st;
            items acc
        | RBRACK ->
            advance st;
            acc
        | _ -> err st "expected ',' or ']'"
    in
    items [])
  else []

and name_ref st env x : P.t =
  match index_of x env with
  | Some i -> P.Var i
  | None -> P.Item (x, spine st env)

(* The identifiers that are never names: a (x : A) after '(' with such
   an x is an annotation, not a binder. *)
and is_keyword s =
  is_form s
  || List.mem s
       [ "let"; "in"; "δ"; "delta"; "𝟘"; "Void"; "𝟙"; "Unit"; "ℕ"; "Nat"; "Z" ]
  || Option.is_some (sort_of_id s)

and atom st env : P.t =
  let base = atom_base st env in
  let rec post e =
    match (peek st).kind with
    | PROJ1 when continues st ->
        advance st;
        post (P.Fst e)
    | PROJ2 when continues st ->
        advance st;
        post (P.Snd e)
    | INV when continues st ->
        advance st;
        post (P.Sym e)
    | _ -> e
  in
  post base

and atom_base st env : P.t =
  match (peek st).kind with
  | UNIT ->
      advance st;
      P.Unit
  | LPAREN -> (
      let saved = st.squash in
      st.squash <- 0;
      let restore () = st.squash <- saved in
      match ((peek_at st 1).kind, (peek_at st 2).kind) with
      | ID x, COLON when not (is_keyword x) -> (
          (* (x : A) → B, (x : A) × B, or the annotation (x : T) *)
          advance st;
          advance st;
          advance st;
          let a = expr st env in
          expect st RPAREN "')'";
          restore ();
          match (peek st).kind with
          | ARROW when continues st ->
              advance st;
              P.Pi (a, arrow st (x :: env))
          | TIMES when continues st ->
              advance st;
              P.Sigma (a, prod st (x :: env))
          | _ -> P.Annot (name_ref st env x, a))
      | _ ->
          advance st;
          let e = expr st env in
          let r =
            match (peek st).kind with
            | COMMA ->
                advance st;
                let f = expr st env in
                expect st RPAREN "')'";
                P.Pair (e, f)
            | COLON ->
                advance st;
                let t = expr st env in
                expect st RPAREN "')'";
                P.Annot (e, t)
            | _ ->
                expect st RPAREN "')'";
                e
          in
          restore ();
          r)
  | LAM ->
      advance st;
      let rec names acc =
        match (peek st).kind with
        | ID x ->
            advance st;
            names (x :: acc)
        | DOT ->
            advance st;
            List.rev acc
        | _ -> err st "expected a name or '.'"
      in
      let xs = names [] in
      if xs = [] then err st "λ needs a name";
      let env' = List.fold_left (fun e x -> x :: e) env xs in
      let body = expr st env' in
      List.fold_left (fun b _ -> P.Lam b) body xs
  | BAR2 ->
      advance st;
      let saved = st.squash in
      st.squash <- saved + 1;
      let e = expr st env in
      st.squash <- saved;
      expect st BAR2 "'∥'";
      P.SquashTy e
  | ID s -> (
      advance st;
      match s with
      | "let" ->
          let x = ident st in
          let h = ident st in
          expect st DEF "':='";
          let a = expr st env in
          (match (peek st).kind with
          | ID "in" -> advance st
          | _ -> err st "expected 'in'");
          let b = expr st (h :: x :: env) in
          P.Let (a, b)
      | "δ" | "delta" ->
          let x = ident st in
          P.Delta (x, spine st env)
      | "in" -> err st "'in' closes a let; it is not a name"
      | "𝟘" | "Void" -> P.Zero
      | "𝟙" | "Unit" -> P.One
      | "ℕ" | "Nat" -> P.Nat
      | "Z" -> P.Z
      | _ -> (
          match sort_of_id s with
          | Some u -> P.Sort u
          | None ->
              if is_form s then
                err st (s ^ " takes arguments; parenthesise the form")
              else name_ref st env s))
  | _ -> err st "expected an expression"

(* ----- items ----- *)

let item st : item =
  let t = peek st in
  if t.col <> 1 then err st "an item starts at column 0";
  let name = ident st in
  let rec params env acc =
    if (peek st).kind = LPAREN && continues st then (
      advance st;
      let x = ident st in
      expect st COLON "':'";
      let a = expr st env in
      expect st RPAREN "')'";
      params (x :: env) ((x, a) :: acc))
    else (env, List.rev acc)
  in
  let env, params = params [] [] in
  expect st COLON "':'";
  let ty = expr st env in
  let def =
    if (peek st).kind = DEF && continues st then (
      advance st;
      Some (expr st env))
    else None
  in
  { name; line = t.line; params; ty; def }

let items (src : string) : item list =
  let st = { toks = Array.of_list (Lexer.tokenize src); pos = 0; squash = 0 } in
  let rec loop acc =
    if (peek st).kind = EOF then List.rev acc else loop (item st :: acc)
  in
  loop []
