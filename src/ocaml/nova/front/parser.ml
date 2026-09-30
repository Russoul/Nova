(* The parser of the proof language: a hand-written recursive descent
   over the lexer's tokens, producing surface proofs. It is UNTRUSTED,
   so it affords conveniences the kernel does not: binders are NAMED
   and resolved to de Bruijn indices here; keyword forms take their
   arguments in the document's spine style; and layout replaces
   parentheses.

   Grammar (precedence from loose to tight):
     item   ::= NAME ('(' NAME ':' expr ')')* ':' expr [':=' expr]
     expr   ::= arrow (';' arrow)*
     arrow  ::= prod ['→' arrow]                     (x : A) → B binds x
     prod   ::= eq ['×' prod | '⊎' prod | '/' (x y. expr)]
     eq     ::= app ['≡' app '∈' app]
     app    ::= (form | atom) (atom | '.π₁' | '.π₂' | '⁻¹' | ⟪arg⟫)*
                                     a postfix applies to the whole spine before it:
                                     f x .π₁ is (f x) .π₁, reflect h⁻¹ is (reflect h)⁻¹
     atom   ::= NAME ['[' expr, … ']'] | 'δ' NAME ['[' … ']'] | sort
              | '(' expr ')' | '(' expr ',' expr ')' | '(' expr ':' expr ')'
              | '⌜' expr [':' expr] '⌝'        inline reify: the equation as a proposition
              | '⌞' expr [':' expr] '⌟'        inline reflect: the proposition as its equation
              | 'λ' NAME+ '.' expr | '∥' expr '∥' | 'let' NAME NAME ':=' expr 'in' expr
     form   ::= keyword slots, a binder slot written (x y. expr) or ⟪x y. expr⟫;
                a form is a spine head: it may take further arguments;
                reify α and reflect α are the block spellings of the corners

   LAYOUT. The file is a block at column 1: an item starts there and
   its other lines are indented. Inside, three rules:
     1. THE OFFSIDE RULE: a construct's continuation lines are indented
        past the block that encloses it (column > b).
     2. AN INDENTED LINE THAT BEGINS A TERM IS AN ARGUMENT, ⟪arg⟫: a line
        deeper than the line the spine's head sits on (column > r) is
        one more argument of the innermost open spine, a whole term up
        to the next line at or left of its own column. Sibling
        argument lines share their column; a line between r and that
        column is an error.
     3. A LINE MAY HOLD WHAT A PARENTHESIS MAY HOLD: a maximal term, an
        ascription e : T, or a binder abstraction x y. e where the slot
        takes binders; the line's extent replaces the parentheses.
   After a token that demands a term (:=, a binder's '.', → × ⊎ / ≡ ∈ ,
   ; :, 'in', '(') a newline is whitespace. A non-term-initial token on
   a deeper line (an operator, ';', ':', 'in', ')') continues the
   enclosing construct. *)

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

(* a `data` declaration: its level and its entries as token ranges,
   re-parsed at every use in the environment of the use *)
type data = {
  dlevel : int;
  dentries : (string * int) list (* name, first token *);
}

type state = {
  datas : (string, data) Hashtbl.t;
  toks : tok array;
  indent : int array; (* the column of the first token on each token's line *)
  mutable pos : int;
  mutable block : int; (* b: the enclosing block's column *)
  mutable block_tok : int; (* the index of the block's first token *)
  mutable squash : int;
      (* > 0 while inside ∥…∥ and not inside parentheses: there a ∥
         closes rather than opening an argument *)
}

let peek st = st.toks.(st.pos)
let peek_at st k = st.toks.(min (st.pos + k) (Array.length st.toks - 1))
let advance st = if (peek st).kind <> EOF then st.pos <- st.pos + 1

let err st msg =
  let t = peek st in
  raise (Error (t.line, t.col, msg))

let err_at (t : tok) msg = raise (Error (t.line, t.col, msg))

(* Is the next token on the line of the previous one? *)
let same_line st = st.pos > 0 && (peek st).line = st.toks.(st.pos - 1).line

(* May the next token continue the construct being parsed? On the
   same line always; on a new line only past the block column. *)
let continues st = same_line st || (peek st).col > st.block

let with_block st c f =
  let saved = (st.block, st.block_tok) in
  st.block <- c;
  st.block_tok <- st.pos;
  Fun.protect
    ~finally:(fun () ->
      st.block <- fst saved;
      st.block_tok <- snd saved)
    f

(* A new line's token at or left of the block column is not part of
   this block — unless it is the block's own first token. *)
let offside st =
  let t = peek st in
  (not (same_line st)) && t.col <= st.block && st.pos <> st.block_tok

let ident st =
  match (peek st).kind with
  | ID x when not (offside st) ->
      advance st;
      x
  | _ -> err st "expected a name"

let expect st kind what =
  if (peek st).kind = kind && not (offside st) then advance st
  else err st ("expected " ^ what)

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

let is_form = function
  | "reify" | "reflect" | "lift" | "S" | "class" | "squash" | "inj₁" | "inj1"
  | "inj₂" | "inj2" | "𝟘-elim" | "Void-elim" | "η→" | "eta->" | "η×" | "eta*"
  | "conv" | "irrel" | "quot-eq" | "prop-irrel" | "restrict" | "unsquash"
  | "propext" | "ℕ-elim" | "Nat-elim" | "⊎-elim" | "Sum-elim" | "quot-elim"
  | "ν" | "nu" | "out" | "corec" | "ην" | "eta-nu" | "coind" ->
      true
  | _ -> false

(* The identifiers that are never names. *)
let is_keyword s =
  is_form s
  || List.mem s
       [
         "let";
         "in";
         "δ";
         "delta";
         "𝟘";
         "Void";
         "𝟙";
         "Unit";
         "ℕ";
         "Nat";
         "Z";
         "𝕏";
         "K";
         "U";
         "El";
         "data";
       ]
  || Option.is_some (sort_of_id s)

(* Can this token begin a term? *)
let term_initial st (t : tok) =
  match t.kind with
  | ID "in" -> false
  | ID _ | LPAREN | UNIT | LAM | LQUOTE | LUNQUOTE -> true
  | BAR2 -> st.squash = 0
  | _ -> false

(* ----- spines and their argument lines ----- *)

(* The layout state of one spine: the reference column r (the indent
   of the line its head sits on) and the column of its argument block
   once one is open. *)
type spine = { r : int; mutable argcol : int option }

let new_spine st = { r = st.indent.(st.pos); argcol = None }

(* Does the next token start an argument LINE of this spine (rule 2)?
   Only asked on a new line. Opens the argument block on the first
   such line; rejects a misaligned one. *)
let arg_column st sp =
  let t = peek st in
  if same_line st then false
  else
    match sp.argcol with
    | None ->
        if t.col > sp.r && t.col > st.block then (
          sp.argcol <- Some t.col;
          true)
        else false
    | Some c0 ->
        if t.col = c0 then true
        else if t.col > sp.r && t.col > st.block then
          err_at t
            (Printf.sprintf
               "an argument line at column %d — this spine's arguments stand \
                at column %d"
               t.col c0)
        else false

let arg_line st sp = term_initial st (peek st) && arg_column st sp

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

(* A same-line atom may follow. *)
and starts_atom st = same_line st && term_initial st (peek st)

and app st env =
  let t = peek st in
  if offside st then err st "a term must be indented past its block";
  let sp = new_spine st in
  let head =
    match t.kind with
    | ID s when is_form s ->
        advance st;
        form st env sp s
    | ID s when Hashtbl.mem st.datas s && (peek_at st 1).kind = DOT ->
        advance st;
        qiit_form st env sp s
    | _ -> atom st env
  in
  let rec loop h =
    match (peek st).kind with
    | PROJ1 when continues st ->
        advance st;
        loop (P.Fst h)
    | PROJ2 when continues st ->
        advance st;
        loop (P.Snd h)
    | INV when continues st ->
        advance st;
        loop (P.Sym h)
    | _ ->
        if starts_atom st then loop (P.App (h, atom st env))
        else if arg_line st sp then loop (P.App (h, block_arg st env))
        else h
  in
  loop head

(* An argument line: a maximal term, or an ascription e : T. *)
and block_arg st env =
  with_block st (peek st).col (fun () ->
      let e = expr st env in
      if (peek st).kind = COLON && continues st then (
        advance st;
        let ty = expr st env in
        P.Annot (e, ty))
      else e)

(* A slot of a keyword form: an atom on the same line, or an argument
   line. With n > 0 binders, the parenthesised (x y. e) or the bare
   x y. e on its line. *)
and slot st env sp n : P.t =
  if same_line st then bound st env n
  else if arg_line st sp then
    with_block st (peek st).col (fun () ->
        if n = 0 then
          let e = expr st env in
          if (peek st).kind = COLON && continues st then (
            advance st;
            let ty = expr st env in
            P.Annot (e, ty))
          else e
        else if (peek st).kind = LPAREN then bound st env n
        else binder_body st env n)
  else err st "expected an argument"

and binder_body st env n =
  let names = List.init n (fun _ -> ident st) in
  expect st DOT "'.' after the binder's names";
  let env' = List.fold_left (fun e x -> x :: e) env names in
  expr st env'

and form st env sp s : P.t =
  let a () = slot st env sp 0 in
  let b n = slot st env sp n in
  let sort () =
    let t = peek st in
    if (not (same_line st)) && not (arg_line st sp) then
      err st "expected a sort";
    match t.kind with
    | ID x -> (
        match sort_of_id x with
        | Some u ->
            advance st;
            u
        | None -> err st "expected a sort")
    | _ -> err st "expected a sort"
  in
  match s with
  | "reify" -> P.Refl (a ())
  | "reflect" -> P.Reflect (a ())
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
  | "ν" | "nu" -> P.Nu (poly st env)
  | "out" -> P.Out (a ())
  | "corec" ->
      let f = poly st env in
      let x, carrier, body = carrier_binder st env sp in
      ignore x;
      let seed = a () in
      P.Corec (f, carrier, body, seed)
  | "ην" | "eta-nu" ->
      let f = poly st env in
      let _, carrier, body = carrier_binder st env sp in
      let h = b 1 in
      let alpha = b 1 in
      let x = a () in
      P.EtaNu (f, carrier, body, h, alpha, x)
  | "coind" ->
      let t0 = a () in
      let t1 = a () in
      let r = b 2 in
      let p = a () in
      let q = b 3 in
      P.Coind (t0, t1, r, p, q)
  | _ -> err st ("not a form: " ^ s)

(* corec's carrier binder (s : a. e): the name, the carrier, the body
   under the name; parenthesised, or bare on an argument line *)
and carrier_binder st env sp =
  let body () =
    let x = ident st in
    expect st COLON "':' after the carrier's name";
    let a = expr st env in
    expect st DOT "'.' after the carrier";
    let e = expr st (x :: env) in
    (x, a, e)
  in
  if same_line st || not (arg_line st sp) then (
    expect st LPAREN "a carrier binder (s : a. …)";
    let r = body () in
    expect st RPAREN "')'";
    r)
  else
    with_block st (peek st).col (fun () ->
        if (peek st).kind = LPAREN then (
          advance st;
          let r = body () in
          expect st RPAREN "')'";
          r)
        else body ())

(* ----- polynomials ----- *)
(* poly ::= pprod ['⊎' poly]; pprod ::= patom ['×' pprod]
   patom ::= '𝕏' | 'K' atom | '(' x ':' expr ')' ('×' | '→') poly | '(' poly ')' *)
and poly st env : P.t poly =
  let l = pprod st env in
  if (peek st).kind = SUM && continues st then (
    advance st;
    PSum (l, poly st env))
  else l

and pprod st env : P.t poly =
  let l = patom st env in
  if (peek st).kind = TIMES && continues st then (
    advance st;
    PProd (l, pprod st env))
  else l

and patom st env : P.t poly =
  match (peek st).kind with
  | ID ("𝕏" | "X") ->
      advance st;
      PX
  | ID "K" ->
      advance st;
      PK (atom st env)
  | LPAREN -> (
      match ((peek_at st 1).kind, (peek_at st 2).kind) with
      | ID x, COLON when not (is_keyword x) -> (
          advance st;
          advance st;
          advance st;
          let a = expr st env in
          expect st RPAREN "')'";
          match (peek st).kind with
          | TIMES ->
              advance st;
              PSigma (a, poly st (x :: env))
          | ARROW ->
              advance st;
              PPi (a, poly st (x :: env))
          | _ -> err st "expected '×' or '→' after a polynomial's binder")
      | _ ->
          advance st;
          let f = poly st env in
          expect st RPAREN "')'";
          f)
  | _ -> err st "expected a polynomial"

(* ----- signatures ----- *)
(* At a use, the entries of a data declaration are parsed in the
   current environment: Nova names resolve against env and the
   external binders, ToS names against the entries before and the
   internal binders. *)
and signature_of st env (name : string) : P.t signature * string list =
  let d = Hashtbl.find st.datas name in
  let saved = (st.pos, st.block, st.block_tok) in
  let entries, names =
    List.fold_left
      (fun (acc, names) (n, start) ->
        st.pos <- start;
        st.block <- st.toks.(start).col;
        st.block_tok <- start;
        ignore (ident st);
        expect st COLON "':'";
        let k = qty st env names in
        (k :: acc, n :: names))
      ([], []) d.dentries
  in
  let p, b, bt = saved in
  st.pos <- p;
  st.block <- b;
  st.block_tok <- bt;
  ({ level = d.dlevel; entries }, names)

and qty st env tos : P.t qty =
  match (peek st).kind with
  | ID "U" ->
      advance st;
      QU
  | ID "El" -> (
      advance st;
      let t = qtm st env tos in
      match (peek st).kind with
      | ARROW2 when continues st ->
          advance st;
          QInt (t, qty st env ("_" :: tos))
      | _ -> QEl t)
  | LPAREN
    when match ((peek_at st 1).kind, (peek_at st 2).kind) with
         | ID _, COLON -> true
         | _ -> false -> (
      advance st;
      let x = ident st in
      expect st COLON "':'";
      match (peek st).kind with
      | ID "El" ->
          advance st;
          let t = qtm st env tos in
          expect st RPAREN "')'";
          expect st ARROW2 "'⇛'";
          QInt (t, qty st env (x :: tos))
      | _ ->
          let a = expr st env in
          expect st RPAREN "')'";
          expect st ARROW2 "'⇛'";
          QExt (a, qty st (x :: env) tos))
  | ID x when List.mem x tos -> (
      (* a bare ToS term: El 𝕥, an equation code included *)
      let t = qtm st env tos in
      match (peek st).kind with
      | ARROW2 when continues st ->
          advance st;
          QInt (t, qty st env ("_" :: tos))
      | _ -> QEl t)
  | _ ->
      let a = expr st env in
      expect st ARROW2 "'⇛'";
      QExt (a, qty st ("_" :: env) tos)

and is_tos_name tos = function ID x -> List.mem x tos | _ -> false

and qtm st env tos : P.t qtm =
  let l = qapp st env tos in
  if (peek st).kind = EQUIV && continues st then (
    advance st;
    QEq (l, qapp st env tos))
  else l

and qapp st env tos : P.t qtm =
  let head =
    match (peek st).kind with
    | ID x when List.mem x tos ->
        advance st;
        QVar (Option.get (index_of x tos))
    | LAM ->
        advance st;
        let x = ident st in
        expect st DOT "'.'";
        QLam (qtm st (x :: env) tos)
    | LPAREN ->
        advance st;
        let t = qtm st env tos in
        expect st RPAREN "')'";
        t
    | _ -> err st "expected a ToS term"
  in
  let rec loop h =
    if not (starts_atom st) then h
    else
      match (peek st).kind with
      | ID x when List.mem x tos ->
          advance st;
          loop (QApp (h, QVar (Option.get (index_of x tos))))
      | LPAREN when is_tos_name tos (peek_at st 1).kind ->
          advance st;
          let u = qtm st env tos in
          expect st RPAREN "')'";
          loop (QApp (h, u))
      | _ -> loop (QAppExt (h, atom st env))
  in
  loop head

(* NAME.entry[args], NAME.entry-elim sorts d̄… [indices] w *)
and qiit_form st env sp (name : string) : P.t =
  expect st DOT "'.' after a data name";
  let entry =
    match (peek st).kind with
    | ID e ->
        advance st;
        e
    | _ -> err st "expected an entry of the data declaration"
  in
  let sg, names = signature_of st env name in
  let n = List.length names in
  let index e =
    match index_of e names with
    | Some i -> i
    | None -> err st (name ^ " has no entry " ^ e)
  in
  let suffix = "-elim" in
  let ls = String.length suffix and le = String.length entry in
  if le > ls && String.sub entry (le - ls) ls = suffix then (
    let s = index (String.sub entry 0 (le - ls)) in
    let n_sorts =
      List.length
        (List.filter
           (fun k ->
             match k with
             | QU | QExt (_, _) | QInt (_, _) -> is_sort_entry k
             | QEl _ -> false)
           sg.entries)
    in
    let rec many k f acc =
      if k = 0 then List.rev acc else many (k - 1) f (f () :: acc)
    in
    let sorts = many n_sorts (fun () -> sort_slot st sp) [] in
    let ds = many n (fun () -> slot st env sp 0) [] in
    (* the index spine may stand on an argument line of its own *)
    if (peek st).kind = LBRACK && not (same_line st) then
      ignore (arg_column st sp);
    let es = spine_args ~line:true st env in
    let w = slot st env sp 0 in
    P.QElim (sg, s, sorts, List.rev ds, es, w))
  else
    let i = index entry in
    let es = spine_args st env in
    if is_sort_entry (List.nth sg.entries i) then P.QSort (sg, i, es)
    else P.QCon (sg, i, es)

and is_sort_entry : P.t qty -> bool = function
  | QU -> true
  | QEl _ -> false
  | QExt (_, k) | QInt (_, k) -> is_sort_entry k

and sort_slot st sp =
  let t = peek st in
  if (not (same_line st)) && not (arg_line st sp) then err st "expected a sort";
  match t.kind with
  | ID x -> (
      match sort_of_id x with
      | Some u ->
          advance st;
          u
      | None -> err st "expected a sort")
  | _ -> err st "expected a sort"

(* A binder argument (x₁ … xₙ. e) with exactly n names; n = 0 is an
   atom. *)
and bound st env n : P.t =
  if n = 0 then atom st env
  else (
    expect st LPAREN "a binder (x. …)";
    let e = binder_body st env n in
    expect st RPAREN "')'";
    e)

and spine_args ?(line = false) st env : P.t list =
  (* [e₀, …, eₙ] in order; returned as a snoc list *)
  if (peek st).kind = LBRACK && (same_line st || line) then (
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
  | None -> P.Item (x, spine_args st env)

and atom st env : P.t =
  let t = peek st in
  if offside st then err st "a term must be indented past its block";
  match t.kind with
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
  | LQUOTE -> corners st env RQUOTE "'⌝'" (fun e -> P.Refl e)
  | LUNQUOTE -> corners st env RUNQUOTE "'⌟'" (fun e -> P.Reflect e)
  | ID s -> (
      advance st;
      match s with
      | "let" ->
          let x = ident st in
          let h = ident st in
          expect st DEF "':='";
          let a = expr st env in
          (match (peek st).kind with
          | ID "in" when continues st -> advance st
          | _ -> err st "expected 'in'");
          let b = expr st (h :: x :: env) in
          P.Let (a, b)
      | "δ" | "delta" ->
          let x = ident st in
          P.Delta (x, spine_args st env)
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

(* ⌜e⌝ and ⌞e⌟: the content is what a parenthesis may hold, an
   expression or an ascription. *)
and corners st env closer what wrap : P.t =
  advance st;
  let saved = st.squash in
  st.squash <- 0;
  let e = expr st env in
  let e =
    if (peek st).kind = COLON && continues st then (
      advance st;
      let ty = expr st env in
      P.Annot (e, ty))
    else e
  in
  st.squash <- saved;
  expect st closer what;
  wrap e

(* ----- items ----- *)

(* data NAME : 𝕌ℓ, then one entry `name : qty` per indented line; the
   entries are recorded as token ranges and parsed at each use *)
let data_decl st : unit =
  advance st;
  let name = ident st in
  expect st COLON "':'";
  let level =
    match (peek st).kind with
    | ID x -> (
        match sort_of_id x with
        | Some (U l) ->
            advance st;
            l
        | _ -> err st "a data declaration names a universe level")
    | _ -> err st "a data declaration names a universe level"
  in
  let rec entries acc =
    let t = peek st in
    if t.kind <> EOF && t.col > 1 then (
      let start = st.pos in
      let n = ident st in
      expect st COLON "':'";
      (* skip the entry's tokens: up to the next line at or left of its column *)
      while (peek st).kind <> EOF && (same_line st || (peek st).col > t.col) do
        advance st
      done;
      entries ((n, start) :: acc))
    else List.rev acc
  in
  let dentries = entries [] in
  Hashtbl.replace st.datas name { dlevel = level; dentries }

let item st : item =
  let t = peek st in
  if t.col <> 1 then
    err st
      (Printf.sprintf
         "column %d does not continue the item above — indent it past the term \
          it belongs to, or start an item at column 1"
         t.col);
  let name =
    match t.kind with
    | ID x ->
        advance st;
        x
    | _ -> err st "expected an item's name"
  in
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
  let toks = Array.of_list (Lexer.tokenize src) in
  let indent = Array.make (Array.length toks) 1 in
  let cur_line = ref 0 and cur_indent = ref 1 in
  Array.iteri
    (fun i (t : tok) ->
      if t.line <> !cur_line then (
        cur_line := t.line;
        cur_indent := t.col);
      indent.(i) <- !cur_indent)
    toks;
  let st =
    {
      datas = Hashtbl.create 8;
      toks;
      indent;
      pos = 0;
      block = 1;
      block_tok = -1;
      squash = 0;
    }
  in
  let rec loop acc =
    match (peek st).kind with
    | EOF -> List.rev acc
    | ID "data" ->
        data_decl st;
        loop acc
    | _ -> loop (item st :: acc)
  in
  loop []
