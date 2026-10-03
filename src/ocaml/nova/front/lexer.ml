(* The lexer of the proof language. Hand-written over UTF-8 code
   points, so the Unicode of docs/NovaKernel.txt lexes directly. Each
   symbol has ONE spelling, the document's. Identifiers may contain '-'
   (ℕ-elim, quot-eq, two-is-SSZ), so keywords are identifiers the
   parser recognises. *)

type kind =
  | ID of string
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | COMMA
  | DOT
  | COLON
  | SEMI
  | ARROW (* → *)
  | TIMES (* × *)
  | SUM (* ⊎ *)
  | SLASH
  | EQUIV (* ≡ *)
  | MEMBER (* ∈ *)
  | LAM (* λ *)
  | BAR2 (* ∥ *)
  | INV (* ⁻¹ *)
  | DEF (* := *)
  | UNIT (* () *)
  | PROJ1 (* .π₁ *)
  | PROJ2 (* .π₂ *)
  | ARROW2 (* ⇛ *)
  | LQUOTE (* ⌜ *)
  | RQUOTE (* ⌝ *)
  | LUNQUOTE (* ⌞ *)
  | RUNQUOTE (* ⌟ *)
  | LANGLE (* ⟨ *)
  | RANGLE (* ⟩ *)
  | MAPSTO (* ↪ *)
  | FIELD of string
    (* .l, a record projection: the dot glued to the label and NOT glued
       to an identifier before it — r .l, (f x).l. A binder's dot
       (λx. e) is followed by a space, a data entry's (Bag.ins) is glued
       on both sides; both stay DOT. *)
  | EOF

type tok = { kind : kind; line : int; col : int }

exception Error of int * int * string

(* UTF-8 to code points with positions; columns count code points. *)
let decode (s : string) : (int * int * int) array =
  let n = String.length s in
  let out = ref [] in
  let i = ref 0 and line = ref 1 and col = ref 1 in
  while !i < n do
    let c = Char.code s.[!i] in
    let cp, len =
      if c < 0x80 then (c, 1)
      else if c < 0xE0 then
        (((c land 0x1F) lsl 6) lor (Char.code s.[!i + 1] land 0x3F), 2)
      else if c < 0xF0 then
        ( ((c land 0x0F) lsl 12)
          lor ((Char.code s.[!i + 1] land 0x3F) lsl 6)
          lor (Char.code s.[!i + 2] land 0x3F),
          3 )
      else
        ( ((c land 0x07) lsl 18)
          lor ((Char.code s.[!i + 1] land 0x3F) lsl 12)
          lor ((Char.code s.[!i + 2] land 0x3F) lsl 6)
          lor (Char.code s.[!i + 3] land 0x3F),
          4 )
    in
    out := (cp, !line, !col) :: !out;
    i := !i + len;
    if cp = 10 then (
      incr line;
      col := 1)
    else incr col
  done;
  Array.of_list (List.rev !out)

let encode (cps : int list) : string =
  let b = Buffer.create 16 in
  List.iter (fun cp -> Buffer.add_utf_8_uchar b (Uchar.of_int cp)) cps;
  Buffer.contents b

(* The Unicode symbols that are tokens of their own, never identifier
   characters. *)
let symbol = function
  | 0x2192 (* → *)
  | 0xD7 (* × *)
  | 0x228E (* ⊎ *)
  | 0x2261 (* ≡ *)
  | 0x2208 (* ∈ *)
  | 0x3BB (* λ *)
  | 0x2225 (* ∥ *)
  | 0x207B (* ⁻ *)
  | 0x231C | 0x231D | 0x231E | 0x231F (* ⌜ ⌝ ⌞ ⌟ *)
  | 0x27E8 | 0x27E9 (* ⟨ ⟩ *)
  | 0x21AA (* ↪ *)
  | 0x21DB (* ⇛ *) ->
      true
  | _ -> false

let is_digit c = c >= 0x30 && c <= 0x39
let is_subscript c = c >= 0x2080 && c <= 0x2089

let is_id_start c =
  (c >= 0x41 && c <= 0x5A)
  || (c >= 0x61 && c <= 0x7A)
  || c = 0x5F
  || (c >= 0x80 && (not (symbol c)) && not (is_subscript c))

let is_id_cont c = is_id_start c || is_digit c || is_subscript c || c = 0x27

let tokenize (src : string) : tok list =
  let a = decode src in
  let n = Array.length a in
  let cp i =
    if i < n then
      let c, _, _ = a.(i) in
      c
    else -1
  in
  let toks = ref [] in
  let emit i kind =
    let _, line, col = a.(i) in
    toks := { kind; line; col } :: !toks
  in
  let err i msg =
    let _, line, col = if i < n then a.(i) else (0, 0, 0) in
    raise (Error (line, col, msg))
  in
  let i = ref 0 in
  while !i < n do
    let c = cp !i in
    let start = !i in
    if c = 0x20 || c = 0x09 || c = 0x0A || c = 0x0D then incr i
    else if c = 0x2D && cp (!i + 1) = 0x2D then
      (* -- comment *)
      while !i < n && cp !i <> 0x0A do
        incr i
      done
    else if is_id_start c then begin
      let j = ref (!i + 1) in
      let continue = ref true in
      while !continue do
        if is_id_cont (cp !j) then incr j
        else if cp !j = 0x2D && is_id_cont (cp (!j + 1)) then j := !j + 2
        else continue := false
      done;
      let cps = List.init (!j - !i) (fun k -> cp (!i + k)) in
      (* η→ and η× are one keyword each *)
      let cps, j =
        if cps = [ 0x3B7 ] && (cp !j = 0x2192 || cp !j = 0xD7) then
          (cps @ [ cp !j ], !j + 1)
        else (cps, !j)
      in
      emit start (ID (encode cps));
      i := j
    end
    else begin
      let two k1 k2 = cp !i = k1 && cp (!i + 1) = k2 in
      let one kind =
        emit start kind;
        incr i
      in
      let two_ kind =
        emit start kind;
        i := !i + 2
      in
      if two 0x28 0x29 then two_ UNIT
      else if two 0x3A 0x3D then two_ DEF
      else if two 0x207B 0xB9 then two_ INV
      else if cp !i = 0x2E && cp (!i + 1) = 0x3C0 && cp (!i + 2) = 0x2081 then (
        emit start PROJ1;
        i := !i + 3)
      else if cp !i = 0x2E && cp (!i + 1) = 0x3C0 && cp (!i + 2) = 0x2082 then (
        emit start PROJ2;
        i := !i + 3)
      else if
        c = 0x2E
        && is_id_start (cp (!i + 1))
        && not (!i > 0 && is_id_cont (cp (!i - 1)))
      then begin
        (* .l: a record projection *)
        let j = ref (!i + 2) in
        let continue = ref true in
        while !continue do
          if is_id_cont (cp !j) then incr j
          else if cp !j = 0x2D && is_id_cont (cp (!j + 1)) then j := !j + 2
          else continue := false
        done;
        emit start
          (FIELD (encode (List.init (!j - !i - 1) (fun k -> cp (!i + 1 + k)))));
        i := !j
      end
      else if c = 0x228E && cp (!i + 1) = 0x2D then begin
        (* ⊎-elim *)
        let j = ref (!i + 2) in
        while is_id_cont (cp !j) do
          incr j
        done;
        emit start (ID (encode (List.init (!j - !i) (fun k -> cp (!i + k)))));
        i := !j
      end
      else
        match c with
        | 0x28 -> one LPAREN
        | 0x29 -> one RPAREN
        | 0x5B -> one LBRACK
        | 0x5D -> one RBRACK
        | 0x2C -> one COMMA
        | 0x2E -> one DOT
        | 0x3A -> one COLON
        | 0x3B -> one SEMI
        | 0x2192 -> one ARROW
        | 0xD7 -> one TIMES
        | 0x228E -> one SUM
        | 0x2F -> one SLASH
        | 0x2261 -> one EQUIV
        | 0x2208 -> one MEMBER
        | 0x3BB -> one LAM
        | 0x2225 -> one BAR2
        | 0x21DB -> one ARROW2
        | 0x231C -> one LQUOTE
        | 0x231D -> one RQUOTE
        | 0x231E -> one LUNQUOTE
        | 0x231F -> one RUNQUOTE
        | 0x27E8 -> one LANGLE
        | 0x27E9 -> one RANGLE
        | 0x21AA -> one MAPSTO
        | _ -> err !i (Printf.sprintf "unexpected character U+%04X" c)
    end
  done;
  let line, col =
    if n = 0 then (1, 1)
    else
      let _, l, c = a.(n - 1) in
      (l, c + 1)
  in
  List.rev ({ kind = EOF; line; col } :: !toks)
