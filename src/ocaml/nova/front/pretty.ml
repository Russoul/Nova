(* A printer for core terms, for reports and golden outputs. De Bruijn
   indices print as ☐i; a part under binders prints as (. e), (.. e),
   one dot per binder. *)

open Core

let sort = function Omega -> "Ω" | U l -> "𝕌" ^ string_of_int l

(* precedence: 0 arrow/chain-free, 1 product, 2 equation, 3 application, 4 atom *)
let rec go (p : int) (t : tm) : string =
  let paren q s = if p > q then "(" ^ s ^ ")" else s in
  let under n e = "(" ^ String.make n '.' ^ " " ^ go 0 e ^ ")" in
  let app head parts =
    paren 3 (String.concat " " (head :: List.map (go 4) parts))
  in
  match t with
  | Var i -> "☐" ^ string_of_int i
  | Item (x, []) -> x
  | Item (x, es) -> x ^ "[" ^ String.concat ", " (List.rev_map (go 0) es) ^ "]"
  | Pi (a, b) -> paren 0 (go 1 a ^ " → " ^ go 0 b)
  | Lam b -> paren 0 ("λ. " ^ go 0 b)
  | App (f, a) -> paren 3 (go 3 f ^ " " ^ go 4 a)
  | Sigma (a, b) -> paren 1 (go 2 a ^ " × " ^ go 1 b)
  | Pair (a, b) -> "(" ^ go 0 a ^ ", " ^ go 0 b ^ ")"
  | Fst e -> go 4 e ^ " .π₁"
  | Snd e -> go 4 e ^ " .π₂"
  | Sum (a, b) -> paren 1 (go 2 a ^ " ⊎ " ^ go 2 b)
  | Inl a -> app "inj₁" [ a ]
  | Inr a -> app "inj₂" [ a ]
  | SumElim (l, r, e) ->
      paren 3 ("⊎-elim " ^ under 1 l ^ " " ^ under 1 r ^ " " ^ go 4 e)
  | Quot (a, r) -> paren 1 (go 2 a ^ " / " ^ under 2 r)
  | Class a -> app "class" [ a ]
  | QuotElim (f, q) -> paren 3 ("quot-elim " ^ under 1 f ^ " " ^ go 4 q)
  | Zero -> "𝟘"
  | ZeroElim e -> app "𝟘-elim" [ e ]
  | One -> "𝟙"
  | Unit -> "()"
  | Nat -> "ℕ"
  | Z -> "Z"
  | S n -> app "S" [ n ]
  | NatElim (z, s, n) ->
      paren 3 ("ℕ-elim " ^ go 4 z ^ " " ^ under 2 s ^ " " ^ go 4 n)
  | Eq (a, b, ty) -> paren 2 (go 3 a ^ " ≡ " ^ go 3 b ^ " ∈ " ^ go 3 ty)
  | Star -> "⋆"
  | Squash a -> "∥" ^ go 0 a ^ "∥"
  | Sort u -> sort u
  | Let (a, b) -> paren 3 ("let " ^ go 4 a ^ " " ^ under 2 b)
  | Nu f -> paren 3 ("ν " ^ poly 4 f)
  | Out e -> app "out" [ e ]
  | Corec (f, g, x) ->
      paren 3 ("corec " ^ poly 4 f ^ " " ^ under 1 g ^ " " ^ go 4 x)
  | QSort (sg, i, es) -> paren 3 (short sg ^ ".⬡" ^ string_of_int i ^ spine es)
  | QCon (sg, i, es) -> paren 3 (short sg ^ ".⬡" ^ string_of_int i ^ spine es)
  | QElim (sg, i, ms, es, w) ->
      paren 3
        (short sg ^ ".⬡" ^ string_of_int i ^ "-elim" ^ spine ms ^ spine es ^ " "
       ^ go 4 w)

and spine es =
  if es = [] then ""
  else "[" ^ String.concat ", " (List.rev_map (go 0) es) ^ "]"

and poly p (f : tm poly) : string =
  let paren q s = if p > q then "(" ^ s ^ ")" else s in
  match f with
  | PX -> "𝕏"
  | PK a -> paren 3 ("K " ^ go 4 a)
  | PProd (f, g) -> paren 1 (poly 2 f ^ " × " ^ poly 1 g)
  | PSum (f, g) -> paren 1 (poly 2 f ^ " ⊎ " ^ poly 2 g)
  | PSigma (a, f) -> paren 1 (go 2 a ^ " × (. " ^ poly 0 f ^ ")")
  | PPi (a, f) -> paren 0 (go 1 a ^ " → (. " ^ poly 0 f ^ ")")

(* a carried signature, by its size and level *)
and short (sg : tm signature) : string =
  "⟨"
  ^ string_of_int (List.length sg.entries)
  ^ "@" ^ string_of_int sg.level ^ "⟩"

and signature (sg : tm signature) : string =
  "⟨"
  ^ String.concat " ▷ " (List.rev_map qty sg.entries)
  ^ "⟩@" ^ string_of_int sg.level

and qty = function
  | QU -> "U"
  | QEl t -> "El " ^ qtm t
  | QExt (a, k) -> go 4 a ^ " ⇛ " ^ qty k
  | QInt (t, k) -> "El " ^ qtm t ^ " ⇛ " ^ qty k

and qtm = function
  | QVar i -> "⬡" ^ string_of_int i
  | QAppExt (t, a) -> "(" ^ qtm t ^ " " ^ go 4 a ^ ")"
  | QApp (t, u) -> "(" ^ qtm t ^ " " ^ qtm u ^ ")"
  | QLam t -> "(λ " ^ qtm t ^ ")"
  | QEq (t, u) -> "(" ^ qtm t ^ " ≡ " ^ qtm u ^ ")"

let tm t = go 0 t
