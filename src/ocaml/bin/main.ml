(* nova check [--fuel N] FILE…: read items in the proof language, check
   each against Σ so far, report it accepted (with its core) or
   rejected (with the kernel's message). Exit 1 if anything was
   rejected, 2 on a syntax error. *)

open Nova

let usage = "usage: nova check [--fuel N] FILE…"

let print_item (it : Parser.item) (k : Sig.item) =
  let params =
    List.rev
      (List.mapi
         (fun i (x, _) ->
           Printf.sprintf " (%s : %s)" x (Pretty.tm (List.nth k.tele i)))
         (List.rev it.params))
  in
  let def = match k.def with Some t -> " := " ^ Pretty.tm t | None -> "" in
  Printf.printf "accepted %s%s : %s%s\n" it.name (String.concat "" params)
    (Pretty.tm k.ty) def

let check_file ~fuel file =
  let src = In_channel.with_open_bin file In_channel.input_all in
  let base = Filename.basename file in
  match Parser.items src with
  | exception Lexer.Error (l, c, msg) ->
      Printf.printf "%s:%d:%d: %s\n" base l c msg;
      2
  | exception Parser.Error (l, c, msg) ->
      Printf.printf "%s:%d:%d: %s\n" base l c msg;
      2
  | items ->
      let sg = ref Sig.empty and status = ref 0 in
      List.iter
        (fun (it : Parser.item) ->
          let tele = List.rev_map snd it.params in
          match Check.check_item ~fuel !sg ~tele ~ty:it.ty ~def:it.def with
          | k -> (
              match Sig.add !sg it.name k with
              | sg' ->
                  sg := sg';
                  print_item it k
              | exception Core.Reject msg ->
                  Printf.printf "rejected %s (line %d): %s\n" it.name it.line
                    msg;
                  status := 1)
          | exception Core.Reject msg ->
              Printf.printf "rejected %s (line %d): %s\n" it.name it.line msg;
              status := 1)
        items;
      !status

let () =
  match Array.to_list Sys.argv with
  | _ :: "check" :: rest ->
      let rec go fuel files = function
        | "--fuel" :: n :: rest -> go (int_of_string n) files rest
        | f :: rest -> go fuel (f :: files) rest
        | [] -> (fuel, List.rev files)
      in
      let fuel, files = go 100_000 [] rest in
      if files = [] then (
        prerr_endline usage;
        exit 2);
      let status =
        List.fold_left (fun s f -> max s (check_file ~fuel f)) 0 files
      in
      exit status
  | _ ->
      prerr_endline usage;
      exit 2
