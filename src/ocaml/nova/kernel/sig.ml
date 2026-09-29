(* The signature Σ: the items accepted so far, each closed over its own
   telescope (docs/NovaKernel.txt, the entry points). Only the entry
   points extend it. *)

open Core

type item = {
  tele : tm list; (* Δ, a snoc list of types, each over the ones below *)
  ty : tm; (* T, over Δ *)
  def : tm option; (* t, over Δ: a definition; None for a declaration *)
}

type t = (name * item) list

let empty : t = []

let find (sg : t) x =
  match List.assoc_opt x sg with
  | Some it -> it
  | None -> reject "unknown item '%s'" x

let add (sg : t) x it : t =
  if List.mem_assoc x sg then reject "item '%s' is already in Σ" x
  else (x, it) :: sg
