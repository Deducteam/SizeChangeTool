(** Size change principle.
    This module implements a decision procedure based on the work of
Chin Soon Lee, Neil D. Jones and Amir M. Ben-Amram (POPL 2001).
    Most of this module comes from an implementation of Rodolphe Lepigre
    and Christophe Raffalli. *)
open Kernel
open Kernel.Basic
open Sizematrix
open Callgraph

let d_sct = Debug.register_flag "SCT"

(** the main function, checking if calls are well-founded *)
let check_sct : call_graph -> bool =
  let rec check_list : ('a list * Cmp_matrix.t) list -> 'a list =
    function
    | []      -> []
    | (x,m) :: tl ->
      begin
        if Cmp_matrix.decreasing m
        then check_list tl
        else
          if Cmp_matrix.is_idempotent m
          then x
          else check_list tl
        end
  in
  fun gr ->
    let nb_fun = gr.signature.next_symb in
    let res = ref true in
    for i = 0 to nb_fun -1 do
      let l = check_list gr.calls.tab.(i).(i) in
      if l != []
      then (
        (Sign.find_symb gr.signature i).result <-
          Sign.SelfLooping l :: (Sign.find_symb gr.signature i).result;
        res := false
      )
    done;
    !res
