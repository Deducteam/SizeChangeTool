open Rules
open Sign
   
let check_lh_arity : signature -> bool =
  fun s ->
  let symbols = s.symbols in
  let res = ref true in
  let treat_rule : pre_rule -> unit =
    fun r ->
    let sy =
      IMap.find (IMap.find_key symbols (fun x -> x.name = r.head)) symbols in
    if Array.length r.args > arity_of sy.typ
    then (res := false; update_result sy (LhsOverApplied r.name))
  in
  IMap.iter (fun _ r -> treat_rule r) s.rules;
  !res
