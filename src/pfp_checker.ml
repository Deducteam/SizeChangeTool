open Term
open Sign
open Dk

let is_pfp : Rules.pre_rule -> Callgraph.call_graph -> bool =
  (* [is_plain args i] is true if one of the element of [args] is the variable of index [i] *)
  let is_plain : term array -> int -> bool =
    fun args i ->
    Array.exists (fun x -> match x with | DB(_,_,j) -> i=j | _ -> false) args
  in
  let is_fo : Rules.typed_rule -> Callgraph.call_graph -> int -> bool =
    fun r gr i ->
    match snd (r.ctx.(i)) with
    | Const(_,f)
      | App(Const(_,f),_,_) -> Callgraph.definable gr f = Static
    | _                     -> false
  in
  fun r gr ->
  let symbols = gr.signature.symbols in
  let res = ref true in
  term_iter
    (fun i _ ->
      if not ((is_plain r.args i) || (is_fo (snd (type_rule r gr)) gr i))
      then
        (res:= false;
         let sy =
           IMap.find
             (IMap.find_key symbols (fun x -> x.name = r.head))
             symbols in
         update_result sy (NotPFP r.name)))
    (fun _ -> ()) () r.rhs;
  !res

let check_pfp : Callgraph.call_graph -> bool =
  fun gr ->
  let res = ref true in
  IMap.iter (fun _ r -> res:= !res && is_pfp r gr) gr.signature.rules;
  !res
