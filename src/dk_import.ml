open Basic
open Term
open Sign
open Callgraph
open Call_extractor

let str_of_name = string_of pp_name

let pre_rule_of_rinfos : Rule.rule_infos -> Rules.pre_rule =
  fun r ->
  let name =
    match r.name with
    | Rule.Beta       -> "β"
    | Rule.Delta(s)   -> Format.asprintf "Def of %s" (str_of_name s)
    | Rule.Gamma(_,s) -> Format.asprintf "Rule %s" (str_of_name s)
  in
  let l_args = List.map Rule.pattern_to_term r.args in
  let args = Array.of_list l_args in
  let nb_vars : term list -> int * (int * ident) list =
    (* Caution, [max_list] requires the maximum to be a positive integer *)
    let max_list_fst =
      let rec bis res=
        function
        | []    -> res
        | a::tl -> bis (max (fst a) res) tl
      in bis 0
    in
    let rec bis nb_lam res=
      function
      | []                        -> res
      | Const(_,f)::tl            -> bis 0 res tl
      | DB(_,id,n)::tl             ->
         bis 0 (max (fst res) (n+1-nb_lam),(n-nb_lam,id)::(snd res)) tl
      | App(t0,t1,l2)::tl          ->
         let ll = List.map (fun t -> bis nb_lam res (t::tl)) (t0::t1::l2) in
         max_list_fst ll, List.flatten (List.map snd ll)
      | Lam(_,_,None,t)::tl   -> bis (nb_lam+1) res (t::tl)
      | Pi(_,_,t1,t2)::tl
        | Lam(_,_,Some t1,t2)::tl ->
         max (bis nb_lam res (t1::tl)) (bis (nb_lam+1) res (t2::tl))
      | _ -> assert false
    in bis 0 (0,[])
  in
  let nb, lass = nb_vars l_args in
  let ctx = Array.init nb (fun i -> List.assoc i lass) in
  {name; args; rhs = r.rhs; head = r.cst; ctx}

let add_symb_name : call_graph -> Signature.symbol_infos -> call_graph =
  fun gr sy ->
  add_symb gr (new_symb (fst sy) (snd sy).ty)

let add_symb_rules : call_graph -> Signature.symbol_infos -> call_graph =
  fun gr sy ->
  let res = ref gr in
  List.iter (fun r -> res := add_rule !res (pre_rule_of_rinfos r)) (snd sy).rules;
  !res

let dk_sig_to_callgraph : Signature.t -> call_graph =
  fun s ->
  let l = Signature.symbols_of s in
  let rec enrich_symb gr =
    function
    | []    -> gr
    | a::tl -> enrich_symb (add_symb_name gr a) tl
  in
  let rec enrich_rules gr =
    function
    | []    -> gr
    | a::tl -> enrich_rules (add_symb_rules gr a) tl
  in
  enrich_rules
    (enrich_symb (new_graph (string_of_mident (Signature.get_name s))) l)
    l
