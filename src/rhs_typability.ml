open Basic
open Dk_export
open Sign

exception NotWS

(* [symbol_order si] contains a matrix such that [tab.(i).(j)=true} iff the [i]th symbol is smaller than the [j] *)
let symbol_order : signature -> Sizematrix.Bool_matrix.t =
  fun si ->
  let symbols = si.symbols in
  let rules = si.rules in
  let res = Sizematrix.Bool_matrix.diago si.next_symb in
  let update_symb_order i =
    term_iter
      (fun _ _ -> ())
      (fun g ->
        res.tab.(find_symbol_index si g).(i) <- true
      )
      ()
  in
  (* First [f] is bigger that every [g] occurring in its type *)
  IMap.iter
    (fun i f -> update_symb_order i f.typ)
    symbols;
  (* Then [f] is bigger than [g] if [f] calls [g] *)
  IMap.iter
    (fun i r ->
      update_symb_order (find_symbol_index si r.Rules.head) r.Rules.rhs;
      (*Array.iter
        (fun t -> update_symb_order (find_symbol_index si r.Rules.head) t)
        r.args*)
    )
    rules;
  Sizematrix.Bool_matrix.trans_clos res

let check_rhs_underf_typab : Callgraph.call_graph -> bool =
  let rec remove_pis : Term.term list -> Term.term -> Term.term =
    function
    | []    -> fun t -> t
    | a::tl ->
       function
       | Pi(_,_,_,b) -> remove_pis tl (Subst.subst b a)
       | _           -> failwith "Over-applying a lhs is not yet permitted"
  in
  fun gr ->
  let si = gr.signature in
  let symbols = si.symbols in
  let rules = si.rules in
  let sym_ord = symbol_order si in
  (* Check that [f] is strictly bigger that every [g] occurring in its type *)
  IMap.iter
    (fun i f ->
    term_iter
      (fun _ _ -> ())
      (fun g ->
        if sym_ord.tab.(i).(find_symbol_index si g)
         then raise NotWS
      )
      () f.typ)
    symbols;
  let partial_export_to_dk_large : Basic.name -> Signature.t =
    fun f ->
    let ind_f = find_symbol_index si f in
    ignore (Env.init (gr.mod_name^".dk"));
    let res = Env.get_signature () in
    IMap.iter
      (fun _ s ->
        if sym_ord.tab.(find_symbol_index si s.name).(ind_f)
        then
          Signature.add_declaration
            res dloc (id s.name) (Callgraph.definable gr s.name) (s.typ))
      symbols;
    IMap.iter
      (fun _ r ->
        if sym_ord.tab.(find_symbol_index si r.Rules.head).(ind_f)
        then
        try
          Signature.add_rules
            res [rule_info_of_pre_rule (mk_mident (gr.mod_name^".dk")) r]
        with
        | Signature.SignatureError e ->
            Errors.fail_env_error dloc (Env.EnvErrorSignature e)
      )
      rules;
    res
  in
  let check_rule : Rules.pre_rule -> bool =
    fun r ->
    let sig_loc_large = partial_export_to_dk_large r.head in
    let sub, tyr = type_rule r gr in
    let symb = IMap.find (find_symbol_index si r.Rules.head) symbols in
    let expected_typ = Subst.Subst.apply sub 0 (remove_pis (Array.to_list r.args) symb.typ) in
    try
      let ctx = List.map (fun (a,b) -> (dloc,a,b)) (Array.to_list tyr.ctx) in
      Typing.Default.check sig_loc_large ctx r.rhs expected_typ;
      true
    with
    | Typing.TypingError (ConvertibilityError(t,_,ty_exp,ty_inf)) ->
       Format.printf "%a has type %a, whether %a was inferred@." Term.pp_term t Term.pp_term ty_inf Term.pp_term ty_exp; false
    | _ -> assert false
  in
  let res = ref true in
  IMap.iter
    (fun _ r ->
      if not (check_rule r)
      then
        (res := false;
         let symb = IMap.find (find_symbol_index si r.Rules.head) symbols in
         update_result symb (RhsUntypable r.name)))
    rules;
  !res
