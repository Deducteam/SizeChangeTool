open Basic
open Term
open Entry
open Sign
open Callgraph
open Call_extractor

let str_of_name = string_of pp_name

let term_iter : (int -> ident -> unit) -> (name -> unit) -> unit -> term -> unit =
  fun f_var f_cst f_typ ->
  let rec aux =
    function
    | Kind               -> ()
    | Type _             -> f_typ
    | DB(_,x,i)          -> f_var i x
    | Const(_,f)         -> f_cst f
    | App(t,u,tl)        -> List.iter aux (t::u::tl)
    | Lam(_,_,None,t)    -> aux t
    | Lam(_,_,Some a, t) -> aux a; aux t
    | Pi(_,_,a,b)        -> aux a; aux b
  in aux

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
  let nb_vars : term list -> int =
    (* Caution, [max_list] requires the maximum to be a non-negative integer *)
    let max_list =
      let rec bis res=
        function
        | []    -> res
        | a::tl -> bis (max a res) tl
      in bis (-1)
    in
    let rec bis nb_lam res=
      function
      | []                        -> res
      | Const(_,f)::tl            -> bis 0 res tl
      | DB(_,_,n)::tl             -> bis 0 (max res (n+1-nb_lam)) tl
      | App(t0,t1,l2)::tl          ->
         max_list (List.map (fun t -> bis nb_lam res (t::tl)) (t0::t1::l2))
      | Lam(_,_,None,t)::tl   -> bis (nb_lam+1) res (t::tl)
      | Pi(_,_,t1,t2)::tl
        | Lam(_,_,Some t1,t2)::tl ->
         max (bis nb_lam res (t1::tl)) (bis (nb_lam+1) res (t2::tl))
      | _ -> assert false
    in bis 0 0
  in
  let ctx = Array.init (nb_vars l_args) (fun _ -> dmark) in
  {name; args; rhs = r.rhs; head = r.cst; ctx}

let rule_info_of_pre_rule : Rules.pre_rule -> Rule.rule_infos =
  fun r -> Rule.(
    let rule_name_conversion rn =
      Gamma (false,mk_name (mk_mident "") (mk_ident rn)) in
    let rec pattern_of_term =
      function
      | DB(l,id,n)             -> Var(l,id,n,[])
      | Const(l,nam)           -> Pattern(l,nam,[])
      | App(DB(l,id,n),u,tl)   -> Var(l,id,n,List.map pattern_of_term (u::tl))
      | App(Const(l,nam),u,tl) ->
         Pattern(l,nam,List.map pattern_of_term (u::tl))
      | Lam(l,id,_,t)          -> Lambda(l,id,pattern_of_term t)
      | _                      -> assert false
    in
    let pattern_of_pre_rule : Rules.pre_rule -> Rule.pattern =
      fun r ->
      Pattern(dloc,r.head,List.map pattern_of_term (Array.to_list r.args))
    in
    Format.printf "Le contexte est %a@." (pp_list "," pp_ident) (Array.to_list r.ctx);
    let ur = {
        name = rule_name_conversion r.name
      ; ctx = List.map (fun x -> dloc,x) (Array.to_list r.ctx)
      ; pat = pattern_of_pre_rule r
      ; rhs = r.rhs
      }
    in
    Format.printf "On arrive à définir ur@.";
    to_rule_infos ur)

let add_symb_name : call_graph -> Signature.symbol_infos -> call_graph =
  fun gr sy ->
  add_symb gr (new_symb sy.ident sy.ty)

let add_symb_rules : call_graph -> Signature.symbol_infos -> call_graph =
  fun gr sy ->
  let res = ref gr in
  List.iter (fun r -> res := add_rule !res (pre_rule_of_rinfos r)) sy.rules;
  !res

let dk_sig_to_callgraph : Signature.t -> call_graph =
  fun s ->
  let l = Signature.access_signature s in
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

let to_dk_signature : string -> entry list -> Signature.t =
  fun path entries ->
  let sg = Signature.make path in
  let md = Signature.get_name sg in
  let mk_entry = function
    | Decl(lc,id,st,ty) ->
       Signature.add_external_declaration sg lc (Basic.mk_name md id) st ty
    | Def(lc,id,op,Some ty,te) ->
       let open Rule in
       Signature.add_external_declaration sg lc (Basic.mk_name md id) Signature.Definable ty;
       let cst = Basic.mk_name md id in
       let rule = { name= Delta(cst) ; ctx = [] ; pat = Pattern(lc, cst, []); rhs = te } in
       Signature.add_rules sg [Rule.to_rule_infos rule]
    | Def(lc,id,op, None,te) ->
       Errors.fail_exit (-1) Basic.dloc "All the types should be given"
    | Rules(lc,rs) ->
       Signature.add_rules sg (List.map Rule.to_rule_infos rs)
    | Require(lc,md) -> Signature.import sg lc md
    | _ -> ()
  in
  List.iter mk_entry entries;
  sg

let export_to_dk : call_graph -> Signature.t =
  fun gr ->
  let res = Signature.make gr.mod_name in
  let si = gr.signature in
  IMap.iter
    (fun _ s ->
      Signature.add_declaration
        res dloc (id s.name) (definable gr s.name) (s.typ))
    si.symbols;
  Format.printf "On a les déclarations@.";
  IMap.iter
    (fun _ r ->
      Format.printf "On étudie %s@." r.Rules.name;
      Signature.add_rules
        res [rule_info_of_pre_rule r])
    si.rules;
  Format.printf "Et les règles@.";
  res

let type_rule : Rules.pre_rule -> Callgraph.call_graph ->
                Subst.Subst.t * Rules.typed_rule =
  fun r gr ->
  let s = export_to_dk gr in
  Format.printf " On a fait un export@.";
  let ri = rule_info_of_pre_rule r in
  Format.printf " On en a fait un rule_infos: %a@." Rule.pp_rule_infos ri;
  let tyr = Typing.typed_rule_of_rule_infos s ri in
  Format.printf " On a typé@.";
  fst tyr, {r with ctx = Array.of_list (List.map (fun (_,a,b) -> a,b) (snd tyr).ctx)}
