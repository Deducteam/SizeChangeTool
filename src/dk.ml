open Basic
open Term
open Entry
open Sign
open Callgraph
open Call_extractor

let str_of_name = string_of pp_name
let mod_export = "sct_export"

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
  let args = Array.of_list (List.map Rule.pattern_to_term r.args) in
  let ctx = Array.init r.esize (fun _ -> dmark) in
  {name; args; rhs = r.rhs; head = r.cst; ctx}

let rule_info_of_pre_rule : Rules.pre_rule -> Rule.rule_infos =
  fun r -> Rule.(
    let rule_name_conversion rn =
      Gamma (false,mk_name (mk_mident mod_export) (mk_ident rn)) in
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
    let ur = {
        name = rule_name_conversion r.name
    ; ctx = List.map (fun x -> dloc,x) (Array.to_list r.ctx)
    ; pat = pattern_of_pre_rule r
    ; rhs = r.rhs
    }
    in
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
  enrich_rules (enrich_symb (new_graph ()) l) l

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
  let res = Signature.make "sct_export" in
  let si = gr.signature in
  IMap.iter
    (fun _ s ->
      Signature.add_declaration
        res dloc (id s.name) (definable gr s.name) (s.typ))
    si.symbols;
  IMap.iter
    (fun _ r ->
      Signature.add_rules
        res [rule_info_of_pre_rule r])
    si.rules;
  res

let type_rule : Rules.pre_rule -> Callgraph.call_graph ->
                Subst.Subst.t * Rules.typed_rule =
  fun r gr ->
  let s = export_to_dk gr in
  let ri = rule_info_of_pre_rule r in
  let tyr = Typing.typed_rule_of_rule_infos s ri in
  fst tyr, {r with ctx = Array.of_list (List.map (fun (_,a,b) -> a,b) (snd tyr).ctx)}
