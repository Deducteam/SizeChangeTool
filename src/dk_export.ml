open Kernel
open Kernel.Basic
open Kernel.Term
open Sign
open Callgraph
open Call_extractor

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

let rule_info_of_pre_rule : mident -> Rules.pre_rule -> Rule.rule_infos =
  fun md r -> Rule.(
    let rule_name_conversion rn =
      Gamma (false,mk_name md (mk_ident rn)) in
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
      ; ctx = List.map (fun x -> dloc,x,None) (Array.to_list r.ctx)
      ; pat = pattern_of_pre_rule r
      ; rhs = r.rhs
      }
    in
    to_rule_infos ur)

let to_dk_signature : string -> Parsing.Entry.entry list -> Signature.t =
  fun path entries ->
  ignore (Api.Env.Default.init path);
  let sg = Api.Env.Default.get_signature () in
  let mk_entry = function
    | Parsing.Entry.Decl(lc,id,scope,stat,ty) ->
       Api.Env.Default.declare lc id scope stat ty
    | Parsing.Entry.Def(lc,id,scope,op,ty_opt,te) ->
       Api.Env.Default.define lc id scope op te ty_opt
    | Parsing.Entry.Rules(lc,rs) -> ignore (Api.Env.Default.add_rules rs)
    | Parsing.Entry.Require(lc,md) -> Signature.import sg lc md
    | _ -> ()
  in
  List.iter mk_entry entries;
  sg

let export_to_dk : call_graph -> Signature.t =
  fun gr ->
  ignore (Api.Env.Default.init (gr.mod_name^".dk"));
  let res = Api.Env.Default.get_signature () in
  let si = gr.signature in
  IMap.iter
    (fun _ s ->
      Signature.add_declaration
        res dloc (id s.name) Signature.Public (definable gr s.name) (s.typ))
    si.symbols;
  IMap.iter
    (fun _ r ->
      Signature.add_rules
        res [rule_info_of_pre_rule (mk_mident (gr.mod_name^".dk")) r])
    si.rules;
  res

let type_rule : Rules.pre_rule -> Callgraph.call_graph ->
                Exsubst.ExSubst.t * Rules.typed_rule =
  fun r gr ->
  let s = export_to_dk gr in
  let ri = rule_info_of_pre_rule (mk_mident (gr.mod_name^".dk")) r in
  let arit_r = Rule.untyped_rule_of_rule_infos ri in
  let untyp_r = {arit_r with ctx = List.map (fun (a,b,_) -> a,b,None) arit_r.ctx} in
  let tyr = Typing.Default.check_rule s untyp_r in
  fst tyr, {r with ctx = Array.of_list (List.map (fun (_,a,b) -> a,b) (snd tyr).ctx)}
