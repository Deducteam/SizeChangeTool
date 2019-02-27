open Basic
open Term
open Sizematrix
open Dk
open Sign

type constr_graph =
  { (** An array containing every type constructor and its status*)
    constructors   : (name * int list) array
  ; (** The main order between type constructors *)
    typ_cstr_order : Bool_matrix.t
  ; (** A refined version of the order between type constructors *)
    refined_order  : Bool_matrix.t
  }

(** [extract_constraints_of_typ t_arg] return the list of types which occur in positive position in [t_arg] and the list of types which occur in negative position in [t_arg]. *)
let extract_constraints_of_typ : term -> term list * term list =
  let rec extract_positive : term -> term list =
    function
    | Const(_,f)
      | App(Const(_,f),_,_) as t-> [t]
    | Pi(_,_,t1,t2)             -> (extract_negative t1) @ (extract_positive t2)
    | _                         -> failwith "It is quite unexpected to have a type which is not a product of application of constants"
  and extract_negative : term -> term list =
    function
    | Const(_,f)
      | App(Const(_,f),_,_) -> []
    | Pi(_,_,t1,t2)         -> (extract_positive t1) @ (extract_negative t2)
    | _                     -> failwith "It is quite unexpected to have a type which is not a product of application of constants"
  in
  fun t_arg -> (extract_positive t_arg,extract_negative t_arg)

let empty_cst_gr : symbol IMap.t -> constr_graph =
  fun m ->
  (* TODO *)
  { constructors = [||]; typ_cstr_order = Bool_matrix.diago 0; refined_order  = Bool_matrix.diago 0 }

let study_typ_level_rules : Sign.signature -> constr_graph -> constr_graph =
  fun si cst_gr ->
  (* TODO *)
  cst_gr

let accessed : Rules.typed_rule -> (Rules.rule_name * name * int) list =
  (* TODO *)
  fun r -> []

let get_ith_arg_and_return : Sign.signature -> (Rules.rule_name * name * int) -> (Rules.rule_name * name * term * term) =
  fun si (r,f,i) ->
  (* TODO *)
  r,f,mk_Kind,mk_Kind

let compute_main_order : (Rules.rule_name * name * term * term) list -> constr_graph -> constr_graph =
  fun acc cst_gr ->
  (* TODO *)
  cst_gr

let mk_secondary_order_consistent : constr_graph -> constr_graph =
  fun cstr_gr ->
  (* TODO *)
  cstr_gr

let is_mkable_pos : (Rules.rule_name * name * term * term) -> constr_graph -> constr_graph * bool =
  fun (r,f,t1,t2) gr ->
  (* TODO *)
  gr,true

let check_positivity : Callgraph.call_graph -> bool =
  fun gr ->
  let si = gr.signature in
  let cst_gr = ref (empty_cst_gr si.symbols) in
  cst_gr := study_typ_level_rules si !cst_gr;
  let acc_name = ref [] in
  IMap.iter (fun _ r -> acc_name := (accessed (snd (type_rule r gr)))::!acc_name) si.rules;
  let acc = List.map (get_ith_arg_and_return si) (List.flatten !acc_name) in
  cst_gr := compute_main_order acc !cst_gr;
  cst_gr := mk_secondary_order_consistent !cst_gr;
  let res = ref true in
  List.iter (fun r -> res:= !res && (let a,b = is_mkable_pos r !cst_gr in cst_gr :=a; b)) acc;
  !res
