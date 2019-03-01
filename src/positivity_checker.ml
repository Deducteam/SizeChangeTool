open Basic
open Term
open Sizematrix
open Dk
open Sign

type constr_graph =
  { (** An array containing every type constructor and its status*)
    constructors   : name array
  ; (** The main order between type constructors *)
    typ_cstr_order : Bool_matrix.t
  }

(** [extract_constraints_of_typ t_arg] return the list of types which occur in positive position in [t_arg] and the list of types which occur in negative position in [t_arg]. *)
let extract_constraints_of_typ : int * term ->
                                 (int * term) list * (int * term) list =
  let rec extract_positive : int * term -> (int * term) list =
    function
    | _,Const(_,f)
      | _,App(Const(_,f),_,_) as t -> [t]
    | i,Pi(_,_,t1,t2)              ->
       (extract_negative (i,t1)) @ (extract_positive (i+1,t2))

    | _                            ->
       failwith "It is quite unexpected to have a type which is not a product of application of constants"
  and extract_negative : int * term -> (int * term) list =
    function
    | _,Const(_,f)
      | _,App(Const(_,f),_,_) -> []
    | i,Pi(_,_,t1,t2)         ->
       (extract_positive (i,t1)) @ (extract_negative (i+1,t2))
    | _                       ->
       failwith "It is quite unexpected to have a type which is not a product of application of constants"
  in
  fun t_arg -> (extract_positive t_arg,extract_negative t_arg)

let rec is_a_kind : term -> bool =
  function
  | Type _       -> true
  | Pi(_,_,_,t2) -> is_a_kind t2
  | _            -> false

(** [empty_cst_gr] construct an graph whose labels are type constructors and the orders are the reflexive relation. *)
let empty_cst_gr : symbol IMap.t -> constr_graph =
  fun m ->
  let l = ref [] in
  IMap.iter (fun _ f -> if is_a_kind f.typ then l:=f.name::!l) m;
  let constructors = Array.of_list !l in
  let lg = Array.length constructors in
  { constructors;
    typ_cstr_order = Bool_matrix.diago lg}

(** [accessed r] lists all the accessed position under a constructor in the rules. *)
let accessed : Rules.pre_rule -> (Rules.rule_name * name * int) list =
  fun r ->
  let used_variables : term -> int list =
    let rec bis : int list -> int -> term -> int list =
      fun acc i ->
      function
      | Kind
        | Type _
        | Const _           -> acc
      | DB(_,_,j)           -> if i<j then (j-i)::acc else acc
      | App(t1,t2,l)        -> List.flatten (List.map (bis acc i) (t1::t2::l))
      | Lam(_,_,None,t)     -> bis acc (i+1) t
      | Lam(_,_,Some t1,t2)
        | Pi(_,_,t1,t2)     -> (bis acc i t1) @ (bis acc (i+1) t2)
    in bis [] 0
  in
  (* [list_of_access vars args] returns the list of constructors under which you have to go to find the first occurrence of each variable whose index is listed in [vars] *)
  let list_of_access : int list -> term list -> (Rules.rule_name * name * int) list =
    let rec bis glob_acc loc_acc i used =
      function
      | []                         -> glob_acc
      | Kind :: tl
        | Type _ :: tl
        | Const _ :: tl            -> bis glob_acc [] 0 used tl
      | DB(_,_,j) :: tl            ->
         if List.mem (j-i) used
         then
           bis (loc_acc @ glob_acc) [] 0
             (List.filter (fun x -> x <> (j-i)) used) tl
         else
           bis glob_acc [] 0 used tl
      | App(Const(_,f),t2,l) :: tl ->
         let index = ref 0 in
         List.flatten
           (List.map
              (fun t ->
                incr index;
                bis glob_acc ((r.name,f,!index)::loc_acc) i used (t::tl)
              )
              (t2::l)
           )
      | App(t1,t2,l) :: tl         ->
         List.flatten
           (List.map
              (fun t -> bis glob_acc loc_acc i used (t::tl))
              (t1::t2::l)
           )
      | Lam(_,_,None,t) :: tl      -> bis glob_acc loc_acc (i+1) used (t::tl)
      | Lam(_,_,Some t1,t2) ::tl
        | Pi(_,_,t1,t2) :: tl      ->
         (bis glob_acc loc_acc i used (t1::tl))
         @ (bis glob_acc loc_acc (i+1) used (t2::tl))
    in bis [] [] 0
  in
  let used_vars = List.sort_uniq compare (used_variables r.rhs) in
  list_of_access used_vars (Array.to_list r.args)

(* Transform the contraint of accessibility into pait of types which must be compare. (Rules.rule_name and name are kept for error messages). *)
let get_ith_arg_and_return : Sign.signature -> (Rules.rule_name * name * int)
                     -> (Rules.rule_name * name * (int * term) * (int * term)) =
  let rec get_return : int -> term -> int * term =
    fun i ->
    function
    | Pi(_,_,_,t) -> get_return (i+1) t
    | u           -> (i,u)
  in
  let rec get_ith : int -> int -> term -> int * term =
    fun i remain t ->
    match (remain,t) with
    | 0,Pi(_,_,t1,_) -> (i,t1)
    | i,Pi(_,_,_,t2) -> get_ith i (remain-1) t2
    | _              -> failwith "Over-applied symbol in the lhs"
  in
  fun si (r,f,i) ->
  let symbols = si.symbols in
  let s = IMap.find (find_symbol_index si f) symbols in
  let tt = s.typ in
  r,f,get_ith i i tt,get_return 0 tt

let find_array : 'a -> 'a array -> int =
    let rec bis : int -> 'a -> 'a list -> int =
      fun i x ->
      function
      | []            -> raise Not_found
      | a::_ when a=x -> i
      | _::tl         -> bis (i+1) x tl
    in
    fun x arr -> bis 0 x (Array.to_list arr)

let compute_main_order : (Rules.rule_name * name * (int * term) * (int * term)) list
                         -> constr_graph -> unit =
  fun acc cst_gr ->
  let cons = cst_gr.constructors in
  List.iter
    (fun (_,_,ti,(_,tr)) ->
      let lpos,lneg = extract_constraints_of_typ ti in
      List.iter
        ( fun (_,t) ->
          match t,tr with
          | Const(_,f), Const(_,g)
            | App(Const(_,f),_,_), Const(_,g)
            | Const(_,f), App(Const(_,g),_,_)
            | App(Const(_,f),_,_), App(Const(_,g),_,_) ->
             let i_f = find_array f cons in
             let i_g = find_array g cons in
             cst_gr.typ_cstr_order.tab.(i_f).(i_g) <- true
          | _ -> failwith "Unexpected types"
        ) (lpos@lneg)
    ) acc

let main_order_type_level_rules : Callgraph.call_graph -> constr_graph -> unit =
  fun gr cst_gr ->
  let si = gr.signature in
  let rec study i =
    function
    | Pi(_,_,t1,t2) -> study i t1; study i t2
    | Const(_,f)
      | App(Const(_,f),_,_) -> cst_gr.typ_cstr_order.tab.(find_array f cst_gr.constructors).(i) <- true
    | _ -> failwith "Unexpected types"
  in
  IMap.iter
    (fun _ r ->
      let tt = (IMap.find (find_symbol_index si r.Rules.head) si.symbols).typ in
      if is_a_kind tt
      then
        study (find_array r.Rules.head cst_gr.constructors) r.Rules.rhs
    )
    si.rules


let rec comp_list : (int * term) list -> (int * term) list -> bool =
  fun l1 l2 ->
  match l1,l2 with
  | [], [] -> false
  | [], _  -> true
  | _, []  -> false
  | (i1,a)::l1,(i2,b)::l2 ->
     match Call_extractor.compare_term (i2-i1) a b with
     | Infi -> false
     | Zero -> comp_list l1 l2
     | Min1 -> true
  
let verify_pos_type_level_rules : Callgraph.call_graph -> constr_graph -> bool =
  fun gr cst_gr ->
  let si = gr.signature in
  let cons = cst_gr.constructors in
  let main = cst_gr.typ_cstr_order.tab in
  let res = ref true in
  IMap.iter
    (fun _ r ->
      let symb = IMap.find (find_symbol_index si r.Rules.head) si.symbols in
      let tt = symb.typ in
      if is_a_kind tt
      then
        let i = find_array r.head cons in
        let _,lneg = extract_constraints_of_typ (0,tt) in
        List.iter
          ( fun (j,t) ->
            match t with
            | Const(_,f) ->
               let i_f = find_array f cons in
               let comp = main.(i).(i_f) in
               if comp then
                 if Array.length r.args = 0 then
                   (res := false;
                    update_result symb (NotPositive r.name))
            | App(Const(_,f),t1,l1) ->
               let i_f = find_array f cons in
               let comp = main.(i).(i_f) in
               if comp then
                 let res_bis =
                   comp_list
                     (List.map (fun x -> j,x) (t1::l1))
                     (List.map (fun x -> 0,x) (Array.to_list r.args))
                 in
                 if not res_bis
                 then
                   (res := false;
                    update_result symb (NotPositive r.name))
            | _ -> failwith "Unexpected types"
          ) lneg;
    )
    si.rules;
  !res
  
let is_mkable_pos : (Rules.rule_name * name * (int * term) * (int * term)) ->
                             signature -> constr_graph -> bool =
  fun (r,c,(i1,ti),(i2,tr)) si cst_gr ->
  let cons = cst_gr.constructors in
  let main = cst_gr.typ_cstr_order.tab in
  let _,lneg = extract_constraints_of_typ (i1,ti) in
  let res = ref true in
  List.iter
    ( fun (i,t) ->
      match t,tr with
      | Const(_,f), Const(_,g)
        | App(Const(_,f),_,_), Const(_,g)             ->
         let i_f = find_array f cons in
         let i_g = find_array g cons in
         let comp = main.(i_g).(i_f) in
         if comp then
           (res := false;
            update_result
              (IMap.find (find_symbol_index si c) si.symbols)
              (NotPositive r))
      | Const(_,f), App(Const(_,g),_,_)              -> ()
      | App(Const(_,f),t1,l1), App(Const(_,g),t2,l2) ->
         let i_f = find_array f cons in
         let i_g = find_array g cons in
         let comp = main.(i_g).(i_f) in
         if comp then
           let res_bis =
             comp_list
               (List.map (fun x -> i,x) (t1::l1))
               (List.map (fun x -> i2,x) (t2::l2))
           in
           if not res_bis
           then
             (res := false;
              update_result
                (IMap.find (find_symbol_index si c) si.symbols)
                (NotPositive r))
      | _ -> failwith "Unexpected types"
    ) lneg;
  !res

let check_positivity : Callgraph.call_graph -> bool =
(* TODO : Il manque les règles au niveau type. *)
  fun gr ->
  let si = gr.signature in
  let cst_gr = empty_cst_gr si.symbols in
  let acc_name = ref [] in
  IMap.iter
    (fun _ r -> acc_name := (accessed r)::!acc_name)
    si.rules;
  let acc = List.map (get_ith_arg_and_return si) (List.flatten !acc_name) in
  compute_main_order acc cst_gr;
  main_order_type_level_rules gr cst_gr;
  let res = ref true in
  res := verify_pos_type_level_rules gr cst_gr;
  List.iter
    (fun r ->
      res:= !res && (is_mkable_pos r si cst_gr)
    ) acc;
  !res
