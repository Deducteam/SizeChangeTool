open Term
open Rules
open Sign
open Sizematrix
open Callgraph

let rec dig_in_rhs : term -> (int * Basic.name * term array) list =
  function
  | Kind
    | Type(_) -> assert false
  | DB(_,_,_) -> []
  | Const(_,f) -> [0, f, [||]]
  | App(Const(_,f),u,l) ->
     (0, f, Array.of_list (u::l))
     :: List.concat (List.map dig_in_rhs (u::l))
  | App(t,u,l) ->
     List.concat (List.map dig_in_rhs (t::u::l))
  | Lam(_,x,None,t) ->
     List.map (fun (i,b,c) -> (i+1,b,c)) (dig_in_rhs t)
  | Lam(_,x,Some ty,t) ->
     (dig_in_rhs ty) @ (List.map (fun (i,b,c) -> (i+1,b,c)) (dig_in_rhs t))
  | Pi(_,_,a,b) ->
     (dig_in_rhs a) @ (List.map (fun (i,b,c) -> (i+1,b,c)) (dig_in_rhs b))

let rec compare_term : int -> term -> term -> Cmp.t =
  fun i t_l t_r ->
  let rec comp_list : Cmp.t -> term list -> term list -> Cmp.t =
    fun cur lp lt ->
    match lp,lt with
    | [], _ | _, [] -> cur
    | a::l1, b::l2  ->
       begin
         match (compare_term i a b), cur with
	 | _   , Infi -> assert false
         (* We are sure, that the current state [cur] cannot contain a Infi, else the Infi would be the result of the function and no recursive call would be needed *)
         | Infi, _    -> Infi
         | Min1, _    -> comp_list Min1 l1 l2
      	 | _   , Min1 -> comp_list Min1 l1 l2
      	 | Zero, Zero -> comp_list Zero l1 l2
       end
  in
  match t_l,t_r with
  (* Two distinct variables are uncomparable *)
  | DB (_,_,n), DB (_,_,m)
  (* A variable when applied has the same size as if it was not applied *)
    | DB (_,_,n), App(DB(_,_,m),_,_)
    | App(DB (_,_,n),_,_), DB (_,_,m)
    | App(DB (_,_,n),_,_), App(DB(_,_,m),_,_) ->
     if n + i = m then Zero else Infi
  | Lam(_,_,_,DB(_,_,n)), DB(_,_,m)
    | Lam(_,_,_,App(DB(_,_,n),_,_)), DB(_,_,m)
    |  Lam(_,_,_,DB(_,_,n)), App(DB(_,_,m),_,_)
    |  Lam(_,_,_,App(DB(_,_,n),_,_)), App(DB(_,_,m),_,_) ->
     if n + i = m + 1 then Zero else Infi
  | App (Const(_,f),up,lp), App(Const(_,g),ut,lt) when f = g ->
     begin
       let res1 = comp_list Zero (up::lp) (ut::lt) in
       let res2 =
         Cmp.minus1 (
             Cmp.mini (
                 List.map (fun t_ll -> compare_term i t_ll t_r) (up::lp)
               )
           ) in
       Cmp.plus res1 res2
     end
  | App (_,u,l),_ ->
     Cmp.minus1
       (Cmp.mini (List.map (fun t_ll -> compare_term i t_ll t_r) (u::l)))
  | Lam(_,_,_,t_ll),Lam(_,_,_,t_rr) -> compare_term i t_ll t_rr
  | _ -> Infi


let study_call : signature -> index -> term array ->
                 int -> index -> term array -> Cmp_matrix.t =
  fun si fun_l arg_l nb fun_r arg_r ->
  let h = arity_of (find_symb si fun_l).typ in
  let w = arity_of (find_symb si fun_r).typ in
  let matrix : Cmp_matrix.t =
    {h; w; tab = Array.make_matrix h w Cmp.Infi} in
  for i=0 to (min h (Array.length arg_l)) -1
  do
    for j=0 to (min w (Array.length arg_r)) -1
    do
      matrix.tab.(i).(j) <- compare_term nb arg_l.(i) arg_r.(j)
    done
  done;
  matrix

(** Add the calls associated to a rule in the call graph *)
let add_rule : call_graph -> pre_rule -> call_graph =
  fun gr r ->
  let sign = gr.signature in
  let ind_l = find_symbol_index sign r.head in
  let new_calls = List.map
    (fun (i,n,a) ->
      let ind_r = find_symbol_index sign n in
      ind_r,study_call sign ind_l r.args i ind_r a
    ) (dig_in_rhs r.rhs)
  in
  { (List.fold_left
       (fun g (callee,matrix) ->
         add_call g {caller = ind_l; callee; matrix; rule_name=r.name }
       ) gr new_calls
    ) with signature = add_rule sign r
  }
