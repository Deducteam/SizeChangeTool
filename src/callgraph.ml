open Basic
open Sizematrix
open Sign

type Debug.flag += D_graph | D_call
let _ = Debug.register_flag D_graph "Call graph";
  Debug.register_flag D_call "Call generation"

module EdgeLabel = struct
  type t = (string list * Cmp_matrix.t) list

  let pp : t printer =
    fun fmt l ->
      Format.fprintf fmt "[%a]"
        (pp_list ",@." (fun fmt (a,b) -> Cmp_matrix.pp fmt b)) l

  let add_neutral : t = []

  let plus : t -> t -> t =
    let compare_cmp_matrix (m1 : Cmp_matrix.t) (m2 : Cmp_matrix.t) =
      assert (m1.h = m2.h);
      assert (m1.w = m2.w);
      let res = ref 0 in
      for i = 0 to m1.h -1 do
        for j = 0 to m1.w -1 do
          if !res = 0
          then
            res := Cmp.(match (m1.tab.(i).(j),m2.tab.(i).(j)) with
              | Infi, Infi -> 0
              | Infi, _    -> 1
              | _   , Infi -> -1
              | Zero, Zero -> 0
              | Zero, Min1 -> 1
              | Min1, Zero -> -1
              | Min1, Min1 -> 0)
        done
      done; !res in
    fun l1 l2 ->
      List.sort_uniq
        (fun (_,a) (_,b) -> compare_cmp_matrix a b) (List.append l1 l2)

  let mult : t -> t -> t =
    fun l1 l2 ->
      List.flatten (
        List.map (
          fun (r1,x) ->
            List.map (fun (r2,y) -> (r1@r2,Cmp_matrix.prod x y)) l2
        ) l1
      )
end

module CallGraphAdjMat = Matrix(EdgeLabel)

(** Internal state of the SCT, including the representation of symbols and the call graph. *)
type call_graph =
  { (** The signature of the system *)
    signature : Sign.signature
  ; (** The adjacence matrix of the call graph *)
    calls     : CallGraphAdjMat.t
  ; (** Module name *)
    mod_name  : string
  }

(** [new_graph mod_name] creates a new graph of name [mod_name] *)
let new_graph : string -> call_graph =
  fun mod_name ->
    { signature = new_signature ()
    ; calls     = CallGraphAdjMat.new_mat 0
    ; mod_name
    }

type call =
  { caller    : index
  ; callee    : index
  ; matrix    : Cmp_matrix.t
  ; rule_name : Rules.rule_name
  }

(** The pretty printer for the type [call]. *)
let pp_call : signature -> call printer=
  fun si fmt cc ->
    let res=ref "" in
    let h = cc.matrix.h -1 in
    for i=0 to h do
      res:=!res^"x"^(string_of_int i);
      if i < h then res := !res^" "
    done;
    Format.fprintf fmt "%a(%s%!) <- %a%!("
      pp_name (find_symb si cc.caller).name
      !res pp_name (find_symb si cc.callee).name;
    let jj=cc.matrix.h in
    if jj>0 then
      let ii=cc.matrix.w in
      for i = 0 to ii - 1 do
        if i > 0 then Format.fprintf fmt ",";
        let some = ref false in
        for j = 0 to jj - 1 do
          let c = cc.matrix.tab.(j).(i) in
          if c <> Cmp.Infi then
            begin
              let sep = if !some then " " else "" in
              Format.fprintf fmt "%s%s" sep (Cmp.cmp_to_string c);
              some := true
            end
        done
      done;
      Format.fprintf fmt ")"

(** Those functions modify the mutable fields in the symbol records *)
let update_result : call_graph -> index -> local_result -> unit =
  fun gr i res ->
    let sy = (IMap.find i gr.signature.symbols) in
    sy.result <- res::sy.result

(** Compute the transitive closure of a call_graph *)
let rec trans_clos : call_graph -> call_graph =
  fun gr ->
  let m = gr.calls in
  let mm = CallGraphAdjMat.sum m (CallGraphAdjMat.prod m m) in
  if m = mm
  then gr
  else trans_clos {gr with calls = mm}

(** Add a new call to the call graph.
    We maintain the transitive closure computed at each step. *)
let add_call : call_graph -> call -> call_graph =
  fun gr cc ->
  let si = gr.signature in
  Debug.debug D_graph "New call: %a" (pp_call si) cc;
  Debug.debug D_graph "The matrix is %a" Cmp_matrix.pp cc.matrix;
  (gr.calls).tab.(cc.caller).(cc.callee) <-
    ([cc.rule_name],cc.matrix) :: (gr.calls).tab.(cc.caller).(cc.callee);
  trans_clos gr

(** Add a new symb to the call graph *)
let add_symb : call_graph -> symbol -> call_graph =
  fun gr sy ->
  { signature = add_symb gr.signature sy
  ; calls     = CallGraphAdjMat.(add_line (add_column (gr.calls)))
  ; mod_name  = gr.mod_name }

let definable : call_graph -> name -> Signature.staticity =
  fun gr s ->
  let res = ref false in
  IMap.iter
    (fun _ r -> res := !res || (r.Rules.head = s))
    gr.signature.rules;
  if !res
  then Signature.Definable
  else Signature.Static
