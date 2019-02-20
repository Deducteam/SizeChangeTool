open Basic

type Debug.flag += D_sign
let _ = Debug.register_flag D_sign "Signature"

(** The local result express the result of the termination checker for this symbol *)
type local_result =
  (** If a call from a symbol to itself lead to potentially non-terminating sequence *)
  | SelfLooping  of Rules.rule_name list
  (** Variables at non-positive position under this constructor are accessed *)
  | NotPFP  of Rules.rule_name
  (** The rhs of this rule is not typable without adding constraints inferred from the lhs *)
  | RhsUntypable of Rules.rule_name
  (** The lhs of this rule has too many arguments compared to the declared type of the head symbol. *)
  | LhsOverApplied of Rules.rule_name

(** The pretty printer for the type [local_result] *)
let pp_local_result : local_result printer =
  fun fmt lr ->
    let st =
      match lr with
      | SelfLooping _    -> "self looping"
      | NotPFP _         -> "not PFP"
      | RhsUntypable _   -> "rhs is untypable"
      | LhsOverApplied _ -> "lhs over applied"
    in
    Format.fprintf fmt "%s" st

type symbol =
  { (** Identifier of the symbol *)
    name           : name
  ; (** Type of the symbol *)
    typ            : Term.term
  ; (** The information about non termination for this symbol, initially empty *)
    mutable result : local_result list
  }

let new_symb : name -> Term.term -> symbol =
  fun name typ -> {name; typ; result = []}

let update_result : symbol -> local_result -> unit =
  fun sy res -> sy.result <- res::sy.result

(** Index of a rule. *)
type index = int

(** Conversion to int. *)
let int_of_index : index -> int =
  fun i -> i

(** The pretty printer for the type [index] *)
let pp_index fmt x =
  Format.pp_print_int fmt (int_of_index x)

(** Map with index as keys. *)
module IMap =
  struct
    include Map.Make(
      struct
        type t = index
        let compare = compare
      end)

    (** The exception [Success_index] is here only to reverse the [IMap] *)
    exception Success_index  of index

    (** [find_key map f] will return a key [k] which is mapped to an element [n] such that [f n = true] *)
    let find_key : 'a t -> ('a -> bool) -> index =
      fun map f ->
      try
        iter
          (
	    fun k x -> if f x then raise (Success_index k)
          ) map;
        raise Not_found
      with Success_index k -> k
  end

(** Type for the signature *)
type signature =
  { (** An index for the next symbol to be added *)
    next_symb : index
  ; (** A map containing every symbol studied *)
    symbols   : symbol IMap.t
  ; (** An index for the next rule to be added *)
    next_rule : index
  ; (** A map containing every rule studied *)
    rules     : Rules.pre_rule IMap.t
  }

let new_signature : unit -> signature =
  fun () ->
  { next_symb = 0
  ; symbols   = IMap.empty
  ; next_rule = 0
  ; rules     = IMap.empty
  }

let find_symb : signature -> index -> symbol =
  fun s i ->
  (IMap.find i s.symbols)

(** [find_symbol_index s n] will return the index [k] which is mapped to the symbol [n] in the signature [s] *)
let find_symbol_index : signature -> name -> index =
  fun s n ->
    IMap.find_key (s.symbols) (fun x -> x.name = n)

(** [find_rule_index s r] will return the index [k] which is mapped to the rule [r] in the signature [s] *)
let find_rule_index : signature -> Rules.rule_name -> index =
  fun s r ->
    IMap.find_key (s.rules) (fun x -> x.name = r)

(** Add a new symbol to the call graph *)
let add_symb : signature -> symbol -> signature =
  fun s sy ->
  let next = s.next_symb in
  Debug.debug D_sign "We add the symbol (%i,%a)" next pp_name (sy.name);
  { s with next_symb = next + 1; symbols = IMap.add next sy (s.symbols)}

(** Add a new rule to the call graph *)
let add_rule : signature -> Rules.pre_rule -> signature =
  fun s r ->
  let next = s.next_rule in
  Debug.debug D_sign "We add the rule (%i,%s)" next (r.name);
  { s with next_rule = next + 1; rules = IMap.add next r (s.rules)}
