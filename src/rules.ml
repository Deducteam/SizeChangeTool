type pre_context   = Basic.ident array
type typed_context = (Basic.ident * Term.term) array

type rule_name = string

type 'a rule =
  { (** An identifier of the rule *)
    name : rule_name
  ; (** Head of the lhs *)
    head : Basic.name
  ; (** List of arguments of the lhs *)
    args : Term.term array
  ; (** Right-hand-side of the rule *)
    rhs  : Term.term
  ; (** Context containing the variables in the lhs with their types *)
    ctx  : 'a
  }

type pre_rule   = pre_context rule
type typed_rule = typed_context rule

let arity_of : Term.term -> int =
  let rec aux : int -> Term.term -> int =
    fun i ->
    function
    | Term.Pi(_, _, a, b) -> aux (i+1) b
    | _                   -> i
  in aux 0
