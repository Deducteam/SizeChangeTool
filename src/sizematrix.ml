open Basic

type Debug.flag += D_matrix
let _ = Debug.register_flag D_matrix "Call matrix"

(** Tools used for the matrices labeling edges in the call-graph studied by sizechange.ml *)

module type SemiRing = sig
  type t
  val pp          : t Basic.printer
  val add_neutral : t
  val plus        : t -> t -> t
  val mult        : t -> t -> t
end

module Matrix = functor (SR : SemiRing) -> struct
  type t = {h : int; w : int; tab : SR.t array array}

  (** The pretty printer for the type [matrix] *)
  let pp : t printer = fun fmt m ->
    Format.fprintf fmt "[[%a]]"
      (Basic.pp_arr "]\n [" (Basic.pp_arr "," SR.pp)) m.tab

  let sum : t -> t -> t =
    fun m1 m2 ->
      assert (m1.h = m2.h);
      assert (m1.w = m2.w);
      let tab = Array.init m1.h
        (fun y->
	   Array.init m1.w
             (fun x ->
                SR.plus m1.tab.(y).(x) m2.tab.(y).(x)
             )
        )
      in {h=m1.h; w=m1.w; tab}

  let prod : t -> t -> t =
    fun m1 m2 ->
      assert (m1.w = m2.h);
      (* The matrix must be compatible to perform product *)
      let tab = Array.init (m1.h)
        (fun y ->
	   Array.init (m2.w)
             (fun x ->
                let r = ref SR.add_neutral in
                for k = 0 to m1.w -1 do
	          r := SR.plus !r (SR.mult m1.tab.(y).(k) m2.tab.(k).(x))
                done; !r
             )
        ) in
      let mat = {h = m1.h; w = m2.w; tab} in
      mat

  (** Check if a matrix is square *)
  let is_idempotent : t -> bool =
    fun m ->
      assert (m.h = m.w);
      (* only square matrix can be idempotent *)
      m = (prod m m)

  (** Create a new square matrix of size [n] *)
  let new_mat : int -> t =
    fun n ->
      let tab= Array.init n (fun i -> Array.init n (fun j -> SR.add_neutral))
      in {h=n; w=n; tab}

  let add_line : t -> t =
    fun m ->
      {h = m.h+1; w = m.w;
        tab = Array.init (m.h +1)
                (fun i ->
                   Array.init m.w
                     (fun j ->
                        if i<m.h then m.tab.(i).(j) else SR.add_neutral
                     )
              )}

  let add_column : t -> t =
    fun m ->
      {h = m.h; w = m.w+1;
        tab = Array.init m.h
                (fun i ->
                   Array.init (m.w +1)
                     (fun j ->
                        if j<m.w then m.tab.(i).(j) else SR.add_neutral
                     )
                )}
end

module Cmp = struct
  (** Representation of the set {-1, 0, ∞} *)
  type t = Min1 | Zero | Infi

  (** String representation. *)
  let cmp_to_string : t -> string =
    function
    | Min1 -> "<"
    | Zero -> "="
    | Infi -> "?"

  (** The pretty printer for the type [cmp] *)
  let pp fmt c=
    Format.fprintf fmt "%s" (cmp_to_string c)

  let add_neutral = Infi

  (** Addition operation (minimum) *)
  let plus : t -> t -> t = fun e1 e2 ->
    match (e1, e2) with
    | (Min1, _   ) | (_, Min1) -> Min1
    | (Zero, _   ) | (_, Zero) -> Zero
    | (Infi, Infi)             -> Infi

  (** Multiplication operation. *)
  let mult : t -> t -> t = fun e1 e2 ->
    match (e1, e2) with
    | (Infi, _   ) | (_, Infi) -> Infi
    | (Min1, _   ) | (_, Min1) -> Min1
    | (Zero, Zero)             -> Zero

  (** Reduce by 1 a cmp *)
  let minus1 : t -> t =
    function
    | Zero -> Min1
    | n -> n

  (** Compute the minimum of a list *)
  let mini : t list -> t = fun l ->
    List.fold_left plus Infi l
end

module Cmp_matrix = struct
  include Matrix(Cmp)

  (** Check if a matrix corresponds to a decreasing idempotent call. *)
  let decreasing : t -> bool = fun m ->
    assert (m.h = m.w);
    (* Only square matrices labeling a self-looping arrow need to be study *)
    try
      for k = 0 to m.h-1 do
        if m.tab.(k).(k) = Cmp.Min1
        then raise Exit
      done;
      false
    with Exit -> true
end

(** Those bool matrices are relation matrices [plus (diago n) M] is the reflexive closure of [M] and [trans_clos M] is the transitive closure of [M] *)
module Bool_matrix = struct
  include
    Matrix(struct
        type t = bool
        let pp          : t Basic.printer =
          fun fmt b -> Format.fprintf fmt "%s" (if b then "T" else "F")
        let add_neutral : t = false
        let plus        : t -> t -> t = (||)
        let mult        : t -> t -> t = (&&)
      end)

  let diago : int -> t =
    fun n -> {h = n; w = n;
              tab = Array.init n (fun i -> Array.init n (fun j -> i=j))}

  let rec trans_clos : t -> t =
    fun m ->
    assert (m.h = m.w);
    let mm = sum m (prod m m) in
    if m = mm
    then m
    else trans_clos mm
end
