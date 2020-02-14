open Kernel.Basic

let export_dk_file : bool ref = ref false

module SString=Set.Make(struct
    type t=string
    let compare= compare
  end)

let parenthesis s=
  if String.contains s ' '
  then "("^s^")"
  else s

let replace c esc s =
  String.concat esc (String.split_on_char c s)

let escaped_char=['/',"_slash_" ; '+',"_plus_" ; '*',"_times_" ;
                  '%',"_percent_" ; '-',"_minus_" ; '#',"_sharp_" ;
                  '$',"_dollar_" ; '@',"_at_" ; ':',"_colon_" ;
                  '\\',"_backslash_" ; '.',"_dot_" ;
                  '<',"_less_than_" ; '>',"_greater_than_" ;
                  '=',"_equal_"
                 ]

let normalise s=
  List.fold_left (fun x (c,esc) -> replace c esc x) s escaped_char

let pp_couple sep pp1 pp2 fmt x =
  Format.fprintf fmt "%a%s%a" pp1 (fst x) sep pp2 (snd x)

let format_of_sep str fmt () : unit = Format.fprintf fmt "%s" str

let pp_list sep pp fmt l = Format.pp_print_list ~pp_sep:(format_of_sep sep) pp fmt l

let pp_sstring sep pp fmt s = pp_list sep pp fmt (SString.elements s)

let rec pp_xml fmt = function
  | Xml.Element(s,l,ll) ->
    Format.fprintf fmt "Element %s,[%a] , [%a] @."
      s
      (pp_list ";"
         (pp_couple "," Format.pp_print_string Format.pp_print_string)
      ) l
      (pp_list ";" pp_xml) ll
  | Xml.PCData(s) -> Format.fprintf fmt "PCData %s" s

let rec get_vars = function
  | Xml.Element(s,[],(Xml.PCData x)::[]) when s="var" ->
    SString.singleton(normalise x)
  | Xml.Element(s,l,ll) when s="var" -> failwith "So many argument in var !"
  | Xml.Element(s,l,(Xml.Element(v,[],(Xml.PCData y)::[])::b::ll))
    when s="lambda" && v="var"->
    SString.remove (normalise y)
      (List.fold_left SString.union SString.empty  (List.map get_vars ll))
  | Xml.Element(s,l,ll) ->
    List.fold_left SString.union SString.empty  (List.map get_vars ll)
  | Xml.PCData(s) -> SString.empty

let rec get_types = function
  | Xml.Element(s,[],(Xml.PCData x)::[]) when s="basic" ->
    SString.singleton((normalise x)^"_Type")
  | Xml.Element(s,l,ll) when s="basic" ->
    failwith "So many argument in basic !"
  | Xml.Element(s,l,ll) ->
    List.fold_left SString.union SString.empty  (List.map get_types ll)
  | Xml.PCData(s) -> SString.empty

let rec eta_expand k t=
  if k<=0
  then t
  else
    let v="new_var_"^(string_of_int k) in
    eta_expand (k-1) ("("^v^" => "^t^" "^v^")")

let var_arity = ref []

type location = Type | Rhs of int | Lhs of int

let add_one : location -> location =
  function
  | Type  -> Type
  | Rhs i -> Rhs (i+1)
  | Lhs i -> Lhs (i+1)

let nul_loc : location -> location =
  function
  | Type  -> Type
  | Rhs i -> Rhs 0
  | Lhs i -> Lhs 0

let rec get_local_type = function
  | Xml.Element(s,[],[]) when s="TYPE" -> "Type"
  | Xml.Element(s,l,ll) when s="TYPE" ->
     failwith "Unexpected arguments in <Type />"
  | Xml.Element(s,[],a::[]) when s="type" -> get_local_type a
  | Xml.Element(s,l,ll) when s="type" ->
    failwith "So many argument in type !"
  | Xml.Element(s,[],a::b::[]) when s="arrow" ->
    "("^(get_local_type a)^"->"^(get_local_type b)^")"
  | Xml.Element(s,[],Xml.Element(s2,[],(Xml.PCData var)::[])::a::b::[])
       when (s="arrow" && s2="var") ->
    "(("^(normalise var)^":"^(get_local_type a)^")->"^(get_local_type b)^")"
  | Xml.Element(s,l,ll) when s="arrow" ->
    failwith "So many argument in arrow !"
  | Xml.Element(s,[],(Xml.PCData x)::[]) when s="basic" ->
    (normalise x)^"_Type"
  | Xml.Element(s,l,ll) when s="basic" ->
     failwith "So many argument in basic !"
  | Xml.Element(s,[],ll) when s="funapp" ->
      begin
        let res=ref "" in
        List.iter
          (fun x ->
             let sep = (if !res="" then "" else " ") in
             res:=!res^sep^(parenthesis (get_term Type x))
          ) ll;
        !res
      end
  | Xml.Element(s,l,_) when s="funapp" ->
     failwith "So many argument in funapp !"
  | Xml.Element(s,[],a::b::[]) when s="application" ->
      let t1=get_local_type a in
      let t2=parenthesis (get_term Type b) in
      t1^" "^t2
  | Xml.Element(s,l,ll) when s="application" ->
     failwith "So many argument in application !"
  | _ -> failwith "Error in get_local_type !"

and get_term (loc:location) =
  function
    | Xml.Element(s,l,ll) when s="funapp" ->
      begin
        let res=ref "" in
        List.iter
          (fun x ->
             let sep = (if !res="" then "" else " ") in
             res:=!res^sep^(parenthesis (get_term (nul_loc loc) x))
          ) ll;
        !res
      end
    | Xml.Element(s,[],(Xml.PCData x)::tl) when s="name" -> normalise x
    | Xml.Element(s,l,ll) when s="name" ->
      failwith "So many argument in name !"
    | Xml.Element(s,[],a::[]) when s="arg" -> get_term (nul_loc loc) a
    | Xml.Element(s,l,ll) when s="arg" ->
      failwith "So many argument in arg !"
    | Xml.Element(s,[],a::b::[]) when s="application" ->
      let t1=get_term (add_one loc) a in
      let t2=parenthesis (get_term (nul_loc loc) b) in
      t1^" "^t2
    | Xml.Element(s,l,ll) when s="application" ->
      failwith "So many argument in application !"
    | Xml.Element(s,[],(Xml.PCData x)::[]) when s="var" ->
       begin
         match loc with
         | Rhs i -> eta_expand ((List.assoc x !var_arity)-i) (normalise x)
         | Lhs i -> var_arity:=(x,i)::!var_arity; normalise x
         | Type -> normalise x
      end
    | Xml.Element(s,l,ll) when s="var" ->
      failwith "So many argument in var !"
    | Xml.Element(s1,[],(Xml.Element(s2,[],(Xml.PCData x)::[]))::b::c::[])
         when s1="lambda" && s2="var" ->
       begin
       "(" ^ (normalise x) ^
         (
           match loc with
           | Type  -> " : " ^ (get_local_type b)
           | Rhs _ -> " : " ^ (get_local_type b)
           | Lhs _ -> ""
         ) ^ " => " ^ (get_term (nul_loc loc) c) ^ ")"
       end
    | Xml.Element(s,l,ll) when s="lambda" ->
      failwith "So many argument in lambda !"
    | x -> failwith
             ("This file is totally unexpected !!\n"^(Xml.to_string x)^"\n")

let get_rule_term =
  function
  | Xml.Element(s,l,a::[]) when s="rhs" -> get_term (Rhs 0) a
  | Xml.Element(s,l,a::[]) when s="lhs" -> var_arity:=[]; get_term (Lhs 0) a
  | x -> failwith
           ("This file is totally unexpected !!\n"^(Xml.to_string x)^"\n")

let rec get_funcs =
  let get_name = function
    | Xml.Element(s,[],(Xml.PCData x)::[]) when s="name" -> normalise x
    | Xml.Element(s,l,ll) when s="name" ->
      failwith "So many argument in name !"
    | _ -> failwith "Unexpected argument for get_name"
  in
  let rec get_type = function
    | Xml.Element(s,[],ll) when s="typeDeclaration" ->
      List.map get_local_type ll
    | x -> failwith ("Error in get_type !"^(Xml.to_string x))
  in
  let rec get_type_arity = function
    | Xml.Element(s,[],(PCData n)::[]) when s="arity" ->
      List.init ((int_of_string n)+1) (fun _ -> "Default_Type")
    | x -> failwith ("Error in get_type_arity !"^(Xml.to_string x))
  in
  function
  | Xml.Element(s,[],a::b::[]) when s="funcDeclaration" ->
    [(get_name a, get_type b)]
  | Xml.Element(s,l,ll) when s="funcDeclaration" ->
    failwith "So many argument in funcDeclaration !"
  | Xml.Element(s,[],a::b::[]) when s="funcsym" ->
    [(get_name a, get_type_arity b)]
  | Xml.Element(s,l,ll) when s="funcsym" ->
    failwith "So many argument in funcsym !"
  | Xml.Element(s,l,ll) ->
    List.flatten (List.map get_funcs ll)
  | Xml.PCData(s) -> []

let rec get_rules = function
  | Xml.Element(s,[],a::b::[]) when s="rule" ->
    let t1= get_rule_term a in
    let t2= get_rule_term b in
    [(get_vars a, t1, t2)]
  | Xml.Element(s,l,ll) when s="rule" ->
    failwith "So many arguments in rule !"
  | Xml.Element(s,l,ll) -> List.flatten (List.map get_rules ll)
  | Xml.PCData(_) -> []

let print_rules fmt triple =
  let a,b,c = triple in
  Format.fprintf fmt "[%a] %s --> %s.@."
    (pp_sstring "," Format.pp_print_string) a b c

let print_type fmt a =
  Format.fprintf fmt "%s : Type.@." a

let print_func fmt couple =
  let a,b = couple in
  Format.fprintf fmt "def %s : %a.@." a
    (pp_list " -> " Format.pp_print_string) b

let print_dk y =
  let name = String.sub y 0 (String.length y -4)^".dk" in
  let output = Format.formatter_of_out_channel (open_out name) in
  let x=Xml.parse_file y in
  let typ = get_types x in
  if SString.cardinal typ = 0
  then print_type output "Default_Type"
  else SString.iter (print_type output) typ;
  let funcs = get_funcs x in
  List.iter (print_func output) funcs;
  let rules = get_rules x in
  List.iter (print_rules output) rules

let add_type : string -> string =
  fun s ->
   "def "^s^" : Type.\n"

let add_func : mident -> (string * string list) -> string =
  let rec constructPi : mident -> string list -> string =
    fun md -> function
    | [] -> assert false
    | s :: [] -> s
    | s :: tl -> s^" -> "^(constructPi md tl)
  in
  fun md (s,l) ->
    "def "^s^" : "^(constructPi md l)^".\n"

let add_rul : mident -> (SString.t * string * string) -> string =
  fun md (var,t1,t2) ->
    let res = ref "[" in
    let first = ref true in
    SString.iter
      (fun s -> res := !res^(if !first then (first := false; s) else ","^s))
      var;
    !res^"] "^t1^" --> "^t2^".\n"

let run : mident -> Xml.xml -> string =
  fun md x ->
  let typ = get_types x in
  let list_typ =
    if SString.cardinal typ = 0
    then add_type "Default_Type"
    else List.fold_left (fun s x -> s^(add_type x)) "" (SString.elements typ)
  in
  let funcs = get_funcs x in
  let list_func = List.fold_left (fun s x -> s^(add_func md x)) "" funcs in
  let rules = get_rules x in
  let list_rul = List.fold_left (fun s x -> s^(add_rul md x)) "" rules in
  list_typ ^ list_func ^ list_rul


let load_file : mident -> string -> string =
  fun md file ->
  run md (Xml.parse_file file)

let load_std : mident -> string =
  fun md ->
  run md (Xml.parse_in stdin)
