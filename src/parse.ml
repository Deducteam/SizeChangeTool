module SString=Set.Make(struct
    type t=string
    let compare= compare
  end)

let parenthesis s=
  if String.contains s ' '
  then "("^s^")"
  else s
    
let pp_couple sep pp1 pp2 fmt x = Format.fprintf fmt "%a%s%a" pp1 (fst x) sep pp2 (snd x)

let format_of_sep str fmt () : unit = Format.fprintf fmt "%s" str
    
let pp_list sep pp fmt l = Format.pp_print_list ~pp_sep:(format_of_sep sep) pp fmt l

let pp_sstring sep pp fmt s = pp_list sep pp fmt (SString.elements s)

let rec pp_xml fmt = function
  | Xml.Element(s,l,ll) -> Format.fprintf fmt "Element %s,[%a] , [%a] @." s (pp_list ";" (pp_couple "," Format.pp_print_string Format.pp_print_string)) l (pp_list ";" pp_xml) ll
  | Xml.PCData(s) -> Format.fprintf fmt "PCData %s" s

let rec get_vars = function
  | Xml.Element(s,l,ll) when s="var" ->
    begin
      let (Xml.PCData x)::tl=ll in
      if tl != [] then failwith ("So many argument in var !");
      SString.singleton(x)
    end
  | Xml.Element(s,l,ll) ->
    List.fold_left SString.union SString.empty  (List.map get_vars ll)
  | Xml.PCData(s) -> SString.empty

let rec get_types = function
  | Xml.Element(s,l,ll) when s="basic" ->
    begin
      let (Xml.PCData x)::tl=ll in
      if tl != [] then failwith ("So many argument in basic !");
      SString.singleton(x)
    end
  | Xml.Element(s,l,ll) ->
    List.fold_left SString.union SString.empty  (List.map get_types ll)
  | Xml.PCData(s) -> SString.empty

let rec get_funcs =
  let get_name = function
    | Xml.Element(s,[],ll) when s="name" ->
      begin
        let (Xml.PCData x)::tl=ll in
        if tl != [] then failwith ("So many argument in name !");
        x
      end
    | _ -> failwith "Unexpected argument for get_name"
  in
  let rec get_local_type = function
    | Xml.Element(s,[],ll) when s="type" ->
      begin
        let a::tl=ll in
        if tl != [] then failwith ("So many argument in type !");
        get_local_type a
      end
    | Xml.Element(s,[],ll) when s="arrow" ->
      begin
        let a::b::tl=ll in
        if tl != [] then failwith ("So many argument in type !");
        "("^(get_local_type a)^"->"^(get_local_type b)^")"
      end
    | Xml.Element(s,[],ll) when s="basic" ->
      begin
        let (Xml.PCData x)::tl=ll in
        if tl != [] then failwith ("So many argument in basic !");
        x
      end
    | _ -> failwith "Error in get_local_type !"
  in
  let rec get_type = function
    | Xml.Element(s,[],ll) when s="typeDeclaration" ->
      List.map get_local_type ll
    | x -> failwith ("Error in get_type !"^(Xml.to_string x))
  in
  function
  | Xml.Element(s,l,ll) when s="funcDeclaration" ->
    begin
      let a::b::tl=ll in
      if tl != [] then failwith ("So many argument in funcDeclaration !");
      [(get_name a, get_type b)]
    end
  | Xml.Element(s,l,ll) ->
    List.flatten (List.map get_funcs ll)
  | Xml.PCData(s) -> []

let rec get_term = function
  | Xml.Element(s,l,ll) when (s="rhs" || s="lhs") ->
    begin
      let a::tl=ll in
      if tl != [] then failwith ("So many argument in "^s^" !");
      get_term a
    end
  | Xml.Element(s,l,ll) when s="funapp" ->
    begin
      let res=ref "" in
      List.iter
        (fun x ->
           let sep = (if !res="" then "" else " ") in
           res:=!res^sep^(parenthesis (get_term x))
        ) ll;
      !res
    end
  | Xml.Element(s,l,ll) when s="name" ->
    begin
      let (Xml.PCData x)::tl=ll in
      if tl != [] then failwith ("So many argument in name !");
      x
    end
  | Xml.Element(s,l,ll) when s="arg" ->
    begin
      let a::tl=ll in
      if tl != [] then failwith ("So many argument in arg !");
      get_term a
    end
  | Xml.Element(s,l,ll) when s="application" ->
    begin
      let a::b::tl=ll in
      if tl != [] then failwith ("So many argument in application !");
      (get_term a)^" "^(parenthesis (get_term b))
    end
  | Xml.Element(s,l,ll) when s="var" ->
    begin
      let (Xml.PCData x)::tl=ll in
      if tl != [] then failwith ("So many argument in var !");
      x
    end
  | Xml.Element(s,l,ll) when s="lambda" ->
    begin
      let a::b::c::tl=ll in
      if tl != [] then failwith ("So many argument in lambda !");
      (get_term a)^" => "^(get_term c)
    end
  | x -> failwith ("CACA !"^(Xml.to_string x))

let rec get_rules = function
  | Xml.Element(s,l,ll) when s="rule" ->
    begin
      let a::b::tl=ll in
      if tl !=[] then failwith "So many arguments in rule !";
      [(get_vars a, get_term a, get_term b)]
    end
  | Xml.Element(s,l,ll) -> List.flatten (List.map get_rules ll)
  | Xml.PCData(_) -> []
  
let print_rules fmt triple =
  let a,b,c = triple in
  Format.fprintf fmt "[%a] %s-->%s.@." (pp_sstring "," Format.pp_print_string) a b c

let print_type fmt a =
  Format.fprintf fmt "%s : Type.@." a

let print_func fmt couple =
  let a,b = couple in
  Format.fprintf fmt "def %s : %a.@." a (pp_list "->" Format.pp_print_string) b
  
let print_dk y =
  let name = (List.hd (String.split_on_char '.' y))^".dk" in
  let output = Format.formatter_of_out_channel (open_out name) in
  let x=Xml.parse_file y in
  let typ = get_types x in
  SString.iter (print_type output) typ;
  let funcs = get_funcs x in
  List.iter (print_func output) funcs;
  let rules = get_rules x in
  List.iter (print_rules output) rules

let _ =
  let files =
    let files = ref [] in
    Arg.parse [] (fun f -> files := f :: !files) "";
    List.rev !files
  in
  List.iter (fun x-> print_dk x) files
