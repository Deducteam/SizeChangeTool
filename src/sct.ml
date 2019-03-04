open Basic
open Dk_export

let perform_checks : Callgraph.call_graph -> bool =
  fun gr ->
  Sizechange.check_sct gr
  && Arity_checker.check_lh_arity gr.signature
  && Positivity_checker.check_positivity gr
  && Rhs_typability.check_rhs_underf_typab gr

type extension = Xml | Dk

let str_to_ext : string -> extension =
  function
  | ".xml"
    | "xml"
    | ".Xml"
    | "Xml"
    | ".XML"
    | "XML" -> Xml
  | ".dk"
    | "dk"
    | ".Dk"
    | "Dk"
    | ".DK"
    | "DK"  -> Dk
  | _      -> failwith "Not handled file extension"

let generate_graph : string -> extension -> bool -> Callgraph.call_graph =
  fun file ext is_stdin ->
  match ext, is_stdin with
  | Dk,  false ->
     let input = open_in file in
     let md = Filename.remove_extension (Filename.basename file) in
     let s =
       to_dk_signature file (Parser.Parse_channel.parse (mk_mident md) input)
     in (close_in input; Dk_import.dk_sig_to_callgraph s)
  | Xml, false ->
     let md = mk_mident file in
     let dk_string = Tpdb_to_dk.load_file md file in
     if !(Tpdb_to_dk.export_dk_file)
     then
       (let output = Format.formatter_of_out_channel (open_out (file^".dk")) in
        Format.fprintf output "%s@." dk_string);
     let s =
       to_dk_signature file (Parser.Parse_string.parse (mk_mident file) dk_string)
     in Dk_import.dk_sig_to_callgraph s
  | Dk,  true  ->
     let s =
       to_dk_signature file (Parser.Parse_channel.parse (mk_mident "std_in") stdin)
     in Dk_import.dk_sig_to_callgraph s
  | Xml, true ->
     let md = mk_mident file in
     let dk_string = Tpdb_to_dk.load_std md in
     if !(Tpdb_to_dk.export_dk_file)
     then
       (let output = Format.formatter_of_out_channel (open_out (file^".dk")) in
        Format.fprintf output "%s@." dk_string);
     let s =
       to_dk_signature file (Parser.Parse_string.parse (mk_mident file) dk_string)
     in Dk_import.dk_sig_to_callgraph s

let run file gr =
  let colored n s =
    if !Errors.color
    then "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"
    else s
  in
  let green  = colored 2 in
  let orange = colored 3 in
  if perform_checks gr
  then
    (Format.printf "%s@." (green "YES");
     Debug.debug Debug.D_warn "%s was proved terminating@." file)
  else
    begin
      Format.eprintf "%s@." (orange "MAYBE");
      Format.eprintf "SizeChangeTool was unable to prove %s terminating@." file;
      let lc_result : Sign.symbol -> unit =
        fun sy ->
          if sy.result = []
          then ()
          else
            List.iter
              (fun lc ->
                 Format.eprintf
                   "\027[31m * %a is %a relatively to the rules\027[m@."
                   pp_name sy.name
                   Sign.pp_local_result lc;
                   (match lc with
                    | SelfLooping l   ->
                      Format.eprintf "  - %a@."
                        (pp_list "\n  - " Format.pp_print_string) l
                    | NotPFP s
                      | NotPositive s
                      | RhsUntypable s
                      | LhsOverApplied s ->
                       Format.eprintf "  - %a@."
                         Format.pp_print_string s
                   )
              )
              sy.result in
      Sign.IMap.iter (fun _ x -> lc_result x) (gr.signature.symbols)
    end

let run_on_file file =
  let ext = str_to_ext (Filename.extension file) in
  let gr = generate_graph file ext false in
  run file gr

let run_on_stdin ext =
  let md_name = "std_in" in
  let gr = generate_graph md_name ext true in
  run md_name gr

let set_debug : string -> unit =
  fun st ->
    String.iter
    (fun c ->
       try Env.set_debug_mode (String.make 1 c)
       with
       | Env.DebugFlagNotRecognized 'x' ->
         Debug.enable_flag Sizematrix.D_matrix
       | Env.DebugFlagNotRecognized 's' ->
         Debug.enable_flag Sizechange.D_sctsummary
       | Env.DebugFlagNotRecognized 'g' ->
         Debug.enable_flag Callgraph.D_graph
       | Env.DebugFlagNotRecognized 'a' ->
         Debug.enable_flag Callgraph.D_call
    ) st

let _ =
  let options = Arg.align
     [( "-d"
      , Arg.String set_debug
      , "flags enables debugging for all given flags [xsgap] and [qnocutrm] inherited from Dedukti" ) ;
      ("--create-dk"
      , Arg.Set Tpdb_to_dk.export_dk_file
      , "create the dk file from an xml" ) ;
      ( "--dk-v"
      , Arg.Unit (fun () -> set_debug "montru")
      , " Verbose mode for Dedukti errors (equivalent to -d 'montru')" ) ;
      ( "--sz-v"
      , Arg.Unit (fun () -> set_debug "xsga")
      , " Verbose mode for SCT specific errors(equivalent to -d 'xsga')" ) ;
      ( "--verbose"
      , Arg.Unit (fun () -> set_debug "montruxsga")
      , " Most verbose mode (equivalent to -d 'montruxsga')" ) ;
      ( "-q"
      , Arg.Unit (fun () -> Env.set_debug_mode "q")
      , " Quiet mode (equivalent to -d 'q'" ) ;
      ( "-nc"
      , Arg.Clear Errors.color
      , " Disable colors in the output" ) ;
      ( "--stdin"
      , Arg.String (fun s -> run_on_stdin (str_to_ext s))
      , " ext Parses standard input considering it is a .ext file")
     ]
  in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\n" in
  let usage = usage ^ "Available options:" in
  let files =
    let files = ref [] in
    Arg.parse options (fun f -> files := f :: !files) usage;
    List.rev !files
  in
  List.iter run_on_file files
