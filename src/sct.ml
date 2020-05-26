open Kernel.Basic
open Parsing
open Dk_export

let d_termin = Debug.new_flag true "Termin"

exception Timeout

let timeout : int ref = ref 0
let pfp : bool ref = ref false

let run_with_timeout : int -> ('a -> unit) -> ('a -> unit) -> 'a -> unit =
  fun timeout fail f x ->
  let old_handler =
    Sys.signal Sys.sigalrm
      (Sys.Signal_handle (fun _ -> raise Timeout)) in
  let finish () =
    ignore (Unix.alarm 0);
    ignore (Sys.signal Sys.sigalrm old_handler) in
  try
    ignore (Unix.alarm timeout);
    ignore (f x);
    finish ()
  with
  | Timeout -> finish (); fail x
  | exn -> finish (); raise exn

let perform_checks : Callgraph.call_graph -> bool =
  fun gr ->
  let sct = Sizechange.check_sct gr in
  let arity = Arity_checker.check_lh_arity gr.signature in
  let pos =
    if !pfp
    then Pfp_checker.check_pfp gr
    else Positivity_checker.check_positivity gr
  in
  let rhs_typ = Rhs_typability.check_rhs_underf_typab gr in
  sct && arity && pos && rhs_typ

type extension = Xtc | Dk

let str_to_ext : string -> extension =
  function
  | ".xml"
    | "xml"
    | ".Xml"
    | "Xml"
    | ".XML"
    | "XML"
    | "xtc"
    | "Xtc"
    | "XTC" -> Xtc
  | ".dk"
    | "dk"
    | ".Dk"
    | "Dk"
    | ".DK"
    | "DK"  -> Dk
  | _       -> failwith "Not handled file extension"

let generate_graph : string -> extension -> bool -> Callgraph.call_graph =
  fun file ext is_stdin ->
  match ext, is_stdin with
  | Dk,  false ->
     let input = Parsers.Parser.input_from_file file in
     let s =
       to_dk_signature file (Parsers.Parser.parse input)
     in Dk_import.dk_sig_to_callgraph s
  | Xtc, false ->
     let file_without_ext = Filename.chop_extension file in
     let md = mk_mident file_without_ext in
     let dk_string = Tpdb_to_dk.load_file md file in
     if !(Tpdb_to_dk.export_dk_file)
     then
       (let output = Format.formatter_of_out_channel (open_out (file_without_ext^".dk")) in
        Format.fprintf output "%s@." dk_string);
     let s =
       to_dk_signature file (Parsers.Parser.parse (Parsers.Parser.input_from_string md dk_string))
     in
     Dk_import.dk_sig_to_callgraph s
  | Dk,  true  ->
     let s =
       to_dk_signature file (Parsers.Parser.parse (Parsers.Parser.input_from_stdin (mk_mident "std_in")))
     in Dk_import.dk_sig_to_callgraph s
  | Xtc, true ->
     let md = mk_mident file in
     let dk_string = Tpdb_to_dk.load_std md in
     if !(Tpdb_to_dk.export_dk_file)
     then
       (let output = Format.formatter_of_out_channel (open_out (file^".dk")) in
        Format.fprintf output "%s@." dk_string);
     let s =
       to_dk_signature file (Parsers.Parser.parse (Parsers.Parser.input_from_string md dk_string))
     in Dk_import.dk_sig_to_callgraph s


let colored n s =
  if !Api.Errors.color
  then "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"
  else s

let green  = colored 2
let orange = colored 3

let run file gr =
  try
    if perform_checks gr
    then
      (Format.printf "%s@." (green "YES");
       Debug.debug d_termin "%s was proved terminating using Dependency Pairs and SCT" file)
    else
      begin
        Format.printf "%s@." (orange "MAYBE");
        Debug.debug Debug.d_warn
          "SizeChangeTool was unable to prove %s terminating" file;
        let lc_result : Sign.symbol -> unit =
          fun sy ->
          if sy.result = []
          then ()
          else
            Debug.debug_eval d_termin
              (fun () ->
                List.iter
                  (fun lc ->
                    Format.eprintf
                      "\027[31m * %a %a in the rules\027[m@."
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
                  sy.result
              )
        in
        Sign.IMap.iter (fun _ x -> lc_result x) (gr.signature.symbols)
      end
  with
  | Rhs_typability.NotWS f ->
     begin
       Format.printf "%s@." (orange "MAYBE");
       Debug.debug Debug.d_warn
         "SizeChangeTool was unable to prove %s terminating" file;
       Debug.debug d_termin "\027[31mThe file is not well-structured, since %a is not smaller than its type.\027[m" pp_name f
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
       try Api.Env.set_debug_mode (String.make 1 c)
       with
       | Api.Env.DebugFlagNotRecognized 'x' ->
          Debug.enable_flag Sizematrix.d_matrix
       | Api.Env.DebugFlagNotRecognized 's' ->
          Debug.enable_flag Sizechange.d_sct
       | Api.Env.DebugFlagNotRecognized 'g' ->
          Debug.enable_flag Callgraph.d_graph
       | Api.Env.DebugFlagNotRecognized 'a' ->
          Debug.enable_flag Callgraph.d_call
       | Api.Env.DebugFlagNotRecognized 'i' ->
          Debug.disable_flag d_termin
       | Api.Env.DebugFlagNotRecognized 'p' ->
          Debug.enable_flag Positivity_checker.d_pos
    ) st

let _ =
  let options = Arg.align
     [( "-d"
      , Arg.String set_debug
      , "flags enables debugging for all given flags [ixsgap] and [qnocutrm] inherited from Dedukti" ) ;
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
      , Arg.Unit (fun () -> Api.Env.set_debug_mode "q")
      , " Quiet mode (equivalent to -d 'q'" ) ;
      ("--create-dk"
      , Arg.Set Tpdb_to_dk.export_dk_file
      , " Create the dk file from an xml" ) ;
      ( "--no-color"
      , Arg.Clear Api.Errors.color
      , " Disable colors in the output" ) ;
      ( "--stdin"
      , Arg.String (fun s -> run_on_stdin (str_to_ext s))
      , "ext Parses standard input considering it is a .ext file") ;
      ( "--timeout"
      , Arg.Set_int timeout
      , "i Set the timeout to i seconds (no timeout if i=0, i=0 by default)");
      ( "--pfp"
      , Arg.Set pfp
      , " Performs PFP check rather than general positivity check")
     ]
  in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\n" in
  let usage = usage ^ "Available options:" in
  let files =
    let files = ref [] in
    Arg.parse options (fun f -> files := f :: !files) usage;
    List.rev !files
  in
  try
    List.iter
      (run_with_timeout
         !timeout
         (Format.eprintf
            "%s@.SizeChangeTool has timed out on %s@."
            (orange "MAYBE")
         )
         run_on_file
      )
      files
  with
  | e                ->
     let (code, lc, msg) = Api.Errors.string_of_exception ~red:(fun x -> x) dloc e in
     Api.Errors.fail_exit ~file:"" ~code:(string_of_int code) (Some lc) "%s" msg
