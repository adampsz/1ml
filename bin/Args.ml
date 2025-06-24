type mode =
  | Run of string list
  | Repl

let inputs = ref []
and repl = ref false
and trace_dir = ref None
and color = ref None

let get_usage () =
  let name = if Array.length Sys.argv > 0 then Sys.argv.(0) else "1ml" in
  Printf.sprintf "Usage: %s [options] [file...]\n" (Filename.basename name)
;;

let get_help msg =
  let f = function
    | line when String.ends_with ~suffix:"[HIDDEN]" line -> None
    | line when String.ends_with ~suffix:"[INTERNAL]" line -> None
    | line when String.starts_with ~prefix:"  -help" line -> None
    | line -> Some line
  in
  String.split_on_char '\n' msg |> List.filter_map f |> String.concat "\n"
;;

let set_string_opt ref = Arg.String (fun s -> ref := Some s)

let set_color ref =
  let f = function
    | "always" | "yes" | "y" -> ref := Some true
    | "never" | "no" | "n" -> ref := Some false
    | "auto" -> ref := None
    | _ -> raise (Arg.Bad "Invalid value for --color. Use 'always', 'never', or 'auto'.")
  in
  Arg.String f
;;

let show_version () =
  Printf.printf "%s v%s\n" Config.name Config.version;
  exit 0
;;

let spec =
  [ "--repl", Arg.Set repl, "\tStart interactive repl"
  ; "--trace-dir", set_string_opt trace_dir, "\t[INTERNAL]"
  ; "--color", set_color color, "\tColorize output (always, never, auto)"
  ; "--version", Arg.Unit show_version, "\tDisplay version information"
  ; "-", Arg.Unit (fun () -> inputs := "-" :: !inputs), "\t[HIDDEN]"
  ]
  |> Arg.align

and positional path = inputs := path :: !inputs

let _ =
  try Arg.parse_argv Sys.argv spec positional (get_usage ()) with
  | Arg.Bad msg ->
    Printf.eprintf "%s" msg;
    exit 2
  | Arg.Help msg ->
    Printf.printf "%s\n" (get_help msg);
    exit 0
;;

let mode =
  match !inputs, !repl with
  | [], false when In_channel.isatty stdin && Out_channel.isatty stdout -> Repl
  | _, true -> Repl
  | [], false -> Run [ "-" ]
  | files, false -> Run (List.rev files)
;;

let trace_dir = !trace_dir

let color =
  match !color with
  | Some enabled -> enabled
  | None ->
    (match Sys.getenv_opt "TERM" with
     | Some "dumb" | Some "" | None -> false
     | Some _ -> Out_channel.isatty stderr)
;;
