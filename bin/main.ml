open OneMl

let read = function
  | "-" -> Syntax.parse_stdin ()
  | path -> Syntax.parse_file path
;;

let read_prelude = function
  | Args.NoPrelude -> []
  | Args.CustomPrelude path -> read path
  | Args.DefaultPrelude -> Syntax.parse_string ~filename:"<prelude>" OneMl.prelude
;;

let read_files prelude inputs : Lang.Surface.file =
  let open Lang.Surface in
  let file path =
    Node.make (BVal (Public, Node.make path, Node.make (EStruct (read path))))
  in
  read_prelude prelude @ List.map file inputs
;;

let run_fomega expr =
  let extern = Eval.Extern.Compat.rossberg Eval.Extern.rossberg in
  let expr = Elaborate.Elab.file Elaborate.Env.empty expr in
  let _ = Lang.FOmega.Typecheck.check Lang.FOmega.Typecheck.Env.empty expr in
  Lang.FOmega.Eval.eval (Lang.FOmega.Eval.Env.init extern) expr
;;

let run expr = Eval.Eval.eval (Eval.Env.init Eval.Extern.rossberg) expr

let file inputs =
  let run () =
    let expr = read_files Args.prelude inputs in
    let expr = Typecheck.Check.file Typecheck.Env.empty expr in
    if Args.fomega then ignore (run_fomega expr) else ignore (run expr)
  in
  match OneMl.Diagnostic.protect run with
  | Some () -> ()
  | None -> exit 1
;;

let repl () =
  let init () =
    let prelude = read_prelude Args.prelude in
    let state, _ = Repl.State.next prelude Repl.State.empty in
    state
  in
  match OneMl.Diagnostic.protect init with
  | Some state ->
    Printf.printf "%s\n%!" Repl.intro;
    Repl.loop state
  | None -> exit 1
;;

let _ =
  OneMl.Diagnostic.Color.enable Args.color;
  let reporter = Logs.format_reporter () in
  let reporter =
    match Args.trace with
    | Some dir ->
      Logs.Src.set_level Trace.src (Some Debug);
      let file name = open_out (Filename.concat dir ("1ml-" ^ name ^ ".log")) in
      Trace.reporter (fun name -> Format.formatter_of_out_channel (file name)) reporter
    | None -> reporter
  in
  Logs.set_reporter reporter
;;

let _ =
  let f = function
    | Exit -> Some "Exit"
    | Invalid_argument _ -> Some "Invalid argument"
    | Failure cause -> Some (Printf.sprintf "Failure: %s" cause)
    | Not_found -> Some "Not found"
    | Sys_error cause -> Some (Printf.sprintf "Sys error: %s" cause)
    | End_of_file -> Some "End of file"
    | Division_by_zero -> Some "Division by zero"
    | _ -> None
  in
  Printexc.register_printer f
;;

let _ =
  match Args.mode with
  | Repl -> repl ()
  | Run inputs -> file inputs
;;
