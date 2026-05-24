open OneMl

let read_files ?prelude inputs =
  let open Lang.Surface in
  let wrap path =
    Node.map (fun file -> BVal (Node.make path, Node.make (EStruct file)))
  in
  let prelude =
    match prelude with
    | Some path -> Syntax.parse_file path |> Lang.Surface.Node.data
    | None -> []
  in
  let files = List.map (fun path -> Syntax.parse_file path |> wrap path) inputs in
  Node.make (prelude @ files)
;;

let run_fomega expr =
  let extern = Eval.Extern.Compat.rossberg Eval.Extern.rossberg in
  let expr = Elaborate.Elab.file Elaborate.Env.empty expr in
  let _ = Lang.FOmega.Typecheck.check Lang.FOmega.Typecheck.Env.empty expr in
  Lang.FOmega.Eval.eval (Lang.FOmega.Eval.Env.init extern) expr
;;

let run expr = Eval.Eval.eval (Eval.Env.init Eval.Extern.rossberg) expr

let file inputs =
  try
    let expr = read_files ?prelude:Args.prelude inputs in
    let expr = Typecheck.Check.file Typecheck.Env.empty expr in
    if Args.fomega then ignore (run_fomega expr) else ignore (run expr)
  with
  | OneMl.Diagnostic.Error.Error diag ->
    OneMl.Diagnostic.print ~read:OneMl.Diagnostic.read diag
;;

let rec repl state =
  let state, cmd = Repl.read state in
  repl (Repl.eval state cmd)
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
  Logs.set_reporter reporter;
  match Args.mode with
  | Repl -> repl Repl.State.empty
  | Run inputs -> file inputs
;;
