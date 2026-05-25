open OneMl

let read = function
  | "-" -> Syntax.parse_stdin ()
  | path -> Syntax.parse_file path
;;

let read_files ?prelude inputs : Lang.Surface.file =
  let open Lang.Surface in
  let prelude = Option.fold ~none:[] ~some:read prelude in
  let file path =
    Node.make (BVal (Public, Node.make path, Node.make (EStruct (read path))))
  in
  prelude @ List.map file inputs
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
  let state = Repl.eval state cmd in
  repl state
;;

let load_prelude path state = fst (Repl.State.next (Syntax.parse_file path) state)

let init_repl () =
  match Args.prelude with
  | None -> Repl.State.empty
  | Some path ->
    (try load_prelude path Repl.State.empty with
     | Diagnostic.Error.Error diag ->
       Diagnostic.print ~read:Diagnostic.read diag;
       exit 1)
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
  | Repl -> repl (init_repl ())
  | Run inputs -> file inputs
;;
