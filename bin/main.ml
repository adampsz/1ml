open OneMl

let file inputs =
  try
    let tree =
      match Args.prelude with
      | Some path ->
        OneMl.Pipeline.prelude path (OneMl.Pipeline.add path path OneMl.Pipeline.empty)
      | None -> OneMl.Pipeline.empty
    in
    let tree = List.fold_left (fun t f -> OneMl.Pipeline.add f f t) tree inputs in
    let expr = OneMl.Pipeline.get tree in
    let expr = OneMl.Pipeline.typecheck expr in
    if Args.fomega then OneMl.Pipeline.eval_fomega expr else OneMl.Pipeline.eval expr
  with
  | OneMl.Diagnostic.Error.Error err ->
    OneMl.Diagnostic.print ~read:OneMl.Diagnostic.read err
;;

let rec repl () =
  let cmd = Repl.read () in
  Repl.eval cmd;
  repl ()
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
  | Repl -> repl ()
  | Run inputs -> file inputs
;;
