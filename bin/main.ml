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

let load_prelude path =
  let file = OneMl.Pipeline.parse_file path in
  OneMl.Lang.Surface.Node.data file
;;

let repl () =
  let initial =
    match Args.prelude with
    | None -> []
    | Some path ->
      (try load_prelude path with
       | OneMl.Diagnostic.Error.Error err ->
         OneMl.Diagnostic.print ~read:OneMl.Diagnostic.read err;
         [])
  in
  let session = ref initial in
  Printf.printf "1ml prototype REPL. Type #help for commands, #exit to quit.\n%!";
  while true do
    try
      let cmd = Repl.read () in
      session := Repl.eval ~fomega:Args.fomega !session cmd
    with
    | OneMl.Diagnostic.Error.Error err ->
      OneMl.Diagnostic.print ~read:OneMl.Diagnostic.read err
  done
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
