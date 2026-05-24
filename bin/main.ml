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

let read_file path =
  let chan = In_channel.open_text path in
  let source = In_channel.input_all chan in
  In_channel.close chan;
  source
;;

let load_prelude session path =
  try
    let source = read_file path in
    let file = OneMl.Pipeline.parse_string ~filename:path source in
    OneMl.Session.cache_source session ~filename:path ~source;
    OneMl.Session.step session ~source (OneMl.Lang.Surface.Node.data file)
  with
  | OneMl.Diagnostic.Error.Error err ->
    OneMl.Diagnostic.print ~read:(OneMl.Session.read session) err
;;

let repl () =
  let session = OneMl.Session.init ~fomega:Args.fomega () in
  Option.iter (load_prelude session) Args.prelude;
  Printf.printf "1ml prototype REPL. Type #help for commands, #exit to quit.\n%!";
  while true do
    try
      let cmd = Repl.read session in
      Repl.eval session cmd
    with
    | OneMl.Diagnostic.Error.Error err ->
      OneMl.Diagnostic.print ~read:(OneMl.Session.read session) err
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
