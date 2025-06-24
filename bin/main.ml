open OneMl

let file inputs =
  let aux deps file =
    let m = OneMl.Pipeline.Module.create () in
    let m =
      match file with
      | "-" -> OneMl.Pipeline.Module.add_from_channel "<input>" stdin m
      | file -> OneMl.Pipeline.Module.add_from_file file m
    in
    m :: deps
  in
  match List.fold_left aux [] inputs with
  | exception OneMl.Diagnostic.Error.Error err -> OneMl.Diagnostic.print err
  | _ -> ()
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
    match Args.trace_dir with
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
