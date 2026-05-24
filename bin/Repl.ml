open OneMl
module S = Lang.Surface

type session = S.bind list

type cmd =
  | CEval of S.bind list
  | CHelp
  | CExit

let help =
  "Available commands:\n  #help - Display this help\n  #exit - Exit interactive session\n"
;;

let prompt p =
  print_string p;
  flush stdout;
  input_line stdin
;;

let read_command line =
  let trimmed = String.trim line in
  let body = String.sub trimmed 1 (String.length trimmed - 1) in
  match String.split_on_char ' ' body |> List.filter (fun s -> s <> "") with
  | [] | [ "help" ] -> CHelp
  | [ "exit" ] -> CExit
  | _ -> Diagnostic.Error.error "unknown REPL command: %s" body
;;

let error_at_eof source diag =
  match Diagnostic.span diag with
  | None -> false
  | Some (p, _) -> p.Lexing.pos_cnum >= Buffer.length source
;;

let read_code line =
  let rec loop buf =
    match Pipeline.parse_string ~filename:"<stdin>" (Buffer.contents buf) with
    | file -> CEval (Lang.Surface.Node.data file)
    | exception Diagnostic.Error.Error diag when error_at_eof buf diag ->
      (match prompt "..> " with
       | line ->
         Buffer.add_string buf line;
         Buffer.add_char buf '\n';
         loop buf
       | exception End_of_file ->
         print_newline ();
         Diagnostic.print ~read:Diagnostic.read diag;
         CEval [])
    | exception Diagnostic.Error.Error diag ->
      Diagnostic.print ~read:Diagnostic.read diag;
      CEval []
  in
  let buf = Buffer.create 64 in
  Buffer.add_string buf line;
  Buffer.add_char buf '\n';
  loop buf
;;

let read () =
  match prompt "1ml> " with
  | line ->
    let trimmed = String.trim line in
    if String.starts_with ~prefix:"#" trimmed then read_command line else read_code line
  | exception End_of_file ->
    print_newline ();
    CExit
;;

let eval_binds ~fomega session new_binds =
  let combined = session @ new_binds in
  let file = Lang.Surface.Node.make combined in
  let typed = Pipeline.typecheck file in
  if fomega then Pipeline.eval_fomega typed else Pipeline.eval typed;
  combined
;;

let eval ~fomega session = function
  | CExit -> exit 0
  | CHelp ->
    print_string help;
    flush stdout;
    session
  | CEval binds ->
    (try eval_binds ~fomega session binds with
     | Diagnostic.Error.Error diag ->
       Diagnostic.print ~read:Diagnostic.read diag;
       session)
;;
