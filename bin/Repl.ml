open OneMl
module S = Lang.Surface

type cmd =
  | CEval of { source : string; binds : S.bind list }
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

let read_code session line =
  let filename = Session.next_filename session in
  let rec loop buf =
    let source = Buffer.contents buf in
    match Pipeline.parse_string ~filename source with
    | file -> CEval { source; binds = Lang.Surface.Node.data file }
    | exception Diagnostic.Error.Error diag when error_at_eof buf diag ->
      (match prompt "..> " with
       | line ->
         Buffer.add_string buf line;
         Buffer.add_char buf '\n';
         loop buf
       | exception End_of_file ->
         print_newline ();
         Session.cache_source session ~filename ~source;
         Diagnostic.print ~read:(Session.read session) diag;
         CEval { source; binds = [] })
    | exception Diagnostic.Error.Error diag ->
      Session.cache_source session ~filename ~source;
      Diagnostic.print ~read:(Session.read session) diag;
      CEval { source; binds = [] }
  in
  let buf = Buffer.create 64 in
  Buffer.add_string buf line;
  Buffer.add_char buf '\n';
  loop buf
;;

let read session =
  match prompt "1ml> " with
  | line ->
    let trimmed = String.trim line in
    if String.starts_with ~prefix:"#" trimmed
    then read_command line
    else read_code session line
  | exception End_of_file ->
    print_newline ();
    CExit
;;

let eval session = function
  | CExit -> exit 0
  | CHelp ->
    print_string help;
    flush stdout
  | CEval { source; binds = [] } ->
    (* Either empty input or already-handled parse error; nothing to step. *)
    ignore source
  | CEval { source; binds } ->
    (try Session.step session ~source binds with
     | Diagnostic.Error.Error diag ->
       Diagnostic.print ~read:(Session.read session) diag)
;;
