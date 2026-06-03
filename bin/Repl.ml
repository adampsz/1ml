open OneMl
module S = Lang.Surface
module T = Lang.Typed

type cmd =
  | CEval of S.file
  | CExpr of S.expr
  | CNone
  | CHelp
  | CExit

module State = struct
  type t =
    { typecheck : OneMl.Typecheck.Session.state
    ; eval : OneMl.Eval.Session.state
    }

  let empty =
    { typecheck = OneMl.Typecheck.Session.empty; eval = OneMl.Eval.Session.empty }
  ;;

  let next xs state =
    let typecheck, es, ts = OneMl.Typecheck.Session.next state.typecheck xs in
    let eval = OneMl.Eval.Session.next state.eval es in
    { typecheck; eval }, ts
  ;;

  let base state = OneMl.Typecheck.Env.base state.typecheck.env
end

module Sources = struct
  let sources : (string, string) Hashtbl.t = Hashtbl.create 16
  let filename () = Printf.sprintf "<repl-%d>" (Hashtbl.length sources + 1)
  let register filename source = Hashtbl.replace sources filename source

  let read path =
    match Hashtbl.find_opt sources path with
    | Some source -> Some source
    | None -> Diagnostic.read path
  ;;
end

let expr_as_file expr =
  let span = S.Node.span expr in
  let it = S.Node.make ?span "#res" in
  [ S.Node.make ?span (S.BVal (Public, it, expr)) ]
;;

let intro = "Type #help for available commands."

let help =
  "Available commands:\n\
  \  #help              Display this help\n\
  \  #load <path>       Load source file\n\
  \  #exit              Exit interactive session"
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
  | [ "load"; path ] -> CEval (OneMl.Syntax.parse_file path)
  | _ -> Diagnostic.Error.error "unknown REPL command: %s" body
;;

let error_at_eof source diag =
  match Diagnostic.span diag with
  | None -> false
  | Some (p, _) -> p.Lexing.pos_cnum >= Buffer.length source
;;

let read_code ?filename line =
  let filename = Option.value ~default:(Sources.filename ()) filename in
  let rec loop buf =
    let source = Buffer.contents buf in
    Sources.register filename source;
    match OneMl.Syntax.parse_repl ~filename source with
    | Left expr -> CExpr expr
    | Right file -> CEval file
    | exception Diagnostic.Error.Error diag when error_at_eof buf diag ->
      (match prompt " ..> " with
       | line ->
         Buffer.add_string buf line;
         Buffer.add_char buf '\n';
         loop buf
       | exception End_of_file ->
         print_newline ();
         raise (Diagnostic.Error.Error diag))
  in
  let buf = Buffer.create 64 in
  Buffer.add_string buf line;
  Buffer.add_char buf '\n';
  loop buf
;;

let read () =
  match prompt "1ml> " with
  | line ->
    (match String.trim line with
     | trimmed when String.starts_with ~prefix:"#" trimmed -> read_command line
     | "" -> CNone
     | _ -> read_code line)
  | exception End_of_file ->
    print_newline ();
    CExit
;;

let print_result env t v =
  let pf = Format.printf "@[<2> :@ %a =@ %a@]@." in
  pf (Pretty.Print.typ ~prec:0 ~env) t Eval.Value.pp v
;;

let eval state cmd =
  match cmd with
  | CExit -> exit 0
  | CNone -> state
  | CHelp ->
    Printf.printf "%s\n%!" help;
    state
  | CEval xs ->
    let state, _ = State.next xs state in
    state
  | CExpr expr ->
    let state, ts = State.next (expr_as_file expr) state in
    let x, t = Lang.Typed.Var.assoc "#res" ts in
    let v = Eval.Env.find x state.eval in
    print_result (State.base state) t v;
    state
;;

let rec loop state =
  let step () = eval state (read ()) in
  match OneMl.Diagnostic.protect ~read:Sources.read step with
  | None -> loop state
  | Some state -> loop state
;;
