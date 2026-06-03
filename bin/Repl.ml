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
    { history : string list
    ; typecheck : OneMl.Typecheck.Session.state
    ; eval : OneMl.Eval.Session.state
    }

  let empty =
    { history = []
    ; typecheck = OneMl.Typecheck.Session.empty
    ; eval = OneMl.Eval.Session.empty
    }
  ;;

  let append input state = { state with history = input :: state.history }
  let filename state = Printf.sprintf "<repl-%d>" (List.length state.history + 1)

  let nth_back_opt i xs =
    let i = List.length xs - i in
    if i < 0 then None else List.nth_opt xs i
  ;;

  let read state file =
    match Scanf.sscanf_opt file "<repl-%d>" (fun i -> nth_back_opt i state.history) with
    | Some contents -> contents
    | None -> Diagnostic.read file
  ;;

  let next xs state =
    let typecheck, es, ts = OneMl.Typecheck.Session.next state.typecheck xs in
    let eval = OneMl.Eval.Session.next state.eval es in
    { state with typecheck; eval }, ts
  ;;

  let base state = OneMl.Typecheck.Env.base state.typecheck.env
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

let read_code ?filename state line =
  let rec loop buf =
    let filename = Option.value ~default:(State.filename state) filename
    and source = Buffer.contents buf in
    match OneMl.Syntax.parse_repl ~filename source with
    | Left expr -> State.append source state, CExpr expr
    | Right file -> State.append source state, CEval file
    | exception Diagnostic.Error.Error diag when error_at_eof buf diag ->
      (match prompt " ..> " with
       | line ->
         Buffer.add_string buf line;
         Buffer.add_char buf '\n';
         loop buf
       | exception End_of_file ->
         print_newline ();
         let state = State.append source state in
         Diagnostic.print ~read:(State.read state) diag;
         state, CNone)
  in
  let buf = Buffer.create 64 in
  Buffer.add_string buf line;
  Buffer.add_char buf '\n';
  loop buf
;;

let read state =
  match prompt "1ml> " with
  | line ->
    (match String.trim line with
     | trimmed when String.starts_with ~prefix:"#" trimmed -> state, read_command line
     | "" -> state, CNone
     | _ -> read_code state line)
  | exception End_of_file ->
    print_newline ();
    state, CExit
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
