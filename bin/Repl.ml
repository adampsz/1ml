open OneMl
module S = Lang.Surface
module T = Lang.Typed

type cmd =
  | CEval of string * S.bind list S.Node.t
  | CExpr of string * S.expr
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
    let i = List.length xs - i - 1 in
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

  let pretty_env state =
    List.fold_left
      (fun env (x, t) -> Pretty.Env.add_var x t env)
      Pretty.Env.empty
      state.typecheck.ts
  ;;
end

let it_name = "it"

let wrap_expr_as_bind expr =
  let span = S.Node.span expr in
  let it = S.Node.make ?span it_name in
  let bind = S.Node.make ?span (S.BVal (S.Public, it, expr)) in
  S.Node.make ?span [ bind ]
;;

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

let try_parse f source ~filename =
  try Ok (f ~filename source) with
  | Diagnostic.Error.Error diag -> Error diag
;;

let read_code ?filename state line =
  let rec loop buf =
    let filename = Option.value ~default:(State.filename state) filename
    and source = Buffer.contents buf in
    match OneMl.Syntax.parse_repl ~filename source with
    | Left expr -> State.append source state, CExpr (source, expr)
    | Right file ->
      State.append source state, CEval (source, OneMl.Lang.Surface.Node.make file)
    | exception Diagnostic.Error.Error diag when error_at_eof buf diag ->
      (match prompt "..> " with
       | line ->
         Buffer.add_string buf line;
         Buffer.add_char buf '\n';
         loop buf
       | exception End_of_file ->
         print_newline ();
         let state = State.append source state in
         Diagnostic.print ~read:(State.read state) diag;
         state, CEval (source, S.Node.make []))
    | exception Diagnostic.Error.Error diag ->
      let state = State.append source state in
      Diagnostic.print ~read:(State.read state) diag;
      state, CEval (source, S.Node.make [])
  in
  let buf = Buffer.create 64 in
  Buffer.add_string buf line;
  Buffer.add_char buf '\n';
  loop buf
;;

let read state =
  match prompt "1ml> " with
  | line ->
    let trimmed = String.trim line in
    if String.starts_with ~prefix:"#" trimmed
    then state, read_command line
    else read_code state line
  | exception End_of_file ->
    print_newline ();
    state, CExit
;;

let print_result env t v =
  let pf = Format.printf "@[<2> :@ %a =@ %a@]@." in
  pf (Pretty.Print.typ ~prec:0 ~env) t Eval.Value.pp v
;;

let eval state = function
  | CExit -> exit 0
  | CHelp ->
    print_string help;
    flush stdout;
    state
  | CEval (_, xs) ->
    (try fst (State.next xs state) with
     | Diagnostic.Error.Error diag ->
       Diagnostic.print ~read:(State.read state) diag;
       state)
  | CExpr (_, expr) ->
    (try
       let state, ts = State.next (wrap_expr_as_bind expr) state in
       (match List.find_opt (fun (x, _) -> T.Var.name x = it_name) (List.rev ts) with
        | Some (x, t) ->
          let v = Eval.Env.find x state.eval in
          print_result (State.pretty_env state) t v
        | None -> ());
       state
     with
     | Diagnostic.Error.Error diag ->
       Diagnostic.print ~read:(State.read state) diag;
       state)
;;
