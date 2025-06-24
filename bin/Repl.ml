type cmd =
  | CEval of unit
  | CHelp
  | CExit
  | CCd of string

let help =
  "Available commands:\n\n\
   #help     - Display this help\n\
   #exit     - Exit interactive session\n\
   #cd \"dir\" - Change directory\n"
;;

(* let lex lexbuf =
  let rec aux acc lexbuf =
    match OneMl.Lexer.token lexbuf with
    | EOF -> List.rev acc
    | t -> aux (t :: acc) lexbuf
  in
  aux [] lexbuf
;;

let read_cmd line =
  let start = String.index line '#' + 1 in
  let lexbuf = Lexing.from_string (String.sub line start (String.length line - start)) in
  Lexing.set_filename lexbuf "<repl>";
  Lexing.set_position lexbuf { lexbuf.lex_curr_p with pos_cnum = start };
  match lex lexbuf with
  | [ ID "help" ] -> CHelp
  | [ ID "exit" ] -> CExit
  | [ ID "cd"; STRING dir ] -> CCd dir
  | _ -> failwith "unknown command"
;; *)

let read_code line = failwith "todo"

let read () =
  Printf.printf "1ml> %!";
  let line = read_line () in
  failwith "todo"
;;

(* if String.trim line |> String.starts_with ~prefix:"#"
  then read_cmd line
  else read_code line *)

let eval = function
  | CCd dir -> Sys.chdir dir
  | CExit -> exit 0
  | CHelp -> Printf.printf "\n%s\n" help
  | CEval prog -> Printf.eprintf "TODO\n"
;;
