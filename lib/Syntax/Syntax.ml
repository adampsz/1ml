let parse_with entry lexbuf =
  try entry Lexer.token lexbuf with
  | Parser.Error as inner ->
    let span = Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf in
    Util.Diagnostic.Error.error ~span ~inner "parse error"
;;

let parse_file path =
  let chan = In_channel.open_text path in
  let lexbuf = Lexing.from_channel chan in
  Lexing.set_filename lexbuf path;
  parse_with Parser.file lexbuf
;;

let parse_stdin () =
  let lexbuf = Lexing.from_channel stdin in
  Lexing.set_filename lexbuf "<stdin>";
  parse_with Parser.file lexbuf
;;

let parse_repl ~filename input =
  let lexbuf = Lexing.from_string input in
  Lexing.set_filename lexbuf filename;
  parse_with Parser.repl_line lexbuf
;;
