let parse lexbuf =
  try Parser.file Lexer.token lexbuf with
  | Parser.Error as inner ->
    let span = Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf in
    Util.Diagnostic.Error.error ~span ~inner "parse error"
;;

let parse_file path =
  let chan = In_channel.open_text path in
  let lexbuf = Lexing.from_channel chan in
  Lexing.set_filename lexbuf path;
  parse lexbuf
;;

let parse_string ~filename source =
  let lexbuf = Lexing.from_string source in
  Lexing.set_filename lexbuf filename;
  parse lexbuf
;;
