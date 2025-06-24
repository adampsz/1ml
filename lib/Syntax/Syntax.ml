let parse lexbuf =
  try Parser.file Lexer.token lexbuf with
  | Parser.Error as inner ->
    let span = Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf in
    Util.Diagnostic.Error.error ~span ~inner "parse error"
;;
