let parse_with entry lexbuf =
  try entry Lexer.token lexbuf with
  | Parser.Error as inner ->
    let span = Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf in
    Util.Diagnostic.Error.error ~span ~inner "parse error"
;;

let parse_string_with entry ~filename input =
  let lexbuf = Lexing.from_string input in
  Lexing.set_filename lexbuf filename;
  parse_with entry lexbuf
;;

let parse_file path =
  let chan =
    try In_channel.open_text path with
    | Sys_error _ as cause ->
      Util.Diagnostic.Error.error ~cause "Could not open file `%s'" path
  in
  let lexbuf = Lexing.from_channel chan in
  Lexing.set_filename lexbuf path;
  parse_with Parser.file lexbuf
;;

let parse_stdin () =
  let lexbuf = Lexing.from_channel stdin in
  Lexing.set_filename lexbuf "<stdin>";
  parse_with Parser.file lexbuf
;;

let parse_typ ~filename input = parse_string_with Parser.typ_eof ~filename input

let parse_repl ~filename input =
  let pos diag =
    match Util.Diagnostic.span diag with
    | Some (_, p) -> p.pos_cnum
    | _ -> 0
  in
  try Either.Left (parse_string_with Parser.expr_eof ~filename input) with
  | Util.Diagnostic.Error.Error diag ->
    (try Either.Right (parse_string_with Parser.file ~filename input) with
     | Util.Diagnostic.Error.Error diag' when pos diag' < pos diag ->
       raise (Util.Diagnostic.Error.Error diag))
;;
