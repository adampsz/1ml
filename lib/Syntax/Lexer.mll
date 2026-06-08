{
  open Util
  open Parser

  let token_of_id = function
    | "_"        -> P_UNDER
    | "and"      -> KW_AND
    | "do"       -> KW_DO
    | "else"     -> KW_ELSE
    | "extern"   -> KW_EXTERN
    | "fun"      -> KW_FUN
    | "if"       -> KW_IF
    | "in"       -> KW_IN
    | "include"  -> KW_INCLUDE
    | "let"      -> KW_LET
    | "open"     -> KW_OPEN
    | "then"     -> KW_THEN
    | "type"     -> KW_TYPE
    | "unwrap"   -> KW_UNWRAP
    | "with"     -> KW_WITH
    | "wrap"     -> KW_WRAP
    | id         -> ID id
  ;;

  let token_of_op = function
    | "->" -> P_ARROW
    | "=>" -> P_ARROW_FAT
    | "="  -> P_EQUAL
    | "&&" -> P_OP_AND "&&"
    | "||" -> P_OP_OR "||"
    | op when String.starts_with ~prefix:"**" op -> P_OP_POW op
    | op -> (match op.[0] with
      | '*' | '/' | '%' -> P_OP_MUL op
      | '+' | '-'       -> P_OP_ADD op
      | '@' | '^'       -> P_OP_CONCAT op
      | '|' | '&'       -> P_OP_CMP op
      | '=' | '>' | '<' -> P_OP_CMP op
      | _   -> assert false)
  ;;

  let add_escape buf esc = match esc.[1] with
    | '0' -> Buffer.add_char buf '\000'
    | _   -> Buffer.add_string buf (Scanf.unescaped esc)
  ;;

  let new_lines lexbuf =
    let rec aux i =
      if Bytes.get lexbuf.Lexing.lex_buffer i = '\010' then Lexing.new_line lexbuf;
      if i + 1 < lexbuf.lex_curr_pos then aux (i + 1)
    in
    aux lexbuf.lex_start_pos
  ;;

  module Error = struct
    exception Error

    let error ?lexbuf =
      let span = match lexbuf with
        | Some lexbuf -> Some (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
        | None -> None
      in
      Diagnostic.Error.error ?span ~cause:Error
    ;;

    let unexpected_char ?lexbuf c = error ?lexbuf "unexpected char %C" c
    let invalid_escape ?lexbuf c = error ?lexbuf "invalid escape sequence %C" c
    let unterminated_string ?lexbuf = error ?lexbuf "unterminated string"
    let unterminated_comment ?lexbuf = error ?lexbuf "unterminated comment"

    let _ =
      let f = function
        | Error -> Some "Syntax error"
        | _ -> None
      in
      Printexc.register_printer f
    ;;
  end
}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']

let ident_start = ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let ident_continue = ident_start | ['0'-'9'] | '\''
let ident = ident_start ident_continue*

let operator_start = ['$' '&' '*' '+' '-' '/' '=' '>' '@' '^' '|' '%' '<']
let operator_continue = operator_start | ['~' '!' '?' ':' '.']
let operator = operator_start operator_continue*

let digit = ['0'-'9']
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let oct_digit = ['0'-'7']
let bin_digit = ['0'-'1']

let char_escape = ['\\' '\"' '\'' '0' 'n' 't' 'b' 'r']
let hex_escape = 'x' hex_digit hex_digit
let escape = '\\' (char_escape | hex_escape)

rule token = parse
  | eof     { EOF }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | blank+  { token lexbuf }

  | "(*"    { comment lexbuf; token lexbuf }

  (* Hack: allow [P_PAREN_L; P_OP_MUL("*"); P_PAREN_R] token sequence, and do not treat it as a comment start *)
  | "(*" (blank | newline)* ")" { lexbuf.lex_curr_pos <- lexbuf.lex_start_pos + 1; P_PAREN_L }

  | "{"  { P_BRACE_L }
  | "}"  { P_BRACE_R }
  | ","  { P_COMMA }
  | ":"  { P_COLON }
  | "."  { P_DOT }
  | "("  { P_PAREN_L }
  | ")"  { P_PAREN_R }
  | ":>" { P_SEAL }
  | ";"  { P_SEMI }
  | "'"  { P_TICK }

  | operator as op { token_of_op op }
  | ident    as id { token_of_id id }

  | digit (digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }

  | ("0x" | "0X") hex_digit (hex_digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }
  | ("0o" | "0O") oct_digit (oct_digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }
  | ("0b" | "0B") bin_digit (bin_digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }

  | digit (digit | '_')* ('.' (digit | '_')*)? (['e' 'E'] ['+' '-']? digit (digit | '_')*)? { FLOAT (Lexing.lexeme lexbuf |> float_of_string) }

  | "'" ("'" | newline)   { lexbuf.lex_start_pos <- lexbuf.lex_start_pos + 1; Error.unexpected_char ~lexbuf '\'' }
  | "'" "\\0"         "'" { CHAR '\000' }
  | "'" (escape as e) "'" { CHAR ((Scanf.unescaped e).[0]) }
  | "'" (_ as c)      "'" { CHAR c }

  | '"'  { STRING (string (Buffer.create 64) lexbuf) }

  | _ as c { Error.unexpected_char ~lexbuf c }

and string buf = parse
  | '"'     { Buffer.contents buf }
  | escape  { add_escape buf (Lexing.lexeme lexbuf); string buf lexbuf }
  | newline { Error.unterminated_string ~lexbuf }
  | eof     { Error.unterminated_string ~lexbuf }

  | '\\' (_ as c) { Error.invalid_escape ~lexbuf c }

  | _ as c  { Buffer.add_char buf c; string buf lexbuf }

and comment = parse
  | "(*"    { comment lexbuf; comment lexbuf }
  | "*)"    { }
  | newline { Lexing.new_line lexbuf; comment lexbuf }
  | _       { comment lexbuf }

  | '(' (blank | newline)* '*' (blank | newline)* ')' { new_lines lexbuf; comment lexbuf }

  | eof  { Error.unterminated_comment ~lexbuf }
