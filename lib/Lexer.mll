{
  open Parser

  let token_of_id = function
    | "and"      -> KW_AND
    | "else"     -> KW_ELSE
    | "external" -> KW_EXTERNAL
    | "false"    -> KW_FALSE
    | "fun"      -> KW_FUN
    | "if"       -> KW_IF
    | "in"       -> KW_IN
    | "include"  -> KW_INCLUDE
    | "let"      -> KW_LET
    | "local"    -> KW_LOCAL
    | "then"     -> KW_THEN
    | "true"     -> KW_TRUE
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
    | op -> (match String.get op 0 with
      | '*' when String.length op >= 2 && String.get op 1 = '*' -> P_OP_POW op
      | '*' | '/' | '%' -> P_OP_MUL op
      | '+' | '-'       -> P_OP_ADD op
      | '@' | '^'       -> P_OP_CONCAT op
      | '|' | '&'       -> P_OP_CMP op
      | '=' | '>' | '<' -> P_OP_CMP op
      | _   -> assert false)
  ;;

  let add_escape buf esc = match String.get esc 1 with
    | '0' -> Buffer.add_char buf '\000'
    | _   -> Buffer.add_string buf (Scanf.unescaped esc)
  ;;


  module Error = struct
    open Diagnostic.Error

    let span = function
      | Some lexbuf -> Some (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
      | None -> None
    ;;

    let unexpected_char ?lexbuf c = error ?span:(span lexbuf) "unexpected char %C" c
    let invalid_escape ?lexbuf c = error ?span:(span lexbuf) "invalid escape sequence %C" c
    let unterminated_string ?lexbuf = error ?span:(span lexbuf) "unterminated string"
    let unterminated_comment ?lexbuf = error ?span:(span lexbuf) "unterminated comment"
  end
}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']

let ident_start = ['A'-'Z' 'a'-'z' '_' '\'' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let ident_continue = ident_start | ['0'-'9']
let ident = ident_start ident_continue*

let operator_start = ['$' '&' '*' '+' '-' '/' '=' '>' '@' '^' '|' '%' '<']
let operator_condinue = operator_start | ['~' '!' '?' ':' '.']
let operator = operator_start operator_condinue*

let digit = ['0'-'9']
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let oct_digit = ['0'-'7']
let bin_digit = ['0'-'1']

let char_escape = ['\\' '\"' '\'' '0' 'n' 't' 'b' 'r' ' ']
let hex_escape = 'x' hex_digit hex_digit
let escape = '\\' (char_escape | hex_escape)

rule token = parse
  | eof     { EOF }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | blank+  { token lexbuf }
  | "(*"    { comment lexbuf; token lexbuf }

  | "{"  { P_BRACE_L }
  | "}"  { P_BRACE_R }
  | ","  { P_COMMA }
  | ":"  { P_COLON }
  | "."  { P_DOT }
  | "("  { P_PAREN_L }
  | ")"  { P_PAREN_R }
  | ":>" { P_SEAL }
  | ";"  { P_SEMI }

  | operator as op { token_of_op op }
  | ident    as id { token_of_id id }

  | digit (digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }

  | ("0x" | "0X") hex_digit (hex_digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }
  | ("0o" | "0O") oct_digit (oct_digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }
  | ("0b" | "0B") bin_digit (bin_digit | '_')* { INT (Lexing.lexeme lexbuf |> int_of_string) }

  | digit (digit | '_')* ('.' (digit | '_')*)? (['e' 'E'] ['+' '-']? digit (digit | '_')*)? { FLOAT (Lexing.lexeme lexbuf |> float_of_string) }

  | '"' { STRING (string (Buffer.create 64) lexbuf) }

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

  | eof  { Error.unterminated_comment ~lexbuf }
