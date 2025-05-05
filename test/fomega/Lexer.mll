{
  open Parser

  let token_of_id = function
    | "unit"     -> KW_UNIT
    | "bool"     -> KW_BOOL
    | "int"      -> KW_INT
    | "string"   -> KW_STRING
    | "true"     -> KW_TRUE
    | "false"    -> KW_FALSE
    | "as"       -> KW_AS
    | "exists"   -> KW_EXISTS
    | "external" -> KW_EXTERNAL
    | "forall"   -> KW_FORALL
    | "in"       -> KW_IN
    | "lambda"   -> KW_LAMBDA
    | "let"      -> KW_LET
    | "pack"     -> KW_PACK
    | "unpack"   -> KW_UNPACK
    | id         -> IDENT id
}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']

let ident_start = ['A'-'Z' 'a'-'z' '_' '\'' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let ident_continue = ident_start | ['0'-'9']
let ident = ident_start ident_continue*

rule token = parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | blank+  { token lexbuf }
  | "//"    { line_comment lexbuf; token lexbuf }
  | "/*"    { block_comment lexbuf; token lexbuf }

  | ident as id { token_of_id id }

  | ['0'-'9']+ as i { INT (int_of_string i) }

  | '"' { string (Buffer.create 64) lexbuf }

  | "->"      { P_ARROW }
  | "{"       { P_BRACE_L }
  | "}"       { P_BRACE_R }
  | "["       { P_BRACKET_L }
  | "]"       { P_BRACKET_R }
  | ":"       { P_COLON }
  | ","       { P_COMMA }
  | "."       { P_DOT }
  | "="       { P_EQ }
  | "("       { P_PAREN_L }
  | ")"       { P_PAREN_R }
  | "*"       { P_STAR }
  | ";"       { P_SEMI }

  | eof     { EOF }

and string buf = parse
    | '"'    { STRING (Buffer.contents buf); }
    | "\\n"  { Buffer.add_char buf '\n'; string buf lexbuf }

    | '\\' | '"' | newline { failwith "Invalid string char" }

    | _ as c { Buffer.add_char buf c; string buf lexbuf }

and line_comment = parse
  | newline { Lexing.new_line lexbuf }
  | _       { line_comment lexbuf }

and block_comment = parse
  | "/*"    { block_comment lexbuf; block_comment lexbuf }
  | "*/"    { }
  | newline { Lexing.new_line lexbuf; block_comment lexbuf }
  | _       { block_comment lexbuf }
