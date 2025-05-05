open One_ml.FOmega

let panic = function
  | ValPrim (ConstString s) -> failwith (Printf.sprintf "Program panicked: %s" s)
  | _ -> failwith "Program panicked: unknown error"
;;

let print = function
  | ValPrim (ConstString x) -> ValPrim (ConstUnit (Format.printf "%s\n%!" x))
  | x -> ValPrim (ConstUnit (Format.printf "%a\n%!" PP.pp_value x))
;;

let add x y =
  match x, y with
  | ValPrim (ConstInt x), ValPrim (ConstInt y) -> ValPrim (ConstInt (x + y))
  | _ -> assert false
;;

let sub x y =
  match x, y with
  | ValPrim (ConstInt x), ValPrim (ConstInt y) -> ValPrim (ConstInt (x - y))
  | _ -> assert false
;;

let mul x y =
  match x, y with
  | ValPrim (ConstInt x), ValPrim (ConstInt y) -> ValPrim (ConstInt (x * y))
  | _ -> assert false
;;

let div x y =
  match x, y with
  | ValPrim (ConstInt x), ValPrim (ConstInt y) -> ValPrim (ConstInt (x / y))
  | _ -> assert false
;;

let builtin =
  let unary f = ValNative f
  and binary f = ValNative (fun x -> ValNative (f x)) in
  function
  | "panic" -> Some (unary panic)
  | "print" -> Some (unary print)
  | "add" -> Some (binary add)
  | "sub" -> Some (binary sub)
  | "mul" -> Some (binary mul)
  | "div" -> Some (binary div)
  | _ -> None
;;

let run parse lexbuf =
  let aux expr =
    let value, typ = Eval.eval (Eval.env builtin) expr in
    Format.printf "%a :: %a\n%!" PP.pp_value value (PP.pp_typ []) typ
  in
  try parse Lexer.token lexbuf |> List.iter aux with
  | Error.Error e -> Format.eprintf "Error: %s\n%!" e
  | Parser.Error ->
    let pos = lexbuf.Lexing.lex_start_p in
    Format.eprintf "Parse error at %d:%d\n%!" pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
;;

let rec repl () =
  Format.printf "FOmega> %!";
  let parse lexfun lexbuf = [ Parser.topexpr lexfun lexbuf ]
  and lexbuf = Lexing.from_string (read_line ()) in
  run parse lexbuf;
  repl ()
;;

let file path =
  let lexbuf = Lexing.from_channel (open_in path) in
  run Parser.program lexbuf
;;

let _ = if Array.length Sys.argv > 1 then file Sys.argv.(1) else repl ()
