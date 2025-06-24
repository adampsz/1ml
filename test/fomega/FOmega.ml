open Lang.FOmega
open Lang.FOmega.Value

let panic = function
  | VPrim (CString s) -> failwith (Printf.sprintf "Program panicked: %s" s)
  | _ -> failwith "Program panicked: unknown error"
;;

let print = function
  | VPrim (CString x) -> VPrim (CUnit (Format.printf "%s\n%!" x))
  | x -> VPrim (CUnit (Format.printf "%a\n%!" PP.value x))
;;

let add x y =
  match x, y with
  | VPrim (CInt x), VPrim (CInt y) -> VPrim (CInt (x + y))
  | _ -> assert false
;;

let sub x y =
  match x, y with
  | VPrim (CInt x), VPrim (CInt y) -> VPrim (CInt (x - y))
  | _ -> assert false
;;

let mul x y =
  match x, y with
  | VPrim (CInt x), VPrim (CInt y) -> VPrim (CInt (x * y))
  | _ -> assert false
;;

let div x y =
  match x, y with
  | VPrim (CInt x), VPrim (CInt y) -> VPrim (CInt (x / y))
  | _ -> assert false
;;

let builtin =
  let unary f = VExternal f
  and binary f = VExternal (fun x -> VExternal (f x)) in
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
    let typ = Typecheck.infer Typecheck.Env.empty expr
    and value = Eval.eval (Eval.Env.empty builtin) expr in
    Format.printf "%a :: %a@." PP.value value PP.typ typ
  in
  try parse Lexer.token lexbuf |> List.iter aux with
  | Util.Diagnostic.Error.Error diag ->
    Format.eprintf "%a\n%!" (Util.Diagnostic.pp ?read:None) diag
;;

let rec repl () =
  Format.printf "FOmega> %!";
  let parse lexfun lexbuf = [ Parser.repl lexfun lexbuf ]
  and lexbuf = Lexing.from_string (read_line ()) in
  run parse lexbuf;
  repl ()
;;

let file path =
  let lexbuf = Lexing.from_channel (open_in path) in
  run Parser.program lexbuf
;;

let _ = if Array.length Sys.argv > 1 then file Sys.argv.(1) else repl ()
