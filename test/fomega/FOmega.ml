open OneMl.FOmega
open OneMl.FOmega.Value

let panic = function
  | VPrim (ConstString s) -> failwith (Printf.sprintf "Program panicked: %s" s)
  | _ -> failwith "Program panicked: unknown error"
;;

let print = function
  | VPrim (ConstString x) -> VPrim (ConstUnit (Format.printf "%s\n%!" x))
  | x -> VPrim (ConstUnit (Format.printf "%a\n%!" PP.pp_value x))
;;

let add x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x + y))
  | _ -> assert false
;;

let sub x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x - y))
  | _ -> assert false
;;

let mul x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x * y))
  | _ -> assert false
;;

let div x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x / y))
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
    and value = Eval.eval (Eval.Env.init builtin) expr in
    Format.printf "%a :: %a\n%!" PP.pp_value value PP.pp_typ typ
  in
  try parse Lexer.token lexbuf |> List.iter aux with
  | OneMl.Diagnostic.Error.Error diag ->
    Format.eprintf "%a\n%!" (OneMl.Diagnostic.pp ?read:None) diag
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
