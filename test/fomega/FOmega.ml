open Lang.FOmega
open Lang.FOmega.Value

let panic = function
  | VConst (CString s) -> failwith (Printf.sprintf "Program panicked: %s" s)
  | _ -> failwith "Program panicked: unknown error"
;;

let print = function
  | VConst (CString x) -> VConst (CUnit (Format.printf "%s\n%!" x))
  | x -> VConst (CUnit (Format.printf "%a\n%!" Value.pp x))
;;

let add x y =
  match x, y with
  | VConst (CInt x), VConst (CInt y) -> VConst (CInt (x + y))
  | _ -> assert false
;;

let sub x y =
  match x, y with
  | VConst (CInt x), VConst (CInt y) -> VConst (CInt (x - y))
  | _ -> assert false
;;

let mul x y =
  match x, y with
  | VConst (CInt x), VConst (CInt y) -> VConst (CInt (x * y))
  | _ -> assert false
;;

let div x y =
  match x, y with
  | VConst (CInt x), VConst (CInt y) -> VConst (CInt (x / y))
  | _ -> assert false
;;

let builtin =
  let unary f = VLam f
  and binary f = VLam (fun x -> VLam (f x))
  and typ f = VTyLam (fun _ -> f) in
  function
  | "panic" -> Some (unary panic)
  | "print" -> Some (typ (unary print))
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
    Format.printf "@[<2>%a ::@ %a@]@." Value.pp value Type.pp typ
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
