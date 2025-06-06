open OneMl
open OneMl.Util

let trace = Tracing.init ~width:7 "main"

let _ =
  Tracing.enable trace (open_out "/tmp/1ml-main.log");
  Tracing.enable OneMl.Elaborate.trace (open_out "/tmp/1ml-elab.log");
  Tracing.enable OneMl.Middle.trace (open_out "/tmp/1ml-middle.log");
  Tracing.enable OneMl.FOmega.trace (open_out "/tmp/1ml-omega.log")
;;

let run ?read parse lexbuf =
  try
    let ast = parse Lexer.token lexbuf in
    Tracing.log trace "surface" (fun fmt -> fmt "%a" Surface.PP.pp_expr ast);
    let _, typ, expr = Elaborate.Elab.expr Elaborate.Env.empty ast in
    Tracing.log trace "middle" (fun fmt -> fmt "%a" Middle.PP.pp_expr expr);
    Tracing.log trace "middle" (fun fmt -> fmt ":: %a" Middle.PP.pp_qtyp typ);
    let expr = Middle.Translate.expr Middle.Translate.Env.empty expr in
    Tracing.log trace "omega" (fun fmt -> fmt "%a" FOmega.PP.pp_expr expr);
    let typ = FOmega.Typecheck.infer FOmega.Typecheck.Env.empty expr in
    Tracing.log trace "omega" (fun fmt -> fmt ":: %a" FOmega.PP.pp_typ typ);
    let value = FOmega.Eval.eval (FOmega.Eval.Env.init Builtin.builtin) expr in
    Tracing.log trace "omega" (fun fmt -> fmt " = %a" FOmega.PP.pp_value value)
  with
  | Parser.Error ->
    let span = Some (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    let diag = Diagnostic.error ?span "parse error" in
    Format.eprintf "%a%!" (Diagnostic.pp ?read) diag
  | Diagnostic.Error.Error diag ->
    Format.eprintf "%a%!" (Diagnostic.pp ?read) diag;
    Printexc.print_backtrace stderr
;;

let repl_file = "<repl>"

let repl_read input = function
  | p when p = repl_file -> Some input
  | _ -> None
;;

let rec repl () =
  Format.printf "1ML> %!";
  let line = read_line () in
  let lexbuf = Lexing.from_string line in
  Lexing.set_filename lexbuf repl_file;
  run ~read:(repl_read line) Parser.repl lexbuf;
  repl ()
;;

let file path =
  let parse lexfun lexbuf = Surface.Ast.EStruct (Parser.file lexfun lexbuf)
  and lexbuf = Lexing.from_channel (open_in path) in
  Lexing.set_filename lexbuf path;
  run (fun lexfun lexbuf -> { data = parse lexfun lexbuf; span = None }) lexbuf
;;

let _ = if Array.length Sys.argv > 1 then file Sys.argv.(1) else repl ()
