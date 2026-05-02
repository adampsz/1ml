open Util
open Lang.Surface

type entry =
  | Entry of string * file
  | Prelude of string

type t = entry list

let empty = []

let parse_file path =
  let chan = In_channel.open_text path in
  let lexbuf = Lexing.from_channel chan in
  Lexing.set_filename lexbuf path;
  Syntax.parse lexbuf
;;

let add name path t = Entry (name, parse_file path) :: t
let prelude name t = Prelude name :: t

let get t =
  let open Node in
  let aux = function
    | Prelude name -> make (BIncl (Private, make (EVar (make name))))
    | Entry (name, file) -> make (BVal (make name, map (fun xs -> EStruct xs) file))
  in
  make (List.map aux (List.rev t))
;;

let typecheck x = Typecheck.Check.file Typecheck.Env.empty x

let eval x =
  let extern = Eval.Extern.rossberg in
  let _ = Eval.Eval.eval (Eval.Env.init extern) x in
  ()
;;

let eval_fomega x =
  let extern = Eval.Extern.Compat.rossberg Eval.Extern.rossberg in
  let x = Elaborate.Elab.file Elaborate.Env.empty x in
  let _ = Lang.FOmega.Typecheck.check Lang.FOmega.Typecheck.Env.empty x in
  let _ = Lang.FOmega.Eval.eval (Lang.FOmega.Eval.Env.init extern) x in
  ()
;;
