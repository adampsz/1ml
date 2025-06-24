open Util

module Module : sig
  type t

  val create : ?prelude:t -> unit -> t
  val add_file : Lang.Surface.file -> t -> t
  val add_from_lexbuf : Lexing.lexbuf -> t -> t
  val add_from_channel : string -> In_channel.t -> t -> t
  val add_from_file : string -> t -> t
end = struct
  type t =
    Typecheck.Check.Env.t
    * Elaborate.Env.t
    * Lang.FOmega.Typecheck.Env.t
    * Lang.FOmega.Eval.Env.t

  let create ?prelude () =
    let m =
      match prelude with
      | Some env -> env
      | None ->
        ( Typecheck.Check.Env.create ()
        , Elaborate.Env.empty
        , Lang.FOmega.Typecheck.Env.empty
        , Lang.FOmega.Eval.Env.empty (fun _ -> assert false) )
    in
    m
  ;;

  let add_file file ((tenv, eenv, fenv, venv) : t) =
    let file = Typecheck.Check.file tenv file in
    let file = Elaborate.Elab.file eenv file in
    let tmp = Format.formatter_of_out_channel (open_out "trace/fomega.log") in
    Format.pp_set_margin tmp 160;
    Format.fprintf tmp "%a@." Lang.FOmega.PP.expr file;
    let _ = Lang.FOmega.Typecheck.infer fenv file in
    let _ = Lang.FOmega.Eval.eval venv file in
    ((tenv, eenv, fenv, venv) : t)
  ;;

  let add_from_lexbuf lexbuf = add_file (Syntax.parse lexbuf)

  let add_from_channel name chan =
    let lexbuf = Lexing.from_channel chan in
    Lexing.set_filename lexbuf name;
    add_from_lexbuf lexbuf
  ;;

  let add_from_file path =
    let chan = In_channel.open_text path in
    add_from_channel path chan
  ;;
end
