open OneMl
module T = Lang.Typed

let prelude =
  "  type unit = extern \"unit\";\n\
  \  type bool = extern \"bool\";\n\
  \  type int = extern \"int\";\n\
  \  type float = extern \"float\";\n\
  \  type char = extern \"char\";\n\
  \  type string = extern \"string\";\n\
  \  Opt = { type t a = unit } :> { type t a };\n\
  \  Alt = { type t l r = unit } :> { type t l r };\n\
  \  opt = Opt.t;\n\
  \  alt = Alt.t;\n\
  \  "
;;

let pp_typ env = Pretty.Print.typ ~prec:0 ~env:(Typecheck.Env.base env)

let () =
  let prelude = Syntax.parse_string ~filename:"<prelude>" prelude in
  let state, _, _ = Typecheck.Session.next Typecheck.Session.empty prelude in
  let env = state.Typecheck.Session.env in
  let typ = Syntax.parse_typ ~filename:"<arg>" Sys.argv.(1) in
  let t = Typecheck.Check.modu_typ env typ in
  Format.printf "@[%a@]@." (pp_typ env) t
;;
