open OneMl
module T = Lang.Typed

let pp_typ env = Pretty.Print.typ ~prec:0 ~env:(Typecheck.Env.base env)

let () =
  let prelude = Syntax.parse_file "prelude.1ml" in
  let state, _, _ = Typecheck.Session.next Typecheck.Session.empty prelude in
  let env = state.Typecheck.Session.env in
  let typ = Syntax.parse_typ ~filename:"<arg>" Sys.argv.(1) in
  let t = Typecheck.Check.modu_typ env typ in
  Format.printf "@[%a@]@." (pp_typ env) t
;;
