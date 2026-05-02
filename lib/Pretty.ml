open Util
module T = Lang.Typed

module Env = struct
  type t = (T.Var.t * T.Type.t) list

  let empty = []
  let add a t env = (a, t) :: env
end

let var ppf x = Format.pp_print_string ppf (T.Var.name x)

let rec typ env ppf t =
  match T.Type.view t with
  | TInfer _ -> Format.pp_print_string ppf "_"
  | TAbstr p -> Format.pp_print_string ppf "type"
  | TPrim p ->
    (match p with
     | PUnit -> Format.pp_print_string ppf "unit"
     | PBool -> Format.pp_print_string ppf "bool"
     | PInt -> Format.pp_print_string ppf "int"
     | PFloat -> Format.pp_print_string ppf "float"
     | PChar -> Format.pp_print_string ppf "char"
     | PString -> Format.pp_print_string ppf "string")
  | TArrow _ ->
    let var ppf x = Format.pp_print_string ppf (T.Var.name x) in
    let arrow ppf = function
      | T.Type.Explicit Pure | T.Type.Implicit -> Format.pp_print_string ppf "=>"
      | T.Type.Explicit Impure -> Format.pp_print_string ppf "->"
    and tick ppf = function
      | T.Type.Implicit -> Format.pp_print_string ppf "'"
      | T.Type.Explicit _ -> ()
    in
    let rec pp env ppf t =
      match T.Type.view t with
      | TMod (_, t) -> pp env ppf t
      | TArrow (x, TMod (_, t1), eff, t2) ->
        let env = Env.add x t1 env in
        let pf = Format.fprintf ppf "%a@[<hv 2>(@,%a @;<1 2>%a@;<0 -2>)@] %a@ %a" in
        pf tick eff var x (typ env) t1 arrow eff (pp env) t2
      | _ -> typ env ppf t
    in
    Format.fprintf ppf "@[<2>%a@]" (pp env) t
  | TRecord ts -> Format.pp_print_record var (typ env) ppf ts
  | TSingleton (TMod (a, t)) ->
    Format.fprintf ppf "@[<2>(=@ %a@;<0 -2>)@]" (typ env) (TMod (a, t) |> T.Type.wrap)
  | TWrapped t -> Format.fprintf ppf "@[<2>wrap@ %a@]" (typ env) t
  | TMod (_, t) -> typ env ppf t
;;
