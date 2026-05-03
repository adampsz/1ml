open Util
module T = Lang.Typed

module Env = struct
  type t = (T.Var.t * T.Type.t) list

  let empty = []
  let add a t env = (a, t) :: env
end

module Abstr = struct
  let rec concretize env = function
    | T.Kind.KEmpty -> T.Type.CEmpty
    | T.Kind.KType -> T.Type.CType (TInfer (T.UVar.fresh env) |> T.Type.wrap)
    | T.Kind.KArrow (k1, k2) ->
      let x = T.TVar.fresh k1 in
      T.Type.CLam (x, concretize (T.TVar.Set.add x env) k2)
    | T.Kind.KRecord ks ->
      T.Type.CRecord (List.map (fun (x, k) -> x, concretize env k) ks)
  ;;

  let rec find_in_env p out env =
    let aux = function
      | x, _ when String.starts_with ~prefix:"#" (T.Var.name x) -> None
      | x, t -> find_in_type p (T.Path.PProj (out, x)) t
    in
    List.find_map aux env

  and find_in_type p out t =
    match T.Type.view t with
    | TSingleton (TMod (a, t)) when T.TVar.is_empty a -> find_in_singleton p out t
    | TRecord ts -> find_in_env p out ts
    | TArrow (_, t1, (Explicit Pure | Implicit), t2) ->
      find_in_type p (T.Path.PApp (out, t1)) t2
    | _ -> None

  and find_in_singleton p out t =
    let rec generalize t = function
      | T.Path.PVar a -> T.Path.PVar a, t
      | T.Path.PProj (p, x) ->
        let out, t = generalize t p in
        T.Path.PProj (out, x), t
      | T.Path.PApp (p, T.Type.TMod (a, t1)) ->
        let c = concretize T.TVar.Set.empty (T.TVar.kind a) in
        let out, t = generalize (T.Subst.typ (T.Subst.one a c) t) p in
        T.Path.PApp (out, T.Subst.typ (T.Subst.one a c) t1), t
    in
    let out, t = generalize t out in
    if T.Equal.typ t (TAbstr p |> T.Type.wrap) then Some out else None
  ;;
end

module Print = struct
  let var ppf x = Format.pp_print_string ppf (T.Var.name x)

  let rec abstr ~env ppf p =
    let rec aux ppf = function
      | T.Path.PProj (T.Path.PVar _, x) -> Format.fprintf ppf "%a" var x
      | T.Path.PProj ((T.Path.PApp _ as p), x) ->
        Format.fprintf ppf "@[<hv 2>(@,%a@;<0 -2>)@]@,.%a" aux p var x
      | T.Path.PProj (p, x) -> Format.fprintf ppf "%a@,.%a" aux p var x
      | T.Path.PApp (p, a) -> Format.fprintf ppf "%a@ %a" aux p (typ ~env) a
      | T.Path.PVar _ -> assert false
    in
    Format.fprintf ppf "@[<2>%a@]" aux p

  and typ ~env ppf t =
    match T.Type.view t with
    | TInfer _ -> Format.pp_print_string ppf "_"
    | TAbstr p ->
      (match Abstr.find_in_env p (T.Path.PVar T.TVar.empty) env with
       | Some p -> abstr ~env ppf p
       | None -> Format.pp_print_string ppf "type")
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
      let rec pp ~env ppf t =
        match T.Type.view t with
        | TMod (_, t) -> pp ~env ppf t
        | TArrow (x, TMod (_, t1), eff, t2) ->
          let env = Env.add x t1 env in
          let pf = Format.fprintf ppf "%a@[<hv 2>(@,%a :@;<1 2>%a@;<0 -2>)@] %a@ %a" in
          pf tick eff var x (typ ~env) t1 arrow eff (pp ~env) t2
        | _ -> typ ~env ppf t
      in
      Format.fprintf ppf "@[<2>%a@]" (pp ~env) t
    | TRecord [] -> Format.pp_print_string ppf "{ }"
    | TRecord ts -> Format.pp_print_record var (typ ~env) ppf ts
    | TSingleton (TMod (a, t)) ->
      let pp = Format.fprintf ppf "@[<2>(=@ %a@;<0 -2>)@]" in
      pp (typ ~env) (TMod (a, t) |> T.Type.wrap)
    | TWrapped t -> Format.fprintf ppf "@[<2>wrap@ %a@]" (typ ~env) t
    | TMod (_, t) -> typ ~env ppf t
  ;;

  let typ env ppf t =
    Format.eprintf "ENV: %a@." (Format.pp_print_record T.Var.pp T.Type.pp) env;
    typ ~env ppf t
  ;;
end
