open Util
module T = Lang.Typed

module Env = struct
  type t = T.Env.t

  let empty = T.Env.empty
  let add_var = T.Env.add_var
  let add_tvar = T.Env.add_tvar
  let tvars = T.Env.domain

  let with_vars xs env =
    List.fold_left
      (fun env (x, t) -> add_var x t env)
      (T.TVar.Set.fold add_tvar (tvars env) empty)
      xs
  ;;

  let find f env =
    T.Var.Map.to_seq (T.Env.vars env) |> Seq.find_map (fun (x, t) -> f x t)
  ;;
end

module Abstr = struct
  type 'a display =
    | DNil
    | DProj of 'a display * T.Var.t
    | DApp of 'a display * 'a
  [@@deriving show]

  let rec concretize env = function
    | T.Kind.KType -> T.Type.CType (TInfer (T.UVar.fresh env) |> T.Type.wrap)
    | T.Kind.KArrow (k1, k2) ->
      let x = T.TVar.fresh k1 in
      T.Type.CLam (x, concretize (T.TVar.Set.add x env) k2)
    | T.Kind.KRecord ks ->
      T.Type.CRecord (List.map (fun (x, k) -> x, concretize env k) ks)
  ;;

  let rec find_in_env p out env =
    Env.find (fun x t -> find_in_type p (DProj (out, x)) env t) env

  and find_in_type p out env t =
    match T.Type.view t with
    | TSingleton t -> find_in_singleton p out env t
    | TRecord ts -> find_in_env p out (Env.with_vars ts env)
    | TArrow (x, t1, (Explicit Pure | Implicit), t2) ->
      let a, t1 = T.Type.as_module t1 in
      let env = Env.add_tvar a env in
      let env = Env.add_var x t1 env in
      find_in_type p (DApp (out, T.Type.as_type a t1)) env t2
    | TMod (a, t) -> find_in_type p out (Env.add_tvar a env) t
    | _ -> None

  and find_in_singleton p out env t =
    let rec generalize t = function
      | DNil -> DNil, t
      | DProj (p, x) ->
        let out, t = generalize t p in
        DProj (out, x), t
      | DApp (p, t1) ->
        let a, t1 = T.Type.as_module t1 in
        let c = concretize (Env.tvars env) (T.TVar.kind a) in
        let out, t = generalize (T.Subst.typ (T.Subst.one a c) t) p in
        DApp (out, T.Subst.typ (T.Subst.one a c) t1), t
    in
    let out, t = generalize t out in
    if T.Equal.typ ~unify:true t (TAbstr p |> T.Type.wrap) then Some out else None
  ;;
end

module Prec = struct
  let abstr ~prec = function
    | Abstr.DProj _ -> 3
    | Abstr.DApp _ -> 2
    | Abstr.DNil -> prec
  ;;

  let rec typ ~prec t =
    match T.Type.view t with
    | TAbstr _ -> prec
    | TArrow _ -> 1
    | TWrapped _ -> 1
    | TMod (_, t) -> typ ~prec t
    | _ -> Int.max_int
  ;;

  let parens fmt = "@[<hv 2>(@," ^^ fmt ^^ "@;<0 -2>)@]"
  let wrap p p' ppf f = if p > p' then Format.fprintf ppf (parens "%a") f p' else f ppf p'
end

module Print = struct
  let var ppf x =
    if String.starts_with ~prefix:"#" (T.Var.name x)
    then Format.pp_print_string ppf "_"
    else Format.pp_print_string ppf (T.Var.name x)
  ;;

  let record fmt ppf = function
    | [] -> Format.pp_print_string ppf "{ }"
    | entries ->
      let is_first = ref true in
      let aux entry =
        if !is_first then is_first := false else Format.fprintf ppf ";@ ";
        fmt ppf entry
      in
      let br = Format.pp_print_custom_break ~fits:("", 1, "") ~breaks:(";", -2, "") in
      Format.fprintf ppf "{@[<hv 1>@;";
      List.iter aux entries;
      Format.fprintf ppf "%t@]}" br
  ;;

  let is_tuple entries =
    let rec aux i = function
      | [] -> i >= 2
      | (k, _) :: rest when T.Var.name k = Int.to_string i -> aux (i + 1) rest
      | _ -> false
    in
    aux 0 entries
  ;;

  let tuple fmt ppf entries =
    let is_first = ref true in
    let aux entry =
      if !is_first then is_first := false else Format.fprintf ppf ",@ ";
      fmt ppf entry
    in
    Format.fprintf ppf "(@[<hv 0>";
    List.iter aux entries;
    Format.fprintf ppf "@])"
  ;;

  let rec abstr ~prec ~env ppf p =
    let arg ~prec ppf t =
      match T.Type.view t with
      | TSingleton t' -> typ ~path:T.Path.empty ~prec ~env ppf t'
      | _ ->
        let pf = Format.fprintf ppf "@[(_:@ %a@])" in
        pf (typ ~path:T.Path.empty ~prec:0 ~env) t
    in
    let rec aux ~prec ppf p =
      Prec.wrap prec (Prec.abstr ~prec p) ppf
      @@ fun ppf prec ->
      match p with
      | Abstr.DProj (Abstr.DNil, x) -> Format.fprintf ppf "%a" var x
      | Abstr.DProj (p, x) -> Format.fprintf ppf "%a@,.%a" (aux ~prec) p var x
      | Abstr.DApp (p, a) ->
        Format.fprintf ppf "%a@ %a" (aux ~prec) p (arg ~prec:(prec + 1)) a
      | Abstr.DNil -> assert false
    in
    Format.fprintf ppf "@[<2>%a@]" (aux ~prec) p

  and typ ~path ~prec ~env ppf t =
    Prec.wrap prec (Prec.typ ~prec t) ppf
    @@ fun ppf prec ->
    match T.Type.view t with
    | TInfer _ -> Format.pp_print_string ppf "_"
    | TAbstr p ->
      (match Abstr.find_in_env p Abstr.DNil env with
       | Some p -> abstr ~prec ~env ppf p
       | None -> Format.pp_print_string ppf "<abstr>")
    | TPrim p ->
      (match p with
       | PUnit -> Format.pp_print_string ppf "unit"
       | PBool -> Format.pp_print_string ppf "bool"
       | PInt -> Format.pp_print_string ppf "int"
       | PFloat -> Format.pp_print_string ppf "float"
       | PChar -> Format.pp_print_string ppf "char"
       | PString -> Format.pp_print_string ppf "string")
    | TArrow _ ->
      let arrow ppf = function
        | T.Type.Explicit Pure | T.Type.Implicit -> Format.pp_print_string ppf "=>"
        | T.Type.Explicit Impure -> Format.pp_print_string ppf "->"
      and tick ppf = function
        | T.Type.Implicit -> Format.pp_print_string ppf "'"
        | T.Type.Explicit _ -> ()
      in
      let is_type_arg ~path t =
        match T.Type.view t with
        | TSingleton t' -> T.Type.is_path path t'
        | _ -> false
      in
      let arg ~path ~prec ~env ppf = function
        | _, x, t when String.starts_with ~prefix:"#" (T.Var.name x) ->
          typ ~path ~prec:(prec + 1) ~env ppf t
        | _, x, t ->
          Format.fprintf ppf (Prec.parens "%a:@ %a") var x (typ ~path ~prec:0 ~env) t
      in
      let rec pp ~path ~env ppf t =
        match T.Type.view t with
        | TMod (a, t) -> pp ~path:(T.Path.PVar a) ~env:(Env.add_tvar a env) ppf t
        | TArrow (x, t1, eff, t2) ->
          let a, t1 = T.Type.as_module t1 in
          let env = Env.add_tvar a env in
          let pf = Format.fprintf ppf "%a%a %a@ %a" in
          let pf = pf tick eff (arg ~path:(T.Path.PVar a) ~prec ~env) (eff, x, t1) in
          pf arrow eff (pp ~path:(PApp (path, a)) ~env:(Env.add_var x t1 env)) t2
        | _ -> typ ~path ~prec ~env ppf t
      in
      Format.fprintf ppf "@[<2>%a@]" (pp ~path ~env) t
    | TRecord ts when is_tuple ts ->
      let entry ppf (k, v) =
        let path = T.Path.PProj (path, k) in
        typ ~path ~prec:0 ~env ppf v
      in
      tuple entry ppf ts
    | TRecord ts ->
      let env = ref env in
      let entry ppf (k, v) =
        let path = T.Path.PProj (path, k) in
        Format.fprintf ppf "@[<2>%a:@ %a@]" var k (typ ~path ~prec:0 ~env:!env) v;
        env := Env.add_var k v !env
      in
      record entry ppf ts
    | TSingleton t' when T.Type.is_path path t' -> Format.pp_print_string ppf "type"
    | TSingleton t' ->
      Format.fprintf
        ppf
        "@[<2>(=@ type %a@;<0 -2>)@]"
        (typ ~path ~prec:0 ~env)
        t'
    | TWrapped t ->
      Format.fprintf ppf "@[<2>wrap@ %a@]" (typ ~path ~prec:3 ~env) t
    | TMod (a, t) -> typ ~path:(T.Path.PVar a) ~prec ~env:(Env.add_tvar a env) ppf t
  ;;
end
