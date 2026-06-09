open Util
module T = Lang.Typed

module Env = struct
  include T.Env

  let with_vars xs env =
    List.fold_left
      (fun env (x, t) -> add_var x t env)
      (T.TVar.Set.fold add_tvar (domain env) empty)
      xs
  ;;

  let find f env =
    let rec aux seen = function
      | [] -> None
      | (x, _) :: xs when String.Set.mem (T.Var.name x) seen -> aux seen xs
      | (x, t) :: xs ->
        (match f x t with
         | Some y -> Some y
         | None -> aux (String.Set.add (T.Var.name x) seen) xs)
    in
    aux String.Set.empty (T.Env.vars env)
  ;;

  let at_root env =
    let root = T.TVar.Set.fold add_tvar (domain env) empty in
    List.fold_right (fun (x, t) env -> add_var x t env) (vars env) root
  ;;
end

module Abstr = struct
  type 'a display =
    | DNil
    | DProj of 'a display * T.Var.t
    | DApp of 'a display * 'a
  [@@deriving show]

  let rec concretize env = function
    | T.Kind.KType -> T.Type.CType (TInfer (T.UVar.fresh env T.Path.empty) |> T.Type.wrap)
    | T.Kind.KArrow (k1, k2) ->
      let x = T.TVar.fresh k1 in
      T.Type.CLam (x, concretize (T.TVar.Set.add x env) k2)
    | T.Kind.KRecord ks ->
      T.Type.CRecord (List.map (fun (x, k) -> x, concretize env k) ks)
  ;;

  let rec find_in_env p out env =
    let f x t =
      if String.starts_with ~prefix:"#" (T.Var.name x)
      then None
      else find_in_type p (DProj (out, x)) env t
    in
    Env.find f env

  and find_in_type p out env t =
    match T.Type.view t with
    | TSingletonType t -> find_in_singleton p out env t
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
        let tc = concretize (Env.domain env) (T.TVar.kind a) in
        let out, t = generalize (T.Subst.typ a (T.Subst.one tc) t) p in
        DApp (out, T.Subst.typ a (T.Subst.one tc) t1), t
    in
    let out, t = generalize t out in
    (* Reject types like `'a => (= type a)`, because they cause infinite loop *)
    let rec mentions t1 =
      match T.Type.view t1 with
      | _ when T.Equal.typ t1 (TAbstr p |> T.Type.wrap) -> true
      | TArrow (_, t1, _, t2) -> mentions t1 || mentions t2
      | TRecord ts -> List.exists (fun (_, t) -> mentions t) ts
      | TSingletonType t | TWrapped t | TMod (_, t) -> mentions t
      | TInfer _ | TAbstr _ | TPrim _ -> false
    in
    let rec circular = function
      | DNil -> false
      | DProj (out, _) -> circular out
      | DApp (out, t1) -> circular out || mentions t1
    in
    if T.Equal.typ ~unify:true t (TAbstr p |> T.Type.wrap) && not (circular out)
    then Some out
    else None
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
    let x = T.Var.name x in
    if String.length x > 0 && String.contains "$&*+-/=>@^|%<~!?:." x.[0]
    then Format.fprintf ppf "(%s)" x
    else Format.pp_print_string ppf x
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
    let root_env = Env.at_root env in
    let arg ~prec ppf t =
      match T.Type.view t with
      | TSingletonType t' -> typ ~prec ~env:root_env ppf t'
      | _ ->
        let pf = Format.fprintf ppf "@[(_:@ %a@])" in
        pf (typ ~prec:0 ~env:root_env) t
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

  and typ ~prec ~env ppf t =
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
      let arg ~prec ~env ppf = function
        | _, x, t when String.starts_with ~prefix:"#" (T.Var.name x) ->
          typ ~prec:(prec + 1) ~env ppf t
        | _, x, t -> Format.fprintf ppf (Prec.parens "%a:@ %a") var x (typ ~prec:0 ~env) t
      in
      let rec pp ~env ppf t =
        match T.Type.view t with
        | TMod (a, t) -> pp ~env:(Env.enter_mod a env) ppf t
        | TArrow (x, t1, eff, t2) ->
          let a, t1 = T.Type.as_module t1 in
          let env = Env.add_tvar a env in
          let pf = Format.fprintf ppf "%a%a %a@ %a" in
          let pf = pf tick eff (arg ~prec ~env:(Env.enter_mod a env)) (eff, x, t1) in
          pf arrow eff (pp ~env:(Env.add_var x t1 (Env.enter_lam a env))) t2
        | _ -> typ ~prec ~env ppf t
      in
      Format.fprintf ppf "@[<2>%a@]" (pp ~env) t
    | TRecord ts when is_tuple ts ->
      let entry ppf (k, v) = typ ~prec:0 ~env:(Env.enter_field k env) ppf v in
      tuple entry ppf ts
    | TRecord ts ->
      let env = ref env in
      let entry ppf (k, v) =
        let pf = Format.fprintf ppf "@[<2>%a:@ %a@]" in
        pf var k (typ ~prec:0 ~env:(Env.enter_field k !env)) v;
        env := Env.add_var k v !env
      in
      record entry ppf ts
    | TSingletonType t' when T.Type.is_path (Env.path env) t' ->
      Format.pp_print_string ppf "type"
    | TSingletonType t' ->
      Format.fprintf ppf "@[<2>(=@ type %a@;<0 -2>)@]" (typ ~prec:0 ~env) t'
    | TWrapped t -> Format.fprintf ppf "@[<2>wrap@ %a@]" (typ ~prec:3 ~env) t
    | TMod (a, t) -> typ ~prec ~env:(Env.enter_mod a env) ppf t
  ;;
end
