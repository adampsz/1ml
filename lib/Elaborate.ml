open Util
open (val Trace.init ~scope:"elaborate" ())
module S = Lang.Typed
module T = Lang.FOmega

module Ex = struct
  type kind = Existential(T.Kind).t
  type tvar = Existential(T.TVar).t
  type typ = Existential(T.Type).t
end

module Flat = struct
  type 'a t =
    | FTyp of 'a
    | FRecord of (S.Var.t * 'a t) list [@polyprinter Format.pp_print_record S.Var.pp]
  [@@deriving show]

  let rec equal eq xs ys =
    match xs, ys with
    | FTyp x, FTyp y -> eq x y
    | FTyp _, _ -> false
    | FRecord xs, FRecord ys ->
      List.equal (fun (a, x) (b, y) -> S.Var.equal a b && equal eq x y) xs ys
    | FRecord _, _ -> false
  ;;

  let rec iter f = function
    | FTyp x -> f x
    | FRecord xs -> List.iter (fun (_, xs) -> iter f xs) xs
  ;;

  let rec fold_left f acc = function
    | FTyp x -> f acc x
    | FRecord xs -> List.fold_left (fun acc (_, xs) -> fold_left f acc xs) acc xs
  ;;

  let rec fold_right f xs acc =
    match xs with
    | FTyp x -> f x acc
    | FRecord xs -> List.fold_right (fun (_, xs) acc -> fold_right f xs acc) xs acc
  ;;

  let to_list xs = fold_right List.cons xs []

  let rec fold_left2 f acc xs ys =
    match xs, ys with
    | FTyp x, FTyp y -> f acc x y
    | FTyp _, _ -> invalid_arg "Flat.fold_left2"
    | FRecord xs, FRecord ys ->
      List.fold_left2 (fun acc (_, xs) (_, ys) -> fold_left2 f acc xs ys) acc xs ys
    | FRecord _, _ -> invalid_arg "Flat.fold_left2"
  ;;

  let rec fold_right2 f xs ys acc =
    match xs, ys with
    | FTyp x, FTyp y -> f x y acc
    | FTyp _, _ -> invalid_arg "Flat.fold_right2"
    | FRecord xs, FRecord ys ->
      List.fold_right2 (fun (_, xs) (_, ys) acc -> fold_right2 f xs ys acc) xs ys acc
    | FRecord _, _ -> invalid_arg "Flat.fold_right2"
  ;;

  let rec map f = function
    | FTyp x -> FTyp (f x)
    | FRecord xs -> FRecord (List.map (fun (x, xs) -> x, map f xs) xs)
  ;;

  let rec map2 f xs ys =
    match xs, ys with
    | FTyp x, FTyp y -> FTyp (f x y)
    | FRecord xs, FRecord ys ->
      FRecord (List.map2 (fun (x, xs) (_, ys) -> x, map2 f xs ys) xs ys)
    | _ -> invalid_arg "Flat.map2"
  ;;
end

module Flatten = struct
  let rec kind k =
    let rec aux acc = function
      | S.Kind.KEmpty -> None
      | S.Kind.KType -> Some (Flat.FTyp (acc (Ex T.Kind.KType : Ex.kind)))
      | S.Kind.KArrow (k1, k2) ->
        let arrow (Ex k1 : Ex.kind) (Ex k2 : Ex.kind) : Ex.kind = Ex (KArrow (k1, k2)) in
        let k1 = kind k1 in
        aux (fun k2 -> acc (Flat.fold_right arrow k1 k2)) k2
      | S.Kind.KRecord xs ->
        (match List.Assoc.filter_map (fun k -> aux acc k) xs with
         | [] -> None
         | xs -> Some (Flat.FRecord xs))
    in
    match aux Fun.id k with
    | Some k -> k
    | None -> Flat.FRecord []
  ;;

  let tvar k = Flat.map (fun (Ex k : Ex.kind) : Ex.tvar -> Ex (T.TVar.fresh k)) (kind k)
end

module Sugar = struct
  open Ex

  module Var = struct
    let typ = "%typ"
    let wrap = "%val"

    let eff = function
      | S.Type.Implicit -> "%implicit"
      | S.Type.Explicit Pure -> "%pure"
      | S.Type.Explicit Impure -> "%impure"
    ;;
  end

  module Type = struct
    let app (Ex t1 : typ) (Ex t2 : typ) : typ =
      match T.Type.kind t1 with
      | KArrow (k, _) ->
        (match T.Kind.hequal (T.Type.kind t2) k with
         | Some Equal -> Ex (T.Type.TApp (t1, t2))
         | _ -> assert false)
      | _ -> assert false
    ;;

    let singleton t = T.Type.TRecord [ Var.typ, T.Type.TArrow (t, T.Type.TRecord []) ]
    let wrap t = T.Type.TRecord [ Var.wrap, t ]
    let eff_arrow t1 eff t2 = T.Type.TArrow (t1, T.Type.TRecord [ Var.eff eff, t2 ])
  end

  module Expr = struct
    let pack a tc s e =
      let aux (Ex a : Ex.tvar) (Ex t : Ex.typ) rest s =
        match T.Kind.hequal (T.TVar.kind a) (T.Type.kind t) with
        | Some Equal ->
          let b, e = rest (T.Type.Subst.subst_one a t s) in
          let s = List.fold_right (fun (Ex a : Ex.tvar) s -> T.Type.TExists (a, s)) b s in
          (Ex a : Ex.tvar) :: b, T.Expr.EPack (t, e, a, s)
        | _ -> assert false
      in
      let _, e = List.fold_right2 aux a tc (Fun.const ([], e)) s in
      e
    ;;

    let unpack a x e1 e2 =
      let aux (Ex a : Ex.tvar) (x, e2) =
        let tmp = T.Var.fresh () in
        tmp, T.Expr.EUnpack (a, x, T.Expr.EVar tmp, e2)
      in
      match List.fold_right aux a (x, e2) with
      | _, T.Expr.EUnpack (a', x, _, e2) when a <> [] ->
        (* Minor optimization - drop top-level let in *)
        T.Expr.EUnpack (a', x, e1, e2)
      | x, e2 -> T.Expr.ELetIn (x, e1, e2)
    ;;

    let repack a x e1 e2 t =
      let tc = List.map (fun (Ex a : Ex.tvar) : Ex.typ -> Ex (T.Type.TVar a)) a in
      unpack a x e1 (pack a tc t e2)
    ;;

    let singleton t =
      T.Expr.ERecord [ Var.typ, T.Expr.ELam (T.Var.fresh (), t, T.Expr.ERecord []) ]
    ;;

    let wrap e = T.Expr.ERecord [ Var.wrap, e ]
    let unwrap e = T.Expr.EProj (e, Var.wrap)
    let eff_lam x t eff e = T.Expr.ELam (x, t, T.Expr.ERecord [ Var.eff eff, e ])
    let eff_app e1 eff e2 = T.Expr.EProj (T.Expr.EApp (e1, e2), Var.eff eff)
    let ty_lam (Ex a : Ex.tvar) e = T.Expr.ETyLam (a, e)
    let ty_app e (Ex t : typ) = T.Expr.ETyApp (e, t)
  end
end

module Env : sig
  type t

  val empty : t
  val add_var : S.Var.t -> t -> t * T.Var.t
  val find_var : S.Var.t -> t -> T.Var.t
  val enter_mod : S.TVar.t -> t -> t * Ex.tvar list
  val enter_field : S.Var.t -> t -> t
  val enter_arrow : S.TVar.t * S.Type.t -> t -> t
  val add_tvar : S.TVar.t -> t -> t * Ex.tvar list
  val find_tvar : S.TVar.t -> t -> Ex.tvar Flat.t
  val module_tvars : t -> Ex.tvar list
end = struct
  type t =
    { module_tvars : Ex.tvar Flat.t option
    ; vars : T.Var.t S.Var.Map.t
    ; tvars : Ex.tvar Flat.t S.TVar.Map.t
    }

  let empty = { module_tvars = None; vars = S.Var.Map.empty; tvars = S.TVar.Map.empty }

  let add_var x env =
    let x' = T.Var.fresh ~name:(S.Var.name x) () in
    debug (fun m -> m ~header:"var" "%a -> %a" S.Var.pp x T.Var.pp x');
    { env with vars = S.Var.Map.add x x' env.vars }, x'
  ;;

  let find_var x env =
    match S.Var.Map.find_opt x env.vars with
    | Some x' -> x'
    | None -> Format.kasprintf failwith "unbound variable: %a" S.Var.pp x
  ;;

  let add_tvar a env =
    let a' = Flatten.tvar (S.TVar.kind a) in
    if not (S.Kind.is_empty (S.TVar.kind a))
    then
      debug (fun m ->
        let pp_tvar ppf (Ex a : Ex.tvar) = T.TVar.pp ppf a in
        m ~header:"tvar" "%a -> %a" S.TVar.pp a (Flat.pp pp_tvar) a');
    { env with tvars = S.TVar.Map.add a a' env.tvars }, Flat.to_list a'
  ;;

  let enter_mod a env =
    let env, a' = add_tvar a env in
    { env with module_tvars = S.TVar.Map.find_opt a env.tvars }, a'
  ;;

  let enter_field x env =
    match env.module_tvars with
    | Some (Flat.FRecord xs) -> { env with module_tvars = List.assoc_opt x xs }
    | None -> env
    | _ -> invalid_arg "Env.enter_field"
  ;;

  let enter_arrow _ _ = failwith "todo enter arrow"

  let find_tvar a env =
    match S.TVar.Map.find_opt a env.tvars with
    | Some x -> x
    | None -> Format.kasprintf failwith "unbound type variable: %a" S.TVar.pp a
  ;;

  let module_tvars env =
    match env.module_tvars with
    | Some a -> Flat.to_list a
    | None -> []
  ;;
end

module Type = struct
  open Ex

  let rec typ env t =
    let (Ex t) = ctyp env t in
    match T.Type.kind t with
    | T.Kind.KType -> (t : T.Type.ttyp)
    | _ -> assert false

  and ctyp env t : Ex.typ =
    trace
      (fun m -> m ~header:"typ" "%a" S.Type.pp t)
      (fun (Ex t : Ex.typ) m -> m ~header:"typ" "~> %t" (fun ppf -> T.Type.pp ppf t))
    @@ fun () ->
    match S.Type.view t with
    | S.Type.TInfer _ ->
      Format.kasprintf failwith "unresolved type inference variable: %a" S.Type.pp t
    | S.Type.TPrim p -> Ex (T.Type.TPrim p)
    | S.Type.TAbstr p -> path env p
    | S.Type.TArrow (_, t1, eff, t2) ->
      let a, t1 = S.Type.as_module t1 in
      let env, a = Env.enter_mod a env in
      let t = Sugar.Type.eff_arrow (typ env t1) eff (typ env t2) in
      Ex (List.fold_right (fun (Ex a : Ex.tvar) t -> T.Type.TForall (a, t)) a t)
    | S.Type.TRecord xs ->
      Ex (T.Type.TRecord (List.map (fun (x, t) -> S.Var.name x, typ env t) xs))
    | S.Type.TSingleton t -> Ex (Sugar.Type.singleton (typ env t))
    | S.Type.TWrapped t -> Ex (Sugar.Type.wrap (typ env t))
    | S.Type.TMod (a, t) ->
      let env, a = Env.enter_mod a env in
      Ex (List.fold_right (fun (Ex a : Ex.tvar) t -> T.Type.TExists (a, t)) a (typ env t))

  and path env p =
    trace
      (fun m -> m ~header:"path" "")
      (fun (Ex t : Ex.typ) m -> m ~header:"path" "~> %t" (fun ppf -> T.Type.pp ppf t))
    @@ fun () ->
    let rec aux acc a r =
      match a, r with
      | Flat.FTyp (Ex x : Ex.tvar), S.Path.Rev.RPNil -> acc (Ex (T.Type.TVar x) : Ex.typ)
      | Flat.FRecord xs, S.Path.Rev.RPProj (r, x) -> aux acc (List.assoc x xs) r
      | a, S.Path.Rev.RPApp (r1, c2) ->
        let t2 = cons env c2 in
        aux (fun t1 -> List.fold_left Sugar.Type.app (acc t1) t2) a r1
      | _ -> assert false
    in
    let a, r = S.Path.rev p in
    aux Fun.id (Env.find_tvar a env) r

  and cons env c =
    let rec aux env acc = function
      | S.Type.CEmpty -> None
      | S.Type.CType t -> Some (Flat.FTyp (acc (ctyp env t)))
      | S.Type.CLam (a1, c2) ->
        let lam (Ex a1 : Ex.tvar) (Ex c2 : Ex.typ) : Ex.typ = Ex (TLam (a1, c2)) in
        let env, a1 = Env.add_tvar a1 env in
        aux env (fun c2 -> acc (List.fold_right lam a1 c2)) c2
      | S.Type.CRecord xs ->
        (match List.Assoc.filter_map (fun k -> aux env acc k) xs with
         | [] -> None
         | xs -> Some (Flat.FRecord xs))
    in
    match aux env Fun.id c with
    | Some c -> Flat.to_list c
    | None -> []
  ;;
end

module Elab = struct
  let rec expr env e =
    trace
      (fun m ->
         let tvar ppf (Ex a : Ex.tvar) = T.TVar.pp ppf a in
         let m = m ~header:"expr" "%a @@ %a" in
         m S.Expr.pp e (Format.pp_print_list tvar) (Env.module_tvars env))
      (fun (_, e) m -> m ~header:"expr" "~> %a" T.Expr.pp e)
    @@ fun () ->
    match e with
    | S.Expr.EVar x -> [], T.Expr.EVar (Env.find_var x env)
    | S.Expr.EConst c -> [], T.Expr.EConst c
    | S.Expr.ECond (x, e1, e2, _) ->
      let aks1, e1 = expr env e1
      and aks2, e2 = expr env e2 in
      let _ =
        let eq (Ex a1 : Ex.tvar) (Ex a2 : Ex.tvar) =
          T.Kind.hequal (T.TVar.kind a1) (T.TVar.kind a2) <> None
        in
        assert (List.equal eq aks1 aks2)
      in
      aks1, T.Expr.ECond (T.Expr.EVar (Env.find_var x env), e1, e2)
    | S.Expr.EStruct (xs, ts) ->
      let env, xs = List.fold_left_map bind env xs in
      let aux (x, _) = S.Var.name x, T.Expr.EVar (Env.find_var x env) in
      let e = T.Expr.ERecord (List.map aux ts) in
      let aks = List.concat_map fst xs in
      let tc = List.map (fun (Ex a : Ex.tvar) : Ex.typ -> Ex (T.Type.TVar a)) aks in
      let t = Type.typ env (S.Type.TRecord ts |> S.Type.wrap) in
      let e = Sugar.Expr.pack aks tc t e in
      aks, List.fold_right (fun (_, f) e -> f e) xs e
    | S.Expr.EProj (e, x, t) ->
      let tmp = T.Var.fresh ()
      and aks, e1 = expr env e in
      let e2 = T.Expr.EProj (EVar tmp, S.Var.name x) in
      let e = Sugar.Expr.repack aks tmp e1 e2 (Type.typ env t) in
      aks, e
    | S.Expr.EFun (x, t, eff, e) ->
      let a, t = S.Type.as_module t in
      let env, a = Env.add_tvar a env in
      let t1 = Type.typ env t in
      let env, x = Env.add_var x env in
      let aks, e = expr env e in
      assert (aks = []);
      let e = Sugar.Expr.eff_lam x t1 eff e in
      [], List.fold_right (fun (Ex a : Ex.tvar) e -> T.Expr.ETyLam (a, e)) a e
    | S.Expr.EApp (e1, tc, eff, e2) ->
      let e =
        let e = List.fold_left Sugar.Expr.ty_app (snd (expr env e1)) (Type.cons env tc) in
        let env, _ = Env.enter_mod S.TVar.empty env in
        let e = Sugar.Expr.eff_app e eff (snd (expr env e2)) in
        e
      in
      [], e
    | S.Expr.EType t -> [], Sugar.Expr.singleton (Type.typ env t)
    | S.Expr.EExtern (s, t) -> [], T.Expr.EExtern (s, Type.typ env t)
    | S.Expr.EWrap (x, _) -> [], Sugar.Expr.wrap (expr env x |> snd)
    | S.Expr.EUnwrap e -> [], Sugar.Expr.unwrap (snd (expr env e))
    | S.Expr.ESeal (e, tc, t) ->
      let a, e = S.Expr.as_module e in
      let x = T.Var.fresh () in
      let env', aks' = Env.enter_mod a env in
      let _, e1 = expr env' e in
      let e2 =
        let e = T.Expr.EVar x in
        let a = Env.module_tvars env in
        Sugar.Expr.pack a (Type.cons env' tc) (Type.typ env t) e
      in
      Env.module_tvars env, Sugar.Expr.unpack aks' x e1 e2
    | S.Expr.EMod (a, e) ->
      let env, aks = Env.enter_mod a env in
      let aks', e = expr env e in
      let _ =
        let eq (Ex a : Ex.tvar) (Ex a' : Ex.tvar) =
          T.Kind.hequal (T.TVar.kind a) (T.TVar.kind a') <> None
        in
        assert (List.equal eq aks aks')
      in
      [], e
    | S.Expr.EUse e -> Env.module_tvars env, snd (expr env e)

  and bind env b =
    trace
      (fun m -> m ~header:"bind" "%a" S.Expr.pp_bind b)
      (fun _ m -> m ~header:"bind" "")
    @@ fun () ->
    let proj tmp env (x, _) =
      let env, x' = Env.add_var x env in
      env, fun e -> T.Expr.ELetIn (x', EProj (EVar tmp, S.Var.name x), e)
    in
    match b with
    | S.Expr.BIncl (_, e, ts) ->
      let tmp = T.Var.fresh () in
      let aks, e = expr env e in
      let env, fs = List.fold_left_map (proj tmp) env ts in
      let f = List.fold_right (fun f e -> f e) fs in
      let f = Fun.compose (Sugar.Expr.unpack aks tmp e) f in
      env, (aks, f)
    | S.Expr.BVal (x, e) ->
      let env' = Env.enter_field x env in
      let aks, e = expr env' e in
      let env, x = Env.add_var x env in
      env, (aks, Sugar.Expr.unpack aks x e)
  ;;

  let file env node =
    trace
      (fun m ->
         let expr = Format.with_margin 140 S.Expr.pp_expr in
         let expr = Format.with_max_boxes Int.max_int expr in
         m ~header:"file" "%a" expr node)
      (fun t m ->
         let expr = Format.with_margin 140 T.Expr.pp in
         let expr = Format.with_max_boxes Int.max_int expr in
         m ~header:"file" "%a" expr t)
    @@ fun () -> expr env node |> snd
  ;;
end
