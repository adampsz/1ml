open Util
open (val Trace.init ~scope:"elaborate" ())
module S = Lang.Typed
module T = Lang.FOmega

module Ex = struct
  type kind = Existential(T.Kind).t
  type tvar = Existential(T.TVar).t
  type typ = Existential(T.Type).t
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

module Mapping = struct
  type 'a t =
    | MRecord of (S.Var.t * 'a t) list
    | MType of 'a

  let empty = MRecord []

  let get p m =
    let rec aux = function
      | S.Path.Rev.RPNil, MType t -> Some t
      | S.Path.Rev.RPNil, _ -> invalid_arg "Mapping.get"
      | S.Path.Rev.RPProj (r, x), MRecord xs ->
        (match List.assoc_opt x xs with
         | Some m -> aux (r, m)
         | None -> None)
      | S.Path.Rev.RPProj _, _ -> invalid_arg "Mapping.get"
      | S.Path.Rev.RPApp (r, _), m -> aux (r, m)
    in
    let _, r = S.Path.rev p in
    aux (r, m)
  ;;

  let to_list m =
    let rec aux acc = function
      | MRecord xs -> List.fold_left (fun acc (_, m) -> aux acc m) acc xs
      | MType t -> t :: acc
    in
    List.rev (aux [] m)
  ;;

  let rec map f = function
    | MRecord xs -> MRecord (List.map (fun (x, m) -> x, map f m) xs)
    | MType t -> MType (f t)
  ;;

  let of_kind k =
    let arrow (Ex k1 : Ex.kind) (Ex k2 : Ex.kind) : Ex.kind =
      Ex (T.Kind.KArrow (k1, k2))
    in
    let rec aux args = function
      | S.Kind.KType -> MType (List.fold_right arrow args (Ex KType : Ex.kind))
      | S.Kind.KArrow (k1, k2) -> aux (args @ to_list (aux [] k1)) k2
      | S.Kind.KRecord xs -> MRecord (List.map (fun (x, k) -> x, aux args k) xs)
    in
    aux [] k
  ;;

  let of_tvar a =
    of_kind (S.TVar.kind a) |> map (fun (Ex k : Ex.kind) : Ex.tvar -> Ex (T.TVar.fresh k))
  ;;
end

module Env : sig
  type t

  val empty : t
  val add_var : S.Var.t -> t -> t * T.Var.t
  val find_var : S.Var.t -> t -> T.Var.t
  val add_tvar : S.TVar.t -> t -> t * Ex.tvar list
  val find_tvar : S.TVar.t -> t -> Ex.tvar Mapping.t
  val enter_mod : S.TVar.t -> t -> t
  val enter_field : S.Var.t -> t -> t
  val enter_lam : S.TVar.t -> t -> t
  val path : t -> S.TVar.t S.Path.t
end = struct
  type t =
    { vars : T.Var.t S.Var.Map.t
    ; tvars : Ex.tvar Mapping.t S.TVar.Map.t
    ; path : S.TVar.t S.Path.t
    }

  let empty = { vars = S.Var.Map.empty; tvars = S.TVar.Map.empty; path = S.Path.empty }

  let add_var x env =
    let x' = T.Var.fresh ~name:(S.Var.name x) () in
    debug (fun m -> m ~header:"var" "%a -> %a" S.Var.pp x T.Var.pp x');
    { env with vars = S.Var.Map.add x x' env.vars }, x'
  ;;

  let find_var x env = S.Var.Map.find x env.vars

  let add_tvar a env =
    let mapping = Mapping.of_tvar a in
    { env with tvars = S.TVar.Map.add a mapping env.tvars }, Mapping.to_list mapping
  ;;

  let find_tvar a env = S.TVar.Map.find a env.tvars
  let enter_mod a env = { env with path = S.Path.PVar a }
  let enter_field x env = { env with path = S.Path.PProj (env.path, x) }
  let enter_lam a env = { env with path = S.Path.PApp (env.path, a) }
  let path env = env.path
end

module Type = struct
  let rec typ env t =
    trace
      (fun m -> m ~header:"typ" "%a" S.Type.pp t)
      (fun t m -> m ~header:"typ" "~> %t" (fun ppf -> T.Type.pp ppf t))
    @@ fun () ->
    match S.Type.view t with
    | TInfer _ -> assert false
    | TPrim p -> T.Type.TPrim p
    | TAbstr p ->
      let (Ex t : Ex.typ) = path env p in
      (match T.Type.kind t with
       | KType -> t
       | _ -> assert false)
    | TArrow (_, t1, eff, t2) ->
      let a, t1 = S.Type.as_module t1 in
      let env, aks = Env.add_tvar a env in
      let t1 = typ (Env.enter_mod a env) t1
      and t2 = typ (Env.enter_lam a env) t2 in
      let t = Sugar.Type.eff_arrow t1 eff t2 in
      List.fold_right (fun (Ex a : Ex.tvar) t -> T.Type.TForall (a, t)) aks t
    | TRecord xs -> T.Type.TRecord (List.map (fun (x, t) -> S.Var.name x, typ env t) xs)
    | TSingletonType t -> Sugar.Type.singleton (typ env t)
    | TWrapped t -> Sugar.Type.wrap (typ env t)
    | TMod (a, t) ->
      let env, aks = Env.add_tvar a env in
      let t = typ (Env.enter_mod a env) t in
      List.fold_right (fun (Ex a : Ex.tvar) t -> T.Type.TExists (a, t)) aks t

  and path env p =
    trace
      (fun m -> m ~header:"path" "")
      (fun (Ex t : Ex.typ) m -> m ~header:"path" "~> %t" (fun ppf -> T.Type.pp ppf t))
    @@ fun () ->
    let rec aux = function
      | S.Path.PVar a -> Env.find_tvar a env, Fun.id
      | S.Path.PApp (p, tc) ->
        (match aux p with
         | m, app -> m, fun t1 -> List.fold_left Sugar.Type.app (app t1) (cons env tc))
      | S.Path.PProj (p, x) ->
        (match aux p with
         | MRecord ms, app -> List.assoc x ms, app
         | _, _ -> assert false)
    in
    match aux p with
    | MType (Ex t), app -> app (Ex (T.Type.TVar t))
    | _, _ -> assert false

  and cons env tc =
    let rec aux env = function
      | S.Type.CType t -> [ (Ex (typ env t) : Ex.typ) ]
      | S.Type.CLam (a1, tc) ->
        let lam (Ex a : Ex.tvar) (Ex c : Ex.typ) : Ex.typ = Ex (T.Type.TLam (a, c)) in
        let env, args = Env.add_tvar a1 env in
        let c2 = aux env tc in
        List.map (fun c -> List.fold_right lam args c) c2
      | S.Type.CRecord xs -> List.concat_map (fun (_, k) -> aux env k) xs
    in
    aux env tc
  ;;
end

module Elab = struct
  let rec expr env e =
    trace
      (fun m -> m ~header:"expr" "%a" S.Expr.pp e)
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
      aks1, T.Expr.ECond (EVar (Env.find_var x env), e1, e2)
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
        let env = Env.enter_mod S.TVar.empty env in
        let e = Sugar.Expr.eff_app e eff (snd (expr env e2)) in
        e
      in
      [], e
    | S.Expr.EType t -> [], Sugar.Expr.singleton (Type.typ env t)
    | S.Expr.EExtern (s, t) -> [], T.Expr.EExtern (s, Type.typ env t)
    | S.Expr.EWrap (e, _) -> [], Sugar.Expr.wrap (expr env e |> snd)
    | S.Expr.EUnwrap e -> [], Sugar.Expr.unwrap (snd (expr env e))
    | S.Expr.ESeal (e, tc, s) ->
      let x = T.Var.fresh () in
      let env', aks', e1 =
        let a', e = S.Expr.as_module e in
        let env', aks' = Env.add_tvar a' env in
        let env' = Env.enter_mod a' env' in
        let _, e1 = expr env' e in
        env', aks', e1
      in
      let e2 =
        let a, s = S.Type.as_module s in
        let env, aks = Env.add_tvar a env in
        let env = Env.enter_mod a env in
        Sugar.Expr.pack aks (Type.cons env' tc) (Type.typ env s) (EVar x)
      in
      [], Sugar.Expr.unpack aks' x e1 e2
    | S.Expr.EMod (a, e) ->
      let env, aks = Env.add_tvar a env in
      let env = Env.enter_mod a env in
      let aks', e = expr env e in
      let _ =
        let eq (Ex a : Ex.tvar) (Ex a' : Ex.tvar) =
          T.Kind.hequal (T.TVar.kind a) (T.TVar.kind a') <> None
        in
        assert (List.equal eq aks aks')
      in
      [], e
    | S.Expr.EUse e ->
      let rec aux = function
        | S.Path.PVar a -> Env.find_tvar a env
        | S.Path.PApp (p, _) -> aux p
        | S.Path.PProj (p, x) ->
          (match aux p with
           | MRecord ms -> List.assoc x ms
           | _ -> assert false)
      in
      let aks, e = expr env e in
      assert (List.is_empty aks);
      aux (Env.path env) |> Mapping.to_list, e

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
    | S.Expr.BVal (_, x, e) ->
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
