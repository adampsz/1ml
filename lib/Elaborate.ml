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
    | FRecord of (S.Var.t * 'a t) list

  let record = function
    | [] -> None
    | xs -> Some (FRecord xs)
  ;;

  let field x = function
    | None -> []
    | Some y -> [ x, y ]
  ;;

  let fields = function
    | None -> []
    | Some (FRecord xs) -> xs
    | Some (FTyp _) -> invalid_arg "Flat.fields"
  ;;

  let equal eq xs ys =
    let rec aux xs ys =
      match xs, ys with
      | FTyp x, FTyp y -> eq x y
      | FRecord xs, FRecord ys ->
        List.equal (fun (a, x) (b, y) -> S.Var.equal a b && aux x y) xs ys
      | _, _ -> false
    in
    Option.equal aux xs ys
  ;;

  let iter f xs =
    let rec aux = function
      | FTyp x -> f x
      | FRecord xs -> List.iter (fun (_, xs) -> aux xs) xs
    in
    Option.iter aux xs
  ;;

  let fold_left f acc xs =
    let rec aux acc = function
      | FTyp x -> f acc x
      | FRecord xs -> List.fold_left (fun acc (_, xs) -> aux acc xs) acc xs
    in
    Option.fold ~none:acc ~some:(aux acc) xs
  ;;

  let fold_right f xs acc =
    let rec aux acc = function
      | FTyp x -> f x acc
      | FRecord xs -> List.fold_right (fun (_, xs) acc -> aux acc xs) xs acc
    in
    Option.fold ~none:acc ~some:(aux acc) xs
  ;;

  let fold_left2 f acc xs ys =
    let rec aux acc xs ys =
      match xs, ys with
      | FTyp x, FTyp y -> f acc x y
      | FRecord xs, FRecord ys ->
        List.fold_left2 (fun acc (_, xs) (_, ys) -> aux acc xs ys) acc xs ys
      | _, _ -> invalid_arg "Flat.fold_left2"
    in
    match xs, ys with
    | Some xs, Some ys -> aux acc xs ys
    | None, None -> acc
    | _, _ -> invalid_arg "Flat.fold_left2"
  ;;

  let fold_right2 f xs ys acc =
    let rec aux xs ys acc =
      match xs, ys with
      | FTyp x, FTyp y -> f x y acc
      | FRecord xs, FRecord ys ->
        List.fold_right2 (fun (_, xs) (_, ys) acc -> aux xs ys acc) xs ys acc
      | _, _ -> invalid_arg "Flat.fold_right2"
    in
    match xs, ys with
    | Some xs, Some ys -> aux xs ys acc
    | None, None -> acc
    | _, _ -> invalid_arg "Flat.fold_right2"
  ;;

  let cardinal = fold_left (fun acc _ -> acc + 1) 0

  let map f xs =
    let rec aux = function
      | FTyp x -> FTyp (f x)
      | FRecord xs -> FRecord (List.map (fun (x, xs) -> x, aux xs) xs)
    in
    Option.map aux xs
  ;;

  let map2 f xs ys =
    let rec aux xs ys =
      match xs, ys with
      | FTyp x, FTyp y -> FTyp (f x y)
      | FRecord xs, FRecord ys ->
        FRecord (List.map2 (fun (x, xs) (_, ys) -> x, aux xs ys) xs ys)
      | _ -> invalid_arg "Flat.map2"
    in
    match xs, ys with
    | Some xs, Some ys -> Some (aux xs ys)
    | None, None -> None
    | _ -> invalid_arg "Flat.map2"
  ;;

  let pp pp ppf xs =
    let rec aux ppf = function
      | FTyp x -> pp ppf x
      | FRecord xs ->
        let pp_sep ppf () = Format.fprintf ppf "; "
        and pp_item ppf (x, xs) = Format.fprintf ppf "%a: %a" S.PP.var x aux xs in
        Format.fprintf ppf "{ %a }" (Format.pp_print_list ~pp_sep pp_item) xs
    in
    match xs with
    | Some xs -> aux ppf xs
    | None -> Format.fprintf ppf "{ }"
  ;;
end

module Flatten = struct
  let kind k =
    let arrow (Ex k1 : Ex.kind) (Ex k2 : Ex.kind) : Ex.kind = Ex (KArrow (k1, k2)) in
    let rec aux args = function
      | S.Kind.KType -> Flat.FTyp (args (Ex T.Kind.KType : Ex.kind))
      | S.Kind.KArrow (k1, k2) ->
        let f k1 k2 = args (Flat.fold_right arrow (Some k1) k2) in
        aux (f (aux Fun.id k1)) k2
      | S.Kind.KRecord xs -> Flat.FRecord (List.map (fun (x, k) -> x, aux args k) xs)
    in
    Option.map (aux Fun.id) k
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
      let _, e = Flat.fold_right2 aux a tc (Fun.const ([], e)) s in
      e
    ;;

    let unpack a x e1 e2 =
      let aux (Ex a : Ex.tvar) (x, e2) =
        let tmp = T.Var.fresh () in
        tmp, T.Expr.EUnpack (a, x, T.Expr.EVar tmp, e2)
      in
      match Flat.fold_right aux a (x, e2) with
      | _, T.Expr.EUnpack (a', x, _, e2) when Flat.cardinal a > 0 ->
        (* Minor optimization - drop top-level let in *)
        T.Expr.EUnpack (a', x, e1, e2)
      | x, e2 -> T.Expr.ELetIn (x, e1, e2)
    ;;

    let repack a x e1 e2 t =
      let tc = Flat.map (fun (Ex a : Ex.tvar) : Ex.typ -> Ex (T.Type.TVar a)) a in
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
  val enter_mod : S.TVar.t -> S.Kind.t option -> t -> t * Ex.tvar Flat.t option
  val enter_field : S.Var.t -> t -> t
  val enter_arrow : S.Type.modu -> t -> t
  val add_tvar : S.TVar.t -> S.Kind.t option -> t -> t * Ex.tvar Flat.t option
  val find_tvar : S.TVar.t -> t -> Ex.tvar Flat.t
  val module_tvars : t -> Ex.tvar Flat.t option
end = struct
  type t =
    { module_tvars : Ex.tvar Flat.t option
    ; vars : T.Var.t S.Var.Map.t
    ; tvars : Ex.tvar Flat.t S.TVar.Map.t
    }

  let empty = { module_tvars = None; vars = S.Var.Map.empty; tvars = S.TVar.Map.empty }

  let add_var x env =
    let x' = T.Var.fresh ~name:(S.Var.name x) () in
    debug (fun m -> m ~header:"var" "%a -> %a" S.PP.var x T.PP.var x');
    { env with vars = S.Var.Map.add x x' env.vars }, x'
  ;;

  let find_var x env =
    match S.Var.Map.find_opt x env.vars with
    | Some x' -> x'
    | None -> Format.kasprintf failwith "unbound variable: %a" S.PP.var x
  ;;

  let add_tvar a k env =
    let a' = Flatten.tvar k in
    match a' with
    | None -> env, None
    | Some a' ->
      debug (fun m ->
        let pp_tvar ppf (Ex a : Ex.tvar) = T.PP.tvar ppf a in
        m ~header:"tvar" "%a -> %a" S.PP.tvar a (Flat.pp pp_tvar) (Some a'));
      { env with tvars = S.TVar.Map.add a a' env.tvars }, Some a'
  ;;

  let enter_mod a k env =
    let env, a' = add_tvar a k env in
    { env with module_tvars = a' }, a'
  ;;

  let enter_field x env =
    match env.module_tvars with
    | None -> env
    | Some (Flat.FRecord xs) ->
      let aux (y, t) = if S.Var.equal x y then Some t else None in
      let module_tvars = List.find_map aux xs in
      { env with module_tvars }
    | Some (Flat.FTyp _) -> invalid_arg "Env.enter_field"
  ;;

  let enter_arrow _ _ = failwith "todo enter arrow"

  let find_tvar a env =
    match S.TVar.Map.find_opt a env.tvars with
    | Some x -> x
    | None -> Format.kasprintf failwith "unbound type variable: %a" S.PP.tvar a
  ;;

  let module_tvars env = env.module_tvars
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
      (fun m -> m ~header:"typ" "%a" S.PP.typ t)
      (fun (Ex t : Ex.typ) m -> m ~header:"typ" "~> %t" (fun ppf -> T.PP.typ ppf t))
    @@ fun () ->
    match S.Type.view t with
    | S.Type.TInfer _ ->
      Format.kasprintf failwith "unresolved type inference variable: %a" S.PP.typ t
    | S.Type.TPrim p -> Ex (T.Type.TPrim p)
    | S.Type.TAbstr p -> path env p
    | S.Type.TArrow (TMod (a1, k1, t1), eff, t2) ->
      let env, a1 = Env.enter_mod a1 k1 env in
      let t = Sugar.Type.eff_arrow (typ env t1) eff (modu env t2) in
      let t = Flat.fold_right (fun (Ex a : Ex.tvar) t -> T.Type.TForall (a, t)) a1 t in
      Ex t
    | S.Type.TRecord xs ->
      let t = T.Type.TRecord (List.map (fun (x, t) -> S.Var.name x, typ env t) xs) in
      Ex t
    | S.Type.TSingleton t -> Ex (Sugar.Type.singleton (modu env t))
    | S.Type.TWrapped t -> Ex (Sugar.Type.wrap (modu env t))

  and modu env (TMod (a, k, t)) =
    let env, a = Env.enter_mod a k env in
    Flat.fold_right (fun (Ex a : Ex.tvar) t -> T.Type.TExists (a, t)) a (typ env t)

  and path env p =
    trace
      (fun m -> m ~header:"path" "")
      (fun (Ex t : Ex.typ) m -> m ~header:"path" "~> %t" (fun ppf -> T.PP.typ ppf t))
    @@ fun () ->
    let rec aux args a r =
      match a, r with
      | Flat.FTyp (Ex x : Ex.tvar), S.Path.Rev.RPNil -> args (Ex (T.Type.TVar x) : Ex.typ)
      | Flat.FRecord xs, S.Path.Rev.RPProj (r, x) -> aux args (List.assoc x xs) r
      | a, S.Path.Rev.RPApp (r1, c2, _) ->
        let f t2 t1 = Flat.fold_left Sugar.Type.app (args t1) t2 in
        aux (f (cons env (Some c2))) a r1
      | _ -> assert false
    in
    let a, r = S.Path.rev p in
    aux Fun.id (Env.find_tvar a env) r

  and cons env (c : _ option) : _ Flat.t option =
    let lam (Ex a1 : Ex.tvar) (Ex c2 : Ex.typ) : Ex.typ = Ex (TLam (a1, c2)) in
    let rec aux env args = function
      | S.Type.CType t -> Flat.FTyp (args (ctyp env t))
      | S.Type.CLam (a1, k1, c2) ->
        let env, a1 = Env.add_tvar a1 k1 env in
        let f a1 c2 = args (Flat.fold_right lam a1 c2) in
        aux env (f a1) c2
      | S.Type.CRecord xs -> Flat.FRecord (List.map (fun (x, k) -> x, aux env args k) xs)
    in
    Option.map (aux env Fun.id) c
  ;;
end

module Elab = struct
  let rec materialize env t =
    trace
      (fun m -> m ~header:"materialize" "%a" S.PP.typ t)
      (fun e m -> m ~header:"materialize" "~> %a" T.PP.expr e)
    @@ fun () ->
    match S.Type.view t with
    | S.Type.TPrim PUnit -> T.Expr.EConst (CUnit ())
    | S.Type.TArrow (TMod (a1, k1, t1), eff, TMod (a2, k2, t2)) ->
      let env1, a1 = Env.enter_mod a1 k1 env in
      (* TODO: What to do with a2? *)
      let env2, a2 = Env.enter_mod a2 k2 env1 in
      let e = materialize env2 t2 in
      let e = Sugar.Expr.eff_lam (T.Var.fresh ()) (Type.typ env1 t1) eff e in
      Flat.fold_right (fun (Ex a : Ex.tvar) e -> T.Expr.ETyLam (a, e)) a1 e
    | S.Type.TRecord ts ->
      let f (x, t) = S.Var.name x, materialize env t in
      T.Expr.ERecord (List.map f ts)
    | S.Type.TSingleton (TMod (a, k, t)) ->
      let env, a = Env.enter_mod a k env in
      let t = Type.typ env t in
      let t = Flat.fold_right (fun (Ex a : Ex.tvar) t -> T.Type.TExists (a, t)) a t in
      Sugar.Expr.singleton t
    | S.Type.TWrapped (TMod (a, k, t)) ->
      (* TODO: What to do with a? *)
      let env, a = Env.enter_mod a k env in
      Sugar.Expr.wrap (materialize env t)
    | _ -> assert false
  ;;

  let rec expr env e =
    trace
      (fun m ->
         let tvar ppf (Ex a : Ex.tvar) = T.PP.tvar ppf a in
         let m = m ~header:"expr" "%a @@ %a" in
         m S.PP.expr e (Flat.pp tvar) (Env.module_tvars env))
      (fun e m -> m ~header:"expr" "~> %a" T.PP.expr e)
    @@ fun () ->
    match e with
    | S.Expr.EVar x -> T.Expr.EVar (Env.find_var x env)
    | S.Expr.EConst c -> T.Expr.EConst c
    | S.Expr.ECond (x, e1, e2, _) ->
      let e1 = expr env e1
      and e2 = expr env e2 in
      T.Expr.ECond (T.Expr.EVar (Env.find_var x env), e1, e2)
    | S.Expr.EStruct (xs, ts) ->
      let env, xs = List.fold_left_map bind env xs in
      let xs = List.concat xs in
      let aux (x, _) = S.Var.name x, T.Expr.EVar (Env.find_var x env) in
      let e = T.Expr.ERecord (List.map aux ts) in
      let a = Env.module_tvars env in
      let tc = Flat.map (fun (Ex a : Ex.tvar) : Ex.typ -> Ex (T.Type.TVar a)) a in
      let t = Type.typ env (S.Type.TRecord ts |> S.Type.wrap) in
      let e = Sugar.Expr.pack a tc t e in
      List.fold_right (fun (x, a, e1) e2 -> Sugar.Expr.unpack a x e1 e2) xs e
    | S.Expr.EProj (e, x, t) ->
      let tmp, e1 = T.Var.fresh (), expr env e in
      let e2 = T.Expr.EProj (EVar tmp, S.Var.name x) in
      let a = Env.module_tvars env in
      let e = Sugar.Expr.repack a tmp e1 e2 (Type.typ env t) in
      e
    | S.Expr.EFun (x, TMod (a, k, t), eff, e) ->
      let env, a = Env.add_tvar a k env in
      let t1 = Type.typ env t in
      let env, x = Env.add_var x env in
      let e = modu env e in
      let e = Sugar.Expr.eff_lam x t1 eff e in
      Flat.fold_right (fun (Ex a : Ex.tvar) e -> T.Expr.ETyLam (a, e)) a e
    | S.Expr.EApp (e1, tc, eff, e2) ->
      let e = Flat.fold_left Sugar.Expr.ty_app (expr env e1) (Type.cons env tc) in
      let env, _ = Env.enter_mod S.TVar.null None env in
      let e = Sugar.Expr.eff_app e eff (expr env e2) in
      e
    | S.Expr.EType t -> Sugar.Expr.singleton (Type.modu env t)
    | S.Expr.EExtern (s, t) -> T.Expr.EExtern (s, Type.typ env t)
    | S.Expr.EWrap (x, _) -> Sugar.Expr.wrap (modu env x)
    | S.Expr.EUnwrap e -> Sugar.Expr.unwrap (expr env e)
    | S.Expr.EInst (e, tc, t) ->
      let tc = Type.cons env tc in
      let e = expr env e in
      let e = Flat.fold_left (fun e (Ex t : Ex.typ) -> T.Expr.ETyApp (e, t)) e tc in
      let e = Sugar.Expr.eff_app e Implicit (materialize env t) in
      e
    | S.Expr.EGen (TMod (a, k, t), e) ->
      let env, a = Env.add_tvar a k env in
      let e = expr env e in
      let e = Sugar.Expr.eff_lam (T.Var.fresh ()) (Type.typ env t) Implicit e in
      Flat.fold_right (fun (Ex a : Ex.tvar) e -> T.Expr.ETyLam (a, e)) a e
    | S.Expr.ESeal (EMod (a, k, e), tc, t) ->
      let x = T.Var.fresh () in
      let env', a = Env.enter_mod a k env in
      let e1 = expr env' e in
      let e2 =
        let e = T.Expr.EVar x in
        let a = Env.module_tvars env in
        Sugar.Expr.pack a (Type.cons env' tc) (Type.typ env t) e
      in
      Sugar.Expr.unpack a x e1 e2

  and modu env (S.Expr.EMod (a, k, e)) =
    let env, _ = Env.enter_mod a k env in
    expr env e

  and bind env b =
    trace (fun m -> m ~header:"bind" "%a" S.PP.bind b) (fun _ m -> m ~header:"bind" "")
    @@ fun () ->
    let proj tmp env (x, _) =
      let env, x' = Env.add_var x env in
      env, (x', None, T.Expr.EProj (T.Expr.EVar tmp, S.Var.name x))
    and proj_a env x =
      Option.map (fun a -> x, a) (Env.module_tvars (Env.enter_field x env))
    in
    match b with
    | S.Expr.BIncl (_, e, ts, ks) ->
      let tmp, e = T.Var.fresh (), expr env e in
      let a = List.filter_map (proj_a env) ks in
      let a = if a = [] then None else Some (Flat.FRecord a) in
      let env, es = List.fold_left_map (proj tmp) env ts in
      env, (tmp, a, e) :: es
    | S.Expr.BVal (x, e) ->
      let env' = Env.enter_field x env in
      let e = expr env' e in
      let env, x = Env.add_var x env in
      env, [ x, Env.module_tvars env', e ]
  ;;

  let file env node =
    trace
      (fun m ->
         let expr = Format.with_margin 140 S.PP.expr_modu in
         let expr = Format.with_max_boxes Int.max_int expr in
         m ~header:"file" "%a" expr node)
      (fun t m ->
         let expr = Format.with_margin 140 T.PP.expr in
         let expr = Format.with_max_boxes Int.max_int expr in
         m ~header:"file" "%a" expr t)
    @@ fun () -> modu env node
  ;;
end

open Format
