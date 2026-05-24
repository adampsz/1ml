open Util
open (val Trace.init ~scope:"typecheck" ())

open struct
  module S = Lang.Surface
  module T = Lang.Typed

  let view = T.Type.view
  let wrap = T.Type.wrap
end

module Env : sig
  type t

  val empty : t
  val add : T.Var.t -> T.Type.t -> t -> t
  val add_tvar : T.TVar.t -> t -> t
  val add_mod : T.Var.t -> T.Type.t -> t -> t
  val add_record : (T.Var.t * T.Type.t) list -> t -> t
  val find : ?span:T.Type.span -> string -> t -> T.Var.t * T.Type.t
  val enter_mod : T.TVar.t -> t -> t
  val enter_lam : T.TVar.t -> t -> t
  val enter_field : T.Var.t -> t -> t
  val path : t -> T.TVar.t T.Path.t
  val domain : t -> T.TVar.Set.t
  val uvar : t -> T.Type.t
  val eff : T.Type.t -> t -> T.Effect.t
  val for_subtype : t -> t * T.Type.Cons.t option
  val for_pp : t -> Pretty.Env.t
end = struct
  type t =
    { path : T.TVar.t T.Path.t
    ; vars : (T.Var.t * T.Type.t) String.Map.t
    ; tvars : T.TVar.Set.t
    }

  let empty = { path = T.Path.empty; vars = String.Map.empty; tvars = T.TVar.Set.empty }
  let add x t env = { env with vars = String.Map.add (T.Var.name x) (x, t) env.vars }
  let add_tvar a env = { env with tvars = T.TVar.Set.add a env.tvars }

  let add_mod x t env =
    let a, t = T.Type.as_module t in
    add_tvar a env |> add x t
  ;;

  let add_record xs env = List.fold_left (fun env (x, t) -> add x t env) env xs

  let for_pp env =
    Pretty.Env.empty
    |> T.TVar.Set.fold Pretty.Env.add_tvar env.tvars
    |> String.Map.fold (fun _ (x, t) -> Pretty.Env.add_var x t) env.vars
  ;;

  let find ?span x env =
    match String.Map.find_opt x env.vars with
    | Some (x, t) ->
      let t = T.Subst.typ T.Subst.id t in
      debug (fun m -> m ~header:"env" "find %a ↦ %a" T.Var.pp x T.Type.pp t);
      x, t
    | None -> Diagnostic.Error.error ?span "unbound variable `%s'" x
  ;;

  let enter_mod a env = { (add_tvar a env) with path = T.Path.PVar a }
  let enter_lam a env = { env with path = PApp (env.path, a) }
  let enter_field x env = { env with path = PProj (env.path, x) }
  let domain env = env.tvars
  let path env = env.path
  let uvar env = TInfer (T.UVar.fresh (domain env)) |> wrap
  let eff t env = T.Type.eff (T.Path.var env.path) t
  let for_subtype env = env, T.Type.Cons.empty
end

module Error = struct
  open Diagnostic.Error

  let pp_typ env ppf t = Pretty.Print.typ ~prec:0 ~env:(Env.for_pp env) ppf t
  let missing_field ?span x = error ?span "record is missing field `%s'" x

  let expected_record_type ?span env t =
    error ?span "expected a record type, but got `%a'" (pp_typ env) t
  ;;

  let expected_record_kind ?span () = error ?span "expected a record kind"

  let expected_function_type ?span env t =
    error ?span "expected a function type, but got `%a'" (pp_typ env) t
  ;;

  let expected_wrapped_type ?span env t =
    error ?span "expected a wrapped type, but got `%a'" (pp_typ env) t
  ;;

  let expected_singleton_type ?span env t =
    error ?span "expected a singleton type, but got `%a'" (pp_typ env) t
  ;;

  let expected_bool ?span env t =
    error ?span "expected a boolean, but got `%a'" (pp_typ env) t
  ;;

  let expected_pure_expression ?span () = error ?span "expected a pure expression"
  let implicit_must_be_pure ?span () = error ?span "implicit function cannot be impure"

  let not_assignable ?span ?cause env t' t =
    let span =
      match span, T.Type.span t, T.Type.span t' with
      | Some span, _, _ | _, Some span, _ | _, _, Some span -> Some span
      | _, _, _ -> None
    in
    let raise = error ?span ?cause "@[type `%a'@ is not assignable to `%a'@]" in
    raise (pp_typ env) t' (pp_typ env) t
  ;;

  let in_field ?span ?cause x = error ?span ?cause "in record field `%s':" x
  let in_function_argument ?span ?cause () = error ?span ?cause "in function argument:"
  let in_function_return ?span ?cause () = error ?span ?cause "in function return:"
  let in_singleton ?span ?cause () = error ?span ?cause "in singleton type:"
  let in_wrapped ?span ?cause () = error ?span ?cause "in wrapped type:"
end

module Implicit = struct
  let rec concretize env = function
    | T.Kind.KType -> T.Type.CType (TInfer (T.UVar.fresh env) |> wrap)
    | T.Kind.KArrow (k1, k2) ->
      let x = T.TVar.fresh k1 in
      T.Type.CLam (x, concretize (T.TVar.Set.add x env) k2)
    | T.Kind.KRecord ks ->
      T.Type.CRecord (List.map (fun (x, k) -> x, concretize env k) ks)
  ;;

  let rec materialize env t =
    match view t with
    | TPrim PUnit -> T.Expr.EConst (CUnit ())
    | TArrow (_, t1, eff, t2) ->
      let a, t1 = T.Type.as_module t1 in
      let env = T.TVar.Set.add a env in
      T.Expr.EFun (T.Var.fresh "a", t1, eff, materialize env t2)
    | TRecord ts ->
      let bind (x, t) = T.Expr.BVal (x, materialize env t) in
      T.Expr.EStruct (List.map bind ts, ts)
    | TSingleton t -> T.Expr.EType t
    | TWrapped t -> T.Expr.EWrap (materialize env t, TWrapped t |> wrap)
    | TMod (a, t) -> materialize (T.TVar.Set.add a env) t
    | _ -> assert false
  ;;

  let generalize level t =
    let rec typ acc t =
      match view t with
      | TInfer z when T.UVar.newer level z ->
        let a = T.TVar.fresh T.Kind.KType in
        T.UVar.set z (TAbstr (PVar a));
        let t1 = TInfer z |> wrap in
        let t1 = TMod (a, TSingleton t1 |> wrap) |> wrap
        and t2 = snd acc in
        ( (fun e -> T.Expr.EFun (T.Var.fresh "a", t1, Implicit, fst acc e))
        , TArrow (T.Var.fresh "a", t1, Implicit, t2) |> wrap )
      | TInfer _ -> acc
      | TAbstr p -> path acc p
      | TPrim _ -> acc
      | TArrow (_, t1, _, t2) -> typ (typ acc t1) t2
      | TRecord ts -> List.fold_left (fun xs (_, t) -> typ xs t) acc ts
      | TSingleton t -> typ acc t
      | TWrapped t -> typ acc t
      | TMod (_, t) -> typ acc t
    and path acc = function
      | T.Path.PVar _ -> acc
      | T.Path.PProj (p, _) -> path acc p
      | T.Path.PApp (p, x) -> path (cons acc x) p
    and cons acc = function
      | T.Type.CType t -> typ acc t
      | T.Type.CLam (_, t) -> cons acc t
      | T.Type.CRecord ts -> List.fold_left (fun xs (_, t) -> cons xs t) acc ts
    in
    typ (Fun.id, t) t
  ;;

  let instantiate env t =
    let rec aux (inst, t) =
      match view t with
      | TArrow (_, t1, Implicit, t2) ->
        let a, t1 = T.Type.as_module t1 in
        let tc = concretize env (T.TVar.kind a) in
        let t1 = T.Subst.typ (T.Subst.one a tc) t1
        and t2 = T.Subst.typ (T.Subst.one a tc) t2 in
        aux ((fun e -> T.Expr.EApp (inst e, tc, Implicit, materialize env t1)), t2)
      | _ -> inst, t
    in
    aux (Fun.id, t)
  ;;
end

module Subtype = struct
  module Env = struct
    include Env

    let enter_mod a env = enter_mod a env, T.Type.Cons.empty
    let enter_field a (env, acc) = enter_field a env, acc
    let enter_lam a (env, acc) = enter_lam a env, acc
    let subst (env, acc) = T.Subst.one_opt (T.Path.var (Env.path env)) acc
  end

  let chain context f =
    try f () with
    | Diagnostic.Error.Error _ as cause -> context cause
  ;;

  (**
    Subtyping rule [Γ ⊢ t′ ≤ t].

    Checks whether a concrete type [t'] is a subtype of a more general type [t].
    All type variables in [t] and [t'] are bound in the environment [env], except one
    type variable bound by the [path].

    The type [t] is a concrete type except an abstract type variable bound in [path].
    When subtyping succedes, it returns a substitution [s] that can be applied
    to the type variable in [path] to make it a concrete supertype of [t'].
  *)
  let rec typ (env, acc) t' t =
    trace
      (fun m ->
         let pf = m ~header:"subtype" "%a <= %a at %a" in
         pf T.Type.pp t' T.Type.pp t (T.Path.pp T.TVar.pp) (Env.path env))
      (fun (acc, _) m ->
         m ~header:"subtype" "~> %a" (Format.pp_print_option T.Type.Cons.pp) acc)
    @@ fun () ->
    match view t', view t with
    (* Implicit functions *)
    | _, TArrow (_, t1, Implicit, t2) ->
      let a, _ = T.Type.as_module t1 in
      let acc, f = typ (Env.add_tvar a env, acc) t' t2 in
      acc, fun e -> T.Expr.EFun (T.Var.fresh "a", t1, Implicit, f e)
    | TArrow (_, _, Implicit, _), _ ->
      let inst, t' = Implicit.instantiate (Env.domain env) t' in
      let acc, f = typ (env, acc) t' t in
      acc, fun e -> f (inst e)
    (* Modules*)
    (* TODO: simplify *)
    | TMod (a', t'), TMod (a, t) ->
      let f =
        let c, f = typ (Env.enter_mod a (Env.add_tvar a' env)) t' t in
        let c = Option.value c ~default:(T.Type.CRecord []) in
        fun e -> T.Expr.EMod (a, ESeal (EMod (a', f (EUse e)), c, t))
      in
      acc, f
    | _, TMod (a, t) ->
      let f =
        let c, f = typ (Env.enter_mod a env) t' t in
        let c = Option.value c ~default:(T.Type.CRecord []) in
        fun e -> T.Expr.EMod (a, ESeal (f e, c, t))
      in
      acc, f
    | TMod (a', t'), _ ->
      let acc, f = typ (Env.add_tvar a' env, acc) t' t in
      acc, fun e -> T.Expr.ESeal (EMod (a', f (EUse e)), T.Type.CRecord [], t)
    (* Unification *)
    | TInfer z', TRecord xs ->
      let t' = wrap (TRecord (List.map (fun (x, _) -> x, Env.uvar env) xs)) in
      assert (T.Type.resolve z' t');
      typ (env, acc) t' t
    | TRecord xs', TInfer z ->
      let t = wrap (TRecord (List.map (fun (x', _) -> x', Env.uvar env) xs')) in
      assert (T.Type.resolve z t);
      typ (env, acc) t' t
    | TInfer z', TArrow (x, t1, Explicit Impure, t2)
      when T.Type.is_small t1 && T.Type.is_small t2 ->
      let t' = TArrow (x, Env.uvar env, Explicit Impure, Env.uvar env) |> wrap in
      assert (T.Type.resolve z' t');
      typ (env, acc) t' t
    | TArrow (x, t1', Explicit _, t2'), TInfer z
      when T.Type.is_small t1' && T.Type.is_small t2' ->
      let t = TArrow (x, Env.uvar env, Explicit Impure, Env.uvar env) |> wrap in
      assert (T.Type.resolve z t);
      typ (env, acc) t' t
    | TInfer z, v | v, TInfer z ->
      if T.Type.resolve z (wrap v)
      then acc, Fun.id
      else Error.not_assignable env (wrap (TInfer z)) (wrap v)
    (* Subtyping *)
    | TAbstr p', TAbstr p when T.Path.equal (equal env) p' p -> acc, Fun.id
    | _, TAbstr p ->
      let t = T.Subst.typ (Env.subst (env, acc)) t in
      (match view t with
       | TAbstr p' when T.Path.equal (equal env) p' p -> Error.not_assignable env t' t
       | _ -> typ (env, acc) t' t)
    | TAbstr _, _ -> Error.not_assignable env t' t
    | TPrim p', TPrim p when T.Prim.equal p' p -> acc, Fun.id
    | TPrim _, _ -> Error.not_assignable env t' t
    | TRecord xs', TRecord xs ->
      chain (fun cause -> Error.not_assignable ~cause env t' t)
      @@ fun () ->
      let aux acc (x, ti) =
        let x', ti' =
          match T.Var.assoc_opt (T.Var.name x) xs' with
          | Some (x', t') -> x', t'
          | None -> Error.missing_field (T.Var.name x)
        in
        chain (fun cause -> Error.in_field ~cause (T.Var.name x))
        @@ fun () ->
        let acc, c = typ (Env.enter_field x (env, acc)) ti' ti in
        acc, T.Expr.BVal (x, c (EVar x'))
      in
      let acc, bs = List.fold_left_map aux acc xs in
      let xs = List.map (fun (x, t) -> x, T.Subst.typ (Env.subst (env, acc)) t) xs in
      acc, fun e -> T.Expr.EStruct (BIncl (Private, e, xs') :: bs, xs)
    | TRecord _, _ -> Error.not_assignable env t' t
    | TArrow (_, t1', Explicit eff', t2'), TArrow (x, t1, Explicit eff, t2)
      when T.Effect.sub eff' eff ->
      chain (fun cause -> Error.not_assignable ~cause env t' t)
      @@ fun () ->
      let (a1', t1'), (a1, t1) = T.Type.as_module t1', T.Type.as_module t1 in
      let env = Env.add_tvar a1 env in
      let t1 = T.Subst.typ (Env.subst (env, acc)) t1 in
      let x1 = T.Var.clone x in
      let tc1, f1 =
        chain (fun cause -> Error.in_function_argument ~cause ())
        @@ fun () -> typ (Env.enter_mod a1' (Env.add_tvar a1 env)) t1 t1'
      in
      let t2' = T.Subst.typ (T.Subst.one_opt a1' tc1) t2' in
      let acc, f2 =
        chain (fun cause -> Error.in_function_return ~cause ())
        @@ fun () ->
        match eff with
        | Impure -> typ (env, acc) t2' (T.Subst.typ (Env.subst (env, acc)) t2)
        | Pure -> typ (Env.enter_lam a1 (env, acc)) t2' t2
      in
      let f e =
        let tc1 = Option.value tc1 ~default:(T.Type.CRecord []) in
        let e = T.Expr.EApp (e, tc1, Explicit eff', f1 (EVar x1)) in
        T.Expr.EFun (x1, T.Type.as_type a1 t1, Explicit eff, f2 e)
      in
      acc, f
    | TArrow _, _ -> Error.not_assignable env t' t
    | TSingleton t', TSingleton t
      when T.Type.is_path (Env.path env) t && T.Type.is_small t' ->
      Some (T.Type.Cons.set (Env.path env) t' acc), Fun.id
    | TSingleton ti', TSingleton ti ->
      chain (fun cause -> Error.not_assignable ~cause env t' t)
      @@ fun () ->
      let ti = T.Subst.typ (Env.subst (env, acc)) ti in
      let chain = chain (fun cause -> Error.in_singleton ~cause ()) in
      let _ = chain @@ fun () -> typ (env, acc) ti' ti
      and _ = chain @@ fun () -> typ (env, acc) ti ti' in
      acc, Fun.const (T.Expr.EType ti)
    | TWrapped ti', TWrapped ti ->
      chain (fun cause -> Error.not_assignable ~cause env t' t)
      @@ fun () ->
      let ti = T.Subst.typ (Env.subst (env, acc)) ti in
      let chain = chain (fun cause -> Error.in_wrapped ~cause ()) in
      let _ = chain @@ fun () -> typ (env, acc) ti' ti
      and _ = chain @@ fun () -> typ (env, acc) ti ti' in
      acc, Fun.id
    | TSingleton _, _ -> Error.not_assignable env t' t
    | TWrapped _, _ -> Error.not_assignable env t' t

  and equal env t' t =
    match t', t with
    | CType t', CType t ->
      (try
         let _ = typ (env, T.Type.Cons.empty) t' t
         and _ = typ (env, T.Type.Cons.empty) t t' in
         true
       with
       | Diagnostic.Error.Error _ -> false)
    | _, _ -> failwith "todo: equality"
  ;;
end

module Check = struct
  let rec proj env xs t =
    match view t, xs with
    | _, [] -> [], t
    | TRecord ts, x :: xs ->
      (match T.Var.assoc_opt (S.Node.data x) ts with
       | Some (x, t) ->
         let xs, t = proj env xs t in
         x :: xs, t
       | None ->
         let span = S.Node.span x in
         Error.missing_field ?span (S.Node.data x))
    | _, x :: _ ->
      let span = S.Node.span x in
      Error.expected_record_type ?span env t
  ;;

  let path_map a f t =
    let aux p =
      if T.TVar.equal (T.Path.var p) a then Some (TAbstr (f p) |> wrap) else None
    in
    T.Subst.typ aux t
  ;;

  let path_prepend env t =
    match view t with
    | TMod (a, t) ->
      let f = T.Path.prepend (T.Type.path_to_abstr (Env.path env)) in
      T.Kind.opt (T.TVar.kind a), path_map a f t, fun e -> T.Expr.EUse e
    | _ -> None, t, Fun.id
  ;;

  let field x = T.Var.fresh (S.Node.data x)

  let rec set_kind xs k' k =
    match xs with
    | [] -> k'
    | x :: xs ->
      let ks =
        match k with
        | None -> []
        | Some (T.Kind.KRecord ks) -> ks
        | Some _ -> Error.expected_record_kind ()
      in
      let update old = set_kind xs k' old in
      T.Kind.opt_record (T.Var.assoc_update (T.Var.name x) update ks)
  ;;

  (* INVARIANT: returned type has correct paths *)
  let rec typ env t =
    trace
      (fun m ->
         let m = m ~header:"typ" "%a at %a" in
         m Lang.Surface.pp_typ t (T.Path.pp T.TVar.pp) (Env.path env))
      (fun (k, t) m ->
         let m = m ~header:"typ" "~> %a at %a with %a" in
         m T.Type.pp t (T.Path.pp T.TVar.pp) (Env.path env) T.Kind.Option.pp k)
    @@ fun () ->
    let span = S.Node.span t in
    match S.Node.data t with
    | S.TPrim p -> None, TPrim p |> wrap ?span
    | S.THole -> None, TInfer (T.UVar.fresh (Env.domain env)) |> wrap ?span
    | S.TType ->
      let abstr = TAbstr (T.Type.path_to_abstr (Env.path env)) |> wrap ?span in
      Some T.Kind.KType, TSingleton abstr |> wrap ?span
    | S.TExpr e ->
      let eff, ty, _ = modu_expr env e in
      let _, ty = Implicit.instantiate (Env.domain env) ty in
      (match eff, view ty with
       | T.Effect.Pure, TSingleton ty ->
         let k, ty, _ = path_prepend env ty in
         k, T.Type.with_span ?span ty
       | T.Effect.Pure, TInfer z ->
         let ty = TInfer (T.UVar.fresh (Env.domain env)) |> wrap ?span in
         assert (T.Type.resolve z (TSingleton ty |> wrap ?span));
         None, ty
       | T.Effect.Pure, _ -> Error.expected_singleton_type ?span env ty
       | _, _ -> Error.expected_pure_expression ?span ())
    | S.TWith (t, xs, t_') ->
      let k, t = typ env t in
      let xs, t_ = proj env xs t in
      let env_ = List.fold_left (fun e x -> Env.enter_field x e) env xs in
      let k_', t_' = typ env_ t_' in
      let c, _ = Subtype.typ (Env.for_subtype env_) t_' t_ in
      set_kind xs k_' k, T.Subst.typ (T.Subst.one_opt (T.Path.var (Env.path env)) c) t
    | S.TStruct xs ->
      let _, xs = List.fold_left_map decl env xs in
      let ks = List.concat_map (fun (ks, _) -> ks) xs
      and ts = List.concat_map (fun (_, ts) -> ts) xs |> T.Var.normalize in
      T.Kind.opt_record ks, TRecord ts |> wrap ?span
    | S.TArrow (x, t1, eff, T.Effect.Impure, t2) ->
      if eff == Implicit then Error.implicit_must_be_pure ?span ();
      let x = T.Var.fresh (S.Node.data x) in
      let t1 = modu_typ env t1 in
      let env = Env.add_mod x t1 env in
      let t2 = modu_typ env t2 in
      None, TArrow (x, t1, Explicit Impure, t2) |> wrap ?span
    | S.TArrow (x, t1, eff, T.Effect.Pure, t2) ->
      let x = T.Var.fresh (S.Node.data x) in
      let t1 = modu_typ env t1 in
      let a1, _ = T.Type.as_module t1 in
      let env = Env.add_mod x t1 env in
      let k2, t2 = typ (Env.enter_lam a1 env) t2 in
      let eff = if eff = Implicit then T.Type.Implicit else T.Type.Explicit Pure in
      T.Kind.opt_arrow (T.TVar.kind a1) k2, TArrow (x, t1, eff, t2) |> wrap ?span
    | S.TSingletonType t -> None, TSingleton (modu_typ env t) |> wrap ?span
    | S.TWrapped t -> None, TWrapped (modu_typ env t) |> wrap ?span

  and decl env d =
    trace
      (fun m ->
         let m = m ~header:"decl" "%a at %a" in
         m Lang.Surface.pp_decl d (T.Path.pp T.TVar.pp) (Env.path env))
      (fun _ m -> m ~header:"decl" "")
    @@ fun () ->
    let span = S.Node.span d in
    match S.Node.data d with
    | S.DVal (x, t) ->
      let x = field x in
      let k, t = typ (Env.enter_field x env) t in
      let ks = Option.fold k ~none:[] ~some:(fun k -> [ x, k ]) in
      Env.add x t env, (ks, [ x, t ])
    | S.DIncl (vis, t) ->
      let k, t = typ env t in
      let ks, ts =
        match k, view t with
        | Some (T.Kind.KRecord ks), TRecord xs -> ks, xs
        | None, TRecord xs -> [], xs
        | _ -> Error.expected_record_type ?span env t
      in
      let env = Env.add_record ts env in
      env, (ks, if vis = Public then ts else [])

  and expr env e =
    trace
      (fun m ->
         let m = m ~header:"expr" "%a at %a" in
         m Lang.Surface.pp_expr e (T.Path.pp T.TVar.pp) (Env.path env))
      (fun (k, _, t, _) m ->
         let m = m ~header:"expr" ":: %a at %a with %a" in
         m T.Type.pp t (T.Path.pp T.TVar.pp) (Env.path env) T.Kind.Option.pp k)
    @@ fun () ->
    let span = S.Node.span e in
    match S.Node.data e with
    | S.EVar x ->
      let x, t = Env.find ?span:(S.Node.span x) (S.Node.data x) env in
      None, T.Effect.Pure, t, T.Expr.EVar x
    | S.EConst c ->
      None, T.Effect.Pure, TPrim (T.Const.typ c) |> wrap ?span, T.Expr.EConst c
    | S.ECond (x, e1, e2, t) ->
      let xspan = S.Node.span x in
      let x, c = Env.find ?span:xspan (S.Node.data x) env in
      (match view c with
       | TPrim PBool -> ()
       | TInfer z -> assert (T.Type.resolve z (wrap (TPrim PBool)))
       | _ -> Error.expected_bool ?span:xspan env c);
      let eff1, t1, e1 = modu_expr env e1
      and eff2, t2, e2 = modu_expr env e2
      and t = modu_typ env t in
      let _, f1 = Subtype.typ (Env.for_subtype env) t1 t
      and _, f2 = Subtype.typ (Env.for_subtype env) t2 t in
      let k, t, e = path_prepend env t in
      let eff = Env.eff t env in
      let eff = T.Effect.join eff (T.Effect.join eff1 eff2) in
      k, eff, t, e (T.Expr.ECond (x, f1 e1, f2 e2, t))
    | S.EStruct xs ->
      let _, xs = List.fold_left_map bind env xs in
      let ks = List.concat_map (fun (ks, _, _, _) -> ks) xs
      and eff = List.fold_left (fun a (_, eff, _, _) -> T.Effect.join a eff) Pure xs
      and ts = List.concat_map (fun (_, _, ts, _) -> ts) xs |> T.Var.normalize
      and xs = List.map (fun (_, _, _, b) -> b) xs in
      T.Kind.opt_record ks, eff, TRecord ts |> wrap ?span, T.Expr.EStruct (xs, ts)
    | S.EProj (e, x) ->
      let k, eff, t, te = expr env e in
      let ts =
        match view t with
        | TRecord ts -> ts
        | TInfer z ->
          let x = T.Var.fresh (S.Node.data x) in
          let ts = [ x, TInfer (T.UVar.fresh (Env.domain env)) |> wrap ?span ] in
          assert (T.Type.resolve z (T.Type.TRecord ts |> wrap ?span));
          ts
        | _ -> Error.expected_record_type ?span:(S.Node.span e) env t
      in
      (match T.Var.assoc_opt (S.Node.data x) ts with
       | Some (x, t) -> k, eff, t, T.Expr.EProj (te, x, t)
       | None -> Error.missing_field ?span:(S.Node.span x) (S.Node.data x))
    | S.EFun (x, t1, feff, e2) ->
      let t1 = modu_typ env t1 in
      let x = T.Var.fresh (S.Node.data x) in
      let env = Env.add_mod x t1 env in
      let eff, t2, e2 = modu_expr env e2 in
      let eff =
        match feff, eff with
        | Explicit, eff -> T.Type.Explicit eff
        | Implicit, Pure -> T.Type.Implicit
        | Implicit, Impure -> Error.implicit_must_be_pure ?span ()
      in
      let t2, e2 =
        match eff with
        | Explicit Impure -> t2, e2
        | Explicit Pure | Implicit ->
          assert (T.TVar.is_empty (fst (T.Type.as_module t2)));
          assert (T.TVar.is_empty (fst (T.Expr.as_module e2)));
          t2, e2
      in
      let t = TArrow (x, t1, eff, t2) |> wrap ?span
      and e = T.Expr.EFun (x, t1, eff, e2) in
      None, T.Effect.Pure, t, e
    | S.EApp (x, x') ->
      let dom = Env.domain env in
      let xv, t = Env.find ?span:(S.Node.span x) (S.Node.data x) env in
      let inst, t = Implicit.instantiate dom t in
      let (a1, t1), eff, t2 =
        match view t with
        | TArrow (_, t1, Explicit eff, t2) -> T.Type.as_module t1, eff, t2
        | TInfer z ->
          let t1 = TInfer (T.UVar.fresh dom) |> wrap ?span
          and t2 = TInfer (T.UVar.fresh dom) |> wrap ?span in
          let tf = TArrow (T.Var.fresh "a", t1, Explicit Impure, t2) |> wrap ?span in
          assert (T.Type.resolve z tf);
          (T.TVar.empty, t1), T.Effect.Impure, t2
        | _ -> Error.expected_function_type ?span:(S.Node.span x) env t
      in
      let x', t1' = Env.find ?span:(S.Node.span x') (S.Node.data x') env in
      let tc, f =
        let env, _ = Env.for_subtype env in
        Subtype.typ (Subtype.Env.enter_mod a1 env) t1' t1
      in
      let k2, t2, e =
        match eff with
        | Impure -> path_prepend env (T.Subst.typ (T.Subst.one_opt a1 tc) t2)
        | Pure -> None, T.Subst.typ (T.Subst.one_opt a1 tc) t2, Fun.id
      in
      let tc = Option.value tc ~default:(T.Type.CRecord []) in
      let e = e (T.Expr.EApp (inst (EVar xv), tc, Explicit eff, f (EVar x'))) in
      k2, eff, t2, e
    | S.EType t ->
      let t = modu_typ env t in
      None, T.Effect.Pure, TSingleton t |> wrap ?span, T.Expr.EType t
    | S.ESeal (x, t) ->
      let xv, t' = Env.find ?span:(S.Node.span x) (S.Node.data x) env
      and k, t = typ env t in
      let c, f = Subtype.typ (Env.for_subtype env) t' t in
      let c = Option.value c ~default:(T.Type.CRecord []) in
      let e = T.Expr.ESeal (f (EVar xv), c, t) in
      k, Env.eff t env, t, e
    | S.EWrap (x, t) ->
      let k, ty = typ env t in
      let ty =
        match view ty with
        | TWrapped tw when Option.is_none k -> tw
        | _ -> Error.expected_wrapped_type ?span:(S.Node.span t) env ty
      in
      let xv, t' = Env.find ?span:(S.Node.span x) (S.Node.data x) env in
      let _, f = Subtype.typ (Env.for_subtype env) t' ty in
      let e = T.Expr.EWrap (f (EVar xv), ty) in
      None, T.Effect.Pure, TWrapped ty |> wrap ?span, e
    | S.EUnwrap (x, t) ->
      let dom = Env.domain env in
      let xv, t1 = Env.find ?span:(S.Node.span x) (S.Node.data x) env in
      let inst, t1 = Implicit.instantiate dom t1 in
      let k, t2 = typ env t in
      let t2 =
        match view t2 with
        | TWrapped t2 when Option.is_none k -> t2
        | _ -> Error.expected_wrapped_type ?span:(S.Node.span t) env t2
      in
      let t1 =
        match view t1 with
        | TWrapped t -> t
        | TInfer z ->
          assert (T.Type.resolve z (TWrapped t2 |> wrap ?span));
          t2
        | _ -> Error.expected_wrapped_type ?span:(S.Node.span x) env t1
      in
      let _, f = Subtype.typ (Env.for_subtype env) t1 t2 in
      let k2, t2, e2 = path_prepend env t2 in
      let e = e2 (f (T.Expr.EUnwrap (inst (EVar xv)))) in
      k2, Env.eff t2 env, t2, e
    | S.EExtern (x, t) ->
      let k, t = typ env t in
      k, Env.eff t env, t, T.Expr.EExtern (x, t)

  and bind env b =
    trace
      (fun m ->
         let m = m ~header:"bind" "%a at %a" in
         m Lang.Surface.pp_bind b (T.Path.pp T.TVar.pp) (Env.path env))
      (fun _ m -> m ~header:"bind" "")
    @@ fun () ->
    match S.Node.data b with
    | S.BVal (x, e) ->
      let x = field x in
      let level = T.UVar.stamp () in
      let k, eff, t, e = expr (Env.enter_field x env) e in
      let gen, t = Implicit.generalize level t in
      let ks = Option.fold k ~none:[] ~some:(fun k -> [ x, k ]) in
      Env.add x t env, (ks, eff, [ x, t ], T.Expr.BVal (x, gen e))
    | S.BIncl (vis, e) ->
      let span = S.Node.span e in
      let k, eff, t, e = expr env e in
      let ks, ts =
        match k, view t with
        | Some (T.Kind.KRecord ks), TRecord xs -> ks, xs
        | None, TRecord xs -> [], xs
        | _ -> Error.expected_record_type ?span env t
      in
      let env = Env.add_record ts env in
      let e = T.Expr.BIncl (vis, e, ts) in
      env, (ks, eff, (if vis = Public then ts else []), e)

  and modu_typ env node =
    let a, set = T.TVar.defer () in
    let k, t = typ (Env.enter_mod a env) node in
    set (Option.value k ~default:T.Kind.empty);
    T.Type.as_type a t

  and modu_expr env node =
    let a, set = T.TVar.defer () in
    let k, eff, t, e = expr (Env.enter_mod a env) node in
    set (Option.value k ~default:T.Kind.empty);
    eff, T.Type.as_type a t, T.Expr.as_expr a e
  ;;

  let file env file =
    let e = S.Node.map (fun xs -> Lang.Surface.EStruct xs) file in
    trace
      (fun m ->
         let expr = Format.with_margin 140 S.pp_expr in
         let expr = Format.with_max_boxes Int.max_int expr in
         m ~header:"file" "%a" expr e)
      (fun t m ->
         let expr = Format.with_margin 140 T.Expr.pp in
         let expr = Format.with_max_boxes Int.max_int expr in
         m ~header:"file" "%a" expr t)
    @@ fun () ->
    let _, _, e = modu_expr env e in
    e
  ;;
end

module Session = struct
  type state =
    { env : Env.t
    ; eff : T.Effect.t
    ; ks : (T.Var.t * T.Kind.t) list
    ; ts : (T.Var.t * T.Type.t) list
    ; es : T.Expr.bind list
    }

  let empty = { env = Env.empty; eff = Pure; ks = []; ts = []; es = [] }

  let next state input =
    let env, xs = List.fold_left_map Check.bind state.env (S.Node.data input) in
    let ks = List.concat_map (fun (ks, _, _, _) -> ks) xs
    and eff = List.fold_left (fun a (_, eff, _, _) -> T.Effect.join a eff) Pure xs
    and ts = List.concat_map (fun (_, _, ts, _) -> ts) xs |> T.Var.normalize
    and es = List.map (fun (_, _, _, b) -> b) xs in
    let state =
      { env
      ; ks = state.ks @ ks
      ; eff = T.Effect.join state.eff eff
      ; ts = state.ts @ ts
      ; es = state.es @ es
      }
    in
    state, es, ts
  ;;
end
