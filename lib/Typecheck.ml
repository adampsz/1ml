open Util
open (val Trace.init ~scope:"typecheck" ())

module Implicit = struct
  module T = Lang.Typed

  let view = T.Type.view
  let wrap = T.Type.wrap

  let rec concretize env = function
    | T.Kind.KType -> T.Type.CType (T.Type.TInfer (T.UVar.fresh env) |> wrap)
    | T.Kind.KArrow (k1, k2) ->
      let x = T.TVar.fresh () in
      T.Type.CLam (x, Some k1, concretize (T.TVar.Set.add x env) k2)
    | T.Kind.KRecord ks ->
      T.Type.CRecord (List.map (fun (x, k) -> x, concretize env k) ks)
  ;;

  let _generalize level t =
    let rec typ acc t =
      match view t with
      | T.Type.TInfer z when T.UVar.newer level z ->
        let a, k = T.TVar.fresh (), Some T.Kind.KType in
        T.UVar.set z (TAbstr (PVar a));
        let t1 = T.Type.TMod (T.TVar.null, None, TInfer z |> wrap) in
        let t1 = T.Type.TMod (a, k, TSingleton t1 |> wrap)
        and t2 = T.Type.TMod (T.TVar.null, None, snd acc) in
        T.Implicit.GGen (t1, fst acc), T.Type.TArrow (t1, Implicit, t2) |> wrap
      | T.Type.TInfer _ -> acc
      | T.Type.TAbstr p -> path acc p
      | T.Type.TPrim _ -> acc
      | T.Type.TArrow (t1, _, t2) -> modu (modu acc t1) t2
      | T.Type.TRecord ts -> List.fold_left (fun xs (_, t) -> typ xs t) acc ts
      | T.Type.TSingleton t -> modu acc t
      | T.Type.TWrapped t -> modu acc t
    and modu acc (T.Type.TMod (_, _, t)) = typ acc t
    and path acc = function
      | T.Path.PVar _ -> acc
      | T.Path.PProj (p, _) -> path acc p
      | T.Path.PApp (p, x, _) -> path (cons acc x) p
    and cons acc = function
      | T.Type.CType t -> typ acc t
      | T.Type.CLam (_, _, t) -> cons acc t
      | T.Type.CRecord ts -> List.fold_left (fun xs (_, t) -> cons xs t) acc ts
    in
    typ (T.Implicit.GNil, t) t
  ;;

  let _instantiate env t =
    let rec aux (inst, t) =
      match view t with
      | T.Type.TArrow (TMod (a1, k1, t1), Implicit, TMod (_, _, t2)) ->
        let tc = Option.map (concretize env) k1 in
        let t1 = T.Subst.typ (T.Subst.one_opt a1 tc) t1
        and t2 = T.Subst.typ (T.Subst.one_opt a1 tc) t2 in
        aux (T.Implicit.IInst (inst, tc, t1), t2)
      | _ -> inst, t
    in
    aux (T.Implicit.INil, t)
  ;;

  let instantiate env t =
    let inst, t = _instantiate env t in
    if inst != INil then debug (fun m -> m ~header:"instantiate" "%a" T.PP.typ t);
    inst, t
  ;;

  let generalize level t =
    let gen, t = _generalize level t in
    if gen != GNil then debug (fun m -> m ~header:"generalize" "%a" T.PP.typ t);
    gen, t
  ;;
end

module Subtype = struct
  module T = Lang.Typed

  let view = T.Type.view
  let wrap = T.Type.wrap

  exception SubtypeError of string * T.Type.t * T.Type.t

  let subst_arrow_arg a zip (T.Type.TMod (a1, k1, t1)) =
    T.Type.TMod (a1, k1, T.Subst.typ (T.Zipper.subst a zip) t1)
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
  let rec typ a zip env t' t =
    trace
      (fun m -> m ~header:"subtype" "%a <= %a" T.PP.typ t' T.PP.typ t)
      (fun (zip, c) m ->
         let pf = m ~header:"subtype" "%a ↦ %a ⟨x, %a⟩" in
         pf T.PP.tvar a T.PP.zipper zip (T.PP.coercion Format.pp_print_string) ("x", c))
    @@ fun () ->
    match view t', view t with
    (* Implicit functions *)
    | _, TArrow (_, Implicit, _) ->
      let rec aux env t =
        match view t with
        | T.Type.TArrow (TMod (a1, k1, t1), Implicit, TMod (_, _, t2)) ->
          let zip, g, c = aux (T.TVar.Set.add a1 env) t2 in
          zip, T.Implicit.GGen (TMod (a1, k1, t1), g), c
        | _ ->
          let zip, c = typ a zip env t' t in
          zip, T.Implicit.GNil, c
      in
      let zip, g, c = aux env t in
      zip, T.Coercion.CGeneralize (g, c)
    | TArrow (_, Implicit, _), _ ->
      let inst, t' = Implicit.instantiate env t' in
      let zip, c = typ a zip env t' t in
      zip, T.Coercion.CInstantiate (c, inst)
    (* Unification *)
    | TInfer z', TRecord xs ->
      let zs' = List.map (fun (x, _) -> x, TInfer (T.UVar.fresh env) |> wrap) xs in
      let t' = wrap (TRecord zs') in
      assert (T.Type.resolve z' t');
      typ a zip env t' t
    | TRecord xs', TInfer z ->
      let zs = List.map (fun (x', _) -> x', TInfer (T.UVar.fresh env) |> wrap) xs' in
      let t = wrap (TRecord zs) in
      assert (T.Type.resolve z t);
      typ a zip env t' t
    | TInfer z', TArrow (TMod (_, None, _), Explicit Impure, TMod (_, None, _)) ->
      let t1' = T.Type.TMod (T.TVar.null, None, TInfer (T.UVar.fresh env) |> wrap)
      and t2' = T.Type.TMod (T.TVar.null, None, TInfer (T.UVar.fresh env) |> wrap)
      and eff' = T.Type.Explicit Impure in
      let t' = TArrow (t1', eff', t2') |> wrap in
      assert (T.Type.resolve z' t');
      typ a zip env t' t
    | TArrow (TMod (_, None, _), Explicit _, TMod (_, None, _)), TInfer z ->
      let t1 = T.Type.TMod (T.TVar.null, None, TInfer (T.UVar.fresh env) |> wrap)
      and t2 = T.Type.TMod (T.TVar.null, None, TInfer (T.UVar.fresh env) |> wrap)
      and eff = T.Type.Explicit Impure in
      let t = TArrow (t1, eff, t2) |> wrap in
      assert (T.Type.resolve z t);
      typ a zip env t' t
    | TInfer z, t | t, TInfer z ->
      if T.Type.resolve z (wrap t)
      then zip, T.Coercion.CRefl
      else raise (SubtypeError ("infer", wrap (TInfer z), wrap t))
    (* Subtyping *)
    | TAbstr p', TAbstr p when T.Path.equal (equal a zip env) p' p ->
      zip, T.Coercion.CRefl
    (* TODO: Guard against infinite recursion here *)
    | t', TAbstr _ -> typ a zip env (wrap t') (T.Subst.typ (T.Zipper.subst a zip) t)
    | TAbstr _, _ -> raise (SubtypeError ("abstr", t', t))
    | TPrim p', TPrim p when T.Prim.equal p' p -> zip, T.Coercion.CRefl
    | TPrim _, _ -> raise (SubtypeError ("prim", t', t))
    | TRecord xs', TRecord xs ->
      let aux zip (x, t) =
        let t' =
          match T.Var.assoc_opt (T.Var.name x) xs' with
          | Some (_, t') -> t'
          | None ->
            let t', t = TRecord xs' |> wrap, TRecord xs |> wrap in
            let n = T.Var.name x in
            raise (SubtypeError (Printf.sprintf "record field %s" n, t', t))
        in
        let zip, c = typ a (T.Zipper.field x zip) env t' t in
        T.Zipper.up zip, (x, c)
      in
      let zip, xs = List.fold_left_map aux zip xs in
      zip, T.Coercion.CRecord xs
    | TRecord _, _ -> raise (SubtypeError ("record", t', t))
    (*
       Γ,a₁ ⊢ t₁ ≤ ∃α₁′. t₁′ ↑ tₐ     Γ,a₁ ⊢ (∃a₂′. t₂′)[tₐ/a₁′] ≤ (∃a₂. t₂)
      ----------------------------------------------------------------------
       Γ ⊢ (∀a₁′. t₁′ →ͺ∃a₂'. t₂′) ≤ (∀α₁.t₁ →ͺ∃a₂. t₂)
    *)
    | ( TArrow ((TMod (a1', _, _) as t1'), Explicit eff', t2')
      , TArrow ((TMod (a1, _, _) as t1), Explicit eff, t2) )
      when T.Effect.sub eff' eff ->
      let env = T.TVar.Set.add a1 env in
      let t1 = subst_arrow_arg a zip t1 in
      let (T.Coercion.CMod ((_, tc1), c1, _)) = modu env t1 t1' in
      let t2' = T.Subst.modu (T.Subst.one_opt a1' tc1) t2' in
      (match eff with
       | Pure ->
         let TMod (a1, k1, _), TMod (_, _, t2'), TMod (_, _, t2) = t1, t2', t2 in
         let zip = T.Zipper.lam a1 k1 zip in
         let zip, c2 = typ a zip env t2' t2 in
         let c2 =
           let null = T.TVar.null in
           let t2 = T.Subst.typ (T.Zipper.subst a zip) t2 in
           T.Coercion.CMod ((null, None), c2, TMod (null, None, t2))
         in
         T.Zipper.up zip, T.Coercion.CArrow (t1, eff, (tc1, c1, c2, eff'))
       | Impure ->
         let c2 = modu env t2' (T.Subst.modu (T.Zipper.subst a zip) t2) in
         zip, T.Coercion.CArrow (t1, eff, (tc1, c1, c2, eff')))
    | TArrow _, _ -> raise (SubtypeError ("arrow", t', t))
    | TSingleton (TMod (_, None, t')), TSingleton (TMod (_, None, t))
      when T.Type.is_path (T.Zipper.path a zip) t && T.Type.is_small t' ->
      T.Zipper.typ t' zip, T.Coercion.CRefl
    | TSingleton t', TSingleton t ->
      let t = T.Subst.modu (T.Zipper.subst a zip) t in
      let _, _ = modu env t' t, modu env t t' in
      zip, T.Coercion.CSingleton t
    | TWrapped t', TWrapped t ->
      let t = T.Subst.modu (T.Zipper.subst a zip) t in
      let _, _ = modu env t' t, modu env t t' in
      zip, T.Coercion.CRefl
    | TSingleton _, _ -> raise (SubtypeError ("singleton", t', t))
    | TWrapped _, _ -> raise (SubtypeError ("wrap", t', t))

  (**
    Matching rule [Γ ⊢ t′ ≤ ∃a. t ↑ tₐ].

    This matches a concrete type [t'] agains an abstract type [∃a. t].
   *)
  and matches env t' (T.Type.TMod (a, k, t)) =
    let zip, c = typ a T.Zipper.empty env t' t in
    let tc = T.Zipper.finish zip in
    tc, c, T.Type.TMod (a, k, t)

  (**
    Subtyping rule [Γ ⊢ t′ ≤ ∃a. t]
   *)
  and modu env (T.Type.TMod (a', _, t')) t =
    let tc, c, t = matches (T.TVar.Set.add a' env) t' t in
    T.Coercion.CMod ((a', tc), c, t)

  and equal a zip env t' t =
    match t', t with
    | CType t', CType t ->
      (try
         let _, _ = typ a zip env t' t, typ a zip env t t' in
         true
       with
       | SubtypeError _ -> false)
    | _, _ -> failwith "todo: equality"
  ;;

  (* Public interface that correcly initializes the zipper and then deconstructs it into complete type *)
  let typ path env t' t = typ (T.Path.var path) (T.Zipper.of_path path) env t' t

  let _ =
    let fmt = Format.asprintf "mismstch in %s between %a and %a" in
    let f = function
      | SubtypeError (msg, t1, t2) -> Some (fmt msg T.PP.typ t1 T.PP.typ t2)
      | _ -> None
    in
    Printexc.register_printer f
  ;;
end

module Invariant = struct
  module T = Lang.Typed

  exception InvariantViolation of T.Type.t * T.TVar.t T.Path.t

  let rec typ env p t =
    let check path = function
      | true -> ()
      | false -> raise (InvariantViolation (t, path))
    in
    let rec aux env p t =
      match T.Type.view t with
      | TInfer _ ->
        (* TODO: check environment *)
        ()
      | TAbstr r -> (* TODO *) ()
      | TPrim _ -> ()
      | TArrow (TMod (a1, k1, t1), eff, t2) ->
        let env = T.TVar.Set.add a1 env in
        aux env (T.Path.PVar a1) t1;
        (match eff with
         | Explicit Pure | Implicit ->
           let (TMod (_, k2, t2)) = t2 in
           check p (k2 = None);
           aux env (T.Path.PApp (p, a1, k1)) t2
         | Explicit Impure -> modu env t2)
      | TRecord xs -> List.iter (fun (x, t) -> aux env (T.Path.PProj (p, x)) t) xs
      | TSingleton (TMod (_, None, t)) when T.Type.is_path p t -> ()
      | TSingleton t -> modu env t
      | TWrapped t -> modu env t
    and modu env (T.Type.TMod (a, _, t)) =
      let env = T.TVar.Set.add a env in
      aux env (T.Path.PVar a) t
    in
    aux env p t
  ;;

  let _ =
    Printexc.register_printer (function
      | InvariantViolation (t, p) ->
        let pp = Format.asprintf in
        let pp = pp "%s: type %a does not respect invariant at path %a" in
        Some (pp "invariant violation" T.PP.typ t (T.PP.path T.PP.tvar) p)
      | _ -> None)
  ;;
end

module Check = struct
  module S = Lang.Surface
  module T = Lang.Typed

  let view = T.Type.view
  let wrap = T.Type.wrap

  module Env : sig
    type t

    val empty : t
    val add : T.Var.t -> T.Type.t -> t -> t
    val add_tvar : T.TVar.t -> t -> t
    val add_mod : T.Var.t -> T.Type.modu -> t -> t
    val add_record : (T.Var.t * T.Type.t) list -> t -> t
    val find : string -> t -> T.Var.t * T.Type.t
    val enter_mod : T.TVar.t -> t -> t
    val enter_arrow : T.TVar.t -> T.Kind.t option -> t -> t
    val enter_field : T.Var.t -> t -> t
    val path : t -> T.TVar.t T.Path.t
    val domain : t -> T.TVar.Set.t
  end = struct
    type t =
      { path : T.TVar.t T.Path.t
      ; vars : (T.Var.t * T.Type.t) String.Map.t
      ; tvars : T.TVar.Set.t
      }

    let empty = { path = T.Path.null; vars = String.Map.empty; tvars = T.TVar.Set.empty }
    let add x t env = { env with vars = String.Map.add (T.Var.name x) (x, t) env.vars }
    let add_tvar a env = { env with tvars = T.TVar.Set.add a env.tvars }
    let add_mod x (T.Type.TMod (a, _, t)) env = add_tvar a env |> add x t
    let add_record xs env = List.fold_left (fun env (x, t) -> add x t env) env xs

    let find x env =
      match String.Map.find_opt x env.vars with
      | Some (x, t) ->
        let t = T.Subst.typ T.Subst.id t in
        debug (fun m -> m ~header:"env" "find %a ↦ %a" T.PP.var x T.PP.typ t);
        x, t
      | None -> failwith (Printf.sprintf "todo error unbound var `%s'" x)
    ;;

    let enter_mod a env = { (add_tvar a env) with path = T.Path.PVar a }
    let enter_arrow a k env = { env with path = PApp (env.path, a, k) }
    let enter_field x env = { env with path = PProj (env.path, x) }
    let domain env = env.tvars
    let path env = env.path
  end

  let rec proj xs t =
    match view t, xs with
    | _, [] -> [], t
    | T.Type.TRecord ts, x :: xs ->
      (match T.Var.assoc_opt (S.Node.data x) ts with
       | Some (x, t) ->
         let xs, t = proj xs t in
         x :: xs, t
       | None -> failwith "todo error missing field")
    | _, _ -> failwith "todo error expected record"
  ;;

  let path_map a f t =
    let aux p =
      T.Type.TAbstr (if T.TVar.equal (T.Path.var p) a then f p else p) |> wrap
    in
    T.Subst.typ aux t
  ;;

  let path_prepend env (T.Type.TMod (a, k, t)) =
    k, path_map a (T.Path.prepend (T.Type.Glue.path_to_cons_path (Env.path env))) t
  ;;

  let field x = T.Var.fresh (S.Node.data x)

  let rec set_kind xs k' k =
    match xs, k with
    | [], _ -> k'
    | x :: xs, Some (T.Kind.KRecord ks) ->
      let ks = T.Var.assoc_update (T.Var.name x) (set_kind xs k') ks in
      T.Kind.record ks
    | x :: xs, None ->
      let k = set_kind xs k' None in
      Option.fold ~none:k ~some:(fun k -> T.Kind.record [ x, k ]) k
    | _, _ -> failwith "todo error expected record kind"
  ;;

  (* INVARIANT: returned type has correct paths *)
  let rec typ env t =
    trace
      (fun m ->
         let m = m ~header:"typ" "%a at %a" in
         m Lang.Surface.PP.typ t (T.PP.path T.PP.tvar) (Env.path env))
      (fun (k, t) m ->
         let m = m ~header:"typ" "~> %a at %a with %a" in
         m T.PP.typ t (T.PP.path T.PP.tvar) (Env.path env) T.PP.kind k)
    @@ fun () ->
    match S.Node.data t with
    | S.TPrim p -> None, T.Type.TPrim p |> wrap
    | S.THole -> None, T.Type.TInfer (T.UVar.fresh (Env.domain env)) |> wrap
    | S.TType ->
      let abstr = T.Type.TAbstr (T.Type.Glue.path_to_cons_path (Env.path env)) |> wrap in
      Some T.Kind.KType, T.Type.TSingleton (TMod (T.TVar.null, None, abstr)) |> wrap
    | S.TExpr e ->
      let eff, T.Type.TMod (_, k, t), _ = modu_expr env e in
      let _, t = Implicit.instantiate (Env.domain env) t in
      (match k, eff, view t with
       | None, T.Effect.Pure, T.Type.TSingleton t -> path_prepend env t
       | None, T.Effect.Pure, T.Type.TInfer z ->
         let t = T.Type.TInfer (T.UVar.fresh (Env.domain env)) |> wrap in
         assert (T.Type.resolve z (T.Type.TSingleton (TMod (T.TVar.null, None, t)) |> wrap));
         None, t
       | _, _, _ -> failwith "todo error expected singleton type")
    | S.TWith (t, xs, t_') ->
      let k, t = typ env t in
      let xs, t_ = proj xs t in
      let env_ = List.fold_left (fun e x -> Env.enter_field x e) env xs in
      let k'_, t_' = typ env_ t_' in
      let zip, _ = Subtype.typ (Env.path env_) (Env.domain env) t_' t_ in
      set_kind xs k'_ k, T.Subst.typ (T.Zipper.subst (T.Path.var (Env.path env)) zip) t
    | S.TStruct xs ->
      let _, xs = List.fold_left_map decl env xs in
      let ks = List.concat_map (fun (ks, _) -> ks) xs
      and ts = List.concat_map (fun (_, ts) -> ts) xs |> T.Var.normalize in
      T.Kind.record ks, T.Type.TRecord ts |> wrap
    | S.TArrow (x, t1, eff, T.Effect.Impure, t2) ->
      if eff == Implicit then failwith "todo error implicit function cannot be impure";
      let t1 = modu_typ env t1 in
      let env = Env.add_mod (T.Var.fresh (S.Node.data x)) t1 env in
      let t2 = modu_typ env t2 in
      None, T.Type.TArrow (t1, T.Type.Explicit T.Effect.Impure, t2) |> wrap
    | S.TArrow (x, t1, eff, T.Effect.Pure, t2) ->
      let (T.Type.TMod (a1, k1, _) as t1) = modu_typ env t1 in
      let env = Env.add_mod (T.Var.fresh (S.Node.data x)) t1 env in
      let k2, t2 = typ (Env.enter_arrow a1 k1 env) t2 in
      let eff = if eff = Implicit then T.Type.Implicit else T.Type.Explicit Pure in
      T.Kind.arrow k1 k2, T.Type.TArrow (t1, eff, TMod (T.TVar.null, None, t2)) |> wrap
    | S.TSingletonType t ->
      let t = modu_typ env t in
      None, T.Type.TSingleton t |> wrap
    | S.TWrapped t ->
      let t = modu_typ env t in
      None, T.Type.TWrapped t |> wrap

  and decl env d =
    trace
      (fun m ->
         let m = m ~header:"decl" "%a at %a" in
         m Lang.Surface.PP.decl d (T.PP.path T.PP.tvar) (Env.path env))
      (fun _ m -> m ~header:"decl" "")
    @@ fun () ->
    match S.Node.data d with
    | S.DVal (x, t) ->
      let x = field x in
      let k, t = typ (Env.enter_field x env) t in
      let ks = Option.fold ~none:[] ~some:(fun k -> [ x, k ]) k in
      Env.add x t env, (ks, [ x, t ])
    | S.DIncl (vis, t) ->
      let k, t = typ env t in
      let ks, ts =
        match k, view t with
        | Some (T.Kind.KRecord ks), T.Type.TRecord xs -> ks, xs
        | None, T.Type.TRecord xs -> [], xs
        | _ -> failwith "todo error expected record type"
      in
      let env = Env.add_record ts env in
      env, (ks, if vis = Public then ts else [])

  and expr env e =
    trace
      (fun m ->
         let m = m ~header:"expr" "%a at %a" in
         m Lang.Surface.PP.expr e (T.PP.path T.PP.tvar) (Env.path env))
      (fun (k, _, t, _) m ->
         let m = m ~header:"expr" ":: %a at %a with %a" in
         m T.PP.typ t (T.PP.path T.PP.tvar) (Env.path env) T.PP.kind k)
    @@ fun () ->
    match S.Node.data e with
    | S.EVar x ->
      let x, t = Env.find (S.Node.data x) env in
      None, T.Effect.Pure, t, T.Expr.EVar x
    | S.EConst c ->
      None, T.Effect.Pure, T.Type.TPrim (T.Const.typ c) |> wrap, T.Expr.EConst c
    | S.ECond (x, e1, e2, t) ->
      let x, c = Env.find (S.Node.data x) env in
      let bool = T.Type.TPrim PBool |> wrap in
      let _ = Subtype.typ (Env.path env) (Env.domain env) c bool in
      let eff1, t1, T.Expr.EMod (_, _, e1) = modu_expr env e1
      and eff2, t2, T.Expr.EMod (_, _, e2) = modu_expr env e2
      and t = modu_typ env t in
      let (T.Coercion.CMod (_, c1, _)) = Subtype.modu (Env.domain env) t1 t
      and (T.Coercion.CMod (_, c2, _)) = Subtype.modu (Env.domain env) t2 t in
      let k, t = path_prepend env t in
      let eff = T.Kind.eff k in
      let eff = T.Effect.join eff (T.Effect.join eff1 eff2) in
      k, eff, t, T.Expr.ECond (x, e1, c1, e2, c2, t)
    | S.EStruct xs ->
      let _, xs = List.fold_left_map bind env xs in
      let tcs = List.concat_map (fun (ks, _, _, _) -> ks) xs
      and eff = List.fold_left (fun a (_, eff, _, _) -> T.Effect.join a eff) Pure xs
      and ts = List.concat_map (fun (_, _, ts, _) -> ts) xs |> T.Var.normalize
      and xs = List.map (fun (_, _, _, b) -> b) xs in
      T.Kind.record tcs, eff, T.Type.TRecord ts |> wrap, T.Expr.EStruct (xs, ts)
    | S.EProj (e, x) ->
      let k, eff, t, e = expr env e in
      let ts =
        match view t with
        | T.Type.TRecord ts -> ts
        | T.Type.TInfer z ->
          let x = T.Var.fresh (S.Node.data x) in
          let ts = [ x, T.Type.TInfer (T.UVar.fresh (Env.domain env)) |> wrap ] in
          assert (T.Type.resolve z (T.Type.TRecord ts |> wrap));
          ts
        | _ -> failwith "todo error expected record type"
      in
      (match T.Var.assoc_opt (S.Node.data x) ts with
       | Some (x, t) -> k, eff, t, T.Expr.EProj (e, x, t)
       | None -> failwith "todo error missing field")
    | S.EFun (x, t1, feff, e2) ->
      let t1 = modu_typ env t1 in
      let x = T.Var.fresh (S.Node.data x) in
      let env = Env.add_mod x t1 env in
      let eff, t2, e2 = modu_expr env e2 in
      let eff =
        match feff, eff with
        | Explicit, eff -> T.Type.Explicit eff
        | Implicit, T.Effect.Pure -> T.Type.Implicit
        | Implicit, T.Effect.Impure ->
          failwith "todo error implicit function cannot be impure"
      in
      let t = T.Type.TArrow (t1, eff, t2) |> wrap
      and e = T.Expr.EFun (x, t1, eff, e2) in
      None, T.Effect.Pure, t, e
    | S.EApp (x, x') ->
      let dom = Env.domain env in
      let x, t = Env.find (S.Node.data x) env in
      let inst, t = Implicit.instantiate dom t in
      let TMod (a1, k1, t1), eff, t2 =
        match view t with
        | T.Type.TArrow (t1, T.Type.Explicit eff, t2) -> t1, eff, t2
        | T.Type.TInfer z ->
          let t1 = T.Type.TMod (T.TVar.null, None, TInfer (T.UVar.fresh dom) |> wrap)
          and t2 = T.Type.TMod (T.TVar.null, None, TInfer (T.UVar.fresh dom) |> wrap) in
          let t = T.Type.TArrow (t1, Explicit Impure, t2) in
          assert (T.Type.resolve z (wrap t));
          t1, T.Effect.Impure, t2
        | _ -> failwith "todo error expected function"
      in
      let x', t1' = Env.find (S.Node.data x') env in
      let tc, c, _ = Subtype.matches dom t1' (TMod (a1, k1, t1)) in
      let t2 = T.Subst.modu (T.Subst.one_opt a1 tc) t2 in
      let k2, t2 = path_prepend env t2 in
      k2, eff, t2, T.Expr.EApp (x, inst, tc, Explicit eff, x', c)
    | S.EType t ->
      let t = modu_typ env t in
      None, T.Effect.Pure, T.Type.TSingleton t |> wrap, T.Expr.EType t
    | S.ESeal (x, t) ->
      let x, t' = Env.find (S.Node.data x) env
      and k, t = typ env t in
      let zip, c = Subtype.typ (Env.path env) (Env.domain env) t' t in
      k, T.Kind.eff k, t, T.Expr.ESeal (x, c, T.Zipper.get zip, t)
    | S.EWrap (x, t) ->
      let k, t = typ env t in
      let t =
        match k, view t with
        | None, T.Type.TWrapped t -> t
        | _, t ->
          let s = Format.asprintf "todo error: expected wrapped type, got %a" in
          let s = s T.PP.typ (wrap t) in
          failwith s
      in
      let dom = Env.domain env in
      let x, t' = Env.find (S.Node.data x) env in
      let _, c, _ = Subtype.matches dom t' t in
      None, T.Effect.Pure, T.Type.TWrapped t |> wrap, T.Expr.EWrap (x, c, t)
    | S.EUnwrap (x, t) ->
      let dom = Env.domain env in
      let x, t1 = Env.find (S.Node.data x) env in
      let inst, t1 = Implicit.instantiate dom t1 in
      let k, t2 = typ env t in
      let t2 =
        match k, view t2 with
        | None, T.Type.TWrapped t2 -> t2
        | _ -> failwith "todo error expected wrapped type"
      in
      let t1 =
        match view t1 with
        | T.Type.TWrapped t -> t
        | T.Type.TInfer z ->
          assert (T.Type.resolve z (T.Type.TWrapped t2 |> wrap));
          t2
        | _ -> failwith "todo error expected wrapped type"
      in
      let (T.Coercion.CMod (_, c, _)) = Subtype.modu dom t1 t2 in
      let k2, t2 = path_prepend env t2 in
      k2, T.Kind.eff k2, t2, T.Expr.EUnwrap (x, inst, c, t2)
    | S.EExternal (x, t) ->
      let k, t = typ env t in
      k, T.Kind.eff k, t, T.Expr.EExternal (x, t)

  and bind env b =
    trace
      (fun m ->
         let m = m ~header:"bind" "%a at %a" in
         m Lang.Surface.PP.bind b (T.PP.path T.PP.tvar) (Env.path env))
      (fun _ m -> m ~header:"bind" "")
    @@ fun () ->
    match S.Node.data b with
    | S.BVal (x, e) ->
      let x = field x in
      let level = T.UVar.stamp () in
      let k, eff, t, e = expr (Env.enter_field x env) e in
      let ks = Option.fold ~none:[] ~some:(fun k -> [ x, k ]) k in
      let gen, t = Implicit.generalize level t in
      Env.add x t env, (ks, eff, [ x, t ], T.Expr.BVal (x, e, gen))
    | S.BIncl (vis, e) ->
      let k, eff, t, e = expr env e in
      let ks, ts =
        match k, view t with
        | Some (T.Kind.KRecord ks), T.Type.TRecord xs -> ks, xs
        | None, T.Type.TRecord xs -> [], xs
        | _ -> failwith "todo error expected record type"
      in
      let env = Env.add_record ts env in
      let e = T.Expr.BIncl (vis, e, ts, List.map fst ks) in
      env, (ks, eff, (if vis = Public then ts else []), e)

  and modu_typ env node =
    let a = T.TVar.fresh () in
    let k, t = typ (Env.enter_mod a env) node in
    T.Type.TMod (a, k, t)

  and modu_expr env node =
    let a = T.TVar.fresh () in
    let k, eff, t, e = expr (Env.enter_mod a env) node in
    eff, T.Type.TMod (a, k, t), T.Expr.EMod (a, k, e)
  ;;

  let file env file =
    let _, _, e = modu_expr env (S.Node.map (fun xs -> Lang.Surface.EStruct xs) file) in
    e
  ;;
end
