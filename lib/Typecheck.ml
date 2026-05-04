open Util
open (val Trace.init ~scope:"typecheck" ())

open struct
  module S = Lang.Surface
  module T = Lang.Typed
end

module Env : sig
  type t

  val empty : t
  val add : T.Var.t -> T.Type.t -> t -> t
  val add_tvar : T.TVar.t -> t -> t
  val add_mod : T.Var.t -> T.Type.modu -> t -> t
  val add_record : (T.Var.t * T.Type.t) list -> t -> t
  val find : string -> t -> T.Var.t * T.Type.t
  val enter_mod : T.TVar.t -> t -> t
  val enter_lam : T.TVar.t -> t -> t
  val enter_field : T.Var.t -> t -> t
  val path : t -> T.TVar.t T.Path.t
  val domain : t -> T.TVar.Set.t
  val for_subtype : t -> t * T.Zipper.t
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
  let add_mod x (T.Type.TMod (a, t)) env = add_tvar a env |> add x t
  let add_record xs env = List.fold_left (fun env (x, t) -> add x t env) env xs

  let find x env =
    match String.Map.find_opt x env.vars with
    | Some (x, t) ->
      let t = T.Subst.typ T.Subst.id t in
      debug (fun m -> m ~header:"env" "find %a ↦ %a" T.Var.pp x T.Type.pp t);
      x, t
    | None -> failwith (Printf.sprintf "todo error unbound var `%s'" x)
  ;;

  let enter_mod a env = { (add_tvar a env) with path = T.Path.PVar a }
  let enter_lam a env = { env with path = PApp (env.path, a) }
  let enter_field x env = { env with path = PProj (env.path, x) }
  let domain env = env.tvars
  let path env = env.path
  let for_subtype env = env, T.Zipper.of_path env.path

  let for_pp env =
    Pretty.Env.empty
    |> T.TVar.Set.fold Pretty.Env.add_tvar env.tvars
    |> String.Map.fold (fun _ (x, t) -> Pretty.Env.add_var x t) env.vars
  ;;
end

module Implicit = struct
  module T = Lang.Typed

  let view = T.Type.view
  let wrap = T.Type.wrap

  let rec concretize env = function
    | T.Kind.KEmpty -> T.Type.CEmpty
    | T.Kind.KType -> T.Type.CType (TInfer (T.UVar.fresh env) |> wrap)
    | T.Kind.KArrow (k1, k2) ->
      let x = T.TVar.fresh k1 in
      T.Type.CLam (x, concretize (T.TVar.Set.add x env) k2)
    | T.Kind.KRecord ks ->
      T.Type.CRecord (List.map (fun (x, k) -> x, concretize env k) ks)
  ;;

  let generalize level t =
    let rec typ acc t =
      match view t with
      | T.Type.TInfer z when T.UVar.newer level z ->
        let a = T.TVar.fresh T.Kind.KType in
        T.UVar.set z (TAbstr (PVar a));
        let t1 = T.Type.TMod (T.TVar.empty, TInfer z |> wrap) in
        let t1 = T.Type.TMod (a, TSingleton t1 |> wrap)
        and t2 = snd acc in
        ( (fun e -> T.Expr.EGen (t1, fst acc e))
        , T.Type.TArrow (T.Var.fresh "a", t1, Implicit, t2) |> wrap )
      | T.Type.TInfer _ -> acc
      | T.Type.TAbstr p -> path acc p
      | T.Type.TPrim _ -> acc
      | T.Type.TArrow (_, t1, _, t2) -> typ (modu acc t1) t2
      | T.Type.TRecord ts -> List.fold_left (fun xs (_, t) -> typ xs t) acc ts
      | T.Type.TSingleton t -> modu acc t
      | T.Type.TWrapped t -> typ acc t
      | T.Type.TMod (_, t) -> typ acc t
    and modu acc (T.Type.TMod (_, t)) = typ acc t
    and path acc = function
      | T.Path.PVar _ -> acc
      | T.Path.PProj (p, _) -> path acc p
      | T.Path.PApp (p, x) -> path (cons acc x) p
    and cons acc = function
      | T.Type.CEmpty -> acc
      | T.Type.CType t -> typ acc t
      | T.Type.CLam (_, t) -> cons acc t
      | T.Type.CRecord ts -> List.fold_left (fun xs (_, t) -> cons xs t) acc ts
    in
    typ (Fun.id, t) t
  ;;

  let instantiate env t =
    let rec aux (inst, t) =
      match view t with
      | T.Type.TArrow (_, TMod (a1, t1), Implicit, t2) ->
        let tc = concretize env (T.TVar.kind a1) in
        let t1 = T.Subst.typ (T.Subst.one a1 tc) t1
        and t2 = T.Subst.typ (T.Subst.one a1 tc) t2 in
        aux ((fun e -> T.Expr.EInst (inst e, tc, t1)), t2)
      | _ -> inst, t
    in
    aux (Fun.id, t)
  ;;
end

module Subtype = struct
  module T = Lang.Typed

  let view = T.Type.view
  let wrap = T.Type.wrap

  module Env = struct
    include Env

    let enter_mod a env = enter_mod a env, T.Zipper.of_path (PVar a)
    let enter_field a (env, zip) = enter_field a env, T.Zipper.field a zip
    let enter_lam a (env, zip) = enter_lam a env, T.Zipper.lam a zip
    let subst (env, zip) = T.Zipper.subst (T.Path.var (Env.path env)) zip
  end

  exception SubtypeError of string * Env.t * T.Type.t * T.Type.t

  let uvar env = TInfer (T.UVar.fresh (Env.domain env)) |> wrap

  (**
    Subtyping rule [Γ ⊢ t′ ≤ t].

    Checks whether a concrete type [t'] is a subtype of a more general type [t].
    All type variables in [t] and [t'] are bound in the environment [env], except one
    type variable bound by the [path].

    The type [t] is a concrete type except an abstract type variable bound in [path].
    When subtyping succedes, it returns a substitution [s] that can be applied
    to the type variable in [path] to make it a concrete supertype of [t'].
  *)
  let rec typ (env, zip) t' t =
    trace
      (fun m ->
         let pf = m ~header:"subtype" "%a <= %a at %a" in
         pf T.Type.pp t' T.Type.pp t (T.Path.pp T.TVar.pp) (Env.path env))
      (fun (zip, _) m -> m ~header:"subtype" "~> %a" T.Zipper.pp zip)
    @@ fun () ->
    match view t', view t with
    (* Implicit functions *)
    | _, T.Type.TArrow (_, TMod (a1, t1), Implicit, t2) ->
      let zip, f = typ (Env.add_tvar a1 env, zip) t' t2 in
      zip, fun e -> T.Expr.EGen (TMod (a1, t1), f e)
    | TArrow (_, _, Implicit, _), _ ->
      let inst, t' = Implicit.instantiate (Env.domain env) t' in
      let zip, f = typ (env, zip) t' t in
      zip, fun e -> f (inst e)
    (* Unification *)
    | TInfer z', TRecord xs ->
      let t' = wrap (TRecord (List.map (fun (x, _) -> x, uvar env) xs)) in
      assert (T.Type.resolve z' t');
      typ (env, zip) t' t
    | TRecord xs', TInfer z ->
      let t = wrap (TRecord (List.map (fun (x', _) -> x', uvar env) xs')) in
      assert (T.Type.resolve z t);
      typ (env, zip) t' t
    | TInfer z', TArrow (x, TMod (a1, _), Explicit Impure, t2)
      when T.TVar.is_empty a1 && T.Type.is_small t2 ->
      let t1' = T.Type.TMod (T.TVar.empty, uvar env)
      and t2' = T.Type.TMod (T.TVar.empty, uvar env) |> T.Type.wrap in
      let t' = TArrow (x, t1', Explicit Impure, t2') |> wrap in
      assert (T.Type.resolve z' t');
      typ (env, zip) t' t
    | TArrow (x, TMod (a1', _), Explicit _, t2'), TInfer z
      when T.TVar.is_empty a1' && T.Type.is_small t2' ->
      let t1 = T.Type.TMod (T.TVar.empty, uvar env)
      and t2 = T.Type.TMod (T.TVar.empty, uvar env) |> T.Type.wrap in
      let t = TArrow (x, t1, Explicit Impure, t2) |> wrap in
      assert (T.Type.resolve z t);
      typ (env, zip) t' t
    | TInfer z, t | t, TInfer z ->
      if T.Type.resolve z (wrap t)
      then zip, Fun.id
      else raise (SubtypeError ("infer", env, wrap (TInfer z), wrap t))
    (* Subtyping *)
    (* TODO: simplify *)
    | TMod (a', t'), TMod (a, t) ->
      let f =
        let zip, f = typ (Env.enter_mod a (Env.add_tvar a' env)) t' t in
        fun e : T.Expr.expr ->
          T.Expr.EMod (a, T.Expr.ESeal (a', f (T.Expr.EUse e), T.Zipper.get zip, t))
      in
      zip, f
    | TMod (a', t'), _ ->
      let zip, f = typ (Env.add_tvar a' env, zip) t' t in
      zip, fun e -> T.Expr.ESeal (a', f (T.Expr.EUse e), T.Zipper.get zip, t)
    | _, TMod (a, t) ->
      let f =
        let zip, f = typ (Env.enter_mod a env) t' t in
        fun e : T.Expr.expr ->
          T.Expr.EMod (a, T.Expr.ESeal (T.TVar.empty, f e, T.Zipper.get zip, t))
      in
      zip, f
    | TAbstr p', TAbstr p when T.Path.equal (equal env zip) p' p -> zip, Fun.id
    | _, TAbstr p ->
      let t = T.Subst.typ (Env.subst (env, zip)) t in
      (match T.Type.view t with
       | TAbstr p' when T.Path.equal (equal env zip) p' p ->
         raise (SubtypeError ("abstr", env, t', t))
       | _ -> typ (env, zip) t' t)
    | TAbstr _, _ -> raise (SubtypeError ("abstr", env, t', t))
    | TPrim p', TPrim p when T.Prim.equal p' p -> zip, Fun.id
    | TPrim _, _ -> raise (SubtypeError ("prim", env, t', t))
    | TRecord xs', TRecord xs ->
      let aux zip (x, t) =
        let x', t' =
          match T.Var.assoc_opt (T.Var.name x) xs' with
          | Some (x', t') -> x', t'
          | None ->
            raise
              (SubtypeError (Printf.sprintf "record field %s" (T.Var.name x), env, t', t))
        in
        let zip, c = typ (Env.enter_field x (env, zip)) t' t in
        T.Zipper.up zip, T.Expr.BVal (x, c (EVar x'))
      in
      let zip, bs = List.fold_left_map aux zip xs in
      let xs = List.map (fun (x, t) -> x, T.Subst.typ (Env.subst (env, zip)) t) xs in
      zip, fun e -> T.Expr.EStruct (BIncl (Private, e, xs') :: bs, xs)
    | TRecord _, _ -> raise (SubtypeError ("record", env, t', t))
    (*
       Γ,a₁ ⊢ t₁ ≤ ∃α₁′. t₁′ ↑ tₐ     Γ,a₁ ⊢ (∃a₂′. t₂′)[tₐ/a₁′] ≤ (∃a₂. t₂)
      ----------------------------------------------------------------------
       Γ ⊢ (∀a₁′. t₁′ →ͺ∃a₂'. t₂′) ≤ (∀α₁.t₁ →ͺ∃a₂. t₂)
    *)
    | ( TArrow (_, TMod (a1', t1'), Explicit eff', t2')
      , TArrow (x, TMod (a1, t1), Explicit eff, t2) )
      when T.Effect.sub eff' eff ->
      let env = Env.add_tvar a1 env in
      let t1 = T.Subst.typ (Env.subst (env, zip)) t1 in
      let x1 = T.Var.clone x in
      let tc1, f1 =
        let zip, f1 = typ (Env.enter_mod a1' (Env.add_tvar a1 env)) t1 t1' in
        T.Zipper.finish zip, f1
      in
      let t2' = T.Subst.typ (T.Subst.one a1' tc1) t2' in
      let zip, f2 =
        match eff with
        | Impure -> typ (env, zip) t2' (T.Subst.typ (Env.subst (env, zip)) t2)
        | Pure ->
          let zip, f2 = typ (Env.enter_lam a1 (env, zip)) t2' t2 in
          T.Zipper.up zip, f2
      in
      let f e =
        let e = T.Expr.EApp (e, tc1, Explicit eff', f1 (EVar x1)) in
        T.Expr.EFun (x1, TMod (a1, t1), Explicit eff, f2 e)
      in
      zip, f
    | TArrow _, _ -> raise (SubtypeError ("arrow", env, t', t))
    | TSingleton (TMod (a', t')), TSingleton (TMod (a, t))
      when T.TVar.is_empty a'
           && T.TVar.is_empty a
           && T.Type.is_path (Env.path env) t
           && T.Type.is_small t' -> T.Zipper.set t' zip, Fun.id
    | TSingleton t', TSingleton t ->
      let t = T.Subst.modu (Env.subst (env, zip)) t in
      let _ = modu env t' t, modu env t t' in
      zip, Fun.const (T.Expr.EType t)
    | TWrapped t', TWrapped t ->
      let t = T.Subst.typ (Env.subst (env, zip)) t in
      let _ = typ (env, zip) t' t, typ (env, zip) t t' in
      zip, Fun.id
    | TSingleton _, _ -> raise (SubtypeError ("singleton", env, t', t))
    | TWrapped _, _ -> raise (SubtypeError ("wrap", env, t', t))

  (**
    Subtyping rule [Γ ⊢ t′ ≤ ∃a. t]
   *)
  and modu env (TMod (a', t')) (TMod (a, t)) =
    let zip, f = typ (Env.enter_mod a (Env.add_tvar a' env)) t' t in
    fun (T.Expr.EMod (_, e)) ->
      T.Expr.EMod (a, T.Expr.ESeal (a', f e, T.Zipper.get zip, t))

  and equal env zip t' t =
    match t', t with
    | CType t', CType t ->
      (try
         let _, _ = typ (env, zip) t' t, typ (env, zip) t t' in
         true
       with
       | SubtypeError _ -> false)
    | _, _ -> failwith "todo: equality"
  ;;

  let _ =
    let fmt = Format.asprintf "mismatch in %s between %a and %a" in
    let f = function
      | SubtypeError (msg, env, t1, t2) ->
        let typ = Pretty.Print.typ ~prec:0 ~env:(Env.for_pp env) in
        Some (fmt msg typ t1 typ t2)
      | _ -> None
    in
    Printexc.register_printer f
  ;;
end

module Check = struct
  module S = Lang.Surface
  module T = Lang.Typed

  let view = T.Type.view
  let wrap = T.Type.wrap

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

  let path_prepend_compat env (T.Type.TMod (a, t)) =
    ( T.TVar.kind a
    , path_map a (T.Path.prepend (T.Type.Glue.path_to_cons_path (Env.path env))) t )
  ;;

  let path_prepend env t =
    match T.Type.view t with
    | T.Type.TMod (a, t) ->
      let k, t = path_prepend_compat env (T.Type.TMod (a, t)) in
      k, t, fun e -> T.Expr.EUse e
    | _ -> failwith "todo error expected module type"
  ;;

  let field x = T.Var.fresh (S.Node.data x)

  let rec set_kind xs k' k =
    match xs, k with
    | [], _ -> k'
    | x :: xs, T.Kind.KRecord ks ->
      (* TODO: clean *)
      T.Kind.KRecord
        (T.Var.assoc_update
           (T.Var.name x)
           (fun k -> Some (set_kind xs k' (Option.get k)))
           ks)
    | x :: xs, T.Kind.KEmpty -> T.Kind.KRecord [ x, set_kind xs k' T.Kind.KEmpty ]
    | _, _ -> failwith "todo error expected record kind"
  ;;

  (* INVARIANT: returned type has correct paths *)
  let rec typ env t =
    trace
      (fun m ->
         let m = m ~header:"typ" "%a at %a" in
         m Lang.Surface.pp_typ t (T.Path.pp T.TVar.pp) (Env.path env))
      (fun (k, t) m ->
         let m = m ~header:"typ" "~> %a at %a with %a" in
         m T.Type.pp t (T.Path.pp T.TVar.pp) (Env.path env) T.Kind.pp k)
    @@ fun () ->
    match S.Node.data t with
    | S.TPrim p -> T.Kind.KEmpty, T.Type.TPrim p |> wrap
    | S.THole -> T.Kind.KEmpty, T.Type.TInfer (T.UVar.fresh (Env.domain env)) |> wrap
    | S.TType ->
      let abstr = T.Type.TAbstr (T.Type.Glue.path_to_cons_path (Env.path env)) |> wrap in
      T.Kind.KType, T.Type.TSingleton (TMod (T.TVar.empty, abstr)) |> wrap
    | S.TExpr e ->
      let eff, T.Type.TMod (a, t), _ = modu_expr env e in
      let _, t = Implicit.instantiate (Env.domain env) t in
      (match eff, view t with
       | T.Effect.Pure, T.Type.TSingleton t when T.TVar.is_empty a ->
         path_prepend_compat env t
       | T.Effect.Pure, T.Type.TInfer z when T.TVar.is_empty a ->
         let t = T.Type.TInfer (T.UVar.fresh (Env.domain env)) |> wrap in
         assert (T.Type.resolve z (T.Type.TSingleton (TMod (T.TVar.empty, t)) |> wrap));
         T.Kind.KEmpty, t
       | T.Effect.Pure, _ -> failwith "todo error expected singleton type"
       | _, _ when T.TVar.is_empty a -> failwith "todo error expected pure expression"
       | _, _ ->
         let fail =
           Format.kasprintf failwith "todo error expected small type, got kind %a"
         in
         fail T.Kind.pp (T.TVar.kind a))
    | S.TWith (t, xs, t_') ->
      let k, t = typ env t in
      let xs, t_ = proj xs t in
      let env_ = List.fold_left (fun e x -> Env.enter_field x e) env xs in
      let k_', t_' = typ env_ t_' in
      let zip, _ = Subtype.typ (Env.for_subtype env_) t_' t_ in
      set_kind xs k_' k, T.Subst.typ (T.Zipper.subst (T.Path.var (Env.path env)) zip) t
    | S.TStruct xs ->
      let _, xs = List.fold_left_map decl env xs in
      let ks = List.concat_map (fun (ks, _) -> ks) xs
      and ts = List.concat_map (fun (_, ts) -> ts) xs |> T.Var.normalize in
      T.Kind.KRecord ks, T.Type.TRecord ts |> wrap
    | S.TArrow (x, t1, eff, T.Effect.Impure, t2) ->
      if eff == Implicit then failwith "todo error implicit function cannot be impure";
      let x = T.Var.fresh (S.Node.data x) in
      let t1 = modu_typ env t1 in
      let env = Env.add_mod x t1 env in
      let (TMod (a2, t2)) = modu_typ env t2 in
      ( T.Kind.KEmpty
      , T.Type.TArrow (x, t1, T.Type.Explicit T.Effect.Impure, TMod (a2, t2) |> wrap)
        |> wrap )
    | S.TArrow (x, t1, eff, T.Effect.Pure, t2) ->
      let x = T.Var.fresh (S.Node.data x) in
      let (T.Type.TMod (a1, _) as t1) = modu_typ env t1 in
      let env = Env.add_mod x t1 env in
      let k2, t2 = typ (Env.enter_lam a1 env) t2 in
      let eff = if eff = Implicit then T.Type.Implicit else T.Type.Explicit Pure in
      T.Kind.KArrow (T.TVar.kind a1, k2), T.Type.TArrow (x, t1, eff, t2) |> wrap
    | S.TSingletonType t ->
      let t = modu_typ env t in
      T.Kind.KEmpty, T.Type.TSingleton t |> wrap
    | S.TWrapped t ->
      let (T.Type.TMod (a, t)) = modu_typ env t in
      T.Kind.KEmpty, T.Type.TWrapped (TMod (a, t) |> wrap) |> wrap

  and decl env d =
    trace
      (fun m ->
         let m = m ~header:"decl" "%a at %a" in
         m Lang.Surface.pp_decl d (T.Path.pp T.TVar.pp) (Env.path env))
      (fun _ m -> m ~header:"decl" "")
    @@ fun () ->
    match S.Node.data d with
    | S.DVal (x, t) ->
      let x = field x in
      let k, t = typ (Env.enter_field x env) t in
      Env.add x t env, ([ x, k ], [ x, t ])
    | S.DIncl (vis, t) ->
      let k, t = typ env t in
      let ks, ts =
        match k, view t with
        | T.Kind.KRecord ks, T.Type.TRecord xs -> ks, xs
        | T.Kind.KEmpty, T.Type.TRecord xs -> [], xs
        | _ -> failwith "todo error expected record type"
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
         m T.Type.pp t (T.Path.pp T.TVar.pp) (Env.path env) T.Kind.pp k)
    @@ fun () ->
    match S.Node.data e with
    | S.EVar x ->
      let x, t = Env.find (S.Node.data x) env in
      T.Kind.KEmpty, T.Effect.Pure, t, T.Expr.EVar x
    | S.EConst c ->
      T.Kind.KEmpty, T.Effect.Pure, T.Type.TPrim (T.Const.typ c) |> wrap, T.Expr.EConst c
    | S.ECond (x, e1, e2, t) ->
      let x, c = Env.find (S.Node.data x) env in
      (match view c with
       | T.Type.TPrim PBool -> ()
       | T.Type.TInfer z -> assert (T.Type.resolve z (wrap (T.Type.TPrim PBool)))
       | _ -> failwith "todo error");
      let eff1, T.Type.TMod (a1, t1), e1 = modu_expr env e1
      and eff2, T.Type.TMod (a2, t2), e2 = modu_expr env e2
      and k, t = typ env t in
      let _, f1 = Subtype.typ (Env.for_subtype env) (TMod (a1, t1) |> wrap) t
      and _, f2 = Subtype.typ (Env.for_subtype env) (TMod (a2, t2) |> wrap) t in
      let eff = T.Kind.eff k in
      let eff = T.Effect.join eff (T.Effect.join eff1 eff2) in
      k, eff, t, T.Expr.ECond (x, f1 e1, f2 e2, t)
    | S.EStruct xs ->
      let _, xs = List.fold_left_map bind env xs in
      let ks = List.concat_map (fun (ks, _, _, _) -> ks) xs
      and eff = List.fold_left (fun a (_, eff, _, _) -> T.Effect.join a eff) Pure xs
      and ts = List.concat_map (fun (_, _, ts, _) -> ts) xs |> T.Var.normalize
      and xs = List.map (fun (_, _, _, b) -> b) xs in
      T.Kind.KRecord ks, eff, T.Type.TRecord ts |> wrap, T.Expr.EStruct (xs, ts)
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
      let eff, TMod (a2, t2), EMod (_, e2) = modu_expr env e2 in
      let eff =
        match feff, eff with
        | Explicit, eff -> T.Type.Explicit eff
        | Implicit, T.Effect.Pure -> T.Type.Implicit
        | Implicit, T.Effect.Impure ->
          failwith "todo error implicit function cannot be impure"
      in
      let t2, e2 =
        match eff with
        | Explicit Impure ->
          T.Type.TMod (a2, t2) |> wrap, (T.Expr.EMod (a2, e2) : T.Expr.t)
        | Explicit Pure | Implicit -> t2, e2
      in
      let t = T.Type.TArrow (x, t1, eff, t2) |> wrap
      and e = T.Expr.EFun (x, t1, eff, e2) in
      T.Kind.KEmpty, T.Effect.Pure, t, e
    | S.EApp (x, x') ->
      let dom = Env.domain env in
      let x, t = Env.find (S.Node.data x) env in
      let inst, t = Implicit.instantiate dom t in
      let TMod (a1, t1), eff, t2 =
        match view t with
        | T.Type.TArrow (_, t1, T.Type.Explicit eff, t2) -> t1, eff, t2
        | T.Type.TInfer z ->
          let t1 = T.Type.TMod (T.TVar.empty, TInfer (T.UVar.fresh dom) |> wrap)
          and t2 =
            T.Type.TMod (T.TVar.empty, TInfer (T.UVar.fresh dom) |> wrap) |> wrap
          in
          let t = T.Type.TArrow (T.Var.fresh "a", t1, Explicit Impure, t2) in
          assert (T.Type.resolve z (wrap t));
          t1, T.Effect.Impure, t2
        | _ -> failwith "todo error expected function"
      in
      let x', t1' = Env.find (S.Node.data x') env in
      let tc, f =
        let env, _ = Env.for_subtype env in
        let zip, f = Subtype.typ (Subtype.Env.enter_mod a1 env) t1' t1 in
        T.Zipper.finish zip, f
      in
      let k2, t2, e =
        match eff with
        | Impure -> path_prepend env (T.Subst.typ (T.Subst.one a1 tc) t2)
        | Pure -> T.Kind.KEmpty, T.Subst.typ (T.Subst.one a1 tc) t2, Fun.id
      in
      let e = e (T.Expr.EApp (inst (EVar x), tc, Explicit eff, f (EVar x'))) in
      k2, eff, t2, e
    | S.EType t ->
      let t = modu_typ env t in
      T.Kind.KEmpty, T.Effect.Pure, T.Type.TSingleton t |> wrap, T.Expr.EType t
    | S.ESeal (x, t) ->
      let x, t' = Env.find (S.Node.data x) env
      and k, t = typ env t in
      let zip, c = Subtype.typ (Env.for_subtype env) t' t in
      let e = T.Expr.ESeal (T.TVar.empty, c (EVar x), T.Zipper.get zip, t) in
      k, T.Kind.eff k, t, e
    | S.EWrap (x, t) ->
      let k, t = typ env t in
      let t =
        match view t with
        | T.Type.TWrapped t when T.Kind.is_empty k -> t
        | t ->
          let s = Format.asprintf "todo error: expected wrapped type, got %a" in
          let s = s T.Type.pp (wrap t) in
          failwith s
      in
      let x, t' = Env.find (S.Node.data x) env in
      let _, f = Subtype.typ (Env.for_subtype env) t' t in
      let e = T.Expr.EWrap (f (EVar x), t) in
      T.Kind.KEmpty, T.Effect.Pure, T.Type.TWrapped t |> wrap, e
    | S.EUnwrap (x, t) ->
      let dom = Env.domain env in
      let x, t1 = Env.find (S.Node.data x) env in
      let inst, t1 = Implicit.instantiate dom t1 in
      let k, t2 = typ env t in
      let t2 =
        match view t2 with
        | T.Type.TWrapped t2 when T.Kind.is_empty k -> t2
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
      let k2, t2, e2 = path_prepend env t2 in
      let _, f = Subtype.typ (Env.for_subtype env) t1 t2 in
      let e = f (e2 (T.Expr.EUnwrap (inst (EVar x)))) in
      k2, T.Kind.eff k2, t2, e
    | S.EExtern (x, t) ->
      let k, t = typ env t in
      k, T.Kind.eff k, t, T.Expr.EExtern (x, t)

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
      Env.add x t env, ([ x, k ], eff, [ x, t ], T.Expr.BVal (x, gen e))
    | S.BIncl (vis, e) ->
      let k, eff, t, e = expr env e in
      let ks, ts =
        match k, view t with
        | T.Kind.KRecord ks, T.Type.TRecord xs -> ks, xs
        | T.Kind.KEmpty, T.Type.TRecord xs -> [], xs
        | _ -> failwith "todo error expected record type"
      in
      let env = Env.add_record ts env in
      let e = T.Expr.BIncl (vis, e, ts) in
      env, (ks, eff, (if vis = Public then ts else []), e)

  and modu_typ env node =
    let a, set = T.TVar.defer () in
    let k, t = typ (Env.enter_mod a env) node in
    set k;
    T.Type.TMod (a, t)

  and modu_expr env node =
    let a, set = T.TVar.defer () in
    let k, eff, t, e = expr (Env.enter_mod a env) node in
    set k;
    eff, T.Type.TMod (a, t), T.Expr.EMod (a, e)
  ;;

  let file env file =
    let _, _, e = modu_expr env (S.Node.map (fun xs -> Lang.Surface.EStruct xs) file) in
    e
  ;;
end
