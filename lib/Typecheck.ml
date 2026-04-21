open Util
open (val Trace.init ~scope:"typecheck" ())

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
        and t2 = T.Type.TMod (T.TVar.empty, snd acc) in
        (fun e -> T.Expr.EGen (t1, fst acc e)), T.Type.TArrow (t1, Implicit, t2) |> wrap
      | T.Type.TInfer _ -> acc
      | T.Type.TAbstr p -> path acc p
      | T.Type.TPrim _ -> acc
      | T.Type.TArrow (t1, _, t2) -> modu (modu acc t1) t2
      | T.Type.TRecord ts -> List.fold_left (fun xs (_, t) -> typ xs t) acc ts
      | T.Type.TSingleton t -> modu acc t
      | T.Type.TWrapped t -> modu acc t
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
      | T.Type.TArrow (TMod (a1, t1), Implicit, TMod (_, t2)) ->
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
    type t =
      { tvar : T.TVar.t
      ; tvars : T.TVar.Set.t
      }

    let of_path path tvars = { tvar = T.Path.var path; tvars }
    let enter_mod a env = { env with tvar = a }, T.Zipper.empty
    let add a env = { env with tvars = T.TVar.Set.add a env.tvars }
    let domain env = env.tvars
    let path env zip = T.Zipper.path env.tvar zip
    let subst env zip = T.Zipper.subst env.tvar zip
  end

  exception SubtypeError of string * T.Type.t * T.Type.t

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
  let rec typ (env, zip) (k', t') t =
    trace
      (fun m ->
         let pf = m ~header:"subtype" "%a <= %a at %a" in
         pf T.Type.pp t' T.Type.pp t (T.Path.pp T.TVar.pp) (Env.path env zip))
      (fun (zip, f) m ->
         let pf = m ~header:"subtype" "~> %a, λX. %a" in
         pf T.Zipper.pp zip T.Expr.pp (f (T.Expr.EVar (T.Var.fresh "X"))))
    @@ fun () ->
    match view t', view t with
    (* Implicit functions *)
    | _, T.Type.TArrow (TMod (a1, t1), Implicit, TMod (_, t2)) ->
      let zip, f = typ (Env.add a1 env, zip) (k', t') t2 in
      zip, fun e -> T.Expr.EGen (TMod (a1, t1), f e)
    | TArrow (_, Implicit, _), _ ->
      let inst, t' = Implicit.instantiate (Env.domain env) t' in
      let zip, f = typ (env, zip) (k', t') t in
      zip, fun e -> f (inst e)
    (* Unification *)
    | TInfer z', TRecord xs ->
      let t' = wrap (TRecord (List.map (fun (x, _) -> x, uvar env) xs)) in
      assert (T.Type.resolve z' t');
      typ (env, zip) (k', t') t
    | TRecord xs', TInfer z ->
      let t = wrap (TRecord (List.map (fun (x', _) -> x', uvar env) xs')) in
      assert (T.Type.resolve z t);
      typ (env, zip) (k', t') t
    | TInfer z', TArrow (TMod (a1, _), Explicit Impure, TMod (a2, _))
      when T.TVar.is_empty a1 && T.TVar.is_empty a2 ->
      let t1' = T.Type.TMod (T.TVar.empty, uvar env)
      and t2' = T.Type.TMod (T.TVar.empty, uvar env) in
      let t' = TArrow (t1', Explicit Impure, t2') |> wrap in
      assert (T.Type.resolve z' t');
      typ (env, zip) (k', t') t
    | TArrow (TMod (a1', _), Explicit _, TMod (a2', _)), TInfer z
      when T.TVar.is_empty a1' && T.TVar.is_empty a2' ->
      let t1 = T.Type.TMod (T.TVar.empty, uvar env)
      and t2 = T.Type.TMod (T.TVar.empty, uvar env) in
      let t = TArrow (t1, Explicit Impure, t2) |> wrap in
      assert (T.Type.resolve z t);
      typ (env, zip) (k', t') t
    | TInfer z, t | t, TInfer z ->
      if T.Type.resolve z (wrap t)
      then zip, Fun.id
      else raise (SubtypeError ("infer", wrap (TInfer z), wrap t))
    (* Subtyping *)
    | TAbstr p', TAbstr p when T.Path.equal (equal env zip) p' p -> zip, Fun.id
    | t', TAbstr _ ->
      (* TODO: Guard against infinite recursion here *)
      typ (env, zip) (k', wrap t') (T.Subst.typ (Env.subst env zip) t)
    | TAbstr _, _ -> raise (SubtypeError ("abstr", t', t))
    | TPrim p', TPrim p when T.Prim.equal p' p -> zip, Fun.id
    | TPrim _, _ -> raise (SubtypeError ("prim", t', t))
    | TRecord xs', TRecord xs ->
      let ks' =
        match k' with
        | T.Kind.KRecord ks' -> ks'
        | T.Kind.KEmpty -> []
        | _ -> assert false
      in
      let aux zip (x, t) =
        let x', t' =
          match T.Var.assoc_opt (T.Var.name x) xs' with
          | Some (x', t') -> x', t'
          | None ->
            let t', t = TRecord xs' |> wrap, TRecord xs |> wrap in
            let n = T.Var.name x in
            raise (SubtypeError (Printf.sprintf "record field %s" n, t', t))
        in
        let zip, c =
          typ
            (env, T.Zipper.field x zip)
            (List.assoc_opt x' ks' |> Option.value ~default:T.Kind.KEmpty, t')
            t
        in
        T.Zipper.up zip, T.Expr.BVal (x, c (EVar x'))
      in
      let zip, bs = List.fold_left_map aux zip xs in
      let xs = List.map (fun (x, t) -> x, T.Subst.typ (Env.subst env zip) t) xs in
      let f e =
        let b = T.Expr.BIncl (Private, e, xs', List.map fst ks') in
        let tmp = T.Var.fresh "tmp" in
        (* TODO: this is only a temporary hack, there should be only a single struct and not tmp variable *)
        T.Expr.EStruct
          ([ b; BVal (tmp, EStruct (bs, xs)); BIncl (Public, EVar tmp, xs, []) ], xs)
      in
      zip, f
    | TRecord _, _ -> raise (SubtypeError ("record", t', t))
    (*
       Γ,a₁ ⊢ t₁ ≤ ∃α₁′. t₁′ ↑ tₐ     Γ,a₁ ⊢ (∃a₂′. t₂′)[tₐ/a₁′] ≤ (∃a₂. t₂)
      ----------------------------------------------------------------------
       Γ ⊢ (∀a₁′. t₁′ →ͺ∃a₂'. t₂′) ≤ (∀α₁.t₁ →ͺ∃a₂. t₂)
    *)
    | ( TArrow (TMod (a1', t1'), Explicit eff', t2')
      , TArrow (TMod (a1, t1), Explicit eff, t2) )
      when T.Effect.sub eff' eff ->
      let env = Env.add a1 env in
      let t1 = T.Subst.typ (Env.subst env zip) t1 in
      let x1 = T.Var.fresh "tmp" in
      let tc1, f1 =
        let zip, f1 = typ (Env.enter_mod a1' (Env.add a1 env)) (T.TVar.kind a1, t1) t1' in
        T.Zipper.finish zip, f1
      in
      let t2' = T.Subst.modu (T.Subst.one a1' tc1) t2' in
      let zip, f2 =
        match eff with
        | Impure -> zip, modu env t2' (T.Subst.modu (Env.subst env zip) t2)
        | Pure ->
          let TMod (_, t2'), TMod (a2, t2) = t2', t2 in
          let k2' =
            match k' with
            | T.Kind.KArrow (_, k2') -> k2'
            | T.Kind.KEmpty -> T.Kind.KEmpty
            | _ -> assert false
          in
          let zip, f2 = typ (env, T.Zipper.lam a1 zip) (k2', t2') t2 in
          T.Zipper.up zip, fun (T.Expr.EMod (_, e)) -> T.Expr.EMod (a2, f2 e)
      in
      let f e =
        let (TMod (a2', _)) = t2' in
        let e = T.Expr.EApp (e, tc1, Explicit eff', f1 (EVar x1)) in
        let e = f2 (EMod (a2', e)) in
        T.Expr.EFun (x1, TMod (a1, t1), Explicit eff, e)
      in
      zip, f
    | TArrow _, _ -> raise (SubtypeError ("arrow", t', t))
    | TSingleton (TMod (a', t')), TSingleton (TMod (a, t))
      when T.TVar.is_empty a'
           && T.TVar.is_empty a
           && T.Type.is_path (Env.path env zip) t
           && T.Type.is_small t' -> T.Zipper.set t' zip, Fun.id
    | TSingleton t', TSingleton t ->
      let t = T.Subst.modu (Env.subst env zip) t in
      let _ = modu env t' t, modu env t t' in
      zip, Fun.const (T.Expr.EType t)
    | TWrapped t', TWrapped t ->
      let t = T.Subst.modu (Env.subst env zip) t in
      let _ = modu env t' t, modu env t t' in
      zip, Fun.id
    | TSingleton _, _ -> raise (SubtypeError ("singleton", t', t))
    | TWrapped _, _ -> raise (SubtypeError ("wrap", t', t))

  (**
    Subtyping rule [Γ ⊢ t′ ≤ ∃a. t]
   *)
  and modu env (TMod (a', t')) (TMod (a, t)) =
    let zip, f = typ (Env.enter_mod a (Env.add a' env)) (T.TVar.kind a', t') t in
    fun (T.Expr.EMod (_, e)) ->
      T.Expr.EMod (a, T.Expr.ESeal (T.Expr.EMod (a', f e), T.Zipper.get zip, t))

  and modu_typ path env (T.Type.TMod (a', t')) t =
    let env = Env.add a' (Env.of_path path env) in
    let zip, f =
      typ
        (Env.of_path path (Env.domain env), T.Zipper.of_path path)
        (T.TVar.kind a', t')
        t
    in
    fun (T.Expr.EMod (a, e)) -> T.Expr.ESeal (T.Expr.EMod (a, f e), T.Zipper.get zip, t)

  and equal env zip t' t =
    match t', t with
    | CType t', CType t ->
      (try
         let _, _ =
           typ (env, zip) (T.Kind.KEmpty, t') t, typ (env, zip) (T.Kind.KEmpty, t) t'
         in
         true
       with
       | SubtypeError _ -> false)
    | _, _ -> failwith "todo: equality"
  ;;

  let _ =
    let fmt = Format.asprintf "mismstch in %s between %a and %a" in
    let f = function
      | SubtypeError (msg, t1, t2) -> Some (fmt msg T.Type.pp t1 T.Type.pp t2)
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
    val subtype : t -> Subtype.Env.t * T.Zipper.t
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
    let subtype env = Subtype.Env.of_path env.path env.tvars, T.Zipper.of_path env.path
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

  let path_prepend env (T.Type.TMod (a, t)) =
    ( T.TVar.kind a
    , path_map a (T.Path.prepend (T.Type.Glue.path_to_cons_path (Env.path env))) t )
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
       | T.Effect.Pure, T.Type.TSingleton t when T.TVar.is_empty a -> path_prepend env t
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
      let zip, _ = Subtype.typ (Env.subtype env_) (k_', t_') t_ in
      set_kind xs k_' k, T.Subst.typ (T.Zipper.subst (T.Path.var (Env.path env)) zip) t
    | S.TStruct xs ->
      let _, xs = List.fold_left_map decl env xs in
      let ks = List.concat_map (fun (ks, _) -> ks) xs
      and ts = List.concat_map (fun (_, ts) -> ts) xs |> T.Var.normalize in
      T.Kind.KRecord ks, T.Type.TRecord ts |> wrap
    | S.TArrow (x, t1, eff, T.Effect.Impure, t2) ->
      if eff == Implicit then failwith "todo error implicit function cannot be impure";
      let t1 = modu_typ env t1 in
      let env = Env.add_mod (T.Var.fresh (S.Node.data x)) t1 env in
      let t2 = modu_typ env t2 in
      T.Kind.KEmpty, T.Type.TArrow (t1, T.Type.Explicit T.Effect.Impure, t2) |> wrap
    | S.TArrow (x, t1, eff, T.Effect.Pure, t2) ->
      let (T.Type.TMod (a1, _) as t1) = modu_typ env t1 in
      let env = Env.add_mod (T.Var.fresh (S.Node.data x)) t1 env in
      let k2, t2 = typ (Env.enter_lam a1 env) t2 in
      let eff = if eff = Implicit then T.Type.Implicit else T.Type.Explicit Pure in
      ( T.Kind.KArrow (T.TVar.kind a1, k2)
      , T.Type.TArrow (t1, eff, TMod (T.TVar.empty, t2)) |> wrap )
    | S.TSingletonType t ->
      let t = modu_typ env t in
      T.Kind.KEmpty, T.Type.TSingleton t |> wrap
    | S.TWrapped t ->
      let t = modu_typ env t in
      T.Kind.KEmpty, T.Type.TWrapped t |> wrap

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
       | _ -> failwith "todo");
      let eff1, t1, e1 = modu_expr env e1
      and eff2, t2, e2 = modu_expr env e2
      and k, t = typ env t in
      let f1 = Subtype.modu_typ (Env.path env) (Env.domain env) t1 t
      and f2 = Subtype.modu_typ (Env.path env) (Env.domain env) t2 t in
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
      T.Kind.KEmpty, T.Effect.Pure, t, e
    | S.EApp (x, x') ->
      let dom = Env.domain env in
      let x, t = Env.find (S.Node.data x) env in
      let inst, t = Implicit.instantiate dom t in
      let TMod (a1, t1), eff, t2 =
        match view t with
        | T.Type.TArrow (t1, T.Type.Explicit eff, t2) -> t1, eff, t2
        | T.Type.TInfer z ->
          let t1 = T.Type.TMod (T.TVar.empty, TInfer (T.UVar.fresh dom) |> wrap)
          and t2 = T.Type.TMod (T.TVar.empty, TInfer (T.UVar.fresh dom) |> wrap) in
          let t = T.Type.TArrow (t1, Explicit Impure, t2) in
          assert (T.Type.resolve z (wrap t));
          t1, T.Effect.Impure, t2
        | _ -> failwith "todo error expected function"
      in
      let x', t1' = Env.find (S.Node.data x') env in
      let tc, f =
        let env, _ = Env.subtype env in
        let zip, f = Subtype.typ (Subtype.Env.enter_mod a1 env) (T.Kind.KEmpty, t1') t1 in
        T.Zipper.finish zip, f
      in
      let k2, t2 = path_prepend env (T.Subst.modu (T.Subst.one a1 tc) t2) in
      let e = T.Expr.EApp (inst (EVar x), tc, Explicit eff, f (EVar x')) in
      k2, eff, t2, e
    | S.EType t ->
      let t = modu_typ env t in
      T.Kind.KEmpty, T.Effect.Pure, T.Type.TSingleton t |> wrap, T.Expr.EType t
    | S.ESeal (x, t) ->
      let x, t' = Env.find (S.Node.data x) env
      and k, t = typ env t in
      let zip, c = Subtype.typ (Env.subtype env) (T.Kind.KEmpty, t') t in
      let e = T.Expr.ESeal (EMod (T.TVar.empty, c (EVar x)), T.Zipper.get zip, t) in
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
      let f = Subtype.modu (Env.subtype env |> fst) (TMod (T.TVar.empty, t')) t in
      let e = T.Expr.EWrap (f (EMod (T.TVar.empty, EVar x)), t) in
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
      let k2, t2 = path_prepend env t2 in
      let f = Subtype.modu_typ (Env.path env) (Env.domain env) t1 t2 in
      let (TMod (a, _)) = t1 in
      let e = f (EMod (a, T.Expr.EUnwrap (inst (EVar x)))) in
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
      let e = T.Expr.BIncl (vis, e, ts, List.map fst ks) in
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
