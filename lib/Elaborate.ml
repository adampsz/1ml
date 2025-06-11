open Middle
open Surface.Node
module Var = Expr.Var
module TVar = Type.TVar
module Ident = Surface.Ident
module S = Surface.Ast
open Util

let trace = Tracing.init ~width:7 "elaborate"

module PP = struct
  let pp_paths ppf ps =
    let pp_sep ppf () = Format.pp_print_string ppf "; "
    and pp_path ppf (Middle.Type.Path.Set.Ex p) = Middle.PP.pp_path ppf p in
    Format.fprintf ppf "{ %a }" (Middle.Type.Path.Set.pp ~pp_sep pp_path) ps
  ;;

  let pp_subst sub ppf ps =
    let rec path_var : type k. k Type.path -> Type.TVar.ex = function
      | Type.Path.TVar a -> Type.TVar.Ex a
      | Type.Path.TApp (p, _) -> path_var p
    in
    let pp_sep ppf () = Format.pp_print_string ppf "; "
    and pp_val ppf (Middle.Type.Path.Set.Ex p) =
      let (Type.TVar.Ex a) = path_var p in
      match Middle.Type.Subst.find_opt a sub with
      | Some t -> Format.fprintf ppf "%a => %a" Middle.PP.pp_path p Middle.PP.pp_typ t
      | None -> Format.fprintf ppf "%a" Middle.PP.pp_path p
    in
    let pp_paths = Format.pp_print_iter ~pp_sep Middle.Type.Path.Set.iter pp_val in
    Format.fprintf ppf "{ %a }" pp_paths ps
  ;;

  let pp_expr_fun env ppf f =
    let x = Expr.Var.fresh ~name:"X" () in
    let e = f env (Expr.EVar x) in
    Format.fprintf ppf "λ X. %a" Middle.PP.pp_expr e
  ;;
end

module Error = struct
  open Diagnostic.Error

  let expected_pure_expression ?span _e = error ?span "expected pure expression"

  let expected_type what ?span t =
    error ?span "expected %s, but got %a" what Middle.PP.pp_qtyp t
  ;;

  let expected_concrete_type = expected_type "a concrete type"
  let expected_singleton_type = expected_type "a singleton"
  let expected_record_type = expected_type "a record"
  let expected_function_type = expected_type "a function"
  let expected_boolean_type = expected_type "a boolean"
  let expected_wrapped_type = expected_type "a wrapped type"

  let subtype_type_mismatch ?span t' t =
    let pp = error ?span "type mismatch, expected %a, but got %a" in
    pp Middle.PP.pp_typ t Middle.PP.pp_typ t'
  ;;

  let undefined_record_field ?span id =
    error ?span "undefined record field %a" Surface.PP.pp_ident id
  ;;

  let unbound_variable ?span id =
    error ?span "unbound variable `%a'" Surface.PP.pp_ident id
  ;;
end

module Env : sig
  open Type
  open Expr
  open Field

  type t

  val empty : t
  val add_var : Ident.t -> ttyp -> t -> Var.t * t
  val add_tvar : 'k TVar.t -> t -> t
  val add_tvars : TVar.ex list -> t -> t
  val add_qtyp : Ident.t -> TVar.ex list -> ttyp -> t -> Var.t * t
  val add_record : TVar.ex list -> (field * ttyp) list -> t -> Var.t list * t
  val find_var : Ident.t -> t -> Var.t * ttyp
end = struct
  open Field
  open Type

  type t = (Var.t * ttyp) Ident.Map.t

  let empty = Ident.Map.empty

  let add_var id t env =
    let x = Var.fresh ?name:(Ident.name id.data) () in
    x, Ident.Map.add id.data (x, t) env
  ;;

  let add_tvar _x env = env
  let add_tvars _ats env = env

  let add_qtyp x ats t env =
    let env = add_tvars ats env in
    add_var x t env
  ;;

  let add_record ats ts env =
    let ident = function
      | FNamed name -> { data = Ident.Named name; span = None }
      | FSynthetic id -> { data = Ident.Synthetic id; span = None }
    in
    let add_field (f, t) (xs, env) =
      let x, env = add_var (ident f) t env in
      x :: xs, env
    in
    let env = add_tvars ats env in
    List.fold_right add_field ts ([], env)
  ;;

  let find_var id env =
    match Ident.Map.find_opt id.data env with
    | Some t -> t
    | None -> Error.unbound_variable ?span:id.span id
  ;;
end

module Subtype = struct
  open Type
  open Expr

  let ident_of_field ?span = function
    | Field.FNamed name -> { data = Ident.Named name; span }
    | Field.FSynthetic id -> { data = Ident.Synthetic id; span }
  ;;

  let path_matches ps t =
    match Type.as_path t with
    | Some p -> Path.Set.mem p ps
    | None -> false
  ;;

  let path_subst t p =
    let rec aux : type k. k typ -> k path -> _ =
      fun t -> function
        | TVar x -> Subst.add x t Subst.empty
        | TApp (p, x) -> aux (TLam (x, t)) p
    in
    aux t p
  ;;

  let paths_of_tvars ats =
    let f = fun ps (TVar.Ex a) -> Path.Set.add (TVar a) ps in
    List.fold_left f Path.Set.empty ats
  ;;

  let sub_pack sub ats =
    let f (TVar.Ex a) = TPack (a, Subst.find a sub) in
    List.map f ats
  ;;

  let rec _qsubtype env t' t ps =
    let open Type in
    let open Expr in
    match t', t with
    | TExists ([], t'), TExists ([], t) -> subtype env t' t ps
    | TExists (ats', t'), TExists (ats, t) ->
      let sub, f = subtype (Env.add_tvars ats' env) t' t (paths_of_tvars ats) in
      let f env x =
        let y = Var.fresh () in
        let e = EPack (f env (EVar y), sub_pack sub ats, t) in
        EUnpack (ats', y, TExists (ats', t'), x, e)
      in
      Subst.empty, f

  and _subtype env t' t ps =
    match t', t with
    | TPrim p', TPrim p when p' = p -> Subst.empty, fun _ e -> e
    | TPrim _, _ -> Error.subtype_type_mismatch t' t
    | TSingleton (TExists ([], t')), TSingleton (TExists ([], t))
      when Type.is_small t' && path_matches ps t ->
      path_subst t' (Type.as_path t |> Option.get), fun _ e -> e
    | TNeu n', TNeu n ->
      let rec aux : type k1 k2. k1 neutral -> k2 neutral -> (k1, k2) eq =
        fun n' n ->
        match n', n with
        | TVar a', TVar a ->
          (match TVar.hequal a' a with
           | Some eq -> eq
           | None -> Error.subtype_type_mismatch t' t)
        | TVar _, _ -> Error.subtype_type_mismatch t' t
        | TApp (n', t'), TApp (n, t) ->
          let Equal = aux n' n in
          (match Kind.hequal (Type.kind t) KType with
           | Some Equal ->
             equiv env (t' : ttyp) (t : ttyp);
             Equal
           | None -> Error.subtype_type_mismatch t' t)
        | TApp _, _ -> Error.subtype_type_mismatch t' t
      in
      let _ = aux n' n in
      Subst.empty, fun _ e -> e
    | TNeu _, _ -> Error.subtype_type_mismatch t' t
    | TSingleton t', TSingleton t ->
      qequiv env t' t;
      Subst.empty, fun _ _ -> ESingleton t
    | TSingleton _, _ -> Error.subtype_type_mismatch t' t
    | TWrapped t', TWrapped t ->
      qequiv env t' t;
      Subst.empty, fun _ e -> e
    | TWrapped _, _ -> Error.subtype_type_mismatch t' t
    | TEffArrow (ats', t1', eff', t2'), TEffArrow (ats, t1, eff, t2)
      when Effect.sub eff' eff ->
      let add_args ats p =
        let f (TVar.Ex a) p =
          match p with
          | Some (Path.Set.Ex p) ->
            (match Path.kind p, TVar.kind a with
             | KArrow (k1, _), k1' ->
               (match Kind.hequal k1 k1' with
                | Some Equal -> Some (Path.Set.Ex (TApp (p, a)))
                | _ -> None)
             | _, _ -> None)
          | None -> None
        in
        List.fold_right f ats (Some p)
      in
      (* TODO: δ₂Σ = Σ *)
      let sub1, fe1 = subtype (Env.add_tvars ats env) t1 t1' (paths_of_tvars ats') in
      let ps' = Path.Set.filter_map (add_args ats) ps in
      let sub2, fe2 = qsubtype (Env.add_tvars ats env) (Subst.qsubst sub1 t2') t2 ps' in
      let f env x =
        let y = Var.fresh () in
        let ts = List.map (fun (TVar.Ex a) -> Type.Ex (Type.Subst.find a sub1)) ats' in
        let e = EEffApp (x, ts, fe1 env (EVar y), eff') in
        EEffLam (ats, y, t1, eff, fe2 env e)
      in
      sub2, f
    | TEffArrow _, _ -> Error.subtype_type_mismatch t' t
    | TRecord fs', TRecord fs ->
      let rec aux = function
        | _, [], _ -> Subst.empty, []
        | ts', (l, t) :: ts, p ->
          (match List.assoc_opt l ts' with
           | Some t' ->
             let sub, f = subtype env t' t p in
             let ts = List.map (fun (l, t) -> l, Subst.subst sub t) ts in
             let subs, fs = aux (ts', ts, p) in
             Subst.merge_disjoint sub subs, f :: fs
           | None -> Error.undefined_record_field (ident_of_field l))
      in
      let ts, fes = aux (fs', fs, ps) in
      let f env x =
        let ts = List.map2 (fun f (l, _) -> l, f env (EProj (x, l))) fes fs in
        ERecord ts
      in
      ts, f
    | TRecord _, _ -> Error.subtype_type_mismatch t' t

  and equiv env t' t =
    let _, _ = subtype env t' t Path.Set.empty
    and _, _ = subtype env t t' Path.Set.empty in
    ()

  and qequiv env t' t =
    let _, _ = qsubtype env t' t Path.Set.empty
    and _, _ = qsubtype env t t' Path.Set.empty in
    ()

  and subtype env t' t ps =
    Tracing.trace4 trace "subtype" _subtype env t' t ps
    @@ fun tr f ->
    Middle.PP.(Tracing.printf tr "%a <= %a %a" pp_typ t' pp_typ t PP.pp_paths ps);
    let sub, fe = f () in
    Tracing.printf tr "%a, %a" (PP.pp_subst sub) ps (PP.pp_expr_fun env) fe;
    sub, fe

  and qsubtype env t' t ps =
    Tracing.trace4 trace "subtype" _qsubtype env t' t ps
    @@ fun tr f ->
    Middle.PP.(Tracing.printf tr "%a <= %a %a" pp_qtyp t' pp_qtyp t PP.pp_paths ps);
    let sub, fe = f () in
    Tracing.printf tr "%a, %a" (PP.pp_subst sub) ps (PP.pp_expr_fun env) fe;
    sub, fe
  ;;
end

module Elab = struct
  let tvar name kind =
    match name with
    | Some { data; _ } -> TVar.fresh ?name:(Ident.name data) kind
    | None -> TVar.fresh kind
  ;;

  let var name =
    match name with
    | Some { data; _ } -> Var.fresh ?name:(Ident.name data) ()
    | None -> Var.fresh ()
  ;;

  let field { data; _ } =
    match data with
    | Ident.Named name -> Field.FNamed name
    | Ident.Synthetic id -> Field.FSynthetic id
  ;;

  let const = function
    | Prim.ConstUnit _ -> Prim.PrimUnit
    | Prim.ConstInt _ -> Prim.PrimInt
    | Prim.ConstFloat _ -> Prim.PrimFloat
    | Prim.ConstBool _ -> Prim.PrimBool
    | Prim.ConstString _ -> Prim.PrimString
  ;;

  let paths_of_tvars ats =
    let f = fun (Type.TVar.Ex x) -> Type.Path.Ex (TVar x) in
    List.map f ats
  ;;

  let ats_repack ats =
    let f (Type.TVar.Ex a) = Expr.TPack (a, TNeu (TVar a)) in
    List.map f ats
  ;;

  let sub_pack sub ats =
    let f (Type.TVar.Ex a) = Expr.TPack (a, Type.Subst.find a sub) in
    List.map f ats
  ;;

  let rec _typ ?name env { data; span } =
    let open Effect in
    let open Kind in
    let open Type in
    let skolemize ats1 ats2 =
      let rec aux : type k. _ -> k kind -> _ -> _ * k neutral =
        fun x k -> function
          | [] -> TVar.rekind k x |> fun y -> TVar.Ex y, TVar y
          | TVar.Ex a :: ats ->
            let y, t = aux x (KArrow (TVar.kind a, k)) ats in
            y, TApp (t, TNeu (TVar a))
      in
      let f sub (TVar.Ex x) =
        let y, t = aux x (TVar.kind x) ats1 in
        Subst.add x (TNeu t) sub, y
      in
      let sub, ats2 = List.fold_left_map f Subst.empty ats2 in
      ats2, sub
    in
    match data with
    | S.TPrim p -> TExists ([], TPrim p)
    | S.TType ->
      let a = tvar name KType in
      let typ = TExists ([], TNeu (TVar a)) in
      TExists ([ TVar.Ex a ], Middle.Type.TSingleton typ)
    | S.TExpr e ->
      (match expr env e with
       | Pure, TExists ([], TSingleton t), _ -> t
       | Pure, t', _ -> Error.expected_singleton_type ?span t'
       | Impure, _, _ -> Error.expected_pure_expression ?span e)
    | S.TWith (t1, ids, t2) ->
      let rec proj t ids =
        match t, ids with
        | t, [] -> t
        | TRecord ts, id :: ids ->
          (match List.assoc_opt (field id) ts with
           | Some t -> proj t ids
           | None -> Error.undefined_record_field ?span:id.span id)
        | t, _ -> Error.expected_record_type ?span:t1.span (TExists ([], t))
      in
      let (TExists (ats1, t1)) = typ env t1
      and (TExists (ats2, t2)) = typ env t2 in
      let t = proj t1 ids in
      let free = Type.free t in
      let ats11 = List.filter (fun (TVar.Ex a) -> not (TVar.Set.mem a free)) ats1 in
      let ats12 = List.filter (fun (TVar.Ex a) -> TVar.Set.mem a free) ats1 in
      let env' = env |> Env.add_tvars ats11 |> Env.add_tvars ats2 in
      let sub, _ = Subtype.subtype env' t2 t (Subtype.paths_of_tvars ats12) in
      TExists (ats11 @ ats2, Subst.subst sub t1)
    | S.TStruct xs ->
      let a, t = decl env xs in
      TExists (a, TRecord t)
    | S.TArrow (x, t1, Impure, t2) ->
      let (TExists (ats1, t1)) = typ ~name:x env t1 in
      let (TExists (ats2, t2)) = typ (Env.add_qtyp x ats1 t1 env |> snd) t2 in
      TExists ([], TEffArrow (ats1, t1, Impure, TExists (ats2, t2)))
    | S.TArrow (x, t1, Pure, t2) ->
      let (TExists (ats1, t1)) = typ ~name:x env t1 in
      let (TExists (ats2, t2)) = typ (Env.add_qtyp x ats1 t1 env |> snd) t2 in
      let ats2, sub = skolemize ats1 ats2 in
      TExists (ats2, TEffArrow (ats1, t1, Pure, TExists ([], Subst.subst sub t2)))
    | S.TSingleton e ->
      (match expr env e with
       | Pure, t, _ -> t
       | Impure, _, _ -> Error.expected_pure_expression ?span e)
    | S.TWrapped t ->
      let t = typ env t in
      TExists ([], TWrapped t)

  and decl env = function
    | [] -> [], []
    | { data = S.DVal (x, t); _ } :: ds ->
      let (TExists (ats1, t1)) = typ ~name:x env t in
      let ats2, t2 = decl (Env.add_qtyp x ats1 t1 env |> snd) ds in
      ats1 @ ats2, (field x, t1) :: t2
    | { data = S.DIncl t; _ } :: ds ->
      (match typ env t with
       | TExists (ats1, TRecord t1) ->
         let _, env = Env.add_record ats1 t1 env in
         let ats2, t2 = decl env ds in
         ats1 @ ats2, t1 @ t2
       | t' -> Error.expected_record_type ?span:t.span t')

  and _expr ?name env ({ data; span } : Surface.Ast.expr) =
    let open Effect in
    let open Type in
    let open Expr in
    match data with
    | EVar x ->
      let x, t = Env.find_var x env in
      Pure, TExists ([], t), EVar x
    | EConst c -> Pure, TExists ([], TPrim (const c)), EConst c
    | ECond (x, e1, e2, t) ->
      (match Env.find_var x env with
       | x, TPrim PrimBool ->
         let eff1, t1, e1 = expr env e1
         and eff2, t2, e2 = expr env e2
         and (TExists (ats, t)) = typ env t in
         let _, fe1 = Subtype.qsubtype env t1 (TExists ([], t)) Path.Set.empty
         and _, fe2 = Subtype.qsubtype env t2 (TExists ([], t)) Path.Set.empty in
         let eff = if ats = [] then Effect.join eff1 eff2 else Impure in
         let t = TExists (ats, t) in
         let e = ECond (EVar x, fe1 env e1, fe2 env e2) in
         eff, t, e
       | _, t -> Error.expected_boolean_type ?span:x.span (TExists ([], t)))
    | EStruct bs -> bind env bs
    | EProj (e, l) ->
      (match expr env e, field l with
       | (eff, TExists (ats, TRecord ts), e), f ->
         (match List.assoc_opt f ts with
          | Some t ->
            let y = var name
            and t0 = TExists (ats, TRecord ts)
            and ats, sub = Subst.add_fresh_tvars ats Subst.empty in
            let t = Subst.subst sub t in
            let e =
              EUnpack (ats, y, t0, e, EPack (EProj (EVar y, f), ats_repack ats, t))
            in
            eff, TExists (ats, t), e
          | None -> Error.undefined_record_field ?span l)
       | (_, t, _), _ -> Error.expected_record_type ?span:e.span t)
    | EFun (x, t, e) ->
      let (TExists (ats1, t1)) = typ ~name:x env t in
      let x, env = Env.add_qtyp x ats1 t1 env in
      let eff, t2, e = expr env e in
      let t = TExists ([], TEffArrow (ats1, t1, eff, t2))
      and e = EEffLam (ats1, x, t1, eff, e) in
      Pure, t, e
    | EApp (x1, x2) ->
      (match Env.find_var x1 env, Env.find_var x2 env with
       | (x1, TEffArrow (ats1, t1, eff, t)), (x2, t2) ->
         let sub, fe = Subtype.subtype env t2 t1 (Subtype.paths_of_tvars ats1) in
         let ts = List.map (fun (TVar.Ex a) -> Ex (Subst.find a sub)) ats1 in
         let e = EEffApp (EVar x1, ts, fe env (EVar x2), eff) in
         eff, Subst.qsubst sub t, e
       | (_, t), _ -> Error.expected_function_type ?span (TExists ([], t)))
    | EType t ->
      let t = typ ?name env t in
      Pure, TExists ([], TSingleton t), ESingleton t
    | ESeal (x, t) ->
      let x, t1 = Env.find_var x env
      and (TExists (ats2, t2)) = typ env t in
      let sub, fe = Subtype.subtype env t1 t2 (Subtype.paths_of_tvars ats2) in
      let eff = if ats2 = [] then Pure else Impure in
      let e = EPack (fe env (EVar x), sub_pack sub ats2, t2) in
      eff, TExists (ats2, t2), e
    | EWrap (x, t) ->
      (match Env.find_var x env, typ env t with
       | (x, t'), TExists ([], TWrapped t) ->
         let _, fe = Subtype.qsubtype env (TExists ([], t')) t Path.Set.empty in
         Pure, TExists ([], TWrapped t), EWrap (fe env (EVar x))
       | _, t -> Error.expected_wrapped_type ?span t)
    | EUnwrap (x, t) ->
      (match Env.find_var x env, typ env t with
       | (x, TWrapped t'), TExists ([], TWrapped t) ->
         let _, fe = Subtype.qsubtype env t' t Path.Set.empty in
         let (TExists (ats, _)) = t in
         (if ats = [] then Pure else Impure), t, fe env (EUnwrap (EVar x))
       | (_, TWrapped _), t' -> Error.expected_wrapped_type ?span:t.span t'
       | (_, t'), _ -> Error.expected_wrapped_type ?span:t.span (TExists ([], t')))
    | EExternal (s, t) ->
      (match typ ~name:{ data = Named s; span = None } env t with
       | TExists ([], t) -> Pure, TExists ([], t), EExternal (s, t)
       | t' -> Error.expected_concrete_type ?span:t.span t')

  and bind env bs =
    let open Effect in
    let open Type in
    let open Expr in
    let rec aux env eff1 ats1 fields = function
      | [] ->
        let fields = List.uniq_by (fun (l1, _, _) (l2, _, _) -> l1 = l2) fields in
        let ts = List.rev_map (fun (l, t, _) -> l, t) fields
        and es = List.rev_map (fun (l, _, e) -> l, e) fields
        and ats = List.rev ats1 in
        let e = EPack (ERecord es, ats_repack ats, TRecord ts) in
        eff1, TExists (ats, TRecord ts), e
        (* TODO: These two arms can be simplified/merged *)
      | { data = S.BVal (x, e); _ } :: bs ->
        let eff2, TExists (ats2, t2), e2 = expr env e in
        let l, (x, env) = field x, Env.add_qtyp x ats2 t2 env in
        let eff = Effect.join eff1 eff2
        and ats = List.rev_append ats1 ats2
        and fields = (l, t2, EVar x) :: fields in
        let eff, t, e = aux env eff ats fields bs in
        eff, t, EUnpack (ats2, x, TExists (ats2, t2), e2, e)
      | { data = S.BIncl e; _ } :: bs ->
        let aux_f x (l, t) = l, t, EVar x
        and aux_e y e x (l, t) = ELet (x, TExists ([], t), EProj (EVar y, l), e) in
        (match expr env e with
         | eff2, TExists (ats2, TRecord t2), e2 ->
           let xs, env = Env.add_record ats2 t2 env in
           let eff = Effect.join eff1 eff2
           and ats = List.rev_append ats1 ats2
           and fields = List.rev_append (List.map2 aux_f xs t2) fields in
           let eff, t, e = aux env eff ats fields bs in
           let y = Var.fresh () in
           let e = List.fold_left2 (aux_e y) e xs t2 in
           let e = EUnpack (ats2, y, TExists (ats2, TRecord t2), e2, e) in
           eff, t, e
         | _, t, _ -> Error.expected_record_type ?span:e.span t)
    in
    aux env Pure [] [] bs

  and typ ?name env t =
    Tracing.trace2 trace "type" (_typ ?name) env t
    @@ fun tr f ->
    Tracing.printf tr "%a" Surface.PP.pp_typ t;
    let t = f () in
    Tracing.printf tr "~> %a" Middle.PP.pp_qtyp t;
    t

  and expr ?name env e =
    Tracing.trace2 trace "expr" (_expr ?name) env e
    @@ fun tr f ->
    Tracing.printf tr "%a" Surface.PP.pp_expr e;
    let eff, t, e = f () in
    Tracing.printf tr "~> %a" Middle.PP.pp_expr e;
    Tracing.printf tr ":: %a" Middle.PP.pp_qtyp t;
    eff, t, e
  ;;
end
