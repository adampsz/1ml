open Util
open (val Trace.init ~scope:"fomega" ())
include Common

module Kind = struct
  type ktyp = private unit

  type _ t =
    | KType : ktyp t
    | KArrow : 'k1 t * 'k2 t -> ('k1 -> 'k2) t

  type 'k kind = 'k t

  let rec hequal : type k1 k2. k1 t -> k2 t -> (k1, k2) eq option =
    fun k1 k2 ->
    match k1, k2 with
    | KType, KType -> Some Equal
    | KArrow (k1a, k1b), KArrow (k2a, k2b) ->
      (match hequal k1a k2a, hequal k1b k2b with
       | Some Equal, Some Equal -> Some Equal
       | _, _ -> None)
    | _, _ -> None
  ;;

  let equal (x : 'k t) (y : 'k t) : bool = x = y

  let rec pp : type k. _ -> k t -> _ =
    fun ppf -> function
    | KType -> Format.fprintf ppf "@[<2>FOmega.Kind.KType@]"
    | KArrow (k1, k2) ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Kind.KArrow (@,%a,@ %a@,))@]" in
      pf pp k1 pp k2
  ;;
end

module TVar : sig
  type 'k t

  val id : 'k t -> int
  val kind : 'k t -> 'k Kind.t
  val name : 'k t -> string option
  val fresh : ?name:string -> 'k Kind.t -> 'k t
  val clone : 'k t -> 'k t
  val equal : 'k t -> 'k t -> bool
  val compare : 'k t -> 'k t -> int
  val hequal : 'k1 t -> 'k2 t -> ('k1, 'k2) eq option
  val hcompare : 'k1 t -> 'k2 t -> int
  val pp : Format.formatter -> 'k t -> unit

  module Map : HMap.S with type 'k key = 'k t
end = struct
  module UID = Counter.Make ()

  type 'k t = UID.t * 'k Kind.t * string option

  let id (x, _, _) = UID.get x
  let kind (_, k, _) = k
  let name (_, _, n) = n
  let fresh ?name k = UID.next (), k, name
  let clone (_, k, name) = fresh ?name k
  let hequal (x1, k1, _) (x2, k2, _) = if x1 = x2 then Kind.hequal k1 k2 else None
  let hcompare (x1, _, _) (x2, _, _) = UID.compare x1 x2
  let equal (x1, _, _) (x2, _, _) = x1 = x2
  let compare = hcompare

  let pp ppf = function
    | x, _, None -> Format.fprintf ppf "#%d" (UID.get x)
    | x, _, Some n -> Format.fprintf ppf "%s#%d" n (UID.get x)
  ;;

  module Map = HMap.Make (struct
      type nonrec 'k t = 'k t

      let hcompare = hcompare
    end)
end

module Type = struct
  open Kind

  (** τ *)
  type _ typ =
    | TVar : 'k TVar.t -> 'k typ (** α *)
    | TPrim : Prim.t -> ktyp typ (** b *)
    | TArrow : ktyp typ * ktyp typ -> ktyp typ (** τ → τ *)
    | TRecord : (string * ktyp typ) list -> ktyp typ (** { l: τ, …, l: τ } *)
    | TForall : 'k TVar.t * ktyp typ -> ktyp typ (** ∀κ. τ *)
    | TExists : 'k TVar.t * ktyp typ -> ktyp typ (** ∃κ. τ *)
    | TLam : 'k1 TVar.t * 'k2 typ -> ('k1 -> 'k2) typ (** λα:κ. τ *)
    | TApp : ('k1 -> 'k2) typ * 'k1 typ -> 'k2 typ (** τ τ *)

  type 'k t = 'k typ
  type ttyp = ktyp typ

  let rec kind : type k. k typ -> k kind = function
    | TVar x -> TVar.kind x
    | TPrim _ -> KType
    | TArrow _ -> KType
    | TRecord _ -> KType
    | TForall _ -> KType
    | TExists _ -> KType
    | TLam (x, t) -> KArrow (TVar.kind x, kind t)
    | TApp (t1, _) -> kind t1 |> fun (KArrow (_, k2)) -> k2
  ;;

  let rec is_free : type k. _ -> k typ -> bool =
    fun x -> function
    | TVar y -> TVar.hequal x y <> None
    | TPrim _ -> false
    | TArrow (t1, t2) -> is_free x t1 || is_free x t2
    | TRecord ts -> List.exists (fun (_, t) -> is_free x t) ts
    | TForall (y, t) -> TVar.hequal x y = None && is_free x t
    | TExists (y, t) -> TVar.hequal x y = None && is_free x t
    | TLam (y, t) -> TVar.hequal x y = None && is_free x t
    | TApp (t1, t2) -> is_free x t1 || is_free x t2
  ;;

  module Subst = struct
    module Sub = TVar.Map.Make (struct
        type nonrec 'k t = 'k typ
      end)

    let add_var x sub =
      let y = TVar.clone x in
      y, Sub.add x (TVar y) sub
    ;;

    let rec subst : type k. Sub.t -> k typ -> k typ =
      fun sub -> function
      | TVar x ->
        (match Sub.find_opt x sub with
         | Some t -> t
         | None -> TVar x)
      | TPrim b -> TPrim b
      | TArrow (t1, t2) -> TArrow (subst sub t1, subst sub t2)
      | TRecord ts -> TRecord (List.map (fun (l, t) -> l, subst sub t) ts)
      | TForall (x, t) ->
        let x, sub = add_var x sub in
        TForall (x, subst sub t)
      | TExists (x, t) ->
        let x, sub = add_var x sub in
        TExists (x, subst sub t)
      | TLam (x, t) ->
        let x, sub = add_var x sub in
        TLam (x, subst sub t)
      | TApp (t1, t2) -> TApp (subst sub t1, subst sub t2)
    ;;

    let subst_one x st t = subst (Sub.singleton x st) t
    let subst_tvar x y t = subst_one x (TVar y) t
  end

  module Normal = struct
    type _ neutral =
      | NVar : 'k TVar.t -> 'k neutral
      | NApp : 'k1 typ * ('k1 -> 'k2) neutral -> 'k2 neutral

    type _ t =
      | NNeutral : 'k neutral -> 'k t
      | NLam : 'k1 TVar.t * 'k2 typ -> ('k1 -> 'k2) t
      | NPrim : Prim.t -> ktyp t
      | NArrow : ttyp * ttyp -> ktyp t
      | NRecord : (string * ttyp) list -> ktyp t
      | NForall : 'k TVar.t * ttyp -> ktyp t
      | NExists : 'k TVar.t * ttyp -> ktyp t

    let rec normalize : type k. k typ -> k t = function
      | TVar x -> NNeutral (NVar x)
      | TPrim p -> NPrim p
      | TArrow (t1, t2) -> NArrow (t1, t2)
      | TRecord ts -> NRecord ts
      | TForall (x, t) -> NForall (x, t)
      | TExists (x, t) -> NExists (x, t)
      | TLam (t1, t2) -> NLam (t1, t2)
      | TApp (t1, t2) ->
        (match normalize t1 with
         | NNeutral n -> NNeutral (NApp (t2, n))
         | NLam (x, t) -> Subst.subst_one x t2 t |> normalize)
    ;;
  end

  module Equiv = struct
    type 'k normal = 'k Normal.t
    type 'k neutral = 'k Normal.neutral

    let equiv t1 t2 =
      let rec aux : type k. k typ -> k typ -> bool =
        fun t1 t2 ->
        match Normal.normalize t1, Normal.normalize t2 with
        | NNeutral n1, NNeutral n2 -> auxn n1 n2 <> None
        | NNeutral _, _ -> false
        | NLam (x1, t1), NLam (x2, t2) -> aux t1 (Subst.subst_tvar x2 x1 t2)
        | NLam _, _ -> false
        | NPrim p1, NPrim p2 -> p1 = p2
        | NPrim _, _ -> false
        | NArrow (ta1, tv1), NArrow (ta2, tv2) -> aux ta1 ta2 && aux tv1 tv2
        | NArrow _, _ -> false
        | NRecord ts1, NRecord ts2 ->
          let eq (l1, t1) (l2, t2) = l1 = l2 && aux t1 t2 in
          List.equal eq ts1 ts2
        | NRecord _, _ -> false
        | NForall (x1, t1), NForall (x2, t2) ->
          (match Kind.hequal (TVar.kind x1) (TVar.kind x2) with
           | Some Equal -> aux t1 (Subst.subst_tvar x2 x1 t2)
           | None -> false)
        | NForall _, _ -> false
        | NExists (x1, t1), NExists (x2, t2) ->
          (match Kind.hequal (TVar.kind x1) (TVar.kind x2) with
           | Some Equal -> aux t1 (Subst.subst_tvar x2 x1 t2)
           | None -> false)
        | NExists _, _ -> false
      and auxn : type k1 k2. k1 neutral -> k2 neutral -> (k1, k2) eq option =
        fun n1 n2 ->
        match n1, n2 with
        | NVar x1, NVar x2 -> TVar.hequal x1 x2
        | NVar _, _ -> None
        | NApp (t1, n1), NApp (t2, n2) ->
          (match auxn n1 n2 with
           | Some Equal -> if aux t1 t2 then Some Equal else None
           | None -> None)
        | NApp _, _ -> None
      in
      aux t1 t2
    ;;
  end

  let rec pp : type k. _ -> k t -> _ =
    fun ppf -> function
    | TVar x ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Type.TVar@ %a@])" in
      pf TVar.pp x
    | TPrim p ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Type.TPrim@ %a@])" in
      pf Prim.pp p
    | TArrow (t1, t2) ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Type.TArrow (@,%a,@ %a@,))@]" in
      pf pp t1 pp t2
    | TRecord ts ->
      let pp_entry = Format.pp_print_record Format.pp_print_string pp in
      Format.fprintf ppf "(@[<2>FOmega.Type.TRecord@ %a@])" pp_entry ts
    | TForall (x, t) ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Type.TForall (@,%a,@ %a@,))@]" in
      pf TVar.pp x pp t
    | TExists (x, t) ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Type.TExists (@,%a,@ %a@,))@]" in
      pf TVar.pp x pp t
    | TLam (x, t) ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Type.TLam (@,%a,@ %a@,))@]" in
      pf TVar.pp x pp t
    | TApp (t1, t2) ->
      let pf = Format.fprintf ppf "(@[<2>FOmega.Type.TApp (@,%a,@ %a@,))@]" in
      pf pp t1 pp t2
  ;;

  let pp_typ = pp
  let pp_ttyp ppf (t : ttyp) = pp ppf t
end

module Var : sig
  type t

  val fresh : ?name:string -> unit -> t
  val clone : t -> t
  val id : t -> int
  val name : t -> string option
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit

  module Map : Map.S with type key = t
end = struct
  module UID = Counter.Make ()

  type t = UID.t * string option

  let fresh ?name () = UID.next (), name
  let clone (_, name) = fresh ?name ()
  let id (x, _) = UID.get x
  let name (_, n) = n
  let equal (x1, _) (x2, _) = x1 = x2
  let compare (x1, _) (x2, _) = UID.compare x1 x2

  let pp ppf = function
    | x, None -> Format.fprintf ppf "#%d" (UID.get x)
    | x, Some n -> Format.fprintf ppf "%s#%d" n (UID.get x)
  ;;

  module Map = Map.Make (struct
      type nonrec t = t

      let compare = compare
    end)
end

module Expr = struct
  open Type

  (** e *)
  type expr =
    | EVar of Var.t (** x *)
    | EConst of Const.t (** c_b *)
    | ELam of Var.t * ttyp * expr (** λx:τ. e *)
    | EApp of expr * expr (** e e *)
    | ERecord of (string * expr) list
    [@printer Format.pp_print_record Format.pp_print_string pp_expr]
    (** { l: e, …, l: e } *)
    | EProj of expr * string (** e.l *)
    | ETyLam : ('k TVar.t[@printer TVar.pp]) * expr -> expr (** λα. e *)
    | ETyApp : expr * ('k Type.t[@printer Type.pp]) -> expr (** e τ *)
    | EPack :
        ('k Type.t[@printer Type.pp]) * expr * ('k TVar.t[@printer TVar.pp]) * ttyp
        -> expr (** pack ⟨τ, e⟩ as ∃α. τ *)
    | EUnpack : ('k TVar.t[@printer TVar.pp]) * Var.t * expr * expr -> expr
    (** unpack ⟨α, x⟩ = e in e *)
    (* Sugar *)
    | ELetIn of Var.t * expr * expr (** let x = e1 in e2 *)
    (* Non-standard *)
    | EExtern of string * ttyp
    | ECond of expr * expr * expr
  [@@deriving show]

  type t = expr

  let pp = pp_expr
end

module Value = struct
  (** v *)
  type value =
    | VConst of Const.t
    | VLam of (value -> value)
    | VRecord of (string * value) list
    [@printer Format.pp_print_record Format.pp_print_string pp_value]
    | VTyLam of (unit -> value)
    | VPack of value
  [@@deriving show]

  type t = value

  let rec equal x y =
    match x, y with
    | VLam _, _ | _, VLam _ -> invalid_arg "Value.equal"
    | VTyLam _, _ | _, VTyLam _ -> invalid_arg "Value.equal"
    | VConst x, VConst y -> Const.equal x y
    | VConst _, _ -> false
    | VRecord xs, VRecord ys ->
      List.equal (fun (x, xv) (y, yv) -> x = y && equal xv yv) xs ys
    | VRecord _, _ -> false
    | VPack x, VPack y -> equal x y
    | VPack _, _ -> false
  ;;

  let pp = pp_value
end

module Error = struct
  open Diagnostic.Error

  let undefined_extern_symbol id = error "undefined external symbol `%s'" id
  let undefined_variable x = error "undefined variable `%a'" Var.pp x
  let undefined_type_variable x = error "undefined type variable `%a'" TVar.pp x

  let expected_matching_kind k1 k2 =
    error "expected kind %a, but got %a" Kind.pp k1 Kind.pp k2
  ;;

  let expected_matching_type t1 t2 =
    let err = error "@[expected@;<1 2>@[%a@],@;<1 -2>but got@;<1 2>@[%a@]@;<1 -2>@]" in
    err Type.pp t1 Type.pp t2
  ;;

  let expected_type what t = error "expected %s, but got %a" what Type.pp t
  let expected_function_type = expected_type "a function type"
  let expected_record_type = expected_type "a record type"
  let expected_existential_type = expected_type "an existential type"
  let expected_universal_type = expected_type "a universal type"
  let expected_bool = expected_type "a boolean"

  let undefined_record_field ts l =
    error "undefined field `%s' in record %a" l Type.pp (TRecord ts)
  ;;

  let variable_escapes_scope a t =
    error "variable `%a' escapes its scope in type `%a'" TVar.pp a Type.pp t
  ;;
end

module Typecheck = struct
  open Type
  open Expr

  module Env : sig
    type t

    val empty : t
    val add_var : Var.t -> ttyp -> t -> t
    val add_typ : 'k TVar.t -> t -> 'k TVar.t * t
    val find_var : Var.t -> t -> ttyp option
    val find_typ : 'k TVar.t -> t -> 'k TVar.t option
  end = struct
    module Subst = TVar.Map.Make (TVar)

    type t =
      { subst : Subst.t
      ; vars : ttyp Var.Map.t
      }

    let empty = { subst = Subst.empty; vars = Var.Map.empty }
    let add_var x t env = { env with vars = Var.Map.add x t env.vars }

    let add_typ x env =
      let y = TVar.clone x in
      y, { env with subst = Subst.add x y env.subst }
    ;;

    let find_var x env = Var.Map.find_opt x env.vars
    let find_typ x env = Subst.find_opt x env.subst
  end

  let rec freshen : type k. _ -> k typ -> k typ =
    fun env -> function
    | TVar x ->
      (match Env.find_typ x env with
       | Some x -> TVar x
       | None -> Error.undefined_type_variable x)
    | TPrim p -> TPrim p
    | TRecord ts -> TRecord (List.map (fun (l, t) -> l, freshen env t) ts)
    | TApp (t1, t2) -> TApp (freshen env t1, freshen env t2)
    | TArrow (t1, t2) -> TArrow (freshen env t1, freshen env t2)
    | TForall (a, t) ->
      let a, env = Env.add_typ a env in
      TForall (a, freshen env t)
    | TExists (a, t) ->
      let a, env = Env.add_typ a env in
      TExists (a, freshen env t)
    | TLam (a, t) ->
      let a, env = Env.add_typ a env in
      TLam (a, freshen env t)
  ;;

  let rec infer env e =
    trace
      (fun m -> m ~header:"infer" "%a" Expr.pp e)
      (fun t m -> m ~header:"infer" ":: %a" Type.pp t)
    @@ fun _ ->
    match e with
    | EVar x ->
      (match Env.find_var x env with
       | Some t -> t
       | None -> Error.undefined_variable x)
    | EConst c -> TPrim (Const.typ c)
    | ELam (x, t, e) ->
      let t = freshen env t in
      let env = Env.add_var x t env in
      TArrow (t, infer env e)
    | EApp (e1, e2) ->
      (match infer env e1, infer env e2 with
       | TArrow (t1, t2), t1' when Equiv.equiv t1 t1' -> t2
       | TArrow (t1, _), t1' -> Error.expected_matching_type t1 t1'
       | t1, _ -> Error.expected_function_type t1)
    | ERecord es -> TRecord (List.map (fun (l, e) -> l, infer env e) es)
    | EProj (e, l) ->
      (match infer env e with
       | TRecord ts ->
         (match List.assoc_opt l ts with
          | Some t -> t
          | None -> Error.undefined_record_field ts l)
       | t -> Error.expected_record_type t)
    | ETyLam (a, e) ->
      let a, env = Env.add_typ a env in
      TForall (a, infer env e)
    | ETyApp (e, t) ->
      (match infer env e, freshen env t with
       | TForall (a, t1), t2 ->
         (match Kind.hequal (TVar.kind a) (kind t2) with
          | Some Equal -> Subst.subst_one a t2 t1
          | None -> Error.expected_matching_kind (TVar.kind a) (kind t2))
       | t1, _ -> Error.expected_universal_type t1)
    | EPack (t, e, a, s) ->
      let a, env' = Env.add_typ a env in
      (match freshen env t, infer env e, freshen env' s with
       | t, t', s when Equiv.equiv t' (Subst.subst_one a t s) -> TExists (a, s)
       | _, t', s -> Error.expected_matching_type t' (Subst.subst_one a t s))
    | EUnpack (a, x, e1, e2) ->
      (match infer env e1 with
       | TExists (a', s) ->
         (match Kind.hequal (TVar.kind a) (TVar.kind a') with
          | Some Equal ->
            let a, env = Env.add_typ a env in
            let env = Env.add_var x (Subst.subst_tvar a' a s) env in
            let t = infer env e2 in
            if Type.is_free a t then Error.variable_escapes_scope a t else t
          | None -> Error.expected_matching_kind (TVar.kind a) (TVar.kind a'))
       | t -> Error.expected_existential_type t)
    | ELetIn (x, e1, e2) ->
      let t1 = infer env e1 in
      infer (Env.add_var x t1 env) e2
    | EExtern (_, t) -> freshen env t
    | ECond (c, e1, e2) ->
      (match infer env c with
       | TPrim PBool ->
         (match infer env e1, infer env e2 with
          | t1, t2 when Equiv.equiv t1 t2 -> t1
          | t1, t2 -> Error.expected_matching_type t1 t2)
       | t -> Error.expected_bool t)
  ;;

  let check env e =
    trace
      (fun m ->
         let expr = Format.with_margin 140 Expr.pp in
         let expr = Format.with_max_boxes Int.max_int expr in
         m ~header:"check" "%a" expr e)
      (fun t m ->
         let typ = Format.with_margin 140 Type.pp in
         let typ = Format.with_max_boxes Int.max_int typ in
         m ~header:"check" "%a" typ t)
    @@ fun () -> infer env e
  ;;
end

module Eval = struct
  open Expr
  open Value

  module Env : sig
    type t

    val init : (string -> value option) -> t
    val add_var : Var.t -> value -> t -> t
    val find_var : Var.t -> t -> value
    val find_extern : string -> t -> value option
  end = struct
    type t = (string -> value option) * value Var.Map.t

    let init extern = extern, Var.Map.empty
    let add_var x v (ext, vars) = ext, Var.Map.add x v vars
    let find_var x (_, vars) = Var.Map.find x vars
    let find_extern x (extern, _) = extern x
  end

  let rec eval env e =
    trace
      (fun m -> m ~header:"eval" "%a" Expr.pp e)
      (fun v m -> m ~header:"eval" "= %a" Value.pp v)
    @@ fun _ ->
    match e with
    | EVar x -> Env.find_var x env
    | EConst c -> VConst c
    | ELam (x, _, e) -> VLam (fun v -> eval (Env.add_var x v env) e)
    | EApp (e1, e2) ->
      (match eval env e1, eval env e2 with
       | VLam f, v -> f v
       | _ -> assert false)
    | ERecord es ->
      let vs = List.map (fun (l, e) -> l, eval env e) es in
      VRecord vs
    | EProj (e, l) ->
      (match eval env e with
       | VRecord ts -> List.assoc l ts
       | _ -> assert false)
    | ETyLam (_, e) -> VTyLam (fun () -> eval env e)
    | ETyApp (e, _) ->
      (match eval env e with
       | VTyLam f -> f ()
       | _ -> assert false)
    | EPack (_, e, _, _) -> VPack (eval env e)
    | EUnpack (_, x, e1, e2) ->
      (match eval env e1 with
       | VPack v -> eval (Env.add_var x v env) e2
       | _ -> assert false)
    | ELetIn (x, e1, e2) ->
      let v1 = eval env e1 in
      eval (Env.add_var x v1 env) e2
    | EExtern (id, _) ->
      (match Env.find_extern id env with
       | Some v -> v
       | None -> Error.undefined_extern_symbol id)
    | ECond (c, e1, e2) ->
      (match eval env c with
       | VConst (CBool true) -> eval env e1
       | VConst (CBool false) -> eval env e2
       | _ -> assert false)
  ;;
end
