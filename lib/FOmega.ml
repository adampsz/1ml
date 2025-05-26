open Util

module Kind = struct
  include struct
    type ktyp = private unit
  end

  type _ t =
    | KType : ktyp t
    | KArrow : 'a t * 'b t -> ('a -> 'b) t

  let rec hequal : type k1 k2. k1 t -> k2 t -> (k1, k2) Type.eq option =
    fun k1 k2 ->
    match k1, k2 with
    | KType, KType -> Some Util.Equal
    | KArrow (k1a, k1b), KArrow (k2a, k2b) ->
      (match hequal k1a k2a, hequal k1b k2b with
       | Some Util.Equal, Some Util.Equal -> Some Util.Equal
       | _, _ -> None)
    | _, _ -> None
  ;;

  let equal (x : 'k t) (y : 'k t) : bool = x = y
end

module Type = struct
  module TVar : sig
    type 'k t

    val id : 'k t -> int
    val kind : 'k t -> 'k Kind.t
    val name : 'k t -> string option
    val fresh : ?name:string -> 'k Kind.t -> 'k t
    val clone : 'k t -> 'k t
    val equal : 'k t -> 'k t -> bool
    val compare : 'k t -> 'k t -> int
    val hequal : 'k1 t -> 'k2 t -> ('k1, 'k2) Util.eq option
    val hcompare : 'k1 t -> 'k2 t -> int

    module Map : Util.HMap.S with type 'k key = 'k t
  end = struct
    let counter = ref 0

    type 'k t = int * 'k Kind.t * string option

    let id (x, _, _) = x
    let kind (_, k, _) = k
    let name (_, _, n) = n
    let fresh ?name k = next counter, k, name
    let clone (_, k, n) = fresh ?name:n k
    let hequal (x1, k1, _) (x2, k2, _) = if x1 = x2 then Kind.hequal k1 k2 else None
    let hcompare (x1, _, _) (x2, _, _) = Int.compare x1 x2
    let equal x1 x2 = hequal x1 x2 <> None
    let compare = hcompare

    module Map = Util.HMap.Make (struct
        type nonrec 'k t = 'k t

        let hcompare = hcompare
      end)
  end

  type ktyp = Kind.ktyp
  type 'k tvar = 'k TVar.t

  (** τ *)
  type _ t =
    | TVar : 'k tvar -> 'k t (** α *)
    | TPrim : Prim.t -> ktyp t (** b *)
    | TArrow : ktyp t * ktyp t -> ktyp t (** τ → τ *)
    | TRecord : (string * ktyp t) list -> ktyp t (** { l: τ, …, l: τ } *)
    | TForall : 'k tvar * ktyp t -> ktyp t (** ∀κ. τ *)
    | TExists : 'k tvar * ktyp t -> ktyp t (** ∃κ. τ *)
    | TLam : 'k1 TVar.t * 'k2 t -> ('k1 -> 'k2) t (** λα:κ. τ *)
    | TApp : ('k1 -> 'k2) t * 'k1 t -> 'k2 t (** τ τ *)

  type ttyp = ktyp t

  let rec kind : type k. k t -> k Kind.t = function
    | TVar x -> TVar.kind x
    | TPrim _ -> KType
    | TArrow _ -> KType
    | TRecord _ -> KType
    | TForall _ -> KType
    | TExists _ -> KType
    | TLam (t1, t2) -> Kind.KArrow (TVar.kind t1, kind t2)
    | TApp (t1, _) ->
      let (Kind.KArrow (_, k2)) = kind t1 in
      k2
  ;;

  module Subst = struct
    module Sub = TVar.Map.Make (struct
        type nonrec 'k t = 'k t
      end)

    let add_var x sub =
      let y = TVar.clone x in
      y, Sub.add x (TVar y) sub
    ;;

    let rec subst : type k. Sub.t -> k t -> k t =
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
    type 'k typ = 'k t

    type _ neutral =
      | NVar : 'k TVar.t -> 'k neutral
      | NApp : 'k1 typ * ('k1 -> 'k2) neutral -> 'k2 neutral

    type _ t =
      | NNeutral : 'k neutral -> 'k t
      | NLam : 'k1 TVar.t * 'k2 typ -> ('k1 -> 'k2) t
      | NPrim : Prim.t -> ktyp t
      | NArrow : ttyp * ttyp -> ktyp t
      | NRecord : (string * ttyp) list -> ktyp t
      | NForall : 'k tvar * ttyp -> ktyp t
      | NExists : 'k tvar * ttyp -> ktyp t

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
      let rec aux : type k. k t -> k t -> bool =
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
           | Some Util.Equal -> aux t1 (Subst.subst_tvar x2 x1 t2)
           | None -> false)
        | NForall _, _ -> false
        | NExists (x1, t1), NExists (x2, t2) ->
          (match Kind.hequal (TVar.kind x1) (TVar.kind x2) with
           | Some Util.Equal -> aux t1 (Subst.subst_tvar x2 x1 t2)
           | None -> false)
        | NExists _, _ -> false
      and auxn : type k1 k2. k1 neutral -> k2 neutral -> (k1, k2) Util.eq option =
        fun n1 n2 ->
        match n1, n2 with
        | NVar x1, NVar x2 -> TVar.hequal x1 x2
        | NVar _, _ -> None
        | NApp (t1, n1), NApp (t2, n2) ->
          (match auxn n1 n2 with
           | Some Util.Equal -> if aux t1 t2 then Some Util.Equal else None
           | None -> None)
        | NApp _, _ -> None
      in
      aux t1 t2
    ;;
  end
end

module Expr = struct
  module Var : sig
    type t

    val fresh : ?name:string -> unit -> t
    val id : t -> int
    val clone : t -> t
    val name : t -> string option
    val equal : t -> t -> bool
    val compare : t -> t -> int

    module Map : Map.S with type key = t
  end = struct
    type t = int * string option

    let counter = ref 0
    let fresh ?name () = next counter, name
    let id (x, _) = x
    let clone (_, n) = fresh ?name:n ()
    let name (_, n) = n
    let equal (x1, _) (x2, _) = Int.equal x1 x2
    let compare (x1, _) (x2, _) = Int.compare x1 x2

    module Map = Map.Make (struct
        type nonrec t = t

        let compare = compare
      end)
  end

  type var = Var.t
  type 'k typ = 'k Type.t
  type 'k tvar = 'k Type.TVar.t
  type ttyp = Type.ktyp typ

  (** e *)
  type t =
    | EVar of Var.t (** x *)
    | EPrim of Prim.const (** c_b *)
    | ELam of var * ttyp * t (** λx:τ. e *)
    | EApp of t * t (** e e *)
    | ERecord of (string * t) list (** { l: e, …, l: e } *)
    | EProj of t * string (** e.l *)
    | ETyLam : 'k tvar * t -> t (** λα:κ. e *)
    | ETyApp : t * 'k typ -> t (** e τ *)
    | EPack : 'k typ * t * ttyp -> t (** pack ⟨τ, e⟩ as τ *)
    | EUnpack : 'k tvar * var * t * t -> t (** unpack ⟨α, x⟩ = e in e *)
    (* Extensions *)
    | EExternal of string * ttyp
    | ECond of t * t * t
end

module Value = struct
  (** v *)
  type t =
    | VPrim of Prim.const
    | VLam of (t -> t)
    | VExternal of (t -> t)
    | VRecord of (string * t) list
    | VTyLam of (unit -> t)
    | VPack of t
end

module PP = struct
  open Format
  open Kind
  open Type
  open Expr
  open Value

  let pp_wrap ppf w fmt =
    match w with
    | false -> fprintf ppf fmt
    | true -> kfprintf (fun f -> kfprintf (dprintf ")") f fmt) ppf "("
  ;;

  let pp_kind ppf =
    let rec aux : type k. _ -> _ -> k Kind.t -> _ =
      fun w ppf -> function
        | KType -> fprintf ppf "∗"
        | KArrow (k1, k2) -> pp_wrap ppf w "%a →  %a" (aux true) k1 (aux false) k2
    in
    aux false ppf
  ;;

  let pp_tvar (type k) ppf (x : k TVar.t) =
    match TVar.name x with
    | Some n -> pp_print_string ppf n
    | None -> fprintf ppf "%%%d" (TVar.id x)
  ;;

  let pp_tvar_param (type k) ppf (x : k TVar.t) =
    match Kind.hequal (TVar.kind x) KType with
    | Some Util.Equal -> pp_tvar ppf x
    | None -> fprintf ppf "%a: %a" pp_tvar x pp_kind (TVar.kind x)
  ;;

  let pp_typ ppf =
    let rec aux : type k. _ -> _ -> k Type.t -> _ =
      fun prec ppf -> function
        | TVar x -> pp_tvar ppf x
        | TPrim PrimUnit -> pp_print_string ppf "unit"
        | TPrim PrimBool -> pp_print_string ppf "bool"
        | TPrim PrimInt -> pp_print_string ppf "int"
        | TPrim PrimFloat -> pp_print_string ppf "float"
        | TPrim PrimString -> pp_print_string ppf "string"
        | TRecord ts ->
          let pp_field fmt (l, t) = fprintf fmt "%s: %a" l (aux 0) t
          and pp_sep fmt _ = pp_print_string fmt ", " in
          fprintf ppf "{ %a }" (pp_print_list ~pp_sep pp_field) ts
        | TApp (t1, t2) -> pp_wrap ppf (prec > 1) "%a %a" (aux 1) t1 (aux 2) t2
        | TArrow (t1, t2) -> pp_wrap ppf (prec > 0) "%a →  %a" (aux 1) t1 (aux 0) t2
        | TForall (a, t) -> pp_wrap ppf (prec > 0) "∀ %a. %a" pp_tvar_param a (aux 0) t
        | TExists (a, t) -> pp_wrap ppf (prec > 0) "∃ %a. %a" pp_tvar_param a (aux 0) t
        | TLam (a, t) -> pp_wrap ppf (prec > 0) "λ %a. %a" pp_tvar_param a (aux 0) t
    in
    aux 0 ppf
  ;;

  let pp_var ppf x =
    match Var.name x with
    | Some n -> pp_print_string ppf n
    | None -> fprintf ppf "%%%d" (Var.id x)
  ;;

  let pp_expr ppf =
    let rec aux prec ppf = function
      | EVar x -> pp_var ppf x
      | EPrim (ConstUnit _) -> pp_print_string ppf "()"
      | EPrim (ConstBool x) -> pp_print_bool ppf x
      | EPrim (ConstInt x) -> pp_print_int ppf x
      | EPrim (ConstFloat x) -> pp_print_float ppf x
      | EPrim (ConstString x) -> fprintf ppf "%S" x
      | ELam (x, t, e) ->
        pp_wrap ppf (prec > 0) "λ %a: %a. %a" pp_var x pp_typ t (aux 0) e
      | EApp (e1, e2) -> pp_wrap ppf (prec > 1) "%a %a" (aux 1) e1 (aux 2) e2
      | ERecord es ->
        let pp_field fmt (l, t) = fprintf fmt "%s = %a" l (aux 0) t
        and pp_sep fmt _ = pp_print_string fmt ", " in
        fprintf ppf "{ %a }" (pp_print_list ~pp_sep pp_field) es
      | EProj (e, l) -> fprintf ppf "%a.%s" (aux 2) e l
      | ETyLam (a, e) -> pp_wrap ppf (prec > 0) "λ %a. %a" pp_tvar_param a (aux 0) e
      | ETyApp (e, t) -> pp_wrap ppf (prec > 1) "%a [%a]" (aux 1) e pp_typ t
      | EPack (t, e, s) ->
        pp_wrap ppf (prec > 0) "pack ⟨%a, %a⟩ as %a" pp_typ t (aux 0) e pp_typ s
      | EUnpack (a, x, e1, e2) ->
        let pp = pp_wrap ppf (prec > 0) "unpack ⟨%a, %a⟩ = %a in %a" in
        pp pp_tvar_param a pp_var x (aux 0) e1 (aux 0) e2
      | EExternal (n, t) -> fprintf ppf "external %s: %a" n pp_typ t
      | ECond (c, e1, e2) ->
        pp_wrap ppf (prec > 0) "if %a then %a else %a" (aux 0) c (aux 0) e1 (aux 0) e2
    in
    aux 0 ppf
  ;;

  let rec pp_value ppf = function
    | VPrim (ConstUnit _) -> fprintf ppf "()"
    | VPrim (ConstBool x) -> fprintf ppf "%b" x
    | VPrim (ConstInt x) -> fprintf ppf "%d" x
    | VPrim (ConstFloat x) -> fprintf ppf "%f" x
    | VPrim (ConstString x) -> fprintf ppf "%S" x
    | VLam _ | VTyLam _ | VExternal _ -> pp_print_string ppf "<fun>"
    | VRecord vs ->
      let pp_field fmt (l, v) = fprintf fmt "%s: %a" l pp_value v
      and pp_sep fmt _ = pp_print_string fmt ", " in
      fprintf ppf "pp { %a }" (pp_print_list ~pp_sep pp_field) vs
    | VPack v -> fprintf ppf "pack %a" pp_value v
  ;;
end

module Error = struct
  exception Error of string

  let err fmt = Format.kasprintf (fun msg -> raise (Error msg)) fmt
  let undefined_external_symbol id = err "undefined external symbol `%s'" id
  let undefined_variable x = err "undefined variable `%a'" PP.pp_var x

  let expected_matching_kind k1 k2 =
    err "expected kind %a, but got %a" PP.pp_kind k1 PP.pp_kind k2
  ;;

  let expected_matching_type t1 t2 =
    err "expected %a, but got %a" PP.pp_typ t1 PP.pp_typ t2
  ;;

  let expected_type what t = err "expected %s, but got %a" what PP.pp_typ t
  let expected_function_type = expected_type "a function type"
  let expected_record_type = expected_type "a record type"
  let expected_existential_type = expected_type "an existential type"
  let expected_universal_type = expected_type "a universal type"
  let expected_bool = expected_type "a boolean"

  let undefined_record_field ts l =
    err "undefined field `%s' in record %a" l PP.pp_typ (Type.TRecord ts)
  ;;
end

module Typecheck = struct
  open Type
  open Expr

  module Env : sig
    type t

    val empty : t
    val add_var : var -> ttyp -> t -> t
    val add_typ : 'k tvar -> t -> 'k tvar * t
    val find_var : Var.t -> t -> ttyp option
    val find_typ : 'k tvar -> t -> 'k tvar option
  end = struct
    module Subst = TVar.Map.Make (struct
        type 'k t = 'k TVar.t
      end)

    type t =
      { subst : Subst.t
      ; vars : ttyp Var.Map.t
      }

    let empty = { subst = Subst.empty; vars = Var.Map.empty }
    let add_var x t env = { env with vars = Var.Map.add x t env.vars }

    let add_typ x env =
      let y = Type.TVar.clone x in
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
       | None -> assert false)
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

  let rec infer env = function
    | EVar x ->
      (match Env.find_var x env with
       | Some t -> t
       | None -> Error.undefined_variable x)
    | EPrim (ConstUnit _) -> TPrim PrimUnit
    | EPrim (ConstBool _) -> TPrim PrimBool
    | EPrim (ConstInt _) -> TPrim PrimInt
    | EPrim (ConstFloat _) -> TPrim PrimFloat
    | EPrim (ConstString _) -> TPrim PrimString
    | ELam (x, t, e) ->
      let t = freshen env t in
      let env = Env.add_var x t env in
      TArrow (t, infer env e)
    | EApp (e1, e2) ->
      (match infer env e1, infer env e2 with
       | TArrow (t1, t2), t1' when Type.Equiv.equiv t1 t1' -> t2
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
          | Some Util.Equal -> Type.Subst.subst_one a t2 t1
          | None -> Error.expected_matching_kind (TVar.kind a) (kind t2))
       | t1, _ -> Error.expected_universal_type t1)
    | EPack (t, e, s) ->
      (match freshen env t, infer env e, freshen env s with
       | t, t', TExists (a, s) ->
         (match Kind.hequal (TVar.kind a) (kind t) with
          | Some Util.Equal when Type.Equiv.equiv t' (Subst.subst_one a t t') ->
            TExists (a, s)
          | Some Util.Equal -> Error.expected_matching_type t' s
          | None -> Error.expected_matching_kind (TVar.kind a) (kind t'))
       | _, _, s -> Error.expected_existential_type s)
    | EUnpack (a, x, e1, e2) ->
      (match infer env e1 with
       | TExists (a', s) ->
         (match Kind.hequal (TVar.kind a) (TVar.kind a') with
          | Some Util.Equal ->
            let a, env = Env.add_typ a env in
            let env = Env.add_var x (Subst.subst_tvar a' a s) env in
            infer env e2
          | None -> Error.expected_matching_kind (TVar.kind a) (TVar.kind a'))
       | t -> Error.expected_existential_type t)
    | EExternal (_, t) -> freshen env t
    | ECond (c, e1, e2) ->
      (match infer env c with
       | TPrim PrimBool ->
         (match infer env e1, infer env e2 with
          | t1, t2 when Type.Equiv.equiv t1 t2 -> t1
          | t1, t2 -> Error.expected_matching_type t1 t2)
       | t -> Error.expected_bool t)
  ;;
end

module Eval = struct
  open Expr
  open Value

  module Env : sig
    type t

    val init : (string -> Value.t option) -> t
    val add_var : var -> Value.t -> t -> t
    val find_var : Var.t -> t -> Value.t
    val find_external : string -> t -> Value.t option
  end = struct
    type t =
      { ext : string -> Value.t option
      ; vars : Value.t Var.Map.t
      }

    let init ext = { ext; vars = Var.Map.empty }
    let add_var x v env = { env with vars = Var.Map.add x v env.vars }
    let find_var x env = Var.Map.find x env.vars
    let find_external x env = env.ext x
  end

  let rec eval env = function
    | EVar x -> Env.find_var x env
    | EPrim p -> VPrim p
    | ELam (x, _, e) -> VLam (fun v -> eval (Env.add_var x v env) e)
    | EApp (e1, e2) ->
      (match eval env e1, eval env e2 with
       | (VLam f | VExternal f), v -> f v
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
       | VExternal f -> VExternal f
       | v ->
         Format.asprintf "not callable: %a = %a\n%!" PP.pp_expr e PP.pp_value v
         |> failwith)
    | EPack (_, e, _) -> VPack (eval env e)
    | EUnpack (_, x, e1, e2) ->
      (match eval env e1 with
       | VPack v -> eval (Env.add_var x v env) e2
       | _ -> assert false)
    | EExternal (id, _) ->
      (match Env.find_external id env with
       | Some v -> v
       | None -> Error.undefined_external_symbol id)
    | ECond (c, e1, e2) ->
      (match eval env c with
       | VPrim (ConstBool true) -> eval env e1
       | VPrim (ConstBool false) -> eval env e2
       | _ -> assert false)
  ;;
end
