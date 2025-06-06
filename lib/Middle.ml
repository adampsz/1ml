open Util

let trace = Tracing.init ~width:9 "middle"

module Kind = struct
  include struct
    type ktyp = private unit
  end

  type _ kind =
    | KType : ktyp kind
    | KArrow : 'k1 kind * 'k2 kind -> ('k1 -> 'k2) kind

  type 'k t = 'k kind

  let rec hequal : type k1 k2. k1 kind -> k2 kind -> (k1, k2) eq option =
    fun k1 k2 ->
    match k1, k2 with
    | KType, KType -> Some Equal
    | KArrow (k1a, k1b), KArrow (k2a, k2b) ->
      (match hequal k1a k2a, hequal k1b k2b with
       | Some Equal, Some Equal -> Some Equal
       | _, _ -> None)
    | _, _ -> None
  ;;

  let equal (x : 'k kind) (y : 'k kind) : bool = x = y
end

module Effect = struct
  type eff =
    | Pure
    | Impure

  type t = eff

  let join eff1 eff2 =
    match eff1, eff2 with
    | Pure, Pure -> Pure
    | Impure, _ | _, Impure -> Impure
  ;;

  let sub eff1 eff2 =
    match eff1, eff2 with
    | Impure, Pure -> false
    | _, _ -> true
  ;;
end

module Field = struct
  type field =
    | FNamed of string
    | FSynthetic of int

  type t = field
end

module Type = struct
  open Kind
  open Effect

  module TVar : sig
    type 'k t
    type ex = Ex : 'k t -> ex

    val id : 'k t -> int
    val kind : 'k t -> 'k kind
    val name : 'k t -> string option
    val fresh : ?name:string -> 'k kind -> 'k t
    val clone : 'k t -> 'k t
    val rekind : 'k kind -> _ t -> 'k t
    val equal : 'k t -> 'k t -> bool
    val compare : 'k t -> 'k t -> int
    val hequal : 'k1 t -> 'k2 t -> ('k1, 'k2) eq option
    val hcompare : 'k1 t -> 'k2 t -> int

    module Set : HSet.S with type 'k elt = 'k t
    module Map : HMap.S with type 'k key = 'k t
  end = struct
    type 'k t = int * 'k kind * string option
    type ex = Ex : 'k t -> ex

    let uid = ref 0
    let id (x, _, _) = x
    let kind (_, kind, _) = kind
    let name (_, _, name) = name
    let fresh ?name kind = next uid, kind, name
    let clone (_, k, name) = fresh ?name k
    let rekind k (_, _, name) = fresh ?name k
    let hequal (x1, k1, _) (x2, k2, _) = if x1 = x2 then Kind.hequal k1 k2 else None
    let hcompare (x1, _, _) (x2, _, _) = Int.compare x1 x2
    let equal (x1, _, _) (x2, _, _) = Int.equal x1 x2
    let compare = hcompare

    module Set = HSet.Make (struct
        type nonrec 'k t = 'k t

        let hcompare = hcompare
      end)

    module Map = HMap.Make (struct
        type nonrec 'k t = 'k t

        let hcompare = hcompare
      end)
  end

  module Path = struct
    open Kind

    type _ path =
      | TVar : 'k TVar.t -> 'k path
      | TApp : ('k1 -> 'k2) path * 'k1 TVar.t -> 'k2 path

    type 'k t = 'k path
    type ex = Ex : 'k path -> ex

    let rec kind : type k. k path -> k kind = function
      | TVar x -> TVar.kind x
      | TApp (p, _) ->
        let (KArrow (_, k)) = kind p in
        k
    ;;

    let rec hequal : type k1 k2. k1 path -> k2 path -> (k1, k2) eq option =
      fun p1 p2 ->
      match p1, p2 with
      | TVar x1, TVar x2 -> TVar.hequal x1 x2
      | TApp (p1a, x1), TApp (p2a, x2) ->
        (match hequal p1a p2a with
         | Some Equal when TVar.equal x1 x2 -> Some Equal
         | _ -> None)
      | _, _ -> None
    ;;

    let equal (p1 : 'k path) (p2 : 'k path) = hequal p1 p2 <> None
    let hcompare p1 p2 = compare (Ex p1) (Ex p2)
    let compare (p1 : 'k path) (p2 : 'k path) = hcompare p1 p2

    module Set = HSet.Make (struct
        type nonrec 'k t = 'k path

        let hcompare = hcompare
      end)
  end

  type 'k path = 'k Path.t

  type _ typ =
    | TNeu : 'k neutral -> 'k typ
    | TLam : 'k1 TVar.t * 'k2 typ -> ('k1 -> 'k2) typ
    | TPrim : Prim.t -> ktyp typ
    | TRecord : (Field.t * ktyp typ) list -> ktyp typ
    | TSingleton : qtyp -> ktyp typ
    | TEffArrow : TVar.ex list * ktyp typ * eff * qtyp -> ktyp typ

  and qtyp = TExists of TVar.ex list * ktyp typ

  and _ neutral =
    | TVar : 'k TVar.t -> 'k neutral
    | TApp : ('k1 -> 'k2) neutral * 'k1 typ -> 'k2 neutral

  type 'k t = 'k typ
  type ttyp = ktyp typ
  type ex = Ex : 'k typ -> ex

  let as_path t =
    let rec aux : type k. k neutral -> k path option = function
      | TVar x -> Some (TVar x)
      | TApp (n, TNeu (TVar x)) ->
        (match aux n with
         | Some p -> Some (TApp (p, x))
         | None -> None)
      | TApp (_, _) -> None
    in
    match t with
    | TNeu n -> aux n
    | TPrim _ | TRecord _ | TSingleton _ | TEffArrow _ -> None
  ;;

  module Subst : sig
    type sub

    val empty : sub
    val cardinal : sub -> int
    val merge_disjoint : sub -> sub -> sub
    val add : 'k TVar.t -> 'k typ -> sub -> sub
    val find : 'k TVar.t -> sub -> 'k typ
    val find_opt : 'k TVar.t -> sub -> 'k typ option
    val add_fresh_tvars : TVar.ex list -> sub -> TVar.ex list * sub
    val subst : sub -> 'k typ -> 'k typ
    val qsubst : sub -> qtyp -> qtyp
  end = struct
    module TVSub = TVar.Map.Make (struct
        type 'k t = 'k typ
      end)

    type sub = TVSub.t

    let empty = TVSub.empty
    let cardinal = TVSub.cardinal
    let merge_disjoint = TVSub.merge_disjoint
    let add = TVSub.add
    let find = TVSub.find
    let find_opt = TVSub.find_opt

    let add_fresh_tvars ats sub =
      let aux sub (TVar.Ex x) =
        let y = TVar.clone x in
        TVSub.add x (TNeu (TVar y)) sub, TVar.Ex y
      in
      let sub, ats = List.fold_left_map aux sub ats in
      ats, sub
    ;;

    let rec subst : type k. _ -> k typ -> k typ =
      fun sub -> function
      | TNeu n -> subst_neutral sub n
      | TLam (x, t) ->
        let y = TVar.clone x in
        TLam (y, subst (TVSub.add x (TNeu (TVar y)) sub) t)
      | TPrim p -> TPrim p
      | TRecord fields -> TRecord (List.map (fun (l, t) -> l, subst sub t) fields)
      | TSingleton t -> TSingleton (qsubst sub t)
      | TEffArrow (ats, t1, eff, t2) ->
        let ats, sub = add_fresh_tvars ats sub in
        TEffArrow (ats, subst sub t1, eff, qsubst sub t2)

    and qsubst sub = function
      | TExists (ats, t) ->
        let xs, sub = add_fresh_tvars ats sub in
        TExists (xs, subst sub t)

    and subst_neutral : type k. _ -> k neutral -> k typ =
      fun sub -> function
      | TVar x ->
        (match TVSub.find_opt x sub with
         | Some t -> t
         | None -> TNeu (TVar x))
      | TApp (n, t) ->
        (match subst_neutral sub n with
         | TNeu n -> TNeu (TApp (n, subst sub t))
         | TLam (x, t') ->
           let sub = add x (subst sub t) sub in
           subst sub t')
    ;;
  end

  let free t =
    let rec aux : type k. k typ -> _ = function
      | TNeu n -> aux_neutral n
      | TLam (x, t) -> TVar.Set.add x (aux t)
      | TPrim _ -> TVar.Set.empty
      | TRecord fields ->
        let f acc (_, t) = TVar.Set.union acc (aux t) in
        List.fold_left f TVar.Set.empty fields
      | TSingleton (TExists (ats, t)) ->
        let f acc (TVar.Ex x) = TVar.Set.remove x acc in
        List.fold_left f (aux t) ats
      | TEffArrow (ats1, t1, _, TExists (ats2, t2)) ->
        let f acc (TVar.Ex x) = TVar.Set.remove x acc in
        let acc = List.fold_left f (aux t2) ats1 in
        List.fold_left f (TVar.Set.union acc (aux t1)) ats2
    and aux_neutral : type k. k neutral -> _ = function
      | TVar x -> TVar.Set.singleton x
      | TApp (n, t) -> TVar.Set.union (aux_neutral n) (aux t)
    in
    aux t
  ;;

  let rec is_small : type k. k typ -> _ = function
    | TNeu n -> is_small_nautral n
    | TLam (_, t) -> is_small t
    | TPrim _ -> true
    | TRecord fields -> List.for_all (fun (_, t) -> is_small t) fields
    | TSingleton (TExists ([], t)) -> is_small t
    | TSingleton (TExists (_, _)) -> false
    | TEffArrow ([], t1, eff, TExists ([], t2)) ->
      is_small t1 && eff = Impure && is_small t2
    | TEffArrow (_, _, _, TExists (_, _)) -> false

  and is_small_nautral : type k. k neutral -> _ = function
    | TVar _ -> true
    | TApp (n, t) -> is_small_nautral n && is_small t
  ;;
end

module Expr = struct
  open Effect
  open Field
  open Type

  module Var : sig
    type t

    val fresh : ?name:string -> unit -> t
    val clone : t -> t
    val id : t -> int
    val name : t -> string option
    val equal : t -> t -> bool
    val compare : t -> t -> int

    module Map : Map.S with type key = t
  end = struct
    type t = int * string option

    let uid = ref 0
    let fresh ?name () = next uid, name
    let clone (_, name) = fresh ?name ()
    let id (x, _) = x
    let name (_, name) = name
    let equal (x1, _) (x2, _) = Int.equal x1 x2
    let compare (x1, _) (x2, _) = Int.compare x1 x2

    module Map = Map.Make (struct
        type nonrec t = t

        let compare = compare
      end)
  end

  type packtyp = TPack : 'k TVar.t * 'k typ -> packtyp

  type expr =
    | EVar of Var.t
    | EConst of Prim.const
    | EExternal of (string * ttyp)
    | ERecord of (field * expr) list
    | EProj of expr * field
    | EPack of expr * packtyp list * ttyp
    | EUnpack of TVar.ex list * Var.t * qtyp * expr * expr
    | ECond of expr * expr * expr
    | ELet of Var.t * qtyp * expr * expr
    | ESingleton of qtyp
    | EEffLam of TVar.ex list * Var.t * ttyp * eff * expr
    | EEffApp of expr * ex list * expr * eff

  type t = expr
end

module PP = struct
  open Field
  open Kind
  open Type
  open Expr
  open Format
  open Effect
  open Util.PP

  let pp_label ppf = function
    | FNamed name -> pp_print_string ppf name
    | FSynthetic id -> fprintf ppf "_#%d" id
  ;;

  let pp_kind ppf =
    let rec aux : type k. _ -> _ -> k kind -> _ =
      fun p ppf -> function
        (* Precedence ∞ *)
        | KType -> fprintf ppf "∗"
        (* Precedence 0 *)
        | KArrow (k1, k2) -> wrap (p > 0) ppf "%a →  %a" (aux 1) k1 (aux 0) k2
    in
    aux 0 ppf
  ;;

  let pp_tvar ppf x =
    match TVar.name x with
    | Some n -> fprintf ppf "%s#%d" n (TVar.id x)
    | None -> fprintf ppf "_#%d" (TVar.id x)
  ;;

  let pp_tvar_param (type k) ppf (x : k TVar.t) =
    match Kind.hequal (TVar.kind x) KType with
    | Some Equal -> pp_tvar ppf x
    | None -> fprintf ppf "%a: %a" pp_tvar x pp_kind (TVar.kind x)
  ;;

  let pp_path ppf p =
    let rec aux : type k. _ -> k path -> _ =
      fun ppf -> function
        | TVar x -> pp_tvar ppf x
        | TApp (p, x) -> fprintf ppf "%a %a" aux p pp_tvar x
    in
    aux ppf p
  ;;

  let pp_eff ppf = function
    | Pure -> pp_print_string ppf "ₚ"
    | Impure -> pp_print_string ppf "ᵢ"
  ;;

  let rec pp_typ : type k. ?p:_ -> _ -> k typ -> _ =
    fun ?(p = 0) ppf -> function
    (* Precedence ∞ *)
    | TPrim p -> Prim.PP.pp_prim ppf p
    | TRecord fields ->
      let pp_field ppf (l, t) = fprintf ppf "%a: %a" pp_label l (pp_typ ~p:0) t
      and pp_sep ppf () = fprintf ppf "; " in
      fprintf ppf "{ %a }" (pp_print_list ~pp_sep pp_field) fields
    | TSingleton t -> fprintf ppf "(= %a)" (pp_qtyp ~p:0) t
    (* Precedence 0 *)
    | TEffArrow ([], t1, eff, t2) ->
      let pp = wrap (p > 0) ppf "%a →%a %a" in
      pp (pp_typ ~p:1) t1 pp_eff eff pp_qtyp t2
    | TEffArrow (ats, t1, eff, t2) ->
      let pp_sep ppf () = pp_print_string ppf ", "
      and pp_tvar ppf (TVar.Ex x) = pp_tvar_param ppf x in
      let pp = wrap (p > 0) ppf "∀ %a. %a →%a %a" in
      pp (pp_print_list ~pp_sep pp_tvar) ats (pp_typ ~p:1) t1 pp_eff eff pp_qtyp t2
    | TLam (x, t) -> wrap (p > 0) ppf "λ %a. %a" pp_tvar_param x (pp_typ ~p:0) t
    (* Other *)
    | TNeu n -> pp_neutral ~p:0 ppf n

  and pp_qtyp ?(p = 0) ppf = function
    | TExists ([], t) -> pp_typ ~p ppf t
    | TExists (ats, t) ->
      let pp_sep ppf () = pp_print_string ppf ", "
      and pp_tvar ppf (TVar.Ex x) = pp_tvar_param ppf x in
      wrap (p > 0) ppf "∃ %a. %a" (pp_print_list ~pp_sep pp_tvar) ats (pp_typ ~p:0) t

  and pp_neutral : type k. ?p:_ -> _ -> k neutral -> _ =
    fun ?(p = 0) ppf -> function
    (* Precedence ∞ *)
    | TVar x -> pp_tvar ppf x
    (* Precedence 1 *)
    | TApp (n, t) -> wrap (p > 1) ppf "%a %a" (pp_neutral ~p:1) n (pp_typ ~p:2) t
  ;;

  let pp_var ppf x =
    match Expr.Var.name x with
    | Some n -> fprintf ppf "%s#%d" n (Expr.Var.id x)
    | None -> fprintf ppf "_#%d" (Expr.Var.id x)
  ;;

  let rec pp_expr ?(p = 0) ppf = function
    (* Precedence ∞ *)
    | EVar x -> pp_var ppf x
    | EConst c -> Prim.PP.pp_const ppf c
    | EExternal (name, t) -> fprintf ppf "(external %s: %a)" name (pp_typ ~p:0) t
    | ESingleton qtyp -> fprintf ppf "[= %a]" (pp_qtyp ~p:0) qtyp
    | ERecord fields ->
      let pp_field ppf (l, e) = fprintf ppf "%a = %a" pp_label l (pp_expr ~p:0) e
      and pp_sep ppf _ = fprintf ppf ", " in
      fprintf ppf "{ %a }" (pp_print_list ~pp_sep pp_field) fields
    | EEffApp (e1, ts, e2, eff) ->
      let pp_sep ppf () = fprintf ppf " "
      and pp_typ ppf (Ex t) = fprintf ppf "[%a]" (pp_typ ~p:0) t in
      let pp = fprintf ppf "(%a %a %a)%a" in
      pp (pp_expr ~p:1) e1 (pp_print_list ~pp_sep pp_typ) ts (pp_expr ~p:2) e2 pp_eff eff
    (* Precedence 2 *)
    | EProj (e, l) -> wrap (p > 2) ppf "%a.%a" (pp_expr ~p:2) e pp_label l
    (* Precedence 0 *)
    | EPack (e, [], t) ->
      let pp = wrap (p > 0) ppf "pack ⟨%a⟩ as %a" in
      pp pp_expr e pp_typ t
    | EPack (e, ps, t) ->
      let pp_tvar ppf (TPack (a, _)) = pp_tvar_param ppf a
      and pp_ptyp ppf (TPack (_, t)) = pp_typ ppf t
      and pp_sep ppf () = fprintf ppf ", " in
      let pp = wrap (p > 0) ppf "pack ⟨%a, %a⟩ as ∃ %a. %a" in
      let pp = pp (pp_print_list ~pp_sep pp_ptyp) ps pp_expr e in
      pp (pp_print_list ~pp_sep pp_tvar) ps pp_typ t
    | EUnpack ([], id, t, e1, e2) ->
      let pp = wrap (p > 0) ppf "unpack ⟨%a: %a⟩ = %a in %a" in
      pp pp_var id pp_qtyp t pp_expr e1 pp_expr e2
    | EUnpack (ats, id, t, e1, e2) ->
      let pp_sep ppf () = fprintf ppf ", "
      and pp_tvar ppf (TVar.Ex x) = pp_tvar_param ppf x in
      let pp = wrap (p > 0) ppf "unpack ⟨%a, %a: %a⟩ = %a in %a" in
      pp (pp_print_list ~pp_sep pp_tvar) ats pp_var id pp_qtyp t pp_expr e1 pp_expr e2
    | ECond (e1, e2, e3) ->
      let pp = wrap (p > 0) ppf in
      pp "if %a then %a else %a" (pp_expr ~p:1) e1 (pp_expr ~p:1) e2 (pp_expr ~p:1) e3
    | ELet (id, qtyp, e1, e2) ->
      let pp = wrap (p > 0) ppf "let %a: %a = %a in %a" in
      pp pp_var id pp_qtyp qtyp pp_expr e1 pp_expr e2
    | EEffLam (uats, id, t, eff, e) ->
      let pp_sep ppf () = pp_print_string ppf ", "
      and pp_tuvar ppf (TVar.Ex x) = pp_tvar_param ppf x in
      let pp = wrap (p > 0) ppf "λ%a %a, %a: %a. %a" in
      let pp = pp pp_eff eff (pp_print_list ~pp_sep pp_tuvar) uats pp_var id pp_typ t in
      pp pp_expr e
  ;;

  let pp_typ t = pp_typ ~p:0 t
  let pp_qtyp t = pp_qtyp ~p:0 t
  let pp_neutral t = pp_neutral ~p:0 t
  let pp_expr t = pp_expr ~p:0 t
end

module Error = struct
  open Diagnostic.Error

  let bug = bug
end

module Translate = struct
  module S = struct
    module Kind = Kind
    module Field = Field
    module Effect = Effect
    module Type = Type
    module Expr = Expr
    include Kind
    include Field
    include Effect
    include Type
    include Expr
  end

  module T = struct
    include FOmega
    include FOmega.Kind
    include FOmega.Type
    include FOmega.Expr
  end

  type tr_tvar = Ex : 'k T.kind * 'k T.TVar.t -> tr_tvar
  type tr_typ = Ex : 'k T.kind * 'k T.typ -> tr_typ

  let rec kind : type k. k S.kind -> T.Kind.ex = function
    | S.KType -> Ex KType
    | S.KArrow (k1, k2) ->
      let Ex k1, Ex k2 = kind k1, kind k2 in
      Ex (KArrow (k1, k2))
  ;;

  module Env : sig
    type t

    val empty : t
    val add_tvar : 'k S.TVar.t -> t -> tr_tvar * t
    val add_var : S.Var.t -> t -> T.Var.t * t
    val find_tvar : 'k S.TVar.t -> t -> tr_tvar
    val find_var : S.Var.t -> t -> T.Var.t
  end = struct
    type t =
      { tvars : tr_tvar S.TVar.Map.t
      ; vars : T.var S.Var.Map.t
      }

    let empty = { tvars = S.TVar.Map.empty; vars = S.Var.Map.empty }

    let add_tvar x env =
      let (Ex k) = kind (S.TVar.kind x) in
      let y : tr_tvar = Ex (k, T.TVar.fresh ?name:(S.TVar.name x) k) in
      y, { env with tvars = S.TVar.Map.add x y env.tvars }
    ;;

    let add_var x env =
      let y = T.Var.fresh ?name:(S.Var.name x) () in
      y, { env with vars = S.Var.Map.add x y env.vars }
    ;;

    let find_tvar x env =
      match S.TVar.Map.find_opt x env.tvars with
      | Some x -> x
      | None -> Error.bug "unbound type variable `%a'" PP.pp_tvar x
    ;;

    let find_var x env =
      match S.Var.Map.find_opt x env.vars with
      | Some x -> x
      | None -> Error.bug "unbound variable `%a'" PP.pp_var x
    ;;
  end

  let field_effect = function
    | S.Pure -> "%p"
    | S.Impure -> "%i"
  ;;

  let field_singleton = function
    | () -> "%t"
  ;;

  let field = function
    | S.FNamed l -> l
    | S.FSynthetic id -> Printf.sprintf "%%%d" id
  ;;

  let rec neutral : type k. _ -> k S.neutral -> tr_typ =
    fun env -> function
    | S.TVar x ->
      let (Ex (k, x)) = Env.find_tvar x env in
      Ex (k, T.TVar x)
    | S.TApp (n, t) ->
      (match neutral env n, typ env t with
       | Ex (KArrow (k1, k2), n), Ex (k1', t) ->
         (match T.Kind.hequal k1 k1' with
          | Some Equal -> Ex (k2, T.TApp (n, t))
          | None -> assert false)
       | _, _ -> assert false)

  and typ : type k. _ -> k S.typ -> tr_typ =
    fun env -> function
    | S.TNeu n -> neutral env n
    | S.TLam (x, t) ->
      let Ex (k1, x), env = Env.add_tvar x env in
      let (Ex (k2, t)) = typ env t in
      Ex (KArrow (k1, k2), T.TLam (x, t))
    | S.TPrim p -> Ex (KType, T.TPrim p)
    | S.TRecord fields ->
      let f (l, t) : _ * T.ttyp =
        match typ env t with
        | Ex (KType, t) -> field l, t
        | _ -> assert false
      in
      Ex (KType, T.TRecord (List.map f fields))
    | S.TSingleton t ->
      let t = qtyp env t in
      let singleton = T.TArrow (t, TRecord []) in
      Ex (KType, TRecord [ field_singleton (), singleton ])
    | S.TEffArrow (ats, t1, eff, t2) ->
      let rec aux env = function
        | [] ->
          (match typ env t1, qtyp env t2 with
           | Ex (KType, t1), t2 ->
             let t2 = T.TRecord [ field_effect eff, t2 ] in
             T.TArrow (t1, t2)
           | _, _ -> assert false)
        | S.TVar.Ex x :: ats ->
          let Ex (_, x), env = Env.add_tvar x env in
          let t = aux env ats in
          T.TForall (x, t)
      in
      Ex (KType, aux env ats)

  and qtyp env (S.TExists (ats, t)) =
    let rec aux env : _ -> T.ttyp = function
      | [] ->
        (match typ env t with
         | Ex (KType, t) -> t
         | _ -> assert false)
      | S.TVar.Ex x :: ats ->
        let Ex (_, x), env = Env.add_tvar x env in
        T.TExists (x, aux env ats)
    in
    aux env ats
  ;;

  type tr_packtyp = Ex : 'k T.kind * 'k T.TVar.t * 'k T.typ -> tr_packtyp

  let pack_sig env ts s =
    let f env (S.Expr.TPack (a, t)) =
      match Env.add_tvar a env, typ env t with
      | (Ex (k, a), env), Ex (k', t) ->
        (match T.Kind.hequal k k' with
         | Some Equal -> env, Ex (k, a, t)
         | None -> assert false)
    in
    let env, ts = List.fold_left_map f env ts in
    match typ env s with
    | Ex (KType, s) -> ts, (s : T.Type.ttyp)
    | _ -> assert false
  ;;

  let rec _expr env = function
    | S.EVar x -> T.EVar (Env.find_var x env)
    | S.EConst c -> T.EConst c
    | S.EExternal (s, t) ->
      (match typ env t with
       | Ex (KType, t) -> T.EExternal (s, t)
       | _ -> assert false)
    | S.ERecord fields ->
      let f (l, e) = field l, expr env e in
      T.ERecord (List.map f fields)
    | S.EProj (e, p) -> T.EProj (expr env e, field p)
    | S.EPack (e, [], t) ->
      let x = S.Var.fresh () in
      expr env (S.ELet (x, S.TExists ([], t), e, S.EVar x))
    | S.EPack (e, ts, s) ->
      let ts, s = pack_sig env ts s in
      let mksig ts s = List.fold_left (fun s (Ex (_, a, _)) -> T.TExists (a, s)) s ts in
      let rec aux s = function
        | [] -> expr env e
        | Ex (_, a, t) :: ts ->
          let s' = T.Type.Subst.subst_one a t s in
          T.EPack (t, aux s' ts, a, mksig ts s)
      in
      aux s ts
    | S.EUnpack ([], x, t, e1, e2) -> expr env (ELet (x, t, e1, e2))
    | S.EUnpack (ats, x, _, e1, e2) ->
      let rec aux env e1 = function
        | [] -> assert false
        | [ S.TVar.Ex a ] ->
          let Ex (_, a), env = Env.add_tvar a env in
          let x, env = Env.add_var x env in
          T.EUnpack (a, x, e1, expr env e2)
        | S.TVar.Ex a :: ats ->
          let Ex (_, a), env = Env.add_tvar a env in
          let x = T.Var.fresh () in
          T.EUnpack (a, x, e1, aux env (T.EVar x) ats)
      in
      aux env (expr env e1) ats
    | S.ECond (x, e1, e2) -> T.ECond (expr env x, expr env e1, expr env e2)
    | S.ELet (x, t, e1, e2) ->
      let t, e1 = qtyp env t, expr env e1
      and x, env = Env.add_var x env in
      T.EApp (T.ELam (x, t, expr env e2), e1)
    | S.ESingleton t ->
      let x = T.Var.fresh () in
      let singleton = T.ELam (x, qtyp env t, T.ERecord []) in
      T.ERecord [ field_singleton (), singleton ]
    | S.EEffLam (ats, x, t, eff, e) ->
      let rec aux env = function
        | [] ->
          (match typ env t with
           | Ex (KType, t) ->
             let x, env = Env.add_var x env in
             let e = T.ERecord [ field_effect eff, expr env e ] in
             T.ELam (x, t, e)
           | _ -> assert false)
        | S.TVar.Ex a :: ats ->
          let Ex (_, a), env = Env.add_tvar a env in
          let e = aux env ats in
          T.ETyLam (a, e)
      in
      aux env ats
    | S.EEffApp (e1, ts, e2, eff) ->
      let rec aux acc = function
        | [] -> T.EProj (T.EApp (acc, expr env e2), field_effect eff)
        | S.Type.Ex t :: ts ->
          let (Ex (_, t)) = typ env t in
          aux (T.ETyApp (acc, t)) ts
      in
      aux (expr env e1) ts

  and expr env e =
    Tracing.trace2 trace "translate" _expr env e
    @@ fun tr f ->
    Tracing.printf tr "%a" PP.pp_expr e;
    let e = f () in
    Tracing.printf tr "~> %a" FOmega.PP.pp_expr e;
    e
  ;;
end
