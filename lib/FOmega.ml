(** Record label *)
type label = string

(** De Bruijn index *)
type index = int

(** κ *)
type kind =
  | KStar (** ∗ *)
  | KArrow of kind * kind (** κ → κ *)

(** b *)
type prim = Prim.t =
  | PrimUnit
  | PrimBool
  | PrimInt
  | PrimString

(** τ *)
type typ =
  | TyVar of index (** α *)
  | TyPrim of prim (** b *)
  | TyArrow of typ * typ (** τ → τ *)
  | TyRecord of (label * typ) list (** { l: τ, …, l: τ } *)
  | TyForall of string * kind * typ (** ∀κ. τ *)
  | TyExists of string * kind * typ (** ∃κ. τ *)
  | TyLam of string * kind * typ (** λα:κ. τ *)
  | TyApp of typ * typ (** τ τ *)

type const = Prim.const =
  | ConstUnit of unit
  | ConstBool of bool
  | ConstInt of int
  | ConstString of string

(** e *)
type term =
  | TmVar of index (** x *)
  | TmPrim of const (** c_b *)
  | TmLam of string * typ * term (** λx:τ. e *)
  | TmExternal of string
  | TmApp of term * term (** e e *)
  | TmRecord of (label * term) list (** { l: e, …, l: e } *)
  | TmProj of term * label (** e.l *)
  | TmTyLam of string * kind * term (** λα:κ. e *)
  | TmTyApp of term * typ (** e τ *)
  | TmPack of typ * term * string * kind * typ (** pack ⟨τ, e⟩ as ∃α:κ. τ *)
  | TmUnpack of string * string * term * term (** unpack ⟨α, x⟩ = e in e *)

type value =
  | ValPrim of const
  | ValLam of value list * term
  | ValNative of (value -> value)
  | ValRecord of (label * value) list
  | ValTyLam of value list * term
  | ValPack of value

module PP = struct
  open Format

  let rec add_name x xs = if List.mem x xs then add_name (x ^ "'") xs else x, x :: xs
  let find_name i xs = List.nth xs i

  let pp_wrap ppf w fmt =
    match w with
    | false -> fprintf ppf fmt
    | true -> kfprintf (fun f -> kfprintf (dprintf ")") f fmt) ppf "("
  ;;

  let pp_kind =
    let rec aux w fmt = function
      | KStar -> fprintf fmt "∗"
      | KArrow (k1, k2) -> pp_wrap fmt w "%a →  %a" (aux true) k1 (aux false) k2
    in
    aux false
  ;;

  let pp_typ typs =
    let rec aux p typs fmt = function
      | TyVar i -> pp_print_string fmt (find_name i typs)
      | TyPrim PrimUnit -> pp_print_string fmt "unit"
      | TyPrim PrimBool -> pp_print_string fmt "bool"
      | TyPrim PrimInt -> pp_print_string fmt "int"
      | TyPrim PrimString -> pp_print_string fmt "string"
      | TyRecord ts ->
        let pp_field fmt (l, t) = fprintf fmt "%s: %a" l (aux 0 typs) t
        and pp_sep fmt _ = pp_print_string fmt ", " in
        pp_print_string fmt "{ ";
        pp_print_list ~pp_sep pp_field fmt ts;
        pp_print_string fmt " }"
      | TyApp (t1, t2) -> pp_wrap fmt (p > 1) "%a %a" (aux 1 typs) t1 (aux 2 typs) t2
      | TyArrow (t1, t2) -> pp_wrap fmt (p > 0) "%a →  %a" (aux 1 typs) t1 (aux 0 typs) t2
      | TyForall (b, k, t) ->
        let b, typs = add_name b typs in
        pp_wrap fmt (p > 0) "∀ %s: %a. %a" b pp_kind k (aux 0 typs) t
      | TyExists (b, k, t) ->
        let b, typs = add_name b typs in
        pp_wrap fmt (p > 0) "∃ %s: %a. %a" b pp_kind k (aux 0 typs) t
      | TyLam (b, k, t) ->
        let b, typs = add_name b typs in
        pp_wrap fmt (p > 0) "λ %s: %a. %a" b pp_kind k (aux 0 typs) t
    in
    aux 0 typs
  ;;

  let pp_expr vars typs =
    let rec aux p vars typs fmt = function
      | TmVar i -> pp_print_string fmt (find_name i vars)
      | TmPrim (ConstUnit _) -> fprintf fmt "()"
      | TmPrim (ConstBool x) -> fprintf fmt "%b" x
      | TmPrim (ConstInt x) -> fprintf fmt "%d" x
      | TmPrim (ConstString x) -> fprintf fmt "%S" x
      | TmLam (b, t, e) ->
        let b, vars = add_name b vars in
        pp_wrap fmt (p > 0) "λ %s: %a. %a" b (pp_typ typs) t (aux 0 vars typs) e
      | TmExternal n -> fprintf fmt "external %s" n
      | TmApp (e1, e2) ->
        pp_wrap fmt (p > 1) "%a %a" (aux 1 vars typs) e1 (aux 2 vars typs) e2
      | TmRecord es ->
        let pp_field fmt (l, t) = fprintf fmt "%s = %a" l (aux 0 vars typs) t
        and pp_sep fmt _ = pp_print_string fmt ", " in
        pp_print_string fmt "{ ";
        pp_print_list ~pp_sep pp_field fmt es;
        pp_print_string fmt " }"
      | TmProj (e, l) -> fprintf fmt "%a.%s" (aux 2 vars typs) e l
      | TmTyLam (b, k, e) ->
        let b, typs = add_name b typs in
        pp_wrap fmt (p > 0) "λ %s: %a. %a" b pp_kind k (aux 0 vars typs) e
      | TmTyApp (e, t) ->
        pp_wrap fmt (p > 1) "%a [%a]" (aux 1 vars typs) e (pp_typ typs) t
      | TmPack (t1, e, b, k, t2) ->
        let pp_typ fmt =
          let b, typs = add_name b typs in
          fprintf fmt "∃ %s: %a. %a" b pp_kind k (pp_typ typs) t2
        and pp_t = pp_typ typs in
        pp_wrap fmt (p > 0) "pack ⟨%a, %a⟩ as %t" pp_t t1 (aux 0 vars typs) e pp_typ
      | TmUnpack (b1, b2, e1, e2) ->
        let b1, vars = add_name b1 vars
        and b2, typs = add_name b2 typs in
        let aux p = aux p vars typs in
        pp_wrap fmt (p > 0) "unpack %s, %s = %a in %a" b1 b2 (aux 0) e1 (aux 0) e2
    in
    aux 0 vars typs
  ;;

  let rec pp_value fmt = function
    | ValPrim (ConstUnit _) -> fprintf fmt "()"
    | ValPrim (ConstBool x) -> fprintf fmt "%b" x
    | ValPrim (ConstInt x) -> fprintf fmt "%d" x
    | ValPrim (ConstString x) -> fprintf fmt "%S" x
    | ValLam _ | ValTyLam _ | ValNative _ -> pp_print_string fmt "<fun>"
    | ValRecord vs ->
      let pp_field fmt (l, v) = fprintf fmt "%s: %a" l pp_value v
      and pp_sep fmt _ = pp_print_string fmt ", " in
      pp_print_string fmt "{ ";
      pp_print_list ~pp_sep pp_field fmt vs;
      pp_print_string fmt " }"
    | ValPack v -> fprintf fmt "pack %a" pp_value v
  ;;
end

module Error = struct
  exception Error of string

  let err fmt = Format.kasprintf (fun s -> Error s |> raise) fmt
  let kind_mismatch k1 k2 = err "kind mismatch: %a vs %a" PP.pp_kind k1 PP.pp_kind k2
  let expected_type_kind k = err "expected type kind, found %a" PP.pp_kind k
  let expected_function_kind k = err "expected function kind, found %a" PP.pp_kind k

  let type_mismatch ctx t1 t2 =
    err "type mismatch: %a vs %a" (PP.pp_typ ctx) t1 (PP.pp_typ ctx) t2
  ;;

  let undefined_external n = err "undefined external symbol `%s'" n
  let undefined_variable n = err "undefined variable `%s'" n
  let undefined_field n = err "undefined record field `%s'" n

  let expected_function_type ctx t =
    err "expected function type, found %a" (PP.pp_typ ctx) t
  ;;

  let expected_record_type ctx t = err "expected record type, found %a" (PP.pp_typ ctx) t

  let expected_universal_type ctx t =
    err "expected universal type, found %a" (PP.pp_typ ctx) t
  ;;

  let expected_existential_type ctx t =
    err "expected existential type, found %a" (PP.pp_typ ctx) t
  ;;

  let variable_escapes_scope ctx b t =
    err "variable %s escapes scope: %a" b (PP.pp_typ ctx) t
  ;;

  let _ =
    Printexc.register_printer (function
      | Error err -> Some err
      | _ -> None)
  ;;
end

module Type = struct
  type binding =
    | BVar of string * typ
    | BTyp of string * kind

  type env = binding list

  let add_typ b k env = BTyp (b, k) :: env

  let rec find_typ x = function
    | BTyp (_, k) :: _ when x = 0 -> k
    | BTyp _ :: env -> find_typ (x - 1) env
    | BVar _ :: env -> find_typ x env
    | [] -> assert false
  ;;

  let rec get_typs = function
    | BTyp (b, _) :: xs -> b :: get_typs xs
    | BVar _ :: xs -> get_typs xs
    | [] -> []
  ;;

  (** [shift n t] shifts all free variables in [t] by [n] *)
  let shift n =
    (* [aux f t] shifts all variables with index at least [f] by [n] *)
    let rec aux f = function
      | TyVar x when x < f -> TyVar x
      | TyVar x when x + n < 0 -> assert false
      | TyVar x -> TyVar (x + n)
      | TyPrim p -> TyPrim p
      | TyArrow (t1, t2) -> TyArrow (aux f t1, aux f t2)
      | TyRecord ts -> TyRecord (List.map (fun (l, t) -> l, aux f t) ts)
      | TyForall (x, k, t) -> TyForall (x, k, aux (f + 1) t)
      | TyExists (x, k, t) -> TyExists (x, k, aux (f + 1) t)
      | TyLam (x, k, t) -> TyLam (x, k, aux (f + 1) t)
      | TyApp (t1, t2) -> TyApp (aux f t1, aux f t2)
    in
    aux 0
  ;;

  (** [subst t' t] substitutes [0] with [t'] in [t],
      simultaneously shifting all free variables by [-1] *)
  let subst t' =
    let rec aux d x = function
      | TyVar y when y > d -> TyVar (y - 1)
      | TyVar y when y = d -> shift d t'
      | TyVar y -> TyVar y
      | TyPrim p -> TyPrim p
      | TyArrow (t1, t2) -> TyArrow (aux d x t1, aux d x t2)
      | TyApp (t1, t2) -> TyApp (aux d x t1, aux d x t2)
      | TyRecord ts -> TyRecord ((List.map (fun (l, t') -> l, aux d x t')) ts)
      | TyForall (b, k, t) -> TyForall (b, k, aux (d + 1) (x + 1) t)
      | TyExists (b, k, t) -> TyExists (b, k, aux (d + 1) (x + 1) t)
      | TyLam (b, k, t) -> TyLam (b, k, aux (d + 1) (x + 1) t)
    in
    aux 0 0
  ;;

  let rec normalize = function
    | TyVar x -> TyVar x
    | TyPrim b -> TyPrim b
    | TyArrow (t1, t2) -> TyArrow (normalize t1, normalize t2)
    | TyRecord ts -> TyRecord ((List.map (fun (l, t) -> l, normalize t)) ts)
    | TyForall (b, k, t) -> TyForall (b, k, normalize t)
    | TyExists (b, k, t) -> TyExists (b, k, normalize t)
    | TyLam (b, k, t) -> TyLam (b, k, normalize t)
    | TyApp (t1, t2) ->
      (match normalize t1, normalize t2 with
       | TyLam (_, _, t1), t2 -> subst t2 t1 |> normalize
       | t1, t2 -> TyApp (t1, t2))
  ;;

  let subst t' t = subst t' t |> normalize

  let equiv t t' =
    let rec aux = function
      | TyPrim t, TyPrim t' -> t = t'
      | TyVar x, TyVar x' -> x = x'
      | TyArrow (t1, t2), TyArrow (t1', t2') -> aux (t1, t1') && aux (t2, t2')
      | TyApp (t1, t2), TyApp (t1', t2') -> aux (t1, t1') && aux (t2, t2')
      | TyRecord ts, TyRecord ts' ->
        List.compare_lengths ts ts' = 0
        && List.for_all2 (fun (l, t) (l', t') -> l = l' && aux (t, t')) ts ts'
      | TyForall (_, k, t), TyForall (_, k', t') -> k = k' && aux (t, t')
      | TyExists (_, k, t), TyExists (_, k', t') -> k = k' && aux (t, t')
      | TyLam (_, k, t), TyLam (_, k', t') -> k = k' && aux (t, t')
      | _, _ -> false
    in
    aux (normalize t, normalize t')
  ;;

  let rec kindof env = function
    | TyPrim _ -> KStar
    | TyVar x -> find_typ x env
    | TyArrow (t1, t2) ->
      (match kindof env t1, kindof env t2 with
       | KStar, KStar -> KStar
       | KStar, k | k, _ -> Error.expected_type_kind k)
    | TyApp (t1, t2) ->
      (match kindof env t1, kindof env t2 with
       | KArrow (k1', k2), k1 when k1' = k1 -> k2
       | KArrow (k1', _), k1 -> Error.kind_mismatch k1' k1
       | k, _ -> Error.expected_function_kind k)
    | TyRecord ts ->
      let rec aux = function
        | [] -> KStar
        | (_, t) :: ts when kindof env t = KStar -> aux ts
        | (_, t) :: _ -> Error.expected_type_kind (kindof env t)
      in
      aux ts
    | TyForall (b, k, t) | TyExists (b, k, t) ->
      (match kindof (add_typ b k env) t with
       | KStar -> k
       | k -> Error.expected_type_kind k)
    | TyLam (b, k, t) -> KArrow (k, kindof (add_typ b k env) t)
  ;;

  let add_var b t env =
    assert (kindof env t = KStar);
    BVar (b, t) :: env
  ;;

  let find_var x =
    let rec aux x y = function
      | [] -> assert false
      | BVar (_, t) :: _ when x = 0 -> shift y t
      | BVar _ :: env -> aux (x - 1) y env
      | BTyp _ :: env -> aux x (y + 1) env
    in
    aux x 0
  ;;

  let rec typeof env = function
    | TmVar x -> find_var x env
    | TmPrim (ConstUnit _) -> TyPrim PrimUnit
    | TmPrim (ConstBool _) -> TyPrim PrimBool
    | TmPrim (ConstInt _) -> TyPrim PrimInt
    | TmPrim (ConstString _) -> TyPrim PrimString
    | TmLam (b, t, e) -> TyArrow (t, typeof (add_var b t env) e)
    | TmExternal _ -> TyForall ("a", KStar, TyVar 0)
    | TmApp (e1, e2) ->
      (match typeof env e1, typeof env e2 with
       | TyArrow (t1', t2), t1 when equiv t1 t1' -> t2
       | TyArrow (t1', _), t1 -> Error.type_mismatch (get_typs env) t1' t1
       | t, _ -> Error.expected_function_type (get_typs env) t)
    | TmRecord es -> TyRecord (List.map (fun (l, e) -> l, typeof env e) es)
    | TmProj (e, l) ->
      (match typeof env e with
       | TyRecord ts ->
         (match List.assoc_opt l ts with
          | Some t -> t
          | None -> Error.undefined_field l)
       | t -> Error.expected_record_type (get_typs env) t)
    | TmTyLam (b, k, e) -> TyForall (b, k, typeof (add_typ b k env) e)
    | TmTyApp (e, t) ->
      (match typeof env e with
       | TyForall (_, k, t') when kindof env t = k -> subst t t'
       | TyForall (_, k, _) -> Error.kind_mismatch k (kindof env t)
       | t -> Error.expected_universal_type (get_typs env) t)
    | TmPack (t', e, b, k, t) ->
      (match typeof env e, subst t' t with
       | t1, t2 when kindof env t' = k && equiv t1 t2 -> TyExists (b, k, t)
       | t1, t2 -> Error.type_mismatch (get_typs env) t1 t2)
    | TmUnpack (b1, b2, e1, e2) ->
      let rec check d = function
        | TyVar x -> x != d
        | TyPrim _ -> true
        | TyRecord ts -> List.for_all (fun (_, t) -> check d t) ts
        | TyArrow (t1, t2) | TyApp (t1, t2) -> check d t1 && check d t2
        | TyForall (_, _, t) | TyExists (_, _, t) | TyLam (_, _, t) -> check (d + 1) t
      in
      (match typeof env e1 with
       | TyExists (_, k, t) ->
         (match typeof (env |> add_typ b1 k |> add_var b2 t) e2 with
          | t when check 0 t -> shift (-1) t
          | t -> Error.variable_escapes_scope (get_typs env) b1 t)
       | t -> Error.expected_existential_type (get_typs env) t)
  ;;
end

module Eval = struct
  type env = (string -> value option) * value list

  let env ext = ext, []
  let add_var x (ext, env) = ext, x :: env
  let find_var x (_, env) = List.nth env x

  let rec eval env = function
    | TmVar x -> find_var x env
    | TmPrim c -> ValPrim c
    | TmLam (_, _, e) -> ValLam (snd env, e)
    | TmExternal n ->
      (match fst env n with
       | Some v -> v
       | None -> Error.undefined_external n)
    | TmApp (e1, e2) ->
      (match eval env e1, eval env e2 with
       | ValLam (v, e), v2 -> eval (add_var v2 (fst env, v)) e
       | ValNative f, v -> f v
       | _ -> assert false)
    | TmRecord es -> ValRecord (List.map (fun (l, e) -> l, eval env e) es)
    | TmProj (e, l) ->
      (match eval env e with
       | ValRecord ts -> List.assoc l ts
       | _ -> assert false)
    | TmTyLam (_, _, e) -> ValTyLam (snd env, e)
    | TmTyApp (e, _) ->
      (match eval env e with
       | ValTyLam (v, e) -> eval (fst env, v) e
       | ValNative f -> ValNative f
       | _ -> assert false)
    | TmPack (_, e, _, _, _) -> ValPack (eval env e)
    | TmUnpack (_, _, e1, e2) ->
      (match eval env e1 with
       | ValPack v -> eval (add_var v env) e2
       | _ -> assert false)
  ;;

  let eval env e =
    let typ = Type.typeof [] e in
    let value = eval env e in
    value, typ
  ;;
end
