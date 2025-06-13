open Prim
open Util

module Node = struct
  type span = Lexing.position * Lexing.position

  type 'a node =
    { span : span option
    ; data : 'a
    }

  type 'a t = 'a node
end

module Ident = struct
  open Node

  type data =
    | Named of string
    | Synthetic of int

  type ident = data node
  type t = ident

  let uid = ref 0
  let fresh () = Synthetic (next uid)
  let named name = Named name
  let equal = ( = )
  let compare = compare

  let name = function
    | Named name -> Some name
    | Synthetic _ -> None
  ;;

  module Map = Map.Make (struct
      type t = data

      let compare = compare
    end)
end

module Ast = struct
  open Node

  type ident = Ident.t

  type eff =
    | Pure
    | Impure

  type typ = typ_data node

  and typ_data =
    | TPrim of prim
    | TType
    | TExpr of expr
    | TWith of typ * ident list * typ
    | TStruct of decl list
    | TArrow of ident * typ * eff * typ
    | TSingleton of expr
    | TWrapped of typ

  and decl = decl_data node

  and decl_data =
    | DVal of ident * typ
    | DIncl of typ
    | DOpen of typ

  and expr = expr_data node

  and expr_data =
    | EVar of ident
    | EConst of const
    | ECond of ident * expr * expr * typ
    | EStruct of bind list
    | EProj of expr * ident
    | EFun of ident * typ * expr
    | EApp of ident * ident
    | EType of typ
    | ESeal of ident * typ
    | EExternal of string * typ
    | EWrap of ident * typ
    | EUnwrap of ident * typ

  and bind = bind_data node

  and bind_data =
    | BVal of ident * expr
    | BIncl of expr
    | BOpen of expr
end

module PP = struct
  open Node
  open Ast
  open Prim
  open Format

  let pp_eff_arrow ppf eff =
    match eff with
    | Pure -> pp_print_string ppf "=>"
    | Impure -> pp_print_string ppf "->"
  ;;

  let pp_ident ppf id =
    match id.data with
    | Ident.Named name -> pp_print_string ppf name
    | Ident.Synthetic n -> fprintf ppf "#%d" n
  ;;

  let rec pp_typ ppf t =
    match t.data with
    (* Level ∞ *)
    | TPrim PrimUnit -> pp_print_string ppf "unit"
    | TPrim PrimBool -> pp_print_string ppf "bool"
    | TPrim PrimInt -> pp_print_string ppf "int"
    | TPrim PrimFloat -> pp_print_string ppf "float"
    | TPrim PrimString -> pp_print_string ppf "string"
    | TType -> pp_print_string ppf "type"
    | TSingleton e -> fprintf ppf "(= %a)" pp_expr e
    | TStruct xs ->
      let pp_sep ppf () = pp_print_string ppf "; " in
      fprintf ppf "{ %a }" (pp_print_list ~pp_sep pp_decl) xs
    | TWith (t, xs, t') ->
      let pp_sep ppf () = pp_print_string ppf "." in
      let pp = fprintf ppf "(%a) with %a = (%a)" in
      pp pp_typ t (pp_print_list ~pp_sep pp_ident) xs pp_typ t'
    | TArrow (x, t1, eff, t2) ->
      let pp = fprintf ppf "(%a: %a) %a (%a)" in
      pp pp_ident x pp_typ t1 pp_eff_arrow eff pp_typ t2
    | TExpr e -> fprintf ppf "(%a)" pp_expr e
    | TWrapped t -> fprintf ppf "wrap (%a)" pp_typ t

  and pp_decl ppf d =
    match d.data with
    | DVal (x, t) -> fprintf ppf "%a: %a" pp_ident x pp_typ t
    | DIncl t -> fprintf ppf "include %a" pp_typ t
    | DOpen t -> fprintf ppf "open %a" pp_typ t

  and pp_expr ppf e =
    match e.data with
    | EVar x -> pp_ident ppf x
    | EConst (ConstUnit _) -> pp_print_string ppf "()"
    | EConst (ConstBool x) -> fprintf ppf "%b" x
    | EConst (ConstInt x) -> fprintf ppf "%d" x
    | EConst (ConstFloat x) -> fprintf ppf "%f" x
    | EConst (ConstString s) -> fprintf ppf "%S" s
    | ECond (c, e1, e2, t) ->
      let pp = fprintf ppf "if %a then (%a) else (%a) : (%a)" in
      pp pp_ident c pp_expr e1 pp_expr e2 pp_typ t
    | EStruct xs ->
      let pp_sep ppf () = pp_print_string ppf "; " in
      fprintf ppf "{ %a }" (pp_print_list ~pp_sep pp_bind) xs
    | EProj (e, x) -> fprintf ppf "%a.%a" pp_expr e pp_ident x
    | EFun (x, t, e) ->
      let pp = fprintf ppf "fun (%a: %a) -> (%a)" in
      pp pp_ident x pp_typ t pp_expr e
    | EApp (x1, x2) ->
      let pp = fprintf ppf "(%a) (%a)" in
      pp pp_ident x1 pp_ident x2
    | EType t -> fprintf ppf "(type %a)" pp_typ t
    | ESeal (e, t) -> fprintf ppf "(%a) :> (%a)" pp_ident e pp_typ t
    | EExternal (s, t) -> fprintf ppf "(external %s: %a)" s pp_typ t
    | EWrap (e, t) -> fprintf ppf "wrap (%a) : (%a)" pp_ident e pp_typ t
    | EUnwrap (e, t) -> fprintf ppf "unwrap (%a) : (%a)" pp_ident e pp_typ t

  and pp_bind ppf b =
    match b.data with
    | BVal (x, e) -> fprintf ppf "%a = %a" pp_ident x pp_expr e
    | BIncl e -> fprintf ppf "include %a" pp_expr e
    | BOpen e -> fprintf ppf "open %a" pp_expr e
  ;;
end

module Sugar = struct
  open Node
  open Ast

  let ( @@ ) data span = { data; span }

  let expr_var_bind e =
    match e.data with
    | EVar x -> [], x
    | _ ->
      let x = Ident.fresh () @@ e.span in
      [ BVal (x, e) @@ e.span ], x
  ;;

  let expr_let_in ?span b e =
    match b with
    | [] -> e
    | _ ->
      let x = Ident.fresh () @@ e.span in
      EProj (EStruct (b @ [ BVal (x, e) @@ span ]) @@ span, x) @@ span
  ;;

  let expr_cond ?span c e1 e2 t =
    let b, x = expr_var_bind c in
    expr_let_in ?span b (ECond (x, e1, e2, t) @@ span)
  ;;

  let expr_app ?span e = function
    | [] -> e
    | es ->
      let b, x = expr_var_bind e
      and r = Ident.fresh () @@ span in
      let f (acc, p) e =
        let b, x = expr_var_bind e in
        ((BVal (r, EApp (p, x) @@ span) @@ span) :: b) @ acc, r
      in
      let b, x = List.fold_left f (b, x) es in
      EProj (EStruct (List.rev b) @@ span, x) @@ span
  ;;

  let expr_op ?span op e1 e2 = expr_app ?span op [ e1; e2 ]

  let expr_seal ?span e t =
    let b, e = expr_var_bind e in
    expr_let_in ?span b (ESeal (e, t) @@ span)
  ;;

  let expr_annot ?span e t =
    let b1, x1 = expr_var_bind e in
    let b2, x2 = expr_var_bind (EFun (x1, t, EVar x1 @@ None) @@ span) in
    expr_let_in ?span (b1 @ b2) (EApp (x2, x1) @@ span)
  ;;

  let expr_fun ?span ps e = List.fold_right (fun (p, t) e -> EFun (p, t, e) @@ span) ps e

  let expr_wrap ?span e t =
    let b, x = expr_var_bind e in
    expr_let_in ?span b (EWrap (x, t) @@ span)
  ;;

  let expr_unwrap ?span e t =
    let b, x = expr_var_bind e in
    expr_let_in ?span b (EUnwrap (x, t) @@ span)
  ;;

  let typ_with ?span:_ t ps =
    let aux (p, t) acc = TArrow (p, t, Pure, acc) @@ None in
    let aux (xs, ps, t') t = TWith (t, xs, List.fold_right aux ps t') @@ None in
    List.fold_right aux ps t
  ;;

  let bind_typ ?span id ps t = BVal (id, expr_fun ps (EType t @@ t.span)) @@ span

  let bind_id ?span id ps ts1 ts2 e =
    let e =
      match ts1, ts2 with
      | [], [] -> e
      | ts1, ts2 ->
        let x = Ident.fresh () @@ e.span
        and f = Ident.fresh () @@ span in
        let app = BVal (x, EApp (f, x) @@ span)
        and fn t = BVal (f, EFun (x, t, EVar x @@ None) @@ t.span) in
        let cast t acc = (fn t @@ t.span) :: (app @@ t.span) :: acc
        and seal t acc = (BVal (x, ESeal (x, t) @@ span) @@ t.span) :: acc in
        let str = [] |> List.fold_right seal ts2 |> List.fold_right cast ts1 in
        EProj (EStruct ((BVal (x, e) @@ e.span) :: str) @@ e.span, x) @@ e.span
    in
    BVal (id, expr_fun ?span ps e) @@ span
  ;;

  let typ_external ?span = function
    | "unit" -> TPrim PrimUnit @@ span
    | "bool" -> TPrim PrimBool @@ span
    | "int" -> TPrim PrimInt @@ span
    | "float" -> TPrim PrimFloat @@ span
    | "string" -> TPrim PrimString @@ span
    | _ -> TType @@ span
  ;;

  let decl_id ?span id ps t =
    let f (p, t) acc = TArrow (p, t, Pure, acc) @@ None in
    DVal (id, List.fold_right f ps t) @@ span
  ;;

  let decl_id_eq ?span id ps e = decl_id ?span id ps (TSingleton e @@ e.span)
  let decl_typ ?span id ps = decl_id ?span id ps (TType @@ None)

  let decl_typ_eq ?span id ps t =
    decl_id ?span id ps (TSingleton (EType t @@ t.span) @@ t.span)
  ;;
end
