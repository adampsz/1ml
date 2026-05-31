open Util
include Common

type ident = string Node.t [@@deriving show]

type eff =
  | Pure
  | Impure
[@@deriving show]

type feff =
  | Explicit
  | Implicit
[@@deriving show]

type vis =
  | Public
  | Private
[@@deriving show]

type typ = typ_data Node.t

and typ_data =
  | TType
  | THole
  | TPrim of Prim.t
  | TExpr of expr
  | TWith of typ * ident list * typ
  | TStruct of decl list
  | TArrow of ident * typ * feff * eff * typ
  | TSingletonType of typ
  | TWrapped of typ
[@@deriving show]

and decl = decl_data Node.t

and decl_data =
  | DVal of ident * typ
  | DIncl of vis * typ
[@@deriving show]

and expr = expr_data Node.t

and expr_data =
  | EVar of ident
  | EConst of Const.t
  | ECond of ident * expr * expr * typ
  | EStruct of bind list
  | EProj of expr * ident
  | EFun of ident * typ * feff * expr
  | EApp of ident * ident
  | EType of typ
  | ESeal of ident * typ
  | EExtern of string * typ
  | EWrap of ident * typ
  | EUnwrap of ident * typ
[@@deriving show]

and bind = bind_data Node.t

and bind_data =
  | BVal of vis * ident * expr
  | BIncl of vis * expr
[@@deriving show]

type file = bind list

module Sugar = struct
  let ( @@ ) data span = Node.make ?span data

  module UID = Counter.Make ()

  type texpr =
    | T of typ
    | E of expr

  type pat = pat_data Node.t

  and pat_data =
    | PId of ident
    | PHole
    | PStruct of (ident * pat) list
    | PAnnot of pat * typ
    | PSeal of pat * typ
    | PWrap of pat * typ

  let as_typ = function
    | T t -> t
    | E e -> TExpr e @@ Node.span e

  and as_expr = function
    | T t -> EType t @@ Node.span t
    | E e -> e
  ;;

  let ident span = Printf.sprintf "#tmp%d" (UID.next () |> UID.get) @@ span

  let expr_var_bind bs e =
    match Node.data e with
    | EVar x -> bs, x
    | _ ->
      let x = ident (Node.span e) in
      (BVal (Private, x, e) @@ Node.span e) :: bs, x
  ;;

  let expr_let_in ?span bs e =
    match bs, e with
    | [], e -> e
    | bs, e ->
      let x = ident (Node.span e) in
      EProj (EStruct (bs @ [ BVal (Public, x, e) @@ span ]) @@ span, x) @@ span
  ;;

  let pat p =
    let rec aux bs e p =
      let span = Node.span p in
      match Node.data p with
      | PId x -> (BVal (Public, x, e) @@ Node.span x) :: bs
      | PHole -> (BVal (Private, ident None, e) @@ None) :: bs
      | PStruct ps ->
        List.fold_left (fun bs (x, p) -> aux bs (EProj (e, x) @@ Node.span p) p) bs ps
      | PAnnot (p, t) ->
        let bs, x = expr_var_bind bs e in
        let f = ident None in
        let e = EFun (x, t, Explicit, EVar x @@ span) @@ span in
        let b = BVal (Public, f, e) @@ span in
        aux (b :: bs) (EApp (f, x) @@ span) p
      | PSeal (p, t) ->
        let bs, x = expr_var_bind bs e in
        aux bs (ESeal (x, t) @@ span) p
      | PWrap (p, t) ->
        let bs, x = expr_var_bind bs e in
        aux bs (EUnwrap (x, t) @@ span) p
    in
    match Node.data p with
    | PId x -> Public, x, []
    | PHole -> Private, ident None, []
    | _ ->
      let x = ident None in
      Private, x, List.rev (aux [] (EVar x @@ None) p)
  ;;

  let pat_param p =
    let rec split p =
      let span = Node.span p in
      match Node.data p with
      | PHole -> PHole @@ span, THole @@ span
      | PId x -> PId x @@ span, THole @@ span
      | PStruct ps ->
        let f (x, p) = split p |> fun (p, t) -> (x, p), DVal (x, t) @@ None in
        let ps, ts = List.map f ps |> List.split in
        PStruct (List.rev ps) @@ span, TStruct (List.rev ts) @@ span
      | PAnnot (p, t) -> p, t
      | PSeal (p, t) ->
        let p, t' = split p in
        PSeal (p, t) @@ span, t'
      | PWrap (p, t) -> PWrap (p, t) @@ span, t
    in
    let p, t = split p in
    let _, x, bs = pat p in
    x, t, bs
  ;;

  let pat_tuple ?span ps =
    let f i p = Int.to_string i @@ None, p in
    PStruct (List.mapi f ps) @@ span
  ;;

  let pat_typ ?span x = PAnnot (PId x @@ span, TType @@ span) @@ span

  let expr_cond ?span c e1 e2 t =
    let bs, x = expr_var_bind [] c in
    expr_let_in ?span bs (ECond (x, e1, e2, t) @@ span)
  ;;

  let expr_or ?span ?op:_ e1 e2 =
    expr_cond ?span e1 (EConst (Const.CBool true) @@ span) e2 (TPrim PBool @@ span)
  ;;

  let expr_and ?span ?op:_ e1 e2 =
    expr_cond ?span e1 e2 (EConst (Const.CBool false) @@ span) (TPrim PBool @@ span)
  ;;

  let expr_app ?span e = function
    | [] -> e
    | es ->
      let bs, x = expr_var_bind [] e
      and r = ident span in
      let f (acc, p) e =
        let bs, x = expr_var_bind [] e in
        ((BVal (Public, r, EApp (p, x) @@ span) @@ span) :: bs) @ acc, r
      in
      let b, x = List.fold_left f (bs, x) es in
      EProj (EStruct (List.rev b) @@ span, x) @@ span
  ;;

  let expr_op ?span ?op id e1 e2 = expr_app ?span (EVar (id @@ op) @@ op) [ e1; e2 ]

  let expr_seal ?span e t =
    let bs, e = expr_var_bind [] e in
    expr_let_in ?span bs (ESeal (e, t) @@ span)
  ;;

  let expr_annot ?span e t =
    let x = ident (Node.span e) in
    let bs, x2 = expr_var_bind [] (EFun (x, t, Explicit, EVar x @@ None) @@ span) in
    let bs, x1 = expr_var_bind bs e in
    expr_let_in ?span bs (EApp (x2, x1) @@ span)
  ;;

  let expr_fun ?span ps e =
    let f (p, i) e =
      let x, t, bs = pat_param p in
      EFun (x, t, i, expr_let_in ?span bs e) @@ span
    in
    List.fold_right f ps e
  ;;

  let expr_wrap ?span e t =
    let bs, x = expr_var_bind [] e in
    expr_let_in ?span bs (EWrap (x, t) @@ span)
  ;;

  let expr_unwrap ?span e t =
    let bs, x = expr_var_bind [] e in
    expr_let_in ?span bs (EUnwrap (x, t) @@ span)
  ;;

  let expr_tuple ?span es =
    let f i e = BVal (Public, Int.to_string i @@ Node.span e, e) @@ Node.span e in
    EStruct (List.mapi f es) @@ span
  ;;

  let typ_let_in ?span b t =
    match b with
    | [] -> t
    | b -> TExpr (expr_let_in ?span b (EType t @@ span)) @@ span
  ;;

  let typ_singleton ?span t = TSingletonType t @@ span

  let typ_with ?span:_ t ps =
    let aux (p, i) acc =
      let x, t, bs = pat_param p in
      typ_let_in bs (TArrow (x, t, i, Pure, acc) @@ None)
    in
    let aux (xs, ps, t') t = TWith (t, xs, List.fold_right aux ps t') @@ None in
    List.fold_right aux ps t
  ;;

  let typ_tuple ?span ts =
    let f i t = DVal (Int.to_string i @@ Node.span t, t) @@ Node.span t in
    TStruct (List.mapi f ts) @@ span
  ;;

  let typ_app ?span:_ t ts = expr_app t ts
  let typ_fun ?span:_ ps t = expr_fun ps (EType t @@ Node.span t)

  let typ_extern ?span = function
    | "unit" -> TPrim PUnit @@ span
    | "bool" -> TPrim PBool @@ span
    | "int" -> TPrim PInt @@ span
    | "float" -> TPrim PFloat @@ span
    | "char" -> TPrim PChar @@ span
    | "string" -> TPrim PString @@ span
    | s -> Diagnostic.Error.error ?span "unknown external type `%s'" s
  ;;

  let bind_typ ?span id ps t = [ BVal (Public, id, typ_fun ps t) @@ span ]

  let bind_fun ?span x ps rs e =
    BVal (Public, x, expr_fun ?span ps (List.fold_left (fun e a -> a e) e rs)) @@ span
  ;;

  let bind_pat ?span p e =
    let vis, x, bs = pat p in
    (BVal (vis, x, e) @@ span) :: bs
  ;;

  let bind_do ?span e =
    let x = ident (Node.span e) in
    [ BVal (Private, x, e) @@ span
    ; BVal (Private, x, ESeal (x, TPrim PUnit @@ span) @@ span) @@ span
    ]
  ;;

  let decl_id ?span id ps t =
    let f (p, i) acc =
      let x, t, bs = pat_param p in
      TArrow (x, t, i, Pure, typ_let_in bs acc) @@ None
    in
    DVal (id, List.fold_right f ps t) @@ span
  ;;

  let decl_typ ?span id ps = decl_id ?span id ps (TType @@ None)
  let decl_typ_eq ?span id ps t = decl_id ?span id ps (typ_singleton t)
end
