open Util
open (val Trace.init ~scope:"eval" ())
module L = Lang.Typed

module Value = struct
  type t =
    | VConst of L.Const.t
    | VRecord of (L.Var.t * t) list
    | VFunction of (t -> t)
    | VSingleton
    | VWrapped of t

  let rec pp ppf = function
    | VConst c -> L.Const.pp ppf c
    | VRecord vs ->
      let pp_field ppf (x, v) = Format.fprintf ppf "%s = %a" (L.Var.name x) pp v
      and pp_sep ppf () = Format.pp_print_string ppf "; " in
      Format.fprintf ppf "{ %a }" (Format.pp_print_list ~pp_sep pp_field) vs
    | VFunction _ -> Format.fprintf ppf "<fun>"
    | VSingleton -> Format.fprintf ppf "<singleton>"
    | VWrapped v -> Format.fprintf ppf "wrap %a" pp v
  ;;

  let rec equal v1 v2 =
    match v1, v2 with
    | VConst c1, VConst c2 -> L.Const.equal c1 c2
    | VConst _, _ -> false
    | VRecord vs1, VRecord vs2 ->
      let eq (x1, v1) (x2, v2) = L.Var.name x1 = L.Var.name x2 && equal v1 v2 in
      List.equal eq (L.Var.normalize vs1) (L.Var.normalize vs2)
    | VRecord _, _ -> false
    | VFunction _, VFunction _ -> assert false
    | VFunction _, _ -> false
    | VSingleton, VSingleton -> assert false
    | VSingleton, _ -> false
    | VWrapped v1, VWrapped v2 -> equal v1 v2
    | VWrapped _, _ -> false
  ;;

  module Convert = struct
    let of_unit x = VConst (CUnit x)
    let of_bool x = VConst (CBool x)
    let of_int x = VConst (CInt x)
    let of_char x = VConst (CChar x)
    let of_string x = VConst (CString x)
    let to_bool (VConst (CBool x)) = x
    let to_int (VConst (CInt x)) = x
    let to_char (VConst (CChar x)) = x
    let to_string (VConst (CString x)) = x
  end
end

module Env : sig
  type t

  val init : (string -> Value.t option) -> t
  val add : L.Var.t -> Value.t -> t -> t
  val find : L.Var.t -> t -> Value.t
  val extern : string -> t -> Value.t option
end = struct
  type t = Value.t L.Var.Map.t * (string -> Value.t option)

  let init extern = L.Var.Map.empty, extern
  let add x v (env, extern) = L.Var.Map.add x v env, extern
  let find x (env, _) = L.Var.Map.find x env
  let extern s (_, extern) = extern s
end

module Implicit = struct
  let rec materialize t =
    match L.Type.view t with
    | L.Type.TPrim PUnit -> Value.VConst (CUnit ())
    | L.Type.TArrow (_, _, TMod (_, _, t)) -> Value.VFunction (fun _ -> materialize t)
    | L.Type.TRecord ts -> Value.VRecord (List.map (fun (x, t) -> x, materialize t) ts)
    | L.Type.TSingleton _ -> VSingleton
    | L.Type.TWrapped (TMod (_, _, t)) -> VWrapped (materialize t)
    | _ -> assert false
  ;;

  let rec generalize v = function
    | L.Implicit.GNil _ -> v
    | L.Implicit.GGen (_, g) -> Value.VFunction (fun _ -> generalize v g)
  ;;

  let rec instantiate v = function
    | L.Implicit.INil _ -> v
    | L.Implicit.IInst (i, _, t) ->
      (match v with
       | Value.VFunction f -> instantiate (f (materialize t)) i
       | _ -> assert false)
  ;;
end

module Extern = struct
  open Value.Convert

  let unary f = Some (Value.VFunction f)
  let binary f = unary (fun x1 -> Value.VFunction (fun x2 -> f x1 x2))
  let ternary f = binary (fun x1 x2 -> Value.VFunction (fun x3 -> f x1 x2 x3))

  let pow l r =
    let rec aux acc l = function
      | r when r < 0 -> invalid_arg "pow"
      | 0 -> acc
      | r when r mod 2 = 0 -> aux acc (l * l) (r / 2)
      | r -> aux (acc * l) (l * l) (r / 2)
    in
    aux 1 l r
  ;;

  let assert_eq l r =
    if Value.equal l r
    then ()
    else Format.kasprintf failwith "expected %a, but got %a" Value.pp l Value.pp r
  ;;

  let rossberg = function
    | "==" -> binary (fun x1 x2 -> Value.VConst (CBool (Value.equal x1 x2)))
    | "Fun.bot" -> Some (Value.VFunction (fun _ -> assert false))
    | "Bool.true" -> Some (Value.VConst (CBool true))
    | "Bool.false" -> Some (Value.VConst (CBool false))
    | "Bool.print" -> unary (fun x -> of_unit (Format.printf "%b" (to_bool x)))
    | "Int.+" -> binary (fun x1 x2 -> of_int (to_int x1 + to_int x2))
    | "Int.-" -> binary (fun x1 x2 -> of_int (to_int x1 - to_int x2))
    | "Int.*" -> binary (fun x1 x2 -> of_int (to_int x1 * to_int x2))
    | "Int./" -> binary (fun x1 x2 -> of_int (to_int x1 / to_int x2))
    | "Int.%" -> binary (fun x1 x2 -> of_int (to_int x1 mod to_int x2))
    | "Int.**" -> binary (fun x1 x2 -> of_int (pow (to_int x1) (to_int x2)))
    | "Int.<" -> binary (fun x1 x2 -> of_bool (to_int x1 < to_int x2))
    | "Int.>" -> binary (fun x1 x2 -> of_bool (to_int x1 > to_int x2))
    | "Int.<=" -> binary (fun x1 x2 -> of_bool (to_int x1 <= to_int x2))
    | "Int.>=" -> binary (fun x1 x2 -> of_bool (to_int x1 >= to_int x2))
    | "Int.print" -> unary (fun x -> of_unit (Format.printf "%d" (to_int x)))
    | "Char.toInt" -> unary (fun x -> of_int (Char.code (to_char x)))
    | "Char.fromInt" -> unary (fun x -> of_char (Char.chr (to_int x)))
    | "Char.print" -> unary (fun x -> of_unit (Format.printf "%c" (to_char x)))
    | "Text.++" -> binary (fun x1 x2 -> of_string (to_string x1 ^ to_string x2))
    | "Text.<" -> binary (fun x1 x2 -> of_bool (to_string x1 < to_string x2))
    | "Text.>" -> binary (fun x1 x2 -> of_bool (to_string x1 > to_string x2))
    | "Text.<=" -> binary (fun x1 x2 -> of_bool (to_string x1 <= to_string x2))
    | "Text.>=" -> binary (fun x1 x2 -> of_bool (to_string x1 >= to_string x2))
    | "Text.length" -> unary (fun x -> of_int (String.length (to_string x)))
    | "Text.sub" ->
      ternary (fun i j x -> of_string (String.sub (to_string x) (to_int i) (to_int j)))
    | "Text.fromChar" -> unary (fun x -> of_string (String.make 1 (to_char x)))
    | "Text.print" -> unary (fun x -> of_unit (Format.printf "%s" (to_string x)))
    | "Assert.ok" -> unary (fun x -> of_unit (assert (to_bool x)))
    | "Assert.eq" -> binary (fun x1 x2 -> of_unit (assert_eq x1 x2))
    | _ -> None
  ;;

  module Compat = struct
    let effects v =
      let p, i = Lang.Typed.Type.Explicit Pure, Lang.Typed.Type.Explicit Impure in
      Lang.FOmega.Value.VRecord
        [ Elaborate.Sugar.Var.eff p, v; Elaborate.Sugar.Var.eff i, v ]
    ;;

    let rec decode = function
      | Lang.FOmega.Value.VConst c -> Value.VConst c
      | _ -> assert false
    ;;

    let rec encode = function
      | Value.VConst c -> Lang.FOmega.Value.VConst c
      | Value.VFunction f ->
        Lang.FOmega.Value.VLam (fun v -> effects (encode (f (decode v))))
      | _ -> assert false
    ;;

    let assert_eq l r =
      let open Lang.FOmega in
      if Value.equal l r
      then ()
      else Format.kasprintf failwith "expected %a, but got %a" PP.value l PP.value r
    ;;

    let rossberg extern = function
      | "Assert.eq" ->
        let open Lang.FOmega in
        let assert_eq x1 x2 = effects (encode (of_unit (assert_eq x1 x2))) in
        Some (Value.VLam (fun x1 -> effects (Value.VLam (assert_eq x1))))
      | s -> Option.map encode (extern s)
    ;;
  end
end

module Coerce = struct
  let rec coerce v = function
    | L.Coercion.CRefl -> v
    | L.Coercion.CSingleton _ -> Value.VSingleton
    | L.Coercion.CGeneralize (g, c) -> Implicit.generalize (coerce v c) g
    | L.Coercion.CInstantiate (c, i) -> coerce (Implicit.instantiate v i) c
    | L.Coercion.CRecord cs ->
      (match v with
       | VRecord vs ->
         let aux (x, c) = x, coerce (L.Var.assoc (L.Var.name x) vs |> snd) c in
         Value.VRecord (List.map aux cs)
       | _ -> assert false)
    | L.Coercion.CArrow (_, _, (_, c1, CMod (_, c2, _, _), _)) ->
      (match v with
       | VFunction f -> VFunction (fun v -> coerce (f (coerce v c1)) c2)
       | _ -> assert false)
  ;;
end

module Eval = struct
  let rec eval env expr =
    trace
      (fun m -> m ~header:"eval" "%a" L.PP.expr expr)
      (fun r m -> m ~header:"eval" "= %a" Value.pp r)
    @@ fun () ->
    match expr with
    | L.Expr.EVar x -> Env.find x env
    | L.Expr.EConst c -> Value.VConst c
    | L.Expr.ECond (x, e1, e2, _) ->
      let L.Expr.EMod (_, _, e1), L.Coercion.CMod (_, c1, _, _) = e1
      and L.Expr.EMod (_, _, e2), L.Coercion.CMod (_, c2, _, _) = e2 in
      (match Env.find x env with
       | VConst (CBool true) -> Coerce.coerce (eval env e1) c1
       | VConst (CBool false) -> Coerce.coerce (eval env e2) c2
       | _ -> assert false)
    | L.Expr.EStruct (bs, _) ->
      let _, xs = List.fold_left_map bind env bs in
      Value.VRecord (List.concat xs)
    | L.Expr.EProj (e, x, _) ->
      (match eval env e with
       | VRecord xs -> List.assoc x xs
       | _ -> assert false)
    | L.Expr.EFun (x, _, _, EMod (_, _, e)) ->
      VFunction (fun v -> eval (Env.add x v env) e)
    | L.Expr.EApp ((x1, i1), _, _, (x2, c2)) ->
      (match Implicit.instantiate (Env.find x1 env) i1 with
       | VFunction f -> f (Coerce.coerce (Env.find x2 env) c2)
       | _ -> assert false)
    | L.Expr.EType _ -> VSingleton
    | L.Expr.ESeal (x, c, _, _) -> Coerce.coerce (Env.find x env) c
    | L.Expr.EExtern (s, _) ->
      (match Env.extern s env with
       | Some v -> v
       | None -> assert false)
    | L.Expr.EWrap ((x, c), _) -> VWrapped (Coerce.coerce (Env.find x env) c)
    | L.Expr.EUnwrap (x, i, CMod (_, c, _, _), _) ->
      (match Implicit.instantiate (Env.find x env) i with
       | VWrapped v -> Coerce.coerce v c
       | _ -> assert false)
    | L.Expr.ECoerce (e, c) -> Coerce.coerce (eval env e) c
    | L.Expr.EInstantiate (e, i) -> Implicit.instantiate (eval env e) i
    | L.Expr.EGeneralize (g, e) -> Implicit.generalize (eval env e) g

  and bind env = function
    | L.Expr.BIncl (_, e, ts, _) ->
      (match eval env e with
       | VRecord vs ->
         let env = List.fold_left (fun env (x, v) -> Env.add x v env) env vs in
         env, List.map (fun (x, _) -> L.Var.assoc (L.Var.name x) vs) ts
       | _ -> assert false)
    | L.Expr.BVal (x, e, g) ->
      let v = Implicit.generalize (eval env e) g in
      let env = Env.add x v env in
      env, [ x, v ]
  ;;

  let modu env (L.Expr.EMod (_, _, e)) = eval env e
end
