open Util
include (val Trace.init ())
include Common

module Effect = struct
  type t = Surface.eff =
    | Pure
    | Impure
  [@@deriving show]

  let join e1 e2 =
    match e1, e2 with
    | Pure, Pure -> Pure
    | _ -> Impure
  ;;

  let sub e1 e2 =
    match e1, e2 with
    | Impure, Pure -> false
    | _, _ -> true
  ;;
end

module Var : sig
  type t

  val fresh : string -> t
  val clone : t -> t
  val id : t -> int
  val name : t -> string
  val equal : t -> t -> bool
  val assoc : string -> (t * 'a) list -> t * 'a
  val assoc_opt : string -> (t * 'a) list -> (t * 'a) option
  val assoc_update : string -> ('a option -> 'a option) -> (t * 'a) list -> (t * 'a) list
  val normalize : (t * 'a) list -> (t * 'a) list
  val pp : Format.formatter -> t -> unit

  module Map : Map.S with type key = t
end = struct
  module UID = Counter.Make ()
  module StringSet = Set.Make (String)

  type t = UID.t * string

  let fresh name = UID.next (), name
  let clone (_, name) = fresh name
  let id (x, _) = UID.get x
  let name (_, name) = name
  let equal (x1, _) (x2, _) = UID.equal x1 x2
  let compare (x1, _) (x2, _) = UID.compare x1 x2
  let matches n (x, _) = String.equal n (name x)
  let assoc name xs = List.find (matches name) xs
  let assoc_opt name xs = List.find_opt (matches name) xs

  let assoc_update name f xs =
    match assoc_opt name xs with
    | Some (x, _) -> List.Assoc.update x f xs
    | None -> Option.fold ~none:xs ~some:(fun v -> (fresh name, v) :: xs) (f None)
  ;;

  let normalize xs =
    let f (f, _) acc = not (StringSet.mem (name f) acc), StringSet.add (name f) acc in
    let xs, _ = List.fold_right_filter f xs StringSet.empty in
    xs
  ;;

  let pp ppf (x, name) = Format.fprintf ppf "%s#%d" name (UID.get x)

  module Map = Map.Make (struct
      type nonrec t = t

      let compare = compare
    end)
end

module Kind = struct
  type t =
    | KEmpty
    | KType
    | KArrow of t * t
    | KRecord of (Var.t * t) list [@printer Format.pp_print_record Var.pp pp]
  [@@deriving show]

  type kind = t

  let equal = ( = )

  let rec is_empty = function
    | KEmpty -> true
    | KType -> false
    | KRecord xs -> List.for_all (fun (_, k) -> is_empty k) xs
    | KArrow (_, k) -> is_empty k
  ;;

  let eff k = if is_empty k then Effect.Pure else Effect.Impure
end

module TVar : sig
  type t

  val id : t -> int
  val kind : t -> Kind.t
  val fresh : Kind.t -> t
  val empty : t
  val defer : unit -> t * (Kind.t -> unit)
  val clone : t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val is_empty : t -> bool
  val pp : Format.formatter -> t -> unit

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end = struct
  module UID = Counter.Make ()

  type t = Kind.t Once.t * UID.t

  let id (_, x) = UID.get x
  let kind (k, _) = Once.get k
  let fresh k = Once.from_val k, UID.next ()

  let defer () =
    let x = Once.make () in
    (x, UID.next ()), fun k -> Once.set x k
  ;;

  let set (kc, _) k = Once.set kc k
  let clone (k, _) = k, UID.next ()
  let equal (_, x1) (_, x2) = UID.equal x1 x2
  let compare (_, x1) (_, x2) = UID.compare x1 x2
  let pp ppf (_, x) = Format.fprintf ppf "#%d" (UID.get x)
  let empty = fresh Kind.KEmpty
  let is_empty x = Kind.is_empty (kind x)

  module Set = Set.Make (struct
      type nonrec t = t

      let compare = compare
    end)

  module Map = Map.Make (struct
      type nonrec t = t

      let compare = compare
    end)
end

module UVar : sig
  type 'a t

  module Level : sig
    type t

    val get : t -> int
  end

  type level = Level.t

  val fresh : TVar.Set.t -> 'a t
  val scope : 'a t -> TVar.Set.t
  val level : 'a t -> level
  val id : 'a t -> int
  val equal : 'a t -> 'a t -> bool
  val get : 'a t -> 'a option
  val set : 'a t -> 'a -> unit
  val view : 'a -> ('a -> 'a) -> 'a t -> 'a
  val resolve : ('a t -> 'a) -> 'a t -> 'a t -> unit
  val extrude : level -> 'a t -> unit
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

  (* Levels *)

  val stamp : unit -> level
  val newer : level -> 'a t -> bool
end = struct
  module UID = Counter.Make ()
  module Level = Counter.Make ()

  type 'a state =
    | Undet of TVar.Set.t * Level.t * UID.t
    | Det of 'a

  type 'a t = 'a state ref
  type level = Level.t

  let stamp () =
    let level = Level.next () in
    debug (fun m -> m ~header:"uvar.stamp" "@%d" (Level.get level));
    level
  ;;

  let newer level z =
    match !z with
    | Undet (_, l, _) -> l >= level
    | _ -> false
  ;;

  let fresh scope =
    let u = ref (Undet (scope, Level.current (), UID.next ())) in
    debug (fun m ->
      let m = m ~header:"uvar.fresh" "#T%d@%d" in
      m (UID.current () |> UID.get) (Level.current () |> Level.get));
    u
  ;;

  let equal = ( == )

  let scope = function
    | { contents = Undet (s, _, _) } -> s
    | _ -> invalid_arg "UVar.scope"
  ;;

  let level = function
    | { contents = Undet (_, l, _) } -> l
    | _ -> invalid_arg "UVar.level"
  ;;

  let id = function
    | { contents = Undet (_, _, id) } -> UID.get id
    | _ -> invalid_arg "UVar.id"
  ;;

  let get = function
    | { contents = Det v } -> Some v
    | _ -> None
  ;;

  let set z v =
    match !z with
    | Undet _ -> z := Det v
    | Det _ -> invalid_arg "UVar.set"
  ;;

  let view t f = function
    | { contents = Det t } as u ->
      let t = f t in
      u := Det t;
      t
    | _ -> t
  ;;

  let extrude level z' =
    match !z' with
    | Undet (s', l', x') when l' > level -> z' := Undet (s', level, x')
    | _ -> ()
  ;;

  let resolve f z' z =
    match !z', !z with
    | Undet (_, _, x'), Undet (_, _, x) when UID.equal x' x -> ()
    | Undet (s', l', _), Undet (s, l, _) ->
      let t = f (ref (Undet (TVar.Set.inter s' s, min l' l, UID.next ()))) in
      set z t;
      set z' t
    | _, _ -> invalid_arg "UVar.resolve"
  ;;

  let pp pp ppf z =
    match !z with
    | Det x -> pp ppf x
    | Undet (_, l, x) -> Format.fprintf ppf "#%d@@%d" (UID.get x) (Level.get l)
  ;;
end

module Path = struct
  type 'a path =
    | PVar of TVar.t
    | PProj of 'a path * Var.t
    | PApp of 'a path * 'a
  [@@deriving show]

  type 'a t = 'a path

  let pp = pp_path
  let empty = PVar TVar.empty

  let rec equal arg p' p =
    match p', p with
    | PVar a', PVar a -> TVar.equal a' a
    | PVar _, _ -> false
    | PProj (p', f'), PProj (p, f) -> equal arg p' p && Var.equal f' f
    | PProj _, _ -> false
    | PApp (p', a'), PApp (p, a) -> equal arg p' p && arg a' a
    | PApp _, _ -> false
  ;;

  let rec var = function
    | PVar a -> a
    | PProj (p, _) -> var p
    | PApp (p, _) -> var p
  ;;

  let rec map f = function
    | PVar a -> PVar a
    | PProj (p, x) -> PProj (map f p, x)
    | PApp (p, a) -> PApp (map f p, f a)
  ;;

  let rec prepend p' p =
    match p with
    | PVar _ -> p'
    | PProj (p, x) -> PProj (prepend p' p, x)
    | PApp (p, a) -> PApp (prepend p' p, a)
  ;;

  module Rev = struct
    type 'a rpath =
      | RPNil
      | RPProj of 'a rpath * Var.t
      | RPApp of 'a rpath * 'a

    type 'a t = 'a rpath

    let rev_append_map p f r =
      let rec aux acc = function
        | RPNil -> acc
        | RPProj (r, x) -> aux (PProj (acc, x)) r
        | RPApp (r, x) -> aux (PApp (acc, f x)) r
      in
      aux p r
    ;;

    let rev_append a r = rev_append_map a Fun.id r
    let rev_map a f r = rev_append_map (PVar a) f r
    let rev a r = rev_append_map (PVar a) Fun.id r
  end

  let rev_map f p =
    let rec aux acc = function
      | PVar a -> a, acc
      | PProj (p, x) -> aux (Rev.RPProj (acc, x)) p
      | PApp (p, x) -> aux (Rev.RPApp (acc, f x)) p
    in
    aux Rev.RPNil p
  ;;

  let rev p = rev_map Fun.id p
end

module Type = struct
  type feff =
    | Implicit
    | Explicit of Effect.t
  [@@deriving show]

  type view =
    | TInfer of view UVar.t
    | TAbstr of cons Path.t
    | TPrim of Prim.t
    | TArrow of Var.t * typ * feff * typ
    | TRecord of (Var.t * typ) list [@printer Format.pp_print_record Var.pp pp_typ]
    | TSingleton of typ
    | TWrapped of typ
    | TMod of TVar.t * typ
  [@@deriving show]

  and cons =
    | CEmpty
    | CType of typ
    | CLam of TVar.t * cons
    | CRecord of (Var.t * cons) list [@printer Format.pp_print_record Var.pp pp_cons]
  [@@deriving show]

  and typ = T of view

  type t = typ

  let rec view = function
    | T (TInfer x as u) -> UVar.view u (fun v -> view (T v)) x
    | T t -> t
  ;;

  let wrap t = T t

  let as_module t =
    match view t with
    | TMod (a, t) -> a, t
    | _ -> TVar.empty, t
  ;;

  let as_type = function
    | a, t when TVar.is_empty a -> t
    | a, t -> TMod (a, t) |> wrap
  ;;

  module Cons = struct
    type t = cons

    let rec kind = function
      | CEmpty -> Kind.KEmpty
      | CType _ -> Kind.KType
      | CLam (x, c) -> Kind.KArrow (TVar.kind x, kind c)
      | CRecord xs -> Kind.KRecord (List.Assoc.map kind xs)
    ;;

    let rec is_tvar a c =
      let rec aux = function
        | CEmpty -> true
        | CType t ->
          (match view t with
           | TAbstr p -> TVar.equal a (Path.var p)
           | _ -> false)
        | CLam (_, c) -> aux c
        | CRecord xs -> List.for_all (fun (_, c) -> aux c) xs
      in
      Kind.equal (kind c) (TVar.kind a) && aux c
    ;;

    let equal = ( = )
    let pp = pp_cons
  end

  module Glue = struct
    let rec concretize a =
      let rec aux path = function
        | Kind.KEmpty -> CEmpty
        | Kind.KType -> CType (TAbstr path |> wrap)
        | Kind.KRecord xs ->
          CRecord (List.map (fun (x, k) -> x, aux (Path.PProj (path, x)) k) xs)
        | Kind.KArrow (k1, k2) ->
          let a1 = TVar.fresh k1 in
          CLam (a1, aux (Path.PApp (path, concretize a1)) k2)
      in
      aux (PVar a) (TVar.kind a)
    ;;

    let path_to_cons_path = Path.map concretize
    let intro_to_singleton p = wrap (TSingleton (wrap (TAbstr (path_to_cons_path p))))
  end
  [@@deprecated]

  let pp ppf t = pp_view ppf (view t)

  let is_path path t =
    match view t with
    | TAbstr p -> Path.equal Cons.is_tvar path p
    | _ -> false
  ;;

  let is_small t =
    let rec typ env t =
      match view t with
      | TInfer _ -> true (* Because only small types can be infered *)
      | TAbstr p -> path env p
      | TPrim _ -> true
      | TArrow (_, t1, Explicit Impure, t2) ->
        let a, t1 = as_module t1 in
        let env = TVar.Set.add a env in
        typ env t1 && typ env t2
      | TArrow (_, _, (Explicit Pure | Implicit), _) -> false
      | TRecord xs -> List.for_all (fun (_, t) -> typ env t) xs
      | TSingleton t -> typ env t
      | TWrapped _ -> true
      | TMod (a, t) -> typ (TVar.Set.add a env) t
    and path env = function
      | Path.PVar a -> not (TVar.Set.mem a env)
      | Path.PApp (p, t) -> path env p && cons env t
      | Path.PProj (p, _) -> path env p
    and cons env = function
      | CEmpty -> true
      | CType t -> typ env t
      | CLam (_, t) -> cons env t
      | CRecord xs -> List.for_all (fun (_, t) -> cons env t) xs
    in
    typ TVar.Set.empty t
  ;;

  let extrude z t =
    let rec typ env t =
      match view t with
      | TInfer z' ->
        UVar.extrude (UVar.level z) z';
        true
      | TAbstr p -> path env p
      | TPrim _ -> true
      | TArrow (_, t1, _, t2) ->
        let a, t1 = as_module t1 in
        let env = TVar.Set.add a env in
        typ env t1 && typ env t2
      | TRecord ts -> List.for_all (fun (_, t) -> typ env t) ts
      | TSingleton t -> typ env t
      | TWrapped t -> typ env t
      | TMod (a, t) -> typ (TVar.Set.add a env) t
    and path env = function
      | Path.PVar a -> TVar.Set.mem a env
      | Path.PApp (p, c) -> path env p && cons env c
      | Path.PProj (p, _) -> path env p
    and cons env = function
      | CEmpty -> true
      | CType t -> typ env t
      | CLam (a, t) -> cons (TVar.Set.add a env) t
      | CRecord ts -> List.for_all (fun (_, t) -> cons env t) ts
    in
    typ (UVar.scope z) t
  ;;

  let resolve z' t =
    match view t with
    | TInfer z ->
      UVar.resolve (fun z -> TInfer z) z' z;
      true
    | _ when is_small t && extrude z' t ->
      UVar.set z' (view t);
      true
    | _ -> false
  ;;
end

module Subst = struct
  open Path
  open Type

  let freshen a rename =
    let a' = TVar.clone a in
    a', TVar.Map.add a a' rename
  ;;

  let rec typ ?(rename = TVar.Map.empty) f t =
    match Type.view t with
    | TInfer _ -> t
    | TAbstr p -> path ~rename f p
    | TPrim _ -> t
    | TArrow (x, t1, eff, t2) ->
      let a, t1 = as_module t1 in
      let a, rename = freshen a rename in
      let t = TArrow (x, as_type (a, typ ~rename f t1), eff, typ ~rename f t2) in
      Type.wrap t
    | TRecord xs -> TRecord (List.map (fun (x, t) -> x, typ ~rename f t) xs) |> Type.wrap
    | TSingleton t -> TSingleton (typ ~rename f t) |> Type.wrap
    | TWrapped t -> TWrapped (typ ~rename f t) |> Type.wrap
    | TMod (a, t) ->
      let a, rename = freshen a rename in
      TMod (a, typ ~rename f t) |> Type.wrap

  and cons ?(rename = TVar.Map.empty) f = function
    | CEmpty -> CEmpty
    | CRecord xs -> CRecord (List.map (fun (x, t) -> x, cons ~rename f t) xs)
    | CLam (a, t) -> freshen a rename |> fun (a, rename) -> CLam (a, cons ~rename f t)
    | CType t -> CType (typ ~rename f t)

  and path ?(rename = TVar.Map.empty) f p =
    let a, r = Path.rev_map (cons ~rename f) p in
    match TVar.Map.find_opt a rename with
    | Some a -> TAbstr (Path.Rev.rev a r) |> Type.wrap
    | None -> f (Path.Rev.rev a r)
  ;;

  let id p = TAbstr p |> Type.wrap

  let rec one a t p =
    let rec aux = function
      | PVar a' -> if TVar.equal a' a then Some t else None
      | PProj (p, x) ->
        (match aux p with
         | Some (CRecord xs) ->
           (match List.assoc_opt x xs with
            | Some c -> Some c
            | None -> None)
         | None -> None
         | _ -> assert false)
      | PApp (p, c) ->
        (match aux p with
         | Some (CLam (a', c')) ->
           assert (Kind.equal (TVar.kind a') (Type.Cons.kind c));
           Some (cons (one a' c) c')
         | None -> None
         | _ -> assert false)
    in
    match aux p with
    | Some (CType t) -> t
    | None -> TAbstr p |> Type.wrap
    | _ -> assert false
  ;;
end

module Equal = struct
  let rename (f : ?rename:_ -> _) a' a = f ~rename:(TVar.Map.singleton a' a) Subst.id

  let rec typ t' t =
    match Type.view t', Type.view t with
    | TInfer z, t | t, TInfer z -> Type.resolve z (Type.wrap t)
    | TAbstr p', TAbstr p -> Path.equal cons p' p
    | TAbstr _, _ -> false
    | TPrim p', TPrim p -> p' = p
    | TPrim _, _ -> false
    | TArrow (_, t1', eff', t2'), TArrow (_, t1, eff, t2) ->
      let (a', t1'), (a, t1) = Type.as_module t1', Type.as_module t1 in
      eff' = eff
      && typ (rename Subst.typ a' a t1') t1
      && typ (rename Subst.typ a' a t2') t2
    | TArrow _, _ -> false
    | TRecord ts', TRecord ts ->
      List.equal (fun (x', t') (x, t) -> Var.equal x' x && typ t' t) ts' ts
    | TRecord _, _ -> false
    | TSingleton t', TSingleton t -> typ t' t
    | TSingleton _, _ -> false
    | TWrapped t', TWrapped t -> typ t' t
    | TWrapped _, _ -> false
    | TMod (a', t'), TMod (a, t) -> typ (rename Subst.typ a' a t') t
    | TMod _, _ -> false

  and cons c' c =
    match c', c with
    | CEmpty, CEmpty -> true
    | CEmpty, _ -> false
    | CType t', CType t -> typ t t'
    | CType _, _ -> false
    | CLam (a', c'), CLam (a, c) -> cons (rename Subst.cons a' a c') c
    | CLam _, _ -> false
    | CRecord ts', CRecord ts ->
      List.equal (fun (x', c') (x, c) -> Var.equal x' x && cons c' c) ts' ts
    | CRecord _, _ -> false
  ;;
end

module Zipper : sig
  type t

  val empty : t
  val of_path : TVar.t Path.t -> t
  val path : TVar.t -> t -> TVar.t Path.t
  val lam : TVar.t -> t -> t
  val field : Var.t -> t -> t
  val set : Type.typ -> t -> t
  val up : t -> t
  val get : t -> Type.cons
  val finish : t -> Type.cons
  val subst : TVar.t -> t -> Type.cons Path.t -> Type.typ
  val pp : Format.formatter -> t -> unit
end = struct
  type trace =
    | TRecord of Var.t * (Var.t * Type.cons) list
    | TLam of TVar.t

  type t = trace list * Type.cons option

  let empty = [], None

  let lam a = function
    | z, (None | Some (Type.CLam _)) -> TLam a :: z, None
    | _, Some _ -> invalid_arg "Zipper.lam"
  ;;

  let field x = function
    | z, None -> TRecord (x, []) :: z, None
    | z, Some (Type.CRecord xs) -> TRecord (x, List.rev xs) :: z, None
    | _, Some _ -> invalid_arg "Zipper.record"
  ;;

  let set t (z, _) = z, Some (Type.CType t)

  let rec of_path = function
    | Path.PVar _ -> empty
    | Path.PProj (p, x) -> field x (of_path p)
    | Path.PApp (p, a) -> lam a (of_path p)
  ;;

  let path a (z, _) =
    let rec aux = function
      | [] -> Path.PVar a
      | TRecord (x, _) :: zs -> Path.PProj (aux zs, x)
      | TLam a :: zs -> Path.PApp (aux zs, a)
    in
    aux z
  ;;

  let up = function
    | TRecord (x, xs) :: ts, Some c -> ts, Some (Type.CRecord (List.rev ((x, c) :: xs)))
    | TRecord (_, xs) :: ts, None ->
      ts, Some (Type.CRecord (List.rev xs)) (* TODO: remove? *)
    | TLam a :: ts, Some c -> ts, Some (Type.CLam (a, c))
    | TLam _ :: ts, None -> ts, None (* TODO: remove? *)
    | [], _ -> invalid_arg "Zipper.up"
  ;;

  let get = function
    | _, Some c -> c
    | _, None -> Type.CEmpty
  ;;

  let rec finish = function
    | [], Some c -> c
    | [], None -> Type.CEmpty
    | z -> finish (up z)
  ;;

  let subst a z = Subst.one a (finish z)
  let pp ppf x = Type.Cons.pp ppf (finish x)
end

module Expr = struct
  type expr =
    | EVar of Var.t
    | EConst of Const.t
    | ECond of Var.t * expr * expr * Type.t
    | EStruct of (bind list * (Var.t * Type.t) list)
    | EProj of expr * Var.t * Type.t
    | EFun of Var.t * Type.typ * Type.feff * expr
    | EApp of expr * Type.cons * Type.feff * expr
    | EType of Type.typ
    | EExtern of string * Type.t
    | EWrap of expr * Type.typ
    | EUnwrap of expr
    | EInst of expr * Type.cons * Type.t
    | EGen of Type.typ * expr
    | ESeal of expr * Type.cons * Type.t
    | EMod of TVar.t * expr
    | EUse of expr
  [@@deriving show]

  and bind =
    | BVal of Var.t * expr
    | BIncl of Surface.vis * expr * (Var.t * Type.t) list
  [@@deriving show]

  type t = expr

  let pp = pp_expr

  let as_module = function
    | EMod (a, e) -> a, e
    | e -> TVar.empty, e
  ;;
end
