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
  let id (x, _) = UID.get x
  let name (_, name) = name
  let equal (x1, _) (x2, _) = UID.equal x1 x2
  let compare (x1, _) (x2, _) = UID.compare x1 x2
  let matches n (x, _) = String.equal n (name x)
  let assoc name xs = List.find (matches name) xs
  let assoc_opt name xs = List.find_opt (matches name) xs

  let assoc_update name f xs =
    match assoc_opt name xs with
    | Some (x, _) -> List.assoc_update x f xs
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
    | KType
    | KRecord of (Var.t * t) list [@printer Format.pp_print_record Var.pp pp]
    | KArrow of t * t
  [@@deriving show]

  type kind = t

  let equal = ( = )

  let eff = function
    | Some _ -> Effect.Impure
    | None -> Effect.Pure
  ;;

  let record = function
    | [] -> None
    | xs -> Some (KRecord xs)
  ;;

  let arrow k1 k2 =
    match k1, k2 with
    | Some k1, Some k2 -> Some (KArrow (k1, k2))
    | None, Some k2 -> Some k2
    | _, None -> None
  ;;
end

module TVar : sig
  type t

  val null : t
  val id : t -> int
  val fresh : unit -> t
  val clone : t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end = struct
  module UID = Counter.Make ()

  type t = UID.t

  let null = UID.next ()
  let id x = UID.get x
  let fresh () = UID.next ()
  let clone _ = fresh ()
  let equal x1 x2 = UID.equal x1 x2
  let compare x1 x2 = UID.compare x1 x2
  let pp ppf x = Format.fprintf ppf "#%d" (UID.get x)

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
    | PApp of 'a path * 'a * Kind.t option
  [@@deriving show]

  type 'a t = 'a path

  let pp = pp_path
  let null = PVar TVar.null

  let rec equal arg p' p =
    match p', p with
    | PVar a', PVar a -> TVar.equal a' a
    | PVar _, _ -> false
    | PProj (p', f'), PProj (p, f) -> equal arg p' p && Var.equal f' f
    | PProj _, _ -> false
    | PApp (p', a', _), PApp (p, a, _) -> equal arg p' p && arg a' a
    | PApp _, _ -> false
  ;;

  let rec var = function
    | PVar a -> a
    | PProj (p, _) -> var p
    | PApp (p, _, _) -> var p
  ;;

  let rec map f = function
    | PVar a -> PVar a
    | PProj (p, x) -> PProj (map f p, x)
    | PApp (p, a, k) -> PApp (map f p, f a, k)
  ;;

  let rec prepend p' p =
    match p with
    | PVar _ -> p'
    | PProj (p, x) -> PProj (prepend p' p, x)
    | PApp (p, a, k) -> PApp (prepend p' p, a, k)
  ;;

  module Rev = struct
    type 'a rpath =
      | RPNil
      | RPProj of 'a rpath * Var.t
      | RPApp of 'a rpath * 'a * Kind.t option

    type 'a t = 'a rpath

    let rev_append_map p f r =
      let rec aux acc = function
        | RPNil -> acc
        | RPProj (r, x) -> aux (PProj (acc, x)) r
        | RPApp (r, x, k) -> aux (PApp (acc, f x, k)) r
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
      | PApp (p, x, k) -> aux (Rev.RPApp (acc, f x, k)) p
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
    | TArrow of modu * feff * modu
    | TRecord of (Var.t * typ) list [@printer Format.pp_print_record Var.pp pp_typ]
    | TSingleton of modu
    | TWrapped of modu
  [@@deriving show]

  and modu = TMod of TVar.t * Kind.t option * typ [@@deriving show]

  and cons =
    | CRecord of (Var.t * cons) list
    | CLam of TVar.t * Kind.t option * cons
    | CType of typ
  [@@deriving show]

  and typ = T of view

  type t = typ

  let rec view = function
    | T (TInfer x as u) -> UVar.view u (fun v -> view (T v)) x
    | T t -> t
  ;;

  let wrap t = T t

  module Cons = struct
    type t = cons

    let kind c =
      let rec aux = function
        | CRecord xs -> Kind.KRecord (List.map (fun (l, c) -> l, aux c) xs)
        | CLam (_, Some k, c) -> Kind.KArrow (k, aux c)
        | CLam (_, None, c) -> aux c
        | CType _ -> Kind.KType
      in
      Option.map aux c
    ;;

    let pp = pp_cons
  end

  module Glue = struct
    let path_to_cons_path = Path.map (fun a -> CType (wrap (TAbstr (PVar a))))

    let intro_to_singleton p =
      wrap (TSingleton (TMod (TVar.null, None, wrap (TAbstr (path_to_cons_path p)))))
    ;;
  end
  [@@deprecated]

  let pp ppf t = pp_view ppf (view t)

  let is_path path t =
    let aux a = function
      | TAbstr (PVar a') -> TVar.equal a' a
      | _ -> false
    in
    let aux a = function
      | CType t -> aux a (view t)
      | _ -> false
    in
    match view t with
    | TAbstr p -> Path.equal aux path p
    | _ -> false
  ;;

  let is_small t =
    let rec typ env t =
      match view t with
      | TInfer _ -> true (* Because only small types can be infered *)
      | TAbstr p -> path env p
      | TPrim _ -> true
      | TArrow (TMod (a1, _, t1), Explicit Impure, t2) ->
        let env = TVar.Set.add a1 env in
        typ env t1 && modu env t2
      | TArrow (TMod (_, _, _), (Explicit Pure | Implicit), _) -> false
      | TRecord xs -> List.for_all (fun (_, t) -> typ env t) xs
      | TSingleton t -> modu env t
      | TWrapped _ -> true
    and modu env (TMod (a, _, t)) = typ (TVar.Set.add a env) t
    and path env = function
      | Path.PVar a -> not (TVar.Set.mem a env)
      | Path.PApp (p, t, _) -> path env p && cons env t
      | Path.PProj (p, _) -> path env p
    and cons env = function
      | CType t -> typ env t
      | CLam (_, _, t) -> cons env t
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
      | TArrow (TMod (a1, _, t1), _, t2) ->
        let env = TVar.Set.add a1 env in
        typ env t1 && modu env t2
      | TRecord ts -> List.for_all (fun (_, t) -> typ env t) ts
      | TSingleton t -> modu env t
      | TWrapped t -> modu env t
    and modu env (TMod (a, _, t)) = typ (TVar.Set.add a env) t
    and path env = function
      | Path.PVar a -> TVar.Set.mem a env
      | Path.PApp (p, c, _) -> path env p && cons env c
      | Path.PProj (p, _) -> path env p
    and cons env = function
      | CType t -> typ env t
      | CLam (a, _, t) -> cons (TVar.Set.add a env) t
      | CRecord ts -> List.for_all (fun (_, t) -> cons env t) ts
    in
    typ (UVar.scope z) t
  ;;

  let resolve z' t =
    match view t with
    | TInfer z ->
      UVar.resolve (fun z -> TInfer z) z' z;
      true
    | t when is_small (wrap t) && extrude z' (wrap t) ->
      UVar.set z' t;
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
    match ctyp ~rename f t with
    | CType t -> t
    | _ -> assert false

  and ctyp ?(rename = TVar.Map.empty) f t =
    match Type.view t with
    | TInfer _ -> CType t
    | TAbstr p -> path ~rename f p
    | TPrim p -> CType (TPrim p |> Type.wrap)
    | TArrow (TMod (a1, k1, t1), eff, t2) ->
      let a1, rename = freshen a1 rename in
      let t = TArrow (TMod (a1, k1, typ ~rename f t1), eff, modu ~rename f t2) in
      CType (Type.wrap t)
    | TRecord xs ->
      CType (TRecord (List.map (fun (x, t) -> x, typ ~rename f t) xs) |> Type.wrap)
    | TSingleton t -> CType (TSingleton (modu ~rename f t) |> Type.wrap)
    | TWrapped t -> CType (TWrapped (modu ~rename f t) |> Type.wrap)

  and modu ?(rename = TVar.Map.empty) f (TMod (a, k, t)) =
    let a, rename = freshen a rename in
    TMod (a, k, typ ~rename f t)

  and cons ?(rename = TVar.Map.empty) f = function
    | CRecord xs -> CRecord (List.map (fun (x, t) -> x, cons ~rename f t) xs)
    | CLam (a, k, t) ->
      freshen a rename |> fun (a, rename) -> CLam (a, k, cons ~rename f t)
    | CType t -> ctyp ~rename f t

  and path ?(rename = TVar.Map.empty) f p =
    let a, r = Path.rev_map (cons ~rename f) p in
    match TVar.Map.find_opt a rename with
    | Some a -> CType (TAbstr (Path.Rev.rev a r) |> Type.wrap)
    | None -> f (Path.Rev.rev a r)
  ;;

  let id p = CType (Type.wrap (TAbstr p))

  let rec one a t p =
    let unabstr t =
      match Type.view t with
      | TAbstr p -> p
      | _ -> assert false
    in
    let rec aux = function
      | PVar a' -> if TVar.equal a' a then t else id (PVar a')
      | PProj (p, x) ->
        (match aux p with
         | CRecord xs ->
           (match List.assoc_opt x xs with
            | Some c -> c
            | None -> CType (TAbstr (PProj (p, x)) |> Type.wrap))
         | CType t -> CType (TAbstr (PProj (unabstr t, x)) |> Type.wrap)
         | _ -> assert false)
      | PApp (p, c, k) ->
        (match aux p with
         | CLam (a', k', c') ->
           assert (Kind.equal k' k);
           cons (one a' c) c'
         | CType t -> CType (TAbstr (PApp (unabstr t, c, k)) |> Type.wrap)
         | _ -> assert false)
    in
    aux p
  ;;

  let one_opt a = function
    | None -> id
    | Some p -> one a p
  ;;
end

module Zipper : sig
  type t

  val empty : t
  val of_path : TVar.t Path.t -> t
  val path : TVar.t -> t -> TVar.t Path.t
  val lam : TVar.t -> Kind.t option -> t -> t
  val field : Var.t -> t -> t
  val set : Type.typ -> t -> t
  val up : t -> t
  val get : t -> Type.cons option
  val finish : t -> Type.cons option
  val subst : TVar.t -> t -> Type.cons Path.t -> Type.cons
  val pp : Format.formatter -> t -> unit
end = struct
  type trace =
    | TRecord of Var.t * (Var.t * Type.cons) list
    | TLam of TVar.t * Kind.t option

  type t = trace list * Type.cons option

  let empty = [], None

  let lam a k = function
    | z, (None | Some (Type.CLam _)) -> TLam (a, k) :: z, None
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
    | Path.PApp (p, a, k) -> lam a k (of_path p)
  ;;

  let path a (z, _) =
    let rec aux = function
      | [] -> Path.PVar a
      | TRecord (x, _) :: zs -> Path.PProj (aux zs, x)
      | TLam (a, k) :: zs -> Path.PApp (aux zs, a, k)
    in
    aux z
  ;;

  let up = function
    | TRecord (x, xs) :: ts, Some c -> ts, Some (Type.CRecord (List.rev ((x, c) :: xs)))
    | TRecord (_, []) :: ts, None -> ts, None
    | TRecord (_, xs) :: ts, None -> ts, Some (Type.CRecord (List.rev xs))
    | TLam (a, k) :: ts, Some c -> ts, Some (Type.CLam (a, k, c))
    | TLam (_, _) :: ts, None -> ts, None
    | [], _ -> invalid_arg "Zipper.up"
  ;;

  let get (_, tc) = tc

  let rec finish = function
    | [], tc -> tc
    | z -> finish (up z)
  ;;

  let subst a z = Subst.one_opt a (finish z)
  let pp ppf x = Format.pp_print_option Type.Cons.pp ppf (finish x)
end

module Expr = struct
  type expr =
    | EVar of Var.t
    | EConst of Const.t
    | ECond of Var.t * expr * expr * Type.t
    | EStruct of (bind list * (Var.t * Type.t) list)
    | EProj of expr * Var.t * Type.t
    | EFun of Var.t * Type.modu * Type.feff * modu
    | EApp of expr * Type.cons option * Type.feff * expr
    | EType of Type.modu
    | EExtern of string * Type.t
    | EWrap of modu * Type.modu
    | EUnwrap of expr
    | EInst of expr * Type.cons option * Type.t
    | EGen of Type.modu * expr
    | ESeal of modu * Type.cons option * Type.t
  [@@deriving show]

  and modu = EMod of TVar.t * Kind.t option * expr [@@deriving show]

  and bind =
    | BVal of Var.t * expr
    | BIncl of Surface.vis * expr * (Var.t * Type.t) list * Var.t list
  [@@deriving show]

  type t = expr

  let pp = pp_expr
end
