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
  val compare : t -> t -> int
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
    | KType
    | KArrow of t * t
    | KRecord of (Var.t * t) List.t [@printer Format.pp_print_record Var.pp pp]
  [@@deriving show]

  type kind = t

  let empty = KRecord []
  let equal = ( = )

  let rec is_empty = function
    | KType -> false
    | KRecord xs -> List.for_all (fun (_, k) -> is_empty k) xs
    | KArrow (_, k) -> is_empty k
  ;;

  let opt k = if is_empty k then None else Some k

  let opt_record = function
    | [] -> None
    | ks -> Some (KRecord ks)
  ;;

  let opt_arrow k1 k2 = Some (KArrow (k1, Option.value k2 ~default:empty))

  module Option = struct
    type nonrec t = t option

    let pp ppf = function
      | None -> Format.pp_print_string ppf "{ }"
      | Some k -> pp ppf k
    ;;

    let eff k = if Option.is_none k then Effect.Pure else Effect.Impure
  end
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

  let clone (k, _) = k, UID.next ()
  let equal (_, x1) (_, x2) = UID.equal x1 x2
  let compare (_, x1) (_, x2) = UID.compare x1 x2
  let pp ppf (_, x) = Format.fprintf ppf "#%d" (UID.get x)
  let empty = fresh Kind.empty
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

  let compare p' p =
    let rec aux r' r =
      match r', r with
      | Rev.RPNil, Rev.RPNil -> Some 0
      | Rev.RPNil, _ -> Some (-1)
      | _, Rev.RPNil -> Some 1
      | Rev.RPProj (r', x'), Rev.RPProj (r, x) ->
        (match Var.compare x' x with
         | 0 -> aux r' r
         | c -> Some c)
      | Rev.RPProj _, _ -> None
      | Rev.RPApp (r', _), Rev.RPApp (r, _) -> aux r' r
      | Rev.RPApp _, _ -> None
    in
    let a', r' = rev p'
    and a, r = rev p in
    if TVar.equal a' a then aux r' r else None
  ;;
end

module UVar : sig
  type 'a t

  module Level : sig
    type t

    val get : t -> int
  end

  type level = Level.t

  val fresh : TVar.Set.t -> TVar.t Path.t -> 'a t
  val scope : 'a t -> TVar.Set.t
  val paths : 'a t -> TVar.t Path.t list
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
    | Undet of TVar.Set.t * TVar.t Path.t list * Level.t * UID.t
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
    | Undet (_, _, l, _) -> l >= level
    | _ -> false
  ;;

  let fresh scope path =
    let u = ref (Undet (scope, [ path ], Level.current (), UID.next ())) in
    debug (fun m ->
      let m = m ~header:"uvar.fresh" "#T%d@%d" in
      m (UID.current () |> UID.get) (Level.current () |> Level.get));
    u
  ;;

  let equal = ( == )

  let scope = function
    | { contents = Undet (s, _, _, _) } -> s
    | _ -> invalid_arg "UVar.scope"
  ;;

  let paths = function
    | { contents = Undet (_, p, _, _) } -> p
    | _ -> invalid_arg "UVar.paths"
  ;;

  let level = function
    | { contents = Undet (_, _, l, _) } -> l
    | _ -> invalid_arg "UVar.level"
  ;;

  let id = function
    | { contents = Undet (_, _, _, id) } -> UID.get id
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
    | Undet (s', b', l', x') when l' > level -> z' := Undet (s', b', level, x')
    | _ -> ()
  ;;

  let resolve f z' z =
    match !z', !z with
    | Undet (_, _, _, x'), Undet (_, _, _, x) when UID.equal x' x -> ()
    | Undet (s', p', l', _), Undet (s, p, l, _) ->
      let z'' = Undet (TVar.Set.inter s' s, p' @ p, min l' l, UID.next ()) in
      let t = f (ref z'') in
      set z t;
      set z' t
    | _, _ -> invalid_arg "UVar.resolve"
  ;;

  let pp pp ppf z =
    match !z with
    | Det x -> pp ppf x
    | Undet (s, _, l, x) ->
      let pp_sep ppf () = Format.pp_print_string ppf "," in
      let pp_scope ppf s = Format.pp_print_iter TVar.Set.iter ~pp_sep TVar.pp ppf s in
      Format.fprintf ppf "?%d@@%d{%a}" (UID.get x) (Level.get l) pp_scope s
  ;;
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
    | CType of typ
    | CLam of TVar.t * cons
    | CRecord of (Var.t * cons) list [@printer Format.pp_print_record Var.pp pp_cons]
  [@@deriving show]

  and typ = view Node.t [@@deriving show]

  type t = typ
  type span = Node.span

  let rec view t =
    match Node.data t with
    | TInfer x as u -> UVar.view u (fun v -> view (Node.make v)) x
    | data -> data
  ;;

  let wrap ?span v : typ = Node.make ?span v
  let span = Node.span
  let with_span ?span t = Node.make ?span (Node.data t)

  let as_module t =
    match view t with
    | TMod (a, t) -> a, t
    | _ -> TVar.empty, t
  ;;

  let as_type a t = if TVar.is_empty a then t else TMod (a, t) |> wrap ?span:(Node.span t)

  module Cons = struct
    type t = cons

    let empty : cons option = None

    let rec kind = function
      | CType _ -> Kind.KType
      | CLam (a, tc) -> Kind.KArrow (TVar.kind a, kind tc)
      | CRecord xs -> Kind.KRecord (List.Assoc.map kind xs)
    ;;

    let concretize f a =
      let rec aux path = function
        | Kind.KType -> CType (f path)
        | Kind.KRecord xs ->
          CRecord (List.map (fun (x, k) -> x, aux (Path.PProj (path, x)) k) xs)
        | Kind.KArrow (k1, k2) ->
          let a1 = TVar.fresh k1 in
          CLam (a1, aux (Path.PApp (path, a1)) k2)
      in
      aux (PVar a) (TVar.kind a)
    ;;

    let is_tvar a tc =
      let rec aux = function
        | CType t ->
          (match view t with
           | TAbstr p -> TVar.equal a (Path.var p)
           | _ -> false)
        | CLam (_, tc) -> aux tc
        | CRecord xs -> List.for_all (fun (_, tc) -> aux tc) xs
      in
      Kind.equal (kind tc) (TVar.kind a) && aux tc
    ;;

    let pp = pp_cons

    let lookup f p tc =
      let rec aux = function
        | Path.Rev.RPNil, CType t -> Some t
        | Path.Rev.RPNil, _ -> invalid_arg "Cons.lookup"
        | Path.Rev.RPProj (r, x), CRecord xs ->
          (match List.assoc_opt x xs with
           | Some tc -> aux (r, tc)
           | None -> None)
        | Path.Rev.RPProj _, _ -> invalid_arg "Cons.lookup"
        | Path.Rev.RPApp (r, x), CLam (a, tc) -> aux (r, f a x tc)
        | Path.Rev.RPApp _, _ -> invalid_arg "Cons.lookup"
      in
      let _, r = Path.rev p in
      aux (r, tc)
    ;;

    let get p tc =
      let f a x tc =
        assert (TVar.equal a x);
        tc
      in
      lookup f p tc
    ;;

    let mem p tc = Option.is_some (lookup (fun _ _ tc -> tc) p tc)

    let set p t tc =
      let rec aux = function
        | Path.Rev.RPNil, (None | Some (CType _)) -> CType t
        | Path.Rev.RPNil, Some _ -> invalid_arg "Cons.set"
        | Path.Rev.RPProj (r, x), None -> CRecord [ x, aux (r, None) ]
        | Path.Rev.RPProj (r, x), Some (CRecord xs) ->
          CRecord (List.Assoc.update x (fun tc -> Some (aux (r, tc))) xs)
        | Path.Rev.RPProj _, _ -> invalid_arg "Cons.set"
        | Path.Rev.RPApp (r, a), None -> CLam (a, aux (r, None))
        | Path.Rev.RPApp (r, a), Some (CLam (x, tc)) ->
          assert (TVar.equal a x);
          CLam (x, aux (r, Some tc))
        | Path.Rev.RPApp _, _ -> invalid_arg "Cons.set"
      in
      let _, r = Path.rev p in
      aux (r, tc)
    ;;
  end

  let rec path_to_abstr p =
    Path.map (Cons.concretize (fun p -> TAbstr (path_to_abstr p) |> wrap)) p
  ;;

  let pp ppf t = pp_view ppf (view t)

  let is_path path t =
    match view t with
    | TAbstr p -> Path.equal Cons.is_tvar path p
    | _ -> false
  ;;

  let is_small t =
    let rec typ env t =
      match view t with
      | TInfer _ -> true (* Because only small types can be inferred *)
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
      | Path.PApp (p, tc) -> path env p && cons env tc
      | Path.PProj (p, _) -> path env p
    and cons env = function
      | CType t -> typ env t
      | CLam (_, tc) -> cons env tc
      | CRecord xs -> List.for_all (fun (_, tc) -> cons env tc) xs
    in
    typ TVar.Set.empty t
  ;;

  let rec is_generative a t =
    match view t with
    | TAbstr p -> TVar.equal a (Path.var p)
    | TInfer _ | TPrim _ | TWrapped _ | TMod _ -> false
    | TRecord ts -> List.exists (fun (_, t) -> is_generative a t) ts
    | TArrow (_, _, _, t) -> is_generative a t
    | TSingleton t -> is_generative a t
  ;;

  let eff a t = if is_generative a t then Effect.Impure else Effect.Pure

  let forbidden p q =
    match Path.compare q p with
    | Some c -> c >= 0
    | None -> false
  ;;

  let extrude z t =
    let rec typ env t =
      match view t with
      | TInfer z' ->
        UVar.extrude (UVar.level z) z';
        true
      | TAbstr p ->
        path env p && List.for_all (fun p' -> not (forbidden p' p)) (UVar.paths z)
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
      | Path.PApp (p, tc) -> path env p && cons env tc
      | Path.PProj (p, _) -> path env p
    and cons env = function
      | CType t -> typ env t
      | CLam (a, tc) -> cons (TVar.Set.add a env) tc
      | CRecord ts -> List.for_all (fun (_, tc) -> cons env tc) ts
    in
    typ (UVar.scope z) t
  ;;

  let occurs z t =
    let rec typ t =
      match view t with
      | TInfer z' -> UVar.equal z z'
      | TAbstr p -> path p
      | TPrim _ -> false
      | TArrow (_, t1, _, t2) -> typ t1 || typ t2
      | TRecord ts -> List.exists (fun (_, t) -> typ t) ts
      | TSingleton t -> typ t
      | TWrapped t -> typ t
      | TMod (_, t) -> typ t
    and path = function
      | Path.PVar _ -> false
      | Path.PApp (p, tc) -> path p || cons tc
      | Path.PProj (p, _) -> path p
    and cons = function
      | CType t -> typ t
      | CLam (_, tc) -> cons tc
      | CRecord ts -> List.exists (fun (_, tc) -> cons tc) ts
    in
    typ t
  ;;

  let resolve z' t =
    match view t with
    | TInfer z ->
      UVar.resolve (fun z -> TInfer z) z' z;
      true
    | _ when (not (occurs z' t)) && is_small t && extrude z' t ->
      UVar.set z' (view t);
      true
    | _ -> false
  ;;
end

module Rename = struct
  open Type

  let freshen a rename =
    let a' = TVar.clone a in
    a', TVar.Map.add a a' rename
  ;;

  let rec typ rename t =
    let span = Type.span t in
    match Type.view t with
    | TInfer _ -> t
    | TAbstr p -> path ?span rename p
    | TPrim _ -> t
    | TArrow (x, t1, eff, t2) ->
      let a, t1 = as_module t1 in
      let a, rename = freshen a rename in
      let t = TArrow (x, as_type a (typ rename t1), eff, typ rename t2) in
      Type.wrap ?span t
    | TRecord xs ->
      TRecord (List.map (fun (x, t) -> x, typ rename t) xs) |> Type.wrap ?span
    | TSingleton t -> TSingleton (typ rename t) |> Type.wrap ?span
    | TWrapped t -> TWrapped (typ rename t) |> Type.wrap ?span
    | TMod (a, t) ->
      let a, rename = freshen a rename in
      TMod (a, typ rename t) |> Type.wrap ?span

  and cons rename = function
    | CRecord xs -> CRecord (List.map (fun (x, tc) -> x, cons rename tc) xs)
    | CLam (a, tc) -> freshen a rename |> fun (a, rename) -> CLam (a, cons rename tc)
    | CType t -> CType (typ rename t)

  and path ?span rename p =
    let a, r = Path.rev_map (cons rename) p in
    let a = Option.value (TVar.Map.find_opt a rename) ~default:a in
    TAbstr (Path.Rev.rev a r) |> Type.wrap ?span
  ;;

  let typ ?(rename = TVar.Map.empty) t = typ rename t
  let cons ?(rename = TVar.Map.empty) tc = cons rename tc
  let one a' a = TVar.Map.singleton a' a
end

module Subst = struct
  open Type

  let rec typ a f t =
    let span = Type.span t in
    match Type.view t with
    | TInfer _ -> t
    | TAbstr p -> path ?span a f p
    | TPrim _ -> t
    | TArrow (x, t1, eff, t2) ->
      let b, t1 = as_module t1 in
      TArrow (x, as_type b (typ a f t1), eff, typ a f t2) |> Type.wrap ?span
    | TRecord xs -> TRecord (List.map (fun (x, t) -> x, typ a f t) xs) |> Type.wrap ?span
    | TSingleton t -> TSingleton (typ a f t) |> Type.wrap ?span
    | TWrapped t -> TWrapped (typ a f t) |> Type.wrap ?span
    | TMod (b, t) -> TMod (b, typ a f t) |> Type.wrap ?span

  and cons a f = function
    | CRecord xs -> CRecord (List.map (fun (x, tc) -> x, cons a f tc) xs)
    | CLam (b, tc) -> CLam (b, cons a f tc)
    | CType t -> CType (typ a f t)

  and path ?span a f p =
    let b, r = Path.rev_map (cons a f) p in
    let p = Path.Rev.rev b r in
    if TVar.equal b a then f p else TAbstr p |> Type.wrap ?span
  ;;

  let rec one tc p =
    match Type.Cons.lookup (fun a tc1 tc2 -> cons a (one tc1) tc2) p tc with
    | Some t -> t
    | None -> TAbstr p |> Type.wrap
  ;;

  let one_opt = function
    | Some tc -> one tc
    | None -> fun p -> TAbstr p |> Type.wrap
  ;;
end

module Equal = struct
  let rec typ ?(unify = false) t' t =
    match Type.view t', Type.view t with
    | (TInfer z, v | v, TInfer z) when unify -> Type.resolve z (Type.wrap v)
    | TInfer z', TInfer z -> UVar.equal z' z
    | TInfer _, _ -> false
    | TAbstr p', TAbstr p -> Path.equal (cons ~unify) p' p
    | TAbstr _, _ -> false
    | TPrim p', TPrim p -> p' = p
    | TPrim _, _ -> false
    | TArrow (_, t1', eff', t2'), TArrow (_, t1, eff, t2) ->
      let (a', t1'), (a, t1) = Type.as_module t1', Type.as_module t1 in
      let rename = Rename.one a' a in
      eff' = eff
      && typ ~unify (Rename.typ ~rename t1') t1
      && typ ~unify (Rename.typ ~rename t2') t2
    | TArrow _, _ -> false
    | TRecord ts', TRecord ts ->
      let eq (x', t') (x, t) = Var.name x' = Var.name x && typ ~unify t' t in
      List.equal eq ts' ts
    | TRecord _, _ -> false
    | TSingleton t', TSingleton t -> typ ~unify t' t
    | TSingleton _, _ -> false
    | TWrapped t', TWrapped t -> typ ~unify t' t
    | TWrapped _, _ -> false
    | TMod (a', t'), TMod (a, t) -> typ ~unify (Rename.typ ~rename:(Rename.one a' a) t') t
    | TMod _, _ -> false

  and cons ?unify tc' tc =
    match tc', tc with
    | CType t', CType t -> typ ?unify t' t
    | CType _, _ -> false
    | CLam (a', tc'), CLam (a, tc) ->
      cons ?unify (Rename.cons ~rename:(Rename.one a' a) tc') tc
    | CLam _, _ -> false
    | CRecord ts', CRecord ts ->
      List.equal (fun (x', tc') (x, tc) -> Var.equal x' x && cons ?unify tc' tc) ts' ts
    | CRecord _, _ -> false
  ;;
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
    | ESeal of expr * Type.cons * Type.t
    | EMod of TVar.t * expr
    | EUse of expr
  [@@deriving show]

  and bind =
    | BVal of Surface.vis * Var.t * expr
    | BIncl of Surface.vis * expr * (Var.t * Type.t) list
  [@@deriving show]

  type t = expr

  let pp = pp_expr

  let as_module = function
    | EMod (a, e) -> a, e
    | e -> TVar.empty, e
  ;;

  let as_expr a e = if TVar.is_empty a then e else EMod (a, e)
end

module Env = struct
  type t =
    { vars : (Var.t * Type.t) list
    ; tvars : TVar.Set.t
    ; path : TVar.t Path.t
    }

  let empty = { vars = []; tvars = TVar.Set.empty; path = Path.empty }
  let add_var x t env = { env with vars = (x, t) :: env.vars }
  let add_tvar a env = { env with tvars = TVar.Set.add a env.tvars }
  let enter_mod a env = { (add_tvar a env) with path = Path.PVar a }
  let enter_lam a env = { env with path = Path.PApp (env.path, a) }
  let enter_field x env = { env with path = Path.PProj (env.path, x) }
  let domain env = env.tvars
  let path env = env.path
  let vars env = env.vars
  let find_var x env = snd (List.find (fun (y, _) -> Var.equal x y) env.vars)
  let find_tvar a env = if not (TVar.Set.mem a env.tvars) then raise Not_found
end

module Invariant = struct
  exception Violation

  let fail () = raise Violation
  let invariant cond = if not cond then fail ()

  let unique_paths kind =
    let rec aux = function
      | Kind.KType -> true
      | Kind.KArrow (k1, k2) -> aux k1 && aux k2
      | Kind.KRecord xs ->
        let rec fields = function
          | [] -> true
          | (x, k) :: xs -> (not (List.mem_assoc x xs)) && aux k && fields xs
        in
        fields xs
    in
    aux kind
  ;;

  module Env = struct
    include Env

    let find_var x env =
      try find_var x env with
      | Not_found -> fail ()
    ;;

    let find_tvar a env =
      try find_tvar a env with
      | Not_found -> fail ()
    ;;
  end

  let rec typ env t =
    trace
      (fun m -> m ~header:"typ" "%a at %a" Type.pp t (Path.pp TVar.pp) env.Env.path)
      (fun _ m -> m ~header:"typ" "ok")
    @@ fun () ->
    match Type.view t with
    | TInfer _ -> fail ()
    | TAbstr p -> path env p
    | TPrim _ -> ()
    | TArrow (x, t1, _, t2) ->
      typ env t1;
      let a, t1 = Type.as_module t1 in
      let env = Env.enter_lam a (Env.add_var x t1 (Env.add_tvar a env)) in
      typ env t2
    | TRecord xs ->
      let decl (x, t) = typ (Env.enter_field x env) t in
      List.iter decl xs
    | TSingleton t -> typ env t
    | TWrapped t -> typ env t
    | TMod (a, t) ->
      invariant (not (TVar.is_empty a));
      invariant (unique_paths (TVar.kind a));
      typ (Env.enter_mod a env) t

  and path env = function
    | Path.PVar a -> Env.find_tvar a env
    | Path.PProj (p, _) -> path env p
    | Path.PApp (p, tc) ->
      cons env tc;
      path env p

  and cons env = function
    | Type.CType t -> typ env t
    | Type.CLam (a, tc) ->
      invariant (unique_paths (TVar.kind a));
      cons (Env.add_tvar a env) tc
    | Type.CRecord xs -> List.iter (fun (_, tc) -> cons env tc) xs
  ;;

  let rec expr env e =
    trace
      (fun m -> m ~header:"expr" "%a at %a" Expr.pp e (Path.pp TVar.pp) env.Env.path)
      (fun t m -> m ~header:"expr" "~> %a" Type.pp t)
    @@ fun () ->
    match e with
    | EVar x -> Env.find_var x env
    | EConst c -> Type.TPrim (Const.typ c) |> Type.wrap
    | ECond (x, e1, e2, t) ->
      invariant (Equal.typ (Env.find_var x env) (TPrim PBool |> Type.wrap));
      invariant (Equal.typ (expr env e1) t);
      invariant (Equal.typ (expr env e2) t);
      typ env t;
      t
    | EStruct (xs, ts) ->
      let _, xs = List.fold_left_map bind env xs in
      let ts' = List.concat xs |> Var.normalize in
      let eq (x', t') (x, t) = Var.equal x' x && Equal.typ t' t in
      invariant (List.equal eq ts' ts);
      TRecord ts |> Type.wrap
    | EProj (e, x, t) ->
      let t' =
        match expr env e |> Type.view with
        | TRecord ts' ->
          (match List.assoc_opt x ts' with
           | Some t' -> t'
           | None -> fail ())
        | _ -> fail ()
      in
      invariant (Equal.typ t' t);
      t
    | EFun (x, t1, eff, e2) ->
      typ env t1;
      let a, t1 = Type.as_module t1 in
      let env = Env.enter_lam a (Env.add_var x t1 (Env.add_tvar a env)) in
      let t2 = expr env e2 in
      TArrow (x, Type.as_type a t1, eff, t2) |> Type.wrap
    | EApp (e, tc, eff', e1) ->
      let t1, eff, t2 =
        match expr env e |> Type.view with
        | TArrow (_, t1, eff, t2) -> t1, eff, t2
        | _ -> fail ()
      in
      let a, t1 = Type.as_module t1 in
      let t1' = expr env e1 in
      cons (Env.add_tvar a env) tc;
      invariant (eff = eff');
      invariant (Equal.typ (Subst.typ a (Subst.one tc) t1) t1');
      Subst.typ a (Subst.one tc) t2
    | EType t ->
      typ env t;
      TSingleton t |> Type.wrap
    | EExtern (_, t) ->
      typ env t;
      t
    | EWrap (e, t) ->
      let t' = TWrapped (expr env e) |> Type.wrap in
      invariant (Equal.typ t' t);
      t
    | EUnwrap e ->
      (match expr env e |> Type.view with
       | TWrapped t -> t
       | _ -> fail ())
    | ESeal (e, tc, s) ->
      let a, t = Type.as_module (expr env e) in
      cons (Env.add_tvar a env) tc;
      let a, s = Type.as_module s in
      invariant (Equal.typ (Subst.typ a (Subst.one tc) s) t);
      Type.as_type a s
    | EMod (a, e) ->
      invariant (not (TVar.is_empty a));
      let t = expr (Env.enter_mod a env) e in
      TMod (a, t) |> Type.wrap
    | EUse e ->
      let path_map a f t = Subst.typ a (fun p -> TAbstr (f p) |> Type.wrap) t in
      (match expr env e |> Type.view with
       | TMod (a, t) -> path_map a (Path.prepend (Type.path_to_abstr env.Env.path)) t
       | _ -> fail ())

  and bind env b =
    match b with
    | Expr.BVal (vis, x, e) ->
      let t = expr (Env.enter_field x env) e in
      let env = Env.add_var x t env in
      env, if vis = Public then [ x, t ] else []
    | Expr.BIncl (vis, e, ts) ->
      let ts =
        match expr env e |> Type.view with
        | TRecord ts' ->
          let eq (x', t') (x, t) = Var.equal x' x && Equal.typ t' t in
          invariant (List.equal eq ts' ts);
          ts
        | _ -> fail ()
      in
      let env = List.fold_left (fun env (x, t) -> Env.add_var x t env) env ts in
      env, if vis = Public then ts else []
  ;;
end
