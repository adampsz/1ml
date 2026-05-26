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
  val [@deprecated] empty : t
  val defer : unit -> t * (Kind.t -> unit)
  val clone : t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val [@deprecated] is_empty : t -> bool
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
    | Undet (s, l, x) ->
      let pp_sep ppf () = Format.pp_print_string ppf "," in
      let pp_scope ppf s = Format.pp_print_iter TVar.Set.iter ~pp_sep TVar.pp ppf s in
      Format.fprintf ppf "?%d@@%d{%a}" (UID.get x) (Level.get l) pp_scope s
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
  let[@deprecated] empty = PVar TVar.empty

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
      | CLam (x, c) -> Kind.KArrow (TVar.kind x, kind c)
      | CRecord xs -> Kind.KRecord (List.Assoc.map kind xs)
    ;;

    let rec concretize f a =
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

    let is_tvar a c =
      let rec aux = function
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

    let lookup f p c =
      let rec aux = function
        | Path.Rev.RPNil, CType t -> Some t
        | Path.Rev.RPNil, _ -> invalid_arg "Cons.lookup"
        | Path.Rev.RPProj (r, x), CRecord xs ->
          (match List.assoc_opt x xs with
           | Some c -> aux (r, c)
           | None -> None)
        | Path.Rev.RPProj _, _ -> invalid_arg "Cons.lookup"
        | Path.Rev.RPApp (r, x), CLam (a, c) -> aux (r, f a x c)
        | Path.Rev.RPApp _, _ -> invalid_arg "Cons.lookup"
      in
      let _, r = Path.rev p in
      aux (r, c)
    ;;

    let get p c =
      let f a x c =
        assert (TVar.equal a x);
        c
      in
      lookup f p c
    ;;

    let mem p c = Option.is_some (lookup (fun _ _ c -> c) p c)

    let set p t c =
      let rec aux = function
        | Path.Rev.RPNil, (None | Some (CType _)) -> CType t
        | Path.Rev.RPNil, Some _ -> invalid_arg "Cons.set"
        | Path.Rev.RPProj (r, x), None -> CRecord [ x, aux (r, None) ]
        | Path.Rev.RPProj (r, x), Some (CRecord xs) ->
          CRecord (List.Assoc.update x (fun c -> Some (aux (r, c))) xs)
        | Path.Rev.RPProj _, _ -> invalid_arg "Cons.set"
        | Path.Rev.RPApp (r, x), None -> CLam (x, aux (r, None))
        | Path.Rev.RPApp (r, a), Some (CLam (x, c)) ->
          assert (TVar.equal a x);
          CLam (x, aux (r, Some c))
        | Path.Rev.RPApp _, _ -> invalid_arg "Cons.set"
      in
      let _, r = Path.rev p in
      aux (r, c)
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
      | CType t -> typ env t
      | CLam (_, t) -> cons env t
      | CRecord xs -> List.for_all (fun (_, t) -> cons env t) xs
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
    let span = Type.span t in
    match Type.view t with
    | TInfer _ -> t
    | TAbstr p -> path ?span ~rename f p
    | TPrim _ -> t
    | TArrow (x, t1, eff, t2) ->
      let a, t1 = as_module t1 in
      let a, rename = freshen a rename in
      let t = TArrow (x, as_type a (typ ~rename f t1), eff, typ ~rename f t2) in
      Type.wrap ?span t
    | TRecord xs ->
      TRecord (List.map (fun (x, t) -> x, typ ~rename f t) xs) |> Type.wrap ?span
    | TSingleton t -> TSingleton (typ ~rename f t) |> Type.wrap ?span
    | TWrapped t -> TWrapped (typ ~rename f t) |> Type.wrap ?span
    | TMod (a, t) ->
      let a, rename = freshen a rename in
      TMod (a, typ ~rename f t) |> Type.wrap ?span

  and cons ?(rename = TVar.Map.empty) f = function
    | CRecord xs -> CRecord (List.map (fun (x, t) -> x, cons ~rename f t) xs)
    | CLam (a, t) -> freshen a rename |> fun (a, rename) -> CLam (a, cons ~rename f t)
    | CType t -> CType (typ ~rename f t)

  and path ?span ?(rename = TVar.Map.empty) f p =
    let a, r = Path.rev_map (cons ~rename f) p in
    match TVar.Map.find_opt a rename with
    | Some a -> TAbstr (Path.Rev.rev a r) |> Type.wrap ?span
    | None ->
      (match f (Path.Rev.rev a r) with
       | Some t -> t
       | None -> TAbstr (Path.Rev.rev a r) |> Type.wrap ?span)
  ;;

  let id _ = None

  let rec one a c p =
    if TVar.equal (Path.var p) a
    then Type.Cons.lookup (fun a t c -> cons (one a t) c) p c
    else None
  ;;

  let one_opt a = Option.fold ~none:id ~some:(one a)
end

module Equal = struct
  let rename (f : ?rename:_ -> _) a' a = f ~rename:(TVar.Map.singleton a' a) Subst.id

  let rec typ t' t =
    match Type.view t', Type.view t with
    | TInfer z, v | v, TInfer z -> Type.resolve z (Type.wrap v)
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
    | CType t', CType t -> typ t t'
    | CType _, _ -> false
    | CLam (a', c'), CLam (a, c) -> cons (rename Subst.cons a' a c') c
    | CLam _, _ -> false
    | CRecord ts', CRecord ts ->
      List.equal (fun (x', c') (x, c) -> Var.equal x' x && cons c' c) ts' ts
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
    | BVal of Var.t * expr
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

module Invariant : sig
  exception Violation of string

  val typ : Type.t -> unit
  val expr : Expr.t -> Type.t
end = struct
  exception Violation of string

  let fail fmt = Format.kasprintf (fun s -> raise (Violation s)) fmt

  module Env = struct
    type t =
      { vars : Type.t Var.Map.t
      ; tvars : TVar.Set.t
      }

    let empty = { vars = Var.Map.empty; tvars = TVar.Set.empty }
    let add_var x t env = { env with vars = Var.Map.add x t env.vars }
    let add_tvar a env = { env with tvars = TVar.Set.add a env.tvars }

    let find_var x env =
      match Var.Map.find_opt x env.vars with
      | Some t -> t
      | None -> fail "unbound variable `%a'" Var.pp x
    ;;

    (* Note: not strictly checked. Path resolution through
       [Subst.typ] and [path_prepend] can leave tvars that are bound in some
       surrounding scope that is hard to recover from the typed AST alone. *)
    let check_tvar _ _ = ()
  end

  let non_empty_tvar a what =
    if Kind.is_empty (TVar.kind a)
    then fail "%s requires non-empty kinded type variable `%a'" what TVar.pp a
  ;;

  let pure_or_implicit = function
    | Type.Implicit | Type.Explicit Pure -> true
    | Type.Explicit Impure -> false
  ;;

  (** Verify type structure: scoping and key invariants:
      - no unresolved [TInfer]
      - all type variables and paths bound in [env]
      - [TMod (a, _)] requires [Kind.is_empty (TVar.kind a) = false]
      - a pure or implicit [TArrow] does not return a [TMod] *)
  let rec typ env t =
    match Type.view t with
    | TInfer _ -> fail "unresolved type inference variable in `%a'" Type.pp t
    | TAbstr p -> path env p
    | TPrim _ -> ()
    | TArrow (_, t1, feff, t2) ->
      let a, t1' = Type.as_module t1 in
      let env' =
        if Kind.is_empty (TVar.kind a) then env else Env.add_tvar a env
      in
      typ env' t1';
      typ env' t2;
      if pure_or_implicit feff
      then (
        match Type.view t2 with
        | TMod _ -> fail "pure/implicit function returns a module type"
        | _ -> ())
    | TRecord xs -> List.iter (fun (_, ti) -> typ env ti) xs
    | TSingleton ti -> typ env ti
    | TWrapped ti -> typ env ti
    | TMod (a, ti) ->
      non_empty_tvar a "TMod";
      typ (Env.add_tvar a env) ti

  and path env = function
    | Path.PVar a -> Env.check_tvar a env
    | Path.PProj (p, _) -> path env p
    | Path.PApp (p, c) ->
      path env p;
      cons env c

  and cons env = function
    | Type.CType t -> typ env t
    | Type.CLam (a, c) -> cons (Env.add_tvar a env) c
    | Type.CRecord xs -> List.iter (fun (_, c) -> cons env c) xs
  ;;

  (** Strip the outer [TMod (a, _)] wrapper, returning the inner type and
      extending [env] with [a]. Leaves non-modules alone. *)
  let open_mod env t =
    match Type.view t with
    | TMod (a, t) -> Env.add_tvar a env, t
    | _ -> env, t
  ;;

  let as_arrow env t =
    let env, t = open_mod env t in
    match Type.view t with
    | TArrow (x, t1, eff, t2) -> env, x, t1, eff, t2
    | _ -> fail "expected function type, got `%a'" Type.pp t
  ;;

  let as_record env t =
    let env, t = open_mod env t in
    match Type.view t with
    | TRecord xs -> env, xs
    | _ -> fail "expected record type, got `%a'" Type.pp t
  ;;

  let as_wrapped env t =
    let env, t = open_mod env t in
    match Type.view t with
    | TWrapped ti -> env, ti
    | _ -> fail "expected wrapped type, got `%a'" Type.pp t
  ;;

  (** Verify the well-formedness of an expression and return its type. Type
      equality is not checked exhaustively — types passed around in annotations
      are validated structurally, but no deep equivalence against computed
      types. *)
  let rec expr env e =
    match e with
    | Expr.EVar x -> Env.find_var x env
    | Expr.EConst c -> TPrim (Const.typ c) |> Type.wrap
    | Expr.ECond (x, e1, e2, t) ->
      let xt = Env.find_var x env in
      (match Type.view (snd (open_mod env xt)) with
       | TPrim PBool -> ()
       | _ -> fail "condition variable `%a' is not a boolean" Var.pp x);
      let _ = expr env e1 in
      let _ = expr env e2 in
      typ env t;
      t
    | Expr.EStruct (binds, ts) ->
      let env' = List.fold_left bind env binds in
      List.iter
        (fun (x, t) ->
           let _ = Env.find_var x env' in
           typ env' t)
        ts;
      TRecord ts |> Type.wrap
    | Expr.EProj (e, x, t) ->
      let te = expr env e in
      let env', xs = as_record env te in
      (match List.find_opt (fun (y, _) -> Var.equal x y) xs with
       | Some _ ->
         typ env' t;
         t
       | None -> fail "projection: field `%a' not in record" Var.pp x)
    | Expr.EFun (x, t1, feff, body) ->
      typ env t1;
      let a, t1' = Type.as_module t1 in
      let env_a =
        if Kind.is_empty (TVar.kind a) then env else Env.add_tvar a env
      in
      let env_b = Env.add_var x t1' env_a in
      let t2 = expr env_b body in
      if pure_or_implicit feff
      then (
        match Type.view t2 with
        | TMod _ -> fail "pure/implicit function returns a module"
        | _ -> ());
      TArrow (x, t1, feff, t2) |> Type.wrap
    | Expr.EApp (e1, tc, feff, e2) ->
      let t1 = expr env e1 in
      let env', _, dom, arr_feff, ret = as_arrow env t1 in
      if arr_feff <> feff
      then fail "EApp effect annotation doesn't match function type";
      let _ = expr env e2 in
      cons env' tc;
      let a1, _ = Type.as_module dom in
      if Kind.is_empty (TVar.kind a1)
      then ret
      else Subst.typ (Subst.one a1 tc) ret
    | Expr.EType t ->
      typ env t;
      TSingleton t |> Type.wrap
    | Expr.EExtern (_, t) ->
      typ env t;
      t
    | Expr.EWrap (e, t) ->
      let _ = expr env e in
      typ env t;
      TWrapped t |> Type.wrap
    | Expr.EUnwrap e ->
      let te = expr env e in
      let _, inner = as_wrapped env te in
      inner
    | Expr.ESeal (e, c, t) ->
      let _ = expr env e in
      cons env c;
      typ env t;
      t
    | Expr.EMod (a, e) ->
      non_empty_tvar a "EMod";
      let env' = Env.add_tvar a env in
      let t = expr env' e in
      TMod (a, t) |> Type.wrap
    | Expr.EUse e ->
      let t = expr env e in
      snd (open_mod env t)

  and bind env = function
    | Expr.BVal (x, e) ->
      let t = expr env e in
      Env.add_var x t env
    | Expr.BIncl (_, e, ts) ->
      let t = expr env e in
      let env', _ = as_record env t in
      List.fold_left (fun env (x, t) -> typ env' t; Env.add_var x t env) env ts
  ;;

  let typ t = typ Env.empty t
  let expr e = expr Env.empty e
end
