let next cnt =
  incr cnt;
  !cnt
;;

type ('a, 'b) eq = ('a, 'b) Type.eq = Equal : ('a, 'a) eq

module List = struct
  include List

  let uniq_by f xs =
    let rec aux acc = function
      | [] -> List.rev acc
      | x :: xs when List.exists (fun y -> f x y) acc -> aux acc xs
      | x :: xs -> aux (x :: acc) xs
    in
    aux [] xs
  ;;
end

module type HType = sig
  type 'a t
end

module type OrderedHType = sig
  include HType

  val hcompare : 'a1 t -> 'a2 t -> int
end

module HMap = struct
  module type ValS = sig
    type t
    type 'k key
    type 'k value

    val empty : t
    val add : 'k key -> 'k value -> t -> t
    val find : 'k key -> t -> 'k value
    val find_opt : 'k key -> t -> 'k value option
    val singleton : 'k key -> 'k value -> t
    val cardinal : t -> int
    val merge_disjoint : t -> t -> t
  end

  module type S = sig
    type 'a t
    type 'k key
    type ex = Ex : 'k key -> ex

    val empty : 'a t
    val add : 'k key -> 'a -> 'a t -> 'a t
    val remove : 'k key -> 'a t -> 'a t
    val find : 'k key -> 'a t -> 'a
    val find_opt : 'k key -> 'a t -> 'a option
    val singleton : 'k key -> 'a -> 'a t
    val cardinal : 'a t -> int
    val mem : 'k key -> 'a t -> bool
    val merge_disjoint : 'a t -> 'a t -> 'a t

    module Make (Val : HType) :
      ValS with type 'k key = 'k key and type 'k value = 'k Val.t
  end

  module Make (Ord : OrderedHType) : S with type 'k key = 'k Ord.t = struct
    type ex = Ex : 'k Ord.t -> ex

    module M = Map.Make (struct
        type t = ex

        let compare (Ex x) (Ex y) = Ord.hcompare x y
      end)

    type 'a t = 'a M.t
    type 'k key = 'k Ord.t

    let empty = M.empty
    let add k v m = M.add (Ex k) v m
    let remove k m = M.remove (Ex k) m
    let find k m = M.find (Ex k) m
    let find_opt k m = M.find_opt (Ex k) m
    let singleton k v = M.singleton (Ex k) v
    let cardinal = M.cardinal
    let mem k m = M.mem (Ex k) m

    let xor _ x y =
      match x, y with
      | Some v, None | None, Some v -> Some v
      | None, None | Some _, Some _ -> failwith "disjoint"
    ;;

    let merge_disjoint m1 m2 = M.merge xor m1 m2

    module Make (Val : HType) = struct
      type nonrec 'k key = 'k key
      type nonrec 'k value = 'k Val.t
      type ex = Ex : 'k value -> ex
      type nonrec t = ex t

      let empty = empty
      let add k v m = add k (Ex v) m

      (* TODO: un-magic-ify *)
      let find k m =
        match find k m with
        | Ex v -> Obj.magic v
      ;;

      (* TODO: un-magic-ify *)
      let find_opt k m =
        match find_opt k m with
        | Some (Ex v) -> Some (Obj.magic v)
        | None -> None
      ;;

      let singleton k v = singleton k (Ex v)
      let cardinal = cardinal
      let merge_disjoint m1 m2 = merge_disjoint m1 m2
    end
  end
end

module HSet = struct
  module type S = sig
    type t
    type 'k elt
    type ex = Ex : 'k elt -> ex

    val empty : t
    val singleton : 'k elt -> t
    val add : 'k elt -> t -> t
    val remove : 'k elt -> t -> t
    val union : t -> t -> t
    val mem : 'k elt -> t -> bool
    val map : (ex -> ex) -> t -> t
    val filter : (ex -> bool) -> t -> t
    val filter_map : (ex -> ex option) -> t -> t
    val iter : (ex -> unit) -> t -> unit

    val pp
      :  ?pp_sep:(Format.formatter -> unit -> unit)
      -> (Format.formatter -> ex -> unit)
      -> Format.formatter
      -> t
      -> unit
  end

  module Make (Ord : OrderedHType) : S with type 'k elt = 'k Ord.t = struct
    type ex = Ex : 'k Ord.t -> ex

    module S = Set.Make (struct
        type t = ex

        let compare (Ex x) (Ex y) = Ord.hcompare x y
      end)

    type t = S.t
    type 'k elt = 'k Ord.t

    let empty = S.empty
    let singleton v = S.singleton (Ex v)
    let add v s = S.add (Ex v) s
    let remove v s = S.remove (Ex v) s
    let union s1 s2 = S.union s1 s2
    let mem v s = S.mem (Ex v) s
    let map f s = S.map f s
    let filter f s = S.filter f s
    let filter_map f s = S.filter_map f s
    let iter f s = S.iter f s
    let pp ?pp_sep = Format.pp_print_iter ?pp_sep iter
  end
end

module PP = struct
  open Format

  let wrap ppf fmt =
    let f ppf = kfprintf (dprintf ")") ppf fmt in
    kfprintf f ppf "("
  ;;

  let wrap w ppf = if w then wrap ppf else fprintf ppf
end

module Tracing = struct
  type t =
    { name : string
    ; mutable prefix : string
    ; mutable width : int
    ; mutable wrap : 'a 'b. string -> ('a -> 'b) -> (trace -> 'a -> 'b) -> 'a -> 'b
    }

  and trace =
    { trace : t
    ; tag : string
    ; ppf : Format.formatter
    }

  let noop _ f _ = f
  let init ?(width = 10) name = { name; prefix = ""; width; wrap = noop }

  let enable t out =
    let ppf = Format.formatter_of_out_channel out in
    t.wrap <- (fun tag _ f -> f { trace = t; tag; ppf })
  ;;

  let pr trace tr f =
    let f () =
      let prefix = tr.trace.prefix in
      tr.trace.prefix <- prefix ^ "|  ";
      let res = f () in
      tr.trace.prefix <- prefix;
      res
    in
    trace tr f
  ;;

  let trace1 t tag f x trace =
    let trace = pr trace in
    t.wrap tag f (fun tr x -> pr trace tr (fun _ -> f x)) x
  ;;

  let trace2 t tag f x1 x2 trace =
    let trace = pr trace in
    t.wrap tag f (fun tr x1 x2 -> trace tr (fun _ -> f x1 x2)) x1 x2
  ;;

  let trace3 t tag f x1 x2 x3 trace =
    let trace = pr trace in
    t.wrap tag f (fun tr x1 x2 x3 -> trace tr (fun _ -> f x1 x2 x3)) x1 x2 x3
  ;;

  let trace4 t tag f x1 x2 x3 x4 trace =
    let trace = pr trace in
    t.wrap tag f (fun tr x1 x2 x3 x4 -> trace tr (fun _ -> f x1 x2 x3 x4)) x1 x2 x3 x4
  ;;

  let printf tr fmt =
    let f ppf = Format.kfprintf (Format.dprintf "@\n%!") ppf fmt in
    let pp = Format.kfprintf f tr.ppf "[%s]%*s %s" in
    pp tr.tag (tr.trace.width - String.length tr.tag) "" tr.trace.prefix
  ;;

  let log t tag f = t.wrap tag Fun.id (fun tr () -> f (printf tr)) ()
end
