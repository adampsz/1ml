let next cnt =
  incr cnt;
  !cnt
;;

type ('a, 'b) eq = ('a, 'b) Type.eq = Equal : ('a, 'a) eq

module HMap = struct
  module type HType = sig
    type 'k t
  end

  module type OrderedHType = sig
    type 'k t

    val hcompare : 'k1 t -> 'k2 t -> int
  end

  module type S1 = sig
    type t
    type 'k key
    type 'k value

    val empty : t
    val add : 'k key -> 'k value -> t -> t
    val find : 'k key -> t -> 'k value
    val find_opt : 'k key -> t -> 'k value option
    val singleton : 'k key -> 'k value -> t
  end

  module type S = sig
    type 'a t
    type 'k key

    val empty : 'a t
    val add : 'k key -> 'a -> 'a t -> 'a t
    val find : 'k key -> 'a t -> 'a
    val find_opt : 'k key -> 'a t -> 'a option
    val singleton : 'k key -> 'a -> 'a t

    module Make (Val : HType) : S1 with type 'k key = 'k key and type 'k value = 'k Val.t
  end

  module Make (Ord : OrderedHType) : S with type 'k key = 'k Ord.t = struct
    module O = struct
      type t = Ex : 'k Ord.t -> t

      let compare (Ex x) (Ex y) = Ord.hcompare x y
    end

    module M = Map.Make (O)

    type 'a t = 'a M.t
    type 'k key = 'k Ord.t

    let empty = M.empty
    let add k v m = M.add (O.Ex k) v m
    let find k m = M.find (O.Ex k) m
    let find_opt k m = M.find_opt (O.Ex k) m
    let singleton k v = M.singleton (O.Ex k) v

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
    end
  end
end
