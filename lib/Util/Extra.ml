module Set = struct
  module type S = sig
    include Set.S

    val add_opt : elt option -> t -> t
  end

  module Make (Ord : Set.OrderedType) : S with type elt = Ord.t = struct
    include Set.Make (Ord)

    let add_opt = function
      | None -> Fun.id
      | Some x -> add x
    ;;
  end
end

module String = struct
  include String

  let repeat s n =
    let len = String.length s in
    let res = Bytes.create (n * len) in
    for i = 0 to pred n do
      Bytes.blit_string s 0 res (i * len) len
    done;
    Bytes.unsafe_to_string res
  ;;

  module Set = Set.Make (String)
  module Map = Map.Make (String)
end

module Option = struct
  include Option

  let fold2 ~none ~some x y =
    match x, y with
    | Some x, Some y -> some x y
    | None, None -> none
    | _ -> invalid_arg "Option.fold2"
  ;;

  let map2 f x y =
    match x, y with
    | Some x, Some y -> Some (f x y)
    | None, None -> None
    | _ -> invalid_arg "Option.map2"
  ;;
end

module List : sig
  include module type of List

  val fold_right_filter : ('a -> 'acc -> bool * 'acc) -> 'a list -> 'acc -> 'a list * 'acc
  val fold_right_map : ('a -> 'acc -> 'b * 'acc) -> 'a list -> 'acc -> 'b list * 'acc

  module Assoc : sig
    val get : 'k -> ('k * 'v) list -> 'v
    val get_opt : 'k -> ('k * 'v) list -> 'v option
    val set : 'k -> 'v option -> ('k * 'v) list -> ('k * 'v) list
    val update : 'k -> ('v option -> 'v option) -> ('k * 'v) list -> ('k * 'v) list
    val map : ('v -> 'w) -> ('k * 'v) list -> ('k * 'w) list
    val filter_map : ('v -> 'w option) -> ('k * 'v) list -> ('k * 'w) list
  end

  module NonEmpty : sig
    type 'a t = ( :: ) of 'a * 'a list

    val fold_left : ('acc -> 'a -> 'acc) -> 'a t -> 'acc -> 'acc
    val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
    val to_list : 'a t -> 'a list
    val of_list : 'a list -> 'a t option
  end
end = struct
  include List

  let rec fold_right_filter f xs acc =
    match xs with
    | [] -> [], acc
    | x :: xs ->
      let xs, acc = fold_right_filter f xs acc in
      let keep, acc = f x acc in
      (if keep then x :: xs else xs), acc
  ;;

  let fold_right_map f xs acc =
    let rec aux xs acc =
      match xs with
      | [] -> [], acc
      | x :: xs ->
        let ys, acc = aux xs acc in
        let y, acc = f x acc in
        y :: ys, acc
    in
    aux xs acc
  ;;

  module Assoc = struct
    let get = assoc
    let get_opt = assoc_opt

    let update x f xs =
      let add_opt xs = function
        | None -> xs
        | Some v -> (x, v) :: xs
      in
      let rec aux = function
        | [] -> add_opt [] (f None)
        | (y, v) :: xs when Stdlib.compare x y = 0 -> add_opt xs (f (Some v))
        | xv :: xs -> xv :: aux xs
      in
      aux xs
    ;;

    let set x v xs = update x (Fun.const v) xs
    let map f xs = List.map (fun (k, v) -> k, f v) xs

    let filter_map f xs =
      List.filter_map (fun (k, v) -> Option.map (fun v -> k, v) (f v)) xs
    ;;
  end

  module NonEmpty = struct
    type 'a t = ( :: ) of 'a * 'a list

    let fold_left f (x :: xs) acc = List.fold_left f acc (x :: xs)
    let fold_right f (x :: xs) acc = List.fold_right f (x :: xs) acc
    let to_list (x :: xs) = List.(x :: xs)

    let of_list = function
      | [] -> None
      | x :: xs -> Some (x :: xs)
    ;;
  end
end

module Format = struct
  include Format

  let sink = make_formatter (fun _ _ _ -> ()) (fun _ -> ())
  let tprintf fmt ppf () = fprintf ppf fmt

  let pp_print_record ?(pp_sep = tprintf ",@ ") ?(pp_ksep = tprintf " :@ ") =
    fun pp_key pp_value ppf -> function
    | [] -> pp_print_string ppf "{ }"
    | xs ->
      let pp_entry ppf (k, v) =
        fprintf ppf "@[<2>%a%a%a@]" pp_key k pp_ksep () pp_value v
      in
      let br = pp_print_custom_break ~fits:("", 1, "") ~breaks:(",", -2, "") in
      fprintf ppf "{@[<hv 1>@;%a%t@]}" (pp_print_list ~pp_sep pp_entry) xs br
  ;;

  let pp_print_nonempty_record ?pp_sep ?pp_ksep pp_key pp_value ppf xs =
    pp_print_record ?pp_sep ?pp_ksep pp_key pp_value ppf (List.NonEmpty.to_list xs)
  ;;

  let with_margin margin pp ppf x =
    let g = Format.pp_get_geometry ppf () in
    let max_indent = min g.max_indent (margin - 1) in
    Format.pp_set_geometry ppf ~margin ~max_indent;
    Fun.protect
      ~finally:(fun () ->
        Format.pp_set_geometry ppf ~margin:g.margin ~max_indent:g.max_indent)
      (fun () -> pp ppf x)
  ;;

  let with_max_boxes boxes pp ppf x =
    let b = Format.pp_get_max_boxes ppf () in
    Format.pp_set_max_boxes ppf boxes;
    Fun.protect ~finally:(fun () -> Format.pp_set_max_boxes ppf b) (fun () -> pp ppf x)
  ;;
end
