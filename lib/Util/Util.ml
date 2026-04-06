type ('a, 'b) eq = ('a, 'b) Type.eq = Equal : ('a, 'a) eq

module Counter = struct
  module type S = sig
    type t

    val current : unit -> t
    val next : unit -> t
    val get : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int

    module Map : Stdlib.Map.S with type key = t
  end

  module Make () : S = struct
    type t = int

    let counter = ref 0
    let current () = !counter

    let next () =
      incr counter;
      !counter
    ;;

    let get = Fun.id
    let equal = ( = )
    let compare = compare
    let hash = Int.hash

    module Map = Map.Make (struct
        type nonrec t = t

        let compare = compare
      end)
  end
end

module Once : sig
  type 'a t

  val make : unit -> 'a t
  val from_val : 'a -> 'a t
  val set : 'a t -> 'a -> unit
  val get : 'a t -> 'a
  val get_opt : 'a t -> 'a option
  val is_set : 'a t -> bool
end = struct
  type 'a t = 'a option ref

  let make () = ref None
  let from_val x = ref (Some x)

  let set c x =
    match !c with
    | Some _ -> invalid_arg "Once.set"
    | None -> c := Some x
  ;;

  let get c =
    match !c with
    | Some x -> x
    | None -> invalid_arg "Once.get"
  ;;

  let get_opt c = !c
  let is_set c = Option.is_some !c
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
end

module type HType = sig
  type 'a t
end

module type OrderedHType = sig
  include HType

  val hcompare : 'a1 t -> 'a2 t -> int
end

module HPair (A : HType) (B : HType) = struct
  type 'a t = 'a A.t * 'a B.t
end

module Existential (T : HType) = struct
  type t = Ex : 'a T.t -> t
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
    module M = Map.Make (struct
        include Existential (Ord)

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
      type ex = Existential(Val).t = Ex : 'a Val.t -> ex
      type nonrec 'k key = 'k key
      type nonrec 'k value = 'k Val.t
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

module PP = struct
  open Format

  let wrap w ppf fmt =
    if w
    then kfprintf (fun ppf -> kfprintf (dprintf ")") ppf fmt) ppf "("
    else fprintf ppf fmt
  ;;
end

module Trace : sig
  exception MaximumDepthExceeded

  val src : Logs.src
  val reporter : (string -> Format.formatter) -> Logs.reporter -> Logs.reporter

  module type Trace = sig
    val debug : ('a, unit) Logs.msgf -> unit
    val trace : ('a, unit) Logs.msgf -> ('r -> ('b, unit) Logs.msgf) -> (unit -> 'r) -> 'r
  end

  val init : ?scope:string -> unit -> (module Trace)
end = struct
  exception MaximumDepthExceeded

  type action =
    | Trace
    | Enter
    | Leave

  let src = Logs.Src.create "trace"
  let scope_tag = Logs.Tag.def "scope" (fun _ _ -> ())

  module Reporter (S : sig
      val file : string -> Format.formatter
      val reporter : Logs.reporter
    end) =
  struct
    let opened = Hashtbl.create 8
    let current = ref (Format.sink, ref 0)

    let pp_header ppf = function
      | Enter, None -> Format.fprintf ppf "> "
      | Leave, None -> Format.fprintf ppf "< "
      | Trace, None -> ()
      | Enter, Some header -> Format.fprintf ppf "> [%s] " header
      | Leave, Some header -> Format.fprintf ppf "< [%s] " header
      | Trace, Some header -> Format.fprintf ppf "[%s] " header
    ;;

    let pp_indent ppf n =
      Format.pp_open_hbox ppf ();
      Format.pp_print_break ppf (2 * n) 0;
      Format.pp_close_box ppf ()
    ;;

    let output name =
      match Hashtbl.find_opt opened name with
      | Some (ppf, indent) -> ppf, indent
      | None ->
        let ppf, indent = S.file name, ref 0 in
        Hashtbl.add opened name (ppf, indent);
        Format.pp_set_ellipsis_text ppf "...";
        Format.pp_set_margin ppf (Format.pp_infinity - 1);
        Format.pp_set_max_indent ppf (Format.pp_infinity - 2);
        Format.pp_set_max_boxes ppf 20;
        ppf, indent
    ;;

    let m over k ?header ?tags fmt =
      let action, (ppf, indent) =
        match Option.bind tags (Logs.Tag.find scope_tag) with
        | Some (action, Some name) -> action, output name
        | Some (action, None) -> action, !current
        | None -> Trace, !current
      in
      let k ppf =
        Format.pp_close_box ppf ();
        Format.pp_print_newline ppf ();
        over ();
        k ()
      in
      current := ppf, indent;
      if action = Leave then decr indent;
      pp_indent ppf !indent;
      pp_header ppf (action, header);
      if action = Enter then incr indent;
      if !indent > 1000 then raise MaximumDepthExceeded;
      Format.pp_open_box ppf 0;
      Format.kfprintf k ppf fmt
    ;;

    let report src' level ~over k msgf =
      if not (Logs.Src.equal src' src)
      then S.reporter.Logs.report src' level ~over k msgf
      else msgf (m over k)
    ;;
  end

  let reporter file reporter =
    let module R =
      Reporter (struct
        let file = file
        let reporter = reporter
      end)
    in
    Logs.{ report = R.report }
  ;;

  let with_tag ?scope ~action m ?header ?tags fmt =
    let tags = Option.value ~default:Logs.Tag.empty tags in
    let tags = Logs.Tag.add scope_tag (action, scope) tags in
    m ?header ?tags:(Some tags) fmt
  ;;

  let debug ?scope msgf =
    Logs.debug ~src (fun m -> msgf (with_tag ?scope ~action:Trace m))
  ;;

  let trace ?scope msga msgb f =
    Logs.debug ~src (fun m -> msga (with_tag ?scope ~action:Enter m));
    let r = f () in
    Logs.debug ~src (fun m -> msgb r (with_tag ?scope ~action:Leave m));
    r
  ;;

  module type Trace = sig
    val debug : ('a, unit) Logs.msgf -> unit
    val trace : ('a, unit) Logs.msgf -> ('r -> ('b, unit) Logs.msgf) -> (unit -> 'r) -> 'r
  end

  let init ?scope () =
    let module S = struct
      let debug msgf = debug ?scope msgf
      let trace a b f = trace ?scope a b f
    end
    in
    (module S : Trace)
  ;;
end

module Diagnostic = Diagnostic
