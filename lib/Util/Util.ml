include Extra

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
    let module R = Reporter (struct
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
