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

module List : sig
  include module type of List

  val fold_right_filter : ('a -> 'acc -> bool * 'acc) -> 'a list -> 'acc -> 'a list * 'acc
  val fold_right_map : ('a -> 'acc -> 'b * 'acc) -> 'a list -> 'acc -> 'b list * 'acc
  val assoc_update : 'k -> ('v option -> 'v option) -> ('k * 'v) list -> ('k * 'v) list
  val assoc_set : 'k -> 'v option -> ('k * 'v) list -> ('k * 'v) list
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

  let assoc_update x f xs =
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

  let assoc_set x v xs = assoc_update x (Fun.const v) xs
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

module Precedence : sig
  type assoc =
    | Left
    | Right
    | NonAssoc

  val setup : Format.formatter -> Format.formatter

  val wprintf
    :  'level
    -> assoc
    -> Format.formatter
    -> ('a, Format.formatter, unit) format
    -> 'a

  val reset : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
  val left : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
  val right : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
  val middle : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
end = struct
  type position =
    | PosLeft
    | PosRight
    | PosMiddle
    | PosReset

  type assoc =
    | Left
    | Right
    | NonAssoc

  type level =
    | Top
    | Level : 'a -> level

  type precedence = level * assoc

  type state =
    { mutable precedence : precedence
    ; mutable position : position
    }

  type container =
    { precedence : precedence
    ; mutable wrap : bool option
    ; mutable parent : precedence
    }

  type Format.stag += PrecContainer of container | PrecChild of position

  let should_wrap (state : state) (l, a) =
    let l', _ = state.precedence in
    match a, state.position with
    | _, PosReset -> false
    | NonAssoc, _ | _, PosMiddle -> l <= l'
    | Left, PosLeft | Right, PosRight -> l < l'
    | Left, PosRight | Right, PosLeft -> l <= l'
  ;;

  let print_open_stag fallback (state : state) = function
    | PrecContainer c ->
      c.wrap <- Some (should_wrap state c.precedence);
      c.parent <- state.precedence;
      state.precedence <- c.precedence;
      state.position <- PosMiddle
    | PrecChild p -> state.position <- p
    | other -> fallback other
  ;;

  let print_close_stag fallback (state : state) = function
    | PrecContainer c -> state.precedence <- c.parent
    | PrecChild _ -> ()
    | other -> fallback other
  ;;

  let setup ppf =
    let state = { precedence = Top, NonAssoc; position = PosReset } in
    let fns =
      let fns = Format.pp_get_formatter_stag_functions ppf () in
      let print_open_stag = print_open_stag fns.print_open_stag state
      and print_close_stag = print_close_stag fns.print_close_stag state in
      { fns with print_open_stag; print_close_stag }
    in
    Format.pp_set_formatter_stag_functions ppf fns;
    Format.pp_set_print_tags ppf true;
    ppf
  ;;

  let rec wprintf level assoc ppf fmt =
    let precedence = Level level, assoc in
    let container = { precedence; wrap = None; parent = Top, NonAssoc } in
    Format.pp_open_stag ppf (PrecContainer container);
    match container.wrap with
    | None -> wprintf level assoc (setup ppf) fmt
    | Some true ->
      Format.fprintf ppf "@[<1>(";
      Format.kfprintf (Format.dprintf ")@]@}") ppf fmt
    | Some false -> Format.kfprintf (Format.dprintf "@}") ppf fmt
  ;;

  let child pos pp ppf x =
    Format.pp_open_stag ppf (PrecChild pos);
    pp ppf x;
    Format.pp_close_stag ppf ()
  ;;

  let reset pp = child PosReset pp
  let left pp = child PosLeft pp
  let middle pp = child PosMiddle pp
  let right pp = child PosRight pp
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
