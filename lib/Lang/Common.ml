open Util

module Node : sig
  type 'a node
  type 'a t = 'a node
  type span = Lexing.position * Lexing.position

  val make : ?span:span -> 'a -> 'a node
  val span : _ node -> span option
  val data : 'a node -> 'a
  val map : ('a -> 'b) -> 'a node -> 'b node
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end = struct
  module UID = Counter.Make ()

  type span = Lexing.position * Lexing.position
  type 'a node = UID.t * 'a * span option
  type 'a t = 'a node

  let make ?span data = UID.next (), data, span
  let data (_, data, _) = data
  let span (_, _, span) = span
  let map f (_, data, span) = make ?span (f data)
  let pp pp ppf (_, data, _) = pp ppf data
end

module Prim = struct
  type prim =
    | PUnit
    | PBool
    | PInt
    | PFloat
    | PChar
    | PString
  [@@deriving show]

  type t = prim

  let compare : t -> t -> int = compare
  let equal : t -> t -> bool = ( = )
  let pp = pp_prim
end

module Const = struct
  type const =
    | CUnit of unit
    | CBool of bool
    | CInt of int
    | CFloat of float
    | CChar of char
    | CString of string
  [@@deriving show]

  type t = const

  let compare : t -> t -> int = compare
  let equal : t -> t -> bool = ( = )

  let typ = function
    | CUnit _ -> Prim.PUnit
    | CBool _ -> Prim.PBool
    | CInt _ -> Prim.PInt
    | CFloat _ -> Prim.PFloat
    | CChar _ -> Prim.PChar
    | CString _ -> Prim.PString
  ;;

  let pp = pp_const
end
