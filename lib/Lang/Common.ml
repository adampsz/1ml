open Util

module Node : sig
  type 'a node
  type 'a t = 'a node
  type span = Lexing.position * Lexing.position

  val make : ?span:span -> 'a -> 'a node
  val span : _ node -> span option
  val data : 'a node -> 'a
end = struct
  module UID = Counter.Make ()

  type span = Lexing.position * Lexing.position
  type 'a node = UID.t * 'a * span option
  type 'a t = 'a node

  let make ?span data = UID.next (), data, span
  let data (_, data, _) = data
  let span (_, _, span) = span
end

module Prim = struct
  type prim =
    | PUnit
    | PBool
    | PInt
    | PFloat
    | PChar
    | PString

  type t = prim

  let compare : t -> t -> int = compare
  let equal : t -> t -> bool = ( = )

  let pp ppf = function
    | PUnit -> Format.pp_print_string ppf "unit"
    | PBool -> Format.pp_print_string ppf "bool"
    | PInt -> Format.pp_print_string ppf "int"
    | PFloat -> Format.pp_print_string ppf "float"
    | PChar -> Format.pp_print_string ppf "char"
    | PString -> Format.pp_print_string ppf "string"
  ;;
end

module Const = struct
  type const =
    | CUnit of unit
    | CBool of bool
    | CInt of int
    | CFloat of float
    | CChar of char
    | CString of string

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

  let pp ppf = function
    | CUnit () -> Format.pp_print_string ppf "()"
    | CBool b -> Format.fprintf ppf "%b" b
    | CInt i -> Format.fprintf ppf "%d" i
    | CFloat f -> Format.fprintf ppf "%f" f
    | CChar c -> Format.fprintf ppf "%C" c
    | CString s -> Format.fprintf ppf "%S" s
  ;;
end
