type t =
  | PrimUnit
  | PrimBool
  | PrimInt
  | PrimFloat
  | PrimString

type prim = t

type const =
  | ConstUnit of unit
  | ConstBool of bool
  | ConstInt of int
  | ConstFloat of float
  | ConstString of string

module PP = struct
  let pp_prim ppf = function
    | PrimUnit -> Format.pp_print_string ppf "unit"
    | PrimBool -> Format.pp_print_string ppf "bool"
    | PrimInt -> Format.pp_print_string ppf "int"
    | PrimFloat -> Format.pp_print_string ppf "float"
    | PrimString -> Format.pp_print_string ppf "string"
  ;;

  let pp_const ppf = function
    | ConstUnit () -> Format.pp_print_string ppf "unit"
    | ConstBool b -> Format.fprintf ppf "%b" b
    | ConstInt i -> Format.fprintf ppf "%d" i
    | ConstFloat f -> Format.fprintf ppf "%f" f
    | ConstString s -> Format.fprintf ppf "%S" s
  ;;
end
