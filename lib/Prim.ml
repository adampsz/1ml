type t =
  | PrimUnit
  | PrimBool
  | PrimInt
  | PrimString

type const =
  | ConstUnit of unit
  | ConstBool of bool
  | ConstInt of int
  | ConstString of string
