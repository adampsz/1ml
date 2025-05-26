type t =
  | PrimUnit
  | PrimBool
  | PrimInt
  | PrimFloat
  | PrimString

type const =
  | ConstUnit of unit
  | ConstBool of bool
  | ConstInt of int
  | ConstFloat of float
  | ConstString of string
