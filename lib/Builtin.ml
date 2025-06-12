open FOmega
open Value

let pure f v = VRecord [ "%p", f v ]
let impure f v = VRecord [ "%i", f v ]
let unary f = VExternal f
let unary_pure f = VExternal (pure f)
let unary_impure f = VExternal (impure f)
let binary f = VExternal (fun x -> VExternal (f x))
let binary_pure f = VExternal (pure (fun x -> VExternal (pure (f x))))
let binary_impure f = VExternal (impure (fun x -> VExternal (impure (f x))))

let binary_int f =
  binary_impure
  @@ fun x y ->
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (f x y)
  | _, _ -> assert false
;;

let panic =
  unary_impure
  @@ function
  | VPrim (ConstString s) -> failwith (Printf.sprintf "Program panicked: %s" s)
  | _ -> failwith "Program panicked: unknown error"
;;

let print =
  unary_impure
  @@ function
  | VPrim (ConstString x) -> VPrim (ConstUnit (Format.printf "%s\n%!" x))
  | x -> VPrim (ConstUnit (Format.printf "%a\n%!" PP.pp_value x))
;;

let igt = binary_int (fun x y -> ConstBool (x > y))
let ige = binary_int (fun x y -> ConstBool (x >= y))
let ilt = binary_int (fun x y -> ConstBool (x < y))
let ile = binary_int (fun x y -> ConstBool (x <= y))
let iadd = binary_int (fun x y -> ConstInt (x + y))
let isub = binary_int (fun x y -> ConstInt (x - y))
let imul = binary_int (fun x y -> ConstInt (x * y))
let idiv = binary_int (fun x y -> ConstInt (x / y))
let imod = binary_int (fun x y -> ConstInt (x mod y))

let ipow =
  let rec aux acc b = function
    | e when e < 0 -> raise (Invalid_argument "ipow")
    | 0 -> acc
    | e when e land 1 = 0 -> aux acc (b * b) (e lsr 1)
    | e -> aux (b * acc) (b * b) (e lsr 1)
  in
  binary_int @@ fun x y -> ConstInt (aux 1 x y)
;;

let builtin = function
  | "panic" -> Some panic
  | "print" -> Some print
  | "igt" -> Some igt
  | "ige" -> Some ige
  | "ilt" -> Some ilt
  | "ile" -> Some ile
  | "iadd" -> Some iadd
  | "isub" -> Some isub
  | "imul" -> Some imul
  | "idiv" -> Some idiv
  | "imod" -> Some imod
  | "ipow" -> Some ipow
  | _ -> None
;;
