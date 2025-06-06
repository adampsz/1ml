open FOmega
open Value

let panic = function
  | VPrim (ConstString s) -> failwith (Printf.sprintf "Program panicked: %s" s)
  | _ -> failwith "Program panicked: unknown error"
;;

let print = function
  | VPrim (ConstString x) -> VPrim (ConstUnit (Format.printf "%s\n%!" x))
  | x -> VPrim (ConstUnit (Format.printf "%a\n%!" PP.pp_value x))
;;

let iadd x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x + y))
  | _, _ -> assert false
;;

let isub x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x - y))
  | _, _ -> assert false
;;

let imul x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x * y))
  | _, _ -> assert false
;;

let idiv x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x mod y))
  | _, _ -> assert false
;;

let imod x y =
  match x, y with
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (x mod y))
  | _, _ -> assert false
;;

let ipow x y =
  let rec aux acc b = function
    | 0 -> acc
    | e when e land 1 = 0 -> aux acc (b * b) (e lsr 1)
    | e -> aux (b * acc) (b * b) (e lsr 1)
  in
  match x, y with
  | VPrim (ConstInt _), VPrim (ConstInt y) when y < 0 -> failwith "Negative exponent"
  | VPrim (ConstInt x), VPrim (ConstInt y) -> VPrim (ConstInt (aux 1 x y))
  | _, _ -> assert false
;;

let pure f v = VRecord [ "%p", f v ]
let impure f v = VRecord [ "%i", f v ]
let unary f = VExternal f
let unary_pure f = VExternal (pure f)
let unary_impure f = VExternal (impure f)
let binary f = VExternal (fun x -> VExternal (f x))
let binary_pure f = VExternal (pure (fun x -> VExternal (pure (f x))))
let binary_impure f = VExternal (impure (fun x -> VExternal (impure (f x))))

let builtin = function
  | "panic" -> Some (unary_impure panic)
  | "print" -> Some (unary_impure print)
  | "iadd" -> Some (binary_pure iadd)
  | "isub" -> Some (binary_pure isub)
  | "imul" -> Some (binary_pure imul)
  | "idiv" -> Some (binary_pure idiv)
  | "imod" -> Some (binary_pure imod)
  | "ipow" -> Some (binary_pure ipow)
  | _ -> None
;;
