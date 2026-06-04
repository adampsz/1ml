  $ ./deps/pp.exe "int"
  int
  $ ./deps/pp.exe "bool"
  bool
  $ ./deps/pp.exe "string"
  string
  $ ./deps/pp.exe "unit"
  unit
  $ ./deps/pp.exe "float"
  float
  $ ./deps/pp.exe "char"
  char

  $ ./deps/pp.exe "_"
  _

  $ ./deps/pp.exe "int -> bool"
  int -> bool
  $ ./deps/pp.exe "int -> bool -> unit"
  int -> bool -> unit
  $ ./deps/pp.exe "int => bool"
  int => bool
  $ ./deps/pp.exe "(x: int) -> bool"
  (x: int) -> bool
  $ ./deps/pp.exe "(x: int) => bool"
  (x: int) => bool
  $ ./deps/pp.exe "(int -> bool) -> unit"
  (int -> bool) -> unit

  $ ./deps/pp.exe "'a => a -> a"
  '(a: type) => a -> a
  $ ./deps/pp.exe "'a => 'b => a -> b -> a"
  '(a: type) => '(b: type) => a -> b -> a
  $ ./deps/pp.exe "'a => opt a -> a"
  '(a: type) => opt a -> a

  $ ./deps/pp.exe "(int, bool)"
  (int, bool)
  $ ./deps/pp.exe "(int, bool, unit)"
  (int, bool, unit)
  $ ./deps/pp.exe "(int, (bool, unit))"
  (int, (bool, unit))
  $ ./deps/pp.exe "opt (int, bool)"
  opt (int, bool)

  $ ./deps/pp.exe "{}"
  { }
  $ ./deps/pp.exe "{ x: int; y: bool }"
  { x: int; y: bool }
  $ ./deps/pp.exe "{ x: int; y: (int, bool) }"
  { x: int; y: (int, bool) }
  $ ./deps/pp.exe "{ type t; v: t }"
  { t: type; v: t }
  $ ./deps/pp.exe "{ type key; v: key }"
  { key: type; v: key }

  $ ./deps/pp.exe "opt int"
  opt int
  $ ./deps/pp.exe "opt (opt int)"
  opt (opt int)
  $ ./deps/pp.exe "opt (int -> bool)"
  opt (int -> bool)
  $ ./deps/pp.exe "alt int bool"
  alt int bool
  $ ./deps/pp.exe "alt (opt int) (opt bool)"
  alt (opt int) (opt bool)

  $ ./deps/pp.exe "{ opt: unit; x: Opt.t int }"
  { opt: unit; x: Opt.t int }

  $ ./deps/pp.exe "wrap int"
  wrap int
  $ ./deps/pp.exe "wrap (int -> int)"
  wrap (int -> int)
  $ ./deps/pp.exe "wrap (opt int)"
  wrap (opt int)

  $ ./deps/pp.exe "{ type optint = opt int; x: opt int }"
  { optint: (= type opt int); x: optint }
  $ ./deps/pp.exe "type"
  type
  $ ./deps/pp.exe "(= type { type key; type map a; empty 'a: map a })"
  (= type { key: type; map: (a: type) => type; empty: '(a: type) => map a })
  $ ./deps/pp.exe "{ t: type; u: (= type t); x: t; M: { u: (); y: t } }"
  { t: type; u: (= type t); x: u; M: { u: unit; y: t } }
