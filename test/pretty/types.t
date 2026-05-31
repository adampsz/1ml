  $ ./pp.exe "int"
  int
  $ ./pp.exe "bool"
  bool
  $ ./pp.exe "string"
  string
  $ ./pp.exe "unit"
  unit
  $ ./pp.exe "float"
  float
  $ ./pp.exe "char"
  char

  $ ./pp.exe "_"
  _

  $ ./pp.exe "int -> bool"
  int -> bool
  $ ./pp.exe "int -> bool -> string"
  int -> bool -> string
  $ ./pp.exe "int => bool"
  int => bool
  $ ./pp.exe "(x: int) -> bool"
  (x: int) -> bool
  $ ./pp.exe "(x: int) => bool"
  (x: int) => bool
  $ ./pp.exe "(int -> bool) -> string"
  (int -> bool) -> string

  $ ./pp.exe "'a => a -> a"
  '(a: type) => a -> a
  $ ./pp.exe "'a => 'b => a -> b -> a"
  '(a: type) => '(b: type) => a -> b -> a
  $ ./pp.exe "'a => opt a -> a"
  '(a: type) => opt a -> a

  $ ./pp.exe "(int, bool)"
  (int, bool)
  $ ./pp.exe "(int, bool, string)"
  (int, bool, string)
  $ ./pp.exe "(int, (bool, string))"
  (int, (bool, string))
  $ ./pp.exe "opt (int, bool)"
  opt (int, bool)

  $ ./pp.exe "{}"
  { }
  $ ./pp.exe "{ x: int; y: bool }"
  { x: int; y: bool }
  $ ./pp.exe "{ x: int; y: (int, bool) }"
  { x: int; y: (int, bool) }
  $ ./pp.exe "{ type t; v: t }"
  { t: type; v: t }
  $ ./pp.exe "{ type key; v: key }"
  { key: type; v: key }

  $ ./pp.exe "opt int"
  opt int
  $ ./pp.exe "opt (opt int)"
  opt (opt int)
  $ ./pp.exe "opt (int -> bool)"
  opt (int -> bool)
  $ ./pp.exe "alt int bool"
  alt int bool
  $ ./pp.exe "alt (opt int) (opt bool)"
  alt (opt int) (opt bool)

  $ ./pp.exe "M.t"
  M.t
  $ ./pp.exe "M.f int"
  M.f int
  $ ./pp.exe "{ opt: unit; x: Opt.t int }"
  { opt: unit; x: #opt int }

  $ ./pp.exe "wrap int"
  wrap int
  $ ./pp.exe "wrap (int -> int)"
  wrap (int -> int)
  $ ./pp.exe "wrap (opt int)"
  wrap (opt int)

  $ ./pp.exe "{ type optint = opt int; x: opt int }"
  { optint: (= type opt int); x: optint }
  $ ./pp.exe "{ type MAP = { type key; type map a; empty 'a: map a } }"
  {
    MAP:
      (= type { key: type; map: (a: type) => type; empty: '(a: type) => map a }
      );
  }
  $ ./pp.exe "type"
  type
