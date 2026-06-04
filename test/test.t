
  $ 1ml --f-omega files/00-basic/001-empty.1ml
  $ 1ml --f-omega files/00-basic/002-syntax.1ml
  $ 1ml --f-omega files/00-basic/003-bindings.1ml
  $ 1ml --f-omega files/00-basic/004-expressions.1ml
  $ 1ml --f-omega files/00-basic/005-infer.1ml
  $ 1ml --f-omega files/00-basic/006-subtyping.1ml
  $ 1ml --f-omega files/00-basic/007-implicit.1ml
  $ 1ml --f-omega files/00-basic/008-with.1ml
  $ 1ml --f-omega files/00-basic/009-multiple-types.1ml
  $ 1ml --f-omega files/00-basic/010-higher-kinded.1ml

  $ 1ml --f-omega files/01-examples/001-typeof.1ml
  $ 1ml --f-omega files/01-examples/002-detached-type.1ml
  $ 1ml --f-omega files/01-examples/003-type-manipulation.1ml

(russo.1ml is omitted, uses too many unsupported features)
  $ 1ml --f-omega --prelude files/02-rossberg/prelude.1ml files/02-rossberg/paper.1ml
  $ 1ml --f-omega --prelude files/02-rossberg/prelude.1ml files/02-rossberg/talk.1ml
  $ 1ml --f-omega --no-prelude files/02-rossberg/prelude.1ml
  $ 1ml --f-omega --no-prelude files/02-rossberg/test.1ml
  Bool
  Toplevel
  Int
  Char
  Text
  Opt
  Alt
  List
  Set
  Map
  Tests
  true

  $ 1ml files/00-basic/001-empty.1ml
  $ 1ml files/00-basic/002-syntax.1ml
  $ 1ml files/00-basic/003-bindings.1ml
  $ 1ml files/00-basic/004-expressions.1ml
  $ 1ml files/00-basic/005-infer.1ml
  $ 1ml files/00-basic/006-subtyping.1ml
  $ 1ml files/00-basic/007-implicit.1ml
  $ 1ml files/00-basic/008-with.1ml
  $ 1ml files/00-basic/009-multiple-types.1ml
  $ 1ml files/00-basic/010-higher-kinded.1ml

  $ 1ml files/01-examples/001-typeof.1ml
  $ 1ml files/01-examples/002-detached-type.1ml
  $ 1ml files/01-examples/003-type-manipulation.1ml

  $ 1ml --prelude files/02-rossberg/prelude.1ml files/02-rossberg/paper.1ml
  $ 1ml --prelude files/02-rossberg/prelude.1ml files/02-rossberg/talk.1ml
  $ 1ml --no-prelude files/02-rossberg/prelude.1ml
  $ 1ml --no-prelude files/02-rossberg/test.1ml
  Bool
  Toplevel
  Int
  Char
  Text
  Opt
  Alt
  List
  Set
  Map
  Tests
  true
