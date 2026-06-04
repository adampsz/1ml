  $ run() {
  >   for file in */*.1ml; do
  >     echo ": $file"
  >     ../deps/runner.exe 1ml "$@" "$file"
  >   done
  > }

  $ run --f-omega
  : 00-basic/001-empty.1ml
  : 00-basic/002-syntax.1ml
  : 00-basic/003-bindings.1ml
  : 00-basic/004-expressions.1ml
  : 00-basic/005-infer.1ml
  : 00-basic/006-subtyping.1ml
  : 00-basic/007-implicit.1ml
  : 00-basic/008-with.1ml
  : 00-basic/009-multiple-types.1ml
  : 00-basic/010-higher-kinded.1ml
  : 01-examples/001-typeof.1ml
  : 01-examples/002-detached-type.1ml
  : 01-examples/003-type-manipulation.1ml
  : 02-rossberg/paper.1ml
  : 02-rossberg/prelude.1ml
  : 02-rossberg/russo.1ml
  : 02-rossberg/talk.1ml
  : 02-rossberg/test.1ml
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

  $ run
  : 00-basic/001-empty.1ml
  : 00-basic/002-syntax.1ml
  : 00-basic/003-bindings.1ml
  : 00-basic/004-expressions.1ml
  : 00-basic/005-infer.1ml
  : 00-basic/006-subtyping.1ml
  : 00-basic/007-implicit.1ml
  : 00-basic/008-with.1ml
  : 00-basic/009-multiple-types.1ml
  : 00-basic/010-higher-kinded.1ml
  : 01-examples/001-typeof.1ml
  : 01-examples/002-detached-type.1ml
  : 01-examples/003-type-manipulation.1ml
  : 02-rossberg/paper.1ml
  : 02-rossberg/prelude.1ml
  : 02-rossberg/russo.1ml
  : 02-rossberg/talk.1ml
  : 02-rossberg/test.1ml
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
