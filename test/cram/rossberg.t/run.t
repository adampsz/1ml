  $ 1ml --f-omega ./test.1ml
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
  

  $ 1ml --prelude ./prelude.1ml --f-omega ./paper.1ml
  Fatal error: exception Failure("unbound type variable: %10402")
  [2]

  $ 1ml --prelude ./prelude.1ml  --f-omega ./talk.1ml
  Fatal error: exception Failure("unbound type variable: %10332")
  [2]
