  $ for test in ok/*.1ml; do \
  >   echo ": $test"; \
  >   1ml --f-omega --prelude ./prelude.1ml "$test"; \
  > done
  : ok/001-empty.1ml
  : ok/002-syntax.1ml
  : ok/003-bindings.1ml
  : ok/004-expressions.1ml
  : ok/005-infer.1ml
  : ok/006-subtyping.1ml
  : ok/007-implicit.1ml
  : ok/008-with.1ml
  : ok/009-multiple-types.1ml
  : ok/010.1ml
