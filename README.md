# `1ml` prototype

Works:

```sh
dune exec -- 1ml --f-omega ./test/cram/rossberg.t/prelude.1ml
dune exec -- 1ml --f-omega ./test/cram/rossberg.t/test.1ml
```

Doesn't work (yet):

```sh
dune exec -- 1ml --prelude ./test/cram/rossberg.t/prelude.1ml ./test/cram/rossberg.t/paper.1ml
dune exec -- 1ml --prelude ./test/cram/rossberg.t/prelude.1ml ./test/cram/rossberg.t/talk.1ml
```
