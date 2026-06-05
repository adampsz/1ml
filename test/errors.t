  $ 1ml nonexistent.1ml
  Error: Could not open file `nonexistent.1ml'
    Sys error: nonexistent.1ml: No such file or directory
  [1]

  $ 1ml --prelude nonexistent.1ml <<- 'EOF'
  > EOF
  Error: Could not open file `nonexistent.1ml'
    Sys error: nonexistent.1ml: No such file or directory
  [1]

  $ 1ml - <<- 'EOF'
  >   x = ;
  > EOF
  File "<stdin>", line 1, character 7:
  Error: unexpected char '\001'
    Syntax error
  [1]

  $ 1ml - <<- 'EOF'
  >   x = "\?";
  > EOF
  File "<stdin>", line 1, characters 8-9:
  Error: invalid escape sequence '?'
    Syntax error
  [1]

  $ 1ml - <<- 'EOF'
  >   x = "abc
  > EOF
  File "<stdin>", line 1, character 11:
  Error: unterminated string
    Syntax error
  [1]

  $ 1ml - <<- 'EOF'
  >   (* comment
  > EOF
  File "<stdin>", line 2, character 0:
  Error: unterminated comment
    Syntax error
  [1]

  $ 1ml - <<- 'EOF'
  >   x =
  > EOF
  File "<stdin>", line 2, character 0:
  Error: parse error
  [1]

  $ 1ml - <<- 'EOF'
  >   type x a b c;
  > EOF
  File "<stdin>", line 1, character 15:
  Error: parse error
  [1]

  $ 1ml - <<- 'EOF'
  >   type t = extern "unknown";
  > EOF
  File "<stdin>", line 1, characters 12-27:
  Error: unknown external type `unknown'
  [1]

  $ 1ml - <<- 'EOF'
  >   x = extern "unknown": unit;
  > EOF
  Error: undefined external symbol `unknown'
  [1]

  $ 1ml - <<- 'EOF'
  >   x = foo;
  > EOF
  File "<stdin>", line 1, characters 7-9:
  Error: unbound variable `foo'
  [1]

  $ 1ml - <<- 'EOF'
  >   x: t = ();
  > EOF
  File "<stdin>", line 1, character 6:
  Error: unbound variable `t'
  [1]

  $ 1ml - <<- 'EOF'
  >   x = {}.x;
  > EOF
  File "<stdin>", line 1, character 10:
  Error: record is missing field `x'
  [1]

  $ 1ml - <<- 'EOF'
  >   x = ().x;
  > EOF
  File "<stdin>", line 1, characters 7-8:
  Error: expected a record type, but got `unit'
  [1]

  $ 1ml - <<- 'EOF'
  >   x = () ();
  > EOF
  File "<stdin>", line 1, characters 7-8:
  Error: expected a function type, but got `unit'
  [1]

  $ 1ml - <<- 'EOF'
  >   x = unwrap (): ();
  > EOF
  File "<stdin>", line 1, characters 18-19:
  Error: expected a wrapped type, but got `unit'
  [1]

  $ 1ml - <<- 'EOF'
  >   t = ();
  >   x: t = ();
  > EOF
  File "<stdin>", line 2, character 6:
  Error: expected a singleton type, but got `unit'
  [1]

  $ 1ml - <<- 'EOF'
  >   x: (Assert.ok true) = ();
  > EOF
  Error: expected a pure expression
  [1]

  $ 1ml - <<- 'EOF'
  >   x = if () then () else ();
  > EOF
  File "<stdin>", line 1, characters 10-11:
  Error: expected a boolean, but got `unit'
  [1]

  $ 1ml - <<- 'EOF'
  >   x: int = ();
  > EOF
  File "<stdin>", line 1, characters 12-13:
  Error: type `unit' is not assignable to `int'
  [1]

  $ 1ml - <<- 'EOF'
  >   f (x: {}): { a: () } = x;
  > EOF
  File "<stdin>", line 1, characters 9-10:
  Error: type `{ }' is not assignable to `{ a: unit }'
    record is missing field `a'
  [1]

  $ 1ml - <<- 'EOF'
  >   f (x: { a: unit }): { a: int } = x;
  > EOF
  File "<stdin>", line 1, characters 9-19:
  Error: type `{ a: unit }' is not assignable to `{ a: int }'
    in record field `a':
    type `unit' is not assignable to `int'
  [1]

  $ 1ml - <<- 'EOF'
  >   f (x: unit -> unit): int -> unit = x;
  > EOF
  File "<stdin>", line 1, characters 9-20:
  Error: type `unit -> unit' is not assignable to `int -> unit'
    in function argument:
    type `int' is not assignable to `unit'
  [1]

  $ 1ml - <<- 'EOF'
  >   f (x: unit -> unit): unit -> int = x;
  > EOF
  File "<stdin>", line 1, characters 9-20:
  Error: type `unit -> unit' is not assignable to `unit -> int'
    in function return:
    type `unit' is not assignable to `int'
  [1]

  $ 1ml - <<- 'EOF'
  >   f (x: (= type unit)): (= type int) = x;
  > EOF
  File "<stdin>", line 1, characters 9-21:
  Error: type `(= type unit)' is not assignable to `(= type int)'
    in singleton type:
    type `unit' is not assignable to `int'
  [1]

  $ 1ml - <<- 'EOF'
  >   f (x: wrap unit): wrap int = x;
  > EOF
  File "<stdin>", line 1, characters 9-17:
  Error: type `wrap unit' is not assignable to `wrap int'
    in wrapped type:
    type `unit' is not assignable to `int'
  [1]

  $ 1ml - <<- 'EOF'
  >   f x = x x;
  > EOF
  Error: type `_' is not assignable to `(a: _) -> _'
  [1]

  $ 1ml - <<- 'EOF'
  >   type pair a b = { fst: a; snd: b };
  >   type Ti = type;
  >   U = pair Ti Ti;
  > EOF
  File "<stdin>", line 2, characters 13-16:
  Error: type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ 1ml - <<- 'EOF'
  >   type Ti = type;
  >   A: type = type Ti;
  > EOF
  File "<stdin>", line 2, characters 13-19:
  Error: type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ 1ml - <<- 'EOF'
  >   type Ti = type;
  >   B = { type u = Ti } :> { type u };
  > EOF
  File "<stdin>", line 2, characters 7-21:
  Error: type `{ u: (= type type) }' is not assignable to `{ u: type }'
    in record field `u':
    type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ 1ml - <<- 'EOF'
  >   type Ti = type;
  >   C = if true then Ti else int: type;
  > EOF
  File "<stdin>", line 1, characters 13-16:
  Error: type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ 1ml - <<- 'EOF'
  >   G = (fun (a: type) => type { x : a }) :> type -> type;
  >   J = G :> type => type;
  > EOF
  File "<stdin>", line 1, characters 44-55:
  Error: type `type -> type' is not assignable to `type => type'
  [1]

  $ 1ml - <<- 'EOF'
  >   do Assert.eq 1 2;
  > EOF
  Error: expected 1, but got 2
  [1]

  $ 1ml - <<- 'EOF'
  >   id: 'a => a -> a = fun x => x;
  >   G (x: int) = { M = { type t = int; v = x } :> { type t; v: t }; f = id id };
  >   C = G 3;
  >   x = C.f (C.M.v);
  > EOF
  Error: type `_' is not assignable to `C.M.t'
  [1]

  $ 1ml - <<- 'EOF'
  >   id: 'a => a -> a = fun x => x;
  >   G (x: int) = { M = { type t = int; v = x } :> { type t; v: t }; f = id id };
  >   C = G 3;
  >   C' = G 3;
  >   x = C.f (C'.M.v);
  > EOF
  Error: type `_' is not assignable to `C'.M.t'
  [1]
