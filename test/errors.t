  $ cat > prelude.1ml <<'EOF'
  > type unit = extern "unit";
  > type bool = extern "bool";
  > type int = extern "int";
  > type string = extern "string";
  > 
  > true = extern "Bool.true" : bool;
  > false = extern "Bool.false" : bool;
  > 
  > Assert = {
  >   ok = extern "Assert.ok" : bool -> unit;
  >   eq 'a (x : a) (y : a) = (extern "Assert.eq" : a -> a -> unit) x y;
  > }
  > EOF

  $ 1ml nonexistent.1ml
  Error: Could not open file `nonexistent.1ml'
    Sys error: nonexistent.1ml: No such file or directory
  [1]

  $ echo '' | 1ml --prelude nonexistent.1ml -
  Error: Could not open file `nonexistent.1ml'
    Sys error: nonexistent.1ml: No such file or directory
  [1]

  $ echo 'x = ;' | 1ml -
  File "<stdin>", line 1, character 5:
  Error: unexpected char '\001'
    Syntax error
  [1]

  $ echo 'x = "\q";' | 1ml -
  File "<stdin>", line 1, characters 6-7:
  Error: invalid escape sequence 'q'
    Syntax error
  [1]

  $ echo 'x = "abc' | 1ml -
  File "<stdin>", line 1, character 9:
  Error: unterminated string
    Syntax error
  [1]

  $ echo '(*' | 1ml -
  File "<stdin>", line 2, character 0:
  Error: unterminated comment
    Syntax error
  [1]

  $ echo 'x =' | 1ml -
  File "<stdin>", line 2, character 0:
  Error: parse error
  [1]

  $ echo 'type x a b c;' | 1ml -
  File "<stdin>", line 1, character 13:
  Error: parse error
  [1]

  $ echo 'type t = extern "unknown"' | 1ml -
  File "<stdin>", line 1, characters 10-25:
  Error: unknown external type `unknown'
  [1]

  $ echo 'x = extern "unknown": unit' | 1ml -
  File "<stdin>", line 1, characters 23-26:
  Error: unbound variable `unit'
  [1]

  $ echo 'x = foo' | 1ml -
  File "<stdin>", line 1, characters 5-7:
  Error: unbound variable `foo'
  [1]

  $ echo 'x: t = ()' | 1ml -
  File "<stdin>", line 1, character 4:
  Error: unbound variable `t'
  [1]

  $ echo 'x = {}.x' | 1ml -
  File "<stdin>", line 1, character 8:
  Error: record is missing field `x'
  [1]

  $ echo 'x = ().x' | 1ml -
  File "<stdin>", line 1, characters 5-6:
  Error: expected a record type, but got `unit'
  [1]

  $ echo 'x = () ()' | 1ml -
  File "<stdin>", line 1, characters 5-6:
  Error: expected a function type, but got `unit'
  [1]

  $ echo 'x = unwrap (): ()' | 1ml -
  File "<stdin>", line 1, characters 16-17:
  Error: expected a wrapped type, but got `unit'
  [1]

  $ echo 't = (); x: t = ()' | 1ml -
  File "<stdin>", line 1, character 12:
  Error: expected a singleton type, but got `unit'
  [1]

  $ echo 'x: (Assert.ok true) = ()' | 1ml --prelude prelude.1ml -
  Error: expected a pure expression
  [1]

  $ echo 'x = if () then () else ()' | 1ml -
  File "<stdin>", line 1, characters 8-9:
  Error: expected a boolean, but got `unit'
  [1]

  $ echo 'x: int = ()' | 1ml --prelude prelude.1ml -
  File "<stdin>", line 1, characters 10-11:
  Error: type `unit' is not assignable to `int'
  [1]

  $ echo 'f (x: {}): { a: () } = x;' | 1ml -
  File "<stdin>", line 1, characters 7-8:
  Error: type `{ }' is not assignable to `{ a: unit }'
    record is missing field `a'
  [1]

  $ echo 'f (x: { a: unit }): { a: int } = x' | 1ml --prelude prelude.1ml -
  File "<stdin>", line 1, characters 7-17:
  Error: type `{ a: unit }' is not assignable to `{ a: int }'
    in record field `a':
    type `unit' is not assignable to `int'
  [1]

  $ echo 'f (x: unit -> unit): int -> unit = x' | 1ml --prelude prelude.1ml -
  File "<stdin>", line 1, characters 7-18:
  Error: type `unit -> unit' is not assignable to `int -> unit'
    in function argument:
    type `int' is not assignable to `unit'
  [1]

  $ echo 'f (x: unit -> unit): unit -> int = x' | 1ml --prelude prelude.1ml -
  File "<stdin>", line 1, characters 7-18:
  Error: type `unit -> unit' is not assignable to `unit -> int'
    in function return:
    type `unit' is not assignable to `int'
  [1]

  $ echo 'f (x: (= type unit)): (= type int) = x' | 1ml --prelude prelude.1ml -
  File "<stdin>", line 1, characters 7-19:
  Error: type `(= type unit)' is not assignable to `(= type int)'
    in singleton type:
    type `unit' is not assignable to `int'
  [1]

  $ echo 'f (x: wrap unit): wrap int = x' | 1ml --prelude prelude.1ml -
  File "<stdin>", line 1, characters 7-15:
  Error: type `wrap unit' is not assignable to `wrap int'
    in wrapped type:
    type `unit' is not assignable to `int'
  [1]

  $ echo 'f x = x x' | 1ml -
  Error: type `_' is not assignable to `(a: _) -> _'
  [1]

  $ echo 'type pair a b = { fst: a; snd: b }; type Ti = type; U = pair Ti Ti' | 1ml -
  File "<stdin>", line 1, characters 47-50:
  Error: type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ echo 'type Ti = type; A = (type Ti): type' | 1ml -
  File "<stdin>", line 1, characters 22-28:
  Error: type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ echo 'type Ti = type; B = { type u = Ti } :> { type u }' | 1ml -
  File "<stdin>", line 1, characters 21-35:
  Error: type `{ u: (= type type) }' is not assignable to `{ u: type }'
    in record field `u':
    type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ echo 'type Ti = type; C = if true then Ti else int: type;' | 1ml --prelude prelude.1ml -
  File "<stdin>", line 1, characters 11-14:
  Error: type `(= type type)' is not assignable to `type'
    in singleton type:
    type `(= type <abstr>)' is not assignable to `<abstr>'
  [1]

  $ echo 'G = (fun (a: type) => type { x : a }) :> type -> type; J = G :> type => type;' | 1ml -
  File "<stdin>", line 1, characters 42-53:
  Error: type `type -> type' is not assignable to `type => type'
  [1]

  $ echo 'do Assert.eq 1 2;' | 1ml --prelude prelude.1ml -
  Error: expected 1, but got 2
  [1]
