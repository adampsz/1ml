# 1ml

A 1ML implementation in OCaml.

## Requirements

- OCaml (recommended via opam)
- dune

## Setup

```sh
opam switch create .
eval "$(opam env)"
opam install . --deps-only
```

## Build and install

```sh
dune build
dune install
```

## Quick start

```sh
$ 1ml --help
Usage: 1ml [options] [file...]

  --repl     Start interactive repl
  --prelude  Configure prelude file
  --f-omega  Elaborate to F-omega and then evaluate
  ...

$ 1ml --repl # or just 1ml
1ml> "hello, world!"
 : string = "hello, world!"
1ml> ^D

$ 1ml program.1ml
$ 1ml - < ./program.1ml
$ 1ml --prelude prelude.1ml program.1ml
```

## Project layout

- `bin/` - CLI entrypoint, argument parsing, and REPL
- `lib/` - core implementation
  - `Syntax/` - lexer/parser
  - `Lang/` - surface (high-level), typed (mid-level), and F-omega (low-level) language representations
  - `Typecheck.ml` - type checking
  - `Elaborate.ml` - elaboration from typed lang to F-omega
  - `Eval.ml` - evaluator and runtime
  - `Pretty.ml` - type pretty-printing
