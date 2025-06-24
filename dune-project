(lang dune 3.17)

(package
 (name 1ml)
 (version 0.0.0-dev)
 (license MIT)
 (source
  (github adampsz/1ml))
 (depends fmt logs))

(using menhir 3.0)

(generate_opam_files true)
