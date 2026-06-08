(lang dune 3.17)

(name 1ml)

(package
 (name 1ml)
 (version 0.0.0-dev)
 (license MIT)
 (source
  (github adampsz/1ml))
 (depends
  logs
  (menhir :build)
  (ppx_deriving :build)
  (bisect_ppx :dev)))

(using menhir 3.0)

(generate_opam_files true)
