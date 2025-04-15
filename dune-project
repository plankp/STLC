(lang dune 3.17)

(name stlc)

(generate_opam_files true)

(source
 (github plankp/STLC))

(authors "Paul Teng")

(maintainers "plankp@outlook.com")

(package
 (name stlc)
 (depends ocaml dune menhir js_of_ocaml coq))

(using menhir 2.1)
(using coq 0.8)

