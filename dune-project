(lang dune 3.17)

(name stlc)

(generate_opam_files true)

(source
 (github plankp/STLC))

(authors "Paul Teng")

(maintainers "plankp@outlook.com")

(package
 (name stlc)
 (depends
   ocaml dune menhir
   js_of_ocaml js_of_ocaml-ppx
   (coq-core (= 8.20.1))
   (coq-stdlib (= 8.20.1))))

(using menhir 2.1)
(using coq 0.8)

