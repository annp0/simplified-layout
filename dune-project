(lang dune 3.0)
(generate_opam_files true)
(name layouts)
(authors "Nan An")
(maintainers "annaneuorg@gmail.com")
(source (github annp0/simplified-layout))

(package
 (name layouts)
 (synopsis "A simplified layout algebra for GPU kernels")
 (depends ocaml dune base stdio sexplib0 ppx_jane))
