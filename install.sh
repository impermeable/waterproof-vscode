#! /usr/bin/bash

# Speed up compilation later
export MAKEFLAGS='-j 10'

# Install OCaml
opam init
eval $(opam env)
opam switch create waterproof --packages coq.8.17.0
$ eval $(opam env --switch=waterproof)

# Install coq-lsp
opam install coq-lsp -y
