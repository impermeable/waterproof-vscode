#! /usr/bin/bash

# Speed up compilation later
export MAKEFLAGS='-j 10'

# Install OCaml
opam init --disable-sandboxing --bare
opam switch create 4.14.1+options waterproof
$ eval $(opam env --switch=waterproof)

# Install coq-lsp
opam install coq-lsp -y
