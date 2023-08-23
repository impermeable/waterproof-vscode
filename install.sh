#! /usr/bin/bash

# Add the repository to get opam from and install it
add-apt-repository ppa:avsm/ppa
apt update
apt install opam

# Speed up compilation later
export MAKEFLAGS='-j 10'

# Install OCaml
opam switch create waterproof --packages coq.8.17.0
$ eval $(opam env --switch=waterproof)

# Install coq-lsp
opam install coq-lsp -y
