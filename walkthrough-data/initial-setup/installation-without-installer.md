# Install the required software

```
apt-get install opam
opam init
eval $(opam env)
opam install coq-lsp.0.2.3+9.0
opam install coq-waterproof
```

If vscode cannot detect the installation, set the coq-lsp path to the output of `which coq-lsp`. This can be done
using ctrl+shift+p and selecting "Waterproof: Change Waterproof path".
Alternatively, make sure that the `PATH` available to vscode contains the coq-lsp binary.