# Local development instructions

- Stay on `cqwhile+distributive` for this development.
- Never push local modifications.
- Use the named `coqq` opam switch, with `ocaml-base-compiler.5.2.0` and the
  dependencies pinned in `coq-mathcomp-quantum.opam`. The repository's `_opam`
  link selects this switch locally.
- Compile changed proofs and their dependencies with `opam exec --switch=coqq --
  dune build`. Do not add admitted proofs or new axioms to discharge program
  correctness obligations.
