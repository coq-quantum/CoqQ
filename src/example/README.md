# Quantum program examples

The examples share the existing `quantum` Dune theory and the `rocq.9.1`
toolchain. Build all examples from the repository root:

```sh
opam exec --switch=rocq.9.1 -- dune build
```

| Directory | Development |
| --- | --- |
| [classical](classical/README.md) | Classical–quantum programs, semantics, Hoare logic, and algorithms |
| [distributive](distributive/README.md) | Distributed programs, concurrency, Hoare logic, and protocols |
| `veri_QEC` | Existing classical–quantum while language and error-correction examples |
| `coqq_paper` | The original CoqQ paper's quantum while language, Hoare rules, and examples |
| `qlaws` | Quantum programming laws, circuits, nondeterminism, and recursion |
| `refinement` | Quantum program refinement |
| `diracdec` | Typed Dirac notation and its semantic laws |

The last four directories were imported from
[`coq-quantum/CoqQ` main at `b169ea4`](https://github.com/coq-quantum/CoqQ/commit/b169ea462b13d20b05e03615ad1d56cc8d8f5784).
Their imports, notations, and proof scripts are adapted to the versions in
`coq-mathcomp-quantum.opam`. The upstream [MIT license](UPSTREAM-LICENSE) is
preserved. These examples use the workspace's existing foundations; the
upstream versions of those foundations were not imported over them.

## Compatibility changes

The imported proofs use the existing `quantum.compat` algebra imports,
`mathcomp.reals`, and `sesquilinear` APIs. Proof scripts select the intended
sums explicitly where the newer rewriting matcher chooses a nested sum.
The Dirac demonstration uses `.@[` for substitution to avoid a parser
collision. These adaptations preserve the imported theorem statements and
use the existing complex-scalar and operator-composition conventions.
