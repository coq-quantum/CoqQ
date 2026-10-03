# Distributed classical-quantum programs

This development formalizes the distributed paper using the shared
[classical language](../classical/language.v), which reuses cqwhile types,
expressions and finite-output measurement expressions. The original
`../veri_QEC/cqwhile.v` is preserved.

`language.v` defines guarded processes and private ownership; `operational.v`
defines probabilistic local steps and synchronized rendezvous. The concrete
commutation, diamond and convergence proofs establish a unique successful
output independent of the scheduler. `correspondence.v` proves that this
operational denotation equals the shared-language serialization.

`memory_replay.v` gives independent Table-1 transitions in arbitrary finite
target tensor memories. A proved unitary interpretation of each primitive
supports replay of the same local instrument, with probability conservation
and normalized branch outputs, including entangled target inputs. This
layer covers one-step replay; its precise scope is in the coverage record.

`guarded_rules.v` and `network_rules.v` define independent inference systems.
`local_hoare.v` proves guarded soundness and completeness against local
completion limits. `operational_hoare.v`, `partial_completeness.v` and
`total_completeness.v` prove network soundness and relative completeness for
arbitrary cq-input states in both correctness modes. Total completeness uses
a constructed ranking from finite operational horizons; it assumes neither
a runtime bound nor the existence of a ranking.
`ranking_complement.v` proves the increasing-assertion characterization and
derives Rep-T′ and Dist-T′, with their operational soundness corollaries.

`protocol_distributed_correctness.v` proves teleportation and remote-CNOT
correctness for actual distributed executions. `protocol_network_derivations.v`
provides derivations in the network inference system. The protocol proofs
allow arbitrary outside quantum memory; remote CNOT permits entangled input.

[COVERAGE.md](COVERAGE.md) maps the paper to checked results and remaining
obligations. [PROOF_GAPS.md](PROOF_GAPS.md) records the mathematical arguments
and counterexamples. Validation is recorded in
[the shared validation record](../classical/VALIDATION.md). These records,
rather than the existence of a module, determine the claimed coverage.

Build from the repository root with:

```sh
opam exec --switch=rocq.9.1 -- dune build
```
