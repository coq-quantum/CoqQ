# Classical and distributed quantum programs

These developments formalize `classical.pdf` and `distributive.pdf` using the
existing CoqQ foundations. The dependency direction is classical foundations
→ distributed programs. The original `../veri_QEC/cqwhile.v` is preserved.
The current theorem maps are [classical coverage](COVERAGE.md) and
[distributed coverage](../distributive/COVERAGE.md); outstanding results are
listed explicitly there.

## Language and semantics

`language.v` reuses cqwhile's classical types, typed expressions, classical
memory, register expressions, and finite-output quantum measurement type.
Measurements may depend on classical expressions. Arbitrary-support random
assignment and unbounded loops use the existing summability and limit APIs.
`operational.v` proves correspondence between terminating operational routes
and the compositional denotation of the new language.

`memory_interpretation.v` and `memory_steps.v` additionally interpret the
same primitives and small-step rules in independent finite quantum memories.
They use an explicit unitary identification of the source footprint and
allow arbitrary entangled target inputs. Their scope is primitive and
one-step replay; full-program transport is recorded separately in coverage.

`state.v`, `kernel.v`, and `mixture.v` provide positive summable cq-states,
state-transformer kernels, probability mixtures, and countable increasing
limits. `assertion.v` retains the paper's countable-image/definable-fiber
assertions as a distinguished subclass. The complete semantic domain consists
of all effect-valued functions, as approved after the counterexample to the
paper's claimed closure under limits.

## Proof rules and examples

`rules.v` defines independent inductive total- and partial-correctness rules
and proves soundness and relative completeness for the core classical
language. Predicate-transformer, expectation, and loop-ranking modules supply
the semantic arguments. The auxiliary modules cover consequence, assertion
algebra, invariant framing, existential elimination, signed integer rankings
with a fresh ghost, and quantum operations on disjoint registers. Consult the
coverage record for the precise side conditions of the checked auxiliary rules.
`ranking_complement.v` also proves Lemma 5.4 and derives WhileT′ using
increasing assertions and partial-correctness premises.

The actual Grover, Fourier, and phase-estimation programs have checked
execution and Hoare theorems. Phase estimation includes its exact Born
probabilities and certainty for representable phases. The actual order-finding program also has a checked exact Fourier/Born
outcome formula. Its modular-orbit Fourier eigenstates, orthonormality,
eigenvalues, and reconstruction of the initialized basis-one state are
checked explicitly. Its literal printed postprocessor is proved unable to
return any order above two. The literal Shor wrapper has partial factor
safety and a total lower bound from its immediate gcd branch. The paper's
general phase-error bound and order-finding success claims have documented
Rocq-checked counterexamples. The modular-unit counting lemma and its conditional-probability form for the
actual sampler are also checked, independently of that faulty postprocessor.

The distributed development reuses the classical language. Its modules define
private processes, rendezvous, probabilistic steps, successful computation
results, concrete commutation and diamonds, scheduler-independent limits,
and independent guarded/network inference rules. Operational execution is
proved equal to the shared-language serialization. Both proof systems are
sound and relatively complete for total and partial correctness against their
actual operational limit semantics. Teleportation and remote CNOT have
checked operational correctness theorems, including arbitrary outside memory
and entangled two-qubit inputs for remote CNOT.

## Mathematical arguments and validation

[PROOF_GAPS.md](PROOF_GAPS.md), [HOARE-NOTES.md](HOARE-NOTES.md),
[CASE-STUDIES.md](CASE-STUDIES.md), and the distributed notes record the
natural-language arguments and paper corrections. The semantic assertion
domain extension was approved on 2026-10-03. Other substantive changes are
identified individually; false paper claims are not silently assumed.

[VALIDATION.md](VALIDATION.md) records validation boundaries and inherited
assumptions. [REFERENCE.md](REFERENCE.md) records the pinned upstream revision,
proof patterns, and preserved MIT license.

Build from the repository root:

```sh
opam exec --switch=rocq.9.1 -- dune build
```

The existing qualified `quantum` Dune theory discovers both directories.
For incremental compilation, append the desired `.vo` targets. Do not edit
generated `_build` files or run simultaneous Dune builds.
