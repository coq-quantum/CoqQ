# Exact QSVT in the classical language

The development is in three new files. No pre-existing source, guide, build
configuration, or local modification is changed.

- `qsvt_poly.v`: parity and degree bounds, exact scalar QSP synthesis,
  nonnegative even polynomial completion, and real polynomial phase existence.
- `qsvt_model.v`: certified projected phases, the independent polynomial
  singular-value target, full-column lifting, adjoint reversal and full-row
  support, and explicit failure columns.
- `qsvt.v`: the native command, finite execution of its actual `While`,
  full-memory branch semantics, and total polynomial Hoare correctness.

## Main contract

For every real polynomial `p` and nominal degree `d` satisfying
`QSVTRealPair.admissible d p` (degree at most `d`, parity `d`, and
`|p(x)| <= 1` for `-1 <= x <= 1`),
`QSVTPolynomialCorrectness.qsvt_framework_and_program` chooses one exact phase
function **before** the unitary encoding, logical dimensions, physical
registers, classical variables, input state, or output effect are chosen.
The nominal list contains `d+1` phases, even if the actual degree drops.

For any unitary `U` and input/output isometries `JR, JL`, set
`A = JL^A \o U \o JR`. The target is defined independently of program
execution in `QSVTModel.sv_even` and `sv_odd`:

- even `d`: `F = q(A^A A)`, where `p(X) = q(X^2)`;
- odd `d`: `F = A q(A^A A)`, where `p(X) = X q(X^2)`.

Polynomial evaluation reuses MathComp's `horner_alg` on CoqQ's existing
forward-composition algebra. Even transformation retains `p(0)` on the
entire right kernel, including unpaired right directions of a rectangular
encoding. `QSVTSVD.sv_even_svd` proves equality with the full square right
SVD basis and the polynomial applied to its zero-extended singular values;
`sv_odd_svd` proves equality with the rectangular `U cdiag(p(sigma)) V^A`
formula. These reuse the existing rectangular SVD. `sv_even_kernel` and
`sv_odd_kernel` directly prove the arbitrary-kernel actions `p(0)*v` and
zero. No inverse of a singular value or defect square root is used.

For every output effect `0 <= E <= I`, the primary result is the existing
judgment `CQHoare.derives true Pre qsvt_heralded Post`. With `Jout=JR` in the
even case and `Jout=JL` in the odd case, its explicit assertions are

```
Pre  = Lift(I_ancilla tensor JR F^A E F JR^A)
Post = [counter=d and herald=false] Lift(I_ancilla tensor Jout E Jout^A).
```

They appear immediately after the native program definitions as
`qsvt_polynomial_pre`, `qsvt_polynomial_post`, and
`qsvt_polynomial_contract`. The parity-specific certified targets and proofs
are `QSVTPolynomialCorrectness.even_target`, `odd_target`, `even_correct`,
and `odd_correct`. `even_preE` / `odd_preE` establish **equality** with the
actual weakest precondition; `even_expect` / `odd_expect` therefore give
exact expectation equality for arbitrary cq states. Their assertions are
built from the independent polynomial target, rather than defined by a
weakest-precondition calculation.

The strongest endpoint is `QSVTNativeCompleteness.qsvt_framework_complete`: it
also includes both exact completion-Gram identities with the same witness.
`QSVTNativeStateCorrectness.qsvt_framework_exact` bundles that phase
witness with both source-facing Hoare contracts, all-outcome totality and
mass preservation, exact all-effects expectations, and both encoded density
identities and success masses. The individual state corollaries are
`native_even_success_density`, `native_odd_success_density`,
`native_even_failure_density`, `native_odd_failure_density`, and the two
`native_*_success_mass` theorems in that module.

The phases are exact mathematical reals. Existence is not a numerical phase
compiler, approximation bound, circuit cost analysis, or application-specific
QSVT algorithm.

## Native source correspondence

`QSVTClassicalProgram.qsvt_heralded` constructs an existing
`ClassicalLanguage.command`. The compact definition block is near the start
of `qsvt.v`, before supporting proofs. `qr : wf_qreg (QPair QBool T)` puts the
ancilla first and provides valid, disjoint ancilla/data subregisters.

| Source operation | Definition and native constructor |
| --- | --- |
| Reset ancilla to plus, retain unknown data | `qsvt_apply`, `Initialize qa plus_state` |
| Set private integer counter to zero | `qsvt_core`, `Assign x 0` |
| Apply the input endpoint phase | `right_rotation (phi d)`, `Unitary qr` |
| Loop while counter is below `d` | actual `While (below x d) qsvt_body` |
| Signal at old counter `t` | `signal_at`: `U` for even `t`, `U^A` for odd `t` |
| Increment before choosing the next phase | `Assign x (increment x)` |
| Next projected phase | `rotation_at`: left for odd `t+1`, right otherwise, angle `phi(d-(t+1))` |
| Read herald | Hadamard on ancilla, computational `Measure y`; `false` means success |
| Optional known-data preparation | `qsvt_run`, additional data `Initialize` |

False ancilla sectors use positive phases; true sectors use negative phases.
Signals are shared, so the implementation needs no controlled oracle.
Composition `F \o G` applies `G` first. `expi theta` is `cos theta+i sin theta`,
without the extra pi factor used by `expip`.

Reachable counters are `Posz t` with `0<=t<=d`; totalized `absz` and natural
subtraction therefore introduce no reachable negative-counter or phase-index
underflow case. The loop ends at exactly `d`. The `d=0,1,2` identities are
`coherent_core_zero`, `coherent_core_one`, and `coherent_core_two`; degree zero
still executes its endpoint, initialization and readout.

The guide-to-command transcription is manual. The subsequent correspondence
is proved: `sector_core_prefix`, `coherent_core_prefix`,
`qsvt_body_execution`, `qsvt_loop_execution`, `qsvt_core_execution`, and
`qsvt_core_denote`. Existing `execution_denote` connects the finite execution
certificate to the unbounded While denotation. The source loop has not been
replaced by a separate language or a gate-list oracle.

No mathematical source bug was found. The guide's schematic code was
elaborated against the actual checkout (for example `Hadamard` is the gate's
actual declaration). These are syntax/API adaptations, with no change to
operand, phase, or iteration order.

## Why the full support proof matters

The real scalar witness satisfies `P+star P=2*:embed p` **and** `Q+star Q=0`.
The latter is essential: merely prescribing the selected real polynomial
would not guarantee the ancilla-only success event has the advertised
support. `QSVTRealPair.real_qsp_phase_witness` proves this stronger witness
using the proved completion theorem, not an assumed completion oracle.

`qsvt_full_column` proves the complete even/odd defect-map invariant.
`real_qsvt_success_even` / `real_qsvt_success_odd` then give
`S JR = Jout F`, where `S=(V_phi+V_-phi)/2`.
The reverse-phase scalar and physical circuit identities prove
`QSVTRows.real_qsvt_row_even` / `real_qsvt_row_odd`:
`S^A Jout = JR F^A`. This excludes leakage from input-complement directions
into the selected output code and justifies the exact all-memory precondition.
A selected-corner equation alone would not suffice.

The Hoare derivations use finite deterministic execution, exact operator and
weakest-precondition calculations, and the existing relative completeness
of `CQHoare`. They are not a new handwritten `DWhileTotal` invariant proof.
No new logic constructor is added.

## Observations, failure, and model boundary

`qsvt_heralded_branches` gives both full-memory cq substates; no branch is
normalized or discarded. `AncillaHeralding.register_success_kraus` gives
success Kraus operators `Lift(|0><i| tensor S)` and
`QSVTFailureSemantics.register_failure_kraus` gives failure operators
`Lift(|1><i| tensor D)`, for `D=(V_phi-V_-phi)/2`.
The sum over the old ancilla basis implements the actual ancilla reset,
including discarding its former correlations.

`QSVTImaginaryColumns.failure_column_even` / `failure_column_odd` define
`Gamma` from the imaginary coefficient polynomials and prove `D JR=i Gamma`.
For an encoded logical density `rho`, success data is
`Jout F rho F^A Jout^A` and failure data is `Gamma rho Gamma^A`.
The phase `i` cancels in the density calculation.
`QSVTNativeCompleteness.native_even_completion_gram` and its odd counterpart
prove `F^A F + Gamma^A Gamma = I`; the logical and native outcome-mass
corollaries prove that the two unnormalized branches sum to the input mass.
Success probability is
`Tr(F rho F^A)` for normalized `rho`. Zero success leaves a zero substate.

`qsvt_heralded_total` is the all-outcome `top`-to-`top` total triple;
`qsvt_heralded_mass` proves preservation of total cq mass. These properties
do not assert probability-one success. Exact expectation theorems quantify
over arbitrary full-memory mixed states and classical mixtures. Identity
extension to unused memory permits entanglement with untouched references.
The counter is deliberately overwritten and `y` records the outcome; all
other classical fields are preserved. `x` and `y` have different types and
cannot alias. Register allocation and oracle unitary/isometry certificates
are explicit structural parameters. No separability or pure-input hypothesis
is imposed by the primary Hoare result.

## Reference and proof map

The supplied PDF is Gilyén–Su–Low–Wiebe, arXiv:1806.01838v1, banner dated
5 June 2018, title page dated June 6. These dates belong to the same version.
The bilingual guide supplies the independent direct recurrence proof.

| Paper item (v1 printed pages) | Checked development |
| --- | --- |
| Theorem 3 (8–9) | `QSVTSynthesis.qsp_pair_converse` and scalar soundness |
| Theorem 5 / Lemma 6 (11–12) | `QSVTRealCompletion.even_nonnegative_completion` |
| Corollary 10 (14) | `QSVTRealPair.real_qsp_phase_witness` |
| Definitions 15–16, Theorem 17 (17–19) | projected gates, `qsvt_full_column`, compressed block theorems |
| Corollary 18 (19–20) | real success columns, full rows, native polynomial Hoare theorem |

`QSVTExamples.qsp_reflection_W_bridge` checks
`R(x)=(-i)D(pi/4)W(x)D(pi/4)` as an actual two-by-two matrix equality,
retaining its global phase. The six `qsp_example_*` lemmas check every scalar
example in guide EN-F.2 symbolically.
`QSVTRejectedParity.mixed_parity_not_admissible` rejects `(1+X)/2` for every
nominal degree, making the fixed-parity boundary explicit.
`QSVTEndpointConvention.qsvt_endpoint_corner_bridge` proves that absorbing
the right endpoint preserves P and multiplies Q by `expi(-2*last)`.
The whole-product phase-shift explanation follows by substitution of the
single-signal identity; no whole-product W theorem is needed by the synthesis
or native correctness proof.

Both endpoint phases are retained. The paper's compressed reflection
presentation absorbs one endpoint and rotates the complementary polynomial;
that operation can destroy `Re Q=0`. It must not silently replace the full
witness used by this heralded program.

## Reproduction and foundations

Run from the repository root:

```
opam exec --switch=coqq -- dune build
python3 src/example/classical/check_qsvt.py --kernel
```

The script builds the whole repository, checks the public results with
`Check` / `Print Assumptions`, and optionally runs the installed library
checker recursively on the three compiled modules. Its source scans are
ordinary executable checks, not a certified parser or compiler.
`QSVT_VALIDATION.log` records the actual final run, toolchain, source hashes,
and transitive assumption reports. The required switch is `coqq`, using
OCaml 5.2.0 and the dependencies pinned in `coq-mathcomp-quantum.opam`.
Work remains local on `cqwhile+distributive`; nothing is pushed.

There are no admissions or new QSVT correctness axioms. The development
inherits CoqQ/MathComp's classical foundations: the two Dedekind-real decision
principles, propositional and dependent functional extensionality, indefinite
and epsilon choice, and the existing quantum-memory context `qreg.G` where
used. The exact dependency lists are printed in the validation log. In
particular, the existing `complex_acf_axiom` is a proved lemma supplying an
algebraic-closure structure, not a new unproved QSVT axiom.

Final validation completed successfully on 2026-10-20: whole-repository
Dune build, all 55 public declaration/assumption audits, and the recursive
Rocq library check. All 100 pre-existing files match the initial SHA-256
snapshot. The eight inherited foundations listed above are the exact union
of the audit reports, including the main framework theorem.
