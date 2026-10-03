# Validation

Date: 2026-10-04. The reorganized project passes:

```sh
opam exec --switch=rocq.9.1 -- dune build
```

All **67 Rocq source files** are covered: 39 original foundation/veriQEC
files, eight classical topic files, eight distributed topic files, and the
12 examples imported from upstream `main` at `b169ea4`.
The 39 original files, dependency manifest, and Dune configuration are
unchanged. The compilation log is
`/private/tmp/coqq-reorganization-full-build.log` (exit status 0).

A source audit of all 28 reorganized/imported files found no `Admitted`,
`admit`, axiom/parameter/conjecture declarations, or unfinished/debug proof
commands. The two developments each contain eight `.v` files and three
Markdown guides. All project imports and documentation links resolve.

Fresh `Print Assumptions` checks cover 15 results: assertion completeness,
bounded operational completions, both classical loop soundness theorems,
classical completeness, memory replay, the phase counterexample, Shor
counting, both public distributed completeness theorems, sequentialization,
distributed memory replay, teleportation, remote CNOT, and the imported
CoqQ total-loop rule. The public `DistributedHoare.Local` and `.Network`
judgments were also checked against their `sound_complete` statements.
Only the inherited real/choice/extensionality foundations and existing
finite-memory parameter `qreg.G` were reported; the exact inherited
assumptions are listed in the historical record below. The audit files are
in `/private/tmp/coqq-reorganization-audit/`.

The reorganization retains the existing mathematical boundaries, including
the C4 liberal-precondition issue, the C6 phase counterexample, the C7
order-finding counterexample, and the one-step boundary of arbitrary-memory
replay. See [coverage](README.md#coverage) and
[proof notes](PROOF_NOTES.md#proof-gaps). No repair of those statements is
introduced by reorganizing or importing examples.

## Validation before reorganization

The following checkpoints refer to the former 233-file layout.

Date: 2026-10-03. The development uses the existing `rocq.9.1` opam switch and
qualified Dune theory `quantum`. The dependency versions, project settings,
foundations, and `veri_QEC/cqwhile.v` are preserved.

### Build boundary before reorganization

A final whole-project build passed on 2026-10-03 with all 233 Rocq sources,
including the 39 existing sources, 105 classical modules, and 89 distributed
modules. This includes both complete core calculi, the concrete Shor
counting/sampling and spectral pipeline, alternative ranking rules, formal
counterexamples, bounded operational completions, raw-serialization Hoare
equivalence, and the independent memory-interpretation/replay layer.
The log is `/private/tmp/coqq-assertion-check/final-full-build.log`
(exit status 0). The final source audit of all 194 new-development files
passed with no forbidden declarations. The source hashes are recorded in
`/private/tmp/coqq-formalization-audit/final-source-manifest.json`.

Direct compiler iterations write their products under `/private/tmp`.
Only Dune manages `_build`. The final command passed:

```sh
opam exec --switch=rocq.9.1 -- dune build
```

### Checked behaviors and central results

* Shared cqwhile types and expressions include unbounded integers and
  unrestricted classical memories. Measurements use its finite `qType`
  outcomes and may depend on classical expressions. Higher-order expression
  footprints may be infinite; distributed source programs require finite
  read sets explicitly.
* Classical operational route sums equal denotational kernels, including
  nested unbounded loops. Arbitrary cq-input execution is linear and trace
  nonincreasing. Simultaneous finite unrollings of all nested loops converge
  to the full denotation, also with arbitrary command continuations.
* The independent classical inference system is sound and relatively complete
  in both correctness modes over the approved semantic assertion domain.
  Checked auxiliary rules include Exist, fresh-ghost integer ranking,
  disjoint-register superoperators, and total probabilistic composition.
* Actual Grover, Fourier, and phase-estimation programs have checked execution
  and correctness results; exact phase probabilities and representable-phase
  certainty are included. Counterexamples to other printed claims are
  documented separately.
* Distributed steps preserve probability and normalized branch states.
  Successful computation stages increase and converge. Concrete diamonds
  prove scheduler-independent successful outputs and a unique denotation.
* The independent distributed network rules are sound and relatively complete
  for actual operational execution in both correctness modes. The explicit
  finite-horizon ranking decreases across every enabled rendezvous and tends
  to zero; no ranking or correspondence hypothesis is assumed.
* Teleportation and remote CNOT have actual distributed correctness theorems
  and network-rule derivations in both modes, together with process ownership.
  The remote-CNOT theorem allows arbitrary entangled two-qubit input.

These are theorem boundaries, not a claim that every paper result is complete.
[the coverage map](README.md#coverage) and the [distributed map](../distributive/README.md#coverage)
track the precise proved coverage and remaining results.

### Assumptions

Fresh `Print Assumptions` audits cover the classical core completeness and
loop rules, assertion limits and expectation continuity, actual Fourier/phase
programs, integer and ghost ranking rules, locality/Exist, quantum framing,
probabilistic composition, concrete distributed confluence and scheduler
independence, the Bellman/least-value construction, local execution limits and
comparison, and both protocol source triples.

The reported logical foundations are inherited from CoqQ and its dependencies:

* `ClassicalDedekindReals.sig_not_dec`
* `ClassicalDedekindReals.sig_forall_dec`
* `boolp.propositional_extensionality`
* `boolp.functional_extensionality_dep`
* `FunctionalExtensionality.functional_extensionality_dep`
* `Epsilon.epsilon_statement`
* `boolp.constructive_indefinite_description`

Concrete memory theorems additionally use the inherited
`qreg.G : qreg.context` finite quantum-memory parameter. No new correctness
axiom or admission occurs in the audited results. In particular, the new
operational correspondence avoids the old cqwhile theorem's `Eqdep` dependency.

Representative temporary logs are in `/private/tmp/coqq-assertion-check/`:
`phase_fourier_assumptions.log`, `locality_ghost_assumptions.log`,
`global_value_assumptions.log`, `composition_local_assumptions.log`, and
`probcomp_assumptions.log`. Agent checks of distributed scheduler and upper
comparison theorems are in `/private/tmp/coqq-distributive-next/`.
These logs are evidence from this workspace, not build dependencies.

Additional checked audits cover `DistributedCQInput.run_point`, `.run_kernel`,
and `.component_reassemble` (`cq_input_assumptions.log`), the exact local
completion limits (`local_limit_assumptions.log`), and arbitrary countable
mixture expectations (`mixture_expectation_assumptions.log`). These report the
same inherited foundations; the generic mixture-expectation theorem does not
depend on `qreg.G`.

`quantum_trace_assumptions.log` audits `CQQuantumTrace.lift_depolarizer` and
`derives_trace`. The arbitrary-space normalized partial-trace identity uses
only inherited classical foundations; the concrete language rule additionally
uses the existing memory context `qreg.G`.

The source audit strips nested comments and strings before checking for
admissions, new axiom/parameter/conjecture declarations, and abandoned proof
commands. It distinguishes the language constructor `Abort` inside a
command definition from the vernacular `Abort.` proof command. The latest
source scan passed for all 194 files, followed by the 233-source full build.

`network_complete_assumptions.log` audits
`DistributedTotalCompleteness.sound_complete`, the constructed
`DistributedNetworkRanking.tail_network_ranking`, and the program
operational/serialization equality. The audit reports only the inherited
foundations above and `qreg.G`; it has no additional correctness hypotheses.

Further audits passed for state-order separation and decreasing-state limits
(`state_limits_assumptions.log`), signed absolute-series kernel linearity
(`kernel_linearity_assumptions.log`), quantum marginal/extension independence
(`memory_extension_assumptions.log`), and scalar local-completion expectation
limits (`local_expectation_assumptions.log`). The generic state and kernel
results do not depend on `qreg.G`.

`protocol_network_assumptions.log` audits the actual network inference-system
derivations for teleportation and remote CNOT in both correctness modes. It
reports the same inherited foundations and `qreg.G`.

Additional audits cover explicit maximal computations (`computations_assumptions.log`),
rectangular SupOper (`quantum_cross_space_audit.log`), predicate linearity and
unital commutation (`predicate_algebra_audit.log`), and the literal Param rule
with invalid/duplicate-index abort cases (`parameterized_audit.log`). These
report inherited foundations and the existing `qreg.G` only.

`phase_bounds_assumptions.log` checks the exact geometric amplitude and
pointwise Born-probability bound; it reports inherited foundations without
`qreg.G`. The modular-multiplication unitary and its basis/power equations
likewise have no quantum-memory parameter in their assumption audit.

`postprocess_assumptions.log` audits
`ClassicalPostprocessCounterexample.printed_denominator_at_most_two` and
`printed_never_four`. Both are closed under the global context: the stronger
postprocessing counterexample uses no axioms, including no inherited classical
axioms or quantum-memory parameter.

Mapped audits of `CQNormalizedValidity`, `CQStateUpdate`, and
`CQPredicateSupport` also pass with the inherited foundations and `qreg.G`.
The distributed `normalized_tests.v` module retains its public API as an
alias of the shared classical normalized-density results.

`order_finding_execution_assumptions.log` audits the actual prefix action,
prepared state, preserved measurement outcome, and complete-command
`order_finding_outcome_pre`. The first, second, and last depend on inherited
foundations and `qreg.G`; the abstract measured-projector identity has no
quantum-memory parameter. The actual-command failure theorem in
`order_finding_failure_audit.log` has the same inherited foundations and
`qreg.G`. `shor_program_audit.log` checks partial factor safety and the
independent total lower bound from the immediate gcd branch.

The concrete Shor counting pipeline has checked, fully closed assumptions
audits: prime-power square-root uniqueness, each order-valuation fiber's
half-cardinality bound, finite product counting, binary and arbitrary finite
unit CRT, exact failure-event correspondence, canonical prime factorization,
and `ClassicalShorCounting.failure_count_bound`. The only theorem premises
are N>1 and odd N; structural CRT and counting facts are all proved. The
numerical uniform-unit ratio and scalar mixture bound over `numFieldType`
are likewise closed under the global context. Exact natural-order and
factor-extraction results, and the cmp(N) distinct-prime consequence, also
have closed audits.

`shor_uniform_assumptions.log` audits the actual-source sampling reindexing,
conditional probability ratio, and `random_conditional_success_bound`. It
reports only the inherited real/choice/extensionality foundations listed
above, with no quantum-memory parameter and no new axiom. This is a
statement about the actual Random source and the exact arithmetic order,
not a success claim about the faulty printed quantum postprocessor.

`shor_sampling_audit.log` checks the actual sampling partition and Equation
(21) inequality. They use the same inherited real/classical foundations,
without `qreg.G`. Their signatures contain only the printed sampling and
scalar premises; no order-finding correctness premise is present.

`order_finding_eigenstates_assumptions.log` audits the concrete modular
Fourier coefficients, orthonormality, normalization, actual-unitary
eigenvalue, and reconstruction of basis one. Only inherited real/choice/
extensionality foundations occur, with no `qreg.G` and no new spectral
assumption. The orbit injection is closed under the global context; its
isometry and channel-action proofs use only the same inherited foundations.

`ranking_complement_direct_assumptions.log` audits classical Lemma 5.4,
WhileT′, and their complement/order/convergence helpers. The command results
use inherited foundations and `qreg.G`; generic effect results need only
the inherited foundations. Both the direct compilation and qualified Dune
target passed.

`/private/tmp/coqq-distributive-next/distributed_ranking_complement_audit.log`
checks the guarded/network increasing-ranking equivalences and derived
Rep-T′/Dist-T′ rules, including their operational soundness corollaries.
Direct and qualified Dune compilation passed. Its seven assumption reports
contain only inherited foundations and `qreg.G`.

`/private/tmp/coqq-classical-check/phase_counterexample_audit.log` audits
`zero_probability_gt_half`, `ordinary_success_below_half`, and
`printed_phase_bound_counterexample`. The concrete counterexample has no
unproved premises and uses only inherited classical foundations, without
`qreg.G`. Its direct and Dune compilations passed. This disproves the
printed ordinary-distance bound without adopting a repaired metric.

`parameterized_counterexample_assumptions.log` audits the identity liberal
precondition, zero printed precondition, and their inequality for constant
parameter zero. Direct and Dune compilation passed; only the inherited
foundations and `qreg.G` occur. The pending C4 repair is not assumed.

Exact route lengths and counted maximal paths have mapped audits in
`/private/tmp/coqq-classical-check/operational_route_cost_audit.log` and
`operational_counted_paths_audit.log`. The generic route-subset cq-state
construction and the concrete bounded-completion chain/limit theorems have
audits in `/private/tmp/coqq-assertion-check/operational_approximants_assumptions.log`
and `operational_completions_assumptions.log`. All direct and Dune targets
passed, followed by the 228-source checkpoint build. Audited assumptions
are inherited foundations and `qreg.G`, with no Eqdep dependency.

`/private/tmp/coqq-distributive-next/serial_hoare_audit.log` checks Lemma C.9
for the raw serializer in both modes, its printed partial postcondition, and
the loop postcondition-agreement lemma. The four reports contain only
inherited foundations and `qreg.G`; direct/Dune/full-checkpoint builds passed.

`memory_transport_assumptions.log` audits generic unitary transport of
Kraus operators, physical channels, composition, inverse transport, trace,
and arbitrary summable instruments. All eight reports contain only the
inherited real/choice/extensionality foundations, without `qreg.G`. Direct
and qualified Dune compilation passed; this module was added after the
228-source checkpoint.

`/private/tmp/coqq-classical-check/memory_interpretation_audit.log` checks
six primitive-covariance, measurement-normalization, original-model and
summation results. `memory_steps_audit.log` checks structural replay,
density preservation, and residual support. Direct and qualified builds
passed; all nine reports use only inherited foundations and `qreg.G`.
Target memories and their unitary interpretation are explicit model
parameters, with no replay or covariance hypothesis.

`memory_instruments_assumptions.log` checks summability reflection from
cylinder lifts, commuting those lifts with sums, and reflection of trace
nonincrease for summed instruments. All three reports use inherited
foundations without `qreg.G`; direct and qualified builds passed.

`/private/tmp/coqq-distributive-next/memory-replay/audit.log` checks seven
distributed memory results: local probability, global normalization, source
instrument summability and trace nonincrease, covariance, the transported
branch family, and `global_step_memory_change_access`. All reports contain
only inherited foundations and `qreg.G`. Direct compilation, qualified Dune
integration, and the final 233-source build passed. Independent review
confirmed that the target transition rules and source instruments are defined
independently of the replay conclusion, and that arbitrary entangled target
states are allowed. The result uses source-process footprints and establishes
one-step replay; full-program cross-context denotational semantics and
Hoare-derivation transport remain outside this checked layer.
