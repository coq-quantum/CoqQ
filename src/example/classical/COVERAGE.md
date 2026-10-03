# Classical paper coverage

Source: Yuan Feng and Mingsheng Ying, *Quantum Hoare Logic with Classical
Variables*, ACM TQC 2(4), article 16 (2021), `classical.pdf`.
References use PDF page numbers. This record distinguishes implemented
definitions from proved properties and remaining work; it is not a claim of
complete paper formalization.

## Dependency and representation

`classical/state.v` supplies the shared cq-state foundation. The language in
`classical/language.v` imports the existing, preserved
`quantum.example.veri_QEC.cqwhile` and reuses its summable superoperator
kernels, sequential composition, and unbounded loop semantics. Distributed
semantics may depend on this state foundation and sequential language; the
classical development does not depend on the distributed one.

The ambient classical store is the existing dependent function `cmem`.
It contains all of cqwhile's `cType` values, including the paper's Boolean and
Integer types as well as naturals, reals, complex numbers, sequences and
composite types. Stores remain infinite and uncountable. This richer syntax
was explicitly requested in the continuation on 2026-10-03. Quantum registers use the existing finite
`DefaultQMem` Hilbert space and `wf_qreg`, whose validity proof enforces
distinctness of constituent variables. Positive dimensions are already
built into `qType`: `QOrd n` represents dimension `n+1`, matching the paper's
positive-dimensional Qudit requirement rather than restricting classical data.

`CQMemoryExtension.apply_marginal_ext` proves that unused quantum memory cannot
affect retained output marginals, for arbitrary cq-inputs including entangled
components. `partial_trace_product` and `normalized_memory_extension` give
the explicit product-extension equation and independence of the normalized
unused-memory state. These results apply to every subsystem of the arbitrary
finite ambient context. An interpretation into a distinct memory is supplied
by an explicit unitary identification of the source footprint in
`CQMemoryInterpretation`. Its target tensor memory is independent of
`qreg.G`, and `ClassicalMemorySteps.step_replay` checks actual one-step
replay for arbitrary target inputs. Full-program cross-context denotational
and Hoare-derivation transport are not asserted by this layer.

## Definitions and results

| Paper location | Rocq definition or result | Coverage |
| --- | --- | --- |
| Section 3.1, pp. 8-9: typed stores | `ClassicalLanguage.sort`, `store_type`, `value`, `variable`, `store` | Direct `cType`, `eval_ctype`, `cvar` aliases; Boolean and Integer compatibility names |
| Definition 3.1, p. 9: cq-state | `CQState.state`, `mass`, `support_countable`, `component_density` in `state.v` | Shared positive summable family, mass at most one; see current source for checked names |
| Lemma 3.3, p. 10: state omega-CPO | `CQState.bottom`, `chain_sup`, `chain_sup_upper`, `chain_sup_least`, `chain_sup_pointwise` | State-domain proof, independent of the false assertion-domain claim |
| Definition 3.5, p. 11: assertions | `CQAssertion.assertion`, `assertion_le` in `assertion.v` | Exact countable-image/definable-fiber subclass retained; broader semantic predicate domain approved on 2026-10-03; see `PROOF_GAPS.md` C1 |
| Corrected assertion-domain omega-CPO, p. 11; approved repair C1 | `semantic_assertion`, `semantic_le`, `semantic_bottom`, `semantic_top`, `semantic_sup`, `semantic_omega_cpo` | All effect-valued functions; pointwise partial order, bottom/top and least upper bounds of countable increasing chains proved. No closure claim for the distinguished paper subclass |
| Definition 3.7 and Lemma 3.9, pp. 12-13: expectation | `CQAssertion.expect`, `expect_summable`, `expect_ge0`, `expect_le_trace`, `expect_le1`, `expect_zero`, `expect_identity`, `expect_singleton` | Summability, positivity, bounds and basic equations proved for effect-valued predicates |
| Lemma 3.10, p. 13: state order and equality | `CQStateExpectation.state_le_iff_expect`, `state_eq_iff_expect`, `pairing_ext` | Separation by all semantic effects checked; the paper's restricted definable-fiber test argument is distinct |
| Lemma 3.11(2), pp. 13-14: decreasing state limits | `CQStateDecreasing.decreasing_converges`, `chain_inf_lower`, `chain_inf_greatest`, `expect_chain_inf` | Trace-norm convergence, greatest lower bound, and expectation convergence checked |
| Lemmas 3.10-3.12, pp. 13-14: expectation laws | `CQAssertion.expect_mono`, `expect_conditional`, `expect_complement`; `CQExpectation.expect_chain_sup`; `CQExpectationLimits.expect_semantic_sup`, `expect_semantic_inf`; `CQPrimitive.assign_pre` | Monotonicity, mask/conditional/complement equations, increasing-state and assertion-limit continuity, and assignment substitution formula checked over the approved semantic effect domain |
| Section 4.1, p. 15: syntax | `ClassicalLanguage.command` | All core constructors, with typed expressions and unbounded loops |
| Footnote 2, p. 14: classical expressions; requested cqwhile generalization | `expression`, `EVar`, `EConst`, `EApp`, `ELam`, `translate_expr`, `eval`, `expression_variables` | Direct `expr_` and `esem`; lambda bodies may have infinite syntactic support, represented as classical sets |
| Section 4.1: normalized random assignment | `probability`, `probability_mass`, `probability_normalized`, `Random` | State-dependent `probability_expression`, normalized at every store; arbitrary summable support permitted |
| Section 2.2, p. 7 and Section 4.1: measurement; requested cqwhile API | `measurement_branches`, `measurement_branchE`, `measurement_complete`, `Measure` | Direct state-dependent `mexpr` with finite `qType` outcomes, matching existing cqwhile; the paper's countably infinite measurement families are outside this chosen API |
| Section 4.1: variable sets | `writes`, `variables`, `quantum_variables`; `ClassicalFootprint.eval_local` in `footprint.v` | Finite write sets and classical-set read supports; expression locality proved for the full HOAS language |
| Table 2, p. 17 | `step` | Explicit small-step constructors, including sequence residuals and every sampled outcome |
| Definition 4.1, pp. 16-17 | `ClassicalComputations.live_step`, `maximal_path`, `finite_computation`, `infinite_computation`, `successful_maximal_iff`, `successful_route_iff`, `true_skip_infinite` | Explicit nonzero-destination computations, maximal finite paths, infinite streams and concrete divergent Skip loop; density preservation and trace nonincrease; successful maximal paths coincide with `terminates` and operational routes restricted to nonzero output |
| Lemma 4.2, p. 17 | `ClassicalOperationalRouteCost.successful_route_exact_iff`, `.successful_route_bounded_iff`; `ClassicalOperationalCountedPaths.successful_counted_route_iff`; `ClassicalOperationalCompletions.exact_completions_countable`, `.bounded_completion_chain`, `.bounded_completion_cvg`, `.bounded_completion_sup` | Exact small-step lengths agree with routes and nonzero maximal paths. Bounded completion sums preserve route multiplicity, form increasing cq-states with bounded mass and countable support, and converge in norm to the full denotation; no finite runtime or finite sampling-support assumption |
| State preservation at each step and successful finite run | `step_positive`, `step_trace_le`, `step_density`, `terminates_positive`, `terminates_trace_le` | Positivity and trace nonincrease; each finite execution preserves partial density operators |
| Finite-memory interpretation of Table 2 | `CQMemoryInterpretation.unitary_channelE`, `.measurement_channelE`, `.initialize_channelE`, `.transport_original`; `ClassicalMemorySteps.memory_step_density`, `.step_replay` | Independent primitive interpretation and actual one-step replay in any finite target tensor memory with an explicit unitary identification of the source footprint. Arbitrary target operators and entangled outside memory are allowed; the identity interpretation recovers the original model |
| Complete measurement, pp. 7,17 | `measurement_total_trace` | Sum over all outcome branches preserves trace |
| Definition 4.3, p. 17 and Lemma 4.6, p. 19 | `denote`, `measure_kernel`; `ClassicalOperational.opfun`, `opsum`, `operational_summable`, `operational_denotational` | Summable branch-labelled operational semantics equals the compositional kernel for every core constructor, including state-dependent measurements/initialization/unitaries and unbounded loops |
| Lemma 4.4(2), p. 18: linearity | `CQKernelLinearity.weighted_output_summable`, `apply_weighted_sum`, `apply_mix` | Arbitrary absolutely summable signed/complex weighted cq-states whose sum is a cq-state; arbitrary subprobability mixtures as a corollary |
| Lemma 4.6(9), p. 19 | `denote_sequenceA` | Sequential associativity inherited from proved `cqwhile.sletA` |
| Lemma 4.6(10), p. 19 | `denote_conditional` | Guard selects the correct branch at the input store |
| Lemma 4.6(11), p. 19 | `unroll`, `denote_unroll`, `denote_while_unroll_le`, `denote_while_least` | Loop denotation is the least upper bound of all finite unrollings, not a truncation |
| Lemma 4.7, p. 20 | `denote_while_unfold`, `denote_while_false` | Kernel fixed-point equation and false-guard behavior |
| Structural identities | `denote_skip_left`, `denote_skip_right` | Skip is both sequential identities |
| Section 4.1 syntactic sugar, pp. 16 and 20 | `Initialize q phi`, `Unitary q ue` | State-dependent normalized-state/unitary expressions on valid composite registers; zero initialization is `Initialize q (EConst (zero_state _))`; `CQParameterized.selected_unitary` selects actual distinct register tuples and aborts on invalid inputs |
| Definition 4.9, pp. 20-21: correctness | `CQHoare.valid`, `valid_partial_loss`, `valid_total_partial`, `run_operational` in `hoare.v` | Total and partial validity distinguished; complement-form partial validity proved equivalent to the paper's lost-trace inequality. Arbitrary-state execution via `CQKernel.apply` expands into terminating-route sums over all input stores |
| Lemma 4.10, p. 21 | `CQNormalizedValidity.valid_normalized_iff`, `.valid_total_normalized`, `.valid_partial_normalized` | Validity is equivalent to checking normalized densities at individual stores; partial clause has exactly the initial-trace-one lost-trace allowance. Distributed tests reuse this classical common theorem |
| Lemma 3.12, p. 14: substitution and state update | `CQStateUpdate.update_stateE`, `.expect_update`, `.update_state_mass`, `.update_state_assignment` | Assignment merges all input stores with the same updated output; expectation equals that of the substituted assertion, and total trace is preserved |
| Definition 4.13 and Table 3, p. 22; Lemmas 4.14/4.17 | `CQPredicate.wp`, `wlp`, `xp`, `expect_wp`, `expect_wlp`; `CQPrimitive.assign_pre`, `random_pre`, `measurement_pre`, `initial_pre`, `unitary_pre`; `CQRules.valid_total_iff`, `valid_partial_iff` | Summable dual-kernel predicate transformers, all core primitive formulas, sequence/conditional laws, arbitrary-state expectation duality and weakest-precondition characterization checked; approved full effect domain. `CQParameterized.selected_wp` proves the indexed guarded-sum wp formula; the printed wlp equality remains subject to C4 |
| Table 4, p. 26 and AbortT, p. 28; Theorems 5.1/5.3 | `CQRules.derives`, `derives_sound`, `derives_pre`, `derives_complete`, `sound_complete` | Independent inductive rules for all core commands; soundness and relative completeness checked for both total and partial correctness over the approved full effect domain. No semantic-validity constructor |
| Definition 5.2 and WhileT, pp. 27-29 | `CQRules.ranking`, `valid_while_partial`, `valid_while_total`, `tail`, `loop_ranking`; `wp_unroll_sup`, `wp_unroll_cvg`, `wlp_unroll_cvg`; `CQRanking.ranking_infimum`, `ranking_of_infimum` | Partial invariant soundness, total quantum-ranking soundness, and explicit ranking construction used by completeness; zero-limit and zero-infimum formulations equivalent; unbounded loops use limits of all finite unrollings |
| Lemma 5.4 and WhileT′, pp. 29-30 | `CQRankingComplement.ranking_iff_partial`, `.derives_while_partial_ranking` | Increasing-complement characterization proved in both directions; WhileT′ derived in the existing independent proof system from the total invariant and partial ranking premises |
| Lemma 4.14(1), p. 22: quantum assertion support | `CQPredicateSupport.local_operator_effect`, `.local_pre`, `.local_preE`, `.pre_quantum_support` | Constructs a local effect assertion on every subsystem containing the command footprint and proves that its cylinder is the full wp/wlp; includes empty subsystems, state-dependent predicates and divergent loops |
| Lemma 4.16(3–5), pp. 23–24 | `CQPredicateAlgebra.wp_finite_linear`, `.wlp_finite_affine`, `.wlp_image_unital`, `.wp_cross`, `.wlp_cross_le`, `.wlp_cross_unital` | Finite wp linearity, wlp affine linearity, exact external-map wp commutation, partial subunital inequality, and equality for unital maps; explicit rectangular V-to-W assertion actions included |
| Assignment integration bridge | `kernel_expect_norm`, `kernel_expect_rectangle`, `expect_apply_sum`, `expect_sunit`, `valid_assign_total` | Absolute scalar Fubini and deterministic-update expectation proved on arbitrary classical index types |
| Table 5 Top/Bot/Disj/Sum/Linear, pp. 31–33 | `CQAuxiliary.derives_top`, `.derives_bottom`, `.derives_disjunction`; `CQAuxiliaryDerivations.derives_sum`, `.derives_linear_total`, `.derives_linear_partial`, `.derives_series_total`, `.derives_series_partial` | Named derivations from the independent core calculus; Top is partial only, partial Linear requires total weight at most one, countable Linear retains explicit convergent-assertion conditions |
| Table 5 Param, pp. 31–33 | `CQParameterized.selected_pre_sum`, `.valid_param`, `.derives_param`; `.parameterized_zero_abort`, `.selected_duplicate_abort` | Printed finite guarded-sum inference rule in both modes, actual physical register selection, and invalid-input Abort boundaries checked; no correction of the false wlp identity adopted |
| Lemma 4.15(3), p. 23; C4 | `CQParameterizedCounterexample.parameterized_zero_partial`, `.parameterized_zero_printed`, `.parameterized_zero_counterexample` | At constant parameter zero the actual liberal precondition is identity and the printed guarded sum is zero, for every postcondition. The inequality is checked without adopting a corrected general formula |
| Table 5 Exist/Inv/C-WhileT, pp. 31–33 | `CQAssertionLocality.derives_exist`, `CQInvariant.derives_invariant`, `CQGhostRanking.derives_fresh_integer_while` | Exist and Inv in both modes; total C-WhileT with the printed single fresh integer ghost premise and a proved rank-family reduction |
| Table 5 Init0/Unit0/Meas0, pp. 31–33 | `CQPrimitiveFrame.derives_init0`, `.derives_unit0`, `.derives_meas0`; `.measurement_pre_frame`, `.measurement_tensor_effect` | Both correctness modes, physical disjoint-register side conditions, explicit measurement tensor precondition with constructed effect bound; initialization additionally permits arbitrary normalized state expressions |
| Table 5 SupOper, pp. 31–33 | `CQQuantumFrame.derives_supoper`; `CQQuantumCrossSpace.derives_supoper_cross`, `.square_extension_tensor`, `.cross_assertionE` | Literal completely positive subunital maps from V to W, allowing different dimensions and overlapping V/W inside the fixed ambient memory. Explicit square extension and matrix-unit proof give the rectangular tensor action on arbitrary entangled assertions in both modes; pre/post remainder supports may differ |
| Table 5 Tens/L-Sum/SupPos, pp. 31-33 | `CQQuantumSpaceRules.derives_tens_direct`, `CQQuantumSelector.derives_lsum`, `CQQuantumSuperposition.derives_suppos` | Tens and weighted orthonormal-label removal in both modes; total superposition from an entangled premise. Explicit unused-register maps and tensor/contraction identities checked; see `QUANTUM-SPACE-NOTES.md` |
| Table 5 Trace, pp. 31-33 | `CQQuantumTrace.derives_trace`, `.trace_assertionE`, `.lift_depolarizer` | Normalized partial trace on an unused register in both modes; the explicit cylinder identity is proved for arbitrary operators by matrix-unit expansion |
| Table 5 ProbComp, p. 31; Theorem 6.1, p. 33 | `CQProbabilisticPure.valid_probcomp`, `.derives_probcomp`, `.pure_success_effectE`; `CQProbabilisticComposition.projection_saturated_support` | Total probabilistic composition on physical registers checked; arbitrary classical predicates and unrestricted complement memory. Saturated output support is proved, not assumed |
| Section 7.1, Grover | `ClassicalGrover.iteration_success`; `ClassicalAlgorithmLoops.counted_unitary_execution`, `counted_unitary_denote`; `ClassicalGroverCorrectness.grover_prefix_denote`, `grover_success_pre`, `grover_correct` | Concrete phase oracle/reflection algebra, actual unbounded counted While, exact success effect sin²((2K+1)θ) I, and total/partial derivations; see `CASE-STUDIES.md` |
| Section 7.2, pp. 34–36 | `ClassicalFourier.fourier_circuit_correct`; `ClassicalFourierProgram.fourier_execution`, `fourier_denote`, `fourier_pre`, `fourier_correct` | Gate circuit equals QFT as a full linear operator; both actual nested While loops, dynamic index checks, final channel equality, and total/partial Hoare rule checked |
| Section 7.3, pp. 36–38 | `ClassicalPhaseCorrectness.phase_outcome_formula`, `phase_estimation_correct`, `phase_exact_pre`, `phase_exact_correct` | Actual nested program has the exact exponential-sum Born probability, with total/partial derivations and probability one for exactly representable phases; `ClassicalPhaseBounds.amplitude_geometric` and `probability_bound` give the exact off-grid geometric formula and pointwise probability bound. Printed concentration bound requires C6 repair |
| Section 7.3, Lemma 7.1, pp. 37–38; C6 | `ClassicalPhaseCounterexample.zero_probability_gt_half`, `.ordinary_success_below_half`, `.printed_phase_bound_counterexample` | Concrete phase 1−1/1024, n=1, ε=1/2, t=3: the printed ordinary-distance success event has probability below 1/2. No unproved probability premise or corrected metric is used |
| Section 7.4, modular-orbit eigenstates, p. 39 | `ClassicalOrderFindingOrbit.orbit_bits_injective`, `.orbit_isometry`, `.modular_orbit_basis`; `ClassicalOrderFindingEigenstates.modular_eigenstateE`, `.modular_eigenstate_dot`, `.modular_eigenvalue`, `.modular_eigenstate_one` | Exact-order orbit embeds isometrically into the actual target register; the printed Fourier-sum states are orthonormal eigenvectors of the actual modular unitary, and their normalized sum is the actual initialized basis-one state. Order one is included |
| Section 7.4, Equation (17), pp. 38–40 | `ClassicalModularUnitary.modular_power_residue`; `ClassicalOrderFinding.prefix_execution`, `.prefix_denote`, `.order_finding`; `ClassicalOrderFindingState.controlled_stateE`, `.outcome_probabilityE`; `ClassicalOrderFindingExecution.prefix_prepares`, `.order_finding_outcome_pre` | Concrete modular multiplication permutation, actual initialized/controlled-power/inverse-QFT/measurement/postprocessing command, and exact finite Fourier/Born outcome formula checked. The complete command preserves the measured outcome in both correctness modes |
| Sections 7.4–7.5, pp. 38–41; C7 | `ClassicalPostprocessCounterexample.printed_denominator_at_most_two`; `ClassicalOrderFindingFailure.order_finding_wp_zero`, `.order_finding_output_zero`, `.order_finding_never_four` | The literal printed selector always returns a denominator at most two; the actual complete command has zero output mass for every denominator above two, including the exact order four for N=15, x=2. The printed order-finding success bound is disproved; the larger Shor bound remains unproved because its subroutine guarantee fails |
| Section 7.5, Lemma 7.2(1), p. 40 | `ClassicalShorArithmetic.nontrivial_sqrt_factor`, `.nontrivial_sqrt_factor_mod` | Nontrivial-square-root factor extraction checked |
| Section 7.5, Lemma 7.2(2), p. 40 | `ClassicalShorCounting.failure_count_bound`; `ClassicalShorProbability.uniform_unit_success_bound`; `ClassicalShorUniform.random_conditional_success_bound` | Full concrete modular-unit count and conditional probability for the actual uniform Random source checked. The only arithmetic premises are odd N and N>1; m is the number of distinct prime divisors. CRT, prime-power roots, order valuation fibers, and finite-product counting are proved internally |
| Section 7.5, Equation (20), p. 41 | `ClassicalShorSampleEvent.natural_order_dvd`, `.natural_order_minimal`, `.natural_success_unit`; `ClassicalShorFactorExtraction.natural_success_factor` | The natural-number order is exact on coprime inputs, and its success event yields a checked nontrivial gcd factor without any order-finding-program premise |
| Section 7.5, Equation (21), p. 41 | `ClassicalShorSampling.sampling_partition`, `.sampling_mixture_bound` | Actual uniform-source gcd/coprime partition and the printed scalar probability inequality checked for every 0≤p≤1. No correctness premise on order finding, and no claim that this scalar expression is the faulty full program’s actual success probability |
| Section 7.5, cmp(N), p. 40 | `ClassicalShorComposite.cmp_distinct_prime_count` | The printed odd/composite/not-perfect-power condition implies at least two distinct prime divisors |
| Table 6, Section 7.5, p. 41 | `ClassicalShorProgram.shor`, `.uniform_probabilityE`, `.shor_partial_safe`, `.derives_shor`, `.shor_direct_total`, `.derives_shor_direct`, `.direct_preE` | Literal normalized uniform/gcd/quantum-order-finding/candidate-check program; partial factor-output safety and an independent total lower bound from the immediate gcd branch checked. The paper's larger success bound remains blocked by C7 |
| Small checked boundary cases | Language examples above; `assertion_examples.v`; `CQHoare.set_integer_constant`, `set_integer_constant_sound`, `partial_abort_top`, `abort_not_total_top`, `two_skips_sound`; `CQRuleExamples.assignment`, `false_loop`, `infinite_skip_partial`, `infinite_skip_not_total`, `initial_core_embeds` | Infinite natural-memory formula/expectation examples, actual signed-integer assignment derivation, partial Abort derivation, total Abort failure, both-mode false-loop derivations, divergent Skip loop partial derivability and total nonderivability, and an embedding of the original structural rules into the complete rules |

## Explicit mathematical parameters and remaining bridges

`probability_normalized` requires normalization at every input store.
`measurement_branches` is built directly from cqwhile's finite quantum
measurement expressions, with the lifted single-Kraus branch equation and
trace preservation proved from the existing packed measurement type. The
continuation explicitly requested this API; countably infinite measurement
families are no longer claimed as covered by the core constructor.

`ClassicalMeasurementExamples.boolean_measurement` supplies constant
measurement expressions. The checked branch, denotation and mass lemmas link
them to inherited semantics. `selected_measurement` and
`selected_measurement_eval` additionally exercise a measurement chosen from a
classical Boolean variable.

`ClassicalOperational.equal_OS_DS` separately proves operational/denotational
correspondence for the new `command`, including all inherited classical types and
state-dependent primitive expressions. Its route representation preserves typed outcomes and
both subroutes of a sequential composition, so distinct paths with coincident
endpoints remain distinct summands. `eval_route_sound` and `terminating_route`
connect successful routes and finite small-step executions in both directions
by existence; an explicit bijection between proof objects and routes is not
claimed. The inherited `cqwhile.equal_OS_DS`, for its older finite-measurement
syntax, remains unchanged.

A final whole-project build passed on 2026-10-03 for all 233 sources,
including the concrete Shor arithmetic, spectral identities, alternative
ranking rules, counterexamples, bounded operational completions, and the
independent memory-interpretation/replay layer.
See [VALIDATION.md](VALIDATION.md) for the
source and assumption audits. Compilation of definitions is not a claim that
the remaining surrounding paper theorems are proved.

The 2026-10-03 assumption audit of `expect_apply_sum`, `valid_assign_total`,
`derives_sound`, `abort_not_total_top`, and `semantic_omega_cpo` found only
the inherited classical real/choice/extensionality foundations and, for the
concrete command results, the existing quantum-memory model parameter
`qreg.G`. The exact assumptions and their roles are recorded in
`HOARE-NOTES.md`; no new axiom or admitted proof was introduced.
The later audit additionally covers the full `CQRules.sound_complete`, both
loop soundness/ranking foundations, arbitrary-state unrolling convergence,
assertion supremum expectation continuity, countable weighted expectation
exchange, and branch reindexing. Their assumptions remain the same inherited
foundations and explicit finite-memory model parameter.

`CQAssertionLocality.pre_local` proves predicate-transformer locality for every
shared-language command, including unbounded loops. `valid_exist` and
`derives_exist` prove the Table-5 existential rule in both correctness modes.
The Fourier/phase program and signed-rank theorems passed a fresh assumptions
audit with only the inherited foundations and, for concrete memories, `qreg.G`.

`CQGhostRanking.valid_fresh_integer_while` and `derives_fresh_integer_while`
prove Table-5 C-WhileT with its single fresh integer ghost premise, reducing it
to the checked signed-rank family through Inv and Exist.
