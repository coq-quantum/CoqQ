# Source audit and proof obligations

Source: Yuan Feng, Sanjiang Li, Mingsheng Ying, *Verification of Distributed
Quantum Programs*, ACM TOCL 23(3), article 19 (2022), `distributive.pdf`.
Page references below use PDF pages, which agree with the article's 19:n suffix.
The actual PDF was extracted and the mathematical layouts of pages 10 and 32 were rendered
and inspected. These notes distinguish repairs of arguments from false claims.
No result below is claimed formally resolved unless theorem names are supplied.

## D1: Reordering measurements preserves joint weights, not edge probabilities

**Location:** Theorem 3.9, Appendix C.1, pp. 31-32, construction of `T_j`, step
(2). The sentence claiming corresponding edges have the same probability is
false when the input is entangled. On the Bell state, a computational-basis
measurement on Alice has outcome 0 with probability 1/2. After fixing Bob's
outcome 0 first, Alice's corresponding outcome has probability 1. Their quantum
variables are disjoint and all program ownership assumptions still hold.

**Correct local argument:** Write `E_a` and `F_b` for the branch completely
positive maps of operations on disjoint registers. Cylindrical extension gives
`F_b o E_a = E_a o F_b`, including on entangled inputs. If `rho` is normalized,
the forward joint weight is

`tr(E_a rho) * tr(F_b(E_a rho / tr(E_a rho))) = tr(F_b(E_a rho))`.

The reverse joint weight is `tr(E_a(F_b rho))`, hence is equal. Positive joint
weight ensures both normalizations are defined, and both final normalized
densities equal the common unnormalized branch divided by its trace. If an
intermediate probability vanishes, the positive semidefinite intermediate
operator has trace zero and is zero, so all descendant weights vanish. Classical
updates commute because neither process changes any variable read by the other.
This proves the needed finite interchange with joint weights; it does not
require a product-state assumption or modify the theorem's hypotheses.

**Gap in the infinite argument:** The last paragraph, "Repeat ... eventually",
does not justify an infinite tree transformation. A full repair must compare
finite successful cylinders, use their countable nonnegative sums, and pass to
suprema of finite terminating mass. It must also specify how unsuccessful runs
are extended after the interchange. It is not enough to assert that finitely
many swaps preserve each finite prefix, since the number of swaps need not be
uniformly bounded across branches. The checked replacement below avoids that infinite transformation.

**Finite-horizon replacement argument (checked):** A stronger local
proof removes the need to transform an infinite tree. For every horizon `d`,
compare the successful outputs after exactly `d` global transitions (terminal
configurations stutter). Induct on `d`, uniformly over reachable residual
configurations and all history-dependent schedulers. At horizon zero the
output depends only on the configuration. If two schedulers choose the same
action, deterministic local control gives the same branch family; apply the
induction hypothesis separately to each outcome. If they choose different
actions, their participant sets are disjoint: exclusive process guards and
point-to-point channels rule out overlapping enabled rendezvous. Each action
remains enabled after the other, unless an abort has produced failure. Neither
first successor can be successful while the other action's participants remain
active. Thus the horizon-one successful outputs are both zero. At a larger
horizon, use the induction hypothesis after the first step to choose the other
action second, and then use the horizon-minus-two successful-output observable.
Commuting classical updates and disjoint quantum operations give equal joint
weights and equal nonfailed residual configurations after those two steps.
Failure branches contribute zero in either order. Absolute Fubini groups the
two-step outcomes, including coincident endpoints. Consequently both schedules
have the same finite-horizon successful output. Equality of their pointwise
limits follows directly from equality at every horizon, using the separately
proved monotone bounded convergence theorem. This argument uses no fairness
assumption and permits a separate scheduler choice at every indexed history.

**Checked final bridge:** `DistributedSchedulerResults.stage_horizon` instantiates
the finite-horizon theorem with the concrete projected global diamond.
`stage_scheduler_independent` proves equality at every finite stage, and
`result_scheduler_independent` proves equality of their cq-state suprema.
`denotational_results_unique` and `denotational_results_singleton` combine this
with the checked convergence/existence results; `denote_program` is the unique
program denotation. These results passed direct compilation and qualified Dune
integration. No abstract confluence assumption remains in their signatures.

The formal obligations are residual preservation of process footprints and
exclusive guards, uniqueness or disjointness of enabled action labels, the
weighted two-step diamond (with failure erased), and the finite-horizon
induction. Only the theorem names listed below denote checked components;
this paragraph is not a claim that the entire diamond has been formalized.

Residual ownership is preserved without a reachability assumption hidden in
the commutation theorem. Initialization statements and each source branch
body have footprints contained in their owning process. A local transition
can only decrease its residual read, write, and quantum footprints; completion
switches to waiting or stopped control. A communication selects two original
branch bodies, so their footprints again lie in the two owning processes.
These facts establish a concrete invariant initially and after every global
step. Distribution lifting preserves it on positive support by regrouping
equal configurations. A step only changes the controls of its participant
set. Every enabled action has a participant whose control is not stopped.
For two disjoint enabled actions, that participant of the other action remains
not stopped after the first, so the first action's output has zero successful
component. This supplies the finite-horizon induction's one-step zero case.

Checked in `DistributedResidual`: `global_step_owned`,
`distribution_step_owned`, `computation_owned`, `global_step_label_control`,
and `disjoint_enabled_successful_component`. `DistributedFootprint` proves
that every changed name is included among the owning statement/process reads.
`DistributedGlobalActions.labeled_step_deterministic` proves family equality
for the same ordered action label. Its `labeled_steps_disjoint_or_equal` and
`distinct_labeled_step_zero` establish the alternative case, and
`global_steps_successful_equal` proves the concrete one-step successful-output
equality required by the finite-horizon induction. The corresponding two-step
operational diamond is checked below in `DistributedConfluence`.

Failure configurations require an explicit quotient in the two-step argument:
if the first action aborts, the concrete semantics stutters immediately, while
the opposite order can retain different residual controls or quantum density
before the same failure. Replace every configuration whose store is `None`
by one fixed failed configuration when comparing distributions. Successful
outputs are unchanged by this map. After first-action failure, a ghost second
instrument has total probability one and all its endpoints map to that same
failure; its mixture therefore equals the actual stuttering failure. This
allows the joint-instrument commutation proof to cover aborts without assuming
that the two failed raw configurations are equal. The quotient is a proof
device; the actual operational relation and its failure states stay unchanged.

**Checked abstract induction:** `ProbabilisticDiamond.horizon_step`,
`horizon_evolution`, `horizon_stages`, and `finite_horizon_unique` in
`diamond.v` prove the finite-horizon argument for an indexed probability-step
relation with an explicit one-step observation-agreement premise and an
explicit two-step distribution-diamond premise. Selectors after a step depend
on its branch index, so coincident configurations may receive different
choices. This generic theorem does not assume or conclude the concrete
program diamond; `DistributedConfluence.projected_two_step_diamond`
discharges it from process privacy, residual footprints, and the weighted
quantum interchange identities, as detailed below.

**Available foundation:** `hstensor.liftfso_compC` proves the required commuting
superoperator equation for disjoint supports. `normalized_joint_weight`,
`commuting_joint_state`, and `commuting_joint_weight` in
`DistributedOperational` formalize the finite weighted-branch identities.
`DistributedScheduler.rendezvous_partner_unique` and
`enabled_labels_disjoint_or_equal` now check the enabled-label claim, with
`global_step_has_label` connecting it to actual transitions. `local_step_wf`
and `local_step_changes` preserve residual well-formedness and write bounds.
`weighted_normalized_output`, `weighted_two_normalized_outputs`, and
`commuting_normalized_outputs` prove the branch identities including zero
probability outcomes, using positivity and trace-zero elimination. These
identities support the operational two-step diamond described below and the
checked `DistributedSchedulerResults` finite-horizon/limit bridge.

`DistributedLocalActions.local_step_deterministic` now checks determinism of
all well-formed local statements; `local_step_reads`, `local_step_quantum`,
`local_step_unchanged`, and `local_step_preserves_expression` establish the
remaining local footprint/store-frame facts. `DistributedInstruments` assigns
each statement a syntax-dependent outcome type `local_index`, a classical
control/store update `local_control`, and a CP map `local_map` per outcome.
`local_realization` proves exact equality with the operational family on every
normalized input, including random-assignment and zero-weight measurement
branches. `local_map_external` proves commutation with any map lifted from a
quantum support disjoint from the statement's support. These lemmas expose
rather than assume the one-step structural claims used by the repair.

**Checked concrete local interchange:**
`DistributedInterchange.local_map_commute` derives commuting branch maps from
disjoint syntactic quantum supports; `local_stores_commute` derives commuting
possibly failing store updates from mutual read/write privacy and distinct
writes. `DistributedObservables.observe_bind_nested` and
`probability_exchange` prove the bounded-observer absolute-Fubini identities
for arbitrary countable probability families. Combining these results,
`DistributedLocalDiamond.local_pair_commute` proves equality of the complete
two-action distributions in both orders. Its endpoint function is arbitrary
provided every failed memory maps to one fixed failure. The proof first
replaces early failure by a probability-one ghost instrument whose outputs
all map to that failure (`pair_ghost_same`), then freezes the independent
second action's classical parameters (`ghost_observe`), and uses joint weights
to commute the resulting branches. This theorem includes zero-probability
quantum outcomes and countably supported state-dependent random assignment.
It has no operational-diamond or scheduler-independence assumption.

**Checked global diamond:** `DistributedConfluence.instrument_replay` connects
the descriptor replay theorem to the normalized instrument representation.
`continuation_step` constructs a legal projected second transition after
every first outcome. `descriptor_join` derives all local interchange premises
from process ownership, privacy, and disjoint enabled participant sets, and
uses commuting descriptor control updates to identify final configurations.
`global_join` handles arbitrary actual global transitions, using exact family
equality when their ordered action labels coincide. Finally,
`projected_two_step_diamond` proves the full strong distribution diamond for
`DistributedSchedulerSemantics.projected_step`, including terminal and invalid
stutters. This is a theorem about the concrete operational semantics; no
abstract diamond or semantic-correctness premise remains. It supplies exactly
the two-step premise of the previously checked finite-horizon induction.


## D2: Assertion closure and omega-CPO claim is false as stated

**Location:** Definition 5.1, p. 17; countable sums and omega-CPO claim, p. 18;
Definition C.5 and Table 5, p. 33. The same issue occurs in the classical paper.

Let `b_0,b_1,...` be distinct Boolean variables and let `I` be the identity on
any nonzero finite-dimensional Hilbert space. Define

`Theta_n(sigma) = (sum_{k<n} 2 * 3^(-k-1) * 1_{sigma(b_k)=true}) I`.

Every `Theta_n` has finite image and each fibre is a finite Boolean formula.
The sequence increases pointwise, lies between zero and `I`, and has a unique
pointwise limit. Its image contains the Cantor set (all ternary expansions with
digits 0 and 2), which is uncountable. Thus that limit is not a cq-assertion
according to Definition 5.1. The infinite sum of the individual summands gives
the same counterexample to countable-sum closure. Even independently of the
image condition, closure of fibres under arbitrary countable Boolean operations
does not follow from ordinary finitary first-order definability.

**Decision:** On 2026-10-03 the user approved using all bounded operator-valued
functions as the semantic assertion domain for limits, while retaining the
paper's countable-image/definable-fibre assertions as an explicit subclass.
The shared classical assertion foundation implements that distinction. This
repairs semantic limit closure without pretending the printed subclass itself
is an omega-CPO. Any completeness theorem must state which assertion domain
its derivations range over; none is currently claimed for the published type.

## D3: Measurement normalization (Lemma 3.3)

**Location:** Lemma 3.3, p. 11, proof omitted as inspection of Table 1.

The earlier countable-instrument representation required an infinite-sum
argument. The shared `cqwhile` API now uses finite `qType` outcome types; the
measurement expression can depend on the input classical store. Let `(E_i)` be the summable
family of branch CP maps, and suppose its sum is trace preserving. For a
normalized positive `rho`, every `E_i rho` is positive. Evaluation at `rho` and
trace are continuous linear maps on the finite-dimensional operator spaces,
so their interchange with the absolutely convergent branch sum gives

`sum_i tr(E_i rho) = tr((sum_i E_i) rho) = tr(rho) = 1`.

The probabilities are nonnegative. For every positive probability `p_i`, the
operator `E_i rho / p_i` is positive and has trace one. A zero-probability branch
is omitted from support; retaining an arbitrary normalized value at that
zero-weight index has exactly the same distribution. Random assignments need
the explicit assumption that the distribution has mass one, because CoqQ's
underlying `Distr` also represents subdistributions.

**Formal resolution:** `ClassicalLanguage.probability` and `.measurement`
contain these model-data conditions. `DistributedOperational` proves
`measurement_probability_nonnegative`, `measurement_probabilities_summable`,
`measurement_probability_total`, `measurement_branch_probability`, and
`measurement_branch_normalized`. `local_step_probability`,
`global_step_probability`, `local_step_normalized`, and
`global_step_normalized` extend these facts to all Table-1 rules. All are checked
without new axioms or admissions. `DistributedDistribution.distribution_step_probability`
and `.distribution_step_normalized` also check preservation for the lifted
distribution relation.

## D4: Distribution trees require histories and a stuttering simulation

**Location:** Definition C.1, p. 30; Lemma C.4 and proof of Theorem 4.2, p. 32.

Nodes at a level cannot simultaneously be identified only by configuration and
be assumed to have a unique path from the root: distinct stochastic histories
can merge into the same configuration. One must use history-indexed nodes or
sum the masses of all incoming paths. The implementation retains branch
indices, including duplicate endpoint configurations; equality of the induced
distributions must subsequently quotient those presentations by aggregated
weights.

The one-step correspondence in Lemma C.4 also needs justification for
administrative transitions: termination of separate process main loops takes
separate parallel steps, whereas one sequentialized do-loop tests the combined
guard. `T` was defined on initial programs, not all residual configurations.
A formal proof should first define a residual translation and then establish
a finite-step or stuttering simulation with terminal restriction by `TERM`.
The residual translation and two comparison directions are now checked in
`DistributedCorrespondence.residual_value` and `.denote_program_sequentialize`,
as detailed below; the theorem concerns the full unbounded operational limit.

## D5: Priority guards cannot be dropped in the completeness proof

**Location:** Proof of Theorem 5.8, completeness step (2), p. 37. The displayed
identity for `B_ij /\ B_kl /\ Psi'` keeps only the summand for that rendezvous,
which is additionally guarded by the priority predicate `B_i`.

Two disjoint enabled rendezvous are permitted by Definition 2.4. For the
lower-priority pair, `B_ij /\ B_kl` is true and `B_i` is false. With postcondition
top and a finitely terminating network, `Psi'` is top; thus the alleged equality
has left side `I` and right side zero. Determinism of each process does not rule
out disjoint simultaneously enabled pairs.

**Required replacement:** Establish that the weakest liberal precondition of
the whole network is preserved by every enabled rendezvous using the corrected
scheduling-independence theorem, and derive the invariant premise from that
semantic fact. The displayed algebraic equality is false; the high-level
completeness result additionally depends on resolving D2. The corrected partial
completeness theorem is now checked as
`DistributedPartialCompleteness.partial_sound_complete`. The operational
horizon ranking construction below additionally proves the total case in
`DistributedTotalCompleteness.sound_complete`. Neither theorem is assumed
as a premise.

## D6: Remote-CNOT invariant contains an incorrect target vector

**Location:** Section 6.2, p. 26, item (1) after equation (8).

The displayed invariant's `|phi>` is defined as the input
`sum alpha_kl |k,l>`, whereas at stages 0, 1 and 2 it must track the CNOT target
`sum alpha_kl |k,l xor k>` (with the indicated pending Pauli corrections).
For input `|1,0>`, the protocol output is `|1,1>`; the printed stage-2 invariant
instead asserts `|1,0>`. This is a counterexample to that invariant, not to the
protocol's equation (8).

**Status:** The printed invariant has not been adopted or silently repaired.
The actual remote-CNOT protocol equation has been proved directly, including
its distributed operational correctness and output data register. These proofs
do not use the false invariant. A repair of that displayed invariant remains
a separate mathematical change requiring explicit approval.

## D7: Classical ranking bounds iterations, not operational steps

**Location:** Theorem 5.11, p. 22. The proof says computations terminate within
`sigma(t)` steps. Even a loop with ranking value one may have a sequential body
with arbitrarily many primitive steps, or an almost-surely terminating inner
probabilistic loop with no uniform step bound.

**Correct argument outline:** Induct on the integer variant for the expected
invariant value, not on raw transition counts. At a state outside the classical
support `p`, the invariant is zero and the required lower bound is trivial.
At a state in `p` with an enabled guard, the classical total-correctness premise
ensures all body output support has a strictly smaller variant. The quantum
invariant premise bounds the initial invariant expectation by the sum of the
output invariant expectations. On output states still in `p`, apply induction;
on output states outside `p`, the invariant contribution is zero. Countable
additivity combines the output bounds. If no guard is enabled, the loop exits
with its invariant unchanged. This proves the intended weighted Hoare bound;
it does not assume `p` itself is preserved or claim that every run from `p`
terminates within a bounded number of primitive steps.

**Checked rules:** `DistributedClassicalAuxiliary.valid_fresh_guarded_loop`
combines all guarded invariant and fresh-integer-ghost decrease premises into
the conditional-chain body, then applies the corrected classical ranking
argument. `.classical_repetition` proves C-Rep-T for actual local completion
semantics, and `.classical_distributed` proves C-Dist-T for actual distributed
execution, with the support condition `p AND BLOCK -> TERM` discharging the
final successful-termination test. The explicit ghost-freshness hypotheses
cover the body, guards, classical support expression, and integer variant.
Both rules passed direct compilation and qualified Dune integration.

## D8: Indexed probability presentations and lifted steps

**Location:** Section 3.2, pp. 11–12, lifting transitions to distributions.
This is a representation obligation in the formalization: equality of summed
point weights alone does not force arbitrary indexed weights to be nonnegative
or summable. For example, weights 2 and -1 on two copies of one configuration
sum to the same point mass as a single weight 1. Such a presentation is not a
probability distribution.

**Repair argument:** Require nonnegative, summable indexed presentations.
If the current weights are `w_i` and each positive branch has a normalized
successor family `v_ij`, the flattened weights are `w_i v_ij`. Zero parent
weights contribute zero regardless of unused successor data. For every finite
set of pairs, partition by the parent index. Each fibre has total at most
`w_i`, so the total is at most 1. Thus the pair family is summable. Absolute
Fubini gives `sum_ij w_i v_ij = sum_i w_i = 1`. Grouping equal configurations
preserves sums by the same absolute Fubini argument. If a grouped target
configuration has positive weight, at least one incoming positive pair exists;
its density is normalized by the local/global preservation theorem. Hence both
probability and positive-support normalization are preserved under lifted steps.

Checked in `DistributedDistribution`: `bind_family_probability`,
`same_distribution_at`, `same_distribution_mass`, `same_distribution_support`,
`distribution_step_probability`, and `distribution_step_normalized`.
`canonical_computation` and `computation_exists` construct legal infinite
computations for every normalized input. These proofs introduce no new axioms.

Existence of an infinite lifted computation requires no scheduler-independence
assumption. For each configuration choose one successor family if a transition
exists, and otherwise choose its singleton stuttering family. Classical choice
is already part of the shared foundations. Iterate this selector by the
flattening operation starting from the singleton input. Induction proves
normalization and total probability at every stage. This constructs one legal
computation; it does not establish that its limit exists or agrees with other
schedulers. Those statements require the separate monotonicity and commutation
arguments.

Distribution equality is expressed by equality of expectations for every
bounded scalar observable. Indicator observables recover each point's summed
weight, and the constant-one observable recovers total mass. For nonnegative
summable discrete presentations this is the usual equality of distributions:
partitioning the countable supports into equal-value fibres and applying
absolute Fubini gives equality for every bounded observable from equality of
point masses. This formulation keeps sums over the support index types; it
does not require summing over the universe of all higher-order configurations.

For operator-valued successful outputs, let `F(c)` be the successful cq-state
component at a fixed store, with zero used for failures, nonterminal controls,
and invalid density inputs. It is positive and has trace norm at most one.
Thus `sum_i w_i F(c_i)` is absolutely summable. Every linear functional on the
finite-dimensional operator space is bounded; composing it with `F` gives a
bounded scalar observable. Distribution equality therefore gives equal values
for all these functionals, which separate operators. This proves that the
weighted successful result is independent of the indexed presentation without
summing over the type of all configurations.

Checked in `DistributedWeighted`: `weighted_summable`, `weighted_norm`,
`weighted_positive`, and `weighted_same`. The padded-fibre Fubini argument is
checked for operator-valued mixtures as `weighted_bind_summable` and
`weighted_bind`; successor normalization is required only on positive parent
weights, so unused zero-weight branches impose no artificial condition.

For the monotonicity and convergence claim in Lemma 3.7, a successful
configuration is terminal, so a lifted transition retains its contribution
exactly by the terminal-stutter clause. Every other configuration contributes
zero initially; all successful successor contributions are positive. Multiply
this branchwise order by each nonnegative parent weight and sum. Absolute
Fubini identifies the iterated mixture with the flattened successor family,
and invariance under bounded-observable distribution equality identifies it
with the selected next stage. The successful cq-states therefore form an
increasing sequence. Each has total trace at most one by the probability and
normalization preservation proofs. The shared cq-state chain completeness
theorem supplies a cq-state supremum and convergence in the summable norm;
continuous coordinate evaluation gives the paper's pointwise limit at each
classical store. Together with `canonical_computation`, this proves existence
of at least one convergent result for every normalized input. It does not
prove that different schedulers have the same result; that is D1's separate
commutation obligation.

Checked in `DistributedResults`: `successful_component_step`,
`successful_state_step`, `stage_state_chain`, `computation_converges`,
`result_state_upper`, `result_state_least`, and `denotational_results_nonempty`.

For priority translation (Section 4), order the finite rendezvous list and
replace guard `b_j` by `b_j and not(or_{i<j} b_i)`. Two such guards cannot hold
at once: the later guard excludes the earlier one. If any raw guard holds,
its least enabled index satisfies the priority guard, so the disjunction is
unchanged. The sequential loop exits when no pair can rendezvous; applying
the paper's separate `term` filter removes exits with unmatched enabled local
guards. The guard lemmas alone do not establish scheduling independence or
justify deleting priority predicates in the completeness proof (D5).

## D9: Guarded-rule transfer through the conditional chain

**Location:** Tables 2–3, pp. 20–22, and the sequentialization used in their
soundness proofs. The shared classical language uses binary conditionals;
the distributed source language uses finite guarded alternatives. To transfer
their rules, inspect the guards in enumeration order. If a guard is enabled,
the conditional-chain precondition is exactly that branch's precondition;
otherwise continue with the tail. If no guard is enabled, the chain aborts.
The latter needs no extra premise for partial correctness. For total
correctness the input assertion must vanish where no guard is enabled,
which is precisely the published alternative coverage premise.

For repetition, restrict the invariant to the disjunction of guards before
the chain. This eliminates the uncovered abort case. Each selected branch
preserves the invariant by its original premise, giving the ordinary while
invariant premise. For total correctness a published ranking assertion
sequence bounds every enabled branch separately; therefore it also bounds
the selected branch at each store. The sequence is consequently a ranking
sequence for the conditional-chain while loop. These arguments prove rules
for the translated sequential statements independently of the global
stuttering correspondence. No global-network soundness theorem follows until
that separate correspondence is established.

For relative completeness of these source rules, use the translated weakest
precondition as invariant. Exclusivity makes every enabled source branch equal
to the selected branch of the conditional chain at that store. Consequently
the chain's weakest precondition implies each guarded branch premise. When no
guard is enabled, its total weakest precondition is zero, which establishes
the total alternative's coverage premise. For loops, unfold the classical
while weakest precondition once to obtain branch invariance. The shared
classical tail-effect ranking sequence, built from the difference between the
whole loop's termination effect and its finite unrollings, tends to zero. At a
store enabling a particular guard, exclusivity identifies that branch with the
chain, so the chain ranking inequality supplies the corresponding source
ranking inequality. Structural induction on well-formed source statements
then yields derivability of the weakest precondition; consequence yields every
semantically valid translated triple. The checked local-completion
correspondence transfers it to actual source execution in
`DistributedLocalHoare.sound_complete`.

For the network rule at the translated-kernel level, the initialization
commands establish a common invariant. Every rendezvous branch preserves that
invariant under its paired guard, so the conditional-chain loop preserves it
and exits with the invariant restricted to BLOCK. The final TERM test yields
the invariant restricted to TERM: partial correctness permits failure of that
test, while total correctness uses exactly the published BLOCK-to-TERM premise
to rule it out. A network ranking sequence bounds every rendezvous branch and
therefore bounds the selected conditional-chain branch, by the same pointwise
argument as source repetition. This proves the translated Dist and Dist-T
rules. Their premises are actual derivations in the separately defined shared
classical inference system. The checked sequentialization correspondence
transfers this translation soundness theorem to distributed operational
execution in `DistributedHoare.derives_sound`.

**Checked source rule results:** `DistributedGuardedRules.conditional_chain_valid`,
`alternative_partial`, `alternative_total`, `guarded_chain_valid`,
`ranking_transfer`, `repetition_partial`, and `repetition_total` establish the
rule premises. The independently inductive `derives` judgment has
`derives_translate_sound`, `derives_pre`, `derives_translate_complete`, and
`translate_sound_complete` for well-formed source statements. Direct compilation
and qualified Dune integration passed. Assumption audits of ranking transfer
and soundness/completeness report only inherited classical foundations and
the existing quantum-memory parameter.

## D10: Serial execution at rendezvous boundaries

**Location:** Section 4 and its operational correspondence proof, pp. 15–17
and Appendix C.2. A local body may itself take an unbounded random number of
primitive steps, so a single fixed primitive-step bound cannot replace one
rendezvous round of the sequential translation.

**Argument:** Use the already checked scheduler independence to choose a
serial scheduler. It finishes the initializations in process order. At each
boundary, all processes are waiting, except those with no communication
branches, which have already stopped. Select the first enabled rendezvous in
the same finite enumeration used by `rendezvous_commands`, perform its typed
assignment, and finish its two bodies in process order. Each completed body
returns its process to the same waiting boundary. The local correspondence
must be proved for all finite body horizons and then passed to its monotone
limit; no uniform termination bound is assumed.

When no rendezvous is enabled, only process-stop steps remain. They change
neither store nor quantum state. If every guard is false, finitely many such
steps reach the successful all-stopped configuration. If some guard is true,
that process can never take its stop step, and there is no communication to
change the store; hence no continuation can become successful. This is exactly
the final TERM filter of `successful_sequentialize`. Finite network-loop
unrollings then give one inequality by serial simulation; the finite-horizon
least-solution bound gives the other. Monotone convergence discharges the
unbounded numbers of rounds and body steps independently. This note records
the intended full argument; it is not a claim that the operational bridge is
already checked.

For the local one-step bridge, package the primitive branch maps as the
existing summable superoperator distribution. For an arbitrary continuation
assertion, the translated weakest precondition equals the sum of branch-map
duals applied to the translated residual weakest preconditions. Structural
induction uses kernel Fubini for sequence, exclusivity for guarded choice,
and the exact while-unfolding equation for repetition. Pairing this equality
with the input density gives the operational expectation: each normalized
branch is multiplied by its trace weight, recovering the unnormalized CP
output, including zero-weight branches. Assertions concentrated at one output
store and density trace separation then give operator equality, also with an
arbitrary continuation kernel. This equality alone does not prove eventual
completion. That requires finite loop unrollings, their finite local-step
bounds, and monotone convergence as described above.

The one-step part is checked as `DistributedLocalCorrespondence.local_pre`,
`local_pre_observe`, and `local_future_harmonic`; the last theorem allows an
arbitrary continuation kernel. Its assumptions audit reports only the
inherited classical foundations and the existing `qreg.G` memory parameter.

The finite local-completion approximation is itself a cq-kernel. At horizon
zero it is identity for `Finished` and zero otherwise. At horizon `n+1`,
compose the summable local instrument with the horizon-`n` kernel of each
residual statement; a failed store contributes the zero kernel. Positivity
gives monotonicity in the horizon. Associativity of summable kernel composition
gives the sequence bound: completing the left body by horizon `k` and the
right by horizon `l` contributes below the sequence's horizon `k+l+1`.
For a finite guarded family, take a common finite bound for its bodies (the
formal proof uses their sum). A loop unrolled `k` times therefore has a finite
bound obtained by adding the guard step, the sequence allowance, and that
common body bound at each unfolding. These are bounds for each
finite unrolling, not a bound on the original loop. Structural bounded
unrolling converges to the original translated kernel, so these finite local
kernels are cofinal below that translation. This supplies completed-body
adequacy without enumerating paths or assuming bounded termination time.

The finite kernels and their normalized operational equation are checked in
`DistributedLocalIterations.local_unfold_weighted`, with arbitrary residual
kernels and arbitrary suffix composition via `local_unfold_compose`.
`DistributedLocalIterationBounds.bounded_local_iter` proves cofinality of
bounded syntactic unrollings. `local_iter_least_output` passes the resulting
output bound through the limit, for every positive input operator and every
continuation kernel. No termination-rate or uniform loop bound is assumed.

The exact local limit is checked as
`DistributedLocalIterationLimits.local_iter_limit`, with arbitrary suffix
composition in `local_iter_suffix_limit` and trace-norm convergence in
`local_iter_cvg`. The complementary upper inequality is proved by induction
on the operational horizon, using the translated residual fixed-point
equation. Thus local completed-body adequacy is fully checked.

For scalar stopping estimates, the increasing local kernels act on any
cq-input as an increasing bounded family; the established kernel-limit
theorem identifies its trace-norm limit with translated execution. Continuous
expectation therefore gives convergence of the corresponding weakest-
precondition pairings. The weakest preconditions themselves are an increasing
effect family, and equality of all density pairings identifies their effect
supremum with the translated weakest precondition. Continuity of composition
and trace then gives pairing convergence for arbitrary input operators.
Closedness of scalar order passes a common bound through this limit.

Checked in `DistributedLocalExpectationLimits.local_wp_cvg`,
`local_wp_pairing_cvg`, and `local_wp_pairing_least`; the scalar theorems
allow arbitrary input operators and require no density normalization premise.

**Checked translated network rules:** `DistributedNetworkRules.list_ranking_transfer`,
`distributed_partial`, `distributed_total`, and `derives_translate_sound` passed
direct compilation and qualified Dune integration. Their assumptions audit
contains only inherited classical foundations and `qreg.G`. The subsequently
checked `DistributedHoare.derives_sound` transfers these rules to actual
operational execution using the proved correspondence;
`DistributedTotalCompleteness.sound_complete` now supplies both operational
soundness and relative completeness.

## Successful-state Bellman equation and leastness

For each projected configuration, define the finite-horizon successful state
recursively: horizon zero is its current successful component, and horizon
`n+1` mixes the horizon-`n` states of the chosen policy's successor family.
These are actual cq-states, since every projected successor family is a
probability family. Successful observations persist at terminal states and
are zero at other proper steps, so the horizon states form an increasing
chain. Their cq-state supremum defines a total value function, also on failed
and invalid configurations, without carrying normalization proofs in its
arguments.

The checked concrete diamond identifies the weighted horizon after *any*
legal projected step with the next horizon. Passing to the limit requires a
countable-mixture continuity proof: for weights `w_i`, the summable vectors
`i ↦ w_i F_n(i)` increase and have trace-norm sum at most one. The inherited
monotone convergence theorem for summable operator families gives convergence
in the sum norm. Pointwise convergence identifies its limit with
`i ↦ w_i F(i)`, and continuity of summation interchanges mixture and limit.
Thus the value obeys the Bellman equation for every enabled scheduler action.

For leastness, let a bounded positive candidate dominate the current
successful component and every weighted one-step continuation. Induction
bounds every finite horizon by the candidate; closedness of the positive
cone gives the same bound for the limit. This proves the leastness property
from the operational horizons, without assuming any desired network
correctness or scheduling theorem beyond the already checked diamond.

The serial invariant also records that a stopped process has every guard false.
This is initially vacuous. A local body can enter `Stopped` directly only for a
process with zero communication branches. An explicit stop transition checks
all its guards. Other processes preserve those guards because their writes are
disjoint from the stopped process's read footprint, including all variables in
its guard expressions. Rendezvous participants are waiting before the step and
executing afterwards, so no new stopped process arises from rendezvous. This
makes the residual translated kernel agree with the successful observation at
all-stopped configurations, even though the source loop still mentions every
process's guards.

`DistributedGlobalValue.weighted_monotone_cvg`, `value_bellman`,
`value_least_invariant`, and `value_denote` now check the above argument.
The invariant leastness theorem needs a suitable successor only for one legal
choice at each invariant configuration; positive successor branches preserve
the invariant. Zero-weight branches impose no such obligation.

**Checked serial foundations:** `DistributedSerialScheduler.rendezvous_indicesE`
identifies the ordered operational candidates with the translation's list;
`selected_rendezvous_command` and `selected_rendezvous_step` connect the first
enabled candidate to its translated body and a legal global transition.
`blocked_ready_step` shows that a ready blocked boundary admits only stop
transitions, and `boundary_terminates` constructs an actual finite path to the
all-stopped configuration under TERM. `DistributedResidualSemantics.residual_state`
is a bounded cq-state candidate, with `residual_initial_state` identifying its
initial instance with the translated kernel. `residual_local_focus` isolates
the first active body and its continuation. `DistributedStoppedInvariant.global_step_stopped_valid`
proves the stopped-guard invariant for every legal global step. These modules
have passed direct compilation and qualified Dune integration. The full
correspondence is subsequently assembled in
`DistributedCorrespondence.residual_value` and `.denote_program_sequentialize`.

**Checked upper inequality:** `DistributedRendezvousHarmonic.residual_rendezvous_step`
constructs the first enabled legal rendezvous and proves equality of its
weighted residual states. `DistributedSerialUpper.residual_successor` combines
this with local harmonicity, blocked stop steps, and terminal stutter.
`value_below_residual` applies invariant leastness, and
`denote_program_below_sequentialize` identifies the initial candidate with the
translated kernel. These results passed direct compilation and qualified Dune
integration. Completed-body adequacy and finite network-round approximation
provide the reverse inequality in the checked
`DistributedCorrespondence.residual_below_value`, as detailed below.

### Serial local completion and active process order

After a rendezvous, ready controls contain exactly two active process bodies.
Filtering idle controls from the enumeration preserves denotation because Skip
is a left unit for sequential composition. The ordinal enumeration lists the
first participant before the second when i<k. `DistributedActivePairs` proves
`active_program_filter`, `filter_pair_order`, and `residual_active_pair`, giving
the exact translated body order with no commutation assumption.

To compare a completed local body with the global operational value, keep the
other controls fixed and first use a finite number of local steps. At Finished,
use the endpoint continuation bound. At any active residual, choose its legal
parallel step and apply the global Bellman equation. The local instrument's
weighted unfolding matches this family exactly. Induction bounds each
normalized successor, and summable nonnegative mixtures preserve the order.
A failed store contributes zero. The established serial invariant (normalized
state, ownership, and validity of stopped guards) is preserved by each actual
step, so the endpoint condition need only hold on that invariant. Finally the
cofinality of finite local iterations with all nested-loop unrollings passes
the comparison to the full translated local denotation. This argument uses no
uniform runtime bound for probabilistic loop bodies.

For a finite list of active controls, complete the first body while holding
all other controls fixed, then complete the remaining list. Uniqueness of
process indices means updating the first process does not change any body in
the remaining list. Induction therefore equates the fold of local translated
bodies with successive complete local executions, using the preceding local
comparison for each body. Idle controls contribute Skip. The final
continuation is checked at the exact controls obtained by replacing each
completed active body with its process's idle control.

### Arbitrary cq-input operational extension

For an input cq-state Delta, assign each classical store s the nonnegative
weight w(s)=tr(Delta(s)). Positivity identifies this trace with its trace norm,
so the weights are summable with sum at most one. If w(s)>0, normalize its
quantum component to Delta(s)/w(s); otherwise positivity and trace zero force
the component to be zero, and any fixed normalized density may represent that
zero-weight input. Add a distinguished zero-output branch with weight
1-sum(w) to obtain a probability mixture. The actual operational denotation
on each positive branch is the previously constructed scheduler-independent
`denote_program` at its normalized point configuration. The resulting cq-state
mixture defines operational execution on arbitrary input cq-states.

The implementation may omit the distinguished zero-output branch: the existing
`Distr` and `CQStateMixture.mix` accept subprobability weights, and adding the
missing mass at the zero state contributes the zero summand. This is the same
mixture, including inputs of trace zero.

When normalized point denotations equal a linear classical kernel K, each
weighted component equals K(s,t)(Delta(s)) by homogeneity; zero-trace inputs
contribute zero by positivity. Summing over s therefore gives exactly
`CQKernel.apply K Delta`. Absolute summability follows from trace nonincrease
and the summable input masses. This proves the arbitrary-input transfer
instead of defining operational execution to be the translated kernel.

The extension is checked in `DistributedCQInput`: `weights` packages the
trace distribution, `normalized_density` and `component_reassemble` prove
normalization including zero components, and `run` is the actual operational
mixture. `run_point` recovers the normalized-input denotation independently
of sequentialization; `run_kernel` transfers a proved normalized-point
correspondence to all cq-inputs. The assumptions audits for these results
and the exact local limits report only inherited classical foundations and
the existing `qreg.G` memory parameter.

`DistributedHoare.run_translate` transfers this mixture to the serialized
kernel, and `.derives_sound` proves the independent network inference rules
sound for the actual mixture execution. `.valid_normalized_iff` proves that
normalized point configurations suffice to test these arbitrary-cq-input
judgments. Its normalization step is independently checked as
`DistributedNormalizedTests.operator_le_normalized`: positive-trace densities
are rescaled to trace one, while a positive zero-trace operator is zero.
`DistributedLocalHoare.sound_complete` likewise transfers the independent
guarded source rules to the actual finite-local-completion kernel limit.
These modules passed direct compilation and qualified Dune integration.

**Full serial correspondence checked:** `DistributedLocalLower.local_iter_lower`
and `.translated_local_lower` prove the finite and unbounded local comparison.
`DistributedActiveLower.active_program_lower` completes an arbitrary finite
unique process list, and `DistributedControlCompletion.finish_controls_ready`
proves its boundary is ready after enumerating all processes.
`DistributedCorrespondence.residual_below_value` combines this with
`DistributedNetworkLower.network_tail_lower`. Together with the checked upper
comparison, `.residual_value` gives exact equality at every configuration
satisfying the serial invariant. `.denote_program_sequentialize` and
`.denote_program_point` specialize to actual initial programs and normalized
input densities. Thus the translation equality is proved from actual global
steps, local executions, and limits; it is not a premise of the Hoare rules.

### D5 replacement: independent network completeness

For partial correctness choose I=wlp(network_tail,Q). At ready controls the
checked residual correspondence and Bellman equation apply to every enabled
rendezvous. Completing both local bodies restores the ready controls and
therefore preserves I. This supplies every guarded branch premise, including
branches excluded by the serialized priority guard. Serialized validity
rewrites as P<=wlp(initialization,I), so classical relative completeness gives
the initialization derivation. At TERM the tail is Skip; consequently
TERM-and-I<=Q. The independent Dist rule followed by consequence proves the
required triple without the paper's false priority-dropping equality.

This argument is checked in `DistributedAllRendezvous.all_tail_invariants`,
`DistributedNetworkPre.initialization_pre` and `.tail_pre_post`, and
`DistributedPartialCompleteness.derives_pre_partial`,
`.derives_complete_partial`, and `.partial_sound_complete`. The last theorem
relates the independent network inference system to actual arbitrary-cq-input
operational validity. Direct compilation and qualified Dune integration passed.

For total correctness a candidate ranking comes from finite primitive-step
horizons, not from a claimed uniform bound on the local bodies. Choose enabled
step descriptors using only controls and classical memory. Their completely
positive branch maps define, by finite recursion, effects H_k for successful
postcondition expectation within k primitive steps. The concrete scheduler
independence theorem identifies these effects with the successful finite-stage
observations for every normalized quantum input. Thus H_k increases to the
full successful effect F. Use rank_0=F and rank_(k+1)=F-H_k at ready controls.
The differences are effects, decrease, and tend to zero.

The effect construction and limit are checked in
`DistributedHorizonEffects.horizon_assertion_pairing`,
`.horizon_assertion_mono`, `.horizon_assertion_sup`, and
`.horizon_assertion_cvg`. The actual effect difference is justified by
`.remainder_effect`; `.rank_assertion_decreasing` and `.rank_assertion_zero`
prove the two sequence conditions. `.rank_assertion_pairing` identifies all
indices, including zero, with the scalar operational progress potential.
Direct compilation and qualified Dune integration passed.

Bellman equality for F and finite-horizon unfolding for H_k show that the
expected remainder is a supermartingale across each primitive step. Finite
local completion induction, followed by the checked local-iteration limit,
therefore preserves the upper bound through an entire body without a runtime
bound. A rendezvous itself consumes one primitive step, giving the required
one-level ranking decrease for every enabled branch. The total invariant is
F=wp(network_tail,Q). A blocked non-TERM state has zero successful denotation,
so the required deadlock exclusion holds on the support of F. The argument
does not posit a ranking or semantic correctness axiom.

This total construction is checked in
`DistributedHorizonRemainder.progress_step` and `.progress_superharmonic`,
`DistributedActiveStopping.active_program_stopping`, and
`DistributedNetworkRanking.enabled_rank_bound` and `.tail_network_ranking`.
`DistributedTotalCompleteness.derives_pre_total` and
`.derives_complete_total` discharge the actual Dist-T rule. Its
`.sound_complete` theorem combines both correctness modes and equates the
independent network inference system with actual arbitrary-cq-input
operational validity. Direct compilation and qualified Dune integration
passed. Completeness is relative to the user-approved bounded semantic
assertion domain and its semantic implication premises, as recorded in D2.

### Lemma 3.4: packaging global Change and Access

For the fixed ambient quantum memory used by this development, a well-owned
global transition has an enabled descriptor: a local instruction, a completed
process, or a communication assignment. Its branch index depends only on that
instruction. The local instrument gives completely positive maps with a
trace-nonincreasing sum, branch weights equal to output traces, and normalized
branch states. Lifting its residual statement through the descriptor gives
the global control vector. Local writes are contained in the participating
processes' write footprints, and local quantum maps commute with every map on
disjoint quantum registers. Ownership preservation keeps every residual
statement within its source process's classical and quantum footprints.

If two classical stores agree on all source-process reads, the same descriptor
remains enabled. Structural induction on its instruction shows that selected
guards, residual controls, and completely positive branch maps agree; the
output stores agree on the read footprint as well, and both leave all names
outside the write footprint unchanged. Therefore the same branch maps replay
the transition at any other normalized quantum input and agreeing classical
store. Failure is retained as the explicit `None` store, and zero-weight
branches may remain in the indexed family without affecting its distribution.
This is the global wrapper argument; quantification over different ambient
memory types is a separate obligation, not an assumption of this argument.

`DistributedChangeAccess.global_step_change_access` packages the global
instrument in `.change_access_witness`; `.initial_change_access` specializes
it to source programs. The witness includes a summable completely positive
branch family, a trace-nonincreasing sum, exact trace/normalized-state
realization, classical frame and access properties, replay from agreeing
stores, and residual ownership. `.descriptor_map_supported` moreover gives
an actual completely positive map on the union of source-process quantum
registers whose lift is each branch map. Direct compilation, qualified Dune
integration, and an assumption audit passed; only inherited classical
foundations and `qreg.G` occur.
