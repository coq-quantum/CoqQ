# Classical-quantum states

Source: Feng and Ying, *Quantum Hoare Logic with Classical Variables*,
Definition 3.1 (PDF p. 9), Lemma 3.3 (p. 10), and Lemma 4.4 (pp. 17–18).

The classical index type is an arbitrary `choiceType`, not a finite or
countable store space. The Hilbert space is a CoqQ `chsType`, as appropriate
for a fixed finite set of finite-dimensional quantum variables. We reuse
`{vdistr I -> 'End(H)}` with CoqQ's trace norm. Positive operators have trace
norm equal to their trace. Consequently the distribution norm bound is
exactly the paper's total-trace bound, not an operator-norm relaxation.
Absolute summability implies countable nonzero support by the existing
`summable_countn0`; it does not require the whole classical state space to be
countable.

## Missing step in Lemma 3.3

Pointwise completeness alone does not establish that the supremum is still
a cq-state. For an increasing sequence of positive operator-valued
distributions, positive trace-norm additivity and the uniform total-trace
bound give convergence in the space of absolutely summable families
(`vdnondecreasing_is_cvgn`). Its limit is positive and has total trace at
most one by closedness; its support is countable by absolute summability.
Pointwise evaluation is continuous, so the limit dominates every member.
If another distribution dominates every member, closedness of the positive
cone shows that it dominates the limit. This proves the least-upper-bound
claim without replacing the uncountable classical store space by a finite
space. The zero distribution is the least element.

Formal names in `state.v`: `state`, `support_countable`, `mass`,
`mass_trace`, `mass_ge0`, `mass_le1`, `component_density`, `bottom_least`,
`chain_converges`, `chain_sup_upper`, `chain_sup_least`.

The existing summability and finite-dimensional quantum foundations are
dependencies of these proofs. This note does not claim that assertion
spaces have the same completeness property; that separate claim has a
counterexample recorded in `PROOF_GAPS.md`.

## Missing summability step in Lemma 4.4

A program kernel `K(i,j)` is completely positive, and for any finite set
`B` of outputs the map `sum_(j in B) K(i,j)` is trace nonincreasing. For
positive input components `d(i)`, positivity and trace-norm additivity give
`sum_(j in B) ||K(i,j)(d(i))|| <= tr(d(i))`. Summing over any finite input
set bounds every finite rectangular double sum by `tr(d)`. Absolute
summability therefore permits changing the order of sums. In particular
`out(j) = sum_i K(i,j)(d(i))` is absolutely summable and positive, and its
total trace is at most `tr(d) <= 1`. This argument applies to every cq-state,
including ones with infinite support; no finite-support approximation is
used as the final semantics. It is implemented in `kernel.v`.

The same finite-sum estimate for a single instrument requires only positivity
of its input operator, not the unit trace bound. `instrument.v` exposes
`CQInstrument.instrument_psum_bound`, `instrument_outputs_summable`, and
`instrument_sumE`. The last theorem pushes summable outcome operators to
their updated classical stores and commutes evaluation with their sum. It
retains multiplicities when distinct outcomes lead to the same final store,
and supplies the atomic case of the route/denotation correspondence.

For sequential composition, the family indexed by input and intermediate
stores consists of positive terms `L(k,j)(K(i,k)(d(i)))`. Each outer map
`L(k,j)` is trace nonincreasing, so its norm is bounded by the norm of
`K(i,k)(d(i))`. The preceding rectangular bound therefore also bounds this
family. Absolute convergence justifies moving superoperator evaluation
through each sum and exchanging input/intermediate sums. Thus applying the
composed kernel equals successive application to states. The theorem is
`CQKernel.apply_sequence`.

## Mixtures for distributed computations

For nonnegative weights with total at most one and cq-states `d_i`, regard
`w_i d_i` as elements of the complete space of summable operator families.
Their norms are at most `w_i`, since the norm of a positive cq-state is its
total trace. Thus the outer family is summable. Its sum is positive
pointwise (closedness of the positive cone), and has norm and total trace
at most one. Continuity of point evaluation gives
`mix(j) = sum_i w_i d_i(j)`. This proves validity of mixtures over arbitrary
choice-type index sets; absolute summability supplies countable support.
Formal names: `CQStateMixture.terms_summable`, `mix_positive`,
`mix_l1_bound`, `mix`, and `mixE` in `mixture.v`.

For any effect assertion, its trace pairing extends to the complete space of
summable operator families as a linear map of norm at most one. Consequently
it commutes with the absolutely convergent outer sum defining a mixture.
This proves that the expectation of a mixture is the weighted sum of the
component expectations, without a finite-support restriction. The checked
theorems are `CQMixtureExpectation.pairing_linear` and `expect_mix` in
`mixture_expectation.v`.

## Passing kernel limits through arbitrary input states

For increasing kernels K_n bounded by K with pointwise limit K, positivity
of rho(i) implies K_n(i,j)(rho(i)) increases and is bounded by
K(i,j)(rho(i)). For a fixed output j these families are absolutely summable
over input i by the kernel row estimate. Monotone convergence in the space
of summable operator families gives a norm limit; continuity of evaluation
identifies every component with K(i,j)(rho(i)). Continuity of summation then
gives pointwise convergence of the output cq-states. The output cq-states
themselves form an increasing chain, so their cq-state convergence theorem
upgrades this to convergence in the summable-family norm. These arguments
apply in particular to the increasing finite unrollings of a while loop.
Composing with the continuous expectation functional proves convergence of
their expectations, the limit step needed for Hoare loop soundness.

The kernel limit bridge is checked as `CQKernelLimits.apply_cvg_monotone`,
`unroll_apply_cvg`, and `unroll_expect_cvg` in `kernel_limits.v`.

## State separation, decreasing limits, and kernel linearity

Classical Lemma 3.10(1), and distributed Appendix B.2(1), also characterize
state order through expectations. In the approved full effect domain, test
the inequality against an effect concentrated at one classical store. The
result is the inequality of all density/effect trace pairings at that store,
which characterizes operator order. Equality of all such expectations gives
state equality. This argument concerns all semantic effects; restricting
the separating tests to the paper's definable-fiber subclass would additionally
require its finite-formula approximation argument.

Checked in `state_expectation.v` as `CQStateExpectation.at_store`,
`expect_at_store`, `state_le_iff_expect`, `state_eq_iff_expect`, and
`pairing_ext`. The last theorem also separates arbitrary summable operator
families, which is used below for signed linear combinations.

For a decreasing cq-state sequence, negate its members in the complete space
of summable operator families. This is an increasing sequence bounded above
by zero, so the existing monotone-convergence theorem gives a norm limit.
Negating again gives convergence of the original sequence. Closed positivity
and the trace bound package the limit as a cq-state. Closedness of order
makes it below every member and above every common lower bound. Continuity
of expectation proves classical Lemma 3.11(2)/distributed Appendix B.3(2).

Checked in `state_decreasing.v` as `CQStateDecreasing.decreasing_converges`,
`chain_inf`, `chain_inf_cvg`, `chain_inf_lower`, `chain_inf_greatest`,
`chain_inf_pointwise`, and `expect_chain_inf`.

For classical Lemma 4.4(2)/distributed Lemma 3.11(2), let the weighted input
family be absolutely summable in the cq trace norm and suppose its sum is a
cq-state d. Kernel application contracts the trace norm on each positive
component. Thus the weighted output family is absolutely summable as well,
including real or complex signed weights. Pair an output sum with an arbitrary
effect. Continuous linear pairing commutes with the sum, and wp duality moves
each kernel from its state to the effect. Commuting pairing through the input
sum then yields the expectation of applying the kernel to d. State separation
gives equality of the two output families. Nonnegative subprobability mixtures
are an immediate special case. Absolute summability is the existing unordered
sum convention; no conditional rearrangement of signed series is used.

Checked in `kernel_linearity.v` as `CQKernelLinearity.weighted_norm_bound`,
`weighted_output_summable`, `apply_weighted_sum`, and `apply_mix`. The general
series theorem assumes explicitly that the input sum is a cq-state; a signed
combination need not itself be positive or have mass at most one.

For distributed Lemma 3.11(2), `DistributedHoare.run_translate` identifies
the actual operational run on every cq-input with the kernel of the
successful serialized command. Substitute this identity for each input and
for their sum in the preceding kernel theorem. The output summability bound
and the full signed-series equality therefore hold for actual distributed
runs; no choice of scheduler or finiteness of the input support is added.

Checked in `../distributive/linearity.v` as
`DistributedLinearity.run_weighted_summable`, `run_weighted_sum`, and
`run_mix`.
