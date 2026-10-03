# Expectation: convergence and bounds

Source: Feng and Ying, *Quantum Hoare Logic with Classical Variables*,
Definition 3.5 (printed page 16:11), Definition 3.7 (16:12), and the
expectation properties following that definition. This note concerns a
fixed finite-dimensional quantum space. Assertions and states on different
variable sets first require the paper's tensor extension/partial trace;
that separate construction is not claimed here.

Definition 3.5 requires both a countable image and definability of each
nonempty fiber by a classical assertion. `CQAssertion.assertion` records
those conditions explicitly. The classical formula type and its
satisfaction relation are parameters of the assertion language, not
assumptions of theorems about program correctness. We make no claim that
this restricted assertion domain is closed under arbitrary increasing
limits.

On 2026-10-03 the user approved using the larger semantic domain of all
effect-valued functions for limits, while retaining Definition 3.5's
countable-image/definable-fiber records as a distinguished subclass.
`semantic_assertion` is this larger domain. Its order is pointwise; reflexivity,
transitivity and antisymmetry follow from operator order and function
extensionality. The constant zero and identity functions are bottom and top.
For a countable increasing chain c, define its supremum at i to be the
already-proved effect supremum `LfunCPO.oflub (fun n => c n i)`. Each pointwise
chain has that least upper bound, so the resulting function is simultaneously
an upper bound at every index and below every common upper bound. These
claims are `semantic_le_refl`, `semantic_le_trans`, `semantic_le_anti`,
`semantic_bottom_le`, `semantic_le_top`, `semantic_sup_upper`,
`semantic_sup_least`, and `semantic_omega_cpo`. This repaired theorem is
explicitly about the larger domain; it is not a proof of the paper's false
closure claim about the distinguished subclass.

Definition 3.7 writes an infinite sum. The needed convergence step is as
follows. For an effect-valued function P and a positive operator family
rho with summable trace norm, each scalar term Tr(P(i) rho(i)) is real and
nonnegative: it is the trace of a product of positive operators. Since
0 <= P(i) <= identity, positivity of rho(i) also gives

    0 <= Tr(P(i) rho(i)) <= Tr(rho(i)) = ||rho(i)||_1.

Every finite sum of absolute values is therefore bounded by the
corresponding finite sum of trace norms of rho. The latter family is
summable, so this proves absolute summability on the entire classical
state space, without assuming the index type finite or countable.
Nonzero state support is countable by the existing
`summable_countn0`, and zero-state terms vanish, so summing over all indices
is the same definition as the paper's sum over support.

Taking limits of finite sums proves nonnegativity and monotonicity in P.
The finite-sum upper bound can be sharpened to Tr(sum rho): trace is
linear on finite sums, each finite state sum is below the full positive
state sum, and trace is monotone. Since the positive sum has trace norm
at most one, expectation lies in [0,1]. This proof also establishes that
the expectation is real despite the ambient scalar field being complex.

The formal results in `assertion.v` are `expect_term_ge0`,
`expect_term_le_trace`, `expect_term_norm_le`, `expect_summable`,
`expect_ge0`, `expect_le_trace`, `expect_le1`, `expect_real`, and
`expect_mono`. Their domain is all effect-valued functions as a scalar
integration lemma; applying them to the recorded paper assertions does
not relax either of Definition 3.5's conditions.

Boundary equations use the same justified sum: the zero effect contributes
zero, the identity effect gives total trace, and a state concentrated at a
single classical memory contributes exactly its one trace pairing. A
Boolean guard restricts an effect by replacing it with zero off the guard.
The expectation of a binary conditional effect splits into the two guarded
expectations because the scalar equality holds at every index and both
scalar families are summable. These are `expect_zero`, `expect_identity`,
`expect_singleton`, `expect_mask_le`, and `expect_conditional`.

For complement effects, Tr((I-P)rho) + Tr(P rho) = Tr(rho)
pointwise. Absolute summability justifies adding the scalar sums, yielding
`expect_complement_sum` and `expect_complement`. This is the algebraic
bridge between the complement form of partial validity used by upstream
CoqQ and the paper's explicit lost-trace inequality.

## Continuity and order separation for completeness

For a fixed effect family P and any absolutely summable operator family x,
the trace pairing extends linearly to
`L_P(x) = sum_i Tr(P(i) x(i))`. Hölder's trace inequality gives
`|Tr(P(i)x(i))| <= ||P(i)||_infinity ||x(i)||_1 <= ||x(i)||_1`.
The sum is therefore absolutely convergent, and `|L_P(x)| <= ||x||_1`.
Applying this estimate to x-y proves continuity, including for differences
that are not positive. Consequently any convergence of cq-states in the
summable-family norm implies convergence of their expectations. Applying
this to the established increasing cq-state limit proves the state-limit
part of Lemma 3.11 without assuming finite classical support.

Conversely, testing an expectation inequality against every cq-state includes
the singleton state at each classical store with an arbitrary partial density
operator. These tests characterize Löwner order at that store by `lef_trden`.
Thus pointwise assertion order is equivalent to comparison against all state
expectations. This is the order-separation step required by weakest
precondition completeness; it does not assume that correctness theorem.

The corresponding results are developed in `expectation.v`.

## Initial validation and assumptions

`assertion.v` was checked with Rocq 9.1.1 in switch `rocq.9.1` against the
workspace's compiled `quantum` theory. `Print Assumptions` was checked for
`expect_summable`, `expect_le1`, `expect_mono`, `expect_identity`, and
`expect_conditional`. The only reported axioms are inherited foundations:
`ClassicalDedekindReals.sig_not_dec`,
`ClassicalDedekindReals.sig_forall_dec`,
`boolp.propositional_extensionality`,
`boolp.functional_extensionality_dep`,
`FunctionalExtensionality.functional_extensionality_dep`,
`Epsilon.epsilon_statement`, and
`boolp.constructive_indefinite_description`. No newly declared axiom,
admission, or assertion-specific closure assumption is used.

## Assertion limits

For an increasing effect family P_n and a fixed cq-state rho, consider the
scalar families a_n(i)=Tr(P_n(i) rho(i)). They increase pointwise and are
bounded above by the summable family Tr(rho(i)). Monotone convergence in
the complete space of summable scalar families therefore supplies a norm
limit. Continuity of point evaluation and of finite-dimensional trace
pairing identifies that limit with Tr((sup_n P_n)(i) rho(i)) at every i.
Continuity of summation gives convergence of the expectations. For a
decreasing effect family, apply the increasing result to I-P_n and use
Exp(rho,I-P)=Tr(rho)-Exp(rho,P). This proves the assertion-limit clauses
of Lemma 3.11 in the user-approved effect-function domain.

Checked results: `CQExpectation.expect_cvg`, `expect_chain_sup`, and
`semantic_le_iff_expect` in `expectation.v`;
`CQExpectationLimits.effect_sup_cvg`, `semantic_sup_cvg`,
`expect_semantic_sup`, and `expect_semantic_inf` in `expectation_limits.v`.
The corresponding Dune targets pass after the cqwhile language refactor.
