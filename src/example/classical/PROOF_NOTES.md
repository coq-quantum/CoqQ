# Mathematical arguments and paper gaps

These notes consolidate the original proof arguments. Historical build checkpoints refer to the former file layout; current validation is in [VALIDATION.md](VALIDATION.md). Source-file references have been updated to the topic files.

<a id="case-studies"></a>

## CASE STUDIES

### Classical algorithm case studies

#### Grover search (Section 7.1, Examples 4.5 and 4.11)

The register has finite basis T, with a nonempty proper set W of marked basis
states. Let N = |T|, M = |W|, and theta = asin(sqrt(M/N)). Write the uniform
state as g + b, its marked and unmarked components. Orthogonality of the basis
gives <g,b> = 0, ||g||² = sin²(theta), and ||b||² = cos²(theta). Both denominators
are nonzero because 0 < M < N. Define

    u(r) = sin(r)/sin(theta) g + cos(r)/cos(theta) b.

The phase oracle negates g and fixes b. Reflection about the uniform state,
followed after that oracle, sends u(r) to u(r + 2 theta), by the sine and cosine
addition identities. Since the uniform state is u(theta), K iterations give
u((2K+1)theta). The projector onto W keeps its g component, so its expectation
is sin²((2K+1)theta). `algorithms.v` checks this concrete matrix argument;
`ClassicalGrover.iteration_success` is the resulting equality.

The connection with the actual unbounded language loop is separate. If an
integer counter starts at k and the bound is k+n, the guard is true for each
of the first n counter values, then false. Induction on n constructs a finite
execution certificate using the real while-step constructors, ending at the
store obtained by n increments. Its superoperator is the n-fold composition
of the lifted rotation channel. The theorem
`ClassicalAlgorithmLoops.counted_unitary_execution` checks this induction;
`counted_unitary_denote` identifies its full denotation. This uses
`ClassicalDeterministic.execution_denote`, proved from the unbounded loop
unfolding theorem, and is not an approximation of the loop semantics.

For arbitrary classical or quantum input, initialization resets the chosen
register; the preparation unitary then produces the uniform state. Composition
of a unitary form channel with initialization at v is initialization at Uv.
The same identity under register lifting shows that the complete prefix resets
the register to the K-fold rotated uniform state, leaving the rest of memory
subject to the inherited local-channel semantics. Consequently, the backward
transformer of the computational measurement and the classical success test
is the lifted projector onto W. The initialization backward transformer is
<v, Pv> times the identity. Combining these identities gives precisely the
constant effect sin²((2K+1)theta) I for both total and partial preconditions:
the finite counted loop and all its primitives are trace preserving.

The checked final program and probability connection are in
`algorithms.v`: `grover_prefix_execution` and `grover_prefix_denote`
identify the complete prefix, `measurement_success_pre` identifies the
measurement transformer, `grover_success_pre` proves the exact scalar
precondition, and `grover_correct` derives the resulting total or partial
Hoare judgment in the independent inference system `CQHoare.derives`.
The general supporting deterministic weakest-precondition and channel
composition lemmas are in `semantics.v`.

For qubit tuples, the uniform preparation agrees on the initialized zero state
with the paper's sequence of Hadamards. No equivalence of those two unitaries
on arbitrary inputs is needed or asserted.

#### Remaining Section 7 examples

The QFT circuit and its actual nested-loop program are checked in `algorithms.v`
and `algorithms.v`; see [fourier notes](PROOF_NOTES.md#fourier-notes). Phase estimation has checked
loop execution, exact outcome probabilities, and derived total/partial
Hoare judgments in `algorithms.v`. The literal order-finding program has a checked exact Fourier/Born
outcome formula for its actual measured output, including its final
postprocessing assignment; see [order finding notes](PROOF_NOTES.md#order-finding-notes). Shor has checked
partial factor safety and an independent total lower bound from its
immediate gcd branch. The printed phase and order-finding success claims
are false; the larger Shor bound remains unproved. The concrete theorem
`ClassicalPhaseCounterexample.printed_phase_bound_counterexample` checks the
phase claim's failure at phase 1−1/1024 with three measured qubits; see
[phase counterexample notes](PROOF_NOTES.md#phase-counterexample-notes). The phase-estimation ordinary-distance error claim requires the
correction described in [proof gaps](PROOF_NOTES.md#proof-gaps), C6, and the printed order-finding
postprocessor has the counterexample C7. No corrected claim is silently
assumed here.

#### Phase estimation: exact spectral identities (Section 7.3)

The following identities do not use the disputed concentration claim C6. For
a normalized eigenvector u with Uu = exp(2 pi i phi)u, induction gives
U^j u = exp(2 pi i j phi)u. Therefore the controlled-power operator
sum_j |j><j| tensor U^j sends the uniform control state tensor u to

    (1/sqrt(2^t)) sum_j exp(2 pi i j phi) |j> tensor u.

This operator is unitary because each block U^j is unitary. The control state
is also a diagonal unitary applied to the uniform state, which proves its
normalization without any finite-sum cancellation assumptions. The adjoint
Fourier transform sends it to a state whose amplitude at output m is

    (1/2^t) sum_j exp(2 pi i j (phi - m/2^t)).

The proof expands the two basis sums, uses orthonormality to keep equal-index
terms, and combines conjugate exponentials. If phi = m/2^t exactly, the
pre-transform control state is the m-th Fourier basis vector, so the output
is exactly |m>. These are pure spectral calculations. The checked identities are `phase_vector_dot`, `output_state_dot`,
`phase_output_amplitude`, `exact_phase_output`, `eigen_power`, and
`phase_kickback` in `algorithms.v`. The actual nested program is checked
in `algorithms.v`: it retains the paper's one-based outer counter,
inner bound 2^(t-x), repeated controlled-U, initialization/preparation, inverse
Fourier gate, and finite control-register measurement. Dynamic indices are
explicitly guarded and abort outside their valid range. Its loop channels are connected gate by gate in `algorithms.v` and
`algorithms.v`.

#### Shor arithmetic: nontrivial square roots (Lemma 7.2(1))

Take the canonical residue s of a nontrivial square root of one modulo N,
so 1 < s and s+1 < N. The congruence gives N | (s²-1), hence
N | (s-1)(s+1). If gcd(N,s-1)=1, Gauss's divisibility lemma implies
N | s+1, contradicting 0 < s+1 < N. Thus gcd(s-1,N)>1. It divides N,
and it is at most s-1 < N, so it is a nontrivial factor. This proves the
paper's disjunction by its first alternative for canonical residues; no
assumption about the disputed order-finding postprocessor is used.

The checked Shor arithmetic names are `nontrivial_sqrt_factor` and
`nontrivial_sqrt_factor_mod`. `convergents_stable` proves that the Euclidean
continued-fraction recursion has stabilized once its fuel reaches the input
denominator. The printed minimal-denominator rule is implemented without a
modular-order filter in `printed_postprocess`; the checked results
`printed_quarter_counterexample`, `printed_three_quarters_counterexample`, and
`two_mod_fifteen_order` support C7. These counterexamples do not formalize a
repaired postprocessor.

For the phase-estimation inner loop, fixing the outer counter at i+1 fixes
its bound M=2^(n-i-1) and its controlled gate. Distinct counter names imply
that updating y preserves x. Induction on the remaining M-y iterations
therefore constructs a real unbounded-loop execution certificate, composing
one controlled-U channel at each true guard and reaching the false guard
at y=M. This is the same finite-execution/unbounded-denotation argument as
the Grover counter, with an explicit store-preservation step for x.

For the local-register channel calculations, validity of a pair register
implies that its two projections have disjoint memory footprints. The
existing `tf2f_pairV` identity identifies an operator on the pair with the
tensor product of its component operators after a memory-set cast. Lifting
removes that cast; tensoring with the identity then yields exactly the
original component's lifted operator. Applying `formso` gives the same
identity for the component unitary channel. These are representation
identities for the actual cqwhile registers, not independence assumptions.

The phase-vector product identity follows from the binary expansion
j = sum_i b_i 2^(n-i-1). Each tensor factor has computational amplitude
(1/sqrt(2)) exp(2 pi i b_i 2^(n-i-1) phi). Multiplying the n factors
recovers exactly the phase-vector amplitude. This includes n=0, using the
empty product and the unique empty bit tuple. The checked results are
`binary_weight_sum`, `binary_weight_sum_real`, `phase_vector_coefficient`,
and `phase_vector_product` in `algorithms.v`.

At stage i of phase estimation, the first i control factors carry their
phases and all later factors are zero. The Hadamard on i produces phstate(0).
Applying controlled-U exactly 2^(n-i-1) times multiplies its one-component
by exp(2 pi i 2^(n-i-1) phi), because the target is an eigenvector, and leaves
the target unchanged. The resulting product is the next invariant layer.
Induction on the sequence of stages, followed by the product identity above,
yields phase_vector tensor u. This is the natural-language argument for
`algorithms.v`. The checked lemmas are `estimation_stageE`,
`estimation_circuit_prefixE`, and `estimation_circuit_eigen`.

For complete initialization of a valid pair register, choose the computational
basis on each component in the Kraus representation of the reset channel.
The composed Kraus operator indexed by (i,j) is the tensor product of the
two reset Kraus operators, hence the pair-reset Kraus operator indexed by
the pair basis vector. Register lifting and the footprint cast preserve this
identity. `initial_register_pair` checks the result. The phase program can
therefore be reduced to initialization at output_state tensor u. Pulling a
computational outcome projector backward gives its Born probability times
the identity, with <u,u>=1. For an exactly representable phase m/2^n, the
output_state identity makes this probability one. These arguments target
`algorithms.v`. The checked names are `phase_prefix_actionE`,
`phase_reset_execution`, `phase_outcome_pre`, `phase_outcome_formula`,
`phase_estimation_correct`, `phase_exact_pre`, and `phase_exact_correct`.
These cover the actual program and its exact distribution for both total and
partial correctness, without the disputed concentration claim C6.

#### Phase amplitudes away from an exact grid point

This calculation supports Section 7.3 without changing the disputed error
metric in C6. Put N=2^t and delta=phi-m/N. The already checked basis expansion
reindexes through the bijection between Boolean tuples and ordinals below N
to give amplitude A=(1/N) sum_(j<N) exp(2 pi i delta j). If
exp(2 pi i delta) is not one, the finite geometric-sum identity gives

    A = (1/N) (1-exp(2 pi i N delta))/(1-exp(2 pi i delta)).

Every exponential has modulus one: its product with its conjugate is the
exponential at zero. Thus the numerator has modulus at most two by the
triangle inequality, giving

    |A| <= (2/N)/|1-exp(2 pi i delta)|.

The denominator is explicitly nonzero in the off-grid case. This pointwise
bound and the exact formula do not assert the paper's false uniform
ordinary-distance success claim or adopt a new distance convention.


Checked in `algorithms.v`: `ClassicalPhaseBounds.amplitude_ordinal`,
`amplitude_geometric`, `amplitude_bound`, and `probability_bound`. Squaring
the nonnegative amplitude bound yields the corresponding Born-probability
bound. The original norm estimate uses the exact finite geometric sum, not
a finite approximation to any program loop.

#### Literal Shor wrapper and partial factor-output safety (Table 6, page 41)

The wrapper samples x uniformly from the finite set {1,...,N-1}, where N>1.
Construct this normalized distribution by pushing the constant mass
1/(N-1) on the finite ordinal type of size N-1 along i ↦ i+1. Its sum is
(N-1)/(N-1)=1, and its support is exactly the printed sampling range.

For any sampled x, if gcd(x,N)>1, then gcd(x,N) divides N and is at most
x<N, so assigning that gcd establishes the nontrivial-factor predicate.
Otherwise the wrapper runs the order-finding command. The explicit failure
option aborts. A returned value z is accepted by the printed evenness and
x^(z/2)≠-1 mod N guard before computing the two gcd candidates. Finally each
successful assignment to y is guarded by the nontrivial-factor predicate on
its candidate; if neither candidate satisfies that predicate the program
aborts. Therefore all terminating output mass is supported on stores where
y is a nontrivial divisor of N. This argument holds for any order-finding
command without a correctness premise: the partial Top rule handles its
prefix, and the final candidate checks prove safety. It claims no positive
success probability and does not repair the incorrect denominator selector
identified in C7. The independent core calculus derives this partial Hoare
judgment by its checked soundness/completeness and ordinary command rules.


An independent conservative total-correctness bound uses only the immediate
gcd branch. Let p_direct be the sum of the uniform masses of a in
{1,...,N-1} for which gcd(a,N)>1. At a store in that range and satisfying
the gcd guard, the immediate assignment establishes the factor predicate
with certainty. The other conditional branch receives the zero assertion,
which is a sound total precondition for any command. Applying the random
assignment rule gives the constant effect p_direct I: each successful
sample contributes its uniform scalar mass times I, and each other sample
contributes zero. Nonnegative summability and the normalized uniform mass
justify moving the scalar sum through multiplication by I and give
0≤p_direct≤1. This lower bound may be zero (for example for prime N); it
neither asserts the paper's larger success bound nor changes order finding.


The checked source is `ClassicalShorProgram.shor` in `shor.v`,
instantiating `ClassicalOrderFinding.order_finding` with the literal printed
postprocessor. `uniform_probabilityE` proves the exact sampling masses.
`shor_partial_safe` and `derives_shor` establish factor-output partial safety.
`shor_direct_total` and `derives_shor_direct` establish the independent
immediate-gcd lower bound; `direct_preE` identifies their precondition with
`direct_probability N *: identity`, and `direct_probability_sum`,
`direct_probability_ge0`, and `direct_probability_le1` identify and bound that
scalar. The more general `shor_with_partial_safe` and
`shor_with_direct_total` hold for any order-finding command, with no
correctness premise on it.

The stronger checked C7 result proves that every successful result of the
printed selector is at most two, at every precision. The complete command's
total precondition for any larger returned order is zero, and its output
expectation for that event is zero on every cq-input. In particular it never
returns the exact order four of two modulo fifteen; see
[order finding failure notes](PROOF_NOTES.md#order-finding-failure-notes). The separate valid modular-unit counting
lemma is now checked, including its conditional-probability statement for
the actual uniform sampler; see [shor counting notes](PROOF_NOTES.md#shor-counting-notes) and
[shor uniform notes](PROOF_NOTES.md#shor-uniform-notes). Exact-order factor extraction in Equation (20)
and the distinct-prime consequence of cmp(N) are also checked.

`ClassicalShorSampling.sampling_partition` identifies the actual gcd and
coprime branch masses as complementary probabilities. Its
`sampling_mixture_bound` proves Equation (21) for every scalar p in [0,1],
using the checked conditional bound and exact-order event. This is the
sampler's probability calculation; a verified success guarantee for the
order-finding subroutine is still needed to apply it to a repaired complete
Shor algorithm. See [shor sampling notes](PROOF_NOTES.md#shor-sampling-notes).

The independent spectral derivation on page 39 is also checked. The modular
orbit has exactly the multiplicative order's number of distinct basis
vectors and yields an isometric embedding. Applying that embedding to the
conjugate Fourier basis gives the printed normalized orbit sums. Their
inner products are Kronecker deltas, the actual modular multiplication
unitary has the printed phase eigenvalues, and the normalized sum over all
eigenstates is the actual initialized basis-one state. The construction
also covers order one. See [order finding orbit notes](PROOF_NOTES.md#order-finding-orbit-notes) and
[order finding eigenstates notes](PROOF_NOTES.md#order-finding-eigenstates-notes) for the proof and checked names.


<a id="cross-space-notes"></a>

## CROSS SPACE NOTES

### Assertion-space-changing SupOper (Table 5, pp. 31–33)

The paper allows a completely positive subunital F from operators on V to
operators on W. The precondition and postcondition need contain V, and their
remaining quantum supports must be disjoint from W. Both V and W must be
disjoint from the program footprint. They need not have the same dimension
and may overlap each other. All supports below are subsets of the arbitrary
finite ambient memory chosen by the shared language.

We implement the rectangular map with the following square extension on
U = V union W. Let A = U minus V and B = U minus W. The rectangular
depolarizer D from A to B is D(X) = tr(X) I_B / dim(A). It is completely
positive, with Kraus operators |j>_B <i|_A / sqrt(dim(A)), and D(I_A)=I_B.
Thus F tensor D, after identifying V union A and W union B with U, is
completely positive and subunital. Its ambient lift acts only on U, so the
already checked square SupOper rule applies in both correctness modes.

On a cylindrically lifted X on V, the extension sends X tensor I_A to
F(X) tensor I_B. It therefore sends the ambient cylinder of X to that of
F(X). If R is disjoint from V and W, the extension also commutes with
operators on R, and consequently sends the cylinder of X tensor Y to the
cylinder of F(X) tensor Y. Expand an arbitrary operator on V union R in
delta matrix units, split each matrix unit over V and R, and use linearity.
This proves the same equation for arbitrary operators, including entangled
effects: the result is exactly the cylinder of (F tensor Id_R)(A).

Every paper assertion support Z with V subset Z and W intersect Z subset V
has this decomposition with R = Z minus V. The precondition and
postcondition may use different remainder supports. The formal rule takes
these disjoint decompositions explicitly; they impose precisely the paper's
support conditions, without a separability assumption. The transformed
assertions are packed effects because the tensor map is completely positive
and subunital. No external register beyond the chosen ambient memory is
created, and no modification of the program semantics is required.

Checked in `auxiliary.v`, module `CQQuantumCrossSpace`:

- `rectangular_depolarizerE`, `rectangular_depolarizer_cp`,
  `rectangular_depolarizer1`, and `rectangular_depolarizer_dqo` prove the
  explicit rectangular map and its complete positivity/unitality bounds.
- `square_extension_lift` and `square_extension_cylinder` prove its action
  on an arbitrary local operator.
- `cylinder_tensor_action` proves the general matrix-unit extension;
  `square_extension_tensor` instantiates it for the constructed map.
- `cross_assertion` constructs the transformed effect assertion and
  `cross_assertionE` exhibits its literal rectangular-tensor formula.
- `image_square_extension` identifies that assertion with the square
  ambient action; `derives_supoper_cross` gives the Table-5 inference in
  both correctness modes, with separate remainder supports at its input
  and output. It has only the paper's derivability and support premises.

The mapped assumption audit of the rectangular depolarizer bound, arbitrary
tensor-action theorem, and final derivation reports only inherited classical
real-model, choice and extensionality foundations and the existing `qreg.G`
memory parameter. There is no new axiom or admitted proof.


<a id="expectation-notes"></a>

## EXPECTATION NOTES

### Expectation: convergence and bounds

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

#### Continuity and order separation for completeness

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

The corresponding results are developed in `assertion.v`.

#### Initial validation and assumptions

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

#### Assertion limits

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
`semantic_le_iff_expect` in `assertion.v`;
`CQExpectationLimits.effect_sup_cvg`, `semantic_sup_cvg`,
`expect_semantic_sup`, and `expect_semantic_inf` in `assertion.v`.
The corresponding Dune targets pass after the cqwhile language refactor.


<a id="fourier-notes"></a>

## FOURIER NOTES

### Fourier circuit argument

Source: classical.pdf Section 7.2, pp. 34–36. The gate-by-gate argument follows
CoqQ's pinned `example/coqq_paper/example.v` QuantumFourierTransform module
(MIT; see REFERENCE.md and UPSTREAM-LICENSE), adapted to shared cqwhile
expressions and explicit classical while counters.

Number qubits from zero. On input basis string b, after finishing positions
strictly below k the state is the tensor product of phase states
`ph(bitstr2rat(drop i b))` at i<k and unchanged computational basis states
`|b_i>` at i>=k. Applying Hadamard at k makes its factor `ph(b_k/2)`.
After processing controls k+1,...,j-1, its phase is
`sum_{r=k}^{j-1} b_r / 2^(r-k+1)`. The controlled phase from j to k adds
`b_j/2^(j-k+1)`. It acts diagonally and preserves all other factors, including
phase states already produced at earlier positions. This proves the inner
loop invariant by induction on j and the outer loop invariant by induction
on k. At j=n the finite binary fraction is exactly
`bitstr2rat(drop k b)`. Reversal of all tensor factors gives `QFTbv b` by the
already proved `qtype.QFTbvTE` identity.

For completeness of this basis argument, equality on the full computational
orthonormal basis establishes equality of linear operators, hence equality
on arbitrary superpositions and entangled extensions. It does not infer
superposition correctness merely from phase-insensitive pure-state Hoare
triples. The classical loop certificates prove that both actual unbounded
while loops perform these finite gate sequences and end with their expected
counter values. The guard/range proofs establish valid indices at each gate.
Consequently their full kernel equals the concrete Fourier unitary kernel.

The tensor calculation is checked in `algorithms.v` through
`single_hadamard_product`, `controlled_phase_product`,
`phase_chain_product`, `bitstr2rat_drop_sum`, and `stage_phase_layer`.
`circuit_prefix_basis` proves the outer circuit invariant;
`fourier_circuit_basis` and `fourier_circuit_correct` prove equality with
the Fourier transform on basis states and as a complete linear operator.
`algorithms.v` supplies that connection. `fourier_inner_execution` and
`fourier_outer_execution` certify both actual while loops;
`accumulated_circuit` identifies their composed channels with the gate list.
`fourier_execution` and `fourier_denote` prove that the complete program,
including initialization of the counter and final reversal, has exactly the
QFT channel. `fourier_pre` gives its explicit total/partial predicate
transformer, and `fourier_correct` derives the corresponding unitary rule in
the independent calculus. The sole classical-register side condition is that
the two counter names differ. The result includes the zero-length array.

The one-based dynamic gate sugar checks both bounds and distinctness of the
controlled-gate indices. Failed checks abort. The loop certificates establish
all checks on reached stores. The comparison `x < n+1` is the signed-integer
form of the paper's `x <= n`; no finite unrolling replaces either loop.

`semantics.v` supplies the shared `indexed_loop_execution` and
`indexed_loop_denote` lemmas. The induction is on the number of remaining
counter increments. At each step, a concrete body execution certificate
supplies its resulting store and superoperator, and a separate elementary
store equation supplies the increment. The zero case has a false guard.
`execution_denote` then identifies the full unbounded-while denotation with
this finite terminating execution. The body may depend on the store and
change additional variables, as the inner counter of the Fourier program
does; no bounded-time or termination premise is assumed about the whole loop.


<a id="hoare-notes"></a>

## HOARE NOTES

### Hoare rules and relative completeness

Source: classical.pdf, Table 4 (printed page 16:26) and Section 5.2
(the total-correctness AbortT rule on 16:28). `CQHoare.derives` is the full
independent inductive inference relation, covering every core constructor,
including conditional and partial/total loop rules. `CQHoare.derives`
preserves the initial structural subsystem. Primitive rules use their explicit
dual-operation preconditions; `semantics.v` proves the substitution, weighted
random sum, Kraus measurement, initialization, and unitary formulas. Neither
system has a constructor assuming arbitrary semantic correctness.
Following the user's approved repair
on 2026-10-03, this inference system works over all effect-valued semantic
assertions. The exact countable-image/definable-fiber paper assertions embed
through their value-function coercion, so one common inference system
serves both domains.
The current assertions share the fixed global quantum-memory space;
the paper's comparison of assertions on differing variable sets is not
yet a separate local-space interface.

The state transformer is the arbitrary-state kernel action, and sequential
composition uses the proved kernel-action composition theorem. Total
validity is the paper's expectation inequality. Partial validity is stored
in the equivalent complement form used in upstream CoqQ:

    Exp(output, I-Q) <= Exp(input, I-P).

Absolute convergence proves Exp(rho,I-P)=Tr(rho)-Exp(rho,P), so this is
exactly Exp(input,P) <= Exp(output,Q)+Tr(input)-Tr(output).
`valid_partial_loss` records the equivalence.

To connect this transformer explicitly to terminating executions, expand
its value at an output store as the absolutely convergent sum over input
stores (`CQKernel.applyE`). Each input component is positive, so the
single-input route/denotation theorem applies to that summand. Substitution
therefore gives the iterated sum of terminating-route outputs over all
input stores, retaining the route indices inside each inner sum. This is
`run_operational`; no finite-support assumption or interchange of an
unjustified sum is required.

Soundness of Skip is identity action. Abort action is the zero state;
its post-expectation is zero, while total AbortT additionally has zero
pre-expectation. Seq chains the two total inequalities in the forward
direction, or the complement inequalities in the reverse direction.
For Imp, trace-pairing monotonicity strengthens the precondition and
weakens the postcondition; complement reverses operator order. Thus
induction on a derivation proves `derives_sound` without any constructor
that inserts an arbitrary semantically valid judgment.

The full extension in `hoare.v` proves total and partial soundness and relative
completeness for the implemented core syntax over the approved effect-valued
domain. It does not assert the false limit-closure claim for the paper's
countable-image/definable-fiber subclass, nor completeness of that subclass.

The primitive assignment bridge uses an explicit convergence argument.
For any kernel K, effect family Q and input state rho, write
F(i,j)=Tr(Q(j) K(i,j)(rho(i))). Positivity and the effect bound give
|F(i,j)| <= ||K(i,j)(rho(i))||_1. Every finite rectangle is consequently
bounded by the input state's total trace norm, using `rectangle_bound`.
The absolute Fubini theorem therefore permits exchanging the two sums;
linearity and continuity of trace pairing permit moving each pairing
through its input sum. For a deterministic update kernel, all output
terms except j=update(i) vanish. This proves `expect_sunit` without a
finite-memory restriction. Classical assignment has identity quantum
operation, so a pointwise substitution equation between the supplied
pre/post assertion records gives its total-validity axiom. Lost trace is
nonnegative by `apply_mass`, which also proves partial validity.

#### Assumption audit

On 2026-10-03, `Print Assumptions` was checked by direct compilation with
Rocq 9.1 for `expect_apply_sum`, `valid_assign_total`, `derives_sound`,
`abort_not_total_top`, and `CQAssertion.semantic_omega_cpo`. The common
foundations are `ClassicalDedekindReals.sig_not_dec`,
`ClassicalDedekindReals.sig_forall_dec`, `boolp.propositional_extensionality`,
`boolp.functional_extensionality_dep`,
`FunctionalExtensionality.functional_extensionality_dep`,
`Epsilon.epsilon_statement`, and `boolp.constructive_indefinite_description`.
These are the inherited classical real-number, choice, and extensionality
foundations. The concrete command theorems additionally depend on
`qreg.G : context`, the existing finite map assigning quantum variable types
in `src/qreg.v`; it is an explicit model parameter, not a correctness axiom.
The generic Fubini theorem and semantic assertion CPO theorem do not depend
on `qreg.G`. No new axioms or admitted obligations occur in these results.

The later full-core audit also checked `CQHoare.valid_while_total`,
`loop_ranking`, `derives_sound`, `derives_complete`, `sound_complete`,
`CQKernelLimits.unroll_apply_cvg`,
`CQExpectationLimits.expect_semantic_sup`, `CQAssertionSeries.expect_series`,
and `CQPredicate.wp_sdlet`. All nine completed `Print Assumptions` checks
have exactly the inherited foundations listed above, with `qreg.G` only for
the six concrete command/loop results. In particular, neither soundness nor
completeness has a new theorem axiom or an unproved program-correctness premise.

#### Predicate transformers and loop rules

For a summable completely positive kernel `K`, define
`wp(K,Q)(i) = sum_j K(i,j)^*(Q(j))` and
`wlp(K,Q) = I - wp(K,I-Q)`. The sum is well-defined even on the unbounded
classical store. Every summand is positive. Its finite partial sums are
bounded above by `(sum_j K(i,j))^*(I) <= I`, since each `Q(j) <= I`
and every finite row sum is trace nonincreasing. Positive operators have
trace norm equal to trace, so every finite sum of term norms is at most
`Tr(I)`. Absolute summability follows. The closed positive cone and closed
interval `[0,I]` then place the sum in the effect domain.

Trace pairing commutes with this absolutely convergent sum. The previously
proved absolute Fubini theorem exchanges input/output indices, yielding
`Exp(rho,wp(K,Q)) = Exp(K(rho),Q)`. Complementation gives the liberal
equation with lost trace. Testing on all singleton states shows that total
validity is exactly `P <= wp(K,Q)` and partial validity exactly
`P <= wlp(K,Q)`. These are characterization theorems, not inference rules:
derivability still uses the independently inductive paper rules.

The loop proof follows Table 3 and Definition 5.2. Increasing finite
unrollings converge to the kernel loop denotation; expectation continuity
therefore identifies their weakest preconditions with the least fixed point.
Complementation supplies the liberal greatest fixed point. Partial loop
soundness follows by induction that an invariant is below every descending
liberal approximant. For total correctness, a decreasing ranking sequence
`R_n` has infimum zero, covers the invariant at `n=0`, and satisfies
`b /\ wp(body,R_n) <= R_(n+1)`. Induction bounds the invariant by the sum
of `R_n` and the total finite-unrolling precondition. Taking limits proves
the total loop rule. Completeness uses the loop's weakest precondition as
invariant and the remaining termination effects after `n` iterations as
ranking assertions; their expectations are the difference between the
full and finite-unrolling termination masses, which decreases to zero.
The checked results are `CQPredicate.term_summable`, `wp_effect`, `expect_wp`,
`expect_wlp`, and the primitive/sequence/conditional equations;
`CQHoare.valid_total_iff`, `valid_partial_iff`, `wp_unroll_sup`,
`wp_unroll_cvg`, `wlp_unroll_cvg`, `valid_while_partial`,
`valid_while_total`, `tail_effect`, and `loop_ranking`. Structural induction
on commands proves `derives_pre`, then consequence gives `derives_complete`.
Induction on the independent derivation proves `derives_sound`.
`sound_complete` combines these directions for either correctness mode.
The record expresses zero infimum as pointwise convergence to zero;
`CQRanking.ranking_infimum` and `ranking_of_infimum` prove equivalence with
the paper's infimum formulation for decreasing effects.

The primitive rules also require respecting merged outcome stores. In a
random assignment or measurement, several branch indices may update to the
same output store. For each output store, move dual evaluation through its
absolutely convergent branch sum. Each surviving term then evaluates the
postcondition at that branch's updated store. The generic reindexing identity
`sdlet_sum` sums these grouped terms without changing their total. Thus
`CQPredicate.wp_sdlet` gives the branch-indexed precondition formula even
when outcome stores coincide. For normalized primitives the row sum is a
channel, so `wp(I)=I`; linearity and complementation imply `wlp=wp`.
`CQPredicate.wp_top`, `wlp_wp`, and `xp_wp` formalize this argument.

#### Auxiliary assertion algebra (Table 5)

For a finite family of assertions and nonnegative coefficients, trace linearity
and absolute summability of each expectation interchange the finite sum and
store sum. Hence the expectation of a supplied effect-valued weighted sum is
the corresponding weighted sum of expectations. Total-validity inequalities
can be added with arbitrary nonnegative coefficients provided both resulting
assertions are effects. Partial validity instead adds one lost-trace term for
each coefficient: their total is at most the single allowed lost-trace term
when the coefficient sum is at most one. This explains that explicit condition
in Theorem 6.1; it is not a condition on total correctness.

For Disj and disjoint Sum, use the weakest-precondition characterization
pointwise. At each store select the applicable premise (or the zero lower
bound). No distributivity property of the noncommutative operator order is
needed. For increasing preconditions with a common postcondition, each is
bounded by the same weakest precondition, hence their supremum is bounded too.
The derived-rule conclusions use the independent core completeness theorem
after semantic soundness has been proved. Named Top, Bot and Disj
derivations are in `CQAuxiliary`; `CQAuxiliaryDerivations.derives_sum`,
`derives_linear_total` and `derives_linear_partial` expose the remaining
finite rules. `derives_series_total` and `derives_series_partial` expose the
corresponding countable rules below.

For countably many nonnegative summands, the same Linear rule requires the
operator series defining the resulting assertions to converge at every store.
A finite partial sum is below its full positive sum. Therefore any finite
rectangle of weighted trace pairings is bounded by the input state's total
trace, since the resulting pre/post assertion is an effect. Absolute Fubini
then exchanges the assertion index and store index. This proves countable
linearity without requiring the coefficient family itself to be summable for
total correctness. Partial correctness retains the summable coefficient and
sum-at-most-one condition needed to bound its accumulated lost trace.

The mapped audit of the five `CQAuxiliaryDerivations` Sum/Linear/series
corollaries reports only inherited classical real-model, choice and
extensionality foundations and the existing `qreg.G` memory parameter.

For Lemma 4.16(3), the dual-kernel row for a finite linear combination of
effect assertions is the same finite linear combination of the individual
dual-kernel rows. Each row is absolutely summable. Finite linearity of the
sum therefore proves linearity of wp, even for arbitrary scalar coefficients
provided the displayed combined assertion is an effect. For (4), complement
distributes across an affine combination because the coefficients sum to
one. The defining identity wlp(Q) = I - wp(I-Q) and wp linearity then give
the stated affine law. No extra sign hypothesis is needed for this algebraic
identity beyond the supplied effect well-formedness.

For the equality case of Lemma 4.16(5), an external unital map F fixes the
program's lost-trace effect L = I - wp(I), by the checked `loss_unital`
commutation argument. Writing wlp(Q) = L + wp(Q), wp commutation and
linearity yield wlp(F(Q)) = F(wlp(Q)). The rectangular square extension
also preserves the identity when its original V-to-W map does: apply the
already proved cylinder equation to I_V, whose cylindrical lift is I_U.
This gives the equality case for literal space-changing maps as well.

Checked in `CQPredicateAlgebra`: `wp_finite_linear`, `wlp_finite_affine`,
and `wlp_image_unital` give the finite algebraic laws and unital equality.
`square_extension_unital` transfers unitality to the explicit square
extension, and `wp_cross`, `wlp_cross_le`, and `wlp_cross_unital` give the
rectangular-map forms of Lemma 4.16(5).

The mapped audit of the six main algebraic/commutation theorems reports only
the inherited classical real-model, choice and extensionality foundations,
and `qreg.G` for the concrete-memory theorems.

#### Quantum locality and SupOper

The quantum frame premise is the language's syntactic disjointness condition:
the external operation's register set is disjoint from `quantum_variables c`.
For each primitive, cylindrical extension of maps on disjoint registers
commutes, including on entangled states. Classical assignment acts as identity
on quantum data and random assignment scales that identity. Summable branch
grouping and sequential kernel composition preserve commutation by continuity
and absolute summability. Conditional selection preserves it pointwise.
Finite loop unrollings therefore commute, and continuity passes the equation
to the unbounded loop denotation. Taking duals yields commutation of the
weakest-precondition transformer with an external assertion operation.
Thus total SupOper follows by applying its positive map to the original
precondition inequality; commutation is derived from syntax, not assumed as
an extra program-correctness premise.

Partial SupOper needs an additional lost-trace argument because its external
map is only sub-unital. Complete an external CP sub-unital map F to a unital
CP map F+G: positivity of I-F(I) gives a factor g with
I-F(I)=g g*, so take G(X)=g X g*. The termination-defect effect
L=I-wp(c,I) is fixed by every unital external map, since such maps commute
with wp and preserve I. Hence F(L)+G(L)=L. Positivity of G gives F(L)<=L.
Applying F to the original liberal-precondition bound now proves the partial
rule. This handles divergence without assuming the program terminates or
that F itself is unital.

The initial formal interface acts on the fixed ambient quantum memory through
cylindrical extension. The paper's literal V-to-W SupOper now has its explicit
rectangular map and tensor action in `CQQuantumCrossSpace`; see
[cross space notes](PROOF_NOTES.md#cross-space-notes). The local-space embedding equations for tensor
extension and normalized partial trace are checked in `CQQuantumSpaceRules`
and `CQQuantumTrace`; see [quantum space notes](PROOF_NOTES.md#quantum-space-notes).

Checked in `CQQuantumFrame`: `denote_disjoint_commute` proves the concrete
kernel commutation theorem for every source command; `wp_external` transfers
it to arbitrary supplied effect-valued image assertions. `subunital_completion`,
`loss_unital`, and `loss_subunital` establish the partial-correctness defect
bound. `valid_supoper` and `derives_supoper` prove the ambient SupOper rule in
both correctness modes. These results have no assumed kernel commutation or
termination premise.

##### Independence from unused finite quantum memory

Fix any unused register set T inside the inherited finite ambient memory.
The normalized depolarizer on T sends an arbitrary operator rho to
lift(tr_T(rho))/dim(T), including entangled inputs. Each source-kernel branch
commutes with this map by the checked syntactic locality theorem. Cancelling
the strictly positive dimension factor proves
lift(tr_T(E(rho))) = E(lift(tr_T(rho))). Injectivity of cylinder lifting then
shows that equal retained marginals produce equal retained output marginals.
Continuity of partial trace and absolute summability extend the result from
one input store to arbitrary cq-inputs. For product inputs A tensor B, the
same depolarizer identity gives tr_T(A tensor B) = tr(B) A, so every normalized
unused-memory extension has the same retained behavior.

This concerns every subsystem of the arbitrary finite `DefaultQMem` universe,
without independence or separability assumptions on input states. A theorem
between two different memory contexts with a supplied variable embedding is
a distinct construction and is not claimed by this result.

Checked in `CQMemoryExtension`: `denote_partial_trace`,
`denote_marginal_ext`, and `apply_marginal_ext` establish branch and cq-input
locality; `partial_trace_product` and `normalized_memory_extension` establish
the explicit tensor-extension equation and normalized-ancilla independence.

#### Classical store locality

A primitive step changes only its assigned classical variable; measurement
and sampling have the same store update. For sequential execution and branch
selection, every remaining write is already in the source command's write
set. Induction on a terminating computation consequently shows that every
variable outside the original write set has its initial value at termination.
Route soundness transfers this property to each successful operational route.
If a predicate reads only such variables, every route preserves its truth.
The absolutely summable route semantics then shows that filtering by this
predicate commutes with program execution, which proves the classical Inv
rule without assuming finite classical support or bounded loop execution.

Checked auxiliary results in `CQAuxiliary`: `valid_bottom`, `valid_top`,
`valid_disjunction`, `valid_disjoint_sum`, `valid_sup`,
`valid_finite_linear_total`, `valid_finite_linear_partial`,
`valid_series_total`, and `valid_series_partial`. `CQAssertionSeries` proves
`expect_series` and `expect_series_summable` by the rectangle bound above.
`ClassicalLocality` proves `step_remaining_writes`, `step_unchanged`,
`terminates_unchanged`, `route_unchanged`, and
`terminates_preserves_expression`. These targets pass the integrated build.
The Inv rule uses these locality results below. Quantum framing and the
remaining auxiliary derivations are checked in `CQPrimitiveFrame`,
`CQQuantumCrossSpace`, and `CQAuxiliaryDerivations`, with their arguments
recorded in [primitive frame notes](PROOF_NOTES.md#primitive-frame-notes), [cross space notes](PROOF_NOTES.md#cross-space-notes), and this note.

`CQInvariant.denote_expression_zero` transfers store locality through the
complete route sum, `wp_guard_agree` transfers it through the dual kernel,
and `valid_invariant` / `derives_invariant` prove Table-5 Inv for both
correctness modes. The integrated `invariant.vo` target passes.
### Classical ranking argument (Table 5, C-WhileT)

The argument uses induction on the initial nonnegative rank, not a bound on
small-step execution time. Write `p` for a classical predicate supporting the
invariant effect `P`. For each rank value `k`, the body premise guarantees
total probability of reaching a store either outside `p` or with smaller
rank. A total-correctness assertion with classical postcondition `g` and
identity precondition implies `wp(body, g I) = I`. Positivity and
sub-unitality then give `wp(body, (not g) I) = 0`; by monotonicity the same
zero equation holds with any effect in place of `I`. Consequently masking
the invariant by `g` does not change its body precondition.

Assume the desired loop precondition bound at all smaller ranks. On an
output in `p` the decrease premise permits that induction hypothesis; on an
output outside `p` the invariant effect is zero. Body monotonicity and the
invariant premise therefore give the desired bound at the current input.
When the guard is false the loop fixed-point equation gives the invariant
itself. This proves total correctness without excluding probability-zero
infinite paths in a body and without assuming a uniform runtime bound. The
family indexed by rank values is the explicit semantic version of the
paper's fresh classical ghost variable. `CQClassicalRanking.wp_certain_mask`
and `valid_classical_while` formalize the probability-one masking and rank
induction. `valid_integer_while` and `derives_integer_while` give the signed
integer version and the derived inference rule. The reduction from the
paper's single fresh-ghost-variable premise to this explicit family is proved
by `CQGhostRanking.valid_fresh_integer_while` and
`derives_fresh_integer_while`, as detailed below.

### Assertion locality and existential elimination

Agreement of two typed memories on a set `X` is preserved when both receive
the same typed update. Every expression whose support is included in `X`
has equal values in such memories, by `ClassicalFootprint.eval_local`.
Induction on commands therefore shows that their predicate transformers
preserve locality on any `X` containing the command variables. Random and
measurement branches use the same outcomes and equal branch weights/maps;
their updated postconditions agree term by term. Sequential composition
uses locality of the intermediate precondition. For a while loop, induction
first proves locality of every finite unrolling, and uniqueness of the
already checked wp/wlp limits proves locality of the actual loop.

Taking `X` to omit one fresh classical name yields invariance under changing
that variable. Thus a witness for `exists x.p` may be installed into the
initial memory without changing the program precondition or an x-independent
postcondition. Applying the premise at that modified memory proves Exist.
`CQAssertionLocality.pre_local`, `valid_exist`, and `derives_exist` check this
argument for both total and partial correctness, including unbounded loops.
The same locality fact permits instantiating a fresh integer ghost with the
current rank, providing the link to the rank-family formulation above.

For the fresh-ghost bridge, fix an integer `k`. Apply the already proved
classical invariant rule to the predicate `z=k`; the body cannot write `z`.
Its premise and conclusion then imply respectively `b /\ p /\ t=k /\ z=k`
and `t<k`. The latter assertion and the command are independent of `z`, so
Exist removes `z=k` from the precondition: use the witness `k`, with expression
locality ensuring that this update preserves `b`, `p`, and `t`. This supplies
every member of the signed-rank family and hence the printed C-WhileT rule.
This derivation requires no assumed substitution or whole-program theorem.

#### Simultaneous bounded unrolling of nested loops

For a natural number `k`, recursively preserve every primitive and classical
branch, recurse into both sequential components, and replace `while b do c`
by `k` unrollings of `b` with recursively approximated body `c`. Every such
syntax tree is loop-free; it is used only as an approximant, not as a
replacement semantics. Increasing `k` increases its completely positive
kernel, and every approximant is bounded by the actual command kernel.

Sequential composition is monotone by composition of positive maps and
absolute summability of each kernel column. Its continuity is the inherited
`slet_lim` theorem. For a loop, fix an outer depth `r`: continuity of sequential
composition proves that the limit over body approximations of its `r`-fold
unrolling is the `r`-fold unrolling of the limiting body. For each body index
`k`, choose `j=max(k,r)`. Monotonicity in both body and outer depth bounds this
term by diagonal approximant `j`. Taking limits first in the body index and
then in `r` proves that the actual loop is below the diagonal limit. The
reverse inequality follows from the uniform kernel upper bound. Thus the
simultaneous finite approximants converge to the full nested-loop semantics,
also after composition with any fixed continuation.

#### Probabilistic composition and quantum support

For Table 5 (ProbComp), fix a classical input satisfying the first precondition
and an arbitrary partial density operator. Total correctness of the first
command gives `input trace <= expectation(p and P) <= output trace <= input
trace`, where P is the projector onto the asserted pure state on the selected
registers (tensored with identity on the remaining memory). Thus every bound
is an equality. The complementary expectation is a sum of nonnegative terms
with value zero, so each term vanishes. For each output store its density has
support in the asserted projector; outside p that projector is zero.

If M is the second command's asserted effect and `P M P = a P`, support gives
`tr(M rho) = a tr(rho)` for every output component. Absolute summability lets
this equality pass through the sum over output stores. The second correctness
premise then gives success at least a times the input trace. Finally use the
point-state characterization of effect order to obtain the program rule on
arbitrary cq-states. For a local normalized vector psi, its rank-one projector
satisfies `P M P = <psi,M psi> P`; this argument permits entanglement with
untouched memory and does not falsely identify the whole output density with
a scalar multiple of a rank-one projector on the full memory.

Checked implementation: `CQProbabilisticComposition` proves
`projection_saturated_support`, `supported_pairing`, `saturated_expectation`,
and the general `valid_probcomp_projection`/`derives_probcomp_projection`.
`CQProbabilisticPure.valid_probcomp` and `.derives_probcomp` instantiate the
printed total-correctness rule on a physical register. `pure_success_effectE`
identifies the initial scalar effect as `<psi,M psi> I`.

The fresh audits of the simultaneous-unrolling limits, the general and
pure-register ProbComp rules, and the finite local/global comparison report
only the inherited classical foundations and the existing `qreg.G` model
parameter. Their logs are `composition_local_assumptions.log` and
`probcomp_assumptions.log` under `/private/tmp/coqq-assertion-check/`.


<a id="memory-interpretation-notes"></a>

## MEMORY INTERPRETATION NOTES

### Distinct finite-memory interpretation: construction and API

This construction addresses classical Section 4.2's domains and distributive
Lemma 3.4(5), whose ambient finite memory V can be any memory containing the
program's quantum footprint. It preserves the actual cqwhile source syntax,
including typed registers and state-dependent classical, measurement,
initialization and unitary expressions. It does not change qreg.G.

Fix an original subsystem S containing the command's quantum footprint.
Let L be any finite label type, H:L->chsType any target tensor system, T and
V target label sets with T contained in V, and U a packed global isometry
from H[msys]_S to H[H]_T. This is a basis/register interpretation, not a
correctness hypothesis. S may equal the program footprint; consequently V
need not contain the unused portion of the original qreg.G. A concrete
register-preserving identification of equal typed variables induces such U.
The theorem quantifies over all choices of finite target memory and U.

For a source register q with mset(q) contained in S, interpret a typed
operator A on q by first applying the existing tf2f q q A, lifting q to S,
conjugating by U, and lifting T to V. This preserves its type and all
state-dependent expression evaluations (the classical store is unchanged).
Interpret a unitary primitive by formso of this operator. Interpret each
measurement outcome by formso of its interpreted measurement operator.
Interpret initialization through its actual reset Kraus family
|tv2v(q,phi)><eb_i| on q: lift, conjugate and lift each Kraus operator, then
sum their form maps. These primitive definitions use the actual constructors
and do not define execution by a desired descriptor-replay equation.

The algebraic proof uses conjugation of superoperators:
conjugate_U(E) = formso(U) o E o formso(U^A).
Global-isometry cancellation proves preservation of identity, composition,
complete positivity, trace preservation and trace nonincrease. Kraus
expansion proves conjugate_U(krausso f) = krausso(U f_i U^A). Existing
liftso_krausso and liftso_formso identify each independently interpreted
primitive with liftso(T<=V)(conjugate_U(liftso(q<=S)(source primitive))).
This proves primitive covariance, including measurements and reset.

An interpreted classical small-step relation copies the source Table 2
constructors with the new primitive channels and target quantum state type.
Each constructor includes only the local footprint inclusion needed to
interpret its actual register. It retains the same assignments, random
outcomes, guards, sequencing and while unrolling. Structural induction on
source steps proves replay at every target input using the same branch
choices and residual/classical results, with quantum output determined by
the interpreted local branch map. The quantum output is not assumed to be
a direct transport of the old full-memory input: arbitrary new inputs may
have additional entanglement and different marginals.

For distributed source statements, define the analogous primitive/local
interpreter independently. Guard and communication control use the existing
classical expressions; primitive branch maps use the above construction.
Structural induction on the local/global transition rules gives replay in
the new memory. Prove normalization for normalized new density input; the
configuration definition requires trace one even though Lemma 3.4(5) writes
D(H_V). Subnormalized inputs belong to the separate linear cq-state
extension, not to a probability-one branch family.

The common formal APIs are `CQMemoryTransport.conjugate_formso` and
`conjugate_krausso` in `semantics.v`, and
`CQMemoryInterpretation.unitary_channelE`, `measurement_channelE`,
`initialize_channelE`, `measurement_sum_tp`, and `transport_original` in
`semantics.v`. `transport_summable` and `transport_sum` extend
the same construction to arbitrary summable branch families. The primitive
module, including all summation helpers, has passed direct and qualified
Dune compilation.

`ClassicalMemorySteps.memory_step` in `semantics.v` is the independently
defined classical Table 2 relation. Its `step_replay` constructs a footprint
operator and the replayed step for each target input; this is an informative
witness, not a correctness parameter. `source_step_quantum` tracks the
residual footprint. `memory_step_positive`, `memory_step_trace_le`, and
`memory_step_density` verify state preservation directly for this new
relation. The classical replay module has passed direct and qualified Dune compilation.
The corresponding distributed implementation is
`DistributedMemoryReplay` in `distributive/operational.v`; its own note
records the checked global replay API.

The scope of this layer is primitive interpretation and one-step operational
replay across memory contexts. Cross-context denotational semantics for full
unbounded programs and transport of Hoare derivations are separate results;
they are not claimed here. No target replay/covariance property is a model
parameter.

Preservation of positive operators and density operators in the interpreted
small-step relation follows directly by induction on its constructors.
Random weights lie between zero and one; measurement branch maps are
completely positive and trace-nonincreasing; initialization and unitary
maps are channels. Structural constructors preserve those facts. The
identity interpretation (the same S, original target full memory, and
identity U) reduces transport to the original liftfso, providing the
original model as an instance of the new interpretation.


Mapped assumption audits of all primitive covariance theorems, measurement
normalization, summation transport, original-model recovery, classical step
replay, density preservation and residual support passed. They use only the
inherited classical-real/choice/extensionality foundations and the original
source-language memory parameter `qreg.G`; no new axioms or admissions were
introduced. The target memory and its footprint identification are explicit
theorem parameters, not additional global assumptions.


<a id="memory-transport-notes"></a>

## MEMORY TRANSPORT NOTES

### Transport between finite quantum memories

This supports the arbitrary ambient-memory clause of distributive.pdf
Lemma 3.4(5), p. 11, while preserving the original cqwhile syntax and its
fixed context. A new interpretation of primitive commands uses an explicit
unitary identification of the source footprint with a subsystem of another
finite memory. Such an identification is a model parameter, not a premise
about program correctness. Additional target memory may be entangled with
the interpreted footprint.

For a unitary isomorphism U:A→B, write J_U(X)=UXU† and transport a
superoperator E on A as C_U(E)=J_U E J_(U†). Both J maps are completely
positive and trace preserving. Their two compositions are identity because
U†U=I and UU†=I. Thus transport is linear, sends identity to identity,
preserves composition, is invertible with inverse C_(U†), and preserves
complete positivity and trace nonincrease/preservation. These statements
hold for arbitrary operators and do not require a product-state assumption.

For a Kraus family f_i, direct multiplication gives
C_U(sum_i f_i X f_i†)=sum_i (Uf_iU†)X(Uf_iU†)†. This proves the exact
transport identities for Kraus families and their single-operator special
case. Continuity of the linear transport map commutes with any absolutely
summable family of superoperators; in particular it preserves the sum of an
instrument. The generic algebra does not mention the original `qreg.G`.

For interpreting primitives, lift the actual source-register Kraus operators
to the source footprint, conjugate by U, and tensor with identity on unused
target memory. Initialization, unitary, and measurement constructors are
interpreted independently using these operators and the original cqwhile
expressions. Structural replay will then follow by induction on actual
small-step constructors, rather than defining replay as the semantics.

The checked generic algebra is in `semantics.v`, module
`CQMemoryTransport`. `conjugate_linear`, `conjugate1`, `conjugate_comp`,
`conjugateK`, and `conjugate_injective` establish the algebraic laws.
`conjugate_formso` and `conjugate_krausso` give the exact operator formulas.
`conjugate_cp`, `conjugate_tn`, and `conjugate_tp` preserve the physical map
classes, with canonical packed instances. `conjugate_apply` and
`conjugate_trace` give the state-action and trace identities, and
`conjugate_summable`/`conjugate_sum` handle arbitrary summable instruments.

For a family F of local superoperators, summability of its cylinder-lifted
family implies summability of F itself: the existing `liftso_norm` theorem
bounds each local norm by its lifted norm, hence bounds every finite norm
sum. Continuity and linearity of cylinder lifting commute with the resulting
absolutely summable family. Consequently trace nonincrease of the summed
lifted instrument reflects back to the summed local instrument, by the
existing exact `liftfso_qoE` equivalence. This supplies one explicit local
map family shared by source realization and target replay.
These helper results are checked in `semantics.v`, module
`CQMemoryInstruments`: `liftso_summable_reflect`, `liftso_sum`, their
`liftfso` specializations, and `liftfso_sum_cptn_reflect`. Direct and
qualified builds and all three assumption audits passed, with inherited
classical foundations only and no `qreg.G` dependency.

Direct and qualified Dune compilation passed. The eight-result assumptions
audit reports only inherited classical real/choice/extensionality
foundations, with no `qreg.G` or new correctness axiom. The typed primitive
interpretation is documented separately in [memory interpretation notes](PROOF_NOTES.md#memory-interpretation-notes).


<a id="normalized-update-notes"></a>

## NORMALIZED UPDATE NOTES

### Normalized tests and store updates (Lemmas 4.10 and 3.12)

For Lemma 4.10 (p. 21), a positive operator rho with positive trace is its
trace times the normalized density rho/tr(rho). Any linear trace-pairing
inequality that holds for normalized densities therefore holds for rho.
When the trace is zero, positivity implies rho=0 and the inequality is
trivial. Thus normalized density tests detect the full operator order.
Apply this to the checked weakest-precondition characterization at each
store. The arbitrary cq-state validity follows from that characterization;
the reverse implication simply tests a singleton state. Partial validity
uses complementary assertions, and the established complement identity
rewrites it into exactly the paper's lost-trace inequality with initial
trace one. This argument is shared with the existing distributed normalized
test interface, which retains aliases to the classical common result.

For Lemma 3.12 (p. 14), update the store by u(m)=m[x:=eval(e,m)] and use the
identity quantum channel at every input. The resulting cq-state has component
sum over all m with u(m)=out of rho(m). This summation is essential because
different stores can update to the same output. The shared kernel action
already proves summability and positivity of that merged family. Absolute
Fubini, as formalized by `expect_sunit`, rewrites its expectation as
sum_m tr(P(u(m)) rho(m)), which is exactly the expectation of the substituted
assertion P composed with u. Taking P=I shows that store update preserves
total trace. The operation agrees definitionally with assignment denotation.

`CQNormalizedValidity.operator_le_normalized` and `valid_normalized_iff`
give the common test theorem. `valid_total_normalized` and
`valid_partial_normalized` state the two paper clauses directly, the latter
with the initial trace-one lost-trace formula.

`CQStateUpdate.update_stateE` exhibits the merged output components.
`expect_update` is Lemma 3.12, `update_state_mass` proves exact trace
preservation, and `update_state_assignment` identifies the state operation
with the shared language's assignment denotation.

Validation: both classical modules and the distributed compatibility alias
pass the mapped Dune build. `Print Assumptions` for `valid_normalized_iff`,
`valid_partial_normalized`, `expect_update`, `update_state_mass`, and the
distributed alias reports only the inherited classical real, choice, and
extensionality foundations and the existing `qreg.G` memory context. There
are no new axioms or admitted obligations.


<a id="operational-approximants-notes"></a>

## OPERATIONAL APPROXIMANTS NOTES

### Bounded operational completions: classical Lemma 4.2

Source: `classical.pdf`, PDF page 17, Lemma 4.2(1–2), together with
Definition 4.3. The sum is indexed by execution routes, preserving distinct
random or measurement choices even when their final configurations coincide.
Only nonzero route contributions matter; zero-weight branches are harmless.

The separate exact route-cost development associates each successful route
with its actual number of small steps. Atomic commands and the false-guard
loop exit cost one step. Conditional selection and true-guard loop unfolding
add one step to the continuation. Sequential composition adds the costs of
its two subroutes: each step of the first command is lifted through Sequence,
and its final step also exposes the second command, so no extra administrative
step is inserted. The counted-execution correspondence identifies cost at
most n with successful executions terminating within n steps.

For a fixed input store and partial density operator, let F(r) be the
singleton cq-output operator family of route r, or zero for an unsuccessful
route. The established operational summability theorem gives
`sum_r ||F(r)||_1 ≤ tr(rho)`. Each F(r) is positive. For any subset A of
routes, restricting F to A preserves summability and positivity and cannot
increase this bound. Hence the sum over A is a well-formed cq-state; its
support and the set of nonzero contributing routes are countable. This also
proves countability at each exact execution length.

Take A_n to be routes of cost at most n and write Δ_n for their sum. The
sets A_n increase, and all contributions are positive, so Δ_n≤Δ_(n+1).
Every route has finite cost. Absolute summability therefore makes Δ_n
converge in the summable-family norm to the unrestricted operational sum:
given epsilon, a finite set captures all but epsilon of the norm sum, and
all its routes occur by the maximum of their costs. This is precisely the
existing `summable_sigma_nat_cvg` theorem after restriction reindexing.

The cq-state supremum of the increasing Δ_n is its norm limit. Uniqueness
of limits identifies that supremum with the full operational sum, and the
already checked operational/denotational correspondence identifies it with
execution of the compositional kernel on the singleton input cq-state.
There is no bound on runtime and no finite-support restriction on sampling.

The generic restriction argument is checked in `semantics.v`,
module `ClassicalOperationalApproximants`, as `selected_summable`,
`selected_state`, `selected_mass_bound`, `selected_routes_countable`,
`selected_state_mono`, `completion_state_chain`, `completion_state_cvg`,
`completion_state_sup`, and `completion_state_denote`.

`semantics.v`, module `ClassicalOperationalCompletions`, uses
the actual `ClassicalOperationalRouteCost.route_cost`:

- `exact_completions_countable` and `bounded_completions_countable` prove
  countability for the exact-length and bounded-length counted executions.
  `selected_routes_countable` also gives countability before endpoint
  aggregation, preserving route multiplicities.
- `bounded_completionE` gives the exact positive route sum for cost at most n.
  `bounded_completion_zero` gives the empty initial approximant.
- `bounded_completion_chain`, `bounded_completion_countable`, and
  `bounded_completion_mass` establish the cq-state chain and trace bound.
- `bounded_completion_cvg` proves norm convergence to the full operational
  sum. `bounded_completion_sup`, `bounded_completion_upper`, and
  `bounded_completion_least` identify the denotational output as its least
  upper bound.

The exact route-cost and counted-execution correspondence is checked in
`semantics.v`. `successful_route_exact_iff` and
`successful_route_bounded_iff` give both directions; the separate
`semantics.v` additionally relates exact nonzero routes to
counted maximal live paths. See [operational route cost notes](PROOF_NOTES.md#operational-route-cost-notes).

The generic approximants module passed direct compilation, Dune mapping,
and five central assumption audits on 2026-10-03. Those results use only the
inherited classical foundations and existing ambient-memory parameter
`qreg.G`; no new axiom or admission is introduced.
The concrete completion module passed direct compilation, Dune integration,
the whole-project checkpoint build, and six central assumption audits on the
same date. Its audited countability, initial-zero, chain, supremum, and
leastness results have the same inherited foundations and `qreg.G` only.
See the shared validation record for the build boundary.


<a id="operational-route-cost-notes"></a>

## OPERATIONAL ROUTE COST NOTES

### Exact lengths of terminating computations

Classical paper, Section 4.2, Lemma 4.2 (printed pp. 16–17), indexes its
operational approximants by the number of small transitions. The existing
`route_size` is a structural induction measure; its sequence constructor
adds one, although the operational sequence rules add no extra transition.
Consequently it cannot be used as the paper's transition count.

Define `route_cost` by assigning one to each atomic route and to a false
while guard, adding one for a conditional choice or a true while guard,
and adding the costs of the two routes in a sequence. Every route has
positive cost. A counted terminating derivation has a final step of cost
one, and each preceding step increases the count by one.

For soundness, induct on the route. The atomic and guard cases follow the
corresponding transition rule. In a sequence, lift each step of the first
terminating derivation through its surrounding sequence. Its final step
changes the residual command to the second component, so concatenating the
second derivation uses exactly the sum of their lengths. No extra step is
introduced. This establishes that evaluating a route successfully produces
a terminating derivation of exactly its route cost.

Conversely, prepend a small transition to a successful route for its
residual command. Induction on the transition reconstructs a route whose
cost increases by exactly one. For a transition ending a sequence's first
component, reconstruct its atomic-length route and concatenate the existing
route for the second component. For an internal sequence transition, split
the residual sequence route, prepend the transition to its first component,
and retain its second component. All other cases select the corresponding
atomic or guard route. Induction on a counted terminating derivation now
gives a successful route with exactly the stated cost. Existentially
quantifying over counts up to n gives the bounded version.

The operational transition relation retains zero-output branches, whereas
the paper's computation paths omit them. This does not change cq sums,
because their contribution is zero. For a nonzero final output, every
intermediate output is nonzero: a zero operator stays zero under every
transition. The exact counted derivation can therefore be converted into
a live path of the same length. Conversely a counted live path ending in
the empty residual command gives a counted terminating derivation. Empty
residual commands are terminal, so these successful paths are maximal.

Formal results are recorded in `semantics.v`, module
`ClassicalOperationalRouteCost`. Its central APIs are `route_cost`,
`eval_route_counted`, `counted_terminating_route`,
`successful_route_exact_iff`, and `successful_route_bounded_iff`.

The separate `semantics.v`, module
`ClassicalOperationalCountedPaths`, defines `counted_path` and
`counted_maximal_path`. Theorems `counted_path_terminates` and
`counted_terminates_path` give the exact live-path correspondence, and
`successful_counted_route_iff` identifies an n-step successful maximal path
with a route of cost n having nonzero output. Both modules compile directly
and pass their qualified Dune builds. Mapped assumption audits of both
correspondences use only the inherited classical-real, choice and
extensionality foundations and cqwhile's fixed memory parameter `qreg.G`.


<a id="order-finding-eigenstates-notes"></a>

## ORDER FINDING EIGENSTATES NOTES

### Modular-orbit Fourier eigenstates (classical.pdf p. 39)

The paper's exact spectral identities are independent of its false printed
continued-fraction success assertion. Let r be the exact multiplicative
order of x modulo N, with N>1, gcd(x,N)=1, and N≤2^L. The r orbit vectors
|x^j mod N⟩, 0≤j<r, are distinct: equality of two orbit residues is equality
of powers of the concrete finite modular unit, and exponents below its
order are injective. Their computational basis vectors are therefore
orthonormal. Sending |j⟩ in the r-dimensional auxiliary space to the j-th
orbit vector defines an isometry E. The actual modular unitary satisfies
U E|j⟩=E|j+1 modulo r⟩.

Use the complex conjugates of the existing arbitrary-size QFT basis in the
auxiliary space, so its s-th vector has coefficients

  r^(−1/2) exp(−2π i s j/r).

Applying E gives precisely the printed orbit Fourier vector u_s. Complex
conjugation preserves orthonormality, and E preserves inner products, so
the u_s are orthonormal and normalized. Shifting the orbit sum forward by
one replaces its coefficient at j+1 by the coefficient at j. The identity
exp(−2π i s(j+1)/r) exp(2π i s/r)=exp(−2π i s j/r), including the wrap at
r, follows from periodicity of the r-th root of unity. Reindexing the finite
sum therefore proves U u_s=exp(2π i s/r)u_s.

Finally, the uniform normalized sum over all Fourier labels is the zero
computational basis vector: the sum of r-th roots of unity is r at j=0
and zero otherwise. Applying E sends this vector to |x^0 mod N⟩=|1⟩.
Thus r^(−1/2)Σ_s u_s=|1⟩. The sum is finite and all normalizing factors are
legitimate because the concrete finite-group order r is positive. The
auxiliary index is implemented as r.-1.+1, proved equal to r, to expose the
existing inhabited positive-dimensional QFT API without imposing a new
mathematical restriction.

The generic finite Fourier facts are checked in `shor.v`
as `ClassicalOrderFindingEigenstates.inverse_fourier_basis_dot`,
`inverse_fourier_basisE`, `inverse_fourier_sum`, `eigenstate_eigenvalue`,
and `eigenstate_sum`. The generic cyclic-action premise is discharged by
the actual modular orbit theorem in the concrete instantiation; it is not
left as an assumption of the modular results.

The concrete checked names are `modular_eigenstateE` (the displayed Fourier
sum), `modular_eigenstate_dot`, `modular_eigenstate_normal`,
`modular_eigenvalue` (the actual modular unitary action),
`modular_eigenstate_sum` (basis one), and `modular_eigenstate_one` (the
exact `ClassicalOrderFinding.one_state` used by the printed source).
`ClassicalOrderFindingOrbit.orbit_lengthE` identifies the positive index
length in these statements with the exact `natural_order N x`. This also
covers order one: there is one normalized eigenvector, eigenvalue one, and
the uniform decomposition contains that single vector.


<a id="order-finding-failure-notes"></a>

## ORDER FINDING FAILURE NOTES

### Impossible outputs of the printed order-finding command

Source: classical.pdf, Section 7.4, pp. 38–40, the final assignment in
`OF(x,N)` and Equation (18). This is a consequence of the literal printed
minimum-denominator selector, whose counterexample and finite-list argument
are recorded as C7 in [proof gaps](PROOF_NOTES.md#proof-gaps).

Every measured control outcome is a t-bit tuple, so its integer value a
satisfies 0 ≤ a < 2^t. The checked selector theorem says that whenever
`printed_postprocess a (2^t) = Some d`, then d ≤ 2. Hence the deterministic
final assignment makes the event `result = Some d` false for every d > 2,
at every input store. Its total weakest precondition is the zero effect.

The complete source program sequences the preparation prefix, the actual
control-register measurement, and that assignment. Sequential composition
propagates the zero effect backwards, because every kernel's total weakest
precondition maps zero to zero. Thus the complete command has total weakest
precondition zero for the event, without any premise about eigenvectors,
the preparation state, success probabilities, or the modular multiplier.
This includes arbitrary initial quantum states and unused entangled memory.

Finally, expectation duality identifies the event expectation in the output
cq-state with the expectation of its weakest precondition in the input.
The latter is zero for every input cq-state. Since the event assertion is
its classical indicator times the identity effect, this is precisely zero
output probability of that returned denominator. In particular the literal
command never returns `Some 4`, so it cannot recover the known order four
of two modulo fifteen. This is a failure theorem for the printed source;
it does not adopt any corrected postprocessing algorithm or assert a
liberal-precondition identity for an arbitrary prefix.

Formal theorem map in `ClassicalOrderFindingFailure`:
`printed_result_ne` rules out the forbidden tuple outputs;
`printed_assignment_pre_zero` proves the final-assignment equation in both
correctness modes; `order_finding_wp_zero` proves the complete command's
total weakest-precondition equation; `order_finding_output_zero` gives the
zero event expectation for every input cq-state; and
`order_finding_never_four` specializes it to denominator four.

Validation: direct compilation and the mapped Dune target both pass.
`Print Assumptions printed_result_ne` is closed under the global context.
The complete-command weakest-precondition and output-expectation theorems,
including the denominator-four corollary, use only the inherited classical
real, choice, and extensionality foundations and the existing `qreg.G`
memory context. The source contains no new axiom or admitted obligation.


<a id="order-finding-notes"></a>

## ORDER FINDING NOTES

### Printed order-finding and Shor programs

Source: classical.pdf, Section 7.4, PDF pages 38–40, Equation (17), and
Section 7.5/Table 6, PDF pages 40–41. The rendered pages were inspected.
This work preserves the printed continued-fraction selector from
`ClassicalShorArithmetic.printed_postprocess`; it does not assert the false
success claim identified in C7 or introduce a corrected selector.

#### Modular multiplication is unitary

Fix a positive modulus N, a multiplier x coprime to N, and L qubits with
N ≤ 2^L. On their computational basis, map y to xy modulo N when y < N,
and fix y otherwise. The first branch stays below N. If two elements of
that branch have the same image, assume their natural representatives
satisfy b ≤ a. Equality of the residues implies N divides x(a−b).
Coprimality cancels x, so N divides a−b. Since both a and b are below N,
their residues, and hence their representatives, are equal. The two
branches have disjoint image ranges, and the second is the identity.
Thus the map is injective on a finite basis, hence permutes that basis.
The corresponding linear operator is unitary. This proves the actual
operator in Equation (17), rather than postulating a unitary with that
behavior.

Checked in `shor.v` as
`ClassicalModularUnitary.modular_value_inj`, `modular_bits_inj`,
`modular_unitary`, `modular_unitaryE`, and `modular_unitary_outside`.
`modular_power_residue` proves that the k-th power sends the basis vector
for a modulo N to the basis vector for x^k a modulo N.

#### Source program and its boundary

The printed program initializes the control register to zero, applies a
tensor of Hadamards, initializes the target register to zero, maps that
state to computational basis one, applies controlled powers of the modular
unitary, applies inverse QFT, measures the control register, and applies
the printed postprocessor. The paper explicitly leaves the gate-level
implementation of controlled powers unspecified, so its packed controlled
unitary is a faithful primitive here. A postprocessing failure is retained
explicitly, as in `printed_postprocess`.

For the inline Shor call, the multiplier is a classical expression evaluated
at the controlled-unitary instruction. To obtain a total unitary expression
on all stores, the selected operation is the proved modular unitary when
the multiplier is coprime to N and the identity otherwise. The Shor source
invokes this command under its coprime branch. This total extension does not
assert that Equation (17) is unitary for non-coprime multipliers. The output
variable has type `COption CNat`, retaining the printed selector's possible
failure; callers can abort that branch rather than inventing a denominator.

The source is checked as `ClassicalOrderFinding.order_finding` in
`shor.v`. `total_modular_unitaryE` identifies the selected operation
under the coprime guard. `one_bits_value` and `one_preparationE` establish
the target initialization. `prefix_execution`, `prefix_denote`, and
`prefix_channel` prove the source prefix's exact channel and its trace
preservation, with the classical store unchanged before measurement.

The register lengths t and L are explicit program parameters. The paper's
choice of precision can instantiate t; the exact program identities do not
depend on its claimed probability estimate. The source requires N>1 and
N≤2^L, which ensure that the target has computational basis one. At the printed boundary N=1, its prescription
L=ceil(log₂ N)=0 cannot satisfy U₊₁|0⟩=|1⟩; the one-dimensional Hilbert
space has no basis one. No claim for that degenerate printed program is
made. The Shor setting N>2 satisfies the required capacity conditions.

The circuit's output can be described directly in the computational basis:
after controlled powers it is the uniform sum of |j⟩|x^j mod N⟩, and after
inverse QFT it is the corresponding finite Fourier sum. Squared norms of
the measured-control slices give exact outcome probabilities independently
of the disputed continued-fraction success theorem.

Checked pure-state formulas are in `shor.v`:
`ClassicalOrderFindingState.controlled_stateE` is the modular-power sum;
`output_amplitude` is the exact finite Fourier sum for every joint basis
outcome; `outcome_probabilityE` sums the squared amplitudes over the
unmeasured target. `controlled_state_normal` and `output_state_normal`
prove normalization independently of any success assertion.

For the concrete-memory execution bridge, compose each preparation unitary
with the initialization immediately before it. The control preparation gives
the uniform vector and the target preparation gives basis one. These two
initialization channels act on disjoint registers, so commute and combine
into initialization of their tensor product. The controlled gate and the
lifted inverse Fourier transform then compose with that initialization,
giving exactly initialization of the final joint output vector. Consequently
control measurement has the Born probabilities computed from its basis
amplitudes, for every input cq-state, including inputs entangled with unused
memory; resetting both program registers removes that initial dependence.

To connect the probability formula to the measured source command, expand
the target identity as the sum of its computational-basis rank-one
projectors. The expectation of the control outcome projector in the joint
output vector is then the sum of squared joint amplitudes defining
`outcome_probability`. The dual of the resetting channel sends that
projector to this scalar times the identity on all ambient memory. The
final postprocessing assignment changes an option-of-naturals variable,
which has a different classical type from the bit-tuple measurement
variable, so it preserves the event that the measured tuple is m. Thus
the weakest precondition of this event for the full printed command is
the exact Born probability times the identity, for both total and partial
correctness because the finite prefix, measurement, and assignment all
terminate. This establishes the source-program bridge without any
continued-fraction success assumption.

The bridge is checked in `shor.v` as
`ClassicalOrderFindingExecution.prefix_actionE` and `prefix_prepares`.
`measured_projector_probability` proves the tensor Born identity,
`postprocess_preserves_outcome` proves the classical event is preserved,
and `order_finding_outcome_pre` gives the full source's total and partial
weakest preconditions as `outcome_probability (eval x s) m` times the
ambient identity. Combined with `ClassicalOrderFindingState.outcome_probabilityE`,
this is the exact finite Fourier formula for actual program measurement,
without a success-bound assumption or a restriction on initial quantum
memory. The multiplier expression can depend on the input classical store.

The printed spectral description is now independently checked in
`shor.v` and `shor.v`. The exact-order
orbit is isometric to its computational basis; its Fourier sums are
orthonormal eigenstates of the actual modular unitary, and their
normalized sum equals the actual target `one_state`. See
[order finding eigenstates notes](PROOF_NOTES.md#order-finding-eigenstates-notes) for the complete argument and names.


<a id="order-finding-orbit-notes"></a>

## ORDER FINDING ORBIT NOTES

### Exact modular orbit for the order-finding eigenstates

Source: classical.pdf, Section 7.4, PDF p. 39. The eigenvectors displayed
there use the orbit |x^k mod N> for 0<=k<r, where r is the exact order.
This note supplies that orbit as an actual orthonormal family in the
target register; the subsequent Fourier construction is independent of
the false continued-fraction selector claim C7.

Assume N>1, gcd(x,N)=1, and N<=2^L. Let u be the actual unit represented
by x modulo N and r=ord(u), using `natural_order`. The exact-order
properties have already been proved against ordinary modular arithmetic.
In particular r>0. Use the manifestly positive length (r-1)+1 for the
ordinal index type; positivity proves that this length equals r, including
the boundary r=1.

If x^i and x^j have the same residue, the corresponding unit powers u^i
and u^j are equal. Exact order implies i=j modulo r; since both indices
are below r, they are equal. Thus the residue-to-bit-tuple conversion is
injective on the orbit indices. Computational basis orthogonality gives
an orthonormal family of actual register vectors b_i=|x^i mod N>.

Define the linear embedding J from the r-dimensional coordinate Hilbert
space into the target register by J=sum_i |b_i><i|. Orthonormality gives
J^*J=I, so it is an isometry, preserves all inner products, and sends the
ith computational basis vector to b_i. No abstract orbit or assumed
spectral basis is introduced.

The already constructed modular unitary U sends |a mod N> to |xa mod N>.
Consequently U b_i=b_(i+1 mod r), because u^r=1. In particular, the orbit
of index zero is the actual computational vector |1>. These identities
hold when r=1: the cyclic successor is the sole index and U fixes |1>.
Fourier-transforming this concrete cyclic shift supplies the eigenstates
on paper p. 39 without relying on a quantum success probability.

The implementation is `shor.v`, module
`ClassicalOrderFindingOrbit`. `orbit_lengthE` identifies the positive
index length with the exact order. `orbit_bits_value` and
`orbit_bits_injective` identify and separate the actual residues.
`orbit_basis_dot` registers the computational vectors as a partial
orthonormal basis. `orbit_embedding_basis`, `orbit_embedding_isometry`,
and `orbit_embedding_dot` give the linear isometry and its action.
`orbit_power_period` proves the arithmetic period reduction;
`modular_orbit_basis` proves the actual modular unitary acts by the
cyclic successor `ordS`; `orbit_basis_zero` identifies the initial vector.
`orbit_isometry` supplies the explicit packed isometry used by the spectral
construction; `orbit_isometryE` identifies its underlying linear map.
The module passes direct and mapped compilation. The arithmetic orbit
injectivity is closed under the global context. The isometry, inner-product,
and modular-action audits use only the inherited real/choice/extensionality
foundations, with no quantum-memory parameter and no new axiom.


<a id="parameterized-counterexample-notes"></a>

## PARAMETERIZED COUNTEREXAMPLE NOTES

### Parameterized-unitary liberal-precondition counterexample

Source: classical.pdf, p. 23, Lemma 4.15(3); diagnosis C4 in
PROOF_NOTES.md#proof-gaps. This records a counterexample to the printed equality,
without adopting its proposed general correction.

Take any finite family of unitary branches and the constant integer
parameter zero. The permitted parameters are one-based, so every branch
guard is false. The actual selector command therefore executes Abort.
Induction over the finite list of guards proves that its total weakest
precondition is zero and its liberal weakest precondition is the identity,
for every postcondition and input store. The printed guarded sum is the
total precondition, hence zero at this input. Identity differs from zero
on the existing nonzero-dimensional quantum-memory Hilbert space. Thus the
printed equality cannot hold in partial-correctness mode.

The counterexample applies also to a single branch, exactly the K=1 case
described in C4. It needs no precondition on the chosen postcondition, no
termination hypothesis, and no modification of the language or Param rule.
The corrected general liberal-precondition formula remains pending approval.

Checked in `auxiliary.v`, module
`CQParameterizedCounterexample`: `parameterized_zero_partial` proves the
identity liberal precondition; `parameterized_zero_printed` proves the
printed precondition is zero; `parameterized_zero_counterexample` proves
their inequality at every store. The existing `selector_pre_sum` and
`parameterized_wp` identify that precondition with the paper's guarded sum.
Direct compilation, qualified Dune integration, and the assumptions audit
passed. Only inherited classical foundations and the existing `qreg.G`
memory parameter occur.


<a id="phase-counterexample-notes"></a>

## PHASE COUNTEREXAMPLE NOTES

### Checked ordinary-distance counterexample for phase estimation

Source: classical.pdf, Section 7.3, PDF pp. 36–38, Equation (13), Equation
(16), and Lemma 7.1; see diagnosis C6 in PROOF_NOTES.md#proof-gaps. This checks the
printed ordinary-distance claim and does not adopt a repaired metric.

Use the existing concrete witness phi=1-1/1024, n=1, epsilon=1/2, t=3.
The paper's precision prescription gives 1+ceil(log_2(3))=3. Its success
event on the eight outcomes m is |phi-m/8|<1/2. Outcome zero is outside
this event because phi>1/2.

The already checked exact phase-estimation amplitude at zero is
A=(1/8) sum_(j<8) exp(2*pi*i*j*phi). Integer periodicity rewrites each
summand as exp(-2*pi*i*j/1024). Put a_j=pi*j/1024. Since pi<=4 and j<8,
0<=a_j<=1/4. The identity cos(2a)=1-2 sin(a)^2 and |sin(a)|<=|a| give
cos(2a_j)>=1-2(1/4)^2=7/8. Thus Re(A)>=7/8, and the norm of A is at
least Re(A). In particular |A|^2>1/2. This looser bound suffices and uses
the same concrete witness as C6.

The final output state is normalized, so Parseval's identity makes the
sum of all eight nonnegative Born probabilities equal to one. The
ordinary-distance success event excludes zero, hence its probability is
at most 1-|A|^2<1/2=1-epsilon. This is a counterexample to the printed
uniform lower bound; it adds no assumption about a circular-distance
replacement or about order-finding correctness.

The implementation is `algorithms.v`, module
`ClassicalPhaseCounterexample`. `witness_phase_bounds`, `cosine_small`,
and `orbit_angle_bound` prove the witness range and scalar estimates.
`zero_amplitudeE` identifies the actual phase-estimation amplitude with
the finite periodic sum; `zero_amplitude_real` proves its real part is
at least 7/8. `zero_probability_gt_half` proves that the zero outcome has
Born probability strictly greater than one half. `ordinary_success` is
exactly the printed ordinary absolute-error test for n=1 and t=3;
`ordinary_success_probability` sums its actual output-state Born weights.
`zero_not_ordinary_success` excludes zero, and
`ordinary_success_below_half` proves that the entire success probability
is less than one half. `printed_phase_bound_counterexample` combines the
valid phase range with the negation of the claimed lower bound.

The normalization/complement step uses the separately checked
`ClassicalPhaseProbability.onb_event_complement_bound`; its argument is
in [phase probability notes](PROOF_NOTES.md#phase-probability-notes). No probability, cosine estimate, or
normalization fact is assumed in the final counterexample theorem.
The explicit source constants correspond to n=1, epsilon=1/2 and t=3;
the elementary evaluation of the paper's logarithmic precision formula
is stated above, rather than introducing a logarithm/ceiling program API.
The module passes direct and mapped Dune compilation. Audits of both the
unchanged source and the mapped module cover `zero_probability_gt_half`,
`ordinary_success_below_half`, and `printed_phase_bound_counterexample`.
They report only the inherited classical real/choice/extensionality
foundations. The proof introduces no new axiom and does not depend on the
quantum-memory parameter `qreg.G`.


<a id="phase-probability-notes"></a>

## PHASE PROBABILITY NOTES

### A finite Born-event complement bound

This supporting argument supplies the event-probability step used to inspect
the classical paper's Section 7.3 phase-estimation claim (C6). It is valid
for every finite orthonormal basis, independently of any phase-estimation
error estimate.

Let b_i be an orthonormal basis and let psi be normalized. Expanding psi in
that basis and taking its inner product with itself gives Parseval's identity:
the sum of |<b_i,psi>|^2 is <psi,psi>=1. Every summand is nonnegative.
If an event P excludes i0, its sum is therefore no greater than the sum
over all i different from i0: for each index the event indicator is at most
the indicator of inequality with i0. Splitting the total sum at i0 gives
the latter sum as 1-|<b_i0,psi>|^2. This proves the desired bound without
an additional dimension assumption; an index i0 is already supplied.

The formal version first proves the generic orthonormal-basis result for a
vector with inner product one, and then specializes it to the computational
basis of an inhabited finite type and a normalized-state value. No global
quantum register model is needed.

The checked module `ClassicalPhaseProbability` in `algorithms.v`
provides `born_total`, `onb_event_complement_bound`, and
`computational_event_complement_bound`. Focused Rocq 9.1 compilation and
Dune integration succeeded. The assumptions audit of all three results
reports only inherited real/classical foundations: Dedekind-real decisions,
extensionality, and choice. It includes no `qreg.G` or new axiom.
The generic theorem takes only a finite orthonormal basis,
a vector with inner product one, an event, and an excluded outcome.


<a id="predicate-support-notes"></a>

## PREDICATE SUPPORT NOTES

### Quantum support of predicate transformers (Lemma 4.14(1), p. 22)

Let Z contain the command's quantum footprint, and represent an assertion on
Z by its cylindrical lift to the ambient memory. Put T = complement(Z).
The completely positive unital depolarizer on T sends any ambient operator A
to the cylindrical lift of tr_T(A)/dim(T). This identity holds for arbitrary
operators, by the previously checked matrix-unit proof. The normalized
partial trace is an effect when A is an effect: its cylinder is the image of
an effect under a completely positive subunital map, and cylinder lifting
reflects both positivity and the upper bound I.

The depolarizer fixes every cylinder on Z, since it is unital and acts on
disjoint T. Because the command does not touch T, it commutes with wp.
Consequently wp of the original cylinder is fixed by the depolarizer, and
therefore equals the cylinder of its normalized partial trace on Z. The
same argument applies to wlp by the checked unital equality, including
diverging programs. This constructs a local effect-valued assertion on Z
for both predicate transformers; it does not merely assert a support tag or
assume a decomposition of the result.

The finite ambient context is the shared language model. The proof applies
to every subsystem Z, including the empty subsystem, and to state-dependent
effect assertions. The claim concerns an available support Z, as in the
paper's typed assertion spaces; it does not claim Z is the minimal support
of the resulting operator.

Checked in `CQPredicateSupport`: `local_operator_cylinder` identifies the
normalized partial trace's ambient lift, and `local_operator_effect` proves
its effect bound. `depolarizer_fixes_local` proves that local predicates are
fixed. `local_pre` constructs the local assertion, and `local_preE` /
`pre_quantum_support` prove the pointwise operator and packed-assertion
equalities for both total and partial predicate transformers.

Validation: the module passes direct compilation and the mapped Dune build.
`Print Assumptions` for `local_operator_effect`, `local_preE`, and
`pre_quantum_support` reports only the inherited classical real, choice, and
extensionality foundations and the existing `qreg.G` memory context. No new
axiom or admitted obligation is used.


<a id="primitive-frame-notes"></a>

## PRIMITIVE FRAME NOTES

### Primitive frame rules (Table 5, p. 31)

The assertion is the cylindrical lift of an effect-valued function on a
quantum subsystem S. The physical target register q is disjoint from S.
There is no classical independence assumption: both the local assertion and
the preparation, unitary, or measurement expression may depend on the input
store. Initialization and unitary execution leave that store unchanged.

For Init0 and Unit0, the dual of the local trace-preserving channel is
unital. Its ambient extension acts on a lifted assertion A on disjoint S
as A tensor E*(I). This equals A tensor I, hence the original cylindrical
assertion. This argument proves initialization by every normalized
state-valued expression; initialization by the paper's zero state is an
explicit instance. The primitive channels preserve trace, so the same
precondition equation holds for weakest and weakest liberal preconditions.

For Meas0, the primitive predicate transformer is the finite sum
sum_i M_i* lift(A(m[x:=i])) M_i. The local target operators commute with
the lifted assertion on disjoint S. Each summand therefore equals the
cylindrical lift of A(m[x:=i]) tensor (M_i* M_i). The sum is an effect:
equivalently it is the established measurement weakest precondition of an
effect assertion. Thus it can be packed as an assertion without an extra
well-formedness premise. Completeness of the measurement makes its weakest
liberal precondition identical. The existing independent core calculus
derives the resulting triples in both correctness modes.

The development uses the shared language's finite qType outcome family,
including state-dependent complete measurements. No commutation premise or
desired validity claim is assumed; commutation follows from the checked
tensor-support lemmas and physical register disjointness.

The checked implementation is `auxiliary.v`, module
`CQPrimitiveFrame`: `initial_pre_frame` and `unitary_pre_frame` give the
invariance equations; `derives_initialize_frame`, `derives_init0`, and
`derives_unit0` give the corresponding core-calculus derivations.
`measurement_pre_frame` gives the explicit tensor sum,
`measurement_tensor_effect` proves its effect bound, and `derives_meas0`
derives the measurement rule for the constructed assertion in both modes.

The mapped assumption audit of all three Table-5 derivation theorems reports
only inherited classical real, choice and extensionality foundations and
the existing ambient-memory parameter `qreg.G`.


<a id="proof-gaps"></a>

## PROOF GAPS

### Proof gaps and fidelity decisions

Source: Yuan Feng and Mingsheng Ying, *Quantum Hoare Logic with Classical
Variables*, ACM TQC 2(4), article 16 (2021), `classical.pdf`. Page numbers below
are PDF page numbers, equal to the suffix of the printed article page number.

#### C1. The asserted omega-CPO of assertions is false

**Location:** page 11, paragraph following Definition 3.5; consequences on
pages 13-14 (Lemma 3.11(3-4)), page 22 (Definition 4.13), and pages 27-29
(weakest-precondition-based completeness arguments).

**Status:** mathematical counterexample established. On 2026-10-03 the user
approved unrestricted effect-valued semantic predicates for limits and
predicate transformers, while retaining the exact paper assertion subclass.
The broader domain is an explicit correction, not a proof of the false
original claim. No Rocq counterexample theorem is claimed yet.

Definition 3.5 requires both a countable image and first-order definability of
every fiber. Pointwise monotone limits need not retain either requirement.
Here is a counterexample which already fails the countable-image requirement,
and also proves that no least upper bound exists inside the stated domain.

Take the permitted model with countably infinitely many Boolean variables
`b_0, b_1, ...`, no quantum variables, and consequently scalar effects in
`[0,1]`. Identify Boolean values with `0` and `1`. Define

```
f_n(sigma) = sum_{i < n} 2 sigma(b_i) / 3^(i+1)
g_n(sigma) = f_n(sigma) + 1 / 3^n.
```

Both functions are legitimate assertions: their images are finite; their
fibers are finite Boolean combinations of the finitely many equalities
`b_i = true` and `b_i = false`; and their values lie in `[0,1]`, since
`sum_{i<n} 2/3^(i+1) = 1-3^(-n)`. The sequence `f_n` is increasing.
For every `m,n`, `f_m <= g_n`: when `m <= n`, use monotonicity; when `m > n`,
bound the tail by `3^(-n)`. Thus every `g_n` is an upper bound of the whole
sequence within the paper's assertion domain.

If this sequence had a least upper bound `L` in that domain, leastness would
give `f_n <= L <= g_n` for every `n`. Since `g_n-f_n = 3^(-n)` tends to zero,
pointwise this forces

```
L(sigma) = sum_{i >= 0} 2 sigma(b_i) / 3^(i+1).
```

This map has uncountable image. Indeed, if Boolean sequences first differ at
index `k`, their sums differ by at least
`2/3^(k+1) - sum_{i>k}2/3^(i+1) = 1/3^(k+1) > 0`.
It therefore injects the uncountable set of Boolean sequences into its image.
This contradicts Definition 3.5(1). The constant-one assertion remains an
upper bound; the failure is existence of a *least* upper bound.

The approved repair uses unrestricted effect-valued semantic predicates with
a separate representability predicate. Merely retaining countable images and
declaring a pointwise supremum does not repair the theorem. Program syntax,
cq-states, operational semantics, and denotational semantics do not depend on
this false assertion-CPO claim and can be developed independently.

#### C2. The state omega-CPO argument needs support and mass bounds

**Location:** page 10, Lemma 3.3; page 14, Lemma 3.11(1).

**Status:** state-domain argument formalized in `state.v` as
`CQState.chain_converges`, `chain_sup_upper`, `chain_sup_least`, and
`chain_sup_pointwise`, with `bottom_least` for the zero state.
`CQExpectation.expect_chain_sup` proves the expectation-limit statement of
Lemma 3.11(1). `CQExpectationLimits.expect_semantic_sup` and
`expect_semantic_inf` prove the assertion-limit clauses in the approved domain.

For an increasing sequence of cq-states `Delta_n`, use finite-dimensional
positive-operator monotone convergence separately at every store to define
`Delta(sigma) = sup_n Delta_n(sigma)`. Its support is contained in the
countable union of the supports of `Delta_n`, hence is countable. For any
finite set `F` of stores, continuity of trace and finite addition gives
`sum_{sigma in F} tr Delta(sigma)
 = lim_n sum_{sigma in F} tr Delta_n(sigma) <= 1`.
Taking the supremum over finite `F` establishes total mass at most one.
Pointwise leastness gives leastness of the cq-state. The zero function is
least. The same finite-sum argument, now with the nonnegative summands
`tr(Theta(sigma) Delta_n(sigma))`, proves monotone convergence of expectation.
No finiteness of the classical store space is required.

#### C3. Terminal computations must retain path multiplicity

**Location:** pages 16-18, Definition 4.1, Lemma 4.2, Definition 4.3, and
Lemma 4.4; pages 19-20, Lemma 4.6(11).

**Status:** branch-labelled operational summation and its denotational
correspondence are formalized for the implemented language, including
state-dependent measurements and unbounded loops, in `semantics.v`. The
2026-10-03 continuation requested cqwhile's shared types/expressions and
finite-outcome `mexpr` interface; countably infinite measurements are outside
this revised core API.
`ClassicalOperational.operational_summable` proves summability and
`operational_denotational` proves equality with the compositional semantics.
`eval_route_sound` and `terminating_route` prove existence correspondence
between successful routes and the explicit small-step executions. An explicit
bijection between proof objects of `terminates` and successful routes has not
been proved; these results do not claim such a bijection.

Distinct random or measurement outcomes can later reach identical stores and
identical density operators. A set of endpoint configurations would discard
their multiplicity. Index the sum by finite terminating derivations (routes),
with each probabilistic/measurement outcome recorded. Remove or retain zero
branches consistently; retaining them contributes zero and does not change
the sum. Bound every finite prefix-free collection of terminating routes by
the input trace, using trace preservation of normalized sampling and complete
measurement and trace nonincrease of all other commands. Countability of the
nonzero branching gives countability of finite routes. At each output store,
the bounded positive sum converges in the finite-dimensional operator space.
The route-state family also has bounded finite sums of trace norms, hence
converges in the complete space of summable operator families. Partitioning routes
by the number of loop unfoldings yields the increasing sequence of finite
unrollings and its supremum. This proves the operational sum agrees with the
unbounded denotational loop, rather than making a finite approximation.

The implementation adapts the preserved `cqwhile` route summation proof.
`ClassicalOperational.route` explicitly records typed random and measurement
outcomes; `TR_seqc` keeps both sequential subroutes. Consequently, coincident
endpoints from distinct outcomes remain distinct summands. The generic
`atomic_route_adequacy` lemma uses injective outcome encodings and
`CQInstrument.instrument_psum_bound` for possibly infinite random-assignment outcome families.
`equal_OS_DS_seqc` and `equal_OS_DS_while` establish the sequential and
unbounded-loop cases; `equal_OS_DS` assembles all constructors. The older
`cqwhile.equal_OS_DS` still applies only to its own syntax; the new result is
a separate theorem about `ClassicalLanguage.command`, without its inherited
`Eqdep.eq_rect_eq` dependency.

#### C4. Parameterized-unitary wlp formula misses abort inputs

**Location:** page 16, parameterized-unitary syntactic sugar; page 23,
Lemma 4.15(3).

**Status:** the wp formula and original Param inference rule are checked,
including invalid-input Abort boundaries. The printed wlp equality is false;
its correction remains pending approval.

The sugar aborts if a parameter is outside its allowed finite range or selected
register indices are invalid. Lemma 4.15(3) states the same guarded sum formula
for both `wp` and `wlp`. At an invalid input every guard is false, so that
formula is zero. But Table 3 explicitly gives `wlp.abort.Theta = top`.
For example choose `K=1` and constant parameter expression `e=0`.
The stated formula is correct for `wp`. For `wlp`, add the identity effect on
the invalid-input guard, or restrict the equality to valid inputs.

The printed Table 5 `(Param)` inference rule is nevertheless sound without
changing that formula. Its guarded-sum precondition vanishes on invalid
inputs, so the total-correctness rule follows from the correct `wp` equality;
total validity then implies partial validity. To formalize this independently
of the disputed `wlp` equality, enumerate the finite valid parameter/register
choices, select the unique matching integer tuple, and execute its unitary;
if none matches, execute `Abort`. Distinct selected register indices ensure
that each selected quantum register is well formed. Conditional unfolding
gives the branch weakest precondition at the selected index and zero when no
index matches. Uniqueness identifies this case split with the printed finite
guarded sum. No invalid-input liberal-precondition equality is required.

The checked formal results are `CQParameterized.selected_register_valid`,
`selected_wp`, `selected_pre_sum`, and `derives_param` (both correctness
modes). `parameterized_zero_abort` and `selected_duplicate_abort` check the
invalid-parameter and repeated-register boundaries. These establish the
original guarded-sum inference rule without adopting the disputed wlp claim.

`CQParameterizedCounterexample.parameterized_zero_counterexample` now
formally proves the mismatch for constant parameter zero: the actual liberal
precondition is identity and the printed guarded precondition is zero at
every store, for every postcondition. See
[parameterized counterexample notes](PROOF_NOTES.md#parameterized-counterexample-notes); this is a counterexample, not an
adopted general correction.

#### C5. Classical ranking proof overstates pathwise termination

**Location:** page 33, proof of Theorem 6.1 for `(C-WhileT)`.

**Status:** `CQClassicalRanking.valid_integer_while` and
`derives_integer_while` prove the signed-integer rank-family formulation.
`CQGhostRanking.valid_fresh_integer_while` and
`derives_fresh_integer_while` now prove the printed single-body-premise rule
using syntactic freshness, invariant framing, and existential elimination. The formal proof bounds outer body completions by
rank induction and does not claim bounded small-step runtime.

The proof says all computations terminate within `sigma(t)` steps. The
premise is semantic total correctness (an expectation inequality), which
guarantees almost-sure termination, not termination of every infinite path.
A loop body may itself have arbitrarily long terminating runs and an infinite
probability-zero run. A decreasing integer rank bounds the number of outer
body completions while the guard remains true, not the number of small steps
nor every possible path. A sound proof must combine almost-sure termination
of each reached body with a decreasing nonnegative rank and countable
additivity; it must not assume bounded execution time.

#### C6. Phase-estimation error must account for wraparound

**Location:** pp. 36–38, Equation (13), the set `K` in Equation (16), and
Lemma 7.1. The ordinary absolute-value bars were checked in rendered PDF
pages 37–38, not inferred from the text extraction.

**Status:** the concrete counterexample is formally checked in
`algorithms.v`; the correction to the stated error metric is
awaiting user approval. The original metric is retained, and no corrected
concentration theorem is claimed.

For `N = 2^t`, the probability of measurement outcome zero is

```
p_0(phi) = |(1/N) sum_{j=0}^{N-1} exp(2*pi*i*j*phi)|^2.
```

Fix any allowed `n,t`. As `phi` tends to one from below, every summand tends
to one, so `p_0(phi)` tends to one. But zero does not belong to the paper's
`K = {m : |phi-m/N| < 2^(-n)}` once `phi > 2^(-n)`. Therefore its claimed
success probability is at most `1-p_0(phi)`, which tends to zero. This
contradicts a uniform lower bound `1-epsilon` for any `epsilon < 1`.

A concrete instance uses `n=1`, `epsilon=1/2`, hence
`t = 1 + ceil(log_2(3)) = 3`, and `phi = 1-1/1024`. With `N=8`, write
`A = (1/8) sum_{j=0}^7 exp(-2*pi*i*j/1024)`. The checked proof uses
`a_j = pi*j/1024`, `pi <= 4`, and `j < 8` to obtain `|a_j| <= 1/4`.
The identity `cos(2*a) = 1-2*sin(a)^2`, together with
`|sin(a)| <= |a|`, gives

```
cos(2*a_j) >= 7/8,
Re(A) >= 7/8,
p_0(phi) = |A|^2 >= 49/64 > 1/2.
```

The actual output state is normalized. Parseval's identity and nonnegative
Born weights bound the probability of the success event, which excludes
zero, by `1-p_0(phi)`. Thus it is strictly less than
`1/2 = 1-epsilon`.

`ClassicalPhaseCounterexample.zero_amplitudeE` identifies the actual
phase-estimation amplitude with this periodic sum; `zero_amplitude_real`
and `zero_probability_gt_half` prove the estimates.
`ordinary_success_below_half` bounds the full printed success event, and
`printed_phase_bound_counterexample` combines the valid phase range with
the negation of its claimed lower bound. The complement step is checked
in `ClassicalPhaseProbability.onb_event_complement_bound`. The final
counterexample has no hypotheses. The explicit source constants are
`n=1`, `epsilon=1/2`, and `t=3`; the logarithm/ceiling calculation above
is documented arithmetic rather than a formalized precision-selection API.
See [phase counterexample notes](PROOF_NOTES.md#phase-counterexample-notes) for the prior argument and theorem map.

The standard phase-estimation guarantee uses circular distance
`min(|phi-m/N|, 1-|phi-m/N|)`. An alternative ordinary-distance theorem
needs an explicit boundary condition that rules out wraparound. In the
order-finding application, nonzero phases `s/r` lie at least `1/r` from both
endpoints, so an appropriate boundary lemma can reconnect the circular
estimate to ordinary rational approximation there. This mathematical repair
must be distinguished from proving Lemma 7.1 literally as printed.

#### C7. Order-finding postprocessing selects the wrong denominator

**Location:** page 38, Section 7.4 definition of `f`, and page 39 claim that
`f(k/2^t)=r` whenever `gcd(s,r)=1` and `k` belongs to `K_s`. The definition
was checked in the rendered page 38: it explicitly says to return the
**minimal** denominator among all continued-fraction convergents satisfying
`|m/n-x| < 1/(2n²)`. There is no modular-order test in that selection.

**Status:** counterexample established; a repaired postprocessing algorithm
requires user approval before its correctness is formalized. Independent
spectral and circuit identities can proceed.

Take modulus 15, multiplier 2, and order `r=4`. Choose `s=1`, coprime to 4,
and a measured dyadic value `k/2^t=1/4` (every `t>=2` permits it). This value
belongs to `K_s` with approximation error zero, but its continued fraction
has convergent `0/1`, whose error `1/4` is strictly smaller than `1/(2*1²)`.
Thus the printed algorithm returns denominator 1, not 4. Even excluding the
zero numerator is insufficient in general: for exact phase `3/4`, convergent
`1/1` has error `1/4<1/2`, so the minimal selected denominator is again 1.

In fact the ideal order-finding circuit for this example produces only
`0,1/4,1/2,3/4`, with equal probabilities. The printed rule returns 1 at
`0,1/4,3/4` and 2 at `1/2`, so it never returns the true order 4, contradicting
the positive success bound in Equation (18).

A standard repair is to enumerate suitable convergent denominators under a
known bound and retain a denominator only when modular exponentiation verifies
`2^n mod 15 = 1` (generally `x^n mod N = 1`), choosing the least verified
candidate. Its correctness and denominator-bound conditions require an actual
continued-fraction theorem; merely replacing the printed `f` by a function
assumed to return the order would hide the target claim. The repaired function
also needs an explicit failure result when no verified candidate is found.

Checked counterexample support is now in `shor.v`: the literal
selector returns 1 at both 1/4 and 3/4 (`printed_quarter_counterexample`,
`printed_three_quarters_counterexample`), while `two_mod_fifteen_order` proves
that the order of 2 modulo 15 is 4. `convergents_stable` justifies the finite
Euclidean recursion bound. No repaired selector is used.

#### Explicit maximal computations (Definition 4.1, pp. 16–17)

The existing operational sum uses successful finite routes. To also represent
the paper's computations themselves, configurations retain an optional residual
command, a classical store, and the unnormalized quantum operator. A lifted
step carries an actual Table-2 step witness and requires its destination
operator to be nonzero, exactly as in the rendered Definition 4.1. A finite
computation is a finite path whose endpoint has no such outgoing transition; this includes successful
termination and abort or blocked residual commands. An infinite computation
is a natural-number-indexed path with a step at every index, hence has no
finite terminal endpoint. This definition imposes no probability or fairness
condition on an individual path.

Induction over a finite path proves positivity, density preservation and
trace nonincrease from the corresponding one-step theorems. The same induction
on a prefix index applies to every infinite path. Unfolding a true-guard Skip
loop and completing its Skip body alternate forever; this supplies an actual
infinite computation, independently of its already-proved zero denotation.
Successful paths with nonzero output coincide with the existing `terminates`
relation restricted to nonzero output: quantum maps preserve zero, so a
nonzero endpoint precludes zero at any earlier step. The route sum can retain
zero-output paths harmlessly; every such summand is the zero operator.

Checked in `semantics.v`: `ClassicalComputations.live_step`, `path`,
`maximal_path`, `finite_computation`, and `infinite_computation` give the
explicit path types. A raw configuration is physical when `well_formed`;
both computation types require density of the initial configuration, and
`path_density`/`infinite_computation_density` preserve it. `path_trace_le` and
`infinite_path_trace_le` prove trace nonincrease. `successful_maximal_iff`
identifies successful maximal paths with `terminates` and nonzero output;
`successful_route_iff` also connects the existing outcome-labelled routes.
`true_skip_infinite` constructs the alternating divergent computation, while
`abort_computation`, `terminal_none`, and `terminal_zero` cover finite and
zero-state boundaries. No change to the operational sum is required.

##### C7: the printed selector never returns an order above two

For any measured rational a/b with 0 <= a < b, the failure is more general
than the quarter-phase example. If 2a<b, the first convergent 0/1 satisfies
the strict approximation test, so the selected minimum denominator is at
most one. If b<2a, then b/a=1 and the second convergent is 1/1; its error
1-a/b is less than one half, again bounding the selected minimum by one.
If 2a=b, the Euclidean continued fraction is exactly [0;2]. Its first
convergent fails the strict test at equality and the second is the exact
rational 1/2, so the selector returns two. This exhausts the measured range.
Consequently the literal printed selector cannot return any order greater
than two at any precision. This is a diagnosis of the printed algorithm,
not an adopted repair. The formal finite-list argument uses that a fold of
minimum is bounded above by every retained denominator.

Checked in `shor.v`:
`ClassicalPostprocessCounterexample.printed_denominator_at_most_two` proves
the general bound for every rational in the measured range, and
`printed_never_four` rules out the true order in the modulus-15 example at
every precision. The proof uses only finite arithmetic and lists.


<a id="quantum-space-notes"></a>

## QUANTUM SPACE NOTES

### Auxiliary quantum-space rules (Table 5, p. 31)

These rules operate in the fixed ambient quantum memory of the shared
language. A local assertion on S is represented by its cylindrical lift,
which tensors it with the identity on the remaining memory. All register
side conditions below are finite-set disjointness conditions on actual
quantum footprints.

For Tens, let M be an effect on an unused register T. Positivity gives
M = B B*, so F(A) = B A B* is completely positive and F(I) = M <= I.
Because an assertion on disjoint S acts trivially on T, applying the local
extension of F to its cylindrical lift gives the lift of its tensor product
with M. The checked SupOper rule therefore proves Tens in both total and
partial correctness. The arbitrary output assertion parameters in the rule
are accompanied only by equalities to these explicit tensor expressions;
they package the existing effect type and are not correctness premises.

For a finite orthonormal family v_i on an unused register, the map
F(A) = sum_i lambda_i <v_i,A v_i> I is completely positive: each summand is
the dual of the state-preparation map for v_i, multiplied by a nonnegative
weight. If sum_i lambda_i <= 1, F(I) <= I. Acting on the labeled block
sum_i P_i tensor |v_i><v_i| removes the label and leaves sum_i lambda_i P_i.
This gives L-Sum in both correctness modes. The same selector with a complete
orthonormal basis and uniform weights gives normalized partial trace.

For Trace, use the selector on the complete delta basis of the traced
register T, with weight 1/dim(T) on each vector. Its local action on any
operator A is tr(A) I/dim(T); positivity and unitality make it a dual quantum
operation. To identify its full-memory lift, expand an arbitrary operator
in delta matrix units. Split each index into the part on T and the part
on its complement. The lifted selector sends a matrix unit to zero unless
its two T indices agree; when they agree it sends it to I_T/dim(T) tensored
with the remaining matrix unit. The defining basis sum of partial trace
has exactly the same two cases. Finite linearity therefore identifies the
lift with the cylindrical lift of partial trace divided by dim(T), including
off-diagonal matrix units. SupOper then gives Trace in both correctness
modes whenever T is disjoint from the program's quantum footprint.

The Trace argument is checked in `CQQuantumTrace.partial_trace_outp`,
`lift_depolarizer`, and `trace_assertionE`. The corresponding inference rule
is `derives_trace`, in both total and partial correctness.

SupPos instead selects the unit vector sum_i conjugate(alpha_i) v_i.
On the entangled input (1/sqrt(d)) sum_i phi_i tensor v_i, contraction yields
(1/sqrt(d)) sum_i alpha_i phi_i, and likewise at the output. Thus SupOper
produces both target predicates scaled by 1/d. In total correctness this
positive scalar cancels from the expectation inequality. It cannot generally
cancel from the additive nontermination allowance for partial correctness;
accordingly Theorem 6.1 explicitly excludes partial SupPos.

Checked implementations:

- `CQQuantumSpaceRules.effect_map_exists`, `tensor_effect`, and
  `derives_tens_direct` construct the tensor assertions and derive Tens.
- `CQQuantumSelector.selector_dqo`, `selector_outp`, `selector_labeled`, and
  `derives_lsum` prove the explicit weighted label-removal rule.
- `CQQuantumSuperposition.selecting_overlap`, `selecting_norm`,
  `selected_entangled`, and `derives_suppos` prove total SupPos. The rule
  permits any positive common input-projector scale r; the paper uses
  r = 1/d. Orthogonality of the data families is sufficient to make the
  displayed expressions effects, but the contraction proof itself only
  needs orthogonality of the label family and normalized coefficients.

L-Sum and SupPos take existing effect assertions together with exact
equalities to their displayed operator formulas. These equalities express
assertion construction, not an assumed channel property or desired Hoare
inequality. Their only derivability premise is the corresponding paper
premise; all needed transformations are proved explicitly.

The mapped assumption audit of all three final rule theorems reports only
the inherited classical real-model, choice and extensionality foundations
and the existing `qreg.G` quantum-memory parameter. No new axiom, admission,
or dependent-equality assumption occurs in these proofs.


<a id="ranking-complement-notes"></a>

## RANKING COMPLEMENT NOTES

### Complement rankings: classical Lemma 5.4 and WhileT′

Source: `classical.pdf`, PDF pages 29–30, Lemma 5.4 and the displayed
WhileT′ rule. The decreasing ranking definition is Definition 5.2. The
assertion domain here is the already approved full semantic effect domain.

Fix a guard b and body S. For any effect assertions R,T, the guarded ranking
inequality `b ∧ wp(S,R) ≤ T` is equivalent to partial correctness of
`{b ∧ (I−T)} S {I−R}`. At a store satisfying b this is the order-reversing
complement identity `wp(S,R) ≤ T` iff `I−T ≤ I−wp(S,R)`, together with
`wlp(S,I−R)=I−wp(S,R)`. At a store not satisfying b, both respective
guarded inequalities hold because zero is below every effect. This proves
the equivalence without a termination assumption on S.

Given a decreasing zero-limit ranking R_n, put Ψ_n=I−R_n. Complementation
reverses the pointwise operator order, so Ψ_n is increasing. Continuity of
operator subtraction gives Ψ_n→I at each store. The supremum of a monotone
effect sequence is also its operator-norm limit; uniqueness of limits thus
gives `sup Ψ_n=I`. The initial bound becomes `P≤I−Ψ_0`, and the guarded
inequalities become the required partial triples by the preceding identity.

Conversely, take an increasing Ψ_n with supremum I, initial bound
`P≤I−Ψ_0`, and partial triples `{b∧Ψ_(n+1)} S {Ψ_n}`. Put R_n=I−Ψ_n.
Order reversal gives decrease. Monotone effect convergence to the given
supremum, followed by subtraction from I, gives R_n→0. The same guarded
identity converts each partial triple to the ranking step. Thus R_n is an
actual Definition-5.2 ranking, proving both directions of Lemma 5.4.

Finally, for WhileT′, apply soundness to its independent partial derivation
premises, construct the ranking above, and apply the existing independent
`DWhileTotal` constructor to the supplied total invariant derivation. No
semantic-validity constructor or pre-assumed ranking is introduced.

The checked source is `hoare.v`, module `CQRankingComplement`:

- `mask_complement_le_iff` and `guarded_wp_partial_iff` prove the guarded
  complement/partial-triple identity.
- `complement_decreasing`, `complement_sup_top`, and
  `complement_zero_of_sup` prove the sequence order and convergence facts.
- `ranking_of_partial` constructs the decreasing ranking explicitly.
- `ranking_iff_partial` proves both directions of Lemma 5.4, with exactly
  the increasing-sequence, initial-bound, supremum, and partial-triple clauses.
- `derives_while_partial_ranking` derives WhileT′ in the existing independent
  `CQHoare.derives` system.

Direct compilation and the six-result assumptions audit passed on 2026-10-03.
The generic complement lemmas use only the inherited classical real, choice,
and extensionality foundations. The command/ranking theorems additionally use
the existing ambient-memory parameter `qreg.G`; no new axiom or admission is
introduced. Integration is recorded in the shared validation record.


<a id="shor-composite-notes"></a>

## SHOR COMPOSITE NOTES

### Distinct prime factors of the paper's Shor inputs

Source: classical.pdf, Section 7.5, PDF pp. 40–41. The printed predicate
cmp(N) requires N>2, oddness, compositeness, and exclusion of perfect
powers. Page 41 uses these conditions to conclude that the number m of
distinct prime divisors exceeds one. This arithmetic conclusion is
independent of any claim about the order-finding program.

For a natural N>1, compositeness is equivalent to not being prime. Exclude
perfect powers by requiring N != a^b whenever a>1 and b>1. This is the
usual natural-number formulation of the printed condition; a positive
integer perfect power with a negative integer base is also a power of
its positive absolute value, so allowing signed bases does not change
which positive N are excluded.

The distinct prime list of N is nonempty because N>1. If it contains only
one prime p, the standard prime factorization of N is N=p^e, where
e=v_p(N)>0. When e=1, N=p is prime, contradicting compositeness. Hence
e>1; since p is prime, p>1, and N=p^e contradicts the exclusion of perfect
powers. Therefore the list has at least two elements. Oddness is not
needed for this implication, but is retained in the explicit cmp predicate
to match its use in the paper.

Together with the independently proved counting bound, m>1 makes
2^(m-1) at least two and hence 1-1/2^(m-1) at least one half. This arithmetic
observation does not provide a success probability for the false printed
order-finding postprocessor.

The implementation in `shor.v`, module `ClassicalShorComposite`,
defines `not_perfect_power` and the faithful positive-natural `cmp`
predicate. `distinct_prime_count_gt1` proves the implication using only
N>1, non-primality, and exclusion of perfect powers;
`cmp_distinct_prime_count` specializes it to the printed input conditions.
Direct and mapped compilation pass. Both theorems' assumptions audits
report `Closed under the global context`.


<a id="shor-counting-notes"></a>

## SHOR COUNTING NOTES

### Uniform modular-unit counting (Lemma 7.2(2))

Source: `classical.pdf`, PDF pp. 40–41, Lemma 7.2(2), the definition of E(x),
and its use in Equation (21). Both rendered pages were inspected. This
number-theory statement is independent of the printed order-finding
postprocessor and of C7. It is not blocked by that counterexample.

The statement concerns an odd composite N and uniform x in {1,...,N-1},
conditioned on gcd(x,N)=1. Write r(x) for the exact multiplicative order and
E(x) for “r(x) is even and x^(r(x)/2) is not -1 modulo N.” The intended m
is the number of distinct prime divisors, represented by `size (primes N)`.
Counting prime factors with multiplicity would make the statement false for
odd prime powers: their units never satisfy E(x), whereas m>1 would give a
positive lower bound. For the distinct-prime interpretation, m=1 gives the
correct trivial lower bound zero. The stronger `cmp(N)` hypothesis used by
the program implies m>1, but is not needed for this counting lemma.

#### Complete finite counting argument

Factor N as the product of its pairwise coprime odd prime powers
q_i = p_i^(e_i), for i=1,...,m, with e_i>0 and distinct primes p_i.
Let G_i be the finite multiplicative group of units modulo q_i. The Chinese
remainder theorem gives a bijection from units modulo N to the product of
the G_i, respecting multiplication and powers. A uniformly selected unit
therefore has independent uniform coordinates x_i in G_i. Conditioning
the paper's uniform x on coprimality gives precisely this uniform unit
distribution: every unit representative lies in {1,...,N-1}, and all were
assigned the same original weight 1/(N-1).

First establish the unique-involution property for each G_i. If y^2=1
modulo q_i, then q_i divides (y-1)(y+1). The odd prime p_i cannot divide
both factors, whose difference is 2. The entire p_i-power q_i therefore
divides one factor, so y=1 or y=-1 modulo q_i. Since q_i is odd and greater
than one, these two residues are distinct. Thus -1 is the unique element
of order two. This elementary argument does not require a primitive-root
theorem modulo prime powers.

For a finite abelian group G with exactly the square roots {1,-1}, let
D be its exponent and let s=v_2(D). The exponent is positive and even,
because -1 has order two. An element g of order D exists: every finite
abelian group realizes its exponent as an element order. Define the group
homomorphism h(x)=x^(D/2). Its square is x^D=1, so its image lies in
{1,-1}; and h(g) is not 1 by the exact order of g, hence h(g)=-1.
The image is therefore exactly {1,-1}. Multiplication by g is a bijection
between the fibers of 1 and -1: h(gx)=-h(x). Consequently each fiber has
exactly half the elements of G.

Every element order r divides D. For a positive divisor r of a positive
even D, r divides D/2 exactly when v_2(r)<v_2(D): writing D=r*a reduces
the assertion to a being even. Therefore h(x)=1 exactly when
v_2(ord(x))<s, and h(x)=-1 exactly when v_2(ord(x))=s. The maximal
valuation fiber has size |G|/2; each smaller individual valuation fiber
lies inside the other half; larger fibers are empty. Thus, for every
integer k≥0,

    2 * #{x in G : v_2(ord(x))=k} ≤ |G|.

Apply this to each G_i. Put r_i=ord(x_i), k_i=v_2(r_i), and
r=ord(x)=lcm_i r_i. The CRT bijection gives the order identity directly:
a power of x is 1 exactly when that exponent is divisible by every r_i.
Hence v_2(r)=max_i k_i. If every k_i is zero, r is odd and E(x) fails.
Otherwise put k=max_i k_i>0. Since r_i divides r,

* if k_i<k, then r_i divides r/2 and x_i^(r/2)=1;
* if k_i=k, then r_i does not divide r/2. Nevertheless the square of
  x_i^(r/2) is 1, so the unique-involution property gives x_i^(r/2)=-1.

CRT now says x^(r/2)=-1 modulo N exactly when every k_i equals k.
Combining the odd-order and even-order cases, failure of E(x) is exactly
the event that all k_i are equal.

Let c_i(k)=#{x_i in G_i : v_2(ord(x_i))=k}. Only finitely many k occur.
Independence gives the failure count B=Σ_k Π_i c_i(k). For each fixed k,
bound all factors except the first by the half-size inequality above:

    2^(m-1) * Π_i c_i(k) ≤ c_1(k) * Π_(i>1) |G_i|.

Summing and using Σ_k c_1(k)=|G_1| gives

    2^(m-1) * B ≤ Π_i |G_i| = |units modulo N| = totient(N).

The unit set is nonempty (it contains 1), so division by its cardinality
is legitimate. Taking complements yields exactly

    Pr[E(x) | gcd(x,N)=1] ≥ 1 - 1/2^(m-1).

This is entirely finite counting. It does not assume an order-finding
program's success, and does not infer that its returned denominator is an
exact order. The proof requires neither a cyclicity theorem for all units
modulo p^e nor a repaired postprocessor.

#### Available checked foundations

The following APIs were inspected in the installed MathComp 2.6.0 sources.
Paths below are relative to `user-contrib/mathcomp` in the active switch.

| Obligation | Existing API |
| --- | --- |
| Distinct prime factorization | `boot/prime.v`: `primes_uniq`, `prod_prime_decomp`, `prime_decompE`, `mem_prime_decomp`, `mem_primes`, `pfactor_coprime`, `coprime_pexpr` |
| Binary CRT and explicit inverse | `boot/div.v`: `chinese_remainder`, `chinese`, `chinese_modl`, `chinese_modr`, `chinese_mod` |
| Units modulo an arbitrary N>1 | `algebra/zmodp.v`: `{unit 'Z_N}`, `units_Zp`, `unitZpE`, `unit_Zp_expg`, `val_Zp_nat`, `card_units_Zp`, `units_Zp_abelian` |
| Positive group exponent and all element orders divide it | `solvable/abelian.v`: `exponent_gt0`, `dvdn_exponent`, `expg_exponent`, `exponentP` |
| Element realizing the exponent | `solvable/abelian.v`: `exponent_witness`; `solvable/nilpotent.v`: `abelian_nil` supplies its premise |
| Exact order and power divisibility | `solvable/cyclic.v`: `order_dvdn`, `orderXdvd`, `orderXgcd`, `orderXdiv`; `finite_group/fingroup.v`: `order_gt0`, `expg_order`, `expgMn` |
| Two-adic arithmetic | `boot/prime.v`: `lognM`, `logn_div`, `logn_lcm`, `pfactor_dvdn`, `dvdn_leq_log`, `pfactor_coprime`; `boot/div.v`: `dvdn2`, `coprime2n`, `coprimeXl`, `Gauss_dvdr` |
| Equal homomorphism-fiber sizes | `finite_group/morphism.v`: `Morphism`, `rcoset_kerP`, `morphpre_set1`; `finite_group/fingroup.v`: `card_rcoset`; `finite_group/quotient.v`: `card_morphpre`, `card_morphim` |
| Product and partition counts | `boot/finfun.v`: `card_family`, `card_dep_ffun`; `boot/finset.v`: `card_partition`, `card_imset` |
| Unit cardinalities | `boot/prime.v`: `totient_gt0`, `totient_count_coprime`, `totient_pfactor`, `totient_coprime` |

`totient_count_coprime` already contains a concrete binary CRT reindexing
proof with `chinese`; it provides a local pattern for constructing the
finite unit-product bijection. The installed `units_Zp_cyclic` theorem in
`solvable/cyclic.v` assumes a prime modulus. It must not be applied to p^e
without proving the missing hypothesis. The exponent argument above avoids
that unavailable specialization.

#### Checked generic group step

`shor.v`, module `ClassicalShorGroupCounting`, directly
compiles. `dvdn_half_logn` proves the exact divisor/valuation equivalence
for a positive even n and a divisor d. `exponent_even`,
`half_exponent_square`, and `half_exponent_is_one` establish the exponent
map's arithmetic. `half_exponent_witness` derives a preimage of the unique
involution from `exponent_witness` and abelianness; no realization premise
is supplied by the caller.

The final counting proof uses an equivalent finite injection formulation.
`translate_order_valuation` proves that multiplication by this witness
changes the two-adic order valuation of every group element. Thus it sends
each fixed-valuation set into its complement. Multiplication is injective,
so the set has cardinality at most its complement. Their cardinalities sum
to the whole group cardinality, proving `order_valuation_fiber_half`:

    2 * #{x : gT | logn 2 (order x) = k} ≤ #gT.

Its premises are a finite group, abelianness, a nonidentity involution z,
and the structural fact that all square roots of one are 1 or z. The
prime-power instantiation must prove these structural premises. No
probability bound or target correctness statement is a premise.

Validation of `shor.v`: direct compilation and the mapped
Dune target pass. `Print Assumptions` for `dvdn_half_logn`,
`half_exponent_witness`, `translate_order_valuation`, and
`order_valuation_fiber_half` reports “Closed under the global context.”
The generic result introduces no axiom and uses no inherited quantum-memory
or classical-real foundation.

#### Checked arithmetic foundations and status

The mathematical proof above is complete, and the generic group step is
checked as described above. `shor.v` passes direct and mapped
compilation; its audited results are closed under the global context:
`ClassicalShorPrimePower.square_roots_mod` and `unit_square_roots` prove
the actual odd-prime-power root classification, and
`prime_power_fiber_half` instantiates the generic cardinal bound.
`shor.v` passes direct and mapped compilation of the exact failure-event
characterization in `failure_iff_equal_valuations`; its structural
homomorphism premises are described in [shor order event notes](PROOF_NOTES.md#shor-order-event-notes).
Its central assumptions audits also report closed global context.

`shor.v`, module `ClassicalShorFactorization`, supplies
`factor_index`, `factor_prime`, `factor_exponent`, and `factor_modulus`.
`factor_count_positive` and `first_factor` prove the nonempty index set for
N>1. `factor_prime_is_prime`, `factor_exponent_positive`,
`factor_modulus_gt1`, `factor_moduli_coprime`, and `factor_modulus_odd`
prove the factor side conditions. `factorization` proves their product is
N. The module passes direct and mapped compilation.

`shor.v` builds the actual modular unit operations and binary CRT.
`shor.v`, module `ClassicalShorCRTProduct`, supplies actual
component `reduction` maps, `reductions_jointly_injective`, and the
`unit_tuple_bijective` bijection. `shor.v` proves
`unit_reduce_negative_one`. All three pass direct and mapped compilation;
their audited central theorems are closed under the global context.

`shor.v`, module `ClassicalShorProductCounting`, proves
`natural_diagonal_half_bound` for arbitrary natural-number labels on a
finite product. Its mapped compilation and closed-context audit pass.
The concrete assembly below discharges its fiber premises and the event
theorem's structural hypotheses. `shor.v` now identifies this
count ratio with the conditional law induced by
`ClassicalShorProgram.uniform_probability`; its
`random_conditional_success_bound` is the paper's conditional bound for
the actual Random source and exact arithmetic order. `shor.v`
also checks the source partition and Equation (21). These results are
independent of C4, C6, and C7.

#### Assembly into the actual modular-unit count

For the final arithmetic theorem, take the index type to be the ordinal
indices of the distinct prime list `primes N`; its size is exactly m.
The checked factorization supplies q_i, their positivity and pairwise
coprimality, and their product N. Instantiate the CRT tuple bijection with
these moduli. Instantiate the event theorem with the actual reductions,
the local `negative_one q_i`, and global `negative_one N`. The reduction
of global negative one to every local negative one is an arithmetic
identity for divisors, not an additional premise.

For every unit x, the event theorem identifies its failure predicate with
the diagonal predicate of the CRT tuple. A bijection preserves predicate
cardinalities, so their failure and diagonal counts agree. Each coordinate
valuation fiber satisfies the checked prime-power half-cardinality bound.
The natural-label version of the finite product bound therefore gives
2^(m-1) times the diagonal count at most the tuple-space cardinality.
The CRT bijection and `card_units_Zp` identify this cardinality with
`totient N`. This yields the concrete failure-count theorem with only
N>1 and odd N as hypotheses; no structural CRT, root, or probability
premise remains. Composite N is a covered specialization.

The implementation is `shor.v`, module `ClassicalShorCounting`.
`factor_tuple_bijective`, `factor_reduction_jointly_injective`,
`factor_involution_nontrivial`, `factor_roots_two`, and
`factor_reduction_negative_one` discharge the structural obligations.
`failure_diagonalE` and `failure_card` identify the concrete failure event
and its cardinality; `factor_order_fiber_half` supplies every local bound.
The resulting `failure_count_bound` states

    2 ^ (size (primes N)).-1 * #|unit_failure| <= totient N.

Its only assumptions are `1 < N` and `odd N`. `unit_successE` identifies
the exact-order success predicate with the complement of `unit_failure`.
The module passes direct and mapped Dune compilation. A check of its
generalized signature confirms that `failure_count_bound` takes exactly N,
`1 < N`, and `odd N`; the structural obligations are not residual
parameters. `Print Assumptions` for `failure_diagonalE`, `failure_card`, and
`failure_count_bound` reports `Closed under the global context` for each.

The numerical corollary is checked in `shor.v` as
`ClassicalShorProbability.uniform_unit_success_bound`: for any numeric
field F, odd N>1, the uniform-unit probability of `unit_success` is at
least `1 - 1 / (2 ^ (size (primes N)).-1)%:R`. It follows from
`finite_complement_ratio`, using `card_units_Zp` and the complement
identity `unit_successE`. The complete scalar argument, including the
independent mixture inequality from Equation (21), is recorded before
formalization in [shor probability notes](PROOF_NOTES.md#shor-probability-notes).


<a id="shor-crt-notes"></a>

## SHOR CRT NOTES

### Concrete unit Chinese remainder bridge

This is the Chinese remainder step in the independent finite counting proof
of classical.pdf Lemma 7.2(2), PDF pp. 40–41. See PROOF_NOTES.md#shor-counting-notes for
the complete counting argument. No claim about the order-finding selector
or its quantum success probability is used here.

For coprime m,n>1, use MathComp's existing finite multiplicative groups
`{unit 'Z_m}`, `{unit 'Z_n}`, and `{unit 'Z_(m*n)}`. Every element has a
unique natural representative below its modulus, and its representative is
coprime to that modulus. Send a unit modulo mn to its two reductions. Each
reduction remains a unit because coprimality to mn implies coprimality to
each factor. Conversely, take the Chinese remainder of the two canonical
representatives and reduce modulo mn. It is a unit: its residues modulo m
and n equal the given units, so it is coprime to both moduli and hence to
their product. The two maps cancel because equality modulo both coprime
factors is equivalent to equality modulo their product. Thus this is a
concrete finite bijection, with the inverse given by MathComp's `chinese`.

Reduction commutes with multiplication and every natural power, since
modular reduction does. Consequently, a power of a unit modulo mn is one
exactly when the corresponding powers of both coordinate units are one.
In a finite group, this means an exponent is divisible by the global order
exactly when it is divisible by both coordinate orders. The least common
multiple has precisely this divisor property, so the global order is the
least common multiple of the two coordinate orders. These are actual group
orders, not separately postulated order witnesses.

The binary bijection also proves any finite sum over global units equals
the sum over coordinate pairs, reindexing by its inverse. Its cardinality
specialization gives the product of the two unit cardinalities. Iterating
this bridge over distinct prime powers will supply the product model used
in the counting argument; the binary lemma itself needs no primality.

The checked binary API is `ClassicalShorCRT.crt_units_bijective`,
`crt_units_mul`, `crt_units_power`, `crt_units_order_dvd`,
`crt_units_order`, and `crt_units_card`. The canonical `unit_reduction`
morphism reduces a unit modulo N to a unit modulo any divisor M>1;
`unit_reduce_value` and `unit_reduce_power` give its concrete behavior.

For an arbitrary finite family q_i>1 of pairwise coprime moduli with
product N, take all these divisor-reduction morphisms together into the
dependent finite function type. They are jointly injective: equal local
images imply the natural representatives are congruent modulo every q_i;
induction through the binary Chinese remainder theorem implies congruence
modulo their product N; the representatives are below N, so are equal.
Totient multiplicativity, proved inductively using coprimality of each
factor with the remaining product, identifies the source cardinality with
the product of the coordinate cardinalities. The dependent function type
has exactly that product cardinality. An injection between these finite
types of equal cardinality is a bijection. Hence this gives a full product
CRT interface without assuming a product representation or a success count.

The finite-family bridge is checked in `shor.v` as
`ClassicalShorCRTProduct.reduction`, `reductions_jointly_injective`,
`unit_tuple`, `unit_tupleE`, `unit_tuple_card`, and `unit_tuple_bijective`.
The tuple type is the actual dependent finite function type whose i-th
entry is a MathComp unit modulo q_i. Auxiliary `coprime_product`,
`totient_product`, and `congruence_product` prove the needed finite-product
arithmetic. These results accept an arbitrary finite index type, including
its cardinality; their explicit nontrivial-product hypothesis simply rules
out an empty factorization when N>1. They introduce no assumption about
order distributions, event counts, or program validity.


<a id="shor-modular-event-notes"></a>

## SHOR MODULAR EVENT NOTES

### Reduction of the distinguished modular involution

This supplies the concrete involution compatibility needed by the order-event
argument for classical.pdf Lemma 7.2(2), PDF pp. 40–41. Let M divide N and
assume M,N>1. The unit called `negative_one N` has canonical representative
N−1. The canonical unit reduction sends it to the representative
(N−1) mod M. Since N is divisible by M and positive, the predecessor
remainder formula gives (N−1) mod M=M−1. This is exactly the representative
of `negative_one M`. Injectivity of canonical unit representatives proves
the equality of the actual group elements. No order-finding correctness or
extra arithmetic hypothesis is used.

The checked results in `shor.v` are
`ClassicalShorModularEvent.predecessor_mod_divisor` and
`ClassicalShorModularEvent.unit_reduce_negative_one`. They use the canonical
reduction from `ClassicalShorCRT` and concrete `negative_one` from
`ClassicalShorPrimePower`.


<a id="shor-order-event-notes"></a>

## SHOR ORDER EVENT NOTES

### Exact failure event under component homomorphisms

This is the group-theoretic event identification used in the proof of
classical.pdf Lemma 7.2(2), p. 40; the full counting argument is recorded in
[shor counting notes](PROOF_NOTES.md#shor-counting-notes).

Let G be a finite group with a nonempty finite family of homomorphisms
red_i:G→H_i. Assume they are jointly injective. In each H_i, assume every
square root of one is either one or a specified nonidentity element z_i.
Let z in G project to every z_i. These are structural hypotheses that the
modular CRT construction must prove; no success-probability statement is a
hypothesis. Abelianness is unnecessary for this event-identification step.

Fix x in G. Write r=ord(x), r_i=ord(red_i(x)), k=v_2(r), and k_i=v_2(r_i).
Every r_i divides r, since red_i(x)^r=red_i(x^r)=1. Thus k_i≤k.
If r is odd, each r_i is odd, every k_i is zero, and the failure event
“r is odd or x^(r/2)=z” is true.

Suppose r is even. For every i, the square of red_i(x^(r/2)) is one.
The positive-divisor lemma proved in `shor.v` gives

    red_i(x^(r/2))=1  iff  r_i divides r/2  iff  k_i<k.

By the local square-root classification and z_i≠1, the remaining case is
red_i(x^(r/2))=z_i exactly when k_i=k. At least one i has k_i=k: otherwise
all images of x^(r/2) would be one. Joint injectivity would give
x^(r/2)=1, contradicting its exact positive order r, since r/2<r.
Equivalently the same divisor lemma would require k<k.

If x^(r/2)=z, all component images are z_i, so every k_i=k. Conversely,
if all k_i are equal, the component attaining k shows that their common
value is k. Every component image of x^(r/2) is then z_i=red_i(z), and
joint injectivity yields x^(r/2)=z. Together with the odd-order case this
proves that failure is exactly equality of all local two-adic order values.

The conclusion is valid for arbitrary finite groups and homomorphisms
satisfying the stated structural hypotheses. It does not assume a product
decomposition, cyclic groups, a least-common-multiple order formula, or a
correct order-finding program. The CRT application supplies the structural
hypotheses and identifies z with the modular residue -1.

Checked in `ClassicalShorOrderEvent`: `component_order_dvd`,
`component_valuation_le`, `odd_component_valuation`,
`half_component_square`, `half_component_is_one`,
`half_component_is_involution`, and `component_valuation_reaches` prove
the individual steps. `failure_iff_equal_valuations` gives the exact Boolean
event equality, indexed against any chosen component i0. The module passes
direct compilation and mapped Dune compilation. An assumptions audit of
`failure_iff_equal_valuations`, `half_component_is_involution`, and
`component_valuation_reaches` reports `Closed under the global context` for
each theorem; the structural assumptions above remain explicit arguments.


<a id="shor-probability-notes"></a>

## SHOR PROBABILITY NOTES

### Numerical probability corollary of the unit count

This records the final finite-ratio step of classical.pdf Lemma 7.2(2),
PDF pp. 40–41, independently of the order-finding postprocessor.
For a nonempty finite type T, let b count a predicate Bad and let g count
its complement. Thus b+g=|T|. Suppose d>0 and d*b≤|T|. Division by the
positive numbers d and |T| gives b/|T|≤1/d. Since g/|T|=1−b/|T|,
the complementary probability is at least 1−1/d. Natural counts embed
order-preservingly into any numeric field, so the proof applies to the
project's real and complex scalar fields without an additional assumption.

For an odd N>1, use the actual finite group of units modulo N, whose
cardinality is the positive integer totient(N). Let Bad be the event that
the exact multiplicative order is odd or the half-order power is −1.
The previously proved concrete count bound has
 d=2^(size(primes N)−1), which is positive. Its complement is precisely the
favorable event “even exact order and half-order power different from −1.”
The ratio lemma therefore yields the claimed lower bound for uniform units.
The separate sampling bridge identifies this ratio with the conditional law
of the literal uniform random assignment, given coprimality.

For the scalar mixture step in Equation (21), assume lambda>=0 and
0<=p<=1, 0<=c<=1. Then p*c<=1, by multiplying the upper bounds through
nonnegative factors. The difference between
lambda+p*((1-lambda)*c) and p*c is lambda*(1-p*c), which is nonnegative.
Consequently the mixture is at least p*c. This is an algebraic implication;
it asserts no success probability for the paper's order-finding code.

The checked Rocq results in `shor.v`, module
`ClassicalShorProbability`, are `finite_complement_ratio`,
`uniform_unit_success_bound`, and `mixture_lower_bound`. The concrete
unit theorem takes exactly a numeric field F, N, `1 < N`, and `odd N`;
its lower bound is `1 - 1 / (2 ^ (size (primes N)).-1)%:R` and its
right side is `#|unit_success|%:R / (totient N)%:R`. In particular the
predecessor applies to the exponent, as in Lemma 7.2(2).

Focused compilation and Dune integration with Rocq 9.1 succeeded.
`Print Assumptions` reports `Closed under the global context` for all three
results. The literal-sampler
interpretation and the connection to the surrounding program are separate
results; the unit bound itself does not assume an order-finding contract.


<a id="shor-product-notes"></a>

## SHOR PRODUCT NOTES

### Finite product counting for Lemma 7.2(2)

This is the combinatorial step of [shor counting notes](PROOF_NOTES.md#shor-counting-notes). Let I be a
nonempty finite index set, X_i finite sets, and l_i : X_i -> K finite labels.
The sets X_i may be different and may be empty. Fix i0 in I. Let c_i(k)
count the elements with label k, and suppose 2 c_i(k) <= |X_i| for every
i other than i0. No restriction on the first coordinate is necessary.

Partition the functions f in the dependent product by their common label.
The constant-label fiber has cardinal product_i c_i(k), by finite function
family counting. Thus the number B of functions with all labels equal is
sum_k product_i c_i(k). For each summand, move the factor 2^(|I|-1)
into the product over i != i0. The coordinate inequalities give

    2^(|I|-1) product_i c_i(k)
      <= c_i0(k) product_(i != i0) |X_i|.

Summing over k and using sum_k c_i0(k)=|X_i0| proves

    2^(|I|-1) B <= product_i |X_i|.

This argument proves a general counting theorem. It does not assume CRT,
the distribution of modular orders, or the desired Shor success bound.
Those number-theory premises must be instantiated by their separate proofs.

Natural-number labels reduce to finite labels without a boundedness premise:
take K to be the ordinals below one plus max_i max_x l_i(x). Every label
belongs to this type by the two finite maximum inequalities, and ordinal
equality is exactly natural-number equality. This yields the same theorem
for logn 2 labels on finite groups.

The direct-compiled module `shor.v` proves
`product_half_bound`, `sum_product_half_bound`, `product_card`, `family_card`,
`label_count_sum`, `diagonal_card`, and `diagonal_half_bound`.
`natural_diagonal_half_bound` gives the natural-label variant, with the bound
constructed internally by `label_bound` and `label_bounded`. No boundedness
premise or axiom is added.


<a id="shor-sample-event-notes"></a>

## SHOR SAMPLE EVENT NOTES

### Natural arithmetic event for the uniform Shor sample

This bridge identifies the arithmetic event E(x) in classical.pdf,
Lemma 7.2(2), pp. 40–41, with the independently counted event on actual
finite modular-unit groups. It does not use an order-finding program or
assume its returned denominator is an exact multiplicative order.

For N>1 and every natural a, define a total unit-valued function: use the
residue of a in the unit group modulo N when gcd(a,N)=1, and use the
identity unit otherwise. The second branch only makes this function total;
the arithmetic order interpretation below is asserted under coprimality.
For every unit u, its canonical natural representative is coprime to N and
lies below N, so conversion of that representative returns u exactly.

Define the natural multiplicative order of a to be the finite-group order
of its converted unit. For coprime a, its k-th group power has canonical
representative a^k modulo N. The finite-group order divisibility theorem
therefore proves that this order divides k exactly when a^k is congruent
to one modulo N. In particular it is positive, its own power is one, and
no smaller positive exponent has that property. These are the exact order
conditions in the paper, proved for the concrete modular residue.

Define natural_success(a) as: this exact order is even and the residue of
a to half that order is not N−1 modulo N. For a canonical unit
representative, the converted unit is the original unit and the natural
order is its group order. The group element −1 has canonical representative
N−1, so equality of the half powers to −1 is equivalent to equality of
the corresponding natural residues. Thus natural_success on canonical
representatives is exactly the counted unit_success predicate. Conditioning
the actual uniform sample on coprimality can therefore use the established
uniform-unit bijection without changing the paper's arithmetic event.

For Equation (20), let r be this exact order and assume natural_success(a)
and coprimality. Then r is positive and even. Put h=r/2 and s=a^h. Since
r=2h, s² is congruent to one. Positivity of r gives 0<h<r, so exact-order
minimality excludes residue one for s. Coprimality of a and N is preserved
by powers, which excludes residue zero (as N>1). Hence the canonical
residue of s is greater than one. Success excludes residue N−1, and every
canonical residue is below N, so this residue plus one is strictly below N.
The already checked `nontrivial_sqrt_factor_mod` now proves that
gcd(s−1,N) is a nontrivial factor. Thus the arithmetic extraction step is
checked independently of whether any order-finding program returns r.

Checked in `shor.v`: `natural_unitK`,
`natural_power_value`, `natural_order_dvd`, `natural_order_positive`,
`natural_order_power`, `natural_order_minimal`, and `natural_success_unit`.
The total definitions `natural_unit N a`, `natural_order N a`, and
`natural_success N a` do not require a proof argument; their arithmetic
interpretation theorems explicitly require N>1 and, where needed,
coprimality. All four central audited theorems are closed under the global
context. Equation (20) is checked independently in
`ClassicalShorFactorExtraction.natural_success_factor` in
`shor.v`.


<a id="shor-sampling-notes"></a>

## SHOR SAMPLING NOTES

### The source sampler and Equation (21)

Source: `classical.pdf`, Section 7.5, Equation (21), PDF p. 41, and the
literal uniform assignment in Table 6. This argument concerns that actual
sampler and the arithmetic exact-order event. It does not assume or assert
correctness of the order-finding postprocessor.

Fix N>1. The sampler has one outcome a=i+1 for each ordinal i<N-1, each
of mass 1/(N-1). For each such positive a, gcd(a,N)>0. Hence precisely
one of gcd(a,N)>1 and gcd(a,N)=1 holds. Coprimality is the latter equality,
with the gcd arguments interchanged. Summing the two complementary indicator
functions against the common mass gives

    direct_probability + coprime_event_probability(True) = 1.

Write lambda for the first term and q for the coprime probability. Thus
q=1-lambda, lambda>=0, and q>0. For odd N the previously checked conditional
bound gives c<=r/q, where c=1-1/2^(size(primes N)-1) and r is the source
probability of coprimality together with the favorable exact-order event.
Multiplication by q>0 gives q*c<=r. The positive integer denominator in c
is at least one, so 0<=c<=1. For any scalar p with 0<=p<=1, multiplication
by p preserves q*c<=r. Adding lambda and applying the already proved
`mixture_lower_bound` gives

    p*c <= lambda+p*((1-lambda)*c) = lambda+p*(q*c) <= lambda+p*r.

Every probability in this statement comes from the printed sampler's finite
sum. The arbitrary scalar p is an algebraic input, not a claimed verified
success probability for the surrounding order-finding program.

The checked module `ClassicalShorSampling` in `shor.v` proves
`gcd_guard_complement`, `sampling_partition`,
`coprime_probability_complement`, and `sampling_mixture_bound`.
Focused Rocq 9.1 compilation and Dune integration succeeded. The assumptions
audit of the partition, complement identity, and mixture bound reports only
the project's inherited real/classical foundations (Dedekind-real decisions,
extensionality, and choice). It reports no new axiom and no order-finding
success assumption. The final theorem takes N>1,
the actual classical input store, `odd N`, and `0 <= p <= 1`; all event
probabilities are the source definitions from `shor.v` and
`shor.v`.


<a id="shor-uniform-notes"></a>

## SHOR UNIFORM NOTES

### The conditional law of the printed Random command

For N>1, `ClassicalShorProgram.uniform_probability` samples each integer
1,...,N-1 with probability 1/(N-1). The underlying finite sampling index is
an ordinal i<N-1, whose sampled value is i+1.

Every modular unit has a unique canonical representative a<N. Coprimality
and N>1 imply a>0, so a-1 is a sampling index. Conversely, every sampling
index whose value is coprime to N gives a unit via the natural-number map
into Z_N. The two constructions are inverse on these domains. Thus, for
any predicate P on sampled natural numbers, reindexing the finite sum gives

    sum_(i<N-1, coprime(N,i+1) and P(i+1)) mass(i+1)
      = #{u : units modulo N | P(representative(u))} / (N-1).

With P=true, this is the probability of the conditioning event. It is
positive because the unit one exists. Dividing the event probability by
this conditioning probability cancels 1/(N-1), leaving the cardinality
ratio for the uniform unit group. Therefore the pure modular-unit count
theorem applies to the conditional law of the actual printed Random
command. This argument neither assumes a quantum order-finding outcome
distribution nor repairs its printed postprocessor.

The finite sum uses the actual `probability_mass uniform_probability` from
the language's Random source. Its exact mass formula has already been
proved. `shor.v` formalizes the bijection, reindexing, positivity,
and conditional ratio.

The checked names in `ClassicalShorUniform` are `sampled_unitK`,
`sample_indexK`, `sample_unit_reindex`, `coprime_event_probabilityE`,
`conditioning_probability_positive`, and `conditional_probabilityE`.
Finally, `random_conditional_success_bound` instantiates the concrete
modular-unit bound and the exact-order natural event from
`ClassicalShorSampleEvent`. Its only arithmetic assumptions are N>1 and
odd N; the initial classical store is arbitrary. The event is exactly
even multiplicative order and modular half power different from N-1.
Direct compilation passes; integration and assumption audits are recorded
in the validation record.


<a id="state-notes"></a>

## STATE NOTES

### Classical-quantum states

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

#### Missing step in Lemma 3.3

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
counterexample recorded in [proof gaps](PROOF_NOTES.md#proof-gaps).

#### Missing summability step in Lemma 4.4

A program kernel `K(i,j)` is completely positive, and for any finite set
`B` of outputs the map `sum_(j in B) K(i,j)` is trace nonincreasing. For
positive input components `d(i)`, positivity and trace-norm additivity give
`sum_(j in B) ||K(i,j)(d(i))|| <= tr(d(i))`. Summing over any finite input
set bounds every finite rectangular double sum by `tr(d)`. Absolute
summability therefore permits changing the order of sums. In particular
`out(j) = sum_i K(i,j)(d(i))` is absolutely summable and positive, and its
total trace is at most `tr(d) <= 1`. This argument applies to every cq-state,
including ones with infinite support; no finite-support approximation is
used as the final semantics. It is implemented in `semantics.v`.

The same finite-sum estimate for a single instrument requires only positivity
of its input operator, not the unit trace bound. `semantics.v` exposes
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

#### Mixtures for distributed computations

For nonnegative weights with total at most one and cq-states `d_i`, regard
`w_i d_i` as elements of the complete space of summable operator families.
Their norms are at most `w_i`, since the norm of a positive cq-state is its
total trace. Thus the outer family is summable. Its sum is positive
pointwise (closedness of the positive cone), and has norm and total trace
at most one. Continuity of point evaluation gives
`mix(j) = sum_i w_i d_i(j)`. This proves validity of mixtures over arbitrary
choice-type index sets; absolute summability supplies countable support.
Formal names: `CQStateMixture.terms_summable`, `mix_positive`,
`mix_l1_bound`, `mix`, and `mixE` in `state.v`.

For any effect assertion, its trace pairing extends to the complete space of
summable operator families as a linear map of norm at most one. Consequently
it commutes with the absolutely convergent outer sum defining a mixture.
This proves that the expectation of a mixture is the weighted sum of the
component expectations, without a finite-support restriction. The checked
theorems are `CQMixtureExpectation.pairing_linear` and `expect_mix` in
`assertion.v`.

#### Passing kernel limits through arbitrary input states

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
`unroll_apply_cvg`, and `unroll_expect_cvg` in `semantics.v`.

#### State separation, decreasing limits, and kernel linearity

Classical Lemma 3.10(1), and distributed Appendix B.2(1), also characterize
state order through expectations. In the approved full effect domain, test
the inequality against an effect concentrated at one classical store. The
result is the inequality of all density/effect trace pairings at that store,
which characterizes operator order. Equality of all such expectations gives
state equality. This argument concerns all semantic effects; restricting
the separating tests to the paper's definable-fiber subclass would additionally
require its finite-formula approximation argument.

Checked in `assertion.v` as `CQStateExpectation.at_store`,
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

Checked in `state.v` as `CQStateDecreasing.decreasing_converges`,
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

Checked in `semantics.v` as `CQKernelLinearity.weighted_norm_bound`,
`weighted_output_summable`, `apply_weighted_sum`, and `apply_mix`. The general
series theorem assumes explicitly that the input sum is a cq-state; a signed
combination need not itself be positive or have mass at most one.

For distributed Lemma 3.11(2), `DistributedHoare.run_translate` identifies
the actual operational run on every cq-input with the kernel of the
successful serialized command. Substitute this identity for each input and
for their sum in the preceding kernel theorem. The output summability bound
and the full signed-series equality therefore hold for actual distributed
runs; no choice of scheduler or finiteness of the input support is added.

Checked in `../distributive/sequentialization.v` as
`DistributedLinearity.run_weighted_summable`, `run_weighted_sum`, and
`run_mix`.


