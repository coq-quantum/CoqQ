# Classical algorithm case studies

## Grover search (Section 7.1, Examples 4.5 and 4.11)

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
is sin²((2K+1)theta). `grover.v` checks this concrete matrix argument;
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
`grover_correctness.v`: `grover_prefix_execution` and `grover_prefix_denote`
identify the complete prefix, `measurement_success_pre` identifies the
measurement transformer, `grover_success_pre` proves the exact scalar
precondition, and `grover_correct` derives the resulting total or partial
Hoare judgment in the independent inference system `CQRules.derives`.
The general supporting deterministic weakest-precondition and channel
composition lemmas are in `algorithm_semantics.v`.

For qubit tuples, the uniform preparation agrees on the initialized zero state
with the paper's sequence of Hadamards. No equivalence of those two unitaries
on arbitrary inputs is needed or asserted.

## Remaining Section 7 examples

The QFT circuit and its actual nested-loop program are checked in `fourier.v`
and `fourier_program.v`; see `FOURIER-NOTES.md`. Phase estimation has checked
loop execution, exact outcome probabilities, and derived total/partial
Hoare judgments in `phase_correctness.v`. The literal order-finding program has a checked exact Fourier/Born
outcome formula for its actual measured output, including its final
postprocessing assignment; see `ORDER-FINDING-NOTES.md`. Shor has checked
partial factor safety and an independent total lower bound from its
immediate gcd branch. The printed phase and order-finding success claims
are false; the larger Shor bound remains unproved. The concrete theorem
`ClassicalPhaseCounterexample.printed_phase_bound_counterexample` checks the
phase claim's failure at phase 1−1/1024 with three measured qubits; see
`PHASE-COUNTEREXAMPLE-NOTES.md`. The phase-estimation ordinary-distance error claim requires the
correction described in `PROOF_GAPS.md`, C6, and the printed order-finding
postprocessor has the counterexample C7. No corrected claim is silently
assumed here.

## Phase estimation: exact spectral identities (Section 7.3)

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
`phase_kickback` in `phase_estimation.v`. The actual nested program is checked
in `phase_program.v`: it retains the paper's one-based outer counter,
inner bound 2^(t-x), repeated controlled-U, initialization/preparation, inverse
Fourier gate, and finite control-register measurement. Dynamic indices are
explicitly guarded and abort outside their valid range. Its loop channels are connected gate by gate in `phase_stages.v` and
`phase_correctness.v`.

## Shor arithmetic: nontrivial square roots (Lemma 7.2(1))

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
and `phase_vector_product` in `phase_tensor.v`.

At stage i of phase estimation, the first i control factors carry their
phases and all later factors are zero. The Hadamard on i produces phstate(0).
Applying controlled-U exactly 2^(n-i-1) times multiplies its one-component
by exp(2 pi i 2^(n-i-1) phi), because the target is an eigenvector, and leaves
the target unchanged. The resulting product is the next invariant layer.
Induction on the sequence of stages, followed by the product identity above,
yields phase_vector tensor u. This is the natural-language argument for
`phase_stages.v`. The checked lemmas are `estimation_stageE`,
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
`phase_correctness.v`. The checked names are `phase_prefix_actionE`,
`phase_reset_execution`, `phase_outcome_pre`, `phase_outcome_formula`,
`phase_estimation_correct`, `phase_exact_pre`, and `phase_exact_correct`.
These cover the actual program and its exact distribution for both total and
partial correctness, without the disputed concentration claim C6.

## Phase amplitudes away from an exact grid point

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


Checked in `phase_bounds.v`: `ClassicalPhaseBounds.amplitude_ordinal`,
`amplitude_geometric`, `amplitude_bound`, and `probability_bound`. Squaring
the nonnegative amplitude bound yields the corresponding Born-probability
bound. The original norm estimate uses the exact finite geometric sum, not
a finite approximation to any program loop.

## Literal Shor wrapper and partial factor-output safety (Table 6, page 41)

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


The checked source is `ClassicalShorProgram.shor` in `shor_program.v`,
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
`ORDER-FINDING-FAILURE-NOTES.md`. The separate valid modular-unit counting
lemma is now checked, including its conditional-probability statement for
the actual uniform sampler; see `SHOR-COUNTING-NOTES.md` and
`SHOR-UNIFORM-NOTES.md`. Exact-order factor extraction in Equation (20)
and the distinct-prime consequence of cmp(N) are also checked.

`ClassicalShorSampling.sampling_partition` identifies the actual gcd and
coprime branch masses as complementary probabilities. Its
`sampling_mixture_bound` proves Equation (21) for every scalar p in [0,1],
using the checked conditional bound and exact-order event. This is the
sampler's probability calculation; a verified success guarantee for the
order-finding subroutine is still needed to apply it to a repaired complete
Shor algorithm. See `SHOR-SAMPLING-NOTES.md`.

The independent spectral derivation on page 39 is also checked. The modular
orbit has exactly the multiplicative order's number of distinct basis
vectors and yields an isometric embedding. Applying that embedding to the
conjugate Fourier basis gives the printed normalized orbit sums. Their
inner products are Kronecker deltas, the actual modular multiplication
unitary has the printed phase eigenvalues, and the normalized sum over all
eigenstates is the actual initialized basis-one state. The construction
also covers order one. See `ORDER-FINDING-ORBIT-NOTES.md` and
`ORDER-FINDING-EIGENSTATES-NOTES.md` for the proof and checked names.
