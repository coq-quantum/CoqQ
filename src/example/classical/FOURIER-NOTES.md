# Fourier circuit argument

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

The tensor calculation is checked in `fourier.v` through
`single_hadamard_product`, `controlled_phase_product`,
`phase_chain_product`, `bitstr2rat_drop_sum`, and `stage_phase_layer`.
`circuit_prefix_basis` proves the outer circuit invariant;
`fourier_circuit_basis` and `fourier_circuit_correct` prove equality with
the Fourier transform on basis states and as a complete linear operator.
`fourier_program.v` supplies that connection. `fourier_inner_execution` and
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

`indexed_loops.v` supplies the shared `indexed_loop_execution` and
`indexed_loop_denote` lemmas. The induction is on the number of remaining
counter increments. At each step, a concrete body execution certificate
supplies its resulting store and superoperator, and a separate elementary
store equation supplies the increment. The zero case has a false guard.
`execution_denote` then identifies the full unbounded-while denotation with
this finite terminating execution. The body may depend on the store and
change additional variables, as the inner counter of the Fourier program
does; no bounded-time or termination premise is assumed about the whole loop.
