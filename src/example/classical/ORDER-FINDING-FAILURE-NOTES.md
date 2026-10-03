# Impossible outputs of the printed order-finding command

Source: classical.pdf, Section 7.4, pp. 38–40, the final assignment in
`OF(x,N)` and Equation (18). This is a consequence of the literal printed
minimum-denominator selector, whose counterexample and finite-list argument
are recorded as C7 in `PROOF_GAPS.md`.

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
