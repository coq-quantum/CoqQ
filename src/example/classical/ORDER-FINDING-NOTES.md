# Printed order-finding and Shor programs

Source: classical.pdf, Section 7.4, PDF pages 38–40, Equation (17), and
Section 7.5/Table 6, PDF pages 40–41. The rendered pages were inspected.
This work preserves the printed continued-fraction selector from
`ClassicalShorArithmetic.printed_postprocess`; it does not assert the false
success claim identified in C7 or introduce a corrected selector.

## Modular multiplication is unitary

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

Checked in `modular_unitary.v` as
`ClassicalModularUnitary.modular_value_inj`, `modular_bits_inj`,
`modular_unitary`, `modular_unitaryE`, and `modular_unitary_outside`.
`modular_power_residue` proves that the k-th power sends the basis vector
for a modulo N to the basis vector for x^k a modulo N.

## Source program and its boundary

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
`order_finding.v`. `total_modular_unitaryE` identifies the selected operation
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

Checked pure-state formulas are in `order_finding_state.v`:
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

The bridge is checked in `order_finding_execution.v` as
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
`order_finding_orbit.v` and `order_finding_eigenstates.v`. The exact-order
orbit is isometric to its computational basis; its Fourier sums are
orthonormal eigenstates of the actual modular unitary, and their
normalized sum equals the actual target `one_state`. See
`ORDER-FINDING-EIGENSTATES-NOTES.md` for the complete argument and names.
