# Checked ordinary-distance counterexample for phase estimation

Source: classical.pdf, Section 7.3, PDF pp. 36–38, Equation (13), Equation
(16), and Lemma 7.1; see diagnosis C6 in PROOF_GAPS.md. This checks the
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

The implementation is `phase_counterexample.v`, module
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
in `PHASE-PROBABILITY-NOTES.md`. No probability, cosine estimate, or
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
