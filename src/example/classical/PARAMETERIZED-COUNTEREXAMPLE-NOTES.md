# Parameterized-unitary liberal-precondition counterexample

Source: classical.pdf, p. 23, Lemma 4.15(3); diagnosis C4 in
PROOF_GAPS.md. This records a counterexample to the printed equality,
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

Checked in `parameterized_counterexample.v`, module
`CQParameterizedCounterexample`: `parameterized_zero_partial` proves the
identity liberal precondition; `parameterized_zero_printed` proves the
printed precondition is zero; `parameterized_zero_counterexample` proves
their inequality at every store. The existing `selector_pre_sum` and
`parameterized_wp` identify that precondition with the paper's guarded sum.
Direct compilation, qualified Dune integration, and the assumptions audit
passed. Only inherited classical foundations and the existing `qreg.G`
memory parameter occur.
