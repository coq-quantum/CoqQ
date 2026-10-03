# Lemma C.9: raw sequentialization and its deadlock postcondition

Source: `distributive.pdf`, Lemma C.9 and Equation (12), PDF p. 35.
The established operational correspondence uses `successful_sequentialize`,
which executes the raw serialization T(S) and then tests TERM, aborting
otherwise. This note records the additional argument for the paper's exact
raw-serialization Hoare statements.

For any loop, two postconditions that agree wherever its guard is false have
the same weakest and weakest liberal preconditions. Indeed, induction on
finite unrollings proves this: the zero unrolling aborts, and at a successor
the true branch uses the induction hypothesis while the false branch returns
the supplied postcondition. The checked wp and wlp convergence of unrollings,
and uniqueness of their pointwise operator limits, give the unbounded-loop
claim. No termination or finite runtime bound is assumed.

For total correctness the final TERM test transforms TERM-and-Q into itself.
Thus the existing operational correspondence gives

    valid_total(P,S,TERM-and-Q) iff valid_total(P,T(S),TERM-and-Q).

For partial correctness the final test transforms TERM-and-Q into the
postcondition that equals Q on TERM and top elsewhere. The raw serialization
ends in the rendezvous loop, whose exit guard is BLOCK. On BLOCK this
postcondition agrees with

    (TERM and Q) + (not TERM and BLOCK),

where classical predicates denote zero/identity effects. The two summands
have disjoint classical supports, so the expression is a valid effect.
The loop postcondition-agreement result permits this replacement inside the
raw serialization, including its preceding initialization. Applying the
existing weakest-liberal-precondition characterization of validity proves
the partial equivalence in Lemma C.9.

The formal postcondition uses a pointwise conditional to package the bounded
effect, and a separate operator equality gives the exact printed disjoint
sum. The actual network execution and both serializers retain their existing
definitions.

The checked module `DistributedSerialHoare` in `serial_hoare.v` proves
`pre_unroll_post_agree` and `pre_while_post_agree`, the exact disjoint-sum
identity `partial_serial_postE`, and the two named C.9 results
`total_raw_sequentialization_iff` and `partial_raw_sequentialization_iff`.
Focused Rocq 9.1 compilation and Dune integration succeeded. The four-result
assumptions audit reports only inherited real/classical foundations and the
existing `qreg.G` memory parameter. The equivalences quantify over
arbitrary cq assertions and every well-formed distributed `program`; their
left side uses the existing independent distributed execution semantics.
