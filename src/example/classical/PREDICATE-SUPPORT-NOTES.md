# Quantum support of predicate transformers (Lemma 4.14(1), p. 22)

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
