# Transport between finite quantum memories

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

The checked generic algebra is in `memory_transport.v`, module
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
These helper results are checked in `memory_instruments.v`, module
`CQMemoryInstruments`: `liftso_summable_reflect`, `liftso_sum`, their
`liftfso` specializations, and `liftfso_sum_cptn_reflect`. Direct and
qualified builds and all three assumption audits passed, with inherited
classical foundations only and no `qreg.G` dependency.

Direct and qualified Dune compilation passed. The eight-result assumptions
audit reports only inherited classical real/choice/extensionality
foundations, with no `qreg.G` or new correctness axiom. The typed primitive
interpretation is documented separately in `MEMORY-INTERPRETATION-NOTES.md`.
