# Primitive frame rules (Table 5, p. 31)

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

The checked implementation is `primitive_frame.v`, module
`CQPrimitiveFrame`: `initial_pre_frame` and `unitary_pre_frame` give the
invariance equations; `derives_initialize_frame`, `derives_init0`, and
`derives_unit0` give the corresponding core-calculus derivations.
`measurement_pre_frame` gives the explicit tensor sum,
`measurement_tensor_effect` proves its effect bound, and `derives_meas0`
derives the measurement rule for the constructed assertion in both modes.

The mapped assumption audit of all three Table-5 derivation theorems reports
only inherited classical real, choice and extensionality foundations and
the existing ambient-memory parameter `qreg.G`.
