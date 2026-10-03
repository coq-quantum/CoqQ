# Auxiliary quantum-space rules (Table 5, p. 31)

These rules operate in the fixed ambient quantum memory of the shared
language. A local assertion on S is represented by its cylindrical lift,
which tensors it with the identity on the remaining memory. All register
side conditions below are finite-set disjointness conditions on actual
quantum footprints.

For Tens, let M be an effect on an unused register T. Positivity gives
M = B B*, so F(A) = B A B* is completely positive and F(I) = M <= I.
Because an assertion on disjoint S acts trivially on T, applying the local
extension of F to its cylindrical lift gives the lift of its tensor product
with M. The checked SupOper rule therefore proves Tens in both total and
partial correctness. The arbitrary output assertion parameters in the rule
are accompanied only by equalities to these explicit tensor expressions;
they package the existing effect type and are not correctness premises.

For a finite orthonormal family v_i on an unused register, the map
F(A) = sum_i lambda_i <v_i,A v_i> I is completely positive: each summand is
the dual of the state-preparation map for v_i, multiplied by a nonnegative
weight. If sum_i lambda_i <= 1, F(I) <= I. Acting on the labeled block
sum_i P_i tensor |v_i><v_i| removes the label and leaves sum_i lambda_i P_i.
This gives L-Sum in both correctness modes. The same selector with a complete
orthonormal basis and uniform weights gives normalized partial trace.

For Trace, use the selector on the complete delta basis of the traced
register T, with weight 1/dim(T) on each vector. Its local action on any
operator A is tr(A) I/dim(T); positivity and unitality make it a dual quantum
operation. To identify its full-memory lift, expand an arbitrary operator
in delta matrix units. Split each index into the part on T and the part
on its complement. The lifted selector sends a matrix unit to zero unless
its two T indices agree; when they agree it sends it to I_T/dim(T) tensored
with the remaining matrix unit. The defining basis sum of partial trace
has exactly the same two cases. Finite linearity therefore identifies the
lift with the cylindrical lift of partial trace divided by dim(T), including
off-diagonal matrix units. SupOper then gives Trace in both correctness
modes whenever T is disjoint from the program's quantum footprint.

The Trace argument is checked in `CQQuantumTrace.partial_trace_outp`,
`lift_depolarizer`, and `trace_assertionE`. The corresponding inference rule
is `derives_trace`, in both total and partial correctness.

SupPos instead selects the unit vector sum_i conjugate(alpha_i) v_i.
On the entangled input (1/sqrt(d)) sum_i phi_i tensor v_i, contraction yields
(1/sqrt(d)) sum_i alpha_i phi_i, and likewise at the output. Thus SupOper
produces both target predicates scaled by 1/d. In total correctness this
positive scalar cancels from the expectation inequality. It cannot generally
cancel from the additive nontermination allowance for partial correctness;
accordingly Theorem 6.1 explicitly excludes partial SupPos.

Checked implementations:

- `CQQuantumSpaceRules.effect_map_exists`, `tensor_effect`, and
  `derives_tens_direct` construct the tensor assertions and derive Tens.
- `CQQuantumSelector.selector_dqo`, `selector_outp`, `selector_labeled`, and
  `derives_lsum` prove the explicit weighted label-removal rule.
- `CQQuantumSuperposition.selecting_overlap`, `selecting_norm`,
  `selected_entangled`, and `derives_suppos` prove total SupPos. The rule
  permits any positive common input-projector scale r; the paper uses
  r = 1/d. Orthogonality of the data families is sufficient to make the
  displayed expressions effects, but the contraction proof itself only
  needs orthogonality of the label family and normalized coefficients.

L-Sum and SupPos take existing effect assertions together with exact
equalities to their displayed operator formulas. These equalities express
assertion construction, not an assumed channel property or desired Hoare
inequality. Their only derivability premise is the corresponding paper
premise; all needed transformations are proved explicitly.

The mapped assumption audit of all three final rule theorems reports only
the inherited classical real-model, choice and extensionality foundations
and the existing `qreg.G` quantum-memory parameter. No new axiom, admission,
or dependent-equality assumption occurs in these proofs.
