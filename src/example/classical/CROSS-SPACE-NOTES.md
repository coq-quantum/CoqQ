# Assertion-space-changing SupOper (Table 5, pp. 31–33)

The paper allows a completely positive subunital F from operators on V to
operators on W. The precondition and postcondition need contain V, and their
remaining quantum supports must be disjoint from W. Both V and W must be
disjoint from the program footprint. They need not have the same dimension
and may overlap each other. All supports below are subsets of the arbitrary
finite ambient memory chosen by the shared language.

We implement the rectangular map with the following square extension on
U = V union W. Let A = U minus V and B = U minus W. The rectangular
depolarizer D from A to B is D(X) = tr(X) I_B / dim(A). It is completely
positive, with Kraus operators |j>_B <i|_A / sqrt(dim(A)), and D(I_A)=I_B.
Thus F tensor D, after identifying V union A and W union B with U, is
completely positive and subunital. Its ambient lift acts only on U, so the
already checked square SupOper rule applies in both correctness modes.

On a cylindrically lifted X on V, the extension sends X tensor I_A to
F(X) tensor I_B. It therefore sends the ambient cylinder of X to that of
F(X). If R is disjoint from V and W, the extension also commutes with
operators on R, and consequently sends the cylinder of X tensor Y to the
cylinder of F(X) tensor Y. Expand an arbitrary operator on V union R in
delta matrix units, split each matrix unit over V and R, and use linearity.
This proves the same equation for arbitrary operators, including entangled
effects: the result is exactly the cylinder of (F tensor Id_R)(A).

Every paper assertion support Z with V subset Z and W intersect Z subset V
has this decomposition with R = Z minus V. The precondition and
postcondition may use different remainder supports. The formal rule takes
these disjoint decompositions explicitly; they impose precisely the paper's
support conditions, without a separability assumption. The transformed
assertions are packed effects because the tensor map is completely positive
and subunital. No external register beyond the chosen ambient memory is
created, and no modification of the program semantics is required.

Checked in `quantum_cross_space.v`, module `CQQuantumCrossSpace`:

- `rectangular_depolarizerE`, `rectangular_depolarizer_cp`,
  `rectangular_depolarizer1`, and `rectangular_depolarizer_dqo` prove the
  explicit rectangular map and its complete positivity/unitality bounds.
- `square_extension_lift` and `square_extension_cylinder` prove its action
  on an arbitrary local operator.
- `cylinder_tensor_action` proves the general matrix-unit extension;
  `square_extension_tensor` instantiates it for the constructed map.
- `cross_assertion` constructs the transformed effect assertion and
  `cross_assertionE` exhibits its literal rectangular-tensor formula.
- `image_square_extension` identifies that assertion with the square
  ambient action; `derives_supoper_cross` gives the Table-5 inference in
  both correctness modes, with separate remainder supports at its input
  and output. It has only the paper's derivability and support premises.

The mapped assumption audit of the rectangular depolarizer bound, arbitrary
tensor-action theorem, and final derivation reports only inherited classical
real-model, choice and extensionality foundations and the existing `qreg.G`
memory parameter. There is no new axiom or admitted proof.
