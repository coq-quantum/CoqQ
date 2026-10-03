# Exact modular orbit for the order-finding eigenstates

Source: classical.pdf, Section 7.4, PDF p. 39. The eigenvectors displayed
there use the orbit |x^k mod N> for 0<=k<r, where r is the exact order.
This note supplies that orbit as an actual orthonormal family in the
target register; the subsequent Fourier construction is independent of
the false continued-fraction selector claim C7.

Assume N>1, gcd(x,N)=1, and N<=2^L. Let u be the actual unit represented
by x modulo N and r=ord(u), using `natural_order`. The exact-order
properties have already been proved against ordinary modular arithmetic.
In particular r>0. Use the manifestly positive length (r-1)+1 for the
ordinal index type; positivity proves that this length equals r, including
the boundary r=1.

If x^i and x^j have the same residue, the corresponding unit powers u^i
and u^j are equal. Exact order implies i=j modulo r; since both indices
are below r, they are equal. Thus the residue-to-bit-tuple conversion is
injective on the orbit indices. Computational basis orthogonality gives
an orthonormal family of actual register vectors b_i=|x^i mod N>.

Define the linear embedding J from the r-dimensional coordinate Hilbert
space into the target register by J=sum_i |b_i><i|. Orthonormality gives
J^*J=I, so it is an isometry, preserves all inner products, and sends the
ith computational basis vector to b_i. No abstract orbit or assumed
spectral basis is introduced.

The already constructed modular unitary U sends |a mod N> to |xa mod N>.
Consequently U b_i=b_(i+1 mod r), because u^r=1. In particular, the orbit
of index zero is the actual computational vector |1>. These identities
hold when r=1: the cyclic successor is the sole index and U fixes |1>.
Fourier-transforming this concrete cyclic shift supplies the eigenstates
on paper p. 39 without relying on a quantum success probability.

The implementation is `order_finding_orbit.v`, module
`ClassicalOrderFindingOrbit`. `orbit_lengthE` identifies the positive
index length with the exact order. `orbit_bits_value` and
`orbit_bits_injective` identify and separate the actual residues.
`orbit_basis_dot` registers the computational vectors as a partial
orthonormal basis. `orbit_embedding_basis`, `orbit_embedding_isometry`,
and `orbit_embedding_dot` give the linear isometry and its action.
`orbit_power_period` proves the arithmetic period reduction;
`modular_orbit_basis` proves the actual modular unitary acts by the
cyclic successor `ordS`; `orbit_basis_zero` identifies the initial vector.
`orbit_isometry` supplies the explicit packed isometry used by the spectral
construction; `orbit_isometryE` identifies its underlying linear map.
The module passes direct and mapped compilation. The arithmetic orbit
injectivity is closed under the global context. The isometry, inner-product,
and modular-action audits use only the inherited real/choice/extensionality
foundations, with no quantum-memory parameter and no new axiom.
