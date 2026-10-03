# Modular-orbit Fourier eigenstates (classical.pdf p. 39)

The paper's exact spectral identities are independent of its false printed
continued-fraction success assertion. Let r be the exact multiplicative
order of x modulo N, with N>1, gcd(x,N)=1, and N≤2^L. The r orbit vectors
|x^j mod N⟩, 0≤j<r, are distinct: equality of two orbit residues is equality
of powers of the concrete finite modular unit, and exponents below its
order are injective. Their computational basis vectors are therefore
orthonormal. Sending |j⟩ in the r-dimensional auxiliary space to the j-th
orbit vector defines an isometry E. The actual modular unitary satisfies
U E|j⟩=E|j+1 modulo r⟩.

Use the complex conjugates of the existing arbitrary-size QFT basis in the
auxiliary space, so its s-th vector has coefficients

  r^(−1/2) exp(−2π i s j/r).

Applying E gives precisely the printed orbit Fourier vector u_s. Complex
conjugation preserves orthonormality, and E preserves inner products, so
the u_s are orthonormal and normalized. Shifting the orbit sum forward by
one replaces its coefficient at j+1 by the coefficient at j. The identity
exp(−2π i s(j+1)/r) exp(2π i s/r)=exp(−2π i s j/r), including the wrap at
r, follows from periodicity of the r-th root of unity. Reindexing the finite
sum therefore proves U u_s=exp(2π i s/r)u_s.

Finally, the uniform normalized sum over all Fourier labels is the zero
computational basis vector: the sum of r-th roots of unity is r at j=0
and zero otherwise. Applying E sends this vector to |x^0 mod N⟩=|1⟩.
Thus r^(−1/2)Σ_s u_s=|1⟩. The sum is finite and all normalizing factors are
legitimate because the concrete finite-group order r is positive. The
auxiliary index is implemented as r.-1.+1, proved equal to r, to expose the
existing inhabited positive-dimensional QFT API without imposing a new
mathematical restriction.

The generic finite Fourier facts are checked in `order_finding_eigenstates.v`
as `ClassicalOrderFindingEigenstates.inverse_fourier_basis_dot`,
`inverse_fourier_basisE`, `inverse_fourier_sum`, `eigenstate_eigenvalue`,
and `eigenstate_sum`. The generic cyclic-action premise is discharged by
the actual modular orbit theorem in the concrete instantiation; it is not
left as an assumption of the modular results.

The concrete checked names are `modular_eigenstateE` (the displayed Fourier
sum), `modular_eigenstate_dot`, `modular_eigenstate_normal`,
`modular_eigenvalue` (the actual modular unitary action),
`modular_eigenstate_sum` (basis one), and `modular_eigenstate_one` (the
exact `ClassicalOrderFinding.one_state` used by the printed source).
`ClassicalOrderFindingOrbit.orbit_lengthE` identifies the positive index
length in these statements with the exact `natural_order N x`. This also
covers order one: there is one normalized eigenvector, eigenvalue one, and
the uniform decomposition contains that single vector.
