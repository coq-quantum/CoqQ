# Natural arithmetic event for the uniform Shor sample

This bridge identifies the arithmetic event E(x) in classical.pdf,
Lemma 7.2(2), pp. 40–41, with the independently counted event on actual
finite modular-unit groups. It does not use an order-finding program or
assume its returned denominator is an exact multiplicative order.

For N>1 and every natural a, define a total unit-valued function: use the
residue of a in the unit group modulo N when gcd(a,N)=1, and use the
identity unit otherwise. The second branch only makes this function total;
the arithmetic order interpretation below is asserted under coprimality.
For every unit u, its canonical natural representative is coprime to N and
lies below N, so conversion of that representative returns u exactly.

Define the natural multiplicative order of a to be the finite-group order
of its converted unit. For coprime a, its k-th group power has canonical
representative a^k modulo N. The finite-group order divisibility theorem
therefore proves that this order divides k exactly when a^k is congruent
to one modulo N. In particular it is positive, its own power is one, and
no smaller positive exponent has that property. These are the exact order
conditions in the paper, proved for the concrete modular residue.

Define natural_success(a) as: this exact order is even and the residue of
a to half that order is not N−1 modulo N. For a canonical unit
representative, the converted unit is the original unit and the natural
order is its group order. The group element −1 has canonical representative
N−1, so equality of the half powers to −1 is equivalent to equality of
the corresponding natural residues. Thus natural_success on canonical
representatives is exactly the counted unit_success predicate. Conditioning
the actual uniform sample on coprimality can therefore use the established
uniform-unit bijection without changing the paper's arithmetic event.

For Equation (20), let r be this exact order and assume natural_success(a)
and coprimality. Then r is positive and even. Put h=r/2 and s=a^h. Since
r=2h, s² is congruent to one. Positivity of r gives 0<h<r, so exact-order
minimality excludes residue one for s. Coprimality of a and N is preserved
by powers, which excludes residue zero (as N>1). Hence the canonical
residue of s is greater than one. Success excludes residue N−1, and every
canonical residue is below N, so this residue plus one is strictly below N.
The already checked `nontrivial_sqrt_factor_mod` now proves that
gcd(s−1,N) is a nontrivial factor. Thus the arithmetic extraction step is
checked independently of whether any order-finding program returns r.

Checked in `shor_sample_event.v`: `natural_unitK`,
`natural_power_value`, `natural_order_dvd`, `natural_order_positive`,
`natural_order_power`, `natural_order_minimal`, and `natural_success_unit`.
The total definitions `natural_unit N a`, `natural_order N a`, and
`natural_success N a` do not require a proof argument; their arithmetic
interpretation theorems explicitly require N>1 and, where needed,
coprimality. All four central audited theorems are closed under the global
context. Equation (20) is checked independently in
`ClassicalShorFactorExtraction.natural_success_factor` in
`shor_factor_extraction.v`.
