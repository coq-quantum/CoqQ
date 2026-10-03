# Exact failure event under component homomorphisms

This is the group-theoretic event identification used in the proof of
classical.pdf Lemma 7.2(2), p. 40; the full counting argument is recorded in
`SHOR-COUNTING-NOTES.md`.

Let G be a finite group with a nonempty finite family of homomorphisms
red_i:G→H_i. Assume they are jointly injective. In each H_i, assume every
square root of one is either one or a specified nonidentity element z_i.
Let z in G project to every z_i. These are structural hypotheses that the
modular CRT construction must prove; no success-probability statement is a
hypothesis. Abelianness is unnecessary for this event-identification step.

Fix x in G. Write r=ord(x), r_i=ord(red_i(x)), k=v_2(r), and k_i=v_2(r_i).
Every r_i divides r, since red_i(x)^r=red_i(x^r)=1. Thus k_i≤k.
If r is odd, each r_i is odd, every k_i is zero, and the failure event
“r is odd or x^(r/2)=z” is true.

Suppose r is even. For every i, the square of red_i(x^(r/2)) is one.
The positive-divisor lemma proved in `shor_group_counting.v` gives

    red_i(x^(r/2))=1  iff  r_i divides r/2  iff  k_i<k.

By the local square-root classification and z_i≠1, the remaining case is
red_i(x^(r/2))=z_i exactly when k_i=k. At least one i has k_i=k: otherwise
all images of x^(r/2) would be one. Joint injectivity would give
x^(r/2)=1, contradicting its exact positive order r, since r/2<r.
Equivalently the same divisor lemma would require k<k.

If x^(r/2)=z, all component images are z_i, so every k_i=k. Conversely,
if all k_i are equal, the component attaining k shows that their common
value is k. Every component image of x^(r/2) is then z_i=red_i(z), and
joint injectivity yields x^(r/2)=z. Together with the odd-order case this
proves that failure is exactly equality of all local two-adic order values.

The conclusion is valid for arbitrary finite groups and homomorphisms
satisfying the stated structural hypotheses. It does not assume a product
decomposition, cyclic groups, a least-common-multiple order formula, or a
correct order-finding program. The CRT application supplies the structural
hypotheses and identifies z with the modular residue -1.

Checked in `ClassicalShorOrderEvent`: `component_order_dvd`,
`component_valuation_le`, `odd_component_valuation`,
`half_component_square`, `half_component_is_one`,
`half_component_is_involution`, and `component_valuation_reaches` prove
the individual steps. `failure_iff_equal_valuations` gives the exact Boolean
event equality, indexed against any chosen component i0. The module passes
direct compilation and mapped Dune compilation. An assumptions audit of
`failure_iff_equal_valuations`, `half_component_is_involution`, and
`component_valuation_reaches` reports `Closed under the global context` for
each theorem; the structural assumptions above remain explicit arguments.
