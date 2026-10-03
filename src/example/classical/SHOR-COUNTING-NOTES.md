# Uniform modular-unit counting (Lemma 7.2(2))

Source: `classical.pdf`, PDF pp. 40–41, Lemma 7.2(2), the definition of E(x),
and its use in Equation (21). Both rendered pages were inspected. This
number-theory statement is independent of the printed order-finding
postprocessor and of C7. It is not blocked by that counterexample.

The statement concerns an odd composite N and uniform x in {1,...,N-1},
conditioned on gcd(x,N)=1. Write r(x) for the exact multiplicative order and
E(x) for “r(x) is even and x^(r(x)/2) is not -1 modulo N.” The intended m
is the number of distinct prime divisors, represented by `size (primes N)`.
Counting prime factors with multiplicity would make the statement false for
odd prime powers: their units never satisfy E(x), whereas m>1 would give a
positive lower bound. For the distinct-prime interpretation, m=1 gives the
correct trivial lower bound zero. The stronger `cmp(N)` hypothesis used by
the program implies m>1, but is not needed for this counting lemma.

## Complete finite counting argument

Factor N as the product of its pairwise coprime odd prime powers
q_i = p_i^(e_i), for i=1,...,m, with e_i>0 and distinct primes p_i.
Let G_i be the finite multiplicative group of units modulo q_i. The Chinese
remainder theorem gives a bijection from units modulo N to the product of
the G_i, respecting multiplication and powers. A uniformly selected unit
therefore has independent uniform coordinates x_i in G_i. Conditioning
the paper's uniform x on coprimality gives precisely this uniform unit
distribution: every unit representative lies in {1,...,N-1}, and all were
assigned the same original weight 1/(N-1).

First establish the unique-involution property for each G_i. If y^2=1
modulo q_i, then q_i divides (y-1)(y+1). The odd prime p_i cannot divide
both factors, whose difference is 2. The entire p_i-power q_i therefore
divides one factor, so y=1 or y=-1 modulo q_i. Since q_i is odd and greater
than one, these two residues are distinct. Thus -1 is the unique element
of order two. This elementary argument does not require a primitive-root
theorem modulo prime powers.

For a finite abelian group G with exactly the square roots {1,-1}, let
D be its exponent and let s=v_2(D). The exponent is positive and even,
because -1 has order two. An element g of order D exists: every finite
abelian group realizes its exponent as an element order. Define the group
homomorphism h(x)=x^(D/2). Its square is x^D=1, so its image lies in
{1,-1}; and h(g) is not 1 by the exact order of g, hence h(g)=-1.
The image is therefore exactly {1,-1}. Multiplication by g is a bijection
between the fibers of 1 and -1: h(gx)=-h(x). Consequently each fiber has
exactly half the elements of G.

Every element order r divides D. For a positive divisor r of a positive
even D, r divides D/2 exactly when v_2(r)<v_2(D): writing D=r*a reduces
the assertion to a being even. Therefore h(x)=1 exactly when
v_2(ord(x))<s, and h(x)=-1 exactly when v_2(ord(x))=s. The maximal
valuation fiber has size |G|/2; each smaller individual valuation fiber
lies inside the other half; larger fibers are empty. Thus, for every
integer k≥0,

    2 * #{x in G : v_2(ord(x))=k} ≤ |G|.

Apply this to each G_i. Put r_i=ord(x_i), k_i=v_2(r_i), and
r=ord(x)=lcm_i r_i. The CRT bijection gives the order identity directly:
a power of x is 1 exactly when that exponent is divisible by every r_i.
Hence v_2(r)=max_i k_i. If every k_i is zero, r is odd and E(x) fails.
Otherwise put k=max_i k_i>0. Since r_i divides r,

* if k_i<k, then r_i divides r/2 and x_i^(r/2)=1;
* if k_i=k, then r_i does not divide r/2. Nevertheless the square of
  x_i^(r/2) is 1, so the unique-involution property gives x_i^(r/2)=-1.

CRT now says x^(r/2)=-1 modulo N exactly when every k_i equals k.
Combining the odd-order and even-order cases, failure of E(x) is exactly
the event that all k_i are equal.

Let c_i(k)=#{x_i in G_i : v_2(ord(x_i))=k}. Only finitely many k occur.
Independence gives the failure count B=Σ_k Π_i c_i(k). For each fixed k,
bound all factors except the first by the half-size inequality above:

    2^(m-1) * Π_i c_i(k) ≤ c_1(k) * Π_(i>1) |G_i|.

Summing and using Σ_k c_1(k)=|G_1| gives

    2^(m-1) * B ≤ Π_i |G_i| = |units modulo N| = totient(N).

The unit set is nonempty (it contains 1), so division by its cardinality
is legitimate. Taking complements yields exactly

    Pr[E(x) | gcd(x,N)=1] ≥ 1 - 1/2^(m-1).

This is entirely finite counting. It does not assume an order-finding
program's success, and does not infer that its returned denominator is an
exact order. The proof requires neither a cyclicity theorem for all units
modulo p^e nor a repaired postprocessor.

## Available checked foundations

The following APIs were inspected in the installed MathComp 2.6.0 sources.
Paths below are relative to `user-contrib/mathcomp` in the active switch.

| Obligation | Existing API |
| --- | --- |
| Distinct prime factorization | `boot/prime.v`: `primes_uniq`, `prod_prime_decomp`, `prime_decompE`, `mem_prime_decomp`, `mem_primes`, `pfactor_coprime`, `coprime_pexpr` |
| Binary CRT and explicit inverse | `boot/div.v`: `chinese_remainder`, `chinese`, `chinese_modl`, `chinese_modr`, `chinese_mod` |
| Units modulo an arbitrary N>1 | `algebra/zmodp.v`: `{unit 'Z_N}`, `units_Zp`, `unitZpE`, `unit_Zp_expg`, `val_Zp_nat`, `card_units_Zp`, `units_Zp_abelian` |
| Positive group exponent and all element orders divide it | `solvable/abelian.v`: `exponent_gt0`, `dvdn_exponent`, `expg_exponent`, `exponentP` |
| Element realizing the exponent | `solvable/abelian.v`: `exponent_witness`; `solvable/nilpotent.v`: `abelian_nil` supplies its premise |
| Exact order and power divisibility | `solvable/cyclic.v`: `order_dvdn`, `orderXdvd`, `orderXgcd`, `orderXdiv`; `finite_group/fingroup.v`: `order_gt0`, `expg_order`, `expgMn` |
| Two-adic arithmetic | `boot/prime.v`: `lognM`, `logn_div`, `logn_lcm`, `pfactor_dvdn`, `dvdn_leq_log`, `pfactor_coprime`; `boot/div.v`: `dvdn2`, `coprime2n`, `coprimeXl`, `Gauss_dvdr` |
| Equal homomorphism-fiber sizes | `finite_group/morphism.v`: `Morphism`, `rcoset_kerP`, `morphpre_set1`; `finite_group/fingroup.v`: `card_rcoset`; `finite_group/quotient.v`: `card_morphpre`, `card_morphim` |
| Product and partition counts | `boot/finfun.v`: `card_family`, `card_dep_ffun`; `boot/finset.v`: `card_partition`, `card_imset` |
| Unit cardinalities | `boot/prime.v`: `totient_gt0`, `totient_count_coprime`, `totient_pfactor`, `totient_coprime` |

`totient_count_coprime` already contains a concrete binary CRT reindexing
proof with `chinese`; it provides a local pattern for constructing the
finite unit-product bijection. The installed `units_Zp_cyclic` theorem in
`solvable/cyclic.v` assumes a prime modulus. It must not be applied to p^e
without proving the missing hypothesis. The exponent argument above avoids
that unavailable specialization.

## Checked generic group step

`shor_group_counting.v`, module `ClassicalShorGroupCounting`, directly
compiles. `dvdn_half_logn` proves the exact divisor/valuation equivalence
for a positive even n and a divisor d. `exponent_even`,
`half_exponent_square`, and `half_exponent_is_one` establish the exponent
map's arithmetic. `half_exponent_witness` derives a preimage of the unique
involution from `exponent_witness` and abelianness; no realization premise
is supplied by the caller.

The final counting proof uses an equivalent finite injection formulation.
`translate_order_valuation` proves that multiplication by this witness
changes the two-adic order valuation of every group element. Thus it sends
each fixed-valuation set into its complement. Multiplication is injective,
so the set has cardinality at most its complement. Their cardinalities sum
to the whole group cardinality, proving `order_valuation_fiber_half`:

    2 * #{x : gT | logn 2 (order x) = k} ≤ #gT.

Its premises are a finite group, abelianness, a nonidentity involution z,
and the structural fact that all square roots of one are 1 or z. The
prime-power instantiation must prove these structural premises. No
probability bound or target correctness statement is a premise.

Validation of `shor_group_counting.v`: direct compilation and the mapped
Dune target pass. `Print Assumptions` for `dvdn_half_logn`,
`half_exponent_witness`, `translate_order_valuation`, and
`order_valuation_fiber_half` reports “Closed under the global context.”
The generic result introduces no axiom and uses no inherited quantum-memory
or classical-real foundation.

## Checked arithmetic foundations and status

The mathematical proof above is complete, and the generic group step is
checked as described above. `shor_prime_power.v` passes direct and mapped
compilation; its audited results are closed under the global context:
`ClassicalShorPrimePower.square_roots_mod` and `unit_square_roots` prove
the actual odd-prime-power root classification, and
`prime_power_fiber_half` instantiates the generic cardinal bound.
`shor_order_event.v` passes direct and mapped compilation of the exact failure-event
characterization in `failure_iff_equal_valuations`; its structural
homomorphism premises are described in `SHOR-ORDER-EVENT-NOTES.md`.
Its central assumptions audits also report closed global context.

`shor_factorization.v`, module `ClassicalShorFactorization`, supplies
`factor_index`, `factor_prime`, `factor_exponent`, and `factor_modulus`.
`factor_count_positive` and `first_factor` prove the nonempty index set for
N>1. `factor_prime_is_prime`, `factor_exponent_positive`,
`factor_modulus_gt1`, `factor_moduli_coprime`, and `factor_modulus_odd`
prove the factor side conditions. `factorization` proves their product is
N. The module passes direct and mapped compilation.

`shor_crt.v` builds the actual modular unit operations and binary CRT.
`shor_crt_product.v`, module `ClassicalShorCRTProduct`, supplies actual
component `reduction` maps, `reductions_jointly_injective`, and the
`unit_tuple_bijective` bijection. `shor_modular_event.v` proves
`unit_reduce_negative_one`. All three pass direct and mapped compilation;
their audited central theorems are closed under the global context.

`shor_product_counting.v`, module `ClassicalShorProductCounting`, proves
`natural_diagonal_half_bound` for arbitrary natural-number labels on a
finite product. Its mapped compilation and closed-context audit pass.
The concrete assembly below discharges its fiber premises and the event
theorem's structural hypotheses. `shor_uniform.v` now identifies this
count ratio with the conditional law induced by
`ClassicalShorProgram.uniform_probability`; its
`random_conditional_success_bound` is the paper's conditional bound for
the actual Random source and exact arithmetic order. `shor_sampling.v`
also checks the source partition and Equation (21). These results are
independent of C4, C6, and C7.

## Assembly into the actual modular-unit count

For the final arithmetic theorem, take the index type to be the ordinal
indices of the distinct prime list `primes N`; its size is exactly m.
The checked factorization supplies q_i, their positivity and pairwise
coprimality, and their product N. Instantiate the CRT tuple bijection with
these moduli. Instantiate the event theorem with the actual reductions,
the local `negative_one q_i`, and global `negative_one N`. The reduction
of global negative one to every local negative one is an arithmetic
identity for divisors, not an additional premise.

For every unit x, the event theorem identifies its failure predicate with
the diagonal predicate of the CRT tuple. A bijection preserves predicate
cardinalities, so their failure and diagonal counts agree. Each coordinate
valuation fiber satisfies the checked prime-power half-cardinality bound.
The natural-label version of the finite product bound therefore gives
2^(m-1) times the diagonal count at most the tuple-space cardinality.
The CRT bijection and `card_units_Zp` identify this cardinality with
`totient N`. This yields the concrete failure-count theorem with only
N>1 and odd N as hypotheses; no structural CRT, root, or probability
premise remains. Composite N is a covered specialization.

The implementation is `shor_counting.v`, module `ClassicalShorCounting`.
`factor_tuple_bijective`, `factor_reduction_jointly_injective`,
`factor_involution_nontrivial`, `factor_roots_two`, and
`factor_reduction_negative_one` discharge the structural obligations.
`failure_diagonalE` and `failure_card` identify the concrete failure event
and its cardinality; `factor_order_fiber_half` supplies every local bound.
The resulting `failure_count_bound` states

    2 ^ (size (primes N)).-1 * #|unit_failure| <= totient N.

Its only assumptions are `1 < N` and `odd N`. `unit_successE` identifies
the exact-order success predicate with the complement of `unit_failure`.
The module passes direct and mapped Dune compilation. A check of its
generalized signature confirms that `failure_count_bound` takes exactly N,
`1 < N`, and `odd N`; the structural obligations are not residual
parameters. `Print Assumptions` for `failure_diagonalE`, `failure_card`, and
`failure_count_bound` reports `Closed under the global context` for each.

The numerical corollary is checked in `shor_probability.v` as
`ClassicalShorProbability.uniform_unit_success_bound`: for any numeric
field F, odd N>1, the uniform-unit probability of `unit_success` is at
least `1 - 1 / (2 ^ (size (primes N)).-1)%:R`. It follows from
`finite_complement_ratio`, using `card_units_Zp` and the complement
identity `unit_successE`. The complete scalar argument, including the
independent mixture inequality from Equation (21), is recorded before
formalization in `SHOR-PROBABILITY-NOTES.md`.
