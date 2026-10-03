# Concrete unit Chinese remainder bridge

This is the Chinese remainder step in the independent finite counting proof
of classical.pdf Lemma 7.2(2), PDF pp. 40–41. See SHOR-COUNTING-NOTES.md for
the complete counting argument. No claim about the order-finding selector
or its quantum success probability is used here.

For coprime m,n>1, use MathComp's existing finite multiplicative groups
`{unit 'Z_m}`, `{unit 'Z_n}`, and `{unit 'Z_(m*n)}`. Every element has a
unique natural representative below its modulus, and its representative is
coprime to that modulus. Send a unit modulo mn to its two reductions. Each
reduction remains a unit because coprimality to mn implies coprimality to
each factor. Conversely, take the Chinese remainder of the two canonical
representatives and reduce modulo mn. It is a unit: its residues modulo m
and n equal the given units, so it is coprime to both moduli and hence to
their product. The two maps cancel because equality modulo both coprime
factors is equivalent to equality modulo their product. Thus this is a
concrete finite bijection, with the inverse given by MathComp's `chinese`.

Reduction commutes with multiplication and every natural power, since
modular reduction does. Consequently, a power of a unit modulo mn is one
exactly when the corresponding powers of both coordinate units are one.
In a finite group, this means an exponent is divisible by the global order
exactly when it is divisible by both coordinate orders. The least common
multiple has precisely this divisor property, so the global order is the
least common multiple of the two coordinate orders. These are actual group
orders, not separately postulated order witnesses.

The binary bijection also proves any finite sum over global units equals
the sum over coordinate pairs, reindexing by its inverse. Its cardinality
specialization gives the product of the two unit cardinalities. Iterating
this bridge over distinct prime powers will supply the product model used
in the counting argument; the binary lemma itself needs no primality.

The checked binary API is `ClassicalShorCRT.crt_units_bijective`,
`crt_units_mul`, `crt_units_power`, `crt_units_order_dvd`,
`crt_units_order`, and `crt_units_card`. The canonical `unit_reduction`
morphism reduces a unit modulo N to a unit modulo any divisor M>1;
`unit_reduce_value` and `unit_reduce_power` give its concrete behavior.

For an arbitrary finite family q_i>1 of pairwise coprime moduli with
product N, take all these divisor-reduction morphisms together into the
dependent finite function type. They are jointly injective: equal local
images imply the natural representatives are congruent modulo every q_i;
induction through the binary Chinese remainder theorem implies congruence
modulo their product N; the representatives are below N, so are equal.
Totient multiplicativity, proved inductively using coprimality of each
factor with the remaining product, identifies the source cardinality with
the product of the coordinate cardinalities. The dependent function type
has exactly that product cardinality. An injection between these finite
types of equal cardinality is a bijection. Hence this gives a full product
CRT interface without assuming a product representation or a success count.

The finite-family bridge is checked in `shor_crt_product.v` as
`ClassicalShorCRTProduct.reduction`, `reductions_jointly_injective`,
`unit_tuple`, `unit_tupleE`, `unit_tuple_card`, and `unit_tuple_bijective`.
The tuple type is the actual dependent finite function type whose i-th
entry is a MathComp unit modulo q_i. Auxiliary `coprime_product`,
`totient_product`, and `congruence_product` prove the needed finite-product
arithmetic. These results accept an arbitrary finite index type, including
its cardinality; their explicit nontrivial-product hypothesis simply rules
out an empty factorization when N>1. They introduce no assumption about
order distributions, event counts, or program validity.
