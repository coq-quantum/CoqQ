# Distinct prime factors of the paper's Shor inputs

Source: classical.pdf, Section 7.5, PDF pp. 40–41. The printed predicate
cmp(N) requires N>2, oddness, compositeness, and exclusion of perfect
powers. Page 41 uses these conditions to conclude that the number m of
distinct prime divisors exceeds one. This arithmetic conclusion is
independent of any claim about the order-finding program.

For a natural N>1, compositeness is equivalent to not being prime. Exclude
perfect powers by requiring N != a^b whenever a>1 and b>1. This is the
usual natural-number formulation of the printed condition; a positive
integer perfect power with a negative integer base is also a power of
its positive absolute value, so allowing signed bases does not change
which positive N are excluded.

The distinct prime list of N is nonempty because N>1. If it contains only
one prime p, the standard prime factorization of N is N=p^e, where
e=v_p(N)>0. When e=1, N=p is prime, contradicting compositeness. Hence
e>1; since p is prime, p>1, and N=p^e contradicts the exclusion of perfect
powers. Therefore the list has at least two elements. Oddness is not
needed for this implication, but is retained in the explicit cmp predicate
to match its use in the paper.

Together with the independently proved counting bound, m>1 makes
2^(m-1) at least two and hence 1-1/2^(m-1) at least one half. This arithmetic
observation does not provide a success probability for the false printed
order-finding postprocessor.

The implementation in `shor_composite.v`, module `ClassicalShorComposite`,
defines `not_perfect_power` and the faithful positive-natural `cmp`
predicate. `distinct_prime_count_gt1` proves the implication using only
N>1, non-primality, and exclusion of perfect powers;
`cmp_distinct_prime_count` specializes it to the printed input conditions.
Direct and mapped compilation pass. Both theorems' assumptions audits
report `Closed under the global context`.
