# Numerical probability corollary of the unit count

This records the final finite-ratio step of classical.pdf Lemma 7.2(2),
PDF pp. 40–41, independently of the order-finding postprocessor.
For a nonempty finite type T, let b count a predicate Bad and let g count
its complement. Thus b+g=|T|. Suppose d>0 and d*b≤|T|. Division by the
positive numbers d and |T| gives b/|T|≤1/d. Since g/|T|=1−b/|T|,
the complementary probability is at least 1−1/d. Natural counts embed
order-preservingly into any numeric field, so the proof applies to the
project's real and complex scalar fields without an additional assumption.

For an odd N>1, use the actual finite group of units modulo N, whose
cardinality is the positive integer totient(N). Let Bad be the event that
the exact multiplicative order is odd or the half-order power is −1.
The previously proved concrete count bound has
 d=2^(size(primes N)−1), which is positive. Its complement is precisely the
favorable event “even exact order and half-order power different from −1.”
The ratio lemma therefore yields the claimed lower bound for uniform units.
The separate sampling bridge identifies this ratio with the conditional law
of the literal uniform random assignment, given coprimality.

For the scalar mixture step in Equation (21), assume lambda>=0 and
0<=p<=1, 0<=c<=1. Then p*c<=1, by multiplying the upper bounds through
nonnegative factors. The difference between
lambda+p*((1-lambda)*c) and p*c is lambda*(1-p*c), which is nonnegative.
Consequently the mixture is at least p*c. This is an algebraic implication;
it asserts no success probability for the paper's order-finding code.

The checked Rocq results in `shor_probability.v`, module
`ClassicalShorProbability`, are `finite_complement_ratio`,
`uniform_unit_success_bound`, and `mixture_lower_bound`. The concrete
unit theorem takes exactly a numeric field F, N, `1 < N`, and `odd N`;
its lower bound is `1 - 1 / (2 ^ (size (primes N)).-1)%:R` and its
right side is `#|unit_success|%:R / (totient N)%:R`. In particular the
predecessor applies to the exponent, as in Lemma 7.2(2).

Focused compilation and Dune integration with Rocq 9.1 succeeded.
`Print Assumptions` reports `Closed under the global context` for all three
results. The literal-sampler
interpretation and the connection to the surrounding program are separate
results; the unit bound itself does not assume an order-finding contract.
