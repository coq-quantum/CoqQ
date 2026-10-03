# The source sampler and Equation (21)

Source: `classical.pdf`, Section 7.5, Equation (21), PDF p. 41, and the
literal uniform assignment in Table 6. This argument concerns that actual
sampler and the arithmetic exact-order event. It does not assume or assert
correctness of the order-finding postprocessor.

Fix N>1. The sampler has one outcome a=i+1 for each ordinal i<N-1, each
of mass 1/(N-1). For each such positive a, gcd(a,N)>0. Hence precisely
one of gcd(a,N)>1 and gcd(a,N)=1 holds. Coprimality is the latter equality,
with the gcd arguments interchanged. Summing the two complementary indicator
functions against the common mass gives

    direct_probability + coprime_event_probability(True) = 1.

Write lambda for the first term and q for the coprime probability. Thus
q=1-lambda, lambda>=0, and q>0. For odd N the previously checked conditional
bound gives c<=r/q, where c=1-1/2^(size(primes N)-1) and r is the source
probability of coprimality together with the favorable exact-order event.
Multiplication by q>0 gives q*c<=r. The positive integer denominator in c
is at least one, so 0<=c<=1. For any scalar p with 0<=p<=1, multiplication
by p preserves q*c<=r. Adding lambda and applying the already proved
`mixture_lower_bound` gives

    p*c <= lambda+p*((1-lambda)*c) = lambda+p*(q*c) <= lambda+p*r.

Every probability in this statement comes from the printed sampler's finite
sum. The arbitrary scalar p is an algebraic input, not a claimed verified
success probability for the surrounding order-finding program.

The checked module `ClassicalShorSampling` in `shor_sampling.v` proves
`gcd_guard_complement`, `sampling_partition`,
`coprime_probability_complement`, and `sampling_mixture_bound`.
Focused Rocq 9.1 compilation and Dune integration succeeded. The assumptions
audit of the partition, complement identity, and mixture bound reports only
the project's inherited real/classical foundations (Dedekind-real decisions,
extensionality, and choice). It reports no new axiom and no order-finding
success assumption. The final theorem takes N>1,
the actual classical input store, `odd N`, and `0 <= p <= 1`; all event
probabilities are the source definitions from `shor_program.v` and
`shor_uniform.v`.
