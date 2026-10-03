# The conditional law of the printed Random command

For N>1, `ClassicalShorProgram.uniform_probability` samples each integer
1,...,N-1 with probability 1/(N-1). The underlying finite sampling index is
an ordinal i<N-1, whose sampled value is i+1.

Every modular unit has a unique canonical representative a<N. Coprimality
and N>1 imply a>0, so a-1 is a sampling index. Conversely, every sampling
index whose value is coprime to N gives a unit via the natural-number map
into Z_N. The two constructions are inverse on these domains. Thus, for
any predicate P on sampled natural numbers, reindexing the finite sum gives

    sum_(i<N-1, coprime(N,i+1) and P(i+1)) mass(i+1)
      = #{u : units modulo N | P(representative(u))} / (N-1).

With P=true, this is the probability of the conditioning event. It is
positive because the unit one exists. Dividing the event probability by
this conditioning probability cancels 1/(N-1), leaving the cardinality
ratio for the uniform unit group. Therefore the pure modular-unit count
theorem applies to the conditional law of the actual printed Random
command. This argument neither assumes a quantum order-finding outcome
distribution nor repairs its printed postprocessor.

The finite sum uses the actual `probability_mass uniform_probability` from
the language's Random source. Its exact mass formula has already been
proved. `shor_uniform.v` formalizes the bijection, reindexing, positivity,
and conditional ratio.

The checked names in `ClassicalShorUniform` are `sampled_unitK`,
`sample_indexK`, `sample_unit_reindex`, `coprime_event_probabilityE`,
`conditioning_probability_positive`, and `conditional_probabilityE`.
Finally, `random_conditional_success_bound` instantiates the concrete
modular-unit bound and the exact-order natural event from
`ClassicalShorSampleEvent`. Its only arithmetic assumptions are N>1 and
odd N; the initial classical store is arbitrary. The event is exactly
even multiplicative order and modular half power different from N-1.
Direct compilation passes; integration and assumption audits are recorded
in the validation record.
