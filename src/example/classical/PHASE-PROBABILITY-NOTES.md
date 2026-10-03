# A finite Born-event complement bound

This supporting argument supplies the event-probability step used to inspect
the classical paper's Section 7.3 phase-estimation claim (C6). It is valid
for every finite orthonormal basis, independently of any phase-estimation
error estimate.

Let b_i be an orthonormal basis and let psi be normalized. Expanding psi in
that basis and taking its inner product with itself gives Parseval's identity:
the sum of |<b_i,psi>|^2 is <psi,psi>=1. Every summand is nonnegative.
If an event P excludes i0, its sum is therefore no greater than the sum
over all i different from i0: for each index the event indicator is at most
the indicator of inequality with i0. Splitting the total sum at i0 gives
the latter sum as 1-|<b_i0,psi>|^2. This proves the desired bound without
an additional dimension assumption; an index i0 is already supplied.

The formal version first proves the generic orthonormal-basis result for a
vector with inner product one, and then specializes it to the computational
basis of an inhabited finite type and a normalized-state value. No global
quantum register model is needed.

The checked module `ClassicalPhaseProbability` in `phase_probability.v`
provides `born_total`, `onb_event_complement_bound`, and
`computational_event_complement_bound`. Focused Rocq 9.1 compilation and
Dune integration succeeded. The assumptions audit of all three results
reports only inherited real/classical foundations: Dedekind-real decisions,
extensionality, and choice. It includes no `qreg.G` or new axiom.
The generic theorem takes only a finite orthonormal basis,
a vector with inner product one, an event, and an excluded outcome.
