# Normalized tests and store updates (Lemmas 4.10 and 3.12)

For Lemma 4.10 (p. 21), a positive operator rho with positive trace is its
trace times the normalized density rho/tr(rho). Any linear trace-pairing
inequality that holds for normalized densities therefore holds for rho.
When the trace is zero, positivity implies rho=0 and the inequality is
trivial. Thus normalized density tests detect the full operator order.
Apply this to the checked weakest-precondition characterization at each
store. The arbitrary cq-state validity follows from that characterization;
the reverse implication simply tests a singleton state. Partial validity
uses complementary assertions, and the established complement identity
rewrites it into exactly the paper's lost-trace inequality with initial
trace one. This argument is shared with the existing distributed normalized
test interface, which retains aliases to the classical common result.

For Lemma 3.12 (p. 14), update the store by u(m)=m[x:=eval(e,m)] and use the
identity quantum channel at every input. The resulting cq-state has component
sum over all m with u(m)=out of rho(m). This summation is essential because
different stores can update to the same output. The shared kernel action
already proves summability and positivity of that merged family. Absolute
Fubini, as formalized by `expect_sunit`, rewrites its expectation as
sum_m tr(P(u(m)) rho(m)), which is exactly the expectation of the substituted
assertion P composed with u. Taking P=I shows that store update preserves
total trace. The operation agrees definitionally with assignment denotation.

`CQNormalizedValidity.operator_le_normalized` and `valid_normalized_iff`
give the common test theorem. `valid_total_normalized` and
`valid_partial_normalized` state the two paper clauses directly, the latter
with the initial trace-one lost-trace formula.

`CQStateUpdate.update_stateE` exhibits the merged output components.
`expect_update` is Lemma 3.12, `update_state_mass` proves exact trace
preservation, and `update_state_assignment` identifies the state operation
with the shared language's assignment denotation.

Validation: both classical modules and the distributed compatibility alias
pass the mapped Dune build. `Print Assumptions` for `valid_normalized_iff`,
`valid_partial_normalized`, `expect_update`, `update_state_mass`, and the
distributed alias reports only the inherited classical real, choice, and
extensionality foundations and the existing `qreg.G` memory context. There
are no new axioms or admitted obligations.
