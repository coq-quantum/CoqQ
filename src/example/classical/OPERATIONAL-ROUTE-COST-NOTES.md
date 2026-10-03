# Exact lengths of terminating computations

Classical paper, Section 4.2, Lemma 4.2 (printed pp. 16–17), indexes its
operational approximants by the number of small transitions. The existing
`route_size` is a structural induction measure; its sequence constructor
adds one, although the operational sequence rules add no extra transition.
Consequently it cannot be used as the paper's transition count.

Define `route_cost` by assigning one to each atomic route and to a false
while guard, adding one for a conditional choice or a true while guard,
and adding the costs of the two routes in a sequence. Every route has
positive cost. A counted terminating derivation has a final step of cost
one, and each preceding step increases the count by one.

For soundness, induct on the route. The atomic and guard cases follow the
corresponding transition rule. In a sequence, lift each step of the first
terminating derivation through its surrounding sequence. Its final step
changes the residual command to the second component, so concatenating the
second derivation uses exactly the sum of their lengths. No extra step is
introduced. This establishes that evaluating a route successfully produces
a terminating derivation of exactly its route cost.

Conversely, prepend a small transition to a successful route for its
residual command. Induction on the transition reconstructs a route whose
cost increases by exactly one. For a transition ending a sequence's first
component, reconstruct its atomic-length route and concatenate the existing
route for the second component. For an internal sequence transition, split
the residual sequence route, prepend the transition to its first component,
and retain its second component. All other cases select the corresponding
atomic or guard route. Induction on a counted terminating derivation now
gives a successful route with exactly the stated cost. Existentially
quantifying over counts up to n gives the bounded version.

The operational transition relation retains zero-output branches, whereas
the paper's computation paths omit them. This does not change cq sums,
because their contribution is zero. For a nonzero final output, every
intermediate output is nonzero: a zero operator stays zero under every
transition. The exact counted derivation can therefore be converted into
a live path of the same length. Conversely a counted live path ending in
the empty residual command gives a counted terminating derivation. Empty
residual commands are terminal, so these successful paths are maximal.

Formal results are recorded in `operational_route_cost.v`, module
`ClassicalOperationalRouteCost`. Its central APIs are `route_cost`,
`eval_route_counted`, `counted_terminating_route`,
`successful_route_exact_iff`, and `successful_route_bounded_iff`.

The separate `operational_counted_paths.v`, module
`ClassicalOperationalCountedPaths`, defines `counted_path` and
`counted_maximal_path`. Theorems `counted_path_terminates` and
`counted_terminates_path` give the exact live-path correspondence, and
`successful_counted_route_iff` identifies an n-step successful maximal path
with a route of cost n having nonzero output. Both modules compile directly
and pass their qualified Dune builds. Mapped assumption audits of both
correspondences use only the inherited classical-real, choice and
extensionality foundations and cqwhile's fixed memory parameter `qreg.G`.
