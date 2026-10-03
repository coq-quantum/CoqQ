# Bounded operational completions: classical Lemma 4.2

Source: `classical.pdf`, PDF page 17, Lemma 4.2(1–2), together with
Definition 4.3. The sum is indexed by execution routes, preserving distinct
random or measurement choices even when their final configurations coincide.
Only nonzero route contributions matter; zero-weight branches are harmless.

The separate exact route-cost development associates each successful route
with its actual number of small steps. Atomic commands and the false-guard
loop exit cost one step. Conditional selection and true-guard loop unfolding
add one step to the continuation. Sequential composition adds the costs of
its two subroutes: each step of the first command is lifted through Sequence,
and its final step also exposes the second command, so no extra administrative
step is inserted. The counted-execution correspondence identifies cost at
most n with successful executions terminating within n steps.

For a fixed input store and partial density operator, let F(r) be the
singleton cq-output operator family of route r, or zero for an unsuccessful
route. The established operational summability theorem gives
`sum_r ||F(r)||_1 ≤ tr(rho)`. Each F(r) is positive. For any subset A of
routes, restricting F to A preserves summability and positivity and cannot
increase this bound. Hence the sum over A is a well-formed cq-state; its
support and the set of nonzero contributing routes are countable. This also
proves countability at each exact execution length.

Take A_n to be routes of cost at most n and write Δ_n for their sum. The
sets A_n increase, and all contributions are positive, so Δ_n≤Δ_(n+1).
Every route has finite cost. Absolute summability therefore makes Δ_n
converge in the summable-family norm to the unrestricted operational sum:
given epsilon, a finite set captures all but epsilon of the norm sum, and
all its routes occur by the maximum of their costs. This is precisely the
existing `summable_sigma_nat_cvg` theorem after restriction reindexing.

The cq-state supremum of the increasing Δ_n is its norm limit. Uniqueness
of limits identifies that supremum with the full operational sum, and the
already checked operational/denotational correspondence identifies it with
execution of the compositional kernel on the singleton input cq-state.
There is no bound on runtime and no finite-support restriction on sampling.

The generic restriction argument is checked in `operational_approximants.v`,
module `ClassicalOperationalApproximants`, as `selected_summable`,
`selected_state`, `selected_mass_bound`, `selected_routes_countable`,
`selected_state_mono`, `completion_state_chain`, `completion_state_cvg`,
`completion_state_sup`, and `completion_state_denote`.

`operational_completions.v`, module `ClassicalOperationalCompletions`, uses
the actual `ClassicalOperationalRouteCost.route_cost`:

- `exact_completions_countable` and `bounded_completions_countable` prove
  countability for the exact-length and bounded-length counted executions.
  `selected_routes_countable` also gives countability before endpoint
  aggregation, preserving route multiplicities.
- `bounded_completionE` gives the exact positive route sum for cost at most n.
  `bounded_completion_zero` gives the empty initial approximant.
- `bounded_completion_chain`, `bounded_completion_countable`, and
  `bounded_completion_mass` establish the cq-state chain and trace bound.
- `bounded_completion_cvg` proves norm convergence to the full operational
  sum. `bounded_completion_sup`, `bounded_completion_upper`, and
  `bounded_completion_least` identify the denotational output as its least
  upper bound.

The exact route-cost and counted-execution correspondence is checked in
`operational_route_cost.v`. `successful_route_exact_iff` and
`successful_route_bounded_iff` give both directions; the separate
`operational_counted_paths.v` additionally relates exact nonzero routes to
counted maximal live paths. See `OPERATIONAL-ROUTE-COST-NOTES.md`.

The generic approximants module passed direct compilation, Dune mapping,
and five central assumption audits on 2026-10-03. Those results use only the
inherited classical foundations and existing ambient-memory parameter
`qreg.G`; no new axiom or admission is introduced.
The concrete completion module passed direct compilation, Dune integration,
the whole-project checkpoint build, and six central assumption audits on the
same date. Its audited countability, initial-zero, chain, supremum, and
leastness results have the same inherited foundations and `qreg.G` only.
See the shared validation record for the build boundary.
