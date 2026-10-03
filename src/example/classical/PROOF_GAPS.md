# Proof gaps and fidelity decisions

Source: Yuan Feng and Mingsheng Ying, *Quantum Hoare Logic with Classical
Variables*, ACM TQC 2(4), article 16 (2021), `classical.pdf`. Page numbers below
are PDF page numbers, equal to the suffix of the printed article page number.

## C1. The asserted omega-CPO of assertions is false

**Location:** page 11, paragraph following Definition 3.5; consequences on
pages 13-14 (Lemma 3.11(3-4)), page 22 (Definition 4.13), and pages 27-29
(weakest-precondition-based completeness arguments).

**Status:** mathematical counterexample established. On 2026-10-03 the user
approved unrestricted effect-valued semantic predicates for limits and
predicate transformers, while retaining the exact paper assertion subclass.
The broader domain is an explicit correction, not a proof of the false
original claim. No Rocq counterexample theorem is claimed yet.

Definition 3.5 requires both a countable image and first-order definability of
every fiber. Pointwise monotone limits need not retain either requirement.
Here is a counterexample which already fails the countable-image requirement,
and also proves that no least upper bound exists inside the stated domain.

Take the permitted model with countably infinitely many Boolean variables
`b_0, b_1, ...`, no quantum variables, and consequently scalar effects in
`[0,1]`. Identify Boolean values with `0` and `1`. Define

```
f_n(sigma) = sum_{i < n} 2 sigma(b_i) / 3^(i+1)
g_n(sigma) = f_n(sigma) + 1 / 3^n.
```

Both functions are legitimate assertions: their images are finite; their
fibers are finite Boolean combinations of the finitely many equalities
`b_i = true` and `b_i = false`; and their values lie in `[0,1]`, since
`sum_{i<n} 2/3^(i+1) = 1-3^(-n)`. The sequence `f_n` is increasing.
For every `m,n`, `f_m <= g_n`: when `m <= n`, use monotonicity; when `m > n`,
bound the tail by `3^(-n)`. Thus every `g_n` is an upper bound of the whole
sequence within the paper's assertion domain.

If this sequence had a least upper bound `L` in that domain, leastness would
give `f_n <= L <= g_n` for every `n`. Since `g_n-f_n = 3^(-n)` tends to zero,
pointwise this forces

```
L(sigma) = sum_{i >= 0} 2 sigma(b_i) / 3^(i+1).
```

This map has uncountable image. Indeed, if Boolean sequences first differ at
index `k`, their sums differ by at least
`2/3^(k+1) - sum_{i>k}2/3^(i+1) = 1/3^(k+1) > 0`.
It therefore injects the uncountable set of Boolean sequences into its image.
This contradicts Definition 3.5(1). The constant-one assertion remains an
upper bound; the failure is existence of a *least* upper bound.

The approved repair uses unrestricted effect-valued semantic predicates with
a separate representability predicate. Merely retaining countable images and
declaring a pointwise supremum does not repair the theorem. Program syntax,
cq-states, operational semantics, and denotational semantics do not depend on
this false assertion-CPO claim and can be developed independently.

## C2. The state omega-CPO argument needs support and mass bounds

**Location:** page 10, Lemma 3.3; page 14, Lemma 3.11(1).

**Status:** state-domain argument formalized in `state.v` as
`CQState.chain_converges`, `chain_sup_upper`, `chain_sup_least`, and
`chain_sup_pointwise`, with `bottom_least` for the zero state.
`CQExpectation.expect_chain_sup` proves the expectation-limit statement of
Lemma 3.11(1). `CQExpectationLimits.expect_semantic_sup` and
`expect_semantic_inf` prove the assertion-limit clauses in the approved domain.

For an increasing sequence of cq-states `Delta_n`, use finite-dimensional
positive-operator monotone convergence separately at every store to define
`Delta(sigma) = sup_n Delta_n(sigma)`. Its support is contained in the
countable union of the supports of `Delta_n`, hence is countable. For any
finite set `F` of stores, continuity of trace and finite addition gives
`sum_{sigma in F} tr Delta(sigma)
 = lim_n sum_{sigma in F} tr Delta_n(sigma) <= 1`.
Taking the supremum over finite `F` establishes total mass at most one.
Pointwise leastness gives leastness of the cq-state. The zero function is
least. The same finite-sum argument, now with the nonnegative summands
`tr(Theta(sigma) Delta_n(sigma))`, proves monotone convergence of expectation.
No finiteness of the classical store space is required.

## C3. Terminal computations must retain path multiplicity

**Location:** pages 16-18, Definition 4.1, Lemma 4.2, Definition 4.3, and
Lemma 4.4; pages 19-20, Lemma 4.6(11).

**Status:** branch-labelled operational summation and its denotational
correspondence are formalized for the implemented language, including
state-dependent measurements and unbounded loops, in `operational.v`. The
2026-10-03 continuation requested cqwhile's shared types/expressions and
finite-outcome `mexpr` interface; countably infinite measurements are outside
this revised core API.
`ClassicalOperational.operational_summable` proves summability and
`operational_denotational` proves equality with the compositional semantics.
`eval_route_sound` and `terminating_route` prove existence correspondence
between successful routes and the explicit small-step executions. An explicit
bijection between proof objects of `terminates` and successful routes has not
been proved; these results do not claim such a bijection.

Distinct random or measurement outcomes can later reach identical stores and
identical density operators. A set of endpoint configurations would discard
their multiplicity. Index the sum by finite terminating derivations (routes),
with each probabilistic/measurement outcome recorded. Remove or retain zero
branches consistently; retaining them contributes zero and does not change
the sum. Bound every finite prefix-free collection of terminating routes by
the input trace, using trace preservation of normalized sampling and complete
measurement and trace nonincrease of all other commands. Countability of the
nonzero branching gives countability of finite routes. At each output store,
the bounded positive sum converges in the finite-dimensional operator space.
The route-state family also has bounded finite sums of trace norms, hence
converges in the complete space of summable operator families. Partitioning routes
by the number of loop unfoldings yields the increasing sequence of finite
unrollings and its supremum. This proves the operational sum agrees with the
unbounded denotational loop, rather than making a finite approximation.

The implementation adapts the preserved `cqwhile` route summation proof.
`ClassicalOperational.route` explicitly records typed random and measurement
outcomes; `TR_seqc` keeps both sequential subroutes. Consequently, coincident
endpoints from distinct outcomes remain distinct summands. The generic
`atomic_route_adequacy` lemma uses injective outcome encodings and
`CQInstrument.instrument_psum_bound` for possibly infinite random-assignment outcome families.
`equal_OS_DS_seqc` and `equal_OS_DS_while` establish the sequential and
unbounded-loop cases; `equal_OS_DS` assembles all constructors. The older
`cqwhile.equal_OS_DS` still applies only to its own syntax; the new result is
a separate theorem about `ClassicalLanguage.command`, without its inherited
`Eqdep.eq_rect_eq` dependency.

## C4. Parameterized-unitary wlp formula misses abort inputs

**Location:** page 16, parameterized-unitary syntactic sugar; page 23,
Lemma 4.15(3).

**Status:** the wp formula and original Param inference rule are checked,
including invalid-input Abort boundaries. The printed wlp equality is false;
its correction remains pending approval.

The sugar aborts if a parameter is outside its allowed finite range or selected
register indices are invalid. Lemma 4.15(3) states the same guarded sum formula
for both `wp` and `wlp`. At an invalid input every guard is false, so that
formula is zero. But Table 3 explicitly gives `wlp.abort.Theta = top`.
For example choose `K=1` and constant parameter expression `e=0`.
The stated formula is correct for `wp`. For `wlp`, add the identity effect on
the invalid-input guard, or restrict the equality to valid inputs.

The printed Table 5 `(Param)` inference rule is nevertheless sound without
changing that formula. Its guarded-sum precondition vanishes on invalid
inputs, so the total-correctness rule follows from the correct `wp` equality;
total validity then implies partial validity. To formalize this independently
of the disputed `wlp` equality, enumerate the finite valid parameter/register
choices, select the unique matching integer tuple, and execute its unitary;
if none matches, execute `Abort`. Distinct selected register indices ensure
that each selected quantum register is well formed. Conditional unfolding
gives the branch weakest precondition at the selected index and zero when no
index matches. Uniqueness identifies this case split with the printed finite
guarded sum. No invalid-input liberal-precondition equality is required.

The checked formal results are `CQParameterized.selected_register_valid`,
`selected_wp`, `selected_pre_sum`, and `derives_param` (both correctness
modes). `parameterized_zero_abort` and `selected_duplicate_abort` check the
invalid-parameter and repeated-register boundaries. These establish the
original guarded-sum inference rule without adopting the disputed wlp claim.

`CQParameterizedCounterexample.parameterized_zero_counterexample` now
formally proves the mismatch for constant parameter zero: the actual liberal
precondition is identity and the printed guarded precondition is zero at
every store, for every postcondition. See
`PARAMETERIZED-COUNTEREXAMPLE-NOTES.md`; this is a counterexample, not an
adopted general correction.

## C5. Classical ranking proof overstates pathwise termination

**Location:** page 33, proof of Theorem 6.1 for `(C-WhileT)`.

**Status:** `CQClassicalRanking.valid_integer_while` and
`derives_integer_while` prove the signed-integer rank-family formulation.
`CQGhostRanking.valid_fresh_integer_while` and
`derives_fresh_integer_while` now prove the printed single-body-premise rule
using syntactic freshness, invariant framing, and existential elimination. The formal proof bounds outer body completions by
rank induction and does not claim bounded small-step runtime.

The proof says all computations terminate within `sigma(t)` steps. The
premise is semantic total correctness (an expectation inequality), which
guarantees almost-sure termination, not termination of every infinite path.
A loop body may itself have arbitrarily long terminating runs and an infinite
probability-zero run. A decreasing integer rank bounds the number of outer
body completions while the guard remains true, not the number of small steps
nor every possible path. A sound proof must combine almost-sure termination
of each reached body with a decreasing nonnegative rank and countable
additivity; it must not assume bounded execution time.

## C6. Phase-estimation error must account for wraparound

**Location:** pp. 36–38, Equation (13), the set `K` in Equation (16), and
Lemma 7.1. The ordinary absolute-value bars were checked in rendered PDF
pages 37–38, not inferred from the text extraction.

**Status:** the concrete counterexample is formally checked in
`phase_counterexample.v`; the correction to the stated error metric is
awaiting user approval. The original metric is retained, and no corrected
concentration theorem is claimed.

For `N = 2^t`, the probability of measurement outcome zero is

```
p_0(phi) = |(1/N) sum_{j=0}^{N-1} exp(2*pi*i*j*phi)|^2.
```

Fix any allowed `n,t`. As `phi` tends to one from below, every summand tends
to one, so `p_0(phi)` tends to one. But zero does not belong to the paper's
`K = {m : |phi-m/N| < 2^(-n)}` once `phi > 2^(-n)`. Therefore its claimed
success probability is at most `1-p_0(phi)`, which tends to zero. This
contradicts a uniform lower bound `1-epsilon` for any `epsilon < 1`.

A concrete instance uses `n=1`, `epsilon=1/2`, hence
`t = 1 + ceil(log_2(3)) = 3`, and `phi = 1-1/1024`. With `N=8`, write
`A = (1/8) sum_{j=0}^7 exp(-2*pi*i*j/1024)`. The checked proof uses
`a_j = pi*j/1024`, `pi <= 4`, and `j < 8` to obtain `|a_j| <= 1/4`.
The identity `cos(2*a) = 1-2*sin(a)^2`, together with
`|sin(a)| <= |a|`, gives

```
cos(2*a_j) >= 7/8,
Re(A) >= 7/8,
p_0(phi) = |A|^2 >= 49/64 > 1/2.
```

The actual output state is normalized. Parseval's identity and nonnegative
Born weights bound the probability of the success event, which excludes
zero, by `1-p_0(phi)`. Thus it is strictly less than
`1/2 = 1-epsilon`.

`ClassicalPhaseCounterexample.zero_amplitudeE` identifies the actual
phase-estimation amplitude with this periodic sum; `zero_amplitude_real`
and `zero_probability_gt_half` prove the estimates.
`ordinary_success_below_half` bounds the full printed success event, and
`printed_phase_bound_counterexample` combines the valid phase range with
the negation of its claimed lower bound. The complement step is checked
in `ClassicalPhaseProbability.onb_event_complement_bound`. The final
counterexample has no hypotheses. The explicit source constants are
`n=1`, `epsilon=1/2`, and `t=3`; the logarithm/ceiling calculation above
is documented arithmetic rather than a formalized precision-selection API.
See `PHASE-COUNTEREXAMPLE-NOTES.md` for the prior argument and theorem map.

The standard phase-estimation guarantee uses circular distance
`min(|phi-m/N|, 1-|phi-m/N|)`. An alternative ordinary-distance theorem
needs an explicit boundary condition that rules out wraparound. In the
order-finding application, nonzero phases `s/r` lie at least `1/r` from both
endpoints, so an appropriate boundary lemma can reconnect the circular
estimate to ordinary rational approximation there. This mathematical repair
must be distinguished from proving Lemma 7.1 literally as printed.

## C7. Order-finding postprocessing selects the wrong denominator

**Location:** page 38, Section 7.4 definition of `f`, and page 39 claim that
`f(k/2^t)=r` whenever `gcd(s,r)=1` and `k` belongs to `K_s`. The definition
was checked in the rendered page 38: it explicitly says to return the
**minimal** denominator among all continued-fraction convergents satisfying
`|m/n-x| < 1/(2n²)`. There is no modular-order test in that selection.

**Status:** counterexample established; a repaired postprocessing algorithm
requires user approval before its correctness is formalized. Independent
spectral and circuit identities can proceed.

Take modulus 15, multiplier 2, and order `r=4`. Choose `s=1`, coprime to 4,
and a measured dyadic value `k/2^t=1/4` (every `t>=2` permits it). This value
belongs to `K_s` with approximation error zero, but its continued fraction
has convergent `0/1`, whose error `1/4` is strictly smaller than `1/(2*1²)`.
Thus the printed algorithm returns denominator 1, not 4. Even excluding the
zero numerator is insufficient in general: for exact phase `3/4`, convergent
`1/1` has error `1/4<1/2`, so the minimal selected denominator is again 1.

In fact the ideal order-finding circuit for this example produces only
`0,1/4,1/2,3/4`, with equal probabilities. The printed rule returns 1 at
`0,1/4,3/4` and 2 at `1/2`, so it never returns the true order 4, contradicting
the positive success bound in Equation (18).

A standard repair is to enumerate suitable convergent denominators under a
known bound and retain a denominator only when modular exponentiation verifies
`2^n mod 15 = 1` (generally `x^n mod N = 1`), choosing the least verified
candidate. Its correctness and denominator-bound conditions require an actual
continued-fraction theorem; merely replacing the printed `f` by a function
assumed to return the order would hide the target claim. The repaired function
also needs an explicit failure result when no verified candidate is found.

Checked counterexample support is now in `shor_arithmetic.v`: the literal
selector returns 1 at both 1/4 and 3/4 (`printed_quarter_counterexample`,
`printed_three_quarters_counterexample`), while `two_mod_fifteen_order` proves
that the order of 2 modulo 15 is 4. `convergents_stable` justifies the finite
Euclidean recursion bound. No repaired selector is used.

## Explicit maximal computations (Definition 4.1, pp. 16–17)

The existing operational sum uses successful finite routes. To also represent
the paper's computations themselves, configurations retain an optional residual
command, a classical store, and the unnormalized quantum operator. A lifted
step carries an actual Table-2 step witness and requires its destination
operator to be nonzero, exactly as in the rendered Definition 4.1. A finite
computation is a finite path whose endpoint has no such outgoing transition; this includes successful
termination and abort or blocked residual commands. An infinite computation
is a natural-number-indexed path with a step at every index, hence has no
finite terminal endpoint. This definition imposes no probability or fairness
condition on an individual path.

Induction over a finite path proves positivity, density preservation and
trace nonincrease from the corresponding one-step theorems. The same induction
on a prefix index applies to every infinite path. Unfolding a true-guard Skip
loop and completing its Skip body alternate forever; this supplies an actual
infinite computation, independently of its already-proved zero denotation.
Successful paths with nonzero output coincide with the existing `terminates`
relation restricted to nonzero output: quantum maps preserve zero, so a
nonzero endpoint precludes zero at any earlier step. The route sum can retain
zero-output paths harmlessly; every such summand is the zero operator.

Checked in `computations.v`: `ClassicalComputations.live_step`, `path`,
`maximal_path`, `finite_computation`, and `infinite_computation` give the
explicit path types. A raw configuration is physical when `well_formed`;
both computation types require density of the initial configuration, and
`path_density`/`infinite_computation_density` preserve it. `path_trace_le` and
`infinite_path_trace_le` prove trace nonincrease. `successful_maximal_iff`
identifies successful maximal paths with `terminates` and nonzero output;
`successful_route_iff` also connects the existing outcome-labelled routes.
`true_skip_infinite` constructs the alternating divergent computation, while
`abort_computation`, `terminal_none`, and `terminal_zero` cover finite and
zero-state boundaries. No change to the operational sum is required.

### C7: the printed selector never returns an order above two

For any measured rational a/b with 0 <= a < b, the failure is more general
than the quarter-phase example. If 2a<b, the first convergent 0/1 satisfies
the strict approximation test, so the selected minimum denominator is at
most one. If b<2a, then b/a=1 and the second convergent is 1/1; its error
1-a/b is less than one half, again bounding the selected minimum by one.
If 2a=b, the Euclidean continued fraction is exactly [0;2]. Its first
convergent fails the strict test at equality and the second is the exact
rational 1/2, so the selector returns two. This exhausts the measured range.
Consequently the literal printed selector cannot return any order greater
than two at any precision. This is a diagnosis of the printed algorithm,
not an adopted repair. The formal finite-list argument uses that a fold of
minimum is bounded above by every retained denominator.

Checked in `postprocess_counterexample.v`:
`ClassicalPostprocessCounterexample.printed_denominator_at_most_two` proves
the general bound for every rational in the measured range, and
`printed_never_four` rules out the true order in the modulus-15 example at
every precision. The proof uses only finite arithmetic and lists.
