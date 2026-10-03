# Hoare rules and relative completeness

Source: classical.pdf, Table 4 (printed page 16:26) and Section 5.2
(the total-correctness AbortT rule on 16:28). `CQRules.derives` is the full
independent inductive inference relation, covering every core constructor,
including conditional and partial/total loop rules. `CQHoare.derives`
preserves the initial structural subsystem. Primitive rules use their explicit
dual-operation preconditions; `primitive.v` proves the substitution, weighted
random sum, Kraus measurement, initialization, and unitary formulas. Neither
system has a constructor assuming arbitrary semantic correctness.
Following the user's approved repair
on 2026-10-03, this inference system works over all effect-valued semantic
assertions. The exact countable-image/definable-fiber paper assertions embed
through their value-function coercion, so one common inference system
serves both domains.
The current assertions share the fixed global quantum-memory space;
the paper's comparison of assertions on differing variable sets is not
yet a separate local-space interface.

The state transformer is the arbitrary-state kernel action, and sequential
composition uses the proved kernel-action composition theorem. Total
validity is the paper's expectation inequality. Partial validity is stored
in the equivalent complement form used in upstream CoqQ:

    Exp(output, I-Q) <= Exp(input, I-P).

Absolute convergence proves Exp(rho,I-P)=Tr(rho)-Exp(rho,P), so this is
exactly Exp(input,P) <= Exp(output,Q)+Tr(input)-Tr(output).
`valid_partial_loss` records the equivalence.

To connect this transformer explicitly to terminating executions, expand
its value at an output store as the absolutely convergent sum over input
stores (`CQKernel.applyE`). Each input component is positive, so the
single-input route/denotation theorem applies to that summand. Substitution
therefore gives the iterated sum of terminating-route outputs over all
input stores, retaining the route indices inside each inner sum. This is
`run_operational`; no finite-support assumption or interchange of an
unjustified sum is required.

Soundness of Skip is identity action. Abort action is the zero state;
its post-expectation is zero, while total AbortT additionally has zero
pre-expectation. Seq chains the two total inequalities in the forward
direction, or the complement inequalities in the reverse direction.
For Imp, trace-pairing monotonicity strengthens the precondition and
weakens the postcondition; complement reverses operator order. Thus
induction on a derivation proves `derives_sound` without any constructor
that inserts an arbitrary semantically valid judgment.

The full extension in `rules.v` proves total and partial soundness and relative
completeness for the implemented core syntax over the approved effect-valued
domain. It does not assert the false limit-closure claim for the paper's
countable-image/definable-fiber subclass, nor completeness of that subclass.

The primitive assignment bridge uses an explicit convergence argument.
For any kernel K, effect family Q and input state rho, write
F(i,j)=Tr(Q(j) K(i,j)(rho(i))). Positivity and the effect bound give
|F(i,j)| <= ||K(i,j)(rho(i))||_1. Every finite rectangle is consequently
bounded by the input state's total trace norm, using `rectangle_bound`.
The absolute Fubini theorem therefore permits exchanging the two sums;
linearity and continuity of trace pairing permit moving each pairing
through its input sum. For a deterministic update kernel, all output
terms except j=update(i) vanish. This proves `expect_sunit` without a
finite-memory restriction. Classical assignment has identity quantum
operation, so a pointwise substitution equation between the supplied
pre/post assertion records gives its total-validity axiom. Lost trace is
nonnegative by `apply_mass`, which also proves partial validity.

## Assumption audit

On 2026-10-03, `Print Assumptions` was checked by direct compilation with
Rocq 9.1 for `expect_apply_sum`, `valid_assign_total`, `derives_sound`,
`abort_not_total_top`, and `CQAssertion.semantic_omega_cpo`. The common
foundations are `ClassicalDedekindReals.sig_not_dec`,
`ClassicalDedekindReals.sig_forall_dec`, `boolp.propositional_extensionality`,
`boolp.functional_extensionality_dep`,
`FunctionalExtensionality.functional_extensionality_dep`,
`Epsilon.epsilon_statement`, and `boolp.constructive_indefinite_description`.
These are the inherited classical real-number, choice, and extensionality
foundations. The concrete command theorems additionally depend on
`qreg.G : context`, the existing finite map assigning quantum variable types
in `src/qreg.v`; it is an explicit model parameter, not a correctness axiom.
The generic Fubini theorem and semantic assertion CPO theorem do not depend
on `qreg.G`. No new axioms or admitted obligations occur in these results.

The later full-core audit also checked `CQRules.valid_while_total`,
`loop_ranking`, `derives_sound`, `derives_complete`, `sound_complete`,
`CQKernelLimits.unroll_apply_cvg`,
`CQExpectationLimits.expect_semantic_sup`, `CQAssertionSeries.expect_series`,
and `CQPredicate.wp_sdlet`. All nine completed `Print Assumptions` checks
have exactly the inherited foundations listed above, with `qreg.G` only for
the six concrete command/loop results. In particular, neither soundness nor
completeness has a new theorem axiom or an unproved program-correctness premise.

## Predicate transformers and loop rules

For a summable completely positive kernel `K`, define
`wp(K,Q)(i) = sum_j K(i,j)^*(Q(j))` and
`wlp(K,Q) = I - wp(K,I-Q)`. The sum is well-defined even on the unbounded
classical store. Every summand is positive. Its finite partial sums are
bounded above by `(sum_j K(i,j))^*(I) <= I`, since each `Q(j) <= I`
and every finite row sum is trace nonincreasing. Positive operators have
trace norm equal to trace, so every finite sum of term norms is at most
`Tr(I)`. Absolute summability follows. The closed positive cone and closed
interval `[0,I]` then place the sum in the effect domain.

Trace pairing commutes with this absolutely convergent sum. The previously
proved absolute Fubini theorem exchanges input/output indices, yielding
`Exp(rho,wp(K,Q)) = Exp(K(rho),Q)`. Complementation gives the liberal
equation with lost trace. Testing on all singleton states shows that total
validity is exactly `P <= wp(K,Q)` and partial validity exactly
`P <= wlp(K,Q)`. These are characterization theorems, not inference rules:
derivability still uses the independently inductive paper rules.

The loop proof follows Table 3 and Definition 5.2. Increasing finite
unrollings converge to the kernel loop denotation; expectation continuity
therefore identifies their weakest preconditions with the least fixed point.
Complementation supplies the liberal greatest fixed point. Partial loop
soundness follows by induction that an invariant is below every descending
liberal approximant. For total correctness, a decreasing ranking sequence
`R_n` has infimum zero, covers the invariant at `n=0`, and satisfies
`b /\ wp(body,R_n) <= R_(n+1)`. Induction bounds the invariant by the sum
of `R_n` and the total finite-unrolling precondition. Taking limits proves
the total loop rule. Completeness uses the loop's weakest precondition as
invariant and the remaining termination effects after `n` iterations as
ranking assertions; their expectations are the difference between the
full and finite-unrolling termination masses, which decreases to zero.
The checked results are `CQPredicate.term_summable`, `wp_effect`, `expect_wp`,
`expect_wlp`, and the primitive/sequence/conditional equations;
`CQRules.valid_total_iff`, `valid_partial_iff`, `wp_unroll_sup`,
`wp_unroll_cvg`, `wlp_unroll_cvg`, `valid_while_partial`,
`valid_while_total`, `tail_effect`, and `loop_ranking`. Structural induction
on commands proves `derives_pre`, then consequence gives `derives_complete`.
Induction on the independent derivation proves `derives_sound`.
`sound_complete` combines these directions for either correctness mode.
The record expresses zero infimum as pointwise convergence to zero;
`CQRanking.ranking_infimum` and `ranking_of_infimum` prove equivalence with
the paper's infimum formulation for decreasing effects.

The primitive rules also require respecting merged outcome stores. In a
random assignment or measurement, several branch indices may update to the
same output store. For each output store, move dual evaluation through its
absolutely convergent branch sum. Each surviving term then evaluates the
postcondition at that branch's updated store. The generic reindexing identity
`sdlet_sum` sums these grouped terms without changing their total. Thus
`CQPredicate.wp_sdlet` gives the branch-indexed precondition formula even
when outcome stores coincide. For normalized primitives the row sum is a
channel, so `wp(I)=I`; linearity and complementation imply `wlp=wp`.
`CQPredicate.wp_top`, `wlp_wp`, and `xp_wp` formalize this argument.

## Auxiliary assertion algebra (Table 5)

For a finite family of assertions and nonnegative coefficients, trace linearity
and absolute summability of each expectation interchange the finite sum and
store sum. Hence the expectation of a supplied effect-valued weighted sum is
the corresponding weighted sum of expectations. Total-validity inequalities
can be added with arbitrary nonnegative coefficients provided both resulting
assertions are effects. Partial validity instead adds one lost-trace term for
each coefficient: their total is at most the single allowed lost-trace term
when the coefficient sum is at most one. This explains that explicit condition
in Theorem 6.1; it is not a condition on total correctness.

For Disj and disjoint Sum, use the weakest-precondition characterization
pointwise. At each store select the applicable premise (or the zero lower
bound). No distributivity property of the noncommutative operator order is
needed. For increasing preconditions with a common postcondition, each is
bounded by the same weakest precondition, hence their supremum is bounded too.
The derived-rule conclusions use the independent core completeness theorem
after semantic soundness has been proved. Named Top, Bot and Disj
derivations are in `CQAuxiliary`; `CQAuxiliaryDerivations.derives_sum`,
`derives_linear_total` and `derives_linear_partial` expose the remaining
finite rules. `derives_series_total` and `derives_series_partial` expose the
corresponding countable rules below.

For countably many nonnegative summands, the same Linear rule requires the
operator series defining the resulting assertions to converge at every store.
A finite partial sum is below its full positive sum. Therefore any finite
rectangle of weighted trace pairings is bounded by the input state's total
trace, since the resulting pre/post assertion is an effect. Absolute Fubini
then exchanges the assertion index and store index. This proves countable
linearity without requiring the coefficient family itself to be summable for
total correctness. Partial correctness retains the summable coefficient and
sum-at-most-one condition needed to bound its accumulated lost trace.

The mapped audit of the five `CQAuxiliaryDerivations` Sum/Linear/series
corollaries reports only inherited classical real-model, choice and
extensionality foundations and the existing `qreg.G` memory parameter.

For Lemma 4.16(3), the dual-kernel row for a finite linear combination of
effect assertions is the same finite linear combination of the individual
dual-kernel rows. Each row is absolutely summable. Finite linearity of the
sum therefore proves linearity of wp, even for arbitrary scalar coefficients
provided the displayed combined assertion is an effect. For (4), complement
distributes across an affine combination because the coefficients sum to
one. The defining identity wlp(Q) = I - wp(I-Q) and wp linearity then give
the stated affine law. No extra sign hypothesis is needed for this algebraic
identity beyond the supplied effect well-formedness.

For the equality case of Lemma 4.16(5), an external unital map F fixes the
program's lost-trace effect L = I - wp(I), by the checked `loss_unital`
commutation argument. Writing wlp(Q) = L + wp(Q), wp commutation and
linearity yield wlp(F(Q)) = F(wlp(Q)). The rectangular square extension
also preserves the identity when its original V-to-W map does: apply the
already proved cylinder equation to I_V, whose cylindrical lift is I_U.
This gives the equality case for literal space-changing maps as well.

Checked in `CQPredicateAlgebra`: `wp_finite_linear`, `wlp_finite_affine`,
and `wlp_image_unital` give the finite algebraic laws and unital equality.
`square_extension_unital` transfers unitality to the explicit square
extension, and `wp_cross`, `wlp_cross_le`, and `wlp_cross_unital` give the
rectangular-map forms of Lemma 4.16(5).

The mapped audit of the six main algebraic/commutation theorems reports only
the inherited classical real-model, choice and extensionality foundations,
and `qreg.G` for the concrete-memory theorems.

## Quantum locality and SupOper

The quantum frame premise is the language's syntactic disjointness condition:
the external operation's register set is disjoint from `quantum_variables c`.
For each primitive, cylindrical extension of maps on disjoint registers
commutes, including on entangled states. Classical assignment acts as identity
on quantum data and random assignment scales that identity. Summable branch
grouping and sequential kernel composition preserve commutation by continuity
and absolute summability. Conditional selection preserves it pointwise.
Finite loop unrollings therefore commute, and continuity passes the equation
to the unbounded loop denotation. Taking duals yields commutation of the
weakest-precondition transformer with an external assertion operation.
Thus total SupOper follows by applying its positive map to the original
precondition inequality; commutation is derived from syntax, not assumed as
an extra program-correctness premise.

Partial SupOper needs an additional lost-trace argument because its external
map is only sub-unital. Complete an external CP sub-unital map F to a unital
CP map F+G: positivity of I-F(I) gives a factor g with
I-F(I)=g g*, so take G(X)=g X g*. The termination-defect effect
L=I-wp(c,I) is fixed by every unital external map, since such maps commute
with wp and preserve I. Hence F(L)+G(L)=L. Positivity of G gives F(L)<=L.
Applying F to the original liberal-precondition bound now proves the partial
rule. This handles divergence without assuming the program terminates or
that F itself is unital.

The initial formal interface acts on the fixed ambient quantum memory through
cylindrical extension. The paper's literal V-to-W SupOper now has its explicit
rectangular map and tensor action in `CQQuantumCrossSpace`; see
`CROSS-SPACE-NOTES.md`. The local-space embedding equations for tensor
extension and normalized partial trace are checked in `CQQuantumSpaceRules`
and `CQQuantumTrace`; see `QUANTUM-SPACE-NOTES.md`.

Checked in `CQQuantumFrame`: `denote_disjoint_commute` proves the concrete
kernel commutation theorem for every source command; `wp_external` transfers
it to arbitrary supplied effect-valued image assertions. `subunital_completion`,
`loss_unital`, and `loss_subunital` establish the partial-correctness defect
bound. `valid_supoper` and `derives_supoper` prove the ambient SupOper rule in
both correctness modes. These results have no assumed kernel commutation or
termination premise.

### Independence from unused finite quantum memory

Fix any unused register set T inside the inherited finite ambient memory.
The normalized depolarizer on T sends an arbitrary operator rho to
lift(tr_T(rho))/dim(T), including entangled inputs. Each source-kernel branch
commutes with this map by the checked syntactic locality theorem. Cancelling
the strictly positive dimension factor proves
lift(tr_T(E(rho))) = E(lift(tr_T(rho))). Injectivity of cylinder lifting then
shows that equal retained marginals produce equal retained output marginals.
Continuity of partial trace and absolute summability extend the result from
one input store to arbitrary cq-inputs. For product inputs A tensor B, the
same depolarizer identity gives tr_T(A tensor B) = tr(B) A, so every normalized
unused-memory extension has the same retained behavior.

This concerns every subsystem of the arbitrary finite `DefaultQMem` universe,
without independence or separability assumptions on input states. A theorem
between two different memory contexts with a supplied variable embedding is
a distinct construction and is not claimed by this result.

Checked in `CQMemoryExtension`: `denote_partial_trace`,
`denote_marginal_ext`, and `apply_marginal_ext` establish branch and cq-input
locality; `partial_trace_product` and `normalized_memory_extension` establish
the explicit tensor-extension equation and normalized-ancilla independence.

## Classical store locality

A primitive step changes only its assigned classical variable; measurement
and sampling have the same store update. For sequential execution and branch
selection, every remaining write is already in the source command's write
set. Induction on a terminating computation consequently shows that every
variable outside the original write set has its initial value at termination.
Route soundness transfers this property to each successful operational route.
If a predicate reads only such variables, every route preserves its truth.
The absolutely summable route semantics then shows that filtering by this
predicate commutes with program execution, which proves the classical Inv
rule without assuming finite classical support or bounded loop execution.

Checked auxiliary results in `CQAuxiliary`: `valid_bottom`, `valid_top`,
`valid_disjunction`, `valid_disjoint_sum`, `valid_sup`,
`valid_finite_linear_total`, `valid_finite_linear_partial`,
`valid_series_total`, and `valid_series_partial`. `CQAssertionSeries` proves
`expect_series` and `expect_series_summable` by the rectangle bound above.
`ClassicalLocality` proves `step_remaining_writes`, `step_unchanged`,
`terminates_unchanged`, `route_unchanged`, and
`terminates_preserves_expression`. These targets pass the integrated build.
The Inv rule uses these locality results below. Quantum framing and the
remaining auxiliary derivations are checked in `CQPrimitiveFrame`,
`CQQuantumCrossSpace`, and `CQAuxiliaryDerivations`, with their arguments
recorded in `PRIMITIVE-FRAME-NOTES.md`, `CROSS-SPACE-NOTES.md`, and this note.

`CQInvariant.denote_expression_zero` transfers store locality through the
complete route sum, `wp_guard_agree` transfers it through the dual kernel,
and `valid_invariant` / `derives_invariant` prove Table-5 Inv for both
correctness modes. The integrated `invariant.vo` target passes.
# Classical ranking argument (Table 5, C-WhileT)

The argument uses induction on the initial nonnegative rank, not a bound on
small-step execution time. Write `p` for a classical predicate supporting the
invariant effect `P`. For each rank value `k`, the body premise guarantees
total probability of reaching a store either outside `p` or with smaller
rank. A total-correctness assertion with classical postcondition `g` and
identity precondition implies `wp(body, g I) = I`. Positivity and
sub-unitality then give `wp(body, (not g) I) = 0`; by monotonicity the same
zero equation holds with any effect in place of `I`. Consequently masking
the invariant by `g` does not change its body precondition.

Assume the desired loop precondition bound at all smaller ranks. On an
output in `p` the decrease premise permits that induction hypothesis; on an
output outside `p` the invariant effect is zero. Body monotonicity and the
invariant premise therefore give the desired bound at the current input.
When the guard is false the loop fixed-point equation gives the invariant
itself. This proves total correctness without excluding probability-zero
infinite paths in a body and without assuming a uniform runtime bound. The
family indexed by rank values is the explicit semantic version of the
paper's fresh classical ghost variable. `CQClassicalRanking.wp_certain_mask`
and `valid_classical_while` formalize the probability-one masking and rank
induction. `valid_integer_while` and `derives_integer_while` give the signed
integer version and the derived inference rule. The reduction from the
paper's single fresh-ghost-variable premise to this explicit family is proved
by `CQGhostRanking.valid_fresh_integer_while` and
`derives_fresh_integer_while`, as detailed below.

# Assertion locality and existential elimination

Agreement of two typed memories on a set `X` is preserved when both receive
the same typed update. Every expression whose support is included in `X`
has equal values in such memories, by `ClassicalFootprint.eval_local`.
Induction on commands therefore shows that their predicate transformers
preserve locality on any `X` containing the command variables. Random and
measurement branches use the same outcomes and equal branch weights/maps;
their updated postconditions agree term by term. Sequential composition
uses locality of the intermediate precondition. For a while loop, induction
first proves locality of every finite unrolling, and uniqueness of the
already checked wp/wlp limits proves locality of the actual loop.

Taking `X` to omit one fresh classical name yields invariance under changing
that variable. Thus a witness for `exists x.p` may be installed into the
initial memory without changing the program precondition or an x-independent
postcondition. Applying the premise at that modified memory proves Exist.
`CQAssertionLocality.pre_local`, `valid_exist`, and `derives_exist` check this
argument for both total and partial correctness, including unbounded loops.
The same locality fact permits instantiating a fresh integer ghost with the
current rank, providing the link to the rank-family formulation above.

For the fresh-ghost bridge, fix an integer `k`. Apply the already proved
classical invariant rule to the predicate `z=k`; the body cannot write `z`.
Its premise and conclusion then imply respectively `b /\ p /\ t=k /\ z=k`
and `t<k`. The latter assertion and the command are independent of `z`, so
Exist removes `z=k` from the precondition: use the witness `k`, with expression
locality ensuring that this update preserves `b`, `p`, and `t`. This supplies
every member of the signed-rank family and hence the printed C-WhileT rule.
This derivation requires no assumed substitution or whole-program theorem.

## Simultaneous bounded unrolling of nested loops

For a natural number `k`, recursively preserve every primitive and classical
branch, recurse into both sequential components, and replace `while b do c`
by `k` unrollings of `b` with recursively approximated body `c`. Every such
syntax tree is loop-free; it is used only as an approximant, not as a
replacement semantics. Increasing `k` increases its completely positive
kernel, and every approximant is bounded by the actual command kernel.

Sequential composition is monotone by composition of positive maps and
absolute summability of each kernel column. Its continuity is the inherited
`slet_lim` theorem. For a loop, fix an outer depth `r`: continuity of sequential
composition proves that the limit over body approximations of its `r`-fold
unrolling is the `r`-fold unrolling of the limiting body. For each body index
`k`, choose `j=max(k,r)`. Monotonicity in both body and outer depth bounds this
term by diagonal approximant `j`. Taking limits first in the body index and
then in `r` proves that the actual loop is below the diagonal limit. The
reverse inequality follows from the uniform kernel upper bound. Thus the
simultaneous finite approximants converge to the full nested-loop semantics,
also after composition with any fixed continuation.

## Probabilistic composition and quantum support

For Table 5 (ProbComp), fix a classical input satisfying the first precondition
and an arbitrary partial density operator. Total correctness of the first
command gives `input trace <= expectation(p and P) <= output trace <= input
trace`, where P is the projector onto the asserted pure state on the selected
registers (tensored with identity on the remaining memory). Thus every bound
is an equality. The complementary expectation is a sum of nonnegative terms
with value zero, so each term vanishes. For each output store its density has
support in the asserted projector; outside p that projector is zero.

If M is the second command's asserted effect and `P M P = a P`, support gives
`tr(M rho) = a tr(rho)` for every output component. Absolute summability lets
this equality pass through the sum over output stores. The second correctness
premise then gives success at least a times the input trace. Finally use the
point-state characterization of effect order to obtain the program rule on
arbitrary cq-states. For a local normalized vector psi, its rank-one projector
satisfies `P M P = <psi,M psi> P`; this argument permits entanglement with
untouched memory and does not falsely identify the whole output density with
a scalar multiple of a rank-one projector on the full memory.

Checked implementation: `CQProbabilisticComposition` proves
`projection_saturated_support`, `supported_pairing`, `saturated_expectation`,
and the general `valid_probcomp_projection`/`derives_probcomp_projection`.
`CQProbabilisticPure.valid_probcomp` and `.derives_probcomp` instantiate the
printed total-correctness rule on a physical register. `pure_success_effectE`
identifies the initial scalar effect as `<psi,M psi> I`.

The fresh audits of the simultaneous-unrolling limits, the general and
pure-register ProbComp rules, and the finite local/global comparison report
only the inherited classical foundations and the existing `qreg.G` model
parameter. Their logs are `composition_local_assumptions.log` and
`probcomp_assumptions.log` under `/private/tmp/coqq-assertion-check/`.
