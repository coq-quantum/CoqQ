# Complement rankings: classical Lemma 5.4 and WhileT′

Source: `classical.pdf`, PDF pages 29–30, Lemma 5.4 and the displayed
WhileT′ rule. The decreasing ranking definition is Definition 5.2. The
assertion domain here is the already approved full semantic effect domain.

Fix a guard b and body S. For any effect assertions R,T, the guarded ranking
inequality `b ∧ wp(S,R) ≤ T` is equivalent to partial correctness of
`{b ∧ (I−T)} S {I−R}`. At a store satisfying b this is the order-reversing
complement identity `wp(S,R) ≤ T` iff `I−T ≤ I−wp(S,R)`, together with
`wlp(S,I−R)=I−wp(S,R)`. At a store not satisfying b, both respective
guarded inequalities hold because zero is below every effect. This proves
the equivalence without a termination assumption on S.

Given a decreasing zero-limit ranking R_n, put Ψ_n=I−R_n. Complementation
reverses the pointwise operator order, so Ψ_n is increasing. Continuity of
operator subtraction gives Ψ_n→I at each store. The supremum of a monotone
effect sequence is also its operator-norm limit; uniqueness of limits thus
gives `sup Ψ_n=I`. The initial bound becomes `P≤I−Ψ_0`, and the guarded
inequalities become the required partial triples by the preceding identity.

Conversely, take an increasing Ψ_n with supremum I, initial bound
`P≤I−Ψ_0`, and partial triples `{b∧Ψ_(n+1)} S {Ψ_n}`. Put R_n=I−Ψ_n.
Order reversal gives decrease. Monotone effect convergence to the given
supremum, followed by subtraction from I, gives R_n→0. The same guarded
identity converts each partial triple to the ranking step. Thus R_n is an
actual Definition-5.2 ranking, proving both directions of Lemma 5.4.

Finally, for WhileT′, apply soundness to its independent partial derivation
premises, construct the ranking above, and apply the existing independent
`DWhileTotal` constructor to the supplied total invariant derivation. No
semantic-validity constructor or pre-assumed ranking is introduced.

The checked source is `ranking_complement.v`, module `CQRankingComplement`:

- `mask_complement_le_iff` and `guarded_wp_partial_iff` prove the guarded
  complement/partial-triple identity.
- `complement_decreasing`, `complement_sup_top`, and
  `complement_zero_of_sup` prove the sequence order and convergence facts.
- `ranking_of_partial` constructs the decreasing ranking explicitly.
- `ranking_iff_partial` proves both directions of Lemma 5.4, with exactly
  the increasing-sequence, initial-bound, supremum, and partial-triple clauses.
- `derives_while_partial_ranking` derives WhileT′ in the existing independent
  `CQRules.derives` system.

Direct compilation and the six-result assumptions audit passed on 2026-10-03.
The generic complement lemmas use only the inherited classical real, choice,
and extensionality foundations. The command/ranking theorems additionally use
the existing ambient-memory parameter `qreg.G`; no new axiom or admission is
introduced. Integration is recorded in the shared validation record.
