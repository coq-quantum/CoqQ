# Increasing ranking assertions: Rep-T′ and Dist-T′

Source: `distributive.pdf`, Definition 5.9 on PDF p. 21, Table 3 and the
displayed Rep-T′ rule on PDF p. 22. Both rendered pages were inspected.
The paper describes Dist-T′ immediately after the display as the analogous
distributed rule. In the third premise of the Rep-T′ display, the body is
printed as S; the branch bodies bound by the rule are S_i. We use S_i for
that indexed premise, consistently with Definition 5.9 and the first
premise. This resolves an unbound notation rather than changing the rule.

Let Psi_k be an increasing sequence of effects with supremum top, and put
R_k=top-Psi_k pointwise in the classical store. Complement reverses the
effect order, so R is decreasing. Since finite-dimensional monotone effect
sequences converge to their supremum, continuity of subtraction implies
R_k converges pointwise to zero. Conversely, if R is decreasing and tends
pointwise to zero, its complements increase and converge to top; uniqueness
of the monotone effect limit identifies their supremum with top.
The initial condition P<=top-Psi_0 is precisely P<=R_0.

For any guard B and command c, partial correctness of

    {B and Psi_(k+1)} c {Psi_k}

is equivalent to the guarded inequality

    B and wp(c, top-Psi_k) <= top-Psi_(k+1).

At stores satisfying B this is the wp/wlp complement identity and order
reversal; at other stores the inequality is the lower bound zero of an
effect. These are exactly the decreasing-ranking step conditions in
Definition 5.9. The existing partial proof system is sound and relatively
complete, so the equivalence also holds when the displayed partial triples
are required to have derivations in that existing system.

Apply this argument independently to every repetitive branch. An increasing
ranking therefore supplies the existing `DistributedGuardedRules.ranking`,
and the existing total repetition constructor yields Rep-T′. Conversely,
complementing any such decreasing ranking gives the increasing witnesses
and partial branch derivations. No new constructor of the proof system is
introduced.

For a distributed network, apply the same argument independently to every
entry in the actual rendezvous-command list, including each communication
effect and the two local bodies. The initialization derivation, global
invariant preservation premises, and blocked-implies-terminated side
condition of Dist-T remain required. Converting the increasing witnesses
to `network_ranking` then permits the existing total distributed constructor
to derive Dist-T′. The operational soundness theorem already proved for
that independent constructor applies unchanged.

The checked `DistributedRankingComplement` module in `ranking_complement.v`
provides `repetition_ranking_of_partial` and `list_ranking_of_partial`,
the equivalences `repetition_ranking_iff_partial`,
`repetition_ranking_iff_derivable`,
`repetition_ranking_iff_guarded_derivable`, `list_ranking_iff_partial`,
`list_ranking_iff_derivable`, and `network_ranking_iff_derivable`.
The guarded-system equivalence requires the existing well-formedness
condition on branch statements; the classical translated-branch equivalence
does not need this extra premise.

The named derived rules are `derives_repetition_total_prime` (Rep-T′) and
`derives_distributed_total_prime` (Dist-T′). Their `repetition_total_prime`
and `distributed_total_prime` corollaries state validity for the independent
local and distributed execution semantics. Focused Rocq 9.1 compilation and
qualified Dune integration succeeded. The seven-result assumptions audit
reports only inherited real/classical foundations and the existing `qreg.G`
memory parameter; no new axiom is introduced.
The generic complement and convergence helpers are reused from
`classical/ranking_complement.v`; neither core rule system is modified.
