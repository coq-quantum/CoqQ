(* Bounded operational completions, Lemma 4.2. See OPERATIONAL-APPROXIMANTS-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.



From quantum.example.classical Require Import operational_route_cost operational_approximants.

Module ClassicalOperationalCompletions.
Import ClassicalLanguage ClassicalOperational ClassicalOperationalRouteCost
  ClassicalOperationalApproximants CQState.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Section Completions.
Variable c : command.
Variable s : store.
Variable rho : 'FD(Hq).

Lemma selected_route_nonzero (p : pred route) rt t (x : 'End(Hq)) :
  p rt -> eval_route rt c (s,(rho : 'End(Hq))) = Some (t,x) -> x != 0 ->
  suppf (selected_family c s rho p) rt.
Proof.
move=>Hp He Hx.
rewrite /suppf /selected_family /= /selected_term Hp /opfun He.
apply/negP=>/eqP Hz.
have Z := congr1 (fun f : {summable store -> 'End(Hq)} => `|f|) Hz.
move: Z; rewrite sunit_normE normr0=>/eqP.
by rewrite normr_eq0 (negbTE Hx).
Qed.

Theorem selected_outcomes_countable (p : pred route) :
  countable [set o : store * 'End(Hq) |
    exists rt, p rt /\ eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0].
Proof.
pose out rt := odflt (s,(0 : 'End(Hq))) (eval_route rt c (s,(rho : 'End(Hq)))).
have Sub : [set o : store * 'End(Hq) |
    exists rt, p rt /\ eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0]
    `<=` out @` suppf (selected_family c s rho p).
  move=>[t x] [rt [Hp [He Hx]]]; exists rt.
  - exact: selected_route_nonzero Hp He Hx.
  - by rewrite /out He.
apply: (sub_countable (subset_card_le Sub)).
apply: (sub_countable (card_image_le out _)).
exact: selected_routes_countable.
Qed.

Theorem exact_completions_countable n :
  countable [set o : store * 'End(Hq) |
    inhabited (counted_terminates n c s rho o.1 o.2) /\ o.2 != 0].
Proof.
apply: (sub_countable (B := [set o : store * 'End(Hq) |
    exists rt, (route_cost rt == n) /\
      eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0])).
- apply: subset_card_le.
  move=>o Ho; case: o Ho=>t x /= [[d] Hx].
  have [rt [He Hcost]] := counted_terminating_route d.
  by exists rt; split; [apply/eqP | split].
- exact: selected_outcomes_countable.
Qed.

Theorem bounded_completions_countable n :
  countable [set o : store * 'End(Hq) |
    (exists k, (k <= n)%N /\ inhabited (counted_terminates k c s rho o.1 o.2)) /\ o.2 != 0].
Proof.
apply: (sub_countable (B := [set o : store * 'End(Hq) |
    exists rt, (route_cost rt <= n)%N /\
      eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0])).
- apply: subset_card_le.
  move=>o Ho; case: o Ho=>t x /= [[k [Hk [d]]] Hx].
  have [rt [He Hcost]] := counted_terminating_route d.
  exists rt; split; [by rewrite Hcost | by split].
- exact: selected_outcomes_countable.
Qed.

Definition bounded_completion n : state := completion_state c s rho route_cost n.

Theorem bounded_completionE n m : bounded_completion n m =
  sum (fun rt => if (route_cost rt <= n)%N then opfun c s rho rt m else 0).
Proof.
rewrite /bounded_completion /completion_state selected_stateE.
by apply: eq_sum=>rt; rewrite /within ltnS.
Qed.

Theorem bounded_completion_zero : bounded_completion 0 = bottom.
Proof.
apply/vdistrP=>m; rewrite bounded_completionE bottomE.
under eq_sum do rewrite leqn0 (gtn_eqF (route_cost_positive _)).
exact: summable_sum_cst0.
Qed.

Theorem bounded_completion_chain : nondecreasing_seq bounded_completion.
Proof. exact: completion_state_chain. Qed.

Theorem bounded_completion_countable n : countable (suppf (bounded_completion n)).
Proof. exact: support_countable. Qed.

Theorem bounded_completion_mass n : mass (bounded_completion n) <= \Tr rho.
Proof. exact: selected_mass_bound. Qed.

Theorem bounded_completion_cvg :
  ((fun n => (bounded_completion n : {summable store -> 'End(Hq)})) @ \oo --> opsum c s rho)%classic.
Proof. exact: completion_state_cvg. Qed.

Theorem bounded_completion_sup :
  chain_sup bounded_completion = CQKernel.apply (denote c) (point s rho).
Proof. exact: completion_state_denote. Qed.

Theorem bounded_completion_upper n :
  bounded_completion n ⊑ CQKernel.apply (denote c) (point s rho).
Proof.
rewrite -bounded_completion_sup.
exact: (@chain_sup_upper cmem Hq bounded_completion bounded_completion_chain n).
Qed.

Theorem bounded_completion_least (d : state) :
  (forall n, bounded_completion n ⊑ d) ->
  CQKernel.apply (denote c) (point s rho) ⊑ d.
Proof.
rewrite -bounded_completion_sup.
exact: (@chain_sup_least cmem Hq bounded_completion d bounded_completion_chain).
Qed.

End Completions.
End ClassicalOperationalCompletions.
