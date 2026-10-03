(* Finite operational horizons as effects; see the D5 completeness argument. *)
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
From Stdlib Require List.
From quantum.example.distributive Require Import language operational sequentialization guarded_rules.
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


From quantum.example.distributive Require Import distribution weighted local_actions progress residual_semantics local_correspondence.

From quantum.example.distributive Require Import local_iterations serial_scheduler serial_invariant scheduler_semantics global_value residual scheduler.

From quantum.example.distributive Require Import local_lower.

From quantum.example.distributive Require Import active_lower control_completion network_lower serial_upper scheduler_results.

From quantum.example.distributive Require Import global_instruments global_actions instruments observables local_diamond results.

From quantum.example.classical Require Import mixture mixture_expectation.
From quantum.example.distributive Require Import global_predicate.

From quantum.example.distributive Require Import horizon_expectation.

From quantum.example.distributive Require Import horizon_remainder rendezvous_all correspondence normalized_tests.

Module DistributedHorizonEffects.
Import DistributedLanguage DistributedOperational DistributedDistribution
  DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions
  DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate
  DistributedHorizonExpectation DistributedHorizonRemainder DistributedObservables
  DistributedSerialScheduler DistributedSerialInvariant DistributedResidualSemantics
  DistributedCorrespondence DistributedAllRendezvous DistributedNormalizedTests
  CQAssertion CQPredicate CQExpectationLimits.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Effects.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable Q : assertion.

Definition tail_assertion := wp (CL.denote (network_tail p)) Q.
Definition horizon_assertion k := @horizon_pre P k Q (fun i => idle_control (p i)).

Lemma idle_value_expect rho0 m rho : rho0 \is den1lf -> rho \is den1lf ->
  expect Q (@value P rho0 (idle_configuration p m rho)) =
  \Tr (tail_assertion m \o rho).
Proof.
move=>Hr0 Hr.
have Hinv := @idle_serial_invariant P m rho Hr.
rewrite -(@residual_value P rho0 Hr0 _ Hinv) /residual_state /=.
case: asboolP=>[Hd|Hd]; last by exfalso; apply: Hd; exact: den1lf_den Hr.
rewrite (residual_idle p (idle_ready p)) -expect_wp CQExpectation.expect_point.
by [].
Qed.

Lemma horizon_assertion_pairing rho0 k m rho : rho \is den1lf ->
  \Tr (horizon_assertion k m \o rho) =
  expect Q (@approximant P rho0 k (idle_configuration p m rho)).
Proof.
move=>Hr; exact: (@horizon_pre_observe P rho0 k Q (idle_configuration p m rho)
  Hr (idle_owned p m rho)).
Qed.

Lemma horizon_assertion_mono : semantic_chain horizon_assertion.
Proof.
move=>k m; apply: operator_le_normalized=>rho.
rewrite !(@horizon_assertion_pairing rho _ m rho (is_den1lf rho)).
apply: expect_state_mono.
exact: (@approximant_increasing P rho (idle_configuration p m rho) k k.+1 (leqnSn k)).
Qed.

Lemma horizon_assertion_bound k : semantic_le (horizon_assertion k) tail_assertion.
Proof.
move=>m; apply: operator_le_normalized=>rho.
rewrite (@horizon_assertion_pairing rho k m rho (is_den1lf rho))
  -(@idle_value_expect rho m rho (is_den1lf rho) (is_den1lf rho)).
exact: approximant_expect_le.
Qed.

Lemma horizon_assertion_sup : semantic_sup horizon_assertion = tail_assertion.
Proof.
apply/funext=>m.
have E (rho : 'FD1(Hq)) :
  \Tr (semantic_sup horizon_assertion m \o rho) = \Tr (tail_assertion m \o rho).
  have C1 := @expect_semantic_sup cmem Hq horizon_assertion
    (CQState.point m (rho : 'FD(Hq))) horizon_assertion_mono.
  have C2 := @CQExpectation.expect_chain_sup cmem Hq Q
    (fun k => @approximant P rho k (idle_configuration p m rho))
    (@approximant_increasing P rho (idle_configuration p m rho)).
  have E1 : (fun k => expect (horizon_assertion k) (CQState.point m (rho : 'FD(Hq)))) =
    (fun k => expect Q (@approximant P rho k (idle_configuration p m rho))).
    apply/funext=>k; rewrite CQExpectation.expect_point.
    exact: (@horizon_assertion_pairing rho k m rho (is_den1lf rho)).
  rewrite E1 CQExpectation.expect_point in C1.
  change ((fun k => expect Q (@approximant P rho k (idle_configuration p m rho))) @ \oo -->
    expect Q (@value P rho (idle_configuration p m rho)))%classic in C2.
  rewrite (@idle_value_expect rho m rho (is_den1lf rho) (is_den1lf rho)) in C2.
  exact: (eq_trans (esym (cvg_lim (@norm_hausdorff _ _) C1))
    (cvg_lim (@norm_hausdorff _ _) C2)).
apply/val_inj/eqP; rewrite eq_le; apply/andP; split;
  apply: operator_le_normalized=>rho; by rewrite E.
Qed.

Lemma horizon_assertion_cvg m :
  (horizon_assertion k m : 'End(Hq)) @[k --> \oo] --> (tail_assertion m : 'End(Hq)).
Proof.
rewrite -horizon_assertion_sup.
exact: (@semantic_sup_cvg cmem Hq horizon_assertion horizon_assertion_mono m).
Qed.

Lemma remainder_effect k m :
  ((tail_assertion m : 'End(Hq)) - (horizon_assertion k m : 'End(Hq))) \is obslf.
Proof.
apply/obslf_lefP; split.
- rewrite subv_ge0; exact: horizon_assertion_bound.
- apply: (le_trans (y := (tail_assertion m : 'End(Hq)))); last exact: obsf_le1.
  by rewrite levBlDr levDl; exact: obsf_ge0.
Qed.

Definition remainder_assertion k m : 'FO(Hq) := ObsLf_Build (remainder_effect k m).
Definition rank_assertion k := if k is j.+1 then remainder_assertion j else tail_assertion.

Lemma remainder_assertionE k m : (remainder_assertion k m : 'End(Hq)) =
  (tail_assertion m : 'End(Hq)) - (horizon_assertion k m : 'End(Hq)).
Proof. by []. Qed.

Lemma rank_assertion_decreasing k : semantic_le (rank_assertion k.+1) (rank_assertion k).
Proof.
case: k=>[|k] m.
- rewrite /rank_assertion remainder_assertionE levBlDr levDl; exact: obsf_ge0.
- rewrite /rank_assertion !remainder_assertionE levD2l levN2.
  exact: horizon_assertion_mono k m.
Qed.

Lemma rank_assertion_zero m :
  (rank_assertion k m : 'End(Hq)) @[k --> \oo] --> 0.
Proof.
rewrite -(@cvg_shiftS _ (fun k => (rank_assertion k m : 'End(Hq))) (nbhs 0)).
change ((fun k => (tail_assertion m : 'End(Hq)) -
  (horizon_assertion k m : 'End(Hq))) @ \oo --> 0)%classic.
have C := cvgB (cvg_cst (tail_assertion m : 'End(Hq))) (@horizon_assertion_cvg m).
rewrite subrr in C; exact: C.
Qed.

Lemma remainder_assertion_pairing rho0 k m rho : rho0 \is den1lf -> rho \is den1lf ->
  \Tr (remainder_assertion k m \o rho) =
  @remainder P rho0 Q k (idle_configuration p m rho).
Proof.
move=>Hr0 Hr; rewrite remainder_assertionE linearBl /= linearB /= /remainder
  (@idle_value_expect rho0 m rho Hr0 Hr) (@horizon_assertion_pairing rho0 k m rho Hr).
by [].
Qed.

Lemma rank_assertion_pairing rho0 k m rho : rho0 \is den1lf -> rho \is den1lf ->
  \Tr (rank_assertion k m \o rho) =
  @progress_potential P rho0 Q k (idle_configuration p m rho).
Proof.
move=>Hr0 Hr; case: k=>[|k].
- rewrite /rank_assertion /progress_potential.
  exact: esym (@idle_value_expect rho0 m rho Hr0 Hr).
- exact: (@remainder_assertion_pairing rho0 k m rho Hr0 Hr).
Qed.

End Effects.
End DistributedHorizonEffects.
