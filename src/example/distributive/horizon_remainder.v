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

Module DistributedHorizonRemainder.
Import DistributedLanguage DistributedOperational DistributedDistribution
  DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions
  DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate
  DistributedHorizonExpectation DistributedObservables CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation C := hermitian.C.

Lemma expect_state_mono (I : choiceType) (H : chsType) (Q : I -> 'FO(H))
    (d e : @CQState.state I H) : d ⊑ e -> expect Q d <= expect Q e.
Proof.
move=>/levdP Hde; rewrite /expect /sum; apply: ler_etlim.
- exact: (summable_cvg (f := Summable.build (expect_summable Q d))).
- exact: (summable_cvg (f := Summable.build (expect_summable Q e))).
- move=>J; rewrite /psum; apply: ler_sum=>i _.
  rewrite /expect_term ![\Tr (Q _ \o _)]lftraceC.
  move: (Hde (val i))=>/lef_psdtr Htrace; apply: Htrace; exact: is_psdlf.
Qed.

Section Remainder.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Variable Q : assertion.
Local Notation V := (@value P rho0).
Local Notation A := (@approximant P rho0).

Definition remainder k c := expect Q (V c) - expect Q (A k c).

Lemma value_global_step c mu (Hs : global_step p c mu)
    (Hr : c.2 \is den1lf) : configuration_owned p c ->
  V c = CQStateMixture.mix (probability_distribution (global_step_probability Hs Hr))
    (fun i => V (branch_value mu i)).
Proof.
move=>Ho; apply/vdistrP=>out; rewrite CQStateMixture.mixE.
have Hp := @ProjectedGlobal P rho0 c mu (conj Hr Ho) Hs.
apply: (eq_trans (@value_bellman P rho0 c _ out Hp)).
by apply: eq_sum=>i; rewrite /= value_collapse.
Qed.

Lemma value_expect_step c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  expect Q (V c) = family_observe mu (fun d => expect Q (V d)).
Proof.
move=>Hs Hr Ho; rewrite (@value_global_step c mu Hs Hr Ho) CQMixtureExpectation.expect_mix.
by apply: eq_sum=>i; rewrite probability_distributionE.
Qed.

Lemma approximant_expect_le k c : expect Q (A k c) <= expect Q (V c).
Proof.
apply: expect_state_mono.
exact: (@CQState.chain_sup_upper cmem Hq (fun j => A j c) (@approximant_increasing P rho0 c) k).
Qed.

Lemma remainder_ge0 k c : 0 <= remainder k c.
Proof. rewrite /remainder subr_ge0; exact: approximant_expect_le. Qed.

Lemma remainder_le1 k c : remainder k c <= 1.
Proof.
apply: (le_trans _ (expect_le1 Q (V c))).
by rewrite /remainder lerBlDr lerDl; exact: expect_ge0.
Qed.

Lemma remainder_bound k c : `|remainder k c| <= 1.
Proof. rewrite ger0_norm ?remainder_ge0 //; exact: remainder_le1. Qed.

Lemma remainder_decreasing k c : remainder k.+1 c <= remainder k c.
Proof.
rewrite /remainder lerD2l lerN2; apply: expect_state_mono.
exact: (@approximant_increasing P rho0 c k k.+1 (leqnSn k)).
Qed.

Lemma remainder_cvg c : remainder k c @[k --> \oo] --> 0.
Proof.
have C := @CQExpectation.expect_chain_sup cmem Hq Q (fun k => A k c)
  (@approximant_increasing P rho0 c).
change ((fun k => expect Q (A k c)) @ \oo --> expect Q (V c))%classic in C.
have D := cvgB (cvg_cst (expect Q (V c))) C.
rewrite subrr in D; exact: D.
Qed.

Lemma remainder_step k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (remainder k) = remainder k.+1 c.
Proof.
move=>Hs Hr Ho.
have Hmu := global_step_probability Hs Hr.
have HV d : `|expect Q (V d)| <= 1 by rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
have HA d : `|expect Q (A k d)| <= 1 by rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
have SV := observe_summable Hmu (ler01 : (0 : C) <= 1) HV.
have SA := observe_summable Hmu (ler01 : (0 : C) <= 1) HA.
change (family_observe mu (fun d => expect Q (V d) - expect Q (A k d)) =
  expect Q (V c) - expect Q (A k.+1 c)).
apply: (eq_trans _ (f_equal2 (fun x y : C => x-y)
  (esym (@value_expect_step c mu Hs Hr Ho))
  (esym (@approximant_expect_step P rho0 Q c mu k Hs Hr Ho)))).
rewrite /family_observe.
rewrite -(summable_sumB (Summable.build SV) (Summable.build SA)).
by apply: eq_sum=>i; rewrite /= mulrBr.
Qed.

Lemma remainder_superharmonic k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (remainder k) <= remainder k c.
Proof. move=>Hs Hr Ho; rewrite (remainder_step k Hs Hr Ho); exact: remainder_decreasing. Qed.


Definition progress_potential k c :=
  if k is j.+1 then remainder j c else expect Q (V c).

Lemma progress_nonnegative k c : 0 <= progress_potential k c.
Proof. case: k=>[|k] /=; [exact: expect_ge0 | exact: remainder_ge0]. Qed.
Lemma progress_bound k c : `|progress_potential k c| <= 1.
Proof.
case: k=>[|k] /=; last exact: remainder_bound.
rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
Qed.
Lemma progress_decreasing k c : progress_potential k.+1 c <= progress_potential k c.
Proof.
case: k=>[|k] /=; last exact: remainder_decreasing.
by rewrite /remainder lerBlDr lerDl; exact: expect_ge0.
Qed.
Lemma progress_step k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (progress_potential k) = progress_potential k.+1 c.
Proof.
move=>Hs Hr Ho; case: k=>[|k]; last exact: remainder_step Hs Hr Ho.
change (family_observe mu (fun d => expect Q (V d)) = remainder 0 c).
have Ezero : successful_component c = CQState.bottom.
  case: (successful_component_terminal_or_zero p c)=>[Ht|Hz] //.
  exfalso; exact: Ht mu Hs.
rewrite /remainder /approximant Ezero CQHoare.expect_bottom subr0.
symmetry; exact: value_expect_step Hs Hr Ho.
Qed.
Lemma progress_superharmonic k c mu : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  family_observe mu (progress_potential k) <= progress_potential k c.
Proof.
move=>Hs Hr Ho; rewrite (progress_step k Hs Hr Ho); exact: progress_decreasing.
Qed.

End Remainder.
End DistributedHorizonRemainder.
