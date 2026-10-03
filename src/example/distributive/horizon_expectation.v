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

Module DistributedHorizonExpectation.
Import DistributedLanguage DistributedOperational DistributedDistribution
  DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions
  DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate
  DistributedGlobalInstruments DistributedObservables CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Horizon.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).

Lemma approximant_collapse k c :
  @approximant P rho0 k (@collapse P rho0 c) = @approximant P rho0 k c.
Proof.
case: c=>[[pc [s|]] rho] //.
change (@approximant P rho0 k (@failure P rho0) =
  @approximant P rho0 k (global_config pc None rho)).
rewrite !approximant_terminal; try exact: failure_terminal.
by [].
Qed.

Lemma approximant_global_step c mu k (Hs : global_step p c mu)
    (Hr : c.2 \is den1lf) : configuration_owned p c ->
  @approximant P rho0 k.+1 c =
  CQStateMixture.mix (probability_distribution (global_step_probability Hs Hr))
    (fun i => @approximant P rho0 k (branch_value mu i)).
Proof.
move=>Ho; apply/vdistrP=>out.
rewrite CQStateMixture.mixE.
have Hp := @ProjectedGlobal P rho0 c mu (conj Hr Ho) Hs.
rewrite -(@approximant_advance P rho0 c _ k out Hp) /weighted_sum.
by apply: eq_sum=>i; rewrite /= approximant_collapse.
Qed.

Lemma approximant_expect_step Q c mu k : global_step p c mu ->
  c.2 \is den1lf -> configuration_owned p c ->
  expect Q (@approximant P rho0 k.+1 c) =
  family_observe mu (fun d => expect Q (@approximant P rho0 k d)).
Proof.
move=>Hs Hr Ho.
rewrite (@approximant_global_step c mu k Hs Hr Ho) CQMixtureExpectation.expect_mix.
by apply: eq_sum=>i; rewrite probability_distributionE.
Qed.

Theorem horizon_pre_observe k Q c : c.2 \is den1lf -> configuration_owned p c ->
  @observe P (@horizon_pre P k Q) c = expect Q (@approximant P rho0 k c).
Proof.
elim: k c=>[|k IH] [[pc [m|]] rho] Hr Ho.
- exact: terminal_pre_observe (den1lf_den Hr).
- by rewrite /observe /= CQHoare.expect_bottom.
- change (\Tr (@horizon_pre P k.+1 Q pc m \o rho) =
    expect Q (@approximant P rho0 k.+1 (global_config pc (Some m) rho))).
  rewrite /horizon_pre -/(@horizon_pre P k Q).
  case Ed: (@selected_descriptor P pc m)=>[d|].
  + have [a [Hd Hwf]] := @selected_descriptor_some P pc m d Ed.
    have Hs := labeled_step_erasure (@descriptor_step n p pc m rho a d Hd Hwf).
    rewrite (@descriptor_pre_observe P (@horizon_pre P k Q) d pc m rho Hr) (@approximant_expect_step Q _ _ k Hs Hr Ho).
    apply: eq_sum=>i; congr (_ * _).
    apply: IH; first exact: global_step_normalized Hs Hr i.
    exact: (@global_step_owned n p _ _ (@processes_wf P) Ho Hs i).
  + rewrite (@approximant_terminal P rho0 _ (@descriptor_terminal P pc m rho Ho Ed)).
    exact: terminal_pre_observe (den1lf_den Hr).
- rewrite (@approximant_terminal P rho0 _ (@failure_terminal n p pc rho)).
  by rewrite /observe /= CQHoare.expect_bottom.
Qed.

End Horizon.
End DistributedHorizonExpectation.
