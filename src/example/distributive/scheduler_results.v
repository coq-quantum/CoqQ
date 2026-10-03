(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.distributive Require Import language operational distribution weighted scheduler local_actions results residual sequentialization observables diamond global_actions scheduler_semantics confluence.
From quantum.example.classical Require Import state.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedSchedulerResults.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted
  DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Section ComputationProjection.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Variable c : global_configuration n.
Variable pi : computation p c.

Definition projected_stage k := fmap (@collapse P rho0) (computation_stage pi k).

Lemma projected_initial :
  same_distribution (projected_stage 0%N) (certain (@collapse P rho0 c)).
Proof. exact: (@same_distribution_fmap _ _ (@collapse P rho0) _ _ (computation_initial pi)). Qed.

Lemma projected_stage_probability k : probability_family (projected_stage k).
Proof. exact: computation_probability. Qed.

Lemma projected_stage_evolution : configuration_owned p c -> forall k,
  ProbabilisticDiamond.evolution (@projected_step P rho0) (projected_stage k) (projected_stage k.+1).
Proof.
move=>Hown k; apply: projected_evolution; first exact: computation_probability.
- move=>i Hi; split.
  + exact: (@computation_normalized n p c pi k i Hi).
  + exact: (@computation_owned n p c pi (@processes_wf P) Hown k i Hi).
- exact: computation_advances.
Qed.

Lemma projected_stage_observe k m :
  weighted_sum (projected_stage k) (fun d => successful_component d m) = stage_state pi k m.
Proof.
rewrite /projected_stage weighted_collapse.
by rewrite /stage_state successful_state_weighted.
Qed.

End ComputationProjection.
Section Independence.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).

Theorem stage_horizon c (pi : computation p c) : configuration_owned p c -> forall k m,
  stage_state pi k m = ProbabilisticDiamond.horizon (@policy P rho0)
    (fun d => successful_component d m) k (@collapse P rho0 c).
Proof.
move=>Hown k m; rewrite -(@projected_stage_observe P rho0 c pi k m).
exact (@ProbabilisticDiamond.finite_horizon_unique (global_configuration n) Hq
  (@projected_step P rho0) (@policy P rho0) (fun d => successful_component d m)
  (@projected_probability P rho0) (@policy_step P rho0)
  (fun d => successful_component_bound d m)
  (fun c mu nu => @projected_one_step P rho0 c mu nu m)
  (@DistributedConfluence.projected_two_step_diamond P rho0)
  (@projected_stage P rho0 c pi) (@collapse P rho0 c)
  (@projected_initial P rho0 c pi) (@projected_stage_probability P rho0 c pi)
  (@projected_stage_evolution P rho0 c pi Hown) k).
Qed.

Theorem stage_scheduler_independent c (pi sigma : computation p c) :
  configuration_owned p c -> forall k, stage_state pi k = stage_state sigma k.
Proof.
move=>Hown k; apply/vdistrP=>m.
by rewrite (@stage_horizon c pi Hown k m) (@stage_horizon c sigma Hown k m).
Qed.

Theorem result_scheduler_independent c (pi sigma : computation p c) :
  configuration_owned p c -> result_state pi = result_state sigma.
Proof.
move=>Hown.
have E : stage_state pi = stage_state sigma.
  apply/funext=>k; exact: (@stage_scheduler_independent c pi sigma Hown k).
by rewrite /result_state E.
Qed.

Theorem denotational_results_unique c d e : configuration_owned p c ->
  denotational_results p c d -> denotational_results p c e -> d = e.
Proof.
move=>Hown [pi Hpi] [sigma Hsigma].
rewrite -(computes_result Hpi) -(computes_result Hsigma); apply/funext=>m.
by rewrite !result_stateE (@result_scheduler_independent c pi sigma Hown).
Qed.

End Independence.

Definition denote_configuration (P : program) c (Hc : c.2 \is den1lf) :=
  result_state (canonical_computation (processes P) Hc).
Arguments denote_configuration P {c} Hc.

Theorem denotational_results_singleton (P : program) c (Hc : c.2 \is den1lf) d :
  configuration_owned (processes P) c ->
  (denotational_results (processes P) c d <->
    d = (fun m => denote_configuration P Hc m)).
Proof.
move=>Hown; split.
- move=>Hd; apply: (@denotational_results_unique P c.2 c d
    (fun m => denote_configuration P Hc m) Hown Hd).
  exists (canonical_computation (processes P) Hc); exact: computation_converges.
- move=>->; exists (canonical_computation (processes P) Hc); exact: computation_converges.
Qed.

Definition denote_program (P : program) m (rho : 'FD1(Hq)) :=
  denote_configuration P (c := initial_configuration (processes P) m rho) (is_den1lf rho).

End DistributedSchedulerResults.
