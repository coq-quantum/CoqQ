(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)
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


From quantum.example.distributive Require Import serial_scheduler residual_semantics stopped_invariant results.

From quantum.example.distributive Require Import boundary_semantics active_pairs weighted.

From quantum.example.distributive Require Import local_harmonic rendezvous_harmonic
  serial_invariant scheduler_semantics scheduler_results global_value residual local_actions.

Module DistributedBoundaryLower.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant
  DistributedBoundarySemantics DistributedWeighted DistributedSerialInvariant
  DistributedSchedulerSemantics DistributedSchedulerResults DistributedGlobalValue
  DistributedResidual DistributedResults.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma deterministic_step_good (P : program) c d :
  @good P c -> global_step (processes P) c (certain d) -> @good P d.
Proof.
move=>[Hr Ho] Hstep; split.
- exact: (@global_step_normalized _ _ _ _ Hstep Hr tt).
- exact: (@global_step_owned _ _ _ _ (@processes_wf P) Ho Hstep tt).
Qed.

Lemma deterministic_step_value (P : program) rho0 c d :
  @good P c -> global_step (processes P) c (certain d) ->
  @value P rho0 c = @value P rho0 d.
Proof.
move=>Hg Hstep; apply/vdistrP=>out.
have Hproj := @ProjectedGlobal P rho0 c (certain d) Hg Hstep.
have E := @value_bellman P rho0 c _ out Hproj.
change (@value P rho0 c out = weighted_sum (certain (@collapse P rho0 d))
  (fun e => @value P rho0 e out)) in E.
by rewrite weighted_certain value_collapse in E.
Qed.

Lemma deterministic_steps_value (P : program) rho0 c d :
  deterministic_steps (processes P) c d -> @good P c ->
  @value P rho0 c = @value P rho0 d.
Proof.
move=>Hpath; elim: Hpath=>[c0|c0 d0 e0 Hstep Htail IH] Hg.
- reflexivity.
- exact: (eq_trans (deterministic_step_value rho0 Hg Hstep)
    (IH (deterministic_step_good Hg Hstep))).
Qed.

Theorem ready_term_value (P : program) rho0 pc m rho :
  ready pc -> term (processes P) m ->
  @good P (global_config pc (Some m) rho) -> forall out,
  @value P rho0 (global_config pc (Some m) rho) out = skip_sem m out rho.
Proof.
move=>Hready Hterm Hg out.
have Hr : rho \is denlf := den1lf_den (proj1 Hg).
have Hpath := @terminate_stop_list _ (processes P) (enum 'I_(process_count P))
  pc m rho Hready Hterm.
rewrite stop_enum in Hpath.
rewrite (@deterministic_steps_value P rho0 _ _ Hpath Hg).
rewrite (@value_terminal P rho0 _
  (@stopped_terminal _ (processes P) (Some m) rho)).
rewrite (@successful_componentE _ (global_config (fun _ => Stopped) (Some m) rho) out Hr).
rewrite /successful_at /=.
have Estop : [forall i : 'I_(process_count P), asbool ((fun _ => Stopped) i = Stopped)].
  by apply/forallP=>i; exact/asboolP.
rewrite Estop andbT skip_semE /=.
by rewrite eq_sym; case: (out == m); rewrite soE.
Qed.

Corollary ready_term_lower (P : program) rho0 pc m rho :
  ready pc -> term (processes P) m ->
  @good P (global_config pc (Some m) rho) -> forall out,
  skip_sem m out rho ⊑ @value P rho0 (global_config pc (Some m) rho) out.
Proof. move=>Hready Hterm Hg out; by rewrite (ready_term_value rho0 Hready Hterm Hg). Qed.

End DistributedBoundaryLower.
