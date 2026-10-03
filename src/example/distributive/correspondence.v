(* Operational/serialized denotational equality for distributed networks. *)
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

Module DistributedCorrespondence.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant
  DistributedGlobalValue DistributedLocalLower DistributedResidual DistributedActiveLower
  DistributedControlCompletion DistributedNetworkLower DistributedSerialUpper
  DistributedSchedulerResults.
Local Notation Hq := 'H[msys]_finset.setT.

Theorem residual_below_value (P : program) rho0 pc m rho out :
  serial_invariant P (global_config pc (Some m) rho) ->
  CL.denote (residual_command (processes P) pc) m out rho ⊑
    @value P rho0 (global_config pc (Some m) rho) out.
Proof.
move=>Hinv; apply: (@active_program_lower P rho0 (enum 'I_(process_count P))
  (enum_uniq _) pc (network_tail (processes P)) out _ m rho Hinv).
move=>u r Hend.
exact: (@network_tail_lower P rho0
  (finish_controls (processes P) (enum 'I_(process_count P)) pc)
  (@finish_controls_ready (process_count P) (processes P) pc) u r out Hend).
Qed.

Theorem residual_value (P : program) rho0 : rho0 \is den1lf ->
  forall c, serial_invariant P c ->
  residual_state (processes P) c = @value P rho0 c.
Proof.
move=>Hrho c Hinv; apply/vdistrP=>out; apply/eqP; rewrite eq_le; apply/andP; split.
- case: c Hinv=>[[pc [m|]] rho] Hinv.
  + have Hr : rho \is denlf.
      apply: den1lf_den; exact: (proj1 (proj1 Hinv)).
    rewrite (@residual_stateE (process_count P) (processes P) pc m rho out Hr).
    exact: residual_below_value Hinv.
  + change (0%:VF ⊑ @value P rho0 (global_config pc None rho) out).
    exact: vdistr_ge0.
- by move: (@value_below_residual P rho0 Hrho c Hinv)=>/levdP/(_ out).
Qed.

Theorem denote_program_sequentialize (P : program) m (rho : 'FD1(Hq)) :
  denote_program P m rho =
    CQKernel.apply (CL.denote (successful_sequentialize (processes P)))
      (CQState.point m (rho : 'FD(Hq))).
Proof.
have Hinit := @serial_initial P m rho (is_den1lf rho).
have E := @residual_value P rho (is_den1lf rho)
  (initial_configuration (processes P) m rho) Hinit.
rewrite residual_initial_state
  (@value_denote P rho (initial_configuration (processes P) m rho)
    (is_den1lf rho) (proj2 (proj1 Hinit))) in E.
exact: esym E.
Qed.

Theorem denote_program_point (P : program) m (rho : 'FD1(Hq)) out :
  denote_program P m rho out =
    CL.denote (successful_sequentialize (processes P)) m out rho.
Proof. by rewrite denote_program_sequentialize CQKernel.apply_point. Qed.

End DistributedCorrespondence.
