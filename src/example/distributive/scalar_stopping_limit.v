(* Finite completed local executions are bounded by the global value. *)
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

From quantum.example.distributive Require Import local_iterations serial_scheduler serial_invariant scheduler_semantics global_value residual scheduler local_iteration_bounds.

From quantum.example.distributive Require Import local_lower local_iteration_limits observables instruments.

From quantum.example.distributive Require Import scalar_stopping local_expectation_limits.

Module DistributedScalarStoppingLimit.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant
  DistributedLocalLower DistributedScalarStopping DistributedLocalExpectationLimits
  DistributedDistribution CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem translated_local_stopping (P : program)
    (pc : 'I_(process_count P) -> control) i
    (V : global_configuration (process_count P) -> C) (A : assertion) :
  (forall c, serial_invariant P c -> 0 <= V c) ->
  (forall c, serial_invariant P c -> `|V c| <= 1) ->
  (forall c mu, serial_invariant P c -> global_step (processes P) c mu ->
    family_observe mu V <= V c) ->
  (forall m rho,
    serial_invariant P (lift_local (processes P) pc i (local_config Finished (Some m) rho)) ->
    \Tr (A m \o rho) <= V (lift_local (processes P) pc i (local_config Finished (Some m) rho))) ->
  forall s m rho,
    serial_invariant P (lift_local (processes P) pc i (local_config s (Some m) rho)) ->
    \Tr (wp (CL.denote (translate_statement s)) A m \o rho) <=
      V (lift_local (processes P) pc i (local_config s (Some m) rho)).
Proof.
move=>Hnonneg Hbounded Hstep Hend s m rho Hinv.
apply: local_wp_pairing_least; first exact: lifted_residual_wf Hinv.
move=>N; exact: (@local_iter_stopping P pc i V Hnonneg Hbounded Hstep A Hend N s m rho Hinv).
Qed.

End DistributedScalarStoppingLimit.
