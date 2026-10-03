(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum Require Import qtype.
From quantum.example.classical Require Import deterministic algorithm_semantics predicate.
From quantum.example.distributive Require Import language sequentialization protocol_processes.

From quantum.example.distributive Require Import protocol_execution protocol_quantum protocol_suffix protocol_serial protocol_register protocol_pre protocol_remote_serial.

From quantum.example.classical Require Import rules primitive.



Module DistributedProtocolRemotePre.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum
  DistributedProtocolRegister DistributedProtocolPre DistributedProtocolRemoteSerial.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQRules CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma remote_tail_pre total qa qb (Q : 'FO(Hq)) s :
  (s.[stageA])%M = (0 : int) ->
  (pre total (remote_tail qa qb) (fun _ => Q) s : 'End(Hq)) =
  (register_action (first_register qa) (pauli_z (s.[zB])%M) :o
   register_action (second_register qb) (pauli_x (s.[xA])%M))^*o Q.
Proof.
move=>Ha.
rewrite /pre (execution_preE total _ (remote_tail_execution qa qb Ha))
  remote_loop_actionE !get_set_nex //.
by rewrite correction_actionZ correction_actionX.
Qed.

Lemma remote_serial_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (remote_serial qa qb) (fun _ => Q) s : 'End(Hq)) =
    \sum_x \sum_z (remote_physical_branch qa qb x z)^*o Q.
Proof.
rewrite /remote_serial pre_sequence pre_sequence pre_sequence pre_sequence
  pre_sequence pre_sequence.
rewrite unitary_pre_register computational_measurement_pre linear_sum.
apply: eq_bigr=>x _.
rewrite /pre CQPrimitive.assign_pre unitary_pre_register unitary_pre_register
  computational_measurement_pre !linear_sum.
apply: eq_bigr=>z _.
rewrite remote_tail_pre.
- by rewrite get_set_nex // get_set_eq.
- rewrite get_set_eq get_set_nex // get_set_nex // get_set_eq.
  by rewrite /remote_physical_branch !dualso_comp !comp_soE.

Qed.

End DistributedProtocolRemotePre.
