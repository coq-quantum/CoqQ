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

From quantum.example.distributive Require Import protocol_execution protocol_quantum protocol_suffix protocol_serial protocol_register.

From quantum.example.classical Require Import rules primitive.


Module DistributedProtocolPre.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum
  DistributedProtocolSerial DistributedProtocolRegister.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQRules CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma unitary_pre_register total u (q : wf_qreg u) U Q s :
  (pre total (CL.Unitary q (CL.EConst U)) Q s : 'End(Hq)) =
    (register_action q U)^*o (Q s).
Proof. exact: CQPrimitive.unitary_pre. Qed.

Lemma computational_measurement_pre total (q : wf_qreg QBool)
    (x : CL.variable (QType QBool)) Q s :
  (pre total (CL.Measure x q (CL.EConst [QM of @tmeas bool])) Q s : 'End(Hq)) =
    \sum_b (register_action q (projector b))^*o (Q (s.[x <- b])%M).
Proof.
rewrite /pre CQPrimitive.measurement_pre.
apply: eq_bigr=>b _.
by rewrite /register_action liftfso_formso dualso_formE.
Qed.

Lemma teleport_tail_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (teleport_tail qa qb) (fun _ => Q) s : 'End(Hq)) =
  (register_action qb (pauli_z (s.[zA])%M \o pauli_x (s.[xA])%M))^*o Q.
Proof.
rewrite /pre (execution_preE total _ (teleport_tail_execution qa qb s))
  teleport_loop_actionE /stages_zero !get_set_nex //.
by rewrite correction_actionZ correction_actionX register_action_comp.
Qed.

Lemma teleport_serial_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (teleport_serial qa qb) (fun _ => Q) s : 'End(Hq)) =
    \sum_z \sum_x (teleport_physical_branch qa qb z x)^*o Q.
Proof.
rewrite /teleport_serial pre_sequence pre_sequence pre_sequence pre_sequence.
rewrite unitary_pre_register unitary_pre_register computational_measurement_pre.
under eq_bigr=>z _ do rewrite computational_measurement_pre.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite teleport_tail_pre get_set_nex // !get_set_eq.
rewrite !linear_sum /=.
apply: eq_bigr=>z _; rewrite !linear_sum /=.
apply: eq_bigr=>x _.
by rewrite /teleport_physical_branch !dualso_comp !comp_soE.

Qed.

End DistributedProtocolPre.
