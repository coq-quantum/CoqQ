(* Branch equations for distributed protocols; see PROTOCOLS-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From quantum Require Import qtype.
From quantum.example.distributive Require Import protocol_quantum protocol_processes protocol_execution protocol_register.

From quantum.example.classical Require Import algorithm_semantics register_tensor.


Module DistributedProtocolPredicate.
Import DistributedProtocolQuantum DistributedProtocolProcesses DistributedProtocolExecution
  DistributedProtocolRegister.
Local Notation Hq := 'H[msys]_finset.setT.

Definition register_predicate u (q : wf_qreg u) (P : 'End('Ht u)) :=
  liftf_lf (tf2f q q P).

Lemma register_predicate_obsE u (q : wf_qreg u) P :
  register_predicate q P \is obslf = (P \is obslf).
Proof. by rewrite /register_predicate -liftf_lf_obsE tf2f_obsE. Qed.

Lemma register_predicate_le u (q : wf_qreg u) P Q :
  register_predicate q P ⊑ register_predicate q Q = (P ⊑ Q).
Proof. by rewrite /register_predicate liftf_lf_lef tf2f_lef. Qed.

Lemma register_action_pre u (q : wf_qreg u) B P :
  (register_action q B)^*o (register_predicate q P) =
    register_predicate q ((formso B)^*o P).
Proof.
rewrite /register_action /register_predicate liftfso_dual liftfsoEf
  !dualso_formE.
by rewrite tf2f_adj !tf2f_comp.
Qed.

End DistributedProtocolPredicate.
