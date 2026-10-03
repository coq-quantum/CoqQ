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
From quantum.example.distributive Require Import protocol_quantum protocol_processes protocol_execution.

From quantum.example.classical Require Import algorithm_semantics register_tensor.

Module DistributedProtocolRegister.
Import DistributedProtocolQuantum DistributedProtocolProcesses DistributedProtocolExecution.
Import ClassicalAlgorithmSemantics ClassicalRegisterTensor.
Local Notation Hq := 'H[msys]_finset.setT.

Definition register_action u (q : wf_qreg u) (A : 'End('Ht u)) : 'SO(Hq) :=
  liftfso (formso (tf2f q q A)).

Lemma register_action1 u (q : wf_qreg u) : register_action q \1 = \:1.
Proof. by rewrite /register_action tf2f1 formso1 liftfso1. Qed.

Lemma register_action_comp u (q : wf_qreg u) A B :
  register_action q A :o register_action q B = register_action q (A \o B).
Proof. exact: register_unitary_comp. Qed.

Lemma register_action_left u v (q : wf_qreg (QPair u v)) A :
  register_action (first_register q) A = register_action q (A ⊗f \1).
Proof. exact: channel_register_left. Qed.

Lemma register_action_right u v (q : wf_qreg (QPair u v)) B :
  register_action (second_register q) B = register_action q (\1 ⊗f B).
Proof. exact: channel_register_right. Qed.

Lemma register_action_pair u v (q : wf_qreg (QPair u v)) A B :
  register_action (second_register q) B :o register_action (first_register q) A =
    register_action q (A ⊗f B).
Proof.
by rewrite register_action_left register_action_right register_action_comp
  tentf_comp comp_lfun1l comp_lfun1r.
Qed.

Lemma correction_actionX q b :
  correction_action q [unitary of PauliX] b = register_action q (pauli_x b).
Proof. by case: b=>//=; rewrite /pauli_x register_action1. Qed.

Lemma correction_actionZ q b :
  correction_action q [unitary of PauliZ] b = register_action q (pauli_z b).
Proof. by case: b=>//=; rewrite /pauli_z register_action1. Qed.

Definition teleport_physical_branch (qa : wf_qreg (QPair QBool QBool))
    (qb : wf_qreg QBool) z x :=
  (register_action qb (pauli_z z \o pauli_x x)) :o
  (register_action (second_register qa) (projector x) :o
   (register_action (first_register qa) (projector z) :o
    (register_action (first_register qa) Hadamard :o
     register_action qa CNOT))).

Lemma teleport_physical_branchE (q : wf_qreg (QPair (QPair QBool QBool) QBool)) z x :
  teleport_physical_branch (first_register q) (second_register q) z x =
    register_action q (teleport_branch z x).
Proof.
rewrite /teleport_physical_branch !(register_action_left, register_action_right)
  !register_action_comp !tentf_comp !comp_lfun1l !comp_lfun1r /teleport_branch.
by rewrite !comp_lfunA !tentf_comp !comp_lfun1l !comp_lfun1r.
Qed.

Definition remote_physical_branch (qa qb : wf_qreg (QPair QBool QBool)) x z :=
  register_action (first_register qa) (pauli_z z) :o
  (register_action (second_register qb) (pauli_x x) :o
  (register_action (first_register qb) (projector z) :o
  (register_action (first_register qb) Hadamard :o
  (register_action qb CNOT :o
  (register_action (second_register qa) (projector x) :o
   register_action qa CNOT))))).

Lemma remote_physical_branchE
    (q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool))) x z :
  remote_physical_branch (first_register q) (second_register q) x z =
    register_action q (remote_branch x z).
Proof.
rewrite /remote_physical_branch.
rewrite !(register_action_left, register_action_right) !register_action_comp.
rewrite !tentf_comp !comp_lfun1l !comp_lfun1r /remote_branch.
by rewrite !comp_lfunA !tentf_comp !comp_lfun1l !comp_lfun1r.
Qed.

End DistributedProtocolRegister.
