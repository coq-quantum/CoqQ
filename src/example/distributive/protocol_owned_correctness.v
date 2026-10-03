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
From quantum.example.distributive Require Import protocol_quantum protocol_state protocol_local protocol_effect protocol_predicate
  protocol_pre protocol_serial protocol_register protocol_processes protocol_execution
  language sequentialization protocol_ownership teleport_correctness remote_correctness.


From quantum.example.classical Require Import rules.

From quantum.example.classical Require Import register_tensor.

Module DistributedOwnedProtocolCorrectness.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses
  DistributedProtocolOwnership ClassicalRegisterTensor.
Local Notation Hq := 'H[msys]_finset.setT.

Definition teleport_network (q : wf_qreg (QPair (QPair QBool QBool) QBool)) :=
  @teleport_program (first_register q) (second_register q) (pair_register_disjoint q).

Definition remote_network (q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool))) :=
  @remote_program (first_register q) (second_register q) (pair_register_disjoint q).

Lemma teleport_network_sourceE q :
  successful_sequentialize (processes (teleport_network q)) =
    DistributedTeleportCorrectness.teleport_source q.
Proof. by []. Qed.

Lemma remote_network_sourceE q :
  successful_sequentialize (processes (remote_network q)) =
    DistributedRemoteCorrectness.remote_source q.
Proof. by []. Qed.

Theorem teleport_network_correct total q v (Hv : [< v; v >] = 1) :
  CQRules.derives total
    (fun _ => @DistributedTeleportCorrectness.teleport_input q v Hv)
    (successful_sequentialize (processes (teleport_network q)))
    (fun _ => @DistributedTeleportCorrectness.teleport_post q v Hv).
Proof.
rewrite teleport_network_sourceE.
exact: (@DistributedTeleportCorrectness.teleport_correct q v Hv total).
Qed.

Theorem remote_network_correct total q v (Hv : [< v; v >] = 1) :
  CQRules.derives total
    (fun _ => @DistributedRemoteCorrectness.remote_input q v Hv)
    (successful_sequentialize (processes (remote_network q)))
    (fun _ => @DistributedRemoteCorrectness.remote_post q v Hv).
Proof.
rewrite remote_network_sourceE.
exact: (@DistributedRemoteCorrectness.remote_correct q v Hv total).
Qed.

End DistributedOwnedProtocolCorrectness.
