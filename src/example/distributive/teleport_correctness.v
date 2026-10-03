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
  language sequentialization.


From quantum.example.classical Require Import rules.

Module DistributedTeleportCorrectness.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses
  DistributedProtocolExecution DistributedProtocolQuantum DistributedProtocolState
  DistributedProtocolLocal DistributedProtocolEffect DistributedProtocolPredicate
  DistributedProtocolPre DistributedProtocolSerial DistributedProtocolRegister.
Import CQRules.
Local Notation Hq := 'H[msys]_finset.setT.

Section Protocol.
Variable q : wf_qreg (QPair (QPair QBool QBool) QBool).
Variable v : 'Hs bool.
Hypothesis normalized_v : [< v; v >] = 1.

Definition teleport_source :=
  successful_sequentialize (paired (teleport_alice (first_register q))
    (teleport_bob (second_register q))).

Lemma teleport_post_obs : register_predicate q (teleport_output v) \is obslf.
Proof. rewrite register_predicate_obsE; exact: teleport_output_obs normalized_v. Qed.
Definition teleport_post : 'FO(Hq) := ObsLf_Build teleport_post_obs.

Lemma teleport_input_obs :
  register_predicate q [> teleport_resource v; teleport_resource v <] \is obslf.
Proof.
rewrite register_predicate_obsE; apply: normalized_outp_obs.
by rewrite isof_dot normalized_v.
Qed.
Definition teleport_input : 'FO(Hq) := ObsLf_Build teleport_input_obs.

Lemma teleport_preE total s :
  (pre total teleport_source (fun _ => teleport_post) s : 'End(Hq)) =
    register_predicate q (teleport_local_pre v).
Proof.
rewrite /teleport_source teleport_serial_preE teleport_serial_pre.
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite teleport_physical_branchE.
change (\sum_z \sum_x (register_action q (teleport_branch z x))^*o
  (register_predicate q (teleport_output v)) = register_predicate q (teleport_local_pre v)).
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite register_action_pre.
rewrite /teleport_local_pre /register_predicate !linear_sum /=.
by apply: eq_bigr=>z _; rewrite !linear_sum /=.
Qed.

Lemma teleport_local_pre_obs (total : bool) (s : CL.store) : teleport_local_pre v \is obslf.
Proof.
rewrite -(register_predicate_obsE q _) -(teleport_preE total s).
exact: is_obslf.
Qed.

Lemma teleport_pre_inequality total s :
  (teleport_input : 'End(Hq)) ⊑ pre total teleport_source (fun _ => teleport_post) s.
Proof.
rewrite teleport_preE /teleport_input /= register_predicate_le.
rewrite (ObsLf_BuildE (teleport_local_pre_obs total s)).
apply: effect_contains_state.
- by rewrite isof_dot normalized_v.
- exact: teleport_local_success normalized_v.
Qed.

Theorem teleport_correct total :
  derives total (fun _ => teleport_input) teleport_source (fun _ => teleport_post).
Proof.
apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>s.
exact: teleport_pre_inequality.
Qed.
End Protocol.

End DistributedTeleportCorrectness.
