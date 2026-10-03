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
From quantum.example.distributive Require Import protocol_quantum protocol_state protocol_local protocol_remote_local protocol_effect protocol_predicate
  protocol_pre protocol_remote_pre protocol_serial protocol_remote_serial protocol_register protocol_processes protocol_execution
  language sequentialization.


From quantum.example.classical Require Import rules.

Module DistributedRemoteCorrectness.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses
  DistributedProtocolExecution DistributedProtocolQuantum DistributedProtocolState
  DistributedProtocolLocal DistributedProtocolRemoteLocal DistributedProtocolEffect DistributedProtocolPredicate
  DistributedProtocolPre DistributedProtocolRemotePre DistributedProtocolSerial DistributedProtocolRemoteSerial DistributedProtocolRegister.
Import CQRules.
Local Notation Hq := 'H[msys]_finset.setT.

Section Protocol.
Variable q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool)).
Variable v : 'Hs (bool * bool)%type.
Hypothesis normalized_v : [< v; v >] = 1.

Definition remote_source :=
  successful_sequentialize (paired (remote_alice (first_register q))
    (remote_bob (second_register q))).

Lemma remote_post_obs : register_predicate q (remote_output v) \is obslf.
Proof. rewrite register_predicate_obsE; exact: remote_output_obs normalized_v. Qed.
Definition remote_post : 'FO(Hq) := ObsLf_Build remote_post_obs.

Lemma remote_input_obs :
  register_predicate q [> remote_resource v; remote_resource v <] \is obslf.
Proof.
rewrite register_predicate_obsE; apply: normalized_outp_obs.
by rewrite isof_dot normalized_v.
Qed.
Definition remote_input : 'FO(Hq) := ObsLf_Build remote_input_obs.

Lemma remote_preE total s :
  (pre total remote_source (fun _ => remote_post) s : 'End(Hq)) =
    register_predicate q (remote_local_pre v).
Proof.
rewrite /remote_source remote_serial_preE remote_serial_pre.
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite remote_physical_branchE.
change (\sum_z \sum_x (register_action q (remote_branch z x))^*o
  (register_predicate q (remote_output v)) = register_predicate q (remote_local_pre v)).
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite register_action_pre.
rewrite /remote_local_pre /register_predicate !linear_sum /=.
by apply: eq_bigr=>z _; rewrite !linear_sum /=.
Qed.

Lemma remote_local_pre_obs (total : bool) (s : CL.store) : remote_local_pre v \is obslf.
Proof.
rewrite -(register_predicate_obsE q _) -(remote_preE total s).
exact: is_obslf.
Qed.

Lemma remote_pre_inequality total s :
  (remote_input : 'End(Hq)) ⊑ pre total remote_source (fun _ => remote_post) s.
Proof.
rewrite remote_preE /remote_input /= register_predicate_le.
rewrite (ObsLf_BuildE (remote_local_pre_obs total s)).
apply: effect_contains_state.
- by rewrite isof_dot normalized_v.
- exact: remote_local_success normalized_v.
Qed.

Theorem remote_correct total :
  derives total (fun _ => remote_input) remote_source (fun _ => remote_post).
Proof.
apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>s.
exact: remote_pre_inequality.
Qed.
End Protocol.

End DistributedRemoteCorrectness.
