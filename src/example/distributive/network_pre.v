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
From quantum.example.distributive Require Import language sequentialization guarded_rules.
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


From quantum.example.distributive Require Import network_rules residual_semantics serial_scheduler boundary_semantics.

Module DistributedNetworkPre.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules
  DistributedResidualSemantics DistributedSerialScheduler DistributedBoundarySemantics CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma xp_row total (K L : CL.kernel) (Q : assertion) m :
  K m = L m -> xp total K Q m = xp total L Q m.
Proof.
move=>E; case: total; apply/val_inj.
- change ((wp K Q m : 'End(Hq)) = (wp L Q m : 'End(Hq))).
  by rewrite !wpE E.
- change ((wp K (complement Q) m : 'End(Hq))^⟂ =
    (wp L (complement Q) m : 'End(Hq))^⟂).
  by rewrite !wpE E.
Qed.

Lemma tail_pre_term total n (p : 'I_n -> process) (Q : assertion) m :
  DistributedLanguage.term p m -> CQRules.pre total (network_tail p) Q m = Q m.
Proof.
move=>Ht; rewrite /CQRules.pre (@xp_row total _ skip_sem Q m (network_tail_term Ht)).
by rewrite xp_skip.
Qed.

Lemma tail_pre_post total n (p : 'I_n -> process) (Q : assertion) :
  semantic_le (mask (DistributedLanguage.term p) (CQRules.pre total (network_tail p) Q)) Q.
Proof.
move=>m; rewrite /mask; case Ht: (DistributedLanguage.term p m).
- by rewrite (tail_pre_term total Q Ht).
- exact: obsf_ge0.
Qed.

Lemma blocked_no_rendezvous n (p : 'I_n -> process) m : blocked p m -> no_rendezvous p m.
Proof.
change (~~ eval (branch_guard (rendezvous_commands p)) m -> no_rendezvous p m).
rewrite eval_branch_guard /no_rendezvous.
change (~~ has (fun bc : expression bool * CL.command => eval bc.1 m)
    (rendezvous_commands p) ->
  all (predC (fun bc : expression bool * CL.command => eval bc.1 m)) (rendezvous_commands p)).
by rewrite all_predC.
Qed.

Lemma tail_pre_deadlock n (p : 'I_n -> process) (Q : assertion) :
  semantic_le (mask (blocked p) (CQRules.pre true (network_tail p) Q))
    (mask (DistributedLanguage.term p) semantic_top).
Proof.
move=>m; rewrite /mask; case Hb: (blocked p m); last exact: obsf_ge0.
case Ht: (DistributedLanguage.term p m); first exact: obsf_le1.
have E : CL.denote (network_tail p) m = abort_sem m.
  by rewrite (network_tail_blocked (blocked_no_rendezvous Hb)) Ht.
rewrite /CQRules.pre (@xp_row true _ abort_sem Q m E) /xp wp_abort.
exact: lexx.
Qed.

Lemma initialization_pre total n (p : 'I_n -> process) (Q : assertion) :
  CQRules.pre total (successful_sequentialize p) Q =
  CQRules.pre total (initialization_command p) (CQRules.pre total (network_tail p) Q).
Proof.
by rewrite /successful_sequentialize /sequentialize /initialization_command /network_tail
  !CQRules.pre_sequence.
Qed.

End DistributedNetworkPre.
