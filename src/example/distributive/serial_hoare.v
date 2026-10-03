(* Lemma C.9 for the raw serializer; see SERIAL-HOARE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion language kernel
  operational kernel_expectation expectation expectation_limits kernel_limits
  predicate hoare rules.
From quantum.example.distributive Require Import language sequentialization
  guarded_rules network_rules operational_hoare.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.

Module DistributedSerialHoare.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules
  CQAssertion CQPredicate CQRules.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma pre_unroll_post_agree total b c (Q R : assertion) :
  (forall m, ~~ eval b m -> Q m = R m) ->
  forall k, pre total (CL.unroll b c k) Q = pre total (CL.unroll b c k) R.
Proof.
move=>H; elim=>[|k IH].
- by case: total; rewrite /pre /= /xp ?wp_abort ?wlp_abort.
- rewrite !pre_unrollS IH; apply/funext=>m; rewrite /conditional -/(eval b m).
  case E: (eval b m)=>//; apply: H; by rewrite E.
Qed.

Lemma pre_while_post_agree total b c (Q R : assertion) :
  (forall m, ~~ eval b m -> Q m = R m) ->
  pre total (CL.While b c) Q = pre total (CL.While b c) R.
Proof.
move=>H; apply/funext=>m; apply/val_inj.
change ((pre total (CL.While b c) Q m : 'End(Hq)) =
  (pre total (CL.While b c) R m : 'End(Hq))).
have CQ : ((fun k => (pre total (CL.unroll b c k) Q m : 'End(Hq))) @ \oo -->
    (pre total (CL.While b c) Q m : 'End(Hq)))%classic.
  by case: total; [exact: wp_unroll_cvg | exact: wlp_unroll_cvg].
have CR : ((fun k => (pre total (CL.unroll b c k) R m : 'End(Hq))) @ \oo -->
    (pre total (CL.While b c) R m : 'End(Hq)))%classic.
  by case: total in CQ *; [exact: wp_unroll_cvg | exact: wlp_unroll_cvg].
have EQ k := pre_unroll_post_agree total c H k.
have Eseq : (fun k => (pre total (CL.unroll b c k) Q m : 'End(Hq))) =
    (fun k => (pre total (CL.unroll b c k) R m : 'End(Hq))).
  by apply/funext=>k; rewrite EQ.
rewrite Eseq in CQ.
by rewrite -(cvg_lim (@norm_hausdorff _ _) CQ) (cvg_lim (@norm_hausdorff _ _) CR).
Qed.

Definition partial_serial_post n (p : 'I_n -> process) (Q : assertion) :=
  conditional (DistributedLanguage.term p) Q (mask (blocked p) semantic_top).

Lemma partial_serial_postE n (p : 'I_n -> process) Q m :
  (partial_serial_post p Q m : 'End(Hq)) =
  (mask (DistributedLanguage.term p) Q m : 'End(Hq)) +
  (mask (fun s => ~~ DistributedLanguage.term p s && blocked p s) semantic_top m : 'End(Hq)).
Proof.
rewrite /partial_serial_post /conditional /mask.
by case: (DistributedLanguage.term p m); case: (blocked p m); rewrite /= ?addr0 ?add0r.
Qed.

Lemma final_test_total_pre n (p : 'I_n -> process) Q :
  pre true (CL.Conditional (termination_guard p) CL.Skip CL.Abort)
    (mask (DistributedLanguage.term p) Q) = mask (DistributedLanguage.term p) Q.
Proof.
rewrite pre_conditional /pre /= /xp wp_skip wp_abort.
apply/funext=>m; rewrite /conditional /mask -/(eval (termination_guard p) m) eval_termination_guard.
by case: (DistributedLanguage.term p m).
Qed.

Lemma final_test_partial_pre n (p : 'I_n -> process) Q :
  pre false (CL.Conditional (termination_guard p) CL.Skip CL.Abort)
    (mask (DistributedLanguage.term p) Q) =
  conditional (DistributedLanguage.term p) Q semantic_top.
Proof.
rewrite pre_conditional /pre /= /xp wlp_skip wlp_abort.
apply/funext=>m; rewrite /conditional /mask -/(eval (termination_guard p) m) eval_termination_guard.
by case: (DistributedLanguage.term p m).
Qed.

Lemma raw_partial_post_agree n (p : 'I_n -> process) Q :
  pre false (sequentialize p) (conditional (DistributedLanguage.term p) Q semantic_top) =
  pre false (sequentialize p) (partial_serial_post p Q).
Proof.
rewrite /sequentialize !pre_sequence.
congr (pre false _ _); apply: pre_while_post_agree=>m Hblocked.
have Hb : blocked p m := Hblocked.
rewrite /partial_serial_post /conditional /mask Hb.
by case: (DistributedLanguage.term p m).
Qed.

Theorem total_raw_sequentialization_iff (P Q : assertion) (S : program) :
  DistributedHoare.valid true P S (mask (DistributedLanguage.term (processes S)) Q) <->
  CQHoare.valid true P (sequentialize (processes S))
    (mask (DistributedLanguage.term (processes S)) Q).
Proof.
rewrite DistributedHoare.valid_translate_iff !valid_iff.
by rewrite /successful_sequentialize pre_sequence final_test_total_pre.
Qed.

Theorem partial_raw_sequentialization_iff (P Q : assertion) (S : program) :
  DistributedHoare.valid false P S (mask (DistributedLanguage.term (processes S)) Q) <->
  CQHoare.valid false P (sequentialize (processes S)) (partial_serial_post (processes S) Q).
Proof.
rewrite DistributedHoare.valid_translate_iff !valid_iff.
by rewrite /successful_sequentialize pre_sequence final_test_partial_pre raw_partial_post_agree.
Qed.

End DistributedSerialHoare.
