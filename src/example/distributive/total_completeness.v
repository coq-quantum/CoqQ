(* Relative completeness of the independent distributed inference rules. *)
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


From quantum.example.distributive Require Import network_rules network_pre operational_hoare rendezvous_all residual_semantics.

From quantum.example.distributive Require Import horizon_effects network_ranking partial_completeness.

Module DistributedTotalCompleteness.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules DistributedNetworkPre
  DistributedResidualSemantics DistributedAllRendezvous DistributedHorizonEffects
  DistributedNetworkRanking CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem derives_pre_total (S : program) (Q : assertion) :
  derives true (CQRules.pre true (successful_sequentialize (processes S)) Q) (processes S) Q.
Proof.
pose I := CQRules.pre true (network_tail (processes S)) Q.
apply: (@DNetworkConsequence true
  (CQRules.pre true (successful_sequentialize (processes S)) Q)
  (mask (DistributedLanguage.term (processes S)) I)
  (CQRules.pre true (successful_sequentialize (processes S)) Q) Q
  (process_count S) (processes S)).
- exact: semantic_le_refl.
- exact: tail_pre_post.
- apply: DDistributedTotal.
  + apply: CQRules.derives_complete.
    apply/(proj2 (CQRules.valid_iff _ _ _ _)).
    rewrite initialization_pre; exact: semantic_le_refl.
  + have H := @all_tail_invariants S true Q.
    elim: H=>[|bc bs Hb Hbs IH]; constructor=>//.
    exact: CQRules.derives_complete Hb.
  + exact: (@tail_network_ranking S Q).
  + exact: tail_pre_deadlock.
Qed.

Theorem derives_complete_total (P Q : assertion) (S : program) :
  DistributedHoare.valid true P S Q -> derives true P (processes S) Q.
Proof.
move=>H.
have Htranslated := proj1 (DistributedHoare.valid_translate_iff true P S Q) H.
have Hpre := proj1 (CQRules.valid_iff true P (successful_sequentialize (processes S)) Q) Htranslated.
apply: (@DNetworkConsequence true
  (CQRules.pre true (successful_sequentialize (processes S)) Q) Q P Q
  (process_count S) (processes S) Hpre (semantic_le_refl Q)).
exact: derives_pre_total.
Qed.

Theorem total_sound_complete (P Q : assertion) (S : program) :
  derives true P (processes S) Q <-> DistributedHoare.valid true P S Q.
Proof. split; [exact: DistributedHoare.derives_sound | exact: derives_complete_total]. Qed.

Theorem derives_pre total (S : program) (Q : assertion) :
  derives total (CQRules.pre total (successful_sequentialize (processes S)) Q) (processes S) Q.
Proof.
case: total; [exact: derives_pre_total | exact: DistributedPartialCompleteness.derives_pre_partial].
Qed.

Theorem derives_complete total (P Q : assertion) (S : program) :
  DistributedHoare.valid total P S Q -> derives total P (processes S) Q.
Proof.
case: total; [exact: derives_complete_total | exact: DistributedPartialCompleteness.derives_complete_partial].
Qed.

Theorem sound_complete total (P Q : assertion) (S : program) :
  derives total P (processes S) Q <-> DistributedHoare.valid total P S Q.
Proof. split; [exact: DistributedHoare.derives_sound | exact: derives_complete]. Qed.

End DistributedTotalCompleteness.
