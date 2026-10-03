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


From quantum.example.distributive Require Import network_rules network_pre operational_hoare rendezvous_all residual_semantics.

Module DistributedPartialCompleteness.
Import DistributedLanguage DistributedSequentialization DistributedNetworkRules DistributedNetworkPre
  DistributedResidualSemantics DistributedAllRendezvous CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem derives_pre_partial (S : program) (Q : assertion) :
  derives false (CQRules.pre false (successful_sequentialize (processes S)) Q) (processes S) Q.
Proof.
pose I := CQRules.pre false (network_tail (processes S)) Q.
apply: (@DNetworkConsequence false
  (CQRules.pre false (successful_sequentialize (processes S)) Q)
  (mask (DistributedLanguage.term (processes S)) I)
  (CQRules.pre false (successful_sequentialize (processes S)) Q) Q
  (process_count S) (processes S)).
- exact: semantic_le_refl.
- exact: tail_pre_post.
- apply: DDistributedPartial.
  + apply: CQRules.derives_complete.
    apply/(proj2 (CQRules.valid_iff _ _ _ _)).
    rewrite initialization_pre; exact: semantic_le_refl.
  + have H := @all_tail_invariants S false Q.
    elim: H=>[|bc bs Hb Hbs IH]; constructor=>//.
    exact: CQRules.derives_complete Hb.
Qed.

Theorem derives_complete_partial (P Q : assertion) (S : program) :
  DistributedHoare.valid false P S Q -> derives false P (processes S) Q.
Proof.
move=>H.
have Htranslated := proj1 (DistributedHoare.valid_translate_iff false P S Q) H.
have Hpre := proj1 (CQRules.valid_iff false P (successful_sequentialize (processes S)) Q) Htranslated.
apply: (@DNetworkConsequence false
  (CQRules.pre false (successful_sequentialize (processes S)) Q) Q P Q
  (process_count S) (processes S) Hpre (semantic_le_refl Q)).
exact: derives_pre_partial.
Qed.

Theorem partial_sound_complete (P Q : assertion) (S : program) :
  derives false P (processes S) Q <-> DistributedHoare.valid false P S Q.
Proof. split; [exact: DistributedHoare.derives_sound | exact: derives_complete_partial]. Qed.

End DistributedPartialCompleteness.
