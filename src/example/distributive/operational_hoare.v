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


From quantum.example.distributive Require Import scheduler_results correspondence cq_input normalized_tests network_rules.

Module DistributedHoare.
Import DistributedLanguage DistributedSequentialization DistributedSchedulerResults
  DistributedCorrespondence CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition run := DistributedCQInput.run.

Theorem run_translate (S : program) rho :
  run S rho = CQHoare.run (successful_sequentialize (processes S)) rho.
Proof.
apply: DistributedCQInput.run_kernel=>m r out.
exact: denote_program_point.
Qed.

Definition valid total (P : assertion) (S : program) Q :=
  forall rho : @CQState.state cmem Hq,
  if total then expect P rho <= expect Q (run S rho)
  else expect (complement Q) (run S rho) <= expect (complement P) rho.

Definition normalized_valid total (P : assertion) (S : program) Q :=
  forall m (rho : 'FD1(Hq)),
  if total then expect P (CQState.point m (rho : 'FD(Hq))) <= expect Q (denote_program S m rho)
  else expect (complement Q) (denote_program S m rho) <=
    expect (complement P) (CQState.point m (rho : 'FD(Hq))).

Theorem valid_translate_iff total P (S : program) Q :
  valid total P S Q <-> CQHoare.valid total P (successful_sequentialize (processes S)) Q.
Proof.
split=>H rho; have Hs := H rho.
- by rewrite run_translate in Hs.
- by rewrite run_translate.
Qed.

Theorem valid_normalized_iff total P (S : program) Q :
  valid total P S Q <-> normalized_valid total P S Q.
Proof.
rewrite valid_translate_iff DistributedNormalizedTests.valid_normalized_iff.
split=>H m rho; have Hpoint := H m rho.
- by rewrite denote_program_sequentialize.
- by rewrite denote_program_sequentialize in Hpoint.
Qed.

Lemma valid_total_partial P S Q : valid true P S Q -> valid false P S Q.
Proof.
move=>H; apply/(proj2 (valid_translate_iff _ _ _ _)).
apply: CQHoare.valid_total_partial; exact: (proj1 (valid_translate_iff _ _ _ _) H).
Qed.

Lemma valid_consequence total P Q P' Q' S :
  semantic_le P' P -> semantic_le Q Q' -> valid total P S Q -> valid total P' S Q'.
Proof.
move=>HP HQ H; apply/(proj2 (valid_translate_iff _ _ _ _)).
apply: CQHoare.valid_consequence HP HQ _.
exact: (proj1 (valid_translate_iff _ _ _ _) H).
Qed.

Theorem derives_sound total P (S : program) Q :
  DistributedNetworkRules.derives total P (processes S) Q -> valid total P S Q.
Proof.
move=>D; apply/(proj2 (valid_translate_iff _ _ _ _)).
exact: DistributedNetworkRules.derives_translate_sound D.
Qed.

Theorem translated_derives_iff total P (S : program) Q :
  CQRules.derives total P (successful_sequentialize (processes S)) Q <-> valid total P S Q.
Proof. rewrite valid_translate_iff; exact: CQRules.sound_complete. Qed.

End DistributedHoare.
