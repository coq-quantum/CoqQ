(* Classical-quantum assertions and expectation, following Feng and Ying,
   Definitions 3.5 and 3.7. See EXPECTATION-NOTES.md and REFERENCE.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology.
From quantum Require Import hermitian cpo quantum summable.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module CQAssertion.

(* Approved domain repair, 2026-10-03: limits use all effect-valued
   functions; the paper's countable/definable assertions remain below. *)
Section SemanticAssertions.
Context {I : choiceType} {H : chsType}.

Definition semantic_assertion := I -> 'FO(H).
Definition semantic_le (P Q : semantic_assertion) :=
  forall i, (P i : 'End(H)) ⊑ (Q i : 'End(H)).
Definition semantic_bottom : semantic_assertion := fun _ => (0%:VF : 'FO(H)).
Definition semantic_top : semantic_assertion := fun _ => (\1 : 'FO(H)).
Definition semantic_chain (c : nat -> semantic_assertion) :=
  forall n, semantic_le (c n) (c n.+1).
Definition semantic_sup (c : nat -> semantic_assertion) : semantic_assertion :=
  fun i => LfunCPO.oflub (fun n => c n i).

Lemma semantic_le_refl P : semantic_le P P.
Proof. by move=>i. Qed.

Lemma semantic_le_trans P Q R :
  semantic_le P Q -> semantic_le Q R -> semantic_le P R.
Proof. by move=>PQ QR i; exact: le_trans (PQ i) (QR i). Qed.

Lemma semantic_le_anti P Q : semantic_le P Q -> semantic_le Q P -> P = Q.
Proof.
move=>PQ QP; apply/funext=>i; apply/val_inj/le_anti/andP.
by split; [apply: PQ | apply: QP].
Qed.

Lemma semantic_bottom_le P : semantic_le semantic_bottom P.
Proof. by move=>i; apply: obsf_ge0. Qed.

Lemma semantic_le_top P : semantic_le P semantic_top.
Proof. by move=>i; apply: obsf_le1. Qed.

Lemma semantic_point_chain c : semantic_chain c ->
  forall i, chain (fun n => c n i).
Proof. by move=>inc i n; rewrite leEsub; apply: inc. Qed.

Lemma semantic_sup_upper c : semantic_chain c ->
  forall n, semantic_le (c n) (semantic_sup c).
Proof.
move=>inc n i; move: (LfunCPO.oflub_ub (semantic_point_chain inc i) n).
by rewrite leEsub.
Qed.

Lemma semantic_sup_least c Q : semantic_chain c ->
  (forall n, semantic_le (c n) Q) -> semantic_le (semantic_sup c) Q.
Proof.
move=>inc bound i.
have B : forall n, c n i ⊑ Q i by move=>n; rewrite leEsub; apply: bound.
move: (LfunCPO.oflub_least (semantic_point_chain inc i) B).
by rewrite leEsub.
Qed.

Theorem semantic_omega_cpo :
  (forall P, semantic_le semantic_bottom P) /\
  (forall c, semantic_chain c ->
    (forall n, semantic_le (c n) (semantic_sup c)) /\
    (forall Q, (forall n, semantic_le (c n) Q) -> semantic_le (semantic_sup c) Q)).
Proof.
split; first exact: semantic_bottom_le.
move=>c inc; split.
  exact: semantic_sup_upper inc.
by move=>Q bound; exact: semantic_sup_least inc bound.
Qed.

End SemanticAssertions.

Section Assertions.
Context {I : choiceType} {H : chsType}.
Variable (Formula : Type) (holds : Formula -> I -> Prop).

Record assertion := Assertion {
  assertion_value : I -> 'FO(H);
  assertion_countable :
    countable [set A | exists i, assertion_value i = A];
  assertion_definable : forall A,
    (exists i, assertion_value i = A) ->
    exists p, forall i, holds p i <-> assertion_value i = A
}.

Coercion assertion_value : assertion >-> Funclass.

Definition assertion_le (P Q : assertion) :=
  forall i, (P i : 'End(H)) ⊑ (Q i : 'End(H)).

Lemma assertion_le_refl (P : assertion) : assertion_le P P.
Proof. by move=>i. Qed.

Lemma assertion_le_trans (P Q R : assertion) :
  assertion_le P Q -> assertion_le Q R -> assertion_le P R.
Proof. by move=>PQ QR i; apply: (le_trans (PQ i) (QR i)). Qed.

End Assertions.

Section Expectation.
Context {I : choiceType} {H : chsType}.
Implicit Type (P Q : I -> 'FO(H)) (rho : {vdistr I -> 'End(H)}).

Definition expect_term P rho i := \Tr (P i \o rho i).

Lemma expect_term_ge0 P rho i : 0 <= expect_term P rho i.
Proof. by apply/trlfM_ge0; [apply: obsf_ge0 | apply: vdistr_ge0]. Qed.

Lemma expect_term_le_trace P rho i : expect_term P rho i <= \Tr (rho i).
Proof.
rewrite /expect_term -{2}(comp_lfun1l (rho i)).
apply/(lef_psdtr (P i) (\1)); first apply: obsf_le1.
by rewrite psdlfE; apply: vdistr_ge0.
Qed.

Lemma expect_term_norm_le P rho i : `|expect_term P rho i| <= `|rho i|.
Proof.
rewrite ger0_norm ?expect_term_ge0// psd_trfnorm.
by rewrite psdlfE; apply: vdistr_ge0.
apply: expect_term_le_trace.
Qed.

Lemma expect_summable P rho : summable (expect_term P rho).
Proof.
apply: psum_ubounded_summable.
move: (summable_bounded (rho : {summable I -> 'End(H)}))=>[M _ BM].
exists M=>J; apply: (le_trans _ (BM J)).
by rewrite /psum; apply: ler_sum=>i _; apply: expect_term_norm_le.
Qed.

Definition expect P rho : C := sum (expect_term P rho).

Lemma expect_ge0 P rho : 0 <= expect P rho.
Proof.
rewrite /expect /sum; apply: etlim_ge.
exact: (summable_cvg (f := Summable.build (expect_summable P rho))).
by move=>J; rewrite /psum; apply: sumr_ge0=>i _; apply: expect_term_ge0.
Qed.

Lemma expect_le_trace P rho : expect P rho <= \Tr (sum rho).
Proof.
rewrite /expect /sum; apply: etlim_le.
exact: (summable_cvg (f := Summable.build (expect_summable P rho))).
move=>J; apply: (le_trans (y := \Tr (psum rho J))).
rewrite /psum linear_sum/=; apply: ler_sum=>i _.
apply: expect_term_le_trace.
by apply/lef_trlf/psum_vdistr_lev_sum.
Qed.

Lemma expect_le1 P rho : expect P rho <= 1.
Proof.
apply: (le_trans (expect_le_trace P rho)).
rewrite -psd_trfnorm; first by rewrite psdlfE; apply: vdistr_sum_ge0.
apply: vdistr_sum_le1.
Qed.

Lemma expect_real P rho : expect P rho \is Num.real.
Proof. apply/ger0_real/expect_ge0. Qed.

Lemma expect_mono P Q rho :
  (forall i, (P i : 'End(H)) ⊑ (Q i : 'End(H))) ->
  expect P rho <= expect Q rho.
Proof.
move=>PQ; rewrite /expect /sum; apply: ler_etlim.
exact: (summable_cvg (f := Summable.build (expect_summable P rho))).
exact: (summable_cvg (f := Summable.build (expect_summable Q rho))).
move=>J; rewrite /psum; apply: ler_sum=>i _.
rewrite /expect_term; move: (PQ (val i))=>/lef_psdtr Pi; apply: Pi.
by rewrite psdlfE; apply: vdistr_ge0.
Qed.

Lemma expect_zero rho : expect (fun _ => (0%:VF : 'FO(H))) rho = 0.
Proof.
rewrite /expect /expect_term.
have -> : (fun i => \Tr (0%:VF \o rho i)) = (fun _ : I => (0 : C)).
  by apply/funext=>i; rewrite comp_lfun0l linear0.
apply: summable_sum_cst0.
Qed.

Lemma expect_identity rho :
  expect (fun _ => (\1 : 'FO(H))) rho = \Tr (sum rho).
Proof.
rewrite /expect /expect_term.
have -> : (fun i => \Tr (\1 \o rho i)) = (@lftrace H \o rho)%FUN.
  by apply/funext=>i; rewrite comp_lfun1l.
symmetry; apply: summable_linear_sumG.
exists 1; split=>// v; rewrite mul1r; apply: trlf_trfnorm.
Qed.

Lemma expect_singleton P rho i :
  (forall j, j != i -> rho j = 0) ->
  expect P rho = \Tr (P i \o rho i).
Proof.
move=>single; rewrite /expect (fin_supp_sum (S := [fset i]%fset)) ?psum1//.
by move=>j; rewrite inE=>/single rj; rewrite /expect_term rj comp_lfun0r linear0.
Qed.

Definition mask (b : pred I) P : I -> 'FO(H) :=
  fun i => if b i then P i else (0%:VF : 'FO(H)).

Definition conditional (b : pred I) P Q : I -> 'FO(H) :=
  fun i => if b i then P i else Q i.

Lemma expect_mask_le (b : pred I) P rho : expect (mask b P) rho <= expect P rho.
Proof.
apply: expect_mono=>i; rewrite /mask; case: (b i)=>//.
apply: obsf_ge0.
Qed.

Lemma expect_mask_true P rho : expect (mask predT P) rho = expect P rho.
Proof. by []. Qed.

Lemma expect_mask_false P rho : expect (mask pred0 P) rho = 0.
Proof. exact: expect_zero. Qed.

Lemma expect_conditional (b : pred I) P Q rho :
  expect (conditional b P Q) rho =
    expect (mask b P) rho + expect (mask (predC b) Q) rho.
Proof.
rewrite /expect -(summable_sumD
  (Summable.build (expect_summable (mask b P) rho))
  (Summable.build (expect_summable (mask (predC b) Q) rho))).
congr (sum _); apply/funext=>i.
by rewrite /= /expect_term /conditional /mask /=;
  case: (b i); rewrite comp_lfun0l linear0 ?add0r ?addr0.
Qed.

Definition complement P : I -> 'FO(H) :=
  fun i => ObsLf_Build (cplmt_obs (P i)).

Lemma expect_complement_sum P rho :
  expect (complement P) rho + expect P rho = \Tr (sum rho).
Proof.
rewrite -(expect_identity rho) /expect -(summable_sumD
  (Summable.build (expect_summable (complement P) rho))
  (Summable.build (expect_summable P rho))).
congr (sum _); apply/funext=>i.
by rewrite /= /expect_term /complement /= /cplmt
  linearBl /= linearB /= subrK.
Qed.

Lemma expect_complement P rho :
  expect (complement P) rho = \Tr (sum rho) - expect P rho.
Proof. by rewrite -(expect_complement_sum P rho) addrK. Qed.

End Expectation.
End CQAssertion.
