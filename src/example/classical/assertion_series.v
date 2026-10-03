(* Order separation and continuous expectations. See EXPECTATION-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQAssertionSeries.
Import CQAssertion.
Local Notation C := hermitian.C.

Lemma positive_partial_sum (J : choiceType) (H : chsType)
    (f : J -> 'End(H)) :
  summable f -> (forall j, 0%:VF ⊑ f j) ->
  forall A, psum f A ⊑ sum f.
Proof.
move=>sf pf A; apply: lim_gev_near; first exact: norm_bounded_cvg sf.
exists A=>// B /= AB.
rewrite -(fsetUD_sub AB) psumU ?fdisjointXD // levDl.
by apply: sumv_ge0=>j _; apply: pf.
Qed.

Section Series.
Context {I J : choiceType} {H : chsType}.
Variable (w : J -> C) (F : J -> I -> 'FO(H)) (P : I -> 'FO(H)).
Hypothesis w_positive : forall j, 0 <= w j.
Hypothesis series_summable : forall i, summable (fun j => w j *: (F j i : 'End(H))).
Hypothesis series_value : forall i,
  (P i : 'End(H)) = sum (fun j => w j *: (F j i : 'End(H))).
Variable (rho : @CQState.state I H).

Definition series_term i j := w j * expect_term (F j) rho i.

Lemma series_term_positive i j : 0 <= series_term i j.
Proof. by apply: mulr_ge0; [apply: w_positive | apply: expect_term_ge0]. Qed.

Lemma series_partial_bound i A :
  psum (fun j => w j *: (F j i : 'End(H))) A ⊑ (P i : 'End(H)).
Proof.
rewrite series_value; apply: positive_partial_sum; first exact: series_summable.
by move=>j; apply: scalev_ge0; [apply: w_positive | apply: obsf_ge0].
Qed.

Lemma series_row_bound i A : psum (fun j => `|series_term i j|) A <= `|rho i|.
Proof.
rewrite /psum.
under eq_bigr do rewrite ger0_norm ?series_term_positive //.
rewrite /series_term /expect_term.
have E j : w j * \Tr (F j i \o rho i) = \Tr ((w j *: (F j i : 'End(H))) \o rho i).
  by rewrite linearZl /= linearZ.
under eq_bigr do rewrite E.
rewrite -linear_sum /= -linear_sumlz /=.
apply: (le_trans (y := expect_term P rho i)).
- apply/(lef_psdtr _ _); first exact: series_partial_bound.
  by rewrite psdlfE vdistr_ge0.
- apply: (le_trans (expect_term_le_trace P rho i)).
  by rewrite psd_trfnorm ?psdlfE ?vdistr_ge0.
Qed.

Lemma series_rectangle : exists B, forall A N,
  psum (fun i => psum (fun j => `|series_term i j|) N) A <= B.
Proof.
exists `|rho : {summable I -> 'End(H)}|=>A N.
apply: (le_trans _ (psum_norm_ler_norm rho A)).
by apply: ler_sum=>i _; apply: series_row_bound.
Qed.

Lemma series_row_value i : sum (series_term i) = expect_term P rho i.
Proof.
rewrite /expect_term series_value /series_term /expect_term.
rewrite (cvg_linearP_sum (f := fun A : 'End(H) => \Tr (A \o rho i))).
- by move=>a x y; rewrite linearPl /= linearP.
- by apply: norm_bounded_cvg; apply: series_summable.
- by apply: eq_sum=>j; rewrite /= linearZl /= linearZ.
Qed.

Lemma series_column_value j : sum (fun i => series_term i j) = w j * expect (F j) rho.
Proof.
change (sum (w j *: Summable.build (expect_summable (F j) rho)) = w j * expect (F j) rho).
by rewrite summable_sumZ.
Qed.

Lemma expect_series : expect P rho = sum (fun j => w j * expect (F j) rho).
Proof.
have E : expect_term P rho = fun i => sum (series_term i).
  by apply/funext=>i; rewrite series_row_value.
rewrite /expect E (pseries2_exchange_lim series_rectangle).
by apply: eq_sum=>j; rewrite series_column_value.
Qed.

Lemma expect_series_summable : summable (fun j => w j * expect (F j) rho).
Proof.
have B : exists B, forall N A,
    psum (fun j => psum (fun i => `|series_term i j|) A) N <= B.
  move: series_rectangle=>[B HB]; exists B=>N A.
  by rewrite /psum exchange_big; apply: HB.
have S := proj1 (proj2 (proj2 (pseries_ubounded_cvg B))).
have E : (fun j => sum (fun i => series_term i j)) = fun j => w j * expect (F j) rho.
  by apply/funext=>j; rewrite series_column_value.
by rewrite E in S.
Qed.
End Series.
End CQAssertionSeries.
