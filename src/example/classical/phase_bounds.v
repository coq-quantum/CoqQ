(* Exact geometric phase amplitudes and bounds; see CASE-STUDIES.md. *)
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

From mathcomp.analysis Require Import exp trigo.
From quantum Require Import qtype.
From quantum.example.classical Require Import language fourier phase_estimation.

Module ClassicalPhaseBounds.
Import ClassicalPhaseEstimation.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition phase_error n (phi : R) (m : n.-tuple bool) : R :=
  phi - (bseq2ord m)%:R / 2%:R ^+ n.

Lemma amplitude_ordinal n phi (m : n.-tuple bool) :
  [< ''m; output_state n phi >] =
  (2%:R ^+ n : C)^-1 *
    \sum_(j < expn 2 n) expip (2 * phase_error phi m * j%:R).
Proof.
rewrite phase_output_amplitude !exprVn -exprM mulnC exprM sqrtCK big_bseq.
congr (_ * _); apply: eq_bigr=>j _; rewrite ord2bseqK.
congr (expip _); rewrite /phase_error natrM mulrBr !mulrA.
rewrite [j%:R * 2]mulrC mulrBl.
by congr (_ - _); rewrite mulrAC.
Qed.

Theorem amplitude_geometric n phi (m : n.-tuple bool) :
  expip (2 * phase_error phi m) != 1 ->
  [< ''m; output_state n phi >] =
  (2%:R ^+ n : C)^-1 *
    ((1 - expip (2 * phase_error phi m * (2%:R ^+ n))) /
      (1 - expip (2 * phase_error phi m))).
Proof. by move=>H; rewrite amplitude_ordinal (expip_sum _ H) natrX. Qed.

Lemma exponential_norm (x : R) : `|expip x| = (1 : C).
Proof.
apply/eqP; rewrite -(@eqrXn2 C 2) ?normr_ge0 ?ler01 //.
rewrite expr1n sqr_normc conjcC.
by rewrite -(@expipNC R x) -expipD subrr expip0.
Qed.

Lemma exponential_difference_bound (x : R) :
  `|1 - expip x| <= (2 : C).
Proof.
apply: (le_trans (ler_normB _ _)).
by rewrite normr1 exponential_norm.
Qed.

Theorem amplitude_bound n phi (m : n.-tuple bool) :
  expip (2 * phase_error phi m) != 1 ->
  `|[< ''m; output_state n phi >]| <=
    (2%:R ^+ n : C)^-1 *
      (2 / `|1 - expip (2 * phase_error phi m)|).
Proof.
move=>H.
have HN : (2%:R ^+ n : C) \is a GRing.unit.
  by rewrite unitfE expf_neq0.
have Hd : (1 - expip (2 * phase_error phi m)) \is a GRing.unit.
  by rewrite unitfE subr_eq0 eq_sym.
rewrite (amplitude_geometric H) !normrM !normrV //
  ger0_norm ?exprn_ge0 //.
apply: ler_wpM2l; first by rewrite invr_ge0 exprn_ge0.
apply: ler_wpM2r; first by rewrite invr_ge0 normr_ge0.
exact: exponential_difference_bound.
Qed.

Theorem probability_bound n phi (m : n.-tuple bool) :
  expip (2 * phase_error phi m) != 1 ->
  ([< output_state n phi; ''m >] * [< ''m; output_state n phi >]) <=
    ((2%:R ^+ n : C)^-1 *
      (2 / `|1 - expip (2 * phase_error phi m)|))^+2.
Proof.
move=>H; rewrite -conj_dotp mulrC -sqr_normc.
have HB := amplitude_bound H.
rewrite !expr2.
exact: (ler_pM (normr_ge0 _) (normr_ge0 _) HB HB).
Qed.

End ClassicalPhaseBounds.
