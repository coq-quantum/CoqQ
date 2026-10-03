(* Counterexample to the printed ordinary-distance phase bound (C6).
   See PHASE-COUNTEREXAMPLE-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap field_tactic ring_tactic.
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

Import Order.TTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From mathcomp.analysis Require Import exp trigo.
From quantum Require Import qtype.
From quantum.example.classical Require Import language fourier phase_estimation
  phase_bounds phase_probability.

Module ClassicalPhaseCounterexample.
Import ClassicalPhaseEstimation ClassicalPhaseBounds.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition witness_phase : R := 1 - 1 / 1024.
Definition zero_outcome : 3.-tuple bool := @ord2bseq 3 (ord0 : 'I_8).
Definition zero_amplitude : C := [< ''zero_outcome; output_state 3 witness_phase >].

Lemma witness_phase_bounds : 1 / 2 < witness_phase < 1.
Proof.
rewrite /witness_phase; apply/andP; split.
- have E : (1 - 1 / 1024 : R) = 1023 / 1024 by field.
  rewrite E ltr_pdivlMr //.
  have -> : (1 / 2 * 1024 : R) = 512 by field.
  by rewrite ltr_nat.
- rewrite ltrBlDr ltrDl; exact: divr_gt0.
Qed.

Lemma cosine_small a : `|a| <= (1 / 4 : R) -> 7 / 8 <= cos (a *+ 2).
Proof.
move=>Ha.
have Hsin := le_trans (ler_abs_sin a) Ha.
have Hq : (0 : R) <= 1 / 4 by apply: divr_ge0.
have Hsq : (sin a)^+2 <= (1 / 4)^+2.
  have Eabs : `|sin a|^+2 = (sin a)^+2 by rewrite -normrX ger0_norm ?sqr_ge0.
  rewrite -Eabs !expr2.
  exact: (ler_pM (normr_ge0 _) (normr_ge0 _) Hsin Hsin).
have E : (7 / 8 : R) = 1 - ((1 / 4)^+2) *+ 2 by field.
by rewrite E cos2x_sin lerD2l lerN2 lerMn2r /=.
Qed.

Lemma orbit_angle_bound (j : 'I_8) : `|pi * j%:R / 1024| <= (1 / 4 : R).
Proof.
have Hnonneg : (0 : R) <= pi * j%:R / 1024.
  by apply: divr_ge0=>//; apply: mulr_ge0; rewrite ?pi_ge0 ?ler0n.
rewrite ger0_norm // ler_pdivrMr //.
have E : (1 / 4 * 1024 : R) = 256 by field.
rewrite E.
apply: le_trans (_ : (4 * 8 : R) <= 256); last by rewrite -natrM ler_nat.
apply: ler_pM; rewrite ?pi_ge0 ?ler0n ?pi_le4 //.
by rewrite ler_nat; exact: ltnW (ltn_ord j).
Qed.

Lemma zero_amplitudeE : zero_amplitude =
  (8 : C)^-1 * \sum_(j < 8) expip (- (2 * j%:R / 1024) : R).
Proof.
rewrite /zero_amplitude amplitude_ordinal /phase_error /zero_outcome ord2bseqK /=
  mul0r subr0 -natrX /=.
congr (_ * _); apply: eq_bigr=>j _.
have E : (2 * witness_phase * j%:R : R) =
    (2 * j)%:R + - (2 * j%:R / 1024).
  rewrite /witness_phase natrM; ring.
by rewrite E expip_period.
Qed.

Lemma zero_amplitude_real : (7 / 8 : R) <= complex.Re zero_amplitude.
Proof.
rewrite zero_amplitudeE.
have E : ((8 : C)^-1)%R = (((8 : R)^-1)%R)%:C.
  by rewrite rmorphV ?unitfE // rmorph_nat.
rewrite E mulr_sumr linear_sum /=.
have Hb (j : 'I_8) : (7 / 8 : R) <= cos ((pi * j%:R / 1024) *+ 2).
  exact: cosine_small (orbit_angle_bound j).
have Er (j : 'I_8) :
  complex.Re ((((8 : R)^-1)%R)%:C * expip (- (2 * j%:R / 1024) : R)) =
  (8 : R)^-1 * cos ((pi * j%:R / 1024) *+ 2).
  rewrite expip.unlock /expi; simpc.
  rewrite cosN; congr (_ * cos _); rewrite !mulr2n; ring.
under eq_bigr do rewrite Er.
have E7 : (7 / 8 : R) = \sum_(j < 8) ((8 : R)^-1 * (7 / 8)).
  rewrite sumr_const card_ord -mulr_natr; field.
rewrite E7; apply: ler_sum=>j _; apply: ler_wpM2l; first by rewrite invr_ge0.
exact: Hb.
Qed.

Lemma zero_probability_gt_half : (1 / 2 : C) < `|zero_amplitude|^+2.
Proof.
have E78 : ((7 / 8 : R)%:C) = (7 / 8 : C).
  by rewrite rmorphM rmorphV ?unitfE // !rmorph_nat.
have Hr : ((7 / 8 : R)%:C) <= (complex.Re zero_amplitude)%:C.
  by rewrite lecR; exact: zero_amplitude_real.
have Ha : (complex.Re zero_amplitude)%:C <= `|complex.Re zero_amplitude|%:C.
  by rewrite lecR ler_norm.
have Hnorm := le_trans (le_trans Hr Ha) (normc_ge_Re zero_amplitude).
rewrite E78 in Hnorm.
have Hnonneg : (0 : C) <= 7 / 8 by apply: divr_ge0.
have Hsq : (7 / 8 : C)^+2 <= `|zero_amplitude|^+2.
  rewrite !expr2; exact: (ler_pM Hnonneg Hnonneg Hnorm Hnorm).
apply: lt_le_trans Hsq.
have E49 : (7 / 8 : C)^+2 = 49 / 64 by field.
rewrite E49 ltr_pdivlMr //.
have E32 : (1 / 2 * 64 : C) = 32 by field.
by rewrite E32 ltr_nat.
Qed.

Definition ordinary_success (m : 3.-tuple bool) :=
  `|witness_phase - (bseq2ord m)%:R / 8| < (1 / 2 : R).

Definition ordinary_success_probability : C :=
  \sum_(m : 3.-tuple bool | ordinary_success m)
    `|[< ''m; output_state 3 witness_phase >]|^+2.

Lemma zero_not_ordinary_success : ~~ ordinary_success zero_outcome.
Proof.
have Hphi := (andP witness_phase_bounds).1.
have Hphi0 : (0 : R) <= witness_phase.
  apply: le_trans (ltW Hphi); exact: divr_ge0.
by rewrite /ordinary_success /zero_outcome ord2bseqK /= mul0r subr0
  ger0_norm // ltNge (ltW Hphi).
Qed.

Theorem ordinary_success_below_half : ordinary_success_probability < (1 / 2 : C).
Proof.
have H := @ClassicalPhaseProbability.onb_event_complement_bound
  'Hs(3.-tuple bool) (Finite.clone (3.-tuple bool) _) t2tv
  (output_state 3 witness_phase) ordinary_success zero_outcome
  (output_state_dot 3 witness_phase) zero_not_ordinary_success.
apply: le_lt_trans H _.
change (1 - `|zero_amplitude|^+2 < (1 / 2 : C)).
rewrite ltrBlDl -ltrBlDr.
have E : (1 - 1 / 2 : C) = 1 / 2 by field.
by rewrite E; exact: zero_probability_gt_half.
Qed.

Corollary printed_phase_bound_counterexample :
  (0 <= witness_phase < 1) /\
  ~~ ((1 / 2 : C) <= ordinary_success_probability).
Proof.
split; last first.
  apply/negP=>Hbad.
  by have := lt_le_trans ordinary_success_below_half Hbad; rewrite ltxx.
have /andP[Hlo Hhi] := witness_phase_bounds; apply/andP; split=>//.
apply: le_trans (ltW Hlo); exact: divr_ge0.
Qed.

End ClassicalPhaseCounterexample.
