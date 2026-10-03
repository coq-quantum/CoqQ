(* Exact finite Fourier amplitudes for the printed order-finding circuit. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences exp trigo.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import language fourier phase_estimation
  modular_unitary order_finding.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalOrderFindingState.
Import ClassicalModularUnitary ClassicalOrderFinding.
Section Circuit.
Variables (N L t : nat).
Hypothesis HN : (1 < N)%N.
Hypothesis capacity : (N <= 2 ^ L)%N.

Definition controlled_state b :=
  @controlled_powers N L t HN capacity b
    (uniformtv ⊗t (@one_state N L HN capacity : 'Hs(L.-tuple bool))).

Definition inverse_fourier_left : 'FU('Hs((t.-tuple bool) * (L.-tuple bool))%type) :=
  [unitary of (ClassicalFourier.tuple_fourier t)^A ⊗f (\1 : 'FU('Hs(L.-tuple bool)))].

Definition output_state b := inverse_fourier_left (controlled_state b).

Lemma controlled_state_normal b : [< controlled_state b; controlled_state b >] = 1.
Proof. by rewrite /controlled_state isof_dot tentv_dot !ns_dot mulr1. Qed.
HB.instance Definition _ b := isNormalState.Build _ (controlled_state b)
  (controlled_state_normal b).

Lemma output_state_normal b : [< output_state b; output_state b >] = 1.
Proof. by rewrite /output_state isof_dot ns_dot. Qed.
HB.instance Definition _ b := isNormalState.Build _ (output_state b)
  (output_state_normal b).

Theorem controlled_stateE b : coprime b N -> controlled_state b =
  (sqrtC 2%:R ^- t) *:
    \sum_(j : t.-tuple bool) (''j ⊗t
      ''(@residue_bits N (modulus_positive HN) L capacity (b ^ (bseq2ord j))%N)).
Proof.
move=>Hb; rewrite /controlled_state uniformtvE linearZl /= linear_sumlz /=
  linearZ /= linear_sum /= card_tuple card_bool natrX sqrtCX_nat.
congr (_ *: _); apply: eq_bigr=>j _.
rewrite controlled_powersE (@total_modular_unitaryE N L HN capacity b Hb) /one_state /one_bits
  modular_power_residue muln1.
by [].
Qed.

Lemma inverse_fourier_coefficient (m j : t.-tuple bool) :
  [< ''m; (ClassicalFourier.tuple_fourier t)^A ''j >] =
  (sqrtC 2%:R ^- t) *
    expip (- (2%:R * (bseq2ord m * bseq2ord j)%:R / 2%:R ^+ t)).
Proof.
rewrite adj_dotEr /ClassicalFourier.tuple_fourier PUnitaryE -conj_dotp
  ClassicalPhaseEstimation.fourier_coefficient rmorphM /=
  geC0_conj ?invr_ge0 ?exprn_ge0 ?sqrtC_ge0 // -expipNC.
by [].
Qed.

Theorem output_amplitude b (m : t.-tuple bool) (y : L.-tuple bool) :
  coprime b N ->
  [< ''m ⊗t ''y; output_state b >] =
  (sqrtC 2%:R ^- t)^+2 *
    \sum_(j : t.-tuple bool)
      expip (- (2%:R * (bseq2ord m * bseq2ord j)%:R / 2%:R ^+ t)) *
      (y == @residue_bits N (modulus_positive HN) L capacity (b ^ (bseq2ord j))%N)%:R.
Proof.
move=>Hb; rewrite /output_state (controlled_stateE Hb) linearZ /= linear_sum /=
  dotpZr dotp_sumr !mulr_sumr.
apply: eq_bigr=>j _.
rewrite /inverse_fourier_left tentf_apply lfunE tentv_dot
  inverse_fourier_coefficient onb_dot.
by rewrite expr2 !mulrA.
Qed.

Definition outcome_probability b (m : t.-tuple bool) : C :=
  \sum_(y : L.-tuple bool) `|[< ''m ⊗t ''y; output_state b >]|^+2.

Theorem outcome_probabilityE b m : coprime b N -> outcome_probability b m =
  \sum_(y : L.-tuple bool)
    `| (sqrtC 2%:R ^- t)^+2 *
      \sum_(j : t.-tuple bool)
        expip (- (2%:R * (bseq2ord m * bseq2ord j)%:R / 2%:R ^+ t)) *
        (y == @residue_bits N (modulus_positive HN) L capacity (b ^ (bseq2ord j))%N)%:R |^+2.
Proof. move=>Hb; apply: eq_bigr=>y _; by rewrite output_amplitude. Qed.

End Circuit.
End ClassicalOrderFindingState.
