(* Exact phase-estimation identities; see CASE-STUDIES.md. *)
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
From quantum.example.classical Require Import language fourier.

Module ClassicalPhaseEstimation.
Import ClassicalLanguage.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition tuple_fourier n : 'FU('Hs (n.-tuple bool)) :=
  ClassicalFourier.tuple_fourier n.

Definition phase_diagonal n (phi : R) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of expmxip t2tv (fun i : n.-tuple bool => (bseq2ord i)%:R) (2 * phi)].

Definition phase_vector n (phi : R) := phase_diagonal n phi uniformtv.

Lemma phase_vector_dot n phi : [<phase_vector n phi; phase_vector n phi>] = 1.
Proof. by rewrite /phase_vector isof_dot ns_dot. Qed.
HB.instance Definition _ n phi := isNormalState.Build _ (phase_vector n phi)
  (phase_vector_dot n phi).

Lemma phase_vectorE n phi : phase_vector n phi =
  (sqrtC 2%:R ^- n) *:
    \sum_(i : n.-tuple bool) expip ((bseq2ord i)%:R * (2 * phi)) *: ''i.
Proof.
rewrite /phase_vector uniformtvE linearZ /= linear_sum /=.
rewrite card_tuple card_bool natrX sqrtCX_nat.
by congr (_ *: _); apply eq_bigr=>i _; rewrite /phase_diagonal expmxipEt.
Qed.

Definition output_state n (phi : R) := (tuple_fourier n)^A (phase_vector n phi).

Lemma output_state_dot n phi : [<output_state n phi; output_state n phi>] = 1.
Proof. by rewrite /output_state isof_dot ns_dot. Qed.
HB.instance Definition _ n phi := isNormalState.Build _ (output_state n phi)
  (output_state_dot n phi).

Lemma fourier_coefficient n (m i : n.-tuple bool) :
  [< ''i; QFTbv m >] = (sqrtC 2%:R ^- n) *
    expip (2%:R * (bseq2ord m * bseq2ord i)%:R / 2%:R ^+ n).
Proof.
rewrite QFTbvE dotpZr dotp_sumr (bigD1 i) //= big1.
- by move=>j /negPf Eji; rewrite dotpZr onb_dot eq_sym Eji mulr0.
- by rewrite dotpZr ns_dot mulr1 addr0.
Qed.

Theorem phase_output_amplitude n phi (m : n.-tuple bool) :
  [< ''m; output_state n phi >] =
  (sqrtC 2%:R ^- n)^+2 *
    \sum_(i : n.-tuple bool)
      expip ((bseq2ord i)%:R * (2 * phi) -
        2%:R * (bseq2ord m * bseq2ord i)%:R / 2%:R ^+ n).
Proof.
rewrite /output_state adj_dotEr /tuple_fourier PUnitaryE phase_vectorE
  dotpZr dotp_sumr !mulr_sumr.
apply eq_bigr=>i _.
rewrite dotpZr -conj_dotp fourier_coefficient rmorphM /=
  geC0_conj ?invr_ge0 ?exprn_ge0 ?sqrtC_ge0 // -expipNC.
by rewrite -!mulrA [expip _ * _]mulrCA -expipD mulrA.
Qed.

Lemma phase_vector_exact n (m : n.-tuple bool) :
  phase_vector n ((bseq2ord m)%:R / 2%:R ^+ n) = QFTbv m.
Proof.
rewrite phase_vectorE QFTbvE; congr (_ *: _); apply eq_bigr=>i _.
congr (_ *: _); congr (expip _).
by rewrite natrM mulrCA !mulrA
  [2 * (bseq2ord i)%:R * (bseq2ord m)%:R]mulrAC.
Qed.

Theorem exact_phase_output n (m : n.-tuple bool) :
  output_state n ((bseq2ord m)%:R / 2%:R ^+ n) = ''m.
Proof.
by rewrite /output_state phase_vector_exact /tuple_fourier PUnitaryEV.
Qed.

Section Eigenstate.
Variable (T : ihbFinType) (U : 'FU('Hs T)) (u : 'Hs T) (phi : R).
Hypothesis eigenstate : U u = expip (2 * phi) *: u.

Lemma eigen_power j : (U%:VF ^+ j) u = expip ((j%:R) * (2 * phi)) *: u.
Proof.
elim: j=>[|j IH].
- by rewrite expr0 lfunE mul0r expip0 scale1r.
- rewrite exprS lfunE /= IH linearZ /= eigenstate scalerA -expipD.
  congr (_ *: _); congr (expip _).
  by rewrite -[j.+1]addn1 natrD [(j%:R + 1) * _]mulrDl mul1r.
Qed.

Definition controlled_powers n : 'FU('Hs ((n.-tuple bool) * T)%type) :=
  [unitary of Multiplexer (fun i : n.-tuple bool =>
    [unitary of U%:VF ^+ (bseq2ord i)])].

Lemma phase_kickback n :
  controlled_powers n (uniformtv ⊗t u) = phase_vector n phi ⊗t u.
Proof.
rewrite uniformtvE linearZl /= linear_sumlz /= linearZ /= linear_sum /=
  phase_vectorE linearZl /= linear_sumlz /=.
rewrite card_tuple card_bool natrX sqrtCX_nat.
congr (_ *: _); apply eq_bigr=>i _.
by rewrite /controlled_powers MultiplexerEt eigen_power linearZ /= linearZl.
Qed.
End Eigenstate.

End ClassicalPhaseEstimation.
