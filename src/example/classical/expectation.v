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


Module CQExpectation.
Import CQAssertion.
Section Pairing.
Context {I : choiceType} {H : chsType}.
Local Notation C := hermitian.C.

Lemma expect_point (P : I -> 'FO(H)) i (rho : 'FD(H)) :
  expect P (CQState.point i rho) = \Tr (P i \o rho).
Proof.
rewrite (@expect_singleton I H P (CQState.point i rho) i).
  by move=>j /negPf ji; rewrite CQState.pointE ji.
by rewrite CQState.pointE eqxx.
Qed.

Lemma semantic_le_iff_expect (P Q : I -> 'FO(H)) :
  semantic_le P Q <-> forall rho : @CQState.state I H,
    expect P rho <= expect Q rho.
Proof.
split; first by move=>PQ rho; apply: expect_mono.
move=>PQ i; apply/lef_trden=>r.
by move: (PQ (CQState.point i r)); rewrite !expect_point.
Qed.

Lemma trace_pair_bound (P : 'FO(H)) (x : 'End(H)) :
  `|\Tr (P \o x)| <= `|x|.
Proof.
apply: (le_trans (trlf_trfnorm _)).
apply: (le_trans (trfnormMr _ _)).
rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
exact: bound1f_i2fnorm.
Qed.

Definition pair_term (P : I -> 'FO(H)) (x : {summable I -> 'End(H)}) i :=
  \Tr (P i \o x i).

Lemma pair_term_summable P x : summable (pair_term P x).
Proof.
apply: psum_ubounded_summable.
move: (summable_bounded x)=>[M _ BM].
exists M=>J; apply: (le_trans _ (BM J)).
by rewrite /psum; apply: ler_sum=>i _; apply: trace_pair_bound.
Qed.

Definition pair_terms P x := Summable.build (pair_term_summable P x).
Definition pairing P x := sum (pair_terms P x).

Lemma pair_termsB P x y : pair_terms P (x-y) = pair_terms P x - pair_terms P y.
Proof.
apply/summableP=>i; rewrite summableE /= /pair_term summableE.
by rewrite linearBr /= linearB.
Qed.

Lemma pair_terms_norm P x : `|pair_terms P x| <= `|x|.
Proof.
change (summable_norm (pair_terms P x) <= summable_norm x).
rewrite /summable_norm; apply: ler_etlim.
- exact: summable_norm_is_cvg.
- exact: summable_norm_is_cvg.
- move=>J; rewrite /psum; apply: ler_sum=>i _.
  exact: trace_pair_bound.
Qed.

Lemma pairing_bound P x : `|pairing P x| <= `|x|.
Proof.
apply: (le_trans (summable_sum_ler_norm _)).
change (summable_norm (pair_terms P x) <= summable_norm x).
exact: pair_terms_norm.
Qed.

Lemma pairingB P x y : pairing P (x-y) = pairing P x - pairing P y.
Proof. by rewrite /pairing pair_termsB summable_sumB. Qed.

Lemma pairing_continuous P : continuous (pairing P).
Proof.
move=>x s /= /nbhs_ballP [e egt0 Pb]; apply/nbhs_ballP.
exists e=>// y /= Py; apply: Pb; move: Py.
rewrite -!ball_normE /= -pairingB; apply: le_lt_trans.
exact: pairing_bound.
Qed.

Lemma expect_pairing P (rho : @CQState.state I H) :
  expect P rho = pairing P (rho : {summable I -> 'End(H)}).
Proof. by []. Qed.

Lemma expect_cvg P (f : nat -> @CQState.state I H) (rho : @CQState.state I H) :
  (f n : {summable I -> 'End(H)}) @[n --> \oo] -->
    (rho : {summable I -> 'End(H)}) ->
  expect P (f n) @[n --> \oo] --> expect P rho.
Proof.
move=>Cf; change (pairing P (f n) @[n --> \oo] --> pairing P rho).
apply: continuous_cvg; first exact: pairing_continuous.
exact: Cf.
Qed.

Lemma expect_chain_sup P (f : nat -> @CQState.state I H) :
  nondecreasing_seq f ->
  expect P (f n) @[n --> \oo] --> expect P (CQState.chain_sup f).
Proof.
move=>inc; apply: expect_cvg.
rewrite /CQState.chain_sup vdlimE; exact: CQState.chain_converges.
Qed.
End Pairing.
End CQExpectation.
