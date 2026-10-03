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
From quantum.example.classical Require Import state assertion expectation mixture.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQMixtureExpectation.
Import CQAssertion CQExpectation.
Section Mixtures.
Context {I J : choiceType} {H : chsType}.
Variable P : J -> 'FO(H).

Lemma pairing_linear : linear (@pairing J H P).
Proof.
move=>a x y.
have E : pair_terms P (a *: x + y) = a *: pair_terms P x + pair_terms P y.
  apply/summableP=>i; rewrite !summableE /= /pair_term !summableE.
  by rewrite linearPr /= linearP.
by rewrite /pairing E summable_sumD summable_sumZ.
Qed.

HB.instance Definition _ := GRing.isLinear.Build C
  {summable J -> 'End(H)} C *:%R (@pairing J H P) pairing_linear.

Lemma expect_mix (w : Distr I) (d : I -> @CQState.state J H) :
  expect P (CQStateMixture.mix w d) = sum (fun i => w i * expect P (d i)).
Proof.
change (pairing P (sum (CQStateMixture.terms w d)) =
  sum (fun i => w i * expect P (d i))).
have B : exists k : C, 0 < k /\ forall x : {summable J -> 'End(H)},
  `|pairing P x| <= k * `|x|.
  exists 1; split=>// x; rewrite mul1r; exact: pairing_bound.
rewrite (summable_linear_sumG (f := pairing P) (CQStateMixture.terms w d) B).
apply: eq_sum=>i.
by rewrite /CQStateMixture.terms /= /CQStateMixture.term linearZ /= -expect_pairing.
Qed.
End Mixtures.
End CQMixtureExpectation.
