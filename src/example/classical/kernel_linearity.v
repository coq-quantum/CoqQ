(* Absolute-series linearity of cq kernels. See STATE_NOTES.md. *)
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
From quantum.example.classical Require Import state assertion expectation kernel
  predicate mixture mixture_expectation state_expectation.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.

Module CQKernelLinearity.
Import CQAssertion CQExpectation CQPredicate CQMixtureExpectation.
Section Kernels.
Context {I J A : choiceType} {H : chsType}.
Variable K : semType I J H H.

Definition weighted_input (w : A -> C) (d : A -> @CQState.state I H) a :
  {summable I -> 'End(H)} := w a *: (d a : {summable I -> 'End(H)}).

Definition weighted_output (w : A -> C) (d : A -> @CQState.state I H) a :
  {summable J -> 'End(H)} :=
  w a *: (CQKernel.apply K (d a) : {summable J -> 'End(H)}).

Lemma weighted_norm_bound w d a :
  `|weighted_output w d a| <= `|weighted_input w d a|.
Proof.
rewrite /weighted_output /weighted_input !normrZ.
apply: ler_wpM2l; first exact: normr_ge0.
exact: CQKernel.apply_l1_bound.
Qed.

Lemma weighted_output_summable w d : summable (weighted_input w d) ->
  summable (weighted_output w d).
Proof.
move=>Hs; pose x := Summable.build Hs.
apply: psum_ubounded_summable; exists `|x|=>F.
apply: (le_trans _ (psum_norm_ler_norm x F)).
by apply: ler_sum=>a _; apply: weighted_norm_bound.
Qed.

Lemma pairing_sum {L : choiceType} (Q : L -> 'FO(H))
  (x : {summable A -> {summable L -> 'End(H)}}) :
  pairing Q (sum x) = sum (fun a => pairing Q (x a)).
Proof.
have B : exists k : C, 0 < k /\
  forall y : {summable L -> 'End(H)}, `|pairing Q y| <= k * `|y|.
  exists 1; split=>// y; rewrite mul1r; exact: pairing_bound.
rewrite (summable_linear_sumG (f := pairing Q) x B).
by [].
Qed.

Theorem apply_weighted_sum w d (d0 : @CQState.state I H) :
  summable (weighted_input w d) ->
  (d0 : {summable I -> 'End(H)}) = sum (weighted_input w d) ->
  (CQKernel.apply K d0 : {summable J -> 'End(H)}) =
    sum (weighted_output w d).
Proof.
move=>Hs Hd; apply: CQStateExpectation.pairing_ext=>Q.
rewrite -expect_pairing -expect_wp expect_pairing Hd.
rewrite (pairing_sum Q (Summable.build (weighted_output_summable Hs))).
rewrite (pairing_sum (wp K Q) (Summable.build Hs)).
apply: eq_sum=>a.
by rewrite /weighted_input /weighted_output !linearZ /= -!expect_pairing expect_wp.
Qed.

Theorem apply_mix (w : Distr A) (d : A -> @CQState.state I H) :
  CQKernel.apply K (CQStateMixture.mix w d) =
    CQStateMixture.mix w (fun a => CQKernel.apply K (d a)).
Proof.
apply/(proj2 (CQStateExpectation.state_eq_iff_expect _ _))=>Q.
rewrite -expect_wp !CQMixtureExpectation.expect_mix.
by apply: eq_sum=>a; rewrite expect_wp.
Qed.
End Kernels.
End CQKernelLinearity.
