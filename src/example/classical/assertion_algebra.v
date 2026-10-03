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


Module CQAssertionAlgebra.
Import CQAssertion.
Section Algebra.
Context {I : choiceType} {H : chsType}.
Local Notation C := hermitian.C.

Lemma expect_finite_linear (J : finType) (w : J -> C)
    (F : J -> I -> 'FO(H)) (P : I -> 'FO(H))
    (rho : @CQState.state I H) :
  (forall i, (P i : 'End(H)) = \sum_j w j *: (F j i : 'End(H))) ->
  expect P rho = \sum_j w j * expect (F j) rho.
Proof.
move=>PE.
pose terms j := w j *: Summable.build (expect_summable (F j) rho).
have E : expect_term P rho = (\sum_j terms j : {summable I -> C}).
  apply/funext=>i; rewrite summable_sumE /expect_term PE linear_sumlz /= linear_sum /=.
  apply: eq_bigr=>j _; rewrite /terms /= /expect_term.
  by rewrite linearZl /= linearZ /=.
rewrite /expect E summable_sum_sum.
apply: eq_bigr=>j _; by rewrite /terms summable_sumZ.
Qed.

Lemma mask_le (p : pred I) (P Q : I -> 'FO(H)) :
  semantic_le P Q -> semantic_le (mask p P) (mask p Q).
Proof. by move=>PQ i; rewrite /mask; case: (p i)=>//; apply: PQ. Qed.

Lemma mask_or_le (p q : pred I) (P Q : I -> 'FO(H)) :
  semantic_le (mask p P) Q -> semantic_le (mask q P) Q ->
  semantic_le (mask (predU p q) P) Q.
Proof.
move=>pQ qQ i.
change (((if p i || q i then P i else (0%:VF : 'FO(H))) : 'End(H)) ⊑ Q i).
case Ep: (p i)=>/=.
- by move: (pQ i); rewrite /mask Ep.
- case Eq: (q i)=>/=; last exact: obsf_ge0.
  by move: (qQ i); rewrite /mask Eq.
Qed.

Lemma mask_disjoint_sum_le (p q : pred I) (P Q R S : I -> 'FO(H)) :
  (forall i, q i -> ~~ p i) ->
  (forall i, (S i : 'End(H)) = (mask p P i : 'End(H)) + (mask q Q i : 'End(H))) ->
  semantic_le (mask p P) R -> semantic_le (mask q Q) R -> semantic_le S R.
Proof.
move=>disj SE pR qR i; rewrite SE /mask.
case Eq: (q i).
- have Ep : p i = false := negPf (disj i Eq).
  rewrite Ep add0r; by move: (qR i); rewrite /mask Eq.
- rewrite addr0; by move: (pR i); rewrite /mask.
Qed.

End Algebra.
End CQAssertionAlgebra.
