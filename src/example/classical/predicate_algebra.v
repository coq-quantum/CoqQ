(* Lemma 4.16(3--5); see HOARE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate
  hoare rules quantum_frame quantum_space_rules quantum_cross_space.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQPredicateAlgebra.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame
  CQQuantumSpaceRules CQQuantumCrossSpace.
Local Notation Hq := 'H[msys]_finset.setT.

Section FiniteAlgebra.
Context {I J : choiceType} {H : chsType}.
Variable K : semType I J H H.

Theorem wp_finite_linear (T : finType) (w : T -> C)
    (F : T -> J -> 'FO(H)) (Q : J -> 'FO(H)) :
  (forall j, (Q j : 'End(H)) = \sum_t w t *: (F t j : 'End(H))) ->
  forall i, (wp K Q i : 'End(H)) = \sum_t w t *: (wp K (F t) i : 'End(H)).
Proof.
move=>HQ i; rewrite wpE.
pose terms t := w t *: Summable.build (term_summable K (F t) i).
have E : (fun j => (K i j)^*o (Q j)) =
    (\sum_t terms t : {summable J -> 'End(H)}).
  apply/funext=>j; rewrite summable_sumE HQ linear_sum /=.
  apply:eq_bigr=>t _; by rewrite /terms /= /term linearZ.
rewrite E summable_sum_sum; apply:eq_bigr=>t _.
by rewrite /terms summable_sumZ wpE.
Qed.

Theorem wlp_finite_affine (T : finType) (w : T -> C)
    (F : T -> J -> 'FO(H)) (Q : J -> 'FO(H)) :
  \sum_t w t = 1 ->
  (forall j, (Q j : 'End(H)) = \sum_t w t *: (F t j : 'End(H))) ->
  forall i, (wlp K Q i : 'End(H)) = \sum_t w t *: (wlp K (F t) i : 'End(H)).
Proof.
move=>Hw HQ i.
have HE j : (complement Q j : 'End(H)) =
    \sum_t w t *: (complement (F t) j : 'End(H)).
  change (\1 - (Q j : 'End(H)) = \sum_t w t *: (\1 - (F t j : 'End(H)))).
  under eq_bigr do rewrite scalerBr.
  by rewrite sumrB -scaler_suml Hw scale1r HQ.
change (\1 - (wp K (complement Q) i : 'End(H)) =
  \sum_t w t *: (\1 - (wp K (complement (F t)) i : 'End(H)))).
rewrite (@wp_finite_linear T w (fun t => complement (F t)) (complement Q) HE).
under [RHS]eq_bigr do rewrite scalerBr.
by rewrite sumrB -scaler_suml Hw scale1r.
Qed.

End FiniteAlgebra.

Theorem wlp_image_unital c S (F : 'DQO[msys]_S) Q :
  [disjoint quantum_variables c & S] -> F \1 = \1 -> forall s,
  (wlp (denote c) (image F Q) s : 'End(Hq)) = liftfso F (wlp (denote c) Q s).
Proof.
move=>Hdis HF s; rewrite !wlp_decompose (wp_image F Q Hdis) linearD.
change ((\1 - (wp (denote c) semantic_top s : 'End(Hq))) +
  liftfso F (wp (denote c) Q s) =
  liftfso F (\1 - (wp (denote c) semantic_top s : 'End(Hq))) +
  liftfso F (wp (denote c) Q s)).
by rewrite (@loss_unital c S F s Hdis HF).
Qed.

Lemma square_extension_unital S T (F : 'DQO[msys]_(S,T)) :
  F \1 = \1 -> square_extension F \1 = \1.
Proof.
move=>HF; have E := square_extension_lift F (\1 : 'F[msys]_S).
by rewrite HF !lift_lf1 in E.
Qed.

Theorem wp_cross c (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (Q : cmem -> 'FO[msys]_(S :|: R)) :
  [disjoint quantum_variables c & S :|: T] -> forall s,
  (wp (denote c) (@cross_assertion S T R F HS HT Q) s : 'End(Hq)) =
    liftfso (square_extension F) (wp (denote c) (lifted Q) s).
Proof.
move=>Hdis s; rewrite -image_square_extension.
exact: (@wp_image c (S :|: T) (square_extension F) (lifted Q) Hdis s).
Qed.

Theorem wlp_cross_le c (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (Q : cmem -> 'FO[msys]_(S :|: R)) :
  [disjoint quantum_variables c & S :|: T] -> forall s,
  liftfso (square_extension F) (wlp (denote c) (lifted Q) s) ⊑
    (wlp (denote c) (@cross_assertion S T R F HS HT Q) s : 'End(Hq)).
Proof.
move=>Hdis s; rewrite -image_square_extension.
exact: (@pre_image_le false c _ (square_extension F) (lifted Q) s Hdis).
Qed.

Theorem wlp_cross_unital c (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (Q : cmem -> 'FO[msys]_(S :|: R)) :
  [disjoint quantum_variables c & S :|: T] -> F \1 = \1 -> forall s,
  (wlp (denote c) (@cross_assertion S T R F HS HT Q) s : 'End(Hq)) =
    liftfso (square_extension F) (wlp (denote c) (lifted Q) s).
Proof.
move=>Hdis HF s; rewrite -image_square_extension.
exact: (@wlp_image_unital c (S :|: T) (square_extension F)
  (lifted Q) Hdis (@square_extension_unital S T F HF) s).
Qed.

End CQPredicateAlgebra.
