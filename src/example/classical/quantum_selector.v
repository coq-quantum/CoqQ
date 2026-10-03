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
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules assertion_algebra assertion_series locality operational footprint auxiliary.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


From quantum.example.classical Require Import quantum_frame.

Module CQQuantumSelector.
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition selector (U : chsType) (I : finType) (w : I -> C) (v : I -> U) :=
  \sum_i w i *: (initialso (v i))^*o.

Lemma selectorE (U : chsType) (I : finType) w (v : I -> U) A :
  selector w v A = (\sum_i w i * [<v i; A (v i)>]) *: \1.
Proof.
rewrite /selector sum_soE scaler_suml.
by apply:eq_bigr=>i _; rewrite scale_soE dualso_initialE scalerA.
Qed.

Lemma selector_cp (U : chsType) (I : finType) w (v : I -> U) :
  (forall i, 0 <= w i) -> selector w v \is cpmap.
Proof.
move=>Hw; rewrite -geso0_cpE /selector; apply: sumv_ge0=>i _.
apply: scalev_ge0; first exact: Hw.
by rewrite geso0_cpE is_cpmap.
Qed.

Lemma selector_dqo (U : chsType) (I : finType) w (v : I -> U) :
  (forall i, 0 <= w i) -> (\sum_i w i <= 1) ->
  (forall i, [<v i; v i>] = 1) -> (selector w v)^*o \is cptn.
Proof.
move=>Hw Hsum Hv; rewrite (CPMap_BuildE (selector_cp v Hw)) cp_isdqoE.
change (selector w v \1 ⊑ \1).
rewrite selectorE; under eq_bigr do rewrite id_lfunE Hv mulr1.
rewrite -{2}(scale1r (\1 : 'End(U))); apply: lev_wpscale2r=>//.
exact: (obsf_ge0 (\1 : 'FO(U))).
Qed.

Lemma selector_outp (U : chsType) (I : finType) w (v : I -> U) j :
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  selector w v [>v j; v j<] = w j *: \1.
Proof.
move=>Hv; rewrite selectorE.
under eq_bigr=>i _ do rewrite outpE dotpZr !Hv.
rewrite (bigD1 j) //= eqxx !mulr1 big1 ?addr0 // =>i Hij.
by rewrite eq_sym (negbTE Hij) !mulr0.
Qed.

Lemma selector_labeled S T (I : finType) w (v : I -> 'H[msys]_T)
    (X : I -> 'F[msys]_S) :
  [disjoint S & T] ->
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  liftfso (selector w v)
    (\sum_i (liftf_lf (X i) \o liftf_lf [>v i; v i<])) =
    \sum_i w i *: liftf_lf (X i).
Proof.
move=>Hdis Hv; rewrite linear_sum /=; apply:eq_bigr=>i _.
rewrite liftfsoEf_compl // liftfsoEf selector_outp //.
by rewrite linearZ /= liftf_lf1 -comp_lfunZr comp_lfun1r.
Qed.

Theorem derives_lsum total c S T (I : finType) (w : I -> C)
    (v : I -> 'H[msys]_T) (P Q : I -> cmem -> 'F[msys]_S)
    (A B R R' : assertion) :
  [disjoint S & T] -> [disjoint quantum_variables c & T] ->
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  (forall i, 0 <= w i) -> (\sum_i w i <= 1) ->
  (forall s, (A s : 'End(Hq)) =
    \sum_i (liftf_lf (P i s) \o liftf_lf [>v i; v i<])) ->
  (forall s, (B s : 'End(Hq)) =
    \sum_i (liftf_lf (Q i s) \o liftf_lf [>v i; v i<])) ->
  (forall s, (R s : 'End(Hq)) = \sum_i w i *: liftf_lf (P i s)) ->
  (forall s, (R' s : 'End(Hq)) = \sum_i w i *: liftf_lf (Q i s)) ->
  derives total A c B -> derives total R c R'.
Proof.
move=>Hdis Hc Hv Hw Hsum HA HB HR HR' Hder.
have Hnorm i : [<v i; v i>] = 1 by rewrite Hv eqxx.
pose F := DualQO_Build (selector_dqo Hw Hsum Hnorm).
have ER : image F A = R.
  apply/funext=>s; apply/val_inj.
  change (liftfso (selector w v) (A s) = (R s : 'End(Hq))).
  by rewrite HA selector_labeled // HR.
have ER' : image F B = R'.
  apply/funext=>s; apply/val_inj.
  change (liftfso (selector w v) (B s) = (R' s : 'End(Hq))).
  by rewrite HB selector_labeled // HR'.
rewrite -ER -ER'; exact: derives_supoper Hc Hder.
Qed.

End CQQuantumSelector.
