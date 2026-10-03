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

Module CQQuantumSuperposition.
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame CQAssertionAlgebra.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition selecting_vector (U : chsType) (I : finType) (a : I -> C) (v : I -> U) :=
  \sum_i (a i)^* *: v i.

Lemma selecting_overlap (U : chsType) (I : finType) a (v : I -> U) j :
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  [<selecting_vector a v; v j>] = a j.
Proof.
move=>Hv; rewrite /selecting_vector dotp_suml (bigD1 j) //=.
rewrite dotpZl Hv eqxx conjCK mulr1 big1 ?addr0 // =>i Hij.
by rewrite dotpZl Hv (negbTE Hij) mulr0.
Qed.

Lemma selecting_norm (U : chsType) (I : finType) a (v : I -> U) :
  (forall i j, [<v i; v j>] = (i == j)%:R) ->
  (\sum_i a i * (a i)^* = 1) ->
  [<selecting_vector a v; selecting_vector a v>] = 1.
Proof.
move=>Hv Ha; rewrite {2}/selecting_vector dotp_sumr.
under eq_bigr=>i _ do rewrite dotpZr selecting_overlap // mulrC.
exact: Ha.
Qed.

Lemma unit_selector_dqo (U : chsType) (u : U) :
  [<u;u>] = 1 -> ((initialso u)^*o)^*o \is cptn.
Proof.
move=>Hu; rewrite cp_isdqoE dualso_initialE id_lfunE Hu scale1r.
exact: lexx.
Qed.

Lemma selected_outp (U : chsType) (I : finType) a (v : I -> U) i j :
  (forall i j, [<v i;v j>] = (i == j)%:R) ->
  (initialso (selecting_vector a v))^*o [>v i;v j<] =
    (a i * (a j)^*) *: \1.
Proof.
move=>Hv; rewrite dualso_initialE outpE dotpZr selecting_overlap //.
by rewrite -conj_dotp selecting_overlap // mulrC.
Qed.

Lemma selected_entangled S T (I : finType) a (v : I -> 'H[msys]_T)
    (phi : I -> 'H[msys]_S) :
  [disjoint S & T] ->
  (forall i j, [<v i;v j>] = (i == j)%:R) ->
  liftfso (initialso (selecting_vector a v))^*o
    (liftf_lf [>\sum_i tenv (phi i) (v i); \sum_i tenv (phi i) (v i)<]) =
  liftf_lf [>\sum_i a i *: phi i; \sum_i a i *: phi i<].
Proof.
move=>Hdis Hv; rewrite !outp_suml !linear_sum /=.
apply:eq_bigr=>i _; rewrite !outp_sumr !linear_sum /=.
apply:eq_bigr=>j _.
rewrite -tenf_outp -liftf_lf_compT // liftfsoEf_compl // liftfsoEf selected_outp //.
by rewrite outpZl outpZr !linearZ /= liftf_lf1 comp_lfun1r scalerA.
Qed.

Lemma expect_scaled (A B : assertion) r rho :
  (forall s, (A s : 'End(Hq)) = r *: (B s : 'End(Hq))) ->
  expect A rho = r * expect B rho.
Proof.
move=>HE.
pose terms := Summable.build (expect_summable B rho).
have TE : expect_term A rho = r *: terms.
  apply/funext=>s; change (\Tr (A s \o rho s) = r * \Tr (B s \o rho s)).
  by rewrite HE linearZl /= linearZ.
by rewrite /expect TE summable_sumZ.
Qed.

Theorem derives_suppos c S T (I : finType) (a : I -> C)
    (v : I -> 'H[msys]_T) (phi psi : I -> 'H[msys]_S)
    (p q : pred cmem) r (A B R R' : assertion) :
  [disjoint S & T] -> [disjoint quantum_variables c & T] ->
  (forall i j, [<v i;v j>] = (i == j)%:R) ->
  (\sum_i a i * (a i)^* = 1) -> 0 < r ->
  (forall s, (A s : 'End(Hq)) = r *:
    (if p s then liftf_lf [>\sum_i tenv (phi i) (v i); \sum_i tenv (phi i) (v i)<] else 0)) ->
  (forall s, (B s : 'End(Hq)) = r *:
    (if q s then liftf_lf [>\sum_i tenv (psi i) (v i); \sum_i tenv (psi i) (v i)<] else 0)) ->
  (forall s, (R s : 'End(Hq)) =
    if p s then liftf_lf [>\sum_i a i *: phi i; \sum_i a i *: phi i<] else 0) ->
  (forall s, (R' s : 'End(Hq)) =
    if q s then liftf_lf [>\sum_i a i *: psi i; \sum_i a i *: psi i<] else 0) ->
  derives true A c B -> derives true R c R'.
Proof.
move=>Hdis Hc Hv Ha Hr HA HB HR HR' Hder.
pose F := DualQO_Build (unit_selector_dqo (selecting_norm Hv Ha)).
have HE s : (image F A s : 'End(Hq)) = r *: (R s : 'End(Hq)).
  change (liftfso (initialso (selecting_vector a v))^*o (A s) = r *: (R s : 'End(Hq))).
  rewrite HA HR linearZ /=; case: (p s); last by rewrite linear0.
  by rewrite selected_entangled.
have HE' s : (image F B s : 'End(Hq)) = r *: (R' s : 'End(Hq)).
  change (liftfso (initialso (selecting_vector a v))^*o (B s) = r *: (R' s : 'End(Hq))).
  rewrite HB HR' linearZ /=; case: (q s); last by rewrite linear0.
  by rewrite selected_entangled.
have HD := @derives_supoper true A c B T F Hc Hder.
apply: derives_complete=>rho.
have HV : expect (image F A) rho <= expect (image F B) (CQHoare.run c rho) :=
  @derives_sound true (image F A) c (image F B) HD rho.
rewrite (expect_scaled _ HE) (expect_scaled _ HE') in HV.
by move: HV; rewrite ler_pM2l.
Qed.

End CQQuantumSuperposition.
