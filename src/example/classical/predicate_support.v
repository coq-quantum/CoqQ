(* Lemma 4.14(1); see PREDICATE-SUPPORT-NOTES.md. *)
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
  hoare rules quantum_frame quantum_space_rules quantum_trace memory_extension predicate_algebra.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


Module CQPredicateSupport.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame
  CQQuantumSpaceRules CQQuantumTrace CQMemoryExtension CQPredicateAlgebra.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma complement_difference (S : {set mlab}) : finset.setT :\: ~: S = S.
Proof. by rewrite finset.setTD finset.setCK. Qed.

Definition local_operator (S : {set mlab}) (A : 'End(Hq)) : 'F[msys]_S :=
  castlf (complement_difference S, complement_difference S)
    (uniform_weight 'H[msys]_(~: S) *: ptraceso (~: S) A).

Lemma local_operator_cylinder S A :
  liftf_lf (local_operator S A) = liftfso (depolarizer msys (~: S)) A.
Proof.
by rewrite /local_operator liftf_lf_cast linearZ /= -depolarizer_full.
Qed.

Lemma local_operator_effect S (A : 'FO(Hq)) : local_operator S A \is obslf.
Proof.
rewrite liftf_lf_obsE local_operator_cylinder.
exact: (dqo_obslf (liftfso (depolarizing msys (~: S))) A).
Qed.

Definition local_assertion (S : {set mlab}) (P : assertion) : cmem -> 'FO[msys]_S :=
  fun m => ObsLf_Build (local_operator_effect S (P m)).

Lemma local_assertionE S P m :
  (local_assertion S P m : 'F[msys]_S) = local_operator S (P m).
Proof. by []. Qed.

Lemma depolarizer_unital (T : {set mlab}) : depolarizer msys T \1 = \1.
Proof.
rewrite depolarizerE /uniform_weight /lftrace h2mx1 mxtrace1 scalerA mulVf.
- by rewrite gt_eqF // dim_proper_gt0.
- by rewrite scale1r.
Qed.

Lemma depolarizer_fixes_local S (P : cmem -> 'FO[msys]_S) :
  image (depolarizing msys (~: S)) (lifted P) = lifted P.
Proof.
apply/funext=>m; apply/val_inj.
change (liftfso (depolarizer msys (~: S)) (liftf_lf (P m)) = liftf_lf (P m)).
have Hd : [disjoint S & ~: S] := disjointXC S.
by rewrite (lift_tensor_image _ _ Hd) depolarizer_unital (liftf_lf_tenf1r _ Hd).
Qed.

Definition local_pre total c (S : {set mlab}) (Q : cmem -> 'FO[msys]_S) :=
  local_assertion S (pre total c (lifted Q)).

Theorem local_preE total c (S : {set mlab}) (Q : cmem -> 'FO[msys]_S) :
  quantum_variables c :<=: S -> forall m,
  (pre total c (lifted Q) m : 'End(Hq)) = liftf_lf (local_pre total c Q m).
Proof.
move=>Hsub m.
have Hdis : [disjoint quantum_variables c & ~: S].
  by rewrite -finset.subsets_disjoint.
rewrite /local_pre local_assertionE local_operator_cylinder.
case: total.
- have E := @wp_image c (~: S) (depolarizing msys (~: S)) (lifted Q) Hdis m.
  rewrite depolarizer_fixes_local in E; exact: E.
- have H1 : depolarizing msys (~: S) \1 = \1 := depolarizer_unital (~: S).
  have E := @wlp_image_unital c (~: S) (depolarizing msys (~: S))
    (lifted Q) Hdis H1 m.
  rewrite depolarizer_fixes_local in E; exact: E.
Qed.

Theorem pre_quantum_support total c (S : {set mlab}) (Q : cmem -> 'FO[msys]_S) :
  quantum_variables c :<=: S ->
  pre total c (lifted Q) = lifted (local_pre total c Q).
Proof.
move=>Hsub; apply/funext=>m; apply/val_inj.
exact: (@local_preE total c S Q Hsub m).
Qed.

End CQPredicateSupport.
