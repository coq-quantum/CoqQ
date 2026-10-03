(* Probabilistic composition via saturated projector support. See HOARE-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace hspace_extra summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules expectation assertion_algebra probabilistic_composition.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.




Module CQProbabilisticPure.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQProbabilisticComposition.
Local Open Scope hspace_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation C := hermitian.C.

Definition register_effect u (q : wf_qreg u) (M : 'FO('Ht u)) : 'FO(Hq) :=
  [obs of liftf_lf (tf2f q q M)].
Definition register_pure u (q : wf_qreg u) (v : 'NS('Ht u)) : {hspace Hq} :=
  HSType [proj of liftf_lf (tf2f q q [> v; v <])].

Lemma pure_sandwich (H : chsType) (v : 'NS(H)) (M : 'End(H)) :
  [> (v : H); (v : H) <] \o M \o [> (v : H); (v : H) <] = [< (v : H); M (v : H) >] *: [> (v : H); (v : H) <].
Proof. by rewrite outp_compl outp_comp adj_dotEl. Qed.

Lemma register_pure_sandwich u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u)) :
  register_pure q v \o register_effect q M \o register_pure q v =
  [< (v : 'Ht u); M (v : 'Ht u) >] *: (register_pure q v : 'End(Hq)).
Proof.
rewrite /register_pure /register_effect !hsE /= -!liftf_lf_comp !tf2f_comp.
by rewrite pure_sandwich !linearZ.
Qed.

Definition pure_success_effect u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u)) : 'FO(Hq) :=
  register_effect q [obs of (initialso v)^*o M].

Lemma pure_success_effectE u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u)) :
  (pure_success_effect q v M : 'End(Hq)) = [< (v : 'Ht u); M (v : 'Ht u) >] *: \1.
Proof.
by rewrite /pure_success_effect /register_effect /= dualso_initialE
  !linearZ /= tf2f1 liftf_lf1.
Qed.

Lemma masked_projection (p : pred cmem) (P : {hspace Hq}) :
  projection_assertion (fun s => if p s then P else `0`) =
  mask p (fun _ => [obs of P]).
Proof.
apply/funext=>s; apply/val_inj; rewrite /projection_assertion /mask /=.
by case: (p s); rewrite // hs2lf0E.
Qed.

Theorem valid_probcomp u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u))
    (p' p : pred cmem) c d (Q : assertion) :
  CQHoare.valid true (mask p' semantic_top) c
    (mask p (fun _ => [obs of register_pure q v])) ->
  CQHoare.valid true (mask p (fun _ => register_effect q M)) d Q ->
  CQHoare.valid true (mask p' (fun _ => pure_success_effect q v M)) (Sequence c d) Q.
Proof.
move=>Vc Vd.
apply: (@valid_probcomp_projection p'
  (fun s => if p s then register_pure q v else `0`)
  (mask p (fun _ => register_effect q M))
  (mask p' (fun _ => pure_success_effect q v M)) Q
  ([< (v : 'Ht u); M (v : 'Ht u) >]) c d).
- move=>s; rewrite /mask; by case: (p' s); rewrite // pure_success_effectE.
- move=>s; rewrite /mask; case: (p s); first exact: register_pure_sandwich.
  by rewrite hs2lf0E comp_lfun0l comp_lfun0r scaler0.
- by rewrite masked_projection.
- exact: Vd.
Qed.

Theorem derives_probcomp u (q : wf_qreg u) (v : 'NS('Ht u)) (M : 'FO('Ht u))
    (p' p : pred cmem) c d (Q : assertion) :
  derives true (mask p' semantic_top) c
    (mask p (fun _ => [obs of register_pure q v])) ->
  derives true (mask p (fun _ => register_effect q M)) d Q ->
  derives true (mask p' (fun _ => pure_success_effect q v M)) (Sequence c d) Q.
Proof.
move=>/derives_sound Vc /derives_sound Vd; apply: derives_complete.
exact: valid_probcomp Vc Vd.
Qed.

End CQProbabilisticPure.
