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

Module CQQuantumSpaceRules.
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition lifted S (P : cmem -> 'FO[msys]_S) : assertion :=
  fun s => liftf_lf (P s).

Lemma effect_map_exists (U : chsType) (M : 'FO(U)) :
  exists F : 'DQO(U), F \1 = M.
Proof.
have [B HB] := gef0_form (obsf_ge0 M).
have H1 : (formso B : 'CP(U)) \1 ⊑ \1.
  by rewrite formsoE comp_lfun1r -HB; exact: obsf_le1.
have Hcp : (formso B)^*o \is cptn := (introT (cp_isdqoP (formso B)) H1).
exists (DualQO_Build Hcp).
by change (formso B \1 = M); rewrite formsoE comp_lfun1r -HB.
Qed.

Lemma lift_tensor_image S T (F : 'SO[msys]_T) (X : 'F[msys]_S) :
  [disjoint S & T] ->
  liftfso F (liftf_lf X) = liftf_lf (X \⊗ F \1).
Proof.
move=>Hdis.
rewrite -{1}(comp_lfun1r (liftf_lf X)) liftfsoEf_compl //.
by rewrite lift_identity liftf_lf_compT.
Qed.

Theorem derives_tens total c S T (P Q : cmem -> 'FO[msys]_S)
    (M : 'FO[msys]_T) (R R' : assertion) :
  [disjoint S & T] -> [disjoint quantum_variables c & T] ->
  (forall s, (R s : 'End(Hq)) = liftf_lf ((P s : 'F[msys]_S) \⊗ M)) ->
  (forall s, (R' s : 'End(Hq)) = liftf_lf ((Q s : 'F[msys]_S) \⊗ M)) ->
  derives total (lifted P) c (lifted Q) -> derives total R c R'.
Proof.
move=>Hdis Hc HR HR' Hder; have [F HF] := effect_map_exists M.
have ER : image F (lifted P) = R.
  apply/funext=>s; apply/val_inj; change (liftfso F (liftf_lf (P s)) = (R s : 'End(Hq))).
  by rewrite lift_tensor_image // HF HR.
have ER' : image F (lifted Q) = R'.
  apply/funext=>s; apply/val_inj; change (liftfso F (liftf_lf (Q s)) = (R' s : 'End(Hq))).
  by rewrite lift_tensor_image // HF HR'.
rewrite -ER -ER'; exact: derives_supoper Hc Hder.
Qed.

Lemma tensor_effect S T (M : 'FO[msys]_S) (N : 'FO[msys]_T) :
  [disjoint S & T] -> (M : 'F[msys]_S) \⊗ (N : 'F[msys]_T) \is obslf.
Proof.
move=>Hdis; apply/obslf_lefP; split.
- exact: tenf_ge0 Hdis (obsf_ge0 M) (obsf_ge0 N).
- apply: (le_trans (y := (\1 : 'F[msys]_S) \⊗ (N : 'F[msys]_T))).
  + rewrite -subv_ge0 -linearBl /=; apply: tenf_ge0 Hdis _ (obsf_ge0 N).
    by rewrite subv_ge0; exact: obsf_le1.
  + rewrite -(@tenf11 _ msys S T).
    rewrite -subv_ge0 -linearBr /=; apply: tenf_ge0 Hdis (obsf_ge0 (\1 : 'FO[msys]_S)) _.
    by rewrite subv_ge0; exact: obsf_le1.
Qed.

Definition tens (S T : {set mlab}) (Hdis : [disjoint S & T]) (P : cmem -> 'FO[msys]_S)
    (M : 'FO[msys]_T) : assertion :=
  fun s => liftf_lf (ObsLf_Build (tensor_effect (P s) M Hdis)).

Corollary derives_tens_direct total c (S T : {set mlab}) (Hdis : [disjoint S & T])
    (P Q : cmem -> 'FO[msys]_S) (M : 'FO[msys]_T) :
  [disjoint quantum_variables c & T] ->
  derives total (lifted P) c (lifted Q) ->
  derives total (tens Hdis P M) c (tens Hdis Q M).
Proof.
move=>Hc Hder; exact: (@derives_tens total c S T P Q M
  (tens Hdis P M) (tens Hdis Q M) Hdis Hc (fun _ => erefl) (fun _ => erefl) Hder).
Qed.

End CQQuantumSpaceRules.
