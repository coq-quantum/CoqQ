(* Derived Sum and Linear rules; see HOARE-NOTES.md. *)
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
  hoare rules primitive quantum_frame quantum_space_rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


From quantum.example.classical Require Import auxiliary.

Module CQAuxiliaryDerivations.
Import CQAssertion CQRules CQAuxiliary.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem derives_sum total c (p q : pred cmem) (P Q R S : assertion) :
  (forall i, q i -> ~~ p i) ->
  (forall i, (S i : 'End(Hq)) = (mask p P i : 'End(Hq)) + (mask q Q i : 'End(Hq))) ->
  derives total (mask p P) c R -> derives total (mask q Q) c R ->
  derives total S c R.
Proof.
move=>Hdis HE /derives_sound HP /derives_sound HQ; apply: derives_complete.
exact: valid_disjoint_sum Hdis HE HP HQ.
Qed.

Theorem derives_linear_total (J : finType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, derives true (F j) c (G j)) -> derives true P c Q.
Proof.
move=>Hw HP HQ HD; apply: derives_complete.
apply: (@valid_finite_linear_total J w F G P Q c Hw HP HQ)=>j.
exact: derives_sound (HD j).
Qed.

Theorem derives_linear_partial (J : finType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) -> (\sum_j w j <= 1) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, derives false (F j) c (G j)) -> derives false P c Q.
Proof.
move=>Hw Hsum HP HQ HD; apply: derives_complete.
apply: (@valid_finite_linear_partial J w F G P Q c Hw Hsum HP HQ)=>j.
exact: derives_sound (HD j).
Qed.

Theorem derives_series_total (J : choiceType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, derives true (F j) c (G j)) -> derives true P c Q.
Proof.
move=>Hw HS HT HP HQ HD; apply: derives_complete.
apply: (@valid_series_total J w F G P Q c Hw HS HT HP HQ)=>j.
exact: derives_sound (HD j).
Qed.

Theorem derives_series_partial (J : choiceType) (w : J -> C)
    (F G : J -> assertion) (P Q : assertion) c :
  (forall j, 0 <= w j) -> summable w -> sum w <= 1 ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, derives false (F j) c (G j)) -> derives false P c Q.
Proof.
move=>Hw Hsw Hsum HS HT HP HQ HD; apply: derives_complete.
apply: (@valid_series_partial J w F G P Q c Hw Hsw Hsum HS HT HP HQ)=>j.
exact: derives_sound (HD j).
Qed.

End CQAuxiliaryDerivations.
