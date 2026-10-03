(* Countable local instruments and their cylindrical lifts.
   See MEMORY-TRANSPORT-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQMemoryInstruments.
Section Instruments.
Context {L : finType} {H : L -> chsType} {I : choiceType}.

Lemma liftso_summable_reflect (S T : {set L}) (sub : S :<=: T) (f : I -> 'SO[H]_S) :
  summable (fun i => liftso sub (f i)) -> summable f.
Proof.
move=>/Summable_Reindex.summableW[M HM].
apply/Summable_Reindex.summableW; exists M=>J.
apply: le_trans (HM J); rewrite /psum; apply: ler_sum=>i _.
exact: liftso_norm.
Qed.

Lemma liftso_sum (S T : {set L}) (sub : S :<=: T) (f : I -> 'SO[H]_S) :
  summable f -> liftso sub (sum f) = sum (fun i => liftso sub (f i)).
Proof.
move=>Hf; apply: cvg_linearP_sum; first exact: liftso_is_linear.
exact: norm_bounded_cvg Hf.
Qed.

Lemma liftfso_summable_reflect S (f : I -> 'SO[H]_S) :
  summable (fun i => liftfso (f i)) -> summable f.
Proof. exact: liftso_summable_reflect. Qed.

Lemma liftfso_sum S (f : I -> 'SO[H]_S) :
  summable f -> liftfso (sum f) = sum (fun i => liftfso (f i)).
Proof. exact: liftso_sum. Qed.

Lemma liftfso_sum_cptn_reflect S (f : I -> 'SO[H]_S) :
  summable (fun i => liftfso (f i)) ->
  sum (fun i => liftfso (f i)) \is cptn -> sum f \is cptn.
Proof.
move=>Hf Htn; rewrite -liftfso_qoE (liftfso_sum (liftfso_summable_reflect Hf)).
exact: Htn.
Qed.

End Instruments.
End CQMemoryInstruments.
