(* Generic change of finite quantum-memory coordinates.
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
From quantum.example.veri_QEC Require Import cqwhile.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQMemoryTransport.

Definition conjugate {A B : chsType} (U : 'FGI(A,B)) (E : 'SO(A)) : 'SO(B) :=
  formso U :o E :o formso U^A.

Section Algebra.
Context {A B : chsType} (U : 'FGI(A,B)).

Lemma conjugate_linear : linear (conjugate U).
Proof. by move=>a E F; rewrite /conjugate ?comp_soPl ?comp_soPr ?comp_soPl. Qed.
HB.instance Definition _ := GRing.isLinear.Build hermitian.C _ _ *:%R
  (conjugate U) conjugate_linear.

Lemma conjugate1 : conjugate U \:1 = \:1.
Proof. by rewrite /conjugate comp_so1r formso_comp gisofEr formso1. Qed.

Lemma conjugate_formso (f : 'End(A)) :
  conjugate U (formso f) = formso (U \o f \o U^A).
Proof. by rewrite /conjugate !formso_comp. Qed.

Lemma conjugate_krausso (I : finType) (f : I -> 'End(A)) :
  conjugate U (krausso f) = krausso (fun i => U \o f i \o U^A).
Proof.
rewrite -!elemso_sum linear_sum /=.
by apply: eq_bigr=>i _; rewrite /elemso conjugate_formso.
Qed.

Lemma conjugate_cp (E : 'CP(A)) : conjugate U E \is cpmap.
Proof. rewrite /conjugate; exact: is_cpmap. Qed.

HB.instance Definition _ (E : 'CP(A)) :=
  isCPMap.Build B B (conjugate U E) (conjugate_cp E).

Lemma conjugate_tn (E : 'QO(A)) : conjugate U E \is cptn.
Proof. rewrite /conjugate; exact: is_cptn. Qed.

HB.instance Definition _ (E : 'QO(A)) :=
  isQOperation.Build B B (conjugate U E) (conjugate_tn E).

Lemma conjugate_tp (E : 'QC(A)) : conjugate U E \is cptp.
Proof. rewrite /conjugate; exact: is_cptp. Qed.

HB.instance Definition _ (E : 'QC(A)) :=
  isQChannel.Build B B (conjugate U E) (conjugate_tp E).

Lemma conjugate_comp (E F : 'SO(A)) :
  conjugate U (E :o F) = conjugate U E :o conjugate U F.
Proof.
rewrite /conjugate -!comp_soA.
by rewrite (comp_soA (formso U^A) (formso U)) formso_comp
  gisofEl formso1 comp_so1l.
Qed.

Lemma conjugateK (E : 'SO(A)) : conjugate [giso of U^A] (conjugate U E) = E.
Proof.
rewrite /conjugate adjfK -!comp_soA.
by rewrite (comp_soA (formso U^A) (formso U)) !formso_comp
  !gisofEl !formso1 comp_so1l comp_so1r.
Qed.

Lemma conjugate_injective : injective (conjugate U).
Proof. exact: can_inj conjugateK. Qed.

Lemma conjugate_apply (E : 'SO(A)) (X : 'End(A)) :
  conjugate U E (formso U X) = formso U (E X).
Proof.
rewrite /conjugate !comp_soE -[formso U^A (formso U X)]comp_soE.
by rewrite formso_comp gisofEl formso1 id_soE.
Qed.

Lemma conjugate_trace (E : 'SO(A)) (X : 'End(A)) :
  \Tr (conjugate U E (formso U X)) = \Tr (E X).
Proof. by rewrite conjugate_apply qc_trlfE. Qed.

Lemma conjugate_summable (I : choiceType) (f : I -> 'SO(A)) :
  summable f -> summable (fun i => conjugate U (f i)).
Proof.
move=>Hf.
have [M HM] := (proj1 (Summable_Reindex.summableW f)) Hf.
have [k [Hk0 Hk]] := linear_bounded (conjugate U : {linear 'SO(A) -> 'SO(B)}).
apply/Summable_Reindex.summableW; exists (k * M)=>J.
apply: le_trans (ler_wpM2l (ltW Hk0) (HM J)).
rewrite /psum mulr_sumr; apply: ler_sum=>i _; exact: Hk.
Qed.

Lemma conjugate_sum (I : choiceType) (f : I -> 'SO(A)) :
  summable f -> conjugate U (sum f) = sum (fun i => conjugate U (f i)).
Proof.
move=>Hf; apply: cvg_linearP_sum; first exact: conjugate_linear.
exact: norm_bounded_cvg Hf.
Qed.

End Algebra.
End CQMemoryTransport.
