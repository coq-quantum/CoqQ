(* Summable mixtures of cq-states for the two papers' distribution semantics. *)
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
From quantum.example.classical Require Import state kernel mixture.
From quantum.example.distributive Require Import language scheduler_results.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Module DistributedCQInput.
Section Components.
Context {I : choiceType} {H : chsType}.
Variable (d : @CQState.state I H).

Definition weight i := \Tr (d i).

Lemma weight_nonnegative i : 0 <= weight i.
Proof. by rewrite /weight -psd_trfnorm ?psdlfE ?vdistr_ge0. Qed.

Lemma weights_summable : summable weight.
Proof.
apply: psum_ubounded_summable; exists `|d : {summable I -> 'End(H)}|=>A.
apply: (le_trans (y := psum (fun i => `|d i|) A)); last exact: psum_norm_ler_norm.
rewrite /psum /normf; apply: ler_sum=>i _.
rewrite ger0_norm ?weight_nonnegative // /weight.
by rewrite psd_trfnorm ?psdlfE ?vdistr_ge0.
Qed.

Lemma weights_bound : `|sum (Summable.build weights_summable)| <= 1.
Proof.
change (`|CQState.mass d| <= 1).
by rewrite ger0_norm ?CQState.mass_ge0 //; apply: CQState.mass_le1.
Qed.

Definition weights : Distr I := VDistr.build (f := Summable.build weights_summable)
  weight_nonnegative weights_bound.

Lemma weightsE i : weights i = \Tr (d i).
Proof. by []. Qed.

Variable fallback : 'FD1(H).
Definition normalized_raw i :=
  if 0 < weight i then (weight i)^-1 *: d i else fallback.

Lemma normalized_density i : normalized_raw i \is den1lf.
Proof.
rewrite /normalized_raw; case: ifP=>Hw; last exact: is_den1lf.
apply/den1lfP; split.
- apply: psdlfZ; first by rewrite invr_ge0; exact: ltW Hw.
  by rewrite psdlfE vdistr_ge0.
- by rewrite linearZ /= -/(weight i) mulVf ?gt_eqF.
Qed.

Definition normalized i : 'FD1(H) := Den1Lf_Build (normalized_density i).

Lemma component_reassemble i : weight i *: (normalized i : 'End(H)) = d i.
Proof.
change (weight i *: normalized_raw i = d i).
rewrite /normalized_raw; case: ifP=>Hw.
  by rewrite scalerA mulfV ?gt_eqF // scale1r.
have Hz : weight i = 0.
  by move: (weight_nonnegative i); rewrite le_eqVlt Hw orbF eq_sym=>/eqP.
have Dz : d i == 0 := introT (@trlf0_eq0 H (d i)) (conj (vdistr_ge0 (s := d) i) Hz).
by rewrite Hz scale0r (eqP Dz).
Qed.

Lemma input_reassemble :
  CQStateMixture.mix weights (fun i => CQState.point i (normalized i)) = d.
Proof.
apply/vdistrP=>j; rewrite CQStateMixture.mixE (fin_supp_sum (S := [fset j])).
- by move=>i; rewrite inE eq_sym=>/negPf ji; rewrite CQState.pointE ji scaler0.
- by rewrite psum1 CQState.pointE eqxx -/(weight j) component_reassemble.
Qed.
End Components.

Section MixtureTransfer.
Context {I J : choiceType} {H : chsType}.
Variables (fallback : 'FD1(H)) (F : I -> 'FD1(H) -> @CQState.state J H).
Definition extend (d : @CQState.state I H) : @CQState.state J H :=
  CQStateMixture.mix (weights d) (fun i => F i (normalized d fallback i)).

Lemma extendE d j : extend d j =
  sum (fun i => weight d i *: F i (normalized d fallback i) j).
Proof. by rewrite /extend CQStateMixture.mixE. Qed.

Theorem extend_kernel (K : semType I J H H) :
  (forall i (rho : 'FD1(H)) j, F i rho j = K i j rho) ->
  forall d, extend d = CQKernel.apply K d.
Proof.
move=>EF d; apply/vdistrP=>j; rewrite extendE CQKernel.applyE.
apply: eq_sum=>i; rewrite EF -linearZ /= component_reassemble.
by [].
Qed.

Lemma normalized_point (i : I) (rho : 'FD1(H)) :
  normalized (CQState.point i rho) fallback i = rho.
Proof.
apply/val_inj; change (normalized_raw (CQState.point i rho) fallback i = rho).
by rewrite /normalized_raw /weight CQState.pointE eqxx den1f_trlf ltr01 invr1 scale1r.
Qed.

Theorem extend_point i (rho : 'FD1(H)) :
  extend (CQState.point i rho) = F i rho.
Proof.
apply/vdistrP=>j; rewrite extendE (fin_supp_sum (S := [fset i])).
- move=>k; rewrite inE=>/negPf ki.
  by rewrite /weight CQState.pointE ki linear0 scale0r.
- by rewrite psum1 /weight CQState.pointE eqxx den1f_trlf scale1r normalized_point.
Qed.
End MixtureTransfer.

Section Programs.
Import DistributedLanguage DistributedSchedulerResults.
Local Notation Hq := 'H[msys]_finset.setT.
Definition default_density : 'FD1(Hq) :=
  [> deltav (@idx_default _ msys finset.setT); deltav idx_default <].

Definition run (P : program) (d : @CQState.state cmem Hq) : @CQState.state cmem Hq :=
  extend default_density (denote_program P) d.

Theorem run_point (P : program) m (rho : 'FD1(Hq)) :
  run P (CQState.point m rho) = denote_program P m rho.
Proof. exact: extend_point. Qed.

Theorem run_kernel (P : program) (K : semType cmem cmem Hq Hq) :
  (forall m (rho : 'FD1(Hq)) out, denote_program P m rho out = K m out rho) ->
  forall d, run P d = CQKernel.apply K d.
Proof. exact: extend_kernel. Qed.
End Programs.
End DistributedCQInput.
