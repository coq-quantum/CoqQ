(* Extension of cqwhile kernels to arbitrary cq-states, classical.pdf 4.3–4.4. *)
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

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

(* Atomic instrument sums. Outcomes may have countably infinite support. *)
Module CQInstrument.
Section Instrument.
Context {I J : choiceType} {H : chsType}.
Variable (f : {vdistr I -> 'SO(H)}) (h : I -> J) (rho : 'End(H)).
Hypothesis positive : 0%:VF ⊑ rho.

Lemma branch_positive i : 0%:VF ⊑ f i rho.
Proof. by apply: cp_ge0. Qed.

Lemma instrument_psum_bound (A : {fset I}) :
  psum (fun i => `|f i rho|) A <= `|rho|.
Proof.
rewrite /psum.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?branch_positive //.
rewrite -linear_sum /= -sum_soE.
have Prho : rho \is psdlf by rewrite psdlfE.
rewrite (psd_trfnorm Prho).
change (\Tr ((psum f A) rho) <= \Tr rho).
apply: (qo_trlfE (QOperation_Build (psum_dso_cptn f A))).
by rewrite psdlfE.
Qed.

Lemma instrument_outputs_summable :
  summable (fun i => (sunit_def (h i) (f i rho) : {summable J -> 'End(H)})).
Proof.
apply: psum_ubounded_summable; exists `|rho|=>A.
rewrite /psum /normf.
under eq_bigr do rewrite sunit_normE.
exact: instrument_psum_bound.
Qed.

Definition instrument_outputs := Summable.build instrument_outputs_summable.

Lemma instrument_column_summable j :
  summable (fun i => sunit_def (h i) (f i : 'SO(H)) j).
Proof.
apply: psum_ubounded_summable; exists `|f : {summable I -> 'SO(H)}|=>A.
apply: (le_trans _ (psum_norm_ler_norm f A)).
apply: ler_sum=>i _; rewrite /normf /sunit_def.
by case: eqP=>_ //; rewrite normr0.
Qed.

Lemma instrument_sumE j :
  sum instrument_outputs j = (sdlet_vdistr h f j) rho.
Proof.
rewrite sum_summableE; first exact: summable_cvg.
change (sum (fun i => sunit_def (h i) (f i rho) j) =
  (sum (fun i => sunit_def (h i) (f i : 'SO(H)) j)) rho).
rewrite sum_summable_soE.
  by apply: norm_bounded_cvg; apply: instrument_column_summable.
apply: eq_sum=>i; rewrite /sunit_def.
by case: eqP=>_ //; rewrite soE.
Qed.
End Instrument.
End CQInstrument.
