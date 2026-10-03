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
From quantum.example.classical Require Import state.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Module CQKernel.
Section Kernel.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H) (d : @CQState.state I H).

Lemma branch_positive i j : 0%:VF ⊑ K i j (d i).
Proof. by rewrite -psdlfE; apply: cp_psdP; rewrite psdlfE vdistr_ge0. Qed.

Lemma row_bound i (B : {fset J}) :
  psum (fun j => `|K i j (d i)|) B <= `|d i|.
Proof.
rewrite /psum.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?branch_positive //.
rewrite -linear_sum /= -sum_soE.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
change (\Tr ((psum (K i) B) (d i)) <= \Tr (d i)).
by apply: qo_trlfE; rewrite psdlfE vdistr_ge0.
Qed.

Lemma rectangle_bound (A : {fset I}) (B : {fset J}) :
  psum (fun i => psum (fun j => `|K i j (d i)|) B) A <=
    `|d : {summable I -> 'End(H)}|.
Proof.
apply: (le_trans _ (psum_norm_ler_norm d A)).
by apply: ler_sum=>i _; apply: row_bound.
Qed.

Lemma columns_summable j : summable (fun i => K i j (d i)).
Proof.
apply: psum_ubounded_summable.
exists `|d : {summable I -> 'End(H)}|=>A.
apply: (le_trans _ (rectangle_bound A [fset j])).
by apply: ler_sum=>i _; rewrite psum1.
Qed.

Definition apply_raw j := sum (fun i => K i j (d i)).

Lemma apply_raw_summable : summable apply_raw.
Proof.
have B : exists M, forall B A,
  psum (fun j => psum (fun i => `|K i j (d i)|) A) B <= M.
  exists `|d : {summable I -> 'End(H)}|=>B A.
  by rewrite /psum exchange_big; apply: rectangle_bound.
exact: (proj1 (proj2 (proj2 (pseries_ubounded_cvg B)))).
Qed.

Definition apply_summable := Summable.build apply_raw_summable.

Lemma apply_positive j : 0%:VF ⊑ apply_raw j.
Proof.
apply: lim_gev_near.
  by apply: norm_bounded_cvg; apply: columns_summable.
by near=>A; apply: sumv_ge0=>i _; apply: branch_positive.
Unshelve. end_near.
Qed.

Lemma apply_norm_lim j : `|apply_raw j| =
  lim ((fun A => `|psum (fun i => K i j (d i)) A|) @ totally)%classic.
Proof.
symmetry; apply: lim_norm.
by apply: norm_bounded_cvg; apply: columns_summable.
Qed.

Lemma apply_psum_bound (B : {fset J}) :
  psum (fun j => `|apply_raw j|) B <= `|d : {summable I -> 'End(H)}|.
Proof.
rewrite /psum.
under eq_bigr do rewrite apply_norm_lim.
rewrite -lim_sum_apply.
  by move=>j _; apply: is_cvg_norm; apply: norm_bounded_cvg; apply: columns_summable.
apply: etlim_le.
  apply: is_cvg_sum_apply=>j _.
  by apply: is_cvg_norm; apply: norm_bounded_cvg; apply: columns_summable.
move=>A; apply: (le_trans (y :=
  \sum_(j : B) psum (fun i => `|K i (val j) (d i)|) A)).
  by apply: ler_sum=>j _; apply: ler_norm_sum.
by rewrite /psum exchange_big; apply: rectangle_bound.
Qed.

Lemma apply_l1_bound : `|apply_summable| <= `|d : {summable I -> 'End(H)}|.
Proof.
rewrite {1}/Num.Def.normr /= /summable_norm.
apply: etlim_le; first exact: summable_norm_is_cvg.
exact: apply_psum_bound.
Qed.

Lemma apply_sum_bound : `|sum apply_summable| <= 1.
Proof.
apply: (le_trans (summable_sum_ler_norm apply_summable)).
rewrite -summable_norm_sumE.
apply: (le_trans apply_l1_bound).
by rewrite -CQState.mass_l1; apply: CQState.mass_le1.
Qed.

Definition apply : @CQState.state J H :=
  VDistr.build (f := apply_summable) apply_positive apply_sum_bound.

Lemma applyE j : apply j = sum (fun i => K i j (d i)).
Proof. by []. Qed.

Lemma apply_mass : CQState.mass apply <= CQState.mass d.
Proof. by rewrite !CQState.mass_l1; exact: apply_l1_bound. Qed.

End Kernel.

Section Equations.
Context {I J : choiceType} {H : chsType}.

Lemma apply_ext (K L : semType I J H H) (d : @CQState.state I H) :
  (forall i j, K i j = L i j) -> apply K d = apply L d.
Proof.
move=>KL; apply/vdistrP=>j; rewrite !applyE.
by apply: eq_sum=>i; rewrite KL.
Qed.

Lemma apply_bottom (K : semType I J H H) :
  apply K CQState.bottom = CQState.bottom.
Proof.
apply/vdistrP=>j; rewrite applyE CQState.bottomE.
under eq_sum do rewrite CQState.bottomE linear0.
exact: summable_sum_cst0.
Qed.

Lemma apply_point (K : semType I J H H) i (rho : 'FD(H)) j :
  apply K (CQState.point i rho) j = K i j rho.
Proof.
rewrite applyE (fin_supp_sum (S := [fset i])).
  by move=>k; rewrite inE=>/negPf ki; rewrite CQState.pointE ki linear0.
by rewrite psum1 CQState.pointE eqxx.
Qed.

Lemma apply_skip (d : @CQState.state I H) : apply skip_sem d = d.
Proof.
apply/vdistrP=>j; rewrite applyE (fin_supp_sum (S := [fset j])).
  by move=>i; rewrite inE eq_sym=>/negPf ji; rewrite skip_semE ji soE.
by rewrite psum1 skip_semE eqxx soE.
Qed.

Lemma apply_abort (d : @CQState.state I H) : apply abort_sem d = CQState.bottom.
Proof.
apply/vdistrP=>j; rewrite applyE CQState.bottomE.
under eq_sum do rewrite abort_semE soE.
exact: summable_sum_cst0.
Qed.
End Equations.

Section Composition.
Context {I M J : choiceType} {H : chsType}.
Variable (K : semType I M H H) (L : semType M J H H)
  (d : @CQState.state I H).

Lemma composition_branch_bound i k j :
  `|L k j (K i k (d i))| <= `|K i k (d i)|.
Proof.
have P : K i k (d i) \is psdlf by rewrite psdlfE; apply: branch_positive.
have Q : L k j (K i k (d i)) \is psdlf := cp_psdP _ P.
rewrite (psd_trfnorm Q) (psd_trfnorm P).
exact: (qo_trlfE (QOperation_Build (dso_cptn (L k) j)) P).
Qed.

Lemma composition_rectangle j : exists B, forall A N,
  psum (fun i => psum (fun k => `|L k j (K i k (d i))|) N) A <= B.
Proof.
exists `|d : {summable I -> 'End(H)}|=>A N.
apply: (le_trans _ (rectangle_bound K d A N)).
apply: ler_sum=>i _; apply: ler_sum=>k _.
exact: composition_branch_bound.
Qed.

Lemma composition_kernel_summable i j :
  summable (fun k => L k j :o K i k).
Proof.
move: (slet_norm_uboundW K L i)=>[B PB].
apply: psum_ubounded_summable; exists B=>N.
by move: (PB [fset j] N); rewrite psum1.
Qed.

Lemma apply_sequence : apply (slet K L) d = apply L (apply K d).
Proof.
apply/vdistrP=>j; rewrite [LHS]applyE.
transitivity (sum (fun i => sum (fun k => L k j (K i k (d i))))).
  apply: eq_sum=>i.
  change ((sum (fun k => L k j :o K i k)) (d i) =
    sum (fun k => L k j (K i k (d i)))).
  rewrite sum_summable_soE.
    by apply: norm_bounded_cvg; apply: composition_kernel_summable.
  by apply: eq_sum=>k; rewrite soE.
rewrite (pseries2_exchange_lim (composition_rectangle j)).
rewrite [RHS]applyE.
apply: eq_sum=>k.
rewrite applyE cvg_linear_sum.
  by apply: norm_bounded_cvg; apply: columns_summable.
by [].
Qed.
End Composition.
End CQKernel.
