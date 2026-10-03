(* Absolute Fubini and expectation for cq kernels. See HOARE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQKernelExpectation.
Import CQAssertion.

Section KernelExpectation.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H) (P : J -> 'FO(H))
  (rho : @CQState.state I H).

Lemma kernel_expect_norm i j :
  `|\Tr (P j \o K i j (rho i))| <= `|K i j (rho i)|.
Proof.
have pos : 0%:VF ⊑ K i j (rho i) := CQKernel.branch_positive K rho i j.
rewrite ger0_norm; first by apply/trlfM_ge0; [apply: obsf_ge0 | exact: pos].
rewrite psd_trfnorm; first by rewrite psdlfE.
rewrite -{2}(comp_lfun1l (K i j (rho i))).
apply/(lef_psdtr (P j) (\1)); first apply: obsf_le1.
by rewrite psdlfE.
Qed.

Lemma kernel_expect_rectangle : exists B, forall A N,
  psum (fun i => psum (fun j => `|\Tr (P j \o K i j (rho i))|) N) A <= B.
Proof.
exists `|rho : {summable I -> 'End(H)}|=>A N.
apply: (le_trans _ (CQKernel.rectangle_bound K rho A N)).
apply: ler_sum=>i _; apply: ler_sum=>j _.
exact: kernel_expect_norm.
Qed.

Lemma expect_apply_sum :
  expect P (CQKernel.apply K rho) =
    sum (fun i => sum (fun j => \Tr (P j \o K i j (rho i)))).
Proof.
rewrite (pseries2_exchange_lim kernel_expect_rectangle) /expect.
apply: eq_sum=>j; rewrite /expect_term CQKernel.applyE.
apply: (cvg_linearP_sum (x := fun i => K i j (rho i))
  (f := fun x : 'End(H) => \Tr (P j \o x))).
  by move=>a x y; rewrite linearPr /= linearP.
by apply: norm_bounded_cvg; apply: CQKernel.columns_summable.
Qed.
End KernelExpectation.

Lemma expect_sunit {I J : choiceType} {H : chsType}
  (F : I -> 'QO(H)) (update : I -> J) (P : J -> 'FO(H))
  (rho : @CQState.state I H) :
  expect P (CQKernel.apply (sunit F update) rho) =
    sum (fun i => \Tr (P (update i) \o F i (rho i))).
Proof.
rewrite expect_apply_sum; apply: eq_sum=>i.
rewrite (fin_supp_sum (S := [fset update i]%fset)).
  move=>j; rewrite inE=>/negPf ji.
  by rewrite /sunit /= /sunit_def ji soE comp_lfun0r linear0.
by rewrite psum1 /sunit /= /sunit_def eqxx.
Qed.

End CQKernelExpectation.
