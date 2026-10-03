(* Independence from unused finite quantum memory.
   See HOARE-NOTES.md for the depolarizer and partial-trace argument. *)
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


From quantum.example.classical Require Import quantum_frame quantum_selector quantum_trace.

Module CQMemoryExtension.
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame CQQuantumTrace.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma uniform_nonzero (U : chsType) : uniform_weight U != 0.
Proof. by rewrite /uniform_weight invr_eq0 pnatr_eq0 -lt0n dim_proper. Qed.

Lemma depolarizer_full (T : {set mlab}) (A : 'End(Hq)) :
  liftfso (depolarizer msys T) A =
  uniform_weight 'H[msys]_T *: liftf_lf (ptraceso T A).
Proof.
have E := @lift_depolarizer _ msys finset.setT T A.
by rewrite finset.setTI liftf_lf_id in E.
Qed.

Theorem denote_partial_trace c (T : {set mlab}) m out (rho : 'End(Hq)) :
  [disjoint quantum_variables c & T] ->
  liftf_lf (ptraceso T (denote c m out rho)) =
    denote c m out (liftf_lf (ptraceso T rho)).
Proof.
move=>Hdis.
have E := congr1 (fun F : 'SO(Hq) => F rho)
  (@denote_disjoint_commute c T (depolarizer msys T) Hdis m out).
rewrite !comp_soE !depolarizer_full linearZ /= in E.
apply: (@scalerI _ _ (uniform_weight 'H[msys]_T) (uniform_nonzero _)).
exact: esym E.
Qed.

Theorem denote_marginal_ext c (T : {set mlab}) m out (rho sigma : 'End(Hq)) :
  [disjoint quantum_variables c & T] -> ptraceso T rho = ptraceso T sigma ->
  ptraceso T (denote c m out rho) = ptraceso T (denote c m out sigma).
Proof.
move=>Hdis E; apply: liftf_lf_inj.
by rewrite !denote_partial_trace // E.
Qed.

Theorem apply_marginal_ext c (T : {set mlab})
  (d e : @CQState.state cmem Hq) :
  [disjoint quantum_variables c & T] ->
  (forall m, ptraceso T (d m) = ptraceso T (e m)) -> forall out,
  ptraceso T (CQKernel.apply (denote c) d out) =
    ptraceso T (CQKernel.apply (denote c) e out).
Proof.
move=>Hdis E out; rewrite !CQKernel.applyE.
rewrite (cvg_linearP_sum (x := fun m => denote c m out (d m))
  (f := ptraceso T) (superop_is_linear (ptraceso T))).
- by apply: norm_bounded_cvg; exact: CQKernel.columns_summable.
rewrite (cvg_linearP_sum (x := fun m => denote c m out (e m))
  (f := ptraceso T) (superop_is_linear (ptraceso T))).
- by apply: norm_bounded_cvg; exact: CQKernel.columns_summable.
apply:eq_sum=>m; exact: denote_marginal_ext Hdis (E m).
Qed.

Theorem partial_trace_product (T : {set mlab})
  (A : 'F[msys]_(finset.setT :\: T)) (B : 'F[msys]_T) :
  ptraceso T (liftf_lf A \o liftf_lf B) = \Tr B *: A.
Proof.
have Hd : [disjoint finset.setT :\: T & T].
  by rewrite finset.setTD disjointCX.
apply: liftf_lf_inj.
apply: (@scalerI _ _ (uniform_weight 'H[msys]_T) (uniform_nonzero _)).
rewrite -depolarizer_full liftfsoEf_compl // liftfsoEf depolarizerE
  !linearZ /= liftf_lf1 comp_lfun1r.
by rewrite !scalerA mulrC.
Qed.

Theorem normalized_memory_extension c (T : {set mlab}) m out
  (A : 'F[msys]_(finset.setT :\: T)) (B D : 'FD1('H[msys]_T)) :
  [disjoint quantum_variables c & T] ->
  ptraceso T (denote c m out (liftf_lf A \o liftf_lf B)) =
    ptraceso T (denote c m out (liftf_lf A \o liftf_lf D)).
Proof.
move=>Hdis; apply: denote_marginal_ext Hdis _.
by rewrite !partial_trace_product !den1f_trlf.
Qed.
End CQMemoryExtension.
