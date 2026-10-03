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
From quantum.example.classical Require Import state assertion expectation kernel language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.



Module CQKernelLimits.
Import CQKernel ClassicalLanguage.
Section Kernels.
Context {I J : choiceType} {H : chsType}.

Lemma apply_mono (K L : semType I J H H) (rho : @CQState.state I H) :
  (forall i, K i ⊑ L i) -> apply K rho ⊑ apply L rho.
Proof.
move=>KL; apply/levdP=>j.
change (sum (fun i => K i j (rho i)) ⊑ sum (fun i => L i j (rho i))).
rewrite /sum; apply: lev_lim.
- apply: norm_bounded_cvg; exact: columns_summable.
- apply: norm_bounded_cvg; exact: columns_summable.
- move=>A; apply: lev_sum=>i _.
  apply: leso_preserve_order; last exact: vdistr_ge0.
  by move: (KL (val i))=>/levdP/(_ j).
Qed.

Lemma apply_increasing (K : nat -> semType I J H H)
    (rho : @CQState.state I H) :
  (forall i, nondecreasing_seq (fun n => K n i)) ->
  nondecreasing_seq (fun n => apply (K n) rho).
Proof. by move=>inc m n mn; apply: apply_mono=>i; apply: inc. Qed.

Lemma apply_cvg_monotone (K : nat -> semType I J H H)
    (L : semType I J H H) (rho : @CQState.state I H) :
  (forall i, nondecreasing_seq (fun n => K n i)) ->
  (forall n i, K n i ⊑ L i) ->
  (forall i j, K n i j @[n --> \oo] --> L i j) ->
  (apply (K n) rho : {summable J -> 'End(H)}) @[n --> \oo] -->
    (apply L rho : {summable J -> 'End(H)}).
Proof.
move=>inc ub pointcv.
have Cpoint j : apply (K n) rho j @[n --> \oo] --> apply L rho j.
  pose col := fun n => Summable.build (columns_summable (K n) rho j).
  pose topcol := Summable.build (columns_summable L rho j).
  have ic : nondecreasing_seq col.
    move=>m n mn; apply/lesP=>i.
    apply: leso_preserve_order; last exact: vdistr_ge0.
    by move: (inc i m n mn)=>/levdP/(_ j).
  have bc : ubounded_by topcol col.
    move=>n; apply/lesP=>i.
    apply: leso_preserve_order; last exact: vdistr_ge0.
    by move: (ub n i)=>/levdP/(_ j).
  have Cc : cvgn col := snondecreasing_is_cvgn (@trfnorm_add H) ic bc.
  have E : limn col = topcol.
    apply/summableP=>i; rewrite -summableE_lim //.
    have C2 : col n i @[n --> \oo] --> L i j (rho i).
      apply: so_cvgl; exact: pointcv.
    exact (cvg_lim (@norm_hausdorff _ _) C2).
  have Csum := summable_sum_cvg Cc.
  rewrite E in Csum; exact: Csum.
have Co : cvgn (fun n => (apply (K n) rho : {summable J -> 'End(H)})).
  apply: CQState.chain_converges; exact: apply_increasing.
have E : limn (fun n => (apply (K n) rho : {summable J -> 'End(H)})) =
    (apply L rho : {summable J -> 'End(H)}).
  apply/summableP=>j; rewrite -summableE_lim //.
  exact (cvg_lim (@norm_hausdorff _ _) (Cpoint j)).
by rewrite -E.
Qed.
End Kernels.

Local Notation Hq := 'H[msys]_finset.setT.
Lemma unroll_apply_cvg b c (rho : @CQState.state cmem Hq) :
  (apply (denote (unroll b c n)) rho : {summable cmem -> 'End(Hq)}) @[n --> \oo] -->
    (apply (denote (While b c)) rho : {summable cmem -> 'End(Hq)}).
Proof.
apply: apply_cvg_monotone.
- move=>i m n mn; rewrite !denote_unroll; exact: while_sem_iter_homo mn.
- move=>n i; exact: denote_while_unroll_le.
- move=>i j; under eq_cvg do rewrite denote_unroll.
  rewrite /= -while_sem_limEE.
  apply: summableE_is_cvg; exact: while_sem_is_cvg.
Qed.

Lemma unroll_expect_cvg P b c (rho : @CQState.state cmem Hq) :
  CQAssertion.expect P (apply (denote (unroll b c n)) rho) @[n --> \oo] -->
    CQAssertion.expect P (apply (denote (While b c)) rho).
Proof. apply: CQExpectation.expect_cvg; exact: unroll_apply_cvg. Qed.
End CQKernelLimits.
