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
From quantum.example.classical Require Import state assertion expectation.
From quantum Require Import cpo.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.



Module CQExpectationLimits.
Import CQAssertion CQExpectation.
Section Limits.
Context {I : choiceType} {H : chsType}.
Local Notation C := hermitian.C.

Lemma scalar_norm_add (x y : C) :
  0 <= x -> 0 <= y -> `|x+y| = `|x| + `|y|.
Proof. by move=>Hx Hy; rewrite !ger0_norm ?addr_ge0. Qed.

Lemma effect_sup_cvg (f : nat -> 'FO(H)) : chain f ->
  (f n : 'End(H)) @[n --> \oo] --> (LfunCPO.oflub f : 'End(H)).
Proof.
move=>inc.
have Cf := vnondecreasing_is_cvgn (LfunCPO.chainof2f inc)
  (LfunCPO.chainof_ub f).
rewrite /LfunCPO.oflub; case: eqP=>P.
- exact: Cf.
- exfalso; apply: P; exact: LfunCPO.limn_obslf Cf.
Qed.

Lemma semantic_sup_cvg (f : nat -> I -> 'FO(H)) : semantic_chain f ->
  forall i, (f n i : 'End(H)) @[n --> \oo] --> (semantic_sup f i : 'End(H)).
Proof. move=>inc i; apply: effect_sup_cvg; exact: semantic_point_chain. Qed.

Lemma expect_semantic_sup (f : nat -> I -> 'FO(H))
    (rho : @CQState.state I H) : semantic_chain f ->
  expect (f n) rho @[n --> \oo] --> expect (semantic_sup f) rho.
Proof.
move=>inc.
pose a := fun n => pair_terms (f n) (rho : {summable I -> 'End(H)}).
pose b := pair_terms (semantic_top : I -> 'FO(H)) (rho : {summable I -> 'End(H)}).
have ia : nondecreasing_seq a.
  move=>m n mn; apply/lesP=>i.
  change (\Tr (f m i \o rho i) <= \Tr (f n i \o rho i)).
  apply/(lef_psdtr (f m i) (f n i)); last by rewrite psdlfE vdistr_ge0.
  exact: (LfunCPO.chainof2f (semantic_point_chain inc i) mn).
have ab : ubounded_by b a.
  move=>n; apply/lesP=>i.
  change (\Tr (f n i \o rho i) <= \Tr (\1 \o rho i)).
  apply/(lef_psdtr (f n i) (\1)); first exact: obsf_le1.
  by rewrite psdlfE vdistr_ge0.
have Ca : cvgn a := snondecreasing_is_cvgn scalar_norm_add ia ab.
have E : limn a = pair_terms (semantic_sup f) (rho : {summable I -> 'End(H)}).
  apply/summableP=>i.
  have C2 : a n i @[n --> \oo] --> \Tr (semantic_sup f i \o rho i).
    change (\Tr (f n i \o rho i) @[n --> \oo] -->
      \Tr (semantic_sup f i \o rho i)).
    apply: continuous_cvg; first exact: trlf_continuous.
    apply: lfun_comp_cvgl; exact: semantic_sup_cvg inc i.
  rewrite -summableE_lim //.
  exact (cvg_lim (@norm_hausdorff _ _) C2).
have Csum := summable_sum_cvg Ca.
rewrite E in Csum; exact: Csum.
Qed.

Definition semantic_decreasing (f : nat -> I -> 'FO(H)) :=
  forall n, semantic_le (f n.+1) (f n).
Definition semantic_inf (f : nat -> I -> 'FO(H)) :=
  complement (semantic_sup (fun n => complement (f n))).

Lemma complement_involutive (P : I -> 'FO(H)) :
  complement (complement P) = P.
Proof.
by apply/funext=>i; apply/val_inj; rewrite /complement /= cplmtK.
Qed.

Lemma complement_chain f : semantic_decreasing f ->
  semantic_chain (fun n => complement (f n)).
Proof. by move=>inc n i; rewrite /complement /= -cplmt_lef; apply: inc. Qed.

Lemma semantic_inf_cvg (f : nat -> I -> 'FO(H)) : semantic_decreasing f ->
  forall i, (f n i : 'End(H)) @[n --> \oo] --> (semantic_inf f i : 'End(H)).
Proof.
move=>dec i.
have Cc := semantic_sup_cvg (i := i) (complement_chain dec).
change ((fun n => (f n i : 'End(H))) @ \oo -->
  (\1 - (semantic_sup (fun n => complement (f n)) i : 'End(H))))%classic.
have E n : (f n i : 'End(H)) = \1 - (complement (f n) i : 'End(H)).
  by rewrite /complement /= -/(cplmt (cplmt (f n i))) cplmtK.
under eq_cvg do rewrite E.
apply: cvgB; first exact: cvg_cst.
exact: Cc.
Qed.

Lemma expect_semantic_inf (f : nat -> I -> 'FO(H))
    (rho : @CQState.state I H) : semantic_decreasing f ->
  expect (f n) rho @[n --> \oo] --> expect (semantic_inf f) rho.
Proof.
move=>dec; have Cc := expect_semantic_sup (rho := rho) (complement_chain dec).
rewrite /semantic_inf expect_complement.
have E n : expect (f n) rho = \Tr (sum rho) - expect (complement (f n)) rho.
  by rewrite expect_complement opprB addrCA subrr addr0.
under eq_cvg do rewrite E.
apply: cvgB; first exact: cvg_cst.
exact: Cc.
Qed.
End Limits.
End CQExpectationLimits.
