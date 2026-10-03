(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)
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
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.



Module CQRanking.
Import CQAssertion CQRules CQExpectationLimits.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma ranking_infimum P b c (r : ranking P b c) :
  semantic_inf (ranking_assertion r) = semantic_bottom.
Proof.
apply/funext=>s; apply/val_inj.
change ((semantic_inf (ranking_assertion r) s : 'End(Hq)) = 0).
have C1 := @semantic_inf_cvg cmem Hq (ranking_assertion r)
  (ranking_decreases r) s.
have C2 := @ranking_zero P b c r s.
by rewrite -(cvg_lim (@norm_hausdorff _ _) C1) (cvg_lim (@norm_hausdorff _ _) C2).
Qed.

Definition ranking_of_infimum P b c (f : nat -> assertion)
    (dec : semantic_decreasing f) (ini : semantic_le P (f 0%N))
    (infimum : semantic_inf f = semantic_bottom)
    (step : forall n, semantic_le (mask (esem b) (wp_command c (f n))) (f n.+1))
    : ranking P b c.
Proof.
apply: (@Ranking P b c f dec ini _ step)=>s.
have C := @semantic_inf_cvg cmem Hq f dec s.
by rewrite infimum in C.
Defined.
End CQRanking.
