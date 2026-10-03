(* Actual printed command cannot return denominators above two.
   See ORDER-FINDING-FAILURE-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import state assertion kernel language predicate
  hoare rules primitive order_finding postprocess_counterexample.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalOrderFindingFailure.
Import ClassicalLanguage CQAssertion CQPredicate CQRules ClassicalOrderFinding
  ClassicalPostprocessCounterexample.
Local Notation Hq := 'H[msys]_finset.setT.

Definition result_is (result : variable (COption CNat)) (d : nat) :
    @semantic_assertion cmem Hq :=
  mask (fun s => (s.[result])%M == Some d) semantic_top.

Lemma printed_result_ne t (bs : t.-tuple bool) d : (2 < d)%N ->
  @printed_result t bs != Some d.
Proof.
move=>Hd; apply/negP=>/eqP E.
have Hb := printed_denominator_at_most_two (ltn_ord (bseq2ord bs)) E.
by move: Hd; rewrite ltnNge Hb.
Qed.

Lemma printed_assignment_pre_zero total t
    (measured : variable (QType (QArray t QBool)))
    (result : variable (COption CNat)) d : (2 < d)%N ->
  pre total (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
    (result_is result d) = semantic_bottom.
Proof.
move=>Hd; apply/funext=>s; apply/val_inj.
change ((pre total (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
  (result_is result d) s : 'End(Hq)) = 0).
rewrite /pre CQPrimitive.assign_pre /result_is /mask get_set_eq /eval /=.
by rewrite (negbTE (printed_result_ne _ Hd)).
Qed.

Section Program.
Variables (N L t : nat).
Hypothesis HN : (1 < N)%N.
Hypothesis capacity : (N <= 2 ^ L)%N.
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).
Variable x : expression nat.
Variable measured : variable (QType (QArray t QBool)).
Variable result : variable (COption CNat).

Theorem order_finding_wp_zero d : (2 < d)%N ->
  pre true (@order_finding N L t HN capacity qr x measured result)
    (result_is result d) = semantic_bottom.
Proof.
move=>Hd; rewrite /order_finding pre_sequence pre_sequence
  (printed_assignment_pre_zero true measured result Hd).
by rewrite /pre /xp /= !wp_zero.
Qed.

Theorem order_finding_output_zero d (rho : @CQState.state cmem Hq) : (2 < d)%N ->
  expect (result_is result d)
    (CQHoare.run (@order_finding N L t HN capacity qr x measured result) rho) = 0.
Proof.
move=>Hd; rewrite /CQHoare.run -expect_wp.
change (expect (pre true (@order_finding N L t HN capacity qr x measured result)
  (result_is result d)) rho = 0).
by rewrite (order_finding_wp_zero Hd) expect_zero.
Qed.

Corollary order_finding_never_four (rho : @CQState.state cmem Hq) :
  expect (result_is result 4)
    (CQHoare.run (@order_finding N L t HN capacity qr x measured result) rho) = 0.
Proof. exact: order_finding_output_zero (isT : (2 < 4)%N). Qed.

End Program.
End ClassicalOrderFindingFailure.
