(* A counterexample to classical.pdf Lemma 4.15(3), partial mode.
   See PARAMETERIZED-COUNTEREXAMPLE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion language kernel
  kernel_expectation predicate hoare rules parameterized.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQParameterizedCounterexample.
Import ClassicalLanguage CQAssertion CQPredicate CQParameterized.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma selector_list_none_partial (I : finType) (choose : expression (option I))
    (branch : I -> command) indices m (Q : assertion) :
  eval choose m = None ->
  CQRules.pre false (selector_list choose branch indices) Q m = \1.
Proof.
move=>He; elim: indices=>[|i rest IH].
- by rewrite /selector_list /CQRules.pre /xp /= wlp_abort.
- change (CQRules.pre false
    (Conditional (selector_guard choose i) (branch i)
      (selector_list choose branch rest)) Q m = \1).
  by rewrite CQRules.pre_conditional /conditional /selector_guard /eval /=
    -/(eval choose m) He.
Qed.

Theorem parameterized_zero_partial t K (q : wf_qreg t)
    (U : 'I_K -> 'FU('Ht t)) (Q : assertion) m :
  CQRules.pre false (parameterized_unitary q U (EConst (0 : int))) Q m = \1.
Proof. apply: selector_list_none_partial; exact: parameter_selector_zero. Qed.

Theorem parameterized_zero_printed t K (q : wf_qreg t)
    (U : 'I_K -> 'FU('Ht t)) (Q : assertion) m :
  parameterized_pre q U (EConst (0 : int)) Q m = 0%:VF.
Proof. by rewrite /parameterized_pre /selector_pre parameter_selector_zero. Qed.

Theorem parameterized_zero_counterexample t K (q : wf_qreg t)
    (U : 'I_K -> 'FU('Ht t)) (Q : assertion) m :
  CQRules.pre false (parameterized_unitary q U (EConst (0 : int))) Q m !=
    parameterized_pre q U (EConst (0 : int)) Q m.
Proof.
rewrite parameterized_zero_partial parameterized_zero_printed.
apply/negP=>/eqP E.
have H := congr1 (fun A : 'FO(Hq) => (A : 'End(Hq))) E.
by move/eqP: H; rewrite /= oner_eq0.
Qed.

End CQParameterizedCounterexample.
