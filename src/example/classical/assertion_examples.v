(* Checked assertion examples over unbounded natural-number memory. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology.
From quantum Require Import hermitian quantum summable.
From quantum.example.classical Require Import assertion.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CQAssertionExamples.
Import CQAssertion.

(* A small, explicit classical formula language, with unbounded memories. *)
Inductive formula :=
| constant of bool
| is_zero
| negate of formula
| conjunction of formula & formula
| disjunction of formula & formula.

Fixpoint eval (p : formula) (n : nat) : bool :=
  match p with
  | constant b => b
  | is_zero => n == 0%N
  | negate p => ~~ eval p n
  | conjunction p q => eval p n && eval q n
  | disjunction p q => eval p n || eval q n
  end.

Section ZeroTest.
Variable (H : chsType) (M : 'FO(H)).

Definition zero_test_value (n : nat) :=
  if n == 0%N then M else (0%:VF : 'FO(H)).

Lemma zero_test_countable :
  countable [set A | exists n, zero_test_value n = A].
Proof.
apply: (sub_countable (B := [set M; (0%:VF : 'FO(H))])).
  apply: subset_card_le=>A [n <-]; rewrite /zero_test_value.
  by case: ifP=>_; [left | right].
apply/finite_set_countable/finite_set2.
Qed.

Lemma zero_test_definable A :
  exists p, forall n, eval p n <-> zero_test_value n = A.
Proof.
exists (disjunction
  (conjunction is_zero (constant (M == A)))
  (conjunction (negate is_zero) (constant ((0%:VF : 'FO(H)) == A)))).
move=>n; rewrite /= /zero_test_value.
by case: (n == 0%N); rewrite /= ?orbF; split=>/eqP.
Qed.

Definition zero_test_assertion :
  @CQAssertion.assertion _ H formula (fun p (n : nat) => eval p n) :=
  @CQAssertion.Assertion _ H formula (fun p (n : nat) => eval p n)
    zero_test_value zero_test_countable (fun A _ => zero_test_definable A).

Example zero_test_at_zero : zero_test_assertion 0%N = M.
Proof. by []. Qed.

Example zero_test_at_successor n : zero_test_assertion n.+1 = (0%:VF : 'FO(H)).
Proof. by []. Qed.

Example zero_test_expectation_bound (rho : {vdistr nat -> 'End(H)}) :
  0 <= expect zero_test_assertion rho <= 1.
Proof. by rewrite expect_ge0 expect_le1. Qed.

Example zero_test_single_memory (rho : {vdistr nat -> 'End(H)}) :
  (forall n, n != 0%N -> rho n = 0) ->
  expect zero_test_assertion rho = \Tr (M \o rho 0%N).
Proof. exact: expect_singleton. Qed.

Example empty_guard_expectation (rho : {vdistr nat -> 'End(H)}) :
  expect (mask pred0 zero_test_assertion) rho = 0.
Proof. exact: expect_mask_false. Qed.

Example full_guard_expectation (rho : {vdistr nat -> 'End(H)}) :
  expect (mask predT (fun _ => (\1 : 'FO(H)))) rho = \Tr (sum rho).
Proof. by rewrite expect_mask_true expect_identity. Qed.

End ZeroTest.
End CQAssertionExamples.
