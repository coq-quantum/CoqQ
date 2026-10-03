(* Generic Born-event complement bound; see PHASE-PROBABILITY-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred svd mxnorm
  hermitian ctopology quantum hspace inhabited.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

Module ClassicalPhaseProbability.
Local Notation C := hermitian.C.

Lemma born_total (H : chsType) (T : finType) (b : 'ONB(T;H)) (psi : H) :
  \sum_(i : T) `|[< b i; psi >]|^+2 = [< psi; psi >].
Proof.
symmetry; rewrite {1}(onb_vec b psi) dotp_suml.
by apply: eq_bigr=>i _; rewrite dotpZl -normCKC.
Qed.

Theorem onb_event_complement_bound (H : chsType) (T : finType)
    (b : 'ONB(T;H)) (psi : H) (P : pred T) (m0 : T) :
  [< psi; psi >] = 1 -> ~~ P m0 ->
  \sum_(m : T | P m) `|[< b m; psi >]|^+2 <=
    1 - `|[< b m0; psi >]|^+2.
Proof.
move=>Hpsi HP.
have Et := born_total b psi.
rewrite Hpsi (bigD1 m0) //= in Et.
have Hsub : \sum_(m : T | P m) `|[< b m; psi >]|^+2 <=
    \sum_(m : T | m != m0) `|[< b m; psi >]|^+2.
  rewrite [X in X <= _]big_mkcond [X in _ <= X]big_mkcond.
  apply: ler_sum=>m _.
  case EP: (P m).
  - have Hne : m != m0.
      apply/eqP=>E; by move: HP; rewrite -E EP.
    by rewrite Hne.
  - by case: (m != m0); rewrite ?exprn_ge0.
rewrite -Et addrAC subrr add0r.
exact: Hsub.
Qed.

Theorem computational_event_complement_bound (T : ihbFinType)
    (psi : 'NS('Hs T)) (P : pred T) (m0 : T) :
  ~~ P m0 ->
  \sum_(m : T | P m) `|[< ''m; (psi : 'Hs T) >]|^+2 <=
    1 - `|[< ''m0; (psi : 'Hs T) >]|^+2.
Proof. apply: onb_event_complement_bound; exact: ns_dot. Qed.

End ClassicalPhaseProbability.
