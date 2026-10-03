(* Concrete distinguished-involution reduction for Lemma 7.2(2).
   See SHOR-MODULAR-EVENT-NOTES.md for the prior mathematical argument. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup cyclic.
From quantum.example.classical Require Import shor_crt shor_prime_power.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorModularEvent.
Import ClassicalShorCRT ClassicalShorPrimePower.

Lemma predecessor_mod_divisor N M :
  1 < N -> 1 < M -> M %| N -> N.-1 %% M = M.-1.
Proof.
move=>HN HM D.
have HM1 : M != 1 by rewrite eq_sym (ltn_eqF HM).
by rewrite modn_pred ?HM1 ?(ltnW HN) ?D.
Qed.

Theorem unit_reduce_negative_one N M (HN : 1 < N) (HM : 1 < M) (D : M %| N) :
  @unit_reduce N M HN HM D (negative_one N) = negative_one M.
Proof.
have EN : unit_value (negative_one N) = N.-1 := @negative_one_nat N HN.
have EM : unit_value (negative_one M) = M.-1 := @negative_one_nat M HM.
apply: unit_value_inj; rewrite unit_reduce_value EN EM.
exact: predecessor_mod_divisor HN HM D.
Qed.

End ClassicalShorModularEvent.
