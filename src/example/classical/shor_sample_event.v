(* The paper's natural-number order event on actual uniform samples.
   See SHOR-SAMPLE-EVENT-NOTES.md. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup cyclic.
From quantum.example.classical Require Import shor_crt shor_prime_power shor_counting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module ClassicalShorSampleEvent.
Import ClassicalShorCRT ClassicalShorPrimePower ClassicalShorCounting.
Local Open Scope group_scope.
Local Open Scope nat_scope.

Section Modulus.
Variable N : nat.
Hypothesis HN : 1 < N.

Definition natural_unit a : {unit 'Z_N} :=
  insubd (1%g : {unit 'Z_N}) (a%:R : 'Z_N)%R.

Lemma natural_unit_value a : coprime N a -> unit_value (natural_unit a) = a %% N.
Proof.
move=>Ha; rewrite /natural_unit /unit_value val_insubd.
rewrite unitZpE // Ha.
exact: val_Zp_nat.
Qed.

Lemma natural_unitK (u : {unit 'Z_N}) : natural_unit (unit_value u) = u.
Proof.
apply: unit_value_inj.
by rewrite natural_unit_value ?unit_value_coprime // modn_small ?unit_value_lt.
Qed.

Definition natural_order a := #[natural_unit a].

Lemma natural_order_positive a : 0 < natural_order a.
Proof. exact: order_gt0. Qed.

Lemma natural_power_value a k : coprime N a ->
  unit_value ((natural_unit a) ^+ k) = a ^ k %% N.
Proof.
move=>Ha; by rewrite (unit_value_power HN) natural_unit_value // modnXm.
Qed.

Theorem natural_order_dvd a k : coprime N a ->
  (natural_order a %| k) = (a ^ k == 1 %[mod N]).
Proof.
move=>Ha; rewrite /natural_order order_dvdn -(inj_eq (@unit_value_inj N)).
by rewrite natural_power_value // (unit_value_one HN) (modn_small HN).
Qed.

Lemma natural_order_power a : coprime N a -> a ^ natural_order a == 1 %[mod N].
Proof. by move=>Ha; rewrite -(natural_order_dvd _ Ha) dvdnn. Qed.

Lemma natural_order_minimal a k : coprime N a ->
  0 < k < natural_order a -> ~~ (a ^ k == 1 %[mod N]).
Proof.
move=>Ha /andP[Hk Hlt]; rewrite -(natural_order_dvd _ Ha).
apply/negP=>D; by move: Hlt; rewrite ltnNge (dvdn_leq Hk D).
Qed.

Definition natural_success a :=
  ~~ odd (natural_order a) &&
    ~~ (a ^ (natural_order a %/ 2) == N.-1 %[mod N]).

Theorem natural_success_unit (u : {unit 'Z_N}) :
  natural_success (unit_value u) = unit_success u.
Proof.
rewrite /natural_success /natural_order natural_unitK /unit_success.
rewrite -(inj_eq (@unit_value_inj N)) (unit_value_power HN).
have E : unit_value (negative_one N) = N.-1 := @negative_one_nat N HN.
have Hpred : N.-1 < N by rewrite ltn_predL; exact: ltnW HN.
by rewrite E (modn_small Hpred).
Qed.

End Modulus.
End ClassicalShorSampleEvent.
