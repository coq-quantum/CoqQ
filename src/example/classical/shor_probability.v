(* Numerical finite-probability corollary for Lemma 7.2(2).
   See SHOR-PROBABILITY-NOTES.md for the prior argument. *)
From mathcomp Require Import all_ssreflect all_algebra.
From quantum.example.classical Require Import shor_counting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Module ClassicalShorProbability.
Import ClassicalShorCounting.

Lemma finite_complement_ratio (F : numFieldType) (T : finType) (bad : pred T) d :
  (0 < d)%N -> (0 < #|{:T}|)%N -> (d * #|bad| <= #|{:T}|)%N ->
  (1 - 1 / d%:R <= (#|predC bad|)%:R / (#|{:T}|)%:R :> F).
Proof.
move=>Hd Hn Hcount.
have HdF : (0 : F) < d%:R by rewrite ltr0n.
have HnF : (0 : F) < (#|{:T}|)%:R by rewrite ltr0n.
have C : #|{:T}| = (#|predC bad| + #|bad|)%N.
  by rewrite addnC cardC.
rewrite ler_pdivlMr // mulrBl mul1r [d%:R^-1 * _]mulrC.
rewrite lerBlDr {1}C natrD mul1r lerD2l ler_pdivlMr //.
by rewrite -natrM mulnC ler_nat.
Qed.

Theorem uniform_unit_success_bound (F : numFieldType) N :
  (1 < N)%N -> odd N ->
  (1 - 1 / ((2 ^ (size (primes N)).-1)%N)%:R <=
   (#|@unit_success N|)%:R / (totient N)%:R :> F).
Proof.
move=>HN odd_N.
have HN0 : (0 < N)%N := ltnW HN.
have Ecard : #|{: {unit 'Z_N}}| = totient N.
  by rewrite -cardsT -/(units_Zp N) card_units_Zp.
have Hcard : (0 < #|{: {unit 'Z_N}}|)%N.
  by rewrite Ecard totient_gt0.
have Egood : #|predC (@unit_failure N)| = #|@unit_success N|.
  apply: eq_card=>u.
  change (~~ unit_failure u = unit_success u).
  exact: esym (unit_successE u).
have Hcount := @failure_count_bound N HN odd_N.
rewrite -Ecard in Hcount.
have Hd : (0 < 2 ^ (size (primes N)).-1)%N by rewrite expn_gt0.
have H := @finite_complement_ratio F [the finType of {unit 'Z_N}]
  (@unit_failure N) _ Hd Hcard Hcount.
by move: H; rewrite Ecard Egood.
Qed.

Lemma mixture_lower_bound (F : numFieldType) (lambda p c : F) :
  0 <= lambda -> 0 <= p -> p <= 1 -> 0 <= c -> c <= 1 ->
  p * c <= lambda + p * ((1 - lambda) * c).
Proof.
move=>Hlambda Hp0 Hp1 Hc0 Hc1.
have Hpc : p * c <= 1.
  by move: (ler_pM Hp0 Hc0 Hp1 Hc1); rewrite mul1r.
have Hd : 0 <= lambda * (1 - p * c).
  by apply: mulr_ge0=>//; rewrite subr_ge0.
have E : lambda + p * ((1 - lambda) * c) = p * c + lambda * (1 - p * c).
  ring.
by rewrite E lerDl.
Qed.

End ClassicalShorProbability.
