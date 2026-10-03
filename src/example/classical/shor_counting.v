(* Concrete failure count for Lemma 7.2(2); see SHOR-COUNTING-NOTES.md. *)
From mathcomp Require Import all_ssreflect all_algebra fingroup morphism
  quotient cyclic nilpotent abelian.
From quantum.example.classical Require Import shor_factorization shor_crt
  shor_crt_product shor_prime_power shor_modular_event shor_order_event
  shor_product_counting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorCounting.
Import ClassicalShorFactorization ClassicalShorCRT ClassicalShorCRTProduct
  ClassicalShorPrimePower ClassicalShorModularEvent ClassicalShorOrderEvent
  ClassicalShorProductCounting.
Local Open Scope group_scope.

Definition unit_failure N (u : {unit 'Z_N}) :=
  odd #[u] || (u ^+ (#[u] %/ 2) == negative_one N).

Definition unit_success N (u : {unit 'Z_N}) :=
  ~~ odd #[u] && (u ^+ (#[u] %/ 2) != negative_one N).

Lemma unit_successE N (u : {unit 'Z_N}) : unit_success u = ~~ unit_failure u.
Proof. by rewrite /unit_success /unit_failure negb_or. Qed.

Lemma bijective_pred_card (A B : finType) (f : A -> B) (P : pred B) :
  bijective f -> #|[pred a : A | P (f a)]| = #|P|.
Proof.
move=>Hf.
have E : #|[pred a : A | P (f a)]| = #|f @^-1: P|.
  by apply: eq_card=>a; rewrite !inE.
rewrite E; apply: on_card_preimset; exact: onW_bij Hf.
Qed.

Section Modulus.
Variable N : nat.
Hypotheses (HN : (1 < N)%N) (odd_N : odd N).

Let I := (Finite.clone (factor_index N) _).
Let q (i : I) := factor_modulus i.
Let Hq (i : I) := factor_modulus_gt1 i.
Let productE := esym (factorization HN).
Let Hi (i : I) := (FinGroup.clone {unit 'Z_(q i)} _).
Let Xi (i : I) := (Finite.clone {unit 'Z_(q i)} _).
Let i0 : I := first_factor HN.

Definition factor_reduction (i : I) := @reduction I q N HN Hq productE i.
Definition factor_tuple := @unit_tuple I q N HN Hq productE.
Definition order_label (i : I) (u : Xi i) := logn 2 #[u].

Lemma factor_tuple_bijective : bijective factor_tuple.
Proof.
exact: (@unit_tuple_bijective I q N HN Hq (@factor_moduli_coprime N) productE).
Qed.

Lemma factor_reduction_jointly_injective (u v : {unit 'Z_N}) :
  (forall i, factor_reduction i u = factor_reduction i v) -> u = v.
Proof.
exact: (@reductions_jointly_injective I q N HN Hq
  (@factor_moduli_coprime N) productE u v).
Qed.

Lemma factor_involution_nontrivial (i : I) : negative_one (q i) != 1.
Proof.
apply: negative_one_distinct.
exact: modulus_gt2 (factor_prime_is_prime i) (factor_prime_odd i odd_N)
  (factor_exponent_positive i).
Qed.

Lemma factor_roots_two (i : I) (u : Hi i) : u ^+ 2 = 1 ->
  u = 1 \/ u = negative_one (q i).
Proof.
exact: (@unit_square_roots (factor_prime i) (factor_exponent i)
  (factor_prime_is_prime i) (factor_prime_odd i odd_N)
  (factor_exponent_positive i) u).
Qed.

Lemma factor_reduction_negative_one (i : I) :
  factor_reduction i (negative_one N) = negative_one (q i).
Proof. exact: unit_reduce_negative_one. Qed.

Lemma failure_diagonalE (u : {unit 'Z_N}) :
  unit_failure u = natural_diagonal order_label i0 (factor_tuple u).
Proof.
rewrite /unit_failure /natural_diagonal /order_label.
transitivity [forall i : I, logn 2 #[factor_reduction i u] ==
  logn 2 #[factor_reduction i0 u]].
- exact: (@failure_iff_equal_valuations I (FinGroup.clone {unit 'Z_N} _) Hi i0
    factor_reduction factor_reduction_jointly_injective
    (fun i => negative_one (q i)) factor_involution_nontrivial factor_roots_two
    (negative_one N) factor_reduction_negative_one u).
- apply: eq_forallb=>i; by rewrite /factor_tuple !unit_tupleE.
Qed.

Lemma failure_card : #|@unit_failure N| = #|natural_diagonal order_label i0|.
Proof.
rewrite -(bijective_pred_card (natural_diagonal order_label i0) factor_tuple_bijective).
exact: eq_card failure_diagonalE.
Qed.

Lemma factor_order_fiber_half (i : I) k :
  (2 * #|[pred u : Xi i | @order_label i u == k]| <= #|Xi i|)%N.
Proof.
have H := @prime_power_fiber_half (factor_prime i) (factor_exponent i)
  (factor_prime_is_prime i) (factor_prime_odd i odd_N) (factor_exponent_positive i) k.
have E : #|[pred u : Xi i | @order_label i u == k]| =
    #|[set u : {unit 'Z_(q i)} | logn 2 #[u] == k]|.
  by apply: eq_card=>u; rewrite !inE.
by rewrite E.
Qed.

Theorem failure_count_bound :
  (2 ^ (size (primes N)).-1 * #|@unit_failure N| <= totient N)%N.
Proof.
have Hhalf : forall i k, i != i0 ->
    (2 * #|[pred u : Xi i | @order_label i u == k]| <= #|Xi i|)%N.
  move=>i k _; exact: factor_order_fiber_half.
have H := @natural_diagonal_half_bound I Xi order_label i0 Hhalf.
have Ec : #|{: {dffun forall i : I, Xi i}}| = totient N.
  rewrite -(bij_eq_card factor_tuple_bijective) -cardsT -/(units_Zp N).
  by rewrite card_units_Zp //; exact: ltnW HN.
by move: H; rewrite /I card_ord Ec -failure_card.
Qed.

End Modulus.
End ClassicalShorCounting.
