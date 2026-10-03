(* The distinct prime-power decomposition used in Lemma 7.2(2).
   See SHOR-COUNTING-NOTES.md for the mathematical argument. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorFactorization.
Section Factorization.
Variable N : nat.
Hypothesis HN : 1 < N.

Definition factor_index := 'I_(size (primes N)).
Definition factor_prime (i : factor_index) := nth 0 (primes N) i.
Definition factor_exponent i := logn (factor_prime i) N.
Definition factor_modulus i := factor_prime i ^ factor_exponent i.

Lemma factor_count_positive : 0 < size (primes N).
Proof. by rewrite lt0n size_eq0 primes_eq0 -leqNgt. Qed.

Definition first_factor : factor_index := Ordinal factor_count_positive.

Lemma factor_prime_mem i : factor_prime i \in primes N.
Proof. exact: mem_nth (ltn_ord i). Qed.

Lemma factor_prime_is_prime i : prime (factor_prime i).
Proof. by have := factor_prime_mem i; rewrite mem_primes=>/and3P[]. Qed.

Lemma factor_prime_divides i : factor_prime i %| N.
Proof. by have := factor_prime_mem i; rewrite mem_primes=>/and3P[]. Qed.

Lemma factor_exponent_positive i : 0 < factor_exponent i.
Proof. by rewrite /factor_exponent logn_gt0 factor_prime_mem. Qed.

Lemma factor_modulus_gt1 i : 1 < factor_modulus i.
Proof.
have Hp := prime_gt1 (factor_prime_is_prime i).
by rewrite /factor_modulus -[1](expn0 (factor_prime i)) ltn_exp2l // factor_exponent_positive.
Qed.

Lemma factor_prime_injective : injective factor_prime.
Proof.
move=>i j /eqP Hij; apply/val_inj/eqP.
by move: Hij; rewrite /factor_prime nth_uniq ?primes_uniq ?ltn_ord.
Qed.

Lemma factor_moduli_coprime i j : i != j -> coprime (factor_modulus i) (factor_modulus j).
Proof.
move=>Hij; apply/coprimeXl/coprimeXr.
rewrite prime_coprime ?factor_prime_is_prime // dvdn_prime2 ?factor_prime_is_prime //.
by rewrite (inj_eq factor_prime_injective).
Qed.

Lemma factor_modulus_divides i : factor_modulus i %| N.
Proof. by rewrite /factor_modulus /factor_exponent pfactor_dvdn ?factor_prime_is_prime // (ltnW HN). Qed.

Lemma factor_prime_odd i : odd N -> odd (factor_prime i).
Proof. exact: dvdn_odd (factor_prime_divides i). Qed.

Lemma factor_modulus_odd i : odd N -> odd (factor_modulus i).
Proof. exact: dvdn_odd (factor_modulus_divides i). Qed.

Lemma factorization : N = \prod_(i : factor_index) factor_modulus i.
Proof.
rewrite {1}(prod_prime_decomp (ltnW HN)) prime_decompE big_map /=.
by rewrite (big_nth 0) big_mkord.
Qed.

End Factorization.
End ClassicalShorFactorization.
