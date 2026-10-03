(* The printed cmp(N) implies at least two distinct prime divisors.
   See SHOR-COMPOSITE-NOTES.md for the prior mathematical argument. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorComposite.

Definition not_perfect_power N :=
  forall a b, 1 < a -> 1 < b -> N != a ^ b.

Definition cmp N :=
  [ /\ 2 < N, odd N, ~~ prime N & not_perfect_power N ].

Theorem distinct_prime_count_gt1 N :
  1 < N -> ~~ prime N -> not_perfect_power N -> 1 < size (primes N).
Proof.
move=>HN Hcomposite Hpower.
have Hnonempty : primes N != [::] by rewrite primes_eq0 -leqNgt.
case E: (primes N) Hnonempty=>[//|p [|q ps]] //= _.
have Hp : prime p.
  have Hmem : p \in primes N by rewrite E mem_head.
  by move: Hmem; rewrite mem_primes=>/and3P[].
have Hfactor : N = p ^ logn p N.
  by rewrite {1}(prod_prime_decomp (ltnW HN)) prime_decompE E /= big_seq1.
have He : 1 < logn p N.
  case Ee: (logn p N) Hfactor=>[|[|e]] //= Ef.
  - by move: HN; rewrite Ef.
  - by move: Hcomposite; rewrite Ef expn1 Hp.
by have := Hpower p (logn p N) (prime_gt1 Hp) He; rewrite -Hfactor eqxx.
Qed.

Theorem cmp_distinct_prime_count N : cmp N -> 1 < size (primes N).
Proof.
move=>[HN _ Hcomposite Hpower].
exact: distinct_prime_count_gt1 (ltnW HN) Hcomposite Hpower.
Qed.

End ClassicalShorComposite.
