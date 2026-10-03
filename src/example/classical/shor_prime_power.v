(* Odd-prime-power square roots for classical paper Lemma 7.2(2).
   The prior mathematical argument is in SHOR-COUNTING-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_fingroup cyclic.
From quantum.example.classical Require Import shor_group_counting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorPrimePower.

Section NaturalRoots.
Variables p e : nat.
Hypotheses (prime_p : prime p) (odd_p : odd p) (positive_e : 0 < e).
Let q := p ^ e.

Lemma modulus_gt2 : 2 < q.
Proof.
apply: leq_trans (odd_prime_gt2 odd_p prime_p) _.
rewrite /q -{1}(expn1 p) leq_exp2l //; exact: prime_gt1.
Qed.

Lemma modulus_positive : 0 < q.
Proof. exact: ltn_trans (ltn0Sn 1) modulus_gt2. Qed.

Lemma roots_distinct : (1 == q.-1 %[mod q]) = false.
Proof.
have Hq1 : 1 < q := ltnW modulus_gt2.
have Hpred : q.-1 < q by rewrite ltn_predL modulus_positive.
rewrite (modn_small Hq1) (modn_small Hpred).
apply: ltn_eqF; by rewrite ltn_predRL; exact: modulus_gt2.
Qed.

Lemma root_representative s : s < q -> s ^ 2 == 1 %[mod q] ->
  s = 1 \/ s = q.-1.
Proof.
move=>Hsq Hroot.
have Hq1 : 1 < q := ltnW modulus_gt2.
have Hs0 : 0 < s.
  apply/negPn/negP=>Hs; have Es : s = 0 by move: Hs; rewrite -eqn0Ngt=>/eqP.
  by move: Hroot; rewrite Es exp0n // mod0n (modn_small Hq1).
have Hs1 : 1 <= s := Hs0.
have Hs2 : 1 <= s ^ 2 by rewrite -[1](exp1n 2) leq_sqr.
have D : q %| (s - 1) * (s + 1).
  by rewrite -subn_sqr exp1n -(eqn_mod_dvd q Hs2).
case Hminus: (p %| s - 1).
- have Hplus : ~~ (p %| s + 1).
    apply/negP=>Hplus.
    have D2 : p %| 2.
      have := dvdn_sub Hplus Hminus.
      by rewrite subnBA // -addnA addKn.
    by move: D2; rewrite (gtnNdvd (isT : 0 < 2) (odd_prime_gt2 odd_p prime_p)).
  have C : coprime q (s + 1).
    by rewrite /q coprime_pexpl // prime_coprime.
  have Dm : q %| s - 1 by move: D; rewrite Gauss_dvdl.
  left; have Z : s - 1 = 0.
    apply/eqP; apply/negPn/negP=>Hnz.
    have Hm : 0 < s - 1 by rewrite lt0n.
    have Hsmall : s - 1 < q := leq_ltn_trans (leq_subr 1 s) Hsq.
    by move: Dm; rewrite (gtnNdvd Hm Hsmall).
  by rewrite -(subnK Hs1) Z.
- have C : coprime q (s - 1).
    by rewrite /q coprime_pexpl // prime_coprime // Hminus.
  have Dp : q %| s + 1 by move: D; rewrite Gauss_dvdr.
  have Hplus : 0 < s + 1 by rewrite addn1.
  have Eq : s + 1 = q.
    apply/eqP; rewrite eqn_leq; apply/andP; split.
    + by rewrite addn1.
    + exact: dvdn_leq Hplus Dp.
  right; by rewrite -Eq addn1.
Qed.

Theorem square_roots_mod x : x ^ 2 == 1 %[mod q] ->
  (x == 1 %[mod q]) || (x == q.-1 %[mod q]).
Proof.
move=>Hx.
have Hr : (x %% q) ^ 2 == 1 %[mod q] by rewrite modnXm.
have Hlt : x %% q < q by rewrite ltn_mod modulus_positive.
case: (root_representative Hlt Hr)=>E; apply/orP.
- left; by rewrite E modn_small //; exact: ltnW modulus_gt2.
- right; have Hpred : q.-1 < q by rewrite ltn_predL modulus_positive.
  by rewrite E (modn_small Hpred).
Qed.

End NaturalRoots.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma unit_negative_one_proof n : (-1 : 'Z_n) \is a GRing.unit.
Proof. by rewrite unitrN unitr1. Qed.
Definition negative_one n : {unit 'Z_n} :=
  FinRing.unit 'Z_n (unit_negative_one_proof n).

Lemma negative_one_nat n : (1 < n)%N -> (val (negative_one n) : nat) = n.-1.
Proof.
case: n=>[//|[//|n]] _.
by rewrite /negative_one /= /Zp_trunc /=
  (modn_small (isT : (1 < n.+2)%N)) subn1 modn_small.
Qed.

Lemma unit_one_nat n : (val (1%g : {unit 'Z_n}) : nat) = 1%N.
Proof. by change ((1 %% (Zp_trunc n).+2)%N = 1%N); rewrite modn_small. Qed.

Lemma unit_power_nat n (u : {unit 'Z_n}) k : (1 < n)%N ->
  (val (u ^+ k)%g : nat) = ((val u : nat) ^ k %% n)%N.
Proof.
move=>Hn; rewrite unit_Zp_expg /=.
exact: (congr1 (fun d => ((val u : nat) ^ k %% d)%N) (Zp_cast Hn)).
Qed.

Lemma negative_one_square n : ((negative_one n) ^+ 2 = 1)%g.
Proof. by apply/val_inj; rewrite FinRing.val_unitX /= expr2 mulrNN mulr1. Qed.

Lemma negative_one_distinct n : (2 < n)%N -> negative_one n != 1%g.
Proof.
move=>Hn; apply/negP=>/eqP E.
have En := congr1 (fun u : {unit 'Z_n} => (val u : nat)) E.
rewrite negative_one_nat ?(ltnW Hn) // unit_one_nat in En.
have Hpred : (1 < n.-1)%N by rewrite ltn_predRL.
by move: Hpred; rewrite En.
Qed.

Local Open Scope group_scope.

Section UnitRoots.
Variables p e : nat.
Hypotheses (prime_p : prime p) (odd_p : odd p) (positive_e : (0 < e)%N).
Let q := (p ^ e)%N.

Lemma unit_modulus_gt2 : (2 < q)%N.
Proof. exact: modulus_gt2 prime_p odd_p positive_e. Qed.

Theorem unit_square_roots (u : {unit 'Z_q}) : (u ^+ 2 = 1)%g ->
  u = 1%g \/ u = negative_one q.
Proof.
move=>Hu; have Hq1 : (1 < q)%N := ltnW unit_modulus_gt2.
have Huq : ((val u : nat) < q)%N.
  apply: leq_trans (valP (val u)) _.
  by rewrite (Zp_cast Hq1).
have Hnat : ((val u : nat) ^ 2 == 1 %[mod q])%N.
  apply/eqP; rewrite (modn_small Hq1).
  have := congr1 (fun v : {unit 'Z_q} => (val v : nat)) Hu.
  by rewrite unit_power_nat // unit_one_nat.
case: (@root_representative p e prime_p odd_p positive_e (val u) Huq Hnat)=>E.
- left; apply/val_inj; apply/val_inj.
  change ((val u : nat) = (val (1%g : {unit 'Z_q}) : nat)).
  by rewrite unit_one_nat.
- right; apply/val_inj; apply/val_inj.
  change ((val u : nat) = (val (negative_one q) : nat)).
  by rewrite negative_one_nat.
Qed.


Theorem prime_power_fiber_half k :
  (2 * #|[set u : {unit 'Z_q} | logn 2 #[u] == k]| <= #|{: {unit 'Z_q}}|)%N.
Proof.
apply: (@ClassicalShorGroupCounting.order_valuation_fiber_half
  _ (negative_one q)).
- exact: units_Zp_abelian.
- apply: negative_one_distinct; exact: unit_modulus_gt2.
- exact: negative_one_square.
- exact: unit_square_roots.
Qed.

End UnitRoots.
End ClassicalShorPrimePower.

