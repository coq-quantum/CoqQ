(* Finite-group counting for Lemma 7.2(2); see SHOR-COUNTING-NOTES.md. *)
From mathcomp Require Import all_ssreflect all_algebra fingroup morphism
  quotient cyclic nilpotent abelian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorGroupCounting.

Lemma dvdn_half_logn d n : 0 < n -> d %| n -> 2 %| n ->
  (d %| n %/ 2) = (logn 2 d < logn 2 n).
Proof.
move=>Hn Hd H2.
have Hd0 : 0 < d := dvdn_gt0 Hn Hd.
have Hq0 : 0 < n %/ d by rewrite (@divn_gt0 d n Hd0); exact: dvdn_leq Hn Hd.
rewrite dvdn_divRL // mulnC -dvdn_divRL //.
rewrite -{1}(expn1 2) pfactor_dvdn //.
by rewrite logn_div // subn_gt0.
Qed.

Section FiniteGroup.
Variable gT : finGroupType.
Variable z : gT.
Hypothesis abG : abelian [set: gT].
Hypothesis z_neq1 : z != 1%g.
Hypothesis z_square : (z ^+ 2)%g = 1%g.
Hypothesis roots_two : forall x : gT, (x ^+ 2)%g = 1%g -> x = 1%g \/ x = z.

Local Open Scope group_scope.
Let D := exponent [set: gT].

Lemma exponent_even : (2 %| D)%N.
Proof.
have oz : #[z] = 2%N := nt_prime_order (isT : prime 2) z_square z_neq1.
rewrite -oz; apply: dvdn_exponent; by rewrite inE.
Qed.

Lemma half_exponent_square (x : gT) : (x ^+ (D %/ 2)) ^+ 2 = 1.
Proof.
rewrite -expgM (divnK exponent_even).
apply: expg_exponent; by rewrite inE.
Qed.

Lemma half_exponent_is_one (x : gT) :
  (x ^+ (D %/ 2) == 1) = (logn 2 #[x] < logn 2 D)%N.
Proof.
rewrite -order_dvdn dvdn_half_logn ?exponent_gt0 ?exponent_even //.
apply: dvdn_exponent; by rewrite inE.
Qed.

Lemma half_exponent_witness : {g : gT | g ^+ (D %/ 2) = z}.
Proof.
have [g _ Dg] := exponent_witness (abelian_nil abG).
exists g.
have Hneq : g ^+ (D %/ 2) != 1 by rewrite half_exponent_is_one -Dg ltnn.
case: (roots_two (half_exponent_square g))=>[E|E]; last exact: E.
by move: Hneq; rewrite E eqxx.
Qed.

Lemma translate_order_valuation (g : gT) : g ^+ (D %/ 2) = z ->
  forall x : gT, logn 2 #[g * x] != logn 2 #[x].
Proof.
move=>Hg x; apply/negP=>/eqP E.
have Cgx : commute g x by apply: (centsP abG); rewrite inE.
have H : ((g * x) ^+ (D %/ 2) == 1) = (x ^+ (D %/ 2) == 1).
  by rewrite !half_exponent_is_one E.
rewrite expgMn // Hg in H.
case: (roots_two (half_exponent_square x))=>Hx; rewrite Hx in H.
- by move: H; rewrite mulg1 (negbTE z_neq1) eqxx.
- have Ezz : z * z = 1 by move: z_square; rewrite expgS expg1.
  by move: H; rewrite Ezz eqxx (negbTE z_neq1).
Qed.

Theorem order_valuation_fiber_half k :
  (2 * #|[set x : gT | logn 2 #[x] == k]| <= #|{:gT}|)%N.
Proof.
have [g Hg] := half_exponent_witness.
pose A := [set x : gT | logn 2 #[x] == k].
have Hsub : g *: A \subset ~: A.
  rewrite -lcosetE; apply/subsetP=>y /imsetP[x Hx ->].
  rewrite !inE; move: Hx; rewrite /A inE=>/eqP <-.
  exact: translate_order_valuation Hg x.
have Hcard := subset_leq_card Hsub.
rewrite card_lcoset in Hcard.
rewrite mul2n -addnn -[X in _ <= X](cardsC A) leq_add2l.
exact: Hcard.
Qed.

End FiniteGroup.
End ClassicalShorGroupCounting.
