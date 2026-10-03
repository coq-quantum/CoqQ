(* The literal printed postprocessor cannot return a denominator above two.
   See C7 and its finite-list proof in PROOF_GAPS.md. *)
From mathcomp Require Import all_ssreflect.
From quantum.example.classical Require Import shor_arithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalPostprocessCounterexample.
Import ClassicalShorArithmetic.

Lemma fold_min_seed seed ds : foldr minn seed ds <= seed.
Proof.
elim: ds=>[|d ds IH] //=; exact: leq_trans (geq_minr _ _) IH.
Qed.

Lemma fold_min_member seed ds d : d \in ds -> foldr minn seed ds <= d.
Proof.
elim: ds=>[|a ds IH] //=; rewrite inE=>/orP[/eqP->|Hd].
- exact: geq_minl.
- exact: leq_trans (geq_minr _ _) (IH Hd).
Qed.

Lemma selector_candidate_bound a b pd d :
  pd \in convergents b.+1 a b -> approximation_test a b pd ->
  printed_postprocess a b = Some d -> d <= pd.2.
Proof.
move=>Hmem Htest.
have H : pd.2 \in map snd (filter (approximation_test a b) (convergents b.+1 a b)).
  apply/mapP; exists pd=>//; by rewrite mem_filter Htest Hmem.
rewrite /printed_postprocess.
case: (map snd _) H=>[|e es] //; rewrite inE=>/orP[/eqP->|He] [<-].
- exact: fold_min_seed.
- exact: fold_min_member He.
Qed.

Lemma convergents_first a b : 0 < b -> (a %/ b, 1) \in convergents b.+1 a b.
Proof. by move=>Hb; rewrite /= (gtn_eqF Hb) inE eqxx. Qed.

Lemma convergents_second a b : 0 < a -> a < b ->
  (1, b %/ a) \in convergents b.+1 a b.
Proof.
move=>Ha Hab; have Hb : 0 < b := ltn_trans Ha Hab.
case: b Hb Hab=>[//|b] Hb Hab.
rewrite /= (divn_small Hab) (modn_small Hab) (gtn_eqF Ha) /=.
by rewrite !inE eqxx orbT.
Qed.

Lemma zero_convergent_test a b : 2 * a < b -> approximation_test a b (0,1).
Proof.
by move=>H; rewrite /approximation_test /= !muln1 mul0n sub0n subn0 add0n.
Qed.

Lemma one_convergent_test a b : a < b -> b < 2 * a ->
  approximation_test a b (1,1).
Proof.
move=>Hab Hba.
have Hsub : a - b = 0 by apply/eqP; rewrite subn_eq0; exact: ltnW Hab.
rewrite /approximation_test /= !muln1 mul1n Hsub addn0.
have Hmul : 2 * a <= 2 * b by rewrite leq_mul2l (ltnW Hab) orbT.
rewrite mulnBr ltn_subLR //.
by rewrite mul2n -addnn addnC ltn_add2l.
Qed.

Lemma half_convergent_test a : 0 < a -> approximation_test a (2*a) (1,2).
Proof. by move=>Ha; rewrite /approximation_test /= mul1n [a * 2]mulnC !subnn addn0 muln0 muln_gt0 Ha. Qed.

Theorem printed_denominator_at_most_two a b d : a < b ->
  printed_postprocess a b = Some d -> d <= 2.
Proof.
move=>Hab Hd; case: (ltngtP (2*a) b)=>[Hlow|Hhigh|Heq].
- have Hb : 0 < b := leq_ltn_trans (leq0n a) Hab.
  have Hfirst := @convergents_first a b Hb.
  rewrite (divn_small Hab) in Hfirst.
  exact: leq_trans (selector_candidate_bound Hfirst (zero_convergent_test Hlow) Hd) (isT : 1 <= 2).
- have Ha : 0 < a.
    case Ea: a=>[|a'] //; by move: Hhigh; rewrite Ea muln0 ltn0.
  have Hdiv : b %/ a = 1.
    apply/eqP; rewrite eqn_leq -ltnS ltn_divLR // leq_divRL // mul1n.
    by rewrite Hhigh (ltnW Hab).
  have Hsecond := convergents_second Ha Hab.
  rewrite Hdiv in Hsecond.
  exact: leq_trans (selector_candidate_bound Hsecond (one_convergent_test Hab Hhigh) Hd) (isT : 1 <= 2).
- have Ha : 0 < a.
    case Ea: a=>[|a'] //; by move: Hab; rewrite -Heq Ea muln0 ltnn.
  have Hsecond := convergents_second Ha Hab.
  have Hdiv : b %/ a = 2 by rewrite -Heq mulnC mulKn.
  rewrite Hdiv in Hsecond.
  apply: (selector_candidate_bound Hsecond _ Hd).
  rewrite -Heq; exact: half_convergent_test Ha.
Qed.

Corollary printed_never_four a b : a < b -> printed_postprocess a b != Some 4.
Proof.
move=>Hab; apply/negP=>/eqP Hd.
by have := printed_denominator_at_most_two Hab Hd.
Qed.

End ClassicalPostprocessCounterexample.
