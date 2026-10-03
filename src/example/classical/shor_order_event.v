(* Failure means equal component order valuations; see SHOR-ORDER-EVENT-NOTES.md. *)
From mathcomp Require Import all_ssreflect all_algebra fingroup morphism
  quotient cyclic nilpotent abelian.
From quantum.example.classical Require Import shor_group_counting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorOrderEvent.
Import ClassicalShorGroupCounting.

Lemma logn2_eq0 n : 0 < n -> (logn 2 n == 0) = odd n.
Proof. by move=>Hn; rewrite eqn0Ngt logn_gt0 mem_primes Hn /= dvdn2 negbK. Qed.

Section Components.
Variables (I : finType) (G : finGroupType) (H : I -> finGroupType).
Variable i0 : I.
Variable red : forall i, {morphism [set: G] >-> H i}.
Hypothesis red_joint_injective :
  forall x y : G, (forall i, red i x = red i y) -> x = y.
Variable zi : forall i, H i.
Hypothesis zi_neq1 : forall i, zi i != 1%g.
Hypothesis roots_two : forall i (y : H i),
  (y ^+ 2)%g = 1%g -> y = 1%g \/ y = zi i.
Variable z : G.
Hypothesis red_z : forall i, red i z = zi i.

Local Open Scope group_scope.

Lemma component_order_dvd i (x : G) : (#[red i x] %| #[x])%N.
Proof. by rewrite order_dvdn -morphX ?inE // expg_order morph1. Qed.

Lemma component_valuation_le i (x : G) :
  (logn 2 #[red i x] <= logn 2 #[x])%N.
Proof. exact: dvdn_leq_log (order_gt0 x) (component_order_dvd i x). Qed.

Lemma odd_component_valuation (x : G) : odd #[x] ->
  forall i, logn 2 #[red i x] = 0%N.
Proof.
move=>Hx i; apply/eqP; rewrite logn2_eq0 ?order_gt0 //.
exact: dvdn_odd (component_order_dvd i x) Hx.
Qed.

Lemma half_component_square i (x : G) : ~~ odd #[x] ->
  (red i (x ^+ (#[x] %/ 2))) ^+ 2 = 1.
Proof.
move=>Hx; have H2 : (2 %| #[x])%N by rewrite dvdn2.
rewrite -morphX ?inE // -expgM (divnK H2) expg_order morph1.
by [].
Qed.

Lemma half_component_is_one i (x : G) : ~~ odd #[x] ->
  (red i (x ^+ (#[x] %/ 2)) == 1) =
    (logn 2 #[red i x] < logn 2 #[x])%N.
Proof.
move=>Hx; have H2 : (2 %| #[x])%N by rewrite dvdn2.
rewrite morphX ?inE // -order_dvdn.
exact: dvdn_half_logn (order_gt0 x) (component_order_dvd i x) H2.
Qed.

Lemma half_component_is_involution i (x : G) : ~~ odd #[x] ->
  (red i (x ^+ (#[x] %/ 2)) == zi i) =
    (logn 2 #[red i x] == logn 2 #[x]).
Proof.
move=>Hx.
have Hle := component_valuation_le i x.
have Hhalf := half_component_is_one i Hx.
case: (roots_two (half_component_square i Hx))=>E.
- have Hlt : (logn 2 #[red i x] < logn 2 #[x])%N.
    by move: Hhalf; rewrite E eqxx=> <-.
  by rewrite E eq_sym (negbTE (zi_neq1 i)) (ltn_eqF Hlt).
- have Hlt : (logn 2 #[red i x] < logn 2 #[x])%N = false.
    by move: Hhalf; rewrite E (negbTE (zi_neq1 i))=> <-.
  have Heq : logn 2 #[red i x] = logn 2 #[x].
    apply/eqP; by move: Hle; rewrite leq_eqVlt Hlt orbF.
  by rewrite E Heq !eqxx.
Qed.

Lemma component_valuation_reaches (x : G) : ~~ odd #[x] ->
  exists i, logn 2 #[red i x] = logn 2 #[x].
Proof.
move=>Hx.
have H2 : (2 %| #[x])%N by rewrite dvdn2.
have Hex : [exists i, logn 2 #[red i x] == logn 2 #[x]].
  case: (boolP [exists i, logn 2 #[red i x] == logn 2 #[x]])
    =>[//|/existsPn Hnone].
  have Ehalf : x ^+ (#[x] %/ 2) = 1.
    apply: red_joint_injective=>i; rewrite morph1; apply/eqP.
    rewrite half_component_is_one // ltn_neqAle Hnone andTb.
    exact: component_valuation_le.
  have Hr : (#[x] %| #[x] %/ 2)%N by rewrite order_dvdn Ehalf eqxx.
  by move: Hr; rewrite dvdn_half_logn ?order_gt0 ?dvdnn // ltnn.
case/existsP: Hex=>i /eqP Hi; by exists i.
Qed.

Theorem failure_iff_equal_valuations (x : G) :
  odd #[x] || (x ^+ (#[x] %/ 2) == z) =
    [forall i, logn 2 #[red i x] == logn 2 #[red i0 x]].
Proof.
case Hodd: (odd #[x]).
- rewrite /=; apply/esym/forallP=>i.
  by rewrite !odd_component_valuation.
- have Heven : ~~ odd #[x] by rewrite Hodd.
  rewrite /=; apply/idP/idP.
  + move=>/eqP E; apply/forallP=>i.
    have Ei : logn 2 #[red i x] = logn 2 #[x].
      apply/eqP; by rewrite -half_component_is_involution // E red_z eqxx.
    have E0 : logn 2 #[red i0 x] = logn 2 #[x].
      apply/eqP; by rewrite -half_component_is_involution // E red_z eqxx.
    by rewrite Ei E0.
  + move=>/forallP Hall; apply/eqP.
    have [j Hj] := component_valuation_reaches Heven.
    have E0 : logn 2 #[red i0 x] = logn 2 #[x].
      by move/eqP: (Hall j); rewrite Hj=> ->.
    apply: red_joint_injective=>i; rewrite red_z; apply/eqP.
    by rewrite half_component_is_involution // (eqP (Hall i)) E0 eqxx.
Qed.

End Components.
End ClassicalShorOrderEvent.
