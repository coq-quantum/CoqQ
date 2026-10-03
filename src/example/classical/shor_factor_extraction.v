(* Equation (20) for the actual arithmetic order-success event.
   See SHOR-SAMPLE-EVENT-NOTES.md; independent of the OrderFinding program. *)
From mathcomp Require Import all_ssreflect.
From quantum.example.classical Require Import shor_arithmetic shor_sample_event.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module ClassicalShorFactorExtraction.
Import ClassicalShorArithmetic ClassicalShorSampleEvent.

Section Modulus.
Variable N : nat.
Hypothesis HN : 1 < N.

Theorem natural_success_factor a : coprime N a -> natural_success N a ->
  nontrivial_factor N (gcdn (a ^ (natural_order N a %/ 2) - 1) N).
Proof.
move=>Ha /andP[Heven Hneg].
have Hr : 0 < natural_order N a := natural_order_positive N a.
have Dr : 2 %| natural_order N a by rewrite dvdn2.
have E : (natural_order N a %/ 2) * 2 = natural_order N a := divnK Dr.
have Hhalf0 : 0 < natural_order N a %/ 2.
  have Hp : 0 < (natural_order N a %/ 2) * 2 by rewrite E.
  by move: Hp; rewrite muln_gt0=>/andP[].
have Hhalf : natural_order N a %/ 2 < natural_order N a.
  exact: ltn_Pdiv (isT : 1 < 2) Hr.
have Hrange : 0 < natural_order N a %/ 2 < natural_order N a.
  by rewrite Hhalf0 Hhalf.
have Hmin := natural_order_minimal HN Ha Hrange.
have Hneq1 : a ^ (natural_order N a %/ 2) %% N != 1.
  by move: Hmin; rewrite (modn_small HN).
have Hpowercop : coprime N (a ^ (natural_order N a %/ 2)).
  exact: coprimeXr Ha.
have Hnonzero : a ^ (natural_order N a %/ 2) %% N != 0.
  apply/negP=>/eqP Hz.
  move: Hpowercop; rewrite -coprime_modr Hz /coprime gcdn0.
  by rewrite eq_sym (ltn_eqF HN).
have Hgreater : 1 < a ^ (natural_order N a %/ 2) %% N.
  by rewrite ltn_neqAle eq_sym Hneq1 lt0n Hnonzero.
have Hpred : N.-1 < N by rewrite ltn_predL; exact: ltnW HN.
have Hneqpred : a ^ (natural_order N a %/ 2) %% N != N.-1.
  by move: Hneg; rewrite (modn_small Hpred).
have Hbound : a ^ (natural_order N a %/ 2) %% N <= N.-1.
  by rewrite -ltnS (prednK (ltnW HN)); exact: ltn_pmod (ltnW HN).
have Hsmall : a ^ (natural_order N a %/ 2) %% N + 1 < N.
  by rewrite addn1 -ltn_predRL ltn_neqAle Hneqpred Hbound.
apply: nontrivial_sqrt_factor_mod HN Hgreater Hsmall _.
rewrite -expnM E.
exact: (@natural_order_power N HN a Ha).
Qed.

End Modulus.
End ClassicalShorFactorExtraction.
