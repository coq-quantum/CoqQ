(* Order separation and continuous expectations. See EXPECTATION-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import state assertion expectation.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQStateDecreasing.
Section States.
Context {I : choiceType} {H : chsType}.
Local Notation state := (@CQState.state I H).

Lemma decreasing_converges (f : nat -> state) : nonincreasing_seq f ->
  cvgn (f : nat -> {summable I -> 'End(H)}).
Proof.
move=>Hd.
pose g n := - (f n : {summable I -> 'End(H)}).
have Hg : nondecreasing_seq g.
  by move=>i j ij; rewrite /g levN2 -levdEsub; exact: Hd ij.
have Hb : ubounded_by (0 : {summable I -> 'End(H)}) g.
  move=>n; apply/lesP=>i; rewrite /g !summableE /= -[0%:VF]oppr0 levN2; exact: vdistr_ge0.
have C := snondecreasing_is_cvgn (@trfnorm_add H) Hg Hb.
have Ef : (f : nat -> {summable I -> 'End(H)}) = (fun n => -g n).
  by apply/funext=>n; rewrite /g opprK.
by rewrite Ef; apply: is_cvgN.
Qed.

Definition chain_inf (f : nat -> state) : state := vdlim (FF := eventually_filter) f.

Lemma chain_inf_cvg (f : nat -> state) : nonincreasing_seq f ->
  (f n : {summable I -> 'End(H)}) @[n --> \oo] -->
    (chain_inf f : {summable I -> 'End(H)}).
Proof.
move=>Hd; rewrite /chain_inf vdlimE; exact: decreasing_converges.
Qed.

Lemma chain_inf_lower (f : nat -> state) : nonincreasing_seq f ->
  forall n, chain_inf f ⊑ f n.
Proof.
move=>Hd n; rewrite levdEsub /chain_inf vdlimE; first exact: decreasing_converges.
apply: lim_les_nearF; first exact: decreasing_converges.
exists n=>// k /= nk; rewrite -levdEsub; exact: Hd nk.
Qed.

Lemma chain_inf_greatest (f : nat -> state) d : nonincreasing_seq f ->
  (forall n, d ⊑ f n) -> d ⊑ chain_inf f.
Proof.
move=>Hd Hb; rewrite levdEsub /chain_inf vdlimE; first exact: decreasing_converges.
apply: lim_ges_nearF; first exact: decreasing_converges.
by apply: nearW=>n; rewrite -levdEsub; exact: Hb.
Qed.

Lemma chain_inf_pointwise (f : nat -> state) : nonincreasing_seq f ->
  forall i, chain_inf f i = limn (fun n => f n i).
Proof. by move=>Hd i; apply: vdlimEE; apply: decreasing_converges. Qed.

Theorem expect_chain_inf (P : I -> 'FO(H)) (f : nat -> state) : nonincreasing_seq f ->
  CQAssertion.expect P (f n) @[n --> \oo] --> CQAssertion.expect P (chain_inf f).
Proof. move=>Hd; apply: CQExpectation.expect_cvg; exact: chain_inf_cvg. Qed.
End States.
End CQStateDecreasing.
