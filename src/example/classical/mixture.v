(* Summable mixtures of cq-states for the two papers' distribution semantics. *)
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
From quantum.example.classical Require Import state.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

(* Countable mixtures of cq-states, used for probabilistic configurations.
   See STATE_NOTES.md for the summability argument. *)
Module CQStateMixture.
Section Mixtures.
Context {I J : choiceType} {H : chsType}.
Variable (w : Distr I) (d : I -> @CQState.state J H).

Definition term i : {summable J -> 'End(H)} :=
  w i *: (d i : {summable J -> 'End(H)}).

Lemma term_norm_bound i : `|term i| <= w i.
Proof.
rewrite /term normrZ ger0_norm ?ge0_mu //.
rewrite -CQState.mass_l1 -[X in _ <= X]mulr1.
apply: ler_wpM2l; first exact: ge0_mu.
exact: CQState.mass_le1.
Qed.

Lemma terms_summable : summable term.
Proof.
apply: psum_ubounded_summable; exists 1=>A.
apply: (le_trans (y := psum (fun i => w i) A)); last exact: psum_le1_mu.
by apply: ler_sum=>i _; apply: term_norm_bound.
Qed.

Definition terms := Summable.build terms_summable.
Definition mix_summable : {summable J -> 'End(H)} := sum terms.

Lemma mix_l1_bound : `|mix_summable| <= 1.
Proof.
apply: (le_trans (summable_sum_ler_norm terms)).
apply: etlim_le; first exact: summable_norm_is_cvg.
move=>A; apply: (le_trans (y := psum (fun i => w i) A)); last exact: psum_le1_mu.
by apply: ler_sum=>i _; apply: term_norm_bound.
Qed.

Lemma mix_positive j : 0%:VF ⊑ mix_summable j.
Proof.
rewrite /mix_summable sum_summableE; first exact: summable_cvg.
apply: lim_gev_near.
  apply: norm_bounded_cvg; apply: psum_ubounded_summable; exists 1=>A.
  apply: (le_trans (y := psum (fun i => `|term i|) A)).
    apply: ler_sum=>i _.
    by move: (psum_norm_ler_norm (term (val i)) [fset j]); rewrite psum1.
  apply: (le_trans (y := psum (fun i => w i) A)); last exact: psum_le1_mu.
  by apply: ler_sum=>i _; apply: term_norm_bound.
near=>A; apply: sumv_ge0=>i _.
by rewrite /terms /= /term scalev_ge0 ?vdistr_ge0 ?ge0_mu.
Unshelve. end_near.
Qed.

Lemma mix_sum_bound : `|sum mix_summable| <= 1.
Proof.
apply: (le_trans (summable_sum_ler_norm mix_summable)).
by rewrite -summable_norm_sumE; apply: mix_l1_bound.
Qed.

Definition mix : @CQState.state J H :=
  VDistr.build (f := mix_summable) mix_positive mix_sum_bound.

Lemma mixE j : mix j = sum (fun i => w i *: d i j).
Proof.
change (mix_summable j = sum (fun i => w i *: d i j)).
rewrite /mix_summable sum_summableE; first exact: summable_cvg.
by [].
Qed.
End Mixtures.
End CQStateMixture.
