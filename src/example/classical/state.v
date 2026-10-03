(* Classical: state. See README.md and PROOF_NOTES.md. *)
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
From quantum.example.classical Require Import language.
Module CQState.
(* Classical-quantum states: classical.pdf, Definition 3.1 and Lemma 3.3.
   Reuses the trace-norm summability foundation of CoqQ's cqwhile example. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section States.
Context {I : choiceType} {H : chsType}.

Definition state := {vdistr I -> 'End(H)}.
Definition mass (d : state) : hermitian.C := sum (fun i => \Tr (d i)).

Lemma support_countable (d : state) : countable (suppf d).
Proof. exact: summable_countn0. Qed.

Lemma mass_trace (d : state) : mass d = \Tr (sum d).
Proof. by rewrite /mass summable_linear_sum. Qed.

Lemma mass_norm (d : state) : mass d = `|sum d|.
Proof. by rewrite mass_trace psd_trfnorm // psdlfE vdistr_sum_ge0. Qed.

Lemma mass_l1 (d : state) : mass d = `|d : {summable I -> 'End(H)}|.
Proof.
rewrite summable_norm_sumE /mass; apply: eq_sum=>i.
by rewrite psd_trfnorm // psdlfE vdistr_ge0.
Qed.

Lemma mass_ge0 (d : state) : 0 <= mass d.
Proof. by rewrite mass_norm. Qed.

Lemma mass_le1 (d : state) : mass d <= 1.
Proof. by rewrite mass_norm; apply: vdistr_sum_le1. Qed.

Lemma component_density (d : state) i : d i \is denlf.
Proof.
apply/denlfP; split; first by rewrite psdlfE vdistr_ge0.
apply: (le_trans _ (mass_le1 d)).
by rewrite mass_trace; apply: lef_trlf; apply: vdistr_le_sum.
Qed.

(* Conversely, positivity and the paper's finite trace-sum bound suffice
   to build our summable representation. No support restriction is added. *)
Lemma trace_bounded_summable (f : I -> 'End(H)) :
  (forall i, 0%:VF ⊑ f i) ->
  (forall A, psum (fun i => \Tr (f i)) A <= 1) -> summable f.
Proof.
move=>positive bound; apply: psum_ubounded_summable; exists 1=>A.
rewrite /psum /normf; under eq_bigr do rewrite psd_trfnorm ?psdlfE ?positive //.
exact: bound.
Qed.

Lemma trace_bounded_sum (f : I -> 'End(H))
  (positive : forall i, 0%:VF ⊑ f i)
  (bound : forall A, psum (fun i => \Tr (f i)) A <= 1) :
  `|sum (Summable.build (trace_bounded_summable positive bound))| <= 1.
Proof.
apply: (le_trans (summable_sum_ler_norm _)).
apply: etlim_le; first exact: summable_norm_is_cvg.
move=>A; rewrite /psum /normf /=.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?positive //.
exact: bound.
Qed.

Definition of_trace_bound (f : I -> 'End(H))
  (positive : forall i, 0%:VF ⊑ f i)
  (bound : forall A, psum (fun i => \Tr (f i)) A <= 1) : state :=
  VDistr.build (f := Summable.build (trace_bounded_summable positive bound))
    positive (trace_bounded_sum positive bound).

Definition bottom : state := vdistr_zero.

Lemma bottomE i : bottom i = 0. Proof. by []. Qed.

Lemma bottom_least (d : state) : bottom ⊑ d.
Proof. by apply/levdP=>i; rewrite bottomE; apply: vdistr_ge0. Qed.

Lemma mass_bottom : mass bottom = 0.
Proof. by rewrite mass_trace /bottom /= summable_sum0 linear0. Qed.

Lemma point_positive (i : I) (rho : 'FD(H)) j :
  0%:VF ⊑ sunit_def i (rho : 'End(H)) j.
Proof. rewrite /sunit_def; case: eqP=>_ //; exact: denf_ge0. Qed.

Lemma point_bound (i : I) (rho : 'FD(H)) :
  `|sum (sunit_def i (rho : 'End(H)))| <= 1.
Proof. by rewrite sunit_sum psd_trfnorm ?is_psdlf //; apply: denf_trlf. Qed.

Definition point (i : I) (rho : 'FD(H)) : state :=
  VDistr.build (point_positive i rho) (point_bound i rho).

Lemma pointE (i j : I) (rho : 'FD(H)) :
  point i rho j = if j == i then rho : 'End(H) else 0.
Proof. by []. Qed.

Lemma point_mass (i : I) (rho : 'FD(H)) : mass (point i rho) = \Tr rho.
Proof. by rewrite mass_trace /point /= sunit_sum. Qed.

Definition chain_sup (f : nat -> state) : state :=
  vdlim (FF := eventually_filter) f.

Lemma chain_converges (f : nat -> state) : nondecreasing_seq f ->
  cvgn (f : nat -> {summable I -> 'End(H)}).
Proof. apply: (vdnondecreasing_is_cvgn (@trfnorm_add H)). Qed.

Lemma chain_sup_upper (f : nat -> state) : nondecreasing_seq f ->
  forall n, f n ⊑ chain_sup f.
Proof. exact: (vdnondecreasing_cvg_le (@trfnorm_add H)). Qed.

Lemma chain_sup_least (f : nat -> state) (d : state) :
  nondecreasing_seq f -> (forall n, f n ⊑ d) -> chain_sup f ⊑ d.
Proof.
move=>inc bound; rewrite levdEsub /chain_sup vdlimE.
  exact: chain_converges inc.
apply: lim_les_nearF; first exact: chain_converges.
by apply: nearW=>n; rewrite -levdEsub; apply: bound.
Qed.

Lemma chain_sup_pointwise (f : nat -> state) : nondecreasing_seq f ->
  forall i, chain_sup f i = limn (fun n => f n i).
Proof. by move=>inc i; apply: vdlimEE; apply: chain_converges. Qed.

End States.
End CQState.


Module CQStateDecreasing.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
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

End States.

End CQStateDecreasing.


Module CQStateMixture.
(* Summable mixtures of cq-states for the two papers' distribution semantics. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

(* Countable mixtures of cq-states, used for probabilistic configurations.
   See PROOF_NOTES.md for the summability argument. *)
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
