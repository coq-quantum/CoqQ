(* Total successful-state value, Bellman equation, and leastness.
   See PROOF_GAPS.md for the monotone mixture argument. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra notation mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.distributive Require Import language operational distribution weighted scheduler local_actions results residual sequentialization observables diamond global_actions scheduler_semantics confluence scheduler_results.
From quantum.example.classical Require Import state mixture.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedGlobalValue.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted
  DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics
  DistributedSchedulerResults.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Lemma weighted_mono X (H : chsType) (mu : family X) (f g : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  (forall x, `|g x| <= 1) -> (forall x, f x ⊑ g x) ->
  weighted_sum mu f ⊑ weighted_sum mu g.
Proof.
move=>Hm Hf Hg Hfg; apply: lev_lim.
- apply: norm_bounded_cvg; exact: weighted_summable Hm Hf.
- apply: norm_bounded_cvg; exact: weighted_summable Hm Hg.
- move=>A; apply: lev_sum=>i _; apply: lev_wpscale2l; first exact: (proj1 (proj2 Hm)).
  exact: Hfg.
Qed.

Lemma weighted_mono_on X (H : chsType) (mu : family X) (f g : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  (forall x, `|g x| <= 1) ->
  (forall i, 0 < branch_weight mu i -> f (branch_value mu i) ⊑ g (branch_value mu i)) ->
  weighted_sum mu f ⊑ weighted_sum mu g.
Proof.
move=>Hm Hf Hg Hfg; apply: lev_lim.
- apply: norm_bounded_cvg; exact: weighted_summable Hm Hf.
- apply: norm_bounded_cvg; exact: weighted_summable Hm Hg.
- move=>A; apply: lev_sum=>i _; case P: (0 < branch_weight mu (val i)).
  + apply: lev_pscale2lP; first exact: P.
    exact: Hfg P.
  + have Z : branch_weight mu (val i) = 0.
      by move: (proj1 (proj2 Hm) (val i)); rewrite le_eqVlt P orbF eq_sym=>/eqP.
    by rewrite Z !scale0r.
Qed.

Lemma weighted_monotone_cvg X (H : chsType) (mu : family X)
    (f : nat -> X -> 'End(H)) (g : X -> 'End(H)) :
  probability_family mu -> (forall n x, `|f n x| <= 1) ->
  (forall x, nondecreasing_seq (fun n => f n x)) ->
  (forall x, `|g x| <= 1) -> (forall x, f n x @[n --> \oo] --> g x) ->
  weighted_sum mu (f n) @[n --> \oo] --> weighted_sum mu g.
Proof.
move=>Hm Hf mono Hg Cg.
pose a n := Summable.build (weighted_summable Hm (Hf n)).
have ia : nondecreasing_seq a.
  move=>j k jk; apply/lesP=>i.
  apply: lev_wpscale2l; first exact: (proj1 (proj2 Hm)).
  exact: mono jk.
have ab n : `|a n| <= 1.
  rewrite summable_norm_sumE.
  apply: etlim_le; first exact: summable_norm_is_cvg.
  move=>A; exact: weighted_partial_bound Hm (Hf n).
have Ca := snondecreasing_norm_is_cvgn (@trfnorm_add H) ia ab.
have E : limn a = Summable.build (weighted_summable Hm Hg).
  apply/summableP=>i; rewrite -summableE_lim //.
  have C : a n i @[n --> \oo] --> branch_weight mu i *: g (branch_value mu i).
    apply: cvgZr; exact: Cg.
  exact: (cvg_lim (@norm_hausdorff _ _) C).
have Csum := summable_sum_cvg Ca.
rewrite E in Csum; exact: Csum.
Qed.

Section Global.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Local Notation cfg := (global_configuration n).
Local Notation next := (@policy P rho0).
Local Notation step := (@projected_step P rho0).

Definition next_probability c := @projected_probability P rho0 c (next c) (@policy_step P rho0 c).
Fixpoint approximant k (c : cfg) : state :=
  if k is j.+1 then CQStateMixture.mix (probability_distribution (next_probability c))
    (fun i => approximant j (branch_value (next c) i))
  else successful_component c.

Lemma approximantS k c m : approximant k.+1 c m =
  weighted_sum (next c) (fun d => approximant k d m).
Proof.
change (CQStateMixture.mix (probability_distribution (next_probability c))
  (fun i => approximant k (branch_value (next c) i)) m =
  weighted_sum (next c) (fun d => approximant k d m)).
rewrite CQStateMixture.mixE /weighted_sum.
by apply: eq_sum=>i; rewrite probability_distributionE.
Qed.
Lemma approximant_horizon k c m : approximant k c m =
  ProbabilisticDiamond.horizon next (fun d => successful_component d m) k c.
Proof.
elim: k c=>[|k IH] c //; rewrite approximantS /=.
by apply: eq_sum=>i; rewrite IH.
Qed.
Lemma approximant_bound k c m : `|approximant k c m| <= 1.
Proof.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
apply: denlf_trlf; exact: CQState.component_density.
Qed.

Lemma projected_progress c mu m : step c mu ->
  successful_component c m ⊑ weighted_sum mu (fun d => successful_component d m).
Proof.
case=>[c' mu' [Hr Ho] Hs|c' Ht|c' Hbad]; try by rewrite weighted_certain.
rewrite weighted_collapse.
exact: (@successful_component_step n p c' mu' m (or_intror Hs) (global_step_probability Hs Hr)).
Qed.

Lemma approximant_increasing c : nondecreasing_seq (fun k => approximant k c).
Proof.
have Step k : forall c, approximant k c ⊑ approximant k.+1 c.
  elim: k=>[|k IH] d; apply/levdP=>m.
- rewrite approximantS; exact: projected_progress (@policy_step P rho0 d).
- rewrite !approximantS; apply: weighted_mono (next_probability d)
    (fun d => approximant_bound k d m) (fun d => approximant_bound k.+1 d m) _ =>d0.
  by move: (IH d0)=>/levdP/(_ m).
apply/nondecreasing_seqP=>k; exact: Step k c.
Qed.

Lemma approximant_point_mono c m : nondecreasing_seq (fun k => approximant k c m).
Proof. by move=>j k jk; move: (@approximant_increasing c j k jk)=>/levdP/(_ m). Qed.

Definition value c : state := CQState.chain_sup (fun k => approximant k c).
Lemma value_cvg c m : approximant k c m @[k --> \oo] --> value c m.
Proof.
rewrite /value (@CQState.chain_sup_pointwise cmem Hq _ (approximant_increasing c) m).
exact: (@summableE_is_cvg _ _ _ _ _ _ _ _
  (@CQState.chain_converges cmem Hq _ (approximant_increasing c)) m).
Qed.
Lemma value_bound c m : `|value c m| <= 1.
Proof.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
apply: denlf_trlf; exact: CQState.component_density.
Qed.

Lemma approximant_advance c mu k m : step c mu ->
  weighted_sum mu (fun d => approximant k d m) = approximant k.+1 c m.
Proof.
move=>Hs; rewrite approximant_horizon.
have E : (fun d => approximant k d m) =
    ProbabilisticDiamond.horizon next (fun d => successful_component d m) k.
  by apply/funext=>d; rewrite approximant_horizon.
rewrite E.
exact (@ProbabilisticDiamond.horizon_step cfg Hq step next
  (fun d => successful_component d m) (@projected_probability P rho0)
  (@policy_step P rho0) (fun d => successful_component_bound d m)
  (fun c mu nu => @projected_one_step P rho0 c mu nu m)
  (@DistributedConfluence.projected_two_step_diamond P rho0) k c mu Hs).
Qed.

Theorem value_bellman c mu m : step c mu ->
  value c m = weighted_sum mu (fun d => value d m).
Proof.
move=>Hs.
have C := @weighted_monotone_cvg cfg Hq mu
  (fun k d => approximant k d m) (fun d => value d m)
  (@projected_probability P rho0 c mu Hs)
  (fun k d => approximant_bound k d m)
  (fun d => @approximant_point_mono d m)
  (fun d => value_bound d m) (fun d => @value_cvg d m).
have E : (fun k => weighted_sum mu (fun d => approximant k d m)) =
    (fun k => approximant k.+1 c m).
  by apply/funext=>k; rewrite (@approximant_advance c mu k m Hs).
rewrite E in C.
have C2 : approximant k.+1 c m @[k --> \oo] --> value c m.
  by rewrite (@cvg_shiftS _ (fun k => approximant k c m) (nbhs (value c m))); exact: value_cvg.
exact: (eq_trans (esym (cvg_lim (@norm_hausdorff _ _) C2))
  (cvg_lim (@norm_hausdorff _ _) C)).
Qed.

Theorem value_least m (F : cfg -> 'End(Hq)) :
  (forall c, `|F c| <= 1) ->
  (forall c, successful_component c m ⊑ F c) ->
  (forall c mu, step c mu -> weighted_sum mu F ⊑ F c) ->
  forall c, value c m ⊑ F c.
Proof.
move=>Hf Hzero Hstep c.
have B k : forall c, approximant k c m ⊑ F c.
  elim: k=>[|k IH] d; first exact: Hzero.
  rewrite approximantS; apply: (le_trans _ (Hstep d (next d) (@policy_step P rho0 d))).
  exact: weighted_mono (next_probability d) (fun e => approximant_bound k e m) Hf IH.
have C := @value_cvg c m.
have L := limn_lev (cvgP _ C) (fun k => B k c).
by rewrite (cvg_lim (@norm_hausdorff _ _) C) in L.
Qed.

Theorem value_least_invariant m (I : cfg -> Prop) (F : cfg -> 'End(Hq)) :
  (forall c, `|F c| <= 1) ->
  (forall c, I c -> successful_component c m ⊑ F c) ->
  (forall c, I c -> exists mu, step c mu /\
    (forall i, 0 < branch_weight mu i -> I (branch_value mu i)) /\
    weighted_sum mu F ⊑ F c) ->
  forall c, I c -> value c m ⊑ F c.
Proof.
move=>Hf Hzero Hnext.
have B k : forall c, I c -> approximant k c m ⊑ F c.
  elim: k=>[|k IH] d Id; first exact: Hzero.
  have [mu [Hs [Hi Hb]]] := Hnext d Id.
  rewrite -(@approximant_advance d mu k m Hs).
  apply: (le_trans _ Hb).
  apply: weighted_mono_on (@projected_probability P rho0 d mu Hs)
    (fun e => approximant_bound k e m) Hf _ =>i Pi.
  exact: IH (Hi i Pi).
move=>c Ic; have C := @value_cvg c m.
have L := limn_lev (cvgP _ C) (fun k => B k c Ic).
by rewrite (cvg_lim (@norm_hausdorff _ _) C) in L.
Qed.

Lemma approximant_terminal c : terminal p c -> forall k, approximant k c = successful_component c.
Proof.
move=>Ht; elim=>[|k IH] //; apply/vdistrP=>m.
rewrite -(@approximant_advance c (certain c) k m (@ProjectedTerminal P rho0 c Ht)) weighted_certain IH.
by [].
Qed.
Lemma value_terminal c : terminal p c -> value c = successful_component c.
Proof.
move=>Ht; apply/vdistrP=>m; have C := @value_cvg c m.
have E : (fun k => approximant k c m) = (fun _ : nat => successful_component c m).
  by apply/funext=>k; rewrite (approximant_terminal Ht k).
by rewrite -(cvg_lim (@norm_hausdorff _ _) C) E lim_cst.
Qed.
Lemma value_collapse c : value (@collapse P rho0 c) = value c.
Proof.
case: c=>[[pc [s|]] rho].
- by [].
- change (value (@failure P rho0) = value (global_config pc None rho)).
  rewrite !value_terminal; try exact: failure_terminal.
  by [].
Qed.

Theorem value_denote (c : cfg) (Hc : c.2 \is den1lf) : configuration_owned p c ->
  value c = denote_configuration P Hc.
Proof.
move=>Ho; rewrite -(@value_collapse c) /denote_configuration /result_state /value.
congr CQState.chain_sup; apply/funext=>k; apply/vdistrP=>m.
rewrite approximant_horizon.
symmetry; exact: (@stage_horizon P rho0 c (canonical_computation p Hc) Ho k m).
Qed.

End Global.
End DistributedGlobalValue.
