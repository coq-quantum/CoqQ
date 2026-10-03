(* Distributive: semantics. See README.md and PROOF_NOTES.md. *)
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
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From Stdlib Require Import String.
From quantum Require Import mcextra notation mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.example.distributive Require Import language operational confluence.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module DistributedSchedulerResults.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Section ComputationProjection.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Variable c : global_configuration n.
Variable pi : computation p c.

Definition projected_stage k := fmap (@collapse P rho0) (computation_stage pi k).

Lemma projected_initial :
  same_distribution (projected_stage 0%N) (certain (@collapse P rho0 c)).
Proof. exact: (@same_distribution_fmap _ _ (@collapse P rho0) _ _ (computation_initial pi)). Qed.

Lemma projected_stage_probability k : probability_family (projected_stage k).
Proof. exact: computation_probability. Qed.

Lemma projected_stage_evolution : configuration_owned p c -> forall k,
  ProbabilisticDiamond.evolution (@projected_step P rho0) (projected_stage k) (projected_stage k.+1).
Proof.
move=>Hown k; apply: projected_evolution; first exact: computation_probability.
- move=>i Hi; split.
  + exact: (@computation_normalized n p c pi k i Hi).
  + exact: (@computation_owned n p c pi (@processes_wf P) Hown k i Hi).
- exact: computation_advances.
Qed.

Lemma projected_stage_observe k m :
  weighted_sum (projected_stage k) (fun d => successful_component d m) = stage_state pi k m.
Proof.
rewrite /projected_stage weighted_collapse.
by rewrite /stage_state successful_state_weighted.
Qed.

End ComputationProjection.
Section Independence.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).

Theorem stage_horizon c (pi : computation p c) : configuration_owned p c -> forall k m,
  stage_state pi k m = ProbabilisticDiamond.horizon (@policy P rho0)
    (fun d => successful_component d m) k (@collapse P rho0 c).
Proof.
move=>Hown k m; rewrite -(@projected_stage_observe P rho0 c pi k m).
exact (@ProbabilisticDiamond.finite_horizon_unique (global_configuration n) Hq
  (@projected_step P rho0) (@policy P rho0) (fun d => successful_component d m)
  (@projected_probability P rho0) (@policy_step P rho0)
  (fun d => successful_component_bound d m)
  (fun c mu nu => @projected_one_step P rho0 c mu nu m)
  (@DistributedConfluence.projected_two_step_diamond P rho0)
  (@projected_stage P rho0 c pi) (@collapse P rho0 c)
  (@projected_initial P rho0 c pi) (@projected_stage_probability P rho0 c pi)
  (@projected_stage_evolution P rho0 c pi Hown) k).
Qed.

Theorem stage_scheduler_independent c (pi sigma : computation p c) :
  configuration_owned p c -> forall k, stage_state pi k = stage_state sigma k.
Proof.
move=>Hown k; apply/vdistrP=>m.
by rewrite (@stage_horizon c pi Hown k m) (@stage_horizon c sigma Hown k m).
Qed.

Theorem result_scheduler_independent c (pi sigma : computation p c) :
  configuration_owned p c -> result_state pi = result_state sigma.
Proof.
move=>Hown.
have E : stage_state pi = stage_state sigma.
  apply/funext=>k; exact: (@stage_scheduler_independent c pi sigma Hown k).
by rewrite /result_state E.
Qed.

Theorem denotational_results_unique c d e : configuration_owned p c ->
  denotational_results p c d -> denotational_results p c e -> d = e.
Proof.
move=>Hown [pi Hpi] [sigma Hsigma].
rewrite -(computes_result Hpi) -(computes_result Hsigma); apply/funext=>m.
by rewrite !result_stateE (@result_scheduler_independent c pi sigma Hown).
Qed.

End Independence.

Definition denote_configuration (P : program) c (Hc : c.2 \is den1lf) :=
  result_state (canonical_computation (processes P) Hc).
Arguments denote_configuration P {c} Hc.

Theorem denotational_results_singleton (P : program) c (Hc : c.2 \is den1lf) d :
  configuration_owned (processes P) c ->
  (denotational_results (processes P) c d <->
    d = (fun m => denote_configuration P Hc m)).
Proof.
move=>Hown; split.
- move=>Hd; apply: (@denotational_results_unique P c.2 c d
    (fun m => denote_configuration P Hc m) Hown Hd).
  exists (canonical_computation (processes P) Hc); exact: computation_converges.
- move=>->; exists (canonical_computation (processes P) Hc); exact: computation_converges.
Qed.

Definition denote_program (P : program) m (rho : 'FD1(Hq)) :=
  denote_configuration P (c := initial_configuration (processes P) m rho) (is_den1lf rho).
End DistributedSchedulerResults.


Module DistributedGlobalValue.
(* Total successful-state value, Bellman equation, and leastness.
   See PROOF_NOTES.md for the monotone mixture argument. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions DistributedSchedulerSemantics DistributedSchedulerResults.
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


Module DistributedCQInput.
(* Summable mixtures of cq-states for the two papers' distribution semantics. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Section Components.
Context {I : choiceType} {H : chsType}.
Variable (d : @CQState.state I H).

Definition weight i := \Tr (d i).

Lemma weight_nonnegative i : 0 <= weight i.
Proof. by rewrite /weight -psd_trfnorm ?psdlfE ?vdistr_ge0. Qed.

Lemma weights_summable : summable weight.
Proof.
apply: psum_ubounded_summable; exists `|d : {summable I -> 'End(H)}|=>A.
apply: (le_trans (y := psum (fun i => `|d i|) A)); last exact: psum_norm_ler_norm.
rewrite /psum /normf; apply: ler_sum=>i _.
rewrite ger0_norm ?weight_nonnegative // /weight.
by rewrite psd_trfnorm ?psdlfE ?vdistr_ge0.
Qed.

Lemma weights_bound : `|sum (Summable.build weights_summable)| <= 1.
Proof.
change (`|CQState.mass d| <= 1).
by rewrite ger0_norm ?CQState.mass_ge0 //; apply: CQState.mass_le1.
Qed.

Definition weights : Distr I := VDistr.build (f := Summable.build weights_summable)
  weight_nonnegative weights_bound.

Lemma weightsE i : weights i = \Tr (d i).
Proof. by []. Qed.

Variable fallback : 'FD1(H).
Definition normalized_raw i :=
  if 0 < weight i then (weight i)^-1 *: d i else fallback.

Lemma normalized_density i : normalized_raw i \is den1lf.
Proof.
rewrite /normalized_raw; case: ifP=>Hw; last exact: is_den1lf.
apply/den1lfP; split.
- apply: psdlfZ; first by rewrite invr_ge0; exact: ltW Hw.
  by rewrite psdlfE vdistr_ge0.
- by rewrite linearZ /= -/(weight i) mulVf ?gt_eqF.
Qed.

Definition normalized i : 'FD1(H) := Den1Lf_Build (normalized_density i).

Lemma component_reassemble i : weight i *: (normalized i : 'End(H)) = d i.
Proof.
change (weight i *: normalized_raw i = d i).
rewrite /normalized_raw; case: ifP=>Hw.
  by rewrite scalerA mulfV ?gt_eqF // scale1r.
have Hz : weight i = 0.
  by move: (weight_nonnegative i); rewrite le_eqVlt Hw orbF eq_sym=>/eqP.
have Dz : d i == 0 := introT (@trlf0_eq0 H (d i)) (conj (vdistr_ge0 (s := d) i) Hz).
by rewrite Hz scale0r (eqP Dz).
Qed.

Lemma input_reassemble :
  CQStateMixture.mix weights (fun i => CQState.point i (normalized i)) = d.
Proof.
apply/vdistrP=>j; rewrite CQStateMixture.mixE (fin_supp_sum (S := [fset j])).
- by move=>i; rewrite inE eq_sym=>/negPf ji; rewrite CQState.pointE ji scaler0.
- by rewrite psum1 CQState.pointE eqxx -/(weight j) component_reassemble.
Qed.
End Components.

Section MixtureTransfer.
Context {I J : choiceType} {H : chsType}.
Variables (fallback : 'FD1(H)) (F : I -> 'FD1(H) -> @CQState.state J H).
Definition extend (d : @CQState.state I H) : @CQState.state J H :=
  CQStateMixture.mix (weights d) (fun i => F i (normalized d fallback i)).

Lemma extendE d j : extend d j =
  sum (fun i => weight d i *: F i (normalized d fallback i) j).
Proof. by rewrite /extend CQStateMixture.mixE. Qed.

Theorem extend_kernel (K : semType I J H H) :
  (forall i (rho : 'FD1(H)) j, F i rho j = K i j rho) ->
  forall d, extend d = CQKernel.apply K d.
Proof.
move=>EF d; apply/vdistrP=>j; rewrite extendE CQKernel.applyE.
apply: eq_sum=>i; rewrite EF -linearZ /= component_reassemble.
by [].
Qed.

Lemma normalized_point (i : I) (rho : 'FD1(H)) :
  normalized (CQState.point i rho) fallback i = rho.
Proof.
apply/val_inj; change (normalized_raw (CQState.point i rho) fallback i = rho).
by rewrite /normalized_raw /weight CQState.pointE eqxx den1f_trlf ltr01 invr1 scale1r.
Qed.

Theorem extend_point i (rho : 'FD1(H)) :
  extend (CQState.point i rho) = F i rho.
Proof.
apply/vdistrP=>j; rewrite extendE (fin_supp_sum (S := [fset i])).
- move=>k; rewrite inE=>/negPf ki.
  by rewrite /weight CQState.pointE ki linear0 scale0r.
- by rewrite psum1 /weight CQState.pointE eqxx den1f_trlf scale1r normalized_point.
Qed.
End MixtureTransfer.

Section Programs.
Import DistributedLanguage DistributedSchedulerResults.
Local Notation Hq := 'H[msys]_finset.setT.
Definition default_density : 'FD1(Hq) :=
  [> deltav (@idx_default _ msys finset.setT); deltav idx_default <].

Definition run (P : program) (d : @CQState.state cmem Hq) : @CQState.state cmem Hq :=
  extend default_density (denote_program P) d.

Theorem run_point (P : program) m (rho : 'FD1(Hq)) :
  run P (CQState.point m rho) = denote_program P m rho.
Proof. exact: extend_point. Qed.

Theorem run_kernel (P : program) (K : semType cmem cmem Hq Hq) :
  (forall m (rho : 'FD1(Hq)) out, denote_program P m rho out = K m out rho) ->
  forall d, run P d = CQKernel.apply K d.
Proof. exact: extend_kernel. Qed.
End Programs.
End DistributedCQInput.
