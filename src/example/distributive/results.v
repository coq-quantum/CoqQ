(* Well-formed cq-states of successful finite-stage outcomes, Section 3.2. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import notation mxpred extnum ctopology hermitian quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import language operational distribution weighted.
From quantum.example.classical Require Import state mixture.

Module DistributedResults.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Definition successful_component n (c : global_configuration n) : state :=
  match c.1.2 with
  | None => CQState.bottom
  | Some s =>
      if [forall i, asbool (c.1.1 i = Stopped)] then
        match asboolP (c.2 \is denlf) with
        | ReflectT H => CQState.point s (DenLf_Build H)
        | ReflectF _ => CQState.bottom
        end
      else CQState.bottom
  end.

Lemma successful_componentE n (c : global_configuration n) m :
  c.2 \is denlf -> successful_component c m =
  if successful_at c m then c.2 else 0.
Proof.
case: c=>[[pc [s|]] rho] Pr; rewrite /successful_component /successful_at /=;
  last by [].
case E: [forall i, asbool (pc i = Stopped)].
- case: asboolP=>[H|H]; last by exfalso; apply: H.
  by rewrite CQState.pointE /= andbT eq_sym.
- by rewrite andbF CQState.bottomE.
Qed.

Definition successful_state n (mu : family (global_configuration n))
    (H : probability_family mu) : state :=
  CQStateMixture.mix (probability_distribution H)
    (fun i => successful_component (branch_value mu i)).

Lemma successful_stateE n (mu : family (global_configuration n))
    (H : probability_family mu) :
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  forall m, successful_state H m = successful_result mu m.
Proof.
move=>Hr m; rewrite /successful_state CQStateMixture.mixE /successful_result.
apply: eq_sum=>i; rewrite probability_distributionE.
case P: (0 < branch_weight mu i).
- rewrite successful_componentE; first by apply: den1lf_den; apply: Hr.
  by case: successful_at; rewrite ?scaler0.
- have w0 : branch_weight mu i = 0.
    by move: (proj1 (proj2 H) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by rewrite w0 scale0r; case: successful_at; rewrite ?scale0r.
Qed.

Definition stage_state n (p : 'I_n -> process) c (pi : computation p c) k : state :=
  successful_state (computation_probability pi k).

Lemma stage_stateE n (p : 'I_n -> process) c (pi : computation p c) k m :
  stage_state pi k m = successful_result (computation_stage pi k) m.
Proof. apply: successful_stateE; exact: computation_normalized. Qed.

Lemma stage_mass_bound n (p : 'I_n -> process) c (pi : computation p c) k :
  CQState.mass (stage_state pi k) <= 1.
Proof. exact: CQState.mass_le1. Qed.

Lemma successful_component_bound n (c : global_configuration n) m :
  `|successful_component c m| <= 1.
Proof.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
apply: denlf_trlf; exact: CQState.component_density.
Qed.

Lemma successful_component_terminal_or_zero n (p : 'I_n -> process) c :
  terminal p c \/ successful_component c = CQState.bottom.
Proof.
case: c=>[[pc [s|]] rho]; last by right.
case E: [forall i, asbool (pc i = Stopped)].
- left; have Epc : pc = (fun _ => Stopped).
    by apply/funext=>i; move/forallP: E=>/(_ i)/asboolP.
  rewrite Epc; exact: stopped_terminal.
- by right; rewrite /successful_component E.
Qed.

Lemma successful_state_weighted n (mu : family (global_configuration n))
    (H : probability_family mu) m :
  successful_state H m = weighted_sum mu (fun c => successful_component c m).
Proof.
rewrite /successful_state CQStateMixture.mixE /weighted_sum.
by apply: eq_sum=>i; rewrite probability_distributionE.
Qed.

Lemma successful_component_step n (p : 'I_n -> process) c nu m :
  ((terminal p c /\ nu = certain c) \/ global_step p c nu) ->
  probability_family nu ->
  successful_component c m ⊑ weighted_sum nu (fun d => successful_component d m).
Proof.
move=>Hs Hn; case: (successful_component_terminal_or_zero p c)=>[Ht|Hz].
- case: Hs=>[[Htc ->]|Hs]; last by exfalso; exact: Ht _ Hs.
  by rewrite weighted_certain.
- rewrite Hz CQState.bottomE -successful_state_weighted.
  exact: vdistr_ge0.
Qed.

Lemma successful_state_step n (p : 'I_n -> process)
    (mu nu : family (global_configuration n))
    (Hm : probability_family mu) (Hn : probability_family nu) :
  distribution_step p mu nu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  successful_state Hm ⊑ successful_state Hn.
Proof.
move=>[Ha [next [Hnext E]]] Hr.
have Hnextprob : forall i, 0 < branch_weight mu i -> probability_family (next i).
  move=>i Hi; case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: global_step_probability Hs (Hr i Hi).
have Hb := bind_family_probability Hm Hnextprob.
apply/levdP=>m; rewrite !successful_state_weighted.
rewrite (weighted_same Hn Hb E (fun c => successful_component_bound c m)).
rewrite (weighted_bind Hm Hnextprob (fun c => successful_component_bound c m)).
apply: lev_lim.
- apply: norm_bounded_cvg.
  exact: weighted_summable Hm (fun c => successful_component_bound c m).
- apply: norm_bounded_cvg; exact: weighted_bind_summable Hm Hnextprob (fun c => successful_component_bound c m).
- move=>A; apply: lev_sum=>i _.
  case P: (0 < branch_weight mu (val i)).
  + apply: lev_pscale2lP; first exact: P.
    exact: successful_component_step (Hnext (val i) P) (Hnextprob (val i) P).
  + have Z : branch_weight mu (val i) = 0.
      by move: (proj1 (proj2 Hm) (val i)); rewrite le_eqVlt P orbF eq_sym=>/eqP.
    by rewrite Z !scale0r.
Qed.

Lemma stage_state_step n (p : 'I_n -> process) c (pi : computation p c) k :
  stage_state pi k ⊑ stage_state pi k.+1.
Proof.
apply: successful_state_step; first exact: computation_advances.
exact: computation_normalized.
Qed.

Lemma stage_state_chain n (p : 'I_n -> process) c (pi : computation p c) :
  nondecreasing_seq (stage_state pi).
Proof. apply/nondecreasing_seqP=>k; exact: stage_state_step. Qed.

Definition result_state n (p : 'I_n -> process) c (pi : computation p c) : state :=
  CQState.chain_sup (stage_state pi).

Theorem computation_converges n (p : 'I_n -> process) c (pi : computation p c) :
  computes pi (fun m => result_state pi m).
Proof.
move=>m; rewrite /result_state
  (@CQState.chain_sup_pointwise cmem Hq (stage_state pi) (stage_state_chain pi) m).
have Eseq : (fun k => successful_result (computation_stage pi k) m) =
    (fun k => stage_state pi k m).
  by apply/funext=>k; rewrite stage_stateE.
rewrite Eseq.
apply: cvgP.
have C := @CQState.chain_converges cmem Hq (stage_state pi) (stage_state_chain pi).
exact: (@summableE_is_cvg _ _ _ _ _ _ _ _ C m).
Qed.

Lemma result_stateE n (p : 'I_n -> process) c (pi : computation p c) m :
  computed_result pi m = result_state pi m.
Proof. by rewrite (computes_result (computation_converges (pi := pi))). Qed.

Lemma result_state_upper n (p : 'I_n -> process) c (pi : computation p c) k :
  stage_state pi k ⊑ result_state pi.
Proof. exact: (@CQState.chain_sup_upper cmem Hq (stage_state pi) (stage_state_chain pi) k). Qed.

Lemma result_state_least n (p : 'I_n -> process) c (pi : computation p c) (d : state) :
  (forall k, stage_state pi k ⊑ d) -> result_state pi ⊑ d.
Proof. exact: (@CQState.chain_sup_least cmem Hq (stage_state pi) d (stage_state_chain pi)). Qed.

Theorem denotational_results_nonempty n (p : 'I_n -> process) c :
  c.2 \is den1lf -> exists d, denotational_results p c d.
Proof.
move=>Hc; pose pi := canonical_computation p Hc.
exists (fun m => result_state pi m); exists pi; exact: computation_converges.
Qed.

End DistributedResults.
