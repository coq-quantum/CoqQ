(* Finite operational horizons as effects; see the D5 completeness argument. *)
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
From Stdlib Require List.
From quantum.example.distributive Require Import language operational sequentialization guarded_rules.
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


From quantum.example.distributive Require Import distribution weighted local_actions progress residual_semantics local_correspondence.

From quantum.example.distributive Require Import local_iterations serial_scheduler serial_invariant scheduler_semantics global_value residual scheduler.

From quantum.example.distributive Require Import local_lower.

From quantum.example.distributive Require Import active_lower control_completion network_lower serial_upper scheduler_results.

From quantum.example.distributive Require Import global_instruments global_actions instruments observables local_diamond results.

From quantum.example.classical Require Import mixture mixture_expectation.
From quantum.example.distributive Require Import global_predicate.

From quantum.example.distributive Require Import horizon_expectation.

From quantum.example.distributive Require Import horizon_remainder rendezvous_all correspondence normalized_tests.

From quantum.example.distributive Require Import horizon_effects active_stopping ranking_controls network_rules.
From quantum.example.classical Require Import primitive.

Module DistributedNetworkRanking.
Import DistributedLanguage DistributedSequentialization DistributedOperational DistributedDistribution
  DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions
  DistributedSchedulerSemantics DistributedGlobalValue DistributedGlobalPredicate
  DistributedHorizonExpectation DistributedHorizonRemainder DistributedHorizonEffects
  DistributedObservables DistributedSerialScheduler DistributedSerialInvariant
  DistributedResidualSemantics DistributedCorrespondence DistributedAllRendezvous
  DistributedNormalizedTests DistributedRankingControls DistributedActiveStopping
  DistributedActiveLower DistributedNetworkRules CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Ranking.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable Q : assertion.
Local Notation ranks := (@rank_assertion P Q).

Lemma active_pair_rank rho0 k (i j : 'I_n) s t m rho : rho0 \is den1lf ->
  (i < j)%N ->
  serial_invariant P (global_config
    (replace (replace (fun z => idle_control (p z)) i (Executing s)) j (Executing t))
    (Some m) rho) ->
  \Tr (wp (CL.denote (CL.Sequence (translate_statement s) (translate_statement t)))
    (ranks k) m \o rho) <=
  @progress_potential P rho0 Q k (global_config
    (replace (replace (fun z => idle_control (p z)) i (Executing s)) j (Executing t))
    (Some m) rho).
Proof.
move=>Hr0 Hij Hinv.
pose pc := replace (replace (fun z => idle_control (p z)) i (Executing s)) j (Executing t).
have Hp : ready (fun z => idle_control (p z)) := DistributedSerialScheduler.idle_ready p.
have Eactive : CL.denote (active_program (enum 'I_n) pc CL.Skip) =
  CL.denote (CL.Sequence (translate_statement s) (translate_statement t)).
  rewrite /pc (@active_program_pair n (fun z => idle_control (p z)) i j s t CL.Skip Hp Hij).
  change (slet (CL.denote (translate_statement s))
    (CL.denote (CL.Sequence (translate_statement t) CL.Skip)) =
    slet (CL.denote (translate_statement s)) (CL.denote (translate_statement t))).
  by rewrite CL.denote_skip_right.
rewrite -Eactive.
apply: (@active_program_stopping P (@progress_potential P rho0 Q k)
  _ _ _ (enum 'I_n) (enum_uniq _) pc CL.Skip (ranks k) _ m rho Hinv).
- move=>c _; exact: progress_nonnegative.
- move=>c _; exact: progress_bound.
- move=>c mu [[Hr Ho] _] Hs; exact: progress_superharmonic Hs Hr Ho.
- move=>u r Hend; rewrite /pc finish_active_pair in Hend *.
  rewrite wp_skip.
  rewrite (@rank_assertion_pairing P Q rho0 k u r Hr0 (proj1 (proj1 Hend))).
  by [].
Qed.

Theorem enabled_rank_bound k (a : rendezvous_index p) g c :
  index_command a = Some (g,c) ->
  semantic_le (mask (eval g) (CQRules.wp_command c (ranks k))) (ranks k.+1).
Proof.
move=>Ha m; rewrite /mask; case Hg: (eval g m); last exact: obsf_ge0.
apply: operator_le_normalized=>rho.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
  by case: Hmatch=>t ch x e; exists t, x, e.
case: Hass=>t [x [e He]]; subst effect.
pose pc := fun z => idle_control (p z).
pose src := global_config pc (Some m) (rho : 'End(Hq)).
pose dst := global_config
  (replace (replace pc (first_process a)
    (Executing (process_body (p (first_process a)) (first_branch a))))
    (second_process a) (Executing (process_body (p (second_process a)) (second_branch a))))
  (Some (m.[x <- eval e m])%M) (rho : 'End(Hq)).
have Hinv : serial_invariant P src := @idle_serial_invariant P m rho (is_den1lf rho).
have Hi : pc (first_process a) = Waiting :=
  @idle_control_waiting (p (first_process a)) (first_branch a).
have Hk : pc (second_process a) = Waiting :=
  @idle_control_waiting (p (second_process a)) (second_branch a).
have Hstep : global_step p src (certain dst).
  exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
have Hdst : serial_invariant P dst := serial_global_step Hinv Hstep tt.
have EB := @active_pair_rank rho k (first_process a) (second_process a)
  (process_body (p (first_process a)) (first_branch a))
  (process_body (p (second_process a)) (second_branch a))
  (m.[x <- eval e m])%M rho (is_den1lf rho) Hik Hdst.
have EP := @progress_step P rho Q k src (certain dst) Hstep
  (is_den1lf rho) (proj2 (proj1 Hinv)).
rewrite observe_certain in EP.
have ER := @rank_assertion_pairing P Q rho k.+1 m rho (is_den1lf rho) (is_den1lf rho).
change (\Tr (CQRules.pre true c (ranks k) m \o rho) <= \Tr (ranks k.+1 m \o rho)).
rewrite HE CQRules.pre_sequence /CQRules.pre CQPrimitive.assign_pre.
apply: (le_trans EB).
by rewrite EP -ER.
Qed.

Theorem tail_network_ranking : network_ranking (@tail_assertion P Q) p.
Proof.
apply: (ListRanking (list_rank := ranks)).
- exact: rank_assertion_decreasing.
- exact: semantic_le_refl.
- exact: rank_assertion_zero.
- move=>k; rewrite -rendezvous_indicesE.
  elim: (rendezvous_indices p)=>[|a rest IH] /=; first exact: List.Forall_nil.
  case Ha: (index_command a)=>[[g c]|] /=; last exact: IH.
  apply: List.Forall_cons; last exact: IH.
  exact: enabled_rank_bound Ha.
Qed.

End Ranking.
End DistributedNetworkRanking.
