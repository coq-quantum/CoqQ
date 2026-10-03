(* Finite completed local executions are bounded by the global value. *)
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

From quantum.example.distributive Require Import local_iterations serial_scheduler serial_invariant scheduler_semantics global_value residual scheduler local_iteration_bounds.

From quantum.example.distributive Require Import local_lower local_iteration_limits observables instruments.

Module DistributedScalarStopping.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedDistribution DistributedWeighted DistributedLocalActions DistributedProgress
  DistributedResidualSemantics DistributedLocalCorrespondence DistributedLocalIterations
  DistributedSerialScheduler DistributedSerialInvariant DistributedSchedulerSemantics
  DistributedResidual DistributedScheduler DistributedObservables DistributedLocalLower DistributedInstruments
  DistributedLocalIterationBounds CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma observe_mono_branches X (mu : family X) (f g : X -> C) :
  probability_family mu ->
  (forall a, `|f (branch_value mu a)| <= 1) ->
  (forall a, `|g (branch_value mu a)| <= 1) ->
  (forall a, f (branch_value mu a) <= g (branch_value mu a)) ->
  family_observe mu f <= family_observe mu g.
Proof.
move=>Hm Hf Hg Hfg.
pose index_family := @Family (branch_index mu) (branch_index mu) (branch_weight mu) id.
have Sf := @observe_summable _ index_family
  (fun a => f (branch_value mu a)) 1 Hm ler01 Hf.
have Sg := @observe_summable _ index_family
  (fun a => g (branch_value mu a)) 1 Hm ler01 Hg.
rewrite /family_observe; apply: ler_etlim.
- exact: norm_bounded_cvg Sf.
- exact: norm_bounded_cvg Sg.
- move=>A; apply: ler_sum=>a _; apply: ler_wpM2l.
  + exact: (proj1 (proj2 Hm)).
  + exact: Hfg.
Qed.

Definition local_observe (F : statement -> CL.kernel) (A : assertion)
    (c : local_configuration) : C :=
  if c.1.2 is Some m then \Tr (wp (F c.1.1) A m \o c.2) else 0.

Lemma local_observe_bound F A c : c.2 \is denlf -> `|local_observe F A c| <= 1.
Proof.
case: c=>[[s [m|]] rho] Hr; last by rewrite /local_observe /= normr0.
rewrite /local_observe /=.
rewrite -(@CQExpectation.expect_point cmem Hq (wp (F s) A) m (DenLf_Build Hr)).
by rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
Qed.

Lemma local_unfold_observe F s m rho A : rho \is den1lf ->
  \Tr (wp (local_unfold F s) A m \o rho) =
    family_observe (local_successor s m rho) (local_observe F A).
Proof.
move=>Hr; rewrite local_unfold_wp wp_pairing
  (@local_realization s m rho Hr) /family_observe /local_family /=.
apply:eq_sum=>a; rewrite local_mapsE.
case E: (@local_control s m a)=>[t [u|]]; rewrite /local_observe /=;
  last by rewrite linear0l linear0 mulr0.
have W := congr1 (fun X : 'End(Hq) => \Tr (wp (F t) A u \o X))
  (weighted_normalized_output (@local_cp s m a) Hr).
by rewrite linearZr /= linearZ /= in W; symmetry.
Qed.

Section Stopping.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable pc : 'I_n -> control.
Variable i : 'I_n.
Variable V : global_configuration n -> C.
Hypothesis Vnonnegative : forall c, serial_invariant P c -> 0 <= V c.
Hypothesis Vbounded : forall c, serial_invariant P c -> `|V c| <= 1.
Hypothesis Vstep : forall c mu, serial_invariant P c -> global_step p c mu ->
  family_observe mu V <= V c.
Variable A : assertion.
Hypothesis endpoint_bound : forall m rho,
  serial_invariant P (lift_local p pc i (local_config Finished (Some m) rho)) ->
  \Tr (A m \o rho) <= V (lift_local p pc i (local_config Finished (Some m) rho)).

Theorem local_iter_stopping N : forall s m rho,
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  \Tr (wp (local_iter N s) A m \o rho) <=
    V (lift_local p pc i (local_config s (Some m) rho)).
Proof.
elim: N=>[|N IH] s m rho Hinv.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished wp_skip; exact: endpoint_bound Hinv.
  + have E : local_iter 0 s = abort_sem by clear Hinv; case: s Hs.
    rewrite E wp_abort linear0l linear0; exact: Vnonnegative Hinv.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished wp_skip; exact: endpoint_bound Hinv.
  + have Hr : rho \is den1lf := proj1 (proj1 Hinv).
    have Hstep := lifted_local_step p pc i m rho Hs.
    change (\Tr (wp (local_unfold (local_iter N) s) A m \o rho) <=
      V (lift_local p pc i (local_config s (Some m) rho))).
    rewrite (@local_unfold_observe (local_iter N) s m rho A Hr).
    apply: (le_trans _ (Vstep Hinv Hstep)).
    change (family_observe (local_successor s m rho) (local_observe (local_iter N) A) <=
      family_observe (local_successor s m rho) (fun d => V (lift_local p pc i d))).
    apply: observe_mono_branches.
    * exact: local_step_probability (local_successor_step Hs m rho) Hr.
    * move=>a; apply: local_observe_bound; apply: den1lf_den.
      exact: local_step_normalized (local_successor_step Hs m rho) Hr a.
    * move=>a; apply: Vbounded; exact: serial_global_step Hinv Hstep a.
    * move=>a; have HI := serial_global_step Hinv Hstep a.
      case E: (branch_value (local_successor s m rho) a)=>[[t [u|]] r].
      -- change (\Tr (wp (local_iter N t) A u \o r) <=
          V (lift_local p pc i (local_config t (Some u) r))).
         apply: IH; by move: HI; rewrite /= E.
      -- change (0 <= V (lift_local p pc i (local_config t None r))).
         apply: Vnonnegative; by move: HI; rewrite /= E.
Qed.
End Stopping.
End DistributedScalarStopping.
