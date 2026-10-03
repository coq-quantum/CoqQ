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

Module DistributedLocalLower.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedDistribution DistributedWeighted DistributedLocalActions DistributedProgress
  DistributedResidualSemantics DistributedLocalCorrespondence DistributedLocalIterations
  DistributedSerialScheduler DistributedSerialInvariant DistributedSchedulerSemantics
  DistributedGlobalValue DistributedResidual DistributedScheduler.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma weighted_mono_branches X (H : chsType) (mu : family X) (f g : X -> 'End(H)) :
  probability_family mu ->
  (forall a, `|f (branch_value mu a)| <= 1) ->
  (forall a, `|g (branch_value mu a)| <= 1) ->
  (forall a, f (branch_value mu a) ⊑ g (branch_value mu a)) ->
  weighted_sum mu f ⊑ weighted_sum mu g.
Proof.
move=>Hm Hf Hg Hfg.
exact: (@weighted_mono (branch_index mu) H
  (@Family _ (branch_index mu) (branch_weight mu) id)
  (fun a => f (branch_value mu a)) (fun a => g (branch_value mu a)) Hm Hf Hg Hfg).
Qed.

Lemma replace_twice n (pc : 'I_n -> control) i a b :
  replace (replace pc i a) i b = replace pc i b.
Proof. apply/funext=>j; rewrite /replace; by case: (j == i). Qed.
Lemma lift_replace n (p : 'I_n -> process) pc i a c :
  lift_local p (replace pc i a) i c = lift_local p pc i c.
Proof. by case: c=>[[s m] rho]; rewrite /lift_local /= replace_twice. Qed.

Lemma lifted_local_step n (p : 'I_n -> process) pc i s m rho : statement_wf s ->
  global_step p (lift_local p pc i (local_config s (Some m) rho))
    (fmap (lift_local p pc i) (local_successor s m rho)).
Proof.
move=>Hs; rewrite (lift_local_start _ _ _ _ _ Hs).
have E : fmap (lift_local p (replace pc i (Executing s)) i) (local_successor s m rho) =
    fmap (lift_local p pc i) (local_successor s m rho).
  congr (@Family _ _ _ _); apply/funext=>a; exact: lift_replace.
rewrite -E; apply: StepParallel; first exact: replace_same.
exact: local_successor_step Hs m rho.
Qed.

Lemma residual_output_bound (F : statement -> CL.kernel) c out :
  c.2 \is denlf -> `|residual_output F c out| <= 1.
Proof.
case: c=>[[s [m|]] rho] Hr; rewrite /residual_output /=; last by rewrite normr0.
have Hd : F s m out rho \is denlf := qo_denlf _ (DenLf_Build Hr).
by rewrite psd_trfnorm ?denlf_psd //; exact: denlf_trlf Hd.
Qed.

Section Lower.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Local Notation V := (@value P rho0).
Variable pc : 'I_n -> control.
Variable i : 'I_n.

Lemma lifted_residual_wf s m rho :
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  residual_wf s.
Proof.
move=>[[Hr Ho] Hv].
have H := Ho i; rewrite /lift_local /= replace_same in H.
clear Hr Ho Hv.
case: s H=>[|a|s t|k g b|k g b] /= H; first by left.
all: right; exact: (proj1 H).
Qed.

Lemma lifted_bellman s m rho out : statement_wf s ->
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  V (lift_local p pc i (local_config s (Some m) rho)) out =
    weighted_sum (local_successor s m rho) (fun d => V (lift_local p pc i d) out).
Proof.
move=>Hs [Hg Hv].
have Hstep := lifted_local_step p pc i m rho Hs.
have Hproj := @ProjectedGlobal P rho0 _ _ Hg Hstep.
apply: (eq_trans (@value_bellman P rho0 _ _ out Hproj)).
apply: eq_sum=>a; by rewrite /= value_collapse.
Qed.

Variable K : CL.kernel.
Variable out : cmem.
Hypothesis endpoint_lower : forall m rho,
  serial_invariant P (lift_local p pc i (local_config Finished (Some m) rho)) ->
  K m out rho ⊑ V (lift_local p pc i (local_config Finished (Some m) rho)) out.

Theorem local_iter_lower N : forall s m rho,
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  slet (local_iter N s) K m out rho ⊑
    V (lift_local p pc i (local_config s (Some m) rho)) out.
Proof.
elim: N=>[|N IH] s m rho Hinv.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished slet1l; exact: endpoint_lower Hinv.
  + have E : local_iter 0 s = abort_sem by clear Hinv; case: s Hs.
    rewrite E slet_abort_left abort_semE soE; exact: vdistr_ge0.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished slet1l; exact: endpoint_lower Hinv.
  + have Hr : rho \is den1lf := proj1 (proj1 Hinv).
    have Hstep := lifted_local_step p pc i m rho Hs.
    change (slet (local_unfold (local_iter N) s) K m out rho ⊑
      V (lift_local p pc i (local_config s (Some m) rho)) out).
    rewrite local_unfold_compose (@local_unfold_weighted
      (fun r => slet (local_iter N r) K) s m rho out Hr).
    rewrite (lifted_bellman out Hs Hinv).
    apply: weighted_mono_branches.
    * exact: local_step_probability (local_successor_step Hs m rho) Hr.
    * move=>a; apply: residual_output_bound; apply: den1lf_den.
      exact: local_step_normalized (local_successor_step Hs m rho) Hr a.
    * move=>a; exact: value_bound.
    * move=>a.
      have HI := serial_global_step Hinv Hstep a.
      case E: (branch_value (local_successor s m rho) a)=>[[t [u|]] r].
      -- change (slet (local_iter N t) K u out r ⊑
          V (lift_local p pc i (local_config t (Some u) r)) out).
         apply: IH; by move: HI; rewrite /= E.
      -- change (0%:VF ⊑ V (lift_local p pc i (local_config t None r)) out).
         exact: vdistr_ge0.
Qed.
Theorem translated_local_lower s m rho : statement_wf s ->
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  slet (CL.denote (translate_statement s)) K m out rho ⊑
    V (lift_local p pc i (local_config s (Some m) rho)) out.
Proof.
move=>Hs Hinv; apply: DistributedLocalIterationBounds.local_iter_least_output Hs _ _.
- rewrite -psdlfE; apply: denlf_psd; apply: den1lf_den.
  exact: (proj1 (proj1 Hinv)).
- move=>N; exact: local_iter_lower Hinv.
Qed.
End Lower.
End DistributedLocalLower.
