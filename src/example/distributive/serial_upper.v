(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)
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


From quantum.example.distributive Require Import serial_scheduler residual_semantics stopped_invariant results.

From quantum.example.distributive Require Import boundary_semantics active_pairs weighted.

From quantum.example.distributive Require Import local_harmonic rendezvous_harmonic
  serial_invariant scheduler_semantics scheduler_results global_value residual local_actions.

Module DistributedSerialUpper.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant
  DistributedBoundarySemantics DistributedWeighted DistributedLocalHarmonic
  DistributedRendezvousHarmonic DistributedSerialInvariant DistributedSchedulerSemantics
  DistributedSchedulerResults DistributedGlobalValue DistributedResidual DistributedLocalActions.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma residual_successor (P : program) rho0 c : serial_invariant P c ->
  exists mu, @projected_step P rho0 c mu /\
    forall out, weighted_sum mu (fun d => residual_state (processes P) d out) =
      residual_state (processes P) c out.
Proof.
case: c=>[[pc [m|]] rho] [[Hr Ho] Hv].
- have Hg : @good P (global_config pc (Some m) rho) by split.
  case Hfirst: (first_active (enum 'I_(process_count P)) pc)=>[[i s]|].
  + have [xs [ys [E [Hi Hp]]]] := first_active_some Hfirst.
    have Hs : statement_wf s.
      have Hiown := Ho i; rewrite /control_owned /= Hi in Hiown; exact: (proj1 Hiown).
    have Hstep := serial_local_step (processes P) m rho Hs Hi.
    exists (fmap (@collapse P rho0)
      (fmap (lift_local (processes P) pc i) (local_successor s m rho))); split.
    * exact: ProjectedGlobal Hg Hstep.
    * move=>out; rewrite weighted_residual_collapse.
      symmetry; exact: residual_local_harmonic Hs Hr Hfirst.
  + have Hready : ready pc.
      move=>i; have Hi : i \in enum 'I_(process_count P) by rewrite mem_enum.
      exact: (@first_active_none _ _ pc Hfirst i Hi).
    case Hselected: (first_enabled (rendezvous_indices (processes P)) m)=>[a|].
    * have [mu [Hstep HE]] := residual_rendezvous_step Hready (Hv m erefl)
        (den1lf_den Hr) Hselected.
      exists (fmap (@collapse P rho0) mu); split.
      -- exact: ProjectedGlobal Hg Hstep.
      -- move=>out; rewrite weighted_residual_collapse; exact: HE.
    * have Hblocked : no_rendezvous (processes P) m.
        rewrite /no_rendezvous -rendezvous_indicesE; exact: first_enabled_none Hselected.
      case: (pselect (exists mu, global_step (processes P)
        (global_config pc (Some m) rho) mu))=>[[mu Hstep]|Hnone].
      -- exists (fmap (@collapse P rho0) mu); split.
         ++ exact: ProjectedGlobal Hg Hstep.
         ++ move=>out; rewrite weighted_residual_collapse.
            exact: blocked_residual_harmonic Hready Hblocked (den1lf_den Hr) Hstep.
      -- exists (certain (global_config pc (Some m) rho)); split.
         ++ apply: ProjectedTerminal=>mu Hstep; apply: Hnone; by exists mu.
         ++ move=>out; exact: weighted_certain.
- exists (certain (global_config pc None rho)); split.
  + apply: ProjectedTerminal; exact: failure_terminal.
  + move=>out; exact: weighted_certain.
Qed.

Theorem value_below_residual (P : program) rho0 : rho0 \is den1lf ->
  forall c, serial_invariant P c ->
    @value P rho0 c ⊑ residual_state (processes P) c.
Proof.
move=>Hrho c Hc; apply/levdP=>out.
apply: (@value_least_invariant P rho0 out (serial_invariant P)
  (fun d => residual_state (processes P) d out)).
- move=>d; exact: residual_state_bound.
- move=>d [[Hr Ho] Hv]; exact: successful_below_residual (den1lf_den Hr) Hv.
- move=>d Hd; have [mu [Hs HE]] := @residual_successor P rho0 d Hd.
  exists mu; split=>//; split.
  + move=>i Hi; exact: serial_projected_step Hrho Hd Hs i.
  + by rewrite HE.
- exact: Hc.
Qed.

Theorem denote_program_below_sequentialize (P : program) m (rho : 'FD1(Hq)) :
  denote_program P m rho ⊑
    CQKernel.apply (CL.denote (successful_sequentialize (processes P)))
      (CQState.point m (rho : 'FD(Hq))).
Proof.
have Hinit := @serial_initial P m rho (is_den1lf rho).
have H := @value_below_residual P rho (is_den1lf rho) _ Hinit.
rewrite (@value_denote P rho (initial_configuration (processes P) m rho)
    (is_den1lf rho) (proj2 (proj1 Hinit)))
  residual_initial_state in H.
exact: H.
Qed.

End DistributedSerialUpper.
