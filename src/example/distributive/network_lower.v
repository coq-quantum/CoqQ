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

From quantum.example.distributive Require Import local_lower scheduler network_iterations boundary_lower.

Module DistributedNetworkLower.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant
  DistributedBoundarySemantics DistributedWeighted DistributedLocalHarmonic
  DistributedRendezvousHarmonic DistributedSerialInvariant DistributedSchedulerSemantics
  DistributedSchedulerResults DistributedGlobalValue DistributedResidual DistributedLocalActions
  DistributedLocalLower DistributedScheduler DistributedNetworkIterations DistributedBoundaryLower.
Local Notation Hq := 'H[msys]_finset.setT.

Section Lower.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Local Notation V := (@value P rho0).

Lemma local_pair_lower pc (i k : 'I_n) s t (K : CL.kernel) out :
  i != k -> pc i = Waiting -> pc k = Waiting ->
  idle_control (p i) = Waiting -> idle_control (p k) = Waiting ->
  statement_wf s -> statement_wf t ->
  (forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
    K m out rho ⊑ V (global_config pc (Some m) rho) out) ->
  forall m rho,
    serial_invariant P (global_config
      (replace (replace pc i (Executing s)) k (Executing t)) (Some m) rho) ->
    slet (CL.denote (translate_statement s))
      (slet (CL.denote (translate_statement t)) K) m out rho ⊑
      V (global_config (replace (replace pc i (Executing s)) k (Executing t))
        (Some m) rho) out.
Proof.
move=>Hik Hi Hk HidleI HidleK Hs Ht HK m rho Hinv.
have Efirst u r : lift_local p (replace pc k (Executing t)) i
    (local_config s (Some u) r) =
    global_config (replace (replace pc i (Executing s)) k (Executing t)) (Some u) r.
  rewrite lift_local_start //; congr (global_config _ _ _); exact: esym (replace_commute _ _ _ Hik).
have Eend u r : lift_local p (replace pc k (Executing t)) i
    (local_config Finished (Some u) r) =
    global_config (replace pc k (Executing t)) (Some u) r.
  rewrite lift_local_finished HidleI.
  have E : replace pc k (Executing t) i = Waiting by rewrite replace_other // Hi.
  by rewrite -{1}E replace_current.
have Esecond u r : lift_local p pc k (local_config t (Some u) r) =
    global_config (replace pc k (Executing t)) (Some u) r.
  exact: lift_local_start Ht.
have Efinished u r : lift_local p pc k (local_config Finished (Some u) r) =
    global_config pc (Some u) r.
  by rewrite lift_local_finished HidleK -Hk replace_current.
rewrite -Efirst in Hinv *.
apply: (@translated_local_lower P rho0 (replace pc k (Executing t)) i
  (slet (CL.denote (translate_statement t)) K) out _ s m rho Hs Hinv).
move=>u r Hentry; rewrite Eend in Hentry *.
rewrite -Esecond in Hentry *.
apply: (@translated_local_lower P rho0 pc k K out _ t u r Ht Hentry).
move=>v q Hdone; rewrite Efinished in Hdone *; exact: HK Hdone.
Qed.


Theorem network_iter_lower pc : ready pc -> forall k m rho out,
  serial_invariant P (global_config pc (Some m) rho) ->
  network_iter p k m out rho ⊑ V (global_config pc (Some m) rho) out.
Proof.
move=>Hready; elim=>[|k IH] m rho out Hinv.
- rewrite network_iter0 abort_semE soE; exact: vdistr_ge0.
- case Hfirst: (first_enabled (rendezvous_indices p) m)=>[a|].
  + have [g [c [Ha [Hg Hchain]]]] := selected_rendezvous_command Hfirst.
    have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
    have Hi := ready_enabled_waiting Hready (proj2 Hinv m erefl) Hj.
    have Hk := ready_enabled_waiting Hready (proj2 Hinv m erefl) Hl.
    have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
      by case: Hmatch=>t ch x e; exists t, x, e.
    case: Hass=>t [x [e He]]; subst effect.
    pose pc' := replace (replace pc (first_process a)
      (Executing (process_body (p (first_process a)) (first_branch a))))
      (second_process a) (Executing (process_body (p (second_process a)) (second_branch a))).
    pose m' := (m.[x <- eval e m])%M.
    have Hstep : global_step p (global_config pc (Some m) rho)
        (certain (global_config pc' (Some m') rho)).
      exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
    have Hnext := serial_global_step Hinv Hstep tt.
    have Hvalue : V (global_config pc (Some m) rho) out =
        V (global_config pc' (Some m') rho) out.
      have E := @deterministic_step_value P rho0
        (global_config pc (Some m) rho) (global_config pc' (Some m') rho)
        (proj1 Hinv) Hstep.
      by move: E=>/vdistrP/(_ out).
    rewrite (@network_iter_selected n p k m a g c Hfirst Ha) HE.
    change (slet (slet (CL.denote (CL.Assign x e))
      (slet (CL.denote (translate_statement (process_body (p (first_process a)) (first_branch a))))
        (CL.denote (translate_statement (process_body (p (second_process a)) (second_branch a))))))
      (network_iter p k) m out rho ⊑ V (global_config pc (Some m) rho) out).
    rewrite !sletA assignment_sequence Hvalue.
    have Hneq : first_process a != second_process a.
      by apply/eqP=>E; move: Hik; rewrite E ltnn.
    have Hs : statement_wf (process_body (p (first_process a)) (first_branch a)).
      exact: (proj1 (@body_owned (p (first_process a)) (first_branch a)
        (@processes_wf P (first_process a)))).
    have Ht : statement_wf (process_body (p (second_process a)) (second_branch a)).
      exact: (proj1 (@body_owned (p (second_process a)) (second_branch a)
        (@processes_wf P (second_process a)))).
    apply: (@local_pair_lower pc (first_process a) (second_process a)
      (process_body (p (first_process a)) (first_branch a))
      (process_body (p (second_process a)) (second_branch a))
      (network_iter p k) out Hneq Hi Hk
      (idle_control_waiting (first_branch a)) (idle_control_waiting (second_branch a))
      Hs Ht).
    * move=>u r Hr; exact: IH u r out Hr.
    * exact: Hnext.
  + have Hblocked : no_rendezvous p m.
      rewrite /no_rendezvous -rendezvous_indicesE; exact: first_enabled_none Hfirst.
    rewrite (network_iter_blocked k Hblocked).
    case Hterm: (term p m); last by rewrite abort_semE soE; exact: vdistr_ge0.
    rewrite -(@ready_term_value P rho0 pc m rho Hready Hterm (proj1 Hinv) out).
    exact: lexx.
Qed.

Theorem network_tail_lower pc : ready pc -> forall m rho out,
  serial_invariant P (global_config pc (Some m) rho) ->
  CL.denote (network_tail p) m out rho ⊑ V (global_config pc (Some m) rho) out.
Proof.
move=>Hready m rho out Hinv; apply: network_iter_least_output=>k.
exact: network_iter_lower Hready k m rho out Hinv.
Qed.

End Lower.
End DistributedNetworkLower.
