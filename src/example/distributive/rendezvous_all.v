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

From quantum.example.distributive Require Import correspondence boundary_lower.

Module DistributedAllRendezvous.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant
  DistributedBoundarySemantics DistributedWeighted DistributedSerialInvariant
  DistributedSchedulerSemantics DistributedGlobalValue DistributedResidual
  DistributedRendezvousHarmonic DistributedCorrespondence DistributedBoundaryLower
  DistributedActivePairs CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma superop_normalized_ext (U V : chsType) (F G : 'SO(U,V)) :
  (forall rho : 'FD1(U), F rho = G rho) -> F = G.
Proof.
move=>H; apply/(proj1 (so_psdP F G))=>A HA.
have Hp : 0 <= \Tr A := psdlf_trlf HA.
case Hpos: (0 < \Tr A).
- have Hnorm : (\Tr A)^-1 *: A \is den1lf.
    apply/den1lfP; split.
    + apply: psdlfZ; first by rewrite invr_ge0.
      exact: HA.
    + by rewrite linearZ /= mulVf ?gt_eqF.
  have Htest := H (Den1Lf_Build Hnorm).
  have E := congr1 (fun X : 'End(V) => \Tr A *: X) Htest.
  change (\Tr A *: F ((\Tr A)^-1 *: A) = \Tr A *: G ((\Tr A)^-1 *: A)) in E.
  by rewrite !linearZ /= !scalerA mulVf ?gt_eqF ?scale1r in E.
- have Htr : \Tr A = 0.
    by move: Hp; rewrite le_eqVlt Hpos orbF eq_sym=>/eqP.
  have EA : A = 0.
    apply/eqP/trlf0_eq0; split.
    + by rewrite -psdlfE.
    + exact: Htr.
  by rewrite EA !linear0.
Qed.

Lemma idle_serial_invariant (P : program) m rho : rho \is den1lf ->
  serial_invariant P (idle_configuration (processes P) m rho).
Proof.
move=>Hr; split.
- split=>//; exact: idle_owned.
- move=>m' [= <-] i Hstop j.
  exfalso; apply: (@after_local_stopped_no_branch (processes P i) Finished j).
  exact: Hstop.
Qed.

Theorem enabled_tail_normalized (P : program) m (rho : 'FD1(Hq))
    (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) -> eval g m -> forall out,
  CL.denote (network_tail (processes P)) m out rho =
    slet (CL.denote c) (CL.denote (network_tail (processes P))) m out rho.
Proof.
move=>Ha Hg out.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
  by case: Hmatch=>t ch x e; exists t, x, e.
case: Hass=>t [x [e He]]; subst effect.
pose pc := fun i => idle_control (processes P i).
pose src := global_config pc (Some m) (rho : 'End(Hq)).
pose dst := global_config
  (replace (replace pc (first_process a)
    (Executing (process_body (processes P (first_process a)) (first_branch a))))
    (second_process a) (Executing (process_body (processes P (second_process a)) (second_branch a))))
  (Some (m.[x <- eval e m])%M) (rho : 'End(Hq)).
have Hready : ready pc := idle_ready (processes P).
have Hinv : serial_invariant P src := @idle_serial_invariant P m rho (is_den1lf rho).
have Hi : pc (first_process a) = Waiting :=
  @idle_control_waiting (processes P (first_process a)) (first_branch a).
have Hk : pc (second_process a) = Waiting :=
  @idle_control_waiting (processes P (second_process a)) (second_branch a).
have Hstep : global_step (processes P) src (certain dst).
  exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
have Hdst : serial_invariant P dst := serial_global_step Hinv Hstep tt.
have Esrc := @residual_value P rho (is_den1lf rho) src Hinv.
have Edst := @residual_value P rho (is_den1lf rho) dst Hdst.
have EV := @deterministic_step_value P rho src dst (proj1 Hinv) Hstep.
have Eres := eq_trans Esrc (eq_trans EV (esym Edst)).
have Eout := congr1 (fun d : @CQState.state cmem Hq => d out) Eres.
have Hr : (rho : 'End(Hq)) \is denlf := den1lf_den (is_den1lf rho).
rewrite /src /dst !(@residual_stateE _ _ _ _ _ _ Hr) in Eout.
rewrite (residual_idle (processes P) Hready)
  (@residual_active_pair _ (processes P) pc (first_process a) (second_process a)
    (process_body (processes P (first_process a)) (first_branch a))
    (process_body (processes P (second_process a)) (second_branch a)) Hready Hik) in Eout.
rewrite HE.
change (CL.denote (network_tail (processes P)) m out rho =
  slet (slet (CL.denote (CL.Assign x e))
    (slet (CL.denote (translate_statement (process_body (processes P (first_process a)) (first_branch a))))
      (CL.denote (translate_statement (process_body (processes P (second_process a)) (second_branch a))))))
    (CL.denote (network_tail (processes P))) m out rho).
rewrite !sletA assignment_sequence.
exact: Eout.
Qed.

Theorem enabled_tail_kernel (P : program) m (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) -> eval g m ->
  CL.denote (network_tail (processes P)) m =
    slet (CL.denote c) (CL.denote (network_tail (processes P))) m.
Proof.
move=>Ha Hg; apply/vdistrP=>out; apply: superop_normalized_ext=>rho.
exact: (@enabled_tail_normalized P m rho a g c Ha Hg out).
Qed.

Lemma pre_row_equal total (c d : CL.command) Q m :
  CL.denote c m = CL.denote d m ->
  CQRules.pre total c Q m = CQRules.pre total d Q m.
Proof.
move=>E; case: total; apply/val_inj.
- change ((wp (CL.denote c) Q m : 'End(Hq)) = (wp (CL.denote d) Q m : 'End(Hq))).
  by rewrite !wpE E.
- change ((\1 - (wp (CL.denote c) (complement Q) m : 'End(Hq))) =
    (\1 - (wp (CL.denote d) (complement Q) m : 'End(Hq)))).
  by rewrite !wpE E.
Qed.

Theorem enabled_tail_pre (P : program) total Q m
    (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) -> eval g m ->
  CQRules.pre total (network_tail (processes P)) Q m =
    CQRules.pre total c (CQRules.pre total (network_tail (processes P)) Q) m.
Proof.
move=>Ha Hg; rewrite -CQRules.pre_sequence.
apply: pre_row_equal; exact: (@enabled_tail_kernel P m a g c Ha Hg).
Qed.

Theorem enabled_tail_invariant (P : program) total Q
    (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) ->
  CQHoare.valid total
    (mask (eval g) (CQRules.pre total (network_tail (processes P)) Q))
    c (CQRules.pre total (network_tail (processes P)) Q).
Proof.
move=>Ha; apply/(proj2 (CQRules.valid_iff _ _ _ _))=>m.
rewrite /mask; case Hg: (eval g m).
- by rewrite (@enabled_tail_pre P total Q m a g c Ha Hg).
- exact: obsf_ge0.
Qed.

Theorem all_tail_invariants (P : program) total Q :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total
      (mask (eval bc.1) (CQRules.pre total (network_tail (processes P)) Q))
      bc.2 (CQRules.pre total (network_tail (processes P)) Q))
    (rendezvous_commands (processes P)).
Proof.
rewrite -rendezvous_indicesE.
elim: (rendezvous_indices (processes P))=>[|a rest IH] /=; first exact: List.Forall_nil.
case Ha: (index_command a)=>[[g c]|] /=; last exact: IH.
apply: List.Forall_cons; last exact: IH.
exact: (@enabled_tail_invariant P total Q a g c Ha).
Qed.

End DistributedAllRendezvous.
