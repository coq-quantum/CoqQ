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

Module DistributedGlobalPredicate.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedResidual DistributedResults DistributedSchedulerSemantics
  DistributedGlobalInstruments DistributedGlobalActions DistributedInstruments
  DistributedLocalActions DistributedProgress DistributedObservables DistributedLocalDiamond
  DistributedGlobalValue DistributedScheduler DistributedLocalCorrespondence CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.
Local Notation assertion := (@semantic_assertion cmem Hq).

Section Step.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Local Notation controls := ('I_n -> control).

Definition descriptor_valid pc m (d : descriptor n) :=
  exists a, enabled_descriptor p pc m a d /\ statement_wf (instruction d).

Definition selected_descriptor pc m : option (descriptor n) :=
  match pselect (exists d, descriptor_valid pc m d) with
  | left H => Some (projT1 (cid H))
  | right _ => None
  end.

Lemma selected_descriptor_some pc m d :
  selected_descriptor pc m = Some d -> descriptor_valid pc m d.
Proof.
rewrite /selected_descriptor; case: pselect=>[H|H] //.
by move=>[= <-]; exact: projT2 (cid H).
Qed.

Lemma selected_descriptor_none pc m : selected_descriptor pc m = None ->
  forall d, ~ descriptor_valid pc m d.
Proof.
rewrite /selected_descriptor; case: pselect=>[H|H] // _ d Hd.
by apply: H; exists d.
Qed.

Lemma descriptor_terminal pc m rho : configuration_owned p (global_config pc (Some m) rho) ->
  selected_descriptor pc m = None -> terminal p (global_config pc (Some m) rho).
Proof.
move=>Ho Hnone mu Hstep.
have [a Ha] := labeled_step_complete Hstep.
have [u [d [Eu [Hd [Hwf E]]]]] := labeled_step_descriptor Ho Ha.
change (Some m = Some u) in Eu; case: Eu=>Eum; subst u.
apply: (@selected_descriptor_none pc m Hnone d); by exists a.
Qed.

Definition observe (F : controls -> assertion) (c : global_configuration n) :=
  if c.1.2 is Some m then \Tr (F c.1.1 m \o c.2) else 0.

Definition descriptor_pre (F : controls -> assertion) (d : descriptor n) pc m : 'FO(Hq) :=
  wp (SemType (fun _ : unit => local_maps (instruction d) m))
    (fun a => if (@local_control (instruction d) m a).2 is Some u then
      F (update_control d (@local_control (instruction d) m a).1 pc) u else 0%:VF) tt.

Lemma descriptor_pre_observe F d pc m rho : rho \is den1lf ->
  \Tr (descriptor_pre F d pc m \o rho) =
  family_observe (descriptor_run d pc m rho) (observe F).
Proof.
move=>Hr; rewrite /descriptor_pre wp_pairing /descriptor_run
  (@local_realization (instruction d) m rho Hr) /family_observe /local_family /=.
apply: eq_sum=>a; rewrite local_mapsE /observe /descriptor_lift /local_config /=.
case E: (@local_control (instruction d) m a)=>[s [u|]] /=;
  last by rewrite linear0l linear0 mulr0.
have W := congr1 (fun A : 'End(Hq) => \Tr (F (update_control d s pc) u \o A))
  (weighted_normalized_output (@local_cp (instruction d) m a) Hr).
by rewrite linearZr /= linearZ /= in W; symmetry.
Qed.

Definition terminal_pre (Q : assertion) (pc : controls) m : 'FO(Hq) :=
  if [forall i, asbool (pc i = Stopped)] then Q m else 0%:VF.

Fixpoint horizon_pre k (Q : assertion) pc m : 'FO(Hq) :=
  if k is j.+1 then
    if selected_descriptor pc m is Some d then descriptor_pre (horizon_pre j Q) d pc m
    else terminal_pre Q pc m
  else terminal_pre Q pc m.

Lemma terminal_pre_observe Q pc m rho : rho \is denlf ->
  \Tr (terminal_pre Q pc m \o rho) =
  expect Q (successful_component (global_config pc (Some m) rho)).
Proof.
move=>Hr; rewrite /terminal_pre /successful_component /=.
case E: [forall i, asbool (pc i = Stopped)].
- case: asboolP=>[H|H]; last by exfalso; apply: H.
  by rewrite CQExpectation.expect_point.
- by rewrite CQHoare.expect_bottom linear0l linear0.
Qed.

End Step.
End DistributedGlobalPredicate.
