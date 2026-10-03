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


From quantum.example.distributive Require Import serial_scheduler residual_semantics stopped_invariant results weighted.

Module DistributedBoundarySemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant DistributedResults.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma term_first_disabled n (p : 'I_n -> process) m : term p m ->
  first_enabled (rendezvous_indices p) m = None.
Proof.
move=>Hterm; case E: (first_enabled (rendezvous_indices p) m)=>[a|] //.
have [g [c [Ha [Hg HC]]]] := selected_rendezvous_command E.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hnone := forallP (forallP Hterm (first_process a)) (first_branch a).
by rewrite Hj in Hnone.
Qed.

Lemma term_no_rendezvous n (p : 'I_n -> process) m : term p m -> no_rendezvous p m.
Proof.
move=>H; rewrite /no_rendezvous -rendezvous_indicesE; apply: first_enabled_none.
exact: term_first_disabled H.
Qed.

Lemma no_rendezvous_loop_guard n (p : 'I_n -> process) m : no_rendezvous p m ->
  eval (guards_any [seq bc.1 | bc <- rendezvous_commands p]) m = false.
Proof.
rewrite eval_guards_any has_map /no_rendezvous.
change (all (predC (fun bc : expression bool * CL.command => eval bc.1 m))
  (rendezvous_commands p) -> has (fun bc : expression bool * CL.command => eval bc.1 m)
    (rendezvous_commands p) = false).
by rewrite all_predC=>/negbTE.
Qed.

Lemma slet_row_eq (K L M : CL.kernel) m : K m = L m -> slet K M m = slet L M m.
Proof.
move=>E; apply/vdistrP=>out; change (slet_def K M m out = slet_def L M m out).
by rewrite /slet_def E.
Qed.

Lemma network_tail_blocked n (p : 'I_n -> process) m : no_rendezvous p m ->
  CL.denote (network_tail p) m = if term p m then skip_sem m else abort_sem m.
Proof.
move=>Hblocked; have Hg := no_rendezvous_loop_guard Hblocked.
have Hw := CL.denote_while_false (conditional_chain (rendezvous_commands p)) Hg.
change (slet (CL.denote (CL.While
  (guards_any [seq bc.1 | bc <- rendezvous_commands p])
  (conditional_chain (rendezvous_commands p))))
  (CL.denote (CL.Conditional (termination_guard p) CL.Skip CL.Abort)) m =
  if term p m then skip_sem m else abort_sem m).
rewrite (slet_row_eq _ Hw) slet1l CL.denote_conditional eval_termination_guard.
by [].
Qed.

Lemma network_tail_term n (p : 'I_n -> process) m : term p m ->
  CL.denote (network_tail p) m = skip_sem m.
Proof. move=>H; by rewrite (network_tail_blocked (term_no_rendezvous H)) H. Qed.

Lemma residual_stopped n (p : 'I_n -> process) m rho : rho \is denlf ->
  stopped_valid p (fun _ => Stopped) m ->
  residual_state p (global_config (fun _ : 'I_n => Stopped) (Some m) rho) =
    successful_component (global_config (fun _ : 'I_n => Stopped) (Some m) rho).
Proof.
move=>Hr Hv; have Hterm := stopped_valid_term Hv.
have Hready : ready (fun _ : 'I_n => Stopped) by move=>i; right.
apply/vdistrP=>out; rewrite residual_stateE // (residual_idle p Hready) (network_tail_term Hterm).
rewrite successful_componentE // /successful_at /=.
have Estop : [forall i : 'I_n, asbool ((fun _ : 'I_n => Stopped) i = Stopped)] by apply/forallP=>i; exact/asboolP.
rewrite Estop andbT skip_semE /=.
by rewrite eq_sym; case: (m == out); rewrite soE.
Qed.

Lemma successful_below_residual n (p : 'I_n -> process) c out :
  c.2 \is denlf -> configuration_stopped_valid p c ->
  successful_component c out ⊑ residual_state p c out.
Proof.
case: c=>[[pc [m|]] rho] Hr Hv; last by [].
case E: [forall i, asbool (pc i = Stopped)].
- have Epc : pc = (fun _ => Stopped).
    by apply/funext=>i; move: (forallP E i)=>/asboolP.
  subst pc; by rewrite (residual_stopped Hr (Hv m erefl)).
- rewrite successful_componentE // /successful_at /= E andbF.
  exact: vdistr_ge0.
Qed.

Lemma blocked_residual_harmonic n (p : 'I_n -> process) pc m rho mu out :
  ready pc -> no_rendezvous p m -> rho \is denlf ->
  global_step p (global_config pc (Some m) rho) mu ->
  DistributedWeighted.weighted_sum mu (fun c => residual_state p c out) =
    residual_state p (global_config pc (Some m) rho) out.
Proof.
move=>Hready Hblocked Hr Hstep.
have [i [Hi [Hg ->]]] := blocked_ready_step Hready Hblocked Hstep.
rewrite DistributedWeighted.weighted_certain !residual_stateE //.
by rewrite (residual_idle p Hready) (residual_idle p (ready_replace i Hready)).
Qed.

End DistributedBoundarySemantics.
