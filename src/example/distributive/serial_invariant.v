(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.distributive Require Import language operational distribution weighted scheduler local_actions results residual sequentialization progress global_actions instruments.
From quantum.example.classical Require Import state footprint.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import global_instruments.

From quantum.example.distributive Require Import stopped_invariant scheduler_semantics residual_semantics weighted.

Module DistributedSerialInvariant.
Import DistributedLanguage DistributedOperational DistributedResidual DistributedStoppedInvariant
  DistributedSchedulerSemantics DistributedResidualSemantics DistributedWeighted.
Local Notation Hq := 'H[msys]_finset.setT.

Definition serial_invariant (P : program) (c : global_configuration (process_count P)) :=
  @good P c /\ configuration_stopped_valid (processes P) c.
Arguments serial_invariant P c : clear implicits.

Lemma serial_initial (P : program) m rho : rho \is den1lf ->
  serial_invariant P (initial_configuration (processes P) m rho).
Proof.
move=>Hr; split; last exact: initial_stopped_valid.
split=>//; apply: initial_configuration_owned; exact: processes_wf.
Qed.

Lemma serial_global_step (P : program) c mu : serial_invariant P c ->
  global_step (processes P) c mu -> forall i, serial_invariant P (branch_value mu i).
Proof.
move=>[[Hr Ho] Hv] Hstep i; split.
- split; first exact: global_step_normalized Hstep Hr i.
  exact: (@global_step_owned _ _ c mu (@processes_wf P) Ho Hstep i).
- exact: global_step_stopped_valid Ho Hv Hstep i.
Qed.

Lemma serial_collapse (P : program) rho0 c : rho0 \is den1lf ->
  serial_invariant P c -> serial_invariant P (@collapse P rho0 c).
Proof.
move=>Hrho [Hg Hs]; split; first exact: (@collapse_good P rho0 Hrho c Hg).
clear Hg; case: c Hs=>[[pc [m|]] rho] Hs //=; by move=>m'.
Qed.

Lemma serial_projected_step (P : program) rho0 c mu : rho0 \is den1lf ->
  serial_invariant P c -> @projected_step P rho0 c mu ->
  forall i, serial_invariant P (branch_value mu i).
Proof.
move=>Hr Hinv Hstep; case: Hstep Hinv=>[d nu Hd Hglobal|d Hterminal|d Hbad] Hinv i //=.
apply: serial_collapse Hr _; exact: serial_global_step Hinv Hglobal i.
Qed.

Lemma residual_collapse (P : program) rho0 c :
  residual_state (processes P) (@collapse P rho0 c) = residual_state (processes P) c.
Proof. by case: c=>[[pc [m|]] rho]. Qed.

Lemma weighted_residual_collapse (P : program) rho0 mu out :
  weighted_sum (fmap (@collapse P rho0) mu) (fun c => residual_state (processes P) c out) =
  weighted_sum mu (fun c => residual_state (processes P) c out).
Proof. apply: eq_sum=>i; by rewrite /= residual_collapse. Qed.

End DistributedSerialInvariant.
