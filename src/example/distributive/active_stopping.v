(* Sequential completion of a finite list of active processes. *)
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

From quantum.example.distributive Require Import active_lower scalar_stopping_limit distribution.

Module DistributedActiveStopping.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant
  DistributedLocalLower DistributedResidual DistributedActiveLower
  DistributedScalarStoppingLimit DistributedDistribution CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Stopping.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable V : global_configuration n -> C.
Hypothesis Vnonnegative : forall c, serial_invariant P c -> 0 <= V c.
Hypothesis Vbounded : forall c, serial_invariant P c -> `|V c| <= 1.
Hypothesis Vstep : forall c mu, serial_invariant P c -> global_step p c mu ->
  family_observe mu V <= V c.

Theorem active_program_stopping indices : uniq indices ->
  forall pc tail (A : assertion),
  (forall m rho,
    serial_invariant P (global_config (finish_controls p indices pc) (Some m) rho) ->
    \Tr (wp (CL.denote tail) A m \o rho) <=
      V (global_config (finish_controls p indices pc) (Some m) rho)) ->
  forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
  \Tr (wp (CL.denote (active_program indices pc tail)) A m \o rho) <=
    V (global_config pc (Some m) rho).
Proof.
elim: indices=>[|i indices IH] /=.
- move=>_ pc tail A HK m rho Hinv; exact: HK Hinv.
- move=>/andP[Hi HU] pc tail A HK m rho Hinv.
  case Ei: (pc i)=>[s| |].
  + have Hs : statement_wf s.
      have H := (proj2 (proj1 Hinv)) i.
      by move: H; rewrite /= Ei=>[][Hs _].
    have HE u r : lift_local p pc i (local_config s (Some u) r) =
        global_config pc (Some u) r.
      rewrite (lift_local_start _ _ _ _ _ Hs) -Ei replace_current; by [].
    change (\Tr (wp (slet (CL.denote (translate_statement s))
      (CL.denote (active_program indices pc tail))) A m \o rho) <=
      V (global_config pc (Some m) rho)).
    rewrite wp_sequence -HE.
    apply: (@translated_local_stopping P pc i V
      (wp (CL.denote (active_program indices pc tail)) A)
      Vnonnegative Vbounded Vstep _ s m rho).
    * move=>u r Hend.
      rewrite lift_local_finished in Hend *.
      rewrite -(@active_program_replace n pc indices i (idle_control (p i)) tail Hi).
      rewrite /finish_one Ei in HK.
      exact: (IH HU (replace pc i (idle_control (p i))) tail A HK u r Hend).
    * by rewrite HE.
  + change (\Tr (wp (slet skip_sem
      (CL.denote (active_program indices pc tail))) A m \o rho) <=
      V (global_config pc (Some m) rho)).
    rewrite slet1l; rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail A HK m rho Hinv).
  + change (\Tr (wp (slet skip_sem
      (CL.denote (active_program indices pc tail))) A m \o rho) <=
      V (global_config pc (Some m) rho)).
    rewrite slet1l; rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail A HK m rho Hinv).
Qed.
Corollary active_commands_stopping indices : uniq indices -> forall pc (A : assertion),
  (forall m rho,
    serial_invariant P (global_config (finish_controls p indices pc) (Some m) rho) ->
    \Tr (A m \o rho) <= V (global_config (finish_controls p indices pc) (Some m) rho)) ->
  forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
  \Tr (wp (CL.denote (active_program indices pc CL.Skip)) A m \o rho) <=
    V (global_config pc (Some m) rho).
Proof.
move=>HU pc A Hend m rho Hinv.
apply: (@active_program_stopping indices HU pc CL.Skip A _ m rho Hinv).
move=>u r Hr; rewrite wp_skip; exact: Hend Hr.
Qed.
End Stopping.
End DistributedActiveStopping.
