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

Module DistributedActiveLower.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant
  DistributedGlobalValue DistributedLocalLower DistributedResidual.
Local Notation Hq := 'H[msys]_finset.setT.

Definition finish_one n (p : 'I_n -> process) (pc : 'I_n -> control) i :=
  if pc i is Executing _ then replace pc i (idle_control (p i)) else pc.
Fixpoint finish_controls n (p : 'I_n -> process) (indices : seq 'I_n) pc :=
  if indices is i :: rest then finish_controls p rest (finish_one p pc i) else pc.

Section Lower.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Local Notation V := (@value P rho0).

Theorem active_program_lower indices : uniq indices ->
  forall pc tail out,
  (forall m rho,
    serial_invariant P (global_config (finish_controls p indices pc) (Some m) rho) ->
    CL.denote tail m out rho ⊑ V (global_config (finish_controls p indices pc) (Some m) rho) out) ->
  forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
  CL.denote (active_program indices pc tail) m out rho ⊑
    V (global_config pc (Some m) rho) out.
Proof.
elim: indices=>[|i indices IH] /=.
- move=>_ pc tail out HK m rho Hinv; exact: HK Hinv.
- move=>/andP[Hi HU] pc tail out HK m rho Hinv.
  case Ei: (pc i)=>[s| |].
  + have Hs : statement_wf s.
      have H := (proj2 (proj1 Hinv)) i.
      by move: H; rewrite /= Ei=>[][Hs _].
    have HE u r : lift_local p pc i (local_config s (Some u) r) =
        global_config pc (Some u) r.
      rewrite (lift_local_start _ _ _ _ _ Hs) -Ei replace_current; by [].
    change (slet (CL.denote (translate_statement s))
      (CL.denote (active_program indices pc tail)) m out rho ⊑
      V (global_config pc (Some m) rho) out).
    rewrite -HE.
    apply: (@translated_local_lower P rho0 pc i
      (CL.denote (active_program indices pc tail)) out _ s m rho Hs).
    * move=>u r Hend.
      rewrite lift_local_finished in Hend *.
      rewrite -(@active_program_replace n pc indices i (idle_control (p i)) tail Hi).
      rewrite /finish_one Ei in HK.
      exact: (IH HU (replace pc i (idle_control (p i))) tail out HK u r Hend).
    * by rewrite HE.
  + change (slet skip_sem
      (CL.denote (active_program indices pc tail)) m out rho ⊑
      V (global_config pc (Some m) rho) out).
    rewrite slet1l.
    rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail out HK m rho Hinv).
  + change (slet skip_sem
      (CL.denote (active_program indices pc tail)) m out rho ⊑
      V (global_config pc (Some m) rho) out).
    rewrite slet1l.
    rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail out HK m rho Hinv).
Qed.
End Lower.
End DistributedActiveLower.
