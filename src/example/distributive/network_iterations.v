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

From quantum.example.classical Require Import bounded_unroll bounded_limits.
From quantum.example.distributive Require Import rendezvous_harmonic local_iterations.

Module DistributedNetworkIterations.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedSerialScheduler DistributedResidualSemantics DistributedBoundarySemantics
  DistributedRendezvousHarmonic DistributedLocalIterations ClassicalBoundedUnroll ClassicalBoundedLimits.
Local Notation Hq := 'H[msys]_finset.setT.

Definition network_iter n (p : 'I_n -> process) k : CL.kernel :=
  slet (CL.denote (CL.unroll
    (guards_any [seq bc.1 | bc <- rendezvous_commands p])
    (conditional_chain (rendezvous_commands p)) k))
    (CL.denote (CL.Conditional (termination_guard p) CL.Skip CL.Abort)).

Lemma network_iter0 n (p : 'I_n -> process) : network_iter p 0 = abort_sem.
Proof. exact: slet_abort_left. Qed.

Lemma network_iterS n (p : 'I_n -> process) k m :
  network_iter p k.+1 m =
  if eval (guards_any [seq bc.1 | bc <- rendezvous_commands p]) m then
    slet (CL.denote (conditional_chain (rendezvous_commands p))) (network_iter p k) m
  else CL.denote (CL.Conditional (termination_guard p) CL.Skip CL.Abort) m.
Proof.
rewrite /network_iter.
pose B := guards_any [seq bc.1 | bc <- rendezvous_commands p].
pose C := conditional_chain (rendezvous_commands p).
pose T := CL.Conditional (termination_guard p) CL.Skip CL.Abort.
change (slet (CL.denote (CL.Conditional B (CL.Sequence C (CL.unroll B C k)) CL.Skip))
  (CL.denote T) m = if eval B m then
  slet (CL.denote C) (slet (CL.denote (CL.unroll B C k)) (CL.denote T)) m
  else CL.denote T m).
case E: (eval B m).
- have H : CL.denote (CL.Conditional B (CL.Sequence C (CL.unroll B C k)) CL.Skip) m =
      slet (CL.denote C) (CL.denote (CL.unroll B C k)) m.
    by rewrite CL.denote_conditional E.
  by rewrite (slet_row_eq _ H) sletA.
- have H : CL.denote (CL.Conditional B (CL.Sequence C (CL.unroll B C k)) CL.Skip) m = skip_sem m.
    by rewrite CL.denote_conditional E.
  by rewrite (slet_row_eq _ H) slet1l.
Qed.

Lemma network_iter_selected n (p : 'I_n -> process) k m a g c :
  first_enabled (rendezvous_indices p) m = Some a -> index_command a = Some (g,c) ->
  network_iter p k.+1 m = slet (CL.denote c) (network_iter p k) m.
Proof.
move=>Hfirst Ha; rewrite network_iterS (selected_loop_guard Hfirst).
have [g' [c' [Ha' [Hg' Hchain]]]] := selected_rendezvous_command Hfirst.
rewrite Ha in Ha'; case: Ha'=>[= Eg Ec]; subst g' c'.
exact: slet_row_eq Hchain.
Qed.

Lemma network_iter_blocked n (p : 'I_n -> process) k m :
  no_rendezvous p m -> network_iter p k.+1 m =
    if term p m then skip_sem m else abort_sem m.
Proof.
move=>H; by rewrite network_iterS (no_rendezvous_loop_guard H)
  CL.denote_conditional eval_termination_guard.
Qed.

Lemma network_iter_chain n (p : 'I_n -> process) : kernel_chain (network_iter p).
Proof.
move=>m j k Hjk; apply: slet_mono _ (kernel_le_refl _) m.
move=>u; rewrite !CL.denote_unroll; exact: while_sem_iter_homo Hjk.
Qed.

Lemma network_iter_limit n (p : 'I_n -> process) :
  sem_lim (network_iter p) = CL.denote (network_tail p).
Proof.
pose B := guards_any [seq bc.1 | bc <- rendezvous_commands p].
pose C := conditional_chain (rendezvous_commands p).
pose T := CL.Conditional (termination_guard p) CL.Skip CL.Abort.
have E : (fun k => slet (CL.denote (CL.unroll B C k)) (CL.denote T)) =
    (fun k => slet (while_sem_iter (CL.translate_expr B) (CL.denote C) k) (CL.denote T)).
  by apply/funext=>k; rewrite CL.denote_unroll.
change (sem_lim (fun k => slet (CL.denote (CL.unroll B C k)) (CL.denote T)) =
  slet (while_sem (CL.translate_expr B) (CL.denote C)) (CL.denote T)).
rewrite E; apply: slet_liml=>m; exact: while_sem_iter_homo.
Qed.

Theorem network_iter_least_output n (p : 'I_n -> process) m out rho V :
  (forall k, network_iter p k m out rho ⊑ V) ->
  CL.denote (network_tail p) m out rho ⊑ V.
Proof.
move=>HV; have C := @sem_limit_cvg (network_iter p) (network_iter_chain p) m.
rewrite network_iter_limit in C.
have Cp : network_iter p k m out @[k --> \oo] --> CL.denote (network_tail p) m out.
  apply: summableE_cvg; exact: C.
have Cr : network_iter p k m out rho @[k --> \oo] --> CL.denote (network_tail p) m out rho.
  exact: so_cvgl Cp.
have L := limn_lev (cvgP _ Cr) HV.
by rewrite (cvg_lim (@norm_hausdorff _ _) Cr) in L.
Qed.

End DistributedNetworkIterations.
