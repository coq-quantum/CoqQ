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


From quantum.example.distributive Require Import distribution weighted local_actions progress residual_semantics local_correspondence.

Module DistributedLocalHarmonic.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedDistribution DistributedWeighted DistributedLocalActions DistributedProgress
  DistributedResidualSemantics DistributedLocalCorrespondence.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma future_residual_lift n (p : 'I_n -> process) pc i tail :
  (forall t, CL.denote (residual_command p (replace pc i (after_local (p i) t))) =
    CL.denote (CL.Sequence (translate_statement t) tail)) ->
  forall d out, d.2 \is denlf ->
    residual_state p (lift_local p pc i d) out = future (CL.denote tail) d out.
Proof.
move=>Hfocus [[s [m|]] rho] out Hr; last by [].
rewrite /lift_local residual_stateE // Hfocus /future /=.
by [].
Qed.

Theorem residual_local_harmonic n (p : 'I_n -> process) pc m rho i s out :
  statement_wf s -> rho \is den1lf -> first_active (enum 'I_n) pc = Some (i,s) ->
  residual_state p (global_config pc (Some m) rho) out =
    weighted_sum (fmap (lift_local p pc i) (local_successor s m rho))
      (fun c => residual_state p c out).
Proof.
move=>Hs Hr Hfirst; have [tail [Hsource Hfocus]] := residual_local_focus p Hfirst.
rewrite residual_stateE ?den1lf_den // Hsource.
apply: (eq_trans (@local_future_harmonic s m rho (CL.denote tail) out Hs Hr)).
apply: eq_sum=>a; congr (_ *: _).
symmetry; apply: (@future_residual_lift n p pc i tail Hfocus _ out).
apply: den1lf_den; exact: (local_step_normalized (local_successor_step Hs m rho) Hr a).
Qed.

End DistributedLocalHarmonic.
