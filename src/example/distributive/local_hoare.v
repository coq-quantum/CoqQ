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
From quantum.example.distributive Require Import language sequentialization guarded_rules.
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


From quantum.example.distributive Require Import local_iterations local_iteration_limits.

Module DistributedLocalHoare.
Import DistributedLanguage DistributedSequentialization DistributedLocalIterations
  DistributedLocalIterationLimits CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition run s (rho : @CQState.state cmem Hq) :=
  CQKernel.apply (sem_lim (fun k => local_iter k s)) rho.

Theorem run_translate s rho : statement_wf s ->
  run s rho = CQHoare.run (translate_statement s) rho.
Proof. move=>Hs; by rewrite /run (local_iter_limit (or_intror Hs)). Qed.

Definition valid total (P : assertion) s Q :=
  forall rho : @CQState.state cmem Hq,
  if total then expect P rho <= expect Q (run s rho)
  else expect (complement Q) (run s rho) <= expect (complement P) rho.

Theorem valid_translate_iff total P s Q : statement_wf s ->
  (valid total P s Q <-> CQHoare.valid total P (translate_statement s) Q).
Proof.
move=>Hs; split=>H rho; have Hpoint := H rho.
- by rewrite (run_translate rho Hs) in Hpoint.
- by rewrite (run_translate rho Hs).
Qed.

Theorem derives_sound total P s Q : statement_wf s ->
  DistributedGuardedRules.derives total P s Q -> valid total P s Q.
Proof.
move=>Hs D; apply/(proj2 (@valid_translate_iff total P s Q Hs)).
exact: DistributedGuardedRules.derives_translate_sound D.
Qed.

Theorem derives_complete total P s Q : statement_wf s ->
  valid total P s Q -> DistributedGuardedRules.derives total P s Q.
Proof.
move=>Hs H; exact: (@DistributedGuardedRules.derives_translate_complete total P s Q Hs
  (proj1 (@valid_translate_iff total P s Q Hs) H)).
Qed.

Theorem sound_complete total P s Q : statement_wf s ->
  (DistributedGuardedRules.derives total P s Q <-> valid total P s Q).
Proof. move=>Hs; split; [exact: derives_sound Hs | exact: derives_complete Hs]. Qed.

End DistributedLocalHoare.
