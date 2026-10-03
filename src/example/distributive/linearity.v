(* Operational linearity for distributed programs. See classical/STATE_NOTES.md. *)
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
From quantum.example.classical Require Import state language kernel mixture
  kernel_linearity hoare.
From quantum.example.distributive Require Import language sequentialization
  operational_hoare.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.

Module DistributedLinearity.
Import DistributedLanguage DistributedSequentialization DistributedHoare.
Local Notation Hq := 'H[msys]_finset.setT.
Section Programs.
Context {A : choiceType}.
Variable S : program.

Definition weighted_run (w : A -> C) (d : A -> @CQState.state cmem Hq) a :
  {summable cmem -> 'End(Hq)} :=
  w a *: (run S (d a) : {summable cmem -> 'End(Hq)}).

Lemma weighted_runE w d : weighted_run w d =
  CQKernelLinearity.weighted_output
    (ClassicalLanguage.denote (successful_sequentialize (processes S))) w d.
Proof. by apply/funext=>a; rewrite /weighted_run run_translate. Qed.

Theorem run_weighted_summable w d :
  summable (CQKernelLinearity.weighted_input w d) ->
  summable (weighted_run w d).
Proof.
rewrite weighted_runE; exact: CQKernelLinearity.weighted_output_summable.
Qed.

Theorem run_weighted_sum w d (d0 : @CQState.state cmem Hq) :
  summable (CQKernelLinearity.weighted_input w d) ->
  (d0 : {summable cmem -> 'End(Hq)}) =
    sum (CQKernelLinearity.weighted_input w d) ->
  (run S d0 : {summable cmem -> 'End(Hq)}) = sum (weighted_run w d).
Proof.
rewrite run_translate weighted_runE /CQHoare.run.
exact: CQKernelLinearity.apply_weighted_sum.
Qed.

Theorem run_mix (w : Distr A) (d : A -> @CQState.state cmem Hq) :
  run S (CQStateMixture.mix w d) = CQStateMixture.mix w (fun a => run S (d a)).
Proof.
rewrite run_translate /CQHoare.run CQKernelLinearity.apply_mix.
congr (CQStateMixture.mix w _); apply/funext=>a.
by rewrite run_translate.
Qed.
End Programs.
End DistributedLinearity.
