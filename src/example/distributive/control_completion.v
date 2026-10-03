(* Readiness after completing every listed active process. *)
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

From quantum.example.distributive Require Import active_lower.

Module DistributedControlCompletion.
Import DistributedLanguage DistributedOperational DistributedSerialScheduler
  DistributedActiveLower.

Definition control_ready (c : control) := c = Waiting \/ c = Stopped.

Lemma idle_ready p : control_ready (idle_control p).
Proof. rewrite /idle_control /after_local; case: branch_count=>[|n]; by [right|left]. Qed.

Lemma finish_one_ready n (p : 'I_n -> process) pc i j :
  control_ready (pc j) -> control_ready (finish_one p pc i j).
Proof.
move=>H; rewrite /finish_one; case: (pc i)=>[s| |] //.
rewrite /replace; case: (j == i); first exact: idle_ready.
exact: H.
Qed.

Lemma finish_one_self_ready n (p : 'I_n -> process) pc i :
  control_ready (finish_one p pc i i).
Proof.
rewrite /finish_one; case Ei: (pc i)=>[s| |].
- rewrite replace_same; exact: idle_ready.
- by left.
- by right.
Qed.

Lemma finish_controls_ready_at n (p : 'I_n -> process) indices pc j :
  control_ready (pc j) \/ j \in indices ->
  control_ready (finish_controls p indices pc j).
Proof.
elim: indices pc=>[|i indices IH] pc /=.
- by case=>[H|].
- case=>[H|Hmem].
  + apply: IH; left; exact: finish_one_ready H.
  + move: Hmem; rewrite inE=>/orP[/eqP E|Hj].
    * subst j; apply: IH; left; exact: finish_one_self_ready.
    * apply: IH; by right.
Qed.

Lemma finish_controls_ready n (p : 'I_n -> process) pc :
  ready (finish_controls p (enum 'I_n) pc).
Proof.
move=>j; apply: finish_controls_ready_at; right; by rewrite mem_enum.
Qed.

End DistributedControlCompletion.
