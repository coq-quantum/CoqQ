(* Ordered active controls after a rendezvous. *)
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
From quantum.example.distributive Require Import language operational sequentialization guarded_rules residual_semantics serial_scheduler.
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



From quantum.example.distributive Require Import active_pairs active_lower control_completion.

Module DistributedRankingControls.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedResidualSemantics DistributedSerialScheduler DistributedActivePairs
  DistributedActiveLower DistributedControlCompletion.

Definition completed_control (p : process) (c : control) :=
  if c is Executing _ then idle_control p else c.

Lemma completed_ready p c : control_ready c -> completed_control p c = c.
Proof. by case=>->. Qed.
Lemma completed_idle p : completed_control p (idle_control p) = idle_control p.
Proof. apply: completed_ready; exact: idle_ready. Qed.

Lemma finish_one_completed n (p : 'I_n -> process) pc i j :
  completed_control (p j) (finish_one p pc i j) = completed_control (p j) (pc j).
Proof.
rewrite /finish_one; case Ei: (pc i)=>[s| |] //.
rewrite /replace; case Eji: (j == i)=>//.
move/eqP: Eji=>E; subst j; by rewrite Ei /= completed_idle.
Qed.

Lemma finish_controls_completed n (p : 'I_n -> process) indices pc j :
  completed_control (p j) (finish_controls p indices pc j) =
  completed_control (p j) (pc j).
Proof.
elim: indices pc=>[|i indices IH] pc //=.
by rewrite IH finish_one_completed.
Qed.

Lemma finish_controls_idle n (p : 'I_n -> process) pc :
  (forall j, completed_control (p j) (pc j) = idle_control (p j)) ->
  finish_controls p (enum 'I_n) pc = (fun j => idle_control (p j)).
Proof.
move=>H; apply/funext=>j.
rewrite -(@completed_ready (p j) _ (finish_controls_ready p pc j)).
by rewrite finish_controls_completed H.
Qed.

Lemma finish_active_pair n (p : 'I_n -> process) i k s t :
  finish_controls p (enum 'I_n)
    (replace (replace (fun j => idle_control (p j)) i (Executing s)) k (Executing t)) =
    (fun j => idle_control (p j)).
Proof.
apply: finish_controls_idle=>j; rewrite /replace.
case: (j == k)=>//; case: (j == i)=>//; exact: completed_idle.
Qed.

Theorem active_program_pair n (pc : 'I_n -> control) (i k : 'I_n) s t tail :
  ready pc -> (i < k)%N ->
  CL.denote (active_program (enum 'I_n)
    (replace (replace pc i (Executing s)) k (Executing t)) tail) =
  CL.denote (CL.Sequence (translate_statement s)
    (CL.Sequence (translate_statement t) tail)).
Proof.
move=>Hready Hik.
have Hneq : i != k by apply/eqP=>E; subst k; move: Hik; rewrite ltnn.
have HF j : j \in enum 'I_n -> ~~ pred2 i k j ->
    control_command (replace (replace pc i (Executing s)) k (Executing t) j) = CL.Skip.
  move=>_; rewrite /pred2 /= negb_or=>/andP[Hji Hjk].
  rewrite (replace_other _ _ Hjk) (replace_other _ _ Hji).
  case: (Hready j)=>->; by [].
rewrite (@active_program_filter n _ _ _ (pred2 i k) HF).
have Ho : (index i (enum 'I_n) < index k (enum 'I_n))%N by rewrite !index_enum_ord.
have Hi : i \in enum 'I_n by rewrite mem_enum.
have Hk : k \in enum 'I_n by rewrite mem_enum.
rewrite (filter_pair_order (enum_uniq _) Hi Hk Ho).
change (CL.denote (CL.Sequence
  (control_command (replace (replace pc i (Executing s)) k (Executing t) i))
  (CL.Sequence (control_command (replace (replace pc i (Executing s)) k (Executing t) k)) tail)) =
  CL.denote (CL.Sequence (translate_statement s) (CL.Sequence (translate_statement t) tail))).
by rewrite (replace_other _ _ Hneq) !replace_same.
Qed.

End DistributedRankingControls.
