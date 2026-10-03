(* Deterministic certificates for the actual nested phase-estimation loops. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From mathcomp.analysis Require Import exp trigo.
From quantum Require Import qtype.
From quantum.example.classical Require Import language deterministic algorithm_loops
  indexed_loops algorithm_semantics predicate phase_estimation phase_program.

Module ClassicalPhaseExecution.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops
  ClassicalIndexedLoops ClassicalPhaseEstimation ClassicalPhaseProgram.
Import ClassicalAlgorithmSemantics CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma increment_other (x y : variable Integer) s count :
  cvname y != cvname x ->
  ((iter count (next_store y) s).[x])%M = (s.[x])%M.
Proof.
move=>Hxy; elim: count s=>[|count IH] s; first by [].
by rewrite iterSr IH /next_store get_set_nex.
Qed.

Lemma integer_le_below n :
  (fun a : int => a <= Posz n) = (fun a : int => a < Posz n.+1).
Proof.
apply/funext=>a.
by rewrite -[n.+1]addn1 PoszD ltzD1.
Qed.

Section Program.
Variable (n : nat) (T : qType).
Variable (qr : wf_qreg (QPair (QArray n QBool) T)).
Variable (U : 'FU('Ht T)).
Variable (x y : variable Integer).
Hypothesis distinct_counters : cvname y != cvname x.

Definition phase_body :=
  Sequence (indexed_gate (control_register qr) x (@hadamard_at n))
  (Sequence (Assign y (EConst (0 : int)))
  (Sequence (phase_inner qr U x y) (Assign x (increment x)))).

Definition phase_next j s :=
  next_store x (iter (2 ^ (n - j)) (next_store y) (s.[y <- (0 : int)])%M).

Definition phase_action j (_ : store) : 'SO(Hq) :=
  if one_based_index n (Posz j) is Some i then
    superop_power (liftfso (formso (tf2f qr qr (controlled_at U i)))) (2 ^ (n - j)) :o
      liftfso (formso (tf2f (control_register qr) (control_register qr) (hadamard_at i)))
  else \:1.

Lemma phase_next_counter j s : (s.[x])%M = Posz j ->
  ((phase_next j s).[x])%M = Posz j.+1.
Proof.
move=>Hx; apply: next_store_value.
by rewrite increment_other // get_set_nex.
Qed.

Lemma phase_body_execution (i : 'I_n) s :
  (s.[x])%M = Posz i.+1 ->
  execution phase_body s (phase_next i.+1 s) (phase_action i.+1 s).
Proof.
move=>Hx.
have Hx0 : ((s.[y <- (0 : int)]).[x])%M = Posz i.+1.
  by rewrite get_set_nex.
have Hy0 : ((s.[y <- (0 : int)]).[y])%M = Posz 0 by rewrite get_set_eq.
have Dloop := @phase_inner_execution n T qr U x y i (2 ^ (n - i.+1)) 0
  (s.[y <- (0 : int)])%M distinct_counters Hx0 Hy0 (add0n _).
have Dhad := @indexed_gate_execution _ n (control_register qr) x
  (@hadamard_at n) i s Hx.
have D := RunSequence Dhad
  (RunSequence (RunAssign y (EConst (0 : int)) s)
    (RunSequence Dloop (RunAssign x (increment x) _))).
rewrite comp_so1l comp_so1r in D.
rewrite /phase_action one_based_indexE.
exact: D.
Qed.

Lemma phase_outer_execution s : (s.[x])%M = Posz 1 ->
  execution (phase_outer qr U x y) s (final_store phase_next 1 n s)
    (accumulated_action phase_next phase_action 1 n s).
Proof.
move=>Hx; rewrite /phase_outer integer_le_below.
change (execution (While (below x n.+1) phase_body) s
  (final_store phase_next 1 n s)
  (accumulated_action phase_next phase_action 1 n s)).
rewrite -[n.+1]add1n.
apply: indexed_loop_execution Hx _ _.
- move=>[|j] t /andP[Hlow Hhigh] Ht; first by rewrite leqn0 in Hlow.
  have Hj : (j < n)%N by move: Hhigh; rewrite add1n ltnS.
  exact: (@phase_body_execution (Ordinal Hj) t Ht).
- move=>j t _ Ht; exact: phase_next_counter Ht.
Qed.

Variable Uu : 'FU('Ht T).

Definition phase_final_store s :=
  final_store phase_next 1 n (s.[x <- (1 : int)])%M.

Definition phase_prefix_action s : 'SO(Hq) :=
  (((liftfso (formso (tf2f (control_register qr) (control_register qr)
      (tuple_fourier n)^A)) :o
    accumulated_action phase_next phase_action 1 n (s.[x <- (1 : int)])%M) :o
    liftfso (initialso (tv2v (control_register qr) (zero_state (QArray n QBool))))) :o
    liftfso (formso (tf2f (target_register qr) (target_register qr) Uu))) :o
    liftfso (initialso (tv2v (target_register qr) (zero_state T))).

Lemma phase_prefix_execution s :
  execution (phase_prefix qr U Uu x y) s (phase_final_store s)
    (phase_prefix_action s).
Proof.
have Hx : ((s.[x <- (1 : int)]).[x])%M = Posz 1 by rewrite get_set_eq.
have Dloop := phase_outer_execution Hx.
have D := RunSequence (RunInitialize (target_register qr) (EConst (zero_state T)) s)
  (RunSequence (RunUnitary (target_register qr) (EConst Uu) s)
  (RunSequence (RunInitialize (control_register qr) (EConst (zero_state (QArray n QBool))) s)
  (RunSequence (RunAssign x (EConst (1 : int)) s)
  (RunSequence Dloop (RunUnitary (control_register qr)
    (EConst [unitary of (tuple_fourier n)^A]) (phase_final_store s)))))).
rewrite comp_so1r in D.
exact: D.
Qed.

Lemma phase_prefix_channel s : phase_prefix_action s \is cptp.
Proof. exact: execution_channel (phase_prefix_execution s). Qed.
HB.instance Definition _ s := isQChannel.Build _ _ (phase_prefix_action s)
  (phase_prefix_channel s).

Lemma phase_prefix_denote s m :
  denote (phase_prefix qr U Uu x y) s m =
  point (phase_final_store s) (phase_prefix_action s) m.
Proof. apply: execution_denote; exact: phase_prefix_execution. Qed.

Lemma phase_prefix_pre total (Q : store -> 'FO(Hq)) s :
  (xp total (denote (phase_prefix qr U Uu x y)) Q s : 'End(Hq)) =
    (phase_prefix_action s)^*o (Q (phase_final_store s)).
Proof. apply: execution_pre; exact: phase_prefix_execution. Qed.

End Program.
End ClassicalPhaseExecution.
