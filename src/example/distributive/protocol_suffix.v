(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum Require Import qtype.
From quantum.example.classical Require Import deterministic algorithm_semantics predicate.
From quantum.example.distributive Require Import language sequentialization protocol_processes.

From quantum.example.distributive Require Import protocol_execution protocol_quantum.

Module DistributedProtocolSuffix.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolQuantum.
Import ClassicalDeterministic ClassicalAlgorithmSemantics.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma execution_preE total c s t F (Q : CL.store -> 'FO(Hq)) :
  execution c s t F ->
  (CQPredicate.xp total (CL.denote c) Q s : 'End(Hq)) = F^*o (Q t).
Proof.
move=>D; have HF := execution_channel D.
rewrite (QChannel_BuildE HF) in D *.
exact: (execution_pre total Q D).
Qed.

Lemma teleport_terminationE qa qb s : synchronized_at s 2 ->
  eval (termination_guard (paired (teleport_alice qa) (teleport_bob qb))) s = true.
Proof.
move=>[Ea Eb].
rewrite /termination_guard !enum_two /= /paired /= !enum_two /=.
by rewrite /guards_all /guard_and /guard_not /stage_guard /= Ea Eb.
Qed.

Lemma remote_terminationE qa qb s : synchronized_at s 2 ->
  eval (termination_guard (paired (remote_alice qa) (remote_bob qb))) s = true.
Proof.
move=>[Ea Eb].
rewrite /termination_guard !enum_two /= /paired /= !enum_two /=.
by rewrite /guards_all /guard_and /guard_not /stage_guard /= Ea Eb.
Qed.

Definition remote_step_store (i : 'I_2) (s : CL.store) :=
  ((s.[(if i == ord0 then xB else zA) <-
       (s.[(if i == ord0 then xA else zB)])]).[stageA <- Posz i.+1]).[stageB <- Posz i.+1]%M.

Definition remote_step_action (qa qb : wf_qreg (QPair QBool QBool))
    (i : 'I_2) (s : CL.store) :=
  if i == ord0 then correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M
  else correction_action (first_register qa) [unitary of PauliZ] (s.[zB])%M.

Lemma remote_step_synchronized i s :
  synchronized_at (remote_step_store i s) i.+1.
Proof.
split; rewrite /remote_step_store; last exact: get_set_eq.
by rewrite get_set_nex // get_set_eq.
Qed.

Lemma remote_step_execution qa qb i s :
  execution (remote_rendezvous qa qb i).2 s (remote_step_store i s)
    (remote_step_action qa qb i s).
Proof.
rewrite /remote_rendezvous /remote_step_action /remote_step_store /=.
case Ei: (i == ord0).
- have D := RunSequence (RunAssign xB (CL.EVar xA) s)
    (RunSequence
      (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _) (RunSkip _))
      (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
        (correct_execution (second_register qb) xB [unitary of PauliX] _))).
  rewrite !comp_so1l !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
- have D := RunSequence (RunAssign zA (CL.EVar zB) s)
    (RunSequence
      (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
        (correct_execution (first_register qa) zA [unitary of PauliZ] _))
      (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _) (RunSkip _))).
  rewrite !comp_so1l !comp_so1r get_set_nex // get_set_eq in D.
  exact: D.
Qed.

Definition remote_final_store s :=
  remote_step_store round_one (remote_step_store ord0 s).

Definition remote_loop_action qa qb s :=
  remote_step_action qa qb round_one (remote_step_store ord0 s) :o
    remote_step_action qa qb ord0 s.

Lemma remote_loop_execution qa qb s : synchronized_at s 0 ->
  execution (two_round_loop (remote_rendezvous qa qb)) s
    (remote_final_store s) (remote_loop_action qa qb s).
Proof.
move=>Hs; apply: two_round_loop_execution.
- exact: synchronized_guardE Hs.
- exact: synchronized_guardE (remote_step_synchronized ord0 s).
- exact: synchronized_guardE (remote_step_synchronized ord0 s).
- exact: synchronized_guardE (remote_step_synchronized round_one _).
- exact: synchronized_guardE (remote_step_synchronized round_one _).
- exact: remote_step_execution.
- exact: remote_step_execution.
Qed.

Lemma remote_loop_actionE qa qb s :
  remote_loop_action qa qb s =
    correction_action (first_register qa) [unitary of PauliZ] (s.[zB])%M :o
    correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M.
Proof.
change (correction_action (first_register qa) [unitary of PauliZ]
    ((remote_step_store ord0 s).[zB])%M :o
    correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M =
    correction_action (first_register qa) [unitary of PauliZ] (s.[zB])%M :o
    correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M).
by rewrite /remote_step_store !get_set_nex.
Qed.

Definition teleport_loop_suffix qa qb :=
  CL.Sequence (two_round_loop (teleport_rendezvous qb))
    (CL.Conditional (termination_guard (paired (teleport_alice qa) (teleport_bob qb)))
      CL.Skip CL.Abort).

Lemma teleport_loop_suffix_execution qa qb s : synchronized_at s 0 ->
  execution (teleport_loop_suffix qa qb) s (teleport_final_store s)
    (teleport_loop_action qb s).
Proof.
move=>Hs; rewrite -(comp_so1l (teleport_loop_action qb s)).
apply: RunSequence (teleport_loop_execution qb Hs) _.
apply: RunIfTrue; last exact: RunSkip.
apply: teleport_terminationE; exact: teleport_step_synchronized.
Qed.

Definition remote_loop_suffix qa qb :=
  CL.Sequence (two_round_loop (remote_rendezvous qa qb))
    (CL.Conditional (termination_guard (paired (remote_alice qa) (remote_bob qb)))
      CL.Skip CL.Abort).

Lemma remote_loop_suffix_execution qa qb s : synchronized_at s 0 ->
  execution (remote_loop_suffix qa qb) s (remote_final_store s)
    (remote_loop_action qa qb s).
Proof.
move=>Hs; rewrite -(comp_so1l (remote_loop_action qa qb s)).
apply: RunSequence (remote_loop_execution qa qb Hs) _.
apply: RunIfTrue; last exact: RunSkip.
apply: remote_terminationE; exact: remote_step_synchronized.
Qed.

End DistributedProtocolSuffix.
