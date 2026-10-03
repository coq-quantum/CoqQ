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

From quantum.example.distributive Require Import protocol_execution protocol_quantum protocol_suffix.

From quantum.example.classical Require Import rules primitive.


Module DistributedProtocolRemoteSerial.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQRules CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition remote_tail qa qb :=
  CL.Sequence (CL.Assign stageB (CL.EConst (0 : int)))
    (CL.Sequence CL.Skip (remote_loop_suffix qa qb)).

Lemma remote_tail_execution qa qb s : (s.[stageA])%M = (0 : int) ->
  execution (remote_tail qa qb) s (remote_final_store (s.[stageB <- (0 : int)])%M)
    (remote_loop_action qa qb (s.[stageB <- (0 : int)])%M).
Proof.
move=>Ha.
have Hs : synchronized_at (s.[stageB <- (0 : int)])%M 0.
  split; last exact: get_set_eq.
  by rewrite get_set_nex.
have D := RunSequence (RunAssign stageB (CL.EConst (0 : int)) s)
  (RunSequence (RunSkip _) (remote_loop_suffix_execution qa qb Hs)).
rewrite !comp_so1r in D; exact: D.
Qed.

Definition remote_serial (qa qb : wf_qreg (QPair QBool QBool)) :=
  CL.Sequence (CL.Unitary qa (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Measure xA (second_register qa) (CL.EConst [QM of @tmeas bool]))
  (CL.Sequence (CL.Assign stageA (CL.EConst (0 : int)))
  (CL.Sequence (CL.Unitary qb (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Unitary (first_register qb) (CL.EConst [unitary of Hadamard]))
  (CL.Sequence (CL.Measure zB (first_register qb) (CL.EConst [QM of @tmeas bool]))
    (remote_tail qa qb)))))).

Lemma remote_serial_preE total qa qb Q :
  pre total (successful_sequentialize (paired (remote_alice qa) (remote_bob qb))) Q =
    pre total (remote_serial qa qb) Q.
Proof.
rewrite /successful_sequentialize /sequentialize remote_rendezvousE enum_two /=.
rewrite /paired /= /remote_serial /remote_tail /remote_loop_suffix /two_round_loop.
rewrite !pre_sequence.
by [].
Qed.

End DistributedProtocolRemoteSerial.
