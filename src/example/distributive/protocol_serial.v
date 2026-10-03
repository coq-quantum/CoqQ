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

Module DistributedProtocolSerial.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQRules CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition stages_zero (s : CL.store) := (s.[stageA <- (0 : int)]).[stageB <- (0 : int)]%M.

Lemma stages_zero_synchronized s : synchronized_at (stages_zero s) 0.
Proof.
split; rewrite /stages_zero; last exact: get_set_eq.
by rewrite get_set_nex // get_set_eq.
Qed.

Definition teleport_tail qa qb :=
  CL.Sequence (CL.Assign stageA (CL.EConst (0 : int)))
    (CL.Sequence (CL.Sequence (CL.Assign stageB (CL.EConst (0 : int))) CL.Skip)
      (teleport_loop_suffix qa qb)).

Lemma teleport_tail_execution qa qb s :
  execution (teleport_tail qa qb) s (teleport_final_store (stages_zero s))
    (teleport_loop_action qb (stages_zero s)).
Proof.
have D := RunSequence (RunAssign stageA (CL.EConst (0 : int)) s)
  (RunSequence (RunSequence (RunAssign stageB (CL.EConst (0 : int)) _) (RunSkip _))
    (teleport_loop_suffix_execution qa qb (stages_zero_synchronized s))).
rewrite !comp_so1l !comp_so1r in D.
exact: D.
Qed.

Definition teleport_serial (qa : wf_qreg (QPair QBool QBool))
    (qb : wf_qreg QBool) :=
  CL.Sequence (CL.Unitary qa (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Unitary (first_register qa) (CL.EConst [unitary of Hadamard]))
  (CL.Sequence (CL.Measure zA (first_register qa) (CL.EConst [QM of @tmeas bool]))
  (CL.Sequence (CL.Measure xA (second_register qa) (CL.EConst [QM of @tmeas bool]))
    (teleport_tail qa qb)))).

Lemma teleport_serial_preE total qa qb Q :
  pre total (successful_sequentialize (paired (teleport_alice qa) (teleport_bob qb))) Q =
    pre total (teleport_serial qa qb) Q.
Proof.
rewrite /successful_sequentialize /sequentialize teleport_rendezvousE enum_two /=.
rewrite /paired /= /teleport_serial /teleport_tail /teleport_loop_suffix /two_round_loop.
rewrite !pre_sequence.
by [].
Qed.

End DistributedProtocolSerial.
