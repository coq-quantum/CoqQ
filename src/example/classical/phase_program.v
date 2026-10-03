(* The actual nested-While PE program from classical.pdf, Section 7.3.
   Invalid dynamic register indices abort, as in the paper syntax sugar. *)
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
  indexed_loops fourier phase_estimation.

Module ClassicalPhaseProgram.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops
  ClassicalIndexedLoops ClassicalPhaseEstimation.

Section Program.
Variable (n : nat) (T : qType).
Variable (qr : wf_qreg (QPair (QArray n QBool) T)).
Variable (U Uu : 'FU('Ht T)).

Definition control_register : wf_qreg (QArray n QBool) :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid qr)).
Definition target_register : wf_qreg T :=
  WF_QReg (QRegAuto.valid_qreg_snd (qreg_is_valid qr)).

Definition controlled_at (i : 'I_n) : 'FU('Ht (QPair (QArray n QBool) T)) :=
  [unitary of Multiplexer (fun bs : n.-tuple bool =>
    if bs~_i then U else (\1 : 'FU('Ht T)))].

Definition hadamard_at (i : 'I_n) : 'FU('Ht (QArray n QBool)) :=
  ClassicalFourier.single_hadamard i.

Definition phase_inner_guard (x y : variable Integer) : bool_expr :=
  EApp (EApp (EConst (fun a b : int => b < Posz (2 ^ (n - absz a))))
    (EVar x)) (EVar y).

Definition phase_inner (x y : variable Integer) :=
  While (phase_inner_guard x y)
    (Sequence (indexed_gate qr x controlled_at) (Assign y (increment y))).

Lemma phase_inner_execution (x y : variable Integer) (i : 'I_n) count k s :
  cvname y != cvname x ->
  (s.[x])%M = Posz i.+1 -> (s.[y])%M = Posz k ->
  (k + count = 2 ^ (n - i.+1))%N ->
  execution (phase_inner x y) s (iter count (next_store y) s)
    (superop_power (liftfso (formso (tf2f qr qr (controlled_at i)))) count).
Proof.
elim: count k s=>[|count IH] k s Hxy Hx Hy Ebound.
- rewrite /phase_inner /=; apply: RunWhileFalse.
  by rewrite /phase_inner_guard /eval /= Hx Hy -Ebound addn0 ltxx.
- have Hb : eval (phase_inner_guard x y) s = true.
    by rewrite /phase_inner_guard /eval /= Hx Hy -Ebound
      ltz_nat addnS ltnS leq_addr.
  have Dgate := @indexed_gate_execution _ _ qr x controlled_at i s Hx.
  have Dbody := RunSequence Dgate (RunAssign y (increment y) s).
  rewrite comp_so1l in Dbody.
  have Hx' : ((next_store y s).[x])%M = Posz i.+1.
    by rewrite /next_store get_set_nex.
  have Hy' := next_store_value Hy.
  have Ebound' : (k.+1 + count = 2 ^ (n - i.+1))%N.
    by rewrite addSn -addnS Ebound.
  have Dtail := IH k.+1 (next_store y s) Hxy Hx' Hy' Ebound'.
  rewrite /phase_inner iterSr /=.
  exact: (RunWhileTrue Hb Dbody Dtail).
Qed.

Definition phase_outer (x y : variable Integer) :=
  While (EApp (EConst (fun a : int => a <= Posz n)) (EVar x))
    (Sequence (indexed_gate control_register x hadamard_at)
    (Sequence (Assign y (EConst (0 : int)))
    (Sequence (phase_inner x y) (Assign x (increment x))))).

Definition phase_prefix (x y : variable Integer) :=
  Sequence (Initialize target_register (EConst (zero_state T)))
  (Sequence (Unitary target_register (EConst Uu))
  (Sequence (Initialize control_register (EConst (zero_state (QArray n QBool))))
  (Sequence (Assign x (EConst (1 : int)))
  (Sequence (phase_outer x y)
    (Unitary control_register (EConst [unitary of (tuple_fourier n)^A])))))).

Definition phase_estimation (x y : variable Integer)
    (z : variable (QType (QArray n QBool))) :=
  Sequence (phase_prefix x y)
    (Measure z control_register (EConst [QM of @tmeas (eval_qtype (QArray n QBool))])).

End Program.
End ClassicalPhaseProgram.
