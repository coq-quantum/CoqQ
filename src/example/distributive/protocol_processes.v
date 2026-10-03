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
From quantum.example.distributive Require Import language sequentialization footprint.

Module DistributedProtocolProcesses.
Import DistributedLanguage DistributedSequentialization.
Local Open Scope ring_scope.
Local Open Scope string_scope.

Definition xA : CL.variable (QType QBool) := CVar (QType QBool) "Alice" "x".
Definition zA : CL.variable (QType QBool) := CVar (QType QBool) "Alice" "z".
Definition stageA : CL.variable CL.Integer := CVar CL.Integer "Alice" "stage".
Definition xB : CL.variable (QType QBool) := CVar (QType QBool) "Bob" "x".
Definition zB : CL.variable (QType QBool) := CVar (QType QBool) "Bob" "z".
Definition stageB : CL.variable CL.Integer := CVar CL.Integer "Bob" "stage".

Definition first_register u v (q : wf_qreg (QPair u v)) : wf_qreg u :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid q)).
Definition second_register u v (q : wf_qreg (QPair u v)) : wf_qreg v :=
  WF_QReg (QRegAuto.valid_qreg_snd (qreg_is_valid q)).

Definition round_bit (i : 'I_2) := i == ord0.
Lemma round_bit_inj : injective round_bit.
Proof.
by move=>[[|[|i]] Hi] [[|[|j]] Hj] //= _; apply: val_inj.
Qed.

Definition conditional (e : expression bool) (yes no : statement) :=
  Alternative (fun i : 'I_2 =>
    CL.EApp (CL.EConst (fun b : bool => b == (round_bit i))) e)
    (fun i => if (round_bit i) then yes else no).

Lemma conditional_wf e yes no :
  statement_wf yes -> statement_wf no -> statement_wf (conditional e yes no).
Proof.
move=>Hy Hn; split.
- move=>s i j /= /eqP Ei /eqP Ej; apply: round_bit_inj.
  exact: eq_trans (esym Ei) Ej.
- by move=>i; case: ((round_bit i)).
Qed.

Definition stage_guard (stage : CL.variable CL.Integer) (i : 'I_2) :=
  CL.EApp (CL.EConst (fun k : int => k == Posz i)) (CL.EVar stage).

Lemma stage_guard_exclusive stage : exclusive (stage_guard stage).
Proof.
move=>s i j /= /eqP Ei /eqP Ej.
have E : Posz i = Posz j := eq_trans (esym Ei) Ej.
by apply: val_inj; case: E.
Qed.

Definition set_stage (stage : CL.variable CL.Integer) (i : nat) := Atomic (AAssign stage (CL.EConst (Posz i))).
Definition gate t (q : wf_qreg t) (U : 'FU('Ht t)) :=
  Atomic (AUnitary q (CL.EConst U)).
Definition measure (q : wf_qreg QBool) (x : CL.variable (QType QBool)) :=
  Atomic (AMeasure x q (CL.EConst [QM of @tmeas bool])).
Definition correct (q : wf_qreg QBool) (x : CL.variable (QType QBool))
    (U : 'FU('Hs bool)) :=
  conditional (CL.EVar x) (gate q U) (Atomic ASkip).

Lemma correct_wf q x U : statement_wf (correct q x U).
Proof. by apply: conditional_wf. Qed.

Definition two_round (init : statement) stage io body :=
  Process init (@stage_guard stage) io body.

Lemma two_round_wf init stage io body : statement_wf init ->
  (forall i, statement_wf (body i)) -> process_wf (two_round init stage io body).
Proof. by move=>Hi Hb; split=>//; split=>//; exact: stage_guard_exclusive. Qed.

Definition teleport_alice (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (gate (first_register q) [unitary of Hadamard])
    (Sequence (measure (first_register q) zA)
    (Sequence (measure (second_register q) xA) (set_stage stageA 0)))))
    stageA
    (fun i => if i == ord0 then Output "c" (CL.EVar xA) else Output "d" (CL.EVar zA))
    (fun i => set_stage stageA i.+1).

Definition teleport_bob (q : wf_qreg QBool) : process :=
  two_round (set_stage stageB 0) stageB
    (fun i => if i == ord0 then Input "c" xB else Input "d" zB)
    (fun i => Sequence (set_stage stageB i.+1)
      (if i == ord0 then correct q xB [unitary of PauliX]
       else correct q zB [unitary of PauliZ])).

Definition remote_alice (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (measure (second_register q) xA) (set_stage stageA 0))) stageA
    (fun i => if i == ord0 then Output "c" (CL.EVar xA) else Input "d" zA)
    (fun i => Sequence (set_stage stageA i.+1)
      (if i == ord0 then Atomic ASkip
       else correct (first_register q) zA [unitary of PauliZ])).

Definition remote_bob (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (gate (first_register q) [unitary of Hadamard])
    (Sequence (measure (first_register q) zB) (set_stage stageB 0)))) stageB
    (fun i => if i == ord0 then Input "c" xB else Output "d" (CL.EVar zB))
    (fun i => Sequence (set_stage stageB i.+1)
      (if i == ord0 then correct (second_register q) xB [unitary of PauliX]
       else Atomic ASkip)).

Lemma teleport_alice_wf q : process_wf (teleport_alice q).
Proof. by apply: two_round_wf=>//=; repeat split. Qed.
Lemma teleport_bob_wf q : process_wf (teleport_bob q).
Proof.
apply: two_round_wf=>//= i; split=>//.
by case: (i == ord0); apply: correct_wf.
Qed.
Lemma remote_alice_wf q : process_wf (remote_alice q).
Proof.
apply: two_round_wf; first by repeat split.
move=>i; split=>//; case: (i == ord0)=>//; exact: correct_wf.
Qed.
Lemma remote_bob_wf q : process_wf (remote_bob q).
Proof.
apply: two_round_wf; first by repeat split.
move=>i; split=>//; case: (i == ord0)=>//; exact: correct_wf.
Qed.

Lemma correct_finite q x U : finite_set (statement_reads (correct q x U)).
Proof.
rewrite /correct /conditional /=.
apply: bigcup_finite; first exact: finite_finset.
move=>i _; rewrite finite_setU; split.
- rewrite /expression_reads /CL.EApp /CL.EConst /CL.EVar /= ?set0U.
  exact: finite_set1.
- by case: ((round_bit i))=>/=; exact: finite_set0.
Qed.

Lemma two_round_finite init stage io body :
  finite_set (statement_reads init) ->
  (forall i, finite_set (communication_reads (io i))) ->
  (forall i, finite_set (statement_reads (body i))) ->
  finite_set (process_reads (two_round init stage io body)).
Proof.
move=>Hi Hio Hb; rewrite /process_reads /= finite_setU; split=>//.
apply: bigcup_finite; first exact: finite_finset.
move=>i _; rewrite !finite_setU; split; last exact: Hb.
split; last exact: Hio.
rewrite /expression_reads /stage_guard /CL.EApp /CL.EConst /CL.EVar /= ?set0U.
split; first exact: finite_set0.
exact: finite_set1.
Qed.

Lemma set_stage_finite stage i : finite_set (statement_reads (set_stage stage i)).
Proof. rewrite /set_stage /= setU0; exact: finite_set1. Qed.

Lemma gate_finite t (q : wf_qreg t) U : finite_set (statement_reads (gate q U)).
Proof. exact: finite_set0. Qed.

Lemma measure_finite q x : finite_set (statement_reads (measure q x)).
Proof. rewrite /measure /= setU0; exact: finite_set1. Qed.

Lemma teleport_alice_finite q : finite_set (process_reads (teleport_alice q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; exact: set_stage_finite.
Qed.

Lemma teleport_bob_finite q : finite_set (process_reads (teleport_bob q)).
Proof.
apply: two_round_finite; first exact: set_stage_finite.
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: correct_finite].
Qed.

Lemma remote_alice_finite q : finite_set (process_reads (remote_alice q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: correct_finite].
Qed.

Lemma remote_bob_finite q : finite_set (process_reads (remote_bob q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: correct_finite].
Qed.

End DistributedProtocolProcesses.
