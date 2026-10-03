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
From quantum.example.classical Require Import deterministic algorithm_semantics.
From quantum.example.distributive Require Import language sequentialization protocol_processes.

Module DistributedProtocolExecution.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import ClassicalDeterministic ClassicalAlgorithmSemantics.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition round_one : 'I_2 := @Ordinal 2 1 (erefl true).
Lemma enum_two : enum 'I_2 = [:: ord0; round_one].
Proof.
rewrite enum_ordSl enum_ordSl enum_ord0 /=.
by congr [:: _; _]; apply: val_inj.
Qed.

Lemma different_channel_effect a b : channel a != channel b ->
  communication_effect a b = None.
Proof.
move=>H; case E: (communication_effect a b)=>[effect|] //.
have M := effect_matches E.
by case: M H=>t c x e; rewrite eqxx.
Qed.

Definition paired (alice bob : process) (i : 'I_2) :=
  if i == ord0 then alice else bob.
Definition synchronized_guard (i : 'I_2) :=
  guard_and (stage_guard stageA i) (stage_guard stageB i).

Definition teleport_rendezvous (qb : wf_qreg QBool) (i : 'I_2) : expression bool * CL.command :=
  (synchronized_guard i,
   CL.Sequence (CL.Assign (if i == ord0 then xB else zB)
     (CL.EVar (if i == ord0 then xA else zA)))
   (CL.Sequence (translate_statement (set_stage stageA i.+1))
     (translate_statement (Sequence (set_stage stageB i.+1)
       (if i == ord0 then correct qb xB [unitary of PauliX]
        else correct qb zB [unitary of PauliZ]))))).

Lemma teleport_rendezvousE qa qb :
  rendezvous_commands (paired (teleport_alice qa) (teleport_bob qb)) =
  [:: teleport_rendezvous qb ord0; teleport_rendezvous qb round_one].
Proof.
Arguments communication_effect _ _ : simpl never.
rewrite /rendezvous_commands !enum_two /= /paired /=
  /rendezvous_command /= !enum_two /=.
rewrite (matching_effect (MatchOutput "c" xB (CL.EVar xA)))
  (matching_effect (MatchOutput "d" zB (CL.EVar zA)))
  !different_channel_effect //=.
Qed.

Definition remote_rendezvous
    (qa qb : wf_qreg (QPair QBool QBool)) (i : 'I_2) : expression bool * CL.command :=
  (synchronized_guard i,
   CL.Sequence (if i == ord0 then CL.Assign xB (CL.EVar xA)
     else CL.Assign zA (CL.EVar zB))
   (CL.Sequence
     (translate_statement (Sequence (set_stage stageA i.+1)
       (if i == ord0 then Atomic ASkip
        else correct (first_register qa) zA [unitary of PauliZ])))
     (translate_statement (Sequence (set_stage stageB i.+1)
       (if i == ord0 then correct (second_register qb) xB [unitary of PauliX]
        else Atomic ASkip))))).

Lemma remote_rendezvousE qa qb :
  rendezvous_commands (paired (remote_alice qa) (remote_bob qb)) =
  [:: remote_rendezvous qa qb ord0; remote_rendezvous qa qb round_one].
Proof.
rewrite /rendezvous_commands !enum_two /= /paired /=
  /rendezvous_command /= !enum_two /=.
rewrite (matching_effect (MatchOutput "c" xB (CL.EVar xA)))
  (matching_effect (MatchInput "d" zA (CL.EVar zB))).
by rewrite /communication_effect /= /remote_rendezvous.
Qed.

Lemma correct_execution q x U s :
  execution (translate_statement (correct q x U)) s s
    (if (s.[x])%M then liftfso (formso (tf2f q q U)) else \:1).
Proof.
rewrite /correct /conditional /= enum_two /= /conditional_chain /=.
case E: ((s.[x])%M).
- apply: RunIfTrue; first by rewrite /= E.
  exact: RunUnitary.
- apply: RunIfFalse; first by rewrite /= E.
  apply: RunIfTrue; first by rewrite /= E.
  exact: RunSkip.
Qed.

Definition two_round_loop (r : 'I_2 -> expression bool * CL.command) :=
  CL.While (guards_any [:: (r ord0).1; (r round_one).1])
    (conditional_chain [:: r ord0; r round_one]).

Lemma two_round_loop_execution r s t u F G :
  eval (r ord0).1 s = true ->
  eval (r ord0).1 t = false -> eval (r round_one).1 t = true ->
  eval (r ord0).1 u = false -> eval (r round_one).1 u = false ->
  execution (r ord0).2 s t F -> execution (r round_one).2 t u G ->
  execution (two_round_loop r) s u (G :o F).
Proof.
move=>Es Et0 Et1 Eu0 Eu1 D0 D1.
have Dbody0 : execution (conditional_chain [:: r ord0; r round_one]) s t F.
  apply: RunIfTrue D0; exact: Es.
have Dbody1 : execution (conditional_chain [:: r ord0; r round_one]) t u G.
  apply: RunIfFalse Et0 _; exact: RunIfTrue Et1 D1.
have Dstop : execution (two_round_loop r) u u \:1.
  apply: RunWhileFalse; by rewrite /= /guards_any /= Eu0 Eu1.
have Dnext : execution (two_round_loop r) t u G.
  rewrite -(comp_so1l G); apply: RunWhileTrue Dbody1 Dstop.
  by rewrite /= /guards_any /= Et0 Et1.
apply: RunWhileTrue Dbody0 Dnext.
by rewrite /= /guards_any /= Es.
Qed.

Definition synchronized_at (s : CL.store) (n : nat) :=
  (s.[stageA])%M = Posz n /\ (s.[stageB])%M = Posz n.

Lemma synchronized_guardE i s n : synchronized_at s n ->
  eval (synchronized_guard i) s = (n == val i).
Proof.
move=>[Ha Hb]; rewrite /synchronized_guard /guard_and /stage_guard /= Ha Hb.
by rewrite eqz_nat andbb.
Qed.

Definition teleport_step_store (i : 'I_2) (s : CL.store) :=
  ((s.[(if i == ord0 then xB else zB) <-
       (s.[(if i == ord0 then xA else zA)])]).[stageA <- Posz i.+1]).[stageB <- Posz i.+1]%M.

Definition correction_action (q : wf_qreg QBool) (U : 'FU('Hs bool)) (b : bool) :=
  if b then liftfso (formso (tf2f q q U)) else \:1.

Definition teleport_step_action (q : wf_qreg QBool) (i : 'I_2) (s : CL.store) :=
  if i == ord0 then correction_action q [unitary of PauliX] (s.[xA])%M
  else correction_action q [unitary of PauliZ] (s.[zA])%M.

Lemma teleport_step_synchronized i s :
  synchronized_at (teleport_step_store i s) i.+1.
Proof.
split; rewrite /teleport_step_store; last exact: get_set_eq.
by rewrite get_set_nex // get_set_eq.
Qed.

Lemma teleport_step_execution qb i s :
  execution (teleport_rendezvous qb i).2 s (teleport_step_store i s)
    (teleport_step_action qb i s).
Proof.
rewrite /teleport_rendezvous /teleport_step_action /teleport_step_store /=.
case Ei: (i == ord0).
- have D := RunSequence (RunAssign xB (CL.EVar xA) s)
    (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
    (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
      (correct_execution qb xB [unitary of PauliX] _))).
  rewrite !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
- have D := RunSequence (RunAssign zB (CL.EVar zA) s)
    (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
    (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
      (correct_execution qb zB [unitary of PauliZ] _))).
  rewrite !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
Qed.

Definition teleport_final_store s :=
  teleport_step_store round_one (teleport_step_store ord0 s).

Definition teleport_loop_action qb s :=
  teleport_step_action qb round_one (teleport_step_store ord0 s) :o
    teleport_step_action qb ord0 s.

Lemma teleport_loop_execution qb s : synchronized_at s 0 ->
  execution (two_round_loop (teleport_rendezvous qb)) s
    (teleport_final_store s) (teleport_loop_action qb s).
Proof.
move=>Hs; apply: two_round_loop_execution.
- exact: synchronized_guardE Hs.
- exact: synchronized_guardE (teleport_step_synchronized ord0 s).
- exact: synchronized_guardE (teleport_step_synchronized ord0 s).
- exact: synchronized_guardE (teleport_step_synchronized round_one _).
- exact: synchronized_guardE (teleport_step_synchronized round_one _).
- exact: teleport_step_execution.
- exact: teleport_step_execution.
Qed.

Lemma teleport_loop_actionE qb s :
  teleport_loop_action qb s =
    correction_action qb [unitary of PauliZ] (s.[zA])%M :o
    correction_action qb [unitary of PauliX] (s.[xA])%M.
Proof.
change (correction_action qb [unitary of PauliZ]
    ((teleport_step_store ord0 s).[zA])%M :o
    correction_action qb [unitary of PauliX] (s.[xA])%M =
    correction_action qb [unitary of PauliZ] (s.[zA])%M :o
    correction_action qb [unitary of PauliX] (s.[xA])%M).
by rewrite /teleport_step_store !get_set_nex.
Qed.

End DistributedProtocolExecution.
