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
From quantum.example.distributive Require Import language sequentialization footprint protocol_processes.

Module DistributedProtocolOwnership.
Import DistributedLanguage DistributedSequentialization DistributedFootprint DistributedProtocolProcesses.
Local Open Scope ring_scope.
Local Open Scope string_scope.

Definition owned (who : string) : set classical_name := fun k => k.2.1 = who.
Definition statement_owned who s := (statement_reads s `<=` owned who)%classic.
Definition process_owned who p := (process_reads p `<=` owned who)%classic.

Lemma sequence_owned who s t : statement_owned who s -> statement_owned who t ->
  statement_owned who (Sequence s t).
Proof. by move=>Hs Ht k [H|H]; [apply: Hs|apply: Ht]. Qed.
Lemma skip_owned who : statement_owned who (Atomic ASkip).
Proof. by []. Qed.
Lemma gate_owned who t (q : wf_qreg t) U : statement_owned who (gate q U).
Proof. by []. Qed.
Lemma set_stage_owned who stage i : owned who (name_of stage) ->
  statement_owned who (set_stage stage i).
Proof. by move=>H k [->|[]]. Qed.
Lemma measure_owned who q x : owned who (name_of x) ->
  statement_owned who (measure q x).
Proof. by move=>H k [->|[]]. Qed.
Lemma correct_owned who q x U : owned who (name_of x) ->
  statement_owned who (correct q x U).
Proof.
move=>Hx k [i _ [H|H]].
- by case: H=>[[]|->].
- by move: H; rewrite /correct /conditional /=; case: (round_bit i).
Qed.

Lemma two_round_owned who init stage io body :
  statement_owned who init -> owned who (name_of stage) ->
  (forall i, (communication_reads (io i) `<=` owned who)%classic) ->
  (forall i, statement_owned who (body i)) ->
  process_owned who (two_round init stage io body).
Proof.
move=>Hi Hstage Hio Hb k [H|[i _ [[H|H]|H]]].
- exact: Hi.
- by case: H=>[[]|->].
- exact: Hio i k H.
- exact: Hb i k H.
Qed.

Lemma teleport_alice_owned q : process_owned "Alice" (teleport_alice q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned; first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- by move=>i; apply: set_stage_owned.
Qed.
Lemma teleport_bob_owned q : process_owned "Bob" (teleport_bob q).
Proof.
apply: two_round_owned=>//.
- by apply: set_stage_owned.
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; apply: sequence_owned; first by apply: set_stage_owned.
  by case: (i == ord0); apply: correct_owned.
Qed.
Lemma remote_alice_owned q : process_owned "Alice" (remote_alice q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned; first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; apply: sequence_owned; first by apply: set_stage_owned.
  by case: (i == ord0); [exact: skip_owned|apply: correct_owned].
Qed.
Lemma remote_bob_owned q : process_owned "Bob" (remote_bob q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned; first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; apply: sequence_owned; first by apply: set_stage_owned.
  by case: (i == ord0); [apply: correct_owned|exact: skip_owned].
Qed.

Lemma first_register_subset u v (q : wf_qreg (QPair u v)) :
  (mset (first_register q) \subset mset q)%SET.
Proof. rewrite mset_pairV; exact: finset.subsetUl. Qed.
Lemma second_register_subset u v (q : wf_qreg (QPair u v)) :
  (mset (second_register q) \subset mset q)%SET.
Proof. rewrite mset_pairV; exact: finset.subsetUr. Qed.

Lemma correct_quantum q x U : statement_quantum (correct q x U) \subset mset q.
Proof.
apply/bigcupsP=>i _; case: (round_bit i)=>/=;
  [exact: fintype.subxx | exact: finset.sub0set].
Qed.

Lemma teleport_alice_quantum q : process_quantum (teleport_alice q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset !fintype.subxx !finset.sub0set
  /= !first_register_subset !second_register_subset /=.
apply/bigcupsP=>i _; exact: finset.sub0set.
Qed.
Lemma teleport_bob_quantum q : process_quantum (teleport_bob q) \subset mset q.
Proof.
rewrite /process_quantum /= finset.set0U; apply/bigcupsP=>i _; rewrite /= finset.set0U.
by case: (i == ord0); apply: correct_quantum.
Qed.
Lemma remote_alice_quantum q : process_quantum (remote_alice q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset; apply/andP; split.
- apply/andP; split=>//; apply/andP; split; [exact: second_register_subset|by rewrite finset.sub0set].
- apply/bigcupsP=>i _; rewrite /= finset.set0U; case: (i == ord0)=>/=; first by rewrite finset.sub0set.
  exact: fintype.subset_trans (@correct_quantum (first_register q) zA [unitary of PauliZ]) (@first_register_subset _ _ q).
Qed.
Lemma remote_bob_quantum q : process_quantum (remote_bob q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset; apply/andP; split.
- apply/andP; split=>//; apply/andP; split; first exact: first_register_subset.
  apply/andP; split; [exact: first_register_subset|by rewrite finset.sub0set].
- apply/bigcupsP=>i _; rewrite /= finset.set0U; case: (i == ord0)=>/=; last by rewrite finset.sub0set.
  exact: fintype.subset_trans (@correct_quantum (second_register q) xB [unitary of PauliX]) (@second_register_subset _ _ q).
Qed.

Definition pair_processes (alice bob : process) (i : 'I_2) :=
  if i == ord0 then alice else bob.

Lemma pair_point_to_point alice bob : point_to_point (pair_processes alice bob).
Proof.
move=>[[|[|i]] Hi] [[|[|j]] Hj] [[|[|k]] Hk] //=;
  rewrite ?eqxx //; by [].
Qed.

Lemma pair_private alice bob (QA QB : {set mlab}) :
  process_owned "Alice" alice -> process_owned "Bob" bob ->
  process_quantum alice \subset QA -> process_quantum bob \subset QB ->
  [disjoint QA & QB] -> pairwise_private (pair_processes alice bob).
Proof.
move=>Ha Hb Hqa Hqb Hdis.
have Hab k : process_reads alice k -> k \notin process_changes bob.
  move=>Hk; apply/negP=>Hj; have Ea := Ha _ Hk.
  have Eb := Hb _ (process_changes_reads Hj).
  by move: Ea; rewrite /owned Eb.
have Hba k : process_reads bob k -> k \notin process_changes alice.
  move=>Hk; apply/negP=>Hj; have Eb := Hb _ Hk.
  have Ea := Ha _ (process_changes_reads Hj).
  by move: Eb; rewrite /owned Ea.
have Hq : [disjoint process_quantum alice & process_quantum bob].
  exact: fintype.disjointW Hqa Hqb Hdis.
move=>i j Hij; rewrite /pair_processes.
case Ei: (i == ord0); case Ej: (j == ord0).
- have Eij : i = j := round_bit_inj (eq_trans Ei (esym Ej)).
  by subst j; rewrite eqxx in Hij.
- split=>//; apply/eqP; exact: finset.disjoint_setI0 Hq.
- split=>//; apply/eqP; rewrite finset.setIC; exact: finset.disjoint_setI0 Hq.
- have Eij : i = j := round_bit_inj (eq_trans Ei (esym Ej)).
  by subst j; rewrite eqxx in Hij.
Qed.

Definition teleport_program (qa : wf_qreg (QPair QBool QBool))
    (qb : wf_qreg QBool) (Hdis : [disjoint mset qa & mset qb]) : program.
Proof.
apply: (@Program 2 (pair_processes (teleport_alice qa) (teleport_bob qb)) erefl).
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: teleport_alice_wf|exact: teleport_bob_wf].
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: teleport_alice_finite|exact: teleport_bob_finite].
- exact: (@pair_private (teleport_alice qa) (teleport_bob qb) (mset qa) (mset qb)
    (@teleport_alice_owned qa) (@teleport_bob_owned qb)
    (@teleport_alice_quantum qa) (@teleport_bob_quantum qb) Hdis).
- exact: pair_point_to_point.
Defined.

Definition remote_program (qa qb : wf_qreg (QPair QBool QBool))
    (Hdis : [disjoint mset qa & mset qb]) : program.
Proof.
apply: (@Program 2 (pair_processes (remote_alice qa) (remote_bob qb)) erefl).
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: remote_alice_wf|exact: remote_bob_wf].
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: remote_alice_finite|exact: remote_bob_finite].
- exact: (@pair_private (remote_alice qa) (remote_bob qb) (mset qa) (mset qb)
    (@remote_alice_owned qa) (@remote_bob_owned qb)
    (@remote_alice_quantum qa) (@remote_bob_quantum qb) Hdis).
- exact: pair_point_to_point.
Defined.

End DistributedProtocolOwnership.
