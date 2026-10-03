(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.distributive Require Import language operational distribution weighted scheduler local_actions results residual sequentialization progress global_actions instruments.
From quantum.example.classical Require Import state footprint.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedGlobalInstruments.
Import DistributedLanguage DistributedOperational DistributedScheduler
  DistributedLocalActions DistributedResults DistributedResidual DistributedProgress
  DistributedGlobalActions DistributedInstruments.

Record descriptor n := Descriptor {
  instruction : statement;
  update_control : statement -> ('I_n -> control) -> ('I_n -> control)
}.
Arguments Descriptor {n} instruction update_control.
Arguments instruction {n} d.
Arguments update_control {n} d s pc i.

Definition local_descriptor n (p : 'I_n -> process) i s : descriptor n :=
  Descriptor s (fun t pc => replace pc i (after_local (p i) t)).
Definition done_descriptor n (i : 'I_n) : descriptor n :=
  Descriptor (Atomic ASkip) (fun _ pc => replace pc i Stopped).
Definition communication_descriptor n (p : 'I_n -> process) i k j l effect : descriptor n :=
  Descriptor (Atomic effect) (fun _ pc =>
    replace (replace pc i (Executing (process_body (p i) j)))
      k (Executing (process_body (p k) l))).
Arguments communication_descriptor {n} p i k j l effect.

Definition descriptor_lift n (d : descriptor n) pc (c : local_configuration) :=
  global_config (update_control d c.1.1 pc) c.1.2 c.2.
Definition descriptor_run n (d : descriptor n) pc m rho :=
  fmap (descriptor_lift d pc) (local_successor (instruction d) m rho).

Inductive enabled_descriptor n (p : 'I_n -> process) pc m :
    action n -> descriptor n -> Prop :=
| EnabledInstruction i s : pc i = Executing s ->
    enabled_descriptor p pc m (Local i) (local_descriptor p i s)
| EnabledDone i : pc i = Waiting ->
    [forall j, ~~ eval (process_guard (p i) j) m] ->
    enabled_descriptor p pc m (Local i) (done_descriptor i)
| EnabledCommunication (i k : 'I_n) j l t (x : CL.variable t) e :
    (i < k)%N -> pc i = Waiting -> pc k = Waiting ->
    eval (process_guard (p i) j) m -> eval (process_guard (p k) l) m ->
    matches (process_io (p i) j) (process_io (p k) l) (AAssign x e) ->
    enabled_descriptor p pc m (Rendezvous i k)
      (communication_descriptor p i k j l (AAssign x e)).

Lemma enabled_instruction_wf n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> statement_wf (instruction d).
Proof.
move=>Hown; case=>[i s Hpc|i Hpc Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch] //=.
by move: (Hown i); rewrite /= Hpc=>/proj1.
Qed.

Lemma descriptor_step n (p : 'I_n -> process) pc m rho a d :
  enabled_descriptor p pc m a d -> statement_wf (instruction d) ->
  labeled_step p a (global_config pc (Some m) rho) (descriptor_run d pc m rho).
Proof.
case=>[i s Hpc|i Hpc Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hwf.
- apply: LParallel Hpc _; exact: local_successor_step Hwf m rho.
- exact: LProcessDone Hpc Hnone.
- exact: LCommunication Hik Hi Hk Hj Hl Hmatch.
Qed.

Lemma labeled_step_descriptor n (p : 'I_n -> process) a c mu :
  configuration_owned p c -> labeled_step p a c mu ->
  exists m d, c.1.2 = Some m /\ enabled_descriptor p c.1.1 m a d /\
    statement_wf (instruction d) /\ mu = descriptor_run d c.1.1 m c.2.
Proof.
move=>Hown Hstep; case: Hstep Hown=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hown.
- have Hs : statement_wf s.
    by move: (Hown i); rewrite /= Hpc=>/proj1.
  exists m, (local_descriptor p i s); split=>//; split.
  + exact: EnabledInstruction Hpc.
  + split=>//; rewrite (local_step_canonical Hloc Hs erefl); by [].
- exists m, (done_descriptor i); split=>//; split.
  + exact: EnabledDone Hpc Hnone.
  + by split.
- exists m, (communication_descriptor p i k j l (AAssign x e)); split=>//; split.
  + exact: EnabledCommunication Hik Hi Hk Hj Hl Hmatch.
  + by split.
Qed.

Lemma descriptor_update_outside n (p : 'I_n -> process) pc m a d :
  enabled_descriptor p pc m a d -> forall s pc' i,
  i \notin participants a -> update_control d s pc' i = pc' i.
Proof.
case=>[j t Hj|j Hj Hnone|j k h l t x e Hjk Hj Hk Hh Hl Hmatch] s pc' i.
- rewrite inE=>Hi; exact: replace_other Hi.
- rewrite inE=>Hi; exact: replace_other Hi.
- rewrite !inE negb_or=>/andP[Hij Hik]; by rewrite /= !replace_other.
Qed.

Lemma descriptor_update_inside n (p : 'I_n -> process) pc m a d :
  enabled_descriptor p pc m a d -> forall s pc' pc'' i,
  i \in participants a -> update_control d s pc' i = update_control d s pc'' i.
Proof.
case=>[j t Hj|j Hj Hnone|j k h l t x e Hjk Hj Hk Hh Hl Hmatch] s pc' pc'' i.
- rewrite inE=>/eqP->; by rewrite /= !replace_same.
- rewrite inE=>/eqP->; by rewrite /= !replace_same.
- rewrite !inE=>/orP[/eqP->|/eqP->]; rewrite /= /replace !eqxx //.
Qed.

Lemma descriptor_update_pointwise n (p : 'I_n -> process) pc m a d :
  enabled_descriptor p pc m a d -> forall s pc' i,
  update_control d s pc' i =
    if i \in participants a then update_control d s pc i else pc' i.
Proof.
move=>Hd s pc' i; case E: (i \in participants a).
- exact: (@descriptor_update_inside _ _ _ _ _ _ Hd s pc' pc i E).
- apply: (@descriptor_update_outside _ _ _ _ _ _ Hd s pc' i).
  by rewrite E.
Qed.

Lemma descriptor_updates_commute n (p : 'I_n -> process) pc m a b d e :
  enabled_descriptor p pc m a d -> enabled_descriptor p pc m b e ->
  [disjoint participants a & participants b]%SET -> forall s t,
  update_control d s (update_control e t pc) = update_control e t (update_control d s pc).
Proof.
move=>Hd He Hdis s t; apply/funext=>i.
rewrite (descriptor_update_pointwise Hd s (update_control e t pc) i)
  (descriptor_update_pointwise He t (update_control d s pc) i).
case Ha: (i \in participants a); case Hb: (i \in participants b)=>//.
- by move/disjointP: Hdis=>/(_ i Ha); rewrite Hb.
- rewrite (@descriptor_update_outside _ _ _ _ _ _ Hd s pc i) ?Ha //.
  by rewrite (@descriptor_update_outside _ _ _ _ _ _ He t pc i) ?Hb.
Qed.

Definition processes_agree n (p : 'I_n -> process) (A : {set 'I_n}) (m m' : cmem) :=
  forall i, i \in A -> forall u (x : CL.variable u),
    process_reads (p i) (name_of x) -> (m.[x] = m'.[x])%M.

Lemma process_guard_reads p j x : expression_reads (process_guard p j) x -> process_reads p x.
Proof. move=>Hx; right; exists j=>//; left; by left. Qed.

Lemma process_io_reads p j x : communication_reads (process_io p j) x -> process_reads p x.
Proof. move=>Hx; right; exists j=>//; left; by right. Qed.

Lemma process_guard_agree n (p : 'I_n -> process) A m m' i j :
  processes_agree p A m m' -> i \in A ->
  eval (process_guard (p i) j) m = eval (process_guard (p i) j) m'.
Proof.
move=>Hagree Hi; apply: ClassicalFootprint.eval_local=>u x Hx.
apply: (Hagree i Hi u x); exact: process_guard_reads Hx.
Qed.

Lemma enabled_descriptor_preserved n (p : 'I_n -> process) pc m a d pc' m' :
  enabled_descriptor p pc m a d ->
  (forall i, i \in participants a -> pc' i = pc i) ->
  processes_agree p (participants a) m m' -> enabled_descriptor p pc' m' a d.
Proof.
move=>Hd; case: Hd=>[i s Hi|i Hi Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch]
  Hpc Hagree.
- apply: EnabledInstruction; rewrite Hpc ?inE ?eqxx //.
- have Hii : i \in [set i] by rewrite inE eqxx.
  apply: EnabledDone; first by rewrite Hpc ?inE ?eqxx //.
  apply/forallP=>j; rewrite -(@process_guard_agree n p [set i] m m' i j Hagree Hii).
  exact: (forallP Hnone j).
- have Hii : i \in [set i; k] by rewrite !inE eqxx.
  have Hkk : k \in [set i; k] by rewrite !inE eqxx orbT.
  apply: EnabledCommunication Hik _ _ _ _ Hmatch.
  + by rewrite Hpc ?inE ?eqxx //.
  + by rewrite Hpc ?inE ?eqxx ?orbT //.
  + by rewrite -(@process_guard_agree n p [set i; k] m m' i j Hagree Hii).
  + by rewrite -(@process_guard_agree n p [set i; k] m m' k l Hagree Hkk).
Qed.

Lemma matches_reads a b effect : matches a b effect -> forall x,
  atom_reads effect x -> communication_reads a x \/ communication_reads b x.
Proof. case=>t c y e x; first by []. by move=>[H|H]; [right | left]. Qed.

Lemma matches_changes a b effect : matches a b effect -> forall x,
  x \in atom_changes effect -> x \in communication_changes a \/ x \in communication_changes b.
Proof. case=>t c y e x Hx; [by left | by right]. Qed.

Lemma process_io_changes p j x : x \in communication_changes (process_io p j) ->
  x \in process_changes p.
Proof.
move=>Hx; rewrite /process_changes in_fsetU; apply/orP; right.
apply/bigfcupP; exists j; first by rewrite mem_index_enum.
by rewrite in_fsetU Hx.
Qed.

Lemma descriptor_reads_owned n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> forall x, statement_reads (instruction d) x ->
  exists i, i \in participants a /\ process_reads (p i) x.
Proof.
move=>Hown; case=>[i s Hi|i Hi Hnone|i k j l t y e Hik Hi Hk Hj Hl Hmatch] x Hx.
- exists i; split; first by rewrite inE eqxx.
  have Ho := Hown i; rewrite /= Hi in Ho; exact: (proj1 (proj2 (proj2 Ho)) x Hx).
- by [].
- case: (matches_reads Hmatch Hx)=>[Hx'|Hx'].
  + exists i; split; first by rewrite !inE eqxx.
    exact: process_io_reads Hx'.
  + exists k; split; first by rewrite !inE eqxx orbT.
    exact: process_io_reads Hx'.
Qed.

Lemma descriptor_changes_owned n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> forall x, x \in statement_changes (instruction d) ->
  exists i, i \in participants a /\ x \in process_changes (p i).
Proof.
move=>Hown; case=>[i s Hi|i Hi Hnone|i k j l t y e Hik Hi Hk Hj Hl Hmatch] x Hx.
- exists i; split; first by rewrite inE eqxx.
  have Ho := Hown i; rewrite /= Hi in Ho.
  exact: (fsubsetP (proj1 (proj2 Ho)) x Hx).
- by move: Hx; rewrite inE.
- case: (matches_changes Hmatch Hx)=>[Hx'|Hx'].
  + exists i; split; first by rewrite !inE eqxx.
    exact: process_io_changes Hx'.
  + exists k; split; first by rewrite !inE eqxx orbT.
    exact: process_io_changes Hx'.
Qed.

Lemma descriptor_quantum_owned n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> forall x, x \in statement_quantum (instruction d) ->
  exists i, i \in participants a /\ x \in process_quantum (p i).
Proof.
move=>Hown; case=>[i s Hi|i Hi Hnone|i k j l t y e Hik Hi Hk Hj Hl Hmatch] x Hx.
- exists i; split; first by rewrite inE eqxx.
  have Ho := Hown i; rewrite /= Hi in Ho.
  exact: (fintype.subsetP (proj2 (proj2 (proj2 Ho))) x Hx).
- by move: Hx; rewrite inE.
- by move: Hx; rewrite inE.
Qed.

Lemma disjoint_participants_neq n (A B : {set 'I_n}) i j :
  [disjoint A & B]%SET -> i \in A -> j \in B -> i != j.
Proof.
move=>Hdis Hi Hj; apply/negP=>/eqP E; subst j.
by move/disjointP: Hdis=>/(_ i Hi); rewrite Hj.
Qed.

Lemma descriptor_private_reads (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET -> forall x,
  statement_reads (instruction d) x -> x \notin statement_changes (instruction e).
Proof.
move=>Hown Hd He Hdis x Hx; apply/negP=>Hx'.
have [i [Hi Hir]] := descriptor_reads_owned Hown Hd Hx.
have [j [Hj Hjw]] := descriptor_changes_owned Hown He Hx'.
have Hij := disjoint_participants_neq Hdis Hi Hj.
have Hfresh := proj1 (@processes_private P i j Hij) x Hir.
by move: Hfresh; rewrite Hjw.
Qed.

Lemma descriptor_private_quantum (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET ->
  ((statement_quantum (instruction d) :&: statement_quantum (instruction e)) == finset.set0)%SET.
Proof.
move=>Hown Hd He Hdis; apply/eqP; apply/setP=>x; rewrite !inE.
apply/negP=>/andP[Hxd Hxe].
have [i [Hi Hiq]] := descriptor_quantum_owned Hown Hd Hxd.
have [j [Hj Hjq]] := descriptor_quantum_owned Hown He Hxe.
have Hij := disjoint_participants_neq Hdis Hi Hj.
have Heq := eqP (proj2 (@processes_private P i j Hij)).
have Hmem : x \in (process_quantum (processes P i) :&: process_quantum (processes P j))%SET.
  by rewrite inE Hiq Hjq.
by move: Hmem; rewrite Heq inE.
Qed.

Lemma descriptor_preserves_other_reads (P : program) pc m rho a b d :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  [disjoint participants a & participants b]%SET -> forall outcome m',
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  processes_agree (processes P) (participants b) m m'.
Proof.
move=>Hown Hd Hdis outcome m' Hout i Hi u x Hx.
have Hwf := enabled_instruction_wf Hown Hd.
have Hstep := local_successor_step Hwf m rho.
apply: (@local_step_unchanged _ _ Hstep outcome m m' erefl Hout u x).
apply/negP=>Hwrite; have [j [Hj Hjw]] := descriptor_changes_owned Hown Hd Hwrite.
have Hji := disjoint_participants_neq Hdis Hj Hi.
have Hij : i != j by rewrite eq_sym.
have Hfresh := proj1 (@processes_private P i j Hij) (name_of x) Hx.
by move: Hfresh; rewrite Hjw.
Qed.


Lemma descriptor_other_enabled (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET -> forall outcome m',
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  enabled_descriptor (processes P) (branch_value (descriptor_run d pc m rho) outcome).1.1 m' b e.
Proof.
move=>Hown Hd He Hdis outcome m' Hout; apply: (enabled_descriptor_preserved He).
- move=>i Hi; apply: (@descriptor_update_outside _ _ _ _ _ _ Hd _ pc i).
  by move: Hdis; rewrite disjoint_sym=>/disjointP/(_ i Hi).
- exact: (@descriptor_preserves_other_reads P pc m rho a b d Hown Hd Hdis outcome m' Hout).
Qed.

Lemma descriptor_replay_after (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET -> forall outcome m',
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  labeled_step (processes P) b (branch_value (descriptor_run d pc m rho) outcome)
    (descriptor_run e (branch_value (descriptor_run d pc m rho) outcome).1.1 m'
      (branch_value (descriptor_run d pc m rho) outcome).2).
Proof.
move=>Hown Hd He Hdis outcome m' Hout.
have Henext := @descriptor_other_enabled P pc m rho a b d e Hown Hd He Hdis outcome m' Hout.
have Hewf := enabled_instruction_wf Hown He.
have Hstep := @descriptor_step _ _ _ _
  (branch_value (descriptor_run d pc m rho) outcome).2 _ _ Henext Hewf.
move: Hstep; rewrite -Hout; by case: (branch_value (descriptor_run d pc m rho) outcome)=>[[pc' store'] rho'].
Qed.

End DistributedGlobalInstruments.
