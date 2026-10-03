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
From quantum.example.distributive Require Import language operational distribution weighted scheduler local_actions results residual sequentialization.
From quantum.example.classical Require Import state.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import progress guarded_rules.

Module DistributedSerialScheduler.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedLocalActions DistributedProgress DistributedResidual DistributedGuardedRules.
Local Notation Hq := 'H[msys]_finset.setT.

Definition idle_control (p : process) := after_local p Finished.
Definition idle_configuration n (p : 'I_n -> process) m rho :=
  global_config (fun i => idle_control (p i)) (Some m) rho.

Lemma idle_control_waiting p (j : 'I_(branch_count p)) : idle_control p = Waiting.
Proof.
have Hpos : (0 < branch_count p)%N.
  exact: (leq_ltn_trans (leq0n _) (ltn_ord j)).
rewrite /idle_control /after_local; case E: (branch_count p)=>[|k] //.
by move: Hpos; rewrite E ltnn.
Qed.

Lemma idle_owned n (p : 'I_n -> process) m rho :
  configuration_owned p (idle_configuration p m rho).
Proof. move=>i; rewrite /idle_configuration /idle_control /after_local /=; by case: branch_count. Qed.

Lemma execute_owned n (p : 'I_n -> process) pc i s m rho :
  configuration_owned p (global_config pc (Some m) rho) -> statement_owned (p i) s ->
  configuration_owned p (global_config (replace pc i (Executing s)) (Some m) rho).
Proof.
move=>Hpc Hs j; rewrite /replace /=; case E: (j == i); first by move/eqP: E=>->.
exact: Hpc.
Qed.

Lemma lift_local_start n (p : 'I_n -> process) pc i s m rho : statement_wf s ->
  lift_local p pc i (local_config s (Some m) rho) =
  global_config (replace pc i (Executing s)) (Some m) rho.
Proof. by case: s. Qed.

Lemma lift_local_finished n (p : 'I_n -> process) pc i m rho :
  lift_local p pc i (local_config Finished (Some m) rho) =
  global_config (replace pc i (idle_control (p i))) (Some m) rho.
Proof. by []. Qed.

Lemma serial_local_step n (p : 'I_n -> process) pc i s m rho : statement_wf s ->
  pc i = Executing s ->
  global_step p (global_config pc (Some m) rho)
    (fmap (lift_local p pc i) (local_successor s m rho)).
Proof. move=>Hs Hi; apply: StepParallel Hi _; exact: local_successor_step. Qed.

Record rendezvous_index n (p : 'I_n -> process) := RendezvousIndex {
  first_process : 'I_n;
  second_process : 'I_n;
  first_branch : 'I_(branch_count (p first_process));
  second_branch : 'I_(branch_count (p second_process))
}.
Arguments RendezvousIndex {n p} first_process second_process first_branch second_branch.
Arguments first_process {n p} _.
Arguments second_process {n p} _.
Arguments first_branch {n p} _.
Arguments second_branch {n p} _.

Definition index_command n (p : 'I_n -> process) (a : rendezvous_index p) :=
  rendezvous_command p (first_process a) (second_process a) (first_branch a) (second_branch a).

Definition rendezvous_indices n (p : 'I_n -> process) :=
  flatten [seq flatten [seq flatten [seq
    [seq RendezvousIndex i k j l | l <- enum 'I_(branch_count (p k))]
    | j <- enum 'I_(branch_count (p i))] | k <- enum 'I_n] | i <- enum 'I_n].

Lemma pmap_flattenE (A B : Type) (f : A -> option B) ss :
  pmap f (flatten ss) = flatten [seq pmap f s | s <- ss].
Proof. by elim: ss=>[|s ss IH] //=; rewrite pmap_cat IH. Qed.

Lemma pmap_compE (A B C : Type) (f : B -> option C) (g : A -> B) s :
  pmap f [seq g a | a <- s] = pmap (fun a => f (g a)) s.
Proof. by elim: s=>[|a s IH] //=; case: (f (g a)); rewrite IH. Qed.

Lemma rendezvous_indicesE n (p : 'I_n -> process) :
  pmap (@index_command n p) (rendezvous_indices p) = rendezvous_commands p.
Proof.
rewrite /rendezvous_indices /rendezvous_commands pmap_flattenE -map_comp.
congr flatten; apply: eq_map=>i.
rewrite /= pmap_flattenE -map_comp; congr flatten; apply: eq_map=>k.
rewrite /= pmap_flattenE -map_comp; congr flatten; apply: eq_map=>j.
by rewrite /= pmap_compE /index_command.
Qed.

Fixpoint first_enabled n (p : 'I_n -> process) (indices : seq (rendezvous_index p)) m :=
  match indices with
  | [::] => None
  | a :: rest =>
      if index_command a is Some bc then
        if eval bc.1 m then Some a else first_enabled rest m
      else first_enabled rest m
  end.

Lemma first_enabled_some n (p : 'I_n -> process) indices m a :
  first_enabled indices m = Some a -> exists b c,
    index_command a = Some (b,c) /\ eval b m /\
    CL.denote (conditional_chain (pmap (@index_command n p) indices)) m = CL.denote c m.
Proof.
elim: indices=>[|d indices IH] //=.
case Ed: (index_command d)=>[[b c]|] /=.
- case Eb: (eval b m)=>/= H.
  + case: H=>E; subst d; exists b,c; split=>//; split=>//.
    change (CL.denote (CL.Conditional b c
      (conditional_chain (pmap (@index_command n p) indices))) m = CL.denote c m).
    by rewrite CL.denote_conditional Eb.
  + have [b' [c' [Ea [Hb' HC]]]] := IH H.
    exists b',c'; split=>//; split=>//.
    change (CL.denote (CL.Conditional b c
      (conditional_chain (pmap (@index_command n p) indices))) m = CL.denote c' m).
    by rewrite CL.denote_conditional Eb HC.
- exact: IH.
Qed.

Lemma first_enabled_none n (p : 'I_n -> process) indices m :
  first_enabled indices m = None ->
  all (fun bc : expression bool * CL.command => ~~ eval bc.1 m)
    (pmap (@index_command n p) indices).
Proof.
elim: indices=>[|d indices IH] //=.
case Ed: (index_command d)=>[[b c]|] /=.
- case Eb: (eval b m)=>//= H; exact: IH H.
- exact: IH.
Qed.

Lemma selected_rendezvous_command n (p : 'I_n -> process) m a :
  first_enabled (rendezvous_indices p) m = Some a -> exists b c,
    index_command a = Some (b,c) /\ eval b m /\
    CL.denote (conditional_chain (rendezvous_commands p)) m = CL.denote c m.
Proof. rewrite -rendezvous_indicesE; exact: first_enabled_some. Qed.

Lemma no_rendezvous_command n (p : 'I_n -> process) m :
  first_enabled (rendezvous_indices p) m = None ->
  CL.denote (conditional_chain (rendezvous_commands p)) m = abort_sem m.
Proof.
move=>H; rewrite -rendezvous_indicesE; apply: conditional_chain_none.
exact: first_enabled_none H.
Qed.

Lemma index_enabled_data n (p : 'I_n -> process) a g c m :
  index_command a = Some (g,c) -> eval g m ->
  exists effect,
    (first_process a < second_process a)%N /\
    eval (process_guard (p (first_process a)) (first_branch a)) m /\
    eval (process_guard (p (second_process a)) (second_branch a)) m /\
    matches (process_io (p (first_process a)) (first_branch a))
      (process_io (p (second_process a)) (second_branch a)) effect /\
    c = CL.Sequence (translate_atom effect)
      (CL.Sequence (translate_statement (process_body (p (first_process a)) (first_branch a)))
        (translate_statement (process_body (p (second_process a)) (second_branch a)))).
Proof.
case: a=>i k j l; rewrite /index_command /rendezvous_command /=.
case Hik: (i < k)%N=>//.
case He: (communication_effect (process_io (p i) j) (process_io (p k) l))=>[effect|] //=.
move=>[= <- <-] /andP[Hj Hl]; exists effect; repeat split=>//.
exact: effect_matches He.
Qed.

Lemma selected_rendezvous_step n (p : 'I_n -> process) m rho a :
  first_enabled (rendezvous_indices p) m = Some a ->
  exists mu, global_step p (idle_configuration p m rho) mu.
Proof.
move=>H; have [g [c [Ha [Hg HC]]]] := selected_rendezvous_command H.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
  by case: Hmatch=>t ch x e; exists t, x, e.
case: Hass=>t [x [e He]]; subst effect.
eexists; apply: StepCommunication Hik _ _ Hj Hl Hmatch.
- exact: (@idle_control_waiting (p (first_process a)) (first_branch a)).
- exact: (@idle_control_waiting (p (second_process a)) (second_branch a)).
Qed.

Definition ready n (pc : 'I_n -> control) := forall i, pc i = Waiting \/ pc i = Stopped.

Lemma idle_ready n (p : 'I_n -> process) : ready (fun i => idle_control (p i)).
Proof. move=>i; rewrite /idle_control /after_local; by case: branch_count; [right | left]. Qed.

Lemma ready_replace n (pc : 'I_n -> control) i : ready pc -> ready (replace pc i Stopped).
Proof. move=>H j; rewrite /replace; case: ifP=>_; [by right | exact: H]. Qed.

Definition no_rendezvous n (p : 'I_n -> process) m :=
  all (fun bc : expression bool * CL.command => ~~ eval bc.1 m) (rendezvous_commands p).

Lemma all_pmapE (A B : Type) (f : A -> option B) (test : B -> bool) s :
  all test (pmap f s) = all (fun a => oapp test true (f a)) s.
Proof. by elim: s=>[|a s IH] //=; case: (f a)=>//= b; rewrite IH. Qed.

Lemma no_rendezvous_guard n (p : 'I_n -> process) m (i k : 'I_n) j l effect :
  no_rendezvous p m -> (i < k)%N ->
  matches (process_io (p i) j) (process_io (p k) l) effect ->
  ~~ (eval (process_guard (p i) j) m && eval (process_guard (p k) l) m).
Proof.
move=>H Hik Hmatch.
have Hi : i \in enum 'I_n by rewrite mem_enum.
have Hk : k \in enum 'I_n by rewrite mem_enum.
have Hj : j \in enum 'I_(branch_count (p i)) by rewrite mem_enum.
have Hl : l \in enum 'I_(branch_count (p k)) by rewrite mem_enum.
move: H; rewrite /no_rendezvous /rendezvous_commands all_flattenE all_map=>/allP/(_ i Hi).
rewrite /= all_flattenE all_map=>/allP/(_ k Hk).
rewrite /= all_flattenE all_map=>/allP/(_ j Hj).
rewrite /= all_pmapE=>/allP/(_ l Hl).
by rewrite /rendezvous_command Hik (matching_effect Hmatch) /= /guard_and /=.
Qed.

Lemma blocked_ready_step n (p : 'I_n -> process) pc m rho mu :
  ready pc -> no_rendezvous p m -> global_step p (global_config pc (Some m) rho) mu ->
  exists i, pc i = Waiting /\ [forall j, ~~ eval (process_guard (p i) j) m] /\
    mu = certain (global_config (replace pc i Stopped) (Some m) rho).
Proof.
move=>Hready Hblocked Hstep.
inversion Hstep as
  [pc0 m0 rho0 i s nu Hi Hloc
  |pc0 m0 rho0 i Hi Hg
  |pc0 m0 rho0 i k j l t x e Hik Hi Hk Hj Hl Hmatch]; subst.
- have [H|H] := Hready i; congruence.
- by exists i; repeat split.
- have Hfalse := no_rendezvous_guard Hblocked Hik Hmatch.
  by rewrite Hj Hl in Hfalse.
Qed.

Inductive deterministic_steps n (p : 'I_n -> process) :
    global_configuration n -> global_configuration n -> Prop :=
| DeterministicRefl c : deterministic_steps p c c
| DeterministicMore c d e : global_step p c (certain d) ->
    deterministic_steps p d e -> deterministic_steps p c e.

Fixpoint stop_list n (pc : 'I_n -> control) (indices : seq 'I_n) :=
  if indices is i :: rest then stop_list (replace pc i Stopped) rest else pc.

Lemma replace_current n (pc : 'I_n -> control) i : replace pc i (pc i) = pc.
Proof. apply/funext=>j; rewrite /replace; by case: eqP=>[->|]. Qed.

Lemma stop_listE n (pc : 'I_n -> control) indices j :
  stop_list pc indices j = if j \in indices then Stopped else pc j.
Proof.
elim: indices pc=>[|i indices IH] pc //=.
rewrite IH inE /replace; by case: (j == i); case: (j \in indices).
Qed.

Lemma stop_enum n (pc : 'I_n -> control) : stop_list pc (enum 'I_n) = (fun _ => Stopped).
Proof. apply/funext=>i; by rewrite stop_listE mem_enum. Qed.

Lemma terminate_stop_list n (p : 'I_n -> process) indices pc m rho :
  ready pc -> term p m ->
  deterministic_steps p (global_config pc (Some m) rho)
    (global_config (stop_list pc indices) (Some m) rho).
Proof.
elim: indices pc=>[|i indices IH] pc Hready Hterm /=; first exact: DeterministicRefl.
have Htail := IH (replace pc i Stopped) (ready_replace i Hready) Hterm.
have [Hi|Hi] := Hready i.
- apply: (DeterministicMore _ Htail); apply: StepProcessDone Hi _.
  exact: (forallP Hterm i).
- have Epc : replace pc i Stopped = pc by rewrite -Hi replace_current.
  by rewrite Epc in Htail *.
Qed.

Theorem boundary_terminates n (p : 'I_n -> process) m rho : term p m ->
  deterministic_steps p (idle_configuration p m rho)
    (global_config (fun _ => Stopped) (Some m) rho).
Proof.
move=>Hterm; rewrite -(stop_enum (fun i => idle_control (p i))).
exact: terminate_stop_list (idle_ready p) Hterm.
Qed.

End DistributedSerialScheduler.
