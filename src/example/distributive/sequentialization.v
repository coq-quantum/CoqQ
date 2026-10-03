(* Distributive: sequentialization. See README.md and PROOF_NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From Stdlib Require Import String.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum Require Import mcextra notation mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.example.distributive Require Import language operational confluence semantics.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module DistributedSequentialization.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage.

Definition guard_not (e : expression bool) : expression bool :=
  CL.EApp (CL.EConst negb) e.
Definition guard_and (e f : expression bool) : expression bool :=
  CL.EApp (CL.EApp (CL.EConst andb) e) f.
Definition guard_or (e f : expression bool) : expression bool :=
  CL.EApp (CL.EApp (CL.EConst orb) e) f.
Definition guards_any (es : seq (expression bool)) : expression bool :=
  foldr guard_or (CL.EConst false) es.
Definition guards_all (es : seq (expression bool)) : expression bool :=
  foldr guard_and (CL.EConst true) es.

Lemma eval_guards_any es m : eval (guards_any es) m = has (fun e => eval e m) es.
Proof. by elim: es=>[|e es IH] //=; rewrite /guards_any /= -/guards_any IH. Qed.
Lemma eval_guards_all es m : eval (guards_all es) m = all (fun e => eval e m) es.
Proof. by elim: es=>[|e es IH] //=; rewrite /guards_all /= -/guards_all IH. Qed.

Definition translate_atom (a : atom) : CL.command :=
  match a with
  | ASkip => CL.Skip
  | AAbort => CL.Abort
  | AAssign t x e => CL.Assign x e
  | ARandom t x p => CL.Random x p
  | AInitial t q phi => CL.Initialize q phi
  | AUnitary t q U => CL.Unitary q U
  | AMeasure t u x q M => CL.Measure x q M
  end.

Definition conditional_chain (bs : seq (expression bool * CL.command)) : CL.command :=
  foldr (fun b rest => CL.Conditional b.1 b.2 rest) CL.Abort bs.

Fixpoint translate_statement (s : statement) : CL.command :=
  match s with
  | Finished => CL.Skip
  | Atomic a => translate_atom a
  | Sequence s t => CL.Sequence (translate_statement s) (translate_statement t)
  | Alternative n g b =>
      conditional_chain [seq (g i, translate_statement (b i)) | i <- enum 'I_n]
  | Repetition n g b =>
      CL.While (guards_any [seq g i | i <- enum 'I_n])
        (conditional_chain [seq (g i, translate_statement (b i)) | i <- enum 'I_n])
  end.

Definition priority_guard n (g : 'I_n -> expression bool) (i : 'I_n) : expression bool :=
  guard_and (g i)
    (guards_all [seq guard_not (g j) | j <- enum 'I_n & ((j : 'I_n) < i)%N]).

Lemma eval_priority_guard n (g : 'I_n -> expression bool) i m :
  eval (priority_guard g i) m =
  (eval (g i) m && [forall j : 'I_n, (j < i)%N ==> ~~ eval (g j) m]).
Proof.
rewrite /priority_guard /guard_and /= eval_guards_all all_map all_filter.
f_equal; apply/idP/forallP.
- move=>/allP H j; apply: H; exact: mem_enum.
- by move=>H; apply/allP=>j _; apply: H.
Qed.

Lemma priority_exclusive n (g : 'I_n -> expression bool) : exclusive (priority_guard g).
Proof.
move=>m i j; rewrite !eval_priority_guard=>/andP [Hi /forallP HprevI]
  /andP [Hj /forallP HprevJ].
case: (ltngtP (val i) (val j))=>Hij.
- by move: (HprevJ i); rewrite Hij Hi.
- by move: (HprevI j); rewrite Hij Hj.
- exact: val_inj Hij.
Qed.

Lemma priority_enabled n (g : 'I_n -> expression bool) m :
  [exists i, eval (priority_guard g i) m] = [exists i, eval (g i) m].
Proof.
apply/existsP/existsP.
- move=>[i Hi]; move: Hi; rewrite eval_priority_guard=>/andP [Hi _]; by exists i.
- move=>[i0 Hi0].
  have [i Hi Hmin] := @arg_minnP (Finite.clone 'I_n _) i0
    (fun i => eval (g i) m) (fun i => val i) Hi0.
  exists i.
  rewrite eval_priority_guard Hi /=; apply/forallP=>j; apply/implyP=>Hj.
  apply/negP=>Hgj; have := Hmin j Hgj.
  by rewrite leqNgt Hj.
Qed.

Definition rendezvous_command n (p : 'I_n -> process) (i k : 'I_n)
    (j : 'I_(branch_count (p i))) (l : 'I_(branch_count (p k))) :=
  if (i < k)%N then
    omap (fun effect =>
      (guard_and (process_guard (p i) j) (process_guard (p k) l),
       CL.Sequence (translate_atom effect)
         (CL.Sequence (translate_statement (process_body (p i) j))
           (translate_statement (process_body (p k) l)))))
      (communication_effect (process_io (p i) j) (process_io (p k) l))
  else None.
Arguments rendezvous_command {n} p i k j l.

Definition rendezvous_commands n (p : 'I_n -> process) :=
  flatten [seq flatten [seq flatten [seq
    pmap (fun l => rendezvous_command p i k j l) (enum 'I_(branch_count (p k)))
    | j <- enum 'I_(branch_count (p i))] | k <- enum 'I_n] | i <- enum 'I_n].

Definition termination_guard n (p : 'I_n -> process) : expression bool :=
  guards_all (flatten [seq
    [seq guard_not (process_guard (p i) j) | j <- enum 'I_(branch_count (p i))]
    | i <- enum 'I_n]).

Definition sequentialize n (p : 'I_n -> process) : CL.command :=
  CL.Sequence
    (foldr CL.Sequence CL.Skip
      [seq translate_statement (initialization (p i)) | i <- enum 'I_n])
    (CL.While (guards_any [seq b.1 | b <- rendezvous_commands p])
      (conditional_chain (rendezvous_commands p))).

(* The paper restricts the sequentialized output to term. This final test
   implements that restriction: unmatched enabled channels contribute zero. *)
Definition successful_sequentialize n (p : 'I_n -> process) : CL.command :=
  CL.Sequence (sequentialize p)
    (CL.Conditional (termination_guard p) CL.Skip CL.Abort).

Lemma all_flattenE (T : Type) (P : pred T) ss :
  all P (flatten ss) = all (fun s => all P s) ss.
Proof. by elim: ss=>[|s ss IH] //=; rewrite all_cat IH. Qed.

Lemma eval_termination_guard n (p : 'I_n -> process) m :
  eval (termination_guard p) m = term p m.
Proof.
rewrite /termination_guard eval_guards_all all_flattenE all_map /term.
apply/idP/forallP.
- move=>/allP H i.
  have Hmem : i \in enum 'I_n by rewrite mem_enum.
  have := H i Hmem; rewrite /= all_map=>/allP Hi; apply/forallP=>j.
  apply: Hi; by rewrite mem_enum.
- move=>H; apply/allP=>i _; rewrite /= all_map; apply/allP=>j _.
  exact: (forallP (H i) j).
Qed.
End DistributedSequentialization.


Module DistributedGuardSemantics.
(* Independent guarded-command rules, quantum ranking assertions, and
   soundness/completeness for their shared-language translation. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedSequentialization CQAssertion CQPredicate.
Lemma conditional_chain_none (bs : seq (expression bool * CL.command)) m :
  all (fun bc => ~~ eval bc.1 m) bs -> ClassicalSemantics.denote (conditional_chain bs) m = abort_sem m.
Proof.
elim: bs=>[|[b c] bs IH] // /andP[Hb Hbs].
change (ClassicalSemantics.denote (CL.Conditional b c (conditional_chain bs)) m = abort_sem m).
rewrite ClassicalSemantics.denote_conditional (negbTE Hb); exact: IH.
Qed.

Lemma conditional_chain_selected n (g : 'I_n -> expression bool) (b : 'I_n -> CL.command)
    (indices : seq 'I_n) m i :
  exclusive g -> i \in indices -> eval (g i) m ->
  ClassicalSemantics.denote (conditional_chain [seq (g j,b j) | j <- indices]) m = ClassicalSemantics.denote (b i) m.
Proof.
move=>Hex; elim: indices=>[|j indices IH] //.
change (i \in j :: indices -> eval (g i) m ->
  ClassicalSemantics.denote (CL.Conditional (g j) (b j) (conditional_chain [seq (g z,b z) | z <- indices])) m = ClassicalSemantics.denote (b i) m).
rewrite inE=>/orP[/eqP E|Hi] Hgi.
- subst j; by rewrite ClassicalSemantics.denote_conditional Hgi.
- rewrite ClassicalSemantics.denote_conditional; case Hgj: (eval (g j) m).
  + by rewrite (Hex m j i Hgj Hgi).
  + exact: IH Hi Hgi.
Qed.

Definition loop_guard n (g : 'I_n -> expression bool) :=
  guards_any [seq g i | i <- enum 'I_n].
Definition enabled n (g : 'I_n -> expression bool) m :=
  has (fun i => eval (g i) m) (enum 'I_n).

Lemma eval_loop_guard n (g : 'I_n -> expression bool) m :
  eval (loop_guard g) m = enabled g m.
Proof. by rewrite /loop_guard eval_guards_any has_map. Qed.

Lemma enabledP n (g : 'I_n -> expression bool) m :
  reflect (exists i, eval (g i) m) (enabled g m).
Proof.
apply: (iffP hasP).
- by move=>[i _ Hi]; exists i.
- by move=>[i Hi]; exists i; rewrite ?mem_enum.
Qed.


End DistributedGuardSemantics.


Module DistributedSerialScheduler.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedLocalActions DistributedProgress DistributedResidual DistributedGuardSemantics.
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
    ClassicalSemantics.denote (conditional_chain (pmap (@index_command n p) indices)) m = ClassicalSemantics.denote c m.
Proof.
elim: indices=>[|d indices IH] //=.
case Ed: (index_command d)=>[[b c]|] /=.
- case Eb: (eval b m)=>/= H.
  + case: H=>E; subst d; exists b,c; split=>//; split=>//.
    change (ClassicalSemantics.denote (CL.Conditional b c
      (conditional_chain (pmap (@index_command n p) indices))) m = ClassicalSemantics.denote c m).
    by rewrite ClassicalSemantics.denote_conditional Eb.
  + have [b' [c' [Ea [Hb' HC]]]] := IH H.
    exists b',c'; split=>//; split=>//.
    change (ClassicalSemantics.denote (CL.Conditional b c
      (conditional_chain (pmap (@index_command n p) indices))) m = ClassicalSemantics.denote c' m).
    by rewrite ClassicalSemantics.denote_conditional Eb HC.
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
    ClassicalSemantics.denote (conditional_chain (rendezvous_commands p)) m = ClassicalSemantics.denote c m.
Proof. rewrite -rendezvous_indicesE; exact: first_enabled_some. Qed.

Lemma no_rendezvous_command n (p : 'I_n -> process) m :
  first_enabled (rendezvous_indices p) m = None ->
  ClassicalSemantics.denote (conditional_chain (rendezvous_commands p)) m = abort_sem m.
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


Module DistributedStoppedInvariant.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedGlobalActions DistributedGlobalInstruments DistributedResidual.

Definition stopped_valid n (p : 'I_n -> process) pc m :=
  forall i, pc i = Stopped -> forall j, ~~ eval (process_guard (p i) j) m.

Definition configuration_stopped_valid n (p : 'I_n -> process) (c : global_configuration n) :=
  forall m, c.1.2 = Some m -> stopped_valid p c.1.1 m.

Lemma initial_stopped_valid n (p : 'I_n -> process) m rho :
  configuration_stopped_valid p (initial_configuration p m rho).
Proof. by move=>m' _ i. Qed.

Lemma stopped_valid_term n (p : 'I_n -> process) m :
  stopped_valid p (fun _ => Stopped) m -> term p m.
Proof. move=>H; apply/forallP=>i; apply/forallP=>j; exact: H i erefl j. Qed.

Lemma after_local_stopped_no_branch p s (j : 'I_(branch_count p)) :
  after_local p s <> Stopped.
Proof.
have Hpos : (0 < branch_count p)%N.
  exact: (leq_ltn_trans (leq0n _) (ltn_ord j)).
case: s=>//=; case E: (branch_count p)=>[|n] //.
by move: Hpos; rewrite E ltnn.
Qed.

Lemma descriptor_stopped_inside n (p : 'I_n -> process) pc m rho a d :
  enabled_descriptor p pc m a d -> forall outcome m' i,
  i \in participants a ->
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  (branch_value (descriptor_run d pc m rho) outcome).1.1 i = Stopped ->
  forall j, ~~ eval (process_guard (p i) j) m'.
Proof.
case=>[i s Hpc|i Hpc Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch] outcome m' z.
- rewrite /participants inE=>/eqP-> Hstore Hstop j.
  have Hne := @after_local_stopped_no_branch (p i)
    (branch_value (DistributedLocalActions.local_successor s m rho) outcome).1.1 j.
  move: Hstop; rewrite /descriptor_run /descriptor_lift /local_descriptor /= replace_same.
  by move=>E; exfalso; apply: Hne.
- rewrite /participants inE=>/eqP-> /= [= <-] _ j; exact: (forallP Hnone j).
- rewrite /participants !inE=>/orP[/eqP->|/eqP->] Hstore Hstop z'.
  + move: Hstop; rewrite /descriptor_run /descriptor_lift /communication_descriptor /=.
    have Hneq : i != k by apply/eqP=>E; move: Hik; rewrite E ltnn.
    by rewrite replace_other // replace_same.
  + by move: Hstop; rewrite /descriptor_run /descriptor_lift /communication_descriptor /= replace_same.
Qed.

Lemma disjoint_single_outside n (a : action n) i : i \notin participants a ->
  [disjoint participants a & participants (Local i)]%SET.
Proof.
move=>Hi; apply/disjointP=>j Hj; rewrite /participants inE; apply/negP=>/eqP E.
by subst j; move: Hi; rewrite Hj.
Qed.

Lemma descriptor_stopped_valid (P : program) pc m rho a d :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  stopped_valid (processes P) pc m ->
  enabled_descriptor (processes P) pc m a d -> forall outcome m',
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  stopped_valid (processes P) (branch_value (descriptor_run d pc m rho) outcome).1.1 m'.
Proof.
move=>Hown Hvalid Hd outcome m' Hout i Hstop j.
case Hi: (i \in participants a).
- exact: (@descriptor_stopped_inside _ _ _ _ _ _ _ Hd outcome m' i Hi Hout Hstop j).
- have Houtside : i \notin participants a by rewrite Hi.
  have Hdis := disjoint_single_outside Houtside.
  have Hagree := @descriptor_preserves_other_reads P pc m rho a (Local i) d
    Hown Hd Hdis outcome m' Hout.
  have HiLocal : i \in participants (Local i) by rewrite /participants inE eqxx.
  have Hguard := @process_guard_agree _ _ _ m m' i j Hagree HiLocal.
  rewrite -Hguard; apply: Hvalid.
  move: Hstop; rewrite /descriptor_run /descriptor_lift /=.
  by rewrite (descriptor_update_outside Hd _ _ Houtside).
Qed.

Theorem global_step_stopped_valid (P : program) c mu :
  configuration_owned (processes P) c -> configuration_stopped_valid (processes P) c ->
  global_step (processes P) c mu -> forall outcome,
  configuration_stopped_valid (processes P) (branch_value mu outcome).
Proof.
move=>Hown Hvalid Hstep.
have [a Ha] := labeled_step_complete Hstep.
have [m [d [Hstore [Hd [Hwf E]]]]] := labeled_step_descriptor Hown Ha.
subst mu; move=>outcome m' Hout.
have Hown' : configuration_owned (processes P) (global_config c.1.1 (Some m) c.2).
  exact: Hown.
exact: (@descriptor_stopped_valid P c.1.1 m c.2 a d Hown'
  (Hvalid m Hstore) Hd outcome m' Hout).
Qed.
End DistributedStoppedInvariant.


Module DistributedResidualSemantics.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Definition control_command (pc : control) :=
  if pc is Executing s then translate_statement s else CL.Skip.
Definition active_program n (indices : seq 'I_n) (pc : 'I_n -> control) tail :=
  foldr (fun i rest => CL.Sequence (control_command (pc i)) rest) tail indices.
Definition network_tail n (p : 'I_n -> process) :=
  CL.Sequence
    (CL.While (guards_any [seq bc.1 | bc <- rendezvous_commands p])
      (conditional_chain (rendezvous_commands p)))
    (CL.Conditional (termination_guard p) CL.Skip CL.Abort).
Definition residual_command n (p : 'I_n -> process) pc :=
  active_program (enum 'I_n) pc (network_tail p).

Lemma active_program_cat n (pc : 'I_n -> control) xs ys tail :
  active_program (xs ++ ys) pc tail = active_program xs pc (active_program ys pc tail).
Proof. exact: foldr_cat. Qed.

Lemma active_program_idle n (pc : 'I_n -> control) indices tail :
  (forall i, i \in indices -> control_command (pc i) = CL.Skip) ->
  ClassicalSemantics.denote (active_program indices pc tail) = ClassicalSemantics.denote tail.
Proof.
elim: indices=>[|i indices IH] //= H.
have Hi : control_command (pc i) = CL.Skip by apply: H; rewrite inE eqxx.
change (ClassicalSemantics.denote (CL.Sequence (control_command (pc i)) (active_program indices pc tail)) = ClassicalSemantics.denote tail).
rewrite Hi ClassicalSemantics.denote_skip_left; apply: IH=>j Hj; apply: H; by rewrite inE Hj orbT.
Qed.

Lemma active_program_prefix n (pc : 'I_n -> control) xs ys tail :
  (forall i, i \in xs -> control_command (pc i) = CL.Skip) ->
  ClassicalSemantics.denote (active_program (xs ++ ys) pc tail) = ClassicalSemantics.denote (active_program ys pc tail).
Proof. rewrite active_program_cat; exact: active_program_idle. Qed.

Lemma active_program_fold n (pc : 'I_n -> control) indices tail :
  ClassicalSemantics.denote (active_program indices pc tail) =
  ClassicalSemantics.denote (CL.Sequence
    (foldr CL.Sequence CL.Skip [seq control_command (pc i) | i <- indices]) tail).
Proof.
elim: indices=>[|i indices IH].
- change (ClassicalSemantics.denote tail = ClassicalSemantics.denote (CL.Sequence CL.Skip tail)).
  by rewrite ClassicalSemantics.denote_skip_left.
- change (slet (ClassicalSemantics.denote (control_command (pc i)))
    (ClassicalSemantics.denote (active_program indices pc tail)) =
    ClassicalSemantics.denote (CL.Sequence (CL.Sequence (control_command (pc i))
      (foldr CL.Sequence CL.Skip [seq control_command (pc j) | j <- indices])) tail)).
  by rewrite ClassicalSemantics.denote_sequenceA /= IH.
Qed.

Lemma residual_initial n (p : 'I_n -> process) :
  ClassicalSemantics.denote (residual_command p (fun i => Executing (initialization (p i)))) =
  ClassicalSemantics.denote (successful_sequentialize p).
Proof.
rewrite /residual_command active_program_fold /successful_sequentialize /sequentialize
  ClassicalSemantics.denote_sequenceA /network_tail.
by [].
Qed.

Lemma residual_idle n (p : 'I_n -> process) pc :
  (forall i, pc i = Waiting \/ pc i = Stopped) ->
  ClassicalSemantics.denote (residual_command p pc) = ClassicalSemantics.denote (network_tail p).
Proof.
move=>H; apply: active_program_idle=>i _; case: (H i)=>->; by [].
Qed.

Definition residual_state n (p : 'I_n -> process) (c : global_configuration n) : state :=
  match c.1.2 with
  | None => CQState.bottom
  | Some m =>
      match asboolP (c.2 \is denlf) with
      | ReflectT H => CQKernel.apply (ClassicalSemantics.denote (residual_command p c.1.1))
          (CQState.point m (DenLf_Build H))
      | ReflectF _ => CQState.bottom
      end
  end.

Lemma residual_stateE n (p : 'I_n -> process) pc m rho out : rho \is denlf ->
  residual_state p (global_config pc (Some m) rho) out =
  ClassicalSemantics.denote (residual_command p pc) m out rho.
Proof.
move=>Hr; rewrite /residual_state /=; case: asboolP=>[H|H]; last by exfalso; apply: H.
exact: CQKernel.apply_point.
Qed.

Lemma residual_state_bound n (p : 'I_n -> process) c out :
  `|residual_state p c out| <= 1.
Proof.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
apply: denlf_trlf; exact: CQState.component_density.
Qed.

Lemma residual_initial_state n (p : 'I_n -> process) m (rho : 'FD(Hq)) :
  residual_state p (initial_configuration p m rho) =
  CQKernel.apply (ClassicalSemantics.denote (successful_sequentialize p)) (CQState.point m rho).
Proof.
apply/vdistrP=>out; rewrite residual_stateE ?is_denlf // residual_initial.
by rewrite CQKernel.apply_point.
Qed.

Lemma control_after_local p s : control_command (after_local p s) = translate_statement s.
Proof. case: s=>//=; by case: branch_count. Qed.

Lemma active_program_ext n (pc pc' : 'I_n -> control) indices tail :
  (forall i, i \in indices -> control_command (pc i) = control_command (pc' i)) ->
  active_program indices pc tail = active_program indices pc' tail.
Proof.
elim: indices=>[|i indices IH] //= H.
change (CL.Sequence (control_command (pc i)) (active_program indices pc tail) =
  CL.Sequence (control_command (pc' i)) (active_program indices pc' tail)).
congr CL.Sequence.
- apply: H; by rewrite inE eqxx.
- apply: IH=>j Hj; apply: H; by rewrite inE Hj orbT.
Qed.

Lemma active_program_replace n (pc : 'I_n -> control) indices i ctl tail :
  i \notin indices ->
  active_program indices (replace pc i ctl) tail = active_program indices pc tail.
Proof.
move=>Hi; apply: active_program_ext=>j Hj; rewrite replace_other //.
apply/negP=>/eqP E; subst j; by move: Hi; rewrite Hj.
Qed.

Lemma active_program_focus n (pc : 'I_n -> control) xs i ys (p : process) s tail :
  i \notin xs -> i \notin ys ->
  (forall j, j \in xs -> control_command (pc j) = CL.Skip) ->
  ClassicalSemantics.denote (active_program (xs ++ i :: ys) (replace pc i (after_local p s)) tail) =
  ClassicalSemantics.denote (CL.Sequence (translate_statement s) (active_program ys pc tail)).
Proof.
move=>Hx Hy Hprefix.
have Hnew j : j \in xs -> control_command (replace pc i (after_local p s) j) = CL.Skip.
  move=>Hj.
  have Hji : j != i by apply/negP=>/eqP E; subst j; move: Hx; rewrite Hj.
  rewrite (replace_other _ _ Hji); exact: Hprefix Hj.
rewrite (@active_program_prefix n (replace pc i (after_local p s)) xs (i :: ys) tail Hnew).
change (ClassicalSemantics.denote (CL.Sequence (control_command (replace pc i (after_local p s) i))
  (active_program ys (replace pc i (after_local p s)) tail)) =
  ClassicalSemantics.denote (CL.Sequence (translate_statement s) (active_program ys pc tail))).
by rewrite replace_same control_after_local
  (@active_program_replace n pc ys i (after_local p s) tail Hy).
Qed.

Fixpoint first_active n (indices : seq 'I_n) (pc : 'I_n -> control) :=
  if indices is i :: rest then
    if pc i is Executing s then Some (i,s) else first_active rest pc
  else None.

Lemma first_active_some n indices (pc : 'I_n -> control) i s :
  first_active indices pc = Some (i,s) ->
  exists xs ys, indices = xs ++ i :: ys /\ pc i = Executing s /\
    forall j, j \in xs -> control_command (pc j) = CL.Skip.
Proof.
elim: indices=>[|j indices IH] //=.
case Ej: (pc j)=>[t| |] /= H.
- case: H=>[= <- <-]; exists [::],indices; split=>//; split=>//.
- have [xs [ys [E [Hi Hp]]]] := IH H.
  exists (j::xs),ys; split; first by rewrite /= E.
  split=>// k; rewrite inE=>/orP[/eqP->|Hk]; first by rewrite Ej.
  exact: Hp Hk.
- have [xs [ys [E [Hi Hp]]]] := IH H.
  exists (j::xs),ys; split; first by rewrite /= E.
  split=>// k; rewrite inE=>/orP[/eqP->|Hk]; first by rewrite Ej.
  exact: Hp Hk.
Qed.

Lemma first_active_none n indices (pc : 'I_n -> control) :
  first_active indices pc = None ->
  forall i, i \in indices -> pc i = Waiting \/ pc i = Stopped.
Proof.
elim: indices=>[|j indices IH] //=.
case Ej: (pc j)=>[s| |] //= H i; rewrite inE=>/orP[/eqP->|Hi].
- by left.
- exact: IH H i Hi.
- by right.
- exact: IH H i Hi.
Qed.

Lemma uniq_focus (T : eqType) (xs : seq T) i ys :
  uniq (xs ++ i :: ys) -> i \notin xs /\ i \notin ys.
Proof.
rewrite cat_uniq /= negb_or=>/and3P[_ /andP[Hi _] /andP[Hj _]]; by split.
Qed.

Lemma residual_local_focus n (p : 'I_n -> process) pc i s :
  first_active (enum 'I_n) pc = Some (i,s) -> exists tail,
    ClassicalSemantics.denote (residual_command p pc) =
      ClassicalSemantics.denote (CL.Sequence (translate_statement s) tail) /\
    forall t,
      ClassicalSemantics.denote (residual_command p (replace pc i (after_local (p i) t))) =
        ClassicalSemantics.denote (CL.Sequence (translate_statement t) tail).
Proof.
move=>H; have [xs [ys [E [Hi Hp]]]] := first_active_some H.
have HU : uniq (xs ++ i :: ys) by rewrite -E enum_uniq.
have [Hx Hy] := uniq_focus HU.
exists (active_program ys pc (network_tail p)); split.
- have Ecmd : residual_command p pc =
      residual_command p (replace pc i (after_local (p i) s)).
    apply: active_program_ext=>j Hj; rewrite /replace.
    case Ej: (j == i); last by [].
    move/eqP: Ej=>->; by rewrite Hi control_after_local.
  rewrite Ecmd /residual_command E; exact: active_program_focus Hx Hy Hp.
- move=>t; rewrite /residual_command E; exact: active_program_focus Hx Hy Hp.
Qed.
End DistributedResidualSemantics.


Module DistributedLocalCorrespondence.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments DistributedProgress DistributedObservables DistributedDistribution DistributedSequentialization DistributedGuardSemantics DistributedWeighted CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition future_pre (Q : assertion) (c : statement * option cmem) : 'FO(Hq) :=
  if c.2 is Some m then wp (ClassicalSemantics.denote (translate_statement c.1)) Q m else 0%:VF.

Definition step_pre s m Q :=
  wp (SemType (fun _ : unit => local_maps s m))
    (fun i => future_pre Q (@local_control s m i)) tt.

Lemma step_preE s m Q : (step_pre s m Q : 'End(Hq)) =
  sum (fun i => (@local_map s m i)^*o (future_pre Q (@local_control s m i))).
Proof. rewrite /step_pre wpE; by apply: eq_sum=>i; rewrite local_mapsE. Qed.

Lemma translate_append s t : ClassicalSemantics.denote (translate_statement (append s t)) =
  slet (ClassicalSemantics.denote (translate_statement s)) (ClassicalSemantics.denote (translate_statement t)).
Proof. by case: s=>//=; rewrite slet1l. Qed.

Lemma future_pre_append s t st Q :
  future_pre Q (append s t, st) =
  future_pre (wp (ClassicalSemantics.denote (translate_statement t)) Q) (s,st).
Proof.
case: st=>[m|] //=; change (wp (ClassicalSemantics.denote (translate_statement (append s t))) Q m =
  wp (ClassicalSemantics.denote (translate_statement s)) (wp (ClassicalSemantics.denote (translate_statement t)) Q) m).
by rewrite translate_append wp_sequence.
Qed.

Lemma sum_unit (V : normedModType C) (f : unit -> V) : sum f = f tt.
Proof.
rewrite fin_dom_sum (bigD1 tt) //=.
by rewrite big1 ?addr0 // => [[]].
Qed.

Lemma raw_skip Q m : wp_raw (@skip_sem cmem Hq) Q m = (Q m : 'End(Hq)).
Proof. change ((wp skip_sem Q m : 'End(Hq)) = (Q m : 'End(Hq))); by rewrite wp_skip. Qed.
Lemma raw_abort Q m : wp_raw (@abort_sem cmem Hq) Q m = 0.
Proof. change ((wp abort_sem Q m : 'End(Hq)) = 0); by rewrite wp_abort. Qed.
Lemma raw_sunit (F : cmem -> 'QO(Hq)) (u : cmem -> cmem) Q m :
  wp_raw (sunit F u) Q m = (F m)^*o (Q (u m)).
Proof. exact: wp_sunit. Qed.
Lemma raw_sdlet (T : choiceType) (f : cmem -> T -> cmem)
  (g : cmem -> {vdistr T -> 'SO(Hq)}) Q m :
  wp_raw (sdlet f g) Q m = sum (fun i => (g m i)^*o (Q (f m i))).
Proof. exact: wp_sdlet. Qed.
Lemma raw_sequence (K L : ClassicalSemantics.kernel) Q m :
  wp_raw (slet K L) Q m = wp_raw K (wp L Q) m.
Proof.
change ((wp (slet K L) Q m : 'End(Hq)) = (wp K (wp L Q) m : 'End(Hq))).
by rewrite wp_sequence.
Qed.

Lemma atom_pre a m Q :
  wp (ClassicalSemantics.denote (translate_atom a)) Q m = step_pre (Atomic a) m Q.
Proof.
apply/val_inj; change ((wp (ClassicalSemantics.denote (translate_atom a)) Q m : 'End(Hq)) =
  (step_pre (Atomic a) m Q : 'End(Hq))).
rewrite step_preE.
case: a=>[| |t x e|t x p|t q phi|t q U|t u x q M];
  rewrite /= /future_pre /= ?raw_skip ?raw_abort ?raw_sunit ?raw_sdlet.
- by rewrite sum_unit dualso1 soE.
- by rewrite sum_unit dualso1 soE.
- by rewrite sum_unit dualso1 soE.
- by apply: eq_sum=>i; rewrite /sdistr /sdistr_def raw_skip.
- by rewrite sum_unit.
- by rewrite sum_unit.
- by apply: eq_sum=>i; rewrite raw_skip.
Qed.

Lemma wp_row (K L : ClassicalSemantics.kernel) Q m : K m = L m -> wp K Q m = wp L Q m.
Proof.
move=>E; apply/val_inj; change ((wp K Q m : 'End(Hq)) = (wp L Q m : 'End(Hq))).
rewrite !wpE; by apply: eq_sum=>j; rewrite E.
Qed.

Lemma raw_row (K L : ClassicalSemantics.kernel) Q m : K m = L m -> wp_raw K Q m = wp_raw L Q m.
Proof. move=>E; exact: (congr1 (fun A : 'FO(Hq) => (A : 'End(Hq))) (@wp_row K L Q m E)). Qed.

Lemma finished_pre m Q : wp (ClassicalSemantics.denote (translate_statement Finished)) Q m = step_pre Finished m Q.
Proof.
apply/val_inj; change ((wp (ClassicalSemantics.denote (translate_statement Finished)) Q m : 'End(Hq)) =
  (step_pre Finished m Q : 'End(Hq))).
rewrite step_preE /= /future_pre /= !raw_skip.
by rewrite sum_unit dualso1 soE.
Qed.

Lemma local_pre s : statement_wf s -> forall m Q,
  wp (ClassicalSemantics.denote (translate_statement s)) Q m = step_pre s m Q.
Proof.
elim: s=>[|a|s IHs t IHt|n g b IH|n g b IH] /=.
- by move=>_ m Q; apply: finished_pre.
- by move=>_ m Q; apply: atom_pre.
- move=>[Hs Ht] m Q; rewrite wp_sequence (IHs Hs).
  apply/val_inj; change ((step_pre s m (wp (ClassicalSemantics.denote (translate_statement t)) Q) : 'End(Hq)) =
    (step_pre (Sequence s t) m Q : 'End(Hq))).
  rewrite !step_preE /=.
  apply: eq_sum=>i; by rewrite future_pre_append.
- move=>[Hex Hwf] m Q; apply/val_inj.
  change ((wp (ClassicalSemantics.denote (translate_statement (Alternative g b))) Q m : 'End(Hq)) =
    (step_pre (Alternative g b) m Q : 'End(Hq))).
  rewrite step_preE /=.
  case: pickP=>[i Hi|Hnone].
  + have Hi' : i \in enum 'I_n by rewrite mem_enum.
    have Hrow := @conditional_chain_selected n g
      (fun i => translate_statement (b i)) (enum 'I_n) m i Hex Hi' Hi.
    rewrite (@raw_row _ _ Q m Hrow) sum_unit /future_pre /= dualso1 soE.
    by [].
  + have Hdisabled : all (fun bc : expression bool * CL.command => ~~ eval bc.1 m)
      [seq (g i,translate_statement (b i)) | i <- enum 'I_n].
      rewrite all_map; apply/allP=>i _ /=; by rewrite (Hnone i).
    have Hrow := conditional_chain_none Hdisabled.
    by rewrite (@raw_row _ _ Q m Hrow) raw_abort sum_unit /future_pre /= dualso1 soE.
- move=>[Hex Hwf] m Q; apply/val_inj.
  change ((wp (ClassicalSemantics.denote (translate_statement (Repetition g b))) Q m : 'End(Hq)) =
    (step_pre (Repetition g b) m Q : 'End(Hq))).
  rewrite step_preE /=.
  have W := congr1 (fun A : assertion => (A m : 'End(Hq)))
    (CQHoare.pre_while_unfold true (loop_guard g)
      (conditional_chain [seq (g i,translate_statement (b i)) | i <- enum 'I_n]) Q).
  case: pickP=>[i Hi|Hnone].
  + have Hany : enabled g m by apply/enabledP; exists i.
    rewrite /conditional -/(eval (loop_guard g) m) eval_loop_guard Hany in W.
    rewrite /CQHoare.pre /CQHoare.wp_command /= in W.
    rewrite W.
    have Hi' : i \in enum 'I_n by rewrite mem_enum.
    have Hrow := @conditional_chain_selected n g
      (fun j => translate_statement (b j)) (enum 'I_n) m i Hex Hi' Hi.
    rewrite (@raw_row _ _ _ m Hrow).
    by rewrite sum_unit /future_pre /= dualso1 soE raw_sequence.
  + have Hany : enabled g m = false.
      apply/negP=>/enabledP[i Hi]; by move: (Hnone i); rewrite Hi.
    rewrite /conditional -/(eval (loop_guard g) m) eval_loop_guard Hany in W.
    rewrite /CQHoare.pre /CQHoare.wp_command /= in W.
    by rewrite W sum_unit /future_pre /= dualso1 soE raw_skip.
Qed.

Definition pre_observe (Q : assertion) (c : local_configuration) : C :=
  if c.1.2 is Some m then
    \Tr (wp (ClassicalSemantics.denote (translate_statement c.1.1)) Q m \o c.2)
  else 0.

Lemma local_pre_observe s m rho Q : statement_wf s -> rho \is den1lf ->
  pre_observe Q (local_config s (Some m) rho) =
  family_observe (local_successor s m rho) (pre_observe Q).
Proof.
move=>Hwf Hr; change (\Tr (wp (ClassicalSemantics.denote (translate_statement s)) Q m \o rho) =
  family_observe (local_successor s m rho) (pre_observe Q)).
rewrite (local_pre Hwf).
rewrite /step_pre wp_pairing (@local_realization s m rho Hr) /family_observe /local_family /=.
apply: eq_sum=>i; rewrite local_mapsE /future_pre.
case E: (@local_control s m i)=>[r [u|]]; rewrite /pre_observe /local_config /=;
  last by rewrite linear0l linear0 mulr0.
have W := congr1 (fun A : 'End(Hq) =>
  \Tr (wp (ClassicalSemantics.denote (translate_statement r)) Q u \o A))
  (weighted_normalized_output (@local_cp s m i) Hr).
by rewrite linearZr /= linearZ /= in W; symmetry.
Qed.

Definition at_store out (A : 'FO(Hq)) : assertion :=
  fun m => if m == out then A else 0%:VF.

Lemma pairing_at_store (K : ClassicalSemantics.kernel) m out (A : 'FO(Hq)) rho :
  \Tr (wp K (at_store out A) m \o rho) = \Tr (A \o K m out rho).
Proof.
rewrite wp_pairing (fin_supp_sum (S := [fset out]%fset)).
- move=>j; rewrite inE=>/negPf E; by rewrite /at_store E linear0l linear0.
- by rewrite psum1 /at_store eqxx.
Qed.

Definition future (K : ClassicalSemantics.kernel) (c : local_configuration) out : 'End(Hq) :=
  if c.1.2 is Some m then
    slet (ClassicalSemantics.denote (translate_statement c.1.1)) K m out c.2
  else 0.

Lemma future_pairing K c out A :
  pre_observe (wp K (at_store out A)) c = \Tr (A \o future K c out).
Proof.
case: c=>[[s [m|]] rho].
- change (\Tr (wp (ClassicalSemantics.denote (translate_statement s)) (wp K (at_store out A)) m \o rho) =
    \Tr (A \o slet (ClassicalSemantics.denote (translate_statement s)) K m out rho)).
  by rewrite -wp_sequence pairing_at_store.
- by rewrite /pre_observe /future /= linear0r linear0.
Qed.

Lemma future_bound K c out : c.2 \is denlf -> `|future K c out| <= 1.
Proof.
case: c=>[[s [m|]] rho] Hr; rewrite /future /=; last by rewrite normr0.
have Hd : slet (ClassicalSemantics.denote (translate_statement s)) K m out rho \is denlf.
  exact: (qo_denlf _ (DenLf_Build Hr)).
by rewrite psd_trfnorm ?denlf_psd //; exact: denlf_trlf Hd.
Qed.

Lemma local_future_summable s m rho K out : statement_wf s -> rho \is den1lf ->
  summable (fun i => branch_weight (local_successor s m rho) i *:
    future K (branch_value (local_successor s m rho) i) out).
Proof.
move=>Hwf Hr; rewrite (@local_realization s m rho Hr).
apply: (@weighted_summable (local_index s) Hq
  (@Family _ (local_index s) (branch_weight (local_family s m rho)) id)
  (fun i => future K (branch_value (local_family s m rho) i) out)).
- exact: (@DistributedLocalDiamond.local_family_probability s m rho Hwf Hr).
- move=>i; apply: future_bound; apply: den1lf_den.
  exact: (normalized_output_den1 (@local_cp s m i) Hr).
Qed.

Theorem local_future_harmonic s m rho K out : statement_wf s -> rho \is den1lf ->
  future K (local_config s (Some m) rho) out =
  weighted_sum (local_successor s m rho) (fun c => future K c out).
Proof.
move=>Hwf Hr.
have E (A : 'FO(Hq)) :
  \Tr (A \o future K (local_config s (Some m) rho) out) =
  \Tr (A \o weighted_sum (local_successor s m rho) (fun c => future K c out)).
  rewrite -future_pairing (@local_pre_observe s m rho _ Hwf Hr) /weighted_sum.
  rewrite (cvg_linearP_sum (f := fun X : 'End(Hq) => \Tr (A \o X))).
  - by move=>a X Y; rewrite linearPr /= linearP.
  - apply: norm_bounded_cvg; exact: local_future_summable.
  - apply: eq_sum=>i; rewrite future_pairing /= linearZr /= linearZ /=; by [].
apply/eqP; rewrite eq_le; apply/andP; split; apply/lef_trobs=>A.
- by rewrite lftraceC E lftraceC.
- by rewrite lftraceC -E lftraceC.
Qed.

Lemma local_future_residual s m rho K out : residual_wf s -> rho \is den1lf ->
  future K (local_config s (Some m) rho) out =
  weighted_sum (local_successor s m rho) (fun c => future K c out).
Proof.
move=>[->|Hs] Hr; first by rewrite /= weighted_certain.
exact: local_future_harmonic Hs Hr.
Qed.

Lemma future_finished K m rho out :
  future K (local_config Finished (Some m) rho) out = K m out rho.
Proof. change (slet skip_sem K m out rho = K m out rho); by rewrite slet1l. Qed.

Lemma future_failed K s rho out : future K (local_config s None rho) out = 0.
Proof. by []. Qed.
End DistributedLocalCorrespondence.


Module DistributedBoundarySemantics.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant DistributedResults.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma term_first_disabled n (p : 'I_n -> process) m : term p m ->
  first_enabled (rendezvous_indices p) m = None.
Proof.
move=>Hterm; case E: (first_enabled (rendezvous_indices p) m)=>[a|] //.
have [g [c [Ha [Hg HC]]]] := selected_rendezvous_command E.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hnone := forallP (forallP Hterm (first_process a)) (first_branch a).
by rewrite Hj in Hnone.
Qed.

Lemma term_no_rendezvous n (p : 'I_n -> process) m : term p m -> no_rendezvous p m.
Proof.
move=>H; rewrite /no_rendezvous -rendezvous_indicesE; apply: first_enabled_none.
exact: term_first_disabled H.
Qed.

Lemma no_rendezvous_loop_guard n (p : 'I_n -> process) m : no_rendezvous p m ->
  eval (guards_any [seq bc.1 | bc <- rendezvous_commands p]) m = false.
Proof.
rewrite eval_guards_any has_map /no_rendezvous.
change (all (predC (fun bc : expression bool * CL.command => eval bc.1 m))
  (rendezvous_commands p) -> has (fun bc : expression bool * CL.command => eval bc.1 m)
    (rendezvous_commands p) = false).
by rewrite all_predC=>/negbTE.
Qed.

Lemma slet_row_eq (K L M : ClassicalSemantics.kernel) m : K m = L m -> slet K M m = slet L M m.
Proof.
move=>E; apply/vdistrP=>out; change (slet_def K M m out = slet_def L M m out).
by rewrite /slet_def E.
Qed.

Lemma network_tail_blocked n (p : 'I_n -> process) m : no_rendezvous p m ->
  ClassicalSemantics.denote (network_tail p) m = if term p m then skip_sem m else abort_sem m.
Proof.
move=>Hblocked; have Hg := no_rendezvous_loop_guard Hblocked.
have Hw := ClassicalSemantics.denote_while_false (conditional_chain (rendezvous_commands p)) Hg.
change (slet (ClassicalSemantics.denote (CL.While
  (guards_any [seq bc.1 | bc <- rendezvous_commands p])
  (conditional_chain (rendezvous_commands p))))
  (ClassicalSemantics.denote (CL.Conditional (termination_guard p) CL.Skip CL.Abort)) m =
  if term p m then skip_sem m else abort_sem m).
rewrite (slet_row_eq _ Hw) slet1l ClassicalSemantics.denote_conditional eval_termination_guard.
by [].
Qed.

Lemma network_tail_term n (p : 'I_n -> process) m : term p m ->
  ClassicalSemantics.denote (network_tail p) m = skip_sem m.
Proof. move=>H; by rewrite (network_tail_blocked (term_no_rendezvous H)) H. Qed.

Lemma residual_stopped n (p : 'I_n -> process) m rho : rho \is denlf ->
  stopped_valid p (fun _ => Stopped) m ->
  residual_state p (global_config (fun _ : 'I_n => Stopped) (Some m) rho) =
    successful_component (global_config (fun _ : 'I_n => Stopped) (Some m) rho).
Proof.
move=>Hr Hv; have Hterm := stopped_valid_term Hv.
have Hready : ready (fun _ : 'I_n => Stopped) by move=>i; right.
apply/vdistrP=>out; rewrite residual_stateE // (residual_idle p Hready) (network_tail_term Hterm).
rewrite successful_componentE // /successful_at /=.
have Estop : [forall i : 'I_n, asbool ((fun _ : 'I_n => Stopped) i = Stopped)] by apply/forallP=>i; exact/asboolP.
rewrite Estop andbT skip_semE /=.
by rewrite eq_sym; case: (m == out); rewrite soE.
Qed.

Lemma successful_below_residual n (p : 'I_n -> process) c out :
  c.2 \is denlf -> configuration_stopped_valid p c ->
  successful_component c out ⊑ residual_state p c out.
Proof.
case: c=>[[pc [m|]] rho] Hr Hv; last by [].
case E: [forall i, asbool (pc i = Stopped)].
- have Epc : pc = (fun _ => Stopped).
    by apply/funext=>i; move: (forallP E i)=>/asboolP.
  subst pc; by rewrite (residual_stopped Hr (Hv m erefl)).
- rewrite successful_componentE // /successful_at /= E andbF.
  exact: vdistr_ge0.
Qed.

Lemma blocked_residual_harmonic n (p : 'I_n -> process) pc m rho mu out :
  ready pc -> no_rendezvous p m -> rho \is denlf ->
  global_step p (global_config pc (Some m) rho) mu ->
  DistributedWeighted.weighted_sum mu (fun c => residual_state p c out) =
    residual_state p (global_config pc (Some m) rho) out.
Proof.
move=>Hready Hblocked Hr Hstep.
have [i [Hi [Hg ->]]] := blocked_ready_step Hready Hblocked Hstep.
rewrite DistributedWeighted.weighted_certain !residual_stateE //.
by rewrite (residual_idle p Hready) (residual_idle p (ready_replace i Hready)).
Qed.
End DistributedBoundarySemantics.


Module DistributedActivePairs.
(* Ordered active controls after a rendezvous. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedResidualSemantics DistributedSerialScheduler.

Lemma active_program_filter n (pc : 'I_n -> control) indices tail (keep : pred 'I_n) :
  (forall i, i \in indices -> ~~ keep i -> control_command (pc i) = CL.Skip) ->
  ClassicalSemantics.denote (active_program indices pc tail) =
  ClassicalSemantics.denote (active_program (seq.filter keep indices) pc tail).
Proof.
elim: indices=>[|i indices IH] //= H.
case Ei: (keep i).
- change (slet (ClassicalSemantics.denote (control_command (pc i)))
    (ClassicalSemantics.denote (active_program indices pc tail)) =
    slet (ClassicalSemantics.denote (control_command (pc i)))
    (ClassicalSemantics.denote (active_program (seq.filter keep indices) pc tail))).
  congr slet; apply: IH=>j Hj; apply: H; by rewrite inE Hj orbT.
- have Hi : control_command (pc i) = CL.Skip.
    apply: H; by rewrite ?inE ?eqxx ?Ei.
  change (ClassicalSemantics.denote (CL.Sequence (control_command (pc i))
    (active_program indices pc tail)) =
    ClassicalSemantics.denote (active_program (seq.filter keep indices) pc tail)).
  rewrite Hi ClassicalSemantics.denote_skip_left; apply: IH=>j Hj; apply: H.
  by rewrite inE Hj orbT.
Qed.

Lemma filter_pair_order (T : eqType) (indices : seq T) i k :
  uniq indices -> i \in indices -> k \in indices ->
  (seq.index i indices < seq.index k indices)%N ->
  seq.filter (pred2 i k) indices = [::i;k].
Proof.
elim: indices=>[|j indices IH] //= /andP[Hj HU] Hi Hk Ho.
have Hik : i != k by apply/negP=>/eqP E; subst k; move: Ho; rewrite ltnn.
case Eji: (j == i).
- move/eqP: Eji=>E; subst j.
  have Hki : k != i by rewrite eq_sym.
  have Hk' : k \in indices by move: Hk; rewrite inE (negbTE Hki).
  change (i :: seq.filter (pred2 i k) indices = [::i;k]).
  have EF : seq.filter (pred2 i k) indices = seq.filter (pred1 k) indices.
    apply: eq_in_filter=>j Hmem; rewrite /pred2 /pred1.
    have Hji : j != i.
      apply/negP=>/eqP E; subst j; by move: Hj; rewrite Hmem.
    by rewrite /xpred2 /xpred1 /= (negbTE Hji).
  by rewrite EF (filter_pred1_uniq HU Hk').
- case Ejk: (j == k).
  + move/eqP: Ejk=>E; subst j.
    by move: Ho; rewrite /= eqxx.
  + have Hi' : i \in indices by move: Hi; rewrite inE eq_sym Eji.
    have Hk' : k \in indices by move: Hk; rewrite inE eq_sym Ejk.
    have Ho' : (seq.index i indices < seq.index k indices)%N.
      by move: Ho; rewrite /= Eji Ejk ltnS.
    exact: IH HU Hi' Hk' Ho'.
Qed.

Theorem residual_active_pair n (p : 'I_n -> process) pc (i k : 'I_n) s t :
  ready pc -> (i < k)%N ->
  ClassicalSemantics.denote (residual_command p
    (replace (replace pc i (Executing s)) k (Executing t))) =
  ClassicalSemantics.denote (CL.Sequence (translate_statement s)
    (CL.Sequence (translate_statement t) (network_tail p))).
Proof.
move=>Hready Hik.
have Hneq : i != k by apply/eqP=>E; subst k; move: Hik; rewrite ltnn.
have HF j : j \in enum 'I_n -> ~~ pred2 i k j ->
    control_command (replace (replace pc i (Executing s)) k (Executing t) j) = CL.Skip.
  move=>_; rewrite /pred2 /= negb_or=>/andP[Hji Hjk].
  rewrite (replace_other _ _ Hjk) (replace_other _ _ Hji).
  case: (Hready j)=>->; by [].
rewrite /residual_command (@active_program_filter n _ _ _ (pred2 i k) HF).
have Ho : (seq.index i (enum 'I_n) < seq.index k (enum 'I_n))%N.
  by rewrite !index_enum_ord.
have Hi : i \in enum 'I_n by rewrite mem_enum.
have Hk : k \in enum 'I_n by rewrite mem_enum.
rewrite (filter_pair_order (enum_uniq _) Hi Hk Ho).
change (ClassicalSemantics.denote (CL.Sequence
  (control_command (replace (replace pc i (Executing s)) k (Executing t) i))
  (CL.Sequence
    (control_command (replace (replace pc i (Executing s)) k (Executing t) k))
    (network_tail p))) =
  ClassicalSemantics.denote (CL.Sequence (translate_statement s)
    (CL.Sequence (translate_statement t) (network_tail p)))).
by rewrite (replace_other _ _ Hneq) !replace_same.
Qed.
End DistributedActivePairs.


Module DistributedSerialInvariant.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedResidual DistributedStoppedInvariant DistributedSchedulerSemantics DistributedResidualSemantics DistributedWeighted.
Local Notation Hq := 'H[msys]_finset.setT.

Definition serial_invariant (P : program) (c : global_configuration (process_count P)) :=
  @good P c /\ configuration_stopped_valid (processes P) c.
Arguments serial_invariant P c : clear implicits.

Lemma serial_initial (P : program) m rho : rho \is den1lf ->
  serial_invariant P (initial_configuration (processes P) m rho).
Proof.
move=>Hr; split; last exact: initial_stopped_valid.
split=>//; apply: initial_configuration_owned; exact: processes_wf.
Qed.

Lemma serial_global_step (P : program) c mu : serial_invariant P c ->
  global_step (processes P) c mu -> forall i, serial_invariant P (branch_value mu i).
Proof.
move=>[[Hr Ho] Hv] Hstep i; split.
- split; first exact: global_step_normalized Hstep Hr i.
  exact: (@global_step_owned _ _ c mu (@processes_wf P) Ho Hstep i).
- exact: global_step_stopped_valid Ho Hv Hstep i.
Qed.

Lemma serial_collapse (P : program) rho0 c : rho0 \is den1lf ->
  serial_invariant P c -> serial_invariant P (@collapse P rho0 c).
Proof.
move=>Hrho [Hg Hs]; split; first exact: (@collapse_good P rho0 Hrho c Hg).
clear Hg; case: c Hs=>[[pc [m|]] rho] Hs //=; by move=>m'.
Qed.

Lemma serial_projected_step (P : program) rho0 c mu : rho0 \is den1lf ->
  serial_invariant P c -> @projected_step P rho0 c mu ->
  forall i, serial_invariant P (branch_value mu i).
Proof.
move=>Hr Hinv Hstep; case: Hstep Hinv=>[d nu Hd Hglobal|d Hterminal|d Hbad] Hinv i //=.
apply: serial_collapse Hr _; exact: serial_global_step Hinv Hglobal i.
Qed.

Lemma residual_collapse (P : program) rho0 c :
  residual_state (processes P) (@collapse P rho0 c) = residual_state (processes P) c.
Proof. by case: c=>[[pc [m|]] rho]. Qed.

Lemma weighted_residual_collapse (P : program) rho0 mu out :
  weighted_sum (fmap (@collapse P rho0) mu) (fun c => residual_state (processes P) c out) =
  weighted_sum mu (fun c => residual_state (processes P) c out).
Proof. apply: eq_sum=>i; by rewrite /= residual_collapse. Qed.
End DistributedSerialInvariant.


Module DistributedLocalIterations.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments DistributedLocalCorrespondence DistributedSequentialization DistributedGuardSemantics DistributedWeighted ClassicalBoundedUnroll CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition residual_row (F : statement -> ClassicalSemantics.kernel) m (c : statement * option cmem) :=
  if c.2 is Some u then F c.1 u else abort_sem m.

Definition local_unfold (F : statement -> ClassicalSemantics.kernel) (s : statement) : ClassicalSemantics.kernel :=
  SemType (fun m => slet (SemType (fun _ : unit => local_maps s m))
    (SemType (fun i => residual_row F m (@local_control s m i))) tt).

Fixpoint local_iter k s : ClassicalSemantics.kernel :=
  match k with
  | O => if s is Finished then skip_sem else abort_sem
  | S n => local_unfold (local_iter n) s
  end.

Lemma local_unfoldE F s m out : local_unfold F s m out =
  sum (fun i => residual_row F m (@local_control s m i) out :o @local_map s m i).
Proof.
rewrite /local_unfold /= /slet_def; by apply: eq_sum=>i; rewrite local_mapsE.
Qed.

Lemma local_unfold_summable F s m out :
  summable (fun i => residual_row F m (@local_control s m i) out :o @local_map s m i).
Proof.
have E : (fun i => residual_row F m (@local_control s m i) out :o @local_map s m i) =
  (fun i => (SemType (fun i => residual_row F m (@local_control s m i))) i out :o
    (SemType (fun _ : unit => local_maps s m)) tt i).
  by apply/funext=>i; rewrite /= local_mapsE.
rewrite E; exact: slet_in_out_summable.
Qed.

Lemma local_unfold_mono F G : (forall r, kernel_le (F r) (G r)) ->
  forall s, kernel_le (local_unfold F s) (local_unfold G s).
Proof.
move=>FG s m; apply/levdP=>out; rewrite !local_unfoldE; apply: lev_lim.
- apply: norm_bounded_cvg; exact: local_unfold_summable.
- apply: norm_bounded_cvg; exact: local_unfold_summable.
- move=>A; apply: lev_sum=>i _.
  apply: cqwhile.leso_comp2l.
  + exact: (cp_geso0 (@local_cp s m (val i))).
  + rewrite /residual_row; case: (@local_control s m (val i))=>[r [u|]] /=.
    * by move: (FG r u)=>/levdP/(_ out).
    * by [].
Qed.

Lemma local_unfold_finished F : local_unfold F Finished = F Finished.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out; rewrite local_unfoldE /= sum_unit /residual_row /=.
by rewrite comp_so1r.
Qed.

Definition residual_output (F : statement -> ClassicalSemantics.kernel) (c : local_configuration) out :=
  if c.1.2 is Some u then F c.1.1 u out c.2 else 0.

Lemma local_unfold_weighted F s m rho out : rho \is den1lf ->
  local_unfold F s m out rho =
  weighted_sum (local_successor s m rho) (fun c => residual_output F c out).
Proof.
move=>Hr; rewrite local_unfoldE sum_summable_soE.
- apply: norm_bounded_cvg; exact: local_unfold_summable.
- rewrite (@local_realization s m rho Hr) /weighted_sum /local_family /=.
  apply: eq_sum=>i; rewrite comp_soE /residual_row /residual_output /local_config /=.
  case: (@local_control s m i)=>[r [u|]] /=.
  + by rewrite -linearZ (weighted_normalized_output (@local_cp s m i) Hr).
  + by rewrite abort_semE soE scaler0.
Qed.

Lemma local_iter_finished k : local_iter k Finished = skip_sem.
Proof. by elim: k=>[|k IH] //=; rewrite local_unfold_finished IH. Qed.

Lemma local_iter_chain k s : kernel_le (local_iter k s) (local_iter k.+1 s).
Proof.
elim: k s=>[|k IH] s.
- case: s=>[|a|s t|n g b|n g b] /=.
  + by rewrite local_unfold_finished.
  + exact: abort_le.
  + exact: abort_le.
  + exact: abort_le.
  + exact: abort_le.
- exact: local_unfold_mono IH s.
Qed.

Lemma local_iter_mono s j k : (j <= k)%N -> kernel_le (local_iter j s) (local_iter k s).
Proof.
move=>jk; have E : k = (j + (k-j))%N by rewrite subnKC.
rewrite E; elim: (k-j)%N=>[|d IH]; first by rewrite addn0; apply: kernel_le_refl.
rewrite addnS; exact: kernel_le_trans IH (local_iter_chain (j+d) s).
Qed.

Lemma slet_abort_left (K : ClassicalSemantics.kernel) : slet abort_sem K = abort_sem.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out; rewrite abort_semE /= /slet_def.
rewrite (eq_sum (g := fun _ => 0)) ?summable_sum_cst0 // =>i.
by rewrite abort_semE comp_so0r.
Qed.

Lemma local_unfold_sequence F s t :
  local_unfold F (Sequence s t) = local_unfold (fun r => F (append r t)) s.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out; rewrite !local_unfoldE /=.
apply: eq_sum=>i; rewrite /residual_row.
by case: (@local_control s m i)=>[r [u|]].
Qed.

Lemma local_unfold_compose F (K : ClassicalSemantics.kernel) s :
  slet (local_unfold F s) K = local_unfold (fun r => slet (F r) K) s.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out.
pose A := SemType (fun _ : unit => local_maps s m).
pose B := SemType (fun i => residual_row F m (@local_control s m i)).
change (slet (slet A B) K tt out =
  slet A (SemType (fun i => residual_row (fun r => slet (F r) K) m (@local_control s m i))) tt out).
rewrite sletA; congr ((slet A _) tt out).
apply/semtypeP=>i; apply/vdistrP=>out'; rewrite /B /= /slet_def /residual_row.
case E: (@local_control s m i)=>[r [u|]] /=; rewrite E /=.
- by [].
- change (slet abort_sem K m out' = abort_sem m out'); by rewrite slet_abort_left.
Qed.
End DistributedLocalIterations.


Module DistributedLocalHarmonic.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedDistribution DistributedWeighted DistributedLocalActions DistributedProgress DistributedResidualSemantics DistributedLocalCorrespondence.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma future_residual_lift n (p : 'I_n -> process) pc i tail :
  (forall t, ClassicalSemantics.denote (residual_command p (replace pc i (after_local (p i) t))) =
    ClassicalSemantics.denote (CL.Sequence (translate_statement t) tail)) ->
  forall d out, d.2 \is denlf ->
    residual_state p (lift_local p pc i d) out = future (ClassicalSemantics.denote tail) d out.
Proof.
move=>Hfocus [[s [m|]] rho] out Hr; last by [].
rewrite /lift_local residual_stateE // Hfocus /future /=.
by [].
Qed.

Theorem residual_local_harmonic n (p : 'I_n -> process) pc m rho i s out :
  statement_wf s -> rho \is den1lf -> first_active (enum 'I_n) pc = Some (i,s) ->
  residual_state p (global_config pc (Some m) rho) out =
    weighted_sum (fmap (lift_local p pc i) (local_successor s m rho))
      (fun c => residual_state p c out).
Proof.
move=>Hs Hr Hfirst; have [tail [Hsource Hfocus]] := residual_local_focus p Hfirst.
rewrite residual_stateE ?den1lf_den // Hsource.
apply: (eq_trans (@local_future_harmonic s m rho (ClassicalSemantics.denote tail) out Hs Hr)).
apply: eq_sum=>a; congr (_ *: _).
symmetry; apply: (@future_residual_lift n p pc i tail Hfocus _ out).
apply: den1lf_den; exact: (local_step_normalized (local_successor_step Hs m rho) Hr a).
Qed.
End DistributedLocalHarmonic.


Module DistributedRendezvousHarmonic.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant DistributedBoundarySemantics DistributedActivePairs DistributedWeighted.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma first_enabled_has n (p : 'I_n -> process) indices m a :
  first_enabled indices m = Some a ->
  has (fun bc : expression bool * CL.command => eval bc.1 m)
    (pmap (@index_command n p) indices).
Proof.
elim: indices=>[|b indices IH] //=.
case Eb: (index_command b)=>[[g c]|] /=.
- case Eg: (eval g m)=>//=; exact: IH.
- exact: IH.
Qed.

Lemma selected_loop_guard n (p : 'I_n -> process) m a :
  first_enabled (rendezvous_indices p) m = Some a ->
  eval (guards_any [seq bc.1 | bc <- rendezvous_commands p]) m.
Proof.
move=>H; rewrite eval_guards_any has_map -rendezvous_indicesE.
exact: first_enabled_has H.
Qed.

Lemma network_tail_selected n (p : 'I_n -> process) m a g c :
  first_enabled (rendezvous_indices p) m = Some a -> index_command a = Some (g,c) ->
  ClassicalSemantics.denote (network_tail p) m = slet (ClassicalSemantics.denote c) (ClassicalSemantics.denote (network_tail p)) m.
Proof.
move=>Hfirst Ha; have Hg := selected_loop_guard Hfirst.
have [g' [c' [Ha' [Hg' Hchain]]]] := selected_rendezvous_command Hfirst.
rewrite Ha in Ha'; case: Ha'=>[= Eg Ec]; subst g' c'.
pose B := guards_any [seq bc.1 | bc <- rendezvous_commands p].
pose C := conditional_chain (rendezvous_commands p).
pose W := CL.While B C.
pose T := CL.Conditional (termination_guard p) CL.Skip CL.Abort.
have Hw : ClassicalSemantics.denote W m = slet (ClassicalSemantics.denote C) (ClassicalSemantics.denote W) m.
  by rewrite {1}/W {1}ClassicalSemantics.denote_while_unfold ClassicalSemantics.denote_conditional Hg.
change (slet (ClassicalSemantics.denote W) (ClassicalSemantics.denote T) m =
  slet (ClassicalSemantics.denote c) (slet (ClassicalSemantics.denote W) (ClassicalSemantics.denote T)) m).
rewrite (slet_row_eq _ Hw) sletA.
exact: slet_row_eq Hchain.
Qed.

Lemma assignment_sequence t (x : CL.variable t) e (K : ClassicalSemantics.kernel) m :
  slet (ClassicalSemantics.denote (CL.Assign x e)) K m = K (m.[x <- eval e m])%M.
Proof.
apply/vdistrP=>out.
change (slet_def (assign_sem x e) K m out = K (m.[x <- eval e m])%M out).
rewrite /slet_def (fin_supp_sum (S := [fset (m.[x <- eval e m])%M]%fset)).
- move=>j; rewrite inE=>/negPf Hj.
  by rewrite /assign_sem /sunit /= /sunit_def Hj comp_so0r.
- by rewrite psum1 /assign_sem /sunit /= /sunit_def eqxx comp_so1r.
Qed.

Lemma ready_enabled_waiting n (p : 'I_n -> process) pc m i j :
  ready pc -> stopped_valid p pc m -> eval (process_guard (p i) j) m -> pc i = Waiting.
Proof.
move=>Hready Hvalid Hg; have [Hi|Hi] := Hready i; first exact: Hi.
by have Hfalse := Hvalid i Hi j; rewrite Hg in Hfalse.
Qed.

Theorem residual_rendezvous_step n (p : 'I_n -> process) pc m rho a :
  ready pc -> stopped_valid p pc m -> rho \is denlf ->
  first_enabled (rendezvous_indices p) m = Some a ->
  exists mu, global_step p (global_config pc (Some m) rho) mu /\
    forall out, weighted_sum mu (fun c => residual_state p c out) =
      residual_state p (global_config pc (Some m) rho) out.
Proof.
move=>Hready Hv Hr Hfirst.
have [g [c [Ha [Hg Hchain]]]] := selected_rendezvous_command Hfirst.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hi := ready_enabled_waiting Hready Hv Hj.
have Hk := ready_enabled_waiting Hready Hv Hl.
have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
  by case: Hmatch=>t ch x e; exists t, x, e.
case: Hass=>t [x [e He]]; subst effect.
exists (certain (global_config
  (replace (replace pc (first_process a)
    (Executing (process_body (p (first_process a)) (first_branch a))))
    (second_process a) (Executing (process_body (p (second_process a)) (second_branch a))))
  (Some (m.[x <- eval e m])%M) rho)); split.
- exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
- move=>out; rewrite weighted_certain !residual_stateE //.
  rewrite (residual_idle p Hready) (@network_tail_selected n p m a g c Hfirst Ha) HE.
  rewrite (@residual_active_pair n p pc (first_process a) (second_process a)
    (process_body (p (first_process a)) (first_branch a))
    (process_body (p (second_process a)) (second_branch a)) Hready Hik).
  change (slet (ClassicalSemantics.denote (translate_statement (process_body (p (first_process a)) (first_branch a))))
    (slet (ClassicalSemantics.denote (translate_statement (process_body (p (second_process a)) (second_branch a))))
      (ClassicalSemantics.denote (network_tail p))) (m.[x <- eval e m])%M out rho =
    slet (slet (ClassicalSemantics.denote (CL.Assign x e))
      (slet (ClassicalSemantics.denote (translate_statement (process_body (p (first_process a)) (first_branch a))))
        (ClassicalSemantics.denote (translate_statement (process_body (p (second_process a)) (second_branch a))))))
      (ClassicalSemantics.denote (network_tail p)) m out rho).
  by rewrite !sletA assignment_sequence.
Qed.
End DistributedRendezvousHarmonic.


Module DistributedLocalIterationBounds.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments DistributedLocalCorrespondence DistributedLocalIterations DistributedSequentialization DistributedGuardSemantics DistributedWeighted ClassicalBoundedUnroll CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma local_iter_sequence : forall k l s t,
  kernel_le (slet (local_iter k s) (local_iter l t)) (local_iter (k+l+1) (Sequence s t)).
Proof.
elim=>[|k IH] l s t.
- case: s=>[|a|s r|n g b|n g b] /=; try by rewrite slet_abort_left; apply: abort_le.
  rewrite add0n addn1 /= local_unfold_sequence local_unfold_finished slet1l.
  exact: kernel_le_refl.
- rewrite addSn /= local_unfold_compose local_unfold_sequence.
  apply: local_unfold_mono=>r.
  case: r=>[|a|r u|n g b|n g b] /=.
  + rewrite local_iter_finished slet1l.
    apply: local_iter_mono; by rewrite (addnC k l) -addnA leq_addr.
  + exact: IH.
  + exact: IH.
  + exact: IH.
  + exact: IH.
Qed.

Lemma local_iter_append k l s t :
  kernel_le (slet (local_iter k s) (local_iter l t)) (local_iter (k+l+1) (append s t)).
Proof.
case: s=>[|a|s u|n g b|n g b].
- rewrite local_iter_finished slet1l /=; apply: local_iter_mono.
  by rewrite (addnC k l) -addnA leq_addr.
- exact: local_iter_sequence.
- exact: local_iter_sequence.
- exact: local_iter_sequence.
- exact: local_iter_sequence.
Qed.

Lemma kernel_wp_ext (K L : ClassicalSemantics.kernel) :
  (forall Q m, wp K Q m = wp L Q m) -> K = L.
Proof.
move=>E; apply/semtypeP=>m; apply/vdistrP=>out; apply/superopP=>rho.
have ET (A : 'FO(Hq)) : \Tr (A \o K m out rho) = \Tr (A \o L m out rho).
  by rewrite -!pairing_at_store E.
apply/eqP; rewrite eq_le; apply/andP; split; apply/lef_trobs=>A.
- by rewrite lftraceC ET lftraceC.
- by rewrite lftraceC -ET lftraceC.
Qed.

Lemma local_unfold_wp F s Q m :
  wp (local_unfold F s) Q m =
  wp (SemType (fun _ : unit => local_maps s m))
    (fun i => if (@local_control s m i).2 is Some u
      then wp (F (@local_control s m i).1) Q u else 0%:VF) tt.
Proof.
apply/val_inj.
change ((wp (slet (SemType (fun _ : unit => local_maps s m))
  (SemType (fun i => residual_row F m (@local_control s m i)))) Q tt : 'End(Hq)) =
  (wp (SemType (fun _ : unit => local_maps s m))
    (fun i => if (@local_control s m i).2 is Some u
      then wp (F (@local_control s m i).1) Q u else 0%:VF) tt : 'End(Hq))).
rewrite wp_sequence.
congr ((wp _ _ tt) : 'End(Hq)); apply/funext=>i.
case E: (@local_control s m i)=>[r [u|]].
- apply/val_inj.
  change (wp_raw (SemType (fun j => residual_row F m (@local_control s m j))) Q i =
    wp_raw (F r) Q u).
  by rewrite /wp_raw /term /= /residual_row E.
- apply/val_inj.
  change (wp_raw (SemType (fun j => residual_row F m (@local_control s m j))) Q i = 0).
  have -> : wp_raw (SemType (fun j => residual_row F m (@local_control s m j))) Q i =
      wp_raw abort_sem Q m.
    by rewrite /wp_raw /term /= /residual_row E.
  exact: raw_abort.
Qed.

Lemma local_unfold_denote s : residual_wf s ->
  local_unfold (fun r => ClassicalSemantics.denote (translate_statement r)) s = ClassicalSemantics.denote (translate_statement s).
Proof.
move=>[->|Hs]; first by rewrite local_unfold_finished.
apply: kernel_wp_ext=>Q m; rewrite local_unfold_wp.
exact: esym (local_pre Hs m Q).
Qed.

Lemma local_iter_atom a : local_iter 1 (Atomic a) = ClassicalSemantics.denote (translate_atom a).
Proof.
rewrite -(@local_unfold_denote (Atomic a) (or_intror I)).
apply/semtypeP=>m; apply/vdistrP=>out.
change (local_unfold (local_iter 0) (Atomic a) m out =
  local_unfold (fun r => ClassicalSemantics.denote (translate_statement r)) (Atomic a) m out).
rewrite !local_unfoldE.
apply: eq_sum=>i; case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i;
  by rewrite /residual_row /=.
Qed.

Lemma local_iter_alternative k n (g : 'I_n -> expression bool) b m :
  local_iter k.+1 (Alternative g b) m =
    if [pick i | eval (g i) m] is Some i then local_iter k (b i) m else abort_sem m.
Proof.
apply/vdistrP=>out.
change (local_unfold (local_iter k) (Alternative g b) m out =
  (if [pick i | eval (g i) m] is Some i then local_iter k (b i) m else abort_sem m) out).
rewrite local_unfoldE /= sum_unit.
by case: pickP=>[i Hi|Hnone]; rewrite /residual_row /= comp_so1r.
Qed.

Lemma local_iter_repetition k n (g : 'I_n -> expression bool) b m :
  local_iter k.+1 (Repetition g b) m =
    if [pick i | eval (g i) m] is Some i then local_iter k (Sequence (b i) (Repetition g b)) m
    else skip_sem m.
Proof.
apply/vdistrP=>out.
change (local_unfold (local_iter k) (Repetition g b) m out =
  (if [pick i | eval (g i) m] is Some i then local_iter k (Sequence (b i) (Repetition g b)) m
    else skip_sem m) out).
rewrite local_unfoldE /= sum_unit.
case: pickP=>[i Hi|Hnone]; rewrite /residual_row /= comp_so1r //.
by rewrite local_iter_finished.
Qed.


Lemma slet_row (K L M : ClassicalSemantics.kernel) m : K m = L m -> slet K M m = slet L M m.
Proof.
move=>E; apply/vdistrP=>out; change (slet_def K M m out = slet_def L M m out).
by rewrite /slet_def; apply: eq_sum=>i; rewrite E.
Qed.

Lemma finite_local_bound n (b : 'I_n -> statement) (K : 'I_n -> ClassicalSemantics.kernel) :
  (forall i, exists k, kernel_le (K i) (local_iter k (b i))) ->
  exists k, forall i, kernel_le (K i) (local_iter k (b i)).
Proof.
move=>H; pose f i := projT1 (cid (H i)).
exists (\sum_(i : 'I_n) f i)%N=>i.
apply: kernel_le_trans (projT2 (cid (H i))) _.
apply: local_iter_mono.
rewrite (bigD1 i) //=; exact: leq_addr.
Qed.

Lemma bounded_chain k bs :
  bounded_unroll k (conditional_chain bs) =
  conditional_chain [seq (bc.1,bounded_unroll k bc.2) | bc <- bs].
Proof. by elim: bs=>[|[g c] bs IH] //=; rewrite IH. Qed.

Lemma bounded_alternative k n (g : 'I_n -> expression bool) b :
  ClassicalSemantics.denote (bounded_unroll k (translate_statement (Alternative g b))) =
  ClassicalSemantics.denote (conditional_chain [seq (g i,bounded_unroll k (translate_statement (b i))) | i <- enum 'I_n]).
Proof. by rewrite /= bounded_chain -map_comp. Qed.

Lemma bounded_repetition k n (g : 'I_n -> expression bool) b :
  ClassicalSemantics.denote (bounded_unroll k (translate_statement (Repetition g b))) =
  ClassicalSemantics.denote (CL.unroll (loop_guard g)
    (conditional_chain [seq (g i,bounded_unroll k (translate_statement (b i))) | i <- enum 'I_n]) k).
Proof. by rewrite /= bounded_chain -map_comp. Qed.

Fixpoint loop_budget bound k :=
  if k is j.+1 then (bound + loop_budget bound j + 1).+1 else 0%N.

Lemma local_iter_loop_bound n (g : 'I_n -> expression bool) b
    (d : 'I_n -> CL.command) bound : exclusive g ->
  (forall i, kernel_le (ClassicalSemantics.denote (d i)) (local_iter bound (b i))) -> forall k,
  kernel_le (ClassicalSemantics.denote (CL.unroll (loop_guard g)
    (conditional_chain [seq (g i,d i) | i <- enum 'I_n]) k))
    (local_iter (loop_budget bound k) (Repetition g b)).
Proof.
move=>Hex Hb; elim=>[|k IH]; first exact: abort_le.
move=>m; rewrite /loop_budget -/loop_budget local_iter_repetition.
case: pickP=>[i Hi|Hnone].
- have Hany : enabled g m by apply/enabledP; exists i.
  rewrite ClassicalSemantics.denote_conditional eval_loop_guard Hany.
  have Hi' : i \in enum 'I_n by rewrite mem_enum.
  have E := @conditional_chain_selected n g d (enum 'I_n) m i Hex Hi' Hi.
  change (slet (ClassicalSemantics.denote (conditional_chain [seq (g j,d j) | j <- enum 'I_n]))
    (ClassicalSemantics.denote (CL.unroll (loop_guard g) (conditional_chain [seq (g j,d j) | j <- enum 'I_n]) k)) m
    ⊑ local_iter (bound + loop_budget bound k + 1) (Sequence (b i) (Repetition g b)) m).
  rewrite (@slet_row _ _ _ m E).
  apply: (le_trans ((slet_mono (Hb i) IH) m)).
  exact: local_iter_sequence.
- have Hany : enabled g m = false.
    apply/negP=>/enabledP[i Hi]; by move: (Hnone i); rewrite Hi.
  by rewrite ClassicalSemantics.denote_conditional eval_loop_guard Hany.
Qed.

Theorem bounded_local_iter s : statement_wf s -> forall k,
  exists horizon, kernel_le (ClassicalSemantics.denote (bounded_unroll k (translate_statement s))) (local_iter horizon s).
Proof.
elim: s=>[|a|s IHs t IHt|n g b IH|n g b IH].
- by move=>[].
- move=>_ k; exists 1%N; rewrite local_iter_atom.
  case: a=>[| |t x e|t x p|t q phi|t q U|t u x q M]; exact: kernel_le_refl.
- move=>[Hs Ht] k; have [i Hi] := IHs Hs k; have [j Hj] := IHt Ht k.
  exists (i+j+1)%N; change (kernel_le
    (slet (ClassicalSemantics.denote (bounded_unroll k (translate_statement s)))
      (ClassicalSemantics.denote (bounded_unroll k (translate_statement t))))
    (local_iter (i+j+1) (Sequence s t))); apply: (kernel_le_trans (slet_mono Hi Hj)).
  exact: local_iter_sequence.
- move=>[Hex Hwf] k.
  have [bound Hb] := @finite_local_bound n b
    (fun i => ClassicalSemantics.denote (bounded_unroll k (translate_statement (b i))))
    (fun i => IH i (Hwf i) k).
  exists bound.+1; rewrite bounded_alternative=>m; rewrite local_iter_alternative.
  case: pickP=>[i Hi|Hnone].
  + have Hi' : i \in enum 'I_n by rewrite mem_enum.
    rewrite (@conditional_chain_selected n g
      (fun i => bounded_unroll k (translate_statement (b i))) (enum 'I_n) m i Hex Hi' Hi).
    exact: Hb.
  + rewrite conditional_chain_none // all_map; apply/allP=>i _ /=; by rewrite Hnone.
- move=>[Hex Hwf] k.
  have [bound Hb] := @finite_local_bound n b
    (fun i => ClassicalSemantics.denote (bounded_unroll k (translate_statement (b i))))
    (fun i => IH i (Hwf i) k).
  exists (loop_budget bound k).
  rewrite bounded_repetition.
  exact: local_iter_loop_bound Hex Hb k.
Qed.

Theorem local_iter_least_output s (K : ClassicalSemantics.kernel) m out rho V :
  statement_wf s -> 0%:VF ⊑ rho ->
  (forall k, slet (local_iter k s) K m out rho ⊑ V) ->
  slet (ClassicalSemantics.denote (translate_statement s)) K m out rho ⊑ V.
Proof.
move=>Hs Hr HV.
pose f k := slet (ClassicalSemantics.denote (bounded_unroll k (translate_statement s))) K.
have Hchain : ClassicalBoundedLimits.kernel_chain f.
  move=>u j k jk; exact: (slet_mono
    (@bounded_unroll_mono (translate_statement s) j k jk) (kernel_le_refl K) u).
have C := @ClassicalBoundedLimits.sem_limit_cvg f Hchain m.
have E : sem_lim f = slet (ClassicalSemantics.denote (translate_statement s)) K.
  exact: ClassicalBoundedLimits.bounded_unroll_suffix_limit.
rewrite E in C.
have Cp : f k m out @[k --> \oo] -->
    slet (ClassicalSemantics.denote (translate_statement s)) K m out.
  apply: summableE_cvg.
  exact: C.
have Cr : f k m out rho @[k --> \oo] -->
    slet (ClassicalSemantics.denote (translate_statement s)) K m out rho.
  exact: so_cvgl Cp.
have B k : f k m out rho ⊑ V.
  have [h Hh] := bounded_local_iter Hs k.
  apply: (le_trans _ (HV h)); apply: leso_preserve_order=>//.
  by move: ((slet_mono Hh (kernel_le_refl K)) m)=>/levdP/(_ out).
have L := limn_lev (cvgP _ Cr) B.
by rewrite (cvg_lim (@norm_hausdorff _ _) Cr) in L.
Qed.
End DistributedLocalIterationBounds.


Module DistributedNetworkIterations.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedSerialScheduler DistributedResidualSemantics DistributedBoundarySemantics DistributedRendezvousHarmonic DistributedLocalIterations ClassicalBoundedUnroll ClassicalBoundedLimits.
Local Notation Hq := 'H[msys]_finset.setT.

Definition network_iter n (p : 'I_n -> process) k : ClassicalSemantics.kernel :=
  slet (ClassicalSemantics.denote (CL.unroll
    (guards_any [seq bc.1 | bc <- rendezvous_commands p])
    (conditional_chain (rendezvous_commands p)) k))
    (ClassicalSemantics.denote (CL.Conditional (termination_guard p) CL.Skip CL.Abort)).

Lemma network_iter0 n (p : 'I_n -> process) : network_iter p 0 = abort_sem.
Proof. exact: slet_abort_left. Qed.

Lemma network_iterS n (p : 'I_n -> process) k m :
  network_iter p k.+1 m =
  if eval (guards_any [seq bc.1 | bc <- rendezvous_commands p]) m then
    slet (ClassicalSemantics.denote (conditional_chain (rendezvous_commands p))) (network_iter p k) m
  else ClassicalSemantics.denote (CL.Conditional (termination_guard p) CL.Skip CL.Abort) m.
Proof.
rewrite /network_iter.
pose B := guards_any [seq bc.1 | bc <- rendezvous_commands p].
pose C := conditional_chain (rendezvous_commands p).
pose T := CL.Conditional (termination_guard p) CL.Skip CL.Abort.
change (slet (ClassicalSemantics.denote (CL.Conditional B (CL.Sequence C (CL.unroll B C k)) CL.Skip))
  (ClassicalSemantics.denote T) m = if eval B m then
  slet (ClassicalSemantics.denote C) (slet (ClassicalSemantics.denote (CL.unroll B C k)) (ClassicalSemantics.denote T)) m
  else ClassicalSemantics.denote T m).
case E: (eval B m).
- have H : ClassicalSemantics.denote (CL.Conditional B (CL.Sequence C (CL.unroll B C k)) CL.Skip) m =
      slet (ClassicalSemantics.denote C) (ClassicalSemantics.denote (CL.unroll B C k)) m.
    by rewrite ClassicalSemantics.denote_conditional E.
  by rewrite (slet_row_eq _ H) sletA.
- have H : ClassicalSemantics.denote (CL.Conditional B (CL.Sequence C (CL.unroll B C k)) CL.Skip) m = skip_sem m.
    by rewrite ClassicalSemantics.denote_conditional E.
  by rewrite (slet_row_eq _ H) slet1l.
Qed.

Lemma network_iter_selected n (p : 'I_n -> process) k m a g c :
  first_enabled (rendezvous_indices p) m = Some a -> index_command a = Some (g,c) ->
  network_iter p k.+1 m = slet (ClassicalSemantics.denote c) (network_iter p k) m.
Proof.
move=>Hfirst Ha; rewrite network_iterS (selected_loop_guard Hfirst).
have [g' [c' [Ha' [Hg' Hchain]]]] := selected_rendezvous_command Hfirst.
rewrite Ha in Ha'; case: Ha'=>[= Eg Ec]; subst g' c'.
exact: slet_row_eq Hchain.
Qed.

Lemma network_iter_blocked n (p : 'I_n -> process) k m :
  no_rendezvous p m -> network_iter p k.+1 m =
    if term p m then skip_sem m else abort_sem m.
Proof.
move=>H; by rewrite network_iterS (no_rendezvous_loop_guard H)
  ClassicalSemantics.denote_conditional eval_termination_guard.
Qed.

Lemma network_iter_chain n (p : 'I_n -> process) : kernel_chain (network_iter p).
Proof.
move=>m j k Hjk; apply: slet_mono _ (kernel_le_refl _) m.
move=>u; rewrite !ClassicalSemantics.denote_unroll; exact: while_sem_iter_homo Hjk.
Qed.

Lemma network_iter_limit n (p : 'I_n -> process) :
  sem_lim (network_iter p) = ClassicalSemantics.denote (network_tail p).
Proof.
pose B := guards_any [seq bc.1 | bc <- rendezvous_commands p].
pose C := conditional_chain (rendezvous_commands p).
pose T := CL.Conditional (termination_guard p) CL.Skip CL.Abort.
have E : (fun k => slet (ClassicalSemantics.denote (CL.unroll B C k)) (ClassicalSemantics.denote T)) =
    (fun k => slet (while_sem_iter (CL.translate_expr B) (ClassicalSemantics.denote C) k) (ClassicalSemantics.denote T)).
  by apply/funext=>k; rewrite ClassicalSemantics.denote_unroll.
change (sem_lim (fun k => slet (ClassicalSemantics.denote (CL.unroll B C k)) (ClassicalSemantics.denote T)) =
  slet (while_sem (CL.translate_expr B) (ClassicalSemantics.denote C)) (ClassicalSemantics.denote T)).
rewrite E; apply: slet_liml=>m; exact: while_sem_iter_homo.
Qed.

Theorem network_iter_least_output n (p : 'I_n -> process) m out rho V :
  (forall k, network_iter p k m out rho ⊑ V) ->
  ClassicalSemantics.denote (network_tail p) m out rho ⊑ V.
Proof.
move=>HV; have C := @sem_limit_cvg (network_iter p) (network_iter_chain p) m.
rewrite network_iter_limit in C.
have Cp : network_iter p k m out @[k --> \oo] --> ClassicalSemantics.denote (network_tail p) m out.
  apply: summableE_cvg; exact: C.
have Cr : network_iter p k m out rho @[k --> \oo] --> ClassicalSemantics.denote (network_tail p) m out rho.
  exact: so_cvgl Cp.
have L := limn_lev (cvgP _ Cr) HV.
by rewrite (cvg_lim (@norm_hausdorff _ _) Cr) in L.
Qed.
End DistributedNetworkIterations.


Module DistributedBoundaryLower.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant DistributedBoundarySemantics DistributedWeighted DistributedSerialInvariant DistributedSchedulerSemantics DistributedSchedulerResults DistributedGlobalValue DistributedResidual DistributedResults.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma deterministic_step_good (P : program) c d :
  @good P c -> global_step (processes P) c (certain d) -> @good P d.
Proof.
move=>[Hr Ho] Hstep; split.
- exact: (@global_step_normalized _ _ _ _ Hstep Hr tt).
- exact: (@global_step_owned _ _ _ _ (@processes_wf P) Ho Hstep tt).
Qed.

Lemma deterministic_step_value (P : program) rho0 c d :
  @good P c -> global_step (processes P) c (certain d) ->
  @value P rho0 c = @value P rho0 d.
Proof.
move=>Hg Hstep; apply/vdistrP=>out.
have Hproj := @ProjectedGlobal P rho0 c (certain d) Hg Hstep.
have E := @value_bellman P rho0 c _ out Hproj.
change (@value P rho0 c out = weighted_sum (certain (@collapse P rho0 d))
  (fun e => @value P rho0 e out)) in E.
by rewrite weighted_certain value_collapse in E.
Qed.

Lemma deterministic_steps_value (P : program) rho0 c d :
  deterministic_steps (processes P) c d -> @good P c ->
  @value P rho0 c = @value P rho0 d.
Proof.
move=>Hpath; elim: Hpath=>[c0|c0 d0 e0 Hstep Htail IH] Hg.
- reflexivity.
- exact: (eq_trans (deterministic_step_value rho0 Hg Hstep)
    (IH (deterministic_step_good Hg Hstep))).
Qed.

Theorem ready_term_value (P : program) rho0 pc m rho :
  ready pc -> term (processes P) m ->
  @good P (global_config pc (Some m) rho) -> forall out,
  @value P rho0 (global_config pc (Some m) rho) out = skip_sem m out rho.
Proof.
move=>Hready Hterm Hg out.
have Hr : rho \is denlf := den1lf_den (proj1 Hg).
have Hpath := @terminate_stop_list _ (processes P) (enum 'I_(process_count P))
  pc m rho Hready Hterm.
rewrite stop_enum in Hpath.
rewrite (@deterministic_steps_value P rho0 _ _ Hpath Hg).
rewrite (@value_terminal P rho0 _
  (@stopped_terminal _ (processes P) (Some m) rho)).
rewrite (@successful_componentE _ (global_config (fun _ => Stopped) (Some m) rho) out Hr).
rewrite /successful_at /=.
have Estop : [forall i : 'I_(process_count P), asbool ((fun _ => Stopped) i = Stopped)].
  by apply/forallP=>i; exact/asboolP.
rewrite Estop andbT skip_semE /=.
by rewrite eq_sym; case: (out == m); rewrite soE.
Qed.

Corollary ready_term_lower (P : program) rho0 pc m rho :
  ready pc -> term (processes P) m ->
  @good P (global_config pc (Some m) rho) -> forall out,
  skip_sem m out rho ⊑ @value P rho0 (global_config pc (Some m) rho) out.
Proof. move=>Hready Hterm Hg out; by rewrite (ready_term_value rho0 Hready Hterm Hg). Qed.
End DistributedBoundaryLower.


Module DistributedSerialUpper.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant DistributedBoundarySemantics DistributedWeighted DistributedLocalHarmonic DistributedRendezvousHarmonic DistributedSerialInvariant DistributedSchedulerSemantics DistributedSchedulerResults DistributedGlobalValue DistributedResidual DistributedLocalActions.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma residual_successor (P : program) rho0 c : serial_invariant P c ->
  exists mu, @projected_step P rho0 c mu /\
    forall out, weighted_sum mu (fun d => residual_state (processes P) d out) =
      residual_state (processes P) c out.
Proof.
case: c=>[[pc [m|]] rho] [[Hr Ho] Hv].
- have Hg : @good P (global_config pc (Some m) rho) by split.
  case Hfirst: (first_active (enum 'I_(process_count P)) pc)=>[[i s]|].
  + have [xs [ys [E [Hi Hp]]]] := first_active_some Hfirst.
    have Hs : statement_wf s.
      have Hiown := Ho i; rewrite /control_owned /= Hi in Hiown; exact: (proj1 Hiown).
    have Hstep := serial_local_step (processes P) m rho Hs Hi.
    exists (fmap (@collapse P rho0)
      (fmap (lift_local (processes P) pc i) (local_successor s m rho))); split.
    * exact: ProjectedGlobal Hg Hstep.
    * move=>out; rewrite weighted_residual_collapse.
      symmetry; exact: residual_local_harmonic Hs Hr Hfirst.
  + have Hready : ready pc.
      move=>i; have Hi : i \in enum 'I_(process_count P) by rewrite mem_enum.
      exact: (@first_active_none _ _ pc Hfirst i Hi).
    case Hselected: (first_enabled (rendezvous_indices (processes P)) m)=>[a|].
    * have [mu [Hstep HE]] := residual_rendezvous_step Hready (Hv m erefl)
        (den1lf_den Hr) Hselected.
      exists (fmap (@collapse P rho0) mu); split.
      -- exact: ProjectedGlobal Hg Hstep.
      -- move=>out; rewrite weighted_residual_collapse; exact: HE.
    * have Hblocked : no_rendezvous (processes P) m.
        rewrite /no_rendezvous -rendezvous_indicesE; exact: first_enabled_none Hselected.
      case: (pselect (exists mu, global_step (processes P)
        (global_config pc (Some m) rho) mu))=>[[mu Hstep]|Hnone].
      -- exists (fmap (@collapse P rho0) mu); split.
         ++ exact: ProjectedGlobal Hg Hstep.
         ++ move=>out; rewrite weighted_residual_collapse.
            exact: blocked_residual_harmonic Hready Hblocked (den1lf_den Hr) Hstep.
      -- exists (certain (global_config pc (Some m) rho)); split.
         ++ apply: ProjectedTerminal=>mu Hstep; apply: Hnone; by exists mu.
         ++ move=>out; exact: weighted_certain.
- exists (certain (global_config pc None rho)); split.
  + apply: ProjectedTerminal; exact: failure_terminal.
  + move=>out; exact: weighted_certain.
Qed.

Theorem value_below_residual (P : program) rho0 : rho0 \is den1lf ->
  forall c, serial_invariant P c ->
    @value P rho0 c ⊑ residual_state (processes P) c.
Proof.
move=>Hrho c Hc; apply/levdP=>out.
apply: (@value_least_invariant P rho0 out (serial_invariant P)
  (fun d => residual_state (processes P) d out)).
- move=>d; exact: residual_state_bound.
- move=>d [[Hr Ho] Hv]; exact: successful_below_residual (den1lf_den Hr) Hv.
- move=>d Hd; have [mu [Hs HE]] := @residual_successor P rho0 d Hd.
  exists mu; split=>//; split.
  + move=>i Hi; exact: serial_projected_step Hrho Hd Hs i.
  + by rewrite HE.
- exact: Hc.
Qed.

Theorem denote_program_below_sequentialize (P : program) m (rho : 'FD1(Hq)) :
  denote_program P m rho ⊑
    CQKernel.apply (ClassicalSemantics.denote (successful_sequentialize (processes P)))
      (CQState.point m (rho : 'FD(Hq))).
Proof.
have Hinit := @serial_initial P m rho (is_den1lf rho).
have H := @value_below_residual P rho (is_den1lf rho) _ Hinit.
rewrite (@value_denote P rho (initial_configuration (processes P) m rho)
    (is_den1lf rho) (proj2 (proj1 Hinit)))
  residual_initial_state in H.
exact: H.
Qed.
End DistributedSerialUpper.


Module DistributedLocalIterationLimits.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments DistributedLocalCorrespondence DistributedLocalIterations DistributedLocalIterationBounds DistributedSequentialization DistributedGuardSemantics DistributedWeighted ClassicalBoundedUnroll CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma control_wf s : statement_wf s -> forall m i,
  residual_wf (@local_control s m i).1.
Proof.
elim: s=>[|a|s IH t IHt|n g b IH|n g b IH] //=.
- move=>_ m i; case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i;
    by left.
- move=>[Hs Ht] m i; right; apply: append_wf=>//; exact: IH.
- move=>[Hex Hwf] m i; case: pickP=>[j Hj|Hnone]; first by right; apply: Hwf.
  by left.
- move=>[Hex Hwf] m i; case: pickP=>[j Hj|Hnone].
  + right; split; first exact: Hwf.
    by split.
  + by left.
Qed.

Lemma local_iter_upper : forall k s, residual_wf s ->
  kernel_le (local_iter k s) (ClassicalSemantics.denote (translate_statement s)).
Proof.
elim=>[|k IH] s Hs.
- case: s Hs=>[|a|s t|n g b|n g b] Hs; first exact: kernel_le_refl;
    exact: abort_le.
- rewrite -(@local_unfold_denote s Hs).
  change (kernel_le (local_unfold (local_iter k) s)
    (local_unfold (fun r => ClassicalSemantics.denote (translate_statement r)) s)).
  case: Hs=>[->|Hs].
  + rewrite !local_unfold_finished; exact: (IH Finished (or_introl erefl)).
  + move=>m; apply/levdP=>out; rewrite !local_unfoldE; apply: lev_lim.
    * apply: norm_bounded_cvg; exact: local_unfold_summable.
    * apply: norm_bounded_cvg; exact: local_unfold_summable.
    * move=>A; apply: lev_sum=>i _; apply: cqwhile.leso_comp2l.
      -- exact: (cp_geso0 (@local_cp s m (val i))).
      -- have Hr := @control_wf s Hs m (val i).
         rewrite /residual_row.
         case E: (@local_control s m (val i))=>[r [u|]] /=; last by [].
         rewrite E /= in Hr; by move: (IH r Hr u)=>/levdP/(_ out).
Qed.

Theorem local_iter_limit s : residual_wf s ->
  sem_lim (fun k => local_iter k s) = ClassicalSemantics.denote (translate_statement s).
Proof.
move=>Hs.
have Hchain : ClassicalBoundedLimits.kernel_chain (fun k => local_iter k s).
  by move=>m j k jk; exact: (@local_iter_mono s j k jk m).
apply: kernel_le_anti.
- apply: ClassicalBoundedLimits.sem_limit_least; first exact: Hchain.
  move=>k.
  exact: (@local_iter_upper k s Hs).
- case: Hs=>[->|Hs].
  + have E : (fun k => local_iter k Finished) = (fun _ : nat => skip_sem).
      by apply/funext=>k; rewrite local_iter_finished.
    by rewrite E sem_lim_cst; apply: kernel_le_refl.
  + rewrite -ClassicalBoundedLimits.bounded_unroll_limit.
    apply: ClassicalBoundedLimits.sem_limit_least.
      exact: (bounded_unroll_chain (translate_statement s)).
    move=>k.
    have [h Hh] := bounded_local_iter Hs k.
    apply: kernel_le_trans Hh _.
    exact: (@ClassicalBoundedLimits.sem_limit_upper (fun k => local_iter k s) Hchain h).
Qed.

Theorem local_iter_suffix_limit s (K : ClassicalSemantics.kernel) : residual_wf s ->
  sem_lim (fun k => slet (local_iter k s) K) = slet (ClassicalSemantics.denote (translate_statement s)) K.
Proof.
move=>Hs.
have Hchain : ClassicalBoundedLimits.kernel_chain (fun k => local_iter k s).
  by move=>m j k jk; exact: (@local_iter_mono s j k jk m).
by rewrite (slet_liml K Hchain) (@local_iter_limit s Hs).
Qed.

Theorem local_iter_cvg s m : residual_wf s ->
  (local_iter k s m : {summable cmem -> 'SO(Hq)}) @[k --> \oo] -->
    (ClassicalSemantics.denote (translate_statement s) m : {summable cmem -> 'SO(Hq)}).
Proof.
move=>Hs.
have Hchain : ClassicalBoundedLimits.kernel_chain (fun k => local_iter k s).
  by move=>u j k jk; exact: (@local_iter_mono s j k jk u).
have C := @ClassicalBoundedLimits.sem_limit_cvg (fun k => local_iter k s) Hchain m.
by rewrite (@local_iter_limit s Hs) in C.
Qed.
End DistributedLocalIterationLimits.


Module DistributedLocalLower.
(* Finite completed local executions are bounded by the global value. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedDistribution DistributedWeighted DistributedLocalActions DistributedProgress DistributedResidualSemantics DistributedLocalCorrespondence DistributedLocalIterations DistributedSerialScheduler DistributedSerialInvariant DistributedSchedulerSemantics DistributedGlobalValue DistributedResidual DistributedScheduler.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma weighted_mono_branches X (H : chsType) (mu : family X) (f g : X -> 'End(H)) :
  probability_family mu ->
  (forall a, `|f (branch_value mu a)| <= 1) ->
  (forall a, `|g (branch_value mu a)| <= 1) ->
  (forall a, f (branch_value mu a) ⊑ g (branch_value mu a)) ->
  weighted_sum mu f ⊑ weighted_sum mu g.
Proof.
move=>Hm Hf Hg Hfg.
exact: (@weighted_mono (branch_index mu) H
  (@Family _ (branch_index mu) (branch_weight mu) id)
  (fun a => f (branch_value mu a)) (fun a => g (branch_value mu a)) Hm Hf Hg Hfg).
Qed.

Lemma replace_twice n (pc : 'I_n -> control) i a b :
  replace (replace pc i a) i b = replace pc i b.
Proof. apply/funext=>j; rewrite /replace; by case: (j == i). Qed.
Lemma lift_replace n (p : 'I_n -> process) pc i a c :
  lift_local p (replace pc i a) i c = lift_local p pc i c.
Proof. by case: c=>[[s m] rho]; rewrite /lift_local /= replace_twice. Qed.

Lemma lifted_local_step n (p : 'I_n -> process) pc i s m rho : statement_wf s ->
  global_step p (lift_local p pc i (local_config s (Some m) rho))
    (fmap (lift_local p pc i) (local_successor s m rho)).
Proof.
move=>Hs; rewrite (lift_local_start _ _ _ _ _ Hs).
have E : fmap (lift_local p (replace pc i (Executing s)) i) (local_successor s m rho) =
    fmap (lift_local p pc i) (local_successor s m rho).
  congr (@Family _ _ _ _); apply/funext=>a; exact: lift_replace.
rewrite -E; apply: StepParallel; first exact: replace_same.
exact: local_successor_step Hs m rho.
Qed.

Lemma residual_output_bound (F : statement -> ClassicalSemantics.kernel) c out :
  c.2 \is denlf -> `|residual_output F c out| <= 1.
Proof.
case: c=>[[s [m|]] rho] Hr; rewrite /residual_output /=; last by rewrite normr0.
have Hd : F s m out rho \is denlf := qo_denlf _ (DenLf_Build Hr).
by rewrite psd_trfnorm ?denlf_psd //; exact: denlf_trlf Hd.
Qed.

Section Lower.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Local Notation V := (@value P rho0).
Variable pc : 'I_n -> control.
Variable i : 'I_n.

Lemma lifted_residual_wf s m rho :
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  residual_wf s.
Proof.
move=>[[Hr Ho] Hv].
have H := Ho i; rewrite /lift_local /= replace_same in H.
clear Hr Ho Hv.
case: s H=>[|a|s t|k g b|k g b] /= H; first by left.
all: right; exact: (proj1 H).
Qed.

Lemma lifted_bellman s m rho out : statement_wf s ->
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  V (lift_local p pc i (local_config s (Some m) rho)) out =
    weighted_sum (local_successor s m rho) (fun d => V (lift_local p pc i d) out).
Proof.
move=>Hs [Hg Hv].
have Hstep := lifted_local_step p pc i m rho Hs.
have Hproj := @ProjectedGlobal P rho0 _ _ Hg Hstep.
apply: (eq_trans (@value_bellman P rho0 _ _ out Hproj)).
apply: eq_sum=>a; by rewrite /= value_collapse.
Qed.

Variable K : ClassicalSemantics.kernel.
Variable out : cmem.
Hypothesis endpoint_lower : forall m rho,
  serial_invariant P (lift_local p pc i (local_config Finished (Some m) rho)) ->
  K m out rho ⊑ V (lift_local p pc i (local_config Finished (Some m) rho)) out.

Theorem local_iter_lower N : forall s m rho,
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  slet (local_iter N s) K m out rho ⊑
    V (lift_local p pc i (local_config s (Some m) rho)) out.
Proof.
elim: N=>[|N IH] s m rho Hinv.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished slet1l; exact: endpoint_lower Hinv.
  + have E : local_iter 0 s = abort_sem by clear Hinv; case: s Hs.
    rewrite E slet_abort_left abort_semE soE; exact: vdistr_ge0.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished slet1l; exact: endpoint_lower Hinv.
  + have Hr : rho \is den1lf := proj1 (proj1 Hinv).
    have Hstep := lifted_local_step p pc i m rho Hs.
    change (slet (local_unfold (local_iter N) s) K m out rho ⊑
      V (lift_local p pc i (local_config s (Some m) rho)) out).
    rewrite local_unfold_compose (@local_unfold_weighted
      (fun r => slet (local_iter N r) K) s m rho out Hr).
    rewrite (lifted_bellman out Hs Hinv).
    apply: weighted_mono_branches.
    * exact: local_step_probability (local_successor_step Hs m rho) Hr.
    * move=>a; apply: residual_output_bound; apply: den1lf_den.
      exact: local_step_normalized (local_successor_step Hs m rho) Hr a.
    * move=>a; exact: value_bound.
    * move=>a.
      have HI := serial_global_step Hinv Hstep a.
      case E: (branch_value (local_successor s m rho) a)=>[[t [u|]] r].
      -- change (slet (local_iter N t) K u out r ⊑
          V (lift_local p pc i (local_config t (Some u) r)) out).
         apply: IH; by move: HI; rewrite /= E.
      -- change (0%:VF ⊑ V (lift_local p pc i (local_config t None r)) out).
         exact: vdistr_ge0.
Qed.
Theorem translated_local_lower s m rho : statement_wf s ->
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  slet (ClassicalSemantics.denote (translate_statement s)) K m out rho ⊑
    V (lift_local p pc i (local_config s (Some m) rho)) out.
Proof.
move=>Hs Hinv; apply: DistributedLocalIterationBounds.local_iter_least_output Hs _ _.
- rewrite -psdlfE; apply: denlf_psd; apply: den1lf_den.
  exact: (proj1 (proj1 Hinv)).
- move=>N; exact: local_iter_lower Hinv.
Qed.
End Lower.
End DistributedLocalLower.


Module DistributedLocalExpectationLimits.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedScheduler DistributedSequentialization DistributedLocalActions DistributedLocalCorrespondence DistributedLocalIterations DistributedLocalIterationLimits CQAssertion CQPredicate CQExpectation CQExpectationLimits.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma local_iter_apply_cvg s (d : @CQState.state cmem Hq) : residual_wf s ->
  (CQKernel.apply (local_iter k s) d : {summable cmem -> 'End(Hq)}) @[k --> \oo] -->
    (CQKernel.apply (ClassicalSemantics.denote (translate_statement s)) d : {summable cmem -> 'End(Hq)}).
Proof.
move=>Hs; apply: CQKernelLimits.apply_cvg_monotone.
- by move=>m i j ij; exact: (@local_iter_mono s i j ij m).
- by move=>k m; exact: (@local_iter_upper k s Hs m).
- move=>m out; apply: summableE_cvg; exact: (@local_iter_cvg s m Hs).
Qed.

Lemma local_iter_expect_cvg s (A : assertion) (d : @CQState.state cmem Hq) : residual_wf s ->
  expect (wp (local_iter k s) A) d @[k --> \oo] -->
    expect (wp (ClassicalSemantics.denote (translate_statement s)) A) d.
Proof.
move=>Hs; under eq_cvg do rewrite expect_wp.
rewrite expect_wp; apply: expect_cvg; exact: local_iter_apply_cvg Hs.
Qed.

Lemma local_wp_chain s (A : assertion) : semantic_chain (fun k => wp (local_iter k s) A).
Proof.
move=>k; apply: wp_kernel_mono=>m out.
by move: (@local_iter_chain k s m)=>/levdP/(_ out).
Qed.

Lemma local_wp_sup s (A : assertion) : residual_wf s ->
  semantic_sup (fun k => wp (local_iter k s) A) = wp (ClassicalSemantics.denote (translate_statement s)) A.
Proof.
move=>Hs.
have E d : expect (semantic_sup (fun k => wp (local_iter k s) A)) d =
    expect (wp (ClassicalSemantics.denote (translate_statement s)) A) d.
  have C1 := @expect_semantic_sup cmem Hq (fun k => wp (local_iter k s) A) d (local_wp_chain s A).
  have C2 := @local_iter_expect_cvg s A d Hs.
  by rewrite -(cvg_lim (@norm_hausdorff _ _) C1) (cvg_lim (@norm_hausdorff _ _) C2).
apply/funext=>m; apply: effect_eq=>rho.
by move: (E (CQState.point m rho)); rewrite !expect_point.
Qed.

Theorem local_wp_cvg s (A : assertion) m : residual_wf s ->
  (wp (local_iter k s) A m : 'End(Hq)) @[k --> \oo] -->
    (wp (ClassicalSemantics.denote (translate_statement s)) A m : 'End(Hq)).
Proof.
move=>Hs; rewrite -(@local_wp_sup s A Hs).
exact: semantic_sup_cvg (local_wp_chain s A) m.
Qed.

Theorem local_wp_pairing_cvg s (A : assertion) m (rho : 'End(Hq)) : residual_wf s ->
  \Tr (wp (local_iter k s) A m \o rho) @[k --> \oo] -->
    \Tr (wp (ClassicalSemantics.denote (translate_statement s)) A m \o rho).
Proof.
move=>Hs; apply: continuous_cvg; first exact: trlf_continuous.
apply: lfun_comp_cvgl; exact: local_wp_cvg Hs.
Qed.

Theorem local_wp_pairing_least s (A : assertion) m (rho : 'End(Hq)) b :
  residual_wf s -> (forall k, \Tr (wp (local_iter k s) A m \o rho) <= b) ->
  \Tr (wp (ClassicalSemantics.denote (translate_statement s)) A m \o rho) <= b.
Proof.
move=>Hs B.
have C := @local_wp_pairing_cvg s A m rho Hs.
move: (climn_le (cvgP _ C) B).
by rewrite (cvg_lim (@norm_hausdorff _ _) C).
Qed.
End DistributedLocalExpectationLimits.


Module DistributedScalarStopping.
(* Finite completed local executions are bounded by the global value. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedDistribution DistributedWeighted DistributedLocalActions DistributedProgress DistributedResidualSemantics DistributedLocalCorrespondence DistributedLocalIterations DistributedSerialScheduler DistributedSerialInvariant DistributedSchedulerSemantics DistributedResidual DistributedScheduler DistributedObservables DistributedLocalLower DistributedInstruments DistributedLocalIterationBounds CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma observe_mono_branches X (mu : family X) (f g : X -> C) :
  probability_family mu ->
  (forall a, `|f (branch_value mu a)| <= 1) ->
  (forall a, `|g (branch_value mu a)| <= 1) ->
  (forall a, f (branch_value mu a) <= g (branch_value mu a)) ->
  family_observe mu f <= family_observe mu g.
Proof.
move=>Hm Hf Hg Hfg.
pose index_family := @Family (branch_index mu) (branch_index mu) (branch_weight mu) id.
have Sf := @observe_summable _ index_family
  (fun a => f (branch_value mu a)) 1 Hm ler01 Hf.
have Sg := @observe_summable _ index_family
  (fun a => g (branch_value mu a)) 1 Hm ler01 Hg.
rewrite /family_observe; apply: ler_etlim.
- exact: norm_bounded_cvg Sf.
- exact: norm_bounded_cvg Sg.
- move=>A; apply: ler_sum=>a _; apply: ler_wpM2l.
  + exact: (proj1 (proj2 Hm)).
  + exact: Hfg.
Qed.

Definition local_observe (F : statement -> ClassicalSemantics.kernel) (A : assertion)
    (c : local_configuration) : C :=
  if c.1.2 is Some m then \Tr (wp (F c.1.1) A m \o c.2) else 0.

Lemma local_observe_bound F A c : c.2 \is denlf -> `|local_observe F A c| <= 1.
Proof.
case: c=>[[s [m|]] rho] Hr; last by rewrite /local_observe /= normr0.
rewrite /local_observe /=.
rewrite -(@CQExpectation.expect_point cmem Hq (wp (F s) A) m (DenLf_Build Hr)).
by rewrite ger0_norm ?expect_ge0 //; exact: expect_le1.
Qed.

Lemma local_unfold_observe F s m rho A : rho \is den1lf ->
  \Tr (wp (local_unfold F s) A m \o rho) =
    family_observe (local_successor s m rho) (local_observe F A).
Proof.
move=>Hr; rewrite local_unfold_wp wp_pairing
  (@local_realization s m rho Hr) /family_observe /local_family /=.
apply:eq_sum=>a; rewrite local_mapsE.
case E: (@local_control s m a)=>[t [u|]]; rewrite /local_observe /=;
  last by rewrite linear0l linear0 mulr0.
have W := congr1 (fun X : 'End(Hq) => \Tr (wp (F t) A u \o X))
  (weighted_normalized_output (@local_cp s m a) Hr).
by rewrite linearZr /= linearZ /= in W; symmetry.
Qed.

Section Stopping.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable pc : 'I_n -> control.
Variable i : 'I_n.
Variable V : global_configuration n -> C.
Hypothesis Vnonnegative : forall c, serial_invariant P c -> 0 <= V c.
Hypothesis Vbounded : forall c, serial_invariant P c -> `|V c| <= 1.
Hypothesis Vstep : forall c mu, serial_invariant P c -> global_step p c mu ->
  family_observe mu V <= V c.
Variable A : assertion.
Hypothesis endpoint_bound : forall m rho,
  serial_invariant P (lift_local p pc i (local_config Finished (Some m) rho)) ->
  \Tr (A m \o rho) <= V (lift_local p pc i (local_config Finished (Some m) rho)).

Theorem local_iter_stopping N : forall s m rho,
  serial_invariant P (lift_local p pc i (local_config s (Some m) rho)) ->
  \Tr (wp (local_iter N s) A m \o rho) <=
    V (lift_local p pc i (local_config s (Some m) rho)).
Proof.
elim: N=>[|N IH] s m rho Hinv.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished wp_skip; exact: endpoint_bound Hinv.
  + have E : local_iter 0 s = abort_sem by clear Hinv; case: s Hs.
    rewrite E wp_abort linear0l linear0; exact: Vnonnegative Hinv.
- have [Es|Hs] := lifted_residual_wf Hinv.
  + subst s; rewrite local_iter_finished wp_skip; exact: endpoint_bound Hinv.
  + have Hr : rho \is den1lf := proj1 (proj1 Hinv).
    have Hstep := lifted_local_step p pc i m rho Hs.
    change (\Tr (wp (local_unfold (local_iter N) s) A m \o rho) <=
      V (lift_local p pc i (local_config s (Some m) rho))).
    rewrite (@local_unfold_observe (local_iter N) s m rho A Hr).
    apply: (le_trans _ (Vstep Hinv Hstep)).
    change (family_observe (local_successor s m rho) (local_observe (local_iter N) A) <=
      family_observe (local_successor s m rho) (fun d => V (lift_local p pc i d))).
    apply: observe_mono_branches.
    * exact: local_step_probability (local_successor_step Hs m rho) Hr.
    * move=>a; apply: local_observe_bound; apply: den1lf_den.
      exact: local_step_normalized (local_successor_step Hs m rho) Hr a.
    * move=>a; apply: Vbounded; exact: serial_global_step Hinv Hstep a.
    * move=>a; have HI := serial_global_step Hinv Hstep a.
      case E: (branch_value (local_successor s m rho) a)=>[[t [u|]] r].
      -- change (\Tr (wp (local_iter N t) A u \o r) <=
          V (lift_local p pc i (local_config t (Some u) r))).
         apply: IH; by move: HI; rewrite /= E.
      -- change (0 <= V (lift_local p pc i (local_config t None r))).
         apply: Vnonnegative; by move: HI; rewrite /= E.
Qed.
End Stopping.
End DistributedScalarStopping.


Module DistributedActiveLower.
(* Sequential completion of a finite list of active processes. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant DistributedGlobalValue DistributedLocalLower DistributedResidual.
Local Notation Hq := 'H[msys]_finset.setT.

Definition finish_one n (p : 'I_n -> process) (pc : 'I_n -> control) i :=
  if pc i is Executing _ then replace pc i (idle_control (p i)) else pc.
Fixpoint finish_controls n (p : 'I_n -> process) (indices : seq 'I_n) pc :=
  if indices is i :: rest then finish_controls p rest (finish_one p pc i) else pc.

Section Lower.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Local Notation V := (@value P rho0).

Theorem active_program_lower indices : uniq indices ->
  forall pc tail out,
  (forall m rho,
    serial_invariant P (global_config (finish_controls p indices pc) (Some m) rho) ->
    ClassicalSemantics.denote tail m out rho ⊑ V (global_config (finish_controls p indices pc) (Some m) rho) out) ->
  forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
  ClassicalSemantics.denote (active_program indices pc tail) m out rho ⊑
    V (global_config pc (Some m) rho) out.
Proof.
elim: indices=>[|i indices IH] /=.
- move=>_ pc tail out HK m rho Hinv; exact: HK Hinv.
- move=>/andP[Hi HU] pc tail out HK m rho Hinv.
  case Ei: (pc i)=>[s| |].
  + have Hs : statement_wf s.
      have H := (proj2 (proj1 Hinv)) i.
      by move: H; rewrite /= Ei=>[][Hs _].
    have HE u r : lift_local p pc i (local_config s (Some u) r) =
        global_config pc (Some u) r.
      rewrite (lift_local_start _ _ _ _ _ Hs) -Ei replace_current; by [].
    change (slet (ClassicalSemantics.denote (translate_statement s))
      (ClassicalSemantics.denote (active_program indices pc tail)) m out rho ⊑
      V (global_config pc (Some m) rho) out).
    rewrite -HE.
    apply: (@translated_local_lower P rho0 pc i
      (ClassicalSemantics.denote (active_program indices pc tail)) out _ s m rho Hs).
    * move=>u r Hend.
      rewrite lift_local_finished in Hend *.
      rewrite -(@active_program_replace n pc indices i (idle_control (p i)) tail Hi).
      rewrite /finish_one Ei in HK.
      exact: (IH HU (replace pc i (idle_control (p i))) tail out HK u r Hend).
    * by rewrite HE.
  + change (slet skip_sem
      (ClassicalSemantics.denote (active_program indices pc tail)) m out rho ⊑
      V (global_config pc (Some m) rho) out).
    rewrite slet1l.
    rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail out HK m rho Hinv).
  + change (slet skip_sem
      (ClassicalSemantics.denote (active_program indices pc tail)) m out rho ⊑
      V (global_config pc (Some m) rho) out).
    rewrite slet1l.
    rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail out HK m rho Hinv).
Qed.
End Lower.
End DistributedActiveLower.


Module DistributedNetworkLower.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant DistributedBoundarySemantics DistributedWeighted DistributedLocalHarmonic DistributedRendezvousHarmonic DistributedSerialInvariant DistributedSchedulerSemantics DistributedSchedulerResults DistributedGlobalValue DistributedResidual DistributedLocalActions DistributedLocalLower DistributedScheduler DistributedNetworkIterations DistributedBoundaryLower.
Local Notation Hq := 'H[msys]_finset.setT.

Section Lower.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Local Notation V := (@value P rho0).

Lemma local_pair_lower pc (i k : 'I_n) s t (K : ClassicalSemantics.kernel) out :
  i != k -> pc i = Waiting -> pc k = Waiting ->
  idle_control (p i) = Waiting -> idle_control (p k) = Waiting ->
  statement_wf s -> statement_wf t ->
  (forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
    K m out rho ⊑ V (global_config pc (Some m) rho) out) ->
  forall m rho,
    serial_invariant P (global_config
      (replace (replace pc i (Executing s)) k (Executing t)) (Some m) rho) ->
    slet (ClassicalSemantics.denote (translate_statement s))
      (slet (ClassicalSemantics.denote (translate_statement t)) K) m out rho ⊑
      V (global_config (replace (replace pc i (Executing s)) k (Executing t))
        (Some m) rho) out.
Proof.
move=>Hik Hi Hk HidleI HidleK Hs Ht HK m rho Hinv.
have Efirst u r : lift_local p (replace pc k (Executing t)) i
    (local_config s (Some u) r) =
    global_config (replace (replace pc i (Executing s)) k (Executing t)) (Some u) r.
  rewrite lift_local_start //; congr (global_config _ _ _); exact: esym (replace_commute _ _ _ Hik).
have Eend u r : lift_local p (replace pc k (Executing t)) i
    (local_config Finished (Some u) r) =
    global_config (replace pc k (Executing t)) (Some u) r.
  rewrite lift_local_finished HidleI.
  have E : replace pc k (Executing t) i = Waiting by rewrite replace_other // Hi.
  by rewrite -{1}E replace_current.
have Esecond u r : lift_local p pc k (local_config t (Some u) r) =
    global_config (replace pc k (Executing t)) (Some u) r.
  exact: lift_local_start Ht.
have Efinished u r : lift_local p pc k (local_config Finished (Some u) r) =
    global_config pc (Some u) r.
  by rewrite lift_local_finished HidleK -Hk replace_current.
rewrite -Efirst in Hinv *.
apply: (@translated_local_lower P rho0 (replace pc k (Executing t)) i
  (slet (ClassicalSemantics.denote (translate_statement t)) K) out _ s m rho Hs Hinv).
move=>u r Hentry; rewrite Eend in Hentry *.
rewrite -Esecond in Hentry *.
apply: (@translated_local_lower P rho0 pc k K out _ t u r Ht Hentry).
move=>v q Hdone; rewrite Efinished in Hdone *; exact: HK Hdone.
Qed.


Theorem network_iter_lower pc : ready pc -> forall k m rho out,
  serial_invariant P (global_config pc (Some m) rho) ->
  network_iter p k m out rho ⊑ V (global_config pc (Some m) rho) out.
Proof.
move=>Hready; elim=>[|k IH] m rho out Hinv.
- rewrite network_iter0 abort_semE soE; exact: vdistr_ge0.
- case Hfirst: (first_enabled (rendezvous_indices p) m)=>[a|].
  + have [g [c [Ha [Hg Hchain]]]] := selected_rendezvous_command Hfirst.
    have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
    have Hi := ready_enabled_waiting Hready (proj2 Hinv m erefl) Hj.
    have Hk := ready_enabled_waiting Hready (proj2 Hinv m erefl) Hl.
    have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
      by case: Hmatch=>t ch x e; exists t, x, e.
    case: Hass=>t [x [e He]]; subst effect.
    pose pc' := replace (replace pc (first_process a)
      (Executing (process_body (p (first_process a)) (first_branch a))))
      (second_process a) (Executing (process_body (p (second_process a)) (second_branch a))).
    pose m' := (m.[x <- eval e m])%M.
    have Hstep : global_step p (global_config pc (Some m) rho)
        (certain (global_config pc' (Some m') rho)).
      exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
    have Hnext := serial_global_step Hinv Hstep tt.
    have Hvalue : V (global_config pc (Some m) rho) out =
        V (global_config pc' (Some m') rho) out.
      have E := @deterministic_step_value P rho0
        (global_config pc (Some m) rho) (global_config pc' (Some m') rho)
        (proj1 Hinv) Hstep.
      by move: E=>/vdistrP/(_ out).
    rewrite (@network_iter_selected n p k m a g c Hfirst Ha) HE.
    change (slet (slet (ClassicalSemantics.denote (CL.Assign x e))
      (slet (ClassicalSemantics.denote (translate_statement (process_body (p (first_process a)) (first_branch a))))
        (ClassicalSemantics.denote (translate_statement (process_body (p (second_process a)) (second_branch a))))))
      (network_iter p k) m out rho ⊑ V (global_config pc (Some m) rho) out).
    rewrite !sletA assignment_sequence Hvalue.
    have Hneq : first_process a != second_process a.
      by apply/eqP=>E; move: Hik; rewrite E ltnn.
    have Hs : statement_wf (process_body (p (first_process a)) (first_branch a)).
      exact: (proj1 (@body_owned (p (first_process a)) (first_branch a)
        (@processes_wf P (first_process a)))).
    have Ht : statement_wf (process_body (p (second_process a)) (second_branch a)).
      exact: (proj1 (@body_owned (p (second_process a)) (second_branch a)
        (@processes_wf P (second_process a)))).
    apply: (@local_pair_lower pc (first_process a) (second_process a)
      (process_body (p (first_process a)) (first_branch a))
      (process_body (p (second_process a)) (second_branch a))
      (network_iter p k) out Hneq Hi Hk
      (idle_control_waiting (first_branch a)) (idle_control_waiting (second_branch a))
      Hs Ht).
    * move=>u r Hr; exact: IH u r out Hr.
    * exact: Hnext.
  + have Hblocked : no_rendezvous p m.
      rewrite /no_rendezvous -rendezvous_indicesE; exact: first_enabled_none Hfirst.
    rewrite (network_iter_blocked k Hblocked).
    case Hterm: (term p m); last by rewrite abort_semE soE; exact: vdistr_ge0.
    rewrite -(@ready_term_value P rho0 pc m rho Hready Hterm (proj1 Hinv) out).
    exact: lexx.
Qed.

Theorem network_tail_lower pc : ready pc -> forall m rho out,
  serial_invariant P (global_config pc (Some m) rho) ->
  ClassicalSemantics.denote (network_tail p) m out rho ⊑ V (global_config pc (Some m) rho) out.
Proof.
move=>Hready m rho out Hinv; apply: network_iter_least_output=>k.
exact: network_iter_lower Hready k m rho out Hinv.
Qed.

End Lower.
End DistributedNetworkLower.


Module DistributedScalarStoppingLimit.
(* Finite completed local executions are bounded by the global value. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant DistributedLocalLower DistributedScalarStopping DistributedLocalExpectationLimits DistributedDistribution CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem translated_local_stopping (P : program)
    (pc : 'I_(process_count P) -> control) i
    (V : global_configuration (process_count P) -> C) (A : assertion) :
  (forall c, serial_invariant P c -> 0 <= V c) ->
  (forall c, serial_invariant P c -> `|V c| <= 1) ->
  (forall c mu, serial_invariant P c -> global_step (processes P) c mu ->
    family_observe mu V <= V c) ->
  (forall m rho,
    serial_invariant P (lift_local (processes P) pc i (local_config Finished (Some m) rho)) ->
    \Tr (A m \o rho) <= V (lift_local (processes P) pc i (local_config Finished (Some m) rho))) ->
  forall s m rho,
    serial_invariant P (lift_local (processes P) pc i (local_config s (Some m) rho)) ->
    \Tr (wp (ClassicalSemantics.denote (translate_statement s)) A m \o rho) <=
      V (lift_local (processes P) pc i (local_config s (Some m) rho)).
Proof.
move=>Hnonneg Hbounded Hstep Hend s m rho Hinv.
apply: local_wp_pairing_least; first exact: lifted_residual_wf Hinv.
move=>N; exact: (@local_iter_stopping P pc i V Hnonneg Hbounded Hstep A Hend N s m rho Hinv).
Qed.
End DistributedScalarStoppingLimit.


Module DistributedControlCompletion.
(* Readiness after completing every listed active process. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSerialScheduler DistributedActiveLower.

Definition control_ready (c : control) := c = Waiting \/ c = Stopped.

Lemma idle_ready p : control_ready (idle_control p).
Proof. rewrite /idle_control /after_local; case: branch_count=>[|n]; by [right|left]. Qed.

Lemma finish_one_ready n (p : 'I_n -> process) pc i j :
  control_ready (pc j) -> control_ready (finish_one p pc i j).
Proof.
move=>H; rewrite /finish_one; case: (pc i)=>[s| |] //.
rewrite /replace; case: (j == i); first exact: idle_ready.
exact: H.
Qed.

Lemma finish_one_self_ready n (p : 'I_n -> process) pc i :
  control_ready (finish_one p pc i i).
Proof.
rewrite /finish_one; case Ei: (pc i)=>[s| |].
- rewrite replace_same; exact: idle_ready.
- by left.
- by right.
Qed.

Lemma finish_controls_ready_at n (p : 'I_n -> process) indices pc j :
  control_ready (pc j) \/ j \in indices ->
  control_ready (finish_controls p indices pc j).
Proof.
elim: indices pc=>[|i indices IH] pc /=.
- by case=>[H|].
- case=>[H|Hmem].
  + apply: IH; left; exact: finish_one_ready H.
  + move: Hmem; rewrite inE=>/orP[/eqP E|Hj].
    * subst j; apply: IH; left; exact: finish_one_self_ready.
    * apply: IH; by right.
Qed.

Lemma finish_controls_ready n (p : 'I_n -> process) pc :
  ready (finish_controls p (enum 'I_n) pc).
Proof.
move=>j; apply: finish_controls_ready_at; right; by rewrite mem_enum.
Qed.
End DistributedControlCompletion.


Module DistributedActiveStopping.
(* Sequential completion of a finite list of active processes. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant DistributedLocalLower DistributedResidual DistributedActiveLower DistributedScalarStoppingLimit DistributedDistribution CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Section Stopping.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable V : global_configuration n -> C.
Hypothesis Vnonnegative : forall c, serial_invariant P c -> 0 <= V c.
Hypothesis Vbounded : forall c, serial_invariant P c -> `|V c| <= 1.
Hypothesis Vstep : forall c mu, serial_invariant P c -> global_step p c mu ->
  family_observe mu V <= V c.

Theorem active_program_stopping indices : uniq indices ->
  forall pc tail (A : assertion),
  (forall m rho,
    serial_invariant P (global_config (finish_controls p indices pc) (Some m) rho) ->
    \Tr (wp (ClassicalSemantics.denote tail) A m \o rho) <=
      V (global_config (finish_controls p indices pc) (Some m) rho)) ->
  forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
  \Tr (wp (ClassicalSemantics.denote (active_program indices pc tail)) A m \o rho) <=
    V (global_config pc (Some m) rho).
Proof.
elim: indices=>[|i indices IH] /=.
- move=>_ pc tail A HK m rho Hinv; exact: HK Hinv.
- move=>/andP[Hi HU] pc tail A HK m rho Hinv.
  case Ei: (pc i)=>[s| |].
  + have Hs : statement_wf s.
      have H := (proj2 (proj1 Hinv)) i.
      by move: H; rewrite /= Ei=>[][Hs _].
    have HE u r : lift_local p pc i (local_config s (Some u) r) =
        global_config pc (Some u) r.
      rewrite (lift_local_start _ _ _ _ _ Hs) -Ei replace_current; by [].
    change (\Tr (wp (slet (ClassicalSemantics.denote (translate_statement s))
      (ClassicalSemantics.denote (active_program indices pc tail))) A m \o rho) <=
      V (global_config pc (Some m) rho)).
    rewrite wp_sequence -HE.
    apply: (@translated_local_stopping P pc i V
      (wp (ClassicalSemantics.denote (active_program indices pc tail)) A)
      Vnonnegative Vbounded Vstep _ s m rho).
    * move=>u r Hend.
      rewrite lift_local_finished in Hend *.
      rewrite -(@active_program_replace n pc indices i (idle_control (p i)) tail Hi).
      rewrite /finish_one Ei in HK.
      exact: (IH HU (replace pc i (idle_control (p i))) tail A HK u r Hend).
    * by rewrite HE.
  + change (\Tr (wp (slet skip_sem
      (ClassicalSemantics.denote (active_program indices pc tail))) A m \o rho) <=
      V (global_config pc (Some m) rho)).
    rewrite slet1l; rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail A HK m rho Hinv).
  + change (\Tr (wp (slet skip_sem
      (ClassicalSemantics.denote (active_program indices pc tail))) A m \o rho) <=
      V (global_config pc (Some m) rho)).
    rewrite slet1l; rewrite /finish_one Ei in HK.
    exact: (IH HU pc tail A HK m rho Hinv).
Qed.
Corollary active_commands_stopping indices : uniq indices -> forall pc (A : assertion),
  (forall m rho,
    serial_invariant P (global_config (finish_controls p indices pc) (Some m) rho) ->
    \Tr (A m \o rho) <= V (global_config (finish_controls p indices pc) (Some m) rho)) ->
  forall m rho, serial_invariant P (global_config pc (Some m) rho) ->
  \Tr (wp (ClassicalSemantics.denote (active_program indices pc CL.Skip)) A m \o rho) <=
    V (global_config pc (Some m) rho).
Proof.
move=>HU pc A Hend m rho Hinv.
apply: (@active_program_stopping indices HU pc CL.Skip A _ m rho Hinv).
move=>u r Hr; rewrite wp_skip; exact: Hend Hr.
Qed.
End Stopping.
End DistributedActiveStopping.


Module DistributedCorrespondence.
(* Operational/serialized denotational equality for distributed networks. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedResidualSemantics DistributedSerialScheduler DistributedSerialInvariant DistributedGlobalValue DistributedLocalLower DistributedResidual DistributedActiveLower DistributedControlCompletion DistributedNetworkLower DistributedSerialUpper DistributedSchedulerResults.
Local Notation Hq := 'H[msys]_finset.setT.

Theorem residual_below_value (P : program) rho0 pc m rho out :
  serial_invariant P (global_config pc (Some m) rho) ->
  ClassicalSemantics.denote (residual_command (processes P) pc) m out rho ⊑
    @value P rho0 (global_config pc (Some m) rho) out.
Proof.
move=>Hinv; apply: (@active_program_lower P rho0 (enum 'I_(process_count P))
  (enum_uniq _) pc (network_tail (processes P)) out _ m rho Hinv).
move=>u r Hend.
exact: (@network_tail_lower P rho0
  (finish_controls (processes P) (enum 'I_(process_count P)) pc)
  (@finish_controls_ready (process_count P) (processes P) pc) u r out Hend).
Qed.

Theorem residual_value (P : program) rho0 : rho0 \is den1lf ->
  forall c, serial_invariant P c ->
  residual_state (processes P) c = @value P rho0 c.
Proof.
move=>Hrho c Hinv; apply/vdistrP=>out; apply/eqP; rewrite eq_le; apply/andP; split.
- case: c Hinv=>[[pc [m|]] rho] Hinv.
  + have Hr : rho \is denlf.
      apply: den1lf_den; exact: (proj1 (proj1 Hinv)).
    rewrite (@residual_stateE (process_count P) (processes P) pc m rho out Hr).
    exact: residual_below_value Hinv.
  + change (0%:VF ⊑ @value P rho0 (global_config pc None rho) out).
    exact: vdistr_ge0.
- by move: (@value_below_residual P rho0 Hrho c Hinv)=>/levdP/(_ out).
Qed.

Theorem denote_program_sequentialize (P : program) m (rho : 'FD1(Hq)) :
  denote_program P m rho =
    CQKernel.apply (ClassicalSemantics.denote (successful_sequentialize (processes P)))
      (CQState.point m (rho : 'FD(Hq))).
Proof.
have Hinit := @serial_initial P m rho (is_den1lf rho).
have E := @residual_value P rho (is_den1lf rho)
  (initial_configuration (processes P) m rho) Hinit.
rewrite residual_initial_state
  (@value_denote P rho (initial_configuration (processes P) m rho)
    (is_den1lf rho) (proj2 (proj1 Hinit))) in E.
exact: esym E.
Qed.

Theorem denote_program_point (P : program) m (rho : 'FD1(Hq)) out :
  denote_program P m rho out =
    ClassicalSemantics.denote (successful_sequentialize (processes P)) m out rho.
Proof. by rewrite denote_program_sequentialize CQKernel.apply_point. Qed.
End DistributedCorrespondence.


Module DistributedRankingControls.
(* Ordered active controls after a rendezvous. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedResidualSemantics DistributedSerialScheduler DistributedActivePairs DistributedActiveLower DistributedControlCompletion.

Definition completed_control (p : process) (c : control) :=
  if c is Executing _ then idle_control p else c.

Lemma completed_ready p c : control_ready c -> completed_control p c = c.
Proof. by case=>->. Qed.
Lemma completed_idle p : completed_control p (idle_control p) = idle_control p.
Proof. apply: completed_ready; exact: idle_ready. Qed.

Lemma finish_one_completed n (p : 'I_n -> process) pc i j :
  completed_control (p j) (finish_one p pc i j) = completed_control (p j) (pc j).
Proof.
rewrite /finish_one; case Ei: (pc i)=>[s| |] //.
rewrite /replace; case Eji: (j == i)=>//.
move/eqP: Eji=>E; subst j; by rewrite Ei /= completed_idle.
Qed.

Lemma finish_controls_completed n (p : 'I_n -> process) indices pc j :
  completed_control (p j) (finish_controls p indices pc j) =
  completed_control (p j) (pc j).
Proof.
elim: indices pc=>[|i indices IH] pc //=.
by rewrite IH finish_one_completed.
Qed.

Lemma finish_controls_idle n (p : 'I_n -> process) pc :
  (forall j, completed_control (p j) (pc j) = idle_control (p j)) ->
  finish_controls p (enum 'I_n) pc = (fun j => idle_control (p j)).
Proof.
move=>H; apply/funext=>j.
rewrite -(@completed_ready (p j) _ (finish_controls_ready p pc j)).
by rewrite finish_controls_completed H.
Qed.

Lemma finish_active_pair n (p : 'I_n -> process) i k s t :
  finish_controls p (enum 'I_n)
    (replace (replace (fun j => idle_control (p j)) i (Executing s)) k (Executing t)) =
    (fun j => idle_control (p j)).
Proof.
apply: finish_controls_idle=>j; rewrite /replace.
case: (j == k)=>//; case: (j == i)=>//; exact: completed_idle.
Qed.

Theorem active_program_pair n (pc : 'I_n -> control) (i k : 'I_n) s t tail :
  ready pc -> (i < k)%N ->
  ClassicalSemantics.denote (active_program (enum 'I_n)
    (replace (replace pc i (Executing s)) k (Executing t)) tail) =
  ClassicalSemantics.denote (CL.Sequence (translate_statement s)
    (CL.Sequence (translate_statement t) tail)).
Proof.
move=>Hready Hik.
have Hneq : i != k by apply/eqP=>E; subst k; move: Hik; rewrite ltnn.
have HF j : j \in enum 'I_n -> ~~ pred2 i k j ->
    control_command (replace (replace pc i (Executing s)) k (Executing t) j) = CL.Skip.
  move=>_; rewrite /pred2 /= negb_or=>/andP[Hji Hjk].
  rewrite (replace_other _ _ Hjk) (replace_other _ _ Hji).
  case: (Hready j)=>->; by [].
rewrite (@active_program_filter n _ _ _ (pred2 i k) HF).
have Ho : (seq.index i (enum 'I_n) < seq.index k (enum 'I_n))%N by rewrite !index_enum_ord.
have Hi : i \in enum 'I_n by rewrite mem_enum.
have Hk : k \in enum 'I_n by rewrite mem_enum.
rewrite (filter_pair_order (enum_uniq _) Hi Hk Ho).
change (ClassicalSemantics.denote (CL.Sequence
  (control_command (replace (replace pc i (Executing s)) k (Executing t) i))
  (CL.Sequence (control_command (replace (replace pc i (Executing s)) k (Executing t) k)) tail)) =
  ClassicalSemantics.denote (CL.Sequence (translate_statement s) (CL.Sequence (translate_statement t) tail))).
by rewrite (replace_other _ _ Hneq) !replace_same.
Qed.
End DistributedRankingControls.


Module DistributedAllRendezvous.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOperational DistributedSequentialization DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant DistributedBoundarySemantics DistributedWeighted DistributedSerialInvariant DistributedSchedulerSemantics DistributedGlobalValue DistributedResidual DistributedRendezvousHarmonic DistributedCorrespondence DistributedBoundaryLower DistributedActivePairs CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma superop_normalized_ext (U V : chsType) (F G : 'SO(U,V)) :
  (forall rho : 'FD1(U), F rho = G rho) -> F = G.
Proof.
move=>H; apply/(proj1 (so_psdP F G))=>A HA.
have Hp : 0 <= \Tr A := psdlf_trlf HA.
case Hpos: (0 < \Tr A).
- have Hnorm : (\Tr A)^-1 *: A \is den1lf.
    apply/den1lfP; split.
    + apply: psdlfZ; first by rewrite invr_ge0.
      exact: HA.
    + by rewrite linearZ /= mulVf ?gt_eqF.
  have Htest := H (Den1Lf_Build Hnorm).
  have E := congr1 (fun X : 'End(V) => \Tr A *: X) Htest.
  change (\Tr A *: F ((\Tr A)^-1 *: A) = \Tr A *: G ((\Tr A)^-1 *: A)) in E.
  by rewrite !linearZ /= !scalerA mulVf ?gt_eqF ?scale1r in E.
- have Htr : \Tr A = 0.
    by move: Hp; rewrite le_eqVlt Hpos orbF eq_sym=>/eqP.
  have EA : A = 0.
    apply/eqP/trlf0_eq0; split.
    + by rewrite -psdlfE.
    + exact: Htr.
  by rewrite EA !linear0.
Qed.

Lemma idle_serial_invariant (P : program) m rho : rho \is den1lf ->
  serial_invariant P (idle_configuration (processes P) m rho).
Proof.
move=>Hr; split.
- split=>//; exact: idle_owned.
- move=>m' [= <-] i Hstop j.
  exfalso; apply: (@after_local_stopped_no_branch (processes P i) Finished j).
  exact: Hstop.
Qed.

Theorem enabled_tail_normalized (P : program) m (rho : 'FD1(Hq))
    (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) -> eval g m -> forall out,
  ClassicalSemantics.denote (network_tail (processes P)) m out rho =
    slet (ClassicalSemantics.denote c) (ClassicalSemantics.denote (network_tail (processes P))) m out rho.
Proof.
move=>Ha Hg out.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
  by case: Hmatch=>t ch x e; exists t, x, e.
case: Hass=>t [x [e He]]; subst effect.
pose pc := fun i => idle_control (processes P i).
pose src := global_config pc (Some m) (rho : 'End(Hq)).
pose dst := global_config
  (replace (replace pc (first_process a)
    (Executing (process_body (processes P (first_process a)) (first_branch a))))
    (second_process a) (Executing (process_body (processes P (second_process a)) (second_branch a))))
  (Some (m.[x <- eval e m])%M) (rho : 'End(Hq)).
have Hready : ready pc := idle_ready (processes P).
have Hinv : serial_invariant P src := @idle_serial_invariant P m rho (is_den1lf rho).
have Hi : pc (first_process a) = Waiting :=
  @idle_control_waiting (processes P (first_process a)) (first_branch a).
have Hk : pc (second_process a) = Waiting :=
  @idle_control_waiting (processes P (second_process a)) (second_branch a).
have Hstep : global_step (processes P) src (certain dst).
  exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
have Hdst : serial_invariant P dst := serial_global_step Hinv Hstep tt.
have Esrc := @residual_value P rho (is_den1lf rho) src Hinv.
have Edst := @residual_value P rho (is_den1lf rho) dst Hdst.
have EV := @deterministic_step_value P rho src dst (proj1 Hinv) Hstep.
have Eres := eq_trans Esrc (eq_trans EV (esym Edst)).
have Eout := congr1 (fun d : @CQState.state cmem Hq => d out) Eres.
have Hr : (rho : 'End(Hq)) \is denlf := den1lf_den (is_den1lf rho).
rewrite /src /dst !(@residual_stateE _ _ _ _ _ _ Hr) in Eout.
rewrite (residual_idle (processes P) Hready)
  (@residual_active_pair _ (processes P) pc (first_process a) (second_process a)
    (process_body (processes P (first_process a)) (first_branch a))
    (process_body (processes P (second_process a)) (second_branch a)) Hready Hik) in Eout.
rewrite HE.
change (ClassicalSemantics.denote (network_tail (processes P)) m out rho =
  slet (slet (ClassicalSemantics.denote (CL.Assign x e))
    (slet (ClassicalSemantics.denote (translate_statement (process_body (processes P (first_process a)) (first_branch a))))
      (ClassicalSemantics.denote (translate_statement (process_body (processes P (second_process a)) (second_branch a))))))
    (ClassicalSemantics.denote (network_tail (processes P))) m out rho).
rewrite !sletA assignment_sequence.
exact: Eout.
Qed.

Theorem enabled_tail_kernel (P : program) m (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) -> eval g m ->
  ClassicalSemantics.denote (network_tail (processes P)) m =
    slet (ClassicalSemantics.denote c) (ClassicalSemantics.denote (network_tail (processes P))) m.
Proof.
move=>Ha Hg; apply/vdistrP=>out; apply: superop_normalized_ext=>rho.
exact: (@enabled_tail_normalized P m rho a g c Ha Hg out).
Qed.

Lemma pre_row_equal total (c d : CL.command) Q m :
  ClassicalSemantics.denote c m = ClassicalSemantics.denote d m ->
  CQHoare.pre total c Q m = CQHoare.pre total d Q m.
Proof.
move=>E; case: total; apply/val_inj.
- change ((wp (ClassicalSemantics.denote c) Q m : 'End(Hq)) = (wp (ClassicalSemantics.denote d) Q m : 'End(Hq))).
  by rewrite !wpE E.
- change ((\1 - (wp (ClassicalSemantics.denote c) (complement Q) m : 'End(Hq))) =
    (\1 - (wp (ClassicalSemantics.denote d) (complement Q) m : 'End(Hq)))).
  by rewrite !wpE E.
Qed.

Theorem enabled_tail_pre (P : program) total Q m
    (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) -> eval g m ->
  CQHoare.pre total (network_tail (processes P)) Q m =
    CQHoare.pre total c (CQHoare.pre total (network_tail (processes P)) Q) m.
Proof.
move=>Ha Hg; rewrite -CQHoare.pre_sequence.
apply: pre_row_equal; exact: (@enabled_tail_kernel P m a g c Ha Hg).
Qed.

Theorem enabled_tail_invariant (P : program) total Q
    (a : rendezvous_index (processes P)) g c :
  index_command a = Some (g,c) ->
  CQHoare.valid total
    (mask (eval g) (CQHoare.pre total (network_tail (processes P)) Q))
    c (CQHoare.pre total (network_tail (processes P)) Q).
Proof.
move=>Ha; apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>m.
rewrite /mask; case Hg: (eval g m).
- by rewrite (@enabled_tail_pre P total Q m a g c Ha Hg).
- exact: obsf_ge0.
Qed.

Theorem all_tail_invariants (P : program) total Q :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total
      (mask (eval bc.1) (CQHoare.pre total (network_tail (processes P)) Q))
      bc.2 (CQHoare.pre total (network_tail (processes P)) Q))
    (rendezvous_commands (processes P)).
Proof.
rewrite -rendezvous_indicesE.
elim: (rendezvous_indices (processes P))=>[|a rest IH] /=; first exact: List.Forall_nil.
case Ha: (index_command a)=>[[g c]|] /=; last exact: IH.
apply: List.Forall_cons; last exact: IH.
exact: (@enabled_tail_invariant P total Q a g c Ha).
Qed.
End DistributedAllRendezvous.


Module DistributedExecutionCorrespondence.
(* Operational linearity for distributed programs. See ../classical/PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedCQInput DistributedCorrespondence.
Theorem run_translate (S : program) rho :
  run S rho = CQHoare.run (successful_sequentialize (processes S)) rho.
Proof.
apply: DistributedCQInput.run_kernel=>m r out.
exact: denote_program_point.
Qed.

End DistributedExecutionCorrespondence.


Module DistributedLinearity.
(* Operational linearity for distributed programs. See ../classical/PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedCQInput DistributedExecutionCorrespondence.
Local Notation Hq := 'H[msys]_finset.setT.
Section Programs.
Context {A : choiceType}.
Variable S : program.

Definition weighted_run (w : A -> C) (d : A -> @CQState.state cmem Hq) a :
  {summable cmem -> 'End(Hq)} :=
  w a *: (run S (d a) : {summable cmem -> 'End(Hq)}).

Lemma weighted_runE w d : weighted_run w d =
  CQKernelLinearity.weighted_output
    (ClassicalSemantics.denote (successful_sequentialize (processes S))) w d.
Proof. by apply/funext=>a; rewrite /weighted_run run_translate. Qed.

Theorem run_weighted_summable w d :
  summable (CQKernelLinearity.weighted_input w d) ->
  summable (weighted_run w d).
Proof.
rewrite weighted_runE; exact: CQKernelLinearity.weighted_output_summable.
Qed.

Theorem run_weighted_sum w d (d0 : @CQState.state cmem Hq) :
  summable (CQKernelLinearity.weighted_input w d) ->
  (d0 : {summable cmem -> 'End(Hq)}) =
    sum (CQKernelLinearity.weighted_input w d) ->
  (run S d0 : {summable cmem -> 'End(Hq)}) = sum (weighted_run w d).
Proof.
rewrite run_translate weighted_runE /CQHoare.run.
exact: CQKernelLinearity.apply_weighted_sum.
Qed.

Theorem run_mix (w : Distr A) (d : A -> @CQState.state cmem Hq) :
  run S (CQStateMixture.mix w d) = CQStateMixture.mix w (fun a => run S (d a)).
Proof.
rewrite run_translate /CQHoare.run CQKernelLinearity.apply_mix.
congr (CQStateMixture.mix w _); apply/funext=>a.
by rewrite run_translate.
Qed.
End Programs.
End DistributedLinearity.
