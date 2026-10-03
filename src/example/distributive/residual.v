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
From quantum.example.distributive Require Import language operational distribution scheduler local_actions results.
From quantum.example.classical Require Import state.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedResidual.
Import DistributedLanguage DistributedOperational DistributedDistribution
  DistributedScheduler DistributedLocalActions DistributedResults.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Definition statement_owned (p : process) (s : statement) :=
  statement_wf s /\
  statement_changes s `<=` process_changes p /\
  (statement_reads s `<=` process_reads p)%classic /\
  (statement_quantum s :<=: process_quantum p)%SET.

Definition control_owned (p : process) (pc : control) :=
  match pc with Executing s => statement_owned p s | _ => True end.
Definition configuration_owned n (p : 'I_n -> process) (c : global_configuration n) :=
  forall i, control_owned (p i) (c.1.1 i).

Lemma initialization_owned p : process_wf p -> statement_owned p (initialization p).
Proof.
move=>[Hinit Hbody]; split=>//; split.
- exact: fsubsetUl.
split.
- by move=>x Hx; left.
- exact: finset.subsetUl.
Qed.

Lemma body_owned p j : process_wf p -> statement_owned p (process_body p j).
Proof.
move=>[Hinit [Hex Hbody]]; split; first exact: Hbody.
split.
- apply: fsubset_trans (fsubsetUr _ _) _.
  rewrite /process_changes (bigD1 j) //=.
  apply: fsubset_trans (fsubsetUl _ _) _; exact: fsubsetUr.
split.
- move=>x Hx; right; exists j=>//; by right.
- rewrite /process_quantum; apply: fintype.subset_trans _ (finset.subsetUr _ _).
  exact: branch_quantum_subset.
Qed.

Lemma initial_configuration_owned n (p : 'I_n -> process) m rho :
  (forall i, process_wf (p i)) -> configuration_owned p (initial_configuration p m rho).
Proof. by move=>H i; apply: initialization_owned. Qed.

Lemma after_local_owned p s t :
  statement_owned p s -> residual_wf t ->
  statement_changes t `<=` statement_changes s ->
  (statement_reads t `<=` statement_reads s)%classic ->
  (statement_quantum t :<=: statement_quantum s)%SET ->
  control_owned p (after_local p t).
Proof.
move=>[Hs [Hc [Hr Hq]]] Ht Htc Htr Htq.
case: t Ht Htc Htr Htq=>[|a|a b|n g b|n g b] /= Ht Htc Htr Htq.
- by case: branch_count.
all: split; first by case: Ht=>[//|].
all: split; first exact: fsubset_trans Htc Hc.
all: split; first by move=>x Hx; apply: Hr; apply: Htr.
all: exact: fintype.subset_trans Htq Hq.
Qed.

Lemma local_successor_owned p s m rho mu :
  statement_owned p s -> local_step (local_config s (Some m) rho) mu ->
  forall outcome, control_owned p (after_local p (branch_value mu outcome).1.1).
Proof.
move=>Hs Hstep outcome; apply: (after_local_owned Hs).
- exact: (@local_step_wf _ _ Hstep (proj1 Hs) outcome).
- exact: (@local_step_changes _ _ Hstep outcome).
- exact: (@local_step_reads _ _ Hstep outcome).
- exact: (@local_step_quantum _ _ Hstep outcome).
Qed.

Lemma global_step_owned n (p : 'I_n -> process) c mu :
  (forall i, process_wf (p i)) -> configuration_owned p c ->
  global_step p c mu -> forall outcome, configuration_owned p (branch_value mu outcome).
Proof.
move=>Hwf Hown Hstep; case: Hstep Hown=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hown outcome z /=.
- rewrite /replace; case E: (z == i).
  + move/eqP: E=>->; apply: (@local_successor_owned (p i) s m rho nu _ Hloc outcome).
    by move: (Hown i); rewrite /= Hpc.
  + exact: Hown.
- rewrite /replace; case E: (z == i)=>//; exact: Hown.
- rewrite /replace; case Ezk: (z == k).
  + move/eqP: Ezk=>->; exact: (@body_owned (p k) l (Hwf k)).
  + case Ezi: (z == i); last exact: Hown.
    move/eqP: Ezi=>->; exact: (@body_owned (p i) j (Hwf i)).
Qed.

Lemma distribution_step_owned n (p : 'I_n -> process) mu nu :
  (forall i, process_wf (p i)) -> distribution_step p mu nu ->
  probability_family mu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  (forall i, 0 < branch_weight mu i -> configuration_owned p (branch_value mu i)) ->
  forall j, 0 < branch_weight nu j -> configuration_owned p (branch_value nu j).
Proof.
move=>Hwf Hstep Hm Hr Hown.
have Hn := distribution_step_probability Hstep Hm Hr.
case: Hstep=>Ha [next [Hnext E]].
have Hbind : probability_family (bind_family mu next).
  apply: bind_family_probability Hm _=>i Hi.
  case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: (global_step_probability Hs (Hr i Hi)).
apply: (same_distribution_support (P := configuration_owned p) Hbind Hn E).
move=>[i j] /= Hij.
case P: (0 < branch_weight mu i).
- have Hchild : forall k, configuration_owned p (branch_value (next i) k).
    case: (Hnext i P)=>[[Ht ->]|Hs].
    + by move=>k; exact: Hown.
    + exact: (@global_step_owned _ p _ _ Hwf (Hown i P) Hs).
  exact: Hchild.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hm) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by move: Hij; rewrite Z mul0r ltxx.
Qed.

Lemma computation_owned n (p : 'I_n -> process) c (pi : computation p c) :
  (forall i, process_wf (p i)) -> configuration_owned p c ->
  forall k i, 0 < branch_weight (computation_stage pi k) i ->
    configuration_owned p (branch_value (computation_stage pi k) i).
Proof.
move=>Hwf Hc; elim=>[|k IH].
- apply: (same_distribution_support (P := configuration_owned p)
    (certain_probability c) (computation_probability pi 0%N) (computation_initial pi)).
  by move=>i Hi.
- exact (@distribution_step_owned n p (computation_stage pi k) (computation_stage pi k.+1)
    Hwf (@computation_advances n p c pi k) (@computation_probability n p c pi k)
    (@computation_normalized n p c pi k) IH).
Qed.

Lemma program_computation_owned (P : program) m rho
    (pi : computation (processes P) (initial_configuration (processes P) m rho)) :
  forall k i, 0 < branch_weight (computation_stage pi k) i ->
    configuration_owned (processes P) (branch_value (computation_stage pi k) i).
Proof.
apply: computation_owned; first exact: processes_wf.
apply: initial_configuration_owned; exact: processes_wf.
Qed.

Local Close Scope fset_scope.

Definition controls_outside n (A : {set 'I_n}) (pc pc' : 'I_n -> control) :=
  forall i, i \notin A -> pc' i = pc i.

Lemma global_step_label_control n (p : 'I_n -> process) c mu : global_step p c mu ->
  exists m A, c.1.2 = Some m /\ enabled_label p c.1.1 m c.2 A /\
    forall outcome, controls_outside A c.1.1 (branch_value mu outcome).1.1.
Proof.
move=>d; case: d=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch].
- exists m, [set i]; split=>//; split.
  + apply: EnabledLocal; left; by exists s, nu.
  + move=>outcome z; rewrite inE=>Hz; exact: replace_other Hz.
- exists m, [set i]; split=>//; split.
  + apply: EnabledLocal; by right.
  + move=>outcome z; rewrite inE=>Hz; exact: replace_other Hz.
- exists m, [set i; k]; split=>//; split.
  + apply: EnabledPair; split=>//; split=>//; split.
      by apply/negP=>/eqP E; move: Hik; rewrite E ltnn.
    by exists j, l, (AAssign x e); repeat split.
  + move=>outcome z; rewrite !inE negb_or=>/andP[Hzi Hzk].
    by rewrite /= !replace_other.
Qed.

Lemma enabled_label_active n (p : 'I_n -> process) pc m rho A :
  enabled_label p pc m rho A -> forall i, i \in A -> pc i <> Stopped.
Proof.
case=>[j Hlocal|j k Hpair] i.
- rewrite inE=>/eqP->.
  case: Hlocal=>[[s [mu [E Hstep]]]|[E Hnone]]; by rewrite E.
- rewrite !inE=>/orP[/eqP->|/eqP->];
    move: Hpair=>[Ej [Ek Hpair]]; by rewrite ?Ej ?Ek.
Qed.

Lemma enabled_label_nonempty n (p : 'I_n -> process) pc m rho A :
  enabled_label p pc m rho A -> exists i, i \in A.
Proof. case=>[i Hi|i k Hik]; exists i; by rewrite !inE eqxx. Qed.

Lemma disjoint_enabled_not_stopped n (p : 'I_n -> process) pc m rho
    (A B : {set 'I_n}) (pc' : 'I_n -> control) :
  enabled_label p pc m rho B -> [disjoint A & B]%SET ->
  controls_outside A pc pc' -> exists i, pc' i <> Stopped.
Proof.
move=>HB HAB Hctrl; have [i Hi] := enabled_label_nonempty HB.
have Hnot : i \notin A.
  by move: HAB; rewrite disjoint_sym=>/disjointP/(_ i Hi).
exists i; rewrite (Hctrl i Hnot); exact: (@enabled_label_active n p pc m rho B HB i Hi).
Qed.

Lemma successful_at_not_stopped n (c : global_configuration n) i m :
  c.1.1 i <> Stopped -> successful_at c m = false.
Proof.
move=>H; rewrite /successful_at; case: c.1.2=>// s.
suff -> : [forall j, asbool (c.1.1 j = Stopped)] = false by rewrite andbF.
apply/negP=>/forallP/(_ i)/asboolP; exact: H.
Qed.

Lemma successful_component_not_stopped n (c : global_configuration n) i :
  c.1.1 i <> Stopped -> successful_component c = CQState.bottom.
Proof.
case: c=>[[pc [m|]] rho] H //=; rewrite /successful_component /=.
suff -> : [forall j, asbool (pc j = Stopped)] = false by [].
apply/negP=>/forallP/(_ i)/asboolP; exact: H.
Qed.

Lemma disjoint_enabled_successful_component n (p : 'I_n -> process)
    (c : global_configuration n) m (A B : {set 'I_n}) (d : global_configuration n) :
  enabled_label p c.1.1 m c.2 B -> [disjoint A & B]%SET ->
  controls_outside A c.1.1 d.1.1 -> successful_component d = CQState.bottom.
Proof.
move=>HB HAB Hctrl; have [i Hi] := disjoint_enabled_not_stopped HB HAB Hctrl.
exact: successful_component_not_stopped Hi.
Qed.

End DistributedResidual.
