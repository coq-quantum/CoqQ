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

Module DistributedGlobalActions.
Import DistributedLanguage DistributedOperational DistributedScheduler
  DistributedLocalActions DistributedResults DistributedResidual DistributedSequentialization
  DistributedWeighted.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Inductive action (n : nat) := Local of 'I_n | Rendezvous of 'I_n & 'I_n.
Arguments Local {n} i.
Arguments Rendezvous {n} i k.

Definition participants n (a : action n) : {set 'I_n} :=
  match a with Local i => [set i] | Rendezvous i k => [set i; k] end.
Definition ordered n (a : action n) :=
  match a with Local _ => True | Rendezvous i k => (i < k)%N end.

Inductive labeled_step n (p : 'I_n -> process) :
    action n -> global_configuration n -> family (global_configuration n) -> Prop :=
| LParallel pc m rho i s mu :
    pc i = Executing s ->
    local_step (local_config s (Some m) rho) mu ->
    labeled_step p (Local i) (global_config pc (Some m) rho) (fmap (lift_local p pc i) mu)
| LProcessDone pc m rho i :
    pc i = Waiting ->
    [forall j, ~~ eval (process_guard (p i) j) m] ->
    labeled_step p (Local i) (global_config pc (Some m) rho)
      (certain (global_config (replace pc i Stopped) (Some m) rho))
| LCommunication pc m rho (i k : 'I_n) j l t (x : CL.variable t) e :
    (i < k)%N -> pc i = Waiting -> pc k = Waiting ->
    eval (process_guard (p i) j) m -> eval (process_guard (p k) l) m ->
    matches (process_io (p i) j) (process_io (p k) l) (AAssign x e) ->
    labeled_step p (Rendezvous i k) (global_config pc (Some m) rho)
      (certain (global_config
        (replace (replace pc i (Executing (process_body (p i) j)))
          k (Executing (process_body (p k) l)))
        (Some (m.[x <- eval e m])%M) rho)).

Lemma labeled_step_erasure n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> global_step p c mu.
Proof. by case; [apply: StepParallel | apply: StepProcessDone | apply: StepCommunication]. Qed.

Lemma labeled_step_complete n (p : 'I_n -> process) c mu :
  global_step p c mu -> exists a, labeled_step p a c mu.
Proof.
case=>[pc m rho i s nu Hi Hloc|pc m rho i Hi Hnone|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch].
- exists (Local i); exact: LParallel Hi Hloc.
- exists (Local i); exact: LProcessDone Hi Hnone.
- exists (Rendezvous i k); exact: LCommunication Hik Hi Hk Hj Hl Hmatch.
Qed.

Lemma labeled_step_ordered n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> ordered a.
Proof. by case. Qed.

Lemma labeled_step_enabled n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> exists m, c.1.2 = Some m /\
    enabled_label p c.1.1 m c.2 (participants a).
Proof.
case=>[pc m rho i s nu Hi Hloc|pc m rho i Hi Hnone|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch]; exists m; split=>//.
- apply: EnabledLocal; left; by exists s, nu.
- apply: EnabledLocal; by right.
- apply: EnabledPair; split=>//; split=>//; split.
    by apply/negP=>/eqP E; move: Hik; rewrite E ltnn.
  by exists j, l, (AAssign x e); repeat split.
Qed.

Lemma labeled_step_controls n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> forall outcome,
    controls_outside (participants a) c.1.1 (branch_value mu outcome).1.1.
Proof.
case=>[pc m rho i s nu Hi Hloc|pc m rho i Hi Hnone|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] outcome z.
- rewrite inE=>Hz; exact: replace_other Hz.
- rewrite inE=>Hz; exact: replace_other Hz.
- rewrite !inE negb_or=>/andP[Hzi Hzk].
  by rewrite /= !replace_other.
Qed.

Definition assignment_store (a : atom) m :=
  match a with AAssign _ x e => (m.[x <- eval e m])%M | _ => m end.

Lemma matches_store_unique a b e f m : matches a b e -> matches a b f ->
  assignment_store e m = assignment_store f m.
Proof.
move=>He Hf; have E : e = f.
  by move: (matching_effect He); rewrite (matching_effect Hf)=>[=].
by rewrite E.
Qed.

Lemma labeled_step_deterministic n (p : 'I_n -> process) a c mu nu :
  (forall i, process_wf (p i)) -> configuration_owned p c ->
  labeled_step p a c mu -> labeled_step p a c nu -> mu = nu.
Proof.
move=>Hwf Hown d1 d2; inversion d1; subst; inversion d2; subst.
all: try congruence.
- have Es : s0 = s by congruence.
  subst s0; have Hs : statement_wf s.
    have Ho := Hown i; rewrite /= H in Ho; exact: (proj1 Ho).
  by rewrite (local_step_deterministic Hs H0 H7).
- have Ej : j0 = j := (proj1 (proj2 (Hwf i))) m j0 j H14 H2.
  have El : l0 = l := (proj1 (proj2 (Hwf k))) m l0 l H15 H3.
  subst j0; subst l0.
  have Em := @matches_store_unique _ _ _ _ m H4 H16.
  change ((m.[x <- eval e m])%M = (m.[x0 <- eval e0 m])%M) in Em.
  by rewrite Em.
Qed.


Lemma ordered_participants_injective n (a b : action n) :
  ordered a -> ordered b -> participants a = participants b -> a = b.
Proof.
case: a=>[i|i k]; case: b=>[j|j l] /= Ha Hb E.
- have Hi : i \in [set j] by rewrite -E inE eqxx.
  by move: Hi; rewrite inE=>/eqP->.
- have Hj : j \in [set i] by rewrite E !inE eqxx.
  have Hl : l \in [set i] by rewrite E !inE eqxx orbT.
  move: Hj Hl; rewrite !inE=>/eqP Hj /eqP Hl.
  by move: Hb; rewrite Hj Hl ltnn.
- have Hi : i \in [set j] by rewrite -E !inE eqxx.
  have Hk : k \in [set j] by rewrite -E !inE eqxx orbT.
  move: Hi Hk; rewrite !inE=>/eqP Hi /eqP Hk.
  by move: Ha; rewrite Hi Hk ltnn.
- have Hi : i \in [set j; l] by rewrite -E !inE eqxx.
  have Hk : k \in [set j; l] by rewrite -E !inE eqxx orbT.
  move: Hi Hk; rewrite !inE=>/orP[/eqP Eij|/eqP Eil] /orP[/eqP Ekj|/eqP Ekl].
  + by move: Ha; rewrite Eij Ekj ltnn.
  + by rewrite Eij Ekl.
  + move: Ha; rewrite Eil Ekj=>Ha'.
    by move: (ltn_trans Hb Ha'); rewrite ltnn.
  + by move: Ha; rewrite Eil Ekl ltnn.
Qed.

Lemma labeled_steps_disjoint_or_equal (P : program) a b c mu nu :
  labeled_step (processes P) a c mu -> labeled_step (processes P) b c nu ->
  a = b \/ [disjoint participants a & participants b]%SET.
Proof.
move=>Ha Hb; have [m [Hm HEa]] := labeled_step_enabled Ha.
have [m' [Hm' HEb]] := labeled_step_enabled Hb.
have Em : m' = m by congruence.
subst m'; case: (enabled_labels_disjoint_or_equal HEa HEb)=>[E|Hd]; last by right.
left; exact: ordered_participants_injective (labeled_step_ordered Ha) (labeled_step_ordered Hb) E.
Qed.

Lemma distinct_labeled_step_zero (P : program) a b c mu nu :
  labeled_step (processes P) a c mu -> labeled_step (processes P) b c nu -> a <> b ->
  forall outcome, successful_component (branch_value mu outcome) = CQState.bottom.
Proof.
move=>Ha Hb Hab outcome.
have Hd : [disjoint participants a & participants b]%SET.
  by case: (labeled_steps_disjoint_or_equal Ha Hb)=>[E|//]; exfalso; apply: Hab.
have [m [Hm HEb]] := labeled_step_enabled Hb.
apply: (disjoint_enabled_successful_component HEb Hd).
exact: (@labeled_step_controls _ _ _ _ _ Ha outcome).
Qed.

Lemma weighted_successful_zero n (mu : family (global_configuration n)) m :
  (forall i, successful_component (branch_value mu i) = CQState.bottom) ->
  weighted_sum mu (fun c => successful_component c m) = 0.
Proof.
move=>H; rewrite /weighted_sum (eq_sum (g := fun _ => 0)).
  by move=>i; rewrite H CQState.bottomE scaler0.
exact: summable_sum_cst0.
Qed.

Theorem global_steps_successful_equal (P : program) c mu nu m :
  configuration_owned (processes P) c ->
  global_step (processes P) c mu -> global_step (processes P) c nu ->
  weighted_sum mu (fun d => successful_component d m) =
  weighted_sum nu (fun d => successful_component d m).
Proof.
move=>Hown Hmu Hnu; have [a Ha] := labeled_step_complete Hmu.
have [b Hb] := labeled_step_complete Hnu.
case: (pselect (a = b))=>[E|E].
- subst b; have Emu : mu = nu.
    exact: (@labeled_step_deterministic _ _ _ _ _ _ (@processes_wf P) Hown Ha Hb).
  by rewrite Emu.
- rewrite !weighted_successful_zero //.
  + exact: distinct_labeled_step_zero Ha Hb E.
  + apply: distinct_labeled_step_zero Hb Ha _.
    by move=>F; apply: E; symmetry.
Qed.

End DistributedGlobalActions.
