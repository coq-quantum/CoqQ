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

From quantum.example.distributive Require Import global_instruments.

Module DistributedStoppedInvariant.
Import DistributedLanguage DistributedOperational DistributedGlobalActions
  DistributedGlobalInstruments DistributedResidual.

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
