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
From quantum.example.distributive Require Import language operational distribution weighted scheduler local_actions results residual sequentialization observables diamond global_actions.
From quantum.example.classical Require Import state.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedSchedulerSemantics.
Import DistributedLanguage DistributedOperational DistributedDistribution
  DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions
  DistributedObservables.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma same_distribution_fmap X Y (f : X -> Y) (mu nu : family X) :
  same_distribution mu nu -> same_distribution (fmap f mu) (fmap f nu).
Proof.
move=>E g [M HM]; apply: (E (fun x => g (f x))); exists M=>x; exact: HM.
Qed.

Section Projected.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Hypothesis Hrho0 : rho0 \is den1lf.

Definition failure : global_configuration n := global_config (fun _ => Stopped) None rho0.
Definition collapse (c : global_configuration n) : global_configuration n :=
  if c.1.2 is None then failure else c.
Definition good (c : global_configuration n) :=
  c.2 \is den1lf /\ configuration_owned p c.

Lemma collapse_idempotent c : collapse (collapse c) = collapse c.
Proof. by case: c=>[[pc [m|]] rho]. Qed.

Lemma collapse_successful_component c : successful_component (collapse c) = successful_component c.
Proof. by case: c=>[[pc [m|]] rho]. Qed.

Lemma collapse_good c : good c -> good (collapse c).
Proof.
by case: c=>[[pc [m|]] rho] [Hr Ho] //=.
Qed.

Lemma collapse_terminal c : terminal p c -> terminal p (collapse c).
Proof.
case: c=>[[pc [m|]] rho] Ht //=; exact: failure_terminal.
Qed.

Lemma step_proper c mu : global_step p c mu -> collapse c = c.
Proof. by case. Qed.

Inductive projected_step : global_configuration n -> family (global_configuration n) -> Prop :=
| ProjectedGlobal c mu : good c -> global_step p c mu ->
    projected_step c (fmap collapse mu)
| ProjectedTerminal c : terminal p c -> projected_step c (certain c)
| ProjectedInvalid c : ~ good c -> projected_step c (certain c).

Lemma projected_probability c mu : projected_step c mu -> probability_family mu.
Proof.
case=>[c' nu [Hr Ho] Hs|c' Ht|c' Hbad]; try exact: certain_probability.
apply: fmap_probability; exact: global_step_probability Hs Hr.
Qed.

Lemma projected_has_step c : exists mu, projected_step c mu.
Proof.
case: (pselect (good c))=>[Hg|Hg].
- case: (pselect (exists mu, global_step p c mu))=>[[mu Hmu]|Hnone].
  + exists (fmap collapse mu); exact: ProjectedGlobal Hg Hmu.
  + exists (certain c); apply: ProjectedTerminal=>mu Hmu; apply: Hnone; by exists mu.
- exists (certain c); exact: ProjectedInvalid Hg.
Qed.

Definition policy c := projT1 (cid (projected_has_step c)).
Lemma policy_step c : projected_step c (policy c).
Proof. exact: projT2 (cid (projected_has_step c)). Qed.

Lemma project_global_step c mu : good c -> global_step p c mu ->
  projected_step (collapse c) (fmap collapse mu).
Proof. move=>Hg Hs; rewrite (step_proper Hs); exact: ProjectedGlobal Hg Hs. Qed.

Lemma project_terminal_step c : terminal p c ->
  projected_step (collapse c) (fmap collapse (certain c)).
Proof. move=>Ht; apply: ProjectedTerminal; exact: collapse_terminal Ht. Qed.

Lemma weighted_collapse mu m :
  weighted_sum (fmap collapse mu) (fun d => successful_component d m) =
  weighted_sum mu (fun d => successful_component d m).
Proof. by apply: eq_sum=>i; rewrite /= collapse_successful_component. Qed.

Lemma projected_evolution mu nu : probability_family mu ->
  (forall i, 0 < branch_weight mu i -> good (branch_value mu i)) ->
  distribution_step p mu nu ->
  ProbabilisticDiamond.evolution projected_step (fmap collapse mu) (fmap collapse nu).
Proof.
move=>Hm Hg Hstep.
have Hr : forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf.
  by move=>i Hi; exact: (proj1 (Hg i Hi)).
have Hn := distribution_step_probability Hstep Hm Hr.
split; first exact: fmap_probability Hn.
case: Hstep=>Ha [next [Hnext E]].
exists (fun i => fmap collapse (next i)); split.
- move=>i Hi; case: (Hnext i Hi)=>[[Ht ->]|Hs].
  + exact: project_terminal_step Ht.
  + exact: project_global_step (Hg i Hi) Hs.
- exact (@same_distribution_fmap _ _ collapse _ _ E).
Qed.

Lemma projected_one_step c mu nu m : projected_step c mu -> projected_step c nu ->
  weighted_sum mu (fun d => successful_component d m) =
  weighted_sum nu (fun d => successful_component d m).
Proof.
move=>Hmu Hnu; inversion Hmu; subst; inversion Hnu; subst; try congruence.
all: try solve [exfalso; match goal with
  | Ht : terminal p ?c, Hs : global_step p ?c ?mu |- _ => exact (Ht _ Hs)
  end].
rewrite !weighted_collapse.
exact: (@global_steps_successful_equal P c mu0 mu m (proj2 H) H0 H2).
Qed.

End Projected.
End DistributedSchedulerSemantics.
