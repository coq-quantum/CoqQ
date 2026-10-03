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
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import footprint.
From quantum.example.distributive Require Import language operational scheduler local_actions instruments interchange progress observables distribution global_instruments global_actions residual scheduler_semantics local_diamond footprint.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedConfluence.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions
  DistributedInstruments DistributedInterchange DistributedProgress DistributedObservables
  DistributedDistribution DistributedGlobalInstruments DistributedGlobalActions
  DistributedResidual DistributedSchedulerSemantics DistributedLocalDiamond DistributedFootprint.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Section Program.
Variable P : program.
Local Notation n := (process_count P).
Local Notation p := (processes P).
Variable rho0 : 'End(Hq).
Hypothesis Hrho0 : rho0 \is den1lf.
Local Notation fail := (@failure P rho0).
Local Notation project := (@collapse P rho0).
Local Notation step := (@projected_step P rho0).

Definition instrument_run (d : descriptor n) pc m rho :=
  fmap (descriptor_lift d pc) (local_family (instruction d) m rho).

Lemma instrument_runE d pc m rho : rho \is den1lf ->
  instrument_run d pc m rho = descriptor_run d pc m rho.
Proof. by move=>Hr; rewrite /instrument_run /descriptor_run local_realization. Qed.

Lemma instrument_step pc m rho a d :
  enabled_descriptor p pc m a d -> statement_wf (instruction d) -> rho \is den1lf ->
  global_step p (global_config pc (Some m) rho) (instrument_run d pc m rho).
Proof.
move=>Hd Hw Hr; rewrite instrument_runE //.
exact: (@labeled_step_erasure n p a _ _ (@descriptor_step n p pc m rho a d Hd Hw)).
Qed.

Lemma instrument_replay pc m rho a b d e :
  configuration_owned p (global_config pc (Some m) rho) -> rho \is den1lf ->
  enabled_descriptor p pc m a d -> enabled_descriptor p pc m b e ->
  [disjoint participants a & participants b]%SET -> forall i m',
  (branch_value (instrument_run d pc m rho) i).1.2 = Some m' ->
  global_step p (branch_value (instrument_run d pc m rho) i)
    (instrument_run e (branch_value (instrument_run d pc m rho) i).1.1 m'
      (branch_value (instrument_run d pc m rho) i).2).
Proof.
move=>Ho Hr Hd He Hdis.
have Hreplay := @descriptor_replay_after P pc m rho a b d e Ho Hd He Hdis.
rewrite -(instrument_runE d pc m Hr) in Hreplay.
move=>i m' Hout; rewrite [instrument_run e _ _ _]instrument_runE.
- exact: (@normalized_output_den1 (@local_cp (instruction d) m i) rho Hr).
- exact: (@labeled_step_erasure n p b _ _ (Hreplay i m' Hout)).
Qed.

Definition pair_finish (d e : descriptor n) pc s t st r :=
  project (global_config (update_control e t (update_control d s pc)) st r).

Lemma pair_finish_failure d e pc s t r : pair_finish d e pc s t None r = fail.
Proof. by []. Qed.

Definition continuation (d e : descriptor n) pc m rho :=
  @second_family _ fail (pair_finish d e pc) (instruction d) (instruction e) m rho.

Lemma continuation_step pc m rho a b d e :
  configuration_owned p (global_config pc (Some m) rho) -> rho \is den1lf ->
  enabled_descriptor p pc m a d -> enabled_descriptor p pc m b e ->
  [disjoint participants a & participants b]%SET -> forall i,
  step (project (branch_value (instrument_run d pc m rho) i))
    (@continuation d e pc m rho i).
Proof.
move=>Ho Hr Hd He Hdis i.
have Hwf := enabled_instruction_wf Ho Hd.
have Hfirst := instrument_step Hd Hwf Hr.
have Hown := @global_step_owned _ p _ _ (@processes_wf P) Ho Hfirst i.
have Hnorm := @global_step_normalized _ p _ _ Hfirst Hr i.
have Hgood : @good P (branch_value (instrument_run d pc m rho) i) by split.
have Hnext := @instrument_replay pc m rho a b d e Ho Hr Hd He Hdis i.
rewrite /continuation /second_family.
case E: ((@local_control (instruction d) m i).2)=>[m'|].
- have Hout : (branch_value (instrument_run d pc m rho) i).1.2 = Some m' := E.
  have Hstep := Hnext m' Hout.
  have Hproj := @project_global_step P rho0 _ _ Hgood Hstep.
  exact Hproj.
- rewrite /instrument_run /local_family /descriptor_lift /fmap /= /collapse E.
  apply: ProjectedTerminal; exact: failure_terminal.
Qed.

Definition projected_join (mu nu : family (global_configuration n)) :=
  exists (left : branch_index mu -> family (global_configuration n))
    (right : branch_index nu -> family (global_configuration n)),
    (forall i, 0 < branch_weight mu i -> step (branch_value mu i) (left i)) /\
    (forall i, 0 < branch_weight nu i -> step (branch_value nu i) (right i)) /\
    same_distribution (bind_family mu left) (bind_family nu right).

Lemma projected_join_refl mu : projected_join mu mu.
Proof.
exists (fun i => @policy P rho0 (branch_value mu i)),
  (fun i => @policy P rho0 (branch_value mu i)); split.
- by move=>i Hi; exact: policy_step.
- split; first by move=>i Hi; exact: policy_step.
  by move=>f Hf.
Qed.

Lemma descriptor_join pc m rho a b d e :
  configuration_owned p (global_config pc (Some m) rho) -> rho \is den1lf ->
  enabled_descriptor p pc m a d -> enabled_descriptor p pc m b e ->
  [disjoint participants a & participants b]%SET ->
  projected_join (fmap project (instrument_run d pc m rho))
    (fmap project (instrument_run e pc m rho)).
Proof.
move=>Ho Hr Hd He Hdis.
have Hrev : [disjoint participants b & participants a]%SET by rewrite disjoint_sym.
have Hst : forall x, x \in statement_changes (instruction d) ->
    ~ statement_reads (instruction e) x.
  move=>x Hx Hread.
  have Hfresh := @descriptor_private_reads P pc m rho b a e d Ho He Hd Hrev x Hread.
  by move: Hfresh; rewrite Hx.
have Hts : forall x, x \in statement_changes (instruction e) ->
    ~ statement_reads (instruction d) x.
  move=>x Hx Hread.
  have Hfresh := @descriptor_private_reads P pc m rho a b d e Ho Hd He Hdis x Hread.
  by move: Hfresh; rewrite Hx.
have Hwrite : [disjoint statement_changes (instruction d) & statement_changes (instruction e)]%fset.
  apply/fdisjointP=>x Hx; apply/negP=>Hy.
  exact: (Hst x Hx (statement_changes_reads Hy)).
have Hquant : [disjoint statement_quantum (instruction d) & statement_quantum (instruction e)].
  apply/disjointP=>x Hx; apply/negP=>Hy.
  have Hempty := eqP (@descriptor_private_quantum P pc m rho a b d e Ho Hd He Hdis).
  have Hboth : x \in (statement_quantum (instruction d) :&: statement_quantum (instruction e)).
    by rewrite inE Hx Hy.
  by move: Hboth; rewrite Hempty inE.
exists (@continuation d e pc m rho), (@continuation e d pc m rho); split.
- move=>i Hi; exact: (@continuation_step pc m rho a b d e Ho Hr Hd He Hdis i).
- split.
  + move=>i Hi; exact: (@continuation_step pc m rho b a e d Ho Hr He Hd Hrev i).
  + change (same_distribution
      (pair_family fail (pair_finish d e pc) (instruction d) (instruction e) m rho)
      (pair_family fail (pair_finish e d pc) (instruction e) (instruction d) m rho)).
    have Efinish : pair_finish e d pc = (fun t s st r => pair_finish d e pc s t st r).
      apply/funext=>t; apply/funext=>s; apply/funext=>st; apply/funext=>r.
      by rewrite /pair_finish (@descriptor_updates_commute _ p pc m a b d e Hd He Hdis s t).
    rewrite Efinish.
    exact: (@local_pair_commute _ fail (pair_finish d e pc)
      (instruction d) (instruction e) m rho (@pair_finish_failure d e pc)
      (enabled_instruction_wf Ho Hd) (enabled_instruction_wf Ho He)
      Hr Hst Hts Hwrite Hquant).
Qed.

Lemma global_join c mu nu : @good P c -> global_step p c mu -> global_step p c nu ->
  projected_join (fmap project mu) (fmap project nu).
Proof.
case: c=>[[pc store] rho] [Hr Ho] Hmu Hnu.
have [a Ha] := labeled_step_complete Hmu.
have [b Hb] := labeled_step_complete Hnu.
case: (@labeled_steps_disjoint_or_equal P a b _ _ _ Ha Hb)=>[E|Hdis].
- subst b; have E := @labeled_step_deterministic n p a _ _ _ (@processes_wf P) Ho Ha Hb.
  rewrite E; exact: projected_join_refl.
- have [m [d [Hstore [Hd [Hwf Emu]]]]]:= labeled_step_descriptor Ho Ha.
  have [m' [e [Hstore' [He [Hwf' Enu]]]]]:= labeled_step_descriptor Ho Hb.
  change (store = Some m) in Hstore; change (store = Some m') in Hstore'.
  have Em : m' = m by congruence.
  subst m'; subst store.
  rewrite Emu Enu -!instrument_runE //.
  exact: (@descriptor_join pc m rho a b d e Ho Hr Hd He Hdis).
Qed.

Theorem projected_two_step_diamond c mu nu : step c mu -> step c nu -> projected_join mu nu.
Proof.
move=>Hmu Hnu; inversion Hmu; subst; inversion Hnu; subst; try congruence.
all: try solve [exfalso; match goal with
  | Ht : terminal p ?c, Hs : global_step p ?c ?mu |- _ => exact (Ht _ Hs)
  end].
all: try exact: projected_join_refl.
eapply global_join; eassumption.
Qed.

End Program.
End DistributedConfluence.
