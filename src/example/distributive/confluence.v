(* Distributive: confluence. See README.md and PROOF_NOTES.md. *)
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
From mathcomp.classical Require Import boolp classical_sets functions.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable.
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From Stdlib Require Import String.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.example.distributive Require Import language operational.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module ProbabilisticDiamond.
(* A finite-horizon argument for probabilistic strong diamonds.
   This abstract theorem is separate from establishing its hypotheses for
   distributed program transitions; it is not itself Theorem 3.9. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedOperational DistributedDistribution DistributedWeighted.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.

Section FiniteHorizon.
Context {X : Type} {H : chsType}.
Variable step : X -> family X -> Prop.
Variable policy : X -> family X.
Variable observe : X -> 'End(H).
Hypothesis step_probability : forall x mu, step x mu -> probability_family mu.
Hypothesis policy_step : forall x, step x (policy x).
Hypothesis observe_bound : forall x, `|observe x| <= 1.
Hypothesis one_step_agreement : forall x mu nu, step x mu -> step x nu ->
  weighted_sum mu observe = weighted_sum nu observe.
Hypothesis two_step_diamond : forall x mu nu, step x mu -> step x nu ->
  exists (left : branch_index mu -> family X) (right : branch_index nu -> family X),
    (forall i, 0 < branch_weight mu i -> step (branch_value mu i) (left i)) /\
    (forall i, 0 < branch_weight nu i -> step (branch_value nu i) (right i)) /\
    same_distribution (bind_family mu left) (bind_family nu right).

Fixpoint horizon n x : 'End(H) :=
  if n is n'.+1 then weighted_sum (policy x) (horizon n') else observe x.

Lemma horizon_bound n x : `|horizon n x| <= 1.
Proof.
elim: n x=>[|n IH] x /=; first exact: observe_bound.
apply: weighted_norm; last exact: IH.
exact: step_probability (policy_step x).
Qed.

Theorem horizon_step n x mu : step x mu ->
  weighted_sum mu (horizon n) = horizon n.+1 x.
Proof.
elim: n x mu=>[|n IH] x mu Hstep.
  exact: one_step_agreement Hstep (policy_step x).
have Hmu := step_probability Hstep.
have Hnu := step_probability (policy_step x).
have [left [right [Hl [Hr Heq]]]] := two_step_diamond Hstep (policy_step x).
have Pl : forall i, 0 < branch_weight mu i -> probability_family (left i).
  move=>i Hi; exact: step_probability (Hl i Hi).
have Pr : forall i, 0 < branch_weight (policy x) i -> probability_family (right i).
  move=>i Hi; exact: step_probability (Hr i Hi).
have EL : weighted_sum mu (horizon n.+1) =
    weighted_sum (bind_family mu left) (horizon n).
  rewrite (@weighted_bind X X H mu left (horizon n) Hmu Pl (horizon_bound n)).
  apply: eq_sum=>i; case Pi: (0 < branch_weight mu i).
    by rewrite (IH _ _ (Hl i Pi)).
  have Zi : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt Pi orbF eq_sym=>/eqP.
  by rewrite Zi !scale0r.
have ER : weighted_sum (policy x) (horizon n.+1) =
    weighted_sum (bind_family (policy x) right) (horizon n).
  rewrite (@weighted_bind X X H (policy x) right (horizon n) Hnu Pr (horizon_bound n)).
  apply: eq_sum=>i; case Pi: (0 < branch_weight (policy x) i).
    by rewrite (IH _ _ (Hr i Pi)).
  have Zi : branch_weight (policy x) i = 0.
    by move: (proj1 (proj2 Hnu) i); rewrite le_eqVlt Pi orbF eq_sym=>/eqP.
  by rewrite Zi !scale0r.
change (weighted_sum mu (horizon n.+1) = weighted_sum (policy x) (horizon n.+1)).
rewrite EL ER.
exact: (weighted_same (bind_family_probability Hmu Pl)
  (bind_family_probability Hnu Pr) Heq (horizon_bound n)).
Qed.

Definition evolution (mu nu : family X) :=
  probability_family nu /\
  exists next : branch_index mu -> family X,
    (forall i, 0 < branch_weight mu i -> step (branch_value mu i) (next i)) /\
    same_distribution nu (bind_family mu next).

Lemma horizon_evolution n mu nu : probability_family mu -> evolution mu nu ->
  weighted_sum mu (horizon n.+1) = weighted_sum nu (horizon n).
Proof.
move=>Hmu [Hnu [next [Hnext Heq]]].
have Pnext : forall i, 0 < branch_weight mu i -> probability_family (next i).
  move=>i Hi; exact: step_probability (Hnext i Hi).
rewrite (weighted_same Hnu (bind_family_probability Hmu Pnext) Heq (horizon_bound n)).
rewrite (@weighted_bind X X H mu next (horizon n) Hmu Pnext (horizon_bound n)).
apply: eq_sum=>i; case Pi: (0 < branch_weight mu i).
  by rewrite (horizon_step n (Hnext i Pi)).
have Zi : branch_weight mu i = 0.
  by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt Pi orbF eq_sym=>/eqP.
by rewrite Zi !scale0r.
Qed.

Lemma horizon_stages (stages : nat -> family X) :
  (forall k, probability_family (stages k)) ->
  (forall k, evolution (stages k) (stages k.+1)) ->
  forall n k, weighted_sum (stages k) (horizon n) = weighted_sum (stages (k + n)%N) observe.
Proof.
move=>Hprob Hstep; elim=>[|n IH] k.
  by rewrite addn0.
rewrite (horizon_evolution n (Hprob k) (Hstep k)) IH.
by rewrite addSn addnS.
Qed.

Theorem finite_horizon_unique (stages : nat -> family X) x :
  same_distribution (stages 0%N) (certain x) ->
  (forall k, probability_family (stages k)) ->
  (forall k, evolution (stages k) (stages k.+1)) ->
  forall n, weighted_sum (stages n) observe = horizon n x.
Proof.
move=>Hinit Hprob Hstep n.
rewrite -(add0n n) -(horizon_stages Hprob Hstep n 0%N).
rewrite (weighted_same (Hprob 0%N) (certain_probability x) Hinit (horizon_bound n)).
exact: weighted_certain.
Qed.

End FiniteHorizon.
End ProbabilisticDiamond.


Module DistributedLocalDiamond.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments DistributedInterchange DistributedProgress DistributedObservables DistributedDistribution.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Definition resume_store s m i := odflt m (@local_store s i m).

Lemma resume_preserves_map s t m i j :
  (forall x, x \in statement_changes s -> ~ statement_reads t x) ->
  @local_map t (@resume_store s m i) j = @local_map t m j.
Proof.
move=>Hfresh; have H := @local_store_outcome s m i.
change (store_outcome (statement_changes s) m (@local_store s i m)) in H.
case: H=>[H|[H|[u [x [v [Hx H]]]]]]; rewrite /resume_store H /= //.
exact: (@local_map_external_update t m u x v j (Hfresh _ Hx)).
Qed.

Lemma resume_preserves_control s t m i j :
  (forall x, x \in statement_changes s -> ~ statement_reads t x) ->
  (@local_control t (@resume_store s m i) j).1 = (@local_control t m j).1.
Proof.
move=>Hfresh; have H := @local_store_outcome s m i.
change (store_outcome (statement_changes s) m (@local_store s i m)) in H.
case: H=>[H|[H|[u [x [v [Hx H]]]]]]; rewrite /resume_store H /= //.
by rewrite (@local_control_external t m u x v j (Hfresh _ Hx)).
Qed.

Lemma local_family_probability s m rho : statement_wf s -> rho \is den1lf ->
  probability_family (local_family s m rho).
Proof.
move=>Hwf Hr; rewrite -local_realization //.
exact: (@local_step_probability (local_config s (Some m) rho)
  (local_successor s m rho) (@local_successor_step s Hwf m rho) Hr).
Qed.

Definition joint_weight (E F : 'SO(Hq)) rho :=
  \Tr (E rho) * \Tr (F (normalized_output E rho)).

Lemma joint_weightE (E F : 'CP(Hq)) rho : rho \is den1lf ->
  joint_weight E F rho = \Tr (F (E rho)).
Proof.
move=>Hr; rewrite /joint_weight -linearZ /= -linearZ /=.
by rewrite (weighted_normalized_output E Hr).
Qed.

Lemma joint_weight_commute (E F : 'CP(Hq)) rho :
  rho \is den1lf -> E :o F = F :o E -> joint_weight E F rho = joint_weight F E rho.
Proof.
by move=>Hr Hcomm; rewrite !joint_weightE //; exact: commuting_joint_weight.
Qed.

Lemma joint_state_commute (E F : 'CP(Hq)) rho :
  rho \is den1lf -> E :o F = F :o E -> joint_weight E F rho != 0 ->
  normalized_output F (normalized_output E rho) =
  normalized_output E (normalized_output F rho).
Proof.
move=>Hr Hcomm Hnz.
have H := commuting_normalized_outputs Hr Hcomm.
change (joint_weight E F rho *: normalized_output F (normalized_output E rho) =
  joint_weight F E rho *: normalized_output E (normalized_output F rho)) in H.
rewrite -(joint_weight_commute Hr Hcomm) in H.
have := congr1 (fun A : 'End(Hq) => (joint_weight E F rho)^-1 *: A) H.
by rewrite !scalerA mulVf // !scale1r.
Qed.

Lemma joint_observe_commute (E F : 'CP(Hq)) rho (f : 'End(Hq) -> C) :
  rho \is den1lf -> E :o F = F :o E ->
  joint_weight E F rho * f (normalized_output F (normalized_output E rho)) =
  joint_weight F E rho * f (normalized_output E (normalized_output F rho)).
Proof.
move=>Hr Hcomm; case Hnz: (joint_weight E F rho == 0).
- move/eqP: Hnz=>Hz; rewrite -(joint_weight_commute Hr Hcomm) Hz !mul0r; by [].
- have Hne : joint_weight E F rho != 0 by rewrite Hnz.
  by rewrite (joint_state_commute Hr Hcomm Hne) (joint_weight_commute Hr Hcomm).
Qed.


Definition combine_store (first second : option cmem) :=
  if first is Some _ then second else None.

Lemma combine_storeE s t m i j :
  combine_store (@local_store s i m) (@local_store t j (@resume_store s m i)) =
  store_compose (@local_store s i) (@local_store t j) m.
Proof. by rewrite /combine_store /store_compose /resume_store; case: local_store. Qed.

Section PairFamilies.
Context {X : Type} (failure : X)
  (finish : statement -> statement -> option cmem -> 'End(Hq) -> X).
Hypothesis finish_failure : forall s t rho, finish s t None rho = failure.

Definition second_family s t m rho (i : local_index s) : family X :=
  let c := @local_control s m i in
  let r := normalized_output (@local_map s m i) rho in
  if c.2 is Some m' then
    fmap (fun d => finish c.1 d.1.1 d.1.2 d.2) (local_family t m' r)
  else certain failure.

Definition ghost_second s t m rho (i : local_index s) : family X :=
  let c := @local_control s m i in
  let r := normalized_output (@local_map s m i) rho in
  fmap (fun d => finish c.1 d.1.1 (combine_store c.2 d.1.2) d.2)
    (local_family t (@resume_store s m i) r).

Definition pair_family s t m rho :=
  bind_family (local_family s m rho) (@second_family s t m rho).
Definition ghost_pair s t m rho :=
  bind_family (local_family s m rho) (@ghost_second s t m rho).

Lemma second_probability s t m rho i : statement_wf t -> rho \is den1lf ->
  probability_family (@second_family s t m rho i).
Proof.
move=>Ht Hr; rewrite /second_family; case: ((@local_control s m i).2)=>[m'|].
- apply: fmap_probability.
  exact: (@local_family_probability t m'
    (normalized_output (@local_map s m i) rho) Ht
    (@normalized_output_den1 (@local_cp s m i) rho Hr)).
- exact: certain_probability.
Qed.

Lemma ghost_second_probability s t m rho i : statement_wf t -> rho \is den1lf ->
  probability_family (@ghost_second s t m rho i).
Proof.
move=>Ht Hr; apply: fmap_probability.
exact: (@local_family_probability t (@resume_store s m i)
  (normalized_output (@local_map s m i) rho) Ht
  (@normalized_output_den1 (@local_cp s m i) rho Hr)).
Qed.

Lemma second_ghost_same s t m rho i : statement_wf t -> rho \is den1lf ->
  same_distribution (@second_family s t m rho i) (@ghost_second s t m rho i).
Proof.
move=>Ht Hr; rewrite /second_family /ghost_second /resume_store /local_store.
case E: ((@local_control s m i).2)=>[m'|] /=.
- by move=>f Hf.
- have Hprob := @local_family_probability t m
    (normalized_output (@local_map s m i) rho) Ht
    (@normalized_output_den1 (@local_cp s m i) rho Hr).
  move=>f Hf; rewrite observe_certain.
  symmetry; change (family_observe
    (local_family t m (normalized_output (@local_map s m i) rho)) (fun d =>
    f (finish (@local_control s m i).1 d.1.1 None d.2)) = f failure).
  rewrite /family_observe (eq_sum (g := fun j =>
    branch_weight (local_family t m (normalized_output (@local_map s m i) rho)) j * f failure)).
    by move=>j; rewrite finish_failure.
  exact: (@observe_constant local_configuration
    (local_family t m (normalized_output (@local_map s m i) rho)) (f failure) Hprob).
Qed.

Lemma pair_ghost_same s t m rho : statement_wf s -> statement_wf t -> rho \is den1lf ->
  same_distribution (pair_family s t m rho) (ghost_pair s t m rho).
Proof.
move=>Hs Ht Hr f [M HM].
have HM0 : 0 <= M := le_trans (normr_ge0 (f failure)) (HM failure).
have P1 := @local_family_probability s m rho Hs Hr.
have P2 := fun i => @second_probability s t m rho i Ht Hr.
have PG := fun i => @ghost_second_probability s t m rho i Ht Hr.
rewrite /pair_family /ghost_pair
  (@observe_bind _ _ _ _ f M P1 (fun i _ => P2 i) HM0 HM)
  (@observe_bind _ _ _ _ f M P1 (fun i _ => PG i) HM0 HM).
apply: eq_sum=>i; congr (_ * _); apply: (@second_ghost_same s t m rho i Ht Hr f).
by exists M.
Qed.

Definition frozen_value s t m rho i j :=
  finish (@local_control s m i).1 (@local_control t m j).1
    (store_compose (@local_store s i) (@local_store t j) m)
    (normalized_output (@local_map t m j)
      (normalized_output (@local_map s m i) rho)).

Lemma ghost_observe s t m rho (f : X -> C) M :
  statement_wf s -> statement_wf t -> rho \is den1lf ->
  (forall x, x \in statement_changes s -> ~ statement_reads t x) ->
  0 <= M -> (forall x, `|f x| <= M) ->
  family_observe (ghost_pair s t m rho) f =
    sum (fun i => sum (fun j =>
      joint_weight (@local_map s m i) (@local_map t m j) rho *
        f (@frozen_value s t m rho i j))).
Proof.
move=>Hs Ht Hr Hfresh HM0 HM.
have P1 := @local_family_probability s m rho Hs Hr.
have PG := fun i => @ghost_second_probability s t m rho i Ht Hr.
rewrite /ghost_pair (@observe_bind_nested _ _ _ _ f M P1 PG HM0 HM).
apply: eq_sum=>i; apply: eq_sum=>j.
rewrite /ghost_second /local_family /fmap /= /frozen_value /joint_weight.
rewrite (@resume_preserves_map s t m i j Hfresh)
  (@resume_preserves_control s t m i j Hfresh).
by rewrite (@combine_storeE s t m i j) mulrA.
Qed.

End PairFamilies.

Lemma joint_exchange s t m rho (f : local_index s -> local_index t -> C) M :
  statement_wf s -> statement_wf t -> rho \is den1lf ->
  0 <= M -> (forall i j, `|f i j| <= M) ->
  sum (fun i => sum (fun j =>
    joint_weight (@local_map s m i) (@local_map t m j) rho * f i j)) =
  sum (fun j => sum (fun i =>
    joint_weight (@local_map s m i) (@local_map t m j) rho * f i j)).
Proof.
move=>Hs Ht Hr HM Hf.
pose w i := \Tr (@local_map s m i rho).
pose v i j := \Tr (@local_map t m j
  (normalized_output (@local_map s m i) rho)).
have Pw : probability_family (@Family _ (local_index s) w id).
  exact: (@local_family_probability s m rho Hs Hr).
have Pv : forall i, probability_family (@Family _ (local_index t) (v i) id).
  move=>i; exact: (@local_family_probability t m
    (normalized_output (@local_map s m i) rho) Ht
    (@normalized_output_den1 (@local_cp s m i) rho Hr)).
transitivity (sum (fun i => sum (fun j => w i * (v i j * f i j)))).
- by apply: eq_sum=>i; apply: eq_sum=>j; rewrite /joint_weight /w /v mulrA.
- rewrite (@probability_exchange (local_index s) (local_index t) w v f M Pw Pv HM Hf).
  by apply: eq_sum=>j; apply: eq_sum=>i; rewrite /joint_weight /w /v mulrA.
Qed.

Local Close Scope fset_scope.

Lemma local_pair_commute X (failure : X)
  (finish : statement -> statement -> option cmem -> 'End(Hq) -> X)
  s t m rho :
  (forall u v r, finish u v None r = failure) ->
  statement_wf s -> statement_wf t -> rho \is den1lf ->
  (forall x, x \in statement_changes s -> ~ statement_reads t x) ->
  (forall x, x \in statement_changes t -> ~ statement_reads s x) ->
  [disjoint statement_changes s & statement_changes t]%fset ->
  [disjoint statement_quantum s & statement_quantum t] ->
  same_distribution (pair_family failure finish s t m rho)
    (pair_family failure (fun v u st r => finish u v st r) t s m rho).
Proof.
move=>Hfailure Hs Ht Hr Hst Hts Hwrite Hquant f [M HM].
have HM0 : 0 <= M := le_trans (normr_ge0 (f failure)) (HM failure).
have Hf : exists M, forall x, `|f x| <= M by exists M.
have Hswap : forall v u r, (fun v u st r => finish u v st r) v u None r = failure.
  by move=>v u r; apply: Hfailure.
rewrite (@pair_ghost_same X failure finish Hfailure s t m rho Hs Ht Hr f Hf)
  (@pair_ghost_same X failure (fun v u st r => finish u v st r)
    Hswap t s m rho Ht Hs Hr f Hf).
rewrite (@ghost_observe X finish s t m rho f M Hs Ht Hr Hst HM0 HM)
  (@ghost_observe X (fun v u st r => finish u v st r)
    t s m rho f M Ht Hs Hr Hts HM0 HM).
rewrite (@joint_exchange s t m rho
  (fun i j => f (@frozen_value X finish s t m rho i j)) M Hs Ht Hr HM0
  (fun i j => HM _)).
apply: eq_sum=>j; apply: eq_sum=>i.
rewrite /frozen_value (@local_stores_commute s t i j m Hst Hts Hwrite).
exact: (@joint_observe_commute (@local_cp s m i) (@local_cp t m j) rho
  (fun r => f (finish (@local_control s m i).1 (@local_control t m j).1
    (store_compose (@local_store t j) (@local_store s i) m) r)) Hr
  (@local_map_commute s t m m i j Hquant)).
Qed.
End DistributedLocalDiamond.


Module DistributedSchedulerSemantics.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted DistributedResults DistributedResidual DistributedGlobalActions DistributedObservables.
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


Module DistributedConfluence.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments DistributedInterchange DistributedProgress DistributedObservables DistributedDistribution DistributedGlobalInstruments DistributedGlobalActions DistributedResidual DistributedSchedulerSemantics DistributedLocalDiamond DistributedFootprint.
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
