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
From quantum.example.distributive Require Import language operational scheduler local_actions instruments interchange progress observables distribution.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedLocalDiamond.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions
  DistributedInstruments DistributedInterchange DistributedProgress DistributedObservables DistributedDistribution.
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
