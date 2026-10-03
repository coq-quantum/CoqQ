(* A finite-horizon argument for probabilistic strong diamonds.
   This abstract theorem is separate from establishing its hypotheses for
   distributed program transitions; it is not itself Theorem 3.9. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.distributive Require Import operational distribution weighted.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ProbabilisticDiamond.
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
  forall n k, weighted_sum (stages k) (horizon n) = weighted_sum (stages (k+n)%N) observe.
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
