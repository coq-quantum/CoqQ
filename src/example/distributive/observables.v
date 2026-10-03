(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import notation mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import language operational distribution.

Module DistributedObservables.
Import DistributedLanguage DistributedOperational DistributedDistribution.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Notation C := hermitian.C.

Lemma observe_summable X (mu : family X) (f : X -> C) M :
  probability_family mu -> 0 <= M -> (forall x, `|f x| <= M) ->
  summable (fun i => branch_weight mu i * f (branch_value mu i)).
Proof.
move=>Hm HM Hf; exists M; near=>A.
apply: (le_trans (y := psum (branch_weight mu) A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  rewrite /normf normrM ger0_norm ?(proj1 (proj2 Hm)) //.
  by apply: ler_wpM2l=>//; exact: (proj1 (proj2 Hm)).
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (psum_le1_mu (probability_distribution Hm)).
Unshelve. end_near.
Qed.

Lemma observe_constant X (mu : family X) c : probability_family mu ->
  family_observe mu (fun _ => c) = c.
Proof.
move=>Hm; rewrite /family_observe (eq_sum (g := fun i => c * branch_weight mu i));
  first by move=>i; rewrite mulrC.
change (sum (c *: Summable.build (proj1 Hm)) = c).
rewrite summable_sumZ.
change (c * family_mass mu = c).
by rewrite (proj2 (proj2 Hm)) mulr1.
Qed.

Lemma observe_certain X (x : X) f : family_observe (certain x) f = f x.
Proof.
rewrite /family_observe /certain /= fin_dom_sum (bigD1 tt) //= mul1r.
by rewrite big1 ?addr0 // => [[]].
Qed.

Lemma constant_family X Y (mu : family X) (y : Y) : probability_family mu ->
  same_distribution (fmap (fun _ => y) mu) (certain y).
Proof.
move=>Hm f Hf; rewrite observe_certain.
change (family_observe mu (fun _ => f y) = f y).
exact: (@observe_constant X mu (f y) Hm).
Qed.

Section BindObserve.
Context {X Y : Type} (mu : family X) (nu : branch_index mu -> family Y)
  (f : Y -> C) (M : C).
Hypothesis Hmu : probability_family mu.
Hypothesis Hnu : forall i, 0 < branch_weight mu i -> probability_family (nu i).
Hypothesis HM : 0 <= M.
Hypothesis Hf : forall y, `|f y| <= M.

Let row i ij := @bind_row X Y mu nu i ij * f (branch_value (bind_family mu nu) ij).

Lemma observe_bind_rectangle A B :
  psum (fun i => psum (fun ij => `|row i ij|) B) A <= M.
Proof.
apply: (le_trans (y := psum (fun i =>
  psum (fun ij => `|@bind_row X Y mu nu i ij|) B) A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  rewrite mulr_suml; apply: ler_sum=>ij _.
  rewrite /row normrM; by apply: ler_wpM2l=>//; exact: Hf.
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (@bind_rectangle_bound X Y mu nu Hmu Hnu A B).
Qed.

Lemma observe_bind_column ij : sum (fun i => row i ij) =
    branch_weight (bind_family mu nu) ij * f (branch_value (bind_family mu nu) ij).
Proof.
rewrite (fin_supp_sum (S := [fset projT1 ij])) ?psum1 /row ?bind_rowE ?eqxx //.
by move=>i; rewrite inE=>/negPf Hi; rewrite bind_rowE Hi mul0r.
Qed.

Lemma observe_bind_row i : sum (row i) = branch_weight mu i * family_observe (nu i) f.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have Er : (row i \o @bind_encode X Y mu nu i)%FUN =
      (fun j => branch_weight mu i * (branch_weight (nu i) j * f (branch_value (nu i) j))).
    by apply/funext=>j; rewrite /= /row /bind_row bind_encodeK /= mulrA.
  rewrite (sum_reindex (@bind_encodeK X Y mu nu i) (@bind_decodeK X Y mu nu i)).
    by move=>ij E; rewrite /row /bind_row E /= mul0r.
    rewrite Er; exact: summable_funZ (observe_summable Hi HM Hf).
  rewrite Er.
  change (sum (branch_weight mu i *: Summable.build (observe_summable Hi HM Hf)) =
    branch_weight mu i * family_observe (nu i) f).
  by rewrite summable_sumZ.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  rewrite (eq_sum (g := fun _ => 0)).
    by move=>ij; rewrite /row (bind_row_zero Z) mul0r.
  by rewrite summable_sum_cst0 Z mul0r.
Qed.

Lemma observe_bind : family_observe (bind_family mu nu) f =
    sum (fun i => branch_weight mu i * family_observe (nu i) f).
Proof.
have rect : exists M', forall A B,
    psum (fun i => psum (fun ij => `|row i ij|) B) A <= M'.
  by exists M=>A B; apply: observe_bind_rectangle.
transitivity (sum (fun i => sum (row i))).
- rewrite (pseries2_exchange_lim rect); apply: eq_sum=>ij.
  by rewrite observe_bind_column.
- by apply: eq_sum=>i; rewrite observe_bind_row.
Qed.

End BindObserve.

Lemma observe_partial_bound X (mu : family X) (f : X -> C) M A :
  probability_family mu -> 0 <= M -> (forall x, `|f x| <= M) ->
  psum (fun i => `|branch_weight mu i * f (branch_value mu i)|) A <= M.
Proof.
move=>Hm HM Hf; apply: (le_trans (y := psum (branch_weight mu) A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  rewrite normrM ger0_norm ?(proj1 (proj2 Hm)) //.
  by apply: ler_wpM2l=>//; exact: (proj1 (proj2 Hm)).
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (psum_le1_mu (probability_distribution Hm)).
Qed.

Lemma probability_rectangle (I J : choiceType) (w : I -> C) (v : I -> J -> C)
    (f : I -> J -> C) M :
  probability_family (@Family I I w id) ->
  (forall i, probability_family (@Family J J (v i) id)) ->
  0 <= M -> (forall i j, `|f i j| <= M) ->
  forall A B, psum (fun i => psum (fun j => `|w i * (v i j * f i j)|) B) A <= M.
Proof.
move=>Hw Hv HM Hf A B.
apply: (le_trans (y := psum w A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  under eq_bigr do rewrite normrM ger0_norm ?(proj1 (proj2 Hw)) //.
  rewrite -mulr_sumr; apply: ler_wpM2l; first exact: (proj1 (proj2 Hw)).
  have Hp := @observe_partial_bound J (@Family J J (v (val i)) id) (f (val i)) M B
    (Hv (val i)) HM (Hf (val i)).
  exact Hp.
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (psum_le1_mu (probability_distribution Hw)).
Qed.

Lemma probability_exchange (I J : choiceType) (w : I -> C) (v : I -> J -> C)
    (f : I -> J -> C) M :
  probability_family (@Family I I w id) ->
  (forall i, probability_family (@Family J J (v i) id)) ->
  0 <= M -> (forall i j, `|f i j| <= M) ->
  sum (fun i => sum (fun j => w i * (v i j * f i j))) =
  sum (fun j => sum (fun i => w i * (v i j * f i j))).
Proof.
move=>Hw Hv HM Hf; apply: pseries2_exchange_lim.
by exists M=>A B; exact: (@probability_rectangle I J w v f M Hw Hv HM Hf A B).
Qed.


Lemma observe_bind_nested X Y (mu : family X) (nu : branch_index mu -> family Y)
    (f : Y -> C) M :
  probability_family mu -> (forall i, probability_family (nu i)) ->
  0 <= M -> (forall y, `|f y| <= M) ->
  family_observe (bind_family mu nu) f =
    sum (fun i => sum (fun j => branch_weight mu i *
      (branch_weight (nu i) j * f (branch_value (nu i) j)))).
Proof.
move=>Hmu Hnu HM Hf.
rewrite (@observe_bind X Y mu nu f M Hmu (fun i _ => Hnu i) HM Hf).
apply: eq_sum=>i; symmetry.
change (sum (branch_weight mu i *: Summable.build (observe_summable (Hnu i) HM Hf)) =
  branch_weight mu i * family_observe (nu i) f).
by rewrite summable_sumZ.
Qed.

End DistributedObservables.
