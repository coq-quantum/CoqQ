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

Module DistributedWeighted.
Import DistributedLanguage DistributedOperational DistributedDistribution.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Import Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Local Notation C := hermitian.C.

Definition weighted_sum {X : Type} {H : chsType} (mu : family X)
    (f : X -> 'End(H)) :=
  sum (fun i => branch_weight mu i *: f (branch_value mu i)).

Lemma weighted_summable X (H : chsType) (mu : family X) (f : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  summable (fun i => branch_weight mu i *: f (branch_value mu i)).
Proof.
move=>Hm Hf; exists 1; near=>A.
apply: (le_trans (y := psum (branch_weight mu) A)).
- apply: ler_sum=>i _; rewrite /normf normrZ ger0_norm ?(proj1 (proj2 Hm)) //.
  rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l=>//.
  exact: (proj1 (proj2 Hm)).
- exact: (psum_le1_mu (probability_distribution Hm)).
Unshelve. end_near.
Qed.

Lemma weighted_partial_bound X (H : chsType) (mu : family X) (f : X -> 'End(H)) A :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  psum (fun i => `|branch_weight mu i *: f (branch_value mu i)|) A <= 1.
Proof.
move=>Hm Hf; apply: (le_trans (y := psum (branch_weight mu) A)).
- apply: ler_sum=>i _; rewrite normrZ ger0_norm ?(proj1 (proj2 Hm)) //.
  rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l=>//.
  exact: (proj1 (proj2 Hm)).
- exact: (psum_le1_mu (probability_distribution Hm)).
Qed.

Lemma weighted_norm X (H : chsType) (mu : family X) (f : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) -> `|weighted_sum mu f| <= 1.
Proof.
move=>Hm Hf; have Hs := weighted_summable Hm Hf.
change (`|sum (Summable.build Hs)| <= 1).
apply: (le_trans (summable_sum_ler_norm _)).
apply: etlim_le; first exact: summable_norm_is_cvg.
move=>A; exact: weighted_partial_bound Hm Hf.
Qed.

Lemma weighted_certain X (H : chsType) x (f : X -> 'End(H)) :
  weighted_sum (certain x) f = f x.
Proof.
rewrite /weighted_sum /certain /= fin_dom_sum (bigD1 tt) //= scale1r.
by rewrite big1 ?addr0 // => [[]].
Qed.

Lemma weighted_positive X (H : chsType) (mu : family X) (f : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  (forall x, 0%:VF ⊑ f x) -> 0%:VF ⊑ weighted_sum mu f.
Proof.
move=>Hm Hf Hp; apply: lim_gev_near.
- by apply: norm_bounded_cvg; apply: weighted_summable.
- near=>A; apply: sumv_ge0=>i _.
  by rewrite scalev_ge0 ?(proj1 (proj2 Hm)) ?Hp.
Unshelve. end_near.
Qed.

Lemma weighted_linear X (H : chsType) (mu : family X) (f : X -> 'End(H))
    (L : {linear 'End(H) -> C}) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  L (weighted_sum mu f) = family_observe mu (fun x => L (f x)).
Proof.
move=>Hm Hf; rewrite /weighted_sum cvg_linear_sum.
- by apply: norm_bounded_cvg; apply: weighted_summable.
- by apply: eq_sum=>i; rewrite /= linearZ.
Qed.

Definition matrix_observer (H : chsType) (u v : H) (A : 'End(H)) : C :=
  [< u; A v >].
Lemma matrix_observer_linear (H : chsType) (u v : H) : linear (matrix_observer u v).
Proof. by move=>a A B; rewrite /matrix_observer add_lfunE scale_lfunE dotpPr. Qed.
HB.instance Definition _ (H : chsType) (u v : H) :=
  GRing.isLinear.Build C 'End(H) C *:%R (matrix_observer u v) (matrix_observer_linear u v).

Lemma weighted_same X (H : chsType) (mu nu : family X) (f : X -> 'End(H)) :
  probability_family mu -> probability_family nu ->
  same_distribution mu nu -> (forall x, `|f x| <= 1) ->
  weighted_sum mu f = weighted_sum nu f.
Proof.
move=>Hm Hn E Hf; apply/lfunP=>v; apply/intro_dotl=>u.
change (matrix_observer u v (weighted_sum mu f) = matrix_observer u v (weighted_sum nu f)).
rewrite !weighted_linear //; apply: E.
have [M [HM Hbound]] := (linear_bounded (matrix_observer u v : {linear 'End(H) -> C})).
exists M=>x; apply: (le_trans (Hbound (f x))).
rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l=>//; exact: ltW HM.
Qed.

Section BindWeighted.
Context {X Y : Type} {H : chsType} (mu : family X)
  (nu : branch_index mu -> family Y) (f : Y -> 'End(H)).
Hypothesis Hmu : probability_family mu.
Hypothesis Hnu : forall i, 0 < branch_weight mu i -> probability_family (nu i).
Hypothesis Hf : forall y, `|f y| <= 1.

Let row i ij := @bind_row X Y mu nu i ij *:
  f (branch_value (bind_family mu nu) ij).

Lemma weighted_bind_rectangle A B :
  psum (fun i => psum (fun ij => `|row i ij|) B) A <= 1.
Proof.
apply: (le_trans (y := psum (fun i =>
  psum (fun ij => `|@bind_row X Y mu nu i ij|) B) A)).
- apply: ler_sum=>i _; apply: ler_sum=>ij _.
  rewrite /row normrZ -[X in _ <= X]mulr1.
  by apply: ler_wpM2l=>//; apply: Hf.
- exact: (@bind_rectangle_bound X Y mu nu Hmu Hnu A B).
Qed.

Lemma weighted_bind_column ij : sum (fun i => row i ij) =
    branch_weight (bind_family mu nu) ij *: f (branch_value (bind_family mu nu) ij).
Proof.
rewrite (fin_supp_sum (S := [fset projT1 ij])) ?psum1 /row ?bind_rowE ?eqxx //.
by move=>i; rewrite inE=>/negPf Hi; rewrite bind_rowE Hi scale0r.
Qed.

Lemma weighted_bind_row i : sum (row i) = branch_weight mu i *: weighted_sum (nu i) f.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have Er : (row i \o @bind_encode X Y mu nu i)%FUN =
      (fun j => branch_weight mu i *: (branch_weight (nu i) j *: f (branch_value (nu i) j))).
    by apply/funext=>j; rewrite /= /row /bind_row bind_encodeK /= scalerA.
  rewrite (sum_reindex (@bind_encodeK X Y mu nu i) (@bind_decodeK X Y mu nu i)).
    by move=>ij E; rewrite /row /bind_row E /= scale0r.
    rewrite Er; exact: summable_funZ (weighted_summable Hi Hf).
  rewrite Er.
  change (sum (branch_weight mu i *: Summable.build (weighted_summable Hi Hf)) =
    branch_weight mu i *: weighted_sum (nu i) f).
  by rewrite summable_sumZ.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  rewrite (eq_sum (g := fun _ => 0)).
    by move=>ij; rewrite /row (bind_row_zero Z) scale0r.
  by rewrite summable_sum_cst0 Z scale0r.
Qed.

Lemma weighted_bind_summable :
  summable (fun i => branch_weight mu i *: weighted_sum (nu i) f).
Proof.
have rect : exists M, forall A B,
    psum (fun i => psum (fun ij => `|row i ij|) B) A <= M.
  by exists 1=>A B; apply: weighted_bind_rectangle.
have [_ [_ [Hs _]]] := pseries_ubounded_cvg rect.
have E : (fun i => sum (row i)) = (fun i => branch_weight mu i *: weighted_sum (nu i) f).
  by apply/funext=>i; rewrite weighted_bind_row.
by rewrite -E.
Qed.

Theorem weighted_bind : weighted_sum (bind_family mu nu) f =
    sum (fun i => branch_weight mu i *: weighted_sum (nu i) f).
Proof.
have rect : exists M, forall A B,
    psum (fun i => psum (fun ij => `|row i ij|) B) A <= M.
  by exists 1=>A B; apply: weighted_bind_rectangle.
transitivity (sum (fun i => sum (row i))).
- rewrite (pseries2_exchange_lim rect); apply: eq_sum=>ij.
  by rewrite weighted_bind_column.
- by apply: eq_sum=>i; rewrite weighted_bind_row.
Qed.

End BindWeighted.

End DistributedWeighted.
