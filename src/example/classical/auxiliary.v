(* Order separation and continuous expectations. See EXPECTATION-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel predicate hoare rules assertion_algebra assertion_series.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQAuxiliary.
Import CQAssertion CQAssertionAlgebra CQAssertionSeries CQPredicate CQRules.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation C := hermitian.C.
Implicit Types P Q : assertion.

Lemma valid_bottom total c : CQHoare.valid total semantic_bottom c semantic_bottom.
Proof. apply/(proj2 (valid_iff _ _ _ _)); exact: semantic_bottom_le. Qed.

Lemma valid_top c : CQHoare.valid false semantic_top c semantic_top.
Proof.
apply/(proj2 (valid_iff _ _ _ _)); rewrite /pre /xp /= wlp_top.
exact: semantic_le_refl.
Qed.

Lemma valid_disjunction total c p q P Q :
  CQHoare.valid total (mask p P) c Q -> CQHoare.valid total (mask q P) c Q ->
  CQHoare.valid total (mask (predU p q) P) c Q.
Proof.
move=>/(proj1 (valid_iff _ _ _ _)) Vp /(proj1 (valid_iff _ _ _ _)) Vq.
apply/(proj2 (valid_iff _ _ _ _)); exact: mask_or_le Vp Vq.
Qed.

Lemma valid_disjoint_sum total c (p q : pred cmem) (P Q R S : assertion) :
  (forall i, q i -> ~~ p i) ->
  (forall i, (S i : 'End(Hq)) = (mask p P i : 'End(Hq)) + (mask q Q i : 'End(Hq))) ->
  CQHoare.valid total (mask p P) c R -> CQHoare.valid total (mask q Q) c R ->
  CQHoare.valid total S c R.
Proof.
move=>disj SE /(proj1 (valid_iff _ _ _ _)) Vp /(proj1 (valid_iff _ _ _ _)) Vq.
apply/(proj2 (valid_iff _ _ _ _)); exact: mask_disjoint_sum_le disj SE Vp Vq.
Qed.

Lemma valid_sup total c (F : nat -> assertion) Q :
  semantic_chain F -> (forall n, CQHoare.valid total (F n) c Q) ->
  CQHoare.valid total (semantic_sup F) c Q.
Proof.
move=>inc VF; apply/(proj2 (valid_iff _ _ _ _)).
exact (@semantic_sup_least cmem Hq F (pre total c Q) inc
  (fun n => (proj1 (valid_iff total (F n) c Q)) (VF n))).
Qed.

Lemma valid_finite_linear_total (J : finType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, CQHoare.valid true (F j) c (G j)) -> CQHoare.valid true P c Q.
Proof.
move=>wn PE QE V rho.
rewrite (@expect_finite_linear cmem Hq J w F P rho PE)
  (@expect_finite_linear cmem Hq J w G Q (CQHoare.run c rho) QE).
by apply: ler_sum=>j _; apply: ler_wpM2l; [apply: wn | apply: V].
Qed.

Lemma valid_finite_linear_partial (J : finType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) -> (\sum_j w j <= 1) ->
  (forall i, (P i : 'End(Hq)) = \sum_j w j *: (F j i : 'End(Hq))) ->
  (forall i, (Q i : 'End(Hq)) = \sum_j w j *: (G j i : 'End(Hq))) ->
  (forall j, CQHoare.valid false (F j) c (G j)) -> CQHoare.valid false P c Q.
Proof.
move=>wn wb PE QE V; apply/CQHoare.valid_partial_loss=>rho.
rewrite (@expect_finite_linear cmem Hq J w F P rho PE)
  (@expect_finite_linear cmem Hq J w G Q (CQHoare.run c rho) QE) -addrA.
pose loss := CQState.mass rho - CQState.mass (CQHoare.run c rho).
have lp : 0 <= loss by rewrite /loss subr_ge0; exact: CQKernel.apply_mass.
apply: (le_trans (y := \sum_j w j * (expect (G j) (CQHoare.run c rho) + loss))).
- apply: ler_sum=>j _; apply: ler_wpM2l; first exact: wn.
  by move: ((proj1 (CQHoare.valid_partial_loss _ _ _) (V j)) rho); rewrite -addrA.
- under eq_bigr do rewrite mulrDr.
  rewrite big_split /= -mulr_suml lerD2l.
  by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r.
Qed.

Lemma valid_series_total (J : choiceType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, CQHoare.valid true (F j) c (G j)) -> CQHoare.valid true P c Q.
Proof.
move=>wn SF SG PE QE V rho.
rewrite (@expect_series cmem J Hq w F P wn SF PE rho)
  (@expect_series cmem J Hq w G Q wn SG QE (CQHoare.run c rho)).
rewrite /sum; apply: ler_etlim.
- apply: norm_bounded_cvg; exact: (@expect_series_summable cmem J Hq w F P wn SF PE rho).
- apply: norm_bounded_cvg; exact: (@expect_series_summable cmem J Hq w G Q wn SG QE (CQHoare.run c rho)).
- move=>A; apply: ler_sum=>j _.
  by apply: ler_wpM2l; [apply: wn | apply: V].
Qed.

Lemma valid_series_partial (J : choiceType) (w : J -> C)
    (F G : J -> assertion) P Q c :
  (forall j, 0 <= w j) -> summable w -> sum w <= 1 ->
  (forall i, summable (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, summable (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall i, (P i : 'End(Hq)) = sum (fun j => w j *: (F j i : 'End(Hq)))) ->
  (forall i, (Q i : 'End(Hq)) = sum (fun j => w j *: (G j i : 'End(Hq)))) ->
  (forall j, CQHoare.valid false (F j) c (G j)) -> CQHoare.valid false P c Q.
Proof.
move=>wn sw wb SF SG PE QE V; apply/CQHoare.valid_partial_loss=>rho.
rewrite (@expect_series cmem J Hq w F P wn SF PE rho)
  (@expect_series cmem J Hq w G Q wn SG QE (CQHoare.run c rho)) -addrA.
pose loss := CQState.mass rho - CQState.mass (CQHoare.run c rho).
have lp : 0 <= loss by rewrite /loss subr_ge0; exact: CQKernel.apply_mass.
pose g := Summable.build (@expect_series_summable cmem J Hq w G Q wn SG QE (CQHoare.run c rho)).
pose weights := Summable.build sw.
have E j : (g + loss *: weights) j = w j * (expect (G j) (CQHoare.run c rho) + loss).
  change (w j * expect (G j) (CQHoare.run c rho) + loss * w j =
    w j * (expect (G j) (CQHoare.run c rho) + loss)).
  by rewrite mulrDr [loss * _]mulrC.
apply: (le_trans (y := sum (g + loss *: weights))).
- rewrite /sum; apply: ler_etlim.
  + apply: norm_bounded_cvg; exact: (@expect_series_summable cmem J Hq w F P wn SF PE rho).
  + exact: summable_cvg.
  + move=>A; apply: ler_sum=>j _; rewrite E.
    apply: ler_wpM2l; first exact: wn.
    by move: ((proj1 (CQHoare.valid_partial_loss _ _ _) (V (val j))) rho); rewrite -addrA.
- rewrite summable_sumD summable_sumZ /g /= lerD2l.
  change (loss * sum w <= loss).
  by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l.
Qed.

Lemma derives_bottom total c : derives total semantic_bottom c semantic_bottom.
Proof. apply: derives_complete; exact: valid_bottom. Qed.
Lemma derives_top c : derives false semantic_top c semantic_top.
Proof. apply: derives_complete; exact: valid_top. Qed.
Lemma derives_disjunction total c p q P Q :
  derives total (mask p P) c Q -> derives total (mask q P) c Q ->
  derives total (mask (predU p q) P) c Q.
Proof.
move=>/derives_sound Vp /derives_sound Vq; apply: derives_complete.
exact: valid_disjunction Vp Vq.
Qed.

End CQAuxiliary.
