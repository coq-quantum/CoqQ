(* Complement rankings: Lemma 5.4 and WhileT′. See RANKING-COMPLEMENT-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.



Module CQRankingComplement.
Import ClassicalLanguage CQAssertion CQRules CQPredicate CQExpectationLimits.

Section Complements.
Context {I : choiceType} {H : chsType}.

Lemma complement_le_iff (P Q : I -> 'FO(H)) :
  semantic_le (complement P) (complement Q) <-> semantic_le Q P.
Proof.
split=>PQ i; have := PQ i.
- by rewrite /complement /= -cplmt_lef.
- by rewrite /complement /= -cplmt_lef.
Qed.

Lemma mask_complement_le_iff (g : pred I) (P Q : I -> 'FO(H)) :
  semantic_le (mask g P) Q <->
  semantic_le (mask g (complement Q)) (complement P).
Proof.
split=>PQ i; case Eg: (g i).
- move: (PQ i); by rewrite /mask Eg /complement /= -cplmt_lef.
- by rewrite /mask Eg; exact: obsf_ge0.
- move: (PQ i); by rewrite /mask Eg /complement /= -cplmt_lef.
- by rewrite /mask Eg; exact: obsf_ge0.
Qed.

Lemma complement_decreasing (f : nat -> I -> 'FO(H)) :
  semantic_chain f -> semantic_decreasing (fun n => complement (f n)).
Proof. by move=>inc n; apply/complement_le_iff; exact: inc. Qed.

Lemma complement_sup_top (f : nat -> I -> 'FO(H)) :
  semantic_decreasing f ->
  (forall i, ((fun n => (f n i : 'End(H))) @ \oo --> 0)%classic) ->
  semantic_sup (fun n => complement (f n)) = semantic_top.
Proof.
move=>dec zero; apply/funext=>i; apply/val_inj.
change ((semantic_sup (fun n => complement (f n)) i : 'End(H)) = \1).
have C1 := semantic_sup_cvg (i := i) (complement_chain dec).
have C2 : ((fun n => (complement (f n) i : 'End(H))) @ \oo --> \1)%classic.
  rewrite -[X in _ --> X](subr0 (\1 : 'End(H))).
  apply: cvgB; [exact: cvg_cst | exact: zero].
by rewrite -(cvg_lim (@norm_hausdorff _ _) C1) (cvg_lim (@norm_hausdorff _ _) C2).
Qed.

Lemma complement_zero_of_sup (f : nat -> I -> 'FO(H)) :
  semantic_chain f -> semantic_sup f = semantic_top ->
  forall i, ((fun n => (complement (f n) i : 'End(H))) @ \oo --> 0)%classic.
Proof.
move=>inc top i.
have C := semantic_sup_cvg (i := i) inc.
rewrite top in C.
have C' : ((fun n => (complement (f n) i : 'End(H))) @ \oo -->
    (\1 - \1 : 'End(H)))%classic.
  apply: cvgB; [exact: cvg_cst | exact: C].
by rewrite subrr in C'.
Qed.
End Complements.

Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma guarded_wp_partial_iff (g : pred cmem) c (R T : assertion) :
  semantic_le (mask g (wp_command c R)) T <->
  CQHoare.valid false (mask g (complement T)) c (complement R).
Proof.
rewrite valid_partial_iff /wlp_command /wlp complementK.
exact: mask_complement_le_iff.
Qed.

Definition ranking_of_partial P b c (f : nat -> assertion)
    (inc : semantic_chain f)
    (ini : semantic_le P (complement (f 0%N)))
    (top : semantic_sup f = semantic_top)
    (step : forall n, CQHoare.valid false (mask (esem b) (f n.+1)) c (f n))
    : ranking P b c.
Proof.
apply: (@Ranking P b c (fun n => complement (f n))).
- exact: complement_decreasing inc.
- exact: ini.
- exact: complement_zero_of_sup inc top.
- move=>n; apply/(proj2 (guarded_wp_partial_iff _ _ _ _)).
  by rewrite !complementK; exact: step.
Defined.

Theorem ranking_iff_partial P b c :
  inhabited (ranking P b c) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall n, CQHoare.valid false (mask (esem b) (f n.+1)) c (f n)).
Proof.
split.
- move=>[r]; exists (fun n => complement (ranking_assertion r n)); split.
  + exact: complement_chain (ranking_decreases r).
  + split; first by rewrite complementK; exact: ranking_initial.
    split.
    * exact: complement_sup_top (ranking_decreases r) (ranking_zero r).
    * move=>n; apply/(proj1 (guarded_wp_partial_iff _ _ _ _)).
      exact: ranking_step.
- move=>[f [inc [ini [top step]]]]; constructor.
  exact: ranking_of_partial inc ini top step.
Qed.

Theorem derives_while_partial_ranking P b c (f : nat -> assertion) :
  derives true (mask (esem b) P) c P ->
  semantic_chain f -> semantic_le P (complement (f 0%N)) ->
  semantic_sup f = semantic_top ->
  (forall n, derives false (mask (esem b) (f n.+1)) c (f n)) ->
  derives true P (While b c) (mask (predC (esem b)) P).
Proof.
move=>inv inc ini top step; apply: DWhileTotal=>//.
apply: ranking_of_partial inc ini top _=>n.
exact: derives_sound (step n).
Qed.
End CQRankingComplement.
