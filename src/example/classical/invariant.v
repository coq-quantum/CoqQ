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
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules assertion_algebra assertion_series locality operational footprint.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQInvariant.
Import CQAssertion CQPredicate CQRules ClassicalLanguage ClassicalLocality ClassicalOperational.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma denote_expression_zero A (e : expression A) c s (rho : 'End(Hq)) t :
  (forall k, expression_variables e k -> k \notin writes c) ->
  0%:VF ⊑ rho -> eval e s <> eval e t -> denote c s t rho = 0.
Proof.
move=>fresh pos diff; rewrite -(operational_denotational c s t pos) /opsum sum_summableE.
  by apply: norm_bounded_cvg; apply: operational_summable.
have Z rt : opfun c s rho rt t = 0.
  rewrite /opfun; case E: (eval_route rt c (s,rho))=>[[u q]|] /=.
  - rewrite /sunit_def; case: eqP=>[ut|//].
    subst u; exfalso; apply: diff.
    exact: terminates_preserves_expression fresh (eval_route_sound E).
  - by [].
under eq_sum do rewrite Z.
exact: summable_sum_cst0.
Qed.

Lemma wp_guard_agree c (b : bool_expr) (P Q : assertion) s :
  (forall k, expression_variables b k -> k \notin writes c) ->
  (forall t, eval b t = eval b s -> P t = Q t) ->
  wp (denote c) P s = wp (denote c) Q s.
Proof.
move=>fresh agree; apply: effect_eq=>rho; rewrite !wp_pairing.
apply: eq_sum=>t.
case: (boolP (eval b t == eval b s))=>[/eqP E|/eqP ne].
- by rewrite (agree t E).
- have Z : denote c s t rho = 0.
    apply (@denote_expression_zero bool b c s rho t fresh (denf_ge0 rho)).
    by move=>E; apply: ne; symmetry.
  by rewrite Z !comp_lfun0r !linear0.
Qed.

Lemma pre_mask_true total c (b : bool_expr) (P : assertion) s :
  (forall k, expression_variables b k -> k \notin writes c) ->
  eval b s = true -> pre total c (mask (eval b) P) s = pre total c P s.
Proof.
move=>fresh bs; case: total.
- apply (@wp_guard_agree c b (mask (eval b) P) P s fresh).
  by move=>t bt; rewrite /mask bt bs.
- have E : wp (denote c) (complement (mask (eval b) P)) s =
      wp (denote c) (complement P) s.
    apply (@wp_guard_agree c b (complement (mask (eval b) P)) (complement P) s fresh)=>t bt.
    by rewrite /complement /mask bt bs.
  apply/val_inj.
  change (\1 - (wp (denote c) (complement (mask (eval b) P)) s : 'End(Hq)) =
    \1 - (wp (denote c) (complement P) s : 'End(Hq))).
  by rewrite E.
Qed.

Lemma valid_invariant total P c Q (b : bool_expr) :
  (forall k, expression_variables b k -> k \notin writes c) ->
  CQHoare.valid total P c Q ->
  CQHoare.valid total (mask (eval b) P) c (mask (eval b) Q).
Proof.
move=>fresh /(proj1 (valid_iff _ _ _ _)) V.
apply/(proj2 (valid_iff _ _ _ _))=>s.
rewrite /mask; case bs: (eval b s); last exact: obsf_ge0.
by rewrite (@pre_mask_true total c b Q s fresh bs); apply: V.
Qed.

Lemma derives_invariant total P c Q (b : bool_expr) :
  (forall k, expression_variables b k -> k \notin writes c) ->
  derives total P c Q -> derives total (mask (eval b) P) c (mask (eval b) Q).
Proof.
move=>fresh /derives_sound V; apply: derives_complete.
exact: valid_invariant fresh V.
Qed.

End CQInvariant.
