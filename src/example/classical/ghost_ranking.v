(* Fresh integer ghosts and the paper's C-WhileT rule. See HOARE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules assertion_algebra assertion_series primitive footprint locality assertion_locality invariant classical_ranking.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQGhostRanking.
Import CQAssertion CQPredicate CQRules ClassicalLanguage ClassicalFootprint CQAssertionLocality.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma writes_variables c k : k \in writes c -> variables c k.
Proof.
elim: c=>[| |u x e|u x p|u v x q M|u q phi|u q U|
    c IH d IHd|b c IH d IHd|b c IH] /=; rewrite ?in_nil //.
- by rewrite inE=>/eqP E; left; exact E.
- by rewrite inE=>/eqP E; left; exact E.
- by rewrite inE=>/eqP E; left; exact E.
- rewrite mem_cat=>/orP[H|H]; [left; exact: IH|right; exact: IHd].
- rewrite mem_cat=>/orP[H|H]; right; [left; exact: IH|right; exact: IHd].
- by move=>H; right; exact: IH.
Qed.

Theorem valid_fresh_integer_while (P : assertion) (p b : bool_expr)
    (r : expression int) (z : variable Integer) c X :
  (variables c `<=` X)%classic ->
  (expression_variables b `<=` X)%classic ->
  (expression_variables p `<=` X)%classic ->
  (expression_variables r `<=` X)%classic -> ~ X (key z) ->
  semantic_le P (mask (eval p) semantic_top) ->
  (forall s, eval p s -> 0 <= eval r s) ->
  CQHoare.valid true (mask (eval b) P) c P ->
  CQHoare.valid true
    (mask (fun s => eval b s && eval p s && (eval r s == (s.[z])%M)) semantic_top) c
    (mask (fun s => eval r s < (s.[z])%M) semantic_top) ->
  CQHoare.valid true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>Hc Hb Hp Hr Hz support nonneg inv dec.
apply: (@CQClassicalRanking.valid_integer_while P (eval p) (eval r) b c
  support nonneg inv)=>k.
pose g : bool_expr := EApp (EConst (fun v : int => v == k)) (EVar z).
have Hg : forall j, expression_variables g j -> j \notin writes c.
  move=>j; rewrite /g /EApp /EConst /EVar /=; move=>[[]|E].
  apply/negP=>Hj; apply: Hz; apply: Hc.
  by rewrite -E; exact: writes_variables Hj.
have Vg := CQInvariant.valid_invariant Hg dec.
pose pk := fun s => eval b s && eval p s && (eval r s == k) && ((s.[z])%M == k).
pose Qk : assertion := mask (fun s => eval r s < k) semantic_top.
have Vk : CQHoare.valid true (mask pk semantic_top) c Qk.
  apply: (@CQHoare.valid_consequence true _ _ _ _ c _ _ Vg).
  - move=>s; rewrite /mask /pk /g /eval /=.
    case E: (esem b s && esem p s && (esem r s == k) && (s.[z]%M == k));
      last exact: obsf_ge0.
    have /andP[/andP[/andP[bs ps] /eqP rk] /eqP zk] := E.
    by rewrite bs ps rk zk eqxx.
  - move=>s; rewrite /Qk /mask /g /eval /=.
    case Z: (s.[z]%M == k); last exact: obsf_ge0.
    by rewrite (eqP Z).
have Qlocal : assertion_local X Qk.
  move=>s t Hst; by rewrite /Qk /mask (eval_agree Hr Hst).
have Ve := @valid_exist true Integer z pk (\1 : 'FO(Hq)) c Qk X Hc Hz Qlocal Vk.
apply: (@CQHoare.valid_consequence true _ _ _ _ c _ (semantic_le_refl Qk) Ve).
move=>s; rewrite /mask.
case E: (eval b s && eval p s && (eval r s == k)); last exact: obsf_ge0.
have Hw : exists_update z pk s.
  apply/asboolP; exists k.
  have Hst := @agree_on_external X Integer z k s Hz.
  by rewrite /pk -(eval_agree Hb Hst) -(eval_agree Hp Hst)
    -(eval_agree Hr Hst) get_set_eq E eqxx.
by rewrite Hw.
Qed.

Theorem derives_fresh_integer_while (P : assertion) (p b : bool_expr)
    (r : expression int) (z : variable Integer) c X :
  (variables c `<=` X)%classic ->
  (expression_variables b `<=` X)%classic ->
  (expression_variables p `<=` X)%classic ->
  (expression_variables r `<=` X)%classic -> ~ X (key z) ->
  semantic_le P (mask (eval p) semantic_top) ->
  (forall s, eval p s -> 0 <= eval r s) ->
  derives true (mask (eval b) P) c P ->
  derives true
    (mask (fun s => eval b s && eval p s && (eval r s == (s.[z])%M)) semantic_top) c
    (mask (fun s => eval r s < (s.[z])%M) semantic_top) ->
  derives true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>Hc Hb Hp Hr Hz support nonneg /derives_sound inv /derives_sound dec.
apply: derives_complete; exact: valid_fresh_integer_while Hc Hb Hp Hr Hz support nonneg inv dec.
Qed.

End CQGhostRanking.
