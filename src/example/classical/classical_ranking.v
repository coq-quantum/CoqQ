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
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules assertion_algebra assertion_series.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQClassicalRanking.
Import CQAssertion CQPredicate CQRules ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma wp_certain_mask (K : semType cmem cmem Hq Hq) (g : pred cmem)
    (Q : assertion) s :
  (\1 : 'End(Hq)) <= wp K (mask g semantic_top) s ->
  wp K (mask g Q) s = wp K Q s.
Proof.
move=>Hg.
have Eg : (wp K (mask g semantic_top) s : 'End(Hq)) = \1.
  by apply/eqP; rewrite eq_le Hg obsf_le1.
have Ed : (wp K (mask (predC g) semantic_top) s : 'End(Hq)) =
    (wp K semantic_top s : 'End(Hq)) - \1.
  rewrite -Eg; apply: wp_difference=>t.
  by rewrite /mask /predC /=; case: (g t); rewrite /= ?subrr ?subr0.
have Zg : (wp K (mask (predC g) semantic_top) s : 'End(Hq)) = 0.
  apply/eqP; rewrite eq_le obsf_ge0 andbT Ed subv_le0; exact: obsf_le1.
have Zq : (wp K (mask (predC g) Q) s : 'End(Hq)) = 0.
  have Hmono : semantic_le (mask (predC g) Q) (mask (predC g) semantic_top).
    apply: CQAssertionAlgebra.mask_le; exact: semantic_le_top.
  have Le := wp_mono K Hmono s.
  rewrite Zg in Le.
  by apply/eqP; rewrite eq_le Le obsf_ge0.
apply/val_inj.
change ((wp K (mask g Q) s : 'End(Hq)) = (wp K Q s : 'End(Hq))).
have E : (wp K (mask g Q) s : 'End(Hq)) =
    (wp K Q s : 'End(Hq)) - (wp K (mask (predC g) Q) s : 'End(Hq)).
  apply: wp_difference=>t.
  by rewrite /mask /predC /=; case: (g t); rewrite /= ?subrr ?subr0.
by rewrite E Zq subr0.
Qed.

Theorem valid_classical_while (P : assertion) (p : pred cmem)
    (rank : cmem -> nat) b c :
  semantic_le P (mask p semantic_top) ->
  CQHoare.valid true (mask (eval b) P) c P ->
  (forall k, CQHoare.valid true
    (mask (fun s => eval b s && p s && (rank s == k)) semantic_top) c
    (mask (fun s => ~~ p s || (rank s < k)%N) semantic_top)) ->
  CQHoare.valid true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>support /(proj1 (valid_total_iff _ _ _)) inv decrease.
pose Q := mask (predC (eval b)) P.
have bound k : forall s, p s -> (rank s < k)%N ->
    (P s : 'End(Hq)) <= pre true (While b c) Q s.
  elim: k=>[|k IH] s ps Hrank; first by rewrite ltn0 in Hrank.
  rewrite pre_while_unfold /conditional.
  case bs: (esem b s); last by rewrite /Q /mask /predC /eval /= bs.
  change ((P s : 'End(Hq)) <= wp (denote c) (pre true (While b c) Q) s).
  pose g := fun t => ~~ p t || (rank t < rank s)%N.
  have Hcertain : (\1 : 'End(Hq)) <= wp (denote c) (mask g semantic_top) s.
    have H := ((proj1 (valid_total_iff _ _ _)) (decrease (rank s))) s.
    by rewrite /mask /eval bs ps eqxx /= in H.
  have Emask := wp_certain_mask P Hcertain.
  apply: (le_trans (y := (wp (denote c) P s : 'End(Hq)))).
  - by move: (inv s); rewrite /mask /eval bs.
  - have Hmono : semantic_le (mask g P) (pre true (While b c) Q).
      move=>t.
      rewrite /mask; case gt: (g t); last exact: obsf_ge0.
      case pt: (p t).
      + have Hlower : (rank t < rank s)%N by move: gt; rewrite /g pt.
        apply: (IH t pt); exact: ltn_leq_trans Hlower Hrank.
      + apply: (le_trans (y := (0 : 'End(Hq)))); last exact: obsf_ge0.
        by move: (support t); rewrite /mask pt.
    have Le := wp_mono (denote c) Hmono s.
    by rewrite Emask in Le.
apply/(proj2 (valid_iff _ _ _ _))=>s; case ps: (p s).
- exact: (bound (rank s).+1 s ps (ltnSn (rank s))).
- apply: (le_trans (y := (0 : 'End(Hq)))); last exact: obsf_ge0.
  by move: (support s); rewrite /mask ps.
Qed.

Theorem valid_integer_while (P : assertion) (p : pred cmem)
    (rank : cmem -> int) b c :
  semantic_le P (mask p semantic_top) ->
  (forall s, p s -> 0 <= rank s) ->
  CQHoare.valid true (mask (eval b) P) c P ->
  (forall k : int, CQHoare.valid true
    (mask (fun s => eval b s && p s && (rank s == k)) semantic_top) c
    (mask (fun s => rank s < k) semantic_top)) ->
  CQHoare.valid true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>support nonneg inv decrease.
apply: (@valid_classical_while P p (fun s => absz (rank s)) b c support inv)=>k.
apply: (@CQHoare.valid_consequence true
  (mask (fun s => eval b s && p s && (rank s == Posz k)) semantic_top)
  (mask (fun s => rank s < Posz k) semantic_top) _ _ c).
- move=>s; rewrite /mask.
  case E: (eval b s && p s && (absz (rank s) == k)); last exact: obsf_ge0.
  have /andP[/andP[bs ps] /eqP rk] := E.
  have Rk : rank s = Posz k by rewrite -(gez0_abs (nonneg s ps)) rk.
  by rewrite bs ps Rk eqxx.
- move=>s; rewrite /mask; case E: (rank s < Posz k); last exact: obsf_ge0.
  case ps: (p s)=>/=; last by [].
  have L : (absz (rank s) < k)%N.
    by rewrite -ltz_nat (gez0_abs (nonneg s ps)).
  by rewrite L.
- exact: decrease.
Qed.

Theorem derives_integer_while (P : assertion) (p : pred cmem)
    (rank : cmem -> int) b c :
  semantic_le P (mask p semantic_top) ->
  (forall s, p s -> 0 <= rank s) ->
  derives true (mask (eval b) P) c P ->
  (forall k : int, derives true
    (mask (fun s => eval b s && p s && (rank s == k)) semantic_top) c
    (mask (fun s => rank s < k) semantic_top)) ->
  derives true P (While b c) (mask (predC (eval b)) P).
Proof.
move=>support nonneg /derives_sound inv decrease; apply: derives_complete.
apply: valid_integer_while support nonneg inv _ =>k.
exact: derives_sound (decrease k).
Qed.

End CQClassicalRanking.
