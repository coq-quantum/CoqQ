(* Predicate-transformer locality and existential elimination. See HOARE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules assertion_algebra assertion_series primitive footprint locality.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQAssertionLocality.
Import CQAssertion CQPredicate CQRules ClassicalLanguage ClassicalFootprint.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition assertion_local (X : set identifier) (P : assertion) :=
  forall s t, agree_on X s t -> P s = P t.

Lemma agree_on_update X u (x : variable u) v s t :
  agree_on X s t -> agree_on X (s.[x <- v])%M (t.[x <- v])%M.
Proof.
move=>H w y Hy.
rewrite /cmset /cmget /cvtype /= /orapp.
case: eqP=>E; last exact: H Hy.
case: (cvname x == cvname y)=>//; exact: H Hy.
Qed.

Lemma agree_on_external X u (x : variable u) v s :
  ~ X (key x) -> agree_on X s (s.[x <- v])%M.
Proof.
move=>H w y Hy; apply: ClassicalLocality.update_unchanged.
rewrite inE; apply/negP=>/eqP E; apply: H; by rewrite -E.
Qed.

Lemma eval_agree A (e : expression A) X s t :
  (expression_variables e `<=` X)%classic ->
  agree_on X s t -> eval e s = eval e t.
Proof. move=>Hsub Hst; apply: eval_local=>u x Hx; exact: Hst (Hsub _ Hx). Qed.

Theorem pre_local total c X Q :
  (variables c `<=` X)%classic -> assertion_local X Q ->
  assertion_local X (pre total c Q).
Proof.
elim: c Q=>[| |u x e|u x p|u v x q M|u q phi|u q U|
    c IH d IHd|b c IH d IHd|b c IH] Q Hsub HQ s t Hst.
- by rewrite /pre /= xp_skip; exact: HQ.
- by case Etotal: total; rewrite /pre /= /xp ?Etotal ?wp_abort ?wlp_abort.
- have Ee : eval e s = eval e t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by right.
  apply/val_inj.
  change ((pre total (Assign x e) Q s : 'End(Hq)) = (pre total (Assign x e) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.assign_pre Ee.
  by rewrite (HQ _ _ (@agree_on_update X u x (eval e t) s t Hst)).
- have Ep : eval (probability_expression p) s = eval (probability_expression p) t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by right.
  apply/val_inj.
  change ((pre total (Random x p) Q s : 'End(Hq)) = (pre total (Random x p) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.random_pre.
  apply: eq_sum=>a; rewrite /probability_mass -/(eval _ s) -/(eval _ t) Ep.
  by rewrite (HQ _ _ (@agree_on_update X u x a s t Hst)).
- have EM : eval M s = eval M t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by right.
  apply/val_inj.
  change ((pre total (Measure x q M) Q s : 'End(Hq)) = (pre total (Measure x q M) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.measurement_pre.
  apply: eq_bigr=>a _; rewrite -/(eval M s) -/(eval M t) EM.
  by rewrite (HQ _ _ (@agree_on_update X (QType u) x a s t Hst)).
- have Ephi := eval_agree Hsub Hst.
  apply/val_inj.
  change ((pre total (Initialize q phi) Q s : 'End(Hq)) = (pre total (Initialize q phi) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.initial_pre.
  by rewrite -/(eval phi s) -/(eval phi t) Ephi (HQ _ _ Hst).
- have EU := eval_agree Hsub Hst.
  apply/val_inj.
  change ((pre total (Unitary q U) Q s : 'End(Hq)) = (pre total (Unitary q U) Q t : 'End(Hq))).
  rewrite /pre !CQPrimitive.unitary_pre.
  by rewrite -/(eval U s) -/(eval U t) EU (HQ _ _ Hst).
- rewrite !pre_sequence; apply: IH Hst.
  + move=>k Hk; apply: Hsub; by left.
  + apply: IHd HQ; move=>k Hk; apply: Hsub; by right.
- have Eb : eval b s = eval b t.
    apply: eval_agree Hst; move=>k Hk; apply: Hsub; by left.
  rewrite !pre_conditional /conditional -/(eval b s) -/(eval b t) Eb.
  case: (eval b t); [apply: (IH Q _ HQ s t Hst)|apply: (IHd Q _ HQ s t Hst)];
    move=>k Hk; apply: Hsub; right; [by left|by right].
- have Hb : (expression_variables b `<=` X)%classic.
    move=>k Hk; apply: Hsub; by left.
  have Hc : (variables c `<=` X)%classic.
    move=>k Hk; apply: Hsub; by right.
  have HU n : assertion_local X (pre total (unroll b c n) Q).
    elim: n=>[|n IHn] a d Had.
    + by case Etotal: total; rewrite /pre /= /xp ?Etotal ?wp_abort ?wlp_abort.
    + rewrite !pre_unrollS /conditional -/(eval b a) -/(eval b d)
        (eval_agree Hb Had).
      case: (eval b d); [exact: (IH _ Hc IHn a d Had)|exact: (HQ a d Had)].
  apply/val_inj.
  change ((pre total (While b c) Q s : 'End(Hq)) = (pre total (While b c) Q t : 'End(Hq))).
  case Etotal: total HU=>HU.
  + change ((wp_command (While b c) Q s : 'End(Hq)) = (wp_command (While b c) Q t : 'End(Hq))).
    have Cs := @wp_unroll_cvg b c Q s.
    have Ct := @wp_unroll_cvg b c Q t.
    have E : (fun n => (wp_command (unroll b c n) Q s : 'End(Hq))) =
        (fun n => (wp_command (unroll b c n) Q t : 'End(Hq))).
      apply/funext=>n; exact: (congr1 (fun f : 'FO(Hq) => (f : 'End(Hq))) (HU n s t Hst)).
    by rewrite -(cvg_lim (@norm_hausdorff _ _) Cs) E
      (cvg_lim (@norm_hausdorff _ _) Ct).
  + change ((wlp_command (While b c) Q s : 'End(Hq)) = (wlp_command (While b c) Q t : 'End(Hq))).
    have Cs := @wlp_unroll_cvg b c Q s.
    have Ct := @wlp_unroll_cvg b c Q t.
    have E : (fun n => (wlp_command (unroll b c n) Q s : 'End(Hq))) =
        (fun n => (wlp_command (unroll b c n) Q t : 'End(Hq))).
      apply/funext=>n; exact: (congr1 (fun f : 'FO(Hq) => (f : 'End(Hq))) (HU n s t Hst)).
    by rewrite -(cvg_lim (@norm_hausdorff _ _) Cs) E
      (cvg_lim (@norm_hausdorff _ _) Ct).
Qed.


Definition exists_update u (x : variable u) (p : pred cmem) : pred cmem :=
  fun s => asbool (exists v, p (s.[x <- v])%M).

Theorem valid_exist total u (x : variable u) (p : pred cmem)
    (M : 'FO(Hq)) c Q X :
  (variables c `<=` X)%classic -> ~ X (key x) -> assertion_local X Q ->
  CQHoare.valid total (mask p (fun _ => M)) c Q ->
  CQHoare.valid total (mask (exists_update x p) (fun _ => M)) c Q.
Proof.
move=>Hc Hx HQ /(proj1 (valid_iff _ _ _ _)) V.
apply/(proj2 (valid_iff _ _ _ _))=>s.
rewrite /mask; case E: (exists_update x p s); last exact: obsf_ge0.
have /asboolP[v Hv] : asbool (exists v, p (s.[x <- v])%M) by exact E.
have Hpre := @pre_local total c X Q Hc HQ s (s.[x <- v])%M
  (@agree_on_external X u x v s Hx).
have := V (s.[x <- v])%M; by rewrite /mask Hv -Hpre.
Qed.

Theorem derives_exist total u (x : variable u) (p : pred cmem)
    (M : 'FO(Hq)) c Q X :
  (variables c `<=` X)%classic -> ~ X (key x) -> assertion_local X Q ->
  derives total (mask p (fun _ => M)) c Q ->
  derives total (mask (exists_update x p) (fun _ => M)) c Q.
Proof.
move=>Hc Hx HQ /derives_sound V; apply: derives_complete.
exact: valid_exist Hc Hx HQ V.
Qed.

End CQAssertionLocality.
