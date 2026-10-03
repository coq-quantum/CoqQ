(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)
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
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQRules.
Import CQAssertion CQPredicate ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Implicit Types (P Q R : assertion).

Definition wp_command c Q := wp (denote c) Q.
Definition wlp_command c Q := wlp (denote c) Q.
Definition pre total c Q := xp total (denote c) Q.

Lemma valid_total_iff P c Q :
  CQHoare.valid true P c Q <-> semantic_le P (wp_command c Q).
Proof.
split=>V.
- apply/(proj2 (CQExpectation.semantic_le_iff_expect _ _))=>rho.
  by rewrite /wp_command expect_wp; apply: V.
- move=>rho; rewrite -expect_wp.
  by apply: expect_mono; apply: V.
Qed.

Lemma valid_partial_iff P c Q :
  CQHoare.valid false P c Q <-> semantic_le P (wlp_command c Q).
Proof.
split=>V.
- apply/(proj2 (CQExpectation.semantic_le_iff_expect _ _))=>rho.
  rewrite /wlp_command expect_wlp.
  exact: (proj1 (CQHoare.valid_partial_loss P c Q) V rho).
- apply/(proj2 (CQHoare.valid_partial_loss P c Q))=>rho.
  rewrite -expect_wlp; apply: expect_mono; exact: V.
Qed.

Lemma valid_iff total P c Q :
  CQHoare.valid total P c Q <-> semantic_le P (pre total c Q).
Proof. by case: total; [apply: valid_total_iff | apply: valid_partial_iff]. Qed.

Lemma pre_valid total c Q : CQHoare.valid total (pre total c Q) c Q.
Proof. apply/(proj2 (valid_iff _ _ _ _)); exact: semantic_le_refl. Qed.

Lemma pre_mono total c P Q : semantic_le P Q ->
  semantic_le (pre total c P) (pre total c Q).
Proof. exact: xp_mono. Qed.

Lemma pre_sequence total c1 c2 Q :
  pre total (Sequence c1 c2) Q = pre total c1 (pre total c2 Q).
Proof. exact: xp_sequence. Qed.

Lemma pre_conditional total b c1 c0 Q :
  pre total (Conditional b c1 c0) Q =
  conditional (esem b) (pre total c1 Q) (pre total c0 Q).
Proof. exact: xp_conditional. Qed.

Lemma pre_while_unfold total b c Q :
  pre total (While b c) Q =
  conditional (esem b) (pre total c (pre total (While b c) Q)) Q.
Proof.
rewrite /pre {1}denote_while_unfold /= xp_conditional xp_sequence xp_skip.
by [].
Qed.

Lemma valid_conditional total P Q b c1 c0 :
  CQHoare.valid total (mask (esem b) P) c1 Q ->
  CQHoare.valid total (mask (predC (esem b)) P) c0 Q ->
  CQHoare.valid total P (Conditional b c1 c0) Q.
Proof.
move=>/(proj1 (valid_iff _ _ _ _)) V1 /(proj1 (valid_iff _ _ _ _)) V0.
apply/(proj2 (valid_iff _ _ _ _)); rewrite pre_conditional=>s.
move: (V1 s) (V0 s); rewrite /mask /conditional /=.
by case: (esem b s).
Qed.


Lemma wp_unroll_chain b c Q :
  semantic_chain (fun n => wp_command (unroll b c n) Q).
Proof.
move=>n; apply: wp_kernel_mono=>i j; rewrite !denote_unroll.
have H := @while_sem_iter_homo Hq b (denote c) i n n.+1 (leqnSn n).
by move: H=>/levdP/(_ j).
Qed.

Lemma wp_unroll_bound b c Q n :
  semantic_le (wp_command (unroll b c n) Q) (wp_command (While b c) Q).
Proof.
apply: wp_kernel_mono=>i j.
by move: (denote_while_unroll_le b c n i)=>/levdP/(_ j).
Qed.

Lemma wp_unroll_sup b c Q :
  semantic_sup (fun n => wp_command (unroll b c n) Q) = wp_command (While b c) Q.
Proof.
have E rho : expect (semantic_sup (fun n => wp_command (unroll b c n) Q)) rho =
    expect (wp_command (While b c) Q) rho.
  have C1 := @CQExpectationLimits.expect_semantic_sup cmem Hq
    (fun n => wp_command (unroll b c n) Q) rho (wp_unroll_chain b c Q).
  have C2 : expect (wp_command (unroll b c n) Q) rho @[n --> \oo] -->
      expect (wp_command (While b c) Q) rho.
    under eq_cvg do rewrite /wp_command expect_wp.
    rewrite /wp_command expect_wp.
    exact (@CQKernelLimits.unroll_expect_cvg Q b c rho).
  by rewrite -(cvg_lim (@norm_hausdorff _ _) C1) (cvg_lim (@norm_hausdorff _ _) C2).
apply/funext=>s; apply: effect_eq=>rho.
by move: (E (CQState.point s rho)); rewrite !CQExpectation.expect_point.
Qed.

Lemma wp_unroll_cvg b c Q s :
  (wp_command (unroll b c n) Q s : 'End(Hq)) @[n --> \oo] -->
    (wp_command (While b c) Q s : 'End(Hq)).
Proof.
rewrite -wp_unroll_sup.
exact: (@CQExpectationLimits.semantic_sup_cvg cmem Hq
  (fun n => wp_command (unroll b c n) Q) (wp_unroll_chain b c Q) s).
Qed.

Lemma wlp_unroll_cvg b c Q s :
  (wlp_command (unroll b c n) Q s : 'End(Hq)) @[n --> \oo] -->
    (wlp_command (While b c) Q s : 'End(Hq)).
Proof.
change ((fun n => \1 - (wp_command (unroll b c n) (complement Q) s : 'End(Hq)))
  @ \oo --> (\1 - (wp_command (While b c) (complement Q) s : 'End(Hq))))%classic.
apply: cvgB; first exact: cvg_cst.
exact: wp_unroll_cvg.
Qed.

Lemma pre_unrollS total b c Q n :
  pre total (unroll b c n.+1) Q =
  conditional (esem b) (pre total c (pre total (unroll b c n) Q)) Q.
Proof. by rewrite /= pre_conditional pre_sequence /pre /= xp_skip. Qed.

Lemma valid_while_partial P b c :
  CQHoare.valid false (mask (esem b) P) c P ->
  CQHoare.valid false P (While b c) (mask (predC (esem b)) P).
Proof.
move=>/(proj1 (valid_partial_iff _ _ _)) inv.
have bound n : semantic_le P (wlp_command (unroll b c n) (mask (predC (esem b)) P)).
  elim: n=>[|n IH].
  - move=>s; change ((P s : 'End(Hq)) ⊑ wlp abort_sem (mask (predC (esem b)) P) s).
    by rewrite wlp_abort; apply: obsf_le1.
  - change (semantic_le P (pre false (unroll b c n.+1) (mask (predC (esem b)) P))).
    rewrite pre_unrollS=>s.
    case E: (esem b s); rewrite /conditional E.
    + apply: (le_trans (y := (wlp_command c P s : 'End(Hq)))).
      * by move: (inv s); rewrite /mask E.
      * exact: wlp_mono IH s.
    + by rewrite /mask /= E.
apply/(proj2 (valid_partial_iff _ _ _))=>s.
have C := @wlp_unroll_cvg b c (mask (predC (esem b)) P) s.
have H := limn_gev (cvgP _ C) (fun n => bound n s).
by rewrite (cvg_lim (@norm_hausdorff _ _) C) in H.
Qed.

(* Definition 5.2: a decreasing sequence of effects, tending to zero,
   bounds the invariant and decreases under one guarded body execution. *)
Record ranking P b c := Ranking {
  ranking_assertion : nat -> assertion;
  ranking_decreases : forall n, semantic_le (ranking_assertion n.+1) (ranking_assertion n);
  ranking_initial : semantic_le P (ranking_assertion 0%N);
  ranking_zero : forall s,
    ((fun n => (ranking_assertion n s : 'End(Hq))) @ \oo --> 0)%classic;
  ranking_step : forall n,
    semantic_le (mask (esem b) (wp_command c (ranking_assertion n)))
      (ranking_assertion n.+1)
}.


Lemma wp_unrollS b c Q n :
  wp_command (unroll b c n.+1) Q =
  conditional (esem b) (wp_command c (wp_command (unroll b c n) Q)) Q.
Proof. exact: (pre_unrollS true b c Q n). Qed.

Lemma valid_while_total P b c :
  CQHoare.valid true (mask (esem b) P) c P -> ranking P b c ->
  CQHoare.valid true P (While b c) (mask (predC (esem b)) P).
Proof.
move=>/(proj1 (valid_total_iff _ _ _)) inv [r dec ini zero step].
have bound n : forall s, (P s : 'End(Hq)) ⊑
    (r n s : 'End(Hq)) + (wp_command (unroll b c n) (mask (predC (esem b)) P) s : 'End(Hq)).
  elim: n=>[|n IH] s.
  - change ((P s : 'End(Hq)) ⊑ (r 0%N s : 'End(Hq)) +
      (wp abort_sem (mask (predC (esem b)) P) s : 'End(Hq))).
    by rewrite wp_abort addr0; apply: ini.
  - rewrite wp_unrollS /conditional.
    case E: (esem b s).
    + apply: (le_trans (y := (wp_command c P s : 'End(Hq)))).
      * by move: (inv s); rewrite /mask E.
      * apply: (le_trans (wp_add_upper (denote c) IH s)).
        apply: levD; last by [].
        by move: (step n s); rewrite /mask E.
    + rewrite /mask /= E.
      by rewrite levDr; exact: obsf_ge0.
apply/(proj2 (valid_total_iff _ _ _))=>s.
have C : ((fun n => (r n s : 'End(Hq)) +
    (wp_command (unroll b c n) (mask (predC (esem b)) P) s : 'End(Hq))) @ \oo -->
    0 + (wp_command (While b c) (mask (predC (esem b)) P) s : 'End(Hq))).
  apply: cvgD; [exact: zero | exact: wp_unroll_cvg].
rewrite add0r in C.
have L := limn_gev (cvgP _ C) (fun n => bound n s).
by rewrite (cvg_lim (@norm_hausdorff _ _) C) in L.
Qed.

Lemma tail_effect b c n s :
  ((wp_command (While b c) semantic_top s : 'End(Hq)) -
   (wp_command (unroll b c n) semantic_top s : 'End(Hq))) \is obslf.
Proof.
rewrite obslfE; apply/andP; split.
- rewrite subv_ge0; exact: wp_unroll_bound.
- apply: (le_trans (y := (wp_command (While b c) semantic_top s : 'End(Hq))));
    last exact: obsf_le1.
  by rewrite levBlDr levDl; exact: obsf_ge0.
Qed.

Definition tail b c n s : 'FO(Hq) := ObsLf_Build (tail_effect b c n s).

Lemma tailE b c n s : (tail b c n s : 'End(Hq)) =
  (wp_command (While b c) semantic_top s : 'End(Hq)) -
  (wp_command (unroll b c n) semantic_top s : 'End(Hq)).
Proof. by []. Qed.

Lemma loop_ranking b c Q : ranking (wp_command (While b c) Q) b c.
Proof.
apply: (Ranking (ranking_assertion := tail b c)).
- move=>n s; rewrite !tailE levD2l levN2.
  exact: (@wp_unroll_chain b c semantic_top n s).
- move=>s; rewrite tailE.
  change ((wp (denote (While b c)) Q s : 'End(Hq)) ⊑
    (wp (denote (While b c)) semantic_top s : 'End(Hq)) -
    (wp abort_sem semantic_top s : 'End(Hq))).
  rewrite wp_abort subr0.
  apply: wp_mono=>i; exact: obsf_le1.
- move=>s.
  change ((fun n => (wp_command (While b c) semantic_top s : 'End(Hq)) -
    (wp_command (unroll b c n) semantic_top s : 'End(Hq))) @ \oo --> 0)%classic.
  have C : ((fun n => (wp_command (While b c) semantic_top s : 'End(Hq)) -
      (wp_command (unroll b c n) semantic_top s : 'End(Hq))) @ \oo -->
      (wp_command (While b c) semantic_top s : 'End(Hq)) -
      (wp_command (While b c) semantic_top s : 'End(Hq))).
    apply: cvgB; [exact: cvg_cst | exact: wp_unroll_cvg].
  by rewrite subrr in C.
- move=>n s; rewrite /mask.
  case E: (esem b s); last exact: obsf_ge0.
  rewrite /wp_command (wp_difference (denote c) (fun j => tailE b c n j)) tailE.
  have W := congr1 (fun A : assertion => (A s : 'End(Hq)))
    (pre_while_unfold true b c semantic_top).
  have A := congr1 (fun A : assertion => (A s : 'End(Hq)))
    (wp_unrollS b c semantic_top n).
  rewrite /conditional E in W A.
  by rewrite W A.
Qed.

Inductive derives : bool -> assertion -> command -> assertion -> Prop :=
| DSkip total P : derives total P Skip P
| DAssign total t (x : variable t) e Q :
    derives total (pre total (Assign x e) Q) (Assign x e) Q
| DRandom total t (x : variable t) p Q :
    derives total (pre total (Random x p) Q) (Random x p) Q
| DInitialize total u (q : wf_qreg u) phi Q :
    derives total (pre total (Initialize q phi) Q) (Initialize q phi) Q
| DUnitary total u (q : wf_qreg u) U Q :
    derives total (pre total (Unitary q U) Q) (Unitary q U) Q
| DMeasure total t u (x : variable (QType t)) (q : wf_qreg u) M Q :
    derives total (pre total (Measure x q M) Q) (Measure x q M) Q
| DAbortPartial : derives false semantic_top Abort semantic_bottom
| DAbortTotal : derives true semantic_bottom Abort semantic_bottom
| DSequence total P Q R c1 c2 :
    derives total P c1 Q -> derives total Q c2 R ->
    derives total P (Sequence c1 c2) R
| DConditional total P Q b c1 c0 :
    derives total (mask (esem b) P) c1 Q ->
    derives total (mask (predC (esem b)) P) c0 Q ->
    derives total P (Conditional b c1 c0) Q
| DWhilePartial P b c :
    derives false (mask (esem b) P) c P ->
    derives false P (While b c) (mask (predC (esem b)) P)
| DWhileTotal P b c :
    derives true (mask (esem b) P) c P -> ranking P b c ->
    derives true P (While b c) (mask (predC (esem b)) P)
| DConsequence total P Q P' Q' c :
    semantic_le P' P -> semantic_le Q Q' -> derives total P c Q ->
    derives total P' c Q'.


Theorem derives_sound total P c Q : derives total P c Q -> CQHoare.valid total P c Q.
Proof.
move=>D; induction D.
- exact: CQHoare.valid_skip.
- exact: pre_valid.
- exact: pre_valid.
- exact: pre_valid.
- exact: pre_valid.
- exact: pre_valid.
- exact: CQHoare.valid_abort_partial.
- by apply: CQHoare.valid_abort_total.
- exact: CQHoare.valid_sequence IHD1 IHD2.
- exact: valid_conditional IHD1 IHD2.
- exact: valid_while_partial IHD.
- apply: valid_while_total; assumption.
- exact: (@CQHoare.valid_consequence total P Q P' Q' c H H0 IHD).
Qed.

Lemma loop_invariant_pre total b c Q :
  semantic_le (mask (esem b) (pre total (While b c) Q))
    (pre total c (pre total (While b c) Q)).
Proof.
move=>s; rewrite /mask; case E: (esem b s); last exact: obsf_ge0.
have W := congr1 (fun A : assertion => (A s : 'End(Hq)))
  (pre_while_unfold total b c Q).
by move: W; rewrite /conditional E=>->.
Qed.

Lemma loop_invariant_post total b c Q :
  semantic_le (mask (predC (esem b)) (pre total (While b c) Q)) Q.
Proof.
move=>s; rewrite /mask /=; case E: (esem b s); first exact: obsf_ge0.
have W := congr1 (fun A : assertion => (A s : 'End(Hq)))
  (pre_while_unfold total b c Q).
by move: W; rewrite /conditional E=>->.
Qed.

Theorem derives_pre total c : forall Q, derives total (pre total c Q) c Q.
Proof.
elim: c=>[| |t x e|t x p|t u x q M|u q phi|u q U|
  c1 IH1 c2 IH2|b c1 IH1 c0 IH0|b c IH] Q.
- rewrite /pre /= xp_skip; exact: DSkip.
- case E: total.
  + change (derives true (wp abort_sem Q) Abort Q).
    rewrite wp_abort; apply: (@DConsequence true semantic_bottom semantic_bottom
      semantic_bottom Q Abort); [exact: semantic_le_refl | exact: semantic_bottom_le | exact: DAbortTotal].
  + change (derives false (wlp abort_sem Q) Abort Q).
    rewrite wlp_abort; apply: (@DConsequence false semantic_top semantic_bottom
      semantic_top Q Abort); [exact: semantic_le_refl | exact: semantic_bottom_le | exact: DAbortPartial].
- exact: DAssign.
- exact: DRandom.
- exact: DMeasure.
- exact: DInitialize.
- exact: DUnitary.
- rewrite pre_sequence; apply: DSequence; [exact: IH1 | exact: IH2].
- apply: DConditional.
  + apply: (@DConsequence total (pre total c1 Q) Q
      (mask (esem b) (pre total (Conditional b c1 c0) Q)) Q c1).
    * rewrite pre_conditional=>s; rewrite /mask /conditional.
      by case: (esem b s)=>//; apply: obsf_ge0.
    * exact: semantic_le_refl.
    * exact: IH1.
  + apply: (@DConsequence total (pre total c0 Q) Q
      (mask (predC (esem b)) (pre total (Conditional b c1 c0) Q)) Q c0).
    * rewrite pre_conditional=>s; rewrite /mask /conditional /=.
      by case: (esem b s)=>//; apply: obsf_ge0.
    * exact: semantic_le_refl.
    * exact: IH0.
- apply: (@DConsequence total (pre total (While b c) Q)
    (mask (predC (esem b)) (pre total (While b c) Q))
    (pre total (While b c) Q) Q (While b c)).
  + exact: semantic_le_refl.
  + exact: loop_invariant_post.
  + have body : derives total (mask (esem b) (pre total (While b c) Q))
        c (pre total (While b c) Q).
      apply: (@DConsequence total (pre total c (pre total (While b c) Q))
        (pre total (While b c) Q) (mask (esem b) (pre total (While b c) Q))
        (pre total (While b c) Q) c).
      * exact: loop_invariant_pre.
      * exact: semantic_le_refl.
      * exact: IH.
    case E: total in body *.
    * apply: DWhileTotal; first exact: body.
      exact: loop_ranking.
    * exact: DWhilePartial body.
Qed.

Theorem derives_complete total P c Q :
  CQHoare.valid total P c Q -> derives total P c Q.
Proof.
move=>/(proj1 (valid_iff _ _ _ _)) bound.
apply: (@DConsequence total (pre total c Q) Q P Q c).
- exact: bound.
- exact: semantic_le_refl.
- exact: derives_pre.
Qed.

Theorem sound_complete total P c Q :
  derives total P c Q <-> CQHoare.valid total P c Q.
Proof. split; [exact: derives_sound | exact: derives_complete]. Qed.

End CQRules.
