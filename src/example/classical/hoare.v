(* Classical: hoare. See README.md and PROOF_NOTES.md. *)
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
From quantum.example.classical Require Import language state assertion semantics.
Module CQHoare.
Local Open Scope classical_set_scope.
(* Core Hoare calculus, loop rankings, soundness, and relative completeness. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion ClassicalLanguage.

Include CQKernelExpectation.

Local Notation Hq := 'H[msys]_finset.setT.

Definition run (c : command) (rho : @CQState.state cmem Hq) :=
  CQKernel.apply (denote c) rho.

Lemma run_skip rho : run Skip rho = rho.
Proof. exact: CQKernel.apply_skip. Qed.

Lemma run_abort rho : run Abort rho = CQState.bottom.
Proof. exact: CQKernel.apply_abort. Qed.

Lemma run_sequence c1 c2 rho :
  run (Sequence c1 c2) rho = run c2 (run c1 rho).
Proof. exact: CQKernel.apply_sequence. Qed.

Lemma run_operational c rho m :
  run c rho m = sum (fun i => ClassicalOperational.opsum c i (rho i) m).
Proof.
rewrite /run CQKernel.applyE; apply: eq_sum=>i; symmetry.
apply: ClassicalOperational.operational_denotational; exact: vdistr_ge0.
Qed.

Lemma expect_bottom (P : cmem -> 'FO(Hq)) : expect P CQState.bottom = 0.
Proof.
rewrite /expect.
have -> : expect_term P CQState.bottom = (fun _ : cmem => (0 : hermitian.C)).
  by apply/funext=>s; rewrite /expect_term CQState.bottomE comp_lfun0r linear0.
apply: summable_sum_cst0.
Qed.

Section Logic.
Local Notation assertion := (@semantic_assertion cmem Hq).
Implicit Type (P Q R : assertion).

Definition valid (total : bool) P (c : command) Q :=
  forall rho : @CQState.state cmem Hq,
  if total then expect P rho <= expect Q (run c rho)
  else expect (complement Q) (run c rho) <= expect (complement P) rho.

Lemma valid_partial_loss P c Q : valid false P c Q <->
  forall rho, expect P rho <= expect Q (run c rho) +
    CQState.mass rho - CQState.mass (run c rho).
Proof.
have algebra (a0 b0 c0 d0 : hermitian.C) :
    (a0 - b0 <= c0 - d0) = (d0 <= b0 + c0 - a0).
  by rewrite lerBrDl addrA lerBlDr lerBrDr [c0 + b0]addrC.
rewrite /valid; split=>V rho; move: (V rho);
  by rewrite !expect_complement !CQState.mass_trace algebra.
Qed.

Lemma valid_skip total P : valid total P Skip P.
Proof. by move=>rho; rewrite run_skip; case: total. Qed.

Lemma valid_total_partial P c Q : valid true P c Q -> valid false P c Q.
Proof.
move=>V; apply/valid_partial_loss=>rho.
apply: (le_trans (V rho)).
rewrite -addrA lerDl subr_ge0; exact: CQKernel.apply_mass.
Qed.

Lemma valid_from_total total P c Q : valid true P c Q -> valid total P c Q.
Proof. by case: total=>//; apply: valid_total_partial. Qed.

Lemma valid_assign_total t (x : variable t) (e : expression (value t)) P Q :
  (forall s, P s = Q (s.[x <- eval e s])%M) ->
  valid true P (Assign x e) Q.
Proof.
move=>PQ rho.
change (expect P rho <=
  expect Q (CQKernel.apply (assign_sem x (translate_expr e)) rho)).
rewrite /assign_sem expect_sunit.
under [in X in _ <= X]eq_sum do rewrite soE.
change (expect P rho <=
  sum (fun s => \Tr (Q (s.[x <- eval e s])%M \o rho s))).
suff -> : expect P rho =
    sum (fun s => \Tr (Q (s.[x <- eval e s])%M \o rho s)) by [].
by rewrite /expect; apply: eq_sum=>s; rewrite /expect_term PQ.
Qed.

Lemma valid_assign total t (x : variable t) (e : expression (value t)) P Q :
  (forall s, P s = Q (s.[x <- eval e s])%M) ->
  valid total P (Assign x e) Q.
Proof. by move=>PQ; apply: valid_from_total; apply: valid_assign_total. Qed.

Lemma valid_abort_partial P Q : valid false P Abort Q.
Proof. by move=>rho; rewrite run_abort expect_bottom expect_ge0. Qed.

Lemma valid_abort_total P Q :
  (forall s, P s = (0%:VF : 'FO(Hq))) -> valid true P Abort Q.
Proof.
move=>P0 rho; rewrite run_abort expect_bottom.
have -> : (P : cmem -> 'FO(Hq)) = (fun _ => (0%:VF : 'FO(Hq))).
  by apply/funext.
by rewrite expect_zero.
Qed.

Lemma valid_sequence total P Q R c1 c2 :
  valid total P c1 Q -> valid total Q c2 R ->
  valid total P (Sequence c1 c2) R.
Proof.
move=>V1 V2 rho; rewrite run_sequence; case: total V1 V2=>V1 V2.
  exact: (le_trans (V1 rho) (V2 (run c1 rho))).
exact: (le_trans (V2 (run c1 rho)) (V1 rho)).
Qed.

Lemma valid_consequence total P Q P' Q' c :
  semantic_le P' P -> semantic_le Q Q' ->
  valid total P c Q -> valid total P' c Q'.
Proof.
move=>PP QQ V rho; case: total V=>V.
  apply: (le_trans (expect_mono rho PP)).
  apply: (le_trans (V rho)); exact: expect_mono QQ.
apply: (le_trans (y := expect (complement Q) (run c rho))).
  apply: expect_mono=>s; rewrite /complement /= -cplmt_lef; exact: QQ.
apply: (le_trans (V rho)); apply: expect_mono=>s.
by rewrite /complement /= -cplmt_lef; apply: PP.
Qed.

Example abort_not_total_top (s : cmem) (rho : 'FD1(Hq)) :
  ~ valid true semantic_top Abort semantic_top.
Proof.
move=>V; move: (V (CQState.point s rho)).
rewrite run_abort expect_bottom /semantic_top expect_identity
  -CQState.mass_trace CQState.point_mass den1f_trlf.
by rewrite ler10.
Qed.

End Logic.

Import CQAssertion CQPredicate ClassicalLanguage.

Local Notation assertion := (@semantic_assertion cmem Hq).
Implicit Types (P Q R : assertion).

Definition wp_command c Q := wp (denote c) Q.
Definition wlp_command c Q := wlp (denote c) Q.
Definition pre total c Q := xp total (denote c) Q.

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

(* Core inference rules, including the partial and total loop rules. *)
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

Lemma valid_total_iff P c Q :
  valid true P c Q <-> semantic_le P (wp_command c Q).
Proof.
split=>V.
- apply/(proj2 (CQExpectation.semantic_le_iff_expect _ _))=>rho.
  by rewrite /wp_command expect_wp; apply: V.
- move=>rho; rewrite -expect_wp.
  by apply: expect_mono; apply: V.
Qed.

Lemma valid_partial_iff P c Q :
  valid false P c Q <-> semantic_le P (wlp_command c Q).
Proof.
split=>V.
- apply/(proj2 (CQExpectation.semantic_le_iff_expect _ _))=>rho.
  rewrite /wlp_command expect_wlp.
  exact: (proj1 (valid_partial_loss P c Q) V rho).
- apply/(proj2 (valid_partial_loss P c Q))=>rho.
  rewrite -expect_wlp; apply: expect_mono; exact: V.
Qed.

Lemma valid_iff total P c Q :
  valid total P c Q <-> semantic_le P (pre total c Q).
Proof. by case: total; [apply: valid_total_iff | apply: valid_partial_iff]. Qed.

Lemma pre_valid total c Q : valid total (pre total c Q) c Q.
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
  valid total (mask (esem b) P) c1 Q ->
  valid total (mask (predC (esem b)) P) c0 Q ->
  valid total P (Conditional b c1 c0) Q.
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
  valid false (mask (esem b) P) c P ->
  valid false P (While b c) (mask (predC (esem b)) P).
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


Lemma wp_unrollS b c Q n :
  wp_command (unroll b c n.+1) Q =
  conditional (esem b) (wp_command c (wp_command (unroll b c n) Q)) Q.
Proof. exact: (pre_unrollS true b c Q n). Qed.

Lemma valid_while_total P b c :
  valid true (mask (esem b) P) c P -> ranking P b c ->
  valid true P (While b c) (mask (predC (esem b)) P).
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


Theorem derives_sound total P c Q : derives total P c Q -> valid total P c Q.
Proof.
move=>D; induction D.
- exact: valid_skip.
- exact: pre_valid.
- exact: pre_valid.
- exact: pre_valid.
- exact: pre_valid.
- exact: pre_valid.
- exact: valid_abort_partial.
- by apply: valid_abort_total.
- exact: valid_sequence IHD1 IHD2.
- exact: valid_conditional IHD1 IHD2.
- exact: valid_while_partial IHD.
- apply: valid_while_total; assumption.
- exact: (@valid_consequence total P Q P' Q' c H H0 IHD).
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
  valid total P c Q -> derives total P c Q.
Proof.
move=>/(proj1 (valid_iff _ _ _ _)) bound.
apply: (@DConsequence total (pre total c Q) Q P Q c).
- exact: bound.
- exact: semantic_le_refl.
- exact: derives_pre.
Qed.

Theorem sound_complete total P c Q :
  derives total P c Q <-> valid total P c Q.
Proof. split; [exact: derives_sound | exact: derives_complete]. Qed.
Example two_skips total P : derives total P (Sequence Skip Skip) P.
Proof. apply: DSequence; apply: DSkip. Qed.

Example two_skips_sound total P : valid total P (Sequence Skip Skip) P.
Proof. apply: derives_sound; apply: two_skips. Qed.

Example set_integer_constant total (x : variable Integer) (z : int) (M : 'FO(Hq)) :
  derives total (fun _ => M) (Assign x (EConst z))
    (fun s => if (s.[x])%M == z then M else (0%:VF : 'FO(Hq))).
Proof. apply: derives_complete; apply: valid_assign=>s; by rewrite eval_const get_set_eq eqxx. Qed.

Example set_integer_constant_sound total (x : variable Integer) (z : int)
    (M : 'FO(Hq)) :
  valid total (fun _ => M) (Assign x (EConst z))
    (fun s => if (s.[x])%M == z then M else (0%:VF : 'FO(Hq))).
Proof. apply: derives_sound; exact: set_integer_constant. Qed.

Example partial_abort_top :
  derives false semantic_top Abort semantic_top.
Proof.
apply: (@DConsequence false semantic_top semantic_bottom
  semantic_top semantic_top Abort).
- exact: semantic_le_refl.
- exact: semantic_bottom_le.
- by apply: DAbortPartial.
Qed.

Example partial_abort_top_sound : valid false semantic_top Abort semantic_top.
Proof. apply: derives_sound; exact: partial_abort_top. Qed.


End CQHoare.


Module CQNormalizedValidity.
(* Lemma 4.10; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma operator_le_normalized (H : chsType) (f g : 'End(H)) :
  (forall rho : 'FD1(H), \Tr (f \o rho) <= \Tr (g \o rho)) -> f ⊑ g.
Proof.
move=>Htest; apply/lef_trden=>rho.
have Hp : 0 <= \Tr rho := psdlf_trlf (is_psdlf rho).
case Hpos: (0 < \Tr rho).
- have Hnorm : (\Tr rho)^-1 *: (rho : 'End(H)) \is den1lf.
    apply/den1lfP; split.
    + apply: psdlfZ; first by rewrite invr_ge0.
      exact: is_psdlf.
    + by rewrite linearZ /= mulVf ?gt_eqF.
  have Htestnorm := Htest (Den1Lf_Build Hnorm).
  have Hscaled : \Tr rho * \Tr (f \o ((\Tr rho)^-1 *: (rho : 'End(H)))) <=
      \Tr rho * \Tr (g \o ((\Tr rho)^-1 *: (rho : 'End(H)))).
    apply: ler_wpM2l; first exact: Hp.
    exact: Htestnorm.
  by move: Hscaled; rewrite !linearZ /= !mulrA mulfV ?gt_eqF ?mul1r.
- have Htr : \Tr rho = 0.
    by move: Hp; rewrite le_eqVlt Hpos orbF eq_sym=>/eqP.
  have Hr : (rho : 'End(H)) = 0.
    apply/eqP/trlf0_eq0; split=>//; by rewrite -psdlfE; exact: is_psdlf.
  by rewrite Hr !comp_lfun0r !linear0.
Qed.

Definition normalized_valid total (P : @semantic_assertion cmem Hq) (c : ClassicalLanguage.command) Q :=
  forall m (rho : 'FD1(Hq)),
  if total then expect P (CQState.point m (rho : 'FD(Hq))) <=
    expect Q (CQHoare.run c (CQState.point m (rho : 'FD(Hq))))
  else expect (complement Q) (CQHoare.run c (CQState.point m (rho : 'FD(Hq)))) <=
    expect (complement P) (CQState.point m (rho : 'FD(Hq))).

Theorem valid_normalized_iff total P c Q :
  CQHoare.valid total P c Q <-> normalized_valid total P c Q.
Proof.
split; first by move=>H m rho; exact: H.
case: total=>H.
- apply/(proj2 (CQHoare.valid_total_iff _ _ _))=>m.
  apply: operator_le_normalized=>rho.
  have Hpoint := H m rho.
  by move: Hpoint; rewrite /CQHoare.run -expect_wp !CQExpectation.expect_point.
- apply/(proj2 (CQHoare.valid_partial_iff _ _ _))=>m.
  rewrite /CQHoare.wlp_command /wlp /complement /= cplmt_lef cplmtK.
  apply: operator_le_normalized=>rho.
  have Hpoint := H m rho.
  by move: Hpoint; rewrite /CQHoare.run -expect_wp !CQExpectation.expect_point.
Qed.


Theorem valid_total_normalized P c Q :
  CQHoare.valid true P c Q <->
  forall m (rho : 'FD1(Hq)),
    expect P (CQState.point m (rho : 'FD(Hq))) <=
    expect Q (CQHoare.run c (CQState.point m (rho : 'FD(Hq)))).
Proof. exact: valid_normalized_iff. Qed.

Theorem valid_partial_normalized P c Q :
  CQHoare.valid false P c Q <->
  forall m (rho : 'FD1(Hq)),
    expect P (CQState.point m (rho : 'FD(Hq))) <=
    expect Q (CQHoare.run c (CQState.point m (rho : 'FD(Hq)))) + 1 -
    CQState.mass (CQHoare.run c (CQState.point m (rho : 'FD(Hq)))).
Proof.
have algebra (a b c0 d : C) : (a - b <= c0 - d) = (d <= b + c0 - a).
  by rewrite lerBrDl addrA lerBlDr lerBrDr [c0 + b]addrC.
rewrite valid_normalized_iff /normalized_valid.
split=>V m rho; move: (V m rho);
  by rewrite !expect_complement -!CQState.mass_trace CQState.point_mass den1f_trlf algebra.
Qed.
End CQNormalizedValidity.


Module CQRanking.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import CQAssertion CQHoare CQExpectationLimits.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma ranking_infimum P b c (r : ranking P b c) :
  semantic_inf (ranking_assertion r) = semantic_bottom.
Proof.
apply/funext=>s; apply/val_inj.
change ((semantic_inf (ranking_assertion r) s : 'End(Hq)) = 0).
have C1 := @semantic_inf_cvg cmem Hq (ranking_assertion r)
  (ranking_decreases r) s.
have C2 := @ranking_zero P b c r s.
by rewrite -(cvg_lim (@norm_hausdorff _ _) C1) (cvg_lim (@norm_hausdorff _ _) C2).
Qed.

Definition ranking_of_infimum P b c (f : nat -> assertion)
    (dec : semantic_decreasing f) (ini : semantic_le P (f 0%N))
    (infimum : semantic_inf f = semantic_bottom)
    (step : forall n, semantic_le (mask (esem b) (wp_command c (f n))) (f n.+1))
    : ranking P b c.
Proof.
apply: (@Ranking P b c f dec ini _ step)=>s.
have C := @semantic_inf_cvg cmem Hq f dec s.
by rewrite infimum in C.
Defined.
End CQRanking.


Module CQRuleExamples.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import CQAssertion CQPredicate CQHoare ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Implicit Types P Q : cmem -> 'FO(Hq).

Lemma assignment total t (x : variable t) e Q :
  derives total (fun s => Q (s.[x <- eval e s])%M) (Assign x e) Q.
Proof.
have E : pre total (Assign x e) Q = (fun s => Q (s.[x <- eval e s])%M).
  apply/funext=>s; apply/val_inj.
  change ((pre total (Assign x e) Q s : 'End(Hq)) =
    (Q (s.[x <- eval e s])%M : 'End(Hq))).
  exact: CQPrimitive.assign_pre.
rewrite -E; exact: DAssign.
Qed.

Example false_loop total P c : derives total P (While (EConst false) c) P.
Proof.
have E : pre total (While (EConst false) c) P = P.
  rewrite pre_while_unfold; apply/funext=>s.
  by rewrite /conditional /EConst /=.
rewrite -{1}E; exact: derives_pre.
Qed.

Example infinite_skip_partial :
  derives false semantic_top (While (EConst true) Skip) semantic_top.
Proof.
apply: (@DConsequence false semantic_top
  (mask (predC (esem (EConst true))) semantic_top)
  semantic_top semantic_top (While (EConst true) Skip)).
- exact: semantic_le_refl.
- move=>s; exact: obsf_le1.
- apply: DWhilePartial.
  have -> : mask (esem (EConst true)) semantic_top = semantic_top by [].
  exact: DSkip.
Qed.

Example infinite_skip_not_total (s : cmem) (rho : 'FD1(Hq)) :
  ~ derives true semantic_top (While (EConst true) Skip) semantic_top.
Proof.
move=>/derives_sound V.
apply: (CQHoare.abort_not_total_top s rho)=>d.
move: (V d); by rewrite /CQHoare.run true_skip_loop_diverges.
Qed.


End CQRuleExamples.


Module CQStateUpdate.
(* Lemma 3.12; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation state := (@CQState.state cmem Hq).

Definition substitute t (x : variable t) (e : expression (value t))
    (P : assertion) : assertion := fun m => P (m.[x <- eval e m])%M.

Definition update_state t (x : variable t) (e : expression (value t))
    (rho : state) : state :=
  CQKernel.apply (sunit (fun _ : cmem => (\:1 : 'QO(Hq)))
    (fun m => (m.[x <- eval e m])%M)) rho.

Lemma update_stateE t (x : variable t) (e : expression (value t)) rho out :
  update_state x e rho out =
    sum (fun m => if out == (m.[x <- eval e m])%M then rho m else 0).
Proof.
rewrite /update_state CQKernel.applyE; apply:eq_sum=>m.
rewrite /sunit /= /sunit_def.
by case: ifP=>_; rewrite ?id_soE ?abort_soE.
Qed.

Theorem expect_update t (x : variable t) (e : expression (value t)) P rho :
  expect (substitute x e P) rho = expect P (update_state x e rho).
Proof.
rewrite /update_state CQKernelExpectation.expect_sunit /expect.
apply:eq_sum=>m; by rewrite /expect_term /substitute id_soE.
Qed.

Theorem update_state_mass t (x : variable t) (e : expression (value t)) rho :
  CQState.mass (update_state x e rho) = CQState.mass rho.
Proof.
have E := expect_update x e semantic_top rho.
change (expect semantic_top rho = expect semantic_top (update_state x e rho)) in E.
by move: E; rewrite !expect_identity -!CQState.mass_trace=>->.
Qed.

Lemma update_state_assignment t (x : variable t) (e : expression (value t)) rho :
  update_state x e rho = CQHoare.run (Assign x e) rho.
Proof. by []. Qed.
End CQStateUpdate.


Module CQRankingComplement.
(* Complement rankings: Lemma 5.4 and WhileT′. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import ClassicalLanguage CQAssertion CQHoare CQPredicate CQExpectationLimits.

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
