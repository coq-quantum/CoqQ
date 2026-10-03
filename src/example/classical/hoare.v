(* Structural inference system and soundness. See HOARE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQHoare.
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

Inductive derives : bool -> assertion -> command -> assertion -> Prop :=
| DSkip total P : derives total P Skip P
| DAssign total t (x : variable t) (e : expression (value t)) P Q :
    (forall s, P s = Q (s.[x <- eval e s])%M) ->
    derives total P (Assign x e) Q
| DAbortPartial P Q :
    (forall s, P s = (\1 : 'FO(Hq))) ->
    (forall s, Q s = (0%:VF : 'FO(Hq))) ->
    derives false P Abort Q
| DAbortTotal P Q :
    (forall s, P s = (0%:VF : 'FO(Hq))) ->
    (forall s, Q s = (0%:VF : 'FO(Hq))) ->
    derives true P Abort Q
| DSequence total P Q R c1 c2 :
    derives total P c1 Q -> derives total Q c2 R ->
    derives total P (Sequence c1 c2) R
| DConsequence total P Q P' Q' c :
    semantic_le P' P -> semantic_le Q Q' -> derives total P c Q ->
    derives total P' c Q'.

Theorem derives_sound total P c Q : derives total P c Q -> valid total P c Q.
Proof.
move=>D; induction D.
- exact: valid_skip.
- exact: valid_assign.
- exact: valid_abort_partial.
- exact: valid_abort_total.
- exact: valid_sequence IHD1 IHD2.
- exact: (@valid_consequence total P Q P' Q' c H H0 IHD).
Qed.

Example two_skips total P : derives total P (Sequence Skip Skip) P.
Proof. apply: DSequence; apply: DSkip. Qed.

Example two_skips_sound total P : valid total P (Sequence Skip Skip) P.
Proof. apply: derives_sound; apply: two_skips. Qed.

Example set_integer_constant total (x : variable Integer) (z : int) (M : 'FO(Hq)) :
  derives total (fun _ => M) (Assign x (EConst z))
    (fun s => if (s.[x])%M == z then M else (0%:VF : 'FO(Hq))).
Proof. apply: DAssign=>s; by rewrite eval_const get_set_eq eqxx. Qed.

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

Example abort_not_total_top (s : cmem) (rho : 'FD1(Hq)) :
  ~ valid true semantic_top Abort semantic_top.
Proof.
move=>V; move: (V (CQState.point s rho)).
rewrite run_abort expect_bottom /semantic_top expect_identity
  -CQState.mass_trace CQState.point_mass den1f_trlf.
by rewrite ler10.
Qed.

End Logic.
End CQHoare.
