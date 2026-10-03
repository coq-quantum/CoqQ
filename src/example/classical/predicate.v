(* Weakest preconditions for arbitrary classical-quantum kernels.
   See HOARE-NOTES.md for the infinite-sum and duality arguments. *)
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
From quantum.example.classical Require Import state assertion kernel kernel_expectation.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQPredicate.
Import CQAssertion.
Section Kernel.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H) (Q : J -> 'FO(H)).

Definition term i j : 'End(H) := (K i j)^*o (Q j).

Lemma term_positive i j : 0%:VF ⊑ term i j.
Proof. apply: cp_ge0; exact: obsf_ge0. Qed.

Lemma partial_bound i A : psum (term i) A ⊑ (\1 : 'End(H)).
Proof.
apply: (le_trans (y := (psum (K i) A)^*o (\1))).
- rewrite /term /psum linear_sum /= sum_soE.
  apply: lev_sum=>j _; apply: cp_preserve_order; exact: obsf_le1.
- exact: dqo1_le1.
Qed.

Lemma term_summable i : summable (term i).
Proof.
apply: psum_ubounded_summable; exists (\Tr (\1 : 'End(H)))=>A.
rewrite /psum /normf.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?term_positive //.
rewrite -linear_sum /=.
apply: lef_trlf; exact: partial_bound.
Qed.

Definition wp_raw i := sum (term i).

Lemma wp_positive i : 0%:VF ⊑ wp_raw i.
Proof.
apply: lim_gev_near; first by apply: norm_bounded_cvg; apply: term_summable.
by near=>A; apply: sumv_ge0=>j _; apply: term_positive.
Unshelve. end_near.
Qed.

Lemma wp_bounded i : wp_raw i ⊑ (\1 : 'End(H)).
Proof.
apply: lim_lev_near; first by apply: norm_bounded_cvg; apply: term_summable.
by near=>A; apply: partial_bound.
Unshelve. end_near.
Qed.

Lemma wp_effect i : wp_raw i \is obslf.
Proof. by rewrite obslfE; apply/andP; split; [exact: wp_positive i | exact: wp_bounded i]. Qed.

Definition wp i : 'FO(H) := ObsLf_Build (wp_effect i).

Lemma wpE i : (wp i : 'End(H)) = sum (fun j => (K i j)^*o (Q j)).
Proof. by []. Qed.

Lemma wp_pairing i (rho : 'End(H)) :
  \Tr (wp i \o rho) = sum (fun j => \Tr (Q j \o K i j rho)).
Proof.
rewrite wpE (cvg_linearP_sum (f := fun A : 'End(H) => \Tr (A \o rho))).
- by move=>a x y; rewrite linearPl /= linearP.
- by apply: norm_bounded_cvg; apply: term_summable.
- by apply: eq_sum=>j; rewrite dualso_trlfEV.
Qed.

Lemma expect_wp (rho : @CQState.state I H) :
  expect wp rho = expect Q (CQKernel.apply K rho).
Proof.
rewrite CQKernelExpectation.expect_apply_sum /expect.
by apply: eq_sum=>i; rewrite /expect_term wp_pairing.
Qed.
End Kernel.

Section Laws.
Context {I J : choiceType} {H : chsType}.
Implicit Types (K L : semType I J H H) (P Q : J -> 'FO(H)).

Lemma wp_mono K P Q : semantic_le P Q -> semantic_le (wp K P) (wp K Q).
Proof.
move=>PQ i; rewrite !wpE.
apply: lev_lim_near.
- by apply: norm_bounded_cvg; apply: term_summable.
- by apply: norm_bounded_cvg; apply: term_summable.
- by near=>A; apply: lev_sum=>j _; apply: cp_preserve_order; apply: PQ.
Unshelve. end_near.
Qed.

Lemma dualso_mono (E F : 'SO(H)) : E ⊑ F -> E^*o ⊑ F^*o.
Proof.
move=>EF.
by rewrite -subv_ge0 -linearB geso0_cpE dualso_cpE -geso0_cpE subv_ge0.
Qed.

Lemma wp_kernel_mono K L P :
  (forall i j, K i j ⊑ L i j) -> semantic_le (wp K P) (wp L P).
Proof.
move=>KL i; rewrite !wpE; apply: lev_lim_near.
- by apply: norm_bounded_cvg; apply: term_summable.
- by apply: norm_bounded_cvg; apply: term_summable.
- near=>A; apply: lev_sum=>j _.
  apply: leso_preserve_order; [apply: dualso_mono; apply: KL | exact: obsf_ge0].
Unshelve. end_near.
Qed.

Lemma wp_ext K L P Q :
  (forall i j, K i j = L i j) -> (forall j, P j = Q j) -> wp K P = wp L Q.
Proof.
move=>KL PQ; apply/funext=>i; apply/val_inj.
change ((wp K P i : 'End(H)) = (wp L Q i : 'End(H))).
rewrite !wpE.
by apply: eq_sum=>j; rewrite KL PQ.
Qed.

Definition wlp K Q := complement (wp K (complement Q)).
Definition xp total K Q := if total then wp K Q else wlp K Q.

Lemma complementK P : complement (complement P) = P.
Proof. apply/funext=>i; apply/val_inj; by rewrite /complement /= cplmtK. Qed.

Lemma expect_wlp K Q (rho : @CQState.state I H) :
  expect (wlp K Q) rho = expect Q (CQKernel.apply K rho) +
    CQState.mass rho - CQState.mass (CQKernel.apply K rho).
Proof.
rewrite /wlp expect_complement expect_wp expect_complement -!CQState.mass_trace.
by rewrite opprB addrA [CQState.mass rho + _]addrC.
Qed.

Lemma wlp_mono K P Q : semantic_le P Q -> semantic_le (wlp K P) (wlp K Q).
Proof.
move=>PQ i; rewrite /wlp /complement /= -cplmt_lef.
apply: wp_mono=>j; rewrite /complement /= -cplmt_lef; exact: PQ.
Qed.

Lemma xp_mono total K P Q : semantic_le P Q -> semantic_le (xp total K P) (xp total K Q).
Proof. by case: total; [apply: wp_mono | apply: wlp_mono]. Qed.

Lemma wp_zero K : wp K semantic_bottom = semantic_bottom.
Proof.
apply/funext=>i; apply/val_inj.
change ((wp K semantic_bottom i : 'End(H)) = 0).
rewrite wpE.
under eq_sum do rewrite /semantic_bottom linear0.
exact: summable_sum_cst0.
Qed.

Lemma wlp_top K : wlp K semantic_top = semantic_top.
Proof.
have CT : @complement J H semantic_top = semantic_bottom.
  by apply/funext=>i; apply/val_inj; rewrite /complement /semantic_top /= cplmt1.
rewrite /wlp CT wp_zero; apply/funext=>i; apply/val_inj.
by rewrite /complement /semantic_bottom /semantic_top /= cplmt0.
Qed.

Lemma wp_add_upper K P Q (R : J -> 'FO(H)) :
  (forall j, (P j : 'End(H)) ⊑ (Q j : 'End(H)) + (R j : 'End(H))) ->
  forall i, (wp K P i : 'End(H)) ⊑ (wp K Q i : 'End(H)) + (wp K R i : 'End(H)).
Proof.
move=>PQR i; rewrite !wpE.
rewrite -(summable_sumD (Summable.build (term_summable K Q i))
  (Summable.build (term_summable K R i))).
apply: lev_lim_near.
- by apply: norm_bounded_cvg; apply: term_summable.
- exact: summable_cvg.
- near=>A; apply: lev_sum=>j _; rewrite summableE /= /term -linearD /=.
  apply: cp_preserve_order; exact: PQR.
Unshelve. end_near.
Qed.

Lemma wp_difference K P Q (R : J -> 'FO(H)) :
  (forall j, (R j : 'End(H)) = (P j : 'End(H)) - (Q j : 'End(H))) ->
  forall i, (wp K R i : 'End(H)) = (wp K P i : 'End(H)) - (wp K Q i : 'End(H)).
Proof.
move=>RPQ i; rewrite !wpE.
rewrite -(summable_sumB (Summable.build (term_summable K P i))
  (Summable.build (term_summable K Q i))).
by apply: eq_sum=>j; rewrite summableE /= /term RPQ linearB.
Qed.

End Laws.

Section Point.
Context {I J : choiceType} {H : chsType}.
Lemma wp_point (K : semType I J H H) (Q : J -> 'FO(H)) i (rho : 'FD(H)) :
  \Tr (wp K Q i \o rho) = expect Q (CQKernel.apply K (CQState.point i rho)).
Proof.
rewrite -expect_wp (@expect_singleton I H (wp K Q) (CQState.point i rho) i).
- by move=>j /negPf ji; rewrite CQState.pointE ji.
- by rewrite CQState.pointE eqxx.
Qed.

End Point.

Section Composition.
Context {I M J : choiceType} {H : chsType}.

Lemma effect_eq (P Q : 'FO(H)) :
  (forall rho : 'FD(H), \Tr (P \o rho) = \Tr (Q \o rho)) -> P = Q.
Proof.
move=>PQ; apply/val_inj/le_anti/andP; split;
  apply/lef_trden=>rho; by rewrite PQ.
Qed.

Lemma wp_sequence (K : semType I M H H) (L : semType M J H H) Q :
  wp (slet K L) Q = wp K (wp L Q).
Proof.
apply/funext=>i; apply: effect_eq=>rho.
by rewrite !wp_point expect_wp CQKernel.apply_sequence.
Qed.

Lemma wlp_sequence (K : semType I M H H) (L : semType M J H H) Q :
  wlp (slet K L) Q = wlp K (wlp L Q).
Proof. by rewrite /wlp wp_sequence complementK. Qed.

Lemma xp_sequence total (K : semType I M H H) (L : semType M J H H) Q :
  xp total (slet K L) Q = xp total K (xp total L Q).
Proof. by case: total; [apply: wp_sequence | apply: wlp_sequence]. Qed.
End Composition.

Section Primitives.
Context {I J : choiceType} {H : chsType}.

Lemma wp_sunit (F : I -> 'QO(H)) (update : I -> J) (Q : J -> 'FO(H)) i :
  (wp (sunit F update) Q i : 'End(H)) = (F i)^*o (Q (update i)).
Proof.
rewrite wpE (fin_supp_sum (S := [fset update i]%fset)).
- move=>j; rewrite inE=>/negPf ji.
  by rewrite /sunit /= /sunit_def ji dualso0 soE.
- by rewrite psum1 /sunit /= /sunit_def eqxx.
Qed.

Lemma xp_sunit total (F : I -> 'QC(H)) (update : I -> J)
    (Q : J -> 'FO(H)) i :
  (xp total (sunit (fun i => (F i : 'QO(H))) update) Q i : 'End(H)) =
    (F i)^*o (Q (update i)).
Proof.
case: total; first exact: wp_sunit.
change (cplmt (wp (sunit (fun i => (F i : 'QO(H))) update) (complement Q) i) =
  (F i)^*o (Q (update i))).
by rewrite wp_sunit cplmt_dualC /= /complement /= cplmtK.
Qed.

Lemma wp_skip (Q : I -> 'FO(H)) : wp skip_sem Q = Q.
Proof.
apply/funext=>i; apply: effect_eq=>rho.
rewrite wp_point CQKernel.apply_skip (@expect_singleton I H Q (CQState.point i rho) i).
- by move=>j /negPf ji; rewrite CQState.pointE ji.
- by rewrite CQState.pointE eqxx.
Qed.

Lemma wp_abort (Q : I -> 'FO(H)) :
  wp (@abort_sem I H) Q = semantic_bottom.
Proof.
apply/funext=>i; apply/val_inj.
change ((wp (@abort_sem I H) Q i : 'End(H)) = 0).
rewrite wpE.
under eq_sum do rewrite abort_semE dualso0 soE.
exact: summable_sum_cst0.
Qed.

Lemma wlp_skip (Q : I -> 'FO(H)) : wlp skip_sem Q = Q.
Proof. by rewrite /wlp wp_skip complementK. Qed.

Lemma wlp_abort (Q : I -> 'FO(H)) :
  wlp (@abort_sem I H) Q = semantic_top.
Proof.
rewrite /wlp wp_abort; apply/funext=>i; apply/val_inj.
by rewrite /complement /semantic_bottom /semantic_top /= cplmt0.
Qed.

Lemma xp_skip total (Q : I -> 'FO(H)) : xp total skip_sem Q = Q.
Proof. by case: total; [apply: wp_skip | apply: wlp_skip]. Qed.
End Primitives.

Section Branching.
Context {H : chsType}.
Variable (b : bexpr) (K L : semType cmem cmem H H).
Implicit Type Q : cmem -> 'FO(H).

Lemma wp_conditional Q :
  wp (if_sem b K L) Q = conditional (esem b) (wp K Q) (wp L Q).
Proof.
apply/funext=>i; apply/val_inj.
change ((wp (if_sem b K L) Q i : 'End(H)) =
  (conditional (esem b) (wp K Q) (wp L Q) i : 'End(H))).
rewrite wpE /conditional /= /if_sem /=.
by case: (esem b i); rewrite wpE.
Qed.

Lemma wlp_conditional Q :
  wlp (if_sem b K L) Q = conditional (esem b) (wlp K Q) (wlp L Q).
Proof.
rewrite /wlp wp_conditional; apply/funext=>i.
by rewrite /complement /conditional; case: (esem b i).
Qed.

Lemma xp_conditional total Q :
  xp total (if_sem b K L) Q = conditional (esem b) (xp total K Q) (xp total L Q).
Proof. by case: total; [apply: wp_conditional | apply: wlp_conditional]. Qed.
End Branching.

Section Reindexing.
Context {I T J : choiceType} {H : chsType}.
Variable (f : I -> T -> J) (g : I -> {vdistr T -> 'SO(H)})
  (Q : J -> 'FO(H)).

Definition row_kernel i : semType unit T H H := SemType (fun _ => g i).
Definition row_effects i := Summable.build
  (term_summable (row_kernel i) (fun t => Q (f i t)) tt).

Lemma filtered_row_summable i j :
  summable (fun t => sunit_def (f i t) (g i t : 'SO(H)) j).
Proof.
apply: psum_ubounded_summable.
exists `|g i : {summable T -> 'SO(H)}|=>A.
apply: (le_trans _ (psum_norm_ler_norm (g i) A)).
apply: ler_sum=>t _; rewrite /sunit_def /normf.
by case: ifP=>_; rewrite ?normr0.
Qed.

Lemma wp_sdlet i :
  (wp (sdlet f g) Q i : 'End(H)) = sum (fun t => (g i t)^*o (Q (f i t))).
Proof.
rewrite wpE.
transitivity (sum (sdlet_def (f i) (row_effects i))).
- apply: eq_sum=>j.
  change ((sum (fun t => sunit_def (f i t) (g i t : 'SO(H)) j))^*o (Q j) =
    sum (fun t => sunit_def (f i t) (row_effects i t) j)).
  rewrite (cvg_linearP_sum (f := fun E : 'SO(H) => E^*o (Q j))).
  + by move=>a x y; rewrite linearP /= !soE.
  + by apply: norm_bounded_cvg; apply: filtered_row_summable.
  + apply: eq_sum=>t; rewrite /= /sunit_def.
    case: eqP=>[->|_]; first by [].
    by rewrite dualso0 soE.
- rewrite sdlet_sum; by [].
Qed.
End Reindexing.

Section Channels.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H).

Lemma wp_top : (forall i, sum (K i) \is tpmap) ->
  wp K semantic_top = semantic_top.
Proof.
move=>KT; apply/funext=>i; apply: effect_eq=>rho.
rewrite wp_pairing /semantic_top /= comp_lfun1l.
under eq_sum do rewrite comp_lfun1l.
rewrite -(cvg_linearP_sum (x := K i) (f := fun E : 'SO(H) => \Tr (E rho))).
- by move=>a x y; rewrite !soE linearP.
- exact: summable_cvg.
- by move: (KT i)=>/tpmapP/(_ rho).
Qed.

Lemma wlp_wp (Q : J -> 'FO(H)) : wp K semantic_top = semantic_top ->
  wlp K Q = wp K Q.
Proof.
move=>KT; apply/funext=>i; apply/val_inj.
change (cplmt (wp K (complement Q) i) = (wp K Q i : 'End(H))).
have C j : (complement Q j : 'End(H)) =
    (semantic_top j : 'End(H)) - (Q j : 'End(H)) by [].
rewrite (wp_difference K C) KT /semantic_top /=.
exact: cplmtK.
Qed.

Lemma xp_wp total (Q : J -> 'FO(H)) :
  (forall i, sum (K i) \is tpmap) -> xp total K Q = wp K Q.
Proof. by move=>KT; case: total=>//; apply: wlp_wp; exact: wp_top KT. Qed.
End Channels.
End CQPredicate.
