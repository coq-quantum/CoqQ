(* Lemma 4.10; see NORMALIZED-UPDATE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate
  hoare rules expectation.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQNormalizedValidity.
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
- apply/(proj2 (CQRules.valid_total_iff _ _ _))=>m.
  apply: operator_le_normalized=>rho.
  have Hpoint := H m rho.
  by move: Hpoint; rewrite /CQHoare.run -expect_wp !CQExpectation.expect_point.
- apply/(proj2 (CQRules.valid_partial_iff _ _ _))=>m.
  rewrite /CQRules.wlp_command /wlp /complement /= cplmt_lef cplmtK.
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
