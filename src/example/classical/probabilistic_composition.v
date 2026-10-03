(* Probabilistic composition via saturated projector support. See HOARE-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace hspace_extra summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules expectation assertion_algebra.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.



Module CQProbabilisticComposition.
Import CQAssertion CQExpectation CQPredicate CQRules ClassicalLanguage.
Local Open Scope hspace_scope.
Local Notation C := hermitian.C.

Section Support.
Context {I : choiceType} {H : chsType}.
Definition projection_assertion (P : I -> {hspace H}) : I -> 'FO(H) :=
  fun i => [obs of P i].

Lemma expect_term_le_expect (P : I -> 'FO(H)) (rho : @CQState.state I H) i :
  expect_term P rho i <= expect P rho.
Proof.
pose terms := Summable.build (expect_summable P rho).
have B := psum_norm_ler_norm terms [fset i]%fset.
have E : psum (fun j => `|terms j|) = psum terms.
  apply: psum_abs_ge0E=>j; exact: expect_term_ge0.
move: B; rewrite psum1 /summable_norm E.
change (`|expect_term P rho i| <= expect P rho ->
  expect_term P rho i <= expect P rho).
by rewrite ger0_norm ?expect_term_ge0.
Qed.

Lemma expect_zero_term (P : I -> 'FO(H)) (rho : @CQState.state I H) :
  expect P rho = 0 -> forall i, expect_term P rho i = 0.
Proof.
move=>E i; apply/eqP; rewrite eq_le expect_term_ge0 andbT.
by move: (expect_term_le_expect P rho i); rewrite E.
Qed.

Lemma projection_saturated_support (P : I -> {hspace H})
    (rho : @CQState.state I H) :
  expect (projection_assertion P) rho = CQState.mass rho ->
  forall i, supph (rho i) `<=` P i.
Proof.
move=>E i.
have Ec : expect (complement (projection_assertion P)) rho = 0.
  by rewrite expect_complement -CQState.mass_trace E subrr.
have Ei := expect_zero_term Ec i.
have Hr : rho i \is psdlf by rewrite psdlfE vdistr_ge0.
apply: (@supph_trlf0_le H (PsdLf_Build Hr) (P i)).
move: Ei; rewrite /expect_term /complement /projection_assertion /=.
by rewrite lftraceC hscmpltE.
Qed.

Lemma support_compr (r : 'F+(H)) (P : {hspace H}) :
  supph r `<=` P -> (r : 'End(H)) \o P = r.
Proof.
move=>HP; move: HP; rewrite leh_compl=>/eqP HP.
rewrite -{1}(suppvlf (r : 'End(H))) -comp_lfunA.
move: HP; rewrite /supph !hsE /= =>HP.
by rewrite HP suppvlf.
Qed.

Lemma support_compl (r : 'F+(H)) (P : {hspace H}) :
  supph r `<=` P -> P \o (r : 'End(H)) = r.
Proof.
move=>Hsupport; have E := support_compr Hsupport.
by move: (f_equal (fun A : 'End(H) => A^A) E); rewrite adjf_comp !hermf_adjE.
Qed.

Lemma supported_pairing (r : 'F+(H)) (P : {hspace H}) (M : 'End(H)) a :
  supph r `<=` P -> P \o M \o P = a *: (P : 'End(H)) ->
  \Tr (M \o r) = a * \Tr r.
Proof.
move=>Hs HM.
have RP := support_compr Hs.
have PR := support_compl Hs.
rewrite -{1}RP comp_lfunA.
rewrite [\Tr ((M \o r) \o P)]lftraceC comp_lfunA.
rewrite -{1}PR comp_lfunA HM linearZl /= linearZ /= PR.
by [].
Qed.

Lemma saturated_expectation (P : I -> {hspace H}) (M : I -> 'FO(H)) a
    (rho : @CQState.state I H) :
  expect (projection_assertion P) rho = CQState.mass rho ->
  (forall i, P i \o M i \o P i = a *: (P i : 'End(H))) ->
  expect M rho = a * CQState.mass rho.
Proof.
move=>E HM.
pose terms := Summable.build (expect_summable (@semantic_top I H) rho).
have Et : sum terms = CQState.mass rho.
  change (expect semantic_top rho = CQState.mass rho).
  by rewrite expect_identity CQState.mass_trace.
have TE : expect_term M rho = a *: terms.
  apply/funext=>i.
  have Hr : rho i \is psdlf by rewrite psdlfE vdistr_ge0.
  change (\Tr (M i \o rho i) = a * \Tr (\1 \o rho i)).
  rewrite comp_lfun1l.
  exact: (supported_pairing (r := PsdLf_Build Hr) (M := M i)
    (projection_saturated_support E i) (HM i)).
by rewrite /expect TE summable_sumZ Et.
Qed.
End Support.

Section Rule.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Theorem valid_probcomp_projection (p : pred cmem) (P : cmem -> {hspace Hq})
    (M R Q : assertion) (a : C) c d :
  (forall s, (R s : 'End(Hq)) = if p s then a *: \1 else 0) ->
  (forall s, P s \o M s \o P s = a *: (P s : 'End(Hq))) ->
  CQHoare.valid true (mask p semantic_top) c (projection_assertion P) ->
  CQHoare.valid true M d Q ->
  CQHoare.valid true R (Sequence c d) Q.
Proof.
move=>RE HM Vc Vd; apply/(proj2 (valid_total_iff _ _ _))=>s.
apply/lef_trden=>rho; rewrite /wp_command wp_point.
change (\Tr (R s \o rho) <=
  expect Q (CQHoare.run (Sequence c d) (CQState.point s rho))).
rewrite CQHoare.run_sequence RE.
case Ep: (p s); last by rewrite comp_lfun0l linear0; apply: expect_ge0.
rewrite linearZl /= linearZ /= comp_lfun1l.
pose output := CQHoare.run c (CQState.point s rho).
have Hfirst : \Tr rho <= expect (projection_assertion P) output.
  have H := Vc (CQState.point s rho).
  by move: H; rewrite expect_point /mask Ep comp_lfun1l.
have Hexp : expect (projection_assertion P) output <= CQState.mass output.
  by rewrite CQState.mass_trace; apply: expect_le_trace.
have Hmass : CQState.mass output <= \Tr rho.
  rewrite -(CQState.point_mass s rho); exact: CQKernel.apply_mass.
have EM : CQState.mass output = \Tr rho.
  by apply/eqP; rewrite eq_le Hmass (le_trans Hfirst Hexp).
have ES : expect (projection_assertion P) output = CQState.mass output.
  by apply/eqP; rewrite eq_le Hexp EM Hfirst.
have EV := saturated_expectation ES HM.
have Hsecond := Vd output.
by move: Hsecond; rewrite EV EM.
Qed.

Theorem derives_probcomp_projection (p : pred cmem) (P : cmem -> {hspace Hq})
    (M R Q : assertion) (a : C) c d :
  (forall s, (R s : 'End(Hq)) = if p s then a *: \1 else 0) ->
  (forall s, P s \o M s \o P s = a *: (P s : 'End(Hq))) ->
  derives true (mask p semantic_top) c (projection_assertion P) ->
  derives true M d Q -> derives true R (Sequence c d) Q.
Proof.
move=>RE HM /derives_sound Vc /derives_sound Vd; apply: derives_complete.
exact: valid_probcomp_projection RE HM Vc Vd.
Qed.
End Rule.

End CQProbabilisticComposition.
