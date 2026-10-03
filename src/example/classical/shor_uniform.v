(* The actual printed Random command conditioned on coprimality.
   See SHOR-UNIFORM-NOTES.md. *)
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
From quantum.example.classical Require Import language shor_crt shor_program
  shor_counting shor_sample_event shor_probability.
Import GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module ClassicalShorUniform.
Import ClassicalShorCRT ClassicalShorProgram ClassicalLanguage
  ClassicalShorCounting ClassicalShorSampleEvent ClassicalShorProbability.
Local Notation C := hermitian.C.
Section Uniform.
Variable N : nat.
Hypothesis HN : 1 < N.

Lemma unit_value_positive (u : {unit 'Z_N}) : 0 < unit_value u.
Proof.
case E: (unit_value u)=>[|a] //.
by have := unit_value_coprime HN u; rewrite E /coprime gcdn0 (gtn_eqF HN).
Qed.

Lemma sample_index_bound (u : {unit 'Z_N}) : (unit_value u).-1 < N.-1.
Proof.
rewrite -ltnS !prednK ?unit_value_positive ?(ltnW HN) //.
exact: unit_value_lt.
Qed.

Definition sample_index (u : {unit 'Z_N}) : 'I_N.-1 := Ordinal (sample_index_bound u).

Lemma sample_index_value u : (val (sample_index u)).+1 = unit_value u.
Proof. by rewrite /= prednK ?unit_value_positive. Qed.

Definition sampled_unit (i : 'I_N.-1) : {unit 'Z_N} :=
  insubd (1%g : {unit 'Z_N}) ((val i).+1%:R : 'Z_N)%R.

Lemma sampled_value_bound (i : 'I_N.-1) : (val i).+1 < N.
Proof. by rewrite -ltn_predRL; exact: ltn_ord. Qed.

Lemma sampled_unit_value (i : 'I_N.-1) : coprime N (val i).+1 ->
  unit_value (sampled_unit i) = (val i).+1.
Proof.
move=>Hi; rewrite /sampled_unit /unit_value val_insubd.
rewrite unitZpE // Hi.
change (((val i).+1%:R : 'Z_N)%R = (val i).+1 :> nat).
by rewrite val_Zp_nat // modn_small ?sampled_value_bound.
Qed.

Lemma sampled_unitK : cancel sample_index sampled_unit.
Proof.
move=>u; apply: unit_value_inj.
by rewrite sampled_unit_value sample_index_value ?unit_value_coprime // sample_index_value unit_value_coprime.
Qed.

Lemma sample_indexK (i : 'I_N.-1) : coprime N (val i).+1 ->
  sample_index (sampled_unit i) = i.
Proof. by move=>Hi; apply/val_inj; rewrite /= sampled_unit_value. Qed.

Local Open Scope ring_scope.

Lemma sample_unit_reindex (P : pred nat) (F : nat -> C) :
  \sum_(i : 'I_N.-1 | coprime N (val i).+1 && P (val i).+1) F (val i).+1 =
  \sum_(u : {unit 'Z_N} | P (unit_value u)) F (unit_value u).
Proof.
have Hcan i : coprime N (val i).+1 && P (val i).+1 ->
    sample_index (sampled_unit i) = i.
  by move=>/andP[Hi _]; exact: sample_indexK.
rewrite (reindex_onto sample_index sampled_unit Hcan).
apply: eq_big=>u; rewrite sample_index_value ?unit_value_coprime ?sampled_unitK ?eqxx ?andbT //.
Qed.

Definition coprime_event_probability s (P : pred nat) : C :=
  \sum_(i : 'I_N.-1 | coprime N (val i).+1 && P (val i).+1)
    probability_mass (uniform_probability HN) s (val i).+1.

Lemma coprime_event_probabilityE s P : coprime_event_probability s P =
  (#|[pred u : {unit 'Z_N} | P (unit_value u)]|%:R : C) / N.-1%:R.
Proof.
rewrite /coprime_event_probability sample_unit_reindex.
transitivity (\sum_(u : {unit 'Z_N} | P (unit_value u)) (N.-1%:R : C)^-1).
  apply: eq_bigr=>u _; rewrite uniform_probabilityE unit_value_positive unit_value_lt //.
by rewrite sumr_const -[X in X = _]mulr_natr mulrC.
Qed.

Definition conditional_probability s (P : pred nat) : C :=
  coprime_event_probability s P / coprime_event_probability s predT.

Lemma unit_card_positive : (0 < #|{: {unit 'Z_N}}|)%N.
Proof. apply/card_gt0P; by exists 1%g. Qed.

Lemma conditioning_probability_positive s : 0 < coprime_event_probability s predT.
Proof.
rewrite coprime_event_probabilityE.
apply: divr_gt0; rewrite ltr0n; first exact: unit_card_positive.
by rewrite ltn_predRL.
Qed.

Theorem conditional_probabilityE s P : conditional_probability s P =
  (#|[pred u : {unit 'Z_N} | P (unit_value u)]|%:R : C) / #|{: {unit 'Z_N}}|%:R.
Proof.
rewrite /conditional_probability !coprime_event_probabilityE.
have Hd : (N.-1%:R : C) != 0 by rewrite pnatr_eq0 -lt0n; case: N HN=>[|[|n]].
by rewrite invf_div mulrA mulfVK.
Qed.

Theorem random_conditional_success_bound s : odd N ->
  1 - 1 / ((2 ^ (size (primes N)).-1)%N)%:R <=
  conditional_probability s (natural_success N).
Proof.
move=>Hodd; rewrite conditional_probabilityE.
have Eg : #|[pred u : {unit 'Z_N} | natural_success N (unit_value u)]| =
    #|@unit_success N|.
  apply: eq_card=>u; exact: (@natural_success_unit N HN u).
have Et : #|{: {unit 'Z_N}}| = totient N.
  by rewrite -cardsT -/(units_Zp N) card_units_Zp //; exact: ltnW HN.
rewrite Eg Et.
exact: uniform_unit_success_bound HN Hodd.
Qed.

End Uniform.
End ClassicalShorUniform.
