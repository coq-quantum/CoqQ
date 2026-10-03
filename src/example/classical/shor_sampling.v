(* The actual sampler partition and scalar Equation (21).
   See SHOR-SAMPLING-NOTES.md for the prior argument. *)
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
From quantum.example.classical Require Import language shor_program
  shor_sample_event shor_probability shor_uniform.
Import Order.LTheory GRing.Theory Num.Def Num.Theory Summable.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module ClassicalShorSampling.
Import ClassicalLanguage ClassicalShorProgram ClassicalShorSampleEvent
  ClassicalShorProbability ClassicalShorUniform.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.

Section Sampling.
Variable N : nat.
Hypothesis HN : (1 < N)%N.

Lemma gcd_guard_complement a : (0 < a)%N ->
  (1 < gcdn a N)%N = ~~ coprime N a.
Proof.
move=>Ha.
have Hg : (0 < gcdn a N)%N by rewrite gcdn_gt0 Ha.
by rewrite ltn_neqAle Hg andbT /coprime gcdnC eq_sym.
Qed.

Theorem sampling_partition s :
  direct_probability N + coprime_event_probability HN s predT = 1.
Proof.
rewrite /direct_probability /direct_ordinal_weights fin_dom_sum /=.
rewrite /coprime_event_probability [X in _ + X]big_mkcond.
rewrite -big_split.
transitivity (\sum_(i : 'I_N.-1) (N.-1%:R : C)^-1).
  apply: eq_bigr=>i _.
  rewrite uniform_probabilityE ltn0Sn sampled_value_bound //=.
  rewrite gcd_guard_complement //.
  by case: (coprime N (val i).+1); rewrite ?addr0 ?add0r.
rewrite sumr_const card_ord -[X in X = 1]mulr_natr mulVf // pnatr_eq0.
by case: N HN=>[|[|n]].
Qed.

Lemma coprime_probability_complement s :
  coprime_event_probability HN s predT = 1 - direct_probability N.
Proof. by rewrite -(sampling_partition s) addrAC subrr add0r. Qed.

Theorem sampling_mixture_bound s (p : C) :
  odd N -> 0 <= p -> p <= 1 ->
  p * (1 - 1 / ((2 ^ (size (primes N)).-1)%N)%:R) <=
  direct_probability N +
    p * coprime_event_probability HN s (natural_success N).
Proof.
move=>Hodd Hp0 Hp1.
pose d := (2 ^ (size (primes N)).-1)%N.
have Hd : (0 : C) < d%:R by rewrite ltr0n /d expn_gt0.
have Hd1 : (1 : C) <= d%:R by rewrite ler1n /d expn_gt0.
have Hc0 : (0 : C) <= 1 - 1 / d%:R.
  by rewrite subr_ge0 ler_pdivrMr // mul1r.
have Hc1 : (1 - 1 / d%:R : C) <= 1.
  rewrite lerBlDr lerDl; apply: divr_ge0; by rewrite ?ler01 ?ler0n.
have Hcond := random_conditional_success_bound HN s Hodd.
rewrite /conditional_probability ler_pdivlMr
  ?conditioning_probability_positive // in Hcond.
have Hprod : (1 - direct_probability N) * (1 - 1 / d%:R) <=
    coprime_event_probability HN s (natural_success N).
  by rewrite -(coprime_probability_complement s) mulrC.
have Hmix := mixture_lower_bound (@direct_probability_ge0 N) Hp0 Hp1 Hc0 Hc1.
apply: le_trans Hmix _.
rewrite lerD2l.
by apply: ler_wpM2l.
Qed.

End Sampling.
End ClassicalShorSampling.
