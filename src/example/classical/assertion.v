(* Classical: assertion. See README.md and PROOF_NOTES.md. *)
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
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology.
From quantum Require Import hermitian cpo quantum summable.
From quantum Require Import hermitian quantum summable.
From quantum Require Import cpo.
From quantum.example.classical Require Import language state.
Module CQAssertion.
(* Classical-quantum assertions and expectation, following Feng and Ying,
   Definitions 3.5 and 3.7. See PROOF_NOTES.md and README.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
(* Approved domain repair, 2026-10-03: limits use all effect-valued
   functions; the paper's countable/definable assertions remain below. *)
Section SemanticAssertions.
Context {I : choiceType} {H : chsType}.

Definition semantic_assertion := I -> 'FO(H).
Definition semantic_le (P Q : semantic_assertion) :=
  forall i, (P i : 'End(H)) ⊑ (Q i : 'End(H)).
Definition semantic_bottom : semantic_assertion := fun _ => (0%:VF : 'FO(H)).
Definition semantic_top : semantic_assertion := fun _ => (\1 : 'FO(H)).
Definition semantic_chain (c : nat -> semantic_assertion) :=
  forall n, semantic_le (c n) (c n.+1).
Definition semantic_sup (c : nat -> semantic_assertion) : semantic_assertion :=
  fun i => LfunCPO.oflub (fun n => c n i).

Lemma semantic_le_refl P : semantic_le P P.
Proof. by move=>i. Qed.

Lemma semantic_le_trans P Q R :
  semantic_le P Q -> semantic_le Q R -> semantic_le P R.
Proof. by move=>PQ QR i; exact: le_trans (PQ i) (QR i). Qed.

Lemma semantic_le_anti P Q : semantic_le P Q -> semantic_le Q P -> P = Q.
Proof.
move=>PQ QP; apply/funext=>i; apply/val_inj/le_anti/andP.
by split; [apply: PQ | apply: QP].
Qed.

Lemma semantic_bottom_le P : semantic_le semantic_bottom P.
Proof. by move=>i; apply: obsf_ge0. Qed.

Lemma semantic_le_top P : semantic_le P semantic_top.
Proof. by move=>i; apply: obsf_le1. Qed.

Lemma semantic_point_chain c : semantic_chain c ->
  forall i, chain (fun n => c n i).
Proof. by move=>inc i n; rewrite leEsub; apply: inc. Qed.

Lemma semantic_sup_upper c : semantic_chain c ->
  forall n, semantic_le (c n) (semantic_sup c).
Proof.
move=>inc n i; move: (LfunCPO.oflub_ub (semantic_point_chain inc i) n).
by rewrite leEsub.
Qed.

Lemma semantic_sup_least c Q : semantic_chain c ->
  (forall n, semantic_le (c n) Q) -> semantic_le (semantic_sup c) Q.
Proof.
move=>inc bound i.
have B : forall n, c n i ⊑ Q i by move=>n; rewrite leEsub; apply: bound.
move: (LfunCPO.oflub_least (semantic_point_chain inc i) B).
by rewrite leEsub.
Qed.

Theorem semantic_omega_cpo :
  (forall P, semantic_le semantic_bottom P) /\
  (forall c, semantic_chain c ->
    (forall n, semantic_le (c n) (semantic_sup c)) /\
    (forall Q, (forall n, semantic_le (c n) Q) -> semantic_le (semantic_sup c) Q)).
Proof.
split; first exact: semantic_bottom_le.
move=>c inc; split.
  exact: semantic_sup_upper inc.
by move=>Q bound; exact: semantic_sup_least inc bound.
Qed.

End SemanticAssertions.

Section Assertions.
Context {I : choiceType} {H : chsType}.
Variable (Formula : Type) (holds : Formula -> I -> Prop).

Record assertion := Assertion {
  assertion_value : I -> 'FO(H);
  assertion_countable :
    countable [set A | exists i, assertion_value i = A];
  assertion_definable : forall A,
    (exists i, assertion_value i = A) ->
    exists p, forall i, holds p i <-> assertion_value i = A
}.

Coercion assertion_value : assertion >-> Funclass.

Definition assertion_le (P Q : assertion) :=
  forall i, (P i : 'End(H)) ⊑ (Q i : 'End(H)).

Lemma assertion_le_refl (P : assertion) : assertion_le P P.
Proof. by move=>i. Qed.

Lemma assertion_le_trans (P Q R : assertion) :
  assertion_le P Q -> assertion_le Q R -> assertion_le P R.
Proof. by move=>PQ QR i; apply: (le_trans (PQ i) (QR i)). Qed.

End Assertions.

Section Expectation.
Context {I : choiceType} {H : chsType}.
Implicit Type (P Q : I -> 'FO(H)) (rho : {vdistr I -> 'End(H)}).

Definition expect_term P rho i := \Tr (P i \o rho i).

Lemma expect_term_ge0 P rho i : 0 <= expect_term P rho i.
Proof. by apply/trlfM_ge0; [apply: obsf_ge0 | apply: vdistr_ge0]. Qed.

Lemma expect_term_le_trace P rho i : expect_term P rho i <= \Tr (rho i).
Proof.
rewrite /expect_term -{2}(comp_lfun1l (rho i)).
apply/(lef_psdtr (P i) (\1)); first apply: obsf_le1.
by rewrite psdlfE; apply: vdistr_ge0.
Qed.

Lemma expect_term_norm_le P rho i : `|expect_term P rho i| <= `|rho i|.
Proof.
rewrite ger0_norm ?expect_term_ge0// psd_trfnorm.
by rewrite psdlfE; apply: vdistr_ge0.
apply: expect_term_le_trace.
Qed.

Lemma expect_summable P rho : summable (expect_term P rho).
Proof.
apply: psum_ubounded_summable.
move: (summable_bounded (rho : {summable I -> 'End(H)}))=>[M _ BM].
exists M=>J; apply: (le_trans _ (BM J)).
by rewrite /psum; apply: ler_sum=>i _; apply: expect_term_norm_le.
Qed.

Definition expect P rho : C := sum (expect_term P rho).

Lemma expect_ge0 P rho : 0 <= expect P rho.
Proof.
rewrite /expect /sum; apply: etlim_ge.
exact: (summable_cvg (f := Summable.build (expect_summable P rho))).
by move=>J; rewrite /psum; apply: sumr_ge0=>i _; apply: expect_term_ge0.
Qed.

Lemma expect_le_trace P rho : expect P rho <= \Tr (sum rho).
Proof.
rewrite /expect /sum; apply: etlim_le.
exact: (summable_cvg (f := Summable.build (expect_summable P rho))).
move=>J; apply: (le_trans (y := \Tr (psum rho J))).
rewrite /psum linear_sum/=; apply: ler_sum=>i _.
apply: expect_term_le_trace.
by apply/lef_trlf/psum_vdistr_lev_sum.
Qed.

Lemma expect_le1 P rho : expect P rho <= 1.
Proof.
apply: (le_trans (expect_le_trace P rho)).
rewrite -psd_trfnorm; first by rewrite psdlfE; apply: vdistr_sum_ge0.
apply: vdistr_sum_le1.
Qed.

Lemma expect_real P rho : expect P rho \is Num.real.
Proof. apply/ger0_real/expect_ge0. Qed.

Lemma expect_mono P Q rho :
  (forall i, (P i : 'End(H)) ⊑ (Q i : 'End(H))) ->
  expect P rho <= expect Q rho.
Proof.
move=>PQ; rewrite /expect /sum; apply: ler_etlim.
exact: (summable_cvg (f := Summable.build (expect_summable P rho))).
exact: (summable_cvg (f := Summable.build (expect_summable Q rho))).
move=>J; rewrite /psum; apply: ler_sum=>i _.
rewrite /expect_term; move: (PQ (val i))=>/lef_psdtr Pi; apply: Pi.
by rewrite psdlfE; apply: vdistr_ge0.
Qed.

Lemma expect_zero rho : expect (fun _ => (0%:VF : 'FO(H))) rho = 0.
Proof.
rewrite /expect /expect_term.
have -> : (fun i => \Tr (0%:VF \o rho i)) = (fun _ : I => (0 : C)).
  by apply/funext=>i; rewrite comp_lfun0l linear0.
apply: summable_sum_cst0.
Qed.

Lemma expect_identity rho :
  expect (fun _ => (\1 : 'FO(H))) rho = \Tr (sum rho).
Proof.
rewrite /expect /expect_term.
have -> : (fun i => \Tr (\1 \o rho i)) = (@lftrace H \o rho)%FUN.
  by apply/funext=>i; rewrite comp_lfun1l.
symmetry; apply: summable_linear_sumG.
exists 1; split=>// v; rewrite mul1r; apply: trlf_trfnorm.
Qed.

Lemma expect_singleton P rho i :
  (forall j, j != i -> rho j = 0) ->
  expect P rho = \Tr (P i \o rho i).
Proof.
move=>single; rewrite /expect (fin_supp_sum (S := [fset i]%fset)) ?psum1//.
by move=>j; rewrite inE=>/single rj; rewrite /expect_term rj comp_lfun0r linear0.
Qed.

Definition mask (b : pred I) P : I -> 'FO(H) :=
  fun i => if b i then P i else (0%:VF : 'FO(H)).

Definition conditional (b : pred I) P Q : I -> 'FO(H) :=
  fun i => if b i then P i else Q i.

Lemma expect_mask_le (b : pred I) P rho : expect (mask b P) rho <= expect P rho.
Proof.
apply: expect_mono=>i; rewrite /mask; case: (b i)=>//.
apply: obsf_ge0.
Qed.

Lemma expect_mask_true P rho : expect (mask predT P) rho = expect P rho.
Proof. by []. Qed.

Lemma expect_mask_false P rho : expect (mask pred0 P) rho = 0.
Proof. exact: expect_zero. Qed.

Lemma expect_conditional (b : pred I) P Q rho :
  expect (conditional b P Q) rho =
    expect (mask b P) rho + expect (mask (predC b) Q) rho.
Proof.
rewrite /expect -(summable_sumD
  (Summable.build (expect_summable (mask b P) rho))
  (Summable.build (expect_summable (mask (predC b) Q) rho))).
congr (sum _); apply/funext=>i.
by rewrite /= /expect_term /conditional /mask /=;
  case: (b i); rewrite comp_lfun0l linear0 ?add0r ?addr0.
Qed.

Definition complement P : I -> 'FO(H) :=
  fun i => ObsLf_Build (cplmt_obs (P i)).

Lemma expect_complement_sum P rho :
  expect (complement P) rho + expect P rho = \Tr (sum rho).
Proof.
rewrite -(expect_identity rho) /expect -(summable_sumD
  (Summable.build (expect_summable (complement P) rho))
  (Summable.build (expect_summable P rho))).
congr (sum _); apply/funext=>i.
by rewrite /= /expect_term /complement /= /cplmt
  linearBl /= linearB /= subrK.
Qed.

Lemma expect_complement P rho :
  expect (complement P) rho = \Tr (sum rho) - expect P rho.
Proof. by rewrite -(expect_complement_sum P rho) addrK. Qed.

End Expectation.
End CQAssertion.


Module CQAssertionAlgebra.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import CQAssertion.
Section Algebra.
Context {I : choiceType} {H : chsType}.
Local Notation C := hermitian.C.

Lemma expect_finite_linear (J : finType) (w : J -> C)
    (F : J -> I -> 'FO(H)) (P : I -> 'FO(H))
    (rho : @CQState.state I H) :
  (forall i, (P i : 'End(H)) = \sum_j w j *: (F j i : 'End(H))) ->
  expect P rho = \sum_j w j * expect (F j) rho.
Proof.
move=>PE.
pose terms j := w j *: Summable.build (expect_summable (F j) rho).
have E : expect_term P rho = (\sum_j terms j : {summable I -> C}).
  apply/funext=>i; rewrite summable_sumE /expect_term PE linear_sumlz /= linear_sum /=.
  apply: eq_bigr=>j _; rewrite /terms /= /expect_term.
  by rewrite linearZl /= linearZ /=.
rewrite /expect E summable_sum_sum.
apply: eq_bigr=>j _; by rewrite /terms summable_sumZ.
Qed.

Lemma mask_le (p : pred I) (P Q : I -> 'FO(H)) :
  semantic_le P Q -> semantic_le (mask p P) (mask p Q).
Proof. by move=>PQ i; rewrite /mask; case: (p i)=>//; apply: PQ. Qed.

Lemma mask_or_le (p q : pred I) (P Q : I -> 'FO(H)) :
  semantic_le (mask p P) Q -> semantic_le (mask q P) Q ->
  semantic_le (mask (predU p q) P) Q.
Proof.
move=>pQ qQ i.
change (((if p i || q i then P i else (0%:VF : 'FO(H))) : 'End(H)) ⊑ Q i).
case Ep: (p i)=>/=.
- by move: (pQ i); rewrite /mask Ep.
- case Eq: (q i)=>/=; last exact: obsf_ge0.
  by move: (qQ i); rewrite /mask Eq.
Qed.

Lemma mask_disjoint_sum_le (p q : pred I) (P Q R S : I -> 'FO(H)) :
  (forall i, q i -> ~~ p i) ->
  (forall i, (S i : 'End(H)) = (mask p P i : 'End(H)) + (mask q Q i : 'End(H))) ->
  semantic_le (mask p P) R -> semantic_le (mask q Q) R -> semantic_le S R.
Proof.
move=>disj SE pR qR i; rewrite SE /mask.
case Eq: (q i).
- have Ep : p i = false := negPf (disj i Eq).
  rewrite Ep add0r; by move: (qR i); rewrite /mask Eq.
- rewrite addr0; by move: (pR i); rewrite /mask.
Qed.

End Algebra.
End CQAssertionAlgebra.


Module CQExpectation.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import CQAssertion.
Section Pairing.
Context {I : choiceType} {H : chsType}.
Local Notation C := hermitian.C.

Lemma expect_point (P : I -> 'FO(H)) i (rho : 'FD(H)) :
  expect P (CQState.point i rho) = \Tr (P i \o rho).
Proof.
rewrite (@expect_singleton I H P (CQState.point i rho) i).
  by move=>j /negPf ji; rewrite CQState.pointE ji.
by rewrite CQState.pointE eqxx.
Qed.

Lemma semantic_le_iff_expect (P Q : I -> 'FO(H)) :
  semantic_le P Q <-> forall rho : @CQState.state I H,
    expect P rho <= expect Q rho.
Proof.
split; first by move=>PQ rho; apply: expect_mono.
move=>PQ i; apply/lef_trden=>r.
by move: (PQ (CQState.point i r)); rewrite !expect_point.
Qed.

Lemma trace_pair_bound (P : 'FO(H)) (x : 'End(H)) :
  `|\Tr (P \o x)| <= `|x|.
Proof.
apply: (le_trans (trlf_trfnorm _)).
apply: (le_trans (trfnormMr _ _)).
rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
exact: bound1f_i2fnorm.
Qed.

Definition pair_term (P : I -> 'FO(H)) (x : {summable I -> 'End(H)}) i :=
  \Tr (P i \o x i).

Lemma pair_term_summable P x : summable (pair_term P x).
Proof.
apply: psum_ubounded_summable.
move: (summable_bounded x)=>[M _ BM].
exists M=>J; apply: (le_trans _ (BM J)).
by rewrite /psum; apply: ler_sum=>i _; apply: trace_pair_bound.
Qed.

Definition pair_terms P x := Summable.build (pair_term_summable P x).
Definition pairing P x := sum (pair_terms P x).

Lemma pair_termsB P x y : pair_terms P (x-y) = pair_terms P x - pair_terms P y.
Proof.
apply/summableP=>i; rewrite summableE /= /pair_term summableE.
by rewrite linearBr /= linearB.
Qed.

Lemma pair_terms_norm P x : `|pair_terms P x| <= `|x|.
Proof.
change (summable_norm (pair_terms P x) <= summable_norm x).
rewrite /summable_norm; apply: ler_etlim.
- exact: summable_norm_is_cvg.
- exact: summable_norm_is_cvg.
- move=>J; rewrite /psum; apply: ler_sum=>i _.
  exact: trace_pair_bound.
Qed.

Lemma pairing_bound P x : `|pairing P x| <= `|x|.
Proof.
apply: (le_trans (summable_sum_ler_norm _)).
change (summable_norm (pair_terms P x) <= summable_norm x).
exact: pair_terms_norm.
Qed.

Lemma pairingB P x y : pairing P (x-y) = pairing P x - pairing P y.
Proof. by rewrite /pairing pair_termsB summable_sumB. Qed.

Lemma pairing_continuous P : continuous (pairing P).
Proof.
move=>x s /= /nbhs_ballP [e egt0 Pb]; apply/nbhs_ballP.
exists e=>// y /= Py; apply: Pb; move: Py.
rewrite -!ball_normE /= -pairingB; apply: le_lt_trans.
exact: pairing_bound.
Qed.

Lemma expect_pairing P (rho : @CQState.state I H) :
  expect P rho = pairing P (rho : {summable I -> 'End(H)}).
Proof. by []. Qed.

Lemma expect_cvg P (f : nat -> @CQState.state I H) (rho : @CQState.state I H) :
  (f n : {summable I -> 'End(H)}) @[n --> \oo] -->
    (rho : {summable I -> 'End(H)}) ->
  expect P (f n) @[n --> \oo] --> expect P rho.
Proof.
move=>Cf; change (pairing P (f n) @[n --> \oo] --> pairing P rho).
apply: continuous_cvg; first exact: pairing_continuous.
exact: Cf.
Qed.

Lemma expect_chain_sup P (f : nat -> @CQState.state I H) :
  nondecreasing_seq f ->
  expect P (f n) @[n --> \oo] --> expect P (CQState.chain_sup f).
Proof.
move=>inc; apply: expect_cvg.
rewrite /CQState.chain_sup vdlimE; exact: CQState.chain_converges.
Qed.
End Pairing.
End CQExpectation.


Module CQAssertionExamples.
(* Checked assertion examples over unbounded natural-number memory. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import CQAssertion.

(* A small, explicit classical formula language, with unbounded memories. *)
Inductive formula :=
| constant of bool
| is_zero
| negate of formula
| conjunction of formula & formula
| disjunction of formula & formula.

Fixpoint eval (p : formula) (n : nat) : bool :=
  match p with
  | constant b => b
  | is_zero => n == 0%N
  | negate p => ~~ eval p n
  | conjunction p q => eval p n && eval q n
  | disjunction p q => eval p n || eval q n
  end.

Section ZeroTest.
Variable (H : chsType) (M : 'FO(H)).

Definition zero_test_value (n : nat) :=
  if n == 0%N then M else (0%:VF : 'FO(H)).

Lemma zero_test_countable :
  countable [set A | exists n, zero_test_value n = A].
Proof.
apply: (sub_countable (B := [set M; (0%:VF : 'FO(H))])).
  apply: subset_card_le=>A [n <-]; rewrite /zero_test_value.
  by case: ifP=>_; [left | right].
apply/finite_set_countable/finite_set2.
Qed.

Lemma zero_test_definable A :
  exists p, forall n, eval p n <-> zero_test_value n = A.
Proof.
exists (disjunction
  (conjunction is_zero (constant (M == A)))
  (conjunction (negate is_zero) (constant ((0%:VF : 'FO(H)) == A)))).
move=>n; rewrite /= /zero_test_value.
by case: (n == 0%N); rewrite /= ?orbF; split=>/eqP.
Qed.

Definition zero_test_assertion :
  @CQAssertion.assertion _ H formula (fun p (n : nat) => eval p n) :=
  @CQAssertion.Assertion _ H formula (fun p (n : nat) => eval p n)
    zero_test_value zero_test_countable (fun A _ => zero_test_definable A).

Example zero_test_at_zero : zero_test_assertion 0%N = M.
Proof. by []. Qed.

Example zero_test_at_successor n : zero_test_assertion n.+1 = (0%:VF : 'FO(H)).
Proof. by []. Qed.

Example zero_test_expectation_bound (rho : {vdistr nat -> 'End(H)}) :
  0 <= expect zero_test_assertion rho <= 1.
Proof. by rewrite expect_ge0 expect_le1. Qed.

Example zero_test_single_memory (rho : {vdistr nat -> 'End(H)}) :
  (forall n, n != 0%N -> rho n = 0) ->
  expect zero_test_assertion rho = \Tr (M \o rho 0%N).
Proof. exact: expect_singleton. Qed.

Example empty_guard_expectation (rho : {vdistr nat -> 'End(H)}) :
  expect (mask pred0 zero_test_assertion) rho = 0.
Proof. exact: expect_mask_false. Qed.

Example full_guard_expectation (rho : {vdistr nat -> 'End(H)}) :
  expect (mask predT (fun _ => (\1 : 'FO(H)))) rho = \Tr (sum rho).
Proof. by rewrite expect_mask_true expect_identity. Qed.

End ZeroTest.
End CQAssertionExamples.


Module CQAssertionSeries.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import CQAssertion.
Local Notation C := hermitian.C.

Lemma positive_partial_sum (J : choiceType) (H : chsType)
    (f : J -> 'End(H)) :
  summable f -> (forall j, 0%:VF ⊑ f j) ->
  forall A, psum f A ⊑ sum f.
Proof.
move=>sf pf A; apply: lim_gev_near; first exact: norm_bounded_cvg sf.
exists A=>// B /= AB.
rewrite -(fsetUD_sub AB) psumU ?fdisjointXD // levDl.
by apply: sumv_ge0=>j _; apply: pf.
Qed.

Section Series.
Context {I J : choiceType} {H : chsType}.
Variable (w : J -> C) (F : J -> I -> 'FO(H)) (P : I -> 'FO(H)).
Hypothesis w_positive : forall j, 0 <= w j.
Hypothesis series_summable : forall i, summable (fun j => w j *: (F j i : 'End(H))).
Hypothesis series_value : forall i,
  (P i : 'End(H)) = sum (fun j => w j *: (F j i : 'End(H))).
Variable (rho : @CQState.state I H).

Definition series_term i j := w j * expect_term (F j) rho i.

Lemma series_term_positive i j : 0 <= series_term i j.
Proof. by apply: mulr_ge0; [apply: w_positive | apply: expect_term_ge0]. Qed.

Lemma series_partial_bound i A :
  psum (fun j => w j *: (F j i : 'End(H))) A ⊑ (P i : 'End(H)).
Proof.
rewrite series_value; apply: positive_partial_sum; first exact: series_summable.
by move=>j; apply: scalev_ge0; [apply: w_positive | apply: obsf_ge0].
Qed.

Lemma series_row_bound i A : psum (fun j => `|series_term i j|) A <= `|rho i|.
Proof.
rewrite /psum.
under eq_bigr do rewrite ger0_norm ?series_term_positive //.
rewrite /series_term /expect_term.
have E j : w j * \Tr (F j i \o rho i) = \Tr ((w j *: (F j i : 'End(H))) \o rho i).
  by rewrite linearZl /= linearZ.
under eq_bigr do rewrite E.
rewrite -linear_sum /= -linear_sumlz /=.
apply: (le_trans (y := expect_term P rho i)).
- apply/(lef_psdtr _ _); first exact: series_partial_bound.
  by rewrite psdlfE vdistr_ge0.
- apply: (le_trans (expect_term_le_trace P rho i)).
  by rewrite psd_trfnorm ?psdlfE ?vdistr_ge0.
Qed.

Lemma series_rectangle : exists B, forall A N,
  psum (fun i => psum (fun j => `|series_term i j|) N) A <= B.
Proof.
exists `|rho : {summable I -> 'End(H)}|=>A N.
apply: (le_trans _ (psum_norm_ler_norm rho A)).
by apply: ler_sum=>i _; apply: series_row_bound.
Qed.

Lemma series_row_value i : sum (series_term i) = expect_term P rho i.
Proof.
rewrite /expect_term series_value /series_term /expect_term.
rewrite (cvg_linearP_sum (f := fun A : 'End(H) => \Tr (A \o rho i))).
- by move=>a x y; rewrite linearPl /= linearP.
- by apply: norm_bounded_cvg; apply: series_summable.
- by apply: eq_sum=>j; rewrite /= linearZl /= linearZ.
Qed.

Lemma series_column_value j : sum (fun i => series_term i j) = w j * expect (F j) rho.
Proof.
change (sum (w j *: Summable.build (expect_summable (F j) rho)) = w j * expect (F j) rho).
by rewrite summable_sumZ.
Qed.

Lemma expect_series : expect P rho = sum (fun j => w j * expect (F j) rho).
Proof.
have E : expect_term P rho = fun i => sum (series_term i).
  by apply/funext=>i; rewrite series_row_value.
rewrite /expect E (pseries2_exchange_lim series_rectangle).
by apply: eq_sum=>j; rewrite series_column_value.
Qed.

Lemma expect_series_summable : summable (fun j => w j * expect (F j) rho).
Proof.
have B : exists B, forall N A,
    psum (fun j => psum (fun i => `|series_term i j|) A) N <= B.
  move: series_rectangle=>[B HB]; exists B=>N A.
  by rewrite /psum exchange_big; apply: HB.
have S := proj1 (proj2 (proj2 (pseries_ubounded_cvg B))).
have E : (fun j => sum (fun i => series_term i j)) = fun j => w j * expect (F j) rho.
  by apply/funext=>j; rewrite series_column_value.
by rewrite E in S.
Qed.
End Series.
End CQAssertionSeries.


Module CQMixtureExpectation.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import CQAssertion CQExpectation.
Section Mixtures.
Context {I J : choiceType} {H : chsType}.
Variable P : J -> 'FO(H).

Lemma pairing_linear : linear (@pairing J H P).
Proof.
move=>a x y.
have E : pair_terms P (a *: x + y) = a *: pair_terms P x + pair_terms P y.
  apply/summableP=>i; rewrite !summableE /= /pair_term !summableE.
  by rewrite linearPr /= linearP.
by rewrite /pairing E summable_sumD summable_sumZ.
Qed.

HB.instance Definition _ := GRing.isLinear.Build C
  {summable J -> 'End(H)} C *:%R (@pairing J H P) pairing_linear.

Lemma expect_mix (w : Distr I) (d : I -> @CQState.state J H) :
  expect P (CQStateMixture.mix w d) = sum (fun i => w i * expect P (d i)).
Proof.
change (pairing P (sum (CQStateMixture.terms w d)) =
  sum (fun i => w i * expect P (d i))).
have B : exists k : C, 0 < k /\ forall x : {summable J -> 'End(H)},
  `|pairing P x| <= k * `|x|.
  exists 1; split=>// x; rewrite mul1r; exact: pairing_bound.
rewrite (summable_linear_sumG (f := pairing P) (CQStateMixture.terms w d) B).
apply: eq_sum=>i.
by rewrite /CQStateMixture.terms /= /CQStateMixture.term linearZ /= -expect_pairing.
Qed.
End Mixtures.
End CQMixtureExpectation.


Module CQExpectationLimits.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import CQAssertion CQExpectation.
Section Limits.
Context {I : choiceType} {H : chsType}.
Local Notation C := hermitian.C.

Lemma scalar_norm_add (x y : C) :
  0 <= x -> 0 <= y -> `|x+y| = `|x| + `|y|.
Proof. by move=>Hx Hy; rewrite !ger0_norm ?addr_ge0. Qed.

Lemma effect_sup_cvg (f : nat -> 'FO(H)) : chain f ->
  (f n : 'End(H)) @[n --> \oo] --> (LfunCPO.oflub f : 'End(H)).
Proof.
move=>inc.
have Cf := vnondecreasing_is_cvgn (LfunCPO.chainof2f inc)
  (LfunCPO.chainof_ub f).
rewrite /LfunCPO.oflub; case: eqP=>P.
- exact: Cf.
- exfalso; apply: P; exact: LfunCPO.limn_obslf Cf.
Qed.

Lemma semantic_sup_cvg (f : nat -> I -> 'FO(H)) : semantic_chain f ->
  forall i, (f n i : 'End(H)) @[n --> \oo] --> (semantic_sup f i : 'End(H)).
Proof. move=>inc i; apply: effect_sup_cvg; exact: semantic_point_chain. Qed.

Lemma expect_semantic_sup (f : nat -> I -> 'FO(H))
    (rho : @CQState.state I H) : semantic_chain f ->
  expect (f n) rho @[n --> \oo] --> expect (semantic_sup f) rho.
Proof.
move=>inc.
pose a := fun n => pair_terms (f n) (rho : {summable I -> 'End(H)}).
pose b := pair_terms (semantic_top : I -> 'FO(H)) (rho : {summable I -> 'End(H)}).
have ia : nondecreasing_seq a.
  move=>m n mn; apply/lesP=>i.
  change (\Tr (f m i \o rho i) <= \Tr (f n i \o rho i)).
  apply/(lef_psdtr (f m i) (f n i)); last by rewrite psdlfE vdistr_ge0.
  exact: (LfunCPO.chainof2f (semantic_point_chain inc i) mn).
have ab : ubounded_by b a.
  move=>n; apply/lesP=>i.
  change (\Tr (f n i \o rho i) <= \Tr (\1 \o rho i)).
  apply/(lef_psdtr (f n i) (\1)); first exact: obsf_le1.
  by rewrite psdlfE vdistr_ge0.
have Ca : cvgn a := snondecreasing_is_cvgn scalar_norm_add ia ab.
have E : limn a = pair_terms (semantic_sup f) (rho : {summable I -> 'End(H)}).
  apply/summableP=>i.
  have C2 : a n i @[n --> \oo] --> \Tr (semantic_sup f i \o rho i).
    change (\Tr (f n i \o rho i) @[n --> \oo] -->
      \Tr (semantic_sup f i \o rho i)).
    apply: continuous_cvg; first exact: trlf_continuous.
    apply: lfun_comp_cvgl; exact: semantic_sup_cvg inc i.
  rewrite -summableE_lim //.
  exact (cvg_lim (@norm_hausdorff _ _) C2).
have Csum := summable_sum_cvg Ca.
rewrite E in Csum; exact: Csum.
Qed.

Definition semantic_decreasing (f : nat -> I -> 'FO(H)) :=
  forall n, semantic_le (f n.+1) (f n).
Definition semantic_inf (f : nat -> I -> 'FO(H)) :=
  complement (semantic_sup (fun n => complement (f n))).

Lemma complement_involutive (P : I -> 'FO(H)) :
  complement (complement P) = P.
Proof.
by apply/funext=>i; apply/val_inj; rewrite /complement /= cplmtK.
Qed.

Lemma complement_chain f : semantic_decreasing f ->
  semantic_chain (fun n => complement (f n)).
Proof. by move=>inc n i; rewrite /complement /= -cplmt_lef; apply: inc. Qed.

Lemma semantic_inf_cvg (f : nat -> I -> 'FO(H)) : semantic_decreasing f ->
  forall i, (f n i : 'End(H)) @[n --> \oo] --> (semantic_inf f i : 'End(H)).
Proof.
move=>dec i.
have Cc := semantic_sup_cvg (i := i) (complement_chain dec).
change ((fun n => (f n i : 'End(H))) @ \oo -->
  (\1 - (semantic_sup (fun n => complement (f n)) i : 'End(H))))%classic.
have E n : (f n i : 'End(H)) = \1 - (complement (f n) i : 'End(H)).
  by rewrite /complement /= -/(cplmt (cplmt (f n i))) cplmtK.
under eq_cvg do rewrite E.
apply: cvgB; first exact: cvg_cst.
exact: Cc.
Qed.

Lemma expect_semantic_inf (f : nat -> I -> 'FO(H))
    (rho : @CQState.state I H) : semantic_decreasing f ->
  expect (f n) rho @[n --> \oo] --> expect (semantic_inf f) rho.
Proof.
move=>dec; have Cc := expect_semantic_sup (rho := rho) (complement_chain dec).
rewrite /semantic_inf expect_complement.
have E n : expect (f n) rho = \Tr (sum rho) - expect (complement (f n)) rho.
  by rewrite expect_complement opprB addrCA subrr addr0.
under eq_cvg do rewrite E.
apply: cvgB; first exact: cvg_cst.
exact: Cc.
Qed.
End Limits.
End CQExpectationLimits.


Module CQStateExpectation.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import CQAssertion CQExpectation.
Section Separation.
Context {I : choiceType} {H : chsType}.

Definition at_store (i : I) (A : 'FO(H)) : I -> 'FO(H) :=
  fun j => if j == i then A else (0%:VF : 'FO(H)).

Lemma pairing_at_store (i : I) (A : 'FO(H)) (x : {summable I -> 'End(H)}) :
  pairing (at_store i A) x = \Tr (A \o x i).
Proof.
rewrite /pairing (fin_supp_sum (S := [fset i]%fset)).
- move=>j; rewrite inE=>/negPf ji.
  by rewrite /pair_terms /= /pair_term /at_store ji comp_lfun0l linear0.
- by rewrite psum1 /pair_terms /= /pair_term /at_store eqxx.
Qed.

Lemma expect_at_store (i : I) (A : 'FO(H)) (d : @CQState.state I H) :
  expect (at_store i A) d = \Tr (A \o d i).
Proof. exact: pairing_at_store. Qed.

Lemma expect_state_mono (P : I -> 'FO(H)) (d e : @CQState.state I H) :
  d ⊑ e -> expect P d <= expect P e.
Proof.
move=>/levdP Hde; rewrite /expect /sum; apply: ler_etlim.
- exact: (summable_cvg (f := Summable.build (expect_summable P d))).
- exact: (summable_cvg (f := Summable.build (expect_summable P e))).
- move=>J; rewrite /psum; apply: ler_sum=>i _.
  rewrite /expect_term ![\Tr (P _ \o _)]lftraceC.
  move: (Hde (val i))=>/lef_psdtr Htrace; apply: Htrace; exact: is_psdlf.
Qed.

Theorem state_le_iff_expect (d e : @CQState.state I H) :
  d ⊑ e <-> forall P : I -> 'FO(H), expect P d <= expect P e.
Proof.
split; first by move=>Hde P; exact: expect_state_mono Hde.
move=>Htest; apply/levdP=>i; apply/lef_trobs=>A.
by move: (Htest (at_store i A)); rewrite !expect_at_store (lftraceC A (d i)) (lftraceC A (e i)).
Qed.

Theorem state_eq_iff_expect (d e : @CQState.state I H) :
  d = e <-> forall P : I -> 'FO(H), expect P d = expect P e.
Proof.
split=>[-> //|Htest]; apply/le_anti/andP; split;
  apply/(proj2 (state_le_iff_expect _ _))=>P; by rewrite Htest.
Qed.

Theorem pairing_ext (x y : {summable I -> 'End(H)}) :
  (forall P : I -> 'FO(H), pairing P x = pairing P y) -> x = y.
Proof.
move=>Htest; apply/summableP=>i; apply/eqP; rewrite eq_le; apply/andP; split;
  apply/lef_trobs=>A.
- by move: (Htest (at_store i A)); rewrite !pairing_at_store (lftraceC A (x i)) (lftraceC A (y i))=>->.
- by move: (Htest (at_store i A)); rewrite !pairing_at_store (lftraceC A (x i)) (lftraceC A (y i))=>->.
Qed.
End Separation.
End CQStateExpectation.


Module CQStateDecreasingExpectation.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import CQStateDecreasing.
Section States.
Context {I : choiceType} {H : chsType}.
Local Notation state := (@CQState.state I H).
Theorem expect_chain_inf (P : I -> 'FO(H)) (f : nat -> state) : nonincreasing_seq f ->
  CQAssertion.expect P (f n) @[n --> \oo] --> CQAssertion.expect P (chain_inf f).
Proof. move=>Hd; apply: CQExpectation.expect_cvg; exact: chain_inf_cvg. Qed.
End States.

End CQStateDecreasingExpectation.
