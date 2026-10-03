(* Order separation and continuous expectations. See EXPECTATION-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion expectation mixture.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQStateExpectation.
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
