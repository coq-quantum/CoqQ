(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From quantum.example.classical Require Import assertion language deterministic
  algorithm_loops predicate.

Module ClassicalAlgorithmSemantics.
Import ClassicalLanguage ClassicalDeterministic CQPredicate CQAssertion.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma execution_channel c s t F : execution c s t F -> F \is cptp.
Proof.
move=>D; elim: c s t F / D=>[s|t x e s|u q phi s|u q ue s|
  c1 c2 s t u F G D1 IH1 D2 IH2|
  b c1 c0 s t F Eb D IH|b c1 c0 s t F Eb D IH|
  b c s Eb|b c s t u F G Eb D1 IH1 D2 IH2].
1-4,8: exact: is_cptp.
2,3: exact: IH.
all: by rewrite (QChannel_BuildE IH1) (QChannel_BuildE IH2) is_cptp.
Qed.

Lemma execution_wp c s t F (Q : store -> 'FO(Hq)) :
  execution c s t F ->
  (wp (denote c) Q s : 'End(Hq)) = F^*o (Q t).
Proof.
move=>D; rewrite wpE (fin_supp_sum (S := [fset t]%fset)).
- move=>j; rewrite inE=>/negPf Ejt.
  by rewrite (execution_denote D) /point Ejt dualso0 soE.
- by rewrite psum1 (execution_denote D) /point eqxx.
Qed.

Lemma execution_pre total c s t (F : 'QC(Hq)) (Q : store -> 'FO(Hq)) :
  execution c s t F ->
  (xp total (denote c) Q s : 'End(Hq)) = F^*o (Q t).
Proof.
move=>D; case: total; first exact: execution_wp D.
change (cplmt (wp (denote c) (complement Q) s) = F^*o (Q t)).
by rewrite (execution_wp _ D) cplmt_dualC /complement /= cplmtK.
Qed.

Lemma formso_initial (U : chsType) (A : 'End(U)) v :
  formso A :o initialso v = initialso (A v).
Proof.
apply/superopP=>rho; rewrite comp_soE !initialsoE linearZ /= formsoE.
by rewrite -outp_complV -outp_comprV.
Qed.

Lemma register_unitary_comp u (q : wf_qreg u) (V U : 'End('Ht u)) :
  liftfso (formso (tf2f q q V)) :o liftfso (formso (tf2f q q U)) =
  liftfso (formso (tf2f q q (V \o U))).
Proof. by rewrite -liftfso_comp formso_comp tf2f_comp. Qed.

Lemma register_unitary_power u (q : wf_qreg u) (U : 'End('Ht u)) n :
  ClassicalAlgorithmLoops.superop_power (liftfso (formso (tf2f q q U))) n =
  liftfso (formso (tf2f q q (U ^+ n))).
Proof.
elim: n=>[|n IH].
- by rewrite /= expr0 tf2f1 formso1 liftfso1.
- by rewrite /= IH register_unitary_comp exprSr.
Qed.

End ClassicalAlgorithmSemantics.
