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

From mathcomp.analysis Require Import exp trigo.
From quantum Require Import qtype.
From quantum.example.classical Require Import assertion language deterministic
  algorithm_loops algorithm_semantics predicate primitive rules grover.

Module ClassicalGroverCorrectness.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops
  ClassicalAlgorithmSemantics ClassicalGrover CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Lemma power_initial u (q : wf_qreg u) (U : 'FU('Ht u)) n v :
  superop_power (liftfso (formso (tf2f q q U))) n :o
    liftfso (initialso (tv2v q v)) =
  liftfso (initialso (tv2v q (iter n U v))).
Proof.
elim: n v=>[|n IH] v; first by rewrite /= comp_so1l.
by rewrite /= -comp_soA -liftfso_comp formso_initial tf2f_apply IH -iterSr iterS.
Qed.

Section Grover.
Variable (T : qType) (q : wf_qreg T).
Notation TT := (eval_qtype T).
Variable (Pw : pred TT).
Hypothesis card_Pw : (0 < #|Pw| < #|TT|)%N.

Definition final_store K (x : variable Integer) s :=
  iter K (next_store x) (s.[x <- (0 : int)])%M.

Lemma grover_prefix_execution K x s :
  execution (grover_prefix q Pw K x) s (final_store K x s)
    (liftfso (initialso (tv2v q (iteration_state Pw K)))).
Proof.
have Hs : ((s.[x <- (0 : int)]).[x])%M = Posz 0 by rewrite get_set_eq.
have Dloop := @counted_unitary_execution T q (rotation Pw) x K 0
  (s.[x <- (0 : int)])%M Hs.
rewrite add0n in Dloop.
have D := RunSequence (RunInitialize q (EConst (zero_state T)) s)
  (RunSequence (RunUnitary q (EConst (@uniformtf TT)) s)
    (RunSequence (RunAssign x (EConst (0 : int)) s) Dloop)).
rewrite comp_so1r -comp_soA -liftfso_comp formso_initial tf2f_apply
  uniformtfE power_initial in D.
exact: D.
Qed.

Lemma grover_prefix_denote K x s m :
  denote (grover_prefix q Pw K x) s m =
  point (final_store K x s)
    (liftfso (initialso (tv2v q (iteration_state Pw K)))) m.
Proof. apply: execution_denote; exact: grover_prefix_execution. Qed.

Definition success_post (y : variable (QType T)) : store -> 'FO(Hq) :=
  fun s => if Pw (s.[y])%M then (\1 : 'FO(Hq)) else (0%:VF : 'FO(Hq)).

Lemma measurement_success_pre total y s :
  (xp total (denote (Measure y q (EConst [QM of @tmeas TT])))
    (success_post y) s : 'End(Hq)) =
  liftf_lf (tf2f q q (success_effect Pw)).
Proof.
rewrite CQPrimitive.measurement_pre.
change (\sum_v ((liftf_lf (tf2f q q (tmeas v)))^A \o
  (success_post y (s.[y <- v])%M : 'End(Hq)) \o
  liftf_lf (tf2f q q (tmeas v))) =
  liftf_lf (tf2f q q (\sum_(i | Pw i) [> ''i ; ''i <]))).
rewrite !linear_sum /= [RHS]big_mkcond; apply eq_bigr=>i _.
rewrite /success_post get_set_eq; case: (Pw i)=>/=.
- by rewrite comp_lfun1r -liftf_lf_adj -liftf_lf_comp tf2f_adj tf2f_comp
    /tmeas adj_outp outp_comp ns_dot scale1r.
- by rewrite comp_lfun0r comp_lfun0l.
Qed.

Theorem grover_success_pre total K x y s :
  (CQRules.pre total (grover q Pw K x y) (success_post y) s : 'End(Hq)) =
  (success_probability Pw K)%:C *: \1.
Proof.
rewrite /grover CQRules.pre_sequence.
rewrite /CQRules.pre (execution_pre _ _ (grover_prefix_execution K x s)).
rewrite measurement_success_pre liftfso_dual liftfsoEf dualso_initialE
  tf2f_apply tv2v_dot (iteration_success card_Pw) linearZ /= liftf_lf1.
by [].
Qed.

Definition success_bound K : 'FO(Hq) :=
  [obs of liftf_lf (tf2f q q
    ((initialso (iteration_state Pw K))^*o (success_effect Pw)))].

Lemma success_boundE K : (success_bound K : 'End(Hq)) =
  (success_probability Pw K)%:C *: \1.
Proof.
by rewrite /success_bound /= dualso_initialE (iteration_success card_Pw)
  !linearZ /= tf2f1 liftf_lf1.
Qed.

Theorem grover_correct total K x y :
  CQRules.derives total (fun _ => success_bound K)
    (grover q Pw K x y) (success_post y).
Proof.
apply: CQRules.derives_complete.
apply/(proj2 (CQRules.valid_iff _ _ _ _))=>s.
by rewrite grover_success_pre success_boundE.
Qed.

End Grover.
End ClassicalGroverCorrectness.
