(* Concrete source prepares the exact order-finding output state.
   See ORDER-FINDING-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences exp trigo.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import language deterministic algorithm_semantics
  register_tensor phase_program phase_correctness predicate rules primitive
  order_finding order_finding_state.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalOrderFindingExecution.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmSemantics
  ClassicalRegisterTensor ClassicalPhaseProgram ClassicalOrderFinding
  ClassicalOrderFindingState.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma all_hadamards_zero t :
  @all_hadamards t (zero_state (QArray t QBool) : 'Ht (QArray t QBool)) = uniformtv.
Proof.
change (tentf_tuple (fun _ : 'I_t => (Hadamard : 'End('Hs bool)))
  ''(nseq_tuple t false) = uniformtv).
rewrite t2tv_tuple tentf_tuple_apply -uniformtv_tuple.
apply: eq_tentv_tuple=>i; by rewrite tnth_nseq Hadamard0 uniformtv_bool.
Qed.

Lemma measured_projector_probability (t L : nat)
    (psi : 'Ht (QPair (QArray t QBool) (QArray L QBool))) (m : t.-tuple bool) :
  [< psi; ([> ''m; ''m <] ⊗f (\1 : 'End('Hs(L.-tuple bool)))) psi >] =
  \sum_(y : L.-tuple bool) `|[< ''m ⊗t ''y; psi >]|^+2.
Proof.
rewrite -(sumonb_out (@t2tv (L.-tuple bool))) tentf_sumr sum_lfunE dotp_sumr.
apply: eq_bigr=>y _.
rewrite tentv_out outpE dotpZr -(conj_dotp (''m ⊗t ''y) psi).
by rewrite -sqr_normc.
Qed.

Section Program.
Variables (N L t : nat).
Hypothesis HN : (1 < N)%N.
Hypothesis capacity : (N <= 2 ^ L)%N.
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).
Variable x : expression nat.

Lemma initial_pair_reverse (a : 'Ht (QArray t QBool)) (b : 'Ht (QArray L QBool)) :
  liftfso (initialso (tv2v (target_register qr) b)) :o
    liftfso (initialso (tv2v (control_register qr) a)) =
  liftfso (initialso (tv2v qr (a ⊗t b))).
Proof.
rewrite (liftfso_compC _ _); first by rewrite disjoint_sym; exact: pair_register_disjoint.
exact: initial_register_pair.
Qed.

Theorem prefix_actionE s : @prefix_action N L t HN capacity qr x s =
  liftfso (initialso (tv2v qr (@output_state N L t HN capacity (eval x s)))).
Proof.
rewrite /prefix_action -!comp_soA.
rewrite -liftfso_comp formso_initial tf2f_apply all_hadamards_zero.
rewrite (comp_soA _ (liftfso (initialso (tv2v (target_register qr)
  (zero_state (QArray L QBool)))))) -liftfso_comp formso_initial tf2f_apply one_preparationE.
rewrite initial_pair_reverse.
rewrite -liftfso_comp formso_initial tf2f_apply.
rewrite /control_register channel_register_left -liftfso_comp formso_initial tf2f_apply.
by [].
Qed.

Theorem prefix_prepares s :
  execution (@prefix N L t HN capacity qr x) s s
    (liftfso (initialso (tv2v qr (@output_state N L t HN capacity (eval x s))))).
Proof. rewrite -prefix_actionE; exact: prefix_execution. Qed.

Variable measured : variable (QType (QArray t QBool)).
Variable result : variable (COption CNat).

Lemma postprocess_preserves_outcome total (m : t.-tuple bool) :
  CQRules.pre total
    (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
    (ClassicalPhaseCorrectness.outcome_post measured m) =
  ClassicalPhaseCorrectness.outcome_post measured m.
Proof.
apply/funext=>s; apply/val_inj.
change ((CQRules.pre total
  (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
  (ClassicalPhaseCorrectness.outcome_post measured m) s : 'End(Hq)) =
  (ClassicalPhaseCorrectness.outcome_post measured m s : 'End(Hq))).
rewrite /CQRules.pre CQPrimitive.assign_pre
  /ClassicalPhaseCorrectness.outcome_post get_set_net //.
Qed.

Theorem order_finding_outcome_pre total (m : t.-tuple bool) s :
  (CQRules.pre total (@order_finding N L t HN capacity qr x measured result)
    (ClassicalPhaseCorrectness.outcome_post measured m) s : 'End(Hq)) =
  (@outcome_probability N L t HN capacity (eval x s) m) *: \1.
Proof.
rewrite /order_finding CQRules.pre_sequence.
rewrite [CQRules.pre _ (Sequence (Measure _ _ _) _) _]CQRules.pre_sequence
  postprocess_preserves_outcome.
rewrite /CQRules.pre.
rewrite (execution_pre _ _ (prefix_prepares s)).
rewrite ClassicalPhaseCorrectness.measurement_outcome_pre.
rewrite /control_register -(lift_register_left qr [> ''m; ''m <])
  liftfso_dual liftfsoEf dualso_initialE tf2f_apply tv2v_dot
  measured_projector_probability linearZ /= liftf_lf1.
by [].
Qed.

End Program.
End ClassicalOrderFindingExecution.
