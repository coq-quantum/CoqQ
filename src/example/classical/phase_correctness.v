(* Deterministic certificates for the actual nested phase-estimation loops. *)
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
From quantum.example.classical Require Import language deterministic algorithm_loops
  indexed_loops algorithm_semantics register_tensor predicate rules primitive fourier
  phase_estimation phase_program phase_execution phase_tensor phase_stages.

Module ClassicalPhaseCorrectness.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops
  ClassicalIndexedLoops ClassicalAlgorithmSemantics ClassicalRegisterTensor
  ClassicalFourier ClassicalPhaseEstimation ClassicalPhaseProgram
  ClassicalPhaseExecution ClassicalPhaseTensor ClassicalPhaseStages.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation R := hermitian.R.

Section PhaseEstimation.
Variable (n : nat) (T : qType).
Variable (qr : wf_qreg (QPair (QArray n QBool) T)).
Variable (U Uu : 'FU('Ht T)).
Variable (x y : variable Integer).
Hypothesis distinct_counters : cvname y != cvname x.

Definition remaining_circuit start :=
  unitary_list [seq estimation_stage U i | i <- drop start (enum 'I_n)].

Lemma remaining_circuit_end :
  (remaining_circuit n : 'End('Ht (QPair (QArray n QBool) T))) = \1.
Proof. by rewrite /remaining_circuit drop_oversize ?size_enum_ord. Qed.

Lemma remaining_circuit_step (i : 'I_n) :
  (remaining_circuit i : 'End('Ht (QPair (QArray n QBool) T))) =
    remaining_circuit i.+1 \o estimation_stage U i.
Proof.
by rewrite /remaining_circuit (drop_nth i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.

Lemma remaining_circuit_whole :
  (remaining_circuit 0 : 'End('Ht (QPair (QArray n QBool) T))) =
    estimation_circuit_prefix n U n.
Proof.
by rewrite /remaining_circuit /estimation_circuit_prefix drop0 take_oversize ?size_enum_ord.
Qed.

Lemma accumulated_circuit count start s : (start + count = n)%N ->
  accumulated_action (phase_next n x y) (phase_action qr U) start.+1 count s =
    liftfso (formso (tf2f qr qr (remaining_circuit start))).
Proof.
elim: count start s=>[|count IH] start s Hn.
- rewrite addn0 in Hn; subst start.
  by rewrite /= remaining_circuit_end tf2f1 formso1 liftfso1.
- have Hstart : (start < n)%N.
    by rewrite -Hn addnS ltnS leq_addr.
  pose i : 'I_n := Ordinal Hstart.
  have Hnt : (start.+1 + count = n)%N by rewrite addSn -addnS.
  change (accumulated_action (phase_next n x y) (phase_action qr U) start.+2 count
    (phase_next n x y start.+1 s) :o phase_action qr U start.+1 s =
      liftfso (formso (tf2f qr qr (remaining_circuit start)))).
  rewrite (IH _ _ Hnt) /phase_action (@one_based_indexE n i)
    register_unitary_power /control_register channel_register_left
    register_unitary_comp register_unitary_comp (remaining_circuit_step i).
  by [].
Qed.

Variable phi : R.
Hypothesis eigenstate : U (Uu (zero_state T : 'Ht T)) = expip (2 * phi) *: Uu (zero_state T : 'Ht T).

Lemma phase_prefix_actionE s :
  phase_prefix_action qr U x y Uu s =
  liftfso (initialso (tv2v qr (output_state n phi ⊗t Uu (zero_state T : 'Ht T)))).
Proof.
rewrite /phase_prefix_action (@accumulated_circuit n 0 (s.[x <- (1 : int)])%M (add0n n)) remaining_circuit_whole
  -!comp_soA -liftfso_comp formso_initial tf2f_apply
  /control_register /target_register initial_register_pair
  -liftfso_comp formso_initial tf2f_apply.
rewrite (estimation_circuit_eigen n eigenstate).
rewrite channel_register_left -liftfso_comp formso_initial tf2f_apply
  tentf_apply lfunE /output_state.
by [].
Qed.

Lemma phase_reset_execution s :
  execution (phase_prefix qr U Uu x y) s (phase_final_store n x y s)
    (liftfso (initialso (tv2v qr (output_state n phi ⊗t Uu (zero_state T : 'Ht T))))).
Proof.
rewrite -(phase_prefix_actionE s).
exact: (@phase_prefix_execution n T qr U x y distinct_counters Uu s).
Qed.

Definition outcome_post (z : variable (QType (QArray n QBool)))
    (m : n.-tuple bool) : store -> 'FO(Hq) :=
  fun s => if (s.[z])%M == m then (\1 : 'FO(Hq)) else (0%:VF : 'FO(Hq)).

Lemma measurement_outcome_pre total z m s :
  (CQPredicate.xp total
    (denote (Measure z (control_register qr)
      (EConst [QM of @tmeas (eval_qtype (QArray n QBool))])))
    (outcome_post z m) s : 'End(Hq)) =
  liftf_lf (tf2f (control_register qr) (control_register qr) [> ''m; ''m <]).
Proof.
rewrite CQPrimitive.measurement_pre.
change (\sum_v ((liftf_lf (tf2f (control_register qr) (control_register qr) (tmeas v)))^A \o
  (outcome_post z m (s.[z <- v])%M : 'End(Hq)) \o
  liftf_lf (tf2f (control_register qr) (control_register qr) (tmeas v))) =
  liftf_lf (tf2f (control_register qr) (control_register qr) [> ''m; ''m <])).
rewrite (bigD1 m) //= /outcome_post get_set_eq eqxx big1.
- move=>i /negPf Him.
  by rewrite get_set_eq Him comp_lfun0r comp_lfun0l.
- by rewrite addr0 comp_lfun1r -liftf_lf_adj -liftf_lf_comp tf2f_adj tf2f_comp
    /tmeas adj_outp outp_comp ns_dot scale1r.
Qed.

Theorem phase_outcome_pre total z m s :
  (CQRules.pre total (phase_estimation qr U Uu x y z) (outcome_post z m) s : 'End(Hq)) =
  ([< output_state n phi; ''m >] * [< ''m; output_state n phi >]) *: \1.
Proof.
rewrite /phase_estimation CQRules.pre_sequence /CQRules.pre
  (execution_pre _ _ (phase_reset_execution s)) measurement_outcome_pre.
rewrite /control_register -(lift_register_left qr [> ''m; ''m <])
  liftfso_dual liftfsoEf dualso_initialE tf2f_apply tv2v_dot
  tentf_apply lfunE tentv_dot isof_dot ns_dot mulr1 outpE dotpZr mulrC
  linearZ /= liftf_lf1.
by [].
Qed.

Theorem phase_outcome_formula total z m s :
  (CQRules.pre total (phase_estimation qr U Uu x y z) (outcome_post z m) s : 'End(Hq)) =
  `| (sqrtC 2%:R ^- n)^+2 *
    \sum_(i : n.-tuple bool)
      expip ((bseq2ord i)%:R * (2 * phi) -
        2%:R * (bseq2ord m * bseq2ord i)%:R / 2%:R ^+ n) |^+2 *: \1.
Proof.
by rewrite phase_outcome_pre -conj_dotp mulrC -sqr_normc phase_output_amplitude.
Qed.

Definition outcome_bound (m : n.-tuple bool) : 'FO(Hq) :=
  [obs of liftf_lf (tf2f (control_register qr) (control_register qr)
    ((initialso (output_state n phi))^*o [> ''m; ''m <]))].

Lemma outcome_boundE m : (outcome_bound m : 'End(Hq)) =
  ([< output_state n phi; ''m >] * [< ''m; output_state n phi >]) *: \1.
Proof.
by rewrite /outcome_bound /= dualso_initialE outpE dotpZr mulrC
  !linearZ /= tf2f1 liftf_lf1.
Qed.

Theorem phase_estimation_correct total z m :
  CQRules.derives total (fun _ => outcome_bound m)
    (phase_estimation qr U Uu x y z) (outcome_post z m).
Proof.
apply: CQRules.derives_complete.
apply/(proj2 (CQRules.valid_iff _ _ _ _))=>s.
by rewrite phase_outcome_pre outcome_boundE.
Qed.

Theorem phase_exact_pre total z m s :
  phi = (bseq2ord m)%:R / 2%:R ^+ n ->
  (CQRules.pre total (phase_estimation qr U Uu x y z) (outcome_post z m) s : 'End(Hq)) = \1.
Proof.
by move=>Hphi; rewrite phase_outcome_pre Hphi exact_phase_output ns_dot mulr1 scale1r.
Qed.

Theorem phase_exact_correct total z m :
  phi = (bseq2ord m)%:R / 2%:R ^+ n ->
  CQRules.derives total (fun _ => (\1 : 'FO(Hq)))
    (phase_estimation qr U Uu x y z) (outcome_post z m).
Proof.
move=>Hphi; apply: CQRules.derives_complete.
apply/(proj2 (CQRules.valid_iff _ _ _ _))=>s.
by rewrite (@phase_exact_pre total z m s Hphi).
Qed.

End PhaseEstimation.
End ClassicalPhaseCorrectness.
