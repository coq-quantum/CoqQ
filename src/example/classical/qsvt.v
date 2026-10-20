(* Exact QSVT in the existing classical language and total Hoare logic.
   QSVT_PROOF_NOTES.md maps the scalar synthesis, full operator support,
   native While execution, heralded branches and uniform polynomial theorem. *)
From HB Require Import structures.
From mathcomp Require Import ring_tactic.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences exp trigo.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable
  qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import
  language state assertion semantics hoare auxiliary qsvt_poly qsvt_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module QSVTClassicalProgram.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics.
Import ClassicalDeterministic ClassicalAlgorithmLoops ClassicalIndexedLoops.
Import ClassicalAlgorithmSemantics CQAssertion CQPredicate QSVTModel.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation R := hermitian.R.
Local Notation Hq := 'H[msys]_finset.setT.

Section Program.
Variable (T : qType).
Variable (qr : wf_qreg (QPair QBool T)).
Variable (U : 'FU('Ht T)).
Variable (PiR PiL : 'FP('Ht T)).
Variable (d : nat) (phi : nat -> R).
Variable (x : variable Integer).
Variable (y : variable (QType QBool)).

Let qa : wf_qreg QBool :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid qr)).
Let qs : wf_qreg T :=
  WF_QReg (QRegAuto.valid_qreg_snd (qreg_is_valid qr)).

(* The false ancilla sector uses theta; the true sector uses -theta. *)
Definition controlled_projector_phase (P : 'FP('Ht T)) (theta : R)
    : 'FU('Ht (QPair QBool T)) :=
  [unitary of Multiplexer
    (fun b : bool => projector_phase P (if b then - theta else theta))].
Definition right_rotation theta := controlled_projector_phase PiR theta.
Definition left_rotation theta := controlled_projector_phase PiL theta.
Definition signal_at (z : int) : 'FU('Ht T) :=
  if odd (absz z) then [unitary of U^A] else U.
Definition rotation_at (z : int) : 'FU('Ht (QPair QBool T)) :=
  if odd (absz z)
  then left_rotation (phi (d - absz z)%N)
  else right_rotation (phi (d - absz z)%N).

(* This is the source's unbounded While, with its private integer counter. *)
Definition qsvt_body : command :=
  Sequence
    (Unitary qs (EApp (EConst signal_at) (EVar x)))
    (Sequence (Assign x (increment x))
      (Unitary qr (EApp (EConst rotation_at) (EVar x)))).
Definition qsvt_core : command :=
  Sequence (Assign x (EConst (0 : int)))
    (Sequence (Unitary qr (EConst (right_rotation (phi d))))
      (While (below x d) qsvt_body)).
Definition plus_state : 'NS('Ht QBool) :=
  [NS of @uniformtv (eval_qtype QBool)].
Definition qsvt_apply : command :=
  Sequence (Initialize qa (EConst plus_state)) qsvt_core.
Definition qsvt_readout_prefix : command :=
  Sequence qsvt_apply (Unitary qa (EConst [unitary of Hadamard])).
Definition qsvt_heralded : command :=
  Sequence qsvt_readout_prefix
    (Measure y qa (EConst [QM of @tmeas (eval_qtype QBool)])).
Definition qsvt_run (v : 'NS('Ht T)) : command :=
  Sequence (Initialize qs (EConst v)) qsvt_heralded.

(* Independent polynomial specification, before proof infrastructure.
   Later theorems construct the contraction F from sv_even / sv_odd below;
   neither assertion is defined by running the command or taking its wp. *)
Section PolynomialSpecification.
Variables (HR HL HO : chsType).
Variables (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T)).
Definition even_polynomial_transform (p : {poly hermitian.C}) :=
  sv_even p (encoded U JR JL).
Definition odd_polynomial_transform (p : {poly hermitian.C}) :=
  sv_odd p (encoded U JR JL).
Variable (JO : 'FI(HO,'Ht T)) (F : 'FB1(HR,HO)).
Definition qsvt_polynomial_pre (E : 'FO(HO)) : store -> 'FO(Hq) :=
  fun _ => [obs of liftf_lf (tf2f qr qr
    ((\1 : 'FO('Ht QBool)) ⊗f
      [obs of formlf JR ((formso F)^*o E)]))].
Definition qsvt_polynomial_post (E : 'FO(HO)) : store -> 'FO(Hq) :=
  fun s => if (((s.[x])%M == Posz d) && ((s.[y])%M == false))
    then [obs of liftf_lf (tf2f qr qr
      ((\1 : 'FO('Ht QBool)) ⊗f [obs of formlf JO E]))]
    else (0%:VF : 'FO(Hq)).
Definition qsvt_polynomial_contract := forall E : 'FO(HO),
  CQHoare.derives true (qsvt_polynomial_pre E)
    qsvt_heralded (qsvt_polynomial_post E).
End PolynomialSpecification.

(* Independent, chronological finite product: signal t, then rotation t+1.
   It is defined by matrix composition, not by executing the command. *)
Definition coherent_step t : 'FU('Ht (QPair QBool T)) :=
  [unitary of rotation_at (Posz t.+1) \o
    ((\1 : 'FU('Ht QBool)) ⊗f signal_at (Posz t))].
Fixpoint coherent_tail k n : 'FU('Ht (QPair QBool T)) :=
  if n is n'.+1
  then [unitary of coherent_tail k.+1 n' \o coherent_step k]
  else (\1 : 'FU('Ht (QPair QBool T))).
Definition coherent_core : 'FU('Ht (QPair QBool T)) :=
  [unitary of coherent_tail 0 d \o right_rotation (phi d)].
Definition signed_phase (b : bool) (t : nat) :=
  if b then - phi t else phi t.
Definition sector_rotation (b : bool) t : 'FU('Ht T) :=
  projector_phase (if odd t then PiL else PiR) (signed_phase b (d-t)%N).
Definition sector_step (b : bool) t : 'FU('Ht T) :=
  [unitary of sector_rotation b t.+1 \o signal_at (Posz t)].
Fixpoint sector_tail (b : bool) k n : 'FU('Ht T) :=
  if n is n'.+1
  then [unitary of sector_tail b k.+1 n' \o sector_step b k]
  else (\1 : 'FU('Ht T)).
Definition sector_core (b : bool) : 'FU('Ht T) :=
  [unitary of sector_tail b 0 d \o projector_phase PiR (signed_phase b d)].
Definition qsvt_final_store s :=
  iter d (next_store x) (s.[x <- (0 : int)])%M.
Definition qsvt_core_channel : 'QC(Hq) :=
  [QC of liftfso (formso (tf2f qr qr coherent_core))].
Definition qsvt_readout_channel : 'QC(Hq) :=
  [QC of liftfso (formso (tf2f qa qa [unitary of Hadamard])) :o
    qsvt_core_channel :o liftfso (initialso (tv2v qa plus_state))].

(* An independently specified all-effects contract for the finite coherent
   product.  Identifying this product with SV_d(p,A) is a further theorem. *)
Definition core_pre (E : 'FO('Ht (QPair QBool T))) : store -> 'FO(Hq) :=
  fun _ => [obs of liftf_lf (tf2f qr qr
    (formlf coherent_core^A E))].
Definition core_post (E : 'FO('Ht (QPair QBool T))) : store -> 'FO(Hq) :=
  fun s => if ((s.[x])%M == Posz d)
    then [obs of liftf_lf (tf2f qr qr E)] else (0%:VF : 'FO(Hq)).

Lemma coherent_core_zero : d = 0%N ->
  (coherent_core : 'End('Ht (QPair QBool T))) = right_rotation (phi 0).
Proof. by move=>Hd; rewrite /coherent_core Hd /= comp_lfun1l. Qed.

Lemma coherent_core_one : d = 1%N ->
  (coherent_core : 'End('Ht (QPair QBool T))) =
    left_rotation (phi 0) \o ((\1 : 'End('Ht QBool)) ⊗f U) \o
      right_rotation (phi 1).
Proof.
move=>Hd.
by rewrite /coherent_core Hd /= /coherent_step /rotation_at /signal_at Hd
  /= comp_lfun1l.
Qed.

Lemma coherent_core_two : d = 2%N ->
  (coherent_core : 'End('Ht (QPair QBool T))) =
    right_rotation (phi 0) \o ((\1 : 'End('Ht QBool)) ⊗f U^A) \o
      left_rotation (phi 1) \o ((\1 : 'End('Ht QBool)) ⊗f U) \o
        right_rotation (phi 2).
Proof.
move=>Hd.
by rewrite /coherent_core Hd /= /coherent_step /rotation_at /signal_at Hd
  /= comp_lfun1l !comp_lfunA.
Qed.

Lemma rotation_at_sector (b : bool) t (v : 'Ht T) :
  rotation_at (Posz t) (''b ⊗t v) = ''b ⊗t (sector_rotation b t v).
Proof.
rewrite /rotation_at /sector_rotation /signed_phase /=.
by case: (odd t); rewrite /left_rotation /right_rotation
  /controlled_projector_phase MultiplexerEt.
Qed.

Lemma coherent_step_sector (b : bool) t (v : 'Ht T) :
  coherent_step t (''b ⊗t v) = ''b ⊗t (sector_step b t v).
Proof.
by rewrite /coherent_step /sector_step !lfunE /= tentf_apply lfunE
  rotation_at_sector.
Qed.

Lemma coherent_tail_sector (b : bool) n k (v : 'Ht T) :
  coherent_tail k n (''b ⊗t v) = ''b ⊗t (sector_tail b k n v).
Proof.
elim: n k v=>[|n IH] k v; first by rewrite /= !lfunE.
by rewrite /= !lfunE /= coherent_step_sector IH.
Qed.

Theorem coherent_core_sector (b : bool) (v : 'Ht T) :
  coherent_core (''b ⊗t v) = ''b ⊗t (sector_core b v).
Proof.
by rewrite /coherent_core /sector_core !lfunE /= /right_rotation
  /controlled_projector_phase MultiplexerEt coherent_tail_sector.
Qed.

Theorem coherent_core_multiplexer :
  (coherent_core : 'End('Ht (QPair QBool T))) = Multiplexer sector_core.
Proof.
apply/(intro_onb (@t2tv2_onbasis (eval_qtype QBool) (eval_qtype T)))=>[[b i]].
by rewrite /t2tv2_onbasis /tentv_onbasis /tentv_fun /=
  coherent_core_sector MultiplexerEt.
Qed.

Section EncodingBridge.
Variables (HR HL : chsType).
Variables (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T)).
Hypothesis right_projector : PiR = range_projector JR.
Hypothesis left_projector : PiL = range_projector JL.

Lemma sector_step_prefix (b : bool) t :
  sector_step b t \o qsvt_prefix U JR JL d (signed_phase b) t =
    qsvt_prefix U JR JL d (signed_phase b) t.+1.
Proof.
by rewrite /sector_step /sector_rotation /signal_at /=
  right_projector left_projector.
Qed.

Lemma sector_tail_prefix (b : bool) n k :
  sector_tail b k n \o qsvt_prefix U JR JL d (signed_phase b) k =
    qsvt_prefix U JR JL d (signed_phase b) (k + n)%N.
Proof.
elim: n k=>[|n IH] k; first by rewrite /= comp_lfun1l addn0.
change ((sector_tail b k.+1 n \o sector_step b k) \o
  qsvt_prefix U JR JL d (signed_phase b) k =
  qsvt_prefix U JR JL d (signed_phase b) (k + n.+1)%N).
by rewrite -comp_lfunA sector_step_prefix IH addSn -addnS.
Qed.

Theorem sector_core_prefix (b : bool) :
  (sector_core b : 'End('Ht T)) = qsvt_prefix U JR JL d (signed_phase b) d.
Proof.
rewrite /sector_core right_projector.
change (sector_tail b 0 d \o qsvt_prefix U JR JL d (signed_phase b) 0 =
  qsvt_prefix U JR JL d (signed_phase b) d).
by rewrite sector_tail_prefix add0n.
Qed.

Theorem coherent_core_prefix :
  (coherent_core : 'End('Ht (QPair QBool T))) =
    Multiplexer (fun b : bool => qsvt_prefix U JR JL d (signed_phase b) d).
Proof.
rewrite coherent_core_multiplexer.
congr (Multiplexer _); apply/funext=>b.
exact: sector_core_prefix.
Qed.
End EncodingBridge.

Lemma qsvt_body_execution t s : (s.[x])%M = Posz t ->
  execution qsvt_body s (next_store x s)
    (liftfso (formso (tf2f qr qr (coherent_step t)))).
Proof.
move=>Hs.
have Dsignal := RunUnitary qs
  (EApp (EConst signal_at) (EVar x)) s.
rewrite /eval /= Hs in Dsignal.
have Drotation := RunUnitary qr
  (EApp (EConst rotation_at) (EVar x)) (next_store x s).
have Er : eval (EApp (EConst rotation_at) (EVar x)) (next_store x s) =
    rotation_at (Posz t.+1).
  change (rotation_at ((next_store x s).[x])%M = rotation_at (Posz t.+1)).
  by rewrite (next_store_value Hs).
rewrite Er in Drotation.
have D := RunSequence Dsignal
  (RunSequence (RunAssign x (increment x) s) Drotation).
rewrite comp_so1r in D.
rewrite /qs ClassicalRegisterTensor.channel_register_right
  register_unitary_comp in D.
exact: D.
Qed.

Lemma qsvt_loop_execution n k s : (s.[x])%M = Posz k ->
  execution (While (below x (k + n)) qsvt_body) s
    (iter n (next_store x) s)
    (liftfso (formso (tf2f qr qr (coherent_tail k n)))).
Proof.
elim: n k s=>[|n IH] k s Hs.
- rewrite addn0 /= tf2f1 formso1 liftfso1.
  apply: RunWhileFalse; by rewrite /below /eval /= Hs ltxx.
- have Hb : eval (below x (k + n.+1)) s = true.
    by rewrite /below /eval /= Hs ltz_nat addnS ltnS leq_addr.
  have Dt := IH k.+1 (next_store x s) (next_store_value Hs).
  rewrite addSn -addnS in Dt.
  have D := RunWhileTrue Hb (qsvt_body_execution Hs) Dt.
  rewrite register_unitary_comp in D.
  rewrite iterSr; exact: D.
Qed.

Theorem qsvt_core_execution s :
  execution qsvt_core s (qsvt_final_store s) qsvt_core_channel.
Proof.
have Hs : ((s.[x <- (0 : int)]).[x])%M = Posz 0 by rewrite get_set_eq.
have Dl := qsvt_loop_execution d Hs.
rewrite add0n in Dl.
have D := RunSequence (RunAssign x (EConst (0 : int)) s)
  (RunSequence (RunUnitary qr (EConst (right_rotation (phi d))) _) Dl).
rewrite comp_so1r register_unitary_comp in D.
exact: D.
Qed.

Theorem qsvt_core_denote s m :
  denote qsvt_core s m = point (qsvt_final_store s) qsvt_core_channel m.
Proof. exact: (execution_denote (qsvt_core_execution s) m). Qed.

Lemma counter_after n k s : (s.[x])%M = Posz k ->
  ((iter n (next_store x) s).[x])%M = Posz (k + n).
Proof.
elim: n k s=>[|n IH] k s Hs; first by rewrite addn0.
by rewrite iterSr (IH _ _ (next_store_value Hs)) addSn -addnS.
Qed.

Theorem qsvt_final_counter s : (qsvt_final_store s).[x]%M = Posz d.
Proof.
by rewrite /qsvt_final_store (counter_after d (get_set_eq _ _ _)) add0n.
Qed.

Theorem qsvt_core_preE total E s :
  (CQHoare.pre total qsvt_core (core_post E) s : 'End(Hq)) = core_pre E s.
Proof.
rewrite /CQHoare.pre (execution_pre _ _ (qsvt_core_execution s)).
rewrite /core_post qsvt_final_counter eqxx /= /qsvt_core_channel
  liftfso_dual liftfsoEf dualso_formE.
by rewrite /core_pre /= formlfEV tf2f_adj !tf2f_comp.
Qed.

Theorem qsvt_core_correct total E :
  CQHoare.derives total (core_pre E) qsvt_core (core_post E).
Proof.
apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite qsvt_core_preE.
Qed.

Theorem qsvt_readout_execution s :
  execution qsvt_readout_prefix s (qsvt_final_store s) qsvt_readout_channel.
Proof.
have D := RunSequence
  (RunSequence (RunInitialize qa (EConst plus_state) s) (qsvt_core_execution s))
  (RunUnitary qa (EConst [unitary of Hadamard]) (qsvt_final_store s)).
by rewrite comp_soA in D.
Qed.

Theorem qsvt_readout_denote s m : denote qsvt_readout_prefix s m =
  point (qsvt_final_store s) qsvt_readout_channel m.
Proof. exact: (execution_denote (qsvt_readout_execution s) m). Qed.

(* Unnormalized branch maps, with the measured ancilla retained in memory.
   false is success and true is failure.  This formula includes both outcomes
   without dividing by their probabilities. *)
Definition herald_branch (b : bool) : 'SO(Hq) :=
  liftfso (formso (tf2f qa qa (@tmeas (eval_qtype QBool) b))) :o
    qsvt_readout_channel.

Theorem qsvt_heralded_denote s m :
  denote qsvt_heralded s m =
    point ((qsvt_final_store s).[y <- false])%M (herald_branch false) m +
    point ((qsvt_final_store s).[y <- true])%M (herald_branch true) m.
Proof.
change (slet (denote qsvt_readout_prefix)
  (denote (Measure y qa (EConst [QM of @tmeas (eval_qtype QBool)]))) s m =
    point ((qsvt_final_store s).[y <- false])%M (herald_branch false) m +
    point ((qsvt_final_store s).[y <- true])%M (herald_branch true) m).
rewrite (@sequence_point (denote qsvt_readout_prefix)
  (denote (Measure y qa (EConst [QM of @tmeas (eval_qtype QBool)])))
  s (qsvt_final_store s) qsvt_readout_channel (qsvt_readout_denote s) m).
rewrite /denote /measure_kernel /measure_sem /sdlet /= /sdlet_def
  fin_dom_sum big_bool linearDl /=.
rewrite /sunit_def /point /herald_branch.
rewrite /smeas /= /smeas_def -!liftfso_elemso [LHS]addrC.
by do 2!case: ifP=>_; rewrite ?comp_so0l.
Qed.

Lemma outcome_store_eq s (b c : bool) :
  ((s.[y <- b])%M == (s.[y <- c])%M) = (b == c).
Proof.
apply/idP/idP.
- move/eqP=>H; apply/eqP.
  have Hy := congr1 (fun t : store => (t.[y])%M) H.
  by rewrite !get_set_eq in Hy.
- by move/eqP=>->.
Qed.

Theorem qsvt_heralded_branches s (rho : 'FD(Hq)) (b : bool) :
  CQHoare.run qsvt_heralded (CQState.point s rho)
    ((qsvt_final_store s).[y <- b])%M = herald_branch b rho.
Proof.
rewrite /CQHoare.run CQKernel.apply_point qsvt_heralded_denote
  /point !outcome_store_eq.
by case: b; rewrite /= !soE ?addr0 ?add0r.
Qed.

Definition branch_probability (rho : 'FD(Hq)) (b : bool) :=
  \Tr (herald_branch b rho).

Corollary qsvt_success_probability s (rho : 'FD(Hq)) :
  \Tr (CQHoare.run qsvt_heralded (CQState.point s rho)
    ((qsvt_final_store s).[y <- false])%M) = branch_probability rho false.
Proof. by rewrite qsvt_heralded_branches. Qed.

(* This statement proves termination and preservation of all outcomes; it
   does not claim that the false herald is obtained with probability one. *)
Theorem qsvt_heralded_top_pre :
  CQHoare.pre true qsvt_heralded semantic_top = semantic_top.
Proof.
rewrite /qsvt_heralded CQHoare.pre_sequence.
have Hm : CQHoare.pre true
    (Measure y qa (EConst [QM of @tmeas (eval_qtype QBool)])) semantic_top =
    semantic_top.
  apply: wp_top; exact: CQPrimitive.measurement_complete.
rewrite Hm; apply/funext=>s; apply/val_inj.
change ((CQHoare.pre true qsvt_readout_prefix semantic_top s : 'End(Hq)) = \1).
rewrite /CQHoare.pre (execution_pre _ _ (qsvt_readout_execution s)).
change (qsvt_readout_channel^*o (\1 : 'End(Hq)) = \1).
exact: qu1_eq1.
Qed.

Theorem qsvt_heralded_total :
  CQHoare.derives true semantic_top qsvt_heralded semantic_top.
Proof.
rewrite -[in X in CQHoare.derives _ X _ _]qsvt_heralded_top_pre.
exact: CQHoare.derives_pre.
Qed.

Theorem qsvt_heralded_mass (rho : @CQState.state store Hq) :
  CQState.mass (CQHoare.run qsvt_heralded rho) = CQState.mass rho.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: CQKernel.apply_mass.
- have H := CQHoare.derives_sound qsvt_heralded_total rho.
  by move: H; rewrite /CQHoare.valid /semantic_top !CQAssertion.expect_identity
    -!CQState.mass_trace.
Qed.

End Program.
End QSVTClassicalProgram.

Module AncillaHeralding.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section Circuit.
Variable (T : ihbFinType) (V : bool -> 'FU('Hs T)).
Definition symmetric_circuit_raw : 'End('Hs T) :=
  (2%:R : hermitian.C)^-1 *: ((V false : 'End('Hs T)) + V true).
Lemma symmetric_circuit_bound : symmetric_circuit_raw \is bound1lf.
Proof.
rewrite bound1lf_i2fnormE /symmetric_circuit_raw i2fnormZ normrV ?unitfE ?pnatr_eq0 // normr_nat.
have Hhalf : (0 <= (2%:R : hermitian.C)^-1)%R by rewrite invr_ge0 ler0n.
apply: (le_trans (ler_wpM2l Hhalf (i2fnorm_triangle _ _))).
by rewrite !i2fnorm_isof -mulr2n -mulr_natl mulr1 mulVf // ?pnatr_eq0.
Qed.
Definition symmetric_circuit : 'FB1('Hs T) :=
  Bound1Lf_Build symmetric_circuit_bound.
Definition reset_kraus (i : bool) : 'End('Hs (bool*T)%type) :=
  [> (@uniformtv bool); ''i <] ⊗f (\1 : 'End('Hs T)).
Definition readout_circuit : 'FU('Hs (bool*T)%type) :=
  [unitary of (Hadamard ⊗f (\1 : 'FU('Hs T))) \o Multiplexer V].
Lemma ancilla_success_kraus i :
  ((@tmeas bool false) ⊗f (\1 : 'End('Hs T))) \o
    readout_circuit \o reset_kraus i =
  [> ''false; ''i <] ⊗f (symmetric_circuit : 'End('Hs T)).
Proof.
have Hanc : @tmeas bool false \o Hadamard =
    [> ''false; (@uniformtv bool) <].
  rewrite /tmeas -{1}Hadamard_adj -outp_comprV Hadamard0.
  by rewrite uniformtv_bool.
rewrite /readout_circuit /reset_kraus comp_lfunA tentf_comp
  comp_lfun1l Hanc MultiplexerE big_bool.
rewrite !linearDr !linearDl /= !tentf_comp !comp_lfun1l !comp_lfun1r.
rewrite uniformtv_bool !outp_comp !linearZl /=
  !dotp_pmcb ?dotp_cbpm /=.
rewrite !outp_comp !dotp_cbpm /= !sign_simp !tentfZl !scalerA !divc_simp.
by rewrite /symmetric_circuit_raw tentfZr tentfDr scalerDr [RHS]addrC.
Qed.
End Circuit.

Section Registers.
Import DefaultQMem.Exports.
Local Notation Hq := 'H[msys]_finset.setT.
Variable (T : qType) (qr : wf_qreg (QPair QBool T)).
Variable (V : bool -> 'FU('Ht T)).
Let qa : wf_qreg QBool :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid qr)).

Lemma ancilla_reset_global :
  liftfso (initialso (tv2v qa (@uniformtv (eval_qtype QBool)))) =
    krausso (fun i : bool => liftf_lf
      (tf2f qr qr (@reset_kraus (eval_qtype T) i))).
Proof.
rewrite -(initialso_onb _ (tv2v_fun _ qa t2tv)) liftfso_krausso.
congr (krausso _); apply/funext=>i.
by rewrite /liftf_fun /lift_fun /qmem.tv2v_fun /= tv2v_out /reset_kraus
  ClassicalRegisterTensor.lift_register_left.
Qed.

Definition success_channel : 'SO(Hq) :=
  liftfso (formso (tf2f qa qa (@tmeas (eval_qtype QBool) false))) :o
  liftfso (formso (tf2f qa qa Hadamard)) :o
  liftfso (formso (tf2f qr qr (Multiplexer V))) :o
  liftfso (initialso (tv2v qa (@uniformtv (eval_qtype QBool)))).

Lemma formso_after_kraus (H : chsType) (F : finType)
    (A : 'End(H)) (K : F -> 'End(H)) :
  formso A :o krausso K = krausso (fun i => A \o K i).
Proof.
apply/superopP=>rho.
rewrite comp_soE formsoE !kraussoE !linear_sumr !linear_sumlz /=.
by apply: eq_bigr=>i _; rewrite adjf_comp !comp_lfunA.
Qed.

Lemma register_success_kraus :
  success_channel = krausso (fun i : bool =>
    liftf_lf (tf2f qr qr ([> ''false; ''i <] ⊗f
      (symmetric_circuit V : 'End('Ht T))))).
Proof.
rewrite /success_channel
  !ClassicalRegisterTensor.channel_register_left
  !ClassicalAlgorithmSemantics.register_unitary_comp liftfso_formso ancilla_reset_global formso_after_kraus.
congr (krausso _); apply/funext=>i.
rewrite -liftf_lf_comp tf2f_comp.
rewrite -(comp_lfunA ((@tmeas (eval_qtype QBool) false) ⊗f (\1 : 'End('Ht T)))
  (Hadamard ⊗f (\1 : 'End('Ht T))) (Multiplexer V)).
change (liftf_lf (tf2f qr qr
  (((@tmeas (eval_qtype QBool) false) ⊗f (\1 : 'End('Ht T))) \o
    readout_circuit V \o (@reset_kraus (eval_qtype T) i))) =
  liftf_lf (tf2f qr qr ([> ''false; ''i <] ⊗f
    (symmetric_circuit V : 'End('Ht T))))).
by rewrite ancilla_success_kraus.
Qed.

Lemma register_success_wp (E : 'FO('Ht T)) :
  success_channel^*o (liftf_lf (tf2f qr qr
    ((\1 : 'End('Ht QBool)) ⊗f E))) =
  liftf_lf (tf2f qr qr ((\1 : 'End('Ht QBool)) ⊗f
    ((formso (symmetric_circuit V))^*o E))).
Proof.
rewrite register_success_kraus dualso_krausE.
under eq_bigr do rewrite -liftf_lf_adj -!liftf_lf_comp tf2f_adj !tf2f_comp
  tentf_adj !tentf_comp adj_outp ?comp_lfun1l ?comp_lfun1r
  outp_comp onb_dot eqxx scale1r.
rewrite -linear_sum /= -linear_sum /= -tentf_suml sumonb_out.
by rewrite dualso_formE.
Qed.

End Registers.

End AncillaHeralding.


Module QSVTHeraldedCorrectness.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics ClassicalAlgorithmSemantics.
Import CQAssertion CQPredicate QSVTClassicalProgram.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Section Program.
Variable (T : qType) (qr : wf_qreg (QPair QBool T)).
Variable (U : 'FU('Ht T)) (PiR PiL : 'FP('Ht T)).
Variable (d : nat) (phi : nat -> hermitian.R).
Variable (x : variable Integer) (y : variable (QType QBool)).
Let qa : wf_qreg QBool :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid qr)).
Let V := @sector_core T U PiR PiL d phi.

Section EncodingBridge.
Variables (HR HL : chsType).
Variables (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T)).
Hypothesis right_projector : PiR = QSVTModel.range_projector JR.
Hypothesis left_projector : PiL = QSVTModel.range_projector JL.

Theorem symmetric_circuit_encoding :
  (AncillaHeralding.symmetric_circuit V : 'End('Ht T)) =
    QSVTModel.success_operator U JR JL d phi d.
Proof.
have H0 : (@sector_core T U PiR PiL d phi false : 'End('Ht T)) =
    QSVTModel.qsvt_prefix U JR JL d phi d.
  exact: (@sector_core_prefix T U PiR PiL d phi HR HL JR JL
    right_projector left_projector false).
have H1 : (@sector_core T U PiR PiL d phi true : 'End('Ht T)) =
    QSVTModel.qsvt_prefix U JR JL d (fun j => -phi j) d.
  exact: (@sector_core_prefix T U PiR PiL d phi HR HL JR JL
    right_projector left_projector true).
change ((2 : hermitian.C)^-1 *:
  ((@sector_core T U PiR PiL d phi false : 'End('Ht T)) +
   @sector_core T U PiR PiL d phi true) =
  QSVTModel.success_operator U JR JL d phi d).
by rewrite H0 H1 /QSVTModel.success_operator.
Qed.
End EncodingBridge.

Definition qsvt_data_effect (E : 'FO('Ht T)) : 'FO(Hq) :=
  [obs of liftf_lf (tf2f qr qr ((\1 : 'FO('Ht QBool)) ⊗f E))].
Definition qsvt_success_pre (E : 'FO('Ht T)) : store -> 'FO(Hq) :=
  fun _ => qsvt_data_effect
    [obs of (formso (AncillaHeralding.symmetric_circuit V))^*o E].
Definition qsvt_success_post (E : 'FO('Ht T)) : store -> 'FO(Hq) :=
  fun s => if (((s.[x])%M == Posz d) && ((s.[y])%M == false))
    then qsvt_data_effect E else (0%:VF : 'FO(Hq)).

Lemma native_success_channel :
  @herald_branch T qr U PiR PiL d phi false =
    AncillaHeralding.success_channel qr V.
Proof.
change ((liftfso (formso (tf2f qa qa (@tmeas (eval_qtype QBool) false))) :o
  ((liftfso (formso (tf2f qa qa Hadamard)) :o
    liftfso (formso (tf2f qr qr (@coherent_core T U PiR PiL d phi)))) :o
    liftfso (initialso (tv2v qa (@uniformtv (eval_qtype QBool)))))) =
  AncillaHeralding.success_channel qr V).
by rewrite /AncillaHeralding.success_channel /V coherent_core_multiplexer
  !comp_soA.
Qed.

Lemma measurement_success_pre (E : 'FO('Ht T)) s :
  (s.[x])%M = Posz d ->
  (xp true (denote (Measure y qa
    (EConst [QM of @tmeas (eval_qtype QBool)])))
    (qsvt_success_post E) s : 'End(Hq)) =
  (liftfso (formso (tf2f qa qa (@tmeas (eval_qtype QBool) false))))^*o
    (qsvt_data_effect E).
Proof.
move=>Hs.
have Hcounter (b : bool) : ((s.[y <- b]).[x])%M = Posz d.
  by rewrite get_set_net //; discriminate.
rewrite CQPrimitive.measurement_pre big_bool /qsvt_success_post
  !get_set_eq !Hcounter !eqxx /=.
by rewrite comp_lfun0r comp_lfun0l add0r liftfso_formso dualso_formE.
Qed.

Theorem qsvt_heralded_circuit_preE (E : 'FO('Ht T)) s :
  (CQHoare.pre true (@qsvt_heralded T qr U PiR PiL d phi x y)
    (qsvt_success_post E) s : 'End(Hq)) = qsvt_success_pre E s.
Proof.
rewrite /qsvt_heralded CQHoare.pre_sequence /CQHoare.pre
  (execution_pre _ _ (@qsvt_readout_execution T qr U PiR PiL d phi x s)).
rewrite measurement_success_pre ?qsvt_final_counter //.
rewrite -comp_soE -dualso_comp -/(herald_branch _ _ _ _ _ _ false)
  native_success_channel.
rewrite /qsvt_data_effect /= AncillaHeralding.register_success_wp.
by rewrite /qsvt_success_pre /qsvt_data_effect /=.
Qed.

Theorem qsvt_heralded_circuit_correct (E : 'FO('Ht T)) :
  CQHoare.derives true (qsvt_success_pre E)
    (@qsvt_heralded T qr U PiR PiL d phi x y) (qsvt_success_post E).
Proof.
apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite qsvt_heralded_circuit_preE.
Qed.
Theorem qsvt_heralded_circuit_expect (E : 'FO('Ht T))
    (rho : @CQState.state store Hq) :
  expect (qsvt_success_pre E) rho =
    expect (qsvt_success_post E)
      (CQHoare.run (@qsvt_heralded T qr U PiR PiL d phi x y) rho).
Proof.
have Hpre : wp (denote (@qsvt_heralded T qr U PiR PiL d phi x y))
    (qsvt_success_post E) = qsvt_success_pre E.
  apply/funext=>s; apply/val_inj.
  change ((CQHoare.pre true (@qsvt_heralded T qr U PiR PiL d phi x y)
    (qsvt_success_post E) s : 'End(Hq)) = qsvt_success_pre E s).
  exact: qsvt_heralded_circuit_preE.
by rewrite /CQHoare.run -expect_wp Hpre.
Qed.
End Program.
End QSVTHeraldedCorrectness.

Module QSVTPolynomialHoareHelpers.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics ClassicalAlgorithmSemantics.
Import CQAssertion CQPredicate QSVTClassicalProgram QSVTHeraldedCorrectness.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Section Compression.
Variables (H HR HL : chsType).
Variables (JR : 'FI(HR,H)) (JO : 'FI(HL,H)).
Variable (S : 'FB1(H)) (F : 'Hom(HR,HL)).

Lemma column_compression_bound : S \o JR = JO \o F ->
  F \is bound1lf.
Proof.
move=>Hcol.
have HF : F = JO^A \o S \o JR.
  by rewrite -comp_lfunA Hcol comp_lfunA isofE comp_lfun1l.
rewrite HF; apply/bound1lf_comp; last exact: is_bound1lf.
apply/bound1lf_comp; exact: is_bound1lf.
Qed.

Lemma row_effect_pullback (E : 'FO(HL)) :
  S^A \o JO = JR \o F^A ->
  (formso S)^*o (formlf JO E) =
    formlf JR ((formso F)^*o E).
Proof.
move=>Hrow.
have HrowA : JO^A \o S = F \o JR^A.
  by move: (congr1 adj_lfun Hrow); rewrite !adjf_comp !adjfK.
rewrite !dualso_formE !formlfE !comp_lfunA.
by rewrite Hrow -!comp_lfunA HrowA.
Qed.
End Compression.

Section Program.
Variable (T : qType) (qr : wf_qreg (QPair QBool T)).
Variable (U : 'FU('Ht T)) (PiR PiL : 'FP('Ht T)).
Variable (d : nat) (phi : nat -> hermitian.R).
Variable (x : variable Integer) (y : variable (QType QBool)).
Variables (HR HL : chsType).
Variables (JR : 'FI(HR,'Ht T)) (JO : 'FI(HL,'Ht T)).
Variable (F : 'FB1(HR,HL)).
Let V := @sector_core T U PiR PiL d phi.
Let S := AncillaHeralding.symmetric_circuit V.
Hypothesis polynomial_row : S^A \o JO = JR \o F^A.

Definition polynomial_input_effect (E : 'FO(HL)) : 'FO('Ht T) :=
  [obs of formlf JR ((formso F)^*o E)].
Definition polynomial_output_effect (E : 'FO(HL)) : 'FO('Ht T) :=
  [obs of formlf JO E].
Definition polynomial_pre (E : 'FO(HL)) : store -> 'FO(Hq) :=
  fun _ => @qsvt_data_effect T qr (polynomial_input_effect E).
Definition polynomial_post (E : 'FO(HL)) : store -> 'FO(Hq) :=
  @qsvt_success_post T qr d x y
    (polynomial_output_effect E).

Theorem polynomial_preE (E : 'FO(HL)) s :
  (CQHoare.pre true (@qsvt_heralded T qr U PiR PiL d phi x y)
    (polynomial_post E) s : 'End(Hq)) = polynomial_pre E s.
Proof.
rewrite /polynomial_post qsvt_heralded_circuit_preE
  /qsvt_success_pre /polynomial_pre /qsvt_data_effect /=.
by rewrite (row_effect_pullback E polynomial_row).
Qed.

Theorem polynomial_correct (E : 'FO(HL)) :
  CQHoare.derives true (polynomial_pre E)
    (@qsvt_heralded T qr U PiR PiL d phi x y) (polynomial_post E).
Proof.
apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite polynomial_preE.
Qed.

Theorem polynomial_expect (E : 'FO(HL))
    (rho : @CQState.state store Hq) :
  expect (polynomial_pre E) rho =
  expect (polynomial_post E)
    (CQHoare.run (@qsvt_heralded T qr U PiR PiL d phi x y) rho).
Proof.
have Hpre : wp (denote (@qsvt_heralded T qr U PiR PiL d phi x y))
    (polynomial_post E) = polynomial_pre E.
  apply/funext=>s; apply/val_inj.
  change ((CQHoare.pre true (@qsvt_heralded T qr U PiR PiL d phi x y)
    (polynomial_post E) s : 'End(Hq)) = polynomial_pre E s).
  exact: polynomial_preE.
by rewrite /CQHoare.run -expect_wp Hpre.
Qed.
End Program.
End QSVTPolynomialHoareHelpers.

Module QSVTFailureSemantics.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import AncillaHeralding.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section Circuit.
Variable (T : ihbFinType) (V : bool -> 'FU('Hs T)).
Definition antisymmetric_circuit_raw : 'End('Hs T) :=
  (2 : hermitian.C)^-1 *: ((V false : 'End('Hs T)) - (V true : 'End('Hs T))).
Lemma antisymmetric_circuit_bound : antisymmetric_circuit_raw \is bound1lf.
Proof.
rewrite bound1lf_i2fnormE /antisymmetric_circuit_raw i2fnormZ
  normrV ?unitfE ?pnatr_eq0 // normr_nat.
have Hhalf : (0 <= (2 : hermitian.C)^-1)%R by rewrite invr_ge0 ler0n.
apply: (le_trans (ler_wpM2l Hhalf (i2fnorm_triangle _ _))).
have HN : i2fnorm (- (V true : 'End('Hs T))) = 1.
  by rewrite -scaleN1r i2fnormZ normrN normr1 mul1r i2fnorm_isof.
by rewrite HN i2fnorm_isof -mulr2n -mulr_natl mulr1 mulVf // ?pnatr_eq0.
Qed.
Definition antisymmetric_circuit : 'FB1('Hs T) :=
  Bound1Lf_Build antisymmetric_circuit_bound.
Lemma ancilla_failure_kraus i :
  ((@tmeas bool true) ⊗f (\1 : 'End('Hs T))) \o
    readout_circuit V \o reset_kraus T i =
  [> ''true; ''i <] ⊗f (antisymmetric_circuit : 'End('Hs T)).
Proof.
have Hanc : @tmeas bool true \o Hadamard = [> ''true; pmbasis true <].
  by rewrite /tmeas -{1}Hadamard_adj -outp_comprV Hadamard1.
rewrite /readout_circuit /reset_kraus comp_lfunA tentf_comp
  comp_lfun1l Hanc MultiplexerE big_bool.
rewrite !linearDr !linearDl /= !tentf_comp !comp_lfun1l !comp_lfun1r.
rewrite uniformtv_bool !outp_comp !linearZl /= !dotp_pmcb ?dotp_cbpm /=.
rewrite !outp_comp !dotp_cbpm /= !sign_simp !tentfZl !scalerA !divc_simp.
rewrite /antisymmetric_circuit_raw tentfZr tentfDr tentfNr
  scalerDr scalerN ?scaleNr [RHS]addrC.
by rewrite mulNr !divc_simp scaleNr.
Qed.
End Circuit.
Section Registers.
Import DefaultQMem.Exports.
Local Notation Hq := 'H[msys]_finset.setT.
Variable (T : qType) (qr : wf_qreg (QPair QBool T)).
Variable (V : bool -> 'FU('Ht T)).
Let qa : wf_qreg QBool :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid qr)).
Definition failure_channel : 'SO(Hq) :=
  liftfso (formso (tf2f qa qa (@tmeas (eval_qtype QBool) true))) :o
  liftfso (formso (tf2f qa qa Hadamard)) :o
  liftfso (formso (tf2f qr qr (Multiplexer V))) :o
  liftfso (initialso (tv2v qa (@uniformtv (eval_qtype QBool)))).

Theorem register_failure_kraus :
  failure_channel = krausso (fun i : bool =>
    liftf_lf (tf2f qr qr ([> ''true; ''i <] ⊗f
      (antisymmetric_circuit V : 'End('Ht T))))).
Proof.
rewrite /failure_channel !ClassicalRegisterTensor.channel_register_left
  !ClassicalAlgorithmSemantics.register_unitary_comp liftfso_formso
  ancilla_reset_global formso_after_kraus.
congr (krausso _); apply/funext=>i.
rewrite -liftf_lf_comp tf2f_comp.
rewrite -(comp_lfunA ((@tmeas (eval_qtype QBool) true) ⊗f (\1 : 'End('Ht T)))
  (Hadamard ⊗f (\1 : 'End('Ht T))) (Multiplexer V)).
change (liftf_lf (tf2f qr qr
  (((@tmeas (eval_qtype QBool) true) ⊗f (\1 : 'End('Ht T))) \o
    readout_circuit V \o (@reset_kraus (eval_qtype T) i))) =
  liftf_lf (tf2f qr qr ([> ''true; ''i <] ⊗f
    (antisymmetric_circuit V : 'End('Ht T))))).
by rewrite ancilla_failure_kraus.
Qed.
End Registers.

End QSVTFailureSemantics.

Module QSVTPolynomialCorrectness.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics ClassicalAlgorithmSemantics.
Import CQAssertion CQPredicate QSVTClassicalProgram QSVTHeraldedCorrectness.
Import QSVTPolynomialHoareHelpers QSVTModel QSVTRows.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.
Local Notation Hq := 'H[msys]_finset.setT.

Section Native.
Variable (T : qType) (qr : wf_qreg (QPair QBool T)).
Variables (HR HL : chsType) (U : 'FU('Ht T)).
Variables (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T)).
Variables (d : nat) (phi : nat -> R) (p : {poly C}).
Hypothesis Hp : poly_real (scalar_pair d phi d).1 = p.
Hypothesis Hq0 : poly_real (scalar_pair d phi d).2 = 0.
Variables (x : variable Integer) (y : variable (QType QBool)).
Let PR := range_projector JR.
Let PL := range_projector JL.
Let V := @sector_core T U PR PL d phi.
Let S := AncillaHeralding.symmetric_circuit V.
Let A := encoded U JR JL.
Definition polynomial_command : command :=
  @qsvt_heralded T qr U PR PL d phi x y.

Lemma native_success_encoding : (S : 'End('Ht T)) =
  success_operator U JR JL d phi d.
Proof.
exact: (@symmetric_circuit_encoding T U PR PL d phi HR HL JR JL erefl erefl).
Qed.

Lemma native_even_column (Hd : odd d = false) :
  S \o JR = JR \o sv_even p A.
Proof.
by rewrite native_success_encoding (real_qsvt_success_even U JR JL Hd Hq0) Hp.
Qed.
Lemma native_odd_column (Hd : odd d = true) :
  S \o JR = JL \o sv_odd p A.
Proof.
by rewrite native_success_encoding (real_qsvt_success_odd U JR JL Hd Hq0) Hp.
Qed.
Lemma native_even_row (Hd : odd d = false) :
  S^A \o JR = JR \o (sv_even p A)^A.
Proof.
by rewrite native_success_encoding (real_qsvt_row_even U JR JL Hd Hq0) Hp.
Qed.
Lemma native_odd_row (Hd : odd d = true) :
  S^A \o JL = JR \o (sv_odd p A)^A.
Proof.
by rewrite native_success_encoding (real_qsvt_row_odd U JR JL Hd Hq0) Hp.
Qed.

Lemma even_target_bound (Hd : odd d = false) : sv_even p A \is bound1lf.
Proof. exact: column_compression_bound (native_even_column Hd). Qed.
Lemma odd_target_bound (Hd : odd d = true) : sv_odd p A \is bound1lf.
Proof. exact: column_compression_bound (native_odd_column Hd). Qed.
Definition even_target (Hd : odd d = false) : 'FB1(HR) :=
  Bound1Lf_Build (even_target_bound Hd).
Definition odd_target (Hd : odd d = true) : 'FB1(HR,HL) :=
  Bound1Lf_Build (odd_target_bound Hd).

Definition even_pre (Hd : odd d = false) (E : 'FO(HR)) :=
  polynomial_pre qr JR (even_target Hd) E.
Definition odd_pre (Hd : odd d = true) (E : 'FO(HL)) :=
  polynomial_pre qr JR (odd_target Hd) E.
Definition even_post (E : 'FO(HR)) := polynomial_post qr d x y JR E.
Definition odd_post (E : 'FO(HL)) := polynomial_post qr d x y JL E.

Theorem even_preE (Hd : odd d = false) (E : 'FO(HR)) s :
  (CQHoare.pre true polynomial_command (even_post E) s : 'End(Hq)) =
    even_pre Hd E s.
Proof.
exact: (@polynomial_preE T qr U PR PL d phi x y HR HR JR JR
  (even_target Hd) (native_even_row Hd) E s).
Qed.
Theorem odd_preE (Hd : odd d = true) (E : 'FO(HL)) s :
  (CQHoare.pre true polynomial_command (odd_post E) s : 'End(Hq)) =
    odd_pre Hd E s.
Proof.
exact: (@polynomial_preE T qr U PR PL d phi x y HR HL JR JL
  (odd_target Hd) (native_odd_row Hd) E s).
Qed.
Theorem even_correct (Hd : odd d = false) (E : 'FO(HR)) :
  CQHoare.derives true (even_pre Hd E) polynomial_command (even_post E).
Proof.
exact: (@polynomial_correct T qr U PR PL d phi x y HR HR JR JR
  (even_target Hd) (native_even_row Hd) E).
Qed.
Theorem odd_correct (Hd : odd d = true) (E : 'FO(HL)) :
  CQHoare.derives true (odd_pre Hd E) polynomial_command (odd_post E).
Proof.
exact: (@polynomial_correct T qr U PR PL d phi x y HR HL JR JL
  (odd_target Hd) (native_odd_row Hd) E).
Qed.
Theorem even_expect (Hd : odd d = false) (E : 'FO(HR))
    (rho : @CQState.state store Hq) :
  expect (even_pre Hd E) rho =
    expect (even_post E) (CQHoare.run polynomial_command rho).
Proof.
exact: (@polynomial_expect T qr U PR PL d phi x y HR HR JR JR
  (even_target Hd) (native_even_row Hd) E rho).
Qed.
Theorem odd_expect (Hd : odd d = true) (E : 'FO(HL))
    (rho : @CQState.state store Hq) :
  expect (odd_pre Hd E) rho =
    expect (odd_post E) (CQHoare.run polynomial_command rho).
Proof.
exact: (@polynomial_expect T qr U PR PL d phi x y HR HL JR JL
  (odd_target Hd) (native_odd_row Hd) E rho).
Qed.
End Native.

Theorem qsvt_framework_and_program d (p : {poly R}) :
  QSVTRealPair.admissible d p ->
  exists phi : nat -> R,
  exists Hp : poly_real (scalar_pair d phi d).1 = QSVTRealPair.r_embed p,
  exists Hq0 : poly_real (scalar_pair d phi d).2 = 0,
  forall (T : qType) (qr : wf_qreg (QPair QBool T))
    (HR HL : chsType) (U : 'FU('Ht T))
    (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T))
    (x : variable Integer) (y : variable (QType QBool)),
  (forall (Hd : odd d = false) (E : 'FO(HR)),
    CQHoare.derives true
      (@even_pre T qr HR HL U JR JL d phi (QSVTRealPair.r_embed p) Hp Hq0 Hd E)
      (@polynomial_command T qr HR HL U JR JL d phi x y)
      (@even_post T qr HR JR d x y E)) /\
  (forall (Hd : odd d = true) (E : 'FO(HL)),
    CQHoare.derives true
      (@odd_pre T qr HR HL U JR JL d phi (QSVTRealPair.r_embed p) Hp Hq0 Hd E)
      (@polynomial_command T qr HR HL U JR JL d phi x y)
      (@odd_post T qr HL JL d x y E)).
Proof.
move=>ha.
have [phi [Hp Hq0]] := QSVTUniformPhase.real_polynomial_phase_witness ha.
exists phi,Hp,Hq0=>T qr HR HL U JR JL x y; split=>Hd E.
- exact: (@even_correct T qr HR HL U JR JL d phi _ Hp Hq0 x y Hd E).
- exact: (@odd_correct T qr HR HL U JR JL d phi _ Hp Hq0 x y Hd E).
Qed.
End QSVTPolynomialCorrectness.

Module QSVTNativeStateCorrectness.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics ClassicalAlgorithmSemantics.
Import CQAssertion CQPredicate QSVTClassicalProgram QSVTHeraldedCorrectness.
Import QSVTPolynomialHoareHelpers QSVTModel QSVTPolynomialCorrectness.
Import QSVTImaginaryColumns.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.
Local Notation Hq := 'H[msys]_finset.setT.

Section Native.
Variable (T : qType) (qr : wf_qreg (QPair QBool T)).
Variables (HR HL : chsType) (U : 'FU('Ht T)).
Variables (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T)).
Variables (d : nat) (phi : nat -> R) (p : {poly C}).
Hypothesis Hp : poly_real (scalar_pair d phi d).1 = p.
Hypothesis Hq0 : poly_real (scalar_pair d phi d).2 = 0.
Variables (x : variable Integer) (y : variable (QType QBool)).
Let PR := range_projector JR.
Let PL := range_projector JL.
Let V := @sector_core T U PR PL d phi.
Let S := AncillaHeralding.symmetric_circuit V.
Let D := QSVTFailureSemantics.antisymmetric_circuit V.
Let A := encoded U JR JL.

Theorem native_even_success_density (Hd : odd d = false) (rho : 'End(HR)) :
  formso S (formlf JR rho) = formlf JR (formlf (sv_even p A) rho).
Proof.
apply: encoded_success_density.
exact: (@native_even_column T HR HL U JR JL d phi p Hp Hq0 Hd).
Qed.
Theorem native_odd_success_density (Hd : odd d = true) (rho : 'End(HR)) :
  formso S (formlf JR rho) = formlf JL (formlf (sv_odd p A) rho).
Proof.
apply: encoded_success_density.
exact: (@native_odd_column T HR HL U JR JL d phi p Hp Hq0 Hd).
Qed.

Theorem native_even_success_mass (Hd : odd d = false) (rho : 'End(HR)) :
  \Tr (formso S (formlf JR rho)) = \Tr (formso (sv_even p A) rho).
Proof.
by rewrite (native_even_success_density Hd) [formlf JR _]formlfE
  lftraceC comp_lfunA isofE comp_lfun1l formlf_soE.
Qed.
Theorem native_odd_success_mass (Hd : odd d = true) (rho : 'End(HR)) :
  \Tr (formso S (formlf JR rho)) = \Tr (formso (sv_odd p A) rho).
Proof.
by rewrite (native_odd_success_density Hd) [formlf JL _]formlfE
  lftraceC comp_lfunA isofE comp_lfun1l formlf_soE.
Qed.

Lemma native_failure_encoding : (D : 'End('Ht T)) =
  difference_operator U JR JL d phi d.
Proof.
have H0 := @sector_core_prefix T U PR PL d phi HR HL JR JL erefl erefl false.
have H1 := @sector_core_prefix T U PR PL d phi HR HL JR JL erefl erefl true.
change ((2:C)^-1 *:
  ((@sector_core T U PR PL d phi false : 'End('Ht T)) -
   (@sector_core T U PR PL d phi true : 'End('Ht T))) =
    difference_operator U JR JL d phi d).
by rewrite H0 H1 /difference_operator.
Qed.

Theorem native_even_failure_column (Hd : odd d = false) :
  D \o JR = ('i%C : C) *: failure_column_even U JR JL d phi d.
Proof.
rewrite native_failure_encoding; exact: explicit_failure_column_even Hd.
Qed.
Theorem native_odd_failure_column (Hd : odd d = true) :
  D \o JR = ('i%C : C) *: failure_column_odd U JR JL d phi d.
Proof.
rewrite native_failure_encoding; exact: explicit_failure_column_odd Hd.
Qed.

Theorem native_even_failure_density (Hd : odd d = false) (rho : 'End(HR)) :
  formso D (formlf JR rho) = formlf (failure_column_even U JR JL d phi d) rho.
Proof.
apply: encoded_failure_density; exact: native_even_failure_column Hd.
Qed.
Theorem native_odd_failure_density (Hd : odd d = true) (rho : 'End(HR)) :
  formso D (formlf JR rho) = formlf (failure_column_odd U JR JL d phi d) rho.
Proof.
apply: encoded_failure_density; exact: native_odd_failure_column Hd.
Qed.

Theorem even_source_contract (Hd : odd d = false) :
  @qsvt_polynomial_contract T qr U PR PL d phi x y HR HR JR JR
    (@even_target T HR HL U JR JL d phi p Hp Hq0 Hd).
Proof.
move=>E; exact: (@even_correct T qr HR HL U JR JL d phi p Hp Hq0 x y Hd E).
Qed.
Theorem odd_source_contract (Hd : odd d = true) :
  @qsvt_polynomial_contract T qr U PR PL d phi x y HR HL JR JL
    (@odd_target T HR HL U JR JL d phi p Hp Hq0 Hd).
Proof.
move=>E; exact: (@odd_correct T qr HR HL U JR JL d phi p Hp Hq0 x y Hd E).
Qed.

(* One witness satisfies the source contracts, global totality and exact
   expectations, and both unnormalized encoded branch specifications. *)
Definition native_exact_contract :=
  (forall Hd : odd d = false,
    @qsvt_polynomial_contract T qr U PR PL d phi x y HR HR JR JR
      (@even_target T HR HL U JR JL d phi p Hp Hq0 Hd)) /\
  (forall Hd : odd d = true,
    @qsvt_polynomial_contract T qr U PR PL d phi x y HR HL JR JL
      (@odd_target T HR HL U JR JL d phi p Hp Hq0 Hd)) /\
  CQHoare.derives true semantic_top
    (@polynomial_command T qr HR HL U JR JL d phi x y) semantic_top /\
  (forall rho : @CQState.state store Hq,
    CQState.mass (CQHoare.run
      (@polynomial_command T qr HR HL U JR JL d phi x y) rho) =
    CQState.mass rho) /\
  (forall (Hd : odd d = false) (E : 'FO(HR)) (rho : @CQState.state store Hq),
    expect (@even_pre T qr HR HL U JR JL d phi p Hp Hq0 Hd E) rho =
    expect (@even_post T qr HR JR d x y E)
      (CQHoare.run (@polynomial_command T qr HR HL U JR JL d phi x y) rho)) /\
  (forall (Hd : odd d = true) (E : 'FO(HL)) (rho : @CQState.state store Hq),
    expect (@odd_pre T qr HR HL U JR JL d phi p Hp Hq0 Hd E) rho =
    expect (@odd_post T qr HL JL d x y E)
      (CQHoare.run (@polynomial_command T qr HR HL U JR JL d phi x y) rho)) /\
  (forall (Hd : odd d = false) (rho : 'End(HR)),
    [ /\ formso S (formlf JR rho) = formlf JR (formlf (sv_even p A) rho),
         formso D (formlf JR rho) = formlf (failure_column_even U JR JL d phi d) rho
       & \Tr (formso S (formlf JR rho)) = \Tr (formso (sv_even p A) rho)]) /\
  (forall (Hd : odd d = true) (rho : 'End(HR)),
    [ /\ formso S (formlf JR rho) = formlf JL (formlf (sv_odd p A) rho),
         formso D (formlf JR rho) = formlf (failure_column_odd U JR JL d phi d) rho
       & \Tr (formso S (formlf JR rho)) = \Tr (formso (sv_odd p A) rho)]).

Theorem native_exact_contract_holds : native_exact_contract.
Proof.
split; first exact: even_source_contract.
split; first exact: odd_source_contract.
split; first exact: (@qsvt_heralded_total T qr U PR PL d phi x y).
split; first exact: (@qsvt_heralded_mass T qr U PR PL d phi x y).
split; first exact: (@even_expect T qr HR HL U JR JL d phi p Hp Hq0 x y).
split; first exact: (@odd_expect T qr HR HL U JR JL d phi p Hp Hq0 x y).
split=>Hd rho; split.
- exact: native_even_success_density Hd rho.
- exact: native_even_failure_density Hd rho.
- exact: native_even_success_mass Hd rho.
- exact: native_odd_success_density Hd rho.
- exact: native_odd_failure_density Hd rho.
- exact: native_odd_success_mass Hd rho.
Qed.
End Native.

Theorem qsvt_native_framework_contract d (p : {poly R}) :
  QSVTRealPair.admissible d p ->
  exists phi : nat -> R,
  exists Hp : poly_real (scalar_pair d phi d).1 = QSVTRealPair.r_embed p,
  exists Hq0 : poly_real (scalar_pair d phi d).2 = 0,
  forall (T : qType) (qr : wf_qreg (QPair QBool T))
    (HR HL : chsType) (U : 'FU('Ht T))
    (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T))
    (x : variable Integer) (y : variable (QType QBool)),
  (forall Hd : odd d = false,
    @qsvt_polynomial_contract T qr U (range_projector JR) (range_projector JL)
      d phi x y HR HR JR JR
      (@even_target T HR HL U JR JL d phi (QSVTRealPair.r_embed p) Hp Hq0 Hd)) /\
  (forall Hd : odd d = true,
    @qsvt_polynomial_contract T qr U (range_projector JR) (range_projector JL)
      d phi x y HR HL JR JL
      (@odd_target T HR HL U JR JL d phi (QSVTRealPair.r_embed p) Hp Hq0 Hd)).
Proof.
move=>ha.
have [phi [Hp Hq0]] := QSVTUniformPhase.real_polynomial_phase_witness ha.
exists phi,Hp,Hq0=>T qr HR HL U JR JL x y; split=>Hd.
- exact: (@even_source_contract T qr HR HL U JR JL d phi _ Hp Hq0 x y Hd).
- exact: (@odd_source_contract T qr HR HL U JR JL d phi _ Hp Hq0 x y Hd).
Qed.

Theorem qsvt_framework_exact d (p : {poly R}) :
  QSVTRealPair.admissible d p ->
  exists phi : nat -> R,
  exists Hp : poly_real (scalar_pair d phi d).1 = QSVTRealPair.r_embed p,
  exists Hq0 : poly_real (scalar_pair d phi d).2 = 0,
  forall (T : qType) (qr : wf_qreg (QPair QBool T))
    (HR HL : chsType) (U : 'FU('Ht T))
    (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T))
    (x : variable Integer) (y : variable (QType QBool)),
  @native_exact_contract T qr HR HL U JR JL d phi (QSVTRealPair.r_embed p) Hp Hq0 x y.
Proof.
move=>ha.
have [phi [Hp Hq0]] := QSVTUniformPhase.real_polynomial_phase_witness ha.
exists phi,Hp,Hq0=>T qr HR HL U JR JL x y.
exact: (@native_exact_contract_holds T qr HR HL U JR JL d phi _ Hp Hq0 x y).
Qed.
End QSVTNativeStateCorrectness.

Module QSVTNormCompleteness.
Import AncillaHeralding QSVTFailureSemantics.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section Circuit.
Variables (T : ihbFinType) (V : bool -> 'FU('Hs T)).
Lemma symmetric_antisymmetric_complete :
  ((symmetric_circuit V)^A \o symmetric_circuit V) +
    ((antisymmetric_circuit V)^A \o antisymmetric_circuit V) = (\1 : 'End('Hs T)).
Proof.
apply/lfunP=>v; apply/intro_dotl=>w.
have HV (b : bool) (u z : 'Hs T) : [<V b u; V b z>] = [<u;z>].
  by rewrite -adj_dotEr isofKE.
rewrite add_lfunE !comp_lfunE id_lfunE dotpDr !adj_dotEr.
rewrite /symmetric_circuit /antisymmetric_circuit /=
  /symmetric_circuit_raw /antisymmetric_circuit_raw !scale_lfunE !add_lfunE !opp_lfunE /=
  !dotpZl !dotpZr !dotpDl !dotpDr !dotpNl !dotpNr.
rewrite rmorphV ?unitfE ?pnatr_eq0 // rmorph_nat !HV.
transitivity (((2 : hermitian.C)^-1 * 2) *
  ((2 : hermitian.C)^-1 * 2) * [<w;v>]); first ring.
have h2 : (2 : hermitian.C) != 0 by rewrite pnatr_eq0.
by rewrite (mulVf h2) !mul1r.
Qed.

End Circuit.
End QSVTNormCompleteness.

Module QSVTNativeCompleteness.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import QSVTModel QSVTClassicalProgram QSVTPolynomialCorrectness.
Import QSVTImaginaryColumns QSVTNativeStateCorrectness.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Section Compression.
Variables (H HR HO : chsType).
Variables (JR : 'FI(HR,H)) (JO : 'FI(HO,H)).
Variables (S D : 'End(H)) (F : 'Hom(HR,HO)) (Gamma : 'Hom(HR,H)).

Lemma compressed_completeness :
  (S^A \o S) + (D^A \o D) = \1 ->
  S \o JR = JO \o F -> D \o JR = ('i%C : C) *: Gamma ->
  (F^A \o F) + (Gamma^A \o Gamma) = \1.
Proof.
move=>Hsum Hs Hd.
have HF : (S \o JR)^A \o (S \o JR) = F^A \o F.
  by rewrite Hs adjf_comp !comp_lfunA isofK.
have HG : (D \o JR)^A \o (D \o JR) = Gamma^A \o Gamma.
  rewrite Hd adjfZ -!comp_lfunZl -!comp_lfunZr scalerA.
  have hi : (('i%C : C)^*%C) * 'i%C = 1 by simpc.
  by rewrite hi scale1r.
rewrite -HF -HG !adjf_comp !comp_lfunA.
have Hcompressed := congr1 (fun K : 'End(H) => JR^A \o K \o JR) Hsum.
by move: Hcompressed; rewrite comp_lfunDr comp_lfunDl !comp_lfunA comp_lfun1r isofE.
Qed.
End Compression.

Section Trace.
Variables (HR HO H : chsType).
Variables (F : 'Hom(HR,HO)) (Gamma : 'Hom(HR,H)).
Lemma complete_branch_mass (rho : 'End(HR)) :
  (F^A \o F) + (Gamma^A \o Gamma) = \1 ->
  \Tr (formso F rho) + \Tr (formso Gamma rho) = \Tr rho.
Proof.
move=>Hgram; rewrite !formsoE.
rewrite [\Tr (F \o rho \o F^A)]lftraceC
  [\Tr (Gamma \o rho \o Gamma^A)]lftraceC !comp_lfunA
  -linearD -comp_lfunDl Hgram comp_lfun1l.
by [].
Qed.
End Trace.

Section Native.
Variable (T : qType).
Variables (HR HL : chsType) (U : 'FU('Ht T)).
Variables (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T)).
Variables (d : nat) (phi : nat -> R) (p : {poly C}).
Hypothesis Hp : poly_real (scalar_pair d phi d).1 = p.
Hypothesis Hq0 : poly_real (scalar_pair d phi d).2 = 0.
Let V := @sector_core T U (range_projector JR) (range_projector JL) d phi.
Let S := AncillaHeralding.symmetric_circuit V.
Let D := QSVTFailureSemantics.antisymmetric_circuit V.
Let A := encoded U JR JL.
Let Ge := failure_column_even U JR JL d phi d.
Let Go := failure_column_odd U JR JL d phi d.

Theorem native_even_completion_gram (Hd : odd d = false) :
  ((sv_even p A)^A \o sv_even p A) + (Ge^A \o Ge) = \1.
Proof.
apply: (@compressed_completeness ('Ht T) HR HR JR JR S D (sv_even p A) Ge).
- exact: QSVTNormCompleteness.symmetric_antisymmetric_complete.
- exact: (@native_even_column T HR HL U JR JL d phi p Hp Hq0 Hd).
- exact: (@native_even_failure_column T HR HL U JR JL d phi Hd).
Qed.

Theorem native_odd_completion_gram (Hd : odd d = true) :
  ((sv_odd p A)^A \o sv_odd p A) + (Go^A \o Go) = \1.
Proof.
apply: (@compressed_completeness ('Ht T) HR HL JR JL S D (sv_odd p A) Go).
- exact: QSVTNormCompleteness.symmetric_antisymmetric_complete.
- exact: (@native_odd_column T HR HL U JR JL d phi p Hp Hq0 Hd).
- exact: (@native_odd_failure_column T HR HL U JR JL d phi Hd).
Qed.

Theorem native_even_logical_mass (Hd : odd d = false) (rho : 'End(HR)) :
  \Tr (formso (sv_even p A) rho) + \Tr (formso Ge rho) = \Tr rho.
Proof. exact: complete_branch_mass rho (native_even_completion_gram Hd). Qed.
Theorem native_odd_logical_mass (Hd : odd d = true) (rho : 'End(HR)) :
  \Tr (formso (sv_odd p A) rho) + \Tr (formso Go rho) = \Tr rho.
Proof. exact: complete_branch_mass rho (native_odd_completion_gram Hd). Qed.

Theorem native_even_outcome_mass (Hd : odd d = false) (rho : 'End(HR)) :
  \Tr (formso S (formlf JR rho)) + \Tr (formso D (formlf JR rho)) = \Tr rho.
Proof.
rewrite (@native_even_success_mass T HR HL U JR JL d phi p Hp Hq0 Hd rho)
  (@native_even_failure_density T HR HL U JR JL d phi Hd rho) formlf_soE.
exact: native_even_logical_mass Hd rho.
Qed.
Theorem native_odd_outcome_mass (Hd : odd d = true) (rho : 'End(HR)) :
  \Tr (formso S (formlf JR rho)) + \Tr (formso D (formlf JR rho)) = \Tr rho.
Proof.
rewrite (@native_odd_success_mass T HR HL U JR JL d phi p Hp Hq0 Hd rho)
  (@native_odd_failure_density T HR HL U JR JL d phi Hd rho) formlf_soE.
exact: native_odd_logical_mass Hd rho.
Qed.
End Native.

Theorem qsvt_framework_complete d (p : {poly R}) :
  QSVTRealPair.admissible d p ->
  exists phi : nat -> R,
  exists Hp : poly_real (scalar_pair d phi d).1 = QSVTRealPair.r_embed p,
  exists Hq0 : poly_real (scalar_pair d phi d).2 = 0,
  forall (T : qType) (qr : wf_qreg (QPair QBool T))
    (HR HL : chsType) (U : 'FU('Ht T))
    (JR : 'FI(HR,'Ht T)) (JL : 'FI(HL,'Ht T))
    (x : ClassicalLanguage.variable ClassicalLanguage.Integer)
    (y : ClassicalLanguage.variable (QType QBool)),
  @native_exact_contract T qr HR HL U JR JL d phi (QSVTRealPair.r_embed p) Hp Hq0 x y /\
  (forall Hd : odd d = false,
    ((sv_even (QSVTRealPair.r_embed p) (encoded U JR JL))^A \o
      sv_even (QSVTRealPair.r_embed p) (encoded U JR JL)) +
    ((failure_column_even U JR JL d phi d)^A \o
      failure_column_even U JR JL d phi d) = \1) /\
  (forall Hd : odd d = true,
    ((sv_odd (QSVTRealPair.r_embed p) (encoded U JR JL))^A \o
      sv_odd (QSVTRealPair.r_embed p) (encoded U JR JL)) +
    ((failure_column_odd U JR JL d phi d)^A \o
      failure_column_odd U JR JL d phi d) = \1).
Proof.
move=>ha.
have [phi [Hp Hq0]] := QSVTUniformPhase.real_polynomial_phase_witness ha.
exists phi,Hp,Hq0=>T qr HR HL U JR JL x y.
split; first exact: (@native_exact_contract_holds T qr HR HL U JR JL d phi _ Hp Hq0 x y).
split=>Hd.
- exact: (@native_even_completion_gram T HR HL U JR JL d phi _ Hp Hq0 Hd).
- exact: (@native_odd_completion_gram T HR HL U JR JL d phi _ Hp Hq0 Hd).
Qed.
End QSVTNativeCompleteness.

