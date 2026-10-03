(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import footprint.
From quantum.example.distributive Require Import language operational scheduler local_actions instruments interchange progress observables distribution sequentialization guarded_rules weighted local_diamond.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.classical Require Import assertion kernel predicate rules primitive.

Module DistributedLocalCorrespondence.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions
  DistributedInstruments DistributedProgress DistributedObservables DistributedDistribution
  DistributedSequentialization DistributedGuardedRules DistributedWeighted
  CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition atom_maps (a : atom) m : {vdistr atom_index a -> 'SO(Hq)} :=
  match a as a' return {vdistr atom_index a' -> 'SO(Hq)} with
  | ARandom _ _ p => sdistr Hq (esem (CL.probability_expression p) m)
  | AInitial _ q phi => sunit_vdistr tt (liftfso (initialso (tv2v q (eval phi m))))
  | AUnitary _ q U => sunit_vdistr tt (liftfso (formso (tf2f q q (eval U m))))
  | AMeasure _ _ _ q M => CL.measurement_branches q M m
  | _ => sunit_vdistr tt (\:1 : 'QO(Hq))
  end.

Fixpoint local_maps s m : {vdistr local_index s -> 'SO(Hq)} :=
  match s as s' return {vdistr local_index s' -> 'SO(Hq)} with
  | Atomic a => atom_maps a m
  | Sequence s _ => local_maps s m
  | _ => sunit_vdistr tt (\:1 : 'QO(Hq))
  end.

Lemma atom_mapsE a m i : @atom_maps a m i = @atom_map a m i.
Proof.
case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i //=;
  by case: i; rewrite /sunit_def /=.
Qed.

Lemma local_mapsE s m i : @local_maps s m i = @local_map s m i.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i //=; try exact: atom_mapsE;
  by case: i; rewrite /sunit_def /=.
Qed.

Definition future_pre (Q : assertion) (c : statement * option cmem) : 'FO(Hq) :=
  if c.2 is Some m then wp (CL.denote (translate_statement c.1)) Q m else 0%:VF.

Definition step_pre s m Q :=
  wp (SemType (fun _ : unit => local_maps s m))
    (fun i => future_pre Q (@local_control s m i)) tt.

Lemma step_preE s m Q : (step_pre s m Q : 'End(Hq)) =
  sum (fun i => (@local_map s m i)^*o (future_pre Q (@local_control s m i))).
Proof. rewrite /step_pre wpE; by apply: eq_sum=>i; rewrite local_mapsE. Qed.

Lemma translate_append s t : CL.denote (translate_statement (append s t)) =
  slet (CL.denote (translate_statement s)) (CL.denote (translate_statement t)).
Proof. by case: s=>//=; rewrite slet1l. Qed.

Lemma future_pre_append s t st Q :
  future_pre Q (append s t, st) =
  future_pre (wp (CL.denote (translate_statement t)) Q) (s,st).
Proof.
case: st=>[m|] //=; change (wp (CL.denote (translate_statement (append s t))) Q m =
  wp (CL.denote (translate_statement s)) (wp (CL.denote (translate_statement t)) Q) m).
by rewrite translate_append wp_sequence.
Qed.

Lemma sum_unit (V : normedModType C) (f : unit -> V) : sum f = f tt.
Proof.
rewrite fin_dom_sum (bigD1 tt) //=.
by rewrite big1 ?addr0 // => [[]].
Qed.

Lemma raw_skip Q m : wp_raw (@skip_sem cmem Hq) Q m = (Q m : 'End(Hq)).
Proof. change ((wp skip_sem Q m : 'End(Hq)) = (Q m : 'End(Hq))); by rewrite wp_skip. Qed.
Lemma raw_abort Q m : wp_raw (@abort_sem cmem Hq) Q m = 0.
Proof. change ((wp abort_sem Q m : 'End(Hq)) = 0); by rewrite wp_abort. Qed.
Lemma raw_sunit (F : cmem -> 'QO(Hq)) (u : cmem -> cmem) Q m :
  wp_raw (sunit F u) Q m = (F m)^*o (Q (u m)).
Proof. exact: wp_sunit. Qed.
Lemma raw_sdlet (T : choiceType) (f : cmem -> T -> cmem)
  (g : cmem -> {vdistr T -> 'SO(Hq)}) Q m :
  wp_raw (sdlet f g) Q m = sum (fun i => (g m i)^*o (Q (f m i))).
Proof. exact: wp_sdlet. Qed.
Lemma raw_sequence (K L : CL.kernel) Q m :
  wp_raw (slet K L) Q m = wp_raw K (wp L Q) m.
Proof.
change ((wp (slet K L) Q m : 'End(Hq)) = (wp K (wp L Q) m : 'End(Hq))).
by rewrite wp_sequence.
Qed.

Lemma atom_pre a m Q :
  wp (CL.denote (translate_atom a)) Q m = step_pre (Atomic a) m Q.
Proof.
apply/val_inj; change ((wp (CL.denote (translate_atom a)) Q m : 'End(Hq)) =
  (step_pre (Atomic a) m Q : 'End(Hq))).
rewrite step_preE.
case: a=>[| |t x e|t x p|t q phi|t q U|t u x q M];
  rewrite /= /future_pre /= ?raw_skip ?raw_abort ?raw_sunit ?raw_sdlet.
- by rewrite sum_unit dualso1 soE.
- by rewrite sum_unit dualso1 soE.
- by rewrite sum_unit dualso1 soE.
- by apply: eq_sum=>i; rewrite /sdistr /sdistr_def raw_skip.
- by rewrite sum_unit.
- by rewrite sum_unit.
- by apply: eq_sum=>i; rewrite raw_skip.
Qed.

Lemma wp_row (K L : CL.kernel) Q m : K m = L m -> wp K Q m = wp L Q m.
Proof.
move=>E; apply/val_inj; change ((wp K Q m : 'End(Hq)) = (wp L Q m : 'End(Hq))).
rewrite !wpE; by apply: eq_sum=>j; rewrite E.
Qed.

Lemma raw_row (K L : CL.kernel) Q m : K m = L m -> wp_raw K Q m = wp_raw L Q m.
Proof. move=>E; exact: (congr1 (fun A : 'FO(Hq) => (A : 'End(Hq))) (@wp_row K L Q m E)). Qed.

Lemma finished_pre m Q : wp (CL.denote (translate_statement Finished)) Q m = step_pre Finished m Q.
Proof.
apply/val_inj; change ((wp (CL.denote (translate_statement Finished)) Q m : 'End(Hq)) =
  (step_pre Finished m Q : 'End(Hq))).
rewrite step_preE /= /future_pre /= !raw_skip.
by rewrite sum_unit dualso1 soE.
Qed.

Lemma local_pre s : statement_wf s -> forall m Q,
  wp (CL.denote (translate_statement s)) Q m = step_pre s m Q.
Proof.
elim: s=>[|a|s IHs t IHt|n g b IH|n g b IH] /=.
- by move=>_ m Q; apply: finished_pre.
- by move=>_ m Q; apply: atom_pre.
- move=>[Hs Ht] m Q; rewrite wp_sequence (IHs Hs).
  apply/val_inj; change ((step_pre s m (wp (CL.denote (translate_statement t)) Q) : 'End(Hq)) =
    (step_pre (Sequence s t) m Q : 'End(Hq))).
  rewrite !step_preE /=.
  apply: eq_sum=>i; by rewrite future_pre_append.
- move=>[Hex Hwf] m Q; apply/val_inj.
  change ((wp (CL.denote (translate_statement (Alternative g b))) Q m : 'End(Hq)) =
    (step_pre (Alternative g b) m Q : 'End(Hq))).
  rewrite step_preE /=.
  case: pickP=>[i Hi|Hnone].
  + have Hi' : i \in enum 'I_n by rewrite mem_enum.
    have Hrow := @conditional_chain_selected n g
      (fun i => translate_statement (b i)) (enum 'I_n) m i Hex Hi' Hi.
    rewrite (@raw_row _ _ Q m Hrow) sum_unit /future_pre /= dualso1 soE.
    by [].
  + have Hdisabled : all (fun bc : expression bool * CL.command => ~~ eval bc.1 m)
      [seq (g i,translate_statement (b i)) | i <- enum 'I_n].
      rewrite all_map; apply/allP=>i _ /=; by rewrite (Hnone i).
    have Hrow := conditional_chain_none Hdisabled.
    by rewrite (@raw_row _ _ Q m Hrow) raw_abort sum_unit /future_pre /= dualso1 soE.
- move=>[Hex Hwf] m Q; apply/val_inj.
  change ((wp (CL.denote (translate_statement (Repetition g b))) Q m : 'End(Hq)) =
    (step_pre (Repetition g b) m Q : 'End(Hq))).
  rewrite step_preE /=.
  have W := congr1 (fun A : assertion => (A m : 'End(Hq)))
    (CQRules.pre_while_unfold true (loop_guard g)
      (conditional_chain [seq (g i,translate_statement (b i)) | i <- enum 'I_n]) Q).
  case: pickP=>[i Hi|Hnone].
  + have Hany : enabled g m by apply/enabledP; exists i.
    rewrite /conditional -/(eval (loop_guard g) m) eval_loop_guard Hany in W.
    rewrite /CQRules.pre /CQRules.wp_command /= in W.
    rewrite W.
    have Hi' : i \in enum 'I_n by rewrite mem_enum.
    have Hrow := @conditional_chain_selected n g
      (fun j => translate_statement (b j)) (enum 'I_n) m i Hex Hi' Hi.
    rewrite (@raw_row _ _ _ m Hrow).
    by rewrite sum_unit /future_pre /= dualso1 soE raw_sequence.
  + have Hany : enabled g m = false.
      apply/negP=>/enabledP[i Hi]; by move: (Hnone i); rewrite Hi.
    rewrite /conditional -/(eval (loop_guard g) m) eval_loop_guard Hany in W.
    rewrite /CQRules.pre /CQRules.wp_command /= in W.
    by rewrite W sum_unit /future_pre /= dualso1 soE raw_skip.
Qed.

Definition pre_observe (Q : assertion) (c : local_configuration) : C :=
  if c.1.2 is Some m then
    \Tr (wp (CL.denote (translate_statement c.1.1)) Q m \o c.2)
  else 0.

Lemma local_pre_observe s m rho Q : statement_wf s -> rho \is den1lf ->
  pre_observe Q (local_config s (Some m) rho) =
  family_observe (local_successor s m rho) (pre_observe Q).
Proof.
move=>Hwf Hr; change (\Tr (wp (CL.denote (translate_statement s)) Q m \o rho) =
  family_observe (local_successor s m rho) (pre_observe Q)).
rewrite (local_pre Hwf).
rewrite /step_pre wp_pairing (@local_realization s m rho Hr) /family_observe /local_family /=.
apply: eq_sum=>i; rewrite local_mapsE /future_pre.
case E: (@local_control s m i)=>[r [u|]]; rewrite /pre_observe /local_config /=;
  last by rewrite linear0l linear0 mulr0.
have W := congr1 (fun A : 'End(Hq) =>
  \Tr (wp (CL.denote (translate_statement r)) Q u \o A))
  (weighted_normalized_output (@local_cp s m i) Hr).
by rewrite linearZr /= linearZ /= in W; symmetry.
Qed.

Definition at_store out (A : 'FO(Hq)) : assertion :=
  fun m => if m == out then A else 0%:VF.

Lemma pairing_at_store (K : CL.kernel) m out (A : 'FO(Hq)) rho :
  \Tr (wp K (at_store out A) m \o rho) = \Tr (A \o K m out rho).
Proof.
rewrite wp_pairing (fin_supp_sum (S := [fset out]%fset)).
- move=>j; rewrite inE=>/negPf E; by rewrite /at_store E linear0l linear0.
- by rewrite psum1 /at_store eqxx.
Qed.

Definition future (K : CL.kernel) (c : local_configuration) out : 'End(Hq) :=
  if c.1.2 is Some m then
    slet (CL.denote (translate_statement c.1.1)) K m out c.2
  else 0.

Lemma future_pairing K c out A :
  pre_observe (wp K (at_store out A)) c = \Tr (A \o future K c out).
Proof.
case: c=>[[s [m|]] rho].
- change (\Tr (wp (CL.denote (translate_statement s)) (wp K (at_store out A)) m \o rho) =
    \Tr (A \o slet (CL.denote (translate_statement s)) K m out rho)).
  by rewrite -wp_sequence pairing_at_store.
- by rewrite /pre_observe /future /= linear0r linear0.
Qed.

Lemma future_bound K c out : c.2 \is denlf -> `|future K c out| <= 1.
Proof.
case: c=>[[s [m|]] rho] Hr; rewrite /future /=; last by rewrite normr0.
have Hd : slet (CL.denote (translate_statement s)) K m out rho \is denlf.
  exact: (qo_denlf _ (DenLf_Build Hr)).
by rewrite psd_trfnorm ?denlf_psd //; exact: denlf_trlf Hd.
Qed.

Lemma local_future_summable s m rho K out : statement_wf s -> rho \is den1lf ->
  summable (fun i => branch_weight (local_successor s m rho) i *:
    future K (branch_value (local_successor s m rho) i) out).
Proof.
move=>Hwf Hr; rewrite (@local_realization s m rho Hr).
apply: (@weighted_summable (local_index s) Hq
  (@Family _ (local_index s) (branch_weight (local_family s m rho)) id)
  (fun i => future K (branch_value (local_family s m rho) i) out)).
- exact: (@DistributedLocalDiamond.local_family_probability s m rho Hwf Hr).
- move=>i; apply: future_bound; apply: den1lf_den.
  exact: (normalized_output_den1 (@local_cp s m i) Hr).
Qed.

Theorem local_future_harmonic s m rho K out : statement_wf s -> rho \is den1lf ->
  future K (local_config s (Some m) rho) out =
  weighted_sum (local_successor s m rho) (fun c => future K c out).
Proof.
move=>Hwf Hr.
have E (A : 'FO(Hq)) :
  \Tr (A \o future K (local_config s (Some m) rho) out) =
  \Tr (A \o weighted_sum (local_successor s m rho) (fun c => future K c out)).
  rewrite -future_pairing (@local_pre_observe s m rho _ Hwf Hr) /weighted_sum.
  rewrite (cvg_linearP_sum (f := fun X : 'End(Hq) => \Tr (A \o X))).
  - by move=>a X Y; rewrite linearPr /= linearP.
  - apply: norm_bounded_cvg; exact: local_future_summable.
  - apply: eq_sum=>i; rewrite future_pairing /= linearZr /= linearZ /=; by [].
apply/eqP; rewrite eq_le; apply/andP; split; apply/lef_trobs=>A.
- by rewrite lftraceC E lftraceC.
- by rewrite lftraceC -E lftraceC.
Qed.

Lemma local_future_residual s m rho K out : residual_wf s -> rho \is den1lf ->
  future K (local_config s (Some m) rho) out =
  weighted_sum (local_successor s m rho) (fun c => future K c out).
Proof.
move=>[->|Hs] Hr; first by rewrite /= weighted_certain.
exact: local_future_harmonic Hs Hr.
Qed.

Lemma future_finished K m rho out :
  future K (local_config Finished (Some m) rho) out = K m out rho.
Proof. change (slet skip_sem K m out rho = K m out rho); by rewrite slet1l. Qed.

Lemma future_failed K s rho out : future K (local_config s None rho) out = 0.
Proof. by []. Qed.

End DistributedLocalCorrespondence.
