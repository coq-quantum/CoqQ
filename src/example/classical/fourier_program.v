(* The nested-While Fourier program of classical.pdf Section 7.2.
   See FOURIER-NOTES.md for the invariant and exact circuit argument. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap perm.
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
From quantum.example.classical Require Import language deterministic algorithm_loops indexed_loops algorithm_semantics fourier predicate rules.

Module ClassicalFourierProgram.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops
  ClassicalIndexedLoops ClassicalAlgorithmSemantics ClassicalFourier.
Local Notation Hq := 'H[msys]_finset.setT.

Definition phase_indices_valid n (a b : int) : bool :=
  if one_based_index n a is Some i then
    if one_based_index n b is Some j then i != j else false
  else false.
Definition selected_phase n (a b : int) : 'FU('Hs (n.-tuple bool)) :=
  if one_based_index n a is Some i then
    if one_based_index n b is Some j then controlled_phase i j (phase_angle i j)
    else (\1 : 'FU('Hs (n.-tuple bool)))
  else (\1 : 'FU('Hs (n.-tuple bool))).

Definition phase_gate n (q : wf_qreg (QArray n QBool))
    (x y : variable Integer) : command :=
  Conditional
    (EApp (EApp (EConst (@phase_indices_valid n)) (EVar x)) (EVar y))
    (Unitary q (EApp (EApp (EConst (@selected_phase n)) (EVar x)) (EVar y)))
    Abort.

Lemma phase_gate_execution n (q : wf_qreg (QArray n QBool)) (x y : variable Integer)
    (i j : 'I_n) s :
  i != j -> (s.[x])%M = Posz i.+1 -> (s.[y])%M = Posz j.+1 ->
  execution (phase_gate q x y) s s
    (liftfso (formso (tf2f q q (controlled_phase i j (phase_angle i j))))).
Proof.
move=>Hij Hx Hy; apply: RunIfTrue.
- by rewrite /eval /= Hx Hy /phase_indices_valid !one_based_indexE Hij.
- have D := RunUnitary q
    (EApp (EApp (EConst (@selected_phase n)) (EVar x)) (EVar y)) s.
  by rewrite /eval /= Hx Hy /selected_phase !one_based_indexE in D.
Qed.

Section Program.
Variable (n : nat) (q : wf_qreg (QArray n QBool)).
Variable (x y : variable Integer).

Definition fourier_inner := While (below y n.+1)
  (Sequence (phase_gate q x y) (Assign y (increment y))).
Definition fourier_body :=
  Sequence (indexed_gate q x (@single_hadamard n))
  (Sequence (Assign y (increment x))
  (Sequence fourier_inner (Assign x (increment x)))).
Definition fourier_outer := While (below x n.+1) fourier_body.
Definition fourier_program := Sequence (Assign x (EConst (1 : int)))
  (Sequence fourier_outer (Unitary q (EConst (reversal n)))).

Definition inner_circuit (k : 'I_n) start : 'FU('Hs (n.-tuple bool)) :=
  unitary_list [seq controlled_phase k j (phase_angle k j) |
    j <- drop start (enum 'I_n)].

Lemma control_indices_drop (k : 'I_n) :
  control_indices k = drop k.+1 (enum 'I_n).
Proof.
apply: (inj_map (@ord_inj n)).
rewrite map_drop val_enum_ord drop_iota add0n /control_indices.
rewrite -filter_map val_enum_ord.
have Hsmall : seq.filter (fun j : nat => (k < j)%N) (iota 0 k.+1) = [::].
  rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 // =>j.
  rewrite mem_iota add0n leq0n /= ltnS =>Hj.
  by rewrite ltnNge Hj.
have Hlarge : seq.filter (fun j : nat => (k < j)%N)
    (iota k.+1 (n - k.+1)) = iota k.+1 (n - k.+1).
  apply/all_filterP/allP=>j; rewrite mem_iota=>/andP[Hj _]; exact: Hj.
have Eseq := iotaD 0 k.+1 (n - k.+1).
rewrite add0n (subnKC (ltn_ord k)) in Eseq.
by rewrite Eseq filter_cat Hsmall Hlarge.
Qed.

Lemma inner_circuit_layer (k : 'I_n) :
  inner_circuit k k.+1 \o single_hadamard k = phase_layer k.
Proof. by rewrite /phase_layer /inner_circuit control_indices_drop. Qed.

Lemma inner_circuit_end (k : 'I_n) :
  (inner_circuit k n : 'End('Hs (n.-tuple bool))) = \1.
Proof. by rewrite /inner_circuit drop_oversize ?size_enum_ord. Qed.

Lemma inner_circuit_step (k j : 'I_n) :
  (inner_circuit k j : 'End('Hs (n.-tuple bool))) =
    inner_circuit k j.+1 \o controlled_phase k j (phase_angle k j).
Proof.
by rewrite /inner_circuit (drop_nth j) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.

Lemma increment_preserves_other s count : cvname y != cvname x ->
  ((iter count (next_store y) s).[x])%M = (s.[x])%M.
Proof.
move=>Hxy; elim: count s=>[|count IH] s; first by [].
by rewrite iterSr IH /next_store get_set_nex.
Qed.

Lemma fourier_inner_execution (k : 'I_n) count start s :
  cvname y != cvname x -> (k < start)%N -> (start + count = n)%N ->
  (s.[x])%M = Posz k.+1 -> (s.[y])%M = Posz start.+1 ->
  execution fourier_inner s (iter count (next_store y) s)
    (liftfso (formso (tf2f q q (inner_circuit k start)))).
Proof.
elim: count start s=>[|count IH] start s Hxy Hks Hn Hx Hy.
- rewrite addn0 in Hn; subst start.
  rewrite inner_circuit_end tf2f1 formso1 liftfso1 /=.
  apply: RunWhileFalse; by rewrite /below /eval /= Hy ltxx.
- have Hstart : (start < n)%N.
    by rewrite -Hn addnS ltnS leq_addr.
  pose j : 'I_n := Ordinal Hstart.
  have Hkj : k != j.
    apply/eqP=>E; move: Hks; by rewrite E ltnn.
  have Hguard : eval (below y n.+1) s = true.
    by rewrite /below /eval /= Hy ltz_nat ltnS Hstart.
  have Hnx : ((next_store y s).[x])%M = Posz k.+1.
    by rewrite /next_store get_set_nex.
  have Hny : ((next_store y s).[y])%M = Posz start.+2.
    exact: next_store_value Hy.
  have Hnt : (start.+1 + count = n)%N by rewrite addSn -addnS.
  have Hkt : (k < start.+1)%N := ltn_trans Hks (ltnSn start).
  have Dt := IH start.+1 (next_store y s) Hxy Hkt Hnt Hnx Hny.
  have Dgate := @phase_gate_execution n q x y k j s Hkj Hx Hy.
  have Db := RunSequence Dgate (RunAssign y (increment y) s).
  rewrite comp_so1l in Db.
  have D := RunWhileTrue Hguard Db Dt.
  rewrite register_unitary_comp in D.
  rewrite iterSr (@inner_circuit_step k j).
  exact: D.
Qed.

Definition fourier_next j s :=
  next_store x (iter (n - j) (next_store y) (s.[y <- eval (increment x) s])%M).
Definition fourier_action j (_ : store) : 'SO(Hq) :=
  if one_based_index n (Posz j) is Some i then
    liftfso (formso (tf2f q q (phase_layer i))) else \:1.

Lemma fourier_next_counter j s : cvname y != cvname x ->
  (s.[x])%M = Posz j -> ((fourier_next j s).[x])%M = Posz j.+1.
Proof.
move=>Hxy Hx; apply: next_store_value.
by rewrite increment_preserves_other // get_set_nex.
Qed.

Lemma fourier_body_execution (i : 'I_n) s :
  cvname y != cvname x -> (s.[x])%M = Posz i.+1 ->
  execution fourier_body s (fourier_next i.+1 s) (fourier_action i.+1 s).
Proof.
move=>Hxy Hx.
have Hx0 : ((s.[y <- eval (increment x) s]).[x])%M = Posz i.+1.
  by rewrite get_set_nex.
have Hy0 : ((s.[y <- eval (increment x) s]).[y])%M = Posz i.+2.
  by rewrite get_set_eq /increment /eval /= Hx -PoszD addn1.
have Dloop := @fourier_inner_execution i (n - i.+1) i.+1
  (s.[y <- eval (increment x) s])%M Hxy (ltnSn i)
  (subnKC (ltn_ord i)) Hx0 Hy0.
have Dhad := @indexed_gate_execution _ n q x (@single_hadamard n) i s Hx.
have D := RunSequence Dhad
  (RunSequence (RunAssign y (increment x) s)
    (RunSequence Dloop (RunAssign x (increment x) _))).
rewrite comp_so1l comp_so1r register_unitary_comp inner_circuit_layer in D.
rewrite /fourier_action one_based_indexE.
exact: D.
Qed.

Lemma fourier_outer_execution s :
  cvname y != cvname x -> (s.[x])%M = Posz 1 ->
  execution fourier_outer s (final_store fourier_next 1 n s)
    (accumulated_action fourier_next fourier_action 1 n s).
Proof.
move=>Hxy Hx; rewrite /fourier_outer -[n.+1]add1n.
apply: indexed_loop_execution Hx _ _.
- move=>[|j] t /andP[Hlow Hhigh] Ht; first by rewrite leqn0 in Hlow.
  have Hj : (j < n)%N by move: Hhigh; rewrite add1n ltnS.
  exact: (@fourier_body_execution (Ordinal Hj) t Hxy Ht).
- move=>j t _ Ht; exact: fourier_next_counter Hxy Ht.
Qed.

Definition outer_circuit start : 'FU('Hs (n.-tuple bool)) :=
  unitary_list [seq phase_layer j | j <- drop start (enum 'I_n)].

Lemma outer_circuit_end : (outer_circuit n : 'End('Hs (n.-tuple bool))) = \1.
Proof. by rewrite /outer_circuit drop_oversize ?size_enum_ord. Qed.

Lemma outer_circuit_step (j : 'I_n) :
  (outer_circuit j : 'End('Hs (n.-tuple bool))) =
    outer_circuit j.+1 \o phase_layer j.
Proof.
by rewrite /outer_circuit (drop_nth j) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.

Lemma outer_circuit_whole :
  (outer_circuit 0 : 'End('Hs (n.-tuple bool))) = circuit_prefix n n.
Proof.
by rewrite /outer_circuit /circuit_prefix drop0 take_oversize ?size_enum_ord.
Qed.

Lemma accumulated_circuit count start s : (start + count = n)%N ->
  accumulated_action fourier_next fourier_action start.+1 count s =
    liftfso (formso (tf2f q q (outer_circuit start))).
Proof.
elim: count start s=>[|count IH] start s Hn.
- rewrite addn0 in Hn; subst start.
  by rewrite /= outer_circuit_end tf2f1 formso1 liftfso1.
- have Hstart : (start < n)%N.
    by rewrite -Hn addnS ltnS leq_addr.
  pose j : 'I_n := Ordinal Hstart.
  have Hnt : (start.+1 + count = n)%N by rewrite addSn -addnS.
  change (accumulated_action fourier_next fourier_action start.+2 count
    (fourier_next start.+1 s) :o fourier_action start.+1 s =
      liftfso (formso (tf2f q q (outer_circuit start)))).
  rewrite (IH _ _ Hnt) /fourier_action (@one_based_indexE n j)
    register_unitary_comp (outer_circuit_step j).
  by [].
Qed.

Definition fourier_final_store s :=
  final_store fourier_next 1 n (s.[x <- (1 : int)])%M.
Definition fourier_channel : 'QC(Hq) :=
  [QC of liftfso (formso (tf2f q q (tuple_fourier n)))].

Theorem fourier_execution s : cvname y != cvname x ->
  execution fourier_program s (fourier_final_store s) fourier_channel.
Proof.
move=>Hxy.
have Hx : ((s.[x <- (1 : int)]).[x])%M = Posz 1 by rewrite get_set_eq.
have Dloop := fourier_outer_execution Hxy Hx.
have D := RunSequence (RunAssign x (EConst (1 : int)) s)
  (RunSequence Dloop (RunUnitary q (EConst (reversal n)) _)).
rewrite (@accumulated_circuit n 0 (s.[x <- (1 : int)])%M (add0n n)) outer_circuit_whole
  comp_so1r register_unitary_comp -/(fourier_circuit n) fourier_circuit_correct in D.
exact: D.
Qed.

Theorem fourier_denote s : cvname y != cvname x ->
  forall m, denote fourier_program s m =
    point (fourier_final_store s) fourier_channel m.
Proof. move=>Hxy; exact: execution_denote (fourier_execution s Hxy). Qed.

Theorem fourier_pre total (Q : store -> 'FO(Hq)) s : cvname y != cvname x ->
  (CQRules.pre total fourier_program Q s : 'End(Hq)) =
    fourier_channel^*o (Q (fourier_final_store s)).
Proof.
move=>Hxy; exact: execution_pre (fourier_execution s Hxy).
Qed.

Theorem fourier_correct total (P Q : store -> 'FO(Hq)) :
  cvname y != cvname x ->
  (forall s, P s <= fourier_channel^*o (Q (fourier_final_store s))) ->
  CQRules.derives total P fourier_program Q.
Proof.
move=>Hxy Hpre; apply: CQRules.derives_complete.
apply/(proj2 (CQRules.valid_iff _ _ _ _))=>s.
by rewrite fourier_pre //; exact: Hpre.
Qed.

End Program.
End ClassicalFourierProgram.
