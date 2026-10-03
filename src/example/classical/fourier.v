(* Quantum Fourier circuit, classical.pdf Section 7.2.
   See FOURIER-NOTES.md; reference proof patterns are MIT-licensed. *)
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
From quantum.example.classical Require Import language.

Module ClassicalFourier.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition tuple_fourier n : 'FU('Hs (n.-tuple bool)) :=
  PUnitary t2tv (@QFTbv n).

Definition single_hadamard n (k : 'I_n) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of tentf_tuple (fun i : 'I_n =>
    if i == k then (Hadamard : 'FU('Hs bool)) else (\1 : 'FU('Hs bool)))].

Definition controlled_phase n (k j : 'I_n) (theta : R) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of expmxip t2tv
    (fun z : n.-tuple bool => ((z~_k) && (z~_j))%:R) (2 * theta)].

Definition reversal n : 'FU('Hs (n.-tuple bool)) :=
  [unitary of permtf bool (perm (@rev_ord_inj n))].

Lemma single_hadamard_product n (k : 'I_n) (v : 'I_n -> 'Hs bool) :
  single_hadamard k (tentv_tuple v) =
  tentv_tuple (fun i => if i == k then Hadamard (v i) else v i).
Proof.
rewrite /single_hadamard tentf_tuple_apply; apply: eq_tentv_tuple=>i.
by case: (i == k); rewrite /= ?lfunE.
Qed.

Lemma diagonal_amplitude n (d : n.-tuple bool -> R) theta
    (v : 'Hs (n.-tuple bool)) z :
  [< ''z; expmxip t2tv d theta v >] = expip (d z * theta) * [< ''z; v >].
Proof.
by rewrite -adj_dotEl expmxip_adj expmxipEt dotpZl -expipNC mulrN opprK.
Qed.

Lemma controlled_phase_amplitude n (k j : 'I_n) theta (v : 'Hs (n.-tuple bool)) z :
  [< ''z; controlled_phase k j theta v >] =
  expip (((z~_k) && (z~_j))%:R * (2 * theta)) * [< ''z; v >].
Proof. exact: diagonal_amplitude. Qed.

Lemma reversal_product n (v : 'I_n -> 'Hs bool) :
  reversal n (tentv_tuple v) = tentv_tuple (fun i => v (rev_ord i)).
Proof. by rewrite /reversal permtfEtv; apply: eq_tentv_tuple=>i; rewrite permE. Qed.

Lemma hadamard_phase b : Hadamard ''b = phstate (b%:R / 2).
Proof.
rewrite Hadamard_cb; rude_bmx; case: b=>/=;
by rewrite ?mul0r ?mulr0 ?expip0 ?mul1r ?mulfV // ?mulr1 ?expip1.
Qed.

Lemma phase_shift_amplitude b r theta :
  [< ''b; phstate (r + theta) >] =
    expip (2 * b%:R * theta) * [< ''b; phstate r >].
Proof. by rewrite !dotp_cbph mulrDr expipD mulrA [RHS]mulrC. Qed.

Definition tensor_replace n (k : 'I_n) (v : 'I_n -> 'Hs bool) u :=
  tentv_tuple (fun i => if i == k then u else v i).

Lemma tensor_replace_amplitude n (k : 'I_n) (v : 'I_n -> 'Hs bool) u z :
  [< ''z; tensor_replace k v u >] =
  [< ''(z~_k); u >] * \prod_(i | i != k) [< ''(z~_i); v i >].
Proof.
rewrite /tensor_replace t2tv_tuple tentv_tuple_dot (bigD1 k) //= eqxx.
f_equal; apply: eq_bigr=>i /negPf ik; by rewrite ik.
Qed.

Lemma tensor_phase_shift n (k : 'I_n) (v : 'I_n -> 'Hs bool) r theta z :
  [< ''z; tensor_replace k v (phstate (r + theta)) >] =
  expip (2 * (z~_k)%:R * theta) * [< ''z; tensor_replace k v (phstate r) >].
Proof. by rewrite !tensor_replace_amplitude phase_shift_amplitude mulrA. Qed.

Lemma tensor_basis_zero n (j : 'I_n) (v : 'I_n -> 'Hs bool) (d : bool) z :
  v j = ''d -> z~_j != d -> [< ''z; tentv_tuple v >] = 0.
Proof.
move=>vj /negPf zd; rewrite t2tv_tuple tentv_tuple_dot (bigD1 j) //= vj.
by rewrite onb_dot zd mul0r.
Qed.

Lemma controlled_phase_product n (k j : 'I_n) theta r d (v : 'I_n -> 'Hs bool) :
  k != j -> v k = phstate r -> v j = ''d ->
  controlled_phase k j theta (tentv_tuple v) =
    tensor_replace k v (phstate (r + d%:R * theta)).
Proof.
move=>kj vk vj; apply/(intro_onbl t2tv)=>z.
rewrite controlled_phase_amplitude.
have Ev : tensor_replace k v (phstate r) = tentv_tuple v.
  apply: eq_tentv_tuple=>i; case: eqP=>[->|] //; exact: esym vk.
case: (boolP (z~_j == d))=>[/eqP zd|zd].
- rewrite tensor_phase_shift Ev zd.
  congr (expip _ * _); clear vj zd.
  by case: (z~_k); case: d; rewrite /= ?mul0r ?mulr0 ?mul1r ?mulr1 ?mul0r.
- rewrite (tensor_basis_zero vj zd) mulr0; symmetry.
  apply: (@tensor_basis_zero n j _ d z) zd.
  by rewrite eq_sym (negPf kj).
Qed.

Lemma tensor_replace_id n (k : 'I_n) (v : 'I_n -> 'Hs bool) :
  tensor_replace k v (v k) = tentv_tuple v.
Proof. apply: eq_tentv_tuple=>i; by case: eqP=>[->|]. Qed.

Lemma tensor_replace_twice n (k : 'I_n) (v : 'I_n -> 'Hs bool) u w :
  tensor_replace k (fun i => if i == k then u else v i) w =
  tensor_replace k v w.
Proof. apply: eq_tentv_tuple=>i; by case: (i == k). Qed.

Definition phase_chain n (k : 'I_n) (theta : 'I_n -> R)
    (js : seq 'I_n) (v : 'Hs (n.-tuple bool)) :=
  foldl (fun w j => controlled_phase k j (theta j) w) v js.

Lemma phase_chain_product n (k : 'I_n) (theta : 'I_n -> R)
    (js : seq 'I_n) (v : 'I_n -> 'Hs bool) (d : 'I_n -> bool) r :
  (forall j, j \in js -> k != j /\ v j = ''(d j)) ->
  phase_chain k theta js (tensor_replace k v (phstate r)) =
  tensor_replace k v (phstate (r + \sum_(j <- js) (d j)%:R * theta j)).
Proof.
elim: js v r=>[v r H|j js IH v r H].
  by rewrite /phase_chain /= big_nil addr0.
have [kj vj] := H j (mem_head j js).
have Hj : (fun i => if i == k then phstate r else v i) j = ''(d j).
  by rewrite eq_sym (negPf kj).
have Hk : (fun i => if i == k then phstate r else v i) k = phstate r.
  by rewrite eqxx.
rewrite /phase_chain /= -/(phase_chain _ _ _ _).
rewrite (@controlled_phase_product n k j (theta j) r (d j) _ kj Hk Hj)
  tensor_replace_twice.
have Htail : forall i, i \in js -> k != i /\ v i = ''(d i).
  by move=>i Hi; apply: H; rewrite in_cons Hi orbT.
by rewrite (IH _ _ Htail) big_cons addrA.
Qed.

Lemma bitstr2rat_sum (bs : seq bool) :
  bitstr2rat bs =
    \sum_(0 <= j < size bs) (nth false bs j)%:R / 2 ^+ j.+1.
Proof.
elim: bs=>[|b bs IH].
  by rewrite [bitstr2rat]unlock big_geq.
rewrite bitstr_cons IH /= big_nat_recl //= expr1; congr (_ + _).
rewrite big_distrl /=; apply: eq_bigr=>j _.
by rewrite [2 ^+ j.+2]exprSr invfM mulrA.
Qed.

Lemma bitstr2rat_drop_sum n (bs : n.-tuple bool) k :
  bitstr2rat (drop k bs) =
    \sum_(j < n | (k <= j)%N) (bs~_j)%:R / 2 ^+ (j - k).+1.
Proof.
rewrite bitstr2rat_sum size_drop size_tuple.
transitivity (\sum_(k <= j < n) (nth false bs j)%:R / 2 ^+ (j - k).+1 : R).
- rewrite -[in RHS](add0n k) big_addn; apply: eq_bigr=>j _.
  by rewrite nth_drop addnK addnC.
- rewrite (big_nat_widenl k 0) // big_mkord.
  apply: eq_big=>j; first by rewrite andTb.
  by move=>_; rewrite (tnth_nth false).
Qed.

Definition control_indices n (k : 'I_n) :=
  seq.filter (fun j : 'I_n => (k < j)%N) (enum 'I_n).
Definition phase_angle n (k j : 'I_n) : R := (2 ^+ (j - k).+1)^-1.
Definition stage_factors n (bs : n.-tuple bool) k (i : 'I_n) : 'Hs bool :=
  if (i < k)%N then phstate (bitstr2rat (drop i bs)) else ''(bs~_i).
Definition stage n (bs : n.-tuple bool) k := tentv_tuple (stage_factors bs k).

Lemma suffix_angle n (bs : n.-tuple bool) (k : 'I_n) :
  (bs~_k)%:R / 2 +
    \sum_(j <- control_indices k) (bs~_j)%:R * phase_angle k j =
  bitstr2rat (drop k bs).
Proof.
rewrite bitstr2rat_drop_sum (bigD1 k) //= subnn expr1.
congr (_ + _); rewrite /control_indices big_filter /phase_angle.
rewrite enumT [index_enum _]unlock.
apply: eq_bigl=>j; case: (eqVneq j k)=>[->|jk].
  by rewrite ltnn ?eqxx ?andbF.
by rewrite [(k <= j)%N]leq_eqVlt (val_eqE k j) eq_sym (negPf jk) /= ?andbT.
Qed.

Lemma stage_hadamard n (bs : n.-tuple bool) (k : 'I_n) :
  single_hadamard k (stage bs k) =
  tensor_replace k (stage_factors bs k) (phstate ((bs~_k)%:R / 2)).
Proof.
rewrite single_hadamard_product; apply: eq_tentv_tuple=>i.
case: eqP=>[->|] //; by rewrite /stage_factors ltnn hadamard_phase.
Qed.

Lemma stage_phase_layer n (bs : n.-tuple bool) (k : 'I_n) :
  phase_chain k (phase_angle k) (control_indices k)
    (single_hadamard k (stage bs k)) = stage bs k.+1.
Proof.
rewrite stage_hadamard.
have Hcontrol j : j \in control_indices k ->
    k != j /\ stage_factors bs k j = ''(bs~_j).
  rewrite /control_indices mem_filter=>/andP[kj _]; split.
    by apply/eqP=>E; move: kj; rewrite E ltnn.
  by rewrite /stage_factors ltnNge (ltnW kj).
rewrite (phase_chain_product _ _ Hcontrol) suffix_angle.
apply: eq_tentv_tuple=>i; rewrite /stage_factors.
case: eqP=>[->|/eqP ik].
  by rewrite ltnSn.
by rewrite ltnS [(i <= k)%N]leq_eqVlt (val_eqE i k) (negPf ik).
Qed.

Fixpoint unitary_list (H : chsType) (us : seq 'FU(H)) : 'FU(H) :=
  if us is u :: us' then [unitary of (unitary_list us') \o u]
  else (\1 : 'FU(H)).

Lemma unitary_listE (H : chsType) (I : Type) (us : I -> 'FU(H)) js v :
  unitary_list [seq us j | j <- js] v = foldl (fun w j => us j w) v js.
Proof.
elim: js v=>[|j js IH] v; first by rewrite /= lfunE.
rewrite /= lfunE /=; exact: IH.
Qed.

Lemma unitary_list_rcons (H : chsType) (us : seq 'FU(H)) u v :
  unitary_list (rcons us u) v = u (unitary_list us v).
Proof.
elim: us v=>[|u0 us IH] v; first by rewrite /= !lfunE /= id_lfunE.
rewrite /= !lfunE /=; exact: IH.
Qed.

Definition phase_layer n (k : 'I_n) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of (unitary_list [seq controlled_phase k j (phase_angle k j) |
    j <- control_indices k]) \o single_hadamard k].

Lemma phase_layerE n (k : 'I_n) v :
  phase_layer k v = phase_chain k (phase_angle k) (control_indices k)
    (single_hadamard k v).
Proof. by rewrite /phase_layer lfunE /= unitary_listE. Qed.

Definition circuit_prefix n k : 'FU('Hs (n.-tuple bool)) :=
  unitary_list [seq phase_layer i | i <- take k (enum 'I_n)].
Definition fourier_circuit n : 'FU('Hs (n.-tuple bool)) :=
  [unitary of reversal n \o circuit_prefix n n].

Lemma stage_initial n (bs : n.-tuple bool) : stage bs 0 = ''bs.
Proof.
rewrite /stage t2tv_tuple; apply: eq_tentv_tuple=>i.
by rewrite /stage_factors ltn0.
Qed.

Lemma stage_final n (bs : n.-tuple bool) : reversal n (stage bs n) = QFTbv bs.
Proof.
rewrite /stage reversal_product QFTbvTE; apply: eq_tentv_tuple=>i.
by rewrite /stage_factors ltn_ord /= subnS predn_sub.
Qed.

Lemma circuit_prefix_basis n (bs : n.-tuple bool) k :
  (k <= n)%N -> circuit_prefix n k ''bs = stage bs k.
Proof.
elim: k=>[|k IH] Hkn.
- by rewrite /circuit_prefix take0 /= lfunE stage_initial.
- have Hk : (k < n)%N := Hkn.
  pose i : 'I_n := Ordinal Hk.
  rewrite /circuit_prefix (take_nth i) ?size_enum_ord //.
  rewrite (nth_ord_enum i i) map_rcons unitary_list_rcons
    -/(circuit_prefix n k) (IH (ltnW Hk)) phase_layerE.
  exact: stage_phase_layer.
Qed.

Theorem fourier_circuit_basis n (bs : n.-tuple bool) :
  fourier_circuit n ''bs = QFTbv bs.
Proof.
by rewrite /fourier_circuit lfunE /= circuit_prefix_basis // stage_final.
Qed.

Theorem fourier_circuit_correct n :
  (fourier_circuit n : 'End('Hs (n.-tuple bool))) = tuple_fourier n.
Proof.
apply/(intro_onb t2tv)=>bs.
by rewrite fourier_circuit_basis /tuple_fourier PUnitaryE.
Qed.

End ClassicalFourier.
