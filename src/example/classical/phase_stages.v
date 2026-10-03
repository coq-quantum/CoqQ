(* Gate-by-gate phase-estimation invariant; see CASE-STUDIES.md. *)
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
From quantum.example.classical Require Import fourier phase_estimation
  phase_program phase_tensor.

Module ClassicalPhaseStages.
Import ClassicalFourier ClassicalPhaseEstimation ClassicalPhaseProgram
  ClassicalPhaseTensor.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Lemma bit_diagonal_product n (i : 'I_n) (v : 'I_n -> 'Hs bool) r phi :
  v i = phstate r ->
  bit_diagonal i phi (tentv_tuple v) = tensor_replace i v (phstate (r + phi)).
Proof.
move=>Hi; apply/(intro_onbl t2tv)=>bs.
rewrite /bit_diagonal diagonal_amplitude tensor_phase_shift.
have E : tensor_replace i v (phstate r) = tentv_tuple v.
  by rewrite -Hi tensor_replace_id.
rewrite E; congr (expip _ * _).
by rewrite mulrCA mulrA.
Qed.

Definition estimation_factors n phi k (i : 'I_n) :=
  if (i < k)%N then phstate (2%:R ^+ (n - i.+1) * phi) else '0.
Definition estimation_layer n phi k := tentv_tuple (@estimation_factors n phi k).

Definition estimation_stage n T (U : 'FU('Ht T)) (i : 'I_n) :
    'FU('Ht (QPair (QArray n QBool) T)) :=
  [unitary of ((controlled_at U i)%:VF ^+ (2 ^ (n - i.+1))) \o
    (hadamard_at i ⊗f (\1 : 'FU('Ht T)))].

Lemma estimation_stageE n T (U : 'FU('Ht T)) (i : 'I_n) phi (u : 'Ht T) :
  U u = expip (2 * phi) *: u ->
  estimation_stage U i (estimation_layer n phi i ⊗t u) =
    estimation_layer n phi i.+1 ⊗t u.
Proof.
move=>Hu; rewrite /estimation_stage lfunE /= tentf_apply lfunE /=
  (@controlled_power_eigen n T U i _ _ u phi Hu).
rewrite /hadamard_at /estimation_layer single_hadamard_product.
have E : tentv_tuple (fun j : 'I_n =>
    if j == i then Hadamard (estimation_factors phi i j)
    else estimation_factors phi i j) =
  tensor_replace i (estimation_factors phi i) (phstate 0).
  apply: eq_tentv_tuple=>j; case: eqP=>[->|] //.
  by rewrite /estimation_factors ltnn hadamard_phase mul0r.
rewrite E.
have Ei : (fun j : 'I_n => if j == i then phstate 0 else
  estimation_factors phi i j) i = phstate 0 by rewrite eqxx.
rewrite (@bit_diagonal_product n i _ 0 _ Ei) tensor_replace_twice add0r natrX.
congr (_ ⊗t _); apply: eq_tentv_tuple=>j.
rewrite /estimation_factors; case Eji: (j == i)=>/=.
- by move/eqP: Eji=>->; rewrite ltnSn.
- by rewrite ltnS [(j <= i)%N]leq_eqVlt (val_eqE j i) Eji.
Qed.

Definition estimation_circuit_prefix n T (U : 'FU('Ht T)) k :=
  unitary_list [seq estimation_stage U i | i <- take k (enum 'I_n)].

Lemma estimation_layer_initial n phi :
  estimation_layer n phi 0 = ''(nseq_tuple n false).
Proof.
rewrite /estimation_layer t2tv_tuple; apply: eq_tentv_tuple=>i.
by rewrite /estimation_factors ltn0 tnth_nseq.
Qed.

Lemma estimation_layer_final n phi : estimation_layer n phi n = phase_vector n phi.
Proof.
rewrite phase_vector_product /estimation_layer; apply: eq_tentv_tuple=>i.
by rewrite /estimation_factors ltn_ord.
Qed.

Lemma estimation_circuit_prefixE n T (U : 'FU('Ht T)) k phi (u : 'Ht T) :
  U u = expip (2 * phi) *: u -> (k <= n)%N ->
  estimation_circuit_prefix n U k (''(nseq_tuple n false) ⊗t u) =
    estimation_layer n phi k ⊗t u.
Proof.
move=>Hu; elim: k=>[|k IH] Hkn.
- by rewrite /estimation_circuit_prefix take0 /= lfunE estimation_layer_initial.
- have Hk : (k < n)%N := Hkn.
  pose i : 'I_n := Ordinal Hk.
  rewrite /estimation_circuit_prefix (take_nth i) ?size_enum_ord //
    (nth_ord_enum i i) map_rcons unitary_list_rcons
    -/(estimation_circuit_prefix n U k) (IH (ltnW Hk)).
  exact: estimation_stageE Hu.
Qed.

Theorem estimation_circuit_eigen n T (U : 'FU('Ht T)) phi (u : 'Ht T) :
  U u = expip (2 * phi) *: u ->
  estimation_circuit_prefix n U n (''(nseq_tuple n false) ⊗t u) =
    phase_vector n phi ⊗t u.
Proof. by move=>Hu; rewrite (estimation_circuit_prefixE Hu) // estimation_layer_final. Qed.

End ClassicalPhaseStages.
