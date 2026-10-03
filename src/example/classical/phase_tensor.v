(* Repeated controlled-U on one indexed control qubit. *)
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
From quantum.example.classical Require Import phase_estimation phase_program.

Module ClassicalPhaseTensor.
Import ClassicalPhaseEstimation ClassicalPhaseProgram.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition bit_diagonal n (i : 'I_n) (phi : R) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of expmxip t2tv (fun bs : n.-tuple bool => (bs~_i)%:R) (2 * phi)].

Lemma bit_diagonal_basis n (i : 'I_n) phi (bs : n.-tuple bool) :
  bit_diagonal i phi ''bs = expip ((bs~_i)%:R * (2 * phi)) *: ''bs.
Proof. exact: expmxipEt. Qed.

Lemma controlled_power_basis n T (U : 'FU('Ht T)) (i : 'I_n)
    k (bs : n.-tuple bool) (u : 'Ht T) :
  ((controlled_at U i)%:VF ^+ k) (''bs ⊗t u) =
  ''bs ⊗t (if bs~_i then (U%:VF ^+ k) u else u).
Proof.
elim: k=>[|k IH].
- by rewrite expr0 lfunE; case: (bs~_i); rewrite ?lfunE.
- rewrite exprS lfunE /= IH /controlled_at MultiplexerEt.
  by case: (bs~_i); rewrite /= ?exprS ?lfunE.
Qed.

Lemma controlled_power_eigen n T (U : 'FU('Ht T)) (i : 'I_n)
    k (v : 'Hs (n.-tuple bool)) (u : 'Ht T) (phi : R) :
  U u = expip (2 * phi) *: u ->
  ((controlled_at U i)%:VF ^+ k) (v ⊗t u) =
    bit_diagonal i (k%:R * phi) v ⊗t u.
Proof.
move=>Hu; rewrite [v](onb_vec t2tv) linear_sumlz /= linear_sum /=
  [in RHS]linear_sum /= linear_sumlz /=.
apply eq_bigr=>bs _.
rewrite !linearZl /= !linearZ /= controlled_power_basis bit_diagonal_basis.
case E: (bs~_i)=>/=.
- have Er : k%:R * (2 * phi) = 2 * (k%:R * phi) by rewrite mulrCA.
  by rewrite (eigen_power Hu) !linearZ /= !linearZl /= mul1r Er.
- by rewrite mul0r expip0 scale1r !linearZl.
Qed.

Lemma binary_weight_sum n (bs : n.-tuple bool) :
  (bseq2ord bs : nat) =
    (\sum_(i < n) (bs~_i) * 2 ^ (n - i.+1))%N.
Proof.
elim: n bs=>[bs|n IH bs].
- by rewrite tuple0 /bseq2ord /bseq2nat /= big_ord0.
- case/tupleP: bs=>b bs.
  change (bseq2nat (b :: bs) =
    (\sum_(i < n.+1) ([tuple of b :: bs]~_i) * 2 ^ (n.+1 - i.+1))%N).
  rewrite [LHS]bseq2nat_cons {1}(size_tuple bs) big_ord_recl /= tnth0 subn1 /=.
  rewrite mulnC; congr (_ + _)%N.
  transitivity (bseq2ord bs : nat); first by [].
  rewrite IH; apply: eq_bigr=>i _.
  by rewrite tnthS.
Qed.

Lemma binary_weight_sum_real n (bs : n.-tuple bool) :
  (bseq2ord bs)%:R =
    \sum_(i < n) (bs~_i)%:R * (2%:R : R) ^+ (n - i.+1).
Proof.
rewrite binary_weight_sum natr_sum; apply: eq_bigr=>i _.
by rewrite natrM natrX.
Qed.

Lemma phase_vector_coefficient n phi (bs : n.-tuple bool) :
  [< ''bs; phase_vector n phi >] =
    (sqrtC 2%:R ^- n) * expip ((bseq2ord bs)%:R * (2 * phi)).
Proof.
rewrite phase_vectorE dotpZr dotp_sumr (bigD1 bs) //= big1.
- by move=>j /negPf Eji; rewrite dotpZr onb_dot eq_sym Eji mulr0.
- by rewrite dotpZr ns_dot mulr1 addr0.
Qed.

Lemma phase_vector_product n phi :
  phase_vector n phi =
    tentv_tuple (fun i : 'I_n => phstate (2%:R ^+ (n - i.+1) * phi)).
Proof.
apply/(intro_onbl t2tv)=>bs /=.
rewrite phase_vector_coefficient t2tv_tuple tentv_tuple_dot.
under eq_bigr do rewrite dotp_cbph.
rewrite big_split /= prodr_const card_ord exprVn expip_prod.
congr (_ * _); congr (expip _).
rewrite binary_weight_sum_real mulr_suml; apply: eq_bigr=>i _.
by rewrite !mulrA [(bs~_i)%:R * _ * 2]mulrAC [(bs~_i)%:R * 2]mulrC.
Qed.

End ClassicalPhaseTensor.
