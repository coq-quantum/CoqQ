(* Branch equations for distributed protocols; see PROTOCOLS-NOTES.md. *)
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

From quantum Require Import qtype.
From quantum.example.distributive Require Import protocol_quantum protocol_state.


Module DistributedProtocolLocal.
Import DistributedProtocolQuantum DistributedProtocolState.
Local Notation C := hermitian.C.

Definition teleport_output (v : 'Hs bool) :=
  (\1 : 'End('Hs (bool * bool)%type)) ⊗f [> v; v <].

Definition teleport_local_pre (v : 'Hs bool) :=
  \sum_z \sum_x (formso (teleport_branch z x))^*o (teleport_output v).

Lemma teleport_output_embed v z x : [< v; v >] = 1 ->
  teleport_output v (teleport_embed z x v) = teleport_embed z x v.
Proof.
move=>Hv; rewrite /teleport_output !teleport_embedE tentf_apply id_lfunE outpE Hv.
by rewrite scale1r.
Qed.

Lemma teleport_local_success v : [< v; v >] = 1 ->
  [< teleport_resource v; teleport_local_pre v (teleport_resource v) >] = 1.
Proof.
move=>Hv; rewrite /teleport_local_pre sum_lfunE dotp_sumr.
under eq_bigr=>z _ do rewrite sum_lfunE dotp_sumr.
have Hbranch z x :
  [< teleport_resource v;
     (formso (teleport_branch z x))^*o (teleport_output v) (teleport_resource v) >] = (4%:R^-1 : C)%R.
  have Hb : teleport_branch z x (teleport_resource v) =
      (2%:R^-1 : C)%R *: teleport_embed z x v.
    by rewrite -comp_lfunE teleport_branch_correct scale_lfunE.
  rewrite dualso_formE !comp_lfunE adj_dotEr !Hb.
  rewrite linearZ /= teleport_output_embed // dotpZl dotpZr geC0_conj ?invr_ge0 //.
  rewrite isof_dot Hv mulr1 -invfM -natrM.
  by [].
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite Hbranch.
rewrite !big_bool /= -!mulr2n -mulrnA.
by rewrite -[LHS]mulr_natr /= mulVf ?pnatr_eq0.
Qed.

Lemma normalized_outp_obs (U : chsType) (v : U) : [< v; v >] = 1 ->
  [> v; v <] \is obslf.
Proof.
move=>Hv; rewrite obslfE outp_ge0 /=.
apply: outp_le1; by rewrite Hv.
Qed.

Lemma teleport_output_obs v : [< v; v >] = 1 -> teleport_output v \is obslf.
Proof.
move=>Hv; rewrite /teleport_output (ObsLf_BuildE (normalized_outp_obs Hv)).
exact: is_obslf.
Qed.

End DistributedProtocolLocal.
