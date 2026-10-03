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


Module DistributedProtocolRemoteLocal.
Import DistributedProtocolQuantum DistributedProtocolState.
Local Notation C := hermitian.C.

Lemma remote_embed_adjoint x z y w :
  (remote_embed x z)^A \o remote_embed y w =
    ((x == y) && (z == w))%:R *: (\1 : 'End('Hs (bool * bool)%type)).
Proof.
apply/(intro_onb t2tv)=>[[b c]] /=; apply/(intro_onbl t2tv)=>[[d e]] /=.
rewrite comp_lfunE adj_dotEr !remote_embed_basis !tentv_dot !onb_dot
  scale_lfunE dotpZr id_lfunE onb_dot /=.
rewrite xpair_eqE.
by case: (x == y); case: (z == w); case: (d == b); case: (e == c)=>/=;
  rewrite ?mulr0 ?mul0r ?mulr1 ?mul1r.
Qed.

Lemma remote_embed_dot x z y w u v :
  [< remote_embed x z u; remote_embed y w v >] =
    ((x == y) && (z == w))%:R * [< u; v >].
Proof.
by rewrite -adj_dotEr -comp_lfunE remote_embed_adjoint scale_lfunE dotpZr id_lfunE.
Qed.

Definition remote_states (v : 'Hs (bool * bool)%type) (i : bool * bool) :=
  remote_embed i.1 i.2 (CNOT v).

Definition remote_output (v : 'Hs (bool * bool)%type) :=
  \sum_i [> remote_states v i; remote_states v i <].

Lemma remote_states_dot v : [< v; v >] = 1 ->
  forall i j, [< remote_states v i; remote_states v j >] = (i == j)%:R.
Proof.
move=>Hv [x z] [y w]; rewrite /remote_states remote_embed_dot isof_dot Hv mulr1.
by rewrite xpair_eqE.
Qed.

Lemma remote_output_embed v x z : [< v; v >] = 1 ->
  remote_output v (remote_embed x z (CNOT v)) = remote_embed x z (CNOT v).
Proof.
move=>Hv; change (remote_output v (remote_states v (x,z)) = remote_states v (x,z)).
rewrite /remote_output sum_lfunE (bigD1 (x,z)) //= big1.
- move=>[y w] /negPf H; rewrite outpE (remote_states_dot Hv) H scale0r.
  by [].
- by rewrite outpE (remote_states_dot Hv) eqxx scale1r addr0.
Qed.

Section NormalizedInput.
Variable v : 'Hs (bool * bool)%type.
Hypothesis normalized_v : [< v; v >] = 1.
HB.instance Definition _ := isPONB.Build _ _ (remote_states v)
  (remote_states_dot normalized_v).

Lemma remote_output_obs : remote_output v \is obslf.
Proof.
rewrite obslfE /remote_output; apply/andP; split.
- apply: sumv_ge0=>i _; exact: outp_ge0.
- exact: sumponb_out.
Qed.
End NormalizedInput.

Definition remote_local_pre (v : 'Hs (bool * bool)%type) :=
  \sum_x \sum_z (formso (remote_branch x z))^*o (remote_output v).

Lemma remote_local_success v : [< v; v >] = 1 ->
  [< remote_resource v; remote_local_pre v (remote_resource v) >] = 1.
Proof.
move=>Hv; rewrite /remote_local_pre sum_lfunE dotp_sumr.
under eq_bigr=>x _ do rewrite sum_lfunE dotp_sumr.
have Hbranch x z :
  [< remote_resource v;
     (formso (remote_branch x z))^*o (remote_output v) (remote_resource v) >] = (4%:R^-1 : C)%R.
  have Hb : remote_branch x z (remote_resource v) =
      ((-1)^(x && z) / 2%:R : C)%R *: remote_embed x z (CNOT v).
    by rewrite -comp_lfunE remote_branch_correct scale_lfunE comp_lfunE.
  rewrite dualso_formE !comp_lfunE adj_dotEr !Hb.
  rewrite linearZ /= remote_output_embed // dotpZl dotpZr isof_dot isof_dot Hv mulr1.
  clear Hb; case: x; case: z=>/=; rewrite ?signr0 ?signr1 ?mul1r ?mulN1r;
  rewrite ?rmorphN /= geC0_conj ?invr_ge0 // ?mulNr ?mulrN ?opprK;
  by rewrite -invfM -natrM.
under eq_bigr=>x _ do under eq_bigr=>z _ do rewrite Hbranch.
rewrite !big_bool /= -!mulr2n -mulrnA.
by rewrite -[LHS]mulr_natr /= mulVf ?pnatr_eq0.
Qed.

End DistributedProtocolRemoteLocal.
