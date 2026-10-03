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
From quantum.example.distributive Require Import protocol_quantum.

Module DistributedProtocolState.
Import DistributedProtocolQuantum.
Local Notation C := hermitian.C.

Lemma teleport_embedE z x (u : 'Hs bool) :
  teleport_embed z x u = (''z ⊗t ''x) ⊗t u.
Proof.
rewrite [u](onb_vec t2tv) linear_sum /= linear_sumr /=.
apply: eq_bigr=>i _.
by rewrite linearZ /= teleport_embed_basis linearZr.
Qed.

Lemma teleport_embed_isolf z x : teleport_embed z x \is isolf.
Proof.
apply/isolfP/(intro_onb t2tv)=>b /=; apply/(intro_onbl t2tv)=>c /=.
by rewrite comp_lfunE adj_dotEr id_lfunE !teleport_embed_basis
  !tentv_dot !ns_dot !mul1r.
Qed.
HB.instance Definition _ z x := isIsoLf.Build _ _ (teleport_embed z x)
  (teleport_embed_isolf z x).

Lemma teleport_resource_dot b c :
  [< teleport_resource ''b; teleport_resource ''c >] = (b == c)%:R.
Proof.
rewrite !teleport_resource_basis !(dotpZl, dotpZr) !(dotpDl, dotpDr) !tentv_dot !onb_dot
  geC0_conj ?invr_ge0 ?sqrtC_ge0 //.
case: b; case: c=>/=;
rewrite ?mulr0 ?mul0r ?addr0 ?add0r ?mulr1 ?mul1r ?divc_simp.
all: by rewrite ?mul0r -?natrD ?divff ?pnatr_eq0.
Qed.

Lemma teleport_resource_isolf : teleport_resource \is isolf.
Proof.
apply/isolfP/(intro_onb t2tv)=>b /=; apply/(intro_onbl t2tv)=>c /=.
by rewrite comp_lfunE adj_dotEr id_lfunE teleport_resource_dot onb_dot.
Qed.
HB.instance Definition _ := isIsoLf.Build _ _ teleport_resource teleport_resource_isolf.

Lemma remote_embed_isolf x z : remote_embed x z \is isolf.
Proof.
apply/isolfP/(intro_onb t2tv)=>[[b c]] /=; apply/(intro_onbl t2tv)=>[[d e]] /=.
rewrite comp_lfunE adj_dotEr id_lfunE !remote_embed_basis !tentv_dot !onb_dot
  !eqxx !mul1r !mulr1.
case: b; case: c; case: d; case: e=>/=; try by rewrite ?mulr0 ?mul0r ?mulr1 ?mul1r.
Qed.
HB.instance Definition _ x z := isIsoLf.Build _ _ (remote_embed x z)
  (remote_embed_isolf x z).

Lemma remote_resource_dot b c d e :
  [< remote_resource ''(b,c); remote_resource ''(d,e) >] = ((b,c) == (d,e))%:R.
Proof.
rewrite !remote_resource_basis !(dotpZl, dotpZr) !(dotpDl, dotpDr) !tentv_dot !onb_dot
  geC0_conj ?invr_ge0 ?sqrtC_ge0 //.
case: b; case: c; case: d; case: e=>/=;
rewrite ?mulr0 ?mul0r ?addr0 ?add0r ?mulr1 ?mul1r ?divc_simp.
all: by rewrite ?mul0r -?natrD ?divff ?pnatr_eq0.
Qed.

Lemma remote_resource_isolf : remote_resource \is isolf.
Proof.
apply/isolfP/(intro_onb t2tv)=>[[b c]] /=; apply/(intro_onbl t2tv)=>[[d e]] /=.
by rewrite comp_lfunE adj_dotEr id_lfunE remote_resource_dot onb_dot.
Qed.
HB.instance Definition _ := isIsoLf.Build _ _ remote_resource remote_resource_isolf.

Lemma formso_scale (U V : chsType) (a : C) (A : 'Hom(U,V)) :
  formso (a *: A) = (a * a^*) *: formso A.
Proof.
apply/superopP=>rho.
by rewrite !soE adjfZ -!comp_lfunZl -!comp_lfunZr scalerA.
Qed.

Lemma teleport_channel_correct z x :
  formso (teleport_branch z x) :o formso teleport_resource =
    4%:R^-1 *: formso (teleport_embed z x).
Proof.
rewrite formso_comp teleport_branch_correct formso_scale.
by rewrite geC0_conj ?invr_ge0 // -invfM -natrM.
Qed.

Lemma remote_channel_correct x z :
  formso (remote_branch x z) :o formso remote_resource =
    4%:R^-1 *: formso (remote_embed x z \o CNOT).
Proof.
rewrite formso_comp remote_branch_correct formso_scale.
case: x; case: z=>/=; rewrite ?signr0 ?signr1 ?mul1r ?mulN1r;
rewrite ?rmorphN /= geC0_conj ?invr_ge0 // ?mulNr ?mulrN ?opprK;
by rewrite -invfM -natrM.
Qed.

End DistributedProtocolState.
