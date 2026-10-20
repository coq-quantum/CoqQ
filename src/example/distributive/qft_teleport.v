(** Distributed QFT: Bell resources and quantum transfer.

    This file proves Bell preparation, teleportation with an arbitrary
    reference and destination state, and reduced data-channel identities.
    The native protocol proofs connect measured branches and classical
    corrections to the transfer operation used by qft.isq.

    Contents, in dependency order:
      1. DistributedQFTTeleport: state and branch algebra.
      2. DistributedQFTBell / DistributedQFTBellSupport: Bell preparation.
      3. DistributedQFTReduction: register marginals and auxiliary erasure.
      4. DistributedQFTTeleportProcesses: native protocol executions.
      5. DistributedQFTTransferCorrectness: the complete transfer channel.
      6. DistributedQFTISQTransfer: qft.isq transfer variants.

    The source and allocation model is in qft_model.v.
    Complete physical program correctness is in qft.v.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology svd
  mxnorm hermitian inhabited prodvect tensor quantum hspace summable qtype.
From quantum.example.distributive Require Import protocols.
From quantum Require Import qreg qmem hspace_extra.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import language state assertion semantics hoare
  auxiliary.
From quantum.example.distributive Require Import language operational confluence
  semantics sequentialization hoare auxiliary.
From Stdlib Require Import String.
From mathcomp Require Import perm.
From quantum.example.distributive Require Import qft_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(** 1. Teleportation state and branch algebra *)

(* State transfer used by qft.isq.  The source sends the pair outcome x
   before the data outcome z; the receiver applies X, then Z, then SWAP.
   The equations below concern channels on arbitrary operators, so they
   preserve correlations with the other QFT qubits. *)

Lemma transfer_bool_pair_sum (V : zmodType) (f : bool -> bool -> V) :
  (\sum_x \sum_z f x z)%R = (\sum_(i : bool * bool) f i.1 i.2)%R.
Proof. by rewrite pair_bigV. Qed.

Module DistributedQFTTeleport.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import DistributedProtocolQuantum DistributedProtocolState.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation data_type := (bool * bool)%type.
Local Notation physical_type := (((bool * bool) * bool) * bool)%type.
Local Notation paired_type := ((bool * bool) * (bool * bool))%type.

Definition transfer_layout_index (i : physical_type) : paired_type :=
  (i.1.1, (i.1.2,i.2)).
Definition transfer_unlayout_index (i : paired_type) : physical_type :=
  ((i.1,i.2.1),i.2.2).
Lemma transfer_layout_indexK : cancel transfer_layout_index transfer_unlayout_index.
Proof. by move=>[[[a b] c] d]. Qed.
Lemma transfer_layout_index_inj : injective transfer_layout_index.
Proof. exact: can_inj transfer_layout_indexK. Qed.
Definition transfer_layout : 'Hom('Hs physical_type, 'Hs paired_type) :=
  \sum_(i : physical_type) [> ''(transfer_layout_index i); ''i <].
Lemma transfer_layout_basis i : transfer_layout ''i = ''(transfer_layout_index i).
Proof.
rewrite /transfer_layout sum_lfunE (bigD1 i) //= big1.
- by move=>j /negPf Hji; rewrite outpE onb_dot Hji scale0r.
- by rewrite outpE ns_dot scale1r addr0.
Qed.
Lemma transfer_layout_isolf : transfer_layout \is isolf.
Proof.
apply/isolfP/(intro_onb t2tv)=>i /=; apply/(intro_onbl t2tv)=>j /=.
by rewrite comp_lfunE adj_dotEr id_lfunE !transfer_layout_basis
  !onb_dot (inj_eq transfer_layout_index_inj).
Qed.
HB.instance Definition _ := isIsoLf.Build _ _ transfer_layout transfer_layout_isolf.

Lemma transfer_layout_adjoint_basis i :
  transfer_layout^A ''i = ''(transfer_unlayout_index i).
Proof.
case: i=>[[a b] [c d]]; apply/(intro_onbl t2tv)=>[[[[w x] y] z]] /=.
by rewrite adj_dotEr transfer_layout_basis !onb_dot
  /transfer_layout_index /transfer_unlayout_index !xpair_eqE /= !andbA.
Qed.

Lemma transfer_layout_gisolf : transfer_layout \is gisolf.
Proof.
apply/gisolfP; split; first exact: isofE.
apply/(intro_onb t2tv)=>[[[a b] [c d]]] /=.
by rewrite comp_lfunE transfer_layout_adjoint_basis transfer_layout_basis
  /transfer_layout_index /transfer_unlayout_index id_lfunE.
Qed.
HB.instance Definition _ := Iso_isGisoLf.Build _ _ transfer_layout transfer_layout_gisolf.

(* Physical wire order: sender data, sender EPR half, receiver EPR half,
   destination.  The final operation swaps only the last two wires. *)
Definition transfer_swap_index (i : physical_type) : physical_type :=
  ((i.1.1, i.2), i.1.2).

Lemma transfer_swap_indexK : involutive transfer_swap_index.
Proof. by move=>[[[z x] c] d]. Qed.

Lemma transfer_swap_index_inj : injective transfer_swap_index.
Proof. exact: can_inj transfer_swap_indexK. Qed.

Definition transfer_swap : 'End('Hs physical_type) :=
  \sum_(i : physical_type) [> ''(transfer_swap_index i); ''i <].

Lemma transfer_swap_basis i : transfer_swap ''i = ''(transfer_swap_index i).
Proof.
rewrite /transfer_swap sum_lfunE (bigD1 i) //= big1.
- by move=>j /negPf Hji; rewrite outpE onb_dot Hji scale0r.
- by rewrite outpE ns_dot scale1r addr0.
Qed.

Lemma transfer_swap_isolf : transfer_swap \is isolf.
Proof.
apply/isolfP/(intro_onb t2tv)=>i /=; apply/(intro_onbl t2tv)=>j /=.
by rewrite comp_lfunE adj_dotEr id_lfunE !transfer_swap_basis
  !onb_dot (inj_eq transfer_swap_index_inj).
Qed.
HB.instance Definition _ := isIsoLf.Build _ _ transfer_swap transfer_swap_isolf.

(* This basis equation records the actual SWAP, including the old
   destination state which moves into the disposable pair register. *)
Lemma transfer_swap_last z x c d :
  transfer_swap ((( ''z ⊗t ''x) ⊗t ''c) ⊗t ''d) =
    (( ''z ⊗t ''x) ⊗t ''d) ⊗t ''c.
Proof. by rewrite !tentv_t2tv transfer_swap_basis /transfer_swap_index. Qed.

(** Source/resource boundary: the two create_epr calls in qft.isq are
    represented by one independent shared Bell pair, supplied before this
    hop. This embedding preserves the input data and the old destination;
    it inserts the Bell pair rather than modeling the QMPI service itself.
    Its framed variants also preserve arbitrary correlations with a reference. *)
Definition transfer_resource : 'Hom('Hs data_type, 'Hs physical_type) :=
  teleport_resource ⊗f (\1 : 'End('Hs bool)).

Definition transfer_branch z x : 'End('Hs physical_type) :=
  transfer_swap \o (teleport_branch z x ⊗f (\1 : 'End('Hs bool))).

(** Quartet coordinates are ((data, sender Bell half),
    (receiver Bell half, old destination)). Composition acts right to left:
    CNOT then H then the sender projections, and X then Z then receiver SWAP.
    The algebra collects both outcomes into one branch; the literal timing
    of measurement and transmission is proved later in DistributedQFTISQTransfer. *)
Definition transfer_paired_branch z x :
    'End('Hs ((bool * bool) * (bool * bool))%type) :=
  ((projector z ⊗f projector x) \o
    (Hadamard ⊗f (\1 : 'End('Hs bool))) \o CNOT) ⊗f
  (@swaptf bool bool \o
    ((pauli_z z \o pauli_x x) ⊗f (\1 : 'End('Hs bool)))).

Definition transfer_embed z x : 'Hom('Hs data_type, 'Hs physical_type) :=
  transfer_swap \o (teleport_embed z x ⊗f (\1 : 'End('Hs bool))).

Lemma transfer_embed_basis z x c d :
  transfer_embed z x ''(c,d) = ''(((z,x),d),c).
Proof.
rewrite /transfer_embed comp_lfunE -[ ''(c,d)]tentv_t2tv.
by rewrite tentf_apply teleport_embed_basis id_lfunE !tentv_t2tv
  transfer_swap_basis /transfer_swap_index.
Qed.

Definition transfer_paired_resource := transfer_layout \o transfer_resource.
Definition transfer_paired_embed z x := transfer_layout \o transfer_embed z x.

Lemma transfer_paired_embed_basis z x c d :
  transfer_paired_embed z x ''(c,d) = ''((z,x),(d,c)).
Proof.
by rewrite /transfer_paired_embed comp_lfunE transfer_embed_basis
  transfer_layout_basis /transfer_layout_index.
Qed.

Lemma transfer_paired_resource_basis c d :
  transfer_paired_resource ''(c,d) = (sqrtC 2%:R)^-1 *:
    (((''c ⊗t '0) ⊗t ('0 ⊗t ''d)) + ((''c ⊗t '1) ⊗t ('1 ⊗t ''d))).
Proof.
rewrite /transfer_paired_resource /transfer_resource comp_lfunE
  -[ ''(c,d)]tentv_t2tv tentf_apply id_lfunE teleport_resource_basis
  linearZl /= linearDl /= linearZ /= linearD /= !tentv_t2tv
  !transfer_layout_basis /transfer_layout_index.
by [].
Qed.

Lemma transfer_paired_branch_correct z x :
  transfer_paired_branch z x \o transfer_paired_resource =
    2%:R^-1 *: transfer_paired_embed z x.
Proof.
apply/(intro_onb t2tv)=>[[c d]] /=.
rewrite scale_lfunE transfer_paired_embed_basis.
rewrite /transfer_paired_branch !lfunE /= transfer_paired_resource_basis
  linearZ /= linearD /= !tentf_apply !lfunE /= !CNOT_cb.
rewrite !lfunE /= !tentf_apply !lfunE /=.
rewrite !measured_hadamard !projector_basis !pauli_x_basis !pauli_z_basis
  !linearZr /= !linearZl /= !linearZ /= !swaptfEtv
  ?linearZr /= !scalerA -!tentv_t2tv.
case: z; case: x; case: c=>/=;
rewrite ?eqxx ?expr0z ?expr1z.
all: rewrite !sign_simp ?mulr0 ?mul0r ?oppr0 ?scale0r ?addr0 ?add0r
  scalerA !divc_simp.
all: by [].
Qed.

Lemma transfer_branch_correct z x :
  transfer_branch z x \o transfer_resource = 2%:R^-1 *: transfer_embed z x.
Proof.
rewrite /transfer_branch /transfer_resource /transfer_embed -comp_lfunA
  tentf_comp teleport_branch_correct comp_lfun1l tentfZl.
by rewrite -comp_lfunZr.
Qed.

Lemma transfer_embed_adjoint z x w y :
  (transfer_embed z x)^A \o transfer_embed w y =
    ((z == w) && (x == y))%:R *: (\1 : 'End('Hs data_type)).
Proof.
apply/(intro_onb t2tv)=>[[c d]] /=;
  apply/(intro_onbl t2tv)=>[[a b]] /=.
rewrite comp_lfunE adj_dotEr !transfer_embed_basis !onb_dot
  scale_lfunE dotpZr id_lfunE onb_dot !xpair_eqE /=.
by case: (z == w); case: (x == y); case: (a == c); case: (b == d)=>/=;
  rewrite ?mulr0 ?mul0r ?mulr1 ?mul1r ?andbT ?andbF.
Qed.

Lemma transfer_embed_isolf z x : transfer_embed z x \is isolf.
Proof.
by apply/isolfP; rewrite transfer_embed_adjoint !eqxx scale1r.
Qed.
HB.instance Definition _ z x := isIsoLf.Build _ _ (transfer_embed z x)
  (transfer_embed_isolf z x).

Lemma transfer_embed_adjoint_basis z x a b c d :
  (transfer_embed z x)^A ''(((a,b),c),d) =
    ((z == a) && (x == b))%:R *: ''(d,c).
Proof.
apply/(intro_onbl t2tv)=>[[e f]] /=.
rewrite adj_dotEr transfer_embed_basis dotpZr !onb_dot !xpair_eqE /=.
by case: (z == a); case: (x == b); case: (e == d); case: (f == c)=>/=;
  rewrite ?mulr0 ?mul0r ?mulr1 ?mul1r ?andbT ?andbF.
Qed.

Lemma transfer_embed_complete :
  \sum_z \sum_x (transfer_embed z x \o (transfer_embed z x)^A) =
    (\1 : 'End('Hs physical_type)).
Proof.
apply/(intro_onb t2tv)=>[[[[a b] c] d]] /=.
rewrite sum_lfunE id_lfunE.
under eq_bigr do rewrite sum_lfunE.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite comp_lfunE transfer_embed_adjoint_basis linearZ /= transfer_embed_basis.
by rewrite !big_bool; case: a; case: b=>/=;
  rewrite ?scale0r ?scale1r ?addr0 ?add0r.
Qed.

(* Discard both measured sender wires, and view the destination as the
   original logical data wire.  The old destination is retained as the
   second logical output; subsequent disposal can therefore be framed. *)
Definition transfer_decode : 'SO('Hs physical_type, 'Hs data_type) :=
  krausso (fun i : bool * bool => (transfer_embed i.1 i.2)^A).

Lemma transfer_decode_cptp : transfer_decode \is cptp.
Proof.
apply/krausso_qcP; apply/eqP; rewrite pair_bigV /=.
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite adjfK.
exact: transfer_embed_complete.
Qed.

Lemma krausso_sum_form (U V : chsType) (I : finType) (K : I -> 'Hom(U,V)) :
  krausso K = \sum_i formso (K i).
Proof.
apply/superopP=>rho; rewrite kraussoE sum_soE.
by apply: eq_bigr=>i _; rewrite formsoE.
Qed.

Lemma transfer_decode_embed z x :
  transfer_decode :o formso (transfer_embed z x) = \:1.
Proof.
rewrite /transfer_decode krausso_sum_form linear_sumlz /=.
under eq_bigr do rewrite formso_comp transfer_embed_adjoint.
rewrite (bigD1 (z,x)) //= big1.
- move=>[a b] /negPf H.
  rewrite !xpair_eqE in H.
  by rewrite H scale0r formso0.
- by rewrite !eqxx scale1r formso1 addr0.
Qed.

Lemma transfer_branch_channel z x :
  formso (transfer_branch z x) :o formso transfer_resource =
    4%:R^-1 *: formso (transfer_embed z x).
Proof.
rewrite formso_comp transfer_branch_correct formso_scale.
by rewrite geC0_conj ?invr_ge0 // -invfM -natrM.
Qed.

Definition transfer_channel := \sum_z \sum_x formso (transfer_branch z x).

Theorem transfer_channel_correct :
  transfer_decode :o transfer_channel :o formso transfer_resource = \:1.
Proof.
rewrite /transfer_channel -comp_soA linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do rewrite linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite transfer_branch_channel comp_soZr transfer_decode_embed.
by rewrite !big_bool /= -!mulr2n -mulrnA -scaler_nat scalerA
  mulfV ?pnatr_eq0 // scale1r.
Qed.

Definition transfer_paired_decode := transfer_decode :o formso ((transfer_layout)^A).
Definition transfer_paired_channel := \sum_z \sum_x formso (transfer_paired_branch z x).

Lemma transfer_paired_decode_embed z x :
  transfer_paired_decode :o formso (transfer_paired_embed z x) = \:1.
Proof.
rewrite /transfer_paired_decode /transfer_paired_embed -comp_soA formso_comp
  comp_lfunA isofE comp_lfun1l.
exact: transfer_decode_embed.
Qed.

Lemma transfer_paired_branch_channel z x :
  formso (transfer_paired_branch z x) :o formso transfer_paired_resource =
    4%:R^-1 *: formso (transfer_paired_embed z x).
Proof.
rewrite formso_comp transfer_paired_branch_correct formso_scale.
by rewrite geC0_conj ?invr_ge0 // -invfM -natrM.
Qed.

Theorem transfer_paired_channel_correct :
  transfer_paired_decode :o transfer_paired_channel :o formso transfer_paired_resource = \:1.
Proof.
rewrite /transfer_paired_channel -comp_soA linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do rewrite linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite transfer_paired_branch_channel comp_soZr transfer_paired_decode_embed.
by rewrite !big_bool /= -!mulr2n -mulrnA -scaler_nat scalerA
  mulfV ?pnatr_eq0 // scale1r.
Qed.

(* An arbitrary reference system may be entangled with either input wire.
   The identities below quantify over all operators, with no separability
   premise on rho. *)
Section Reference.
Variable R : ihbFinType.
Local Notation logical_reference := (data_type * R)%type.
Local Notation physical_reference := (physical_type * R)%type.

Definition transfer_resource_ref :
    'Hom('Hs logical_reference, 'Hs physical_reference) :=
  transfer_resource ⊗f (\1 : 'End('Hs R)).
Definition transfer_branch_ref z x : 'End('Hs physical_reference) :=
  transfer_branch z x ⊗f (\1 : 'End('Hs R)).
Definition transfer_embed_ref z x :
    'Hom('Hs logical_reference, 'Hs physical_reference) :=
  transfer_embed z x ⊗f (\1 : 'End('Hs R)).
Definition transfer_decode_ref : 'SO('Hs physical_reference, 'Hs logical_reference) :=
  krausso (fun i : bool * bool => (transfer_embed_ref i.1 i.2)^A).
Definition transfer_channel_ref := \sum_z \sum_x formso (transfer_branch_ref z x).

(* Kraus contractions for the partial trace over the old destination.
   The data and reference retain their joint density operator. *)
Definition discard_old_destination_kraus (d : bool) :
    'Hom('Hs logical_reference, 'Hs (bool * R)%type) :=
  \sum_(i : bool * R) [> ''i; ''((i.1,d),i.2) <].
Lemma discard_old_destination_kraus_basis d c e r :
  discard_old_destination_kraus d ''((c,e),r) =
    (d == e)%:R *: ''(c,r).
Proof.
rewrite /discard_old_destination_kraus sum_lfunE (bigD1 (c,r)) //= big1.
- move=>[k s] /negPf H.
  rewrite !xpair_eqE in H.
  by rewrite outpE onb_dot !xpair_eqE /= andbAC H /= scale0r.
- by rewrite outpE onb_dot !xpair_eqE !eqxx /= andbT addr0.
Qed.
Definition discard_old_destination_ref :
    'SO('Hs logical_reference, 'Hs (bool * R)%type) :=
  krausso discard_old_destination_kraus.
Lemma discard_old_destination_ref_outp c d r k e s :
  discard_old_destination_ref [> ''((c,d),r); ''((k,e),s) <] =
    (d == e)%:R *: [> ''(c,r); ''(k,s) <].
Proof.
rewrite /discard_old_destination_ref kraussoE.
under eq_bigr do rewrite outp_compr outp_compl adjfK
  !discard_old_destination_kraus_basis outpZl outpZr scalerA.
rewrite (bigD1 d) //= big1.
- move=>i /negPf Hi.
  by rewrite Hi mul0r scale0r.
- by rewrite eqxx mul1r addr0 geC0_conj ?ler0n.
Qed.
Definition transfer_data_output_ref := discard_old_destination_ref :o transfer_decode_ref.

Definition transfer_paired_resource_ref := transfer_paired_resource ⊗f (\1 : 'End('Hs R)).
Definition transfer_paired_branch_ref z x := transfer_paired_branch z x ⊗f (\1 : 'End('Hs R)).
Definition transfer_paired_decode_ref := transfer_decode_ref :o
  formso ((transfer_layout)^A ⊗f (\1 : 'End('Hs R))).
Definition transfer_paired_channel_ref := \sum_z \sum_x formso (transfer_paired_branch_ref z x).
Definition transfer_paired_data_output_ref := discard_old_destination_ref :o transfer_paired_decode_ref.

Lemma transfer_branch_ref_correct z x :
  transfer_branch_ref z x \o transfer_resource_ref =
    2%:R^-1 *: transfer_embed_ref z x.
Proof.
by rewrite /transfer_branch_ref /transfer_resource_ref /transfer_embed_ref
  tentf_comp transfer_branch_correct comp_lfun1l tentfZl.
Qed.

Lemma transfer_embed_ref_adjoint z x w y :
  (transfer_embed_ref z x)^A \o transfer_embed_ref w y =
    ((z == w) && (x == y))%:R *: (\1 : 'End('Hs logical_reference)).
Proof.
by rewrite /transfer_embed_ref tentf_adj tentf_comp transfer_embed_adjoint
  adjf1 comp_lfun1l tentfZl tentf11.
Qed.

Lemma transfer_decode_ref_embed z x :
  transfer_decode_ref :o formso (transfer_embed_ref z x) = \:1.
Proof.
rewrite /transfer_decode_ref krausso_sum_form linear_sumlz /=.
under eq_bigr do rewrite formso_comp transfer_embed_ref_adjoint.
rewrite (bigD1 (z,x)) //= big1.
- move=>[a b] /negPf H.
  rewrite !xpair_eqE in H.
  by rewrite H scale0r formso0.
- by rewrite !eqxx scale1r formso1 addr0.
Qed.

Lemma transfer_branch_ref_channel z x :
  formso (transfer_branch_ref z x) :o formso transfer_resource_ref =
    4%:R^-1 *: formso (transfer_embed_ref z x).
Proof.
rewrite formso_comp transfer_branch_ref_correct formso_scale.
by rewrite geC0_conj ?invr_ge0 // -invfM -natrM.
Qed.

Lemma transfer_decoded_branch_ref z x :
  transfer_decode_ref :o formso (transfer_branch_ref z x) :o
    formso transfer_resource_ref = 4%:R^-1 *: (\:1 : 'SO('Hs logical_reference)).
Proof.
by rewrite -comp_soA transfer_branch_ref_channel comp_soZr transfer_decode_ref_embed.
Qed.

Theorem transfer_channel_ref_correct :
  transfer_decode_ref :o transfer_channel_ref :o formso transfer_resource_ref = \:1.
Proof.
rewrite /transfer_channel_ref -comp_soA linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do rewrite linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite transfer_branch_ref_channel comp_soZr transfer_decode_ref_embed.
by rewrite !big_bool /= -!mulr2n -mulrnA -scaler_nat scalerA
  mulfV ?pnatr_eq0 // scale1r.
Qed.

Corollary transfer_entangled_state (rho : 'End('Hs logical_reference)) :
  transfer_decode_ref (transfer_channel_ref (formso transfer_resource_ref rho)) = rho.
Proof. by rewrite -!comp_soE transfer_channel_ref_correct id_soE. Qed.

Theorem transfer_reduced_data_ref_correct :
  transfer_data_output_ref :o transfer_channel_ref :o formso transfer_resource_ref =
    discard_old_destination_ref.
Proof.
by rewrite /transfer_data_output_ref -!comp_soA
  (comp_soA transfer_decode_ref transfer_channel_ref (formso transfer_resource_ref))
  transfer_channel_ref_correct comp_so1r.
Qed.

Corollary transfer_reduced_entangled_state (rho : 'End('Hs logical_reference)) :
  transfer_data_output_ref (transfer_channel_ref (formso transfer_resource_ref rho)) =
    discard_old_destination_ref rho.
Proof. by rewrite -!comp_soE transfer_reduced_data_ref_correct. Qed.
Lemma transfer_paired_ref_branch_channel z x :
  formso (transfer_paired_branch_ref z x) :o formso transfer_paired_resource_ref =
    4%:R^-1 *: formso (transfer_paired_embed z x ⊗f (\1 : 'End('Hs R))).
Proof.
rewrite /transfer_paired_branch_ref /transfer_paired_resource_ref formso_comp
  tentf_comp transfer_paired_branch_correct comp_lfun1l tentfZl formso_scale.
by rewrite geC0_conj ?invr_ge0 // -invfM -natrM.
Qed.

Lemma transfer_embed_ref_complete :
  \sum_(i : bool * bool) (transfer_embed_ref i.1 i.2 \o
    (transfer_embed_ref i.1 i.2)^A) = (\1 : 'End('Hs physical_reference)).
Proof.
rewrite pair_bigV /= /transfer_embed_ref.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite tentf_adj tentf_comp adjf1 comp_lfun1l.
under eq_bigr=>z _ do rewrite -linear_sumlz /=.
by rewrite -linear_sumlz /= transfer_embed_complete tentf11.
Qed.

Definition transfer_encoded_gate_ref (U : 'End('Hs logical_reference)) :=
  \sum_(i : bool * bool) (transfer_embed_ref i.1 i.2 \o U \o
    (transfer_embed_ref i.1 i.2)^A).

Lemma transfer_encoded_gate_ref_natural U z x :
  transfer_encoded_gate_ref U \o transfer_embed_ref z x =
    transfer_embed_ref z x \o U.
Proof.
rewrite /transfer_encoded_gate_ref linear_sumlz /=.
under eq_bigr do
  rewrite -!comp_lfunA transfer_embed_ref_adjoint -xpair_eqE.
rewrite (bigD1 (z,x)) //= big1.
- move=>[a b] /negPf H.
  by rewrite H scale0r !comp_lfun0r.
- by rewrite eqxx scale1r comp_lfun1r addr0.
Qed.

Lemma transfer_encoded_gate_ref_adj U :
  (transfer_encoded_gate_ref U)^A = transfer_encoded_gate_ref (U^A).
Proof.
rewrite /transfer_encoded_gate_ref adjf_sum.
by apply: eq_bigr=>[[z x]] _; rewrite !adjf_comp adjfK comp_lfunA.
Qed.

Lemma transfer_encoded_gate_ref_decoder U z x :
  (transfer_embed_ref z x)^A \o transfer_encoded_gate_ref U =
    U \o (transfer_embed_ref z x)^A.
Proof.
apply: adjf_inj.
by rewrite !adjf_comp transfer_encoded_gate_ref_adj adjfK
  transfer_encoded_gate_ref_natural.
Qed.

Lemma transfer_encoded_gate_ref_unitary (U : 'FU('Hs logical_reference)) :
  transfer_encoded_gate_ref U \is unitarylf.
Proof.
apply/unitarylfP; rewrite transfer_encoded_gate_ref_adj
  {2}/transfer_encoded_gate_ref linear_sumr /=.
under eq_bigr do rewrite !comp_lfunA
  transfer_encoded_gate_ref_natural -[(_ \o U^A) \o U]comp_lfunA
  isofE comp_lfun1r.
exact: transfer_embed_ref_complete.
Qed.
HB.instance Definition _ (U : 'FU('Hs logical_reference)) := isUnitaryLf.Build _
  (transfer_encoded_gate_ref U) (transfer_encoded_gate_ref_unitary U).

Lemma transfer_encoded_gate_ref_decode U :
  transfer_decode_ref :o formso (transfer_encoded_gate_ref U) =
    formso U :o transfer_decode_ref.
Proof.
rewrite /transfer_decode_ref krausso_sum_form linear_sumlz /= linear_sumr /=.
apply: eq_bigr=>[[z x]] _.
by rewrite !formso_comp transfer_encoded_gate_ref_decoder.
Qed.

Theorem transfer_encoded_gate_ref_correct U :
  transfer_decode_ref :o formso (transfer_encoded_gate_ref U) :o
    transfer_channel_ref :o formso transfer_resource_ref = formso U.
Proof.
rewrite transfer_encoded_gate_ref_decode -!comp_soA.
by rewrite (comp_soA transfer_decode_ref transfer_channel_ref (formso transfer_resource_ref))
  transfer_channel_ref_correct comp_so1r.
Qed.

Lemma transfer_paired_decode_ref_embed z x :
  transfer_paired_decode_ref :o
    formso (transfer_paired_embed z x ⊗f (\1 : 'End('Hs R))) = \:1.
Proof.
rewrite /transfer_paired_decode_ref /transfer_paired_embed -comp_soA formso_comp
  tentf_comp comp_lfunA isofE !comp_lfun1l.
exact: transfer_decode_ref_embed.
Qed.

Lemma transfer_paired_decoded_branch_ref z x :
  transfer_paired_decode_ref :o formso (transfer_paired_branch_ref z x) :o
    formso transfer_paired_resource_ref = 4%:R^-1 *: (\:1 : 'SO('Hs logical_reference)).
Proof.
by rewrite -comp_soA transfer_paired_ref_branch_channel comp_soZr
  transfer_paired_decode_ref_embed.
Qed.

Theorem transfer_paired_channel_ref_correct :
  transfer_paired_decode_ref :o transfer_paired_channel_ref :o
    formso transfer_paired_resource_ref = \:1.
Proof.
rewrite /transfer_paired_channel_ref -comp_soA linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do rewrite linear_sumlz /= linear_sumr /=.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite transfer_paired_ref_branch_channel comp_soZr transfer_paired_decode_ref_embed.
by rewrite !big_bool /= -!mulr2n -mulrnA -scaler_nat scalerA
  mulfV ?pnatr_eq0 // scale1r.
Qed.

Theorem transfer_paired_reduced_data_ref_correct :
  transfer_paired_data_output_ref :o transfer_paired_channel_ref :o
    formso transfer_paired_resource_ref = discard_old_destination_ref.
Proof.
rewrite -[RHS]comp_so1r -[in RHS]transfer_paired_channel_ref_correct.
by rewrite /transfer_paired_data_output_ref !comp_soA.
Qed.

Definition transfer_paired_embed_ref z x :=
  (transfer_layout ⊗f (\1 : 'End('Hs R))) \o transfer_embed_ref z x.

Lemma transfer_paired_embed_refE z x :
  transfer_paired_embed_ref z x =
    transfer_paired_embed z x ⊗f (\1 : 'End('Hs R)).
Proof.
by rewrite /transfer_paired_embed_ref /transfer_embed_ref tentf_comp
  comp_lfun1l /transfer_paired_embed.
Qed.

Lemma transfer_paired_embed_ref_basis z x c d r :
  transfer_paired_embed_ref z x ''((c,d),r) = ''(((z,x),(d,c)),r).
Proof.
by rewrite transfer_paired_embed_refE -[ ''((c,d),r)]tentv_t2tv
  tentf_apply transfer_paired_embed_basis id_lfunE tentv_t2tv.
Qed.

Lemma transfer_paired_embed_ref_adjoint z x w y :
  (transfer_paired_embed_ref z x)^A \o transfer_paired_embed_ref w y =
    ((z == w) && (x == y))%:R *: (\1 : 'End('Hs logical_reference)).
Proof.
rewrite /transfer_paired_embed_ref adjf_comp -comp_lfunA.
rewrite (comp_lfunA ((transfer_layout ⊗f (\1 : 'End('Hs R)))^A)
  (transfer_layout ⊗f (\1 : 'End('Hs R))) (transfer_embed_ref w y))
  gisofEl comp_lfun1l.
exact: transfer_embed_ref_adjoint.
Qed.

Lemma transfer_paired_embed_ref_complete :
  \sum_(i : bool * bool) (transfer_paired_embed_ref i.1 i.2 \o
    (transfer_paired_embed_ref i.1 i.2)^A) =
      (\1 : 'End('Hs (paired_type * R)%type)).
Proof.
under eq_bigr=>i _ do rewrite /transfer_paired_embed_ref adjf_comp
  -comp_lfunA (comp_lfunA (transfer_embed_ref i.1 i.2)
    ((transfer_embed_ref i.1 i.2)^A) ((transfer_layout ⊗f (\1 : 'End('Hs R)))^A))
  comp_lfunA.
by rewrite -linear_sumlz /= -linear_sumr /= transfer_embed_ref_complete
  comp_lfun1r gisofEr.
Qed.

(* Gates act on the decoded data and reference while the two measured
   sender bits are retained.  Their physical extension is block diagonal
   in those bits and hence composes with every teleportation outcome. *)
Definition transfer_paired_encoded_gate_ref (U : 'End('Hs logical_reference)) :=
  \sum_(i : bool * bool) (transfer_paired_embed_ref i.1 i.2 \o U \o
    (transfer_paired_embed_ref i.1 i.2)^A).

Lemma transfer_paired_encoded_gate_ref_natural U z x :
  transfer_paired_encoded_gate_ref U \o transfer_paired_embed_ref z x =
    transfer_paired_embed_ref z x \o U.
Proof.
rewrite /transfer_paired_encoded_gate_ref linear_sumlz /=.
under eq_bigr do
  rewrite -!comp_lfunA transfer_paired_embed_ref_adjoint -xpair_eqE.
rewrite (bigD1 (z,x)) //= big1.
- move=>[a b] /negPf H.
  by rewrite H scale0r !comp_lfun0r.
- by rewrite eqxx scale1r comp_lfun1r addr0 !comp_lfunA.
Qed.

Lemma transfer_paired_encoded_gate_ref_basis U z x c d r :
  transfer_paired_encoded_gate_ref U ''(((z,x),(d,c)),r) =
    transfer_paired_embed_ref z x (U ''((c,d),r)).
Proof.
rewrite -transfer_paired_embed_ref_basis -comp_lfunE.
by rewrite transfer_paired_encoded_gate_ref_natural comp_lfunE.
Qed.

Lemma transfer_paired_encoded_gate_ref_adj U :
  (transfer_paired_encoded_gate_ref U)^A = transfer_paired_encoded_gate_ref (U^A).
Proof.
rewrite /transfer_paired_encoded_gate_ref adjf_sum.
by apply: eq_bigr=>[[z x]] _; rewrite !adjf_comp !adjfK !comp_lfunA.
Qed.

Lemma transfer_paired_encoded_gate_ref_unitary (U : 'FU('Hs logical_reference)) :
  transfer_paired_encoded_gate_ref U \is unitarylf.
Proof.
apply/unitarylfP; rewrite transfer_paired_encoded_gate_ref_adj
  {2}/transfer_paired_encoded_gate_ref linear_sumr /=.
under eq_bigr=>i _ do rewrite
  (comp_lfunA (transfer_paired_encoded_gate_ref U^A)
    (transfer_paired_embed_ref i.1 i.2 \o U)
    (transfer_paired_embed_ref i.1 i.2)^A)
  (comp_lfunA (transfer_paired_encoded_gate_ref U^A)
    (transfer_paired_embed_ref i.1 i.2) U)
  transfer_paired_encoded_gate_ref_natural
  -(comp_lfunA (transfer_paired_embed_ref i.1 i.2) U^A U)
  isofE comp_lfun1r.
exact: transfer_paired_embed_ref_complete.
Qed.
HB.instance Definition _ (U : 'FU('Hs logical_reference)) := isUnitaryLf.Build _
  (transfer_paired_encoded_gate_ref U) (transfer_paired_encoded_gate_ref_unitary U).

Lemma transfer_paired_encoded_branch_ref U z x :
  transfer_paired_decode_ref :o formso (transfer_paired_encoded_gate_ref U) :o
    formso (transfer_paired_branch_ref z x) :o
    formso transfer_paired_resource_ref = 4%:R^-1 *: formso U.
Proof.
rewrite -(comp_soA (transfer_paired_decode_ref :o
    formso (transfer_paired_encoded_gate_ref U))
    (formso (transfer_paired_branch_ref z x))
    (formso transfer_paired_resource_ref))
  transfer_paired_ref_branch_channel comp_soZr -transfer_paired_embed_refE.
rewrite -(comp_soA transfer_paired_decode_ref
    (formso (transfer_paired_encoded_gate_ref U))
    (formso (transfer_paired_embed_ref z x)))
  formso_comp transfer_paired_encoded_gate_ref_natural -formso_comp
  (comp_soA transfer_paired_decode_ref
    (formso (transfer_paired_embed_ref z x)) (formso U))
  transfer_paired_embed_refE transfer_paired_decode_ref_embed comp_so1l.
by [].
Qed.
End Reference.

(* The measurements commute because they act on distinct sender wires.
   This connects the existing z-then-x branch equation to qft.isq's
   x-then-z order.  Correction composition already applies X before Z. *)
Lemma transfer_measure_order z x :
  (projector z ⊗f (\1 : 'End('Hs bool))) \o
    ((\1 : 'End('Hs bool)) ⊗f projector x) =
  ((\1 : 'End('Hs bool)) ⊗f projector x) \o
    (projector z ⊗f (\1 : 'End('Hs bool))).
Proof. by rewrite !tentf_comp !comp_lfun1l !comp_lfun1r. Qed.

Lemma transfer_branch_source_order z x :
  transfer_branch z x =
  transfer_swap \o
    ((((projector z ⊗f (\1 : 'End('Hs bool))) \o
       ((\1 : 'End('Hs bool)) ⊗f projector x) \o
       (Hadamard ⊗f (\1 : 'End('Hs bool))) \o CNOT) ⊗f
        (pauli_z z \o pauli_x x)) ⊗f (\1 : 'End('Hs bool))).
Proof.
by rewrite /transfer_branch /teleport_branch tentf_comp
  comp_lfun1l comp_lfun1r.
Qed.
End DistributedQFTTeleport.

(** 2. Bell preparation and support *)

(* State transfer used by qft.isq.  The source sends the pair outcome x
   before the data outcome z; the receiver applies X, then Z, then SWAP.
   The equations below concern channels on arbitrary operators, so they
   preserve correlations with the other QFT qubits. *)

Module DistributedQFTBell.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import DistributedProtocolQuantum DistributedProtocolRegister.
Import ClassicalSemantics ClassicalDeterministic ClassicalRegisterTensor CQMemoryTransport ClassicalAlgorithmSemantics.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition bell_unitary : 'FU('Hs (bool * bool)%type) :=
  [unitary of CNOT \o (Hadamard ⊗f (\1 : 'End('Hs bool)))].
Definition bell_state : 'Hs (bool * bool)%type :=
  CNOT ((Hadamard ⊗f (\1 : 'End('Hs bool))) ''(false,false)).
Lemma bell_state_ns : [< bell_state; bell_state >] = 1.
Proof.
by rewrite /bell_state -adj_dotEl isofKE -adj_dotEl isofKE ns_dot.
Qed.
HB.instance Definition _ := isNormalState.Build
  ('Hs (bool * bool)%type) bell_state bell_state_ns.
Definition bell_projector : 'End('Hs (bool * bool)%type) :=
  [> bell_state; bell_state <].

Lemma bell_stateE : (bell_state : 'Hs (bool * bool)%type) =
  (sqrtC 2%:R)^-1 *: (''(false,false) + ''(true,true)).
Proof.
rewrite /bell_state -tentv_t2tv tentf_apply Hadamard_cb id_lfunE
  (onb_vec t2tv ('± false)) big_bool !dotp_cbpm /=
  ?expr0z ?div1r tentvDl !tentvZl linearD /=
  !linearZ /= !CNOT_cb !tentv_t2tv.
by rewrite -scalerDr addrC.
Qed.

Definition native_bell_projector (q : wf_qreg (QPair QBool QBool)) : 'End(Hq) :=
  liftf_lf (tf2f q q bell_projector).
(** Fresh-resource invariant: the Bell projector on its two-qubit register
    has rank one; its lifted projector superoperator fixes the whole memory
    operator. The later factorization theorem recovers an independent Bell pair,
    even with correlated data, destination, and reference. This support condition
    is discharged by preparation below. *)
Definition bell_supported q (rho : 'End(Hq)) :=
  formso (native_bell_projector q) rho = rho.

Lemma bell_projector_fixed : bell_projector bell_state = bell_state.
Proof. by rewrite /bell_projector outpE ns_dot scale1r. Qed.
Lemma bell_projector_initial :
  formso bell_projector :o initialso bell_state = initialso bell_state.
Proof. by rewrite formso_initial bell_projector_fixed. Qed.

End DistributedQFTBell.

Module DistributedQFTBellSupport.
Module CL := ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics ClassicalDeterministic ClassicalAlgorithmSemantics.
Import DistributedProtocolQuantum DistributedProtocolRegister DistributedProtocolProcesses
  DistributedProtocolOwnership.
Import CQQuantumFrame DistributedQFTBell.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition native_bell_initializer (q : wf_qreg (QPair QBool QBool)) :=
  liftfso (initialso (tv2v q bell_state)).

Lemma native_bell_initializer_supported q :
  formso (native_bell_projector q) :o native_bell_initializer q =
    native_bell_initializer q.
Proof.
by rewrite /native_bell_projector /native_bell_initializer -liftfso_formso
  -liftfso_comp formso_initial tf2f_apply bell_projector_fixed.
Qed.

Lemma bell_initializer_support q (rho : 'End(Hq)) :
  bell_supported q (native_bell_initializer q rho).
Proof.
by rewrite /bell_supported -comp_soE native_bell_initializer_supported.
Qed.

Lemma bell_supported_denote c (q : wf_qreg (QPair QBool QBool)) s out (rho : 'End(Hq)) :
  [disjoint quantum_variables c & mset q] ->
  bell_supported q rho -> bell_supported q (denote c s out rho).
Proof.
move=>Hdis Hsupp; rewrite /bell_supported /native_bell_projector -liftfso_formso.
rewrite -comp_soE -(@denote_disjoint_commute c _ _ Hdis s out) comp_soE
  liftfso_formso -/native_bell_projector.
by rewrite Hsupp.
Qed.

(** Explicit ideal resource preparation: reset both halves, H on the first,
    then CNOT. This is the resource-service initializer, before the private
    distributed program; it is not a local rank action implementing create_epr
    across two owners. Full-source freshness and unchanged data reduction are
    established in DistributedQFTResources in qft.v. *)
Definition prepare_bell (q : wf_qreg (QPair QBool QBool)) :=
  CL.Sequence (CL.Initialize q (CL.EConst [NS of ''(false,false)]))
    (CL.Sequence
      (CL.Unitary (first_register q) (CL.EConst [unitary of Hadamard]))
      (CL.Unitary q (CL.EConst [unitary of CNOT]))).

Lemma prepare_bell_action (q : wf_qreg (QPair QBool QBool)) :
  (register_action q CNOT :o register_action (first_register q) Hadamard) :o
    liftfso (initialso (tv2v q ''(false,false))) = native_bell_initializer q.
Proof.
rewrite register_action_left register_action_comp /register_action
  -liftfso_comp formso_initial tf2f_apply comp_lfunE.
by rewrite /native_bell_initializer /bell_state.
Qed.

Lemma prepare_bell_execution (q : wf_qreg (QPair QBool QBool)) s :
  execution (prepare_bell q) s s (native_bell_initializer q).
Proof.
have D := RunSequence (RunInitialize q (CL.EConst [NS of ''(false,false)]) s)
  (RunSequence
    (RunUnitary (first_register q) (CL.EConst [unitary of Hadamard]) s)
    (RunUnitary q (CL.EConst [unitary of CNOT]) s)).
change (execution (prepare_bell q) s s
  ((register_action q CNOT :o register_action (first_register q) Hadamard) :o
    liftfso (initialso (tv2v q ''(false,false))))) in D.
by rewrite prepare_bell_action in D.
Qed.

Lemma prepare_bell_denote (q : wf_qreg (QPair QBool QBool)) s out :
  denote (prepare_bell q) s out = point s (native_bell_initializer q) out.
Proof. exact (execution_denote (prepare_bell_execution q s) out). Qed.

Lemma prepare_bell_quantum (q : wf_qreg (QPair QBool QBool)) :
  quantum_variables (prepare_bell q) \subset mset q.
Proof.
by rewrite /prepare_bell /= !finset.subUset !fintype.subxx
  !first_register_subset.
Qed.
End DistributedQFTBellSupport.

(** 3. Register marginals and auxiliary erasure *)

(* Native reduced-register semantics for QFT gates and teleportation. *)

Module DistributedQFTReduction.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import CQQuantumTrace CQMemoryExtension.
Import ClassicalRegisterTensor DistributedFourierAlgebra DistributedQFTTeleport.
Import DistributedQFTBell.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma complement_difference (S : {set mlab}) :
 finset.setT :\: ~: S = S.
Proof. by rewrite finset.setTD finset.setCK. Qed.

(* This is the unnormalized physical partial trace.  It preserves the
   trace of a density operator; no dimension factor is introduced. *)
Definition memory_marginal (S : {set mlab}) (rho : 'End(Hq)) : 'F[msys]_S :=
 castlf (complement_difference S, complement_difference S)
   (ptraceso (~: S) rho).

Lemma memory_marginal_lift S rho :
 liftf_lf (memory_marginal S rho) = liftf_lf (ptraceso (~: S) rho).
Proof. by rewrite /memory_marginal liftf_lf_cast. Qed.

Lemma memory_marginal_depolarizer S rho :
 liftfso (depolarizer msys (~: S)) rho =
 uniform_weight 'H[msys]_(~: S) *: liftf_lf (memory_marginal S rho).
Proof. by rewrite depolarizer_full memory_marginal_lift. Qed.

Theorem memory_marginal_liftfso S (F : 'SO('H[msys]_S)) rho :
 memory_marginal S (liftfso F rho) = F (memory_marginal S rho).
Proof.
have Hdis : [disjoint S & ~: S] by rewrite disjointXC.
have E := congr1 (fun G : 'SO(Hq) => G rho)
  (liftfso_compC F (depolarizer msys (~: S)) Hdis).
rewrite !comp_soE !memory_marginal_depolarizer !linearZ /= liftfsoEf in E.
apply: liftf_lf_inj.
apply: (@scalerI _ _ (uniform_weight 'H[msys]_(~: S)) (uniform_nonzero _)).
exact: esym E.
Qed.

(* Pull a physical marginal back along the register's canonical memory
   basis.  Correlations with wires outside the register are discarded. *)
Definition register_reduction u (q : wf_qreg u) (rho : 'End(Hq)) : 'End('Ht u) :=
 @f2tf q q (memory_marginal (mset q) rho).

Lemma register_reduction_linear u (q : wf_qreg u) : linear (register_reduction q).
Proof.
move=>a x y; rewrite /register_reduction /memory_marginal.
by rewrite linearP /= linearP /= linearP.
Qed.
HB.instance Definition _ u (q : wf_qreg u) :=
 GRing.isLinear.Build C _ _ _ (register_reduction q) (register_reduction_linear q).

Definition register_reduction_superop u (q : wf_qreg u) :
 'SO(Hq, 'Ht u) := SOType (vector.linfun (register_reduction q)).
Lemma register_reduction_superopE u (q : wf_qreg u) rho :
 register_reduction_superop q rho = register_reduction q rho.
Proof. by rewrite /register_reduction_superop superopE lfunE. Qed.

Lemma f2tf_formso u (q : wf_qreg u) (U : 'End('Ht u)) A :
 @f2tf q q (formso (tf2f q q U) A) = formso U (@f2tf q q A).
Proof.
apply: (@tf2f_inj default_qmemory u u q q).
by rewrite f2tfK !formsoE -!(tf2f_comp _ q q q) tf2f_adj f2tfK.
Qed.

Theorem register_reduction_gate u (q : wf_qreg u) (U : 'End('Ht u)) rho :
 register_reduction q (liftfso (formso (tf2f q q U)) rho) =
 formso U (register_reduction q rho).
Proof.
by rewrite /register_reduction memory_marginal_liftfso f2tf_formso.
Qed.

Lemma tenf_trace (S T : {set mlab}) (A : 'F[msys]_S) (B : 'F[msys]_T) :
 [disjoint S & T] -> \Tr (A \⊗ B) = \Tr A * \Tr B.
Proof.
move=>Hdis.
rewrite (onb_trlf deltav) idxSsum //
  (onb_trlf deltav A) (onb_trlf deltav B) mulr_suml.
apply: eq_bigr=>i _; rewrite mulr_sumr; apply: eq_bigr=>j _.
rewrite /= -tenf_dv dv_split !idxSUl // !idxSUr //.
by rewrite tenv_dot //.
Qed.

Lemma liftf_lf_trace S (A : 'F[msys]_S) :
 \Tr (liftf_lf A) = \Tr A * (dim 'H[msys]_(~: S))%:R.
Proof.
by rewrite liftf_lfE -castlf_trlf tenf_trace ?disjointXC //
  /lftrace h2mx1 mxtrace1.
Qed.

Lemma depolarizer_selfdual S : (depolarizer msys S)^*o = depolarizer msys S.
Proof.
apply/superopP=>rho; apply/eqP/trlf_introl=>A.
rewrite dualso_trlfEV dualsoK !depolarizerE
  !linearZl !linearZr !linearZ /= comp_lfun1l comp_lfun1r.
by rewrite [\Tr A * \Tr rho]mulrC.
Qed.

Lemma depolarizer_identity S : depolarizer msys S \1 = \1.
Proof.
rewrite depolarizerE /uniform_weight /lftrace h2mx1 mxtrace1
  scalerA mulVf ?scale1r //.
by rewrite pnatr_eq0 -lt0n dim_proper.
Qed.

Lemma depolarizer_fixes_frame S (A : 'F[msys]_S) :
 liftfso (depolarizer msys (~: S)) (liftf_lf A) = liftf_lf A.
Proof.
by rewrite -{1}(comp_lfun1r (liftf_lf A))
  -(@liftf_lf1 mlab msys (~: S))
  liftfsoEf_compl ?disjointXC //
  liftfsoEf depolarizer_identity liftf_lf1 comp_lfun1r.
Qed.

(* Observables on the selected register have exactly the same expectation
   before and after taking its physical partial trace. *)
Theorem memory_marginal_trace S (A : 'F[msys]_S) rho :
 \Tr (A \o memory_marginal S rho) = \Tr (liftf_lf A \o rho).
Proof.
have E := dualso_trlfEV (liftfso (depolarizer msys (~: S))) rho (liftf_lf A).
rewrite /= liftfso_dual depolarizer_selfdual depolarizer_fixes_frame in E.
rewrite memory_marginal_depolarizer linearZr /= linearZ
  -liftf_lf_comp /= liftf_lf_trace in E.
have Hdim : ((dim 'H[msys]_(~: S))%:R : C) != 0.
  by rewrite pnatr_eq0 -lt0n dim_proper.
by rewrite /uniform_weight mulrCA mulVf // mulr1 in E.
Qed.

Theorem register_reduction_trace u (q : wf_qreg u) (A : 'End('Ht u)) rho :
 \Tr (A \o register_reduction q rho) =
 \Tr (liftf_lf (tf2f q q A) \o rho).
Proof.
rewrite /register_reduction
  -(tf2f_trlf default_qmemory q
    (A \o @f2tf q q (memory_marginal (mset q) rho))).
rewrite -(tf2f_comp _ q q q) f2tfK.
exact: memory_marginal_trace.
Qed.

Lemma register_pair_product u v (p : wf_qreg (QPair u v))
 (A : 'End('Ht u)) (B : 'End('Ht v)) :
 liftf_lf (tf2f p p (A ⊗f B)) =
 liftf_lf (tf2f (qreg_fst p) (qreg_fst p) A) \o
 liftf_lf (tf2f (qreg_snd p) (qreg_snd p) B).
Proof.
rewrite -(liftf_lf_cast (@mset_pairV _ _ _ p) (tf2f p p (A ⊗f B))).
by rewrite tf2f_pairV -liftf_lf_compT // pair_register_disjoint.
Qed.

Lemma tensor_trace_ext (T U : ihbFinType)
 (rho sigma : 'End('Hs (T * U)%type)) :
 (forall (A : 'End('Hs T)) (B : 'End('Hs U)),
  \Tr ((A ⊗f B) \o rho) = \Tr ((A ⊗f B) \o sigma)) -> rho = sigma.
Proof.
move=>H.
apply/(intro_onb t2tv)=>[[a b]] /=; apply/(intro_onbl t2tv)=>[[c d]] /=.
rewrite -!outp_trlf -!outp_compr
 [\Tr (rho \o _)]lftraceC [\Tr (sigma \o _)]lftraceC
 -!tentv_t2tv -tentv_out.
exact: H.
Qed.

Lemma tuple_trace_ext n (T : ihbFinType)
 (rho sigma : 'End('Hs(n.-tuple T))) :
 (forall f : 'I_n -> 'End('Hs T),
  \Tr (tentf_tuple f \o rho) = \Tr (tentf_tuple f \o sigma)) -> rho = sigma.
Proof.
move=>H.
apply/(intro_onb t2tv)=>a /=; apply/(intro_onbl t2tv)=>b /=.
rewrite -!outp_trlf -!outp_compr
 [\Tr (rho \o _)]lftraceC [\Tr (sigma \o _)]lftraceC
 !t2tv_tuple -tentf_tuple_out.
exact: H.
Qed.

(* The reference stores the other coordinates in their original order.
   Taking out coordinate k is therefore an exact change of tensor layout. *)
Lemma array_pair_operatorF n (a : wf_qreg (QArray n.+1 QBool))
 (p : wf_qreg (QPair QBool (QArray n QBool))) (k : 'I_n.+1)
 (Hk : <{a.[k]}> =r <{p.1}>)
 (Hr : forall i : 'I_n, <{a.[nlift k i]}> =r <{p.2.[i]}>)
 (f : 'I_n.+1 -> 'End('Ht QBool)) :
 (tf2f a a (tentf_tuple f))%:Fnd =
 (tf2f p p (f k ⊗f tentf_tuple (fun i => f (nlift k i))))%:Fnd.
Proof.
rewrite tf2F_tupleV tf2F_pairV tf2F_tupleV (bigD1_ord k) //=.
f_equal.
- exact (tf2F_eqr default_qmemory Hk Hk (f k)).
- apply: eq_bigr=>i _.
  exact (tf2F_eqr default_qmemory (Hr i) (Hr i) (f (nlift k i))).
Qed.

Lemma array_pair_operator_memory n (a : wf_qreg (QArray n.+1 QBool))
 (p : wf_qreg (QPair QBool (QArray n QBool))) (k : 'I_n.+1)
 (Hk : <{a.[k]}> =r <{p.1}>)
 (Hr : forall i : 'I_n, <{a.[nlift k i]}> =r <{p.2.[i]}>)
 (f : 'I_n.+1 -> 'End('Ht QBool)) :
 liftf_lf (tf2f a a (tentf_tuple f)) =
 liftf_lf (tf2f p p (f k ⊗f tentf_tuple (fun i => f (nlift k i)))).
Proof.
have E := array_pair_operatorF Hk Hr f.
have Hset := (eq_Fnd1 E).1; rewrite /= in Hset.
rewrite /liftf_lf /lift_lf.
to_Fnd; rewrite E.
f_equal; apply: Fnd_eq1.
by rewrite Hset.
Qed.

Theorem array_pair_reduction_transfer n
 (before after : wf_qreg (QArray n.+1 QBool))
 (input output : wf_qreg (QPair QBool (QArray n QBool)))
 (k : 'I_n.+1) (weight : C) rho sigma :
 <{before.[k]}> =r <{input.1}> ->
 (forall i : 'I_n, <{before.[nlift k i]}> =r <{input.2.[i]}>) ->
 <{after.[k]}> =r <{output.1}> ->
 (forall i : 'I_n, <{after.[nlift k i]}> =r <{output.2.[i]}>) ->
 register_reduction output sigma = weight *: register_reduction input rho ->
 register_reduction after sigma = weight *: register_reduction before rho.
Proof.
move=>Hik Hir Hok Hor Hr.
apply: tuple_trace_ext=>f.
rewrite linearZr /= linearZ /=.
rewrite (register_reduction_trace after) (register_reduction_trace before).
rewrite (array_pair_operator_memory Hik Hir) (array_pair_operator_memory Hok Hor).
rewrite -(register_reduction_trace input) -(register_reduction_trace output) Hr.
by rewrite linearZr /= linearZ.
Qed.

Lemma sqrt_two_normalization (x : C) :
 (sqrtC 2)^-1 * ((sqrtC 2)^-1 * x) +
 (sqrtC 2)^-1 * ((sqrtC 2)^-1 * x) = x.
Proof.
by rewrite -mulr2n -mulr_natr mulrA mulrAC -invfM -expr2
 sqrtCK mulVf ?pnatr_eq0 // mul1r.
Qed.

Lemma transfer_paired_resource_first_observable (A : 'End('Hs bool)) :
 transfer_paired_resource^A \o
  ((A ⊗f (\1 : 'End('Hs bool))) ⊗f (\1 : 'End('Hs (bool * bool)%type))) \o
  transfer_paired_resource = A ⊗f (\1 : 'End('Hs bool)).
Proof.
apply/(intro_onb t2tv)=>[[c d]] /=; apply/(intro_onbl t2tv)=>[[e f]] /=.
rewrite -comp_lfunA comp_lfunE adj_dotEr.
rewrite (comp_lfunE
 ((A ⊗f (\1 : 'End('Hs bool))) ⊗f (\1 : 'End('Hs (bool * bool)%type)))
 transfer_paired_resource).
rewrite !transfer_paired_resource_basis linearZ /= linearD /= linearD /=
 !tentf_apply !id_lfunE -!tentv_t2tv.
rewrite !(dotpDl, dotpDr, dotpZl, dotpZr) !tentv_dot !onb_dot
 geC0_conj ?invr_ge0 ?sqrtC_ge0 //.
rewrite /= ?mulr0 ?mul0r ?addr0 ?add0r ?mulr1 ?mul1r
 tentf_apply id_lfunE tentv_dot onb_dot.
exact: sqrt_two_normalization.
Qed.

Lemma transfer_paired_resource_isolf : transfer_paired_resource \is isolf.
Proof.
apply/isolfP.
have E := transfer_paired_resource_first_observable (\1 : 'End('Hs bool)).
by rewrite !tentf11 comp_lfun1r in E.
Qed.
HB.instance Definition _ := isIsoLf.Build _ _ transfer_paired_resource
 (transfer_paired_resource_isolf).

Lemma transfer_paired_resource_ref_first_observable (R : ihbFinType)
 (A : 'End('Hs bool)) (B : 'End('Hs R)) :
 (transfer_paired_resource_ref R)^A \o
  (((A ⊗f (\1 : 'End('Hs bool))) ⊗f
    (\1 : 'End('Hs (bool * bool)%type))) ⊗f B) \o
  transfer_paired_resource_ref R =
  (A ⊗f (\1 : 'End('Hs bool))) ⊗f B.
Proof.
by rewrite /transfer_paired_resource_ref tentf_adj !tentf_comp
 transfer_paired_resource_first_observable adjf1 comp_lfun1l comp_lfun1r.
Qed.

Lemma discard_old_destination_ref_dual_tensor (R : ihbFinType)
 (A : 'End('Hs bool)) (B : 'End('Hs R)) :
 (discard_old_destination_ref R)^*o (A ⊗f B) =
 (A ⊗f (\1 : 'End('Hs bool))) ⊗f B.
Proof.
apply/(intro_onb t2tv)=>[[[c d] r]] /=;
 apply/(intro_onbl t2tv)=>[[[e f] s]] /=.
rewrite -outp_trlf -outp_compr -dualso_trlfEV
 discard_old_destination_ref_outp linearZr /= linearZ /= outp_compr outp_trlf.
rewrite -!tentv_t2tv !tentf_apply !id_lfunE !tentv_dot !onb_dot [d == f]eq_sym.
by rewrite -mulrA mulrCA.
Qed.

Lemma transfer_paired_embed_ref_adjoint_basis (R : ihbFinType)
 z x a b c d (r : R) :
 (transfer_paired_embed_ref R z x)^A ''(((a,b),(c,d)),r) =
 ((z == a) && (x == b))%:R *: ''((d,c),r).
Proof.
rewrite /transfer_paired_embed_ref adjf_comp comp_lfunE tentf_adj.
rewrite -[ ''(((a,b),(c,d)),r)]tentv_t2tv tentf_apply
 transfer_layout_adjoint_basis adjf1 id_lfunE.
by rewrite /transfer_unlayout_index /transfer_embed_ref tentf_adj tentf_apply
 transfer_embed_adjoint_basis adjf1 id_lfunE tentvZl tentv_t2tv.
Qed.

Lemma transfer_paired_decode_ref_outp (R : ihbFinType)
 a b c d (r : R) e f g h (s : R) :
 transfer_paired_decode_ref R
  [> ''(((a,b),(c,d)),r); ''(((e,f),(g,h)),s) <] =
 ((a == e) && (b == f))%:R *: [> ''((d,c),r); ''((h,g),s) <].
Proof.
have E i : (transfer_embed_ref R i.1 i.2)^A \o
 (transfer_layout^A ⊗f (\1 : 'End('Hs R))) =
 (transfer_paired_embed_ref R i.1 i.2)^A.
 by rewrite /transfer_paired_embed_ref adjf_comp tentf_adj adjf1.
rewrite /transfer_paired_decode_ref /transfer_decode_ref comp_soE formsoE
 outp_compr outp_compl adjfK kraussoE.
under eq_bigr=>i _ do rewrite outp_compr outp_compl adjfK
 -!comp_lfunE E !transfer_paired_embed_ref_adjoint_basis
 outpZl outpZr scalerA.
rewrite (bigD1 (a,b)) //= big1.
- move=>[z x] /negPf H; rewrite !xpair_eqE in H.
  by rewrite H mul0r scale0r.
- by rewrite !eqxx /= mul1r addr0 geC0_conj ?ler0n.
Qed.

Lemma transfer_paired_data_output_ref_outp (R : ihbFinType)
 a b c d (r : R) e f g h (s : R) :
 transfer_paired_data_output_ref R
  [> ''(((a,b),(c,d)),r); ''(((e,f),(g,h)),s) <] =
 (((a == e) && (b == f)) && (c == g))%:R *:
  [> ''(d,r); ''(h,s) <].
Proof.
rewrite /transfer_paired_data_output_ref comp_soE transfer_paired_decode_ref_outp
 linearZ /= discard_old_destination_ref_outp scalerA -natrM.
by rewrite mulnb.
Qed.

Lemma transfer_paired_data_output_ref_dual_tensor (R : ihbFinType)
 (A : 'End('Hs bool)) (B : 'End('Hs R)) :
 (transfer_paired_data_output_ref R)^*o (A ⊗f B) =
 ((\1 : 'End('Hs (bool * bool)%type)) ⊗f
  ((\1 : 'End('Hs bool)) ⊗f A)) ⊗f B.
Proof.
apply/(intro_onb t2tv)=>[[[[a b] [c d]] r]] /=;
 apply/(intro_onbl t2tv)=>[[[[e f] [g h]] s]] /=.
rewrite -outp_trlf -outp_compr -dualso_trlfEV
 transfer_paired_data_output_ref_outp linearZr /= linearZ /=
 outp_compr outp_trlf.
rewrite -!tentv_t2tv !tentf_apply !id_lfunE !tentv_dot !onb_dot.
rewrite [a == e]eq_sym [b == f]eq_sym [c == g]eq_sym.
by rewrite !mulrA -!natrM !mulnb.
Qed.

Section NativeTransfer.
Variable U : qType.
Variable q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) U).

Definition transfer_output_register := [wf_qreg of <{ (q.1.2.2, q.2) }>].
Definition transfer_input_register := [wf_qreg of <{ (q.1.1.1, q.2) }>].

Lemma paired_output_observable (A : 'End('Ht QBool)) (B : 'End('Ht U)) :
 liftf_lf (tf2f q q
  (((\1 : 'End('Ht (QPair QBool QBool))) ⊗f
   ((\1 : 'End('Ht QBool)) ⊗f A)) ⊗f B)) =
 liftf_lf (tf2f transfer_output_register transfer_output_register (A ⊗f B)).
Proof.
rewrite (register_pair_product q)
 (register_pair_product transfer_output_register).
rewrite (lift_register_right [wf_qreg of <{q.1}>])
 (lift_register_right [wf_qreg of <{q.1.2}>]).
rewrite /transfer_output_register /=.
have Ef : (qreg_fst <{(q.1.2.2,q.2)}>) =r <{q.1.2.2}> := eq_qreg_fst _ _.
have Es : (qreg_snd <{(q.1.2.2,q.2)}>) =r <{q.2}> := eq_qreg_snd _ _.
by rewrite -(tf2f_eqr default_qmemory Ef Ef)
 -(tf2f_eqr default_qmemory Es Es) !liftf_lf_cast.
Qed.

Lemma paired_input_observable (A : 'End('Ht QBool)) (B : 'End('Ht U)) :
 liftf_lf (tf2f q q
  (((A ⊗f (\1 : 'End('Ht QBool))) ⊗f
    (\1 : 'End('Ht (QPair QBool QBool)))) ⊗f B)) =
 liftf_lf (tf2f transfer_input_register transfer_input_register (A ⊗f B)).
Proof.
rewrite (register_pair_product q) (register_pair_product transfer_input_register).
rewrite (lift_register_left [wf_qreg of <{q.1}>])
 (lift_register_left [wf_qreg of <{q.1.1}>]).
rewrite /transfer_input_register /=.
have Ef : (qreg_fst <{(q.1.1.1,q.2)}>) =r <{q.1.1.1}> := eq_qreg_fst _ _.
have Es : (qreg_snd <{(q.1.1.1,q.2)}>) =r <{q.2}> := eq_qreg_snd _ _.
by rewrite -(tf2f_eqr default_qmemory Ef Ef)
 -(tf2f_eqr default_qmemory Es Es) !liftf_lf_cast.
Qed.

(* The decoder used in the typed teleportation proof is exactly the
   physical partial trace keeping the destination and the reference. *)
Theorem native_transfer_output_reduction rho :
 register_reduction transfer_output_register rho =
 transfer_paired_data_output_ref (evalQT U) (register_reduction q rho).
Proof.
apply: tensor_trace_ext=>A B.
rewrite (dualso_trlfEV (transfer_paired_data_output_ref (evalQT U)))
 transfer_paired_data_output_ref_dual_tensor.
rewrite (register_reduction_trace transfer_output_register)
 (register_reduction_trace q).
by rewrite paired_output_observable.
Qed.

Theorem native_transfer_input_resource rho sigma :
 register_reduction q rho = formso (transfer_paired_resource_ref (evalQT U)) sigma ->
 register_reduction transfer_input_register rho =
 discard_old_destination_ref (evalQT U) sigma.
Proof.
move=>Hr; apply: tensor_trace_ext=>A B.
rewrite (dualso_trlfEV (discard_old_destination_ref (evalQT U)))
 discard_old_destination_ref_dual_tensor.
rewrite (register_reduction_trace transfer_input_register).
rewrite -paired_input_observable -(register_reduction_trace q) Hr.
rewrite (dualso_trlfEV (formso (transfer_paired_resource_ref (evalQT U)))) dualsoE.
by rewrite transfer_paired_resource_ref_first_observable.
Qed.

Definition native_transfer_branch z x :=
 liftfso (formso (tf2f <{q.1}> <{q.1}> (transfer_paired_branch z x))).

Lemma native_transfer_branch_reduction z x rho :
 register_reduction q (native_transfer_branch z x rho) =
 formso (transfer_paired_branch_ref (evalQT U) z x) (register_reduction q rho).
Proof.
rewrite /native_transfer_branch (channel_register_left q (transfer_paired_branch z x)).
by rewrite register_reduction_gate /transfer_paired_branch_ref.
Qed.

End NativeTransfer.

Lemma transfer_paired_reduced_branch_ref (R : ihbFinType) z x sigma :
 transfer_paired_data_output_ref R
  (formso (transfer_paired_branch_ref R z x)
   (formso (transfer_paired_resource_ref R) sigma)) =
 4%:R^-1 *: discard_old_destination_ref R sigma.
Proof.
have E := congr1 (fun F : 'SO('Hs ((bool * bool) * R)%type) => F sigma)
 (transfer_paired_decoded_branch_ref R z x).
rewrite !comp_soE scale_soE id_soE in E.
by rewrite /transfer_paired_data_output_ref !comp_soE E linearZ.
Qed.

Theorem native_transfer_branch_relocation (U : qType)
 (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) U))
 z x rho sigma :
 register_reduction q rho = formso (transfer_paired_resource_ref (evalQT U)) sigma ->
 register_reduction (transfer_output_register q) (native_transfer_branch q z x rho) =
 4%:R^-1 *: register_reduction (transfer_input_register q) rho.
Proof.
move=>Hr.
rewrite native_transfer_output_reduction native_transfer_branch_reduction Hr
 transfer_paired_reduced_branch_ref.
by rewrite (native_transfer_input_resource Hr).
Qed.

Theorem native_array_branch_relocation n
 (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool))
   (QArray n QBool)))
 (before after : wf_qreg (QArray n.+1 QBool)) (k : 'I_n.+1) z x rho sigma :
 <{before.[k]}> =r qreg_fst (transfer_input_register q) ->
 (forall i : 'I_n, <{before.[nlift k i]}> =r
   qreg_tuplei i (qreg_snd (transfer_input_register q))) ->
 <{after.[k]}> =r qreg_fst (transfer_output_register q) ->
 (forall i : 'I_n, <{after.[nlift k i]}> =r
   qreg_tuplei i (qreg_snd (transfer_output_register q))) ->
 register_reduction q rho =
   formso (transfer_paired_resource_ref (evalQT (QArray n QBool))) sigma ->
 register_reduction after (native_transfer_branch q z x rho) =
 4%:R^-1 *: register_reduction before rho.
Proof.
move=>Hik Hir Hok Hor Hr.
exact: array_pair_reduction_transfer Hik Hir Hok Hor
 (native_transfer_branch_relocation z x Hr).
Qed.

(* A freshly prepared pure resource is characterized by support on its
   preparation isometry.  This gives its exact factorization with an
   arbitrary operator on all remaining wires. *)
Theorem supported_image_factorization (U V : chsType)
 (E : 'Hom(U,V)) (rho : 'End(V)) :
 formso (E \o E^A) rho = rho ->
 formso E (formso (E^A) rho) = rho.
Proof. by move=>H; rewrite -comp_soE formso_comp. Qed.

Lemma isometric_resource_recovery (U V : chsType)
 (E : 'FI(U,V)) (rho : 'End(U)) :
 formso (E^A) (formso E rho) = rho.
Proof.
by rewrite -comp_soE formso_comp isofE formso1 id_soE.
Qed.

Lemma transfer_paired_resource_adjoint_basis a b c d :
 transfer_paired_resource^A ''((a,b),(c,d)) =
 (sqrtC 2)^-1 * (b == c)%:R *: ''(a,d).
Proof.
apply/(intro_onbl t2tv)=>[[e f]] /=.
rewrite adj_dotEr transfer_paired_resource_basis
 dotpZl dotpDl !tentv_t2tv !onb_dot dotpZr onb_dot
 geC0_conj ?invr_ge0 ?sqrtC_ge0 //.
rewrite !xpair_eqE /=.
case: b; case: c=>/=;
 rewrite ?andbT ?andbF ?mulr0 ?mul0r ?addr0 ?add0r ?mulr1 ?mul1r.
all: by rewrite /= ?mulr0.
Qed.

Lemma bell_projectorE :
 bell_projector = 2%:R^-1 *:
  (\sum_(b : bool) \sum_(c : bool) ([>''b;''c<] ⊗f [>''b;''c<])).
Proof.
rewrite /bell_projector bell_stateE outpZl outpZr scalerA
 geC0_conj ?invr_ge0 ?sqrtC_ge0 //.
rewrite -invfM -expr2 sqrtCK outpDl !outpDr !big_bool
 !tentv_out !tentv_t2tv.
congr (_ *: _).
rewrite [RHS]addrC.
congr (_ + _); exact: addrC.
Qed.

Lemma transfer_paired_resource_projector :
 transfer_paired_resource \o transfer_paired_resource^A =
 2%:R^-1 *:
  (\sum_(b : bool) \sum_(c : bool)
   (((\1 : 'End('Hs bool)) ⊗f [>''b;''c<]) ⊗f
    ([>''b;''c<] ⊗f (\1 : 'End('Hs bool))))).
Proof.
apply/(intro_onb t2tv)=>[[[a b] [c d]]] /=.
rewrite comp_lfunE transfer_paired_resource_adjoint_basis linearZ /=
 transfer_paired_resource_basis scalerA mulrAC -invfM -expr2 sqrtCK.
rewrite scale_lfunE sum_lfunE.
under eq_bigr do rewrite sum_lfunE.
under eq_bigr=>e _ do under eq_bigr=>f _ do
 rewrite -[ ''((a,b),(c,d))]tentv_t2tv tentf_apply
 -[ ''(a,b)]tentv_t2tv -[ ''(c,d)]tentv_t2tv
 !tentf_apply !id_lfunE !outpE !onb_dot !tentvZr !tentvZl ?scalerA.
rewrite !big_bool /=.
case: b; case: c=>/=;
 rewrite ?mulr0 ?mul0r ?mulr1 ?mul1r ?scale0r ?scale1r ?addr0 ?add0r.
- by rewrite addrC.
- by rewrite !tentv0 addr0 scaler0.
- by rewrite !tentv0 addr0 scaler0.
- by rewrite addrC.
Qed.

Section NativeBell.
Variable U : qType.
Variable q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) U).

Definition transfer_bell_register := [wf_qreg of <{(q.1.1.2,q.1.2.1)}>].

Lemma paired_middle_observable (B C : 'End('Ht QBool)) :
 liftf_lf (tf2f q q
  ((((\1 : 'End('Ht QBool)) ⊗f B) ⊗f (C ⊗f (\1 : 'End('Ht QBool)))) ⊗f
   (\1 : 'End('Ht U)))) =
 liftf_lf (tf2f transfer_bell_register transfer_bell_register (B ⊗f C)).
Proof.
rewrite (lift_register_left q)
 (register_pair_product [wf_qreg of <{q.1}>])
 (register_pair_product transfer_bell_register).
rewrite (lift_register_right [wf_qreg of <{q.1.1}>])
 (lift_register_left [wf_qreg of <{q.1.2}>]).
rewrite /transfer_bell_register /=.
have Ef : (qreg_fst <{(q.1.1.2,q.1.2.1)}>) =r <{q.1.1.2}> := eq_qreg_fst _ _.
have Es : (qreg_snd <{(q.1.1.2,q.1.2.1)}>) =r <{q.1.2.1}> := eq_qreg_snd _ _.
by rewrite -(tf2f_eqr default_qmemory Ef Ef)
 -(tf2f_eqr default_qmemory Es Es) !liftf_lf_cast.
Qed.

Theorem transfer_resource_projector_memory :
 liftf_lf (tf2f q q
   ((transfer_paired_resource_ref (evalQT U)) \o
    (transfer_paired_resource_ref (evalQT U))^A)) =
 native_bell_projector transfer_bell_register.
Proof.
rewrite /transfer_paired_resource_ref tentf_adj tentf_comp adjf1 comp_lfun1r
 transfer_paired_resource_projector tentfZl.
rewrite /native_bell_projector bell_projectorE !linearZ /=.
rewrite linear_sumlz /= !linear_sum /=.
apply: eq_bigr=>b _.
rewrite linear_sumlz /= !linear_sum /=.
apply: eq_bigr=>c _.
by rewrite paired_middle_observable.
Qed.

End NativeBell.

(* Pure Bell support forces factorization even when the old destination
   and every remaining carrier wire are entangled with the input data. *)
Theorem native_bell_resource_factorization (U : qType)
 (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) U)) rho :
 bell_supported (transfer_bell_register q) rho ->
 register_reduction q rho = formso (transfer_paired_resource_ref (evalQT U))
  (formso ((transfer_paired_resource_ref (evalQT U))^A) (register_reduction q rho)).
Proof.
move=>Hbell.
have Hp : formso
 ((transfer_paired_resource_ref (evalQT U)) \o (transfer_paired_resource_ref (evalQT U))^A)
 (register_reduction q rho) = register_reduction q rho.
 rewrite -(register_reduction_gate q
 ((transfer_paired_resource_ref (evalQT U)) \o (transfer_paired_resource_ref (evalQT U))^A))
 liftfso_formso transfer_resource_projector_memory.
 by rewrite Hbell.
exact: esym (supported_image_factorization Hp).
Qed.

Theorem native_bell_transfer_branch_relocation (U : qType)
 (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) U)) z x rho :
 bell_supported (transfer_bell_register q) rho ->
 register_reduction (transfer_output_register q) (native_transfer_branch q z x rho) =
 4%:R^-1 *: register_reduction (transfer_input_register q) rho.
Proof.
move=>Hbell.
exact (native_transfer_branch_relocation z x (native_bell_resource_factorization Hbell)).
Qed.

(** Native per-hop data law: all untouched array coordinates are retained,
    and the selected coordinate moves from sender data to receiver destination.
    Only Bell support is assumed; no reset or independence of the old
    destination is required. Each outcome has quantum branch weight 1/4. *)
Theorem native_bell_array_branch_relocation n
 (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool))
   (QArray n QBool)))
 (before after : wf_qreg (QArray n.+1 QBool)) (k : 'I_n.+1) z x rho :
 <{before.[k]}> =r qreg_fst (transfer_input_register q) ->
 (forall i : 'I_n, <{before.[nlift k i]}> =r
   qreg_tuplei i (qreg_snd (transfer_input_register q))) ->
 <{after.[k]}> =r qreg_fst (transfer_output_register q) ->
 (forall i : 'I_n, <{after.[nlift k i]}> =r
   qreg_tuplei i (qreg_snd (transfer_output_register q))) ->
 bell_supported (transfer_bell_register q) rho ->
 register_reduction after (native_transfer_branch q z x rho) =
 4%:R^-1 *: register_reduction before rho.
Proof.
move=>Hik Hir Hok Hor Hbell.
exact (native_array_branch_relocation z x Hik Hir Hok Hor
 (native_bell_resource_factorization Hbell)).
Qed.

End DistributedQFTReduction.

(** 4. Native teleportation processes *)

(* State transfer used by qft.isq.  The source sends the pair outcome x
   before the data outcome z; the receiver applies X, then Z, then SWAP.
   The equations below concern channels on arbitrary operators, so they
   preserve correlations with the other QFT qubits. *)

Module DistributedQFTTeleportProcesses.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics DistributedLanguage DistributedCommunication.
Import DistributedProtocolProcesses DistributedProtocolOwnership.
Import DistributedProtocolExecution.
Import DistributedProtocolRegister DistributedProtocolQuantum.
Import DistributedProtocolSuffix DistributedProtocolSerial DistributedProtocolPre.
Import DistributedSequentialization ClassicalDeterministic ClassicalAlgorithmSemantics.
Import CQHoare CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.

(** Premeasured helper protocol: transfer_sender measures both x and z in
    initialization, then sends x followed by z. Its channel and row proofs
    provide reusable branch algebra. For qft.isq's literal send-x-before-M(q)
    order, use transfer_isq_sender in DistributedQFTISQTransfer below.
    The input pair is (data, sender Bell half); the fresh shared pair is
    supplied by transfer_resource, not created by this private process. *)
Definition transfer_sender (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (gate (first_register q) [unitary of Hadamard])
    (Sequence (measure (second_register q) xA)
    (Sequence (measure (first_register q) zA) (set_stage stageA 0)))))
    stageA
    (fun i => Output "88" (CL.EVar (if i == ord0 then xA else zA)))
    (fun i => set_stage stageA i.+1).

(** Literal receiver endpoint, shared by both sender variants. Its register
    is (receiver Bell half, destination). First receive x and apply X to the
    half; then receive z, apply Z, and SWAP into the destination. Both sends
    and receives use tag 88; the stages enforce their ordered matching. *)
Definition transfer_receiver (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round (set_stage stageB 0) stageB
    (fun i => Input "88" (if i == ord0 then xB else zB))
    (fun i => Sequence (set_stage stageB i.+1)
      (if i == ord0 then correct (first_register q) xB [unitary of PauliX]
       else Sequence (correct (first_register q) zB [unitary of PauliZ])
         (gate q [unitary of (@swaptf bool bool)]))).

Lemma transfer_sender_wf q : process_wf (transfer_sender q).
Proof. by apply: two_round_wf=>//=; repeat split. Qed.

Lemma transfer_receiver_wf q : process_wf (transfer_receiver q).
Proof.
apply: two_round_wf=>//= i; split=>//.
case: (i == ord0); first exact: correct_wf.
by split; first exact: correct_wf.
Qed.

Lemma transfer_sender_finite q : finite_set (process_reads (transfer_sender q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 |
      exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; exact: set_stage_finite.
Qed.

Lemma transfer_receiver_finite q : finite_set (process_reads (transfer_receiver q)).
Proof.
apply: two_round_finite; first exact: set_stage_finite.
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: correct_finite].
Qed.

Lemma transfer_sender_owned q : process_owned "Alice" (transfer_sender q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned;
    first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- by move=>i; apply: set_stage_owned.
Qed.

Lemma transfer_receiver_owned q : process_owned "Bob" (transfer_receiver q).
Proof.
apply: two_round_owned=>//.
- by apply: set_stage_owned.
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; apply: sequence_owned; first by apply: set_stage_owned.
  case: (i == ord0); first by apply: correct_owned.
  apply: sequence_owned; first by apply: correct_owned.
  exact: gate_owned.
Qed.

Lemma transfer_sender_quantum q : process_quantum (transfer_sender q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset !fintype.subxx !finset.sub0set
  /= !first_register_subset !second_register_subset /=.
apply/bigcupsP=>i _; exact: finset.sub0set.
Qed.

Lemma transfer_receiver_quantum q : process_quantum (transfer_receiver q) \subset mset q.
Proof.
rewrite /process_quantum /= finset.set0U; apply/bigcupsP=>i _.
rewrite /= finset.set0U; case: (i == ord0)=>/=.
- exact: fintype.subset_trans (@correct_quantum (first_register q) xB
    [unitary of PauliX]) (@first_register_subset _ _ q).
- rewrite finset.subUset; apply/andP; split; last exact: fintype.subxx.
  exact: fintype.subset_trans (@correct_quantum (first_register q) zB
    [unitary of PauliZ]) (@first_register_subset _ _ q).
Qed.

Definition transfer_program (qa qb : wf_qreg (QPair QBool QBool))
    (Hdis : [disjoint mset qa & mset qb]) : program.
Proof.
apply: (@Program 2 (pair_processes (transfer_sender qa) (transfer_receiver qb)) erefl).
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: transfer_sender_wf | exact: transfer_receiver_wf].
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: transfer_sender_finite | exact: transfer_receiver_finite].
- exact: (@pair_private (transfer_sender qa) (transfer_receiver qb) (mset qa) (mset qb)
    (@transfer_sender_owned qa) (@transfer_receiver_owned qb)
    (@transfer_sender_quantum qa) (@transfer_receiver_quantum qb) Hdis).
- exact: pair_point_to_point.
Defined.

Lemma transfer_same_tag_order s k (i j : 'I_2) :
  synchronized_at s k ->
  eval (stage_guard stageA i) s = true ->
  eval (stage_guard stageB j) s = true -> i = j.
Proof.
move=>[Ha Hb]; rewrite /stage_guard /= Ha Hb.
move=>/eqP Ei /eqP Ej.
have E : Posz i = Posz j := eq_trans (esym Ei) Ej.
by apply: val_inj; case: E.
Qed.

Definition transfer_rendezvous (qb : wf_qreg (QPair QBool QBool)) (i j : 'I_2) :
    expression bool * CL.command :=
  (guard_and (stage_guard stageA i) (stage_guard stageB j),
   CL.Sequence (CL.Assign (if j == ord0 then xB else zB)
     (CL.EVar (if i == ord0 then xA else zA)))
   (CL.Sequence (translate_statement (set_stage stageA i.+1))
     (translate_statement (Sequence (set_stage stageB j.+1)
       (if j == ord0 then correct (first_register qb) xB [unitary of PauliX]
        else Sequence (correct (first_register qb) zB [unitary of PauliZ])
          (gate qb [unitary of (@swaptf bool bool)])))))).

Lemma transfer_rendezvousE qa qb :
  rendezvous_commands (paired (transfer_sender qa) (transfer_receiver qb)) =
  [:: transfer_rendezvous qb ord0 ord0;
      transfer_rendezvous qb ord0 round_one;
      transfer_rendezvous qb round_one ord0;
      transfer_rendezvous qb round_one round_one].
Proof.
Arguments communication_effect _ _ : simpl never.
rewrite /rendezvous_commands !enum_two /= /paired /=
  /rendezvous_command /= !enum_two /=.
rewrite (matching_effect (MatchOutput "88" xB (CL.EVar xA)))
  (matching_effect (MatchOutput "88" zB (CL.EVar xA)))
  (matching_effect (MatchOutput "88" xB (CL.EVar zA)))
  (matching_effect (MatchOutput "88" zB (CL.EVar zA))).
by rewrite /transfer_rendezvous /=.
Qed.

Definition transfer_step_action (qb : wf_qreg (QPair QBool QBool))
    (i : 'I_2) (s : CL.store) :=
  if i == ord0 then correction_action (first_register qb) [unitary of PauliX] (s.[xA])%M
  else register_action qb (@swaptf bool bool) :o
    correction_action (first_register qb) [unitary of PauliZ] (s.[zA])%M.

Lemma transfer_step_execution qb i s :
  execution (transfer_rendezvous qb i i).2 s (teleport_step_store i s)
    (transfer_step_action qb i s).
Proof.
rewrite /transfer_rendezvous /transfer_step_action /teleport_step_store /=.
case Ei: (i == ord0).
- have D := RunSequence (RunAssign xB (CL.EVar xA) s)
    (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
    (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
      (correct_execution (first_register qb) xB [unitary of PauliX] _))).
  rewrite !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
- have D := RunSequence (RunAssign zB (CL.EVar zA) s)
    (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
    (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
      (RunSequence (correct_execution (first_register qb) zB [unitary of PauliZ] _)
        (RunUnitary qb (CL.EConst [unitary of (@swaptf bool bool)]) _)))).
  rewrite !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
Qed.

Definition transfer_loop_action qb s :=
  transfer_step_action qb round_one (teleport_step_store ord0 s) :o
    transfer_step_action qb ord0 s.

Lemma transfer_rendezvous_guardE qb i j s k : synchronized_at s k ->
  eval (transfer_rendezvous qb i j).1 s = ((k == val i) && (k == val j)).
Proof.
move=>[Ha Hb]; rewrite /transfer_rendezvous /guard_and /stage_guard /= ?Ha ?Hb.
by rewrite !eqz_nat.
Qed.

Lemma transfer_round_guardE qb s k : synchronized_at s k ->
  eval (guards_any [seq r.1 | r <-
    [:: transfer_rendezvous qb ord0 ord0;
        transfer_rendezvous qb ord0 round_one;
        transfer_rendezvous qb round_one ord0;
        transfer_rendezvous qb round_one round_one]]) s =
    ((k == 0%N) || (k == 1%N)).
Proof.
move=>Hs; have E i j := transfer_rendezvous_guardE qb i j Hs.
change ([|| eval (transfer_rendezvous qb ord0 ord0).1 s,
  eval (transfer_rendezvous qb ord0 round_one).1 s,
  eval (transfer_rendezvous qb round_one ord0).1 s,
  eval (transfer_rendezvous qb round_one round_one).1 s | false] =
  ((k == 0%N) || (k == 1%N))).
rewrite (E ord0 ord0) (E ord0 round_one) (E round_one ord0)
  (E round_one round_one) /=.
by case: (k == 0%N); case: (k == 1%N).
Qed.

Definition transfer_round_loop qb :=
  let rounds := [:: transfer_rendezvous qb ord0 ord0;
      transfer_rendezvous qb ord0 round_one;
      transfer_rendezvous qb round_one ord0;
      transfer_rendezvous qb round_one round_one] in
  CL.While (guards_any [seq r.1 | r <- rounds]) (conditional_chain rounds).

Lemma transfer_round_loop_execution qb s : synchronized_at s 0 ->
  execution (transfer_round_loop qb) s (teleport_final_store s)
    (transfer_loop_action qb s).
Proof.
move=>Hs.
have Ht := teleport_step_synchronized ord0 s.
have Hu := teleport_step_synchronized round_one (teleport_step_store ord0 s).
have Es i j := transfer_rendezvous_guardE qb i j Hs.
have Et i j := transfer_rendezvous_guardE qb i j Ht.
have Eu i j := transfer_rendezvous_guardE qb i j Hu.
have Dbody0 : execution
    (conditional_chain [:: transfer_rendezvous qb ord0 ord0;
      transfer_rendezvous qb ord0 round_one;
      transfer_rendezvous qb round_one ord0;
      transfer_rendezvous qb round_one round_one])
    s (teleport_step_store ord0 s) (transfer_step_action qb ord0 s).
  apply: RunIfTrue; first by rewrite Es.
  exact: transfer_step_execution.
have Dbody1 : execution
    (conditional_chain [:: transfer_rendezvous qb ord0 ord0;
      transfer_rendezvous qb ord0 round_one;
      transfer_rendezvous qb round_one ord0;
      transfer_rendezvous qb round_one round_one])
    (teleport_step_store ord0 s) (teleport_final_store s)
    (transfer_step_action qb round_one (teleport_step_store ord0 s)).
  apply: RunIfFalse; first by rewrite Et.
  apply: RunIfFalse; first by rewrite Et.
  apply: RunIfFalse; first by rewrite Et.
  apply: RunIfTrue; first by rewrite Et.
  exact: transfer_step_execution.
have Dstop : execution (transfer_round_loop qb) (teleport_final_store s)
    (teleport_final_store s) \:1.
  apply: RunWhileFalse.
  by rewrite /teleport_final_store (transfer_round_guardE qb Hu).
have Dnext : execution (transfer_round_loop qb) (teleport_step_store ord0 s)
    (teleport_final_store s)
    (transfer_step_action qb round_one (teleport_step_store ord0 s)).
  rewrite -(comp_so1l (transfer_step_action qb round_one (teleport_step_store ord0 s))).
  apply: RunWhileTrue Dbody1 Dstop.
  by rewrite (transfer_round_guardE qb Ht).
apply: RunWhileTrue Dbody0 Dnext.
by rewrite (transfer_round_guardE qb Hs).
Qed.

Lemma transfer_loop_actionE qb s :
  transfer_loop_action qb s =
    register_action qb (@swaptf bool bool \o
      ((pauli_z (s.[zA])%M \o pauli_x (s.[xA])%M) ⊗f
        (\1 : 'End('Hs bool)))).
Proof.
change ((register_action qb (@swaptf bool bool) :o
  correction_action (first_register qb) [unitary of PauliZ]
    ((teleport_step_store ord0 s).[zA])%M) :o
  correction_action (first_register qb) [unitary of PauliX] (s.[xA])%M =
  register_action qb (@swaptf bool bool \o
    ((pauli_z (s.[zA])%M \o pauli_x (s.[xA])%M) ⊗f
      (\1 : 'End('Hs bool))))).
rewrite /teleport_step_store !get_set_nex //.
rewrite correction_actionX correction_actionZ !register_action_left
  !register_action_comp -comp_lfunA tentf_comp comp_lfun1l.
by [].
Qed.

Lemma transfer_terminationE qa qb s : synchronized_at s 2 ->
  eval (termination_guard (paired (transfer_sender qa) (transfer_receiver qb))) s = true.
Proof.
move=>[Ha Hb].
rewrite /termination_guard !enum_two /= /paired /= !enum_two /=.
by rewrite /guards_all /guard_and /guard_not /stage_guard /= Ha Hb.
Qed.

Definition transfer_loop_suffix qa qb :=
  CL.Sequence (transfer_round_loop qb)
    (CL.Conditional (termination_guard (paired (transfer_sender qa) (transfer_receiver qb)))
      CL.Skip CL.Abort).

Lemma transfer_loop_suffix_execution qa qb s : synchronized_at s 0 ->
  execution (transfer_loop_suffix qa qb) s (teleport_final_store s)
    (transfer_loop_action qb s).
Proof.
move=>Hs; rewrite -(comp_so1l (transfer_loop_action qb s)).
apply: RunSequence (transfer_round_loop_execution qb Hs) _.
apply: RunIfTrue; last exact: RunSkip.
apply: transfer_terminationE; exact: teleport_step_synchronized.
Qed.

Definition transfer_tail qa qb :=
  CL.Sequence (CL.Assign stageA (CL.EConst (0 : int)))
    (CL.Sequence (CL.Sequence (CL.Assign stageB (CL.EConst (0 : int))) CL.Skip)
      (transfer_loop_suffix qa qb)).

Lemma transfer_tail_execution qa qb s :
  execution (transfer_tail qa qb) s (teleport_final_store (stages_zero s))
    (transfer_loop_action qb (stages_zero s)).
Proof.
have D := RunSequence (RunAssign stageA (CL.EConst (0 : int)) s)
  (RunSequence (RunSequence (RunAssign stageB (CL.EConst (0 : int)) _) (RunSkip _))
    (transfer_loop_suffix_execution qa qb (stages_zero_synchronized s))).
rewrite !comp_so1l !comp_so1r in D; exact: D.
Qed.

Definition transfer_serial (qa qb : wf_qreg (QPair QBool QBool)) :=
  CL.Sequence (CL.Unitary qa (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Unitary (first_register qa) (CL.EConst [unitary of Hadamard]))
  (CL.Sequence (CL.Measure xA (second_register qa) (CL.EConst [QM of @tmeas bool]))
  (CL.Sequence (CL.Measure zA (first_register qa) (CL.EConst [QM of @tmeas bool]))
    (transfer_tail qa qb)))).

Lemma transfer_serial_preE total qa qb Q :
  pre total (successful_sequentialize (paired (transfer_sender qa) (transfer_receiver qb))) Q =
    pre total (transfer_serial qa qb) Q.
Proof.
rewrite /successful_sequentialize /sequentialize transfer_rendezvousE enum_two /=.
rewrite /paired /= /transfer_serial /transfer_tail /transfer_loop_suffix /transfer_round_loop.
rewrite !pre_sequence.
by [].
Qed.

(** Common native quantum branch, independent of auxiliary counter names.
    It records CNOT/H/M(pair)=x/M(data)=z and receiver X/Z/SWAP in execution
    order. transfer_physical_branchE identifies it with the typed quartet
    branch above. The variable-parametric source kernel call_serial_denote
    in DistributedQFTTransferKernel (qft.v) uses this same branch family. *)
Definition transfer_physical_branch (qa qb : wf_qreg (QPair QBool QBool)) z x :=
  register_action qb (@swaptf bool bool \o
    ((pauli_z z \o pauli_x x) ⊗f (\1 : 'End('Hs bool)))) :o
  (register_action (first_register qa) (projector z) :o
   (register_action (second_register qa) (projector x) :o
    (register_action (first_register qa) Hadamard :o register_action qa CNOT))).

Lemma transfer_physical_branchE
    (q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool))) z x :
  transfer_physical_branch (first_register q) (second_register q) z x =
    register_action q (DistributedQFTTeleport.transfer_paired_branch z x).
Proof.
rewrite /transfer_physical_branch !(register_action_left, register_action_right)
  !register_action_comp !tentf_comp !comp_lfun1l !comp_lfun1r
  /DistributedQFTTeleport.transfer_paired_branch.
by rewrite !comp_lfunA !tentf_comp !comp_lfun1l !comp_lfun1r.
Qed.

Lemma transfer_tail_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (transfer_tail qa qb) (fun _ => Q) s : 'End(Hq)) =
  (register_action qb (@swaptf bool bool \o
    ((pauli_z (s.[zA])%M \o pauli_x (s.[xA])%M) ⊗f
      (\1 : 'End('Hs bool)))))^*o Q.
Proof.
by rewrite /pre (execution_preE total _ (transfer_tail_execution qa qb s))
  transfer_loop_actionE /stages_zero !get_set_nex //.
Qed.

Theorem transfer_source_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (successful_sequentialize (paired (transfer_sender qa) (transfer_receiver qb)))
    (fun _ => Q) s : 'End(Hq)) =
    \sum_x \sum_z (transfer_physical_branch qa qb z x)^*o Q.
Proof.
rewrite transfer_serial_preE /transfer_serial pre_sequence pre_sequence
  pre_sequence pre_sequence.
rewrite unitary_pre_register unitary_pre_register computational_measurement_pre.
under eq_bigr=>x _ do rewrite computational_measurement_pre.
under eq_bigr=>x _ do under eq_bigr=>z _ do
  rewrite transfer_tail_pre get_set_eq get_set_nex // get_set_eq.
rewrite !linear_sum /=.
apply: eq_bigr=>x _; rewrite !linear_sum /=.
apply: eq_bigr=>z _.
by rewrite /transfer_physical_branch !dualso_comp !comp_soE.
Qed.

(* Exact kernels, including the classical outcomes.  These equations are
   stronger than precondition equations for constant postconditions. *)
Lemma sum_finite_points (I : finType) (f : I -> CL.store) (F : I -> 'SO(Hq)) :
  sum (fun out => \sum_i point (f i) (F i) out) = \sum_i F i.
Proof.
pose rows i := Summable.build (@sunit_summable_subproof CL.store C 'SO(Hq) (f i) (F i)).
have E out : (\sum_i rows i) out = \sum_i point (f i) (F i) out.
  rewrite summable_sumE; apply: eq_bigr=>i _.
  by rewrite /rows /point /sunit_def.
rewrite -(eq_sum E) summable_sum_sum.
by apply: eq_bigr=>i _; rewrite /rows sunit_sum.
Qed.

Lemma sequence_finite_points (K L : ClassicalSemantics.kernel)
    (I : finType) s (f : I -> CL.store) (F : I -> 'SO(Hq)) :
  (forall out, K s out = \sum_i point (f i) (F i) out) ->
  forall out, slet K L s out = \sum_i (L (f i) out :o F i).
Proof.
move=>HK out; change (sum (fun m => L m out :o K s m) =
  \sum_i (L (f i) out :o F i)).
under eq_sum=>m do rewrite HK linear_sumr /=.
transitivity (sum (fun m => \sum_i point (f i) (L (f i) out :o F i) m)).
  apply: eq_sum=>m; apply: eq_bigr=>i _.
  rewrite /point; case E: (m == f i); last by rewrite comp_so0r.
  by move/eqP: E=>->.
exact: sum_finite_points.
Qed.

Lemma computational_measurement_denote (q : wf_qreg QBool)
    (x : CL.variable (QType QBool)) s out :
  ClassicalSemantics.denote (CL.Measure x q (CL.EConst [QM of @tmeas bool])) s out =
    \sum_b point (s.[x <- b])%M (register_action q (projector b)) out.
Proof.
change (sum (fun b : bool => sunit_def (s.[x <- b])%M
  (measurement_branches (tc := QBool) q (CL.EConst [QM of @tmeas bool]) s b) out) =
    \sum_b point (s.[x <- b])%M (register_action q (projector b)) out).
rewrite fin_dom_sum; apply: eq_bigr=>b _.
by rewrite measurement_branchE /point /sunit_def /register_action /projector.
Qed.

Lemma computational_measurement_sequence (q : wf_qreg QBool)
    (x : CL.variable (QType QBool)) c s out :
  ClassicalSemantics.denote
    (CL.Sequence (CL.Measure x q (CL.EConst [QM of @tmeas bool])) c) s out =
    \sum_b (ClassicalSemantics.denote c (s.[x <- b])%M out :o
      register_action q (projector b)).
Proof.
apply: sequence_finite_points=>m; exact: computational_measurement_denote.
Qed.

Lemma constant_unitary_sequence u (q : wf_qreg u) (U : 'FU('Ht u)) c s out :
  ClassicalSemantics.denote (CL.Sequence (CL.Unitary q (CL.EConst U)) c) s out =
    ClassicalSemantics.denote c s out :o register_action q U.
Proof.
by apply: sequence_point=>m.
Qed.

Definition transfer_outcome_store s x z :=
  teleport_final_store (stages_zero ((s.[xA <- x]).[zA <- z])%M).

Lemma transfer_measured_zero_x s x z :
  (stages_zero ((s.[xA <- x]).[zA <- z])%M).[xA]%M = x.
Proof.
by rewrite /stages_zero get_set_nex // get_set_nex // get_set_nex // get_set_eq.
Qed.

Lemma transfer_measured_zero_z s x z :
  (stages_zero ((s.[xA <- x]).[zA <- z])%M).[zA]%M = z.
Proof.
by rewrite /stages_zero get_set_nex // get_set_nex // get_set_eq.
Qed.

Theorem transfer_serial_denote qa qb s out :
  ClassicalSemantics.denote (transfer_serial qa qb) s out =
    \sum_x \sum_z point (transfer_outcome_store s x z)
      (transfer_physical_branch qa qb z x) out.
Proof.
rewrite /transfer_serial constant_unitary_sequence constant_unitary_sequence
  computational_measurement_sequence.
under eq_bigr=>x _ do rewrite computational_measurement_sequence.
under eq_bigr=>x _ do under eq_bigr=>z _ do
  rewrite (execution_denote (transfer_tail_execution qa qb _))
    transfer_loop_actionE transfer_measured_zero_x transfer_measured_zero_z.
rewrite !linear_sumlz /=.
apply: eq_bigr=>x _; rewrite !linear_sumlz /=; apply: eq_bigr=>z _.
rewrite /point /transfer_outcome_store /transfer_physical_branch.
case: (_ == _); last by rewrite !comp_so0l.
by rewrite !comp_soA.
Qed.

Local Arguments ClassicalSemantics.denote _ : simpl never.

Lemma transfer_sequence_denote c d :
  ClassicalSemantics.denote (CL.Sequence c d) =
    slet (ClassicalSemantics.denote c) (ClassicalSemantics.denote d).
Proof. by []. Qed.

Lemma transfer_serial_denoteE qa qb :
  ClassicalSemantics.denote
    (successful_sequentialize (paired (transfer_sender qa) (transfer_receiver qb))) =
      ClassicalSemantics.denote (transfer_serial qa qb).
Proof.
rewrite /successful_sequentialize /sequentialize transfer_rendezvousE enum_two /=.
rewrite /paired /= /transfer_serial /transfer_tail /transfer_loop_suffix /transfer_round_loop.
by rewrite !transfer_sequence_denote !sletA ?slet1r.
Qed.

Theorem transfer_source_denote qa qb s out :
  ClassicalSemantics.denote
    (successful_sequentialize (paired (transfer_sender qa) (transfer_receiver qb))) s out =
    \sum_x \sum_z point (transfer_outcome_store s x z)
      (transfer_physical_branch qa qb z x) out.
Proof. by rewrite transfer_serial_denoteE transfer_serial_denote. Qed.

Theorem transfer_source_channel qa qb s :
  sum (ClassicalSemantics.denote
    (successful_sequentialize (paired (transfer_sender qa) (transfer_receiver qb))) s) =
    \sum_x \sum_z transfer_physical_branch qa qb z x.
Proof.
rewrite (eq_sum (transfer_source_denote qa qb s)).
rewrite !transfer_bool_pair_sum /=.
under eq_sum=>out do rewrite transfer_bool_pair_sum.
exact: sum_finite_points.
Qed.

Definition transfer_register_channel u (q : wf_qreg u) (E : 'SO('Ht u)) :=
  liftfso (CQMemoryTransport.conjugate [giso of (v2tU q)^A] E).

Lemma transfer_register_channel_linear u (q : wf_qreg u) :
  linear (transfer_register_channel q).
Proof.
move=>a E F; rewrite /transfer_register_channel.
rewrite (CQMemoryTransport.conjugate_linear _ a E F).
exact: linearP.
Qed.
HB.instance Definition _ u (q : wf_qreg u) := GRing.isLinear.Build C _ _ *:%R
  (transfer_register_channel q) (transfer_register_channel_linear q).

Lemma transfer_register_channel_form u (q : wf_qreg u) (A : 'End('Ht u)) :
  transfer_register_channel q (formso A) = register_action q A.
Proof.
by rewrite /transfer_register_channel CQMemoryTransport.conjugate_formso
  adjfK -tf2f_UE.
Qed.

Lemma transfer_register_channel_comp u (q : wf_qreg u) E F :
  transfer_register_channel q (E :o F) =
    transfer_register_channel q E :o transfer_register_channel q F.
Proof.
by rewrite /transfer_register_channel CQMemoryTransport.conjugate_comp liftfso_comp.
Qed.

Lemma transfer_register_channel1 u (q : wf_qreg u) :
  transfer_register_channel q \:1 = \:1.
Proof.
by rewrite /transfer_register_channel CQMemoryTransport.conjugate1 liftfso1.
Qed.

Theorem transfer_source_channel_lifted
    (q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool))) s :
  sum (ClassicalSemantics.denote (successful_sequentialize
    (paired (transfer_sender (first_register q)) (transfer_receiver (second_register q)))) s) =
      transfer_register_channel q DistributedQFTTeleport.transfer_paired_channel.
Proof.
rewrite transfer_source_channel.
under eq_bigr=>x _ do under eq_bigr=>z _ do rewrite transfer_physical_branchE.
rewrite /DistributedQFTTeleport.transfer_paired_channel linear_sum /=.
under [RHS]eq_bigr=>z _ do rewrite linear_sum /=.
under [RHS]eq_bigr=>z _ do under eq_bigr=>x _ do rewrite transfer_register_channel_form.
by rewrite exchange_big.
Qed.

Lemma transfer_outcome_store_x s x z : (transfer_outcome_store s x z).[xA]%M = x.
Proof.
rewrite /transfer_outcome_store /teleport_final_store /teleport_step_store
  get_set_nex // get_set_nex // get_set_nex // get_set_nex //
  get_set_nex // get_set_nex //.
exact: transfer_measured_zero_x.
Qed.

Lemma transfer_outcome_store_z s x z : (transfer_outcome_store s x z).[zA]%M = z.
Proof.
rewrite /transfer_outcome_store /teleport_final_store /teleport_step_store
  get_set_nex // get_set_nex // get_set_nex // get_set_nex //
  get_set_nex // get_set_nex //.
exact: transfer_measured_zero_z.
Qed.

Lemma transfer_outcome_store_inj s :
  injective (fun i : bool * bool => transfer_outcome_store s i.1 i.2).
Proof.
move=>[x z] [y w] E.
have Ex := congr1 (fun t : CL.store => (t.[xA])%M) E.
have Ez := congr1 (fun t : CL.store => (t.[zA])%M) E.
have Exy : x = y := Logic.eq_trans (Logic.eq_sym (transfer_outcome_store_x s x z))
  (Logic.eq_trans Ex (transfer_outcome_store_x s y w)).
have Ezw : z = w := Logic.eq_trans (Logic.eq_sym (transfer_outcome_store_z s x z))
  (Logic.eq_trans Ez (transfer_outcome_store_z s y w)).
exact (congr2 (@pair bool bool) Exy Ezw).
Qed.
End DistributedQFTTeleportProcesses.

(** 5. Complete transfer channel *)

(* State transfer used by qft.isq.  The source sends the pair outcome x
   before the data outcome z; the receiver applies X, then Z, then SWAP.
   The equations below concern channels on arbitrary operators, so they
   preserve correlations with the other QFT qubits. *)

Module DistributedQFTTransferCorrectness.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import DistributedQFTTeleport DistributedQFTTeleportProcesses.
Import DistributedProtocolProcesses DistributedProtocolExecution DistributedProtocolRegister.
Import ClassicalSemantics ClassicalDeterministic DistributedLanguage DistributedSequentialization.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

(** Channel wrapper for the premeasured helper, retaining every actual
    output store. This module proves decoding and reference identities;
    DistributedQFTISQTransfer repeats the row connection for literal isQ
    timing. Neither wrapper is the full many-rank source program. *)
Definition transfer_source_local_kernel s out :=
  \sum_x \sum_z if out == transfer_outcome_store s x z
    then formso (transfer_paired_branch z x) else 0.

Theorem transfer_source_kernel_lifted
    (q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool))) s out :
  ClassicalSemantics.denote (successful_sequentialize
    (paired (transfer_sender (first_register q)) (transfer_receiver (second_register q))))
    s out = transfer_register_channel q (transfer_source_local_kernel s out).
Proof.
rewrite transfer_source_denote /transfer_source_local_kernel linear_sum /=.
under [RHS]eq_bigr=>x _ do rewrite linear_sum /=.
apply: eq_bigr=>x _; apply: eq_bigr=>z _.
rewrite /point; case: (_ == _); first by
  rewrite transfer_register_channel_form transfer_physical_branchE.
by rewrite linear0.
Qed.

Section Reference.
Variable R : ihbFinType.
Local Notation logical := 'Hs ((bool * bool) * R)%type.

(* The classical store may itself be correlated with the quantum reference:
   the theorem below holds for every initial store and every operator. *)
Definition transfer_source_reference_kernel (s out : CL.store) :=
  \sum_x \sum_z if out == transfer_outcome_store s x z
    then formso (transfer_paired_branch_ref R z x) else 0.

Definition transfer_outcome_weight (s out : CL.store) : C :=
  \sum_x \sum_z if out == transfer_outcome_store s x z then ((4%:R : C)^-1)%R else 0.

Lemma transfer_outcome_weightE s x z :
  transfer_outcome_weight s (transfer_outcome_store s x z) = ((4%:R : C)^-1)%R.
Proof.
rewrite /transfer_outcome_weight transfer_bool_pair_sum /= (bigD1 (x,z)) //= big1.
- move=>[y w] /negPf H.
  case E: (transfer_outcome_store s x z == transfer_outcome_store s y w)=>//.
  have Et := @transfer_outcome_store_inj s (x,z) (y,w) (elimT eqP E).
  by move: H; rewrite -Et eqxx.
- by rewrite eqxx addr0.
Qed.

Lemma sum_finite_point_values (I : finType) (V : completeNormedModType C)
    (f : I -> CL.store) (F : I -> V) :
  sum (fun out => \sum_i if out == f i then F i else 0) = \sum_i F i.
Proof.
pose rows i := Summable.build (@sunit_summable_subproof CL.store C V (f i) (F i)).
have E out : (\sum_i rows i) out = \sum_i if out == f i then F i else 0.
  by rewrite summable_sumE.
rewrite -(eq_sum E) summable_sum_sum.
by apply: eq_bigr=>i _; rewrite /rows sunit_sum.
Qed.

Lemma transfer_outcome_weight_total s : sum (transfer_outcome_weight s) = 1.
Proof.
rewrite /transfer_outcome_weight.
under eq_sum=>out do rewrite transfer_bool_pair_sum.
rewrite sum_finite_point_values sumr_const card_prod !card_bool -[LHS]mulr_natr.
change (((4%:R : C)^-1)%R * (4%:R : C) = 1).
by rewrite mulVf // pnatr_eq0.
Qed.

Theorem transfer_source_decoded_kernel s out :
  transfer_paired_decode_ref R :o transfer_source_reference_kernel s out :o
    formso (transfer_paired_resource_ref R) =
      transfer_outcome_weight s out *: (\:1 : 'SO(logical)).
Proof.
rewrite /transfer_source_reference_kernel /transfer_outcome_weight
  -comp_soA linear_sumlz /= linear_sumr /= scaler_suml.
apply: eq_bigr=>x _.
rewrite linear_sumlz /= linear_sumr /= scaler_suml.
apply: eq_bigr=>z _.
case: (_ == _); first by rewrite comp_soA transfer_paired_decoded_branch_ref.
by rewrite comp_so0l comp_so0r scale0r.
Qed.

Corollary transfer_source_cq_reference s out (rho : 'End(logical)) :
  transfer_paired_decode_ref R
    (transfer_source_reference_kernel s out (formso (transfer_paired_resource_ref R) rho)) =
      transfer_outcome_weight s out *: rho.
Proof.
by rewrite -!comp_soE transfer_source_decoded_kernel scale_soE id_soE.
Qed.

Theorem transfer_source_reduced_cq_reference s out (rho : 'End(logical)) :
  transfer_paired_data_output_ref R
    (transfer_source_reference_kernel s out (formso (transfer_paired_resource_ref R) rho)) =
      transfer_outcome_weight s out *: discard_old_destination_ref R rho.
Proof.
by rewrite /transfer_paired_data_output_ref comp_soE transfer_source_cq_reference linearZ.
Qed.

(* Pointwise equality of kernels also permits an arbitrary correlation
   between the input classical store and its quantum density operator. *)
Theorem transfer_correlated_cq_reference
    (d : CL.store -> 'End(logical)) out :
  sum (fun s => transfer_paired_decode_ref R
    (transfer_source_reference_kernel s out (formso (transfer_paired_resource_ref R) (d s)))) =
      sum (fun s => transfer_outcome_weight s out *: d s).
Proof. by apply: eq_sum=>s; rewrite transfer_source_cq_reference. Qed.

Theorem transfer_correlated_reduced_cq_reference
    (d : CL.store -> 'End(logical)) out :
  sum (fun s => transfer_paired_data_output_ref R
    (transfer_source_reference_kernel s out (formso (transfer_paired_resource_ref R) (d s)))) =
      sum (fun s => transfer_outcome_weight s out *: discard_old_destination_ref R (d s)).
Proof. by apply: eq_sum=>s; rewrite transfer_source_reduced_cq_reference. Qed.
End Reference.

Theorem transfer_source_reference_kernel_lifted (T : qType)
    (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) T)) s out :
  ClassicalSemantics.denote (successful_sequentialize
    (paired (transfer_sender (first_register (first_register q)))
      (transfer_receiver (second_register (first_register q))))) s out =
        transfer_register_channel q
          (@transfer_source_reference_kernel (eval_qtype T) s out).
Proof.
rewrite transfer_source_denote /transfer_source_reference_kernel linear_sum /=.
under [RHS]eq_bigr=>x _ do rewrite linear_sum /=.
apply: eq_bigr=>x _; apply: eq_bigr=>z _.
rewrite /point; case: (_ == _); last by rewrite linear0.
by rewrite transfer_register_channel_form transfer_physical_branchE
  register_action_left /transfer_paired_branch_ref.
Qed.
End DistributedQFTTransferCorrectness.

(** 6. Source transfer variants *)

(* State transfer used by qft.isq.  The source sends the pair outcome x
   before the data outcome z; the receiver applies X, then Z, then SWAP.
   The equations below concern channels on arbitrary operators, so they
   preserve correlations with the other QFT qubits. *)

Module DistributedQFTISQTransfer.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic ClassicalAlgorithmSemantics.
Import DistributedLanguage DistributedCommunication DistributedSequentialization.
Import DistributedProtocolProcesses DistributedProtocolOwnership DistributedProtocolExecution.
Import DistributedProtocolSuffix DistributedProtocolSerial DistributedProtocolQuantum DistributedProtocolRegister.
Import DistributedQFTTeleport DistributedQFTTeleportProcesses DistributedQFTTransferCorrectness.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

(** Literal sender endpoint for qft.isq teleport_send. CNOT(q,pair), H(q),
    and M(pair)=x occur in initialization. The first Output 88 transmits x;
    only its continuation measures M(q)=z, which the second Output 88 sends.
    Thus the second measurement is not moved before the first communication.
    Together with transfer_receiver this models both source endpoints after
    the ideal create_epr service has supplied their fresh shared Bell pair. *)
Definition transfer_isq_sender (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (gate (first_register q) [unitary of Hadamard])
    (Sequence (measure (second_register q) xA) (set_stage stageA 0))))
    stageA
    (fun i => Output "88" (CL.EVar (if i == ord0 then xA else zA)))
    (fun i => if i == ord0 then
      Sequence (measure (first_register q) zA) (set_stage stageA i.+1)
      else set_stage stageA i.+1).

Lemma transfer_isq_sender_wf q : process_wf (transfer_isq_sender q).
Proof.
apply: two_round_wf; first by repeat split.
by move=>i; case: (i == ord0)=>/=; repeat split.
Qed.

Lemma transfer_isq_sender_finite q : finite_set (process_reads (transfer_isq_sender q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1].
Qed.

Lemma transfer_isq_sender_owned q : process_owned "Alice" (transfer_isq_sender q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned;
    first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; case: (i == ord0); last by apply: set_stage_owned.
  apply: sequence_owned; first by apply: measure_owned.
  by apply: set_stage_owned.
Qed.

Lemma transfer_isq_sender_quantum q : process_quantum (transfer_isq_sender q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset !fintype.subxx !finset.sub0set
  /= !first_register_subset !second_register_subset /=.
apply/bigcupsP=>i _; case: (i == ord0)=>/=; last exact: finset.sub0set.
by rewrite finset.setU0; exact: first_register_subset.
Qed.

Definition transfer_isq_program (qa qb : wf_qreg (QPair QBool QBool))
    (Hdis : [disjoint mset qa & mset qb]) : program.
Proof.
apply: (@Program 2 (pair_processes (transfer_isq_sender qa) (transfer_receiver qb)) erefl).
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: transfer_isq_sender_wf | exact: transfer_receiver_wf].
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: transfer_isq_sender_finite | exact: transfer_receiver_finite].
- exact: (@pair_private (transfer_isq_sender qa) (transfer_receiver qb) (mset qa) (mset qb)
    (@transfer_isq_sender_owned qa) (@transfer_receiver_owned qb)
    (@transfer_isq_sender_quantum qa) (@transfer_receiver_quantum qb) Hdis).
- exact: pair_point_to_point.
Defined.

Definition transfer_isq_rendezvous (qa qb : wf_qreg (QPair QBool QBool)) (i j : 'I_2) :
    expression bool * CL.command :=
  (guard_and (stage_guard stageA i) (stage_guard stageB j),
   CL.Sequence (CL.Assign (if j == ord0 then xB else zB)
     (CL.EVar (if i == ord0 then xA else zA)))
   (CL.Sequence (if i == ord0 then
     CL.Sequence (CL.Measure zA (first_register qa) (CL.EConst [QM of @tmeas bool]))
       (CL.Assign stageA (CL.EConst (Posz i.+1)))
     else CL.Assign stageA (CL.EConst (Posz i.+1)))
   (translate_statement (Sequence (set_stage stageB j.+1)
     (if j == ord0 then correct (first_register qb) xB [unitary of PauliX]
      else Sequence (correct (first_register qb) zB [unitary of PauliZ])
        (gate qb [unitary of (@swaptf bool bool)])))))).

Lemma transfer_isq_rendezvousE qa qb :
  rendezvous_commands (paired (transfer_isq_sender qa) (transfer_receiver qb)) =
  [:: transfer_isq_rendezvous qa qb ord0 ord0;
      transfer_isq_rendezvous qa qb ord0 round_one;
      transfer_isq_rendezvous qa qb round_one ord0;
      transfer_isq_rendezvous qa qb round_one round_one].
Proof.
Arguments communication_effect _ _ : simpl never.
rewrite /rendezvous_commands !enum_two /= /paired /=
  /rendezvous_command /= !enum_two /=.
rewrite (matching_effect (MatchOutput "88" xB (CL.EVar xA)))
  (matching_effect (MatchOutput "88" zB (CL.EVar xA)))
  (matching_effect (MatchOutput "88" xB (CL.EVar zA)))
  (matching_effect (MatchOutput "88" zB (CL.EVar zA))).
by rewrite /transfer_isq_rendezvous /=.
Qed.

Lemma transfer_isq_guardE qa qb i j s k : synchronized_at s k ->
  eval (transfer_isq_rendezvous qa qb i j).1 s = ((k == val i) && (k == val j)).
Proof.
move=>[Ha Hb]; rewrite /transfer_isq_rendezvous /guard_and /stage_guard /= ?Ha ?Hb.
by rewrite !eqz_nat.
Qed.

Lemma transfer_isq_round_guardE qa qb s k : synchronized_at s k ->
  eval (guards_any [seq r.1 | r <-
    [:: transfer_isq_rendezvous qa qb ord0 ord0;
        transfer_isq_rendezvous qa qb ord0 round_one;
        transfer_isq_rendezvous qa qb round_one ord0;
        transfer_isq_rendezvous qa qb round_one round_one]]) s =
    ((k == 0%N) || (k == 1%N)).
Proof.
move=>Hs.
change (eval (guards_any [seq r.1 | r <-
  [:: transfer_rendezvous qb ord0 ord0;
      transfer_rendezvous qb ord0 round_one;
      transfer_rendezvous qb round_one ord0;
      transfer_rendezvous qb round_one round_one]]) s =
  ((k == 0%N) || (k == 1%N))).
exact (@transfer_round_guardE qb s k Hs).
Qed.

Definition transfer_isq_round_loop qa qb :=
  let rounds := [:: transfer_isq_rendezvous qa qb ord0 ord0;
      transfer_isq_rendezvous qa qb ord0 round_one;
      transfer_isq_rendezvous qa qb round_one ord0;
      transfer_isq_rendezvous qa qb round_one round_one] in
  CL.While (guards_any [seq r.1 | r <- rounds]) (conditional_chain rounds).

Lemma transfer_isq_round_one_execution qa qb s : synchronized_at s 1 ->
  execution (transfer_isq_round_loop qa qb) s (teleport_step_store round_one s)
    (transfer_step_action qb round_one s).
Proof.
move=>Hs.
have Ht := teleport_step_synchronized round_one s.
have Es i j := transfer_isq_guardE qa qb i j Hs.
have Et i j := transfer_isq_guardE qa qb i j Ht.
have Dbody : execution
    (conditional_chain [:: transfer_isq_rendezvous qa qb ord0 ord0;
      transfer_isq_rendezvous qa qb ord0 round_one;
      transfer_isq_rendezvous qa qb round_one ord0;
      transfer_isq_rendezvous qa qb round_one round_one]) s
    (teleport_step_store round_one s) (transfer_step_action qb round_one s).
  apply: RunIfFalse; first by rewrite Es.
  apply: RunIfFalse; first by rewrite Es.
  apply: RunIfFalse; first by rewrite Es.
  apply: RunIfTrue; first by rewrite Es.
  exact: transfer_step_execution.
have Dstop : execution (transfer_isq_round_loop qa qb) (teleport_step_store round_one s)
    (teleport_step_store round_one s) \:1.
  apply: RunWhileFalse; by rewrite (transfer_isq_round_guardE qa qb Ht).
rewrite -(comp_so1l (transfer_step_action qb round_one s)).
apply: RunWhileTrue Dbody Dstop.
by rewrite (transfer_isq_round_guardE qa qb Hs).
Qed.

Lemma transfer_isq_terminationE qa qb s : synchronized_at s 2 ->
  eval (termination_guard (paired (transfer_isq_sender qa) (transfer_receiver qb))) s = true.
Proof.
move=>[Ha Hb]; rewrite /termination_guard !enum_two /= /paired /= !enum_two /=.
by rewrite /guards_all /guard_and /guard_not /stage_guard /= Ha Hb.
Qed.

Definition transfer_isq_loop_suffix qa qb :=
  CL.Sequence (transfer_isq_round_loop qa qb)
    (CL.Conditional (termination_guard (paired (transfer_isq_sender qa) (transfer_receiver qb)))
      CL.Skip CL.Abort).

Lemma transfer_isq_suffix_one_execution qa qb s : synchronized_at s 1 ->
  execution (transfer_isq_loop_suffix qa qb) s (teleport_step_store round_one s)
    (transfer_step_action qb round_one s).
Proof.
move=>Hs; rewrite -(comp_so1l (transfer_step_action qb round_one s)).
apply: RunSequence (transfer_isq_round_one_execution qa qb Hs) _.
apply: RunIfTrue; last exact: RunSkip.
apply: transfer_isq_terminationE; exact: teleport_step_synchronized.
Qed.
Definition transfer_isq_after_measure_store t :=
  (t.[stageA <- (1 : int)]).[stageB <- (1 : int)]%M.

Lemma transfer_isq_after_measure_sync t :
  synchronized_at (transfer_isq_after_measure_store t) 1.
Proof.
split; rewrite /transfer_isq_after_measure_store; last exact: get_set_eq.
by rewrite get_set_nex // get_set_eq.
Qed.

Definition transfer_isq_after_measure_command qa qb :=
  CL.Sequence (CL.Assign stageA (CL.EConst (1 : int)))
  (CL.Sequence
    (CL.Sequence (CL.Assign stageB (CL.EConst (1 : int)))
      (translate_statement (correct (first_register qb) xB [unitary of PauliX])))
    (transfer_isq_loop_suffix qa qb)).

Definition transfer_isq_after_measure_action qb t :=
  transfer_step_action qb round_one (transfer_isq_after_measure_store t) :o
    correction_action (first_register qb) [unitary of PauliX] (t.[xB])%M.

Lemma transfer_isq_after_measure_execution qa qb t :
  execution (transfer_isq_after_measure_command qa qb) t
    (teleport_step_store round_one (transfer_isq_after_measure_store t))
    (transfer_isq_after_measure_action qb t).
Proof.
have D := RunSequence (RunAssign stageA (CL.EConst (1 : int)) t)
  (RunSequence
    (RunSequence (RunAssign stageB (CL.EConst (1 : int)) _)
      (correct_execution (first_register qb) xB [unitary of PauliX] _))
    (transfer_isq_suffix_one_execution qa qb (transfer_isq_after_measure_sync t))).
rewrite !comp_so1r !get_set_nex // in D; exact: D.
Qed.

Lemma constant_assignment_sequence t (x : CL.variable t) e c s out :
  ClassicalSemantics.denote (CL.Sequence (CL.Assign x e) c) s out =
    ClassicalSemantics.denote c (s.[x <- CL.eval e s])%M out.
Proof.
rewrite -(comp_so1r (ClassicalSemantics.denote c (s.[x <- CL.eval e s])%M out)).
apply: sequence_point=>m; exact: (execution_denote (RunAssign x e s) m).
Qed.

Lemma transfer_isq_suffix_unfold qa qb s out : synchronized_at s 0 ->
  ClassicalSemantics.denote (transfer_isq_loop_suffix qa qb) s out =
    ClassicalSemantics.denote (CL.Sequence (transfer_isq_rendezvous qa qb ord0 ord0).2
      (transfer_isq_loop_suffix qa qb)) s out.
Proof.
move=>Hs; have Es i j := transfer_isq_guardE qa qb i j Hs.
have Eguard : eval (guards_any [seq r.1 | r <-
    [:: transfer_isq_rendezvous qa qb ord0 ord0;
        transfer_isq_rendezvous qa qb ord0 round_one;
        transfer_isq_rendezvous qa qb round_one ord0;
        transfer_isq_rendezvous qa qb round_one round_one]]) s = true.
  by rewrite (transfer_isq_round_guardE qa qb Hs).
have Erow m : ClassicalSemantics.denote (transfer_isq_round_loop qa qb) s m =
    ClassicalSemantics.denote (CL.Sequence (transfer_isq_rendezvous qa qb ord0 ord0).2
      (transfer_isq_round_loop qa qb)) s m.
  rewrite {1}/transfer_isq_round_loop denote_while_unfold denote_conditional Eguard.
  change (sum (fun t => ClassicalSemantics.denote (transfer_isq_round_loop qa qb) t m :o
    ClassicalSemantics.denote (conditional_chain
      [:: transfer_isq_rendezvous qa qb ord0 ord0;
          transfer_isq_rendezvous qa qb ord0 round_one;
          transfer_isq_rendezvous qa qb round_one ord0;
          transfer_isq_rendezvous qa qb round_one round_one]) s t) =
    ClassicalSemantics.denote (CL.Sequence (transfer_isq_rendezvous qa qb ord0 ord0).2
      (transfer_isq_round_loop qa qb)) s m).
  under eq_sum=>t do rewrite denote_conditional (Es ord0 ord0).
  by [].
change (sum (fun m => ClassicalSemantics.denote
  (CL.Conditional (termination_guard (paired (transfer_isq_sender qa) (transfer_receiver qb)))
    CL.Skip CL.Abort) m out :o
  ClassicalSemantics.denote (transfer_isq_round_loop qa qb) s m) =
    ClassicalSemantics.denote (CL.Sequence (transfer_isq_rendezvous qa qb ord0 ord0).2
      (transfer_isq_loop_suffix qa qb)) s out).
under eq_sum=>m do rewrite Erow.
change (slet (slet (ClassicalSemantics.denote (transfer_isq_rendezvous qa qb ord0 ord0).2)
  (ClassicalSemantics.denote (transfer_isq_round_loop qa qb)))
  (ClassicalSemantics.denote (CL.Conditional
    (termination_guard (paired (transfer_isq_sender qa) (transfer_receiver qb)))
    CL.Skip CL.Abort)) s out =
    ClassicalSemantics.denote (CL.Sequence (transfer_isq_rendezvous qa qb ord0 ord0).2
      (transfer_isq_loop_suffix qa qb)) s out).
by rewrite sletA.
Qed.

Definition transfer_isq_first_store s z :=
  transfer_isq_after_measure_store ((s.[xB <- (s.[xA])%M]).[zA <- z])%M.

Lemma transfer_isq_suffix_denote qa qb s out : synchronized_at s 0 ->
  ClassicalSemantics.denote (transfer_isq_loop_suffix qa qb) s out =
    \sum_z point (teleport_step_store round_one (transfer_isq_first_store s z))
      (transfer_isq_after_measure_action qb ((s.[xB <- (s.[xA])%M]).[zA <- z])%M :o
        register_action (first_register qa) (projector z)) out.
Proof.
move=>Hs; rewrite (@transfer_isq_suffix_unfold qa qb s out Hs)
  /transfer_isq_rendezvous denote_sequenceA constant_assignment_sequence
  denote_sequenceA denote_sequenceA.
change (ClassicalSemantics.denote
  (CL.Sequence (CL.Measure zA (first_register qa) (CL.EConst [QM of @tmeas bool]))
    (transfer_isq_after_measure_command qa qb)) (s.[xB <- (s.[xA])%M])%M out =
    \sum_z point (teleport_step_store round_one (transfer_isq_first_store s z))
      (transfer_isq_after_measure_action qb ((s.[xB <- (s.[xA])%M]).[zA <- z])%M :o
        register_action (first_register qa) (projector z)) out).
rewrite computational_measurement_sequence.
apply: eq_bigr=>z _.
rewrite (execution_denote (transfer_isq_after_measure_execution qa qb _) out)
  /point /transfer_isq_first_store.
case: (_ == _); last by rewrite comp_so0l.
by [].
Qed.

Lemma transfer_isq_first_actionE qb s z :
  transfer_isq_after_measure_action qb ((s.[xB <- (s.[xA])%M]).[zA <- z])%M =
    register_action qb (@swaptf bool bool \o
      ((pauli_z z \o pauli_x (s.[xA])%M) ⊗f (\1 : 'End('Hs bool)))).
Proof.
have Ez : ((transfer_isq_after_measure_store
    ((s.[xB <- (s.[xA])%M]).[zA <- z])%M).[zA])%M = z.
  by rewrite /transfer_isq_after_measure_store get_set_nex // get_set_nex // get_set_eq.
have Ex : (((s.[xB <- (s.[xA])%M]).[zA <- z]).[xB])%M = (s.[xA])%M.
  by rewrite get_set_nex // get_set_eq.
have Eround : (round_one == ord0) = false by [].
rewrite /transfer_isq_after_measure_action /transfer_step_action Eround Ez Ex
  correction_actionX correction_actionZ !register_action_left
  !register_action_comp -comp_lfunA tentf_comp comp_lfun1l.
by [].
Qed.

Definition transfer_isq_tail qa qb :=
  CL.Sequence (CL.Assign stageA (CL.EConst (0 : int)))
    (CL.Sequence (CL.Sequence (CL.Assign stageB (CL.EConst (0 : int))) CL.Skip)
      (transfer_isq_loop_suffix qa qb)).

Lemma transfer_isq_tail_denote qa qb s out :
  ClassicalSemantics.denote (transfer_isq_tail qa qb) s out =
    \sum_z point (teleport_step_store round_one (transfer_isq_first_store (stages_zero s) z))
      (register_action qb (@swaptf bool bool \o
        ((pauli_z z \o pauli_x (s.[xA])%M) ⊗f (\1 : 'End('Hs bool)))) :o
        register_action (first_register qa) (projector z)) out.
Proof.
rewrite /transfer_isq_tail constant_assignment_sequence denote_sequenceA
  constant_assignment_sequence denote_skip_left
  (@transfer_isq_suffix_denote qa qb (stages_zero s) out (stages_zero_synchronized s)).
apply: eq_bigr=>z _.
by rewrite transfer_isq_first_actionE /stages_zero !get_set_nex.
Qed.

Definition transfer_isq_serial (qa qb : wf_qreg (QPair QBool QBool)) :=
  CL.Sequence (CL.Unitary qa (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Unitary (first_register qa) (CL.EConst [unitary of Hadamard]))
  (CL.Sequence (CL.Measure xA (second_register qa) (CL.EConst [QM of @tmeas bool]))
    (transfer_isq_tail qa qb))).

Definition transfer_isq_outcome_store s x z :=
  teleport_step_store round_one (transfer_isq_first_store (stages_zero (s.[xA <- x])%M) z).

Theorem transfer_isq_serial_denote qa qb s out :
  ClassicalSemantics.denote (transfer_isq_serial qa qb) s out =
    \sum_x \sum_z point (transfer_isq_outcome_store s x z)
      (transfer_physical_branch qa qb z x) out.
Proof.
rewrite /transfer_isq_serial constant_unitary_sequence constant_unitary_sequence
  computational_measurement_sequence.
under eq_bigr=>x _ do rewrite transfer_isq_tail_denote get_set_eq.
rewrite !linear_sumlz /=.
apply: eq_bigr=>x _; rewrite !linear_sumlz /=; apply: eq_bigr=>z _.
rewrite /point /transfer_isq_outcome_store /transfer_physical_branch.
case: (_ == _); last by rewrite !comp_so0l.
by rewrite !comp_soA.
Qed.

Local Arguments ClassicalSemantics.denote _ : simpl never.

Lemma transfer_isq_serial_denoteE qa qb :
  ClassicalSemantics.denote
    (successful_sequentialize (paired (transfer_isq_sender qa) (transfer_receiver qb))) =
      ClassicalSemantics.denote (transfer_isq_serial qa qb).
Proof.
rewrite /successful_sequentialize /sequentialize transfer_isq_rendezvousE enum_two /=.
rewrite /paired /= /transfer_isq_serial /transfer_isq_tail
  /transfer_isq_loop_suffix /transfer_isq_round_loop.
by rewrite !transfer_sequence_denote !sletA ?slet1r ?slet1l.
Qed.

(** Exact literal two-endpoint row, including both measurement assignments,
    communication copies, and final stage values. The full QFT instead uses
    call_preparation/call_first_message/call_second_message in
    DistributedQFTLowering (qft_model.v), with actual rank-specific registers
    and variables. Its checked canonicalization and call_serial_denote in
    qft.v connect that source to this common transfer_physical_branch family;
    they do not replace its processes by the Alice/Bob helper. *)
Theorem transfer_isq_source_denote qa qb s out :
  ClassicalSemantics.denote
    (successful_sequentialize (paired (transfer_isq_sender qa) (transfer_receiver qb))) s out =
    \sum_x \sum_z point (transfer_isq_outcome_store s x z)
      (transfer_physical_branch qa qb z x) out.
Proof. by rewrite transfer_isq_serial_denoteE transfer_isq_serial_denote. Qed.

Theorem transfer_isq_distributed_denote
    (qa qb : wf_qreg (QPair QBool QBool))
    (Hdis : [disjoint mset qa & mset qb]) s (rho : 'FD1(Hq)) out :
  DistributedSchedulerResults.denote_program (@transfer_isq_program qa qb Hdis) s rho out =
    (\sum_x \sum_z point (transfer_isq_outcome_store s x z)
      (transfer_physical_branch qa qb z x) out) rho.
Proof.
rewrite DistributedCorrespondence.denote_program_point.
change (ClassicalSemantics.denote (successful_sequentialize
  (paired (transfer_isq_sender qa) (transfer_receiver qb))) s out rho =
    (\sum_x \sum_z point (transfer_isq_outcome_store s x z)
      (transfer_physical_branch qa qb z x) out) rho).
by rewrite transfer_isq_source_denote.
Qed.

Theorem transfer_isq_source_channel qa qb s :
  sum (ClassicalSemantics.denote
    (successful_sequentialize (paired (transfer_isq_sender qa) (transfer_receiver qb))) s) =
      \sum_x \sum_z transfer_physical_branch qa qb z x.
Proof.
rewrite (eq_sum (transfer_isq_source_denote qa qb s)) !transfer_bool_pair_sum /=.
under eq_sum=>out do rewrite transfer_bool_pair_sum.
exact: sum_finite_points.
Qed.

Lemma transfer_isq_outcome_store_x s x z : (transfer_isq_outcome_store s x z).[xA]%M = x.
Proof.
rewrite /transfer_isq_outcome_store /transfer_isq_first_store /transfer_isq_after_measure_store
  /teleport_step_store /stages_zero.
by repeat first [rewrite get_set_eq | rewrite get_set_nex //].
Qed.

Lemma transfer_isq_outcome_store_z s x z : (transfer_isq_outcome_store s x z).[zA]%M = z.
Proof.
rewrite /transfer_isq_outcome_store /transfer_isq_first_store /transfer_isq_after_measure_store
  /teleport_step_store /stages_zero.
by repeat first [rewrite get_set_eq | rewrite get_set_nex //].
Qed.

Lemma transfer_isq_outcome_store_inj s :
  injective (fun i : bool * bool => transfer_isq_outcome_store s i.1 i.2).
Proof.
move=>[x z] [y w] E.
have Ex : x = y := eq_trans (esym (transfer_isq_outcome_store_x s x z))
  (eq_trans (congr1 (fun t : CL.store => (t.[xA])%M) E)
    (transfer_isq_outcome_store_x s y w)).
have Ez : z = w := eq_trans (esym (transfer_isq_outcome_store_z s x z))
  (eq_trans (congr1 (fun t : CL.store => (t.[zA])%M) E)
    (transfer_isq_outcome_store_z s y w)).
by rewrite -Ex -Ez.
Qed.

Definition transfer_isq_outcome_weight (s out : CL.store) : C :=
  \sum_x \sum_z if out == transfer_isq_outcome_store s x z then ((4%:R : C)^-1)%R else 0.

Lemma transfer_isq_outcome_weightE s x z :
  transfer_isq_outcome_weight s (transfer_isq_outcome_store s x z) = ((4%:R : C)^-1)%R.
Proof.
rewrite /transfer_isq_outcome_weight transfer_bool_pair_sum /= (bigD1 (x,z)) //= big1.
- move=>[y w] /negPf H.
  case E: (transfer_isq_outcome_store s x z == transfer_isq_outcome_store s y w)=>//.
  have Et := @transfer_isq_outcome_store_inj s (x,z) (y,w) (elimT eqP E).
  by move: H; rewrite -Et eqxx.
- by rewrite eqxx addr0.
Qed.

Lemma transfer_isq_outcome_weight_total s : sum (transfer_isq_outcome_weight s) = 1.
Proof.
rewrite /transfer_isq_outcome_weight.
under eq_sum=>out do rewrite transfer_bool_pair_sum.
rewrite sum_finite_point_values sumr_const card_prod !card_bool -[LHS]mulr_natr.
change (((4%:R : C)^-1)%R * (4%:R : C) = 1).
by rewrite mulVf // pnatr_eq0.
Qed.

Lemma transfer_isq_weighted_value_total (V : completeNormedModType C) s (v : V) :
  sum (fun out => transfer_isq_outcome_weight s out *: v) = v.
Proof.
have E out : transfer_isq_outcome_weight s out *: v =
    \sum_x \sum_z if out == transfer_isq_outcome_store s x z
      then ((4%:R : C)^-1)%R *: v else 0.
  rewrite /transfer_isq_outcome_weight scaler_suml.
  apply: eq_bigr=>x _; rewrite scaler_suml; apply: eq_bigr=>z _.
  by case: (_ == _); rewrite ?scale0r.
rewrite (eq_sum E).
under eq_sum=>out do rewrite transfer_bool_pair_sum.
rewrite sum_finite_point_values sumr_const card_prod !card_bool -scaler_nat scalerA.
by rewrite mulfV ?pnatr_eq0 // scale1r.
Qed.

Lemma transfer_cq_selected_summable (V : completeNormedModType C)
    (P : pred CL.store) (d : {summable CL.store -> V}) :
  summable (fun s => if P s then d s else 0).
Proof.
exists `|d|; near=>J.
apply: (le_trans _ (psum_norm_ler_norm d J)).
rewrite /psum; apply: ler_sum=>s _.
rewrite /normf /=.
by case: (P (val s)); rewrite ?normr0 // normr_ge0.
Unshelve. end_near.
Qed.

Lemma transfer_isq_weighted_distributionE (V : completeNormedModType C)
    (d : {summable CL.store -> V}) out :
  sum (fun s => transfer_isq_outcome_weight s out *: d s) =
    \sum_(i : bool * bool) sdlet_def
      (fun s => transfer_isq_outcome_store s i.1 i.2) (((4%:R : C)^-1)%R *: d) out.
Proof.
pose rows (i : bool * bool) := Summable.build
  (transfer_cq_selected_summable
    (fun s => out == transfer_isq_outcome_store s i.1 i.2) (((4%:R : C)^-1)%R *: d)).
have E s : transfer_isq_outcome_weight s out *: d s = \sum_i rows i s.
  rewrite /transfer_isq_outcome_weight transfer_bool_pair_sum /= scaler_suml.
  apply: eq_bigr=>[[x z]] _; rewrite /rows /=.
  by case: (_ == _); rewrite ?scale0r.
rewrite (eq_sum E).
have Es s : (\sum_i rows i) s = \sum_i rows i s.
  by rewrite summable_sumE.
rewrite -(eq_sum Es) summable_sum_sum; apply: eq_bigr=>[[x z]] _.
by rewrite /rows /sdlet_def /sunit_def.
Qed.

(* No finite-support restriction is imposed on the initial classical
   distribution.  Each outcome is a pushforward of one quarter of it. *)
Theorem transfer_isq_total_correlated_value (V : completeNormedModType C)
    (d : {summable CL.store -> V}) :
  sum (fun out => sum (fun s => transfer_isq_outcome_weight s out *: d s)) = sum d.
Proof.
rewrite (eq_sum (transfer_isq_weighted_distributionE d)).
pose rows (i : bool * bool) := Summable.build (@sdlet_summable_subproof
  CL.store CL.store V (fun s => transfer_isq_outcome_store s i.1 i.2) (((4%:R : C)^-1)%R *: d)).
have E out : (\sum_i rows i) out = \sum_(i : bool * bool) sdlet_def
    (fun s => transfer_isq_outcome_store s i.1 i.2) (((4%:R : C)^-1)%R *: d) out.
  by rewrite summable_sumE.
rewrite -(eq_sum E) summable_sum_sum.
under eq_bigr do rewrite /rows sdlet_sum summable_sumZ.
rewrite sumr_const card_prod !card_bool -scaler_nat scalerA.
by rewrite mulfV ?pnatr_eq0 // scale1r.
Qed.

Section Reference.
Variable R : ihbFinType.
Local Notation logical := 'Hs ((bool * bool) * R)%type.

(** Framed literal row: x and z select the actual final classical store,
    while the reference is untouched. The resource embedding below inserts
    the independent Bell pair and allows data and old destination to be
    jointly entangled with that reference. Summing output stores erases only
    the classical record; the reduced decoder also discards the old destination. *)
Definition transfer_isq_reference_kernel (s out : CL.store) :=
  \sum_x \sum_z if out == transfer_isq_outcome_store s x z
    then formso (transfer_paired_branch_ref R z x) else 0.

Theorem transfer_isq_decoded_kernel s out :
  transfer_paired_decode_ref R :o transfer_isq_reference_kernel s out :o
    formso (transfer_paired_resource_ref R) =
      transfer_isq_outcome_weight s out *: (\:1 : 'SO(logical)).
Proof.
rewrite /transfer_isq_reference_kernel /transfer_isq_outcome_weight
  -comp_soA linear_sumlz /= linear_sumr /= scaler_suml.
apply: eq_bigr=>x _.
rewrite linear_sumlz /= linear_sumr /= scaler_suml.
apply: eq_bigr=>z _.
case: (_ == _); first by rewrite comp_soA transfer_paired_decoded_branch_ref.
by rewrite comp_so0l comp_so0r scale0r.
Qed.

(* Sum the literal program's actual classical output stores.  This is the
   usable per-hop data channel; both input wires may be entangled with R. *)
Theorem transfer_isq_total_decoded_channel s :
  sum (fun out => transfer_paired_decode_ref R :o
    transfer_isq_reference_kernel s out :o
      formso (transfer_paired_resource_ref R)) = (\:1 : 'SO(logical)).
Proof.
rewrite (eq_sum (transfer_isq_decoded_kernel s)).
exact: transfer_isq_weighted_value_total.
Qed.

Theorem transfer_isq_total_reduced_channel s :
  sum (fun out => transfer_paired_data_output_ref R :o
    transfer_isq_reference_kernel s out :o
      formso (transfer_paired_resource_ref R)) = discard_old_destination_ref R.
Proof.
have E out : transfer_paired_data_output_ref R :o
    transfer_isq_reference_kernel s out :o formso (transfer_paired_resource_ref R) =
      transfer_isq_outcome_weight s out *: discard_old_destination_ref R.
  rewrite /transfer_paired_data_output_ref
    -(comp_soA (discard_old_destination_ref R) (transfer_paired_decode_ref R)
      (transfer_isq_reference_kernel s out))
    -(comp_soA (discard_old_destination_ref R)
      (transfer_paired_decode_ref R :o transfer_isq_reference_kernel s out)
      (formso (transfer_paired_resource_ref R))).
  by rewrite transfer_isq_decoded_kernel comp_soZr comp_so1r.
rewrite (eq_sum E); exact: transfer_isq_weighted_value_total.
Qed.

Theorem transfer_isq_gated_decoded_kernel U s out :
  transfer_paired_decode_ref R :o formso (@transfer_paired_encoded_gate_ref R U) :o
    transfer_isq_reference_kernel s out :o formso (transfer_paired_resource_ref R) =
      transfer_isq_outcome_weight s out *: formso U.
Proof.
rewrite /transfer_isq_reference_kernel /transfer_isq_outcome_weight
  linear_sumr /= linear_sumlz /= scaler_suml.
apply: eq_bigr=>x _.
rewrite linear_sumr /= linear_sumlz /= scaler_suml.
apply: eq_bigr=>z _.
case: (_ == _); first exact: (@transfer_paired_encoded_branch_ref R U z x).
by rewrite comp_so0r comp_so0l scale0r.
Qed.

Theorem transfer_isq_total_gated_decoded_channel U s :
  sum (fun out => transfer_paired_decode_ref R :o
    formso (@transfer_paired_encoded_gate_ref R U) :o
      transfer_isq_reference_kernel s out :o formso (transfer_paired_resource_ref R)) =
        formso U.
Proof.
rewrite (eq_sum (transfer_isq_gated_decoded_kernel U s)).
exact: transfer_isq_weighted_value_total.
Qed.

Theorem transfer_isq_cq_reference s out (rho : 'End(logical)) :
  transfer_paired_decode_ref R
    (transfer_isq_reference_kernel s out (formso (transfer_paired_resource_ref R) rho)) =
      transfer_isq_outcome_weight s out *: rho.
Proof. by rewrite -!comp_soE transfer_isq_decoded_kernel scale_soE id_soE. Qed.

Theorem transfer_isq_reduced_cq_reference s out (rho : 'End(logical)) :
  transfer_paired_data_output_ref R
    (transfer_isq_reference_kernel s out (formso (transfer_paired_resource_ref R) rho)) =
      transfer_isq_outcome_weight s out *: discard_old_destination_ref R rho.
Proof.
by rewrite /transfer_paired_data_output_ref comp_soE transfer_isq_cq_reference linearZ.
Qed.

Theorem transfer_isq_total_cq_reference s (rho : 'End(logical)) :
  sum (fun out => transfer_paired_decode_ref R
    (transfer_isq_reference_kernel s out (formso (transfer_paired_resource_ref R) rho))) = rho.
Proof.
rewrite (eq_sum (fun out => transfer_isq_cq_reference s out rho)).
exact: transfer_isq_weighted_value_total.
Qed.

Theorem transfer_isq_total_reduced_cq_reference s (rho : 'End(logical)) :
  sum (fun out => transfer_paired_data_output_ref R
    (transfer_isq_reference_kernel s out (formso (transfer_paired_resource_ref R) rho))) =
      discard_old_destination_ref R rho.
Proof.
rewrite (eq_sum (fun out => transfer_isq_reduced_cq_reference s out rho)).
exact: transfer_isq_weighted_value_total.
Qed.

Theorem transfer_isq_correlated_cq_reference (d : CL.store -> 'End(logical)) out :
  sum (fun s => transfer_paired_decode_ref R
    (transfer_isq_reference_kernel s out (formso (transfer_paired_resource_ref R) (d s)))) =
      sum (fun s => transfer_isq_outcome_weight s out *: d s).
Proof. by apply: eq_sum=>s; rewrite transfer_isq_cq_reference. Qed.

Theorem transfer_isq_correlated_reduced_cq_reference (d : CL.store -> 'End(logical)) out :
  sum (fun s => transfer_paired_data_output_ref R
    (transfer_isq_reference_kernel s out (formso (transfer_paired_resource_ref R) (d s)))) =
      sum (fun s => transfer_isq_outcome_weight s out *: discard_old_destination_ref R (d s)).
Proof. by apply: eq_sum=>s; rewrite transfer_isq_reduced_cq_reference. Qed.

Theorem transfer_isq_total_correlated_cq_reference
    (d : {summable CL.store -> 'End(logical)}) :
  sum (fun out => sum (fun s => transfer_paired_decode_ref R
    (transfer_isq_reference_kernel s out
      (formso (transfer_paired_resource_ref R) (d s))))) = sum d.
Proof.
under eq_sum=>out do rewrite transfer_isq_correlated_cq_reference.
exact: transfer_isq_total_correlated_value.
Qed.
End Reference.

Theorem transfer_isq_reference_kernel_lifted (T : qType)
    (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) T)) s out :
  ClassicalSemantics.denote (successful_sequentialize
    (paired (transfer_isq_sender (first_register (first_register q)))
      (transfer_receiver (second_register (first_register q))))) s out =
        transfer_register_channel q
          (@transfer_isq_reference_kernel (eval_qtype T) s out).
Proof.
rewrite transfer_isq_source_denote /transfer_isq_reference_kernel linear_sum /=.
under [RHS]eq_bigr=>x _ do rewrite linear_sum /=.
apply: eq_bigr=>x _; apply: eq_bigr=>z _.
rewrite /point; case: (_ == _); last by rewrite linear0.
by rewrite transfer_register_channel_form transfer_physical_branchE
  register_action_left /transfer_paired_branch_ref.
Qed.
End DistributedQFTISQTransfer.
