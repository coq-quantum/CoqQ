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

Module DistributedProtocolQuantum.
Local Notation C := hermitian.C.

Definition projector (b : bool) : 'End('Hs bool) := [> ''b; ''b <].
Definition pauli_x (b : bool) : 'FU('Hs bool) :=
  if b then [unitary of PauliX] else (\1 : 'FU('Hs bool)).
Definition pauli_z (b : bool) : 'FU('Hs bool) :=
  if b then [unitary of PauliZ] else (\1 : 'FU('Hs bool)).

Lemma projector_basis b c : projector b ''c = (b == c)%:R *: ''b.
Proof. by rewrite /projector outpE onb_dot. Qed.

Lemma pauli_x_basis b c : pauli_x b ''c = ''(b (+) c).
Proof. by case: b=>/=; rewrite /pauli_x /= ?PauliX_cb ?lfunE. Qed.

Lemma pauli_z_basis b c : pauli_z b ''c = (-1)^(b && c) *: ''c.
Proof. by case: b=>/=; rewrite /pauli_z /= ?PauliZ_cb ?lfunE ?expr0z ?scale1r. Qed.

Lemma measured_hadamard b c :
  projector b (Hadamard ''c) = ((-1)^(b && c) / sqrtC 2%:R) *: ''b.
Proof. by rewrite /projector outpE Hadamard_cb dotp_cbpm. Qed.

Definition teleport_embed (a b : bool) : 'Hom('Hs bool, 'Hs ((bool * bool) * bool)%type) :=
  \sum_(c : bool) [> (''a ⊗t ''b) ⊗t ''c; ''c <].

Definition teleport_resource : 'Hom('Hs bool, 'Hs ((bool * bool) * bool)%type) :=
  (sqrtC 2%:R)^-1 *:
    \sum_(c : bool) [> ((''c ⊗t '0) ⊗t '0) + ((''c ⊗t '1) ⊗t '1); ''c <].

Lemma teleport_embed_basis a b c : teleport_embed a b ''c = (''a ⊗t ''b) ⊗t ''c.
Proof.
rewrite /teleport_embed sum_lfunE (bigD1 c) //= big1.
- by move=>j /negPf Ejc; rewrite outpE onb_dot Ejc scale0r.
- by rewrite outpE ns_dot scale1r addr0.
Qed.

Lemma teleport_resource_basis c :
  teleport_resource ''c = (sqrtC 2%:R)^-1 *:
    (((''c ⊗t '0) ⊗t '0) + ((''c ⊗t '1) ⊗t '1)).
Proof.
rewrite /teleport_resource lfunE /= sum_lfunE (bigD1 c) //= big1.
- by move=>j /negPf Ejc; rewrite outpE onb_dot Ejc scale0r.
- by rewrite outpE ns_dot scale1r addr0.
Qed.

Definition teleport_branch z x : 'End('Hs ((bool * bool) * bool)%type) :=
  ((projector z ⊗f projector x) \o
    (Hadamard ⊗f (\1 : 'End('Hs bool))) \o CNOT) ⊗f
  (pauli_z z \o pauli_x x).

Lemma teleport_branch_correct z x :
  teleport_branch z x \o teleport_resource = 2%:R^-1 *: teleport_embed z x.
Proof.
apply/(intro_onb t2tv)=>c /=.
rewrite /teleport_branch !lfunE /= teleport_resource_basis linearZ /= linearD /=.
rewrite !tentf_apply !lfunE /=.
rewrite !CNOT_cb.
rewrite !lfunE /= !tentf_apply !lfunE /=.
rewrite !measured_hadamard !projector_basis !pauli_x_basis !pauli_z_basis
  !linearZr /= !linearZl /= !scalerA teleport_embed_basis.
case: z; case: x; case: c=>/=;
rewrite ?eqxx ?expr0z ?expr1z ?mul1r ?mulN1r ?scale0r ?scale1r
  ?addr0 ?add0r ?scalerN ?opprK ?divc_simp
  ?oppr0 ?mul0r ?scale0r ?addr0 ?add0r scalerA -invfM -expr2 sqrtCK.
all: by [].
Qed.

Definition remote_embed (x z : bool) :
    'Hom('Hs (bool * bool)%type, 'Hs ((bool * bool) * (bool * bool))%type) :=
  \sum_(ij : bool * bool) [> (''ij.1 ⊗t ''x) ⊗t (''z ⊗t ''ij.2); ''ij <].

Lemma remote_embed_basis x z b c :
  remote_embed x z ''(b,c) = (''b ⊗t ''x) ⊗t (''z ⊗t ''c).
Proof.
rewrite /remote_embed sum_lfunE (bigD1 (b,c)) //= big1.
- by move=>j /negPf Ejc; rewrite outpE onb_dot Ejc scale0r.
- by rewrite outpE ns_dot scale1r addr0.
Qed.

Definition remote_resource := (sqrtC 2%:R)^-1 *:
  (remote_embed false false + remote_embed true true).

Lemma remote_resource_basis b c :
  remote_resource ''(b,c) = (sqrtC 2%:R)^-1 *:
    (((''b ⊗t '0) ⊗t ('0 ⊗t ''c)) + ((''b ⊗t '1) ⊗t ('1 ⊗t ''c))).
Proof. by rewrite /remote_resource lfunE /= lfunE /= !remote_embed_basis. Qed.

Definition remote_branch x z : 'End('Hs ((bool * bool) * (bool * bool))%type) :=
  (((pauli_z z) ⊗f projector x) \o CNOT) ⊗f
  ((projector z ⊗f pauli_x x) \o (Hadamard ⊗f (\1 : 'End('Hs bool))) \o CNOT).

Lemma remote_branch_correct x z :
  remote_branch x z \o remote_resource =
    ((-1)^(x && z) / 2%:R) *: (remote_embed x z \o CNOT).
Proof.
apply/(intro_onb t2tv)=>[[b c]] /=.
rewrite [LHS]comp_lfunE [RHS]scale_lfunE [in RHS]comp_lfunE.
rewrite [in RHS](esym (tentv_t2tv b c)) CNOT_cb tentv_t2tv remote_embed_basis.
rewrite remote_resource_basis /remote_branch linearZ /= linearD /=.
rewrite !tentf_apply !lfunE /= !CNOT_cb.
rewrite !lfunE /= !tentf_apply !lfunE /=.
rewrite !measured_hadamard !projector_basis !pauli_x_basis !pauli_z_basis
  !linearZr /= !linearZl /= !scalerA.

case: x; case: z; case: b; case: c=>/=;
rewrite ?eqxx ?expr0z ?expr1z ?mul1r ?mulN1r ?scale0r ?scale1r
  ?addr0 ?add0r ?scalerN ?opprK ?divc_simp.
all: by rewrite ?mul0r ?scale0r ?addr0 ?add0r !linearZr /= !scalerA
  ?mulN1r ?mul1r ?mulr1 ?mulrN ?mulNr ?opprK -invfM -expr2 sqrtCK.
Qed.

End DistributedProtocolQuantum.
