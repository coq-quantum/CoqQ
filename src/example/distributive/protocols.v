(* Distributive: protocols. See README.md and PROOF_NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From mathcomp.classical Require Import boolp classical_sets functions.
From quantum Require Import qtype.
From quantum Require Import hspace_extra.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From Stdlib Require Import String.
From quantum.example.distributive Require Import language operational confluence semantics sequentialization hoare auxiliary.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module DistributedProtocolQuantum.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
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


Module DistributedProtocolEffect.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Lemma effect_saturated (U : chsType) (A : 'FO(U)) (v : U) :
  [< v; v >] = 1 -> [< v; A v >] = 1 -> A v = v.
Proof.
move=>Hnorm Hv.
have Hzero : [< (v : U); (cplmt A) v >] = 0.
  by rewrite /cplmt lfunE /= id_lfunE opp_lfunE dotpBr Hnorm Hv subrr.
have Hz := psdf_dot_eq0P Hzero.
move: Hz; rewrite /cplmt lfunE /= id_lfunE opp_lfunE.
by move=>/subr0_eq /esym.
Qed.

Lemma effect_contains_state (U : chsType) (A : 'FO(U)) (v : U) :
  [< v; v >] = 1 -> [< v; A v >] = 1 -> [> (v : U); v <] ⊑ (A : 'End(U)).
Proof.
move=>Hnorm Hv.
have Av := effect_saturated Hnorm Hv.
have AP : (A : 'End(U)) \o [> (v : U); v <] = [> (v : U); v <].
  by rewrite -outp_complV Av.
have PA : [> (v : U); v <] \o (A : 'End(U)) = [> (v : U); v <].
  by rewrite -(hermf_adjE A) -outp_comprV Av.
have PP : [> (v : U); v <] \o [> (v : U); v <] = [> (v : U); v <].
  by rewrite outp_comp Hnorm scale1r.
have H := gef0_formfV (cplmt [> (v : U); v <]) (obsf_ge0 A).
rewrite /cplmt adjfB adjf1 adj_outp !linearBr /= !linearBl /=
  !comp_lfun1l !comp_lfun1r AP PA PP in H.
move: H.
by rewrite subrr subr0 subv_ge0.
Qed.
End DistributedProtocolEffect.


Module DistributedProtocolProcesses.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization.
Local Open Scope ring_scope.
Local Open Scope string_scope.

Definition xA : CL.variable (QType QBool) := CVar (QType QBool) "Alice" "x".
Definition zA : CL.variable (QType QBool) := CVar (QType QBool) "Alice" "z".
Definition stageA : CL.variable CL.Integer := CVar CL.Integer "Alice" "stage".
Definition xB : CL.variable (QType QBool) := CVar (QType QBool) "Bob" "x".
Definition zB : CL.variable (QType QBool) := CVar (QType QBool) "Bob" "z".
Definition stageB : CL.variable CL.Integer := CVar CL.Integer "Bob" "stage".

Definition first_register u v (q : wf_qreg (QPair u v)) : wf_qreg u :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid q)).
Definition second_register u v (q : wf_qreg (QPair u v)) : wf_qreg v :=
  WF_QReg (QRegAuto.valid_qreg_snd (qreg_is_valid q)).

Definition round_bit (i : 'I_2) := i == ord0.
Lemma round_bit_inj : injective round_bit.
Proof.
by move=>[[|[|i]] Hi] [[|[|j]] Hj] //= _; apply: val_inj.
Qed.

Definition conditional (e : expression bool) (yes no : statement) :=
  Alternative (fun i : 'I_2 =>
    CL.EApp (CL.EConst (fun b : bool => b == (round_bit i))) e)
    (fun i => if (round_bit i) then yes else no).

Lemma conditional_wf e yes no :
  statement_wf yes -> statement_wf no -> statement_wf (conditional e yes no).
Proof.
move=>Hy Hn; split.
- move=>s i j /= /eqP Ei /eqP Ej; apply: round_bit_inj.
  exact: eq_trans (esym Ei) Ej.
- by move=>i; case: ((round_bit i)).
Qed.

Definition stage_guard (stage : CL.variable CL.Integer) (i : 'I_2) :=
  CL.EApp (CL.EConst (fun k : int => k == Posz i)) (CL.EVar stage).

Lemma stage_guard_exclusive stage : exclusive (stage_guard stage).
Proof.
move=>s i j /= /eqP Ei /eqP Ej.
have E : Posz i = Posz j := eq_trans (esym Ei) Ej.
by apply: val_inj; case: E.
Qed.

Definition set_stage (stage : CL.variable CL.Integer) (i : nat) := Atomic (AAssign stage (CL.EConst (Posz i))).
Definition gate t (q : wf_qreg t) (U : 'FU('Ht t)) :=
  Atomic (AUnitary q (CL.EConst U)).
Definition measure (q : wf_qreg QBool) (x : CL.variable (QType QBool)) :=
  Atomic (AMeasure x q (CL.EConst [QM of @tmeas bool])).
Definition correct (q : wf_qreg QBool) (x : CL.variable (QType QBool))
    (U : 'FU('Hs bool)) :=
  conditional (CL.EVar x) (gate q U) (Atomic ASkip).

Lemma correct_wf q x U : statement_wf (correct q x U).
Proof. by apply: conditional_wf. Qed.

Definition two_round (init : statement) stage io body :=
  Process init (@stage_guard stage) io body.

Lemma two_round_wf init stage io body : statement_wf init ->
  (forall i, statement_wf (body i)) -> process_wf (two_round init stage io body).
Proof. by move=>Hi Hb; split=>//; split=>//; exact: stage_guard_exclusive. Qed.

Definition teleport_alice (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (gate (first_register q) [unitary of Hadamard])
    (Sequence (measure (first_register q) zA)
    (Sequence (measure (second_register q) xA) (set_stage stageA 0)))))
    stageA
    (fun i => if i == ord0 then Output "c" (CL.EVar xA) else Output "d" (CL.EVar zA))
    (fun i => set_stage stageA i.+1).

Definition teleport_bob (q : wf_qreg QBool) : process :=
  two_round (set_stage stageB 0) stageB
    (fun i => if i == ord0 then Input "c" xB else Input "d" zB)
    (fun i => Sequence (set_stage stageB i.+1)
      (if i == ord0 then correct q xB [unitary of PauliX]
       else correct q zB [unitary of PauliZ])).

Definition remote_alice (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (measure (second_register q) xA) (set_stage stageA 0))) stageA
    (fun i => if i == ord0 then Output "c" (CL.EVar xA) else Input "d" zA)
    (fun i => Sequence (set_stage stageA i.+1)
      (if i == ord0 then Atomic ASkip
       else correct (first_register q) zA [unitary of PauliZ])).

Definition remote_bob (q : wf_qreg (QPair QBool QBool)) : process :=
  two_round
    (Sequence (gate q [unitary of CNOT])
    (Sequence (gate (first_register q) [unitary of Hadamard])
    (Sequence (measure (first_register q) zB) (set_stage stageB 0)))) stageB
    (fun i => if i == ord0 then Input "c" xB else Output "d" (CL.EVar zB))
    (fun i => Sequence (set_stage stageB i.+1)
      (if i == ord0 then correct (second_register q) xB [unitary of PauliX]
       else Atomic ASkip)).

Lemma teleport_alice_wf q : process_wf (teleport_alice q).
Proof. by apply: two_round_wf=>//=; repeat split. Qed.
Lemma teleport_bob_wf q : process_wf (teleport_bob q).
Proof.
apply: two_round_wf=>//= i; split=>//.
by case: (i == ord0); apply: correct_wf.
Qed.
Lemma remote_alice_wf q : process_wf (remote_alice q).
Proof.
apply: two_round_wf; first by repeat split.
move=>i; split=>//; case: (i == ord0)=>//; exact: correct_wf.
Qed.
Lemma remote_bob_wf q : process_wf (remote_bob q).
Proof.
apply: two_round_wf; first by repeat split.
move=>i; split=>//; case: (i == ord0)=>//; exact: correct_wf.
Qed.

Lemma correct_finite q x U : finite_set (statement_reads (correct q x U)).
Proof.
rewrite /correct /conditional /=.
apply: bigcup_finite; first exact: finite_finset.
move=>i _; rewrite finite_setU; split.
- rewrite /expression_reads /CL.EApp /CL.EConst /CL.EVar /= ?set0U.
  exact: finite_set1.
- by case: ((round_bit i))=>/=; exact: finite_set0.
Qed.

Lemma two_round_finite init stage io body :
  finite_set (statement_reads init) ->
  (forall i, finite_set (communication_reads (io i))) ->
  (forall i, finite_set (statement_reads (body i))) ->
  finite_set (process_reads (two_round init stage io body)).
Proof.
move=>Hi Hio Hb; rewrite /process_reads /= finite_setU; split=>//.
apply: bigcup_finite; first exact: finite_finset.
move=>i _; rewrite !finite_setU; split; last exact: Hb.
split; last exact: Hio.
rewrite /expression_reads /stage_guard /CL.EApp /CL.EConst /CL.EVar /= ?set0U.
split; first exact: finite_set0.
exact: finite_set1.
Qed.

Lemma set_stage_finite stage i : finite_set (statement_reads (set_stage stage i)).
Proof. rewrite /set_stage /= setU0; exact: finite_set1. Qed.

Lemma gate_finite t (q : wf_qreg t) U : finite_set (statement_reads (gate q U)).
Proof. exact: finite_set0. Qed.

Lemma measure_finite q x : finite_set (statement_reads (measure q x)).
Proof. rewrite /measure /= setU0; exact: finite_set1. Qed.

Lemma teleport_alice_finite q : finite_set (process_reads (teleport_alice q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; exact: set_stage_finite.
Qed.

Lemma teleport_bob_finite q : finite_set (process_reads (teleport_bob q)).
Proof.
apply: two_round_finite; first exact: set_stage_finite.
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: correct_finite].
Qed.

Lemma remote_alice_finite q : finite_set (process_reads (remote_alice q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: correct_finite].
Qed.

Lemma remote_bob_finite q : finite_set (process_reads (remote_bob q)).
Proof.
apply: two_round_finite.
- rewrite /= !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: measure_finite | exact: set_stage_finite].
- move=>i; case: (i == ord0)=>/=; exact: finite_set1.
- move=>i; case: (i == ord0)=>/=; rewrite !finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 | exact: correct_finite].
Qed.
End DistributedProtocolProcesses.


Module DistributedProtocolState.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
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


Module DistributedProtocolExecution.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import ClassicalDeterministic ClassicalAlgorithmSemantics.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition round_one : 'I_2 := @Ordinal 2 1 (erefl true).
Lemma enum_two : enum 'I_2 = [:: ord0; round_one].
Proof.
rewrite enum_ordSl enum_ordSl enum_ord0 /=.
by congr [:: _; _]; apply: val_inj.
Qed.

Lemma different_channel_effect a b : channel a != channel b ->
  communication_effect a b = None.
Proof.
move=>H; case E: (communication_effect a b)=>[effect|] //.
have M := effect_matches E.
by case: M H=>t c x e; rewrite eqxx.
Qed.

Definition paired (alice bob : process) (i : 'I_2) :=
  if i == ord0 then alice else bob.
Definition synchronized_guard (i : 'I_2) :=
  guard_and (stage_guard stageA i) (stage_guard stageB i).

Definition teleport_rendezvous (qb : wf_qreg QBool) (i : 'I_2) : expression bool * CL.command :=
  (synchronized_guard i,
   CL.Sequence (CL.Assign (if i == ord0 then xB else zB)
     (CL.EVar (if i == ord0 then xA else zA)))
   (CL.Sequence (translate_statement (set_stage stageA i.+1))
     (translate_statement (Sequence (set_stage stageB i.+1)
       (if i == ord0 then correct qb xB [unitary of PauliX]
        else correct qb zB [unitary of PauliZ]))))).

Lemma teleport_rendezvousE qa qb :
  rendezvous_commands (paired (teleport_alice qa) (teleport_bob qb)) =
  [:: teleport_rendezvous qb ord0; teleport_rendezvous qb round_one].
Proof.
Arguments communication_effect _ _ : simpl never.
rewrite /rendezvous_commands !enum_two /= /paired /=
  /rendezvous_command /= !enum_two /=.
rewrite (matching_effect (MatchOutput "c" xB (CL.EVar xA)))
  (matching_effect (MatchOutput "d" zB (CL.EVar zA)))
  !different_channel_effect //=.
Qed.

Definition remote_rendezvous
    (qa qb : wf_qreg (QPair QBool QBool)) (i : 'I_2) : expression bool * CL.command :=
  (synchronized_guard i,
   CL.Sequence (if i == ord0 then CL.Assign xB (CL.EVar xA)
     else CL.Assign zA (CL.EVar zB))
   (CL.Sequence
     (translate_statement (Sequence (set_stage stageA i.+1)
       (if i == ord0 then Atomic ASkip
        else correct (first_register qa) zA [unitary of PauliZ])))
     (translate_statement (Sequence (set_stage stageB i.+1)
       (if i == ord0 then correct (second_register qb) xB [unitary of PauliX]
        else Atomic ASkip))))).

Lemma remote_rendezvousE qa qb :
  rendezvous_commands (paired (remote_alice qa) (remote_bob qb)) =
  [:: remote_rendezvous qa qb ord0; remote_rendezvous qa qb round_one].
Proof.
rewrite /rendezvous_commands !enum_two /= /paired /=
  /rendezvous_command /= !enum_two /=.
rewrite (matching_effect (MatchOutput "c" xB (CL.EVar xA)))
  (matching_effect (MatchInput "d" zA (CL.EVar zB))).
by rewrite /communication_effect /= /remote_rendezvous.
Qed.

Lemma correct_execution q x U s :
  execution (translate_statement (correct q x U)) s s
    (if (s.[x])%M then liftfso (formso (tf2f q q U)) else \:1).
Proof.
rewrite /correct /conditional /= enum_two /= /conditional_chain /=.
case E: ((s.[x])%M).
- apply: RunIfTrue; first by rewrite /= E.
  exact: RunUnitary.
- apply: RunIfFalse; first by rewrite /= E.
  apply: RunIfTrue; first by rewrite /= E.
  exact: RunSkip.
Qed.

Definition two_round_loop (r : 'I_2 -> expression bool * CL.command) :=
  CL.While (guards_any [:: (r ord0).1; (r round_one).1])
    (conditional_chain [:: r ord0; r round_one]).

Lemma two_round_loop_execution r s t u F G :
  eval (r ord0).1 s = true ->
  eval (r ord0).1 t = false -> eval (r round_one).1 t = true ->
  eval (r ord0).1 u = false -> eval (r round_one).1 u = false ->
  execution (r ord0).2 s t F -> execution (r round_one).2 t u G ->
  execution (two_round_loop r) s u (G :o F).
Proof.
move=>Es Et0 Et1 Eu0 Eu1 D0 D1.
have Dbody0 : execution (conditional_chain [:: r ord0; r round_one]) s t F.
  apply: RunIfTrue D0; exact: Es.
have Dbody1 : execution (conditional_chain [:: r ord0; r round_one]) t u G.
  apply: RunIfFalse Et0 _; exact: RunIfTrue Et1 D1.
have Dstop : execution (two_round_loop r) u u \:1.
  apply: RunWhileFalse; by rewrite /= /guards_any /= Eu0 Eu1.
have Dnext : execution (two_round_loop r) t u G.
  rewrite -(comp_so1l G); apply: RunWhileTrue Dbody1 Dstop.
  by rewrite /= /guards_any /= Et0 Et1.
apply: RunWhileTrue Dbody0 Dnext.
by rewrite /= /guards_any /= Es.
Qed.

Definition synchronized_at (s : CL.store) (n : nat) :=
  (s.[stageA])%M = Posz n /\ (s.[stageB])%M = Posz n.

Lemma synchronized_guardE i s n : synchronized_at s n ->
  eval (synchronized_guard i) s = (n == val i).
Proof.
move=>[Ha Hb]; rewrite /synchronized_guard /guard_and /stage_guard /= Ha Hb.
by rewrite eqz_nat andbb.
Qed.

Definition teleport_step_store (i : 'I_2) (s : CL.store) :=
  ((s.[(if i == ord0 then xB else zB) <-
       (s.[(if i == ord0 then xA else zA)])]).[stageA <- Posz i.+1]).[stageB <- Posz i.+1]%M.

Definition correction_action (q : wf_qreg QBool) (U : 'FU('Hs bool)) (b : bool) :=
  if b then liftfso (formso (tf2f q q U)) else \:1.

Definition teleport_step_action (q : wf_qreg QBool) (i : 'I_2) (s : CL.store) :=
  if i == ord0 then correction_action q [unitary of PauliX] (s.[xA])%M
  else correction_action q [unitary of PauliZ] (s.[zA])%M.

Lemma teleport_step_synchronized i s :
  synchronized_at (teleport_step_store i s) i.+1.
Proof.
split; rewrite /teleport_step_store; last exact: get_set_eq.
by rewrite get_set_nex // get_set_eq.
Qed.

Lemma teleport_step_execution qb i s :
  execution (teleport_rendezvous qb i).2 s (teleport_step_store i s)
    (teleport_step_action qb i s).
Proof.
rewrite /teleport_rendezvous /teleport_step_action /teleport_step_store /=.
case Ei: (i == ord0).
- have D := RunSequence (RunAssign xB (CL.EVar xA) s)
    (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
    (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
      (correct_execution qb xB [unitary of PauliX] _))).
  rewrite !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
- have D := RunSequence (RunAssign zB (CL.EVar zA) s)
    (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
    (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
      (correct_execution qb zB [unitary of PauliZ] _))).
  rewrite !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
Qed.

Definition teleport_final_store s :=
  teleport_step_store round_one (teleport_step_store ord0 s).

Definition teleport_loop_action qb s :=
  teleport_step_action qb round_one (teleport_step_store ord0 s) :o
    teleport_step_action qb ord0 s.

Lemma teleport_loop_execution qb s : synchronized_at s 0 ->
  execution (two_round_loop (teleport_rendezvous qb)) s
    (teleport_final_store s) (teleport_loop_action qb s).
Proof.
move=>Hs; apply: two_round_loop_execution.
- exact: synchronized_guardE Hs.
- exact: synchronized_guardE (teleport_step_synchronized ord0 s).
- exact: synchronized_guardE (teleport_step_synchronized ord0 s).
- exact: synchronized_guardE (teleport_step_synchronized round_one _).
- exact: synchronized_guardE (teleport_step_synchronized round_one _).
- exact: teleport_step_execution.
- exact: teleport_step_execution.
Qed.

Lemma teleport_loop_actionE qb s :
  teleport_loop_action qb s =
    correction_action qb [unitary of PauliZ] (s.[zA])%M :o
    correction_action qb [unitary of PauliX] (s.[xA])%M.
Proof.
change (correction_action qb [unitary of PauliZ]
    ((teleport_step_store ord0 s).[zA])%M :o
    correction_action qb [unitary of PauliX] (s.[xA])%M =
    correction_action qb [unitary of PauliZ] (s.[zA])%M :o
    correction_action qb [unitary of PauliX] (s.[xA])%M).
by rewrite /teleport_step_store !get_set_nex.
Qed.
End DistributedProtocolExecution.


Module DistributedProtocolOwnership.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedFootprint DistributedProtocolProcesses.
Local Open Scope ring_scope.
Local Open Scope string_scope.

Definition owned (who : string) : set classical_name := fun k => k.2.1 = who.
Definition statement_owned who s := (statement_reads s `<=` owned who)%classic.
Definition process_owned who p := (process_reads p `<=` owned who)%classic.

Lemma sequence_owned who s t : statement_owned who s -> statement_owned who t ->
  statement_owned who (Sequence s t).
Proof. by move=>Hs Ht k [H|H]; [apply: Hs|apply: Ht]. Qed.
Lemma skip_owned who : statement_owned who (Atomic ASkip).
Proof. by []. Qed.
Lemma gate_owned who t (q : wf_qreg t) U : statement_owned who (gate q U).
Proof. by []. Qed.
Lemma set_stage_owned who stage i : owned who (name_of stage) ->
  statement_owned who (set_stage stage i).
Proof. by move=>H k [->|[]]. Qed.
Lemma measure_owned who q x : owned who (name_of x) ->
  statement_owned who (measure q x).
Proof. by move=>H k [->|[]]. Qed.
Lemma correct_owned who q x U : owned who (name_of x) ->
  statement_owned who (correct q x U).
Proof.
move=>Hx k [i _ [H|H]].
- by case: H=>[[]|->].
- by move: H; rewrite /correct /conditional /=; case: (round_bit i).
Qed.

Lemma two_round_owned who init stage io body :
  statement_owned who init -> owned who (name_of stage) ->
  (forall i, (communication_reads (io i) `<=` owned who)%classic) ->
  (forall i, statement_owned who (body i)) ->
  process_owned who (two_round init stage io body).
Proof.
move=>Hi Hstage Hio Hb k [H|[i _ [[H|H]|H]]].
- exact: Hi.
- by case: H=>[[]|->].
- exact: Hio i k H.
- exact: Hb i k H.
Qed.

Lemma teleport_alice_owned q : process_owned "Alice" (teleport_alice q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned; first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- by move=>i; apply: set_stage_owned.
Qed.
Lemma teleport_bob_owned q : process_owned "Bob" (teleport_bob q).
Proof.
apply: two_round_owned=>//.
- by apply: set_stage_owned.
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; apply: sequence_owned; first by apply: set_stage_owned.
  by case: (i == ord0); apply: correct_owned.
Qed.
Lemma remote_alice_owned q : process_owned "Alice" (remote_alice q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned; first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; apply: sequence_owned; first by apply: set_stage_owned.
  by case: (i == ord0); [exact: skip_owned|apply: correct_owned].
Qed.
Lemma remote_bob_owned q : process_owned "Bob" (remote_bob q).
Proof.
apply: two_round_owned=>//.
- repeat apply: sequence_owned; first [exact: gate_owned | by apply: measure_owned | by apply: set_stage_owned].
- by move=>i; case: (i == ord0)=>k ->.
- move=>i; apply: sequence_owned; first by apply: set_stage_owned.
  by case: (i == ord0); [apply: correct_owned|exact: skip_owned].
Qed.

Lemma first_register_subset u v (q : wf_qreg (QPair u v)) :
  (mset (first_register q) \subset mset q)%SET.
Proof. rewrite mset_pairV; exact: finset.subsetUl. Qed.
Lemma second_register_subset u v (q : wf_qreg (QPair u v)) :
  (mset (second_register q) \subset mset q)%SET.
Proof. rewrite mset_pairV; exact: finset.subsetUr. Qed.

Lemma correct_quantum q x U : statement_quantum (correct q x U) \subset mset q.
Proof.
apply/bigcupsP=>i _; case: (round_bit i)=>/=;
  [exact: fintype.subxx | exact: finset.sub0set].
Qed.

Lemma teleport_alice_quantum q : process_quantum (teleport_alice q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset !fintype.subxx !finset.sub0set
  /= !first_register_subset !second_register_subset /=.
apply/bigcupsP=>i _; exact: finset.sub0set.
Qed.
Lemma teleport_bob_quantum q : process_quantum (teleport_bob q) \subset mset q.
Proof.
rewrite /process_quantum /= finset.set0U; apply/bigcupsP=>i _; rewrite /= finset.set0U.
by case: (i == ord0); apply: correct_quantum.
Qed.
Lemma remote_alice_quantum q : process_quantum (remote_alice q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset; apply/andP; split.
- apply/andP; split=>//; apply/andP; split; [exact: second_register_subset|by rewrite finset.sub0set].
- apply/bigcupsP=>i _; rewrite /= finset.set0U; case: (i == ord0)=>/=; first by rewrite finset.sub0set.
  exact: fintype.subset_trans (@correct_quantum (first_register q) zA [unitary of PauliZ]) (@first_register_subset _ _ q).
Qed.
Lemma remote_bob_quantum q : process_quantum (remote_bob q) \subset mset q.
Proof.
rewrite /process_quantum /= !finset.subUset; apply/andP; split.
- apply/andP; split=>//; apply/andP; split; first exact: first_register_subset.
  apply/andP; split; [exact: first_register_subset|by rewrite finset.sub0set].
- apply/bigcupsP=>i _; rewrite /= finset.set0U; case: (i == ord0)=>/=; last by rewrite finset.sub0set.
  exact: fintype.subset_trans (@correct_quantum (second_register q) xB [unitary of PauliX]) (@second_register_subset _ _ q).
Qed.

Definition pair_processes (alice bob : process) (i : 'I_2) :=
  if i == ord0 then alice else bob.

Lemma pair_point_to_point alice bob : point_to_point (pair_processes alice bob).
Proof.
move=>[[|[|i]] Hi] [[|[|j]] Hj] [[|[|k]] Hk] //=;
  rewrite ?eqxx //; by [].
Qed.

Lemma pair_private alice bob (QA QB : {set mlab}) :
  process_owned "Alice" alice -> process_owned "Bob" bob ->
  process_quantum alice \subset QA -> process_quantum bob \subset QB ->
  [disjoint QA & QB] -> pairwise_private (pair_processes alice bob).
Proof.
move=>Ha Hb Hqa Hqb Hdis.
have Hab k : process_reads alice k -> k \notin process_changes bob.
  move=>Hk; apply/negP=>Hj; have Ea := Ha _ Hk.
  have Eb := Hb _ (process_changes_reads Hj).
  by move: Ea; rewrite /owned Eb.
have Hba k : process_reads bob k -> k \notin process_changes alice.
  move=>Hk; apply/negP=>Hj; have Eb := Hb _ Hk.
  have Ea := Ha _ (process_changes_reads Hj).
  by move: Eb; rewrite /owned Ea.
have Hq : [disjoint process_quantum alice & process_quantum bob].
  exact: fintype.disjointW Hqa Hqb Hdis.
move=>i j Hij; rewrite /pair_processes.
case Ei: (i == ord0); case Ej: (j == ord0).
- have Eij : i = j := round_bit_inj (eq_trans Ei (esym Ej)).
  by subst j; rewrite eqxx in Hij.
- split=>//; apply/eqP; exact: finset.disjoint_setI0 Hq.
- split=>//; apply/eqP; rewrite finset.setIC; exact: finset.disjoint_setI0 Hq.
- have Eij : i = j := round_bit_inj (eq_trans Ei (esym Ej)).
  by subst j; rewrite eqxx in Hij.
Qed.

Definition teleport_program (qa : wf_qreg (QPair QBool QBool))
    (qb : wf_qreg QBool) (Hdis : [disjoint mset qa & mset qb]) : program.
Proof.
apply: (@Program 2 (pair_processes (teleport_alice qa) (teleport_bob qb)) erefl).
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: teleport_alice_wf|exact: teleport_bob_wf].
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: teleport_alice_finite|exact: teleport_bob_finite].
- exact: (@pair_private (teleport_alice qa) (teleport_bob qb) (mset qa) (mset qb)
    (@teleport_alice_owned qa) (@teleport_bob_owned qb)
    (@teleport_alice_quantum qa) (@teleport_bob_quantum qb) Hdis).
- exact: pair_point_to_point.
Defined.

Definition remote_program (qa qb : wf_qreg (QPair QBool QBool))
    (Hdis : [disjoint mset qa & mset qb]) : program.
Proof.
apply: (@Program 2 (pair_processes (remote_alice qa) (remote_bob qb)) erefl).
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: remote_alice_wf|exact: remote_bob_wf].
- move=>i; rewrite /pair_processes; case: (i == ord0);
    [exact: remote_alice_finite|exact: remote_bob_finite].
- exact: (@pair_private (remote_alice qa) (remote_bob qb) (mset qa) (mset qb)
    (@remote_alice_owned qa) (@remote_bob_owned qb)
    (@remote_alice_quantum qa) (@remote_bob_quantum qb) Hdis).
- exact: pair_point_to_point.
Defined.
End DistributedProtocolOwnership.


Module DistributedProtocolLocal.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
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


Module DistributedProtocolRemoteLocal.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
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


Module DistributedProtocolRegister.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedProtocolQuantum DistributedProtocolProcesses DistributedProtocolExecution.
Import ClassicalAlgorithmSemantics ClassicalRegisterTensor.
Local Notation Hq := 'H[msys]_finset.setT.

Definition register_action u (q : wf_qreg u) (A : 'End('Ht u)) : 'SO(Hq) :=
  liftfso (formso (tf2f q q A)).

Lemma register_action1 u (q : wf_qreg u) : register_action q \1 = \:1.
Proof. by rewrite /register_action tf2f1 formso1 liftfso1. Qed.

Lemma register_action_comp u (q : wf_qreg u) A B :
  register_action q A :o register_action q B = register_action q (A \o B).
Proof. exact: register_unitary_comp. Qed.

Lemma register_action_left u v (q : wf_qreg (QPair u v)) A :
  register_action (first_register q) A = register_action q (A ⊗f \1).
Proof. exact: channel_register_left. Qed.

Lemma register_action_right u v (q : wf_qreg (QPair u v)) B :
  register_action (second_register q) B = register_action q (\1 ⊗f B).
Proof. exact: channel_register_right. Qed.

Lemma register_action_pair u v (q : wf_qreg (QPair u v)) A B :
  register_action (second_register q) B :o register_action (first_register q) A =
    register_action q (A ⊗f B).
Proof.
by rewrite register_action_left register_action_right register_action_comp
  tentf_comp comp_lfun1l comp_lfun1r.
Qed.

Lemma correction_actionX q b :
  correction_action q [unitary of PauliX] b = register_action q (pauli_x b).
Proof. by case: b=>//=; rewrite /pauli_x register_action1. Qed.

Lemma correction_actionZ q b :
  correction_action q [unitary of PauliZ] b = register_action q (pauli_z b).
Proof. by case: b=>//=; rewrite /pauli_z register_action1. Qed.

Definition teleport_physical_branch (qa : wf_qreg (QPair QBool QBool))
    (qb : wf_qreg QBool) z x :=
  (register_action qb (pauli_z z \o pauli_x x)) :o
  (register_action (second_register qa) (projector x) :o
   (register_action (first_register qa) (projector z) :o
    (register_action (first_register qa) Hadamard :o
     register_action qa CNOT))).

Lemma teleport_physical_branchE (q : wf_qreg (QPair (QPair QBool QBool) QBool)) z x :
  teleport_physical_branch (first_register q) (second_register q) z x =
    register_action q (teleport_branch z x).
Proof.
rewrite /teleport_physical_branch !(register_action_left, register_action_right)
  !register_action_comp !tentf_comp !comp_lfun1l !comp_lfun1r /teleport_branch.
by rewrite !comp_lfunA !tentf_comp !comp_lfun1l !comp_lfun1r.
Qed.

Definition remote_physical_branch (qa qb : wf_qreg (QPair QBool QBool)) x z :=
  register_action (first_register qa) (pauli_z z) :o
  (register_action (second_register qb) (pauli_x x) :o
  (register_action (first_register qb) (projector z) :o
  (register_action (first_register qb) Hadamard :o
  (register_action qb CNOT :o
  (register_action (second_register qa) (projector x) :o
   register_action qa CNOT))))).

Lemma remote_physical_branchE
    (q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool))) x z :
  remote_physical_branch (first_register q) (second_register q) x z =
    register_action q (remote_branch x z).
Proof.
rewrite /remote_physical_branch.
rewrite !(register_action_left, register_action_right) !register_action_comp.
rewrite !tentf_comp !comp_lfun1l !comp_lfun1r /remote_branch.
by rewrite !comp_lfunA !tentf_comp !comp_lfun1l !comp_lfun1r.
Qed.
End DistributedProtocolRegister.


Module DistributedProtocolSuffix.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolQuantum.
Import ClassicalDeterministic ClassicalAlgorithmSemantics.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma execution_preE total c s t F (Q : CL.store -> 'FO(Hq)) :
  execution c s t F ->
  (CQPredicate.xp total (ClassicalSemantics.denote c) Q s : 'End(Hq)) = F^*o (Q t).
Proof.
move=>D; have HF := execution_channel D.
rewrite (QChannel_BuildE HF) in D *.
exact: (execution_pre total Q D).
Qed.

Lemma teleport_terminationE qa qb s : synchronized_at s 2 ->
  eval (termination_guard (paired (teleport_alice qa) (teleport_bob qb))) s = true.
Proof.
move=>[Ea Eb].
rewrite /termination_guard !enum_two /= /paired /= !enum_two /=.
by rewrite /guards_all /guard_and /guard_not /stage_guard /= Ea Eb.
Qed.

Lemma remote_terminationE qa qb s : synchronized_at s 2 ->
  eval (termination_guard (paired (remote_alice qa) (remote_bob qb))) s = true.
Proof.
move=>[Ea Eb].
rewrite /termination_guard !enum_two /= /paired /= !enum_two /=.
by rewrite /guards_all /guard_and /guard_not /stage_guard /= Ea Eb.
Qed.

Definition remote_step_store (i : 'I_2) (s : CL.store) :=
  ((s.[(if i == ord0 then xB else zA) <-
       (s.[(if i == ord0 then xA else zB)])]).[stageA <- Posz i.+1]).[stageB <- Posz i.+1]%M.

Definition remote_step_action (qa qb : wf_qreg (QPair QBool QBool))
    (i : 'I_2) (s : CL.store) :=
  if i == ord0 then correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M
  else correction_action (first_register qa) [unitary of PauliZ] (s.[zB])%M.

Lemma remote_step_synchronized i s :
  synchronized_at (remote_step_store i s) i.+1.
Proof.
split; rewrite /remote_step_store; last exact: get_set_eq.
by rewrite get_set_nex // get_set_eq.
Qed.

Lemma remote_step_execution qa qb i s :
  execution (remote_rendezvous qa qb i).2 s (remote_step_store i s)
    (remote_step_action qa qb i s).
Proof.
rewrite /remote_rendezvous /remote_step_action /remote_step_store /=.
case Ei: (i == ord0).
- have D := RunSequence (RunAssign xB (CL.EVar xA) s)
    (RunSequence
      (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _) (RunSkip _))
      (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _)
        (correct_execution (second_register qb) xB [unitary of PauliX] _))).
  rewrite !comp_so1l !comp_so1r get_set_nex // get_set_nex // get_set_eq in D.
  exact: D.
- have D := RunSequence (RunAssign zA (CL.EVar zB) s)
    (RunSequence
      (RunSequence (RunAssign stageA (CL.EConst (Posz i.+1)) _)
        (correct_execution (first_register qa) zA [unitary of PauliZ] _))
      (RunSequence (RunAssign stageB (CL.EConst (Posz i.+1)) _) (RunSkip _))).
  rewrite !comp_so1l !comp_so1r get_set_nex // get_set_eq in D.
  exact: D.
Qed.

Definition remote_final_store s :=
  remote_step_store round_one (remote_step_store ord0 s).

Definition remote_loop_action qa qb s :=
  remote_step_action qa qb round_one (remote_step_store ord0 s) :o
    remote_step_action qa qb ord0 s.

Lemma remote_loop_execution qa qb s : synchronized_at s 0 ->
  execution (two_round_loop (remote_rendezvous qa qb)) s
    (remote_final_store s) (remote_loop_action qa qb s).
Proof.
move=>Hs; apply: two_round_loop_execution.
- exact: synchronized_guardE Hs.
- exact: synchronized_guardE (remote_step_synchronized ord0 s).
- exact: synchronized_guardE (remote_step_synchronized ord0 s).
- exact: synchronized_guardE (remote_step_synchronized round_one _).
- exact: synchronized_guardE (remote_step_synchronized round_one _).
- exact: remote_step_execution.
- exact: remote_step_execution.
Qed.

Lemma remote_loop_actionE qa qb s :
  remote_loop_action qa qb s =
    correction_action (first_register qa) [unitary of PauliZ] (s.[zB])%M :o
    correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M.
Proof.
change (correction_action (first_register qa) [unitary of PauliZ]
    ((remote_step_store ord0 s).[zB])%M :o
    correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M =
    correction_action (first_register qa) [unitary of PauliZ] (s.[zB])%M :o
    correction_action (second_register qb) [unitary of PauliX] (s.[xA])%M).
by rewrite /remote_step_store !get_set_nex.
Qed.

Definition teleport_loop_suffix qa qb :=
  CL.Sequence (two_round_loop (teleport_rendezvous qb))
    (CL.Conditional (termination_guard (paired (teleport_alice qa) (teleport_bob qb)))
      CL.Skip CL.Abort).

Lemma teleport_loop_suffix_execution qa qb s : synchronized_at s 0 ->
  execution (teleport_loop_suffix qa qb) s (teleport_final_store s)
    (teleport_loop_action qb s).
Proof.
move=>Hs; rewrite -(comp_so1l (teleport_loop_action qb s)).
apply: RunSequence (teleport_loop_execution qb Hs) _.
apply: RunIfTrue; last exact: RunSkip.
apply: teleport_terminationE; exact: teleport_step_synchronized.
Qed.

Definition remote_loop_suffix qa qb :=
  CL.Sequence (two_round_loop (remote_rendezvous qa qb))
    (CL.Conditional (termination_guard (paired (remote_alice qa) (remote_bob qb)))
      CL.Skip CL.Abort).

Lemma remote_loop_suffix_execution qa qb s : synchronized_at s 0 ->
  execution (remote_loop_suffix qa qb) s (remote_final_store s)
    (remote_loop_action qa qb s).
Proof.
move=>Hs; rewrite -(comp_so1l (remote_loop_action qa qb s)).
apply: RunSequence (remote_loop_execution qa qb Hs) _.
apply: RunIfTrue; last exact: RunSkip.
apply: remote_terminationE; exact: remote_step_synchronized.
Qed.
End DistributedProtocolSuffix.


Module DistributedProtocolRemoteOutput.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedProtocolQuantum DistributedProtocolState DistributedProtocolRemoteLocal.

Lemma remote_output_on_data v x z :
  remote_output v \o remote_embed x z =
    remote_embed x z \o [> CNOT v; CNOT v <].
Proof.
apply/lfunP=>u; rewrite [LHS]comp_lfunE /remote_output sum_lfunE
  (bigD1 (x,z)) //= big1.
- move=>[y w] /negPf H.
  rewrite outpE /remote_states remote_embed_dot.
  move: H; rewrite xpair_eqE=>->.
  by rewrite mul0r scale0r.
- by rewrite /remote_states outpE remote_embed_dot !eqxx mul1r addr0
    comp_lfunE outpE linearZ.
Qed.
End DistributedProtocolRemoteOutput.


Module DistributedProtocolPredicate.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedProtocolQuantum DistributedProtocolProcesses DistributedProtocolExecution DistributedProtocolRegister.
Local Notation Hq := 'H[msys]_finset.setT.

Definition register_predicate u (q : wf_qreg u) (P : 'End('Ht u)) :=
  liftf_lf (tf2f q q P).

Lemma register_predicate_obsE u (q : wf_qreg u) P :
  register_predicate q P \is obslf = (P \is obslf).
Proof. by rewrite /register_predicate -liftf_lf_obsE tf2f_obsE. Qed.

Lemma register_predicate_le u (q : wf_qreg u) P Q :
  register_predicate q P ⊑ register_predicate q Q = (P ⊑ Q).
Proof. by rewrite /register_predicate liftf_lf_lef tf2f_lef. Qed.

Lemma register_action_pre u (q : wf_qreg u) B P :
  (register_action q B)^*o (register_predicate q P) =
    register_predicate q ((formso B)^*o P).
Proof.
rewrite /register_action /register_predicate liftfso_dual liftfsoEf
  !dualso_formE.
by rewrite tf2f_adj !tf2f_comp.
Qed.
End DistributedProtocolPredicate.


Module DistributedProtocolRemoteSerial.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQHoare CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition remote_tail qa qb :=
  CL.Sequence (CL.Assign stageB (CL.EConst (0 : int)))
    (CL.Sequence CL.Skip (remote_loop_suffix qa qb)).

Lemma remote_tail_execution qa qb s : (s.[stageA])%M = (0 : int) ->
  execution (remote_tail qa qb) s (remote_final_store (s.[stageB <- (0 : int)])%M)
    (remote_loop_action qa qb (s.[stageB <- (0 : int)])%M).
Proof.
move=>Ha.
have Hs : synchronized_at (s.[stageB <- (0 : int)])%M 0.
  split; last exact: get_set_eq.
  by rewrite get_set_nex.
have D := RunSequence (RunAssign stageB (CL.EConst (0 : int)) s)
  (RunSequence (RunSkip _) (remote_loop_suffix_execution qa qb Hs)).
rewrite !comp_so1r in D; exact: D.
Qed.

Definition remote_serial (qa qb : wf_qreg (QPair QBool QBool)) :=
  CL.Sequence (CL.Unitary qa (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Measure xA (second_register qa) (CL.EConst [QM of @tmeas bool]))
  (CL.Sequence (CL.Assign stageA (CL.EConst (0 : int)))
  (CL.Sequence (CL.Unitary qb (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Unitary (first_register qb) (CL.EConst [unitary of Hadamard]))
  (CL.Sequence (CL.Measure zB (first_register qb) (CL.EConst [QM of @tmeas bool]))
    (remote_tail qa qb)))))).

Lemma remote_serial_preE total qa qb Q :
  pre total (successful_sequentialize (paired (remote_alice qa) (remote_bob qb))) Q =
    pre total (remote_serial qa qb) Q.
Proof.
rewrite /successful_sequentialize /sequentialize remote_rendezvousE enum_two /=.
rewrite /paired /= /remote_serial /remote_tail /remote_loop_suffix /two_round_loop.
rewrite !pre_sequence.
by [].
Qed.
End DistributedProtocolRemoteSerial.


Module DistributedProtocolSerial.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQHoare CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition stages_zero (s : CL.store) := (s.[stageA <- (0 : int)]).[stageB <- (0 : int)]%M.

Lemma stages_zero_synchronized s : synchronized_at (stages_zero s) 0.
Proof.
split; rewrite /stages_zero; last exact: get_set_eq.
by rewrite get_set_nex // get_set_eq.
Qed.

Definition teleport_tail qa qb :=
  CL.Sequence (CL.Assign stageA (CL.EConst (0 : int)))
    (CL.Sequence (CL.Sequence (CL.Assign stageB (CL.EConst (0 : int))) CL.Skip)
      (teleport_loop_suffix qa qb)).

Lemma teleport_tail_execution qa qb s :
  execution (teleport_tail qa qb) s (teleport_final_store (stages_zero s))
    (teleport_loop_action qb (stages_zero s)).
Proof.
have D := RunSequence (RunAssign stageA (CL.EConst (0 : int)) s)
  (RunSequence (RunSequence (RunAssign stageB (CL.EConst (0 : int)) _) (RunSkip _))
    (teleport_loop_suffix_execution qa qb (stages_zero_synchronized s))).
rewrite !comp_so1l !comp_so1r in D.
exact: D.
Qed.

Definition teleport_serial (qa : wf_qreg (QPair QBool QBool))
    (qb : wf_qreg QBool) :=
  CL.Sequence (CL.Unitary qa (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Unitary (first_register qa) (CL.EConst [unitary of Hadamard]))
  (CL.Sequence (CL.Measure zA (first_register qa) (CL.EConst [QM of @tmeas bool]))
  (CL.Sequence (CL.Measure xA (second_register qa) (CL.EConst [QM of @tmeas bool]))
    (teleport_tail qa qb)))).

Lemma teleport_serial_preE total qa qb Q :
  pre total (successful_sequentialize (paired (teleport_alice qa) (teleport_bob qb))) Q =
    pre total (teleport_serial qa qb) Q.
Proof.
rewrite /successful_sequentialize /sequentialize teleport_rendezvousE enum_two /=.
rewrite /paired /= /teleport_serial /teleport_tail /teleport_loop_suffix /two_round_loop.
rewrite !pre_sequence.
by [].
Qed.
End DistributedProtocolSerial.


Module DistributedProtocolPre.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum DistributedProtocolSerial DistributedProtocolRegister.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQHoare CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma unitary_pre_register total u (q : wf_qreg u) U Q s :
  (pre total (CL.Unitary q (CL.EConst U)) Q s : 'End(Hq)) =
    (register_action q U)^*o (Q s).
Proof. exact: CQPrimitive.unitary_pre. Qed.

Lemma computational_measurement_pre total (q : wf_qreg QBool)
    (x : CL.variable (QType QBool)) Q s :
  (pre total (CL.Measure x q (CL.EConst [QM of @tmeas bool])) Q s : 'End(Hq)) =
    \sum_b (register_action q (projector b))^*o (Q (s.[x <- b])%M).
Proof.
rewrite /pre CQPrimitive.measurement_pre.
apply: eq_bigr=>b _.
by rewrite /register_action liftfso_formso dualso_formE.
Qed.

Lemma teleport_tail_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (teleport_tail qa qb) (fun _ => Q) s : 'End(Hq)) =
  (register_action qb (pauli_z (s.[zA])%M \o pauli_x (s.[xA])%M))^*o Q.
Proof.
rewrite /pre (execution_preE total _ (teleport_tail_execution qa qb s))
  teleport_loop_actionE /stages_zero !get_set_nex //.
by rewrite correction_actionZ correction_actionX register_action_comp.
Qed.

Lemma teleport_serial_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (teleport_serial qa qb) (fun _ => Q) s : 'End(Hq)) =
    \sum_z \sum_x (teleport_physical_branch qa qb z x)^*o Q.
Proof.
rewrite /teleport_serial pre_sequence pre_sequence pre_sequence pre_sequence.
rewrite unitary_pre_register unitary_pre_register computational_measurement_pre.
under eq_bigr=>z _ do rewrite computational_measurement_pre.
under eq_bigr=>z _ do under eq_bigr=>x _ do
  rewrite teleport_tail_pre get_set_nex // !get_set_eq.
rewrite !linear_sum /=.
apply: eq_bigr=>z _; rewrite !linear_sum /=.
apply: eq_bigr=>x _.
by rewrite /teleport_physical_branch !dualso_comp !comp_soE.

Qed.
End DistributedProtocolPre.


Module DistributedProtocolRemotePre.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses.
Import DistributedProtocolExecution DistributedProtocolSuffix DistributedProtocolQuantum DistributedProtocolRegister DistributedProtocolPre DistributedProtocolRemoteSerial.
Import ClassicalDeterministic ClassicalAlgorithmSemantics CQHoare CQPredicate.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope string_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma remote_tail_pre total qa qb (Q : 'FO(Hq)) s :
  (s.[stageA])%M = (0 : int) ->
  (pre total (remote_tail qa qb) (fun _ => Q) s : 'End(Hq)) =
  (register_action (first_register qa) (pauli_z (s.[zB])%M) :o
   register_action (second_register qb) (pauli_x (s.[xA])%M))^*o Q.
Proof.
move=>Ha.
rewrite /pre (execution_preE total _ (remote_tail_execution qa qb Ha))
  remote_loop_actionE !get_set_nex //.
by rewrite correction_actionZ correction_actionX.
Qed.

Lemma remote_serial_pre total qa qb (Q : 'FO(Hq)) s :
  (pre total (remote_serial qa qb) (fun _ => Q) s : 'End(Hq)) =
    \sum_x \sum_z (remote_physical_branch qa qb x z)^*o Q.
Proof.
rewrite /remote_serial pre_sequence pre_sequence pre_sequence pre_sequence
  pre_sequence pre_sequence.
rewrite unitary_pre_register computational_measurement_pre linear_sum.
apply: eq_bigr=>x _.
rewrite /pre CQPrimitive.assign_pre unitary_pre_register unitary_pre_register
  computational_measurement_pre !linear_sum.
apply: eq_bigr=>z _.
rewrite remote_tail_pre.
- by rewrite get_set_nex // get_set_eq.
- rewrite get_set_eq get_set_nex // get_set_nex // get_set_eq.
  by rewrite /remote_physical_branch !dualso_comp !comp_soE.

Qed.
End DistributedProtocolRemotePre.


Module DistributedTeleportCorrectness.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses DistributedProtocolExecution DistributedProtocolQuantum DistributedProtocolState DistributedProtocolLocal DistributedProtocolEffect DistributedProtocolPredicate DistributedProtocolPre DistributedProtocolSerial DistributedProtocolRegister.
Import CQHoare.
Local Notation Hq := 'H[msys]_finset.setT.

Section Protocol.
Variable q : wf_qreg (QPair (QPair QBool QBool) QBool).
Variable v : 'Hs bool.
Hypothesis normalized_v : [< v; v >] = 1.

Definition teleport_source :=
  successful_sequentialize (paired (teleport_alice (first_register q))
    (teleport_bob (second_register q))).

Lemma teleport_post_obs : register_predicate q (teleport_output v) \is obslf.
Proof. rewrite register_predicate_obsE; exact: teleport_output_obs normalized_v. Qed.
Definition teleport_post : 'FO(Hq) := ObsLf_Build teleport_post_obs.

Lemma teleport_input_obs :
  register_predicate q [> teleport_resource v; teleport_resource v <] \is obslf.
Proof.
rewrite register_predicate_obsE; apply: normalized_outp_obs.
by rewrite isof_dot normalized_v.
Qed.
Definition teleport_input : 'FO(Hq) := ObsLf_Build teleport_input_obs.

Lemma teleport_preE total s :
  (pre total teleport_source (fun _ => teleport_post) s : 'End(Hq)) =
    register_predicate q (teleport_local_pre v).
Proof.
rewrite /teleport_source teleport_serial_preE teleport_serial_pre.
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite teleport_physical_branchE.
change (\sum_z \sum_x (register_action q (teleport_branch z x))^*o
  (register_predicate q (teleport_output v)) = register_predicate q (teleport_local_pre v)).
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite register_action_pre.
rewrite /teleport_local_pre /register_predicate !linear_sum /=.
by apply: eq_bigr=>z _; rewrite !linear_sum /=.
Qed.

Lemma teleport_local_pre_obs (total : bool) (s : CL.store) : teleport_local_pre v \is obslf.
Proof.
rewrite -(register_predicate_obsE q _) -(teleport_preE total s).
exact: is_obslf.
Qed.

Lemma teleport_pre_inequality total s :
  (teleport_input : 'End(Hq)) ⊑ pre total teleport_source (fun _ => teleport_post) s.
Proof.
rewrite teleport_preE /teleport_input /= register_predicate_le.
rewrite (ObsLf_BuildE (teleport_local_pre_obs total s)).
apply: effect_contains_state.
- by rewrite isof_dot normalized_v.
- exact: teleport_local_success normalized_v.
Qed.

Theorem teleport_correct total :
  derives total (fun _ => teleport_input) teleport_source (fun _ => teleport_post).
Proof.
apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>s.
exact: teleport_pre_inequality.
Qed.
End Protocol.
End DistributedTeleportCorrectness.


Module DistributedRemoteCorrectness.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses DistributedProtocolExecution DistributedProtocolQuantum DistributedProtocolState DistributedProtocolLocal DistributedProtocolRemoteLocal DistributedProtocolEffect DistributedProtocolPredicate DistributedProtocolPre DistributedProtocolRemotePre DistributedProtocolSerial DistributedProtocolRemoteSerial DistributedProtocolRegister.
Import CQHoare.
Local Notation Hq := 'H[msys]_finset.setT.

Section Protocol.
Variable q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool)).
Variable v : 'Hs (bool * bool)%type.
Hypothesis normalized_v : [< v; v >] = 1.

Definition remote_source :=
  successful_sequentialize (paired (remote_alice (first_register q))
    (remote_bob (second_register q))).

Lemma remote_post_obs : register_predicate q (remote_output v) \is obslf.
Proof. rewrite register_predicate_obsE; exact: remote_output_obs normalized_v. Qed.
Definition remote_post : 'FO(Hq) := ObsLf_Build remote_post_obs.

Lemma remote_input_obs :
  register_predicate q [> remote_resource v; remote_resource v <] \is obslf.
Proof.
rewrite register_predicate_obsE; apply: normalized_outp_obs.
by rewrite isof_dot normalized_v.
Qed.
Definition remote_input : 'FO(Hq) := ObsLf_Build remote_input_obs.

Lemma remote_preE total s :
  (pre total remote_source (fun _ => remote_post) s : 'End(Hq)) =
    register_predicate q (remote_local_pre v).
Proof.
rewrite /remote_source remote_serial_preE remote_serial_pre.
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite remote_physical_branchE.
change (\sum_z \sum_x (register_action q (remote_branch z x))^*o
  (register_predicate q (remote_output v)) = register_predicate q (remote_local_pre v)).
under eq_bigr=>z _ do under eq_bigr=>x _ do rewrite register_action_pre.
rewrite /remote_local_pre /register_predicate !linear_sum /=.
by apply: eq_bigr=>z _; rewrite !linear_sum /=.
Qed.

Lemma remote_local_pre_obs (total : bool) (s : CL.store) : remote_local_pre v \is obslf.
Proof.
rewrite -(register_predicate_obsE q _) -(remote_preE total s).
exact: is_obslf.
Qed.

Lemma remote_pre_inequality total s :
  (remote_input : 'End(Hq)) ⊑ pre total remote_source (fun _ => remote_post) s.
Proof.
rewrite remote_preE /remote_input /= register_predicate_le.
rewrite (ObsLf_BuildE (remote_local_pre_obs total s)).
apply: effect_contains_state.
- by rewrite isof_dot normalized_v.
- exact: remote_local_success normalized_v.
Qed.

Theorem remote_correct total :
  derives total (fun _ => remote_input) remote_source (fun _ => remote_post).
Proof.
apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>s.
exact: remote_pre_inequality.
Qed.
End Protocol.
End DistributedRemoteCorrectness.


Module DistributedOwnedProtocolCorrectness.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedProtocolProcesses DistributedProtocolOwnership ClassicalRegisterTensor.
Local Notation Hq := 'H[msys]_finset.setT.

Definition teleport_network (q : wf_qreg (QPair (QPair QBool QBool) QBool)) :=
  @teleport_program (first_register q) (second_register q) (pair_register_disjoint q).

Definition remote_network (q : wf_qreg (QPair (QPair QBool QBool) (QPair QBool QBool))) :=
  @remote_program (first_register q) (second_register q) (pair_register_disjoint q).

Lemma teleport_network_sourceE q :
  successful_sequentialize (processes (teleport_network q)) =
    DistributedTeleportCorrectness.teleport_source q.
Proof. by []. Qed.

Lemma remote_network_sourceE q :
  successful_sequentialize (processes (remote_network q)) =
    DistributedRemoteCorrectness.remote_source q.
Proof. by []. Qed.

Theorem teleport_network_correct total q v (Hv : [< v; v >] = 1) :
  CQHoare.derives total
    (fun _ => @DistributedTeleportCorrectness.teleport_input q v Hv)
    (successful_sequentialize (processes (teleport_network q)))
    (fun _ => @DistributedTeleportCorrectness.teleport_post q v Hv).
Proof.
rewrite teleport_network_sourceE.
exact: (@DistributedTeleportCorrectness.teleport_correct q v Hv total).
Qed.

Theorem remote_network_correct total q v (Hv : [< v; v >] = 1) :
  CQHoare.derives total
    (fun _ => @DistributedRemoteCorrectness.remote_input q v Hv)
    (successful_sequentialize (processes (remote_network q)))
    (fun _ => @DistributedRemoteCorrectness.remote_post q v Hv).
Proof.
rewrite remote_network_sourceE.
exact: (@DistributedRemoteCorrectness.remote_correct q v Hv total).
Qed.
End DistributedOwnedProtocolCorrectness.


Module DistributedProtocolCorrectness.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedOwnedProtocolCorrectness.

Theorem teleport_correct total q v (Hv : [< v; v >] = 1) :
  DistributedNetworkValidity.valid total
    (fun _ => @DistributedTeleportCorrectness.teleport_input q v Hv)
    (teleport_network q)
    (fun _ => @DistributedTeleportCorrectness.teleport_post q v Hv).
Proof.
apply/(proj2 (DistributedNetworkValidity.valid_translate_iff _ _ _ _)).
apply: CQHoare.derives_sound.
exact: teleport_network_correct.
Qed.

Theorem remote_correct total q v (Hv : [< v; v >] = 1) :
  DistributedNetworkValidity.valid total
    (fun _ => @DistributedRemoteCorrectness.remote_input q v Hv)
    (remote_network q)
    (fun _ => @DistributedRemoteCorrectness.remote_post q v Hv).
Proof.
apply/(proj2 (DistributedNetworkValidity.valid_translate_iff _ _ _ _)).
apply: CQHoare.derives_sound.
exact: remote_network_correct.
Qed.
End DistributedProtocolCorrectness.


Module DistributedProtocolDerivations.
(* Branch equations for distributed protocols; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedOwnedProtocolCorrectness.

Theorem teleport_partial q v (Hv : [< v; v >] = 1) :
  DistributedNetworkRules.derives false
    (fun _ => @DistributedTeleportCorrectness.teleport_input q v Hv)
    (processes (teleport_network q))
    (fun _ => @DistributedTeleportCorrectness.teleport_post q v Hv).
Proof.
apply: DistributedPartialCompleteness.derives_complete_partial.
exact: DistributedProtocolCorrectness.teleport_correct.
Qed.

Theorem remote_partial q v (Hv : [< v; v >] = 1) :
  DistributedNetworkRules.derives false
    (fun _ => @DistributedRemoteCorrectness.remote_input q v Hv)
    (processes (remote_network q))
    (fun _ => @DistributedRemoteCorrectness.remote_post q v Hv).
Proof.
apply: DistributedPartialCompleteness.derives_complete_partial.
exact: DistributedProtocolCorrectness.remote_correct.
Qed.


Theorem teleport_derive total q v (Hv : [< v; v >] = 1) :
  DistributedNetworkRules.derives total
    (fun _ => @DistributedTeleportCorrectness.teleport_input q v Hv)
    (processes (teleport_network q))
    (fun _ => @DistributedTeleportCorrectness.teleport_post q v Hv).
Proof.
apply: DistributedTotalCompleteness.derives_complete.
exact: DistributedProtocolCorrectness.teleport_correct.
Qed.

Theorem remote_derive total q v (Hv : [< v; v >] = 1) :
  DistributedNetworkRules.derives total
    (fun _ => @DistributedRemoteCorrectness.remote_input q v Hv)
    (processes (remote_network q))
    (fun _ => @DistributedRemoteCorrectness.remote_post q v Hv).
Proof.
apply: DistributedTotalCompleteness.derives_complete.
exact: DistributedProtocolCorrectness.remote_correct.
Qed.
End DistributedProtocolDerivations.
