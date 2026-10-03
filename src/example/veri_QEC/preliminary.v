From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import interval_inference.
From mathcomp Require Import -(notations) sesquilinear.
Require Import mcextra mcaextra notation mxpred extnum ctopology svd mxnorm.
Require Import hermitian inhabited prodvect.
From quantum Require Import tensor.
Require Import quantum orthomodular.
Require Import hspace hspace_extra inhabited summable qreg qmem cqwhile qtype.
From quantum.dirac Require Import hstensor.
From Stdlib Require Import Program.Equality String.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Local Notation R := hermitian.R.
Local Notation C := hermitian.C.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Section mulii.
Local Open Scope ring_scope.
Variable (R : numClosedFieldType).

Lemma mulCii : 'i * 'i = -1 :> R.
Proof. by rewrite -expr2 sqrCi. Qed.
Lemma mulCNii : (- 'i) * 'i = 1 :> R.
Proof. by rewrite mulNr mulCii opprK. Qed.
Lemma mulCiNi : 'i * (-'i) = 1 :> R. 
Proof. by rewrite mulrN mulCii opprK. Qed.
Lemma mulCNiNi : -'i * -'i = -1 :> R.
Proof. by rewrite mulrN mulCNii. Qed.
Lemma divC1i : 1 / 'i = - 'i :> R.
Proof. by rewrite div1r invCi. Qed.
Lemma divCi x : x / 'i = - (x * 'i) :> R.
Proof. by rewrite invCi mulrN. Qed.

End mulii.

Definition TGate := PhGate ((4%:R)^-1).
Notation "'''T'" := TGate.

HB.lock Definition iSWAP : 'End('Hs (bool * bool)%type) :=
  ([> '0 ⊗t '0 ; '0 ⊗t '0 <] + [> '1 ⊗t '1 ; '1 ⊗t '1 <]
  + -'i *: ([> '0 ⊗t '1 ; '1 ⊗t '0 <] + [> '1 ⊗t '0 ; '0 ⊗t '1 <]))%R%VF.
Definition iSWAPE := iSWAP.unlock.
  
Section GateMul.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

(* Basic Gate : X Y Z H S T   a for dagger*)
(* Multiplication *)
Definition Gate_XX := PauliX_id.
Definition Gate_YY := PauliY_id.
Definition Gate_ZZ := PauliZ_id.

Lemma Gate_XY : ''X \o ''Y = 'i *: ''Z.
Proof. by rude_bmx=>//; rewrite mulrN1. Qed.

Lemma Gate_XZ : ''X \o ''Z = -'i *: ''Y.
Proof. by rude_bmx=>//; rewrite !simp_muli. Qed.

Lemma Gate_YX : ''Y \o ''X = -'i *: ''Z.
Proof. by rude_bmx=>//; rewrite mulrN1 opprK. Qed.

Lemma Gate_YZ : ''Y \o ''Z = 'i *: ''X.
Proof. by rude_bmx=>//; rewrite mulrN1 opprK. Qed.

Lemma Gate_ZX : ''Z \o ''X = 'i *: ''Y.
Proof. by rude_bmx=>//; rewrite !simp_muli. Qed.

Lemma Gate_ZY : ''Z \o ''Y = -'i *: ''X.
Proof. by rude_bmx=>//; rewrite mulN1r. Qed.

Lemma Gate_XXX : ''X \o ''X \o ''X = ''X.
Proof. by rewrite Gate_XX comp_lfun1l. Qed.

Lemma Gate_XYX : ''X \o ''Y \o ''X = - ''Y.
Proof. by rude_bmx=>//; rewrite opprK. Qed.

Lemma Gate_XZX : ''X \o ''Z \o ''X = - ''Z.
Proof. by rude_bmx=>//; rewrite opprK. Qed.

Lemma Gate_YXY : ''Y \o ''X \o ''Y = - ''X.
Proof. by rude_bmx=>//; rewrite !simp_muli. Qed.

Lemma Gate_YYY : ''Y \o ''Y \o ''Y = ''Y.
Proof. by rewrite Gate_YY comp_lfun1l. Qed.

Lemma Gate_YZY : ''Y \o ''Z \o ''Y = - ''Z.
Proof. by rude_bmx=>//; rewrite !simp_muli. Qed.

Lemma Gate_ZXZ : ''Z \o ''X \o ''Z = - ''X.
Proof. by rude_bmx=>//; rewrite opprK. Qed.

Lemma Gate_ZYZ : ''Z \o ''Y \o ''Z = - ''Y.
Proof. by rude_bmx=>//; rewrite ?mulrN1// mulN1r. Qed.

Lemma Gate_ZZZ : ''Z \o ''Z \o ''Z = ''Z.
Proof. by rewrite Gate_ZZ comp_lfun1l. Qed.

Lemma Gate_HE : ''H = (sqrtC 2)^-1 *: (''X + ''Z).
Proof. by rude_bmx=>//; rewrite mulrN1 mulNr div1r. Qed.

Definition Gate_HH := Hadamard_id.

Lemma Gate_XH : ''X \o ''H = (sqrtC 2)^-1 *: (\1 - 'i *: ''Y).
Proof. by rewrite Gate_HE linearZr/= linearDr/= Gate_XX Gate_XZ scaleNr. Qed.

Lemma Gate_HX : ''H \o ''X = (sqrtC 2)^-1 *: (\1 + 'i *: ''Y).
Proof. by rewrite Gate_HE linearZl/= linearDl/= Gate_XX Gate_ZX. Qed.

Lemma Gate_YH : ''Y \o ''H = ((sqrtC 2)^-1 * 'i) *: (''X - ''Z).
Proof.
by rewrite Gate_HE linearZr/= linearDr/= 
  Gate_YX Gate_YZ addrC scaleNr -scalerBr scalerA.
Qed.

Lemma Gate_HY : ''H \o ''Y = ((sqrtC 2)^-1 * 'i) *: (''Z - ''X).
Proof.
by  rewrite Gate_HE linearZl/= linearDl/= 
  Gate_XY Gate_ZY scaleNr -scalerBr scalerA.
Qed.

Lemma Gate_YHC : ''Y \o ''H = - (''H \o ''Y).
Proof. by rewrite Gate_YH Gate_HY -scalerN opprB. Qed.

Lemma Gate_HYC : ''H \o ''Y = - (''Y \o ''H).
Proof. by rewrite Gate_YHC opprK. Qed.

Lemma Gate_ZH : ''Z \o ''H = (sqrtC 2)^-1 *: (\1 + 'i *: ''Y).
Proof. by rewrite Gate_HE linearZr/= linearDr/= Gate_ZX Gate_ZZ addrC. Qed.

Lemma Gate_HZ : ''H \o ''Z = (sqrtC 2)^-1 *: (\1 - 'i *: ''Y).
Proof. by rewrite Gate_HE linearZl/= linearDl/= Gate_XZ Gate_ZZ addrC scaleNr. Qed.

Lemma Gate_XHC : ''X \o ''H = ''H \o ''Z.
Proof. by rewrite Gate_XH Gate_HZ. Qed.

Lemma Gate_HXC : ''H \o ''X = ''Z \o ''H.
Proof. by rewrite Gate_HX Gate_ZH. Qed.

Definition Gate_HZC := esym Gate_XHC.
Definition Gate_ZHC := esym Gate_HXC.

Lemma Gate_XHX : ''X \o ''H \o ''X = (sqrtC 2)^-1 *: (''X - ''Z).
Proof.
by rewrite Gate_XHC -comp_lfunA Gate_ZX linearZr/= Gate_HY
  scalerA mulrCA mulCii mulrN1 scaleNr -scalerN opprB.
Qed.

Lemma Gate_YHY : ''Y \o ''H \o ''Y = - ''H.
Proof. by rewrite Gate_YHC linearNl/= -comp_lfunA Gate_YY comp_lfun1r. Qed.

Lemma Gate_ZHZ : ''Z \o ''H \o ''Z = (sqrtC 2)^-1 *: (''Z - ''X).
Proof.
by rewrite Gate_ZHC -comp_lfunA Gate_XZ linearZr/= Gate_HY
  scalerA mulrCA mulCNii mulr1.
Qed.

Lemma Gate_HXH : ''H \o ''X \o ''H = ''Z.
Proof. by rewrite Gate_HXC -comp_lfunA Gate_HH comp_lfun1r. Qed.

Lemma Gate_HYH : ''H \o ''Y \o ''H = - ''Y.
Proof. by rewrite Gate_HYC linearNl/= -comp_lfunA Gate_HH comp_lfun1r. Qed.

Lemma Gate_HZH : ''H \o ''Z \o ''H = ''X.
Proof. by rewrite Gate_HZC -comp_lfunA Gate_HH comp_lfun1r. Qed.

Lemma Gate_HHH : ''H \o ''H \o ''H = ''H.
Proof. by rewrite Gate_HH comp_lfun1l. Qed.

Lemma Gate_SS : ''S \o ''S = ''Z.
Proof. by rude_bmx=>//; rewrite expip_half mulCii. Qed.

Lemma Gate_XSC : ''X \o ''S = - (''S \o ''Y).
Proof. by rude_bmx=>//; rewrite expip_half ?mulCii opprK. Qed.

Lemma Gate_SXC : ''S \o ''X = ''Y \o ''S.
Proof. by rude_bmx=>//; rewrite expip_half// mulCNii. Qed.

Lemma Gate_XSaC : ''X \o ''S^A = ''S^A \o ''Y.
Proof. by rude_bmx=>//; rewrite expip_half conjCi// mulCNii. Qed.

Lemma Gate_SaXC : ''S^A \o ''X = - (''Y \o ''S^A).
Proof. by rude_bmx=>//; rewrite expip_half// conjCi// mulCNiNi opprK. Qed.

Definition Gate_YSC := esym Gate_SXC.
Lemma Gate_SYC : ''S \o ''Y = - (''X \o ''S).
Proof. by rewrite Gate_XSC opprK. Qed.

Definition Gate_SaYC := esym Gate_XSaC.
Lemma Gate_YSaC : ''Y \o ''S^A = - (''S^A \o ''X).
Proof. by rewrite Gate_SaXC opprK. Qed.

Lemma Gate_ZSC : ''Z \o ''S = ''S \o ''Z.
Proof. by rude_bmx=>//; rewrite mulN1r mulrN1. Qed.
Definition Gate_SZC := esym Gate_ZSC.

Lemma Gate_ZSaC : ''Z \o ''S^A = ''S^A \o ''Z.
Proof. by rude_bmx=>//; rewrite mulN1r mulrN1. Qed.
Definition Gate_SaZC := esym Gate_ZSaC.

Lemma Gate_HSC : ''H \o ''S = ''S \o (sqrtC 2)^-1 *: (''Z - ''Y).
Proof.
by rewrite Gate_HE linearZl/= linearZr/= linearDl/= 
  Gate_XSC Gate_ZSC addrC -linearBr.
Qed.

Lemma Gate_SHC : ''S \o ''H = (sqrtC 2)^-1 *: (''Y + ''Z) \o ''S.
Proof.
rewrite Gate_HE linearZl/= linearZr/= linearDr/=.
by rewrite Gate_SXC Gate_SZC -linearDl.
Qed.

Lemma Gate_HSaC : ''H \o ''S^A = ''S^A \o (sqrtC 2)^-1 *: (''Y + ''Z).
Proof.
by rewrite Gate_HE linearZl linearZr linearDl/= Gate_XSaC Gate_ZSaC linearDr.
Qed.

Lemma Gate_SaHC : ''S^A \o ''H = (sqrtC 2)^-1 *: (''Z - ''Y) \o ''S^A.
Proof. 
by rewrite Gate_HE linearZl linearZr linearDr/= Gate_SaXC Gate_SaZC addrC linearBl.
Qed.

Lemma Gate_SSS : ''S \o ''S \o ''S = ''S^A.
Proof. by rewrite Gate_SS; rude_bmx=>//; rewrite expip_half conjCi mulN1r. Qed.

Lemma Gate_XSX : ''X \o ''S \o ''X = ''S \o 'i *: ''Z.
Proof. by rewrite Gate_XSC comp_lfunNl -comp_lfunA Gate_YX -comp_lfunNr -scaleNr opprK. Qed.  

Lemma Gate_YSY : ''Y \o ''S \o ''Y = ''S \o 'i *: ''Z.
Proof. by rewrite Gate_YSC -comp_lfunA Gate_XY. Qed.

Lemma Gate_ZSZ : ''Z \o ''S \o ''Z = ''S.
Proof. by rewrite Gate_ZSC -comp_lfunA Gate_ZZ comp_lfun1r. Qed.

Lemma Gate_HSH : ''H \o ''S \o ''H = ((1 + 'i) / 2) *: \1 + ((1 - 'i) / 2) *: ''X.
Proof.
rude_bmx; rewrite expip_half; 
by rewrite !divc_simp ?sign_simp// addrC ?mulrBl ?mulrDl div1r.
Qed.

Lemma Gate_SaXS : ''S^A \o ''X \o ''S = - ''Y.
Proof. by rude_bmx=>//; rewrite expip_half ?opprK// conjCi. Qed.

Lemma Gate_SaYS : ''S^A \o ''Y \o ''S = ''X.
Proof. by rude_bmx=>//; rewrite expip_half ?conjCi mulCNii. Qed.

Lemma Gate_SaZS : ''S^A \o ''Z \o ''S = ''Z.
Proof. by rewrite -comp_lfunA Gate_ZSC comp_lfunA unitaryf_form comp_lfun1l. Qed.

Lemma Gate_SaHS : ''S^A \o ''H \o ''S = (sqrtC 2)^-1 *: (''Z - ''Y).
Proof. by rewrite -comp_lfunA Gate_HSC comp_lfunA unitaryf_form comp_lfun1l. Qed.

Lemma Gate_SXSa : ''S \o ''X \o ''S^A = ''Y.
Proof. by rude_bmx=>//; rewrite expip_half// conjCi. Qed.

Lemma Gate_SYSa : ''S \o ''Y \o ''S^A = - ''X.
Proof. by rude_bmx=>//; rewrite expip_half ?conjCi ?mulCii ?mulCNiNi. Qed.

Lemma Gate_SZSa : ''S \o ''Z \o ''S^A = ''Z.
Proof. by rewrite Gate_SZC unitaryfKr. Qed.

Lemma Gate_SHSa : ''S \o ''H \o ''S^A = (sqrtC 2)^-1 *: (''Y + ''Z).
Proof. by rewrite Gate_SHC unitaryfKr. Qed. 

Lemma Gate_TT : ''T \o ''T = ''S.
Proof. by rude_bmx=>//; rewrite -expipD -[X in _ = expip X]split2r -!invfM -natrM. Qed.

Lemma Gate_TTTT : ''T \o ''T \o ''T \o ''T = ''Z.
Proof. by rewrite Gate_TT -comp_lfunA Gate_TT Gate_SS. Qed.

Lemma Gate_TTT : ''T \o ''T \o ''T = ''Z \o ''T^A.
Proof. by rewrite -Gate_TTTT unitaryfKr. Qed.

Lemma Gate_ZTC : ''Z \o ''T = ''T \o ''Z.
Proof. by rewrite -Gate_TTTT !comp_lfunA. Qed.
Definition Gate_TZC := esym Gate_ZTC.

Lemma Gate_ZTaC : ''Z \o ''T^A = ''T^A \o ''Z.
Proof. by rude_bmx=>//; rewrite mulrC. Qed.
Definition Gate_TaZC := esym Gate_ZTaC.

Lemma Gate_STC : ''S \o ''T = ''T \o ''S.
Proof. by rewrite -Gate_TT !comp_lfunA. Qed.
Definition Gate_TSC := esym Gate_STC.

Lemma Gate_STaC : ''S \o ''T^A = ''T^A \o ''S.
Proof. by rude_bmx=>//; rewrite mulrC. Qed.
Definition Gate_TaSC := esym Gate_STaC.

Lemma Gate_SaTaC : ''S^A \o ''T^A = ''T^A \o ''S^A.
Proof. by rude_bmx=>//; rewrite mulrC. Qed.
Definition Gate_TaSaC := esym Gate_SaTaC.

Lemma Gate_SaTC : ''S^A \o ''T = ''T \o ''S^A.
Proof. by rude_bmx=>//; rewrite mulrC. Qed.
Definition Gate_TSaC := esym Gate_SaTC.

From mathcomp.analysis Require Import trigo.

Lemma cos_piquarter : cos (pi/4) = ((Num.sqrt 2)^-1)%R :> R.
Proof. by rewrite -atan1 cos_atan expr1n. Qed.
Lemma sin_piquarter : sin (pi/4) = ((Num.sqrt 2)^-1)%R :> R.
Proof.
move: (@cosK R (pi / 4))=><-.
  by rewrite in_itv/= divr_ge0// ?pi_ge0//= 
    ler_pdivrMr// mulrDr mulr1 lerDl mulr_ge0// pi_ge0.
by rewrite sin_acos ?cos_le1 ?cos_geN1// cos_piquarter 
  exprVn sqr_sqrtr// -{1}[1]split2 addrK sqrtrV.
Qed.

Lemma sqrtrC (x : R) : 0 <= x -> (Num.sqrt x)%:C = sqrtC x%:C.
Proof.
move=>Px; apply/(pexpIrn (n := 2))=>//; rewrite ?nnegrE ?lec0R//.
by rewrite sqrtC_ge0 lec0R.
by rewrite -realcX sqr_sqrtr// sqrtCK.
Qed.

Lemma expip_quarter : expip ((4%:R)^-1) = (sqrtC 2)^-1 * (1 + 'i) :> C.
Proof.
rewrite !unlock /expip /expi cos_piquarter sin_piquarter mulrDr mulr1.
by rewrite -natrC -sqrtrC// -realcI; simpc.
Qed.

Lemma Gate_TaXT : ''T^A \o ''X \o ''T = (sqrtC 2)^-1 *: (''X - ''Y).
Proof.
by rude_bmx=>//; rewrite expip_quarter ?opprK// 
  conjcM conj_Creal// rmorphD/= conjC1 conjCi.
Qed.

Lemma Gate_TXTa : ''T \o ''X \o ''T^A = (sqrtC 2)^-1 *: (''X + ''Y).
Proof.
by rude_bmx=>//; rewrite expip_quarter ?opprK// 
  conjcM conj_Creal// rmorphD/= conjC1 conjCi.
Qed.

Lemma Gate_TaYT : ''T^A \o ''Y \o ''T = (sqrtC 2)^-1 *: (''X + ''Y).
Proof.
rude_bmx=>//; rewrite expip_quarter.
by rewrite conjcM conj_Creal// rmorphD/= conjC1 conjCi 
  -mulrA mulrBl mul1r mulCii opprK addrC.
by rewrite mulrCA mulrDr mulr1 mulCNii addrC.
Qed.

Lemma Gate_TYTa : ''T \o ''Y \o ''T^A = (sqrtC 2)^-1 *: (''Y - ''X).
Proof.
rude_bmx=>//; rewrite expip_quarter.
by rewrite -mulrA mulrDl mul1r mulCii.
by rewrite conjcM conj_Creal// rmorphD/= conjC1 conjCi mulrCA mulrBr mulr1 mulCNii.
Qed.

Lemma Gate_TaZT : ''T^A \o ''Z \o ''T = ''Z.
Proof. by rewrite Gate_TaZC unitaryfKl. Qed.

Lemma Gate_TZTa : ''T \o ''Z \o ''T^A = ''Z.
Proof. by rewrite Gate_TZC unitaryfKr. Qed.

Lemma Gate_TaHT : ''T^A \o ''H \o ''T = 2^-1 *: (''X - ''Y) + (sqrtC 2)^-1 *: ''Z.
Proof.
by rewrite Gate_HE linearZr linearZl/= linearDr linearDl/= 
  Gate_TaXT Gate_TaZT scalerDr scalerA -invfM -expr2 sqrtCK.
Qed.

Lemma Gate_THTa : ''T \o ''H \o ''T^A = 2^-1 *: (''X + ''Y) + (sqrtC 2)^-1 *: ''Z.
Proof.
by rewrite Gate_HE linearZr linearZl/= linearDr linearDl/=
  Gate_TXTa Gate_TZTa scalerDr scalerA -invfM -expr2 sqrtCK.
Qed.

Lemma Gate_TaST : ''T^A \o ''S \o ''T = ''S.
Proof. by rewrite Gate_TaSC unitaryfKl. Qed.

Lemma Gate_TSTa : ''T \o ''S \o ''T^A = ''S.
Proof. by rewrite Gate_TSC unitaryfKr. Qed.

Lemma CNOT_adj : CNOT^A = CNOT.
Proof. by rewrite CNOTE linearD/= !tentf_adj !adj_outp adjf1 PauliX_adj. Qed.

Lemma PauliXE : ''X = [> '0; '1 <] + [> '1; '0 <].
Proof.
apply/(intro_onb t2tv)=>[[]]; 
by rewrite PauliX_cb lfunE/= !outpE !onb_dot/= scale0r scale1r ?addr0// add0r.
Qed.

Lemma PauliY_cb b : PauliY ''b = ((-1)^b * 'i) *: ''(negb b).
Proof. by case: b; rude_bmx=>//; rewrite mulN1r. Qed.

Lemma PauliYE : ''Y = 'i *: ([> '1; '0 <] - [> '0; '1 <]).
Proof.
apply/(intro_onb t2tv)=>[[]]; 
rewrite PauliY_cb !lfunE/= !lfunE/= !lfunE/= !outpE !onb_dot/= scale0r scale1r.
by rewrite sub0r scalerN expr1z mulN1r scaleNr.
by rewrite subr0 expr0z mul1r.
Qed.

Lemma PauliZE : ''Z = [> '0; '0 <] - [> '1; '1 <].
Proof.
by apply/(intro_onb t2tv)=>[[]]; rewrite PauliZ_cb !lfunE/= !lfunE/= 
  !outpE !onb_dot/= scale0r scale1r ?subr0// expr1z sub0r scaleN1r.
Qed.

Lemma Gate_CNOTX1CNOT : CNOT \o (''X ⊗f \1) \o CNOT = ''X ⊗f ''X.
Proof.
rewrite CNOTE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite -!comp_lfunA !outp_compr !PauliX_cb !outpE !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 -linearDl/= -PauliXE.
Qed.

Lemma Gate_CNOTX2CNOT : CNOT \o (\1 ⊗f ''X) \o CNOT = \1 ⊗f ''X.
Proof.
rewrite CNOTE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite Gate_XXX !outp_comp !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 -linearDl/= sumbtv_out.
Qed.

Lemma Gate_CNOTY1CNOT : CNOT \o (''Y ⊗f \1) \o CNOT = ''Y ⊗f ''X.
Proof.
rewrite CNOTE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite -!comp_lfunA !outp_compr !PauliY_cb/= expr0z expr1z !outpE !dotpZr !onb_dot/=.
rewrite !mulr0 !scale0r !out0p !ten0tf add0r addr0 !mulr1 mul1r mulN1r.
by rewrite -linearDl/= !outpZl addrC scaleNr -scalerBr -PauliYE.
Qed.

Lemma Gate_CNOTY2CNOT : CNOT \o (\1 ⊗f ''Y) \o CNOT = ''Z ⊗f ''Y.
Proof.
rewrite CNOTE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite Gate_XYX !outp_comp !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 tentfNr -tentfBl PauliZE.
Qed.

Lemma Gate_CNOTZ1CNOT : CNOT \o (''Z ⊗f \1) \o CNOT = ''Z ⊗f \1.
Proof.
rewrite CNOTE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite -!comp_lfunA !outp_compr !PauliZ_cb expr0z expr1z !outpE !dotpZr !onb_dot/=.
rewrite !mulr0 !scale0r !out0p !ten0tf add0r addr0 !mulr1.
by rewrite scale1r scaleN1r outpNl Gate_XX -tentfDl PauliZE.
Qed.

Lemma Gate_CNOTZ2CNOT : CNOT \o (\1 ⊗f ''Z) \o CNOT = ''Z ⊗f ''Z.
Proof.
rewrite CNOTE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite Gate_XZX !outp_comp !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 tentfNr -tentfBl PauliZE.
Qed.

(* CZ : CZ^A = CZ *)
Lemma CZGate_adj : ''CZ^A = ''CZ.
Proof. by rewrite CZGateE linearD/= !tentf_adj !adj_outp adjf1 PauliZ_adj. Qed.

Lemma Gate_CZCZ : ''CZ \o ''CZ = \1.
Proof. by rewrite -{1}CZGate_adj unitaryf_form. Qed.

Lemma Gate_CZX1CZ : ''CZ \o (''X ⊗f \1) \o ''CZ = ''X ⊗f ''Z.
Proof.
rewrite CZGateE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite -!comp_lfunA !outp_compr !PauliX_cb !outpE !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 -linearDl/= -PauliXE.
Qed.

Lemma Gate_CZX2CZ : ''CZ \o (\1 ⊗f ''X) \o ''CZ = ''Z ⊗f ''X.
Proof.
rewrite CZGateE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite Gate_ZXZ !outp_comp !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 tentfNr -tentfBl PauliZE.
Qed.

Lemma Gate_CZY1CZ : ''CZ \o (''Y ⊗f \1) \o ''CZ = ''Y ⊗f ''Z.
Proof.
rewrite CZGateE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite -!comp_lfunA !outp_compr !PauliY_cb/= expr0z expr1z !outpE !dotpZr !onb_dot/=.
rewrite !mulr0 !scale0r !out0p !ten0tf add0r addr0 !mulr1 mul1r mulN1r.
by rewrite -linearDl/= !outpZl addrC scaleNr -scalerBr -PauliYE.
Qed.

Lemma Gate_CZY2CZ : ''CZ \o (\1 ⊗f ''Y) \o ''CZ = ''Z ⊗f ''Y.
Proof.
rewrite CZGateE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite Gate_ZYZ !outp_comp !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 tentfNr -tentfBl PauliZE.
Qed.

Lemma Gate_CZZ1CZ : ''CZ \o (''Z ⊗f \1) \o ''CZ = ''Z ⊗f \1.
Proof.
rewrite CZGateE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite -!comp_lfunA !outp_compr !PauliZ_cb expr0z expr1z !outpE !dotpZr !onb_dot/=.
rewrite !mulr0 !scale0r !out0p !ten0tf add0r addr0 !mulr1.
by rewrite scale1r scaleN1r outpNl Gate_ZZ -tentfDl PauliZE.
Qed.

Lemma Gate_CZZ2CZ : ''CZ \o (\1 ⊗f ''Z) \o ''CZ = \1 ⊗f ''Z.
Proof.
rewrite CZGateE !linearDl !linearDr/= !tentf_comp ?(comp_lfun1l, comp_lfun1r).
rewrite Gate_ZZZ !outp_comp !onb_dot/= !scale0r !scale1r.
by rewrite !linear0l add0r addr0 -tentfDl sumbtv_out.
Qed.

Lemma iSWAP_tr : iSWAP^T = iSWAP.
Proof.
by rewrite iSWAPE trfD trfZ !trfD !tr_outp !tentv_conj !t2tv_conj; f_equal; rewrite addrC.
Qed.

Lemma iSWAP_cb (b1 b2 : bool) : iSWAP (''b1 ⊗t ''b2) = 
  ((-'i) ^ (b1 != b2)) *: ( ''(b1 (+) (b1 != b2)) ⊗t ''(b2 (+) (b1 != b2))).
Proof.
case: b1; case: b2=>/=; rewrite iSWAPE; (do ! rewrite lfunE/=);
rewrite !outpE !tentv_dot !onb_dot/= ?(mulr0, mul0r, mul1r, mulr1);
by rewrite ?(scale0r, scale1r) ?addr0 ?add0r ?expr1z// scaler0 addr0.
Qed.

Lemma iSWAPa_cb (b1 b2 : bool) : iSWAP^A (''b1 ⊗t ''b2) = 
  ('i ^ (b1 != b2)) *: ( ''(b1 (+) (b1 != b2)) ⊗t ''(b2 (+) (b1 != b2))).
Proof.
case: b1; case: b2=>/=; 
rewrite iSWAPE !adjfD adjfZ adjfD adj_outp -mulci3 conjCK !adj_outp;
(do ! rewrite lfunE/=);
rewrite !outpE !tentv_dot !onb_dot/= ?(mulr0, mul0r, mul1r, mulr1);
by rewrite ?(scale0r, scale1r) ?addr0 ?add0r ?expr1z// scaler0 addr0.
Qed.

Lemma iSWAP_SWAP : SWAP \o iSWAP \o SWAP = iSWAP.
Proof.
apply/(intro_onb t2tv2_onbasis)=>[[]][][]/=;
by rewrite /tentv_fun lfunE/= swaptfEtv lfunE/= !iSWAP_cb/= linearZ/= swaptfEtv.
Qed.

Lemma iSWAPa_SWAP : SWAP \o iSWAP^A \o SWAP = iSWAP^A.
Proof.
apply/(intro_onb t2tv2_onbasis)=>[[]][][]/=;
by rewrite /tentv_fun lfunE/= swaptfEtv lfunE/= !iSWAPa_cb/= linearZ/= swaptfEtv.
Qed.

Lemma SWAP_id : SWAP \o SWAP = \1 :> 'End[(bool * bool)%type].
Proof. by rewrite -{1}swaptf_adj unitaryf_form. Qed.

Lemma Gate_SWAPiSWAPC : SWAP \o iSWAP = iSWAP \o SWAP.
Proof. by rewrite -{1}iSWAP_SWAP !comp_lfunA SWAP_id comp_lfun1l. Qed.
Definition Gate_iSWAPSWAPC := esym Gate_SWAPiSWAPC.

Lemma Gate_SWAPiSWAPaC : SWAP \o iSWAP^A = iSWAP^A \o SWAP.
Proof. by rewrite -{1}iSWAPa_SWAP !comp_lfunA SWAP_id comp_lfun1l. Qed.
Definition Gate_iSWAPaSWAPC := esym Gate_SWAPiSWAPaC.

Lemma iSWAP_unitary : iSWAP \is unitarylf.
Proof.
apply/unitarylfP/(intro_onb t2tv2_onbasis)=>[[]][][]/=;
rewrite /tentv_fun/= lfunE/= iSWAP_cb linearZ/= iSWAPa_cb/= scalerA lfunE/=;
by rewrite ?expr0z ?expr1z ?mulr1 ?scale1r// mulCNii scale1r.
Qed.
HB.instance Definition _ :=
  isUnitaryLf.Build 'Hs(bool * bool)%type iSWAP iSWAP_unitary.

Lemma Gate_iSWAPaX1iSWAP : iSWAP^A \o (''X ⊗f \1) \o iSWAP = ''Z ⊗f ''Y.
Proof.
apply/(intro_onb t2tv2_onbasis)=>[[]][][]/=;
rewrite /tentv_fun/= tentf_apply PauliZ_cb PauliY_cb lfunE/= iSWAP_cb linearZ/=;
rewrite lfunE/= tentf_apply PauliX_cb/= lfunE/= iSWAPa_cb/= tentvZl tentvZr;
by rewrite scalerA ?expr0z ?expr1z ?mulr1 ?scale1r// ?mul1r// !mulN1r// opprK.
Qed.

Lemma Gate_iSWAPaX2iSWAP : iSWAP^A \o (\1 ⊗f ''X) \o iSWAP = ''Y ⊗f ''Z.
Proof.
rewrite -swaptf_tf -!comp_lfunA Gate_SWAPiSWAPC !comp_lfunA Gate_iSWAPaSWAPC.
by rewrite [X in X \o _]comp_lfunACA -[X in X \o _]comp_lfunA Gate_iSWAPaX1iSWAP swaptf_tf.
Qed.

Lemma Gate_iSWAPaY1iSWAP : iSWAP^A \o (''Y ⊗f \1) \o iSWAP = (- ''Z) ⊗f ''X.
Proof.
apply/(intro_onb t2tv2_onbasis)=>[[]][][]/=;
rewrite /tentv_fun/= tentf_apply !lfunE/= PauliZ_cb PauliX_cb lfunE/= iSWAP_cb linearZ/=;
rewrite tentf_apply PauliY_cb/= !lfunE/= tentvZl !linearZ/= iSWAPa_cb/=;
rewrite -scaleN1r !scalerA tentvZl ?expr0z ?expr1z ?(mulr1,mul1r,mulN1r,mulrN1);
by rewrite ?mulCii// ?mulCNiNi// mulCNii opprK.
Qed.

Lemma Gate_iSWAPaY2iSWAP : iSWAP^A \o (\1 ⊗f ''Y) \o iSWAP = (- ''X) ⊗f ''Z.
Proof.
rewrite -swaptf_tf -!comp_lfunA Gate_SWAPiSWAPC !comp_lfunA Gate_iSWAPaSWAPC.
rewrite [X in X \o _]comp_lfunACA -[X in X \o _]comp_lfunA.
by rewrite Gate_iSWAPaY1iSWAP swaptf_tf tentfNl tentfNr.
Qed.

Lemma Gate_iSWAPaZ1iSWAP : iSWAP^A \o (''Z ⊗f \1) \o iSWAP = \1 ⊗f ''Z.
Proof.
apply/(intro_onb t2tv2_onbasis)=>[[]][][]/=;
rewrite /tentv_fun/= tentf_apply !lfunE/=  lfunE/= iSWAP_cb linearZ/=;
rewrite tentf_apply !PauliZ_cb/= !lfunE/= tentvZl !linearZ/= iSWAPa_cb/=;
by rewrite !scalerA ?expr0z ?expr1z ?(mulr1,mul1r,mulN1r,mulrN1)// ?mulCNii// opprK mulCii.
Qed.

Lemma Gate_iSWAPaZ2iSWAP : iSWAP^A \o (\1 ⊗f ''Z) \o iSWAP = ''Z ⊗f \1.
Proof.
rewrite -swaptf_tf -!comp_lfunA Gate_SWAPiSWAPC !comp_lfunA Gate_iSWAPaSWAPC.
by rewrite [X in X \o _]comp_lfunACA -[X in X \o _]comp_lfunA Gate_iSWAPaZ1iSWAP swaptf_tf.
Qed.

Lemma CNOT_id : CNOT \o CNOT = \1.
Proof. by rewrite -{1}CNOT_adj unitaryf_form. Qed.

End GateMul.


Section ExtraOML.
Import ComplLatticeSyntax.
Variable (disp : Order.disp_t) (T : oModularLatticeType disp).

Lemma meetxJxy (a b : T) :
  (a `&` (a `&&` b) = (a `&&` b))%O.
Proof. OM_autodec a b. Qed.

Lemma joinJxyJOxy (a b : T) :
  ((a `&&` b) `|` (~` a `&&` b) = (a `|` b) `&` (~` a `|` b))%O.
Proof. OM_autodec a b. Qed.

Lemma sprojxIxy (a b : T) :
  (a `&&` (a `&` b) = (a `&` b))%O.
Proof. OM_autodec a b. Qed.

Lemma sprojOxIxy (a b : T) :
  (~` a `&&` (a `&` b) = \bot)%O.
Proof. OM_autodec a b. Qed.

Lemma sprojxIOxy (a b : T) :
  (a `&&` (~` a `&` b) = \bot)%O.
Proof. OM_autodec a b. Qed.

End ExtraOML.


Section ExtraSubspace.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.

Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.

Variable (V : chsType).

Lemma memh_formU (H : {hspace V}) (U : 'FU(V)) v :
  (U v \in H) = (v \in formh U^A H).
Proof. by rewrite memh_form/= adjfK. Qed.

Lemma supph_formV (H : {hspace V}) (U : 'FU(V)) (x : 'FH) :
  (supph (formlf U x) `<=` H) = (supph x `<=` formh U^A H).
Proof.
have -> : formlf U x = sumoutp (eigenval (U:=x)) 
  (fun i => U (eigenvec i)) (fun i => U (eigenvec i)).
  rewrite formlfE {1}spectralE /spectral !sumoutpE linear_sumr linear_sumlz/=.
  by apply eq_bigr=>i _; rewrite linearZr/= outp_compr linearZl/= outp_compl adjfK.
rewrite [in RHS]spectralE /spectral; apply/eqb_iff; split.
  rewrite !sumoutpE -lehO -kerhE=>/lehP IH.
  rewrite -lehO -kerhE; apply/lehP=>v.
  rewrite -formhO -memh_formU=>/IH.
  rewrite !memh_kerE=>/eqP/(f_equal (fun y => U^A y)).
  rewrite linear0 !sum_lfunE !linear_sum/==>{2}<-; apply/eqP.
  apply eq_bigr=>i _; rewrite !lfunE/= linearZ/= !outpE !linearZ/=.
  by rewrite -adj_dotEr !unitaryfKEl.
rewrite !sumoutpE -lehO -kerhE=>/lehP IH.
rewrite -lehO -kerhE; apply/lehP=>v.
rewrite -{1}[v](unitaryfKEr U) memh_formU formhO=>/IH;
rewrite !memh_kerE=>/eqP/(f_equal (fun y => U y)).
rewrite linear0 2!sum_lfunE linear_sum/==>{2}<-; apply/eqP.
by apply eq_bigr=>i _; rewrite !lfunE/= linearZ/= !outpE !linearZ/= adj_dotEr.
Qed.

Lemma supph_denf_leP (H1 H2 : {hspace V}) (U : 'FU(V)) :
  (forall v : V, (U v \in H1) = (v \in H2)) ->
  (forall A : 'FH, (supph (formlf U A) `<=` H1) = (supph A `<=` H2))%HS.
Proof.
move=>P1 A; rewrite supph_formV.
have ->// : formh U^A H1 = H2 by apply/eqP/hseqP=>x; rewrite -memh_formU.
Qed.

Lemma leh_nsP (A B : {hspace V}) :
  reflect (forall v : 'NS(V), (v : V) \in A -> (v : V) \in B) (A `<=` B).
Proof.
apply/(iffP (lehP _ _))=>P v; first by apply P.
have [/eqP->|Pv] := boolP (v == 0).
  by rewrite !mem0h.
have P1 : [< normd v ; normd v >] = 1.
  by rewrite dotp_norml dotp_normr dotp_norm mulrA 
    -expr2 exprVn mulVf// expf_neq0// normr_eq0.
move: (P (HB.pack (normd v) (isNormalState.Build _ _ P1) : 'NS(V)))=>/=.
by rewrite /normd !memhE_line hlineZ// invr_eq0 normr_eq0.
Qed.

Lemma leh_suppP (A B : {hspace V}) :
  reflect (forall x : 'FD(V), supph x `<=` A -> supph x `<=` B) (A `<=` B).
Proof.
apply/(iffP idP)=>[P x /le_trans/(_ P)//|P].
apply/leh_nsP=>v; move: (P [> v ; v <]).
by rewrite !memhE_line hlineE.
Qed.

Lemma eq_supphP (A B : {hspace V}) :
  reflect (forall x : 'FD(V), (supph x `<=` A) = (supph x `<=` B)) (A == B).
Proof.
apply/(iffP idP)=>[/eqP->|H]//.
by apply/eqP/le_anti/andP; split; apply/leh_suppP=>x; rewrite H.
Qed.

Lemma kerh_eq1 (f : 'End(V)) :
  (kerh f == `1`) = (f == 0).
Proof.
apply/eqb_iff; split=>[/eqP P|/eqP->]; last by rewrite kerh0.
by apply/eqP/lfunP=>v; move: (memh1 v); rewrite -P memh_kerE lfunE/==>/eqP.
Qed.

Lemma supph_eq0 (f : 'End(V)) :
  (supph f == `0`) = (f == 0).
Proof. by rewrite supphE hsOx_eq hsO0 kerh_eq1. Qed.

Lemma supph_formlf (P : {hspace V}) (r : 'F+) :
  supph (formlf P r) = (P `&&` supph r).
Proof.
rewrite sprojhE -[X in _ \o _ \o X]hermf_adjE -formlfE !formlf_soE.
apply/hsO_inj; rewrite -!kerhE; apply/eqP/hseqP=>x.
rewrite !memh_kerE -!psdf_dot_eq0E/= !formsoE !lfunE/= !lfunE/=.
rewrite -adj_dotEl psdf_dot_eq0E -adj_dotEl psdf_dot_eq0E.
by rewrite -!memh_kerE /kerh supph_id.
Qed.

Lemma formh_supph (U : 'FU(V)) (x : 'F+) :
  supph (formlf U x) = formh U (supph x).
Proof.
apply/hsO_inj; rewrite -formhO -!kerhE; apply/eqP/hseqP=>v.
rewrite memh_kerE memh_form memh_kerE -!psdf_dot_eq0E/=.
by rewrite formlfE lfunE/= lfunE/= adj_dotEl.
Qed.

(* from refinement/language *)
Lemma CP_supph_le (E : 'CP(V)) (P Q : {hspace V}) :
  (forall r : 'FD, supph r `<=` P -> supph (E r) `<=` Q) <->
    (supph (E P) `<=` Q).
Proof.
split=>[ Ph | /supph_le_trlf0P P1 x Px].
  apply /supph_trlf0_le =>/=.
  rewrite heigenE sumoutpE linear_sum/=
    linear_sumlz/= linear_sum/= big1// =>i _.
  rewrite scale1r; move: (heigen_mem i).
  by rewrite memhE_line hlineE=>/Ph/=/supph_le_trlf0P.
apply/supph_trlf0_le=>/=; apply/le_anti/andP; split; 
  last by apply/psdlf_TrM; apply/is_psdlf.
rewrite -P1; apply/lef_psdtr/is_psdlf/cp_preserve_order.
by apply: (le_trans (obslf_le_supph _)); rewrite -leh_lef.
Qed.

Lemma CP_kerh_ge (E : 'CP(V)) (P Q : {hspace V}) :
  (forall r : 'FD, supph r `<=` P -> supph (E r) `<=` Q) <->
    (P `<=` kerh (E^*o (~` Q))).
Proof.
by rewrite CP_supph_le; split; rewrite -supp_le_trlfE/= dualso_trlfE 
  lftraceC -[P]ocomplK supp_le_trlfE/= kerhE lehO.
Qed.

Lemma trlf_psdf_comp_eq0 (A B : 'F+(V)) :
  (\Tr (A \o B) == 0) = (supph A \o supph B == 0).
Proof.
apply/eqb_iff; split.
  rewrite {1}spectralE supph_eigenE /spectral sumoutpE linear_sumlz linear_sum/=.
  rewrite psumr_eq0/=.
    move=>i _; rewrite linearZl linearZ/= mulr_ge0//.
    by apply/ltW/eigenval_psd.
    by rewrite outp_compl outp_trlf adj_dotEl; apply/psdlfP/is_psdlf.
  move=>/allP Pi; apply/eqP; rewrite sumoutpE linear_sumlz big1//==>i _.
  move: (Pi i); rewrite mem_index_enum=>/(_ isT); rewrite linearZl/= linearZ/=.
  rewrite mulf_eq0 eigenval_eq0/= scale1r !outp_compl outp_trlf adj_dotEl.
  by rewrite hermf_adjE psdf_dot_eq0E -supphP=>/eqP->; rewrite outp0.
move=>/eqP H.
rewrite {1}spectralE /spectral sumoutpE linear_sumlz linear_sum/= big1// =>i _.
rewrite linearZl/= outp_compl hermf_adjE.
move: H=>/(f_equal (fun x : 'End(V) => [< eigenvec i; x (eigenvec i) >])).
rewrite !lfunE/= dotp0 -adj_dotEl hermf_adjE/= (supph_eigenE A).
rewrite sumoutpE sum_lfunE (bigD1 i)//= big1=>[|/eqP].
  by move=>j /negPf nji; rewrite scale1r outpE ponb_dot nji scale0r.
rewrite scale1r addr0 outpE ns_dot scale1r psdf_dot_eq0E supphP=>/eqP->.
by rewrite outp0 scaler0 linear0.
Qed.
(* Lemma A.9 *)
Lemma CP_supph_le_kerh (E : 'CP(V)) (r : 'FD) (Q : {hspace V}) :
  (supph (E r) `<=` Q) = (supph r `<=` kerh (E^*o (~` Q))).
Proof.
apply/eqb_iff; split.
  move=>/supph_le_trlf0P/eqP; rewrite dualso_trlfE trlf_psdf_comp_eq0/==>H.
  by apply/supph_trlf0_le/eqP; rewrite -supphE trlf_psdf_comp_eq0 supph_id.
move=>/supph_le_trlf0P/eqP; rewrite -supphE trlf_psdf_comp_eq0 supph_id=>H.
by apply/supph_trlf0_le/eqP; rewrite /= dualso_trlfE trlf_psdf_comp_eq0.
Qed.

Lemma supph_sum_le_inf (I : choiceType) (f : I -> 'F+(V)) :
  cvg ((psum (f : I -> 'End(V)) @ totally))%classic -> 
    supph (sum (f : I -> 'End(V))) = \cups_i supph (f i).
Proof.
move=>P1; apply/le_anti/andP; split.
  rewrite -lehO cupsO -kerhE; apply/lehP=>v /memh_capsP H.
  rewrite memh_kerE sum_summable_lfunE//.
  have -> : (fun i : I => f i v) = (fun _ => 0).
    by apply/funext=>i; apply/eqP; move: (H i)=>/=; rewrite -kerhE memh_kerE; apply.
  by rewrite summable_sum_cst0.
apply/cups_glb=>i _; apply/supph_lef; rewrite /sum.
apply/lim_gev_near=>//; exists [fset i]%fset=>// B/=; rewrite fsub1set=>PB.
rewrite /psum -(big_seq_fsetE _ B xpredT (f : I -> 'End(V)))/=.
by rewrite (big_fsetD1 i)//= levDl sumv_ge0// =>j _; rewrite psdf_ge0.
Qed.

Lemma supph_lim_le (T : Type) (F : set_system T) 
  {FF : ProperFilter F} (f : T -> 'End(V)) A :
  cvg (f @ F)%classic -> (forall i, supph (f i) `<=` A) ->
    supph (lim (f @ F)%classic) `<=` A.
Proof.
move=>P1 P2; rewrite -lehO -kerhE; apply/lehP=>x Px.
rewrite memh_kerE -lfun_liml//.
suff -> : (fun i => f i x) = (fun => 0) by rewrite lim_cst.
apply/funext=>i; move: (P2 i); rewrite -lehO -kerhE=>/lehP/(_ _ Px).
by rewrite memh_kerE=>/eqP.
Qed.

End ExtraSubspace.

Section ESpace1.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.

(* eigenspace w.r.t. eigenvalue 1 *)
Definition espace1 (V : chsType) (f : 'End(V)) := kerh (cplmt f).

Lemma espace1E (V : chsType) (f : 'End(V)) (x : V) :
  (x \in espace1 f) = (f x == x).
Proof. by rewrite memh_kerE /cplmt lfunE/= !lfunE/= subr_eq0 eq_sym. Qed.

Lemma espace1P (V : chsType) (f : 'End(V)) (x : V) :
  reflect (f x = x) (x \in espace1 f).
Proof. by rewrite espace1E; apply/eqP. Qed.

Lemma espace1_PauliZ : espace1 ''Z = <[ '0 ]>.
Proof.
apply/eqP/hseqP=>v; rewrite espace1E; apply/eqb_iff; split.
rewrite [v](onb_vec t2tv) big_bool/= linearD/= !linearZ/= !PauliZ_cb/= expr0z expr1z.
rewrite scaleN1r scale1r=>/eqP/addIr/eqP; rewrite scalerN eq_sym -subr_eq0.
rewrite opprK -mulr2n -scaler_nat scaler_eq0 pnatr_eq0/==>/eqP->.
by rewrite add0r memhZ_line.
by move=>/hlineP[k]->; rewrite linearZ/= PauliZ_cb expr0z scale1r.
Qed.

Lemma espace1_PauliZN : espace1 (-''Z) = <[ '1 ]>.
Proof.
apply/eqP/hseqP=>v; rewrite espace1E; apply/eqb_iff; split.
rewrite [v](onb_vec t2tv) big_bool/= linearD/= !linearZ/= 
  !lfunE/= !PauliZ_cb/= expr0z expr1z.
rewrite scale1r scaleN1r opprK=>/eqP/addrI/eqP.
rewrite scalerN eq_sym -subr_eq0 opprK.
rewrite -mulr2n -scaler_nat scaler_eq0 pnatr_eq0/==>/eqP->.
by rewrite addr0 memhZ_line.
by move=>/hlineP[k]->; rewrite linearZ/= lfunE/= PauliZ_cb expr1z scaleN1r opprK.
Qed.

End ESpace1.

Section ESpaceCmplt.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Variable (U : chsType).

Lemma normallf_dec (A : 'End(U)) :
  A \is normallf -> exists (o : 'ONB('I_(dim U) ; U)) (f : 'I_(dim U) -> C),
    A = sumoutp f o o.
Proof.
rewrite qualifE=>/eigen_dec P1.
pose ff i := c2h (col i (eigenmx (h2mx A))).
have P3 : #|'I_(dim U)| = dim U by exact: card_ord.
have P2 : forall i j, [< ff i ; ff j >] = (i == j)%:R.
  move=>i j; rewrite dotp_mulmx /ff !c2hK.
  by rewrite adj_col -mulmx_rowcol unitarymxKV ?eigen_unitarymx ?mxE.
pose o : 'ONB := HB.pack ff (isONB.Build U 'I_(dim U) ff P2 P3).
exists o; exists (mxpred.eigenval (h2mx A)).
rewrite sumoutp.unlock; apply/h2mx_inj.
rewrite {1}P1 linear_sum/= mulmx_diag_colrow; apply eq_bigr=>i _.
by rewrite linearZ/= outp.unlock mx2hK c2hK adj_col.
Qed.

Lemma normallf_idem_dec (A : 'End(U)) :
  A \is normallf -> A \o A = \1 ->
    exists (o : 'ONB('I_(dim U) ; U)) (f : 'I_(dim U) -> bool),
      A = sumoutp (fun i => (-1) ^+ (f i)) o o.
Proof.
move=>/normallf_dec[o][fo ->].
rewrite sumoutp_comp=>P1.
exists o; exists (fun i => fo i == -1).
apply/(intro_onb o)=>i; rewrite !sumoutp_apply.
move: P1=>/lfunP/(_ (o i)); rewrite sumoutp_apply lfunE/= -{2}[o i]scale1r.
move=>/ns_scaleI/eqP; rewrite -expr2 sqrf_eq1=>/orP[/eqP->|/eqP->].
by rewrite -subr_eq0 opprK -mulr2n mulrn_eq0//= oner_eq0 expr0.
by rewrite eqxx expr1.
Qed.

Lemma espace1_sumoutp (o : 'ONB('I_(dim U) ; U)) (ff : 'I_(dim U) -> bool) :
  espace1 (sumoutp (fun i => (-1) ^+ (ff i)) o o) =
    sumoutp (fun i => (~~ ff i)%:R) o o :> 'End(U).
Proof.
pose X := sumoutp (fun i => (~~ ff i)%:R) o o.
have PX : X \is projlf.
  apply/projlfP; split.
    rewrite sumoutp_adj; apply/sumoutp_eq=>i.
    by rewrite conj_Creal.
  rewrite sumoutp_comp; apply/sumoutp_eq=>i.
  by rewrite -natrM mulnb andbb.
pose HX := HSType (ProjLf_Build PX).
suff -> : espace1 (sumoutp (fun i => (-1) ^+ (ff i)) o o) = HX.
  by rewrite hsE.
apply/le_anti/andP; split.
  apply/lehP=>x; rewrite espace1E memhE/= (onb_vec o x)=>/eqP H.
  apply/eqP; rewrite hsE/= linear_sum; apply eq_bigr=>i _ /=.
  move: H =>/(intro_onbl o)/(_ i).
  rewrite linear_sum/= !dotp_sumr (bigD1 i)//= big1 1?(bigD1 i) 1?big1//=.
    by move=>j /negPf nji; rewrite linearZ/= sumoutp_apply !dotpZr onb_dot eq_sym nji !mulr0.
    by move=>j /negPf nji; rewrite dotpZr onb_dot eq_sym nji mulr0.
  rewrite !linearZ/= !sumoutp_apply !dotpZr ?addr0 onb_dot eqxx !mulr1.
  case: (ff i); rewrite ?expr0 ?scale1r// expr1 mulrN1=>/eqP.
  by rewrite eqNr=>/eqP->; rewrite !scale0r.
apply/lehP=>x; rewrite espace1E memhE/= (onb_vec o x)=>/eqP H.
apply/eqP; rewrite linear_sum; apply eq_bigr=>i _ /=.
move: H =>/(intro_onbl o)/(_ i).
rewrite linear_sum/= !dotp_sumr (bigD1 i)//= big1 1?(bigD1 i) 1?big1//=.
  by move=>j /negPf nji; rewrite linearZ/= hsE/= sumoutp_apply !dotpZr onb_dot eq_sym nji !mulr0.
  by move=>j /negPf nji; rewrite dotpZr onb_dot eq_sym nji mulr0.
rewrite !addr0 hsE/= !linearZ/= !sumoutp_apply.
rewrite !dotpZr ?addr0 onb_dot eqxx !mulr1.
by case: (ff i); rewrite ?expr0 ?scale1r// mulr0=><-; rewrite !scale0r.
Qed.

Lemma espace1_sumoutpN (o : 'ONB('I_(dim U) ; U)) (ff : 'I_(dim U) -> bool) :
  espace1 (- sumoutp (fun i => (-1) ^+ (ff i)) o o) =
    sumoutp (fun i => (ff i)%:R) o o :> 'End(U).
Proof.
transitivity (sumoutp (fun i => (~~ ~~ (ff i))%:R) o o).
  rewrite sumoutpN -espace1_sumoutp; do 3 f_equal.
  by apply/sumoutp_eq=>i; case: (ff i); rewrite expr1 expr0// opprK.
by apply/sumoutp_eq=>i; rewrite negbK.
Qed.

Lemma espace1N_sumoutp (o : 'ONB('I_(dim U) ; U)) (ff : 'I_(dim U) -> bool) :
  espace1 (- sumoutp (fun i => (-1) ^+ (ff i)) o o) =
    (~` espace1 (sumoutp (fun i => (-1) ^+ (ff i)) o o))%HS.
Proof.
apply/hspacelfP; rewrite espace1_sumoutpN hs2lfOE/= espace1_sumoutp/= -cplmtE.
apply/eqP; rewrite eq_sym subr_eq sumoutpD; apply/eqP/(intro_onb o)=>i.
by rewrite lfunE sumoutp_apply/=; case: (ff i); rewrite ?addr0 ?add0r scale1r.
Qed. 

Lemma espace1N (A : 'End(U)) :
  A \is normallf -> A \o A = \1 ->
    espace1 (- A) = (~` espace1 A)%HS.
Proof. by move=>P1 P2; move: (normallf_idem_dec P1 P2)=>[o][fo]->; apply/espace1N_sumoutp. Qed.

End ESpaceCmplt.

Section ProjectiveMeas.
Variable (U : chsType).

Definition measure_proj (P : {hspace U}) : bool -> 'End(U) :=
  fun b : bool => if b then (~` P)%HS else P.
Lemma measure_proj_tp P : 
  trace_presv (@measure_proj P).
Proof.
by rewrite /trace_presv big_bool/= /measure_proj !hermf_adjE !projf_idem
  addrC hs2lfE addrC subrK.
Qed.
HB.instance Definition _ (P : {hspace U}) := 
  isQMeasure.Build _ _ bool (@measure_proj P) (@measure_proj_tp P).

Lemma elemso_projTE (P : {hspace U}) : 
  elemso (measure_proj P) true = formso (~` P)%HS.
Proof. by rewrite /elemso /measure_proj. Qed.
Lemma elemso_projFE (P : {hspace U}) : 
  elemso (measure_proj P) false = formso P.
Proof. by rewrite /elemso /measure_proj. Qed.

End ProjectiveMeas.
