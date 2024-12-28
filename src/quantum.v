(* -------------------------------------------------------------------- *)
(* Change numClosedFieldType to C *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap fingroup perm.
From quantum.external Require Import spectral.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import reals signed topology normedtype sequences exp.
From mathcomp.analysis Require Import -(notations)forms.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
From mathcomp.real_closed Require Import mxtens.
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra mcaextra notation hermitian cpo mxpred extnum ctopology svd mxnorm.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(******************************************************************************)
(*                 Fundamental Concepts for Quantum Framework                 *)
(* This file gives most of the mathematical objects of quantum computation    *)
(* based on linear function representation, that is, all the things are       *)
(* defined and represented by linear maps 'Hom                                *)
(* -------------------------------------------------------------------------- *)
(* Linear function properties and subtypes. U and V are chsType.              *)
(*                   \Tr f := trace of f                                      *)
(*                 \Rank f := rank of f                                       *)
(*                    f^⟂ := complement of f, i.e., \1 - f                    *)
(* Predicates on 'End(U) / Structure notation                                 *)
(*     normallf   'FN      := Normal, i.e., f \o f^A = f^A \o f               *)
(*     hermlf     'FH      := Hermitian, i.e., f^A = f                        *)
(*     psdlf      'F+      := positive-semidefinite                           *)
(*     obslf      'FO      := observable, psdlf and f ⊑ \1                    *)
(*     denlf      'FD      := partial density operator, psdlf and \Tr f <= 1  *)
(*     den1lf     'FD1     := density operator, psdlf and \Tr f = 1           *)
(*     projlf     'FP      := projection, f \o f = f & f^A = f                *)
(*     proj1lf    'FP1     := rank 1 projection, projlf & \Rank f = 1         *)
(*     unitarylf  'FU      := unitary, f^A \o f = \1                          *)
(* Predicates on 'Hom(U,V) / Structure notation                               *)
(*     isolf      'FI      := isometry, f^A \o f = \1                         *)
(*     gisolf     'FGI     := global isometry, f^A \o f = \1 & f \o f^A = \1  *)
(*                                                                            *)
(*    normalfType U , 'FH(U)  == interface type for normal lfun               *)
(*                               The HB class is NormalLf                     *)
(*      hermfType U , 'FH(U)  == interface type for hermitian lfun            *)
(*                               The HB class is HermLf                       *)
(*       psdfType U , 'F+(U)  == interface type for positive-semidefinite lfun*)
(*                               The HB class is PsdLf                        *)
(*       obsfType U , 'FO(U)  == interface type for observable lfun           *)
(*                               The HB class is ObsLf                        *)
(*       denfType U , 'FD(U)  == interface type for partial density operator  *)
(*                               The HB class is DenLf                        *)
(*      den1fType U , 'FD1(U) == interface type for density operator          *)
(*                               The HB class is Den1Lf                       *)
(*      projfType U , 'FP(U)  == interface type for projection lfun           *)
(*                               The HB class is ProjLf                       *)
(*     proj1fType U , 'FP1(U) == interface type for rank 1 projection lfun    *)
(*                               The HB class is Proj1Lf                      *)
(*   isofType U V , 'FI(U,V)  == interface type for isometry lfun             *)
(*                               The HB class is IsoLf                        *)
(*  gisofType U V , 'FGI(U,V) == interface type for global isometry lfun      *)
(*                               The HB class is GisoLf                       *)
(*                                                                            *)
(* All above interface type are declared as                                   *)
(* subtype of 'End(U) or 'Hom(U,V) instead of their hierarchy                 *)
(* -------------------------------------------------------------------------- *)
(* super-operators: linear function from 'End(U) -> 'End(V).                  *)
(*                'SO(U,V) := type of super-operator ; coercion to 'Hom       *)
(*                     \:1 := identity super-operator (= \1)                  *)
(*                  E :o F := composition of super-operator                   *)
(*                            (E :o F)(x) = E(F(x))                           *)
(*                  E o: F := composition of super-operator                   *)
(*                            (E o: F)(x) = F(E(x))                           *)
(*               krausso f := with (f : F -> 'Hom(U,V))                       *)
(*                            build super-operator E s.t.                     *)
(*                            E x = \sum_i (f i) \o x \o (f i)^A              *)
(*                formso f := with (f : 'Hom(U,V))                            *)
(*                            build super-operator E s.t.                     *)
(*                            E x = f \o x \o f^A                             *)
(*               ifso f br := with (f : F -> 'Hom(U,V))                       *)
(*                                 (br : forall i : F, 'SO(V,W))              *)
(*                            build super-operator E s.t.                     *)
(*                            E x = \sum_i (br i) ((f i) \o x \o (f i)^A)     *)
(*                dualso E := build super-operator E^*o s.t.                  *)
(*                            \Tr (E x \o A) = \Tr (x \o (E^*o A))            *)
(*                            via choi matrix                                 *)
(*    whileso_iter M b D n := with (M : bool -> 'End(U)) (b : bool)           *)
(*                                 (D : 'SO(U)) (n : nat)                     *)
(*                            nth iteration of                                *)
(*                                ifso M (fun i => if i==b then D else 0)     *)
(*           whileso M b D := lim (whileso_iter M b D)                        *)
(*                            limit exists if trace_nincr M & D is CPTN       *)
(*   Theory between super-operator and choi matrix.                           *)
(*               so2choi E := choi matrix of super-operator E                 *)
(*               choi2so M := super-operator build from choi matrix M         *)
(*                            so2choi (choi2so M) = M                         *)
(*                            choi2so (so2choi E) = E                         *)
(*               krausop E := build the kraus operator of E                   *)
(*                            krausso (krausop E) = E if E is cpmap           *)
(* -------------------------------------------------------------------------- *)
(* Provide U V W : chsType, F : finType                                       *)
(*                                                                            *)
(*           trace_nincr f := with (f : F -> 'Hom(U,V))                       *)
(*                            trace nonincreasing, i.e.,                      *)
(*                            \sum_i ((f i)^A \o (f i)) ⊑ \1)%VF              *)
(*           trace_presv f := with (f : F -> 'Hom(U,V))                       *)
(*                            trace preserving, i.e.,                         *)
(*                            (\sum_i ((f i)^A \o (f i)) == \1)%VF            *)
(*                 cpmap E == so2choi is psdmx                                *)
(*                            E is completely positive                        *)
(*                 tnmap E == E is trace-nonincreasing, i.e.,                 *)
(*                            \Tr (E x) <= \Tr x provided 0 <= x (psdlf)      *)
(*                 tpmap E == E is trace-preserving, i.e.,                    *)
(*                            \Tr (E x) = \Tr x                               *)
(*                  cptn E == so2choi is psdmx && ptrace (so2choi ⊑ 1%:M)     *)
(*                         == cpmap E & tnmap E                               *)
(*                            E is completely positive and trace nonincreaing *)
(*                            i.e., E is CPTN                                 *)
(*                  cptp E == so2choi is psdmx && ptrace (so2choi = 1%:M)     *)
(*                         == cpmap E & tpmap E                               *)
(*                            E is completely positive and trace perserving   *)
(*                            i.e., E is CPTP                                 *)
(* -------------------------------------------------------------------------- *)
(*             'PONB(F; U) := interface type of ponbasis function f : F -> U  *)
(*                            The HB class is PONB                            *)
(*                            parital orthnormal basis, i.e.,                 *)
(*                            forall i j : F, [< f i ; f j >] = (i == j)      *)
(*              'ONB(F; U) := interface type of onbasis function f : F -> U   *)
(*                            The HB class is ONB                             *)
(*                            orthonormal basis, i.e., #|F| = dim U and       *)
(*                            forall i j : F, [< f i ; f j >] = (i == j)      *)
(*                  'PS(U) := interface type of partial state                 *)
(*                            The HB class is PartialState                    *)
(*                            [< v ; v >] <= 1, i.e., `|v| <= 1               *)
(*                  'NS(U) := interface type of normalized state              *)
(*                            The HB class is NormalState                     *)
(*                            [< v ; v >] = 1, i.e., `|v| = 1                 *)
(*             'TN(F; U,V) := interface type of trace-nonincreasing function  *)
(*                            f : F -> 'Hom(U,V), trace_nincr f               *)
(*                            The HB class is TraceNincr                      *)
(*             'QM(F; U,V) := interface type of trace-perserving function     *)
(*                            f : F -> 'Hom(U,V), trace_presv f               *)
(*                            such function also is considered as quantum     *)
(*                            measurement, i.e., POVM                         *)
(*                            The HB class is QMeasure                        *)
(*                'CP(U,V) := interface type of completely positive           *)
(*                            super-operator, i.e., cpmap                     *)
(*                            The HB class is CPMap                           *)
(*                'QO(U,V) := interface type of quantum operation, i.e.,      *)
(*                            completely positive and trace nonincreaing,     *)
(*                            cptn, i.e., cpmap & tnmap                       *)
(*                            The HB class is QOperation                      *)
(*                'QC(U,V) := interface type of quantum channel, i.e.,        *)
(*                            completely positive and trace perservingl       *)
(*                            cptp, i.e., cpmap & tpmap                       *)
(*                            The HB class is QChannel                        *)
(* -------------------------------------------------------------------------- *)
(* Topology / Vector Order                                                    *)
(*   U, 'Hom(U,V), 'SO(U,V) :   finNormedModType, CompleteNormedModule        *)
(*                        U :   hnorm (induced by inner product)              *)
(*                'Hom(U,V) :   trace norm                                    *)
(*                 'SO(U,V) :   induced trace norm, i.e., sup (`|E x| / `|x|) *)
(*                    f ⊑ g := (g - f) \is psdlf                              *)
(*                    E ⊑ F := (F - E) \is cpmap                              *)
(*   'FD(U), 'FO(U), 'QO(U) :  forms CPO (complete partial order)             *)
(* -------------------------------------------------------------------------- *)
(* Others:                                                                    *)
(*     Ranking function : define for total correctness of program             *)
(*     Provide a lot of Canonical Structure, e.g.,                            *)
(*         \1 is canonical to 'FH 'F+ 'FU 'FO 'FP                             *)
(*         and can apply theory of these structures to \1 directly            *)
(******************************************************************************)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.

Section lfunExtra.
Local Close Scope lfun_scope.

Definition lftrace (H: chsType) (f: 'End(H)) : C :=
  \tr (h2mx f).

Local Notation "\Tr f" := (@lftrace _ f).

Lemma lftrace_baseE (H: chsType) (f: 'End(H)) :
  \Tr f = \sum_i [< eb i ; f (eb i) >].
Proof. by rewrite /lftrace /mxtrace; apply eq_bigr=>i _; exact: h2mx_dec. Qed.

Lemma lftraceC (H G : chsType) (f: 'Hom(H,G)) (g: 'Hom(G,H)) :
  \Tr (f \o g) = \Tr (g \o f).
Proof. by rewrite /lftrace !h2mx_comp mxtrace_mulC. Qed.

Lemma lftrace_is_linear (H: chsType) : linear_for *%R (@lftrace H).

Proof. move=>c f g; by rewrite /lftrace !linearP/=. Qed.
HB.instance Definition _ (H: chsType) := GRing.isLinear.Build C 'End(H) C
(* Canonical lftrace_additive (H: chsType) := Additive (@lftrace_is_linear H).
Canonical lftrace_linear (H: chsType) := Linear (@lftrace_is_linear H). *)
*%R (@lftrace H) (@lftrace_is_linear H).

Lemma lftrace_adj (H: chsType) (f: 'End(H)) : \Tr f^A = (\Tr f)^*.
Proof. by rewrite /lftrace h2mx_adj mxtrace_adj. Qed.

Lemma lftrace_tr (H: chsType) (f: 'End(H)) : \Tr f^T = (\Tr f).
Proof. by rewrite /lftrace h2mx_tr mxtrace_tr. Qed. 

Lemma lftrace_conj (H: chsType) (f: 'End(H)) : \Tr f^C = (\Tr f)^*.
Proof. by rewrite conjfAT lftrace_tr lftrace_adj. Qed.

Lemma dotp_ebl (H: chsType) (u: H) i : [< eb i; u >] = ((h2c u) i 0).
Proof.
by rewrite (dec_eb u) dotp_mulmx h2c_eb adjmx_delta delta_mx_mulEr eqxx mul1r.
Qed.

Lemma dotp_ebr (H: chsType) (u: H) i : [< u; eb i >] = ((h2c u) i 0)^*.
Proof. by rewrite -conj_dotp dotp_ebl. Qed.

Lemma outp_trlf (H : chsType) (u v : H) : \Tr [> u; v <] = [< v; u >].
Proof.
rewrite lftrace_baseE dotp_mulmx mxE; apply eq_bigr=>i _.
by rewrite outpE linearZ/= dotp_ebl dotp_ebr !mxE.
Qed.
  
Lemma intro_eb (H G: chsType) (f g: 'Hom(H,G)) : 
  (forall i, f (eb i) = g (eb i)) <-> f = g.
Proof.
split=>[P|->//]; apply/lfunP=>u; rewrite (dec_eb u) !linear_sum/=.
by apply eq_bigr=>i _; rewrite !linearZ/= P.
Qed.

(* Definition delta_lf (H G: chsType) i j : 'Hom(H,G) := Hom (delta_mx j i).
Check delta_lf. *)

Lemma eb_out (H G: chsType) i j : 
  [> eb i ; eb j <] = mx2h (delta_mx i j) :> 'Hom(H,G).
Proof.
by apply/intro_eb=>k; rewrite outpE eb_dot applyfh mx2hK 
  h2c_eb mul_delta_mx_cond -[in RHS]scaler_nat linearZ/= c2h_eb.
Qed.

Lemma sumeb_out (H: chsType) : \sum_i [> eb i; eb i <] = \1%VF :> 'End(H).
Proof.
apply/h2mx_inj; rewrite h2mx1 mx1_sum_delta linear_sum;
by under eq_bigr do rewrite eb_out/= mx2hK.
Qed.

Definition delta_lf (H G: chsType) i j : 'Hom(H,G) := [> eb i; eb j <].

Lemma delta_lfE (H G: chsType) i j :
  (delta_lf i j : 'Hom(H,G)) = mx2h (delta_mx i j).
Proof. exact: eb_out. Qed.

Lemma delta_lf_eb (H G: chsType) i j k :
  (delta_lf i j : 'Hom(H,G)) (eb k) = (k == j)%:R *: eb i.
Proof. by rewrite /delta_lf outpE eb_dot eq_sym. Qed.

Lemma comp_delta_lf_cond (H G W: chsType) i j k l :
  ((delta_lf i j : 'Hom(G,W)) \o
   (delta_lf k l : 'Hom(H,G)) = (j == k)%:R *: delta_lf i l)%VF.
Proof. by rewrite /delta_lf outp_comp eb_dot. Qed.

Lemma comp_delta_lf (H G W: chsType) i j k :
  ((delta_lf i j : 'Hom(G,W)) \o (delta_lf j k : 'Hom(H,G)) = delta_lf i k)%VF.
Proof. by rewrite comp_delta_lf_cond eqxx scale1r. Qed.

Lemma trlf_deltar (H G: chsType) (f: 'Hom(H,G)) i j :
  \Tr (f \o delta_lf i j) = [< eb j; f (eb i) >].
Proof.
rewrite lftrace_baseE (bigD1 j)// big1/=.
by move=>k /negPf nkj; rewrite lfunE/= delta_lf_eb nkj scale0r !linear0.
by rewrite lfunE/= delta_lf_eb eqxx scale1r addr0.
Qed.

Lemma trlf_intror (H G: chsType) (f1 f2: 'Hom(H,G)) :
  reflect (forall g, \Tr (f1 \o g) = \Tr (f2 \o g)) (f1 == f2).
Proof.
apply/(iffP eqP)=>[->//|P]; apply/intro_eb=>/=i. apply/intro_ebl=>/= j.
by rewrite -!trlf_deltar P.
Qed.

Lemma trlf_introl (H G: chsType) (f1 f2: 'Hom(H,G)) :
  reflect (forall g, \Tr (g \o f1) = \Tr (g \o f2)) (f1 == f2).
Proof.
apply/(iffP eqP)=>[->//|P].
apply/intro_eb=>/=i. apply/intro_ebl=>/= j.
by rewrite -!trlf_deltar lftraceC P lftraceC.
Qed.

Lemma lfun_sum_delta (H G: chsType) (f: 'Hom(H,G)) :
  f = \sum_j\sum_i [< eb i; f (eb j) >] *: delta_lf i j.
Proof.
apply/h2mx_inj. rewrite [LHS]matrix_sum_delta linear_sum exchange_big/=.
apply eq_bigr=>i _; rewrite linear_sum; apply eq_bigr=>j _.
by rewrite linearZ/= delta_lfE mx2hK h2mx_dec.
Qed.

End lfunExtra.

Notation "\Tr f" := (@lftrace _ f).

Section LFunRank.
Implicit Type (U V : chsType).

Definition lfrank U V (A : 'Hom(U,V)) := \rank (h2mx A).
Notation "\Rank A" := (lfrank A).

Lemma ranklf_adj U V (A : 'Hom(U,V)) : \Rank (A^A) = \Rank A.
Proof. by rewrite /lfrank/= adj_lfun.unlock mx2hK mxrank_adj. Qed.

Lemma ranklf_conj U V (A : 'Hom(U,V)) : \Rank (A^C) = \Rank A.
Proof. by rewrite /lfrank/= conj_lfun.unlock mx2hK mxrank_conj. Qed.

Lemma ranklf_tr U V (A : 'Hom(U,V)) : \Rank (A^T) = \Rank A.
Proof. by rewrite /lfrank/= tr_lfun.unlock mx2hK mxrank_tr. Qed.

Lemma ranklf0 U V : \Rank (0 : 'Hom(U,V)) = 0%N.
Proof. by rewrite /lfrank linear0 mxrank0. Qed.

Lemma ranklf1 U : \Rank (\1 : 'End(U)) = dim U.
Proof. by rewrite /lfrank h2mx1 mxrank1. Qed.

End LFunRank.

Notation "\Rank A" := (lfrank A) : lfun_scope.

Section Lfpred.
Context (V: chsType).

Definition normallf :=
  [qualify A : 'End(V) | h2mx A \is normalmx].
Fact normallf_key : pred_key normallf. Proof. by []. Qed.
Canonical normallf_keyed := KeyedQualifier normallf_key.

Definition hermlf :=
  [qualify A : 'End(V) | h2mx A \is hermmx].
Fact hermlf_key : pred_key hermlf. Proof. by []. Qed.
Canonical hermlf_keyed := KeyedQualifier hermlf_key.

Definition psdlf :=
  [qualify A : 'End(V) | h2mx A \is psdmx].
Fact psdlf_key : pred_key psdlf. Proof. by []. Qed.
Canonical psdlf_keyed := KeyedQualifier psdlf_key.

Definition denlf :=
  [qualify A : 'End(V) | h2mx A \is denmx].
Fact denlf_key : pred_key denlf. Proof. by []. Qed.
Canonical denlf_keyed := KeyedQualifier denlf_key.

Definition obslf :=
  [qualify A : 'End(V) | h2mx A \is obsmx].
Fact obslf_key : pred_key obslf. Proof. by []. Qed.
Canonical obslf_keyed := KeyedQualifier obslf_key.

Definition bound1lf (W : chsType) :=
  [qualify A : 'Hom(V,W) | (h2mx A)^*t *m h2mx A \is obsmx].
Fact bound1lf_key W : pred_key (bound1lf W). Proof. by []. Qed.
Canonical bound1lf_keyed W := KeyedQualifier (bound1lf_key W).

Definition isolf (W : chsType) :=
  [qualify A : 'Hom(V,W) | (h2mx A)^*t \is unitarymx].
Fact isolf_key W : pred_key (@isolf W). Proof. by []. Qed.
Canonical isolf_keyed W := KeyedQualifier (@isolf_key W).

Definition gisolf (W : chsType) :=
  [qualify A : 'Hom(V,W) | ((h2mx A)^*t \is unitarymx) && (h2mx A \is unitarymx)].
Fact gisolf_key W : pred_key (@gisolf W). Proof. by []. Qed.
Canonical gisolf_keyed W := KeyedQualifier (@gisolf_key W).

(* Definition unitarylf :=
  [qualify A : 'End(V) | h2mx A \is unitarymx].
Fact unitarylf_key : pred_key unitarylf. Proof. by []. Qed.
Canonical unitarylf_keyed := KeyedQualifier unitarylf_key. *)

Definition den1lf :=
  [qualify A : 'End(V) | h2mx A \is den1mx].
Fact den1lf_key : pred_key den1lf. Proof. by []. Qed.
Canonical den1lf_keyed := KeyedQualifier den1lf_key.

Definition projlf :=
  [qualify A : 'End(V) | h2mx A \is projmx].
Fact projlf_key : pred_key projlf. Proof. by []. Qed.
Canonical projlf_keyed := KeyedQualifier projlf_key.

Definition proj1lf :=
  [qualify A : 'End(V) | h2mx A \is proj1mx].
Fact proj1lf_key : pred_key proj1lf. Proof. by []. Qed.
Canonical proj1lf_keyed := KeyedQualifier proj1lf_key.

Lemma hermlf_normal A : A \is hermlf -> A \is normallf.
Proof. by rewrite qualifE [in X in _-> X]qualifE=>/hermmx_normal. Qed.

Lemma psdlf_herm A : A \is psdlf -> A \is hermlf.
Proof. by rewrite qualifE [in X in _-> X]qualifE=>/psdmx_herm. Qed.
Lemma psdlf_normal A : A \is psdlf -> A \is normallf.
Proof. by move=>/psdlf_herm/hermlf_normal. Qed.

Lemma obslf_bound1 A : A \is obslf -> A \is (bound1lf _).
Proof.
rewrite [in X in X->_]qualifE [in X in _-> X]qualifE=>P1.
rewrite obsmx_psd_eq; apply/andP; split; first by apply: formV_psd.
move: {+}P1=>/obsmxP[]/hermmx_normal/eigen_dec {2 3}-> Pu.
rewrite !adjmxM adjmxK !mulmxA mulmxKtV ?eigen_unitarymx=>[//|//|].
move: (eigen_unitarymx (h2mx A))=>/unitarymxP; rewrite -adjmxE=><-.
rewrite mulmxACA -[X in X *m _ - _]mulmx1 -mulmxBl -mulmxBr -diag_const_mx.
rewrite diag_mx_adj diag_mx_dmul -linearB/=.
apply: nneg_form. apply/nnegmxP=>i j; rewrite !ord1 !mxE.
move: Pu=>/uintmxP=>/(_ 0 j)/andP[] P2 P3.
by rewrite nnegrE -normCKC subr_ge0 expr_le1// ger0_norm.
Qed.
Lemma obslf_psd A : A \is obslf -> A \is psdlf.
Proof. by rewrite [in X in X->_]qualifE [in X in _-> X]qualifE=>/obsmx_psd. Qed.
Lemma obslf_herm A : A \is obslf -> A \is hermlf.
Proof. by move=>/obslf_psd/psdlf_herm. Qed.
Lemma obslf_normal A : A \is obslf -> A \is normallf.
Proof. by move=>/obslf_herm/hermlf_normal. Qed.
Lemma psdlf_bound1lf_obs A : A \is psdlf -> A \is (bound1lf _) -> A \is obslf.
Proof.
rewrite [in X in X->_]qualifE [in X in _ -> X -> _]qualifE [in X in _ -> _ -> X]qualifE.
move=>P1 P2. apply/obsmxP; split. by apply/psdmx_herm/P1.
move: P2=>/obsmxP[] _.
move: (erefl ((h2mx A)^*t *m h2mx A)).
move: {+}P1=>/psdmx_herm/hermmx_normal/eigen_dec{1 2}->.
rewrite !adjmxM !mulmxA mulmxKtV ?eigen_unitarymx=>[//|//|].
rewrite mulmxACA diag_mx_adj diag_mx_dmul.
have P3: (eigenmx (h2mx A))^*t \is unitarymx by rewrite trmxC_unitary eigen_unitarymx.
move=>/(spectral_unique P3)[s <-]/uintmxP/(_ 0) Pj.
apply/uintmxP=>i j; rewrite ord1.
move: (Pj (s^-1 j)%g); rewrite !mxE permKV -normCKC expr_le1// =>/andP[] _.
move: P1=>/psdmxP[] _/nnegmxP/(_ 0 j); rewrite nnegrE=>P1.
by rewrite P1/= ger0_norm.
Qed.

Lemma denlf_obs A : A \is denlf -> A \is obslf.
Proof. by rewrite qualifE [in X in _-> X]qualifE=>/denmx_obs. Qed.
Lemma denlf_psd A : A \is denlf -> A \is psdlf.
Proof. by move=>/denlf_obs/obslf_psd. Qed.
Lemma denlf_herm A : A \is denlf -> A \is hermlf.
Proof. by move=>/denlf_psd/psdlf_herm. Qed.
Lemma denlf_normal A : A \is denlf -> A \is normallf.
Proof. by move=>/denlf_herm/hermlf_normal. Qed.
Lemma denlf_bound1 A : A \is denlf -> A \is (bound1lf _).
Proof. by move=>/denlf_obs/obslf_bound1. Qed.

Lemma den1lf_den A : A \is den1lf -> A \is denlf.
Proof. by rewrite qualifE [in X in _-> X]qualifE=>/den1mx_den. Qed.
Lemma den1lf_psd A : A \is den1lf -> A \is psdlf.
Proof. by move=>/den1lf_den/denlf_psd. Qed.
Lemma den1lf_obs A : A \is den1lf -> A \is obslf.
Proof. by move=>/den1lf_den/denlf_obs. Qed.
Lemma den1lf_herm A : A \is den1lf -> A \is hermlf.
Proof. by move=>/den1lf_den/denlf_herm. Qed.
Lemma den1lf_normal A : A \is den1lf -> A \is normallf.
Proof. by move=>/den1lf_herm/hermlf_normal. Qed.
Lemma den1lf_bound1 A : A \is den1lf -> A \is (bound1lf _).
Proof. by move=>/den1lf_obs/obslf_bound1. Qed.

Lemma projlf_obs A : A \is projlf -> A \is obslf.
Proof. by rewrite [in X in X->_]qualifE [in X in _-> X]qualifE=>/projmx_obs. Qed.
Lemma projlf_psd A : A \is projlf -> A \is psdlf.
Proof. by move=>/projlf_obs/obslf_psd. Qed.
Lemma projlf_herm A : A \is projlf -> A \is hermlf.
Proof. by move=>/projlf_obs/obslf_herm. Qed.
Lemma projlf_normal A : A \is projlf -> A \is normallf.
Proof. by move=>/projlf_herm/hermlf_normal. Qed.
Lemma projlf_bound1 A : A \is projlf -> A \is (bound1lf _).
Proof. by move=>/projlf_obs/obslf_bound1. Qed.

Lemma proj1lf_den1 A : A \is proj1lf -> A \is den1lf.
Proof. by rewrite qualifE [in X in _-> X]qualifE=>/proj1mx_den1. Qed.
Lemma proj1lf_proj A : A \is proj1lf ->  A \is projlf.
Proof. by rewrite qualifE [in X in _-> X]qualifE=>/proj1mx_proj. Qed.
Lemma proj1lf_den A : A \is proj1lf -> A \is denlf.
Proof. by move=>/proj1lf_den1/den1lf_den. Qed.
Lemma proj1lf_psd A : A \is proj1lf -> A \is psdlf.
Proof. by move=>/proj1lf_den/denlf_psd. Qed.
Lemma proj1lf_obs A : A \is proj1lf -> A \is obslf.
Proof. by move=>/proj1lf_den/denlf_obs. Qed.
Lemma proj1lf_herm A : A \is proj1lf -> A \is hermlf.
Proof. by move=>/proj1lf_den/denlf_herm. Qed.
Lemma proj1lf_normal A : A \is proj1lf -> A \is normallf.
Proof. by move=>/proj1lf_herm/hermlf_normal. Qed.
Lemma proj1lf_bound1 A : A \is proj1lf -> A \is (bound1lf _).
Proof. by move=>/proj1lf_obs/obslf_bound1. Qed.

Lemma isolf_bound1 (W : chsType) B : B \is isolf W -> B \is bound1lf W.
Proof.
rewrite [in X in X -> _]qualifE [in X in _-> X]qualifE.
by move=>/unitarymxP; rewrite -adjmxE adjmxK=>->; rewrite obsmx1.
Qed.
Lemma isolf_normal A : A \is isolf V -> A \is normallf.
Proof.
by rewrite [in X in X -> _]qualifE [in X in _-> X]qualifE
trmxC_unitary=>/unitarymx_normal.
Qed.
Lemma isolf_giso A : A \is isolf V -> A \is gisolf V.
Proof.
by rewrite [in X in X -> _]qualifE [in X in _-> X]qualifE
trmxC_unitary=>->.
Qed.

Lemma gisolf_iso (W : chsType) B : B \is gisolf W -> B \is isolf W.
Proof.
by rewrite [in X in X -> _]qualifE [in X in _-> X]qualifE=>/andP[].
Qed.
Lemma gisolf_bound1 (W : chsType) B : B \is gisolf W -> B \is bound1lf W.
Proof. by move=>/gisolf_iso/isolf_bound1. Qed.

Lemma den1lf_projlf_proj1 A : A \is den1lf -> A \is projlf ->  A \is proj1lf.
Proof.
rewrite qualifE [in X in _-> X]qualifE=>/den1mxP[]P1 /eqP P2 P3.
by move: (projmx_tr P3)=>/esym/eqP; rewrite P2 pnatr_eq1=>P4;
rewrite qualifE; apply/proj1mxP.
Qed.

End Lfpred.

Arguments normallf {V}.
Arguments hermlf {V}.
Arguments psdlf {V}.
Arguments denlf {V}.
Arguments bound1lf {V W}.
Arguments obslf {V}.
Arguments isolf {V W}.
Arguments gisolf {V W}.
Arguments den1lf {V}.
Arguments projlf {V}.
Arguments proj1lf {V}.
Definition unitarylf {V : chsType} := @isolf V V.

Lemma unitarylf_bound1 (V : chsType) (A : 'End(V)) :
  A \is unitarylf -> A \is bound1lf.
Proof. exact: isolf_bound1. Qed.

Lemma unitarylf_iso (V : chsType) (A : 'End(V)) :
  A \is unitarylf -> A \is isolf.
Proof. by []. Qed.

Lemma unitarylf_giso (V : chsType) (A : 'End(V)) :
  A \is unitarylf -> A \is gisolf.
Proof. exact: isolf_giso. Qed.

Lemma isolf_unitary (V : chsType) (A : 'End(V)) :
  A \is isolf -> A \is unitarylf.
Proof. by []. Qed.

Lemma isolf_le_dim (U V : chsType)  (A : 'Hom(U,V)) : 
  A \is isolf -> (dim U <= dim V)%N.
Proof. by rewrite qualifE=>/unitary_dim. Qed.

Lemma gisolf_unitary (V : chsType) (A : 'End(V)) :
  A \is gisolf -> A \is unitarylf.
Proof. exact: gisolf_iso. Qed.

Lemma gisolf_eq_dim (U V : chsType) (A : 'Hom(U,V)) : 
  A \is gisolf -> dim U = dim V.
Proof.
rewrite qualifE=>/andP[]/mxrank_unitary{6}<-/mxrank_unitary{3}<-.
by rewrite mxrank_adj.
Qed.

Lemma isolf_giso_dim (U V : chsType) (A : 'Hom(U,V)) :
  A \is isolf -> dim U = dim V -> A \is gisolf.
Proof.
rewrite qualifE [in X in _ -> _ -> X]qualifE=>+ Pd.
set mA := h2mx A; move: mA; case: (dim V) / Pd => mA.
by rewrite trmxC_unitary=>->.
Qed.

Lemma ranklf_BIr {U V W : chsType} (A : 'Hom(U,V)) (B : 'Hom(W,U)) :
  B \is gisolf -> \Rank (A \o B) = \Rank A.
Proof.
move=>PB; move: (gisolf_eq_dim PB)=>/esym Pd.
move: PB; rewrite qualifE /lfrank h2mx_comp.
set mb := h2mx B; move: mb; case: (dim W) / Pd => mb /andP [] _.
by apply: mxrank_mulmxU.
Qed.

Lemma ranklf_Il {U V W : chsType} (A : 'Hom(U,V)) (B : 'Hom(V,W)) :
  B \is isolf -> \Rank (B \o A) = \Rank A.
Proof.
rewrite qualifE /lfrank h2mx_comp -mxrank_adj adjmxM=>/mxrank_unitary P1.
by rewrite mxrankMfree ?mxrank_adj// /row_free P1.
Qed. 

Lemma rankUlf {U V : chsType} (A : 'Hom(U,V)) (B : 'End(V)) :
  B \is unitarylf -> \Rank (B \o A) = \Rank A.
Proof. by exact: ranklf_Il. Qed.

Lemma ranklfU {U V : chsType} (A : 'Hom(U,V)) (B : 'End(U)) :
  B \is unitarylf -> \Rank (A \o B) = \Rank A.
Proof. by move=>/unitarylf_giso; exact: ranklf_BIr. Qed.

(* lfun hierarchy *)
HB.mixin Record isNormalLf (V : chsType) (f : 'End(V)) :=
  { is_normallf : f \is normallf}.

#[short(type="normalfType")]
HB.structure Definition NormalLf (V : chsType) := 
  { f of isNormalLf V f}.

HB.mixin Record Normal_isHermLf (V : chsType) f of NormalLf V f :=
  { is_hermlf : f \is hermlf}.

#[short(type="hermfType")]
HB.structure Definition HermLf (V : chsType) := 
  { f of NormalLf V f & Normal_isHermLf V f}.

HB.mixin Record Herm_isPsdLf (V : chsType) f of HermLf V f :=
  { is_psdlf : f \is psdlf}.

#[short(type="psdfType")]
HB.structure Definition PsdLf (V : chsType) := 
  { f of HermLf V f & Herm_isPsdLf V f}.

HB.mixin Record isBound1Lf (U V : chsType) (f : 'Hom(U,V)) :=
  { is_bound1lf : f \is bound1lf}.

#[short(type="bound1fType")]
HB.structure Definition Bound1Lf (U V : chsType) := 
  { f of isBound1Lf U V f}.

#[short(type="obsfType")]
HB.structure Definition ObsLf (V : chsType) := 
  { f of PsdLf V f & @Bound1Lf V V f}.

HB.mixin Record Obs_isDenLf (V : chsType) f of ObsLf V f :=
  { is_denlf : f \is denlf}.

#[short(type="denfType")]
HB.structure Definition DenLf (V : chsType) := 
  { f of ObsLf V f & Obs_isDenLf V f}.

HB.mixin Record Den_isDen1Lf (V : chsType) f of DenLf V f :=
  { is_den1lf : f \is den1lf}.

#[short(type="den1fType")]
HB.structure Definition Den1Lf (V : chsType) := 
  { f of DenLf V f & Den_isDen1Lf V f}.

HB.mixin Record Obs_isProjLf (V : chsType) f of ObsLf V f :=
  { is_projlf : f \is projlf}.

#[short(type="projfType")]
HB.structure Definition ProjLf (V : chsType) := 
  { f of ObsLf V f & Obs_isProjLf V f}.

#[short(type="proj1fType")]
HB.structure Definition Proj1Lf (V : chsType) := 
  { f of ProjLf V f & Den1Lf V f}.

HB.mixin Record Bound1_isIsoLf (U V : chsType) f of @Bound1Lf U V f :=
  { is_isolf : f \is isolf}.

#[short(type="isofType")]
HB.structure Definition IsoLf (U V : chsType) := 
  { f of @Bound1Lf U V f & Bound1_isIsoLf U V f}.

HB.mixin Record Iso_isGisoLf (U V : chsType) f of @IsoLf U V f :=
  { is_gisolf : f \is gisolf}.

#[short(type="gisofType")]
HB.structure Definition GisoLf (U V : chsType) := 
  { f of @IsoLf U V f & @Iso_isGisoLf U V f}.

#[non_forgetful_inheritance]
HB.instance Definition _ (U : chsType) (f : isofType U U) := 
  isNormalLf.Build U f (isolf_normal (@is_isolf _ _ f)).

#[non_forgetful_inheritance]
HB.instance Definition _ (U : chsType) (f : gisofType U U) := 
  isNormalLf.Build U f (isolf_normal (@is_isolf _ _ f)).

(* factories *)
HB.factory Record isHermLf (U : chsType) (f : 'End(U)) := {
  is_hermlf : f \is hermlf;
}.
HB.builders Context U f of isHermLf U f.
  HB.instance Definition _ := isNormalLf.Build U f (hermlf_normal is_hermlf).
  HB.instance Definition _ := Normal_isHermLf.Build U f is_hermlf.
HB.end.

HB.factory Record isPsdLf (U : chsType) (f : 'End(U)) := {
  is_psdlf : f \is psdlf;
}.
HB.builders Context U f of isPsdLf U f.
  HB.instance Definition _ := isHermLf.Build U f (psdlf_herm is_psdlf).
  HB.instance Definition _ := Herm_isPsdLf.Build U f is_psdlf.
HB.end.

HB.factory Record Psd_isObsLf (U : chsType) f of PsdLf U f :=
  { is_obslf : f \is obslf}.
HB.builders Context U f of Psd_isObsLf U f.
  HB.instance Definition _ := isBound1Lf.Build U U f (obslf_bound1 is_obslf).
  HB.instance Definition _ := ObsLf.Class (PsdLf.on f) (Bound1Lf.on f).
HB.end.

HB.factory Record isObsLf (U : chsType) (f : 'End(U)) := {
  is_obslf : f \is obslf;
}.
HB.builders Context U f of isObsLf U f.
  HB.instance Definition _ := isPsdLf.Build U f (obslf_psd is_obslf).
  HB.instance Definition _ := Psd_isObsLf.Build U f is_obslf.
HB.end.

HB.factory Record isDenLf (U : chsType) (f : 'End(U)) := {
  is_denlf : f \is denlf;
}.
HB.builders Context U f of isDenLf U f.
  HB.instance Definition _ := isObsLf.Build U f (denlf_obs is_denlf).
  HB.instance Definition _ := Obs_isDenLf.Build U f is_denlf.
HB.end.

HB.factory Record isDen1Lf (U : chsType) (f : 'End(U)) := {
  is_den1lf : f \is den1lf;
}.
HB.builders Context U f of isDen1Lf U f.
  HB.instance Definition _ := isDenLf.Build U f (den1lf_den is_den1lf).
  HB.instance Definition _ := Den_isDen1Lf.Build U f is_den1lf.
HB.end.

HB.factory Record isProjLf (U : chsType) (f : 'End(U)) := {
  is_projlf : f \is projlf;
}.
HB.builders Context U f of isProjLf U f.
  HB.instance Definition _ := isObsLf.Build U f (projlf_obs is_projlf).
  HB.instance Definition _ := Obs_isProjLf.Build U f is_projlf.
HB.end.

HB.factory Record isProj1Lf (U : chsType) (f : 'End(U)) := {
  is_proj1lf : f \is proj1lf;
}.
HB.builders Context U f of isProj1Lf U f.
  HB.instance Definition _ := isDen1Lf.Build U f (proj1lf_den1 is_proj1lf).
  HB.instance Definition _ := Obs_isProjLf.Build U f (proj1lf_proj is_proj1lf).
HB.end.

HB.factory Record isIsoLf (U V : chsType) (f : 'Hom(U,V)) := {
  is_isolf : f \is isolf;
}.
HB.builders Context U V f of isIsoLf U V f.
  HB.instance Definition _ := isBound1Lf.Build U V f (isolf_bound1 is_isolf).
  HB.instance Definition _ := Bound1_isIsoLf.Build U V f is_isolf.
HB.end.

HB.factory Record isGisoLf (U V : chsType) (f : 'Hom(U,V)) := {
  is_gisolf : f \is gisolf;
}.
HB.builders Context U V f of isGisoLf U V f.
  HB.instance Definition _ := isIsoLf.Build U V f (gisolf_iso is_gisolf).
  HB.instance Definition _ := Iso_isGisoLf.Build U V f is_gisolf.
HB.end.

HB.factory Record isUnitaryLf (U : chsType) (f : 'End(U)) := {
  is_unitarylf : f \is unitarylf;
}.
HB.builders Context U f of isUnitaryLf U f.
  HB.instance Definition _ := isGisoLf.Build U U f (unitarylf_giso is_unitarylf).
  HB.instance Definition _ := isNormalLf.Build U f (isolf_normal is_unitarylf).
HB.end.

Section LfSubType.
Variable (U V : chsType).

Section LfBuild.
Variable (x : 'End(U)) (y : 'Hom(U,V)).

Definition NormalLf_Build (H : x \is normallf) :=
  NormalLf.Pack (NormalLf.Class (isNormalLf.Axioms_ x H)).
Definition HermLf_Build (H : x \is hermlf) :=
  HermLf.Pack (HermLf.Class (Normal_isHermLf.Axioms_ 
    (isNormalLf.Axioms_ x (hermlf_normal H)) H)).
Definition PsdLf_Build (H : x \is psdlf) :=
  PsdLf.Pack (PsdLf.Class (Herm_isPsdLf.Axioms_ (Normal_isHermLf.Axioms_ 
  (isNormalLf.Axioms_ x (psdlf_normal H)) (psdlf_herm H)) H)).
Definition ObsLf_Build (H : x \is obslf) :=
  ObsLf.Pack (ObsLf.Class (Herm_isPsdLf.Axioms_ (Normal_isHermLf.Axioms_ 
  (isNormalLf.Axioms_ x (obslf_normal H)) (obslf_herm H)) (obslf_psd H)) 
  (isBound1Lf.Axioms_ _ x (obslf_bound1 H))).
Definition DenLf_Build (H : x \is denlf) :=
  DenLf.Pack (DenLf.Class (@Obs_isDenLf.Axioms_ _ _ _ _
  (Herm_isPsdLf.Axioms_ (Normal_isHermLf.Axioms_ (isNormalLf.Axioms_ x 
  (denlf_normal H)) (denlf_herm H)) (denlf_psd H))
  (isBound1Lf.Axioms_ _ x (denlf_bound1 H)) H)).
Definition Den1Lf_Build (H : x \is den1lf) :=
  Den1Lf.Pack (Den1Lf.Class (Den_isDen1Lf.Axioms_
  (@Obs_isDenLf.Axioms_ _ _ _ _
  (Herm_isPsdLf.Axioms_ (Normal_isHermLf.Axioms_ (isNormalLf.Axioms_ x 
  (den1lf_normal H)) (den1lf_herm H)) (den1lf_psd H))
  (isBound1Lf.Axioms_ _ x (den1lf_bound1 H)) (den1lf_den H)) H)).
Definition ProjLf_Build (H : x \is projlf) :=
  ProjLf.Pack (ProjLf.Class (@Obs_isProjLf.Axioms_ _ _ _ _ 
  (Herm_isPsdLf.Axioms_ (Normal_isHermLf.Axioms_ (isNormalLf.Axioms_ x 
  (projlf_normal H)) (projlf_herm H)) (projlf_psd H))
  (isBound1Lf.Axioms_ _ x (projlf_bound1 H)) H)).
Definition Proj1Lf_Build (H : x \is proj1lf) :=
  Proj1Lf.Pack (Proj1Lf.Class (@Obs_isProjLf.Axioms_ _ _ _ _ 
  (Herm_isPsdLf.Axioms_ (Normal_isHermLf.Axioms_ (isNormalLf.Axioms_ x 
  (proj1lf_normal H)) (proj1lf_herm H)) (proj1lf_psd H))
  (isBound1Lf.Axioms_ _ x (proj1lf_bound1 H)) (proj1lf_proj H))
  (Den_isDen1Lf.Axioms_
  (Obs_isDenLf.Axioms_ _ (proj1lf_den H)) (proj1lf_den1 H))).
Definition Bound1Lf_Build (H : y \is bound1lf) :=
  Bound1Lf.Pack (Bound1Lf.Class (isBound1Lf.Axioms_ _ y H)).
Definition IsoLf_Build (H : y \is isolf) :=
  IsoLf.Pack (IsoLf.Class (Bound1_isIsoLf.Axioms_ y 
  (isBound1Lf.Axioms_ _ y (isolf_bound1 H)) H)).
Definition GisoLf_Build (H : y \is gisolf) :=
  GisoLf.Pack (GisoLf.Class (Iso_isGisoLf.Axioms_ _
  (Bound1_isIsoLf.Axioms_ y (isBound1Lf.Axioms_ _ y 
  (gisolf_bound1 H)) (gisolf_iso H)) H)).
Definition UnitaryLf_Build (H : x \is unitarylf) :=
  GisoLf.Pack (GisoLf.Class (Iso_isGisoLf.Axioms_ _
  (Bound1_isIsoLf.Axioms_ x (isBound1Lf.Axioms_ _ x 
  (unitarylf_bound1 H)) (unitarylf_iso H)) (unitarylf_giso H))).

Lemma NormalLf_BuildE (H : x \is normallf) : x = NormalLf_Build H.
Proof. by []. Qed.
Lemma HermLf_BuildE (H : x \is hermlf) : x = HermLf_Build H.
Proof. by []. Qed.
Lemma PsdLf_BuildE (H : x \is psdlf) : x = PsdLf_Build H.
Proof. by []. Qed.
Lemma Bound1Lf_BuildE (H : y \is bound1lf) : y = Bound1Lf_Build H.
Proof. by []. Qed.
Lemma ObsLf_BuildE (H : x \is obslf) : x = ObsLf_Build H.
Proof. by []. Qed.
Lemma DenLf_BuildE (H : x \is denlf) : x = DenLf_Build H.
Proof. by []. Qed.
Lemma Den1Lf_BuildE (H : x \is den1lf) : x = Den1Lf_Build H.
Proof. by []. Qed.
Lemma ProjLf_BuildE (H : x \is projlf) : x = ProjLf_Build H.
Proof. by []. Qed.
Lemma Proj1Lf_BuildE (H : x \is proj1lf) : x = Proj1Lf_Build H.
Proof. by []. Qed.
Lemma IsoLf_BuildE (H : y \is isolf) : y = IsoLf_Build H.
Proof. by []. Qed.
Lemma GisoLf_BuildE (H : y \is gisolf) : y = GisoLf_Build H.
Proof. by []. Qed.
Lemma UnitaryLf_BuildE (H : x \is unitarylf) : x = UnitaryLf_Build H.
Proof. by []. Qed.

End LfBuild.

(* subtype *)
(* we define all types as a subtype of lfun instead of their hierarchy *)
Program Definition normalf_subType := 
  @isSub.Build 'End(U) (fun f => f \is normallf) (normalfType U) 
  (@NormalLf.sort U) NormalLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_normallf _ u) (X _ (@is_normallf _ u)).
by case: u=>/= u [[Pu1]] Pu2; rewrite (eq_irrelevance Pu1 Pu2).
Qed.
HB.instance Definition _ := normalf_subType.
HB.instance Definition _ := [Equality of (normalfType U) by <:].
HB.instance Definition _ := [Choice of (normalfType U) by <:].

Program Definition hermf_subType := @isSub.Build 'End(U) 
  (fun f => f \is hermlf) (hermfType U) (@HermLf.sort U) 
  HermLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_hermlf _ u) (X _ (@is_hermlf _ u)).
by case: u=>/= u [[Pu1]] [Pu2] Pu3; 
  rewrite /HermLf_Build (eq_irrelevance Pu2 Pu3) (eq_irrelevance (_ _) Pu1).
Qed.
HB.instance Definition _ := hermf_subType.
HB.instance Definition _ := [Equality of (hermfType U) by <:].
HB.instance Definition _ := [Choice of (hermfType U) by <:].

Program Definition psdf_subType := @isSub.Build 'End(U) 
  (fun f => f \is psdlf) (psdfType U) (@PsdLf.sort U) 
  PsdLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_psdlf _ u) (X _ (@is_psdlf _ u)).
by case: u=>/= u [[Pu1]] [Pu2] [Pu3] Pu4;
  rewrite /PsdLf_Build (eq_irrelevance Pu3 Pu4)
  (eq_irrelevance (_ _) Pu1) (eq_irrelevance (_ _) Pu2).
Qed.
HB.instance Definition _ := psdf_subType.
HB.instance Definition _ := [Equality of (psdfType U) by <:].
HB.instance Definition _ := [Choice of (psdfType U) by <:].

Program Definition bound1f_subType := 
  @isSub.Build 'Hom(U,V) (fun f => f \is bound1lf) (bound1fType U V) 
  (@Bound1Lf.sort U V) Bound1Lf_Build _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_bound1lf _ _ u) (X _ (@is_bound1lf _ _ u)).
by case: u=>/= u [[Pu1]] Pu2; rewrite (eq_irrelevance Pu1 Pu2).
Qed.
HB.instance Definition _ := bound1f_subType.
HB.instance Definition _ := [Equality of (bound1fType U V) by <:].
HB.instance Definition _ := [Choice of (bound1fType U V) by <:].

Program Definition obsf_subType := @isSub.Build 'End(U) 
  (fun f => f \is obslf) (obsfType U) (@ObsLf.sort U) 
  ObsLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros.
move: (psdlf_bound1lf_obs (@is_psdlf _ u) (@is_bound1lf _ _ u))=>Pu.
by move: (X _ Pu); case: u Pu =>/= u [[Pu1]] [Pu2] [Pu3] [Pu4] Pu5;
  rewrite /ObsLf_Build (eq_irrelevance (_ _) Pu1) (eq_irrelevance (_ _) Pu2) 
    (eq_irrelevance (_ _) Pu3) (eq_irrelevance (_ _) Pu4).
Qed.
HB.instance Definition _ := obsf_subType.
HB.instance Definition _ := [Equality of (obsfType U) by <:].
HB.instance Definition _ := [Choice of (obsfType U) by <:].

Program Definition denf_subType := @isSub.Build 'End(U) 
  (fun f => f \is denlf) (denfType U) (@DenLf.sort U) 
  DenLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros. move: (@is_denlf _ u) (X _ (@is_denlf _ u)).
by case: u=>/= u [[Pu1]] [Pu2] [Pu3] [Pu4] [Pu5] Pu6;
  rewrite /DenLf_Build (eq_irrelevance Pu5 Pu6) (eq_irrelevance (_ _) Pu1) 
    (eq_irrelevance (_ _) Pu2) (eq_irrelevance (_ _) Pu3) 
    (eq_irrelevance (_ _) Pu4).
Qed.
HB.instance Definition _ := denf_subType.
HB.instance Definition _ := [Equality of (denfType U) by <:].
HB.instance Definition _ := [Choice of (denfType U) by <:].

Program Definition den1f_subType := @isSub.Build 'End(U) 
  (fun f => f \is den1lf) (den1fType U) (@Den1Lf.sort U) 
  Den1Lf_Build _ (fun _ _ => erefl).
Next Obligation.
intros. move: (@is_den1lf _ u) (X _ (@is_den1lf _ u)).
by case: u=>/= u [[Pu1]] [Pu2] [Pu3] [Pu4] [Pu5] [Pu6] Pu7;
  rewrite /Den1Lf_Build (eq_irrelevance Pu6 Pu7) (eq_irrelevance (_ _) Pu1) 
    (eq_irrelevance (_ _) Pu2) (eq_irrelevance (_ _) Pu3) 
    (eq_irrelevance (_ _) Pu4) (eq_irrelevance (_ _) Pu5).
Qed.
HB.instance Definition _ := den1f_subType.
HB.instance Definition _ := [Equality of (den1fType U) by <:].
HB.instance Definition _ := [Choice of (den1fType U) by <:].

Program Definition projf_subType := @isSub.Build 'End(U) 
  (fun f => f \is projlf) (projfType U) (@ProjLf.sort U) 
  ProjLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros. move: (@is_projlf _ u) (X _ (@is_projlf _ u)).
by case: u=>/= u [[Pu1]] [Pu2] [Pu3] [Pu4] [Pu5] Pu6;
  rewrite /ProjLf_Build (eq_irrelevance Pu5 Pu6) (eq_irrelevance (_ _) Pu1) 
    (eq_irrelevance (_ _) Pu2) (eq_irrelevance (_ _) Pu3) 
    (eq_irrelevance (_ _) Pu4).
Qed.
HB.instance Definition _ := projf_subType.
HB.instance Definition _ := [Equality of (projfType U) by <:].
HB.instance Definition _ := [Choice of (projfType U) by <:].

Program Definition proj1f_subType := @isSub.Build 'End(U) 
  (fun f => f \is proj1lf) (proj1fType U) (@Proj1Lf.sort U) 
  Proj1Lf_Build _ (fun _ _ => erefl).
Next Obligation.
intros; move: (den1lf_projlf_proj1 (@is_den1lf _ u) (@is_projlf _ u))=>Pu.
move: (X _ Pu); case: u Pu
  =>/= u [[Pu1]] [Pu2] [Pu3] [Pu4] [Pu5] [Pu6] [Pu7] Pu8.
by rewrite /Proj1Lf_Build (eq_irrelevance (_ _) Pu1)
    (eq_irrelevance (_ _) Pu2) (eq_irrelevance (_ _) Pu3) 
    (eq_irrelevance (_ _) Pu4) (eq_irrelevance (_ _) Pu5) 
    (eq_irrelevance (_ _) Pu6) (eq_irrelevance (_ _) Pu7).
Qed.
HB.instance Definition _ := proj1f_subType.
HB.instance Definition _ := [Equality of (proj1fType U) by <:].
HB.instance Definition _ := [Choice of (proj1fType U) by <:].

Program Definition isof_subType := 
  @isSub.Build 'Hom(U,V) (fun f => f \is isolf) (isofType U V) 
  (@IsoLf.sort U V) IsoLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_isolf _ _ u) (X _ (@is_isolf _ _ u)).
by case: u=>/= u [[Pu1]] [Pu2] Pu3; rewrite /IsoLf_Build 
  (eq_irrelevance Pu2 Pu3) (eq_irrelevance (_ _) Pu1).
Qed.
HB.instance Definition _ := isof_subType.
HB.instance Definition _ := [Equality of (isofType U V) by <:].
HB.instance Definition _ := [Choice of (isofType U V) by <:].

Program Definition gisof_subType := 
  @isSub.Build 'Hom(U,V) (fun f => f \is gisolf) (gisofType U V) 
  (@IsoLf.sort U V) GisoLf_Build _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_gisolf _ _ u) (X _ (@is_gisolf _ _ u)).
by case: u=>/= u [[Pu1]] [Pu2] [Pu3] Pu4; rewrite /GisoLf_Build 
  (eq_irrelevance Pu3 Pu4) (eq_irrelevance (_ _) Pu1) (eq_irrelevance (_ _) Pu2).
Qed.
HB.instance Definition _ := gisof_subType.
HB.instance Definition _ := [Equality of (gisofType U V) by <:].
HB.instance Definition _ := [Choice of (gisofType U V) by <:].

End LfSubType.

Reserved Notation "''FB1'" .
Reserved Notation "''FB1_' S"     (at level 8, S at level 2, format "''FB1_' S").
Reserved Notation "''FB1_' ( S )" (at level 8).
Reserved Notation "''FB1_' ( S , T )" (at level 8, format "''FB1_' ( S ,  T )").
Reserved Notation "''FB1[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''FB1[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FB1[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''FB1' ( S )"  (at level 8, format "''FB1' ( S )").
Reserved Notation "''FB1' ( S , T )"  (at level 8, format "''FB1' ( S ,  T )").
Reserved Notation "''FGI'" .
Reserved Notation "''FGI_' S"     (at level 8, S at level 2, format "''FGI_' S").
Reserved Notation "''FGI_' ( S )" (at level 8).
Reserved Notation "''FGI_' ( S , T )" (at level 8, format "''FGI_' ( S ,  T )").
Reserved Notation "''FGI[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''FGI[' H ]_ ( S )"     (at level 8).
Reserved Notation "''FGI[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''FGI' ( S )"  (at level 8, format "''FGI' ( S )").
Reserved Notation "''FGI' ( S , T )"  (at level 8, format "''FGI' ( S ,  T )").

Notation "''FN'  ( V )"     := (normalfType V) : type_scope.
Notation "''FH'  ( V )"     := (hermfType V) : type_scope.
Notation "''F+'  ( V )"     := (psdfType V) : type_scope.
Notation "''FB1' ( U , V )" := (bound1fType U V) : type_scope.
Notation "''FB1' ( V )"     := (bound1fType V V) : type_scope.
Notation "''FO'  ( V )"     := (obsfType V) : type_scope.
Notation "''FD'  ( V )"     := (denfType V) : type_scope.
Notation "''FI'  ( U , V )" := (isofType U V) : type_scope.
Notation "''FI'  ( V )"     := (isofType V V) (only parsing) : type_scope.
Notation "''FGI' ( U , V )" := (gisofType U V) : type_scope.
Notation "''FGI' ( V )"     := (gisofType V V) (only parsing) : type_scope.
Notation "''FU'  ( V )"     := (gisofType V V) : type_scope.
Notation "''FD1' ( V )"     := (den1fType V) : type_scope.
Notation "''FP'  ( V )"     := (projfType V) : type_scope.
Notation "''FP1' ( V )"     := (proj1fType V) : type_scope.
Notation "''FN'"  := ('FN(_))  (only parsing) : type_scope.
Notation "''FH'"  := ('FH(_))  (only parsing) : type_scope.
Notation "''F+'"  := ('F+(_))  (only parsing) : type_scope.
Notation "''FB1'"  := ('FB1(_,_))  (only parsing) : type_scope.
Notation "''FO'"  := ('FO(_))  (only parsing) : type_scope.
Notation "''FD'"  := ('FD(_))  (only parsing) : type_scope.
Notation "''FI'"  := ('FI(_,_))  (only parsing) : type_scope.
Notation "''FGI'" := ('FGI(_,_))  (only parsing) : type_scope.
Notation "''FU'"  := ('FU(_))  (only parsing) : type_scope.
Notation "''FD1'" := ('FD1(_)) (only parsing) : type_scope.
Notation "''FP'"  := ('FP(_))  (only parsing) : type_scope.
Notation "''FP1'" := ('FP1(_)) (only parsing) : type_scope.

Module LfunExports.
#[deprecated(since="mathcomp 2.0.0", note="Use NormalLf.clone instead.")]
Notation "[ 'normal' 'of' f 'as' g ]" := (NormalLf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use NormalLf.clone instead.")]
Notation "[ 'normal' 'of' f ]" := (NormalLf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use HermLf.clone instead.")]
Notation "[ 'herm' 'of' f 'as' g ]" := (HermLf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use HermLf.clone instead.")]
Notation "[ 'herm' 'of' f ]" := (HermLf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use PsdLf.clone instead.")]
Notation "[ 'psd' 'of' f 'as' g ]" := (PsdLf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use PsdLf.clone instead.")]
Notation "[ 'psd' 'of' f ]" := (PsdLf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Bound1Lf.clone instead.")]
Notation "[ 'bound1' 'of' f 'as' g ]" := (Bound1Lf.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Bound1Lf.clone instead.")]
Notation "[ 'bound1' 'of' f ]" := (Bound1Lf.clone _ _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ObsLf.clone instead.")]
Notation "[ 'obs' 'of' f 'as' g ]" := (ObsLf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ObsLf.clone instead.")]
Notation "[ 'obs' 'of' f ]" := (ObsLf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use DenLf.clone instead.")]
Notation "[ 'den' 'of' f 'as' g ]" := (DenLf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use DenLf.clone instead.")]
Notation "[ 'den' 'of' f ]" := (DenLf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Den1Lf.clone instead.")]
Notation "[ 'den1' 'of' f 'as' g ]" := (Den1Lf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Den1Lf.clone instead.")]
Notation "[ 'den1' 'of' f ]" := (Den1Lf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ProjLf.clone instead.")]
Notation "[ 'proj' 'of' f 'as' g ]" := (ProjLf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ProjLf.clone instead.")]
Notation "[ 'proj' 'of' f ]" := (ProjLf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Proj1Lf.clone instead.")]
Notation "[ 'proj1' 'of' f 'as' g ]" := (Proj1Lf.clone _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Proj1Lf.clone instead.")]
Notation "[ 'proj1' 'of' f ]" := (Proj1Lf.clone _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use IsoLf.clone instead.")]
Notation "[ 'iso' 'of' f 'as' g ]" := (IsoLf.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use IsoLf.clone instead.")]
Notation "[ 'iso' 'of' f ]" := (IsoLf.clone _ _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GisoLf.clone instead.")]
Notation "[ 'giso' 'of' f 'as' g ]" := (GisoLf.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GisoLf.clone instead.")]
Notation "[ 'giso' 'of' f ]" := (GisoLf.clone _ _ f _) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GisoLf.clone instead.")]
Notation "[ 'unitary' 'of' f 'as' g ]" := (GisoLf.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use GisoLf.clone instead.")]
Notation "[ 'unitary' 'of' f ]" := (GisoLf.clone _ _ f _) : form_scope.
End LfunExports.
HB.export LfunExports.

Arguments is_normallf [V] s.
Arguments is_hermlf [V] s.
Arguments is_psdlf [V] s.
Arguments is_bound1lf [U V] s.
Arguments is_denlf [V] s.
Arguments is_den1lf [V] s.
Arguments is_projlf [V] s.
Arguments is_isolf [U V] s.
Arguments is_gisolf [U V] s.

Lemma is_obslf (V : chsType) (f : 'FO(V)) : f%:VF \is obslf.
Proof. by move: (is_psdlf f) (is_bound1lf f); exact: psdlf_bound1lf_obs. Qed. 
Lemma is_unitarylf (V : chsType) (f : 'FU(V)) : f%:VF \is unitarylf.
Proof. by move: (is_isolf f)=>/isolf_unitary. Qed.
Lemma is_proj1lf (V : chsType) (f : 'FP1(V)) : f%:VF \is proj1lf.
Proof. by move: (is_den1lf f) (is_projlf f); exact: den1lf_projlf_proj1. Qed.  

Section LfPredReflect.
Variable (V: chsType) (A : 'End(V)).
Implicit Type (U W T: chsType).

Lemma lf_psd_decomp :
  exists (M1 M2 M3 M4 : 'End(V)) , M1 \is psdlf /\ M2 \is psdlf 
  /\ M3 \is psdlf /\ M4 \is psdlf /\ A = M1 - M2 + 'i *: M3 - 'i *: M4.
Proof.
move: (mx_psd_decomp (h2mx A))=>[M1 [M2 [M3 [M4]]]] [P1 [P2 [P3 [P4]]]] P5.
exists (mx2h M1). exists (mx2h M2). exists (mx2h M3). exists (mx2h M4).
do ? split.
1,2,3,4: by rewrite qualifE/= mx2hK ?P1 ?P2 ?P3 ?P4.
by rewrite -linearB/= -!linearZ/= -!linearD/= -linearB/= -P5 h2mxK.
Qed.

Lemma normallfP : reflect (A \o A^A = A^A \o A) (A \is normallf).
Proof.
rewrite qualifE adj_lfun.unlock;
apply/(iffP idP)=>[/normalmxP P|/(f_equal h2mx)].
by apply/h2mx_inj; rewrite !h2mx_comp mx2hK P.
by rewrite !h2mx_comp mx2hK=>/normalmxP.
Qed.

Lemma normallfE : (A \is normallf) = (A \o A^A == A^A \o A).
Proof. by apply/eqb_iff; split=>[/normallfP/eqP->|/eqP/normallfP]. Qed.

Lemma isolfP U W (B : 'Hom(U,W)) :
  reflect (B^A \o B = \1) (B \is isolf).
Proof.
rewrite qualifE adj_lfun.unlock;
apply/(iffP idP)=>[/unitarymxP P|/(f_equal h2mx)].
by apply/h2mx_inj; rewrite h2mx_comp h2mx1 mx2hK -P -adjmxE adjmxK.
by rewrite h2mx_comp mx2hK h2mx1 -[X in _ *m X]adjmxK=>/unitarymxP.
Qed.

Lemma isolfE U W (B : 'Hom(U,W)) : (B \is isolf) = (B^A \o B == \1).
Proof. by apply/eqb_iff; split=>[/isolfP/eqP->|/eqP/isolfP]. Qed.

Lemma gisolf_isoP U W (B : 'Hom(U,W)) :
  reflect (B \is isolf /\ B^A \is isolf) (B \is gisolf).
Proof.
rewrite ![_ \is isolf]qualifE ![_ \is gisolf]qualifE
  adj_lfun.unlock mx2hK adjmxK.
by apply/(iffP andP).
Qed.

Lemma gisolf_isoE U W (B : 'Hom(U,W)) :
  (B \is gisolf) = (B \is isolf) && (B^A \is isolf).
Proof. by apply/eqb_iff; split=>[/gisolf_isoP[]->->|/andP/gisolf_isoP]. Qed.

Lemma gisolfP U W (B : 'Hom(U,W)) :
  reflect (B^A \o B = \1 /\ B \o B^A = \1) (B \is gisolf).
Proof.
apply/(iffP (gisolf_isoP _))=>[[/isolfP->/isolfP<-]|[]/isolfP->];
by rewrite ?adjfK// -{1}[B]adjfK=>/isolfP->.
Qed.  

Lemma gisolfE (W : chsType) (B : 'Hom(V,W)) : 
  (B \is gisolf) = (B^A \o B == \1) && (B \o B^A == \1).
Proof. by rewrite gisolf_isoE !isolfE adjfK. Qed.

Lemma hermlfP : reflect (A^A = A) (A \is hermlf).
Proof.
rewrite qualifE adj_lfun.unlock; apply/(iffP idP)=>[/hermmxP <-|/(f_equal h2mx)].
by rewrite h2mxK. by rewrite mx2hK=>/esym/hermmxP.
Qed.

Lemma hermlfE : (A \is hermlf) = (A^A == A).
Proof. by apply/eqb_iff; split=>[/hermlfP/eqP->|/eqP/hermlfP]. Qed.

Lemma psdlfP : 
  reflect (forall v, [< v ; A v>] >= 0) (A \is psdlf). 
Proof.
apply (iffP idP); rewrite qualifE.
move=>/psdmx_dot P v. move: P =>/(_ (h2c v)).
2: move=>P; apply/psdmx_dot=>u; move: (P (c2h u))%VF.
all: by rewrite nnegrE dotp_mulmx applyfh !c2hK trace_mx11 mulmxA.
Qed.

Lemma hermlf_trlf : A \is hermlf -> \Tr A \is Num.real.
Proof.
rewrite qualifE=>P1; rewrite lftrace_baseE; apply/sum_real=>i _.
move: P1=>/hermmx_dot/(_ (delta_mx i 0)).
by rewrite dotp_mulmx/= applyfh h2c_eb c2hK mulmxA trace_mx11.
Qed.

Lemma psdlf_trlf : A \is psdlf -> 0 <= \Tr A.
Proof. by move/psdlfP=>P; rewrite lftrace_baseE sumr_ge0. Qed.

Lemma denlfP : reflect (A \is psdlf /\ \Tr A <= 1) (A \is denlf). 
Proof.
by rewrite qualifE [_ \is denlf]qualifE /lftrace;
apply (iffP (denmxP _)).
Qed.

Lemma denlf_trlf : A \is denlf -> \Tr A <= 1.
Proof. by move=>/denlfP[]. Qed.

Lemma obslfP : 
  reflect (A \is psdlf /\ forall u, [<u ; A u>] <= [< u; u >]) (A \is obslf). 
Proof.
rewrite [X in reflect _ X]qualifE.
apply (iffP (obsmx_dot _))=>[P|[/psdlfP P1 P2 u]].
split. apply/psdlfP. 1,2: move=>v; move: (P (h2c v))%VF=>/andP.
3: apply/andP; move: (P1 (c2h u))%VF (P2 (c2h u))%VF.
all: rewrite !dotp_mulmx applyfh !c2hK !trace_mx11 mulmxA.
by move=>[->]. by move=>[_->]. by split.
Qed.

Lemma bound1lf_obsE U (B : 'Hom(V,U)) :
  B \is bound1lf = (B^A \o B \is obslf).
Proof. by rewrite [LHS]qualifE [RHS]qualifE h2mx_comp adj_lfun.unlock mx2hK. Qed.

Lemma unitarylfP : reflect (A^A \o A = \1) (A \is unitarylf).
Proof. by apply/(iffP (isolfP _)). Qed.

Lemma unitarylfPV : reflect (A \o A^A = \1) (A \is unitarylf).
Proof.
rewrite qualifE; apply/(iffP (unitarymxPV _))=>[P|/(f_equal h2mx)].
apply/h2mx_inj.
all: by rewrite h2mx_comp adj_lfun.unlock h2mx1 mx2hK -{1}[h2mx A]adjmxK.
Qed.

Lemma unitarylfE : (A \is unitarylf) = (A^A \o A == \1).
Proof. by apply/eqb_iff; rewrite eq_iff; split=>/unitarylfP. Qed.

Lemma unitarylfEV : (A \is unitarylf) = (A \o A^A == \1).
Proof. by apply/eqb_iff; rewrite eq_iff; split=>/unitarylfPV. Qed.

Lemma lfun_eq0P U (B : 'End(U)) : 
  reflect (forall u, [< u ; B u >] = 0) (B == 0).
Proof.
apply/(iffP eqP)=>[-> u|P]; first by rewrite lfunE/= dotp0.
apply/h2mx_inj/eqP; rewrite h2mx0; apply/mx_dot_eq0=>u.
by move: (P (c2h u)); rewrite !dotp_mulmx applyfh !c2hK mulmxA trace_mx11.
Qed.

Lemma isolf_dotP U W (B : 'Hom(U,W)) :
  reflect (forall u, [< B u ; B u>] = [< u; u >]) (B \is isolf).
Proof.
apply/(iffP (isolfP _))=>[P u|P].
  by rewrite -adj_dotEl -comp_lfunE P lfunE.
apply/subr0_eq/eqP/lfun_eq0P=>u.
by rewrite !lfunE/= lfunE/= lfunE/= lfunE/= dotpBr adj_dotEr P addrN.
Qed.

Lemma unitarylf_dotP : 
  reflect (forall u, [< A u ; A u>] = [< u; u >]) (A \is unitarylf). 
Proof. exact: isolf_dotP. Qed.

Lemma idemr_01 (T : fieldType) (x : T) : 
  (x ^+2 == x) = ((x == 0) || (x == 1)).
Proof. by rewrite -subr_eq0 -{2}(mul1r x) -mulrBl mulf_eq0 subr_eq0 orbC. Qed.

Lemma boolmx_dmul (T : numClosedFieldType) m n (M : 'M[T]_(m,n)) :
  M \is a boolmx <-> M .* M = M.
split.
move=>/boolmxP P; apply/matrixP=> i j; rewrite mxE.
by move: (P i j); rewrite -idemr_01 expr2=>/eqP.
move=>/matrixP P; apply/boolmxP=> i j.
by move: (P i j)=>/eqP; rewrite mxE -expr2 idemr_01.
Qed.

Lemma projmxP_id (T : numClosedFieldType) m (B : 'M[T]_m) : 
  reflect (B \is hermmx /\ (B *m B = B)) (B \is projmx).
Proof.
apply(iffP (projmxP _))=>[[P1 P2]|[P1 P2]]; split=>//; 
move: P1=>/hermmx_normal/eigen_dec P1; [|move: P2].
  rewrite P1 !mulmxA mulmxKtV// mulmxACA diag_mx_dmul.
  by do 3 f_equal; apply/boolmx_dmul.
rewrite {1 2 3}P1 !mulmxA mulmxKtV// mulmxUC// mulmxKtV// -mulmxA mulUmx//.
by rewrite mulmxA unitarymxKV// mul1mx diag_mx_dmul=>/diag_mx_inj/boolmx_dmul.
Qed.

Lemma projlfP : reflect (A^A = A /\ (A \o A = A)) (A \is projlf).
Proof.
apply(iffP idP)=>[H0|[/hermlfP P1 P2]].
split. by apply/hermlfP/projlf_herm.
by apply/h2mx_inj; rewrite h2mx_comp; move: H0; rewrite qualifE=>/projmxP_id[_ ].
rewrite qualifE; apply/projmxP_id; split.
by move: P1; rewrite qualifE.
by move: P2=>/(f_equal h2mx); rewrite h2mx_comp.
Qed.

Lemma projlf_psdP : reflect (A \is psdlf /\ (A \o A = A)) (A \is projlf).
Proof.
apply(iffP idP)=>[H0|[P1 P2]].
by split; [apply/projlf_psd | move: H0=>/projlfP[]].
by apply/projlfP; split=>//; apply/hermlfP/psdlf_herm.
Qed.

Lemma den1lfP : reflect (A \is psdlf /\ \Tr A = 1) (A \is den1lf).
Proof.
apply(iffP idP).
by rewrite qualifE=>/den1mxP=>[[P1 /eqP P2]]; split=>[|//]; rewrite qualifE.
by rewrite qualifE /lftrace=>[[P1 P2]]; rewrite qualifE; apply/den1mxP;
  split=>//; apply/eqP.
Qed.

(* generalize bi-isolf *)
Lemma isofK U W (F : 'Hom(U,W)) (u : 'FI(U,V)) :
  F \o u^A \o u = F.
Proof.
by move: (is_isolf u)=>/isolfP; rewrite -comp_lfunA=>->;
rewrite comp_lfun1r.
Qed.

Lemma isofE U W (u : 'FI(U,W)) : u^A \o u = \1.
Proof. by apply/isolfP/is_isolf. Qed.

Lemma isofKE U W (u : 'FI(U,W)) x : u^A (u x) = x.
Proof. by rewrite -comp_lfunE isofE lfunE. Qed.

Lemma gisofKl U W (F : 'Hom(U,W)) (u : 'FGI(U,V)) :
  F \o u^A \o u = F.
Proof. by rewrite isofK. Qed.

Lemma gisofKr U W (F : 'Hom(U,W)) (u : 'FGI(V,U)) :
  F \o u \o u^A = F.
Proof.
by move: (is_gisolf u)=>/gisolfP[] _; rewrite -comp_lfunA=>->;
rewrite comp_lfun1r.
Qed.

Lemma gisofEl U W (u : 'FGI(U,W)) : u^A \o u = \1.
Proof. by rewrite isofE. Qed.

Lemma gisofEr U W (u : 'FGI(U,W)) : u \o u^A = \1.
Proof. by move: (is_gisolf u)=>/gisolfP[]. Qed.

Lemma gisofKEl U W (u : 'FGI(U,W)) x : u^A (u x) = x.
Proof. by rewrite isofKE. Qed.

Lemma gisofKEr U W (u : 'FGI(U,W)) x : u (u^A x) = x.
Proof. by rewrite -comp_lfunE gisofEr lfunE. Qed.

Lemma unitaryfKl U (F : 'Hom(V,U)) (u : 'FU(V)) :
  F \o u^A \o u = F.
Proof. exact: gisofKl. Qed.

Lemma unitaryfKr U (F : 'Hom(V,U)) (u : 'FU(V)) :
  F \o u \o u^A = F.
Proof. exact: gisofKr. Qed.

Lemma unitaryfEl (u : 'FU(V)) : u^A \o u = \1.
Proof. by rewrite isofE. Qed.

Lemma unitaryfEr (u : 'FU(V)) : u \o u^A = \1.
Proof. by rewrite gisofEr. Qed.

Lemma unitaryfKEl (u : 'FU(V)) x : u^A (u x) = x.
Proof. exact: gisofKEl. Qed.

Lemma unitaryfKEr (u : 'FU(V)) x : u (u^A x) = x.
Proof. exact: gisofKEr. Qed.

Lemma isof_inj U (u : 'FI(V,U)) : injective u.
Proof. by move=>x y /(f_equal u^A); rewrite !isofKE. Qed.

Lemma gisof_bij U (u : 'FGI(V,U)) : bijective u.
Proof. by exists (u^A)=>x; rewrite ?gisofKEl ?gisofKEr. Qed.

Lemma unitaryf_inj (u : 'FU(V)) : injective u.
Proof. exact: isof_inj. Qed.

Lemma unitaryf_bij (u : 'FU(V)) : bijective u.
Proof. exact: gisof_bij. Qed.

End LfPredReflect.

Arguments isof_inj {V U u}.
Arguments gisof_bij {V U u}.
Arguments unitaryf_inj {V u}.
Arguments unitaryf_bij {V u}.

Lemma hnorm_l2norm (W : chsType) (v : W) :
  `| v | = l2norm (h2c v).
Proof.
rewrite /normr/= /hnorm dotp_mulmx mxE l2normE exchange_big big_ord1. 
by f_equal; apply eq_bigr=>i _; rewrite !mxE normCKC.
Qed.

Lemma bound1lfP (U V : chsType) (B : 'Hom(U, V)) :
  reflect (forall u, [<B u ; B u>] <= [< u; u >]) (B \is bound1lf).
Proof.
rewrite bound1lf_obsE; apply/(iffP (obslfP _)).
by move=>[] _ ? u; rewrite -adj_dotEr -comp_lfunE.
move=>?; split=>[|u]; last by rewrite lfunE/= adj_dotEr.
by rewrite qualifE h2mx_comp adj_lfun.unlock mx2hK formV_psd.
Qed.

Lemma bound1lf_normP (U V : chsType) (B : 'Hom(U, V)) :
  reflect (forall v, `|B v| <= `|v|) (B \is bound1lf).
Proof.
apply/(iffP (bound1lfP _))=>P u; move: (P u);
by rewrite !dotp_norm ler_pXn2r// ?nnegrE.
Qed.

Lemma bound1lf_i2normE (U V : chsType) (B : 'Hom(U, V)) :
  B \is bound1lf = (i2norm (h2mx B) <= 1).
Proof.
apply/eqb_iff; split.
- move=>/bound1lf_normP=>P.
  have P1 (v : 'cV_(dim U)) : l2norm (h2mx B *m v) <= l2norm v
    by move: (P (c2h v)); rewrite !hnorm_l2norm applyfh !c2hK.
  move: P1; set mB := h2mx B; move: mB.
    rewrite -dim_proper_cast -(@dim_proper_cast V)=>mB P1.
    move: (i2norm_existsr mB 0)=>[] v Pv Pm; move: (P1 v).
    by rewrite Pv Pm.
move=>P1; apply/bound1lf_normP=>v; rewrite !hnorm_l2norm applyfh c2hK.
apply/(le_trans (i2norm_dotr _ _))/ler_piMl=>//; apply: l2norm_ge0.
Qed.

Section Projlf.
Variable (H : chsType).

Lemma psdf_trlf (A : 'F+(H)) : 0 <= \Tr A.
Proof. apply/psdlf_trlf/is_psdlf. Qed.

Lemma denf_trlf (A : 'FD(H)) : \Tr A <= 1.
Proof. apply/denlf_trlf/is_denlf. Qed.

Lemma den1lf_trlf (A : 'End(H)) : A \is den1lf -> \Tr A = 1.
Proof. by move=>/den1lfP[]. Qed.
Lemma den1f_trlf (A : 'FD1(H)) : \Tr A = 1.
Proof. by apply/den1lf_trlf/is_den1lf. Qed.

Lemma projlf_trlf (A : 'End(H)) : A \is projlf -> \Tr A = (\Rank A)%:R.
Proof. by rewrite qualifE=>/projmx_tr. Qed.
Lemma projf_trlf (A : 'FP(H)) : \Tr A = (\Rank A)%:R.
Proof. apply/projlf_trlf/is_projlf. Qed.

Lemma proj1lf_rankP (A : 'End(H)) : 
  reflect (A \is projlf /\ \Rank A = 1%N) (A \is proj1lf).
Proof.
rewrite qualifE /lfrank [X in reflect _ X]qualifE.
by apply/(iffP (proj1mxP _))=>[[P1 /eqP]|[P1 P2]]; split=>//; apply/eqP.
Qed.
Lemma proj1lf_rank (P : 'End(H)) : P \is proj1lf -> \Rank P = 1%N.
Proof. by move=>/proj1lf_rankP[]. Qed.
Lemma proj1f_rank (P : 'FP1(H)) : \Rank P = 1%N.
Proof. apply/proj1lf_rank/is_proj1lf. Qed.

Lemma proj1lfP (A : 'End(H)) : 
  reflect (A \is projlf /\ \Tr A = 1) (A \is proj1lf).
Proof.
apply/(iffP (proj1lf_rankP _))=>[[P1 P2]|[P1/eqP P2]]; split=>//.
by rewrite projlf_trlf// P2. by move: P2;
rewrite projlf_trlf// pnatr_eq1=>/eqP.
Qed.
Lemma proj1lf_trlf (P : 'End(H)) : P \is proj1lf -> \Tr P = 1.
Proof. by move=>/proj1lfP[]. Qed.
Lemma proj1f_trlf (P : 'FP1(H)) : \Tr P = 1.
Proof. apply/proj1lf_trlf/is_proj1lf. Qed.

Lemma hermlf_adjE (P : 'End(H)) : P \is hermlf -> P^A = P.
Proof. by move=>/hermlfP. Qed.
Lemma hermf_adjE (P : 'FH(H)) : P^A = P.
Proof. apply/hermlf_adjE/is_hermlf. Qed.

Lemma projlf_idem (A : 'End(H)) : A \is projlf -> A \o A = A.
Proof. by move=>/projlfP[]. Qed.
Lemma projf_idem (A : 'FP(H)) : A \o A = A.
Proof. apply/projlf_idem/is_projlf. Qed.
Lemma projlf_idemE (A : 'End(H)) x : A \is projlf -> A (A x) = A x.
Proof. by move=>/projlf_idem{3}<-; rewrite lfunE. Qed.
Lemma projf_idemE (A : 'FP(H)) x : A (A x) = A x.
Proof. by rewrite -[in RHS]projf_idem lfunE. Qed.

Lemma hermlf_dotE (P : 'End(H)) x y :
  P \is hermlf -> [< P x ; y >] = [< x ; P y >].
Proof. by move=>/hermlf_adjE; rewrite -adj_dotEl=>->. Qed.
Lemma hermf_dotE (P : 'FH(H)) x y : [< P x ; y >] = [< x ; P y >].
Proof. by apply/hermlf_dotE/is_hermlf. Qed.

Lemma projlf_dot (P : 'End(H)) x : P \is projlf -> [< x ; P x >] = `|P x|^+2.
Proof.
by move=>P1; rewrite -dotp_norm -adj_dotEr hermlf_adjE ?projlf_idemE//;
apply/projlf_herm.
Qed.
Lemma projf_dot (P : 'FP(H)) x : [< x ; P x >] = `|P x|^+2.
Proof. by apply/projlf_dot/is_projlf. Qed.

Lemma bound1f_dot G (f : 'FB1(H,G)) v : [< f v ; f v >] <= [< v ; v >].
Proof. by apply/bound1lfP/is_bound1lf. Qed.
Lemma bound1f_norm G (f : 'FB1(H,G)) v : `|f v| <= `|v|.
Proof. by apply/bound1lf_normP/is_bound1lf. Qed.

End Projlf.

Section DefaultDenObs.
Variable (V: chsType).
Implicit Type (U W T : chsType).

Lemma projlf0 : (0 : 'End(V)) \is projlf.
Proof. by apply/projlfP; rewrite linear0 comp_lfun0l. Qed.
HB.instance Definition _ := isProjLf.Build V 0 projlf0.
Lemma denlf0 : (0 : 'End(V)) \is denlf.
Proof. apply/denlfP; split. apply/is_psdlf. by rewrite linear0. Qed.
HB.instance Definition _ := Obs_isDenLf.Build V 0 denlf0.

Lemma projlf1 : (\1 : 'End(V)) \is projlf.
Proof. by apply/projlfP; rewrite adjf1 comp_lfun1l. Qed.
HB.instance Definition _ := isProjLf.Build V \1 projlf1.
Lemma unitarylf1 : (\1 : 'End(V)) \is unitarylf.
Proof. by apply/unitarylfP; rewrite adjf1 comp_lfun1l. Qed.
HB.instance Definition _ := Bound1_isIsoLf.Build V V \1 (unitarylf_iso unitarylf1).
HB.instance Definition _ := Iso_isGisoLf.Build V V \1 (unitarylf_giso unitarylf1).

Lemma normallf_adj (A:'End(V)) : A^A \is normallf = (A \is normallf).
Proof. by rewrite !normallfE adjfK eq_sym. Qed.
Lemma normallf_tr (A:'End(V)) : A^T \is normallf = (A \is normallf).
Proof. by rewrite !normallfE lfTAC -!trf_comp eq_sym (can_eq (@trfK _ _)). Qed.
Lemma normallf_conj (A:'End(V)) : A^C \is normallf = (A \is normallf).
Proof. by rewrite conjfAT normallf_tr normallf_adj. Qed.

Lemma normallfZ (c : C) (A : 'End(V)) : A \is normallf -> c *: A \is normallf.
Proof. by rewrite !normallfE adjfZ -!comp_lfunZl -!comp_lfunZr !scalerA mulrC=>/eqP->. Qed.
Lemma normallfN (A : 'End(V)) : - A \is normallf = (A \is normallf).
Proof. by rewrite !normallfE adjfN/= !comp_lfunNl !comp_lfunNr !opprK. Qed.

Lemma hermlf_adj (A:'End(V)) : A^A \is hermlf = (A \is hermlf).
Proof. by rewrite !hermlfE adjfK eq_sym. Qed.
Lemma hermlf_tr (A:'End(V)) : A^T \is hermlf = (A \is hermlf).
Proof. by rewrite !hermlfE lfTAC (can_eq (@trfK _ _)). Qed.
Lemma hermlf_conj (A:'End(V)) : A^C \is hermlf = (A \is hermlf).
Proof. by rewrite conjfAT hermlf_tr hermlf_adj. Qed.

Lemma hermlfD (A B : 'End(V)) : A \is hermlf -> B \is hermlf -> A + B \is hermlf.
Proof. by move=>/hermlfP P1/hermlfP P2; apply/hermlfP; rewrite adjfD P1 P2. Qed.
Lemma hermlfN (A : 'End(V)) : - A \is hermlf = (A \is hermlf).
Proof. by rewrite !hermlfE raddfN/= eqr_opp. Qed.
Lemma hermlf_sum I (r : seq I) (P : pred I) (f : I -> 'End(V)) :
  (forall i, P i -> f i \is hermlf) -> \sum_(i <- r | P i) f i \is hermlf.
Proof.
move=>IH; elim: r=>[|r i IH1]; first by rewrite big_nil is_hermlf.
by rewrite big_cons; case E: (P r)=>[|//]; apply hermlfD=>[|//]; apply IH.
Qed.

Lemma psdlf_adj (A:'End(V)) : A^A \is psdlf = (A \is psdlf).
Proof. by rewrite qualifE/= [RHS]qualifE adj_lfun.unlock mx2hK psdmx_adj. Qed.
Lemma psdlf_conj (A:'End(V)) : A^C \is psdlf = (A \is psdlf).
Proof. by rewrite qualifE/= [RHS]qualifE conj_lfun.unlock mx2hK psdmx_conj. Qed.
Lemma psdlf_tr (A:'End(V)) : A^T \is psdlf = (A \is psdlf).
Proof. by rewrite trfAC psdlf_conj psdlf_adj. Qed.

Lemma psdlfD (A B : 'End(V)) : A \is psdlf -> B \is psdlf -> A + B \is psdlf.
Proof.
by move=>/psdlfP P1/psdlfP P2; apply/psdlfP=>v;
rewrite lfunE/= dotpDr addr_ge0.
Qed.
Lemma psdlf_sum I (r : seq I) (P : pred I) (f : I -> 'End(V)) :
  (forall i, P i -> f i \is psdlf) -> \sum_(i <- r | P i) f i \is psdlf.
Proof.
move=>IH; elim: r=>[|r i IH1]; first by rewrite big_nil is_psdlf.
by rewrite big_cons; case E: (P r)=>[|//]; apply psdlfD=>[|//]; apply IH.
Qed.

Lemma bound1lf_adj U W (B : 'Hom(U,W)) : B^A \is bound1lf = (B \is bound1lf).
Proof. by rewrite !bound1lf_i2normE adj_lfun.unlock mx2hK i2norm_adjmx. Qed.
Lemma bound1lf_tr U W (B : 'Hom(U,W)) : B^T \is bound1lf = (B \is bound1lf).
Proof. by rewrite !bound1lf_i2normE tr_lfun.unlock mx2hK i2norm_trmx. Qed.
Lemma bound1lf_conj U W (B : 'Hom(U,W)) : B^C \is bound1lf = (B \is bound1lf).
Proof. by rewrite conjfAT bound1lf_tr bound1lf_adj. Qed.
Lemma bound1lf_comp U W T (A : 'Hom(U,W)) (B : 'Hom(T,U)) :
  A \is bound1lf -> B \is bound1lf -> A \o B \is bound1lf.
Proof.
move=>/bound1lfP PA /bound1lfP PB; apply/bound1lfP=>u.
by rewrite lfunE/=; apply/(le_trans (PA _))/PB.
Qed.

Lemma obslf_adj (A:'End(V)) : A^A \is obslf = (A \is obslf).
Proof. by rewrite qualifE/= [RHS]qualifE adj_lfun.unlock mx2hK obsmx_adj. Qed.
Lemma obslf_tr (A:'End(V)) : A^T \is obslf = (A \is obslf).
Proof. by rewrite qualifE/= [RHS]qualifE tr_lfun.unlock mx2hK obsmx_tr. Qed.
Lemma obslf_conj (A:'End(V)) : A^C \is obslf = (A \is obslf).
Proof. by rewrite conjfAT obslf_tr obslf_adj. Qed.

Lemma denlf_adj (A:'End(V)) : A^A \is denlf = (A \is denlf).
Proof. by rewrite qualifE/= [RHS]qualifE adj_lfun.unlock mx2hK denmx_adj. Qed.
Lemma denlf_tr (A:'End(V)) : A^T \is denlf = (A \is denlf).
Proof. by rewrite qualifE/= [RHS]qualifE tr_lfun.unlock mx2hK denmx_tr. Qed.
Lemma denlf_conj (A:'End(V)) : A^C \is denlf = (A \is denlf).
Proof. by rewrite conjfAT denlf_tr denlf_adj. Qed.

Lemma den1lf_adj (A:'End(V)) : A^A \is den1lf = (A \is den1lf).
Proof.
apply/eqb_iff; split=>/den1lfP P; apply/den1lfP; move: P;
by rewrite psdlf_adj lftrace_adj=>[[->/(f_equal Num.conj_op)]];
rewrite ?conjCK conjC1.
Qed.
Lemma den1lf_tr (A:'End(V)) : A^T \is den1lf = (A \is den1lf).
Proof.
apply/eqb_iff; split=>/den1lfP P; apply/den1lfP; move: P;
by rewrite psdlf_tr lftrace_tr.
Qed.
Lemma den1lf_conj (A:'End(V)) : A^C \is den1lf = (A \is den1lf).
Proof. by rewrite conjfAT den1lf_tr den1lf_adj. Qed.

Lemma projlf_adj (A:'End(V)) : A^A \is projlf = (A \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP; rewrite ?adjfK=>[[P1 P2]]; apply/projlfP; 
by split; apply/adjf_inj; rewrite ?adjf_comp ?adjfK.
Qed.
Lemma projlf_tr (A:'End(V)) : A^T \is projlf = (A \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP[P1 P2]; apply/projlfP;
by split; apply/trf_inj; rewrite ?trf_comp ?lfATC ?trfK.
Qed.
Lemma projlf_conj (A:'End(V)) : A^C \is projlf = (A \is projlf).
Proof. by rewrite conjfAT projlf_tr projlf_adj. Qed.

Lemma proj1lf_adj (A:'End(V)) : A^A \is proj1lf = (A \is proj1lf).
Proof.
apply/eqb_iff; split=>/proj1lf_rankP P; apply/proj1lf_rankP; 
by move: P; rewrite projlf_adj ranklf_adj.
Qed.
Lemma proj1lf_tr (A:'End(V)) : A^T \is proj1lf = (A \is proj1lf).
Proof.
apply/eqb_iff; split=>/proj1lf_rankP P; apply/proj1lf_rankP; 
by move: P; rewrite projlf_tr ranklf_tr.
Qed.
Lemma proj1lf_conj (A:'End(V)) : A^C \is proj1lf = (A \is proj1lf).
Proof. by rewrite conjfAT proj1lf_tr proj1lf_adj. Qed.

Lemma isolf_conj U W (B : 'Hom(U,W)) : B^C \is isolf = (B \is isolf).
Proof.
by rewrite qualifE/= [RHS]qualifE conj_lfun.unlock mx2hK mxCAC conjC_unitary.
Qed.
Lemma isolf_comp U W T (A : 'Hom(U,W)) (B : 'Hom(T,U)) :
  A \is isolf -> B \is isolf -> A \o B \is isolf.
Proof.
move=>/isolfP PA /isolfP PB.
by apply/isolfP; rewrite adjf_comp comp_lfunA comp_lfunACA PA comp_lfun1r PB.
Qed.

Lemma gisolf_comp U W T (A : 'Hom(U,W)) (B : 'Hom(T,U)) :
  A \is gisolf -> B \is gisolf -> A \o B \is gisolf.
Proof.
move=>/gisolfP [] PA1 PA2 /gisolfP [] PB1 PB2.
by apply/gisolfP;
rewrite adjf_comp !comp_lfunA !comp_lfunACA PA1 PB2 !comp_lfun1r PB1 PA2.
Qed.
Lemma gisolf_adj U W (A : 'Hom(U,W)) : A^A \is gisolf = (A \is gisolf).
Proof. by rewrite qualifE/= [RHS]qualifE adj_lfun.unlock mx2hK adjmxK andbC. Qed.
Lemma gisolf_conj U W (A : 'Hom(U,W)) : A^C \is gisolf = (A \is gisolf).
Proof. by rewrite !gisolf_isoE lfCAC !isolf_conj. Qed.
Lemma gisolf_tr U W (A : 'Hom(U,W)) : A^T \is gisolf = (A \is gisolf).
Proof. by rewrite trfAC gisolf_conj gisolf_adj. Qed.

Lemma unitarylf_comp (A B : 'End(V)): 
  A \is unitarylf -> B \is unitarylf -> A \o B \is unitarylf.
Proof. exact: isolf_comp. Qed.
Lemma unitarylf_adj (A:'End(V)) : A^A \is unitarylf = (A \is unitarylf).
Proof. by rewrite qualifE/= [RHS]qualifE adj_lfun.unlock mx2hK trmxC_unitary. Qed.
Lemma unitarylf_tr (A:'End(V)) : A^T \is unitarylf = (A \is unitarylf).
Proof. by rewrite qualifE/= [RHS]qualifE tr_lfun.unlock mx2hK mxTAC trmx_unitary. Qed.
Lemma unitarylf_conj (A:'End(V)) : A^C \is unitarylf = (A \is unitarylf).
Proof. by rewrite conjfAT unitarylf_tr unitarylf_adj. Qed.

Lemma normalf_adj (A : 'FN(V)) : A^A \is normallf.
Proof. by rewrite normallf_adj is_normallf. Qed.
Lemma normalf_tr (A : 'FN(V)) : A^T \is normallf.
Proof. by rewrite normallf_tr is_normallf. Qed.
Lemma normalf_conj (A : 'FN(V)) : A^C \is normallf.
Proof. by rewrite normallf_conj is_normallf. Qed.
Lemma normalfZ (c : C) (A : 'FN(V)) : (c *: A%:VF) \is normallf.
Proof. by apply/normallfZ/is_normallf. Qed.
Lemma normalfN (A : 'FN(V)) : (-A%:VF) \is normallf.
Proof. by rewrite normallfN is_normallf. Qed.
HB.instance Definition _ (A : 'FN(V)) := isNormalLf.Build V (A^A) (normalf_adj A).
HB.instance Definition _ (A : 'FN(V)) := isNormalLf.Build V (A^T) (normalf_tr A).
HB.instance Definition _ (A : 'FN(V)) := isNormalLf.Build V (A^C) (normalf_conj A).
HB.instance Definition _ (c : C) (A : 'FN(V)) :=
  isNormalLf.Build V (c *: A%:VF) (normalfZ c A).
HB.instance Definition _ (A : 'FN(V)) := isNormalLf.Build V (-A%:VF) (normalfN A).

Lemma hermf_adj (A : 'FH(V)) : A^A \is hermlf.
Proof. by rewrite hermlf_adj is_hermlf. Qed.
Lemma hermf_tr (A : 'FH(V)) : A^T \is hermlf.
Proof. by rewrite hermlf_tr is_hermlf. Qed.
Lemma hermf_conj (A : 'FH(V)) : A^C \is hermlf.
Proof. by rewrite hermlf_conj is_hermlf. Qed.
Lemma hermfD (A B : 'FH(V)) : A%:VF + B \is hermlf.
Proof. apply/hermlfD; apply/is_hermlf. Qed.
Lemma hermfN (A : 'FH(V)) : - A%:VF \is hermlf.
Proof. by rewrite hermlfN is_hermlf. Qed.
Lemma hermf_sum I (r : seq I) (P : pred I) (f : I -> 'FH(V)) :
  \sum_(i <- r | P i) (f i)%:VF \is hermlf.
Proof. by apply/hermlf_sum=>i _; apply/is_hermlf. Qed.
HB.instance Definition _ (A : 'FH(V)) := Normal_isHermLf.Build V (A^A) (hermf_adj A).
HB.instance Definition _ (A : 'FH(V)) := Normal_isHermLf.Build V (A^T) (hermf_tr A).
HB.instance Definition _ (A : 'FH(V)) := Normal_isHermLf.Build V (A^C) (hermf_conj A).
HB.instance Definition _ (A B : 'FH(V)) := isHermLf.Build V (A%:VF + B) (hermfD A B).
HB.instance Definition _ (A : 'FH(V)) := Normal_isHermLf.Build V (-A%:VF) (hermfN A).
HB.instance Definition _ I (r : seq I) (P : pred I) (f : I -> 'FH(V)) := 
  isHermLf.Build V (\sum_(i <- r | P i) (f i)%:VF) (hermf_sum r P f).

(* psdf_add : defined later *)
Lemma psdf_adj (A : 'F+(V)) : A^A \is psdlf.
Proof. by rewrite psdlf_adj is_psdlf. Qed.
Lemma psdf_conj (A : 'F+(V)) : A^C \is psdlf.
Proof. by rewrite psdlf_conj is_psdlf. Qed.
Lemma psdf_tr (A : 'F+(V)) : A^T \is psdlf.
Proof. by rewrite psdlf_tr is_psdlf. Qed.
Lemma psdfD (A B : 'F+(V)) : A%:VF + B \is psdlf.
Proof. apply/psdlfD; apply/is_psdlf. Qed.
Lemma psdf_sum I (r : seq I) (P : pred I) (f : I -> 'F+(V)) :
  \sum_(i <- r | P i) (f i)%:VF \is psdlf.
Proof. by apply/psdlf_sum=>i _; apply/is_psdlf. Qed.
HB.instance Definition _ (A : 'F+(V)) := Herm_isPsdLf.Build V (A^A) (psdf_adj A).
HB.instance Definition _ (A : 'F+(V)) := Herm_isPsdLf.Build V (A^T) (psdf_tr A).
HB.instance Definition _ (A : 'F+(V)) := Herm_isPsdLf.Build V (A^C) (psdf_conj A).
HB.instance Definition _ (A B : 'F+(V)) := Herm_isPsdLf.Build V (A%:VF + B) (psdfD A B).
HB.instance Definition _ I (r : seq I) (P : pred I) (f : I -> 'F+(V)) := 
  Herm_isPsdLf.Build V (\sum_(i <- r | P i) (f i)%:VF) (psdf_sum r P f).

Lemma bound1f_adj U W (B : 'FB1(U,W)) : B^A \is bound1lf.
Proof. by rewrite bound1lf_adj is_bound1lf. Qed.
Lemma bound1f_conj U W (B : 'FB1(U,W)) : B^C \is bound1lf.
Proof. by rewrite bound1lf_conj is_bound1lf. Qed.
Lemma bound1f_tr U W (B : 'FB1(U,W)) : B^T \is bound1lf.
Proof. by rewrite bound1lf_tr is_bound1lf. Qed.
Lemma bound1f_comp U W T (A : 'FB1(U,W)) (B : 'FB1(T,U)) : A \o B \is bound1lf.
Proof. by rewrite bound1lf_comp ?is_bound1lf. Qed.
HB.instance Definition _ U W (B : 'FB1(U,W)) := isBound1Lf.Build W U (B^A) (bound1f_adj B).
HB.instance Definition _ U W (B : 'FB1(U,W)) := isBound1Lf.Build U W (B^C) (bound1f_conj B).
HB.instance Definition _ U W (B : 'FB1(U,W)) := isBound1Lf.Build W U (B^T) (bound1f_tr B).
HB.instance Definition _ U W T (A : 'FB1(U,W)) (B : 'FB1(T,U)) := 
  isBound1Lf.Build _ _ (A \o B) (bound1f_comp A B).

HB.instance Definition _ (A : 'FO(V)) := ObsLf.Class (PsdLf.on (A^A)) (Bound1Lf.on (A^A)).
HB.instance Definition _ (A : 'FO(V)) := ObsLf.Class (PsdLf.on (A^T)) (Bound1Lf.on (A^T)).
HB.instance Definition _ (A : 'FO(V)) := ObsLf.Class (PsdLf.on (A^C)) (Bound1Lf.on (A^C)).
Lemma obsf_adj (A : 'FO(V)) : A^A \is obslf. Proof. apply/is_obslf. Qed.
Lemma obsf_conj (A : 'FO(V)) : A^C \is obslf. Proof. apply/is_obslf. Qed.
Lemma obsf_tr (A : 'FO(V)) : A^T \is obslf. Proof. apply/is_obslf. Qed.
(* HB.instance Definition _ (A : 'FO(V)) := Psd_isObsLf.Build V (A^A) (obsf_adj A).
HB.instance Definition _ (A : 'FO(V)) := Psd_isObsLf.Build V (A^T) (obsf_tr A).
HB.instance Definition _ (A : 'FO(V)) := Psd_isObsLf.Build V (A^C) (obsf_conj A). *)

Lemma denf_adj (A : 'FD(V)) : A^A \is denlf.
Proof. by rewrite denlf_adj is_denlf. Qed.
Lemma denf_conj (A : 'FD(V)) : A^C \is denlf.
Proof. by rewrite denlf_conj is_denlf. Qed.
Lemma denf_tr (A : 'FD(V)) : A^T \is denlf.
Proof. by rewrite denlf_tr is_denlf. Qed.
HB.instance Definition _ (A : 'FD(V)) := Obs_isDenLf.Build V (A^A) (denf_adj A).
HB.instance Definition _ (A : 'FD(V)) := Obs_isDenLf.Build V (A^T) (denf_tr A).
HB.instance Definition _ (A : 'FD(V)) := Obs_isDenLf.Build V (A^C) (denf_conj A).

Lemma den1f_adj (A : 'FD1(V)) : A^A \is den1lf.
Proof. by rewrite den1lf_adj is_den1lf. Qed.
Lemma den1f_conj (A : 'FD1(V)) : A^C \is den1lf.
Proof. by rewrite den1lf_conj is_den1lf. Qed.
Lemma den1f_tr (A : 'FD1(V)) : A^T \is den1lf.
Proof. by rewrite den1lf_tr is_den1lf. Qed.
HB.instance Definition _ (A : 'FD1(V)) := Den_isDen1Lf.Build V (A^A) (den1f_adj A).
HB.instance Definition _ (A : 'FD1(V)) := Den_isDen1Lf.Build V (A^T) (den1f_tr A).
HB.instance Definition _ (A : 'FD1(V)) := Den_isDen1Lf.Build V (A^C) (den1f_conj A).

Lemma projf_adj (A : 'FP(V)) : A^A \is projlf.
Proof. by rewrite projlf_adj is_projlf. Qed.
Lemma projf_conj (A : 'FP(V)) : A^C \is projlf.
Proof. by rewrite projlf_conj is_projlf. Qed.
Lemma projf_tr (A : 'FP(V)) : A^T \is projlf.
Proof. by rewrite projlf_tr is_projlf. Qed.
HB.instance Definition _ (A : 'FP(V)) := Obs_isProjLf.Build V (A^A) (projf_adj A).
HB.instance Definition _ (A : 'FP(V)) := Obs_isProjLf.Build V (A^T) (projf_tr A).
HB.instance Definition _ (A : 'FP(V)) := Obs_isProjLf.Build V (A^C) (projf_conj A).

HB.instance Definition _ (A : 'FP1(V)) := Proj1Lf.Class (ProjLf.on (A^A)) (Den1Lf.on (A^A)).
HB.instance Definition _ (A : 'FP1(V)) := Proj1Lf.Class (ProjLf.on (A^T)) (Den1Lf.on (A^T)).
HB.instance Definition _ (A : 'FP1(V)) := Proj1Lf.Class (ProjLf.on (A^C)) (Den1Lf.on (A^C)).
Lemma proj1f_adj (A : 'FP1(V)) : A^A \is proj1lf. Proof. apply/is_proj1lf. Qed.
Lemma proj1f_conj (A : 'FP1(V)) : A^C \is proj1lf. Proof. apply/is_proj1lf. Qed.
Lemma proj1f_tr (A : 'FP1(V)) : A^T \is proj1lf. Proof. apply/is_proj1lf. Qed.
 
(* HB.instance Definition _ (A : 'FP1(V)) := isProj1Lf.Build V (A^A) (proj1f_adj A).
HB.instance Definition _ (A : 'FP1(V)) := isProj1Lf.Build V (A^T) (proj1f_tr A).
HB.instance Definition _ (A : 'FP1(V)) := isProj1Lf.Build V (A^C) (proj1f_conj A). *)

Lemma isof_conj U W (B : 'FI(U,W)) : B^C \is isolf.
Proof. by rewrite isolf_conj is_isolf. Qed.
Lemma isof_comp U W T (A : 'FI(U,W)) (B : 'FI(T,U)) : A \o B \is isolf.
Proof. by rewrite isolf_comp ?is_isolf. Qed.
HB.instance Definition _ U W (B : 'FI(U,W)) := Bound1_isIsoLf.Build U W (B^C) (isof_conj B).
HB.instance Definition _ U W T (A : 'FI(U,W)) (B : 'FI(T,U)) := 
  Bound1_isIsoLf.Build _ _ (A \o B) (isof_comp A B).

Lemma gisof_adj U W (B : 'FGI(U,W)) : B^A \is gisolf.
Proof. by rewrite gisolf_adj is_gisolf. Qed.
Lemma gisof_conj U W (B : 'FGI(U,W)) : B^C \is gisolf.
Proof. by rewrite gisolf_conj is_gisolf. Qed.
Lemma gisof_tr U W (B : 'FGI(U,W)) : B^T \is gisolf.
Proof. by rewrite gisolf_tr is_gisolf. Qed.
Lemma gisof_comp U W T (A : 'FGI(U,W)) (B : 'FGI(T,U)) : A \o B \is gisolf.
Proof. by rewrite gisolf_comp ?is_gisolf. Qed.
HB.instance Definition _ U W (B : 'FGI(U,W)) := Bound1_isIsoLf.Build W U (B^A) (gisolf_iso (gisof_adj B)).
HB.instance Definition _ U W (B : 'FGI(U,W)) := Iso_isGisoLf.Build W U (B^A) (gisof_adj B).
HB.instance Definition _ U W (B : 'FGI(U,W)) := Iso_isGisoLf.Build U W (B^C) (gisof_conj B).
HB.instance Definition _ U W (B : 'FGI(U,W)) := Bound1_isIsoLf.Build W U (B^T) (gisolf_iso (gisof_tr B)).
HB.instance Definition _ U W (B : 'FGI(U,W)) := Iso_isGisoLf.Build W U (B^T) (gisof_tr B).
HB.instance Definition _ U W T (A : 'FGI(U,W)) (B : 'FGI(T,U)) := 
  Iso_isGisoLf.Build _ _ (A \o B) (gisof_comp A B).

Lemma unitaryf_comp (A B : 'FU(V)) : A \o B \is unitarylf. Proof. by apply/is_unitarylf. Qed.
Lemma unitaryf_adj (A : 'FU(V)) : A^A \is unitarylf. Proof. by apply/is_unitarylf. Qed.
Lemma unitaryf_conj (A : 'FU(V)) : A^C \is unitarylf. Proof. by apply/is_unitarylf. Qed.
Lemma unitaryf_tr (A : 'FU(V)) : A^T \is unitarylf. Proof. by apply/is_unitarylf. Qed.
(* HB.instance Definition _ (A : 'FU(V)) := isUnitaryLf.Build V (A^A) (unitaryf_adj A).
HB.instance Definition _ (A : 'FU(V)) := isUnitaryLf.Build V (A^T) (unitaryf_tr A).
HB.instance Definition _ (A : 'FU(V)) := isUnitaryLf.Build V (A^C) (unitaryf_conj A).
HB.instance Definition _ (A B : 'FU(V)) := isUnitaryLf.Build V (A \o B) (unitaryf_comp A B). *)

(* same as unitaryfEl ?? *)
Lemma unitaryf_form (A : 'FU(V)) : A^A \o A = \1.
Proof. apply/unitarylfP/is_unitarylf. Qed.
Lemma unitaryf_formV (A : 'FU(V)) : A \o A^A = \1.
Proof. apply/unitarylfPV/is_unitarylf. Qed.

Lemma unitaryf_sym (A : 'FU(V)) u v : (A^A u == v)%VF = (A v == u).
Proof.
by apply/eqb_iff; rewrite !eq_iff; split=><-; 
rewrite -comp_lfunE ?unitaryf_form ?unitaryf_formV lfunE.
Qed.

End DefaultDenObs.

(* should build PONB -> ONB *)
(* do this later; e.g., canonical ONB as PONB*)

HB.mixin Record isPONB (H : chsType) (F : finType) (f : F -> H) := {
  ponb_dot : forall i j, [< f i ; f j >] = (i == j)%:R;
}.

#[short(type="ponbType")]
HB.structure Definition PONB (H : chsType) (F : finType) :=
  { f of isPONB H F f}.

Notation "''PONB' ( F ; S )" := (ponbType S F) : type_scope.
Notation "''PONB'" := ('PONB(_;_)) (only parsing) : type_scope.

Module PONBExports.
#[deprecated(since="mathcomp 2.0.0", note="Use PONB.clone instead.")]
Notation "[ 'PONB' 'of' f 'as' g ]" := (@PONB.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use PONB.clone instead.")]
Notation "[ 'PONB' 'of' f ]" := (@PONB.clone _ _ f _) : form_scope.
End PONBExports.
HB.export PONBExports.

HB.mixin Record isFullDim (H : chsType) (F : finType) f of @PONB H F f := {
  onb_card : #|F| = dim H;
}.

#[short(type="onbType")]
HB.structure Definition ONB (H : chsType) (F : finType) :=
  { f of @PONB H F f & @isFullDim H F f}.

Notation "''ONB' ( F ; S )" := (onbType S F) : type_scope.
Notation "''ONB'" := ('ONB(_;_)) (only parsing) : type_scope.

Module ONBExports.
#[deprecated(since="mathcomp 2.0.0", note="Use ONB.clone instead.")]
Notation "[ 'ONB' 'of' f 'as' g ]" := (@ONB.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ONB.clone instead.")]
Notation "[ 'ONB' 'of' f ]" := (@ONB.clone _ _ f _) : form_scope.
End ONBExports.
HB.export ONBExports.

HB.factory Record isONB (H : chsType) (F : finType) (f : F -> H) := {
  onb_dot : forall i j, [< f i ; f j >] = (i == j)%:R;
  onb_card : #|F| = dim H;
}.
HB.builders Context H F f of isONB H F f.
  HB.instance Definition _ := isPONB.Build H F f onb_dot.
  HB.instance Definition _ := isFullDim.Build H F f onb_card.
HB.end.

HB.mixin Record isPartialState (U : chsType) (u : U) := {
  ps_dot : [< u ; u >] <= 1;
}.

#[short(type="psType")]
HB.structure Definition PartialState (U : chsType) :=
  { u of isPartialState U u }.

Notation "''PS' ( S )" := (psType S) : type_scope.
Notation "''PS'" := ('PS(_)) (only parsing) : type_scope.

Module PartialStateExports.
#[deprecated(since="mathcomp 2.0.0", note="Use PartialState.clone instead.")]
Notation "[ 'PS' 'of' u 'as' v ]" := (@PartialState.clone _ u v) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use PartialState.clone instead.")]
Notation "[ 'PS' 'of' u ]" := (@PartialState.clone _ u _) : form_scope.
End PartialStateExports.
HB.export PartialStateExports.

HB.mixin Record Partial_isNormalState (U : chsType) u of PartialState U u := {
  ns_dot : [< u ; u >] = 1;
}.

#[short(type="nsType")]
HB.structure Definition NormalState (U : chsType) :=
  { u of PartialState U u & Partial_isNormalState U u}.

Notation "''NS' ( S )" := (nsType S) : type_scope.
Notation "''NS'" := ('NS(_)) (only parsing) : type_scope.

Module NormalStateExports.
#[deprecated(since="mathcomp 2.0.0", note="Use NormalState.clone instead.")]
Notation "[ 'NS' 'of' u 'as' v ]" := (@NormalState.clone _ u v) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use NormalState.clone instead.")]
Notation "[ 'NS' 'of' u ]" := (@NormalState.clone _ u _) : form_scope.
End NormalStateExports.
HB.export NormalStateExports.

HB.factory Record isNormalState (U : chsType) (u : U) := {
  ns_dot : [< u ; u >] = 1;
}.
HB.builders Context U u of isNormalState U u.
  Lemma ps_dot : [< u ; u >] <= 1.
  Proof. by rewrite ns_dot. Qed.
  HB.instance Definition _ := isPartialState.Build U u ps_dot.
  HB.instance Definition _ := Partial_isNormalState.Build U u ns_dot.
HB.end.

Program Definition PartialState_subType (U : chsType) := 
  @isSub.Build U (fun u => [< u ; u >] <= 1) (psType U) 
  (@PartialState.sort U) (fun (u : U) (H : [< u ; u >] <= 1) => 
  PartialState.Pack (PartialState.Class (isPartialState.Axioms_ u H))) _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@ps_dot _ u) (X _ (@ps_dot _ u)).
by case: u=>/= u [[Pu1]] Pu2; rewrite (eq_irrelevance Pu1 Pu2).
Qed.
HB.instance Definition _ (U : chsType) := @PartialState_subType U.
HB.instance Definition _ (U : chsType) := [Equality of (psType U) by <:].
HB.instance Definition _ (U : chsType) := [Choice of (psType U) by <:].

Program Definition NormalState_subType (U : chsType) := 
  @isSub.Build U (fun u => [< u ; u >] == 1) (nsType U) 
  (@NormalState.sort U) (fun (u : U) (H : [< u ; u >] == 1) => 
  NormalState.Pack (NormalState.Class 
  (Partial_isNormalState.Axioms_ (isPartialState.Axioms_ u _) (eqP H)))) _ (fun _ _ => erefl).
Next Obligation. by move=>??/eqP->. Qed.
Next Obligation.
intros; move: (@ns_dot _ u)=>/eqP Pu; move: (X _ Pu).
case: u Pu=>/= u [[Pu1]] [Pu2] Pu3.
by rewrite (eq_irrelevance (_ Pu3) Pu1) (eq_irrelevance (_ Pu3) Pu2).
Qed.
HB.instance Definition _ (U : chsType) := @NormalState_subType U.
HB.instance Definition _ (U : chsType) := [Equality of (nsType U) by <:].
HB.instance Definition _ (U : chsType) := [Choice of (nsType U) by <:].

Arguments ponb_dot [H F] s i j.
Arguments ps_dot [U] s.
Arguments ns_dot [U] s.

(* provide the complement of an ponb basis *)
Section PONBDot.
Variable (H : chsType) (F : finType) (f : 'PONB(F;H)).

Definition ponb2mx := \matrix_(i < dim H, j < #|F|) h2c (f (enum_val j)) i 0.
Lemma ponb2mx_col i : col i ponb2mx = h2c (f (enum_val i)).
Proof. by apply/matrixP=>j k; rewrite !mxE ord1. Qed.
Lemma ponb2mx_colV i : h2c (f i) = col (enum_rank i) ponb2mx.
Proof. by rewrite ponb2mx_col enum_rankK. Qed.

Lemma ponb2mx_unitary : ponb2mx^*t \is unitarymx.
Proof.
apply/unitarymxP/matrixP=>j k.
by rewrite -adjmxE adjmxK mulmx_rowcol -adj_col !ponb2mx_col 
  -dotp_mulmx ponb_dot mxE (can_eq enum_valK) eq_sym.
Qed.
Lemma ponb_card : (#|F| <= dim H)%N.
Proof.
move: ponb2mx_unitary (rank_leq_row ponb2mx)=>/mxrank_unitary.
by rewrite mxrank_map mxrank_tr=>->.
Qed.

Definition ponb_compl (i : 'I_(dim H - #|F|)) :=
  c2h (row i (dsubmx (schmidt (col_mx (ponb2mx^*t) (0 : 'M_(dim H - #|F|,_))))))^*t.

Definition ponb_ext (i : F + 'I_(dim H - #|F|)%N) :=
  match i with inl j => f j | inr j => ponb_compl j end.

Lemma ponb_compl_ponb i j : [< ponb_compl i ; ponb_compl j >] = (i == j)%:R.
Proof.
rewrite dotp_mulmx /ponb_compl !c2hK !row_dsubmx
  adjmxK adj_row -mulmx_rowcol unitarymxK.
by apply/schmidt_unitarymx; rewrite subnKC// ponb_card.
by rewrite mxE (inj_eq (@rshift_inj _ _)) eq_sym.
Qed.
HB.instance Definition _ :=
  isPONB.Build H 'I_(dim H - #|F|) ponb_compl ponb_compl_ponb.

Lemma ponb_ortho_compl i j : [< f i ; ponb_compl j >] = 0.
Proof.
rewrite dotp_mulmx /ponb_compl !c2hK row_dsubmx ponb2mx_colV adj_col 
  {1}(unitary_ext ponb2mx_unitary) row_usubmx adj_row -mulmx_rowcol unitarymxK.
by apply/schmidt_unitarymx; rewrite subnKC// ponb_card.
by rewrite mxE eq_lrshift. 
Qed.

Lemma ponb_ortho_complV i j : [< ponb_compl i ; f j >] = 0.
Proof. by rewrite -conj_dotp ponb_ortho_compl conjC0. Qed.

Lemma ponb_extE i : ponb_ext (inl i) = f i. Proof. by []. Qed.
Lemma ponb_extCE i : ponb_ext (inr i) = ponb_compl i. Proof. by []. Qed.

Lemma ponb_ext_onb i j : [< ponb_ext i ; ponb_ext j >] = (i == j)%:R.
Proof.
by case: i; case: j=>i j; rewrite /ponb_ext/= ?ponb_compl_ponb 
  ?ponb_dot// ?ponb_ortho_compl ?ponb_ortho_complV.
Qed.
Lemma ponb_ext_card : #|{: F + 'I_(dim H - #|F|)%N}| = dim H.
Proof. by rewrite card_sum card_ord addnC subnK// ponb_card. Qed.
HB.instance Definition _ := isONB.Build H (F + 'I_(dim H - #|F|)%N)%type 
  ponb_ext ponb_ext_onb ponb_ext_card.

End PONBDot.

Section ONBTheory.
Variable (H : chsType) (F : finType) (f : 'ONB(F;H)).

Lemma onb_dot i j : [< f i ; f j >] = (i == j)%:R. Proof. exact: ponb_dot. Qed.

Local Notation "'''' i" := (cast_ord (@onb_card _ _ f) (enum_rank i)) (at level 2).
Definition onb2eb : 'End(H) := \sum_i [> eb ''i ; f i <].
Definition eb2onb : 'End(H) := \sum_i [> f i ; eb ''i <].

Lemma onb2eb_adj : onb2eb^A = eb2onb.
Proof. by rewrite /onb2eb /eb2onb raddf_sum/=; under eq_bigr do rewrite adj_outp. Qed.
Lemma eb2onb_adj : eb2onb^A = onb2eb.
Proof. by rewrite -onb2eb_adj adjfK. Qed.

Lemma onb2eb_unitary : onb2eb \is unitarylf.
Proof.
apply/unitarylfPV; rewrite onb2eb_adj /onb2eb /eb2onb linear_sumr/=.
rewrite [LHS](eq_bigr (fun i=>[> eb ''i; eb ''i <])).
by move=>i _; rewrite linear_suml/= (bigD1 i)//= big1=>[j/negPf nj|];
rewrite outp_comp onb_dot ?nj ?scale0r// eqxx scale1r addr0.
symmetry; rewrite -sumeb_out; apply: reindex; apply bij_ord_enum.
Qed.

Lemma sumonb_out : \sum_i [> f i ; f i <] = \1.
Proof.
move: onb2eb_unitary=>/unitarylfP<-. symmetry.
rewrite onb2eb_adj /eb2onb /onb2eb linear_sumr/=; apply eq_bigr=>i _.
rewrite (bigD1 i)//= comp_lfunDl linear_suml big1/==>[j/negPf nj|];
by rewrite outp_comp eb_dot -enum_ord_eq cast_ord_comp cast_ord_id enum_rankK 
  ?nj ?scale0r// eqxx scale1r addr0.
Qed.

Lemma onb_vec (v : H) : v = \sum_i [< f i ; v >] *: f i.
Proof. by under eq_bigr do rewrite -outpE; rewrite -sum_lfunE sumonb_out lfunE. Qed.

Lemma outp_complV (G : chsType) (u v : H) (g : 'Hom(H,G)) :
  [> g u ; v <] = g \o [> u ; v <].
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE linearZ/=. Qed.

Lemma outp_comprV (G : chsType) (u v : H) (g : 'Hom(H,G)) :
  [> u ; g v <] = [> u ; v <] \o g^A.
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE adj_dotEr. Qed.

Lemma onb_lfun (G : chsType) (g : 'Hom(H,G)) : g = \sum_i [> g (f i) ; f i <].
Proof.
under eq_bigr do rewrite outp_complV.
by rewrite -linear_sumr/= sumonb_out comp_lfun1r.
Qed.

Lemma intro_onbl (u v: H) : 
  (forall i, [< f i ; u >] = [< f i ; v >]) <-> u = v.
Proof.
split=>[P|->//]; apply intro_dotl=> t; rewrite (onb_vec t) !dotp_suml.
by apply eq_bigr=>i _; rewrite !dotpZl P.
Qed.

Lemma intro_onbr (u v: H) : 
  (forall i, [< u ; f i >] = [< v ; f i >]) <-> u = v.
Proof.
split=>[|->//]; rewrite -intro_onbl=> P t.
by apply (can_inj conjCK); rewrite !conj_dotp.
Qed.

Lemma onb_trlf x : \Tr x = \sum_i [< f i ; x (f i) >].
Proof. 
rewrite {1}(onb_lfun x) linear_sum/=; apply eq_bigr=>i _.
by rewrite outp_trlf.
Qed.

Lemma intro_onb (G : chsType) (g h : 'Hom(H,G)) :
  (forall i, g (f i) = h (f i)) <-> g = h.
Proof.
split=>[P|->//]; apply/lfunP=>u; rewrite (onb_vec u) !linear_sum/=.
by apply eq_bigr=>i _; rewrite !linearZ/= P.
Qed.

End ONBTheory.

Lemma sumonb_out_bool (U : chsType) (phi : 'ONB(bool; U)) :
  [> phi true ; phi true <] + [> phi false; phi false <] = \1.
Proof. by rewrite -(sumonb_out phi) big_bool. Qed.

Section ONB2Theory.
Variable (U V : chsType) (F G : finType) (ou : 'ONB(F;U)) (ov : 'ONB(G;V)).

Lemma onb_lfun2 (E : 'Hom(U,V)) : 
  E = \sum_i \sum_j [< ov j ; E (ou i) >] *: [> ov j ; ou i <].
Proof.
rewrite [LHS](onb_lfun ou); apply eq_bigr=>i _.
by rewrite {1}(onb_vec ov (E (ou i))) linear_suml/=;
under eq_bigr do rewrite linearZl_LR.
Qed.

Lemma onb_lfun2id (E : 'End(U)) : 
  E = \sum_i \sum_j [< ou j ; E (ou i) >] *: [> ou j ; ou i <].
Proof.
rewrite [LHS](onb_lfun ou); apply eq_bigr=>i _.
by rewrite {1}(onb_vec ou (E (ou i))) linear_suml/=;
under eq_bigr do rewrite linearZl_LR.
Qed.

End ONB2Theory.

Section DefaultONB.

Lemma eb_card (H : chsType) : #|'I_(dim H) | = dim H.
Proof. by rewrite card_ord. Qed.
HB.instance Definition _ (H : chsType) := 
  isONB.Build H 'I_(dim H) (@eb H) (@eb_dot H) (@eb_card H).

End DefaultONB.

Section PartialStateTheory.
Variable (U : chsType).
Implicit Types (F : finType).

Lemma ps_norm (v : 'PS(U)) : `|v : U| <= 1.
Proof. by rewrite hnorm_le1 ps_dot. Qed.

Lemma ponb_ns F (f : 'PONB(F;U)) i : [< f i ; f i >] = 1.
Proof. by rewrite ponb_dot eqxx. Qed.

#[non_forgetful_inheritance]
HB.instance Definition _ F (f : 'PONB(F;U)) (i : F) := 
  isNormalState.Build U (f i) (ponb_ns f i).

#[non_forgetful_inheritance]
HB.instance Definition _ F (f : 'ONB(F;U)) (i : F) := 
  NormalState.copy (f i) ((f : 'PONB) i : 'NS).

HB.instance Definition _ (i : 'I_(dim U)) := 
  NormalState.copy (eb i) ((eb : 'ONB) i : 'NS).

Lemma zero_ps_subproof : [<0 : U ; 0>] <= 1.
Proof. by rewrite linear0 ler01. Qed.
HB.instance Definition _ := isPartialState.Build U 0 zero_ps_subproof.

Lemma bound1lf_ps (V : chsType) (f : 'FB1(U,V)) (v : 'PS(U)) :
  [< f (v : U) ; f (v : U) >] <= 1.
Proof.
move: (is_bound1lf f)=>/bound1lfP/(_ (v : U)) P1.
apply/(le_trans P1)/ps_dot.
Qed.

HB.instance Definition _ (V : chsType) (f : 'FB1(U,V)) (v : 'PS(U)) := 
  isPartialState.Build V (f (v : U)) (bound1lf_ps f v).

End PartialStateTheory.

Section NormalizedStateTheory.
Variable (U : chsType) (v : 'NS(U)).

Lemma ns_norm : `|v : U| = 1.
Proof. by rewrite hnormE ns_dot sqrtC1. Qed.

Lemma ns_neq0 : (v : U) != 0.
Proof. by rewrite -normr_eq0 ns_norm oner_neq0. Qed.

Lemma ns_eq0F : (v : U) == 0 = false.
Proof. by apply/eqP/eqP; exact: ns_neq0. Qed.

Lemma ns_scale_eq0 (c : C) : c *: (v : U) == 0 = (c == 0).
Proof. by rewrite scaler_eq0 ns_eq0F orbF. Qed.

Lemma ns_scaleI : injective (GRing.scale ^~ (v : U)).
Proof.
by move=>??/eqP; rewrite -subr_eq0 -scalerBl ns_scale_eq0 subr_eq0=>/eqP.
Qed.

Lemma isolf_ns (V : chsType) (f : 'FI(U,V)) :
  [< f (v : U) ; f (v : U) >] = 1.
Proof. by rewrite -adj_dotEl isofKE ns_dot. Qed.

HB.instance Definition _ (V : chsType) (f : 'FI(U,V)) := 
  Partial_isNormalState.Build V (f (v : U)) (isolf_ns f).

End NormalizedStateTheory.

Section LownerorderLfun.
Context {V: chsType}.
Implicit Type (f g h : 'End(V)).

Definition lef_def f g := (g - f) \is psdlf.
(* Definition ltf_def f g := (g != f) && (lef_def f g). *)

Lemma lef_def_mx f g : lef_def f g = (h2mx f ⊑ h2mx g).
Proof. by rewrite /lef_def qualifE linearB/= le_lownerE. Qed.

(* Lemma ltf_def_mx f g : ltf_def f g = (h2mx f ⊏ h2mx g).
Proof. by rewrite /ltf_def lt_def (can_eq (@h2mxK _ _)) lef_def_mx. Qed.

Lemma ltf_def_def : forall f g, ltf_def f g = (g != f) && (lef_def f g).
Proof. by rewrite /lef_def. Qed. *)

Lemma lef_def_anti : antisymmetric lef_def.
Proof. by move=>x y; rewrite !lef_def_mx -eq_le=>/eqP/h2mx_inj. Qed.

Lemma lef_def_refl : reflexive lef_def.
Proof. by move=>x; rewrite lef_def_mx. Qed.

Lemma lef_def_trans : transitive lef_def.
Proof. by move=>x y z; rewrite !lef_def_mx; apply le_trans. Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build ring_display 'End(V)
  lef_def_refl lef_def_anti lef_def_trans.

(* HB.instance Definition _ := [SubChoice_isSubPOrder of 'F+(V) by <: with ring_display]. *)
HB.instance Definition _ := [SubChoice_isSubPOrder of 'FD(V) by <: with ring_display].
HB.instance Definition _ := [SubChoice_isSubPOrder of 'FO(V) by <: with ring_display].

Lemma lef_h2mx f g : f ⊑ g = (h2mx f ⊑ h2mx g).
Proof. by rewrite {1}/Order.le/= lef_def_mx. Qed.

Lemma ltf_h2mx f g : f ⊏ g = (h2mx f ⊏ h2mx g).
Proof. by rewrite !lt_def lef_h2mx (inj_eq h2mx_inj). Qed.

Lemma lef_add2rP h f g : f ⊑ g -> (f + h) ⊑ (g + h).
Proof. by rewrite addrC /Order.le/= /lef_def opprD addrA addrK. Qed.

Lemma lef_pscale2lP (e : C) f g : 0 < e -> f ⊑ g -> (e *: f) ⊑ (e *: g).
Proof. rewrite !lef_h2mx !linearZ/=; exact: lev_pscale2lP. Qed.

Lemma pscalef_lge0 f (a : C) : 
  (0 : 'End(V)) ⊏ f -> (0 : 'End(V)) ⊑ a *: f = (0 <= a).
Proof. rewrite lef_h2mx ltf_h2mx linear0 linearZ/=; exact: pscalev_lge0. Qed.

HB.instance Definition _ := POrderedLmodule_isVOrder.Build C 'End(V) lef_add2rP lef_pscale2lP.
HB.instance Definition _ := VOrder_isCan.Build C 'End(V) pscalef_lge0.

Lemma lefE f g : f ⊑ g = (g - f \is psdlf).
Proof. by rewrite {1}/Order.le/=. Qed.

Lemma lef_dot f g : f ⊑ g <-> forall v, [<v ; f v>] <= [<v ; g v >].
Proof.
rewrite {1}/Order.le [in X in X <-> _]/= /lef_def. 
split=>[/psdlfP P v|P]; last apply/psdlfP=>v.
all: by move: (P v); rewrite !lfunE/= !lfunE/= linearB/= subr_ge0.
Qed.

Local Notation "0" := (0 : 'End(V)).

(* Properties of the psdlf subset. *)
Lemma psdlfE f : (f \is psdlf) = (0 ⊑ f). Proof. by rewrite lefE subr0. Qed.
Lemma psdlf_ge0 f : f \is psdlf -> 0 ⊑ f. Proof. by rewrite psdlfE. Qed.
Lemma psdf_ge0 (f : 'F+(V)) : 0 ⊑ f. Proof. apply/psdlf_ge0/is_psdlf. Qed.
Lemma gef0_psd f : 0 ⊑ f -> f \is psdlf.  Proof. by rewrite psdlfE => ->. Qed.
Lemma gtf0_psd f : 0 ⊏ f -> f \is psdlf.  Proof. by move=> /ltW/gef0_psd. Qed.

Lemma psdf_le0 (f : 'F+(V)) : f%:VF ⊑ 0 -> f = 0 :> 'End(V).
Proof. by move=>P; apply/le_anti; rewrite P psdf_ge0. Qed.

Lemma gef0_formV f : 0 ⊑ f -> exists g, f = g^A \o g.
Proof.
rewrite -psdlfE qualifE=>/psdmx_form[B PB]; exists (mx2h B^*t).
by apply/h2mx_inj; rewrite adj_lfun.unlock h2mx_comp !mx2hK adjmxK.
Qed.

Lemma gef0_form f : 0 ⊑ f -> exists g, f = g \o g^A.
Proof. by move=>/gef0_formV[g Pg]; exists g^A; rewrite adjfK. Qed.

Lemma gtf0_pd f : reflect (0 ⊑ f /\ exists v, [<v ; f v>] != 0%R) (0 ⊏ f).
Proof.
rewrite lt_def; apply/(iffP andP); move=>[P1 P2]; split=>//.
move: P1=>/eqP; rewrite not_existsP; apply contra_not=>P1.
move: P2=>/gef0_formV[g Pg]; apply/lfunP=>v; move: (P1 v)=>/negP. 
rewrite negbK Pg lfunE/= -adj_dotEl adjfK dotp_eq0=>/eqP->.
by rewrite !lfunE/= linear0.
by move: P2=>[v]; apply contraNN=>/eqP->; rewrite lfunE/= linear0.
Qed.

Lemma gtf0_pdP f : reflect (0 ⊑ f /\ exists v, 0%:R < [<v ; f v>]) (0 ⊏ f).
Proof.
apply/(iffP (gtf0_pd f)); move=>[fge0 [v Pv]]; split=>//; exists v.
by rewrite lt0r Pv/=; apply/psdlfP; rewrite psdlfE.
by apply/lt0r_neq0.
Qed.

Lemma trlf0_eq0 f : reflect (0 ⊑ f /\ \Tr f = 0%R) (f == 0).
Proof.
apply/(iffP eqP)=>[->|]; first by rewrite linear0.
rewrite -psdlfE qualifE /lftrace=>[[P1]].
by rewrite -psdmx_trnorm// =>/trnorm0_eq0/(f_equal mx2h); rewrite h2mxK mx2h0.
Qed.

Lemma lef01 : 0 ⊑ \1.
Proof. by apply lef_dot=>v; rewrite !lfunE/= linear0 ge0_dotp. Qed.

Lemma ltf01 : 0 ⊏ \1.
Proof. by rewrite lt_def lef01 (oner_neq0 ('End(V) : ringType)). Qed.

Lemma lef_adj x y : (x^A ⊑ y^A) = (x ⊑ y).
Proof. by rewrite -subv_ge0 -psdlfE -linearB/= psdlf_adj psdlfE subv_ge0. Qed.
Lemma lef_conj x y : (x^C ⊑ y^C) = (x ⊑ y).
Proof. by rewrite -subv_ge0 -psdlfE -linearB/= psdlf_conj psdlfE subv_ge0. Qed.
Lemma lef_tr x y : (x^T ⊑ y^T) = (x ⊑ y).
Proof. by rewrite !trfAC lef_conj lef_adj. Qed.

Lemma lef_trlf f g : f ⊑ g -> \Tr f <= \Tr g.
Proof. by rewrite lefE=>/psdlf_trlf; rewrite linearB/= subr_ge0. Qed.

Definition NnegZProp (T : numDomainType) (U : lmodType T) (P : U -> Prop) :=
  forall c : T, 0%R <= c -> forall x : U, P x -> P (c *: x).

Lemma psdlfZ (c : C) (x : 'End(V)) : 0%R <= c -> x \is psdlf -> c*:x \is psdlf.
Proof.
by rewrite qualifE=>P1 /(psdmxZ P1);
rewrite -linearZ/= [in X in _ -> X]qualifE.
Qed.

Lemma denlf_psdlf_eq_nnegz (P : 'End(V) -> Prop) : NnegZProp P ->
  (forall x, x \is denlf -> P x) <-> (forall x, x \is psdlf -> P x).
Proof.
move=>IH; split=>[H x Px|H x /denlf_psd/H//].
have Pt : \Tr x >= 0%R by move: Px; rewrite psdlfE=>/lef_trlf; rewrite linear0.
have ->: (x = \Tr x *: ((\Tr x)^-1 *: x)).
  case E: (\Tr x == 0%R); last by rewrite scalerA mulfV ?E// scale1r.
  by move: (conj Px (eqP E)); rewrite psdlfE=>/trlf0_eq0/eqP->; rewrite !scaler0.
apply/IH=>//; apply/H/denlfP; split.
  by apply/psdlfZ=>//; rewrite invr_ge0.
rewrite !linearZ/=; case E: (\Tr x == 0%R).
by move: E=>/eqP->; rewrite mulr0.
by rewrite mulVf// E.
Qed.

Lemma denlf_denf_eq_prop (P : 'End(V) -> Prop) :
  (forall x, x \is denlf -> P x) <-> (forall x : 'FD, P x).
Proof.
split; first by move=>H x; apply/H/is_denlf.
move=>H x Px; have ->: x = DenLf_Build Px by apply/val_inj. apply/H.
Qed.

Lemma psdlf_psdf_eq_prop (P : 'End(V) -> Prop) :
  (forall x, x \is psdlf -> P x) <-> (forall x : 'F+, P x).
Proof.
split; first by move=>H x; apply/H/is_psdlf.
move=>H x Px; have ->: x = PsdLf_Build Px by apply/val_inj. apply/H.
Qed.

Lemma trlf_compr_le_nnegz f g : 
  NnegZProp (fun x : 'End(V) => \Tr (f \o x) <= \Tr (g \o x)).
Proof.
by move=>/= c Pc x Px; rewrite -!comp_lfunZr !linearZ/=; apply/ler_wpM2l.
Qed.

Lemma lef_dentr f g :
  reflect (forall x, x \is denlf -> \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
rewrite lef_h2mx; apply/(iffP (@le_lownerE_dentr _ _ _ _))=>P x Px.
rewrite /lftrace !h2mx_comp P=>[|//]; by move: Px; rewrite qualifE.
have: mx2h x \is denlf by rewrite qualifE mx2hK.
by move=>/P; rewrite /lftrace !h2mx_comp/= mx2hK.
Qed.

Lemma lef_psdtr f g :
  reflect (forall x, x \is psdlf -> \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
by apply/(iffP (lef_dentr _ _)); 
  rewrite (denlf_psdlf_eq_nnegz (@trlf_compr_le_nnegz f g)).
Qed.

Lemma lef_obstr f g : 
  reflect (forall x, x \is obslf -> \Tr (f \o x) <= \Tr (g \o x))	(f ⊑ g).
Proof.
apply/(iffP idP)=>[/lef_psdtr P x /obslf_psd/P//|P].
by apply/lef_dentr=>x /denlf_obs/P.
Qed.

Lemma lef_trden f g : 
  reflect (forall x : 'FD(V), \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
apply/(iffP (lef_dentr _ _))=>[H x|H x P].
by apply/H/is_denlf. by move: (H (HB.pack x (isDenLf.Build _ x P))).
Qed.

Lemma lef_trobs f g : 
  reflect (forall x : 'FO(V), \Tr (f \o x) <= \Tr (g \o x)) (f ⊑ g).
Proof.
apply/(iffP (lef_obstr _ _))=>[H x|H x P].
by apply/H/is_obslf. by move: (H (ObsLf_Build P)).
Qed.

End LownerorderLfun.

Section LownerorderForm.
Variable (U V: chsType) .

Lemma formV_gef0 (f : 'Hom(U,V)) :  (0 : 'End(V)) ⊑ f \o f^A.
Proof. by rewrite -psdlfE; apply/psdlfP=>v; rewrite lfunE/= -adj_dotEl ge0_dotp. Qed.

Lemma form_gef0 (f : 'Hom(U,V)) : (0 : 'End(U)) ⊑ f^A \o f.
Proof.
by rewrite -psdlfE; apply/psdlfP=>v;
rewrite lfunE/= -adj_dotEl adjfK ge0_dotp.
Qed.

Lemma form_eq0 (f : 'Hom(U,V)) : f^A \o f == 0 = (f == 0).
Proof.
apply/eqb_iff; rewrite !eq_iff; split=>[P1|->]; last by rewrite comp_lfun0r.
apply/lfunP=>v; rewrite lfunE/=; apply/eqP;
by rewrite -normr_eq0 hnormE -adj_dotEl -comp_lfunE P1 lfunE/= linear0l sqrtC0.
Qed.

Lemma formV_eq0 (f : 'Hom(U,V)) : f \o f^A == 0 = (f == 0).
Proof. 
apply/eqb_iff; rewrite !eq_iff; split=>[P1|->]; last by rewrite comp_lfun0l.
apply/adjf_inj/lfunP=>v; rewrite raddf0 lfunE/=; apply/eqP.
by rewrite -normr_eq0 hnormE adj_dotEl -comp_lfunE P1 lfunE/= linear0 sqrtC0.
Qed.

Lemma lef_formV (g1 g2: 'End(U)) (f: 'Hom(U,V))  :
  g1 ⊑ g2 -> f \o g1 \o f^A ⊑ f \o g2 \o f^A.
Proof.
move=>/lef_dot=>P; apply/lef_dot=>v; move: (P (f^A v)).
by rewrite !lfunE/= !lfunE/= -!adj_dotEl.
Qed.

Lemma lef_form (g1 g2: 'End(U)) (f: 'Hom(V,U)) :
  g1 ⊑ g2 -> f^A \o g1 \o f ⊑ f^A \o g2 \o f.
Proof. by move=>/(@lef_formV _ _ f^A); by rewrite !adjfK. Qed.

Lemma gef0_formfV (g: 'End(U)) (f: 'Hom(U,V))  :
  (0 : 'End(_)) ⊑ g -> (0 : 'End(_)) ⊑ f \o g \o f^A.
Proof. by move=>/(lef_formV f); rewrite comp_lfun0r comp_lfun0l. Qed.

Lemma gef0_formf (g: 'End(U)) (f: 'Hom(V,U))  :
  (0 : 'End(_)) ⊑ g -> (0 : 'End(_)) ⊑ f^A \o g \o f.
Proof. by move=>/(lef_form f); rewrite comp_lfun0r comp_lfun0l. Qed.

End LownerorderForm.

Section LownerorderExtra.
Variable (U: chsType).

Lemma obslfE (f: 'End(U)) :
  f \is obslf = (((0 : 'End(U)) ⊑ f) && (f ⊑ \1)).
Proof. by rewrite !lef_h2mx qualifE obsmx_psd_eq !le_lownerE h2mx1 linear0 subr0. Qed.

Lemma psdlf_TrM (f g: 'End(U)) : 
  f \is psdlf -> g \is psdlf -> 0%:R <= \Tr (f \o g).
Proof.
rewrite !psdlfE=>/gef0_formV[h ->] /(lef_formV h)/lef_trlf.
by rewrite comp_lfun0r comp_lfun0l linear0 [\Tr (_ \o h^A)]lftraceC comp_lfunA.
Qed.

Lemma denf_ges0 (x : 'FD(U)) : (0%:VF : 'FD) ⊑ x.
Proof. by rewrite leEsub/= -psdlfE; apply/denlf_psd/is_denlf. Qed.

Lemma denf_ge0 (x : 'FD(U)) : (0 : 'End(U)) ⊑ x.
Proof. by move: (denf_ges0 x); rewrite leEsub. Qed.

Lemma denf_le1 (x : 'FD(U)) : (x : 'End(U)) ⊑ \1.
Proof. 
rewrite lefE; apply/psdlfP=>u.
rewrite lfunE/= lfunE/= lfunE/= linearB/= subr_ge0.
by move: (is_denlf x)=>/denlf_obs/obslfP[_ P]. 
Qed.

Lemma obsf_ges0 (x : 'FO(U)) : (0%:VF : 'FO) ⊑ x.
Proof. by rewrite leEsub/= -psdlfE; apply/obslf_psd/is_obslf. Qed.

Lemma obsf_ge0 (x : 'FO(U)) : (0 : 'End(U)) ⊑ x.
Proof. by move: (obsf_ges0 x); rewrite leEsub. Qed.

Lemma obsf_les1 (x : 'FO(U)) : x ⊑ \1.
Proof.
rewrite leEsub/= lefE; move: (is_obslf x)=>/obslfP[_ P].
by apply/psdlfP=>u; rewrite lfunE/= !lfunE/= linearB/= subr_ge0 P.
Qed.

Lemma obslf_le1 (x : 'End(U)) : x \is obslf -> x ⊑ \1.
Proof. by rewrite obslfE=>/andP[]. Qed.

Lemma obsf_le1 (x : 'FO(U)) : (x : 'End(U)) ⊑ \1.
Proof. apply/obslf_le1/is_obslf. Qed.

Lemma obslf_lefP (A : 'End(U)) : 
  reflect (0%:VF ⊑ A /\ (A ⊑ \1)) (A \is obslf).
Proof. by rewrite obslfE; apply/(iffP andP). Qed.

Lemma lfun_neq0P (V : chsType) (f : 'Hom(U,V)) : 
  reflect (exists v, [< f v ; f v >] != 0) (f != 0).
Proof.
apply/(iffP negP); rewrite not_existsP; apply contra_not.
by move=>P; apply/eqP/lfunP=>u; move: (P u)=>/negP;
rewrite negbK dotp_eq0 lfunE/==>/eqP.
by move=>/eqP-> x; rewrite lfunE/= linear0 eqxx.
Qed.

Lemma bound1lf_form_le1 (V : chsType) (f : 'Hom(U,V)) :
  f \is bound1lf = (f^A \o f <= \1).
Proof. by rewrite bound1lf_obsE obslfE form_gef0. Qed.

Lemma bound1lf_formV_le1 (V : chsType) (f : 'Hom(V,U)) :
  f \is bound1lf = (f \o f^A <= \1).
Proof. by rewrite -bound1lf_adj bound1lf_form_le1 adjfK. Qed.

Lemma bound1f_form_le1 V (f : 'FB1(U,V)) : f^A \o f <= \1.
Proof. by rewrite -bound1lf_form_le1 is_bound1lf. Qed.

Lemma bound1f_formV_le1 V (f : 'FB1(V,U)) : f \o f^A <= \1.
Proof. by rewrite -bound1lf_formV_le1 is_bound1lf. Qed.

End LownerorderExtra.

Section Outp.
Variable (H : chsType).

Lemma outp_ge0 (v : H) : (0 : 'End(H)) ⊑ [> v ; v <].
Proof. 
apply/lef_dot=>u; rewrite lfunE/= linear0 outpE 
  linearZ/= -conj_dotp -normCKC exprn_ge0//.
Qed.
Lemma outp_psd (v : H) : [> v ; v <] \is psdlf.
Proof. by rewrite psdlfE outp_ge0. Qed.
HB.instance Definition _ v := isPsdLf.Build H [> v ; v <] (@outp_psd v).

Lemma outp_den (v : 'PS(H)) : [> v ; v <] \is denlf.
Proof. by apply/denlfP; split; [apply/is_psdlf | rewrite outp_trlf ps_dot]. Qed.
HB.instance Definition _ (v : 'PS(H)) := Psd_isObsLf.Build 
  H [> v ; v <] (denlf_obs (@outp_den v)).
HB.instance Definition _ (v : 'PS(H)) := Obs_isDenLf.Build 
  H [> v ; v <] (@outp_den v).

Lemma outp_proj1 (v : 'NS(H)) : [> v; v <] \is proj1lf.
Proof.
apply/proj1lfP; split; last by rewrite outp_trlf ns_dot.
by apply/projlfP; rewrite adj_outp outp_comp ns_dot scale1r.
Qed.
HB.instance Definition _ (v : 'NS(H)) := Obs_isProjLf.Build 
  H [> v ; v <] (proj1lf_proj (@outp_proj1 v)).
HB.instance Definition _ (v : 'NS(H)) := Den_isDen1Lf.Build 
  H [> v ; v <] (proj1lf_den1 (@outp_proj1 v)).

Lemma outp_le1 (v : H) : [< v ; v >] <= 1 -> [> v; v <] ⊑ \1.
Proof.
move=>P. apply/lef_dot=>u; rewrite outpE dotpZr -conj_dotp -normCKC.
by apply: (le_trans (CauchySchwartz _ _)); rewrite lfunE/= ler_piMr// ge0_dotp.
Qed.
Lemma ns_outp_le1 (v : 'NS(H)) : [> v; v <] ⊑ \1.
Proof. by apply outp_le1; rewrite ns_dot. Qed.

End Outp.

Lemma sumponb_out (U : chsType) (F : finType) (p : 'PONB(F;U)) :
  \sum_i [> p i ; p i <] <= \1.
Proof.
by rewrite -(sumonb_out (ponb_ext p)) big_sumType/= levDl sumv_ge0// =>??; 
rewrite outp_ge0.
Qed.

Section SuperOperatorDef.
Variable (U V: chsType).

Variant superop : predArgType := 
  Superop of 'Hom('End(U),'End(V)).

Definition so_val A := let: Superop g := A in g.

HB.instance Definition _ := [isNew for so_val].

Definition fun_of_superof A x := so_val A x.

Coercion fun_of_superof : superop >-> Funclass.

End SuperOperatorDef.

Fact superop_key : unit. Proof. by []. Qed.
HB.lock 
Definition superof_of_fun (U V : chsType) (k : unit) (F : 'Hom('End(U),'End(V))) :=
  @Superop U V F.
Canonical superof_unlockable := Unlockable superof_of_fun.unlock.

Notation "''SO' ( S , T )" := (@superop S T) : type_scope.
Notation "''SO' ( S )" := ('SO(S,S)) : type_scope.
Notation "''SO'" := (@superop _ _) (only parsing) : type_scope.
Notation SOType F := (superof_of_fun superop_key F).

HB.instance Definition _ U V := [Equality of 'SO(U,V) by <:].
HB.instance Definition _ U V := [Choice of 'SO(U,V) by <:].

Section  SuperOperator.
Variable (U V : chsType).
Implicit Type (F : 'Hom('End(U), 'End(V))).
Local Notation SO := ('SO(U,V)).

Lemma superopE k F : superof_of_fun k F =1 F.
Proof. by move=> i; rewrite unlock /fun_of_superof. Qed.

Lemma soK k F : so_val (superof_of_fun k F) = F.
Proof. by rewrite unlock/=. Qed.

Lemma superopP (A B : SO) : A =1 B <-> A = B.
Proof.
rewrite /fun_of_superof; split=> [/= eqAB | -> //].
by apply/val_inj/lfunP=>i; apply eqAB.
Qed.

Lemma superop_is_linear (A: SO) : linear A.
Proof. by move=>a x y; rewrite /fun_of_superof/= linearP. Qed.
HB.instance Definition _ (A : SO) := 
  GRing.isLinear.Build C 'End(U) 'End(V) _ A (@superop_is_linear A).

Lemma so_psdP (u v : SO) : (forall x, x \is psdlf -> u x = v x) <-> u = v.
Proof.
split=>[P|->//]. apply/superopP=>x.
move: (lf_psd_decomp x)=>[f1 [f2 [f3 [f4]]]] [/P P1] [/P P2] [/P P3] [/P P4]->.
do ! (rewrite linearD/= [RHS]linearD/=; congr (_ + _)); 
[by [] | by  rewrite !linearN/= P2 | by rewrite !linearZ/= P3 |
by rewrite !linearN/=; congr (- _); rewrite !linearZ/= P4].
(* time by rewrite !linearD/= !linearN/= !linearZ/= P1 P2 P3 P4. *)
Qed.

Lemma so_ebP (u v : SO) :
  (forall i j, u (delta_lf i j) = v (delta_lf i j)) <-> u = v.
Proof.
split=>[P|->//]; apply/superopP=>x.
rewrite (lfun_sum_delta x) !linear_sum/=. apply eq_bigr=>i _.
rewrite !linear_sum/=. apply eq_bigr=>j _. by rewrite !linearZ/= P.
Qed.

Lemma eq_so k (F1 F2 : 'Hom('End(U), 'End(V))) : 
  (F1 =1 F2) -> superof_of_fun k F1 = superof_of_fun k F2.
Proof. by move=> eq_F; apply/superopP => i; rewrite !superopE eq_F. Qed.

Definition abortso : SO := SOType 0.
Definition oppso A : SO := SOType (- (so_val A)).
Definition addso A B : SO := SOType ((so_val A) + (so_val B)).
Definition scaleso (x : C) A : SO := SOType (x *: (so_val A)).
Lemma addsoA : associative addso.
Proof. by move=> A B C; apply/val_inj; rewrite /= !soK addrA. Qed.
Lemma addsoC : commutative addso.
Proof. by move=> A B; apply/val_inj; rewrite /= !soK addrC. Qed.
Lemma add0so : left_id abortso addso.
Proof. by move=> A; apply/val_inj; rewrite /= !soK add0r. Qed.
Lemma addNso : left_inverse abortso oppso addso.
Proof. by move=> A; apply/val_inj; rewrite /= !soK addNr. Qed.

HB.instance Definition _ := GRing.isZmodule.Build SO addsoA addsoC add0so addNso.

Lemma scale1so A : scaleso 1 A = A.
Proof. by apply/val_inj; rewrite /= !soK scale1r. Qed.
Lemma scalesoDl A (x y : C) : scaleso (x + y) A = scaleso x A + scaleso y A.
Proof. by apply/val_inj; rewrite /= !soK scalerDl. Qed.
Lemma scalesoDr (x : C) A B : scaleso x (A + B) = scaleso x A + scaleso x B.
Proof. by apply/val_inj; rewrite /= !soK scalerDr. Qed.
Lemma scalesoA (x y : C) A : scaleso x (scaleso y A) = scaleso (x * y) A.
Proof. by apply/val_inj; rewrite /= !soK scalerA. Qed.

HB.instance Definition _ := 
  GRing.Zmodule_isLmodule.Build C SO scalesoA scale1so scalesoDr scalesoDl.

(* Lemma soconstruct_is_linear : linear Superop.
Proof. by move=>x A B; apply/val_inj; rewrite /=!soK. Qed.
Canonical soconstruct_linear := Linear soconstruct_is_linear.
Lemma so_val_is_linear : linear so_val.
Proof. by move=>x A B; rewrite !soK. Qed.
Canonical so_val_linear := Linear so_val_is_linear. *)

Lemma abort_soE x : abortso x = 0. Proof. by rewrite superopE lfunE. Qed.
Lemma add_soE (f g : SO) x : (f + g) x = f x + g x. Proof. by rewrite superopE lfunE. Qed.
Lemma opp_soE (f : SO) x : (- f) x = - f x. Proof. by rewrite superopE lfunE. Qed.
Lemma sum_soE I (r : seq I) (P : pred I) (fs : I -> SO) x :
  (\sum_(i <- r | P i) fs i) x = \sum_(i <- r | P i) fs i x.
Proof. by elim/big_rec2: _ => [|i _ f _ <-]; rewrite superopE lfunE. Qed.
Lemma scale_soE k (f : SO) x : (k *: f) x = k *: f x. Proof. by rewrite superopE lfunE. Qed.

End SuperOperator.

Section CompSuperopDef.

Definition idso (T:chsType) : 'SO(T):= SOType \1%VF.

Definition comp_so (U V W : chsType) (A : 'SO(U,V)) (B : 'SO(W,U)) := 
    SOType ((so_val A) \o (so_val B))%VF.
Definition comp_sor (U V W : chsType) (A : 'SO(U,V)) (B : 'SO(V,W)) := 
    SOType ((so_val B) \o (so_val A))%VF.

End CompSuperopDef.

Arguments idso {T}.
Notation "\:1" := (@idso _) : lfun_scope.
Notation "E ':o' F" := (comp_so E F) : lfun_scope.
Notation "E 'o:' F" := (comp_sor E F) : lfun_scope.
Lemma comp_soElr (U V W : chsType) (f : 'SO(U,V)) (g : 'SO(W,U)) : 
  (f :o g) = g o: f. 
Proof. by []. Qed.
Lemma comp_soErl (U V W : chsType) (f : 'SO(U,V)) (g : 'SO(V,W)) : 
  (f o: g) = g :o f. 
Proof. by []. Qed.

Notation "\compl_ ( i <- r | P ) F" := 
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i <- r | P%B) F%VF ) : lfun_scope.
Notation "\compl_ ( i <- r ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i <- r) F%VF) : lfun_scope.
Notation "\compl_ ( m <= i < n | P ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_( m%N <= i < n%N | P%B) F%VF)%BIG) 
    : lfun_scope.
Notation "\compl_ ( m <= i < n ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_(m%N <= i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compl_ ( i | P ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i | P%B) F%VF) : lfun_scope.
Notation "\compl_ i F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_i F%VF) : lfun_scope.
Notation "\compl_ ( i : t | P ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i : t | P%B) F%VF) (only parsing) 
    : lfun_scope.
Notation "\compl_ ( i : t ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i : t) F%VF) (only parsing) : lfun_scope.
Notation "\compl_ ( i < n | P ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_(i < n%N | P%B) F%VF)%BIG) : lfun_scope.
Notation "\compl_ ( i < n ) F" :=
  ((\big[ (@comp_so _ _ _) / (@idso _) ]_(i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compl_ ( i 'in' A | P ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i in A | P%B) F%VF) : lfun_scope.
Notation "\compl_ ( i 'in' A ) F" :=
  (\big[ (@comp_so _ _ _) / (@idso _) ]_(i in A) F%VF) : lfun_scope.

Notation "\compr_ ( i <- r | P ) F" := 
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i <- r | P%B) F%VF ) : lfun_scope.
Notation "\compr_ ( i <- r ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i <- r) F%VF) : lfun_scope.
Notation "\compr_ ( m <= i < n | P ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_( m%N <= i < n%N | P%B) F%VF)%BIG) 
    : lfun_scope.
Notation "\compr_ ( m <= i < n ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_(m%N <= i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compr_ ( i | P ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i | P%B) F%VF) : lfun_scope.
Notation "\compr_ i F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_i F%VF) : lfun_scope.
Notation "\compr_ ( i : t | P ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i : t | P%B) F%VF) (only parsing) 
    : lfun_scope.
Notation "\compr_ ( i : t ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i : t) F%VF) (only parsing) : lfun_scope.
Notation "\compr_ ( i < n | P ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_(i < n%N | P%B) F%VF)%BIG) : lfun_scope.
Notation "\compr_ ( i < n ) F" :=
  ((\big[ (@comp_sor _ _ _) / (@idso _) ]_(i < n%N) F%VF)%BIG) : lfun_scope.
Notation "\compr_ ( i 'in' A | P ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i in A | P%B) F%VF) : lfun_scope.
Notation "\compr_ ( i 'in' A ) F" :=
  (\big[ (@comp_sor _ _ _) / (@idso _) ]_(i in A) F%VF) : lfun_scope.

Section CompSuperop.
Variable (U V W T: chsType).
Implicit Types (f : 'SO(W, T)) (g : 'SO(V, W)) (h : 'SO(U, V)).

Lemma id_soE (K : chsType) (u : 'End(K)) : \:1 u = u .
Proof. by rewrite superopE !lfunE. Qed.

Lemma comp_soE f g u : (f :o g) u = f (g u).
Proof. by rewrite superopE !lfunE. Qed.
Lemma comp_sorE g f u : (g o: f) u = f (g u).
Proof. by rewrite superopE !lfunE. Qed.

Lemma comp_soA f g h : (f :o (g :o h) = (f :o g) :o h).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunA. Qed.
Lemma comp_sorA h g f : (h o: (g o: f) = (h o: g) o: f).
Proof. by apply/val_inj; rewrite /= !soK comp_lfunA. Qed.

Lemma linear_comp_so f : linear (@comp_so W T V f).
Proof. by move=>a u v; apply/val_inj; rewrite /= !soK comp_lfunDr comp_lfunZr. Qed.

HB.instance Definition _ f := GRing.isLinear.Build C 'SO(V, W) 'SO(V, T)
  *:%R (@comp_so W T V f) (@linear_comp_so f).

Lemma linear_compr_so g : linear ((@comp_so W T V)^~ g).
Proof. by move=>a u v; apply/val_inj; rewrite /= !soK comp_lfunDl comp_lfunZl. Qed.

HB.instance Definition _ := bilinear_isBilinear.Build C 'SO(W, T) 'SO(V, W) 'SO(V, T)
  *:%R *:%R (@comp_so W T V) (linear_compr_so, linear_comp_so).

Lemma linear_comp_sor g : linear (@comp_sor V W T g).
Proof. by move=>a u v; rewrite !comp_soErl linear_compr_so. Qed.

HB.instance Definition _ g := GRing.isLinear.Build C 'SO(W, T) 'SO(V, T)
  *:%R (@comp_sor V W T g) (@linear_comp_sor g).

Lemma linear_compr_sor f : linear ((@comp_sor V W T)^~ f).
Proof. by move=>a u v; rewrite !comp_soErl linear_comp_so. Qed.

HB.instance Definition _ := bilinear_isBilinear.Build C 'SO(V, W) 'SO(W, T) 'SO(V, T)
  *:%R *:%R (@comp_sor V W T) (linear_compr_sor, linear_comp_sor).

Lemma comp_so1l f : \:1 :o f = f.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1l. Qed.
Lemma comp_so1r f : f :o \:1 = f.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1r. Qed.
Lemma comp_so0l g : 0 :o g = 0 :> 'SO(V, T).
Proof. exact: linear0l. Qed.
Lemma comp_so0r f : f :o 0 = 0 :> 'SO(V, T).
Proof. exact: linear0r. Qed.
Lemma comp_soDl f1 f2 g : (f1 + f2) :o g = (f1 :o g) + (f2 :o g).
Proof. exact: linearDl. Qed.
Lemma comp_soDr f g1 g2 : f :o (g1 + g2) = (f :o g1) + (f :o g2).
Proof. exact: linearDr. Qed.
Lemma comp_soNl f g : (- f) :o g = - (f :o g).
Proof. exact: linearNl. Qed.
Lemma comp_soNr f g : f :o (- g) = - (f :o g).
Proof. exact: linearNr. Qed.
Lemma comp_soZl (k : C) f g : (k *: f) :o g = k *: (f :o g).
Proof. exact: linearZl. Qed.
Lemma comp_soZr (k : C) f g : f :o (k *: g) = k *: (f :o g).
Proof. exact: linearZr. Qed.
Lemma comp_soPl (k : C) f1 f2 g : (k *: f1 + f2) :o g = k *: (f1 :o g) + (f2 :o g).
Proof. exact: linearPl. Qed.
Lemma comp_soPr (k : C) f g1 g2 : f :o (k *: g1 + g2) = k *: (f :o g1) + (f :o g2).
Proof. exact: linearPr. Qed.

Lemma comp_sor1l g : \:1 o: g = g.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1r. Qed.
Lemma comp_sor1r g : g o: \:1 = g.
Proof. by apply/val_inj; rewrite /= !soK comp_lfun1l. Qed.
Lemma comp_sor0l f : 0 o: f = 0 :> 'SO(V, T).
Proof. exact: linear0l. Qed.
Lemma comp_sor0r g : g o: 0 = 0 :> 'SO(V, T).
Proof. exact: linear0r. Qed.
Lemma comp_sorDl g1 g2 f : (g1 + g2) o: f = (g1 o: f) + (g2 o: f).
Proof. exact: linearDl. Qed.
Lemma comp_sorDr g f1 f2 : g o: (f1 + f2) = (g o: f1) + (g o: f2).
Proof. exact: linearDr. Qed.
Lemma comp_sorNl g f : (- g) o: f = - (g o: f).
Proof. exact: linearNl. Qed.
Lemma comp_sorNr g f : g o: (- f) = - (g o: f).
Proof. exact: linearNr. Qed.
Lemma comp_sorZl (k : C) g f : (k *: g) o: f = k *: (g o: f).
Proof. exact: linearZl. Qed.
Lemma comp_sorZr (k : C) g f : g o: (k *: f) = k *: (g o: f).
Proof. exact: linearZr. Qed.
Lemma comp_sorPl (k : C) g1 g2 f : (k *: g1 + g2) o: f = k *: (g1 o: f) + (g2 o: f).
Proof. exact: linearPl. Qed.
Lemma comp_sorPr (k : C) g f1 f2 : g o: (k *: f1 + f2) = k *: (g o: f1) + (g o: f2).
Proof. exact: linearPr. Qed.

End CompSuperop.

HB.instance Definition _ (U : chsType) := Monoid.isLaw.Build 
  'SO(U) \:1 (@comp_so U U U) (@comp_soA U U U U) (@comp_so1l U U) (@comp_so1r U U).
HB.instance Definition _ (U : chsType) := Monoid.isLaw.Build 
  'SO(U) \:1 (@comp_sor U U U) (@comp_sorA U U U U) (@comp_sor1l U U) (@comp_sor1r U U).

Lemma comp_soACA (U1 U2 U3 U4 U5 : chsType) (A: 'SO(U4,U5)) (B: 'SO(U3,U4))
(C: 'SO(U2,U3)) (D: 'SO(U1,U2)) :
  A :o B :o C :o D = A :o (B :o C) :o D.
Proof. by rewrite !comp_soA. Qed.

Lemma comp_sorACA (U1 U2 U3 U4 U5 : chsType) (A: 'SO(U1,U2)) (B: 'SO(U2,U3))
(C: 'SO(U3,U4)) (D: 'SO(U4,U5)) :
  A o: B o: C o: D = A o: (B o: C) o: D.
Proof. by rewrite !comp_sorA. Qed.

Definition krausso_fun (U V: chsType) (F : finType) (f : F -> 'Hom(U,V)) := 
  (fun x : 'End(U) => \sum_i ((f i) \o x \o (f i)^A)).
HB.lock Definition krausso U V F f := SOType (linfun (@krausso_fun U V F f)).

Definition ifso_fun (U V W : chsType) (F : finType) (f : F -> 'Hom(U,V)) 
  (br : forall (i : F), 'SO(V,W)) :=
    (fun x : 'End(U) => \sum_i (br i ((f i) \o x \o (f i)^A))).
HB.lock Definition ifso U V W F f br := SOType (linfun (@ifso_fun U V W F f br)).

Section KrausIfSuperop.
Variable (U V W: chsType).

Lemma krausso_fun_is_linear F f : linear (@krausso_fun U V F f).
Proof. 
move=>a x y; rewrite /krausso_fun linear_sum -big_split/=.
by apply eq_bigr=>i _; rewrite linearPr linearPl.
Qed.
HB.instance Definition _ F f := GRing.isLinear.Build C 'End(U) 'End(V) 
  *:%R (@krausso_fun U V F f) (@krausso_fun_is_linear F f).

Lemma kraussoE F f x : (@krausso U V F f) x = \sum_i ((f i) \o x \o (f i)^A).
Proof. by rewrite krausso.unlock superopE lfunE/=. Qed.

Lemma krausso_reindex (I J : finType) (h : J -> I) F G :
  bijective h -> (forall j, F (h j) = G j ) -> 
    @krausso U V I F = @krausso U V J G.
Proof.
move=>[g hK gK] P1; apply/superopP=>x.
rewrite !kraussoE (@reindex _ _ _ _ _ h)//=; first by exists g=>s _.
by apply eq_bigr=>i _; rewrite P1.
Qed.

Definition formso (f : 'Hom(U,V)) := krausso (fun _ : 'I_1 =>f).

Lemma formsoE f x : (formso f) x = f \o x \o f^A. 
Proof. by rewrite kraussoE big_ord1. Qed.

Lemma formso0 : (formso 0) = 0.
Proof. by apply/superopP=>x; rewrite formsoE abort_soE !comp_lfun0l. Qed.

Lemma ifso_fun_is_linear F f br : linear (@ifso_fun U V W F f br).
Proof. 
move=>a x y; rewrite /ifso_fun linear_sum/= -big_split/=.
by apply eq_bigr=>i _; rewrite linearPr linearPl linearP.
Qed.
HB.instance Definition _ F f br := GRing.isLinear.Build C 'End(U) 'End(W) 
  *:%R (@ifso_fun U V W F f br) (@ifso_fun_is_linear F f br).

Lemma ifsoE F f br x : (@ifso U V W F f br) x = \sum_i (br i ((f i) \o x \o (f i)^A)).
Proof. by rewrite ifso.unlock superopE lfunE. Qed.

End KrausIfSuperop.

Section KrausSuperopExtra.

Lemma formso1 (U : chsType) : formso (\1 : 'End(U)) = \:1.
Proof. by apply/superopP=>x; rewrite formsoE adjf1 id_soE comp_lfun1l comp_lfun1r. Qed.

Lemma comp_krausso (U V W : chsType) (F G : finType) (f : F -> 'Hom(U,V)) 
  (g : G -> 'Hom(W,U)) :
  krausso f :o krausso g = krausso (fun i : F * G => f i.1 \o g i.2).
Proof.
apply/superopP=>x; rewrite comp_soE !kraussoE.
under eq_bigr do rewrite linear_sumr linear_suml/=.
by rewrite pair_big/=; apply eq_bigr=>i _; rewrite adjf_comp !comp_lfunA.
Qed.

Lemma compr_krausso (U V W : chsType) (F G : finType) (f : F -> 'Hom(U,V)) 
  (g : G -> 'Hom(V, W)) :
  krausso f o: krausso g = krausso (fun i : F * G => g i.2 \o f i.1).
Proof.
apply/superopP=>x. rewrite comp_soE !kraussoE.
under eq_bigr do rewrite linear_sumr linear_suml/=.
by rewrite exchange_big pair_big/=; apply eq_bigr=>i _; rewrite adjf_comp !comp_lfunA.
Qed.

Lemma ifso_krausso (U V W : chsType) (F : finType) (f : F -> 'Hom(U,V)) 
  (G : F -> finType) (br : forall (i : F), G i -> 'Hom(V,W)) :
  ifso f (fun i=>krausso (br i)) = 
  krausso (fun i : {i : F & G i} => br (tag i) (tagged i) \o f (tag i)).
Proof.
apply/superopP=>x. rewrite ifsoE !kraussoE.
under eq_bigr do rewrite kraussoE.
by rewrite sig_big_dep/=; apply eq_bigr=>i _; rewrite adjf_comp !comp_lfunA. 
Qed.

Lemma krausso_ord (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) :
  krausso f = krausso (fun i : 'I_#|F| =>f (enum_val i)).
Proof.
apply/superopP=>x; rewrite !kraussoE; apply: reindex.
by exists enum_rank=>a _; rewrite ?enum_rankK// enum_valK.
Qed.

Lemma addso_krausso (U V : chsType) (F G : finType) (f : F -> 'Hom(U,V)) 
  (g : G -> 'Hom(U,V)) :
  krausso f + krausso g = krausso (fun i : F + G => 
  match i with inl j => f j | inr k => g k end).
Proof. by apply/superopP=>x; rewrite add_soE !kraussoE big_sumType/=. Qed.

Lemma scaleso_krausso (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) (c : C) :
  0 <= c -> c *: krausso f = krausso (fun i=>sqrtC c *: f i).
Proof.
move=>Pc. apply/superopP=>x; rewrite scale_soE !kraussoE.
under [RHS]eq_bigr do rewrite -!comp_lfunZl linearZ/= -!comp_lfunZr scalerA.
by rewrite -linear_sum/=; f_equal; rewrite -normCK ger0_norm ?sqrtC_ge0// sqrtCK.
Qed.

End KrausSuperopExtra.

Definition soE := (comp_soE, scale_soE, opp_soE, add_soE, sum_soE, abort_soE, 
  id_soE, superopE, formsoE, kraussoE).

Section SOVectType.
Variable (U V: chsType).

Lemma so_vect_iso : Vector.axiom (dim 'End(U) * dim 'End(V)) 'SO(U,V).
Proof.
move: (lfun_vect_iso 'End(U) 'End(V))=>[f lf bf].
exists (f \o @so_val U V)%FUN=>[a x y /= | ]; first by rewrite !soK lf.
by apply bij_comp=>//; exists (@Superop U V)=>[x|//]; apply/val_inj.
Qed.
HB.instance Definition _ := Lmodule_hasFinDim.Build C 'SO(U,V) so_vect_iso.

End SOVectType.

Definition trace_nincr (U V : chsType) (F:finType) (f : F -> 'Hom(U,V)) 
  := (\sum_i ((f i)^A \o (f i)) ⊑ \1)%VF.

Definition trace_presv (U V : chsType) (F:finType) (f : F -> 'Hom(U,V)) 
  := (\sum_i ((f i)^A \o (f i)) == \1)%VF.

Lemma trace_presv_nincr (U V : chsType) (F:finType) (f : F -> 'Hom(U,V)) : 
  trace_presv f -> trace_nincr f.
Proof. by rewrite /trace_presv /trace_nincr=>/eqP->. Qed.

(* trace nonincreasing *)
HB.mixin Record isTraceNincr (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) := {
  is_trnincr : trace_nincr f;
}.

#[short(type="tnType")]
HB.structure Definition TraceNincr (U V : chsType) (F : finType) :=
  { f of isTraceNincr U V F f}.

Notation "''TN' ( F ; S , T )" := (tnType S T F) : type_scope.
Notation "''TN' ( F ; S )"     := ('TN(F; S, S)) : type_scope.
Notation "''TN'" := ('TN(_; _, _)) (only parsing): type_scope.

Module TraceNincrExports.
#[deprecated(since="mathcomp 2.0.0", note="Use TraceNincr.clone instead.")]
Notation "[ 'TN' 'of' f 'as' g ]" := (@TraceNincr.clone _ _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use TraceNincr.clone instead.")]
Notation "[ 'TN' 'of' f ]" := (@TraceNincr.clone _ _ _ f _) : form_scope.
End TraceNincrExports.
HB.export TraceNincrExports.

HB.mixin Record TraceNincr_isQMeasure (U V : chsType) (F : finType) 
  f of isTraceNincr U V F f := {
  is_qmeasure : trace_presv f;
}.

#[short(type="qmType")]
HB.structure Definition QMeasure (U V : chsType) (F : finType) :=
  { f of @TraceNincr U V F f & TraceNincr_isQMeasure U V F f}.

HB.factory Record isQMeasure (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) := {
  is_qmeasure : trace_presv f; 
}.
HB.builders Context U V F f of isQMeasure U V F f.
  HB.instance Definition _ := isTraceNincr.Build U V F f (trace_presv_nincr is_qmeasure).
  HB.instance Definition _ := TraceNincr_isQMeasure.Build U V F f is_qmeasure.
HB.end.

Notation "''QM' ( F ; S , T )" := (qmType S T F) : type_scope.
Notation "''QM' ( F ; S )"     := ('QM(F; S, S)) : type_scope.
Notation "''QM'" := ('QM(_; _, _)) (only parsing): type_scope.
Notation tpType := qmType (only parsing).

Module QMeasureExports.
#[deprecated(since="mathcomp 2.0.0", note="Use QMeasure.clone instead.")]
Notation "[ 'QM' 'of' f 'as' g ]" := (@QMeasure.clone _ _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use QMeasure.clone instead.")]
Notation "[ 'QM' 'of' f ]" := (@QMeasure.clone _ _ _ f _) : form_scope.
End QMeasureExports.
HB.export QMeasureExports.

Section QMBuild.
Variable (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)).

Definition TraceNincr_Build (H : trace_nincr f) :=
  TraceNincr.Pack (TraceNincr.Class (isTraceNincr.Axioms_ V F f H)).
Definition QMeasure_Build (H : trace_presv f) :=
  QMeasure.Pack (QMeasure.Class (TraceNincr_isQMeasure.Axioms_ F f 
    (isTraceNincr.Axioms_ V F f (trace_presv_nincr H)) H)).

Lemma TraceNincr_BuildE (tn : trace_nincr f) : f = TraceNincr_Build tn.
Proof. by []. Qed.
Lemma QMeasure_BuildE (tp : trace_presv f) : f = QMeasure_Build tp.
Proof. by []. Qed.
End QMBuild.

(* choimx for super operator 'Hom('End(U),'End(V))*)

HB.lock Definition so2choi (U V: chsType) (E : 'SO(U,V)) : 'M[C]_(dim U * dim V, dim U * dim V) :=
  \sum_i\sum_j (delta_mx i j *t h2mx (E (delta_lf i j))).
Definition choi2so_fun (U V: chsType) (M : 'M[C]_(dim U * dim V)) : 'End(U) -> 'End(V) :=
  (fun x => mx2h (ptrace1 (M *m ((h2mx x)^T *t 1%:M)))).
HB.lock Definition choi2so (U V: chsType) (M : 'M[C]_(dim U * dim V)) := 
  SOType (linfun (choi2so_fun M)).
HB.lock Definition choi2kraus (U V: chsType) (A : 'M[C]_(dim U * dim V)) k
 := mx2h (castmx (mul1n _, erefl _) 
  (\sum_i (delta_mx 0 i *t 1%:M) *m (sqrtC (eigenval A k) *: (eigenvec A k)) 
    *m (delta_mx (0 : 'I_1) i))).

Section SOChoiMatrix.
Variable (U V: chsType).
Implicit Type (E F : 'SO(U,V)).
Local Open Scope lfun_scope.

Local Notation so2choi := (@so2choi U V).
Local Notation choi2so := (@choi2so U V).
Local Notation choi2kraus := (@choi2kraus U V).

Lemma choimxE E x :
  ptrace1 (so2choi E *m ((h2mx x)^T *t 1%:M) ) = h2mx (E x).
Proof.
rewrite /ptrace1 [RHS]tens_mx_cast1lE; f_equal.
rewrite {2}[x]lfun_sum_delta exchange_big !linear_sum/= linear_sumr/=;
apply eq_bigr=>i _.
rewrite so2choi.unlock linear_suml/= linear_sumr/= (bigD1 i)//= [X in _ + X]big1.
  move=>j /negPf nji; rewrite linear_suml/= linear_sumr/= big1// =>k _.
  by rewrite mulmxA tensmx_mul mul_delta_mx_cond eq_sym nji mulr0n !linear0l.
rewrite addr0 !linear_sum/= !linear_suml/= !linear_sumr/= linear_suml/=.
apply eq_bigr=>j _.
rewrite !tensmx_mul mul1mx !mulmx1 mulmxA mul_delta_mx !linearZ/=.
rewrite linearZr/= -linearZl/=; f_equal; apply/matrixP=> a b; rewrite !ord1.
by rewrite dotp_ebl applyfh c2hK h2c_eb !delta_mx_mulEl
  delta_mx_mulEr !mxE eqxx !mul1r mulr1.
Qed.

Lemma choi2so_fun_is_linear M : linear (@choi2so_fun U V M).
Proof. by move=>a x y; rewrite /choi2so_fun !linearP/= linearPl/= !linearP. Qed.
HB.instance Definition _ M := GRing.isLinear.Build C 'End(U) 'End(V) *:%R 
  (@choi2so_fun U V M) (@choi2so_fun_is_linear M).

Lemma choi2so_soE M x :
  choi2so M x = mx2h (ptrace1 (M *m ((h2mx x)^T *t 1%:M))).
Proof. by rewrite choi2so.unlock superopE lfunE. Qed.

Lemma so2choiK : cancel so2choi choi2so.
Proof. by move=>E; apply/superopP=>x; rewrite choi2so_soE choimxE h2mxK. Qed.

Lemma so2choi_inj : injective so2choi.
Proof. exact: (can_inj so2choiK). Qed.

Lemma choi2so_inj : injective choi2so.
Proof.
move=>E F eqEF; apply/matrix_tenP=>a c b d.
move: eqEF=>/superopP/(_ (delta_lf a b)).
rewrite !choi2so_soE delta_lfE mx2hK=>/mx2h_inj.
move=>/matrixP/(_ c d).
have P: forall G, ptrace1 (G *m ((delta_mx a b)^T *t 1%:M)) c d
                = G (mxtens_index (a, c)) (mxtens_index (b, d)) :> C.
move=>G; rewrite trmx_delta /ptrace1 castmxE/= !mxtens_1index (bigD1 a)//= big1.
by move=>i /negPf nia; rewrite -!mulmxA/= tensmx_mul 
  mul_delta_mx_cond eq_sym nia mulr0n linear0l !mulmx0.
by rewrite addr0 -!mulmxA tensmx_mul mul_delta_mx mulmx1 ord1
  tens_delta_mx1_mulEl tens_delta_mx1_mulEr eqxx !mul1r.
by rewrite -!P.
Qed.

Lemma choi2soK : cancel choi2so so2choi.
Proof. move=>E. apply/choi2so_inj. apply so2choiK. Qed.

Lemma so2choi_is_linear : linear so2choi.
Proof.
move=>a x y; rewrite so2choi.unlock.
do 2 (rewrite linear_sum -big_split; apply eq_bigr=>? _).
by rewrite !soE/= linearP linearPr.
Qed.
HB.instance Definition _ := GRing.isLinear.Build C 'SO(U,V) 
  'M[C]_(dim U * dim V) *:%R so2choi so2choi_is_linear.

Lemma choi2so_is_linear : linear choi2so.
Proof. apply: (can2_linear so2choiK choi2soK). Qed.
HB.instance Definition _ := GRing.isLinear.Build C 'M[C]_(dim U * dim V) 
  'SO(U,V) *:%R choi2so choi2so_is_linear.

Lemma so2choi_bij : bijective so2choi.
Proof. exists choi2so. exact: so2choiK. exact: choi2soK. Qed.

Lemma choi2so_bij : bijective choi2so.
Proof. exists so2choi. exact: choi2soK. exact: so2choiK. Qed.

Definition cpmap := [qualify A : 'SO(_, _) | (so2choi A \is psdmx)].
Fact cpmap_key : pred_key cpmap. Proof. by []. Qed.
Canonical iscp_keyed := KeyedQualifier cpmap_key.

Definition tnmap := [qualify A : 'SO(_, _) | ptrace2 (so2choi A) ⊑ 1%:M].
Fact tnmap_key : pred_key tnmap. Proof. by []. Qed.
Canonical tnmap_keyed := KeyedQualifier tnmap_key.

Definition tpmap := [qualify A : 'SO(_, _) | ptrace2 (so2choi A) == 1%:M].
Fact tpmap_key : pred_key tpmap. Proof. by []. Qed.
Canonical tpmap_keyed := KeyedQualifier tpmap_key.

Definition cptn :=
  [qualify A : 'SO(_, _) | (A \is cpmap) && (A \is tnmap)].
Fact cptn_key : pred_key cptn. Proof. by []. Qed.
Canonical cptn_keyed := KeyedQualifier cptn_key.

Definition cptp :=
  [qualify A : 'SO(_, _) | (A \is cpmap) && (A \is tpmap)].
Fact cptp_key : pred_key cptp. Proof. by []. Qed.
Canonical cptp_keyed := KeyedQualifier cptp_key.

Lemma cpmapP A : reflect ((so2choi A \is psdmx)) (A \is cpmap).
Proof. by rewrite [_ \is cpmap]qualifE; apply/(iffP idP). Qed.

(*
sum_k sum_ij (xjk *: |i><k|) *t (E |i><j| *m y)
sum_k sum_ij xij *: <k| E |i><j| *m y |k>
*)
Lemma tr_choi_sep E (x: 'End(U)) (y: 'End(V)) : 
\tr (so2choi E *m (h2mx (x^T) *t (h2mx y))) = \Tr (E x \o y).
Proof.
rewrite so2choi.unlock linear_suml/= linear_sum/=.
under eq_bigr do rewrite linear_suml/= linear_sum/=.
under eq_bigr do under eq_bigr do
  rewrite /= tensmx_mul mxtrace_tens -h2mx_comp.
rewrite [in RHS](lfun_sum_delta x) linear_sum linear_suml linear_sum exchange_big.
apply eq_bigr=>i _. rewrite /= linear_sum linear_suml linear_sum/=.
apply eq_bigr=>j _. rewrite linearZ/= linearZl/= linearZ/=.
congr (_ * _); rewrite /mxtrace (bigD1 j)// big1/= =>[k /negPf nk|].
by rewrite delta_mx_mulEr eq_sym nk mul0r.
by rewrite applyfh dotp_mulmx c2hK !h2c_eb adjmx_delta !delta_mx_mulEr 
  delta_mx_mulEl !eqxx h2mx_tr mxE !mul1r addr0.
Qed.

Lemma tnmapP (A : 'SO(U,V)) : 
  reflect (forall x : 'FD, \Tr (A x) <= \Tr x) (A \is tnmap).
Proof.
rewrite qualifE -[ptrace2 _]mx2hK -h2mx1 -lef_h2mx.
apply/(iffP (lef_trden _ _))=>P x; move: (P x^T);
rewrite comp_lfun1l -[A _]comp_lfun1r -tr_choi_sep 
  h2mx1 tr_ptrace2 ptrace2_mulmxI lftrace_tr;
by apply: le_trans; rewrite ?trfK /lftrace h2mx_comp mx2hK.
Qed.

Lemma tpmapP (A : 'SO(U,V)) : 
  reflect (forall x, \Tr (A x) = \Tr x) (A \is tpmap).
Proof.
rewrite qualifE -[ptrace2 _]mx2hK -h2mx1 (inj_eq h2mx_inj).
apply/(iffP (trlf_intror _ _))=>P x; move: (P x^T);
rewrite comp_lfun1l -[A _]comp_lfun1r -tr_choi_sep 
  h2mx1 tr_ptrace2 ptrace2_mulmxI lftrace_tr=><-;
by rewrite ?trfK /lftrace h2mx_comp mx2hK.
Qed.

Lemma cptnP A : reflect (A \is cpmap /\ A \is tnmap) (A \is cptn).
Proof. by rewrite [_ \is cptn]qualifE; apply/(iffP andP). Qed.

Lemma cptpP A : reflect (A \is cpmap /\ A \is tpmap) (A \is cptp).
Proof. by rewrite [_ \is cptp]qualifE; apply/(iffP andP). Qed.

Lemma tpmap_tn A : A \is tpmap -> A \is tnmap.
Proof. by move=>/tpmapP P; apply/tnmapP=>x; move: (P x)=>->. Qed.

Lemma cptn_cpmap A : A \is cptn -> A \is cpmap.
Proof. by move=>/cptnP[]. Qed.

Lemma cptn_tnmap A : A \is cptn -> A \is tnmap.
Proof. by move=>/cptnP[]. Qed.

Lemma cptp_cptn A : A \is cptp -> A \is cptn.
Proof. by move=>/cptpP[]?/tpmap_tn ?; apply/cptnP. Qed.

Lemma cptp_cpmap A : A \is cptp -> A \is cpmap.
Proof. by move/cptp_cptn/cptn_cpmap. Qed.

Lemma cptp_tpmap A : A \is cptp -> A \is tpmap.
Proof. by move=>/cptpP[]. Qed.

Lemma cpmap_tpmap_cptp A : A \is cpmap -> A \is tpmap -> A \is cptp.
Proof. by move=>??; apply/cptpP. Qed.

Lemma cpmap_tnmap_cptn A : A \is cpmap -> A \is tnmap -> A \is cptn.
Proof. by move=>??; apply/cptnP. Qed.

Lemma krausso2choiE (F: finType) (f : F -> 'Hom(U,V)) :
let A k := \sum_i (delta_mx i (0:'I_1) *t (h2mx (f k) *m (delta_mx i (0:'I_1)))) 
  in \sum_k ((A k) *m (A k)^*t) = so2choi (krausso f).
Proof.
rewrite so2choi.unlock/=; under [RHS]eq_bigr do (under eq_bigr do rewrite soE 
  linear_sum linear_sumr; rewrite exchange_big/=).
rewrite exchange_big. apply eq_bigr=>k _.
rewrite linear_suml/=. apply eq_bigr=>i _.
rewrite linear_sum/= linear_sumr/=. apply eq_bigr=>j _.
rewrite adjmx_tens tensmx_mul adjmxM !adjmx_delta mulmxA mulmxACA !mul_delta_mx.
by rewrite !h2mx_comp adj_lfun.unlock delta_lfE !mx2hK.
Qed.

Lemma krausso2choi_psd (F: finType) (f : F -> 'Hom(U,V)) : 
  so2choi (krausso f) \is psdmx.
Proof. by rewrite -krausso2choiE; apply/psdmx_sum=>k _; apply form_psd. Qed.

Lemma krausso_tnE (F: finType) (f : F -> 'Hom(U,V)) :
  krausso f \is tnmap = (trace_nincr f).
Proof.
apply/eqb_iff; split=>[/tnmapP P|/lef_trden P].
apply/lef_trden=>x; move: (P x).
rewrite kraussoE comp_lfun1l; apply: le_trans; rewrite linear_suml/= !linear_sum/=.
by apply ler_sum=>i _; rewrite -!comp_lfunA [X in X <= _]lftraceC comp_lfunA.
apply/tnmapP=>x; move: (P x).
rewrite kraussoE comp_lfun1l; apply: le_trans; rewrite linear_suml/= !linear_sum/=.
by apply ler_sum=>i _; rewrite -!comp_lfunA [X in _ <= X]lftraceC comp_lfunA.
Qed.

Lemma krausso_tpE (F: finType) (f : F -> 'Hom(U,V)) :
  krausso f \is tpmap = (trace_presv f).
Proof.
apply/eqb_iff; split=>[/tpmapP P|/trlf_intror P].
  apply/trlf_intror=>x; move: (P x); rewrite comp_lfun1l kraussoE linear_suml/= !linear_sum/==><-.
  by apply eq_bigr=>i _; rewrite -!comp_lfunA [LHS]lftraceC comp_lfunA.
apply/tpmapP=>x; move: (P x); rewrite comp_lfun1l=><-.
rewrite kraussoE linear_suml/= !linear_sum/=.
by apply eq_bigr=>i _; rewrite -!comp_lfunA [RHS]lftraceC comp_lfunA.
Qed.

Lemma krausso2choiK E : so2choi E \is psdmx ->
  krausso (choi2kraus (so2choi E)) = E.
Proof.
move=>P1. apply/so2choi_inj. move: P1. set M := (so2choi E).
move=>/diag_decomp_absorb P1. rewrite -krausso2choiE [RHS]P1.
apply eq_bigr=>k _. have P0: (1 = 1 * 1)%N by [].
rewrite -[RHS](@castmx_id _ _ _ (erefl _, erefl _))
  -(mcextra.castmx_mul P0)/= adjmx_castV/=.
congr (_ *m _ ^*t); [do 2 f_equal|]; apply/matrix_tenP=>a b c d;
rewrite castmxE !cast_ord_id  summxE choi2kraus.unlock;
set v := (sqrtC (spectral_diag (so2choi E) 0 k) *: row k (spectralmx (so2choi E))).
all: under eq_bigr do rewrite mx2hK tensmxE delta_mx_mulEl/=;
  rewrite (bigD1 a)//= [X in _ + X]big1=>[i /negPf ni|]; 
  first by rewrite mxE [a == i]eq_sym ni mul0r.
all: rewrite !castmxE/= !cast_ord_id summxE (bigD1 a)// big1/==>[i /negPf ni|];
  first by rewrite delta_mx_mulEl ni mul0r.
all: have <-: mxtens_index (0,b) = (cast_ord (esym (mul1n (dim V))) b)
  by apply/ord_inj; rewrite /= mul0n add0n.
all: rewrite delta_mx_mulEl !ord1 [in LHS]mxE !eqxx !mul1r !addr0 [LHS]mxE
  (bigD1 (mxtens_index (a,b)))//= big1; first by move=>i; 
  rewrite -(mxtens_unindexK i) tensmxE (inj_eq (can_inj (@mxtens_indexK _ _)))=>
  /pair_neq/=[P|P]; rewrite !mxE [b == _]eq_sym P/= ?(mul0r, mulr0).
all: by rewrite tensmxE !mxE !eqxx !mul1r addr0.
Qed.

Lemma choimx_preserve_order E F : 
  (so2choi E ⊑ so2choi F) -> (forall x, x \is psdlf -> E x ⊑ F x).
Proof.
rewrite le_lownerE -linearB/= =>/psdmx_form [B PB].
move=>x Px. apply/lef_psdtr=>y Py.
rewrite -subr_ge0 -linearB/= -linearBl/= -opp_soE -add_soE -tr_choi_sep.
have: (h2mx x^T *t h2mx y) \is psdmx.
apply psdmx_tens. rewrite ?h2mx_tr psdmx_tr.
move: Px. 2: move: Py. 1,2: by rewrite qualifE.
by move=>/psdmx_form [A ->]; rewrite PB mulmxA 
  mxtrace_mulC !mulmxA -mulmxA -{2}(adjmxK A) -adjmxM form_tr_ge0.
Qed.

Definition leso_def E F := (so2choi E ⊑ so2choi F).
(* Definition ltso_def E F := (F != E) && (leso_def E F). *)

Lemma leso_def_choimx E F : leso_def E F = (so2choi E ⊑ so2choi F).
Proof. by []. Qed.

(* Lemma ltso_def_choimx E F : ltso_def E F = (so2choi E ⊏ so2choi F).
Proof. by rewrite /ltso_def lt_def (can_eq so2choiK) leso_def_choimx. Qed. *)

(* Lemma ltso_def_def : forall E F, ltso_def E F = (F != E) && (leso_def E F).
Proof. by rewrite /ltso_def. Qed. *)

Lemma ltso_def_anti : antisymmetric leso_def.
Proof. by move=>x y; rewrite !leso_def_choimx -eq_le=>/eqP/so2choi_inj. Qed.

Lemma leso_def_refl : reflexive leso_def.
Proof. by move=>x; rewrite leso_def_choimx. Qed.

Lemma leso_def_trans : transitive leso_def.
Proof. by move=>x y z; rewrite !leso_def_choimx; apply le_trans. Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build ring_display 'SO(U,V)
  leso_def_refl ltso_def_anti leso_def_trans.

Lemma leso_mx E F : E ⊑ F = (so2choi E ⊑ so2choi F).
Proof. by rewrite {1}/Order.le/= leso_def_choimx. Qed.

Lemma ltso_mx E F : E ⊏ F = (so2choi E ⊏ so2choi F).
Proof. by rewrite !lt_def leso_mx (inj_eq so2choi_inj). Qed.

Lemma leso_add2rP (G E F : 'SO(U,V)) : E ⊑ F -> (E + G) ⊑ (F + G).
Proof. 
rewrite addrC !leso_mx -subv_ge0 -[in X in _ -> X]subv_ge0.
by rewrite !linearD/= addrA addrK.
Qed.

Lemma leso_pscale2lP (e : C) E F : 0 < e -> E ⊑ F -> (e *: E) ⊑ (e *: F).
Proof. rewrite !leso_mx !linearZ/=; exact: lev_pscale2lP. Qed.

Lemma pscaleso_lge0 E (a : C) : 
  (0 : 'SO(U,V)) ⊏ E -> (0 : 'SO(U,V)) ⊑ a *: E = (0 <= a).
Proof. rewrite leso_mx ltso_mx linear0 linearZ/=; exact: pscalev_lge0. Qed.

HB.instance Definition _ :=
  POrderedLmodule_isVOrder.Build C 'SO(U,V) leso_add2rP leso_pscale2lP.
HB.instance Definition _ := VOrder_isCan.Build C 'SO(U,V) pscaleso_lge0.

End SOChoiMatrix.

Arguments so2choi {U V}.
Arguments choi2so {U V}.
Arguments cpmap {U V}.
Arguments tnmap {U V}.
Arguments tpmap {U V}.
Arguments cptn {U V}.
Arguments cptp {U V}.
Arguments so2choi_bij {U V}.
Arguments choi2so_bij {U V}. 

Reserved Notation "E '^*o' " (at level 8).

HB.lock Definition dualso (U V : chsType) (E : 'SO(U,V)) :=
  choi2so (mxswap (so2choi E)^T).
Notation "E '^*o' " := (dualso E) : lfun_scope.

Lemma dualsoK (U V : chsType) (E : 'SO(U,V)) : dualso (dualso E) = E.
Proof. by rewrite dualso.unlock choi2soK mxswap_tr mxswapK trmxK so2choiK. Qed.

(* adjoint of super operator *)
Section DualSO.
Variable (U V : chsType).

Lemma dualso_trlfE (E : 'SO(U,V)) (x : 'End(U)) A :
  \Tr (E x \o A) = \Tr (x \o (E^*o A)).
Proof.
rewrite -tr_choi_sep [in RHS]lftraceC -tr_choi_sep dualso.unlock.
rewrite -mxtrace_tr trmx_mul mxtrace_mulC choi2soK trmx_tens !h2mx_tr trmxK.
by rewrite -mxswap_trace -mxswap_mul mxswap_tens.
Qed.

Lemma dualso_trlfEV (E : 'SO(U,V)) (x : 'End(U)) A :
  \Tr (A \o E x) = \Tr ((E^*o A) \o x).
Proof. by rewrite lftraceC dualso_trlfE lftraceC. Qed.

Lemma dualso_krausE (F: finType) (f : F -> 'Hom(U,V)) (A : 'End(V)) :
  dualso (krausso f) A = \sum_i ((f i)^A \o A \o (f i)).
Proof.
apply/eqP/trlf_introl=>x.
rewrite -dualso_trlfE soE linear_sumr linear_suml !linear_sum.
apply eq_bigr =>/= i _.
by rewrite -!comp_lfunA lftraceC !comp_lfunA.
Qed.

Lemma dualso_formE (f : 'Hom(U,V)) (A : 'End(V)) :
  dualso (formso f) A = (f^A \o A \o f).
Proof. by rewrite dualso_krausE big_ord1. Qed.
Definition dualsoE := (dualso_formE, dualso_krausE).

Lemma dualso_krausso (F: finType) (f : F -> 'Hom(U,V)) :
  dualso (krausso f) = krausso (fun i=> (f i)^A).
Proof.
by apply/superopP=>A; rewrite dualsoE soE; under [RHS]eq_bigr do rewrite adjfK.
Qed.
Lemma dualso_formso (f : 'Hom(U,V)) :
  dualso (formso f) = formso (f^A).
Proof. exact: dualso_krausso. Qed.

Lemma dualso_is_linear : linear (@dualso U V).
Proof. by move=>a x y; rewrite dualso.unlock !linearP/=. Qed.
HB.instance Definition _ := GRing.isLinear.Build 
  C 'SO(U,V) 'SO(V,U) *:%R (@dualso U V) dualso_is_linear.

End DualSO.

Lemma dualso_cpE U V (E : 'SO(U,V)) : E ^*o \is cpmap = (E \is cpmap).
Proof.
apply/eqb_iff; split; first rewrite -{2}(dualsoK E).
all: move=>/cpmapP/krausso2choiK<-; rewrite dualso_krausso; 
apply/cpmapP/krausso2choi_psd.
Qed.

Lemma dualso_cpP U V (E : 'SO(U,V)) : E ^*o \is cpmap -> (E \is cpmap).
Proof. by rewrite dualso_cpE. Qed.

(* complete positive maps*)
HB.mixin Record isCPMap (U V : chsType) (f : 'SO(U,V)) :=
  { is_cpmap : f \is cpmap}.

#[short(type="cpType")]
HB.structure Definition CPMap (U V : chsType) := 
  { f of isCPMap U V f}.

Notation "''CP' ( S , T )" := (cpType S T) : type_scope.
Notation "''CP' ( S )" := ('CP(S,S)) : type_scope.
Notation "''CP'" := ('CP(_,_)) (only parsing) : type_scope.
Module CPMapExports.
#[deprecated(since="mathcomp 2.0.0", note="Use CPMap.clone instead.")]
Notation "[ 'CP' 'of' f 'as' g ]" := (CPMap.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use CPMap.clone instead.")]
Notation "[ 'CP' 'of' f ]" := (CPMap.clone _ _ f _) : form_scope.
End CPMapExports.
HB.export CPMapExports.

(* quantum operation - complete positive trace nonincreasing *)
HB.mixin Record CPMap_isTNMap (U V : chsType) f of @CPMap U V f :=
  { is_tnmap : f \is tnmap}.

#[short(type="qoType")]
HB.structure Definition QOperation (U V : chsType) := 
  { f of @CPMap U V f & CPMap_isTNMap U V f}.

Notation cptnType := qoType (only parsing).
Notation "''QO' ( S , T )" := (qoType S T) : type_scope.
Notation "''QO' ( S )" := ('QO(S,S)) : type_scope.
Notation "''QO'" := ('QO(_,_)) (only parsing) : type_scope.
Module QOperationExports.
#[deprecated(since="mathcomp 2.0.0", note="Use QOperation.clone instead.")]
Notation "[ 'QO' 'of' f 'as' g ]" := (QOperation.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use QOperation.clone instead.")]
Notation "[ 'QO' 'of' f ]" := (QOperation.clone _ _ f _) : form_scope.
End QOperationExports.
HB.export QOperationExports.

(* quantum operation - complete positive trace preserving *)
HB.mixin Record QOperation_isTPMap (U V : chsType) f of @QOperation U V f :=
  { is_tpmap : f \is tpmap}.

#[short(type="qcType")]
HB.structure Definition QChannel (U V : chsType) := 
  { f of @QOperation U V f & QOperation_isTPMap U V f}.

Notation cptpType := qcType (only parsing).
Notation "''QC' ( S , T )" := (qcType S T) : type_scope.
Notation "''QC' ( S )" := ('QC(S,S)) : type_scope.
Notation "''QC'" := ('QC(_,_)) (only parsing) : type_scope.
Module QChannelExports.
#[deprecated(since="mathcomp 2.0.0", note="Use QChannel.clone instead.")]
Notation "[ 'QC' 'of' f 'as' g ]" := (QChannel.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use QChannel.clone instead.")]
Notation "[ 'QC' 'of' f ]" := (QChannel.clone _ _ f _) : form_scope.
End QChannelExports.
HB.export QChannelExports.

(* dual of quantum operation, E(I) <= I *)
HB.mixin Record CPMap_isDTNMap (U V : chsType) f of @CPMap U V f :=
  { is_dualtn : f^*o \is tnmap}.

#[short(type="dualqoType")]
HB.structure Definition DualQO (U V : chsType) := 
  { f of @CPMap U V f & CPMap_isDTNMap U V f}.

Notation "''DQO' ( S , T )" := (dualqoType S T) : type_scope.
Notation "''DQO' ( S )" := ('DQO(S,S)) : type_scope.
Notation "''DQO'" := ('DQO(_,_)) (only parsing) : type_scope.
Module DualQOExports.
#[deprecated(since="mathcomp 2.0.0", note="Use DualQO.clone instead.")]
Notation "[ 'DQO' 'of' f 'as' g ]" := (DualQO.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use DualQO.clone instead.")]
Notation "[ 'DQO' 'of' f ]" := (DualQO.clone _ _ f _) : form_scope.
End DualQOExports.
HB.export DualQOExports.

(* unital map - complete positive and unital, i.e., E(I) = I *)
HB.mixin Record DualQO_isUnitalMap (U V : chsType) f of @DualQO U V f :=
  { is_dualtp : f^*o \is tpmap}.

#[short(type="quType")]
HB.structure Definition QUnital (U V : chsType) := 
  { f of @DualQO U V f & DualQO_isUnitalMap U V f}.

Notation "''QU' ( S , T )" := (quType S T) : type_scope.
Notation "''QU' ( S )" := ('QU(S,S)) : type_scope.
Notation "''QU'" := ('QU(_,_)) (only parsing) : type_scope.
Module QUnitalExports.
#[deprecated(since="mathcomp 2.0.0", note="Use QUnital.clone instead.")]
Notation "[ 'QU' 'of' f 'as' g ]" := (QUnital.clone _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use QUnital.clone instead.")]
Notation "[ 'QU' 'of' f ]" := (QUnital.clone _ _ f _) : form_scope.
End QUnitalExports.
HB.export QUnitalExports.

(* factories *)
HB.factory Record isQOperation (U V : chsType) (f : 'SO(U,V)) := {
  is_cptn : f \is cptn;
}.
HB.builders Context U V f of isQOperation U V f.
  HB.instance Definition _ := isCPMap.Build U V f (cptn_cpmap is_cptn).
  HB.instance Definition _ := CPMap_isTNMap.Build U V f (cptn_tnmap is_cptn).
HB.end.

HB.factory Record isQChannel (U V : chsType) (f : 'SO(U,V)) := {
  is_cptp : f \is cptp;
}.
HB.builders Context U V f of isQChannel U V f.
  HB.instance Definition _ := isQOperation.Build U V f (cptp_cptn is_cptp).
  HB.instance Definition _ := QOperation_isTPMap.Build U V f (cptp_tpmap is_cptp).
HB.end.

HB.factory Record isDualQO (U V : chsType) (f : 'SO(U,V)) := {
  is_cptn : f^*o \is cptn;
}.
HB.builders Context U V f of isDualQO U V f.
  HB.instance Definition _ := isCPMap.Build U V f (dualso_cpP (cptn_cpmap is_cptn)).
  HB.instance Definition _ := CPMap_isDTNMap.Build U V f (cptn_tnmap is_cptn).
HB.end.

HB.factory Record isQUnital (U V : chsType) (f : 'SO(U,V)) := {
  is_cptp : f^*o \is cptp;
}.
HB.builders Context U V f of isQUnital U V f.
  HB.instance Definition _ := isDualQO.Build U V f (cptp_cptn is_cptp).
  HB.instance Definition _ := DualQO_isUnitalMap.Build U V f (cptp_tpmap is_cptp).
HB.end.

HB.factory Record CPMap_isQChannel (U V : chsType) f of @CPMap U V f := {
  is_tpmap : f \is tpmap;
}.
HB.builders Context U V f of CPMap_isQChannel U V f.
  HB.instance Definition _ := CPMap_isTNMap.Build U V f (tpmap_tn is_tpmap).
  HB.instance Definition _ := QOperation_isTPMap.Build U V f is_tpmap.
HB.end.

HB.factory Record CPMap_isQUnital (U V : chsType) f of @CPMap U V f := {
  is_dualtp : f^*o \is tpmap;
}.
HB.builders Context U V f of CPMap_isQUnital U V f.
  HB.instance Definition _ := CPMap_isDTNMap.Build U V f (tpmap_tn is_dualtp).
  HB.instance Definition _ := DualQO_isUnitalMap.Build U V f is_dualtp.
HB.end.

Section SOBuild.
Variable (U V : chsType) (f : 'SO(U,V)).

Definition CPMap_Build (H : f \is cpmap) :=
  CPMap.Pack (CPMap.Class (isCPMap.Axioms_ V f H)).
Definition QOperation_Build (H : f \is cptn) :=
  QOperation.Pack (QOperation.Class (CPMap_isTNMap.Axioms_ f 
    (isCPMap.Axioms_ V f (cptn_cpmap H))  (cptn_tnmap H)) ).
Definition QChannel_Build (H : f \is cptp) :=
  QChannel.Pack (QChannel.Class (QOperation_isTPMap.Axioms_ _ (CPMap_isTNMap.Axioms_ f 
  (isCPMap.Axioms_ V f (cptp_cpmap H))  (cptn_tnmap (cptp_cptn H))) (cptp_tpmap H) ) ).
Definition DualQO_Build (H : f^*o \is cptn) :=
  DualQO.Pack (DualQO.Class (CPMap_isDTNMap.Axioms_ f (isCPMap.Axioms_ 
  V f (dualso_cpP (cptn_cpmap H))) (cptn_tnmap H))).
Definition QUnital_Build (H : f^*o \is cptp) :=
  QUnital.Pack (QUnital.Class (DualQO_isUnitalMap.Axioms_ _
  (CPMap_isDTNMap.Axioms_ f (isCPMap.Axioms_ V f (dualso_cpP (cptp_cpmap H)))
  (cptn_tnmap (cptp_cptn H))) (cptp_tpmap H))).

Lemma CPMap_BuildE (cp : f \is cpmap) : f = CPMap_Build cp.
Proof. by []. Qed.
Lemma QOperation_BuildE (qo : f \is cptn) : f = QOperation_Build qo.
Proof. by []. Qed.
Lemma QChannel_BuildE (qc : f \is cptp) : f = QChannel_Build qc.
Proof. by []. Qed.
Lemma DualQO_BuildE (qo : f^*o \is cptn) : f = DualQO_Build qo.
Proof. by []. Qed.
Lemma QUnital_BuildE (qc : f^*o \is cptp) : f = QUnital_Build qc.
Proof. by []. Qed.
End SOBuild.

(* subtype *)
(* we define all types as a subtype of lfun instead of their hierarchy *)
Program Definition cpmap_subType (U V : chsType) := 
  @isSub.Build 'SO(U,V) (fun f => f \is cpmap) (cpType U V) 
  (@CPMap.sort U V) (fun (x : 'SO(U,V)) (H : x \is cpmap) => 
  CPMap_Build H) _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_cpmap _ _ u) (X _ (@is_cpmap _ _ u)).
by case: u=>/= u [[Pu1]] Pu2; rewrite (eq_irrelevance Pu1 Pu2).
Qed.
HB.instance Definition _ (U V : chsType) := @cpmap_subType U V.
HB.instance Definition _ (U V : chsType) := [Equality of (cpType U V) by <:].
HB.instance Definition _ (U V : chsType) := [Choice of (cpType U V) by <:].

Program Definition qoperation_subType (U V : chsType) := 
  @isSub.Build 'SO(U,V) (fun f => f \is cptn) (qoType U V) 
  (@QOperation.sort U V) (fun (x : 'SO(U,V)) (H : x \is cptn) => 
  QOperation_Build H) _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_tnmap _ _ u) (@is_cpmap _ _ u)=>P1 P2.
move: (X _ (cpmap_tnmap_cptn P2 P1)); case: u P1 P2=>/= u [[Pu1]] [Pu2] Pu3 Pu4.
by rewrite /QOperation_Build (eq_irrelevance (cptn_cpmap _) Pu1) 
  (eq_irrelevance (cptn_tnmap _) Pu2).
Qed.
HB.instance Definition _ (U V : chsType) := @qoperation_subType U V.
HB.instance Definition _ (U V : chsType) := [Equality of (qoType U V) by <:].
HB.instance Definition _ (U V : chsType) := [Choice of (qoType U V) by <:].

Program Definition qchannel_subType (U V : chsType) := 
  @isSub.Build 'SO(U,V) (fun f => f \is cptp) (qcType U V) 
  (@QChannel.sort U V) (fun (x : 'SO(U,V)) (H : x \is cptp) => 
  QChannel_Build H) _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_tpmap _ _ u) (@is_cpmap _ _ u)=>P1 P2.
move: (X _ (cpmap_tpmap_cptp P2 P1));
case: u P1 P2=>/= u [[Pu1]] [Pu2] [Pu3] Pu4 Pu5.
by rewrite /QChannel_Build (eq_irrelevance (cptp_cpmap _) Pu1) 
  (eq_irrelevance (cptn_tnmap _) Pu2) (eq_irrelevance (cptp_tpmap _) Pu3).
Qed.
HB.instance Definition _ (U V : chsType) := @qchannel_subType U V.
HB.instance Definition _ (U V : chsType) := [Equality of (qcType U V) by <:].
HB.instance Definition _ (U V : chsType) := [Choice of (qcType U V) by <:].

Program Definition dualqo_subType (U V : chsType) := 
  @isSub.Build 'SO(U,V) (fun f => f^*o \is cptn) (dualqoType U V) 
  (@DualQO.sort U V) (fun (x : 'SO(U,V)) (H : x^*o \is cptn) => 
  DualQO_Build H) _ (fun _ _ => erefl).
Next Obligation.
intros. move: (@is_cpmap _ _ u) (@is_dualtn _ _ u); rewrite -dualso_cpE=>P1 P2.
move: (X _ (cpmap_tnmap_cptn P1 P2)); case: u P1 P2=>/= u [[Pu1]] [Pu2] Pu3 Pu4.
by rewrite /DualQO_Build (eq_irrelevance (dualso_cpP _) Pu1) 
  (eq_irrelevance (cptn_tnmap _) Pu2).
Qed.
HB.instance Definition _ (U V : chsType) := @dualqo_subType U V.
HB.instance Definition _ (U V : chsType) := [Equality of (dualqoType U V) by <:].
HB.instance Definition _ (U V : chsType) := [Choice of (dualqoType U V) by <:].

Program Definition qunital_subType (U V : chsType) := 
  @isSub.Build 'SO(U,V) (fun f => f^*o \is cptp) (quType U V) 
  (@QUnital.sort U V) (fun (x : 'SO(U,V)) (H : x^*o \is cptp) => 
  QUnital_Build H) _ (fun _ _ => erefl).
Next Obligation.
intros; move: (@is_cpmap _ _ u) (@is_dualtp _ _ u); rewrite -dualso_cpE=>P1 P2.
move: (X _ (cpmap_tpmap_cptp P1 P2)); case: u P1 P2=>/= u [[Pu1]] [Pu2] [Pu3] Pu4 Pu5.
by rewrite /QUnital_Build (eq_irrelevance (dualso_cpP  _) Pu1) 
  (eq_irrelevance (cptn_tnmap _) Pu2) (eq_irrelevance (cptp_tpmap _) Pu3).
Qed.
HB.instance Definition _ (U V : chsType) := @qunital_subType U V.
HB.instance Definition _ (U V : chsType) := [Equality of (quType U V) by <:].
HB.instance Definition _ (U V : chsType) := [Choice of (quType U V) by <:].

(* HB.instance Definition _ (U V : chsType) :=
  [SubChoice_isSubPOrder of 'CP(U,V) by <: with ring_display]. *)
HB.instance Definition _ (U V : chsType) :=
  [SubChoice_isSubPOrder of 'QO(U,V) by <: with ring_display].
(* HB.instance Definition _ (U V : chsType) := [SubChoice_isSubPOrder of 'QC(V) by <: with ring_display]. *)

(* we use trace norm *)
Section LfunNorm.
Variable (U V: chsType).

Local Notation F := 'Hom(U,V).
Definition trfnorm (f: F) := \tr| h2mx f |.

Lemma trfnorm0_eq0 (f: F) : trfnorm f = 0 -> f = 0.
Proof. by rewrite /trfnorm=>/trnorm0_eq0 P1; apply/h2mx_inj; rewrite P1 linear0. Qed.

Lemma trfnorm_triangle (f g: F) : trfnorm (f + g) <= trfnorm f + trfnorm g.
Proof. rewrite /trfnorm linearD/=. exact: trnorm_triangle. Qed.

Lemma trfnormZ (a: C) (f: F) : trfnorm (a *: f) = `|a| * trfnorm f.
Proof. rewrite /trfnorm linearZ/=. exact: trnormZ. Qed.

HB.instance Definition _ := isVNorm.Build C F trfnorm
  trfnorm_triangle trfnorm0_eq0 trfnormZ.

Lemma trfnormMn (f: F) n : trfnorm (f *+ n) = trfnorm f *+ n.
Proof. exact: normvMn. Qed.

Lemma trfnormN (f: F) : trfnorm (- f) = trfnorm f.
Proof. exact: normvN. Qed.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build C F 
  trfnorm trfnorm_triangle trfnorm0_eq0 trfnormMn trfnormN.

Lemma trfnormE f : trfnorm f = `|f|. Proof. by []. Qed.

Definition i2fnorm (f: F) := i2norm (h2mx f).

Lemma i2fnorm0_eq0 (f: F) : i2fnorm f = 0 -> f = 0.
Proof. by rewrite /i2fnorm=>/i2norm0_eq0 P1; apply/h2mx_inj; rewrite P1 linear0. Qed.

Lemma i2fnorm_triangle (f g: F) : i2fnorm (f + g) <= i2fnorm f + i2fnorm g.
Proof. rewrite /i2fnorm linearD/=. exact: i2norm_triangle. Qed.

Lemma i2fnormZ (a: C) (f: F) : i2fnorm (a *: f) = `|a| * i2fnorm f.
Proof. rewrite /i2fnorm linearZ/=. exact: i2normZ. Qed.

HB.instance Definition _ := isVNorm.Build C F i2fnorm
  i2fnorm_triangle i2fnorm0_eq0 i2fnormZ.

Lemma i2fnorm_trfnorm (f : F) : i2fnorm f <= `|f|.
Proof. exact: i2norm_trnorm. Qed.

Lemma i2fnormP (f : 'Hom(U,V)) u :
  `| f u | <= i2fnorm f * `| u |.
Proof. by rewrite !hnorm_l2norm applyfh c2hK -!fbnorm_l2norm /i2fnorm fbnormMr. Qed.

End LfunNorm.

Section LfunNormExtra.
Implicit Type (U V W : chsType).

Lemma i2fnorm_adj U V (f : 'Hom(U,V)) :
  i2fnorm f^A = i2fnorm f.
Proof. by rewrite /i2fnorm adj_lfun.unlock mx2hK i2norm_adjmx. Qed.

Lemma i2fnorm_conj U V (f : 'Hom(U,V)) :
  i2fnorm f^C = i2fnorm f.
Proof. by rewrite /i2fnorm conj_lfun.unlock mx2hK i2norm_conjmx. Qed.

Lemma i2fnorm_tr U V (f : 'Hom(U,V)) :
  i2fnorm f^T = i2fnorm f.
Proof. by rewrite /i2fnorm tr_lfun.unlock mx2hK i2norm_trmx. Qed.

Lemma i2fnormM U V W (f : 'Hom(U,V)) (g : 'Hom(W,U)) :
  i2fnorm (f \o g) <= i2fnorm f * i2fnorm g.
Proof. by rewrite /i2fnorm h2mx_comp i2normM. Qed.

Lemma i2fnormUl U V W  (f : 'Hom(U,V)) (u : 'FGI(V,W)) :
  i2fnorm (u \o f) = i2fnorm f.
Proof.
rewrite /i2fnorm h2mx_comp i2normUl_cond//.
by move: (is_gisolf u); rewrite qualifE=>/andP[].
Qed.

Lemma i2fnormUr U V W  (f : 'Hom(U,V)) (u : 'FGI(W,U)) :
  i2fnorm (f \o u) = i2fnorm f.
Proof.
rewrite /i2fnorm h2mx_comp i2normUr//.
by move: (is_gisolf u); rewrite qualifE=>/andP[].
Qed.

Lemma bound1lf_i2fnormE U V  (f : 'Hom(U,V)) :
  f \is bound1lf = (i2fnorm f <= 1).
Proof. by rewrite bound1lf_i2normE. Qed.

Lemma bound1f_i2fnorm U V  (f : 'FB1(U,V)) :
  i2fnorm f <= 1.
Proof. by rewrite -bound1lf_i2fnormE is_bound1lf. Qed.

Lemma i2fnorm_iso U V  (f : 'Hom(U,V)) :
  f \is isolf -> i2fnorm f = 1.
Proof. 
rewrite qualifE /i2fnorm -i2norm_adjmx=>Pf.
by rewrite i2norm_unitary// ?gtn_eqF// dim_proper.
Qed.

Lemma i2fnorm_isof U V  (f : 'FI(U,V)) : i2fnorm f = 1.
Proof. apply/i2fnorm_iso/is_isolf. Qed.

Lemma isofEr_le1 U V  (f : 'FI(U,V)) : f \o f^A <= \1.
Proof.
apply/lef_dot=>u; rewrite !lfunE/= -adj_dotEl !dotp_norm lerXn2r ?nnegrE//.
by apply: (le_trans (i2fnormP _ _)); rewrite i2fnorm_adj i2fnorm_isof mul1r.
Qed.

(* TODO : generalize *)
Lemma isof_dot U V  (f : 'FI(U,V)) u : 
  [< f u; f u >] = [< u; u >].
Proof. by apply/isolf_dotP/is_isolf. Qed.

Lemma isofA_dot U V  (f : 'FI(U,V)) u : 
  [< f^A u; f^A u >] <= [< u; u >].
Proof. by move: (isofEr_le1 f)=>/lef_dot/(_ u); rewrite !lfunE/= -adj_dotEl. Qed.

Lemma gisofA_dot U V  (f : 'FGI(U,V)) u : 
  [< f^A u; f^A u >] = [< u; u >].
Proof. exact: isof_dot. Qed.

Lemma trfnorm_adj U V (f : 'Hom(U,V)) :
  `| f^A | = `| f |.
Proof. by rewrite /Num.norm/= /trfnorm adj_lfun.unlock mx2hK trnorm_adjmx. Qed.

Lemma trfnorm_conj U V (f : 'Hom(U,V)) :
  `| f^C | = `| f |.
Proof. by rewrite /Num.norm/= /trfnorm conj_lfun.unlock mx2hK trnorm_conjmx. Qed.

Lemma trfnorm_tr U V (f : 'Hom(U,V)) :
  `| (f^T)%VF | = `| f |.
Proof. by rewrite /Num.norm/= /trfnorm tr_lfun.unlock mx2hK trnorm_trmx. Qed.

Lemma trfnormMl U V W  (f : 'Hom(U,V)) (g : 'Hom(W,U)) : 
  `|f \o g| <= `|f| * i2fnorm g.
Proof. rewrite/Num.norm/=/trfnorm/=h2mx_comp; exact: trnormMl. Qed.

Lemma trfnormMr U V W  (f : 'Hom(U,V)) (g : 'Hom(W,U)) : 
  `|f \o g| <= i2fnorm f * `|g|.
Proof. rewrite/Num.norm/=/trfnorm/=h2mx_comp; exact: trnormMr. Qed.

Lemma trfnormM U V W  (f : 'Hom(U,V)) (g : 'Hom(W,U)) : 
  `|f \o g| <= `|f| * `|g|.
Proof. apply/(le_trans (trfnormMl _ _))/ler_wpM2l=>//; apply/i2norm_trnorm. Qed.

Lemma trfnormUl U V W  (f : 'Hom(U,V)) (u : 'FGI(V,W)) :
  `| (u \o f) | = `| f |.
Proof.
rewrite /Num.norm/= /trfnorm h2mx_comp schnormUl_cond//.
by move: (is_gisolf u); rewrite qualifE=>/andP[].
Qed.

Lemma trfnormUr U V W  (f : 'Hom(U,V)) (u : 'FGI(W,U)) :
  `| (f \o u) | = `| f |.
Proof.
rewrite /Num.norm/= /trfnorm h2mx_comp schnormUr//.
by move: (is_gisolf u); rewrite qualifE=>/andP[].
Qed.

Lemma trfnormP U V  (f : 'Hom(U,V)) x :
  `|f x| <= `| f | * `|x|.
Proof.
rewrite !hnorm_l2norm applyfh c2hK -!fbnorm_l2norm.
apply: (le_trans (fbnormMr _ _)). 
rewrite ler_wpM2r// ?fbnorm_ge0//; exact: i2fnorm_trfnorm.
Qed.

Lemma i2fnorm_unitary U  (f : 'End(U)) : 
  f \is unitarylf -> i2fnorm f = 1.
Proof. exact: i2fnorm_iso. Qed.

Lemma i2fnorm1 U  : i2fnorm (\1 : 'End(U)) = 1.
Proof. apply: i2fnorm_isof. Qed.

Lemma trfnorm_iso U V  (f : 'Hom(U,V)) : 
  f \is isolf -> `| f | = (dim U)%:R.
Proof.
move=>Pf; move: (isolf_le_dim Pf) => /minn_idPl P1.
move: Pf; rewrite qualifE -trfnorm_adj /Num.norm/= 
  /trfnorm adj_lfun.unlock mx2hK schnorm.unlock.
move=>/svd_d_unitary->; rewrite l1normE big_ord1.
under eq_bigr do rewrite mxE normr1.
by rewrite sumr_const !card_ord P1.
Qed.

Lemma trfnorm_isof U V  (f : 'FI(U,V)) : 
  `| f%:VF | = (dim U)%:R.
Proof. by apply/trfnorm_iso/is_isolf. Qed.

Lemma trfnorm_gisof U V  (f : 'FGI(U,V)) : 
  `| f%:VF | = (dim V)%:R.
Proof. by rewrite -trfnorm_adj; apply/trfnorm_iso/is_isolf. Qed.

Lemma trfnorm_unitary U  (f : 'End(U)) : 
  f \is unitarylf -> `| f | = (dim U)%:R.
Proof. exact: trfnorm_iso. Qed.

Lemma trfnorm_unitaryf U  (f : 'FU(U)) : `|f%:VF| = (dim U)%:R.
Proof. exact: trfnorm_isof. Qed.

Lemma trfnorm1 U  : `| \1 : 'End(U) | = (dim U)%:R.
Proof. apply: trfnorm_isof. Qed.

End LfunNormExtra.

Section LfunNormExtra.
Variable (U : chsType).

Lemma trlf_trfnorm (f : 'End(U)) : `|\Tr f| <= `|f|.
Proof. by rewrite/lftrace/Num.norm/=/trfnorm; exact: trnorm_ge_tr. Qed.

Lemma psd_trfnorm (f: 'End(U)) : 
  f \is psdlf -> `|f| = \Tr f.
Proof. by rewrite qualifE /Num.norm/=/trfnorm/lftrace; apply: psdmx_trnorm. Qed.

Lemma trfnorm_psd (f : 'F+(U)) : `|f%:VF| = \Tr f.
Proof. by apply/psd_trfnorm/is_psdlf. Qed.

Lemma outp_norm (u : U) : `|[> u ; u <]| = `|u|^+2.
Proof. by rewrite trfnorm_psd/= outp_trlf dotp_norm. Qed.

Lemma outp_ns_norm (u : 'NS(U)) : `|[> u ; u <]| = 1.
Proof. by rewrite outp_norm ns_norm expr1n. Qed.

Definition chs_default_vect : U := eb (cast_ord dim_proper_cast ord0).

Definition trfnorm_set (f : 'End(U)) : set C := [set x | exists g : 'End(U), i2fnorm g = 1 /\ `|\Tr (f \o g) | = x].

Lemma trfnorm_set_has_sup f : has_sup (trfnorm_set f).
Proof. split.
exists (`|\Tr (f \o \1) |).
by exists \1; split=>//; rewrite i2fnorm1 .
exists `|f|=>?[x [Px <-]]; apply/(le_trans (trlf_trfnorm _))/(le_trans (trfnormMl _ _)).
by rewrite Px mulr1.
Qed.

Lemma trfnorm_csup (f : 'End(U)) : `|f| = csup (trfnorm_set f).
Proof.
apply/le_anti/andP; split.
apply/(csup_upper_bound (trfnorm_set_has_sup _)).
move: (svdsE (h2mx f))=>Pf.
exists (mx2h ((svd_v (h2mx f)) *m (svd_u (h2mx f))^*t)); split.
apply: i2fnorm_unitary; rewrite qualifE mx2hK trmxC_unitary; apply/mul_unitarymx;
by rewrite ?trmxC_unitary svd_pE.
rewrite/lftrace{2}/Num.norm/=/trfnorm h2mx_comp mx2hK {1 4}Pf.
rewrite trnormUr; first by rewrite trmxC_unitary svd_pE.
rewrite trnormUl ?svd_pE// mulmxA mulmxKtV// ?svd_pE//.
rewrite -mulmxA mxtrace_mulC mulmxKtV// ?svd_pE//.
rewrite psdmx_trnorm ?ger0_norm//.
apply/diagmx_nnegmx_psd/svd_diag_nneg/svds_d_svd_diag.
by rewrite mxtrace_diag sumr_ge0//==>i _; apply/svd_diag_ge0/svds_d_svd_diag.
apply/(csup_least_ubound (trfnorm_set_has_sup _))=>e[x [Px <-]].
by apply/(le_trans (trlf_trfnorm _))/(le_trans (trfnormMl _ _)); rewrite Px mulr1.
Qed.

Lemma trfnorm_add (f g : 'End(U)) : 0%:VF ⊑ f -> 0%:VF ⊑ g ->
  `|f + g| = `|f| + `|g|.
Proof.
move=>P1 P2; rewrite !psd_trfnorm ?psdlfE ?linearD=>[|||//].
rewrite -(addr0 0) levD=>[||//].
1,3: apply/P1. all: apply/P2.
Qed.

Lemma trfnorm_ler (f g : 'End(U)) : 0%:VF ⊑ f -> f ⊑ g -> `|f| <= `|g|.
Proof. by move=>P1 P2; rewrite -[g](addrNK f) trfnorm_add ?subv_ge0// lerDr. Qed.

End LfunNormExtra.

Arguments chs_default_vect {U}.

Section SOTraceNorm.
Variable (U V: chsType).

(* arbitrary norm, just used for normed space *)
Local Notation F := 'SO(U,V).
Definition trsfnorm (f: F) := \tr| f2mx (so_val f) |.

Lemma trsfnorm0_eq0 (f: F) : trsfnorm f = 0 -> f = 0.
Proof. by move/trnorm0_eq0=>P1; apply/val_inj/f2mx_inj; rewrite P1/= soK linear0. Qed.

Lemma trsfnorm_triangle (f g: F) : trsfnorm (f + g) <= trsfnorm f + trsfnorm g.
Proof. by rewrite /trsfnorm soK !linearD/=; exact: trnorm_triangle. Qed.

Lemma trsfnormZ (a: C) (f: F) : trsfnorm (a *: f) = `|a| * trsfnorm f.
Proof. by rewrite /trsfnorm soK !linearZ/=; exact: trnormZ. Qed.

HB.instance Definition _ := isVNorm.Build C F trsfnorm
  trsfnorm_triangle trsfnorm0_eq0 trsfnormZ.

Lemma trsfnormMn (f: F) n : trsfnorm (f *+ n) = trsfnorm f *+ n.
Proof. exact: normvMn. Qed.

Lemma trsfnormN (f: F) : trsfnorm (- f) = trsfnorm f.
Proof. exact: normvN. Qed.

Lemma trnorm_map m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q)) :
  linear f -> bijective f -> exists c : C, c > 0 /\ (forall x, \tr| f x | <= c * \tr| x |).
Proof.
move=>lf [g fK gK]; move: (linearlfE lf)=>Pf; set Lf := GRing.Linear.Pack _ in Pf.
move: (@can2_linear _ _ _ Lf)=>/=/(_ g fK gK) lg.
pose mn x := \tr| f x |.
have meq0 : forall x, mn x = 0 -> x = 0.
  by move=>x/normv0_eq0; rewrite -{2}(fK x)/==>->; rewrite (linearlfE lg) linear0.
have mtrg : forall x y, mn (x + y) <= mn x + mn y.
  by move=>x y; rewrite /mn (linearlfE lf) linearD lev_normD.
have mZ : forall (a: C) (x : 'M_(m,n)), mn (a *: x) = `|a| * mn x.
  by move=>a x; rewrite /mn (linearlfE lf) linearZ normvZ.
pose mvn := VNorm.Pack (VNorm.Class (isVNorm.Build C 'M[C]_(m,n) mn mtrg meq0 mZ)).
move: (cmnorm_bounded mvn (@trnorm _ _))=>[c /= cgt0 Pml].
exists c=>//.
Qed.

Lemma sobounded_apply_trsfnorm :
  exists c, (c > 0 /\ forall (f : 'SO(U,V)) x, `|f x| <= c * (trsfnorm f) * `|x|).
Proof.
rewrite /normr/= /trfnorm /trsfnorm.
set f1 := (h2mx \o @r2v _ 'End(V))%FUN.
have lf1 : linear f1 by move=>a b c; rewrite /f1 linearP.
have bf1 : bijective f1.
by exists (@v2r _ 'End(V) \o mx2h)%FUN;
move=>x/=; rewrite /f1/= ?h2mxK ?r2vK// v2rK mx2hK.
move: (trnorm_map lf1 bf1)=>[c1 [c1gt0 Pc1]].
set f2 := (@v2r _ 'End(U) \o mx2h)%FUN.
have lf2 : linear f2 by move=>a b c; rewrite /f2 linearP.
have bf2 : bijective f2.
by exists (h2mx \o @r2v _ 'End(U))%FUN;
move=>x/=; rewrite /f2/= ?v2rK ?mx2hK// h2mxK r2vK.
move: (trnorm_map lf2 bf2)=>[c2 [c2gt0 Pc2]].
have c12gt0 : (c1 * c2 > 0) by apply mulr_gt0.
exists (c1 * c2); split=>// f x.
rewrite /fun_of_superof [in so_val f x]unlock/=.
apply: (le_trans (Pc1 _)). rewrite -!mulrA ler_pM2l// -trnorm_adjmx adjmxM.
apply: (le_trans (trnormMl _ _)).
rewrite trnorm_adjmx i2norm_adjmx [X in _ <= X]mulrC -mulrA.
apply ler_wpM2l. apply/trnorm_ge0. apply: (le_trans (i2norm_trnorm _)).
by move: (Pc2 (h2mx x)); rewrite /f2/= h2mxK mulrC.
Qed.

End SOTraceNorm.

Lemma divf_ave_le_max2 (T : numFieldType) (a1 a2 b1 b2 : T) :
  a1 \is Num.real -> a2 \is Num.real ->
  0 < b1 -> 0 < b2 ->
    (a1 + a2) / (b1 + b2) <= maxr (a1/b1) (a2/b2).
Proof.
move=>Pa1 Pa2 Pb1 Pb2.
have: b1 * a2 >=< b2 * a1.
by rewrite comparablerE realB// realM// gtr0_real.
rewrite comparable_le_max; 
  first by rewrite comparablerE realB// realM// realV gtr0_real.
move=>/orP[] P; apply/orP. left. 2: right.
all: rewrite ler_pdivrMr ?addr_gt0// -mulrA mulrC 
  -mulrA ler_pdivlMl// mulrDr mulrDl ?lerD2r ?lerD2l//.
Qed.

Lemma divf_ave_le_max (T : numFieldType) (I : eqType) (r : seq I)
                      (P : pred I) (F G : I -> T) :
  (forall i, P i -> F i \is Num.real) -> (forall i, P i -> G i > 0) ->
    (\sum_(i <- r | P i) F i) / (\sum_(i <- r | P i) G i) 
      <= \big[maxr/0]_(i <- r | P i) (F i / G i).
Proof.
move=>P1 P2; elim: r=>[|a l IH]; first by rewrite !big_nil.
rewrite !big_cons; case E: (P a)=>//.
case PE: (0 < \sum_(j <- l | P j) G j).
apply: (le_trans (divf_ave_le_max2 _ _ _ _))=>//.
by apply/P1. by apply/sum_real=>i; apply: P1. by apply/P2. by apply/ler_max2l.
have: (0 <= \sum_(j <- l | P j) G j) by apply sumr_ge0=>i /P2/ltW.
rewrite le_eqVlt PE orbF eq_sym=>/eqP P3.
have ->: \sum_(j <- l | P j) F j = 0.
move: P3; clear -P2; elim: l=>[|a l IH]; first by rewrite !big_nil.
rewrite !big_cons; case E: (P a)=>// /eqP; rewrite addrC addr_eq0=>/eqP P1.
have P3: G a <= 0 by rewrite -oppr_ge0 -P1; apply sumr_ge0=>i/P2/ltW.
by move: (lt_le_trans (P2 _ E) P3); rewrite ltxx.
rewrite P3 !addr0 comparable_le_max ?lexx//; apply/real_comparable.
2: apply/bigmax_real=>// b Pb.
all: rewrite realM// ?realV. 
1,3: by apply/P1. all: by apply/gtr0_real/P2.
Qed.

(* https://arxiv.org/pdf/quant-ph/0411077.pdf *)
(* Remark: currently we only use it for CP map, so we choice induced trace norm *)
(* Note that, `|Phi| = `|Phi|^H = `|Phi|_diamond for CP map Phi *)
(* so we can change it to `|Phi|^H or `|Phi|_diamond *)
Section InducedTraceNorm.
Variable (U V : chsType).
Implicit Type (f g : 'SO(U,V)).

Definition itnorm_set f : set C := 
    [set x : C | exists y, `|y| = 1 /\ x = `|f y|].
Definition itnorm_set_ns f : set C :=
    [set x : C | exists v : U, `|v| = 1 /\ x = `|f [> v ; v <]|].
Definition itnorm_set_psd f : set C :=
    [set x : C | exists y : 'End(U), y \is psdlf /\ `|y| = 1 /\ x = `|f y|].

Let u1 : U := eb (cast_ord dim_proper_cast ord0).
#[local] Lemma u1_norm : `| [> u1; u1 <] | = 1.
Proof. by rewrite outp_norm ns_norm expr1n. Qed.
Local Hint Resolve u1_norm : core.
#[local] Lemma u1_psd : [> u1; u1 <] \is psdlf.
Proof. apply: outp_psd. Qed.
Local Hint Resolve u1_psd : core.

Lemma itnorm_set_has_sup f : has_sup (itnorm_set f).
Proof.
split. exists (`|f  [> u1; u1 <] |).
rewrite/itnorm_set/=; exists [> u1; u1 <]; do ! split=>//.
move: (sobounded_apply_trsfnorm U V)=>[c [cgt0 /(_ f) Pc]].
exists (c * trsfnorm f)=>e; rewrite/itnorm_set/==>[[x []Px ->]].
by apply: (le_trans (Pc x)); rewrite Px mulr1.
Qed.

Lemma itnorm_set_psd_sub_itnorm_set f : 
  (itnorm_set_psd f `<=` itnorm_set f)%classic.
Proof. by move=>x[v [_ [Pv ->]]]; exists v; split. Qed.

Lemma itnorm_set_ns_sub_itnorm_set_psd f : 
  (itnorm_set_ns f `<=` itnorm_set_psd f)%classic.
Proof.
move=>x[v [Pv ->]]; exists [> v ; v <]; split; first by apply/is_psdlf.
by rewrite outp_norm Pv expr1n.
Qed.

Lemma itnorm_set_ns_has_sup f : has_sup (itnorm_set_ns f).
Proof.
split; last first.
move: (itnorm_set_has_sup f)=>[] _ [e Pe]; exists e=>x Px; 
by apply/Pe/itnorm_set_psd_sub_itnorm_set/itnorm_set_ns_sub_itnorm_set_psd.
exists (`|f [> chs_default_vect ; chs_default_vect <]|).
by exists chs_default_vect; rewrite ns_norm.
Qed.

Lemma itnorm_set_psd_has_sup f : has_sup (itnorm_set_psd f).
Proof.
split; last first.
move: (itnorm_set_has_sup f)=>[] _ [e Pe]; exists e=>x Px; 
by apply/Pe/itnorm_set_psd_sub_itnorm_set.
apply: (subset_nonempty (@itnorm_set_ns_sub_itnorm_set_psd f)).
by move: (itnorm_set_ns_has_sup f)=>[].
Qed.

Definition itnorm f := csup (itnorm_set f).

#[local] Lemma itnormPB f (x : 'End(U)) : `|f x| <= itnorm f * `|x|.
Proof.
case E: (x == 0); first by move: E=>/eqP->; rewrite !linear0 !normr0 mulr0.
move: E=>/eqP/eqP Py; rewrite mulrC -ler_pdivrMl ?normr_gt0// mulrC.
apply: (csup_upper_bound (itnorm_set_has_sup f)); exists (`|x|^-1 *: x); split;
by rewrite /normr/= ?normvZV// linearZ/= normvZ/=
  ger0_norm ?invr_ge0 ?normv_ge0// mulrC.
Qed.

#[local] Lemma itnorm0 : itnorm 0 = 0.
Proof.
apply/le_anti/andP; split.
apply: (csup_least_ubound (itnorm_set_has_sup _))=>x[]/= y[] _ ->.
by rewrite soE normr0.
apply: (csup_upper_bound (itnorm_set_has_sup _)).
by exists [> u1; u1 <]; rewrite soE normr0 u1_norm.
Qed.

Lemma itnorm0_eq0 f : itnorm f = 0 -> f = 0.
Proof.
move=>Pf; apply/superopP=>/=y; rewrite soE.
by move: (itnormPB f y); rewrite Pf mul0r normr_le0=>/eqP.
Qed.

Lemma itnorm_triangle f g : itnorm (f + g) <= itnorm f + itnorm g.
Proof.
apply: (csup_least_ubound (itnorm_set_has_sup _))=>x[]/= y[]Py ->.
rewrite soE; apply/(le_trans (ler_normD _ _))/lerD; 
by apply/(le_trans (@itnormPB _ _)); rewrite Py mulr1.
Qed.

Lemma itnormZ (a: C) f : itnorm (a *: f) = `|a| * itnorm f.
Proof.
apply/le_anti/andP; split.
apply: (csup_least_ubound (itnorm_set_has_sup _))=>x[]/= y[]Py ->.
rewrite soE {1}/Num.norm/= trfnormZ ler_wpM2l// -[itnorm f]mulr1 -Py;
apply/itnormPB.
case E: (a == 0); first by move: E=>/eqP->;
rewrite scale0r itnorm0 normr0 mul0r.
move: E=>/eqP/eqP=>E; rewrite -ler_pdivlMl ?normr_gt0//.
apply: (csup_least_ubound (itnorm_set_has_sup _))=>x[]/= y[]Py ->.
rewrite ler_pdivlMl ?normr_gt0//.
apply: (csup_upper_bound (itnorm_set_has_sup _)).
by exists y; split=>//; rewrite soE /normr/= normvZ/=.
Qed.

HB.instance Definition _ := isVNorm.Build C 'SO(U,V) 
  itnorm itnorm_triangle itnorm0_eq0 itnormZ.

Lemma itnormMn f n : itnorm (f *+ n) = itnorm f *+ n.
Proof. exact: normvMn. Qed.

Lemma itnormN f : itnorm (- f) = itnorm f.
Proof. exact: normvN. Qed.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build C 'SO(U,V) 
  itnorm itnorm_triangle itnorm0_eq0 itnormMn itnormN.

Lemma itnormE f : itnorm f = `|f|. Proof. by []. Qed.

Lemma itnormP f x : `|f x| <= `|f| * `|x|. Proof. exact: itnormPB. Qed.
Lemma itnormPD f x : `|f x| / `|x| <= `|f|.
Proof.
case E: (x == 0); first by move: E=>/eqP->; rewrite normr0 invr0 mulr0.
rewrite ler_pdivrMr ?normr_gt0 ?E//; exact: itnormP.
Qed.

Lemma itnorm_ler f (e : C) : (forall x, `|f x| <= e * `|x|) -> `|f| <= e.
Proof.
move=>P1; apply: (csup_least_ubound (itnorm_set_has_sup _))=>?[]/= y[]Py ->.
by rewrite -[e]mulr1 -Py; apply/P1.
Qed.

Lemma itnorm_ger f (e : C) :
  (exists x, x != 0 /\ `|f x| = e * `|x|) -> e <= `|f|.
Proof.
move=>[x [Px1 Px2]]; apply: (csup_upper_bound (itnorm_set_has_sup _)).
exists (`|x|^-1 *: x); split; rewrite /normr/=; first by rewrite normvZV.
move: Px2; rewrite linearZ/= normvZ/= ger0_norm ?invr_ge0 ?normv_ge0// /normr/==>->.
by rewrite mulrC mulfK// normv_eq0.
Qed.

Lemma itnorm_def f (e : C) : 
  (forall x, `|f x| <= e * `|x|) -> (exists x, x != 0 /\ `|f x| = e * `|x|) 
    -> `|f| = e.
Proof. by move=>??; apply/le_anti/andP; split; [apply: itnorm_ler|apply: itnorm_ger]. Qed.

Lemma trfnorm_existsr (W T: chsType) (A : 'Hom(W,T)) : exists2 B : 'Hom(T,W), 
  i2fnorm B = 1 & `|A| = `|\Tr(A \o B) |.
Proof.
clear. 
move: (trnorm_exists (castmx (esym dim_proper_cast, esym dim_proper_cast) (h2mx A)))=>[B0].
pose B1 := (castmx (dim_proper_cast, dim_proper_cast) B0).
have ->: B0 = (castmx (esym dim_proper_cast, esym dim_proper_cast) B1). 
  by rewrite/B1 castmx_comp castmx_id.
move: B1=>B1; rewrite castmx_mul !castmx_funE/==>PB1 PB2.
exists (mx2h B1); first by rewrite /i2fnorm mx2hK.
by rewrite/lftrace h2mx_comp mx2hK mxtrace_mulC PB2.
Qed.

Lemma trfnorm_lbound (W T: chsType) (A : 'Hom(W,T)) (B : 'Hom(T,W)) : 
  i2fnorm B = 1 -> `|\Tr(A \o B) | <= `|A|.
Proof.
rewrite /i2fnorm /lftrace h2mx_comp {2}/normr/= /trfnorm=>PB.
by apply/(le_trans (trnormM_gel _ _)); rewrite PB mulr1.
Qed.

Lemma mulmx_diag_colrow (T : comRingType) m n p 
  (A : 'M[T]_(m,n)) (B : 'M[T]_(n,p)) (D : 'rV_n) :
    A *m diag_mx D *m B = \sum_i D 0 i *: (col i A *m row i B).
Proof.
clear; rewrite -mulmxA mulmx_colrow.
by apply eq_bigr => i _; rewrite row_diag_mul linearZr.
Qed.

Lemma cpmap_csup_psdE f : (f \is cpmap) -> `| f | = csup (itnorm_set_psd f).
Proof.
move=>Pf; rewrite /normr/=/itnorm.
apply/le_anti/andP; split; last first.
  move: (csup_least_ubound (itnorm_set_psd_has_sup f))
    =>/(_ (csup (itnorm_set f)))->//= i Pi.
  move: (csup_upper_bound (itnorm_set_has_sup f))=>/(_ i)->//=.
  move: Pi; rewrite/itnorm_set_psd/=/itnorm_set/==>[[y [Py1 []Py2 Py3]]].
  by exists y; split.
move: (csup_least_ubound (itnorm_set_has_sup f))
  =>/(_ (csup (itnorm_set_psd f)))->//= i.
rewrite /itnorm_set/==>[[y [Py1 Py2]]].
move: (trfnorm_existsr (f y))=>[x Px1 Px2].
move: {+}Pf=>/cpmapP/krausso2choiK; set A := (choi2kraus (so2choi f)) => PA.
pose my := h2mx y. set mx := h2mx x in Px1. pose mA := (fun i => h2mx (A i)).
pose yl := (svd_u my *m diag_mx (svds_d my) *m (svd_u my)^*t).
pose yr := (svd_v my *m diag_mx (svds_d my) *m (svd_v my)^*t).
pose xl := (svd_u mx *m diag_mx (svds_d mx) *m (svd_u mx)^*t).
pose xr := (svd_v mx *m diag_mx (svds_d mx) *m (svd_v mx)^*t).
have mAE k : h2mx (A k) = mA k by [].
have: `|f y|^+2 <= `|\Tr (f (mx2h yl) \o (mx2h xr)) | * `|\Tr (f (mx2h yr) \o (mx2h xl)) |.
  rewrite Px2 /lftrace -PA !kraussoE !linear_suml !linear_sum/=.
  under eq_bigr do rewrite !h2mx_comp h2mx_adj [h2mx y]svdsE [h2mx x]svdsE -/mx -/my mAE.
  (* mulmx_diag_colrow mulmx_diag_colrow !(linear_sumr, linear_sum)/=. *)
  under [in X in _ <= X * _]eq_bigr do
    rewrite !h2mx_comp mx2hK mx2hK h2mx_adj mAE /yl /xr.
  under [in X in _ <= _ * X]eq_bigr do
    rewrite !h2mx_comp mx2hK mx2hK h2mx_adj mAE /yr /xl.
  have RE1 m n B (Uy Vy : 'M[C]_m) Y (Ux Vx : 'M[C]_n) X :
    \tr (B *m (Uy *m diag_mx (svds_d Y) *m Vy^*t) *m 
    B^*t *m (Ux *m diag_mx (svds_d X) *m Vx^*t)) = \sum_k 
    (sqrtC ((svds_d X) 0 k.1 * (svds_d Y) 0 k.2) * (row k.1 Vx^*t *m B *m col k.2 Uy) 0 0) *
    (sqrtC ((svds_d X) 0 k.1 * (svds_d Y) 0 k.2) * (row k.1 Ux^*t *m B *m col k.2 Vy) 0 0)^*.
      rewrite !mulmx_diag_colrow !linear_sumr/= linear_sum;
      under eq_bigr do rewrite !linear_suml/= linear_sum/=.
      rewrite pair_big/=; apply eq_bigr =>k _.
      rewrite linearZ/= linearZr/= linearZ/= 2!linearZl_LR/= linearZ/= mulrA !mulmxA 
        mxtrace_mulC !mulmxA -mulmxA -mulmxA [X in _ *m X]mulmxA trace_mx11 mxE big_ord1.
      rewrite conjcM !mulrA. f_equal.
      rewrite [RHS]mulrC mulrA; f_equal.
      rewrite -normCKC ger0_norm ?sqrtCK// sqrtC_ge0 mulr_ge0//;
      apply/svd_diag_ge0/svds_d_svd_diag.
      by rewrite -mxE_adj !adjmxM adj_row adj_col adjmxK mulmxA.
  time under eq_bigr do rewrite RE1. rewrite pair_big.
  apply: (le_trans (Cauchy_Schwarz_C _ _ _ _)).
  have Pe (a b : C) : a = b -> a <= b by move=>->.
  apply/Pe; f_equal; under [in RHS]eq_bigr do rewrite RE1; rewrite pair_big ger0_norm.
  1,3: apply sumr_ge0=>k _; rewrite mulrC -normCKC exprn_ge0//.
  by apply eq_bigr=>k _; rewrite normCKC mulrC.
  by apply eq_bigr=>k _; rewrite normCKC conjCK.
move=>P; rewrite -(@ler_pXn2r _ 2)// ?nnegrE ?Py2//.
  apply: (le_trans (y := `|f [> u1; u1 <]|))=>//.
  apply: (csup_upper_bound (itnorm_set_psd_has_sup f)).
  by exists [> u1; u1 <]; do ! split.
apply/(le_trans P); rewrite expr2 ler_pM//; 
  (apply: (le_trans (trfnorm_lbound _ _)); 
    first by rewrite /i2fnorm mx2hK /xr/xl i2normUr// i2normUl// -i2norm_svds);
  apply: (csup_upper_bound (itnorm_set_psd_has_sup f)); 
  [exists (mx2h yl) | exists (mx2h yr)]; 
  (do ! split; first by rewrite qualifE mx2hK /yr; 
    apply/nneg_form/svd_diag_nneg/svds_d_svd_diag);
  by rewrite /yl/yr/normr/=/trfnorm mx2hK 
    trnormUr ?trnormUl -?trnorm_svds ?trmxC_unitary ?svd_pE.
Qed.

Lemma unitary_rowMcol (T : numClosedFieldType) m (u : 'M[T]_m) i :
  u \is unitarymx -> (row i u^*t *m col i u) 0 0 = 1.
Proof.
by move=>/unitarymxPV/matrixP/(_ i i); rewrite -{2}[u]adjmxK dot_dotmxE 
  dotmxE -adjmxE adj_row adjmxK=>->; rewrite mxE eqxx.
Qed.

Lemma cpmap_csup_nsE f : (f \is cpmap) -> `| f | = csup (itnorm_set_ns f).
Proof.
move=>Pf; rewrite (cpmap_csup_psdE Pf).
apply/le_anti/andP; split; last first.
  move: (csup_least_ubound (itnorm_set_ns_has_sup f))
    =>/(_ (csup (itnorm_set_psd f)))->//= i Pi.
  move: (csup_upper_bound (itnorm_set_psd_has_sup f))=>/(_ i)->//=.
  move: Pi; rewrite/itnorm_set_psd/=/itnorm_set_ns/==>[[y [Py1 Py2]]].
  exists [> y ; y <]; do ! split. apply/outp_psd.
  by rewrite outp_norm Py1 expr1n. apply/Py2.
move: (csup_least_ubound (itnorm_set_psd_has_sup f))
  =>/(_ (csup (itnorm_set_ns f)))->//= i [x []Px1 []Px2 Px3].
move: {+}Px1; rewrite qualifE=>/psdmx_herm/hermmx_normal/eigen_dec=>P2.
have P3: `|x| = \sum_(i | spectral_diag (h2mx x) 0 i != 0) spectral_diag (h2mx x) 0 i.
  rewrite /normr/=/trfnorm psdmx_trnorm. by move: Px1; rewrite qualifE.
  rewrite {1}P2 mxtrace_mulC mulmxA unitarymxKV// mul1mx mxtrace_diag.
  by rewrite [RHS]big_mkcond/=; apply eq_bigr => j _; case: eqP.
have P4 j : 0 <= spectral_diag (h2mx x) 0 j.
  by move: Px1; rewrite qualifE=>/psdmxP[] _ /nnegmxP/(_ 0 j); rewrite nnegrE.
pose v i := c2h (col i (eigenmx (h2mx x))).
have Pv j : `|v j| = 1 by
  rewrite hnormE dotp_mulmx /v c2hK adj_col unitary_rowMcol// sqrtC1.
have Px: `|f x| <= \sum_(i | spectral_diag (h2mx x) 0 i != 0) 
  spectral_diag (h2mx x) 0 i * `|f [> v i ; v i <]|.
  rewrite -{1}[x]h2mxK {1}P2 mulmx_diag_colrow !linear_sum/=.
  apply: (le_trans (ler_norm_sum _ _ _));
  rewrite [X in _ <= X]big_mkcond; apply ler_sum=>j _.
  case: eqP=>[->| _ ]; first by rewrite scale0r !linear0/= normr0.
  rewrite/= !linearZ/= /normr/= normvZ/= ler_pM=>[// | | | | //].
  apply/trnorm_ge0. rewrite ger0_norm//. 
  by rewrite/normr/= outp.unlock/v c2hK adj_col.
rewrite Px3; apply: (le_trans Px). rewrite -[X in X <= _]mulr1 -invr1 -Px2 P3.
apply: (le_trans (divf_ave_le_max _ _ _)).
  by move=>j _; rewrite realM// ger0_real.
  by move=>j Pj; rewrite lt_neqAle eq_sym Pj/=.
case: bigmax_eq_elemP.
  apply: (le_trans (y := `|f [> u1; u1 <]|))=>//.
  apply: (csup_upper_bound (itnorm_set_ns_has_sup f)).
  exists u1; do ! split; by rewrite ns_norm.
move=>j _ Pj; rewrite mulrC mulKf//.  
apply: (csup_upper_bound (itnorm_set_ns_has_sup f)).
by exists (v j); do ! split.
Qed.

Lemma itnorm_ler_psd f (e : C) : (f \is cpmap) ->
  (forall x, x \is psdlf -> `|f x| <= e * `|x|) -> `|f| <= e.
Proof.
move=>P1 P2; rewrite cpmap_csup_psdE//.
apply: (csup_least_ubound (itnorm_set_psd_has_sup _))=>?[]/= y[]Py1 []Py2 ->.
by move: (P2 y Py1); rewrite Py2 mulr1.
Qed.

Lemma itnorm_def_psd f (e : C) : (f \is cpmap) ->
     (forall x, x \is psdlf -> `|f x| <= e * `|x|)
  -> (exists x, x != 0 /\ `|f x| = e * `|x|) 
  -> `|f| = e.
Proof.
by move=>???; apply/le_anti/andP; split;
[apply: itnorm_ler_psd|apply: itnorm_ger].
Qed.

Lemma itnorm_ler_ns f (e : C) : (f \is cpmap) ->
  (forall u, `|u| = 1 -> `|f [> u ; u <]| <= e) -> `|f| <= e.
Proof.
move=>P1 P2; rewrite cpmap_csup_nsE//.
by apply: (csup_least_ubound (itnorm_set_ns_has_sup _))=>?[]/= y[]Py ->; apply/P2.
Qed.

Lemma itnorm_def_ns f (e : C) : (f \is cpmap) ->
  (forall u, `|u| = 1 -> `|f [> u ; u <]| <= e ) -> (exists x, x != 0 /\ `|f x| = e * `|x|) 
    -> `|f| = e.
Proof. by move=>???; apply/le_anti/andP; split; [apply: itnorm_ler_ns|apply: itnorm_ger]. Qed.

End InducedTraceNorm.

Lemma itnormM (U V W: chsType) (A : 'SO(U,V)) (B : 'SO(V,W)) :
  `|B :o A| <= `|B| * `|A|.
Proof.
apply: itnorm_ler=>x; rewrite soE. apply: (le_trans (itnormP _ _)).
rewrite -mulrA ler_wpM2l//; apply: itnormP.
Qed.

(* choinorm of super operator : fact: choinorm f + g = choinorm f + choinorm g *)
(* if both f and g are CP map *)
Section ChoiNormDef.
Variable (U V : chsType).
Implicit Type (f g : 'SO(U,V)).

Definition choinorm f := \tr| so2choi f | / (dim U)%:R.

Lemma dim_proper_gt0 (R : numDomainType): (0 : R) < (dim U)%:R.
Proof. by rewrite ltr0n dim_proper. Qed.

Lemma choinorm0_eq0 f : choinorm f = 0 -> f = 0.
Proof.
move=>/eqP; rewrite/choinorm mulf_eq0 invr_eq0 =>/orP[/eqP/trnorm0_eq0 P| P].
by rewrite -(so2choiK f) P linear0.
by move: P (@dim_proper U); rewrite pnatr_eq0=>/eqP->.
Qed.

Lemma choinorm_triangle f g : choinorm (f + g) <= choinorm f + choinorm g.
Proof.
rewrite/choinorm linearD/= -mulrDl ler_pM2r//.
by rewrite invr_gt0 dim_proper_gt0. exact: trnorm_triangle.
Qed.

Lemma choinormZ (a: C) f : choinorm (a *: f) = `|a| * choinorm f.
Proof. by rewrite /choinorm linearZ/= trnormZ mulrA. Qed.

HB.instance Definition _ := isVNorm.Build C 'SO(U,V) choinorm
  choinorm_triangle choinorm0_eq0 choinormZ.

Lemma choinormMn f n : choinorm (f *+ n) = choinorm f *+ n.
Proof. exact: normvMn. Qed.

Lemma choinormN f : choinorm (- f) = choinorm f.
Proof. exact: normvN. Qed.

End ChoiNormDef.

Module HermitianTopology.
Import Pointed.Exports Filtered.Exports Topological.Exports
  Uniform.Exports PseudoMetric.Exports.
Import Complete.Exports CompletePseudoMetric.Exports CTopology.
Import FinNormedModule.Exports VNorm.Exports ComplexField.

Section HermitianTopology.
Variable (V: hermitianType).

#[non_forgetful_inheritance]
HB.instance Definition _ := isPointed.Build V 0.
#[non_forgetful_inheritance]
HB.instance Definition _ := hasNbhs.Build V (nbhs_ball_ (ball_ (fun x => `|x|))).
#[non_forgetful_inheritance]
HB.instance Definition _ := Nbhs_isPseudoMetric.Build C V
    nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.
#[non_forgetful_inheritance]
HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build C V erefl.
#[non_forgetful_inheritance]
HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build C V (@hnormZ V).
#[non_forgetful_inheritance]
HB.instance Definition _ := Complete.copy V (V : finNormedModType C).

End HermitianTopology.

Section CHSTopology.
Variable (V: chsType).

#[non_forgetful_inheritance]
HB.instance Definition _ := CompleteNormedModule.copy V (V : hermitianType).

End CHSTopology.

Section LfunTopology.
Variable (U V: chsType).

Local Notation F := 'Hom(U,V).

HB.instance Definition _ := isPointed.Build F 0.
HB.instance Definition _ := hasNbhs.Build F (nbhs_ball_ (ball_ (fun x => `|x|))).
HB.instance Definition _ := Nbhs_isPseudoMetric.Build C F
    nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.
HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build C F erefl.
HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build C F (@trfnormZ U V).
HB.instance Definition _ := Complete.copy F (F : finNormedModType C).

End LfunTopology.

Section SuperopTopology.
Variable (U V: chsType).

Local Notation F := 'SO(U,V).

HB.instance Definition _ := isPointed.Build F 0.
HB.instance Definition _ := hasNbhs.Build F (nbhs_ball_ (ball_ (fun x => `|x|))).
HB.instance Definition _ := Nbhs_isPseudoMetric.Build C F
    nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.
HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build C F erefl.
HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build C F (@itnormZ U V).
HB.instance Definition _ := Complete.copy F (F : finNormedModType C).

End SuperopTopology.

Section Theory.
Local Open Scope classical_set_scope.
(* since trivial mx is not normedModType, we cannot use linear_continuous *)
(* linear_continuous : U -> mx   mx -> U *)

Lemma hermitian_hausdorff (U : hermitianType) : hausdorff_space U.
Proof. exact: Vhausdorff. Qed.

Implicit Type (U V : chsType).

Lemma chs_hausdorff U : hausdorff_space U.
Proof. exact: Vhausdorff. Qed.

Lemma lfun_hausdorff U V : hausdorff_space 'Hom(U,V).
Proof. exact: Vhausdorff. Qed.

Lemma superop_hausdorff U V : hausdorff_space 'SO(U,V).
Proof. exact: Vhausdorff. Qed.

Lemma f2mx_continuous U V : continuous (@f2mx _ U V).
Proof. exact: linear_to_mx_continuous. Qed.

Lemma vecthom_continuous U V : continuous (@Hom _ U V).
Proof. exact: linear_of_mx_continuous. Qed.

Lemma f2mx_cvgnE U V (f : nat -> 'Hom(U,V)) (a : 'Hom(U,V)) :
  f @ \oo --> a = ((f2mx \o f)%FUN @ \oo --> f2mx a).
Proof. apply: (bijective_to_mx_cvgnE _ f2mx_bij); exact: linearP. Qed.

Lemma f2mx_is_cvgnE U V (f : nat -> 'Hom(U,V)) :
  cvgn f = cvgn (f2mx \o f)%FUN.
Proof. apply: (bijective_to_mx_is_cvgnE _ f2mx_bij); exact: linearP. Qed.

Lemma f2mx_limnE U V (f : nat -> 'Hom(U,V)) :
  cvgn f -> limn (f2mx \o f)%FUN = f2mx (limn f).
Proof. apply: (bijective_to_mx_limnE _ f2mx_bij); exact: linearP. Qed.

Lemma h2mx_continuous U V : continuous (@h2mx U V).
Proof. exact: linear_to_mx_continuous. Qed.

Lemma mx2h_continuous U V : continuous (@mx2h U V).
Proof. exact: linear_of_mx_continuous. Qed.

Lemma h2mx_cvgnE U V (f : nat -> 'Hom(U,V)) (a : 'Hom(U,V)) :
  f @ \oo --> a = ((h2mx \o f)%FUN @ \oo --> h2mx a).
Proof. apply: (bijective_to_mx_cvgnE _ h2mx_bij); exact: linearP. Qed.

Lemma h2mx_is_cvgnE U V (f : nat -> 'Hom(U,V)) :
  cvgn f = cvgn (h2mx \o f)%FUN.
Proof. apply: (bijective_to_mx_is_cvgnE _ h2mx_bij); exact: linearP. Qed.

Lemma h2mx_limnE U V (f : nat -> 'Hom(U,V)) :
  cvgn f -> limn (h2mx \o f)%FUN = h2mx (limn f).
Proof. apply: (bijective_to_mx_limnE _ h2mx_bij); exact: linearP. Qed.

Lemma mx2h_cvgnE U V (f : nat -> 'M__) (a : 'M__) :
  f @ \oo --> a = ((@mx2h U V \o f)%FUN @ \oo --> mx2h a).
Proof. apply: (bijective_of_mx_cvgnE _ mx2h_bij); exact: linearP. Qed.

Lemma mx2h_is_cvgnE U V (f : nat -> 'M__) :
  cvgn f = cvgn (@mx2h U V \o f)%FUN.
Proof. apply: (bijective_of_mx_is_cvgnE _ mx2h_bij); exact: linearP. Qed.

Lemma mx2h_limnE U V (f : nat -> 'M__) :
  cvgn f -> limn (@mx2h U V \o f)%FUN = mx2h (limn f).
Proof. apply: (bijective_of_mx_limnE _ mx2h_bij); exact: linearP. Qed.

Lemma h2c_continuous V : continuous (@h2c V).
Proof. apply: (bijective_to_mx_continuous _ h2c_bij); exact: linearP. Qed.

Lemma c2h_continuous V : continuous (@c2h V).
Proof. apply: (bijective_of_mx_continuous _ c2h_bij); exact: linearP. Qed.

Lemma h2c_cvgnE V (u : nat -> V) (a : V): 
  u @ \oo --> a = ((h2c \o u)%FUN @ \oo --> h2c a).
Proof. apply: (bijective_to_mx_cvgnE _ h2c_bij); exact: linearP. Qed.

Lemma c2h_cvgnE V (u : nat -> 'M__) (a : 'M__) : 
  u @ \oo --> a = ((@c2h V \o u)%FUN @ \oo --> c2h a).
Proof. apply: (bijective_of_mx_cvgnE _ c2h_bij); exact: linearP. Qed.

Lemma h2c_is_cvgnE V (u : nat -> V) : cvgn u = cvgn (h2c \o u)%FUN.
Proof. apply: (bijective_to_mx_is_cvgnE _ h2c_bij); exact: linearP. Qed.

Lemma c2h_is_cvgnE V (u : nat -> 'M__) : cvgn u = cvgn (@c2h V \o u)%FUN.
Proof. apply: (bijective_of_mx_is_cvgnE _ c2h_bij). exact: linearP. Qed.

Lemma h2c_limnE V (u : nat -> V) : 
  cvgn u -> limn (h2c \o u)%FUN = h2c (limn u).
Proof. apply: (bijective_to_mx_limnE _ h2c_bij); exact: linearP. Qed.

Lemma c2h_limnE V (u : nat -> 'M__) : 
  cvgn u -> limn (@c2h V \o u)%FUN = c2h (limn u).
Proof. apply: (bijective_of_mx_limnE _ c2h_bij); exact: linearP. Qed.

End Theory.

End HermitianTopology.

Import HermitianTopology.

Section LfunVOrderFinNomredMod.
Local Open Scope classical_set_scope.
Variable (U : chsType).

Lemma closed_gef0 : closed [set x : 'End(U) | (0 : 'End(U)) ⊑ x].
Proof.
rewrite (_ : mkset _ = h2mx @^-1` [set y | (0 : 'M__) ⊑ y]).
by apply/funext=>y/=; rewrite lef_h2mx linear0.
apply: closed_comp=>[x _|]; [apply: h2mx_continuous | apply: cmxclosed_ge].
Qed.

HB.instance Definition lfun_vorderFinNormedModMixin := 
  FinNormedModule_isVOrderFinNormedModule.Build C 'End(U) closed_gef0.
Canonical quantum_lfun__canonical__extnum_VOrderFinNormedModule := 
  VOrderFinNormedModule.Pack (VOrderFinNormedModule.Class lfun_vorderFinNormedModMixin).

End LfunVOrderFinNomredMod.

Section ClosedLfSet.
Local Open Scope classical_set_scope.
Variable (U : chsType).

Lemma closed_lef (g : 'End(U)) : closed [set f : 'End(U) | f ⊑ g].
Proof. exact: closed_lev. Qed.

Lemma closed_gef (g : 'End(U)) : closed [set f : 'End(U) | g ⊑ f].
Proof. exact: closed_gev. Qed.

Lemma closed_psdlf : closed [set f : 'End(U) | f \is psdlf].
Proof.
rewrite (_ : mkset _ = [set y | (0 : 'End(U)) ⊑ y]).
by apply/funext=>y/=; rewrite psdlfE. apply: closed_gev.
Qed.

Lemma trlf_continuous : continuous (@lftrace U).
Proof. exact: linear_continuous. Qed.

Lemma closed_letrlf (x : C) : closed [set f : 'End(U) | \Tr f <= x].
Proof.
rewrite (_ : mkset _ = (@lftrace U) @^-1` [set y | y <= x])%classic.
by apply/funext=>y. apply: closed_linear. apply/cclosed_le.
Qed.

Lemma closed_getrf (x : C) : closed [set f : 'End(U) | x <= \Tr f].
Proof.
rewrite (_ : mkset _ = (@lftrace U) @^-1` [set y | x <= y])%classic.
by apply/funext=>y. apply: closed_linear. apply/cclosed_ge.
Qed.

Lemma closed_denlf : closed [set f : 'End(U) | f \is denlf].
Proof.
rewrite (_ : mkset _ = [set f | f \is psdlf] `&` [set f | \Tr f <= 1]).
by apply/funext=>y/=; rewrite propeqE; split=>[/denlfP//|P]; apply/denlfP.
apply closedI. apply closed_psdlf. apply closed_letrlf.
Qed.

Lemma closed_obslf : closed [set f : 'End(U) | f \is obslf]%classic.
Proof.
rewrite (_ : mkset _ = [set f | (0:'End(U)) ⊑ f] `&` [set f | f ⊑ \1]).
by apply/funext=>y/=; rewrite obslfE propeqE; split=>[/andP//|P]; apply/andP.
apply closedI. apply closed_gef. apply closed_lef.
Qed.
End ClosedLfSet.

Module LfunCPO.
Local Open Scope classical_set_scope.

(* FD and FO are CPO *)
Section LfunCPO.
Local Close Scope lfun_scope.
Variable (V: chsType).

Definition df2f (x : 'FD(V)) := x : 'End(V).
Definition of2f (x : 'FO(V)) := x : 'End(V).

Definition dflub (u : nat -> 'FD(V)) : 'FD(V) :=
  match limn (df2f \o u) \is denlf =P true with
  | ReflectT isden => DenLf_Build isden
  | _ => (0 : 'End(V)) : 'FD
  end.

Definition oflub (u : nat -> 'FO(V)) : 'FO(V) :=
  match limn (of2f \o u) \is obslf =P true with
  | ReflectT isobs => ObsLf_Build isobs
  | _ => (0 : 'End(V)) : 'FO
  end.

Lemma chaindf2f (u : nat -> 'FD(V)) : chain u -> nondecreasing_seq (df2f \o u).
Proof. by move=>/chain_homo P m n Pmn; move: (P _ _ Pmn); rewrite leEsub. Qed.

Lemma chaindf_lb (u : nat -> 'FD(V)) : lbounded_by (0:'End(V))%VF (df2f \o u).
Proof. move=>i; apply: denf_ge0. Qed.

Lemma chaindf_ub (u : nat -> 'FD(V)) : ubounded_by (\1:'End(V))%VF (df2f \o u).
Proof. by move=>i; apply: denf_le1. Qed.

Lemma chainof2f (u : nat -> 'FO(V)) : chain u -> nondecreasing_seq (of2f \o u).
Proof. by move=>/chain_homo P m n Pmn; move: (P _ _ Pmn); rewrite leEsub. Qed.

Lemma chainof_lb (u : nat -> 'FO(V)) : lbounded_by (0:'End(V))%VF (of2f \o u).
Proof. by move=>i; apply: obsf_ge0. Qed.

Lemma chainof_ub (u : nat -> 'FO(V)) : ubounded_by (\1:'End(V))%VF (of2f \o u).
Proof. by move=>i; apply: obsf_le1. Qed.

Lemma limn_denlf (u : nat -> 'FD(V)) : 
  cvgn (df2f \o u) -> [set x | x \is denlf] (limn (df2f \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (df2f \o u) _ _ _ _)=>//.
apply closed_denlf. by apply: nearW=>x; rewrite /=/df2f is_denlf.
Qed.

Lemma limn_obslf (u : nat -> 'FO(V)) : 
  cvgn (of2f \o u) -> [set x | x \is obslf] (limn (of2f \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (of2f \o u) _ _ _ _)=>//.
apply closed_obslf. by apply: nearW=>x; rewrite /=/of2f is_obslf.
Qed.

Lemma dflub_lub : forall c : nat -> 'FD(V), chain c -> (forall i, c i ⊑ dflub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> dflub c ⊑ x).
Proof.
move=>c Pc. move: (chaindf2f Pc) (chaindf_ub c)=>P1 P2.
move: (vnondecreasing_is_cvgn P1 P2)=>P3.
move: (nondecreasing_cvgn_lev P1 P3)=>P4.
rewrite /dflub; case: eqP=>P5; last by exfalso; apply P5; apply limn_denlf.
split. by move=>i; rewrite leEsub/= P4.
by move=>x Px; rewrite leEsub/=; apply: limn_lev.
Qed.

Lemma dflub_ub : forall c : nat -> 'FD(V), chain c -> (forall i, c i ⊑ dflub c).
Proof. by move=>c /dflub_lub=>[[P1]]. Qed.

Lemma dflub_least : forall c : nat -> 'FD(V), 
  chain c -> forall x, (forall i, c i ⊑ x) -> dflub c ⊑ x.
Proof. by move=>c /dflub_lub=>[[_ ]]. Qed.

Lemma oflub_lub : forall c : nat -> 'FO(V), chain c -> (forall i, c i ⊑ oflub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> oflub c ⊑ x).
Proof.
move=>c Pc. move: (chainof2f Pc) (chainof_ub c)=>P1 P2.
move: (vnondecreasing_is_cvgn P1 P2)=>P3.
move: (nondecreasing_cvgn_lev P1 P3)=>P4.
rewrite /oflub; case: eqP=>P5; last by exfalso; apply P5; apply limn_obslf.
split. by move=>i; rewrite leEsub/= P4.
by move=>x Px; rewrite leEsub; apply: limn_lev.
Qed.

Lemma oflub_ub : forall c : nat -> 'FO(V), chain c -> (forall i, c i ⊑ oflub c).
Proof. by move=>c /oflub_lub=>[[P1]]. Qed.

Lemma oflub_least : forall c : nat -> 'FO(V), 
  chain c -> forall x, (forall i, c i ⊑ x) -> oflub c ⊑ x.
Proof. by move=>c /oflub_lub=>[[_ ]]. Qed.

End LfunCPO.

Module Import Exports.
HB.instance Definition _ (V : chsType) := isCpo.Build ring_display 
  'FD(V) (@denf_ges0 V) (@dflub_ub V) (@dflub_least V).
HB.instance Definition _ (V : chsType) := isCpo.Build ring_display 
  'FO(V) (@obsf_ges0 V) (@oflub_ub V) (@oflub_least V).
End Exports.

End LfunCPO.
Export LfunCPO.Exports.

Section ClosedSOSet.
Local Open Scope classical_set_scope.
Variable (U V : chsType).
Implicit Type (f g : 'SO(U,V)).

Lemma so2choi_continuous : continuous (@so2choi U V).
Proof. apply: (bijective_to_mx_continuous _ so2choi_bij); exact: linearP. Qed.

Lemma choi2so_continuous : continuous (@choi2so U V).
Proof. apply: (bijective_of_mx_continuous _ choi2so_bij); exact: linearP. Qed.

Lemma so2choi_cvgE (f : nat -> 'SO(U,V)) (a : 'SO(U,V)) :
  f @ \oo --> a = ((so2choi \o f)%FUN @ \oo --> so2choi a).
Proof. apply: (bijective_to_mx_cvgnE _ so2choi_bij); exact: linearP. Qed.

Lemma so2choi_is_cvgE (f : nat -> 'SO(U,V)) :
  cvgn f = cvgn (so2choi \o f)%FUN.
Proof. apply: (bijective_to_mx_is_cvgnE _ so2choi_bij); exact: linearP. Qed.

Lemma so2choi_limE (f : nat -> 'SO(U,V)) :
  cvgn f -> limn (so2choi \o f)%FUN = so2choi (limn f).
Proof. apply: (bijective_to_mx_limnE _ so2choi_bij); exact: linearP. Qed.

Lemma closed_geso0 : closed [set E | (0 : 'SO(U,V)) ⊑ E].
Proof.
rewrite (_ : mkset _ = so2choi @^-1` [set y | (0 : 'M__) ⊑ y]).
by apply/funext=>y/=; rewrite leso_mx linear0.
apply: closed_to_mx_linear. apply: cmxclosed_ge.
Qed.

HB.instance Definition superop_vorderFinNormedModMixin := 
  FinNormedModule_isVOrderFinNormedModule.Build C 'SO(U,V) closed_geso0.
Canonical quantum_soperop__canonical__extnum_VOrderFinNormedModule := 
  VOrderFinNormedModule.Pack (VOrderFinNormedModule.Class superop_vorderFinNormedModMixin).

(* qo is a closed set among all super operators *)
Lemma closed_isqo : closed [set f : 'SO(U,V) | f \is cptn].
Proof.
rewrite (_ : mkset _ = (so2choi @^-1` [set y | (0 : 'M__) ⊑ y]) `&` 
  (so2choi @^-1` [set y | ptrace2 y ⊑ 1%:M])).
apply/funext=>y/=; rewrite qualifE qualifE propeqE [y \is tnmap]qualifE 
  /Order.le/= /lownerle subr0; split=>[/andP//|[->->//]].
apply closedI; apply: closed_to_mx_linear. apply: cmxclosed_ge.
move: (@cmxclosed_le _ _ (1%:M : 'M[C]_(dim U))).
apply: cmxclosed_comp. exact: linearP.
Qed.
End ClosedSOSet.

Section Continuous.

Lemma bounded_near_cst {K : numFieldType} (V : normedModType K) (x : V):
  \forall x0 \near nbhs +oo, \forall x1 \near x, `|x1| <= x0.
Proof.
exists (`|x|+1); split; first by rewrite ger0_real// addr_ge0.
move=>M PM; have: (x --> x)%classic by apply: cvg_refl.
move=>/fcvgrPdist_lt/(_ 1 ltr01); rewrite near_simpl=>Py.
near=>y. have Pxy: `|x - y| < 1 by near: y.
apply/ltW/(lt_trans _ PM). rewrite -ltrBlDl.
by apply/(le_lt_trans (lerB_dist _ _)); rewrite -normrN opprB.
Unshelve. end_near.
Qed.

Lemma bilinear_continuousP {K : numFieldType} {U V W : normedModType K} 
  (f : U -> V -> W) :
  (forall a b c, f a b - f a c = f a (b - c)) ->
  (forall a b c, f a c - f b c = f (a - b) c) ->
  (forall a b, `|f a b| <= `|a| * `|b|) ->
  continuous (fun z : U * V => f z.1 z.2).
Proof.
move=>H1 H2 H3 [/= k x]; apply/cvgrPdist_lt => _/posnumP[e]; near +oo_K => M.
have M0 : 0 < M by [].
near=> l z => /=.
rewrite (@distm_lt_split _ _ (f k z))// ?(H1, H2).
rewrite (@le_lt_trans _ _ (M * `|x - z|)) ?ler_wpM2r -?ltr_pdivlMl//.
apply/(le_trans (H3 _ _))/ler_wpM2r=>[//|].
by apply/ltW; near: M; exists `|k|; split=>//.
by near: z; apply: cvgr_dist_lt; rewrite // mulrC divr_gt0.
rewrite (@le_lt_trans _ _ (`|k - l| * M)) ?ler_wpM2l -?ltr_pdivlMr//.
apply/(le_trans (H3 _ _))/ler_wpM2l=>[//|].
by near: z; rewrite near_simpl/=; near: M; apply: bounded_near_cst.
by near: l; apply: cvgr_dist_lt; rewrite // divr_gt0.
Unshelve. all: end_near.
Qed.

Lemma lfun_comp_continuous {U V W : chsType} :
  continuous (fun z : 'Hom(U,V) * 'Hom(W,U) => z.1 \o z.2).
Proof.
by apply/bilinear_continuousP; intros; rewrite ?(linearBl, linearBr)// trfnormM.
Qed.

Lemma so_comp_continuous {U V W : chsType} :
  continuous (fun z : 'SO(U,V) * 'SO(W,U) => z.1 :o z.2).
Proof.
by apply/bilinear_continuousP; intros; rewrite ?(linearBl, linearBr)// itnormM.
Qed.

Lemma so_compr_continuous {U V W : chsType} :
  continuous (fun z : 'SO(U,V) * 'SO(V,W) => z.1 o: z.2).
Proof.
by apply/bilinear_continuousP; intros;
rewrite ?(linearBl, linearBr)// comp_soErl mulrC itnormM.
Qed.

Lemma lfun_continuous {U V : chsType} :
  continuous (fun z : 'Hom(U,V) * U => z.1 z.2).
Proof.
apply/bilinear_continuousP; intros.
by rewrite linearB. by rewrite lfunE/= lfunE. apply: trfnormP.
Qed.

Lemma so_continuous {U V : chsType} :
  continuous (fun z : 'SO(U,V) * 'End(U) => z.1 z.2).
Proof.
apply/bilinear_continuousP; intros.
by rewrite linearB. by rewrite soE/= soE. apply: itnormP.
Qed.

Variable (U V W: chsType) (T : Type) (F : set_system T).
Implicit Type (FF : Filter F) (PF : ProperFilter F).
Local Open Scope classical_set_scope.

Section SO.
Implicit Type (f: T -> 'SO(U,V)) (g : 'SO(U,V)) (x : T -> 'End(U)) (y : 'End(U)).

Lemma so_cvg {FF} f g x y :
  f @ F --> g -> x @ F --> y -> (fun i => f i (x i)) @ F --> g y.
Proof.
move=> ? ?; apply: continuous2_cvg => //;
exact: @so_continuous _ _ (g,y).
Qed.

Lemma so_cvgl {FF} y f g :
  f @ F --> g -> (fun i => f i y) @ F --> g y.
Proof. by move=>P; apply: so_cvg=>//; apply: cvg_cst. Qed.

Lemma so_cvgr {FF} g x y :
  x @ F --> y -> (fun i => g (x i)) @ F --> g y.
Proof. by move=>P; apply: so_cvg=>//; apply: cvg_cst. Qed.

Lemma so_is_cvg {FF} f x :
  cvg (f @ F) -> cvg (x @ F) -> cvg ((fun i => f i (x i)) @ F).
Proof.
by move=>??; apply/cvg_ex;
exists (lim (f @ F) (lim (x @ F))); apply: so_cvg.
Qed.  

Lemma so_is_cvgl {FF} y f :
  cvg (f @ F) -> cvg ((fun i => f i y) @ F).
Proof. by move=>P; apply: so_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma so_is_cvgr {FF} g x :
  cvg (x @ F) -> cvg ((fun i => g (x i)) @ F).
Proof. by move=>P; apply: so_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma so_lim {PF} f x : cvg (f @ F) -> cvg (x @ F) -> 
  lim ((fun i => f i (x i)) @ F) = lim (f @ F) (lim (x @ F)).
Proof. by move=>??; apply: cvg_lim=>//; apply: so_cvg. Qed.

Lemma so_liml {PF} y f : cvg (f @ F) ->
  lim ((fun i => f i y) @ F) = lim (f @ F) y.
Proof. by move=>?; apply: cvg_lim=>//; apply: so_cvgl. Qed.

Lemma so_limr {PF} g x : cvg (x @ F) -> 
  lim ((fun i => g (x i)) @ F) = g (lim (x @ F)).
Proof. by move=>?; apply: cvg_lim=>//; apply: so_cvgr. Qed.
End SO.

Section LFun.
Implicit Type (f: T -> 'Hom(U,V)) (g : 'Hom(U,V)) (x : T -> U) (y : U).

Lemma lfun_cvg {FF} f g x y :
  f @ F --> g -> x @ F --> y -> (fun i => f i (x i)) @ F --> g y.
Proof.
by move=> ? ?; apply: continuous2_cvg => //;
exact: (@lfun_continuous _ _ (g,y)).
Qed.

Lemma lfun_cvgl {FF} y f g :
  f @ F --> g -> (fun i => f i y) @ F --> g y.
Proof. by move=>P; apply: lfun_cvg=>//; apply: cvg_cst. Qed.

Lemma lfun_cvgr {FF} g x y :
  x @ F --> y -> (fun i => g (x i)) @ F --> g y.
Proof. by move=>P; apply: lfun_cvg=>//; apply: cvg_cst. Qed.

Lemma lfun_is_cvg {FF} f x :
  cvg (f @ F) -> cvg (x @ F) -> cvg ((fun i => f i (x i)) @ F).
Proof.
by move=>??; apply/cvg_ex;
exists (lim (f @ F) (lim (x @ F))); apply: lfun_cvg.
Qed.  

Lemma lfun_is_cvgl {FF} y f :
  cvg (f @ F) -> cvg ((fun i => f i y) @ F).
Proof. by move=>P; apply: lfun_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma lfun_is_cvgr {FF} g x :
  cvg (x @ F) -> cvg ((fun i => g (x i)) @ F).
Proof. by move=>P; apply: lfun_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma lfun_lim {PF} f x : cvg (f @ F) -> cvg (x @ F) -> 
  lim ((fun i => f i (x i)) @ F) = lim (f @ F) (lim (x @ F)).
Proof. by move=>??; apply: cvg_lim=>//; apply: lfun_cvg. Qed.

Lemma lfun_liml {PF} y f : cvg (f @ F) ->
  lim ((fun i => f i y) @ F) = lim (f @ F) y.
Proof. by move=>?; apply: cvg_lim=>//; apply: lfun_cvgl. Qed.

Lemma lfun_limr {PF} g x : cvg (x @ F) -> 
  lim ((fun i => g (x i)) @ F) = g (lim (x @ F)).
Proof. by move=>?; apply: cvg_lim=>//; apply: lfun_cvgr. Qed.
End LFun.

Section SO_comp.
Implicit Type (f: T -> 'SO(U,V)) (g : 'SO(U,V)) (x : T -> 'SO(W,U)) (y : 'SO(W,U)).

Lemma so_comp_cvg {FF} f g x y :
  f @ F --> g -> x @ F --> y -> (fun i => f i :o x i) @ F --> g :o y.
Proof.
by move=> ? ?; apply: continuous2_cvg => //;
exact: (@so_comp_continuous _ _ _ (g,y)).
Qed.

Lemma so_comp_cvgl {FF} y f g :
  f @ F --> g -> (fun i => f i :o y) @ F --> g :o y.
Proof. by move=>P; apply: so_comp_cvg=>//; apply: cvg_cst. Qed.

Lemma so_comp_cvgr {FF} g x y :
  x @ F --> y -> (fun i => g :o (x i)) @ F --> g :o y.
Proof. by move=>P; apply: so_comp_cvg=>//; apply: cvg_cst. Qed.

Lemma so_comp_is_cvg {FF} f x :
  cvg (f @ F) -> cvg (x @ F) -> cvg ((fun i => f i :o x i) @ F).
Proof.
by move=>??; apply/cvg_ex;
exists (lim (f @ F) :o (lim (x @ F)));
apply: so_comp_cvg.
Qed.  

Lemma so_comp_is_cvgl {FF} y f :
  cvg (f @ F) -> cvg ((fun i => f i :o y) @ F).
Proof. by move=>P; apply: so_comp_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma so_comp_is_cvgr {FF} g x :
  cvg (x @ F) -> cvg ((fun i => g :o (x i)) @ F).
Proof. by move=>P; apply: so_comp_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma so_comp_lim {PF} f x : cvg (f @ F) -> cvg (x @ F) -> 
  lim ((fun i => f i :o x i) @ F) = lim (f @ F) :o (lim (x @ F)).
Proof. by move=>??; apply: cvg_lim=>//; apply: so_comp_cvg. Qed.

Lemma so_comp_liml {PF} y f : cvg (f @ F) ->
  lim ((fun i => f i :o y) @ F) = lim (f @ F) :o y.
Proof. by move=>?; apply: cvg_lim=>//; apply: so_comp_cvgl. Qed.

Lemma so_comp_limr {PF} g x : cvg (x @ F) -> 
  lim ((fun i => g :o (x i)) @ F) = g :o (lim (x @ F)).
Proof. by move=>?; apply: cvg_lim=>//; apply: so_comp_cvgr. Qed.
End SO_comp.

Section SO_compr.
Implicit Type (f: T -> 'SO(U,V)) (g : 'SO(U,V)) (x : T -> 'SO(V,W)) (y : 'SO(V,W)).

Lemma so_compr_cvg {FF} f g x y :
  f @ F --> g -> x @ F --> y -> (fun i => f i o: x i) @ F --> g o: y.
Proof.
by move=> ? ?; apply: continuous2_cvg => //;
exact: (@so_compr_continuous _ _ _ (g,y)).
Qed.

Lemma so_compr_cvgl {FF} y f g :
  f @ F --> g -> (fun i => f i o: y) @ F --> g o: y.
Proof. by move=>P; apply: so_compr_cvg=>//; apply: cvg_cst. Qed.

Lemma so_compr_cvgr {FF} g x y :
  x @ F --> y -> (fun i => g o: (x i)) @ F --> g o: y.
Proof. by move=>P; apply: so_compr_cvg=>//; apply: cvg_cst. Qed.

Lemma so_compr_is_cvg {FF} f x :
  cvg (f @ F) -> cvg (x @ F) -> cvg ((fun i => f i o: x i) @ F).
Proof.
by move=>??; apply/cvg_ex; exists (lim (f @ F) o: (lim (x @ F)));
apply: so_compr_cvg.
Qed.  

Lemma so_compr_is_cvgl {FF} y f :
  cvg (f @ F) -> cvg ((fun i => f i o: y) @ F).
Proof. by move=>P; apply: so_compr_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma so_compr_is_cvgr {FF} g x :
  cvg (x @ F) -> cvg ((fun i => g o: (x i)) @ F).
Proof. by move=>P; apply: so_compr_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma so_compr_lim {PF} f x : cvg (f @ F) -> cvg (x @ F) -> 
  lim ((fun i => f i o: x i) @ F) = lim (f @ F) o: (lim (x @ F)).
Proof. by move=>??; apply: cvg_lim=>//; apply: so_compr_cvg. Qed.

Lemma so_compr_liml {PF} y f : cvg (f @ F) ->
  lim ((fun i => f i o: y) @ F) = lim (f @ F) o: y.
Proof. by move=>?; apply: cvg_lim=>//; apply: so_compr_cvgl. Qed.

Lemma so_compr_limr {PF} g x : cvg (x @ F) -> 
  lim ((fun i => g o: (x i)) @ F) = g o: (lim (x @ F)).
Proof. by move=>?; apply: cvg_lim=>//; apply: so_compr_cvgr. Qed.
End SO_compr.

Section Lfun_comp.
Implicit Type (f: T -> 'Hom(U,V)) (g : 'Hom(U,V)) (x : T -> 'Hom(W,U)) (y : 'Hom(W,U)).

Lemma lfun_comp_cvg {FF} f g x y :
  f @ F --> g -> x @ F --> y -> (fun i => f i \o x i) @ F --> g \o y.
Proof.
by move=> ? ?; apply: continuous2_cvg => //;
exact: (@lfun_comp_continuous _ _ _ (g,y)).
Qed.

Lemma lfun_comp_cvgl {FF} y f g :
  f @ F --> g -> (fun i => f i \o y) @ F --> g \o y.
Proof. by move=>P; apply: lfun_comp_cvg=>//; apply: cvg_cst. Qed.

Lemma lfun_comp_cvgr {FF} g x y :
  x @ F --> y -> (fun i => g \o (x i)) @ F --> g \o y.
Proof. by move=>P; apply: lfun_comp_cvg=>//; apply: cvg_cst. Qed.

Lemma lfun_comp_is_cvg {FF} f x :
  cvg (f @ F) -> cvg (x @ F) -> cvg ((fun i => f i \o x i) @ F).
Proof.
by move=>??; apply/cvg_ex; exists (lim (f @ F) \o (lim (x @ F)));
apply: lfun_comp_cvg.
Qed.  

Lemma lfun_comp_is_cvgl {FF} y f :
  cvg (f @ F) -> cvg ((fun i => f i \o y) @ F).
Proof. by move=>P; apply: lfun_comp_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma lfun_comp_is_cvgr {FF} g x :
  cvg (x @ F) -> cvg ((fun i => g \o (x i)) @ F).
Proof. by move=>P; apply: lfun_comp_is_cvg=>//; apply: is_cvg_cst. Qed.

Lemma lfun_comp_lim {PF} f x : cvg (f @ F) -> cvg (x @ F) -> 
  lim ((fun i => f i \o x i) @ F) = lim (f @ F) \o (lim (x @ F)).
Proof. by move=>??; apply: cvg_lim=>//; apply: lfun_comp_cvg. Qed.

Lemma lfun_comp_liml {PF} y f : cvg (f @ F) ->
  lim ((fun i => f i \o y) @ F) = lim (f @ F) \o y.
Proof. by move=>?; apply: cvg_lim=>//; apply: lfun_comp_cvgl. Qed.

Lemma lfun_comp_limr {PF} g x : cvg (x @ F) -> 
  lim ((fun i => g \o (x i)) @ F) = g \o (lim (x @ F)).
Proof. by move=>?; apply: cvg_lim=>//; apply: lfun_comp_cvgr. Qed.
End Lfun_comp.

End Continuous.

HB.lock Definition krausop (U V : chsType) (x : 'SO(U,V)) := choi2kraus (so2choi x).

Section KrausOp.
Variable (U V : chsType).

Lemma trNincrP (F : finType) (A B : 'TN(F;U,V)) : A =1 B <-> A = B.
Proof.
split=>[/funext|->//]. case: A=>A[[P1]]/=; case: B=>B[[P2]]/= eqAB.
by move: P1; rewrite eqAB=>P1; rewrite (eq_irrelevance P1 P2).
Qed.

Lemma qmeasureP (F : finType) (A B : 'QM(F;U,V)) : A =1 B <-> A = B.
Proof.
split=>[/funext|->//]. case: A=>A[[PA1]][PA2]/=; case: B=>B[[PB1]][PB2]/= eqAB.
by move: PA1 PA2; rewrite eqAB=>PA1 PA2;
rewrite (eq_irrelevance PA1 PB1) (eq_irrelevance PA2 PB2).
Qed.
Definition trPresvP := qmeasureP.

Definition is_trpresv := @is_qmeasure.

Lemma qmeasure_tpE (F : finType) (A : 'QM(F;U,V)) :
  \sum_i ((A i)^A \o A i) = \1.
Proof. apply/eqP/is_qmeasure. Qed.

Lemma tn_trlf_psd (F : finType) (A : 'TN(F;U,V)) x :
  x \is psdlf -> \sum_i \Tr (A i \o x \o (A i)^A) <= \Tr x.
Proof.
under eq_bigr do rewrite lftraceC comp_lfunA.
rewrite -linear_sum/= -linear_suml/= -{3}(comp_lfun1l x)=>Px.
by apply/lef_psdtr=>[|//]; apply/is_trnincr.
Qed.

Lemma qm_trlf (F : finType) (A : 'QM(F;U,V)) x :
  \sum_i \Tr (A i \o x \o (A i)^A) = \Tr x.
Proof. 
under eq_bigr do rewrite lftraceC comp_lfunA.
by rewrite -linear_sum/= -linear_suml/= qmeasure_tpE comp_lfun1l.
Qed.
Definition tp_trlf := qm_trlf.

Lemma is_cptn (x : 'QO(U,V)) : (x : 'SO) \is cptn.
Proof. apply/cptnP; split. apply/is_cpmap. apply/is_tnmap. Qed.
  
Lemma is_cptp (x : 'QC(U,V)) : (x : 'SO) \is cptp.
Proof. apply/cptpP; split. apply/is_cpmap. apply/is_tpmap. Qed.

(* dualso property cp - cp  qo <-> dqo  qc <-> qu *)
Lemma dualso_cp (E : 'CP(U,V)) : E ^*o \is cpmap.
Proof. by rewrite dualso_cpE is_cpmap. Qed.
HB.instance Definition _ (E : 'CP(U,V)) := 
  isCPMap.Build V U E^*o (dualso_cp E).
Lemma dualso_dualtn (E : 'QO(U,V)) : (E^*o)^*o \is tnmap.
Proof. by rewrite dualsoK is_tnmap. Qed.
HB.instance Definition _ (E : 'QO(U,V)) :=
  CPMap_isDTNMap.Build V U E^*o (dualso_dualtn E).
Lemma dualso_tn (E : 'DQO(U,V)) : E^*o \is tnmap.
Proof. by rewrite is_dualtn. Qed.
HB.instance Definition _ (E : 'DQO(U,V)) :=
  CPMap_isTNMap.Build V U E^*o (dualso_tn E).
Lemma dualso_unital (E : 'QC(U,V)) : (E^*o)^*o \is tpmap.
Proof. by rewrite dualsoK is_tpmap. Qed.
HB.instance Definition _ (E : 'QC(U,V)) :=
  DualQO_isUnitalMap.Build V U E^*o (dualso_unital E).
Lemma dualso_tp (E : 'QU(U,V)) : E^*o \is tpmap.
Proof. by rewrite is_dualtp. Qed.
HB.instance Definition _ (E : 'QU(U,V)) :=
  QOperation_isTPMap.Build V U E^*o (dualso_tp E).

Lemma krausso_cp (F : finType) (f : F -> 'Hom(U,V)) :
  krausso f \is cpmap.
Proof. apply/cpmapP; exact: krausso2choi_psd. Qed.
HB.instance Definition _ F f := isCPMap.Build U V (krausso f) (@krausso_cp F f).

Lemma formso_dual (f : 'Hom(U,V)) : (formso f)^*o = formso (f^A).
Proof. by rewrite dualso_krausso. Qed.

Lemma formso_cp (f : 'Hom(U,V)) : formso f \is cpmap.
Proof. apply: krausso_cp. Qed.
HB.instance Definition _ f := isCPMap.Build U V (formso f) (formso_cp f).
Lemma formso_tn (f : 'FB1(U,V)) : formso f \is tnmap.
Proof. by rewrite krausso_tnE /trace_nincr big_ord1 bound1f_form_le1. Qed.
HB.instance Definition _ (f : 'FB1(U,V)) := 
  CPMap_isTNMap.Build U V (formso f) (formso_tn f).
Lemma formso_tp (f : 'FI(U,V)) : formso f \is tpmap.
Proof. by rewrite krausso_tpE /trace_presv big_ord1 isofE eqxx. Qed.
HB.instance Definition _ (f : 'FI(U,V)) := 
  QOperation_isTPMap.Build U V (formso f) (formso_tp f).
Lemma formso_dualtn (f : 'FB1(U,V)) : (formso f)^*o \is tnmap.
Proof. by rewrite formso_dual krausso_tnE /trace_nincr big_ord1 adjfK bound1f_formV_le1. Qed.
HB.instance Definition _ (f : 'FB1(U,V)) :=
  CPMap_isDTNMap.Build U V (formso f) (formso_dualtn f).
Lemma formso_unital (f : 'FGI(U,V)) : (formso f)^*o \is tpmap.
Proof. by rewrite formso_dual krausso_tpE /trace_presv big_ord1 adjfK gisofEr. Qed.
HB.instance Definition _ (f : 'FGI(U,V)) :=
  DualQO_isUnitalMap.Build U V (formso f) (formso_unital f).

Lemma krausso_qoP (F : finType) (f : F -> 'Hom(U,V)) :
  trace_nincr f <-> krausso f \is cptn.
Proof. by rewrite qualifE krausso_cp krausso_tnE. Qed.
Lemma krausso_tn (F : finType) (f : 'TN(F;U,V)) :
  krausso f \is tnmap.
Proof. by apply/cptn_tnmap/krausso_qoP/is_trnincr. Qed.
HB.instance Definition _ F (f : 'TN(F;U,V)) :=
  CPMap_isTNMap.Build U V (krausso f) (krausso_tn f).

Lemma krausso_qcP (F : finType) (f : F -> 'Hom(U,V)) :
  trace_presv f <-> krausso f \is cptp.
Proof. by rewrite qualifE krausso_tpE krausso_cp. Qed.
Lemma krausso_tp (F : finType) (f : 'QM(F;U,V)) :
  krausso f \is tpmap.
Proof. apply/cptp_tpmap/krausso_qcP/is_trpresv. Qed.
HB.instance Definition _ F (f : 'QM(F;U,V)) :=
  QOperation_isTPMap.Build U V (krausso f) (krausso_tp f).

Lemma krausopE (x : 'CP(U,V)) : x = krausso (krausop x) :> 'SO.
Proof.
by apply/val_inj; rewrite krausop.unlock/= !krausso2choiK//; 
  apply: cpmapP; apply/is_cpmap.
Qed.

Lemma krausE (E : 'CP(U,V)) x :
  E x = \sum_i ((krausop E i) \o x \o (krausop E i)^A)%VF.
Proof. by rewrite {1}krausopE kraussoE. Qed.

Lemma krausop_tn (x : 'QO(U,V)) : trace_nincr (krausop x).
Proof. by rewrite krausso_qoP -krausopE is_cptn. Qed.
HB.instance Definition _ (x : 'QO(U,V)) := isTraceNincr.Build 
  U V 'I_(dim U * dim V) (krausop x) (krausop_tn x).

Lemma krausop_tp (x : 'QC(U,V)) : trace_presv (krausop x).
Proof. by rewrite krausso_qcP -krausopE is_cptp. Qed.
HB.instance Definition _ (x : 'QC(U,V)) := TraceNincr_isQMeasure.Build 
  U V 'I_(dim U * dim V) (krausop x) (krausop_tp x).

Lemma cp_isqcP (E: 'CP(U,V)) : 
  reflect (forall x, \Tr (E x) = \Tr x) ((E : 'SO) \is cptp).
Proof. by apply/(iffP (cptpP _))=>[[ _ /tpmapP//]|/tpmapP->]; rewrite is_cpmap. Qed.

Lemma cp_isqoP (E : 'CP(U,V)) :
  reflect (forall x, x \is psdlf -> \Tr (E x) <= \Tr x) ((E : 'SO) \is cptn).
Proof.
apply/(iffP (cptnP _)); rewrite -(denlf_psdlf_eq_nnegz _) ?denlf_denf_eq_prop.
1,3: by move=>c Pc/= x Px; rewrite !linearZ/= ler_wpM2l.
by move=>[] _ /tnmapP. by move=>/tnmapP->; rewrite is_cpmap.
Qed.

Lemma cp_isdualtpE (E : 'CP(V,U)) : E^*o \is tpmap = (E \1 == \1).
Proof.
apply/eqb_iff; split=>[|/eqP P]; last first.
  by apply/tpmapP=>x; rewrite -[E^*o x]comp_lfun1r -dualso_trlfEV P comp_lfun1r.
move: (@is_cpmap _ _ E); rewrite -dualso_cpE -{3}(dualsoK E) =>P1.
rewrite (CPMap_BuildE P1) krausopE krausso_tpE /trace_presv=>/eqP <-.
by rewrite dualso_krausE; under eq_bigr do rewrite comp_lfun1r.
Qed.

Lemma cp_isdualtpP (E : 'CP(V,U)) : reflect (E \1 = 1) (E^*o \is tpmap).
Proof. by rewrite cp_isdualtpE; apply/(iffP eqP). Qed.

Lemma cp_isquE (E : 'CP(V,U)) : E^*o \is cptp = (E \1 == \1).
Proof. by rewrite qualifE dualso_cpE is_cpmap/= cp_isdualtpE. Qed.

Lemma cp_isquP (E : 'CP(V,U)) : reflect (E \1 = 1) (E^*o \is cptp).
Proof. by rewrite cp_isquE; apply/(iffP eqP). Qed.

Lemma cp_isdualtnE (E : 'CP(V,U)) : E^*o \is tnmap = (E \1 <= \1).
Proof.
apply/eqb_iff; split=>[|/lef_trden P]; last first.
  apply/tnmapP=>x; rewrite -[E^*o x]comp_lfun1l -dualso_trlfE.
  by apply/(le_trans (P x)); rewrite comp_lfun1l.
move: (@is_cpmap _ _ E); rewrite -dualso_cpE -{3}(dualsoK E) =>P1.
rewrite (krausopE (CPMap_Build P1)) krausso_tnE /trace_nincr.
by apply: le_trans; rewrite dualso_krausE; under eq_bigr do rewrite comp_lfun1r.
Qed.

Lemma cp_isdualtnP (E : 'CP(V,U)) : reflect (E \1 <= 1) (E^*o \is tnmap).
Proof. by rewrite cp_isdualtnE; apply/(iffP idP). Qed.

Lemma cp_isdqoE (E : 'CP(V,U)) : E^*o \is cptn = (E \1 <= \1).
Proof. by rewrite qualifE dualso_cpE is_cpmap/= cp_isdualtnE. Qed.

Lemma cp_isdqoP (E : 'CP(V,U)) : reflect (E \1 <= 1) (E^*o \is cptn).
Proof. by rewrite cp_isdqoE; apply/(iffP idP). Qed.

Lemma qc_trlfE (E: 'QC(U,V)) x : \Tr (E x) = \Tr x.
Proof. apply/cp_isqcP/is_cptp. Qed.

Lemma qo_trlfE (E: 'QO(U,V)) x : x \is psdlf -> \Tr (E x) <= \Tr x.
Proof. apply/cp_isqoP/is_cptn. Qed.

(* TODO : renaming? *)
Lemma qu1_eq1 (E : 'QU(V,U)) : E \1 = \1.
Proof. by apply/eqP; rewrite -cp_isdualtpE is_dualtp. Qed.

Lemma dqo1_le1 (E : 'DQO(V,U)) : E \1 <= \1.
Proof. by apply/eqP; rewrite -cp_isdualtnE is_dualtn. Qed.

Lemma cp_psdP (E : 'CP(U,V)) x : x \is psdlf -> (E x) \is psdlf.
Proof.
rewrite !psdlfE=>P1.
by rewrite krausE/= sumv_ge0// =>i _; apply/gef0_formfV.
Qed.

Lemma cp_ge0 (E: 'CP(U,V)) (x:'End(U)) :
  (0 : 'End(U)) ⊑ x -> (0 : 'End(V)) ⊑ E x.
Proof. rewrite -!psdlfE; exact: cp_psdP. Qed.

Lemma cp_preserve_order (E: 'CP(U,V)) (x y:'End(U)) :
  x ⊑ y -> E x ⊑ E y.
Proof. by rewrite -subv_ge0=>/(cp_ge0 E); rewrite linearB/= subv_ge0. Qed.

Lemma cp_geso0 (E: 'CP(U,V)) : (0 : 'SO) ⊑ E.
Proof.
by rewrite leso_mx linear0 le_lownerE subr0;
apply: cpmapP; apply/is_cpmap.
Qed.

Lemma scalemx_le m (a b: C) : a <= b -> (a%:M : 'M_m) ⊑ b%:M.
Proof.
move=>P1; rewrite le_lownerE; apply/psdmx_dot=>u.
rewrite mulmxBr !mul_mx_scalar -scalerBl -scalemxAl linearZ/= nnegrE.
apply mulr_ge0. by rewrite subr_ge0. by rewrite formV_tr_ge0.
Qed.

Lemma geso0_cpP (E : 'SO(U,V)) :
  ((0 : 'SO) ⊑ E) <-> (E \is cpmap).
Proof.
by rewrite leso_mx linear0 le_lownerE subr0; 
  split=>[?|/cpmapP//]; apply/cpmapP.
Qed.

Lemma geso0_cpE (E : 'SO(U,V)) :
  ((0 : 'SO) ⊑ E) = (E \is cpmap).
Proof. apply/eqb_iff; exact: geso0_cpP. Qed.

Lemma lecpP (E F : 'CP(U,V)) :
  reflect (exists W : 'CP(U,V), (W : 'SO) + E = F) ((E : 'SO) ⊑ F).
Proof.
rewrite -subv_ge0 geso0_cpE; apply/(iffP idP)=>[P1|[W PW]].
by exists (CPMap_Build P1); rewrite /= addrNK.
by rewrite -PW addrK/= is_cpmap.
Qed.

Lemma leqoP (E F : 'QO(U,V)) :
  reflect (exists W : 'QO(U,V), (W : 'SO) + E = F) (E ⊑ F).
Proof.
rewrite leEsub/= -subv_ge0 geso0_cpE; apply/(iffP idP)=>[P1|[W PW]].
have P2: (F : 'SO) - (E : 'SO) \is cptn.
  apply/cptnP; split=>//; apply/tnmapP=>x.
  rewrite !soE linearB/= -[\Tr x]subr0 lerB//.
  by apply/tnmapP/cptn_tnmap/is_cptn.
  by apply/psdlf_trlf/cp_psdP/is_psdlf.
by exists (QOperation_Build P2); rewrite /= addrNK.
by rewrite -PW addrK is_cpmap.
Qed.

Lemma leso_preserve_order (E F : 'SO(U,V)) x:
  E ⊑ F -> (0 : 'End(U)) ⊑ x -> E x ⊑ F x.
Proof.
rewrite -subv_ge0=>/geso0_cpP P1.
rewrite -[in X in _ -> X]subv_ge0 -opp_soE -add_soE (CPMap_BuildE P1).
exact: cp_ge0.
Qed.

(* choinorm *)
Lemma choinorm_ge0_add (f g : 'SO(U,V)) : 
  ((0 : 'SO) ⊑ f) -> ((0 : 'SO) ⊑ g) ->
  choinorm (f + g) = choinorm f + choinorm g.
Proof.
rewrite !leso_mx /Order.le/=/MxLownerOrder.lownerle linear0 !subr0=>Pf Pg.
rewrite/choinorm linearD/= !psdmx_trnorm ?linearD/= ?mulrDl.
apply: psdmxD; [apply: Pf | apply: Pg]. apply: Pf. apply: Pg. by [].
Qed.

Lemma choinorm_cp_add (f g : 'CP(U,V)) : 
  choinorm ((f : 'SO) + g) = choinorm f + choinorm g.
Proof. apply: choinorm_ge0_add; apply/geso0_cpP/is_cpmap. Qed.

Lemma choinorm_ge0_sum (I : Type) (r : seq I) (P : pred I) (F : I -> 'SO(U,V)) :
  (forall i, (0 : 'SO) ⊑ F i) ->
  choinorm (\sum_(i <- r | P i) (F i : 'SO)) = \sum_(i <- r | P i) choinorm (F i).
Proof.
move=>PF.
elim: r=>[|a r IH]; first by rewrite !big_nil normv0.
rewrite !big_cons; case: (P a)=>//; rewrite choinorm_ge0_add ?IH//.
apply: sumv_ge0=>i _. apply: PF. 
Qed.

Lemma choinorm_cp_sum (I : Type) (r : seq I) (P : pred I) (F : I -> 'CP(U,V)) :
  choinorm (\sum_(i <- r | P i) (F i : 'SO)) = \sum_(i <- r | P i) choinorm (F i).
Proof. by apply: choinorm_ge0_sum=>i; apply/geso0_cpP/is_cpmap. Qed.

Lemma choinorm_ge0_le (f g : 'SO(U,V)) : ((0 : 'SO) ⊑ f) ->
  f ⊑ g -> choinorm f <= choinorm g.
Proof.
by move=>P1; rewrite -subv_ge0=>P2; 
  rewrite -[g](addrNK f) choinorm_ge0_add// lerDr normv_ge0.
Qed.

Lemma choinorm_qcP (f : 'SO(U,V)) : f \is cptp -> choinorm f = 1.
Proof.
move=>P; rewrite/choinorm psdmx_trnorm; first by apply: cpmapP; apply/cptp_cpmap.
rewrite tr_ptrace2; move: P=>/cptpP[] _ /eqP->; rewrite mxtrace1 mulfV//.
apply/lt0r_neq0/dim_proper_gt0.
Qed.

Lemma choinorm_qoP (f : 'SO(U,V)) : f \is cptn -> choinorm f <= 1.
Proof.
move=>P; rewrite/choinorm psdmx_trnorm; first by apply: cpmapP; apply/cptn_cpmap.
rewrite tr_ptrace2; move: P=>/cptnP[] _ /le_lownerE_psdtr/(_ _ (form_psd 1%:M)).
by rewrite mul1mx !adjmx1 !mulmx1 mxtrace1 ler_pdivrMr ?mul1r// dim_proper_gt0.
Qed.

Lemma choinorm_qc (f : 'QC(U,V)) : choinorm f = 1.
Proof. apply/choinorm_qcP/is_cptp. Qed.

Lemma choinorm_qo (f : 'QO(U,V)) : choinorm f <= 1.
Proof. apply/choinorm_qoP/is_cptn. Qed.

(* itnorm *)
Lemma itnorm_qc (f : 'QC(U,V)) : `| f : 'SO | = 1.
Proof.
apply: itnorm_def_ns; first by apply/is_cpmap.
move=>/=u Pu; rewrite psd_trfnorm; first by apply/cp_psdP/is_psdlf.
by rewrite qc_trlfE outp_trlf dotp_norm Pu expr1n.
exists [> chs_default_vect ; chs_default_vect <]; split.
by rewrite -normr_eq0 outp_ns_norm oner_neq0.
rewrite psd_trfnorm; first by apply/cp_psdP/is_psdlf.
by rewrite qc_trlfE outp_trlf ns_dot outp_ns_norm mulr1.
Qed.

Lemma itnorm_qcP (f : 'SO(U,V)) : f \is cptp ->  `| f | = 1.
Proof. by move=>Pf; move: (itnorm_qc (QChannel_Build Pf)). Qed.

Lemma itnorm_ge0_le (f g : 'SO(U,V)) : ((0 : 'SO) ⊑ f) ->
  f ⊑ g -> `| f | <= `| g |.
Proof.
move=>P1 P2; rewrite itnorm_ler_psd=>[|x Px|//]. by rewrite -geso0_cpE.
apply/(le_trans (y := `|g x|)); last by apply itnormP.
apply/trfnorm_ler. rewrite -psdlfE. move: P1=>/geso0_cpP Pf.
by move: (cp_psdP (CPMap_Build Pf) Px).
by apply/leso_preserve_order=>[//|]; rewrite -psdlfE.
Qed.

Lemma itnorm_qo (f : 'QO(U,V)) : `| f : 'SO | <= 1.
Proof.
apply: itnorm_ler_ns=>[|u Pu]; first by apply/is_cpmap.
rewrite psd_trfnorm. apply/cp_psdP/is_psdlf.
apply: (le_trans (qo_trlfE _ _)); first by apply/is_psdlf.
by rewrite outp_trlf dotp_norm Pu expr1n.
Qed.

Lemma itnorm_qoP (f : 'SO(U,V)) : f \is cptn -> `| f | <= 1.
Proof. by move=>Pf; move: (itnorm_qo (QOperation_Build Pf)). Qed.

Lemma itnorm_ge0_le1P (f : 'SO(U,V)) : ((0 : 'SO) ⊑ f) ->
  `|f : 'SO| <= 1 -> f \is cptn.
Proof.
move=>/geso0_cpP P1 P2; suff: ((CPMap_Build P1 : 'SO) \is cptn) by [].
apply/cp_isqoP=>x Px; rewrite -!psd_trfnorm=>[|//|]; first by apply/cp_psdP.
apply/(le_trans (itnormP _ _))/ler_piMl=>//.
Qed.

End KrausOp.

Lemma dqo_obsP U V (E : 'DQO(U,V)) x : x \is obslf -> E x \is obslf.
Proof.
move=>/obslf_lefP[] P1 P2; apply/obslf_lefP; split.
by apply/cp_ge0. by apply/(le_trans _ (dqo1_le1 E))/cp_preserve_order.
Qed.

Section QOConstruct.
Implicit Type (U V W : chsType).

(* abortso is cp, qo *)
Lemma abortso_formE U V : (0 : 'SO) = formso (0 : 'Hom(U,V)).
Proof. by apply/superopP=>x; rewrite !soE !comp_lfun0l. Qed.
Lemma dualso0 U V : dualso (0: 'SO(U,V)) = 0.
Proof. by rewrite abortso_formE dualso_formso linear0 -abortso_formE. Qed.
Lemma abortso_qo U V : (0 : 'SO(U,V)) \is cptn.
Proof.
apply/cptnP; split. by rewrite abortso_formE is_cpmap.
by apply/tnmapP=>x; rewrite soE linear0 psdlf_trlf ?is_psdlf.
Qed.
HB.instance Definition _ U V := isQOperation.Build U V 0 (abortso_qo U V).
HB.instance Definition _ U V := QOperation.copy (abortso U V) (0 : 'SO(U,V)).
Lemma abortso_dualtn U V : (0 : 'SO(U,V))^*o \is tnmap.
Proof. by rewrite dualso0 is_tnmap. Qed.
HB.instance Definition _ U V := CPMap_isDTNMap.Build U V 0 (abortso_dualtn U V).
HB.instance Definition _ U V := DualQO.copy (abortso U V) (0 : 'SO(U,V)).

(* idso is cp, qo, qc *)
Lemma idso_formE U : \:1 = formso (\1 : 'End(U)).
Proof. by apply/superopP=>x; rewrite !soE adjf1 comp_lfun1l comp_lfun1r. Qed.
Lemma dualso1 U : dualso (\:1 : 'SO(U)) = \:1.
Proof. by rewrite idso_formE dualso_formso adjf1. Qed.
Lemma idso_qc U : (\:1 : 'SO(U)) \is cptp.
Proof.
apply/cptpP; split. by rewrite idso_formE is_cpmap.
by apply/tpmapP=>x; rewrite soE.
Qed.
HB.instance Definition _ U := isQChannel.Build U U \:1 (idso_qc U).
Lemma idso_qu U : (\:1 : 'SO(U))^*o \is tpmap.
Proof. by rewrite dualso1 is_tpmap. Qed.
HB.instance Definition _ U := CPMap_isQUnital.Build U U \:1 (idso_qu U).

(* unitaryso is cp, qo, qc *)
Definition unitaryso U (f: 'FU(U)) := formso f.
HB.instance Definition _ U (f: 'FU(U)) := QChannel.on (unitaryso f).
HB.instance Definition _ U (f: 'FU(U)) := QUnital.on (unitaryso f).

Definition unitarysoE := formsoE.
Lemma unitaryso1 (U : chsType) : unitaryso (\1 : 'End(U)) = \:1.
Proof. by apply/superopP=>x; rewrite formsoE/= comp_lfun1l adjf1 comp_lfun1r soE. Qed.

Lemma dualso_unitary U (f : 'FU(U)) : 
  dualso (unitaryso f) = unitaryso (f^A).
Proof. by rewrite /unitaryso dualso_formso. Qed.

(* initialso is cp, qo, qc *)
Definition initialso U (v : U) := krausso (fun i=>[> v ; eb i : U <]).
HB.instance Definition _ U (v : U) := CPMap.on (initialso v).
Lemma initialso_tn U (v : 'PS(U)) : (@initialso U v) \is tnmap.
Proof.
apply/tnmapP=>x; rewrite soE linear_sum/=.
under eq_bigr do rewrite lftraceC comp_lfunA adj_outp outp_comp linearZl/= linearZ/=.
by rewrite -mulr_sumr -linear_sum/= -linear_suml/= sumonb_out 
  comp_lfun1l ler_piMl// ?ps_dot// psdf_trlf.
Qed.
HB.instance Definition _ U (v : 'PS(U)) := CPMap_isTNMap.Build U U 
  (initialso v) (initialso_tn v).
Lemma initialso_qc U (v : 'NS(U)) : (@initialso U v) \is tpmap.
Proof.
apply/tpmapP=>x; rewrite soE linear_sum/=. 
under eq_bigr do rewrite lftraceC comp_lfunA adj_outp outp_comp ns_dot scale1r.
by rewrite -linear_sum/= -linear_suml/= sumonb_out comp_lfun1l.
Qed.
HB.instance Definition _ U (v : 'NS(U)) := QOperation_isTPMap.Build U U 
  (initialso v) (initialso_qc v).

Lemma initialsoE U (v : U) x : initialso v x = \Tr x *: [> v ; v <].
Proof.
rewrite soE (onb_trlf eb x)/= scaler_suml; apply eq_bigr=>i _.
by rewrite adj_outp -comp_lfunA outp_compr outp_comp.
Qed.

Lemma initialso_onb U (v : U) (F : finType) (onb : 'ONB(F;U)) :
  krausso (fun i=>[> v ; onb i <]) = initialso v.
Proof.
apply/superopP=>x; rewrite soE initialsoE (onb_trlf onb x)/= scaler_suml.
by apply eq_bigr=>i _; rewrite adj_outp -comp_lfunA outp_compr outp_comp.
Qed.

Lemma dualso_initialE U (v : U) (x : 'End(U)) :
  dualso (initialso v) x = [<v : U ; x (v : U)>] *: \1.
Proof.
rewrite /initialso dualso_krausE.
under eq_bigr do rewrite adj_outp outp_compl outp_comp adj_dotEl.
by rewrite -linear_sum/= sumonb_out.
Qed.

(* ifso, cp - cp, qo - qo, qc - qc *)
Lemma ifso_cp U V W (F : finType) (f : F -> 'Hom(U, V)) (br : F -> 'CP(V, W)) :
  ifso f br \is cpmap.
Proof.
have ->: (fun x : F => br x : 'SO) = (fun x : F => krausso (krausop (br x))).
apply/funext=>i; exact: krausopE. 
by rewrite ifso_krausso is_cpmap.
Qed.
HB.instance Definition _ U V W (F : finType) f (br : F -> 'CP(V,W)) := 
  isCPMap.Build U W (ifso f br) (@ifso_cp U V W F f br).

Lemma ifso_tn U V W (F : finType) (f : 'TN(F;U,V)) (br : F -> 'QO(V, W)) :
  ifso f br \is tnmap.
Proof.
apply/tnmapP=>x; apply: (le_trans _ (tn_trlf_psd f (is_psdlf x))).
rewrite ifsoE linear_sum/= ler_sum// =>i _.
by apply/qo_trlfE; move: (is_psdlf x); rewrite !psdlfE; exact: gef0_formfV.
Qed.
HB.instance Definition _ U V W (F : finType) (f : 'TN(F;U,V)) (br : F -> 'QO(V, W)) := 
  CPMap_isTNMap.Build U W (ifso f br) (@ifso_tn U V W F f br).

Lemma ifso_tp U V W (F : finType) (f : 'QM(F;U,V)) (br : F -> 'QC(V, W)) :
  ifso f br \is tpmap.
Proof.
apply/tpmapP=>x; rewrite -[RHS](tp_trlf f) ifsoE linear_sum/=.
apply eq_bigr =>i _; apply/qc_trlfE.
Qed.
HB.instance Definition _ U V W (F : finType) (f : 'QM(F;U,V)) (br : F -> 'QC(V, W)) := 
  QOperation_isTPMap.Build U W (ifso f br) (@ifso_tp U V W F f br).

Lemma dualso_comp U V W (E : 'SO(U,V)) (F : 'SO(W,U)) :
  dualso (E :o F) = dualso F :o dualso E.
Proof.
apply/superopP=>A; apply/eqP/trlf_introl=>x.
by rewrite comp_soE -!dualso_trlfE comp_soE.
Qed.

Lemma dualso_compr U V W (E : 'SO(U,V)) (F : 'SO(V,W)) :
  dualso (E o: F) = dualso F o: dualso E.
Proof.
apply/superopP=>A; apply/eqP/trlf_introl=>x.
by rewrite comp_sorE -!dualso_trlfE comp_sorE.
Qed.

(* comp_so, cp - cp, qo - qo, qc - qc *)
Lemma comp_so_cp U V W (E: 'CP(U,V)) (F: 'CP(W,U)) :
  E :o F \is cpmap.
Proof. by rewrite krausopE (krausopE F) comp_krausso is_cpmap. Qed.
HB.instance Definition _ U V W (E: 'CP(U,V)) (F: 'CP(W,U)) := 
  isCPMap.Build W V (E :o F) (comp_so_cp E F).
Lemma comp_so_tn U V W (E: 'QO(U,V)) (F: 'QO(W,U)) :
  E :o F \is tnmap.
Proof.
apply/tnmapP=>x; apply: (le_trans _ (qo_trlfE F (is_psdlf x))).
by rewrite comp_soE qo_trlfE// cp_psdP ?is_psdlf.
Qed.
HB.instance Definition _ U V W (E: 'QO(U,V)) (F: 'QO(W,U)) := 
  CPMap_isTNMap.Build W V (E :o F) (comp_so_tn E F).
Lemma comp_so_tp U V W (E: 'QC(U,V)) (F: 'QC(W,U)) :
  E :o F \is tpmap.
Proof. by apply/tpmapP=>x; rewrite comp_soE !qc_trlfE. Qed.
HB.instance Definition _ U V W (E: 'QC(U,V)) (F: 'QC(W,U)) := 
  QOperation_isTPMap.Build W V (E :o F) (comp_so_tp E F).
Lemma comp_so_dualtn U V W (E: 'DQO(U,V)) (F: 'DQO(W,U)) :
  (E :o F)^*o \is tnmap.
Proof. by rewrite dualso_comp is_tnmap. Qed.
HB.instance Definition _ U V W (E: 'DQO(U,V)) (F: 'DQO(W,U)) := 
  CPMap_isDTNMap.Build W V (E :o F) (comp_so_dualtn E F).
Lemma comp_so_dualtp U V W (E: 'QU(U,V)) (F: 'QU(W,U)) :
  (E :o F)^*o \is tpmap.
Proof. by rewrite dualso_comp is_tpmap. Qed.
HB.instance Definition _ U V W (E: 'QU(U,V)) (F: 'QU(W,U)) := 
  DualQO_isUnitalMap.Build W V (E :o F) (comp_so_dualtp E F).

Lemma comp_sor_cp U V W (E: 'CP(U,V)) (F: 'CP(V,W)) :
  E o: F \is cpmap.
Proof. by rewrite comp_soErl is_cpmap. Qed.
HB.instance Definition _ U V W (E: 'CP(U,V)) (F: 'CP(V,W)) := 
  isCPMap.Build U W (E o: F) (comp_sor_cp E F).
Lemma comp_sor_tn U V W (E: 'QO(U,V)) (F: 'QO(V,W)) :
  E o: F \is tnmap.
Proof. by rewrite comp_soErl is_tnmap. Qed.
HB.instance Definition _ U V W (E: 'QO(U,V)) (F: 'QO(V,W)) := 
  CPMap_isTNMap.Build U W (E o: F) (comp_sor_tn E F).
Lemma comp_sor_tp U V W (E: 'QC(U,V)) (F: 'QC(V,W)) :
  E o: F \is tpmap.
Proof. by rewrite comp_soErl is_tpmap. Qed.
HB.instance Definition _ U V W (E: 'QC(U,V)) (F: 'QC(V,W)) := 
  QOperation_isTPMap.Build U W (E o: F) (comp_sor_tp E F).
Lemma comp_sor_dualtn U V W (E: 'DQO(U,V)) (F: 'DQO(V,W)) :
  (E o: F)^*o \is tnmap.
Proof. by rewrite dualso_compr is_tnmap. Qed.
HB.instance Definition _ U V W (E: 'DQO(U,V)) (F: 'DQO(V,W)) := 
  CPMap_isDTNMap.Build U W (E o: F) (comp_sor_dualtn E F).
Lemma comp_sor_dualtp U V W (E: 'QU(U,V)) (F: 'QU(V,W)) :
  (E o: F)^*o \is tpmap.
Proof. by rewrite dualso_compr is_tpmap. Qed.
HB.instance Definition _ U V W (E: 'QU(U,V)) (F: 'QU(V,W)) := 
  DualQO_isUnitalMap.Build U W (E o: F) (comp_sor_dualtp E F).

Lemma comp_so_ge0 (U V W : chsType) (h : 'SO(U,V)) (g : 'SO(W,U)) :
  0 <= h -> 0 <= g -> 0 <= h :o g.
Proof. 
by rewrite !geso0_cpE=>Ph Pg; rewrite (CPMap_BuildE Ph) (CPMap_BuildE Pg) is_cpmap.
Qed.

Lemma leso_comp2 (U V W : chsType) (f1 f2 : 'SO(U,V)) (g1 g2 : 'SO(W,U)) :
  0 <= f1 -> 0 <= g1 -> f1 <= f2 -> g1 <= g2 -> f1 :o g1 <= f2 :o g2.
Proof.
move=>Pf1 Pg1 Pf12 Pg12.
apply: (le_trans (y := f1 :o g2)); rewrite -subv_ge0 -?linearBr -?linearBl/=; apply: comp_so_ge0.
apply: Pf1. 1,2: by rewrite subv_ge0. apply: (le_trans Pg1 Pg12).
Qed.

Lemma leso_comp2l (U V W : chsType) (f : 'SO(U,V)) (g1 g2 : 'SO(W,U)) :
  0 <= f -> g1 <= g2 -> f :o g1 <= f :o g2.
Proof. by move=>Pf Pg; rewrite -subv_ge0 -linearBr/= comp_so_ge0 ?subv_ge0. Qed.

Lemma leso_comp2r (U V W : chsType) (f1 f2 : 'SO(U,V)) (g : 'SO(W,U)) :
  f1 <= f2 -> 0 <= g -> f1 :o g <= f2 :o g.
Proof. by move=>Pf Pg; rewrite -subv_ge0 -linearBl/= comp_so_ge0 ?subv_ge0. Qed.

(* part of tn / qm *)
Definition elemso U V (F : finType) (f : F -> 'Hom(U,V)) (i : F) := formso (f i).
Lemma elemso_qo U V (F : finType) (f : 'TN(F;U,V)) i : (@elemso U V F f i) \is cptn.
Proof.
apply/cptnP; split. apply/is_cpmap.
apply/tnmapP=>x; rewrite soE lftraceC comp_lfunA -{2}(comp_lfun1l x).
apply/lef_psdtr; last by apply is_psdlf.
apply: (le_trans _ (is_trnincr (s := f))); rewrite (bigD1 i)//= levDl sumv_ge0// =>j _.
by rewrite form_gef0.
Qed.
HB.instance Definition _ U V (F : finType) (f : 'TN(F;U,V)) i := 
  isQOperation.Build U V (elemso f i) (elemso_qo f i).

Lemma elemso_sum U V (F : finType) (f : F -> 'Hom(U,V)) :
  \sum_i (elemso f i) = krausso f.
Proof. by apply/superopP=>x; rewrite !soE; under eq_bigr do rewrite soE. Qed.

Lemma ifso_elemE U V W (F : finType) (f : F -> 'Hom(U,V)) (br : F -> 'SO(V, W)) x:
  ifso f br x = \sum_i ((br i :o elemso f i) x).
Proof. by under eq_bigr do rewrite comp_soE soE; rewrite ifsoE. Qed.

Lemma ifso_elem U V W (F : finType) (f : F -> 'Hom(U,V)) (br : F -> 'SO(V, W)):
  ifso f br = \sum_i (br i :o elemso f i).
Proof. by apply/superopP=>x; rewrite !soE ifso_elemE. Qed.

Lemma elemso_trlf U V (F : finType) (f : 'QM(F;U,V)) x :
  \sum_i \Tr ((elemso f i) x) = \Tr x.
Proof. under eq_bigr do rewrite soE; exact: qm_trlf. Qed.

Lemma dualso_if U V W (F : finType) (f : F -> 'Hom(U,V)) (br : F -> 'SO(V, W)) :
  dualso (ifso f br) = \sum_i dualso (br i :o (elemso f i)).
Proof. by rewrite ifso_elem linear_sum. Qed.

Definition dualqm U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) :=
  \sum_i ((f i)^A \o (O i) \o (f i)).

Lemma dualqmE U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) :
  dualqm f O = \sum_i ((elemso f i)^*o (O i)).
Proof. by under eq_bigr do rewrite dualso_formE. Qed.

Lemma dualqm_trlfE U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) (x : 'End(U)) :
  \sum_i \Tr ((elemso f i) x \o O i) = \Tr (x \o dualqm f O).
Proof.
rewrite /dualqm linear_sumr linear_sum. apply eq_bigr=>i _.
by rewrite dualso_trlfE dualso_formE.
Qed.

Lemma dualqm_trlfEV U V (F : finType) (f : F -> 'Hom(U,V)) (O : F -> 'End(V)) (x : 'End(U)) :
  \sum_i \Tr (O i \o (elemso f i) x) = \Tr (dualqm f O \o x).
Proof. by under eq_bigr do rewrite lftraceC; rewrite dualqm_trlfE lftraceC. Qed.

Lemma bool_index : index_enum bool = [:: true; false].
Proof. by rewrite /index_enum !unlock/=. Qed.

Lemma ifso_boolE U V W (M : bool -> 'Hom(U,V))
  (br : forall (b : bool), 'SO(V,W)) b x :
  ifso M br x = (br b :o elemso M b) x + (br (~~b) :o elemso M (~~b)) x.
Proof.
rewrite ifso_elemE bool_index unlock/= /reducebig/= addr0.
by case: b=>[//|]; rewrite addrC.
Qed.
Global Arguments ifso_boolE [U V W M br].

Lemma ifso_bool U V W (M : bool -> 'Hom(U,V))
  (br : forall (b : bool), 'SO(V,W)) b :
  ifso M br = (br b :o elemso M b) + (br (~~b) :o elemso M (~~b)).
Proof. by apply/superopP=>x; rewrite soE -ifso_boolE. Qed.
Global Arguments ifso_bool [U V W M br].

Lemma abortso_eq0 U V : (@abortso U V) = 0.
Proof. by []. Qed.

Lemma addso_cp U V (E F : 'CP(U,V)) : (E : 'SO) + F \is cpmap.
Proof. by rewrite krausopE (krausopE F) addso_krausso is_cpmap. Qed.
HB.instance Definition _ U V (E F : 'CP(U,V)) := isCPMap.Build U V 
  ((E : 'SO) + F) (addso_cp E F).

Lemma sumso_cp U V F (r : seq F) (P : pred F) (f : F -> 'CP(U,V)) :
  \sum_(i <- r | P i) (f i : 'SO) \is cpmap.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cpmap.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (CPMap_BuildE IH) is_cpmap.
Qed.
HB.instance Definition _ U V F (r : seq F) (P : pred F) (f : F -> 'CP(U,V)) := 
  isCPMap.Build U V (\sum_(i <- r | P i) (f i : 'SO)) (sumso_cp r P f).

(* since the projection is bigop, and we already define the sum, the 
   canonical will be ignored, i.e., HB instance won't work *)
Lemma complso_cp U F (r : seq F) (P : pred F) (f : F -> 'CP(U)) :
  \compl_(i <- r | P i) (f i) \is cpmap.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cpmap.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (CPMap_BuildE IH) is_cpmap.
Qed.
Definition complso_cpE U F r P f := CPMap_BuildE (@complso_cp U F r P f).

Lemma complso_qo U F (r : seq F) (P : pred F) (f : F -> 'QO(U)) :
  \compl_(i <- r | P i) (f i) \is cptn.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptn.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (QOperation_BuildE IH) is_cptn.
Qed.
Definition complso_qoE U F r P f := QOperation_Build (@complso_qo U F r P f).

Lemma complso_qc U F (r : seq F) (P : pred F) (f : F -> 'QC(U)) :
  \compl_(i <- r | P i) (f i) \is cptp.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptp.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (QChannel_BuildE IH) is_cptp.
Qed.
Definition complso_qcE U F r P f := QChannel_Build (@complso_qc U F r P f).

Lemma complso_dqo U F (r : seq F) (P : pred F) (f : F -> 'DQO(U)) :
  (\compl_(i <- r | P i) (f i))^*o \is cptn.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptn.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (DualQO_BuildE IH) is_cptn.
Qed.
Definition complso_dqoE U F r P f := DualQO_Build (@complso_dqo U F r P f).

Lemma complso_qu U F (r : seq F) (P : pred F) (f : F -> 'QU(U)) :
  (\compl_(i <- r | P i) (f i))^*o \is cptp.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptp.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (QUnital_BuildE IH) is_cptp.
Qed.
Definition complso_quE U F r P f := QUnital_Build (@complso_qu U F r P f).

Lemma comprso_cp U F (r : seq F) (P : pred F) (f : F -> 'CP(U)) :
  \compr_(i <- r | P i) (f i) \is cpmap.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cpmap.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (CPMap_BuildE IH) is_cpmap.
Qed.
Definition comprso_cpE U F r P f := CPMap_BuildE (@comprso_cp U F r P f).

Lemma comprso_qo U F (r : seq F) (P : pred F) (f : F -> 'QO(U)) :
  \compr_(i <- r | P i) (f i) \is cptn.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptn.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (QOperation_BuildE IH) is_cptn.
Qed.
Definition comprso_qoE U F r P f := QOperation_BuildE (@comprso_qo U F r P f).
(* qo is ok, but cp won't work *)
HB.instance Definition _ U F (r : seq F) (P : pred F) (f : F -> 'QO(U)) := 
  isQOperation.Build U U (\compr_(i <- r | P i) (f i)) (comprso_qo r P f).

Lemma comprso_qc U F (r : seq F) (P : pred F) (f : F -> 'QC(U)) :
  \compr_(i <- r | P i) (f i) \is cptp.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptp.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (QChannel_BuildE IH) is_cptp.
Qed.
Definition comprso_qcE U F r P f := QChannel_BuildE (@comprso_qc U F r P f).
(* qc is ok, but cp won't work *)
HB.instance Definition _ U F (r : seq F) (P : pred F) (f : F -> 'QC(U)) := 
  QOperation_isTPMap.Build U U (\compr_(i <- r | P i) (f i)) (cptp_tpmap (comprso_qc r P f)).

Lemma comprso_dqo U F (r : seq F) (P : pred F) (f : F -> 'DQO(U)) :
  (\compr_(i <- r | P i) (f i))^*o \is cptn.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptn.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (DualQO_BuildE IH) is_cptn.
Qed.
Definition comprso_dqoE U F r P f := DualQO_Build (@comprso_dqo U F r P f).
HB.instance Definition _ U F (r : seq F) (P : pred F) (f : F -> 'DQO(U)) := 
  isDualQO.Build U U (\compr_(i <- r | P i) (f i)) (comprso_dqo r P f).

Lemma comprso_qu U F (r : seq F) (P : pred F) (f : F -> 'QU(U)) :
  (\compr_(i <- r | P i) (f i))^*o \is cptp.
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil is_cptp.
by rewrite big_cons; case: (P x)=>[|//]; rewrite (QUnital_BuildE IH) is_cptp.
Qed.
Definition comprso_quE U F r P f := QUnital_Build (@comprso_qu U F r P f).
HB.instance Definition _ U F (r : seq F) (P : pred F) (f : F -> 'QU(U)) := 
  DualQO_isUnitalMap.Build U U (\compr_(i <- r | P i) (f i)) (cptp_tpmap (comprso_qu r P f)).

End QOConstruct.

Section leso_extra.
Implicit Type (U V : chsType).

Lemma leso01 U : (0 : 'SO) ⊑ (\:1 : 'SO(U)).
Proof. by apply/cp_geso0. Qed.
Lemma qc_neq0 U V (E : 'QC(U,V)) : (E : 'SO) != 0.
Proof.
apply/eqP=>P; move: P=>/(f_equal (@dualso _ _))/superopP/(_ \1)/eqP.
by rewrite dualso0 qu1_eq1 soE oner_eq0.
Qed.
Lemma qc_gt0 U V (E : 'QC(U,V)) : (0 : 'SO) ⊏ E.
Proof. by rewrite lt_def qc_neq0 cp_geso0. Qed.
Lemma idso_neq0 U : (\:1 : 'SO(U)) != 0. Proof. exact: qc_neq0. Qed.
Lemma ltso01 U : (0 : 'SO(U)) ⊏ \:1. Proof. exact: qc_gt0. Qed.

Lemma so_neq0P U V (E : 'SO(U,V)) : 
  reflect (exists f, E f != 0) (E != 0).
Proof.
apply/(iffP negP); rewrite not_existsP; apply contra_not.
by move=>P; apply/eqP/superopP=>u; move: (P u)=>/negP; rewrite negbK soE=>/eqP.
by move=>/eqP-> x; rewrite soE/= eqxx.
Qed.

Lemma psdlf_decomp U (f : 'End(U)): f \is psdlf -> 
  exists (v : 'I_(dim U) -> U), f = \sum_i [> v i ; v i <].
Proof.
rewrite qualifE=>/diag_decomp_absorb.
set v := fun k => sqrtC (eigenval (h2mx f) k) *: eigenvec (h2mx f) k.
rewrite/==>P. exists (fun k=> c2h (v k)).
apply/h2mx_inj; rewrite P linear_sum.
by apply eq_bigr=>i _; rewrite outp.unlock/= mx2hK !c2hK.
Qed.

Lemma ge0_krausE U V (E : 'SO(U,V)) x : (0:'SO) ⊑ E ->
  E x = \sum_i ((krausop E i) \o x \o (krausop E i)^A)%VF.
Proof. by move=>/geso0_cpP P; move: (krausE (CPMap_Build P) x). Qed.

Lemma gtf0_trlfP U (x : 'End(U)) :
  reflect (0%:VF ⊑ x /\ \Tr x > 0) (0%:VF ⊏ x).
Proof.
rewrite [_ ⊏ x]lt_def; apply/(iffP andP)=>[[P1 P2]|[P1 P2]]; split=>//; last first.
move: P2; apply/contraTN=>/eqP->; by rewrite linear0 ltxx.
rewrite lt_def psdlf_trlf ?psdlfE// andbT; move: P1; apply/contraNN=>/eqP.
rewrite lftrace_baseE=>P4. move: (gef0_formV P2)=>[g Pg].
have P3 : forall i, true -> (fun i=>[< eb i; x (eb i) >]) i = 0.
by apply: psumr_eq0P=>// i _; rewrite Pg lfunE adj_dotEr/= ge0_dotp.
suff: g = 0 by rewrite Pg=>->; rewrite comp_lfun0r.
apply/(intro_onb eb)=>i/=; rewrite lfunE/=; apply/eqP.
by rewrite -dotp_eq0 -adj_dotEr -comp_lfunE -Pg; apply/eqP/P3.
Qed.

End leso_extra.

Section QOQMDenObs.
Implicit Type (U V: chsType).

Lemma qoge0 U V (E: 'QO(U,V)) : ((0 : 'SO) : 'QO) ⊑ E.
Proof. by rewrite leEsub/= cp_geso0. Qed.

Lemma cp_psdlf U V (E : 'CP(U,V)) (x : 'F+(U)) : E x \is psdlf.
Proof. apply/cp_psdP/is_psdlf. Qed.
HB.instance Definition _ U V (E : 'CP(U,V)) (x : 'F+(U)) := 
  isPsdLf.Build V (E x) (cp_psdlf E x).

Lemma dqo_obslf U V (E : 'DQO(U,V)) (O : 'FO(U)) : E O \is obslf.
Proof. by apply/dqo_obsP/is_obslf. Qed.
Canonical dqo_obsfType U V E O := ObsLf_Build (@dqo_obslf U V E O).

Lemma qo_denlf U V (E : 'QO(U,V)) (x : 'FD(U)) : E x \is denlf.
Proof.
apply/denlfP; split. apply/cp_psdP/denlf_psd/is_denlf.
apply: (le_trans _ (denf_trlf x)); apply/qo_trlfE/denlf_psd/is_denlf.
Qed.
Canonical qo_denfType U V E x := DenLf_Build (@qo_denlf U V E x).

Lemma qc_den1lf U V (E : 'QC(U,V)) (x : 'FD1(U)) : E x \is den1lf.
Proof.
apply/den1lfP; split. apply: cp_psdlf.
by rewrite qc_trlfE den1lf_trlf// is_den1lf.
Qed.
Canonical qc_den1fType U V E x := Den1Lf_Build (@qc_den1lf U V E x).

Lemma dualqm_obslf U V (F: finType) (M : 'TN(F;U,V)) (Of : F -> 'FO(V)) :
  dualqm M Of \is obslf.
Proof.
rewrite obslfE. apply/andP. split.
by rewrite sumv_ge0// =>i _; rewrite gef0_formf// obsf_ge0.
apply: (le_trans _ (dqo1_le1 (krausso M)^*o)).
rewrite dualqmE/= -elemso_sum linear_sum/= soE lev_sum// =>i _.
apply/cp_preserve_order/obsf_le1.
Qed.
Canonical dualqm_obsfType U V F M O := ObsLf_Build (@dualqm_obslf U V F M O).

Lemma elem_sum_trlfE U V (F: finType) (M : 'QM(F;U,V)) x :
  \sum_i \Tr (elemso M i x) = \Tr x.
Proof. by rewrite -linear_sum/= -sum_soE elemso_sum qc_trlfE. Qed.

Lemma qo_ubound (U V: chsType) (E: 'QO(U,V)) : 
  (E : 'SO) ⊑ (choi2so (dim U)%:R%:M)%VF.
Proof.
move: (is_cptn E)=>/cptnP[P1 P2].
rewrite /= leso_mx choi2soK; apply (le_trans (lemx_psd_ub P1)).
apply/scalemx_le; rewrite tr_ptrace2; move: P2=>/lemx_trace P2.
by apply (le_trans P2); rewrite mxtrace_scalar.
Qed.

End QOQMDenObs.

Module QOCPO.

Section QOCPOProof.
Local Close Scope lfun_scope.
Variable (U V: chsType).
Local Open Scope classical_set_scope.

Local Notation qosort := (@QOperation.sort U V).

Definition qolub (u : nat -> 'QO(U,V)) :=
  match limn (qosort \o u) \is cptn =P true with
  | ReflectT is_qo => QOperation_Build is_qo
  | _ => (0 : 'SO(U,V))
  end.

Lemma chainqomap (u: nat -> 'QO(U,V)) :
  chain u -> nondecreasing_seq (qosort \o u).
Proof. by move=>/chain_homo P m n Pmn; move: (P _ _ Pmn). Qed.

Lemma chainqo_lb (u : nat -> 'QO(U,V)) : lbounded_by (0:'SO(U,V)) (qosort \o u).
Proof. by move=>i/=; rewrite cp_geso0. Qed.

Lemma chainqo_ub (u : nat -> 'QO(U,V)) : 
  ubounded_by (choi2so (dim U)%:R%:M)%VF (qosort \o u).
Proof. move=>i/=; apply qo_ubound. Qed.

Lemma lim_qo (u : nat -> 'QO(U,V)) : 
  cvgn (qosort \o u) -> [set x : 'SO(U,V) | x \is cptn] (limn (qosort \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (qosort \o u) _ _ _ _)=>//.
apply closed_isqo. by apply: nearW=>x/=; apply is_cptn.
Qed.

Lemma chainqo_cvg : forall c : nat -> 'QO(U,V), chain c ->
  cvgn (qosort \o c).
Proof.
move=>c Pc. move: (chainqomap Pc) (chainqo_ub c)=>P1 P2.
by apply (vnondecreasing_is_cvgn P1 P2).
Qed.

Lemma qolub_lub : forall c : nat -> 'QO(U,V), chain c -> (forall i, c i ⊑ qolub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> qolub c ⊑ x).
Proof.
move=>c Pc. move: (chainqomap Pc) (chainqo_cvg Pc)=>P1 P3.
move: (nondecreasing_cvgn_lev P1 P3)=>P4.
rewrite /qolub; case: eqP=>P5; last by exfalso; apply P5; apply lim_qo.
split. by move=>i; rewrite leEsub/= P4.
move=>x Px. rewrite leEsub/=.
by apply: (@limn_lev _ _ _ (qosort x) _ P3)=>i; move: (Px i).
Qed.

Lemma qolub_ub : forall c : nat -> 'QO(U,V), chain c -> (forall i, c i ⊑ qolub c).
Proof. by move=>c /qolub_lub=>[[P1]]. Qed.

Lemma qolub_least : forall c : nat -> 'QO(U,V), 
  chain c -> forall x, (forall i, c i ⊑ x) -> qolub c ⊑ x.
Proof. by move=>c /qolub_lub=>[[_ ]]. Qed.

Definition qo_cpoMixin := isCpo.Build ring_display 'QO(U,V) 
  (@qoge0 U V) qolub_ub qolub_least.

End QOCPOProof.

Module Exports.

HB.instance Definition _ (U V : chsType) := (@qo_cpoMixin U V).

Lemma qolubE (U V : chsType) : forall c : nat -> 'QO(U,V), 
  chain c -> limn ((@QOperation.sort U V) \o c)%FUN = lub c.
Proof.
move=>c Pc. rewrite /lub/= /qolub. case: eqP=>//.
by move: (chainqo_cvg Pc)=>/lim_qo/= ->.
Qed.

End Exports.
End QOCPO.

Import QOCPO.Exports.

Fixpoint whileso_iter (U: chsType) (M: bool -> 'End(U)) (b : bool) (D: 'SO(U)) (n : nat) :=
  match n with
  | O => (0 : 'SO(U))
  | S n => ifso M (fun b' => if b' == b then (whileso_iter M b D n) :o D else \:1)
  end.

HB.lock Definition whileso (U: chsType) (M: bool -> 'End(U)) b (D: 'SO(U)) :=
  limn (whileso_iter M b D).

Section QOWhile.
Variable (U: chsType).
Local Open Scope lfun_scope.

Fixpoint whileso_incr (M: bool -> 'End(U)) (b : bool) (D: 'SO(U)) (n : nat) :=
  match n with
  | O => \:1
  | S n => (whileso_incr M b D n) :o (D :o (elemso M b)) 
  end.

Lemma whileso_incrED (M: bool -> 'End(U)) b (D: 'SO(U)) n :
  (whileso_incr M b D n.+1) = (whileso_incr M b D n) :o (D :o (elemso M b)).
Proof. by []. Qed.

Lemma whileso_incrE (M: bool -> 'End(U)) b (D: 'SO(U)) n :
  (whileso_incr M b D n.+1) = (D :o (elemso M b)) :o (whileso_incr M b D n).
Proof.
elim: n=>[|n IH]. by rewrite /= comp_so1l comp_so1r.
by rewrite whileso_incrED {1}IH whileso_incrED !comp_soA.
Qed.

Lemma neqb (b : bool) : ~~ b == b = false.
Proof. by case: b. Qed.

Lemma whileso_iter_incrEx (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) x :
  whileso_iter M b D n x = (elemso M (~~b)) (\sum_(i < n) (whileso_incr M b D i x)).
Proof.
elim: n x=>[x|n IH x]; first by rewrite big_ord0 linear0 /= soE.
rewrite (ifso_boolE b) eqxx neqb -/whileso_iter !comp_soE soE big_ord_recl /= IH.
rewrite -linearD/= soE addrC. do 2 f_equal. 
apply eq_bigr=>i _. by rewrite !comp_soE.
Qed.

Lemma whileso_iter_incrE (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) :
  whileso_iter M b D n = (elemso M (~~b)) :o (\sum_(i < n) (whileso_incr M b D i)).
Proof. by apply/superopP=>x; rewrite soE sum_soE whileso_iter_incrEx. Qed.

Lemma whileso_iterEx (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) x :
  whileso_iter M b D n.+1 x = whileso_iter M b D n x + 
    ((elemso M (~~b)) :o (whileso_incr M b D n)) x.
Proof. by rewrite !whileso_iter_incrEx big_ord_recr/= linearD comp_soE. Qed.

Lemma whileso_iterE (M: bool -> 'End(U)) b (D: 'SO(U)) (n: nat) :
  whileso_iter M b D n.+1 = whileso_iter M b D n + 
    ((elemso M (~~b)) :o (whileso_incr M b D n)).
Proof. by apply/superopP=>x; rewrite soE whileso_iterEx. Qed.

Lemma whilso_incr_cp (M: bool -> 'End(U)) b (D: 'CP(U)) (n : nat) :
  whileso_incr M b D n \is cpmap.
Proof.
elim: n=>[|n IH]; first by rewrite /= is_cpmap.
by rewrite whileso_incrE (CPMap_BuildE IH) is_cpmap.
Qed.
HB.instance Definition _ (M: bool -> 'End(U)) b (D: 'CP(U)) (n : nat) :=
  isCPMap.Build U U (whileso_incr M b D n) (whilso_incr_cp M b D n).

Lemma whilso_incr_tn (M: 'TN(bool;U)) b (D: 'QO(U)) (n : nat) :
  whileso_incr M b D n \is tnmap.
Proof.
apply/cptn_tnmap; elim: n=>[|n IH]; first by rewrite /= is_cptn.
by rewrite whileso_incrE (QOperation_BuildE IH) is_cptn.
Qed.
HB.instance Definition _ (M: 'TN(bool;U)) b (D: 'QO(U)) (n : nat) :=
  CPMap_isTNMap.Build U U (whileso_incr M b D n) (whilso_incr_tn M b D n).

Lemma whileso_iter_cp (M: bool -> 'End(U)) b (D: 'CP(U)) (n : nat) :
  whileso_iter M b D n \is cpmap.
Proof.
elim: n=>[|n IH]; first by rewrite /= is_cpmap.
by rewrite whileso_iterE (CPMap_BuildE IH) is_cpmap.
Qed.
HB.instance Definition _ (M: bool -> 'End(U)) b (D: 'CP(U)) (n : nat) :=
  isCPMap.Build U U (whileso_iter M b D n) (whileso_iter_cp M b D n).

(* match : makes canonical of ifso fails *)
Lemma whileso_iter_tn (M: 'TN(bool;U)) b (D: 'QO(U)) (n : nat) :
  whileso_iter M b D n \is tnmap.
Proof.
apply/cptn_tnmap; elim: n=>[|n IH/=]; first by rewrite /= is_cptn.
suff ->: (fun b' => if b' == b then whileso_iter M b D n :o D else \:1)
  = (fun b' => if b' == b then ((QOperation_Build IH) :o D : 'QO) else (\:1 : 'QO)).
apply: is_cptn. by apply/funext=>b'; case: eqP.
Qed.
HB.instance Definition _ (M: 'TN(bool;U)) b (D: 'QO(U)) (n : nat) :=
CPMap_isTNMap.Build U U (whileso_iter M b D n) (whileso_iter_tn M b D n).

(* whileso_iter is nondecreasing *)
Lemma whileso_iter_chain (M: bool -> 'End(U)) b (D: 'CP(U)) : chain (whileso_iter M b D).
Proof. by rewrite /chain=>i; rewrite whileso_iterE levDl; apply/cp_geso0. Qed.

Lemma whileso_iter_homo (M: bool -> 'End(U)) b (D: 'CP(U)) : 
  nondecreasing_seq (whileso_iter M b D).
Proof. by apply/chain_homo/whileso_iter_chain. Qed.

Lemma whileso_iter_ub (M: 'TN(bool;U)) b (D: 'QO(U)) : 
  ubounded_by (choi2so (dim U)%:R%:M) (whileso_iter M b D).
Proof. by move=>i; apply/qo_ubound. Qed.

Lemma whileso_is_cvg (M: 'TN(bool;U)) b (D: 'QO(U)) : 
  cvgn (whileso_iter M b D).
Proof.
apply: (vnondecreasing_is_cvgn (whileso_iter_homo _ b _) (whileso_iter_ub M b D)).
Qed.

Lemma whileso_cvgn (M: 'TN(bool;U)) b (D: 'QO(U)) : 
  (whileso_iter M b D @ \oo --> whileso M b D)%classic.
Proof. by rewrite whileso.unlock; exact: whileso_is_cvg. Qed.

Lemma whileso_qo (M: 'TN(bool;U)) b (D: 'QO(U)) :
  whileso M b D \is cptn.
Proof.
rewrite whileso.unlock.
suff : [set x : 'SO(U) | x \is cptn]%classic (limn (whileso_iter M b D)) by [].
apply: (@closed_cvg _ _ _ eventually_filter (whileso_iter M b D) _ _ _ _)=>//.
apply closed_isqo. by apply: nearW=>x/=; apply is_cptn.
by apply whileso_is_cvg.
Qed.
HB.instance Definition _ (M: 'TN(bool;U)) b (D: 'QO(U)) := 
  isQOperation.Build U U (whileso M b D) (whileso_qo M b D).

Lemma whileso_ub (M: 'TN(bool;U)) b (D: 'QO(U)) i : whileso_iter M b D i ⊑ whileso M b D.
Proof.
rewrite whileso.unlock.
apply/(nondecreasing_cvgn_lev (whileso_iter_homo _ b _))/whileso_is_cvg.
Qed.

Lemma whileso_least (M: 'TN(bool;U)) b (D: 'QO(U)) x :
  (forall i, whileso_iter M b D i ⊑ x) -> whileso M b D ⊑ x.
Proof. by move=>/(limn_lev (@whileso_is_cvg M b D)); rewrite whileso.unlock. Qed.

Lemma whileso_lim (M: bool -> 'End(U)) b (D: 'SO(U)) : 
  limn (whileso_iter M b D) = whileso M b D.
Proof. by rewrite whileso.unlock. Qed.

End QOWhile.

Section QOWhileRanking.
Variable (U: chsType) (M: 'TN(bool;U)) (b: bool) (D: 'QO(U)).

Definition ranking_function (P: 'FO(U)) 
(t : C -> 'FD(U) -> nat) :=
  forall e, e > 0 ->
  (forall x : 'FD(U), (t e ((D :o elemso M b) x : 'FD) <= t e x)%N /\
  (\Tr (P \o x) >= e -> (t e ((D :o elemso M b) x : 'FD) < t e x)%N)).

Lemma trlfM_ge0 (V: chsType) (f: 'End(V)) (g: 'End(V)) :
  (0 : 'End(V)) ⊑ f -> (0 : 'End(V)) ⊑ g -> 0 <= \Tr (f \o g).
Proof.
move/gef0_formV=>[f' ->]/gef0_formV[g' ->].
rewrite comp_lfunA lftraceC. apply/psdlf_trlf.
by rewrite psdlfE -{2}(adjfK f') -comp_lfunA -adjf_comp comp_lfunA formV_gef0.
Qed.

Lemma nat_well_founded (tt : nat -> nat) : 
  (forall n : nat, (tt n.+1 < tt n)%N) -> False.
Proof.
move=>H.
have P n: (tt n >= 0 -> tt n <= tt 0 - n)%N.
elim: n=>[_|n IH]. by rewrite subn0.
move=>P1. move: (leq_ltn_trans P1 (H _))=> P3.
move: {+}P3=>/ltnW/IH P2. move: (leq_trans P3 P2)=>P4.
rewrite -(leq_add2r 1) addn1. apply (leq_trans (H _)).
apply (leq_trans P2).
rewrite -addn1 -subnA. by rewrite addn1. 
rewrite -leq_psubRL//. by rewrite addn1 subn1.
move: (leq0n (tt (tt 0%N)))=>/P. rewrite subnn leqn0=>/eqP P1.
move: (H (tt 0%N)). by rewrite P1.
Qed.

Fixpoint minpred (P : nat -> bool) m :=
  if (P m) then
    match m with
    | O => 0%N
    | S m' => (minpred P m')
    end
  else m.+1.

Lemma minpred0 (P : nat -> bool) m : ((minpred P m) <= m.+1)%N.
Proof.
elim: m=>[/=|n IH/=]. by case: (P 0%N).
case: (P n.+1)=>//. by apply (leq_trans IH).
Qed.

Lemma minpred6 (P : nat -> bool) m : P m -> ((minpred P m) <= m)%N.
Proof.
case: m=>/=. by move=>->.
move=>n ->. apply minpred0.
Qed.

Lemma minpred5 (P : nat -> bool) m n : ((minpred P m) <= n)%N -> (n <= m)%N -> P n.
Proof.
elim: m. rewrite /=leqn0=>+/eqP P1. rewrite P1; by case E: (P 0%N).
move=>m IH. rewrite /=. case E: (P m.+1).
rewrite [in X in _ -> X]leq_eqVlt. case: eqP=>[->//|_ P1/= P2].
by apply IH.
move=>P1 P2. move: (leq_ltn_trans P2 P1). by rewrite ltnn.
Qed.

Lemma discrete_nat : discrete_space nat.
Proof.
apply/funext=>x; apply/funext=>A; rewrite /principal_filter/=.
rewrite propeqE; split.
  by move=>[B/=[]]/= _ Px /(_ x)/(_ Px) + x1 ->.
move=>/(_ x erefl) Ax; exists ([set x])%classic.
do ! split=>//=; last by move=>?/=->.
exists ([set x])%classic=>//=; by rewrite bigcup_set1.
Qed.

Lemma nat_hausdorff : hausdorff_space nat.
Proof. by apply/discrete_hausdorff/discrete_nat. Qed.

Lemma minpred4 (P : nat -> bool) m : 
  (forall n, (m <= n)%N -> P n) -> limn (minpred P) = minpred P m.
Proof.
move=>H.
suff: ((minpred P) @ \oo --> (minpred P m))%classic.
by move/(cvg_lim nat_hausdorff)=>/=->.
rewrite -(cvg_shiftn m)/=.
have->: (fun n : nat => minpred P (n + m)) = (fun=>minpred P m).
apply/funext=>x. elim: x=>[|n IH]. by rewrite add0n.
by rewrite addSn/= H ?IH// leqW// leq_addl.
apply: cvg_cst.
Qed.

Lemma minpredP (P : nat -> bool) m :
  (forall n, (m <= n)%N -> P n) -> (limn (minpred P) <= m)%N.
Proof. move=>H. rewrite (minpred4 H) minpred6// H//. Qed.

Lemma minpred2 (P : nat -> bool) m :
  (forall n, (m <= n)%N -> P n) -> (forall n, (n >= (limn (minpred P)))%N -> P n).
Proof.
move=>H n. rewrite (minpred4 H)=>P1.
case E: (~~ (n < m))%N. move: E. rewrite -leqNgt. apply H.
move: E=>/negbFE/ltnW. by apply minpred5.
Qed.

Lemma minpred3 (P : nat -> bool) m :
  (forall n, (m <= n)%N -> P n) -> (forall n, ~~ P n -> (n < (limn (minpred P)))%N).
Proof.
move=>H n. apply contraNT. rewrite -leqNgt. apply (minpred2 H).
Qed.

Lemma rankingP (P: 'FO(U)) :
  (exists t, ranking_function P t) <-> 
  (forall x : 'FD(U), (fun n=>\Tr (P \o (whileso_incr M b D n) x)) @ \oo --> 0)%classic.
Proof.
have P0 : forall n (y : 'FD(U)), (whileso_incr M b D n.+1 y) = 
  (D :o elemso M b) (whileso_incr M b D n y : 'FD) :> 'FD.
by move=>n y; apply/val_inj; rewrite /= -whileso_incrED whileso_incrE soE.
split.
apply: contraPP. rewrite -existsNP -forallNP=>[[y Px] t].
move: Px. rewrite ccvgn_subseqPN=>[[e [h [Ph [egt0 /= Pn]]]]].
rewrite /ranking_function -existsNP.
exists e. rewrite not_implyP.
split=>//. move=>/all_and2 [P11 P12].
pose t1 n := t e (whileso_incr M b D n y : 'FD).
have Pt1 n : (t1 n.+1 <= t1 n)%N by rewrite /t1 P0 P11.
have Pt2 : forall m n, (n >= m -> t1 n <= t1 m)%N.
move=>m n /subnK => <-. elim: (n - m)%N => //= l ih.
rewrite addSn. apply: (leq_trans _ ih). apply Pt1. 
pose tt n := (t1 (h n)).
have Pc: forall n, (tt n.+1 < tt n)%N.
move=>n. rewrite /tt.
apply: (@leq_ltn_trans (t1 (h n).+1)).
by apply Pt2. rewrite /t1 P0. apply P12.
rewrite -[X in _ <= X]ger0_norm. apply trlfM_ge0; rewrite -psdlfE.
apply/obslf_psd/is_obslf. apply/denlf_psd/is_denlf.
by move: (Pn n); rewrite subr0.
apply (nat_well_founded Pc).
move=>H1.
pose Q c (x : 'FD(U)) := (fun n=> \Tr (P \o (whileso_incr M b D n) x) < c).
exists (fun c x => (limn (minpred (Q c x)))).
split.
all: move: (H1 x); rewrite ccvgn_limnP=>/(_ _ H)[N Pn];
have P1: (forall n, (N <= n)%N -> Q e x n)
by move=>n len; move: (Pn n len); rewrite /Q subr0 -[X in _ -> X < _]ger0_norm// 
?trlfM_ge0//=; [apply/obsf_ge0 | apply/denf_ge0].
all: have P3 n : Q e x n.+1 = (Q e ((D :o elemso M b) x : 'FD) n)
by rewrite /Q whileso_incrED/= soE.
move: (minpred2 P1)=>P2. apply/minpredP=>n len. rewrite -P3.
apply P2. apply (leq_trans len). by [].
move: (minpred2 P1)=>P2 P4.
have P5: (limn (minpred (Q e x)) > 0)%N.
apply (minpred3 P1). rewrite /Q -real_leNgt/= ?soE//.
by apply gtr0_real. by apply ger0_real; apply: (le_trans _ P4); apply/ltW.
have P7 : forall n m, (n <= m = (n.+1 <= m.+1))%N. by [].
suff P6: limn (minpred (Q e x)) = (limn (minpred (Q e x))).-1.+1.
rewrite P6/= -P7.  
apply/minpredP=>n. rewrite -P3 -ltnS -P6. apply P2.
rewrite  -[_.-1.+1]addn1 -subn1 subnK//.
Qed.

End QOWhileRanking.
(* for quantum programs, we mostly work while. 
Instead of introducing the completeNormedModType of lfun, 
we provide a some lemmas to lim while *)

Section QOWhileLim.
Local Open Scope classical_set_scope.

Lemma while_sf_cvg (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U)) (f: 'End(U) -> C) x :
  scalar f -> ((fun n=>f ((whileso_iter M b D n) x)) @ \oo --> f (whileso M b D x))%classic.
Proof. move=>sf; apply: linear_cvgP=>//; apply: so_cvgl; apply/whileso_cvgn. Qed.

Lemma while_sf_is_cvg (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) (f: 'End(U) -> C) x :
  scalar f -> cvgn (fun n=>f ((whileso_iter M b D n) x)).
Proof. move=>sf; apply: linear_is_cvgP=>//; apply: so_is_cvgl; apply/whileso_is_cvg. Qed.

Lemma while_sf_lim (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) (f: 'End(U) -> C) x :
  scalar f -> limn (fun n=>f ((whileso_iter M b D n) x)) = f (whileso M b D x).
Proof. move=>P. apply/cvg_lim. apply/Chausdorff. by apply/while_sf_cvg. Qed.

Lemma while_sf_ge_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvgn c -> (\forall n \near \oo, c n <= f ((whileso_iter M b D n) x))
  -> limn c <= f (whileso M b D x).
Proof.
by move=>sf cc Pn; rewrite -while_sf_lim//; 
apply/ler_climn_near=>[//||//]; apply/while_sf_is_cvg.
Qed.

Lemma while_sf_ge (U: chsType) (M: 'TN(bool;U)) b
        (D: 'QO(U,U)) (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvgn c -> (forall n, c n <= f ((whileso_iter M b D n) x))
  -> limn c <= f (whileso M b D x).
Proof.
move=>sf cc Pn; rewrite -while_sf_lim//;
apply/ler_climn=>[//||//]; by apply/while_sf_is_cvg.
Qed.

Lemma while_sf_ge_cst_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (\forall n \near \oo, c <= f ((whileso_iter M b D n) x))
  -> c <= f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite ccvgn_limnE=>[[{5}<- P1]] P2 P3; by apply while_sf_ge_near.
Qed.

Lemma while_sf_ge_cst (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (forall n, c <= f ((whileso_iter M b D n) x))
  -> c <= f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite ccvgn_limnE=>[[{4}<- P1]] P2 P3; by apply while_sf_ge.
Qed.

Lemma while_sf_le_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvgn c
  -> (\forall n \near \oo, f ((whileso_iter M b D n) x) <= c n)
  -> f (whileso M b D x) <= limn c.
Proof.
move=>sf cc Pn; rewrite -while_sf_lim//.
by apply/ler_climn_near=>[|//|//]; apply/while_sf_is_cvg.
Qed.

Lemma while_sf_le (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) (c: nat -> C) x :
  scalar f -> cvgn c -> (forall n, f ((whileso_iter M b D n) x) <= c n)
  -> f (whileso M b D x) <= limn c.
Proof.
move=>sf cc Pn; rewrite -while_sf_lim//;
apply/ler_climn=>[|//|//]; by apply/while_sf_is_cvg.
Qed.

Lemma while_sf_le_cst_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (\forall n \near \oo, f ((whileso_iter M b D n) x) <= c)
  -> f (whileso M b D x) <= c.
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite ccvgn_limnE=>[[{5}<- P1]] P2 P3; by apply while_sf_le_near.
Qed.

Lemma while_sf_le_cst (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'End(U) -> C) c x :
  scalar f -> (forall n, f ((whileso_iter M b D n) x) <= c)
  -> f (whileso M b D x) <= c.
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite ccvgn_limnE=>[[{4}<- P1]] P2 P3; by apply while_sf_le.
Qed.

Lemma while_sf_eq_near (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f g : 'End(U) -> C) m x c :
  scalar f -> scalar g -> (\forall n \near \oo, 
    f ((whileso_iter M b D n) x) + c = g ((whileso_iter M b D (n+m)%N) x))
  -> f (whileso M b D x) + c = g (whileso M b D x).
Proof.
move=>sf sg /(lim_eq_near (@norm_hausdorff _ _)).
rewrite climnD. by apply while_sf_is_cvg. apply: is_ccvgn_cst.
rewrite climn_cst while_sf_lim// =>->.
move: (@while_sf_cvg _ M b D _ x sg).
by rewrite -(cvg_shiftn m)=>/(cvg_lim (@Chausdorff _)).
Qed.

Lemma while_lf_cvg (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) x :
  ((fun n=>f ((whileso_iter M b D n) x)) @ \oo --> f (whileso M b D x))%classic.
Proof.
apply: continuous_cvg. apply: linear_continuous.
apply: so_cvgl. apply whileso_cvgn.
Qed.

Lemma while_lf_is_cvg (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) x :
  cvgn (fun n=>f ((whileso_iter M b D n) x)).
Proof. by apply/cvg_ex; exists (f (whileso M b D x)); apply while_lf_cvg. Qed.

Lemma while_lf_lim (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) x :
  limn (fun n=>f ((whileso_iter M b D n) x)) = f (whileso M b D x).
Proof. apply/cvg_lim. apply/norm_hausdorff. by apply/while_lf_cvg. Qed.

Lemma while_lf_ge_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) (c: nat -> 'End(V)) x :
  cvgn c -> (\forall n \near \oo, c n ⊑ f ((whileso_iter M b D n) x))
  -> limn c ⊑ f (whileso M b D x).
Proof.
by move=>cc Pn; rewrite -while_lf_lim//; 
apply/lev_limn_near=>[//||//]; apply/while_lf_is_cvg.
Qed.

Lemma while_lf_ge (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) (c: nat -> 'End(V)) x :
  cvgn c -> (forall n, c n ⊑ f ((whileso_iter M b D n) x))
  -> limn c ⊑ f (whileso M b D x).
Proof.
move=>cc Pn; rewrite -while_lf_lim//;
apply/lev_limn=>[//||//]; by apply/while_lf_is_cvg.
Qed.

Lemma while_lf_ge_cst_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) c x :
  (\forall n \near \oo, c ⊑ f ((whileso_iter M b D n) x))
  -> c ⊑ f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite cvgn_limnE. apply: norm_hausdorff.
move=>[{5}<- P1] P3; by apply while_lf_ge_near.
Qed.

Lemma while_lf_ge_cst (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) c x :
  (forall n, c ⊑ f ((whileso_iter M b D n) x))
  -> c ⊑ f (whileso M b D x).
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite cvgn_limnE. apply norm_hausdorff.
move=>[{4}<- P1] P3; by apply while_lf_ge.
Qed.

Lemma while_lf_le_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) (c: nat -> 'End(V)) x :
  cvgn c -> (\forall n \near \oo, f ((whileso_iter M b D n) x) ⊑ c n)
  -> f (whileso M b D x) ⊑ limn c.
Proof.
move=>cc Pn; rewrite -while_lf_lim//.
by apply/lev_limn_near=>[|//|//]; apply/while_lf_is_cvg.
Qed.

Lemma while_lf_le (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) (c: nat -> 'End(V)) x :
  cvgn c -> (forall n, f ((whileso_iter M b D n) x) ⊑ c n)
  -> f (whileso M b D x) ⊑ limn c.
Proof.
move=>cc Pn; rewrite -while_lf_lim//;
apply/lev_limn=>[|//|//]; by apply/while_lf_is_cvg.
Qed.

Lemma while_lf_le_cst_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) c x :
  (\forall n \near \oo, f ((whileso_iter M b D n) x) ⊑ c)
  -> f (whileso M b D x) ⊑ c.
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite cvgn_limnE. apply norm_hausdorff.
move=>[{5}<- P1] P2; by apply while_lf_le_near.
Qed.

Lemma while_lf_le_cst (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f: 'Hom('End(U), 'End(V))) c x :
  (forall n, f ((whileso_iter M b D n) x) ⊑ c)
  -> f (whileso M b D x) ⊑ c.
Proof.
have: ((fun n:nat=>c) @ \oo --> c)%classic by apply: cvg_cst.
rewrite cvgn_limnE. apply norm_hausdorff.
move=>[{4}<- P1] P2; by apply while_lf_le.
Qed.

Lemma while_lf_eq_near (U V: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) 
  (f g : 'Hom('End(U), 'End(V))) m x c :
  (\forall n \near \oo, f ((whileso_iter M b D n) x) + c = g ((whileso_iter M b D (n+m)%N) x))
  -> f (whileso M b D x) + c = g (whileso M b D x).
Proof.
move=>/(lim_eq_near (@norm_hausdorff _ _)).
rewrite limD. by apply while_lf_is_cvg. apply: is_cvg_cst.
rewrite lim_cst ?while_lf_lim// =>->.
move: (@while_lf_cvg _ _ M b D g x).
by rewrite -(cvg_shiftn m)=>/(cvg_lim (@norm_hausdorff _ _)).
Qed.

Lemma whileso_fixpoint (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) : 
  whileso M b D = ifso M (fun b'=> if b' == b then whileso M b D :o D
  else idso).
Proof.
apply/so_psdP=>x. rewrite psdlfE=>Px.
rewrite (ifso_boolE b) eqxx neqb !comp_soE soE.
apply/eqP. rewrite eq_le. apply/andP. split.
2: rewrite -levBrDr.
all: rewrite -[X in X ⊑ _]id_lfunE;
  apply/while_lf_le_cst=>n; rewrite lfunE/=.
case: n=>[|n]; first by rewrite /= soE addv_ge0=>[||//]; 
  [apply/cp_ge0/cp_ge0/cp_ge0 | apply/cp_ge0].
2: move: (whileso_ub M b D n.+1)=>/leso_preserve_order/(_ Px); 
  rewrite levBrDr; apply le_trans.
all: rewrite /= (ifso_boolE b) eqxx neqb !comp_soE soE levD2r.
2: by apply lexx.
apply/leso_preserve_order. apply/whileso_ub. by apply/cp_ge0/cp_ge0.
Qed.

Lemma whileso_incr_while (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) n :
  whileso M b D :o (whileso_incr M b D n) = whileso M b D - whileso_iter M b D n.
Proof.
elim: n=>[|n IH]; first by rewrite /= comp_so1r subr0.
rewrite whileso_incrE whileso_iterE opprD addrA -IH -linearBl/= !comp_soA.
f_equal.
by rewrite {2}whileso_fixpoint (ifso_bool b) eqxx neqb comp_so1l addrK.
Qed.

Lemma whileso_incr_whileE (U: chsType) (M: 'TN(bool;U)) b (D: 'QO(U,U)) n x :
  whileso M b D (whileso_incr M b D n x) = whileso M b D x - whileso_iter M b D n x.
Proof. by move: (whileso_incr_while M b D n)=>/superopP/(_ x); rewrite !soE. Qed.

Lemma whileso_iter_leso (U : chsType) (M : bool -> 'End(U)) (b : bool) (c1 c2 : 'CP(U)) :
  (c1 : 'SO) <= c2 -> forall n, whileso_iter M b c1 n <= whileso_iter M b c2 n.
Proof.
move=>P; elim; first by rewrite /= lexx.
move=>n Pn. rewrite /= !(ifso_bool b) eqxx/= neqb levD ?lexx=>[|//|//].
apply: leso_comp2r; last by apply: cp_geso0.
apply: leso_comp2. 1,2: apply: cp_geso0. apply: Pn. apply: P.
Qed.

Lemma whileso_leso (U : chsType) (M : 'TN(bool;U)) (b : bool) (c1 c2 : 'QO(U)) :
  (c1 : 'SO) <= c2 -> whileso M b c1 <= whileso M b c2.
Proof.
move=>Pc; rewrite whileso.unlock.
apply: lev_limn=>[||n]. 1,2: apply: whileso_is_cvg.
by apply: whileso_iter_leso.
Qed.

Lemma whileso_iter_continuous (U : chsType) (M : bool -> 'End(U)) b n :
  continuous (@whileso_iter U M b ^~ n).
Proof.
move=>/= x; rewrite /continuous_at.
elim: n.  rewrite /=; apply: cvg_cst. apply: nbhs_filter.
move=>i IH /=; rewrite (ifso_bool b)/= eqxx neqb.
under eq_cvg do rewrite (ifso_bool b)/= eqxx neqb.
apply: cvgD. apply: nbhs_filter.
apply: so_comp_cvgl. apply: nbhs_filter.
apply: so_comp_cvg. apply: nbhs_filter. apply: IH. apply: cvg_id.
apply: cvg_cst. apply: nbhs_filter.
Qed.

Lemma whileso_iter_cvg (U : chsType) (M : bool -> 'End(U)) b n 
  (T : Type) (F : set_system T) {FF : Filter F} (f : T -> 'SO) (g : 'SO) :
  f @ F --> g -> (fun i => @whileso_iter U M b (f i) n) @ F --> whileso_iter M b g n.
Proof.
move=>P; have Pi i : whileso_iter M b (f i) n = 
  ((@whileso_iter U M b ^~ n) \o f)%FUN i by [].
under eq_cvg do rewrite Pi.
apply: (continuous_cvg FF _ P). apply: whileso_iter_continuous.
Qed.

Lemma whileso_iter_is_cvg (U : chsType) (M : bool -> 'End(U)) b n 
  (T : Type) (F : set_system T) {FF : Filter F} (f : T -> 'SO) :
   cvg (f @ F) -> cvg ((fun i => @whileso_iter U M b (f i) n) @ F).
Proof.
by move=>?; apply/cvg_ex; 
  exists (whileso_iter M b (lim (f @ F)) n); apply: whileso_iter_cvg.
Qed.

Lemma whileso_iter_limn (U : chsType) (M : bool -> 'End(U)) b n 
  (T : Type) (F : set_system T) {PF : ProperFilter F} (f : T -> 'SO) :
  cvg (f @ F)%classic ->
    (lim ((fun i => @whileso_iter U M b (f i) n) @ F) = 
      whileso_iter M b (lim (f @ F)) n)%classic.
Proof.
by move=>?; apply: cvg_lim=>[//|]; apply: whileso_iter_cvg.
Qed.

End QOWhileLim.

From mathcomp Require Import finset.

Section ComplementObs.
Variable (U : chsType).

Definition cplmt (P : 'End(U)) := \1 - P.
Lemma cplmtE (P : 'End(U)) : \1 - P = cplmt P. Proof. by []. Qed.

Lemma cplmtK P : cplmt (cplmt P) = P.
Proof. by rewrite /cplmt opprB addrC addrNK. Qed.

Lemma cplmt1 : cplmt \1 = 0.
Proof. by rewrite /cplmt subrr. Qed.

Lemma cplmt0 : cplmt 0 = \1.
Proof. by rewrite -cplmt1 cplmtK. Qed.

(* canonical structures *)
Lemma cplmt_obs (P : 'FO(U)) : cplmt P \is obslf.
Proof. 
by move: (is_obslf P); rewrite !obslfE subv_ge0 levBlDr levDl=>/andP[->->].
Qed.
HB.instance Definition _ (P : 'FO(U)) := isObsLf.Build U (cplmt P) (cplmt_obs P).

Lemma cplmt_proj (P : 'FP(U)) : cplmt P \is projlf.
Proof.
apply/projlfP; split. apply/hermlfP/obslf_herm/is_obslf.
rewrite /cplmt linearBl/= !linearBr/= !comp_lfun1l comp_lfun1r.
by move: (is_projlf P)=>/projlfP[_ ->]; rewrite addrN subr0.  
Qed.
HB.instance Definition _ (P : 'FP(U)) := Obs_isProjLf.Build U (cplmt P) (cplmt_proj P).

Lemma cplmt_dualC (E: 'QC(U)) (P:'FO(U)) : 
  cplmt (E^*o P) = E^*o (cplmt P).
Proof. by rewrite /cplmt linearB/= qu1_eq1. Qed.
Lemma cplmt_lef (P Q : 'End(U)) : P ⊑ Q = (cplmt Q ⊑ cplmt P).
Proof. by rewrite levBlDl addrA levBrDl levD2r. Qed. 

End ComplementObs.

Arguments cplmt {U} P.
Notation "P '^⟂'" := (cplmt P).

Lemma formso_comp (U V W : chsType) (f1 : 'Hom(U,V)) (f2 : 'Hom(W,U)) :
  formso f1 :o formso f2 = formso (f1 \o f2).
Proof. by apply/superopP=>A; rewrite soE !formsoE adjf_comp !comp_lfunA. Qed.

Lemma normalfE U (f : 'FN(U)) : f \o f^A = f^A \o f.
Proof. by apply/normallfP/is_normallf. Qed.

HB.lock
Definition formlf (U V : chsType) (f : 'Hom(U,V)) (A : 'End(U)) :=
  f \o A \o f^A.
(* for isometry !! *)
(* to use different canonical route w.r.t. formso *)

Lemma formlf_comp (U V W : chsType) (f1 : 'Hom(U,V)) (f2 : 'Hom(W,U)) A :
  formlf f1 (formlf f2 A) = formlf (f1 \o f2) A.
Proof. by rewrite formlf.unlock adjf_comp !comp_lfunA. Qed.

Section formlf_extra.
Variable (U V : chsType).

Lemma formlf_soE (f : 'Hom(U,V)) A :
  formlf f A = formso f A.
Proof. by rewrite formsoE formlf.unlock. Qed.

Lemma formlf_adj (f : 'Hom(U,V)) A :
  (formlf f A)^A = formlf f A^A.
Proof. by rewrite formlf.unlock !adjf_comp adjfK comp_lfunA. Qed.

Lemma formlf_normal (u : 'FI(U,V)) (A : 'FN) :
  formlf u A \is normallf.
Proof.
rewrite formlf.unlock; apply/normallfP.
by rewrite !adjf_comp !adjfK !comp_lfunA !isofK comp_lfunACA normalfE comp_lfunA.
Qed.
HB.instance Definition _ (u : 'FI(U,V)) (A : 'FN) :=
  isNormalLf.Build _ (formlf u A) (@formlf_normal u A).

Lemma formlf_herm (u : 'FI(U,V)) (A : 'FH) :
  formlf u A \is hermlf.
Proof. by apply/hermlfP; rewrite formlf.unlock !adjf_comp adjfK hermf_adjE comp_lfunA. Qed.
HB.instance Definition _ (u : 'FI(U,V)) (A : 'FH) :=
  Normal_isHermLf.Build _ (formlf u A) (@formlf_herm u A).

Lemma formlf_psd (u : 'FI(U,V)) (A : 'F+) :
  formlf u A \is psdlf.
Proof.
apply/psdlfP=>v; rewrite formlf.unlock lfunE/= lfunE/= -adj_dotEl.
by apply/psdlfP/is_psdlf.
Qed.
HB.instance Definition _ (u : 'FI(U,V)) (A : 'F+) :=
  Herm_isPsdLf.Build _ (formlf u A) (@formlf_psd u A).

Lemma formlf_obs (u : 'FI(U,V)) (A : 'FO) :
  formlf u A \is obslf.
Proof.
apply/obslfP; split=>[|v]. apply/is_psdlf.
rewrite formlf.unlock lfunE/= lfunE/= -adj_dotEl.
move: (is_obslf A)=>/obslfP[] _ /(_ (u^A v)) P1.
by apply: (le_trans P1); apply/isofA_dot.
Qed.
HB.instance Definition _ (u : 'FI(U,V)) (A : 'FO) :=
  Psd_isObsLf.Build _ (formlf u A) (@formlf_obs u A).

Lemma formlf_den (u : 'FI(U,V)) (A : 'FD) :
  formlf u A \is denlf.
Proof.
apply/denlfP; split. apply/is_psdlf.
by rewrite formlf.unlock lftraceC comp_lfunA isofE comp_lfun1l denf_trlf.
Qed.
HB.instance Definition _ (u : 'FI(U,V)) (A : 'FD) :=
  Obs_isDenLf.Build _ (formlf u A) (@formlf_den u A).

Lemma formlf_den1 (u : 'FI(U,V)) (A : 'FD1) :
  formlf u A \is den1lf.
Proof.
apply/den1lfP; split. apply/is_psdlf.
by rewrite formlf.unlock lftraceC comp_lfunA isofE comp_lfun1l den1f_trlf.
Qed.
HB.instance Definition _ (u : 'FI(U,V)) (A : 'FD1) :=
  Den_isDen1Lf.Build _ (formlf u A) (@formlf_den1 u A).

Lemma formlf_proj (u : 'FI(U,V)) (A : 'FP) :
  formlf u A \is projlf.
Proof.
apply/projlfP; split. apply/hermf_adjE.
by rewrite formlf.unlock !comp_lfunA isofK comp_lfunACA projf_idem.
Qed.
HB.instance Definition _ (u : 'FI(U,V)) (A : 'FP) :=
  Obs_isProjLf.Build _ (formlf u A) (@formlf_proj u A).

HB.instance Definition _ (u : 'FI(U,V)) (A : 'FP1) := Proj1Lf.Class
  (ProjLf.on (formlf u A)) (Den1Lf.on (formlf u A)).

End formlf_extra.

Lemma formlf1E (U V : chsType) (N : 'Hom(U,V)) :
  formlf N \1 = N \o N^A.
Proof. by rewrite formlf.unlock comp_lfun1r. Qed.
Lemma formlf1EV (U V : chsType) (N : 'Hom(U,V)) :
  formlf N^A \1 = N^A \o N.
Proof. by rewrite formlf.unlock comp_lfun1r adjfK. Qed.
Lemma formlfE (U V : chsType) (N : 'Hom(U,V)) (A : 'End(U)) :
  formlf N A = N \o A \o N^A.
Proof. by rewrite formlf.unlock. Qed.
Lemma formlfEV (U V : chsType) (N : 'Hom(U,V)) (A : 'End(V)) :
  formlf N^A A = N^A \o A \o N.
Proof. by rewrite formlfE adjfK. Qed.

Lemma formlf_linear (U V : chsType) (N : 'Hom(U,V)) : linear (@formlf U V N).
Proof. by move=>a u v; rewrite !formlfE linearPr/= linearPl. Qed.
HB.instance Definition _ (U V : chsType) (N : 'Hom(U,V)) :=
  GRing.isLinear.Build C 'End(U) 'End(V) *:%R (@formlf U V N) (formlf_linear N).

Lemma formlf_lef (U V : chsType) (N : 'Hom(U,V)) (A B : 'End(U)) :
  A <= B -> formlf N A <= formlf N B.
Proof. by rewrite formlf.unlock; exact: lef_formV. Qed.

Lemma formlf_sum_diag (U V : chsType) (F : finType)
  (N : F -> 'Hom(U,V)) (A : 'End(U)) :
  (forall i j, i != j -> (N i) \o A \o (N j)^A = 0) ->
  formlf (\sum_i N i) A = \sum_i formlf (N i) A.
Proof.
move=>P1; rewrite formlfE adjf_sum !linear_sumr/=.
apply eq_bigr=>i _; rewrite !linear_suml/= (bigD1 i)//= big1=>[j /P1 //|];
by rewrite addr0 formlfE.
Qed.

Lemma formlf_bound1f_le1 (U V : chsType) (N : 'FB1(U,V)) (A : 'End(U)) :
  A <= \1 -> formlf N A <= \1.
Proof.
move=>/(formlf_lef N) P; apply: (le_trans P).
by rewrite formlf1E bound1f_formV_le1.
Qed.

Lemma formlf_sum_bound1 (U V : chsType) (F : finType) (N : 'TN(F;U,V)) 
  (W X : chsType) (A : 'FB1(V,W)) (B : 'FB1(X,U)) (C : F -> 'FB1(X)) :
    (forall i j, i != j -> (N i)^A \o N j = 0) ->
    (\sum_i (N i \o (N i)^A) <= \1) ->
      \sum_i formlf (A \o N i \o B) (C i) \is bound1lf.
Proof.
move=>Pij PN.
rewrite bound1lf_form_le1 -formlf1EV adjf_sum.
under eq_bigr do rewrite formlf_adj -comp_lfunA -formlf_comp formlfE -comp_lfunA.
rewrite -linear_sumr/= -formlf_comp; apply/formlf_bound1f_le1.
rewrite -linear_suml/= -formlf_comp formlf1EV.
apply: (le_trans (formlf_lef _ (bound1f_form_le1 A))).
under eq_bigr do rewrite -formlf_comp formlfE.
rewrite formlf_sum_diag.
by move=>i j /Pij nij; rewrite comp_lfun1r adjf_comp adjfK 
  comp_lfunA [LHS]comp_lfunACA nij comp_lfun0r comp_lfun0l.
apply/(le_trans _ PN)/lev_sum=>i _.
rewrite -formlf1E -comp_lfunA -formlf_comp; apply/formlf_lef.
rewrite [in X in formlf X \1]formlfE -!comp_lfunA -!formlf_comp.
apply/formlf_bound1f_le1/formlf_bound1f_le1/formlf_bound1f_le1.
apply: (le_trans _ (@is_trnincr _ _ _ N)).
by rewrite (bigD1 i)//= formlf1EV levDl sumv_ge0// =>j _; rewrite form_gef0.
Qed.

(* generalized while; in each iteration, it executes a quantum operation     *)
(* (but not fixed)                                                           *)
Section WhileCvg.
Variable (U : chsType) (M0 M1 : 'End(U)).
Hypothesis (M_tn : (M0^A \o M0) + (M1^A \o M1) <= \1).
Implicit Type (f : nat -> 'SO(U)).
(* Variable (f : nat -> 'SO(U)) (fQO : forall i, f i \is cptn). *)

Let whilegso_iter f :=
  (fun n => \sum_(i < n) (formso M0 :o \compr_(j < i) ((f j) :o (formso M1)))).

Lemma comp_so_cpmap (V W X : chsType) (E : 'SO(V,W)) (F : 'SO(X,V)) :
  E \is cpmap -> F \is cpmap -> E :o F \is cpmap.
Proof.
by move=>P1 P2;
rewrite (CPMap_BuildE P1) (CPMap_BuildE P2) is_cpmap.
Qed.

Lemma whilegso_iter_homo f (fQO : forall i, f i \is cptn) :
  nondecreasing_seq (whilegso_iter f).
Proof.
apply/cpo.chain_homo=>i; rewrite /whilegso_iter big_ord_recr/= levDl geso0_cpE.
apply/comp_so_cpmap; first by apply/is_cpmap.
elim/big_rec: _ =>[|j x _ Px]; first by apply/is_cpmap.
rewrite comp_soErl; apply/comp_so_cpmap=>[//|]; apply/comp_so_cpmap.
by apply/cptn_cpmap. apply/is_cpmap.
Qed.

#[local] Lemma M1_den (x : 'FD) : formso M1 x \is denlf.
Proof.
apply/denlfP; split; first by apply/is_psdlf.
apply: (le_trans _ (denf_trlf x)).
rewrite -{2}(comp_lfun1l x) formsoE lftraceC comp_lfunA.
apply/lef_trden; rewrite -subv_ge0; apply: (le_trans (y := M0^A \o M0)).
apply: form_gef0. by rewrite levBrDr.
Qed.

#[local] Lemma M01_trlf (x : 'FD) (E : 'SO) (H : E \is tnmap) : 
  \Tr (formso M0 x + E (formso M1 x)) <= \Tr x.
Proof.
apply: (le_trans (y := \Tr (formso M0 x + formso M1 x))).
  by rewrite !linearD/= lerD2l (DenLf_BuildE (M1_den x)); apply/tnmapP.
rewrite linearD/= !formsoE lftraceC [\Tr (_ \o M1^A)]lftraceC.
rewrite !comp_lfunA -linearD/= -comp_lfunDl -{2}(comp_lfun1l x).
by apply/lef_trden/M_tn.
Qed.

Lemma whilegso_iter_tn f n (fQO : forall i, f i \is cptn) :
  whilegso_iter f n \is tnmap.
Proof.
elim: n f fQO.
by move=>f _; rewrite /whilegso_iter big_ord0 is_tnmap.
move=>n IH f Pf; apply/tnmapP=>x.
apply: (le_trans _ (M01_trlf x (cptn_tnmap (Pf 0)))).
rewrite /whilegso_iter big_ord_recl /=
  big_ord0 comp_so1r soE !linearD/= lerD2l.
have P1: f 0 (formso M1 x) \is denlf.
  by rewrite (DenLf_BuildE (M1_den x)) (QOperation_BuildE (Pf 0)) is_denlf.
pose g i := f i.+1.
have Pg i : g i \is cptn by rewrite /g.
move: (IH g Pg)=>/tnmapP/(_ (DenLf_Build P1))/=; apply: le_trans;
rewrite /whilegso_iter !sum_soE !linear_sum/=; apply ler_sum=>i _.
by rewrite /bump leq0n add1n big_ord_recl /=
  comp_soErl comp_soA soE [(_ :o _) x]soE.
Qed.

Lemma whilegso_iter_cptn f n (fQO : forall i, f i \is cptn) :
  whilegso_iter f n \is cptn.
Proof.
apply/cptnP; split; last by apply/whilegso_iter_tn.
rewrite -geso0_cpE; apply: (le_trans (y := whilegso_iter f 0)).
by rewrite /whilegso_iter big_ord0. by apply/whilegso_iter_homo/leq0n.
Qed.

Lemma whilegso_iter_ub f (fQO : forall i, f i \is cptn) : 
  ubounded_by (choi2so (dim U)%:R%:M) (whilegso_iter f).
Proof.
by move=>i; rewrite (QOperation_BuildE (whilegso_iter_cptn i fQO));
apply/qo_ubound.
Qed.

Lemma whilegso_is_cvgn f (fQO : forall i, f i \is cptn) : 
  cvgn (whilegso_iter f).
Proof.
by apply: (vnondecreasing_is_cvgn
  (whilegso_iter_homo fQO) (whilegso_iter_ub fQO)). Qed.

Lemma whilegso_cptn f (fQO : forall i, f i \is cptn) : 
  limn (whilegso_iter f) \is cptn.
Proof.
suff : [set x : 'SO(U) | x \is cptn]%classic (limn (whilegso_iter f)) by [].
apply: (@closed_cvg _ _ _ eventually_filter (whilegso_iter f) _ _ _ _)=>//.
apply closed_isqo. by apply: nearW=>x/=; apply (whilegso_iter_cptn x fQO).
by apply whilegso_is_cvgn.
Qed.

Lemma whilegso_ub f (fQO : forall i, f i \is cptn) n : 
  whilegso_iter f n ⊑ limn (whilegso_iter f).
Proof.
by apply/(nondecreasing_cvgn_lev (whilegso_iter_homo fQO))/whilegso_is_cvgn.
Qed.

Lemma whilegso_least f (fQO : forall i, f i \is cptn) x : 
  (forall i, whilegso_iter f i ⊑ x) -> limn (whilegso_iter f) ⊑ x.
Proof. by move=>/(limn_lev (whilegso_is_cvgn fQO)). Qed.

End WhileCvg.

HB.lock Definition whilegso (U : chsType) (M : bool -> 'End(U)) (f : nat -> 'SO(U)) :=
  limn (fun n => \sum_(i < n) (formso (M false) :o \compr_(j < i) ((f j) :o (formso (M true))))).

Lemma whilegso_fixpoint (U : chsType) (M : 'TN(bool;U)) (f : nat -> 'QO(U)) :
  (whilegso M (fun i : nat => f i.+1) :o f 0%N) :o formso (M true) + formso (M false) =
  whilegso M f.
Proof.
have Pc: cvgn (fun n : nat => \sum_(i < n) (formso (M false) :o \compr_(j < i) (f j.+1 :o formso (M true)))).
  apply: (whilegso_is_cvgn _ (f := (fun i : nat => f i.+1))).
  by move: (@is_trnincr _ _ _ M); rewrite /trace_nincr big_bool/= addrC.
  move=>i; apply/is_cptn.
rewrite whilegso.unlock -so_comp_liml//.
rewrite -so_comp_liml. apply: so_comp_is_cvgl=>//.
rewrite -limDl. apply: so_comp_is_cvgl. apply: so_comp_is_cvgl=>//.
rewrite -[RHS]limn_shiftS; apply: eq_lim=>i.
rewrite /= big_ord_recl/= big_ord0 comp_so1r addrC; f_equal.
rewrite linear_suml/= linear_suml/=; apply eq_bigr=>j _.
by rewrite bump0 big_ord_recl/= comp_soErl !comp_soA.
Qed.
