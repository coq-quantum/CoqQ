From mathcomp Require Import all_ssreflect all_algebra.
Require Import forms.
From mathcomp.analysis Require Import boolp reals classical_sets 
  topology normedtype sequences functions.
From mathcomp.real_closed Require Import complex.
From mathcomp Require Import finset.
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra hermitian prodvect tensor setdec lfundef mxpred mxtopology mxnorm.
Require Import quantum hspace inhabited dirac qwhile.
Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import Vector.InternalTheory CTopology.Exports HermitianTopology.Exports.
Local Notation C := hermitian.C.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(******************************************************************************)
(*                            quantum Hoare logic                             *)
(* this file formly implement the quantum Hoare logic                         *)
(* the proof rules are roughly divided to four :                              *)
(* global : (lfun, predicate are global observable)                           *)
(*          rules comes from [1]                                              *)
(*          ⊨g [ pt , st ] { P } c { Q }                                     *)
(* local  : (lfun, predicate are linear function 'F[H]_S for all S : {set L}) *)
(*          rules inspired by [1,4]                                           *)
(*          New rule R_Inner (and its variant)                                *)
(*          ⊨l [ pt , st ] { P } c { Q }                                     *)
(* dirac  : (qexpr, predicate are 'QE )                                       *)
(*          rules inspired by [1,2,3,4]                                       *)
(*          ⊨ [ pt , st ] { P } c { Q }                                      *)
(* state  : (qexpr, predicate are 'QE )                                       *)
(*          rules inspired by [1,2,3,4]                                       *)
(*          ⊨s [ pt , st ] { P } c { Q }                                     *)
(* Naming rule :  G : global, L : local, S : state                            *)
(*                V : vector, P : partial, T : total                          *)
(*                (S : with 'QE of {wf _,_}) (V : with 'QE of {ket _})        *)
(* for example, R_XX :                                                        *)
(*    R_XX_L : R_XX for local                                                 *)
(*    R_XX_GP : R_XX for global and for partial                               *)
(*    R_XX : for dirac                                                        *)
(*    RS_XX_T : for state and for total (predicate are {wf _,_})              *)
(*    RV_XX_P : for state and for partial (predicate are {ket _})             *)
(* -------------------------------------------------------------------------- *)
(* Rules include :                                                            *)
(*    partial/total/saturated,                                                *)
(*    forward/backward,                                                       *)
(*    for abstract/concrete syntax,                                           *)
(*    basic construct,                                                        *)
(*    structural rule such as frame,                                          *)
(*    parallel rule for for loops                                             *)
(*    R_Inner for connect forward/backward reasoning                          *)
(* -------------------------------------------------------------------------- *)
(* Others : show weakest (liberal) precondition for global is well-defined    *)
(*          and derive it for each basic constructs                           *)
(******************************************************************************)

Notation GPRE  := (X in (⊨g [ _ , _ ] { X } _ { _ }) )%pattern.
Notation GPOST := (X in (⊨g [ _ , _ ] { _ } _ { X }) )%pattern.
Notation GCMD  := (X in (⊨g [ _ , _ ] { _ } X { _ }) )%pattern.
Notation LPRE  := (X in (⊨l [ _ , _ ] { X } _ { _ }) )%pattern.
Notation LPOST := (X in (⊨l [ _ , _ ] { _ } _ { X }) )%pattern.
Notation LCMD  := (X in (⊨l [ _ , _ ] { _ } X { _ }) )%pattern.
Notation PRE  := (X in (⊨ [ _ , _ ] { X } _ { _ })%QE )%pattern.
Notation POST := (X in (⊨ [ _ , _ ] { _ } _ { X })%QE )%pattern.
Notation CMD  := (X in (⊨ [ _ , _ ] { _ } X { _ })%QE )%pattern.
Notation SPRE  := (X in (⊨s [ _ , _ ] { X } _ { _ })%QE )%pattern.
Notation SPOST := (X in (⊨s [ _ , _ ] { _ } _ { X })%QE )%pattern.
Notation SCMD  := (X in (⊨s [ _ , _ ] { _ } X { _ })%QE )%pattern.

Lemma big_boolb (R : Type) (idx : R) (op : Monoid.com_law idx) b (F : bool -> R):
    \big[op/idx]_i F i = op (F b) (F (~~b)).
Proof. by rewrite big_bool; case: b=>/=; rewrite Monoid.mulmC. Qed.
Global Arguments big_boolb [R idx op].

Lemma not_eqb (b1 b2 : bool) : b1 <> b2 <-> b1 = ~~b2.
Proof. by case: b1; case: b2. Qed.

Section FinQHL.
Context (L : finType) (H : L -> chsType).
Local Notation cmd_ := (@cmd_ L H).
Local Notation abort_ := (@abort_ L H).
Local Notation skip_ := (@skip_ L H).
Local Notation init_ := (@init_ L H).
Local Notation unitary_ := (@unitary_ L H).
Local Notation cond_ := (@cond_ L H).
Local Notation while_ := (@while_ L H).
Local Notation seqc_ := (@seqc_ L H).
Implicit Type (pt st : bool) (c : cmd_).

(* for backward reasoning, we set all arguments implicit *)
(****************************************************************************)
Section GlobalHoare.
Implicit Type (P Q R : 'FO[H]_setT).

Lemma no_while_enoughg st pt c P Q : no_while c ->
  ⊫tg { P } c { Q } -> ⊨g [pt,st] { P } c { Q }.
Proof. by move=>P1; case: pt=>//; rewrite ?no_while_GPT// =>/saturated_strong_G. Qed.
Global Arguments no_while_enoughg [st pt c P Q].

Lemma Ax_Ab_GT st P : ⊨tg [st] { [obs of 0] } abort_ { P }.
Proof. by case: st=>x; rewrite fsemE soE comp_lfun0r comp_lfun0l linear0. Qed.
Global Arguments Ax_Ab_GT [st P].

Lemma Ax_Ab_GP st P : ⊨pg [st] { [obs of 1] } abort_ { P }.
Proof. by case: st=>x; rewrite fsemE/= soE cplmt1 comp_lfun0r comp_lfun0l linear0. Qed.
Global Arguments Ax_Ab_GP [st P].

Lemma Ax_Sk_G pt st P : ⊨g [pt,st] { P } skip_ { P }.
Proof. by case: pt; case: st=>x; rewrite fsemE soE. Qed.
Global Arguments Ax_Sk_G [pt st P].

Lemma Ax_In_G pt st S (v : 'NS_S) P : 
  ⊨g [pt,st] { [obs of (liftfso (initialso v))^*o P] } (init_ v) { P }.
Proof. by case: st; apply/no_while_enoughg=>[//|y]; rewrite fsemE dualso_trlfEV. Qed.
Global Arguments Ax_In_G [pt st S v P].

Lemma Ax_UT_G pt st S (U : 'FU[H]_S) P :
  ⊨g [pt,st] { [obs of (liftfso (unitaryso U))^*o P] } (unitary_ U) { P }.
Proof. by case: st; apply/no_while_enoughg=>[//|y]; rewrite fsemE dualso_trlfEV. Qed.
Global Arguments Ax_UT_G [pt st S U P].

Lemma R_IF_G pt st (F: finType) (S : {set L}) (M : 'QM[H]_(F;S)) (f : F -> cmd_)
  (P : F -> 'FO[H]_setT) Q :
  (forall i, ⊨g [pt , st] { P i } (f i) { Q }) ->
  ⊨g [pt , st] { [obs of dualqm (liftf_fun M) P] } (cond_ M f) { Q }.
Proof.
case: pt. case: st=>P1 x/=; rewrite fsemE -dualqm_trlfEV ifso_elemE linear_sumr/= 
  linear_sum/= ?ler_sum//; first apply eq_bigr; move=>i _; rewrite comp_soE; apply P1.
move=>P1; rewrite partial_alter_G fsemE; case: st P1=>P1 x;
rewrite -dualqm_trlfEV ifso_elemE -(elemso_trlf [QM of (liftf_fun M)] x) 
  ?ler_subr_addl linear_sumr/= -?linearN/= !linear_sum/= -!big_split/= ?ler_sum//;
  first apply eq_bigr; move=>i _; rewrite ?linearN/= -?ler_subr_addl comp_soE;
  by move: (P1 i); rewrite partial_alter_G=>/(_ [den of elemso (liftf_fun M) i x]).
Qed.
Global Arguments R_IF_G [pt st F S M f P Q].

Lemma R_SC_G pt st Q P R c1 c2 :
  ⊨g [pt,st] { P } c1 { Q } -> ⊨g [pt,st] { Q } c2 { R } -> 
    ⊨g [pt,st] { P } (seqc_ c1 c2) { R }.
Proof.
case: st; case: pt=>P1 P2 x; rewrite fsemE comp_soE; [rewrite P1 | rewrite -P1 
| apply: (le_trans (P1 x)) | apply: (le_trans _ (P1 x))]; apply P2.
Qed.
Global Arguments R_SC_G [pt st] Q [P R c1 c2].

Lemma R_Or_G pt P Q P' Q' c :
  (P' ⊑ P) -> (Q ⊑ Q') -> ⊨g[pt] { P } c { Q } -> ⊨g[pt] { P' } c { Q' }.
Proof.
case: pt; first by move=>/lef_trden P1 /lef_trden P2 IH x;
  apply/(le_trans (P1 x))/(le_trans (IH x)); apply: P2. 
rewrite !leEsub/= cplmt_lef=>/lef_trden P1.
rewrite cplmt_lef=>/lef_trden P2 IH x; 
apply/(le_trans _ (P1 x))/(le_trans _ (IH x)).
by move: (P2 [den of (fsem c) x]).
Qed.
Global Arguments R_Or_G [pt] P Q [P' Q' c].

Lemma R_LP_GP (S : {set L}) (M : 'QM_(bool;S)) b (D: cmd_)
(P : bool -> 'FO[H]_setT) :
  ⊨pg { P b } D { [obs of dualqm (liftf_fun M) P] } ->
    ⊨pg { [obs of dualqm (liftf_fun M) P] } (while_ M b D) { P (~~b) }.
Proof.
set R := dualqm (liftf_fun M) P.
move=>P1 x; rewrite [in X in _ <= X]/= fsemE.
set f := (lftrace (H:=Hs H setT) \o comp_lfun (cplmt (P (~~b))))%FUN.
have sf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
suff: forall i, f (whileso_iter (liftf_fun M) b (fsem D) i x) <= \Tr (cplmt R \o x).
by move=>/(while_sf_le_cst sf)/=.
move=>n. suff Pn : ⊨pg { [obs of R] } (while_iter_ M b D n) { P (~~b) }.
by move: (Pn x); rewrite fsem_while_iter_.
elim: n=>[y|n IH/=]; first by rewrite fsemE soE comp_lfun0r -(comp_lfun0l _ y);
  apply/lef_trden/obsf_ge0.
apply/R_IF_G=>b'; case: eqP=>[->|/not_eqb->]; [apply (R_SC_G _ P1 IH) | apply/Ax_Sk_G].
Qed.
Global Arguments R_LP_GP [S M b D P].

Local Open Scope classical_set_scope.

(* introduce ranking function ?? do it in lfrepresent.v? *)
Lemma R_LP_GT (S : {set L}) (M : 'QM_(bool;S)) b (D: cmd_)
(P : bool -> 'FO[H]_setT) :
(exists t, ranking_function [TN of (liftf_fun M)] b [QO of fsem D] 
  ([obs of (elemso (liftf_fun M) b)^*o (P b)]) t) ->
  ⊨tg { P b } D { [obs of dualqm (liftf_fun M) P] } ->
    ⊨tg { [obs of dualqm (liftf_fun M) P] } (while_ M b D) { P (~~b) }.
Proof.
set R := (dualqm (liftf_fun M) P).
move=>+P2 x. move=>/rankingP /(_ x)/=.
set cf:= (fun n => \Tr ((elemso (liftf_fun M) b) ^*o (P b) \o 
  whileso_incr (liftf_fun M) b (fsem D) n x)).
move=>cvgcf.
set f := (lftrace (H:=Hs H setT) \o comp_lfun ((P (~~b))))%FUN.
have sf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
set cg:= (fun n=>\Tr (R \o x) - cf n).
set cg1 := [sequence if (n <= 0)%N then (fun i:nat=>0) n else [sequence cg (k - 1)%N]_k n]_n.
have: cg1 --> \Tr (R \o x). rewrite cvg_restrict cvg_centern -[X in _ --> X]subr0. 
apply ccvgB. apply: cvg_cst. by []. rewrite ccvg_limE=>[[P1 P3]].
have scf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
suff: forall i, cg1 i <= f (whileso_iter (liftf_fun M) b (fsem D) i x).
move=>/(while_sf_ge scf P3); by rewrite fsemE P1 /f/=.
move=>i. case: i=>[|i]. by rewrite /cg1/f/= soE comp_lfun0r linear0.
elim: i=>[|i]. by rewrite /cg1/cg/cf/f/R/= dualqmE ler_subl_addl soE (ifso_bool b)
  (big_boolb b)/= eqxx neqb !comp_so0l comp_so1l add0r linearDl/= linearD/= dualso_trlfEV.
have P5: forall n, cg1 n.+1 = cg n by move=>n; rewrite /cg1/= -addn1 addnK.
rewrite !P5 /cg !ler_subl_addl=>P6. apply (le_trans P6).
rewrite [in X in _ <= X]whileso_iterE. set t:= (whileso_iter (liftf_fun M) b (fsem D) i.+1 x).
rewrite /cf soE soE. set s:= (whileso_incr (liftf_fun M) b (fsem D) i x).
have ->: whileso_incr (liftf_fun M) b (fsem D) i.+1 x = ((fsem D) :o (elemso (liftf_fun M) b)) s.
by rewrite whileso_incrE !comp_soE.
rewrite /f/= comp_lfunDr linearD/= [X in _<=_+X]addrC addrA ler_add2r.
rewrite /= -!dualso_trlfEV.
move: (P2 [den of (elemso (liftf_fun M) b) s])=>/=.
by rewrite /R dualqmE (big_boolb b)/= linearDl/= linearD/= -!dualso_trlfEV !comp_soE.
Qed.
Global Arguments R_LP_GT [S M b D P].

End GlobalHoare.

Section PDsystemComplete.

(* definition of wlpqo *)
Local Notation "'FO" := ('FO[H]_setT).
Definition wlpso (E: 'SO[H]_setT) P := ((E^*o (P^⟂))^⟂).

Lemma wlpso_trE P (E: 'SO[H]_setT) x :
  \Tr ((wlpso E P)^⟂ \o x) = \Tr (P^⟂ \o E x).
Proof. by rewrite /wlpso cplmtK -dualso_trlfEV. Qed.

Lemma wlpso_least (E: 'SO[H]_setT) P Q :
  (forall (x : 'FD[H]_setT), \Tr (P^⟂ \o E x) <= 
  \Tr (Q^⟂ \o x)) -> Q ⊑ (wlpso E P).
Proof. 
move=>H1. rewrite cplmt_lef. apply/lef_trden=>x.
apply: (le_trans _ (H1 x)). by rewrite wlpso_trE.
Qed.

Lemma wlpso_saturated (E: 'SO_setT) P Q :
  (forall (x : 'FD[H]_setT), \Tr (P^⟂ \o E x) = 
  \Tr (Q^⟂ \o x)) -> Q = (wlpso E P).
Proof.
move=>H1; apply/le_anti/andP; split; rewrite cplmt_lef; apply/lef_trden=>x.
by rewrite -[X in _ <= X]H1 wlpso_trE. by rewrite -[X in X <= _]H1 wlpso_trE.
Qed.

Lemma wlpso_preserve_order (E: 'CP[H]_setT) P Q :
  P ⊑ Q -> wlpso E P ⊑ wlpso E Q.
Proof. by rewrite /wlpso -cplmt_lef cplmt_lef; apply/cp_preserve_order. Qed.

Definition wlp (c: cmd_) (P : 'FO) := [obs of wlpso (fsem c) P].
Lemma wlpE (c: cmd_) (P : 'FO) : wlpso (fsem c) P = wlp c P. by []. Qed.
Lemma wlp_valid (c: cmd_) (P : 'FO) : ⊨pg { wlp c P } c { P }.
Proof. by move=>x; rewrite /wlp -wlpso_trE. Qed.
Lemma wlp_least (c: cmd_) P Q : ⊨pg { Q } c { P } -> Q ⊑ (wlp c P).
Proof. by move=>P1; apply/wlpso_least/P1. Qed.
Lemma wlp_preserve_order (c: cmd_) (P Q: 'FO) :
  P ⊑ Q -> wlp c P ⊑ wlp c Q.
Proof. rewrite /wlp. apply/wlpso_preserve_order. Qed. 

(* structure property of wlp *)

Lemma wlp_Ab P : wlp abort_ P = [obs of \1].
Proof. by rewrite -obsfP/=/wlpso fsemE dualso0 soE cplmt0. Qed.

Lemma wlp_Sk P : wlp skip_ P = P.
Proof. by rewrite -obsfP/=/wlpso fsemE dualso1 soE cplmtK. Qed.

Lemma wlp_In S (v : 'NS_S) P : 
  wlp (init_ v) P = [obs of (liftfso (initialso v))^*o P].
Proof. by rewrite -obsfP/=/wlpso fsemE cplmt_dualC/= cplmtK. Qed.

Lemma wlp_UT S (U : 'FU[H]_S) P : 
  wlp (unitary_ U) P = [obs of (liftfso (unitaryso U))^*o P].
Proof. by rewrite -obsfP/=/wlpso fsemE cplmt_dualC/= cplmtK. Qed.

Lemma wlp_SC c1 c2 P : 
  wlp (seqc_ c1 c2) P = wlp c1 (wlp c2 P).
Proof. by rewrite -obsfP/wlp/wlpso/= fsemE cplmtK dualso_comp comp_soE. Qed.

Lemma elemso_dual_sum (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) :
  \sum_i (elemso f i)^*o = (krausso f)^*o.
Proof. by apply/superopP=>x; rewrite dualsoE soE; under eq_bigr do rewrite dualsoE. Qed.

Lemma wlp_If (F: finType) (S : {set L}) (M : 'QM_(F;S)) (f : F -> cmd_)
  P : wlp (cond_ M f) P = [obs of dualqm (liftf_fun M) (fun i=>wlp (f i) P)].
Proof.
rewrite -obsfP/=/wlpso fsemE dualso_if dualqmE soE /cplmt linear_sum/=.
under eq_bigr do rewrite dualso_comp soE.
under [RHS]eq_bigr do rewrite linearB/=.
by rewrite [RHS]big_split/= -sum_soE elemso_dual_sum [X in _ = X + _]dual_qc1_eq1.
Qed.

(* what we need is the fixpoint equation of while *)
(* we don't need to give the explicit form of wlp while, though we can... *)
Lemma while_fsem_fp S (M : 'QM_(bool;S)) b (c: cmd_) :
  fsem (while_ M b c) = fsem (cond_ M 
    (fun b'=> if b' == b then seqc_ c (while_ M b c)
    else skip_)).
Proof.
rewrite !fsemE/= whileso_fixpoint. f_equal.
by apply/funext=>b'; case: eqP=>_; rewrite !fsemE.
Qed.

Lemma wlp_eqfsem (c1 c2 : cmd_) (P : 'FO) : 
  fsem c1 = fsem c2 -> wlp c1 P = wlp c2 P.
Proof. by move=>ef; rewrite -obsfP/= ef. Qed.

Lemma wlp_LP S (M : 'QM_(bool;S)) b (c: cmd_) P : 
  wlp (while_ M b c) P = [obs of dualqm (liftf_fun M) 
    (fun b'=> if b'==b then (wlp c (wlp (while_ M b c) P)) else P)].
Proof.
rewrite {1}(wlp_eqfsem _ (while_fsem_fp M b c)) wlp_If -obsfP/=.
f_equal; apply/funext=>b'; case: eqP=>_.
by rewrite -wlp_SC. by rewrite -[in RHS](wlp_Sk P).
Qed.

(* Completeness: wlp can be derived by PDsystem *)
(* shall I define deductive formulas as inductive type? *)
(* this part is trivial by above lemmas *)

End PDsystemComplete.

Section TDsystemComplete.

Local Notation "'FO" := ('FO[H]_setT).
(* definition of wpso *)
Definition wpso (E: 'SO[H]_setT) P := (E^*o P).

Lemma wpso_trE P (E: 'SO_setT) x :
  \Tr ((wpso E P) \o x) = \Tr (P \o E x).
Proof. by rewrite /wpso dualso_trlfEV. Qed.

Lemma wpso_least (E: 'SO_setT) P Q :
  (forall (x : 'FD[H]_setT), \Tr (Q \o x) <= 
  \Tr (P \o E x)) -> Q ⊑ (wpso E P).
Proof. by move=>H1; apply/lef_trden=>x; rewrite /wpso -dualso_trlfEV H1. Qed.

Lemma wpso_saturated (E: 'SO_setT) P Q :
  (forall (x : 'FD[H]_setT), \Tr (Q \o x) = 
  \Tr (P \o E x)) -> Q = (wpso E P).
Proof.
by move=>H1; apply/le_anti/andP; split; 
  apply/lef_trden=>x; rewrite /wpso -dualso_trlfEV H1.
Qed.

Lemma wpso_preserve_order (E: 'CP_setT) P Q :
  P ⊑ Q -> wpso E P ⊑ wpso E Q.
Proof. by rewrite /wpso; apply/cp_preserve_order. Qed.

Definition wp (c: cmd_) (P : 'FO) := [obs of wpso (fsem c) P].
Lemma wpE (c: cmd_) (P : 'FO) : wpso (fsem c) P = wp c P. by []. Qed.
Lemma wp_valid (c: cmd_) P : ⊨tg { wp c P } c { P }.
Proof. by move=>x; rewrite /wp -wpso_trE. Qed.
Lemma wp_least (c: cmd_) P Q : ⊨tg { Q } c { P } -> Q ⊑ (wp c P).
Proof. by move=>P1; apply/wpso_least/P1. Qed.
Lemma wp_preserve_order (c: cmd_) (P Q: 'FO[H]_setT) :
  P ⊑ Q -> wp c P ⊑ wp c Q.
Proof. rewrite /wp. apply/wpso_preserve_order. Qed. 

(* structure property of wp *)

Lemma wp_Ab P : wp abort_ P = [obs of 0].
Proof. by rewrite -obsfP/=/wpso fsemE dualso0 soE. Qed.

Lemma wp_Sk P : wp skip_ P = P.
Proof. by rewrite -obsfP/=/wpso fsemE dualso1 soE. Qed.

Lemma wp_In S (v : 'NS_S) P : 
  wp (init_ v) P = [obs of (liftfso (initialso v))^*o P].
Proof. by rewrite -obsfP/= fsemE. Qed.

Lemma wp_UT S (U : 'FU[H]_S) P : 
  wp (unitary_ U) P = [obs of (liftfso (unitaryso U))^*o P].
Proof. by rewrite -obsfP/= fsemE. Qed.

Lemma wp_SC c1 c2 P : 
  wp (seqc_ c1 c2) P = wp c1 (wp c2 P).
Proof. by rewrite -obsfP/= fsemE /wpso dualso_comp soE. Qed.

Lemma wp_If (F: finType) (S : {set L}) (M : 'QM_(F;S)) (f : F -> cmd_)
  P : wp (cond_ M f) P = [obs of dualqm (liftf_fun M) (fun i=>wp (f i) P)].
Proof.
rewrite -obsfP/=/wpso fsemE dualso_if dualqmE soE; apply eq_bigr=>i _.
by rewrite dualso_comp soE.
Qed.

Lemma wp_eqfsem (c1 c2 : cmd_) (P : 'FO) : 
  fsem c1 = fsem c2 -> wp c1 P = wp c2 P.
Proof. by move=>ef; apply/val_inj; rewrite /= ef. Qed.

(* deduction step *)
Lemma wp_LP1 S (M : 'QM_(bool;S)) b (c: cmd_) P : 
  wp (while_ M b c) P = 
  [obs of dualqm (liftf_fun M) (fun b'=>
    if b'==b then (wp c (wp (while_ M b c) P))
    else P)].
Proof.
rewrite {1}(wp_eqfsem _ (while_fsem_fp M b c)) wp_If.
apply/val_inj=>/=; f_equal; apply/funext=>b'; case: eqP=>_.
by rewrite -wp_SC. by rewrite -[in RHS](wp_Sk P).
Qed.

(* existence of ranking function *)
Lemma wp_LP2 S (M : 'QM_(bool;S)) b (c: cmd_) P : 
  (exists t, ranking_function [TN of (liftf_fun M)] b [QO of fsem c] 
    ([obs of (elemso (liftf_fun M) b)^*o (wp c (wp (while_ M b c) P))]) t).
Proof.
apply rankingP=> x/=; rewrite fsemE.
set f := (lftrace (H:=Hs H setT) \o comp_lfun (P))%FUN.
have sf: scalar f by move=>a b' d; rewrite /f/= linearPr/= linearP/=.
set cc := (fun n: nat=> (\Tr (P \o whileso (liftf_fun M) b (fsem c) x))).
set cf := [sequence (fun i=> f (whileso_iter (liftf_fun M) b (fsem c) i x)) n.+1]_n.
have ->: (fun n : nat => \Tr ((elemso (liftf_fun M) b) ^*o
  (wpso (fsem c) (wpso (whileso (liftf_fun M) b (fsem c)) P)) \o
  whileso_incr (liftf_fun M) b (fsem c) n x)) = (fun n=>cc n - cf n).
apply/funext=>i; rewrite /wpso -dualso_trlfEV -dualso_trlfEV -!comp_soE 
  -whileso_incrE -dualso_trlfEV -comp_soE/= -whileso_incrED whileso_incr_while/=.
by rewrite /cc/cf/f/= !soE linearBr linearB/=.
have P1: (cc --> (\Tr (P \o whileso (liftf_fun M) b (fsem c) x)))%classic by apply: cvg_cst. 
rewrite -(subrr (\Tr (P \o whileso (liftf_fun M) b (fsem c) x))). apply ccvgB.
by []. rewrite cvg_shiftS. 
move: (@while_sf_cvg _ [TN of (liftf_fun M)] b [QO of (fsem c)] _ x sf); by rewrite {4}/f/=.
Qed.

End TDsystemComplete.

(* doing things locally *)
(* remark : try not keep denlf obslf *)
Section LocalHoare.

Lemma eq_trden (V : chsType) (f g : 'End(V)) : 
  reflect (forall x : 'FD(V), \Tr (f \o x) = \Tr (g \o x)) (f == g).
Proof.
apply/(iffP eqP)=>[->//| IH]; apply/le_anti/andP;
by split; apply/lef_trden=>x; rewrite IH.
Qed.

Lemma hoare_wp pt st S T (P: 'F[H]_S) (Q: 'F[H]_T) (c: cmd_) :
  ⊨l [pt,st] {P} c {Q} <-> 
  if pt then
    if st then liftf_lf P = (fsem c)^*o (liftf_lf Q)
          else liftf_lf P ⊑ (fsem c)^*o (liftf_lf Q)
  else
    if st then liftf_lf (P - \1) = (fsem c)^*o (liftf_lf (Q - \1))
          else liftf_lf (P - \1) ⊑ (fsem c)^*o (liftf_lf (Q - \1)).
Proof.
case: pt; case: st; (split=>[IH| + x]).
apply/eqP/eq_trden. 3:apply/lef_trden.
1,3: by move=>x; move: (IH x); rewrite dualso_trlfEV.
1,2: rewrite dualso_trlfEV. by move=>->. by move=>/lef_trden.
apply/eqP/eq_trden. 3:apply/lef_trden.
1,3: move=>x; move: (IH x).
all: rewrite dualso_trlfEV /cplmt -![\1 - _]opprB !linearN/= !comp_lfunNl !linearN/=.
by move=>/esym/oppr_inj. 1,3: rewrite ler_opp2//.
by move=>/lef_trden. by move=>->.
Qed.

Lemma no_while_enoughl st pt c S T (P: 'F[H]_S) (Q: 'F[H]_T) : no_while c ->
  ⊫tl { P } c { Q } -> ⊨l [pt,st] { P } c { Q }.
Proof. by move=>P1; case: pt=>//; rewrite ?no_while_LPT// =>/saturated_strong_L. Qed.
Global Arguments no_while_enoughl [st pt c S T P Q].

Lemma local_hoareP pt st S T (P: 'FO[H]_S) (c: cmd_) (Q: 'FO[H]_T) :
  ⊨l [pt,st] { P } c { Q } -> ⊨g [pt,st] { [obs of liftf_lf P] } c { [obs of liftf_lf Q] }.
Proof. by move=>IH x; move: (IH x); rewrite -?liftf_lf_cplmt. Qed.
Global Arguments local_hoareP [pt st S T P c Q].

Lemma lec_eq (x y : C) : x = y -> x <= y.
Proof. by move=>->. Qed. 

Lemma cplmtZ (U : chsType) (P : 'End(U)) a :
  (a *: P)^⟂ = (1-a)*:\1 + a *: P^⟂.
Proof. by rewrite -!cplmtE scalerBl scalerBr scale1r addrA addrNK. Qed.

Lemma alter_LPT st S T (P : 'F[H]_S) (Q : 'F[H]_T) (c: cmd_) :
  ⊨pl [st] { P } c { Q } <-> ⊨tl [st] { P - \1 } c { Q - \1 }.
Proof. by rewrite !hoare_wp. Qed.

Lemma alter_LTP st S T (P : 'F[H]_S) (Q : 'F[H]_T) (c: cmd_) :
  ⊨tl [st] { P } c { Q } <-> ⊨pl [st] { \1 + P } c { \1 + Q }.
Proof. by rewrite alter_LPT addrC addKr addrC addKr. Qed.

Lemma Ax_00_LP S T (c: cmd_) :
  ⊨pl { (0 : 'F_S) } c { (0 : 'F_T) }.
Proof.
by move=>x; rewrite !cplmt0 !liftf_lf1 dualso_trlfEV; apply/lef_trden/dual_qo1_le1.
Qed.

Lemma Ax_N1N1_LT S T (c: cmd_) :
  ⊨tl { (-\1 : 'F_S) } c { (-\1 : 'F_T) }.
Proof. rewrite alter_LTP !subrr; apply Ax_00_LP. Qed.

Lemma Ax_00_LT st S T (c: cmd_) :
  ⊨tl [st] { (0 : 'F_S) } c { (0 : 'F_T) }.
Proof. by move=>x; rewrite !linear0 !comp_lfun0l; case: st. Qed.

(* rules for local total correctness *)
Lemma Ax_Ab_LT st T S (P: 'F[H]_S) : ⊨tl[st] { (0 : 'F_T) } abort_ { P }.
Proof. by case: st=>x; rewrite fsemE soE linear0 comp_lfun0r comp_lfun0l linear0. Qed.
Global Arguments Ax_Ab_LT [st T S P].

Lemma Ax_Ab_LP st T S (P: 'F[H]_S) : ⊨pl[st] { (\1 : 'F_T) } abort_ { P }.
Proof. by case: st=>x; rewrite fsemE soE cplmt1 linear0 comp_lfun0r comp_lfun0l linear0. Qed.
Global Arguments Ax_Ab_LP [st T S P].

Lemma Ax_Sk_L pt st S (P: 'F[H]_S) : ⊨l[pt,st] { P } skip_ { P }.
Proof. by apply/no_while_enoughl=>//x; rewrite fsemE soE. Qed.
Global Arguments Ax_Sk_L [pt st S P].

Lemma Ax_In_L pt st S (v : 'NS[H]_S) (F : finType) (onb : 'ONB[H]_(F;S)) T (P: 'F[H]_T) : 
  ⊨l [pt, st] { \sum_i [> onb i ; v <] \O P \O [> v ; onb i <] } (init_ v) { P }.
Proof.
apply/no_while_enoughl=>//x/=; rewrite fsemE dualso_trlfEV -(initialso_onb v onb); 
do !f_equal; rewrite liftfso_krausso dualso_krausE/= liftf_funE linear_sum/=.
by apply eq_bigr=>i _; rewrite -liftf_lf_adj adj_outp !liftf_lf_sdot.
Qed.
Global Arguments Ax_In_L [pt st S v F] onb [T P].

Lemma Ax_InF_L pt st T S (v : 'NS[H]_S) : 
  ⊨l [pt,st] { (\1 : 'F_T) } (init_ v) { [> v ; v <] }.
Proof.
apply/no_while_enoughl=>//x/=; rewrite liftf_lf1 fsemE 
  dualso_trlfEV liftfso_krausso dualso_krausE/= liftf_funE.
under eq_bigr do rewrite -liftf_lf_adj -!liftf_lf_comp adj_outp !(outp_comp, ns_dot, scale1r).
by rewrite -linear_sum/= sumonb_out liftf_lf1.
Qed.
Global Arguments Ax_InF_L [pt st T S v].

Lemma Ax_UT_L pt st S (U : 'FU[H]_S) T (P: 'F[H]_T) :
  ⊨l [pt,st] { U^A \O P \O U} (unitary_ U) { P }.
Proof.
apply/no_while_enoughl=>//x/=; rewrite fsemE dualso_trlfEV liftfso_formso.
do !f_equal; by rewrite dualso_formE/= !liftf_lf_sdot liftf_lf_adj.
Qed.
Global Arguments Ax_UT_L [pt st S U T P].

Lemma Ax_UTF_L pt st S (U : 'FU[H]_S) T (P: 'F[H]_T) :
  ⊨l [pt,st] { P } (unitary_ U) { U \O P \O U^A }.
Proof.
apply/no_while_enoughl=>//x/=; rewrite fsemE dualso_trlfEV liftfso_formso.
do !f_equal; rewrite dualso_formE/= !liftf_lf_sdot -liftf_lf_adj.
rewrite !comp_lfunA -liftf_lf_comp -!comp_lfunA -liftf_lf_comp unitaryf_form.
by rewrite !liftf_lf1 comp_lfun1l comp_lfun1r.
Qed.
Global Arguments Ax_UTF_L [pt st S U T P].

Lemma R_IF_L pt st (F: finType) S (M : 'QM[H]_(F;S)) (f : F -> cmd_) T
  (P : F -> 'F[H]_T) W (Q : 'F[H]_W):
  (forall i, ⊨l [pt,st] { P i } (f i) { Q }) ->
  ⊨l [pt,st] { \sum_i (M i)^A \O P i \O M i} (cond_ M f) { Q }.
Proof.
case: pt.
- case: st=>IH x/=; rewrite fsemE ifso_elemE linear_sumr linear_sum/=;
  rewrite linear_suml !linear_sum/= ?ler_sum//; first apply eq_bigr; move=>i _;
  move: (IH i [den of elemso (liftf_fun M) i x])=>/= P1;
  rewrite soE liftf_funE !liftf_lf_sdot -?P1; last apply/(le_trans _ P1)/lec_eq;
  by rewrite soE liftf_lf_adj !comp_lfunA lftraceC !comp_lfunA.
have P0: liftf_lf (\sum_i (M i)^A \O P i \O M i)^⟂ = 
  \sum_i liftf_lf ((M i)^A \O (P i)^⟂ \O M i).
  rewrite /cplmt linearB/= liftf_lf1 linear_sum/=.
  under [RHS]eq_bigr do rewrite sdotfBr sdotfBl linearB/=.
  rewrite big_split/= linear_sum/=; f_equal.
  rewrite -(qm_tpE [QM of liftf_fun M]); apply eq_bigr=>i _.
  by rewrite /= liftf_funE !liftf_lf_sdot liftf_lf1 comp_lfun1r liftf_lf_adj.
case: st=>IH x/=; rewrite fsemE ifso_elemE linear_sumr linear_sum/= P0;
rewrite linear_suml linear_sum/= ?ler_sum//; first apply eq_bigr; move=>i _;
move: (IH i [den of elemso (liftf_fun M) i x])=>/= P1;
rewrite soE liftf_funE !liftf_lf_sdot ?P1; last apply/(le_trans P1)/lec_eq;
by rewrite soE liftf_lf_adj !comp_lfunA lftraceC !comp_lfunA.
Qed.
Global Arguments R_IF_L [pt st F S M f T P W Q].

Lemma R_SC_L pt st T (Q: 'F[H]_T) S W (P: 'F[H]_S) (R: 'F[H]_W) c1 c2 :
  ⊨l [pt,st] { P } c1 { Q } -> ⊨l [pt,st] { Q } c2 { R } -> 
    ⊨l [pt,st] { P } (seqc_ c1 c2) { R }.
Proof.
case: st; case: pt=>P1 P2 x; rewrite fsemE comp_soE; [rewrite P1 | rewrite -P1 
| apply: (le_trans (P1 x)) | apply: (le_trans _ (P1 x))]; apply P2.
Qed.
Global Arguments R_SC_L [pt st T] Q [S W P] [R c1 c2].

Lemma R_Or_L pt S T (P : 'F[H]_S) (Q : 'F[H]_T) P' Q' c :
  (P' ⊑ P) -> (Q ⊑ Q') -> ⊨l [pt] { P } c { Q } -> ⊨l [pt] { P' } c { Q' }.
Proof.
case: pt; last rewrite cplmt_lef; rewrite -liftf_lf_lef =>/lef_trden P1;
last rewrite cplmt_lef; rewrite -liftf_lf_lef =>/lef_trden P2 IH x.
apply/(le_trans (P1 x))/(le_trans (IH x)).
2: apply/(le_trans _ (P1 x))/(le_trans _ (IH x)).
all: by move: (P2 [den of (fsem c) x]).
Qed.
Global Arguments R_Or_L [pt S T] P Q [P' Q' c].

(* loop for local partial correctness *)
(* P : false Q : true *)
Lemma R_LP_LP (S : {set L}) (M : 'QM[H]_(bool;S)) b (D: cmd_) T 
  (P Q : 'F[H]_T) :
  let R := (M (~~b))^A \O P \O (M (~~b)) + (M b)^A \O Q \O (M b) in 
  R ⊑ \1 -> ⊨pl { Q } D { R } -> ⊨pl { R } (while_ M b D) { P }.
Proof.
rewrite /=. set R := (M (~~b))^A \O P \O (M (~~b)) + (M b)^A \O Q \O (M b).
set P' := fun b' => if b'==b then Q else P.
set R' := \sum_i (M i)^A \O P' i \O M i.
have eqR: R = R' by rewrite /R /R' addrC (big_boolb b)/=/P' eqxx neqb.
move=>PR P1 x; rewrite [in X in _ <= X]/= fsemE.
set f := (lftrace (H:=Hs H setT) \o comp_lfun (liftf_lf P^⟂))%FUN.
have sf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
suff: forall i, f (whileso_iter (liftf_fun M) b (fsem D) i x) <= \Tr (liftf_lf R^⟂ \o x).
by move=>/(while_sf_le_cst sf).
move=>n. suff Pn : ⊨pl { R } (while_iter_ M b D n) { P }.
by move: (Pn x); rewrite fsem_while_iter_.
elim: n=>[y|n IH/=].
rewrite fsemE soE comp_lfun0r linear0 trlfM_ge0// /cplmt -?liftf_lf_ge0.
by rewrite subv_ge0. apply/denf_ge0.
rewrite eqR /R'; apply R_IF_L=>b'; rewrite/P'; case: eqP=>_.
apply (R_SC_L _ P1 IH). apply Ax_Sk_L.
Qed.
Global Arguments R_LP_LP [S M b D T P Q].

Lemma R_LP'_LP (S : {set L}) (M : 'QM[H]_(bool;S)) b (D: cmd_) T 
  (P Q : 'F[H]_T) :
  let R := (M (~~b))^A \O P \O (M (~~b)) + (M b)^A \O Q \O (M b) in 
  P ⊑ \1 -> Q ⊑ \1 -> ⊨pl { Q } D { R } -> ⊨pl { R } (while_ M b D) { P }.
Proof.
move=>/= P1 Q1; apply: R_LP_LP.
rewrite -liftf_lf_lef liftf_lf1 linearD/= !liftf_lf_sdot addrC.
rewrite -(qm_tpE [QM of liftf_fun M]) (big_boolb b)/= lev_add=>[||//];
rewrite -[X in _ ⊑ X \o _](comp_lfun1r)/= liftf_lf_adj liftf_funE lef_form=>//;
by rewrite -(liftf_lf1 _ T) liftf_lf_lef.
Qed.
Global Arguments R_LP'_LP [S M b D T P Q].

(* P : false Q : true *)
(* how to locally represent ranking function? *)
(* Lemma R_LP_LP (S : {set L}) (M : 'QM[H]_(bool;S)) (D: cmd_) T 
  (P Q : 'F[H]_T) :
  let R := (M false)^A \O P \O (M false) + (M true)^A \O Q \O (M true) in 
  
  (exists t, ranking_function (liftf_qm M) (fsem D) (dual_qo_apply (qo_of_qm (liftf_qm M) true) (P true)) t) ->

  R ⊑ \1 -> ⊨pl { Q } D { R } -> ⊨pl { R } (while_ M D) { P }. *)

Lemma R_castl pt st S T S' (eqS : (S = S') * (S = S')) P (Q : 'F_T) c :
  ⊨l [pt,st] { castlf eqS P } c { Q } <-> ⊨l [pt,st] { P } c { Q }.
Proof. by case: eqS=>a b; case: S' / a b=>b; rewrite castlf_id. Qed.
Global Arguments R_castl [pt st S T S' eqS P Q].

Lemma R_castr pt st S T T' (eqT : (T = T') * (T = T')) (P : 'F_S) Q c :
  ⊨l [pt,st] { P } c { castlf eqT Q } <-> ⊨l [pt,st] { P } c { Q }.
Proof. by case: eqT=>a b; case: T' / a b=>b; rewrite castlf_id. Qed.
Global Arguments R_castr [pt st S T T' eqT P Q].

(* frame rule for partial correctness only holds when c is isqc *)
Lemma R_Frame_L pt st W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) c :
  (pt || no_while c) ->
  (0 : 'F__) ⊑ R -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊨l [pt,st] { P } c { Q } -> ⊨l [pt,st] { P \⊗ R } c { Q \⊗ R }.
Proof.
wlog ptt: pt / pt = true => [th_sym|].
case: pt=>P1 P2 P3 P4; last rewrite !no_while_LPT//; by apply th_sym.
rewrite ptt disjointUX=>_ rge0 disc /andP[diss dist].
move: (fsem_local c)=>[E PE].
have subs : S :<=: ~: W by rewrite -disjoints_subset.
have subt : T :<=: ~: W by rewrite -disjoints_subset.
have subc : fvars c :<=: ~: W by rewrite -disjoints_subset.
case: st=>[/wpso_saturated P1 x|/wpso_least P1 x]; rewrite dualso_trlfEV;
[do 2 f_equal | apply/lef_trden];
move: P1; rewrite /wpso PE -(liftf_lf2 subs) -(liftf_lf2 subt) -{1}(liftfso2 subc);
rewrite liftfso_dual liftfsoEf 1?liftf_lf_lef; move: (disjointCX W)=>disw.
move=>/liftf_lf_inj/(f_equal (fun x=>x\⊗ R)).
2: move=>P1; move: (lef_tenfl disw rge0 P1).
all: rewrite -{2}(id_soE R) -dualso1 tenso_correct// -tenso_dual - 1 ?liftf_lf_lef.
1: move=>/(f_equal (fun x=>liftf_lf x)).
all: by rewrite -liftfsoEf -liftfso_dual -(liftsoEl _ disw) !liftfso2 !liftf_lf2_tensl.
Qed.
Global Arguments R_Frame_L [pt st W R S T P Q c].

Lemma R_Frame_LT st W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) c :
  (0 : 'F__) ⊑ R -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊨tl [st] { P } c { Q } -> ⊨tl [st] { P \⊗ R } c { Q \⊗ R }.
Proof. by apply: R_Frame_L. Qed.
Global Arguments R_Frame_LT [st W R S T P Q c].

(* Lemma R_Framel_L pt st W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) c :
  (pt || no_while c) ->
  (0 : 'F__) ⊑ R -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊨l [pt,st] { P } c { Q } -> ⊨l [pt,st] { R \⊗ P } c { R \⊗ Q }.
Proof.
move=>P1 P2 P3 P4 P5; move: (R_Frame_L P1 P2 P3 P4 P5).
by rewrite -tenf_castC R_castl -[_ \⊗ R]tenf_castC R_castr.
Qed.
Global Arguments R_Framel_L [pt st W R S T P Q c]. *)

Lemma R_El_L pt st (W S T : {set _}) (P : 'F[H]_S) (Q : 'F[H]_T) (c: cmd_) :
  [disjoint S & W] ->
  ⊨l [pt,st] { P \⊗ (\1 : 'F_W) } c { Q } <-> ⊨l [pt,st] { P } c { Q }.
Proof. by move=>P1; rewrite /local_hoare !liftf_lf_cplmt liftf_lf_tenf1r. Qed.
Global Arguments R_El_L [pt st] W [S T P Q c].

Lemma R_Er_L pt st (W S T : {set _}) (P : 'F[H]_S) (Q : 'F[H]_T) (c: cmd_) :
  [disjoint T & W] ->
  ⊨l [pt,st] { P } c { Q \⊗ (\1 : 'F_W)} <-> ⊨l [pt,st] { P } c { Q }.
Proof. by move=>P1; rewrite /local_hoare !liftf_lf_cplmt liftf_lf_tenf1r. Qed.
Global Arguments R_Er_L [pt st] W [S T P Q c].

Lemma R_TI_L pt st (W1 W2 : {set _}) S T (P : 'F[H]_S) (Q : 'F[H]_T) (c: cmd_) :
  [disjoint S & W1] -> [disjoint T & W2] ->
    ⊨l [pt,st] { P \⊗ (\1 : 'F_W1) } c { Q \⊗ (\1 : 'F_W2)} <-> ⊨l [pt,st] { P } c { Q }.
Proof. by move=>P1 P2; rewrite R_El_L// R_Er_L. Qed.
Global Arguments R_TI_L [pt st] W1 W2 [S T P Q c].

Lemma R_Scale_LT st S T (P : 'F[H]_S) (Q : 'F[H]_T) (c: cmd_) a :
  0 <= a -> ⊨tl [st] { P } c { Q } -> 
  ⊨tl [st] { a *: P } c { a *: Q }.
Proof.
move=>age0; case: st=>IH x; 
rewrite !linearZ/= !linearZl/= !linearZ/=.
by rewrite (IH x). by rewrite ler_wpmul2l.
Qed.
Global Arguments R_Scale_LT [st S T P Q c].

Lemma R_Add_LT st S T (P1 P2 : 'F[H]_S) (Q1 Q2 : 'F[H]_T) (c: cmd_) :
  ⊨tl [st] { P1 } c { Q1 } -> ⊨tl [st] { P2 } c { Q2 }
    -> ⊨tl [st] { P1 + P2 } c { Q1 + Q2 }.
Proof.
case: st=>IH1 IH2 x; rewrite !linearD/= !linearDl/= !linearD/=.
by rewrite (IH1 x) (IH2 x). by rewrite ler_add.
Qed.
Global Arguments R_Add_LT [st S T P1 P2 Q1 Q2 c].

Lemma R_Sum_LT st I (r : seq I) (Pr : pred I) S T (P : I -> 'F[H]_S)
  (Q : I -> 'F[H]_T) (c : cmd_) :
  (forall i, Pr i -> ⊨tl [st] { P i } c { Q i })
    -> ⊨tl [st] { \sum_(i <- r | Pr i) P i } c 
                  { \sum_(i <- r | Pr i) Q i }.
Proof.
elim/big_rec2: _=>[_|h P1 Q1 Ph IH P2]; first exact: Ax_00_LT.
by apply: R_Add_LT; [apply: P2|apply IH].
Qed.
Global Arguments R_Sum_LT [st I r Pr S T P Q c].

Lemma R_CC_LT st I (r : seq I) (Pr : pred I) S T (P : I -> 'F[H]_S)
  (Q : I -> 'F[H]_T) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨tl [st] { P i } c { Q i })
    -> ⊨tl [st] { \sum_(i <- r | Pr i) (a i *: P i) } c 
                  { \sum_(i <- r | Pr i) (a i *: Q i) }.
Proof.
elim/big_rec2: _=>[_|h P1 Q1 Ph IH P2].
by move=>x; case: st; rewrite !linear0 !comp_lfun0l.
apply: R_Add_LT; last by apply IH.
by apply: R_Scale_LT; move: (P2 _ Ph)=>[].
Qed.
Global Arguments R_CC_LT [st I r Pr S T] P Q a [c].

Lemma R_Scale_LP S T (P : 'F[H]_S) (Q : 'F[H]_T) (c: cmd_) a :
  0 <= a <= 1 -> ⊨pl { P } c { Q } -> 
  ⊨pl { a *: P } c { a *: Q }.
Proof.
move=>/andP[Pa1 Pa2]; rewrite !alter_LPT=>IH.
have H1 W (R : 'F[H]_W) : a *: R - \1 = a *: (R - \1) + (1-a) *: (-\1).
by rewrite scalerBr scalerN scalerBl opprB addrA addrNK scale1r.
rewrite !H1; apply R_Add_LT; apply: R_Scale_LT=>//.
by rewrite subr_ge0. by apply Ax_N1N1_LT.
Qed.
Global Arguments R_Scale_LP [S T P Q c].

Lemma R_CC_LP I (r : seq I) (Pr : pred I) S T (P : I -> 'F[H]_S)
  (Q : I -> 'F[H]_T) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨pl { P i } c { Q i })
    -> (\sum_(i <- r | Pr i) a i <= 1)
      -> ⊨pl { \sum_(i <- r | Pr i) (a i *: P i) } c 
                  { \sum_(i <- r | Pr i) (a i *: Q i) }.
Proof.
move=>P1 P2; rewrite alter_LPT.
suff IH W (R : I -> 'F[H]_W) : (\sum_(i <- r | Pr i) a i *: R i) - \1 = 
\sum_(i <- r | Pr i) a i *: (R i - \1) + (1-\sum_(i <- r | Pr i) a i) *: (-\1).
rewrite !IH; apply R_Add_LT. 
by apply: R_CC_LT=>i /P1; rewrite -alter_LPT.
apply: R_Scale_LT. by rewrite subr_ge0. apply Ax_N1N1_LT.
rewrite scalerN scalerBl opprB scale1r addrA scaler_suml -big_split/=.
by f_equal; apply eq_bigr=>i _; rewrite scalerBr addrNK.
Qed.
Global Arguments R_CC_LP [I r Pr S T] P Q a [c].

Lemma R_lim_L pt st S T (A : nat -> 'F[H]_S) (B : nat -> 'F[H]_T) (c : cmd_) :
  (forall i, ⊨l[pt,st] {A i} c {B i}) -> cvg A -> cvg B ->
    ⊨l[pt,st] {lim A} c {lim B}.
Proof.
move: A B; wlog ptt: pt / pt = true => [th_sym|].
case: pt. by apply th_sym.
move=>A B IH1 cA cB; rewrite alter_LPT.
have P2 W : continuous (fun x : 'F[H]_W => x - \1) by apply: addl_continuous.
suff P1 W (C : nat -> 'F[H]_W) : cvg C ->
lim C - \1 = lim ((fun x : 'F[H]_W => x - \1)\o C)%FUN.
rewrite !P1//. apply: th_sym. by [].
by move=>i/=; rewrite -alter_LPT.
1,2: apply: is_vcvg_mapV=>[|//]; apply P2.
move=>cC; rewrite vlim_mapV=>[|//|//]; apply P2.
rewrite ptt=>A B IH cA cB; rewrite hoare_wp.
rewrite -!linear_lim//=. by apply: linear_is_cvg.
case: st IH=>IH; [congr (lim _); apply/funext=>i/=|apply: lev_lim=>[||i/=]].
1,4: by move: (IH i); rewrite hoare_wp.
all: by do ? [apply: linear_is_cvg=>//].
Qed.
Global Arguments R_lim_L [pt st S T A B c].

Lemma Ax_Inv_LP S (P : 'F[H]_S) (c : cmd_) :
  P ⊑ \1 -> [disjoint fvars c & S] ->
    ⊨pl { P } c { P }.
Proof.
rewrite alter_LPT hoare_wp=>P1 P2; move: (fsem_local c)=>[E ->].
by rewrite liftfso_dual -(liftf_lf_tenf1l (S:=fvars c))//
  -liftf_lf_compT// liftfsoEf_compr 1?disjoint_sym// liftfsoEf !liftf_lf_compT//
  liftf_lf_lef lev_wnbreg2r ?dual_qo1_le1 ?subv_le0.
Qed.

Lemma R_Frame_LP W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) c :
  ((0 : 'F__) ⊑ R) && (R ⊑ \1) -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊨pl { P } c { Q } -> ⊨pl { P \⊗ R } c { Q \⊗ R }.
Proof.
move=>/andP[R1 R2] dis1 dis2.
rewrite !alter_LPT=>IH.
rewrite -[P](addrNK \1) -[Q](addrNK \1) tenfDl [(_+\1)\⊗_]tenfDl.
rewrite -!tenf11 -!addrA -!tenfBr; apply: R_Add_LT.
by apply: R_Frame_LT.
move: dis2; rewrite disjointUX=>/andP[dis2 dis3].
rewrite -![\1\⊗_]tenf_castC R_castl R_castr !(R_El_L,R_Er_L) 1?disjoint_sym//.
by rewrite -alter_LPT; apply: Ax_Inv_LP.
Qed.
Global Arguments R_Frame_LP [W R S T P Q c].

Lemma R_SO_LT pt st S T (P : 'F[H]_S) (Q : 'F_T) c W (E : 'QC_W) :
  ⊨l [pt,st] { P } c { Q } -> [disjoint fvars c & W] ->
  ⊨l [pt,st] { (liftfso E)^*o (liftf_lf P) } c { (liftfso E)^*o (liftf_lf Q) }.
Proof.
move=>+dis; rewrite !hoare_wp; move: (fsem_local c)=>[F->].
rewrite !liftf_lf_id !liftfso_dual !linearB/= !liftf_lf1
  -comp_soE liftfso_compC ?soE=>[//|]; case: pt; case: st.
by move=>->. apply: cp_preserve_order.
move=>/(f_equal (liftfso E ^*o)).
2: move=>/(cp_preserve_order [CP of liftfso E ^*o])=>/=.
all: have H1: liftfso E ^*o \1 = \1 by rewrite -liftfso_dual dual_qc1_eq1.
all: rewrite !linearB/= -!comp_soE -liftfso_compC=>[//|].
all: by rewrite !soE H1.
Qed.

Local Open Scope hspace_scope.
Lemma R_Inner_LT S (u v : 'H_S) (c : cmd_) T W :
  `|u| <= 1 -> 
  ⊫tl { (\1 : 'F[H]_T) } c { [> u ; u <] } ->
  ⊫tl { `|[< u ; v >]| ^+2 *: (\1 : 'F[H]_W) } c { [> v ; v <] }.
move=>Pu P1.
have P2: (fsem c)^*o (liftf_lf [> u ; u <]) = \1.
apply/le_anti/andP; split; apply/lef_trden=>x; move: (P1 x);
by rewrite liftf_lf1 dualso_trlfEV=>->.
move: (leh1 <[u]>). rewrite leh_lef hs2lfE -liftf_lf_lef liftf_lf1.
move=>/(cp_preserve_order [CP of (fsem c)^*o])=>P3.
move: (le_trans P3 (dual_qo1_le1 [QO of (fsem c)])).
rewrite/= hline_def hsE/= !linearZ/= P2 -{2}(scale1r \1) -subv_ge0.
have Pu_neq0: `|u| != 0. case: eqP=>///eqP; rewrite normr_eq0=>/eqP Pt; move: P2; 
by rewrite Pt !linear0=>/eqP; rewrite eq_sym oner_eq0.
rewrite -scalerBl pscalev_lge0 ?ltf01=>[//|].
rewrite subr_ge0 invf_le1 ?exprn_gt0 ?lt_def ?normr_ge0 ?Pu_neq0=>[//|//| P4].
have Pux: `|u| = 1. apply/le_anti; rewrite Pu/=; move: P4; rewrite expr_ge1//.
clear Pu P4. have Pul : <[u]>%:VF = [>u; u<]. 
by rewrite hline_def hsE/= Pux expr1n invr1 scale1r.
have P4: forall w : 'H_S, [< w ; u >] = 0 -> 
  (fsem c)^*o (liftf_lf [> w ; w <]) = 0.
move=>w Po.
have: <[u]> \o <[w]> = 0.
by rewrite !hline_def !hsE/= linearZl/= linearZr/= outp_comp -conj_dotp Po conjC0 scale0r !scaler0.
move=>/suppU_comp0 P4.
move: (leh1 (supph <[u]> `|` supph <[w]>)).
rewrite leh_lef P4 hs2lfE -liftf_lf_lef liftf_lf1=>P5.
have P6: (fsem c) ^*o (liftf_lf (<[u]>%:VF + <[w]>)) ⊑ (fsem c) ^*o \1.
by apply/cp_preserve_order.
have P7: (fsem c) ^*o \1 ⊑ \1 by apply/dual_qo1_le1.
move: (le_trans P6 P7). rewrite -P2 !linearD/= Pul gev_addl=>/psdf_le0/=.
rewrite hline_def hsE/= !linearZ/==>/eqP.
case E: (`|w| == 0). by move: E; rewrite normr_eq0=>/eqP->; rewrite !linear0.
by rewrite scaler_eq0 invr_eq0 expf_eq0 E/==>/eqP.
pose liftv (x : 'H[H]_S) := (castlf (erefl, setUCr _) (v2f x \⊗ (\1 : 'F_(~: S)))).
have P5 (x y : 'H[H]_S) : liftf_lf [> x; y <] = (liftv x) \o (liftv y)^A.
rewrite liftf_lfE castlf_adj mul_cast/= tenf_adj adjf1 -tenf_comp ?disjoint0X//.
by rewrite comp_lfun1l comp_out.
have liftvD (x y : 'H[H]_S) : liftv (x + y) = liftv x + liftv y.
by rewrite /liftv linearD/= tenfDl linearD.
have liftvZ (a : C) (x : 'H[H]_S) : liftv (a *: x) = a *: liftv x.
by rewrite /liftv linearZ/= tenfZl linearZ.
have P6 i (w : 'H_S) : [< w; u >] = 0 -> 
  @krausop _ _ ((fsem c) ^*o) i \o (liftv w) = 0.
move=>/P4; rewrite krausE/==>/eqP; rewrite psumv_eq0=>[j _|].
by rewrite P5 -!comp_lfunA -adjf_comp comp_lfunA formV_ge0.
rewrite -big_all big_andE=>/forallP/=/(_ i).
by rewrite P5 -!comp_lfunA -adjf_comp comp_lfunA formV_eq0=>/eqP.
set v1 := <[u]> v. set v2 := (~` <[u]>) v.
have dv : v = v1 + v2 by move: (hs_vec_dec <[u]> v).
have v2o : [< v2 ; u >] = 0.
move: (memh_proj (~` <[u]>) v). rewrite memhCE hsCK -/v2 hline_def hsE/= 
  Pux expr1n invr1 scale1r outpE scaler_eq0 -[u == 0]normr_eq0 Pux oner_eq0 orbF 
  -[[<_;u>]]conj_dotp=>/eqP->; rewrite conjC0//.
have: (fsem c) ^*o (liftf_lf [> v; v <]) = (fsem c) ^*o (liftf_lf [> v1; v1 <]).
rewrite dv outpDl !outpDr !linearD/= -addrA. apply/subr0_eq.
rewrite addrC !addrA addNr add0r !krausE !big1/= ?addr0//.
1,2,3: move=>i _; rewrite P5 -!comp_lfunA -adjf_comp ?(P6 i v2 v2o).
1,3: by rewrite raddf0 !comp_lfun0r. by rewrite comp_lfunA (P6 i v2 v2o) comp_lfun0l.
rewrite /v1 Pul outpE outpZl outpZr scalerA -normCK !linearZ/= P2=>P7 x.
by rewrite dualso_trlfEV P7 linearZ/= liftf_lf1.
Qed.

Lemma R_PInner_LT S T (u : 'H_(S :|: T)) (v : 'H_S) (F : finType) 
  (onb : 'ONB(F;'H_T)) (c : cmd_) W1 W2 :
  `|u| <= 1 -> [disjoint S & T] ->
  ⊫tl { (\1 : 'F[H]_W1) } c { [> u ; u <] } ->
  ⊫tl { (\sum_i (`|[< v ⊗v (onb i) ; u >]| ^+2)) *: (\1 : 'F[H]_W2) } c { [> v ; v <] }.
Proof.
move=>P1 P2 P3; rewrite -(R_Er_L T)=>[//|].
rewrite -(sumonb_out onb) tenf_sumr scaler_suml.
apply: R_Sum_LT=>i _; rewrite tenf_outp -conj_dotp norm_conjC.
by apply: R_Inner_LT.
Qed.

Lemma lift_hoare pt st S T (P : 'F_S) (Q : 'F_T) (c : cmd_) (W : {set L}) 
  (ls : S :<=: W) (lt : T :<=: W) : 
    ⊨l [pt,st] {P} c {Q} <-> ⊨l [pt,st] {lift_lf ls P} c {lift_lf lt Q}.
Proof.
by split=>IH x; move: (IH x); rewrite -!lift_lf_cplmt 
  /liftf_lf !lift_lf2 !(eq_irrelevance (fintype.subset_trans _ _) (subsetT S))
  !(eq_irrelevance (fintype.subset_trans _ _) (subsetT T)).
Qed.
Global Arguments lift_hoare [pt st S T P Q c W].

Lemma R_PC2_LT st S T (P1 Q1 : 'F_S) (P2 Q2 : 'F_T) (c1 c2 : cmd_) :
  fvars c1 :<=: S -> fvars c2 :<=: T -> [disjoint S & T] ->
  st || ((0%:VF ⊑ P1) && (0%:VF ⊑ P2)) 
  -> ⊨tl [st] {P1} c1 {Q1} -> ⊨tl [st] {P2} c2 {Q2}
  -> ⊨tl [st] {P1 \⊗ P2} (c1;;c2) {Q1 \⊗ Q2}.
Proof.
move=>/fsem_lift[E1 PE1]/fsem_lift[E2 PE2] dis H1.
move=>/hoare_wp+/hoare_wp; case: st H1=>/=H1 IH1 IH2; apply/hoare_wp.
all: rewrite fsemE dualso_comp soE -!liftf_lf_compT=>[//|//|].
all: rewrite PE1 PE2 !liftfso_dual liftfsoEf_compl=>[//|].
all: rewrite liftfsoEf liftfsoEf_compr 1?disjoint_sym=>[//|].
all: move: IH1 IH2; rewrite PE1 PE2 !liftfso_dual !liftfsoEf.
by move=>->->.
by rewrite !liftf_lf_compT=>[//|//|]; rewrite !liftf_lf_lef;
apply: lev_pbreg2; move: H1=>/andP[].
Qed.

Lemma R_PC2_LP S T (P1 Q1 : 'F_S) (P2 Q2 : 'F_T) (c1 c2 : cmd_) :
  fvars c1 :<=: S -> fvars c2 :<=: T -> [disjoint S & T] ->
  0%:VF ⊑ P1 -> Q1 ⊑ \1 -> 0%:VF ⊑ P2 -> Q2 ⊑ \1 -> ⊨pl {P1} c1 {Q1} -> ⊨pl {P2} c2 {Q2}
  -> ⊨pl {P1 \⊗ P2} (c1;;c2) {Q1 \⊗ Q2}.
Proof.
move=>/fsem_lift[E1 PE1]/fsem_lift[E2 PE2] dis H1 H2 H3 H4.
move=>/hoare_wp IH1/hoare_wp IH2; apply/hoare_wp.
move: IH1 IH2; rewrite fsemE dualso_comp soE PE1 PE2 !liftfso_dual.
rewrite !liftfsoEf !liftf_lf_lef !lev_subl_addr=>H5 H6.
have: P1 \⊗ P2 ⊑ (E1 ^*o (Q1 - \1) + \1) \⊗ (E2 ^*o (Q2 - \1) + \1).
by apply: lev_pbreg2; rewrite ?dis?H1?H3?H5?H6.
rewrite tenfDl !tenfDr tenf11 addrA -lev_subl_addr.
have ->: E1^*o (Q1 - \1) \⊗ E2^*o (Q2 - \1) = 
E1^*o Q1 \⊗ E2^*o Q2 - E1^*o \1 \⊗ E2^*o \1 + 
(E1^*o (Q1 - \1) \⊗ (- E2^*o \1) + (- E1^*o\1) \⊗ E2 ^*o (Q2 - \1)).
by apply/eqP; rewrite eq_sym addrA tenfNl tenfNr subr_eq -tenfDl 
  -linearD/= addrNK !linearB/= tenfBl opprB addrA addrNK.
rewrite -addrA -addrA [X in _ - _ + X]addrACA -tenfDr -tenfDl=>H7.
have: P1 \⊗ P2 - \1 ⊑ E1 ^*o Q1 \⊗ E2 ^*o Q2 - E1 ^*o \1 \⊗ E2 ^*o \1.
apply: (le_trans H7). rewrite gev_addl lev_naddl=>[||//].
apply: bregv_le0_ge0=>[//||]. 3: apply: bregv_ge0_le0=>[//||].
1,4: rewrite -opprB linearN/= oppv_le0; apply/cp_ge0; rewrite subv_ge0.
3,4: by rewrite addrC subv_ge0 dual_qo1_le1. apply: H2. apply H4.
rewrite -liftf_lf_lef=>H8; apply: (le_trans H8); rewrite le_eqVlt; apply/orP; left; apply/eqP.
move: {+}dis; rewrite disjoint_sym=>dis1.
by rewrite !linearB/= -tenf11 -!liftf_lf_compT// liftfsoEf_compl// liftfsoEf
  liftfsoEf_compr// liftfsoEf_compl// !liftfsoEf liftfsoEf_compr// liftfsoEf.
Qed.

(* add Parametric Morphism ? *)
End LocalHoare.

Local Open Scope qexpr_scope.
Section DiracHoare.
Implicit Type (S T W Wl Wr: {set L}).

Lemma qexpr_localP pt st S T (P: 'F_S) c (Q: 'F_T) :
  ⊨ [pt,st] { ⌈ P ⌉ } c { ⌈ Q ⌉ } <-> ⊨l [pt,st] { P } c { Q }.
Proof.
split. move=>[S'[T']][/sqr_linP/orP[/eqP<-|/eqP->]][/sqr_linP/orP[/eqP<-|/eqP->]].
by rewrite !linqe_id. 1,2,3: rewrite ?linqe_id !linear0 !qexprE;
rewrite /local_hoare ?cplmt0 ?liftf_lf1 ?linear0//.
move=>H1. exists S. exists T. rewrite !linqe_id; do !split=>//; apply/sqrP.
Qed.
Global Arguments qexpr_localP [pt st S T P c].

Lemma qexpr_sqrP pt st S T (P : {sqr S}) (Q : {sqr T}) c :
  ⊨ [pt,st] { P } c { Q } <-> ⊨l [pt,st] { P S S } c { Q T T }.
Proof. by rewrite -qexpr_localP {1}sqr_linE {1}(sqr_linE Q). Qed.
Global Arguments qexpr_sqrP [pt st S T P Q].

Lemma no_while_enough st pt (c : cmd_) P Q : no_while c ->
  ⊫t { P } c { Q } -> ⊨ [pt,st] { P } c { Q }.
Proof.
by move=>nc [S[T[PS[PT Pl]]]]; exists S; exists T; 
do 2 split=>//; apply/no_while_enoughl.
Qed.
Global Arguments no_while_enough [st pt c P Q].

Lemma R_back pt st (R P Q : 'QE) c :
  R = P -> ⊨ [pt,st] { R } c { Q } -> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments R_back [pt st R P Q c].

Lemma R_forward pt st (R P Q : 'QE) c :
  R = Q -> ⊨ [pt,st] { P } c { R } -> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments R_forward [pt st R P Q c].

Lemma R_eq2 pt st (P' Q' P Q : 'QE) c :
  P' = P -> Q' = Q -> ⊨ [pt,st] { P' } c { Q' } -> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>->->. Qed.
Global Arguments R_eq2 [pt st P' Q' P Q c].

Lemma Ax_Sk pt st S (P : {sqr S}) :
  ⊨ [pt,st] { P } skip_ { P }.
Proof. by rewrite qexpr_sqrP sqr_linE linqe_id; apply Ax_Sk_L. Qed.
Global Arguments Ax_Sk [pt st S].

Lemma Ax_UT pt st S T (U : 'FU[H]_S) (P : {sqr T}) :
  ⊨ [pt,st] { ⌈U^A⌉ ∘ P ∘ ⌈U⌉} (unitary_ U) { P }.
Proof.
rewrite qexpr_sqrP/= sqr_linE/= -!sdot_correct !linqe_id; apply Ax_UT_L.
Qed.
Global Arguments Ax_UT [pt st S T U].

Lemma R_UT pt st (Q : 'QE) S W (U : 'FU[H]_S) (P : {sqr W}) :
  Q = ⌈U^A⌉ ∘ P ∘ ⌈U⌉ -> ⊨ [pt,st] { Q } (unitary_ U) { P }.
Proof. by move=>/esym P1; apply/(R_back P1)/Ax_UT. Qed.
Global Arguments R_UT [pt st Q S W U P].

Lemma Ax_UTF pt st S T (U : 'FU[H]_S) (P : {sqr T}) :
  ⊨ [pt,st] { P } (unitary_ U) {  ⌈U⌉ ∘ P ∘ ⌈U^A⌉ }.
Proof.
rewrite qexpr_sqrP/= sqr_linE/= -!sdot_correct !linqe_id; apply Ax_UTF_L.
Qed.
Global Arguments Ax_UTF [pt st S T U].

Lemma R_UTF pt st (Q : 'QE) S W (U : 'FU[H]_S) (P : {sqr W}) :
  Q = ⌈U⌉ ∘ P ∘ ⌈U^A⌉ -> ⊨ [pt,st] { P } (unitary_ U) { Q }.
Proof. by move=>/esym P1; apply/(R_forward P1)/Ax_UTF. Qed.
Global Arguments R_UTF [pt st Q S W U P].

Lemma tenfI0 S T (f : 'F[H]_S) (g : 'F_T) :
  [disjoint S & T] -> g != 0 -> f \⊗ g = 0 -> f = 0.
Proof. by move=>dis /negPf P1 /eqP; rewrite tenf_eq0// P1 orbF=>/eqP. Qed.

Lemma R_El pt st W S (P : {sqr S}) (Q : 'QE) c :
  [disjoint S & W] ->
  ⊨ [pt,st] { P ⊗ I_ W } c { Q } <-> ⊨ [pt,st] { P } c { Q }.
Proof.
move=>P1; symmetry; rewrite sqr_linE -tenqe_correct; split;
  move=>[S' [T]][/sqr_linP/=/orP[/eqP<-|/eqP P2]]; rewrite ?linqe_id=>[[Pt P3]].
1,2: exists (S :|: W). 3,4: exists S. 
all: exists T; (do 2 ?(split=>//; do 1?apply/sqrP)); rewrite !linqe_id.
1,3: move: P3; by rewrite R_El_L. 
all: move: {+}P2 P3=>->; rewrite linear0 qexprE ?linear0l.
2: have ->: P S S = 0 by apply: (tenfI0 P1 _ P2); rewrite oner_neq0.
all: by rewrite /local_hoare !liftf_lf_cplmt !linear0.
Qed.
Global Arguments R_El [pt st W S P Q c].

Lemma R_Er pt st W T (P : 'QE) (Q : {sqr T}) c :
  [disjoint T & W] ->
  ⊨ [pt,st] { P } c { Q ⊗ I_ W } <-> ⊨ [pt,st] { P } c { Q }.
Proof.
move=>P1; symmetry; rewrite sqr_linE -tenqe_correct; split;
  move=>[S [T']][Ps][/sqr_linP/=/orP[/eqP<-|/eqP P2]]; rewrite ?linqe_id=>P3.
all: exists S. 1,2: exists (T :|: W). 3,4: exists T. 
all: (do 2 ?(split=>//; do 1?apply/sqrP)); rewrite !linqe_id.
1,3: move: P3; by rewrite R_Er_L. 
all: move: {+}P2 P3=>->; rewrite linear0 qexprE ?linear0l.
2: have ->: Q T T = 0 by apply: (tenfI0 P1 _ P2); rewrite oner_neq0.
all: by rewrite /local_hoare !liftf_lf_cplmt !linear0.
Qed.
Global Arguments R_Er [pt st W T P Q c].

Lemma R_TI pt st Wl Wr S T (P : {sqr S}) (Q : {sqr T}) c :
  [disjoint S & Wl] -> [disjoint T & Wr] ->
  ⊨ [pt,st] { P ⊗ I_ Wl } c { Q ⊗ I_ Wr } <-> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>H1 H2; rewrite R_El/= ?R_Er//. Qed.
Global Arguments R_TI [pt st Wl Wr S T P Q c].

Lemma R_Et pt st W S T (P : {sqr S}) (Q : {sqr T}) c :
  [disjoint S :|: T & W] ->
  ⊨ [pt,st] { P ⊗ I_ W } c { Q ⊗ I_ W } <-> ⊨ [pt,st] { P } c { Q }.
Proof. by rewrite disjointUX=>/andP [P1]; move: P1; exact: R_TI. Qed.
Global Arguments R_Et [pt st W S T P Q c].

Lemma R_SC pt st (Q P R : 'QE) c1 c2:
  ⊨ [pt,st] { P } c1 { Q } -> ⊨ [pt,st] { Q } c2 { R } -> 
    ⊨ [pt,st] { P } (seqc_ c1 c2) { R }.
Proof.
move=>[S [T]][Ps [Pt P1]].
rewrite (sqrE Pt) sqr_linE=>[[T' [W [/sqr_linP/=/orP[/eqP P2|/eqP P3] [Pw]]]]].
  case: T' / P2; rewrite linqe_id=>P2; exists S; exists W; 
  by do 2 split=>//; move: P1 P2; exact: R_SC_L.
move: P1; rewrite P3 linear0 qexprE=>P1 P2; exists S; exists W; 
do 2 split=>//; move=>x; move: (P1 x) (P2 [den of fsem c1 x]);
rewrite !cplmt0 !linear0 !liftf_lf1; clear -x; case: pt; case: st;
rewrite fsemE soE/=. 1,3: by move=>->. exact: le_trans.
by move=>+P1; apply: le_trans.
Qed.
Global Arguments R_SC [pt st] Q [P R c1 c2].

Lemma R_Frame pt st W (R : {sqr W}) S (P : {sqr S}) T (Q : {sqr T})  c :
  (pt || no_while c) ->
  (0 : 'F_W) ⊑ R W W -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨ [pt,st] { P } c { Q } -> ⊨ [pt,st] { P ⊗ R } c { Q ⊗ R }.
Proof.
rewrite qexpr_sqrP=>P0 P1 P2 P3 P4; move: (R_Frame_L P0 P1 P2 P3 P4).
by rewrite -qexpr_localP !tenqe_correct -!sqr_linE.
Qed.
Global Arguments R_Frame [pt st W R S P T Q c].

Lemma R_Framel pt st W (R : {sqr W}) S (P : {sqr S}) T (Q : {sqr T}) c :
  (pt || no_while c) ->
  (0 : 'F_W) ⊑ R W W -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] -> 
  ⊨ [pt,st] { P } c { Q } -> ⊨ [pt,st] { R ⊗ P } c { R ⊗ Q }.
Proof. rewrite ![R ⊗ _]tenqC; exact: R_Frame. Qed.
Global Arguments R_Framel [pt st W R S P T Q c].

Lemma R_Frame_T st W (R : {sqr W}) S (P : {sqr S}) T (Q : {sqr T})  c :
  (0 : 'F_W) ⊑ R W W -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨t [st] { P } c { Q } -> ⊨t [st] { P ⊗ R } c { Q ⊗ R }.
Proof. by apply: R_Frame. Qed.
Global Arguments R_Frame_T [st W R S P T Q c].

Lemma R_Framel_T st W (R : {sqr W}) S (P : {sqr S}) T (Q : {sqr T}) c :
  (0 : 'F_W) ⊑ R W W -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] -> 
  ⊨t [st] { P } c { Q } -> ⊨t [st] { R ⊗ P } c { R ⊗ Q }.
Proof. by apply: R_Framel. Qed.
Global Arguments R_Framel_T [st W R S P T Q c].

Lemma R_Frame_P W (R : {sqr W}) S (P : {sqr S}) T (Q : {sqr T})  c :
  ((0 : 'F_W) ⊑ R W W) && (R W W ⊑ \1) -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨p { P } c { Q } -> ⊨p { P ⊗ R } c { Q ⊗ R }.
Proof.
rewrite qexpr_sqrP=>P0 P1 P2 P3; move: (R_Frame_LP P0 P1 P2 P3).
by rewrite -qexpr_localP !tenqe_correct -!sqr_linE.
Qed.
Global Arguments R_Frame_P [W R S P T Q c].

Lemma R_Framel_P W (R : {sqr W}) S (P : {sqr S}) T (Q : {sqr T})  c :
  ((0 : 'F_W) ⊑ R W W) && (R W W ⊑ \1) -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨p { P } c { Q } -> ⊨p { R ⊗ P } c { R ⊗ Q }.
Proof. rewrite ![R⊗_]tenqC; exact: R_Frame_P. Qed.
Global Arguments R_Framel_P [W R S P T Q c].

(* initialization *)
Lemma Ax_In_onb pt st S (v : 'NS_S) (F : finType) (onb : 'QONB_(F;S)) T (P: {sqr T}) : 
  ⊨ [pt,st] { \sum_i (qeform (ketqe v ∗ (onb i)`A) P) } (init_ v) { P }.
Proof.
move: (@Ax_In_L pt st _ v _ [ONB of (qe2onb onb)] _ (P T T))=>/=.
rewrite -qexpr_localP -sqr_linE; apply/R_back.
rewrite linear_sum/=; apply eq_bigr=>i _.
by rewrite !sdot_correct /qeform -sqr_linE -!outerM adjqM adjqK -!ket_adj !qe2vK/=.
Qed.
Global Arguments Ax_In_onb [pt st S v F] onb [T].

Lemma Ax_InF pt st W S (v : 'NS[H]_S) : 
  ⊨ [pt,st] { I_ W } (init_ v) { ⌈ [> v ; v <] ⌉ }.
Proof. by apply/qexpr_sqrP=>/=; rewrite !linqe_id; exact: Ax_InF_L. Qed.
Global Arguments Ax_InF [pt st W S].

(* if , R is provided *)
Lemma R_IF pt st (F: finType) S (M : 'QM[H]_(F;S)) (f : F -> cmd_) T
  (P : F -> {sqr T}) W (Q : {sqr W}) :
  (forall i, ⊨ [pt,st] { P i } (f i) { Q }) ->
  ⊨ [pt,st] { \sum_i (qeform (linqe (M i)) (P i)) } (cond_ M f) { Q }.
Proof.
move=>IH; have P1 i : ⊨l[pt,st] {(P i) T T} (f i) {Q W W}
  by rewrite -qexpr_localP -!sqr_linE.
move: (@R_IF_L pt st _ _ M _ _ _ _ _ P1); rewrite -qexpr_localP -sqr_linE; 
apply/R_back; rewrite linear_sum/=; apply eq_bigr=>i _.
by rewrite !sdot_correct /qeform -sqr_linE lin_adj.
Qed.
Global Arguments R_IF [pt st F S M f T P W Q].

(* while *)
Lemma R_LP_P S (M : 'QM[H]_(bool;S)) b (D: cmd_) T 
  (P Q : {sqr T}) :
  let R := qeform (linqe (M (~~b))) P + qeform (linqe (M b)) Q in 
  P T T ⊑ \1 -> Q T T ⊑ \1 -> ⊨p { Q } D { R } -> ⊨p { R } (while_ M b D) { P }.
Proof.
move=>R PP PQ.
suff ->: R = linqe ((M (~~b))^A \O P T T \O (M (~~b)) + (M b)^A \O Q T T \O (M b)).
rewrite !qexpr_sqrP/= !linqe_id; apply: R_LP'_LP; [apply PP|apply PQ].
by rewrite /R /qeform linearD/= !sdot_correct !lin_adj -!sqr_linE.
Qed.
Global Arguments R_LP_P [S M b D T P Q].

(* move *)
Lemma leqe_elem (P Q : 'QE[H]) : 
  P ⊑ Q -> forall S, P S S ⊑ Q S S.
Proof. by rewrite -subv_ge0=>/geqe0P[+ _]S; move=>/(_ S); rewrite !qexprE subv_ge0. Qed.

Lemma leqe_liftf S W (P : {sqr H | S}) (Q : {sqr W}) :
  (P : 'QE) ⊑ Q -> liftf_lf (P S S) ⊑ liftf_lf (Q W W).
Proof.
case E: (S == W).
by move: E=>/eqP P1; case: W / P1 Q=>Q/leqe_elem/(_ S); rewrite liftf_lf_lef.
move=>P1; move: P1 {+}P1=>/leqe_elem/(_ S)+/leqe_elem/(_ W).
rewrite sqr_linE (sqr_linE Q) !linqe_id !qeset_eq0r ?E// 1?eq_sym ?E//.
rewrite -liftf_lf_lef -[_ ⊑ Q W W]liftf_lf_lef !linear0; exact: le_trans.
Qed.

Lemma leqe_liftf_cplmt S W (P : {sqr H | S}) (Q : {sqr W}) :
  (P : 'QE) ⊑ Q -> liftf_lf (Q W W)^⟂ ⊑ liftf_lf (P S S)^⟂.
Proof. rewrite !liftf_lf_cplmt -cplmt_lef; exact: leqe_liftf. Qed.

Lemma R_Orl pt (P Q : 'QE) S (P' : {sqr S}) (c : cmd_) :
  ((P' : 'QE) ⊑ P) -> ⊨ [pt] { P } c { Q } -> ⊨ [pt] { P' } c { Q }.
Proof.
rewrite sqr_linE =>+[S' [W' [P3 [P4]]]] IH.
rewrite (sqrE P3) (sqrE P4) (sqr_linE (SqrQExpr P4)) qexpr_localP; 
case: pt IH=>[IH/leqe_liftf/lef_trden| IH/leqe_liftf_cplmt/lef_trden];
rewrite !linqe_id=>P1 x.
apply/(le_trans (P1 x))/(le_trans (IH x)).
2: apply/(le_trans _ (P1 x))/(le_trans _ (IH x)).
all: by move: (P1 [den of (fsem c) x]).
Qed.
Global Arguments R_Orl [pt] P Q [S P' c].

Lemma R_Orr pt (P Q : 'QE) S (Q' : {sqr S}) (c : cmd_) :
  (Q ⊑ Q') -> ⊨ [pt] { P } c { Q } -> ⊨ [pt] { P } c { Q' }.
Proof.
rewrite sqr_linE =>+[S' [W' [P3 [P4]]]] IH.
rewrite (sqrE P3) (sqrE P4) (sqr_linE (SqrQExpr P3)) qexpr_localP; 
case: pt IH=>[IH/leqe_liftf/lef_trden| IH/leqe_liftf_cplmt/lef_trden];
rewrite !linqe_id=>P1 x; [apply/(le_trans (IH x))|apply/(le_trans _ (IH x))];
by move: (P1 [den of (fsem c) x]).
Qed.
Global Arguments R_Orl [pt] P Q [S P' c].

Lemma R_Or pt (P Q : 'QE) S W (P' : {sqr S}) (Q' : {sqr W}) (c : cmd_) :
  ((P' : 'QE) ⊑ P) -> (Q ⊑ Q') -> ⊨ [pt] { P } c { Q } -> ⊨ [pt] { P' } c { Q' }.
Proof. by move=>P1 P2 P3; move: (R_Orl _ _ P1 P3); apply: R_Orr. Qed.
Global Arguments R_Or [pt] P Q [S W P' Q' c].

Lemma alter_PT st S T (P : {sqr S}) (Q : {sqr T}) (c: cmd_) :
  ⊨p [st] { P } c { Q } <-> ⊨t [st] { (P : 'QE) - I_ S } c { (Q : 'QE) - I_ T }.
Proof. by rewrite !qexpr_sqrP/= !(linqe_id, qexprE) alter_LPT. Qed.

Lemma alter_TP st S T (P : {sqr S}) (Q : {sqr T}) (c: cmd_) :
  ⊨t [st] { P } c { Q } <-> ⊨p [st] { I_ S + P } c { I_ T + Q }.
Proof. by rewrite alter_PT/= addrC addKr addrC addKr. Qed.

Lemma Ax_00_P (c: cmd_) : ⊨p { 0 } c { 0 }.
Proof. by move: (Ax_00_LP set0 set0 c); rewrite -qexpr_localP/= linear0. Qed.

Lemma Ax_N1N1_T S T (c: cmd_) : ⊨t { - I_ S } c { - I_ T }.
Proof. by rewrite qexpr_sqrP/= !(linqe_id, qexprE); exact: Ax_N1N1_LT. Qed.

Lemma Ax_00_T st (c: cmd_) : ⊨t [st] { 0 } c { 0 }.
Proof. by move: (Ax_00_LT st set0 set0 c); rewrite -qexpr_localP/= linear0. Qed.

Lemma R_Scale_T st (P Q : 'QE) (c: cmd_) a :
  0 <= a -> ⊨t [st] { P } c { Q } -> 
    ⊨t [st] { a *: P } c { a *: Q }.
Proof.
move=>Pa[S [T]][PS [PT IH]].
rewrite (sqrE PS) (sqrE PT) qexpr_sqrP/= !(linqe_id, qexprE).
by apply: R_Scale_LT.
Qed.
Global Arguments R_Scale_T [st P Q c a].

Lemma R_Add_T st S T (P1 P2 : {sqr S}) (Q1 Q2 : {sqr T}) (c: cmd_) :
  ⊨t [st] { P1 } c { Q1 } -> ⊨t [st] { P2 } c { Q2 }
    -> ⊨t [st] { (P1 : 'QE) + P2 } c { (Q1 : 'QE) + Q2 }.
Proof.
rewrite sqr_linE (sqr_linE Q1) (sqr_linE P2) (sqr_linE Q2)
!qexpr_sqrP/= !(linqe_id, qexprE); exact: R_Add_LT.
Qed.
Global Arguments R_Add_T [st S T P1 P2 Q1 Q2 c].

Lemma R_Sum_T st I (r : seq I) (Pr : pred I) S T (P : I -> {sqr S})
  (Q : I -> {sqr T}) (c : cmd_) :
  (forall i, Pr i -> ⊨t [st] { P i } c { Q i })
    -> ⊨t [st] { \sum_(i <- r | Pr i) (P i : 'QE) } c 
                { \sum_(i <- r | Pr i) (Q i : 'QE) }.
Proof.
move=>IH; rewrite qexpr_sqrP/= !qexpr_sumE; 
by apply: R_Sum_LT=>i /IH; rewrite qexpr_sqrP/=.
Qed.
Global Arguments R_Sum_T [st I r Pr S T] P Q [c].

Lemma R_CC_T st I (r : seq I) (Pr : pred I) S T (P : I -> {sqr S})
  (Q : I -> {sqr T}) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨t [st] { P i } c { Q i })
    -> ⊨t [st] { \sum_(i <- r | Pr i) (a i *: (P i : 'QE)) } c 
                  { \sum_(i <- r | Pr i) (a i *: (Q i : 'QE)) }.
Proof. move=>IH; apply: R_Sum_T=>i /IH[]/=; apply/R_Scale_T. Qed.
Global Arguments R_CC_T [st I r Pr S T] P Q a [c].

Lemma R_Scale_P (P Q : 'QE) (c: cmd_) a :
  0 <= a <= 1 -> ⊨p { P } c { Q } -> 
  ⊨p { a *: P } c { a *: Q }.
Proof.
move=>Pa[S [T]][PS [PT IH]].
rewrite (sqrE PS) (sqrE PT) qexpr_sqrP/= !(linqe_id, qexprE).
by apply: R_Scale_LP.
Qed.
Global Arguments R_Scale_P [P Q c].

Lemma R_CC_P I (r : seq I) (Pr : pred I) S T (P : I -> {sqr S})
  (Q : I -> {sqr T}) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨p { P i } c { Q i })
    -> (\sum_(i <- r | Pr i) a i <= 1)
      -> ⊨p { \sum_(i <- r | Pr i) (a i *: (P i : 'QE)) } c 
                  { \sum_(i <- r | Pr i) (a i *: (Q i : 'QE)) }.
Proof.
move=>P1 P2; have: forall i : I, Pr i -> 0 <= a i /\ ⊨pl { P i S S } c { Q i T T }.
by move=>i /P1[]; rewrite qexpr_sqrP/=.
move=>/R_CC_LP/(_ P2); rewrite -qexpr_localP; apply R_eq2; 
by rewrite linear_sum/=; apply eq_bigr=>i _; rewrite linearZ/= -sqr_linE.
Qed.
Global Arguments R_CC_P [I r Pr S T] P Q a [c].

Lemma Ax_Inv_P S (P : {sqr S}) (c : cmd_) :
  P S S ⊑ \1 -> [disjoint fvars c & S] ->
    ⊨p { P } c { P }.
Proof. rewrite qexpr_sqrP; exact: Ax_Inv_LP. Qed.
Global Arguments Ax_Inv_P [S P c].

Lemma R_Inner S (u v : 'H_S) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫t { |1 } c { ⌈ [> u ; u <] ⌉ } ->
  ⊫t { (`|[< u ; v >]| ^+2)%:QE } c { ⌈ [> v ; v <] ⌉ }.
Proof.
by rewrite one1I cplxZ1 one1I !qexpr_sqrP/= !(linqe_id,qexprE); exact: R_Inner_LT.
Qed.

Lemma R_PInner S T (u : 'H_(S :|: T)) (v : 'H_S) (F : finType) 
  (onb : 'ONB(F;'H_T)) (c : cmd_) :
  `|u| <= 1 -> [disjoint S & T] ->
  ⊫t { |1 } c { ⌈ [> u ; u <] ⌉ } ->
  ⊫t { (\sum_i (`|[< v ⊗v (onb i) ; u >]| ^+2))%:QE } c { ⌈ [> v ; v <] ⌉ }.
Proof.
by rewrite one1I cplxZ1 one1I !qexpr_sqrP/= !(linqe_id,qexprE); exact: R_PInner_LT.
Qed.

Lemma R_PC2_T st S1 T1 (P1 : {sqr S1}) (Q1 : {sqr T1})
  S2 T2 (P2 : {sqr S2}) (Q2 : {sqr T2}) (c1 c2 : cmd_) :
  [disjoint fvars c1 :|: S1 :|: T1 & fvars c2 :|: S2 :|: T2] ->
  st || ((0%:VF ⊑ P1 S1 S1) && (0%:VF ⊑ P2 S2 S2)) 
  -> ⊨t [st] {P1} c1 {Q1} -> ⊨t [st] {P2} c2 {Q2}
  -> ⊨t [st] {P1 ⊗ P2} (c1;;c2) {Q1 ⊗ Q2}.
Proof.
set W1 := fvars c1 :|: S1 :|: T1.
set W2 := fvars c2 :|: S2 :|: T2.
move=>dis P IH1 IH2.
have RS1 : S1 :<=: W1 by rewrite /W1 setUAC subsetUr.
have RT1 : T1 :<=: W1 by rewrite /W1 subsetUr.
have RS2 : S2 :<=: W2 by rewrite /W2 setUAC subsetUr.
have RT2 : T2 :<=: W2 by rewrite /W2 subsetUr.
have: ⊨tl[st]{ (lift_lf RS1 (P1 S1 S1)) \⊗ (lift_lf RS2 (P2 S2 S2))} (c1;;c2)
             { (lift_lf RT1 (Q1 T1 T1)) \⊗ (lift_lf RT2 (Q2 T2 T2))}.
apply: R_PC2_LT. 1,2: by rewrite/W1/W2 -setUA subsetUl. by [].
by rewrite -!lift_lf_ge0.
1,2: by rewrite -qexpr_localP !lift_lfE !linqe_cast 
  !tenqe_correct R_TI/= -?sqr_linE// ?disjointXD.
rewrite -qexpr_localP !tenqe_correct !lift_lfE !linqe_cast !tenqe_correct
  tenqACA tenqII tenqACA tenqII R_TI/= -?sqr_linE//.
all: move: dis; rewrite/W1 /W2; fsetdec L.
Qed.

Lemma R_PC2_P S1 T1 (P1 : {sqr S1}) (Q1 : {sqr T1})
  S2 T2 (P2 : {sqr S2}) (Q2 : {sqr T2}) (c1 c2 : cmd_) :
  [disjoint fvars c1 :|: S1 :|: T1 & fvars c2 :|: S2 :|: T2] ->
  0%:VF ⊑ P1 S1 S1 -> Q1 T1 T1 ⊑ \1 -> 0%:VF ⊑ P2 S2 S2 -> Q2 T2 T2 ⊑ \1 
  -> ⊨p {P1} c1 {Q1} -> ⊨p {P2} c2 {Q2}
  -> ⊨p {P1 ⊗ P2} (c1;;c2) {Q1 ⊗ Q2}.
Proof.
set W1 := fvars c1 :|: S1 :|: T1.
set W2 := fvars c2 :|: S2 :|: T2.
move=>dis R1 R2 R3 R4 IH1 IH2.
have RS1 : S1 :<=: W1 by rewrite /W1 setUAC subsetUr.
have RT1 : T1 :<=: W1 by rewrite /W1 subsetUr.
have RS2 : S2 :<=: W2 by rewrite /W2 setUAC subsetUr.
have RT2 : T2 :<=: W2 by rewrite /W2 subsetUr.
have: ⊨pl { (lift_lf RS1 (P1 S1 S1)) \⊗ (lift_lf RS2 (P2 S2 S2))} (c1;;c2)
             { (lift_lf RT1 (Q1 T1 T1)) \⊗ (lift_lf RT2 (Q2 T2 T2))}.
apply: R_PC2_LP. 1,2: by rewrite/W1/W2 -setUA subsetUl. by [].
1,3: by rewrite -lift_lf_ge0. 1,2: by rewrite -lift_lf_le1.
1,2: by rewrite -qexpr_localP !lift_lfE !linqe_cast 
  !tenqe_correct R_TI/= -?sqr_linE// ?disjointXD.
rewrite -qexpr_localP !tenqe_correct !lift_lfE !linqe_cast !tenqe_correct
  tenqACA tenqII tenqACA tenqII R_TI/= -?sqr_linE//.
all: move: dis; rewrite/W1 /W2; fsetdec L.
Qed.

Lemma fvars_for (T : Type) (r : seq T) (P : pred T) (fp : T -> cmd_) :
    fvars [for i <- r | P i do (fp i)] = \bigcup_(i<-r|P i) (fvars (fp i)).
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil/=.
rewrite !big_cons; case: (P x)=>/=; by rewrite IH.
Qed. 

Lemma R_PC_seq_T st (I : eqType) (r : seq I) (R : pred I) (S T : I -> {set L})
  (P : forall i, {sqr (S i)}) (Q : forall i, {sqr (T i)}) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> uniq r ->
  st \/ (forall i, R i -> (0 : 'QE[H]) ⊑ P i)
  -> (forall i, R i -> ⊨t [st] {P i} (c i) {Q i})
  -> ⊨t [st] {\tens_(i <- r | R i) (P i)} [for i <- r | R i do c i] {\tens_(i <- r | R i) (Q i)}.
Proof.
move=>dis+IH1 IH2; elim: r=>[_|a r IH].
rewrite !big_nil bigq; apply: Ax_Sk.
rewrite cons_uniq=>/andP[na ur]; move: {+}ur=>/IH; rewrite !big_cons; case E: (R a)=>//.
rewrite !bigqE; apply: R_PC2_T.
rewrite fvars_for -!big_split/=; apply/bigcup_disjoint_seqP=>i/andP[Pi Ri].
apply: dis=>//. by apply: (notin_in_neq na).
move: IH1=>[->//|Pi]; apply/orP; right. rewrite -!lin_gef0/= -!sqr_linE Pi//=.
apply: tens_ge0_seq=>// i j Ri Rj nij; move: (dis i j Ri Rj nij); fsetdec L.
by apply IH2.
Qed.

Lemma R_PC_T st (I : finType) (r : seq I) (R : pred I) (S T : I -> {set L})
  (P : forall i, {sqr (S i)}) (Q : forall i, {sqr (T i)}) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> 
  st \/ (forall i, R i -> (0 : 'QE[H]) ⊑ P i)
  -> (forall i, R i -> ⊨t [st] {P i} (c i) {Q i})
  -> ⊨t [st] {\tens_(i | R i) (P i)} [for i | R i do c i] {\tens_(i | R i) (Q i)}.
Proof. by move=>??; apply: R_PC_seq_T. Qed.

Lemma R_PC_seq_P (I : eqType) (r : seq I) (R : pred I) (S T : I -> {set L})
  (P : forall i, {sqr (S i)}) (Q : forall i, {sqr (T i)}) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> uniq r ->
  (forall i, R i -> (0 : 'QE[H]) ⊑ P i) ->
  (forall i, R i -> (0 : 'QE[H]) ⊑ (Q i : 'QE) ⊑ I_ (T i)) ->
  (forall i, R i -> ⊨p {P i} (c i) {Q i})
  -> ⊨p {\tens_(i <- r | R i) (P i)} [for i <- r | R i do c i] {\tens_(i <- r | R i) (Q i)}.
Proof.
move=>dis+IH1 IH2; elim: r=>[_ _|a r IH].
rewrite !big_nil bigq; apply: Ax_Sk.
rewrite cons_uniq=>/andP[na ur]; move: {+}ur=>/IH IH3 IH4; 
  rewrite !big_cons; case E: (R a)=>[|//].
rewrite !bigqE; apply: R_PC2_P=>/=.
rewrite fvars_for -!big_split/=; apply/bigcup_disjoint_seqP=>i/andP[Pi Ri].
apply: dis=>//. by apply: (notin_in_neq na).
1,3: rewrite -sqr_gef0 ?IH1//=.
2,3: rewrite -sqr_lef1/=. 2: by move: (IH2 _ E)=>/andP[].
2: suff: (0:'QE) ⊑ \tens_(i <- r | R i) Q i ⊑ I_ (\bigcup_(i <- r | R i) T i)
  by move=>/andP[].
apply: tens_ge0_seq=>//. 2: apply: tens_ge0_le1_seq=>//.
1,2: move=>i j Ri Rj nij; move: (dis i j Ri Rj nij); fsetdec L.
by apply: IH4. all: by apply: IH.
Qed.

Lemma R_PC_P (I : finType) (r : seq I) (R : pred I) (S T : I -> {set L})
  (P : forall i, {sqr (S i)}) (Q : forall i, {sqr (T i)}) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> 
  (forall i, R i -> (0 : 'QE[H]) ⊑ P i) ->
  (forall i, R i -> (0 : 'QE[H]) ⊑ (Q i : 'QE) ⊑ I_ (T i)) ->
  (forall i, R i -> ⊨p {P i} (c i) {Q i})
  -> ⊨p {\tens_(i | R i) (P i)} [for i | R i do c i] {\tens_(i | R i) (Q i)}.
Proof. by move=>??; apply: R_PC_seq_P. Qed.

End DiracHoare.

Section StateHoare.
Implicit Type (S T W Wl Wr: {set L}).

Lemma stateE pt st (P Q : 'QE) c :
  ⊨s [pt,st] { P } c { Q } <-> ⊨ [pt,st] { P ∗ P`A } c { Q ∗ Q`A }.
Proof. by []. Qed.
Global Arguments stateE [pt st P Q].

(* following : specification for states, all predicates are P ∗ P`A *)
(* rules for total correctness *)

Lemma no_while_enoughS st pt (c : cmd_) P Q : no_while c ->
  ⊫ts { P } c { Q } -> ⊨s [pt,st] { P } c { Q }.
Proof. exact: no_while_enough. Qed.
Global Arguments no_while_enoughS [st pt c P Q].

Lemma RS_forward pt st (R P Q : 'QE) c :
  R = Q -> ⊨s [pt,st] { P } c { R } -> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments RS_forward [pt st R P Q c].

Lemma RS_back pt st (R P Q : 'QE) c :
  R = P -> ⊨s [pt,st] { R } c { Q } -> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments RS_back [pt st R P Q c].

Lemma RS_eq2 pt st (P' Q' P Q : 'QE) c :
  P' = P -> Q' = Q -> ⊨s [pt,st] { P' } c { Q' } -> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>->->. Qed.
Global Arguments RS_eq2 [pt st P' Q' P Q c].

Lemma AxS_Sk pt st S T (P : {wf S,T}) :
  ⊨s [pt,st] { P } skip_ { P }.
Proof. apply/Ax_Sk. Qed.
Global Arguments AxS_Sk [pt st S T].

Lemma AxS_UT pt st S (U : 'FU[H]_S) T T' (P : {wf T, T'}) :
  T :<=: T' ->
  ⊨s [pt,st] { ⌈U^A⌉ ∘ P } (unitary_ U) { P }.
Proof.
move=>P1; apply/R_UT; rewrite /= -!dotq_com/= adjqG adjq_lin 
  adjfK !dotqA_cond//=; move: P1; fsetdec L.
Qed.
Global Arguments AxS_UT [pt st S U T T' P].

Lemma AxV_UT pt st S T (U : 'FU[H]_S) (P : {ket T}) :
  ⊨s [pt,st] { ⌈U^A⌉ ∘ P } (unitary_ U) { P }.
Proof. by apply/AxS_UT; rewrite sub0set. Qed.
Global Arguments AxV_UT [pt st S T U].

(* whenever difficult to canonical ⌈U^A⌉ ∘ P *)
Lemma RS_UT pt st (Q : 'QE) S W W' (U : 'FU[H]_S) (P : {wf W,W'}) :
  W :<=: W' ->
  Q = ⌈U^A⌉ ∘ P -> ⊨s [pt,st] { Q } (unitary_ U) { P }.
Proof. by move=>P2 ->; apply/AxS_UT. Qed.
Global Arguments RS_UT [pt st Q S W W' U P].

Lemma RV_UT pt st (Q : 'QE) S W (U : 'FU[H]_S) (P : {ket W}) :
  Q = ⌈U^A⌉ ∘ P -> ⊨s [pt,st] { Q } (unitary_ U) { P }.
Proof. by move=>/esym P1; apply/(RS_back P1)/AxV_UT. Qed.
Global Arguments RV_UT [pt st Q S W U P].

Lemma AxS_UTF pt st S (U : 'FU[H]_S) T T' (P : {wf T, T'}) :
  T :<=: T' ->
  ⊨s [pt,st] { P } (unitary_ U) { ⌈U⌉ ∘ P }.
Proof.
move=>P1; apply/R_UTF; rewrite /= -!dotq_com/=
  adjqG adjq_lin !dotqA_cond//=; move: P1; fsetdec L.
Qed.
Global Arguments AxS_UTF [pt st S U T T' P].

Lemma AxV_UTF pt st S (U : 'FU[H]_S) T (P : {ket T}) :
  ⊨s [pt,st] { P } (unitary_ U) { ⌈U⌉ ∘ P }.
Proof. by apply/AxS_UTF; rewrite sub0set. Qed.
Global Arguments AxV_UTF [pt st S U T] P.

Lemma RS_UTF pt st (P : 'QE) S W W' (U : 'FU[H]_S) (Q : {wf W,W'}) :
  W :<=: W' ->
  P = ⌈U⌉ ∘ Q -> ⊨s [pt,st] { Q } (unitary_ U) { P }.
Proof. by move=>P2 ->; apply/AxS_UTF. Qed.
Global Arguments RS_UTF [pt st P S W W' U Q].

Lemma RV_UTF pt st (P : 'QE) S W (U : 'FU[H]_S) (Q : {ket W}) :
  P = ⌈U⌉ ∘ Q -> ⊨s [pt,st] { Q } (unitary_ U) { P }.
Proof. by move=>/esym P1; apply/(RS_forward P1)/AxV_UTF. Qed.
Global Arguments RV_UTF [pt st P S W U Q].

Lemma RS_El pt st W S S' (P : {wf S,S'}) (Q : 'QE) c :
  [disjoint S :|: S' & W] ->
  ⊨s [pt,st] { P ⊗ I_ W } c { Q } <-> ⊨s [pt,st] { P } c { Q }.
Proof.
rewrite disjointUX !stateE =>/andP[P1 P2].
by rewrite adjqT adjqI tenq_com/= ?comqI/= ?R_El.
Qed.
Global Arguments RS_El [pt st W S S' P Q c].

Lemma RS_Er pt st W T T' (P : 'QE) (Q : {wf T,T'}) c :
  [disjoint T :|: T' & W] ->
  ⊨s [pt,st] { P } c { Q ⊗ I_ W } <-> ⊨s [pt,st] { P } c { Q }.
Proof.
rewrite disjointUX !stateE=>/andP[P1 P2].
by rewrite adjqT adjqI tenq_com/= ?comqI/= ?R_Er.
Qed.
Global Arguments RS_Er [pt st W T T' P Q c].

Lemma RS_TI pt st Wl Wr S S' T T' (P : {wf S,S'}) (Q : {wf T,T'}) c :
  [disjoint S :|: S' & Wl] -> [disjoint T :|: T' & Wr] ->
  ⊨s [pt,st] { P ⊗ I_ Wl } c { Q ⊗ I_ Wr } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>H1 H2; rewrite RS_El/= ?RS_Er. Qed.
Global Arguments RS_TI [pt st Wl Wr S S' T T' P Q c].

Lemma RS_Et pt st W S S' T T' (P : {wf S,S'}) (Q : {wf T,T'}) c :
  [disjoint (S :|: S') :|: (T :|: T') & W] ->
  ⊨s [pt,st] { P ⊗ I_ W } c { Q ⊗ I_ W } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by rewrite disjointUX=>/andP [P1]; move: P1; exact: RS_TI. Qed.
Global Arguments RS_Et [pt st W S S' T T' P Q c].

Lemma RV_El pt st W S (P : {ket S}) (Q : 'QE) c :
  [disjoint S & W] ->
  ⊨s [pt,st] { P ⊗ I_ W } c { Q } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>P1; apply RS_El; rewrite set0U. Qed.
Global Arguments RV_El [pt st W S P Q c].

Lemma RV_Er pt st W T (P : 'QE) (Q : {ket T}) c :
  [disjoint T & W] ->
  ⊨s [pt,st] { P } c { Q ⊗ I_ W } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>P1; apply RS_Er; rewrite set0U. Qed.
Global Arguments RV_Er [pt st W T P Q c].

Lemma RV_TI pt st Wl Wr S T (P : {ket S}) (Q : {ket T}) c :
  [disjoint S & Wl] -> [disjoint T & Wr] ->
  ⊨s [pt,st] { P ⊗ I_ Wl } c { Q ⊗ I_ Wr } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>H1 H2; rewrite RV_Er/= ?RV_El. Qed.
Global Arguments RV_TI [pt st Wl Wr S T P Q c].

Lemma RV_Et pt st W S T (P : {ket S}) (Q : {ket T}) c :
  [disjoint S :|: T & W] ->
  ⊨s [pt,st] { P ⊗ I_ W } c { Q ⊗ I_ W } <-> ⊨s [pt,st] { P } c { Q }.
Proof. rewrite disjointUX=>/andP[P1 P2]; exact: RV_TI. Qed.
Global Arguments RV_Et [pt st W S T P Q c].

Lemma RS_SC pt st (Q P R : 'QE) c1 c2:
  ⊨s [pt,st] { P } c1 { Q } -> ⊨s [pt,st] { Q } c2 { R } -> 
    ⊨s [pt,st] { P } (seqc_ c1 c2) { R }.
Proof. by rewrite !stateE; apply R_SC. Qed.
Global Arguments RS_SC [pt st] Q [P R c1 c2].

Lemma RS_Frame pt st W W' (R : {wf W,W'}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  (pt || no_while c) ->
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { P ⊗ R } c { Q ⊗ R }.
Proof.
rewrite !stateE=>P1 P2 P3 P4.
suff ->: ((P ⊗ R) ∗ (P ⊗ R) `A) = ((P ∗ P`A) ⊗ (R ∗ R`A)).
suff ->: ((Q ⊗ R) ∗ (Q ⊗ R) `A) = ((Q ∗ Q`A) ⊗ (R ∗ R`A)).
apply: R_Frame=>//. 
by rewrite /= wf_linE adjq_lin -comqe_correct linqe_id formV_ge0.
all: by rewrite adjqT tenq_com//; move: P3; rewrite disjointUX=>/andP[P5 P6].
Qed.
Global Arguments RS_Frame [pt st W W' R S S' P T T' Q c].

Lemma RS_Framel pt st W W' (R : {wf W,W'}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  (pt || no_while c) ->
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { R ⊗ P } c { R ⊗ Q }.
Proof. by rewrite ![R ⊗ _]tenqC; apply RS_Frame. Qed.
Global Arguments RS_Framel [pt st W W' R S S' P T T' Q c].

Lemma RS_Frame_T st W W' (R : {wf W,W'}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { P ⊗ R } c { Q ⊗ R }.
Proof. by apply: RS_Frame. Qed.
Global Arguments RS_Frame_T [st W W' R S S' P T T' Q c].

Lemma RS_Framel_T st W W' (R : {wf W,W'}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { R ⊗ P } c { R ⊗ Q }.
Proof. by apply: RS_Framel. Qed.
Global Arguments RS_Framel_T [st W W' R S S' P T T' Q c].

Lemma RS_Frame_P W W' (R : {wf W,W'}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  (R ∗ R`A) W' W' ⊑ \1 -> [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ps { P } c { Q } -> ⊨ps { P ⊗ R } c { Q ⊗ R }.
Proof.
rewrite !stateE=>P1 P2 P3 P4.
suff ->: ((P ⊗ R) ∗ (P ⊗ R) `A) = ((P ∗ P`A) ⊗ (R ∗ R`A)).
suff ->: ((Q ⊗ R) ∗ (Q ⊗ R) `A) = ((Q ∗ Q`A) ⊗ (R ∗ R`A)).
apply: R_Frame_P=>//=; apply/andP; split=>[|//].
by rewrite /= wf_linE adjq_lin -comqe_correct linqe_id formV_ge0.
all: by rewrite adjqT tenq_com//; move: P3; rewrite disjointUX=>/andP[P5 P6].
Qed.
Global Arguments RS_Frame_P [W W' R S S' P T T' Q c].

Lemma RS_Framel_P W W' (R : {wf W,W'}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  (R ∗ R`A) W' W' ⊑ \1 -> [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ps { P } c { Q } -> ⊨ps { R ⊗ P } c { R ⊗ Q }.
Proof. rewrite ![R⊗_]tenqC; exact: RS_Frame_P. Qed.
Global Arguments RS_Framel_P [W W' R S S' P T T' Q c].

Lemma RV_Frame pt st W (R : {ket W}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  (pt || no_while c) ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { P ⊗ R } c { Q ⊗ R }.
Proof. by move=>P1 P2 P3; apply: RS_Frame=>//; rewrite disjointX0. Qed.
Global Arguments RV_Frame [pt st W R S S' P T T' Q c].

Lemma RV_Framel pt st W (R : {ket W}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  (pt || no_while c) ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { R ⊗ P } c { R ⊗ Q }.
Proof. by rewrite ![R ⊗ _]tenqC; apply RV_Frame. Qed.
Global Arguments RV_Framel [pt st W R S S' P T T' Q c].

Lemma RV_Frame_T st W (R : {ket W}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { P ⊗ R } c { Q ⊗ R }.
Proof. by move=>P1 P2 P3; apply: RS_Frame_T=>//; rewrite disjointX0. Qed.
Global Arguments RV_Frame_T [st W R S S' P T T' Q c].

Lemma RV_Framel_T st W (R : {ket W}) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { R ⊗ P } c { R ⊗ Q }.
Proof. by rewrite ![R ⊗ _]tenqC; apply RV_Frame_T. Qed.
Global Arguments RV_Framel_T [st W R S S' P T T' Q c].

Lemma RV_Frame_P W (u : 'H_W) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  `|u| <= 1 ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ps { P } c { Q } -> ⊨ps { P ⊗ ｜u〉 } c { Q ⊗ ｜u〉 }.
Proof.
move=>P1 P2 P3; apply: RS_Frame_P=>//; rewrite ?disjointX0//=.
by rewrite ket_adj outerM linqe_id outp_le1// -hnorm_le1.
Qed.
Global Arguments RV_Frame_P [W u S S' P T T' Q c].

Lemma RV_Framel_P W (u : 'H_W) S S' (P : {wf S,S'}) T T' (Q : {wf T,T'}) c :
  `|u| <= 1 ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ps { P } c { Q } -> ⊨ps { ｜u〉 ⊗ P } c { ｜u〉 ⊗ Q }.
Proof. rewrite ![｜u〉⊗_]tenqC; exact: RV_Frame_P. Qed.
Global Arguments RV_Framel_P [W u S S' P T T' Q c].

Lemma Ax_In pt st S (v : 'NS_S) T (P: {sqr T}) : 
  ⊨ [pt,st] { (qeform (ketqe v) P) } (init_ v) { P }.
Proof.
rewrite -(@R_El _ _ S)/= 1?tenqC; last first.
apply: (R_back _ (Ax_In_onb [QONB of (onb2qe eb_onbasis)] _)).
rewrite -(sumonb_outerM [QONB of (onb2qe eb_onbasis)]) tenq_suml.
apply eq_bigr=>i _; rewrite /= -[in RHS]dotq_com/= -dotq_ten/=; last first.
rewrite -[in RHS]dotqA_cond/=; last first.
rewrite [_`A ∘ _]dotqC/=; last first.
rewrite !qeformE/= adjqM adjqK/= -!dotq_com/= !dotqA_cond//.
all: fsetdec L.
Qed.
Global Arguments Ax_In [pt st S v T].

Lemma AxS_In pt st S (v : 'NS_S) T (P : {sqr T}) : 
  ⊨s [pt,st] { (braqe v) ∘ P } (init_ v) { P }.
Proof.
rewrite stateE; apply: (R_back _ (Ax_In _)).
rewrite qeformE/= adjqG ket_adj bra_adj -!dotq_com/= !dotqA_cond//.
all: fsetdec L.
Qed.
Global Arguments AxS_In [pt st S v T].

Lemma AxV_In pt st S (v : 'NS_S) T (P : {ket T}) : 
  ⊨s [pt,st] { (braqe v) ∘ P } (init_ v) { P }.
Proof.
rewrite stateE; apply: (R_back _ (Ax_In _)).
rewrite qeformE/= adjqG ket_adj bra_adj -!dotq_com/= !dotqA_cond//.
all: fsetdec L.
Qed.
Global Arguments AxV_In [pt st S v T].

Lemma AxS_00_P (c: cmd_) : ⊨ps { 0 } c { 0 }.
Proof. rewrite stateE com0q; exact: Ax_00_P. Qed.

Lemma AxS_00_T st (c: cmd_) : ⊨ts [st] { 0 } c { 0 }.
Proof. rewrite stateE com0q; exact: Ax_00_T. Qed.

Lemma AxV_Inv_P S (u : 'H_S) (c : cmd_) :
  `|u| <= 1 -> [disjoint fvars c & S] ->
    ⊨ps { ｜u〉 } c { ｜u〉 }.
Proof.
move=>P; rewrite stateE ket_adj outerM; apply: Ax_Inv_P.
by rewrite/= linqe_id outp_le1// -hnorm_le1.
Qed.
Global Arguments AxV_Inv_P [S u c].

Lemma RV_Inner S (u v : 'H_S) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫ts { |1 } c { ｜u〉 } ->
  ⊫ts { (`|[< u ; v >]|)%:QE } c { ｜v〉 }.
Proof.
rewrite [X in _ ->X->_]stateE [X in _->_->X]stateE.
rewrite !ket_adj !outerM !(adjq_scale, cplxM).
rewrite conjC1 mulr1 -normCK normr_id; exact: R_Inner.
Qed.

Lemma RS_Scale_T st (P Q : 'QE) (c: cmd_) a :
  ⊨ts [st] { P } c { Q } -> 
    ⊨ts [st] { a *: P } c { a *: Q }.
Proof.
rewrite !stateE !adjqZ !comqZl !comqZr !scalerA; 
by apply/R_Scale_T/mul_conjC_ge0.
Qed.
Global Arguments RS_Scale_T [st P Q c a].

Lemma RS_Scale_P (P Q : 'QE) (c: cmd_) a :
  `|a| <= 1 -> ⊨ps { P } c { Q } -> 
  ⊨ps { a *: P } c { a *: Q }.
Proof.
rewrite !stateE !adjqZ !comqZl !comqZr !scalerA=>P1;
by apply/R_Scale_P; rewrite mul_conjC_ge0 -normCK expr_le1.
Qed.
Global Arguments RS_Scale_P [P Q c].

End StateHoare.

(* with type, and some Parallel rule *)
Section TypedFinQHL.
Implicit Type (T : ihbFinType).
Notation vars T := (@tvars_of L H _ (Phant T)).

(* initialization *)
Lemma tAx_In pt st T (x : vars T) (v : 'NS('Hs T)) (A : 'End[T]) S (P: {sqr S}) : 
  [disjoint lb x & S] ->
  ⊨ [pt, st] { [< v%:V ; A v%:V >] *: (P : 'QE) } (initt_ x v) { ⌈A;x⌉ ⊗ P }.
Proof.
move=>dis; apply: (R_back _ (Ax_In _)).
by rewrite/= qeformE ket_adj tlinT_bral//= dotqTrl//= tinnerG cplxTl adj_dotE.
Qed.
Global Arguments tAx_In [pt st T x v A S P].

Lemma tAx_InF pt st T (x : vars T) (v : 'NS('Hs T)) S (P: {sqr S}) : 
  [disjoint lb x & S] ->
  ⊨ [pt,st] { P } (initt_ x v) { ⌈ [> v ; v <] ; x⌉ ⊗ P }.
Proof.
move=>dis; apply: (R_back _ (tAx_In dis)).
by rewrite outpE !(ns_dot, scale1r).
Qed.
Global Arguments tAx_InF [pt st T x v S P].

(* initialization *)
Lemma tAxV_In pt st T (x : vars T) (v : 'NS('Hs T)) (u : 'Hs T) S (P: {ket S}) : 
  [disjoint lb x & S] ->
  ⊨s [pt,st] { [< v%:V ; u >] *: (P : 'QE) } (initt_ x v) { ｜u;x〉 ⊗ P }.
Proof.
move=>dis. rewrite stateE adjqZ adjqT comqZr comqZl scalerA.
rewrite tenq_com ?disjointX0//= ket_adj touterM. 
apply: (R_back _ (tAx_In dis)).
by rewrite/= outpE dotpZr conj_dotp.
Qed.
Global Arguments tAxV_In [pt st T x v u S P].

Lemma tAxV_InF pt st T (x : vars T) (v : 'NS('Hs T)) S (P: {ket S}) : 
  [disjoint lb x & S] ->
  ⊨s [pt,st] { P } (initt_ x v) { ｜v;x〉 ⊗ P }.
Proof.
by move=>dis; apply: (RS_back _ (tAxV_In dis)); rewrite ns_dot scale1r.
Qed.
Global Arguments tAxV_InF [pt st T x v S P].

(* if *)
Lemma tR_IF pt st (F : finType) T (x : vars T) (M : 'QM(F;'Hs T)) (f : F -> cmd_) S
  (P : F -> {sqr S}) W (Q : {sqr W}) : 
  (forall i, ⊨ [pt,st] { P i } (f i) { Q }) ->
  ⊨ [pt,st] { \sum_i (qeform (⌈ M i ; x ⌉) (P i)) } (condt_ x M f) { Q }.
Proof. by move=>P1; apply: (R_back _ (R_IF P1)); rewrite/tm2m. Qed.
Global Arguments tR_IF [pt st F T x M f S P W Q].

Lemma t2R_IF pt st (F : finType) (T1 T2 : ihbFinType) (x : vars T1) (y : vars T2)  
  (M : 'QM(F;'Hs (T1 * T2))) (f : F -> cmd_) S (P : F -> {sqr S}) W (Q : {sqr W}) :
  [disjoint lb x & lb y] ->
  (forall i, ⊨ [pt,st] { P i } (f i) { Q }) ->
  ⊨ [pt,st] { \sum_i (qeform (⌈ M i ; (x,y) ⌉) (P i)) } (condt2_ x y M f) { Q }.
Proof. 
move=>P1 P2; apply: (R_back _ (R_IF P2)).
by apply eq_bigr=>i _/=; rewrite tm2m2E.
Qed.
Global Arguments t2R_IF [pt st F T1 T2 x y M f S P W Q].

Lemma tR_LP_P S (P Q : {sqr S}) T (x : vars T) (M : 'QM(bool;'Hs T)) b (D: cmd_) :
  let R := qeform (⌈ M (~~b) ; x ⌉) P + qeform (⌈ M b ; x ⌉) Q in 
  P S S ⊑ \1 -> Q S S ⊑ \1 -> ⊨p { Q } D { R } -> ⊨p { R } (whilet_ x M b D) { P }.
Proof.
by move=>R PP PQ; move: (@R_LP_P _ [QM of tm2m x M ] b D _ _ _ PP PQ); rewrite/= !tm2mE.
Qed.
Global Arguments tR_LP_P [S P Q T x M b D].

Lemma t2R_LP_P S (P Q : {sqr S}) T1 T2 (x : vars T1) (y : vars T2) 
  (M : 'QM(bool;'Hs (T1 * T2))) b (D: cmd_) :
  let R := qeform (⌈ M (~~b) ; (x,y) ⌉) P + qeform (⌈ M b ; (x,y) ⌉) Q in 
  [disjoint lb x & lb y] ->
  P S S ⊑ \1 -> Q S S ⊑ \1 -> ⊨p { Q } D { R } -> ⊨p { R } (whilet2_ x y M b D) { P }.
Proof.
move=>R dis PP PQ; move: (@R_LP_P _ [QM of tm2m2 x y M ] b D _ _ _ PP PQ).
rewrite/= !tm2m2E//.
Qed.
Global Arguments t2R_LP_P [S P Q T1 T2 x y M b D].

Lemma tbR_LP_P S (P Q : {sqr S}) (x : vars bool) b (D: cmd_) :
  let R := qeform (⌈ [> ''~~b ; ''~~b <] ; x ⌉) P + qeform (⌈ [> ''b ; ''b <] ; x ⌉) Q in 
  P S S ⊑ \1 -> Q S S ⊑ \1 -> ⊨p { Q } D { R } -> ⊨p { R } 
    [while tmeas[x] = b do D] { P }.
Proof.
move=>/=PP PQ; move: (@tR_LP_P _ _ _ _ x (tmeas_qmType _) b D PP PQ).
by rewrite/= !tmeasE.
Qed.
Global Arguments tbR_LP_P [S P Q x b D].

(* parallel unitary transformation *)
Lemma Ax_UTP_seq pt st (F : eqType) (r : seq F) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {sqr W}) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i <- r | P i) linqe (Uf i) in 
  ⊨ [pt,st] { U`A ∘ Q ∘ U} [for i <- r | P i do unitary_ (Uf i)] { Q }.
Proof.
rewrite/=; elim: r=>[_ _|i r IH +dis].
rewrite !big_nil bigq adjq1 dot1q dotq1; exact: Ax_Sk.
rewrite cons_uniq=>/andP[Pi ur].
rewrite !big_cons; case E: (P i); last by apply: IH.
rewrite bigqE; move: (IH ur dis); apply R_SC.
rewrite -!qeformE; apply: R_UT.
rewrite/= !qeformE adjqT lin_adj [X in _ ∘ X]tenqC -!dotq_ten/= ?dotqA//.
2: rewrite disjoint_sym.
all: apply/bigcup_disjoint_seqP=>j/andP[inj Pj].
all: by apply/dis=>//; move: (notin_in_neq Pi inj).
Qed.
Global Arguments Ax_UTP_seq [pt st F r P fd Uf W Q].

Lemma Ax_UTP pt st (F : finType) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {sqr W}) :
  (forall i j, (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i | P i) linqe (Uf i) in 
  ⊨ [pt,st] { U`A ∘ Q ∘ U} [for i | P i do unitary_ (Uf i)] { Q }.
Proof. move=>IH; apply: Ax_UTP_seq=>[//|i j _ _]; exact: IH. Qed.
Global Arguments Ax_UTP [pt st F P fd Uf W Q].

Lemma no_while_for F (r : seq F) (P : pred F) (c : F -> cmd_) :
  (forall i, P i -> no_while (c i)) ->
    no_while [for i <- r | P i do c i].
Proof. by move=>Pi; elim/big_rec: _=>[//|i x IH]; rewrite /= Pi. Qed.

Lemma Ax_UTFP_seq pt st (F : eqType) (r : seq F) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {sqr W}) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i <- r | P i) linqe (Uf i) in 
  ⊨ [pt,st] { Q } [for i <- r | P i do unitary_ (Uf i)] { U ∘ Q ∘ U`A }.
Proof.
move=>ur dis U; rewrite -qeformEV.
move: (@Ax_UTP_seq pt st _ _ _ _ Uf _ [sqr of qeform U`A Q] ur dis).
rewrite/= -/U -qeformE qeform_comp/= tens_adj dotq_com/= tensM/==>[//|//|].
under eq_bigr do rewrite lin_adj -comqe_correct unitaryf_form.
rewrite tensI {1}qeformE adjqI dotIqT/= dotqIT/= tenqA tenqII tenqC.
by rewrite R_El// disjointXU -setDDl !disjointXD/=.
Qed.
Global Arguments Ax_UTFP_seq [pt st F r P fd Uf W Q].

Lemma Ax_UTFP pt st (F : finType) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {sqr W}) :
  (forall i j, (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i | P i) linqe (Uf i) in 
  ⊨ [pt,st] { Q } [for i | P i do unitary_ (Uf i)] { U ∘ Q ∘ U`A }.
Proof. move=>IH; apply: Ax_UTFP_seq=>[//|i j _ _]; exact: IH. Qed.
Global Arguments Ax_UTFP [pt st F P fd Uf W Q].

Lemma AxV_UTP_seq pt st (F : eqType) (r : seq F) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {ket W}) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i <- r | P i) linqe (Uf i) in 
  ⊨s [pt,st] { U`A ∘ Q } [for i <- r | P i do unitary_ (Uf i)] { Q }.
Proof.
move=>ur dis U; rewrite stateE; apply: (R_back _ (Ax_UTP_seq ur dis)).
by rewrite -/U/= adjqG adjqK -!dotq_com/= -/U !dotqA_cond// ?disjoint0X// setD0
  ?disjointX0// set0U disjointXD.
Qed.
Global Arguments AxV_UTP_seq [pt st F r P fd Uf W Q].

Lemma AxV_UTP pt st (F : finType) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {ket W}) :
  (forall i j, (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i | P i) linqe (Uf i) in 
  ⊨s [pt,st] { U`A ∘ Q } [for i | P i do unitary_ (Uf i)] { Q }.
Proof. move=>IH; apply: AxV_UTP_seq=>[//|i j _ _]; exact: IH. Qed.
Global Arguments AxV_UTP [pt st F P fd Uf W Q].

Lemma AxV_UTFP_seq pt st (F : eqType) (r : seq F) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {ket W}) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i <- r | P i) linqe (Uf i) in 
  ⊨s [pt,st] { Q } [for i <- r | P i do unitary_ (Uf i)] { U ∘ Q }.
Proof.
move=>ur dis U; rewrite stateE; apply: (R_forward _ (Ax_UTFP_seq ur dis)).
by rewrite -/U/= adjqG -!dotq_com/= -/U !dotqA_cond// ?disjoint0X// setD0
  ?disjointX0// set0U disjointXD.
Qed.
Global Arguments AxV_UTFP_seq [pt st F r P fd Uf W Q].

Lemma AxV_UTFP pt st (F : finType) (P : pred F) (fd : F -> {set _}) 
  (Uf : forall i : F, 'FU[H]_(fd i)) W (Q : {ket W}) :
  (forall i j, (i != j) -> [disjoint fd i & fd j]) ->
  let U := \tens_(i | P i) linqe (Uf i) in 
  ⊨s [pt,st] { Q } [for i | P i do unitary_ (Uf i)] { U ∘ Q }.
Proof. move=>IH; apply: AxV_UTFP_seq=>[//|i j _ _]; exact: IH. Qed.
Global Arguments AxV_UTFP [pt st F P fd Uf W Q].

Lemma tAx_InP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) (A : forall i : F, 'End[T i]) W (Q : {sqr W}):
  (forall i j, P i -> P j -> (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  uniq r ->
  [disjoint W & \bigcup_(i <- r | P i) lb (fx i)] ->
  ⊨ [pt,st] { (\prod_(i <- r | P i) [< (v i)%:V ; A i (v i)%:V >]) *: (Q : 'QE) } 
    [for i <- r | P i do initt_ (fx i) (v i)]
    { (\tens_(i <- r | P i) ⌈A i;fx i⌉) ⊗ Q }.
Proof.
move=>disx; elim: r W Q=>[W Q _ _ |i r IH W Q].
rewrite !big_nil bigq scale1r ten1q; exact: Ax_Sk.
rewrite !big_cons cons_uniq=>/andP[pi ur]; case E: (P i); last by apply: IH.
rewrite disjointXU=>/andP[disi disw].
move: {+}E. rewrite [CMD]fsem_seqC; last first.
rewrite bigqE=>_; rewrite -tenqA mulrC -scalerA.
apply: (R_SC _ _ (tAx_In _ )).
rewrite/= -tenqZr; apply: IH=>//.
rewrite disjointXU [X in _ && X]disjoint_sym disi andbT.
2: rewrite /=fvars_for/=.
all: apply/bigcup_disjoint_seqP=>j/andP[inj Pj]; rewrite/= disx//.
all: by move: (notin_in_neq pi inj).
Qed.
Global Arguments tAx_InP_seq [pt st F r P T fx v A W Q].

Lemma tAx_InP pt st (F : finType) (P : pred F) 
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) (A : forall i : F, 'End[T i]) W (Q : {sqr W}):
  (forall i j, (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  [disjoint W & \bigcup_(i | P i) lb (fx i)] ->
  ⊨ [pt,st] { (\prod_(i | P i) [< (v i)%:V ; A i (v i)%:V >]) *: (Q : 'QE) } 
    [for i | P i do initt_ (fx i) (v i)]
    { (\tens_(i | P i) ⌈A i;fx i⌉) ⊗ Q }.
Proof. move=>IH; apply: tAx_InP_seq=>[i j _ _|//]; exact: IH. Qed.
Global Arguments tAx_InP [pt st F P T fx v A W Q].

Lemma tAx_InFP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) W (Q : {sqr W}):
  (forall i j, P i -> P j -> (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  uniq r ->
  [disjoint W & \bigcup_(i <- r | P i) lb (fx i)] ->
  ⊨ [pt,st] { Q } [for i <- r | P i do initt_ (fx i) (v i)]
    { (\tens_(i <- r | P i) ⌈[> v i ; v i <];fx i⌉) ⊗ Q }.
Proof.
move=>disx ur dis; apply: (R_back _ (tAx_InP_seq disx ur dis)).
rewrite big1 ?scale1r// =>i _; by rewrite outpE !(ns_dot, scale1r).
Qed.
Global Arguments tAx_InFP_seq [pt st F r P T fx v W Q].

Lemma tAx_InFP pt st (F : finType) (P : pred F) 
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) W (Q : {sqr W}):
  (forall i j, (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  [disjoint W & \bigcup_(i | P i) lb (fx i)] ->
  ⊨ [pt,st] { Q } [for i | P i do initt_ (fx i) (v i)]
    { (\tens_(i | P i) ⌈[> v i ; v i <];fx i⌉) ⊗ Q }.
Proof. move=>IH; apply: tAx_InFP_seq=>[i j _ _|//]; exact: IH. Qed.
Global Arguments tAx_InFP [pt st F P T fx v W Q].

Lemma tAxV_InP_seq pt st (F : eqType) (r : seq F) (P : pred F)
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) (u : forall i : F, 'Hs (T i)) W (Q : {ket W}):
  (forall i j, P i -> P j -> (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  uniq r ->
  [disjoint W & \bigcup_(i <- r | P i) lb (fx i)] ->
  ⊨s [pt,st] { (\prod_(i <- r | P i) [< (v i)%:V ; (u i) >]) *: (Q : 'QE) } 
    [for i <- r | P i do initt_ (fx i) (v i)]
    { (\tens_(i <- r | P i) ｜u i; fx i〉) ⊗ Q }.
Proof.
move=>disx ur disw; rewrite stateE adjqT tenq_com/= ?disjointX0//.
rewrite tens_adj tensM//==>[i j _ _ _|]; rewrite ?disjointX0//.
under [in POST]eq_bigr do rewrite ket_adj touterM.
apply: (R_back _ (tAx_InP_seq _ _ _))=>//=.
rewrite adjqZ comqZr comqZl scalerA; f_equal.
rewrite rmorph_prod -big_split/=; apply eq_bigr=>i _.
by rewrite outpE dotpZr conj_dotp.
Qed.
Global Arguments tAxV_InP_seq [pt st F r P T fx v u W Q].

Lemma tAxV_InP pt st (F : finType) (P : pred F)
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) (u : forall i : F, 'Hs (T i)) W (Q : {ket W}):
  (forall i j, (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  [disjoint W & \bigcup_(i | P i) lb (fx i)] ->
  ⊨s [pt,st] { (\prod_(i | P i) [< (v i)%:V ; (u i) >]) *: (Q : 'QE) } 
    [for i | P i do initt_ (fx i) (v i)]
    { (\tens_(i | P i) ｜u i; fx i〉) ⊗ Q }.
Proof. move=>IH; apply: tAxV_InP_seq=>[i j _ _|//]; exact: IH. Qed.
Global Arguments tAxV_InP [pt st F P T fx v u W Q].

Lemma tAxV_InFP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) W (Q : {ket W}):
  (forall i j, P i -> P j -> (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  uniq r ->
  [disjoint W & \bigcup_(i <- r | P i) lb (fx i)] ->
  ⊨s [pt,st] { Q } [for i <- r | P i do initt_ (fx i) (v i)]
    { (\tens_(i <- r | P i) ｜v i; fx i〉) ⊗ Q }.
Proof.
move=>disx ur dis; apply: (RS_back _ (tAxV_InP_seq disx ur dis)).
by rewrite big1 ?scale1r// =>i _; rewrite ns_dot.
Qed.
Global Arguments tAxV_InFP_seq [pt st F r P T fx v W Q].

Lemma tAxV_InFP pt st (F : finType) (P : pred F) 
  (T : F -> ihbFinType) (fx : forall i : F, vars (T i)) 
  (v : forall i : F, 'NS('Hs (T i))) W (Q : {ket W}):
  (forall i j, (i != j) -> [disjoint lb (fx i) & lb (fx j)]) ->
  [disjoint W & \bigcup_(i | P i) lb (fx i)] ->
  ⊨s [pt,st] { Q } [for i | P i do initt_ (fx i) (v i)]
    { (\tens_(i | P i) ｜v i; fx i〉) ⊗ Q }.
Proof. move=>IH; apply: tAxV_InFP_seq=>[i j _ _|//]; exact: IH. Qed.
Global Arguments tAxV_InFP [pt st F P T fx v W Q].

Lemma tR_Inner T (x : vars T) (u v : 'Hs T) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫t { |1 } c { ⌈ [> u ; u <] ; x⌉ } ->
  ⊫t { (`|[< u ; v >]| ^+2)%:QE } c { ⌈ [> v ; v <] ; x⌉ }.
Proof. by rewrite -!tv2v_out -(tv2v_dot x) -(tv2v_norm x); exact: R_Inner. Qed.

Lemma t2R_Inner T1 T2 (x : vars T1) (y : vars T2) (dis: [disjoint lb x & lb y])
  (u v : 'Hs (T1 * T2)) (c : cmd_) : 
  `|u| <= 1 -> 
  ⊫t { |1 } c { ⌈ [> u ; u <] ; (x,y)⌉ } ->
  ⊫t { (`|[< u ; v >]| ^+2)%:QE } c { ⌈ [> v ; v <] ; (x,y)⌉ }.
Proof. rewrite -!tv2v2_out -(tv2v2_dot dis) -(tv2v2_norm dis); exact: R_Inner. Qed.

Lemma tR_PInnerl T1 T2 (x : vars T1) (y : vars T2) (dis: [disjoint lb x & lb y])
  (u : 'Hs (T1 * T2)) (v : 'Hs T1) (c : cmd_) : 
  `|u| <= 1 ->
  ⊫t { |1 } c { ⌈ [> u ; u <] ; (x,y) ⌉ } ->
  ⊫t { (\sum_i (`|[< v ⊗t ''i ; u >]| ^+2))%:QE } c { ⌈ [> v ; v <] ; x ⌉ }.
Proof.
rewrite -tv2v2_out -tv2v_out -(tv2v2_norm dis)=>u1.
under eq_bigr do rewrite -(tv2v2_dot dis) tv2v2_ten .
by move=>/(R_PInner (tv2v x v) (tv2v_onbasis y t2tv_onbasis) u1 dis).
Qed.

Lemma tR_PInnerr T1 T2 (x : vars T1) (y : vars T2) (dis: [disjoint lb x & lb y])
  (u : 'Hs (T1 * T2)) (v : 'Hs T2) (c : cmd_) : 
  `|u| <= 1 ->
  ⊫t { |1 } c { ⌈ [> u ; u <] ; (x,y) ⌉ } ->
  ⊫t { (\sum_i (`|[< ''i ⊗t v ; u >]| ^+2))%:QE } c { ⌈ [> v ; v <] ; y ⌉ }.
Proof.
move: dis; rewrite -swaptf_norm disjoint_sym=>dis u1.
rewrite -touterT_swap =>/(tR_PInnerl dis v u1).
by apply: R_back; f_equal; apply eq_bigr=>i _; rewrite -swaptf_dot swaptfK swaptfEtv.
Qed.

Lemma tRV_Inner T (x : vars T) (u v : 'Hs T) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫ts { |1 } c { ｜u;x〉 } ->
  ⊫ts { (`|[< u ; v >]|)%:QE } c { ｜v;x〉 }.
Proof. by rewrite -(tv2v_dot x) -(tv2v_norm x); exact: RV_Inner. Qed.

Lemma t2RV_Inner T1 T2 (x : vars T1) (y : vars T2) (dis: [disjoint lb x & lb y])
  (u v : 'Hs (T1 * T2)) (c : cmd_) : 
  `|u| <= 1 -> 
  ⊫ts { |1 } c { ｜u;(x,y)〉 } ->
  ⊫ts { (`|[< u ; v >]|)%:QE } c { ｜v;(x,y)〉 }.
Proof. by rewrite -(tv2v2_dot dis) -(tv2v2_norm dis); exact: RV_Inner. Qed.

End TypedFinQHL.

End FinQHL.
