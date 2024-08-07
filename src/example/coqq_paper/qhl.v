From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals topology normedtype sequences.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
From mathcomp Require Import finset.

Require Import mcextra mcaextra autonat notation mxpred extnum ctopology.
Require Import hermitian quantum hspace inhabited prodvect tensor qreg qmem.
From quantum.dirac Require Import setdec hstensor dirac.
From quantum.example.coqq_paper Require Import qwhile.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import HermitianTopology DefaultQMem.Exports.

Local Notation C := hermitian.C.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.

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
(*          ⊨g [ pt , st ] { P } c { Q }                                      *)
(* local  : (lfun, predicate are linear function 'F[H]_S for all S : {set L}) *)
(*          rules inspired by [1,4]                                           *)
(*          New rule R_Inner (and its variant)                                *)
(*          ⊨l [ pt , st ] { P } c { Q }                                      *)
(* dirac  : (dirac, predicate are 'D )                                        *)
(*          rules inspired by [1,2,3,4]                                       *)
(*          ⊨ [ pt , st ] { P } c { Q }                                       *)
(* state  : (dirac, predicate are 'D )                                        *)
(*          rules inspired by [1,2,3,4]                                       *)
(*          ⊨s [ pt , st ] { P } c { Q }                                      *)
(* Naming rule :  G : global, L : local, S : state                            *)
(*                V : vector, P : partial, T : total                          *)
(*                (S : with 'D of 'D_(_,_)) (V : with 'D of 'Ket__)           *)
(* for example, R_XX :                                                        *)
(*    R_XX_L : R_XX for local                                                 *)
(*    R_XX_GP : R_XX for global and for partial                               *)
(*    R_XX : for dirac                                                        *)
(*    RS_XX_T : for state and for total (predicate are 'D_(_,_))              *)
(*    RV_XX_P : for state and for partial (predicate are 'Ket__)              *)
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
Notation PRE  := (X in (⊨ [ _ , _ ] { X } _ { _ })%D )%pattern.
Notation POST := (X in (⊨ [ _ , _ ] { _ } _ { X })%D )%pattern.
Notation CMD  := (X in (⊨ [ _ , _ ] { _ } X { _ })%D )%pattern.
Notation SPRE  := (X in (⊨s [ _ , _ ] { X } _ { _ })%D )%pattern.
Notation SPOST := (X in (⊨s [ _ , _ ] { _ } _ { X })%D )%pattern.
Notation SCMD  := (X in (⊨s [ _ , _ ] { _ } X { _ })%D )%pattern.

(* TODO : merge to mcextra, also in qlaws/basic_def.v *)
Lemma big_boolb (R : Type) (idx : R) (op : Monoid.com_law idx) b (F : bool -> R):
    \big[op/idx]_i F i = op (F b) (F (~~b)).
Proof. by rewrite big_bool; case: b=>/=; rewrite Monoid.mulmC. Qed.
Global Arguments big_boolb [R idx op].

Lemma not_eqb (b1 b2 : bool) : b1 <> b2 <-> b1 = ~~b2.
Proof. by case: b1; case: b2. Qed.

Section FinQHL.
Implicit Type (pt st : bool) (c : cmd_).

(* for backward reasoning, we set all arguments implicit *)
(****************************************************************************)
Section GlobalHoare.
Implicit Type (P Q R : 'FO[msys]_setT).

Lemma no_while_enoughg st pt (c : Cmd_) P Q : no_while c ->
  ⊫tg { P } c { Q } -> ⊨g [pt,st] { P } c { Q }.
Proof.
move=>P1; case: pt=>//; rewrite ?no_while_GPT// ?cmd_is_valid//;
apply/saturated_strong_G.
Qed.
Global Arguments no_while_enoughg [st pt c P Q].

Lemma Ax_Ab_GT st P : ⊨tg [st] { 0%:VF } abort_ { P }.
Proof.
by rewrite global_hoare.unlock; case: st=>x; 
rewrite fsemE soE comp_lfun0r comp_lfun0l linear0.
Qed.
Global Arguments Ax_Ab_GT {st P}.

Lemma Ax_Ab_GP st P : ⊨pg [st] { \1 } abort_ { P }.
Proof.
by rewrite global_hoare.unlock; case: st=>x; 
rewrite fsemE/= soE cplmt1 comp_lfun0r comp_lfun0l linear0.
Qed.
Global Arguments Ax_Ab_GP {st P}.

Lemma Ax_Sk_G pt st P : ⊨g [pt,st] { P } skip_ { P }.
Proof. by rewrite global_hoare.unlock; case: pt; case: st=>x; rewrite fsemE soE. Qed.
Global Arguments Ax_Sk_G {pt st P}.

Lemma Ax_In_G pt st T (x : 'QReg[T]) (v : 'NS('Ht T)) P : 
  ⊨g [pt,st] { (liftfso (initialso (tv2v x v)))^*o P } (init_ x v) { P }.
Proof.
case: st; apply/no_while_enoughg=>//; 
by rewrite global_hoare.unlock=>y; rewrite fsemE dualso_trlfEV.
Qed.
Global Arguments Ax_In_G {pt st T x v P}.

Lemma Ax_UT_G pt st T (x : 'QReg[T]) (U : 'FU) P :
  ⊨g [pt,st] { (liftfso (unitaryso (tf2f x x U)))^*o P } (unitary_ x U) { P }.
Proof.
by case: st; apply/no_while_enoughg=>//;
rewrite global_hoare.unlock=>y; rewrite fsemE dualso_trlfEV.
Qed.
Global Arguments Ax_UT_G {pt st T x U P}.

Lemma R_IF_G pt st T (F: finType) (x : 'QReg[T]) (M : 'QM) (f : F -> cmd_)
  (P : F -> 'FO_setT) Q :
  (forall i, ⊨g [pt , st] { P i } (f i) { Q }) ->
  ⊨g [pt , st] { dualqm (liftf_fun (tm2m x x M)) P } (cond_ x M f) { Q }.
Proof.
case: pt.
  rewrite global_hoare.unlock; case: st=>P1 y/=; 
  rewrite fsemE -dualqm_trlfEV ifso_elemE linear_sumr/= linear_sum/= ?ler_sum//; 
  first apply eq_bigr; move=>i _; rewrite comp_soE; apply P1.
move=>P1; rewrite partial_alter_G fsemE; case: st P1=>P1 y;
rewrite -dualqm_trlfEV ifso_elemE -(elemso_trlf (liftf_fun (tm2m x x M)) y) 
  ?lerBrDl linear_sumr/= -?linearN/= !linear_sum/= -!big_split/= ?ler_sum//;
  first apply eq_bigr; move=>i _; rewrite ?linearN/= -?lerBrDl comp_soE;
  by move: (P1 i); rewrite partial_alter_G=>/(_ (elemso (liftf_fun (tm2m x x M)) i y)).
Qed.
Global Arguments R_IF_G [pt st T F x M f P Q].

Lemma R_SC_G pt st Q P R c1 c2 :
  ⊨g [pt,st] { P } c1 { Q } -> ⊨g [pt,st] { Q } c2 { R } -> 
    ⊨g [pt,st] { P } (seqc_ c1 c2) { R }.
Proof.
rewrite global_hoare.unlock; case: st; case: pt=>P1 P2 x; 
rewrite fsemE comp_soE; [rewrite P1 | rewrite -P1 
| apply: (le_trans (P1 x)) | apply: (le_trans _ (P1 x))]; apply P2.
Qed.
Global Arguments R_SC_G [pt st] Q [P R c1 c2].

Lemma R_Or_G pt P Q P' Q' c :
  (P' ⊑ P) -> (Q ⊑ Q') -> ⊨g[pt] { P } c { Q } -> ⊨g[pt] { P' } c { Q' }.
Proof.
rewrite global_hoare.unlock; case: pt; 
  first by move=>/lef_trden P1 /lef_trden P2 IH x;
  apply/(le_trans (P1 x))/(le_trans (IH x)); apply: P2. 
rewrite !leEsub/= cplmt_lef=>/lef_trden P1.
rewrite cplmt_lef=>/lef_trden P2 IH x; 
apply/(le_trans _ (P1 x))/(le_trans _ (IH x)).
by move: (P2 (fsem c x)).
Qed.
Global Arguments R_Or_G [pt] P Q [P' Q' c].

Lemma R_LP_GP T (x : 'QReg[T]) (M : 'QM) b (D: cmd_)
(P : bool -> 'FO_setT) :
  ⊨pg { P b } D { dualqm (liftf_fun (tm2m x x M)) P } ->
    ⊨pg { dualqm (liftf_fun (tm2m x x M)) P } (while_ x M b D) { P (~~b) }.
Proof.
set R := dualqm (liftf_fun (tm2m x x M)) P.
rewrite global_hoare.unlock=>P1 y; rewrite [in X in _ <= X]/= fsemE.
set f := (lftrace (H:=Hs msys setT) \o comp_lfun (cplmt (P (~~b))))%FUN.
have sf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
suff: forall i, f (whileso_iter (liftf_fun (tm2m x x M)) b (fsem D) i y) <= \Tr (cplmt R \o y).
  by move=>/(while_sf_le_cst sf)/=.
move=>n. suff : ⊨pg { R } (while_iter_ x M b D n) { P (~~b) }.
  by rewrite global_hoare.unlock=>/(_ y); rewrite fsem_while_iter_.
elim: n=>[|n IH/=].
  by rewrite global_hoare.unlock=>z; 
  rewrite fsemE soE comp_lfun0r -(comp_lfun0l _ z); apply/lef_trden/obsf_ge0.
by apply/R_IF_G=>b'; case: eqP=>[->|/not_eqb->];
  [apply/(R_SC_G _ _ IH) | apply/Ax_Sk_G]; rewrite global_hoare.unlock.
Qed.
Global Arguments R_LP_GP [T x M b D P].

Local Open Scope classical_set_scope.

(* introduce ranking function ?? do it in lfrepresent.v? *)
Lemma R_LP_GT T (x : 'QReg[T]) (M : 'QM) b (D: cmd_)
  (P : bool -> 'FO_setT) :
(exists t, ranking_function (liftf_fun (tm2m x x M)) b (fsem D)
  ((elemso (liftf_fun (tm2m x x M)) b)^*o (P b)) t) ->
  ⊨tg { P b } D { dualqm (liftf_fun (tm2m x x M)) P } ->
    ⊨tg { dualqm (liftf_fun (tm2m x x M)) P } (while_ x M b D) { P (~~b) }.
Proof.
set R := (dualqm (liftf_fun (tm2m x x M)) P).
rewrite global_hoare.unlock=>+P2 y; move=>/rankingP /(_ y)/=.
set cf := (fun n => \Tr ((elemso (liftf_fun (tm2m x x M)) b) ^*o (P b) \o 
  whileso_incr (liftf_fun (tm2m x x M)) b (fsem D) n y)).
move=>cvgcf.
set f := (lftrace (H:=Hs msys setT) \o comp_lfun ((P (~~b))))%FUN.
have sf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
set cg := (fun n=>\Tr (R \o y) - cf n).
set cg1 := [sequence if (n <= 0)%N then (fun i:nat=>0) n else [sequence cg (k - 1)%N]_k n]_n.
have: cg1 @ \oo --> \Tr (R \o y).
  rewrite cvg_restrict cvg_centern -[X in _ --> X]subr0.
  apply ccvgnB; [apply: cvg_cst | by []].
rewrite ccvgn_limnE=>[[P1 P3]].
have scf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
suff: forall i, cg1 i <= f (whileso_iter (liftf_fun (tm2m x x M)) b (fsem D) i y).
  by move=>/(while_sf_ge scf P3); rewrite fsemE P1 /f/=.
case; first by rewrite /cg1/f/= soE comp_lfun0r linear0.
elim=>[|i].
  by rewrite /cg1/cg/cf/f/R/= dualqmE lerBlDl soE (ifso_bool b)
    (big_boolb b)/= eqxx neqb !comp_so0l comp_so1l 
    add0r linearDl/= linearD/= dualso_trlfEV.
have P5: forall n, cg1 n.+1 = cg n by move=>n; rewrite /cg1/= -addn1 addnK.
rewrite !P5 /cg !lerBlDl=>P6. apply (le_trans P6).
rewrite [in X in _ <= X]whileso_iterE.
set t:= (whileso_iter (liftf_fun (tm2m x x M)) b (fsem D) i.+1 y).
rewrite /cf soE soE.
set s:= (whileso_incr (liftf_fun (tm2m x x M)) b (fsem D) i y).
have ->: whileso_incr (liftf_fun (tm2m x x M)) b (fsem D) i.+1 y 
  = ((fsem D) :o (elemso (liftf_fun (tm2m x x M)) b)) s.
by rewrite whileso_incrE !comp_soE.
rewrite /f/= comp_lfunDr linearD/= [X in _<=_+X]addrC addrA lerD2r.
rewrite /= -!dualso_trlfEV.
move: (P2 ((elemso (liftf_fun (tm2m x x M)) b) s))=>/=.
by rewrite /R dualqmE (big_boolb b)/= linearDl/= linearD/= -!dualso_trlfEV !comp_soE.
Qed.
Global Arguments R_LP_GT [T x M b D P].

End GlobalHoare.

Section PDsystemComplete.

(* definition of wlpqo *)
Definition wlpso (E: 'SO[msys]_setT) P := ((E^*o (P^⟂))^⟂).

Lemma wlpso_trE P E x :
  \Tr ((wlpso E P)^⟂ \o x) = \Tr (P^⟂ \o E x).
Proof. by rewrite /wlpso cplmtK -dualso_trlfEV. Qed.

Lemma wlpso_least (E: 'SO) P Q :
  (forall (x : 'FD), \Tr (P^⟂ \o E x) <= 
  \Tr (Q^⟂ \o x)) -> Q ⊑ (wlpso E P).
Proof. 
move=>H1. rewrite cplmt_lef. apply/lef_trden=>x.
apply: (le_trans _ (H1 x)). by rewrite wlpso_trE.
Qed.

Lemma wlpso_saturated (E: 'SO) P Q :
  (forall (x : 'FD_setT), \Tr (P^⟂ \o E x) = 
  \Tr (Q^⟂ \o x)) -> Q = (wlpso E P).
Proof.
move=>H1; apply/le_anti/andP; split; rewrite cplmt_lef; apply/lef_trden=>x.
by rewrite -[X in _ <= X]H1 wlpso_trE. by rewrite -[X in X <= _]H1 wlpso_trE.
Qed.

Lemma wlpso_preserve_order (E: 'CP) P Q :
  P ⊑ Q -> wlpso E P ⊑ wlpso E Q.
Proof. by rewrite /wlpso -cplmt_lef cplmt_lef; apply/cp_preserve_order. Qed.

Definition wlp (c: cmd_) (P : 'FO) := wlpso (fsem c) P.
Lemma wlpE (c: cmd_) (P : 'FO) : wlpso (fsem c) P = wlp c P. by []. Qed.
Lemma wlp_valid (c: cmd_) (P : 'FO) : ⊨pg { wlp c P } c { P }.
Proof. by rewrite global_hoare.unlock /wlp=>x; rewrite /wlp -wlpso_trE. Qed.
Lemma wlp_least (c: cmd_) P Q : ⊨pg { Q } c { P } -> Q ⊑ (wlp c P).
Proof. by rewrite global_hoare.unlock=>P1; apply/wlpso_least/P1. Qed.
Lemma wlp_preserve_order (c: cmd_) (P Q: 'FO) :
  P ⊑ Q -> wlp c P ⊑ wlp c Q.
Proof. rewrite /wlp; apply/wlpso_preserve_order. Qed. 

(* structure property of wlp *)

Lemma wlp_Ab P : wlp abort_ P = \1.
Proof. by rewrite /wlp /wlpso fsemE dualso0 soE cplmt0. Qed.

Lemma wlp_Sk P : wlp skip_ P = P.
Proof. by rewrite /wlp /wlpso fsemE dualso1 soE cplmtK. Qed.

Lemma wlp_In T (x : 'QReg[T]) (v : 'NS) P : 
  wlp (init_ x v) P = (liftfso (initialso (tv2v x v)))^*o P.
Proof. by rewrite /wlp /wlpso fsemE cplmt_dualC/= cplmtK. Qed.

Lemma wlp_UT T (x : 'QReg[T]) (U : 'FU) P : 
  wlp (unitary_ x U) P = (liftfso (unitaryso (tf2f x x U)))^*o P.
Proof. by rewrite /wlp /wlpso fsemE cplmt_dualC/= cplmtK. Qed.

Lemma wlp_SC c1 c2 P : 
  wlp (seqc_ c1 c2) P = wlp c1 (wlp c2 P).
Proof. by rewrite /wlp /wlpso/= fsemE cplmtK dualso_comp comp_soE. Qed.

Lemma elemso_dual_sum (U V : chsType) (F : finType) (f : F -> 'Hom(U,V)) :
  \sum_i (elemso f i)^*o = (krausso f)^*o.
Proof. by apply/superopP=>x; rewrite dualsoE soE; under eq_bigr do rewrite dualsoE. Qed.

Lemma wlp_If T (F: finType) (x : 'QReg[T]) (M : 'QM(F; 'Ht T)) (f : F -> cmd_)
  P : wlp (cond_ x M f) P = dualqm (liftf_fun (tm2m x x M)) (fun i=>wlp (f i) P).
Proof.
rewrite /wlp /wlpso fsemE dualso_if dualqmE soE /cplmt linear_sum/=.
under eq_bigr do rewrite dualso_comp soE.
under [RHS]eq_bigr do rewrite linearB/=.
by rewrite [RHS]big_split/= -sum_soE elemso_dual_sum [X in _ = X + _]qu1_eq1.
Qed.

(* what we need is the fixpoint equation of while *)
(* we don't need to give the explicit form of wlp while, though we can... *)
Lemma while_fsem_fp T (x : 'QReg[T]) (M : 'QM) b (c: cmd_) :
  fsem (while_ x M b c) = fsem (cond_ x M 
    (fun b'=> if b' == b then seqc_ c (while_ x M b c)
    else skip_)).
Proof.
rewrite !fsemE/= whileso_fixpoint. f_equal.
by apply/funext=>b'; case: eqP=>_; rewrite !fsemE.
Qed.

Lemma wlp_eqfsem (c1 c2 : cmd_) (P : 'FO) : 
  fsem c1 = fsem c2 -> wlp c1 P = wlp c2 P.
Proof. by move=>ef; rewrite /wlp /= ef. Qed.

Lemma wlp_LP T (x : 'QReg[T]) (M : 'QM) b (c: cmd_) P : 
  wlp (while_ x M b c) P = dualqm (liftf_fun (tm2m x x M)) 
    (fun b'=> if b'==b then (wlp c (wlp (while_ x M b c) P)) else P).
Proof.
rewrite {1}(wlp_eqfsem _ (while_fsem_fp x M b c)) wlp_If.
f_equal; apply/funext=>b'; case: eqP=>_.
by rewrite -wlp_SC. by rewrite -[in RHS](wlp_Sk P).
Qed.

(* Completeness: wlp can be derived by PDsystem *)
(* this part is trivial by above lemmas *)

End PDsystemComplete.

Section TDsystemComplete.

(* definition of wpso *)
Definition wpso (E: 'SO[msys]_setT) P := (E^*o P).

Lemma wpso_trE P E x :
  \Tr ((wpso E P) \o x) = \Tr (P \o E x).
Proof. by rewrite /wpso dualso_trlfEV. Qed.

Lemma wpso_least (E: 'SO) P Q :
  (forall (x : 'FD_setT), \Tr (Q \o x) <= 
  \Tr (P \o E x)) -> Q ⊑ (wpso E P).
Proof. by move=>H1; apply/lef_trden=>x; rewrite /wpso -dualso_trlfEV H1. Qed.

Lemma wpso_saturated (E: 'SO) P Q :
  (forall (x : 'FD_setT), \Tr (Q \o x) = 
  \Tr (P \o E x)) -> Q = (wpso E P).
Proof.
by move=>H1; apply/le_anti/andP; split; 
  apply/lef_trden=>x; rewrite /wpso -dualso_trlfEV H1.
Qed.

Lemma wpso_preserve_order (E: 'CP) P Q :
  P ⊑ Q -> wpso E P ⊑ wpso E Q.
Proof. by rewrite /wpso; apply/cp_preserve_order. Qed.

Definition wp (c: cmd_) (P : 'FO) := wpso (fsem c) P.
Lemma wpE (c: cmd_) (P : 'FO) : wpso (fsem c) P = wp c P. by []. Qed.
Lemma wp_valid (c: cmd_) P : ⊨tg { wp c P } c { P }.
Proof. by rewrite global_hoare.unlock=>x; rewrite /wp -wpso_trE. Qed.
Lemma wp_least (c: cmd_) P Q : ⊨tg { Q } c { P } -> Q ⊑ (wp c P).
Proof. by rewrite global_hoare.unlock=>P1; apply/wpso_least/P1. Qed.
Lemma wp_preserve_order (c: cmd_) (P Q: 'FO) :
  P ⊑ Q -> wp c P ⊑ wp c Q.
Proof. rewrite /wp. apply/wpso_preserve_order. Qed. 

(* structure property of wp *)

Lemma wp_Ab P : wp abort_ P = 0.
Proof. by rewrite /wp /wpso fsemE dualso0 soE. Qed.

Lemma wp_Sk P : wp skip_ P = P.
Proof. by rewrite /wp /wpso fsemE dualso1 soE. Qed.

Lemma wp_In T (x : 'QReg[T]) (v : 'NS) P : 
  wp (init_ x v) P = (liftfso (initialso (tv2v x v)))^*o P.
Proof. by rewrite /wp fsemE. Qed.

Lemma wp_UT T (x : 'QReg[T]) (U : 'FU) P : 
  wp (unitary_ x U) P = (liftfso (unitaryso (tf2f x x U)))^*o P.
Proof. by rewrite /wp fsemE. Qed.

Lemma wp_SC c1 c2 P : 
  wp (seqc_ c1 c2) P = wp c1 (wp c2 P).
Proof. by rewrite /wp fsemE /wpso dualso_comp soE. Qed.

Lemma wp_If T (F: finType) (x : 'QReg[T]) (M : 'QM) (f : F -> cmd_) P : 
  wp (cond_ x M f) P = dualqm (liftf_fun (tm2m x x M)) (fun i=>wp (f i) P).
Proof.
rewrite /wp /wpso fsemE dualso_if dualqmE soE; apply eq_bigr=>i _.
by rewrite dualso_comp soE.
Qed.

Lemma wp_eqfsem (c1 c2 : cmd_) (P : 'FO) : 
  fsem c1 = fsem c2 -> wp c1 P = wp c2 P.
Proof. by move=>ef; rewrite /wp /wpso ef. Qed.

(* deduction step *)
Lemma wp_LP1 T (x : 'QReg[T]) (M : 'QM) b (c: cmd_) P : 
  wp (while_ x M b c) P = dualqm (liftf_fun (tm2m x x M)) (fun b'=>
    if b'==b then (wp c (wp (while_ x M b c) P)) else P).
Proof.
rewrite {1}(wp_eqfsem _ (while_fsem_fp x M b c)) wp_If.
f_equal; apply/funext=>b'; case: eqP=>_.
by rewrite -wp_SC. by rewrite -[in RHS](wp_Sk P).
Qed.

(* existence of ranking function *)
Lemma wp_LP2 T (x : 'QReg[T]) (M : 'QM) b (c: cmd_) P : 
  (exists t, ranking_function (liftf_fun (tm2m x x M)) b (fsem c)
    ((elemso (liftf_fun (tm2m x x M)) b)^*o (wp c (wp (while_ x M b c) P))) t).
Proof.
apply rankingP=> y/=; rewrite fsemE.
set f := (lftrace (H:=Hs msys setT) \o comp_lfun (P))%FUN.
have sf: scalar f by move=>a b' d; rewrite /f/= linearPr/= linearP/=.
set cc := (fun n: nat=> (\Tr (P \o whileso (liftf_fun (tm2m x x M)) b (fsem c) y))).
set cf := [sequence (fun i=> f (whileso_iter (liftf_fun (tm2m x x M)) b (fsem c) i y)) n.+1]_n.
have ->: (fun n : nat => \Tr ((elemso (liftf_fun (tm2m x x M)) b) ^*o
  (wpso (fsem c) (wpso (whileso (liftf_fun (tm2m x x M)) b (fsem c)) P)) \o
  whileso_incr (liftf_fun (tm2m x x M)) b (fsem c) n y)) = (fun n=>cc n - cf n).
apply/funext=>i; rewrite /wpso -dualso_trlfEV -dualso_trlfEV -!comp_soE 
  -whileso_incrE -dualso_trlfEV -comp_soE/= -whileso_incrED whileso_incr_while/=.
by rewrite /cc/cf/f/= !soE linearBr linearB/=.
have P1: (cc @ \oo --> (\Tr (P \o whileso (liftf_fun (tm2m x x M)) b (fsem c) y)))%classic by apply: cvg_cst. 
rewrite -(subrr (\Tr (P \o whileso (liftf_fun (tm2m x x M)) b (fsem c) y))).
apply ccvgnB=>[//|]; rewrite cvg_shiftS. 
move: (@while_sf_cvg _ (liftf_fun (tm2m x x M)) b (fsem c) _ y sf)=>//.
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

Lemma hoare_wp pt st S T (P: 'F_S) (Q: 'F_T) (c: cmd_) :
  ⊨l [pt,st] {P} c {Q} <-> 
  if pt then
    if st then liftf_lf P = (fsem c)^*o (liftf_lf Q)
          else liftf_lf P ⊑ (fsem c)^*o (liftf_lf Q)
  else
    if st then liftf_lf (P - \1) = (fsem c)^*o (liftf_lf (Q - \1))
          else liftf_lf (P - \1) ⊑ (fsem c)^*o (liftf_lf (Q - \1)).
Proof.
rewrite local_hoare.unlock; case: pt; case: st; (split=>[IH| + x]).
apply/eqP/eq_trden. 3:apply/lef_trden.
1,3: by move=>x; move: (IH x); rewrite dualso_trlfEV.
1,2: rewrite dualso_trlfEV. by move=>->. by move=>/lef_trden.
apply/eqP/eq_trden. 3:apply/lef_trden.
1,3: move=>x; move: (IH x).
all: rewrite dualso_trlfEV /cplmt -![\1 - _]opprB !linearN/= !comp_lfunNl !linearN/=.
by move=>/esym/oppr_inj. 1,3: rewrite lerN2//.
by move=>/lef_trden. by move=>->.
Qed.

Lemma no_while_enoughl st pt (c : Cmd_) S T (P: 'F_S) (Q: 'F_T) : no_while c ->
  ⊫tl { P } c { Q } -> ⊨l [pt,st] { P } c { Q }.
Proof.
move=>P1; case: pt=>//; rewrite ?no_while_LPT// ?cmd_is_valid//;
by move=>/saturated_strong_L.
Qed.
Global Arguments no_while_enoughl [st pt c S T P Q].

Lemma local_hoareP pt st S T (P: 'FO_S) (c: cmd_) (Q: 'FO_T) :
  ⊨l [pt,st] { P } c { Q } -> ⊨g [pt,st] { liftf_lf P } c { liftf_lf Q }.
Proof.
rewrite local_hoare.unlock global_hoare.unlock=>IH x;
by move: (IH x); rewrite -?liftf_lf_cplmt.
Qed.
Global Arguments local_hoareP [pt st S T P c Q].

Lemma lec_eq (x y : C) : x = y -> x <= y.
Proof. by move=>->. Qed.

Lemma cplmtZ (U : chsType) (P : 'End(U)) a :
  (a *: P)^⟂ = (1 - a) *: \1 + a *: P^⟂.
Proof. by rewrite -!cplmtE scalerBl scalerBr scale1r addrA addrNK. Qed.

Lemma alter_LPT st S T (P : 'F_S) (Q : 'F_T) (c: cmd_) :
  ⊨pl [st] { P } c { Q } <-> ⊨tl [st] { P - \1 } c { Q - \1 }.
Proof. by rewrite !hoare_wp. Qed.

Lemma alter_LTP st S T (P : 'F_S) (Q : 'F_T) (c: cmd_) :
  ⊨tl [st] { P } c { Q } <-> ⊨pl [st] { \1 + P } c { \1 + Q }.
Proof. by rewrite alter_LPT addrC addKr addrC addKr. Qed.

Lemma Ax_00_LP S T (c: cmd_) :
  ⊨pl { (0 : 'F_S) } c { (0 : 'F_T) }.
Proof.
rewrite local_hoare.unlock=>x; 
by rewrite !cplmt0 !liftf_lf1 dualso_trlfEV; apply/lef_trden/dqo1_le1.
Qed.

Lemma Ax_N1N1_LT S T (c: cmd_) :
  ⊨tl { (-\1 : 'F_S) } c { (-\1 : 'F_T) }.
Proof. rewrite alter_LTP !subrr; apply Ax_00_LP. Qed.

Lemma Ax_00_LT st S T (c: cmd_) :
  ⊨tl [st] { (0 : 'F_S) } c { (0 : 'F_T) }.
Proof. by rewrite local_hoare.unlock=>x; rewrite !linear0 !comp_lfun0l; case: st. Qed.

(* rules for local total correctness *)
Lemma Ax_Ab_LT st T S (P: 'F_S) : ⊨tl[st] { (0 : 'F_T) } abort_ { P }.
Proof.
by rewrite local_hoare.unlock; case: st=>x; 
rewrite fsemE soE linear0 comp_lfun0r comp_lfun0l linear0.
Qed.
Global Arguments Ax_Ab_LT {st T S P}.

Lemma Ax_Ab_LP st T S (P: 'F_S) : ⊨pl[st] { (\1 : 'F_T) } abort_ { P }.
Proof.
by rewrite local_hoare.unlock; case: st=>x; 
rewrite fsemE soE cplmt1 linear0 comp_lfun0r comp_lfun0l linear0.
Qed.
Global Arguments Ax_Ab_LP {st T S P}.

Lemma Ax_Sk_L pt st S (P: 'F_S) : ⊨l[pt,st] { P } skip_ { P }.
Proof.
by apply/no_while_enoughl=>//;
rewrite local_hoare.unlock=>x; rewrite fsemE soE.
Qed.
Global Arguments Ax_Sk_L {pt st S P}.

Lemma Ax_In_L pt st T (x : 'QReg[T]) (v : 'NS) (F : finType) (onb : 'ONB(F;'Ht T)) S (P: 'F_S) : 
  ⊨l [pt, st] { \sum_i [> tv2v x (onb i) ; tv2v x v <] \O P \O [> tv2v x v ; tv2v x (onb i) <] } (init_ x v) { P }.
Proof.
apply/no_while_enoughl=>//; rewrite local_hoare.unlock=> y /=;
rewrite fsemE dualso_trlfEV -(initialso_onb _ (tv2v_fun _ x onb)); 
do !f_equal; rewrite liftfso_krausso dualso_krausE/= liftf_funE linear_sum/=.
by apply eq_bigr=>i _; rewrite -liftf_lf_adj adj_outp !liftf_lf_sdot.
Qed.
Global Arguments Ax_In_L [pt st T x v F] onb {S P}.

Lemma Ax_InF_L pt st T (x : 'QReg[T]) (v : 'NS) S : 
  ⊨l [pt,st] { (\1 : 'F_S) } (init_ x v) { [> tv2v x v ; tv2v x v <] }.
Proof.
apply/no_while_enoughl=>//; rewrite local_hoare.unlock=> y /=;
rewrite liftf_lf1 fsemE dualso_trlfEV liftfso_krausso dualso_krausE/= liftf_funE.
under eq_bigr do rewrite -liftf_lf_adj -!liftf_lf_comp adj_outp !(outp_comp, ns_dot, scale1r).
by rewrite -linear_sum/= sumonb_out liftf_lf1.
Qed.
Global Arguments Ax_InF_L {pt st T x v S}.

Lemma Ax_UT_L pt st T (x : 'QReg[T]) (U : 'FU) S (P: 'F_S) :
  ⊨l [pt,st] { (tf2f x x U)^A \O P \O (tf2f x x U)} (unitary_ x U) { P }.
Proof.
apply/no_while_enoughl=>//; rewrite local_hoare.unlock=> y/=;
rewrite fsemE dualso_trlfEV liftfso_formso.
do !f_equal; by rewrite dualso_formE/= !liftf_lf_sdot liftf_lf_adj.
Qed.
Global Arguments Ax_UT_L {pt st T x U S P}.

Lemma Ax_UTF_L pt st T (x : 'QReg[T]) (U : 'FU) S (P: 'F_S) :
  ⊨l [pt,st] { P } (unitary_ x U) { (tf2f x x U) \O P \O (tf2f x x U)^A }.
Proof.
apply/no_while_enoughl=>//; rewrite local_hoare.unlock=> y/=;
rewrite fsemE dualso_trlfEV liftfso_formso.
do !f_equal; rewrite dualso_formE/= !liftf_lf_sdot -liftf_lf_adj.
rewrite !comp_lfunA -liftf_lf_comp -!comp_lfunA -liftf_lf_comp unitaryf_form.
by rewrite !liftf_lf1 comp_lfun1l comp_lfun1r.
Qed.
Global Arguments Ax_UTF_L {pt st T x U S P}.

Lemma R_IF_L pt st T (F: finType) (x : 'QReg[T]) (M : 'QM) (f : F -> cmd_) S
  (P : F -> 'F_S) W (Q : 'F_W):
  (forall i, ⊨l [pt,st] { P i } (f i) { Q }) ->
  ⊨l [pt,st] { \sum_i (tf2f x x (M i))^A \O P i \O tf2f x x (M i)} (cond_ x M f) { Q }.
Proof.
case: pt; rewrite local_hoare.unlock.
- case: st=>IH y/=; rewrite fsemE ifso_elemE linear_sumr linear_sum/=;
  rewrite linear_suml !linear_sum/= ?ler_sum//; first apply eq_bigr; move=>i _;
  move: (IH i (elemso (liftf_fun (tm2m x x M)) i y))=>/= P1;
  rewrite soE liftf_funE !liftf_lf_sdot -?P1; last apply/(le_trans _ P1)/lec_eq;
  by rewrite soE liftf_lf_adj !comp_lfunA lftraceC !comp_lfunA.
have P0: liftf_lf (\sum_i (tf2f x x (M i))^A \O P i \O tf2f x x (M i))^⟂ = 
  \sum_i liftf_lf ((tf2f x x (M i))^A \O (P i)^⟂ \O tf2f x x (M i)).
  rewrite /cplmt linearB/= liftf_lf1 linear_sum/=.
  under [RHS]eq_bigr do rewrite sdotfBr sdotfBl linearB/=.
  rewrite big_split/= linear_sum/=; f_equal.
  rewrite -(qmeasure_tpE (liftf_fun (tm2m x x M))); apply eq_bigr=>i _.
  by rewrite /= liftf_funE !liftf_lf_sdot liftf_lf1 comp_lfun1r liftf_lf_adj.
case: st=>IH y/=; rewrite fsemE ifso_elemE linear_sumr linear_sum/= P0;
rewrite linear_suml linear_sum/= ?ler_sum//; first apply eq_bigr; move=>i _;
move: (IH i (elemso (liftf_fun (tm2m x x M)) i y))=>/= P1;
rewrite soE liftf_funE !liftf_lf_sdot ?P1; last apply/(le_trans P1)/lec_eq;
by rewrite soE liftf_lf_adj !comp_lfunA lftraceC !comp_lfunA.
Qed.
Global Arguments R_IF_L [pt st T F x M f S P W Q].

Lemma R_SC_L pt st T (Q: 'F_T) S W (P: 'F_S) (R: 'F_W) c1 c2 :
  ⊨l [pt,st] { P } c1 { Q } -> ⊨l [pt,st] { Q } c2 { R } -> 
    ⊨l [pt,st] { P } (seqc_ c1 c2) { R }.
Proof.
case: st; case: pt; rewrite local_hoare.unlock=>P1 P2 x; 
rewrite fsemE comp_soE; [rewrite P1 | rewrite -P1 
  | apply: (le_trans (P1 x)) | apply: (le_trans _ (P1 x))]; apply P2.
Qed.
Global Arguments R_SC_L [pt st T] Q [S W P] [R c1 c2].

Lemma R_Or_L pt S T (P : 'F_S) (Q : 'F_T) P' Q' c :
  (P' ⊑ P) -> (Q ⊑ Q') -> ⊨l [pt] { P } c { Q } -> ⊨l [pt] { P' } c { Q' }.
Proof.
rewrite local_hoare.unlock; case: pt; last rewrite cplmt_lef/=;
rewrite -[in X in X -> _]liftf_lf_lef=>/lef_trden P1;
last rewrite cplmt_lef; rewrite -liftf_lf_lef =>/lef_trden P2 IH x.
apply/(le_trans (P1 x))/(le_trans (IH x))/P2.
apply/(le_trans _ (P1 x))/(le_trans _ (IH x))/P2.
Qed.
Global Arguments R_Or_L [pt S T] P Q [P' Q' c].

(* loop for local partial correctness *)
(* P : false Q : true *)
Lemma R_LP_LP T (x : 'QReg[T]) (M : 'QM) b (D: cmd_) S (P Q : 'F_S) :
  let R := (tf2f x x (M (~~b)))^A \O P \O (tf2f x x (M (~~b))) 
           + (tf2f x x (M b))^A \O Q \O (tf2f x x (M b)) in 
  R ⊑ \1 -> ⊨pl { Q } D { R } -> ⊨pl { R } (while_ x M b D) { P }.
Proof.
move=>R; rewrite local_hoare.unlock.
set P' := fun b' => if b' == b then Q else P.
set R' := \sum_i (tf2f x x (M i))^A \O P' i \O (tf2f x x (M i)).
have eqR: R = R' by rewrite /R /R' addrC (big_boolb b)/=/P' eqxx neqb.
move=>PR P1 y; rewrite [in X in _ <= X]/= fsemE.
set f := (lftrace (H:=Hs msys setT) \o comp_lfun (liftf_lf P^⟂))%FUN.
have sf: scalar f by move=>a b' c; rewrite /f/= linearPr/= linearP/=.
suff: forall i, f (whileso_iter (liftf_fun (tm2m x x M)) b (fsem D) i y) <= \Tr (liftf_lf R^⟂ \o y).
by move=>/(while_sf_le_cst sf).
move=>n. suff : ⊨pl { R } (while_iter_ x M b D n) { P }.
  by rewrite local_hoare.unlock=>/(_ y); rewrite fsem_while_iter_.
elim: n=>[|n IH/=]; first rewrite local_hoare.unlock=>z.
  rewrite fsemE soE comp_lfun0r linear0 trlfM_ge0// /cplmt -?liftf_lf_ge0.
  by rewrite subv_ge0. by apply/denf_ge0.
rewrite eqR /R'; apply R_IF_L=>b'; rewrite /P'.
case: eqP=>_; last by apply: Ax_Sk_L.
by apply/(R_SC_L _ _ IH); rewrite local_hoare.unlock.
Qed.
Global Arguments R_LP_LP [T x M b D S P Q].

Lemma R_LP'_LP T (x : 'QReg[T]) (M : 'QM) b (D: cmd_) S (P Q : 'F_S) :
  let R := (tf2f x x (M (~~b)))^A \O P \O (tf2f x x (M (~~b))) 
           + (tf2f x x (M b))^A \O Q \O (tf2f x x (M b)) in 
  P ⊑ \1 -> Q ⊑ \1 -> ⊨pl { Q } D { R } -> ⊨pl { R } (while_ x M b D) { P }.
Proof.
move=>/= P1 Q1; apply: R_LP_LP.
rewrite -liftf_lf_lef liftf_lf1 linearD/= !liftf_lf_sdot addrC.
rewrite -(qmeasure_tpE (liftf_fun (tm2m x x M))) (big_boolb b)/= levD=>[||//];
rewrite -[X in _ ⊑ X \o _](comp_lfun1r)/= liftf_lf_adj liftf_funE lef_form=>//;
by rewrite -(liftf_lf1 _ S) liftf_lf_lef.
Qed.
Global Arguments R_LP'_LP [T x M b D S P Q].

(* P : false Q : true *)
(* how to locally represent ranking function? *)
(* Lemma R_LP_LP (S : {set L}) (M : 'QM_(bool;S)) (D: cmd_) T 
  (P Q : 'F_T) :
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

(* frame rule for partial correctness only holds when c is cptp *)
Lemma R_Frame_L pt st W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) (c : Cmd_) :
  (pt || no_while c) ->
  0%:VF ⊑ R -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊨l [pt,st] { P } c { Q } -> ⊨l [pt,st] { P \⊗ R } c { Q \⊗ R }.
Proof.
wlog ptt: pt / pt = true => [th_sym|].
case: pt=>????; last rewrite !no_while_LPT// ?cmd_is_valid//; by apply th_sym.
rewrite ptt disjointUX=>_ rge0 disc /andP[diss dist].
move: (fsem_local c)=>[E PE].
have subs : S :<=: ~: W by rewrite -disjointX_subset.
have subt : T :<=: ~: W by rewrite -disjointX_subset.
have subc : fvars c :<=: ~: W by rewrite -disjointX_subset.
rewrite local_hoare.unlock.
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

Lemma R_Frame_LT st W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) (c : cmd_) :
  (0 : 'F__) ⊑ R -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊨tl [st] { P } c { Q } -> ⊨tl [st] { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite disjointUX=> rge0 disc /andP[diss dist].
move: (fsem_local c)=>[E PE].
have subs : S :<=: ~: W by rewrite -disjointX_subset.
have subt : T :<=: ~: W by rewrite -disjointX_subset.
have subc : fvars c :<=: ~: W by rewrite -disjointX_subset.
rewrite local_hoare.unlock.
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
Global Arguments R_Frame_LT [st W R S T P Q c].

Lemma R_Framel_L pt st W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) (c : Cmd_) :
  (pt || no_while c) ->
  (0 : 'F__) ⊑ R -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊨l [pt,st] { P } c { Q } -> ⊨l [pt,st] { R \⊗ P } c { R \⊗ Q }.
Proof.
move=>P1 P2 P3 P4 P5; move: (R_Frame_L P1 P2 P3 P4 P5).
by rewrite -tenf_castC R_castl -[_ \⊗ R]tenf_castC R_castr.
Qed.
Global Arguments R_Framel_L [pt st W R S T P Q c].

Lemma R_El_L pt st (W S T : {set _}) (P : 'F_S) (Q : 'F_T) (c: cmd_) :
  [disjoint S & W] ->
  ⊨l [pt,st] { P \⊗ (\1 : 'F_W) } c { Q } <-> ⊨l [pt,st] { P } c { Q }.
Proof. by move=>P1; rewrite local_hoare.unlock !liftf_lf_cplmt liftf_lf_tenf1r. Qed.
Global Arguments R_El_L [pt st] W [S T P Q c].

Lemma R_Er_L pt st (W S T : {set _}) (P : 'F_S) (Q : 'F_T) (c: cmd_) :
  [disjoint T & W] ->
  ⊨l [pt,st] { P } c { Q \⊗ (\1 : 'F_W)} <-> ⊨l [pt,st] { P } c { Q }.
Proof. by move=>P1; rewrite local_hoare.unlock !liftf_lf_cplmt liftf_lf_tenf1r. Qed.
Global Arguments R_Er_L [pt st] W [S T P Q c].

Lemma R_TI_L pt st (W1 W2 : {set _}) S T (P : 'F_S) (Q : 'F_T) (c: cmd_) :
  [disjoint S & W1] -> [disjoint T & W2] ->
    ⊨l [pt,st] { P \⊗ (\1 : 'F_W1) } c { Q \⊗ (\1 : 'F_W2)} <-> ⊨l [pt,st] { P } c { Q }.
Proof. by move=>P1 P2; rewrite R_El_L// R_Er_L. Qed.
Global Arguments R_TI_L [pt st] W1 W2 [S T P Q c].

Lemma R_Scale_LT st S T (P : 'F_S) (Q : 'F_T) (c: cmd_) a :
  0 <= a -> ⊨tl [st] { P } c { Q } -> 
  ⊨tl [st] { a *: P } c { a *: Q }.
Proof.
move=>age0; rewrite local_hoare.unlock; case: st=>IH x; 
rewrite !linearZ/= !linearZl/= !linearZ/=.
by rewrite (IH x). by rewrite ler_wpM2l.
Qed.
Global Arguments R_Scale_LT [st S T P Q c].

Lemma R_Add_LT st S T (P1 P2 : 'F_S) (Q1 Q2 : 'F_T) (c: cmd_) :
  ⊨tl [st] { P1 } c { Q1 } -> ⊨tl [st] { P2 } c { Q2 }
    -> ⊨tl [st] { P1 + P2 } c { Q1 + Q2 }.
Proof.
rewrite local_hoare.unlock; case: st=>IH1 IH2 x; 
rewrite !linearD/= !linearDl/= !linearD/=.
by rewrite (IH1 x) (IH2 x). by rewrite lerD.
Qed.
Global Arguments R_Add_LT [st S T P1 P2 Q1 Q2 c].

Lemma R_Sum_LT st I (r : seq I) (Pr : pred I) S T (P : I -> 'F_S)
  (Q : I -> 'F_T) (c : cmd_) :
  (forall i, Pr i -> ⊨tl [st] { P i } c { Q i })
    -> ⊨tl [st] { \sum_(i <- r | Pr i) P i } c 
                  { \sum_(i <- r | Pr i) Q i }.
Proof.
elim/big_rec2: _=>[_|h P1 Q1 Ph IH P2]; first exact: Ax_00_LT.
by apply: R_Add_LT; [apply: P2|apply IH].
Qed.
Global Arguments R_Sum_LT [st I r Pr S T P Q c].

Lemma R_CC_LT st I (r : seq I) (Pr : pred I) S T (P : I -> 'F_S)
  (Q : I -> 'F_T) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨tl [st] { P i } c { Q i })
    -> ⊨tl [st] { \sum_(i <- r | Pr i) (a i *: P i) } c 
                  { \sum_(i <- r | Pr i) (a i *: Q i) }.
Proof.
elim/big_rec2: _=>[_|h P1 Q1 Ph IH P2]; first apply/Ax_00_LT.
apply: R_Add_LT; last by apply IH.
by apply: R_Scale_LT; move: (P2 _ Ph)=>[].
Qed.
Global Arguments R_CC_LT [st I r Pr S T] P Q a [c].

Lemma R_Scale_LP S T (P : 'F_S) (Q : 'F_T) (c: cmd_) a :
  0 <= a <= 1 -> ⊨pl { P } c { Q } -> 
  ⊨pl { a *: P } c { a *: Q }.
Proof.
move=>/andP[Pa1 Pa2]; rewrite !alter_LPT=>IH.
have H1 W (R : 'F_W) : a *: R - \1 = a *: (R - \1) + (1-a) *: (-\1).
by rewrite scalerBr scalerN scalerBl opprB addrA addrNK scale1r.
rewrite !H1; apply R_Add_LT; apply: R_Scale_LT=>//.
by rewrite subr_ge0. by apply Ax_N1N1_LT.
Qed.
Global Arguments R_Scale_LP [S T P Q c].

Lemma R_CC_LP I (r : seq I) (Pr : pred I) S T (P : I -> 'F_S)
  (Q : I -> 'F_T) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨pl { P i } c { Q i })
    -> (\sum_(i <- r | Pr i) a i <= 1)
      -> ⊨pl { \sum_(i <- r | Pr i) (a i *: P i) } c 
                  { \sum_(i <- r | Pr i) (a i *: Q i) }.
Proof.
move=>P1 P2; rewrite alter_LPT.
suff IH W (R : I -> 'F[msys]_W) : (\sum_(i <- r | Pr i) a i *: R i) - \1 = 
\sum_(i <- r | Pr i) a i *: (R i - \1) + (1-\sum_(i <- r | Pr i) a i) *: (-\1).
rewrite !IH; apply R_Add_LT. 
by apply: R_CC_LT=>i /P1; rewrite -alter_LPT.
apply: R_Scale_LT. by rewrite subr_ge0. apply Ax_N1N1_LT.
rewrite scalerN scalerBl opprB scale1r addrA scaler_suml -big_split/=.
by f_equal; apply eq_bigr=>i _; rewrite scalerBr addrNK.
Qed.
Global Arguments R_CC_LP [I r Pr S T] P Q a [c].

Lemma R_lim_L pt st S T (A : nat -> 'F_S) (B : nat -> 'F_T) (c : cmd_) :
  (forall i, ⊨l[pt,st] {A i} c {B i}) -> cvgn A -> cvgn B ->
    ⊨l[pt,st] {limn A} c {limn B}.
Proof.
move: A B; wlog ptt: pt / pt = true => [th_sym|].
case: pt. by apply th_sym.
move=>A B IH1 cA cB; rewrite alter_LPT.
have P2 W : continuous (fun x : 'F_W => x - \1) by apply: addl_continuous.
suff P1 W (C : nat -> 'F[msys]_W) : cvgn C ->
  limn C - \1 = limn ((fun x : 'F_W => x - \1)\o C)%FUN.
rewrite !P1//. apply: th_sym. by [].
by move=>i/=; rewrite -alter_LPT.
1,2: apply: is_vcvgn_mapV=>[|//]; apply P2.
move=>cC; rewrite vlimn_mapV=>[|//|//]; apply P2.
rewrite ptt=>A B IH cA cB; rewrite hoare_wp.
rewrite -!linear_lim//=. by apply: linear_is_cvg.
case: st IH=>IH; [apply: eq_lim=>i/=|apply: lev_lim=>[||i/=]].
1,4: by move: (IH i); rewrite hoare_wp.
all: by do ? [apply: linear_is_cvg=>//].
Qed.
Global Arguments R_lim_L [pt st S T A B c].

Lemma Ax_Inv_LP S (P : 'F_S) (c : cmd_) :
  P ⊑ \1 -> [disjoint fvars c & S] ->
    ⊨pl { P } c { P }.
Proof.
rewrite alter_LPT hoare_wp=>P1 P2; move: (fsem_local c)=>[E ->].
by rewrite liftfso_dual -(liftf_lf_tenf1l (S:=fvars c))//
  -liftf_lf_compT// liftfsoEf_compr 1?disjoint_sym// liftfsoEf !liftf_lf_compT//
  liftf_lf_lef lev_wnbreg2r ?dqo1_le1 ?subv_le0.
Qed.

Lemma R_Frame_LP W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) (c : cmd_) :
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

Lemma R_Frame_LPS W (R : 'F_W) S T (P : 'F_S) (Q : 'F_T) (c : Cmd_) :
  no_while c -> ((0 : 'F__) ⊑ R) -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
  ⊫pl { P } c { Q } -> ⊫pl { P \⊗ R } c { Q \⊗ R }.
Proof. by move=>??; rewrite !no_while_LPT// ?cmd_is_valid//; apply/R_Frame_LT. Qed.

Lemma R_SO_LT pt st S T (P : 'F_S) (Q : 'F_T) c W (E : 'QC_W) :
  ⊨l [pt,st] { P } c { Q } -> [disjoint fvars c & W] ->
  ⊨l [pt,st] { (liftfso E)^*o (liftf_lf P) } c { (liftfso E)^*o (liftf_lf Q) }.
Proof.
move=>+dis; rewrite !hoare_wp; move: (fsem_local c)=>[F->].
rewrite !liftf_lf_id !liftfso_dual !linearB/= !liftf_lf1
  -comp_soE liftfso_compC ?soE=>[//|]; case: pt; case: st.
by move=>->. apply: cp_preserve_order.
move=>/(f_equal (liftfso E ^*o)).
2: move=>/(cp_preserve_order (liftfso E ^*o))=>/=.
all: have H1: liftfso E ^*o \1 = \1 by rewrite -liftfso_dual qu1_eq1.
all: rewrite !linearB/= -!comp_soE -liftfso_compC=>[//|].
all: by rewrite !soE H1.
Qed.

Lemma R_Inner_LT S (u v : 'H_S) (c : cmd_) T W :
  `|u| <= 1 -> 
  ⊫tl { (\1 : 'F_T) } c { [> u ; u <] } ->
  ⊫tl { `|[< u ; v >]| ^+2 *: (\1 : 'F_W) } c { [> v ; v <] }.
Proof.
rewrite local_hoare.unlock; move=>Pu P1.
have P2: (fsem c)^*o (liftf_lf [> u ; u <]) = \1.
apply/le_anti/andP; split; apply/lef_trden=>x; move: (P1 x);
by rewrite liftf_lf1 dualso_trlfEV=>->.
move: (leh1 <[u]>%HS). rewrite leh_lef hs2lfE -liftf_lf_lef liftf_lf1.
move=>/(cp_preserve_order (fsem c)^*o)=>P3.
move: (le_trans P3 (dqo1_le1 (fsem c)^*o)).
rewrite/= hline_def hsE/= !linearZ/= P2 -{2}(scale1r \1) -subv_ge0.
have Pu_neq0: `|u| != 0. case: eqP=>///eqP; rewrite normr_eq0=>/eqP Pt; move: P2; 
by rewrite Pt !linear0=>/eqP; rewrite eq_sym oner_eq0.
rewrite -scalerBl pscalev_lge0 ?ltf01=>[//|].
rewrite subr_ge0 invf_le1 ?exprn_gt0 ?lt_def ?normr_ge0 ?Pu_neq0=>[//|//| P4].
have Pux: `|u| = 1. apply/le_anti; rewrite Pu/=; move: P4; rewrite expr_ge1//.
clear Pu P4. have Pul : <[u]>%HS%:VF = [>u; u<]. 
by rewrite hline_def hsE/= Pux expr1n invr1 scale1r.
have P4: forall w : 'H_S, [< w ; u >] = 0 -> 
  (fsem c)^*o (liftf_lf [> w ; w <]) = 0.
move=>w Po.
have: <[u]>%HS \o <[w]>%HS = 0.
by rewrite !hline_def !hsE/= linearZl/= linearZr/= outp_comp -conj_dotp Po conjC0 scale0r !scaler0.
move=>/suppU_comp0 P4.
move: (leh1 (supph <[u]> `|` supph <[w]>)%HS).
rewrite leh_lef P4 hs2lfE -liftf_lf_lef liftf_lf1=>P5.
have P6: (fsem c) ^*o (liftf_lf (<[u]>%:VF + <[w]>)%HS) ⊑ (fsem c) ^*o \1.
by apply/cp_preserve_order.
have P7: (fsem c) ^*o \1 ⊑ \1 by apply/dqo1_le1.
move: (le_trans P6 P7). rewrite -P2 !linearD/= Pul gev_addl=>/psdf_le0/=.
rewrite hline_def hsE/= !linearZ/==>/eqP.
case E: (`|w| == 0). by move: E; rewrite normr_eq0=>/eqP->; rewrite !linear0.
by rewrite scaler_eq0 invr_eq0 expf_eq0 E/==>/eqP.
pose liftv (x : 'H[msys]_S) := (castlf (erefl, setUCr _) (v2f x \⊗ (\1 : 'F_(~: S)))).
have P5 (x y : 'H_S) : liftf_lf [> x; y <] = (liftv x) \o (liftv y)^A.
rewrite liftf_lfE castlf_adj -castlf_complf tenf_adj adjf1 -tenf_comp ?disjoint0X//.
by rewrite comp_lfun1l v2f_adj comp_out.
have liftvD (x y : 'H_S) : liftv (x + y) = liftv x + liftv y.
by rewrite /liftv linearD/= tenfDl linearD.
have liftvZ (a : C) (x : 'H_S) : liftv (a *: x) = a *: liftv x.
by rewrite /liftv linearZ/= tenfZl linearZ.
have P6 i (w : 'H_S) : [< w; u >] = 0 -> 
  @krausop _ _ ((fsem c) ^*o) i \o (liftv w) = 0.
move=>/P4; rewrite krausE/==>/eqP; rewrite psumv_eq0=>[j _|].
by rewrite P5 -!comp_lfunA -adjf_comp comp_lfunA formV_gef0.
rewrite -big_all big_andE=>/forallP/=/(_ i).
by rewrite P5 -!comp_lfunA -adjf_comp comp_lfunA formV_eq0=>/eqP.
set v1 := <[u]>%HS v. set v2 := (~` <[u]>)%HS v.
have dv : v = v1 + v2 by move: (hs_vec_dec <[u]>%HS v).
have v2o : [< v2 ; u >] = 0.
move: (memh_proj (~` <[u]>)%HS v). rewrite memhOE hsOK -/v2 hline_def hsE/= 
  Pux expr1n invr1 scale1r outpE scaler_eq0 -[u == 0]normr_eq0 Pux oner_eq0 orbF 
  -[[<_;u>]]conj_dotp=>/eqP->; rewrite conjC0//.
have: (fsem c) ^*o (liftf_lf [> v; v <]) = (fsem c) ^*o (liftf_lf [> v1; v1 <]).
rewrite dv outpDl !outpDr !linearD/= -addrA. apply/subr0_eq.
rewrite addrC !addrA addNr add0r !krausE !big1/= ?addr0//.
1,2,3: move=>i _; rewrite P5 -!comp_lfunA -adjf_comp ?(P6 i v2 v2o).
1,3: by rewrite raddf0 !comp_lfun0r. by rewrite comp_lfunA (P6 i v2 v2o) comp_lfun0l.
rewrite /v1 Pul outpE outpZl outpZr scalerA -normCK !linearZ/= P2=>P7 x.
by rewrite dualso_trlfEV P7 liftf_lf1.
Qed.

Lemma R_PInner_LT S T (u : 'H_(S :|: T)) (v : 'H_S) (F : finType) 
  (onb : 'ONB(F;'H_T)) (c : cmd_) W1 W2 :
  `|u| <= 1 -> [disjoint S & T] ->
  ⊫tl { (\1 : 'F_W1) } c { [> u ; u <] } ->
  ⊫tl { (\sum_i (`|[< v ⊗v (onb i) ; u >]| ^+2)) *: (\1 : 'F_W2) } c { [> v ; v <] }.
Proof.
move=>P1 P2 P3; rewrite -(R_Er_L T)=>[//|].
rewrite -(sumonb_out onb) tenf_sumr scaler_suml.
apply: R_Sum_LT=>i _; rewrite tenf_outp -conj_dotp norm_conjC.
apply: R_Inner_LT=>//; apply: P3.
Qed.

Lemma lift_hoare pt st S T (P : 'F_S) (Q : 'F_T) (c : cmd_) (W : {set mlab}) 
  (ls : S :<=: W) (lt : T :<=: W) : 
    ⊨l [pt,st] {P} c {Q} <-> ⊨l [pt,st] {lift_lf ls P} c {lift_lf lt Q}.
Proof.
rewrite local_hoare.unlock; split=>IH x; move: (IH x); 
by rewrite -!lift_lf_cplmt /liftf_lf !lift_lf2 
  !(eq_irrelevance (fintype.subset_trans _ _) (subsetT S))
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
rewrite !liftfsoEf !liftf_lf_lef !levBlDr=>H5 H6.
have: P1 \⊗ P2 ⊑ (E1 ^*o (Q1 - \1) + \1) \⊗ (E2 ^*o (Q2 - \1) + \1).
by apply: lev_pbreg2; rewrite ?dis?H1?H3?H5?H6.
rewrite tenfDl !tenfDr tenf11 addrA -levBlDr.
have ->: E1^*o (Q1 - \1) \⊗ E2^*o (Q2 - \1) = 
E1^*o Q1 \⊗ E2^*o Q2 - E1^*o \1 \⊗ E2^*o \1 + 
(E1^*o (Q1 - \1) \⊗ (- E2^*o \1) + (- E1^*o\1) \⊗ E2 ^*o (Q2 - \1)).
by apply/eqP; rewrite eq_sym addrA tenfNl tenfNr subr_eq -tenfDl 
  -linearD/= addrNK !linearB/= tenfBl opprB addrA addrNK.
rewrite -addrA -addrA [X in _ - _ + X]addrACA -tenfDr -tenfDl=>H7.
have: P1 \⊗ P2 - \1 ⊑ E1 ^*o Q1 \⊗ E2 ^*o Q2 - E1 ^*o \1 \⊗ E2 ^*o \1.
apply: (le_trans H7). rewrite gev_addl lev_wnDl=>[||//].
apply: bregv_le0_ge0=>[//||]. 3: apply: bregv_ge0_le0=>[//||].
1,4: rewrite -opprB linearN/= oppv_le0; apply/cp_ge0; rewrite subv_ge0.
3,4: by rewrite addrC subv_ge0 dqo1_le1. apply: H2. apply H4.
rewrite -[in X in X -> _]liftf_lf_lef=>H8; 
apply: (le_trans H8); rewrite le_eqVlt; apply/orP; left; apply/eqP.
move: {+}dis; rewrite disjoint_sym=>dis1.
by rewrite !linearB/= -tenf11 -!liftf_lf_compT// liftfsoEf_compl// liftfsoEf
  liftfsoEf_compr// liftfsoEf_compl// !liftfsoEf liftfsoEf_compr// liftfsoEf.
Qed.

(* add Parametric Morphism ? *)
End LocalHoare.

Local Open Scope dirac_scope.
Section DiracHoare.
Implicit Type (S W Wl Wr: {set mlab}).

Lemma dirac_localP pt st S T (P: 'F_S) c (Q: 'F_T) :
  ⊨ [pt,st] { '[ P ] } c { '[ Q ] } <-> ⊨l [pt,st] { P } c { Q }.
Proof.
split; rewrite dirac_hoare.unlock.
move=>[S'[T']][/sqr_linP/orP[/eqP<-|/eqP->]][/sqr_linP/orP[/eqP<-|/eqP->]].
by rewrite !lind_id. 1,2,3: rewrite ?lind_id !linear0 !diracE;
rewrite local_hoare.unlock ?cplmt0 ?liftf_lf1 ?linear0//.
move=>H1. exists S. exists T. rewrite !lind_id; do !split=>//; apply/sqrdP.
Qed.
Global Arguments dirac_localP [pt st S T P c].

Lemma dirac_sqrP pt st S T (P : 'D_S) (Q : 'D_T) c :
  ⊨ [pt,st] { P } c { Q } <-> ⊨l [pt,st] { P S S } c { Q T T }.
Proof. by rewrite -dirac_localP {1}sqrdiracE {1}(sqrdiracE Q). Qed.
Global Arguments dirac_sqrP [pt st S T P Q].

Lemma no_while_enough st pt (c : Cmd_) P Q : no_while c ->
  ⊫t { P } c { Q } -> ⊨ [pt,st] { P } c { Q }.
Proof.
by rewrite dirac_hoare.unlock=>nc [S[T[PS[PT Pl]]]]; exists S; exists T; 
do 2 split=>//; apply/no_while_enoughl.
Qed.
Global Arguments no_while_enough [st pt c P Q].

Lemma R_back pt st (R P Q : 'D) c :
  R = P -> ⊨ [pt,st] { R } c { Q } -> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments R_back [pt st R P Q c].

Lemma R_forward pt st (R P Q : 'D) c :
  R = Q -> ⊨ [pt,st] { P } c { R } -> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments R_forward [pt st R P Q c].

Lemma R_eq2 pt st (P' Q' P Q : 'D) c :
  P' = P -> Q' = Q -> ⊨ [pt,st] { P' } c { Q' } -> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>->->. Qed.
Global Arguments R_eq2 [pt st P' Q' P Q c].

Lemma Ax_Sk pt st S (P : 'D_S) :
  ⊨ [pt,st] { P } skip_ { P }.
Proof. by rewrite dirac_sqrP sqrdiracE lind_id; apply Ax_Sk_L. Qed.
Global Arguments Ax_Sk [pt st S].

Lemma Ax_UT pt st T (x : 'QReg[T]) (U : 'FU) S (P : 'D_S) :
  ⊨ [pt,st] { '[U^A ; x] \· P \· '[U ; x]} (unitary_ x U) { P }.
Proof.
rewrite dirac_sqrP/= sqrdiracE/= QMemory.tlin.unlock !sdotd_correct !lind_id.
rewrite -tf2f_adj; apply Ax_UT_L.
Qed.
Global Arguments Ax_UT [pt st T x U S].

Lemma R_UT pt st (Q : 'D) W T (x : 'QReg[T]) (U : 'FU) (P : 'D_W) :
  Q = '[U^A ; x] \· P \· '[U ; x] -> ⊨ [pt,st] { Q } (unitary_ x U) { P }.
Proof. by move=>/esym P1; apply/(R_back P1)/Ax_UT. Qed.
Global Arguments R_UT [pt st Q W T x U P].

Lemma Ax_UTF pt st S T (x : 'QReg[T]) (U : 'FU) (P : 'D_S) :
  ⊨ [pt,st] { P } (unitary_ x U) {  '[U ; x] \· P \· '[U^A ; x] }.
Proof.
rewrite dirac_sqrP/= sqrdiracE/= QMemory.tlin.unlock !sdotd_correct !lind_id.
rewrite -tf2f_adj; apply Ax_UTF_L.
Qed.
Global Arguments Ax_UTF [pt st S T x U].

Lemma R_UTF pt st (Q : 'D) W T (x : 'QReg[T]) (U : 'FU) (P : 'D_W) :
  Q = '[U ; x] \· P \· '[U^A ; x] -> ⊨ [pt,st] { P } (unitary_ x U) { Q }.
Proof. by move=>/esym P1; apply/(R_forward P1)/Ax_UTF. Qed.
Global Arguments R_UTF [pt st Q W T x U P].

Lemma tenfI0 S T (f : 'F[msys]_S) (g : 'F_T) :
  [disjoint S & T] -> g != 0 -> (f \⊗ g)%VF = 0 -> f = 0.
Proof. by move=>dis /negPf P1 /eqP; rewrite tenf_eq0// P1 orbF=>/eqP. Qed.

Lemma R_El pt st W S (P : 'D_S) (Q : 'D) c :
  [disjoint S & W] ->
  ⊨ [pt,st] { P \⊗ \1_W } c { Q } <-> ⊨ [pt,st] { P } c { Q }.
Proof.
rewrite dirac_hoare.unlock.
move=>P1; symmetry; rewrite sqrdiracE tend_correct; split;
  move=>[S' [T]][/sqr_linP/=/orP[/eqP<-|/eqP P2]]; rewrite ?lind_id=>[[Pt P3]].
1,2: exists (S :|: W). 3,4: exists S. 
all: exists T; (do 2 ?(split=>//; do 1?apply/sqrdP)); rewrite !lind_id//.
1,3: move: P3; by rewrite R_El_L. 
all: move: {+}P2 P3=>->; rewrite linear0 diracE ?linear0l.
2: have ->: P S S = 0 by apply: (tenfI0 P1 _ P2); rewrite oner_neq0.
all: by rewrite local_hoare.unlock !liftf_lf_cplmt !linear0.
Qed.
Global Arguments R_El [pt st W S P Q c].

Lemma R_Er pt st W T (P : 'D) (Q : 'D_T) c :
  [disjoint T & W] ->
  ⊨ [pt,st] { P } c { Q \⊗ \1_W } <-> ⊨ [pt,st] { P } c { Q }.
Proof.
rewrite dirac_hoare.unlock.
move=>P1; symmetry; rewrite sqrdiracE tend_correct; split;
  move=>[S [T']][Ps][/sqr_linP/=/orP[/eqP<-|/eqP P2]]; rewrite ?lind_id=>P3.
all: exists S. 1,2: exists (T :|: W). 3,4: exists T. 
all: (do 2 ?(split=>//; do 1?apply/sqrdP)); rewrite !lind_id//.
1,3: move: P3; by rewrite R_Er_L. 
all: move: {+}P2 P3=>->; rewrite linear0 diracE ?linear0l.
2: have ->: Q T T = 0 by apply: (tenfI0 P1 _ P2); rewrite oner_neq0.
all: by rewrite local_hoare.unlock !liftf_lf_cplmt !linear0.
Qed.
Global Arguments R_Er [pt st W T P Q c].

Lemma R_TI pt st Wl Wr S T (P : 'D_S) (Q : 'D_T) c :
  [disjoint S & Wl] -> [disjoint T & Wr] ->
  ⊨ [pt,st] { P \⊗ \1_Wl } c { Q \⊗ \1_Wr } <-> ⊨ [pt,st] { P } c { Q }.
Proof. by move=>H1 H2; rewrite R_El/= ?R_Er//. Qed.
Global Arguments R_TI [pt st Wl Wr S T P Q c].

Lemma R_Et pt st W S T (P : 'D_S) (Q : 'D_T) c :
  [disjoint S :|: T & W] ->
  ⊨ [pt,st] { P \⊗ \1_W } c { Q \⊗ \1_W } <-> ⊨ [pt,st] { P } c { Q }.
Proof. by rewrite disjointUX=>/andP [P1]; move: P1; exact: R_TI. Qed.
Global Arguments R_Et [pt st W S T P Q c].

Lemma R_SC pt st (Q P R : 'D) c1 c2:
  ⊨ [pt,st] { P } c1 { Q } -> ⊨ [pt,st] { Q } c2 { R } -> 
    ⊨ [pt,st] { P } (seqc_ c1 c2) { R }.
Proof.
rewrite dirac_hoare.unlock=>[[S [T]][Ps [Pt P1]]].
rewrite -Ps -Pt=>[[T' [W [/sqr_linP/=/orP[/eqP P2|/eqP P3] [Pw]]]]].
  case: T' / P2; rewrite lind_id Ps=>P2; exists S; exists W;
  by do 2 split=>//; move: P1 P2; exact: R_SC_L.
move: P1; rewrite P3 linear0 diracE Ps=>P1 P2; exists S; exists W;
do 2 split=>//. apply: (R_SC_L (Q T T)); rewrite P3//.
by move: P2; rewrite local_hoare.unlock; rewrite !cplmt0 !liftf_lf1 !linear0.
Qed.
Global Arguments R_SC [pt st] Q [P R c1 c2].

Lemma R_Frame pt st W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T) (c : Cmd_) :
  (pt || no_while c) ->
  (0 : 'F_W) ⊑ R W W -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨ [pt,st] { P } c { Q } -> ⊨ [pt,st] { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite dirac_sqrP=>P0 P1 P2 P3 P4; move: (R_Frame_L P0 P1 P2 P3 P4).
by rewrite -dirac_localP -!tend_correct -!sqrdiracE.
Qed.
Global Arguments R_Frame [pt st W R S P T Q c].

Lemma R_Framel pt st W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T) (c : Cmd_) :
  (pt || no_while c) ->
  (0 : 'F_W) ⊑ R W W -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] -> 
  ⊨ [pt,st] { P } c { Q } -> ⊨ [pt,st] { R \⊗ P } c { R \⊗ Q }.
Proof. rewrite ![R \⊗ _]tendC; exact: R_Frame. Qed.
Global Arguments R_Framel [pt st W R S P T Q c].

Lemma R_Frame_T st W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T) c :
  (0 : 'F_W) ⊑ R W W -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨t [st] { P } c { Q } -> ⊨t [st] { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite dirac_sqrP=>P0 P1 P2 P3; move: (R_Frame_LT P0 P1 P2 P3).
by rewrite -dirac_localP -!tend_correct -!sqrdiracE.
Qed.
Global Arguments R_Frame_T [st W R S P T Q c].

Lemma R_Framel_T st W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T) c :
  (0 : 'F_W) ⊑ R W W -> 
  [disjoint (fvars c) & W] -> [disjoint S :|: T & W] -> 
  ⊨t [st] { P } c { Q } -> ⊨t [st] { R \⊗ P } c { R \⊗ Q }.
Proof. rewrite ![R \⊗ _]tendC; exact: R_Frame_T. Qed. 
Global Arguments R_Framel_T [st W R S P T Q c].

Lemma R_Frame_P W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T)  c :
  ((0 : 'F_W) ⊑ R W W) && (R W W ⊑ \1) -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨p { P } c { Q } -> ⊨p { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite dirac_sqrP=>P0 P1 P2 P3; move: (R_Frame_LP P0 P1 P2 P3).
by rewrite -dirac_localP -!tend_correct -!sqrdiracE.
Qed.
Global Arguments R_Frame_P [W R S P T Q c].

Lemma R_Framel_P W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T)  c :
  ((0 : 'F_W) ⊑ R W W) && (R W W ⊑ \1) -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊨p { P } c { Q } -> ⊨p { R \⊗ P } c { R \⊗ Q }.
Proof. rewrite ![R\⊗_]tendC; exact: R_Frame_P. Qed.
Global Arguments R_Framel_P [W R S P T Q c].

Lemma R_Frame_PS W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T) (c : Cmd_) :
  no_while c -> 0%:VF ⊑ R W W -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊫p { P } c { Q } -> ⊫p { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite dirac_sqrP=>P0 P1 P2 P3 P4; move: (R_Frame_LPS P0 P1 P2 P3 P4).
by rewrite -dirac_localP -!tend_correct -!sqrdiracE.
Qed.
Global Arguments R_Frame_PS [W R S P T Q c].

Lemma R_Framel_PS W (R : 'D_W) S (P : 'D_S) T (Q : 'D_T) (c : Cmd_) :
  no_while c -> 0%:VF ⊑ R W W -> 
    [disjoint (fvars c) & W] -> [disjoint S :|: T & W] ->
    ⊫p { P } c { Q } -> ⊫p { R \⊗ P } c { R \⊗ Q }.
Proof. rewrite ![R\⊗_]tendC; exact: R_Frame_PS. Qed.
Global Arguments R_Framel_PS [W R S P T Q c].

(* initialization *)
Lemma Ax_In_onb pt st T (x : 'QReg[T]) (v : 'NS) 
  (F : finType) (onb : 'ONB(F;'Ht T)) S (P: 'D_S) : 
  ⊨ [pt,st] { \sum_i (dform ('| v >< onb i ; x|) P) } (init_ x v) { P }.
Proof.
move: (@Ax_In_L pt st _ x v _ onb _ (P S S))=>/=.
rewrite -dirac_localP -sqrdiracE; apply/R_back.
rewrite linear_sum/=; apply eq_bigr=>i _.
rewrite -!sdotd_correct /dform -sqrdiracE -!outerM adjdM.
by rewrite tket_adj tbra_adj QMemory.tket.unlock QMemory.tbra.unlock.
Qed.
Global Arguments Ax_In_onb [pt st T x v F] onb [S].

Lemma Ax_InF pt st W T (x : 'QReg[T]) (v : 'NS) : 
  ⊨ [pt,st] { \1_W } (init_ x v) { '[ [> v ; v <] ; x ] }.
Proof.
apply/dirac_sqrP=>/=; rewrite QMemory.tlin.unlock !lind_id -tv2v_out;
by exact: Ax_InF_L.
Qed.
Global Arguments Ax_InF [pt st W T x].

(* if , R is provided *)
Lemma R_IF pt st T (F: finType) (x : 'QReg[T]) (M : 'QM) (f : F -> cmd_) S
  (P : F -> 'D_S) W (Q : 'D_W) :
  (forall i, ⊨ [pt,st] { P i } (f i) { Q }) ->
  ⊨ [pt,st] { \sum_i (dform '[ M i ; x ] (P i)) } (cond_ x M f) { Q }.
Proof.
move=>IH; have P1 i : ⊨l[pt,st] {(P i) S S} (f i) {Q W W}
  by rewrite -dirac_localP -!sqrdiracE.
move: (@R_IF_L pt st _ _ x M _ _ _ _ _ P1); rewrite -dirac_localP -sqrdiracE; 
apply/R_back; rewrite linear_sum/=; apply eq_bigr=>i _.
by rewrite -!sdotd_correct /dform -sqrdiracE QMemory.tlin.unlock lind_adj.
Qed.
Global Arguments R_IF [pt st T F x M f S P W Q].

(* while *)
Lemma R_LP_P T (x : 'QReg[T]) (M : 'QM) b (D: cmd_) S (P Q : 'D_S) :
  let R := dform '[M (~~b) ; x] P + dform '[M b ; x] Q in 
  P S S ⊑ \1 -> Q S S ⊑ \1 -> ⊨p { Q } D { R } -> ⊨p { R } (while_ x M b D) { P }.
Proof.
move=>R PP PQ.
suff ->: R = '[(tf2f x x (M (~~b)))^A \O P S S \O (tf2f x x (M (~~b))) 
                + (tf2f x x (M b))^A \O Q S S \O (tf2f x x (M b))].
  by rewrite !dirac_sqrP/= !lind_id; apply: R_LP'_LP; [apply PP|apply PQ].
by rewrite /R /dform linearD/= -!sdotd_correct QMemory.tlin.unlock !lind_adj -!sqrdiracE.
Qed.
Global Arguments R_LP_P [T x M b D S P Q].

(* move *)
Lemma led_elem (P Q : 'D[msys]) : 
  P ⊑ Q -> forall S, P S S ⊑ Q S S.
Proof. by rewrite -subv_ge0=>/ged0P[+ _]S; move=>/(_ S); rewrite !diracE subv_ge0. Qed.

Lemma led_liftf S W (P : 'D[msys]_S) (Q : 'D_W) :
  (P : 'D) ⊑ Q -> liftf_lf (P S S) ⊑ liftf_lf (Q W W).
Proof.
case E: (S == W).
by move: E=>/eqP P1; case: W / P1 Q=>Q/led_elem/(_ S); rewrite liftf_lf_lef.
move=>P1; move: P1 {+}P1=>/led_elem/(_ S)+/led_elem/(_ W).
rewrite sqrdiracE (sqrdiracE Q) !lind_id !lind_eq0r ?E// 1?eq_sym ?E//.
rewrite -liftf_lf_lef -[_ ⊑ Q W W]liftf_lf_lef !linear0; exact: le_trans.
Qed.

Lemma led_liftf_cplmt S W (P : 'D[msys]_S) (Q : 'D_W) :
  (P : 'D) ⊑ Q -> liftf_lf (Q W W)^⟂ ⊑ liftf_lf (P S S)^⟂.
Proof. rewrite !liftf_lf_cplmt -cplmt_lef; exact: led_liftf. Qed.

Lemma R_Orl pt (P Q : 'D) S (P' : 'D_S) (c : cmd_) :
  ((P' : 'D) ⊑ P) -> ⊨ [pt] { P } c { Q } -> ⊨ [pt] { P' } c { Q }.
Proof.
rewrite {1}dirac_hoare.unlock sqrdiracE =>+[S' [W' [P3 [P4]]]] IH.
rewrite -P3 -P4 dirac_localP; rewrite local_hoare.unlock in IH.
case: pt IH=>[IH/led_liftf/lef_trden| IH/led_liftf_cplmt/lef_trden];
rewrite !lind_id local_hoare.unlock=>P1 x.
apply/(le_trans (P1 x))/(le_trans (IH x)).
2: apply/(le_trans _ (P1 x))/(le_trans _ (IH x)).
all: by move: (P1 ((fsem c) x)).
Qed.
Global Arguments R_Orl [pt] P Q [S P' c].

Lemma R_Orr pt (P Q : 'D) S (Q' : 'D_S) (c : cmd_) :
  (Q ⊑ Q') -> ⊨ [pt] { P } c { Q } -> ⊨ [pt] { P } c { Q' }.
Proof.
rewrite {1}dirac_hoare.unlock sqrdiracE =>+[S' [W' [P3 [P4]]]] IH.
rewrite -P3 -P4 dirac_localP; rewrite local_hoare.unlock in IH.
case: pt IH=>[IH/led_liftf/lef_trden| IH/led_liftf_cplmt/lef_trden];
rewrite !lind_id local_hoare.unlock=>P1 x;
[apply/(le_trans (IH x))|apply/(le_trans _ (IH x))];
by move: (P1 ((fsem c) x)).
Qed.
Global Arguments R_Orl [pt] P Q [S P' c].

Lemma R_Or pt (P Q : 'D) S W (P' : 'D_S) (Q' : 'D_W) (c : cmd_) :
  ((P' : 'D) ⊑ P) -> (Q ⊑ Q') -> ⊨ [pt] { P } c { Q } -> ⊨ [pt] { P' } c { Q' }.
Proof. by move=>P1 P2 P3; move: (R_Orl _ _ P1 P3); apply: R_Orr. Qed.
Global Arguments R_Or [pt] P Q [S W P' Q' c].

Lemma alter_PT st S T (P : 'D_S) (Q : 'D_T) (c: cmd_) :
  ⊨p [st] { P } c { Q } <-> ⊨t [st] { (P : 'D) - \1_S } c { (Q : 'D) - \1_T }.
Proof. by rewrite !dirac_sqrP/= !(lind_id, diracE) alter_LPT. Qed.

Lemma alter_TP st S T (P : 'D_S) (Q : 'D_T) (c: cmd_) :
  ⊨t [st] { P } c { Q } <-> ⊨p [st] { \1_S + P } c { \1_T + Q }.
Proof. by rewrite alter_PT/= addrC addKr addrC addKr. Qed.

Lemma Ax_00_P (c: cmd_) : ⊨p { 0 } c { 0 }.
Proof. by move: (Ax_00_LP set0 set0 c); rewrite -dirac_localP/= linear0. Qed.

Lemma Ax_N1N1_T S T (c: cmd_) : ⊨t { - \1_S } c { - \1_T }.
Proof. by rewrite dirac_sqrP/= !(lind_id, diracE); exact: Ax_N1N1_LT. Qed.

Lemma Ax_00_T st (c: cmd_) : ⊨t [st] { 0 } c { 0 }.
Proof. by move: (Ax_00_LT st set0 set0 c); rewrite -dirac_localP/= linear0. Qed.

Lemma R_Scale_T st (P Q : 'D) (c: cmd_) (a : C) :
  0 <= a -> ⊨t [st] { P } c { Q } -> 
    ⊨t [st] { a *: P } c { a *: Q }.
Proof.
rewrite {1}dirac_hoare.unlock => Pa [S [T]][PS [PT IH]].
rewrite -PS -PT dirac_sqrP/= !(lind_id, diracE).
by apply: R_Scale_LT.
Qed.
Global Arguments R_Scale_T [st P Q c a].

Lemma R_Add_T st S T (P1 P2 : 'D_S) (Q1 Q2 : 'D_T) (c: cmd_) :
  ⊨t [st] { P1 } c { Q1 } -> ⊨t [st] { P2 } c { Q2 }
    -> ⊨t [st] { (P1 : 'D) + P2 } c { (Q1 : 'D) + Q2 }.
Proof.
rewrite sqrdiracE (sqrdiracE Q1) (sqrdiracE P2) (sqrdiracE Q2)
!dirac_sqrP/= !(lind_id, diracE); exact: R_Add_LT.
Qed.
Global Arguments R_Add_T [st S T P1 P2 Q1 Q2 c].

Lemma R_Sum_T st I (r : seq I) (Pr : pred I) S T (P : I -> 'D_S)
  (Q : I -> 'D_T) (c : cmd_) :
  (forall i, Pr i -> ⊨t [st] { P i } c { Q i })
    -> ⊨t [st] { \sum_(i <- r | Pr i) (P i : 'D) } c 
                { \sum_(i <- r | Pr i) (Q i : 'D) }.
Proof.
move=>IH; rewrite dirac_sqrP/= !dirac_sumE; 
by apply: R_Sum_LT=>i /IH; rewrite dirac_sqrP/=.
Qed.
Global Arguments R_Sum_T [st I r Pr S T] P Q [c].

Lemma R_CC_T st I (r : seq I) (Pr : pred I) S T (P : I -> 'D_S)
  (Q : I -> 'D_T) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨t [st] { P i } c { Q i })
    -> ⊨t [st] { \sum_(i <- r | Pr i) (a i *: (P i : 'D)) } c 
                  { \sum_(i <- r | Pr i) (a i *: (Q i : 'D)) }.
Proof. move=>IH; apply: R_Sum_T=>i /IH[]/=; apply/R_Scale_T. Qed.
Global Arguments R_CC_T [st I r Pr S T] P Q a [c].

Lemma R_Scale_P (P Q : 'D) (c: cmd_) (a : C) :
  0 <= a <= 1 -> ⊨p { P } c { Q } -> 
  ⊨p { a *: P } c { a *: Q }.
Proof.
rewrite {1}dirac_hoare.unlock => Pa [S [T]][PS [PT IH]].
rewrite -PS -PT dirac_sqrP/= !(lind_id, diracE).
by apply: R_Scale_LP.
Qed.
Global Arguments R_Scale_P [P Q c].

Lemma R_CC_P I (r : seq I) (Pr : pred I) S T (P : I -> 'D_S)
  (Q : I -> 'D_T) (a : I -> C) (c : cmd_) :
  (forall i, Pr i -> 0 <= a i /\ ⊨p { P i } c { Q i })
    -> (\sum_(i <- r | Pr i) a i <= 1)
      -> ⊨p { \sum_(i <- r | Pr i) (a i *: (P i : 'D)) } c 
                  { \sum_(i <- r | Pr i) (a i *: (Q i : 'D)) }.
Proof.
move=>P1 P2; have: forall i : I, Pr i -> 0 <= a i /\ ⊨pl { P i S S } c { Q i T T }.
by move=>i /P1[]; rewrite dirac_sqrP/=.
move=>/R_CC_LP/(_ P2); rewrite -dirac_localP; apply R_eq2; 
by rewrite linear_sum/=; apply eq_bigr=>i _; rewrite linearZ/= -sqrdiracE.
Qed.
Global Arguments R_CC_P [I r Pr S T] P Q a [c].

Lemma Ax_Inv_P S (P : 'D_S) (c : cmd_) :
  P S S ⊑ \1 -> [disjoint fvars c & S] ->
    ⊨p { P } c { P }.
Proof. rewrite dirac_sqrP; exact: Ax_Inv_LP. Qed.
Global Arguments Ax_Inv_P [S P c].

Lemma R_Inner S (u v : 'H_S) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫t { :1 } c { '[ [> u ; u <] ] } ->
  ⊫t { (`|[< u ; v >]| ^+2)%:D } c { '[ [> v ; v <] ] }.
Proof.
rewrite numd1I numdZ1 numd1I !dirac_sqrP/= !(lind_id,diracE);
by exact: R_Inner_LT.
Qed.

Lemma R_PInner S T (u : 'H_(S :|: T)) (v : 'H_S) (F : finType) 
  (onb : 'ONB(F;'H_T)) (c : cmd_) :
  `|u| <= 1 -> [disjoint S & T] ->
  ⊫t { :1 } c { '[ [> u ; u <] ] } ->
  ⊫t { (\sum_i (`|[< v ⊗v (onb i) ; u >]| ^+2))%:D } c { '[ [> v ; v <] ] }.
Proof.
by rewrite numd1I numdZ1 numd1I !dirac_sqrP/= !(lind_id,diracE); exact: R_PInner_LT.
Qed.

Lemma R_PC2_T st S1 T1 (P1 : 'D_S1) (Q1 : 'D_T1)
  S2 T2 (P2 : 'D_S2) (Q2 : 'D_T2) (c1 c2 : cmd_) :
  [disjoint fvars c1 :|: S1 :|: T1 & fvars c2 :|: S2 :|: T2] ->
  st || ((0%:VF ⊑ P1 S1 S1) && (0%:VF ⊑ P2 S2 S2)) 
  -> ⊨t [st] {P1} c1 {Q1} -> ⊨t [st] {P2} c2 {Q2}
  -> ⊨t [st] {P1 \⊗ P2} (c1;;c2) {Q1 \⊗ Q2}.
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
1,2: by rewrite -dirac_localP /lift_lf !lind_cast 
  -!tend_correct R_TI/= -?sqrdiracE// ?disjointXD.
rewrite -dirac_localP -!tend_correct /lift_lf !lind_cast -!tend_correct
  tendACA tendII tendACA tendII R_TI/= -?sqrdiracE//.
all: move: dis; rewrite/W1 /W2; setdec.
Qed.

Lemma R_PC2_P S1 T1 (P1 : 'D_S1) (Q1 : 'D_T1)
  S2 T2 (P2 : 'D_S2) (Q2 : 'D_T2) (c1 c2 : cmd_) :
  [disjoint fvars c1 :|: S1 :|: T1 & fvars c2 :|: S2 :|: T2] ->
  0%:VF ⊑ P1 S1 S1 -> Q1 T1 T1 ⊑ \1 -> 0%:VF ⊑ P2 S2 S2 -> Q2 T2 T2 ⊑ \1 
  -> ⊨p {P1} c1 {Q1} -> ⊨p {P2} c2 {Q2}
  -> ⊨p {P1 \⊗ P2} (c1;;c2) {Q1 \⊗ Q2}.
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
1,2: by rewrite -dirac_localP /lift_lf !lind_cast 
  -!tend_correct R_TI/= -?sqrdiracE// ?disjointXD.
rewrite -dirac_localP -!tend_correct /lift_lf !lind_cast -!tend_correct
  tendACA tendII tendACA tendII R_TI/= -?sqrdiracE//.
all: move: dis; rewrite/W1 /W2; setdec.
Qed.

Lemma R_PC_seq_T st (I : eqType) (r : seq I) (R : pred I) (S T : I -> {set mlab})
  (P : forall i, 'D_(S i)) (Q : forall i, 'D_(T i)) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> uniq r ->
  st \/ (forall i, R i -> (0 : 'D) ⊑ P i)
  -> (forall i, R i -> ⊨t [st] {P i} (c i) {Q i})
  -> ⊨t [st] {\ten_(i <- r | R i) (P i)} [for i <- r | R i do c i] {\ten_(i <- r | R i) (Q i)}.
Proof.
move=>dis+IH1 IH2; elim: r=>[_|a r IH].
rewrite !big_nil bigd; apply: Ax_Sk.
rewrite cons_uniq=>/andP[na ur]; move: {+}ur=>/IH; rewrite !big_cons; case E: (R a)=>//.
rewrite !bigdE; apply: R_PC2_T.
rewrite fvars_for -!big_split/=; apply/bigcup_disjoint_seqP=>i/andP[Pi Ri].
apply: dis=>//. by apply: (notin_in_neq na).
move: IH1=>[->//|Pi]; apply/orP; right. rewrite -!lin_gef0/= -!sqrdiracE Pi//=.
apply: tends_ge0_seq=>// i j Ri Rj nij; move: (dis i j Ri Rj nij); setdec.
by apply IH2.
Qed.

Lemma R_PC_T st (I : finType) (r : seq I) (R : pred I) (S T : I -> {set mlab})
  (P : forall i, 'D_(S i)) (Q : forall i, 'D_(T i)) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> 
  st \/ (forall i, R i -> (0 : 'D) ⊑ P i)
  -> (forall i, R i -> ⊨t [st] {P i} (c i) {Q i})
  -> ⊨t [st] {\ten_(i | R i) (P i)} [for i | R i do c i] {\ten_(i | R i) (Q i)}.
Proof. by move=>??; apply: R_PC_seq_T=>//; apply: index_enum_uniq. Qed.

Lemma R_PC_seq_P (I : eqType) (r : seq I) (R : pred I) (S T : I -> {set mlab})
  (P : forall i, 'D_(S i)) (Q : forall i, 'D_(T i)) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> uniq r ->
  (forall i, R i -> (0 : 'D) ⊑ P i) ->
  (forall i, R i -> (0 : 'D) ⊑ (Q i : 'D) ⊑ \1_(T i)) ->
  (forall i, R i -> ⊨p {P i} (c i) {Q i})
  -> ⊨p {\ten_(i <- r | R i) (P i)} [for i <- r | R i do c i] {\ten_(i <- r | R i) (Q i)}.
Proof.
move=>dis+IH1 IH2; elim: r=>[_ _|a r IH].
rewrite !big_nil bigd; apply: Ax_Sk.
rewrite cons_uniq=>/andP[na ur]; move: {+}ur=>/IH IH3 IH4; 
  rewrite !big_cons; case E: (R a)=>[|//].
rewrite !bigdE; apply: R_PC2_P=>/=.
rewrite fvars_for -!big_split/=; apply/bigcup_disjoint_seqP=>i/andP[Pi Ri].
apply: dis=>//. by apply: (notin_in_neq na).
1,3: rewrite -sqr_gef0 ?IH1//=.
2,3: rewrite -sqr_lef1/=. 2: by move: (IH2 _ E)=>/andP[].
2: suff: (0:'D) ⊑ \ten_(i <- r | R i) Q i ⊑ \1_(\bigcup_(i <- r | R i) T i)
  by move=>/andP[].
apply: tends_ge0_seq=>//. 2: apply: tends_ge0_le1_seq=>//.
1,2: move=>i j Ri Rj nij; move: (dis i j Ri Rj nij); setdec.
by apply: IH4. all: by apply: IH.
Qed.

Lemma R_PC_P (I : finType) (r : seq I) (R : pred I) (S T : I -> {set mlab})
  (P : forall i, 'D_(S i)) (Q : forall i, 'D_(T i)) (c : I -> cmd_) :
  (forall i j, R i -> R j -> i != j -> [disjoint fvars (c i) :|: (S i) :|: (T i) & 
    fvars (c j) :|: (S j) :|: (T j)]) -> 
  (forall i, R i -> (0 : 'D) ⊑ P i) ->
  (forall i, R i -> (0 : 'D) ⊑ (Q i : 'D) ⊑ \1_(T i)) ->
  (forall i, R i -> ⊨p {P i} (c i) {Q i})
  -> ⊨p {\ten_(i | R i) (P i)} [for i | R i do c i] {\ten_(i | R i) (Q i)}.
Proof. by move=>??; apply: R_PC_seq_P=>//; apply: index_enum_uniq. Qed.

End DiracHoare.

Section StateHoare.
Implicit Type (S W Wl Wr: {set mlab}).

Lemma stateE pt st (P Q : 'D) c :
  ⊨s [pt,st] { P } c { Q } <-> ⊨ [pt,st] { P \o P^A } c { Q \o Q^A }.
Proof. by rewrite state_hoare.unlock. Qed.
Global Arguments stateE [pt st P Q].

(* following : specification for states, all predicates are P \o P^A *)
(* rules for total correctness *)

Lemma no_while_enoughS st pt (c : Cmd_) P Q : no_while c ->
  ⊫ts { P } c { Q } -> ⊨s [pt,st] { P } c { Q }.
Proof. rewrite !stateE; exact: no_while_enough. Qed.
Global Arguments no_while_enoughS [st pt c P Q].

Lemma RS_forward pt st (R P Q : 'D) c :
  R = Q -> ⊨s [pt,st] { P } c { R } -> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments RS_forward [pt st R P Q c].

Lemma RS_back pt st (R P Q : 'D) c :
  R = P -> ⊨s [pt,st] { R } c { Q } -> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>->. Qed.
Global Arguments RS_back [pt st R P Q c].

Lemma RS_eq2 pt st (P' Q' P Q : 'D) c :
  P' = P -> Q' = Q -> ⊨s [pt,st] { P' } c { Q' } -> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>->->. Qed.
Global Arguments RS_eq2 [pt st P' Q' P Q c].

Lemma AxS_Sk pt st S T (P : 'D_(S,T)) :
  ⊨s [pt,st] { P } skip_ { P }.
Proof. rewrite stateE; apply/Ax_Sk. Qed.
Global Arguments AxS_Sk [pt st S T].

Lemma AxS_UT pt st T (x : 'QReg[T]) (U : 'FU) S S' (P : 'D_(S,S')) :
  S :<=: S' ->
  ⊨s [pt,st] { '[U^A; x] \· P } (unitary_ x U) { P }.
Proof.
rewrite stateE=>P1; apply/R_UT=>/=.
rewrite -!dotd_mul/= adjdG tlin_adj adjfK !dotdA_cond//=; move: P1; setdec.
Qed.
Global Arguments AxS_UT [pt st T x U S S' P].

Lemma AxV_UT pt st T (x : 'QReg[T]) (U : 'FU) S (P : 'Ket_S) :
  ⊨s [pt,st] { '[U^A;x] \· P } (unitary_ x U) { P }.
Proof. by apply/AxS_UT; rewrite sub0set. Qed.
Global Arguments AxV_UT [pt st T x U S].

(* whenever difficult to canonical '[U^A] \· P *)
Lemma RS_UT pt st (Q : 'D) T (x : 'QReg[T]) W W' (U : 'FU) (P : 'D_(W,W')) :
  W :<=: W' ->
  Q = '[U^A;x] \· P -> ⊨s [pt,st] { Q } (unitary_ x U) { P }.
Proof. by move=>P2 ->; apply/AxS_UT. Qed.
Global Arguments RS_UT [pt st Q T x W W' U P].

Lemma RV_UT pt st (Q : 'D) T (x : 'QReg[T]) W (U : 'FU) (P : 'Ket_W) :
  Q = '[U^A;x] \· P -> ⊨s [pt,st] { Q } (unitary_ x U) { P }.
Proof. by move=>/esym P1; apply/(RS_back P1)/AxV_UT. Qed.
Global Arguments RV_UT [pt st Q T x W U P].

Lemma AxS_UTF pt st T (x : 'QReg[T]) (U : 'FU) S S' (P : 'D_(S,S')) :
  S :<=: S' ->
  ⊨s [pt,st] { P } (unitary_ x U) { '[U;x] \· P }.
Proof.
rewrite stateE=>P1; apply/R_UTF; 
rewrite /= -!dotd_mul/= adjdG tlin_adj !dotdA_cond//=; move: P1; setdec.
Qed.
Global Arguments AxS_UTF [pt st T x U S S' P].

Lemma AxV_UTF pt st T (x : 'QReg[T]) (U : 'FU) S (P : 'Ket_S) :
  ⊨s [pt,st] { P } (unitary_ x U) { '[U;x] \· P }.
Proof. by apply/AxS_UTF; rewrite sub0set. Qed.
Global Arguments AxV_UTF [pt st T x U S] P.

Lemma RS_UTF pt st (P : 'D) T (x : 'QReg[T]) W W' (U : 'FU) (Q : 'D_(W,W')) :
  W :<=: W' ->
  P = '[U;x] \· Q -> ⊨s [pt,st] { Q } (unitary_ x U) { P }.
Proof. by move=>P2 ->; apply/AxS_UTF. Qed.
Global Arguments RS_UTF [pt st P T x W W' U Q].

Lemma RV_UTF pt st (P : 'D) T (x : 'QReg[T]) W (U : 'FU) (Q : 'Ket_W) :
  P = '[U;x] \· Q -> ⊨s [pt,st] { Q } (unitary_ x U) { P }.
Proof. by move=>/esym P1; apply/(RS_forward P1)/AxV_UTF. Qed.
Global Arguments RV_UTF [pt st P T x W U Q].

Lemma RS_El pt st W S S' (P : 'D_(S,S')) (Q : 'D) c :
  [disjoint S :|: S' & W] ->
  ⊨s [pt,st] { P \⊗ \1_W } c { Q } <-> ⊨s [pt,st] { P } c { Q }.
Proof.
rewrite disjointUX !stateE =>/andP[P1 P2].
by rewrite adjdT adjdI tend_mul/= ?muldI/= ?R_El.
Qed.
Global Arguments RS_El [pt st W S S' P Q c].

Lemma RS_Er pt st W T T' (P : 'D) (Q : 'D_(T,T')) c :
  [disjoint T :|: T' & W] ->
  ⊨s [pt,st] { P } c { Q \⊗ \1_W } <-> ⊨s [pt,st] { P } c { Q }.
Proof.
rewrite disjointUX !stateE=>/andP[P1 P2].
by rewrite adjdT adjdI tend_mul/= ?muldI/= ?R_Er.
Qed.
Global Arguments RS_Er [pt st W T T' P Q c].

Lemma RS_TI pt st Wl Wr S S' T T' (P : 'D_(S,S')) (Q : 'D_(T,T')) c :
  [disjoint S :|: S' & Wl] -> [disjoint T :|: T' & Wr] ->
  ⊨s [pt,st] { P \⊗ \1_Wl } c { Q \⊗ \1_Wr } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>H1 H2; rewrite RS_El/= ?RS_Er. Qed.
Global Arguments RS_TI [pt st Wl Wr S S' T T' P Q c].

Lemma RS_Et pt st W S S' T T' (P : 'D_(S,S')) (Q : 'D_(T,T')) c :
  [disjoint (S :|: S') :|: (T :|: T') & W] ->
  ⊨s [pt,st] { P \⊗ \1_W } c { Q \⊗ \1_W } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by rewrite disjointUX=>/andP [P1]; move: P1; exact: RS_TI. Qed.
Global Arguments RS_Et [pt st W S S' T T' P Q c].

Lemma RV_El pt st W S (P : 'Ket_S) (Q : 'D) c :
  [disjoint S & W] ->
  ⊨s [pt,st] { P \⊗ \1_W } c { Q } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>P1; apply RS_El; rewrite set0U. Qed.
Global Arguments RV_El [pt st W S P Q c].

Lemma RV_Er pt st W T (P : 'D) (Q : 'Ket_T) c :
  [disjoint T & W] ->
  ⊨s [pt,st] { P } c { Q \⊗ \1_W } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>P1; apply RS_Er; rewrite set0U. Qed.
Global Arguments RV_Er [pt st W T P Q c].

Lemma RV_TI pt st Wl Wr S T (P : 'Ket_S) (Q : 'Ket_T) c :
  [disjoint S & Wl] -> [disjoint T & Wr] ->
  ⊨s [pt,st] { P \⊗ \1_Wl } c { Q \⊗ \1_Wr } <-> ⊨s [pt,st] { P } c { Q }.
Proof. by move=>H1 H2; rewrite RV_Er/= ?RV_El. Qed.
Global Arguments RV_TI [pt st Wl Wr S T P Q c].

Lemma RV_Et pt st W S T (P : 'Ket_S) (Q : 'Ket_T) c :
  [disjoint S :|: T & W] ->
  ⊨s [pt,st] { P \⊗ \1_W } c { Q \⊗ \1_W } <-> ⊨s [pt,st] { P } c { Q }.
Proof. rewrite disjointUX=>/andP[P1 P2]; exact: RV_TI. Qed.
Global Arguments RV_Et [pt st W S T P Q c].

Lemma RS_SC pt st (Q P R : 'D) c1 c2:
  ⊨s [pt,st] { P } c1 { Q } -> ⊨s [pt,st] { Q } c2 { R } -> 
    ⊨s [pt,st] { P } (seqc_ c1 c2) { R }.
Proof. by rewrite !stateE; apply R_SC. Qed.
Global Arguments RS_SC [pt st] Q [P R c1 c2].

Lemma RS_Frame pt st W W' (R : 'D_(W,W')) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  (pt || no_while c) ->
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite !stateE=>P1 P2 P3 P4.
suff ->: ((P \⊗ R) \o (P \⊗ R) ^A) = ((P \o P^A) \⊗ (R \o R^A)).
suff ->: ((Q \⊗ R) \o (Q \⊗ R) ^A) = ((Q \o Q^A) \⊗ (R \o R^A)).
apply: R_Frame=>//. 
by rewrite /= wfdiracE adjd_lin muld_correct lind_id formV_gef0.
all: by rewrite adjdT tend_mul//; move: P3; rewrite disjointUX=>/andP[P5 P6].
Qed.
Global Arguments RS_Frame [pt st W W' R S S' P T T' Q c].

Lemma RS_Framel pt st W W' (R : 'D_(W,W')) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  (pt || no_while c) ->
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { R \⊗ P } c { R \⊗ Q }.
Proof. by rewrite ![R \⊗ _]tendC; apply RS_Frame. Qed.
Global Arguments RS_Framel [pt st W W' R S S' P T T' Q c].

Lemma RS_Frame_T st W W' (R : 'D_(W,W')) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite !stateE=>P1 P2 P3.
suff ->: ((P \⊗ R) \o (P \⊗ R) ^A) = ((P \o P^A) \⊗ (R \o R^A)).
suff ->: ((Q \⊗ R) \o (Q \⊗ R) ^A) = ((Q \o Q^A) \⊗ (R \o R^A)).
apply: R_Frame_T=>//. 
by rewrite /= wfdiracE adjd_lin muld_correct lind_id formV_gef0.
all: by rewrite adjdT tend_mul//; move: P2; rewrite disjointUX=>/andP[].
Qed.
Global Arguments RS_Frame_T [st W W' R S S' P T T' Q c].

Lemma RS_Framel_T st W W' (R : 'D_(W,W')) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { R \⊗ P } c { R \⊗ Q }.
Proof. rewrite ![R \⊗ _]tendC; exact: RS_Frame_T. Qed.
Global Arguments RS_Framel_T [st W W' R S S' P T T' Q c].

Lemma RS_Frame_P W W' (R : 'D_(W,W')) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  (R \o R^A) W' W' ⊑ \1 -> [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ps { P } c { Q } -> ⊨ps { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite !stateE=>P1 P2 P3 P4.
suff ->: ((P \⊗ R) \o (P \⊗ R) ^A) = ((P \o P^A) \⊗ (R \o R^A)).
suff ->: ((Q \⊗ R) \o (Q \⊗ R) ^A) = ((Q \o Q^A) \⊗ (R \o R^A)).
apply: R_Frame_P=>//=; apply/andP; split=>[|//].
by rewrite /= wfdiracE adjd_lin muld_correct lind_id formV_gef0.
all: by rewrite adjdT tend_mul//; move: P3; rewrite disjointUX=>/andP[P5 P6].
Qed.
Global Arguments RS_Frame_P [W W' R S S' P T T' Q c].

Lemma RS_Framel_P W W' (R : 'D_(W,W')) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  (R \o R^A) W' W' ⊑ \1 -> [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊨ps { P } c { Q } -> ⊨ps { R \⊗ P } c { R \⊗ Q }.
Proof. rewrite ![R\⊗_]tendC; exact: RS_Frame_P. Qed.
Global Arguments RS_Framel_P [W W' R S S' P T T' Q c].

Lemma RS_Frame_PS W W' (R : 'D_(W,W')) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  no_while c -> [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊫ps { P } c { Q } -> ⊫ps { P \⊗ R } c { Q \⊗ R }.
Proof.
rewrite !stateE=>P1 P2 P3 P4.
suff ->: ((P \⊗ R) \o (P \⊗ R) ^A) = ((P \o P^A) \⊗ (R \o R^A)).
suff ->: ((Q \⊗ R) \o (Q \⊗ R) ^A) = ((Q \o Q^A) \⊗ (R \o R^A)).
apply: R_Frame_PS=>//=.
by rewrite /= wfdiracE adjd_lin muld_correct lind_id formV_gef0.
all: by rewrite adjdT tend_mul//; move: P3; rewrite disjointUX=>/andP[P5 P6].
Qed.
Global Arguments RS_Frame_PS [W W' R S S' P T T' Q c].

Lemma RS_Framel_PS W W' (R : 'D_(W,W')) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  no_while c -> [disjoint (fvars c) & W'] -> 
  [disjoint (S :|: T) & W] -> [disjoint (S' :|: T') & W'] ->
  ⊫ps { P } c { Q } -> ⊫ps { R \⊗ P } c { R \⊗ Q }.
Proof. rewrite ![R\⊗_]tendC; exact: RS_Frame_PS. Qed.
Global Arguments RS_Framel_PS [W W' R S S' P T T' Q c].

Lemma RV_Frame pt st W (R : 'Ket_W) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  (pt || no_while c) ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { P \⊗ R } c { Q \⊗ R }.
Proof. by move=>P1 P2 P3; apply: RS_Frame=>//; rewrite disjointX0. Qed.
Global Arguments RV_Frame [pt st W R S S' P T T' Q c].

Lemma RV_Framel pt st W (R : 'Ket_W) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  (pt || no_while c) ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨s [pt,st] { P } c { Q } -> ⊨s [pt,st] { R \⊗ P } c { R \⊗ Q }.
Proof. by rewrite ![R \⊗ _]tendC; apply RV_Frame. Qed.
Global Arguments RV_Framel [pt st W R S S' P T T' Q c].

Lemma RV_Frame_T st W (R : 'Ket_W) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { P \⊗ R } c { Q \⊗ R }.
Proof. by move=>P1 P2 P3; apply: RS_Frame_T=>//; rewrite disjointX0. Qed.
Global Arguments RV_Frame_T [st W R S S' P T T' Q c].

Lemma RV_Framel_T st W (R : 'Ket_W) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ts [st] { P } c { Q } -> ⊨ts [st] { R \⊗ P } c { R \⊗ Q }.
Proof. by rewrite ![R \⊗ _]tendC; apply RV_Frame_T. Qed.
Global Arguments RV_Framel_T [st W R S S' P T T' Q c].

Lemma RV_Frame_P W (u : 'H_W) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  `|u| <= 1 ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ps { P } c { Q } -> ⊨ps { P \⊗ '|u> } c { Q \⊗ '|u> }.
Proof.
move=>P1 P2 P3; apply: RS_Frame_P=>//; rewrite ?disjointX0//=.
by rewrite ketd_adj outerM lind_id outp_le1// -hnorm_le1.
Qed.
Global Arguments RV_Frame_P [W u S S' P T T' Q c].

Lemma RV_Framel_P W (u : 'H_W) S S' (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) c :
  `|u| <= 1 ->
  [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊨ps { P } c { Q } -> ⊨ps { '|u> \⊗ P } c { '|u> \⊗ Q }.
Proof. rewrite !['|u>\⊗_]tendC; exact: RV_Frame_P. Qed.
Global Arguments RV_Framel_P [W u S S' P T T' Q c].

Lemma RV_Frame_PS W (u : 'H_W) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  no_while c -> [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊫ps { P } c { Q } -> ⊫ps { P \⊗ '|u> } c { Q \⊗ '|u> }.
Proof. by move=>P1 P2 P3; apply: RS_Frame_PS=>//; rewrite ?disjointX0. Qed.
Global Arguments RV_Frame_PS [W u S S' P T T' Q c].

Lemma RV_Framel_PS W (u : 'H_W) S S' 
  (P : 'D_(S,S')) T T' (Q : 'D_(T,T')) (c : Cmd_) :
  no_while c -> [disjoint (fvars c) & W] -> 
  [disjoint (S' :|: T') & W] ->
  ⊫ps { P } c { Q } -> ⊫ps { '|u> \⊗ P } c { '|u> \⊗ Q }.
Proof. rewrite !['|u>\⊗_]tendC; exact: RV_Frame_PS. Qed.
Global Arguments RV_Framel_PS [W u S S' P T T' Q c].

Lemma Ax_In pt st T (x : 'QReg[T]) (v : 'NS) S (P: 'D_S) : 
  ⊨ [pt,st] { (dform '|v;x> P) } (init_ x v) { P }.
Proof.
rewrite -(@R_El _ _ (mset x))/= 1?tendC; last first.
apply: (R_back _ (Ax_In_onb eb _)).
rewrite -tf2f1 -(sumonb_out eb) !linear_sum/= tend_suml.
apply eq_bigr=>i _; rewrite !dformE ?QMemory.tbra.unlock ?QMemory.tket.unlock//.
rewrite -tv2v_out -outerG -dotd_ten/=; last first.
rewrite -[in RHS]dotdA_cond/=; last first.
rewrite ['< _ | \· _]dotdC/=; last first. 
rewrite adjdM ketd_adj brad_adj -!dotd_mul/= !dotdA_cond//=.
all: setdec.
Qed.
Global Arguments Ax_In [pt st T x v S].

Lemma AxS_In pt st T (x : 'QReg[T]) (v : 'NS) S (P : 'D_S) : 
  ⊨s [pt,st] { '<v;x| \· P } (init_ x v) { P }.
Proof.
rewrite stateE; apply: (R_back _ (Ax_In _)).
rewrite dformE/= adjdG tket_adj tbra_adj -!dotd_mul/= !dotdA_cond//.
all: setdec.
Qed.
Global Arguments AxS_In [pt st T x v S].

Lemma AxV_In pt st T (x : 'QReg[T]) (v : 'NS) S (P : 'Ket_S) : 
  ⊨s [pt,st] { '<v;x| \· P } (init_ x v) { P }.
Proof.
rewrite stateE; apply: (R_back _ (Ax_In _)).
rewrite dformE/= adjdG tket_adj tbra_adj -!dotd_mul/= !dotdA_cond//.
all: setdec.
Qed.
Global Arguments AxV_In [pt st T x v S].

Lemma AxS_00_P (c: cmd_) : ⊨ps { 0 } c { 0 }.
Proof. rewrite stateE mul0d; exact: Ax_00_P. Qed.

Lemma AxS_00_T st (c: cmd_) : ⊨ts [st] { 0 } c { 0 }.
Proof. rewrite stateE mul0d; exact: Ax_00_T. Qed.

Lemma AxV_Inv_P S (u : 'H_S) (c : cmd_) :
  `|u| <= 1 -> [disjoint fvars c & S] ->
    ⊨ps { '|u> } c { '|u> }.
Proof.
move=>P; rewrite stateE ketd_adj outerM; apply: Ax_Inv_P.
by rewrite/= lind_id outp_le1// -hnorm_le1.
Qed.
Global Arguments AxV_Inv_P [S u c].

Lemma RV_Inner S (u v : 'H_S) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫ts { :1 } c { '|u> } ->
  ⊫ts { (`|[< u ; v >]|)%:D } c { '|v> }.
Proof.
rewrite !stateE !ketd_adj !outerM !(adjd_num, numdM).
rewrite conjC1 mulr1 -normCK normr_id; exact: R_Inner.
Qed.

Lemma RS_Scale_T st (P Q : 'D) (c: cmd_) a :
  ⊨ts [st] { P } c { Q } -> 
    ⊨ts [st] { a *: P } c { a *: Q }.
Proof.
rewrite !stateE !adjdZ !muldZl !muldZr !scalerA; 
by apply/R_Scale_T/mul_conjC_ge0.
Qed.
Global Arguments RS_Scale_T [st P Q c a].

Lemma RS_Scale_P (P Q : 'D) (c: cmd_) a :
  `|a| <= 1 -> ⊨ps { P } c { Q } -> 
  ⊨ps { a *: P } c { a *: Q }.
Proof.
rewrite !stateE !adjdZ !muldZl !muldZr !scalerA=>P1;
by apply/R_Scale_P; rewrite mul_conjC_ge0 -normCK expr_le1.
Qed.
Global Arguments RS_Scale_P [P Q c].

End StateHoare.

(* with type, and some Parallel rule *)
Section TypedFinQHL.

(* initialization *)
Lemma tAx_In pt st T (x : 'QReg[T]) (v : 'NS('Ht T)) (A : 'End{T}) S (P: 'D_S) : 
  [disjoint mset x & S] ->
  ⊨ [pt, st] { [< v%:V ; A v%:V >] *: (P : 'D) } (init_ x v) { '[A;x] \⊗ P }.
Proof.
move=>dis; apply: (R_back _ (Ax_In _)).
by rewrite/= dformE tket_adj dotdTll//= tlin_bra dotdTrl//= tinner adj_dotEl numdTl.
Qed.
Global Arguments tAx_In [pt st T x v A S P].

Lemma tAx_InF pt st T (x : 'QReg[T]) (v : 'NS('Ht T)) S (P: 'D_S) : 
  [disjoint mset x & S] ->
  ⊨ [pt,st] { P } (init_ x v) { '[ [> v ; v <] ; x] \⊗ P }.
Proof.
move=>dis; apply: (R_back _ (tAx_In dis)).
by rewrite outpE !(ns_dot, scale1r).
Qed.
Global Arguments tAx_InF [pt st T x v S P].

(* initialization *)
Lemma tAxV_In pt st T (x : 'QReg[T]) (v : 'NS('Ht T)) (u : 'Ht T) S (P: 'Ket_S) : 
  [disjoint mset x & S] ->
  ⊨s [pt,st] { [< v%:V ; u >] *: (P : 'D) } (init_ x v) { '|u;x> \⊗ P }.
Proof.
move=>dis. rewrite stateE adjdZ adjdT muldZr muldZl scalerA.
rewrite tend_mul ?disjointX0//= tket_adj touterM.
apply: (R_back _ (tAx_In dis)).
by rewrite/= outpE dotpZr conj_dotp.
Qed.
Global Arguments tAxV_In [pt st T x v u S P].

Lemma tAxV_InF pt st T (x : 'QReg[T]) (v : 'NS('Ht T)) S (P: 'Ket_S) : 
  [disjoint mset x & S] ->
  ⊨s [pt,st] { P } (init_ x v) { '|v;x> \⊗ P }.
Proof.
by move=>dis; apply: (RS_back _ (tAxV_In dis)); rewrite ns_dot scale1r.
Qed.
Global Arguments tAxV_InF [pt st T x v S P].

(* if *)
Lemma tR_IF pt st (F : finType) T (x : 'QReg[T]) (M : 'QM(F;'Ht T)) (f : F -> cmd_) S
  (P : F -> 'D_S) W (Q : 'D_W) : 
  (forall i, ⊨ [pt,st] { P i } (f i) { Q }) ->
  ⊨ [pt,st] { \sum_i (dform ('[ M i ; x ]) (P i)) } (cond_ x M f) { Q }.
Proof. by move=>P1; apply: (R_back _ (R_IF P1)); rewrite/tm2m. Qed.
Global Arguments tR_IF [pt st F T x M f S P W Q].

Lemma tR_LP_P S (P Q : 'D_S) T (x : 'QReg[T]) (M : 'QM(bool;'Ht T)) b (D: cmd_) :
  let R := dform ('[ M (~~b) ; x ]) P + dform ('[ M b ; x ]) Q in 
  P S S ⊑ \1 -> Q S S ⊑ \1 -> ⊨p { Q } D { R } -> ⊨p { R } (while_ x M b D) { P }.
Proof.
by move=>R PP PQ; move: (@R_LP_P _ x M b D _ _ _ PP PQ).
Qed.
Global Arguments tR_LP_P [S P Q T x M b D].

Lemma tbR_LP_P S (P Q : 'D_S) (x : qreg Bool) b (D: cmd_) :
  let R := dform ('[ [> ''~~b ; ''~~b <] ; x ]) P + dform ('[ [> ''b ; ''b <] ; x ]) Q in 
  P S S ⊑ \1 -> Q S S ⊑ \1 -> 
    ⊨p { Q } D { R } -> ⊨p { R } [while tmeas[x] = b do D] { P }.
Proof.
move=>/= PP PQ. 
apply: (@tR_LP_P _ _ _ _ x tmeas b D PP PQ).
Qed.
Global Arguments tbR_LP_P [S P Q x b D].

(* parallel unitary transformation *)
Lemma Ax_UTP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'D_W) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i <- r | P i) '[Uf i; x i] in 
  ⊨ [pt,st] { U^A \· Q \· U} [for i <- r | P i do unitary_ (x i) (Uf i)] { Q }.
Proof.
rewrite/=; elim: r=>[_ _|i r IH +dis].
rewrite !big_nil bigd adjd1 dot1d dotd1; exact: Ax_Sk.
rewrite cons_uniq=>/andP[Pi ur].
rewrite !big_cons; case E: (P i); last by apply: IH.
rewrite bigdE; move: (IH ur dis); apply R_SC.
rewrite -!dformE; apply: R_UT=>/=.
rewrite/= !dformE adjdT tlin_adj [X in _ \· X]tendC -!dotd_ten/= ?dotdA//.
2: rewrite disjoint_sym.
all: apply/bigcup_disjoint_seqP=>j/andP[inj Pj].
all: by apply/dis=>//; move: (notin_in_neq Pi inj).
Qed.
Global Arguments Ax_UTP_seq [pt st F r P T x Uf W Q].

Lemma Ax_UTP pt st (F : finType) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'D_W) :
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i | P i) '[Uf i; x i] in 
  ⊨ [pt,st] { U^A \· Q \· U} [for i | P i do unitary_ (x i) (Uf i)] { Q }.
Proof. move=>IH; apply: Ax_UTP_seq=>[|i j _ _]; [apply: index_enum_uniq | exact: IH]. Qed.
Global Arguments Ax_UTP [pt st F P T x Uf W Q].

Lemma Ax_UTP_tuple pt st n T (x : 'QReg[T.[n]])
  (Uf : 'I_n -> 'FU('Ht T)) W (Q : 'D_W) :
  let U := \ten_i '[Uf i; x.[i]] in 
  ⊨ [pt,st] { U^A \· Q \· U} [for i do [ut x.[i] := Uf i]] { Q }.
Proof. by apply: Ax_UTP=>/=; tac_qwhile_auto. Qed.
Global Arguments Ax_UTP_tuple [pt st n T x ].

Lemma Ax_UTP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}])
  (Uf : forall i, 'FU('Ht (T i))) W (Q : 'D_W) :
  let U := \ten_i '[Uf i; x.-[i]] in 
  ⊨ [pt,st] { U^A \· Q \· U} [for i do [ut x.-[i] := Uf i]] { Q }.
Proof. by apply: Ax_UTP=>/=; tac_qwhile_auto. Qed.
Global Arguments Ax_UTP_ffun [pt st n T x ].

Lemma Ax_UTFP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'D_W) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i <- r | P i) '[Uf i; x i] in 
  ⊨ [pt,st] { Q } [for i <- r | P i do unitary_ (x i) (Uf i)] { U \· Q \· U^A }.
Proof.
move=>ur dis U; rewrite -dformEV.
move: (@Ax_UTP_seq pt st _ _ _ _ x Uf _ (dform U^A Q) ur dis).
rewrite/= -/U -dformE dform_comp/= tends_adj dotd_mul/= tendsM/==>[//|//|].
under eq_bigr do rewrite tlin_adj tlinM unitaryf_form -tlin1.
rewrite tendsI {1}dformE adjdI dotIdT/= dotdIT/= tendA tendII tendC.
by rewrite R_El// disjointXU -setDDl !disjointXD/=.
Qed.
Global Arguments Ax_UTFP_seq [pt st F r P T x Uf W Q].

Lemma Ax_UTFP pt st (F : finType) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'D_W) :
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i | P i) '[Uf i; x i] in 
  ⊨ [pt,st] { Q } [for i | P i do unitary_ (x i) (Uf i)] { U \· Q \· U^A }.
Proof. move=>IH; apply: Ax_UTFP_seq=>[|i j _ _]; [apply: index_enum_uniq | exact: IH]. Qed.
Global Arguments Ax_UTFP [pt st F P T x Uf W Q].

Lemma Ax_UTFP_tuple pt st n T (x : 'QReg[T.[n]])
  (Uf : 'I_n -> 'FU('Ht T)) W (Q : 'D_W) :
  let U := \ten_i '[Uf i; x.[i]] in 
  ⊨ [pt,st] { Q } [for i do [ut x.[i] := Uf i]] { U \· Q \· U^A }.
Proof. by apply: Ax_UTFP=>/=; tac_qwhile_auto. Qed.
Global Arguments Ax_UTFP_tuple [pt st n T x ].

Lemma Ax_UTFP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}])
  (Uf : forall i, 'FU('Ht (T i))) W (Q : 'D_W) :
  let U := \ten_i '[Uf i; x.-[i]] in 
  ⊨ [pt,st] { Q } [for i do [ut x.-[i] := Uf i]] { U \· Q \· U^A }.
Proof. by apply: Ax_UTFP=>/=; tac_qwhile_auto. Qed.
Global Arguments Ax_UTFP_ffun [pt st n T x ].

Lemma AxV_UTP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'Ket_W) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i <- r | P i) '[Uf i; x i] in 
  ⊨s [pt,st] { U^A \· Q } [for i <- r | P i do [ut (x i) := Uf i]] { Q }.
Proof.
move=>ur dis U; rewrite stateE; apply: (R_back _ (Ax_UTP_seq ur dis)).
by rewrite -/U/= adjdG adjdK -!dotd_mul/= -/U !dotdA_cond// ?disjoint0X// setD0
  ?disjointX0// set0U disjointXD.
Qed.
Global Arguments AxV_UTP_seq [pt st F r P T x Uf W Q].

Lemma AxV_UTP pt st (F : finType) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'Ket_W) :
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i | P i) '[Uf i; x i] in 
  ⊨s [pt,st] { U^A \· Q } [for i | P i do [ut (x i) := Uf i]] { Q }.
Proof. move=>IH; apply: AxV_UTP_seq=>[|i j _ _]; [apply: index_enum_uniq | exact: IH]. Qed.
Global Arguments AxV_UTP [pt st F P T x Uf W Q].

Lemma AxV_UTP_tuple pt st n T (x : 'QReg[T.[n]])
  (Uf : 'I_n -> 'FU('Ht T)) W (Q : 'Ket_W) :
  let U := \ten_i '[Uf i; x.[i]] in 
  ⊨s [pt,st] { U^A \· Q } [for i do [ut x.[i] := Uf i]] { Q }.
Proof. by apply: AxV_UTP=>/=; tac_qwhile_auto. Qed.
Global Arguments AxV_UTP_tuple [pt st n T x ].

Lemma AxV_UTP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}])
  (Uf : forall i, 'FU('Ht (T i))) W (Q : 'Ket_W) :
  let U := \ten_i '[Uf i; x.-[i]] in 
  ⊨s [pt,st] { U^A \· Q } [for i do [ut x.-[i] := Uf i]] { Q }.
Proof. by apply: AxV_UTP=>/=; tac_qwhile_auto. Qed.
Global Arguments AxV_UTP_ffun [pt st n T x ].

Lemma AxV_UTFP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'Ket_W) :
  uniq r -> (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i <- r | P i) '[Uf i; x i] in 
  ⊨s [pt,st] { Q } [for i <- r | P i do [ut (x i) := Uf i]] { U \· Q }.
Proof.
move=>ur dis U; rewrite stateE; apply: (R_forward _ (Ax_UTFP_seq ur dis)).
by rewrite -/U/= adjdG -!dotd_mul/= -/U !dotdA_cond// ?disjoint0X// setD0
  ?disjointX0// set0U disjointXD.
Qed.
Global Arguments AxV_UTFP_seq [pt st F r P T x Uf W Q].

Lemma AxV_UTFP pt st (F : finType) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i])
  (Uf : forall i : F, 'FU('Ht (T i))) W (Q : 'Ket_W) :
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  let U := \ten_(i | P i) '[Uf i; x i] in 
  ⊨s [pt,st] { Q } [for i | P i do [ut (x i) := Uf i]] { U \· Q }.
Proof. move=>IH; apply: AxV_UTFP_seq=>[|i j _ _]; [apply: index_enum_uniq | exact: IH]. Qed.
Global Arguments AxV_UTFP [pt st F P T x Uf W Q].

Lemma AxV_UTFP_tuple pt st n T (x : 'QReg[T.[n]])
  (Uf : 'I_n -> 'FU('Ht T)) W (Q : 'Ket_W) :
  let U := \ten_i '[Uf i; x.[i]] in 
  ⊨s [pt,st] { Q } [for i do [ut x.[i] := Uf i]] { U \· Q }.
Proof. by apply: AxV_UTFP=>/=; tac_qwhile_auto. Qed.
Global Arguments AxV_UTFP_tuple [pt st n T x ].

Lemma AxV_UTFP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}])
  (Uf : forall i, 'FU('Ht (T i))) W (Q : 'Ket_W) :
  let U := \ten_i '[Uf i; x.-[i]] in 
  ⊨s [pt,st] { Q } [for i do [ut x.-[i] := Uf i]] { U \· Q }.
Proof. by apply: AxV_UTFP=>/=; tac_qwhile_auto. Qed.
Global Arguments AxV_UTFP_ffun [pt st n T x ].

Lemma tAx_InP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) (A : forall i : F, 'End{T i}) W (Q : 'D_W):
  (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  uniq r ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨ [pt,st] { (\prod_(i <- r | P i) [< (v i)%:V ; A i (v i)%:V >]) *: (Q : 'D) } 
    [for i <- r | P i do init_ (x i) (v i)]
    { (\ten_(i <- r | P i) '[A i; x i]) \⊗ Q }.
Proof.
move=>disx; elim: r W Q=>[W Q _ _ |i r IH W Q + disw].
  by rewrite !big_nil bigd scale1r ten1d; exact: Ax_Sk.
rewrite !big_cons cons_uniq=>/andP[pi ur]; case E: (P i); last by apply: IH.
move: {+}E; rewrite [CMD]fsem_seqC_mset; last first.
rewrite bigdE=>_; rewrite -tendA mulrC -scalerA.
apply: (R_SC _ _ (tAx_In _ )).
rewrite/= -tendZr; apply: IH=>//.
rewrite disjointXU [X in _ && X]disjoint_sym disw// andbT.
2: rewrite /= fvars_for /=.
all: apply/bigcup_disjoint_seqP=>j/andP[inj Pj];
  by apply/(disx _ _ _ _ (notin_in_neq pi inj)).
Qed.
Global Arguments tAx_InP_seq [pt st F r P T x v A W Q].

Lemma tAx_InP pt st (F : finType) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) (A : forall i : F, 'End{T i}) W (Q : 'D_W):
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨ [pt,st] { (\prod_(i | P i) [< (v i)%:V ; A i (v i)%:V >]) *: (Q : 'D) } 
    [for i | P i do init_ (x i) (v i)]
    { (\ten_(i | P i) '[A i; x i]) \⊗ Q }.
Proof. move=>IH; apply: tAx_InP_seq=>[i j _ _|]; [exact: IH | apply: index_enum_uniq]. Qed.
Global Arguments tAx_InP [pt st F P T x v A W Q].

Lemma tAx_InP_tuple pt st n T (x : 'QReg[T.[n]]) 
  (v : 'I_n -> 'NS('Ht T)) (A : 'I_n -> 'End{T}) W (Q : 'D_W):
  (forall i, [disjoint W & mset <{x.[i]}>]) ->
  ⊨ [pt,st] { (\prod_i [< (v i)%:V ; A i (v i)%:V >]) *: (Q : 'D) } 
    [for i do [it x.[i] := v i]]
    { (\ten_i '[A i; x.[i]]) \⊗ Q }.
Proof. by move=>IH; apply: tAx_InP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAx_InP_tuple [pt st n T x v A W Q].

Lemma tAx_InP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}]) 
  (v : forall i, 'NS('Ht (T i))) (A : forall i, 'End{T i}) W (Q : 'D_W):
  (forall i, [disjoint W & mset <{x.-[i]}>]) ->
  ⊨ [pt,st] { (\prod_i [< (v i)%:V ; A i (v i)%:V >]) *: (Q : 'D) } 
    [for i do [it x.-[i] := v i]]
    { (\ten_i '[A i; x.-[i]]) \⊗ Q }.
Proof. by move=>IH; apply: tAx_InP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAx_InP_ffun [pt st n T x v A W Q].

Lemma tAx_InFP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) W (Q : 'D_W):
  (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  uniq r ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨ [pt,st] { Q } [for i <- r | P i do init_ (x i) (v i)]
    { (\ten_(i <- r | P i) '[[> v i ; v i <]; x i]) \⊗ Q }.
Proof.
move=>disx ur dis; apply: (R_back _ (tAx_InP_seq disx ur dis)).
rewrite big1 ?scale1r// =>i _; by rewrite outpE !(ns_dot, scale1r).
Qed.
Global Arguments tAx_InFP_seq [pt st F r P T x v W Q].

Lemma tAx_InFP pt st (F : finType) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) W (Q : 'D_W):
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨ [pt,st] { Q } [for i | P i do init_ (x i) (v i)]
    { (\ten_(i | P i) '[[> v i ; v i <]; x i]) \⊗ Q }.
Proof. move=>IH; apply: tAx_InFP_seq=>[i j _ _|]; [exact: IH | apply: index_enum_uniq]. Qed.
Global Arguments tAx_InFP [pt st F P T x v W Q].

Lemma tAx_InFP_tuple pt st n T (x : 'QReg[T.[n]]) 
  (v : 'I_n -> 'NS('Ht T)) (A : 'I_n -> 'End{T}) W (Q : 'D_W):
  (forall i, [disjoint W & mset <{x.[i]}>]) ->
  ⊨ [pt,st] { Q } [for i do [it x.[i] := (v i)]]
    { (\ten_i '[[> v i ; v i <]; x.[i]]) \⊗ Q }.
Proof. by move=>IH; apply: tAx_InFP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAx_InFP_tuple [pt st n T x v A W Q].

Lemma tAx_InFP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}]) 
  (v : forall i, 'NS('Ht (T i))) (A : forall i, 'End{T i}) W (Q : 'D_W):
  (forall i, [disjoint W & mset <{x.-[i]}>]) ->
  ⊨ [pt,st] { Q } [for i do [it x.-[i] := (v i)]]
    { (\ten_i '[[> v i ; v i <]; x.-[i]]) \⊗ Q }.
Proof. by move=>IH; apply: tAx_InFP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAx_InP_ffun [pt st n T x v A W Q].

Lemma tAxV_InP_seq pt st (F : eqType) (r : seq F) (P : pred F)
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) (u : forall i : F, 'Ht (T i)) W (Q : 'Ket_W):
  (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  uniq r ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨s [pt,st] { (\prod_(i <- r | P i) [< (v i)%:V ; (u i) >]) *: (Q : 'D) } 
    [for i <- r | P i do init_ (x i) (v i)]
    { (\ten_(i <- r | P i) '|u i; x i>) \⊗ Q }.
Proof.
move=>disx ur disw; rewrite stateE adjdT tend_mul/= ?disjointX0//.
rewrite tends_adj tendsM//==>[i j _ _ _|]; rewrite ?disjointX0//.
under [in POST]eq_bigr do rewrite tket_adj touterM.
apply: (R_back _ (tAx_InP_seq _ _ _))=>//=.
rewrite adjdZ muldZr muldZl scalerA; f_equal.
rewrite rmorph_prod -big_split/=; apply eq_bigr=>i _.
by rewrite outpE dotpZr conj_dotp.
Qed.
Global Arguments tAxV_InP_seq [pt st F r P T x v u W Q].

Lemma tAxV_InP pt st (F : finType) (P : pred F)
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) (u : forall i : F, 'Ht (T i)) W (Q : 'Ket_W):
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨s [pt,st] { (\prod_(i | P i) [< (v i)%:V ; (u i) >]) *: (Q : 'D) } 
    [for i | P i do init_ (x i) (v i)]
    { (\ten_(i | P i) '|u i; x i>) \⊗ Q }.
Proof. move=>IH; apply: tAxV_InP_seq=>[i j _ _|]; [exact: IH | apply: index_enum_uniq]. Qed.
Global Arguments tAxV_InP [pt st F P T x v u W Q].

Lemma tAxV_InP_tuple pt st n T (x : 'QReg[T.[n]]) 
  (v : 'I_n -> 'NS('Ht T)) (u : 'I_n -> 'Ht T) W (Q : 'Ket_W):
  (forall i, [disjoint W & mset <{x.[i]}>]) ->
  ⊨s [pt,st] { (\prod_i [< (v i)%:V ; (u i) >]) *: (Q : 'D) } 
    [for i do [it x.[i] := (v i)]]
    { (\ten_i '|u i; x.[i] >) \⊗ Q }.
Proof. by move=>IH; apply: tAxV_InP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAxV_InP_tuple [pt st n T x v u W Q].

Lemma tAxV_InP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}]) 
  (v : forall i, 'NS('Ht (T i))) (u : forall i, 'Ht (T i)) W (Q : 'Ket_W):
  (forall i, [disjoint W & mset <{x.-[i]}>]) ->
  ⊨s [pt,st] { (\prod_i [< (v i)%:V ; (u i) >]) *: (Q : 'D) } 
    [for i do [it x.-[i] := (v i)]]
    { (\ten_i '|u i; x.-[i] >) \⊗ Q }.
Proof. by move=>IH; apply: tAxV_InP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAxV_InP_ffun [pt st n T x v u W Q].

Lemma tAxV_InFP_seq pt st (F : eqType) (r : seq F) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) W (Q : 'Ket_W):
  (forall i j, P i -> P j -> (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  uniq r ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨s [pt,st] { Q } [for i <- r | P i do init_ (x i) (v i)]
    { (\ten_(i <- r | P i) '|v i; x i>) \⊗ Q }.
Proof.
move=>disx ur dis; apply: (RS_back _ (tAxV_InP_seq disx ur dis)).
by rewrite big1 ?scale1r// =>i _; rewrite ns_dot.
Qed.
Global Arguments tAxV_InFP_seq [pt st F r P T x v W Q].

Lemma tAxV_InFP pt st (F : finType) (P : pred F) 
  (T : F -> qType) (x : forall i : F, 'QReg[T i]) 
  (v : forall i : F, 'NS('Ht (T i))) W (Q : 'Ket_W):
  (forall i j, (i != j) -> [disjoint mset (x i) & mset (x j)]) ->
  (forall i, P i -> [disjoint W & mset (x i)]) ->
  ⊨s [pt,st] { Q } [for i | P i do init_ (x i) (v i)]
    { (\ten_(i | P i) '|v i; x i>) \⊗ Q }.
Proof. move=>IH; apply: tAxV_InFP_seq=>[i j _ _|]; [exact: IH | apply: index_enum_uniq]. Qed.
Global Arguments tAxV_InFP [pt st F P T x v W Q].

Lemma tAxV_InFP_tuple pt st n T (x : 'QReg[T.[n]]) 
  (v : 'I_n -> 'NS('Ht T)) (u : 'I_n -> 'Ht T) W (Q : 'Ket_W):
  (forall i, [disjoint W & mset <{x.[i]}>]) ->
  ⊨s [pt,st] { Q } [for i do [it x.[i] := v i]]
    { (\ten_i '|v i; x.[i] >) \⊗ Q }.
Proof. by move=>IH; apply: tAxV_InFP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAxV_InFP_tuple [pt st n T x v u W Q].

Lemma tAxV_InFP_ffun pt st n (T : 'I_n -> qType) (x : 'QReg[{qffun T}]) 
  (v : forall i, 'NS('Ht (T i))) (u : forall i, 'Ht (T i)) W (Q : 'Ket_W):
  (forall i, [disjoint W & mset <{x.-[i]}>]) ->
  ⊨s [pt,st] { Q } [for i do [it x.-[i] := v i]]
    { (\ten_i '|v i; x.-[i] >) \⊗ Q }.
Proof. by move=>IH; apply: tAxV_InFP=>//=; tac_qwhile_auto. Qed.
Global Arguments tAxV_InFP_ffun [pt st n T x v u W Q].

Lemma tR_Inner T (x : 'QReg[T]) (u v : 'Ht T) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫t { :1 } c { '[ [> u ; u <] ; x] } ->
  ⊫t { (`|[< u ; v >]| ^+2)%:D } c { '[ [> v ; v <] ; x] }.
Proof.
by rewrite QMemory.tlin.unlock -!tv2v_out -(tv2v_dot default_qmemory x) 
  -(tv2v_norm default_qmemory x); exact: R_Inner.
Qed.

Lemma tR_PInnerl T1 T2 (x : 'QReg[T1]) (y : 'QReg[T2]) (dis: [disjoint mset x & mset y])
  (u : 'Ht (T1 * T2)) (v : 'Ht T1) (c : cmd_) : 
  `|u| <= 1 ->
  ⊫t { :1 } c { '[ [> u ; u <] ; (x,y) ] } ->
  ⊫t { (\sum_i (`|[< v ⊗t ''i ; u >]| ^+2))%:D } c { '[ [> v ; v <] ; x ] }.
Proof.
move: dis; rewrite -disj_setE QMemory.tlin.unlock =>dis Pu H.
move: (R_PInner (u := casths (esym (mset_pair default_qmemory)) (tv2v <{ (x, y) }> u)) 
  (tv2v x v) (tv2v_fun _ y t2tv) (c := c)).
rewrite hnormE casths_dot -hnormE tv2v_norm=>/(_ Pu).
rewrite -disj_setE tv2v_out -castlf_outp lind_cast tv2v_out =>/(_ dis H).
by under eq_bigr do rewrite /tv2v_fun/= /tv2v_fun/= -casths_dotl tv2v_pair tv2v_dot.
Qed.

Lemma tR_PInnerr T1 T2 (x : 'QReg[T1]) (y : 'QReg[T2])
  (dis: [disjoint mset x & mset y]) (u : 'Ht (T1 * T2)) (v : 'Ht T2) (c : cmd_) : 
  `|u| <= 1 ->
  ⊫t { :1 } c { '[ [> u ; u <] ; (x,y) ] } ->
  ⊫t { (\sum_i (`|[< ''i ⊗t v ; u >]| ^+2))%:D } c { '[ [> v ; v <] ; y ] }.
Proof.
move: dis; rewrite -swaptf_norm disjoint_sym=>dis /(tR_PInnerl (x:=y) (y:=x) dis v (c:=c)).
rewrite touterT_swap !eq_qrE.
by under eq_bigr do rewrite -swaptf_dot swaptfK swaptfEtv.
Qed.

Lemma tRV_Inner T (x : 'QReg[T]) (u v : 'Ht T) (c : cmd_) :
  `|u| <= 1 -> 
  ⊫ts { :1 } c { '|u; x> } ->
  ⊫ts { (`|[< u ; v >]|)%:D } c { '|v; x> }.
Proof.
rewrite -(tv2v_dot default_qmemory x) -(tv2v_norm default_qmemory x);
rewrite QMemory.tket.unlock; exact: RV_Inner.
Qed.

End TypedFinQHL.

End FinQHL.
