From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.

Require Import mcextra mcaextra notation mxpred.
Require Import hermitian quantum hspace inhabited prodvect tensor.
Require Import orthomodular hspace_extra.
From quantum.dirac Require Import hstensor.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.

(****************************************************************************)
(*                       Basic Definitions for QLaws                        *)
(*  Including: Definition 5.2, 5.3, 5.4, 5.5                                *)
(****************************************************************************)

Local Notation C := hermitian.C.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* the unitary operator that changes the orthonormal basis *)
HB.lock
Definition onb_change (U V : chsType) (F : finType) (u : F -> U) 
  (v : F -> V) := \sum_i [> v i; u i <].

(* TODO : move to quantum.v, ONB to quantum measurement *)
(* quantum measurement generated by orthonormal basis *)
Definition onb_meas (F : finType) (U : chsType) (b : 'ONB(F;U)) i : 'End(U) 
  := [> b i ; b i <].
Lemma onb_measE F U b i : @onb_meas F U b i = [> b i ; b i <]. Proof. by []. Qed.
Lemma onb_meas_tp F U b : trace_presv (@onb_meas F U b).
rewrite/trace_presv -(sumonb_out b); apply/eqP; apply eq_bigr=>i _.
by rewrite/= !onb_measE adj_outp outp_comp onb_dot eqxx scale1r.
Qed.
HB.instance Definition _ F U b := isQMeasure.Build U U F (@onb_meas F U b) 
  (onb_meas_tp b).

Section ExtraDef.

Lemma formlf_liftf_sum_bound1 (I : finType) (H : I -> chsType) (U V : chsType) 
  (F : finType) (N : 'TN(F;U,V)) (S : {set I}) 
  (A : 'FB1(V, 'H[H]_S)) (B : 'FB1('H_S,U)) (C : F -> 'FB1('H_setT)) :
    (forall i j, i != j -> (N i)^A \o N j = 0) ->
    (\sum_i (N i \o (N i)^A) <= \1) ->
      \sum_i formlf (liftf_lf (A \o N i \o B)) (C i) \is bound1lf.
Proof.
move=>Pij PN.
pose TU := 'I_((dim U)-1).+1.
pose TV := 'I_((dim V)-1).+1.
pose TR := 'I_((dim 'H[H]_(~: S))-1).+1.
pose TS := 'I_((dim 'H[H]_S)-1).+1.
have CTU : dim U = dim ('Hs TU).
  by rewrite /= -ihb_dim_cast card_ord dim_proper_cast.
have CTV : dim V = dim ('Hs TV).
  by rewrite /= -ihb_dim_cast card_ord dim_proper_cast.
have CTR : dim 'H[H]_(~: S) = dim ('Hs TR).
  by rewrite /= -ihb_dim_cast card_ord dim_proper_cast.
have CTS : dim 'H[H]_S = dim ('Hs TS).
  by rewrite /= -ihb_dim_cast card_ord dim_proper_cast.
have CTA : dim 'H[H]_setT = dim ('Hs (TS * TR)%type).
  by rewrite -ihb_dim_cast/= card_prod !card_ord 
    !dim_proper_cast -tenv_dim ?disjointXC// finset.setUCr.
pose UU := default_iso CTU.
pose UV := default_iso CTV.
pose UR := default_iso CTR.
pose US := default_iso CTS.
(* pose UA := default_iso CTA. *)
pose UA_fun (v : 'H_[set: I]) :=
  \sum_i [< deltav (castidx (finset.setUCr _) i) ; v >] *: 
    (US (deltav (idxSl i)) ⊗t UR (deltav (idxSr i))).
have UA_fun_linear : linear UA_fun.
  move=>a u v; rewrite /UA_fun scaler_sumr -big_split; apply eq_bigr=>i _.
  by rewrite /= dotpPr scalerDl scalerA.
pose UAf := linfun UA_fun.
have UA_giso : UAf \is gisolf.
  apply/isolf_giso_dim; last by rewrite CTA.
  apply/isolf_dotP=>u.
  rewrite /UAf (linearlfE UA_fun_linear) lfunE/= /UA_fun idxSsum ?disjointXC//.
  rewrite -(casths_dot (esym (finset.setUCr S))) [casths _ u](onb_vec deltav) idxSsum ?disjointXC//.
  rewrite !pair_big/= !dotp_suml; apply eq_bigr=>i _.
  rewrite !dotp_sumr; apply eq_bigr=>j _.
  rewrite -!deltav_cast !casths_dotl !dotpZl !dotpZr; f_equal; f_equal.
  by rewrite !idxSUl !idxSUr ?disjointXC// tentv_dot -!adj_dotEl 
    !gisofKEl !dv_dot -idxBE !idxSUl !idxSUr ?disjointXC// -mulnb natrM.
pose UA := GisoLf_Build UA_giso.
pose NN i := (UV \o (N i) \o UU^A) ⊗f (\1 : 'End('Hs TR)).
have PNN1 : trace_nincr NN.
  rewrite /trace_nincr; under eq_bigr do rewrite /NN tentf_adj tentf_comp adjf1 comp_lfun1r.
  rewrite -tentf11 -tentf_suml lev_pbreg2// ?lef01//.
    by apply/sumv_ge0=>i _; rewrite form_gef0.
  under eq_bigr do rewrite !adjf_comp adjfK !comp_lfunA gisofKl comp_lfunACA.
  rewrite -linear_suml/= -linear_sumr/= -formlfE.
  by apply/formlf_bound1f_le1/is_trnincr.
pose AA := UA^A \o ((US \o A \o UV^A) ⊗f (\1 : 'End('Hs TR))).
pose BB := ((UU \o B \o US^A) ⊗f (\1 : 'End('Hs TR))) \o UA.
have AA_b : AA \is bound1lf.
  rewrite bound1lf_form_le1 /AA adjf_comp adjfK comp_lfunA gisofKr 
    tentf_adj tentf_comp adjf1 comp_lfun1l -tentf11.
  apply/lev_pbreg2=>//. apply: form_gef0. apply: lef01.
  rewrite !adjf_comp !adjfK !comp_lfunA gisofKl comp_lfunACA -formlfE.
  by apply/formlf_bound1f_le1/bound1f_form_le1.
have BB_b : BB \is bound1lf.
  rewrite bound1lf_form_le1 /BB adjf_comp comp_lfunA comp_lfunACA -formlfEV.
  apply/formlf_bound1f_le1; rewrite -tentf11 tentf_adj tentf_comp adjf1 comp_lfun1r.
  apply/lev_pbreg2=>[|||//]. apply: form_gef0. apply: lef01.
  rewrite !adjf_comp !adjfK !comp_lfunA gisofKl comp_lfunACA -formlfE.
  by apply/formlf_bound1f_le1/bound1f_form_le1.
have lP1 X : ((US \o X \o US^A) ⊗f \1) = UA \o liftf_lf X \o UA^A.
  apply/(intro_onb t2tv2_onbasis)=>[[a b]].
  apply/(intro_onbl t2tv2_onbasis)=>[[c d]].
  rewrite/= /tentv_fun/= tentf_apply !lfunE/= !lfunE/=.
  rewrite/= tentv_dot -adj_dotEl -[RHS]adj_dotEl.
  rewrite /liftf_lf/lift_lf castlfE casths_dotr.
  move: (esym (setUD_sub (finset.subsetT S))).
  move: (finset.setTD S)=>/esym P1; case: _ / P1=>P1.
  suff Pk i j : casths P1 (UAf^A (''i ⊗t ''j)) = (US^A ''i) ⊗v (UR^A ''j).
    by rewrite !Pk tenf_apply ?disjointXC// tenv_dot ?disjointXC// lfunE/= adj_dotEr gisofKEr.
  apply/(intro_onbl deltav)=>/=k.
  rewrite casths_dotr adj_dotEr /UAf (linearlfE UA_fun_linear) lfunE/= 
    /UA_fun dotp_suml (bigD1 k)//= big1=>[l /negPf nlk|];
    rewrite -deltav_cast (eq_irrelevance (esym P1) (finset.setUCr S)) casths_dot dv_dot.
    by rewrite nlk scale0r dot0p.
    by rewrite eqxx scale1r tentv_dot addr0 dv_split tenv_dot ?disjointXC// !adj_dotEr.
have lP X : UA^A \o ((US \o X \o US^A) ⊗f \1) \o UA = liftf_lf X.
  by rewrite lP1 !comp_lfunA gisofKl gisofEl comp_lfun1l.
have lE : forall i, liftf_lf ((A \o N i) \o B) = AA \o NN i \o BB.
  by move=>i; rewrite /AA /NN /BB comp_lfunACA tentf_comp comp_lfunA comp_lfunACA 
    tentf_comp !comp_lfunA !gisofKl !comp_lfun1l -lP !comp_lfunA.
under eq_bigr do rewrite lE (TraceNincr_BuildE PNN1) (Bound1Lf_BuildE AA_b) (Bound1Lf_BuildE BB_b).
apply: formlf_sum_bound1.
  by move=>i j /Pij P1; rewrite /NN tentf_adj tentf_comp !adjf_comp 
    !comp_lfunA gisofKl comp_lfunACA P1 comp_lfun0r comp_lfun0l ten0tf.
under eq_bigr do rewrite /NN tentf_adj tentf_comp adjf1 comp_lfun1r.
rewrite -tentf11 -tentf_suml lev_pbreg2// ?lef01//.
  by apply/sumv_ge0=>i _; rewrite formV_gef0.
under eq_bigr do rewrite !adjf_comp adjfK !comp_lfunA gisofKl comp_lfunACA.
rewrite -linear_suml/= -linear_sumr/= -formlfE.
by apply/formlf_bound1f_le1.
Qed.

(* property of orthonormal basis changes *)
Lemma onb_change_adj U V F u v :
  (@onb_change U V F u v)^A = onb_change v u.
Proof. by rewrite onb_change.unlock adjf_sum; under eq_bigr do rewrite adj_outp. Qed.
Lemma onb_change_bound1 U V F (u : 'PONB) (v : 'PONB) :
  @onb_change U V F u v \is bound1lf.
Proof.
rewrite bound1lf_form_le1 onb_change.unlock adjf_sum linear_suml/=.
apply/(le_trans _ (sumponb_out u))/lev_sum=>i _.
rewrite adj_outp outp_compl adjf_sum sum_lfunE/= (bigD1 i)//= big1.
by move=>j /negPf nji; rewrite adj_outp outpE ponb_dot nji scale0r.
by rewrite adj_outp outpE ponb_dot eqxx scale1r addr0.
Qed.
HB.instance Definition _ U V F (u : 'PONB(F;U)) (v : 'PONB(F;V)) 
  := isBound1Lf.Build U V (onb_change u v) (onb_change_bound1 u v).
Lemma onb_change_iso U V F (u : 'ONB) (v : 'PONB) :
  @onb_change U V F u v \is isolf.
Proof.
apply/isolfP; rewrite onb_change.unlock adjf_sum linear_suml/=.
rewrite -(sumonb_out u); apply eq_bigr=>i _.
rewrite adj_outp outp_compl adjf_sum sum_lfunE/= (bigD1 i)//= big1.
by move=>j /negPf nji; rewrite adj_outp outpE ponb_dot nji scale0r.
by rewrite adj_outp outpE ponb_dot eqxx scale1r addr0.
Qed.
HB.instance Definition _ U V F (u : 'ONB(F;U)) (v : 'PONB(F;V)) := 
  Bound1_isIsoLf.Build U V (onb_change u v) (onb_change_iso u v).
Lemma onb_change_giso U V F (u : 'ONB) (v : 'ONB) :
  @onb_change U V F u v \is gisolf.
Proof.
apply/gisolfP; split; rewrite onb_change.unlock adjf_sum linear_suml/=.
rewrite -(sumonb_out u). 2: rewrite -(sumonb_out v). 
all: apply eq_bigr=>i _; rewrite linear_sumr/= (bigD1 i)//= big1=>[j /negPf nji|];
  first by rewrite adj_outp outp_comp onb_dot eq_sym nji scale0r.
all: by rewrite addr0 adj_outp outp_comp onb_dot eqxx scale1r.
Qed.
HB.instance Definition _ U V F (u : 'ONB(F;U)) (v : 'ONB(F;V)) := 
  Iso_isGisoLf.Build U V (onb_change u v) (onb_change_giso u v).
Lemma onb_changeE U V F (u : 'ONB) v i : (@onb_change U V F u v) (u i) = v i.
Proof.
rewrite onb_change.unlock sum_lfunE (bigD1 i)//= big1=>[j /negPf nji |];
by rewrite outpE onb_dot ?nji ?scale0r// eqxx scale1r addr0.
Qed.

(* for orthonormal basis of qubit, swap the order *)
Definition onb_swap (U : chsType) (u : bool -> U) := fun b => u (~~ b).
Lemma onb_swap_onb U (u : 'ONB(bool; U)) i j : 
  [< @onb_swap U u i; @onb_swap U u j >] = (i == j)%:R.
Proof. by rewrite/onb_swap onb_dot (inj_eq negb_inj). Qed.
HB.instance Definition _ U (u : 'ONB(bool; U)) := 
  isONB.Build _ _ _ (@onb_swap_onb U u) (@onb_card _ _ u).
Lemma onb_swapK U u : onb_swap (@onb_swap U u) = u.
Proof. by apply/funext; case. Qed.
Lemma onb_change_swap (U : chsType) (u : bool -> U) :
  onb_change u (onb_swap u) = [> u true; u false <] + [> u false; u true <].
Proof. by rewrite onb_change.unlock big_bool/= /onb_swap addrC. Qed.

(* definition 5.2, binary measurement generated by state |phi> *)
Definition bvmeas T (phi : 'Hs T) := fun b => if b then [> phi; phi <]
  else \1 - [> phi ; phi <].
Notation "''[|' phi '>]'" := (bvmeas phi).
Lemma bvmeas_qm T (phi : 'NS('Hs T)) : trace_presv '[| phi >].
Proof.
by rewrite /trace_presv big_bool/= adjfB adjf1 adj_outp linearBl/= !linearBr/= 
  !comp_lfun1l comp_lfun1r outp_comp ns_dot scale1r subrr subr0 addrC subrK.
Qed.
HB.instance Definition _ T (phi : 'NS('Hs T)) := 
  isQMeasure.Build _ _ _ (bvmeas phi) (bvmeas_qm phi).

(* definition 5.4, complement of binary measurement *)
Definition bcmeas (U V : chsType) (M : bool -> 'Hom(U,V)) := fun b => M (~~ b).
Notation "M '^m⟂'" := (bcmeas M) (at level 8).
Lemma bcmeas_tn U V (M : 'TN(bool; U,V)) : trace_nincr (M ^m⟂).
Proof. by move: (@is_trnincr _ _ _ M); rewrite /trace_nincr !big_bool/= addrC. Qed.
HB.instance Definition _ U V (M : 'TN(bool; U,V)) :=
  isTraceNincr.Build _ _ _ (M ^m⟂) (bcmeas_tn M).
Lemma bcmeas_tp U V (M : 'QM(bool; U,V)) : trace_presv (M ^m⟂).
Proof. by move: (@is_trpresv _ _ _ M); rewrite /trace_presv !big_bool/= addrC. Qed.
HB.instance Definition _ U V (M : 'QM(bool; U,V)) :=
  TraceNincr_isQMeasure.Build _ _ _ (M ^m⟂) (bcmeas_tp M).

Section pmeas.
Variable (U : chsType).

(* example 5.1 (1) : binary projective measurement *)
Definition pmeas (P : {hspace U}) : bool -> 'End(U) :=
  fun b : bool => if b then P else (~` P)%HS.
Lemma pmeas_tp P : 
  trace_presv (@pmeas P).
Proof.
by rewrite /trace_presv bool_index unlock/= /reducebig/=
  /pmeas !hermf_adjE !projf_idem addr0 addrC hs2lfE subrK.
Qed.
HB.instance Definition _ (P : {hspace U}) := 
  isQMeasure.Build _ _ bool (@pmeas P) (@pmeas_tp P).

Lemma elemso_projTE (P : {hspace U}) : 
  elemso (pmeas P) true = formso P.
Proof. by rewrite /elemso /pmeas. Qed.
Lemma elemso_projFE (P : {hspace U}) : 
  elemso (pmeas P) false = formso (~` P)%HS.
Proof. by rewrite /elemso /pmeas. Qed.

Lemma pmeasO P : bcmeas (pmeas P) = pmeas (~` P)%HS.
Proof. by apply/funext; case=>/=; rewrite /pmeas /bcmeas//= hsOK. Qed.

Lemma pmeasO_qmE P : bcmeas (pmeas P) = pmeas (~` P)%HS :> 'QM.
Proof. by apply/qmeasureP; case=>/=; rewrite /pmeas /bcmeas//= hsOK. Qed.

End pmeas.

(* Definition 5.3 *)
Definition k_proportion (U : chsType) (A B : 'End(U)) (k : C) :=
  exists2 c : C, `|c| = k & A = c *: B.
Definition k_left_absorb (U : chsType) (A B : 'End(U)) k := 
  k_proportion (A \o B) B k.
Definition k_right_absorb (U : chsType) (A B : 'End(U)) k := 
  k_proportion (A \o B) A k.
Definition op_orthogonal (U : chsType) (A B : 'End(U)) := 
  A \o B = 0.

Notation "A '⋈_(' p ) B" := (k_proportion A B p) (at level 50, p, B at next level).
Notation "A '⋈_0' B" := (k_proportion A B 1) (at level 50, B at next level).
Notation "A ⋈ B" := (k_proportion A B 1) (at level 50, B at next level).
Notation "A '⋉_(' p ) B" := (k_left_absorb A B p) (at level 50, p, B at next level).
Notation "A '⋉_0' B" := (k_left_absorb A B 0) (at level 50, B at next level).
Notation "A ⋉ B" := (k_left_absorb A B 1) (at level 50, B at next level).
Notation "A '⋊_(' p ) B" := (k_right_absorb A B p) (at level 50, p, B at next level).
Notation "A '⋊_0' B" := (k_right_absorb A B 0) (at level 50, B at next level).
Notation "A ⋊ B" := (k_right_absorb A B 1) (at level 50, B at next level).
Notation "A ⊥ B" := (op_orthogonal A B) (at level 50, B at next level).

Lemma k_absorblE (U : chsType) (A B : 'End(U)) k : 
  A ⋉_(k) B <-> A \o B ⋈_(k) B.
Proof. by []. Qed.
Lemma k_absorbrE (U : chsType) (A B : 'End(U)) k : 
  A ⋊_(k) B <-> A \o B ⋈_(k) A.
Proof. by []. Qed.
Lemma op_ortholE (U : chsType) (A B : 'End(U)) :
  A ⊥ B <-> A ⋉_0 B.
Proof.
rewrite k_absorblE; split.
by exists 0; rewrite ?normr0// H scale0r.
by move=>[c /normr0_eq0 ->]; rewrite scale0r.
Qed.
Lemma op_orthorE (U : chsType) (A B : 'End(U)) :
  A ⊥ B <-> A ⋊_0 B.
Proof.
rewrite k_absorbrE; split.
by exists 0; rewrite ?normr0// H scale0r.
by move=>[c /normr0_eq0 ->]; rewrite scale0r.
Qed.
Lemma proportion1C (U : chsType) (A B : 'End(U)) :
  A ⋈ B <-> B ⋈ A.
Proof.
split; move=>[c] Pc /(f_equal (fun x => c^-1 *: x));
rewrite scalerA mulVf -1?normr_eq0 ?Pc ?oner_neq0// scale1r=>P1;
by exists (c^-1)%R=>//; rewrite normfV Pc invr1.
Qed.

(* definition 5.4 *)
Definition meas_entail (U : chsType) (M N : bool -> 'End(U)) := 
  N false ⊥ M true.
Definition meas_weaker (U : chsType) (M N : bool -> 'End(U)) :=
  (M true) ⋉ (N true).
Definition meas_pmeet (U : chsType) (K M N : bool -> 'End(U)) :=
  K true ⋈ (N true \o M true).
Notation "M '▶' N" := (meas_entail M N) (at level 50).
Notation "M '∝' N" := (meas_weaker M N) (at level 50).
Notation "M '≫' N" := (M ∝ N^m⟂) (at level 50).
Notation "K ≅ M & N" := (meas_pmeet K M N) (at level 50).

(* definition 5.5 *)
Definition meas_lcom (U : chsType) (M N : bool -> 'End(U)) :=
  M false \o N true = N true \o M false /\ 
  M true \o N true = N true \o M true.
Definition meas_rcom (U : chsType) (M N : bool -> 'End(U)) :=
  M false \o N false = N false \o M false /\ 
  M true \o N false = N false \o M true.
Notation "M '◇L' N" := (meas_lcom M N) (at level 50).
Notation "M '◇R' N" := (meas_rcom M N) (at level 50).

(* trivial measurements True *)
Definition measT {U : chsType} : bool -> 'End(U) := fun b => if b then \1 else 0.
Notation M_T := measT.
Lemma measT_qm U : trace_presv (@measT U).
Proof. by rewrite /trace_presv big_bool/= comp_lfun0r comp_lfun1r adjf1 addr0. Qed.
HB.instance Definition _ U := isQMeasure.Build _ _ _ (@measT U) (measT_qm U).
(* trivial measurements False *)
Definition measF {U : chsType} : bool -> 'End(U) := fun b => if b then 0 else \1.
Notation M_F := measF.
Lemma measF_qm U : trace_presv (@measF U).
Proof. by rewrite /trace_presv big_bool/= comp_lfun0r comp_lfun1r adjf1 add0r. Qed.
HB.instance Definition _ U := isQMeasure.Build _ _ _ (@measF U) (measF_qm U).
Lemma bcmeasT U : bcmeas (@measT U) = measF.
Proof. by apply/funext; case. Qed.
Lemma bcmeasF U : bcmeas (@measF U) = measT.
Proof. by apply/funext; case. Qed.
Lemma pmeasT U : pmeas (`1` : {hspace U})%HS = measT.
Proof. by apply/funext; case; rewrite /pmeas /M_T !hsE//= !hsE/= /cplmt subrr. Qed.
Lemma pmeasF U : pmeas (`0` : {hspace U})%HS = measF.
Proof. by rewrite -bcmeasT -pmeasT pmeasO hsO1. Qed.

Lemma lf_svds (U : chsType) (A : 'End(U)) :
  exists (F : finType) (u v : 'ONB(F;U)) (f : F -> C),
    A = \sum_i (f i) *: [> u i ; v i <].
Proof.
move: (svdsE (h2mx A))=>PA.
exists ('I_(dim U)).
pose uf i := c2h (col i (svd_u (h2mx A))).
pose vf i := c2h (col i (svd_v (h2mx A))).
have Pu : forall i j, [< uf i ; uf j >] = (i == j)%:R.
  move=>i j; rewrite dotp_mulmx !c2hK adj_col -mulmx_rowcol.
  by move: (svd_u_unitarymx (h2mx A))=>/unitarymxPV->; rewrite mxE.
have Pv : forall i j, [< vf i ; vf j >] = (i == j)%:R.
  move=>i j; rewrite dotp_mulmx !c2hK adj_col -mulmx_rowcol.
  by move: (svd_v_unitarymx (h2mx A))=>/unitarymxPV->; rewrite mxE.
have Pd : #|'I_(dim U)| = dim U by rewrite card_ord.
exists (ONB.Pack (ONB.Class (isFullDim.Axioms_ uf (isPONB.Axioms_ _ uf Pu) Pd))).
exists (ONB.Pack (ONB.Class (isFullDim.Axioms_ vf (isPONB.Axioms_ _ vf Pv) Pd))).
exists (fun i => (svds_d (h2mx A)) 0 i)=>/=.
apply/h2mx_inj.
rewrite {1}PA mulmx_colrow linear_sum; apply eq_bigr=>i _.
by rewrite col_diag_mul/= linearZ/= outp.unlock mx2hK !c2hK adj_col linearZl.
Qed.

(* Lemma A.1 *)
Lemma proportionP (U : chsType) (A B : 'End(U)) :
  (forall v, exists k, B v = k *: (A v)) -> exists c : C, B = c *: A.
Proof.
move=>P1. move: (lf_svds A)=>[F] [u] [v] [D] PA.
pose V : 'End(U) := \sum_i [> v i ; u i <].
have PV : V \is unitarylf.
  apply/unitarylfP; rewrite /V adjf_sum -(sumonb_out u) linear_suml/=.
  apply eq_bigr=>i _; rewrite adj_outp linear_sumr/= (bigD1 i)//= big1=>[j /negPf nji|];
  by rewrite outp_comp ?ns_dot ?scale1r ?addr0// onb_dot eq_sym nji scale0r.
pose c i := projT1 (cid (P1 (v i))).
have PAE i : A (v i) = D i *: (u i).
  rewrite PA sum_lfunE (bigD1 i)//= big1=>[j /negPf nji|];
  by rewrite lfunE/= outpE ?ns_dot ?scale1r ?addr0// onb_dot nji scale0r scaler0.
move: (EM (forall i, D i = 0))=>[PD|PD].
  exists 0; rewrite scale0r; apply/(intro_onb v)=>i.
  by rewrite lfunE/=; move: (P1 (v i))=>[a]->; rewrite PAE PD scale0r scaler0.
move: PD; rewrite -existsNP=>[[i0 /eqP Pi0]].
exists (c i0); apply/(intro_onb v)=>i.
move: (projT2 (cid (P1 (v i)))) (projT2 (cid (P1 (v i0)))).
rewrite -!/(c _)=>P2 P3.
case Ei: (i == i0).
  by move: Ei=>/eqP->; rewrite P3 lfunE.
move: (P1 (v i + v i0))=>[k].
rewrite lfunE !linearD/= P2 P3 !PAE=>Pk.
move: {+}Pk=>/(f_equal (fun x=>[< u i ; x >])).
rewrite !dotpDr !dotpZr ns_dot onb_dot Ei !mulr0 !addr0 mulr1 !scalerA=>->.
move: {+}Pk=>/(f_equal (fun x=>[< u i0 ; x >])).
rewrite !dotpDr !dotpZr ns_dot onb_dot eq_sym Ei !mulr0 !add0r !mulr1.
by move: (mulIf Pi0)=>P4; move=>/P4->.
Qed.

Definition LinearProp (T : numDomainType) (U : lmodType T) (P : U -> Prop) :=
  forall (c : T) (x y : U), P x -> P y -> P (c *: x + y).

Lemma denlf_eq_LinearProp (V : chsType) (P : 'End(V) -> Prop) : 
  LinearProp P -> (forall x, x \is denlf -> P x) <-> (forall x, P x).
Proof.
move=>LP; split=>//.
have PD x y : P x -> P y -> P (x + y).
  by move=>Px Py; move: (LP 1 _ _ Px Py); rewrite scale1r.
have PZ (c : C) x : P x -> P (c *: x).
  by move=>Px; move: (LP (c - 1) _ _ Px Px); rewrite scalerBl scale1r subrK.
rewrite denlf_psdlf_eq_nnegz=>[c _|Ps x]; first by apply: PZ.
move: (lf_psd_decomp x)=>[M1] [M2] [M3] [M4] [P1] [P2] [P3] [P4] ->.
rewrite -scaleNr -scaleN1r; try do ! [apply/PD | apply/PZ]; by apply/Ps.
Qed.

(* Lemma A.2 (1) *)
Lemma op_orthoP (U : chsType) (M N : 'End(U)) :
  M ⊥ N <-> (forall x : 'End(U), M \o (N \o x \o N^A) \o M^A = 0).
Proof.
rewrite /op_orthogonal; split=>[P x|/(_ \1)/eqP].
by rewrite !comp_lfunA P !comp_lfun0l.
by rewrite -!comp_lfunA -adjf_comp !comp_lfunA comp_lfun1r formV_eq0=>/eqP.
Qed.
Lemma op_ortho_denP (U : chsType) (M N : 'End(U)) :
  M ⊥ N <-> (forall x : 'FD(U), M \o (N \o x \o N^A) \o M^A = 0).
Proof.
rewrite op_orthoP -denlf_eq_LinearProp.
  by move=>a x y; rewrite !(linearPr, linearPl)/==>->->; rewrite scaler0 addr0.
split=>P x; first by apply/P/is_denlf.
by move=>Px; rewrite (DenLf_BuildE Px).
Qed.

(* Lemma A.2 (2) *)
Lemma absorblP (U : chsType) (M N : 'End(U)) :
  M ⋉ N <-> 
    (forall x : 'End(U), M \o (N \o x \o N^A) \o M^A = N \o x \o N^A).
Proof.
split=>[[/=] c Pc IH x | IH1].
by rewrite !comp_lfunA IH -!comp_lfunA -adjf_comp 
  IH adjfZ -!comp_lfunZr -comp_lfunZl scalerA -normCKC Pc expr1n scale1r.
pose c i j := [< eb j ; (M \o N) (eb i) >].
pose d i j := [< eb j ; N (eb i) >].
have Pij i j i' j' : c i j * (c i' j')^* = d i j * (d i' j')^*.
  move: (IH1 [> eb i; eb i' <])=>/(f_equal (fun y : 'End(_) => [<eb j; y (eb j')>])).
  by rewrite outp_compr -outp_comprV outp_compr -outp_comprV !outpE !dotpZr 
    -!comp_lfunE -conj_dotp -!/(c _ _) -conj_dotp -!/(d _ _) mulrC=>->; rewrite mulrC.
have P_eq0 i j : c i j = 0 <-> d i j = 0.
  split=>P; move: (Pij i j i j); rewrite P mul0r -normCK. move=>/esym.
  1,2: by move=>/eqP; rewrite sqrf_eq0 normr_eq0=>/eqP.
case E: (N == 0).
  exists 1; first by rewrite normr1.
  by move: E=>/eqP ->; rewrite comp_lfun0r scaler0.
have [i0 [j0 d_neq0]] : exists i j, d i j != 0.
  rewrite not_existsP=>P; move: E=>/eqP; apply.
  apply/(intro_onb eb)=>/=i; apply/(intro_onbl eb)=>/=j.
  move: (P i); rewrite -forallNP=>/(_ j)/negP.
  by rewrite negbK /d=>/eqP->; rewrite lfunE/= dotp0.
have c_neq0 : (c i0 j0) ^* != 0.
  by rewrite conjC_eq0; apply/eqP=>/P_eq0; apply/eqP.
exists ((d i0 j0)^* / (c i0 j0)^*).
  by rewrite normrM normrV// !norm_conjC !normC_def Pij mulfV// -normC_def normr_eq0.
apply/(intro_onb eb)=>/=i; apply/(intro_onbl eb)=>/=j.
rewrite -/(c _ _) lfunE/= dotpZr -/(d _ _) mulrC.
by apply/(mulIf c_neq0); rewrite -mulrA mulfVK.
Qed.

Lemma absorbl_denP (U : chsType) (M N : 'End(U)) :
  M ⋉ N <-> 
    (forall x : 'FD(U), M \o (N \o x \o N^A) \o M^A = N \o x \o N^A).
Proof.
rewrite absorblP -denlf_eq_LinearProp.
  by move=>a x y; rewrite !(linearPr, linearPl)/==>->->.
split=>P x; first by apply/P/is_denlf.
by move=>Px; rewrite (DenLf_BuildE Px).
Qed.

Lemma ortho_scaleP (U : chsType) (u v : U) :
  (forall w, [< w ; u >] = 0 -> [< w ; v >] = 0) ->
    exists c, v = c *: u.
Proof.
case E: (u == 0).
  move: E=>/eqP-> P; exists 0; rewrite scale0r; apply/intro_dotl=>w.
  by move: (P w); rewrite !dotp0=>->.
move=>P; apply/hlineP; rewrite memhE_line; apply/lehOP=>w.
rewrite !memhE !hsE/= /cplmt !lfunE/= !lfunE/= !hlineE !subr_eq ![w + _]addrC 
  -!subr_eq !subrr ![0 == _]eq_sym !supphP !outpE scaler_eq0 E orbF.
by rewrite -![dotp _ w]conj_dotp conjC_eq0=>/eqP/P->; rewrite conjC0 scale0r.
Qed.

(* Lemma A.2 (3) *)
Lemma meas_proportionP (U : chsType) (A0 A1 B : 'End(U)) :
  (exists c0 c1 : C, (c0^+2 + c1^+2 = 1) /\ (A0 ⋈_(c0) B) /\ (A1 ⋈_(c1) B))
    <-> (forall x : 'End(U), (A0 \o x \o A0^A) + (A1 \o x \o A1^A) = B \o x \o B^A).
Proof.
split=>[|P].
  move=>[c0] [c1] [Pc] [] [d0 Pd0 PA0] [d1 Pd1 PA1] x.
  by rewrite PA0 PA1 !adjfZ !linearZl/= !linearZr/= 
    !scalerA -!normCK Pd0 Pd1 -scalerDl Pc scale1r.
suff /proportionP [d0 P0]: (forall v, exists k, A0 v = k *: (B v)).
suff /proportionP [d1 P1]: (forall v, exists k, A1 v = k *: (B v)).
case E: (B == 0).
exists 1; exists 0; split; first by rewrite expr1n expr0n/= addr0.
split; [exists 1 | exists 0];
  by rewrite ?normr1 ?normr0// ?P0 ?P1; move: E=>/eqP->; rewrite !scaler0.
exists `|d0|; exists `|d1|; split.
move: (P \1)=>/eqP; rewrite !comp_lfun1r P0 P1 !adjfZ !(linearZl, linearZr)/= 
  !scalerA -!normCK -scalerDl -subr_eq0 -[X in _ + X]scaleN1r -scalerDl.
by rewrite scaler_eq0 subr_eq formV_eq0 E orbF add0r =>/eqP.
by split; [exists d0 | exists d1].
all: move=>v; move: (P [> v; v <]); rewrite !outp_compr -!outp_comprV=>P1;
  apply/ortho_scaleP=>w Pw;
  move: P1=>/(f_equal (fun x : 'End(U) => [< w ; x w >]))/eqP.
all: rewrite lfunE/= !outpE dotpDr !dotpZr Pw mulr0 -conj_dotp -normCKC
  -[[<A1 v; w>]]conj_dotp -normCKC paddr_eq0 ?exprn_ge0// =>/andP[].
all:  by rewrite !sqrf_eq0 !normr_eq0=>/eqP+/eqP.
Qed.

Lemma meas_aborb (U : chsType) (A0 A1 B : 'End(U)) :
  (exists c0 c1 : C, (c0^+2 + c1^+2 = 1) /\ (B ⋊_(c0) A0) /\ (B ⋊_(c1) A1))
    <-> (forall x : 'End(U), (B \o A0 \o x \o A0^A \o B^A) + 
      (B \o A1 \o x \o A1^A \o B^A) = B \o x \o B^A).
Proof.
rewrite /k_right_absorb meas_proportionP; split=>IH u; move: (IH u);
by rewrite !adjf_comp !comp_lfunA.
Qed.

(* TODO : move *)
Lemma formlf_eq0 (U V : chsType) (N : 'Hom(U, V)) :
  (forall x, formlf N x = 0) -> N = 0.
Proof.
move=>IH; apply/(intro_onb eb)=>/=i; apply/(intro_onbl eb)=>/=j.
move: (IH [> eb i; eb i <])=>/(f_equal (fun y : 'End(_) => [<eb j; y (eb j)>])).
rewrite formlfE outp_compr lfunE/= outpE dotpZr 
  -conj_dotp adj_dotEl -normCKC !lfunE/= dotp0=>/eqP.
by rewrite sqrf_eq0 normr_eq0=>/eqP.
Qed.

Lemma formlf_trlf0  (U V : chsType) (N : 'Hom(U, V)) :
  (forall x, \Tr (formlf N x) = 0) -> N = 0.
Proof.
move=>IH; apply/formlf_eq0; rewrite -denlf_eq_LinearProp.
  by move=>/= c x y; rewrite linearP/==>->->; rewrite scaler0 addr0.
move=>x Px; rewrite (DenLf_BuildE Px) formlf_soE.
by apply/eqP/trlf0_eq0; rewrite psdf_ge0/=; split=>//; rewrite -formlf_soE.
Qed.

(* TODO : merge to mcextra, also in coqq_paper/qhl.v *)
Lemma big_bool_cond [R : Type] [idx : R] [op : Monoid.com_law idx] b (F : bool -> R) :
  \big[op/idx]_i F i = op (F b) (F (~~b)).
Proof. by rewrite big_bool; case: b=>//; rewrite Monoid.mulmC. Qed.

(* Lemma A.2 (4) *)
Lemma meas_absorb_entail (U : chsType) (M : 'QM(bool;U)) N (b1 b2 : bool) :
  (M b1) ⋉ (N b2) -> M (~~ b1) ⊥ N b2.
Proof.
move=>/absorblP IH; apply/formlf_trlf0=>x; rewrite formlfE.
move: (IH x) (qm_trlf M ((N b2 \o x) \o (N b2)^A))=>/(f_equal (@lftrace _)) + /eqP.
by rewrite (big_bool_cond b1)/==>->; 
  rewrite addrC -subr_eq0 addrK adjf_comp !comp_lfunA=>/eqP.
Qed.

Lemma meas_weakerP (U : chsType) (M : 'QM) (N : bool -> 'End(U)) :
  M ∝ N -> (M true) ⋉ (N true) /\  (M false) ⊥ (N true).
Proof. by split=>//; move: H=>/meas_absorb_entail. Qed.

Lemma meas_contradictP (U : chsType) (M : 'QM) (N : bool -> 'End(U)) :
  M ≫ N -> (M true) ⋉ (N false) /\ (M false) ⊥ (N false) .
Proof. by split=>//; move: H=>/meas_absorb_entail. Qed.

(* TODO : move to hspace.v *)
Lemma leh_compr0 (H : chsType) (U V : {hspace H}) :
  (U `<=` V)%HS = (~` V \o U == 0)%HS.
Proof.
by rewrite leh_compr hsE /cplmt linearBl/= comp_lfun1l subr_eq0 eq_sym.
Qed.
Lemma leh_compl0 (H : chsType) (U V : {hspace H}) :
  (U `<=` V)%HS = (U \o ~` V == 0)%HS.
Proof.
by rewrite leh_compl hsE /cplmt linearBr/= comp_lfun1r subr_eq0 eq_sym.
Qed.

(* example 5.1 (1) *)
Lemma pmeas_entailP (U : chsType) (X Y : {hspace U}) :
  pmeas X ▶ pmeas Y <-> (X `<=` Y)%HS.
Proof. by rewrite leh_compr0; split=>[/eqP|/eqP]. Qed.

Lemma pmeas_weakerP (U : chsType) (X Y : {hspace U}) :
  pmeas X ∝ pmeas Y <-> (Y `<=` X)%HS.
Proof.
split=>[[c Pc]|].
  rewrite /pmeas leh_compr=>/(f_equal (fun x=> c^-1 *: x)).
  rewrite scalerA mulVf -1?normr_eq0 ?Pc ?oner_neq0// scale1r=>PY.
  by rewrite -PY linearZr/= comp_lfunA projf_idem.
by rewrite leh_compr=>/eqP P1; exists 1; rewrite ?normr1// scale1r /pmeas -{2}P1.
Qed.

Lemma pmeas_contradictP (U : chsType) (X Y : {hspace U}) :
  pmeas X ≫ pmeas Y <-> (~` X `<=` Y)%HS.
Proof. by rewrite pmeasO pmeas_weakerP lehOx. Qed.

Lemma pmeas_entailO (U : chsType) (X Y : {hspace U}) :
  pmeas X ▶ pmeas Y <-> pmeas (~` Y)%HS ▶ pmeas (~` X)%HS.
Proof. by rewrite !pmeas_entailP lehO. Qed.
Lemma pmeas_entailW (U : chsType) (X Y : {hspace U}) :
  pmeas X ▶ pmeas Y <-> pmeas Y ∝ pmeas X.
Proof. by rewrite pmeas_entailP pmeas_weakerP. Qed.
Lemma pmeas_entailC (U : chsType) (X Y : {hspace U}) :
  pmeas X ▶ pmeas Y <-> pmeas (~` X)%HS ≫ pmeas Y.
Proof. by rewrite pmeas_contradictP pmeas_entailP hsOK. Qed.

Lemma pmeas_weakerlO (U : chsType) (X Y : {hspace U}) :
  pmeas X ∝ pmeas Y <-> pmeas (~` Y)%HS ∝ pmeas (~` X)%HS.
Proof. by rewrite !pmeas_weakerP lehO. Qed.
Lemma pmeas_weakerE (U : chsType) (X Y : {hspace U}) :
  pmeas X ∝ pmeas Y <-> pmeas Y ▶ pmeas X.
Proof. by rewrite pmeas_entailW. Qed.
Lemma pmeas_weakerC (U : chsType) (X Y : {hspace U}) :
  pmeas X ∝ pmeas Y <-> pmeas X ≫ pmeas (~` Y)%HS.
Proof. by rewrite pmeasO hsOK. Qed.

Lemma pmeas_contradictC (U : chsType) (X Y : {hspace U}) :
  pmeas X ≫ pmeas Y <-> pmeas Y ≫ pmeas X.
Proof. by rewrite !pmeas_contradictP lehOx. Qed.
Lemma pmeas_contradictE (U : chsType) (X Y : {hspace U}) :
  pmeas X ≫ pmeas Y <-> pmeas (~` X)%HS ▶ pmeas Y.
Proof. by rewrite pmeasO pmeas_weakerE pmeas_entailO hsOK. Qed.
Lemma pmeas_contradictW (U : chsType) (X Y : {hspace U}) :
  pmeas X ≫ pmeas Y <-> pmeas X ∝ pmeas (~` Y)%HS.
Proof. by rewrite pmeas_weakerC hsOK. Qed.

(* example 5.1 (3) *)
Lemma meas_weaker_pmeet (U : chsType) (M N : 'QM(bool;U)) :
  M ∝ N <-> N ≅ N & M.
Proof. by rewrite /meas_pmeet proportion1C. Qed.

Lemma meas_weaker_entail (U : chsType) (M N : 'QM(bool;U)) :
  M ∝ N -> N ▶ M.
Proof. by move=>/meas_weakerP[]. Qed.

(* TODO : move to hspace.v *)
Lemma hcommute (U : chsType) (X Y : {hspace U}) :
  (X _C_ Y)%O <-> X \o Y = Y \o X.
Proof.
rewrite -commute_char2; split=>[|P1]; last first.
  have P3 : (X `&&` Y)%O = (Y `&&` X)%O.
    by rewrite !sprojhE P1 -comp_lfunA projf_idem -P1 -comp_lfunA projf_idem.
  by rewrite joinC -shookxJxy -P3 shookxJyx -sprojxHxy shookHxyx sprojHxyx meetC.
move: X Y.
have PXY (X Y : {hspace U}): (X _C_ Y)%O -> ((X \o Y) \o (X \o Y)) = (X \o Y) \o X.
  move=>/commuteJE/(f_equal (fun x => ~` x)%HS).
  rewrite [X in _ = X]hsOI sprojO=>/hspacelfP.
  rewrite shookhE hsOK ![in X in _ = X]hs2lfE.
  move=>/(f_equal (fun x=>X\o Y\o X \o x)).
  rewrite kerhE hsE {1}/cplmt linearBr/= hsE suppvlf comp_lfun1r subrr -cosupplf_adj.
  move=>/(f_equal (fun x=>x \o (X^⟂ + Y^⟂)^A))/eqP.
  rewrite comp_lfun0l -comp_lfunA cosupplfv adjfD /cplmt !adjfB.
  by rewrite !hermf_adjE/= -comp_lfunA comp_lfunDr linearBr/= projf_idem 
    comp_lfun1r subrr add0r !linearBr/= comp_lfun1r eq_sym subr_eq0=>/eqP<-.
move=>X Y; rewrite commute_char2=>P1.
move: (PXY _ _ P1) {+}P1 =>P2; rewrite -commutexO=>/PXY.
rewrite hsE /cplmt !linearBr/= !linearBl/= comp_lfun1r P2 opprB addrA subrK.
move=>/(f_equal (fun x => - (X \o X) + x)); rewrite !addKr comp_lfunA projf_idem=>/oppr_inj P3.
by rewrite P3; apply/adjf_inj; rewrite !adjf_comp !hermf_adjE comp_lfunA -P3.
Qed.

(* example 5.2 *)
Lemma pmeas_lcomP (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇L pmeas Y <-> (X _C_ Y)%O.
Proof.
rewrite /meas_lcom /pmeas; split=>[[] _ /hcommute//|Pc].
by split; apply/hcommute=>//; rewrite commuteOx.
Qed.

Lemma pmeas_lcom_projP (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇L pmeas Y <-> X \o Y \is projlf.
Proof.
rewrite pmeas_lcomP hcommute; split.
by move=>P; apply/projlfP; rewrite {1 3}P adjf_comp !hermf_adjE
  !comp_lfunA comp_lfunACA projf_idem -P -comp_lfunA projf_idem.
by move=>/projlfP[]; rewrite adjf_comp !hermf_adjE=>->.
Qed.

Lemma pmeas_rcomP (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇R pmeas Y <-> (X _C_ Y)%O.
Proof.
rewrite /meas_rcom /pmeas -commutexO; split=>[[] _ /hcommute//|Pc].
by split; apply/hcommute=>//; rewrite commuteOx.
Qed.

Lemma pmeas_rcom_projP (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇R pmeas Y <-> X \o Y \is projlf.
Proof. by rewrite pmeas_rcomP -pmeas_lcomP pmeas_lcom_projP. Qed.

Lemma meas_lrcomE (U : chsType) (M N : bool -> 'End(U)) :
  M ◇L N <-> M ◇R N^m⟂.
Proof. by []. Qed.

Lemma meas_rlcomE (U : chsType) (M N : bool -> 'End(U)) :
  M ◇R N <-> M ◇L N^m⟂.
Proof. by []. Qed.

Lemma pmeas_lrcom (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇L pmeas Y <-> pmeas X ◇R pmeas Y.
Proof. by rewrite pmeas_lcomP pmeas_rcomP. Qed.

Lemma pmeas_lcomOx (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇L pmeas Y <-> pmeas (~` X)%HS ◇L pmeas Y.
Proof. by rewrite !pmeas_lcomP commuteOx. Qed.

Lemma pmeas_lcomxO (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇L pmeas Y <-> pmeas X ◇L pmeas (~` Y)%HS.
Proof. by rewrite pmeas_lrcom meas_rlcomE. Qed.

Lemma pmeas_rcomOx (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇R pmeas Y <-> pmeas (~` X)%HS ◇R pmeas Y.
Proof. by rewrite !pmeas_rcomP commuteOx. Qed.

Lemma pmeas_rcomxO (U : chsType) (X Y : {hspace U}) :
  pmeas X ◇R pmeas Y <-> pmeas X ◇R pmeas (~` Y)%HS.
Proof. by rewrite -pmeas_lrcom meas_lrcomE pmeasO. Qed.

Lemma pmeas_entail_lcom (U : chsType) (X Y : {hspace U}) :
  pmeas X ▶ pmeas Y -> pmeas X ◇L pmeas Y.
Proof. by rewrite pmeas_entailP pmeas_lcomP; exact: le_commute. Qed.

Lemma pmeas_entail_rcom (U : chsType) (X Y : {hspace U}) :
  pmeas X ▶ pmeas Y -> pmeas X ◇R pmeas Y.
Proof. by rewrite pmeas_entailP pmeas_rcomP; exact: le_commute. Qed.

Lemma pmeas_weaker_lcom (U : chsType) (X Y : {hspace U}) :
  pmeas X ∝ pmeas Y -> pmeas X ◇L pmeas Y.
Proof. by rewrite pmeas_weakerP pmeas_lcomP commuteC; exact: le_commute. Qed.

Lemma pmeas_weaker_rcom (U : chsType) (X Y : {hspace U}) :
  pmeas X ∝ pmeas Y -> pmeas X ◇R pmeas Y.
Proof. by move=>/pmeas_weaker_lcom; rewrite pmeas_lrcom. Qed.

Lemma pmeas_contradict_lcom (U : chsType) (X Y : {hspace U}) :
  pmeas X ≫ pmeas Y -> pmeas X ◇L pmeas Y.
Proof. by rewrite pmeas_contradictP pmeas_lcomP -commuteOx; exact: le_commute. Qed.

Lemma pmeas_contradict_rcom (U : chsType) (X Y : {hspace U}) :
  pmeas X ≫ pmeas Y -> pmeas X ◇R pmeas Y.
Proof. by move=>/pmeas_contradict_lcom; rewrite pmeas_lrcom. Qed.

Lemma formso_eqZ (U V : chsType) (c : C) (N : 'Hom(U,V)) :
  `|c| = 1 -> formso (c *: N) = formso N.
Proof.
by move=>Pc; apply/superopP=>y; rewrite !formsoE adjfZ
  !(linearZl, linearZr)/= scalerA -normCKC Pc expr1n scale1r.
Qed.

Definition measUr (U V W : chsType) (F : finType) (f : F -> 'Hom(U,V)) (u : 'Hom(W,U)) :=
  fun i => f i \o u.
Lemma measUr_tn U V W F (f : 'TN(F;U,V)) (u : 'FB1(W,U)) : trace_nincr (measUr f u).
Proof. 
rewrite /trace_nincr /measUr.
under eq_bigr do rewrite adjf_comp comp_lfunA comp_lfunACA -formlfEV.
by rewrite -linear_sum/=; apply/formlf_bound1f_le1/is_trnincr.
Qed.
HB.instance Definition _ U V W F (f : 'TN(F;U,V)) (u : 'FB1(W,U)) :=
  isTraceNincr.Build _ _ F (measUr f u) (measUr_tn f u).
Lemma measUr_tp U V W F (f : 'QM(F;U,V)) (u : 'FI(W,U)) : trace_presv (measUr f u).
Proof. 
rewrite /trace_presv /measUr.
under eq_bigr do rewrite adjf_comp comp_lfunA comp_lfunACA -formlfEV.
by rewrite -linear_sum/= qmeasure_tpE formlf1E adjfK isofE.
Qed.
HB.instance Definition _ U V W F (f : 'QM(F;U,V)) (u : 'FI(W,U)) :=
  TraceNincr_isQMeasure.Build _ _ F (measUr f u) (measUr_tp f u).

End ExtraDef.

Notation "''[|' phi '>]'" := (bvmeas phi).
Notation "M '^m⟂'" := (bcmeas M) (at level 8).
Notation "A '⋈_(' p ) B" := (k_proportion A B p) (at level 50, p, B at next level).
Notation "A '⋈_0' B" := (k_proportion A B 1) (at level 50, B at next level).
Notation "A ⋈ B" := (k_proportion A B 1) (at level 50, B at next level).
Notation "A '⋉_(' p ) B" := (k_left_absorb A B p) (at level 50, p, B at next level).
Notation "A '⋉_0' B" := (k_left_absorb A B 0) (at level 50, B at next level).
Notation "A ⋉ B" := (k_left_absorb A B 1) (at level 50, B at next level).
Notation "A '⋊_(' p ) B" := (k_right_absorb A B p) (at level 50, p, B at next level).
Notation "A '⋊_0' B" := (k_right_absorb A B 0) (at level 50, B at next level).
Notation "A ⋊ B" := (k_right_absorb A B 1) (at level 50, B at next level).
Notation "A ⊥ B" := (op_orthogonal A B) (at level 50, B at next level).
Notation "M '▶' N" := (meas_entail M N) (at level 50).
Notation "M '∝' N" := (meas_weaker M N) (at level 50).
Notation "M '≫' N" := (M ∝ N^m⟂) (at level 50).
Notation "K ≅ M & N" := (meas_pmeet K M N) (at level 50).
Notation "M '◇L' N" := (meas_lcom M N) (at level 50).
Notation "M '◇R' N" := (meas_rcom M N) (at level 50).
Notation M_T := measT.
Notation M_F := measF.
