From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals topology normedtype.
From quantum.external Require Import complex.
Require Import mcextra mcaextra notation hermitian quantum
  orthomodular hspace inhabited autonat hspace_extra.

From quantum Require Import prodvect tensor mxpred cpo extnum
  ctopology qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.refinement Require Import language.
Require Import Coq.Program.Equality String.

(************************************************************************)
(*                   Formalization of Section 5                         *)
(************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import DefaultQMem.Exports.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.
Local Open Scope hspace_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(************************************************************************)
(*                   Definition of Refinement Relation                  *)
(* We use HB.lock to avoid unexpected simplifation during proofs, it's  *)
(* equivalent to define it without HB.lock by rewrite refined.unlcok    *)
(************************************************************************)
HB.lock
Definition refined (c c' : cmd_) :=
  forall P Q, hoare P Q c -> hoare P Q c'.

Definition eq_refine (c c' : cmd_) := refined c c' /\ refined c' c.

Notation "c1 '⊑' c2" := (refined c1 c2). 
Notation "c1 '≡' c2" := (eq_refine c1 c2) (at level 69).

Lemma refined_trans : 
  forall a b c, a ⊑ b -> b ⊑ c -> a ⊑ c.
Proof.
move=>a b c; rewrite refined.unlock.
by move=>IH1 IH2 P Q Pa; apply/IH2/IH1.
Qed.
Lemma refined_refl : forall c, c ⊑ c.
Proof. by rewrite refined.unlock. Qed.

Lemma eq_refine_trans : 
  forall a b c, a ≡ b -> b ≡ c -> a ≡ c.
Proof.
move=>a b c [] Pab Pba [] Pbc Pcb; split.
apply: (refined_trans Pab Pbc).
apply: (refined_trans Pcb Pba).
Qed.
Lemma eq_refine_refl : forall c, c ≡ c.
Proof. by move=>c; split; apply: refined_refl. Qed.
Lemma eq_refine_sym : forall a b, a ≡ b -> b ≡ a.
Proof. by move=>a b [] ? ?; split. Qed.

Add Parametric Relation : cmd_ refined
  reflexivity proved by refined_refl
  transitivity proved by refined_trans
  as refined_ref.

Add Parametric Relation : cmd_ eq_refine
  reflexivity proved by eq_refine_refl
  symmetry proved by eq_refine_sym
  transitivity proved by eq_refine_trans
  as eq_refine_ref.

Lemma wlp_weakestP c (Q P : {hspace _}) : 
  hoare P Q c <-> P `<=` wlp c Q.
Proof.
split; first by exact: wlp_weakest.
move=>IH; rewrite hoare_iff_post=>E Pe.
apply: (le_trans IH); move: E Pe; rewrite -hoare_iff_post.
apply: wlp_hoare.
Qed.

Lemma sp_strongestP c (Q P : {hspace _}) : 
  hoare P Q c <-> sp c P `<=` Q.
Proof.
split; first by exact: sp_strongest.
move=>IH; rewrite hoare_iff_pre=>E Pe.
apply: (le_trans _ IH); move: E Pe.
by rewrite -hoare_iff_pre; apply: sp_hoare.
Qed.

Lemma hoare_homo_pre c (Q P P' : {hspace _}) : 
  P `<=` P' -> hoare P' Q c  -> hoare P Q c.
Proof.
move=>IH1 /wlp_weakestP P1; apply/wlp_weakestP;
apply: (le_trans IH1 P1).
Qed.

Lemma hoare_homo_post c (P Q Q' : {hspace _}) : 
  Q' `<=` Q -> hoare P Q' c  -> hoare P Q c.
Proof.
move=>IH1 /sp_strongestP P1; apply/sp_strongestP;
apply: (le_trans P1 IH1).
Qed.

Lemma wlp_mono c : {homo (wlp c) : P Q / P `<=` Q}.
Proof. by move=>P Q H; apply/wlp_weakestP/(hoare_homo_post H)/wlp_hoare. Qed.
Lemma sp_mono c : {homo (sp c) : P Q / P `<=` Q}.
Proof. by move=>P Q H; apply/sp_strongestP/(hoare_homo_pre H)/sp_hoare. Qed.

(*****************************************************************************)
(*                                Theorem 5.1                                *)
(*****************************************************************************)
Lemma refined_wlp c c' :
  c ⊑ c' <-> (forall Q, wlp c Q `<=` wlp c' Q).
Proof.
split; rewrite refined.unlock => IH W.
  apply/wlp_weakest/IH/wlp_hoare.
by move=>Q /wlp_weakest PW; apply/wlp_weakestP/(le_trans _ (IH _)).
Qed.

Lemma refined_sp c c' :
  c ⊑ c' <-> (forall P, sp c' P `<=` sp c P).
Proof.
split; rewrite refined.unlock => IH W.
  apply/sp_strongest/IH/sp_hoare.
by move=>Q /sp_strongest PW; apply/sp_strongestP/(le_trans (IH _)).
Qed.

(*****************************************************************************)
(*                                Theorem 5.2                                *)
(*****************************************************************************)
Lemma refined_prescription_wlp P Q c :
  prescription_ P Q ⊑ c <-> P `<=` wlp c Q.
Proof.
rewrite refined_wlp; split=>[/(_ Q)|IH R].
  apply: le_trans; rewrite wlp_str_prescription.
  by case: eqP=> _; [apply/leh1 | rewrite lexx].
rewrite wlp_str_prescription.
case: eqP=>[->|_]; first by rewrite wlp_str_1 lexx.
case P1: (Q `<=` R); last by apply/le0h.
by apply/(le_trans IH)/wlp_mono/P1.
Qed.

Lemma refined_prescription_sp P Q c :
  prescription_ P Q ⊑ c <-> sp c P `<=` Q.
Proof.
rewrite refined_sp; split=>[/(_ P) P1|IH R].
  apply: (le_trans P1); rewrite sp_str_prescription.
  by case: eqP=> _; [apply/le0h | rewrite lexx lexx].
rewrite sp_str_prescription.
case: eqP=>[->|_]; first by rewrite sp_str_0 lexx.
case P1: (R `<=` P); last by apply/leh1.
by apply/(le_trans _ IH)/sp_mono/P1.
Qed.

Lemma hoare_prescription P Q :
  hoare P Q (prescription_ P Q).
Proof.
rewrite hoare_iff_pre=>E; rewrite fsemE/==>[[Pe]].
by rewrite (QOperation_BuildE Pe) CP_supph_le/=.
Qed.

Lemma hoare_prescription_postW (P Q Q' : {hspace _}) :
  Q `<=` Q' -> hoare P Q' (prescription_ P Q).
Proof. by move=>P1; apply/(hoare_homo_post P1)/hoare_prescription. Qed.

Lemma hoare_prescription_preW (P' P Q : {hspace _}) :
  P' `<=` P -> hoare P' Q (prescription_ P Q).
Proof. by move=>P1; apply/(hoare_homo_pre P1)/hoare_prescription. Qed.

(*****************************************************************************)
(*                Fig 2: Structural rules (declared as Lemmas)               *)
(*****************************************************************************)
Lemma Stru_Ref c : c ≡ c. Proof. exact: eq_refine_refl. Qed.

Lemma Stru_Tran c0 c1 c2 : (c0 ⊑ c1 /\ c1 ⊑ c2) -> c0 ⊑ c2.
Proof. move=>[]; exact: refined_trans. Qed.

Lemma Stru_Seq c0 d0 c1 d1 : 
  (c0 ⊑ d0 /\ c1 ⊑ d1) -> sequence_ c0 c1 ⊑ sequence_ d0 d1.
Proof.
rewrite !refined_wlp=>[[]] P0 P1 Q.
rewrite !wlp_str_sequence.
apply: (le_trans (wlp_mono c0 (P1 Q)) (P0 _ )).
Qed.

Lemma Stru_Cond T x P c0 c1 d0 d1 :
  (c0 ⊑ d0 /\ c1 ⊑ d1) -> @condition_ T x P c1 c0 ⊑ @condition_ T x P d1 d0.
Proof.
rewrite !refined_wlp=>[[]] P0 P1 Q.
by rewrite !wlp_str_condition; apply lehI2; apply/leHr.
Qed.

Lemma Stru_Pcho p c0 d0 c1 d1 : 
  (c0 ⊑ d0 /\ c1 ⊑ d1) -> prob_choice_ p c0 c1 ⊑ prob_choice_ p d0 d1.
Proof.
rewrite !refined_wlp=>[[]] P0 P1 Q.
by rewrite !wlp_str_prob_choice; apply lehI2.
Qed.

Lemma Stru_While T x P c d :
  (c ⊑ d) -> @while_ T x P c ⊑ while_ x P d.
Proof.
rewrite !refined_wlp=>Pcd Q.
rewrite !wlp_str_while; apply/leh_caps_r=>n.
elim: n=>[//|n] Pn/=.
apply lehI2; apply/leHr; last by apply/lexx.
apply: (le_trans (wlp_mono c Pn) (Pcd _)).
Qed.

(*****************************************************************************)
(*       Fig 3: Refinement rules for prescriptions (declared as Lemmas)      *)
(* ------------------------------------------------------------------------- *)
(*                          Fig 3.1 : Common rules                           *)
(*****************************************************************************)
Lemma Comm_Pres_All0 Q c : prescription_ `0` Q ⊑ c.
Proof. by rewrite refined_prescription_wlp le0h. Qed.

Lemma Comm_Pres_All1 P c : prescription_ P `1` ⊑ c.
Proof. by rewrite refined_prescription_wlp wlp_str_1 leh1. Qed.

Lemma Comm_Pres_Abort P Q : prescription_ P Q ⊑ abort_.
Proof. by rewrite refined_prescription_wlp wlp_str_abort lex1. Qed.

Lemma Comm_Pres_Skip P : prescription_ P P ⊑ skip_.
Proof. by rewrite refined_prescription_wlp wlp_str_skip lexx. Qed.

Lemma Comm_Pres_Cons P Q R S :
  (P `<=` R) /\ (S `<=` Q) -> prescription_ P Q ⊑ prescription_ R S.
Proof.
move=>[] P1 P2.
rewrite refined_prescription_wlp wlp_str_prescription P2.
case: eqP=>[|//]; by rewrite leh1.
Qed.

Lemma Comm_Pres_Seq P Q R :
  prescription_ P Q ⊑ sequence_ (prescription_ P R) (prescription_ R Q).
Proof.
rewrite refined_prescription_wlp wlp_str_sequence !wlp_str_prescription lexx.
case: eqP=> _; first by rewrite leh1.
by case: eqP; rewrite ?leh1 !lexx.
Qed.

(*****************************************************************************)
(*           Fig 3.2 : Rules based on weakest liberal preconditions          *)
(*****************************************************************************)
Lemma Wpc_Pres_Init T (x : 'QReg[T]) Q :
    prescription_ (kerh_init_dual x Q) Q ⊑ initial_ x.
Proof. by rewrite refined_prescription_wlp wlp_str_initial lexx. Qed.

Lemma Wpc_Pres_Unit T (x : 'QReg[T]) (U : 'FU) Q :
  prescription_ (formh (liftf_lf (tf2f x x U^A)) Q) Q ⊑ unitary_ x U.
Proof. by rewrite refined_prescription_wlp wlp_str_unitary lexx. Qed.

Lemma Wpc_Pres_Ass T (x : 'QReg[T]) (P : {hspace _}) (Q : {hspace _}) :
  prescription_ (liftfh x P `=>` Q) Q ⊑ assert_ x P.
Proof. by rewrite refined_prescription_wlp wlp_str_assert lexx. Qed.

Lemma Wpc_Pres_Pcho p (P1 P2 Q : {hspace _}) :
  prescription_ (P1 `&` P2) Q ≡ 
    prob_choice_ p (prescription_ P1 Q) (prescription_ P2 Q).
Proof.
split; last rewrite refined_wlp=>W.
  rewrite refined_prescription_wlp wlp_str_prob_choice lehI2=>[||//];
  by rewrite wlp_str_prescription lexx; case: eqP; rewrite ?leh1 ?lexx.
rewrite wlp_str_prob_choice !wlp_str_prescription.
case: eqP=>_; first by rewrite meetx1 lexx.
by case E: (_ `<=` W); rewrite ?meetx0 lexx.
Qed.

Lemma Wpc_Pres_Cond T (x : 'QReg[T]) P (P1 P0 Q : {hspace _}) :
  prescription_ (((liftfh x P) `=>` P1) `&` ((liftfh x (~` P)) `=>` P0)) Q 
    ≡ condition_ x P (prescription_ P1 Q) (prescription_ P0 Q).
Proof.
split.
  by rewrite refined_prescription_wlp wlp_str_condition lehI2=>[||//];
  rewrite leHr// wlp_str_prescription lexx; case: eqP; rewrite ?leh1 ?lexx.
rewrite !refined_wlp=>W.
rewrite wlp_str_condition !wlp_str_prescription.
case: eqP=> _; first by rewrite leh1.
case: (_ `<=` W); first by rewrite lexx.
by rewrite !shookx0 liftfhO meetxO lexx.
Qed.

Lemma Wpc_Pres_While T (x : 'QReg[T]) P (Q R : {hspace _}) :
  prescription_ (((liftfh x P) `=>` Q) `&` ((liftfh x (~` P)) `=>` R)) R
    ⊑ while_ x P (prescription_ Q (((liftfh x P) `=>` Q) `&`
                                   ((liftfh x (~` P)) `=>` R))).
Proof.
rewrite refined_prescription_wlp wlp_str_while.
apply/caps_lub=>n _.
elim: n=>[|n IH /=]; first by rewrite /= leh1.
rewrite lehI2=>[||//]; last by rewrite lexx.
rewrite leHr=>[|//]; rewrite wlp_str_prescription.
by case: eqP=> _; by rewrite ?leh1 ?IH ?lexx.
Qed.

(*****************************************************************************)
(*             Fig 3.2 : Rules based on strongest postconditions             *)
(*****************************************************************************)
Lemma Spc_Pres_Init T (x : 'QReg[T]) P :
  prescription_ P (supph_init x P) ⊑ initial_ x.
Proof. by rewrite refined_prescription_sp sp_str_initial. Qed.

Lemma Spc_Pres_Unit T (x : 'QReg[T]) (U : 'FU) P :
  prescription_ P (formh (liftf_lf (tf2f x x U)) P) ⊑ unitary_ x U.
Proof. by rewrite refined_prescription_sp sp_str_unitary. Qed.

Lemma Spc_Pres_Ass T (x : 'QReg[T]) (P : {hspace _}) (Q : {hspace _}) :
  prescription_ P (liftfh x Q `&&` P) ⊑ assert_ x Q.
Proof. by rewrite refined_prescription_sp sp_str_assert lexx. Qed.

Lemma Spc_Pres_Pcho p (P Q1 Q2 : {hspace _}) :
  prescription_ P (Q1 `|` Q2) ≡ 
    prob_choice_ p (prescription_ P Q1) (prescription_ P Q2).
Proof.
split; last rewrite refined_sp=>W.
  rewrite refined_prescription_sp sp_str_prob_choice lehU2=>[||//];
  by rewrite sp_str_prescription lexx; case: eqP; rewrite ?le0h ?lexx.
rewrite sp_str_prob_choice !sp_str_prescription.
case: eqP=>_; first by rewrite le0h.
by case E: (_ `<=` P); rewrite ?joinx1 lexx.
Qed.

Lemma Spc_Pres_Cond T (x : 'QReg[T]) R (P Q : {hspace _}) :
  prescription_ P Q 
    ⊑ condition_ x R (prescription_ (liftfh x R `&&` P) Q) 
                     (prescription_ (liftfh x (~` R) `&&` P) Q).
Proof.
rewrite refined_prescription_sp sp_str_condition -{3}[Q]joinxx lehU2=>[||//];
  by apply/sp_strongest/hoare_prescription.
Qed.

Lemma Spc_Pres_While T (x : 'QReg[T]) (P : {hspace _}) Inv :
  prescription_ Inv (liftfh x (~` P) `&&` Inv)
    ⊑ while_ x P (prescription_ (liftfh x P `&&` Inv) Inv).
Proof.
rewrite refined_prescription_sp sp_str_while.
apply/cups_glb=>n _; apply: leJr.
elim: n=>[|n IH]; first by rewrite /= le0h.
rewrite /= leUh lexx/=.
apply/sp_strongest/(hoare_homo_pre (leJr _ IH))/hoare_prescription.
Qed.

(*****************************************************************************)
(*                               Wpc Proof system                            *)
(*****************************************************************************)
Inductive Wpc_Proof : cmd_ -> cmd_ -> Type :=
  | Stru_Ref_Wpc (c : cmd_) : Wpc_Proof c c
  | Stru_Tran_Wpc c0 c1 c2 of (Wpc_Proof c0 c1) & (Wpc_Proof c1 c2) : Wpc_Proof c0 c2
  | Stru_Seq_Wpc c0 t0 c1 t1 of (Wpc_Proof c0 t0) & (Wpc_Proof c1 t1) 
      : Wpc_Proof (sequence_ c0 c1) (sequence_ t0 t1)
  | Stru_Cond_Wpc T x P c0 t0 c1 t1 of (Wpc_Proof c0 t0) & (Wpc_Proof c1 t1)
      : Wpc_Proof (@condition_ T x P c1 c0) (@condition_ T x P t1 t0)
  | Stru_Pcho_Wpc p c0 t0 c1 t1 of (Wpc_Proof c0 t0) & (Wpc_Proof c1 t1)
      : Wpc_Proof (@prob_choice_ p c0 c1) (@prob_choice_ p t0 t1)
  | Stru_While_Wpc T x P c t of (Wpc_Proof c t)
      : Wpc_Proof (@while_ T x P c) (@while_ T x P t)
  | Comm_Pres_All0_Wpc Q c
      : Wpc_Proof (prescription_ `0` Q) c
  | Comm_Pres_All1_Wpc P c
      : Wpc_Proof (prescription_ P `1`) c
  | Comm_Pres_Abort_Wpc P Q
      : Wpc_Proof (prescription_ P Q) abort_
  | Comm_Pres_Skip_Wpc P
      : Wpc_Proof (prescription_ P P) skip_
  | Comm_Pres_Cons_Wpc (P Q R T : {hspace _}) of (P `<=` R) & (T `<=` Q)
      : Wpc_Proof (prescription_ P Q) (prescription_ R T)
  | Comm_Pres_Seq_Wpc P Q R
      : Wpc_Proof (prescription_ P Q)
                  (sequence_ (prescription_ P R) (prescription_ R Q))
  | Wpc_Pres_Init_Wpc T x Q
      : Wpc_Proof (prescription_ (@kerh_init_dual T x Q) Q) (initial_ x)
  | Wpc_Pres_Unit_Wpc T (x : 'QReg[T]) (U : 'FU) Q
      : Wpc_Proof (prescription_ (formh (liftf_lf (tf2f x x U^A)) Q) Q)
                  (unitary_ x U)
  | Wpc_Pres_Ass_Wpc T x P (Q : {hspace _})
      : Wpc_Proof (prescription_ (liftfh x P `=>` Q) Q) (@assert_ T x P)
  | Wpc_Pres_Pcho_Wpc p (P1 P2 Q : {hspace _})
      : Wpc_Proof (prescription_ (P1 `&` P2) Q)
                  (prob_choice_ p (prescription_ P1 Q) (prescription_ P2 Q))
  | Wpc_Pres_Cond_Wpc T (x : 'QReg[T]) P (P1 P0 Q : {hspace _})
      : Wpc_Proof (prescription_ (((liftfh x P) `=>` P1) `&`
                                  ((liftfh x (~` P)) `=>` P0)) Q)
          (condition_ x P (prescription_ P1 Q) (prescription_ P0 Q))
  | Wpc_Pres_While_Wpc T (x : 'QReg[T]) P (Q R : {hspace _})
      : Wpc_Proof (prescription_ (((liftfh x P) `=>` Q) `&`
                                  ((liftfh x (~` P)) `=>` R)) R)
          (while_ x P (prescription_ Q (((liftfh x P) `=>` Q) `&`
                                        ((liftfh x (~` P)) `=>` R)))).

(*****************************************************************************)
(*                Theorem 5.4:  Soundness of Wpc proof system                *)
(*****************************************************************************)
Lemma Wpc_Proof_sound c1 c2 : 
  Wpc_Proof c1 c2 -> c1 ⊑ c2.
Proof.
elim; try clear c1 c2.
by move=>c; move: (Stru_Ref c)=>[].
by move=>c0 c1 c2 _ IH1 _ IH2; apply: (Stru_Tran (conj IH1 IH2)).
by move=>c0 t0 c1 t1 _ IH0 _ IH1; apply: (Stru_Seq (conj IH0 IH1)).
by move=>T x P c0 t0 c1 t1 _ IH0 _ IH1; apply: (Stru_Cond x P (conj IH0 IH1)).
by move=>p c0 t0 c1 t1 _ IH0 _ IH1; apply: (Stru_Pcho p (conj IH0 IH1)).
by move=>T x P c t _ IH; apply: (Stru_While x P IH).
by intros; apply: Comm_Pres_All0.
by intros; apply: Comm_Pres_All1.
by intros; apply: Comm_Pres_Abort.
by intros; apply: Comm_Pres_Skip.
by move=>P Q R T IH1 IH2; apply: (Comm_Pres_Cons (conj IH1 IH2)).
by intros; apply: Comm_Pres_Seq.
by intros; apply: Wpc_Pres_Init.
by intros; apply: Wpc_Pres_Unit.
by intros; apply: Wpc_Pres_Ass.
by intros; move: (Wpc_Pres_Pcho p P1 P2 Q)=>[].
by intros; move: (Wpc_Pres_Cond x P P1 P0 Q)=>[].
by intros; apply: Wpc_Pres_While.
Qed.

Lemma wlp_caps (I : eqType) (P : set I) (F : I -> {hspace _}) c :
  wlp c (\caps_(i in P) F i) = \caps_(i in P) wlp c (F i).
Proof.
rewrite /wlp caps_exchange; apply eq_capsr=>E Pe.
by rewrite capsO (QOperation_BuildE (fsem_qo Pe)) kerh_cups.
Qed.

Lemma sp_cups (I : eqType) (P : set I) (F : I -> {hspace _}) c :
  sp c (\cups_(i in P) F i) = \cups_(i in P) sp c (F i).
Proof.
rewrite /sp cups_exchange; apply eq_cupsr=>E Pe.
by rewrite (QOperation_BuildE (fsem_qo Pe)) supph_cups.
Qed.

Lemma wlp_while_fixpoint T x P c Q :
  let A := wlp (@while_ T x P c) Q in
    (liftfh x P `=>` wlp c A) `&` (liftfh x (~` P) `=>` Q) = A.
Proof.
move=>A; rewrite /A wlp_str_while wlp_caps shook_caps -capsIl.
by exists 0%N.
have {2}->: (@setT nat = [set 0%N] `|` [set i.+1 | i in setT])%classic.
  by rewrite seteqP; split=>// i _ /=; case: i=>[|i]; [left|right; exists i].
rewrite caps_setU caps_set1/= cap1h caps_image//.
Qed.

(*****************************************************************************)
(*               Theorem 5.5:  Completeness of Wpc proof system              *)
(*****************************************************************************)
Lemma Wpc_Proof_complete P Q c :
  hoare P Q c -> Wpc_Proof (prescription_ P Q) c.
Proof.
move=>/wlp_weakest IH.
suff Hw: Wpc_Proof (prescription_ (wlp c Q) Q) c.
apply: (Stru_Tran_Wpc (Comm_Pres_Cons_Wpc IH (lexx Q)) Hw).
clear P IH.
elim: c Q.
- move=>Q; rewrite wlp_str_skip; apply: Comm_Pres_Skip_Wpc.
- move=>Q; rewrite wlp_str_abort; apply: Comm_Pres_Abort_Wpc.
- move=>T x Q; rewrite wlp_str_initial; apply: Wpc_Pres_Init_Wpc.
- move=>T x U Q; rewrite wlp_str_unitary; apply: Wpc_Pres_Unit_Wpc.
- move=>T x U Q; rewrite wlp_str_assert; apply: Wpc_Pres_Ass_Wpc.
- move=>P Q R; rewrite wlp_str_prescription.
  case: eqP=>[->|_]; first by apply: Comm_Pres_All1_Wpc.
  case E: (Q `<=` R); first by apply: (Comm_Pres_Cons_Wpc (lexx P) E).
  apply: Comm_Pres_All0_Wpc.
- move=>p c0 IH0 c1 IH1 Q; rewrite wlp_str_prob_choice.
  apply: (Stru_Tran_Wpc (Wpc_Pres_Pcho_Wpc p _ _ Q) 
            (Stru_Pcho_Wpc p (IH0 _) (IH1 _))).
- move=>c1 IH1 c2 IH2 Q; rewrite wlp_str_sequence.
  apply: (Stru_Tran_Wpc (Comm_Pres_Seq_Wpc _ _ _) 
            (Stru_Seq_Wpc (IH1 _) (IH2 _))).
- move=>T x P c1 IH1 c0 IH0 Q; rewrite wlp_str_condition.
  apply: (Stru_Tran_Wpc (Wpc_Pres_Cond_Wpc x P _ _ Q)
            (Stru_Cond_Wpc x P (IH0 Q) (IH1 Q))).
- move=>T x P c IH R.
  move: (Wpc_Pres_While_Wpc x P (wlp c (wlp (while_ x P c) R)) R).
  rewrite wlp_while_fixpoint=>Pw.
  apply: (Stru_Tran_Wpc Pw (Stru_While_Wpc x P (IH _))).
Qed.

(*****************************************************************************)
(*                               Spc Proof system                            *)
(*****************************************************************************)
Inductive Spc_Proof : cmd_ -> cmd_ -> Type :=
  | Stru_Ref_Spc (c : cmd_) : Spc_Proof c c
  | Stru_Tran_Spc c0 c1 c2 of (Spc_Proof c0 c1) & (Spc_Proof c1 c2) : Spc_Proof c0 c2
  | Stru_Seq_Spc c0 t0 c1 t1 of (Spc_Proof c0 t0) & (Spc_Proof c1 t1) 
      : Spc_Proof (sequence_ c0 c1) (sequence_ t0 t1)
  | Stru_Cond_Spc T x P c0 t0 c1 t1 of (Spc_Proof c0 t0) & (Spc_Proof c1 t1)
      : Spc_Proof (@condition_ T x P c1 c0) (@condition_ T x P t1 t0)
  | Stru_Pcho_Spc p c0 t0 c1 t1 of (Spc_Proof c0 t0) & (Spc_Proof c1 t1)
      : Spc_Proof (@prob_choice_ p c0 c1) (@prob_choice_ p t0 t1)
  | Stru_While_Spc T x P c t of (Spc_Proof c t)
      : Spc_Proof (@while_ T x P c) (@while_ T x P t)
  | Comm_Pres_All0_Spc Q c
      : Spc_Proof (prescription_ `0` Q) c
  | Comm_Pres_All1_Spc P c
      : Spc_Proof (prescription_ P `1`) c
  | Comm_Pres_Abort_Spc P Q
      : Spc_Proof (prescription_ P Q) abort_
  | Comm_Pres_Skip_Spc P
      : Spc_Proof (prescription_ P P) skip_
  | Comm_Pres_Cons_Spc (P Q R T : {hspace _}) of (P `<=` R) & (T `<=` Q)
      : Spc_Proof (prescription_ P Q) (prescription_ R T)
  | Comm_Pres_Seq_Spc P Q R
      : Spc_Proof (prescription_ P Q)
                  (sequence_ (prescription_ P R) (prescription_ R Q))
  | Spc_Pres_Init_Spc T x P
      : Spc_Proof (prescription_ P (@supph_init T x P)) (initial_ x)
  | Spc_Pres_Unit_Spc T (x : 'QReg[T]) (U : 'FU) P
      : Spc_Proof (prescription_ P (formh (liftf_lf (tf2f x x U)) P))
                  (unitary_ x U)
  | Spc_Pres_Ass_Spc T x Q (P : {hspace _})
      : Spc_Proof (prescription_ P (liftfh x Q `&&` P)) (@assert_ T x Q)
  | Spc_Pres_Pcho_Spc p (P Q1 Q2 : {hspace _})
      : Spc_Proof (prescription_ P (Q1 `|` Q2))
                  (prob_choice_ p (prescription_ P Q1) (prescription_ P Q2))
  | Spc_Pres_Cond_Spc T (x : 'QReg[T]) R (P Q : {hspace _})
      : Spc_Proof (prescription_ P Q)
          (condition_ x R (prescription_ (liftfh x R `&&` P) Q)
                          (prescription_ (liftfh x (~` R) `&&` P) Q))
  | Spc_Pres_While_Spc T (x :'QReg[T]) (P : {hspace _}) Inv
      : Spc_Proof (prescription_ Inv (liftfh x (~` P) `&&` Inv))
          (while_ x P (prescription_ (liftfh x P `&&` Inv) Inv)).

(*****************************************************************************)
(*                Theorem 5.4:  Soundness of Spc proof system                *)
(*****************************************************************************)
Lemma Spc_Proof_sound c1 c2 : 
  Spc_Proof c1 c2 -> c1 ⊑ c2.
Proof.
elim; try clear c1 c2.
by move=>c; move: (Stru_Ref c)=>[].
by move=>c0 c1 c2 _ IH1 _ IH2; apply: (Stru_Tran (conj IH1 IH2)).
by move=>c0 t0 c1 t1 _ IH0 _ IH1; apply: (Stru_Seq (conj IH0 IH1)).
by move=>T x P c0 t0 c1 t1 _ IH0 _ IH1; apply: (Stru_Cond x P (conj IH0 IH1)).
by move=>p c0 t0 c1 t1 _ IH0 _ IH1; apply: (Stru_Pcho p (conj IH0 IH1)).
by move=>T x P c t _ IH; apply: (Stru_While x P IH).
by intros; apply: Comm_Pres_All0.
by intros; apply: Comm_Pres_All1.
by intros; apply: Comm_Pres_Abort.
by intros; apply: Comm_Pres_Skip.
by move=>P Q R T IH1 IH2; apply: (Comm_Pres_Cons (conj IH1 IH2)).
by intros; apply: Comm_Pres_Seq.
by intros; apply: Spc_Pres_Init.
by intros; apply: Spc_Pres_Unit.
by intros; apply: Spc_Pres_Ass.
by intros; move: (Spc_Pres_Pcho p P Q1 Q2)=>[].
by intros; apply: Spc_Pres_Cond.
by intros; apply: Spc_Pres_While.
Qed.

Lemma sp_while_fixpoint T x P c R :
  let A := \cups_(n : nat) (@sp_while_iter T x P c R n) in
    R `|` sp c (liftfh x P `&&` A) = A.
rewrite /= sproj_cups sp_cups -cupsUr.
by exists 0%N.
have {2}->: (@setT nat = [set 0%N] `|` [set i.+1 | i in setT])%classic.
  by rewrite seteqP; split=>// i _ /=; case: i=>[|i]; [left|right; exists i].
by rewrite cups_setU cups_set1 /= cup0h cups_image.
Qed.

(*****************************************************************************)
(*               Theorem 5.5:  Completeness of Spc proof system              *)
(*****************************************************************************)
Lemma Spc_Proof_complete P Q c :
  hoare P Q c -> Spc_Proof (prescription_ P Q) c.
Proof.
move=>/sp_strongest IH.
suff Hs: Spc_Proof (prescription_ P (sp c P)) c.
apply: (Stru_Tran_Spc (Comm_Pres_Cons_Spc (lexx P) IH) Hs).
clear Q IH.
elim: c P.
- move=>P; rewrite sp_str_skip; apply: Comm_Pres_Skip_Spc.
- move=>P; rewrite sp_str_abort; apply: Comm_Pres_Abort_Spc.
- move=>T x P; rewrite sp_str_initial; apply: Spc_Pres_Init_Spc.
- move=>T x U P; rewrite sp_str_unitary; apply: Spc_Pres_Unit_Spc.
- move=>T x U P; rewrite sp_str_assert; apply: Spc_Pres_Ass_Spc.
- move=>Q P R; rewrite sp_str_prescription.
  case: eqP=>[->|_]; first by apply: Comm_Pres_All0_Spc.
  case E: (R `<=` Q); first by apply: (Comm_Pres_Cons_Spc E (lexx P)).
  apply: Comm_Pres_All1_Spc.
- move=>p c0 IH0 c1 IH1 P; rewrite sp_str_prob_choice.
  apply: (Stru_Tran_Spc (Spc_Pres_Pcho_Spc p P _ _) 
            (Stru_Pcho_Spc p (IH0 _) (IH1 _))).
- move=>c1 IH1 c2 IH2 P; rewrite sp_str_sequence.
  apply: (Stru_Tran_Spc (Comm_Pres_Seq_Spc _ _ _) 
            (Stru_Seq_Spc (IH1 _) (IH2 _))).
- move=>T x Q c1 IH1 c0 IH0 P; rewrite sp_str_condition.
  apply: (Stru_Tran_Spc (Spc_Pres_Cond_Spc x Q P _) _).
  apply: Stru_Cond_Spc.
  apply: (Stru_Tran_Spc (Comm_Pres_Cons_Spc (lexx _) (lehUr _ _)) (IH0 _)).
  apply: (Stru_Tran_Spc (Comm_Pres_Cons_Spc (lexx _) (lehUl _ _)) (IH1 _)).
- move=>T x Q c IH R.
  set Inv : {hspace _} := \cups_(n : nat) (sp_while_iter x Q c R n).
  rewrite sp_str_while -sproj_cups -/Inv.
  apply: (Stru_Tran_Spc (Comm_Pres_Cons_Spc (R := Inv) _ (lexx _))).
  by rewrite /Inv -sp_while_fixpoint lehUl.
  apply: (Stru_Tran_Spc (Spc_Pres_While_Spc x Q Inv) _).
  apply: Stru_While_Spc.
  apply: (Stru_Tran_Spc (Comm_Pres_Cons_Spc (lexx _) _) (IH _)).
  by rewrite /Inv -{2}sp_while_fixpoint lehUr.
Qed.
