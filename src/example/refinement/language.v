From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals topology normedtype.
From quantum.external Require Import complex.
(* From mathcomp.real_closed Require Import complex. *)
Require Import mcextra mcaextra notation hermitian quantum
  orthomodular hspace inhabited autonat hspace_extra.

(* memory model *)
(* From mathcomp.real_closed Require Import complex. *)
From quantum Require Import prodvect tensor mxpred cpo extnum
  ctopology qreg qmem.
From quantum.dirac Require Import hstensor.
Require Import Coq.Program.Equality String.
(* Require Import Relation_Definitions Setoid. *)

(*****************************************************************************)
(*                      Formalization of Section 3 & 4                       *)
(*****************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import DefaultQMem.Exports.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Section Syntax.
Local Open Scope set_scope.

(*****************************************************************************)
(*                        Syntax of Definition 3.1                           *)
(*****************************************************************************)
Inductive cmd_ : Type :=
  | skip_
  | abort_
  | initial_           T of 'QReg[T]
  | unitary_           T (x : 'QReg[T]) (U : 'FU('Ht T))
  | assert_            T (x : 'QReg[T]) (P : {hspace 'Ht T})
  | prescription_      (P Q : {hspace 'H[msys]_finset.setT})
  | prob_choice_       of {p : C | 0 < p < 1} & cmd_ & cmd_
  | sequence_          of cmd_ & cmd_
  | condition_         T (x : 'QReg[T]) (P : {hspace 'Ht T}) of cmd_ & cmd_
  | while_             T (x : 'QReg[T]) (P : {hspace 'Ht T}) of cmd_.

Fixpoint while_iter_ T (x : 'QReg[T]) (P : {hspace 'Ht T}) (c: cmd_) n : cmd_:=
  match n with
  | O => abort_
  | S n => condition_ x P (sequence_ c (while_iter_ x P c n)) skip_
  end.

Fixpoint fvars (c : cmd_) : {set mlab} :=
  match c with
  | abort_                  => finset.set0
  | skip_                   => finset.set0
  | initial_ T x            => mset x
  | unitary_ T x U          => mset x
  | assert_ T x P           => mset x
  | prescription_  P Q      => finset.setT
  | prob_choice_ p c1 c2    => fvars c1 :|: fvars c2
  | sequence_ c1 c2         => fvars c1 :|: fvars c2
  | condition_ T x P c1 c2  => mset x :|: (fvars c1 :|: fvars c2)
  | while_ T x P c          => mset x :|: fvars c
  end.

Fixpoint executable (c : cmd_) : bool :=
  match c with
  | abort_                  => true
  | skip_                   => true
  | initial_ T x            => true
  | unitary_ T x U          => true
  | assert_ T x P           => true
  | prescription_  P Q      => false
  | prob_choice_ p c1 c2    => executable c1 && executable c2
  | sequence_ c1 c2         => executable c1 && executable c2
  | condition_ T x P c1 c2  => executable c1 && executable c2
  | while_ T x P c          => executable c
  end.

End Syntax.

Notation witness := (@point _).

Section Init.
Local Open Scope hspace_scope.

Variable (U : chsType).
Definition measure_proj (P : {hspace U}) : bool -> 'End(U) :=
  fun b : bool => if b then P else (~` P)%HS.
Lemma measure_proj_tp P : 
  trace_presv (@measure_proj P).
Proof.
by rewrite /trace_presv bool_index unlock/= /reducebig/=
  /measure_proj !hermf_adjE !projf_idem addr0 addrC hs2lfE subrK.
Qed.
HB.instance Definition _ (P : {hspace U}) := 
  isQMeasure.Build _ _ bool (@measure_proj P) (@measure_proj_tp P).
(* elemso (measure_proj P true) : P rho P *)
(* elemso (measure_proj P false) : ~` P rho ~` P *)

Lemma elemso_projTE (P : {hspace U}) : 
  elemso (measure_proj P) true = formso P.
Proof. by rewrite /elemso /measure_proj. Qed.
Lemma elemso_projFE (P : {hspace U}) : 
  elemso (measure_proj P) false = formso (~` P)%HS.
Proof. by rewrite /elemso /measure_proj. Qed.

Definition initialso_mix (V : chsType) : 'SO(U,V) :=
  krausso (fun j => (sqrtC (dim V)%:R)^-1 *: [> eb j.2 ; eb j.1 <]).

Lemma initialso_mixE (V : chsType) (x : 'End(U)) :
  @initialso_mix V x = (\Tr x * (dim V)%:R^-1) *: \1.
Proof.
rewrite kraussoE pair_bigV/= exchange_big/= [\1](onb_lfun eb) linear_sum/=.
apply eq_bigr=>i _; rewrite (onb_trlf eb) mulr_suml scaler_suml.
apply eq_bigr=>j _; rewrite lfunE/= !linearZl/= adjfZ !linearZr/= 
  scalerA adj_outp outp_compl outp_comp adj_dotEl scalerA mulrC.
f_equal; f_equal; rewrite geC0_conj.
  by rewrite invr_ge0 sqrtC_ge0 ler0n.
by rewrite -expr2 exprVn sqrtCK.
Qed.

Lemma initialso_mix_dualE :
  (@initialso_mix U)^*o = @initialso_mix U.
Proof.
apply/superopP=>x; rewrite dualsoE kraussoE.
rewrite !pair_bigV/= exchange_big/=; apply eq_bigr=>i _; apply eq_bigr=>j _.
by rewrite !adjfZ !adj_outp !linearZl/= !linearZr/= !scalerA mulrC.
Qed.

Lemma initialso_mix_cptp (V : chsType) :
  @initialso_mix V \is cptp.
Proof.
apply/cptpP; split; first by apply/is_cpmap.
by apply/tpmapP=>x; rewrite initialso_mixE linearZ/= -hs2lf1E 
  -dimh_trlf dimh1 mulfVK// pnatr_eq0 lt0n_neq0// dim_proper.
Qed.
HB.instance Definition _ (V : chsType) := 
  isQChannel.Build U V (@initialso_mix V) (@initialso_mix_cptp V).

Lemma initialso_mix_supp (V : chsType) (f : 'F+(U)) :
  f%:VF != 0 -> supph (@initialso_mix V f) = `1`.
Proof.
move=>Pf; have P: \Tr f != 0.
  by move: Pf; apply/contraNN=>/eqP Pf; apply/trlf0_eq0; rewrite psdf_ge0.
by rewrite initialso_mixE supphZ ?supph1// mulf_neq0//
  invr_neq0// pnatr_eq0 -lt0n dim_proper.
Qed.

Lemma initialso_mix_dual_supp (f : 'F+(U)) :
  f%:VF != 0 -> supph ((@initialso_mix U)^*o f) = `1`.
Proof. rewrite initialso_mix_dualE; exact: initialso_mix_supp. Qed.

End Init.

Section Semantics.
Local Open Scope classical_set_scope.
Import HermitianTopology.

(*****************************************************************************)
(*                       Semantics of Definition 3.1                         *)
(* We here use the default memory model msys to formalize the semantics      *)
(*****************************************************************************)
Fixpoint fsem_aux (c : cmd_) : set 'SO[msys]_finset.setT  := 
  match c with
  | abort_                  => [ set 0 ]
  | skip_                   => [ set \:1 ]
  | initial_ T x            => [ set liftfso (initialso (tv2v x ''witness)) ]
  | unitary_ T x U          => [ set liftfso (unitaryso (tf2f x x U)) ]
  | assert_ T x P           => [ set liftfso (formso (tf2f x x P)) ]
  | prescription_  P Q 
           => [ set f | f \is cptn /\ forall rho : 'FD[msys]_[set: mlab], 
                            (supph rho `<=` P -> supph (f rho) `<=` Q)%HS]
  | prob_choice_ p c1 c2    => [ set (val p) *: l1 + (1 - val p) *: l2 
                                | l1 in fsem_aux c1 & l2 in fsem_aux c2 ]
              (* equivalent to : 
                  { (val p) *: l1 + (1 - val p) *: l2 | l1 in [| c1 |] & l2 in [| c2 |] } *)
  | sequence_ c1 c2
           => [ set l2 :o l1 | l1 in fsem_aux c1 & l2 in fsem_aux c2]
              (* equivalent to : 
                  { l2 :o l1 | l1 in [| c1 |] & l2 in [| c2 |] } *)
  | condition_ T x P c1 c2  => [ set (l1 :o liftfso (formso (tf2f x x P))) + 
                                (l2 :o liftfso (formso (tf2f x x (~` P)%HS)))
                                | l1 in fsem_aux c1 & l2 in fsem_aux c2]
              (* equivalent to : 
                { l1 :o P + l2 :o (~` P) | l1 in [| c1 |] & l2 in [| c2 |] ] *)
  | while_ T x P c          => [ set f | exists l : nat -> 'SO, 
        limn (fun n => \sum_(i < n) (liftfso (formso (tf2f x x (~` P)%HS)) :o 
              \compr_(j < i) ((l j) :o liftfso (formso (tf2f x x P))))) = f /\ 
                                  forall n : nat, (fsem_aux c) (l n)  ]
              (* equivalent to : 
                { \sum_i l i | exists l : nat -> 'SO,
                         l n \in (~` P) :so ( [| c |] :so P ) ^ n  } *)
  end.

Definition fsem_r := nosimpl fsem_aux.
Fact fsem_key : unit. Proof. by []. Qed.
Definition fsem := locked_with fsem_key fsem_r.
Canonical fsem_unlockable := [unlockable of fsem].

Lemma fsem_abortE : fsem abort_ = [set 0].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_skipE : fsem skip_ = [set \:1].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_initialE T x : fsem (@initial_ T x) = 
                          [ set liftfso (initialso (tv2v x ''witness)) ].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_unitaryE T x U : fsem (@unitary_ T x U) = 
                          [ set liftfso (unitaryso (tf2f x x U)) ].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_assertE T x P : fsem (@assert_ T x P) = 
                          [ set liftfso (formso (tf2f x x P)) ].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_prescriptionE P Q : fsem (@prescription_ P Q) = 
            [ set f | f \is cptn /\ forall rho : 'FD[msys]_[set: mlab], 
             (supph rho `<=` P -> supph (f rho) `<=` Q)%HS].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_prob_choiceE p c1 c2 : fsem (@prob_choice_ p c1 c2) = 
          [ set (val p) *: l1 + (1 - val p) *: l2 
                                | l1 in fsem c1 & l2 in fsem c2 ].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_conditionE T x P c1 c2 : fsem (@condition_ T x P c1 c2) = 
                    [ set (l1 :o liftfso (formso (tf2f x x P))) + 
                                (l2 :o liftfso (formso (tf2f x x (~` P)%HS)))
                                | l1 in fsem c1 & l2 in fsem c2].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_whileE T x P c : fsem (@while_ T x P c) = 
    [ set f | exists l : nat -> 'SO, 
        limn (fun n => \sum_(i < n) (liftfso (formso (tf2f x x (~` P)%HS)) :o 
              \compr_(j < i) ((l j) :o liftfso (formso (tf2f x x P))))) = f /\ 
                                  forall n : nat, (fsem c) (l n)  ].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_sequenceE c1 c2 :
  fsem (sequence_ c1 c2) = [ set l2 :o l1 | l1 in fsem c1 & l2 in fsem c2].
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_prob_choiceE1 p c1 c2 :
  fsem (@prob_choice_ p c1 c2) = 
    [ set val p *: i.1 + (1 - val p) *: i.2
      | i in (fsem c1 `*` fsem c2)]%classic.
Proof.
rewrite fsem_prob_choiceE image2E; f_equal.
by apply/funext=>[[a b]]/=.
Qed.

Lemma fsem_sequenceE1 c1 c2 :
  fsem (@sequence_ c1 c2)
    = [ set i.2 :o i.1 | i in (fsem c1 `*` fsem c2)]%classic.
Proof.
rewrite fsem_sequenceE image2E; f_equal.
by apply/funext=>[[a b]]/=.
Qed.

Lemma fsem_conditionE1 T x P c1 c2 :
  fsem (@condition_ T x P c1 c2) = 
  [ set (i.1 :o liftfso (elemso (measure_proj (th2h x P)) true)) + 
      (i.2 :o liftfso (elemso (measure_proj (th2h x P)) false)) |
    i in (fsem c1 `*` fsem c2)]%classic.
Proof.
rewrite fsem_conditionE image2E; f_equal.
by apply /funext =>[[a b]] /=;
rewrite elemso_projFE elemso_projTE -th2hO !th2hE.
Qed.

Lemma fsem_whileE1 T x P c :
  fsem (@while_ T x P c) = ((fun l : nat -> 'SO
    => limn (fun n => \sum_(i < n) (formso (liftf_lf (tf2f x x (~` P)%HS)) :o 
      \compr_(j < i) ((l j) :o (formso (liftf_lf (tf2f x x P))))))) @` 
      [ set l : nat -> 'SO | forall n : nat, (fsem c) (l n)])%classic.
Proof.
rewrite fsem_whileE.
apply/eq_set=>E; apply/propeqP; split.
move=>[l] [] <- Pl; exists l=>//.
apply eq_lim=>i; apply eq_bigr=>j _; rewrite liftfso_formso.
by under eq_bigr do rewrite -liftfso_formso.
move=>[l] /= Pl <-; exists l; split=>[|//].
apply eq_lim=>i; apply eq_bigr=>j _; rewrite liftfso_formso.
by under eq_bigr do rewrite liftfso_formso.
Qed.

Definition fsemE := (fsem_abortE, fsem_skipE, fsem_initialE, 
  fsem_unitaryE, fsem_assertE, fsem_prescriptionE, 
  fsem_prob_choiceE, fsem_conditionE, fsem_sequenceE, fsem_whileE).

(*****************************************************************************)
(*                                 Lemma 3.2                                 *)
(* ------------------------------------------------------------------------- *)
(* In our paper, 'super-operator' defaultly refers to completely-positive    *)
(* trace-nonincreasing (cptn) super operators (see just before Section 2.2)  *)
(* In CoqQ, 'SO is super-operators without further restriction, so Lemma 3.2 *)
(* is stated as follows by asserting that f is a cptn super-operator         *)
(*****************************************************************************)
Lemma fsem_qo (c : cmd_) (f : 'SO) : fsem c f -> f \is cptn.
Proof.
elim: c f=>[f|f|T x f|T x U f|T x P f|P Q f||||].
1-4: by rewrite fsemE/==>->; apply/is_cptn.
- by rewrite fsemE/==>->; rewrite -th2hE -elemso_projTE is_cptn.
- by rewrite fsemE/==>[[]].
- move=>[] s Ps c1 + c2 + f; rewrite fsemE/==>++ [x1 P1] [x2 P2] <-.
  move=>/(_ _ P1) IH1 /(_ _ P2) IH2; apply/cptnP; split.
  rewrite -geso0_cpE addv_ge0// pscalev_rge0 ?subr_gt0 ?geso0_cpE.
  1,3: by move: Ps=>/andP[]. 1,2: by apply/cptn_cpmap.
  apply/tnmapP=>x; rewrite !soE linearD/= !linearZ/= -[\Tr x]mul1r 
    -{2}[1](subrK s) addrC [_ * \Tr x]mulrDl lerD// ler_pM2l ?subr_gt0.
  1,3: by move: Ps=>/andP[]. 1,2: by apply/tnmapP/cptn_tnmap.
- move=>c1 IH1 c2 IH2 f; rewrite fsemE/==>[[x1/IH1 P1][x2/IH2 P2]<-].
  by rewrite (QOperation_BuildE P2) (QOperation_BuildE P1) is_cptn.
- move=>T x P c1 + c2 + f; 
  rewrite fsem_conditionE1/==>IH1 IH2 [[x1 x2] /=[] /IH1 P1 /IH2 P2 <-].
  rewrite (QOperation_BuildE P2) (QOperation_BuildE P1).
  apply/cptnP; split; first by apply/is_cpmap.
  apply/tnmapP=>r; rewrite !soE linearD/= 
    -[\Tr r](qc_trlfE (liftfso (krausso (measure_proj (th2h x P))))) /=
    -elemso_sum linear_sum/= big_bool/= soE linearD/= lerD//.
  rewrite (QOperation_BuildE P1); apply/qo_trlfE/is_psdlf.
  rewrite (QOperation_BuildE P2); apply/qo_trlfE/is_psdlf.
- move=>T x P c IH f; rewrite fsem_whileE1/==>[[l Pl <-]].
  apply: whilegso_cptn; last by move=>i; apply/IH.
  by rewrite !hermf_adjE/= !projf_idem/= -linearD/=
    -linearD/= hs2lfOE subrK tf2f1 liftf_lf1.
Qed.

Lemma fsem_nonempty c : (fsem c !=set0)%classic.
Proof.
elim: c=>[ | | T x | T x U | T x P | P Q | | | | ].
by rewrite fsemE; exists \:1.
by rewrite fsemE; exists 0.
by rewrite fsemE; exists (liftfso (initialso (tv2v x ''witness))).
by rewrite fsemE; exists (liftfso (unitaryso (tf2f x x U))).
by rewrite fsemE; exists (liftfso (formso (tf2f x x P))).
by rewrite fsemE; exists 0=>/=; split;
  [apply/is_cptn | move=>r _; rewrite soE supph0 le0h].
by move=>p c1 [x1 P1] c2 [x2 P2]; rewrite fsem_prob_choiceE1/=;
  exists (val p *: x1 + (1 - val p) *: x2)=>/=; exists (x1,x2).
- move=>c1 [x1 P1] c2 [x2 P2]; rewrite fsem_sequenceE1/=;
  by exists (x2 :o x1)=>/=; exists (x1,x2).
- move=>T x P c1 [x1 P1] c2 [x2 P2]; rewrite fsem_conditionE1.
  by exists (x1 :o liftfso (elemso (measure_proj (th2h x P)) true) + 
    (x2 :o liftfso (elemso (measure_proj (th2h x P)) false))) => /=;
    exists (x1, x2).
- move=>T x P c [x1 P1]. rewrite fsemE.
  exists (limn (fun n : nat =>
    \sum_(i < n) (liftfso (formso (tf2f x x (~` P)%HS)) 
    :o \compr_(j < i) (x1 :o liftfso (formso (tf2f x x P))))))%classic =>/=.
  by exists (fun=> x1).
Qed.

(* local denotational semantics *)

(* Lemma fsem_local c f : fsem c f -> exists E : 'QO_(fvars c), f = liftfso E.
Proof.
suff P: fsem c f -> exists E : 'SO_(fvars c), f = liftfso E.
  move=>P1; move: (P P1) (fsem_qo P1)=>[x ->]; rewrite liftso_qoE=>P2.
  by exists (QOperation_Build P2).
move: finset.subsetUl finset.subsetUr=>/(_ mlab) Ul /(_ mlab) Ur.
elim: c f=>[f|f|T x f|T x U f|T x P f|T x P Q f||||].
by rewrite fsemE /setso1/==>->; exists \:1; rewrite liftfso1.
by rewrite fsemE /setso0/==>->; exists (0 : 'SO); rewrite linear0.
by rewrite fsemE/==>->; exists (initialso (tv2v x ''witness)).
by rewrite fsemE/==>->; exists (unitaryso (tf2f x x U)).
by rewrite fsemE/==>->; exists (formso (tf2f x x P)).
by rewrite fsemE/==>[[l []]] <- _; exists l.
- move=>[] p Pp c1 + c2 + ?; rewrite fsemE/==>++[[?[x1 P1 <-]][?[x2 P2 <-]]<-].
  move=>/(_ _ P1)[x11 ->]/(_ _ P2)[x22 ->].
  exists ((liftso (Ul _ (fvars c2)) (p *: x11)) + 
    (liftso (Ur (fvars c1) _) ((1-p) *: x22))).
  by rewrite linearD/= !linearZ/= !liftfso2.
- move=>c1 IH1 c2 IH2 ?; rewrite fsemE/==>[[?/IH2[x2->]][?/IH1[x1->]]<-].
  exists ((liftso (Ur (fvars c1) _) x2) :o (liftso (Ul _ (fvars c2)) x1)).
  by rewrite liftfso_comp !liftfso2.
- move=>T x P c1 + c2 + ?; rewrite fsemE/==>++[[?[x1 P1 [?/=->] <-]][?[x2 P2 [?/=->] <-]]<-];
  move=>/(_ _ P1)[x11 ->]/(_ _ P2)[x22 ->].
  exists (liftso (Ur (mset x) _) (liftso (Ul _ (fvars c2)) x11) :o 
    liftso (Ul _ (fvars c1 :|: fvars c2)) (formso (tf2f x x P)) + 
    (liftso (Ur (mset x) _) (liftso (Ur (fvars c1) _) x22) :o 
    liftso (Ul _ (fvars c1 :|: fvars c2)) (formso (tf2f x x (~` P)%HS)))).
  by rewrite linearD/= !liftfso_comp !liftfso2.
- move=>T x P c + ?; rewrite fsemE [fsem]unlock/==>[IH [f [] ] <- Pf].
  pose g i := liftso (Ur (mset x) _) (projT1 (cid (IH _ (Pf i)))).
  have Pg i : f i = liftfso (g i).
    by move: (projT2 (cid (IH _ (Pf i))))=>->; rewrite /g liftfso2.
  exists (limn (fun n => \sum_(i < n) (formso (lift_lf (Ul _ (fvars c)) (tf2f x x (~` P)%HS)) :o 
    (\compr_(j < i) (g j :o formso (lift_lf (Ul _ (fvars c)) (tf2f x x P))))))).
  rewrite -[RHS]extnum.linear_lim.
  apply: whilegso_is_cvgn.
  by rewrite !hermf_adjE/= !projf_idem/= -linearD/= -lift_lf_le1 -linearD/= hs2lfOE subrK tf2f1.
  by move=>i; rewrite -liftfso_qoE -Pg; apply: (@fsem_qo c); rewrite [fsem]unlock.
  apply: eq_lim=>i/=; rewrite linear_sum; apply eq_bigr=>j _ /=.
  rewrite !liftfso_comp -liftso_formso liftfso2; f_equal.
  elim/big_rec2: _ =>[|k y1 ? _ ->]; first by rewrite liftfso1.
  by rewrite !liftfso_comp -liftso_formso liftfso2 comp_soErl -Pg.
Qed. *)

End Semantics.

(* TODO : move to quantum.v *)
(* CP -> QO -> QC -> QU -> Unitary : once this is done, rearrange the *)
(* canonical of fun_of_superop and make all consistent ??? *)


Section HoareTriple.
Local Open Scope order_scope.
Local Open Scope hspace_scope.
Import ComplLatticeSyntax.

(* Lemma cups_fsem (U : chsType) c (F : 'SO -> {hspace U}) :
  \cups_(i in fsem c) F i 
    = \cups_(i in [set x : 'CP | fsem c (x : 'SO)]) F i.
Admitted.
Lemma caps_fsem (U : chsType) c (F : 'SO -> {hspace U}) :
  \caps_(i in fsem c) F i 
    = \caps_(i in [set x : 'CP | fsem c (x : 'SO)]) F i.
Admitted. *)


(* predicates are Hilbert subspace over full space : {hspace 'H[msys]_setT } *)
(* there are two boolean variables, pt : false - partial , true - toal *)
(* st : false - may not saturated , true saturated (the weakest (literal) precondition)*)
(* pt and st are introduced to avoid messy amount of rules *)
Definition hoare (P: {hspace 'H[msys]_finset.setT})
                 (Q: {hspace 'H[msys]_finset.setT}) (c: cmd_) :=
  forall E, fsem c E -> forall r : 'FD, supph r `<=` P -> supph (E r) `<=` Q.

(* TODO : replace CP_supph_le *)
Lemma CP_supph_le (U : chsType) (E : 'CP(U)) (P Q : {hspace U}) :
  (forall r : 'FD, supph r `<=` P -> supph (E r) `<=` Q) <->
    (supph (E P) `<=` Q).
Proof.
split=>[ Ph | /supph_le_trlf0P P1 x Px].
  apply /supph_trlf0_le =>/=.
  rewrite heigenE sumoutpE linear_sum/=
    linear_suml/= linear_sum/= big1// =>i _.
  rewrite scale1r; move: (heigen_mem i).
  by rewrite memhE_line hlineE=>/Ph/=/supph_le_trlf0P.
apply/supph_trlf0_le=>/=; apply/le_anti/andP; split; 
  last by apply/psdlf_TrM; apply/is_psdlf.
rewrite -P1; apply/lef_psdtr/is_psdlf/cp_preserve_order.
by apply: (le_trans (obslf_le_supph _)); rewrite -leh_lef.
Qed.

Lemma CP_kerh_ge (U : chsType) (E : 'CP(U)) (P Q : {hspace U}) :
  (forall r : 'FD, supph r `<=` P -> supph (E r) `<=` Q) <->
    (P `<=` kerh (E^*o (~` Q))).
Proof.
by rewrite CP_supph_le; split; rewrite -supp_le_trlfE/= dualso_trlfE 
  lftraceC -[P]ocomplK supp_le_trlfE/= kerhE lehO.
Qed.

(*****************************************************************************)
(*                                 Lemma 3.5                                 *)
(*****************************************************************************)
Lemma hoare_iff_pre P Q c :
  hoare P Q c <-> (forall E, fsem c E -> supph (E P) `<=` Q).
Proof.
split=>+ E Pe; move=>/(_ E Pe); 
by rewrite (QOperation_BuildE (fsem_qo Pe)) ?CP_supph_le.
Qed.

Lemma hoare_iff_post P Q c :
  hoare P Q c <-> (forall E, fsem c E -> P `<=` kerh (E^*o (~` Q))).
Proof.
split=>+ E Pe; move=>/(_ E Pe);
by rewrite (QOperation_BuildE (fsem_qo Pe)) ?CP_kerh_ge.
Qed.

Definition wlp c (Q : {hspace _}) :=
  \caps_(E in fsem c) kerh (E^*o (~` Q)%HS).

Definition sp c (P : {hspace _}) :=
  \cups_(E in fsem c) supph (E P).

Lemma wlp_ubounded c Q E :
  fsem c E -> wlp c Q `<=` kerh (E^*o (~` Q)%HS).
Proof. by move=>Pe; rewrite /wlp; apply: (caps_inf (i := E)). Qed.

(*************************     Definition 4.1 (1)    *************************)
Lemma wlp_hoare c Q : hoare (wlp c Q) Q c.
Proof. rewrite hoare_iff_post; exact: wlp_ubounded. Qed.

Lemma wlp_greatest c (Q Q' : {hspace _}) :
  (forall E, fsem c E -> Q' `<=` kerh (E^*o (~` Q)%HS)) -> Q' `<=` wlp c Q.
Proof. by move=>PQ; apply: caps_lub. Qed.

(*************************     Definition 4.1 (2)    *************************)
Lemma wlp_weakest c (Q P : {hspace _}) :
  hoare P Q c -> P `<=` wlp c Q.
Proof. by rewrite hoare_iff_post; exact: wlp_greatest. Qed.

Lemma sp_lbounded c (P : {hspace _}) E :
  fsem c E -> supph (E P) `<=` sp c P.
Proof. by move=>Pe; rewrite /sp; apply: (cups_sup (i := E)). Qed.

(*************************     Definition 4.3 (1)    *************************)
Lemma sp_hoare c P : hoare P (sp c P) c.
Proof. rewrite hoare_iff_pre; exact: sp_lbounded. Qed.

Lemma sp_least c (P P' : {hspace _}) :
  (forall E, fsem c E -> supph (E P) `<=` P') -> sp c P `<=` P'.
Proof. by move=>PQ; apply: cups_glb. Qed.

(*************************     Definition 4.3 (2)    *************************)
Lemma sp_strongest c (P Q : {hspace _}) :
  hoare P Q c -> sp c P `<=` Q.
Proof. by rewrite hoare_iff_pre; exact: sp_least. Qed.

(* formalize E : E(<0|P|0>) = kerh (Init^*o (~` P)) where Init is the initialso *)
Definition kerh_init_dual T (x : 'QReg[T]) (P : {hspace 'H[msys]_finset.setT}) :=
  kerh ((liftfso (initialso (tv2v x ''witness)))^*o (~` P)).

(* formalize |0>_x_<0| ⊗ supph (tr_x P) = supph (Init P) where Init is the initialso *)
Definition supph_init T (x : 'QReg[T]) (P : {hspace 'H[msys]_finset.setT}) :=
  supph (liftfso (initialso (tv2v x ''witness)) P).

(*****************************************************************************)
(*              Lemma 4.2 : structure representation of wlp                  *)
(*****************************************************************************)
Lemma wlp_str_1 c : wlp c `1` = `1`.
Proof.
apply/eqP; rewrite -le1h; apply/wlp_greatest=>E Pe.
by rewrite hsO1 hs2lfE linear0/= kerh0.
Qed.

Lemma wlp_str_abort R : wlp abort_ R = `1`.
Proof. by rewrite /wlp fsemE caps_set1 dualso0 soE kerh0. Qed.

Lemma wlp_str_skip R : wlp skip_ R = R.
Proof. by rewrite /wlp fsemE caps_set1 dualso1 soE kerhO ocomplK. Qed.

Lemma wlp_str_initial T x R : wlp (@initial_ T x) R = kerh_init_dual x R.
Proof. by rewrite /wlp fsemE caps_set1. Qed.

Lemma wlp_str_unitary T x U R : 
  wlp (@unitary_ T x U) R = formh (liftf_lf (tf2f x x U^A)) R.
Proof.
by rewrite /wlp fsemE caps_set1 liftfso_formso dualso_formso
   -liftf_lf_adj tf2f_adj -formlf_soE kerhE/= -formhE supph_id formhO ocomplK.
Qed.

Lemma wlp_str_assert T x P R :
  wlp (@assert_ T x P) R = (liftfh x P `=>` R).
Proof.
by rewrite /wlp fsemE caps_set1 liftfso_formso 
  dualso_formE hermf_adjE/= -th2hE -liftfhE shookhE.
Qed.

(* Lemma left_nonempty_dim_ge (U : chsType) (E : 'SO(U)) (A : 'End(U)) (x : U) :
  (E A) x = 0 -> \Tr (E A \o [> x ; x <]) = 0.
Proof. by rewrite outp_compr=>->; rewrite out0p linear0. Qed. *)

Lemma wlp_str_prescription P Q R :
  wlp (@prescription_ P Q) R = if R == `1` then `1` else 
                                   (if (Q `<=` R) then P 
                                   else `0`).
Proof.
case: eqP=>[->|/eqP rneq1]; first by rewrite wlp_str_1.
case P1: (Q `<=` R).
- apply/le_anti/andP; split; last first.
    apply/wlp_greatest=>E; rewrite fsemE/==>[[Pe]].
    rewrite (QOperation_BuildE Pe) CP_kerh_ge=>P2.
    apply/(le_trans P2)/kerh_lef=>/=.
    rewrite (QOperation_BuildE Pe) cp_preserve_order=>[|//].
    by rewrite -leh_lef lehO P1.
  apply: (le_trans (wlp_ubounded _ (E := 
    (@initialso_mix _ _ :o elemso (measure_proj P) false)) _)).
    rewrite fsemE/=; split; first by apply/is_cptn.
    by rewrite CP_supph_le/= soE elemso_projFE 
      formsoE/= hsOx_comp comp_lfun0l linear0 supph0 le0h.
  rewrite dualso_comp soE -kerh_cp_supp/= initialso_mix_dual_supp.
  case: eqP=>//; rewrite -hs2lf0E; move=>/lfunP/hspaceP=>P2.
    by move: rneq1; rewrite -hsO_eq P2 ocompl1 eqxx.
  by rewrite elemso_projFE dualso_formE hermf_adjE hsE
    comp_lfun1r projf_idem kerhE supph_id ocomplK lexx.
- apply/le_anti/andP; split; last by apply/le0h.
move: P1; rewrite -{1}[R]hsOK -eq_sproj0=>/eqP/eqP/hs_neq0_exists=>[[v Pv]].
apply: (le_trans (wlp_ubounded _ (E := initialso v) _)).
  rewrite fsemE/=; split. apply/is_cptn.
  rewrite CP_supph_le/= initialsoE; apply: (le_trans (supphZ_le _ _)).
  rewrite -hlineE -memhE_line; move: Pv; apply/lehP/leJl.
rewrite dualso_initialE kerhZ ?kerh1// -memh_dotOE.
apply/negP=>Pv1. move: (conj Pv Pv1)=>/memhIP.
by rewrite meetJxOyy memh0 ns_eq0F.
Qed.

Import HermitianTopology.

Lemma scaleso_cp (U : chsType) (c : C) (E : 'CP(U)) :
  (0 <= c) -> (c *: (E : 'SO)) \is cpmap.
Proof.
move=>Pc; apply/cpmapP; rewrite linearZ/=.
apply: psdmxZ=>//.
by move: (@is_cpmap _ _ E)=>/cpmapP.
Qed.
Definition scaleso_cpType (U : chsType) (c : C) (E : 'CP(U)) H :=
  CPMap_Build (@scaleso_cp U c E H).
Local Canonical scaleso_cpType.
(* ?? #[local] fails *)
(* HB.instance Definition _ (U : chsType) (c : C) (E : 'CP(U)) H :=
  isCPMap.Build _ _ (c *: (E : 'SO)) (@leh_kerhP U c E H). *)

Lemma wlp_str_prob_choice p c1 c2 R : 
  wlp (@prob_choice_ p c1 c2) R = wlp c1 R `&` wlp c2 R.
Proof.
rewrite /wlp fsem_prob_choiceE1 caps_image. 
rewrite (caps_setM (fun i j => kerh ((_ *: i + _ *: j) ^*o (~` R)))).
rewrite -(capsIl _ _ (fsem_nonempty c1)); apply eq_capsr=>x1 P1.
rewrite -(capsIr _ _ (fsem_nonempty c2)); apply eq_capsr=>x2 P2.
move: (projT2 p) (projT2 p)=>/andP[]/ltW/=?/ltW;
rewrite -subr_ge0=>?/andP[]??;
rewrite linearD/= linearZ/= linearZ/= soE (QOperation_BuildE (fsem_qo P1))
  (QOperation_BuildE (fsem_qo P2)) kerhD/=.
by rewrite soE kerhZ 1?soE 1?kerhZ ?lt0r_neq0 1?subr_gt0.
Qed.

Lemma wlp_str_sequence c1 c2 R :
  wlp (@sequence_ c1 c2) R = wlp c1 (wlp c2 R).
Proof.
rewrite /wlp fsem_sequenceE1 caps_image. 
rewrite (caps_setM (fun i j => kerh ((j :o i) ^*o (~` R)))).
apply eq_capsr=>x1 P1.
rewrite capsO (QOperation_BuildE (fsem_qo P1)) kerh_cups.
by apply eq_capsr=>x2 P2;
rewrite -supphE (QOperation_BuildE (fsem_qo P2)) kerh_cp_supp/=
  dualso_comp soE.
Qed.

Lemma wlp_str_condition T x P c1 c2 R : 
  wlp (@condition_ T x P c1 c2) R = 
    (liftfh x P `=>` wlp c1 R) `&` (liftfh x (~` P) `=>` wlp c2 R).
Proof.
rewrite /wlp fsem_conditionE1 caps_image !shook_caps. 
rewrite (caps_setM (fun i j => kerh ((i :o _ + (j :o _)) ^*o (~` R)))).
rewrite -(capsIl _ _ (fsem_nonempty c1)); apply eq_capsr=>x1 P1.
rewrite -(capsIr _ _ (fsem_nonempty c2)); apply eq_capsr=>x2 P2.
rewrite linearD/= soE (QOperation_BuildE (fsem_qo P1))
  (QOperation_BuildE (fsem_qo P2)) kerhD/=.
f_equal.
  rewrite elemso_projTE liftfso_formso dualso_comp soE 
    (QOperation_BuildE (fsem_qo P1)) -kerh_cp_supp/=.
  by rewrite  dualso_formE hermf_adjE/= -liftfhE shookhE supphE.
rewrite elemso_projFE liftfso_formso dualso_comp soE 
  (QOperation_BuildE (fsem_qo P2)) -kerh_cp_supp/=.
by rewrite -th2hO dualso_formE hermf_adjE/= -liftfhE shookhE supphE.
Qed.

(* Lemma kerh_limn_sum (U : chsType) (f : nat -> 'End(U)) :
  cvgn (fun i => \sum_(j < i) (f j)) -> (forall i, f i \is psdlf) ->
    kerh (limn (fun i => \sum_(j < i) (f j))) = \caps_(i : nat) kerh (f i).
Admitted. *)

Fixpoint wlp_while_iter (T : qType) (x : 'QReg[T]) (P : {hspace 'Ht T}) 
  (c : cmd_) (R : {hspace _}) n : {hspace _} :=
  match n with
  | 0 => `1`
  | S n => (liftfh x P `=>` wlp c (wlp_while_iter x P c R n)) `&` 
          (liftfh x (~` P) `=>` R)
  end.

Lemma bump0 i : bump 0%N i = i.+1.
Proof. by rewrite /bump leq0n add1n. Qed.

Lemma set_natfun_splitl (T : Type) (P : T -> Prop) :
  [set l : nat -> T | forall n : nat, P (l n)]%classic = 
  (( fun i => (fun n => match n with O => i.1 | S n => i.2 n end ) ) @`
  ([set t : T | P t ] `*` [set l : nat -> T | forall n : nat, P (l n)]))%classic.
Proof.
rewrite eqEsubset; split.
move=>l /= Pl; exists (l 0%N, (fun i => l i.+1))=>//=.
by apply/funext=>i; case: i.
by move=>? /= [[x l /= [] Px Pl] <-] n; case: n.
Qed.

Lemma wlp_str_while T x P c R :
  wlp (@while_ T x P c) R = \caps_(n : nat) (wlp_while_iter x P c R n).
Proof.
rewrite /wlp fsem_whileE1 caps_image.
transitivity (\caps_(l in [set l | (forall n : nat, fsem c (l n))])
\caps_i kerh (\sum_(i0 < i) (formso (liftf_lf (tf2f x x (~` P))) :o 
  \compr_(j < i0) (l j :o formso (liftf_lf (tf2f x x P)))) ^*o (~` R))).
- apply eq_capsr => l /= Pl.
  have Pc: cvgn (fun n => \sum_(i < n) (formso (liftf_lf (tf2f x x (~` P))) :o 
    \compr_(j < i) (l j :o formso (liftf_lf (tf2f x x P))))).
    apply: whilegso_is_cvgn=>[|i]; last by apply/(fsem_qo (Pl i)).
    by rewrite !hermf_adjE/= !projf_idem/= -linearD/= -linearD/=
      hsE subrK tf2f1 liftf_lf1.
  rewrite -linear_limP.
    apply: linearP. apply: Pc.
  rewrite -so_liml.
    apply: linear_is_cvgP.
    apply: linearP. apply: Pc.
  under eq_lim do rewrite /= linear_sum/= sum_soE.
  rewrite kerh_limn//.
    - under eq_fun do rewrite -sum_soE -linear_sum/=.
      apply: so_is_cvgl. apply: linear_is_cvgP.
      apply: linearP. apply: Pc.
    - apply/chain_homo=>i; rewrite big_ord_recr/= levDl -psdlfE.
      under eq_bigr do rewrite (QOperation_BuildE (fsem_qo (Pl _))).
      by rewrite (CPMap_BuildE (comprso_cp _ _ _)) is_psdlf.
    - move=>n; apply/psdlf_sum=>/=i _.
      under eq_bigr do rewrite (QOperation_BuildE (fsem_qo (Pl _))).
      by rewrite (CPMap_BuildE (comprso_cp _ _ _)) is_psdlf.
rewrite caps_exchange; apply eq_capsr => n _.
elim: n R.
- move=>R /=; under eq_capsr do rewrite big_ord0 kerh0.
  rewrite caps_const//. move: (fsem_nonempty c)=>[y Py].
  by exists (fun i => y)=>/=.
move=>n IH R; rewrite set_natfun_splitl caps_image.
rewrite (caps_setM (fun x0 l => kerh (\sum_(i0 < n.+1) (_ :o \compr_(j < i0)
  (match nat_of_ord j with | 0%N => x0 | n0.+1 => l n0 end :o _)) ^*o (~` R) ))).
rewrite /= /wlp shook_caps -(capsIl _ _ (fsem_nonempty c)).
apply eq_capsr=>E Pe.
rewrite -IH capsO (QOperation_BuildE (fsem_qo Pe))
  kerh_cups shook_caps -capsIl.
  by move: (fsem_nonempty c)=>[y Py]; exists (fun=>y).
apply eq_capsr=>l /= Pl.
rewrite big_ord_recl big_ord0 comp_so1r/=.
under eq_bigr do
  rewrite bump0 big_ord_recl/= comp_soErl comp_soA dualso_comp soE.
rewrite -supphE -linear_sum/=.
set f := \sum_(i < n) _; have Pf: f \is psdlf.
  apply/psdlf_sum=>/=i _.
  under eq_bigr do rewrite (QOperation_BuildE (fsem_qo (Pl _))).
  by rewrite (CPMap_BuildE (comprso_cp _ _ _)) is_psdlf.
rewrite (QOperation_BuildE (fsem_qo Pe)) (PsdLf_BuildE Pf).
set E1 := _ (_ Pe); set f1 := _ Pf; move: E1 f1 => E1 f1.
rewrite kerhD/= caphC; f_equal.
by rewrite dualso_comp soE kerh_cp_supp/= -kerh_cp_supp/= 
  dualso_formE hermf_adjE/= -th2hE -liftfhE shookhE supphE.
by rewrite -kerh_cp_supp/= dualso_formE hermf_adjE/= 
  -th2hE -liftfhE shookhE supph_id.
Qed.

(*****************************************************************************)
(*              Lemma 4.4 : structure representation of sp                   *)
(*****************************************************************************)
Lemma sp_str_0 c : sp c `0` = `0`.
Proof.
apply/eqP; rewrite -leh0; apply/sp_least=>E Pe.
by rewrite hsE linear0 supph0.
Qed.

Lemma sp_str_abort R : sp abort_ R = `0`.
Proof. by rewrite /sp fsemE cups_set1 soE supph0. Qed.

Lemma sp_str_skip R : sp skip_ R = R.
Proof. by rewrite /sp fsemE cups_set1 soE supph_id. Qed.

Lemma sp_str_initial T x R : sp (@initial_ T x) R = supph_init x R.
Proof. by rewrite /sp fsemE cups_set1. Qed.

Lemma sp_str_unitary T x U R : 
  sp (@unitary_ T x U) R = formh (liftf_lf (tf2f x x U)) R.
Proof.
by rewrite /sp fsemE cups_set1 liftfso_formso -formlf_soE -formhE supph_id.
Qed.

Lemma sp_str_assert T x P R :
  sp (@assert_ T x P) R = (liftfh x P `&&` R).
Proof.
by rewrite /sp fsemE cups_set1 liftfso_formso -th2hE -liftfhE
  formsoE hermf_adjE/= sprojhE.
Qed.

(* Lemma left_nonempty_dim_ge (U : chsType) (E : 'SO(U)) (A : 'End(U)) (x : U) :
  (E A) x = 0 -> \Tr (E A \o [> x ; x <]) = 0.
Proof. by rewrite outp_compr=>->; rewrite out0p linear0. Qed. *)

Lemma sp_str_prescription P Q R :
  sp (@prescription_ P Q) R = if R == `0` then `0` else 
                                   (if (R `<=` P) then Q
                                   else `1`).
Proof.
case: eqP=>[->|/eqP rneq0]; first by rewrite sp_str_0.
case P1: (R `<=` P).
- apply/le_anti/andP; split.
    apply/sp_least=>E; rewrite fsemE/==>[[Pe]].
    rewrite (QOperation_BuildE Pe) CP_supph_le=>P2.
    apply/(le_trans _ P2)/supph_lef=>/=.
    rewrite (QOperation_BuildE Pe) cp_preserve_order=>[|//].
    by rewrite -leh_lef P1.
  rewrite {1}[Q]heigenUE; apply/cuphs_le=>/=i _.
  apply: (le_trans _ (sp_lbounded _ (E := initialso (heigen i)) _)).
    by rewrite initialsoE supphZ -?hlineE ?lexx//;
    rewrite -dimh_trlf pnatr_eq0 dimh_eq0.
  rewrite fsemE/=; split. apply/is_cptn.
  rewrite CP_supph_le initialsoE; apply/(le_trans (supphZ_le _ _)).
  by rewrite -hlineE -memhE_line heigen_mem.
- apply/le_anti/andP; split; first by apply/leh1.
  move: P1; rewrite -lehO -eq_sproj0=>/eqP/eqP/hs_neq0_exists=>[[v Pv]].
rewrite [`1`]heigenUE; apply/cuphs_le=>/=i _.
apply: (le_trans _ (sp_lbounded _ (E := formso [> heigen i; v <] ) _)).
  rewrite formsoE adj_outp outp_compl outp_comp adj_dotEl supphZ.
    by rewrite psdf_dot_eq0E (sprojh_memJE Pv) ns_neq0.
    by rewrite -hlineE lexx.
rewrite fsemE/=; split.
  apply/cptnP; split. apply/is_cpmap.
  by rewrite krausso_tnE /trace_nincr big_ord1 
    adj_outp outp_comp ns_dot scale1r outp_le1// ns_dot.
rewrite CP_supph_le/= formsoE outp_compl hermf_adjE.
move: Pv; rewrite /sasaki_projection memhI memhOE ocomplK=>/andP[]/eqP-> _.
by rewrite outp0 comp_lfun0l supph0 le0h.
Qed.

Lemma sp_str_prob_choice p c1 c2 R : 
  sp (@prob_choice_ p c1 c2) R = sp c1 R `|` sp c2 R.
Proof.
rewrite /sp fsem_prob_choiceE1 cups_image. 
rewrite (cups_setM (fun i j => supph ((_ *: i + _ *: j : 'SO) R))).
rewrite -(cupsUl _ _ (fsem_nonempty c1)); apply eq_cupsr=>x1 P1.
rewrite -(cupsUr _ _ (fsem_nonempty c2)); apply eq_cupsr=>x2 P2.
move: (projT2 p) (projT2 p)=>/andP[]/ltW/=?/ltW;
rewrite -subr_ge0=>?/andP[]??.
by rewrite soE (QOperation_BuildE (fsem_qo P1)) (QOperation_BuildE (fsem_qo P2))
  supphD /= !soE !supphZ// lt0r_neq0// subr_gt0.
Qed.

Lemma sp_str_sequence c1 c2 R :
  sp (@sequence_ c1 c2) R = sp c2 (sp c1 R).
Proof.
rewrite /sp fsem_sequenceE1 cups_image. 
rewrite (cups_setM (fun i j => supph ((j :o i : 'SO) R))) cups_exchange.
apply eq_cupsr=>x2 P2.
rewrite (QOperation_BuildE (fsem_qo P2)) supph_cups.
apply eq_cupsr=>x1 P1.
by rewrite (QOperation_BuildE (fsem_qo P1)) supph_cp_supp soE.
Qed.

Lemma sp_str_condition T x P c1 c2 R : 
  sp (@condition_ T x P c1 c2) R = 
    (sp c1 (liftfh x P `&&` R)) `|` (sp c2 (liftfh x (~` P) `&&` R)).
Proof.
rewrite /sp fsem_conditionE1 cups_image. 
rewrite (cups_setM (fun i j => supph ((i :o _ + (j :o _) : 'SO) R))).
rewrite -(cupsUl _ _ (fsem_nonempty c1)); apply eq_cupsr=>x1 P1.
rewrite -(cupsUr _ _ (fsem_nonempty c2)); apply eq_cupsr=>x2 P2.
rewrite soE (QOperation_BuildE (fsem_qo P1)) (QOperation_BuildE (fsem_qo P2))
  supphD/=.
f_equal; rewrite 1?(QOperation_BuildE (fsem_qo P1))
  1?(QOperation_BuildE (fsem_qo P2)).
  by rewrite elemso_projTE liftfso_formso -liftfhE soE
    -supph_cp_supp/= formsoE hermf_adjE/= sprojhE.
by rewrite elemso_projFE liftfso_formso -th2hO -liftfhE soE
  -supph_cp_supp/= formsoE hermf_adjE/= sprojhE.
Qed.

Fixpoint sp_while_iter (T : qType) (x : 'QReg[T]) (P : {hspace 'Ht T}) 
  (c : cmd_) (R : {hspace _}) n : {hspace _} :=
  match n with
  | 0 => `0`
  | S n => R `|` sp c (liftfh x P `&&` (sp_while_iter x P c R n))
  end.

Lemma sp_sprojUr (c : cmd_) (P R1 R2 : {hspace _}) :
  sp c (P `&&` (R1 `|` R2)) = sp c (P `&&` R1) `|` sp c (P `&&` R2).
Proof.
rewrite /sp -cupsU; apply eq_cupsr=>E Pe.
by rewrite sprojUr -[in LHS]cuphE /cuph 
  (QOperation_BuildE (fsem_qo Pe)) supph_cp_supp linearD supphD/=.
Qed.

Lemma sp_while_iterE (T : qType) (x : 'QReg[T]) (P : {hspace 'Ht T}) 
  (c : cmd_) (R : {hspace _}) n : 
  sp_while_iter x P c R n.+1 = 
    R `|` sp_while_iter x P c (sp c (liftfh x P `&&` R)) n.
Proof.
have IH: forall n R, sp_while_iter x P c R n.+1 = 
  R `|` sp c (liftfh x P `&&` (sp_while_iter x P c R n)) by [].
elim: n R=>[R/=|n IH1 R]; first by rewrite sprojx0 sp_str_0.
by rewrite IH IH1 IH [in LHS]sp_sprojUr.
Qed.

Lemma sp_str_while T x P c R :
  sp (@while_ T x P c) R = \cups_(n : nat)
    (liftfh x (~` P) `&&` sp_while_iter x P c R n).
Proof.
rewrite /sp fsem_whileE1 cups_image.
transitivity (\cups_(x0 in [set l | (forall n : nat, fsem c (l n))])
  \cups_i supph ((\sum_(i0 < i) (formso (liftf_lf (tf2f x x (~` P))) :o 
    \compr_(j < i0) (x0 j :o formso (liftf_lf (tf2f x x P))))) R)).
- apply eq_cupsr => l /= Pl.
  have Pc: cvgn (fun n => \sum_(i < n) (formso (liftf_lf (tf2f x x (~` P))) :o 
    \compr_(j < i) (l j :o formso (liftf_lf (tf2f x x P))))).
    apply: whilegso_is_cvgn=>[|i]; last by apply/(fsem_qo (Pl i)).
    by rewrite !hermf_adjE/= !projf_idem/= -linearD/= -linearD/=
      hsE subrK tf2f1 liftf_lf1.
  rewrite -so_liml. apply: Pc.
  rewrite supphE kerh_limn ?capsO.
    - apply: so_is_cvgl. apply: Pc.
    - apply/chain_homo=>i; rewrite big_ord_recr/= soE !sum_soE levDl -psdlfE.
      under eq_bigr do rewrite (QOperation_BuildE (fsem_qo (Pl _))).
      by rewrite (CPMap_BuildE (comprso_cp _ _ _)) is_psdlf.
    - move=>n; rewrite soE; apply/psdlf_sum=>/=i _.
      under eq_bigr do rewrite (QOperation_BuildE (fsem_qo (Pl _))).
      by rewrite (CPMap_BuildE (comprso_cp _ _ _)) is_psdlf.
    - by under eq_cupsr do rewrite -supphE.
rewrite cups_exchange; apply eq_cupsr => n _.
elim: n R.
- move=>R /=; under eq_cupsr do rewrite big_ord0 soE supph0.
  rewrite sprojx0 cups_const//. move: (fsem_nonempty c)=>[y Py].
  by exists (fun i => y)=>/=.
move=>n IH R; rewrite set_natfun_splitl cups_image.
rewrite (cups_setM (fun x0 l => supph ((\sum_(i0 < n.+1) (_ :o \compr_(j < i0) 
  (match nat_of_ord j with | 0%N => x0 | n0.+1 => l n0 end :o _))) R))).
rewrite sp_while_iterE sprojUr -IH cups_exchange -cupsUr .
  by move: (fsem_nonempty c)=>[y Py]; exists (fun => y).
apply eq_cupsr=>l /= Pl.
set t := \sum_(_ | _) _; have Pt: t \is cpmap.
  rewrite /t -geso0_cpE sumv_ge0//==>[[m /= _ _]]; rewrite geso0_cpE.
  suff Pm: \compr_(j < m) (l j :o formso (liftf_lf (tf2f x x P))) \is cpmap
    by rewrite (CPMap_BuildE Pm) is_cpmap.
  elim: m=>[|m IH1]; first by rewrite big_ord0 is_cpmap.
  by rewrite big_ord_recr/= (CPMap_BuildE IH1) 
    (QOperation_BuildE (fsem_qo (Pl m))) is_cpmap.
rewrite /sp (CPMap_BuildE Pt) supph_cups -(cupsUr _ _ (fsem_nonempty c)).
apply eq_cupsr=>E Pe.
rewrite big_ord_recl big_ord0 comp_so1r soE/=.
under eq_bigr do rewrite/= bump0 big_ord_recl/= comp_soErl comp_soA.
rewrite -linear_suml/= [X in _ + X]soE -/t [X in _ + t X]soE.
rewrite (CPMap_BuildE Pt) (QOperation_BuildE (fsem_qo Pe)) supphD 
  -[X in _ `|` X]supph_cp_supp -[in X in _ `|` supph (_ X)]supph_cp_supp/=.
by do ! f_equal; rewrite -th2hE -liftfhE formsoE hermf_adjE sprojhE.
Qed.

End HoareTriple.