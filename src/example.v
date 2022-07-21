From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
Require Import forms.
From mathcomp.analysis Require Import boolp reals exp trigo.
From mathcomp.real_closed Require Import complex.
From mathcomp Require Import finset.

Require Import mcextra mxnorm mxtopology tensor dirac lfundef quantum inhabited.
Require Import hspace qwhile qhl qtype hspace hermitian.

(************************************************************************)
(* case study : prove Hoare triple of program via quantum Hoare logic   *)
(*      parallel Hadamard                : circuit                      *)
(*      reverse circuit                  : circuit                      *)
(*      quantum Fourier transformation   : circuit                      *)
(*      HHL algorithm                    : abstract                     *)
(*      hidden linear function problem   : abstract                     *)
(*      Grover's (search) algorithm      : abstract                     *)
(*      quantum phase estimation         : abstract                     *)
(*      hidden subgroup problem          : abstract                     *)
(************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import Vector.InternalTheory.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.
Local Open Scope ring_scope.
Local Open Scope set_scope.
Local Open Scope lfun_scope.
Local Open Scope qexpr_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* to hide the canonical of each cmd, define Phant later *)
(* maybe also change all the rules *)
(* e.g., definition unitary_of_ (U : 'FU) (phU : phant U) := unitary_ U *)
(* then define Notation unitary U := (unitary_of_ (Phant U)) *)

Section CaseStudy.
Context (L : finType) (HA : L -> chsType).
Notation vars T := (@tvars_of L HA _ (Phant T)).
Notation cmd_ := (@cmd_ L HA).
Notation seqc := (@seqc_ L HA).
Notation skip := (@skip_ L HA).

Section ParallelHadamardTuple.
Variable (pt st : bool) (n : nat) (fx : n.-tuple (vars bool)).
Hypotheses (disx : forall i j, i != j -> [disjoint lb (fx ~_ i) & lb (fx ~_ j)]).
Let px := pvars_tuple disx. (* we can pack fx as a whole *)

Definition bitstr_dot n (b1 b2 : n.-tuple bool) : nat :=
  (\sum_i (b1~_i * b2~_i))%N.

Lemma ParaHadamard_tuple (b : n.-tuple bool) :
  \tens_(i < n) ⌈''H;fx ~_ i⌉ ∘ ｜''b ; px〉
  = \sum_k sqrtC 2%:R ^- n *: ((-1) ^ bitstr_dot b k *: ｜''k ; px〉).
Proof.
rewrite pvarsEt dotq_com/=tensM//= =>[i j _ _ |]; first by apply: disx.
under eq_bigr do rewrite tlin_ket Hadamard_cb (onb_vec t2tv_onbasis '±(_))/= -tket_sum.
under eq_bigr do under eq_bigr do rewrite dotp_cbpm -tketZ mulrC -scalerA.
rewrite tenqA_distr_sumA (reindex (finfun_of_tuple)).
by exists tuple_of_finfun=>x _; rewrite ?finfun_of_tupleK ?tuple_of_finfunK.
apply eq_bigr=>i _; rewrite scalerA pvarsEt.
under eq_bigr do rewrite ffunE scalerA.
rewrite tensZ; f_equal. rewrite big_split/= prodr_const card_ord exprVn; f_equal.
by rewrite -expr_sum /bitstr_dot exprnP; under eq_bigr do rewrite andbC -mulnb.
Qed.

Lemma RS_ParaHadamard_tuple (b : n.-tuple bool) :
    ⊨s [pt,st] { ｜''b ; px〉 } 
          [for i do [ut fx ~_ i := ''H]]
        { (sqrtC 2%:R ^- n) *: \sum_i (-1) ^ (bitstr_dot b i) *: ｜''i ; px〉 }.
Proof.
rewrite linear_sum/=; apply: (RS_forward _ (AxV_UTFP _))=>[|i j]/=.
exact: ParaHadamard_tuple. apply: disx.
Qed.

End ParallelHadamardTuple.
Global Arguments RS_ParaHadamard_tuple [pt st n fx].

Section ParallelHadamardFfun.
Variable (pt st : bool) (F : finType) (fx : F -> (vars bool)).
Hypotheses (disx : forall i j, i != j -> [disjoint lb (fx i) & lb (fx j)]).

Lemma RS_ParaHadamard_ffun :
    ⊨s [pt,st] { \tens_i ｜'0; fx i〉 } 
          [for i do [ut fx i := ''H]]
        { \tens_i ｜'+; fx i〉 }.
Proof.
apply: (RS_forward _ (AxV_UTFP _))=>[|//].
rewrite/=dotq_com/= tensM//==>[+ + _ _|]; first exact: disx.
by under eq_bigr do rewrite tlin_ketM Hadamard_cb.
Qed.

Lemma RS_ParaHadamardV_ffun :
    ⊨s [pt,st] { \tens_i ｜'+; fx i〉 } 
          [for i do [ut fx i := ''H]]
        { \tens_i ｜'0; fx i〉 }.
Proof.
apply: (RS_forward _ (AxV_UTFP _))=>[/=|//].
rewrite/=dotq_com/= tensM//==>[+ + _ _|]; first exact: disx.
by under eq_bigr do rewrite tlin_ketM Hadamard_pm.
Qed.

End ParallelHadamardFfun.


Section RevTuple.
Variable (pt st : bool) (T : ihbFinType) (n : nat).
Variable (x : n.-tuple (vars T)).
Hypotheses (disx : forall i j, i != j -> [disjoint lb (x ~_ i) & lb (x ~_ j)]).

Lemma rev_disx i j : i != j -> 
  [disjoint lb ([tuple of rev x] ~_ i) & lb ([tuple of rev x] ~_ j)].
Proof. by rewrite -(inj_eq rev_ord_inj) !tnth_rev; exact: disx. Qed.

Definition rev_circuit :=
  \big[seqc/skip]_(i : 'I_n | (i < (n./2))%N) 
    [ut [x ~_ i , x ~_ (rev_ord i)] := SWAP ].

Lemma ltn_half_double : (n < (n./2).*2)%N = false.
Proof.
by apply/negP; rewrite -{1}(odd_double_half n) addnC=>/ltn_dropl; rewrite ltnn.
Qed.

Lemma rev_half_neq (i j : 'I_n) : (i < n./2)%N -> (j < n./2)%N -> rev_ord i != j.
Proof.
move=>Pi Pj; apply/eqP=>P; move: (leq_add Pi Pj).
by rewrite -P/= addnS addnC subnK// addnn ltn_half_double.
Qed.

Lemma rev_disjoint (i j : 'I_n) : (i < n./2)%N -> (j < n./2)%N -> i != j -> 
  [disjoint lb (x ~_ i) :|: lb (x ~_ (rev_ord i)) & lb (x ~_ j) :|: lb (x ~_ (rev_ord j))].
Proof.
by move=>Pi Pj nij; rewrite disjointUX !disjointXU !disx// 
  ?(can_eq rev_ordK)// ?[_ == rev_ord _]eq_sym ?rev_half_neq//.
Qed.

Lemma rev_unitaryE (t : 'Hs (n.-tuple T)) :
  \tens_(i : 'I_n | (i < n./2)%N) ⌈ SWAP ; (x~_i , x~_(rev_ord i)) ⌉
  ∘ ｜t; pvars_tuple disx〉= ｜t; pvars_tuple rev_disx〉.
Proof.
rewrite (onb_vec t2tv_onbasis t)/= -(t1ket_sum (pvars_tuple disx)).
rewrite -(t1ket_sum (pvars_tuple rev_disx)) dotq_sumr; apply eq_bigr=>i _.
rewrite -!tketZ dotqZr; f_equal; rewrite !pvarsEt.
move: rev_disjoint. case: n x disx t i; clear n x disx.
by move=>x disx t i; rewrite !big_ord0 bigq dot1q.
move=>n x disx t i rd; rewrite !big_half_split !bigqE/=; case E: (odd n).
2: under [in X in X ⊗ _]eq_bigr do rewrite tketT;
rewrite dotqTll//=; last (rewrite tnth_rev uphalf_ord_odd_rev ?E//; f_equal).
1,3: rewrite ?tenq1 dotq_com/= tensM//= bigq; apply eq_bigr=>j Pj;
by rewrite ?[in LHS]tketT tlin_ketM ?disx// 1?eq_sym ?rev_ord_neq// tenqC tketT swaptfEtv !tnth_rev rev_ordK.
rewrite disjoint_sym; apply/bigcup_disjointP=>j Pj;
rewrite disjointXU !disx//; last rewrite -(can_eq rev_ordK) rev_ordK uphalf_ord_odd_rev ?E//.
all: by rewrite uphalf_ord_neq.
Qed.

Lemma RS_rev_circuit (t : 'Hs (n.-tuple T)) :
  ⊨s [pt,st] { ｜t; pvars_tuple disx〉 } 
                rev_circuit
             { ｜t; pvars_tuple rev_disx〉 }.
Proof.
rewrite /rev_circuit.
apply: (RS_forward _ (AxV_UTFP_seq _ _))=>//=.
2: by move=>i j; apply: rev_disjoint.
rewrite -rev_unitaryE; do 2 f_equal; apply eq_bigr=>i Pi;
rewrite tf2f2cE// disx// -(inj_eq val_inj)/=. 
apply/eqP=>/(f_equal (addn^~ i.+1)); rewrite subnK// addnS addnn=>Pc.
move: Pi; rewrite -ltn_Sdouble Pc -{1}(odd_double_half n) addnC=>/ltn_dropl; 
by rewrite ltnn.
Qed.

Lemma RS_rev_circuitV (t : 'Hs (n.-tuple T)) :
  ⊨s [pt,st] { ｜t; pvars_tuple rev_disx〉 } 
                rev_circuit
             { ｜t; pvars_tuple disx〉 }.
Proof.
rewrite /rev_circuit.
apply: (RS_back _ (AxV_UTP_seq _ _))=>//=.
2: by move=>i j; apply: rev_disjoint.
rewrite -rev_unitaryE tens_adj; do 2 f_equal; apply eq_bigr=>i Pi;
rewrite tf2f2cE// ?tlin_adj ?swaptf_adj// disx// -(inj_eq val_inj)/=.
apply/eqP=>/(f_equal (addn^~ i.+1)); rewrite subnK// addnS addnn=>Pc.
move: Pi; rewrite -ltn_Sdouble Pc -{1}(odd_double_half n) addnC=>/ltn_dropl; 
by rewrite ltnn.
Qed.

End RevTuple.
Arguments RS_rev_circuit [pt st T n x disx].

(* implement QFT for tuple of qubits *)
Section QuantumFourierTransform.
Variable (pt st : bool).

Definition omegan (n : nat) : R := (2%:R ^- n.+1).

Definition QFT_sub (x : vars bool) (s : seq (vars bool)) :=
    [for i < (size s) do 
        [ut [x , (nth x s i)] := BControl (PhGate (omegan i))]
    ].

Fixpoint QFT_iter (s : seq (vars bool)) :=
    match s with 
    | [::] => skip
    | x :: t => [ut x := ''H] ;; (QFT_sub x t) ;; (@QFT_iter t)
    end.

Definition QFT_cir n (s : n.-tuple (vars bool)) :=
  ((QFT_iter s) ;; (rev_circuit s)).

Lemma fvars_QFT_sub (x : vars bool) (s : seq (vars bool)) :
    fvars (QFT_sub x s) =  \bigcup_(i <- s) (lb x :|: lb i).
Proof.
rewrite /QFT_sub fvars_for (big_nth x)/= big_mkord.
by apply eq_bigr =>i _.
Qed.

Lemma QFT_sub_rcons x y (s : seq (vars bool)) :
    (QFT_sub x (rcons s y)) =s 
    (QFT_sub x s ;; [ut [x,y] := BControl (PhGate (omegan (size s)))]).
Proof.
rewrite /eqcmd /QFT_sub/= fsemE !fsem_big/= size_rcons big_ord_recr .
rewrite comp_soElr nth_rcons ltnn eqxx. congr (_ o: _).
apply eq_bigr=>i _. rewrite nth_rcons. by destruct i=>/=; rewrite i.
Qed.

Lemma QFT_iter_no_while (s : seq (vars bool)) : no_while (QFT_iter s).
Proof. by elim: s=>[//|x r IH]; rewrite/= IH /QFT_sub no_while_for. Qed.

Lemma bigcup_add T (r : seq T) (P : pred T) (fp : T -> {set L}) (A : {set L}) :
    A :|: \bigcup_(i <- r | P i) (fp i) = A :|: \bigcup_(i <- r | P i) (A :|: (fp i)).
Proof.
elim: r=>[|x r]; first by rewrite !big_nil.
by rewrite !big_cons; case: (P x)=>//; rewrite !setUA setUid 
  [A :|: fp x]setUC -setUA=>->; rewrite setUA.
Qed.

Lemma fvars_QFT_iter (s : seq (vars bool)) : fvars (QFT_iter s) = \bigcup_(i <- s) lb i.
Proof.
elim: s=>[|x r IH]; first by rewrite /= big_nil.
by rewrite /= IH fvars_QFT_sub big_cons -bigcup_add -setUA setUid.
Qed.

Lemma PhGate_cb r b : PhGate r ''b = expip (b%:R * r) *: ''b.
Proof. by rude_bmx; case: b=>/=; rewrite ?mul0r ?mulr0// ?mul1r ?mulr1// expip0. Qed.

Lemma test1 b0 b (bs : seq bool) (x y : vars bool) : 
  [disjoint lb x & lb y] ->
  ｜'ph (bitstr2rat (b0 :: bs));x〉 ⊗ ｜''b;y〉
  = ⌈ (BControl (PhGate (omegan (size bs))))^A;(x,y) ⌉ ∘ 
    (｜'ph (bitstr2rat (b0 :: rcons bs b));x〉 ⊗ ｜''b;y〉).
Proof.
move=>P1. rewrite !tketT tlin_ketG -?vars_labelE=>[//|].
rewrite BControl_adj; congr (｜_;(_,_)〉).
rewrite BControlE lfunE/= !tentf_apply !outpE PhGate_adj.
rewrite dotp_cb0ph dotp_cb1ph phstateE linearDl/= lfunE/= PhGate_cb.
f_equal. rewrite !linearZl/= linearZr/= scalerA -mulrA. do 2 f_equal.
rewrite -expipD -rcons_cons bitstr_rcons.
case: b; last by rewrite !mul0r !addr0.
by rewrite mulrDr /omegan !mul1r exprS invfM mulrA mulfV// mul1r addrK.
Qed.

Lemma RS_QFT_sub n (x : vars bool) (b : bool) (s : n.-tuple (vars bool)) 
  (sb : n.-tuple bool) :
    (forall i, [disjoint lb x & lb (s~_i)]) ->
    (forall i j, i != j -> [disjoint lb (s~_i) & lb (s~_j)]) ->
    let: prev := ｜''b;x〉 ⊗ (\tens_i｜''(sb~_i);s~_i〉) in
    let: postv :=  ｜'ph (bitstr2rat (b :: sb));x〉 ⊗ (\tens_i｜''(sb~_i);s~_i〉) in
    ⊨s [pt,st] { prev  } ([ut x := ''H] ;; (QFT_sub x s)) { postv }.
Proof.
elim: n s sb=>[s sb _ _|n IH s bs xs us]; last first.
case/tupleNP: s xs us=>sl sh /=/rcons_disjointx[]P1 P2/rcons_disjoint[]P3 P4.
case/tupleNP: bs=>bsl bsh/=.
rewrite big_ord_recr/= bigqE.
rewrite !tnthN. under eq_bigr do rewrite !tnthNS.
rewrite [SPRE]tenqA [SPOST]tenqA.
move: P1; rewrite QFT_sub_rcons fsem_seqA=>P1.
apply (RS_SC (｜'ph (bitstr2rat (b :: bsh));x〉 
  ⊗ (\tens_i｜''(bsh~_i);sh~_i〉) ⊗ ｜''bsl;sl〉))=>/=; last first.
apply: RV_UT=>/=; rewrite [LHS]tenqAC [in RHS]tenqAC dotqTll/==>[//||].
2: by f_equal; rewrite test1 ?size_tuple// tf2f2cE// tf2f2_adj.
2: move: (IH sh bsh P2 P4); apply: RV_Frame.
2: by rewrite/=/QFT_sub no_while_for//=; clear -pt; case: pt.
1,2,3: rewrite ?setUid /=?fvars_QFT_sub -?bigcup_add disjointUX ?Q4/=.
2,3: rewrite P1/= disjoint_sym ?big_tuple. 1: apply/andP; split.
1,2,3,4: by apply/bigcup_disjoint_seqP=>i _.
rewrite !tuple0 ![sb]tuple0 /QFT_sub/= {1 2}big_ord0 big_ord0 bigq !tenq1.
apply: (RS_SC _ _ (AxS_Sk _))=>/=.
apply RS_UT=>//=; rewrite ?sub0set// tf2f_adj tlin_ketG Hadamard_adj.
rewrite -Hadamard_pm; do ! f_equal. rude_bmx.
rewrite [in _ [::b]]unlock.
by case: b; rewrite !sign_simp ?mul0r addr0 ?mulr0 ?mulfV// ?expip0 ?expip1 !sign_simp.
Qed.

Lemma QFTbv_rev n (s : n.-tuple (vars bool)) (sb : n.-tuple bool) 
  (diss : forall i j, i != j -> [disjoint lb (s ~_ i) & lb (s ~_ j)]) :
  ｜QFTbv sb; pvars_tuple (rev_disx diss)〉 = 
    \tens_(i < n) ｜'ph (bitstr2rat (drop i sb));s~_i〉.
Proof.
rewrite QFTbvTE pvarsEv; clear diss.
case: n s sb=>[s sb|n s sb]; first by rewrite !big_ord0.
rewrite [in RHS](reindex_inj rev_ord_inj)/= bigq; apply eq_bigr=>i _; congr (｜_;_〉).
by pose s0 := s~_ord0; rewrite !(tnth_nth s0)/= nth_rev size_tuple//.
by rewrite tnth_ffun_tuple ffunE.
Qed.

Lemma RS_QFT_iter n (s : n.-tuple (vars bool)) (sb : n.-tuple bool) 
  (diss : forall i j, i != j -> [disjoint lb (s ~_ i) & lb (s ~_ j)]) :
    ⊨s [pt,st] { ｜''sb ; pvars_tuple diss 〉 } (QFT_iter s) 
        { ｜QFTbv sb; pvars_tuple (rev_disx diss)〉 }.
Proof.
rewrite QFTbv_rev pvarsEt.
elim: n s sb diss =>[s sb _ | n IH s sb us];
  first by rewrite /QFT_iter/= !big_ord0 bigq tuple0/=; apply: AxS_Sk.
rewrite !big_ord_recl/= !bigqE.
case/tupleP: s us=>x bs; case/tupleP: sb=>b bsb/cons_disjoint[] P2 P3.
rewrite !tnth0; under eq_bigr do rewrite !tnthS.
apply (RS_SC (｜'ph (bitstr2rat (b :: bsb));x〉
  ⊗ (\tens_i ｜''(bsb ~_ i); bs ~_ i〉)))=>/=; last first.
apply: RV_Framel=>/=; last by under [in SPOST]eq_bigr do rewrite tnthS; apply IH.
clear -bs; case: pt=>//; apply: QFT_iter_no_while.
3 : by apply RS_QFT_sub. rewrite fvars_QFT_iter. 
2: rewrite setUC; under eq_bigr do rewrite tnthS.
all: by rewrite 1?setUid disjoint_sym ?big_tuple; apply/bigcup_disjointP=>i _.
Qed.

Lemma RS_QFT_cir n (s : n.-tuple (vars bool)) (sb : n.-tuple bool) 
  (diss : forall i j, i != j -> [disjoint lb (s ~_ i) & lb (s ~_ j)]) :
    ⊨s [pt,st] { ｜''sb ; pvars_tuple diss 〉 } ((QFT_iter s) ;; (rev_circuit s))
        { ｜QFTbv sb; pvars_tuple diss〉 }.
Proof.
apply: (RS_SC _ (RS_QFT_iter _ _)).
apply: RS_rev_circuitV.
Qed.

End QuantumFourierTransform.


Local Open Scope hspace_scope.

(* to hide local theorems, use Let instead of Definition and Lemma *)
Section HHL.
Variable (m n : nat).
(* q : m.+1 : dimension of data; p : n.+1 : dimension of control system *)
Variable (p : vars 'I_n.+1) (q : vars 'I_m.+1) (r : vars bool).
(* here, we provide the decomposition of data : A; pure state b *)
Variable (u : 'ONB('I_m.+1; 'Hs 'I_m.+1)) (λ : 'I_m.+1 -> R) (b : 'NS('Hs 'I_m.+1)).
Let A := \sum_i (λ i)%:C *: [> u i ; u i <].
(* δ : ensure that control system is enough to store eigenvalue δ *)
Variable  (t0 : R) (δ : 'I_m.+1 -> 'I_n.+1) (cc : C).
(* this assumption to make the algorithm exact *)
Hypothesis (Hyp : forall i, pi * 2%:R * (δ i)%:R = λ i * t0).
(* assume A is non-degenerate *)
Hypothesis (D_neq0 : forall i, (0 < (δ i))%N).
(* to construct a valid control gate between p and auxiliary system r *)
Hypothesis (cc_bound : `|cc| <= 1).
Let β := (fun i=> [<u i ; b : 'Hs 'I_m.+1 >]).
Let decb : ((b : 'Hs 'I_m.+1) = \sum_i (β i) *: (u i)).
Proof. exact: onb_vec. Qed.
Let lambda_gt0 : forall i, λ i != 0.
Proof. 
move=>i; apply/eqP=>P. move: (Hyp i)=>/eqP; apply/negP.
rewrite P mul0r mulf_eq0 mulf_eq0 !pnatr_eq0 !negb_or.
do ? (apply/andP; split=>//). apply pi_neq0. by apply/lt0n_neq0.
Qed.
Let t0_neq0 : t0 != 0.
Proof.
apply/eqP=>P. move: (Hyp ord0)=>/eqP; apply/negP.
rewrite P mulr0 mulf_eq0 mulf_eq0 !pnatr_eq0 !negb_or.
do ? (apply/andP; split=>//). apply pi_neq0. by apply/lt0n_neq0.
Qed.
Let  lambdaE i : λ i = (pi * 2%:R / t0) * (δ i)%:R.
Proof. by rewrite -mulrA [_^-1 * _]mulrC mulrA Hyp mulfK//. Qed.
Let x_uns := \sum_i (β i / (λ i)%:C) *: (u i).
Let c := `|x_uns|.
Let c_gt0 : c > 0.
have : exists i, β i != 0.
  rewrite not_existsP=>P.
  have Pb : (b : 'Hs _) = 0 by rewrite decb big1// =>i _; 
    move: (P i)=>/negP/negbNE/eqP->; rewrite scale0r.
  by move: (ns_dot b); rewrite Pb linear0=>/eqP; rewrite eq_sym oner_eq0.
move=>[i/negPf Pi]. rewrite /c lt_def normr_ge0 andbT hnormE sqrtC_eq0.
rewrite /x_uns linear_sumr/= psumr_eq0=>[j _|].
2: rewrite -big_all big_negb_all big_orE; apply/existsP; exists i=>/=.
1: rewrite linear_suml/= (bigD1 j)//=. 2: rewrite linear_suml/= (bigD1 i)//=.
all: rewrite big1=>[k/negPf nk|];
rewrite dotpZl dotpZr onb_dot ?nk ?mulr0// eqxx mulr1 addr0 -normCKC ?exprn_ge0//.
by rewrite sqrf_eq0 normr_eq0 mulf_eq0 Pi/= invr_eq0 realc_eq0 lambda_gt0.
Qed.
Let x := c^-1 *: x_uns.
Let x_ns : [< x ; x >] == 1.
Proof.
rewrite dotp_norm /x normrZ -/c ger0_norm ?invr_ge0 ?mulVf ?expr1n//.
apply/ltW/c_gt0. apply/lt0r_neq0/c_gt0.
Qed.
Local Canonical x_nsType := NSType x_ns.
(* Ub |0;p> -> b *)
Let Ub := VUnitary [NS of ''ord0] b.
Let Uf_fun := (fun i : 'I_n.+1 => expmxip u λ (i%:R * t0 / pi / n.+1%:R)).
(* Uf is a Multiplexer *)
Let Uf := Multiplexer Uf_fun.
(* QFT : QFT : QFT unitary; QFTv : QFT basis *)
(* to defintion Uc, note that its partial *)
Let Uc_from := (fun i : 'I_n.+1 => ''i ⊗t '0).
Let v k := (fun i : 'I_k.+1 => if i == 0 then '0 else 
  [bmv sqrtC (1 - `|cc|^+2/i%:R^+2) ; cc / i%:R]).
Let v_ns k i : [< @v k i ; @v k i >] == 1.
Proof.
apply/eqP; rewrite /v; case: eqP=>[_|/eqP]; rude_bmx=>//.
rewrite -lt0n=>P; rewrite -!normCKC [in X in _ + X]ger0_norm.
rewrite sqrtC_ge0 subr_ge0 ler_pdivr_mulr ?exprn_gt0// ?ltr0n// mul1r.
apply: ler_expn2r; rewrite ?nnegrE//.
by apply: (le_trans cc_bound); rewrite ler1n.
by rewrite sqrtCK normf_div [`|i%:R|]ger0_norm// 
  expr_div_n addrC -addrA addNr addr0.
Qed.
Local Canonical v_nsType k i := NSType (@v_ns k i).
Let Uc_to := (fun i : 'I_n.+1 => ''i ⊗t v i).
Let Uc_from_ponb : forall i j, [< Uc_from i ; Uc_from j >] = (i == j)%:R.
Proof. by move=>i j; rewrite /Uc_from tentv_dot !onb_dot eqxx mulr1. Qed.
Let Uc_to_ponb : forall i j, [< Uc_to i ; Uc_to j >] = (i == j)%:R.
Proof.
move=>i j; rewrite /Uc_to tentv_dot onb_dot.
by case: eqP=>[->|_]; rewrite ?mul0r// ns_dot mulr1.
Qed.
Local Canonical Uc_from_ponbasis := PONBasis Uc_from_ponb.
Local Canonical Uc_to_ponbasis := PONBasis Uc_to_ponb.
Let Uc := PUnitary [PONB of Uc_from] [PONB of Uc_to].

(* we assume that p q r are different *)
Hypothesis (npq : [disjoint lb p & lb q]) (nqr : [disjoint lb q & lb r]) 
  (npr : [disjoint lb p & lb r]).
(* define the loop body of HHL *)
(* we split the initial part out, to use etdf of HHL body *)
Definition HHL_body := 
  [ut q := Ub ];;
  [ut p := 'Hn ];;
  [ut [p,q] := Uf ];;
  [ut p := IQFT ];;
  [ut [p,r] := Uc ];;
  [ut p := QFT ];;
  [ut [p,q] := Uf^A ];;
  [ut p := 'Hn^A ].

Definition HHL :=
  [it p := ''ord0 ];;
  [it q := ''ord0 ];;
  [it r := '0 ];;
  [while tmeas[ r ] = false do [it q := ''ord0] ;; HHL_body].

(* we show the correctness w.r.t. local correctness *)
Let P := ⌈ [> ''ord0; ''ord0 <]; p ⌉ ⊗ ⌈ \1; q ⌉ ⊗ ⌈ [> '0; '0 <]; r ⌉.
Let Q := ⌈ [> ''ord0; ''ord0 <]; p ⌉ ⊗ ⌈ [> x ; x <]; q ⌉ ⊗ ⌈ [> '1; '1 <]; r ⌉.

Let vv := \sum_(i < m.+1) (β i *: u i ⊗t v (δ i)).
Lemma vv_norm1 : `|vv| = 1.
Proof.
apply/eqP; rewrite hnorm_eq1 /vv linear_sum/=.
move: (ns_dot b)=><-; rewrite decb linear_sum/=.
apply/eqP; apply eq_bigr=>i _; rewrite !dotp_suml; apply eq_bigr=>j _.
rewrite !linearZl/= !linearZr/= tentv_dot onb_dot.
by case: eqP=>[->|]; rewrite ?mul0r ?mulr0// ns_dot mulr1.
Qed.
Let pp0 := (\1 : 'End['I_m.+1]) ⊗f [> '0; '0 <].
Let pp1 := [> x ; x <] ⊗f [> '1; '1 <].
Lemma pp0_proj : pp0 \is projlf.
Proof.
by apply/projlfP; rewrite /pp0 tentf_adj adj_outp adjf1 
  tentf_comp comp_lfun1l outp_comp onb_dot scale1r.
Qed.
Local Canonical pp0_projfType := ProjfType pp0_proj.
Lemma pp1_proj : pp1 \is projlf.
Proof.
by apply/projlfP; rewrite /pp1 tentf_adj !adj_outp
  tentf_comp !outp_comp !ns_dot !scale1r.
Qed.
Local Canonical pp1_projfType := ProjfType pp1_proj.
Lemma pp0_ortho_pp1 : pp0 \o pp1 = 0.
Proof. by rewrite /pp0 /pp1 tentf_comp outp_comp onb_dot/= scale0r tentf0. Qed.

Lemma v_deltai i : v (δ i) = cc / (δ i)%:R *: '1 + sqrtC (1 - `|cc| ^+ 2 / (δ i)%:R ^+ 2) *: '0.
Proof.
rewrite /v; case: eqP=>[P1|_]. by move: (D_neq0 i); rewrite P1.
by rude_bmx.
Qed.

Lemma vv_lef : [> vv ; vv <] ⊑ pp0 + pp1.
Proof.
move: (suppU_comp0 pp0_ortho_pp1)=>/=<-; apply lef_outp; rewrite ?vv_norm1//= /vv.
under eq_bigr do rewrite v_deltai linearDr/=.
rewrite big_split/= addrC; apply: memhU.
  rewrite memhE supph_projK hsE/=/pp0 linear_sum.
  apply/eqP; apply eq_bigr=>i _.
  by rewrite/=tentf_apply lfunE/= linearZ/= outpE ns_dot scale1r.
  rewrite /pp1 tentv_out -hlineE.
under eq_bigr do rewrite linearZl/= linearZr/= scalerA mulrC -mulrA -scalerA.
rewrite -linear_sum/=; apply memhZ; rewrite /x linearZl/= hlineZ.
by rewrite invr_eq0; apply/lt0r_neq0.
rewrite /x_uns tentv_suml. under [in X in <[X]> ]eq_bigr do rewrite lambdaE mulrC
  realcM invfM natrC tentvZl -[_ * _ * β _]mulrA -scalerA.
rewrite -linear_sum/= hlineZ; last by apply: memh_line.
by rewrite invr_eq0 realc_eq0 !mulf_eq0 !negb_or pi_neq0/= invr_eq0 t0_neq0 andbT.
Qed.

Let R := ｜''ord0;p〉 ⊗ ｜vv;(q,r)〉.
Lemma RS_HHL_body pt st : 
  ⊨s [pt,st] { ｜''ord0;p〉 ⊗ ｜''ord0;q〉 ⊗ ｜'0;r〉 } 
               HHL_body { R }.
rewrite /HHL_body /R.
apply: (RS_SC _ _ (AxV_UT _))=>/=.
rewrite tf2f_adj tlin_ketTl/=.
- by rewrite disjointXU npq npr.
rewrite adjfK VUnitaryE/= uniformtvE card_ord -tketZ tenqZl /vv -tket_sum -tket_sum tenq_sumr.
+ apply: (RS_SC _ _ (AxV_UT _))=>/=.
rewrite tf2f2c_adj adjfK [in SPOST]tf2f2cE// dotqZr dotq_sumr.
under eq_bigr do rewrite tenq_suml dotq_sumr/=.
suff P1: [disjoint lb p :|: lb q & lb r].
under eq_bigr do under eq_bigr do rewrite -tketT tenqA tketT (t2lin_ketTl npq _ _ _ P1)/=.
+ apply: (RS_SC _ _ (AxV_UT _))=>/=.
+ apply: (RS_forward (R := \sum_j(｜''(δ j) ⊗t v (δ j);(p,r)〉 ⊗ ｜β j *: u j;q〉))).
rewrite linear_sum/= dotq_sumr; apply eq_bigr=>i _.
rewrite tf2f_adj -/IQFT -tketT tenqAC -tenqA.
under eq_bigr do rewrite 2!linearZ/= MultiplexerEt expmxipEt -tentvZS -linearZr/= -tketT -tenqA.
rewrite -tenq_suml -tenqZl tket_sum tketZ tlin_ketTl/=.
- by rewrite disjointXU npq npr.
congr (｜_;p〉⊗ _).
under eq_bigr do rewrite mulrA -[ _ / pi]mulrA [_%:R * _]mulrC !mulrA -Hyp -[ _ / pi]mulrC.
under eq_bigr do rewrite !mulrA (mulVf pi_neq0) mul1r -[_%:R * _ * _]mulrA -natrM -runityE.
by rewrite -QFTvE IQFTEt.
+ apply: (RS_SC _ _ (AxV_UT _))=>/=.
rewrite tf2f2cE// tf2f2_adj dotq_sumr.
suff P2: [disjoint lb p :|: lb r & lb q].
under eq_bigr do rewrite (t2lin_ketTl npr _ _ _ P2)/= PUnitaryEV -tketT tenqAC.
rewrite -tenq_suml.
+ apply: RV_Frame=>//=; first by case: pt.
- 1,2: rewrite ?disjointX0// ?[_ :|: lb p]setUC setUid// setUA setUid//.
move: npq. rewrite -!fsem_seqA=>_.
+ apply: (RS_SC _ (AxV_UTF _))=>/=.
rewrite tlin_ketTr/= 1?disjoint_sym//.
+ apply: (RS_SC _ (AxV_UTF _))=>/=.
rewrite tlin_ketTl//=.
+ apply: (RS_SC _ (AxV_UTF _))=>/=.
rewrite tketT tf2f2cE// tlin_ketG//.
+ apply: RV_UTF.
rewrite/= !VUnitaryE/= uniformtvE card_ord decb 2!linear_sum/= -tket_sum dotq_sumr.
apply eq_bigr=>i _.
rewrite linearZl/= [in RHS]linearZ/= -[in RHS]tketZ linear_suml/= linear_sum/= -tket_sum.
under eq_bigr do rewrite 2!linearZ/= MultiplexerEt expmxipEt -tentvZS -linearZr/= -tketT
  mulrA -[ _ / pi]mulrA [_%:R * _]mulrC !mulrA -Hyp -[ _ / pi]mulrC 
  !mulrA (mulVf pi_neq0) mul1r -[_%:R * _ * _]mulrA -natrM -runityE.
by rewrite -tenq_suml -tenqZl tket_sum tketZ -QFTvE tlin_ketTl -?disjoint_neqE//= IQFTEt.
all: by rewrite disjointUX ?[[disjoint lb r & _]]disjoint_sym ?npq ?nqr// npr.
Qed.

(* need the theory of subspace/projection here *)
(* set up a new file for this theory ; to replace vector vspace *)
Let disjointr_pq : [disjoint lb r & lb p :|: lb q].
Proof. by rewrite disjoint_sym disjointUX npr nqr. Qed.

Lemma HHL_PQR_relation : R ∗ R`A ⊑ qeform (⌈ [> '1 ; '1 <];r ⌉) Q 
  + qeform (⌈ [> '0 ; '0 <];r ⌉) P.
Proof.
rewrite !qeformE !tlin_adj !adj_outp /P /Q ![_ ⊗ ⌈_;r⌉]tenqC.
rewrite !tlin_comTll//= ?tlin_comTrl//=  !outp_comp !onb_dot !eqxx 
  !scale1r !outp_comp !onb_dot !eqxx !scale1r ![⌈_;r⌉ ⊗ _]tenqC -!tenqA -tenqDr.
rewrite /R adjqT !ket_adj tenq_com ?disjoint0X// !touter.
apply: le_wptenq2l=>/=. by rewrite disjointXU npq npr.
by rewrite lin_gef0 tf2f_ge0 outp_ge0.
by rewrite !tlinT tlinD lin_lef tf2f2_lef// addrC vv_lef.
Qed.

Let P' := ⌈ [> ''ord0; ''ord0 <]; p ⌉ ⊗ ⌈ [> ''ord0; ''ord0 <]; q ⌉ ⊗ ⌈ [> '0; '0 <]; r ⌉.
Lemma R_HHL_loop_P :
  ⊨p { qeform (⌈ [> ''(~~false) ; ''(~~false) <];r ⌉) Q + qeform (⌈ [> '0 ; '0 <];r ⌉) P } 
  [while tmeas[r] = false do [it q := ''ord0] ;; HHL_body]
  { Q }.
apply: tbR_LP_P=>/=.
1,2: rewrite tlinT -tenqe_correct linqe_id -tenf11; apply: lev_pbreg2.
1,6: by rewrite disjointUX npr nqr.
1,5: rewrite tf2f2_ge0//. 4,7: rewrite tf2f2_le1//.
1,2,3,7: apply: psdf_ge0.
1,2,3,4: apply: obsf_le1.
apply: (R_SC [sqr of P' ]).
rewrite /=/P' -!tenqA [POST]tenqC -tenqA.
rewrite tenqC -tenqA -tlin1 tenqC R_El/= 1?disjoint_sym.
2: apply: tAx_InF.
1,2: by rewrite disjointXU nqr disjoint_sym npq.
rewrite/=. move: (RS_HHL_body false false); rewrite stateE.
apply: R_Or; last by exact: HHL_PQR_relation.
by rewrite /P'/= !adjqT !ket_adj !tenq_com/= ?disjointX0// !touterM.
Qed.


Lemma R_HHL_P : ⊨ps { |1 } HHL { ｜x;q〉}.
Proof.
rewrite stateE adjq1 cplxM mul1r ket_adj touterM.
apply/(R_Er (W:= lb p :|: lb r) _)=>/=.
by rewrite disjointXU nqr disjoint_sym npq.
apply: (R_Orr (Q:=Q) _)=>/=.
by rewrite /Q -tenqA tenqCA tlinT//; apply: le_wptenq2l=>/=;
rewrite ?lin_gef0 ?psdf_ge0 ?lin_lef1 ?tf2f2_le1 ?obsf_le1// disjointXU nqr disjoint_sym npq.
rewrite /HHL. apply: (R_SC _ _ R_HHL_loop_P)=>/=.
have: ⊨p { |1 } ([it p := ''ord0] ;; [it q := ''ord0] ;; [it r := '0]) {P'}.
rewrite /P' tenqC; apply: (R_SC _ _ (tAx_In _))=>/=.
rewrite outpE ns_dot scale1r ns_dot scale1r.
apply: (R_SC _ (tAx_InF _))=>/=;
rewrite ?disjointX0// tenq1 tenqC; apply: tAx_InF.
1,2: by rewrite ?disjointXU disjoint_sym ?npq// npr/= disjoint_sym.
apply: R_Or=>//=. rewrite -[P']add0r lev_add//.
all: rewrite tenqC qeformE tlin_adj adj_outp tlin_comTll// tlin_comTrl//=.
all: rewrite outp_comp ns_dot scale1r outp_comp ns_dot scale1r /P'.
2: rewrite tenqC. all: rewrite !tenqA tlinT -!tenqe_correct ?lin_lef.
1: rewrite lin_gef0.
apply: bregv_ge0. 4: apply: lev_wpbreg2l.
2,5: rewrite tf2f2_ge0. 3,5,6: apply: psdf_ge0.
5: by rewrite tf2f_lef obsf_le1.
all: rewrite ?disjointUX ?npq disjoint_sym ?npr// ?nqr//.
Qed.

End HHL.


(* HLF *)
Section HiddenLinearFunction.
Variable (pt st : bool) (N : nat). (* grid of N.+1 * N.+1 *)
Variable (A : 'M[bool]_N.+1).
Hypotheses (A_sym : forall i j, A i j = A j i).
Variable (x : N.+1.-tuple (vars bool)).
Hypothesis (disx : forall i j, i != j -> [disjoint lb (x ~_ i) & lb (x ~_ j)]).

Definition HLF_q (k : N.+1.-tuple bool) :=
  ((\sum_j A j.1 j.2 * k ~_ j.1 * k ~_ j.2) %% 4)%N.

Definition SD := [set x : 'I_N.+1 | A x x == true].
Definition SS := [set x : 'I_N.+1 * 'I_N.+1 | (A x.1 x.2 == true) && (x.1 < x.2)%N].
Lemma SD_inP y : y \in SD -> A y y = true.
Proof. by rewrite inE=>/eqP. Qed. 
Lemma SS_inP y : y \in SS -> A y.1 y.2 = true /\ (y.1 < y.2)%N /\ y.1 != y.2.
Proof. by rewrite inE=>/andP[/eqP]; split=>//; split=>//; apply: ltn_neq. Qed.

Definition HLF_sub1 :=
  [for i do [it x ~_ i := '0 ]];;
  [for i do [ut x ~_ i := ''H ]].

Definition HLF_sub2 (r1 : seq 'I_N.+1) (SP1 : pred 'I_N.+1) :=
  [for i <- r1 | SP1 i do [ut x ~_ i := ''S ]].

Definition HLF_sub3 (r2 : seq ('I_N.+1 * 'I_N.+1)) (SP2 : pred ('I_N.+1 * 'I_N.+1)) :=
  [for i <- r2 | SP2 i do [ut [x ~_ i.1 , x ~_ i.2] := ''CZ ]].

Definition HLF :=
  [for i do [it x ~_ i := '0 ]];;
  [for i do [ut x ~_ i := ''H ]];;
  [for i in SD do [ut x ~_ i := ''S ]];;
  [for i in SS do [ut [x ~_ i.1 , x ~_ i.2] := ''CZ ]];;
  [for i do [ut x ~_ i := ''H ]].

Lemma fsem_big_rcons I i r (P : pred I) (F : I -> cmd_) :
  let x := \big[seqc/skip]_(j <- r | P j) F j in
  \big[seqc/skip]_(j <- rcons r i | P j) F j =s if P i then x ;; (F i) else x.
Proof. by rewrite/=/eqcmd; case E: (P i)=>/=; rewrite ?fsemE !fsem_big big_rcons/= E//. Qed.

Lemma fsem_big_recr n F :
  \big[seqc/skip]_(i < n.+1) F i =s
     ((\big[seqc/skip]_(i < n) F (widen_ord (leqnSn n) i)) ;; F ord_max).
Proof. by rewrite/eqcmd fsemE !fsem_big big_ord_recr/=. Qed.

Lemma plus_dec : '+ = (sqrtC 2%:R)^-1 *: \sum_(i : bool) ''i.
Proof. by rewrite big_bool/=; rude_bmx. Qed.

Let PT: True. by []. Qed.

Lemma RS_HLF_sub12 (r1 : seq 'I_N.+1) (SP1 : pred 'I_N.+1) :
  ⊨s [pt,st] { |1 } (HLF_sub1 ;; HLF_sub2 r1 SP1) { (sqrtC 2%:R ^- N.+1 *:
  (\sum_(i : N.+1.-tuple bool) ('i ^ (\sum_(j <- r1 | SP1 j) i ~_ j)%N) *: ｜''i;pvars_tuple disx〉)) }.
Proof.
rewrite /HLF. move: {+}PT. rewrite -!fsem_seqA=>_.
apply: (RS_SC _ (tAxV_InFP_seq _ _ _))=>[++ _ _|||]; 
rewrite ?disjoint0X//=tenq1 -pvarsEt_nseq.
apply: (RS_SC _ (RS_ParaHadamard_tuple disx _) _).
rewrite /HLF_sub2; elim/last_ind: r1=>[|r i IH].
rewrite !big_nil; apply: (RS_forward _ (AxS_Sk _)).
rewrite/=; f_equal; apply eq_bigr=>bs _; f_equal; 
rewrite /bitstr_dot big_nil big1 ?expr0z// =>i _. by rewrite tnth_nseq.
move: PT; rewrite fsem_big_rcons=>_; case E: (SP1 i); last first.
by apply: (RS_forward _ IH); under [in RHS]eq_bigr do rewrite big_rcons E/=.
apply: (RS_SC _ IH).
apply : (RS_forward _ (AxV_UTF _)).
rewrite/= !linear_sum/=; apply eq_bigr=>bs _.
rewrite !dotqZr; f_equal; rewrite/= pvarsEt (bigD1 i)//= bigqE tlin_ketTl/=; last first.
rewrite SGate_cb -tketZ tenqZl scalerA; f_equal.
by rewrite big_rcons E/= -!exprnP -exprD.
apply/bigcup_disjoint_seqP=>j/andP[_]; rewrite disjoint_sym; apply: disx.
Qed.

Lemma RS_HLF_sub (r1 : seq 'I_N.+1) (SP1 : pred 'I_N.+1) 
  (r2 : seq ('I_N.+1 * 'I_N.+1)) (SP2 : pred ('I_N.+1 * 'I_N.+1)) :
  (forall x, SP2 x -> x.1 != x.2) -> 
  ⊨s [pt,st] { |1 } (HLF_sub1 ;; HLF_sub2 r1 SP1 ;; HLF_sub3 r2 SP2) { (sqrtC 2%:R ^- N.+1 *:
  (\sum_(i : N.+1.-tuple bool) 
    ('i ^ (\sum_(j <- r1 | SP1 j) i ~_ j + 2 * \sum_(j <- r2 | SP2 j) i ~_ j.1 * i ~_ j.2)%N) 
      *: ｜''i;pvars_tuple disx〉)) }.
Proof.
move=>H2; apply: (RS_SC _ (RS_HLF_sub12 _ _)).
rewrite /HLF_sub3; elim/last_ind: r2=>[|r i IH].
rewrite !big_nil; apply: (RS_forward _ (AxS_Sk _)).
by rewrite/=; f_equal; apply eq_bigr=>bs _; f_equal; 
rewrite /bitstr_dot big_nil muln0 addn0.
move: PT; rewrite fsem_big_rcons=>_; case E: (SP2 i); last first.
by apply: (RS_forward _ IH); under [in RHS]eq_bigr do rewrite big_rcons E/=.
apply: (RS_SC _ IH).
apply : (RS_forward _ (AxV_UTF _)).
rewrite/= !linear_sum/=; apply eq_bigr=>bs _.
rewrite !dotqZr; f_equal; rewrite/= big_rcons E/= mulnDr addnA -!exprnP [in RHS]exprD.
rewrite -scalerA; f_equal. rewrite exprM sqrCi tf2f2cE; last first.
rewrite pvarsEt (bigD1 i.1)//= bigqE (bigD1 i.2) 1?eq_sym ?H2// bigqE tenqA  
  tketT tlin_ketTl; last first.
rewrite/= CZGate_cb tentvZr -tketZ tenqZl; f_equal.
by case: (bs ~_ i.1); case: (bs ~_ i.2).
rewrite disjointUX; apply/andP; split; apply/bigcup_disjoint_seqP;
  by move=>j/andP[_]/andP[]P1 P2; apply disx; rewrite eq_sym.
all: by rewrite disx// H2.
Qed.

Lemma RS_HLF_gen :
  ⊨s [pt,st] { |1 } HLF { (2%:R ^- N.+1 *:
  (\sum_(z : N.+1.-tuple bool) (\sum_(k : N.+1.-tuple bool) 
    ('i ^ (\sum_(j in SD) k ~_ j + 2 * (\sum_(j in SS) k ~_ j.1 * k ~_ j.2) + 2 * \sum_j k~_j * z ~_ j)%N)) 
      *: ｜''z;pvars_tuple disx〉)) }.
rewrite /HLF big_setEV.
apply: (RS_SC _ (RS_HLF_sub _ _ _ _)).
by move=>i; rewrite inE=>/andP[] _; exact: ltn_neq.
apply: (RS_forward _ (AxV_UTFP_seq _ _))=>[|//|++ _ _]; last by [].
rewrite/= dotqZr dotq_sumr.
under eq_bigr do rewrite dotqZr (ParaHadamard_tuple disx) linear_sum/=.
rewrite exchange_big !linear_sum/=; apply eq_bigr=>bs _.
under eq_bigr do rewrite scalerA mulrC scalerA -mulrA -scalerA.
rewrite -linear_sum/= scalerA -invfM -expr2 exprAC sqrtCK -scaler_suml; do 2 f_equal.
apply eq_bigr=>k _. rewrite -!exprnP [in RHS]exprD; f_equal.
by rewrite exprM sqrCi.
Qed.

Lemma HLF_quadE (k : N.+1.-tuple bool) : 
  ('i : C) ^ (\sum_(j in SD) k ~_ j + 2 * (\sum_(j in SS) k ~_ j.1 * k ~_ j.2))%N
  = 'i ^ (HLF_q k).
Proof.
have ->: (\sum_(j in SD) k ~_ j + 2 * (\sum_(j in SS) k ~_ j.1 * k ~_ j.2))%N
  = (\sum_j ((A j.1 j.2) * k ~_ j.1 * k ~_ j.2))%N.
rewrite [in RHS](bigID (fun i=>(i.1 == i.2)))/=; f_equal.
rewrite -big_setE pair_bigV/= big_mkcond /=; apply eq_bigr=>i _.
rewrite (bigD1 i)//= big1=>[j|]; first by rewrite eq_sym andbN.
by rewrite addn0; case: (A i i); rewrite /= ?mul0n// mul1n mulnb Bool.andb_diag.
rewrite mul2n -addnn [in RHS](bigID (fun i : 'I_N.+1 * 'I_N.+1=>(i.1 < i.2)%N))/=.
f_equal. rewrite -big_setE big_mkcond/= [RHS]big_mkcond/=.
2: rewrite [RHS]big_mkcond/= [RHS]pair_bigV exchange_big pair_big/= -big_setE big_mkcond/=.
1,2: by apply eq_bigr=>i _; rewrite -?leqNgt ?[i.2 == _]eq_sym ltn_neqAle
  (inj_eq val_inj) ?[A i.2 i.1]A_sym; case: (A i.1 i.2)=>/=; 
  case: eqP=>_; case: (i.1 <= i.2)%N=>//=; rewrite mul1n// mulnC.
rewrite (divn_eq (\sum_(_ |_) _) 4%N) exprzD_nat mulnC PoszM -exprz_exp.
suff ->: ('i : C) ^ 4%N = 1 by rewrite exp1rz mul1r.
by rewrite -[RHS]opprK -mulrN1 -!sqrCi -exprD exprnP.
Qed.

Lemma RS_HLF :
  ⊨s [pt,st] { |1 } HLF { (2%:R ^- N.+1 *:
  (\sum_(z : N.+1.-tuple bool) (\sum_(k : N.+1.-tuple bool) 
    ('i ^ (HLF_q k + 2 * \sum_j k~_j * z ~_ j)%N)) 
      *: ｜''z;pvars_tuple disx〉)) }.
Proof.
apply: (RS_forward _ RS_HLF_gen). f_equal; apply eq_bigr=>z _; f_equal.
by apply eq_bigr=>k _; rewrite exprzD_nat HLF_quadE -exprzD_nat PoszM.
Qed.

End HiddenLinearFunction.

Ltac simpc2r := rewrite -?(natrC, realcN, realcD, realcM, realcI, realcX, realc_norm).

Section GroverAlgorithm.
Variable (pt st : bool) (T : ihbFinType). (* arbitrary ihbFinType *)
Variable (x : vars T).
Variable (Pw : pred T). (* Solution *)
Hypothesis (card_Pw : (0 < #|Pw| < #|T|)%N). (* proper number of solutions *)
Local Notation t0 := (witness T : T).
Local Notation us := (@uniformtv T).
Let Uw := PhOracle Pw.
Let Ut0 := 2%:R *: [> ''t0 ; ''t0 <] - \1.
Let Us := 2%:R *: [> us ; us <] - \1.
Lemma Us_diffE : Us = 'Hn \o Ut0 \o 'Hn^A.
Proof.
by rewrite /Ut0 linearBr/= linearZr/= outp_compr VUnitaryE/= comp_lfun1r 
  linearBl/= linearZl/= outp_compl adjfK VUnitaryE/= unitaryf_formV.
Qed.
Let Ut0_unitary : Ut0 \is unitarylf.
Proof.
apply/unitarylfP; rewrite /Us raddfB/= adjf1 adjfZ conjC_nat adj_outp.
rewrite linearBr/= !linearBl/= !comp_lfun1l comp_lfun1r linearZl/= linearZr/=.
rewrite scalerA outp_comp ns_dot scale1r opprB -scalerBl [\1 - _]addrC.
by rewrite addrA -scalerBl mulr_natr mulr2n addrK subrr scale0r add0r.
Qed.
Local Canonical Ut0_unitaryfType := UnitaryfType Ut0_unitary.
Let Us_unitary : Us \is unitarylf.
Proof. by rewrite Us_diffE unitaryf_unitary. Qed.
Local Canonical Us_unitaryfType := UnitaryfType Us_unitary.

Definition Grover_sub :=
  [ut x := Uw];;
  [ut x := 'Hn^A];;
  [ut x := Ut0];;
  [ut x := 'Hn].

Definition Grover (r : nat) :=
  [it x := ''t0 ];;
  [ut x := 'Hn ];;
  [for i < r do Grover_sub].

Let t := asin (Num.sqrt (#|Pw|%:R / #|T|%:R) : R).
Let cos2Dsin2c : (cos t ^+ 2)%:C + (sin t ^+2 )%:C = 1.
Proof. by rewrite -realcD cos2Dsin2. Qed.
Let sin2t : (sin t ^+2 )%:C = #|Pw|%:R / #|T|%:R.
Proof.
rewrite /t asinK; last first.
by rewrite sqr_sqrtr ?realcM ?realcI ?natrC// divr_ge0.
rewrite itv_boundlr/= /<=%O/=; apply/andP; split.
by apply: (le_trans (lerN10 _)); rewrite sqrtr_ge0.
by rewrite -{3}sqrtr1; apply/ler_wsqrtr; rewrite ler_pdivr_mulr 
  ?ihb_card_gtr0// mul1r ler_nat max_card.
Qed.
Let sint_neq0 : (sin t) != 0.
Proof.
rewrite -sqrf_eq0 -eqcR sin2t; apply/lt0r_neq0; apply divr_gt0;
by rewrite ?ihb_card_gtr0// ltr0n; move: card_Pw=>/andP[].
Qed.
Let cos2t : (cos t ^+ 2)%:C = (#|T|%:R - #|Pw|%:R) / #|T|%:R.
Proof.
rewrite mulrBl mulfV ?ihb_card_neq0// -sin2t; apply/subr0_eq.
by rewrite opprB addrA -realcD cos2Dsin2 subrr.
Qed.
Let cost_neq0 : cos t != 0.
Proof.
rewrite -sqrf_eq0 -eqcR cos2t; apply/lt0r_neq0; apply divr_gt0;
by rewrite ?ihb_card_gtr0// subr_gt0 ltr_nat; move: card_Pw=>/andP[].
Qed.

Let vw := (sqrtC #|T|%:R)^-1 *: \sum_(i | Pw i) ''i.
Let vwc := (sqrtC #|T|%:R)^-1 *: \sum_(i | ~~ Pw i) ''i.
Lemma us_vwE : us = vw + vwc.
Proof. by rewrite uniformtvE /vw /vwc (bigID Pw)/= scalerDr. Qed.
Lemma vw_vwc_dot : [<vw ; vwc >] = 0.
Proof.
rewrite /vw /vwc dotpZl dotpZr dotp_suml big1 ?mulr0// =>i Pi;
by rewrite dotp_sumr big1// =>j; rewrite onb_dot; case: eqP=>// <-; rewrite Pi.
Qed.
Lemma vw_dot : [<vw ; vw >] = (sin t ^+ 2)%:C.
Proof.
rewrite /vw dotpZl dotpZr mulrA geC0_conj ?invr_ge0 ?sqrtC_ge0// -invfM -expr2 sqrtCK 
  sin2t [RHS]mulrC; f_equal; rewrite dotp_suml (eq_bigr (fun=>1)) ?sumr_const// =>i Pi.
by rewrite dotp_sumr (bigD1 i)//= big1=>[j/andP[_]/negPf/eqsymPf Pj|]; rewrite onb_dot ?Pj// eqxx addr0.
Qed.
Lemma vwc_dot : [<vwc ; vwc >] = (cos t ^+ 2)%:C.
Proof.
move: (ns_dot [NS of us]); rewrite/= us_vwE dotpD vw_vwc_dot vw_dot conjC0 !addr0=>/eqP.
by rewrite eq_sym addrC -subr_eq=>/eqP<-; rewrite -cos2Dsin2c addrK.
Qed.
Lemma Uw_vw : Uw vw = - vw.
Proof.
rewrite /vw !linearZ/=; f_equal; rewrite !linear_sum; apply eq_bigr=>i Pi.
by rewrite/= PhOracleEt Pi expr1z scaleN1r.
Qed.
Lemma Uw_vwc : Uw vwc = vwc.
Proof.
rewrite /vwc !linearZ/=; f_equal; rewrite !linear_sum; apply eq_bigr=>i/negPf Pi.
by rewrite/= PhOracleEt Pi expr0z scale1r.
Qed.

Let uw (r : R) := ((sin r / sin t)%:C *: vw + (cos r / cos t)%:C *: vwc).

Lemma UsUwE_ind (r : R) : (Us \o Uw) (uw r) = uw (r + t *+ 2).
Proof.
rewrite lfunE/= linearP/= Uw_vw scalerN [Uw _]linearZ/= Uw_vwc /Us us_vwE lfunE/= !lfunE/= lfunE/=.
rewrite outpE dotpDr dotpNr dotpZr (dotpZr (_%:C)) !dotpDl vw_dot -conj_dotp !vw_vwc_dot vwc_dot conjC0.
rewrite addr0 add0r scalerA scalerDr opprD opprK addrACA -scalerDl -[_ - _ *: vwc]scalerBl /uw.
do ? f_equal; simpc2r; f_equal; rewrite !expr2 mulrACA mulVf// mulrACA mulVf//;
rewrite !mulr1 mulr_natl mulrnDl.
rewrite /uw sinD cos2x_sin sin2x addrC mulrDl mulrBr mulrBl mulr1 addrA [sin t * _]mulrC; do 2 f_equal.
3: rewrite cosD cos2x_cos sin2x mulrBr mulr1 [in RHS]addrC mulrDl mulrBl addrA; do 2 f_equal.
all: by rewrite -[in RHS]mulr_natl ?mulNr -!mulrA  ?mulfV// mulr1 mulr_natl mulrnAr// mulNrn.
Qed.

Lemma unitaryf_sym (V : chsType) (U : 'FU(V)) u v : (U^A u == v) = (U v == u).
Proof.
by apply/eqb_iff; rewrite !eq_iff; split=><-; 
rewrite -comp_lfunE ?unitaryf_form ?unitaryf_formV lfunE.
Qed.
Lemma UsUwEV_ind (r : R) : (Us \o Uw)^A (uw r) = (uw (r - t *+ 2)).
Proof. by apply/eqP; rewrite unitaryf_sym/= UsUwE_ind addrNK. Qed.

Let vw_uw : vw = (sin t)%:C *: uw (pi/2%:R).
Proof. by rewrite /uw cos_pihalf sin_pihalf mul0r scale0r addr0 scalerA mul1r -realcM mulfV// scale1r. Qed.

Lemma RS_Grover_sub (n : nat) : 
  ⊨s [pt,st] { ｜uw (pi/2%:R - t *+ 2 *+ n);x〉 } 
    [for i < n do Grover_sub]
      { ｜(sin t)%:C ^-1 *: vw ; x〉 }.
Proof.
elim: n=>[|n IH].
rewrite big_ord0 mulr0n subr0 vw_uw scalerA -realcI -realcM mulVf// scale1r; exact: AxS_Sk.
rewrite big_ord_recl; apply: (RS_SC _ _ (IH)); rewrite /Grover_sub.
do 3 (apply: (RS_SC _ _ (AxV_UT _)); rewrite/= tf2f_adj tlin_ket).
apply: (RS_back _ (AxV_UT _)).
rewrite/= tf2f_adj tlin_ket -!comp_lfunE -!adjf_comp !comp_lfunA.
by rewrite -Us_diffE UsUwEV_ind -addrA -opprD -mulrSr.
Qed.

Lemma RS_Grover (n : nat) : 
  ⊨s [pt,st] { (cos (pi / 2%:R - t *+ (2 * n + 1)))%:C *: |1 } 
    (Grover n) { ｜(sin t)%:C ^-1 *: vw;x〉 }.
Proof.
rewrite /Grover. apply: (RS_SC _ _ (RS_Grover_sub _)).
apply: (RS_SC _ _ (AxV_UT _)).
rewrite/= tf2f_adj tlin_ket -[SPOST]tenq1.
apply: (RS_back _ (tAxV_In _ )).
rewrite /= adj_dotEV VUnitaryE/=.
set tx := (pi / 2%:R - t *+ 2 *+ n).
rewrite /uw us_vwE dotpDr dotpZr dotpDl vw_dot -conj_dotp vw_vwc_dot conjC0.
rewrite dotpZr dotpDl vw_vwc_dot vwc_dot addr0 add0r; simpc2r.
rewrite !expr2 mulrACA mulVf// mulrACA mulVf// !mulr1 addrC -cosB.
by rewrite /tx -addrA -opprD -mulrnA -mulrSr addn1.
by rewrite disjointX0.
Qed.

Let solution := (\sum_(i | Pw i) [> ''i ; ''i <]).
Lemma solution_proj : solution \is projlf.
Proof.
apply/projlfP; split.
by rewrite /solution raddf_sum/=; under eq_bigr do rewrite adj_outp.
rewrite /solution linear_suml/=; apply eq_bigr=>i Pi.
rewrite linear_sumr/= (bigD1 i)//= big1=>[j/andP[] _/negPf nj|];
by rewrite outp_comp ?ns_dot ?scale1r ?addr0// onb_dot eq_sym nj scale0r.
Qed.

Lemma R_Grover (n : nat) : 
  ⊨ [pt] { ((sin (t *+ (2 * n + 1)))^+2)%:C%:QE } 
    (Grover n) { ⌈(\sum_(i | Pw i) [> ''i ; ''i <]);x⌉ }.
Proof.
move: (RS_Grover n)=>/saturated_weakS.
rewrite stateE; apply: R_Or.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
rewrite adjqZ comqZl comqZr conjC_real scalerA cplx_adj cplxM conjC1 mulr1 cplxZ mulr1
  -realcM -expr2/=; do 3 f_equal.
by rewrite [in RHS]addrC cosDpihalf sinN opprK.
rewrite ket_adj touterM/= lin_lef tf2f_lef -/solution.
have ->: solution = HSType (ProjfType solution_proj) by rewrite hsE/=.
apply lef_outp.
rewrite hnorm_le1 dotpZl dotpZr vw_dot -!real2c conjC_real -!real2c
  mulrA -invfM -expr2 mulVf// expf_neq0//.
apply: memhZ; rewrite memhE hsE/= /vw/solution !linear_sum/=.
by apply/eqP; apply eq_bigr=>i Pi; rewrite linearZ/=; f_equal; 
  rewrite sum_lfunE (bigD1 i)//= big1=>[j/andP[] _/negPf nj|]; 
  rewrite outpE onb_dot ?nj ?scale0r// eqxx scale1r addr0.
Qed.

End GroverAlgorithm.

Section PhaseEstimation.
Variable (pt st : bool) (T : ihbFinType) (U : 'FU('Hs T)) (phi : 'Hs T) (theta : R).
(* since 'End[T] is a ringType, exp can be directly written as ^+ *)
Hypothesis (eigU : U phi = (expip (2%:R * theta) *: phi)).
Hypothesis (theta_bound : 0 <= theta < 1).
Variable (n : nat). (* control system *)
Variable (x : vars 'I_n.+1) (y : vars T).
Hypothesis (nxy : [disjoint lb x & lb y]).
Let eigUn m : (U%:VF ^+ m)^A phi = expip (- (2%:R * theta * m%:R)) *: phi.
Proof.
apply/eqP; rewrite unitaryf_sym/= linearZ/=.
elim: m=>[|m/eqP IH]; first by rewrite expr0 lfunE/= mulr0 oppr0 expip0 scale1r.
by rewrite -{2}IH exprSr lfunE/= eigU linearZ/= scalerA -expipD 
  -[m.+1]addn1 natrD mulrDr mulr1 opprD addrNK.
Qed.
Let Uf_fun := (fun i : 'I_n.+1 => U%:VF ^+ i).
(* Uf is a Multiplexer *)
Let Uf := Multiplexer Uf_fun.

Definition QPE :=
  [it x := ''ord0 ];;
  [ut x := 'Hn ];;
  [ut [x,y] := Uf ];;
  [ut x := IQFT ].

Let c (a : 'I_n.+1) := (\sum_(i < n.+1) expip (2%:R * (a%:R / n.+1%:R - theta) * i%:R)) / n.+1%:R.

Lemma RS_QPE (a : 'I_n.+1) : 
  ⊨s [pt,st] { c a *: ｜phi;y〉 } QPE { ｜''a;x〉 ⊗ ｜phi;y〉 }.
Proof.
apply: (RS_SC _ _ (AxV_UT _)).
rewrite /= tf2f_adj adjfK tlin_ketTl//=.
apply: (RS_SC _ _ (AxV_UT _)).
rewrite/= tf2f2cE// tf2f2_adj tketT tlin_ket//.
apply: (RS_SC _ _ (AxV_UT _)).
rewrite/= QFTEt QFTvE tentvZl tentv_suml linearZ/= linear_sum/= -tketZ -tket_sum dotqZr dotq_sumr.
under eq_bigr do rewrite tentvZl linearZ/= MultiplexerEVt /Uf_fun eigUn tentvZr 
  scalerA -tketZ dotqZr tf2f_adj -tketT (t1lin_ketTl _ _ _ nxy)/= -tenqZl tketZ.
rewrite -tenq_suml -tenqZl tket_sum [in SPOST]tketZ.
apply: (RS_back _ (tAxV_In _ ))=>//.
rewrite/= dotpZr dotp_sumr.
under eq_bigr do rewrite dotpZr adj_dotEV VUnitaryE/= dotp_uniformtvcb card_ord
  runityE -expipD natrM -!mulrA -mulrBr [_ / n.+1%:R]mulrC mulrA -mulrBl mulrA.
by rewrite -mulr_suml mulrC -mulrA -invfM -expr2 sqrtCK.
Qed.

Lemma RS_QPE_exact (a : 'I_n.+1) : 
  a%:R = theta * n.+1%:R ->
  ⊨s [pt,st] { ｜phi;y〉 } QPE { ｜''a;x〉 ⊗ ｜phi;y〉 }.
Proof.
move=>P1; move: (RS_QPE a); 
by rewrite /c expip_sum_cst ?P1 ?mulfK ?mulfV/= ?scale1r// subrr mulr0 expip0.
Qed.

Lemma foo1 a : `|1 - expip (2%:R * a)| = 2%:R * `|sin (pi * a)|%:C.
Proof.
have ->: 2%:R * `|sin (pi * a)|%:C = `|2%:R * sinp a|%:C.
by rewrite unlock normrM ger0_norm// realcM natrC.
rewrite !unlock /expi; simpc; f_equal.
rewrite sqrrN sqrrB -!addrA cos2Dsin2 expr1n mul1r addrC -addrA -mulr2n addrC.
rewrite -mulrnBl mulrC -mulrA [in LHS]mulr_natl cos2x_sin opprB addrC addrNK.
by rewrite -mulr_natl -(mulr_natl (_ * _)) mulrA -expr2 -exprMn sqrtr_sqr (mulrC a).
Qed.

Let foo5 a : a%:R - theta * n.+1%:R =  (a%:R / n.+1%:R - theta) * n.+1%:R.
Proof. by rewrite mulrBl mulfVK//. Qed.

Lemma c_approx (a : 'I_n.+1) : 
  `| a%:R - theta * n.+1%:R | <= ((2%:R)^-1)%R -> 
    `|c a| >= (2%:R / pi)%:C.
Proof.
rewrite /c; case E: (a%:R / n.+1%:R - theta == 0).
rewrite expip_sum_cst=>[|_].
by move: E=>/eqP->; rewrite mulr0 expip0.
by rewrite mulfV ?natrS_neq0// normr1 lecR1 ler_pdivr_mulr ?pi_gt0// mul1r pi_ge2.
move: E; rewrite foo5; set t := a%:R / n.+1%:R - theta; move=>P1 P2.
have P4: `|t| <= (2%:R^-1)%R.
by apply: (le_trans _ P2); rewrite normrM ler_pemulr// ger0_norm// ler1n.
have P5: `|t| < 1 by apply: (le_lt_trans P4); rewrite invf_lt1 ?ltr0n// ltr1n.
have P6 : `|pi * t| <= pi / 2%:R by rewrite normrM ger0_norm ?pi_ge0// ler_pmul2l// ?pi_gt0.
have P7 : `|pi * (t * n.+1%:R)| <= pi / 2%:R.
  by rewrite normrM ger0_norm ?pi_ge0// ler_pmul2l// ?pi_gt0.
rewrite expip_sum.
apply/expip_neq1; rewrite ?mulf_eq0 ?negb_or ?P1 ?andbT// !normrM 
  ger0_norm// gtr_pmulr// ltr0n//.
rewrite !normrM !normfV -[_ * t * _]mulrA !foo1 [2%:R * _%:C]mulrC invfM mulrA mulfK//.
rewrite -natrC -realc_norm; simpc2r; rewrite lecR.
rewrite ler_pdivl_mulr ?normr_gt0// ler_pdivl_mulr.
apply: (lt_le_trans _ (ger_abs_sin P6)); rewrite !mulr_gt0// ?normrM 
  1?gtr0_norm ?mulr_gt0// ?invr_gt0 ?pi_gt0// normr_gt0 P1//.
apply: (le_trans _ (ger_abs_sin P7)). rewrite -!mulrA ler_pmul2l ?ltr0n// mulrC ler_pmul2r 
  ?invr_gt0 ?pi_gt0// mulrA normrM mulrC ler_pmul2r ?ler_abs_sin// gtr0_norm ltr0n//.
Qed.

End PhaseEstimation.

Section FinGroupPartition.
Variable (T : Type) (zero one : T).
Variable (gT : finGroupType).

Lemma cardg_gt0 : (0 < #|gT|)%N.
Proof. by apply/card_gt0P; exists 1%g; rewrite inE. Qed.

Lemma big_rcoset (op : Monoid.com_law one) (H : {group gT}) (f : gT -> T) (j : {set gT}) :
  j \in [set rcoset H x | x : gT] ->
    (\big[op/one]_(i | rcoset H i == j) f i = 
      \big[op/one]_(i in H) f (i * (repr j))%g)%R.
Proof.
move=>/imsetP[x Px1 Px2].
rewrite (reindex (fun i=> i * repr j)%g).
exists (fun i=>i * (repr j)^-1)%g.
by move=>y _; rewrite -mulgA mulgV mulg1.
by move=>y _; rewrite -mulgA mulVg mulg1.
move: Px2; rewrite rcosetE=>Px2. apply eq_bigl=>y.
rewrite rcosetE; apply/Bool.eq_iff_eq_true; split.
move=>/eqP.
rewrite Px2 -{2}[(H :* x)%g]rcoset_repr.
set t := repr (H :* x)%g =>P.
suff : (y * t * t^-1)%g \in H by rewrite -mulgA mulgV mulg1.
by rewrite -mem_rcoset -P mem_rcoset mulgV group1.
move=>Py. apply/eqP.
by rewrite rcosetM rcoset_id// Px2 rcoset_repr.
Qed.

Lemma big_rcoset_partition (op : Monoid.com_law one) (f : gT -> T) (H : {group gT}) : 
  (\big[op/one]_i (f i) = 
    \big[op/one]_(j in [set rcoset H x | x : gT]) 
      \big[op/one]_(i in H) f (i * (repr j))%g)%R.
Proof.
rewrite (partition_big_imset (rcoset H)) /=.
by apply eq_bigr=>i Pi; rewrite big_rcoset.
Qed.
Global Arguments big_rcoset_partition [op f].

Lemma eq_imsetr (aT rT : finType) (f : aT -> rT) (D1 D2 : {pred aT}) : 
  D1 =i D2 -> [set f x | x in D1] = [set f x | x in D2].
Proof.
by move=>P1; apply/setP=>x; apply/eqb_iff; split=>/imsetP[y P2 P3]; 
  apply/imsetP; exists y=>//; rewrite ?P1// -P1.
Qed.

Lemma LagrangeA (H : {group gT}) :
  (#|H| * #|[set rcoset H x | x : gT]|)%N = #|gT|.
Proof.
move: (subsetT H)=>/Lagrange; rewrite cardsT /indexg /rcosets=><-.
by do 4 f_equal; apply eq_imsetr=>i; rewrite !inE.
Qed.

End FinGroupPartition.

Section dffun_group.
Variable (n : nat) (fn : 'I_n.+1 -> nat).
Notation ZZ := {dffun forall i : 'I_n.+1, ('I_(fn i).+2)}.
Definition ZZ0 : ZZ := [ffun i => 0].
Definition ZZ_add (f g : ZZ) : ZZ := [ffun i => f i + g i].
Definition ZZ_opp (f : ZZ) : ZZ := [ffun i => - f i].

Lemma ZZ_add0z : left_id ZZ0 ZZ_add.
Proof. by move=>f; apply/ffunP=>i; rewrite !ffunE add0r. Qed.

Lemma ZZ_addNz : left_inverse ZZ0 ZZ_opp ZZ_add.
Proof. by move=>f; apply/ffunP=>i; rewrite !ffunE addNr. Qed.

Lemma ZZ_addA : associative ZZ_add.
Proof. by move=>f g h; apply/ffunP=>i; rewrite !ffunE addrA. Qed.

Lemma ZZ_addC : commutative ZZ_add.
Proof. by move=>f g; apply/ffunP=>i; rewrite !ffunE addrC. Qed.

Definition ZZ_zmodMixin := ZmodMixin ZZ_addA ZZ_addC ZZ_add0z ZZ_addNz.
Canonical ZZ_zmodType := Eval hnf in ZmodType ZZ ZZ_zmodMixin.
Canonical ZZ_finZmodType := Eval hnf in [finZmodType of ZZ].
Canonical ZZ_baseFinGroupType := Eval hnf in [baseFinGroupType of ZZ for +%R].
Canonical ZZ_finGroupType := Eval hnf in [finGroupType of ZZ for +%R].
(* Local Notation ZZ' := ZZ_finGroupType. *)

Definition charZZ (x y : ZZ) := 
    \prod_k expip (2%:R * (x k)%:R * (y k)%:R / (fn k).+2%:R).
Lemma charZZ_D (x y z : ZZ) :
  charZZ x y * charZZ x z = charZZ x (y + z).
Proof.
rewrite /charZZ -big_split/=; apply eq_bigr=>i _.
rewrite -expipD {2}/GRing.add/= ffunE{2}/GRing.add/=.
rewrite -mulrDl -mulrDr -natrD {1}(divn_eq (y i + z i) (fn i).+2).
rewrite natrD mulrDr mulrDl expipD natrM -!mulrA mulfV ?natrS_neq0// mulr1.
by rewrite -!natrM expip2n mul1r.
Qed.
Lemma charZZ_C (x y : ZZ) :
  charZZ x y = charZZ y x.
Proof.
rewrite /charZZ; apply eq_bigr=>i _; do 2 f_equal.
rewrite -!mulrA; f_equal; exact: mulrC.
Qed.

Lemma charZZ_sum_eq0 (H : {group ZZ}) (x : ZZ) :
  (exists h : ZZ, h \in H /\ charZZ x h != 1) ->
  \sum_(i in H) charZZ x i = 0.
Proof.
move=>[h [Ph1 /negPf Ph2]].
have: charZZ x h * (\sum_(i in H) charZZ x i) = \sum_(i in H) charZZ x i.
rewrite mulr_sumr; under eq_bigr do rewrite charZZ_D.
rewrite [RHS](reindex (fun x => h + x)); last first.
apply eq_bigl=>y; apply/eqb_iff; split=>P.
by move: (groupM Ph1 P).
move: (groupM (groupVr Ph1) P).
by rewrite/invg/=/mulg/= addrA addNr add0r.
exists (fun x => - h + x)=>y _; by rewrite addrA ?(addNr, addrN) add0r.
by move/eqP; rewrite -[X in _ == X]mul1r -subr_eq0 -mulrBl mulf_eq0 subr_eq0 Ph2/==>/eqP.
Qed.

End dffun_group.

(* Section lfunsemExtra.
Context (L : finType) (H : L -> chsType).

Lemma com1q S (e : {bra H | S}) : |1 ∗ e = e.
Proof. by rewrite -dotq_com/= dot1q. Qed.
Lemma comq1 S (e : {ket H | S}) : e ∗ |1 = e.
Proof. by rewrite -dotq_com/= dotq1. Qed.

End lfunsemExtra. *)

Section HSP.
Variable (n : nat) (fn : 'I_n.+1 -> nat).
Variable (x : forall i, vars ('I_(fn i).+2)).
Hypothesis (disx : forall i j, i != j -> [disjoint lb (x i) & lb (x j)]).
Notation px := (pvars_dffun disx).
Notation G := {dffun forall i : 'I_n.+1, ('I_(fn i).+2)}.
Variable (H : {group G}). (* provide a group *)
Variable (X : finZmodType) (ff : G -> X) (y : vars X). (* auxiliary system, oracle *)
Hypothesis (disy : [disjoint lb (pvars_dffun disx) & lb y]).
Hypotheses (Hff_eq : forall (i j : G), (i \in (H :* j)%g) <-> ff i = ff j).

Definition tau (t : {set G}) :=
  \sum_(i : G) [> ''(i + repr t) ; ''i <].

Definition phi (t : {set G}) :=
  \sum_(i : G) charZZ i (repr t) *: [> ''i ; '' i <].

Definition HC := [set i : G | [forall h, ~~ (h \in H) || (charZZ i h == 1)]].
Lemma HC_inP i : reflect (forall h, h \in H -> charZZ i h = 1) (i \in HC).
Proof.
apply/(iffP idP).
by rewrite inE=>/forallP P h hH; move: (P h); rewrite hH/==>/eqP.
move=>P; rewrite inE; apply/forallP=>h.
by case E: (h \in H)=>//=; apply/eqP/P.
Qed.

Definition H_state :=
  (sqrtC #|H|%:R)^-1 *: \sum_(i in H) ''i.

Definition HC_state :=
  (sqrtC (#|H|%:R / #|G|%:R)) *: \sum_(i in HC) ''i.

Definition FG := (sqrtC #|G|%:R)^-1 *: \sum_(i : G)\sum_j charZZ i j *: [> ''i ; '' j <].

Lemma FG_apply j : FG ''j = (sqrtC #|G|%:R)^-1 *: \sum_i charZZ i j *: ''i.
Proof.
rewrite /FG lfunE/= sum_lfunE/=; f_equal; apply eq_bigr=>i _.
rewrite sum_lfunE (bigD1 j)//= big1=>[k/negPf nk|];
by rewrite lfunE/= outpE ?ns_dot ?onb_dot ?nk ?scale0r ?scaler0// scale1r addr0.
Qed.

Lemma QFT_FG_apply : tentf_dffun (fun j=> QFT) = FG.
Proof.
apply /(intro_onb t2tv_onbasis)=>i; apply/(intro_onbl t2tv_onbasis)=>j.
rewrite/= ![in LHS]t2tv_dffun FG_apply tentf_dffun_apply tentv_dffun_dot.
rewrite dotpZr dotp_sumr (bigD1 j)//= [in RHS]big1=>[k/negPf nk|];
rewrite dotpZr ?ns_dot ?onb_dot 1?eq_sym ?nk ?mulr0// addr0 mulr1.
under eq_bigr do rewrite QFTEt dotp_cbQFT.
rewrite big_split/= -invf_prod -sqrt_prod=>[k _//|].
rewrite -natr_prod card_dffun; under [in RHS]eq_bigr do rewrite card_ord.
by f_equal; apply eq_bigr=>k _; rewrite runityE mulnC natrM mulrA.
Qed.

Let FG_unitary : FG \is unitarylf.
Proof. by rewrite -QFT_FG_apply unitaryf_unitary. Qed.
Local Canonical FG_unitaryfType := UnitaryfType FG_unitary.

Let cardH : #|H|%:R != 0 :> C.
Proof. by rewrite pnatr_eq0 lt0n_neq0// cardG_gt0. Qed.
Let cardZZ : #|G|%:R != 0 :> C.
Proof. rewrite pnatr_eq0 lt0n_neq0//; by move: (cardg_gt0 [finGroupType of G]). Qed.

Lemma FG_H_state : FG H_state = HC_state.
Proof.
rewrite/H_state linearZ linear_sum/=; under eq_bigr do rewrite FG_apply.
rewrite -linear_sum/= exchange_big/= (big_setIDx HC)/=.
rewrite (eq_bigr (fun i=>#|H|%:R *: ''i))=>[i /HC_inP P|].
by rewrite (eq_bigr (fun=>''i))=>[j/P->|]; rewrite ?scale1r// sumr_const scaler_nat.
rewrite [X in _ + X]big1=>[i Pi|].
rewrite -scaler_suml charZZ_sum_eq0 ?scale0r//; move: Pi.
rewrite inE not_existsP=>/negP; apply contra_not=>P; apply/HC_inP=>j Pj.
by move: (P j); rewrite -implyNE=>/(_ Pj)/negP; rewrite negbK=>/eqP.
rewrite addr0 -linear_sum/= !scalerA /HC_state; f_equal. 
rewrite -{2}(sqrtCK #|H|%:R) expr2 mulrACA mulVf ?sqrtC_eq0//
  mul1r sqrtCM// 1?mulrC// ?sqrtC_inv// nnegrE invr_ge0//.
Qed.

Lemma FG_tauC (t : {set G}) : FG \o (tau t) = (phi t) \o FG.
Proof.
rewrite /FG linearZl linearZr/=; f_equal.
rewrite /tau {1}exchange_big/= linear_sumr/= [LHS](eq_bigr (fun i=>
phi t \o (\sum_j charZZ j i *: [> ''j ; ''i <]) ))=>[i _|]; last first.
by rewrite -linear_sumr [in LHS]exchange_big/=.
rewrite exchange_big linear_suml [RHS]linear_sumr/=; apply eq_bigr=>j _.
rewrite [LHS]linear_suml (bigD1 (i + repr t))//= big1=>[k/negPf nk|];
rewrite linearZl/= outp_comp ?ns_dot ?onb_dot ?nk ?scale0r ?scaler0//.
rewrite addr0 scale1r /phi linear_suml/= (bigD1 j)//= big1=>[k/negPf nk|];
rewrite linearZl linearZr/= outp_comp ?ns_dot ?onb_dot ?nk ?scale0r ?scaler0//.
by rewrite addr0 scale1r scalerA -charZZ_D mulrC.
Qed.

Lemma Phi_HC_state (t : {set G}) : phi t HC_state = 
  (sqrtC (#|H|%:R / #|G|%:R)) *: \sum_(i in HC) charZZ i (repr t) *: ''i.
Proof.
rewrite /HC_state linearZ/= linear_sum; f_equal; apply eq_bigr=>i Pi.
rewrite /phi/= sum_lfunE (bigD1 i)//= big1=>[j/negPf nj|];
by rewrite lfunE/= outpE ?ns_dot ?onb_dot ?nj ?scale0r ?scaler0// scale1r addr0.
Qed.

Notation t0 := (witness X : X).

Definition HSP :=
  [for i do [it x i := ''ord0 ]];;
  [it y := ''t0 ];;
  [for i do [ut x i := QFT ]];;
  [ut [px, y] := Oracle ff ];;
  [for i do [ut x i := QFT ]].

Lemma inr i : i \in [set rcoset H x0 | x0 : G] -> (i = H :* (repr i))%g.
Proof. by move/imsetP=>[z Pz Pi]; rewrite Pi rcosetE rcoset_repr . Qed.

Let i0 := [ ffun i : 'I_n.+1 => ord0] : {dffun forall i : 'I_n.+1, 'I_(fn i).+2}.
Let Di0 i : charZZ i i0 = 1.
Proof. by rewrite/charZZ big1// =>k _; rewrite ffunE mulr0 mul0r expip0. Qed.

Let vf := (#|H|%:R / #|G|%:R) *: (\sum_(j in HC) (''j ⊗t 
    \sum_(i in [set rcoset H x0 | x0 : {dffun forall i1 : 'I_n.+1, 'I_(fn i1).+2}]) 
       (charZZ j (repr i) *: ''(t0 + ff (repr i))))).

Lemma test : (FG ⊗f \1) (Oracle ff ((FG ⊗f \1) (''i0 ⊗t ''t0))) = vf.
Proof.
rewrite tentf_apply FG_apply lfunE/= tentvZl tentv_suml !linearZ/= linear_sum/=.
rewrite (big_rcoset_partition H)/= /vf (eq_bigr (fun j=> (sqrtC #|H|%:R) *: 
  ((tau j H_state) ⊗t ''(t0 + ff (repr j))) )).
move=>i /inr P1; rewrite /H_state linearZ/= tentvZl scalerA mulfV ?sqrtC_eq0//
 scale1r linear_sum/= tentv_suml; apply eq_bigr=>k inK.
rewrite Di0 scale1r OracleEt; do 3 f_equal.
by rewrite /tau sum_lfunE (bigD1 k)//= big1=>[j/negPf nj|]; 
  rewrite outpE ?ns_dot ?onb_dot ?nj ?scale0r// scale1r addr0.
by apply/Hff_eq/rcoset_eqP; rewrite rcosetM rcoset_id.
under [in RHS]eq_bigr do rewrite tentv_sumr.
rewrite exchange_big/= !linear_sum; apply eq_bigr=>i _/=.
rewrite linearZ/= tentf_apply -comp_lfunE FG_tauC !lfunE/= FG_H_state.
rewrite Phi_HC_state tentvZl !scalerA tentv_suml; f_equal.
by rewrite sqrtC_inv// -sqrtCM ?nnegrE// ?invr_ge0// [_^-1 * _]mulrC -expr2 sqrtCK.
by under eq_bigr do rewrite tentvZS.
Qed.

Lemma unitaryf_norm (U : chsType) (f : 'FU(U)) (v : U) :
  `|f v| = `|v|.
Proof.
by move: (unitaryf_unitary f)=>/unitarylf_dotP/(_ v)/eqP;
rewrite !dotp_norm eqr_expn2// =>/eqP.
Qed.

Lemma ortho_norm (U : chsType) (I : finType) (P : pred I) (F : I -> U):
  (forall i j, P i -> P j -> i != j -> [<F i; F j>] = 0) ->
  `| \sum_(i | P i) F i| ^+ 2 = \sum_(i | P i) `|F i| ^+ 2.
Proof.
move=>P1; rewrite -dotp_norm dotp_suml; apply eq_bigr=>i Pi.
rewrite dotp_sumr (bigD1 i)//= big1 ?addr0 ?dotp_norm//.
move=>j/andP[Pj/negPf nj]; by rewrite P1// eq_sym nj.
Qed.

Lemma expip_norm r : `|expip r| = 1.
Proof. by rewrite normC_def -expipNC -expipD subrr expip0 sqrtC1. Qed.

Lemma charZZ_norm (i j : G) : `|charZZ i j| = 1.
Proof. by rewrite /charZZ normr_prod big1// =>k _; rewrite expip_norm. Qed.

Let H_rcoset_card : 
  #|[set rcoset H x0 | x0 : G]|%:R = #|G|%:R / #|H|%:R :> C.
Proof. by apply/(@mulfI _ #|H|%:R)=>//; rewrite -natrM mulrC mulfVK// LagrangeA. Qed.

Lemma Hff_neq (j k : {set G}) :
  j = (H :* repr j)%g -> k = (H :* repr k)%g -> j != k ->
  ff (repr j) == ff (repr k) = false.
Proof.
move=>Pj Pk njk; case: eqP=>[/Hff_eq/rcoset_eqP|//].
by rewrite -Pj -Pk=>P1; move: njk; rewrite P1 eqxx.
Qed.

Lemma vf_norm1 : `|vf| = 1.
Proof. by rewrite -test !unitaryf_norm tentv_t2tv ns_norm. Qed.

Lemma cardHC : #|HC|%:R = #|G|%:R / #|H|%:R :> C.
Proof.
move: vf_norm1=>/(f_equal (fun x=>x^+2)).
rewrite expr1n normrZ exprMn ortho_norm=>[i j _ _ /negPf ni|].
by rewrite tentv_dot onb_dot ni mul0r.
rewrite (eq_bigr (fun=>#|G|%:R / #|H|%:R))=>[i Pi|].
rewrite tentv_norm ns_norm mul1r ortho_norm=>[j k/inr Pj/inr Pk njk|].
by rewrite dotpZl dotpZr onb_dot (can_eq (addKr t0)) Hff_neq// !mulr0.
under eq_bigr do rewrite normrZ charZZ_norm mul1r ns_norm expr1n.
by rewrite sumr_const H_rcoset_card.
rewrite sumr_const -[_ *+ #|HC|]mulr_natl ger0_norm ?divr_ge0// mulrC expr2.
rewrite !mulrA mulfVK// mulfK// -[X in _ -> _ = X]mulr1=>P1.
rewrite -{4}P1 [RHS]mulrC !mulrA mulfVK// mulfK//.
Qed.

Lemma RS_HSP pt st : ⊨s [pt,st] { |1 } HSP { ｜vf ; (px, y)〉}.
Proof.
have: true by []. rewrite /HSP -!fsem_seqA=>_.
apply: (RS_SC _ (tAxV_InFP_seq _ _ _))=>[++ _ _|//||]; rewrite ?disjoint0X//=.
apply: (RS_SC _ (tAxV_InF _))=>/=.
by rewrite setU0 disjoint_sym disy.
apply: (RS_SC _ (AxV_UTFP _))=>//=.
rewrite tenq1 -pvarsEt_cst -pvarsEf -/i0 tenqC QFT_FG_apply (tketT px) tketGl//.
apply: (RS_SC _ (AxV_UTF _))=>//=.
rewrite tf2f2cE// ?(t2lin_ketG (x1 := px))//.
apply: (RS_forward _ (AxV_UTFP _))=>//=.
by rewrite -pvarsEf QFT_FG_apply tketGl ?test.
Qed.

Let HSP_no_while : no_while HSP.
Proof. by rewrite/= !no_while_for. Qed.

Lemma R_HSP_notin pt st i : 
  i \notin HC -> ⊨ [pt,st] { 0 } HSP { ⌈ [> ''i ; ''i <] ; px ⌉ }.
Proof.
move=>Pi; apply/no_while_enough=>//.
move: (RS_HSP true true); rewrite stateE cplx_adj cplxM conjC1 mulr1 ket_adj touterM=>IH.
apply: (R_back _ (tR_PInnerl disy ''i _ IH)); last by rewrite vf_norm1.
rewrite big1 ?cplx0// =>j _; rewrite /vf linearZ/= linear_sumr/= big1=>[k nk|].
by rewrite tentv_dot onb_dot; move: Pi=>/memPnC/(_ _ nk)/negPf->; rewrite mul0r.
by rewrite mulr0 normr0 expr0n.
Qed.

Definition PX (i : X) := 
  [exists j, (j \in [set rcoset H x0 | x0 : G]) && (i == (witness X + ff (repr j)))].

Lemma cardPX : #|PX| = #|[set rcoset H x0 | x0 : G]|.
Proof.
suff : #|[finType of {i : X | PX i}]| = #|[finType of {i | i \in [set rcoset H x0 | x0 : G]}]|.
by rewrite !card_sig.
pose H1 (j : {i : X | PX i}) := sigW (existsP (projT2 j)).
have H2 (j : {i : X | PX i}) : projT1 (H1 j) \in [set rcoset H x0 | x0 : G].
by move: (projT2 (H1 j))=>/andP[].
pose fb (j : {i : X | PX i}) : {i | i \in [set rcoset H x0 | x0 : G]} 
  := exist _ (projT1 (H1 j)) (H2 j).
have Ef j : val j = witness X + ff (repr (val (fb j))).
by move: (projT2 (H1 j))=>/andP[] _/eqP.
have Ff j : val (fb j) = (projT1 (H1 j)). by [].
have H3 (j : {i | i \in [set rcoset H x0 | x0 : G]}) : PX (witness X + ff (repr (projT1 j))).
by rewrite/PX; apply/existsP; exists (projT1 j); rewrite eqxx; move: (projT2 j)=>->.
pose gb (j : {i | i \in [set rcoset H x0 | x0 : G]}) : {i : X | PX i}
  := exist _ (witness X + ff (repr (projT1 j))) (H3 j).
have Eg j : val (gb j) = witness X + ff (repr (val j)). by [].
have Fg j : projT1 (gb j) = (witness X + ff (repr (projT1 j))). by [].
apply: (@bij_eq_card _ _ fb).
exists gb. move=>i. apply/val_inj. by rewrite Eg -Ef.
move=>i. apply/val_inj. rewrite Ff.
move: (projT2 (H1 (gb i)))=>/andP[]/inr P1/eqP.
rewrite {1}Fg=>/addrI/Hff_eq/rcoset_eqP; rewrite -P1=><-.
by move: (projT2 i)=>/inr<-.
Qed.

Lemma R_HSP_in pt st i : 
  i \in HC -> ⊨ [pt,st] { ((#|HC|%:R)^-1)%R%:QE } HSP { ⌈ [> ''i ; ''i <] ; px ⌉ }.
Proof.
move=>Pi; apply/no_while_enough=>//.
move: (RS_HSP true true); rewrite stateE cplx_adj cplxM conjC1 mulr1 ket_adj touterM=>IH.
apply: (R_back _ (tR_PInnerl disy ''i _ IH)); last by rewrite vf_norm1.
f_equal. rewrite /vf.
rewrite (eq_bigr (fun i1=> `|#|H|%:R / #|G|%:R *
  (\sum_(v in [set rcoset H x0 | x0 : G]) charZZ i (repr v) * 
    (i1 == (witness X + ff (repr v)))%:R) | ^+ 2)).
move=>j _; rewrite linear_sum/= dotp_sumr (bigD1 i)//= [X in _ + X]big1
  =>[k/andP[] _/negPf nk|]; rewrite dotpZr tentv_dot ?ns_dot ?onb_dot 
  1?eq_sym ?nk ?mul0r ?mulr0// mul1r addr0 dotp_sumr; 
  do 3 f_equal; apply eq_bigr=>v _; by rewrite dotpZr onb_dot.
rewrite (bigID PX)/= [X in _ + X]big1=>[j|].
rewrite/PX negb_exists=>/forallP/==>IH1.
rewrite big1 ?mulr0 ?normr0 ?expr0n// =>k Pk.
by move: (IH1 k); rewrite negb_and Pk/==>/negPf->; rewrite mulr0.
rewrite (eq_bigr (fun i1=>(#|H|%:R / #|G|%:R) ^+ 2))=>[j|].
rewrite /PX=>/existsP=>[[k/andP[Pk jk]]].
rewrite (bigD1 k)//= big1=>[l/andP[Pl/negPf nl]|].
case: eqP; rewrite ?mulr0//; move: jk=>/eqP->/addrI/Hff_eq/rcoset_eqP.
by move: Pk Pl=>/inr<-/inr<- kl; rewrite kl eqxx in nl.
by rewrite jk mulr1 addr0 normrM charZZ_norm mulr1 ger0_norm// divr_ge0.
rewrite addr0 sumr_const cardPX -mulr_natr H_rcoset_card cardHC.
by rewrite invfM invrK expr2 mulrACA mulfVK// mulrAC mulfV// mul1r mulrC.
Qed.

Lemma RS_HSP_notin pt st i t : 
  i \notin HC -> ⊨s [pt,st] { 0 } HSP { ｜''i ⊗t ''t; (px, y)〉}.
Proof.
move=>Pi. apply/no_while_enoughS=>//.
apply: (RS_back _ (t2RV_Inner disy _ _ (RS_HSP true true))).
rewrite /vf dotpZl dotp_suml big1 ?mulr0 ?normr0 ?zero0//  =>j Pj.
rewrite tentv_dot onb_dot eq_sym.
by move: Pi=>/memPnC/(_ _ Pj)/negPf->; rewrite mul0r.
by rewrite vf_norm1.
Qed.

Lemma RS_HSP_in pt st i (t : {set G}): 
  i \in HC -> t \in [set rcoset H x0 | x0 : G] ->
   ⊨s [pt,st] { (#|H|%:R / #|G|%:R)%:QE } HSP { ｜''i ⊗t ''(t0 + ff (repr t)); (px, y)〉}.
Proof.
move=>Pi /inr Pt. apply/no_while_enoughS=>//.
apply: (RS_back _ (t2RV_Inner disy _ _ (RS_HSP true true))).
f_equal. rewrite /vf dotpZl dotp_suml normrM norm_conjC [`|_ / _|]ger0_norm
  ?divr_ge0// -[RHS]mulr1; f_equal.
rewrite (bigD1 i)//= [X in _ + X]big1=>[j/andP[_ /negPf nj]|].
by rewrite tentv_dot onb_dot nj mul0r.
rewrite tentv_dot ns_dot mul1r (bigD1 (rcoset H (repr t)))/=.
by apply/imsetP; exists (repr t).
rewrite dotpDl dotp_suml ?big1=>[j/andP[/inr Pj]|].
rewrite rcosetE -Pt=>nj.
by rewrite dotpZl onb_dot (can_eq (addKr t0)) Hff_neq// !mulr0.
by rewrite rcosetE -Pt dotpZl ns_dot mulr1 !addr0 norm_conjC charZZ_norm.
by rewrite vf_norm1.
Qed.

End HSP.
End CaseStudy.
