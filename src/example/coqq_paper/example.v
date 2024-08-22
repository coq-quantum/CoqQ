From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals exp trigo.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
From mathcomp Require Import finset.
Require Import Relation_Definitions.
Require Import Setoid.

Require Import mcextra mcaextra autonat notation mxpred ctopology tensor.
Require Import hermitian quantum hspace inhabited qtype qreg qmem.
From quantum.dirac Require Import setdec hstensor dirac.
From quantum.example.coqq_paper Require Import qwhile qhl.

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

Import Order.TTheory GRing.Theory Num.Theory Num.Def DefaultQMem.Exports.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.
Local Open Scope ring_scope.
Local Open Scope set_scope.
Local Open Scope lfun_scope.
Local Open Scope dirac_scope.
Local Open Scope reg_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Module ParallelHadamardTuple.

Section ParallelHadamardTuple.
Variable (pt st : bool) (n : nat) (x : 'QReg[Bool.[n]]).

Definition bitstr_dot n (b1 b2 : n.-tuple bool) : nat :=
  (\sum_i (b1~_i * b2~_i))%N.

Lemma ParaHadamard_tuple (b : n.-tuple bool) :
  \ten_(i < n) '[''H; x.[i]] \· '|''b ; x>
  = \sum_k sqrtC 2%:R ^- n *: ((-1) ^ bitstr_dot b k *: '|''k ; x>).
Proof.
rewrite -tlinTV tlin_ket t2tv_tuple tentf_tuple_apply tketTV.
under eq_bigr do rewrite Hadamard_cb (onb_vec t2tv '±(_))/= -tket_sum.
under eq_bigr do under eq_bigr do rewrite dotp_cbpm -tketZ mulrC -scalerA.
rewrite tendA_distr_sumA (reindex (finfun_of_tuple))/=.
  by exists tuple_of_finfun=>y _; rewrite ?finfun_of_tupleK ?tuple_of_finfunK.
apply eq_bigr=>i _; rewrite scalerA t2tv_tuple tketTV.
under eq_bigr do rewrite ffunE scalerA.
rewrite tendsZ; f_equal. rewrite big_split/= prodr_const card_ord exprVn; f_equal.
by rewrite -expr_sum /bitstr_dot exprnP; under eq_bigr do rewrite andbC -mulnb.
Qed.

Lemma RS_ParaHadamard_tuple (b : n.-tuple bool) :
    ⊨s [pt,st] { '|''b ; x> } 
          [for i do [ut x.[i] := ''H]]
        { (sqrtC 2%:R ^- n) *: \sum_i (-1) ^ (bitstr_dot b i) *: '|''i ; x> }.
Proof.
rewrite linear_sum/=; apply: (RS_forward _ (AxV_UTFP _))=>[|i j]/=.
exact: ParaHadamard_tuple. tac_qwhile_auto.
Qed.

Lemma RS_ParaHadamard_tuple0 :
    ⊨s [pt,st] { \ten_i '| '0; x.[i] > } 
          [for i do [ut x.[i] := ''H]]
        { \ten_i '| '+; x.[i] > }.
Proof.
apply: (RS_forward _ (AxV_UTFP _))=>/=; last by tac_qwhile_auto.
rewrite -tlinTV -tketTV tlin_ketG tentf_tuple_apply tketTV.
by under eq_bigr do rewrite Hadamard_cb.
Qed.

Lemma RS_ParaHadamardV_tuple0 :
    ⊨s [pt,st] { \ten_i '|'+; x.[i] > } 
          [for i do [ut x.[i] := ''H]]
        { \ten_i '|'0; x.[i] > }.
Proof.
apply: (RS_forward _ (AxV_UTFP _))=>/=; last by tac_qwhile_auto.
rewrite -tlinTV -tketTV tlin_ket tentf_tuple_apply tketTV.
by under eq_bigr do rewrite Hadamard_pm.
Qed.

End ParallelHadamardTuple.
Global Arguments RS_ParaHadamard_tuple [pt st n x].

End ParallelHadamardTuple.

Module RevTuple.
Section RevTuple.
Variable (pt st : bool) (n : nat) (T : qType) (x : 'QReg[T.[n]]).

Definition rev_circuit :=
  [for i < n./2 do 
    [ut (x.[half_ord i] , x.[rev_ord (half_ord i)]) := SWAP ]].

Lemma rev_unitaryE (t : 'Ht T.[n]) :
  \ten_(i < n./2) '[ SWAP ; (x.[half_ord i] , x.[rev_ord (half_ord i)]) ]
  \· '|t; x> = '|t; (tuple i => x.[rev_ord i]) >.
Proof.
rewrite (onb_vec t2tv t)/= -!tket_sum dotd_sumr; apply eq_bigr=>i _.
rewrite -!tketZ dotdZr; f_equal; rewrite t2tv_tuple !tketTV.
case: n x t i; clear n x.
by move=>x _ t; rewrite !big_ord0 bigd dot1d.
move=>n x _ t; rewrite !big_half_split !bigdE/=.
under [in X in _ \· X]eq_bigr do rewrite tketT.
case E: (odd n); last rewrite dotdTll/=; last 
  (rewrite eq_qrE uphalf_ord_odd_rev ?E//; f_equal).
2,3: rewrite disjoint_sym; apply/bigcup_disjoint_seqP=>/= j/andP[] _ Pj;
  move: E=>/negbT E; tac_qwhile_auto; AutoNat.mc_nat.
all: rewrite ?tend1 dotd_mul/= tendsM//=; first by tac_qwhile_auto.
all: f_equal; apply eq_bigr=>j _;
by rewrite tlin_ketM swaptfEtv !eq_qrE tendC rev_ordK tketT.
Qed.


(* Lemma rev_disx i j : i != j -> 
  [disjoint lb (frev x i) & lb (frev x j)].
Proof. by rewrite -(inj_eq rev_ord_inj) !frevE; exact: disx. Qed. *)

Lemma RS_rev_circuit (t : 'Ht T.[n]) :
  ⊨s [pt,st] { '|t; x> } 
                rev_circuit
             { '|t; (tuple i => x.[rev_ord i]) > }.
Proof.
apply: (RS_forward _ (AxV_UTFP_seq _ _))=>//=.
apply: rev_unitaryE. tac_qwhile_auto.
Qed.

Lemma RS_rev_circuitV (t : 'Ht T.[n]) :
  ⊨s [pt,st] { '|t; (tuple i => x.[rev_ord i])> } 
                rev_circuit
             { '|t; x> }.
Proof.
apply: (RS_back _ (AxV_UTP_seq _ _))=>//=; last by tac_qwhile_auto.
rewrite tends_adj; under eq_bigr do rewrite tlin_adj swaptf_adj; apply: rev_unitaryE.
Qed.

End RevTuple.
Arguments RS_rev_circuit [pt st n T x].
End RevTuple.

(* implement QFT for tuple of qubits *)
Module QuantumFourierTransform.
Import RevTuple.
Section QuantumFourierTransform.
Variable (pt st : bool).

Definition omegan (n : nat) : R := (2%:R ^- n.+1).

Definition QFT_sub n (s : 'QReg[Bool * Bool.[n]]) :=
    [for i do 
        [ut (s.1 , s.2.[i]) := BControl (PhGate (omegan i))]
    ].

Definition QFT_iter n (s : 'QReg[Bool.[n]]) :=
  [for i do 
    [ut s.[i] := ''H] ;; 
    QFT_sub <{(s.[i], (tuple j : 'I_(rev_ord i) => s.[right_ord j]))}>
  ].

Definition QFT_cir n (s : 'QReg[Bool.[n]]) :=
  ((QFT_iter s) ;; (rev_circuit s)).

Lemma QFT_sub_cast n (x : 'QReg[Bool * Bool.[n]]) m 
  (y : 'QReg[Bool * Bool.[m]]) (eqn : n = m) :
  <{x.1}> =r <{y.1}> -> 
  (forall i, <{ x.2.[i] }> =r <{ y.2.[cast_ord eqn i] }>) ->  
    QFT_sub x =s QFT_sub y.
Proof.
case: m / eqn y => y P1 Pn.
apply/eq_forr=>i _; apply eq_unit=>//.
by rewrite /= P1 Pn cast_ord_id.
Qed.

Lemma QFT_iterE n (s : 'QReg[Bool.[n.+1]]) :
  QFT_iter s =s ([ut s.[0] := ''H] ;; 
                 (QFT_sub <{(s.[0], (tuple i : 'I_n => s.[nlift 0 i]))}>) ;; 
                 QFT_iter <{(tuple i => s.[nlift 0 i])}>).
Proof.
rewrite /QFT_iter big_ord_recl/=; do ! apply eq_seqc=>//.
  apply/QFT_sub_cast=>//; first by rewrite subn1.
  move=>P i; rewrite !eq_qrE; apply eq_qreg_qreg_tuplei=>//; mc_nat.
apply/eq_forr=>i _; apply eq_seqc.
apply eq_unit=>//=; first by rewrite eq_qrE.
apply/QFT_sub_cast; first by rewrite /= !eq_qrE.
move=>j /=; rewrite !eq_qrE; apply eq_qreg_qreg_tuplei=>//; mc_nat.
Qed.

(* Lemma QFT_iterE n x (s : 'I_n -> (vars bool)) :
  QFT_iter (fcons x s) =s ([ut x := ''H] ;; (QFT_sub x s) ;; QFT_iter s).
Proof.
rewrite/eqcmd/QFT_iter fsem_big big_ord_recl [in RHS]fsem_seqE fsem_big comp_soElr; f_equal.
do ! f_equal; by rewrite fcons0// fright0 fconsKV QFT_sub_cast.
apply eq_bigr=>i _; do ! f_equal; by rewrite ?fright_consE// fconsE.
Qed.

Lemma fvars_QFT_sub n (x : vars bool) (s : 'I_n -> (vars bool)) :
    fvars (QFT_sub x s) =  \bigcup_i (lb x :|: lb (s i)).
Proof. rewrite /QFT_sub fvars_for; by apply eq_bigr =>i _. Qed. *)

Lemma QFT_sub_rcons n (s : 'QReg[Bool * Bool.[n.+1]]) :
    (QFT_sub s) =s 
    (QFT_sub <{(s.1, (tuple i => s.2.[nlift ord_max i]))}> ;; 
     [ut (s.1, s.2.[ord_max]) := BControl (PhGate (omegan n))]).
Proof.
rewrite /QFT_sub eq_for_ord_recr; apply eq_seqc=>//.
apply/eq_forr=>/= i _; apply eq_unit=>//=.
rewrite !eq_qrE; apply eq_qreg_qreg_pair=>//; apply eq_qreg_qreg_tuplei=>//; mc_nat.
Qed.

Lemma QFT_iter_no_while n (s : 'QReg[Bool.[n]]) : no_while (QFT_iter s).
Proof. by apply/no_while_for=>/=i _; apply/no_while_for. Qed.

(* Lemma bigcup_add T (r : seq T) (P : pred T) (fp : T -> {set L}) (A : {set L}) :
    A :|: \bigcup_(i <- r | P i) (fp i) = A :|: \bigcup_(i <- r | P i) (A :|: (fp i)).
Proof.
elim: r=>[|x r]; first by rewrite !big_nil.
by rewrite !big_cons; case: (P x)=>//; rewrite !setUA setUid 
  [A :|: fp x]setUC -setUA=>->; rewrite setUA.
Qed.

Lemma fvars_QFT_iter n (s : 'I_n -> (vars bool)) : fvars (QFT_iter s) = \bigcup_i (lb (s i)).
Proof.
elim: n s=>[s|n IH]; first by rewrite fvars_for !big_ord0.
case/fconsP=>x s. rewrite fvars_for !big_ord_recl/= fcons0.
under eq_bigr do rewrite fconsE fright_consE. under [in RHS]eq_bigr do rewrite fconsE.
move: (IH s); rewrite fvars_for=>/=->. rewrite fright0 QFT_sub_cast fconsKV fvars_QFT_sub.
by rewrite -bigcup_add -setUA setUid.
Qed. *)

Lemma PhGate_cb r b : PhGate r ''b = expip (b%:R * r) *: ''b.
Proof. by rude_bmx; case: b=>/=; rewrite ?mul0r ?mulr0// ?mul1r ?mulr1// expip0. Qed.

(* Lemma test1 b0 b (bs : seq bool) (x y : vars bool) : 
  [disjoint lb x & lb y] ->
  '|'ph (bitstr2rat (b0 :: bs)), x> \⊗ '|''b, y>
  = '[ (BControl (PhGate (omegan (size bs))))^A, x;y ] \· 
    ('|'ph (bitstr2rat (b0 :: rcons bs b)), x> \⊗ '|''b, y>).
Proof.
move=>P1. rewrite !tketT tlin_ketG -?vars_labelE=>[//|].
rewrite BControl_adj; congr ('|_, _;_>).
rewrite BControlE lfunE/= !tentf_apply !outpE PhGate_adj.
rewrite dotp_cb0ph dotp_cb1ph phstateE linearDl/= lfunE/= PhGate_cb.
f_equal. rewrite !linearZl/= linearZr/= scalerA -mulrA. do 2 f_equal.
rewrite -expipD -rcons_cons bitstr_rcons.
case: b; last by rewrite !mul0r !addr0.
by rewrite mulrDr /omegan !mul1r exprS invfM mulrA mulfV// mul1r addrK.
Qed. *)

Lemma RS_QFT_sub n (sb : n.-tuple bool) (b : bool) (s : 'QReg[ Bool * Bool.[n]]) :
    let: prev := '|''b; s.1 > \⊗ (\ten_i '|''(sb~_i); s.2.[i] >) in
    let: postv :=  '|'ph (bitstr2rat (b :: sb)); s.1 > \⊗ (\ten_i '|''(sb~_i); s.2.[i] >) in
    ⊨s [pt,st] { prev  } ([ut s.1 := ''H] ;; (QFT_sub s)) { postv }.
Proof.
elim: n s sb=>[s sb |n IH s bs].
  rewrite /QFT_sub !big_ord0 bigd !tend1.
  apply: (RS_SC _ _ (AxS_Sk _))=>/=.
  apply: RS_UT=>//=; rewrite ?sub0set// Hadamard_adj tlin_ket.
  rewrite -Hadamard_pm; do ! f_equal. rude_bmx.
  rewrite tuple0/= [in _ [::b]]unlock/= mul0r addr0 mulrCA mulfV// mulr1.
  by case: b=>/=; rewrite ?expip0 ?expip1.
rewrite QFT_sub_rcons fsem_seqA.
case/tupleNP: bs=>bsl bsh/=.
rewrite big_ord_recr/= bigdE !tnthN.
under eq_bigr do rewrite tnthNS widen_lift.
rewrite [SPRE]tendA [SPOST]tendA.
apply (RS_SC ('|'ph (bitstr2rat (b :: bsh)); s.1> 
  \⊗ (\ten_i '|''(bsh~_i); s.2.[nlift ord_max i] >) \⊗ '|''bsl; s.2.[ord_max] >))=>/=; last first.
  apply: RV_UT=>/=; rewrite [LHS]tendAC [in RHS]tendAC dotdTll/==>[||].
    tac_qwhile_auto. tac_qwhile_auto.
  f_equal; rewrite !tketT tlin_ket; f_equal.
  rewrite BControl_adj BControlE lfunE/= !tentf_apply !outpE PhGate_adj.
  rewrite dotp_cb0ph dotp_cb1ph phstateE linearDl/= lfunE/= PhGate_cb.
  f_equal. rewrite !linearZl/= linearZr/= scalerA -mulrA. do 2 f_equal.
  rewrite -rcons_cons bitstr_rcons mulrDr expipD -[LHS]mulr1 -mulrA; f_equal.
  rewrite -expip0 -expipD; f_equal.
  by rewrite mulrCA -mulrDr exprS invfM mulrA mulfV//= size_tuple mul1r addrN mulr0.
move: IH=>/(_ <{ (s.1, (qreg_tuple (fun i : 'I_n => <{ s.2.[nlift ord_max i] }>)))}> bsh).
rewrite [in SPRE]eq_qrE; under eq_bigr do rewrite !eq_qrE.
rewrite [in SPOST]eq_qrE [in SCMD](eq_unitl _ (eq_qreg_fst _ _))/=.
rewrite /QFT_sub; apply: RV_Frame.
by apply/orP; right; apply/no_while_for.
rewrite /QFT_sub/=; tac_qwhile_auto.
tac_qwhile_auto.
Qed.

Lemma QFTbv_rev n (s : 'QReg[Bool.[n]]) (sb : n.-tuple bool) :
  '|QFTbv sb; (tuple i => s.[rev_ord i])> = 
    \ten_(i < n) '|'ph (bitstr2rat (drop i sb)); s.[i] >.
Proof.
rewrite QFTbvTE tketTV [in RHS](reindex_inj rev_ord_inj)/= bigd.
by apply eq_bigr=>i _; rewrite eq_qrE subnS predn_sub.
Qed.

Lemma RS_QFT_iter n (s : 'QReg[Bool.[n]]) (sb : n.-tuple bool) :
    ⊨s [pt,st] { '|''sb ; s > } (QFT_iter s) 
        { '|QFTbv sb ; (tuple i => s.[rev_ord i]) > }.
Proof.
rewrite QFTbv_rev.
elim: n s sb=>[s sb|n IH s sb].
  rewrite /QFT_iter t2tv_tuple tketTV !big_ord0 bigd; apply: AxS_Sk.
rewrite !big_ord_recl/= !bigdE.
case/tupleP: sb=>b sb.
rewrite QFT_iterE/=.
apply (RS_SC ('|'ph (bitstr2rat (b :: sb)); s.[0] >
  \⊗ ('|''sb; (tuple i => s.[nlift 0 i])>)))=>/=.
  move: RS_QFT_sub=>/(_ _ sb b <{(s.[0], (tuple i => s.[nlift 0 i]))}>)/=.
  apply: eq_state_hoare.
    - rewrite eq_qrE t2tv_tuple tketTV big_ord_recl bigdE tnth0 bigd.
      by f_equal; apply eq_bigr=>i _; rewrite !eq_qrE tnthS.
    - by rewrite (eq_unitl _ (eq_qreg_fst _ _)).
    - by rewrite eq_qrE t2tv_tuple tketTV; under eq_bigr do rewrite eq_qrE.
apply: RV_Framel=>/=[| _ | _ ||].
  - rewrite /QFT_iter /QFT_sub; tac_qwhile_auto.
  - by rewrite QFT_iter_no_while orbT.
  - rewrite /QFT_iter/= fvars_for disjoint_sym; apply/bigcup_disjointP=>/= i _.
    rewrite /QFT_sub/=; tac_qwhile_auto.
  - tac_qwhile_auto.
move: IH=>/(_ <{(tuple i => s.[nlift 0 i])}> sb)=>/=;
by under eq_bigr do rewrite eq_qrE.
Qed.

Lemma RS_QFT_cir n (s : 'QReg[Bool.[n]]) (sb : n.-tuple bool) :
    ⊨s [pt,st] { '|''sb ; s > } ((QFT_iter s) ;; (rev_circuit s))
        { '|QFTbv sb; s > }.
Proof.
apply: (RS_SC _ (RS_QFT_iter _ _)).
apply: RS_rev_circuitV.
Qed.

End QuantumFourierTransform.
End QuantumFourierTransform.


(* to hide local theorems, use Let instead of Definition and Lemma *)
Module HHL.
Local Open Scope hspace_scope.
Local Open Scope ring_scope.
Section HHL.
Variable (m n : nat).
(* q : m.+1 : dimension of data; p : n.+1 : dimension of control system *)
(* here, we provide the decomposition of data : A; pure state b *)
Variable (u : 'ONB('I_m.+1; 'Ht 'I_m)) (λ : 'I_m.+1 -> R) (b : 'NS('Ht 'I_m)).
Let A := \sum_i (λ i)%:C *: [> u i ; u i <].
(* δ : ensure that control system is enough to store eigenvalue δ *)
Variable  (t0 : R) (δ : 'I_m.+1 -> 'I_n.+1) (cc : C).
(* this assumption to make the algorithm exact *)
Hypothesis (Hyp : forall i, pi * 2%:R * (δ i)%:R = λ i * t0).
(* assume A is non-degenerate *)
Hypothesis (D_neq0 : forall i, (0 < (δ i))%N).
(* to construct a valid control gate between p and auxiliary system r *)
Hypothesis (cc_bound : `|cc| <= 1).
Let β := (fun i=> [<u i ; b : 'Ht 'I_m >]).
Lemma decb : ((b : 'Ht 'I_m) = \sum_i (β i) *: (u i)).
Proof. exact: onb_vec. Qed.
Lemma lambda_gt0 : forall i, λ i != 0.
Proof. 
move=>i; apply/eqP=>P. move: (Hyp i)=>/eqP; apply/negP.
rewrite P mul0r mulf_eq0 mulf_eq0 !pnatr_eq0 !negb_or.
do ? (apply/andP; split=>//). apply pi_neq0. by apply/lt0n_neq0.
Qed.
Lemma t0_neq0 : t0 != 0.
Proof.
apply/eqP=>P. move: (Hyp ord0)=>/eqP; apply/negP.
rewrite P mulr0 mulf_eq0 mulf_eq0 !pnatr_eq0 !negb_or.
do ? (apply/andP; split=>//). apply pi_neq0. by apply/lt0n_neq0.
Qed.
Lemma lambdaE i : λ i = (pi * 2%:R / t0) * (δ i)%:R.
Proof. by rewrite -mulrA [_^-1 * _]mulrC mulrA Hyp mulfK// t0_neq0. Qed.
Let x_uns := \sum_i (β i / (λ i)%:C) *: (u i).
Let c := `|x_uns|.
Lemma c_gt0 : c > 0.
Proof.
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
Let x : 'Ht 'I_m := c^-1 *: x_uns.
Lemma x_ns : [< x ; x >] = 1.
Proof.
rewrite dotp_norm /x hnormZ -/c ger0_norm ?invr_ge0 ?mulVf ?expr1n//.
apply/ltW/c_gt0. apply/lt0r_neq0/c_gt0.
Qed.
HB.instance Definition _ := isNormalState.Build ('Ht 'I_m) x x_ns.
(* Canonical x_nsType := NSType x_ns. *)
(* Ub |0;p> -> b *)
Let Ub := VUnitary ''ord0 b.
Let Uf_fun := (fun i : 'I_n.+1 => expmxip u λ (i%:R * t0 / pi / n.+1%:R)).
(* Uf is a Multiplexer *)
Let Uf := Multiplexer Uf_fun.
(* QFT : QFT : QFT unitary; QFTv : QFT basis *)
(* to defintion Uc, note that its partial *)
Let v k (i : 'I_k.+1) : 'Ht Bool := 
  if i == 0 then '0 else 
  [bmv sqrtC (1 - `|cc|^+2/i%:R^+2) ; cc / i%:R].
Lemma v_ns k i : [< @v k i ; @v k i >] = 1.
Proof.
rewrite /v; case: eqP=>[_|/eqP]; rude_bmx=>//.
rewrite -lt0n=>P; rewrite -!normCKC [ `|sqrtC _|]ger0_norm.
rewrite sqrtC_ge0 subr_ge0 ler_pdivrMr ?exprn_gt0// ?ltr0n// mul1r.
apply: lerXn2r; rewrite ?nnegrE//.
by apply: (le_trans cc_bound); rewrite ler1n.
by rewrite sqrtCK normf_div [ `|i%:R|]ger0_norm// 
  expr_div_n addrC -addrA addNr addr0.
Qed.
HB.instance Definition _ k i := 
  isNormalState.Build ('Ht Bool) (@v k i) (@v_ns k i).
(* Local Canonical v_nsType k i := NSType (@v_ns k i). *)
Let Uc_from : 'I_n.+1 -> 'Ht ('I_n * Bool) := (fun i : 'I_n.+1 => ''i ⊗t '0).
Let Uc_to : 'I_n.+1 -> 'Ht ('I_n * Bool) := (fun i : 'I_n.+1 => ''i ⊗t v i).
Lemma Uc_from_ponb : forall i j, [< Uc_from i ; Uc_from j >] = (i == j)%:R.
Proof. by move=>i j; rewrite /Uc_from tentv_dot !onb_dot eqxx mulr1. Qed.
Lemma Uc_to_ponb : forall i j, [< Uc_to i ; Uc_to j >] = (i == j)%:R.
Proof.
move=>i j; rewrite /Uc_to tentv_dot onb_dot.
by case: eqP=>[->|_]; rewrite ?mul0r//= ns_dot mulr1.
Qed.
HB.instance Definition _ := 
  isPONB.Build ('Ht ('I_n * Bool)) 'I_n.+1 Uc_from Uc_from_ponb.
HB.instance Definition _ := 
  isPONB.Build ('Ht ('I_n * Bool)) 'I_n.+1 Uc_to Uc_to_ponb.
(* Local Canonical Uc_from_ponbasis := PONBasis Uc_from_ponb. *)
(* Local Canonical Uc_to_ponbasis := PONBasis Uc_to_ponb. *)
Let Uc := PUnitary Uc_from Uc_to.

(* quantum registers *)
Variable (pqr : 'QReg['I_n * 'I_m * Bool]).
Notation p := <{ pqr.1.1 }>.
Notation q := <{ pqr.1.2 }>.
Notation r := <{ pqr.2 }>.

(* define the loop body of HHL *)
(* we split the initial part out, to use etdf of HHL body *)
Definition HHL_body := 
  [ut q := Ub ];;
  [ut p := 'Hn ];;
  [ut (p,q) := Uf ];;
  [ut p := IQFT ];;
  [ut (p,r) := Uc ];;
  [ut p := QFT ];;
  [ut (p,q) := (Uf^A)%VF ];;
  [ut p := ('Hn^A)%VF ].

Definition HHL :=
  [it p := ''ord0 ];;
  [it q := ''ord0 ];;
  [it r := '0 ];;
  [while tmeas[ r ] = false do [it q := ''ord0] ;; HHL_body].

(* we show the correctness w.r.t. local correctness *)
Let P := '[ [> ''ord0; ''ord0 <]; p ] \⊗ '[ \1; q ] \⊗ '[ [> '0; '0 <]; r ].
Let Q := '[ [> ''ord0; ''ord0 <]; p ] \⊗ '[ [> x ; x <]; q ] \⊗ '[ [> '1; '1 <]; r ].

Let vv := \sum_(i < m.+1) (β i *: u i ⊗t v (δ i)).
Lemma vv_norm1 : `|vv| = 1.
Proof.
apply/eqP; rewrite hnorm_eq1 /vv linear_sum/=.
move: (ns_dot b)=><-; rewrite decb linear_sum/=.
apply/eqP; apply eq_bigr=>i _; rewrite !dotp_suml; apply eq_bigr=>j _.
rewrite !linearZl/= !linearZr/= tentv_dot onb_dot.
by case: eqP=>[->|]; rewrite ?mul0r ?mulr0// ns_dot mulr1.
Qed.
Let pp0 : 'End{'I_m * Bool} := (\1 : 'End{'I_m}) ⊗f [> '0; '0 <].
Let pp1 : 'End{'I_m * Bool} := [> x ; x <] ⊗f [> '1; '1 <].
Lemma pp0_proj : pp0 \is projlf.
Proof.
by apply/projlfP; rewrite /pp0 tentf_adj adj_outp adjf1 
  tentf_comp comp_lfun1l outp_comp onb_dot scale1r.
Qed.
HB.instance Definition _ := isProjLf.Build ('Ht 'I_m * Bool) pp0 pp0_proj.
(* Local Canonical pp0_projfType := ProjfType pp0_proj. *)
Lemma pp1_proj : pp1 \is projlf.
Proof.
by apply/projlfP; rewrite /pp1 tentf_adj !adj_outp
  tentf_comp !outp_comp !ns_dot !scale1r.
Qed.
HB.instance Definition _ := isProjLf.Build ('Ht 'I_m * Bool) pp1 pp1_proj.
(* Local Canonical pp1_projfType := ProjfType pp1_proj. *)
Lemma pp0_ortho_pp1 : (pp0 \o pp1)%VF = 0.
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
  by rewrite invr_eq0; apply/lt0r_neq0/c_gt0.
rewrite /x_uns tentv_suml. under [in X in <[X]> ]eq_bigr do rewrite lambdaE mulrC
  realcM invfM natrC tentvZl -[_ * _ * β _]mulrA -scalerA.
rewrite -linear_sum/= hlineZ; last by apply: memh_line.
by rewrite invr_eq0 realc_eq0 !mulf_eq0 !negb_or pi_neq0/= invr_eq0 t0_neq0 andbT.
Qed.

Let R := '|''ord0; p> \⊗ '|vv; (q,r)>.
Lemma RS_HHL_body pt st : 
  ⊨s [pt,st] { '|''ord0; p> \⊗ '|''ord0; q> \⊗ '|'0; r> } 
               HHL_body { R }.
Proof.
rewrite /HHL_body /R.
+ apply: (RS_SC _ _ (AxV_UT _))=>/=.
  rewrite adjfK dotdTll/=; try tac_qwhile_auto.
  rewrite tlin_ket VUnitaryE/= uniformtvE card_ord/= -tketZ tendZl /vv -tket_sum -tket_sum tend_sumr.
+ apply: (RS_SC _ _ (AxV_UT _))=>/=.
  rewrite adjfK dotdZr dotd_sumr.
  under eq_bigr do rewrite tend_suml dotd_sumr/=.
  have P1: [disjoint mset <{(p,q)}> & mset r] by tac_qwhile_auto.
  under eq_bigr do under eq_bigr do rewrite -tketT tendA tketT 
    (dotdTll _ _ _ P1 P1)/= tlin_ket.
+ apply: (RS_SC _ _ (AxV_UT _))=>/=.
+ apply: (RS_forward (R := \sum_j('|''(δ j) ⊗t v (δ j); (p,r)> \⊗ '|β j *: u j; q>))).
  rewrite linear_sum/= dotd_sumr; apply eq_bigr=>i _.
  rewrite -/IQFT -tketT tendAC -tendA.
  under eq_bigr do rewrite 2!linearZ/= MultiplexerEt expmxipEt -tentvZS -linearZr/= -tketT -tendA.
  rewrite -tend_suml -tendZl tket_sum tketZ dotdTll/=; try tac_qwhile_auto.
  f_equal; rewrite tlin_ket.
  under eq_bigr do rewrite mulrA -[ _ / pi]mulrA [_%:R * _]mulrC !mulrA -Hyp -[ _ / pi]mulrC.
  under eq_bigr do rewrite !mulrA (mulVf pi_neq0) mul1r -[_%:R * _ * _]mulrA -natrM -runityE.
  by rewrite -QFTvE IQFTEt.
+ apply: (RS_SC _ _ (AxV_UT _))=>/=.
  rewrite dotd_sumr.
  have P2: [disjoint mset <{(p,r)}> & mset q] by tac_qwhile_auto.
  under eq_bigr do rewrite (dotdTll _ _ _ P2 P2)/= tlin_ket PUnitaryEV -tketT tendAC.
  rewrite -tend_suml.
+ apply: RV_Frame=>//=; first by rewrite orbT.
  tac_qwhile_auto. tac_qwhile_auto.
  rewrite -!fsem_seqA. 
+ apply: (RS_SC _ (AxV_UTF _))=>/=.
  rewrite dotdTlr/= ?tlin_ket; try tac_qwhile_auto.
+ apply: (RS_SC _ (AxV_UTF _))=>/=.
  rewrite dotdTll/= ?tlin_ket; try tac_qwhile_auto.
+ apply: (RS_SC _ (AxV_UTF _))=>/=.
  rewrite tketT tlin_ket.
+ apply: RV_UTF.
rewrite/= !VUnitaryE/= uniformtvE card_ord decb 2!linear_sum/= -tket_sum dotd_sumr.
apply eq_bigr=>i _.
rewrite linearZl/= [in RHS]linearZ/= -[in RHS]tketZ linear_suml/= linear_sum/= -tket_sum.
under eq_bigr do rewrite 2!linearZ/= MultiplexerEt expmxipEt -tentvZS -linearZr/= -tketT
  mulrA -[ _ / pi]mulrA [_%:R * _]mulrC !mulrA -Hyp -[ _ / pi]mulrC 
  !mulrA (mulVf pi_neq0) mul1r -[_%:R * _ * _]mulrA -natrM -runityE.
rewrite -tend_suml -tendZl tket_sum tketZ -QFTvE dotdTll/=; try tac_qwhile_auto.
by rewrite tlin_ket IQFTEt.
Qed.

(* need the theory of subspace/projection here *)
Lemma HHL_PQR_relation : R \o R^A ⊑ dform ('[ [> '1 ; '1 <]; r ]) Q 
  + dform ('[ [> '0 ; '0 <]; r ]) P.
Proof.
rewrite !dformE !tlin_adj !adj_outp /P /Q ![_ \⊗ '[_;r]]tendC.
rewrite !dotdTll/= ?tlinG ?dotdTrl/= ?tlinG; try tac_qwhile_auto.
rewrite !outp_comp !ns_dot !scale1r !outp_comp !ns_dot !scale1r 
  !['[_;r] \⊗ _]tendC -!tendA -tendDr !tlinT tlinD.
rewrite /R adjdT !tket_adj tend_mul ?disjoint0X// !touter.
apply: le_wptend2l=>/=. tac_qwhile_auto.
by rewrite tlin_ge0 outp_ge0.
by rewrite tlin_le addrC vv_lef.
Qed.

Let P' := '[ [> ''ord0; ''ord0 <]; p ] \⊗ '[ [> ''ord0; ''ord0 <]; q ] \⊗ '[ [> '0; '0 <]; r ].
Lemma R_HHL_loop_P :
  ⊨p { dform ('[ [> ''(~~false) ; ''(~~false) <]; r ]) Q + dform ('[ [> '0 ; '0 <]; r ]) P } 
  [while tmeas[r] = false do [it q := ''ord0] ;; HHL_body]
  { Q }.
Proof.
rewrite /P /Q !tlinT.
+ apply: tbR_LP_P=>/=.
  1,2:  by rewrite tlin_lef1 -!tentf11 ?lev_pbreg2// 
    ?ns_outp_le1// ?bregv_ge0// ?outp_ge0// lef01.
+ apply: (R_SC P').
  rewrite -!tlinT tendAC -tlin1 R_El/=; first by tac_qwhile_auto.
  rewrite /P' tendAC [POST]tendC; apply: tAx_InF; tac_qwhile_auto.
move: (RS_HHL_body false false); rewrite stateE.
rewrite -!tlinT -/P -/Q !tketT tket_adj touter -!tentv_out -!tlinT.
by apply: R_Or=>//; exact: HHL_PQR_relation.
Qed.

Lemma R_HHL_P : ⊨ps { :1 } HHL { '|x; q>}.
Proof.
rewrite stateE adjd1 numdM mul1r tket_adj touter.
apply/(R_Er (W:= mset <{(p,r)}>) _)=>/=; first by tac_qwhile_auto.
apply: (R_Orr (Q:=Q) _)=>/=.
  rewrite tlin1 /Q -tentf11 -tlinT tendA [X in X \⊗ _]tendC !tlinT.
  by rewrite tlin_le ?lev_pbreg2// ?ns_outp_le1// ?outp_ge0// bregv_ge0// outp_ge0.
rewrite /HHL. apply: (R_SC _ _ R_HHL_loop_P)=>/=.
rewrite -fsem_seqA.
apply: (R_SC _ (tAx_InF _))=>/=; first by rewrite disjointX0.
apply: (R_SC _ (tAx_InF _))=>/=; first by rewrite setU0; tac_qwhile_auto.
apply: (R_Orr _ (tAx_InF _))=>/=; last by rewrite setU0; tac_qwhile_auto.
rewrite !dformE !tlin_adj !dotdTlr/= ?tlinG ?dotdTrr/=; try tac_qwhile_auto.
rewrite !tlinG !adj_outp !outp_comp !ns_dot !scale1r !outp_comp !ns_dot !scale1r.
rewrite tend1 tendAC -[X in X <= _]add0r levD//.
by rewrite !tlinT tlin_ge0 !bregv_ge0 ?outp_ge0.
rewrite tendCA tendA tendC tendA !tlinT tlin_le.
by rewrite !lev_pbreg2// ?bregv_ge0// ?outp_ge0// ns_outp_le1.
Qed.

End HHL.
End HHL.


(* HLF *)
Module HiddenLinearFunction.
Import ParallelHadamardTuple.
Section HiddenLinearFunction.
Variable (pt st : bool) (N : nat). (* grid of N.+1 * N.+1 *)
Variable (A : 'M[bool]_N.+1).
Hypotheses (A_sym : forall i j, A i j = A j i).
Variable (x : 'QReg[Bool.[N.+1]]).

Definition HLF_q (k : N.+1.-tuple bool) :=
  ((\sum_j A j.1 j.2 * k ~_ j.1 * k ~_ j.2) %% 4)%N.

Definition SD := [set x : 'I_N.+1 | A x x == true].
Definition SS := [set x : 'I_N.+1 * 'I_N.+1 | (A x.1 x.2 == true) && (x.1 < x.2)%N].
Lemma SD_inP y : y \in SD -> A y y = true.
Proof. by rewrite inE=>/eqP. Qed. 
Lemma SS_inP y : y \in SS -> A y.1 y.2 = true /\ (y.1 < y.2)%N /\ y.1 != y.2.
Proof. by rewrite inE=>/andP[/eqP]; split=>//; split=>//; apply: ltn_neq. Qed.

Definition HLF_sub1 :=
  [for i do [it x.[i] := '0 ]];;
  [for i do [ut x.[i] := ''H ]].

Definition HLF_sub2 (r1 : seq 'I_N.+1) (SP1 : pred 'I_N.+1) :=
  [for i <- r1 | SP1 i do [ut x.[i] := ''S ]].

Definition HLF_sub3 (r2 : seq ('I_N.+1 * 'I_N.+1)) (SP2 : pred ('I_N.+1 * 'I_N.+1)) :=
  [for i <- r2 | SP2 i do [ut (x.[i.1] , x.[i.2]) := ''CZ ]].

Definition HLF :=
  [for i do [it x.[i] := '0 ]];;
  [for i do [ut x.[i] := ''H ]];;
  [for i in SD do [ut x.[i] := ''S ]];;
  [for i in SS do [ut (x.[i.1] , x.[i.2]) := ''CZ ]];;
  [for i do [ut x.[i] := ''H ]].

Lemma fsem_big_rcons I i r (P : pred I) (F : I -> cmd_) :
  let x := [for j <- r | P j do F j] in
  [for j <- rcons r i | P j do F j] =s if P i then x ;; (F i) else x.
Proof.
rewrite /= eqcmd.unlock; case E: (P i)=>/=;
by rewrite ?fsemE !fsem_big big_rcons/= E.
Qed.

Lemma plus_dec : '+ = (sqrtC 2%:R)^-1 *: \sum_(i : bool) ''i.
Proof. by rewrite big_bool/=; rude_bmx. Qed.

(* Let PT: True. by []. Qed. *)

Lemma RS_HLF_sub12 (r1 : seq 'I_N.+1) (SP1 : pred 'I_N.+1) :
  ⊨s [pt,st] { :1 } (HLF_sub1 ;; HLF_sub2 r1 SP1) { (sqrtC 2%:R ^- N.+1 *:
  (\sum_(i : N.+1.-tuple bool) ('i ^ (\sum_(j <- r1 | SP1 j) i ~_ j)%N) *: '|''i; x>)) }.
Proof.
rewrite /HLF. rewrite -!fsem_seqA.
apply: (RS_SC _ (tAxV_InFP_seq _ _ _))=>/=[i j _ _|//|i _|]; try tac_qwhile_auto;
rewrite ?disjoint0X//= tend1 tketT eq_qrE.
have ->: tentv_tuple (fun=> '0) = ''(nseq_tuple N.+1 false) :> 'Ht Bool.[N.+1].
  by rewrite t2tv_tuple; under [in RHS]eq_tentv_tuple do rewrite tnth_nseq.
apply: (RS_SC _ (RS_ParaHadamard_tuple _) _).
rewrite /HLF_sub2; elim/last_ind: r1=>[|r i IH].
rewrite !big_nil; apply: (RS_forward _ (AxS_Sk _));
rewrite/=; f_equal; apply eq_bigr=>bs _; f_equal.
by rewrite /bitstr_dot big_nil big1 ?expr0z// =>i _; rewrite tnth_nseq.
rewrite fsem_big_rcons; case E: (SP1 i); last first.
by apply: (RS_forward _ IH); under [in RHS]eq_bigr do rewrite big_rcons E/=.
apply: (RS_SC _ IH).
apply : (RS_forward _ (AxV_UTF _)).
rewrite/= !linear_sum/=; apply eq_bigr=>bs _.
rewrite !dotdZr; f_equal; rewrite/= t2tv_tuple tketTV (bigD1 i)//= bigdE tketGTl.
  tac_qwhile_auto.
rewrite SGate_cb -tketZ tendZl scalerA; f_equal.
by rewrite big_rcons E/= -!exprnP -exprD.
Qed.

Lemma RS_HLF_sub (r1 : seq 'I_N.+1) (SP1 : pred 'I_N.+1) 
  (r2 : seq ('I_N.+1 * 'I_N.+1)) (SP2 : pred ('I_N.+1 * 'I_N.+1)) :
  (forall x, SP2 x -> x.1 != x.2) -> 
  ⊨s [pt,st] { :1 } (HLF_sub1 ;; HLF_sub2 r1 SP1 ;; HLF_sub3 r2 SP2) { (sqrtC 2%:R ^- N.+1 *:
  (\sum_(i : N.+1.-tuple bool) 
    ('i ^ (\sum_(j <- r1 | SP1 j) i ~_ j + 2 * \sum_(j <- r2 | SP2 j) i ~_ j.1 * i ~_ j.2)%N) 
      *: '|''i; x>)) }.
Proof.
move=>H2; apply: (RS_SC _ (RS_HLF_sub12 _ _)).
rewrite /HLF_sub3; elim/last_ind: r2=>[|r i IH].
rewrite !big_nil; apply: (RS_forward _ (AxS_Sk _)).
by rewrite/=; f_equal; apply eq_bigr=>bs _; f_equal; 
rewrite /bitstr_dot big_nil muln0 addn0.
rewrite fsem_big_rcons; case E: (SP2 i); last first.
by apply: (RS_forward _ IH); under [in RHS]eq_bigr do rewrite big_rcons E/=.
apply: (RS_SC _ IH).
have Hx : valid_qreg <{ (x.[i.1], x.[i.2]) }>.
  by tac_qwhile_auto=>/=; rewrite H2.
apply : (RS_forward _ (AxV_UTF _)).
rewrite/= !linear_sum/=; apply eq_bigr=>bs _.
rewrite !dotdZr; f_equal; rewrite/= big_rcons E/= mulnDr addnA -!exprnP [in RHS]exprD.
rewrite -scalerA; f_equal. rewrite exprM sqrCi t2tv_tuple tketTV.
rewrite (bigD1 i.1)//= bigdE (bigD1 i.2)/= 1?eq_sym ?H2// bigdE tendA tketT tketGTl.
  by tac_qwhile_auto=>/=; rewrite eq_sym orbF; move: H => /andP[].
rewrite/= CZGate_cb tentvZr -tketZ tendZl; f_equal.
by case: (bs ~_ i.1); case: (bs ~_ i.2).
Qed.

Lemma RS_HLF_gen :
  ⊨s [pt,st] { :1 } HLF { (2%:R ^- N.+1 *:
  (\sum_(z : N.+1.-tuple bool) (\sum_(k : N.+1.-tuple bool) 
    ('i ^ (\sum_(j in SD) k ~_ j + 2 * (\sum_(j in SS) k ~_ j.1 * k ~_ j.2) + 2 * \sum_j k~_j * z ~_ j)%N)) 
      *: '|''z; x>)) }.
Proof.
rewrite /HLF big_setEV.
apply: (RS_SC _ (RS_HLF_sub _ _ _ _)).
by move=>i; rewrite inE=>/andP[] _; exact: ltn_neq.
apply: (RS_forward _ (AxV_UTFP_seq _ _))=>/=[|//|]; last by tac_qwhile_auto.
rewrite/= dotdZr dotd_sumr.
under eq_bigr do rewrite dotdZr (ParaHadamard_tuple x) linear_sum/=.
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
rewrite addn0; case: (A i i); rewrite /= ?mul0n// mul1n mulnb; by case: (k ~_ i).
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
  ⊨s [pt,st] { :1 } HLF { (2%:R ^- N.+1 *:
  (\sum_(z : N.+1.-tuple bool) (\sum_(k : N.+1.-tuple bool) 
    ('i ^ (HLF_q k + 2 * \sum_j k~_j * z ~_ j)%N)) 
      *: '|''z; x>)) }.
Proof.
apply: (RS_forward _ RS_HLF_gen). f_equal; apply eq_bigr=>z _; f_equal.
by apply eq_bigr=>k _; rewrite exprzD_nat HLF_quadE -exprzD_nat PoszM.
Qed.

End HiddenLinearFunction.
End HiddenLinearFunction.

Ltac simpc2r := rewrite -?(natrC, realcN, realcD, realcM, realcI, realcX, realc_norm).

Module GroverAlgorithm.
Section GroverAlgorithm.
Variable (pt st : bool) (T : qType) (x : 'QReg[T]). (* arbitrary ihbFinType *)
Notation TT := (evalQT T).
Variable (Pw : pred TT). (* Solution *)
Hypothesis (card_Pw : (0 < #|Pw| < #|TT|)%N). (* proper number of solutions *)
Local Notation t0 := (witness TT : TT).
Local Notation us := (@uniformtv TT).
Let Uw := PhOracle Pw.
Let Ut0 := 2%:R *: [> ''t0 ; ''t0 <] - \1.
Let Us := 2%:R *: [> us ; us <] - \1.
Lemma Us_diffE : Us = ('Hn \o Ut0 \o 'Hn^A)%VF.
Proof.
by rewrite /Ut0 linearBr/= linearZr/= outp_compr VUnitaryE/= comp_lfun1r 
  linearBl/= linearZl/= outp_compl adjfK VUnitaryE/= unitaryf_formV.
Qed.
Lemma Ut0_unitary : Ut0 \is unitarylf.
Proof.
apply/unitarylfP; rewrite /Us raddfB/= adjf1 adjfZ conjC_nat adj_outp.
rewrite linearBr/= !linearBl/= !comp_lfun1l comp_lfun1r linearZl/= linearZr/=.
rewrite scalerA outp_comp ns_dot scale1r opprB -scalerBl [\1 - _]addrC.
by rewrite addrA -scalerBl mulr_natr mulr2n addrK subrr scale0r add0r.
Qed.
HB.instance Definition _ := isUnitaryLf.Build _ Ut0 Ut0_unitary.
Lemma Us_unitary : Us \is unitarylf.
Proof. by rewrite Us_diffE is_unitarylf. Qed.
HB.instance Definition _ := isUnitaryLf.Build _ Us Us_unitary.

Definition Grover_sub :=
  [ut x := Uw];;
  [ut x := 'Hn^A];;
  [ut x := Ut0];;
  [ut x := 'Hn].

Definition Grover (r : nat) :=
  [it x := ''t0 ];;
  [ut x := 'Hn ];;
  [for i < r do Grover_sub].

Let t := asin (Num.sqrt (#|Pw|%:R / #|TT|%:R) : R).
Lemma cos2Dsin2c : (cos t ^+ 2)%:C + (sin t ^+2 )%:C = 1.
Proof. by rewrite -realcD cos2Dsin2. Qed.
Lemma sin2t : (sin t ^+2 )%:C = #|Pw|%:R / #|TT|%:R.
Proof.
rewrite /t asinK; last first.
by rewrite sqr_sqrtr ?realcM ?realcI ?natrC// divr_ge0.
rewrite itv_boundlr/= /<=%O/=; apply/andP; split.
by apply: (le_trans (lerN10 _)); rewrite sqrtr_ge0.
by rewrite -{3}sqrtr1; apply/ler_wsqrtr; rewrite ler_pdivrMr 
  ?ihb_card_gtr0// mul1r ler_nat max_card.
Qed.
Lemma sint_neq0 : (sin t) != 0.
Proof.
rewrite -sqrf_eq0 -eqcR sin2t; apply/lt0r_neq0; apply divr_gt0;
by rewrite ?ihb_card_gtr0// ltr0n; move: card_Pw=>/andP[].
Qed.
Let sint_neq0 := sint_neq0.
Lemma cos2t : (cos t ^+ 2)%:C = (#|TT|%:R - #|Pw|%:R) / #|TT|%:R.
Proof.
rewrite mulrBl mulfV ?ihb_card_neq0// -sin2t; apply/subr0_eq.
by rewrite opprB addrA -realcD cos2Dsin2 subrr.
Qed.
Lemma cost_neq0 : cos t != 0.
Proof.
rewrite -sqrf_eq0 -eqcR cos2t; apply/lt0r_neq0; apply divr_gt0;
by rewrite ?ihb_card_gtr0// subr_gt0 ltr_nat; move: card_Pw=>/andP[].
Qed.
Let cost_neq0 := cost_neq0.

Let vw := (sqrtC #|TT|%:R)^-1 *: \sum_(i | Pw i) ''i.
Let vwc := (sqrtC #|TT|%:R)^-1 *: \sum_(i | ~~ Pw i) ''i.
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
by rewrite dotp_sumr (bigD1 i)//= big1=>[j/andP[_]/negPf Pj|]; 
  rewrite ?ns_dot ?addr0// onb_dot eq_sym Pj.
Qed.
Lemma vwc_dot : [<vwc ; vwc >] = (cos t ^+ 2)%:C.
Proof.
move: (ns_dot us); rewrite/= us_vwE dotpD vw_vwc_dot vw_dot conjC0 !addr0=>/eqP.
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

Lemma UsUwE_ind (r : R) : (Us \o Uw)%VF (uw r) = uw (r + t *+ 2).
Proof.
rewrite lfunE/= linearP/= Uw_vw scalerN [Uw _]linearZ/= Uw_vwc /Us us_vwE lfunE/= !lfunE/= lfunE/=.
rewrite outpE dotpDr dotpNr dotpZr (dotpZr (_%:C)) !dotpDl vw_dot -conj_dotp !vw_vwc_dot vwc_dot conjC0.
rewrite addr0 add0r scalerA scalerDr opprD opprK addrACA -scalerDl -[_ - _ *: vwc]scalerBl /uw.
do ? f_equal; simpc2r; f_equal; rewrite !expr2 mulrACA mulVf// mulrACA mulVf//;
rewrite !mulr1 mulr_natl mulrnDl.
rewrite /uw sinD cos2x_sin sin2x addrC mulrDl mulrBr mulrBl mulr1 addrA [sin t * _]mulrC; do 2 f_equal.
3: rewrite cosD cos2x_cos sin2x mulrBr mulr1 [in RHS]addrC mulrDl mulrBl [in RHS]addrA; do 2 f_equal.
all: by rewrite -[in RHS]mulr_natl ?mulNr -!mulrA  ?mulfV// mulr1 mulr_natl mulrnAr// mulNrn.
Qed.

Lemma UsUwEV_ind (r : R) : ((Us \o Uw)^A)%VF (uw r) = (uw (r - t *+ 2)).
Proof. by apply/eqP; rewrite unitaryf_sym/= UsUwE_ind addrNK. Qed.

Lemma vw_uw : vw = (sin t)%:C *: uw (pi/2%:R).
Proof.
by rewrite /uw cos_pihalf sin_pihalf mul0r scale0r addr0 
  scalerA mul1r -realcM mulfV// scale1r.
Qed.

Lemma RS_Grover_sub (n : nat) : 
  ⊨s [pt,st] { '|uw (pi/2%:R - t *+ 2 *+ n); x> } 
    [for i < n do Grover_sub]
      { '|(sin t)%:C ^-1 *: vw ; x> }.
Proof.
elim: n=>[|n IH].
rewrite big_ord0 mulr0n subr0 vw_uw scalerA -realcI -realcM mulVf// scale1r; exact: AxS_Sk.
rewrite big_ord_recl; apply: (RS_SC _ _ (IH)); rewrite /Grover_sub.
do 3 (apply: (RS_SC _ _ (AxV_UT _)); rewrite/= tlin_ket).
apply: (RS_back _ (AxV_UT _)).
rewrite/= tlin_ket -!comp_lfunE -!adjf_comp !comp_lfunA.
by rewrite -Us_diffE UsUwEV_ind -addrA -opprD -mulrSr.
Qed.

Lemma RS_Grover (n : nat) : 
  ⊨s [pt,st] { (cos (pi / 2%:R - t *+ (2 * n + 1)))%:C *: :1 } 
    (Grover n) { '|(sin t)%:C ^-1 *: vw; x> }.
Proof.
rewrite /Grover. apply: (RS_SC _ _ (RS_Grover_sub _)).
apply: (RS_SC _ _ (AxV_UT _)).
rewrite/= tlin_ket -[SPOST]tend1.
apply: (RS_back _ (tAxV_In _ )).
rewrite /= adj_dotEr VUnitaryE/=.
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
HB.instance Definition _ := isProjLf.Build _ solution solution_proj.

Lemma R_Grover (n : nat) : 
  ⊨ [pt] { ((sin (t *+ (2 * n + 1)))^+2)%:C%:D } 
    (Grover n) { '[(\sum_(i | Pw i) [> ''i ; ''i <]); x] }.
Proof.
move: (RS_Grover n)=>/saturated_weakS.
rewrite stateE; apply: R_Or.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
rewrite adjdZ muldZl muldZr conjC_real scalerA numd_adj numdM conjC1 
  mulr1 numdZ mulr1 -realcM -expr2/=; do 3 f_equal.
by rewrite [in RHS]addrC cosDpihalf sinN opprK.
rewrite tket_adj touterM/= tlin_le -/solution.
have ->: solution = HSType solution by rewrite hsE/=.
apply lef_outp.
rewrite hnorm_le1 dotpZl dotpZr vw_dot -!real2c conjC_real -!real2c
  mulrA -invfM -expr2 mulVf// expf_neq0//.
apply: memhZ; rewrite memhE hsE/= /vw/solution !linear_sum/=.
by apply/eqP; apply eq_bigr=>i Pi; rewrite linearZ/=; f_equal; 
  rewrite sum_lfunE (bigD1 i)//= big1=>[j/andP[] _/negPf nj|]; 
  rewrite outpE onb_dot ?nj ?scale0r// eqxx scale1r addr0.
Qed.

End GroverAlgorithm.
End GroverAlgorithm.

Module PhaseEstimation.
Section PhaseEstimation.
Variable (pt st : bool) (T : qType) (U : 'FU('Ht T)) (phi : 'Ht T) (theta : R).
(* since 'End[T] is a ringType, exp can be directly written as ^+ *)
Hypothesis (eigU : U phi = (expip (2%:R * theta) *: phi)).
Hypothesis (theta_bound : 0 <= theta < 1).
Variable (n : nat). (* control system *)
Variable (xy : 'QReg['I_n * T]).
Notation x := <{xy.1}>.
Notation y := <{xy.2}>.
Let eigUn m : ((U%:VF ^+ m)^A)%VF phi = expip (- (2%:R * theta * m%:R)) *: phi.
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
  [ut (x,y) := Uf ];;
  [ut x := IQFT ].

Let c (a : 'I_n.+1) := (\sum_(i < n.+1) expip (2%:R * (a%:R / n.+1%:R - theta) * i%:R)) / n.+1%:R.

Lemma RS_QPE (a : 'I_n.+1) : 
  ⊨s [pt,st] { c a *: '|phi; y> } QPE { '|''a; x> \⊗ '|phi; y> }.
Proof.
apply: (RS_SC _ _ (AxV_UT _)).
rewrite /= adjfK tketGTl//=; first by tac_qwhile_auto.
apply: (RS_SC _ _ (AxV_UT _)).
rewrite/= tketT tlin_ket//.
apply: (RS_SC _ _ (AxV_UT _)).
rewrite/= QFTEt QFTvE tentvZl tentv_suml linearZ/= linear_sum/= -tketZ -tket_sum dotdZr dotd_sumr.
have nxy : disjoint_qreg x y by tac_qwhile_auto.
under eq_bigr do rewrite tentvZl linearZ/= MultiplexerEVt /Uf_fun eigUn tentvZr 
  scalerA -tketZ dotdZr (tketGl _ _ _ _ nxy) tentf_apply lfunE/= tketTV !eq_qrE -tendZl tketZ.
rewrite -tend_suml -tendZl tket_sum [in SPOST]tketZ.
apply: (RS_back _ (tAxV_In _ )); last tac_qwhile_auto.
rewrite/= dotpZr dotp_sumr.
under eq_bigr do rewrite dotpZr adj_dotEr VUnitaryE/= dotp_uniformtvcb card_ord
  runityE -expipD natrM -!mulrA -mulrBr [_ / n.+1%:R]mulrC mulrA -mulrBl mulrA.
by rewrite -mulr_suml mulrC -mulrA -invfM -expr2 sqrtCK.
Qed.

Lemma RS_QPE_exact (a : 'I_n.+1) : 
  a%:R = theta * n.+1%:R ->
  ⊨s [pt,st] { '|phi; y> } QPE { '|''a; x> \⊗ '|phi; y> }.
Proof.
move=>P1; move: (RS_QPE a); 
by rewrite /c expip_sum_cst ?P1 ?mulfK ?mulfV/= ?scale1r// subrr mulr0 expip0.
Qed.

Lemma abs_expip_sin a : `|1 - expip (2%:R * a)| = 2%:R * `|sin (pi * a)|%:C.
Proof.
have ->: 2%:R * `|sin (pi * a)|%:C = `|2%:R * sinp a|%:C.
by rewrite [sinp]unlock normrM ger0_norm// realcM natrC.
rewrite [expip]unlock [sinp]unlock /expi; simpc; f_equal.
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
by rewrite mulfV ?natrS_neq0// normr1 lecR1 ler_pdivrMr ?pi_gt0// mul1r pi_ge2.
move: E; rewrite foo5; set t := a%:R / n.+1%:R - theta; move=>P1 P2.
have P4: `|t| <= (2%:R^-1)%R.
by apply: (le_trans _ P2); rewrite normrM ler_peMr// ger0_norm// ler1n.
have P5: `|t| < 1 by apply: (le_lt_trans P4); rewrite invf_lt1 ?ltr0n// ltr1n.
have P6 : `|pi * t| <= pi / 2%:R by rewrite normrM ger0_norm ?pi_ge0// ler_pM2l// ?pi_gt0.
have P7 : `|pi * (t * n.+1%:R)| <= pi / 2%:R.
  by rewrite normrM ger0_norm ?pi_ge0// ler_pM2l// ?pi_gt0.
rewrite expip_sum.
apply/expip_neq1; rewrite ?mulf_eq0 ?negb_or ?P1 ?andbT// !normrM 
  ger0_norm// gtr_pMr// ltr0n//.
rewrite !normrM !normfV -[_ * t * _]mulrA !abs_expip_sin [2%:R * _%:C]mulrC invfM mulrA mulfK//.
rewrite -natrC -realc_norm; simpc2r; rewrite lecR.
rewrite ler_pdivlMr ?normr_gt0// ler_pdivlMr.
apply: (lt_le_trans _ (ger_abs_sin P6)); rewrite !mulr_gt0// ?normrM 
  1?gtr0_norm ?mulr_gt0// ?invr_gt0 ?pi_gt0// normr_gt0 P1//.
apply: (le_trans _ (ger_abs_sin P7)). rewrite -!mulrA ler_pM2l ?ltr0n// mulrC ler_pM2r 
  ?invr_gt0 ?pi_gt0// mulrA normrM mulrC ler_pM2r ?ler_abs_sin// gtr0_norm ltr0n//.
Qed.

End PhaseEstimation.
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
rewrite rcosetE; apply/Coq.Bool.Bool.eq_iff_eq_true; split.
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

HB.instance Definition _ := GRing.isZmodule.Build ZZ ZZ_addA ZZ_addC ZZ_add0z ZZ_addNz.
HB.instance Definition _ := [finGroupMixin of ZZ for +%R].

(* Definition ZZ_zmodMixin := ZmodMixin ZZ_addA ZZ_addC ZZ_add0z ZZ_addNz.
Canonical ZZ_zmodType := Eval hnf in ZmodType ZZ ZZ_zmodMixin.
Canonical ZZ_finZmodType := Eval hnf in [finZmodType of ZZ].
Canonical ZZ_baseFinGroupType := Eval hnf in [baseFinGroupType of ZZ for +%R].
Canonical ZZ_finGroupType := Eval hnf in [finGroupType of ZZ for +%R]. *)
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

Lemma com1q S (e : 'Bra[H]_S) : :1 \o e = e.
Proof. by rewrite -dotd_mul/= dot1d. Qed.
Lemma muld1 S (e : 'Ket[H]_S) : e \o :1 = e.
Proof. by rewrite -dotd_mul/= dotd1. Qed.

End lfunsemExtra. *)

Module HSP.
Section HSP.
Variable (n : nat) (fn : 'I_n.+1 -> nat).
Notation G := {dffun forall i : 'I_n.+1, ('I_(fn i).+2)}.
Variable (H : {group G}). (* provide a group *)

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
apply /(intro_onb t2tv)=>i; apply/(intro_onbl t2tv)=>j.
rewrite/= ![in LHS]t2tv_dffun FG_apply tentf_dffun_apply tentv_dffun_dot.
rewrite dotpZr dotp_sumr (bigD1 j)//= [in RHS]big1=>[k/negPf nk|];
rewrite dotpZr ?ns_dot ?onb_dot 1?eq_sym ?nk ?mulr0// addr0 mulr1.
under eq_bigr do rewrite QFTEt dotp_cbQFT.
rewrite big_split/= -invf_prod -sqrt_prod=>[k _//|].
rewrite -natr_prod card_dffun; under [in RHS]eq_bigr do rewrite card_ord.
by f_equal; apply eq_bigr=>k _; rewrite runityE mulnC natrM mulrA.
Qed.

Lemma FG_unitary : FG \is unitarylf.
Proof. by rewrite -QFT_FG_apply is_unitarylf. Qed.
HB.instance Definition _ := isUnitaryLf.Build _ FG FG_unitary.

Lemma cardH : #|H|%:R != 0 :> C.
Proof. by rewrite pnatr_eq0 lt0n_neq0// cardG_gt0. Qed.
Let cardH := cardH.
Lemma cardZZ : #|G|%:R != 0 :> C.
Proof. rewrite pnatr_eq0 lt0n_neq0//; by move: (cardg_gt0 G). Qed.
Let cardZZ := cardZZ.

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
rewrite -{2}(sqrtCK #|H|%:R) expr2 mulrA mulrACA mulVf ?sqrtC_eq0//
  mul1r sqrtCM// 1?mulrC// ?sqrtC_inv// nnegrE invr_ge0//.
Qed.

Lemma FG_tauC (t : {set G}) : (FG \o (tau t) = (phi t) \o FG)%VF.
Proof.
rewrite /FG linearZl linearZr/=; f_equal.
rewrite /tau {1}exchange_big/= linear_sumr/= [LHS](eq_bigr (fun i=>
(phi t \o (\sum_j charZZ j i *: [> ''j ; ''i <]) )%VF))=>[i _|]; last first.
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


Variable (m : nat) (ff : G -> 'I_m.+1). (* auxiliary system, oracle *)
Hypotheses (Hff_eq : forall (i j : G), (i \in (H :* j)%g) <-> ff i = ff j).

Variable (xy : 'QReg[{qffun forall i, 'I_(fn i).+1} * 'I_m]).
Notation x := <{xy.1}>.
Notation y := <{xy.2}>.
Notation X := 'I_m.+1.
(* Check 'I_m.+1 : finZmodType.
Variable (x : forall i, vars ('I_(fn i).+2)).
Notation px := (pvars_dffun disx).
Hypothesis (disx : forall i j, i != j -> [disjoint lb (x i) & lb (x j)]).
Variable (y : vars X).
Hypothesis (disy : [disjoint lb (pvars_dffun disx) & lb y]). *)
(* Notation t0 := (ord0 : X). *)

Definition HSP :=
  [for i do [it x.-[i] := ''ord0 ]];;
  [it y := ''ord0 ];;
  [for i do [ut x.-[i] := QFT ]];;
  [ut (x,y) := Oracle ff ];;
  [for i do [ut x.-[i] := QFT ]].

Lemma inr i : i \in [set rcoset H x0 | x0 : G] -> (i = H :* (repr i))%g.
Proof. by move/imsetP=>[z Pz Pi]; rewrite Pi rcosetE rcoset_repr. Qed.

Let i0 := [ ffun i : 'I_n.+1 => ord0] : {dffun forall i : 'I_n.+1, 'I_(fn i).+2}.
Lemma Di0 i : charZZ i i0 = 1.
Proof. by rewrite/charZZ big1// =>k _; rewrite ffunE mulr0 mul0r expip0. Qed.

Let vf : 'Ht ({qffun forall i, 'I_(fn i).+1} * 'I_m) := 
  (#|H|%:R / #|G|%:R) *: (\sum_(j in HC) (''j ⊗t 
    \sum_(i in [set rcoset H x0 | x0 : {dffun forall i1 : 'I_n.+1, 'I_(fn i1).+2}]) 
       (charZZ j (repr i) *: ''(ord0 + ff (repr i))))).

Lemma vfE : (FG ⊗f \1) (Oracle ff ((FG ⊗f \1) (''i0 ⊗t ''ord0))) = vf.
Proof.
rewrite tentf_apply FG_apply lfunE/= tentvZl tentv_suml !linearZ/= linear_sum/=.
rewrite (big_rcoset_partition H)/= /vf (eq_bigr (fun j=> (sqrtC #|H|%:R) *: 
  ((tau j H_state) ⊗t ''(ord0 + ff (repr j))) )).
move=>i /inr P1; rewrite /H_state linearZ/= tentvZl scalerA mulfV ?sqrtC_eq0//
 scale1r linear_sum/= tentv_suml; apply eq_bigr=>k inK.
rewrite Di0 scale1r OracleEt; do 3 f_equal.
by rewrite /tau sum_lfunE (bigD1 k)//= big1=>[j/negPf nj|]; 
  rewrite outpE ?ns_dot ?onb_dot ?nj ?scale0r// scale1r addr0.
by apply/Hff_eq/rcoset_eqP; rewrite rcosetM [(H :* k)%g]rcoset_id.
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
by move: (is_unitarylf f)=>/unitarylf_dotP/(_ v)/eqP;
rewrite !dotp_norm eqrXn2// =>/eqP.
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
Proof. by rewrite -vfE !unitaryf_norm tentv_t2tv ns_norm. Qed.

Lemma cardHC : #|HC|%:R = #|G|%:R / #|H|%:R :> C.
Proof.
move: vf_norm1=>/(f_equal (fun x=>x^+2)).
rewrite expr1n hnormZ exprMn ortho_norm=>[i j _ _ /negPf ni|].
by rewrite tentv_dot onb_dot ni mul0r.
rewrite (eq_bigr (fun=>#|G|%:R / #|H|%:R))=>[i Pi|].
rewrite tentv_norm ns_norm mul1r ortho_norm=>[j k/inr Pj/inr Pk njk|].
by rewrite dotpZl dotpZr onb_dot (can_eq (addKr ord0)) Hff_neq// !mulr0.
under eq_bigr do rewrite hnormZ charZZ_norm mul1r ns_norm expr1n.
by rewrite sumr_const H_rcoset_card.
rewrite sumr_const -[_ *+ #|HC|]mulr_natl ger0_norm ?divr_ge0// mulrC expr2.
rewrite !mulrA mulfVK// mulfK// -[X in _ -> _ = X]mulr1=>P1.
rewrite -{4}P1 [RHS]mulrC !mulrA mulfVK// mulfK//.
Qed.

Lemma RS_HSP pt st : ⊨s [pt,st] { :1 } HSP { '|vf ; (x,y)>}.
Proof.
rewrite /HSP -!fsem_seqA.
apply: (RS_SC _ (tAxV_InFP_seq _ _ _))=>/=[|//|? _|]; 
  rewrite ?disjoint0X//=; try tac_qwhile_auto.
apply: (RS_SC _ (tAxV_InF _))=>/=;
  first by rewrite setU0; tac_qwhile_auto.
apply: (RS_SC _ (AxV_UTFP_ffun _ _ _))=>//=.
rewrite tend1 -tlinTV -tketTV/= tketGTr/=; first by tac_qwhile_auto.
  rewrite QFT_FG_apply tendC tketT.
apply: (RS_SC _ (AxV_UTF _))=>//=.
rewrite tlin_ket.
apply: (RS_forward _ (AxV_UTFP_ffun _ _ _))=>/=.
rewrite -tlinTV QFT_FG_apply tketGl; first by tac_qwhile_auto.
rewrite -vfE tentf_apply [\1 _]lfunE/= t2tv_dffun/=.
by under [in RHS]eq_tentv_dffun do rewrite ffunE.
Qed.

Lemma HSP_no_while : no_while HSP.
Proof. by rewrite/= !no_while_for. Qed.
Let HSP_no_while := HSP_no_while.
Lemma HSP_is_valid : cmd_valid HSP.
Proof. by rewrite /HSP; tac_qwhile_auto. Qed.
Canonical HSP_valid := WF_CMD HSP_is_valid.
(* Let HSP_valid := HSP_valid. *)

Lemma disy : [disjoint mset x & mset y]. Proof. by tac_qwhile_auto. Qed.

Lemma R_HSP_notin pt st i : 
  i \notin HC -> ⊨ [pt,st] { 0 } HSP { '[ [> ''i ; ''i <] ; x ] }.
Proof.
move=>Pi; apply/no_while_enough=>//=.
move: (RS_HSP true true); rewrite stateE numd_adj numdM conjC1 mulr1 tket_adj touterM=>IH.
apply: (R_back _ (tR_PInnerl disy ''i _ IH)); last by rewrite vf_norm1.
rewrite big1 ?numd0// =>j _; rewrite /vf linearZ/= linear_sumr/= big1=>[k nk|].
by rewrite tentv_dot onb_dot; move: Pi=>/memPnC/(_ _ nk)/negPf->; rewrite mul0r.
by rewrite mulr0 normr0 expr0n.
Qed.

Definition PX (i : 'I_m.+1) := 
  [exists j, (j \in [set rcoset H x0 | x0 : G]) && (i == (ord0 + ff (repr j)))].

Lemma cardPX : #|PX| = #|[set rcoset H x0 | x0 : G]|.
Proof.
suff : #|[finType of {i : X | PX i}]| = #|[finType of {i | i \in [set rcoset H x0 | x0 : G]}]|.
by rewrite !card_sig.
pose H1 (j : {i : X | PX i}) := sigW (existsP (projT2 j)).
have H2 (j : {i : X | PX i}) : projT1 (H1 j) \in [set rcoset H x0 | x0 : G].
by move: (projT2 (H1 j))=>/andP[].
pose fb (j : {i : X | PX i}) : {i | i \in [set rcoset H x0 | x0 : G]} 
  := exist _ (projT1 (H1 j)) (H2 j).
have Ef j : val j = ord0 + ff (repr (val (fb j))).
by move: (projT2 (H1 j))=>/andP[] _/eqP.
have Ff j : val (fb j) = (projT1 (H1 j)). by [].
have H3 (j : {i | i \in [set rcoset H x0 | x0 : G]}) : PX (ord0 + ff (repr (projT1 j))).
by rewrite/PX; apply/existsP; exists (projT1 j); rewrite eqxx; move: (projT2 j)=>->.
pose gb (j : {i | i \in [set rcoset H x0 | x0 : G]}) : {i : X | PX i}
  := exist _ (ord0 + ff (repr (projT1 j))) (H3 j).
have Eg j : val (gb j) = ord0 + ff (repr (val j)). by [].
have Fg j : projT1 (gb j) = (ord0 + ff (repr (projT1 j))). by [].
apply: (@bij_eq_card _ _ fb).
exists gb. move=>i. apply/val_inj. by rewrite Eg -Ef.
move=>i. apply/val_inj. rewrite Ff.
move: (projT2 (H1 (gb i)))=>/andP[]/inr P1/eqP.
rewrite {1}Fg=>/addrI/Hff_eq/rcoset_eqP; rewrite -P1=><-.
by move: (projT2 i)=>/inr<-.
Qed.

Lemma R_HSP_in pt st i : 
  i \in HC -> ⊨ [pt,st] { ((#|HC|%:R)^-1)%R%:D } HSP { '[ [> ''i ; ''i <] ; x ] }.
Proof.
move=>Pi; apply/no_while_enough=>//.
move: (RS_HSP true true); rewrite stateE numd_adj numdM conjC1 mulr1 tket_adj touterM=>IH.
apply: (R_back _ (tR_PInnerl disy ''i _ IH)); last by rewrite vf_norm1.
f_equal. rewrite /vf.
rewrite (eq_bigr (fun i1=> `|#|H|%:R / #|G|%:R *
  (\sum_(v in [set rcoset H x0 | x0 : G]) charZZ i (repr v) * 
    (i1 == (ord0 + ff (repr v)))%:R) | ^+ 2)).
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
  i \notin HC -> ⊨s [pt,st] { 0 } HSP { '|''i ⊗t ''t; (x,y) >}.
Proof.
move=>Pi. apply/no_while_enoughS=>//.
apply: (RS_back _ (tRV_Inner _ _ (RS_HSP true true))).
rewrite /vf dotpZl dotp_suml big1 ?mulr0 ?normr0 ?numd0//  =>j Pj.
rewrite tentv_dot onb_dot eq_sym.
by move: Pi=>/memPnC/(_ _ Pj)/negPf->; rewrite mul0r.
by rewrite vf_norm1.
Qed.

Lemma RS_HSP_in pt st i (t : {set G}): 
  i \in HC -> t \in [set rcoset H x0 | x0 : G] ->
   ⊨s [pt,st] { (#|H|%:R / #|G|%:R)%:D } HSP { '|''i ⊗t ''(ord0 + ff (repr t)); (x,y) >}.
Proof.
move=>Pi /inr Pt. apply/no_while_enoughS=>//.
apply: (RS_back _ (tRV_Inner _ _ (RS_HSP true true))).
f_equal. rewrite /vf dotpZl dotp_suml normrM norm_conjC [ `|_ / _|]ger0_norm
  ?divr_ge0// -[RHS]mulr1; f_equal.
rewrite (bigD1 i)//= [X in _ + X]big1=>[j/andP[_ /negPf nj]|].
by rewrite tentv_dot onb_dot nj mul0r.
rewrite tentv_dot ns_dot mul1r (bigD1 (rcoset H (repr t)))/=.
by apply/imsetP; exists (repr t).
rewrite dotpDl dotp_suml ?big1=>[j/andP[/inr Pj]|].
rewrite rcosetE -Pt=>nj.
by rewrite dotpZl onb_dot (can_eq (addKr ord0)) Hff_neq// !mulr0.
by rewrite rcosetE -Pt dotpZl ns_dot mulr1 !addr0 norm_conjC charZZ_norm.
by rewrite vf_norm1.
Qed.

End HSP.
End HSP.
