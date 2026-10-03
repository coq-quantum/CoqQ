(* Classical: algorithms. See README.md and PROOF_NOTES.md. *)
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
From mathcomp.analysis Require Import exp trigo.
From quantum Require Import qtype.
From mathcomp Require Import all_ssreflect finmap perm.
From mathcomp Require Import all_ssreflect.
From quantum Require Import mcextra mcaextra notation mxpred svd mxnorm
  hermitian ctopology quantum hspace inhabited.
From mathcomp Require Import all_ssreflect finmap field_tactic ring_tactic.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module ClassicalGrover.
Import trigo.
(* Grover's search, classical.pdf Examples 4.5/4.11 and Section 7.1.
   The concrete phase-oracle/reflection algebra adapts CoqQ's upstream
   example/coqq_paper/example.v, GroverAlgorithm (MIT; see
   UPSTREAM-LICENSE). The program uses a classical counted while loop. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.
Ltac simpc2r := rewrite -?(natrC, realcN, realcD, realcM, realcI, realcX, realc_norm).

Section Grover.
Variable (T : qType) (q : wf_qreg T).
Notation TT := (eval_qtype T).
Variable (Pw : pred TT).
Hypothesis card_Pw : (0 < #|Pw| < #|TT|)%N.
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
apply/unitarylfP; rewrite /Ut0 adjfB adjf1 adjfZ conjC_nat adj_outp.
rewrite linearBr/= !linearBl/= !comp_lfun1l comp_lfun1r linearZl/= linearZr/=.
rewrite scalerA outp_comp ns_dot scale1r opprB -scalerBl [\1 - _]addrC.
by rewrite addrA -scalerBl mulr_natr mulr2n addrK subrr scale0r add0r.
Qed.
HB.instance Definition _ := isUnitaryLf.Build _ Ut0 Ut0_unitary.
Lemma Us_unitary : Us \is unitarylf.
Proof. by rewrite Us_diffE is_unitarylf. Qed.
HB.instance Definition _ := isUnitaryLf.Build _ Us Us_unitary.

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

Let solution := (\sum_(i | Pw i) [> ''i ; ''i <]).
Lemma solution_proj : solution \is projlf.
Proof.
apply/projlfP; split.
by rewrite /solution raddf_sum/=; under eq_bigr do rewrite adj_outp.
rewrite /solution linear_sumlz/=; apply eq_bigr=>i Pi.
rewrite linear_sumr/= (bigD1 i)//= big1=>[j/andP[] _/negPf nj|];
by rewrite outp_comp ?ns_dot ?scale1r ?addr0// onb_dot eq_sym nj scale0r.
Qed.
HB.instance Definition _ := isProjLf.Build _ solution solution_proj.

Lemma solution_vw : solution vw = vw.
Proof.
rewrite /solution /vw linearZ/= linear_sum/=; congr (_ *: _).
apply eq_bigr=>i Pi; rewrite sum_lfunE (bigD1 i)//= big1.
- by move=>j /andP[_]/negPf nj; rewrite outpE onb_dot nj scale0r.
- by rewrite outpE ns_dot scale1r addr0.
Qed.

Lemma solution_vwc : solution vwc = 0.
Proof.
rewrite /solution /vwc linearZ/= linear_sum/= big1 ?scaler0// =>i /negPf Pi.
rewrite sum_lfunE big1// =>j Pj; rewrite outpE onb_dot.
case: eqP=>[E|_]; last by rewrite scale0r.
by rewrite -E Pj in Pi.
Qed.

Lemma uw_initial : uw t = us.
Proof.
by rewrite /uw !divff ?sint_neq0 ?cost_neq0// ?natrC !scale1r -us_vwE.
Qed.

Lemma solution_uw r : solution (uw r) = (sin r / sin t)%:C *: vw.
Proof. by rewrite /uw linearP/= solution_vw [solution (_ *: vwc)]linearZ/= solution_vwc scaler0 addr0. Qed.

Lemma uw_success r : [<uw r; solution (uw r)>] = (sin r ^+ 2)%:C.
Proof.
rewrite solution_uw /uw dotpDl
  (dotpZl ((sin r / sin t)%:C)) (dotpZl ((cos r / cos t)%:C))
  !(dotpZr ((sin r / sin t)%:C)) vw_dot
  -[ [<vwc; vw>] ]conj_dotp vw_vwc_dot conjC0 !mulr0 addr0
  conjC_real.
simpc2r; congr (_%:C).
by rewrite mulrA -expr2 -exprMn divfK.
Qed.

Definition phase_angle : R := t.
Definition phase_state (r : R) : 'Ht T := uw r.
Definition success_effect : 'FP('Ht T) := [proj of solution].

Definition rotation : 'FU('Ht T) := [unitary of (Us \o Uw)%VF].

Definition counter_increment (x : variable Integer) : command :=
  Assign x (EApp (EConst (fun z : int => z + 1)) (EVar x)).

Definition grover_prefix (K : nat) (x : variable Integer) : command :=
  Sequence (Initialize q (EConst (zero_state T)))
  (Sequence (Unitary q (EConst (@uniformtf TT)))
  (Sequence (Assign x (EConst (0 : int)))
    (While (EApp (EConst (fun z : int => z < Posz K)) (EVar x))
      (Sequence (Unitary q (EConst rotation)) (counter_increment x))))).

Definition grover (K : nat) (x : variable Integer)
    (y : variable (QType T)) : command :=
  Sequence (grover_prefix K x) (Measure y q (EConst [QM of @tmeas TT])).

Definition iteration_state (n : nat) := iter n rotation us.
Definition success_probability (n : nat) : R := (sin (t *+ (2 * n + 1))) ^+ 2.

Lemma iteration_state_dot n : [<iteration_state n; iteration_state n>] = 1.
Proof.
elim: n=>[|n IH].
- exact: ns_dot.
- by rewrite /iteration_state iterS isof_dot -/(iteration_state n) IH.
Qed.
HB.instance Definition _ n := isNormalState.Build ('Ht T)
  (iteration_state n) (iteration_state_dot n).

Lemma success_probability_ge0 n : 0 <= success_probability n.
Proof. exact: sqr_ge0. Qed.
Lemma success_probability_le1 n : success_probability n <= 1.
Proof.
rewrite /success_probability -[1](cos2Dsin2 (t *+ (2 * n + 1))) ?lerDl ?lerDr.
exact: sqr_ge0.
Qed.

Lemma iteration_stateE n : iteration_state n = uw (t + t *+ (2 * n)).
Proof.
elim: n=>[|n IH].
- by rewrite /iteration_state /= muln0 mulr0n addr0 uw_initial.
- rewrite /iteration_state iterS -/(iteration_state n) IH /rotation UsUwE_ind.
  congr (uw _).
  have En : (2 * n.+1 = 2 * n + 2)%N by rewrite mulnS addnC.
  by rewrite En [t *+ (2 * n + 2)]mulrnDr mulr2n !addrA.
Qed.

Lemma iteration_success n :
  [<iteration_state n; success_effect (iteration_state n)>] = (success_probability n)%:C.
Proof.
rewrite iteration_stateE uw_success /success_probability.
by rewrite [t *+ (2 * n + 1)]mulrnDr mulr1n addrC.
Qed.

End Grover.
End ClassicalGrover.


Module ClassicalFourier.
(* Quantum Fourier circuit, classical.pdf Section 7.2.
   See PROOF_NOTES.md; reference proof patterns are MIT-licensed. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition tuple_fourier n : 'FU('Hs (n.-tuple bool)) :=
  PUnitary t2tv (@QFTbv n).

Definition single_hadamard n (k : 'I_n) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of tentf_tuple (fun i : 'I_n =>
    if i == k then (Hadamard : 'FU('Hs bool)) else (\1 : 'FU('Hs bool)))].

Definition controlled_phase n (k j : 'I_n) (theta : R) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of expmxip t2tv
    (fun z : n.-tuple bool => ((z~_k) && (z~_j))%:R) (2 * theta)].

Definition reversal n : 'FU('Hs (n.-tuple bool)) :=
  [unitary of permtf bool (perm (@rev_ord_inj n))].

Lemma single_hadamard_product n (k : 'I_n) (v : 'I_n -> 'Hs bool) :
  single_hadamard k (tentv_tuple v) =
  tentv_tuple (fun i => if i == k then Hadamard (v i) else v i).
Proof.
rewrite /single_hadamard tentf_tuple_apply; apply: eq_tentv_tuple=>i.
by case: (i == k); rewrite /= ?lfunE.
Qed.

Lemma diagonal_amplitude n (d : n.-tuple bool -> R) theta
    (v : 'Hs (n.-tuple bool)) z :
  [< ''z; expmxip t2tv d theta v >] = expip (d z * theta) * [< ''z; v >].
Proof.
by rewrite -adj_dotEl expmxip_adj expmxipEt dotpZl -expipNC mulrN opprK.
Qed.

Lemma controlled_phase_amplitude n (k j : 'I_n) theta (v : 'Hs (n.-tuple bool)) z :
  [< ''z; controlled_phase k j theta v >] =
  expip (((z~_k) && (z~_j))%:R * (2 * theta)) * [< ''z; v >].
Proof. exact: diagonal_amplitude. Qed.

Lemma reversal_product n (v : 'I_n -> 'Hs bool) :
  reversal n (tentv_tuple v) = tentv_tuple (fun i => v (rev_ord i)).
Proof. by rewrite /reversal permtfEtv; apply: eq_tentv_tuple=>i; rewrite permE. Qed.

Lemma hadamard_phase b : Hadamard ''b = phstate (b%:R / 2).
Proof.
rewrite Hadamard_cb; rude_bmx; case: b=>/=;
by rewrite ?mul0r ?mulr0 ?expip0 ?mul1r ?mulfV // ?mulr1 ?expip1.
Qed.

Lemma phase_shift_amplitude b r theta :
  [< ''b; phstate (r + theta) >] =
    expip (2 * b%:R * theta) * [< ''b; phstate r >].
Proof. by rewrite !dotp_cbph mulrDr expipD mulrA [RHS]mulrC. Qed.

Definition tensor_replace n (k : 'I_n) (v : 'I_n -> 'Hs bool) u :=
  tentv_tuple (fun i => if i == k then u else v i).

Lemma tensor_replace_amplitude n (k : 'I_n) (v : 'I_n -> 'Hs bool) u z :
  [< ''z; tensor_replace k v u >] =
  [< ''(z~_k); u >] * \prod_(i | i != k) [< ''(z~_i); v i >].
Proof.
rewrite /tensor_replace t2tv_tuple tentv_tuple_dot (bigD1 k) //= eqxx.
f_equal; apply: eq_bigr=>i /negPf ik; by rewrite ik.
Qed.

Lemma tensor_phase_shift n (k : 'I_n) (v : 'I_n -> 'Hs bool) r theta z :
  [< ''z; tensor_replace k v (phstate (r + theta)) >] =
  expip (2 * (z~_k)%:R * theta) * [< ''z; tensor_replace k v (phstate r) >].
Proof. by rewrite !tensor_replace_amplitude phase_shift_amplitude mulrA. Qed.

Lemma tensor_basis_zero n (j : 'I_n) (v : 'I_n -> 'Hs bool) (d : bool) z :
  v j = ''d -> z~_j != d -> [< ''z; tentv_tuple v >] = 0.
Proof.
move=>vj /negPf zd; rewrite t2tv_tuple tentv_tuple_dot (bigD1 j) //= vj.
by rewrite onb_dot zd mul0r.
Qed.

Lemma controlled_phase_product n (k j : 'I_n) theta r d (v : 'I_n -> 'Hs bool) :
  k != j -> v k = phstate r -> v j = ''d ->
  controlled_phase k j theta (tentv_tuple v) =
    tensor_replace k v (phstate (r + d%:R * theta)).
Proof.
move=>kj vk vj; apply/(intro_onbl t2tv)=>z.
rewrite controlled_phase_amplitude.
have Ev : tensor_replace k v (phstate r) = tentv_tuple v.
  apply: eq_tentv_tuple=>i; case: eqP=>[->|] //; exact: esym vk.
case: (boolP (z~_j == d))=>[/eqP zd|zd].
- rewrite tensor_phase_shift Ev zd.
  congr (expip _ * _); clear vj zd.
  by case: (z~_k); case: d; rewrite /= ?mul0r ?mulr0 ?mul1r ?mulr1 ?mul0r.
- rewrite (tensor_basis_zero vj zd) mulr0; symmetry.
  apply: (@tensor_basis_zero n j _ d z) zd.
  by rewrite eq_sym (negPf kj).
Qed.

Lemma tensor_replace_id n (k : 'I_n) (v : 'I_n -> 'Hs bool) :
  tensor_replace k v (v k) = tentv_tuple v.
Proof. apply: eq_tentv_tuple=>i; by case: eqP=>[->|]. Qed.

Lemma tensor_replace_twice n (k : 'I_n) (v : 'I_n -> 'Hs bool) u w :
  tensor_replace k (fun i => if i == k then u else v i) w =
  tensor_replace k v w.
Proof. apply: eq_tentv_tuple=>i; by case: (i == k). Qed.

Definition phase_chain n (k : 'I_n) (theta : 'I_n -> R)
    (js : seq 'I_n) (v : 'Hs (n.-tuple bool)) :=
  foldl (fun w j => controlled_phase k j (theta j) w) v js.

Lemma phase_chain_product n (k : 'I_n) (theta : 'I_n -> R)
    (js : seq 'I_n) (v : 'I_n -> 'Hs bool) (d : 'I_n -> bool) r :
  (forall j, j \in js -> k != j /\ v j = ''(d j)) ->
  phase_chain k theta js (tensor_replace k v (phstate r)) =
  tensor_replace k v (phstate (r + \sum_(j <- js) (d j)%:R * theta j)).
Proof.
elim: js v r=>[v r H|j js IH v r H].
  by rewrite /phase_chain /= big_nil addr0.
have [kj vj] := H j (mem_head j js).
have Hj : (fun i => if i == k then phstate r else v i) j = ''(d j).
  by rewrite eq_sym (negPf kj).
have Hk : (fun i => if i == k then phstate r else v i) k = phstate r.
  by rewrite eqxx.
rewrite /phase_chain /= -/(phase_chain _ _ _ _).
rewrite (@controlled_phase_product n k j (theta j) r (d j) _ kj Hk Hj)
  tensor_replace_twice.
have Htail : forall i, i \in js -> k != i /\ v i = ''(d i).
  by move=>i Hi; apply: H; rewrite in_cons Hi orbT.
by rewrite (IH _ _ Htail) big_cons addrA.
Qed.

Lemma bitstr2rat_sum (bs : seq bool) :
  bitstr2rat bs =
    \sum_(0 <= j < size bs) (nth false bs j)%:R / 2 ^+ j.+1.
Proof.
elim: bs=>[|b bs IH].
  by rewrite [bitstr2rat]unlock big_geq.
rewrite bitstr_cons IH /= big_nat_recl //= expr1; congr (_ + _).
rewrite big_distrl /=; apply: eq_bigr=>j _.
by rewrite [2 ^+ j.+2]exprSr invfM mulrA.
Qed.

Lemma bitstr2rat_drop_sum n (bs : n.-tuple bool) k :
  bitstr2rat (drop k bs) =
    \sum_(j < n | (k <= j)%N) (bs~_j)%:R / 2 ^+ (j - k).+1.
Proof.
rewrite bitstr2rat_sum size_drop size_tuple.
transitivity (\sum_(k <= j < n) (nth false bs j)%:R / 2 ^+ (j - k).+1 : R).
- rewrite -[in RHS](add0n k) big_addn; apply: eq_bigr=>j _.
  by rewrite nth_drop addnK addnC.
- rewrite (big_nat_widenl k 0) // big_mkord.
  apply: eq_big=>j; first by rewrite andTb.
  by move=>_; rewrite (tnth_nth false).
Qed.

Definition control_indices n (k : 'I_n) :=
  seq.filter (fun j : 'I_n => (k < j)%N) (enum 'I_n).
Definition phase_angle n (k j : 'I_n) : R := (2 ^+ (j - k).+1)^-1.
Definition stage_factors n (bs : n.-tuple bool) k (i : 'I_n) : 'Hs bool :=
  if (i < k)%N then phstate (bitstr2rat (drop i bs)) else ''(bs~_i).
Definition stage n (bs : n.-tuple bool) k := tentv_tuple (stage_factors bs k).

Lemma suffix_angle n (bs : n.-tuple bool) (k : 'I_n) :
  (bs~_k)%:R / 2 +
    \sum_(j <- control_indices k) (bs~_j)%:R * phase_angle k j =
  bitstr2rat (drop k bs).
Proof.
rewrite bitstr2rat_drop_sum (bigD1 k) //= subnn expr1.
congr (_ + _); rewrite /control_indices big_filter /phase_angle.
rewrite enumT [index_enum _]unlock.
apply: eq_bigl=>j; case: (eqVneq j k)=>[->|jk].
  by rewrite ltnn ?eqxx ?andbF.
by rewrite [(k <= j)%N]leq_eqVlt (val_eqE k j) eq_sym (negPf jk) /= ?andbT.
Qed.

Lemma stage_hadamard n (bs : n.-tuple bool) (k : 'I_n) :
  single_hadamard k (stage bs k) =
  tensor_replace k (stage_factors bs k) (phstate ((bs~_k)%:R / 2)).
Proof.
rewrite single_hadamard_product; apply: eq_tentv_tuple=>i.
case: eqP=>[->|] //; by rewrite /stage_factors ltnn hadamard_phase.
Qed.

Lemma stage_phase_layer n (bs : n.-tuple bool) (k : 'I_n) :
  phase_chain k (phase_angle k) (control_indices k)
    (single_hadamard k (stage bs k)) = stage bs k.+1.
Proof.
rewrite stage_hadamard.
have Hcontrol j : j \in control_indices k ->
    k != j /\ stage_factors bs k j = ''(bs~_j).
  rewrite /control_indices mem_filter=>/andP[kj _]; split.
    by apply/eqP=>E; move: kj; rewrite E ltnn.
  by rewrite /stage_factors ltnNge (ltnW kj).
rewrite (phase_chain_product _ _ Hcontrol) suffix_angle.
apply: eq_tentv_tuple=>i; rewrite /stage_factors.
case: eqP=>[->|/eqP ik].
  by rewrite ltnSn.
by rewrite ltnS [(i <= k)%N]leq_eqVlt (val_eqE i k) (negPf ik).
Qed.

Fixpoint unitary_list (H : chsType) (us : seq 'FU(H)) : 'FU(H) :=
  if us is u :: us' then [unitary of (unitary_list us') \o u]
  else (\1 : 'FU(H)).

Lemma unitary_listE (H : chsType) (I : Type) (us : I -> 'FU(H)) js v :
  unitary_list [seq us j | j <- js] v = foldl (fun w j => us j w) v js.
Proof.
elim: js v=>[|j js IH] v; first by rewrite /= lfunE.
rewrite /= lfunE /=; exact: IH.
Qed.

Lemma unitary_list_rcons (H : chsType) (us : seq 'FU(H)) u v :
  unitary_list (rcons us u) v = u (unitary_list us v).
Proof.
elim: us v=>[|u0 us IH] v; first by rewrite /= !lfunE /= id_lfunE.
rewrite /= !lfunE /=; exact: IH.
Qed.

Definition phase_layer n (k : 'I_n) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of (unitary_list [seq controlled_phase k j (phase_angle k j) |
    j <- control_indices k]) \o single_hadamard k].

Lemma phase_layerE n (k : 'I_n) v :
  phase_layer k v = phase_chain k (phase_angle k) (control_indices k)
    (single_hadamard k v).
Proof. by rewrite /phase_layer lfunE /= unitary_listE. Qed.

Definition circuit_prefix n k : 'FU('Hs (n.-tuple bool)) :=
  unitary_list [seq phase_layer i | i <- take k (enum 'I_n)].
Definition fourier_circuit n : 'FU('Hs (n.-tuple bool)) :=
  [unitary of reversal n \o circuit_prefix n n].

Lemma stage_initial n (bs : n.-tuple bool) : stage bs 0 = ''bs.
Proof.
rewrite /stage t2tv_tuple; apply: eq_tentv_tuple=>i.
by rewrite /stage_factors ltn0.
Qed.

Lemma stage_final n (bs : n.-tuple bool) : reversal n (stage bs n) = QFTbv bs.
Proof.
rewrite /stage reversal_product QFTbvTE; apply: eq_tentv_tuple=>i.
by rewrite /stage_factors ltn_ord /= subnS predn_sub.
Qed.

Lemma circuit_prefix_basis n (bs : n.-tuple bool) k :
  (k <= n)%N -> circuit_prefix n k ''bs = stage bs k.
Proof.
elim: k=>[|k IH] Hkn.
- by rewrite /circuit_prefix take0 /= lfunE stage_initial.
- have Hk : (k < n)%N := Hkn.
  pose i : 'I_n := Ordinal Hk.
  rewrite /circuit_prefix (take_nth i) ?size_enum_ord //.
  rewrite (nth_ord_enum i i) map_rcons unitary_list_rcons
    -/(circuit_prefix n k) (IH (ltnW Hk)) phase_layerE.
  exact: stage_phase_layer.
Qed.

Theorem fourier_circuit_basis n (bs : n.-tuple bool) :
  fourier_circuit n ''bs = QFTbv bs.
Proof.
by rewrite /fourier_circuit lfunE /= circuit_prefix_basis // stage_final.
Qed.

Theorem fourier_circuit_correct n :
  (fourier_circuit n : 'End('Hs (n.-tuple bool))) = tuple_fourier n.
Proof.
apply/(intro_onb t2tv)=>bs.
by rewrite fourier_circuit_basis /tuple_fourier PUnitaryE.
Qed.
End ClassicalFourier.


Module ClassicalPhaseProbability.
(* Generic Born-event complement bound; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Import ClassicalSemantics.
Local Notation C := hermitian.C.

Lemma born_total (H : chsType) (T : finType) (b : 'ONB(T;H)) (psi : H) :
  \sum_(i : T) `|[< b i; psi >]|^+2 = [< psi; psi >].
Proof.
symmetry; rewrite {1}(onb_vec b psi) dotp_suml.
by apply: eq_bigr=>i _; rewrite dotpZl -normCKC.
Qed.

Theorem onb_event_complement_bound (H : chsType) (T : finType)
    (b : 'ONB(T;H)) (psi : H) (P : pred T) (m0 : T) :
  [< psi; psi >] = 1 -> ~~ P m0 ->
  \sum_(m : T | P m) `|[< b m; psi >]|^+2 <=
    1 - `|[< b m0; psi >]|^+2.
Proof.
move=>Hpsi HP.
have Et := born_total b psi.
rewrite Hpsi (bigD1 m0) //= in Et.
have Hsub : \sum_(m : T | P m) `|[< b m; psi >]|^+2 <=
    \sum_(m : T | m != m0) `|[< b m; psi >]|^+2.
  rewrite [X in X <= _]big_mkcond [X in _ <= X]big_mkcond.
  apply: ler_sum=>m _.
  case EP: (P m).
  - have Hne : m != m0.
      apply/eqP=>E; by move: HP; rewrite -E EP.
    by rewrite Hne.
  - by case: (m != m0); rewrite ?exprn_ge0.
rewrite -Et addrAC subrr add0r.
exact: Hsub.
Qed.

Theorem computational_event_complement_bound (T : ihbFinType)
    (psi : 'NS('Hs T)) (P : pred T) (m0 : T) :
  ~~ P m0 ->
  \sum_(m : T | P m) `|[< ''m; (psi : 'Hs T) >]|^+2 <=
    1 - `|[< ''m0; (psi : 'Hs T) >]|^+2.
Proof. apply: onb_event_complement_bound; exact: ns_dot. Qed.
End ClassicalPhaseProbability.


Module ClassicalGroverCorrectness.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops ClassicalAlgorithmSemantics ClassicalGrover CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Lemma power_initial u (q : wf_qreg u) (U : 'FU('Ht u)) n v :
  superop_power (liftfso (formso (tf2f q q U))) n :o
    liftfso (initialso (tv2v q v)) =
  liftfso (initialso (tv2v q (iter n U v))).
Proof.
elim: n v=>[|n IH] v; first by rewrite /= comp_so1l.
by rewrite /= -comp_soA -liftfso_comp formso_initial tf2f_apply IH -iterSr iterS.
Qed.

Section Grover.
Variable (T : qType) (q : wf_qreg T).
Notation TT := (eval_qtype T).
Variable (Pw : pred TT).
Hypothesis card_Pw : (0 < #|Pw| < #|TT|)%N.

Definition final_store K (x : variable Integer) s :=
  iter K (next_store x) (s.[x <- (0 : int)])%M.

Lemma grover_prefix_execution K x s :
  execution (grover_prefix q Pw K x) s (final_store K x s)
    (liftfso (initialso (tv2v q (iteration_state Pw K)))).
Proof.
have Hs : ((s.[x <- (0 : int)]).[x])%M = Posz 0 by rewrite get_set_eq.
have Dloop := @counted_unitary_execution T q (rotation Pw) x K 0
  (s.[x <- (0 : int)])%M Hs.
rewrite add0n in Dloop.
have D := RunSequence (RunInitialize q (EConst (zero_state T)) s)
  (RunSequence (RunUnitary q (EConst (@uniformtf TT)) s)
    (RunSequence (RunAssign x (EConst (0 : int)) s) Dloop)).
rewrite comp_so1r -comp_soA -liftfso_comp formso_initial tf2f_apply
  uniformtfE power_initial in D.
exact: D.
Qed.

Lemma grover_prefix_denote K x s m :
  denote (grover_prefix q Pw K x) s m =
  point (final_store K x s)
    (liftfso (initialso (tv2v q (iteration_state Pw K)))) m.
Proof. apply: execution_denote; exact: grover_prefix_execution. Qed.

Definition success_post (y : variable (QType T)) : store -> 'FO(Hq) :=
  fun s => if Pw (s.[y])%M then (\1 : 'FO(Hq)) else (0%:VF : 'FO(Hq)).

Lemma measurement_success_pre total y s :
  (xp total (denote (Measure y q (EConst [QM of @tmeas TT])))
    (success_post y) s : 'End(Hq)) =
  liftf_lf (tf2f q q (success_effect Pw)).
Proof.
rewrite CQPrimitive.measurement_pre.
change (\sum_v ((liftf_lf (tf2f q q (tmeas v)))^A \o
  (success_post y (s.[y <- v])%M : 'End(Hq)) \o
  liftf_lf (tf2f q q (tmeas v))) =
  liftf_lf (tf2f q q (\sum_(i | Pw i) [> ''i ; ''i <]))).
rewrite !linear_sum /= [RHS]big_mkcond; apply eq_bigr=>i _.
rewrite /success_post get_set_eq; case: (Pw i)=>/=.
- by rewrite comp_lfun1r -liftf_lf_adj -liftf_lf_comp tf2f_adj tf2f_comp
    /tmeas adj_outp outp_comp ns_dot scale1r.
- by rewrite comp_lfun0r comp_lfun0l.
Qed.

Theorem grover_success_pre total K x y s :
  (CQHoare.pre total (grover q Pw K x y) (success_post y) s : 'End(Hq)) =
  (success_probability Pw K)%:C *: \1.
Proof.
rewrite /grover CQHoare.pre_sequence.
rewrite /CQHoare.pre (execution_pre _ _ (grover_prefix_execution K x s)).
rewrite measurement_success_pre liftfso_dual liftfsoEf dualso_initialE
  tf2f_apply tv2v_dot (iteration_success card_Pw) linearZ /= liftf_lf1.
by [].
Qed.

Definition success_bound K : 'FO(Hq) :=
  [obs of liftf_lf (tf2f q q
    ((initialso (iteration_state Pw K))^*o (success_effect Pw)))].

Lemma success_boundE K : (success_bound K : 'End(Hq)) =
  (success_probability Pw K)%:C *: \1.
Proof.
by rewrite /success_bound /= dualso_initialE (iteration_success card_Pw)
  !linearZ /= tf2f1 liftf_lf1.
Qed.

Theorem grover_correct total K x y :
  CQHoare.derives total (fun _ => success_bound K)
    (grover q Pw K x y) (success_post y).
Proof.
apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite grover_success_pre success_boundE.
Qed.

End Grover.
End ClassicalGroverCorrectness.


Module ClassicalFourierProgram.
(* The nested-While Fourier program of classical.pdf Section 7.2.
   See PROOF_NOTES.md for the invariant and exact circuit argument. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops ClassicalIndexedLoops ClassicalAlgorithmSemantics ClassicalFourier.
Local Notation Hq := 'H[msys]_finset.setT.

Definition phase_indices_valid n (a b : int) : bool :=
  if one_based_index n a is Some i then
    if one_based_index n b is Some j then i != j else false
  else false.
Definition selected_phase n (a b : int) : 'FU('Hs (n.-tuple bool)) :=
  if one_based_index n a is Some i then
    if one_based_index n b is Some j then controlled_phase i j (phase_angle i j)
    else (\1 : 'FU('Hs (n.-tuple bool)))
  else (\1 : 'FU('Hs (n.-tuple bool))).

Definition phase_gate n (q : wf_qreg (QArray n QBool))
    (x y : variable Integer) : command :=
  Conditional
    (EApp (EApp (EConst (@phase_indices_valid n)) (EVar x)) (EVar y))
    (Unitary q (EApp (EApp (EConst (@selected_phase n)) (EVar x)) (EVar y)))
    Abort.

Lemma phase_gate_execution n (q : wf_qreg (QArray n QBool)) (x y : variable Integer)
    (i j : 'I_n) s :
  i != j -> (s.[x])%M = Posz i.+1 -> (s.[y])%M = Posz j.+1 ->
  execution (phase_gate q x y) s s
    (liftfso (formso (tf2f q q (controlled_phase i j (phase_angle i j))))).
Proof.
move=>Hij Hx Hy; apply: RunIfTrue.
- by rewrite /eval /= Hx Hy /phase_indices_valid !one_based_indexE Hij.
- have D := RunUnitary q
    (EApp (EApp (EConst (@selected_phase n)) (EVar x)) (EVar y)) s.
  by rewrite /eval /= Hx Hy /selected_phase !one_based_indexE in D.
Qed.

Section Program.
Variable (n : nat) (q : wf_qreg (QArray n QBool)).
Variable (x y : variable Integer).

Definition fourier_inner := While (below y n.+1)
  (Sequence (phase_gate q x y) (Assign y (increment y))).
Definition fourier_body :=
  Sequence (indexed_gate q x (@single_hadamard n))
  (Sequence (Assign y (increment x))
  (Sequence fourier_inner (Assign x (increment x)))).
Definition fourier_outer := While (below x n.+1) fourier_body.
Definition fourier_program := Sequence (Assign x (EConst (1 : int)))
  (Sequence fourier_outer (Unitary q (EConst (reversal n)))).

Definition inner_circuit (k : 'I_n) start : 'FU('Hs (n.-tuple bool)) :=
  unitary_list [seq controlled_phase k j (phase_angle k j) |
    j <- drop start (enum 'I_n)].

Lemma control_indices_drop (k : 'I_n) :
  control_indices k = drop k.+1 (enum 'I_n).
Proof.
apply: (inj_map (@ord_inj n)).
rewrite map_drop val_enum_ord drop_iota add0n /control_indices.
rewrite -filter_map val_enum_ord.
have Hsmall : seq.filter (fun j : nat => (k < j)%N) (iota 0 k.+1) = [::].
  rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 // =>j.
  rewrite mem_iota add0n leq0n /= ltnS =>Hj.
  by rewrite ltnNge Hj.
have Hlarge : seq.filter (fun j : nat => (k < j)%N)
    (iota k.+1 (n - k.+1)) = iota k.+1 (n - k.+1).
  apply/all_filterP/allP=>j; rewrite mem_iota=>/andP[Hj _]; exact: Hj.
have Eseq := iotaD 0 k.+1 (n - k.+1).
rewrite add0n (subnKC (ltn_ord k)) in Eseq.
by rewrite Eseq filter_cat Hsmall Hlarge.
Qed.

Lemma inner_circuit_layer (k : 'I_n) :
  inner_circuit k k.+1 \o single_hadamard k = phase_layer k.
Proof. by rewrite /phase_layer /inner_circuit control_indices_drop. Qed.

Lemma inner_circuit_end (k : 'I_n) :
  (inner_circuit k n : 'End('Hs (n.-tuple bool))) = \1.
Proof. by rewrite /inner_circuit drop_oversize ?size_enum_ord. Qed.

Lemma inner_circuit_step (k j : 'I_n) :
  (inner_circuit k j : 'End('Hs (n.-tuple bool))) =
    inner_circuit k j.+1 \o controlled_phase k j (phase_angle k j).
Proof.
by rewrite /inner_circuit (drop_nth j) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.

Lemma increment_preserves_other s count : cvname y != cvname x ->
  ((iter count (next_store y) s).[x])%M = (s.[x])%M.
Proof.
move=>Hxy; elim: count s=>[|count IH] s; first by [].
by rewrite iterSr IH /next_store get_set_nex.
Qed.

Lemma fourier_inner_execution (k : 'I_n) count start s :
  cvname y != cvname x -> (k < start)%N -> (start + count = n)%N ->
  (s.[x])%M = Posz k.+1 -> (s.[y])%M = Posz start.+1 ->
  execution fourier_inner s (iter count (next_store y) s)
    (liftfso (formso (tf2f q q (inner_circuit k start)))).
Proof.
elim: count start s=>[|count IH] start s Hxy Hks Hn Hx Hy.
- rewrite addn0 in Hn; subst start.
  rewrite inner_circuit_end tf2f1 formso1 liftfso1 /=.
  apply: RunWhileFalse; by rewrite /below /eval /= Hy ltxx.
- have Hstart : (start < n)%N.
    by rewrite -Hn addnS ltnS leq_addr.
  pose j : 'I_n := Ordinal Hstart.
  have Hkj : k != j.
    apply/eqP=>E; move: Hks; by rewrite E ltnn.
  have Hguard : eval (below y n.+1) s = true.
    by rewrite /below /eval /= Hy ltz_nat ltnS Hstart.
  have Hnx : ((next_store y s).[x])%M = Posz k.+1.
    by rewrite /next_store get_set_nex.
  have Hny : ((next_store y s).[y])%M = Posz start.+2.
    exact: next_store_value Hy.
  have Hnt : (start.+1 + count = n)%N by rewrite addSn -addnS.
  have Hkt : (k < start.+1)%N := ltn_trans Hks (ltnSn start).
  have Dt := IH start.+1 (next_store y s) Hxy Hkt Hnt Hnx Hny.
  have Dgate := @phase_gate_execution n q x y k j s Hkj Hx Hy.
  have Db := RunSequence Dgate (RunAssign y (increment y) s).
  rewrite comp_so1l in Db.
  have D := RunWhileTrue Hguard Db Dt.
  rewrite register_unitary_comp in D.
  rewrite iterSr (@inner_circuit_step k j).
  exact: D.
Qed.

Definition fourier_next j s :=
  next_store x (iter (n - j) (next_store y) (s.[y <- eval (increment x) s])%M).
Definition fourier_action j (_ : store) : 'SO(Hq) :=
  if one_based_index n (Posz j) is Some i then
    liftfso (formso (tf2f q q (phase_layer i))) else \:1.

Lemma fourier_next_counter j s : cvname y != cvname x ->
  (s.[x])%M = Posz j -> ((fourier_next j s).[x])%M = Posz j.+1.
Proof.
move=>Hxy Hx; apply: next_store_value.
by rewrite increment_preserves_other // get_set_nex.
Qed.

Lemma fourier_body_execution (i : 'I_n) s :
  cvname y != cvname x -> (s.[x])%M = Posz i.+1 ->
  execution fourier_body s (fourier_next i.+1 s) (fourier_action i.+1 s).
Proof.
move=>Hxy Hx.
have Hx0 : ((s.[y <- eval (increment x) s]).[x])%M = Posz i.+1.
  by rewrite get_set_nex.
have Hy0 : ((s.[y <- eval (increment x) s]).[y])%M = Posz i.+2.
  by rewrite get_set_eq /increment /eval /= Hx -PoszD addn1.
have Dloop := @fourier_inner_execution i (n - i.+1) i.+1
  (s.[y <- eval (increment x) s])%M Hxy (ltnSn i)
  (subnKC (ltn_ord i)) Hx0 Hy0.
have Dhad := @indexed_gate_execution _ n q x (@single_hadamard n) i s Hx.
have D := RunSequence Dhad
  (RunSequence (RunAssign y (increment x) s)
    (RunSequence Dloop (RunAssign x (increment x) _))).
rewrite comp_so1l comp_so1r register_unitary_comp inner_circuit_layer in D.
rewrite /fourier_action one_based_indexE.
exact: D.
Qed.

Lemma fourier_outer_execution s :
  cvname y != cvname x -> (s.[x])%M = Posz 1 ->
  execution fourier_outer s (final_store fourier_next 1 n s)
    (accumulated_action fourier_next fourier_action 1 n s).
Proof.
move=>Hxy Hx; rewrite /fourier_outer -[n.+1]add1n.
apply: indexed_loop_execution Hx _ _.
- move=>[|j] t /andP[Hlow Hhigh] Ht; first by rewrite leqn0 in Hlow.
  have Hj : (j < n)%N by move: Hhigh; rewrite add1n ltnS.
  exact: (@fourier_body_execution (Ordinal Hj) t Hxy Ht).
- move=>j t _ Ht; exact: fourier_next_counter Hxy Ht.
Qed.

Definition outer_circuit start : 'FU('Hs (n.-tuple bool)) :=
  unitary_list [seq phase_layer j | j <- drop start (enum 'I_n)].

Lemma outer_circuit_end : (outer_circuit n : 'End('Hs (n.-tuple bool))) = \1.
Proof. by rewrite /outer_circuit drop_oversize ?size_enum_ord. Qed.

Lemma outer_circuit_step (j : 'I_n) :
  (outer_circuit j : 'End('Hs (n.-tuple bool))) =
    outer_circuit j.+1 \o phase_layer j.
Proof.
by rewrite /outer_circuit (drop_nth j) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.

Lemma outer_circuit_whole :
  (outer_circuit 0 : 'End('Hs (n.-tuple bool))) = circuit_prefix n n.
Proof.
by rewrite /outer_circuit /circuit_prefix drop0 take_oversize ?size_enum_ord.
Qed.

Lemma accumulated_circuit count start s : (start + count = n)%N ->
  accumulated_action fourier_next fourier_action start.+1 count s =
    liftfso (formso (tf2f q q (outer_circuit start))).
Proof.
elim: count start s=>[|count IH] start s Hn.
- rewrite addn0 in Hn; subst start.
  by rewrite /= outer_circuit_end tf2f1 formso1 liftfso1.
- have Hstart : (start < n)%N.
    by rewrite -Hn addnS ltnS leq_addr.
  pose j : 'I_n := Ordinal Hstart.
  have Hnt : (start.+1 + count = n)%N by rewrite addSn -addnS.
  change (accumulated_action fourier_next fourier_action start.+2 count
    (fourier_next start.+1 s) :o fourier_action start.+1 s =
      liftfso (formso (tf2f q q (outer_circuit start)))).
  rewrite (IH _ _ Hnt) /fourier_action (@one_based_indexE n j)
    register_unitary_comp (outer_circuit_step j).
  by [].
Qed.

Definition fourier_final_store s :=
  final_store fourier_next 1 n (s.[x <- (1 : int)])%M.
Definition fourier_channel : 'QC(Hq) :=
  [QC of liftfso (formso (tf2f q q (tuple_fourier n)))].

Theorem fourier_execution s : cvname y != cvname x ->
  execution fourier_program s (fourier_final_store s) fourier_channel.
Proof.
move=>Hxy.
have Hx : ((s.[x <- (1 : int)]).[x])%M = Posz 1 by rewrite get_set_eq.
have Dloop := fourier_outer_execution Hxy Hx.
have D := RunSequence (RunAssign x (EConst (1 : int)) s)
  (RunSequence Dloop (RunUnitary q (EConst (reversal n)) _)).
rewrite (@accumulated_circuit n 0 (s.[x <- (1 : int)])%M (add0n n)) outer_circuit_whole
  comp_so1r register_unitary_comp -/(fourier_circuit n) fourier_circuit_correct in D.
exact: D.
Qed.

Theorem fourier_denote s : cvname y != cvname x ->
  forall m, denote fourier_program s m =
    point (fourier_final_store s) fourier_channel m.
Proof. move=>Hxy; exact: execution_denote (fourier_execution s Hxy). Qed.

Theorem fourier_pre total (Q : store -> 'FO(Hq)) s : cvname y != cvname x ->
  (CQHoare.pre total fourier_program Q s : 'End(Hq)) =
    fourier_channel^*o (Q (fourier_final_store s)).
Proof.
move=>Hxy; exact: execution_pre (fourier_execution s Hxy).
Qed.

Theorem fourier_correct total (P Q : store -> 'FO(Hq)) :
  cvname y != cvname x ->
  (forall s, P s <= fourier_channel^*o (Q (fourier_final_store s))) ->
  CQHoare.derives total P fourier_program Q.
Proof.
move=>Hxy Hpre; apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite fourier_pre //; exact: Hpre.
Qed.

End Program.
End ClassicalFourierProgram.


Module ClassicalPhaseEstimation.
(* Exact phase-estimation identities; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition tuple_fourier n : 'FU('Hs (n.-tuple bool)) :=
  ClassicalFourier.tuple_fourier n.

Definition phase_diagonal n (phi : R) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of expmxip t2tv (fun i : n.-tuple bool => (bseq2ord i)%:R) (2 * phi)].

Definition phase_vector n (phi : R) := phase_diagonal n phi uniformtv.

Lemma phase_vector_dot n phi : [<phase_vector n phi; phase_vector n phi>] = 1.
Proof. by rewrite /phase_vector isof_dot ns_dot. Qed.
HB.instance Definition _ n phi := isNormalState.Build _ (phase_vector n phi)
  (phase_vector_dot n phi).

Lemma phase_vectorE n phi : phase_vector n phi =
  (sqrtC 2%:R ^- n) *:
    \sum_(i : n.-tuple bool) expip ((bseq2ord i)%:R * (2 * phi)) *: ''i.
Proof.
rewrite /phase_vector uniformtvE linearZ /= linear_sum /=.
rewrite card_tuple card_bool natrX sqrtCX_nat.
by congr (_ *: _); apply eq_bigr=>i _; rewrite /phase_diagonal expmxipEt.
Qed.

Definition output_state n (phi : R) := (tuple_fourier n)^A (phase_vector n phi).

Lemma output_state_dot n phi : [<output_state n phi; output_state n phi>] = 1.
Proof. by rewrite /output_state isof_dot ns_dot. Qed.
HB.instance Definition _ n phi := isNormalState.Build _ (output_state n phi)
  (output_state_dot n phi).

Lemma fourier_coefficient n (m i : n.-tuple bool) :
  [< ''i; QFTbv m >] = (sqrtC 2%:R ^- n) *
    expip (2%:R * (bseq2ord m * bseq2ord i)%:R / 2%:R ^+ n).
Proof.
rewrite QFTbvE dotpZr dotp_sumr (bigD1 i) //= big1.
- by move=>j /negPf Eji; rewrite dotpZr onb_dot eq_sym Eji mulr0.
- by rewrite dotpZr ns_dot mulr1 addr0.
Qed.

Theorem phase_output_amplitude n phi (m : n.-tuple bool) :
  [< ''m; output_state n phi >] =
  (sqrtC 2%:R ^- n)^+2 *
    \sum_(i : n.-tuple bool)
      expip ((bseq2ord i)%:R * (2 * phi) -
        2%:R * (bseq2ord m * bseq2ord i)%:R / 2%:R ^+ n).
Proof.
rewrite /output_state adj_dotEr /tuple_fourier PUnitaryE phase_vectorE
  dotpZr dotp_sumr !mulr_sumr.
apply eq_bigr=>i _.
rewrite dotpZr -conj_dotp fourier_coefficient rmorphM /=
  geC0_conj ?invr_ge0 ?exprn_ge0 ?sqrtC_ge0 // -expipNC.
by rewrite -!mulrA [expip _ * _]mulrCA -expipD mulrA.
Qed.

Lemma phase_vector_exact n (m : n.-tuple bool) :
  phase_vector n ((bseq2ord m)%:R / 2%:R ^+ n) = QFTbv m.
Proof.
rewrite phase_vectorE QFTbvE; congr (_ *: _); apply eq_bigr=>i _.
congr (_ *: _); congr (expip _).
by rewrite natrM mulrCA !mulrA
  [2 * (bseq2ord i)%:R * (bseq2ord m)%:R]mulrAC.
Qed.

Theorem exact_phase_output n (m : n.-tuple bool) :
  output_state n ((bseq2ord m)%:R / 2%:R ^+ n) = ''m.
Proof.
by rewrite /output_state phase_vector_exact /tuple_fourier PUnitaryEV.
Qed.

Section Eigenstate.
Variable (T : ihbFinType) (U : 'FU('Hs T)) (u : 'Hs T) (phi : R).
Hypothesis eigenstate : U u = expip (2 * phi) *: u.

Lemma eigen_power j : (U%:VF ^+ j) u = expip ((j%:R) * (2 * phi)) *: u.
Proof.
elim: j=>[|j IH].
- by rewrite expr0 lfunE mul0r expip0 scale1r.
- rewrite exprS lfunE /= IH linearZ /= eigenstate scalerA -expipD.
  congr (_ *: _); congr (expip _).
  by rewrite -[j.+1]addn1 natrD [(j%:R + 1) * _]mulrDl mul1r.
Qed.

Definition controlled_powers n : 'FU('Hs ((n.-tuple bool) * T)%type) :=
  [unitary of Multiplexer (fun i : n.-tuple bool =>
    [unitary of U%:VF ^+ (bseq2ord i)])].

Lemma phase_kickback n :
  controlled_powers n (uniformtv ⊗t u) = phase_vector n phi ⊗t u.
Proof.
rewrite uniformtvE linearZl /= linear_sumlz /= linearZ /= linear_sum /=
  phase_vectorE linearZl /= linear_sumlz /=.
rewrite card_tuple card_bool natrX sqrtCX_nat.
congr (_ *: _); apply eq_bigr=>i _.
by rewrite /controlled_powers MultiplexerEt eigen_power linearZ /= linearZl.
Qed.
End Eigenstate.
End ClassicalPhaseEstimation.


Module ClassicalPhaseProgram.
(* The actual nested-While PE program from classical.pdf, Section 7.3.
   Invalid dynamic register indices abort, as in the paper syntax sugar. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops ClassicalIndexedLoops ClassicalPhaseEstimation.

Section Program.
Variable (n : nat) (T : qType).
Variable (qr : wf_qreg (QPair (QArray n QBool) T)).
Variable (U Uu : 'FU('Ht T)).

Definition control_register : wf_qreg (QArray n QBool) :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid qr)).
Definition target_register : wf_qreg T :=
  WF_QReg (QRegAuto.valid_qreg_snd (qreg_is_valid qr)).

Definition controlled_at (i : 'I_n) : 'FU('Ht (QPair (QArray n QBool) T)) :=
  [unitary of Multiplexer (fun bs : n.-tuple bool =>
    if bs~_i then U else (\1 : 'FU('Ht T)))].

Definition hadamard_at (i : 'I_n) : 'FU('Ht (QArray n QBool)) :=
  ClassicalFourier.single_hadamard i.

Definition phase_inner_guard (x y : variable Integer) : bool_expr :=
  EApp (EApp (EConst (fun a b : int => b < Posz (2 ^ (n - absz a))))
    (EVar x)) (EVar y).

Definition phase_inner (x y : variable Integer) :=
  While (phase_inner_guard x y)
    (Sequence (indexed_gate qr x controlled_at) (Assign y (increment y))).

Lemma phase_inner_execution (x y : variable Integer) (i : 'I_n) count k s :
  cvname y != cvname x ->
  (s.[x])%M = Posz i.+1 -> (s.[y])%M = Posz k ->
  (k + count = 2 ^ (n - i.+1))%N ->
  execution (phase_inner x y) s (iter count (next_store y) s)
    (superop_power (liftfso (formso (tf2f qr qr (controlled_at i)))) count).
Proof.
elim: count k s=>[|count IH] k s Hxy Hx Hy Ebound.
- rewrite /phase_inner /=; apply: RunWhileFalse.
  by rewrite /phase_inner_guard /eval /= Hx Hy -Ebound addn0 ltxx.
- have Hb : eval (phase_inner_guard x y) s = true.
    by rewrite /phase_inner_guard /eval /= Hx Hy -Ebound
      ltz_nat addnS ltnS leq_addr.
  have Dgate := @indexed_gate_execution _ _ qr x controlled_at i s Hx.
  have Dbody := RunSequence Dgate (RunAssign y (increment y) s).
  rewrite comp_so1l in Dbody.
  have Hx' : ((next_store y s).[x])%M = Posz i.+1.
    by rewrite /next_store get_set_nex.
  have Hy' := next_store_value Hy.
  have Ebound' : (k.+1 + count = 2 ^ (n - i.+1))%N.
    by rewrite addSn -addnS Ebound.
  have Dtail := IH k.+1 (next_store y s) Hxy Hx' Hy' Ebound'.
  rewrite /phase_inner iterSr /=.
  exact: (RunWhileTrue Hb Dbody Dtail).
Qed.

Definition phase_outer (x y : variable Integer) :=
  While (EApp (EConst (fun a : int => a <= Posz n)) (EVar x))
    (Sequence (indexed_gate control_register x hadamard_at)
    (Sequence (Assign y (EConst (0 : int)))
    (Sequence (phase_inner x y) (Assign x (increment x))))).

Definition phase_prefix (x y : variable Integer) :=
  Sequence (Initialize target_register (EConst (zero_state T)))
  (Sequence (Unitary target_register (EConst Uu))
  (Sequence (Initialize control_register (EConst (zero_state (QArray n QBool))))
  (Sequence (Assign x (EConst (1 : int)))
  (Sequence (phase_outer x y)
    (Unitary control_register (EConst [unitary of (tuple_fourier n)^A])))))).

Definition phase_estimation (x y : variable Integer)
    (z : variable (QType (QArray n QBool))) :=
  Sequence (phase_prefix x y)
    (Measure z control_register (EConst [QM of @tmeas (eval_qtype (QArray n QBool))])).

End Program.
End ClassicalPhaseProgram.


Module ClassicalPhaseBounds.
(* Exact geometric phase amplitudes and bounds; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalPhaseEstimation.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition phase_error n (phi : R) (m : n.-tuple bool) : R :=
  phi - (bseq2ord m)%:R / 2%:R ^+ n.

Lemma amplitude_ordinal n phi (m : n.-tuple bool) :
  [< ''m; output_state n phi >] =
  (2%:R ^+ n : C)^-1 *
    \sum_(j < expn 2 n) expip (2 * phase_error phi m * j%:R).
Proof.
rewrite phase_output_amplitude !exprVn -exprM mulnC exprM sqrtCK big_bseq.
congr (_ * _); apply: eq_bigr=>j _; rewrite ord2bseqK.
congr (expip _); rewrite /phase_error natrM mulrBr !mulrA.
rewrite [j%:R * 2]mulrC mulrBl.
by congr (_ - _); rewrite mulrAC.
Qed.

Theorem amplitude_geometric n phi (m : n.-tuple bool) :
  expip (2 * phase_error phi m) != 1 ->
  [< ''m; output_state n phi >] =
  (2%:R ^+ n : C)^-1 *
    ((1 - expip (2 * phase_error phi m * (2%:R ^+ n))) /
      (1 - expip (2 * phase_error phi m))).
Proof. by move=>H; rewrite amplitude_ordinal (expip_sum _ H) natrX. Qed.

Lemma exponential_norm (x : R) : `|expip x| = (1 : C).
Proof.
apply/eqP; rewrite -(@eqrXn2 C 2) ?normr_ge0 ?ler01 //.
rewrite expr1n sqr_normc conjcC.
by rewrite -(@expipNC R x) -expipD subrr expip0.
Qed.

Lemma exponential_difference_bound (x : R) :
  `|1 - expip x| <= (2 : C).
Proof.
apply: (le_trans (ler_normB _ _)).
by rewrite normr1 exponential_norm.
Qed.

Theorem amplitude_bound n phi (m : n.-tuple bool) :
  expip (2 * phase_error phi m) != 1 ->
  `|[< ''m; output_state n phi >]| <=
    (2%:R ^+ n : C)^-1 *
      (2 / `|1 - expip (2 * phase_error phi m)|).
Proof.
move=>H.
have HN : (2%:R ^+ n : C) \is a GRing.unit.
  by rewrite unitfE expf_neq0.
have Hd : (1 - expip (2 * phase_error phi m)) \is a GRing.unit.
  by rewrite unitfE subr_eq0 eq_sym.
rewrite (amplitude_geometric H) !normrM !normrV //
  ger0_norm ?exprn_ge0 //.
apply: ler_wpM2l; first by rewrite invr_ge0 exprn_ge0.
apply: ler_wpM2r; first by rewrite invr_ge0 normr_ge0.
exact: exponential_difference_bound.
Qed.

Theorem probability_bound n phi (m : n.-tuple bool) :
  expip (2 * phase_error phi m) != 1 ->
  ([< output_state n phi; ''m >] * [< ''m; output_state n phi >]) <=
    ((2%:R ^+ n : C)^-1 *
      (2 / `|1 - expip (2 * phase_error phi m)|))^+2.
Proof.
move=>H; rewrite -conj_dotp mulrC -sqr_normc.
have HB := amplitude_bound H.
rewrite !expr2.
exact: (ler_pM (normr_ge0 _) (normr_ge0 _) HB HB).
Qed.
End ClassicalPhaseBounds.


Module ClassicalPhaseExecution.
(* Deterministic certificates for the actual nested phase-estimation loops. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops ClassicalIndexedLoops ClassicalPhaseEstimation ClassicalPhaseProgram.
Import ClassicalAlgorithmSemantics CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma increment_other (x y : variable Integer) s count :
  cvname y != cvname x ->
  ((iter count (next_store y) s).[x])%M = (s.[x])%M.
Proof.
move=>Hxy; elim: count s=>[|count IH] s; first by [].
by rewrite iterSr IH /next_store get_set_nex.
Qed.

Lemma integer_le_below n :
  (fun a : int => a <= Posz n) = (fun a : int => a < Posz n.+1).
Proof.
apply/funext=>a.
by rewrite -[n.+1]addn1 PoszD ltzD1.
Qed.

Section Program.
Variable (n : nat) (T : qType).
Variable (qr : wf_qreg (QPair (QArray n QBool) T)).
Variable (U : 'FU('Ht T)).
Variable (x y : variable Integer).
Hypothesis distinct_counters : cvname y != cvname x.

Definition phase_body :=
  Sequence (indexed_gate (control_register qr) x (@hadamard_at n))
  (Sequence (Assign y (EConst (0 : int)))
  (Sequence (phase_inner qr U x y) (Assign x (increment x)))).

Definition phase_next j s :=
  next_store x (iter (2 ^ (n - j)) (next_store y) (s.[y <- (0 : int)])%M).

Definition phase_action j (_ : store) : 'SO(Hq) :=
  if one_based_index n (Posz j) is Some i then
    superop_power (liftfso (formso (tf2f qr qr (controlled_at U i)))) (2 ^ (n - j)) :o
      liftfso (formso (tf2f (control_register qr) (control_register qr) (hadamard_at i)))
  else \:1.

Lemma phase_next_counter j s : (s.[x])%M = Posz j ->
  ((phase_next j s).[x])%M = Posz j.+1.
Proof.
move=>Hx; apply: next_store_value.
by rewrite increment_other // get_set_nex.
Qed.

Lemma phase_body_execution (i : 'I_n) s :
  (s.[x])%M = Posz i.+1 ->
  execution phase_body s (phase_next i.+1 s) (phase_action i.+1 s).
Proof.
move=>Hx.
have Hx0 : ((s.[y <- (0 : int)]).[x])%M = Posz i.+1.
  by rewrite get_set_nex.
have Hy0 : ((s.[y <- (0 : int)]).[y])%M = Posz 0 by rewrite get_set_eq.
have Dloop := @phase_inner_execution n T qr U x y i (2 ^ (n - i.+1)) 0
  (s.[y <- (0 : int)])%M distinct_counters Hx0 Hy0 (add0n _).
have Dhad := @indexed_gate_execution _ n (control_register qr) x
  (@hadamard_at n) i s Hx.
have D := RunSequence Dhad
  (RunSequence (RunAssign y (EConst (0 : int)) s)
    (RunSequence Dloop (RunAssign x (increment x) _))).
rewrite comp_so1l comp_so1r in D.
rewrite /phase_action one_based_indexE.
exact: D.
Qed.

Lemma phase_outer_execution s : (s.[x])%M = Posz 1 ->
  execution (phase_outer qr U x y) s (final_store phase_next 1 n s)
    (accumulated_action phase_next phase_action 1 n s).
Proof.
move=>Hx; rewrite /phase_outer integer_le_below.
change (execution (While (below x n.+1) phase_body) s
  (final_store phase_next 1 n s)
  (accumulated_action phase_next phase_action 1 n s)).
rewrite -[n.+1]add1n.
apply: indexed_loop_execution Hx _ _.
- move=>[|j] t /andP[Hlow Hhigh] Ht; first by rewrite leqn0 in Hlow.
  have Hj : (j < n)%N by move: Hhigh; rewrite add1n ltnS.
  exact: (@phase_body_execution (Ordinal Hj) t Ht).
- move=>j t _ Ht; exact: phase_next_counter Ht.
Qed.

Variable Uu : 'FU('Ht T).

Definition phase_final_store s :=
  final_store phase_next 1 n (s.[x <- (1 : int)])%M.

Definition phase_prefix_action s : 'SO(Hq) :=
  (((liftfso (formso (tf2f (control_register qr) (control_register qr)
      (tuple_fourier n)^A)) :o
    accumulated_action phase_next phase_action 1 n (s.[x <- (1 : int)])%M) :o
    liftfso (initialso (tv2v (control_register qr) (zero_state (QArray n QBool))))) :o
    liftfso (formso (tf2f (target_register qr) (target_register qr) Uu))) :o
    liftfso (initialso (tv2v (target_register qr) (zero_state T))).

Lemma phase_prefix_execution s :
  execution (phase_prefix qr U Uu x y) s (phase_final_store s)
    (phase_prefix_action s).
Proof.
have Hx : ((s.[x <- (1 : int)]).[x])%M = Posz 1 by rewrite get_set_eq.
have Dloop := phase_outer_execution Hx.
have D := RunSequence (RunInitialize (target_register qr) (EConst (zero_state T)) s)
  (RunSequence (RunUnitary (target_register qr) (EConst Uu) s)
  (RunSequence (RunInitialize (control_register qr) (EConst (zero_state (QArray n QBool))) s)
  (RunSequence (RunAssign x (EConst (1 : int)) s)
  (RunSequence Dloop (RunUnitary (control_register qr)
    (EConst [unitary of (tuple_fourier n)^A]) (phase_final_store s)))))).
rewrite comp_so1r in D.
exact: D.
Qed.

Lemma phase_prefix_channel s : phase_prefix_action s \is cptp.
Proof. exact: execution_channel (phase_prefix_execution s). Qed.
HB.instance Definition _ s := isQChannel.Build _ _ (phase_prefix_action s)
  (phase_prefix_channel s).

Lemma phase_prefix_denote s m :
  denote (phase_prefix qr U Uu x y) s m =
  point (phase_final_store s) (phase_prefix_action s) m.
Proof. apply: execution_denote; exact: phase_prefix_execution. Qed.

Lemma phase_prefix_pre total (Q : store -> 'FO(Hq)) s :
  (xp total (denote (phase_prefix qr U Uu x y)) Q s : 'End(Hq)) =
    (phase_prefix_action s)^*o (Q (phase_final_store s)).
Proof. apply: execution_pre; exact: phase_prefix_execution. Qed.

End Program.
End ClassicalPhaseExecution.


Module ClassicalPhaseTensor.
(* Repeated controlled-U on one indexed control qubit. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalPhaseEstimation ClassicalPhaseProgram.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition bit_diagonal n (i : 'I_n) (phi : R) : 'FU('Hs (n.-tuple bool)) :=
  [unitary of expmxip t2tv (fun bs : n.-tuple bool => (bs~_i)%:R) (2 * phi)].

Lemma bit_diagonal_basis n (i : 'I_n) phi (bs : n.-tuple bool) :
  bit_diagonal i phi ''bs = expip ((bs~_i)%:R * (2 * phi)) *: ''bs.
Proof. exact: expmxipEt. Qed.

Lemma controlled_power_basis n T (U : 'FU('Ht T)) (i : 'I_n)
    k (bs : n.-tuple bool) (u : 'Ht T) :
  ((controlled_at U i)%:VF ^+ k) (''bs ⊗t u) =
  ''bs ⊗t (if bs~_i then (U%:VF ^+ k) u else u).
Proof.
elim: k=>[|k IH].
- by rewrite expr0 lfunE; case: (bs~_i); rewrite ?lfunE.
- rewrite exprS lfunE /= IH /controlled_at MultiplexerEt.
  by case: (bs~_i); rewrite /= ?exprS ?lfunE.
Qed.

Lemma controlled_power_eigen n T (U : 'FU('Ht T)) (i : 'I_n)
    k (v : 'Hs (n.-tuple bool)) (u : 'Ht T) (phi : R) :
  U u = expip (2 * phi) *: u ->
  ((controlled_at U i)%:VF ^+ k) (v ⊗t u) =
    bit_diagonal i (k%:R * phi) v ⊗t u.
Proof.
move=>Hu; rewrite [v](onb_vec t2tv) linear_sumlz /= linear_sum /=
  [in RHS]linear_sum /= linear_sumlz /=.
apply eq_bigr=>bs _.
rewrite !linearZl /= !linearZ /= controlled_power_basis bit_diagonal_basis.
case E: (bs~_i)=>/=.
- have Er : k%:R * (2 * phi) = 2 * (k%:R * phi) by rewrite mulrCA.
  by rewrite (eigen_power Hu) !linearZ /= !linearZl /= mul1r Er.
- by rewrite mul0r expip0 scale1r !linearZl.
Qed.

Lemma binary_weight_sum n (bs : n.-tuple bool) :
  (bseq2ord bs : nat) =
    (\sum_(i < n) (bs~_i) * 2 ^ (n - i.+1))%N.
Proof.
elim: n bs=>[bs|n IH bs].
- by rewrite tuple0 /bseq2ord /bseq2nat /= big_ord0.
- case/tupleP: bs=>b bs.
  change (bseq2nat (b :: bs) =
    (\sum_(i < n.+1) ([tuple of b :: bs]~_i) * 2 ^ (n.+1 - i.+1))%N).
  rewrite [LHS]bseq2nat_cons {1}(size_tuple bs) big_ord_recl /= tnth0 subn1 /=.
  rewrite mulnC; congr (_ + _)%N.
  transitivity (bseq2ord bs : nat); first by [].
  rewrite IH; apply: eq_bigr=>i _.
  by rewrite tnthS.
Qed.

Lemma binary_weight_sum_real n (bs : n.-tuple bool) :
  (bseq2ord bs)%:R =
    \sum_(i < n) (bs~_i)%:R * (2%:R : R) ^+ (n - i.+1).
Proof.
rewrite binary_weight_sum natr_sum; apply: eq_bigr=>i _.
by rewrite natrM natrX.
Qed.

Lemma phase_vector_coefficient n phi (bs : n.-tuple bool) :
  [< ''bs; phase_vector n phi >] =
    (sqrtC 2%:R ^- n) * expip ((bseq2ord bs)%:R * (2 * phi)).
Proof.
rewrite phase_vectorE dotpZr dotp_sumr (bigD1 bs) //= big1.
- by move=>j /negPf Eji; rewrite dotpZr onb_dot eq_sym Eji mulr0.
- by rewrite dotpZr ns_dot mulr1 addr0.
Qed.

Lemma phase_vector_product n phi :
  phase_vector n phi =
    tentv_tuple (fun i : 'I_n => phstate (2%:R ^+ (n - i.+1) * phi)).
Proof.
apply/(intro_onbl t2tv)=>bs /=.
rewrite phase_vector_coefficient t2tv_tuple tentv_tuple_dot.
under eq_bigr do rewrite dotp_cbph.
rewrite big_split /= prodr_const card_ord exprVn expip_prod.
congr (_ * _); congr (expip _).
rewrite binary_weight_sum_real mulr_suml; apply: eq_bigr=>i _.
by rewrite !mulrA [(bs~_i)%:R * _ * 2]mulrAC [(bs~_i)%:R * 2]mulrC.
Qed.
End ClassicalPhaseTensor.


Module ClassicalPhaseCounterexample.
Import trigo.
(* Counterexample to the printed ordinary-distance phase bound (C6).
   See PROOF_NOTES.md. *)


Import Order.TTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalPhaseEstimation ClassicalPhaseBounds.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Definition witness_phase : R := 1 - 1 / 1024.
Definition zero_outcome : 3.-tuple bool := @ord2bseq 3 (ord0 : 'I_8).
Definition zero_amplitude : C := [< ''zero_outcome; output_state 3 witness_phase >].

Lemma witness_phase_bounds : 1 / 2 < witness_phase < 1.
Proof.
rewrite /witness_phase; apply/andP; split.
- have E : (1 - 1 / 1024 : R) = 1023 / 1024 by field.
  rewrite E ltr_pdivlMr //.
  have -> : (1 / 2 * 1024 : R) = 512 by field.
  by rewrite ltr_nat.
- rewrite ltrBlDr ltrDl; exact: divr_gt0.
Qed.

Lemma cosine_small a : `|a| <= (1 / 4 : R) -> 7 / 8 <= cos (a *+ 2).
Proof.
move=>Ha.
have Hsin := le_trans (ler_abs_sin a) Ha.
have Hq : (0 : R) <= 1 / 4 by apply: divr_ge0.
have Hsq : (sin a)^+2 <= (1 / 4)^+2.
  have Eabs : `|sin a|^+2 = (sin a)^+2 by rewrite -normrX ger0_norm ?sqr_ge0.
  rewrite -Eabs !expr2.
  exact: (ler_pM (normr_ge0 _) (normr_ge0 _) Hsin Hsin).
have E : (7 / 8 : R) = 1 - ((1 / 4)^+2) *+ 2 by field.
by rewrite E cos2x_sin lerD2l lerN2 lerMn2r /=.
Qed.

Lemma orbit_angle_bound (j : 'I_8) : `|pi * j%:R / 1024| <= (1 / 4 : R).
Proof.
have Hnonneg : (0 : R) <= pi * j%:R / 1024.
  by apply: divr_ge0=>//; apply: mulr_ge0; rewrite ?pi_ge0 ?ler0n.
rewrite ger0_norm // ler_pdivrMr //.
have E : (1 / 4 * 1024 : R) = 256 by field.
rewrite E.
apply: le_trans (_ : (4 * 8 : R) <= 256); last by rewrite -natrM ler_nat.
apply: ler_pM; rewrite ?pi_ge0 ?ler0n ?pi_le4 //.
by rewrite ler_nat; exact: ltnW (ltn_ord j).
Qed.

Lemma zero_amplitudeE : zero_amplitude =
  (8 : C)^-1 * \sum_(j < 8) expip (- (2 * j%:R / 1024) : R).
Proof.
rewrite /zero_amplitude amplitude_ordinal /phase_error /zero_outcome ord2bseqK /=
  mul0r subr0 -natrX /=.
congr (_ * _); apply: eq_bigr=>j _.
have E : (2 * witness_phase * j%:R : R) =
    (2 * j)%:R + - (2 * j%:R / 1024).
  rewrite /witness_phase natrM; ring.
by rewrite E expip_period.
Qed.

Lemma zero_amplitude_real : (7 / 8 : R) <= complex.Re zero_amplitude.
Proof.
rewrite zero_amplitudeE.
have E : ((8 : C)^-1)%R = (((8 : R)^-1)%R)%:C.
  by rewrite rmorphV ?unitfE // rmorph_nat.
rewrite E mulr_sumr linear_sum /=.
have Hb (j : 'I_8) : (7 / 8 : R) <= cos ((pi * j%:R / 1024) *+ 2).
  exact: cosine_small (orbit_angle_bound j).
have Er (j : 'I_8) :
  complex.Re ((((8 : R)^-1)%R)%:C * expip (- (2 * j%:R / 1024) : R)) =
  (8 : R)^-1 * cos ((pi * j%:R / 1024) *+ 2).
  rewrite expip.unlock /expi; simpc.
  rewrite cosN; congr (_ * cos _); rewrite !mulr2n; ring.
under eq_bigr do rewrite Er.
have E7 : (7 / 8 : R) = \sum_(j < 8) ((8 : R)^-1 * (7 / 8)).
  rewrite sumr_const card_ord -mulr_natr; field.
rewrite E7; apply: ler_sum=>j _; apply: ler_wpM2l; first by rewrite invr_ge0.
exact: Hb.
Qed.

Lemma zero_probability_gt_half : (1 / 2 : C) < `|zero_amplitude|^+2.
Proof.
have E78 : ((7 / 8 : R)%:C) = (7 / 8 : C).
  by rewrite rmorphM rmorphV ?unitfE // !rmorph_nat.
have Hr : ((7 / 8 : R)%:C) <= (complex.Re zero_amplitude)%:C.
  by rewrite lecR; exact: zero_amplitude_real.
have Ha : (complex.Re zero_amplitude)%:C <= `|complex.Re zero_amplitude|%:C.
  by rewrite lecR ler_norm.
have Hnorm := le_trans (le_trans Hr Ha) (normc_ge_Re zero_amplitude).
rewrite E78 in Hnorm.
have Hnonneg : (0 : C) <= 7 / 8 by apply: divr_ge0.
have Hsq : (7 / 8 : C)^+2 <= `|zero_amplitude|^+2.
  rewrite !expr2; exact: (ler_pM Hnonneg Hnonneg Hnorm Hnorm).
apply: lt_le_trans Hsq.
have E49 : (7 / 8 : C)^+2 = 49 / 64 by field.
rewrite E49 ltr_pdivlMr //.
have E32 : (1 / 2 * 64 : C) = 32 by field.
by rewrite E32 ltr_nat.
Qed.

Definition ordinary_success (m : 3.-tuple bool) :=
  `|witness_phase - (bseq2ord m)%:R / 8| < (1 / 2 : R).

Definition ordinary_success_probability : C :=
  \sum_(m : 3.-tuple bool | ordinary_success m)
    `|[< ''m; output_state 3 witness_phase >]|^+2.

Lemma zero_not_ordinary_success : ~~ ordinary_success zero_outcome.
Proof.
have Hphi := (andP witness_phase_bounds).1.
have Hphi0 : (0 : R) <= witness_phase.
  apply: le_trans (ltW Hphi); exact: divr_ge0.
by rewrite /ordinary_success /zero_outcome ord2bseqK /= mul0r subr0
  ger0_norm // ltNge (ltW Hphi).
Qed.

Theorem ordinary_success_below_half : ordinary_success_probability < (1 / 2 : C).
Proof.
have H := @ClassicalPhaseProbability.onb_event_complement_bound
  'Hs(3.-tuple bool) (Finite.clone (3.-tuple bool) _) t2tv
  (output_state 3 witness_phase) ordinary_success zero_outcome
  (output_state_dot 3 witness_phase) zero_not_ordinary_success.
apply: le_lt_trans H _.
change (1 - `|zero_amplitude|^+2 < (1 / 2 : C)).
rewrite ltrBlDl -ltrBlDr.
have E : (1 - 1 / 2 : C) = 1 / 2 by field.
by rewrite E; exact: zero_probability_gt_half.
Qed.

Corollary printed_phase_bound_counterexample :
  (0 <= witness_phase < 1) /\
  ~~ ((1 / 2 : C) <= ordinary_success_probability).
Proof.
split; last first.
  apply/negP=>Hbad.
  by have := lt_le_trans ordinary_success_below_half Hbad; rewrite ltxx.
have /andP[Hlo Hhi] := witness_phase_bounds; apply/andP; split=>//.
apply: le_trans (ltW Hlo); exact: divr_ge0.
Qed.
End ClassicalPhaseCounterexample.


Module ClassicalPhaseStages.
(* Gate-by-gate phase-estimation invariant; see PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalFourier ClassicalPhaseEstimation ClassicalPhaseProgram ClassicalPhaseTensor.
Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Lemma bit_diagonal_product n (i : 'I_n) (v : 'I_n -> 'Hs bool) r phi :
  v i = phstate r ->
  bit_diagonal i phi (tentv_tuple v) = tensor_replace i v (phstate (r + phi)).
Proof.
move=>Hi; apply/(intro_onbl t2tv)=>bs.
rewrite /bit_diagonal diagonal_amplitude tensor_phase_shift.
have E : tensor_replace i v (phstate r) = tentv_tuple v.
  by rewrite -Hi tensor_replace_id.
rewrite E; congr (expip _ * _).
by rewrite mulrCA mulrA.
Qed.

Definition estimation_factors n phi k (i : 'I_n) :=
  if (i < k)%N then phstate (2%:R ^+ (n - i.+1) * phi) else '0.
Definition estimation_layer n phi k := tentv_tuple (@estimation_factors n phi k).

Definition estimation_stage n T (U : 'FU('Ht T)) (i : 'I_n) :
    'FU('Ht (QPair (QArray n QBool) T)) :=
  [unitary of ((controlled_at U i)%:VF ^+ (2 ^ (n - i.+1))) \o
    (hadamard_at i ⊗f (\1 : 'FU('Ht T)))].

Lemma estimation_stageE n T (U : 'FU('Ht T)) (i : 'I_n) phi (u : 'Ht T) :
  U u = expip (2 * phi) *: u ->
  estimation_stage U i (estimation_layer n phi i ⊗t u) =
    estimation_layer n phi i.+1 ⊗t u.
Proof.
move=>Hu; rewrite /estimation_stage lfunE /= tentf_apply lfunE /=
  (@controlled_power_eigen n T U i _ _ u phi Hu).
rewrite /hadamard_at /estimation_layer single_hadamard_product.
have E : tentv_tuple (fun j : 'I_n =>
    if j == i then Hadamard (estimation_factors phi i j)
    else estimation_factors phi i j) =
  tensor_replace i (estimation_factors phi i) (phstate 0).
  apply: eq_tentv_tuple=>j; case: eqP=>[->|] //.
  by rewrite /estimation_factors ltnn hadamard_phase mul0r.
rewrite E.
have Ei : (fun j : 'I_n => if j == i then phstate 0 else
  estimation_factors phi i j) i = phstate 0 by rewrite eqxx.
rewrite (@bit_diagonal_product n i _ 0 _ Ei) tensor_replace_twice add0r natrX.
congr (_ ⊗t _); apply: eq_tentv_tuple=>j.
rewrite /estimation_factors; case Eji: (j == i)=>/=.
- by move/eqP: Eji=>->; rewrite ltnSn.
- by rewrite ltnS [(j <= i)%N]leq_eqVlt (val_eqE j i) Eji.
Qed.

Definition estimation_circuit_prefix n T (U : 'FU('Ht T)) k :=
  unitary_list [seq estimation_stage U i | i <- take k (enum 'I_n)].

Lemma estimation_layer_initial n phi :
  estimation_layer n phi 0 = ''(nseq_tuple n false).
Proof.
rewrite /estimation_layer t2tv_tuple; apply: eq_tentv_tuple=>i.
by rewrite /estimation_factors ltn0 tnth_nseq.
Qed.

Lemma estimation_layer_final n phi : estimation_layer n phi n = phase_vector n phi.
Proof.
rewrite phase_vector_product /estimation_layer; apply: eq_tentv_tuple=>i.
by rewrite /estimation_factors ltn_ord.
Qed.

Lemma estimation_circuit_prefixE n T (U : 'FU('Ht T)) k phi (u : 'Ht T) :
  U u = expip (2 * phi) *: u -> (k <= n)%N ->
  estimation_circuit_prefix n U k (''(nseq_tuple n false) ⊗t u) =
    estimation_layer n phi k ⊗t u.
Proof.
move=>Hu; elim: k=>[|k IH] Hkn.
- by rewrite /estimation_circuit_prefix take0 /= lfunE estimation_layer_initial.
- have Hk : (k < n)%N := Hkn.
  pose i : 'I_n := Ordinal Hk.
  rewrite /estimation_circuit_prefix (take_nth i) ?size_enum_ord //
    (nth_ord_enum i i) map_rcons unitary_list_rcons
    -/(estimation_circuit_prefix n U k) (IH (ltnW Hk)).
  exact: estimation_stageE Hu.
Qed.

Theorem estimation_circuit_eigen n T (U : 'FU('Ht T)) phi (u : 'Ht T) :
  U u = expip (2 * phi) *: u ->
  estimation_circuit_prefix n U n (''(nseq_tuple n false) ⊗t u) =
    phase_vector n phi ⊗t u.
Proof. by move=>Hu; rewrite (estimation_circuit_prefixE Hu) // estimation_layer_final. Qed.
End ClassicalPhaseStages.


Module ClassicalPhaseCorrectness.
(* Deterministic certificates for the actual nested phase-estimation loops. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops ClassicalIndexedLoops ClassicalAlgorithmSemantics ClassicalRegisterTensor ClassicalFourier ClassicalPhaseEstimation ClassicalPhaseProgram ClassicalPhaseExecution ClassicalPhaseTensor ClassicalPhaseStages.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation R := hermitian.R.

Section PhaseEstimation.
Variable (n : nat) (T : qType).
Variable (qr : wf_qreg (QPair (QArray n QBool) T)).
Variable (U Uu : 'FU('Ht T)).
Variable (x y : variable Integer).
Hypothesis distinct_counters : cvname y != cvname x.

Definition remaining_circuit start :=
  unitary_list [seq estimation_stage U i | i <- drop start (enum 'I_n)].

Lemma remaining_circuit_end :
  (remaining_circuit n : 'End('Ht (QPair (QArray n QBool) T))) = \1.
Proof. by rewrite /remaining_circuit drop_oversize ?size_enum_ord. Qed.

Lemma remaining_circuit_step (i : 'I_n) :
  (remaining_circuit i : 'End('Ht (QPair (QArray n QBool) T))) =
    remaining_circuit i.+1 \o estimation_stage U i.
Proof.
by rewrite /remaining_circuit (drop_nth i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.

Lemma remaining_circuit_whole :
  (remaining_circuit 0 : 'End('Ht (QPair (QArray n QBool) T))) =
    estimation_circuit_prefix n U n.
Proof.
by rewrite /remaining_circuit /estimation_circuit_prefix drop0 take_oversize ?size_enum_ord.
Qed.

Lemma accumulated_circuit count start s : (start + count = n)%N ->
  accumulated_action (phase_next n x y) (phase_action qr U) start.+1 count s =
    liftfso (formso (tf2f qr qr (remaining_circuit start))).
Proof.
elim: count start s=>[|count IH] start s Hn.
- rewrite addn0 in Hn; subst start.
  by rewrite /= remaining_circuit_end tf2f1 formso1 liftfso1.
- have Hstart : (start < n)%N.
    by rewrite -Hn addnS ltnS leq_addr.
  pose i : 'I_n := Ordinal Hstart.
  have Hnt : (start.+1 + count = n)%N by rewrite addSn -addnS.
  change (accumulated_action (phase_next n x y) (phase_action qr U) start.+2 count
    (phase_next n x y start.+1 s) :o phase_action qr U start.+1 s =
      liftfso (formso (tf2f qr qr (remaining_circuit start)))).
  rewrite (IH _ _ Hnt) /phase_action (@one_based_indexE n i)
    register_unitary_power /control_register channel_register_left
    register_unitary_comp register_unitary_comp (remaining_circuit_step i).
  by [].
Qed.

Variable phi : R.
Hypothesis eigenstate : U (Uu (zero_state T : 'Ht T)) = expip (2 * phi) *: Uu (zero_state T : 'Ht T).

Lemma phase_prefix_actionE s :
  phase_prefix_action qr U x y Uu s =
  liftfso (initialso (tv2v qr (output_state n phi ⊗t Uu (zero_state T : 'Ht T)))).
Proof.
rewrite /phase_prefix_action (@accumulated_circuit n 0 (s.[x <- (1 : int)])%M (add0n n)) remaining_circuit_whole
  -!comp_soA -liftfso_comp formso_initial tf2f_apply
  /control_register /target_register initial_register_pair
  -liftfso_comp formso_initial tf2f_apply.
rewrite (estimation_circuit_eigen n eigenstate).
rewrite channel_register_left -liftfso_comp formso_initial tf2f_apply
  tentf_apply lfunE /output_state.
by [].
Qed.

Lemma phase_reset_execution s :
  execution (phase_prefix qr U Uu x y) s (phase_final_store n x y s)
    (liftfso (initialso (tv2v qr (output_state n phi ⊗t Uu (zero_state T : 'Ht T))))).
Proof.
rewrite -(phase_prefix_actionE s).
exact: (@phase_prefix_execution n T qr U x y distinct_counters Uu s).
Qed.

Definition outcome_post (z : variable (QType (QArray n QBool)))
    (m : n.-tuple bool) : store -> 'FO(Hq) :=
  fun s => if (s.[z])%M == m then (\1 : 'FO(Hq)) else (0%:VF : 'FO(Hq)).

Lemma measurement_outcome_pre total z m s :
  (CQPredicate.xp total
    (denote (Measure z (control_register qr)
      (EConst [QM of @tmeas (eval_qtype (QArray n QBool))])))
    (outcome_post z m) s : 'End(Hq)) =
  liftf_lf (tf2f (control_register qr) (control_register qr) [> ''m; ''m <]).
Proof.
rewrite CQPrimitive.measurement_pre.
change (\sum_v ((liftf_lf (tf2f (control_register qr) (control_register qr) (tmeas v)))^A \o
  (outcome_post z m (s.[z <- v])%M : 'End(Hq)) \o
  liftf_lf (tf2f (control_register qr) (control_register qr) (tmeas v))) =
  liftf_lf (tf2f (control_register qr) (control_register qr) [> ''m; ''m <])).
rewrite (bigD1 m) //= /outcome_post get_set_eq eqxx big1.
- move=>i /negPf Him.
  by rewrite get_set_eq Him comp_lfun0r comp_lfun0l.
- by rewrite addr0 comp_lfun1r -liftf_lf_adj -liftf_lf_comp tf2f_adj tf2f_comp
    /tmeas adj_outp outp_comp ns_dot scale1r.
Qed.

Theorem phase_outcome_pre total z m s :
  (CQHoare.pre total (phase_estimation qr U Uu x y z) (outcome_post z m) s : 'End(Hq)) =
  ([< output_state n phi; ''m >] * [< ''m; output_state n phi >]) *: \1.
Proof.
rewrite /phase_estimation CQHoare.pre_sequence /CQHoare.pre
  (execution_pre _ _ (phase_reset_execution s)) measurement_outcome_pre.
rewrite /control_register -(lift_register_left qr [> ''m; ''m <])
  liftfso_dual liftfsoEf dualso_initialE tf2f_apply tv2v_dot
  tentf_apply lfunE tentv_dot isof_dot ns_dot mulr1 outpE dotpZr mulrC
  linearZ /= liftf_lf1.
by [].
Qed.

Theorem phase_outcome_formula total z m s :
  (CQHoare.pre total (phase_estimation qr U Uu x y z) (outcome_post z m) s : 'End(Hq)) =
  `| (sqrtC 2%:R ^- n)^+2 *
    \sum_(i : n.-tuple bool)
      expip ((bseq2ord i)%:R * (2 * phi) -
        2%:R * (bseq2ord m * bseq2ord i)%:R / 2%:R ^+ n) |^+2 *: \1.
Proof.
by rewrite phase_outcome_pre -conj_dotp mulrC -sqr_normc phase_output_amplitude.
Qed.

Definition outcome_bound (m : n.-tuple bool) : 'FO(Hq) :=
  [obs of liftf_lf (tf2f (control_register qr) (control_register qr)
    ((initialso (output_state n phi))^*o [> ''m; ''m <]))].

Lemma outcome_boundE m : (outcome_bound m : 'End(Hq)) =
  ([< output_state n phi; ''m >] * [< ''m; output_state n phi >]) *: \1.
Proof.
by rewrite /outcome_bound /= dualso_initialE outpE dotpZr mulrC
  !linearZ /= tf2f1 liftf_lf1.
Qed.

Theorem phase_estimation_correct total z m :
  CQHoare.derives total (fun _ => outcome_bound m)
    (phase_estimation qr U Uu x y z) (outcome_post z m).
Proof.
apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite phase_outcome_pre outcome_boundE.
Qed.

Theorem phase_exact_pre total z m s :
  phi = (bseq2ord m)%:R / 2%:R ^+ n ->
  (CQHoare.pre total (phase_estimation qr U Uu x y z) (outcome_post z m) s : 'End(Hq)) = \1.
Proof.
by move=>Hphi; rewrite phase_outcome_pre Hphi exact_phase_output ns_dot mulr1 scale1r.
Qed.

Theorem phase_exact_correct total z m :
  phi = (bseq2ord m)%:R / 2%:R ^+ n ->
  CQHoare.derives total (fun _ => (\1 : 'FO(Hq)))
    (phase_estimation qr U Uu x y z) (outcome_post z m).
Proof.
move=>Hphi; apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite (@phase_exact_pre total z m s Hphi).
Qed.

End PhaseEstimation.
End ClassicalPhaseCorrectness.
