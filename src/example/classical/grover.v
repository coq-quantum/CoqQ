(* Grover's search, classical.pdf Examples 4.5/4.11 and Section 7.1.
   The concrete phase-oracle/reflection algebra adapts CoqQ's upstream
   example/coqq_paper/example.v, GroverAlgorithm (MIT; see
   UPSTREAM-LICENSE). The program uses a classical counted while loop. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From mathcomp.analysis Require Import exp trigo.
From quantum Require Import qtype.
From quantum.example.classical Require Import language.

Module ClassicalGrover.
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
