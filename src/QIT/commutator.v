From mathcomp Require Import all_ssreflect all_algebra complex.
From mathcomp.analysis Require Import -(notations)forms.
Require Import spectral.
From mathcomp.classical Require Import boolp classical_sets mathcomp_extra.
From mathcomp.analysis Require Import reals topology normedtype sequences distr realsum realseq ereal discrete.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import mcextra mcaextra notation prodvect hermitian tensor
  cpo EqdepFacts Eqdep_dec mxpred extnum ctopology setdec inhabited qtype.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(****************************************************************************)
(*                       Commutator and Inequality                          *)
(* ------------------------------------------------------------------------ *)
(* Implementation of commutator and its related theories, including:        *)
(*      *  Jacobi's identity                                                *)
(*      *  Parallelogram inequality                                         *)
(*      *  Heisenberg uncertainty                                           *)
(*      *  Maccone-Pati uncertainty                                         *)
(*      *  CHSH inequality and its violation                                *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Num.Theory GRing.Theory GRing.
Local Open Scope ring_scope.
Local Open Scope set_scope.
Local Open Scope lfun_scope. 

Section Uncertainty.

Lemma sqr_ge0_le (x y : hermitian.C) (Hx : 0 <= x) (Hy : 0 <= y) :
  x^+2 <= y^+2 -> x <= y.
Proof. by move => Hs; rewrite -ler_sqr. Qed.

Lemma sqr_le (x y : hermitian.C) :
  `|x|^+2 <= `|y|^+2 -> `|x| <= `|y|.
Proof. by apply sqr_ge0_le. Qed.

Lemma ge_addr (R : numDomainType) (x y z : R) :
  (- z + x <= y) = (x <= y + z). 
Proof.
by rewrite -subr_ge0 -[LHS]subr_ge0 opprD addrA opprK.
Qed.

Variable H : chsType.
Implicit Types u v : H.
Implicit Types A B : 'End(H).

Lemma sub_lfunE A B x : (A - B) x = A x - B x.
Proof.
  by rewrite add_lfunE opp_lfunE.
Qed.

Lemma parallelogram_law : forall u v,
  2 * (`|u|^+2 + `|v|^+2) = `|u+v|^+2 + `|u-v|^+2.
Proof.
  move => u v; rewrite -!dotp_norm dotpBl !dotpBr dotpDl !dotpDr
    mulr_natl mulr2n opprB -!addrA; f_equal;
  rewrite [RHS]addrC [ [<v;u>] + _ ]addrC -!addrA; f_equal; f_equal;
  by rewrite addrC -!addrA addrN addr0 addNr addr0.
Qed.

Lemma constCl : forall (c : hermitian.C) A,
  (c *:\1) \o A = c *: A.
Proof. by move => c A; rewrite -comp_lfunZl comp_lfun1l. Qed.

Lemma constCr : forall c A,
  A \o (c *:\1) = c *: A.
Proof. by move => c A; rewrite -comp_lfunZr comp_lfun1r. Qed.

Lemma constC : forall c A,
  A \o (c *:\1) = (c *:\1) \o A.
Proof. by move => c A; rewrite constCr constCl. Qed.

Lemma dotpA_ge0 : forall A,
  (exists B, A = B^A \o B) -> forall u, 0 <= [< u ; A u >].
Proof. by move => A [B HB] u; rewrite HB comp_lfunE adj_dotEr ge0_dotp. Qed.

Section Expectation.

Definition ave u A := [< u ; A u >].
Definition delta u A := sqrtC (ave u ((A - ave u A *:\1)^+2)).

Lemma ave_real : forall A (HA : A ^A = A) u,
  (ave u A)^* = ave u A.
Proof. by move => A HA u; rewrite conj_dotp -adj_dotEr HA. Qed.

Lemma delta_ge0 : forall A (HA : A ^A = A) u,
  delta u A >= 0.
Proof.
  rewrite /delta /ave => A HA u.
  rewrite sqrtC_ge0 expr2 dotpA_ge0 //.
  exists (A - [< u; A u>] *:\1).
  by rewrite adjfB adjfZ adjf1 conj_dotp -adj_dotEr HA.
Qed.

Lemma expr2o : forall A,
  A ^+2 = A \o A.
Proof. by move => A; rewrite expr2 //. Qed.

Lemma delta_sqr : forall A u,
  (delta u A)^+2 = ave u ((A - ave u A *:\1)^+2).
Proof. by move => A u; rewrite /delta sqrtCK. Qed.

Lemma delta_sqr_norm : forall A (HA : A^A = A) u,
  (delta u A)^+2 = `| (A - ave u A*:\1) u |^+2.
Proof.
  by move => A HA u;
  rewrite delta_sqr -dotp_norm -adj_dotEr adjfB HA;
  rewrite adjfZ adjf1 ave_real // -comp_lfunE -expr2o.
Qed.

Lemma delta_sqr_eq : forall A u, [< u ; u >] = 1 ->
  (delta u A)^+2 = ave u (A^+2) - (ave u A)^+2.
Proof.
  move => A u Hnorm. pose e := [< u ; A u>].
  by rewrite delta_sqr /ave -/e !expr2o;
  rewrite comp_lfunDl !comp_lfunDr !comp_lfunNr !comp_lfunNl opprK;
  rewrite !constCr constCl !add_lfunE !opp_lfunE !scale_lfunE id_lfunE;
  rewrite !dotpDr !dotpNr !dotpZr -/e Hnorm mulr1 addNr addr0.
Qed.

Lemma ave_opp : forall A u,
  ave u (-A) = - ave u A.
Proof. by move => A u; rewrite /ave opp_lfunE dotpNr. Qed.

Lemma delta_opp : forall A u,
   delta u (-A) = delta u A.
Proof.
  move => A u.
  rewrite /delta ave_opp /ave; f_equal; f_equal; f_equal;
  by rewrite -[RHS]sqrrN opprD scaleNr.
Qed.

End Expectation.

Section Commutator.

Definition commer A B := (A \o B) - (B \o A).
Definition atcommer A B := (A \o B) + (B \o A).

Lemma add_commer A B :
  atcommer A B + commer A B = 2 *: (A \o B).
Proof.
  rewrite /commer /atcommer [ _ - (B \o A) ]addrC addrA addrK.
  by have ->: 2 = 1 + 1 by []; rewrite scalerDl scale1r.
Qed.

Lemma sub_commer A B :
  atcommer A B - commer A B = 2 *: (B \o A).
Proof.
  rewrite /commer /atcommer [ _ + (B \o A) ]addrC opprD addrA addrK.
  by have ->: 2 = 1 + 1 by []; rewrite scalerDl scale1r opprK.
Qed.

Lemma Jacobi's_identity A B C :
  (commer (commer A B) C) + (commer (commer B C) A) + (commer (commer C A) B) = 0.
Proof.
  by rewrite /commer !comp_lfunDl !comp_lfunDr
  !comp_lfunNr !comp_lfunNl !comp_lfunA !opprB !addrA
  (addrAC (_ - ((B \o A) \o C))) (addrAC (_ - ((C \o A) \o B))) addrK
  (addrAC (_ + ((B \o C) \o A))) (addrAC (_ - ((A \o B) \o C))) addrK
  (addrAC (_ - ((B \o A) \o C))) (addrAC (_ + ((B \o C) \o A))) addrNK
  (addrAC (_ - ((B \o A) \o C))) (addrAC (_ - ((A \o B) \o C))) addrK
  addrAC addrNK addrN.
Qed.

Lemma ave_commer_im A B (HA : A^A = A) (HB : B^A = B):
  forall v, (ave v (commer A B))^* = - ave v (commer A B).
Proof.
  by move => v;
  rewrite /ave conj_dotp -adj_dotEr adjfB !adjf_comp;
  rewrite HA HB -dotpNr -opp_lfunE opprB.
Qed.

Lemma ave_atcommer_rl A B (HA :A^A = A) (HB : B^A = B):
  forall v, (ave v (atcommer A B))^* = ave v (atcommer A B).
Proof.
  by move => v;
  rewrite /ave conj_dotp -adj_dotEr adjfD !adjf_comp;
  rewrite HA HB addrC.
Qed.

Lemma commer_subconst A B:
  forall a b, commer A B = commer (A - a*:\1) (B - b*:\1).
Proof.
  move => a b;
  rewrite /commer !comp_lfunDr !comp_lfunDl !comp_lfunNr !comp_lfunNl
    !opprD !opprK !constCr !constCl -!addrA; f_equal.
  rewrite [ - (_ \o _) + _ ]addrC !addrA -{1}(add0r (-(B \o A))); f_equal.
  rewrite -(addrN (a *: (b*:\1))); f_equal.
  rewrite -[LHS]addr0 -(addNr (a *: B)) addrA; f_equal.
  rewrite -!addrA addrC; f_equal.
  by rewrite addrC -addrA addrN addr0 !scalerA mulrC.
Qed.

Lemma commer_oppr A B:
  commer A (-B) = - commer A B.
Proof.
  by rewrite /commer comp_lfunNr comp_lfunNl opprD.
Qed.

End Commutator.

Lemma Heisenberg_uncertainty A B (HA : A^A = A) (HB : B^A = B) :
  forall u,
    (delta u A) * (delta u B) >= (2^-1) * `| ave u (commer A B) |.
Proof.
  move => v; apply sqr_ge0_le.
  by rewrite pmulr_rge0 // invr_gt0 addr_gt0 // ltr01.
  by apply mulr_ge0; apply delta_ge0.
  rewrite !exprMn_comm /comm mulrC // !delta_sqr mulrC.
  pose C:= (A - ave v A *:\1); pose D:= (B - ave v B *:\1); rewrite -/C -/D.
  have ->: commer A B = commer C D by rewrite -commer_subconst.
  have HC : C^A = C; have HD : D^A = D;
  try by rewrite adjfB (HA, HB) adjfZ adjf1 ave_real.
  apply le_trans with (y:=`|[< C v; D v>]| ^+ 2);
  try by rewrite /ave [C^+2]expr2o [D^+2]expr2o !comp_lfunE;
  rewrite -![ [< v ; _ >] ]adj_dotEl HC HD CauchySchwartz.
  rewrite [ `|[< C v ; _ >]| ^+ 2 ]normCK
    conj_dotp -!adj_dotEr -!comp_lfunE HC HD. 
  have ->: C \o D = (2^-1) *: (atcommer C D + commer C D) by
    rewrite add_commer scalerA mulVf (scale1r,pnatr_eq0).
  have ->: D \o C = (2^-1) *: (atcommer C D - commer C D) by
    rewrite sub_commer scalerA mulVf (scale1r,pnatr_eq0).
  rewrite !scale_lfunE !dotpZr [X in _ <= X]mulrA [X in _ <= X * _]mulrC
    -(ler_pM2l (_ : 0 < 2%:R * 2%:R)) ?normCKC ?mulrA ?mulfK
    ?divff ?pnatr_eq0 ?pmulr_rgt0 // !mul1r.
  have -> : [< v; (atcommer C D + commer C D) v >] * [< v; (atcommer C D - commer C D) v >] = (ave v (atcommer C D))^+2 - (ave v (commer C D))^+2
    by rewrite subrXX_comm ?/comm mulrC // !big_ord_recr big_ord0 /=
      add0r add_lfunE add_lfunE opp_lfunE !dotpDr dotpNr
      subn0 subnn !expr0 !expr1 mulr1 mul1r.
  by rewrite ave_commer_im // mulNr -expr2 -[ X in X <= _ ]sub0r lerD2r
    expr2 -[ X in _ * X ](ave_atcommer_rl HC HD) mul_conjC_ge0.
Qed.

Lemma Maccone_Pati_uncertainty_1p A B (HA : A ^A = A) (HB : B ^A = B):
  forall u v (Hortho : [<u;v>] = 0) (Hv : [<v;v>] = 1),
    (delta u A)^+2 + (delta u B)^+2 >=
      (2%:R^-1) * `| [< u ; (A + B) v>] | ^+2.
Proof.
  move => u v Hortho Hv;
  rewrite !delta_sqr_norm // -(ler_pM2l (_:0%:R < 2%:R)) ?ltr_nat //
    parallelogram_law mulrA divff ?pnatr_eq0 // mul1r -add_lfunE.
  apply le_trans with (y:=`|(A - ave u A *: \1 + (B - ave u B *: \1)) u| ^+ 2);
  last by rewrite lerDl -realEsqr ger0_real.
  have ->: [< u; (A + B) v >] = [< (A - ave u A *:\1 + (B - ave u B *:\1)) u; v >]
  by rewrite -adj_dotEr !adjfD !adjfN !adjfZ !adjf1 !ave_real // HA HB
    addrAC !addrA !add_lfunE !opp_lfunE !scale_lfunE !id_lfunE
    !dotpDr !dotpNr !dotpZr !Hortho !mulr0 !subr0.
  by rewrite -dotp_norm -[X in _ <= X]mulr1 -Hv CauchySchwartz.
Qed.

Lemma Maccone_Pati_uncertainty_1m A B (HA : A ^A = A) (HB : B ^A = B):
  forall u v (Hortho : [<u;v>] = 0) (Hv : [<v;v>] = 1),
    (delta u A)^+2 + (delta u B)^+2 >=
      (2%:R^-1) * `| [< u ; (A - B) v>] | ^+2.
Proof.
  move => u v Hortho Hv;
  have ->: delta u B = delta u (-B)
  by rewrite /delta ave_opp /ave; f_equal; f_equal; f_equal;
    rewrite -[LHS]sqrrN opprD scaleNr.
  by rewrite Maccone_Pati_uncertainty_1p // adjfN HB.
Qed.

Lemma Maccone_Pati_uncertainty_1 A B (HA : A ^A = A) (HB : B ^A = B):
  forall u v (Hortho : [<u;v>] = 0) (Hv : [<v;v>] = 1),
    (delta u A)^+2 + (delta u B)^+2 >= maxr
    ((2%:R^-1) * `| [< u ; (A + B) v>] | ^+2)
    ((2%:R^-1) * `| [< u ; (A - B) v>] | ^+2).
Proof.
  move => u v Hortho Hv; rewrite comparable_ge_max.
  by apply /andP; split;
    rewrite (Maccone_Pati_uncertainty_1m, Maccone_Pati_uncertainty_1p).
  rewrite real_comparable // realE; apply /orP; left;
  rewrite pmulr_rge0; try (by rewrite normCK mul_conjC_ge0);
  by rewrite invr_gt0 addr_gt0 // ltr01.
Qed.

Lemma Maccone_Pati_uncertainty_2m A B (HA : A ^A = A) (HB : B ^A = B):
  forall u v (Hortho : [<u;v>] = 0) (Hv : [<v;v>] = 1),
    (delta u A)^+2 + (delta u B)^+2 >= 
      -'i * (ave u (commer A B)) + `|[< u; (A - 'i *: B) v>] |^+2.
Proof.
  move => u v Hortho Hv; rewrite mulNr ge_addr.
  pose C:= (A - ave u A *:\1); pose D:= (B - ave u B *:\1);
  have HC : C^A = C; have HD : D^A = D;
  try by rewrite adjfB (HA, HB) adjfZ adjf1 ave_real.
  have ->: [< u; (A - 'i *: B) v >] = [< (C + 'i *: D) u; v >]
  by rewrite scalerDr scalerN -adj_dotEr !adjfD !adjfN !adjfZ !adjf1
    !ave_real // HA HB conjCi addrAC !addrA !add_lfunE !opp_lfunE !scale_lfunE
    !id_lfunE !dotpDr !dotpNr !dotpZr !Hortho !mulr0 !subr0 mulNr.
  have ->: delta u A ^+ 2 + delta u B ^+ 2 + 'i * ave u (commer A B)
    = `| (C + 'i *: D) u | ^+2 * `|v| ^+2
  by rewrite !delta_sqr_norm // -!dotp_norm Hv mulr1
    (commer_subconst _ _ (ave u A) (ave u B)) -/C -/D
    add_lfunE scale_lfunE dotpDl !dotpDr !dotpZl !dotpZr
    conjCi !mulNr mulrA mulCii mulNr mul1r opprK -!addrA;
  f_equal => [_ _ -> // |];
  rewrite addrA [RHS]addrC -mulrBr; f_equal; f_equal;
  rewrite -!adj_dotEr -dotpBr HC HD -!comp_lfunE -sub_lfunE.
  by rewrite -!dotp_norm CauchySchwartz.
Qed.

Lemma Maccone_Pati_uncertainty_2p A B (HA : A ^A = A) (HB : B ^A = B):
  forall u v (Hortho : [<u;v>] = 0) (Hv : [<v;v>] = 1),
    (delta u A)^+2 + (delta u B)^+2 >= 
      'i * (ave u (commer A B)) + `|[< u; (A + 'i *: B) v>] |^+2.
Proof.
  move => u v Hortho Hv;
  pose E:= -B; have ->: B = -E by rewrite opprK.
  by rewrite delta_opp commer_oppr ave_opp mulrN -mulNr
    scalerN Maccone_Pati_uncertainty_2m // adjfN HB.
Qed.

Lemma Maccone_Pati_uncertainty_2 A B (HA : A ^A = A) (HB : B ^A = B):
  forall u v (Hortho : [<u;v>] = 0) (Hv : [<v;v>] = 1),
    (delta u A)^+2 + (delta u B)^+2 >= maxr
      ('i * (ave u (commer A B)) + `|[< u;(A + 'i *: B) v>] |^+2)
      (-'i * (ave u (commer A B)) + `|[< u; (A - 'i *: B) v>] |^+2).
Proof.
  move => u v Hortho Hv; rewrite comparable_ge_max.
  by apply /andP; split;
    rewrite (Maccone_Pati_uncertainty_2p, Maccone_Pati_uncertainty_2m).
  by rewrite real_comparable // CrealE rmorphD rmorphM rmorphXn
    conj_normC ave_commer_im // ?rmorphN conjCi mulrNN.
Qed.

End Uncertainty.

Section CHSH.

Variable R : realType.

Definition bool2pm (b:bool) : R := if b then 1%:R else -1%:R.

Definition x1 (a : bool * bool * (bool * bool)) : R :=
  bool2pm a.1.1.
Definition x2 (a : bool * bool * (bool * bool)) : R :=
  bool2pm a.1.2.
Definition y1 (a : bool * bool * (bool * bool)) : R :=
  bool2pm a.2.1.
Definition y2 (a : bool * bool * (bool * bool)) : R :=
  bool2pm a.2.2.

Lemma b2pm_norm_le1: forall b, `| bool2pm b | <= 1%R.
Proof. by move => [] /=; rewrite ?mulr1n ?normrN normr1. Qed.

Definition b2pm4 (a : bool * bool * (bool * bool)) :=
  ((x1,x2),(y1,y2)). 

Lemma CHSH_inequality: forall mu : {distr (bool * bool * (bool * bool)) / R},
  \E_[mu] (x1 \* y1 \+ x1 \* y2 \+ x2 \* y1 \- x2 \* y2) <= (2%:R).
Proof.
  move => mu; rewrite exp_le_bd //.
  move => [[[][]][[][]]] /= ; rewrite /x1 /x2 /y1 /y2 /=;
  rewrite ?mulr1n ?mulrN ?mulNr ?opprK mulr1
    ?addrK ?addrNK ?addrN ?addNr ?add0r -?opprD ?normrN;
  (have <- : `|1| + `|1| = 2%:R by move => t; rewrite normr1);
  apply ler_normD.
Qed.

Lemma tentf_Z (T1 T2 S1 S2 : ihbFinType) (f : 'Hom[T1,T2]) (g : 'Hom[S1,S2]) a v:
  (f ⊗f g) (a *: v) = a *: ((f ⊗f g) v).
Proof. exact: linearZ. Qed.

Lemma tentf_B (T1 T2 S1 S2 : ihbFinType) (f : 'Hom[T1,T2]) (g : 'Hom[S1,S2]) u v:
  (f ⊗f g) (u - v) = ((f ⊗f g) u) - ((f ⊗f g) v).
Proof. exact: linearB. Qed.

Lemma PauliX'0 : ''X '0 = '1.
Proof. exact: PauliX_cb. Qed.

Lemma PauliX'1 : ''X '1 = '0.
Proof. exact: PauliX_cb. Qed.

Lemma PauliZ'0 : ''Z '0 = '0.
Proof. by rude_bmx. Qed.

Lemma PauliZ'1 : ''Z '1 = -'1.
Proof. by rude_bmx. Qed.

Definition Pauli' := (PauliX'0, PauliX'1, PauliZ'0, PauliZ'1).

Lemma CHSH_violation : forall (psi := sqrtC(2%:R)^-1 *: ('0 ⊗t '1 - '1 ⊗t '0))
  (X1 := ''X) (Y1 := sqrtC(2%:R)^-1 *: (- ''Z - ''X))
  (X2 := ''Z) (Y2 := sqrtC(2%:R)^-1 *: (''Z - ''X)),
    ave psi (X1 ⊗f Y1) + ave psi (X1 ⊗f Y2)
    + ave psi (X2 ⊗f Y1) - ave psi (X2 ⊗f Y2) = 2%:R * sqrtC(2%:R).
Proof.
  move => psi X1 Y1 X2 Y2; rewrite /ave.
  rewrite [X in (X + _ + _) - _ ]dotpZl [X in (_ + X + _) - _ ]dotpZl
    [X in (_ + _ + X) - _ ]dotpZl [X in _ - X]dotpZl
    !tentf_Z !tentfZr !tentfBr !scale_lfunE.
  rewrite !sub_lfunE !tentf_B !tentf_apply !opp_lfunE !Pauli'.
  rewrite !tentvNl !tentvNr !opprK !dotpZr -!mulrDr -!mulrBr
    !dotpBl !dotpBr !dotpDr !dotpNr !tentv_dot !t2tv_dot
    mulrA -normCKC /= -normrX sqrtCK ger0_norm;
  last by rewrite invr_ge0 addr_ge0 ?ler01.
  rewrite !mulr0 !mulr1 mulr1n mulr0n !opprD !opprK !addrA !subr0 !addr0 add0r.
  have ->: 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 2 * 2 * 2 by
    move => t; have ->: 2 = 1 + 1 by []; rewrite !mulrDr !mulrDl !mulr1 !addrA.
  rewrite !mulrA mulrC; f_equal;
  by rewrite mulrC !mulrA divff ?pnatr_eq0 // mul1r -{2}(sqrtCK 2) expr2 mulrA
    -sqrtCM ?mulVf // ?nnegrE ?invr_ge0 ?addr_ge0 ?ler01// sqrtC1 mul1r.
Qed.

End CHSH.