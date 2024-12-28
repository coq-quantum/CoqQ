From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean interval finmap.
From mathcomp Require Import perm fingroup.
From mathcomp.analysis Require Import -(notations)forms.
From quantum.external Require Import complex.
From mathcomp.real_closed Require Import mxtens.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import signed reals ereal topology normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure lebesgue_integral numfun exp.
From mathcomp Require Import convex itv realfun derive hoelder.
Require Import notation mcextra mcaextra cpo mxpred svd majorization extnum ctopology.
From quantum.external Require Import spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports ExtNumTopology.

(******************************************************************************)
(*                             Matrix Norms                                   *)
(* -------------------------------------------------------------------------- *)
(* lpnorm p of matrix                                                         *)
(*      hoelder's inequality, cauchy's inequality of lpnorm                   *)
(* ipqnorm p q of matrix, induced norm                                        *)
(* schnorm p : schattern norm, i.e., lpnorm p over its singular values        *)
(*      generalized hoelder's inequlity of schnorm                            *)
(* l1norm := lpnorm 1; l2norm := lpnorm 2                                     *)
(* i2norm := ipqnorm 2 2   induced 2-norm                                     *)
(* fbnorm := schnorm 2 : Frobenius norm (= l2norm)                            *)
(* trnorm := schnorm 1 : trace/nuclear norm                                   *)
(******************************************************************************)
(* convergence w.r.t. lowner order of matrices                                *)
(* denmx forms CPO                                                            *)
(******************************************************************************)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "'\l_' p | M |" (at level 2, format "'\l_' p |  M  |").
Reserved Notation "'\l_' ( p ) | M |" (at level 2).
Reserved Notation "'\l1|' M |" (at level 2).
Reserved Notation "'\l2|' M |" (at level 2).
Reserved Notation "'\i_' p | M |" (at level 2, format "'\i_' p |  M  |").
Reserved Notation "'\i_' ( p ) | M |" (at level 2).
Reserved Notation "'\i_' ( p , q ) | M |" 
  (at level 2, format "'\i_' ( p ,  q ) |  M  |").
Reserved Notation "'\i2' | M |" (at level 2).
Reserved Notation "'\s_' p | M |" (at level 2, format "'\s_' p |  M  |").
Reserved Notation "'\s_' ( p ) | M |" (at level 2).
Reserved Notation "\fb| M |" (at level 2).
Reserved Notation "\tr| M |" (at level 2).

(* structure for conjugate index *)
(* extended conjugate index : p^-1 + q^-1 = 1 with 0 <= p and 0 <= q *)
(*                            which accept p = 0 and q = 1, where 0  *)
(*                            is defined as oo, i.e., f 0 = limn f   *)
(* (strict) conjugate index : p^-1 + q^-1 = 1 with 0 < p and 0 < q   *)
(*                            where we do not consider the infinite case *)

HB.mixin Record isEConjugateIndex (R : realType) (p q : R) := {
  ci_p_ge0 : 0 <= p;
  ci_q_ge0 : 0 <= q;
  invfD_eq1 : (p : R) ^-1 + q^-1 = 1;
}.

#[short(type="ecindexType")]
HB.structure Definition EConjugateIndex (R : realType) (p : R) := 
  {q of @isEConjugateIndex R p q}.

Arguments ci_p_ge0 {R} {p} s.
Arguments ci_q_ge0 {R} {p} s.
Arguments invfD_eq1 {R} {p} s.

HB.mixin Record EConjugateIndex_isConjugate (R : realType) (p q : R) := {
  ci_p_gt0 : 0 < p;
  ci_q_gt0 : 0 < q;
}.

#[short(type="cindexType")]
HB.structure Definition ConjugateIndex (R : realType) (p : R) := 
  {q of @EConjugateIndex_isConjugate R p q & @isEConjugateIndex R p q}.

Arguments ci_p_gt0 {R} {p} s.
Arguments ci_q_gt0 {R} {p} s.

HB.factory Record isConjugateIndex (R : realType) (p q : R) := {
  p_gt0 : 0 < p;
  q_gt0 : 0 < q;
  invfD_eq1 : p^-1 + q^-1 = 1
}.

HB.builders Context R p q of isConjugateIndex R p q.

HB.instance Definition _ := 
  isEConjugateIndex.Build R p q (ltW p_gt0) (ltW q_gt0) invfD_eq1.
HB.instance Definition _ := 
  EConjugateIndex_isConjugate.Build R p q p_gt0 q_gt0.

HB.end.

Section ConjugateIndex_Theory.
Variable (R : realType).

Lemma conjugate_index_ge0 (p : R) (Hp : 1 <= p) : 0 <= p / (p - 1).
Proof.
move: Hp; rewrite le_eqVlt=>/orP[/eqP<-|Pp].
by rewrite subrr invr0 mulr0.
by rewrite ler_pdivlMr ?mul0r ?subr_gt0// ltW// (lt_trans ltr01 Pp).
Qed.

Lemma conjugate_index_invfD_eq1 (p : R) (Hp : 1 <= p) : p^-1 + (p / (p - 1))^-1 = 1.
Proof.
move: Hp; rewrite le_eqVlt=>/orP[/eqP<-|Pp].
by rewrite subrr invr0 mulr0 invr0 invr1 addr0.
by rewrite invfM invrK mulrBr mulr1 addrC subrK mulVf// gt_eqF// (lt_trans ltr01 Pp).
Qed.

Definition econjugate_index (p : R) (Hp : 1 <= p) : ecindexType p := 
  HB.pack (p / (p - 1)) (isEConjugateIndex.Build R p (p / (p - 1)) 
  (le_trans ler01 Hp) (conjugate_index_ge0 Hp) (conjugate_index_invfD_eq1 Hp)).

Lemma conjugate_index_gt0 (p : R) (Hp : 1 < p) : 0 < p / (p - 1).
Proof. by rewrite ltr_pdivlMr ?mul0r ?subr_gt0// (lt_trans ltr01 Hp). Qed.

Definition conjugate_index (p : R) (Hp : 1 < p) : cindexType p := 
  HB.pack (p / (p - 1)) (isConjugateIndex.Build R p (p / (p - 1)) 
  (lt_trans ltr01 Hp) (conjugate_index_gt0 Hp) (conjugate_index_invfD_eq1 (ltW Hp))).

Lemma invfDC_eq1 (p : R) (q : ecindexType p) : (q : R)^-1 + p^-1 = 1.
Proof. by rewrite addrC invfD_eq1. Qed.

HB.instance Definition _ p (q : ecindexType p) :=
  isEConjugateIndex.Build R q p (ci_q_ge0 q) (@ci_p_ge0 R _ q) (@invfDC_eq1 p q).

HB.instance Definition _ p (q : cindexType p) :=
  isConjugateIndex.Build R q p (ci_q_gt0 q) (@ci_p_gt0 R _ q) (@invfDC_eq1 p q).

Lemma ci_p_eqVge (p : R) (q : ecindexType p) : (p == 0) || (1 <= p).
Proof.
case: q=>/= q [][] Pp Pq Ppq.
move: Pp; rewrite le_eqVlt=>/orP[/eqP<-|Pp].
by move: Pq Ppq; rewrite eqxx/= le_eqVlt=>/orP[/eqP <- /eqP|Pq Ppq].
by rewrite gt_eqF//= -invf_le1// -Ppq lerDl invr_ge0.
Qed.

Lemma ci_q_eqVge (p : R) (q : ecindexType p) : ((q : R) == 0) || (1 <= (q : R)).
Proof. by apply/(ci_p_eqVge p). Qed.

(* ecindex is either cindex or 0 or 1 *)
Variant ecindex_spec (p : R) (q : ecindexType p) : Type :=
  | ECSpec_CIndex (r : cindexType p) of (q = r :> R) : @ecindex_spec p q
  | ECSpec_p0q1   of (q = 1 :> R) & p = 0 : @ecindex_spec p q
  | ECSpec_p1q0   of (q = 0 :> R) & p = 1 : @ecindex_spec p q.

Lemma ecindexP (p : R) (q : ecindexType p) : @ecindex_spec p q.
Proof.
move: (ci_q_eqVge q)=>/orP/decide_or[/eqP Pq|].
by apply ECSpec_p1q0=>//; move: (invfD_eq1 q); 
  rewrite Pq invr0 addr0=>/eqP; rewrite invr_eq1=>/eqP.
move=>Pq; move: (ci_p_eqVge q)=>/orP/decide_or[/eqP Pp|Pp].
by apply ECSpec_p0q1=>//; move: (invfD_eq1 q);
  rewrite {1}Pp invr0 add0r=>/eqP; rewrite invr_eq1=>/eqP.
pose r : cindexType p := HB.pack (q : R) 
  (isConjugateIndex.Build R p (q : R) (lt_le_trans ltr01 Pp) 
  (lt_le_trans ltr01 Pq) (invfD_eq1 q)).
by apply (@ECSpec_CIndex p q r).
Qed.

(* Goal test11 (p : R) (q : ecindexType p) : p <= (q : R).
case: (ecindexP q)=>[r ->|-> ->|-> ->]. *)
(* compare with 0 *)
Lemma ci_p_eq0 (p : R) (q : cindexType p) : (p == 0) = false.
Proof. by rewrite gt_eqF// (ci_p_gt0 q). Qed.
Lemma ci_q_eq0 (p : R) (q : cindexType p) : ((q : R) == 0) = false.
Proof. apply/(ci_p_eq0 p). Qed.
Lemma ci_p_neq0 (p : R) (q : cindexType p) : p != 0.
Proof. by rewrite (ci_p_eq0 q). Qed.
Lemma ci_q_neq0 (p : R) (q : cindexType p) : (q : R) != 0.
Proof. apply/(ci_p_neq0 p). Qed.
Lemma ci_pV_eq0 (p : R) (q : cindexType p) : (p^-1 == 0) = false.
Proof. by rewrite gt_eqF// invr_gt0 (ci_p_gt0 q). Qed.
Lemma ci_qV_eq0 (p : R) (q : cindexType p) : ((q : R)^-1 == 0) = false.
Proof. apply/(ci_pV_eq0 p). Qed.
Lemma ci_pV_neq0 (p : R) (q : cindexType p) : p^-1 != 0.
Proof. by rewrite (ci_pV_eq0 q). Qed.
Lemma ci_qV_neq0 (p : R) (q : cindexType p) : (q : R)^-1 != 0.
Proof. apply/(ci_pV_neq0 p). Qed.

(* compare wiht 1 *)
Lemma ci_p_gt1 (p : R) (q : cindexType p) : 1 < p.
Proof. 
by rewrite -invf_lt1 ?(ci_p_gt0 q)// -(invfD_eq1 q) ltrDl invr_gt0 (ci_q_gt0 q).
Qed.
Lemma ci_p_ge1 (p : R) (q : cindexType p) : 1 <= p.
Proof. by apply/ltW/(ci_p_gt1 q). Qed.
Lemma ci_q_gt1 (p : R) (q : cindexType p) : 1 < (q : R).
Proof. apply/(ci_p_gt1 p). Qed.
Lemma ci_q_ge1 (p : R) (q : cindexType p) : 1 <= (q : R).
Proof. apply/(ci_p_ge1 p). Qed.
Lemma ci_p_eq1 (p : R) (q : cindexType p) : (p == 1) = false.
Proof. by rewrite gt_eqF// (ci_p_gt1 q). Qed.
Lemma ci_q_eq1 (p : R) (q : cindexType p) : ((q : R) == 1) = false.
Proof. apply/(ci_p_eq1 p). Qed.
Lemma ci_p_neq1 (p : R) (q : cindexType p) : p != 1.
Proof. by rewrite (ci_p_eq1 q). Qed.
Lemma ci_q_neq1 (p : R) (q : cindexType p) : (q : R) != 1.
Proof. apply/(ci_p_neq1 p). Qed.

Lemma invf_le2 (F : numFieldType) (x : F) : 0 < x -> (x^-1 <= 2) = (2^-1 <= x).
Proof. by move=>Px; rewrite -{1}[2]invrK lef_pV2// ?posrE invr_gt0. Qed.
Lemma invf_lt2 (F : numFieldType) (x : F) : 0 < x -> (x^-1 < 2) = (2^-1 < x).
Proof. by move=>Px; rewrite -{1}[2]invrK ltf_pV2// ?posrE invr_gt0. Qed.
Lemma invf_ge2 (F : numFieldType) (x : F) : 0 < x -> (2 <= x^-1) = (x <= 2^-1).
Proof. by move=>Px; rewrite -{1}[2]invrK lef_pV2// ?posrE invr_gt0. Qed.
Lemma invf_gt2 (F : numFieldType) (x : F) : 0 < x -> (2 < x^-1) = (x < 2^-1).
Proof. by move=>Px; rewrite -{1}[2]invrK ltf_pV2// ?posrE invr_gt0. Qed.

Lemma ci_pE (p : R) (q : ecindexType p) : p = (1 - (q : R)^-1)^-1.
Proof. by rewrite -(invfD_eq1 q) addrK invrK. Qed.
Lemma ci_pVE (p : R) (q : ecindexType p) : p^-1 = 1 - (q : R)^-1.
Proof. by rewrite -(invfD_eq1 q) addrK. Qed.

Lemma ci_qE (p : R) (q : ecindexType p) : q = (1 - p^-1)^-1 :> R.
Proof. apply/(ci_pE p). Qed.
Lemma ci_qVE (p : R) (q : ecindexType p) : (q : R)^-1 = 1 - p^-1.
Proof. apply/(ci_pVE p). Qed.

(* compare with 2 *)
(* 2 <= p  =  q <= 2  =  q <= p *)
Lemma ci_pge2_qle2 (p : R) (q : cindexType p) :
  (2 <= p) = ((q : R) <= 2).
Proof.
by rewrite -lef_pV2 ?posrE// ?(ci_p_gt0 q)// (ci_pVE q) 
  -{1}split21 lerBlDl lerD2r lef_pV2// posrE ?(ci_q_gt0 q).
Qed.

Lemma ci_pgt2_qlt2 (p : R) (q : cindexType p) :
  (2 < p) = ((q : R) < 2).
Proof.
by rewrite -ltf_pV2 ?posrE// ?(ci_p_gt0 q)// (ci_pVE q) 
  -{1}split21 ltrBlDl ltrD2r ltf_pV2// posrE ?(ci_q_gt0 q).
Qed.

Lemma ci_ple2_qge2 (p : R) (q : cindexType p) :
  (p <= 2) = (2 <= (q : R)).
Proof. by rewrite leNgt (ci_pgt2_qlt2 q) leNgt. Qed.

Lemma ci_plt2_qgt2 (p : R) (q : cindexType p) :
  (p < 2) = (2 < (q : R)).
Proof. by rewrite ltNge (ci_pge2_qle2 q) ltNge. Qed.

Lemma ci_pge2_qlep (p : R) (q : cindexType p) :
  (2 <= p) = ((q : R) <= p).
Proof.
case: leP=>Pp; move: {+}Pp.
by rewrite (ci_pge2_qle2 q) => /le_trans/(_ Pp)->.
by rewrite (ci_plt2_qgt2 q) leNgt => /(lt_trans Pp)->.
Qed.

Lemma ci_pgt2_qltp (p : R) (q : cindexType p) :
  (2 < p) = ((q : R) < p).
Proof.
case: leP=>Pp; move: {+}Pp.
by rewrite (ci_ple2_qge2 q) ltNge => /(le_trans Pp)->.
by rewrite (ci_pgt2_qlt2 q) => /lt_trans/(_ Pp)->.
Qed.

Lemma ci_ple2_pleq (p : R) (q : cindexType p) :
  (p <= 2) = (p <= (q : R)).
Proof. by rewrite leNgt (ci_pgt2_qltp q) leNgt. Qed.

Lemma ci_plt2_pltq (p : R) (q : cindexType p) :
  (p < 2) = (p < (q : R)).
Proof. by rewrite ltNge (ci_pge2_qlep q) ltNge. Qed.

Lemma ci_qge2_ple2 (p : R) (q : cindexType p) :
  (2 <= (q : R)) = (p <= 2).
Proof. apply/(ci_pge2_qle2 p). Qed.

Lemma ci_qgt2_plt2 (p : R) (q : cindexType p) :
  (2 < (q : R)) = (p < 2).
Proof. apply/(ci_pgt2_qlt2 p). Qed.

Lemma ci_qle2_pge2 (p : R) (q : cindexType p) :
  ((q : R) <= 2) = (2 <= p).
Proof. apply/(ci_ple2_qge2 p). Qed.

Lemma ci_qlt2_pgt2 (p : R) (q : cindexType p) :
  ((q : R) < 2) = (2 < p).
Proof. apply/(ci_plt2_qgt2 p). Qed.

Lemma ci_qge2_pleq (p : R) (q : cindexType p) :
  (2 <= (q : R)) = (p <= (q : R)).
Proof. apply/(ci_pge2_qlep p). Qed.

Lemma ci_qgt2_pltq (p : R) (q : cindexType p) :
  (2 < (q : R)) = (p < (q : R)).
Proof. apply/(ci_pgt2_qltp p). Qed.

Lemma ci_qle2_qlep (p : R) (q : cindexType p) :
  ((q : R) <= 2) = ((q : R) <= p).
Proof. apply/(ci_ple2_pleq p). Qed.

Lemma ci_qlt2_qltp (p : R) (q : cindexType p) :
  ((q : R) < 2) = ((q : R) < p).
Proof. apply/(ci_plt2_pltq p). Qed.

Lemma ci_pleq_cp2 (p : R) (q : cindexType p) : 
  p <= (q : R) -> (2 <= q :> R) && (p <= 2).
Proof. by rewrite (ci_ple2_pleq q) (ci_qge2_pleq q)=>->. Qed.

Lemma ci_qlep_cp2 (p : R) (q : cindexType p) : 
  (q : R) <= p -> (q <= 2 :> R) && (2 <= p).
Proof. by rewrite andbC; move=>/ci_pleq_cp2. Qed.

Lemma ci_pltq_cp2 (p : R) (q : cindexType p) : 
  p < (q : R) -> (2 < q :> R) && (p < 2).
Proof. by rewrite (ci_plt2_pltq q) (ci_qgt2_pltq q)=>->. Qed.

Lemma ci_qltp_cp2 (p : R) (q : cindexType p) : 
  (q : R) < p -> (q < 2 :> R) && (2 < p).
Proof. by rewrite andbC; move=>/ci_pltq_cp2. Qed.

HB.instance Definition _ := 
  isConjugateIndex.Build R 2 2 (ltr0Sn R 1) (ltr0Sn R 1) (@split21 R).

Definition conjugate_index_2 := ((2 : R) : cindexType 2).

Lemma invr01D_subproof : 0^-1 + 1^-1 = 1 :> R.
Proof. by rewrite invr0 invr1 add0r. Qed.

HB.instance Definition _ := 
  isEConjugateIndex.Build R 0 1 (lexx 0) ler01 invr01D_subproof.

HB.instance Definition _ := 
  EConjugateIndex.copy 0 ((0 : R) : ecindexType 1).

Definition conjugate_index_0 := ((1 : R) : ecindexType 0).
Definition conjugate_index_1 := ((0 : R) : ecindexType 1).

End ConjugateIndex_Theory.

#[global] Hint Extern 0 (is_true (0 <= _ `^ _)) => apply: powR_ge0 : core.

Section Hoelder_Fin.
Variable (R : realType).

Lemma hoelder_ord n (a b : 'I_n -> R) (p : R) (q : cindexType p) :
  (forall i, 0 <= a i) -> (forall i, 0 <= b i) ->
  \sum_i a i * b i <= (\sum_i (a i) `^ p) `^ p^-1 *
                      (\sum_i (b i) `^ q) `^ (q : R)^-1.
Proof.
move: (ci_p_gt0 q) (ci_q_gt0 q) (invfD_eq1 q)=> p0 q0 pq a0 b0.
pose f (c : 'I_n -> R) (i : nat) : R := match (i < n)%N =P true with
                  | ReflectT E => c (Ordinal E)
                  | _ => 0 end.
have mf c : measurable_fun setT (f c) by [].
have := hoelder [the measure _ _ of counting] (mf a) (mf b) p0 q0 pq.
rewrite !Lnorm_counting//.
rewrite (nneseries_split 0 n); last by move=> k; rewrite lee_fin powR_ge0.
rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
move=> i _ /=; rewrite andbT /f =>/leq_gtF; case: eqP=>[p1 | _ _];
by rewrite ?p1// mulr0 normr0 powR0.
rewrite (nneseries_split 0 n); last by move=> k; rewrite lee_fin powR_ge0.
rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
move=> i _ /=; rewrite andbT /f =>/leq_gtF; case: eqP=>[p1 | _ _];
by rewrite ?p1// normr0 powR0// gt_eqF.
rewrite (nneseries_split 0 n); last by move=> k; rewrite lee_fin powR_ge0.
rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
move=> i _ /=; rewrite andbT /f =>/leq_gtF; case: eqP=>[p1 | _ _];
by rewrite ?p1// normr0 powR0// gt_eqF.
rewrite !big_mkord/= !sumEFin !poweR_EFin -EFinM invr1 lee_fin powRr1;
last by rewrite sumr_ge0// =>i _; rewrite powR_ge0.
have ->: \sum_(i < n) normr (f a i * f b i) `^ 1 = \sum_(i < n) a i * b i.
apply eq_bigr => [[i Pi]] _; rewrite powRr1// /f; case: eqP=>/=[p1 | ];
by rewrite ?Pi// (eq_irrelevance Pi p1) ger0_norm// mulr_ge0.
have ->: \sum_(i < n) normr (f a i) `^ p = \sum_(i < n) a i `^ p.
apply eq_bigr => [[i Pi]] _; f_equal; rewrite /f; case: eqP=>/=[p1 | ];
by rewrite ?Pi// (eq_irrelevance Pi p1) ger0_norm.
have -> //: \sum_(i < n) normr (f b i) `^ q = \sum_(i < n) b i `^ q.
apply eq_bigr => [[i Pi]] _; f_equal; rewrite /f; case: eqP=>/=[p1 | ];
by rewrite ?Pi// (eq_irrelevance Pi p1) ger0_norm.
Qed.

Lemma hoelder_seq I (r : seq I) (P : pred I) (a b : I -> R) (p : R) (q : cindexType p) :
  (forall i, P i -> 0 <= a i) -> (forall i, P i -> 0 <= b i) ->
  \sum_(i <- r | P i) a i * b i <= (\sum_(i <- r | P i) (a i) `^ p) `^ p^-1 *
                      (\sum_(i <- r | P i) (b i) `^ q) `^ (q : R)^-1.
Proof.
move=>a0 b0.
case: r=>[|x0 r0].
  by rewrite !big_nil !powR0 ?(ci_pV_neq0 q) ?(ci_qV_neq0 q) ?mulr0.
set r := x0 :: r0.
rewrite -big_filter -[in X in X * _]big_filter -[in X in _ * X]big_filter.
rewrite !(big_nth x0) !big_mkord; apply: hoelder_ord=>// i; 
  [apply/a0|apply/b0]; apply/seq_nth_ord_size_true.
Qed.

Lemma hoelder_fin (I : finType) (P : pred I) (a b : I -> R) (p : R) (q : cindexType p) :
  (forall i, 0 <= a i) -> (forall i, 0 <= b i) ->
  \sum_(i | P i) a i * b i <= (\sum_(i | P i) (a i) `^ p) `^ p^-1 *
                      (\sum_(i | P i) (b i) `^ q) `^ (q : R)^-1.
Proof. by move=>a0 b0; apply: hoelder_seq. Qed.

End Hoelder_Fin.

Section Hoelder_Gen_Fin.
Variable (R : realType).

Lemma hoelder_gen_seq I (s : seq I) (P : pred I) (a b : I -> R) (p q r : R) :
  (forall i, P i -> 0 <= a i) -> (forall i, P i -> 0 <= b i) ->
  (1 <= p) -> (1 <= q) -> (1 <= r) -> (p^-1 + q^-1 = r^-1) ->
  (\sum_(i <- s | P i) (a i * b i) `^ r) `^ r^-1 <= (\sum_(i <- s | P i) (a i) `^ p) `^ p^-1 *
                      (\sum_(i <- s | P i) (b i) `^ q) `^ (q : R)^-1.
Proof.
move=>Pa Pb Pp Pq Pr Ppqr; move: (le_trans ler01 Pr)=>Pr0.
have Pr1 : r != 0 by rewrite ?gt_eqF// (lt_le_trans ltr01 Pr).
have Hp : 0 < p / r by rewrite divr_gt0// ?(lt_le_trans ltr01).
have Hq : 0 < q / r by rewrite divr_gt0// ?(lt_le_trans ltr01).
have Hpq : (p/r)^-1 + (q/r)^-1 = 1.
  by rewrite !invfM -mulrDl Ppqr mulfV// gt_eqF// invr_gt0 (lt_le_trans ltr01).
pose t : cindexType (p/r) :=
  HB.pack (q/r) (isConjugateIndex.Build R (p/r) (q/r) Hp Hq Hpq). 
apply/(le_trans (y := (\sum_(i <- s | P i) (a i) `^ r * (b i) `^ r) `^ r^-1)).
  by rewrite ge0_ler_powR// ?invr_ge0// ?nnegrE ?sumr_ge0// 
    ?ler_sum// =>i Pi; rewrite -powRM// ?Pa ?Pb.
apply/(le_trans (y := ((\sum_(i <- s | P i) (a i) `^ r `^ (p/r)) `^ (p/r)^-1 * 
  (\sum_(i <- s | P i) (b i) `^ r `^ (q/r)) `^ (q/r)^-1) `^ r^-1)).
  rewrite ge0_ler_powR// ?invr_ge0// ?nnegrE ?mulr_ge0 ?sumr_ge0//.
    by move=>??; apply mulr_ge0.
  by apply (hoelder_seq _ t).
by rewrite powRM// ler_pM// -powRrM invfM invrK mulfK ?ge0_ler_powR//
  ?nnegrE ?sumr_ge0// ?invr_ge0 ?(le_trans ler01 Pp)//
  ?(le_trans ler01 Pq)// ler_sum// =>i Pi;
  rewrite -powRrM mulrC mulfVK.
Qed.

Lemma hoelder_gen_fin (I : finType) (P : pred I) (a b : I -> R) (p q r : R) :
  (forall i, 0 <= a i) -> (forall i, 0 <= b i) ->
  (1 <= p) -> (1 <= q) -> (1 <= r) -> (p^-1 + q^-1 = r^-1) ->
  (\sum_(i | P i) (a i * b i) `^ r) `^ r^-1 <= (\sum_(i | P i) (a i) `^ p) `^ p^-1 *
                      (\sum_(i | P i) (b i) `^ q) `^ (q : R)^-1.
Proof. by move=>a0 b0; apply: hoelder_gen_seq. Qed.

End Hoelder_Gen_Fin.

Section Minkowski_Fin.
Variable (R : realType).

Lemma minkowski_ord n (a b : 'I_n -> R) p : 
  (forall i, 0 <= a i) -> (forall i, 0 <= b i) -> 1 <= p -> 
    (\sum_i (a i + b i) `^ p) `^ p^-1 <= (\sum_i (a i) `^ p) `^ p^-1 + 
                                   (\sum_i (b i) `^ p) `^ p^-1.
Proof.
move=> a0 b0 p1.
have p0 : 0 < p by apply: (lt_le_trans ltr01 p1).
pose f (c : 'I_n -> R) (i : nat) : R := match (i < n)%N =P true with
                    | ReflectT E => c (Ordinal E)
                    | _ => 0 end.
have mf c : measurable_fun setT (f c) by [].
have := minkowski [the measure _ _ of counting] (mf a) (mf b) p1.
rewrite !Lnorm_counting//.
rewrite (nneseries_split 0 n); last by move=> k; rewrite lee_fin powR_ge0.
rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
  move=> i _ /=; rewrite andbT /f =>/leq_gtF; case: eqP=>[p2 | _ _];
  by rewrite ?p2// addr0 normr0 powR0// gt_eqF.
rewrite (nneseries_split 0 n); last by move=> k; rewrite lee_fin powR_ge0.
rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
  move=> i _ /=; rewrite andbT /f =>/leq_gtF; case: eqP=>[p2 | _ _];
  by rewrite ?p2// normr0 powR0// gt_eqF.
rewrite (nneseries_split 0 n); last by move=> k; rewrite lee_fin powR_ge0.
rewrite add0n ereal_series_cond eseries0 ?adde0; last first.
  move=> i _ /=; rewrite andbT /f =>/leq_gtF; case: eqP=>[p2 | _ _];
  by rewrite ?p2// normr0 powR0// gt_eqF.
rewrite !big_mkord/= !sumEFin !poweR_EFin -EFinD lee_fin.
have ->: \sum_(i < n) `| f a i + f b i | `^ p = \sum_(i < n) (a i + b i) `^ p.
  apply eq_bigr => [[i Pi]] _; f_equal; rewrite /f; case: eqP=>/=[p2 | ];
  by rewrite ?Pi// (eq_irrelevance Pi p2) ger0_norm// addr_ge0.
have ->: \sum_(i < n) normr (f a i) `^ p = \sum_(i < n) a i `^ p.
  apply eq_bigr => [[i Pi]] _; f_equal; rewrite /f; case: eqP=>/=[p2 | ];
  by rewrite ?Pi// (eq_irrelevance Pi p2) ger0_norm.
have -> //: \sum_(i < n) normr (f b i) `^ p = \sum_(i < n) b i `^ p.
  apply eq_bigr => [[i Pi]] _; f_equal; rewrite /f; case: eqP=>/=[p2 | ];
  by rewrite ?Pi// (eq_irrelevance Pi p2) ger0_norm.
Qed.

Lemma minkowski_seq I (r : seq I) (P : pred I) (a b : I -> R) (p : R) :
  (forall i, P i -> 0 <= a i) -> (forall i, P i -> 0 <= b i) -> 1 <= p -> 
  (\sum_(i <- r | P i)  (a i + b i) `^ p) `^ p^-1 <= 
      (\sum_(i <- r | P i)  (a i) `^ p) `^ p^-1 + 
      (\sum_(i <- r | P i)  (b i) `^ p) `^ p^-1.
Proof.
move=>a0 b0 p1; case: r=>[|x0 r0].
  by rewrite !big_nil !powR0// invr_eq0 gt_eqF//; apply: (lt_le_trans ltr01 p1).
set r := x0 :: r0.
rewrite -big_filter -[in X in X + _]big_filter -[in X in _ + X]big_filter.
rewrite !(big_nth x0) !big_mkord; apply: minkowski_ord=>// i; 
  [apply/a0|apply/b0]; apply/seq_nth_ord_size_true.
Qed.

Lemma minkowski_fin (I : finType) (P : pred I) (a b : I -> R) (p : R) :
  (forall i, 0 <= a i) -> (forall i, 0 <= b i) -> 1 <= p -> 
  (\sum_(i | P i)  (a i + b i) `^ p) `^ p^-1 <= 
      (\sum_(i | P i)  (a i) `^ p) `^ p^-1 + 
      (\sum_(i | P i)  (b i) `^ p) `^ p^-1.
Proof. by move=>a0 b0; apply: minkowski_seq. Qed.

End Minkowski_Fin.

HB.lock Definition normrc (R : realType) (C : extNumType R) (x : C) := c2r `|x|.
Notation "``| x |" := (normrc x) : ring_scope.

Section NormRC.
Variable (R : realType) (C : extNumType R).
Implicit Type (x y : C).

Lemma normrcE x : r2c ``| x | = `| x |.
Proof. by rewrite normrc.unlock/= c2rK. Qed.

Lemma normrc0_eq0 x : ``| x | = 0 -> x = 0.
Proof. by move=>/(f_equal (@r2c _ C)); rewrite normrcE r2c0=>/normr0_eq0. Qed.

Lemma normrc0 : ``| (0 : C) | = 0.
Proof. by rewrite normrc.unlock normr0 c2r0. Qed.

Lemma normrc1 : ``| (1 : C) | = 1.
Proof. by rewrite normrc.unlock normr1 c2r1. Qed.

Lemma normrc0P x : reflect (``|x| = 0) (x == 0).
Proof. apply: (iffP eqP)=> [->|/normrc0_eq0 //]; apply: normrc0. Qed.

Lemma normrcN x : ``| - x | = ``| x |.
Proof. by apply/(@r2c_inj _ C); rewrite !normrcE normrN. Qed.

Definition normrc_eq0 x := sameP (``|x| =P 0) (normrc0P x).

Lemma distcrC x y : ``|x - y| = ``|y - x|.
Proof. by rewrite -opprB normrcN. Qed.

Lemma normrc_sum I (r : seq I) (P : pred I) (f : I -> C) :
  (forall i, P i -> 0 <= f i) ->
  ``| \sum_(i <- r | P i) f i | = \sum_(i <- r | P i) ``|f i|.
Proof.
move=>Pf; apply/(@r2c_inj _ C).
rewrite normrcE rmorph_sum ger0_norm; last by apply sumr_ge0.
by apply eq_bigr=>i Pi; rewrite normrcE ger0_norm// Pf.
Qed.

Lemma ler_normrcD (x y : C) : ``| x + y | <= ``|x| + ``|y|.
Proof. by rewrite -(@ler_r2c _ C) rmorphD !normrcE ler_normD. Qed.

Lemma normrc_ge0 (x : C) : 0 <= ``| x |.
Proof. by rewrite -(@r2c_ge0 _ C) normrcE. Qed.

Lemma ger0_normrc (x : C) : 
  0 <= x -> ``|x| = c2r x.
Proof. by move=>Px; rewrite normrc.unlock ger0_norm. Qed.

Lemma normrc_id (x : C) : `| ``| x | | = ``| x |.
Proof. by rewrite ger0_norm// normrc_ge0. Qed.

Lemma normrc_idV (x : C) : ``| `| x | | = ``| x |.
Proof. by rewrite normrc.unlock normr_id. Qed.

Lemma normrc_le0 x : ``|x| <= 0 = (x == 0).
Proof. by rewrite -(@r2c_le0 _ C) normrcE normr_le0. Qed.

Lemma normrc_lt0 x : ``|x| < 0 = false.
Proof. by rewrite -(@r2c_lt0 _ C) normrcE normr_lt0. Qed.

Lemma normrc_gt0 x : ``|x| > 0 = (x != 0).
Proof. by rewrite lt_def normrc_eq0 normrc_ge0 andbT. Qed.

Lemma normrcM x y : ``|x * y| = ``|x| * ``|y|.
Proof. by apply/(@r2c_inj _ C); rewrite rmorphM !normrcE normrM. Qed.

Lemma normrcXn n x : ``| x ^+ n | = ``|x| ^+ n.
Proof.
elim: n =>[|n IH]; first by rewrite !expr0 normrc1.
by rewrite !exprS -IH -normrcM.
Qed.

Lemma ler_normrc_sum I (r : seq I) (P : pred I) (f : I -> C) : 
  ``| \sum_(i <- r | P i) f i | <= \sum_(i <- r | P i) ``|f i|.
Proof.
elim/big_rec2: _ =>[|?????]. by rewrite normrc0.
by apply/(le_trans (ler_normrcD _ _)); rewrite lerD2l.
Qed.

End NormRC.

Lemma normrc_conjC (R : realType) (x : R[i]) : ``|x^*| = ``|x|.
Proof. by apply/(@r2c_inj _ R[i]); rewrite !normrcE norm_conjC. Qed.

Lemma normrcV (R : realType) (x : R[i]) : ``|x^-1| = ``|x|^-1.
Proof. by apply/(@r2c_inj _ R[i]); rewrite /r2c/= realcI !normrcE normfV. Qed.

#[global] Hint Extern 0 (is_true (0 <= normrc _)) => apply: normrc_ge0 : core.

(* generally, we only consider Lp norm for 1 <= p < oo *)
(* we define the case for p < 1 by default that make it as a norm *)
(* e.g., if p < 1, we set | x |_p = | x |_oo or equivalently, the max norm *)

HB.lock
Definition lpnormrc (R : realType) (C : extNumType R) (p : R) 
  (m n : nat) (A : 'M[C]_(m,n)) : R :=
  (if p < 1 then (\big[Order.max/0]_i ``|A i.1 i.2|)
  else ((\sum_i ``|A i.1 i.2| `^ p) `^ p^-1)).

(* entry wise p norm for RClike (extNumType) *)
Section PNormRC.
Variable (R: realType) (C : extNumType R) (p : R) (m n : nat).
Implicit Type (A B : 'M[C]_(m,n)).
Local Notation lpnormrc := (lpnormrc p).

(* Lemma lpnormrc_pair A : lpnormrc A = r2c ((\sum_i\sum_j ``|A i j| `^ p) `^ p^-1).
Proof. by rewrite lpnormrc.unlock; do 2 f_equal; rewrite pair_bigA. Qed. *)

Lemma lpnormrc0_eq0 : forall A, lpnormrc A = 0 -> A = 0.
Proof.
move=>A; rewrite lpnormrc.unlock; case: lerP=> _.
  move=>/powR_eq0_eq0.
  have P1 i: true -> 0 <= ``|A i.1 i.2| `^ p by [].
  move/(psumr_eq0P P1)=>/= P2;  apply/matrixP=>i j.
  by move: (P2 (i,j) isT)=>/powR_eq0_eq0/=/normrc0_eq0; rewrite mxE.
move=>/eqP; rewrite eq_le=>/andP[]/bigmax_leP/=[] _ Pi _.
by apply/matrixP=>i j; move: (Pi (i,j) isT); rewrite normrc_le0/= mxE=>/eqP.
Qed.

Lemma lpnormrc_ge0 : forall A, lpnormrc A >= 0.
Proof.
move=>A; rewrite lpnormrc.unlock; case: lerP=> _ //.
by apply/bigmax_geP; left.
Qed.

Lemma lpnormrc_nneg A : lpnormrc A \is Num.nneg.
Proof. by rewrite qualifE /Rnneg_pred lpnormrc_ge0. Qed.

Lemma lpnormrcZ a A : lpnormrc (a *: A) = ``|a| * lpnormrc A.
Proof.
rewrite lpnormrc.unlock; case: lerP=>[Hp| _].
  have ->: ``|a| = ``|a| `^ p `^ p^-1.
    by rewrite -powRrM mulfV ?gt_eqF ?powRr1// (lt_le_trans ltr01 Hp).
  rewrite -powRM// ?sumr_ge0// mulr_sumr; f_equal.
  by apply eq_bigr=>i _; rewrite mxE normrcM powRM.
apply/le_anti/andP; split.
  apply/bigmax_leP=>/=; split=>[|i _].
  by apply/mulr_ge0=>//; apply/bigmax_geP; left.
  by rewrite mxE normrcM ler_wpM2l//; apply/bigmax_geP; right; exists i.
move: (normrc_ge0 a); rewrite le0r=>/orP[/eqP->|Pa].
  by rewrite mul0r; apply/bigmax_geP; left.
rewrite -ler_pdivlMl//; apply/bigmax_leP=>/=; split=>[|i _].
  apply/mulr_ge0. by rewrite invr_ge0; apply/ltW.
  by apply/bigmax_geP; left.
rewrite ler_pdivlMl//; apply/bigmax_geP; right.
by exists i=>//; rewrite mxE normrcM.
Qed.

Lemma lpnormrc0 : lpnormrc (0 : 'M[C]_(m,n)) = 0.
Proof. by rewrite -(scale0r 0) lpnormrcZ// normrc0 mul0r. Qed.

Lemma lpnormrc0P A : reflect (lpnormrc A = 0) (A == 0).
Proof. by apply: (iffP eqP)=> [->|/lpnormrc0_eq0 //]; apply: lpnormrc0. Qed.

Definition lpnormrc_eq0 A := sameP (lpnormrc A =P 0) (lpnormrc0P A).

Lemma lpnormrc_triangle A B : lpnormrc (A + B) <= lpnormrc A + lpnormrc B.
Proof.
rewrite lpnormrc.unlock; case: ltP=>[_ |Hp].
  apply/bigmax_leP=>/=; split.
    by rewrite addr_ge0//; apply/bigmax_geP; left.
  move=>i _; rewrite mxE; apply/(le_trans (ler_normrcD _ _))/lerD;
  by apply/bigmax_geP; right; exists i.
apply: (le_trans (y := (\sum_i (``| A i.1 i.2 | + ``| B i.1 i.2 |) `^ p) `^ p^-1));
  last by apply: minkowski_fin.
rewrite ge0_ler_powR// ?nnegrE ?sumr_ge0// ?invr_ge0 ?(le_trans ler01)//.
apply/ler_sum=>/= i _; rewrite ge0_ler_powR// ?nnegrE// ?addr_ge0//.
  by apply: (le_trans ler01).
  by rewrite mxE ler_normrcD.
Qed.

(* HB.instance Definition _ := isVNorm.Build C 'M_(m, n) (@lpnormrc m n)
  lpnormrc_triangle lpnormrc0_eq0 lpnormrcZ. *)

Program Definition r2c_lpnormrc_vnorm :=
  (VNorm.Pack (VNorm.Class (isVNorm.Build C _ (@r2c R C \o @lpnormrc m n) _ _ _))).
Next Obligation.
by move=>x y; rewrite -rmorphD ler_r2c lpnormrc_triangle.
Qed.
Next Obligation.
by move=>x /(f_equal c2r); rewrite r2cK c2r0=>/lpnormrc0_eq0.
Qed.
Next Obligation.
by move=>a x; rewrite lpnormrcZ rmorphM normrcE.
Qed.

End PNormRC.

#[global] Hint Extern 0 (is_true (0 <= lpnormrc _ _)) => apply: lpnormrc_ge0 : core.

Section powR_root.
Variable (R : realType).

Lemma powC_root (p : nat) (x : R[i]) : 
  (0 < p)%N -> 0 <= x -> (``|x| `^ (p%:R^-1))%:C = p.-root x.
Proof.
move=>p0 x0; apply/eqP; rewrite -(eqrXn2 p0) ?rootC_ge0// ?lec0R//.
rewrite rootCK// -realcX -powR_mulrn//.
rewrite -powRrM mulVf// ?powRr1// ?normrcE// ?ger0_norm//.
by rewrite pnatr_eq0 lt0n_neq0.
Qed.

Lemma powC_rootV (p : nat) (x : R) : 
  (0 < p)%N -> 0 <= x -> (x `^ (p%:R^-1))%:C = p.-root x%:C.
Proof.
move=>Pp Px; rewrite -powC_root// ?lec0R//.
by rewrite normrc.unlock ger0_norm ?lec0R.
Qed.

Lemma powR12_sqrtC (x : R[i]) : 
  0 <= x -> (``|x| `^ (2^-1))%:C = sqrtC x.
Proof. by move=>Px; rewrite powC_root. Qed.

Lemma powR12_sqrtCV (x : R) : 
  0 <= x -> (x `^ (2^-1))%:C = sqrtC x%:C.
Proof. by move=>Px; rewrite powC_rootV. Qed.

Lemma powRrK (a r : R) : 0 <= a -> r != 0 -> (a `^ r) `^ r^-1 = a.
Proof. by move=>Pa Pr; rewrite -powRrM mulfV// powRr1. Qed. 

End powR_root.

Section lpnormrc_basic.
Variable (R : realType) (C : extNumType R).
Implicit Type (p q : R).

Lemma lpnormrc_continuous p m n : continuous (@lpnormrc R C p m n).
Proof.
have -> : @lpnormrc R C p m n = c2r \o r2c_lpnormrc_vnorm C p m n.
by apply/funext=>x /=; rewrite r2cK.
apply/continuous_comp_simp; last by apply c2r_continuous.
apply/continuous_mnorm.
Qed.

Lemma continuous_lpnormrc p (m n : nat) (A : 'M[C]_(m,n)) : 
  1 < p -> {for p, continuous (fun p0 : R => lpnormrc p0 A)}.
Proof.
have [/eqP -> _| PA Hp] := boolP (A == 0).
  have: {for p, continuous (cst 0 : R -> R)}.
    rewrite /prop_for /continuous_at; apply: cvg_cst.
  by apply: continuous_near_eq; near=>q; rewrite fctE lpnormrc0.
have P0 q : \sum_i ``| A i.1 i.2 | `^ q > 0.
  rewrite lt_def; apply/andP; split; last by apply sumr_ge0.
  apply/eqP=>P. move: PA=>/negP; apply; apply/eqP/matrixP=>i j.
  have P1 i0 : true -> 0 <= ``| A i0.1 i0.2 | `^ q by [].
  move: P=>/(psumr_eq0P P1)/(_ (i,j) isT)/=/eqP;
  by rewrite powR_eq0 mxE=>/andP[]/eqP/normrc0_eq0->.
rewrite lpnormrc.unlock.
suff: {for p, continuous (expR \o ((fun p : R => p^-1) * 
                  (@ln R \o (\sum_i powR ``|A i.1 i.2|))))}.
  apply: continuous_near_eq.
  exists `|p - 1|=>[/= |q /= Pq]; first by rewrite normr_gt0 subr_eq0 gt_eqF.
  have q_gt1: 1 < q.
    by move: Pq; rewrite ltr_norml gtr0_norm ?subr_gt0// ltrD2l ltrN2=>/andP[].
  rewrite ltNge; move: q_gt1=>/ltW->/=.
  rewrite !fctE fct_sumE {2}/powR; case: eqP=>// P.
  by move: (P0 q); rewrite P ltxx.
apply: continuous_comp; last by apply: continuous_expR.
apply: continuousM.
  by apply: continuousV=>//; rewrite gt_eqF// (lt_trans ltr01 Hp).
apply: continuous_comp.
  apply: continuous_sum=>/= i _; apply/continuous_powR/(lt_trans ltr01 Hp).
by apply: continuous_ln; rewrite fct_sumE.
Unshelve. end_near.
Qed.

Lemma lpnormrc_nincr p1 p2 (m n : nat) (A : 'M[C]_(m,n)) :
  1 <= p1 <= p2 -> lpnormrc p1 A >= lpnormrc p2 A.
Proof.
have [/eqP -> _| PA Hp] := boolP (A == 0).
  by rewrite !lpnormrc0.
have P0 q : \sum_i ``| A i.1 i.2 | `^ q > 0.
  rewrite lt_def; apply/andP; split; last by apply sumr_ge0.
  apply/eqP=>P. move: PA=>/negP; apply; apply/eqP/matrixP=>i j.
  have P1 i0 : true -> 0 <= ``| A i0.1 i0.2 | `^ q by [].
  move: P=>/(psumr_eq0P P1)/(_ (i,j) isT)/=/eqP;
  by rewrite powR_eq0 mxE=>/andP[]/eqP/normrc0_eq0->.
move: Hp =>/andP[] P1 P12; move: (le_trans P1 P12)=>P2.
rewrite lpnormrc.unlock !ltNge P1 P2 /= -ler_ln ?posrE; last first.
  1,2: by apply/powR_gt0.
rewrite [X in X <= _]ln_powR [X in _ <= X]ln_powR.
have ix x : x \in `]p1, p2[ -> 0 < x.
  by move=>/itvP/= [[[[[]]]]] /(le_trans P1)/(lt_le_trans ltr01).
have P3 (p : R) : 0 < p -> is_derive p 1 (fun p : R => p^-1 * ln (\sum_i ``| A i.1 i.2 | `^ p)) 
  ( - p^-2 * ln (\sum_i ``| A i.1 i.2 | `^ p) + 
    p^-1 / (\sum_i ``| A i.1 i.2 | `^ p) * 
    (\sum_i ln ``| A i.1 i.2 | * ``| A i.1 i.2 | `^ p)  ).
  move=>Pp; apply: (is_derive_eq (is_deriveM (df := - p ^- 2) 
    (dg := (\sum_i ``| A i.1 i.2 | `^ p)^-1 * 
      (\sum_i ln ``| A i.1 i.2 | * ``| A i.1 i.2 | `^ p)) _ _)).
  apply: (is_derive_eq (is_deriveV _ _)).
    by rewrite gt_eqF// ix.
    by rewrite /GRing.scale/= mulr1.
  apply: is_derive1_comp.
    by apply: is_derive1_ln.
  have ->: (fun x : R => \sum_i ``| A i.1 i.2 | `^ x) = \sum_i (fun x : R => ``| A i.1 i.2 | `^ x).
    by apply/funext=>?; rewrite fct_sumE.
  by apply: is_derive_sum=>/= i _; apply/is_derive1_powRx.
  by rewrite addrC /GRing.scale/=; f_equal; rewrite ?mulrA// mulrC.
apply: (ler0_derive1_nincr (f := fun p => p^-1 * 
  ln (\sum_i ``| A i.1 i.2 | `^ p)) (a := p1) (b := p2))=>//.
- by move=>x /ix /P3 [].
- move=>x /ix Px; move: (P3 x Px)=>[ _ ].
  rewrite derive1E=>->.
  rewrite addrC mulNr subr_le0 ler_pdivlMl ?exprn_gt0// ?ix// !mulrA 
    expr2 mulfK ?(gt_eqF Px)// mulrAC ler_pdivrMr// [X in _ <= X]mulrC.
  rewrite mulr_sumr. under eq_bigr do rewrite mulrA -ln_powR mulrC.
  by apply: xlnx_sum=>/= i _.
- apply: continuous_in_subspaceT=>x.
  rewrite inE/= in_itv/==>/andP[]/(le_trans P1)/(lt_le_trans ltr01)/P3[] + _ _.
  by rewrite derivable1_diffP=>/differentiable_continuous.
Qed.

Lemma lpnormrc_is_cvg (m n : nat) (A : 'M[C]_(m,n)) :
  cvgn (fun k : nat => lpnormrc k.+1%:R A).
Proof.
apply: (etnonincreasing_is_cvgn (M := 0))=>//.
by move=>k1 k2 Pk; apply: lpnormrc_nincr; rewrite ler1Sn/= ler_nat ltnS.
Qed.

Lemma lpnormrc_limn_ge (m n : nat) (A : 'M[C]_(m,n)) :
  lpnormrc 0 A <= limn (fun k : nat => lpnormrc k.+1%:R A).
Proof.
apply: etlimn_ge. apply: lpnormrc_is_cvg.
move=>k; rewrite lpnormrc.unlock ltr01 ltrn1/=.
apply/bigmax_leP=>/=; split=>// i _.
apply: (le_trans (y := ``|A i.1 i.2| `^ k.+1%:R `^ k.+1%:R^-1)).
  by rewrite -powRrM mulfV ?powRr1.
rewrite ge0_ler_powR// ?nnegrE// ?sumr_ge0//.
by rewrite (bigD1 i)//= lerDl sumr_ge0// =>? _; apply: powR_ge0.
Qed.

Lemma lpnormrc_limn_le (m n : nat) (A : 'M[C]_(m,n)) :
  limn (fun k : nat => lpnormrc k.+1%:R A) <= lpnormrc 0 A.
Proof.
have [/eqP -> | PA] := boolP (A == 0).
  under eq_lim do rewrite lpnormrc0.
  by rewrite lim_cst// lpnormrc0.
have P1 : 0 < \big[Order.max/0]_i ``|A i.1 i.2|.
  rewrite lt_def; apply/andP; split.
  move: PA; apply contraNN=>/eqP P; apply/eqP/matrixP=>i j.
  move: P; rewrite (bigD1 (i,j))//= mxE =>P1.
  by apply/eqP; rewrite -normrc_le0 -P1 le_max lexx.
  by apply/bigmax_geP; left.
have P2 : 0 < ((m * n)%:R : R). rewrite ltr0n lt0n muln_eq0.
  by move: PA; apply: contraNN=>P; rewrite mx_dim0_cond.
have P3: cvgn (fun x : nat => (m * n)%:R `^ x.+1%:R^-1 * \big[maxr/0]_i ``| A i.1 i.2 |).
  apply: is_cvgM; last by apply: is_cvg_cst.
  by apply/cvg_ex; exists 1; move: (powR1n_limn P2); rewrite -cvg_shiftS/=.
apply: (le_trans (y := limn (fun k : nat => 
  ( (m * n)%:R `^ k.+1%:R ^-1 *  (\big[Order.max/0]_i ``|A i.1 i.2|))))).
apply: ler_etlimn=>[|//|]. apply: lpnormrc_is_cvg.
move=>k; rewrite lpnormrc.unlock ltrn1/=.
apply: (le_trans (y := (\sum_(i : 'I_m * 'I_n) 
  (\big[maxr/0]_i ``| A i.1 i.2 |) `^ k.+1%:R) `^ k.+1%:R^-1)).
rewrite ge0_ler_powR//= ?nnegrE ?sumr_ge0//.
  apply ler_sum=>i _; rewrite ge0_ler_powR//= ?nnegrE//; 
  apply/bigmax_geP; by [left | right; exists i].
by rewrite sumr_const -mulr_natl card_prod !card_ord 
  powRM// -powRrM mulfV//= powRr1// ltW.
rewrite lpnormrc.unlock ltr01 limM.
by rewrite lim_cst//; move: (powR1n_limn P2); 
  rewrite -cvg_shiftS/==>/cvg_lim->//; rewrite mul1r.
by apply/cvg_ex; exists 1; move: (powR1n_limn P2); rewrite -cvg_shiftS/=.
apply: is_cvg_cst.
Qed.

Lemma lpnormrc_cvg (m n : nat) (A : 'M[C]_(m,n)) :
  (fun k => lpnormrc k.+1%:R A) @ \oo --> lpnormrc 0 A.
Proof.
rewrite cvgn_limnE//; split; last by apply: lpnormrc_is_cvg.
apply/le_anti/andP; split.
apply/lpnormrc_limn_le. apply/lpnormrc_limn_ge.
Qed.

Lemma lpnormrc_gep0 p (m n : nat) (A : 'M[C]_(m,n)) :
  lpnormrc 0 A <= lpnormrc p A.
Proof.
case E: (p < 1); first by rewrite lpnormrc.unlock ltr01 E.
apply: (le_trans (y := lpnormrc (Num.ExtraDef.archi_bound (p-1)).+1%:R A)).
move: (lpnormrc_cvg (A := A))=>/cvg_lim <-//.
apply: etnonincreasing_cvgn_ge.
by move=>k1 k2 Pk; apply: lpnormrc_nincr; rewrite ler1Sn/= ler_nat ltnS.
apply: lpnormrc_is_cvg.
move: E; rewrite ltNge=>/negbFE E.
apply/lpnormrc_nincr; rewrite E/=.
by move: E; rewrite -subr_ge0=>/archi_boundP/ltW; rewrite lerBlDr -addn1 natrD.
Qed.

Lemma lpnormrc_ndecr p1 p2 (m n : nat) (A : 'M[C]_(m,n)) : 
  1 <= p1 <= p2 -> lpnormrc p1 A / ((m * n)%:R `^ p1^-1) <= 
                     lpnormrc p2 A / ((m * n)%:R `^ p2^-1).
Proof.
have [/eqP -> _| PA Hp] := boolP (A == 0).
  by rewrite !lpnormrc0 !mul0r.
have P0 q : \sum_i ``| A i.1 i.2 | `^ q > 0.
  rewrite lt_def; apply/andP; split; last by apply sumr_ge0.
  apply/eqP=>P. move: PA=>/negP; apply; apply/eqP/matrixP=>i j.
  have P1 i0 : true -> 0 <= ``| A i0.1 i0.2 | `^ q by [].
  move: P=>/(psumr_eq0P P1)/(_ (i,j) isT)/=/eqP;
  by rewrite powR_eq0 mxE=>/andP[]/eqP/normrc0_eq0->.
have P00 : 0 < ((m * n)%:R : R). rewrite ltr0n lt0n muln_eq0.
  by move: PA; apply: contraNN=>P; rewrite mx_dim0_cond.
move: Hp =>/andP[] P1 P12; move: (le_trans P1 P12)=>P2.
rewrite lpnormrc.unlock !ltNge P1 P2 /= -ler_ln ?posrE; last first.
  1,2: by rewrite divr_gt0// ?powR_gt0.
rewrite !powRN_inv// -[in leLHS]powRM -?[in leRHS]powRM=>[||//||//].
  2,3: by apply/ltW.
rewrite [leLHS]ln_powR [leRHS]ln_powR.
have ix x : x \in `]p1, p2[ -> 0 < x.
  by move=>/itvP/= [[[[[]]]]] /(le_trans P1)/(lt_le_trans ltr01).
have P3 (p : R) : 0 < p -> is_derive p 1 
  (fun p : R => p^-1 * ln ((\sum_i ``| A i.1 i.2 | `^ p) / (m * n)%:R))
  ( - p^-2 * ln ((\sum_i ``| A i.1 i.2 | `^ p) / (m * n)%:R) + 
    p^-1 / (\sum_i ``| A i.1 i.2 | `^ p) * 
    (\sum_i ln ``| A i.1 i.2 | * ``| A i.1 i.2 | `^ p)  ).
  move=>Pp; apply: (is_derive_eq (is_deriveM (df := - p ^- 2) 
    (dg := (\sum_i ``| A i.1 i.2 | `^ p)^-1 * 
      (\sum_i ln ``| A i.1 i.2 | * ``| A i.1 i.2 | `^ p)) _ _)).
  apply: (is_derive_eq (is_deriveV _ _)).
    by rewrite gt_eqF// ix.
    by rewrite /GRing.scale/= mulr1.
  have P01 : 0 < (m * n)%:R^-1 :> R by rewrite invr_gt0.
  under eq_fun do rewrite (lnM (P0 _) P01).
  rewrite -[X in is_derive _ _ _ X]addr0.
  apply: is_deriveD. apply: is_derive1_comp.
    by apply: is_derive1_ln.
  have ->: (fun x : R => \sum_i ``| A i.1 i.2 | `^ x) = \sum_i (fun x : R => ``| A i.1 i.2 | `^ x).
    by apply/funext=>?; rewrite fct_sumE.
  by apply: is_derive_sum=>/= i _; apply/is_derive1_powRx.
  by rewrite addrC /GRing.scale/=; f_equal; rewrite ?mulrA// mulrC.
apply: (le0r_derive1_ndecr (f := fun p => p^-1 * 
  ln ((\sum_i ``| A i.1 i.2 | `^ p) / (m * n)%:R)) (a := p1) (b := p2))=>//.
- by move=>x/ix/P3 [].
- move=>x /ix Px; move: (P3 _ Px)=>[ _ ].
  rewrite derive1E=>->.
  rewrite addrC mulNr subr_ge0 ler_pdivrMl ?exprn_gt0// !mulrA 
    expr2 mulfK ?(gt_eqF Px)// mulrAC ler_pdivlMr// mulrC.
  rewrite mulr_sumr. under [leRHS]eq_bigr do rewrite mulrA -ln_powR mulrC.
  move: (xlnx_average_sum (index_enum _) (P := xpredT) (x := fun i => ``| A i.1 i.2 | `^ x)).
  by rewrite /= sumr_const card_prod !card_ord; apply.
- apply: continuous_in_subspaceT=>/= x.
  rewrite inE/= in_itv/==>/andP[]/(le_trans P1)/(lt_le_trans ltr01)/P3[] + _ _.
  by rewrite derivable1_diffP=>/differentiable_continuous.
Qed.

Lemma lpnormrc_plt1E p :
  p < 1 -> @lpnormrc R C p = lpnormrc 0.
Proof. by rewrite lpnormrc.unlock ltr01=>->. Qed.

Lemma lpnormrc_lep0 p (m n : nat) (A : 'M[C]_(m,n)) :
  0 <= p -> lpnormrc p A / ((m * n)%:R `^ p^-1) <= lpnormrc 0 A.
Proof.
have [Pmn|] := boolP (0 < (m * n)%:R :> R); last first.
  rewrite ltr0n -eqn0Ngt muln_eq0 => /mx_dim0_cond ->.
  by rewrite !lpnormrc0 mul0r.
have [/eqP -> _| ] := boolP (p == 0).
  by rewrite invr0 powRr0 divr1.
rewrite le_eqVlt eq_sym =>/negPf->/= Pp.
have [plt1 | ] := boolP (p < 1).
  rewrite lpnormrc_plt1E// ler_piMr// invf_le1 ?powR_gt0//.
  apply: (le_trans _ (le1r_powR _ _)).
  1,2: by move: Pmn; rewrite ler1n ltr0n.
  by rewrite invf_ge1// ltW.
rewrite -leNgt => Pp1.
rewrite lpnormrc.unlock ltr01 ltNge Pp1/= powRN_inv// -powRM// ?sumr_ge0//.
rewrite -[leRHS]powRr1; last by apply/bigmax_geP; left.
rewrite -{2}(mulfV (lt0r_neq0 Pp)) powRrM ge0_ler_powR// ?nnegrE//.
  by rewrite invr_ge0 ltW.
  by rewrite divr_ge0// sumr_ge0.
rewrite ler_pdivrMr//.
apply: (le_trans (y := \sum_i (\big[maxr/0]_i ``| A i.1 i.2 |) `^ p)).
  apply ler_sum=>/= i _; rewrite ge0_ler_powR// ?nnegrE//.
    by rewrite ltW.
    by apply/bigmax_geP; left.
  by apply/bigmax_geP; right; exists i.
by rewrite sumr_const -mulr_natr card_prod !card_ord.
Qed.

Lemma lpnormrc_p0ge p (m n : nat) (A : 'M[C]_(m,n)) :
  0 <= p -> lpnormrc p A <= ((m * n)%:R `^ p^-1) * lpnormrc 0 A.
Proof.
have [Pmn Pp|] := boolP (0 < (m * n)%:R :> R); last first.
  rewrite ltr0n -eqn0Ngt muln_eq0 => /mx_dim0_cond ->;
  by rewrite !lpnormrc0 mulr0.
by rewrite -ler_pdivrMl ?powR_gt0// mulrC; apply: lpnormrc_lep0.
Qed.

Lemma lpnormrc_trmx p (m n : nat) (A : 'M[C]_(m,n)) :
  lpnormrc p (A^T) = lpnormrc p A.
Proof.
rewrite lpnormrc.unlock; case: (p < 1).
  apply/le_anti/andP; split; apply/bigmax_leP; split=>[|/= i _];
  by apply/bigmax_geP; (try by left); right; exists (i.2,i.1); rewrite//= mxE.
rewrite pair_bigV/= exchange_big/= pair_big.
by under eq_bigr do rewrite mxE.
Qed.

Lemma lpnormrc_diag p n (D : 'rV[C]_n) : 
  lpnormrc p (diag_mx D) = lpnormrc p D.
Proof.
rewrite lpnormrc.unlock; case E: (_ < _).
  apply/le_anti/andP; split; apply/bigmax_leP; split.
  1,3: by apply/bigmax_geP; left.
  - move=>/= [i j] _; rewrite mxE/=; case: eqP=> _.
    + by rewrite mulr1n; apply/bigmax_geP; right; exists (0,i).
    + by rewrite mulr0n normrc0; apply/bigmax_geP; left.
  - move=>/= [i j] _; rewrite /= ord1; apply/bigmax_geP; right; 
    by exists (j,j); rewrite //= mxE eqxx mulr1n.
f_equal. rewrite !pair_bigV/= big_ord1; apply eq_bigr=>i _.
rewrite (bigD1 i)//= big1 ?mxE ?eqxx ?mulr1n ?addr0// =>j /negPf nji.
rewrite mxE eq_sym nji mulr0n normrc0 powR0//; 
by move: E; case: eqP=>// ->; rewrite ltr01.
Qed.

Lemma lpnormrc_col_perm p m n (s : 'S_n) (A : 'M[C]_(m,n)) :
  lpnormrc p (col_perm s A) = lpnormrc p A.
Proof.
rewrite lpnormrc.unlock; case: ltP=>[ _ |Pp].
  apply/le_anti/andP; split.
    apply/bigmax_leP; split=>[|[i j] _ /=]; first by apply/bigmax_geP; left.
    by apply/bigmax_geP; right; exists (i, (s j))=>//; rewrite mxE/=.
  apply/bigmax_leP; split=>[|[i j] _ /=]; first by apply/bigmax_geP; left.
  by apply/bigmax_geP; right; exists (i, ((s^-1)%g j))=>//; rewrite mxE/= permKV.
f_equal; rewrite !pair_bigV/=; apply eq_bigr => i _.
by rewrite [RHS](reindex_perm s)/=; under eq_bigr do rewrite mxE.
Qed.

Lemma lpnormrc_row_perm p m n (s : 'S_m) (A : 'M[C]_(m,n)) :
  lpnormrc p (row_perm s A) = lpnormrc p A.
Proof. by rewrite -lpnormrc_trmx tr_row_perm lpnormrc_col_perm lpnormrc_trmx. Qed.

Lemma lpnormrc_permMl p m n (s : 'S_m) (A : 'M[C]_(m,n)) :
  lpnormrc p (perm_mx s *m A) = lpnormrc p A.
Proof. by rewrite -row_permE lpnormrc_row_perm. Qed.

Lemma lpnormrc_permMr p m n (s : 'S_n) (A : 'M[C]_(m,n)) :
  lpnormrc p (A *m perm_mx s) = lpnormrc p A.
Proof. by rewrite col_permEV lpnormrc_col_perm. Qed.

Lemma lpnormrcM p m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  1 <= p <= 2 -> lpnormrc p (A *m B) <= lpnormrc p A * lpnormrc p B.
Proof.
move=>/andP[] Pp1 Pp2; move: (le_trans ler01 Pp1)=>Pp0.
rewrite lpnormrc.unlock ltNge Pp1/= -powRM ?ge0_ler_powR// 
  ?nnegrE ?mulr_ge0// ?sumr_ge0// ?invr_ge0//.
under eq_bigr do rewrite mxE.
have [/eqP ->| Pp1'] := boolP (p == 1).
  rewrite !pair_bigV/= mulr_suml ler_sum// =>i _.
  rewrite exchange_big/= mulr_sumr ler_sum// =>j _.
  rewrite powRr1//; apply/(le_trans (ler_normrc_sum _ _ _)).
  rewrite mulr_suml ler_sum// =>k _.
  by rewrite normrcM powRr1// ler_wpM2l// (bigD1 k)//= powRr1// lerDl sumr_ge0.
have Pp1'': 1 < p by rewrite lt_def Pp1' Pp1.
pose q := conjugate_index Pp1''.
apply: (le_trans (y := \sum_i 
  ((\sum_k ``|A i.1 k| `^ p) `^ p^-1 * (\sum_k ``|B k i.2| `^ q) `^ (q:R)^-1) `^ p )).
apply/ler_sum=> i _; rewrite ?ge0_ler_powR// ?nnegrE// ?mulr_ge0//.
apply/(le_trans (ler_normrc_sum _ _ _)).
under eq_bigr do rewrite normrcM.
apply: hoelder_seq=>//=.
rewrite !pair_bigV/= mulr_suml ler_sum// =>i _.
rewrite exchange_big/= mulr_sumr ler_sum// =>j _.
rewrite powRM// ler_pM//.
rewrite -powRrM mulVf// ?(ci_p_neq0 q)// powRr1// sumr_ge0//.
move: (lpnormrc_nincr (p1 := p) (p2 := q) (col j B)).
rewrite Pp1 -ci_ple2_pleq Pp2 lpnormrc.unlock !ltNge (ci_p_ge1 q) (ci_q_ge1 q)/=
  !pair_bigV/= exchange_big big_ord1 exchange_big big_ord1/==>/(_ isT).
under eq_bigr do rewrite mxE.
move=>/(ge0_ler_powR Pp0) P.
apply: (le_trans (P _ _)); try by rewrite nnegrE//.
rewrite -powRrM mulVf ?(ci_p_neq0 q)// powRr1 ?sumr_ge0//.
by under eq_bigr do rewrite mxE.
Qed.

Lemma lpnormrcMl (p : R) (q : cindexType p) m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  2 <= p -> lpnormrc p (A *m B) <= lpnormrc p A * lpnormrc q B.
Proof.
move=>Pp2; move: (ci_p_ge0 q) (ci_q_ge0 q)=>Pp0 Pq0.
rewrite lpnormrc.unlock !ltNge (ci_p_ge1 q) (ci_q_ge1)/=.
apply: (le_trans (y := (\sum_i 
  ((\sum_k ``|A i.1 k| `^ p) `^ p^-1 * (\sum_k ``|B k i.2| `^ q) `^ (q:R)^-1) `^ p )`^ p^-1 )).
  rewrite ge0_ler_powR// ?invr_ge0// ?nnegrE ?sumr_ge0//.
  apply/ler_sum=> i _; rewrite ?ge0_ler_powR// ?nnegrE// ?mxE ?mulr_ge0//.
  apply/(le_trans (ler_normrc_sum _ _ _)).
  under eq_bigr do rewrite normrcM.
  apply: hoelder_seq=>//=.
under eq_bigr do rewrite (powRM _ (powR_ge0 _ _) (powR_ge0 _ _)).
apply: (le_trans (y := (\sum_i
    ((\sum_k ``| A i.1 k | `^ p) * (\sum_k ``| B k i.2 | `^ q) `^ (p/(q:R))
    ))`^ p^-1)).
rewrite ge0_ler_powR// ?nnegrE ?invr_ge0// ?sumr_ge0// =>[??|??|]; 
rewrite ?mulr_ge0// ?sumr_ge0//.
by apply ler_sum=>/= i _;  rewrite -[in X in X * _]powRrM mulVf
  ?(ci_p_neq0 q)// powRr1 ?ler_wpM2l// ?sumr_ge0// -[leLHS]powRrM mulrC.
rewrite !pair_bigV/=.
under eq_bigr do rewrite -mulr_sumr.
rewrite -mulr_suml powRM ?ler_wpM2l// ?sumr_ge0// =>[|??]; last by apply/sumr_ge0.
rewrite -{2}[(q:R)^-1](mulfK (x := p)) ?(ci_p_neq0 q)// powRrM mulrC 
  ge0_ler_powR// ?nnegrE// ?invr_ge0// ?sumr_ge0// exchange_big/=.
apply powR_sum_ler=>[|i _]; last by apply sumr_ge0.
by rewrite ler_pdivlMl ?mulr1 -?(ci_pge2_qlep q) ?ci_q_gt0.
Qed.

Lemma lpnormrcMr (p : R) (q : cindexType p) m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  2 <= p -> lpnormrc p (A *m B) <= lpnormrc q A * lpnormrc p B.
Proof.
move=>Pp2; move: (ci_p_ge0 q) (ci_q_ge0 q)=>Pp0 Pq0.
rewrite lpnormrc.unlock !ltNge (ci_p_ge1 q) (ci_q_ge1)/=.
apply: (le_trans (y := (\sum_i 
  ((\sum_k ``|A i.1 k| `^ q) `^ (q:R)^-1 * (\sum_k ``|B k i.2| `^ p) `^ p^-1) `^ p )`^ p^-1 )).
  rewrite ge0_ler_powR// ?invr_ge0// ?nnegrE ?sumr_ge0//.
  apply/ler_sum=> i _; rewrite ?ge0_ler_powR// ?nnegrE// ?mxE ?mulr_ge0//.
  apply/(le_trans (ler_normrc_sum _ _ _)).
  under eq_bigr do rewrite normrcM.
  by apply: hoelder_seq=>//=; rewrite addrC.
under eq_bigr do rewrite (powRM _ (powR_ge0 _ _) (powR_ge0 _ _)).
apply: (le_trans (y := (\sum_i ((\sum_k ``| A i.1 k | `^ q) `^ (p/(q:R)) * 
  (\sum_k ``| B k i.2 | `^ p)))`^ p^-1)).
rewrite ge0_ler_powR// ?nnegrE ?invr_ge0// ?sumr_ge0// =>[??|??|]; 
rewrite ?mulr_ge0// ?sumr_ge0//.
by apply ler_sum=>/= i _;  rewrite -[in X in X * _]powRrM [_ * p]mulrC 
  ?ler_wpM2l// -powRrM mulVf ?(ci_p_neq0 q)// powRr1// sumr_ge0.
rewrite !pair_bigV/=.
under eq_bigr do rewrite -mulr_sumr exchange_big/=.
rewrite -mulr_suml powRM ?ler_wpM2r// ?sumr_ge0// =>[|??]; last by apply/sumr_ge0.
rewrite -{2}[(q:R)^-1](mulfK (x := p)) ?(ci_p_neq0 q)// powRrM mulrC 
  ge0_ler_powR// ?nnegrE// ?invr_ge0// ?sumr_ge0//.
apply powR_sum_ler=>[|i _]; last by apply sumr_ge0.
by rewrite ler_pdivlMl ?mulr1 -?(ci_pge2_qlep q) ?ci_q_gt0.
Qed.

Lemma l0normrc_elem m n (A : 'M[C]_(m,n)) i j :
  ``| A i j | <= lpnormrc 0 A.
Proof. by rewrite lpnormrc.unlock ltr01; apply/bigmax_geP; right; exists (i,j). Qed.

Lemma l0normrcMl m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  lpnormrc 0 (A *m B) <= lpnormrc 0 A * lpnormrc 1 B.
Proof.
rewrite {1 3}lpnormrc.unlock ltr01 ltxx.
apply/bigmax_leP; split=>[|/= [i j] _ /=]; first by rewrite mulr_ge0.
rewrite mxE invr1 powRr1 ?sumr_ge0// pair_bigV/= exchange_big/= (bigD1 j)//= 
  mulrDr -[leLHS]addr0 lerD//.
rewrite mulr_sumr; apply/(le_trans (ler_normrc_sum _ _ _))/ler_sum=>k _.
by rewrite powRr1// normrcM ler_wpM2r// l0normrc_elem.
by rewrite mulr_ge0// sumr_ge0// =>k _; rewrite sumr_ge0.
Qed.

Lemma l0normrcMr m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  lpnormrc 0 (A *m B) <= lpnormrc 1 A * lpnormrc 0 B.
Proof.
rewrite {1 2}lpnormrc.unlock ltr01 ltxx.
apply/bigmax_leP; split=>[|/= [i j] _ /=]; first by rewrite mulr_ge0.
rewrite mxE invr1 powRr1 ?sumr_ge0// pair_bigV/= (bigD1 i)//=
  mulrDl -[leLHS]addr0 lerD//.
rewrite mulr_suml; apply/(le_trans (ler_normrc_sum _ _ _))/ler_sum=>k _.
by rewrite powRr1// normrcM ler_wpM2l// l0normrc_elem.
by rewrite mulr_ge0// sumr_ge0// =>k _; rewrite sumr_ge0.
Qed.

Lemma lpnormrc_castmx p m n m' n' (eqmn : (m = m') * (n = n')) (A : 'M[C]_(m,n)) :
  lpnormrc p (castmx eqmn A) = lpnormrc p A.
Proof. by rewrite castmx_funE. Qed.

Lemma lpnormrc_row0mx p m n r (A : 'M[C]_(m,r)) : 
  lpnormrc p (row_mx (0 : 'M_(m,n)) A) = lpnormrc p A.
Proof.
rewrite lpnormrc.unlock; case E: (_ < _).
  apply/le_anti/andP; split; apply/bigmax_leP; split.
  1,3: by apply/bigmax_geP; left.
  - move=>/= [i j] _ /=; case: (split_ordP  j)=>k ->.
    by rewrite row_mxEl mxE normrc0; apply/bigmax_geP; left.
    by rewrite row_mxEr; apply/bigmax_geP; right; exists (i,k).
  - move=>/= [i j] _ /=; apply/bigmax_geP; right; 
    by exists (i,rshift _ j); rewrite //= row_mxEr.
f_equal; rewrite !pair_bigV/=; apply eq_bigr=>i _.
have P1: p != 0 by move: E; case: eqP=>// ->; rewrite ltr01.
rewrite big_split_ord/=.
under eq_bigr do rewrite row_mxEl mxE normrc0 (powR0 P1).
rewrite sumr_const mul0rn add0r.
by under eq_bigr do rewrite row_mxEr.
Qed.

Lemma lpnormrc_rowmx0 p m n r (A : 'M[C]_(m,n)) : 
  lpnormrc p (row_mx A (0 : 'M_(m,r))) = lpnormrc p A.
Proof.
rewrite lpnormrc.unlock; case E: (_ < _).
  apply/le_anti/andP; split; apply/bigmax_leP; split.
  1,3: by apply/bigmax_geP; left.
  - move=>/= [i j] _ /=; case: (split_ordP  j)=>k ->.
    by rewrite row_mxEl; apply/bigmax_geP; right; exists (i,k).
    by rewrite row_mxEr mxE normrc0; apply/bigmax_geP; left.
  - move=>/= [i j] _ /=; apply/bigmax_geP; right; 
    by exists (i,lshift _ j); rewrite //= row_mxEl.
f_equal; rewrite !pair_bigV/=; apply eq_bigr=>i _.
have P1: p != 0 by move: E; case: eqP=>// ->; rewrite ltr01.
rewrite big_split_ord/=.
under [X in _ + X]eq_bigr do rewrite row_mxEr mxE normrc0 (powR0 P1).
rewrite sumr_const mul0rn addr0.
by under eq_bigr do rewrite row_mxEl.
Qed.

Lemma lpnormrc_col0mx p m n r (A : 'M[C]_(n,r)) : 
  lpnormrc p (col_mx (0 : 'M_(m,r)) A) = lpnormrc p A.
Proof. by rewrite -lpnormrc_trmx tr_col_mx trmx0 lpnormrc_row0mx lpnormrc_trmx. Qed.

Lemma lpnormrc_colmx0 p m n r (A : 'M[C]_(m,r)) : 
  lpnormrc p (col_mx A (0 : 'M_(n,r))) = lpnormrc p A.
Proof. by rewrite -lpnormrc_trmx tr_col_mx trmx0 lpnormrc_rowmx0 lpnormrc_trmx. Qed.

Lemma lpnormrc_col_pge1 p m n (A : 'M[C]_(m,n)) :
  1 <= p -> lpnormrc p A = (\sum_i (lpnormrc p (col i A)) `^ p) `^ p^-1.
Proof.
move=>Pp1; move: (lt_le_trans ltr01 Pp1)=>Pp0.
rewrite lpnormrc.unlock ltNge Pp1/= pair_bigV/= exchange_big/=; f_equal.
apply eq_bigr => i _; rewrite -[RHS]powRrM mulVf ?gt_eqF// 
  powRr1 ?sumr_ge0// pair_bigV/= exchange_big/= big_ord1.
by apply eq_bigr => j _; rewrite mxE.
Qed.

Lemma lpnormrc_col_plt1 p m n (A : 'M[C]_(m,n)) :
  p < 1 -> lpnormrc p A = \big[maxr/0]_i (lpnormrc 0 (col i A)).
Proof.
move=>Pp; rewrite lpnormrc.unlock Pp ltr01.
apply/le_anti/andP; split.
apply/bigmax_leP=>/=; split=>[|[i j] _ /=].
  by apply/bigmax_geP; left.
  apply/bigmax_geP; right; exists j=>//.
  by apply/bigmax_geP; right; exists (i,0)=>//=; rewrite mxE.
apply/bigmax_leP=>/=; split=>[|i _ /=].
  by apply/bigmax_geP; left.
  apply/bigmax_leP=>/=; split=>[|[j k] _ /=].
    by apply/bigmax_geP; left.
  by rewrite ord1; apply/bigmax_geP; right; exists (j,i)=>//; rewrite mxE.
Qed.

Lemma lpnormrc_col_le p m n (A : 'M[C]_(m,n)) i :
  lpnormrc p (col i A) <= lpnormrc p A.
Proof.
case E: (p < 1).
  rewrite [leRHS]lpnormrc_col_plt1//; apply/bigmax_geP; right; 
  by exists i=>//; rewrite lpnormrc_plt1E.
have Pp : 0 <= p by apply/(le_trans ler01); rewrite leNgt E.
rewrite lpnormrc.unlock E ge0_ler_powR// ?nnegrE ?sumr_ge0// ?invr_ge0//.
rewrite !pair_bigV/= ler_sum// => j _.
by rewrite big_ord1 mxE (bigD1 i)//= lerDl sumr_ge0.
Qed.

Lemma lpnormrc_row_le p m n (A : 'M[C]_(m,n)) i :
  lpnormrc p (row i A) <= lpnormrc p A.
Proof.
rewrite -lpnormrc_trmx tr_row; 
by apply/(le_trans (lpnormrc_col_le _ _ _)); rewrite lpnormrc_trmx.
Qed.

Lemma lpnormrc_rowmxl_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  lpnormrc p A <= lpnormrc p (row_mx A B).
Proof.
case E : (p < 1).
  rewrite lpnormrc_col_plt1// lpnormrc_col_plt1//.
  apply/bigmax_leP; split=>[|/= i _]; first by apply/bigmax_geP; left.
  by apply/bigmax_geP; right; exists (lshift _ i)=>//; rewrite colKl.
have P1: 1 <= p by rewrite leNgt E. move: (le_trans ler01 P1)=>P0. 
rewrite lpnormrc_col_pge1// lpnormrc_col_pge1// ge0_ler_powR// ?invr_ge0// ?nnegrE ?sumr_ge0//.
rewrite big_split_ord/= -[leLHS]addr0 lerD// ?sumr_ge0//.
by under [leRHS]eq_bigr do rewrite colKl.
Qed.

Lemma lpnormrc_rowmxr_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  lpnormrc p B <= lpnormrc p (row_mx A B).
Proof.
case E : (p < 1).
  rewrite lpnormrc_col_plt1// lpnormrc_col_plt1//.
  apply/bigmax_leP; split=>[|/= i _]; first by apply/bigmax_geP; left.
  by apply/bigmax_geP; right; exists (rshift _ i)=>//; rewrite colKr.
have P1: 1 <= p by rewrite leNgt E. move: (le_trans ler01 P1)=>P0. 
rewrite lpnormrc_col_pge1// lpnormrc_col_pge1// ge0_ler_powR// ?invr_ge0// ?nnegrE ?sumr_ge0//.
rewrite big_split_ord/= -[leLHS]add0r lerD// ?sumr_ge0//.
by under [leRHS]eq_bigr do rewrite colKr.
Qed.

Lemma lpnormrc_colmxl_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  lpnormrc p A <= lpnormrc p (col_mx A B).
Proof. 
by rewrite -[leRHS]lpnormrc_trmx tr_col_mx 
  -[leLHS]lpnormrc_trmx lpnormrc_rowmxl_le.
Qed.

Lemma lpnormrc_colmxr_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  lpnormrc p B <= lpnormrc p (col_mx A B).
Proof.
by rewrite -[leRHS]lpnormrc_trmx tr_col_mx 
  -[leLHS]lpnormrc_trmx lpnormrc_rowmxr_le.
Qed.

Lemma lpnormrc_delta p m n (i : 'I_m) (j : 'I_n) : 
  lpnormrc p (delta_mx i j : 'M[C]_(m,n)) = 1.
Proof.
case E: (p < 1); rewrite lpnormrc.unlock E.
  apply/le_anti/andP; split.
    apply/bigmax_leP; split=>//= [k l]; rewrite mxE; 
    by case: eqP=> _; case: eqP=> _ /=; rewrite ?normrc0// ?normrc1.
  by apply/bigmax_geP; right; exists (i,j)=>//=; rewrite mxE !eqxx normrc1.
rewrite (bigD1 (i,j))//= big1=>[|[k l]].
  rewrite addr0 -powRrM mulfV ?mxE ?eqxx ?normrc1 ?powRr1//.
2: rewrite /eq_op/= mxE=>/negPf->; rewrite normrc0 powR0//.
all: by apply/eqP=>P; move: E; rewrite P ltr01.
Qed.

Lemma lpnormrc_const_plt1 p m n (a : C) :
  p < 1 -> lpnormrc p (const_mx a : 'M[C]_(m,n)) = ``|a| * ((m != 0) && (n != 0))%:R.
Proof.
rewrite lpnormrc.unlock=>->; apply/le_anti/andP; split.
  apply/bigmax_leP; split=>[|[i j] _]; first by apply/mulr_ge0.
  by rewrite mxE; case: i; case: j; 
    case: eqP=>[->//|]; case: eqP=>[->//|]; rewrite mulr1.
case: m=>/=[|m]; first by rewrite mulr0; apply/bigmax_geP; left.
case: n=>/=[|n]; first by rewrite mulr0; apply/bigmax_geP; left.
by apply/bigmax_geP; right=>/=; exists (0,0)=>//; rewrite mxE mulr1.
Qed.

Lemma lpnormrc_const_pge1 p m n (a : C) :
  1 <= p -> lpnormrc p (const_mx a : 'M[C]_(m,n)) = (m * n)%:R `^ p^-1 * ``|a|.
Proof.
move=>Pp; rewrite lpnormrc.unlock ltNge Pp/=.
under eq_bigr do rewrite mxE.
by rewrite sumr_const card_prod/= !card_ord -[in LHS]mulr_natl powRM// 
  -powRrM mulfV ?powRr1// gt_eqF// (lt_le_trans ltr01 Pp).
Qed.

Lemma lpnormrc_scale_plt1 p m (a : C) :
  p < 1 -> lpnormrc p (a%:M : 'M[C]_m) = ``|a| * (m != 0)%:R.
Proof.
move=>Pp; rewrite lpnormrc.unlock Pp/=; apply/le_anti/andP; split.
  apply/bigmax_leP; split=>[|[i j] _]; first by apply/mulr_ge0.
  case: m i j=>[[]//|m i j]; rewrite !mxE/= mulr1.
  by case: eqP; rewrite ?mulr1n// mulr0n normrc0.
case: m=>[|m]; first by rewrite eqxx mulr0; apply/bigmax_geP; left.
by rewrite /= mulr1; apply/bigmax_geP; right; 
  exists (0,0); rewrite // !mxE/= mulr1n.
Qed.

Lemma lpnormrc_scale_pge1 p m (a : C) :
  1 <= p -> lpnormrc p (a%:M : 'M[C]_m) = m%:R `^ p^-1 * ``|a|.
Proof.
move=>Pp; rewrite lpnormrc.unlock ltNge Pp/=.
rewrite pair_bigV/=; transitivity ((\sum_(i < m) ``| a | `^ p) `^ p^-1).
  f_equal; apply eq_bigr=>i _; rewrite (bigD1 i)//= big1 ?addr0=>[|j/negPf nj].
    by rewrite mxE eqxx mulr1n.
  by rewrite mxE eq_sym nj mulr0n normrc0 powR0// gt_eqF// (lt_le_trans ltr01).
by rewrite sumr_const !card_ord -[in LHS]mulr_natl powRM// 
  -powRrM mulfV ?powRr1// gt_eqF// (lt_le_trans ltr01 Pp).
Qed.

Lemma lpnormrc11 p (A : 'M[C]_(1,1)) :
  lpnormrc p A = ``|A 0 0|.
Proof.
rewrite lpnormrc.unlock; case: ltP=>Pp.
apply/le_anti/andP; split.
  by apply/bigmax_leP; split=>// i _; rewrite !ord1.
  by apply/bigmax_geP; right; exists (0,0).
by rewrite pair_bigV !big_ord1/= -powRrM mulfV 
  ?powRr1// gt_eqF// (lt_le_trans ltr01 Pp).
Qed.

Lemma l0normrc1 m : lpnormrc 0 (1%:M : 'M[C]_m) = (m != 0)%:R.
Proof.
case: m=>[|m/=]; first by rewrite mx_dim0 lpnormrc0.
rewrite lpnormrc.unlock ltr01; apply/le_anti/andP; split.
  apply/bigmax_leP; split=>// i _; 
  by rewrite mxE; case: eqP; rewrite ?normrc1// normrc0.
by apply/bigmax_geP; right; exists (0,0)=>//; rewrite mxE eqxx normrc1.
Qed.

Lemma lpnormrc1_pge1 p m : 
  1 <= p -> lpnormrc p (1%:M : 'M[C]_m) = (m%:R `^ p^-1).
Proof.
move=>Pp; rewrite lpnormrc.unlock ltNge Pp/=; f_equal.
transitivity (\sum_(i < m) (1 : R));
  last by rewrite sumr_const card_ord.
rewrite pair_bigV/=; apply eq_bigr=>i _; 
rewrite (bigD1 i)//= big1=>[|j /negPf Pj];
by rewrite mxE ?eqxx ?normrc1 ?powR1 ?addr0// eq_sym 
  Pj normrc0 powR0// gt_eqF// (lt_le_trans ltr01 Pp).
Qed.

Lemma lpnormrc_mul_deltar p m n l (A : 'M[C]_(m,n)) (i : 'I_n) (j : 'I_l) : 
  lpnormrc p (A *m delta_mx i j) = lpnormrc p (col i A).
Proof.
rewrite mulmx_colrow (bigD1 i)//= big1=>[|k /negPf Pk]; last first.
  by apply/matrixP=>s t; rewrite !mxE big1// =>? _; rewrite !mxE Pk mulr0.
rewrite addr0 lpnormrc.unlock; case: ltP=>Pp.
  apply/le_anti/andP; split; apply/bigmax_leP; 
  split => [|/= [a b] _]; try by apply/bigmax_geP; left.
    rewrite /= mxE big_ord1/= !mxE eqxx/=.
    apply/bigmax_geP; right; exists (a,0)=>//; rewrite mxE/=; 
    by case: eqP; rewrite ?mulr1// mulr0 normrc0.
  apply/bigmax_geP; right; exists (a,j)=>//.
  by rewrite /= !mxE big_ord1 !mxE !eqxx mulr1.
f_equal; rewrite !pair_bigV/=; apply eq_bigr=>k _.
rewrite big_ord1 (bigD1 j)//= big1=>[|a /negPf Pa].
  by rewrite addr0 !mxE big_ord1 !mxE !eqxx mulr1.
rewrite mxE big_ord1 !mxE Pa andbF mulr0 normrc0.
by rewrite powR0// gt_eqF// (lt_le_trans ltr01 Pp).
Qed.

Lemma lpnormrc_mul_deltal p m n l (A : 'M[C]_(m,n)) (i : 'I_l) (j : 'I_m) : 
  lpnormrc p (delta_mx i j *m A) = lpnormrc p (row j A).
Proof.
by rewrite -lpnormrc_trmx trmx_mul trmx_delta 
  lpnormrc_mul_deltar -tr_row lpnormrc_trmx.
Qed.

Lemma lpnormrc_hoelder p (q : ecindexType p) m (u : 'rV[C]_m) (v : 'cV[C]_m) :
  lpnormrc 1 (u *m v) <= lpnormrc p u * lpnormrc q v.
Proof.
case: (ecindexP q)=>[r->|->->|->->].
- rewrite lpnormrc.unlock ltxx !ltNge (ci_p_ge1 r) ci_q_ge1/=.
  rewrite !pair_bigV/= !big_ord1 exchange_big big_ord1/= mxE invr1 !powRr1//.
  apply/(le_trans (ler_normrc_sum _ _ _ )).
  under eq_bigr do rewrite normrcM.
  by apply hoelder_fin.
- rewrite lpnormrc.unlock ltxx ltr01 invr1 !powRr1 ?sumr_ge0// 
    !pair_bigV !big_ord1/= exchange_big big_ord1/= powRr1// mxE mulr_sumr.
  apply/(le_trans (ler_normrc_sum _ _ _))/ler_sum=> i _.
  by rewrite powRr1// normrcM ler_wpM2r//; apply/bigmax_geP; right; exists (0,i).
- rewrite lpnormrc.unlock ltxx ltr01 invr1 !powRr1 ?sumr_ge0// 
    !pair_bigV !big_ord1/= powRr1// mxE mulr_suml.
  apply/(le_trans (ler_normrc_sum _ _ _))/ler_sum=> i _.
  by rewrite powRr1// normrcM ler_wpM2l//; apply/bigmax_geP; right; exists (i,0).
Qed.

Lemma lpnormrc_cauchy m (u : 'rV[C]_m) (v : 'cV[C]_m) :
  ``| \tr (u *m v) | <= lpnormrc 2 u * lpnormrc 2 v.
Proof.
apply/(le_trans _ (lpnormrc_hoelder (2 : R) _ _))=>//.
rewrite lpnormrc.unlock ltxx invr1 powRr1 ?sumr_ge0//.
by rewrite trace_mx11 mxE pair_bigV/= !big_ord1 mxE powRr1.
Qed. 

Lemma lpnormrc_cvg1R (m n : nat) (A : 'M[C]_(m,n)) :
  (fun p => lpnormrc p A) @ 1^'+ --> lpnormrc 1 A.
Proof.
have [/eqP -> | PA ] := boolP (A == 0).
  under eq_fun do rewrite lpnormrc0.
  rewrite lpnormrc0; apply: cvg_cst.
have [ | Pmn0 ] := boolP (m * n == 1)%N.
  rewrite muln_eq1=>/andP[/eqP Pm /eqP Pn].
  move: A PA; rewrite Pm Pn=>A PA.
  under eq_fun do rewrite lpnormrc11.
  rewrite lpnormrc11; apply: cvg_cst.
have Pmn : 1 < (m * n)%:R :> R.
  rewrite ltr1n ltnNge leq_eqVlt negb_or Pmn0/=.
  case E : (m * n)%N=>//; move: E PA=>/eqP; 
  by rewrite muln_eq0=>/mx_dim0_cond->; rewrite eqxx.
have PA1 : 0 < lpnormrc 1 A by rewrite lt_def lpnormrc_eq0 PA/=. 
move: (lt_trans ltr01 Pmn) => Pmn3.
apply/cvgrPdist_lt=>/= e.
pose e0 := (1-(m*n)%:R^-1) * lpnormrc 1 A.
have Pe0 : 0 < e0 by rewrite mulr_gt0// ?subr_gt0 ?invf_lt1.
wlog : e / e < e0 =>[IH| Pe1 Pe ].
  case: (ltP e e0)=>[|P _]; first by apply: IH.
  have P1 : 0 <  e0 / 2 by rewrite divr_gt0.
  have P2 : e0 / 2 < e0 by rewrite -{2}[e0]split2r ltrDl.
  move: (IH _ P2 P1)=>[e1 /= P3 P4].
  by exists e1=>//= y P5 /(P4 _ P5)=>/lt_trans/(_ P2)/lt_le_trans/(_ P).
have : 0 < (1%R + ln (1 - e / lpnormrc 1 A) / ln (m * n)%:R).
  rewrite /= -ltrBlDl sub0r ltr_pdivlMr ?ln_gt0// -ln_powR powR_inv1//.
  rewrite ltr_ln ?posrE ?invr_gt0//.
  1,2: move: Pe1; rewrite /e0 -ltr_pdivrMr// ltrBrDl -ltrBrDr//; 
    by apply/lt_trans; rewrite invr_gt0.
exists (((1 + ln (1- e / lpnormrc 1 A) / ln (m*n)%:R))^-1 - 1).
  rewrite /= subr_gt0 invf_gt1//.
  rewrite -ltrBrDr ltrDl oppr_gt0 ltr_pdivrMr ?ln_gt0// mul0r ln_lt0//
    ltrBlDl ltrDr divr_gt0// andbT subr_gt0 ltr_pdivrMr//.
  by apply/(lt_trans Pe1); rewrite ltr_pM2r// ltrBlDl ltrDr invr_gt0.
move=>p /= P1 Pp.
have Pp1 : (1 : R) <= 1 <= p by rewrite lexx ltW.
rewrite ger0_norm ?subr_ge0 ?lpnormrc_nincr// ltrBlDl.
move: (lpnormrc_ndecr A Pp1).
rewrite ler_pdivlMr ?powR_gt0// -(lerD2r e).
apply: lt_le_trans; rewrite -ltrBlDl -{1}[lpnormrc 1 A]mulr1.
rewrite -mulrA -mulrBr -ltr_pdivlMl; 
  last by rewrite lt_def lpnormrc_eq0 PA/=.
rewrite [in ltRHS]mulrC ltrBlDl -ltrBlDr -powRN -powRD;
  last by apply/implyP=> _; rewrite gt_eqF//.
case: (leP (1 - e / lpnormrc 1 A) 0)=>P.
  by apply/(le_lt_trans P)/powR_gt0.
rewrite -ltr_ln ?posrE// ?powR_gt0// ln_powR -ltr_pdivrMr ?ln_gt0//.
rewrite invr1 -ltrBlDl opprK addrC -invf_ltp ?posrE// ?(lt_trans ltr01 Pp)//.
rewrite -(ltrD2r (-1)); apply/(le_lt_trans _ P1).
by rewrite -normrN opprB ger0_norm// subr_ge0 ltW.
Qed.

Lemma lpnormrc_cvg1 (m n : nat) (A : 'M[C]_(m,n)) :
  (fun p : nat => lpnormrc (1+p%:R^-1) A) @ \oo --> lpnormrc 1 A.
Proof.
apply/cvgrPdist_lt=>/= e Pe.
move: (lpnormrc_cvg1R (A := A))=>/cvgrPdist_lt/(_ e Pe)[t /= Pt Pb].
exists ((Num.ExtraDef.archi_bound (t^-1)).+1)=>// p /= Pp.
move: (leq_ltn_trans (leq0n _) Pp)=>Pp0.
apply/Pb=>//=; last by rewrite ltrDl invr_gt0 ltr0n.
rewrite opprD addNKr normrN ger0_norm ?invr_ge0// invf_plt ?posrE// ?ltr0n//.
move: Pp; rewrite -(ltr_nat R); apply/le_lt_trans/ltW/archi_boundP/ltW.
by rewrite invr_gt0.
Qed.

Lemma lpnormrc_tens x (m n p q : nat) (A : 'M[C]_(m,n)) (B : 'M_(p,q)) :
  lpnormrc x (A *t B) = lpnormrc x A * lpnormrc x B.
Proof.
case: m A=>[A|m]; last (case: n=>[A|n A]; 
  last (case: p B=>[B|p]; last case: q=>[B|q B])).
1-4: by rewrite !mx_dim0E ?tensmx0 !lpnormrc0 ?mulr0// mul0r.
have [Px | Px] := leP 1 x.
  rewrite lpnormrc.unlock ltNge Px/=.
  rewrite -powRM ?sumr_ge0//; f_equal.
  rewrite !pair_bigV/= mulr_suml reindex_mxtens_index/= pair_bigV/=.
  apply eq_bigr=>i _; rewrite mulr_sumr.
  apply eq_bigr=>j _; rewrite reindex_mxtens_index/= pair_bigV/= mulr_suml.
  apply eq_bigr=>k _; rewrite mulr_sumr.
  by apply eq_bigr=>l _; rewrite tensmxE normrcM powRM.
rewrite lpnormrc_plt1E// lpnormrc.unlock ltr01; f_equal.
apply/le_anti/andP; split.
  apply/bigmax_leP; split=>[|/= [i j]/= _].
    by rewrite mulr_ge0//; apply/bigmax_geP; left.
  case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
  rewrite tensmxE normrcM ler_pM//; apply/bigmax_geP; right.
  by exists (i0,j0). by exists (i1, j1).
rewrite (bigmax_eq_arg _ (0,0))//= (bigmax_eq_arg _ (0,0))//=.
apply/bigmax_geP; right=>/=.
set i := [arg max_(_ > _) _]%O.
set j := [arg max_(_ > _) _]%O.
exists (mxtens_index (i.1, j.1), mxtens_index (i.2, j.2))=>//.
by rewrite tensmxE normrcM.
Qed.

Lemma lpnormrc_swap p m n l k (A : 'M[C]_(m * n, l * k)) : 
  lpnormrc p (mxswap A) = lpnormrc p A.
Proof. by rewrite mxswap_permE lpnormrc_row_perm lpnormrc_col_perm lpnormrc_castmx. Qed.

Lemma ptrace1E m n (A : 'M[C]_(m * n)) i j :
  ptrace1 A i j = \sum_k A (mxtens_index (k,i)) (mxtens_index (k,j)).
Proof.
rewrite castmxE/= summxE; apply eq_bigr=>k _.
rewrite !mxtens_1index mxE (bigD1 (mxtens_index (k, j)))//=.
rewrite mxE (bigD1 (mxtens_index (k, i)))//= !big1.
  by rewrite !tensmxE !mxE !eqxx/= !mulr1 !addr0 mul1r.
all: move=>l; case: (mxtens_indexP l)=>a b;
  rewrite (inj_eq (@mxtens_index_inj _ _))=>/pair_neq/= [|]P;
  by rewrite tensmxE !mxE ?P/= ?(mulr0, mul0r)// [i == b]eq_sym P mulr0 mul0r.
Qed.

Lemma lpnormrc_ptrace1_plt1 p m n (A : 'M[C]_(m * n)) : 
  p < 1 -> lpnormrc p (ptrace1 A) <= m%:R * lpnormrc p A.
Proof.
rewrite lpnormrc.unlock=>->.
apply/bigmax_leP; split=>[|/=[] i j _ /=].
  by rewrite mulr_ge0//; apply/bigmax_geP; left.
rewrite ptrace1E; apply/(le_trans (ler_normrc_sum _ _ _)).
rewrite -[m in m%:R]card_ord mulr_natl -sumr_const.
apply/ler_sum=>k _; apply/bigmax_geP; right.
by exists (mxtens_index (k, i), mxtens_index (k, j)).
Qed.

Lemma lpnormrc_ptrace2_plt1 p m n (A : 'M[C]_(m * n)) : 
  p < 1 -> lpnormrc p (ptrace2 A) <= n%:R * lpnormrc p A.
Proof.
move=>Pp; rewrite ptrace2E1 -[in leRHS]lpnormrc_swap.
by apply/(le_trans (lpnormrc_ptrace1_plt1 _ Pp)).
Qed.

Lemma test I (s : seq I) (P : pred I) (F : I -> C) p :
  1 <= p ->
  let m := (\sum_(i <- s | P i) 1) in
  ``|\sum_(i <- s | P i) F i| `^ p <= m `^ (p - 1) * \sum_(i <- s | P i) ``|F i| `^ p.
Proof.
move=>Pp /=; move: (lt_le_trans ltr01 Pp)=>Pp1; move: (ltW Pp1)=>Pp2.
set m := \sum_(i <- s | P i) 1.
have [/eqP Pm|Pm] := boolP (m == 0).
  suff -> : \sum_(i <- s | P i) F i = 0.
    by rewrite normrc0 powR0// ?gt_eqF// mulr_ge0// sumr_ge0.
  move: Pm; rewrite /m; clear.
  elim: s=>[|a s IH]; first by rewrite !big_nil.
  rewrite !big_cons; case: (P a)=>// /eqP;
  rewrite eq_sym addrC -subr_eq sub0r -[_ == _]negbK=>/negP Pv.
  exfalso; apply/Pv; rewrite eq_sym gt_eqF//.
  apply/(lt_le_trans (y := 0)); first by apply/ltrN10.
  by apply sumr_ge0.
have Pm1: 0 < m by rewrite lt_neqAle eq_sym Pm sumr_ge0.
move: (ltW Pm1)=>Pm2.
pose f := fun i : I => ``|F i|.
under [in leRHS]eq_bigr do rewrite -/(f _).
apply/(le_trans (y := (\sum_(i <- s | P i) f i) `^ p)).
  rewrite ge0_ler_powR// ?nnegrE// ?sumr_ge0 /f//; apply/ler_normrc_sum.
rewrite powRD ?Pm ?implybT// powRN powRr1// mulrAC -mulrA -ler_pdivrMl;
  last by apply powR_gt0.
rewrite mulrC powRN_inv ?sumr_ge0// -powRM ?invr_ge0// ?sumr_ge0//;
  last by rewrite /f.
apply: (@convex_average_seq _ (@powR _ ^~ p) `[0, +oo[).
by move=>t a b; rewrite !in_itv/= !andbT; apply/convex_powR.
by move=>i _; rewrite in_itv/= andbT /f.
by rewrite powR0// gt_eqF.
Qed.

Lemma lpnormrc_ptrace1_pge1 p m n (A : 'M[C]_(m * n)) : 
  1 <= p -> lpnormrc p (ptrace1 A) <= (m%:R) `^ ((p-1)/p) * lpnormrc p A.
Proof.
move=>Pp; rewrite lpnormrc.unlock ltNge Pp/= powRrM -powRM//;
  last by apply/sumr_ge0.
rewrite ge0_ler_powR// ?nnegrE ?mulr_ge0// ?sumr_ge0// ?invr_ge0 ?(le_trans ler01 Pp)//.
rewrite mulr_sumr !pair_bigV/= reindex_mxtens_index/= pair_bigV/= [leRHS]exchange_big/=.
apply ler_sum=>i _; rewrite exchange_big/= reindex_mxtens_index pair_bigV/= [leRHS]exchange_big/=.
apply ler_sum=>j _; rewrite ptrace1E.
apply/(le_trans (test _ _ _ Pp)).
rewrite sumr_const card_ord/= mulr_sumr; apply ler_sum=>k _.
by rewrite -mulr_sumr ler_wpM2l// (bigD1 k)//= lerDl sumr_ge0.
Qed.

Lemma lpnormrc_ptrace2_pge1 p m n (A : 'M[C]_(m * n)) : 
  1 <= p -> lpnormrc p (ptrace2 A) <= (n%:R) `^ ((p-1)/p) * lpnormrc p A.
Proof.
move=>Pp; rewrite ptrace2E1 -[in leRHS]lpnormrc_swap.
by apply/(le_trans (lpnormrc_ptrace1_pge1 _ Pp)).
Qed.

End lpnormrc_basic.

(* Redefine for complex number R[i] *)
(* to avoid unexpected simpl for _ %:C *)
HB.lock
Definition lpnorm (R : realType) (p : R) m n (A : 'M[R[i]]_(m,n)) 
  := (lpnormrc p A)%:C.

Notation "\l_ ( p ) | M |" := (lpnorm p M) : ring_scope.
Notation "\l_ p | M |" := (lpnorm p M) : ring_scope.
Notation l0norm := (lpnorm 0).
Notation "\loo| M |" := (l0norm M) : ring_scope.
Notation l1norm := (lpnorm 1).
Notation "\l1| M |" := (l1norm M) : ring_scope.
Notation l2norm := (lpnorm 2).
Notation "\l2| M |" := (l2norm M) : ring_scope.

(* inherited from normedtype *)
(* `|A| = mx_norm = max element of matrix *)
Section Lpnorm.
Variable (R : realType).
Local Notation C := R[i].

Lemma lpnorm_pSE (p : nat) m n (A : 'M[C]_(m,n)) :
  lpnorm p.+1%:R A = p.+1.-root (\sum_i `|A i.1 i.2| ^+ p.+1).
Proof.
rewrite lpnorm.unlock lpnormrc.unlock ltrn1/= -powC_root//.
do 2 f_equal; rewrite normrc_sum.
apply eq_bigr=>i _; rewrite normrcXn normrc_idV powR_mulrn//.
by move=>i _; rewrite exprn_ge0.
by apply sumr_ge0=> i _; rewrite exprn_ge0.
Qed.

Lemma lpnorm_plt1E p :
  p < 1 -> @lpnorm R p = @lpnorm R 0.
Proof. by move=>Pp; rewrite lpnorm.unlock lpnormrc_plt1E. Qed.

Lemma lpnorm_plt1 p m n :
  p < 1 -> @lpnorm R p m n = normr.
Proof.
move=>Pp; apply/funext=>A.
rewrite lpnorm.unlock lpnormrc.unlock Pp /normr/= mx_normrE.
elim/big_rec2 : _ =>//= i y1 y2 _ <-.
by rewrite /maxr /maxr -ltcR normrcE; case: (_ < _)=>//; rewrite normrcE.
Qed.

Lemma l0norm_norm m n : @lpnorm R 0 m n = normr.
Proof. apply/lpnorm_plt1/ltr01. Qed.

Lemma l0normE m n (A : 'M[C]_(m,n)) :
  lpnorm 0 A = \big[maxr/0]_i `|A i.1 i.2|.
Proof. by rewrite l0norm_norm// /normr/= mx_normrE. Qed.

Lemma l0norm_elem m n (A : 'M[C]_(m,n)) i j :
  `| A i j | <= lpnorm 0 A.
Proof. by rewrite lpnorm.unlock -normrcE /r2c/= lecR l0normrc_elem. Qed.

(* inherited properties *)
Section basic_properties.
Variable (p : R) (m n : nat).
Implicit Type (A B C : 'M[C]_(m,n)).
Local Notation "`[ x ]" := (lpnorm p x).

Lemma lpnorm0_eq0 A : `[ A ] = 0 -> A = 0.
Proof. by move=>/eqP; rewrite lpnorm.unlock realc_eq0 =>/eqP/lpnormrc0_eq0. Qed.

Lemma lpnormZ a A : `[ a *: A ] = `|a| * `[ A ].
Proof. by rewrite lpnorm.unlock lpnormrcZ realcM normrcE. Qed.

Lemma lpnorm_triangle A B : `[ A + B ] <= `[ A ] + `[ B ].
Proof. by rewrite lpnorm.unlock -realcD lecR lpnormrc_triangle. Qed.
Definition ler_lpnormD := lpnorm_triangle.

HB.instance Definition _ := isVNorm.Build C 'M[C]_(m, n) (@lpnorm R p m n)
  lpnorm_triangle lpnorm0_eq0 lpnormZ.

Lemma lpnorm0 : `[ 0 : 'M[C]_(m,n) ] = 0.
Proof. exact: normv0. Qed.

Lemma lpnorm0P A : reflect (`[ A ] = 0) (A == 0).
Proof. exact: normv0P. Qed.

Definition lpnorm_eq0 A := sameP (`[ A ] =P 0) (lpnorm0P A).

Lemma lpnormMn A : `[ A *+ n] = `[ A ] *+ n.
Proof. exact: normvMn. Qed.

Lemma lpnormN A : `[ - A ] = `[ A ].
Proof. exact: normvN. Qed.

Lemma lpnorm_ge0 A : `[ A ] >= 0.
Proof. exact: normv_ge0. Qed.

Lemma lpnorm_nneg A : `[ A ] \is Num.nneg.
Proof. exact: normv_nneg. Qed.

Lemma lpnorm_real A : `[ A ] \is Num.real.
Proof. exact: normv_real. Qed.

Lemma lpnorm_gt0 A : `[ A ] > 0 = (A != 0).
Proof. exact: normv_gt0. Qed.

Lemma ler_lpnormB A B : `[A - B] <= `[A] + `[B].
Proof. exact: lev_normB. Qed.

Lemma ler_lpdistD A B C : `[B-C] <= `[B-A] + `[A-C].
Proof. exact: lev_distD. Qed.

Lemma lpdistC A B : `[ A - B ] = `[ B - A ].
Proof. exact: distvC. Qed.

Lemma lerB_lpnormD A B : `[A] - `[B] <= `[A + B].
Proof. exact: levB_normD. Qed.

Lemma lerB_lpdist A B : `[A] - `[B] <= `[A - B].
Proof. exact: levB_dist. Qed.

Lemma ler_dist_lpdist A B : `| `[A] - `[B] | <= `[A - B].
Proof. exact: lev_dist_dist. Qed.

Lemma ler_lpnorm_sum I (r : seq I) (P: pred I) (f : I -> 'M[C]_(m,n)) :
  `[ \sum_(i <- r | P i) f i ] <= \sum_(i <- r | P i) `[ f i ].
Proof. exact: normv_sum. Qed.

Lemma lpnorm_id A : `| `[A] | = `[A].
Proof. exact: normv_id. Qed.

Lemma lpnorm_le0 A : `[A] <= 0 = (A == 0).
Proof. exact: normv_le0. Qed.

Lemma lpnorm_lt0 A : `[A] < 0 = false.
Proof. exact: normv_lt0. Qed.

Lemma lpnorm_gep0 A : lpnorm 0 A <= lpnorm p A.
Proof. by rewrite lpnorm.unlock lecR lpnormrc_gep0. Qed.

Lemma lpnorm_lep0 (A : 'M[C]_(m,n)) :
  0 <= p -> lpnorm p A / ((m * n)%:R `^ p^-1)%:C <= lpnorm 0 A.
Proof. by rewrite lpnorm.unlock -realcI -realcM lecR; exact: lpnormrc_lep0. Qed.

Lemma lpnorm_p0ge (A : 'M[C]_(m,n)) :
  0 <= p -> lpnorm p A <= ((m * n)%:R `^ p^-1)%:C * lpnorm 0 A.
Proof. by rewrite lpnorm.unlock -realcM lecR; exact: lpnormrc_p0ge. Qed.

End basic_properties.

Lemma lpnorm_continuous p m n : continuous (@lpnorm R p m n).
Proof. by apply/continuous_mnorm. Qed.

Lemma continuous_lpnorm p m n (A : 'M[C]_(m,n)) : 
  1 < p -> {for p, continuous (fun p0 : R => lpnorm p0 A)}.
Proof.
move=>Pp; rewrite lpnorm.unlock; apply/continuous_comp.
by apply/continuous_lpnormrc. by apply/rc_continuous.
Qed.

Lemma lpnorm_nincr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) :
  1 <= p1 <= p2 -> lpnorm p1 A >= lpnorm p2 A.
Proof. rewrite lpnorm.unlock lecR; exact: lpnormrc_nincr. Qed.

Lemma lpnorm_is_cvg (m n : nat) (A : 'M[C]_(m,n)) :
  cvgn (fun k : nat => lpnorm k.+1%:R A).
Proof.
rewrite lpnorm.unlock; apply: is_etcvg_map.
apply: rc_continuous. apply: lpnormrc_is_cvg.
Qed.

Lemma lpnorm_cvg (m n : nat) (A : 'M[C]_(m,n)) :
  (fun k => lpnorm k.+1%:R A) @ \oo --> lpnorm 0 A.
Proof.
rewrite lpnorm.unlock; apply: etcvg_map.
apply: rc_continuous. apply: lpnormrc_cvg.
Qed.

Lemma lpnorm_cvg1R (m n : nat) (A : 'M[C]_(m,n)) :
  (fun p => lpnorm p A) @ 1^'+ --> lpnorm 1 A.
Proof.
rewrite lpnorm.unlock; apply: etcvg_map.
apply: rc_continuous. apply: lpnormrc_cvg1R.
Qed.

Lemma lpnorm_cvg1 (m n : nat) (A : 'M[C]_(m,n)) :
  (fun p : nat => lpnorm (1+p%:R^-1) A) @ \oo --> lpnorm 1 A.
Proof.
rewrite lpnorm.unlock; apply: etcvg_map.
apply: rc_continuous. apply: lpnormrc_cvg1.
Qed.

Lemma lpnorm_is_cvg1 (m n : nat) (A : 'M[C]_(m,n)) :
  cvgn (fun p : nat => lpnorm (1+p%:R^-1) A).
Proof. apply/cvg_ex; exists (lpnorm 1 A); exact: lpnorm_cvg1. Qed.

Lemma lpnorm_ndecr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) : 
  1 <= p1 <= p2 -> 
  lpnorm p1 A / ((m * n)%:R `^ p1^-1)%:C <= lpnorm p2 A / ((m * n)%:R `^ p2^-1)%:C.
Proof. rewrite lpnorm.unlock -!realcI -!realcM lecR; exact: lpnormrc_ndecr. Qed.

Lemma lpnorm_trmx p q r (M: 'M[C]_(q,r)) : lpnorm p (M^T) = lpnorm p M.
Proof. by rewrite lpnorm.unlock lpnormrc_trmx. Qed.

Lemma lpnorm_diag p q (D : 'rV[C]_q) : lpnorm p (diag_mx D) = lpnorm p D.
Proof. by rewrite lpnorm.unlock lpnormrc_diag. Qed.

Lemma lpnorm_conjmx p q r (M: 'M[C]_(q,r)) : lpnorm p (M^*m) = lpnorm p M.
Proof.
rewrite lpnorm.unlock lpnormrc.unlock.
under eq_bigr do rewrite mxE normrc_conjC.
by under [X in if _ then X else _] eq_bigr do rewrite mxE normrc_conjC.
Qed.

Lemma lpnorm_adjmx p q r (M: 'M[C]_(q,r)) : lpnorm p (M^*t) = lpnorm p M.
Proof. by rewrite adjmxE lpnorm_conjmx lpnorm_trmx. Qed.

Lemma lpnorm_col_perm p m n (s : 'S_n) (A : 'M[C]_(m,n)) :
  lpnorm p (col_perm s A) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_col_perm. Qed.

Lemma lpnorm_row_perm p m n (s : 'S_m) (A : 'M[C]_(m,n)) :
  lpnorm p (row_perm s A) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_row_perm. Qed.

Lemma lpnorm_permMl p m n (s : 'S_m) (A : 'M[C]_(m,n)) :
  lpnorm p (perm_mx s *m A) = lpnorm p A.
Proof. by rewrite -row_permE lpnorm_row_perm. Qed.

Lemma lpnorm_permMr p m n (s : 'S_n) (A : 'M[C]_(m,n)) :
  lpnorm p (A *m perm_mx s) = lpnorm p A.
Proof. by rewrite col_permEV lpnorm_col_perm. Qed.

Lemma lpnorm_castmx p m n m' n' (eqmn : (m = m') * (n = n')) (A : 'M[C]_(m,n)) :
  lpnorm p (castmx eqmn A) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_castmx. Qed.

Lemma lpnorm_row0mx p m n r (A : 'M[C]_(m,r)) : 
  lpnorm p (row_mx (0 : 'M_(m,n)) A) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_row0mx. Qed.

Lemma lpnorm_rowmx0 p m n r (A : 'M[C]_(m,n)) : 
  lpnorm p (row_mx A (0 : 'M_(m,r))) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_rowmx0. Qed.

Lemma lpnorm_col0mx p m n r (A : 'M[C]_(n,r)) : 
  lpnorm p (col_mx (0 : 'M_(m,r)) A) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_col0mx. Qed.

Lemma lpnorm_colmx0 p m n r (A : 'M[C]_(m,r)) : 
  lpnorm p (col_mx A (0 : 'M_(n,r))) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_colmx0. Qed.

Lemma lpnorm_cdiag m p q (D: 'rV[C]_(minn p q)) :
  lpnorm m (cdiag_mx D) = lpnorm m D.
Proof.
by rewrite /cdiag_mx /block_mx lpnorm_castmx 
  row_mx0 lpnorm_colmx0 lpnorm_rowmx0 lpnorm_diag.
Qed.

Lemma lpnorm_svd_d_exdr p (m n : nat) (D : 'rV[C]_(minn m n)) :
  lpnorm p (svd_d_exdr D) = lpnorm p D.
Proof. by rewrite /svd_d_exdr lpnorm_castmx lpnorm_rowmx0. Qed.

Lemma lpnorm_svd_d_exdl p (m n : nat) (D : 'rV[C]_(minn m n)) :
  lpnorm p (svd_d_exdl D) = lpnorm p D.
Proof. by rewrite /svd_d_exdl lpnorm_castmx lpnorm_rowmx0. Qed.

Lemma lpnormM p m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  1 <= p <= 2 -> lpnorm p (A *m B) <= lpnorm p A * lpnorm p B.
Proof. by rewrite lpnorm.unlock -rmorphM/= lecR; exact: lpnormrcM. Qed.

Lemma lpnormMl p (q : cindexType p) m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  2 <= p -> lpnorm p (A *m B) <= lpnorm p A * lpnorm q B.
Proof. by rewrite lpnorm.unlock -rmorphM/= lecR; exact: lpnormrcMl. Qed.

Lemma lpnormMr p (q : cindexType p) m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  2 <= p -> lpnorm p (A *m B) <= lpnorm q A * lpnorm p B.
Proof. by rewrite lpnorm.unlock -rmorphM/= lecR; exact: lpnormrcMr. Qed.

Lemma l0normMl m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  lpnorm 0 (A *m B) <= lpnorm 0 A * lpnorm 1 B.
Proof. by rewrite lpnorm.unlock -rmorphM/= lecR; exact: l0normrcMl. Qed.

Lemma l0normMr m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) : 
  lpnorm 0 (A *m B) <= lpnorm 1 A * lpnorm 0 B.
Proof. by rewrite lpnorm.unlock -rmorphM/= lecR; exact: l0normrcMr. Qed.

Lemma lpnorm_col_pge1 p m n (A : 'M[C]_(m,n)) : 1 <= p -> 
  lpnorm p A = ((\sum_i (complex.Re (lpnorm p (col i A)) : R) `^ p) `^ p^-1)%:C.
Proof.
move=>Pp; rewrite lpnorm.unlock/=; f_equal.
exact: lpnormrc_col_pge1.
Qed.

Lemma bigmax_r2c I (r : seq I) (P : pred I) (f : I -> R) :
  \big[maxr/0]_(i <- r | P i) (f i)%:C = (\big[maxr/0]_(i <- r | P i) f i)%:C.
Proof.
elim/big_rec2: _ =>// i y1 ?? ->.
by rewrite !/maxr ltcR; case: ltP.
Qed.

Lemma lpnorm_col_plt1 p m n (A : 'M[C]_(m,n)) :
  p < 1 -> lpnorm p A = \big[maxr/0]_i (lpnorm 0 (col i A)).
Proof.
rewrite lpnorm.unlock bigmax_r2c => Pp; 
by f_equal; exact: lpnormrc_col_plt1.
Qed.

Lemma lpnorm_col_le p m n (A : 'M[C]_(m,n)) i :
  lpnorm p (col i A) <= lpnorm p A.
Proof. by rewrite lpnorm.unlock lecR lpnormrc_col_le. Qed.

Lemma lpnorm_row_le p m n (A : 'M[C]_(m,n)) i :
  lpnorm p (row i A) <= lpnorm p A.
Proof. by rewrite lpnorm.unlock lecR lpnormrc_row_le. Qed.

Lemma lpnorm_rowmxl_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  lpnorm p A <= lpnorm p (row_mx A B).
Proof. by rewrite lpnorm.unlock lecR lpnormrc_rowmxl_le. Qed.

Lemma lpnorm_rowmxr_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  lpnorm p B <= lpnorm p (row_mx A B).
Proof. by rewrite lpnorm.unlock lecR lpnormrc_rowmxr_le. Qed.

Lemma lpnorm_colmxl_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  lpnorm p A <= lpnorm p (col_mx A B).
Proof. by rewrite lpnorm.unlock lecR lpnormrc_colmxl_le. Qed.

Lemma lpnorm_colmxr_le p m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  lpnorm p B <= lpnorm p (col_mx A B).
Proof. by rewrite lpnorm.unlock lecR lpnormrc_colmxr_le. Qed.

Lemma lpnorm_delta p m n (i : 'I_m) (j : 'I_n) : 
  lpnorm p (delta_mx i j : 'M[C]_(m,n)) = 1.
Proof. by rewrite lpnorm.unlock lpnormrc_delta. Qed.

Lemma lpnorm_const_plt1 p m n (a : C) : p < 1 -> 
  lpnorm p (const_mx a : 'M[C]_(m,n)) = `|a| * ((m != 0) && (n != 0))%:R.
Proof.
by move=>Pp; rewrite lpnorm.unlock lpnormrc_const_plt1// realcM normrcE natrC.
Qed.

Lemma lpnorm_const_pge1 p m n (a : C) : 1 <= p -> 
  lpnorm p (const_mx a : 'M[C]_(m,n)) = ((m * n)%:R `^ p^-1)%:C * `|a|.
Proof.
by move=>Pp; rewrite lpnorm.unlock lpnormrc_const_pge1// realcM normrcE.
Qed.

Lemma lpnorm_scale_plt1 p m (a : C) : p < 1 -> 
  lpnorm p (a%:M : 'M[C]_m) = `|a| * (m != 0)%:R.
Proof.
by move=>Pp; rewrite lpnorm.unlock lpnormrc_scale_plt1// realcM normrcE natrC.
Qed.

Lemma lpnorm_scale_pge1 p m (a : C) : 1 <= p -> 
  lpnorm p (a%:M : 'M[C]_m) = (m%:R `^ p^-1)%:C * `|a|.
Proof.
by move=>Pp; rewrite lpnorm.unlock lpnormrc_scale_pge1// realcM normrcE.
Qed.

Lemma lpnorm1_pge1 p m : 
  1 <= p -> lpnorm p (1%:M : 'M[C]_m) = ((m)%:R `^ p^-1)%:C.
Proof. by move=>Pp; rewrite lpnorm.unlock lpnormrc1_pge1. Qed.

Lemma lpnorm1_plt1 p m : 
  p < 1 -> lpnorm p (1%:M : 'M[C]_m) = (m != 0)%:R.
Proof. by move=>Pp; rewrite lpnorm_scale_plt1// normr1 mul1r. Qed.

Lemma lpnorm11 p (A : 'M[C]_(1,1)) :
  lpnorm p A = `|A 0 0|.
Proof. by rewrite lpnorm.unlock lpnormrc11 normrcE. Qed.

Lemma lpnorm_mul_deltar p m n l (A : 'M[C]_(m,n)) (i : 'I_n) (j : 'I_l) : 
  lpnorm p (A *m delta_mx i j) = lpnorm p (col i A).
Proof. by rewrite lpnorm.unlock lpnormrc_mul_deltar. Qed.

Lemma lpnorm_mul_deltal p m n l (A : 'M[C]_(m,n)) (i : 'I_l) (j : 'I_m) : 
  lpnorm p (delta_mx i j *m A) = lpnorm p (row j A).
Proof. by rewrite lpnorm.unlock lpnormrc_mul_deltal. Qed.

Lemma lpnorm_hoelder p (q : ecindexType p) m (u : 'rV[C]_m) (v : 'cV[C]_m) :
  lpnorm 1 (u *m v) <= lpnorm p u * lpnorm q v.
Proof. rewrite lpnorm.unlock -realcM lecR; exact: lpnormrc_hoelder. Qed.

Lemma lpnorm_cauchy m (u : 'rV[C]_m) (v : 'cV[C]_m) :
  `| \tr (u *m v) | <= l2norm u * l2norm v.
Proof. rewrite lpnorm.unlock -realcM -normrcE lecR; exact: lpnormrc_cauchy. Qed.

Lemma lpnorm_tens x (m n p q : nat) (A : 'M[C]_(m,n)) (B : 'M_(p,q)) :
  lpnorm x (A *t B) = lpnorm x A * lpnorm x B.
Proof. by rewrite lpnorm.unlock lpnormrc_tens realcM. Qed.

Lemma lpnorm_swap p m n l k (A : 'M[C]_(m * n, l * k)) : 
  lpnorm p (mxswap A) = lpnorm p A.
Proof. by rewrite lpnorm.unlock lpnormrc_swap. Qed.

Lemma lpnorm_ptrace1_plt1 p m n (A : 'M[C]_(m * n)) : 
  p < 1 -> lpnorm p (ptrace1 A) <= m%:R * lpnorm p A.
Proof. by move=>Pp; rewrite lpnorm.unlock -natrC -realcM lecR lpnormrc_ptrace1_plt1. Qed.

Lemma lpnorm_ptrace2_plt1 p m n (A : 'M[C]_(m * n)) : 
  p < 1 -> lpnorm p (ptrace2 A) <= n%:R * lpnorm p A.
Proof. by move=>Pp; rewrite lpnorm.unlock -natrC -realcM lecR lpnormrc_ptrace2_plt1. Qed.

Lemma lpnorm_ptrace1_pge1 p m n (A : 'M[C]_(m * n)) : 
  1 <= p -> lpnorm p (ptrace1 A) <= ((m%:R) `^ ((p-1)/p))%:C * lpnorm p A.
Proof. by move=>Pp; rewrite lpnorm.unlock -realcM lecR lpnormrc_ptrace1_pge1. Qed.

Lemma lpnorm_ptrace2_pge1 p m n (A : 'M[C]_(m * n)) : 
  1 <= p -> lpnorm p (ptrace2 A) <= ((n%:R) `^ ((p-1)/p))%:C * lpnorm p A.
Proof. by move=>Pp; rewrite lpnorm.unlock -realcM lecR lpnormrc_ptrace2_pge1. Qed.

Lemma l0norm_dmul m n (M : 'M[C]_(m,n)) :
  l0norm (M .^+ 2) = (l0norm M) ^+ 2.
Proof.
rewrite l0norm_norm.
case: m M=>[|m]; case: n=>[|n]; intros; rewrite ?mx_dim0 ?normr0 ?expr0n//.
apply/le_anti/andP; split; rewrite /Num.norm/= /mx_norm;
rewrite (bigmax_eq_arg _ (ord0,ord0))//=.
2,4: move=>? _; rewrite -num_le//=.
all: set t := [arg max_(i > (ord0, ord0)) _]%O.
rewrite mxE normrX ler_pXn2r// ?nnegrE// num_le.
by apply/bigmax_geP; right; exists t=>//; rewrite -num_le/=.
rewrite -normrX num_le.
by apply/bigmax_geP; right; exists t=>//; rewrite -num_le/= mxE.
Qed.

Section L0L1L2Norm.
Variable (m n: nat).
Local Notation M := 'M[C]_(m,n).

Definition l0norm_ge0 := (lpnorm_ge0 (0 : R)).
Definition l0norm_nneg := (lpnorm_nneg (0 : R)).
Definition l0norm_trmx := (lpnorm_trmx (0 : R)).
Definition l0norm_adjmx := (lpnorm_adjmx (0 : R)).
Definition l0norm_conjmx := (lpnorm_conjmx (0 : R)).
Definition l0norm_diag := (lpnorm_diag (0 : R)).
Definition l0norm_cdiag := (lpnorm_cdiag (0 : R)).
Definition l0norm_triangle := (lpnorm_triangle (0 : R)).
Definition ler_l0normD := l0norm_triangle.
Definition l0norm_delta := (lpnorm_delta (0 : R)).
Definition l0norm11 := (lpnorm11 (0 : R)).
Definition l1norm_ge0 := (lpnorm_ge0 (1 : R)).
Definition l1norm_nneg := (lpnorm_nneg (1 : R)).
Definition l1norm_trmx := (lpnorm_trmx (1 : R)).
Definition l1norm_adjmx := (lpnorm_adjmx (1 : R)).
Definition l1norm_conjmx := (lpnorm_conjmx (1 : R)).
Definition l1norm_diag := (lpnorm_diag (1 : R)).
Definition l1norm_cdiag := (lpnorm_cdiag (1 : R)).
Definition l1norm_triangle := (lpnorm_triangle (1 : R)).
Definition ler_l1normD := l1norm_triangle.
Definition l1norm_delta := (lpnorm_delta (1 : R)).
Definition l1norm11 := (lpnorm11 (1 : R)).
Definition l1norm_tens := (lpnorm_tens (1 : R)).
Definition l1norm_swap := (lpnorm_swap (1 : R)).
Definition l2norm_ge0 := (lpnorm_ge0 (2 : R)).
Definition l2norm_nneg := (lpnorm_nneg (2 : R)).
Definition l2norm_trmx := (lpnorm_trmx (2 : R)).
Definition l2norm_adjmx := (lpnorm_adjmx (2 : R)).
Definition l2norm_conjmx := (lpnorm_conjmx (2 : R)).
Definition l2norm_diag := (lpnorm_diag (2 : R)).
Definition l2norm_cdiag := (lpnorm_cdiag (2 : R)).
Definition l2norm_triangle := (lpnorm_triangle (2 : R)).
Definition ler_l2normD := l2norm_triangle.
Definition l2norm_delta := (lpnorm_delta (2 : R)).
Definition l2norm11 := (lpnorm11 (2 : R)).
Definition l2norm_tens := (lpnorm_tens (2 : R)).
Definition l2norm_swap := (lpnorm_swap (2 : R)).

Lemma l0norm_const (a : C) : 
  lpnorm 0 (const_mx a : 'M[C]_(m,n)) = `|a| * ((m != 0) && (n != 0))%:R.
Proof. by rewrite lpnorm_const_plt1. Qed.

Lemma l1norm_const (a : C) : 
  lpnorm 1 (const_mx a : 'M[C]_(m,n)) = (m * n)%:R * `|a|.
Proof. by rewrite lpnorm_const_pge1// invr1 powRr1// natrC. Qed.

Lemma l2norm_const (a : C) : 
  lpnorm 2 (const_mx a : 'M[C]_(m,n)) = sqrtC (m * n)%:R * `|a|.
Proof. by rewrite lpnorm_const_pge1 ?powR12_sqrtCV// ?natrC// mulr2n lerDl. Qed.

Lemma l0norm_scale (a : C) : 
  lpnorm 0 (a%:M : 'M[C]_m) = `|a| * (m != 0)%:R.
Proof. by rewrite lpnorm_scale_plt1. Qed.

Lemma l1norm_scale (a : C) : 
  lpnorm 1 (a%:M : 'M[C]_m) = m%:R * `|a|.
Proof. by rewrite lpnorm_scale_pge1// invr1 powRr1// natrC. Qed.

Lemma l2norm_scale (a : C) : 
  lpnorm 2 (a%:M : 'M[C]_m) = sqrtC m%:R * `|a|.
Proof. by rewrite lpnorm_scale_pge1 ?powR12_sqrtCV// ?natrC// mulr2n lerDl. Qed.

Lemma l0norm1 : lpnorm 0 (1%:M : 'M[C]_m) = (m != 0)%:R.
Proof. by rewrite lpnorm.unlock l0normrc1 natrC. Qed.

Lemma l1norm1 : lpnorm 1 (1%:M : 'M[C]_m) = m%:R.
Proof. by rewrite l1norm_scale normr1 mulr1. Qed.

Lemma l2norm1 : lpnorm 2 (1%:M : 'M[C]_m) = sqrtC m%:R.
Proof. by rewrite l2norm_scale normr1 mulr1. Qed.

Lemma dotV_l2norm (M: 'M[C]_(m,n)) : \tr (M ^*t *m M) = l2norm M ^+2.
Proof.
rewrite lpnorm_pSE sqrtCK -(pair_bigA _ (fun x y=> `|M x y| ^+2))/= exchange_big.
rewrite /mxtrace; apply eq_bigr=>i _; rewrite !mxE; apply eq_bigr=>j _.
by rewrite !mxE normCKC.
Qed.

Lemma dot_l2norm (M: 'M[C]_(m,n)) : \tr (M *m M ^*t) = l2norm M ^+2.
Proof. by rewrite -dotV_l2norm mxtrace_mulC. Qed.

Lemma l2norm_dotV (M: 'M[C]_(m,n)) : l2norm M = sqrtC (\tr (M ^*t *m M)).
Proof. by rewrite dotV_l2norm exprCK// l2norm_ge0. Qed.

Lemma l2norm_dot (M: 'M[C]_(m,n)) : l2norm M = sqrtC (\tr (M *m M ^*t)).
Proof. by rewrite l2norm_dotV mxtrace_mulC. Qed.

Lemma l2normE (A : 'M[C]_(m,n)) : l2norm A = sqrtC (\sum_i\sum_j `|A i j| ^+ 2).
Proof. by rewrite lpnorm_pSE pair_bigV. Qed.

Lemma l1normE (A : 'M[C]_(m,n)) : l1norm A = \sum_i\sum_j `|A i j|.
Proof.
have -> : 1 = 0.+1%:R :> R by [].
rewrite lpnorm_pSE root1C pair_bigV/=.
by do 2 apply/eq_bigr=>? _; rewrite expr1.
Qed.

Lemma l2norm_le_l1 (A: 'M[C]_(m,n)) : l2norm A <= l1norm A.
Proof. by apply/lpnorm_nincr; rewrite lexx ler1Sn. Qed.

Lemma l1norm_le_l2 (A: 'M[C]_(m,n)) : l1norm A <= sqrtC (m * n)%:R * l2norm A.
Proof.
move: (lpnorm_ndecr (p1 := 1) (p2 := 2))=>/(_ _ _ A).
rewrite lexx ler1Sn=>/(_ isT).
rewrite (powC_rootV (p := 1))// (powC_rootV (p := 2))// root1C natrC.
case E: (0 < (m * n)%:R :> C).
  by rewrite ler_pdivrMr// -{2}[(m*n)%:R]sqrtCK expr2 !mulrA 
    mulfVK 1?mulrC// sqrtC_eq0 (gt_eqF E).
move: E; rewrite ltr0n lt0n muln_eq0=>/negbFE/mx_dim0_cond/(_ A)/=->.
by rewrite !lpnorm0 mulr0.
Qed.

Lemma l2norm_unitary (U : 'M[C]_(m,n)) :
  U \is unitarymx -> l2norm U = sqrtC m%:R.
Proof. by move=>/unitarymxP PU; rewrite l2norm_dot PU mxtrace1. Qed.

End L0L1L2Norm.

Lemma l2normCE : @l2normC C = @l2norm.
Proof.
do 2 apply/functional_extensionality_dep=>?.
by apply/funext=>A; rewrite l2norm_dot l2normC_dot.
Qed.

Lemma l2normUr m n l (U : 'M[C]_(n,l)) (M : 'M[C]_(m,n)): 
  U \is unitarymx -> l2norm (M *m U) = l2norm M.
Proof.
by move=>P; rewrite l2norm_dot !adjmxM !mulmxA mulmxtVK// -l2norm_dot.
Qed.

Lemma l2normUl_cond m n l (U : 'M[C]_(l,m)) (M : 'M[C]_(m,n)): 
  U^*t \is unitarymx -> l2norm (U *m M) = l2norm M.
Proof. by move=>PU; rewrite -l2norm_adjmx adjmxM l2normUr// l2norm_adjmx. Qed.

Lemma l2normUl m n (U : 'M[C]_m) (M : 'M[C]_(m,n)): 
  U \is unitarymx -> l2norm (U *m M) = l2norm M.
Proof. by move=>PU; rewrite l2normUl_cond ?adjmx_unitary. Qed.

Lemma l0norm_ptrace1 m n (A : 'M[C]_(m * n)) : 
  l0norm (ptrace1 A) <= m%:R * l0norm A.
Proof. by apply/lpnorm_ptrace1_plt1. Qed.

Lemma l0norm_ptrace2 m n (A : 'M[C]_(m * n)) : 
  l0norm (ptrace2 A) <= n%:R * l0norm A.
Proof. by apply/lpnorm_ptrace2_plt1. Qed.

Lemma l1norm_ptrace1 m n (A : 'M[C]_(m * n)) : 
  l1norm (ptrace1 A) <= l1norm A.
Proof.
by move: (lpnorm_ptrace1_pge1 A (lexx 1)); rewrite subrr mul0r powRr0 mul1r.
Qed.

Lemma l1norm_ptrace2 m n (A : 'M[C]_(m * n)) : 
  l1norm (ptrace2 A) <= l1norm A.
Proof.
by move: (lpnorm_ptrace2_pge1 A (lexx 1)); rewrite subrr mul0r powRr0 mul1r.
Qed.

Lemma l2norm_ptrace1 m n (A : 'M[C]_(m * n)) : 
  l2norm (ptrace1 A) <= sqrtC m%:R * l2norm A.
Proof.
have /(lpnorm_ptrace1_pge1 A) : 1 <= 2 :> R by rewrite ler1n.
by rewrite -{2}nat1r addrK mul1r powR12_sqrtCV// natrC.
Qed.

Lemma l2norm_ptrace2 m n (A : 'M[C]_(m * n)) : 
  l2norm (ptrace2 A) <= sqrtC n%:R * l2norm A.
Proof.
have /(lpnorm_ptrace2_pge1 A) : 1 <= 2 :> R by rewrite ler1n.
by rewrite -{2}nat1r addrK mul1r powR12_sqrtCV// natrC.
Qed.

End Lpnorm.

#[global] Hint Extern 0 (is_true (0 <= lpnorm _ _)) => apply: lpnorm_ge0 : core.

(* induced norm *)
HB.lock
Definition ipqnormrc (R : realType) (C : extNumType R) p q m n (A : 'M[C]_(m,n)) :=
  sup ([set 0] `|` [set x | exists v : 'cV[C]_n, lpnormrc p v = 1 /\ lpnormrc q (A *m v) = x]).

Section induced_normrc.
Variable (R : realType) (C : extNumType R).
Implicit Type (p q : R) (m n : nat).

Lemma ipqnormrc_plt1E p q : 
  p < 1 -> @ipqnormrc R C p q = ipqnormrc 0 q.
Proof. by move=>Pp; rewrite ipqnormrc.unlock (lpnormrc_plt1E _ Pp). Qed.

Lemma ipqnormrc_qlt1E p q : 
  q < 1 -> @ipqnormrc R C p q = ipqnormrc p 0.
Proof. by move=>Pq; rewrite ipqnormrc.unlock (lpnormrc_plt1E _ Pq). Qed.

Lemma ipqnormrc_pqlt1E p q : 
  p < 1 -> q < 1 -> @ipqnormrc R C p q = ipqnormrc 0 0.
Proof. by move=>Pp Pq; rewrite ipqnormrc_plt1E// ipqnormrc_qlt1E. Qed.

Lemma ipqnormrc_set_has_sup p q m n (A : 'M[C]_(m,n)) :
  has_sup ([set 0] `|` [set x | exists v : 'cV[C]_n, 
    lpnormrc p v = 1 /\ lpnormrc q (A *m v) = x]).
Proof.
split; first by exists 0=>/=; left.
case: (leP 0 q) => [Hq | Hq]; last first.
  rewrite (lpnormrc_plt1E _ (lt_trans Hq ltr01)); clear q Hq; pose q := 0 : R;
  have Hq : 0 <= q by [].
all:  exists (((m * 1)%:R `^ q^-1) * lpnormrc 1 A) => x /= [->| [v [Pv <-]]];
    first by rewrite mulr_ge0.
all: apply/(le_trans (lpnormrc_p0ge (A *m v) Hq));
  rewrite ler_wpM2l//; apply/(le_trans (l0normrcMr _ _))/ler_piMr;
  by rewrite // -Pv lpnormrc_gep0.
Qed.

Lemma ipqnormrc_ge0 p q m n (A : 'M[C]_(m,n)) :
  0 <= ipqnormrc p q A.
Proof.
rewrite ipqnormrc.unlock; 
by apply: (sup_upper_bound (ipqnormrc_set_has_sup p q A))=>/=; left.
Qed.

#[local] Hint Extern 0 (is_true (0 <= ipqnormrc _ _ _)) => apply: ipqnormrc_ge0 : core.

Lemma ipqnormrcP p q m n (A : 'M[C]_(m,n)) (v : 'cV[C]_n) :
  lpnormrc q (A *m v) <= ipqnormrc p q A * lpnormrc p v.
Proof.
case E: (v == 0); first by move: E=>/eqP->; rewrite mulmx0 !lpnormrc0 mulr0.
move: E=>/eqP/eqP Py.
have Pv: 0 < lpnormrc p v by rewrite lt_def lpnormrc_eq0 Py/=.
rewrite mulrC -ler_pdivrMl// mulrC ipqnormrc.unlock.
apply: (sup_upper_bound (ipqnormrc_set_has_sup p q A))=>/=; right.
exists (r2c (lpnormrc p v)^-1 *: v); split.
  by rewrite lpnormrcZ normrc.unlock ger0_norm ?r2c_ge0/= 
    ?invr_ge0// r2cK mulVf// gt_eqF.
by rewrite linearZ/= lpnormrcZ mulrC normrc.unlock ger0_norm 
  ?r2c_ge0/= ?invr_ge0// r2cK.
Qed.

Lemma ipqnormrcPV p q m n (A : 'M[C]_(m,n)) (v : 'cV[C]_n) :
  lpnormrc q (A *m v) / lpnormrc p v <= ipqnormrc p q A.
Proof.
have [/eqP ->| Pv ] := boolP (lpnormrc p v == 0).
  by rewrite invr0 mulr0.
by rewrite ler_pdivrMr ?lt_def ?Pv//= ipqnormrcP.
Qed.

Lemma ipqnormrcP_pqge1 p q m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  1 <= p <= q ->
  lpnormrc q (A *m v) <= ipqnormrc p q A * lpnormrc p v.
Proof.
move=>/andP[] Pp Ppq; move: (le_trans Pp Ppq)=>Pq; move: (le_trans ler01 Pq)=>Pq0.
rewrite !lpnormrc_col_pge1//.
apply: (le_trans (y := (\sum_i (ipqnormrc p q A) `^ q * lpnormrc p (col i v) `^ q) `^ q^-1)).
rewrite ge0_ler_powR// ?invr_ge0// ?nnegrE ?sumr_ge0// =>[??|];
rewrite ?mulr_ge0// ler_sum//==> i _; rewrite -powRM// ?lpnormrc_ge0//.
rewrite ge0_ler_powR// ?nnegrE// ?mulr_ge0//.
by rewrite colE -mulmxA -colE ipqnormrcP.
rewrite -mulr_sumr powRM ?sumr_ge0 ?powR_ge0=>[|//|//|//].
rewrite -powRrM mulfV ?powRr1 ?ler_wpM2l=>[//|//||//|].
pose B := \col_i (lpnormrc p (col i v)).
move: (lpnormrc_nincr (p1 := p) (p2 := q) B).
rewrite Ppq Pp/= {1 2}lpnormrc.unlock ?ltNge Pq Pp/= !pair_bigV/= 
  exchange_big/= big_ord1 exchange_big/= big_ord1=>/(_ isT).
under eq_bigr do rewrite mxE (ger0_normrc (lpnormrc_ge0 _ _)) /c2r/=.
by under [in X in _ <= X -> _]eq_bigr do 
  rewrite mxE (ger0_normrc (lpnormrc_ge0 _ _)) /c2r/=.
by rewrite gt_eqF// (lt_le_trans ltr01 Pq).
Qed.

Lemma ipqnormrcPV_pqge1 p q m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  1 <= p <= q ->
  lpnormrc q (A *m v) / lpnormrc p v <= ipqnormrc p q A.
Proof.
have [/eqP ->| Pv ] := boolP (lpnormrc p v == 0).
  by rewrite invr0 mulr0.
by rewrite ler_pdivrMr ?lt_def ?Pv//=; exact: ipqnormrcP_pqge1.
Qed.

Lemma ip0normrcP p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnormrc 0 (A *m v) <= ipqnormrc p 0 A * lpnormrc p v.
Proof.
rewrite lpnormrc_col_plt1 ?ltr01//; apply/bigmax_leP; 
  split=>[|/= i _]; first by rewrite mulr_ge0.
rewrite colE -mulmxA -colE.
apply/(le_trans (ipqnormrcP p _ _ _)).
by rewrite ler_wpM2l// lpnormrc_col_le.
Qed.

Lemma ip0normrcPV p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnormrc 0 (A *m v) / lpnormrc p v <= ipqnormrc p 0 A.
Proof.
have [/eqP ->| Pv ] := boolP (lpnormrc p v == 0).
  by rewrite invr0 mulr0.
by rewrite ler_pdivrMr ?lt_def ?Pv//=; exact: ip0normrcP.
Qed.

Lemma ipnormrcP p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnormrc p (A *m v) <= ipqnormrc p p A * lpnormrc p v.
Proof.
case E: (p < 1).
  by rewrite lpnormrc_plt1E// ipqnormrc_pqlt1E// ip0normrcP.
by apply/ipqnormrcP_pqge1; rewrite lexx leNgt E.
Qed.

Lemma ipnormrcPV p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnormrc p (A *m v) / lpnormrc p v <= ipqnormrc p p A.
Proof.
have [/eqP ->| Pv ] := boolP (lpnormrc p v == 0).
  by rewrite invr0 mulr0.
by rewrite ler_pdivrMr ?lt_def ?Pv//=; exact: ipnormrcP.
Qed.

Lemma ipqnormrc_exist p q m n (A : 'M[C]_(m,n)) :
  exists v : 'cV[C]_n, lpnormrc q (A *m v) / lpnormrc p v = ipqnormrc p q A.
Proof.
rewrite ipqnormrc.unlock; set S := _ |` _.
suff P1 : compact S.
have P2 : S !=set0 by exists 0; left.
move: (compact_max P1 P2)=>[x Px1 Px2].
have ->: sup S = x.
  apply/le_anti/andP; split.
  apply/sup_least_ubound=>//; apply/ipqnormrc_set_has_sup.
  apply/sup_upper_bound=>//; apply/ipqnormrc_set_has_sup.
move: Px1; rewrite /S/==>[[->|[v [Pv1 Pv2]]]].
  by exists 0; rewrite lpnormrc0 invr0 mulr0.
  by exists v; rewrite Pv1 divr1.
apply/compactU; first by apply/compact_set1.
rewrite (_ : mkset _ = (@lpnormrc R C q m 1) @` ((fun x => A *m x) @` 
  [set x : 'M[C]_(n,1) | r2c_lpnormrc_vnorm C p n 1 x = 1])).
apply/continuous_compact.
  by apply/continuous_subspaceT/lpnormrc_continuous.
apply/continuous_compact; last by apply/compact_mnorm_sphere.
by apply/continuous_subspaceT/mxlinear_continuous=>a x y; rewrite linearP.
apply/seteqP; split=>[x /= [v [Pv1 Pv2]] | x /= [? [v Pv1 <- <-]]].
  by exists (A *m v)=>//; exists v=>//; rewrite Pv1 r2c1.
by exists v; split=>//; rewrite -[LHS](@r2cK R C) Pv1 c2r1.
Qed.

Lemma ipqnormrc_triangle p q m n (A B : 'M[C]_(m,n)) :
  ipqnormrc p q (A + B) <= ipqnormrc p q A + ipqnormrc p q B.
Proof.
move: (ipqnormrc_exist p q (A + B))=>[v <-].
apply: (le_trans _ (lerD (ipqnormrcPV _ _ A v) (ipqnormrcPV _ _ B v))).
by rewrite -mulrDl ler_wpM2r// ?invr_ge0// mulmxDl lpnormrc_triangle.
Qed.

Lemma ipqnormrc0_eq0 p q m n (A : 'M[C]_(m,n)) :
  ipqnormrc p q A = 0 -> A = 0.
Proof.
move=>P1; suff P i : col i A == 0.
  by apply/matrixP=>i j; move: (P j)=>/eqP/matrixP/(_ i 0); rewrite !mxE.
move: (ipqnormrcP p q A (delta_mx i (0 : 'I_1))).
by rewrite -colE P1 mul0r le_eqVlt ltNge lpnormrc_ge0/= orbF lpnormrc_eq0.
Qed.

Lemma ipqnormrcZ p q m n a (A : 'M[C]_(m,n)) : 
  ipqnormrc p q (a *: A) = ``|a| * ipqnormrc p q A.
Proof.
apply/le_anti/andP; split.
  move: (ipqnormrc_exist p q (a *: A))=>[v <-].
  by rewrite -scalemxAl lpnormrcZ -mulrA ler_wpM2l// ipqnormrcPV.
by move: (ipqnormrc_exist p q A)=>[v <-]; 
  rewrite mulrA -lpnormrcZ scalemxAl ipqnormrcPV.
Qed.

Lemma ipqnormrc0 p q m n : ipqnormrc p q (0 : 'M[C]_(m,n)) = 0.
Proof.
move: (ipqnormrc_exist p q (0 : 'M[C]_(m,n)))=>[v <-].
by rewrite mul0mx lpnormrc0 mul0r.
Qed.

Lemma ipqnormrc0P p q m n (A : 'M[C]_(m,n)) :
  reflect (ipqnormrc p q A = 0) (A == 0).
Proof. by apply: (iffP eqP)=> [->|/ipqnormrc0_eq0 //]; apply: ipqnormrc0. Qed.

Definition ipqnormrc_eq0 p q m n (A : 'M[C]_(m,n)) := 
  sameP (ipqnormrc p q A =P 0) (ipqnormrc0P p q A).

Lemma ipqnormrcM p q r m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) :
  ipqnormrc p q (A *m B) <= ipqnormrc r q A * ipqnormrc p r B.
Proof.
move: (ipqnormrc_exist p q (A *m B))=>[v <-].
have [/eqP ->| Pv] := boolP (lpnormrc p v == 0).
  by rewrite invr0 mulr0 mulr_ge0.
rewrite -mulmxA ler_pdivrMr ?lt_def ?Pv//=.
by apply/(le_trans (ipqnormrcP r q _ _)); rewrite -mulrA ler_wpM2l// ipqnormrcP.
Qed.

Lemma ipqnormrc_delta p q m n (i : 'I_m) (j : 'I_n) :
  ipqnormrc p q (delta_mx i j : 'M[C]_(m,n)) = 1.
Proof.
apply/le_anti/andP; split; last first.
  move: (ipqnormrcP p q (delta_mx i j : 'M[C]_(m,n)) (delta_mx j 0)).
  by rewrite mul_delta_mx !lpnormrc_delta mulr1.
move: (ipqnormrc_exist p q (delta_mx i j : 'M[C]_(m,n)))=>[v <-].
have [/eqP ->| Pv ] := boolP (lpnormrc p v == 0).
  by rewrite invr0 mulr0.
rewrite ler_pdivrMr ?lt_def ?Pv//= mul1r.
have ->: delta_mx i j *m v = v j 0 *: delta_mx i 0.
  apply/matrixP=>k l; rewrite !mxE ord1 eqxx (bigD1 j)//= big1.
  by rewrite mxE eqxx !andbT addr0 mulrC.
  by move=>t /negPf Pt; rewrite mxE Pt andbF mul0r.
rewrite lpnormrcZ lpnormrc_delta mulr1.
by apply/(le_trans _ (lpnormrc_row_le _ _ j)); rewrite lpnormrc11 mxE.
Qed.

Lemma ipqnormrc_col_perm p q m n s (A : 'M[C]_(m,n)) :
  ipqnormrc p q (col_perm s A) = ipqnormrc p q A.
Proof.
apply/le_anti/andP; split.
  move: (ipqnormrc_exist p q (col_perm s A))=>[v <-].
  by rewrite mul_col_perm -[lpnormrc p v](lpnormrc_row_perm _ (s^-1)%g) ipqnormrcPV.
move: (ipqnormrc_exist p q A)=>[v <-].
have -> : A *m v = col_perm s A *m row_perm s v.
  by rewrite mul_col_perm -row_permM mulVg row_perm1.
by rewrite -[lpnormrc p v](lpnormrc_row_perm _ s) ipqnormrcPV.
Qed.

Lemma ipqnormrc_row_perm p q m n s (A : 'M[C]_(m,n)) :
  ipqnormrc p q (row_perm s A) = ipqnormrc p q A.
Proof.
apply/le_anti/andP; split.
  move: (ipqnormrc_exist p q (row_perm s A))=>[v <-].
  by rewrite row_permE -mulmxA lpnormrc_permMl ipqnormrcPV.
move: (ipqnormrc_exist p q A)=>[v <-].
by rewrite -(lpnormrc_row_perm _ s) row_permE mulmxA -row_permE ipqnormrcPV.
Qed.

Lemma ipqnormrc_permMl p q m n s (A : 'M[C]_(m,n)) :
  ipqnormrc p q (perm_mx s *m A) = ipqnormrc p q A.
Proof. by rewrite -row_permE ipqnormrc_row_perm. Qed.

Lemma ipqnormrc_permMr p q m n s (A : 'M[C]_(m,n)) :
  ipqnormrc p q (A *m perm_mx s) = ipqnormrc p q A.
Proof. by rewrite col_permEV ipqnormrc_col_perm. Qed.

Lemma ipqnormrc_castmx p q m n m' n' (eqmn : (m = m') * (n = n')) (A : 'M[C]_(m,n)) :
  ipqnormrc p q (castmx eqmn A) = ipqnormrc p q A.
Proof. by rewrite castmx_funE. Qed.

Lemma ipqnormrc_row0mx p q m n r (A : 'M[C]_(m,r)) : 
  ipqnormrc p q (row_mx (0 : 'M_(m,n)) A) = ipqnormrc p q A.
Proof.
apply/le_anti/andP; split; last first.
  move: (ipqnormrc_exist p q A)=>[v <-].
  apply/(le_trans _ (ipqnormrcPV p q _ (col_mx 0 v))).
  by rewrite lpnormrc_col0mx mul_row_col mulmx0 add0r.
move: (ipqnormrc_exist p q (row_mx (0 : 'M_(m,n)) A))=>[v <-].
have [/eqP ->| Pv ] := boolP (lpnormrc p v == 0).
  by rewrite invr0 mulr0.
rewrite ler_pdivrMr ?lt_def ?Pv//= -[v]vsubmxK mul_row_col mul0mx add0r.
apply/(le_trans (ipqnormrcP p q _ _)).
by rewrite ler_wpM2l// lpnormrc_colmxr_le.
Qed.

Lemma ipqnormrc_rowmx0 p q m n r (A : 'M[C]_(m,n)) : 
  ipqnormrc p q (row_mx A (0 : 'M_(m,r))) = ipqnormrc p q A.
Proof. by rewrite row_mx_perm castmx_funE ipqnormrc_permMr ipqnormrc_row0mx. Qed.

Lemma ipqnormrc_col0mx p q m n r (A : 'M[C]_(n,r)) : 
  ipqnormrc p q (col_mx (0 : 'M_(m,r)) A) = ipqnormrc p q A.
Proof.
apply/le_anti/andP; split; last first.
  move: (ipqnormrc_exist p q A)=>[v <-].
  apply/(le_trans _ (ipqnormrcPV p q _ v)).
  by rewrite mul_col_mx mul0mx lpnormrc_col0mx.
move: (ipqnormrc_exist p q (col_mx (0 : 'M_(m,r)) A))=>[v <-].
by rewrite mul_col_mx mul0mx lpnormrc_col0mx ipqnormrcPV.
Qed.

Lemma ipqnormrc_colmx0 p q m n r (A : 'M[C]_(m,r)) : 
  ipqnormrc p q (col_mx A (0 : 'M_(n,r))) = ipqnormrc p q A.
Proof. by rewrite col_mx_perm castmx_funE ipqnormrc_permMl ipqnormrc_col0mx. Qed.

Lemma ipqnormrc_diag p q m (v : 'rV[C]_m) :
  lpnormrc 0 v <= ipqnormrc p q (diag_mx v).
Proof.
rewrite lpnormrc.unlock ltr01.
apply/bigmax_leP; split=>//= [[? i]] _; rewrite /= ord1.
suff -> : ``|v 0 i| = lpnormrc q (diag_mx v *m (delta_mx i 0 : 'cV_m)) 
                    / lpnormrc p (delta_mx i 0 : 'cV[C]_m).
    apply/ipqnormrcPV.
rewrite lpnormrc_delta divr1.
have ->: diag_mx v *m (delta_mx i 0 : 'cV_m) = v 0 i *: delta_mx i 0.
  by apply/matrixP=>? j; rewrite diag_mx_deltaM.
by rewrite lpnormrcZ lpnormrc_delta mulr1.
Qed.

Lemma ipnormrc_diag p m (v : 'rV[C]_m) :
  ipqnormrc p p (diag_mx v) = lpnormrc 0 v.
Proof.
apply/le_anti/andP; split; last by apply/ipqnormrc_diag.
move: (ipqnormrc_exist p p (diag_mx v))=>[u <-].
have [->|/eqP Pu] := @eqP _ (lpnormrc p u) 0.
  by rewrite invr0 mulr0.
rewrite ler_pdivrMr ?lt_def ?Pu//= lpnormrc.unlock ltr01.
case: ltP=>Pp.
  under eq_bigr do rewrite mul_diag_mx mxE.
  apply/bigmax_leP; split=>/=[|[i ?] _].
    by rewrite mulr_ge0//; apply/bigmax_geP; left.
  rewrite /= ord1 normrcM ler_pM//.
    by apply/bigmax_geP; right; exists (0,i).
  by apply/bigmax_geP; right; exists (i,0).
rewrite -[X in X * _](powRrK (r := p)); 
  last by rewrite gt_eqF// (lt_le_trans ltr01 Pp).
rewrite -powRM// ?sumr_ge0// ge0_ler_powR// ?nnegrE ?mulr_ge0// ?sumr_ge0//.
  by rewrite ?invr_ge0 (le_trans ler01 Pp).
rewrite mulr_sumr ler_sum//==>[[i ? _]].
rewrite ord1/= -powRM// ?ge0_ler_powR// ?nnegrE// ?mulr_ge0//.
  by rewrite  (le_trans ler01 Pp).
  1,3,4: by apply/bigmax_geP; left.
rewrite mul_diag_mx mxE normrcM ler_pM//.
by apply/bigmax_geP; right; exists (0,i).
Qed.

(* Lemma ipqnormrc_const p q m n (c : C) :
  ipqnormrc p q (const_mx c : 'M[C]_(m,n)) = 
    (m%:R `^ q^-1 * n%:R `^ (1-p^-1)) * ``|c|. *)

Lemma ipnormrc_scale p m (c : C) :
  ipqnormrc p p (c%:M : 'M[C]_m) = ``| c | * (m != 0)%:R.
Proof. by rewrite -diag_const_mx ipnormrc_diag lpnormrc_const_plt1. Qed.

Lemma ipnormrc1 p m : ipqnormrc p p (1%:M : 'M[C]_m) = (m != 0)%:R.
Proof. by rewrite ipnormrc_scale normrc1 mul1r. Qed.

Lemma ipqnormrc11 p q (A : 'M[C]_1) :
  ipqnormrc p q A = ``|A 0 0|.
Proof.
apply/le_anti/andP; split.
  move: (ipqnormrc_exist p q A)=>[v <-].
  rewrite !lpnormrc11 mxE big_ord1 normrcM.
  have [/eqP->|Pv] := boolP (``|v 0 0| == 0).
    by rewrite mulr0 mul0r.
  by rewrite mulfK.
have ->: ``|A 0 0| = lpnormrc q (A *m 1%:M) / lpnormrc p (1%:M : 'M[C]_1).
  by rewrite mulmx1 !lpnormrc11 mxE eqxx normrc1 divr1.
apply/ipqnormrcPV.
Qed.

Lemma ipqnormrc_rowmxl_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  ipqnormrc p q A <= ipqnormrc p q (row_mx A B).
Proof.
move: (ipqnormrc_exist p q A)=>[v <-].
apply/(le_trans _ (ipqnormrcPV p q _ (col_mx v 0))).
by rewrite lpnormrc_colmx0 mul_row_col mulmx0 addr0.
Qed.

Lemma ipqnormrc_rowmxr_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  ipqnormrc p q B <= ipqnormrc p q (row_mx A B).
Proof.
move: (ipqnormrc_exist p q B)=>[v <-].
apply/(le_trans _ (ipqnormrcPV p q _ (col_mx 0 v))).
by rewrite lpnormrc_col0mx mul_row_col mulmx0 add0r.
Qed.

Lemma ipqnormrc_colmxl_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  ipqnormrc p q A <= ipqnormrc p q (col_mx A B).
Proof.
move: (ipqnormrc_exist p q A)=>[v <-].
apply/(le_trans _ (ipqnormrcPV p q _ v)).
by rewrite ler_wpM2r// ?invr_ge0// mul_col_mx lpnormrc_colmxl_le.
Qed.

Lemma ipqnormrc_colmxr_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  ipqnormrc p q B <= ipqnormrc p q (col_mx A B).
Proof.
move: (ipqnormrc_exist p q B)=>[v <-].
apply/(le_trans _ (ipqnormrcPV p q _ v)).
by rewrite ler_wpM2r// ?invr_ge0// mul_col_mx lpnormrc_colmxr_le.
Qed.

Lemma ipqnormrc_col_le p q m n (A : 'M[C]_(m,n)) i :
  ipqnormrc p q (col i A) <= ipqnormrc p q A.
Proof.
move: (ipqnormrc_exist p q (col i A))=>[v <-].
apply/(le_trans _ (ipqnormrcPV p q _ (`|v 0 0| *: delta_mx i 0))).
rewrite lpnormrcZ normrc_idV lpnormrc_delta mulr1 lpnormrc11.
rewrite ler_wpM2r// ?invr_ge0// -scalemxAr.
by rewrite {1}[v]mx11_scalar mul_mx_scalar !lpnormrcZ colE normrc_idV.
Qed.

Lemma ipqnormrc_row_le p q m n (A : 'M[C]_(m,n)) i :
  ipqnormrc p q (row i A) <= ipqnormrc p q A.
Proof.
move: (ipqnormrc_exist p q (row i A))=>[v <-].
apply/(le_trans _ (ipqnormrcPV p q _ v)).
by rewrite ler_wpM2r// ?invr_ge0// -row_mul lpnormrc_row_le.
Qed.

Lemma ipqnormrc_tens p q m n l k (A : 'M[C]_(m,n)) (B : 'M_(l,k)) :
  ipqnormrc p q A * ipqnormrc p q B <= ipqnormrc p q (A *t B).
Proof.
move: (ipqnormrc_exist p q A) (ipqnormrc_exist p q B)=>[u <-] [v <-].
by rewrite mulrACA -invfM -!lpnormrc_tens -tensmx_mul; apply/ipqnormrcPV.
Qed.

Lemma ipqnormrc_swap p q m n l k (A : 'M[C]_(m * n, l * k)) : 
  ipqnormrc p q (mxswap A) = ipqnormrc p q A.
Proof. by rewrite mxswap_permE ipqnormrc_row_perm ipqnormrc_col_perm ipqnormrc_castmx. Qed.

End induced_normrc.

#[global] Hint Extern 0 (is_true (0 <= ipqnormrc _ _ _)) => apply: ipqnormrc_ge0 : core.

HB.lock
Definition ipqnorm (R : realType) (p q : R) m n (A : 'M[R[i]]_(m,n)) 
  := (ipqnormrc p q A)%:C.

Notation "\i_ ( p , q ) | M |" := (ipqnorm p q M) : ring_scope.
Notation ipnorm p := (ipqnorm p p).
Notation "\i_ ( p ) | M |" := (ipqnorm p p M) : ring_scope.
Notation "\i_ p | M |" := (ipnorm p M) : ring_scope.
Notation i2norm := (ipqnorm 2 2).
Notation "'\i2|' M |" := (i2norm M) : ring_scope.

Section ipqnorm.
Variable (R : realType).
Local Notation C := R[i].
Implicit Type (p q r : R) (m n l : nat).

Section basic_properties.
Variable (p q : R) (m n : nat).
Local Notation "`[ x ]" := (@ipqnorm R p q m n x).

Lemma ipqnorm_triangle (A B : 'M[C]_(m,n)) :
  `[ A + B ] <= `[ A ] + `[ B ].
Proof. by rewrite ipqnorm.unlock -realcD lecR ipqnormrc_triangle. Qed.
Definition ler_ipqnormD := ipqnorm_triangle.

Lemma ipqnorm0_eq0 (A : 'M[C]_(m,n)) :
  `[ A ] = 0 -> A = 0.
Proof. by rewrite ipqnorm.unlock=>/(f_equal (@complex.Re _))/=/ipqnormrc0_eq0. Qed.

Lemma ipqnormZ a (A : 'M[C]_(m,n)) : 
  `[ a *: A ] = `|a| * `[ A ].
Proof. by rewrite ipqnorm.unlock ipqnormrcZ realcM normrcE. Qed.

HB.instance Definition _ := isVNorm.Build C 'M[C]_(m, n) 
  (@ipqnorm R p q m n) ipqnorm_triangle ipqnorm0_eq0 ipqnormZ.

Lemma ipqnorm0 : `[ 0 : 'M[C]_(m,n) ] = 0.
Proof. exact: normv0. Qed.

Lemma ipqnorm0P A : reflect (`[ A ] = 0) (A == 0).
Proof. exact: normv0P. Qed.

Definition ipqnorm_eq0 A := sameP (`[ A ] =P 0) (ipqnorm0P A).

Lemma ipqnormMn A : `[ A *+ n] = `[ A ] *+ n.
Proof. exact: normvMn. Qed.

Lemma ipqnormN A : `[ - A ] = `[ A ].
Proof. exact: normvN. Qed.

Lemma ipqnorm_ge0 A : `[ A ] >= 0.
Proof. exact: normv_ge0. Qed.

Lemma ipqnorm_nneg A : `[ A ] \is Num.nneg.
Proof. exact: normv_nneg. Qed.

Lemma ipqnorm_real A : `[ A ] \is Num.real.
Proof. exact: normv_real. Qed.

Lemma ipqnorm_gt0 A : `[ A ] > 0 = (A != 0).
Proof. exact: normv_gt0. Qed.

Lemma ler_ipqnormB A B : `[A - B] <= `[A] + `[B].
Proof. exact: lev_normB. Qed.

Lemma ler_ipqdistD A B C : `[B-C] <= `[B-A] + `[A-C].
Proof. exact: lev_distD. Qed.

Lemma ipqdistC A B : `[ A - B ] = `[ B - A ].
Proof. exact: distvC. Qed.

Lemma lerB_ipqnormD A B : `[A] - `[B] <= `[A + B].
Proof. exact: levB_normD. Qed.

Lemma lerB_ipqdist A B : `[A] - `[B] <= `[A - B].
Proof. exact: levB_dist. Qed.

Lemma ler_dist_ipqdist A B : `| `[A] - `[B] | <= `[A - B].
Proof. exact: lev_dist_dist. Qed.

Lemma ler_ipqnorm_sum I (r : seq I) (P: pred I) (f : I -> 'M[C]_(m,n)) :
  `[ \sum_(i <- r | P i) f i ] <= \sum_(i <- r | P i) `[ f i ].
Proof. exact: normv_sum. Qed.

Lemma ipqnorm_id A : `| `[A] | = `[A].
Proof. exact: normv_id. Qed.

Lemma ipqnorm_le0 A : `[A] <= 0 = (A == 0).
Proof. exact: normv_le0. Qed.

Lemma ipqnorm_lt0 A : `[A] < 0 = false.
Proof. exact: normv_lt0. Qed.

End basic_properties.

#[local] Hint Extern 0 (is_true (0 <= ipqnorm _ _ _)) => apply: ipqnorm_ge0 : core.

Section inherited.

Lemma ipqnorm_plt1E p q : 
  p < 1 -> @ipqnorm R p q = ipqnorm 0 q.
Proof. by move=>Pp; rewrite ipqnorm.unlock ipqnormrc_plt1E. Qed.

Lemma ipqnorm_qlt1E p q : 
  q < 1 -> @ipqnorm R p q = ipqnorm p 0.
Proof. by move=>Pp; rewrite ipqnorm.unlock ipqnormrc_qlt1E. Qed.

Lemma ipqnorm_pqlt1E p q : 
  p < 1 -> q < 1 -> @ipqnorm R p q = ipqnorm 0 0.
Proof. by move=>Pp Pq; rewrite ipqnorm.unlock ipqnormrc_pqlt1E. Qed.

Lemma ipqnormP p q m n (A : 'M[C]_(m,n)) (v : 'cV[C]_n) :
  lpnorm q (A *m v) <= ipqnorm p q A * lpnorm p v.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock -realcM lecR ipqnormrcP. Qed.

Lemma ipqnormPV p q m n (A : 'M[C]_(m,n)) (v : 'cV[C]_n) :
  lpnorm q (A *m v) / lpnorm p v <= ipqnorm p q A.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock -realcI -realcM lecR ipqnormrcPV. Qed.

Lemma ipqnormP_pqge1 p q m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  1 <= p <= q -> lpnorm q (A *m v) <= ipqnorm p q A * lpnorm p v.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock -realcM lecR; exact: ipqnormrcP_pqge1. Qed.

Lemma ipqnormPV_pqge1 p q m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  1 <= p <= q -> lpnorm q (A *m v) / lpnorm p v <= ipqnorm p q A.
Proof. rewrite lpnorm.unlock ipqnorm.unlock -realcI -realcM lecR; exact: ipqnormrcPV_pqge1. Qed.

Lemma ip0normP p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnorm 0 (A *m v) <= ipqnorm p 0 A * lpnorm p v.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock -realcM lecR; exact: ip0normrcP. Qed.

Lemma ip0normPV p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnorm 0 (A *m v) / lpnorm p v <= ipqnorm p 0 A.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock -realcI -realcM lecR; exact: ip0normrcPV. Qed.

Lemma ipnormP p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnorm p (A *m v) <= ipqnorm p p A * lpnorm p v.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock -realcM lecR ipnormrcP. Qed.

Lemma ipnormPV p m n l (A : 'M[C]_(m,n)) (v : 'M[C]_(n,l)) :
  lpnorm p (A *m v) / lpnorm p v <= ipqnorm p p A.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock -realcI -realcM lecR ipnormrcPV. Qed.

Lemma ipqnorm_exist p q m n (A : 'M[C]_(m,n)) :
  exists v : 'cV[C]_n, lpnorm q (A *m v) / lpnorm p v = ipqnorm p q A.
Proof.
move: (ipqnormrc_exist p q A)=>[v Pv]; 
by exists v; rewrite lpnorm.unlock ipqnorm.unlock -realcI -realcM Pv.
Qed.
Definition ipnorm_exist p := ipqnorm_exist p p.

Lemma ipqnorm_col_perm p q m n s (A : 'M[C]_(m,n)) :
  ipqnorm p q (col_perm s A) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_col_perm. Qed.

Lemma ipqnorm_row_perm p q m n s (A : 'M[C]_(m,n)) :
  ipqnorm p q (row_perm s A) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_row_perm. Qed.

Lemma ipqnorm_permMl p q m n s (A : 'M[C]_(m,n)) :
  ipqnorm p q (perm_mx s *m A) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_permMl. Qed.

Lemma ipqnorm_permMr p q m n s (A : 'M[C]_(m,n)) :
  ipqnorm p q (A *m perm_mx s) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_permMr. Qed.

Lemma ipqnormM p q r m n l (A : 'M[C]_(m,n)) (B : 'M[C]_(n,l)) :
  ipqnorm p q (A *m B) <= ipqnorm r q A * ipqnorm p r B.
Proof. by rewrite ipqnorm.unlock -realcM lecR; exact: ipqnormrcM. Qed.
Definition ipnormM p := ipqnormM p p p.

Lemma ipqnorm_castmx p q m n m' n' (eqmn : (m = m') * (n = n')) (A : 'M[C]_(m,n)) :
  ipqnorm p q (castmx eqmn A) = ipqnorm p q A.
Proof. by rewrite castmx_funE. Qed.

Lemma ipqnorm_row0mx p q m n l (A : 'M[C]_(m,l)) : 
  ipqnorm p q (row_mx (0 : 'M_(m,n)) A) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_row0mx. Qed.

Lemma ipqnorm_rowmx0 p q m n l (A : 'M[C]_(m,n)) : 
  ipqnorm p q (row_mx A (0 : 'M_(m,l))) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_rowmx0. Qed.

Lemma ipqnorm_col0mx p q m n l (A : 'M[C]_(n,l)) : 
  ipqnorm p q (col_mx (0 : 'M_(m,l)) A) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_col0mx. Qed.

Lemma ipqnorm_colmx0 p q m n l (A : 'M[C]_(m,l)) : 
  ipqnorm p q (col_mx A (0 : 'M_(n,l))) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_colmx0. Qed.

Lemma ipqnorm_diag p q m (v : 'rV[C]_m) :
  lpnorm 0 v <= ipqnorm p q (diag_mx v).
Proof. by rewrite lpnorm.unlock ipqnorm.unlock lecR ipqnormrc_diag. Qed.

Lemma ipnorm_diag p m (v : 'rV[C]_m) :
  ipqnorm p p (diag_mx v) = lpnorm 0 v.
Proof. by rewrite lpnorm.unlock ipqnorm.unlock ipnormrc_diag. Qed.

Lemma ipnorm_cdiag p m n (v : 'rV[C]_(minn m n)) :
  ipqnorm p p (cdiag_mx v) = lpnorm 0 v.
Proof.
by rewrite /cdiag_mx ipqnorm_castmx /block_mx 
  row_mx0 ipqnorm_colmx0 ipqnorm_rowmx0 ipnorm_diag.
Qed.

Lemma ipnorm_scale p m (c : C) :
  ipqnorm p p (c%:M : 'M[C]_m) = `| c | * (m != 0)%:R.
Proof. by rewrite ipqnorm.unlock ipnormrc_scale realcM normrcE natrC. Qed.

Lemma ipnorm1 p m : ipqnorm p p (1%:M : 'M[C]_m) = (m != 0)%:R.
Proof. by rewrite ipnorm_scale normr1 mul1r. Qed.

Lemma ipqnorm11 p q (A : 'M[C]_1) :
  ipqnorm p q A = `|A 0 0|.
Proof. by rewrite ipqnorm.unlock ipqnormrc11 normrcE. Qed.
Definition ipnorm11 p := (ipqnorm11 p p).

Lemma ipqnorm_rowmxl_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  ipqnorm p q A <= ipqnorm p q (row_mx A B).
Proof. by rewrite ipqnorm.unlock lecR ipqnormrc_rowmxl_le. Qed.

Lemma ipqnorm_rowmxr_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(m,l)) :
  ipqnorm p q B <= ipqnorm p q (row_mx A B).
Proof. by rewrite ipqnorm.unlock lecR ipqnormrc_rowmxr_le. Qed.

Lemma ipqnorm_colmxl_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  ipqnorm p q A <= ipqnorm p q (col_mx A B).
Proof. by rewrite ipqnorm.unlock lecR ipqnormrc_colmxl_le. Qed.

Lemma ipqnorm_colmxr_le p q m n l (A : 'M[C]_(m,n)) (B : 'M_(l,n)) :
  ipqnorm p q B <= ipqnorm p q (col_mx A B).
Proof. by rewrite ipqnorm.unlock lecR ipqnormrc_colmxr_le. Qed.

Lemma ipqnorm_col_le p q m n (A : 'M[C]_(m,n)) i :
  ipqnorm p q (col i A) <= ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock lecR ipqnormrc_col_le. Qed.

Lemma ipqnorm_row_le p q m n (A : 'M[C]_(m,n)) i :
  ipqnorm p q (row i A) <= ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock lecR ipqnormrc_row_le. Qed.

Lemma ipqnorm_tens p q m n l k (A : 'M[C]_(m,n)) (B : 'M_(l,k)) :
  ipqnorm p q A * ipqnorm p q B <= ipqnorm p q (A *t B).
Proof. by rewrite ipqnorm.unlock -realcM lecR ipqnormrc_tens. Qed.

Lemma ipqnorm_swap p q m n l k (A : 'M[C]_(m * n, l * k)) : 
  ipqnorm p q (mxswap A) = ipqnorm p q A.
Proof. by rewrite ipqnorm.unlock ipqnormrc_swap. Qed.

End inherited.

Lemma i1normE m n (A : 'M[C]_(m,n)) :
  ipnorm 1 A = \big[maxr/0]_i l1norm (col i A).
Proof.
rewrite ipqnorm.unlock lpnorm.unlock bigmax_r2c; f_equal.
apply/le_anti/andP; split; last first.
  apply/bigmax_leP; split=>//= i _.
  rewrite colE; apply/(le_trans (ipqnormrcP 1 1 _ _)).
  by rewrite lpnormrc_delta mulr1.
move: (ipqnormrc_exist 1 1 A)=>[v <-].
have [/eqP ->|Pv] := boolP (lpnormrc 1 v == 0).
  by rewrite invr0 mulr0; apply/bigmax_geP; left.
rewrite ler_pdivrMr ?lt_def ?Pv//= lpnormrc.unlock ltxx invr1 !powRr1 ?sumr_ge0//.
rewrite !pair_bigV/= exchange_big/= big_ord1 exchange_big/= big_ord1.
under eq_bigr do rewrite mxE (powRr1 (normrc_ge0 _)).
apply: (le_trans (y := \sum_i\sum_j ``|A i j| * ``|v j 0|)).
  by apply/ler_sum=>i _; apply/(le_trans (ler_normrc_sum _ _ _));
  apply/ler_sum=>j _; rewrite normrcM.
rewrite exchange_big/= mulr_sumr; apply/ler_sum=>i _.
rewrite powRr1// -mulr_suml ler_wpM2r//.
apply/bigmax_geP; right; exists i=>//.
rewrite powRr1 ?sumr_ge0// pair_bigV/= exchange_big/= big_ord1 ler_sum// =>j _.
by rewrite mxE powRr1.
Qed.

Lemma col_tens m n l k (A : 'M[C]_(m,n)) (B : 'M_(l,k)) i :
  col i (A *t B) = col (mxtens_unindex i).1 A *t col (mxtens_unindex i).2 B.
Proof.
case: (mxtens_indexP i)=>a b; rewrite !mxtens_indexK/= tensvE.
apply/matrixP=>j ?; rewrite ord1 castmxE/= cast_ord_id mxtens_1index.
by case: (mxtens_indexP j)=>c d; rewrite mxE !tensmxE !mxE.
Qed.

Lemma row_tens m n l k (A : 'M[C]_(m,n)) (B : 'M_(l,k)) i :
  row i (A *t B) = row (mxtens_unindex i).1 A *t row (mxtens_unindex i).2 B.
Proof.
case: (mxtens_indexP i)=>a b; rewrite !mxtens_indexK/= tensvE.
apply/matrixP=>? j; rewrite ord1 castmxE/= cast_ord_id mxtens_1index.
by case: (mxtens_indexP j)=>c d; rewrite mxE !tensmxE !mxE.
Qed.

Lemma i1norm_tens m n l k (A : 'M[C]_(m,n)) (B : 'M_(l,k)) :
  ipnorm 1 (A *t B) = ipnorm 1 A * ipnorm 1 B.
Proof.
rewrite !i1normE lpnorm.unlock !bigmax_r2c -realcM; f_equal.
apply/le_anti/andP; split.
  apply/bigmax_leP; split=>[|/= i _].
    by apply/mulr_ge0; apply/bigmax_geP; left.
  case: (mxtens_indexP i)=>[a b].
  rewrite col_tens tensvE castmx_funE lpnormrc_tens mxtens_indexK/=.
  by apply ler_pM=>//; apply/bigmax_geP; right; [exists a | exists b].
set x := \big[maxr/0]_i lpnormrc 1 (col i A).
have [/eqP ->| Px ] := boolP (x == 0).
  by rewrite mul0r; apply/bigmax_geP; left.
have Px0 : 0 < x by rewrite lt_neqAle eq_sym Px/=; apply/bigmax_geP; left.
rewrite -ler_pdivlMl//; apply/bigmax_leP; split=>[|/= i _].
  apply/mulr_ge0; first by rewrite invr_ge0 ltW.
  by apply/bigmax_geP; left.
rewrite ler_pdivlMl//.
have [/eqP ->| P1 ] := boolP (lpnormrc 1 (col i B) == 0).
  by rewrite mulr0; apply/bigmax_geP; left.
have P2 : 0 < lpnormrc 1 (col i B) by rewrite lt_neqAle eq_sym P1/=.
rewrite -ler_pdivlMr//; apply/bigmax_leP; split=>[|/= j _].
  by rewrite divr_ge0//; apply/bigmax_geP; left.
rewrite ler_pdivlMr//; apply/bigmax_geP; right.
exists (mxtens_index (j,i))=>//;
by rewrite col_tens tensvE castmx_funE mxtens_indexK/= lpnormrc_tens.
Qed.

Lemma i0normE m n (A : 'M[C]_(m,n)) :
  ipnorm 0 A = \big[maxr/0]_i l1norm (row i A).
Proof.
rewrite ipqnorm.unlock lpnorm.unlock bigmax_r2c; f_equal.
apply/le_anti/andP; split; last first.
  apply/bigmax_leP; split=>//= i _.
  case: n A=>[A |n A /=]; first by rewrite !mx_dim0 lpnormrc0 ipqnormrc0.
  move: (ipqnormrcP 0 0 A (\col_j (directc (A i j)) ^-1)).
  have ->: lpnormrc 0 (\col_j (directc (A i j))^-1) = 1.
    rewrite lpnormrc.unlock ltr01; apply/le_anti/andP; split.
      apply/bigmax_leP; split=>//==>[[j k] _];
      by rewrite mxE/= -lecR normrcE normfV directc_norm invr1.
    apply/bigmax_geP; right; exists (0,0)=>//; 
    by rewrite mxE/= -lecR normrcE normfV directc_norm invr1.
  rewrite mulr1; apply/le_trans.
  rewrite lpnormrc.unlock ltxx ltr01 invr1 powRr1 ?sumr_ge0//.
  apply/bigmax_geP; right; exists (i,0)=>//=.
  rewrite mxE pair_bigV/= big_ord1 normrc_sum ?ler_sum// => j _;
  by rewrite ?powRr1// mxE -norm_directcE// mxE normrc_idV.
move: (ipqnormrc_exist 0 0 A)=>[v <-].
have [/eqP ->|Pv] := boolP (lpnormrc 0 v == 0).
  by rewrite invr0 mulr0; apply/bigmax_geP; left.
rewrite ler_pdivrMr ?lt_def ?Pv//= lpnormrc.unlock ltr01 ltxx invr1.
apply/bigmax_leP; split=>[|/=[i j] _].
  by apply/mulr_ge0; apply/bigmax_geP; left.
apply: (le_trans (y := (\sum_k ``|A i k|) * \big[maxr/0]_i0 ``| v i0.1 i0.2 |)).
  rewrite ord1 mxE/= mulr_suml; 
  apply/(le_trans (ler_normrc_sum _ _ _))/ler_sum=>k _.
  by rewrite normrcM ler_wpM2l//; apply/bigmax_geP; right; exists (k,0).
apply/ler_pM.
  by apply/sumr_ge0.
  by apply/bigmax_geP; left.
  apply/bigmax_geP; right; exists i=>//; 
  rewrite powRr1 ?sumr_ge0// pair_bigV/= big_ord1 ler_sum// =>k _; 
  by rewrite powRr1// mxE.
apply/bigmax_leP; split=>[|/=[k l] _]; first by apply/bigmax_geP; left.
by apply/bigmax_geP; right; exists (k,0)=>//; rewrite ord1.
Qed.

Lemma i0norm_tens m n l k (A : 'M[C]_(m,n)) (B : 'M_(l,k)) :
  ipnorm 0 (A *t B) = ipnorm 0 A * ipnorm 0 B.
Proof.
rewrite !i0normE lpnorm.unlock !bigmax_r2c -realcM; f_equal.
apply/le_anti/andP; split.
  apply/bigmax_leP; split=>[|/= i _].
    by apply/mulr_ge0; apply/bigmax_geP; left.
  case: (mxtens_indexP i)=>[a b].
  rewrite row_tens tensvE castmx_funE lpnormrc_tens mxtens_indexK/=.
  by apply ler_pM=>//; apply/bigmax_geP; right; [exists a | exists b].
set x := \big[maxr/0]_i lpnormrc 1 (row i A).
have [/eqP ->| Px ] := boolP (x == 0).
  by rewrite mul0r; apply/bigmax_geP; left.
have Px0 : 0 < x by rewrite lt_neqAle eq_sym Px/=; apply/bigmax_geP; left.
rewrite -ler_pdivlMl//; apply/bigmax_leP; split=>[|/= i _].
  apply/mulr_ge0; first by rewrite invr_ge0 ltW.
  by apply/bigmax_geP; left.
rewrite ler_pdivlMl//.
have [/eqP ->| P1 ] := boolP (lpnormrc 1 (row i B) == 0).
  by rewrite mulr0; apply/bigmax_geP; left.
have P2 : 0 < lpnormrc 1 (row i B) by rewrite lt_neqAle eq_sym P1/=.
rewrite -ler_pdivlMr//; apply/bigmax_leP; split=>[|/= j _].
  by rewrite divr_ge0//; apply/bigmax_geP; left.
rewrite ler_pdivlMr//; apply/bigmax_geP; right.
exists (mxtens_index (j,i))=>//;
by rewrite row_tens tensvE castmx_funE mxtens_indexK/= lpnormrc_tens.
Qed.

Lemma normrc_r2c (x : R) (T : extNumType R) : ``| r2c x : T | = `|x|.
Proof. by rewrite normrc.unlock r2c_norm r2cK. Qed.  

Lemma i20normE m n (A : 'M[C]_(m,n)) :
  ipqnorm 2 0 A = \big[maxr/0]_i l2norm (row i A).
Proof.
rewrite ipqnorm.unlock lpnorm.unlock bigmax_r2c; f_equal.
apply/le_anti/andP; split; last first.
  apply/bigmax_leP; split=>//= i _.
  case: n A=>[A |n A /=]; first by rewrite !mx_dim0 lpnormrc0 ipqnormrc0.
  have [/eqP->| Pi] := boolP (row i A == 0).
    by rewrite lpnormrc0.
  pose sA := \sum_j ``| A i j | `^ 2.
  have PsA : 0 < sA.
    move: Pi; rewrite -(lpnorm_gt0 2) lpnorm.unlock ltc0R 
      lpnormrc.unlock ltrn1/==>/(gt0_powR _ _).
    rewrite sumr_ge0// pair_bigV/= big_ord1; 
    by under eq_bigr do rewrite mxE; apply.
  pose v := \col_j ((A i j)^* / (sA `^ 2^-1)%:C).
  move: (ipqnormrcP 2 0 A v).
  have ->: lpnormrc 2 v = 1.
    rewrite lpnormrc.unlock ltrn1/= pair_bigV/= exchange_big big_ord1/=.
    under eq_bigr do rewrite mxE normrcM (powRM _ (normrc_ge0 _) 
      (normrc_ge0 _)) normrc_conjC normrcV normrc_r2c.
    by rewrite -mulr_suml -/sA ger0_norm// -powR_inv1// -!powRrM 
      mulN1r mulrN mulVf// powR_inv1 ?ltW// mulfV ?gt_eqF// powR1.
  rewrite mulr1; apply/le_trans.
  rewrite lpnormrc.unlock ltrn1/= ltr01.
  apply/bigmax_geP; right; exists (i,0)=>//=.
  rewrite mxE pair_bigV/= big_ord1 normrc_sum ?ler_sum// =>[|j _].
    under eq_bigr do rewrite mxE; rewrite -/sA.
    under eq_bigr do rewrite mxE mulrA -normCK normrcM normrcXn 
      normrc_idV -(powR_mulrn _ (normrc_ge0 _)).
    rewrite -mulr_suml -/sA -realcI normrc_r2c ger0_norm ?invr_ge0// powR12_sqrt.
    rewrite ler_pdivlMr ?sqrtr_gt0// -expr2 sqr_sqrtr//.
    1,2: by rewrite ltW.
  by rewrite mxE mulrA -normCK mulr_ge0// invr_ge0 lec0R.
move: (ipqnormrc_exist 2 0 A)=>[v <-].
have [/eqP ->|Pv] := boolP (lpnormrc 2 v == 0).
  by rewrite invr0 mulr0; apply/bigmax_geP; left.
rewrite ler_pdivrMr ?lt_def ?Pv//= lpnormrc.unlock ltr01 ltrn1/=.
apply/bigmax_leP; split=>[|/=[i j] _].
  by apply/mulr_ge0=>//; apply/bigmax_geP; left.
apply: (le_trans (y := (\sum_k ``|A i k| * ``|v k 0|))).
  rewrite mxE/= ord1; apply/(le_trans (ler_normrc_sum _ _ _));
  by under eq_bigr do rewrite normrcM.
apply/(le_trans (hoelder_fin _ (2 : R) _ _))=>//.
rewrite pair_bigV/= exchange_big/= big_ord1 ler_wpM2r//.
apply/bigmax_geP; right; exists i=>//=.
rewrite pair_bigV/= big_ord1.
by under [in leRHS]eq_bigr do rewrite mxE.
Qed.

Lemma i12normE m n (A : 'M[C]_(m,n)) :
  ipqnorm 1 2 A = \big[maxr/0]_i l2norm (col i A).
Proof.
rewrite ipqnorm.unlock lpnorm.unlock bigmax_r2c; f_equal.
apply/le_anti/andP; split; last first.
  apply/bigmax_leP; split=>//= i _.
  rewrite colE; apply/(le_trans (ipqnormrcP 1 2 _ _)).
  by rewrite lpnormrc_delta mulr1.
move: (ipqnormrc_exist 1 2 A)=>[v <-].
have [/eqP ->|Pv] := boolP (lpnormrc 1 v == 0).
  by rewrite invr0 mulr0; apply/bigmax_geP; left.
rewrite ler_pdivrMr ?lt_def ?Pv//= mulmx_colrow.
apply/(le_trans (y := \sum_i lpnormrc 2 (col i A *m row i v))).
  elim/big_rec2: _ =>/= [|i y1 y2 _ Py]; first by rewrite lpnormrc0.
  by apply/(le_trans (lpnormrc_triangle _ _ _))/lerD.
rewrite {3}lpnormrc.unlock ltxx invr1 powRr1 ?sumr_ge0//
  pair_bigV/= exchange_big/= big_ord1 mulr_sumr.
apply ler_sum=>i _; rewrite powRr1// [row i v]mx11_scalar 
  mxE mul_mx_scalar lpnormrcZ mulrC ler_wpM2r//.
by apply/bigmax_geP; right; exists i.
Qed.

Lemma ipqnorm_conjmx p q m n (A : 'M[C]_(m,n)) :
  ipqnorm p q A^*m = ipqnorm p q A.
Proof.
suff P (B : 'M[C]_(m,n)) : ipqnorm p q B^*m <= ipqnorm p q B.
by apply/le_anti/andP; split=>//; rewrite -{1}[A]conjmxK.
move: (ipqnorm_exist p q B^*m)=>[v <-].
have [/eqP ->|Pv] := boolP (v == 0).
  by rewrite lpnorm0 invr0 mulr0.
rewrite ler_pdivrMr ?lpnorm_gt0// -lpnorm_conjmx conjmxM conjmxK.
by apply/(le_trans (ipqnormP p _ _ _)); rewrite lpnorm_conjmx.
Qed.
Definition ipnorm_conjmx p := ipqnorm_conjmx p p.

Lemma ipqnorm_delta p q m n (i : 'I_m) (j : 'I_n) :
  ipqnorm p q (delta_mx i j : 'M[C]_(m,n)) = 1.
Proof. by rewrite ipqnorm.unlock ipqnormrc_delta. Qed.
Definition ipnorm_delta p := ipqnorm_delta p p.

End ipqnorm.

#[global] Hint Extern 0 (is_true (0 <= ipqnorm _ _ _)) => apply: ipqnorm_ge0 : core.

Lemma bigmax_eq_elem (d : unit) (T : porderType d) (I : eqType) 
  (r : seq I) i0 (P : pred I) (F : I -> T) x : 
    P i0 -> (x <= F i0)%O -> i0 \in r ->
    (forall i, P i -> F i <= F i0)%O ->
      (\big[Order.max/x]_(i <- r| P i) F i)%O = F i0.
Proof.
move=>Pi0 lei0 +H; elim: r=>[//|j r IH]; rewrite inE=>/orP[/eqP<-|].
by rewrite big_cons Pi0 max_l//; apply/bigmax_le.
by rewrite big_cons; case E: (P j)=>///IH IH1; rewrite max_r// IH1; apply H.
Qed.

Lemma bigmax_find (d : unit) (T : porderType d) (I : finType) i0 (P : pred I) 
  (F : I -> T) x : 
  P i0 -> (x <= F i0)%O -> (forall i, P i -> F i <= F i0)%O ->
    (\big[Order.max/x]_(i | P i) F i)%O = F i0.
Proof. by move=>Pi0 lei0 IH; apply: (bigmax_eq_elem Pi0 lei0 _ IH). Qed.
Arguments bigmax_find {d T I} i0 {P F x}.

Section svd_move.
Variable (C : numClosedFieldType).

Definition minnSS_ord0 m n := (cast_ord (esym (minnSS _ _)) (0 : 'I_((minn m n).+1))).
Global Arguments minnSS_ord0 {m n}.

Lemma svd_d_exdr0 m n (D : 'rV[C]_(minn m.+1 n.+1)) :
  svd_d_exdr D 0 0 = D 0 minnSS_ord0.
Proof. 
rewrite /svd_d_exdr castmxE ord1 mxE/= /minnSS_ord0; move: (esym (minnSS m n))=>P1.
move: (esym (min_idr m.+1 n.+1))=>P2; case: (minn m.+1 n.+1) / P1 D P2=>D P2.
have ->: (cast_ord P2 0) = @lshift _ _ 0 by apply/ord_inj.
by case: split_ordP=>// j /lshift_inj<-; f_equal; apply/ord_inj.
Qed.

Lemma max_svd_diag_Sn m n (D : 'rV[C]_(minn m.+1 n.+1)) : D \is svd_diag -> 
  \big[maxr/0%:R]_i (D 0 i) = D 0 minnSS_ord0.
Proof.
move=>PD. apply/bigmax_find=>//[|i _].
by apply/nnegmxP/svd_diag_nneg.
by apply/rv_nincrP=>//=; apply/svd_diag_nincr.
Qed.

End svd_move.

(* frequently used : i2norm, known as spectral norm, schattern oo-norm *)
Section i2norm.
Variable (R : realType).
Implicit Type (m n : nat).
Local Notation C := R[i].

Definition i2norm_ge0 := (ipqnorm_ge0 (R := R) 2 2).
Definition i2norm_nneg := (ipqnorm_nneg (R := R) 2 2).
Definition i2norm_conjmx := (ipqnorm_conjmx (R := R) 2 2).
Definition i2norm_triangle := (ipqnorm_triangle (R := R) 2 2).
Definition ler_i2normD := i2norm_triangle.
Definition i2norm_delta := (ipqnorm_delta (R := R) 2 2).
Definition i2norm0_eq0 := (ipqnorm0_eq0 (R := R) (p := 2) (q := 2)).
Definition i2normZ := (ipqnormZ (R := R) 2 2).
Definition i2norm0 := (ipqnorm0 (R := R) 2 2).
Definition i2norm0P := (ipqnorm0P (R := R) 2 2).
Definition i2norm_eq0 := (ipqnorm_eq0 (R := R) 2 2).
Definition i2norm_exist := (ipqnorm_exist (R := R) 2 2).
Definition i2normPV := (ipnormPV (R := R) 2).
Definition i2norm_dotr := (ipnormP (R := R) 2).
Definition i2normM := (ipnormM (R := R) 2).
Definition i2norm_diag := (ipnorm_diag (R := R) 2).
Definition i2norm_cdiag := (ipnorm_cdiag (R := R) 2).
Definition i2norm_scale := (ipnorm_scale (R := R) 2).
Definition i2norm1 := (ipnorm1 (R := R) 2).
Definition i2norm11 := (ipnorm11 (R := R) 2).
Definition i2norm_col_perm := (ipqnorm_col_perm (R := R) 2 2).
Definition i2norm_row_perm := (ipqnorm_row_perm (R := R) 2 2).
Definition i2norm_permMl := (ipqnorm_permMl (R := R) 2 2).
Definition i2norm_permMr := (ipqnorm_permMr (R := R) 2 2).
Definition i2norm_castmx := (ipqnorm_castmx (R := R) 2 2).
Definition i2norm_row0mx := (ipqnorm_row0mx (R := R) 2 2).
Definition i2norm_rowmx0 := (ipqnorm_rowmx0 (R := R) 2 2).
Definition i2norm_col0mx := (ipqnorm_col0mx (R := R) 2 2).
Definition i2norm_colmx0 := (ipqnorm_colmx0 (R := R) 2 2).
Definition i2norm_rowmxl_le := (ipqnorm_rowmxl_le (R := R) 2 2).
Definition i2norm_rowmxr_le := (ipqnorm_rowmxr_le (R := R) 2 2).
Definition i2norm_colmxl_le := (ipqnorm_colmxl_le (R := R) 2 2).
Definition i2norm_colmxr_le := (ipqnorm_colmxr_le (R := R) 2 2).
Definition i2norm_col_le := (ipqnorm_col_le (R := R) 2 2).
Definition i2norm_row_le := (ipqnorm_row_le (R := R) 2 2).
Definition i2norm_swap := (ipqnorm_swap (R := R) 2 2).

Lemma i2normUl m n (U : 'M[C]_m) (A : 'M[C]_(m,n)) : 
  U \is unitarymx -> i2norm (U *m A) = i2norm A.
Proof.
move=>PU; apply/le_anti/andP; split.
  move: (i2norm_exist (U *m A))=>[v <-].
  by rewrite -mulmxA l2normUl// i2normPV.
move: (i2norm_exist A)=>[v <-].
by apply/(le_trans _ (i2normPV _ v)); rewrite -mulmxA l2normUl.
Qed.

#[local] Lemma i2normUr_temp m n (A : 'M[C]_(m,n)) (U : 'M[C]_n) : 
  U \is unitarymx -> i2norm (A *m U) = i2norm A.
Proof.
move=>PU; apply/le_anti/andP; split.
  move: (i2norm_exist (A *m U))=>[v <-].
  apply/(le_trans _ (i2normPV _ (U *m v))).
  by rewrite l2normUl// mulmxA.
move: (i2norm_exist A)=>[v <-].
apply/(le_trans _ (i2normPV _ (U^*t *m v))).
by rewrite mulmxA mulmxtVK// l2normUl ?adjmx_unitary.
Qed.

Lemma i2normE m n (M : 'M[C]_(m,n)) :
  i2norm M = \big[maxr/0%:R]_i (svd_d M 0 i).
Proof.
case: n M=>[M|n M]; first by rewrite mx_dim0 i2norm0/= big_ord0.
case: m M=>[M|m M].
  have P1: 0%N = minn 0 n.+1 by rewrite minnC.
  by set t := svd_d M; move: t; rewrite -P1/==>t; rewrite big_ord0 mx_dim0 i2norm0.
rewrite {1}(svdE M) i2normUr_temp// i2normUl//.
rewrite /cdiag_mx ipqnorm_castmx /block_mx row_mx0 ipqnorm_colmx0 ipqnorm_rowmx0.
have -> : \big[maxr/0]_i svd_d M 0 i = (\big[maxr/0]_i c2r (svd_d M 0 i))%:C.
  by rewrite -bigmax_r2c; apply eq_bigr=>i _; rewrite c2rK// ger0_real.
rewrite ipqnorm.unlock; f_equal.
apply/le_anti/andP; split; last first.
  apply/bigmax_leP; split=>//= i _.
  apply/(le_trans _ (ipqnormrcPV _ _ _ (delta_mx i 0))).
  rewrite lpnormrc_delta divr1 -colE lpnormrc.unlock ltrn1/= 
    pair_bigV/= exchange_big big_ord1/= (bigD1 i)//= big1=>[|j /negPf Pj].
  by rewrite !mxE eqxx mulr1n addr0 -powRrM mulfV// 
    powRr1// normrc.unlock ler_c2r// ger0_norm.
  by rewrite !mxE Pj mulr0n normrc0 powR0.
move: (ipqnormrc_exist 2 2 (diag_mx (svd_d M)))=>[v <-].
have [/eqP ->|Pv] := boolP (lpnormrc 2 v == 0).
  by rewrite invr0 mulr0; apply/bigmax_geP; left.
rewrite ler_pdivrMr ?lt_def ?Pv//=.
rewrite lpnormrc.unlock ltrn1/= !pair_bigV/= 
  exchange_big/= big_ord1 exchange_big/= big_ord1. 
set c := \big[maxr/0]_(i < minn m.+1 n.+1) c2r (svd_d M 0 i).
apply/(le_trans (y := (\sum_(i < minn m.+1 n.+1) c `^ 2 * ``| v i 0 | `^ 2) `^ 2^-1)).
  rewrite ge0_ler_powR// ?nnegrE ?sumr_ge0// =>[i _|]; first by rewrite mulr_ge0.
  apply ler_sum=>i _; rewrite mxE (bigD1 i)//= big1 =>[|j/negPf Pj];
    last by rewrite mxE eq_sym Pj mulr0n mul0r.
  rewrite !mxE eqxx mulr1n addr0 normrcM powRM// 
    ler_wpM2r// ge0_ler_powR// ?nnegrE// /c.
    by apply/bigmax_geP; left.
  apply/bigmax_geP; right; exists i=>//; 
  by rewrite normrc.unlock ler_c2r// ger0_norm.
rewrite -mulr_sumr powRM// ?sumr_ge0// -powRrM mulfV// powRr1//.
by apply/bigmax_geP; left.
Qed.

Lemma i2norm_adjmx m n (M : 'M[C]_(m,n)) : i2norm (M^*t) = i2norm M.
Proof.
rewrite !i2normE svd_d_adjmx; move: (minnC m n)=>P1.
by case: (minn n m) / P1; under eq_bigr do rewrite castmx_id.
Qed.

Lemma i2norm_trmx m n (M : 'M[C]_(m,n)) : i2norm (M^T) = i2norm M.
Proof.
rewrite !i2normE svd_d_trmx; move: (minnC m n)=>P1.
by case: (minn n m) / P1; under eq_bigr do rewrite castmx_id.
Qed.

Lemma i2norm_dotl m n p (M : 'M[C]_(m,n)) (N : 'M[C]_(n,p)): 
  l2norm (M *m N) <= l2norm M * i2norm N.
Proof. 
by rewrite -l2norm_adjmx -[X in X * _]l2norm_adjmx 
  adjmxM -i2norm_adjmx mulrC i2norm_dotr.
Qed.

Lemma i2normsE m (M : 'M[C]_m) : 
  i2norm M = \big[maxr/0%:R]_i (svds_d M 0 i).
Proof.
rewrite i2normE /svds_d.
move: (minn_id m) (minn_id m)=>/esym P1 P2.
rewrite (eq_irrelevance P2 (esym P1)). clear P2.
set t := svd_d M. destruct t.
case: (minn m m) / P1 f=>f. by rewrite castmx_id.
Qed.

Lemma i2normE_Sn m n (M : 'M[C]_(m.+1,n.+1)) : i2norm M = svd_d M 0 minnSS_ord0.
Proof. by rewrite i2normE max_svd_diag_Sn. Qed.

Lemma i2normsE_Sn m (M : 'M[C]_m.+1) : i2norm M = svds_d M 0 0.
Proof. by rewrite i2normE_Sn /svds_d castmxE ord1; f_equal; apply/ord_inj=>/=. Qed.

Lemma i2norm_existsr m n (M : 'M[C]_(m.+1,n.+1)) p : exists2 A : 'M[C]_(n.+1,p.+1), 
  (l2norm A = 1) & (l2norm (M *m A) = i2norm M). 
Proof.
exists (svd_v M *m delta_mx 0 0); last first.
rewrite {1}(svdE M) mulmxA mulmxKtV// -mulmxA l2normUl//.
by rewrite l2norm_dotV adjmxM -mulmxA [X in _ *m X]mulmxA cdiag_mx_mulr 
  -diag_mx_dmul svd_d_exdr_conj -diag_mx_adj -mulmxA mulmxA -adjmxM 
  -l2norm_dotV diag_mx_deltaM normvZ/= i2normE_Sn l2norm_delta 
  mulr1 svd_d_exdr0 ?ger0_norm.
by rewrite l2normUl// l2norm_delta.
Qed.

Lemma i2norm_existsl m n (M : 'M[C]_(m.+1,n.+1)) p : 
  exists2 A : 'M[C]_(p.+1,m.+1), (l2norm A = 1) & (l2norm (A *m M) = i2norm M). 
Proof.
move: (i2norm_existsr (M^*t) p)=>[A P1 P2].
exists (A^*t). by rewrite l2norm_adjmx.
by rewrite -[LHS]l2norm_adjmx !adjmxM adjmxK P2 i2norm_adjmx.
Qed.

Lemma i2norm_unitary m n (U : 'M[C]_(m,n)) : 
  U \is unitarymx -> i2norm U = (m != 0)%:R.
Proof.
case: m U=>[U|m]; first by rewrite mx_dim0 i2norm0.
case: n=>[U /mxrank_unitary PU|n U UU].
  by move: (rank_leq_col U); rewrite PU.
by rewrite i2normE_Sn svd_d_unitary ?mxE.
Qed.

Lemma i2norm_l2norm m n (A : 'M[C]_(m,n)) : i2norm A <= l2norm A.
Proof.
case: m A=>[A|m]; last case: n =>[A|n A].
  1,2: by rewrite !mx_dim0E i2norm0 normv0.
rewrite i2normE_Sn {2}(svdE A) l2normUr// l2normUl//.
rewrite l2norm_dotV cdiag_mx_mulr -diag_mx_dmul svd_d_exdr_conj -diag_mx_adj.
rewrite -l2norm_dotV l2norm_diag -(ler_pXn2r (ltn0Sn 1)) ?nnegrE//.
rewrite -svd_d_exdr0 svd_d_exdr0 /svd_d_exdr lpnorm_castmx lpnorm_rowmx0 lerXn2r// ?nnegrE//.
by apply/(le_trans _ (lpnorm_col_le _ _ minnSS_ord0)); rewrite lpnorm11 mxE ger0_norm.
Qed.

Lemma i2norm_elem m n (A : 'M[C]_(m,n)) : forall i j, `|A i j| <= i2norm A.
Proof.
move=>i j. suff ->: `|A i j| = l2norm ((delta_mx i i) *m A *m (delta_mx j j)).
apply (le_trans (i2norm_dotr _ _)). rewrite l2norm_delta mulr1.
apply (le_trans (i2normM _ _)). apply ler_piMl. apply i2norm_ge0.
apply (le_trans (i2norm_l2norm _)). by rewrite l2norm_delta.
rewrite lpnorm_mul_deltar.
suff -> : col j (delta_mx i i *m A) = A i j *: delta_mx i 0.
  by rewrite lpnormZ lpnorm_delta mulr1.
by apply/matrixP=>a b; rewrite ord1 mxE delta_mx_mulEr !mxE eqxx andbT mulrC eq_sym.
Qed.

Lemma i2norm_svd m n (A : 'M[C]_(m,n)) : i2norm A = i2norm (cdiag_mx (svd_d A)).
Proof. by rewrite {1}[A]svdE i2normUr_temp// i2normUl. Qed.
Lemma i2norm_svds m (A : 'M[C]_m) : i2norm A = i2norm (diag_mx (svds_d A)).
Proof. by rewrite {1}[A]svdsE i2normUr_temp// i2normUl. Qed.

End i2norm.

(* schattern norm *)
HB.lock
Definition schnorm (R : realType) (p : R) m n (A : 'M[R[i]]_(m,n)) :=
  lpnorm p (svd_d A).

Notation "'\s_' ( p ) | M |" := (schnorm p M) : ring_scope.
Notation "'\s_' p | M |" := (schnorm p M) : ring_scope.
(* Frobenius norm or the Hilbert–Schmidt norm, also the l2norm *)
Notation fbnorm := (schnorm 2).
Notation "\fb| M |" := (fbnorm M).
(* nuclear norm or trace norm, or the Ky Fan n-norm *)
Notation trnorm := (schnorm 1).
Notation "\tr| M |" := (trnorm M).

Lemma schnormsE (R : realType) (p : R) m (A : 'M[R[i]]_m) :
  schnorm p A = lpnorm p (svds_d A).
Proof. by rewrite schnorm.unlock /svds_d lpnorm_castmx. Qed.

Lemma schnormcE (R : realType) (p : R) m n (A : 'M[R[i]]_(m,n)) (r : nat) (eqr : _ = r) :
  schnorm p A = lpnorm p (csvdr_d A eqr).
Proof.
by case: r / eqr; rewrite schnorm.unlock (svd_d_csvdE A)
  castmx_funE lpnorm_rowmx0 castmx_funE.
Qed.

Section schnorm_baisc.
Variable (R : realType).
Local Notation C := R[i].

Lemma schnorm_plt1E p :
  p < 1 -> @schnorm R p = @schnorm R 0.
Proof. by move=>Pp; rewrite schnorm.unlock lpnorm_plt1E. Qed.

Lemma schnorm_castmx p m n m' n' (eqmn : (m = m') * (n = n')) (A : 'M[C]_(m,n)) :
  schnorm p (castmx eqmn A) = schnorm p A.
Proof. by rewrite castmx_funE. Qed.

Lemma schnormUl p m n (U : 'M[C]_m) (A : 'M[C]_(m,n)) :
  U \is unitarymx -> schnorm p (U *m A) = schnorm p A.
Proof. by move=>UU; rewrite schnorm.unlock svd_d_Ul. Qed.

#[local] Lemma schnormUr_temp p m n (U : 'M[C]_n) (A : 'M[C]_(m,n)) :
  U \is unitarymx -> schnorm p (A *m U) = schnorm p A.
Proof. by move=>UU; rewrite schnorm.unlock svd_d_Ur. Qed.

Lemma schnorm_permMl p m n (s : 'S_m) (A : 'M[C]_(m,n)) :
  schnorm p (perm_mx s *m A) = schnorm p A.
Proof. by rewrite schnormUl// perm_mx_unitary. Qed.

Lemma schnorm_permMr p m n (s : 'S_n) (A : 'M[C]_(m,n)) :
  schnorm p (A *m perm_mx s) = schnorm p A.
Proof. by rewrite schnormUr_temp// perm_mx_unitary. Qed.

Lemma schnorm_col_perm p m n (s : 'S_n) (A : 'M[C]_(m,n)) :
  schnorm p (col_perm s A) = schnorm p A.
Proof. by rewrite col_permE schnorm_permMr. Qed.

Lemma schnorm_row_perm p m n (s : 'S_m) (A : 'M[C]_(m,n)) :
  schnorm p (row_perm s A) = schnorm p A.
Proof. by rewrite row_permE schnorm_permMl. Qed.

Lemma schnorm_trmx p m n (A : 'M[C]_(m,n)) :
  schnorm p (A^T) = schnorm p A.
Proof. by rewrite schnorm.unlock svd_d_trmx lpnorm_castmx. Qed.

Lemma schnorm_adjmx p m n (A : 'M[C]_(m,n)) :
  schnorm p (A^*t) = schnorm p A.
Proof. by rewrite schnorm.unlock svd_d_adjmx lpnorm_castmx. Qed.

Lemma schnorm_conjmx p m n (A : 'M[C]_(m,n)) :
  schnorm p (A^*m) = schnorm p A.
Proof. by rewrite schnorm.unlock svd_d_conjmx. Qed.

Lemma schnorm_col_mx0 p m n r (A : 'M[C]_(m,n)) :
  schnorm p (col_mx A (0 : 'M_(r,n))) = schnorm p A.
Proof.
rewrite !(schnormcE _ erefl) csvd_d_col_mx0; 
by set P := etrans _ _; case: _ / P.
Qed.

Lemma schnorm_col_0mx p m n r (A : 'M[C]_(m,n)) :
  schnorm p (col_mx (0 : 'M_(r,n)) A) = schnorm p A.
Proof.
rewrite !(schnormcE _ erefl) csvd_d_col_0mx; 
by set P := etrans _ _; case: _ / P.
Qed.

Lemma schnorm_row_mx0 p m n r (A : 'M[C]_(m,n)) :
  schnorm p (row_mx A (0 : 'M_(m,r))) = schnorm p A.
Proof.
rewrite !(schnormcE _ erefl) csvd_d_row_mx0; 
by set P := etrans _ _; case: _ / P.
Qed.

Lemma schnorm_row_0mx p m n r (A : 'M[C]_(m,n)) :
  schnorm p (row_mx (0 : 'M_(m,r)) A) = schnorm p A.
Proof.
rewrite !(schnormcE _ erefl) csvd_d_row_0mx; 
by set P := etrans _ _; case: _ / P.
Qed.

Lemma schnormUr p m n l (U : 'M[C]_(n,l)) (A : 'M[C]_(m,n)) :
  U \is unitarymx -> schnorm p (A *m U) = schnorm p A.
Proof.
move=>PU; move: (unitary_dim PU)=>nl.
move: (unitary_ext PU)=>PU1.
have -> : A *m U = row_mx A 0 *m schmidt (col_mx U (0 : 'M_(l - n, l))).
  by rewrite -[X in _ = _ *m X]vsubmxK mul_row_col mul0mx addr0 -PU1.
rewrite -[_ *m _](castmx_id (erefl, erefl)) -(castmx_mul (subnKC nl)).
rewrite schnormUr_temp ?schnorm_castmx ?schnorm_row_mx0//.
by rewrite castmx_funE; apply/schmidt_unitarymx; rewrite subnKC.
Qed.

Lemma schnormUl_cond p m n l (U : 'M[C]_(l,m)) (A : 'M[C]_(m,n)) :
  U^*t \is unitarymx -> schnorm p (U *m A) = schnorm p A.
Proof. by move=>PU; rewrite -schnorm_adjmx adjmxM schnormUr// schnorm_adjmx. Qed.

Lemma schnorm_block_mx000 p m n k l (A : 'M[C]_(m,n)) :
  schnorm p (block_mx A 0 0 (0 : 'M_(k,l))) = schnorm p A.
Proof. by rewrite /block_mx row_mx0 schnorm_col_mx0 schnorm_row_mx0. Qed.

Lemma schnorm_ge0 p m n (A : 'M[C]_(m,n)) : 0 <= schnorm p A.
Proof. by rewrite schnorm.unlock. Qed.
#[local] Hint Extern 0 (is_true (0 <= schnorm _ _)) => apply: schnorm_ge0 : core.

Lemma schnorm0 p m n : schnorm p (0 : 'M[C]_(m,n)) = 0.
Proof. by rewrite schnorm.unlock svd_d0 lpnorm0. Qed.

Lemma schnorm0_eq0 p m n (A : 'M[C]_(m,n)) : schnorm p A = 0 -> A = 0.
Proof. by rewrite schnorm.unlock {2}(svdE A)=>/lpnorm0_eq0 ->; rewrite linear0 mulmx0 mul0mx. Qed.

Lemma schnorm0P p m n (A : 'M[C]_(m,n)) : reflect (schnorm p A = 0) (A == 0).
Proof. by apply/(iffP eqP)=>[->|/schnorm0_eq0//]; exact: schnorm0. Qed.
Definition schnorm_eq0 p m n A := sameP (schnorm p A =P 0) (@schnorm0P p m n A).

Lemma schnormM_ge p (q : ecindexType p) m n (A : 'M[C]_(m,n)) B : 
  `| \tr (A *m B) | <= schnorm p A * schnorm q B.
Proof.
wlog : m n p q A B / (m <= n)%N => [IH|Hmn].
  case: (leqP m n); first by apply IH.
  move=>/ltnW; rewrite mxtrace_mulC mulrC; apply/IH.
pose A' := castmx (subnKC Hmn, erefl) (col_mx A 0).
pose B' := castmx (erefl, subnKC Hmn) (row_mx B 0).
suff : `| \tr (A' *m B') | <= schnorm p A' * schnorm q B'.
  by rewrite castmx_mul !castmx_funE schnorm_row_mx0 schnorm_col_mx0 
    mul_col_row !mulmx0 mxtrace_block linear0 addr0.
move: A' B'; clear=> A B.
rewrite !schnormsE -[lpnorm q _]lpnorm_trmx.
apply/(le_trans _ (lpnorm_hoelder q _ _))=>//.
rewrite l1normE !big_ord1 mxE.
apply/(le_trans (vonNeumann_trace_ler A B)).
rewrite ger0_norm.
by under [leRHS]eq_bigr do rewrite mxE.
by apply sumr_ge0=>i _; rewrite mxE mulr_ge0.
Qed.

Lemma schnorm_existsl p (q : ecindexType p) m n (B : 'M[C]_(m,n)): 
  exists (A : 'M[C]_(n,m)), `| \tr (A *m B) | / schnorm p A = schnorm q B.
Proof.
case: (ecindexP q)=>[r->|->->|->->].
(* for finite case, 1 < p,q *)
clear q; rename r into q.
have [/eqP->|PB] := boolP (B == 0).
  by exists 0; rewrite mulmx0 linear0 normr0 !schnorm0 mul0r.
pose Da := \row_i ((c2r (svd_d B 0 i / schnorm q B)) `^ ((q : R)/p))%:C.
have PDa : Da \is svd_diag.
  apply/svd_diagP=>i; split; first by rewrite mxE lec0R.
  move=>j Pij; move: (svd_d_svd_diag B)=>/svd_diagP/(_ i)[] _ /(_ j Pij) P.
  rewrite !mxE lecR ge0_ler_powR ?nnegrE=>[//||||].
    by rewrite divr_ge0 ?(ci_p_ge0 q) ?ci_q_ge0.
    1,2: by rewrite c2r_ge0// divr_ge0.
    by rewrite ler_c2r// ler_wpM2r ?invr_ge0.
exists (svd_v B *m (cdiag_mx Da)^*t *m (svd_u B)^*t).
rewrite schnormUr// schnormUl// schnorm.unlock {2}cdiag_mx_adj svd_d_cdiag//;
  last by rewrite castmx_funE svd_diag_conj.
rewrite lpnorm_castmx lpnorm_conjmx {3}(svdE B) -!mulmxA mxtrace_mulC 
  !mulmxA !mulmxKtV// cdiag_mx_mulr svd_diag_conj// mxtrace_diag.
have -> : lpnorm p Da = 1.
  rewrite lpnorm.unlock lpnormrc.unlock ltNge (ci_p_ge1 q)/=.
  rewrite pair_bigV/= big_ord1.
  transitivity (((c2r (schnorm q B / schnorm q B)) `^ q `^ p^-1 )%:C);
    last by rewrite mulfV ?schnorm_eq0// c2r1 !powR1.
  f_equal; f_equal.
  rewrite {1}schnorm.unlock lpnorm.unlock lpnormrc.unlock ?ltNge ci_q_ge1/=.
  rewrite pair_bigV big_ord1/= c2rZ powRM// ?c2r_ge0// ?invr_ge0//.
  rewrite -powRrM mulVf ?ci_q_neq0// powRr1 ?sumr_ge0// mulr_suml.
  apply eq_bigr=>i _; rewrite !mxE normrc_r2c ger0_norm//.
  by rewrite -powRrM mulfVK ?(ci_p_neq0 q)// -!ger0_normrc 
    ?invr_ge0// ?divr_ge0// normrcM powRM.
rewrite invr1 mulr1 ger0_norm ?sumr_ge0//= =>[|i _]; last first.
  by rewrite !mxE mulr_ge0//; apply/svd_diag_ge0/svd_diag_exdr.
transitivity (\sum_j c2r (svd_d B 0 j) `^ q / c2r (schnorm q B) `^ ((q:R)/p))%:C.
  rewrite svd_d_exdr_dmul -(svd_d_exdr_sum _ (f := id))//.
  rewrite rmorph_sum/=; apply eq_bigr=>i _.
  rewrite !mxE -{2}[svd_d B 0 i]c2rK ?ger0_real//.
  rewrite -!ger0_normrc// ?divr_ge0// -realcM normrcM.
  rewrite powRM// mulrC mulrA normrcV -powRN_inv//.
  f_equal; f_equal.
  have /eqP -> : (q : R) / p == (q : R) - 1.
    by rewrite -{2}[q : R]mulr1 -{1}(invfD_eq1 q) mulrDr mulfV ?ci_q_neq0// addrK.
  by rewrite mulr_powRB1 ?ci_q_gt0.
rewrite -mulr_suml schnorm.unlock lpnorm.unlock r2cK lpnormrc.unlock ltNge ci_q_ge1/=
  -powRrM mulKf ?ci_q_neq0// pair_bigV big_ord1/= -powRN -[in RHS]mulr_powRB1.
under eq_bigr do rewrite -(ger0_normrc (svd_d_ge0 B _ _)).
by do ! f_equal; rewrite -(invfD_eq1 q) opprD addrC subrK.
by rewrite sumr_ge0. by rewrite invr_gt0 ci_q_gt0.
(* for spectial case: p = 0 (i.e., +oo) and q = 1 *)
pose Da : 'rV[C]_(minn m n) := const_mx 1.
have PDa : Da \is svd_diag.
  apply/svd_diagP=>i; split; first by rewrite mxE ler01.
  by move=>j _; rewrite !mxE lexx.
exists (svd_v B *m (cdiag_mx Da)^*t *m (svd_u B)^*t).
rewrite schnormUr// schnormUl// schnorm.unlock {2}cdiag_mx_adj svd_d_cdiag//;
  last by rewrite castmx_funE svd_diag_conj.
rewrite lpnorm_castmx lpnorm_conjmx {3}(svdE B) -!mulmxA mxtrace_mulC 
  !mulmxA !mulmxKtV// cdiag_mx_mulr svd_diag_conj// mxtrace_diag.
rewrite svd_d_exdr_dmul -(svd_d_exdr_sum _ (f := id))//.
rewrite lpnorm_const_plt1//= l1normE big_ord1 ger0_norm;
  last by rewrite sumr_ge0=>// i _; rewrite !mxE mul1r.
rewrite mulr_suml; apply eq_bigr=>/= i _.
case: eqP=>Pmn; first by exfalso; move: i; rewrite Pmn=>[[]].
by rewrite mulr1 normr1 divr1 !mxE mul1r ger0_norm.
(* for spectial case: p = 1 and q = 0 (i.e., +oo) *)
case: m B => [B | m]; last case: n => [B | n B].
  1,2: by exists 0; rewrite mx_dim0 !schnorm0 invr0 mulr0.
pose Da : 'rV[C]_(minn m.+1 n.+1) := delta_mx 0 minnSS_ord0.
have PDa : Da \is svd_diag.
  apply/svd_diagP=>i; split; first by rewrite mxE eqxx/= ler0n.
  move=>j; rewrite !mxE eqxx/= ler_nat; case: eqP=>// ->.
  by case: eqP=>//= P Pi; exfalso; apply/P/val_inj/eqP; rewrite /= -leqn0.
exists (svd_v B *m (cdiag_mx Da)^*t *m (svd_u B)^*t).
rewrite schnormUr// schnormUl// schnorm.unlock {2}cdiag_mx_adj svd_d_cdiag//;
  last by rewrite castmx_funE svd_diag_conj.
rewrite lpnorm_castmx lpnorm_conjmx {3}(svdE B) -!mulmxA mxtrace_mulC 
  !mulmxA !mulmxKtV// cdiag_mx_mulr svd_diag_conj// mxtrace_diag.
rewrite svd_d_exdr_dmul -(svd_d_exdr_sum _ (f := id))//.
rewrite lpnorm_delta divr1 (bigD1 minnSS_ord0)//= big1=>[|i/negPf Pi];
  last by rewrite !mxE eqxx Pi mul0r.
rewrite !mxE !eqxx/= mul1r addr0 lpnorm.unlock lpnormrc.unlock ltr01.
rewrite -normrcE /r2c/=; f_equal.
apply/le_anti/andP; split.
  by apply/bigmax_geP; right; exists (0,minnSS_ord0).
apply/bigmax_leP; split=>// [[i j]] _ /=.
rewrite ord1 !ger0_normrc// ler_c2r//.
by move: (svd_d_svd_diag B)=>/svd_diag_nincr/rv_nincrP/(_ minnSS_ord0 j); apply.
Qed.

Lemma schnorm_existsr p (q : ecindexType p) m n (B : 'M[C]_(m,n)): 
  exists (A : 'M[C]_(n,m)), `| \tr (A *m B) | / schnorm q A = schnorm p B.
Proof. apply/(schnorm_existsl p). Qed.

Lemma schnorm_triangle p m n (A B : 'M[C]_(m,n)) :
  schnorm p (A + B) <= schnorm p A + schnorm p B.
Proof.
case: (ltP p 1).
  move=>Pp; rewrite schnorm_plt1E//.
  pose q := (1 : R) : ecindexType 0.
2 : move=>Pp; pose q := (econjugate_index Pp).
all: move: (schnorm_existsr q (A + B))=>[X <-].
all: have [/eqP ->| Px ] := boolP (schnorm q X == 0).
1,3: by rewrite invr0 mulr0 addr_ge0.
all: rewrite ler_pdivrMr ?lt_def ?Px//= mulrDl mulmxDr linearD/=;
  apply/(le_trans (ler_normD _ _))/lerD; rewrite mxtrace_mulC.
1,3: by move: (schnormM_ge q A X).
all: by move: (schnormM_ge q B X).
Qed.
Definition ler_schnormD := schnorm_triangle.

Lemma schnormZ p (m n : nat) (c : C) (A : 'M[C]_(m,n)) :
  schnorm p (c *: A) = `|c| * schnorm p A.
Proof. by rewrite schnorm.unlock svd_dZ lpnormZ normr_id. Qed.

HB.instance Definition _ p m n := isVNorm.Build C 'M[C]_(m,n) (@schnorm R p m n)
  (@schnorm_triangle p m n) (@schnorm0_eq0 p m n) (@schnormZ p m n).

(* inherited properties *)
Section basic_properties.
Variable (p : R) (m n : nat).
Implicit Type (A B C : 'M[C]_(m,n)).
Local Notation "`[ x ]" := (schnorm p x).

Lemma schnormMn A : `[ A *+ n] = `[ A ] *+ n.
Proof. exact: normvMn. Qed.

Lemma schnormN A : `[ - A ] = `[ A ].
Proof. exact: normvN. Qed.

Lemma schnorm_nneg A : `[ A ] \is Num.nneg.
Proof. exact: normv_nneg. Qed.

Lemma schnorm_real A : `[ A ] \is Num.real.
Proof. exact: normv_real. Qed.

Lemma schnorm_gt0 A : `[ A ] > 0 = (A != 0).
Proof. exact: normv_gt0. Qed.

Lemma ler_schnormB A B : `[A - B] <= `[A] + `[B].
Proof. exact: lev_normB. Qed.

Lemma ler_schdistD A B C : `[B-C] <= `[B-A] + `[A-C].
Proof. exact: lev_distD. Qed.

Lemma schdistC A B : `[ A - B ] = `[ B - A ].
Proof. exact: distvC. Qed.

Lemma lerB_schnormD A B : `[A] - `[B] <= `[A + B].
Proof. exact: levB_normD. Qed.

Lemma lerB_schdist A B : `[A] - `[B] <= `[A - B].
Proof. exact: levB_dist. Qed.

Lemma ler_dist_schdist A B : `| `[A] - `[B] | <= `[A - B].
Proof. exact: lev_dist_dist. Qed.

Lemma ler_schnorm_sum I (r : seq I) (P: pred I) (f : I -> 'M[C]_(m,n)) :
  `[ \sum_(i <- r | P i) f i ] <= \sum_(i <- r | P i) `[ f i ].
Proof. exact: normv_sum. Qed.

Lemma schnorm_id A : `| `[A] | = `[A].
Proof. exact: normv_id. Qed.

Lemma schnorm_le0 A : `[A] <= 0 = (A == 0).
Proof. exact: normv_le0. Qed.

Lemma schnorm_lt0 A : `[A] < 0 = false.
Proof. exact: normv_lt0. Qed.

Lemma schnorm_gep0 A : schnorm 0 A <= schnorm p A.
Proof. by rewrite schnorm.unlock lpnorm_gep0. Qed.

Lemma schnorm_lep0 (A : 'M[C]_(m,n)) :
  0 <= p -> schnorm p A / ((minn m n)%:R `^ p^-1)%:C <= schnorm 0 A.
Proof. rewrite schnorm.unlock -{2}[minn m n]mul1n; exact: lpnorm_lep0. Qed.

Lemma schnorm_p0ge (A : 'M[C]_(m,n)) :
  0 <= p -> schnorm p A <= ((minn m n)%:R `^ p^-1)%:C * schnorm 0 A.
Proof. by rewrite schnorm.unlock -{2}[minn m n]mul1n; exact: lpnorm_p0ge. Qed.

End basic_properties.

Lemma schnormf_pge1_E (p : R) m n (A : 'M[C]_(m,n)) k : 
  (\rank A <= k)%N -> 1 <= p ->
  schnorm p A = ((\sum_(i < k) (svd_fR A i) `^ p) `^ p^-1)%:C.
Proof.
move=>/subnKC Pk Pp.
rewrite (schnormcE _ erefl) lpnorm.unlock; f_equal.
rewrite lpnormrc.unlock ltNge Pp/=; f_equal.
rewrite pair_bigV/= big_ord1 -Pk big_split_ord/= [X in _ + X]big1 ?addr0.
  by apply eq_bigr=>i _; f_equal; rewrite csvdr_dE svd_fE/= ger0_normrc// lec0R.
by move=>i _; rewrite svd_fR_eq0 ?leq_addr// powR0// gt_eqF// (lt_le_trans ltr01 Pp).
Qed.

Lemma schnorm_cvg1R (m n : nat) (A : 'M[C]_(m,n)) :
  (fun p => schnorm p A) @ 1^'+ --> schnorm 1 A.
Proof. by rewrite schnorm.unlock; exact: lpnorm_cvg1R. Qed.

Lemma schnorm_cvg1 (m n : nat) (A : 'M[C]_(m,n)) :
  (fun p : nat => schnorm (1+p%:R^-1) A) @ \oo --> schnorm 1 A.
Proof. rewrite schnorm.unlock; exact: lpnorm_cvg1. Qed.

Lemma schnorm_is_cvg1 (m n : nat) (A : 'M[C]_(m,n)) :
  cvgn (fun p : nat => schnorm (1+p%:R^-1) A).
Proof. apply/cvg_ex; exists (schnorm 1 A); exact: schnorm_cvg1. Qed.

Lemma schnorm_cvg (m n : nat) (A : 'M[C]_(m,n)) :
  (fun p : nat => schnorm (p.+1)%:R A) @ \oo --> schnorm 0 A.
Proof. rewrite schnorm.unlock; exact: lpnorm_cvg. Qed.

Lemma schnorm_is_cvg (m n : nat) (A : 'M[C]_(m,n)) :
  cvgn (fun p : nat => schnorm (p.+1)%:R A).
Proof. rewrite schnorm.unlock; exact: lpnorm_is_cvg. Qed.

Lemma schnorm_formC p m n (x : 'M[C]_(m,n)) :
  schnorm p (x^*t *m x) = schnorm p (x *m x^*t).
Proof.
rewrite (svdE x) !adjmxM !adjmxK -!mulmxA !schnormUl// !mulmxA !mulmxKtV//
  cdiag_mx_mull cdiag_mx_mulr !schnormUr// svd_d_exdr_dmul svd_d_exdl_dmul.
by rewrite /svd_d_exdr /svd_d_exdl !diag_mx_cast !schnorm_castmx !diag_mx_row
  /block_mx !linear0 !row_mx0 !schnorm_col_mx0 !schnorm_row_mx0 dmulmxC.
Qed.

Lemma schnorm_continuous p m n : continuous (@schnorm R p m n).
Proof. by apply/continuous_mnorm. Qed.

Lemma continuous_schnorm p m n (A : 'M[C]_(m,n)) : 
  1 < p -> {for p, continuous (fun p0 : R => schnorm p0 A)}.
Proof. rewrite schnorm.unlock; exact: continuous_lpnorm. Qed.

Lemma schnorm_nincr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) :
  1 <= p1 <= p2 -> schnorm p1 A >= schnorm p2 A.
Proof. rewrite schnorm.unlock; exact: lpnorm_nincr. Qed.

Lemma schnorm_ndecr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) : 
  1 <= p1 <= p2 ->     schnorm p1 A / ((\rank A)%:R `^ p1^-1)%:C 
                    <= schnorm p2 A / ((\rank A)%:R `^ p2^-1)%:C.
Proof. rewrite !(schnormcE _ erefl) -[X in X%:R]mul1n; exact: lpnorm_ndecr. Qed.

Lemma schnorm_diag p q (D : 'rV[C]_q) : schnorm p (diag_mx D) = lpnorm p D.
Proof.
pose D1 := \row_i (directc (D 0 i))^-1.
have UD1 : diag_mx D1 \is unitarymx.
  apply/unitarymxP/matrixP=>i j.
  rewrite mxE (bigD1 i)//= big1=>[|k /negPf Pk];
    last by rewrite mxE eq_sym Pk mulr0n mul0r.
  rewrite !mxE eqxx mulr1n eq_sym; case: eqP=>[->|].
    by rewrite mulr1n addr0 -normCK normfV directc_norm invr1 expr1n.
  by rewrite mulr0n conjC0 mulr0 addr0.
rewrite -(schnormUr _ _ UD1) diag_mx_dmul.
have PD1 : D .* D1 \is a nnegmx.
  by apply/nnegmxP=>i j; rewrite !mxE ord1 -norm_directcE.
move: (permv_sortv (D .* D1)) (nnegmx_svd_diag PD1)=>[s <- Ps].
move: (perm_mx_unitary C s) (diag_perm s (D .* D1))=>Ps1.
rewrite -mulmxU// -mulUCmx// =><-.
rewrite schnormUl ?trmxC_unitary// schnormUr// schnorm.unlock.
rewrite svd_d_diag// lpnorm_castmx lpnorm.unlock lpnormrc_col_perm; f_equal.
rewrite lpnormrc.unlock; case: ltP=> _;
under eq_bigr do rewrite !mxE ord1 -norm_directcE normrc_idV;
by under [in RHS]eq_bigr do rewrite ord1.
Qed.

Lemma schnorm_cdiag p m n (D : 'rV[C]_(minn m n)) : 
  schnorm p (cdiag_mx D) = lpnorm p D.
Proof.
by rewrite /cdiag_mx schnorm_castmx /block_mx row_mx0 
  schnorm_col_mx0 schnorm_row_mx0 schnorm_diag.
Qed.

Lemma schnorm_scale_plt1 p m (c : C) :
  p < 1 -> schnorm p (c%:M : 'M[C]_m) = `|c| * (m != 0)%:R.
Proof. by move=>Pp; rewrite schnormsE svds_d_scale lpnorm_const_plt1//= normr_id. Qed.

Lemma schnorm_scale_pge1 p m (c : C) :
  1 <= p -> schnorm p (c%:M : 'M[C]_m) = (m%:R `^ p^-1)%:C * `|c|.
Proof. by move=>Pp; rewrite schnormsE svds_d_scale lpnorm_const_pge1//= normr_id mul1n. Qed.

Lemma schnorm1_plt1 p m :
  p < 1 -> schnorm p (1%:M : 'M[C]_m) = (m != 0)%:R.
Proof. by move=>Pp; rewrite schnorm_scale_plt1//= normr1 mul1r. Qed.

Lemma schnorm1_pge1 p m :
  1 <= p -> schnorm p (1%:M : 'M[C]_m) = (m%:R `^ p^-1)%:C.
Proof. by move=>Pp; rewrite schnorm_scale_pge1//= normr1 mulr1. Qed.

Lemma schnorm11 p (A : 'M[C]_1) : schnorm p A = `|A 0 0|.
Proof.
have {1}->: A = A 0 0 *: 1%:M 
  by apply/matrixP=>i j; rewrite !mxE !ord1 eqxx mulr1.
by rewrite schnormZ schnormsE svds_d1 lpnorm11 mxE normr1 mulr1.
Qed.

Lemma schnorm_mxdiag p m n k l (A : 'M[C]_(m,n)) (B : 'M_(k,l)) :
  schnorm p (block_mx A 0 0 B) = lpnorm p (row_mx (svd_d A) (svd_d B)).
Proof.
pose Ul := block_mx (svd_u A) 0 0 (svd_u B).
pose Ur := block_mx (svd_v A) 0 0 (svd_v B).
have -> : block_mx A 0 0 B = Ul *m 
  (block_mx (cdiag_mx (svd_d A)) 0 0 (cdiag_mx (svd_d B))) *m Ur^*t.
  rewrite mulmx_block !mulmx0 !mul0mx !addr0 add0r adj_block_mx.
  by rewrite !linear0 mulmx_block !mulmx0 !mul0mx !addr0 add0r -!svdE.
rewrite schnormUr ?trmxC_unitary ?mxdiag_unitary//.
rewrite schnormUl ?mxdiag_unitary// /cdiag_mx mxdiag_cast schnorm_castmx.
rewrite -row_mx0 -!col_mx0 block_mxA schnorm_castmx ?(row_mx0,col_mx0).
rewrite schnorm_block_mx000.
set X := block_mx (diag_mx (svd_d A)) 0 0 0.
rewrite block_mx_perm schnorm_castmx schnormUr ?schnormUl ?perm_mx_unitary//.
rewrite -row_mx0 -col_mx0 block_mxA schnorm_castmx row_mx0 col_mx0.
by rewrite schnorm_block_mx000 block_mx_perm schnorm_castmx schnormUr 
  ?schnormUl ?perm_mx_unitary// -diag_mx_row schnorm_diag.
Qed.

Lemma schnorm_tens p m n k l (A : 'M[C]_(m,n)) (B : 'M_(k,l)) :
  schnorm p (A *t B) = schnorm p A * schnorm p B.
Proof.
rewrite !(schnormcE _ (rank_tens A B)).
move: (csvdr_d_tens erefl erefl (rank_tens A B))=>[] s ->. 
by rewrite lpnorm_col_perm tensvE castmx_funE lpnorm_tens !(schnormcE _ erefl).
Qed.

Lemma schnorm_swap p m n l k (A : 'M[C]_(m * n, l * k)) : 
  schnorm p (mxswap A) = schnorm p A.
Proof. by rewrite mxswap_permE schnorm_row_perm schnorm_col_perm castmx_funE. Qed.

(* TODO : https://arxiv.org/pdf/1202.3853 *)
(* about partial trace *)

Definition PauliX_genmx m (i : 'I_m.+1) : 'M[C]_(m.+1) :=
  perm_mx (perm (@subIr _ i)).
Definition PauliZ_genmx m (i : 'I_m.+1) : 'M[C]_(m.+1) :=
  diag_mx (\row_j expip (2 * i%:R * j%:R / m.+1%:R)).

(* Lemma PauliX_genmx_sumE m i : 
  @PauliX_genmx m i = \sum_j delta_mx (j + i) j.
Proof.
apply/matrixP=>j k; rewrite !mxE summxE permE (bigD1 k)//= big1.
by rewrite addr0 mxE eqxx andbT subr_eq.
by move=>l /negPf nlk; rewrite mxE andbC eq_sym nlk.
Qed.

Lemma PauliX_genmx_adj m i : (@PauliX_genmx m i)^*t = @PauliX_genmx m (-i).
Proof. by apply/matrixP=>j k; rewrite !mxE !permE conj_Creal// opprK subr_eq eq_sym. Qed.

Lemma PauliZ_genmx_adj m i : (@PauliZ_genmx m i)^*t = @PauliZ_genmx m (-i).
Proof.
apply/matrixP=>j k; rewrite !mxE eq_sym.
case: eqP=>[->|]; rewrite ?mulr0n ?conjC0// !mulr1n -expipNC.
have [/eqP -> | Pi ] := boolP (i == 0).
  by rewrite {2}/GRing.opp/= subn0 modnn !(mulr0, mul0r) oppr0.
rewrite {2}/GRing.opp/= modn_small; last by rewrite ltn_subrL lt0n Pi.
rewrite natrB 1?ltnW// mulrBr mulrBl mulrBl -!mulNr addrC expipD -[LHS]mulr1.
by f_equal; rewrite mulrAC mulfK// -natrM expip2n.
Qed.

Lemma PauliX_genmxE m i j k : @PauliX_genmx m i j k = (k + i == j)%:R.
Proof.
rewrite PauliX_genmx_sumE summxE (bigD1 k)//= big1.
by rewrite addr0 mxE eqxx andbT eq_sym.
by move=>l /negPf nl; rewrite mxE andbC eq_sym nl.
Qed.

Lemma PauliZ_genmxE m i j k : @PauliZ_genmx m i j k = 
  expip (2 * i%:R * j%:R / m.+1%:R) * (j == k)%:R.
Proof. by rewrite mxE -[LHS]mulr_natr mxE. Qed. *)

Lemma PauliX_genmx_unitary m i : @PauliX_genmx m i \is unitarymx.
Proof. by apply/perm_mx_unitary. Qed.
Lemma PauliZ_genmx_unitary m i : @PauliZ_genmx m i \is unitarymx.
Proof.
apply/unitarymxPV; rewrite diag_mx_adj diag_mx_dmul -diag_const_mx.
f_equal; apply/matrixP=>? j.
by rewrite !mxE -expipNC -expipD addNr expip0.
Qed.

Lemma ptrace1_unitary_sum m n (A : 'M[C]_(m.+1 * n)) :
  1%:M *t ptrace1 A = m.+1%:R^-1 *: (\sum_i\sum_j 
    ((PauliX_genmx i *m PauliZ_genmx j) *t 1%:M)^*t *m A *m 
    ((PauliX_genmx i *m PauliZ_genmx j) *t 1%:M)).
Proof.
apply/matrix_tenP=>a b c d; rewrite tensmxE !mxE summxE/=.
transitivity (m.+1%:R^-1 *  \sum_(i < m.+1) \sum_(j < m.+1) 
  expip (2 * (c%:R - a%:R) * j%:R / m.+1%:R) * 
  A (mxtens_index (a + i,b)) (mxtens_index (c + i,d))).
- under eq_bigr do rewrite -mulr_suml.
  rewrite -mulr_sumr expip_sum_ord// eq_sym.
  case: eqP=>[->|]; last by rewrite !mul0r mulr0.
  rewrite !mul1r mulrA mulVf// mul1r ptrace1E (reindex_perm (perm (@addrI _ a)))/=.
  by apply eq_bigr=>i _; rewrite !permE.
f_equal; apply eq_bigr=>i _; rewrite summxE; apply eq_bigr=>j _.
rewrite tensmxE_mid (bigD1 (c + i))//= (bigD1 d)//= !big1 ?addr0.
rewrite tensmxE tensmxE_mid (bigD1 (a + i))//= (bigD1 b)//= !big1 ?addr0.
rewrite adjmx_tens adjmx1 adjmxM tensmxE diag_mx_adj mul_diag_mx mul_mx_diag !mxE.
rewrite !permE !addrK !eqxx conjC1 !mulr1 mul1r [RHS]mulrAC -expipNC -expipD.
rewrite -mulNr -mulrDl -mulrN -mulrDr addrC; 
by do 3 f_equal; rewrite -!mulrA; f_equal; rewrite mulrC.
by move=>k /negPf nk; rewrite big1// =>? _; 
  rewrite adjmx_tens adjmx1 adjmxM tensmxE diag_mx_adj 
  mul_diag_mx !mxE permE subr_eq nk conjC0 mulr0 !mul0r.
by move=>k /negPf nk; rewrite adjmx_tens adjmx1 adjmxM tensmxE 
  diag_mx_adj mul_diag_mx mxE !mxE [b == k]eq_sym nk mulr0 !mul0r.
by move=>k /negPf nk; rewrite big1// =>? _;
  rewrite tensmxE mul_mx_diag !mxE permE subr_eq nk !mul0r mulr0.
by move=>k /negPf nk; rewrite tensmxE !mxE nk !mulr0.
Qed.

Lemma schnorm_ptrace1_plt1 p m n (A : 'M[C]_(m * n)) :
  p < 1 -> schnorm p (ptrace1 A) <= m%:R * schnorm p A.
Proof.
case: m A=>[A _ | m A Pp ].
  have -> : A = 0 by move: A; rewrite mul0n=>A; rewrite mx_dim0.
  by rewrite mul0r linear0 normv0.
have -> : \s_p| ptrace1 A | = \s_p| (1%:M : 'M_m.+1) *t ptrace1 A |.
  by rewrite schnorm_tens schnorm1_plt1//= mul1r.
rewrite ptrace1_unitary_sum schnormZ pair_big/= normfV ler_pdivrMl ?normr_gt0//.
apply/(le_trans (normv_sum _ _ _))/(le_trans (y := \sum_(i : 'I_m.+1 * 'I_m.+1) \s_p| A |)).
  apply/ler_sum=>[[i j] _]; rewrite /= schnormUr ?schnormUl//.
  1,2: by rewrite ?adjmx_unitary unitarymx_tens// mul_unitarymx// 
    ?PauliX_genmx_unitary ?PauliZ_genmx_unitary.
by rewrite sumr_const -[leLHS]mulr_natl card_prod card_ord ger0_norm// mulrA natrM.
Qed.

Lemma schnorm_ptrace2_plt1 p m n (A : 'M[C]_(m * n)) :
  p < 1 -> schnorm p (ptrace2 A) <= n%:R * schnorm p A.
Proof. by move=>Pp; rewrite ptrace2E1 -schnorm_swap schnorm_ptrace1_plt1. Qed.

Lemma schnorm_ptrace1_pge1 p m n (A : 'M[C]_(m * n)) : 
  1 <= p -> schnorm p (ptrace1 A) <= ((m%:R) `^ ((p-1)/p))%:C * schnorm p A.
Proof.
case: m A=>[A _ | m A Pp ].
  have -> : A = 0 by move: A; rewrite mul0n=>A; rewrite mx_dim0.
  by rewrite linear0 !normv0 mulr0.
have -> : \s_p| ptrace1 A | = ((m.+1%:R `^ p^-1) ^-1)%:C * \s_p| (1%:M : 'M_m.+1) *t ptrace1 A |.
  by rewrite schnorm_tens schnorm1_pge1//= mulrA -realcM mulVf ?mul1r// gt_eqF// powR_gt0.
rewrite ptrace1_unitary_sum schnormZ pair_big/= normfV realcI ler_pdivrMl 
  ?ltc0R ?powR_gt0// ler_pdivrMl ?normr_gt0//.
apply/(le_trans (normv_sum _ _ _))/(le_trans (y := \sum_(i : 'I_m.+1 * 'I_m.+1) \s_p| A |)).
  apply/ler_sum=>[[i j] _]; rewrite /= schnormUr ?schnormUl//.
  1,2: by rewrite ?adjmx_unitary unitarymx_tens// mul_unitarymx// 
    ?PauliX_genmx_unitary ?PauliZ_genmx_unitary.
rewrite sumr_const -[leLHS]mulr_natl card_prod card_ord ger0_norm//.
rewrite natrM -!mulrA ler_wpM2l// mulrA -realcM -powRD;
  last by rewrite natrS_neq0 implybT.
by rewrite mulrBl div1r addrC subrK mulfV ?gt_eqF// ?powRr1// ?natrC// (lt_le_trans ltr01 Pp).
Qed.

Lemma schnorm_ptrace2_pge1 p m n (A : 'M[C]_(m * n)) : 
  1 <= p -> schnorm p (ptrace2 A) <= ((n%:R) `^ ((p-1)/p))%:C * schnorm p A.
Proof. by move=>Pp; rewrite ptrace2E1 -schnorm_swap schnorm_ptrace1_pge1. Qed.

Lemma sch0norm_i2norm : @schnorm R 0 = i2norm.
Proof.
apply/functional_extensionality_dep=>m.
apply/functional_extensionality_dep=>n.
apply/funext=>M; rewrite i2normE schnorm.unlock l0normE.
under eq_bigr do rewrite -normrcE.
under [RHS]eq_bigr do rewrite -(ger0_norm (svd_d_ge0 _ _ _)) -normrcE.
rewrite !bigmax_r2c; f_equal; apply/le_anti/andP; split.
  apply/bigmax_leP; split=>[|[a b] _]; first by apply/bigmax_geP; left.
    by apply/bigmax_geP; right; exists b=>//=; rewrite ord1.
apply/bigmax_leP; split=>[|b _]; first by apply/bigmax_geP; left.
    by apply/bigmax_geP; right; exists (0,b).
Qed.

Lemma i2norm_sch0norm : i2norm = @schnorm R 0.
Proof. by rewrite sch0norm_i2norm. Qed.

Lemma i2norm_tens m n k l (A : 'M[C]_(m,n)) (B : 'M_(k,l)) :
  i2norm (A *t B) = i2norm A * i2norm B.
Proof. by rewrite i2norm_sch0norm schnorm_tens. Qed.

Lemma i2norm_formC m n (x : 'M[C]_(m,n)) :
  i2norm (x^*t *m x) = i2norm (x *m x^*t).
Proof. by rewrite i2norm_sch0norm schnorm_formC. Qed.

Lemma i2norm_ptrace1 m n (A : 'M[C]_(m * n)) :
  i2norm (ptrace1 A) <= m%:R * i2norm A.
Proof. by rewrite i2norm_sch0norm schnorm_ptrace1_plt1. Qed.

Lemma i2norm_ptrace2 m n (A : 'M[C]_(m * n)) :
  i2norm (ptrace2 A) <= n%:R * i2norm A.
Proof. by rewrite i2norm_sch0norm schnorm_ptrace2_plt1. Qed.

Lemma i2normUr m n l (U : 'M[C]_(n,l)) (A : 'M[C]_(m,n)) :
  U \is unitarymx -> i2norm (A *m U) = i2norm A.
Proof. by rewrite i2norm_sch0norm; apply schnormUr. Qed.

Lemma i2normUl_cond m n l (U : 'M[C]_(l,m)) (A : 'M[C]_(m,n)) :
  U^*t \is unitarymx -> i2norm (U *m A) = i2norm A.
Proof. by rewrite i2norm_sch0norm; apply schnormUl_cond. Qed.

Lemma schnormf0E m n (A : 'M[C]_(m,n)) : 
  schnorm 0 A = (svd_fR A 0)%:C.
Proof.
case: m A=>[A|m]; last case: n=>[A|n A].
1,2: by rewrite !mx_dim0E normv0 svd_fRE/= svd_f0.
by rewrite sch0norm_i2norm i2normE_Sn svd_dE svd_fE/=.
Qed.

Lemma fbnorm_l2norm : @schnorm R 2 = l2norm.
Proof.
apply/functional_extensionality_dep=>m.
apply/functional_extensionality_dep=>n.
apply/funext=>M.
by rewrite schnorm.unlock {2}[M]svdE l2normUr// l2normUl// l2norm_cdiag.
Qed.

Lemma l2norm_fbnorm : l2norm = @schnorm R 2.
Proof. by rewrite fbnorm_l2norm. Qed.

Lemma schnorm_hoelder_gen p q r m n k (A : 'M[C]_(m,n)) (B : 'M_(n,k)) :
  (0 <= p) -> (0 <= q) -> ((r == 0) || (1 <= r)) -> 
  p^-1 + q^-1 = r^-1 ->
  schnorm r (A *m B) <= schnorm p A * schnorm q B.
Proof.
move: (rank_leq_col A) (rank_leq_row B) (mulmx_max_rank A B) => A_r B_r AB_r.
move=>Pp Pq /orP[/eqP Pr Ppq|Pr Ppq].
have -> : p = 0.
  apply/le_anti/andP; split=>//; rewrite -invr_le0.
  by move: Ppq; rewrite Pr invr0 -[q^-1]opprK=>/subr0_eq->; rewrite oppr_le0 invr_ge0.
have -> : q = 0.
  apply/le_anti/andP; split=>//; rewrite -invr_le0.
  by move: Ppq; rewrite Pr invr0 -[p^-1]opprK addrC=>/subr0_eq->; rewrite oppr_le0 invr_ge0.
by rewrite Pr sch0norm_i2norm i2normM.
move: (lt_le_trans ltr01 Pr) (le_trans ler01 Pr)=>rgt0 rge0.
have /orP[/eqP peq0|pge1] : (p == 0) || (1 <= p).
move: Pp Pr; rewrite le_eqVlt=>/orP[/eqP<-|Pp]; first by rewrite eqxx.
by rewrite gt_eqF//= -!invf_le1//; apply: le_trans; rewrite -Ppq lerDl invr_ge0.
- move: Ppq; rewrite peq0 invr0 add0r=>/(f_equal GRing.inv); rewrite !invrK=>->.
  rewrite schnormf0E (schnormf_pge1_E AB_r)// (schnormf_pge1_E B_r)//.
  rewrite -realcM lecR -[svd_fR A 0](powRrK (r := r))// ?gt_eqF//.
  rewrite -powRM// ?sumr_ge0// ge0_ler_powR// ?invr_ge0// 
    ?nnegrE ?mulr_ge0// ?sumr_ge0// mulr_sumr.
  apply/(le_trans (svd_fR_powM _ _ _ rgt0))/ler_sum=>/= i _.
  by rewrite -powRM// ge0_ler_powR// ?nnegrE ?mulr_ge0// ler_pM// svd_fR_nincr.
have /orP[/eqP qeq0|qge1] : (q == 0) || (1 <= q).
  move: Pq Pr; rewrite le_eqVlt=>/orP[/eqP<-|Pq]; first by rewrite eqxx.
  by rewrite gt_eqF//= -!invf_le1//; apply: le_trans; rewrite -Ppq lerDr invr_ge0.
- move: Ppq; rewrite qeq0 invr0 addr0=>/(f_equal GRing.inv); rewrite !invrK=>->.
  rewrite schnormf0E (schnormf_pge1_E AB_r)// (schnormf_pge1_E A_r)//.
  rewrite -realcM lecR -[svd_fR B 0](powRrK (r := r))// ?gt_eqF//.
  rewrite -powRM// ?sumr_ge0// ge0_ler_powR// ?invr_ge0// 
    ?nnegrE ?mulr_ge0// ?sumr_ge0// mulr_suml.
  apply/(le_trans (svd_fR_powM _ _ _ rgt0))/ler_sum=>/= i _.
  by rewrite -powRM// ge0_ler_powR// ?nnegrE ?mulr_ge0// ler_pM// svd_fR_nincr.
rewrite (schnormf_pge1_E A_r)// (schnormf_pge1_E B_r)// (schnormf_pge1_E AB_r)//.
rewrite -realcM lecR.
apply/(le_trans _ (hoelder_gen_fin _ _ _ pge1 qge1 Pr Ppq))=>[|//|//].
rewrite ge0_ler_powR// ?invr_ge0// ?nnegrE ?sumr_ge0//.
by apply/svd_fR_powM.
Qed.

Lemma schnorm_hoelder p (q : ecindexType p) m n k (A : 'M[C]_(m,n)) (B : 'M_(n,k)) :
  schnorm 1 (A *m B) <= schnorm p A * schnorm q B.
Proof.
apply/schnorm_hoelder_gen.
by apply (ci_p_ge0 q).
by apply ci_q_ge0.
by rewrite lexx orbT.
by rewrite invr1 invfD_eq1.
Qed.

Lemma schnormM0r p m n k (A : 'M[C]_(m,n)) (B : 'M_(n,k)) :
  schnorm p (A *m B) <= schnorm 0 A * schnorm p B.
Proof.
have [Pp | Pp] := leP 1 p.
  by apply/schnorm_hoelder_gen=>//; 
    rewrite ?Pp ?orbT// ?invr0 ?add0r// (le_trans ler01).
rewrite schnorm_plt1E//.
by apply/schnorm_hoelder_gen=>//; rewrite ?eqxx// invr0 addr0.
Qed.

Lemma schnormMr p m n k (A : 'M[C]_(m,n)) (B : 'M_(n,k)) :
  schnorm p (A *m B) <= i2norm A * schnorm p B.
Proof. by rewrite i2norm_sch0norm schnormM0r. Qed.

Lemma schnormM0l p m n k (A : 'M[C]_(m,n)) (B : 'M_(n,k)) :
  schnorm p (A *m B) <= schnorm p A * schnorm 0 B.
Proof.
have [Pp | Pp] := leP 1 p.
  apply/schnorm_hoelder_gen=>//; 
  by rewrite ?Pp ?orbT// ?invr0 ?addr0// (le_trans ler01).
rewrite schnorm_plt1E//.
by apply/schnorm_hoelder_gen=>//; rewrite ?eqxx// invr0 add0r.
Qed.

Lemma schnormMl p m n k (A : 'M[C]_(m,n)) (B : 'M_(n,k)) :
  schnorm p (A *m B) <= schnorm p A * i2norm B.
Proof. by rewrite i2norm_sch0norm schnormM0l. Qed.

Lemma schnormM p m n k (A : 'M[C]_(m,n)) (B : 'M_(n,k)) :
  schnorm p (A *m B) <= schnorm p A * schnorm p B.
Proof.
apply/(le_trans (schnormM0l _ A B))/ler_pM=>//.
apply/schnorm_gep0.
Qed.

Lemma schnorm_svd p m n (M : 'M[C]_(m,n)) :
  schnorm p M = schnorm p (cdiag_mx (svd_d M)).
Proof. by rewrite {1}[M]svdE schnormUr ?schnormUl. Qed.

Lemma schnorm_svds p m (M : 'M[C]_(m)) :
  schnorm p M = schnorm p (diag_mx (svds_d M)).
Proof. by rewrite {1}[M]svdsE schnormUr ?schnormUl. Qed.

Lemma schnorm_delta p m n i j : schnorm p (delta_mx i j : 'M[C]_(m,n)) = 1.
Proof.
case: m i=>[[]//|/= m i]; case: n j=>[[]//|/= n j].
have <- : row_perm (tperm 0 i) (col_perm (tperm 0 j) (delta_mx 0 0)) 
  = delta_mx i j :> 'M[C]_(m.+1,n.+1).
  apply/matrixP=>a b; rewrite !mxE -(inj_eq (perm_inj (s := tperm 0 i))).
  rewrite -{1}tpermV permK permE/= -(inj_eq (perm_inj (s := tperm 0 j))).
  by rewrite -{1}tpermV permK permE/=.
rewrite schnorm_row_perm schnorm_col_perm.
have -> : delta_mx 0 0 = castmx ((add1n _), (add1n _)) 
  (block_mx (diag_mx (const_mx 1 : 'rV_1)) 0 0 0) :> 'M[C]_(m.+1,n.+1).
  apply/castmx_symV/matrixP=>a b; rewrite castmxE/= !esymK.
  case: (split_ordP a)=>[?->|c ->]; case: (split_ordP b)=>[?->|d ->];
  rewrite /= ?ord1/= ?block_mxEul ?block_mxEdl ?block_mxEur ?block_mxEdr !mxE//.
by rewrite castmx_funE /block_mx row_mx0/= schnorm_col_mx0 
  schnorm_row_mx0 schnorm_diag lpnorm11 mxE normr1.
Qed.

(*******   fbnorm and trnorm inherited   *******)
Definition fbnorm_adjmx := (schnorm_adjmx 2).
Definition fbnorm_conjmx := (schnorm_conjmx 2).
Definition fbnorm_trmx := (schnorm_trmx 2).
Definition fbnorm0_eq0 := (schnorm0_eq0 (p := 2)).
Definition fbnorm_ge0 := (schnorm_ge0 2).
Definition fbnorm_nneg := (schnorm_nneg 2).
Definition fbnorm0 := (schnorm0 2).
Definition fbnorm0P := (schnorm0P 2).
Definition fbnorm_eq0 := (schnorm_eq0 2).
Definition fbnormZ := (schnormZ 2).
Definition fbnormUl := (schnormUl 2).
Definition fbnormUl_cond := (schnormUl_cond 2).
Definition fbnormUr := (schnormUr 2).
Definition fbnorm_permMl := (schnorm_permMl 2).
Definition fbnorm_permMr := (schnorm_permMr 2).
Definition fbnorm_col_perm := (schnorm_col_perm 2).
Definition fbnorm_row_perm := (schnorm_row_perm 2).
Definition fbnorm_svd := (schnorm_svd 2).
Definition fbnorm_svds := (schnorm_svds 2).
Definition fbnorm_triangle := (schnorm_triangle 2).
Definition ler_fbnormD := fbnorm_triangle.
Definition fbnormM := (schnormM 2).
Definition fbnormMl := (schnormMl 2).
Definition fbnormMr := (schnormMr 2).
Definition fbnorm_diag := (schnorm_diag 2).
Definition fbnorm_cdiag := (schnorm_cdiag 2).
Definition fbnorm_formC := (schnorm_formC 2).
Definition fbnorm_delta := (schnorm_delta 2).
Definition fbnorm11 := (schnorm11 2).
Definition fbnorm_tens := (schnorm_tens 2).
Definition fbnorm_swap := (schnorm_swap 2).

Definition trnorm_adjmx := (schnorm_adjmx 1).
Definition trnorm_conjmx := (schnorm_conjmx 1).
Definition trnorm_trmx := (schnorm_trmx 1).
Definition trnorm0_eq0 := (schnorm0_eq0 (p := 1)).
Definition trnorm_ge0 := (schnorm_ge0 1).
Definition trnorm_nneg := (schnorm_nneg 1).
Definition trnorm0 := (schnorm0 1).
Definition trnorm0P := (schnorm0P 1).
Definition trnorm_eq0 := (schnorm_eq0 1).
Definition trnormZ := (schnormZ 1).
Definition trnormUl := (schnormUl 1).
Definition trnormUl_cond := (schnormUl_cond 1).
Definition trnormUr := (schnormUr 1).
Definition trnorm_permMl := (schnorm_permMl 1).
Definition trnorm_permMr := (schnorm_permMr 1).
Definition trnorm_col_perm := (schnorm_col_perm 1).
Definition trnorm_row_perm := (schnorm_row_perm 1).
Definition trnorm_svd := (schnorm_svd 1).
Definition trnorm_svds := (schnorm_svds 1).
Definition trnorm_triangle := (schnorm_triangle 1).
Definition ler_trnormD := trnorm_triangle.
Definition trnormM := (schnormM 1).
Definition trnormMl := (schnormMl 1).
Definition trnormMr := (schnormMr 1).
Definition trnorm_diag := (schnorm_diag 1).
Definition trnorm_cdiag := (schnorm_cdiag 1).
Definition trnorm_formC := (schnorm_formC 1).
Definition trnorm_delta := (schnorm_delta 1).
Definition trnorm11 := (schnorm11 1).
Definition trnorm_tens := (schnorm_tens 1).
Definition trnorm_swap := (schnorm_swap 1).

Lemma fbnorm_scale m (c : C) :
  fbnorm (c%:M : 'M[C]_m) = sqrtC (m%:R) * `|c|.
Proof. by rewrite schnorm_scale_pge1 ?powC_rootV// ?natrC// mulr2n lerDl. Qed.  

Lemma trnorm_scale m (c : C) :
  trnorm (c%:M : 'M[C]_m) = m%:R * `|c|.
Proof. by rewrite schnorm_scale_pge1// invr1 powRr1// natrC. Qed.

Lemma fbnorm1 m : fbnorm (1%:M : 'M[C]_m) = sqrtC (m%:R).
Proof. by rewrite fbnorm_scale normr1 mulr1. Qed.

Lemma trnorm1 m : trnorm (1%:M : 'M[C]_m) = m%:R.
Proof. by rewrite trnorm_scale normr1 mulr1. Qed.

Lemma fbnorm_ptrace1 m n (A : 'M[C]_(m * n)) : 
  fbnorm (ptrace1 A) <= sqrtC m%:R * fbnorm A.
Proof. by rewrite fbnorm_l2norm l2norm_ptrace1. Qed.

Lemma fbnorm_ptrace2 m n (A : 'M[C]_(m * n)) : 
  fbnorm (ptrace2 A) <= sqrtC n%:R * fbnorm A.
Proof. by rewrite fbnorm_l2norm l2norm_ptrace2. Qed.

Lemma trnorm_ptrace1 m n (A : 'M[C]_(m * n)) : 
  trnorm (ptrace1 A) <= trnorm A.
Proof.
move: (schnorm_ptrace1_pge1 A (lexx 1)).
by rewrite subrr mul0r powRr0 mul1r.
Qed.

Lemma trnorm_ptrace2 m n (A : 'M[C]_(m * n)) : 
  trnorm (ptrace2 A) <= trnorm A.
Proof. by rewrite ptrace2E1 -trnorm_swap trnorm_ptrace1. Qed.

Lemma fbnorm_dotV m n (M : 'M[C]_(m,n)) :
  \fb| M | = sqrtC (\tr (M^*t *m M)).
Proof. by rewrite fbnorm_l2norm dotV_l2norm sqrCK. Qed.

Lemma fbnorm_dot m n (M : 'M[C]_(m,n)) :
  \fb| M | = sqrtC (\tr (M *m M^*t)).
Proof. by rewrite dot_l2norm fbnorm_l2norm sqrCK. Qed.

Lemma fbnorm_existsr m n (M: 'M[C]_(m.+1,n.+1)) : exists2 A : 'M[C]_(n.+1),
  (i2norm A = 1) & (l2norm (M *m A) = fbnorm M).
Proof.
exists (svd_v M); first by rewrite i2norm_unitary//.
by rewrite {1}(svdE M) mulmxKtV// l2normUl// l2norm_cdiag schnorm.unlock.
Qed.

Lemma fbnorm_existsl m n (M: 'M[C]_(m.+1,n.+1)) : exists2 A : 'M[C]_(m.+1),
  (i2norm A = 1) & (l2norm (A *m M) = fbnorm M).
Proof.
by move: (fbnorm_existsr (M^*t))=>[A P1 P2]; exists (A^*t); 
  rewrite ?i2norm_adjmx// -l2norm_adjmx adjmxM adjmxK P2 schnorm_adjmx.
Qed.

Lemma i2norm_fbnorm m n (M : 'M[C]_(m,n)) : i2norm M <= fbnorm M.
Proof. by rewrite i2norm_sch0norm schnorm_gep0. Qed.

Lemma fbnormM_ge m n (A : 'M[C]_(m, n)) (B : 'M_(n, m)) :
  `| \tr (A *m B) | <= \fb| A | * \fb| B |.
Proof. by apply schnormM_ge. Qed.

(*****  trnorm (nuclear norm)  *****)

Lemma trnorm_exists m n (B: 'M[C]_(m.+1,n.+1)) : exists2 A : 'M_(n.+1,m.+1),
  (i2norm A = 1) & (`| \tr (A *m B) | = trnorm B).
Proof.
exists (svd_v B *m (cdiag_mx (const_mx 1))^*t *m (svd_u B)^*t).
by rewrite i2normUr ?trmxC_unitary ?i2normUl// i2norm_adjmx i2norm_cdiag 
  lpnorm_const_plt1// oner_eq0/= normr1 minnSS/= mulr1.
rewrite {3 4}(svdE B) -!mulmxA mxtrace_mulC !mulmxA !mulmxKtV// 
  trnormUr// trnormUl// trnorm_cdiag cdiag_mx_mulr conjmx_const svd_d_exdr_dmul.
rewrite conjC1 ger0_norm mxtrace_diag -(svd_d_exdr_sum _ (f := id))//.
  by rewrite l1normE big_ord1; apply eq_bigr=>i _; rewrite !mxE mul1r ger0_norm.
by apply sumr_ge0=>i _ ; rewrite !mxE mul1r.
Qed.

Lemma i2norm_trnorm m n (M : 'M[C]_(m,n)) : i2norm M <= trnorm M.
Proof. by rewrite i2norm_sch0norm schnorm_gep0. Qed.

Lemma trnorm_svdE m n (M: 'M[C]_(m,n)) : \tr| M | = \sum_i svd_d M 0 i.
Proof.
rewrite schnorm_svd schnorm_cdiag l1normE big_ord1.
by apply eq_bigr=>i _; rewrite ger0_norm.
Qed.

Lemma trnormM_ge m n (A : 'M[C]_(m, n)) (B : 'M_(n, m)) :
  `| \tr (A *m B) | <= \i2| A | * \tr| B |.
Proof. by rewrite i2norm_sch0norm; apply schnormM_ge. Qed.
Definition trnormM_ger := trnormM_ge.

Lemma trnormM_gel m n (A : 'M[C]_(m, n)) (B : 'M_(n, m)) :
  `| \tr (A *m B) | <= \tr| A | * \i2| B |.
Proof. by rewrite i2norm_sch0norm; apply schnormM_ge. Qed.

Lemma trnorm_ge_tr n (M : 'M[C]_n) : `| \tr M | <= trnorm M.
Proof.
case: n M => [M | n M]; first by rewrite mx_dim0E trnorm0 linear0 normr0.
rewrite (svdE M); apply/(le_trans (trnormM_gel _ _)).
by rewrite i2norm_unitary//= mulr1 trnormUl// trnormUr// trnormUl.
Qed.

Lemma psdmx_trnorm n (M : 'M[C]_n) : M \is psdmx -> \tr| M | = \tr M.
Proof.
move=>/psdmxP[]/hermmx_normal/eigen_dec{2 3}-> P1.
rewrite trnormUr ?trnormUl// adjmxK//.
rewrite -mulmxA mxtrace_mulC mulmxtVK// trnorm_diag mxtrace_diag l1normE big_ord1.
by apply eq_bigr=>/= i _; rewrite ger0_norm// -nnegrE; apply/nnegmxP.
Qed.

Lemma trnorm_inner n p (M : 'M[C]_n) (N : 'M[C]_(n,p)) : 
  `| \tr (N^*t *m M *m N ) | <= \tr| M | * \tr(N^*t *m N ).
Proof.
rewrite mxtrace_mulC mulmxA mxtrace_mulC.
apply/(le_trans (trnorm_ge_tr _))/(le_trans (trnormMl _ _))/ler_pM=>//.
apply (le_trans (i2norm_trnorm _)).
by rewrite [X in _ <= X]mxtrace_mulC psdmx_trnorm// form_psd.
Qed.

Lemma fbnorm_trnorm m n (M : 'M[C]_(m,n)) :
  fbnorm M <= trnorm M.
Proof. by apply/schnorm_nincr; rewrite lexx//= mulr2n lerDr. Qed.

Import MxLownerOrder.

Lemma lemx_psd_ub m (M : 'M[C]_m) : M \is psdmx -> M <= (\tr M)%:M.
Proof.
move=>P1; rewrite le_lownerE. apply/psdmx_dot=>u.
rewrite nnegrE linearB/= mulmxBl/= linearB/= subr_ge0 mul_mx_scalar -scalemxAl linearZ/=.
rewrite -(psdmx_trnorm P1). apply: (le_trans _ (trnorm_inner _ _)).
by apply/real_ler_norm/hermmx_dot/psdmx_herm.
Qed.

Lemma trnormD_eq n (x y : 'M[C]_n) : 
  (0 : 'M[C]_n) <= x -> (0 : 'M[C]_n) <= y 
    -> trnorm x  + trnorm y = trnorm (x + y).
Proof.
rewrite !le_lownerE !subr0=>P1 P2. move: (psdmxD P1 P2).
move: P1 P2=>/psdmx_trnorm->/psdmx_trnorm->/psdmx_trnorm->.
by rewrite linearD.
Qed.

End schnorm_baisc.

#[global] Hint Extern 0 (is_true (0 <= schnorm _ _)) => apply: schnorm_ge0 : core.

Section CmxLownerOrder.
Import MxLownerOrder.
Variable (R : realType).
Local Notation C := R[i].

Lemma form_nng_neq0 n x : reflect (exists u: 'cV[C]_n, 
  (0 < \tr (u^*t *m u)) && (\tr (u^*t *m x *m u) \isn't Num.nneg))
  (~~ ((0 : 'M[C]_n) <= x)).
Proof.
apply (iffP negP). apply contra_notP.
rewrite -forallNP=>P1. rewrite le_lownerE subr0. apply/psdmx_dot=>u.
move: (P1 u). move/negP. rewrite mxtrace_mulC negb_and=>/orP[|].
rewrite lt_def form_tr_ge0 negb_and/= orbF negbK=>/eqP/form_tr_eq0->.
by rewrite !mulmx0 linear0 nnegrE.
by rewrite negbK.
apply contraPnot. rewrite -forallNP le_lownerE subr0=>/psdmx_dot=>P1 u.
by apply/negP; rewrite negb_and negbK P1 orbT.
Qed.

Lemma Cnng_open (t : C) : t \isn't Num.nneg -> 
  exists2 e : C, 0 < e & forall s, `|s - t| < e -> s \isn't Num.nneg.
Proof.
rewrite nnegrE lecE/= negb_and -real_ltNge ?real0// ?num_real// =>/orP[P1|P1].
exists (`|complex.Im t|)%:C=>[|s]; first by rewrite ltcR normr_gt0.
2: exists (`|complex.Re t|)%:C=>[|s]; first by move: P1; rewrite ltcR !lt_def 
  normr_ge0 normr_eq0 eq_sym=>/andP[->].
all: rewrite nnegrE lecE negb_and/= -normr_gt0=>P2.
move: (le_lt_trans (normc_ge_Im _) P2). 2: move: (le_lt_trans (normc_ge_Re _) P2).
all: rewrite ltcR raddfB/= -[normr (_ - _)]normrN opprB =>P3.
move: (le_lt_trans (lerB_dist _ _) P3).
by rewrite ltrBlDl -ltrBlDr addrN=>->.
move/ltr_distlCDr: P3. 
by rewrite ltr0_norm// addrN -real_ltNge ?real0// ?num_real// orbC=>->.
Qed.

Lemma psdmx_closed n : (closed [set x : 'M[C]_n | (0 : 'M[C]_n) <= x])%classic.
Proof.
case: n=>[x/= _|n]; first by rewrite !mx_dim0. 
rewrite (_ : mkset _ = ~` [set x | ~ (0 : 'M[C]_n.+1) <= x]); last first.
by rewrite predeqE=>x /=; rewrite notK.
rewrite closedC. move=> x /= /negP /form_nng_neq0 [u /andP[P1 /Cnng_open [e egt0 Pe]]].
move: (@mnorm_bounded _ C n.+1 n.+1 (@trnorm _ _ : vnorm _) (@mx_norm _ _ _ : vnorm _))=>[c cgt0 Pc].
rewrite nbhs_ballP. 
exists (e/c/(\tr (u^*t *m u)))=>/=[|y/=]; first by do 2 apply divr_gt0=>//.
rewrite -ball_normE/= mulrAC ltr_pdivlMr// =>Pb; apply/negP/form_nng_neq0.
exists u; apply/andP; split=>//; apply Pe.
rewrite /ball/= -linearB/= -mulmxBl -mulmxBr.
apply: (le_lt_trans (trnorm_inner _ _)).
rewrite mulrC -lter_pdivlMl// mulrC. apply: (le_lt_trans _ Pb).
by move: (Pc (y - x))=>/=; rewrite mulrC -normrN opprB.
Qed.

Program Definition lowner_mxcporder n := MxCPorder _ _ (@psdmx_closed n).
Next Obligation. exact: lemx_add2rP. Qed.
Next Obligation. exact: lemx_pscale2lP. Qed.

Lemma cmxnondecreasing_opp n (u : nat -> 'M[C]_n) :
  nondecreasing_seq (- u) = nonincreasing_seq u.
Proof. exact: (mxnondecreasing_opp (lowner_mxcporder n)). Qed.

Lemma cmxnonincreasing_opp n (u : nat -> 'M[C]_n) :
  nonincreasing_seq (- u) = nondecreasing_seq u.
Proof. exact: (mxnonincreasing_opp (lowner_mxcporder n)). Qed.

Lemma cmxlbounded_by_opp n (b : 'M[C]_n) (u : nat -> 'M[C]_n) :
  lbounded_by (-b) (- u) = ubounded_by b u.
Proof. exact: (mxlbounded_by_opp (lowner_mxcporder n)). Qed.

Lemma cmxubounded_by_opp n (b : 'M[C]_n) (u : nat -> 'M[C]_n) :
  ubounded_by (-b) (- u) = lbounded_by b u.
Proof. exact: (mxubounded_by_opp (lowner_mxcporder n)). Qed.

(* different canonical route. prevent eq_op porderType ringType *)
Lemma ltcmx_def n (x y : 'M[C]_n) : (x ⊏ y) = (y != x) && (x ⊑ y).
Proof. exact: ltmx_def. Qed.

Lemma subcmx_gt0 n (x y : 'M[C]_n) : ((0 : 'M[C]_n) ⊏ y - x) = (x ⊏ y).
Proof. exact: (submx_gt0 (lowner_mxcporder n)). Qed.

(* restate the cmxcvgn of lowner order and trnorm *)
Lemma cmxcvgn_trnorm m n (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  u @ \oo --> a -> ((@trnorm _ _) \o u) @ \oo --> \tr| a |.
Proof. exact: mxcvgn_mnorm. Qed.

Lemma is_cmxcvgn_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvgn u -> cvgn ((@trnorm _ _) \o u).
Proof. exact: is_mxcvgn_mnorm. Qed.

Lemma cmxlimn_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvgn u -> limn ((@trnorm _ _) \o u) = \tr| limn u |.
Proof. exact: cmxlimn_mnorm. Qed.

Lemma cmxnondecreasing_is_cvgn n (f : nat -> 'M[C]_n) (b : 'M[C]_n) :
  nondecreasing_seq f -> ubounded_by b f -> cvgn f.
Proof. exact: (mxnondecreasing_is_cvgn (lowner_mxcporder n)). Qed.

Lemma cmxnonincreasing_is_cvgn n (f : nat -> 'M[C]_n) (b : 'M[C]_n) :
  nonincreasing_seq f -> lbounded_by b f -> cvgn f.
Proof. exact: (mxnonincreasing_is_cvgn (lowner_mxcporder n)). Qed.

Lemma cmxopen_nge0 n : open [set x : 'M[C]_n | ~ 0 ⊑ x].
Proof. exact: (mxopen_nge0 (lowner_mxcporder n)). Qed.

Lemma cmxopen_nge n (y : 'M[C]_n) : open [set x : 'M[C]_n | ~ y ⊑ x].
Proof. exact: (mxopen_nge (lowner_mxcporder n)). Qed.

Lemma cmxopen_nle0 n : open [set x : 'M[C]_n | ~ x ⊑ 0].
Proof. exact: (mxopen_nle0 (lowner_mxcporder n)). Qed.

Lemma cmxopen_nle n (y : 'M[C]_n) : open [set x : 'M[C]_n | ~ x ⊑ y].
Proof. exact: (mxopen_nle (lowner_mxcporder n)). Qed.

Lemma cmxclosed_ge n (x : 'M[C]_n) : closed [set y : 'M[C]_n | x ⊑ y ].
Proof. exact: (mxclosed_ge (lowner_mxcporder n)). Qed.

Lemma cmxclosed_le n (x : 'M[C]_n) : closed [set y : 'M[C]_n | y ⊑ x ].
Proof. exact: (mxclosed_le (lowner_mxcporder n)). Qed.

Lemma cmxlimn_ge_near n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvgn u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ limn u.
Proof. exact: (mxlimn_ge_near (lowner_mxcporder n)). Qed.

Lemma cmxlimn_le_near n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvgn u -> (\forall n \near \oo, u n ⊑ x) -> limn u ⊑ x.
Proof. exact: (mxlimn_le_near (lowner_mxcporder n)). Qed.

Lemma ler_cmxlimn_near n (u_ v_ : nat -> 'M[C]_n) : cvgn u_ -> cvgn v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> limn u_ ⊑ limn v_.
Proof. exact: (ler_mxlimn_near (lowner_mxcporder n)). Qed.

Lemma cmxlimn_ge n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvgn u -> lbounded_by x u -> x ⊑ limn u.
Proof. exact: (mxlimn_ge (lowner_mxcporder n)). Qed.

Lemma cmxlimn_le n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvgn u -> ubounded_by x u -> limn u ⊑ x.
Proof. exact: (mxlimn_le (lowner_mxcporder n)). Qed.

Lemma ler_cmxlimn n (u v : nat -> 'M[C]_n) : cvgn u -> cvgn v ->
  (forall n, u n ⊑ v n) -> limn u ⊑ limn v.
Proof. exact: (ler_mxlimn (lowner_mxcporder n)). Qed.

Lemma cmxnondecreasing_cvgn_le n (u : nat -> 'M[C]_n) :
  nondecreasing_seq u -> cvgn u -> ubounded_by (limn u) u.
Proof. exact: (mxnondecreasing_cvgn_le (lowner_mxcporder n)). Qed.

Lemma cmxnonincreasing_cvgn_ge n (u : nat -> 'M[C]_n) : 
  nonincreasing_seq u -> cvgn u -> lbounded_by (limn u) u.
Proof. exact: (mxnonincreasing_cvgn_ge (lowner_mxcporder n)). Qed.

Lemma trace_continuous n : continuous (@mxtrace _ n : 'M[C]_n -> C).
Proof. by apply/cmxscalar_continuous/linearP. Qed.

Variable (V : finNormedModType C).

Lemma bijective_to_cmx_continuous (m n: nat) (f: V -> 'M[C]_(m,n)) 
  (lf: linear f) (bf: bijective f) : continuous f.
Proof. exact: bijective_to_mx_continuous. Qed.

Lemma bijective_of_cmx_continuous (m n: nat) (g: 'M[C]_(m,n) -> V) 
  (lg: linear g) (bg: bijective g) : continuous g.
Proof. exact: bijective_of_mx_continuous. Qed.

Lemma bijective_to_cmx_cvgnE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V) 
  (a : V) (lf: linear f) (bf: bijective f) :
  u @ \oo --> a = ((f \o u)%FUN @ \oo --> f a).
Proof. exact: bijective_to_mx_cvgnE. Qed.

Lemma bijective_of_cmx_cvgnE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  u @ \oo --> a = ((f \o u)%FUN @ \oo --> f a).
Proof. exact: bijective_of_mx_cvgnE. Qed.

Lemma bijective_to_cmx_is_cvgnE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) : cvgn u = cvgn (f \o u)%FUN.
Proof. exact: bijective_to_mx_is_cvgnE. Qed.

Lemma bijective_of_cmx_is_cvgnE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  cvgn u = cvgn (f \o u)%FUN.
Proof. exact: bijective_of_mx_is_cvgnE. Qed.

Lemma bijective_to_cmx_limnE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) :
  cvgn u -> limn (f \o u)%FUN = f (limn u).
Proof. exact: bijective_to_mx_limnE. Qed.

Lemma bijective_of_cmx_limnE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  cvgn u -> limn (f \o u)%FUN = f (limn u).
Proof. exact: bijective_of_mx_limnE. Qed.

Lemma linear_to_cmx_continuous m n (f : {linear V -> 'M[C]_(m,n)}) :
  continuous f.
Proof. exact: linear_to_mx_continuous. Qed.

Lemma linear_to_cmx_continuousP m n (f : V -> 'M[C]_(m,n)) :
  linear f -> continuous f.
Proof. exact: linear_to_mx_continuousP. Qed.

Lemma linear_of_cmx_continuous m n (f : {linear 'M[C]_(m,n) -> V}) :
  continuous f.
Proof. exact: linear_of_mx_continuous. Qed.

Lemma linear_of_cmx_continuousP m n (f : 'M[C]_(m,n) -> V) :
  linear f -> continuous f.
Proof. exact: linear_of_mx_continuousP. Qed.

Lemma closed_letr n (x : C) : closed [set y : 'M[C]_n | \tr y <= x].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | y <= x])%classic.
apply: cmxcclosed_comp. exact: linearP. apply/cclosed_le. by apply/funext=>y.
Qed.

Lemma closed_getr n (x : C) : closed [set y : 'M[C]_n | x <= \tr y].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | x <= y])%classic.
apply: cmxcclosed_comp. exact: linearP. apply/cclosed_ge. by apply/funext=>y.
Qed.

Lemma closed_eqtr n (x : C) : closed [set y : 'M[C]_n | \tr y = x].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | y = x])%classic.
apply: cmxcclosed_comp. exact: linearP. apply/cclosed_eq. by apply/funext=>y.
Qed.

Lemma cmxcvgn_trace n (u : nat -> 'M[C]_n) (a : 'M[C]_n) : 
  u @ \oo --> a -> ((@mxtrace _ n) \o u) @ \oo --> \tr a.
Proof. by apply/cmxcvgn_sfun/linearP. Qed.

Lemma is_cmxcvgn_trace n (u : nat -> 'M[C]_n) : cvgn u -> cvgn ((@mxtrace _ n) \o u).
Proof. by apply/is_cmxcvgn_sfun/linearP. Qed.

Lemma cmxlimn_trace n (u : nat -> 'M[C]_n) : 
  cvgn u -> limn ((@mxtrace _ n) \o u) = \tr (limn u).
Proof. by apply/cmxlimn_sfun/linearP. Qed.

Lemma closed_denmx n : closed [set x : 'M[C]_n | x \is denmx].
Proof.
rewrite (_ : mkset _ = [set x | (0:'M[C]_n) ⊑ x] `&` [set x | \tr x <= 1]).
apply: closedI. apply: cmxclosed_ge. apply: closed_letr.
by rewrite predeqE=>x/=; split; rewrite le_lownerE subr0=>/denmxP.
Qed.

Lemma closed_obsmx n : closed [set x : 'M[C]_n | x \is obsmx].
Proof.
rewrite (_ : mkset _ = [set x | (0:'M[C]_n) ⊑ x] `&` [set x | x ⊑ 1%:M]).
apply: closedI. apply: cmxclosed_ge. apply: cmxclosed_le.
rewrite predeqE=>x/=; split.
by rewrite [in X in X -> _]obsmx_psd_eq !le_lownerE subr0=>/andP.
by rewrite [in X in _ -> X]obsmx_psd_eq !le_lownerE subr0=>[[]]->->.
Qed.

Lemma closed_to_cmx_linearP m n (f : V -> 'M[C]_(m,n)) (A : set 'M[C]_(m,n)):
  linear f -> closed A -> closed (f @^-1` A).
Proof. exact: closed_to_mx_linearP. Qed.

Lemma closed_to_cmx_linear m n (f : {linear V -> 'M[C]_(m,n)}) (A : set 'M[C]_(m,n)):
  closed A -> closed (f @^-1` A).
Proof. exact: closed_to_mx_linear. Qed.

Lemma open_to_cmx_linearP m n (f : V -> 'M[C]_(m,n)) (A : set 'M[C]_(m,n)):
  linear f -> open A -> open (f @^-1` A).
Proof. exact: open_to_mx_linearP. Qed.

Lemma open_to_cmx_linear m n (f : {linear V -> 'M[C]_(m,n)}) (A : set 'M[C]_(m,n)):
  open A -> open (f @^-1` A).
Proof. exact: open_to_mx_linear. Qed.

Lemma closed_of_cmx_linearP m n (f : 'M[C]_(m,n) -> V) (A : set V):
  linear f -> closed A -> closed (f @^-1` A).
Proof. exact: closed_of_mx_linearP. Qed.

Lemma closed_of_cmx_linear m n (f : {linear 'M[C]_(m,n) -> V}) (A : set V):
  closed A -> closed (f @^-1` A).
Proof. exact: closed_of_mx_linear. Qed.

Lemma open_of_cmx_linearP m n (f : 'M[C]_(m,n) -> V) (A : set V):
  linear f -> open A -> open (f @^-1` A).
Proof. exact: open_of_mx_linearP. Qed.

Lemma open_of_cmx_linear m n (f : {linear 'M[C]_(m,n) -> V}) (A : set V):
  open A -> open (f @^-1` A).
Proof. exact: open_of_mx_linear. Qed.

End CmxLownerOrder.

Section DenmxCPO.
Import MxLownerOrder Num.Theory.
Variable (R: realType) (n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_n.
Local Notation D := 'MDen[C]_n.

Local Open Scope complex_scope.

Definition D2M (x : D) := x : M.

Lemma denmx0 : (0 : 'M[C]_n) \is denmx.
Proof. by apply/denmxP; split; [apply psdmx0 | rewrite linear0 lter01]. Qed.

Definition Denmx0 := ((DenMx denmx0) : D).

Definition Dlub (u : nat -> D) :=
  match limn (D2M \o u) \is denmx =P true with
  | ReflectT isden => (DenMx isden : D)
  | _ => Denmx0
  end.

Lemma chainD_subproof (u : nat -> D) : chain u -> nondecreasing_seq (D2M \o u).
Proof. by move=>/chain_homo P i j Pij; move: (P _ _ Pij); rewrite/= leEsub. Qed.

Lemma Dge0_subproof : forall (x : D), Denmx0 ⊑ x.
Proof. by move=>x/=; case: x=>m Pm; rewrite leEsub/= le_lownerE subr0; apply/denmx_psd. Qed.

Lemma chainD_lb_subproof (u : nat -> D) : forall i, (0:M) ⊑ (D2M \o u) i.
Proof. by move=>i/=; case: (u i)=>m Pm; rewrite/= le_lownerE subr0; apply/denmx_psd. Qed.

Lemma chainD_ub_subproof (u : nat -> D) : forall i, (D2M \o u) i ⊑ 1%:M.
Proof.
move=>i/=; case: (u i)=>m Pm; rewrite/= le_lownerE.
by move: Pm=>/denmx_obs; rewrite obsmx_psd_eq=>/andP[_].
Qed.

Lemma limn_denmx (u : nat -> D) : 
  cvgn (D2M \o u) -> [set x | x \is denmx] (limn (D2M \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (D2M \o u) _ _ _ _)=>//.
apply closed_denmx. by apply: nearW=>x/=; case: (u x).
Qed.

Lemma Dlub_lub : forall c : nat -> D, chain c -> (forall i, c i ⊑ Dlub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> Dlub c ⊑ x).
Proof.
move=>c Pc. move: (chainD_subproof Pc) (chainD_ub_subproof c)=>P1 P2.
move: (cmxnondecreasing_is_cvgn P1 P2)=>P3.
move: (cmxnondecreasing_cvgn_le P1 P3)=>P4.
rewrite /Dlub; case: eqP=>P5; last by exfalso; apply P5; apply limn_denmx.
split. by move=>i; rewrite leEsub/= P4.
by move=>x Px; rewrite leEsub/=; apply: cmxlimn_le.
Qed.

Lemma Dlub_ub : forall c : nat -> D, chain c -> (forall i, c i ⊑ Dlub c).
Proof. by move=>c /Dlub_lub=>[[P1]]. Qed.

Lemma Dlub_least : 
  forall c : nat -> D, chain c -> forall x, (forall i, c i ⊑ x) -> Dlub c ⊑ x.
Proof. by move=>c /Dlub_lub=>[[_ ]]. Qed.

HB.instance Definition _ := isCpo.Build ring_display D Dge0_subproof Dlub_ub Dlub_least.

End DenmxCPO.