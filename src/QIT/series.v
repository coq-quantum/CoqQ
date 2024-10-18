From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra bigop.
From mathcomp.analysis Require Import -(notations)forms.
Require Import spectral.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import reals topology normedtype sequences exp prodnormedzmodule.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import mcextra mcaextra notation prodvect hermitian tensor
 cpo EqdepFacts Eqdep_dec mxpred extnum ctopology setdec quantum summable.

(****************************************************************************)
(*                       Module for Generalized Series                      *)
(* ------------------------------------------------------------------------ *)
(* We define the generalized exponential function expM that can be used for *)
(* R[i] and chsf based on series theory. For the convergence of expM, we    *)
(* constrain the multiplication to satisfy biMulNormed, which is defined in *)
(* the following hierarchy:                                                 *)
(*   mcNormed --> mulNormed ---> biMulNormed --> biMulNormed1               *)
(*                                                                          *)
(*      mcNormed == There exists a positive constant mc such that           *)
(*                  `|A * B| <= mc * `|A| * `|B|                            *)
(*     mulNormed == The above constant mc equals to 1:                      *)
(*                  `|A * B| <= `|A| * `|B|                                 *)
(*   biMulNormed == bilinear and mulNormed                                  *)
(*  biMulNormed1 == biMulNormed and monoid                                  *)
(* ------------------------------------------------------------------------ *)
(* * Theories :                                                             *)
(*    The convergence of the series expM and several equations              *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order Order.Theory GRing.Theory GRing.
Import Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import VNorm.Exports VOrder.Exports.
Import ExtNumTopology.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope lfun_scope.

HB.mixin Record isMCNormed (R : realType) (C : extNumType R)
    (V : completeNormedModType C) (mulx : V -> V -> V) := {
  mc : C;
  mc_gt0 : mc > 0;
  normMC : forall A B, `|mulx A B| <= mc * `|A| * `|B|
}.

#[short(type="mcNormed")]
HB.structure Definition MCNormed (R : realType) (C : extNumType R)
    (V : completeNormedModType C) :=
  {mulx of isMCNormed R C V mulx}.

HB.mixin Record MCNormed_isMulNormed (R : realType) (C : extNumType R)
  (V : completeNormedModType C) mulx of @MCNormed R C V mulx := {
  mc_eq1 : @mc R C V mulx = 1
}.

#[short(type="mulNormed")]
HB.structure Definition MulNormed (R : realType) (C : extNumType R)
    (V : completeNormedModType C) :=
  {mulx of MCNormed_isMulNormed R C V mulx & @MCNormed R C V mulx}.

HB.factory Record isMulNormed (R : realType) (C : extNumType R)
  (V : completeNormedModType C) (mulx : V -> V -> V) := {
  normM : forall A B, `|mulx A B| <= `|A| * `|B|
}.
HB.builders Context R C V mulx of isMulNormed R C V mulx.
Program Definition isMCNormed_mixin := @isMCNormed.Build R C V mulx 1 ltr01 _.
Next Obligation.
by move=> A B; rewrite mul1r normM.
Qed.
HB.instance Definition _ := isMCNormed_mixin.
HB.instance Definition _ := @MCNormed_isMulNormed.Build R C V mulx erefl.
HB.end.

#[short(type="biMulNormed")]
HB.structure Definition BiMulNormed (R : realType) (C : extNumType R)
    (V : completeNormedModType C) :=
  {mulx of @Bilinear C V V V *:%R *:%R mulx & @MulNormed R C V mulx}.

Module BiMulNormedExports.
#[deprecated(since="mathcomp 2.0.0", note="Use BiMulNormed.clone instead.")]
Notation "[ 'biMulNormed' 'of' T 'for' cT ]" := (BiMulNormed.clone _ _ _ T%type cT)
  (at level 0, format "[ 'biMulNormed'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use BiMulNormed.clone instead.")]
Notation "[ 'biMulNormed' 'of' f ]" := (BiMulNormed.clone _ _ _ f _)
  (at level 0, format "[ 'biMulNormed'  'of'  f ]") : form_scope.
End BiMulNormedExports.
HB.export BiMulNormedExports.

#[short(type="biMulNormed1")]
HB.structure Definition BiMulNormed1 (R : realType) (C : extNumType R)
    (V : completeNormedModType C) (idm : V) :=
  {mulx of @BiMulNormed R C V mulx & Monoid.Law V idm mulx}.

Module BiMulNormed1Exports.
#[deprecated(since="mathcomp 2.0.0", note="Use BiMulNormed1.clone instead.")]
Notation "[ 'biMulNormed1' 'of' T 'for' cT ]" := (BiMulNormed1.clone _ _ _ _ T%type cT)
  (at level 0, format "[ 'biMulNormed1'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use BiMulNormed1.clone instead.")]
Notation "[ 'biMulNormed1' 'of' f ]" := (BiMulNormed1.clone _ _ _ _ f _)
  (at level 0, format "[ 'biMulNormed1'  'of'  f ]") : form_scope.
End BiMulNormed1Exports.
HB.export BiMulNormed1Exports.

Section C_biMulNormed1.
Variable R : realType.
Local Notation C := R[i]. 

Program Definition C_mulNormedMixin := @isMulNormed.Build R C C (@mul C) _.
Next Obligation. by move => a b; rewrite normrM. Qed.
HB.instance Definition _ := C_mulNormedMixin.

Program Definition C_bilinearMixin := bilinear_isBilinear.Build C C C C
  *:%R *:%R *%R (_, _).
Next Obligation. by move => a b x y; rewrite /scale /= mulrDl mulrA. Qed.
Next Obligation. by move => a b x y; rewrite /scale /= mulrDr mulrCA. Qed.
HB.instance Definition _ := C_bilinearMixin.

End C_biMulNormed1.

Section chsf_biMulNormed1.
Local Notation R := hermitian.R.
Local Notation C := hermitian.C.
Variable V: chsType.
Local Notation F := 'End(V).
Import HermitianTopology.
HB.instance Definition _ := @isMulNormed.Build R C F
  (@comp_lfun C V V V) (@trfnormM V V V).
HB.instance Definition _ := Monoid.isLaw.Build F (1%:VF)
  (@comp_lfun C V V V) mulrA mul1r mulr1.

End chsf_biMulNormed1.

Section MCNormedTheory.

Variable (R : realType) (C : extNumType R) (V : completeNormedModType C).
Variable (mulx : mcNormed V).
Implicit Type A B: V.
Implicit Types u : V ^nat.

Local Notation mc := (@mc R C V mulx).
Local Notation "x *x y" := (mulx x y) (at level 45, left associativity).

Lemma mc_ge0 : mc >= 0.
Proof. apply /ltW /mc_gt0. Qed.
Lemma mc_neq0 : mc != 0.
Proof. exact: (lt0r_neq0 mc_gt0). Qed.
Local Hint Resolve mc_gt0 : core.
Local Hint Resolve mc_ge0 : core.
Local Hint Resolve mc_neq0 : core.

Lemma mnormed_cvg u :
  cvgn [normed series u] -> cvgn (series u).
Proof.
move=> /cauchy_cvgP/cauchy_seriesP u_ncvg;
apply /cauchy_cvgP /cauchy_seriesP => e /u_ncvg P.
near=> n;
apply le_lt_trans with
  (y:=`|\sum_(n.1 <= k < n.2) `|u k| |).
by rewrite ger0_norm (ler_norm_sum, sumr_ge0).
near: n; apply P. Unshelve. end_near.
Qed.

Definition mulx1 A B := mc^-1 *: (A *x B).
Local Notation "x *x1 y" := (mulx1 x y) (at level 45, left associativity).

Lemma normM1 : forall A B, `|A *x1 B| <= `|A| * `|B|.
Proof.
by move=> A B;
rewrite /mulx1 normrZ -[leRHS]mul1r ger0_norm -?(mulVf mc_neq0)
  -?mulrA ?ler_wpM2l ?invr_ge0 // mulrA normMC.
Qed.

HB.instance Definition _ := @isMulNormed.Build R C V mulx1 normM1.

End MCNormedTheory.

Section MulNormedTheory.

Variable (R : realType) (C : extNumType R) (V : completeNormedModType C).
Variable (mulx : mulNormed V).
Implicit Type x y A B: V.
Implicit Types u v : V ^nat.

Lemma normM : forall A B, `|mulx A B| <= `|A| * `|B|.
Proof.
by move=> A B;
rewrite -[leRHS]mul1r mulrA -(@mc_eq1 _ _ _ mulx) normMC.
Qed.

End MulNormedTheory.

Section BiMulNormedTheory.

Variable (R : realType) (C : extNumType R) (V : completeNormedModType C).
Variable (mulx : biMulNormed V).
Implicit Type x y A B: V.
Implicit Types u v : V ^nat.

Local Notation "x *x y" := (mulx x y) (at level 45, left associativity).
Local Notation "x \*x y" := (fun i => (x i) *x (y i))
                                      (at level 45, left associativity).
Local Notation "x \o*x y" := (fun i => (y i) *x x)
                                      (at level 45, left associativity).
Local Notation "x \*ox y" := (fun i => x *x (y i))
                                      (at level 45, left associativity).

Lemma mulx_continuous : continuous (fun z : V * V => mulx z.1 z.2).
Proof.
by apply/bilinear_continuousP =>*; rewrite ?(linearBl, linearBr)// normM.
Qed.

Lemma mcvgM u v x y:
  u @ \oo --> x -> v @ \oo --> y -> u \*x v @ \oo --> x *x y.
Proof.
move=> *; apply: continuous2_cvg =>//;
exact: mulx_continuous (x,y).
Qed.

Lemma is_mcvgM u v:
  cvgn u -> cvgn v -> cvgn (u \*x v).
Proof. by have := cvgP _ (mcvgM _ _); apply. Qed.

Lemma mlimM u v:
  cvgn u -> cvgn v -> limn (u \*x v) = limn u *x limn v.
Proof.
by move => ? ?; apply: cvg_lim => //; apply: mcvgM.
Qed.

Lemma mcvgMl u x y:
  u @ \oo --> y -> x \o*x u @ \oo --> y *x x.
Proof.
by move => ?; apply: mcvgM => //; exact: cvg_cst.
Qed.

Lemma is_mcvgMl u x:
  cvgn u -> cvgn (x \o*x u).
Proof. by have := cvgP _ (mcvgMl _); apply. Qed.

Lemma mlimMl u x:
  cvgn u -> limn (x \o*x u) = limn u *x x.
Proof.
by move => Hu; apply: cvg_lim => //; apply: mcvgMl.
Qed.

Lemma mcvgMr u x y:
  u @ \oo --> y -> x \*ox u @ \oo --> x *x y.
Proof.
by apply: mcvgM => //; exact: cvg_cst.
Qed.

Lemma is_mcvgMr u x:
  cvgn u -> cvgn (x \*ox u).
Proof. by have := cvgP _ (mcvgMr _); apply. Qed.

Lemma mlimMr u x:
  cvgn u -> limn (x \*ox u) = x *x limn u.
Proof.
by move => Hu; apply: cvg_lim => //; apply: mcvgMr.
Qed.

Lemma mseriesMl u x:
  series (x \o*x u) = x \o*x series u.
Proof.
by apply: funext=> n;
rewrite /series /= linear_suml.
Qed.

Lemma mseriesMr u x:
  series (x \*ox u) = x \*ox series u.
Proof.
by apply: funext=> n;
rewrite /series /= linear_sumr.
Qed.

Definition conv u v :=
  [sequence \sum_(i < n.+1) (u (n-i)%N *x v i)]_n.
Local Notation " u `* v " := (conv u v) (at level 40, left associativity).

Lemma eq_tagged (n:nat) (x y: {i : 'I_n & 'I_i.+1}) :
  (val(tag x) = val(tag y)
  /\ if (val(tag x)).+1 =P (val(tag y)).+1 is ReflectT eq then
    cast_ord eq (tagged x) = tagged y else Logic.True)
-> x = y.
Proof.
case: x=> [[x Hnx] [p /= Hxp]].
case: y=> [[y Hny] [q /= Hyq]] [Hxy].
case: y /Hxy Hny Hyq => Hny Hxq.
case: eqP=>// p0 /(f_equal val) /= Hpq.
case: q /Hpq Hxq => Hxq.
by rewrite (Prop_irrelevance Hnx Hny) (Prop_irrelevance Hxp Hxq).
Qed.

Lemma cauchy_reindex (S : numFieldType) (u v : S ^nat) n:
  \sum_(s < n) \sum_(j < s.+1) u (s - j)%N * v j
  = \sum_(s < n) u (n - s.+1)%N * \sum_(j < s.+1) v j.
Proof.
under [RHS]eq_big_seq do rewrite mulr_sumr.
rewrite !sig_big_dep /=.
have Hs: forall (s : 'I_n) (j : 'I_s.+1), (n + j - s.+1 < n)%N
  by move=> [s Hsn] [j /= Hjs]; rewrite ltn_subLR addnC ?ltn_add2r ?ltn_addl.
have Hj: forall (s : 'I_n) (j : 'I_s.+1), (j < (n + j - s.+1).+1)%N
  by move=> [s Hsn] [j /= Hjs]; rewrite ltnS (subDnCA _ Hsn) leq_addr.
pose I := {s : 'I_n & 'I_s.+1}.
pose h : I -> I := (fun p : I => @Tagged 'I_n (Ordinal (Hs (tag p) (tagged p)))
                  (fun s : 'I_n => 'I_s.+1) (Ordinal (Hj (tag p) (tagged p)))).
rewrite [RHS](reindex h) /=.
have Heq: forall j : I,
  (n - (n + tagged j - (tag j).+1).+1)%N = (tag j - tagged j)%N
  by move=> [[s Hsn] [j /= Hjs]]; rewrite subnSK ?ltn_addr// -subnBA// subKn//;
  apply: (leq_trans (leq_subr j s) (ltnW Hsn)).
by under [RHS]eq_big_seq do rewrite Heq.
suff: forall x : I, h (h x) = x by exists h.
move=> [[x Hnx] [p /= Hxp]]; apply: eq_tagged; split.
by rewrite /= subnSK ?ltn_addr// subKn// (ltnW (ltn_addr p Hnx)).
by case: eqP =>//= H0; apply /val_inj.
Qed.

Lemma cauchy_BMreindex u v n:
  \sum_(s < n) \sum_(j < s.+1) (u (s - j)%N *x v j)
  = \sum_(s < n) (u (n - s.+1)%N *x \sum_(j < s.+1) v j).
Proof.
under [RHS]eq_big_seq do rewrite linear_sumr.
rewrite !sig_big_dep /=.
have Hs: forall (s : 'I_n) (j : 'I_s.+1), (n + j - s.+1 < n)%N
  by move=> [s Hsn] [j /= Hjs]; rewrite ltn_subLR addnC ?ltn_add2r ?ltn_addl.
have Hj: forall (s : 'I_n) (j : 'I_s.+1), (j < (n + j - s.+1).+1)%N
  by move=> [s Hsn] [j /= Hjs]; rewrite ltnS (subDnCA _ Hsn) leq_addr.
pose I := {s : 'I_n & 'I_s.+1}.
pose h : I -> I := (fun p : I => @Tagged 'I_n (Ordinal (Hs (tag p) (tagged p)))
                  (fun s : 'I_n => 'I_s.+1) (Ordinal (Hj (tag p) (tagged p)))).
rewrite [RHS](reindex h) /=.
have Heq: forall j : I,
  (n - (n + tagged j - (tag j).+1).+1)%N = (tag j - tagged j)%N
  by move=> [[s Hsn] [j /= Hjs]]; rewrite subnSK ?ltn_addr// -subnBA// subKn//;
  apply: (leq_trans (leq_subr j s) (ltnW Hsn)).
by under [RHS]eq_big_seq do rewrite Heq.
suff: forall x : I, h (h x) = x by exists h.
move=> [[x Hnx] [p /= Hxp]]; apply: eq_tagged; split.
by rewrite /= subnSK ?ltn_addr// subKn// (ltnW (ltn_addr p Hnx)).
by case: eqP =>//= H0; apply /val_inj.
Qed.

Lemma bigmax_ge_id_ord N (x : C) u :
  0 <= x -> x <= \big[maxr/x]_(i < N) normr (u i).
Proof.
elim/big_rec: _ => //= [[i Hi] y _] Hxy Hx.
rewrite comparable_le_max.
- apply /orP; right; apply: (Hxy Hx).
- apply: real_comparable; apply: ger0_real=>//.
  apply: (le_trans Hx (Hxy Hx)).
Qed.

Lemma le_bigmax_ord (i0 N : nat) u (x : C) :
  0 <= x -> (i0 < N)%N -> normr (u i0) <= \big[maxr/x]_(i < N) normr (u i).
Proof. 
move=> Hx Hi0; pose j:= Ordinal Hi0.
have i0j: normr (u i0) = normr (u j) by [].
have := mem_index_enum j. elim: (index_enum 'I_N) => //= a l.
rewrite inE !i0j=> IH /orP [/eqP ->|/IH H]; rewrite big_cons comparable_le_max.
2,4 : by apply: (real_comparable (normr_real _));
      apply: (bigmax_real _ (ger0_real Hx))=> p _;
      apply: normr_real.
- by apply /orP; left.
- by apply /orP; right.
Qed.
  
Lemma mcvg_seriesC u v x y (x' : C):
  series u @ \oo --> x ->
  [normed series u] @ \oo --> x' ->
  series v @ \oo --> y ->
  series (u `* v) @ \oo --> x *x y.
Proof.
move=>Su Snu Sv; move:{+}Su {+}Snu {+}Sv.
move=> /cvgrPdistC_lt /= Hsu /cvgrPdistC_lt /= Hnsu /cvgrPdistC_lt /= Hsv.
have Csu : cvgn (series u) by apply /cvg_ex; exists x.
apply /cvgrPdistC_lt => e He.
have He2: 0 < e / 2 by rewrite divr_gt0 ?ltr0Sn.
have Hx': 0 <= x' by
  move: Snu; rewrite cvgn_limnE // => [[ <- csnu]];
  apply: etlimn_ge => // n;
  rewrite /= /series sumr_ge0.
move: (Hsv _ (mulr_gt0 (divr_gt0 ltr01 (ltr_wpDr Hx' ltr01))
  (divr_gt0 He2 (ltr0Sn _ 1)))) => [N /= _];
rewrite /subset /= => HN.
move: (cvg_series_cvg_0 Csu) => /cvgrPdistC_lt /= Hu.
pose MB := \big[maxr/1]_(i < N) normr (\sum_(j < i.+1) v j - y).
have HMB0: MB > 0 by exact: (lt_le_trans ltr01
    (bigmax_ge_id_ord _ (fun i=> (\sum_(j < i.+1) v j - y)) ler01)).
move: (Hu _ (divr_gt0 (divr_gt0 (divr_gt0 He2 (ltr0Sn _ 1))
      (ltr0Sn _ N)) HMB0)) => [M _ HM].
near=> n.
rewrite /series /conv /= big_mkord cauchy_BMreindex
  (distm_lt_split (z:=\sum_(s < n) (u (n - s.+1)%N *x y))) -?sumrB //.
- under eq_big_seq do rewrite -linearBr.
  apply: (le_lt_trans (ler_norm_sum _ _ _));
  apply: (le_lt_trans (ler_sum _ _)) => [s _|];
  first exact: normM.
  near: n; exists (N + M)%N => // n /= HNMn.
  rewrite -(big_mkord xpredT (fun i => `|u (n - i.+1)%N| *
    `|\sum_(j < i.+1) v j - y|)) (big_cat_nat _ _ _ (leq0n N)) //=;
  last by rewrite -(leq_add2r M) (leq_trans HNMn (leq_addr _ _)).
  have ->: e / 2 = e / 2 / 2 + e / 2 / 2
  by rewrite -(mulr1 (e/2/2)) -mulrDr;
  have ->: 1 + 1 = 2 by []; rewrite mulfVK ?lt0r_neq0.
  apply: ltrD.
  - apply: (le_lt_trans (ler_sum_nat _
      (G := fun i=> e / 2 / 2 / N.+1%:R / MB * MB)));
    last by under eq_bigr do rewrite (mulfVK (lt0r_neq0 HMB0));
    rewrite sumr_const_nat subn0 -(mulr_natr _ N) mulrAC ltr_pdivrMr //
      ltr_pM2l ?ltr_nat // divr_gt0 //.
    move=> i Hi; apply: (ler_pM (normr_ge0 _) (normr_ge0 _)).
    - apply: ltW; move: HM;
      rewrite /subset /= -(subr0 (u _)); apply.
      by rewrite -(leq_add2l N) (leq_trans HNMn) // addnBCA ?leq_addr //;
      apply: (leq_trans (n:=N));
      last by rewrite -(leq_add2r M) (leq_trans HNMn (leq_addr _ _)).
    - exact: (le_bigmax_ord (fun i=> \sum_(j < i.+1) v j - y)).
  - apply: (le_lt_trans (ler_sum_nat _)).
    - move=> i Hi; apply: (ler_wpM2l (normr_ge0 _)); apply: ltW.
      have ->: \sum_(j < i.+1) v j = series v i.+1 by rewrite seriesEord.
      by apply: (HN _ (leqW _))=>//; move: Hi => /andP [].
    rewrite /= -mulr_suml !mulrA mulr1 !ltr_pM2r ?invr_gt0 // -[ltRHS]mul1r
      ltr_pM2r // (ltr_pdivrMr _ _ (ltr_wpDr Hx' ltr01)) mul1r.
    apply: (le_lt_trans _ (ltr_pwDl ltr01 (lexx x')));
    apply: (le_trans (y:= series (fun i : nat => normr (u i)) n)).
    rewrite [leRHS]big_nat_rev [leRHS](big_cat_nat _ (n:=N)) //=;
    last by rewrite -(leq_add2r M) (leq_trans HNMn (leq_addr _ _)).
    by apply: (ler_wpDl (sumr_ge0 _ (fun _ _ => normr_ge0 _)));
    apply: ler_sum_nat => i _; rewrite add0n.
    move: Snu; rewrite cvgn_limnE // => [[ <- Cnsu]];
    apply: etnondecreasing_cvgn_le =>// i j Hij.
    by rewrite /series /= [leRHS](big_cat_nat _ (n:=i)) //=;
    apply: (ler_wpDr (sumr_ge0 _ _)).
- have ->: \sum_(s < n) (u (n - s.+1)%N *x y) = \sum_(s < n) (u s *x y)
  by rewrite -(big_mkord xpredT (fun s => u s *x y)) big_rev_mkord subn0.
  rewrite -linear_suml -linearBl;
  apply: (le_lt_trans (normM _ _ _));
  apply: (le_lt_trans (ler_wpM2l (normr_ge0 _) (ler_wpDl ler01 (lexx _)))).
  rewrite -ltr_pdivlMr -?(big_mkord xpredT);
  last exact: ltr_wpDr (normr_ge0 _) ltr01.
  near: n. apply: Hsu.
  apply: (divr_gt0 He2 (ltr_wpDr (normr_ge0 _) ltr01)).
Unshelve. end_near.
Qed.

Lemma mlim_seriesM u v:
  cvgn [normed series u] -> cvgn (series v) ->
  limn [sequence \sum_(i<n) \sum_(j<n) (u i *x v j) ]_n
    = limn [sequence \sum_(s<n) \sum_(k<s.+1) (u (s-k)%N *x v k)]_n.
Proof.
move => Hsnu Hsv.
have Hsu: cvgn (series u) by apply: mnormed_cvg.
have ->: [sequence \sum_(i < n) \sum_(j < n) (u i *x v j)]_n
  = (series u) \*x (series v) by
  apply: funext => n;
  rewrite /series /= linear_suml big_mkord;
  apply: eq_bigr => ? _ /=;
  rewrite linear_sumr big_mkord.
have <-: series (u `* v) = [sequence \sum_(s<n) \sum_(k<s.+1) (u (s-k)%N *x v k) ]_n by
  apply: funext => n;
  rewrite /series /conv /= big_mkord.
rewrite mlimM //; symmetry.
apply: cvg_lim =>//.
apply: (mcvg_seriesC (x' := limn [normed series u])) =>//.
Qed.

Lemma is_mcvg_seriesC u v:
  cvgn [normed series u] -> cvgn (series v) ->
  cvgn (series (u `* v)).
Proof. 
move => Hnsu Hsv.
have Hsu: cvgn (series u) by apply: mnormed_cvg.
apply: (cvgP ((limn (series u)) *x (limn (series v)))).
exact: mcvg_seriesC Hsu Hnsu Hsv.
Qed.

Lemma mlim_seriesC u v:
  cvgn [normed series u] -> cvgn (series v) ->
  limn (series (u `* v)) = limn (series u) *x limn (series v).
Proof. 
move => Hsu Hsv.
have ->: series (u `* v) = [sequence \sum_(s<n) \sum_(k<s.+1) (u (s-k)%N *x v k) ]_n by
  apply: funext => n;
  rewrite /series /conv /= big_mkord.
rewrite -mlimM //;
try by apply: mnormed_cvg.
have ->: series u \*x series v = [sequence \sum_(i<n) \sum_(j<n) (u i *x v j)]_n by
  apply: funext => n;
  rewrite /series /= linear_suml big_mkord;
  apply: eq_bigr => ? _ /=;
  rewrite linear_sumr big_mkord.
by rewrite mlim_seriesM.
Qed.

End BiMulNormedTheory.

Section series.
Local Open Scope classical_set_scope.

Local Notation R := hermitian.R.
Local Notation C := hermitian.C.

Local Notation r2cC := (GRing.RMorphism.clone _ _ (real_complex R) _).
Local Notation c2rC := (@complex.Re R).

Section exponential_series_cvg.

Variable (H : completeNormedModType C).
Variable (idm : H) (mulx : biMulNormed1 idm).
Implicit Type x : H.
Implicit Type u : H ^nat.
Import Monoid.

Local Notation "x *x y" := (mulx x y) (at level 45, left associativity).
Local Notation "x \*x y" := (fun i => (x i) *x (y i))
                                      (at level 45, left associativity).
Local Notation "x \o*x y" := (fun i => (y i) *x x)
                                      (at level 45, left associativity).
Local Notation "x \*ox y" := (fun i => x *x (y i))
                                      (at level 45, left associativity).

Definition expx x n := nosimpl (@iterop H n mulx x idm).

Local Notation "1" := idm.
Local Notation "x ^x n" := (expx x n) (at level 29, left associativity).

Lemma expxS x n : x ^x n.+1 = x *x x ^x n.
Proof. by case: n => //; rewrite opm1. Qed.

Definition expM_coeff x := [sequence (n`!%:R^-1) *: x ^x n ]_n.
Local Notation expm := expM_coeff.
Local Notation expr := exp_coeff.

Lemma exp_norm_ubounded x k:
  `|x ^x k| <= `|1 : H| * (`|x| ^+ k).
Proof.
elim: k => [|n IHn].
- by rewrite !expr0 mulr1.
- by rewrite expxS exprS (le_trans (normM _ _ _)) // mulrCA ler_wpM2l.
Qed.

Lemma r2cCM (x y: R):
  r2cC (x * y) = r2cC x * r2cC y :> R[i].
Proof. exact: rmorphM. Qed.

Lemma c2rCM (x y: R[i])
  (Hx: x \is Num.real) (Hy: y \is Num.real):
    c2rC (x * y) = c2rC x * c2rC y.
Proof.
apply: (@r2c_inj R C).
by rewrite rmorphM !c2rK ?realM.
Qed.

Lemma c2rCX (x: R[i]) (Hx: x \is Num.real) k:
  c2rC (x ^+ k) = (c2rC x) ^+ k.
Proof.
by elim: k => [|n IHn];
rewrite ?rmorph1 // !exprS !c2rCM ?IHn //;
apply realX.
Qed.

Lemma rc_div (x: R[i]) (Hx: x \is Num.real) (y: R): 
  (complex.Re x / y)%:C = x / (y%:C).
Proof.
by rewrite rmorphM /= realcI RRe_real.
Qed.

Lemma mnormed_le_exp x k:
  `|expm x k| <= `|1 : H| * r2cC (expr (c2rC `|x|) k).
Proof.
rewrite /expm /expr /= -c2rCX ?ger0_real // normvZ /=.
apply: le_trans.
- apply: ler_wpM2l.
  auto. apply: exp_norm_ubounded.
- rewrite ger0_norm;
  last by rewrite invr_ge0 ler0n.
  by rewrite mulrCA ler_wpM2l // divcM3 rc_div
    ?natrC // realX ?realM ?ger0_real ?mc_ge0.
Qed.

Definition expM x := limn (series (expM_coeff x)).

Lemma normed_expM_is_cvg x : cvgn [normed series (expm x)].
Proof.
rewrite /normed_series_of /= /series /=.
apply: (cnondecreasing_is_cvgn
  (M := `|1 : H| * r2cC (expR (c2rC `|x|)))).
- by apply /nondecreasing_seqP => n;
  rewrite big_nat_recr //= lerDl.
- move => n.
  apply: le_trans.
  - apply: ler_sum_nat => i Hi.
    apply: mnormed_le_exp.
  - rewrite -mulr_sumr ler_wpM2l // -raddf_sum ler_r2c.
    apply: nondecreasing_cvgn_le.
    - apply: nondecreasing_series => m t.
      apply: exp_coeff_ge0.
      rewrite -ler0c RRe_real ?ger0_real //.
    - apply: is_cvg_series_exp_coeff.
Qed.

Lemma expM_is_cvg x : cvgn (series (expm x)).
Proof. exact: (mnormed_cvg (@normed_expM_is_cvg x)). Qed.

End exponential_series_cvg.

Section C_expM.

Lemma CexpM_coeff_eqR (x : C) i (Hx : x \is Num.real):
  expM_coeff *%R x i = r2cC (exp_coeff (c2rC x) i).
Proof.
by rewrite /expM_coeff /exp_coeff /scale /= mulrC
  r2cCM /= realcI natrC -c2rCX ?RRe_real ?realX.
Qed.

Lemma CexpM_eqR (x : C) (Hx : x \is Num.real):
  expM *%R x = r2cC (expR (c2rC x)).
Proof.
rewrite /expR /expM -climn_mapV;
[ |apply: r2c_continuous |apply: is_cvg_series_exp_coeff].
by have ->: series (expM_coeff *%R x)
  = (r2cC \o series (exp_coeff (complex.Re x)))%FUN
by apply: funext => i /=; rewrite /series /= raddf_sum;
  apply: eq_bigr => k _; rewrite CexpM_coeff_eqR.
Qed.

End C_expM.

Section chsf_expM.

Variable H: chsType.
Implicit Types u v: H.
Implicit Types A B: 'End(H).
Import HermitianTopology.

Definition commer A B := (A \o B) - (B \o A).

Fixpoint xcom n A B :=
  match n with
  | O => B
  | S n => commer A (xcom n A B)
  end.
Local Notation "^ n [ A , B ]" := (xcom n A B).

Lemma xcom0 A B: ^0[A,B] = B.
Proof. by []. Qed.

Lemma xcom1 A B: ^1[A,B] = commer A B.
Proof. by []. Qed.

Lemma xcom2 A B: ^2[A,B] = commer A (commer A B).
Proof. by []. Qed.

Lemma commer_eqn A B:
  commer A B = A * B + B * (-A).
Proof. by rewrite mulrN. Qed.

Lemma sum_nat_recl (T: zmodType) n m (F: nat -> T) :
  (m <= n)%N ->
  \sum_(m <= i < n.+1) F i = (F m) + (\sum_(m <= i < n) F i.+1).
Proof. exact: big_nat_recl. Qed.

Lemma sum_nat_recr (T: zmodType) n m (F: nat -> T) :
  (m <= n)%N ->
  \sum_(m <= i < n.+1) F i = (\sum_(m <= i < n) F i) + (F n).
Proof. exact: big_nat_recr. Qed.

Lemma xcom_sum_bino n A B:
  ^n[A,B] = \sum_(0 <= k < n.+1) 'C(n,k)%:R *: (A ^+ (n-k) * B * (-A) ^+ k).
Proof.
elim: n => [|n IHn /=]; first by
  rewrite big_nat1 subn0 bin0 scale1r !expr0 mulr1 mul1r.
rewrite IHn commer_eqn mulr_sumr mulr_suml.
have ->: \sum_(0 <= i < n.+1)
          A * (('C(n, i))%:R *: (A ^+ (n - i) * B * (- A) ^+ i))
    = A ^+ (n.+1) * B * (-A) ^+ 0 + \sum_(0 <= i < n)
      'C(n,i.+1)%:R *: (A ^+ (n.+1 - i.+1) * B * (-A) ^+ i.+1)
by rewrite sum_nat_recl // bin0 scale1r !mulrA subn0 exprS;
f_equal; apply: eq_big_nat => k Hk;
rewrite -scalerAr !mulrA -exprS subnS subSS prednK ?subn_gt0.
have ->: \sum_(0 <= i < n.+1)
        ('C(n, i))%:R *: (A ^+ (n - i) * B * (- A) ^+ i) * - A
    = \sum_(0 <= i < n) 'C(n,i)%:R *: (A ^+ (n.+1 - i.+1) * B * (-A) ^+ i.+1)
    + A ^+ 0 * B * (-A) ^+ (n.+1)
by rewrite sum_nat_recr // binn scale1r -!mulrA subnn exprSr
  addrC [RHS]addrC; f_equal; apply: eq_bigr => k _;
rewrite -scalerAl -!mulrA -exprSr subSS.
by rewrite sum_nat_recr // sum_nat_recl // bin0 binn
  !scale1r subn0 subnn -!addrA; f_equal;
rewrite addrA addrC [RHS]addrC -big_split; f_equal;
apply: eq_bigr => k _ /=; rewrite -scalerDl binS mulrnDr.
Qed.

Local Notation expM := (expM (@comp_lfun C H H H)).
Local Notation expM_coeff := (expM_coeff (@comp_lfun C H H H)).

Lemma sum_xcom n A B:
  \sum_(k < n.+1)
    (expM_coeff A (n-k)%N) * (B * (expM_coeff (-A) k))
  = n`!%:R^-1 *: ^n[A, B].
Proof.
rewrite /expM_coeff xcom_sum_bino scaler_sumr big_mkord;
apply: eq_bigr => [[k Hk]];
rewrite -(@bin_fact n k) // !natrM scalerA !invfM mulrC !mulrA divff;
last by rewrite lt0r_neq0 // ltr0n bin_gt0.
by rewrite -scalerAl -scalerAr -scalerAl scalerA mul1r.
Qed.

Lemma chsf_compE A B : A * B = A \o B.
Proof. by []. Qed.

Lemma expM_trans_xcom A B:
  (expM A) * B * (expM (-A)) = limn [series (n`!%:R^-1) *: ^n[A,B]]_n.
Proof.
have LB: limn [sequence B]_n = B by exact: lim_cst.
rewrite /expM -{1}LB !chsf_compE -!mlimM /=.
2: apply: is_mcvgMl.
5: exact: is_cvg_cst.
all: try exact: expM_is_cvg.
have ->: (fun i => series (expM_coeff A) i \o B \o series (expM_coeff (-A)) i)
  = [sequence \sum_(i < n) \sum_(j < n)
          ((expM_coeff A i) \o (B \o (expM_coeff (-A) j)))]_n by
apply: funext => n;
  rewrite /series /= -!chsf_compE !mulr_suml big_mkord;
  apply: eq_bigr => ? _ /=;
  rewrite mulr_sumr big_mkord;
  under eq_bigr do rewrite comp_lfunA. 
have ->: [series (n`!%:R^-1 *: ^ n [A, B])]_n
  = [sequence \sum_(s < n) \sum_(k < s.+1)
((expM_coeff A (s-k)%N) \o (B \o (expM_coeff (-A) k)))]_n by
  apply: funext => n;
  rewrite /series /= big_mkord;
  under eq_bigr do rewrite sum_xcom.
apply: (mlim_seriesM _ (v := fun i => B \o (expM_coeff (-A)) i));
first exact: normed_expM_is_cvg.
rewrite mseriesMr /=;
apply: is_mcvgMr; exact: expM_is_cvg.
Qed.

End chsf_expM.

End series.