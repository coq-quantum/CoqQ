From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp cardinality mathcomp_extra
  classical_sets functions.
From mathcomp.analysis Require Import ereal reals signed topology 
  prodnormedzmodule normedtype sequences.
From mathcomp.analysis Require Import -(notations)forms.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import mcextra mcaextra notation mxpred extnum cpo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order Order.Theory GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import VNorm.Exports VOrder.Exports.
Import ExtNumTopology.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*                Topology of R[i] and vector space over R[i]                 *)
(* -------------------------------------------------------------------------- *)
(* Specify extnum theory for R[i] : topology/theory of R[i], 'M[R[i]] and     *)
(*    finNormedModType R[i]                                                   *)
(* convergence w.r.t. lowner order of matrices                                *)
(* denmx forms CPO                                                            *)
(******************************************************************************)

Module CTopology.

Section C_extNumType.
Import Num.Def Num.Theory.
Variable (R : realType).
Notation C := R[i].

HB.instance Definition _ := NormedModule.copy C C^o.

Let r2cC := real_complex R : {rmorphism R -> C}.
Let c2rC := (@complex.Re R).

Lemma continuous_c2rC : continuous c2rC.
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb]; apply/nbhs_ballP.
have Pe: (e%:C) > 0 by rewrite ltc0R.
exists e%:C =>//=; move=> y /= Pxy; apply Pb; move: Pxy.
by rewrite -!ball_normE /ball_/=/c2rC -raddfB/= -ltcR; apply/le_lt_trans/normc_ge_Re.
Qed.

Lemma c2rC_linear (a : R) (b c : C) : 
  c2rC ((r2cC a) * b + c) = a * (c2rC b) + c2rC c.
Proof. 
by rewrite/r2cC/c2rC/= raddfD/=; f_equal; case: b=>br bi=>/=; rewrite mul0r subr0.
Qed.

Let mx2c (m : 'rV[R]_2) := (m 0 0 +i* m 0 1)%C.
Let mx2c_norm (m : 'rV[R]_2) := complex.Re `|mx2c m|.

Lemma mx2c_is_additive : additive mx2c.
Proof. by move=>m n; rewrite/mx2c !mxE; simpc. Qed.
#[local]
HB.instance Definition _ := GRing.isAdditive.Build 'rV_2 R[i] mx2c mx2c_is_additive.

Lemma mx2c_continuous : continuous mx2c.
Proof.
move=> x s/= /nbhs_ballP [/=[e1 e2] /andP[/eqP e2eq0 e1gt0] Pb]; 
apply/nbhs_ballP; exists (e1/(Num.sqrt 2))=>//=; first by rewrite divr_gt0//.
move=>y/=; rewrite{1}/ball/=/mx_ball=>P; apply Pb.
move: (P 0 0) (P 0 1); rewrite -!ball_normE/ball_ /= e2eq0 /mx2c; simpc.
rewrite -![`| _ | < _ / _](ltr_pXn2r (_ : (0 < 2)%N)) ?real_normK ?num_real// 
  ?nnegrE// ?divr_ge0// ?ltW//= => P1 P2.
rewrite -[e1]gtr0_norm// -sqrtr_sqr ltr_sqrt ?exprn_gt0//.
by apply: (lt_le_trans (ltrD P1 P2)); rewrite expr_div_n sqr_sqrtr// -splitr.
Qed.

Program Definition mx2c_vnorm_mixin := @isVNorm.Build _ _ mx2c_norm _ _ _.
Next Obligation.
move=>x y; move: (ler_normD (mx2c x) (mx2c y)).
by rewrite lecE/mx2c_norm !raddfD/==>/andP[].
Qed.
Next Obligation.
move=>x/ComplexField.Normc.eq0_normc/eqP; rewrite eq_complex/==>/andP[/eqP P1/eqP P2].
apply/matrixP=>i j; rewrite ord1 mxE; case: j=>m; case: m=>//=[Pi|n]; last case: n=>//Pi.
rewrite -P1. 2: rewrite -P2. all: by f_equal; apply/val_inj.
Qed.
Next Obligation.
by move=>a x; rewrite/mx2c_norm/= !mxE !exprMn -mulrDr sqrtrM ?sqr_ge0// sqrtr_sqr.
Qed.

Local Canonical mx2c_vnorm := VNorm.Pack (VNorm.Class mx2c_vnorm_mixin).

Lemma C_bounded_compact (a : C): compact [set x : C | `|x| <= a].
Proof.
case E: (a \is Num.real).
rewrite (_ : mkset _ = mx2c @` [set x : 'rV[R]_2 | mx2c_vnorm x <= complex.Re a]).
apply: continuous_compact.
apply: continuous_subspaceT=>x/= ?; apply: mx2c_continuous.
apply: compact_mnorm_le.
rewrite predeqE=>[[x1 x2]]/=; split=>[Px|[y Py1 Py2]].
exists (\row_j ((j == 0)%:R * x1 + (j == 1)%:R * x2)).
1,2: by rewrite/mx2c/mx2c_norm/=!mxE/= !mul0r !mul1r addr0 add0r// -lecR RRe_real.
by rewrite -Py2 lecE Py1 andbT/= -eqcR/=; apply/eqP/RIm_real.
rewrite (_ : mkset _ = set0).
apply: compact0.
rewrite predeqE=>x/=; split=>// P; move: E; 
by rewrite Num.Theory.realE (le_trans (Num.Theory.normr_ge0 x) P).
Qed.

HB.instance Definition _ := @NumField_isExtNum.Build R C 
  r2cC c2rC (@lecR R) (@erefl R) (@RRe_real R) continuous_c2rC c2rC_linear C_bounded_compact.

Lemma C_compact_minmax (S : set C) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> y <= x)) /\
    (exists2 x, S x & (forall y, S y -> x <= y)).
Proof. exact: extNum_compact_minmax. Qed.

Lemma C_compact_max (S : set C) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> y <= x)).
Proof. exact: extNum_compact_max. Qed.

Lemma C_compact_min (S : set C) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> x <= y)).
Proof. exact: extNum_compact_min. Qed.

Lemma C_complete (F : set_system C) : ProperFilter F -> cauchy F -> cvg F.
Proof. exact: extNum_complete. Qed.

HB.instance Definition _ := Uniform_isComplete.Build C C_complete.

End C_extNumType.
End CTopology.
Export CTopology.

Section C_sequence.
Variable (R: realType).
Local Notation C := R[i].
Implicit Type (f g: nat -> C) (n: nat) (s a b : C).

Lemma Chausdorff : hausdorff_space C. Proof. exact: ethausdorff. Qed.

Lemma cclosed_real : closed [set x : C | x \is Num.real].
Proof. exact: etclosed_real. Qed.

Lemma C_ltr_add_invr (y x : C) : y < x -> exists k, y + k.+1%:R^-1 < x.
Proof. exact: extNum_ltr_add_invr. Qed.

Lemma C_archi (x : C) : 0 < x -> exists k, k.+1%:R^-1 < x.
Proof. exact: extNum_archi. Qed.

Lemma C_bounded_subsvg (f : nat -> C) b : (forall i, `|f i| <= b) -> 
  exists (h: nat -> nat), (forall n, (h n.+1 > h n)%N) /\ cvgn (f \o h).
Proof. exact: extNum_bounded_subsvg. Qed.

Lemma ccvgn_limnE f a : f @ \oo --> a <-> limn f = a /\ cvgn f.
Proof. exact: (cvgn_limnE f a Chausdorff). Qed.

Lemma ccvgn_cst a : (fun n:nat=>a) @ \oo --> a. Proof. exact: cvg_cst. Qed.
Lemma is_ccvgn_cst a : cvgn (fun n:nat=>a). Proof. exact: is_cvg_cst. Qed.
Lemma climn_cst a : limn (fun n:nat=>a) = a. Proof. exact: lim_cst. Qed.
Lemma ccvgnN f a : f @ \oo --> a -> (- f) @ \oo --> - a. Proof. exact: cvgN. Qed.
Lemma is_ccvgnN f : cvgn f -> cvgn (- f). Proof. exact: is_cvgN. Qed.
Lemma is_ccvgnNE f : cvgn (- f) = cvgn f. Proof. exact: is_cvgNE. Qed.
Lemma ccvgnMn f n a : f @ \oo --> a -> ((@GRing.natmul _)^~n \o f) @ \oo --> a *+ n. Proof. exact: cvgMn. Qed.
Lemma is_ccvgnMn f n : cvgn f -> cvgn ((@GRing.natmul _)^~n \o f). Proof. exact: is_cvgMn. Qed.
Lemma ccvgnD f g a b : f @ \oo --> a -> g @ \oo --> b -> (f + g) @ \oo --> a + b. Proof. exact: cvgD. Qed.
Lemma is_ccvgnD f g : cvgn f -> cvgn g -> cvgn (f + g). Proof. exact: is_cvgD. Qed.
Lemma ccvgnB f g a b : f @ \oo --> a -> g @ \oo --> b -> (f - g) @ \oo --> a - b. Proof. exact: cvgB. Qed.
Lemma is_ccvgnB f g : cvgn f -> cvgn g -> cvgn (f - g). Proof. exact: is_cvgB. Qed.
Lemma is_ccvgnDlE f g : cvgn g -> cvgn (f + g) = cvgn f. Proof. exact: is_cvgDlE. Qed.
Lemma is_ccvgnDrE f g : cvgn f -> cvgn (f + g) = cvgn g. Proof. exact: is_cvgDrE. Qed.
Lemma ccvgnM f g a b : f @ \oo --> a -> g @ \oo --> b -> (f * g) @ \oo --> a * b. Proof. exact: cvgZ. Qed.
Lemma is_ccvgnM f g : cvgn f -> cvgn g -> cvgn (f * g). Proof. exact: is_cvgZ. Qed.
Lemma ccvgnMl f a b (g := fun=>b): f @ \oo --> a -> f * g @ \oo --> a * b. Proof. exact: cvgZl. Qed.
Lemma ccvgnMr g a b (f := fun=>a): g @ \oo --> b -> f * g @ \oo --> a * b. Proof. exact: cvgZr. Qed.
Lemma is_ccvgnMr g a (f := fun=> a) : cvgn g -> cvgn (f * g). Proof. exact: is_cvgZr. Qed.
Lemma is_ccvgnMrE g a (f := fun=> a) : a != 0 -> cvgn (f * g) = cvgn g. Proof. exact: is_cvgZrE. Qed.
Lemma is_ccvgnMl f a (g := fun=> a) : cvgn f -> cvgn (f * g). Proof. exact: is_cvgMl. Qed.
Lemma is_ccvgnMlE f a (g := fun=> a) : a != 0 -> cvgn (f * g) = cvgn f. Proof. exact: is_cvgMlE. Qed.
Lemma ccvgn_norm f a : f @ \oo --> a -> (Num.norm \o f) @ \oo --> `|a|. Proof. exact: cvg_norm. Qed.
Lemma is_ccvgn_norm f : cvgn f -> cvgn (Num.norm \o f). Proof. exact: is_cvg_norm. Qed.
Lemma climnN f : cvgn f -> limn (- f) = - limn f. Proof. exact: limN. Qed.
Lemma climnD f g : cvgn f -> cvgn g -> limn (f + g) = limn f + limn g. Proof. exact: limD. Qed.
Lemma climnB f g : cvgn f -> cvgn g -> limn (f - g) = limn f - limn g. Proof. exact: limB. Qed.
Lemma climnM f g : cvgn f -> cvgn g -> limn (f * g) = limn f * limn g. Proof. exact: limM. Qed.
Lemma climn_norm f : cvgn f -> limn (Num.norm \o f) = `|limn f|. Proof. exact: lim_norm. Qed.
Lemma climnV f : limn f != 0 -> limn ((fun x => (f x)^-1)) = (limn f)^-1. Proof. exact: limV. Qed.

Lemma ccvgn_map f a (V : completeType) (h : C -> V) :
  continuous h -> f @ \oo --> a -> (h \o f) @ \oo --> h a.
Proof. exact: etcvg_map. Qed. 

Lemma ccvgn_mapV (V : completeType) (h : V -> C) (h' : nat -> V) (a : V) :
  continuous h -> h' @ \oo --> a -> (h \o h') @ \oo --> h a.
Proof. exact: etcvg_mapV. Qed. 

Lemma is_ccvgn_map f (V : completeType) (h : C -> V) :
  continuous h -> cvgn f -> cvgn (h \o f).
Proof. exact: is_etcvg_map. Qed.

Lemma is_ccvgn_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvgn h' -> cvgn (h \o h').
Proof. exact: is_etcvg_mapV. Qed.

Lemma climn_map f (V : completeType) (h : C -> V) :
  hausdorff_space V -> continuous h -> cvgn f -> limn (h \o f) = h (limn f).
Proof. by move=>hV ch; move/(ccvgn_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma climn_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvgn h' -> limn (h \o h') = h (limn h').
Proof. by move=>ch; move/(ccvgn_mapV ch)/cvg_lim=>/(_ Chausdorff). Qed.

Lemma ccvgn_limnP f a :
  f @ \oo --> a <-> forall e : C, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvgn_limnP. Qed.

Lemma ccvgn_subseqP f a : 
  f @ \oo --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) @ \oo --> a).
Proof. exact: cvgn_subseqP. Qed.

Lemma ccvgn_subseqPN f a :
  ~ (f @ \oo --> a) <-> exists (e : C) (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvgn_subseqPN. Qed.

Definition ccauchy_seq f := forall e : C, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> `| f i - f j | < e.

Lemma ccauchy_seqP f : ccauchy_seq f <-> cvgn f.
Proof. exact: cauchy_seqP. Qed.

Definition ccvgn_seq f a := 
  forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> `| a - f i | < e.

Lemma ccvgn_seqP f a : ccvgn_seq f a <-> f @ \oo --> a.
Proof. exact: cvgn_seqP. Qed.

Lemma re_continuous : continuous (@Re R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e%:C =>//=. by rewrite ltcR.
move=> y /= Pxy. apply (Pb (Re y)). move: Pxy.
rewrite -ball_normE/= /ball/= -raddfB/= -ltcR.
apply: (le_lt_trans (normc_ge_Re _)).
Qed.

Lemma im_continuous : continuous (@Im R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e%:C =>//=. by rewrite ltcR.
move=> y /= Pxy. apply (Pb (Im y)). move: Pxy.
rewrite -ball_normE/= /ball/= -raddfB/= -ltcR.
apply: (le_lt_trans (normc_ge_Im _)).
Qed.

Lemma rc_continuous : continuous (@real_complex R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (Re e) =>//=. by apply real_gt0.
move=> y /= Pxy. apply (Pb y%:C). move: Pxy.
by rewrite -ball_normE/= /ball/= -raddfB/= -ltcR cgt0_real// normc_real.
Qed.

Lemma ic_continuous : continuous (@im_complex R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (Re e) =>//=. by apply real_gt0.
move=> y /= Pxy. apply (Pb y%:Ci). move: Pxy.
rewrite -ball_normE/= /ball/= -(@raddfB _ _ (im_complex_additive R))/=.
by rewrite normc_im -ltcR cgt0_real// normc_real.
Qed.

Lemma conjC_continuous (K : numClosedFieldType) : continuous (@Num.conj_op K).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (e) =>//=.
move=> y /= Pxy. apply (Pb (@Num.conj_op K y)). move: Pxy.
by rewrite /ball/= -rmorphB Num.Theory.norm_conjC.
Qed.
Lemma ccvgn_conj f a : f @ \oo --> a -> (Num.conj_op \o f) @ \oo --> (Num.conj_op a).
Proof. by apply: continuous_cvg; apply conjC_continuous. Qed.
Lemma is_ccvgn_conj f : cvgn f -> cvgn (Num.conj_op \o f).
Proof. by move=> /ccvgn_conj /cvgP. Qed.
Lemma is_ccvgn_conjE f : cvgn (Num.conj_op \o f) = cvgn f.
Proof. 
rewrite propeqE; split.
have P1: f = (Num.conj_op \o (Num.conj_op \o f))
by apply/funext=>x/=; rewrite Num.Theory.conjCK.
rewrite [in X in _ -> X]P1. all: apply is_ccvgn_conj.
Qed.
Lemma climn_conj f : cvgn f -> limn (Num.conj_op \o f) = Num.conj_op (limn f).
Proof. by move=> ?; apply: cvg_lim; [apply: Chausdorff | apply: ccvgn_conj]. Qed.

End C_sequence.

Section C_monotone.
Variable (R : realType).
Local Notation C := R[i].

Lemma climn_split (u_ : C ^nat) :
  cvgn u_ -> limn u_ = (limn ((@Re _) \o u_))%:C + (limn ((@Im _) \o u_))%:Ci.
Proof.
move=>Pcvg; move: Pcvg {+}Pcvg.
move=>/(ccvgn_map (@re_continuous R))/(cvg_lim (@Rhausdorff _))->.
move=>/(ccvgn_map (@im_continuous R))/(cvg_lim (@Rhausdorff _))->.
by rewrite complex_split.
Qed.

Lemma Re_cvgn_realV (u_ : C ^nat) a : 
  u_ @ \oo --> a -> ((@Re _) \o u_) @ \oo --> Re a.
Proof. exact: c2r_cvgn_realV. Qed.

Lemma cnondecreasing_is_cvgn (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> cvgn u_.
Proof. exact: etnondecreasing_is_cvgn. Qed.

Lemma cnondecreasing_cvgn (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> 
        u_ @ \oo --> (limn ((@Re _) \o u_))%:C + (Im M)%:Ci.
Proof.
move=>P1 P2. move: (cnondecreasing_is_cvgn P1 P2)=>P3.
rewrite ccvgn_limnE; split=>//. rewrite climn_split//.
do 2 f_equal. suff ->: (Im (R:=R) \o u_) = (fun=>Im M) by apply: lim_cst.
by apply/funext=>i; move: (P2 i); rewrite/= lecE=>/andP[/eqP->].
Qed.

Lemma cnonincreasing_is_cvgn (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> cvgn u_.
Proof. exact: etnonincreasing_is_cvgn. Qed.

Lemma cnonincreasing_cvgn (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> 
        u_ @ \oo --> (limn ((@Re _) \o u_))%:C + (Im M)%:Ci.
Proof.
move=>P1 P2. move: (cnonincreasing_is_cvgn P1 P2)=>P3.
rewrite ccvgn_limnE; split=>//. rewrite climn_split//.
do 2 f_equal. suff ->: (Im (R:=R) \o u_) = (fun=>Im M) by apply: lim_cst.
by apply/funext=>i; move: (P2 i); rewrite/= lecE=>/andP[/eqP->].
Qed.

Lemma cnondecreasing_cvgn_le (u_ : C ^nat) :
       nondecreasing_seq u_ -> cvgn u_ -> (forall n : nat, u_ n <= limn u_).
Proof. exact: etnondecreasing_cvgn_le. Qed.

Lemma cnonincreasing_cvgn_ge (u_ : C ^nat) : 
  nonincreasing_seq u_ -> cvgn u_ -> (forall n, limn u_ <= u_ n).
Proof. exact: etnonincreasing_cvgn_ge. Qed.

Lemma cclosed_ge (y:C) : closed [set x : C | y <= x].
Proof. exact: etclosed_ge. Qed.

Lemma cclosed_le (y : C) : closed [set x : C | x <= y].
Proof. exact: etclosed_le. Qed.

Lemma cclosed_eq (y : C) : closed [set x : C | x = y].
Proof. exact: etclosed_eq. Qed.

Lemma climn_ge_near (x : C) (u : C ^nat) : 
  cvgn u -> (\forall n \near \oo, x <= u n) -> x <= limn u.
Proof. exact: etlimn_ge_near. Qed.

Lemma climn_le_near (x : C) (u : C ^nat) : 
  cvgn u -> (\forall n \near \oo, x >= u n) -> x >= limn u.
Proof. exact: etlimn_le_near. Qed.

Lemma lt_climn (u : C ^nat) (x : C) : nondecreasing_seq u -> cvgn u -> x < limn u ->
  \forall n \near \oo, x <= u n.
Proof. exact: lt_etlimn. Qed.

Lemma gt_climn (u : C ^nat) (x : C) : nonincreasing_seq u -> cvgn u -> x > limn u ->
  \forall n \near \oo, x >= u n.
Proof. exact: gt_etlimn. Qed.

Lemma ler_climn_near (u_ v_ : C ^nat) : cvgn u_ -> cvgn v_ ->
  (\forall n \near \oo, u_ n <= v_ n) -> limn u_ <= limn v_.
Proof. exact: ler_etlimn_near. Qed.

Lemma climn_ge (x : C) (u : C ^nat) : cvgn u -> (forall n, x <= u n) -> x <= limn u.
Proof. exact: etlimn_ge. Qed.

Lemma climn_le (x : C) (u : C ^nat) : cvgn u -> (forall n, u n <= x) -> limn u <= x.
Proof. exact: etlimn_le. Qed.

Lemma ler_climn (u_ v_ : C^nat) : cvgn u_ -> cvgn v_ ->
  (forall n, u_ n <= v_ n) -> limn u_ <= limn v_.
Proof. exact: ler_etlimn. Qed.

End C_monotone.

Section C_sup.
Variable (R : realType).
Local Notation C := R[i].

Definition csup : set C -> C := nosimpl (@etsup R C).
Definition cinf : set C -> C := nosimpl (@etinf R C).

Lemma csup_adherent (E : set C) (eps : C) : 0 < eps ->
  has_sup E -> exists2 e : C, E e & (csup E - eps) < e.
Proof. exact: etsup_adherent. Qed. 

Lemma csup_upper_bound E : has_sup E -> ubound E (csup E).
Proof. exact: etsup_upper_bound. Qed.

Lemma csup_least_ubound E : has_sup E -> lbound (ubound E) (csup E).
Proof. exact: etsup_least_ubound. Qed.

End C_sup.

Section CmxCvg.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m,n).
Implicit Type (f g: nat -> M) (r: nat) (a b : M) (s : nat -> C) (k: C).

Lemma cmxhausdorff p q : hausdorff_space 'M[C]_(p,q).
Proof. exact: mxhausdorff. Qed.

Lemma cmxcvgn_limnE f a : f @ \oo --> a <-> limn f = a /\ cvgn f. Proof. exact: mxcvgn_limnE. Qed.
Lemma cmxcvgn_limn f a : f @ \oo --> a -> limn f = a. Proof. by move=>/cmxcvgn_limnE[]. Qed.
Lemma cmxcvgn_cst a : (fun n:nat=>a) @ \oo --> a. Proof. exact: cvg_cst. Qed.
Lemma is_cmxcvgn_cst a : cvgn (fun n:nat=>a). Proof. exact: is_mxcvgn_cst. Qed.
Lemma cmxlimn_cst a : limn (fun n:nat=>a) = a. Proof. exact: mxlimn_cst. Qed.
Lemma cmxcvgnN f a : f @ \oo --> a -> (- f) @ \oo --> - a. Proof. exact: mxcvgnN. Qed.
Lemma is_cmxcvgnN f : cvgn f -> cvgn (- f). Proof. by move=> /cmxcvgnN /cvgP. Qed.
Lemma is_cmxcvgnNE f : cvgn (- f) = cvgn f.
Proof. by rewrite propeqE; split=> /cmxcvgnN; rewrite ?opprK => /cvgP. Qed.
Lemma cmxcvgnMn f r a : f @ \oo --> a -> ((@GRing.natmul _)^~r \o f) @ \oo --> a *+ r.
Proof. exact: mxcvgnMn. Qed.
Lemma is_cmxcvgnMn f r : cvgn f -> cvgn ((@GRing.natmul _)^~r \o f).
Proof. by move=> /(@cmxcvgnMn _ r) /cvgP. Qed.
Lemma cmxcvgnD f g a b : f @ \oo --> a -> g @ \oo --> b -> (f + g) @ \oo --> a + b.
Proof. exact: mxcvgnD. Qed.
Lemma is_cmxcvgnD f g : cvgn f -> cvgn g -> cvgn (f + g).
Proof. by have := cvgP _ (cmxcvgnD _ _); apply. Qed.
Lemma cmxcvgnB f g a b : f @ \oo --> a -> g @ \oo --> b -> (f - g) @ \oo --> a - b.
Proof. exact: mxcvgnB. Qed.
Lemma is_cmxcvgnB f g : cvgn f -> cvgn g -> cvgn (f - g).
Proof. by have := cvgP _ (cmxcvgnB _ _); apply. Qed.
Lemma is_cmxcvgnDlE f g : cvgn g -> cvgn (f + g) = cvgn f.
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cmxcvgnD; apply.
by move=> /is_cmxcvgnB /(_ g_cvg); rewrite addrK.
Qed.
Lemma is_cmxcvgnDrE f g : cvgn f -> cvgn (f + g) = cvgn g.
Proof. by rewrite addrC; apply: is_cmxcvgnDlE. Qed.
Lemma cmxcvgnZ s f k a : s @ \oo --> k -> f @ \oo --> a -> (fun x => s x *: f x) @ \oo --> k *: a.
Proof. exact: mxcvgnZ. Qed.
Lemma is_cmxcvgnZ s f : cvgn s -> cvgn f -> cvgn (fun x => s x *: f x).
Proof. by have := cvgP _ (cmxcvgnZ _ _); apply. Qed.
Lemma cmxcvgnZl s k a : s @ \oo --> k -> (fun x => s x *: a) @ \oo --> k *: a.
Proof. by move=> ?; apply: cmxcvgnZ => //; exact: cmxcvgn_cst. Qed.
Lemma is_cmxcvgnZl s a : cvgn s -> cvgn (fun x => s x *: a).
Proof. by have := cvgP _ (cmxcvgnZl  _); apply. Qed.
Lemma is_cmxcvgnZlE s a : a != 0 -> cvgn (fun x => s x *: a) = cvgn s.
Proof. exact: is_mxcvgnZlE. Qed.
Lemma cmxcvgnZr k f a : f @ \oo --> a -> k \*: f @ \oo --> k *: a.
Proof. apply: cmxcvgnZ => //; exact: ccvgn_cst. Qed.
Lemma is_cmxcvgnZr k f : cvgn f -> cvgn (k *: f ).
Proof. by have := cvgP _ (cmxcvgnZr  _); apply. Qed.
Lemma is_cmxcvgnZrE k f : k != 0 -> cvgn (k *: f) = cvgn f.
Proof.
move=> k_neq0; rewrite propeqE; split=>[/(@cmxcvgnZr k^-1)|/(@cmxcvgnZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

(* exact works, but very slow *)
Lemma cmxlimnN f : cvgn f -> limn (- f) = - limn f.
Proof. by move=>?; apply/cmxcvgn_limn/cmxcvgnN. Qed.  
Lemma cmxlimnD f g : cvgn f -> cvgn g -> limn (f + g) = limn f + limn g.
Proof. by move=>Pf Pg; apply/cmxcvgn_limn/cmxcvgnD; [apply Pf|apply Pg]. Qed.
Lemma cmxlimnB f g : cvgn f -> cvgn g -> limn (f - g) = limn f - limn g.
Proof. move=> Pf Pg; apply/cmxcvgn_limn/cmxcvgnB; [apply Pf|apply Pg]. Qed.
Lemma cmxlimnZ s f : cvgn s -> cvgn f -> limn (fun x => s x *: f x) = limn s *: limn f.
Proof. move=> Ps Pf; apply/cmxcvgn_limn/cmxcvgnZ;[apply Ps|apply Pf]. Qed.
Lemma cmxlimnZl s a : cvgn s -> limn (fun x => s x *: a) = limn s *: a.
Proof. by move=> ?; apply/cmxcvgn_limn/cmxcvgnZl. Qed.
Lemma cmxlimnZr k f : cvgn f -> limn (k *: f) = k *: limn f.
Proof.  by move=> ?; apply/cmxcvgn_limn/mxcvgnZr. Qed.

(* since only nontrivial matrix are canonical to normZmodType *)
Lemma cmxcvgn_norm (h : nat->'M[C]_(m.+1,n.+1)) (x : 'M[C]_(m.+1,n.+1)) : 
  h @ \oo --> x -> (Num.norm \o h) @ \oo --> `|x|.
Proof. exact: cvg_norm. Qed.
Lemma is_cmxcvgn_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvgn h -> cvgn (Num.norm \o h).
Proof. exact: is_cvg_norm. Qed.
Lemma cmxlimn_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvgn h -> limn (Num.norm \o h) = `|limn h|.
Proof. exact: lim_norm. Qed.

Lemma cmxcvgn_map f a (V : completeType) (h : M -> V) :
  continuous h -> f @ \oo --> a -> (h \o f) @ \oo --> h a.
Proof. exact: mxcvgn_map. Qed.
Lemma cmxcvgn_mapV (V : completeType) (h : V -> M) (h' : nat -> V) (a : V) :
  continuous h -> h' @ \oo --> a -> (h \o h') @ \oo --> h a.
Proof. exact: mxcvgn_mapV. Qed.
Lemma is_cmxcvgn_map f (V : completeType) (h : M -> V) :
  continuous h -> cvgn f -> cvgn (h \o f).
Proof. exact: is_mxcvgn_map. Qed.
Lemma is_cmxcvgn_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvgn h' -> cvgn (h \o h').
Proof. exact: is_mxcvgn_mapV. Qed.
Lemma cmxlimn_map f a (V : completeType) (h : M -> V) :
  hausdorff_space V -> continuous h -> cvgn f -> limn (h \o f) = h (limn f).
Proof. exact: mxlimn_map. Qed.
Lemma cmxlimn_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvgn h' -> limn (h \o h') = h (limn h').
Proof. exact: mxlimn_mapV. Qed.

Lemma cmxcvgn_limnP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  h @ \oo --> x <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> mx_norm (h n - x) < e.
Proof. exact: mxcvgn_limnP. Qed.
Lemma cmxcvgn_subseqP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) : 
  h @ \oo --> x <-> (forall (h': nat -> nat), (forall n, (h' n.+1 > h' n)%N) -> (h \o h') @ \oo --> x).
Proof. exact: mxcvgn_subseqP. Qed.
Lemma cmxcvgn_subseqPN p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  ~ (h @ \oo --> x) <-> exists e (h': nat -> nat), 
    (forall n, (h' n.+1 > h' n)%N) /\ 0 < e /\ (forall n, mx_norm ((h \o h') n - x) >= e).
Proof. exact: mxcvgn_subseqPN. Qed.

Lemma cmxnatmul_continuous p : continuous (fun x : M => x *+ p).
Proof. exact: mxnatmul_continuous. Qed.
Lemma cmxscale_continuous : continuous (fun z : C * M => z.1 *: z.2).
Proof. exact: mxscale_continuous. Qed.
Lemma cmxscaler_continuous k : continuous (fun x : M => k *: x).
Proof. exact: mxscaler_continuous. Qed.
Lemma cmxscalel_continuous (x : M) : continuous (fun k : C => k *: x).
Proof. exact: mxscalel_continuous. Qed.
Lemma cmxopp_continuous : continuous (fun x : M => -x).
Proof. exact: mxopp_continuous. Qed.
Lemma cmxadd_continuous : continuous (fun z : M * M => z.1 + z.2).
Proof. exact: mxadd_continuous. Qed.
Lemma cmxaddr_continuous a : continuous (fun z : M => a + z).
Proof. exact: mxaddr_continuous. Qed.
Lemma cmxaddl_continuous a : continuous (fun z : M => z + a).
Proof. exact: mxaddl_continuous. Qed.

Definition cmxcauchy_seq f := 
  forall e : C, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> mx_norm (f i - f j) < e.

Definition cmxcvgn_seq f a := 
  forall e : C, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> mx_norm (a - f i) < e.

Lemma cmxcauchy_seqP f : cmxcauchy_seq f <-> cvgn f.
Proof. exact: mxcauchy_seqP. Qed.
Lemma cmxcvgn_seqP f a : cmxcvgn_seq f a <-> f @ \oo --> a.
Proof. exact: mxcvgn_seqP. Qed.

End CmxCvg.

Section CmxLinearContinuous.
Variable (R: realType).
Local Notation C := R[i].

Lemma cmxlinear_continuous m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q)) :
  linear f -> continuous f.
Proof. exact: mxlinear_continuous. Qed.

Lemma cmxcvgn_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  linear f -> u @ \oo --> a -> (fun x=> f (u x)) @ \oo --> (f a).
Proof. exact: mxcvgn_lfun. Qed.

Lemma is_cmxcvgn_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
(u : nat -> 'M[C]_(m,n))  : linear f -> cvgn u -> cvgn (f \o u).
Proof. exact: is_mxcvgn_lfun. Qed.

Lemma cmxlimn_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) : 
  linear f -> cvgn u -> limn (f \o u) = f (limn u).
Proof. exact: mxlimn_lfun. Qed.

Lemma cmxclosed_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
    linear f -> closed A -> closed (f @^-1` A).
Proof. exact: mxclosed_comp. Qed.

Lemma cmxopen_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> open A -> open (f @^-1` A).
Proof. exact: mxopen_comp. Qed.

Lemma cmxscalar_continuous m n (f : 'M[C]_(m,n) -> C) :
  scalar f -> continuous f.
Proof. exact: mxscalar_continuous. Qed.

Lemma cmxcvgn_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  scalar f -> u @ \oo --> a -> (fun x=> f (u x)) @ \oo --> (f a).
Proof. exact: mxcvgn_sfun. Qed.

Lemma is_cmxcvgn_sfun m n (f : 'M[C]_(m,n) -> C) (u : nat -> 'M[C]_(m,n)) : 
  scalar f -> cvgn u -> cvgn (f \o u).
Proof. exact: is_mxcvgn_sfun. Qed.

Lemma cmxlimn_sfun m n (f : 'M[C]_(m,n) -> C) (u : nat -> 'M[C]_(m,n)) : 
  scalar f -> cvgn u -> limn (f \o u) = f (limn u).
Proof. exact: mxlimn_sfun. Qed.

Lemma cmxcclosed_comp m n (f : 'M[C]_(m,n) -> C) (A : set C) :
  scalar f -> closed A -> closed (f @^-1` A).
Proof. exact: mxcclosed_comp. Qed.

Lemma cmxcopen_comp m n (f : 'M[C]_(m,n) -> C) (A : set C) :
  scalar f -> open A -> open (f @^-1` A).
Proof. exact: mxcopen_comp. Qed.

End CmxLinearContinuous.

Section CmxNormExtNumEqual.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m,n).
Implicit Type (mnorm : vnorm M).

Lemma cmxlimn_mnorm mnorm (f : M ^nat) : 
  cvgn f -> limn (mnorm \o f) = mnorm (limn f).
Proof. exact: mxlimn_mnorm. Qed.

Lemma cmnorm_lbounded mnorm : exists2 c : C, 
  0 < c & forall x,  c * mx_norm x <= mnorm x.
Proof. exact: mnorm_lbounded. Qed.

Lemma compact_cmnorm_le mnorm (y : C) : compact [set x : M | mnorm x <= y].
Proof. exact: compact_mnorm_le. Qed.

Lemma compact_cmnorm_sphere mnorm (y : C) : compact [set x : M | mnorm x = y].
Proof. exact: compact_mnorm_sphere. Qed.

Lemma cmx_Bolzano_Weierstrass (f : nat -> 'M[C]_(m,n)) (M : C) :
  (forall n, mx_norm (f n) <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvgn (f \o h).
Proof. exact: Bolzano_Weierstrass. Qed.

(* bounded seq: cvgn <-> any cvgn subseq to a *)
Lemma cmxcvgn_subseqP_cvgn (f : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (M : C): 
  (forall n, mx_norm (f n) <= M) ->
  f @ \oo --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) 
    -> cvgn (f \o h) -> limn (f \o h) = a).
Proof. exact: mxcvgn_subseqP_cvgn. Qed.

Lemma cmnorm_bounded mnorm1 mnorm2 :
  exists2 c : C, 0 < c & forall x : M, mnorm1 x <= c * mnorm2 x.
Proof. exact: mnorm_bounded. Qed.

Lemma cmxcauchy_seqv_eq mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f -> cauchy_seqv mnorm2 f.
Proof. exact: mxcauchy_seqv_eq. Qed.

Lemma cmxcauchy_seqvE mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f <-> cauchy_seqv mnorm2 f.
Proof. exact: mxcauchy_seqvE. Qed.

Lemma cmxcauchy_seqE mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> mxcauchy_seq f.
Proof. exact: mxcauchy_seqE. Qed.

Lemma cmxcauchy_seqvP mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> cvgn f.
Proof. exact: mxcauchy_seqvP. Qed.

End CmxNormExtNumEqual.

HB.instance Definition _ (C : numFieldType) := Lmodule_hasFinDim.Build _
  C^o (regular_vect_iso C).
HB.instance Definition _ (C : numFieldType) := FinNormedModule.copy C C^o.
HB.instance Definition _ (R : rcfType) := FinNormedModule.copy R[i] (R[i]: numFieldType).

Section C_vorderFinNormedModType.
Variable (R : realType).
Local Notation C := R[i].

Program Definition C_vorderMixin := POrderedLmodule_isVOrder.Build R[i] R[i]^o _ _.
Next Obligation. by intros; rewrite Num.Theory.lerD2r. Qed.
Next Obligation. by intros; rewrite Num.Theory.ler_pM2l. Qed.

HB.instance Definition _ := C_vorderMixin.
(*?*)
Canonical C_vorderType := VOrder.Pack (VOrder.Class C_vorderMixin).

HB.instance Definition _ := VOrder.copy C C^o.

HB.instance Definition C_vorderFinNormedModMixin := 
  FinNormedModule_isVOrderFinNormedModule.Build C C (@cclosed_ge _ 0).
Canonical ctopology_C__canonical__extnum_VOrderFinNormedModule := 
  VOrderFinNormedModule.Pack (VOrderFinNormedModule.Class C_vorderFinNormedModMixin).

End C_vorderFinNormedModType.

Section CmxLownerOrder.
Import MxLownerOrder Num.Def Num.Theory.
Variable (R : realType).
Local Notation C := R[i].

Lemma form_nng_neq0 n x : reflect (exists u: 'cV[C]_n, 
  (0 < \tr (u^*t *m u)) && (\tr (u^*t *m x *m u) \isn't Num.nneg))
  (~~ ((0 : 'M[C]_n) ⊑ x)).
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

Lemma psdmx_closed n : (closed [set x : 'M[C]_n | (0 : 'M[C]_n) ⊑ x])%classic.
Proof.
case: n=>[x/= _|n]; first by rewrite !mx_dim0. 
rewrite (_ : mkset _ = ~` [set x | ~ (0 : 'M[C]_n.+1) ⊑ x]); last first.
by rewrite predeqE=>x /=; rewrite notK.
rewrite closedC. move=> x /= /negP /form_nng_neq0 [u /andP[P1 /Cnng_open [e egt0 Pe]]].
move: (@mnorm_bounded _ C n.+1 n.+1 (@trnorm _ _ _ : vnorm _) (@mx_norm _ _ _ : vnorm _))=>[c cgt0 Pc].
rewrite nbhs_ballP. 
exists (e/c/(\tr (u^*t *m u)))=>/=[|y/=]; first by do 2 apply divr_gt0=>//.
rewrite -ball_normE/= mulrAC ltr_pdivlMr// =>Pb; apply/negP/form_nng_neq0.
exists u; apply/andP; split=>//; apply Pe.
rewrite /ball/= -linearB/= -mulmxBl -mulmxBr.
apply: (le_lt_trans (trnorm_inner _ _)).
rewrite mulrC -lter_pdivlMl// mulrC. apply: (le_lt_trans _ Pb).
by move: (Pc (y - x))=>/=; rewrite mulrC -normrN opprB.
Qed.

Lemma trnorm_add_eq n (x y : 'M[C]_n) : (0 : 'M[C]_n) ⊑ x -> (0 : 'M[C]_n) ⊑ y 
  -> trnorm x  + trnorm y = trnorm (x + y).
Proof.
rewrite !le_lownerE !subr0=>P1 P2. move: (psdmx_add P1 P2).
move: P1 P2=>/psdmx_trnorm->/psdmx_trnorm->/psdmx_trnorm->.
by rewrite linearD.
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
  u @ \oo --> a -> ((@trnorm _ _ _) \o u) @ \oo --> \tr| a |.
Proof. exact: mxcvgn_mnorm. Qed.

Lemma is_cmxcvgn_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvgn u -> cvgn ((@trnorm _ _ _) \o u).
Proof. exact: is_mxcvgn_mnorm. Qed.

Lemma cmxlimn_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvgn u -> limn ((@trnorm _ _ _) \o u) = \tr| limn u |.
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

Let chainD (u : nat -> D) : chain u -> nondecreasing_seq (D2M \o u).
Proof. by move=>/chain_homo P i j Pij; move: (P _ _ Pij); rewrite/= leEsub. Qed.

Let Dge0 : forall (x : D), Denmx0 ⊑ x.
Proof. by move=>x/=; case: x=>m Pm; rewrite leEsub/= le_lownerE subr0; apply/denmx_psd. Qed.

Let chainD_lb (u : nat -> D) : forall i, (0:M) ⊑ (D2M \o u) i.
Proof. by move=>i/=; case: (u i)=>m Pm; rewrite/= le_lownerE subr0; apply/denmx_psd. Qed.

Let chainD_ub (u : nat -> D) : forall i, (D2M \o u) i ⊑ 1%:M.
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
move=>c Pc. move: (chainD Pc) (chainD_ub c)=>P1 P2.
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

HB.instance Definition _ := isCpo.Build ring_display D Dge0 Dlub_ub Dlub_least.

End DenmxCPO.