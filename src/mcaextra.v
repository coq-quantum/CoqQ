From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra perm.
From mathcomp.classical Require Import boolp cardinality mathcomp_extra
  classical_sets functions.
From mathcomp.analysis Require Import ereal reals exp trigo signed
  derive topology prodnormedzmodule normedtype sequences.
From mathcomp.analysis Require Import -(notations)forms.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import mcextra autonat.

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import VectorInternalTheory numFieldNormedType.Exports.

(*****************************************************************************)
(*                  Extra theories for Mathcomp-Analysis                     *)
(*****************************************************************************)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope ring_scope.

Module BiLinearReload.
Module BilinearWrapExports.
Module BilinearWrap.
Section BilinearWrap.
Variables (R : ringType) (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).
Notation mapUUV := (@Bilinear.type R U U' V s s').
Definition map_class := mapUUV.
Definition map_at_left (a : R) := mapUUV.
Definition map_at_right (b : R) := mapUUV.
Definition map_at_both (a b : R) := mapUUV.
Structure map_for_left a s_a := MapForLeft {map_for_left_map : mapUUV; _ : s a = s_a }.
Structure map_for_right b s'_b := MapForRight {map_for_right_map : mapUUV; _ : s' b = s'_b }.
Structure map_for_both a b s_a s'_b :=
  MapForBoth {map_for_both_map : mapUUV; _ : s a = s_a ; _ : s' b = s'_b }.
Definition unify_map_at_left a (f : map_at_left a) := MapForLeft f (erefl (s a)).
Definition unify_map_at_right b (f : map_at_right b) := MapForRight f (erefl (s' b)).
Definition unify_map_at_both a b (f : map_at_both a b) :=
   MapForBoth f (erefl (s a)) (erefl (s' b)).
Structure wrapped := Wrap {unwrap : mapUUV}.
Definition wrap (f : map_class) := Wrap f.
End BilinearWrap.
End BilinearWrap.

(* similar to linear, using Bilinear.type directly instead of Bilinear.map *)
Notation "{ 'bilinear' U '->' V '->' W '|' s '&' t }" := 
  (@Bilinear.type _ U%type V%type W%type s t)
  (at level 0, U at level 97, V at level 98, W at level 99, 
  format "{ 'bilinear'  U  ->  V  ->  W  |  s  &  t }") : ring_scope.
Notation "{ 'bilinear' U '->' V  '->'  W '|' s }" := 
  (@Bilinear.type _ U%type V%type W%type s.1 s.2)
  (at level 0, U at level 97, V at level 98, W at level 99, 
  format "{ 'bilinear'  U  ->  V  ->  W  |  s }") : ring_scope.
Notation "{ 'bilinear' U '->' V '->' W }" := 
  (@Bilinear.type _ U%type V%type W%type *:%R *:%R)
  (at level 0, U at level 97, V at level 98, W at level 99, 
  format "{ 'bilinear'  U  ->  V  ->  W }") : ring_scope.
Notation "{ 'biscalar' U }" := (@Bilinear.type _ U%type U%type _ *%R *%R)
  (at level 0, format "{ 'biscalar'  U }") : ring_scope.
Notation "[ 'bilinear' 'of' f 'as' g ]" := (Bilinear.clone _ _ _ _ _ _ f g)
  (at level 0, format "[ 'bilinear'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'bilinear' 'of' f ]" := (Bilinear.clone _ _ _ _ _ _ f _)
  (at level 0, format "[ 'bilinear'  'of'  f ]") : form_scope.

Coercion BilinearWrap.map_for_left_map : BilinearWrap.map_for_left >-> Bilinear.type.
Coercion BilinearWrap.map_for_right_map : BilinearWrap.map_for_right >-> Bilinear.type.
Coercion BilinearWrap.map_for_both_map : BilinearWrap.map_for_both >-> Bilinear.type.
Coercion BilinearWrap.unify_map_at_left : BilinearWrap.map_at_left >-> BilinearWrap.map_for_left.
Coercion BilinearWrap.unify_map_at_right : BilinearWrap.map_at_right >-> BilinearWrap.map_for_right.
Coercion BilinearWrap.unify_map_at_both : BilinearWrap.map_at_both >-> BilinearWrap.map_for_both.
Canonical BilinearWrap.unify_map_at_left.
Canonical BilinearWrap.unify_map_at_right.
Canonical BilinearWrap.unify_map_at_both.
Coercion BilinearWrap.unwrap : BilinearWrap.wrapped >-> Bilinear.type.
Coercion BilinearWrap.wrap : BilinearWrap.map_class >-> BilinearWrap.wrapped.
Canonical BilinearWrap.wrap.
End BilinearWrapExports.
Export BilinearWrapExports.

Section BidirectionalLinearZ.
Variable (R : ringType) (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).
Variables (S : ringType) (h h' : GRing.Scale.law S V).

Lemma linearZl (z : U') c a (h_c := h c)
  (f : BilinearWrap.map_for_left U U' s s' a h_c) (u : U) :
    f (a *: u) z = h_c (BilinearWrap.wrap f u z).
Proof. by rewrite linearZl_LR; case: f => f /= ->. Qed.

Lemma linearZr z c' b (h'_c' := h' c')
  (f : BilinearWrap.map_for_right U U' s s' b h'_c') u :
  f z (b *: u) = h'_c' (BilinearWrap.wrap f z u).
Proof. by rewrite linearZr_LR; case: f => f /= ->. Qed.

Lemma linearZlr c c' a b (h_c := h c) (h'_c' := h' c')
    (f : BilinearWrap.map_for_both U U' s s' a b h_c h'_c') u v :
  f (a *: u) (b *: v) = h_c (h'_c' (BilinearWrap.wrap f u v)).
Proof. by rewrite linearZl_LR linearZr_LR; case: f => f /= -> ->. Qed.

Lemma linearZrl c c' a b (h_c := h c) (h'_c' := h' c')
    (f : BilinearWrap.map_for_both U U' s s' a b h_c h'_c') u v :
  f (a *: u) (b *: v) = h'_c' (h_c (BilinearWrap.wrap f u v)).
Proof. by rewrite linearZr_LR/= linearZl_LR; case: f => f /= -> ->. Qed.

End BidirectionalLinearZ.
End BiLinearReload.
Export BiLinearReload.

Section BiLinearComplfun.
Local Open Scope lfun_scope.
Variable (R : comRingType) (aT vT rT : vectType R).

Lemma linear_comp_lfunl f : linear (@comp_lfun _ aT vT rT f).
Proof. by move=>a u v; rewrite comp_lfunDr comp_lfunZr. Qed.
Lemma linear_comp_lfunr f : linear ((@comp_lfun _ aT vT rT)^~ f).
Proof. by move=>a u v; rewrite comp_lfunDl comp_lfunZl. Qed.

HB.instance Definition _ := bilinear_isBilinear.Build R 'Hom(vT, rT) 'Hom(aT, vT) 'Hom(aT, rT)
  *:%R *:%R (@comp_lfun _ aT vT rT) (linear_comp_lfunr, linear_comp_lfunl).

End BiLinearComplfun.

Lemma eq_lim (T : Type) (T' : topologicalType) (F : set_system T) (f g : T -> T') :
  f =1 g -> lim (f @ F)%classic = lim (g @ F)%classic.
Proof. by move=> /funext->. Qed.

Section RealC.
Variable (R : realType).
Implicit Type (x y : R).
Notation C := R[i].

(* for convert conjc and conjC *)
Lemma conjcC : (@conjc R) = Num.conj_op. Proof. by []. Qed.
Lemma conjCc : (@Num.conj_op _ : R[i] -> R[i]) = (@conjc R). Proof. by []. Qed.
Lemma conjC_inj (x y : R[i]) : x^* = y^* -> x = y.
Proof. by move=> P; rewrite -(conjcK x) P conjcK. Qed.

Lemma natrC n : n%:R%:C = n%:R :> C. Proof. exact: raddfMn. Qed.
Lemma realcN x : (- x)%:C = - x%:C. Proof. exact: raddfN. Qed.
Lemma realcD x y : (x + y)%:C = x%:C + y%:C. Proof. exact: raddfD. Qed.
Lemma realcM x y : (x * y)%:C = x%:C * y%:C. Proof. exact: rmorphM. Qed.
Lemma realcB x y : (x - y)%:C = x%:C - y%:C. Proof. exact: raddfB. Qed.
Lemma realcMn x n : (x *+ n)%:C = x%:C *+ n. Proof. exact: raddfMn. Qed.
Lemma realcMNn x n : (x *- n)%:C = x%:C *- n. Proof. exact: raddfMNn. Qed.
Lemma realcI x : ((x^-1)%:C = x%:C^-1)%R.
Proof.
rewrite {2}/GRing.inv/= expr0n/= mul0r addr0 expr2 invfM mulrA.
case E: (x == 0). by move: E=>/eqP->; rewrite invr0 mulr0 oppr0.
by rewrite mulfV ?E// mul1r; simpc.
Qed.
Lemma realcX x n : (x^+n)%:C = x%:C^+n. Proof. exact: rmorphXn. Qed.
Lemma realcXN x n : (x^-n)%:C = x%:C^-n. Proof. by rewrite realcI realcX. Qed.
Lemma realc_sum (I : Type) (r : seq I) (P : pred I) (F : I -> R) :
  (\sum_(i <- r | P i) F i)%:C = \sum_(i <- r | P i) (F i)%:C.
Proof. exact: rmorph_sum. Qed.
Lemma realc_prod (I : Type) (r : seq I) (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i)%:C = \prod_(i <- r | P i) (F i)%:C.
Proof. exact: rmorph_prod. Qed.
Lemma realc_norm (r : R) : `|r|%:C = `|r%:C|.
Proof. by rewrite {2}/Num.norm/= expr0n/= addr0 sqrtr_sqr. Qed.
Lemma eqcR x y : (x%:C == y%:C) = (x == y).
Proof. by rewrite (inj_eq (@complexI _)). Qed.
Lemma realc_eq1 x : (x%:C == 1) = (x == 1). Proof. exact: eqcR. Qed.
Lemma realc_eq0 x : (x%:C == 0) = (x == 0). Proof. exact: eqcR. Qed.
Lemma lecR0 x : (x%:C <= 0) = (x <= 0). Proof. exact: lecR. Qed.
Lemma lec0R x : (0 <= x%:C) = (0 <= x). Proof. exact: lecR. Qed.
Lemma lecR1 x : (x%:C <= 1) = (x <= 1). Proof. exact: lecR. Qed.
Lemma lec1R x : (1 <= x%:C) = (1 <= x). Proof. exact: lecR. Qed.
Lemma ltcR0 x : (x%:C < 0) = (x < 0). Proof. exact: ltcR. Qed.
Lemma ltc0R x : (0 < x%:C) = (0 < x). Proof. exact: ltcR. Qed.
Lemma ltcR1 x : (x%:C < 1) = (x < 1). Proof. exact: ltcR. Qed.
Lemma ltc1R x : (1 < x%:C) = (1 < x). Proof. exact: ltcR. Qed.
Lemma natc_inj (a b : nat) : ((a%:R : C) = b%:R) -> a = b.
Proof. by move=>/eqP; rewrite eqr_nat=>/eqP. Qed.
Lemma eqc_nat (a b : nat) : ((a%:R : C) == b%:R) = (a == b).
Proof. exact: eqr_nat. Qed.

Lemma conjcM (x y : C) : (x * y)^* = x^* * y^*.
Proof. exact: rmorphM. Qed.
Lemma invcM (x y : C) : x^-1 * y^-1 = (x * y)^-1.
Proof. by rewrite invfM. Qed.
Lemma divcM1 (x y z : C) : x / y / z = x / (y * z).
Proof. by rewrite -mulrA invfM. Qed.
Lemma divcM2 (x y z : C) : x / y * z = x * z / y.
Proof. by rewrite -mulrA [_ * z]mulrC mulrA. Qed.
Lemma divcM3 (x y : C) : x^-1 * y = y * x^-1.
Proof. by rewrite mulrC. Qed.
Lemma divcM4 (x y z : C) : x * (y / z) = x * y / z.
Proof. by rewrite mulrA. Qed.
Lemma conjc_inv_ (x : C) : (x^-1)^* = x^*^-1.
Proof. exact: conjc_inv. Qed.
Lemma conjc_sqrt (x : nat) : (sqrtC (x%:R : C))^* = sqrtC x%:R.
Proof. by rewrite conj_Creal// ger0_real// sqrtC_ge0 ler0n. Qed.

Lemma sqrtcMK (x : nat) : sqrtC (x%:R : C) * sqrtC x%:R = x%:R.
Proof. by rewrite -expr2 sqrtCK. Qed.

Definition divc_simp := (invcM, divcM1, divcM2, divcM3, divcM4, 
  conjcM, conjc_inv_, conjc_sqrt, sqrtcMK).

Lemma conjCN1 : (-1 : C)^* = -1. Proof. by rewrite rmorphN conjC1. Qed.
Lemma oppcK (x : C) : - (- x) = x. Proof. exact: opprK. Qed.
Definition sign_simp := (conjC0, conjC1, conjCN1, mulN1r, mulrN1, 
  mulNr, mulrN, mulr1, mul1r, invrN, oppcK, addNr, addrN).

Lemma sqrtCV_nat (x : nat) n :
  (sqrtC ((x%:R : C) ^+ n)) ^-1 = sqrtC (x%:R ^-n).
Proof. by case: n=>[|n]; rewrite rootCV// exprn_ge0// ler0n. Qed.

Lemma sqrtCNV_nat (x : nat) n :
  (sqrtC ((x%:R : C) ^- n)) ^-1 = sqrtC (x%:R ^+n).
Proof. by rewrite -sqrtCV_nat invrK. Qed.

Lemma sqrtCX_nat (x : nat) n :
  sqrtC ((x%:R : C) ^+ n) = sqrtC x%:R ^+ n.
Proof. by case: n=>[|n]; rewrite ?expr0 ?sqrtC1// rootCX// ler0n. Qed.

Lemma sqrtCNX_nat (x : nat) n :
  sqrtC ((x%:R : C) ^- n) = sqrtC x%:R ^- n.
Proof. by rewrite rootCV// ?sqrtCX_nat// exprn_ge0// ler0n. Qed.

End RealC.

Definition directc (C : numFieldType) (c : C) := 
  if c == 0 then 1 else c / `|c|.

Lemma directc_norm (C : numFieldType) (c : C) : `| directc c | = 1.
Proof.
rewrite /directc; case: eqP=>[|/eqP Pc]; first by rewrite normr1.
by rewrite normrM normfV normr_id mulfV// normr_eq0.
Qed.

Lemma norm_directcE (C : numFieldType) (c : C) : `|c| = c / (directc c).
Proof.
rewrite /directc; case: eqP=>[->|/eqP Pc]; first by rewrite normr0 mul0r.
by rewrite invfM mulVKf// invrK.
Qed.

Lemma directcE (C : numFieldType) (c : C) : (directc c) * `|c| = c.
Proof. by rewrite norm_directcE mulrC mulfVK// -normr_eq0 directc_norm oner_neq0. Qed.

Lemma invf_prod (F : fieldType) I (r : seq I) (P : pred I) (f : I -> F) :
  ((\prod_(i <- r | P i) (f i))^-1 = \prod_(i <- r | P i) (f i)^-1)%R.
Proof. by elim/big_rec2: _=>[|i x y _ <-]; rewrite ?invr1// invfM. Qed.

Lemma normr_prod (F : numDomainType) I (r : seq I) (P : pred I) (f : I -> F) :
  `|(\prod_(i <- r | P i) (f i))| = \prod_(i <- r | P i) `|(f i)|.
Proof. by elim/big_rec2: _=>[|i x y _ <-]; rewrite ?normr1// normrM. Qed.

Lemma sqrt_prod (F : numClosedFieldType) I (r : seq I) (P : pred I) (f : I -> F) :
  (forall i, P i -> f i >= 0) ->
  sqrtC (\prod_(i <- r | P i) (f i)) = \prod_(i <- r | P i) sqrtC (f i).
Proof.
move=>P1; rewrite (eq_bigr (fun i=> `|f i|)) -?normr_prod.
by move=>i /P1 P2; rewrite ger0_norm.
elim/big_rec2: _=>[|i x y Pi <-]; rewrite ?normr1 ?sqrtC1//; apply/eqP.
by rewrite -(@eqrXn2 _ 2%N)// ?mulr_ge0// ?sqrtC_ge0// ?P1// 
  exprMn !sqrtCK normrM ger0_norm// P1.
Qed.

Lemma sqrtC_inv (F : numClosedFieldType) (x : F) : 
  0 <= x -> ((sqrtC x)^-1 = sqrtC (x^-1))%R.
Proof.
by move=>Px; apply/eqP; rewrite -(@eqrXn2 _ 2%N)// ?invr_ge0 
  ?sqrtC_ge0// ?invr_ge0// exprVn !sqrtCK.
Qed.

Local Open Scope classical_set_scope.

(* use the module ExtNum (R : realType) : numFieldType                        *)
(* C : extNumType R : bounded -> compact &                                    *)
(*                    r2c : {rmorphism R -> C}: bij on real & mono to <=      *)
(* both R and C belongs to ExtNum; ExtNum is enough for the things we need    *)
(* TODO: ExtNum somewhat non-standard; I haven't seen such a thing before     *)
(*       Change to a more reasonable one?                                     *)
(* Remark : alternative is to define ExtNum as a finite dimensional realType  *)
(*          but since want to treat ExtNum itself as a numFieldType, avoid    *)
(*          to canonical it as a vectType R                                   *)
(* Question: show compactness of C by reusing the compactness of matrix       *)
(*           over extNum R??                                                  *)

Lemma continuous_comp_simp (R S T : topologicalType) (f : R -> S) (g : S -> T) :
  continuous f -> continuous g -> continuous (g \o f)%FUN.
Proof. 
move=>cf cg; suff: forall x, {for x, continuous (g \o f)%FUN} by [].
move=>x. apply continuous_comp. apply cf. apply cg.
Qed.

Lemma nbhsx_ballxe {R : numDomainType} {M : pseudoMetricType R} (x : M) 
  e : 0 < e -> nbhs x (ball x e).
Proof. by move=>egt0; apply/nbhs_ballP; exists e => /=. Qed.

Lemma closedU {T : topologicalType} (A B : set T) :
  closed A -> closed B -> closed (A `|` B).
Proof.
move=>cA cB. rewrite -[_`|`_]setCK setCU closedC.
by apply/openI; rewrite openC.
Qed.

Section Extra_continuity_pseudoMetricNormedZmodType.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.

Lemma addr_continuous  (x : V) : continuous (fun z => x + z).
Proof. by move=> t; apply: (cvg_comp2 (cvg_cst _) cvg_id (@add_continuous _ _ (_, _))). Qed.

Lemma addl_continuous (x : V) : continuous (fun z => z + x).
Proof. by move=> t; apply: (cvg_comp2 cvg_id (cvg_cst _) (@add_continuous _ _ (_, _))). Qed.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=>/=x; apply/cvgrPdist_lt=> e egt0; rewrite !near_simpl/=.
near=>y; rewrite -Num.Theory.normrN opprK addrC opprB.
near: y; by apply: cvgr_dist_lt. Unshelve. end_near.
Qed.

Lemma subr_continuous (x : V) : continuous (fun z => x - z).
Proof.
have -> : (fun z=>x-z) = ((fun z=>x+z)\o(fun z=>-z))%FUN by apply/funext=>z.
apply: continuous_comp_simp. apply: opp_continuous. apply: addr_continuous.
Qed.

Context {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limDl f a : cvg (f @ F) -> lim ((fun x => f x + a) @ F) = lim (f @ F) + a.
Proof. by move=>Pf; rewrite limD// ?lim_cst//; apply: cvg_cst. Qed.

Lemma limDr a f : cvg (f @ F) -> lim ((fun x => a + f x) @ F) = a + lim (f @ F).
Proof. by move=>Pf; rewrite limD// ?lim_cst//; apply: cvg_cst. Qed.

End Extra_continuity_pseudoMetricNormedZmodType.

Section NatShift.

Lemma is_cvgn_centern N (V : topologicalType) (u_ : nat -> V) :
  cvgn [sequence u_ (n - N)%N]_n = cvgn u_.
Proof.
rewrite propeqE; split.
by rewrite cvg_centern=>/cvgP.
by rewrite -(cvg_centern N)=>/cvgP.
Qed.

Lemma is_cvgn_shiftn N (V : topologicalType) (u_ : nat -> V) :
  cvgn [sequence u_ (n + N)%N]_n = cvgn u_.
Proof.
rewrite propeqE; split.
by rewrite cvg_shiftn=>/cvgP.
by rewrite -(cvg_shiftn N)=>/cvgP.
Qed.

Lemma is_cvgn_shiftS (V : topologicalType) (u_ : nat -> V) :
  cvgn [sequence u_ n.+1]_n = cvgn u_.
Proof.
rewrite -[RHS](is_cvgn_shiftn 1).
by apply: eq_is_cvg=>n /=; rewrite addn1.
Qed.

Lemma limn_centern N (R : numFieldType) (V : pseudoMetricNormedZmodType R) (u_ : nat -> V) :
  limn [sequence u_ (n - N)%N]_n = limn u_.
Proof.
move: (EM (cvgn u_))=>[].
by move=>Pc; apply: norm_cvg_lim; rewrite cvg_centern.
by move=>Pc; rewrite (dvgP Pc); apply/dvgP; rewrite is_cvgn_centern.
Qed.

Lemma limn_shiftn N (R : numFieldType) (V : pseudoMetricNormedZmodType R) (u_ : nat -> V) :
  limn [sequence u_ (n + N)%N]_n = limn u_.
Proof.
move: (EM (cvgn u_))=>[].
by move=>Pc; apply: norm_cvg_lim; rewrite cvg_shiftn.
by move=>Pc; rewrite (dvgP Pc); apply/dvgP; rewrite is_cvgn_shiftn.
Qed.

Lemma limn_shiftS (R : numFieldType) (V : pseudoMetricNormedZmodType R) (u_ : nat -> V) :
  limn [sequence u_ n.+1]_n = limn u_.
Proof.
rewrite -[RHS](limn_shiftn 1).
by apply: eq_lim=>n /=; rewrite addn1.
Qed.

End NatShift.

(* Cauchy Sequence Characterization *)
Section CauchySeq.
Import Num.Def Num.Theory.
Variable (R: numFieldType) (V: completeNormedModType R).

(* to use cauchy_seq for other functions *)
Definition cauchy_seq  (u: nat -> V) := 
  forall e : R, 0 < e -> exists N : nat, 
    forall s t, (N <= s)%N -> (N <= t)%N -> `| u s - u t | < e.

Lemma cauchy_seqP  (u: nat -> V) : cauchy_seq u <-> cvgn u.
Proof.
split=>[P1|/cvg_cauchy/cauchyP].
  apply: cauchy_cvg; apply/cauchyP.
  rewrite /cauchy_ex=>e egt0 /=; move: (P1 _ egt0)=>[N Pn].
  exists (u N); exists N=>// s/= Ps.
  rewrite -ball_normE/=; apply Pn=>//.
rewrite /cauchy_ex=>P e egt0 /=.
have: e / 2%:R > 0 by rewrite divr_gt0// ltr0n.
move/(P _) =>[x /= [N _ PN]]; exists N=>s t Ps Pt.
move: (PN s) (PN t)=>/= /(_ Ps) P1 /(_ Pt) P2.
by move: (ball_splitr P1 P2); rewrite -ball_normE.
Qed.

(* to use cauchy_seq for other functions *)
Definition cvgn_seq  (u: nat -> V) a := 
  forall e : R, 0 < e -> exists N : nat, 
    forall s, (N <= s)%N -> `| a - u s | < e.

Lemma cvgn_seqP  (u: nat -> V) a : cvgn_seq u a <-> u @ \oo --> a.
Proof.
split=>[P1|/cvgr_dist_lt +e egt0].
rewrite cvgrPdist_le=>/= e egt0; rewrite/prop_near1 nbhs_filterE/=.
by move: (P1 _ egt0)=>[N PN]; exists N=>//= i/=/PN/ltW.
move=>/(_ e egt0); rewrite/prop_near1 nbhs_filterE=>[[N _ PN]].
by exists N=>n Pn; move: (PN n)=>/=/(_ Pn).
Qed.

Lemma nchain_ge (h: nat -> nat) :
  (forall n, (h n.+1 > h n)%N) -> forall n, (h n >= n)%N.
Proof. by move=>P1 n; elim: n=>[|n IH]; [rewrite leq0n| apply/(leq_ltn_trans IH)]. Qed.

Lemma nchain_mono (h: nat -> nat) :
  (forall n, (h n.+1 > h n)%N) -> forall n m, (n > m)%N -> (h n > h m)%N.
Proof.
move=>P1 n m; elim: n=>// n IH /ltnSE. 
rewrite leq_eqVlt=>/orP[/eqP->//|/IH H].
by apply (ltn_trans H).
Qed.

Fixpoint nseq_sig Q (P : forall n, {m : nat | Q n m}) m :=
  match m with
  | O => projT1 (P O)
  | S n => projT1 (P (nseq_sig P n))
  end.

Lemma nseq_sigE Q (P : forall n, {m : nat | Q n m}) m :
  nseq_sig P m.+1 = projT1 (P (nseq_sig P m)).
Proof. by []. Qed.

Lemma nseq_sigP Q (P : forall n, {m : nat | Q n m}) (m:nat) :
  Q (nseq_sig P m) (projT1 (P (nseq_sig P m))).
Proof. by move: (projT2 (P (nseq_sig P m))). Qed.

Lemma implyE (P Q : Prop) : (P -> Q) = ~ P \/ Q.
Proof. by rewrite -(notK (P -> Q)) not_implyE propeqE not_andP notK. Qed.

Lemma implyNE (P Q : Prop) : (P -> ~ Q) = (~ (P /\ Q)).
Proof. by rewrite implyE propeqE not_andP. Qed.

(* not exists subseq -> there is a bound *)
Lemma non_exists_nseq (P : nat -> Prop) :
  ~ (exists (h : nat -> nat), (forall n, (h n.+1 > h n)%N) /\ (forall n, P (h n)))
  -> exists N, forall n, (n >= N)%N -> ~ (P n).
Proof.
apply contra_notP. rewrite not_existsP !notK=>H.
suff H1: forall n, {m : nat | (n < m /\ P m)%N}.
exists (nseq_sig H1); split=>n.
by move: (nseq_sigP H1 n)=>[+_]; rewrite nseq_sigE.
rewrite /=; case: n=>[|n]. 
by rewrite /nseq_sig; move: (projT2 (H1 0%N))=>[].
by rewrite nseq_sigE; move: (projT2 (H1 (nseq_sig H1 n)))=>[].
move=>n; apply/cid; move: (H n.+1); apply contra_notP; 
by rewrite not_existsP notK=>H1 m; move: (H1 m); rewrite -implyNE.
Qed.

Lemma cvgn_limnP (f: nat -> V) (a: V) :
  f @ \oo --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof.
rewrite cvg_ballP; split=>+e egt0; move=>/(_ e egt0)[N Pn].
move=>P1; exists N=>n ltNn; move: (P1 n)=>/=. 
2: exists N=>// n/=/Pn.
all: rewrite -ball_normE/= -Num.Theory.normrN opprB// =>P2; by apply P2.
Qed.

Lemma cvgn_subseqP (f: nat -> V) (a: V) : 
  f @ \oo --> a
  <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N)
  -> (f \o h) @ \oo --> a).
Proof.
split=>[|H].
rewrite cvgn_limnP=>H h Ph; rewrite cvgn_limnP=>e egt0.
move: (H _ egt0)=>[N H1]; exists N=>n IH.
apply H1; by apply/(leq_trans IH)/nchain_ge.
have /H: forall n, (id n < id n.+1)%N by [].
suff ->: f \o id = f by []. by apply/funext=>n.
Qed.

Lemma cvgn_subseqPN (f: nat -> V) (a: V) :
  ~ (f @\oo --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
split; last first.
- apply contraPnot. rewrite -forallNP.
  move=>/cvgn_limnP H1 e. rewrite -forallNP=>h [P1 [P2]] /not_forallP P3.
  apply P3. move: (H1 _ P2)=>[N PN]. exists N.+1. apply/negP.
  rewrite -real_ltNge//= ?gtr0_real//. apply/PN.
  by apply: (leq_trans _ (nchain_ge P1 _)).
rewrite cvgn_limnP -existsNE=>[[e]].
rewrite not_implyP -forallNP=>[[egt0 P]].
exists e. pose P1 n := (e <= `|f n - a|) : Prop.
suff: (exists h, (forall n, (h n.+1 > h n)%N) /\ (forall n, P1 (h n))).
by move=>[h [Ph1 Ph2]]; exists h; split=>//.
move: P; apply contraPP=>/non_exists_nseq[N PN].
rewrite not_forallP notK; exists N; rewrite notK=>n/PN.
by rewrite /P1=>/negP; rewrite -real_ltNge// gtr0_real.
Qed.

Lemma cvgn_limnE (f: nat -> V) (a: V) : hausdorff_space V -> f @ \oo --> a <-> limn f = a /\ cvgn f.
Proof. 
split=>[P1|[ <-]//]. split. apply/cvg_lim. apply H.
apply P1. by move: P1=>/cvgP.
Qed.

Hypothesis (archi : forall x : R, 0 < x -> exists k, k.+1%:R^-1 < x).
Variable (f : nat -> V) (S : set V).
Hypothesis (cS : compact S) (bS : forall i, S (f i)).

Lemma compact_cluster : exists y, cluster (nbhs (f @ \oo)) y.
Proof.
set F := nbhs (f @ \oo).
have FS: F S by rewrite /F/=; exists 0%N=>// n/= _.
by move: (@cS F (fmap_proper_filter f eventually_filter) FS)
  =>/=[y /=[] _ Py]; exists y.
Qed.

Lemma foo4 y N e : cluster (nbhs (f @ \oo)) y
  -> 0 < e -> { M | (N < M)%N & `|f M - y| < e}.
Proof.
rewrite /cluster/==>P1 egt0.
have P2: nbhs (f @ \oo) (f @` [set n | (n > N)%N]) by exists N.+1=>//= t/= Pt; exists t.
move: P1=>/(_ (f @` [set n | (n > N)%N]) (ball y e) P2 (nbhsx_ballxe _ egt0))
  /=/cid[z]/=[]/cid2[M Pm <-].
by rewrite -ball_normE/= -normrN opprB=>P1; exists M.
Qed.

(* have convergence subsequence *)
Lemma cluster_subsvg : exists (h: nat -> nat), 
  (forall n, (h n.+1 > h n)%N) /\ cvgn (f \o h).
move: compact_cluster=>/=[y P2].
pose Q n m := (n < m)%N /\ `|f m - y| < 1/n.+1%:R.
have P n : {m | Q n m}.
have H1: 0 < 1/n.+1%:R :> R by rewrite divr_gt0.
by move: (foo4 n P2 H1)=>[m Pm1 Pm2]; exists m; split.
pose sf := nseq_sig P.
exists sf. have sfmn n : (sf n < sf n.+1)%N.
by move: (nseq_sigP P n)=>[+_]; rewrite /sf nseq_sigE.
split=>//.
apply/cvg_ex; exists y.
apply/cvgn_limnP=>e egt0.
move: (archi egt0)=>[N] PN.
exists N.+1=>n.
rewrite /=; case: n=>[//|n]; last first.
rewrite/sf nseq_sigE; move: (projT2 (P (nseq_sig P n)))=>[] _ P4 P5.
apply: (lt_trans P4). apply: (le_lt_trans _ PN).
rewrite mul1r lef_pV2 ?posrE// ler_nat; apply: (leq_trans P5).
by move: (nchain_ge sfmn n); rewrite/sf ltnS.
Qed.

End CauchySeq.

Lemma compA U V W T (f: U -> V) (g : V -> W) (h : W -> T) :
  h \o (g \o f) = h \o g \o f.
Proof. exact. Qed.

(* compact R set has maximum and minimum *)
Section R_compact_min_max.
Variable (R: realType).
Import Num.Theory numFieldNormedType.Exports.

Lemma compact_max (S: set R) : 
  compact S -> S !=set0 -> exists2 x, S x & (forall y, S y -> y <= x).
Proof.
move=>P1 P2; move: {+}P2=>[x Px].
have PF : ProperFilter (globally S) by apply: (@globally_properfilter _ _ x).
have ubS : has_ubound S.
move: P1=>/compact_bounded/=/(ex_bound)/==>[[M PM]].
exists M=>y Py; apply: (le_trans (ler_norm _)); by apply PM.
exists (sup S); last by apply/ubP/sup_upper_bound; split.
by move: (compact_closed (@Rhausdorff R) P1)=>/closure_id{1}->; apply closure_sup.
Qed.

Lemma compact_min (S: set R) : 
  compact S -> S !=set0 -> exists2 x, S x & (forall y, S y -> x <= y).
Proof.
move=>P1 P2; have cS : compact [set - x | x in S]
  by apply/continuous_compact=>//; apply/continuous_subspaceT=>x?; apply: opp_continuous.
have nS : [set - x | x in S] !=set0 by apply set_interval.nonemptyN.
have inS: forall x, [set - x | x in S] (-x) <-> S x.
move=>x; split=>[[y Py /oppr_inj<-//]|Px]; by exists x.
move: (compact_max cS nS)=>[x Px lex].
exists (- x)=>[|y]; first by rewrite -inS opprK.
by rewrite -inS Num.Theory.lerNl =>/lex.
Qed.

End R_compact_min_max.

Section bounded_compact_complete.
Import Num.Def Num.Theory numFieldNormedType.Exports.
Variable (C : numFieldType) (V : normedModType C).
Hypothesis (bc : forall (e : C), compact [set y : V | `|y| <= e]).

Lemma bounded_compact_shift (x : V) (e : C) : compact [set y : V | `|y-x| <= e].
Proof.
rewrite (_ : mkset _ = (fun z=>z + x) @` [set z : V | `|z| <= e]).
rewrite predeqE => z /=; split=>[P|[y Py]<-].
by exists (z - x)=>//; rewrite addrNK. by rewrite addrK.
apply: continuous_compact; last exact: bc.
by apply/continuous_subspaceT=>z ?; apply: addl_continuous.
Qed.

(* first extract the cluster point *)
Lemma bounded_compact_complete (F : set_system V) : 
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF /cauchyP F_cauchy; move: (F_cauchy _ (@ltr01 C))=>[x Px].
  pose sx := [set y : V | `|y-x| <= 1+1].
  have P1: ball x 1 `<=` sx.
  move=>y; rewrite -ball_normE/= /sx/= -normrN opprB=>P1.
  by apply/ltW; apply: (lt_le_trans P1); rewrite -subr_ge0 addrK ler01.
  have Fsx: F sx by apply: (filterS P1).
  have csx: compact sx by exact: bounded_compact_shift.
  move: (csx _ FF Fsx)=>[y /=[] _];rewrite/cluster/==>P2.
apply/cvg_ex; exists y; apply/cvg_ballP=>e egt0; rewrite -nbhs_nearE/= /nbhs/=.
have eh : e/2/2 > 0 by rewrite !divr_gt0.
move: (F_cauchy _ eh)=>/=[z Pz].
move: {+}Pz; apply: filterS; move=>/=w.
move: P2=>/(_ (ball z (e/2/2)) (ball y (e/2)) Pz)P4.
have: nbhs y (ball y (e/2)) by apply: nbhsx_ballxe; rewrite divr_gt0.
move=>/P4[t]/=[]; rewrite -ball_normE/= -normrN opprB=>Q1 Q2 Q3.
move: (le_lt_trans (ler_normD _ _) (ltrD Q3 (le_lt_trans (ler_normD _ _) (ltrD Q1 Q2)))).
by rewrite addrCA !addrA addrNK addrC !addrA addNr add0r addrC -!splitr.
Qed.

End bounded_compact_complete.

Fact fun0 (T : Type) (x : 'I_0) : T.
Proof. by case: x. Qed.

Lemma fun0E (T : Type) : all_equal_to (@fun0 T).
Proof. by move=>f; apply/funext; case. Qed.

Section FFunFirstLast.

Variables (n m : nat) (T U rT : Type).
Implicit Type t : 'I_n -> T.

Definition ftail (u : 'I_n.+1 -> T) := (fun i : 'I_n => u (fintype.lift ord0 i) ).
Definition ffirst (u : 'I_n.+1 -> T) := (fun i : 'I_n => u (fintype.lift ord_max i)).

Fact ffun_key : unit. Proof. by []. Qed.

Definition fcons_fun (x : T) (u : 'I_n -> T) :=
  (fun i : 'I_n.+1 => match unlift ord0 i with 
    | None => x | Some i => u i end ).
Definition fcons :=  locked_with ffun_key fcons_fun.
Definition frcons_fun (u : 'I_n -> T) (x : T) :=
  (fun i : 'I_n.+1 => match unlift ord_max i with 
    | None => x | Some i => u i end ).
Definition frcons := locked_with ffun_key frcons_fun.
Canonical fcons_unlockable := [unlockable fun fcons].
Canonical frcons_unlockable := [unlockable fun frcons].

Lemma fcons0 x (u : 'I_n -> T) : fcons x u ord0 = x.
Proof. by rewrite unlock; case: unliftP. Qed.
Lemma fconsE x (u : 'I_n -> T) i : fcons x u (fintype.lift ord0 i) = u i.
Proof. by rewrite unlock; case: unliftP=>// j /lift_inj->. Qed.

Lemma fconsK (u : 'I_n.+1 -> T) : fcons (u ord0) (ftail u) = u.
Proof.
by apply/funext=>i; case: (unliftP ord0 i)=>/=[j->|->]; 
  rewrite ?fconsE ?fcons0.
Qed.
Lemma fconsKV x (u : 'I_n -> T) : ftail (fcons x u) = u.
Proof. by apply/funext=>i; rewrite /ftail fconsE. Qed. 

Lemma frcons_max (u : 'I_n -> T) x : frcons u x ord_max = x.
Proof. by rewrite unlock; case: unliftP=>//= j /eqP; rewrite eq_liftF. Qed.
Lemma frconsE (u : 'I_n -> T) x (i : 'I_n) : frcons u x (fintype.lift ord_max i) = u i.
Proof. by rewrite unlock; case: unliftP=>[j/lift_inj->//|/eqP]; rewrite lift_eqF. Qed.

Lemma frconsK (u : 'I_n.+1 -> T) : frcons (ffirst u) (u ord_max) = u.
Proof.
by apply/funext=>i; case: (unliftP ord_max i)=>/=[j->|->]; 
  rewrite ?frconsE ?frcons_max.
Qed.
Lemma frconsKV (u : 'I_n -> T) x : ffirst (frcons u x) = u.
Proof. by apply/funext=>i; rewrite /ffirst frconsE. Qed. 

Variant fcons_spec : ('I_n.+1 -> T) -> Type :=
  FconsSpec x t : fcons_spec (fcons x t).

Lemma fconsP u : fcons_spec u.
Proof. by rewrite -(fconsK u); apply: (FconsSpec (u ord0) (ftail u)). Qed.

Variant frcons_spec : ('I_n.+1 -> T) -> Type :=
  FrconsSpec t x : frcons_spec (frcons t x).

Lemma frconsP u : frcons_spec u.
Proof. by rewrite -(frconsK u); apply: (FrconsSpec (ffirst u) (u ord_max)). Qed.

End FFunFirstLast.

Section FFunRev.
Implicit Type (T : Type).

Definition frev_fun {n T} (u : 'I_n -> T) := (fun i : 'I_n => u (rev_ord i) ).
Definition frev {n T} := locked_with ffun_key (@frev_fun n T).
Canonical frev_unlockable n T := [unlockable fun @frev n T].

Lemma frevE {n T} (u : 'I_n -> T) i : frev u i = u (rev_ord i).
Proof. by rewrite unlock. Qed.
Lemma frev_revE {n T} (u : 'I_n -> T) i : frev u (rev_ord i) = u i.
Proof. by rewrite frevE rev_ordK. Qed.
Lemma frevK {n T} : cancel (@frev n T) (@frev n T).
Proof. by move=>u; apply/funext=>i; rewrite frevE frev_revE. Qed.

Lemma frev_inj {n T} : injective (@frev n T).
Proof. by apply/(can_inj frevK). Qed.
Lemma frev_rcons {n T} (u : 'I_n -> T) (x : T) : frev (frcons u x) = fcons x (frev u).
Proof.
apply/funext=>i; case: (unliftP ord0 i)=>/=[j ->|->];
by rewrite !frevE ?rev_ord0 ?rev_ord_lift0 ?frconsE ?frcons_max ?fconsE ?fcons0// frevE.
Qed.
Lemma frev_cons {n T} (x : T) (u : 'I_n -> T) : frev (fcons x u) = frcons (frev u) x.
Proof. by apply/frev_inj; rewrite frev_rcons !frevK. Qed.
Lemma frev_unfold {n T} (u : 'I_n -> T) : frev u = (fun i => u (rev_ord i)).
Proof. by rewrite unlock. Qed.

End FFunRev.

Class ord_expose (P : Prop) := OrdExpose : P.

Global Hint Extern 0 (ord_expose _) => (rewrite /ord_expose; mc_nat) : typeclass_instances.

Definition AutoOrdinal (n : nat) {m : nat} {H : ord_expose (n < m)%N} : 'I_m := Ordinal H.
Arguments AutoOrdinal n {m H}.
Notation "'Ord' n" := (@AutoOrdinal n _ _) (at level 8).

Section FFunLRShift.

Definition left_ord {n} {i : 'I_n} (j : 'I_i) := (widen_ord (ltnW (ltn_ord i)) j).
Definition right_ord {n} {i : 'I_n} (j : 'I_(rev_ord i)) :=
  (rev_ord (widen_ord (ltnW (ltn_ord (rev_ord i))) (rev_ord j))).

Implicit Type (n : nat) (T : Type).

Definition cast_fun_ord {n m} (eqnm : n = m) T (f : 'I_n -> T) : 'I_m -> T :=
  let: erefl in _ = m := eqnm return 'I_m -> T in f.
Lemma cast_fun_ord_id {n T} (f : 'I_n -> T) eqn :
  cast_fun_ord eqn f = f.
Proof. by rewrite eq_axiomK. Qed.
Lemma cast_fun_ordE {n m} (eqnm : n = m) T (f : 'I_n -> T) i :
  cast_fun_ord eqnm f i = f (cast_ord (esym eqnm) i).
Proof. by case: m / eqnm i => i; rewrite cast_ord_id. Qed.
Lemma cast_fun_ordEV {n m} (eqnm : m = n) T (f : 'I_n -> T) i :
  cast_fun_ord (esym eqnm) f i = f (cast_ord eqnm i).
Proof. by rewrite cast_fun_ordE esymK. Qed.

Definition fleft_fun {n T} (u : 'I_n -> T) (i : 'I_n) :=
  (fun j : 'I_i => u (left_ord j)).
Definition fleft {n T} := locked_with ffun_key (@fleft_fun n T).
Canonical fleft_unlockable {n T} := [unlockable fun (@fleft n T)].
Global Arguments fleft {n T} u i.
Definition fright_fun {n T} (u : 'I_n -> T) (i : 'I_n) :=
  (fun j : 'I_(rev_ord i) => u (right_ord j)).
Definition fright {n T} := locked_with ffun_key (@fright_fun n T).
Canonical fright_unlockable {n T} := [unlockable fun (@fright n T)].
Global Arguments fright {n T} u i.

Lemma fleftE {n T} (u : 'I_n -> T) (i : 'I_n) j :
  fleft u i j = u (left_ord j).
Proof. by rewrite unlock. Qed.
Lemma frightE {n T} (u : 'I_n -> T) (i : 'I_n) j :
  fright u i j = u (right_ord j).
Proof. by rewrite unlock. Qed.
Lemma fright_leftE {n T} (u : 'I_n -> T) (i : 'I_n) : 
  fright u i = frev (fleft (frev u) (rev_ord i)).
Proof. by apply/funext=>j; rewrite frightE frevE fleftE frevE. Qed.
Lemma fleft_rightE n T (u : 'I_n -> T) (i : 'I_n) j :
  fleft u i j = frev (fright (frev u) (rev_ord i)) (cast_ord (esym (f_equal val (rev_ordK i))) j).
Proof. rewrite fleftE frevE frightE frevE; f_equal; mc_nat. Qed.

Lemma fleft0 n T (u : 'I_n.+1 -> T) :
  fleft u ord0 = fun => u ord0.
Proof. by apply/funext=>i; case: i. Qed.
Lemma fright_max n T (u : 'I_n.+1 -> T) :
  fright u ord_max = fun => u ord_max.
Proof. by apply/funext=>i; exfalso; case: i=>/=; rewrite subnn. Qed.

Lemma fleft_consE n T (x : T) (u : 'I_n -> T) (i : 'I_n) :
  fleft (fcons x u) (nlift ord0 i) = fcons x (fleft u i).
Proof.
apply/funext=>j; rewrite fleftE.
case: (unliftP ord0 j)=>/=[k->|->].
by rewrite fconsE fleftE -[RHS](fconsE x); f_equal; apply/val_inj.
by rewrite fcons0 -[RHS](fcons0 x u); f_equal; apply/val_inj.
Qed.
Lemma fleft_rcons_max n T (u : 'I_n -> T) (x : T) :
  fleft (frcons u x) ord_max = u.
Proof. by apply/funext=>i; rewrite fleftE -[RHS](frconsE u x); f_equal; mc_nat. Qed.
Lemma fleft_rconsEE n T (u : 'I_n -> T) (x : T) (i : 'I_n) j :
  fleft (frcons u x) (nlift ord_max i) j = fleft u i (cast_ord (lift_max _) j).
Proof. by rewrite !fleftE -[RHS](frconsE u x); f_equal; mc_nat. Qed.
Lemma fleft_rconsE n T (u : 'I_n -> T) (x : T) (i : 'I_n) :
  fleft (frcons u x) (nlift ord_max i) = cast_fun_ord (esym (lift_max _)) (fleft u i).
Proof. by apply/funext=>j; rewrite fleft_rconsEE cast_fun_ordEV. Qed.

Lemma fleft_max n T (u : 'I_n.+1 -> T) :
  fleft u ord_max = ffirst u.
Proof. by case: (frconsP u)=>t x; rewrite fleft_rcons_max frconsKV. Qed.
Lemma fright0E n T (u : 'I_n.+1 -> T) i :
  fright u ord0 i = ftail u (cast_ord (f_equal val (rev_ord0 _)) i).
Proof. by rewrite frightE -[RHS](fconsE (u ord0)) fconsK; f_equal; mc_nat. Qed.
Lemma fright0 n T (u : 'I_n.+1 -> T) :
  fright u ord0 = cast_fun_ord (esym (f_equal val (rev_ord0 _))) (ftail u).
Proof. by apply/funext=>j; rewrite fright0E cast_fun_ordEV. Qed.

Lemma fright_consE n T (x : T) (u : 'I_n -> T) (i : 'I_n) :
  fright (fcons x u) (nlift ord0 i) = fright u i.
Proof. by apply/funext=>j; rewrite !frightE -[RHS](fconsE x); f_equal; mc_nat. Qed.
Lemma fright_rcons_max n T (u : 'I_n -> T) (x : T) :
  fright (frcons u x) ord_max = fun => x.
Proof. by apply/funext=>i; exfalso; case: i=>/=; rewrite subnn. Qed.
Lemma fright_rconsEE n T (u : 'I_n -> T) (x : T) (i : 'I_n) j :
  fright (frcons u x) (nlift ord_max i) j = 
    frcons (fright u i) x (cast_ord (f_equal val (rev_ord_lift_max _)) j).
Proof.
set k := cast_ord _ _.
have ->: j = cast_ord (esym (f_equal val (rev_ord_lift_max _))) k
  by rewrite /k cast_ord_comp etrans_esym cast_ord_id.
case: (unliftP ord_max k)=>/=[l->|->].
by rewrite frconsE !frightE -[RHS](frconsE _ x); f_equal; mc_nat.
by rewrite frcons_max !frightE -[RHS](frcons_max u x); f_equal; mc_nat.
Qed.
Lemma fright_rconsE n T (u : 'I_n -> T) (x : T) (i : 'I_n) :
  fright (frcons u x) (nlift ord_max i) = 
    cast_fun_ord (esym (f_equal val (rev_ord_lift_max _))) (frcons (fright u i) x).
Proof. by apply/funext=>j; rewrite fright_rconsEE cast_fun_ordEV. Qed.

End FFunLRShift.

Local Close Scope classical_set_scope.

Lemma natrS_neq0 (T : numDomainType) n : (n.+1%:R : T) != 0.
Proof. by rewrite pnatr_eq0. Qed.
Lemma natr_nneg (F : numDomainType) n : (n%:R : F) \is Num.nneg.
Proof. by rewrite nnegrE. Qed.
Global Hint Extern 0 (is_true (_.+1%:R != 0)) => solve [apply: natrS_neq0] : core.
Global Hint Extern 0 (is_true (0 <= _%:R)) => solve [apply: ler0n] : core.
Global Hint Extern 0 (is_true (0 < _.+1%:R)) => solve [apply: ltr0Sn] : core.
Global Hint Extern 0 (is_true (_%:R \is Num.nneg)) => solve [apply: natr_nneg] : core.

Section ExpTrigoDef.
Variable (R : realType).

Definition expi (x : R) := (cos x +i* sin x)%C.
Lemma expi0 : expi 0 = 1. Proof. by rewrite /expi cos0 sin0. Qed.
Lemma expiD (x y : R) : expi (x + y) = expi x * expi y.
Proof. by rewrite /expi cosD sinD; simpc; f_equal; rewrite addrC. Qed.
Lemma expiN (x : R) : expi (- x) = (expi x)^-1.
Proof. by rewrite /expi /GRing.inv/= cos2Dsin2 !divr1 cosN sinN. Qed.

End ExpTrigoDef.

HB.lock
Definition expip (R : realType) (x : R) : R[i] := expi (pi * x).
HB.lock
Definition sinp (R : realType) (x : R) : R := sin (pi * x).
HB.lock
Definition cosp (R : realType) (x : R) : R := cos (pi * x).
Canonical expip_unlockable := Unlockable expip.unlock.
Canonical sinp_unlockable := Unlockable sinp.unlock.
Canonical cosp_unlockable := Unlockable cosp.unlock.

Section ExpTrigoDef.
Variable (R : realType).

(* we absorb pi into exp sin and cos. to work on rational number *)
(* set up theories on rat - C *)
(* remark: there already some automation of rat, ring_theory and field_theory *)

Lemma expipD (x y : R) : expip (x + y) = expip x * expip y.
Proof. by rewrite !unlock /expip -expiD -mulrDr/=. Qed.
Lemma expipN (x : R) : expip (- x) = (expip x)^-1.
Proof. by rewrite !unlock /expip -expiN mulrN. Qed.
Lemma expipNC (x : R) : expip (- x) = (expip x)^*.
Proof. by rewrite !unlock /expi; simpc; rewrite cosN sinN. Qed.
Lemma expipB (x y : R) : expip (x - y) = expip x / expip y.
Proof. by rewrite expipD expipN. Qed.
Lemma expip0 : expip (0 : R) = 1. Proof. by rewrite !unlock /expip mulr0 expi0. Qed.
Lemma expip1 : expip (1 : R) = -1. 
Proof. by rewrite !unlock /expip mulr1 /expi cospi sinpi; simpc. Qed.
Lemma expip2 : expip (2%:R : R) = 1. 
Proof.
rewrite !unlock /expip /expi mulr_natr -[_*+2]mulr1n -[_*+_*+_]add0r 
  !periodicn ?cos0 ?sin0//. apply cosD2pi. apply sinD2pi.
Qed.
Lemma expip_half : expip ((2%:R)^-1 : R) = 'i.
Proof. by rewrite !unlock /expip /expi cos_pihalf sin_pihalf. Qed.
Lemma expipX (r : R) (n : nat) : expip (r * n%:R) = (expip r) ^+ n.
Proof.
elim: n=>[|n IH]. by rewrite mulr0 expr0 expip0.
by rewrite -{1}addn1 natrD mulrDr expipD mulr1 IH exprSr.
Qed.
Lemma expip2n (n : nat) : expip ((2 * n)%:R : R) = 1.
Proof. by rewrite natrM expipX expip2 expr1n. Qed.
Lemma expip_prod I (r : seq I) (P : pred I) (f : I -> R):
  \prod_(i <- r | P i) expip (f i) = expip (\sum_(i <- r | P i) f i).
Proof. by elim/big_rec2: _=>[|i?? _ ->]; rewrite ?expip0//expipD. Qed.

Lemma periodicN [U V : zmodType] [f : U -> V] [T : U] :
  periodic f T -> periodic f (-T).
Proof. by move=> + u => /(_ (u - T)); rewrite addrNK => /esym. Qed.

Lemma periodicz [U V : zmodType] [f : U -> V] [T : U] :
  periodic f T -> forall (n : int) (a : U), f (a + T *~ n) = f a.
Proof.
move=> prd_f [] /= n; first by rewrite -pmulrn; apply: periodicn.
move=> u; rewrite NegzE -nmulrn -mulNrn.
by apply/periodicn/periodicN.
Qed.

Lemma cos_eq1 (x : R) : `|x| < pi * 2%:R -> cos x = 1 -> x = 0.
Proof.
suff wlog: forall (y : R), 0 <= y < pi * 2%:R -> cos y = 1 -> y = 0.
- case: (lerP 0 x) => [ge0_x|/ltW le0_x].
  - by rewrite ger0_norm // => ?; apply: wlog; apply/andP; split.
  - rewrite ltr_norml => /andP[+ _]; rewrite ltrNl -cosN => bd_Nx.
    move/wlog; rewrite bd_Nx oppr_ge0 le0_x /= => /(_ (erefl true)).
    by rewrite (rwP eqP) oppr_eq0 => /eqP ->.
move=> {}x bd_x; case: (lerP x pi) => [le_x_pi|le_pi_x].
- rewrite -cos0 => /cos_inj; apply; rewrite in_itv /=.
  - by rewrite le_x_pi andbT; case/andP: bd_x.
  - by rewrite lexx /= pi_ge0.
- move=> /(congr1 -%R); rewrite -cosDpi -(periodicz (@cosD2pi _) (-1)).
  rewrite mulrN1z mulr2n opprD addrA addrK -cospi.
  move/cos_inj; rewrite !in_itv /=.
  rewrite pi_ge0 lexx /= subr_ge0 [pi <= x]ltW //=.
  rewrite lerBlDr -mulr2n -mulr_natr.
  case/andP: (bd_x) => _ /ltW -> /(_ (erefl true) (erefl true)).
  move/(congr1 (fun x => x + pi)); rewrite subrK -mulr2n -mulr_natr => xE.
  by case/andP: bd_x => _; rewrite xE ltxx.
Qed.

Section IsDeriveV.
Variables (T : numFieldType) (V : normedModType T).

Global Instance is_deriveV (f : V -> T) (x v : V) (df : T) :
     f x != 0
  -> is_derive x v f df
  -> is_derive x v (fun x => (f x)^-1) (- (f x) ^- 2 * df).
Proof.
move=> nz_fx dfx; apply: DeriveDef; first exact: derivableV.
by rewrite deriveV // !derive_val.
Qed.
End IsDeriveV.

Section IsDeriveDiv.
Variables (T : numFieldType) (V : normedModType T).

Lemma derive_div (f g : V -> T) (x v : V) :
     g x != 0
  -> derivable f x v
  -> derivable g x v
  -> derivable (fun y => f y / g y) x v.
Proof.
move=> nz_gx df dg; apply: derivableM; first exact df.
by apply: derivableV.
Qed.

Global Instance is_derive_div (f g : V -> T) (x v : V) (df dg : T) :
     g x != 0
  -> is_derive x v f df
  -> is_derive x v g dg
  -> is_derive x v (fun y => f y / g y) ((g x) ^- 2 * (df * g x - f x * dg)).
Proof.
move=> nz_g dfv dgv; have dgIv := is_deriveV nz_g dgv.
move: (is_deriveM dfv dgIv); set d := (X in is_derive _ _ _ X -> _).
move=> h; set d' := (X in is_derive _ _ _ X).
(suff ->//: d' = d by apply: h); rewrite {h}/d {}/d'.
rewrite /GRing.scale /= !(mulNr, mulrN) [RHS]addrC mulrBr.
congr (_ - _); last by rewrite mulrCA.
rewrite mulrA [LHS]mulrAC; congr (_ * _).
by rewrite mulrC expr2 invfM mulrCA divff // mulr1.
Qed.
End IsDeriveDiv.

Lemma pi_gt1 : 1 < pi :> R.
Proof. by apply:(lt_le_trans _ (pi_ge2 R)) => //; rewrite (natrD _ 1 1) ltrDl. Qed.

Lemma pi_le4 : pi <= 4%:R :> R.
Proof.
rewrite /pi; case xgetP => /= [x _ | _]; last by rewrite mul0rn.
case=> /andP[_ le2_x] _; rewrite mulr2n -[4%:R]/(2+2)%:R.
by rewrite natrD lerD.
Qed.

Lemma ger_tan x : x \in `[0, pi / 2%:R[ -> x <= tan x :> R.
Proof.
rewrite in_itv /= => /andP[+ lt_pihalf].
rewrite le_eqVlt => /orP[/eqP<-|gt0_x]; first by rewrite tan0.
have le2_x: x <= 2%:R.
- apply/ltW/(lt_le_trans lt_pihalf); rewrite ler_pdivrMr //.
  by rewrite -natrM /= pi_le4.
have nz_cos c: c \in `[0, x] -> cos c != 0.
- rewrite in_itv /= => /andP[gt0_c le_cx].
  apply/contraL: (lt_pihalf) => /eqP z_cosc.
  rewrite -leNgt; have <-// := @cos_02_uniq _ c (pi / 2%:R).
  - by rewrite gt0_c //= (le_trans le_cx).
  - rewrite mulr_ge0 //= ?(invr_ge0, pi_ge0) //.
    by rewrite ler_pdivrMr // -natrM pi_le4.
  - by rewrite cos_pihalf.
have dt: forall y, y \in `]0, x[ -> is_derive y 1 tan (cos y ^- 2).
- move=> y rg_y; apply: is_derive_tan.
  by apply: nz_cos; apply: subset_itv rg_y.
have ct: {within `[0, x], continuous tan}%classic.
- apply: continuous_in_subspaceT=>c; rewrite mem_setE /= => rg_c.
  by apply/continuous_tan/nz_cos; apply: subset_itv rg_c.
have [d +] := MVT gt0_x dt ct; rewrite in_itv /= => /andP[gt0_d lt_dx].
rewrite tan0 !subr0 => ->; rewrite ler_peMl //; first by apply/ltW.
rewrite invf_ge1; last first.
- rewrite exprn_ile1 // (cos_le1, cos_ge0_pihalf) //.
  by rewrite -ler_norml gtr0_norm // ltW // (lt_trans lt_dx).
rewrite exprn_gt0 // cos_gt0_pihalf // -ltr_norml gtr0_norm //.
by rewrite (lt_trans lt_dx).
Qed.

Lemma ler_abs_sin (a : R) : `|sin a| <= `|a|.
Proof.
suff wlog: forall (a : R), 0 <= a <= 1 -> sin a <= a.
- case: (lerP 1 `|a|) => [|lt1_a].
  - by move=> le; apply: (le_trans (sin_max a) le).
  wlog: a lt1_a / (0 <= a) => [{}wlog|ge0_a].
  case: (ler0P a) => [|/ltW ge0_a]; last first.
  - by rewrite -[X in _ <= X]ger0_norm //; apply: wlog.
  move=> le0_a; have := wlog (-a).
  rewrite normrN oppr_ge0 => /(_ lt1_a le0_a).
  by rewrite sinN normrN [ `|a|]ler0_norm.
  rewrite !ger0_norm //; last first.
  - by apply/wlog/andP; split=> //; apply/ltW/ltr_normlW.
  apply/sin_ge0_pi; rewrite ge0_a /= (@le_trans _ _ 1) //.
  - by apply/ltW/ltr_normlW.
  - by apply/ltW/pi_gt1.
move=> {}a /andP[+ le1_a]; rewrite le_eqVlt => /orP[|lt0_a].
- by move/eqP=> <-; rewrite sin0.
have := @MVT R sin cos 0 a lt0_a (fun x _ => is_derive_sin x).
case; first by apply/continuous_subspaceT/continuous_sin.
move=> c rg_c; rewrite sin0 !subr0 => ->.
by rewrite ler_piMl //; [apply/ltW | apply/cos_le1].
Qed.

Lemma ger_abs_sin (a : R) : `|a| <= pi / 2%:R -> (2%:R * `|a| / pi) <= `|sin a|.
Proof.
wlog: a / (0 <= a) => [wlog|ge0_a].
- case: (ler0P a) => [le0_a|/ltW ge0_a]; last first.
  - by have := wlog a ge0_a; rewrite ger0_norm.
  move=> bd_a; rewrite -ler0_norm //.
  have := wlog (-a); rewrite oppr_ge0 sinN !normrN.
  by apply=> //; rewrite ler0_norm.
rewrite [ `|a|]ger0_norm // => bd_a; rewrite ger0_norm.
- apply: sin_ge0_pi; rewrite ge0_a /=; apply: (le_trans bd_a).
  rewrite ler_pdivrMr // ler_pMr ?pi_gt0 //.
  by rewrite (natrD _ 1 1) lerDl.
move: ge0_a; rewrite le_eqVlt => /orP[/eqP <-|gt0_a].
- by rewrite !Monoid.simpm sin0.
move: bd_a; rewrite le_eqVlt => /orP[/eqP->|bd_a].
- rewrite sin_pihalf mulrAC -[pi / _]invf_div divff //.
  by rewrite mulf_neq0 //= invr_eq0 gt_eqF // pi_gt0.
pose f (x : R) := sin x / x.
pose F (x : R) := (x * cos x - sin x) / (x ^+ 2).
have fF (c : R): c \in `[a, pi / 2%:R] -> is_derive c 1 f (F c).
- rewrite in_itv /= => /andP[lt_ac lt_c_pi].
  have nz_c: c != 0 by rewrite gt_eqF // (lt_le_trans gt0_a).
  have := @is_derive_div R R sin idfun c 1 (cos c) 1 nz_c (is_derive_sin c) (is_derive_id c 1).
  set d := (X in is_derive _ _ _ X -> _) => h; suff <-: d = F c by done.
  by rewrite {h}/d {}/F /= [LHS]mulrC mulr1 [c * cos c]mulrC.
have h1 (c : R): c \in `]a, pi / 2%:R[ -> is_derive c 1 f (F c).
- by move=> rg_c; apply: fF; apply: subset_itv rg_c.
have h2: {within `[a, pi / 2%:R], continuous f}%classic.
  (* this should be a direct consequence of `fF`! *)
- apply: continuous_in_subspaceT => c rg_c.
  apply: cvgM; first by apply: continuous_sin.
  apply: cvgV; last by apply: cvg_id.
  move: rg_c; rewrite mem_setE in_itv /= => /andP[+ _].
  by apply: contraL => /eqP->; rewrite -ltNge.
have {h1 h2 fF}[c] := @MVT R f F a (pi / 2%:R) bd_a h1 h2.
rewrite in_itv /= => /andP[lt_ac bd_c]; rewrite {}/f {}/F.
rewrite sin_pihalf invf_div mul1r (rwP eqP) subr_eq.
rewrite [_ + (sin a / a)]addrC -subr_eq => /eqP /esym sinaVaE.
rewrite mulrAC -ler_pdivlMr // {}sinaVaE lerBrDl.
rewrite ler_wnDl //; apply: mulr_le0_ge0; last first.
- by rewrite subr_ge0; apply/ltW.
apply: mulr_le0_ge0; last first.
- by rewrite invr_ge0 exprn_ge0 //; apply/ltW/(lt_trans gt0_a).
rewrite subr_le0; rewrite -ler_pdivlMr.
- apply: cos_gt0_pihalf; rewrite -ltr_norml ger0_norm //.
  by apply/ltW/(lt_trans gt0_a).
rewrite -/(tan c); apply: ger_tan; rewrite in_itv /=.
by rewrite !ltW // (lt_trans gt0_a).
Qed.

Lemma pi_neq0 : (pi : R) != 0.
Proof. by move: (pi_gt0 R)=>/lt0r_neq0/negPf->/=. Qed.

Lemma pi_eq0 : (pi : R) == 0 = false.
Proof. apply/eqP/eqP/pi_neq0. Qed.

Lemma expip_sum_cst n (r : R) :
  expip r = 1 -> \sum_(k < n) expip (r * k%:R) = n%:R.
Proof. by move=>P; under eq_bigr do rewrite expipX P expr1n; rewrite sumr_const card_ord. Qed.

Lemma expip_sum n (r : R) :
  expip r != 1 -> \sum_(k < n) expip (r * k%:R) = (1 - expip (r * n%:R)) / (1 - expip r).
Proof.
rewrite -subr_eq0=>/eqP/eqP=>P; apply/(mulfI P); under eq_bigr do rewrite expipX.
by rewrite -subrX1 expipX mulrC -[X in _ / X]opprB invrN mulrN mulNr mulfVK// opprB.
Qed.

Lemma expip_eq1_uniq (r : R) : `|r| < 2%:R -> expip r = 1 -> r = 0.
Proof.
move=>Pr; have P1: `|pi * r| < pi * 2%:R 
  by rewrite normrM ger0_norm ?pi_ge0// ltr_pM2l// ?pi_gt0.
rewrite unlock /expi=>P2; inversion P2.
by move: (cos_eq1 P1 H0)=>/eqP; rewrite mulf_eq0 pi_eq0/==>/eqP.
Qed.

Lemma expip_neq1 (r : R) : `|r| < 2%:R -> r != 0 -> expip r != 1.
Proof. by move=>/expip_eq1_uniq P1; apply contraNN=>/eqP/P1->. Qed.

Lemma expip_sum_ord (m n : nat) (i j : 'I_m) : (m <= n)%N ->
  \sum_(k < n) expip (2%:R * (i%:R - j%:R) * k%:R / n%:R :> R) = ((i == j))%:R * n%:R.
Proof.
under eq_bigr do rewrite mulrC mulrA.
case: eqP=>[->|]; first by rewrite expip_sum_cst ?mul1r// subrr !mulr0 expip0.
move=>/eqP P1 P2; case: n P2=>[_|n P2]; first by rewrite big_ord0 mulr0.
rewrite expip_sum; first apply/expip_neq1.
rewrite !normrM 2?ger0_norm ?invr_ge0 ?ler0n// ltr_pdivrMl ?ltr0n// 
  mulrC ltr_pM2r ?ltr0n// lter_distl ltrBlDl addrC; apply/andP; 
  by split; apply/ltr_wpDl; rewrite ?ler0n// ltr_nat; apply: (leq_trans _ P2).
by rewrite !mulf_eq0 invr_eq0 !negb_or !natrS_neq0/= subr_eq0 eqr_nat.
by rewrite mulrC mulfVK ?natrS_neq0// mulrBr 
  expipB -!natrM !expip2n invr1 mulr1 subrr mul0r mul0n.
Qed.

Lemma expip_period n (r : R) : expip ( (2 * n)%:R + r) = expip r.
Proof.
rewrite unlock mulrDr natrM mulrA !mulr_natr addrC /expi.
rewrite !periodicn//. apply cosD2pi. apply sinD2pi.
Qed.

End ExpTrigoDef.

Section trigoExtra.
Variable (R : realType).
Implicit Type (x y z : R).
Local Notation "2" := (2%:R : R).

Lemma sinB x y : sin (x - y) = sin x * cos y - cos x * sin y.
Proof. by rewrite sinD cosN sinN mulrN. Qed.
Lemma cosB x y : cos (x - y) = cos x * cos y + sin x * sin y.
Proof. by rewrite cosD cosN sinN mulrN opprK. Qed.

Lemma sin2x x : sin (x *+ 2) = (sin x * cos x) *+ 2.
Proof. by rewrite mulr2n sinD [cos _* _]mulrC -mulr2n -mulr_natl mulrA. Qed.
Lemma cos2x x : cos (x *+ 2) = (cos x) ^+ 2 - (sin x) ^+ 2.
Proof. by rewrite mulr2n cosD -!expr2. Qed.
Lemma cos2x_cos x : cos (x *+ 2) = ((cos x) ^+ 2) *+ 2 - 1.
Proof. by rewrite cos2x -(cos2Dsin2 x) mulr2n opprD addrACA subrr add0r. Qed.
Lemma cos2x_sin x : cos (x *+ 2) = 1 - ((sin x) ^+ 2) *+ 2.
Proof. by rewrite cos2x -(cos2Dsin2 x) mulr2n opprD addrACA subrr addr0. Qed.

End trigoExtra.
