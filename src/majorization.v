From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean interval finmap fingroup perm.
From mathcomp.analysis Require Import -(notations)forms.
From quantum.external Require Import complex.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import signed reals ereal topology normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure lebesgue_integral numfun exp.
From mathcomp Require Import convex itv realfun.
Require Import mcextra mcaextra mxpred svd extnum ctopology convex.
From quantum.external Require Import spectral.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.

Section majorize_def.
Variable (R : numFieldType).

Definition majorize m (x y : 'rV[R]_m) := (forall (i : 'I_m), 
    \sum_(j < m | (j < i)%N) sort_v x 0 j <= \sum_(j < m | (j < i)%N) sort_v y 0 j)
    /\ \sum_(j < m) sort_v x 0 j = \sum_(j < m) sort_v y 0 j.

Definition weak_majorize m (x y : 'rV[R]_m) := (forall (i : 'I_m), 
    \sum_(j < m | (j <= i)%N) sort_v x 0 j <= \sum_(j < m | (j <= i)%N) sort_v y 0 j).

Lemma sort_v_sum m (x : 'rV[R]_m) : \sum_i sort_v x 0 i = \sum_i x 0 i.
Proof.
move: (perm_sort_v x)=>[s <-]; rewrite (reindex_perm s^-1).
by under eq_bigr do rewrite mxE permKV.
Qed. 

Lemma weak_majorize_ltP m (x y : 'rV[R]_m) :
  weak_majorize x y <-> (forall i, \sum_(j < m | (j < i)%N) sort_v x 0 j 
                                <= \sum_(j < m | (j < i)%N) sort_v y 0 j).
Proof.
case: m x y=>[x y |m x y].
  by split=> _ i; rewrite !big_ord0.
split.
- move=>P; case=>[|i]; first by rewrite !big1.
  have [Pi|Pi] := leqP m.+1 i.
    under eq_bigl do rewrite ltnS (leq_trans (ltnW (@ltn_ord _ _)) Pi).
    under [leRHS]eq_bigl do rewrite ltnS (leq_trans (ltnW (@ltn_ord _ _)) Pi).
    move: (P ord_max).
    under [X in X <= _ -> _]eq_bigl do rewrite /= -ltnS ltn_ord.
    by under [X in _ <= X -> _]eq_bigl do rewrite /= -ltnS ltn_ord.
  by move: (P (Ordinal Pi)).
- by move=>P i; move: (P i.+1).
Qed.

Lemma weak_majorize_leP m (x y : 'rV[R]_m) :
  weak_majorize x y <-> (forall i, \sum_(j < m | (j <= i)%N) sort_v x 0 j 
                                <= \sum_(j < m | (j <= i)%N) sort_v y 0 j).
Proof.
rewrite weak_majorize_ltP; split=>P i; first by move: (P i.+1).
case: i=>[|i]; by [rewrite !big1| move: (P i)].
Qed.

Lemma majorize_ltP m (x y : 'rV[R]_m) : majorize x y <->
  ((forall i, \sum_(j < m | (j < i)%N) sort_v x 0 j <= \sum_(j < m | (j < i)%N) sort_v y 0 j)
  /\ \sum_(j < m) sort_v x 0 j = \sum_(j < m) sort_v y 0 j).
Proof.
split=>[[P1 P2]|[P1 P2]]; split=>// i.
have [Pi | Pi] := leqP m i.
  under eq_bigl do rewrite (leq_trans (@ltn_ord _ _) Pi).
  under [leRHS]eq_bigl do rewrite (leq_trans (@ltn_ord _ _) Pi).
  by rewrite P2.
by move: (P1 (Ordinal Pi)).
Qed.

Lemma majorize_leP m (x y : 'rV[R]_m) : majorize x y <->
  ((forall i, \sum_(j < m | (j <= i)%N) sort_v x 0 j <= \sum_(j < m | (j <= i)%N) sort_v y 0 j)
  /\ \sum_(j < m) sort_v x 0 j = \sum_(j < m) sort_v y 0 j).
Proof. by rewrite majorize_ltP -weak_majorize_ltP -weak_majorize_leP. Qed.

Lemma majorizeW m (x y : 'rV[R]_m) :
  majorize x y -> weak_majorize x y.
Proof. by rewrite majorize_leP -weak_majorize_leP=>[[]]. Qed.

Lemma majorize_refl m (x : 'rV[R]_m) : majorize x x.
Proof. by split. Qed.

Lemma weak_majorize_refl m (x : 'rV[R]_m) : weak_majorize x x.
Proof. by []. Qed.

Lemma majorize_trans m (x y z : 'rV[R]_m) : 
  majorize x y -> majorize y z -> majorize x z.
Proof.
move=>[P1 P2] [P3 P4]; split=>[i |].
by apply/(le_trans (P1 i)). by rewrite P2.
Qed.

Lemma weak_majorize_trans m (x y z : 'rV[R]_m) : 
  weak_majorize x y -> weak_majorize y z -> weak_majorize x z.
Proof. by move=>P1 P2 i; apply/(le_trans (P1 i)). Qed.

Lemma weak_majorize_anti m (x y : 'rV[R]_m) :
  weak_majorize x y -> weak_majorize y x -> exists s, y = col_perm s x.
Proof.
move=>P1 P2; suff : sort_v x = sort_v y.
  move: (perm_sort_v x) (perm_sort_v y)=>[s1 <-][s2 <-]/(f_equal (col_perm (s2^-1))).
  rewrite -!col_permM mulVg col_perm1 =>Py.
  by exists (s2^-1 * s1)%g; rewrite Py.
apply/matrixP=>i j; rewrite ord1.
elim/ord_ltn_ind: j=> j Pj.
have : \sum_(j0 < m | (j0 <= j)%N) sort_v x 0 j0 = 
  \sum_(j0 < m | (j0 <= j)%N) sort_v y 0 j0.
  by apply/le_anti; rewrite P1 P2.
rewrite (bigD1 j)//= [in X in _ = X](bigD1 j)//=.
under eq_bigl do rewrite andbC -ltn_neqAle/=.
under [X in _ = _ + X]eq_bigl do rewrite andbC -ltn_neqAle/=.
by rewrite (eq_bigr _ Pj)=>/addIr.
Qed.

Lemma majorize_anti m (x y : 'rV[R]_m) :
  majorize x y -> majorize y x -> exists s, y = col_perm s x.
Proof. move=>/majorizeW + /majorizeW; exact: weak_majorize_anti. Qed.

Lemma sort_v_eq m (x y : 'rV[R]_m) : 
  (exists s, col_perm s x = y) -> y \is rv_nonincreasing -> sort_v x = y.
Proof.
move=>[]s <-. move: (perm_sort_v x)=>[s1]/(f_equal (col_perm s1^-1)).
rewrite -col_permM mulVg col_perm1=>{1 3}->.
rewrite -col_permM=>P; symmetry; apply/rv_nonincreasing_perm=>//.
apply/rv_nonincreasingP/sort_v_nonincreasing.
move: (perm_sort_v x) P=>[s2 <-]; 
by rewrite -col_permM=>/rv_nonincreasing_is_cmp; rewrite col_perm_rv_cmp.
Qed.

End majorize_def.

Section doubly_stochastic_def.
Variable (R : numFieldType).

Definition doubly_substochastic {m} :=
  [qualify A : 'M[R]_m | (A \is a nnegmx) &&
    [forall i : 'I_m, (\sum_j A i j <= 1) && (\sum_j A j i <= 1) ]].

Definition doubly_stochastic {m} :=
  [qualify A : 'M[R]_m | (A \is a nnegmx) &&
    [forall i : 'I_m, (\sum_j A i j == 1) && (\sum_j A j i == 1) ]].

Lemma doubly_substochasticP m (A : 'M[R]_m) :
  reflect ((forall i j, 0 <= A i j) /\ (forall i, \sum_j A i j <= 1) /\ (forall i, \sum_j A j i <= 1))
    (A \is doubly_substochastic).
Proof.
apply (iffP andP)=>[[/nnegmxP P1 /forallP P2]|[P1 [P2 P3]]].
  do ! split.
    by move=>i j; move: (P1 i j); rewrite nnegrE.
  1,2: by move=>i; move: (P2 i)=>/andP[].
split.
  by apply/nnegmxP=>i j; rewrite nnegrE.
by apply/forallP=>i; apply/andP; split.
Qed.

Lemma doubly_stochasticP m (A : 'M[R]_m) :
  reflect ((forall i j, 0 <= A i j) /\ (forall i, \sum_j A i j = 1) /\ (forall i, \sum_j A j i = 1))
    (A \is doubly_stochastic).
Proof.
apply (iffP andP)=>[[/nnegmxP P1 /forallP P2]|[P1 [P2 P3]]].
  do ! split.
    by move=>i j; move: (P1 i j); rewrite nnegrE.
  1,2: by move=>i; move: (P2 i)=>/andP[]/eqP+/eqP.
split.
  by apply/nnegmxP=>i j; rewrite nnegrE.
by apply/forallP=>i; apply/andP; split; apply/eqP.
Qed.

Lemma doubly_stochasticW m (A : 'M[R]_m) :
  A \is doubly_stochastic -> A \is doubly_substochastic.
Proof.
move=>/doubly_stochasticP[P1 [P2 P3]].
apply/doubly_substochasticP; do ! split=>//.
by move=>i; move: (P2 i)=>->.
by move=>i; move: (P3 i)=>->.
Qed.

Lemma doubly_stochastic_convex m :
  conv [set A : 'M[R]_m | A \is doubly_stochastic]%classic =
    [set A : 'M[R]_m | A \is doubly_stochastic]%classic.
Proof.
apply/seteqP; split; last by apply: conv_le.
move=>x /=; rewrite /conv/==>[[F][c][f][]Pc1[]Pc2[]Pf Px].
rewrite Px; apply/doubly_stochasticP; do ! split.
- move=>i j; rewrite summxE sumr_ge0//==>k _;
  rewrite mxE mulr_ge0//; first by move: (Pc1 k)=>/andP[].
  by move: (Pf k); rewrite inE/==>/doubly_stochasticP[]/(_ i j).
- move=>i; under eq_bigr do (rewrite summxE; under eq_bigr do rewrite mxE).
  rewrite exchange_big/=; under eq_bigr do rewrite -mulr_sumr.
  rewrite -Pc2; apply eq_bigr=>j _; rewrite -[RHS]mulr1.
  by move: (Pf j); rewrite inE=>/doubly_stochasticP[] _ []/(_ i)-> _.
- move=>i; under eq_bigr do (rewrite summxE; under eq_bigr do rewrite mxE).
  rewrite exchange_big/=; under eq_bigr do rewrite -mulr_sumr.
  rewrite -Pc2; apply eq_bigr=>j _; rewrite -[RHS]mulr1.
  by move: (Pf j); rewrite inE=>/doubly_stochasticP[] _ [] _ /(_ i)->.
Qed.

Lemma doubly_substochastic_nnegmx m (A : 'M[R]_m) :
  A \is doubly_substochastic -> A \is a nnegmx.
Proof. by move=>/andP[]. Qed.

Lemma doubly_stochastic_nnegmx m (A : 'M[R]_m) :
  A \is doubly_stochastic -> A \is a nnegmx.
Proof. by move=>/andP[]. Qed.

Lemma doubly_stochastic_ge0 m (A : 'M[R]_m) i j :
  A \is doubly_stochastic -> 0 <= A i j.
Proof. by move=>/doubly_stochastic_nnegmx/nnegmxP; rewrite -nnegrE. Qed.

Lemma doubly_substochastic_ge0 m (A : 'M[R]_m) i j :
  A \is doubly_substochastic -> 0 <= A i j.
Proof. by move=>/doubly_substochastic_nnegmx/nnegmxP; rewrite -nnegrE. Qed.

Lemma doubly_stochastic_le1 m (A : 'M[R]_m) i j :
  A \is doubly_stochastic -> A i j <= 1.
Proof.
move=>/doubly_stochasticP=>[[Pij][_]]/(_ j)=><-.
by rewrite (bigD1 i)//= lerDl sumr_ge0.
Qed.

Lemma doubly_substochastic_le1 m (A : 'M[R]_m) i j :
  A \is doubly_substochastic -> A i j <= 1.
Proof.
move=>/doubly_substochasticP=>[[Pij][_]]/(_ j); apply: le_trans.
by rewrite (bigD1 i)//= lerDl sumr_ge0.
Qed.

Lemma doubly_stochasticM m (x y : 'M[R]_m) :
  x \is doubly_stochastic -> y \is doubly_stochastic ->
    x *m y \is doubly_stochastic.
Proof.
move=>/doubly_stochasticP[P1 [P2 P3]].
move=>/doubly_stochasticP[P4 [P5 P6]].
apply/doubly_stochasticP; do ! split.
- by move=>i j; rewrite mxE sumr_ge0//==>k _; rewrite mulr_ge0.
- move=>i; rewrite -(P2 i);  under eq_bigr do rewrite mxE.
  by rewrite exchange_big/=; under eq_bigr do rewrite -mulr_sumr P5 mulr1.
- move=>i; rewrite -(P6 i);  under eq_bigr do rewrite mxE.
  by rewrite exchange_big/=; under eq_bigr do rewrite -mulr_suml P3 mul1r.
Qed.

Lemma doubly_substochasticM m (x y : 'M[R]_m) :
  x \is doubly_substochastic -> y \is doubly_substochastic ->
    x *m y \is doubly_substochastic.
Proof.
move=>/doubly_substochasticP[P1 [P2 P3]].
move=>/doubly_substochasticP[P4 [P5 P6]].
apply/doubly_substochasticP; do ! split.
- by move=>i j; rewrite mxE sumr_ge0//==>k _; rewrite mulr_ge0.
- move=>i; apply/(le_trans _ (P2 i));  under eq_bigr do rewrite mxE.
  rewrite exchange_big/=; apply ler_sum=>/= j _.
  by rewrite -mulr_sumr ler_piMr.
- move=>i; apply/(le_trans _ (P6 i));  under eq_bigr do rewrite mxE.
  rewrite exchange_big/=; apply ler_sum=>/= j _.
  by rewrite -mulr_suml ler_piMl.
Qed.

Lemma trmx_doubly_stochastic m (x : 'M[R]_m) :
  (x^T \is doubly_stochastic) = (x \is doubly_stochastic).
Proof.
apply/eqb_iff; split=>/doubly_stochasticP[P1][P2]P3;
apply/doubly_stochasticP; (split=>[i j|]; first by move: (P1 j i); rewrite mxE);
(split=>i; [move: (P3 i)=><- | move: (P2 i)=><-]);
by apply eq_bigr=>k _; rewrite mxE.
Qed.

Lemma trmx_doubly_substochastic m (x : 'M[R]_m) :
  (x^T \is doubly_substochastic) = (x \is doubly_substochastic).
Proof.
apply/eqb_iff; split=>/doubly_substochasticP[P1][P2]P3;
apply/doubly_substochasticP; (split=>[i j|]; first by move: (P1 j i); rewrite mxE);
(split=>i; [apply/(le_trans _ (P3 i))|apply/(le_trans _ (P2 i))]);
by apply ler_sum=>??; rewrite mxE.
Qed.

Lemma perm_mx_doubly_stochastic m (s : 'S_m) :
  perm_mx s \is doubly_stochastic.
Proof.
apply/doubly_stochasticP; do ! split.
- by move=>i j; rewrite !mxE; case: eqP.
- move=>i; rewrite (bigD1 (s i))//= big1=>[j/negPf nj|];
  by rewrite !mxE ?eqxx ?addr0// eq_sym nj.
- move=>i; rewrite (bigD1 ((s^-1)%g i))//= big1=>[j/negPf nj|];
  by rewrite !mxE ?addr0 ?permKV ?eqxx// (can2_eq (@permK _ s) (@permKV _ s)) nj.
Qed.

Lemma perm_mx_doubly_substochastic m (s : 'S_m) :
  perm_mx s \is doubly_substochastic.
Proof. apply/doubly_stochasticW/perm_mx_doubly_stochastic. Qed.

Lemma doubly_stochastic_col_perm m (A : 'M[R]_m) s :
  (col_perm s A \is doubly_stochastic) = (A \is doubly_stochastic).
Proof.
suff PB B (t : 'S_m): B \is doubly_stochastic -> col_perm t B \is doubly_stochastic.
  apply/eqb_iff; split; last by apply PB.
  by move=>/PB P; move: (P (s^-1)%g); rewrite -col_permM mulVg col_perm1.
move=>/doubly_stochasticP[P1][P2]P3; apply/doubly_stochasticP; do ! split.
- by move=>i j; rewrite mxE.
- move=>i; rewrite (reindex_perm t^-1)/=.
  by under eq_bigr do rewrite mxE permKV.
- by move=>i; under eq_bigr do rewrite mxE.
Qed.

Lemma doubly_stochastic_row_perm m (A : 'M[R]_m) s :
  (row_perm s A \is doubly_stochastic) = (A \is doubly_stochastic).
Proof.
by rewrite -trmx_doubly_stochastic tr_row_perm 
  doubly_stochastic_col_perm trmx_doubly_stochastic.
Qed.

Lemma doubly_substochastic_col_perm m (A : 'M[R]_m) s :
  (col_perm s A \is doubly_substochastic) = (A \is doubly_substochastic).
Proof.
suff PB B (t : 'S_m): B \is doubly_substochastic -> col_perm t B \is doubly_substochastic.
  apply/eqb_iff; split; last by apply PB.
  by move=>/PB P; move: (P (s^-1)%g); rewrite -col_permM mulVg col_perm1.
move=>/doubly_substochasticP[P1][P2]P3; apply/doubly_substochasticP; do ! split.
- by move=>i j; rewrite mxE.
- move=>i; rewrite (reindex_perm t^-1)/=.
  by under eq_bigr do rewrite mxE permKV.
- by move=>i; under eq_bigr do rewrite mxE.
Qed.

Lemma doubly_substochastic_row_perm m (A : 'M[R]_m) s :
  (row_perm s A \is doubly_substochastic) = (A \is doubly_substochastic).
Proof.
by rewrite -trmx_doubly_substochastic tr_row_perm 
  doubly_substochastic_col_perm trmx_doubly_substochastic.
Qed.

Definition elem_lemx m n (x y : 'M[R]_(m,n)) := [forall i, [forall j, x i j <= y i j]].

Lemma elem_lemxP m n (x y : 'M[R]_(m,n)) : 
  reflect (forall i j, x i j <= y i j) (elem_lemx x y).
Proof.
apply/(iffP forallP)=>IH i.
by move: (IH i)=>/forallP. by apply/forallP.
Qed.

Lemma elem_lemx_refl m n (x : 'M[R]_(m,n)) : elem_lemx x x.
Proof. by apply/elem_lemxP. Qed.

Lemma elem_lemx_trans m n : transitive (@elem_lemx m n).
Proof.
move=>x y z /elem_lemxP Px /elem_lemxP Py; apply/elem_lemxP=>i j.
move: (Px i j) (Py i j); exact: le_trans.
Qed.

Lemma elem_lemx_anti m n : antisymmetric (@elem_lemx m n).
Proof.
move=>x y /andP [] /elem_lemxP Px /elem_lemxP Py.
by apply/matrixP=>i j; apply/le_anti; rewrite Px Py.
Qed.

Lemma normM_elem_lemx m n r(A : 'M[R]_(m,n)) (x : 'M[R]_(r,m)) :
  A \is a nnegmx -> 
    elem_lemx (map_mx normr (x *m A)) (map_mx normr x *m A).
Proof.
move=>/nnegmxP PA; apply/elem_lemxP=>i j; rewrite !mxE.
apply/(le_trans (ler_norm_sum _ _ _))/ler_sum=>k _.
by rewrite mxE normrM ler_wpM2l// ger0_norm// -nnegrE.
Qed.

End doubly_stochastic_def.

Arguments doubly_stochastic {R m}.
Arguments doubly_substochastic {R m}.

Section PerfectMatching.

Let G m (R : {set 'I_m * 'I_m}) i : {set 'I_m} := 
  [set j : 'I_m | (i,j) \in R].

Let Gk m (R : {set 'I_m * 'I_m}) k (f : 'I_k -> 'I_m) :=
  \bigcup_i G R (f i).

Lemma imset_inj_ord (T : finType) (S : {set T}) k :
  #|S| = k -> exists (f : 'I_k -> T), injective f /\ S = f @: finset.setT.
Proof.
elim: k S.
  move=>S /eqP; rewrite cards_eq0=>/eqP->; exists (fun0 T); split=>[[]//|].
  apply/setP=>i; rewrite inE; apply/esym/negbTE/negP.
  by move=>/imsetP[[]].
move=>k IH S Ps.
have : (0 < #|S|)%N by rewrite Ps.
rewrite card_gt0=>/set0Pn[x Px].
have : #|S :\ x| = k.
  by move: Ps; rewrite (cardsD1 x) Px -add1n=>/addnI.
move=>/IH[f [injf Pf]].
exists (fcons x f); split.
  move=>a b; case: (unliftP ord0 a)=>/=[c ->|->];
  case: (unliftP ord0 b)=>/=[d ->|->]; rewrite ?fconsE ?fcons0//.
  - by move=>/injf->.
  - have: (f c \in S :\ x).
      by rewrite Pf; apply/imsetP; exists c=>//; rewrite inE.
    by move=>+Pc; rewrite Pc !inE eqxx.
  - have: (f d \in S :\ x).
      by rewrite Pf; apply/imsetP; exists d=>//; rewrite inE.
    by move=>+Pd; rewrite -Pd !inE eqxx.
apply/setP=>i; rewrite -(finset.setD1K Px) 2 !inE.
apply/eqb_iff; split.
  move=>/orP[/eqP->|].
    by apply/imsetP; exists ord0; rewrite ?fcons0.
  rewrite Pf=>/imsetP[/=j _ ->]; apply/imsetP; 
  by exists (nlift ord0 j); rewrite // fconsE.
move=>/imsetP[/= j _ ->].
case: (unliftP ord0 j)=>/=[l->|->]; rewrite ?fcons0 ?eqxx// fconsE.
by apply/orP; right; rewrite Pf; apply/imsetP; exists l.
Qed.

Lemma inj_ord_perm m n (h : 'I_m -> 'I_n) (H : (m + (n - m) = n)%N) :
  injective h -> exists (s : 'S_n), h = s \o cast_ord H \o lshift _.
Proof.
move=>injh.
pose ph := ~: (h @: finset.setT).
have : #|ph| = (n - m)%N.
  by rewrite cardsCs finset.setCK/= card_imset// cardsT !card_ord.
move=>/imset_inj_ord[/= g][injg Pg].
pose s (i : 'I_n) : 'I_n := 
  match fintype.split (cast_ord (esym H) i) with
  | inl i => h i
  | inr i => g i
  end.
have injs : injective s.
  move=>a b; rewrite /s; case: split_ordP=>c /cast_ord_sym->;
  case: split_ordP=>d /cast_ord_sym->.
  - by move=>/injh->.
  - have Pd: g d \in ph 
      by rewrite Pg; apply/imsetP; exists d=>//; rewrite inE.
    have : h c \notin ph.
      by rewrite -finset.in_setC finset.setCK; apply/imsetP; exists c=>//; rewrite inE.
    by move=>+Pcd; rewrite Pcd Pd.
  - have Pd: g c \in ph 
      by rewrite Pg; apply/imsetP; exists c=>//; rewrite inE.
    have : h d \notin ph.
      by rewrite -finset.in_setC finset.setCK; apply/imsetP; exists d=>//; rewrite inE.
    by move=>+Pcd; rewrite -Pcd Pd.
  - by move=>/injg->.
exists (perm injs); apply/funext=>i.
rewrite /= permE /s cast_ord_comp cast_ord_id.
by case: split_ordP=>[?/lshift_inj->//|?/eqP]; rewrite eq_lrshift.
Qed.

Theorem Hall_perfect_matching m (R : {set 'I_m * 'I_m}) :
  (exists s : 'S_m, forall i, (i, s i) \in R) <->
    (forall k (f : 'I_k.+1 -> 'I_m), injective f -> (k < #|Gk R f|)%N).
Proof.
split.
  move=>[s Ps] k f injf.
  have : (s \o f) @: [set: 'I_k.+1] :<=: Gk R f.
    apply/fintype.subsetP=>i /imsetP[]/= j _ ->.
    by apply/bigcupP; exists j=>//=; rewrite inE.
  move=>/subset_leqif_cards; apply/leq_trans.
  rewrite card_imset ?cardsT ?card_ord//.
  apply inj_comp=>//; apply perm_inj.
move: m R; apply: ltn_ind; case=>[|m IH R P].
  by move=> _ ??; exists (@perm_one _)=>[[]].
pose E0 := forall k (f : 'I_k.+1 -> 'I_m.+1), 
  injective f -> (k < m)%N -> (k.+1 < #|Gk R f|)%N.
move: (EM E0)=>[P0|].
  (* for the first case, k < #|Gk R f| *)
  have Pi : injective (fun i : 'I_1 => ord_max : 'I_m.+1)
    by move=>i j; rewrite !ord1.
  move: (P 0 (fun=>ord_max) Pi); rewrite /Gk big_ord1.
  rewrite card_gt0=>/set0Pn[j]; rewrite inE=>Pmax.
  pose R1 : {set 'I_m * 'I_m} := 
    [set i : 'I_m * 'I_m | (nlift ord_max i.1, nlift j i.2) \in R].
  have PR1 : forall k (f : 'I_k.+1 -> 'I_m), injective f -> (k < #|Gk R1 f|)%N.
      move=>k f injf; pose g := fun i => nlift ord_max (f i).
      have injg : injective g.
        by move=>a b; rewrite /g=>/lift_inj/injf.
    move: (leq_card f injf); rewrite !card_ord=>Pkm.
    have <- : #| nlift j @: Gk R1 f| = #|Gk R1 f|.
      rewrite card_imset//; apply lift_inj.
    have : (k.+1 <= #|Gk R g :\ j|)%N.
      move: (P0 k g injg Pkm); rewrite (cardsD1 j).
      case: (_ \in _). by rewrite add1n ltnS. by rewrite add0n=>/ltnW.
    move/leq_trans; apply.
    apply/subset_leqif_cards/fintype.subsetP=>i.
    case: (unliftP j i)=>/=[a ->|->]; last by rewrite !inE eqxx.
    rewrite !inE=>/andP[] _ /bigcupP[b _].
    rewrite inE=>Pa; apply/imsetP=>/=.
    by exists a=>//; apply/bigcupP; exists b=>//; rewrite !inE.
  move: (IH m (leqnn _) R1 PR1)=>[s Ps].
  pose t (i : 'I_m.+1) : 'I_m.+1 := match unlift ord_max i with
                               | None => j | Some i => nlift j (s i) end.
  have injt : injective t.
    move=>a b; rewrite /t; case: unliftP=>/=[a' ->|->];
    case: unliftP=>/=[b' ->|->//].
      by move=>/lift_inj/perm_inj->.
    by move=>/eqP; rewrite lift_eqF.
    by move=>/eqP; rewrite eq_liftF.
  exists (perm injt)=>i; rewrite permE /t; 
  by case: unliftP=>[/=a ->|->//]; move: (Ps a); rewrite inE.
have P' k (f : 'I_k -> 'I_m.+1) : injective f -> (k <= #|Gk R f|)%N by case: k f.
rewrite -existsNE=>[[j]]; rewrite -existsNE=>[[f]] /not_implyP[] 
  injf /not_implyP[] Pkm /negP.
move: (P j f injf); rewrite -leqNgt=>Pk1 Pk2.
have Pk : j.+1 = #|Gk R f| by apply/anti_leq/andP; split.
move: {+}Pkm=>/ltnW; rewrite -ltnS=>/subnKC Pc.
pose sl := cast_ord Pc \o lshift _.
pose sr := cast_ord Pc \o @rshift _ _.
have injsl : injective sl by move=>a b /cast_ord_inj/lshift_inj.
have injsr : injective sr by move=>a b /cast_ord_inj/rshift_inj.
move: (inj_ord_perm Pc injf)=>[sf Pf].
have [sg Pg] : exists (s : 'S_m.+1), (s \o sl) @: finset.setT = Gk R f.
  move: (imset_inj_ord (esym Pk))=>[g [injg Pg]].
  by move: (inj_ord_perm Pc injg)=>[s Ps]; exists s; rewrite Pg Ps.
have P1 : (j.+1 < m.+1)%N by rewrite ltnS.
have P2 : (m.+1 - j.+1 < m.+1)%N by rewrite subSS ltnS leq_subr.
pose R1 : {set 'I_j.+1 * 'I_j.+1} :=
  [set i | (sf (sl i.1), sg (sl i.2)) \in R ].
pose R2 : {set 'I_(m.+1-j.+1) * 'I_(m.+1-j.+1)} :=
  [set i | (sf (sr i.1), sg (sr i.2)) \in R ].
have PR1 : forall k (f : 'I_k.+1 -> 'I_j.+1), injective f -> (k < #|Gk R1 f|)%N.
  move=>k g injg; pose g' := sf \o sl \o g.
  have injg' : injective g'.
    by apply/inj_comp=>//; apply/inj_comp=>//; apply/perm_inj.
  move: (P k _ injg'); move=>/leq_trans; apply.
  have -> : #|Gk R1 g| = #|(sg \o sl) @: Gk R1 g|.
    by rewrite card_imset//; apply inj_comp=>//; apply perm_inj.
  apply/subset_leqif_cards/fintype.subsetP=>i.
  move=>/bigcupP/=[a _]; rewrite inE=>Pa.
  have : i \in Gk R f.
    by apply/bigcupP; exists (g a)=>//; rewrite inE Pf.
  rewrite -Pg=>/imsetP[/=b _ Pb].
  by apply/imsetP; exists b=>//; apply/bigcupP; exists a=>//; rewrite !inE/= -Pb.
have PR2 : forall k (f : 'I_k.+1 -> 'I_(m.+1-j.+1)), injective f -> (k < #|Gk R2 f|)%N.
  move=>k g injg.
  pose fm (i : 'I_(j.+1 + k.+1)) := 
    match fintype.split i with
    | inl i => sf (sl i)
    | inr i => sf (sr (g i))
    end.
  have injfm : injective fm.
    move=>a b; rewrite /fm; case: split_ordP=>c->; case: split_ordP=>d->/perm_inj/cast_ord_inj.
    by move=>/lshift_inj->.
    by move=>/eqP; rewrite eq_lrshift.
    by move=>/eqP; rewrite eq_rlshift.
    by move=>/rshift_inj/injg->.
  move: (P' _ fm injfm)=>Pjk.
  have: Gk R fm :<=: Gk R f :|: (sg \o sr) @: Gk R2 g.
    apply/fintype.subsetP=>i; rewrite inE =>/bigcupP[/= a _].
    rewrite inE /fm; case: split_ordP=>b Pa H.
      by apply/orP; left; apply/bigcupP; exists b=>//; rewrite inE Pf.
    case: (split_ordP (cast_ord (esym Pc) ((sg^-1)%g i))).
      move=>c /cast_ord_sym/(f_equal sg); rewrite permKV esymK -/(sl _)=>->.
      by apply/orP; left; rewrite -Pg; apply/imsetP; exists c=>//; rewrite inE.
    move=>c /cast_ord_sym/(f_equal sg); rewrite permKV esymK -/(sr _)=> Pi.
    apply/orP; right; apply/imsetP; exists c=>//.
    by apply/bigcupP; exists b=>//; rewrite !inE/= -Pi.
  move=>/subset_leqif_cards/(leq_trans Pjk)/leq_trans/(_ (@leq_card_setU _ _ _)).
  rewrite -Pk leq_add2l card_imset//; apply/inj_comp=>//; apply/perm_inj.
move: (IH _ P1 _ PR1) (IH _ P2 _ PR2)=>[s1 Ps1][s2 Ps2].
pose s (i : 'I_m.+1) : 'I_m.+1 := 
  match fintype.split (cast_ord (esym Pc) ((sf^-1)%g i)) with
  | inl i => sg (sl (s1 i))
  | inr i => sg (sr (s2 i)) end.
have injs : injective s.
  move=>a b; rewrite /s; case: split_ordP=>c /cast_ord_sym/(f_equal sf); rewrite permKV=>->;
  case: split_ordP=>d /cast_ord_sym/(f_equal sf); rewrite permKV=>-> /perm_inj /cast_ord_inj.
  by move=>/lshift_inj/perm_inj->.
  by move=>/eqP; rewrite eq_lrshift.
  by move=>/eqP; rewrite eq_rlshift.
  by move=>/rshift_inj/perm_inj->.
exists (perm injs) => i.
rewrite permE /s; case: split_ordP=>a /cast_ord_sym/(f_equal sf); rewrite permKV=>->.
by move: (Ps1 a); rewrite inE/= esymK.
by move: (Ps2 a); rewrite inE/= esymK.
Qed.

Theorem Konig_FrobeniusN m (T : ringType) (A : 'M[T]_m) :
  (exists s : 'S_m, forall i, A i (s i) != 0) <->
  (forall k l (f : 'I_k -> 'I_m) (g : 'I_l -> 'I_m), 
    injective f -> injective g -> mxsub f g A = 0 -> (k + l <= m)%N).
Proof.
pose R : {set 'I_m * 'I_m} := [set i | A i.1 i.2 != 0]; split=>[[s Ps]|P1].
  have : exists s : 'S_m, forall i, (i, s i) \in R.
    by exists s; move=>i; rewrite inE/= Ps.
  move=>/Hall_perfect_matching P n l f g injf injg PA.
  case: n f injf PA=>[f _ _|n f injf PA].
    by move: (leq_card g injg); rewrite !card_ord add0n.
  move: (P _ f injf).
  have : Gk R f :<=: ~: g @: finset.setT.
    apply/fintype.subsetP=>i /bigcupP/=[j _]; rewrite !inE/==>/eqP Pi.
    apply/negP=>/imsetP=>/=[[k _ Pk]].
    by move: PA=>/matrixP/(_ j k); rewrite mxE -Pk mxE.
  move=>/subset_leqif_cards P2; move=>/leq_trans/(_ P2).
  rewrite cardsCs finset.setCK card_imset// cardsT !card_ord=>Pn.
  by rewrite addSn addnC -ltn_subRL.  
suff : exists s : 'S_m, forall i, (i, s i) \in R.
  by move=>[s Ps]; exists s=>i; move: (Ps i); rewrite inE.
apply/Hall_perfect_matching=>k f injf.
set n := #|Gk R f|.
have: #|~: (Gk R f)| = (m - n)%N by rewrite cardsCs finset.setCK card_ord.
move=>/imset_inj_ord[] g[] injg Pg.
move: (P1 k.+1 (m-n)%N f g injf injg); rewrite addSn addnC -ltn_subRL subKn.
  move: (finset.subsetT (Gk R f))=>/subset_leqif_cards; 
  by rewrite cardsT card_ord=>->.
apply; apply/matrixP=>i j; rewrite !mxE.
suff : g j \in (~: Gk R f).
  rewrite -implyNN=>/eqP PA; rewrite inE; apply/negP; rewrite negbK.
  by apply/bigcupP; exists i=>//; rewrite !inE/=.
by rewrite Pg; apply/imsetP; exists j.
Qed.

Theorem Konig_Frobenius m (T : ringType) (A : 'M[T]_m) :
  (forall s : 'S_m, exists i, A i (s i) = 0) <->
  (exists k l (f : 'I_k -> 'I_m) (g : 'I_l -> 'I_m), 
    injective f /\ injective g /\ mxsub f g A = 0 /\ (m < k + l)%N).
Proof.
rewrite -iff_not2; apply: (iff_trans (B := (exists s : 'S_m, forall i, A i (s i) != 0))).
  rewrite -existsNE; split=>[[s]|[s P1]].
    by rewrite -forallNE=>Pi; exists s=>i; move: (Pi i)=>/eqP.
  by exists s; rewrite -forallNE=>i; apply/eqP.
rewrite Konig_FrobeniusN; split=>P.
  move=>[k] [l] [f] [g] [injf] [injg] [PA].
  by move=>/(leq_ltn_trans (P _ _ f g injf injg PA)); rewrite ltnn.
move=>k l f g injf injg PA; rewrite leqNgt; apply/negP=>Pm.
by apply P; exists k; exists l; exists f; exists g; do ! split.
Qed.

End PerfectMatching.

Lemma big_option [R : Type] [idx : R] [op : R -> R -> R] 
  [T : finType] (F : option T -> R) :
  \big[op/idx]_i F i = op (F None) (\big[op/idx]_i F (Some i)).
Proof.
rewrite [index_enum _]unlock Finite.enum.unlock/= /option_enum.
by rewrite big_cons big_map.
Qed.

Section Birkhoff_doubly_stochastic.
Variable (R : numFieldType).

Lemma doubly_stochastic_mxsub0 m (A : 'M[R]_m) :
  A \is doubly_stochastic ->
  forall k l (f : 'I_k -> 'I_m) (g : 'I_l -> 'I_m),
  injective f -> injective g -> mxsub f g A = 0 -> (k + l <= m)%N.
Proof.
move=>/doubly_stochasticP [PA1][PA2]PA3 k l f g injf injg Psub.
move: (leq_card f injf); rewrite !card_ord=>/subnKC Pk.
move: (leq_card g injg); rewrite !card_ord=>/subnKC Pl.
move: (inj_ord_perm Pk injf)=>[sf Pf].
move: (inj_ord_perm Pl injg)=>[sg Pg].
have: \sum_i\sum_j A i j = m%:R.
  under eq_bigr do rewrite PA2.
  by rewrite sumr_const card_ord.
rewrite (reindex_perm sf)/= (big_split_ord_cast Pk)/=.
under eq_bigr do rewrite PA2.
rewrite sumr_const card_ord exchange_big/= (reindex_perm sg)/=.
rewrite (big_split_ord_cast Pl)/=.
have Pli (i : 'I_l) : \sum_(i0 < m - k) A (sf (cast_ord Pk (rshift k i0)))
           (sg (cast_ord Pl (lshift (m - l) i))) = 1.
  rewrite -(PA3 (g i)) (reindex_perm sf)/= (big_split_ord_cast Pk)/= 
    [X in X + _]big1 ?add0r Pg// =>j _.
  by move: Psub=>/matrixP/(_ j i); rewrite !mxE Pf Pg.
under eq_bigr do rewrite Pli.
rewrite sumr_const card_ord addrA -natrD=>/eqP; rewrite eq_sym -subr_eq=>/eqP.
rewrite -(@ler_nat R)=><-; rewrite lerBlDl lerDr.
by apply sumr_ge0=>i _; apply sumr_ge0=>j _.
Qed.

Lemma doubly_stochastic_cards_neq0 m (A : 'M[R]_m) :
  A \is doubly_stochastic -> (m <= #|[set i | A i.1 i.2 != 0%R]%SET|)%N.
Proof.
move=>/doubly_stochastic_mxsub0; rewrite -Konig_FrobeniusN=>[[s Ps]].
have : (fun i => (i, s i)) @: finset.setT :<=: [set i | A i.1 i.2 != 0].
  by apply/fintype.subsetP=>i; rewrite inE=>/imsetP[j _ ->].
move=>/subset_leqif_cards; rewrite card_imset ?cardsT ?card_ord; last by apply.
by move=>i j P; inversion P.
Qed.

Lemma Birkhoff_doubly_stochastic m : 
  [set A : 'M[R]_m | A \is doubly_stochastic]%classic =
  conv [set A : 'M[R]_m | is_perm_mx A]%classic.
Proof.
apply/seteqP; split=>A; last first.
  rewrite /conv/==>[[F [c [f]]]][P1][P2][P3]P4.
  apply/doubly_stochasticP; do ! split.
  - move=>i j; rewrite P4 summxE sumr_ge0// =>k _; rewrite mxE mulr_ge0//.
    by move: (P1 k)=>/andP[].
    by move: (P3 k); rewrite inE/==>/is_perm_mxP[s ->]; rewrite !mxE; case: eqP.
  - move=>i; rewrite P4; under eq_bigr do rewrite summxE.
    rewrite -P2 exchange_big/=; apply eq_bigr=>j _.
    move: (P3 j); rewrite inE -[RHS]mulr1/==>/is_perm_mxP[s ->].
    move: (perm_mx_doubly_stochastic R s)=>/doubly_stochasticP[ _ [/(_ i)<- _]].
    by rewrite mulr_sumr; apply eq_bigr=>k _; rewrite mxE.
  - move=>i; rewrite P4; under eq_bigr do rewrite summxE.
    rewrite -P2 exchange_big/=; apply eq_bigr=>j _.
    move: (P3 j); rewrite inE -[RHS]mulr1/==>/is_perm_mxP[s ->].
    move: (perm_mx_doubly_stochastic R s)=>/doubly_stochasticP[ _ [_ /(_ i)<-]].
    by rewrite mulr_sumr; apply eq_bigr=>k _; rewrite mxE.
pose n := #|[set i | A i.1 i.2 != 0]%SET|%R.
have : #|[set i | A i.1 i.2 != 0]%SET|%R = n by [].
move: n=>n Pn; move: n A Pn; apply: ltn_ind; case.
  move=>_ A /= P1 P2; move: (doubly_stochastic_cards_neq0 P2); 
  rewrite P1 leqn0=>/eqP/esym Pm.
  case: m / Pm A P1 P2=>A _ _.
  rewrite /conv/=; exists 'I_1; exists (fun=>1); exists (fun=>perm_mx (perm_one _)).
  rewrite ler01 lexx !big_ord1 scale1r; do ! split.
  by move=>_; rewrite inE/=; apply/is_perm_mxP; exists (perm_one  _).
  by rewrite !mx_dim0E.
move=>n /= IH A PA1 PA.
move: (@doubly_stochastic_mxsub0 _ A PA).
rewrite -Konig_FrobeniusN=>[[s Ps]].
case: m IH A PA1 PA s Ps=>[_ A _ _ _ _|m IH A PA1 PA s Ps].
  rewrite /conv/=; exists 'I_1; exists (fun=>1); exists (fun=>A).
  rewrite ler01 lexx !big_ord1 scale1r; do ! split=>//.
  by move=> _; rewrite inE/=; apply/existsP; exists (perm_one _); rewrite !mx_dim0E.
pose v := \row_i A i (s i).
pose c := sort_v v 0 ord_max.
have Pvi i : c <= A i (s i).
  move: (perm_sort_v v)=>[t Pv].
  have : v \is rv_cmp.
    apply/realmx_is_cmp/nnegmx_real/nnegmxP=>j k.
    by rewrite nnegrE mxE doubly_stochastic_ge0.
  move=>/sort_v_nonincreasing/(_ ((t^-1)%g i) ord_max).
  by rewrite -/c -ltnS/= -Pv mxE permKV /v mxE; apply.
have [Pc|/eqP Pc] := @eqP _ c 1.
  have PAi i : A i (s i) = 1.
    apply/le_anti; rewrite doubly_stochastic_le1//=.
    rewrite -Pc; apply Pvi.
  have -> : A = perm_mx s.
    apply/matrixP=>i j.
    have [->|/eqP Pj] := @eqP _ j (s i); first by rewrite !mxE eqxx PAi.
    move: {+}PA=>/doubly_stochasticP[] _ []/(_ i) /eqP + _.
    rewrite (bigD1 (s i))//= PAi addrC eq_sym -subr_eq subrr eq_sym.
    rewrite psumr_eq0/==>[k _|/allP/(_ j)]; 
      first by rewrite doubly_stochastic_ge0.
    rewrite mem_index_enum=>/(_ isT)/implyP/(_ Pj)=>/eqP->.
    by move: Pj=>/negPf; rewrite !mxE eq_sym=>->.
  exists 'I_1; exists (fun=>1); exists (fun=>perm_mx s).
  rewrite ler01 lexx !big_ord1 scale1r; do ! split=>//.
  by move=> _; rewrite inE/=; apply/existsP; exists s.
move: (perm_sort_v v)=>[t Pt].
have cgt0 : 0 < c.
  rewrite /c -Pt; rewrite mxE /v mxE lt_def Ps/=.
  by apply/nnegmxP/doubly_stochastic_nnegmx.
have cle1 : c < 1.
  by rewrite lt_def eq_sym Pc/= /c -Pt mxE /v mxE doubly_stochastic_le1.
pose B : 'M_m.+1 := (1-c)^-1 *: (A - c *: perm_mx s).
have PB : B \is doubly_stochastic.
  apply/doubly_stochasticP; do ! split.
  - move=>i j; rewrite !mxE mulr_ge0//.
      by rewrite invr_ge0 subr_ge0// ltW.
    case: eqP=>[<-|]; first by rewrite mulr1 subr_ge0.
    by rewrite mulr0 subr0 doubly_stochastic_ge0.
  - move=>i; rewrite (bigD1 (s i))//=.
    have -> : (\sum_(j < m.+1 | j != s i) B i j) = 
      (1-c)^-1 * \sum_(j < m.+1 | j != s i) A i j.
      rewrite mulr_sumr; apply eq_bigr=>j /negPf Pj; 
      by rewrite !mxE eq_sym Pj mulr0 subr0.
    rewrite !mxE eqxx mulr1 -mulrDr addrAC.
    move: {+}PA=>/doubly_stochasticP[] _ []/(_ i) + _.
    by rewrite (bigD1 (s i))//==>->; rewrite mulVf// subr_eq add0r eq_sym.
  - move=>i; rewrite (bigD1 ((s^-1)%g i))//=.
    have -> : (\sum_(j < m.+1 | j != (s^-1)%g i) B j i) = 
      (1-c)^-1 * \sum_(j < m.+1 | j != (s^-1)%g i) A j i.
      rewrite mulr_sumr; apply eq_bigr=>j /negPf Pj.
      by rewrite !mxE -(inj_eq (@perm_inj _ s^-1)) permK Pj mulr0 subr0.
    rewrite !mxE permKV eqxx mulr1 -mulrDr addrAC.
    move: {+}PA=>/doubly_stochasticP[] _ [] _ /(_ i).
    by rewrite (bigD1 ((s^-1)%g i))//==>->; rewrite mulVf// subr_eq add0r eq_sym.
have /IH/(_ B erefl PB) : (#|[set i | B i.1 i.2 != 0%R]%SET| < n.+1)%N.
  suff : [set i | B i.1 i.2 != 0%R]%SET :<=: 
    [set i | A i.1 i.2 != 0%R]%SET :\ (t ord_max, s (t ord_max)).
    move=>/subset_leqif_cards/leq_trans; apply.
    by rewrite -ltnS -subn_gt0 -PA1 (cardsD1 (t ord_max, s (t ord_max))) addnK inE Ps.
  apply/fintype.subsetP=>[[i j]]; rewrite !inE/= !mxE mulf_eq0.
  rewrite invr_eq0 subr_eq0 eq_sym; move: {+}Pc=>/negPf->/=/eqP.
  case: eqP=>[<-|].
    rewrite mulr1 Ps andbT=>P1; apply/eqP=>P2.
    by inversion P2; apply P1; rewrite H0 /c -Pt !mxE subrr.
  rewrite mulr0 subr0=>+/eqP->; rewrite andbT=>P1; apply/eqP=>P2.
  by inversion P2; apply P1; rewrite H0 H1.
move=>[T][cf]/=[Bf][P1][P2][P3]P4.
exists (option T).
exists (fun i => match i with None => c | Some i => (1-c) * cf i end).
exists (fun i => match i with None => perm_mx s | Some i => Bf i end).
do ! split.
- case=>[i|]; last by apply/andP; split; apply/ltW.
  move: (P1 i)=>/andP[] Pi1 Pi2.
  apply/andP; split.
    by apply/mulr_ge0=>//; rewrite subr_ge0 ltW.
  by apply/mulr_ile1=>//; rewrite ltW// ?subr_gt0// gtrBl.
- by rewrite big_option -mulr_sumr P2 mulr1 addrC subrK.
- by case=>[i//|]; rewrite inE/=; apply/existsP; exists s.
- rewrite big_option.
  under eq_bigr do rewrite -scalerA.
  rewrite -scaler_sumr -P4 /B scalerA mulfV.
    by rewrite subr_eq add0r eq_sym.
  by rewrite scale1r addrC subrK.
Qed.

Lemma mxsub_doubly_substochastic m (A : 'M[R]_m) n (f g : 'I_n -> 'I_m) :
  A \is doubly_stochastic -> injective f -> injective g ->
    mxsub f g A \is doubly_substochastic.
Proof.
move=>/doubly_stochasticP[]PA1[]PA2 PA3 injf injg.
apply/doubly_substochasticP; do ! split.
- by move=>i j; rewrite mxE.
- move=>i; move: (PA2 (f i)).
  move: {+}injg=>/leq_card; rewrite !card_ord=>/subnKC H.
  move: (inj_ord_perm H injg)=>[s ->].
  rewrite (reindex_perm s)/= (big_split_ord_cast H)/==><-.
  under eq_bigr do rewrite mxE/=.
  by rewrite lerDl sumr_ge0.
- move=>i; move: (PA3 (g i)).
  move: {+}injf=>/leq_card; rewrite !card_ord=>/subnKC H.
  move: (inj_ord_perm H injf)=>[s ->].
  rewrite (reindex_perm s)/= (big_split_ord_cast H)/==><-.
  under eq_bigr do rewrite mxE/=.
  by rewrite lerDl sumr_ge0.
Qed.

Lemma doubly_substochastic_ulsubP m (A : 'M[R]_m) : 
  A \is doubly_substochastic <-> 
    exists2 B : 'M_(m+m), B \is doubly_stochastic & A = ulsubmx B.
Proof.
split; last first.
  move=>[B]/doubly_stochasticP[PB1][PB2]PB3.
  move=>->; apply/doubly_substochasticP; do ! split.
  - by move=>i j; rewrite !mxE.
  - move=>i; rewrite -(PB2 (lshift _ i)) big_split_ord/=.
    under eq_bigr do rewrite !mxE.
    by rewrite lerDl sumr_ge0.
  - move=>i; rewrite -(PB3 (lshift _ i)) big_split_ord/=.
    under eq_bigr do rewrite !mxE.
    by rewrite lerDl sumr_ge0.
move=>/doubly_substochasticP[]PA1[]PA2 PA3.
pose B := \row_i (1-\sum_j A i j).
pose C := \row_i (1-\sum_j A j i).
exists (block_mx A (diag_mx B) (diag_mx C) A^T); last by rewrite block_mxKul.
apply/doubly_stochasticP; do ! split.
- move=>i j; case: (split_ordP i)=>a ->; case: (split_ordP j)=>b ->.
    by rewrite block_mxEul.
    by rewrite block_mxEur !mxE; case: eqP; rewrite ?mulr0n// mulr1n subr_ge0.
    by rewrite block_mxEdl !mxE; case: eqP; rewrite ?mulr0n// mulr1n subr_ge0.
  by rewrite block_mxEdr mxE.
- move=>i; case: (split_ordP i)=>a ->; apply/eqP.
    rewrite big_split_ord/=; under eq_bigr do rewrite block_mxEul.
    rewrite eq_sym -subr_eq (bigD1 a)//= big1=>[b/negPf nb|];
    rewrite block_mxEur mxE ?eqxx 1?eq_sym ?nb ?mulr0n//.
    by rewrite mulr1n addr0 mxE subKr.
  rewrite big_split_ord/= (bigD1 a)//= big1=>[b/negPf nb|];
  rewrite block_mxEdl mxE ?eqxx 1?eq_sym ?nb ?mulr0n//.
  under eq_bigr do rewrite block_mxEdr mxE.
  by rewrite mulr1n addr0 mxE subrK.
- move=>i; case: (split_ordP i)=>a ->; apply/eqP.
    rewrite big_split_ord/=; under eq_bigr do rewrite block_mxEul.
    rewrite eq_sym -subr_eq (bigD1 a)//= big1=>[b/negPf nb|];
    rewrite block_mxEdl mxE ?eqxx ?nb ?mulr0n//.
    by rewrite mulr1n addr0 mxE subKr.
  rewrite big_split_ord/= (bigD1 a)//= big1=>[b/negPf nb|];
  rewrite block_mxEur mxE ?eqxx ?nb ?mulr0n//.
  under eq_bigr do rewrite block_mxEdr mxE.
  by rewrite mulr1n addr0 mxE subrK.
Qed.

Lemma ulsub_doubly_substochastic m n (A : 'M[R]_(m+n)) :
  A \is doubly_stochastic -> ulsubmx A \is doubly_substochastic.
Proof.
move=>/doubly_stochasticP[P1][P2]P3.
apply/doubly_substochasticP; split; first by move=>x y; rewrite !mxE.
split=>i.
  move: (P2 (lshift _ i)); rewrite big_split_ord/==><-.
  by under eq_bigr do rewrite !mxE; rewrite lerDl sumr_ge0.
move: (P3 (lshift _ i)); rewrite big_split_ord/==><-.
by under eq_bigr do rewrite !mxE; rewrite lerDl sumr_ge0.
Qed.

Definition is_partial_perm_mx m (A : 'M[R]_m) := 
    [exists s : 'S_(m+m), A == ulsubmx (perm_mx s)].

Lemma is_partial_perm_mxP m (A : 'M[R]_m) :
  reflect (exists s : 'S_(m+m), A = ulsubmx (perm_mx s)) (is_partial_perm_mx A).
Proof. by apply/(iffP existsP)=>[[x/eqP]|[x/eqP]]; exists x. Qed.

Theorem Birkhoff_doubly_substochastic m :
  [set A : 'M[R]_m | A \is doubly_substochastic]%classic =
  conv [set A : 'M[R]_m | is_partial_perm_mx A]%classic.
Proof.
apply/seteqP; split=>A /=.
  move=>/doubly_substochastic_ulsubP [B PB PA].
  have: [set` doubly_stochastic]%classic B by [].
  rewrite Birkhoff_doubly_stochastic=>[[T][c][f][Pc1][Pc2][Pc3]Pc4].
  exists T; exists c; exists (fun i => ulsubmx (f i)); do ! split=>//.
    move=>i; rewrite inE/=; apply/is_partial_perm_mxP.
    by move: (Pc3 i); rewrite inE/==>/is_perm_mxP[s ->]; exists s.
  rewrite PA Pc4 /ulsubmx !linear_sum/=.
  by under eq_bigr do rewrite !linearZ.
move=>[T][c][f][Pc1][Pc2][Pc3]Pc4; apply/doubly_substochastic_ulsubP.
have Pf i : {s : 'S_(m+m) | f i = ulsubmx (perm_mx s)}.
  by move: (Pc3 i); rewrite inE=>/=/existsP/cid[s /eqP]; exists s.
pose B := \sum_i c i *: perm_mx (projT1 (Pf i)).
exists B.
  suff : [set` doubly_stochastic]%classic B by [].
  rewrite Birkhoff_doubly_stochastic; exists T; exists c; 
  exists (fun i => perm_mx (projT1 (Pf i))); do ! split=>//.
  move=>i; rewrite inE; apply/perm_mx_is_perm.
rewrite Pc4 /B /ulsubmx !linear_sum/=; apply eq_bigr=>i _.
by rewrite !linearZ/=; move: (projT2 (Pf i))=>{1}->.
Qed.

Lemma perm_exd (T : finType) (f : T -> option T) : 
  (forall i j, f i = f j -> i = j \/ f i = None) ->
  exists s : {perm T}, (forall i, f i = None \/ f i = Some (s i)). 
Proof.
move=>Pf.
pose sl : {pred T} := fun i => f i == None.
pose sr : {pred T} := fun i => [forall j, f j != Some i].
pose h (i : T) := match f i with | Some i => i | _ => i end.
have injh : {in predC sl &, injective h}.
  move=>i j; rewrite !inE /sl /h; 
  case Ei: (f i)=>[i'|//]; case Ej: (f j)=>[j'|//] _ _ Peq.
  by move: {+}Ei; rewrite Peq -Ej=>/Pf; rewrite Ei=>[[]].
have : #|predC sr| = #|fintype.image h (predC sl)|.
  apply/eq_card=>i; apply/eqb_iff; split.
    rewrite inE /sr negb_forall=>/existsP[j]; rewrite negbK=>/eqP Pj.
    apply/mapP; exists j; last by rewrite /h Pj.
    by rewrite mem_enum inE /sl Pj.
  move=>/mapP[j]; rewrite mem_enum !inE /sl /sr negb_forall /h.
  by case E: (f j)=>[a|//] _ ->; apply/existsP; exists j; rewrite E eqxx.
rewrite card_in_image// =>Pcs.
move: (cardC sr) (cardC sl)=><-; rewrite Pcs=>/addIn Pc.
pose g (i : T) := match (i \in sl) =P true with
                  | ReflectT E => enum_val (cast_ord Pc (enum_rank_in E i))
                  | ReflectF _ => match f i with 
                                  | Some i => i
                                  | None => i
                                  end
                  end.
have injg : injective g.
  move=>a b; rewrite /g; case: eqP; last first.
    rewrite {1}/in_mem/= /sl; case Ea: (f a)=>[a'|//] _.
    case: eqP=>[p Pa|]; last first.
      rewrite /in_mem/=; case Eb: (f b)=>[b'|//] _ Pab; move: {+}Ea.
      by rewrite Pab -Eb=>/Pf; rewrite Ea=>[[]].
    move: (enum_valP (cast_ord Pc (enum_rank_in p b))); 
    by rewrite -Pa /in_mem/==>/forallP/(_ a); rewrite Ea eqxx.
  move=>pa; case: eqP=>[pb|].
    move=>/enum_val_inj/cast_ord_inj/enum_rank_in_inj; apply;
    by move: pa pb; rewrite /in_mem/= /sl /sr; case: eqP.
  rewrite {1}/in_mem/=/sl; case Eb: (f b)=>[b'|//] _ Pb.
  move: (enum_valP (cast_ord Pc (enum_rank_in pa a))).
  by rewrite Pb /in_mem/==>/forallP/(_ b); rewrite Eb eqxx.
exists (perm injg).
  move=>i; rewrite permE /g; case: eqP.
    by left; move: p; rewrite /in_mem/= /sl; case: eqP.
  by rewrite /in_mem/= /sl; case: (f i)=>//; right.
Qed.

Lemma is_partial_perm_mx_le m (A : 'M[R]_m) : 
  is_partial_perm_mx A ->
  exists2 B, is_perm_mx B & elem_lemx A B.
Proof.
move=>/is_partial_perm_mxP[s PA].
pose f (i : 'I_m) := match fintype.split (s (lshift _ i)) with
                     | inl i => Some i
                     | inr _ => None
                     end.
have Pf i j : f i = f j -> i = j \/ f i = None.
  rewrite /f; case: split_ordP=>[a Pa|]; last by right.
  case: split_ordP=>[b Pb P|]; last by right.
  by move: Pa Pb; inversion P=><- /perm_inj/lshift_inj; left.
move: (perm_exd Pf)=>/= [t Pt].
exists (perm_mx t); first by apply/perm_mx_is_perm.
apply/elem_lemxP=>i j.
rewrite PA !mxE; case: eqP=>// Pi.
move: (Pt i); rewrite /f Pi; case: split_ordP=>k.
by move=>/lshift_inj->[//|P]; inversion P; rewrite eqxx.
by move=>/eqP; rewrite eq_lrshift.
Qed.

Lemma doubly_substochastic_elem_leP m (A : 'M[R]_m) : A \is a nnegmx ->
  A \is doubly_substochastic <->
    exists2 B, B \is doubly_stochastic & elem_lemx A B.
Proof.
move=>HA; split; last first.
  move=>[B /doubly_stochasticP[P1 [P2 P3]] /elem_lemxP PB2].
  apply/doubly_substochasticP; do ! split.
  - by move=>i j; rewrite -nnegrE; apply/nnegmxP.
  - by move=>i; rewrite -(P2 i) ler_sum.
  - by move=>i; rewrite -(P3 i) ler_sum.
move=>PA; have: [set` doubly_substochastic]%classic A by [].
rewrite Birkhoff_doubly_substochastic=>[[T][c][f][Pc1][Pc2][Pf]->].
have Pfi i : {s : 'S_m | elem_lemx (f i) (perm_mx s)}.
  move: (Pf i); rewrite inE/==>/is_partial_perm_mx_le;
  by move=>/cid2[B]/is_perm_mxP/cid[s ->]; exists s.
pose B := \sum_i c i *: perm_mx (projT1 (Pfi i)).
exists B.
  suff: [set` doubly_stochastic]%classic B by [].
  rewrite Birkhoff_doubly_stochastic; exists T; exists c; 
  exists (fun i=>perm_mx (projT1 (Pfi i))); do ! split=>//.
  move=>i; rewrite inE/=; apply/perm_mx_is_perm.
rewrite /B; apply/elem_lemxP=>i j; rewrite !summxE ler_sum//==>k _.
move: (projT2 (Pfi k))=>/elem_lemxP Pk.
by rewrite 2!mxE ler_wpM2l//; move: (Pc1 k)=>/andP[].
Qed.

End Birkhoff_doubly_stochastic.

Section S2.
Variable (R : realFieldType).

Lemma rV_rv_cmp m (v : 'rV[R]_m) : v \is rv_cmp.
Proof. by apply/rv_cmpP=>i j; apply/real_comparable; apply/num_real. Qed.
#[local] Hint Extern 0 (is_true (_ \is rv_cmp)) => apply: rV_rv_cmp : core.

Lemma sort_vZ_ge0 m (x : 'rV[R]_m) (c : R) : 
  0 <= c -> sort_v (c *: x) = c *: sort_v x.
Proof.
move=>Pc; apply/sort_v_eq.
by move: (perm_sort_v x)=>[s<-]; exists s; rewrite !col_permE scalemxAl.
apply/rv_nonincreasingP=>i j Pij; rewrite mxE [leRHS]mxE ler_wpM2l//.
by move: Pij; apply/sort_v_nonincreasing.
Qed.

(* move *)
Definition perm_rev_ord {n} := (perm (@rev_ord_inj n)).

Lemma sort_vZ_le0 m (x : 'rV[R]_m) (c : R) : 
  c <= 0 -> sort_v (c *: x) = c *: (col_perm perm_rev_ord (sort_v x)).
Proof.
move=>Pc; apply/sort_v_eq.
  move: (perm_sort_v x)=>[s<-]; exists (perm_rev_ord * s)%g; 
  by rewrite col_permE -scalemxAl -col_permM col_permE.
apply/rv_nonincreasingP=>i j Pij; rewrite mxE [leRHS]mxE ler_wnM2l//.
rewrite mxE [leRHS]mxE; apply/sort_v_nonincreasing=>//.
by rewrite !permE /=; apply/leq_sub2l; rewrite ltnS.
Qed.

Lemma weak_majorizeZ m (x y : 'rV[R]_m) (c : R) :
  0 <= c -> weak_majorize x y -> weak_majorize (c *: x) (c *: y).
Proof.
move=>Pc Pxy i.
under eq_bigr do rewrite (sort_vZ_ge0 _ Pc) mxE.
under [leRHS]eq_bigr do rewrite (sort_vZ_ge0 _ Pc) mxE.
by rewrite -!mulr_sumr ler_wpM2l.
Qed.

(* Lemma rv_nonincreasing_itv m (x : 'rV[R]_m) (t : R) : x \is rv_nonincreasing ->
  exists i : nat, forall j : 'I_m, 
  ((j < i)%N -> t <= x 0 j) /\ ((i <= j)%N -> x 0 j <= t).
Proof.
move: m x; apply: row_ind=>[A _ | n c A IH PA]; first by exists 0=>[[]].
have PA1 : A \is rv_nonincreasing.
  apply/rv_nonincreasingP=>i j Pij.
  move: PA=>/rv_nonincreasingP/(_ (rshift 1 i) (rshift 1 j)) /=.
  by rewrite leq_add2l=>/(_ Pij); rewrite !row_mxEr.
move: (IH PA1)=>[] i Pi.
have [Pt | /ltW Pt] := leP t (c 0 0).
  exists i.+1 => j; case: (split_ordP j)=>/=[k ->|k ->].
  - by rewrite /= ord1 row_mxEl; split.
  - by rewrite /= row_mxEr add1n !ltnS.
exists 0=>j; split=>// _; apply/(le_trans (y := row_mx c A 0 (lshift n 0))).
by apply/rv_nonincreasingP. by rewrite row_mxEl.
Qed. *)

Lemma rv_nonincreasing_itv m (x : 'rV[R]_m) (t : R) : x \is rv_nonincreasing ->
  exists i : nat, forall j : 'I_m, 
  ((j < i)%N -> t < x 0 j) /\ ((i <= j)%N -> x 0 j <= t).
Proof.
move: m x; apply: row_ind=>[A _ | n c A IH PA]; first by exists 0=>[[]].
have PA1 : A \is rv_nonincreasing.
  apply/rv_nonincreasingP=>i j Pij.
  move: PA=>/rv_nonincreasingP/(_ (rshift 1 i) (rshift 1 j)) /=.
  by rewrite leq_add2l=>/(_ Pij); rewrite !row_mxEr.
move: (IH PA1)=>[] i Pi.
have [Pt | Pt] := leP (c 0 0) t.
  exists 0=>j; split=>// _; apply/(le_trans (y := row_mx c A 0 (lshift n 0))).
  by apply/rv_nonincreasingP. by rewrite row_mxEl.
exists i.+1 => j; case: (split_ordP j)=>/=[k ->|k ->].
- by rewrite /= ord1 row_mxEl; split.
- by rewrite /= row_mxEr add1n !ltnS.
Qed.

Lemma weak_majorize_maxP m (x y : 'rV[R]_m) :
  weak_majorize x y <-> 
    (forall t : R, \sum_i maxr (x 0 i - t) 0 <= \sum_i maxr (y 0 i - t) 0).
Proof.
have P0 (s : 'S_m) (v : 'rV[R]_m) t : 
  \sum_i maxr (v 0 i - t) 0 = \sum_i maxr (col_perm s v 0 i - t) 0.
by rewrite (reindex_perm s)/=; apply eq_bigr=>i _; rewrite mxE.
split.
- move=>P t; move: (sort_v_nonincreasing (v := x))=>
    /(_ (rV_rv_cmp _))/rv_nonincreasingP/(rv_nonincreasing_itv t)[i Pi].
  move: (perm_sort_v x)=>[sx Psx]; rewrite (P0 sx) Psx.
  move: (perm_sort_v y)=>[sy Psy]; rewrite [leRHS](P0 sy) Psy.
  have ->: \sum_i0 maxr (sort_v x 0 i0 - t) 0 = 
    \sum_(i0 < m | (i0 < i)%N) sort_v x 0 i0 - \sum_(i0 < m | (i0 < i)%N) t.
    rewrite (bigID (fun j : 'I_m => (j < i)%N))/= [X in _ + X]big1=>[j|].
      rewrite -leqNgt=>Pj; move: (Pi j)=>[] _ /(_ Pj).
      by rewrite -subr_le0 maxEle=>->.
    rewrite addr0 raddf_sum/= -big_split/=; apply eq_bigr=>j Pj.
    by move: (Pi j)=>[]/(_ Pj)/ltW + _; rewrite -subr_ge0 /maxr ltNge =>->.
  rewrite lerBlDr; move: P; rewrite weak_majorize_ltP=>/(_ i)/le_trans; apply.
  rewrite -lerBlDr raddf_sum/= -big_split/= [leRHS](bigID (fun j : 'I_m => (j < i)%N))/= -[leLHS]addr0.
  apply: lerD.
    by apply ler_sum=>j _; rewrite le_max lexx.
    by apply sumr_ge0=>j _; rewrite le_max lexx orbT.
- move=>P i; move: (P (sort_v y 0 i)). 
  move: (perm_sort_v x)=>[sx Psx]; rewrite (P0 sx) Psx.
  move: (perm_sort_v y)=>[sy Psy]; rewrite [leRHS](P0 sy) Psy.
  have -> : \sum_i0 maxr (sort_v y 0 i0 - sort_v y 0 i) 0 = \sum_(j < m | (j <= i)%N) (sort_v y 0 j - sort_v y 0 i).
    rewrite (bigID (fun j : 'I_m => (j <= i)%N))/= [X in _ + X]big1 ?addr0=>[j|].
      by rewrite -ltnNge=>/ltnW Pij; rewrite maxEle subr_le0 sort_v_nonincreasing.
    by apply eq_bigr=>j Pj; rewrite /maxr subr_lt0 ltNge sort_v_nonincreasing.
  rewrite big_split/= -raddf_sum/= lerBrDl; apply: le_trans.
  rewrite -lerBlDl raddf_sum -big_split/= -[leLHS]addr0.
  rewrite [leRHS](bigID (fun j : 'I_m => (j <= i)%N))/= lerD//.
    by apply ler_sum=>j _; rewrite le_max lexx.
  by apply sumr_ge0=>j _; rewrite le_max lexx orbT.
Qed.

Lemma majorize_normP m (x y : 'rV[R]_m) :
  majorize x y <-> 
    (forall t : R, \sum_i `| x 0 i - t | <= \sum_i `| y 0 i - t |).
Proof.
have P0 (s : 'S_m) (v : 'rV[R]_m) t : 
  \sum_i`|v 0 i - t| = \sum_i `|col_perm s v 0 i - t|.
by rewrite (reindex_perm s)/=; apply eq_bigr=>i _; rewrite mxE.
have P1 (v : 'rV[R]_m) t i : 
  \sum_(j < m | (j < i)%N) (v 0 j - t) + \sum_(j < m | ~~(j < i)%N) (t - v 0 j) = 
  (2 * \sum_(j < m | (j < i)%N) v 0 j) - \sum_j v 0 j - \sum_(j < m | (j < i)%N) t + 
  \sum_(j < m | ~~(j < i)%N) t.
  rewrite !big_split/= -!raddf_sum/= addrA addrC !addrA; do 2 f_equal.
  apply/eqP; rewrite eq_sym subr_eq addrC [X in X + _](bigID (fun j : 'I_m => (j < i)%N))/=.
  by rewrite addrA addrK mulrDl mul1r.
split.
- move=>P t; move: (sort_v_nonincreasing (v := x))=>
    /(_ (rV_rv_cmp _))/rv_nonincreasingP/(rv_nonincreasing_itv t)[i Pi].
  move: (perm_sort_v x)=>[sx Psx]; rewrite (P0 sx) Psx.
  move: (perm_sort_v y)=>[sy Psy]; rewrite [leRHS](P0 sy) Psy.
  have -> : \sum_i0 normr (sort_v x 0 i0 - t) = 
    \sum_(j < m | (j < i)%N) (sort_v x 0 j - t) + \sum_(j < m | ~~(j < i)%N) (t - sort_v x 0 j).
    rewrite (bigID (fun j : 'I_m => (j < i)%N))/=; f_equal; apply eq_bigr=>j Pj.
      by rewrite ger0_norm// subr_ge0; move: (Pi j)=>[]/(_ Pj)/ltW.
    by rewrite ler0_norm ?opprB// subr_le0; move: (Pi j)=>[] _; apply; rewrite leqNgt.
  rewrite P1; move: P; rewrite majorize_ltP=>[[/(_ i) P2 ->]].
  apply/(le_trans (y := \sum_(j < m | (j < i)%N) (sort_v y 0 j - t) + \sum_(j < m | ~~(j < i)%N) (t - sort_v y 0 j))).
    by rewrite P1 -!addrA lerD2r ler_wpM2l.
  rewrite [leRHS](bigID (fun j : 'I_m => (j < i)%N))/= lerD//; apply ler_sum=>j _.
    apply/ler_norm.
  rewrite -normrN opprB; apply/ler_norm.
- move: (perm_sort_v x) (perm_sort_v y) =>[sx Psx] [sy Psy] P.
  have Ps : \sum_i sort_v x 0 i = \sum_i sort_v y 0 i.
    case: m x y P0 P1 sx Psx sy Psy P=> [x y _ _ _ _ _ _ _|
      m x y P0 P1 sx Psx sy Psy P]; first by rewrite !big_ord0.
    apply/le_anti/andP; split.
    - pose t := (minr (sort_v x 0 ord_max) (sort_v y 0 ord_max)); move: (P t).
      suff -> : \sum_i normr (y 0 i - t) = \sum_i sort_v y 0 i + \sum_(i < m.+1)-t.
      suff -> : \sum_i normr (x 0 i - t) = \sum_i sort_v x 0 i + \sum_(i < m.+1)-t.
        by rewrite lerD2r.
      1 : rewrite (P0 sx) Psx -big_split. 2 : rewrite (P0 sy) Psy -big_split.
      1,2: by apply eq_bigr=>i _; rewrite ger0_norm// subr_ge0 
              /t ge_min sort_v_nonincreasing// ?orbT//= -ltnS.
    - pose t := (maxr (sort_v x 0 0) (sort_v y 0 0)); move: (P t).
      suff -> : \sum_i normr (y 0 i - t) = \sum_(i < m.+1) t - \sum_i sort_v y 0 i.
      suff -> : \sum_i normr (x 0 i - t) = \sum_(i < m.+1) t - \sum_i sort_v x 0 i.
        by rewrite lerD2l lerN2.
      1 : rewrite (P0 sx) Psx. 2 : rewrite (P0 sy) Psy.
      1,2: rewrite raddf_sum -big_split/=; apply eq_bigr=>i _;
        by rewrite -normrN opprB ger0_norm// subr_ge0 /t le_max sort_v_nonincreasing// ?orbT//=.
  split=>// i.
  move: (P (sort_v y 0 i)).
  have -> : \sum_i0 normr (y 0 i0 - sort_v y 0 i) = 
    \sum_(j < m | (j < i)%N) (sort_v y 0 j - sort_v y 0 i) + 
    \sum_(j < m | ~~(j < i)%N) (sort_v y 0 i - sort_v y 0 j).
    rewrite (P0 sy) Psy (bigID (fun j : 'I_m => (j < i)%N))/=; f_equal; apply eq_bigr=>j Pj.
      by rewrite ger0_norm// subr_ge0 sort_v_nonincreasing// ltnW.
    by rewrite -normrN opprB ger0_norm// subr_ge0 sort_v_nonincreasing// leqNgt.
  have : \sum_i0 normr (x 0 i0 - sort_v y 0 i) >= 
    \sum_(j < m | (j < i)%N) (sort_v x 0 j - sort_v y 0 i) + 
    \sum_(j < m | ~~(j < i)%N) (sort_v y 0 i - sort_v x 0 j).
    rewrite (P0 sx) Psx [leRHS](bigID (fun j : 'I_m => (j < i)%N))/= lerD//; 
    apply ler_sum=>j _; first by apply/ler_norm.
    by rewrite -normrN opprB; apply/ler_norm.
  by move=>P2 P3; move: (le_trans P2 P3); rewrite !P1 Ps -!addrA lerD2r ler_pM2l.
Qed.

Lemma majorizeZ m (x y : 'rV[R]_m) c :
  majorize x y -> majorize (c *: x) (c *: y).
Proof.
have [->|/eqP Pc0] := @eqP _ c 0.
  by rewrite !scale0r.
move=>/majorize_normP P1; apply/majorize_normP=>t.
under eq_bigr do rewrite mxE.
move: (P1 (t / c)); rewrite -(ler_pM2l (x := `|c|)) ?normr_gt0//.
rewrite !mulr_sumr.
under eq_bigr do rewrite -normrM mulrBr [_ * (_ / _)]mulrC (mulfVK Pc0).
move=>/le_trans; apply; apply/ler_sum=>i _.
by rewrite -normrM mulrBr mxE [_ * (_ / _)]mulrC (mulfVK Pc0).
Qed.

Lemma weak_majorize_row_mx m n (x y : 'rV[R]_m) (u w : 'rV_n) :
  weak_majorize x y -> weak_majorize u w -> weak_majorize (row_mx x u) (row_mx y w).
Proof.
move=>/weak_majorize_maxP Px /weak_majorize_maxP Pu.
apply/weak_majorize_maxP=>t; rewrite !big_split_ord/= lerD//.
  under eq_bigr do rewrite row_mxEl.
  by under [leRHS]eq_bigr do rewrite row_mxEl.
under eq_bigr do rewrite row_mxEr.
by under [leRHS]eq_bigr do rewrite row_mxEr.
Qed.

Lemma weak_majorize_row_mxP m n (x y : 'rV[R]_m) :
  weak_majorize x y <-> (forall u : 'rV_n, weak_majorize (row_mx x u) (row_mx y u)).
Proof.
split=>P; first by move=>u; apply/weak_majorize_row_mx.
apply/weak_majorize_maxP=>t; move: (P 0).
move=>/weak_majorize_maxP/(_ t); rewrite !big_split_ord/=.
under [X in X + _]eq_bigr do rewrite row_mxEl.
under [X in _ + X]eq_bigr do rewrite row_mxEr mxE.
under [X in _ <= X + _]eq_bigr do rewrite row_mxEl.
under [X in _ <= _ + X]eq_bigr do rewrite row_mxEr mxE.
by rewrite lerD2r.
Qed.

Lemma majorize_row_mx m n (x y : 'rV[R]_m) (u w : 'rV_n) :
  majorize x y -> majorize u w -> majorize (row_mx x u) (row_mx y w).
Proof.
move=>/majorize_normP Px /majorize_normP Pu.
apply/majorize_normP=>t; rewrite !big_split_ord/= lerD//.
  under eq_bigr do rewrite row_mxEl.
  by under [leRHS]eq_bigr do rewrite row_mxEl.
under eq_bigr do rewrite row_mxEr.
by under [leRHS]eq_bigr do rewrite row_mxEr.
Qed.

Lemma majorize_row_mxP m n (x y : 'rV[R]_m) :
  majorize x y <-> (forall u : 'rV_n, majorize (row_mx x u) (row_mx y u)).
Proof.
split=>P; first by move=>u; apply/majorize_row_mx.
apply/majorize_normP=>t; move: (P 0).
move=>/majorize_normP/(_ t); rewrite !big_split_ord/=.
under [X in X + _]eq_bigr do rewrite row_mxEl.
under [X in _ + X]eq_bigr do rewrite row_mxEr mxE.
under [X in _ <= X + _]eq_bigr do rewrite row_mxEl.
under [X in _ <= _ + X]eq_bigr do rewrite row_mxEr mxE.
by rewrite lerD2r.
Qed.

Lemma sort_v_rv_nonincreasing m (v : 'rV[R]_m) : sort_v v \is rv_nonincreasing.
Proof. by apply/rv_nonincreasingP/sort_v_nonincreasing. Qed.

Lemma sort_vK m (v : 'rV[R]_m) : sort_v (sort_v v) = sort_v v.
Proof. by apply/rv_nonincreasing_sorted/sort_v_rv_nonincreasing. Qed.

Lemma sort_v_permK m (v : 'rV[R]_m) s :
  sort_v (col_perm s v) = sort_v v.
Proof.
move: (perm_sort_v (col_perm s v)) (sort_v_rv_nonincreasing (col_perm s v))=>[s1 <-].
move: (perm_sort_v v)=>[s2]/(f_equal (col_perm (s2^-1)%g)).
rewrite -col_permM mulVg col_perm1=>{1 2}->.
by rewrite -!col_permM; apply/rv_nonincreasing_perm/sort_v_rv_nonincreasing.
Qed.

Lemma majorize_perml m (x y : 'rV[R]_m) s :
  majorize (col_perm s x) y <-> majorize x y.
Proof. by rewrite /majorize sort_v_permK. Qed.

Lemma majorize_permr m (x y : 'rV[R]_m) s :
  majorize x (col_perm s y) <-> majorize x y.
Proof. by rewrite /majorize sort_v_permK. Qed.

Lemma majorize_sortl m (x y : 'rV[R]_m) :
  majorize (sort_v x) y <-> majorize x y.
Proof. by move: (perm_sort_v x)=>[s <-]; rewrite majorize_perml. Qed.

Lemma majorize_sortr m (x y : 'rV[R]_m) :
  majorize x (sort_v y) <-> majorize x y.
Proof. by move: (perm_sort_v y)=>[s <-]; rewrite majorize_permr. Qed.

Lemma sort_v_delta_mx m (i : 'I_m.+1) :
  sort_v (delta_mx 0 i : 'rV[R]__) = delta_mx 0 0.
Proof.
rewrite -(sort_v_permK _ (tperm 0 i)).
have -> : col_perm (tperm 0 i) (delta_mx 0 i : 'rV[R]__) = delta_mx 0 0.
  apply/matrixP=>j k; rewrite !mxE; do 3 ! f_equal.
  rewrite permE/=; case E1: (k == 0); first by rewrite eqxx.
  have [ <-|/eqP/negPf//] := @eqP _ k i; by rewrite eq_sym.
apply/rv_nonincreasing_sorted/rv_nonincreasingP=>j k.
case: (unliftP 0 k)=>/=[l-> _|->].
  by rewrite !mxE eqxx/=; case: eqP.
by rewrite leqn0 !mxE !eqxx/= -(inj_eq val_inj)/= =>->.
Qed.

Lemma majorize_delta_nneg m (x : 'rV[R]_m) i :
  majorize x (delta_mx 0 i) -> x \is a nnegmx.
Proof.
case: m x i=>[?[]//|/= m x i].
move=>[]; rewrite sort_v_delta_mx=>P1 P2.
suff: sort_v x \is a nnegmx.
  move: (perm_sort_v x)=>[s <-].
  move=>/nnegmxP P; apply/nnegmxP=>j k.
  by move: (P j ((s^-1)%g k)); rewrite mxE permKV.
have [] := leP 0 (sort_v x 0 ord_max).
  move=>P3; apply/nnegmxP=>j k; rewrite ord1 nnegrE; 
  apply/(le_trans P3)/rv_nonincreasingP.
    apply/sort_v_rv_nonincreasing.
  by rewrite /= -ltnS.
have P (f : _ -> R) :
  \sum_(j < m.+1) f j = \sum_(j < m.+1 | (j < @ord_max m)%N) f j + f ord_max.
  rewrite (bigID (fun j : 'I_m.+1 => (j < @ord_max m)%N))/=; f_equal.
  rewrite (bigD1 ord_max)//= ?ltnn// big1 ?addr0// =>j.
  by rewrite -leqNgt -(inj_eq val_inj)/= eq_sym andbC -ltn_neqAle ltnNge -ltnS ltn_ord.
move: P2 (P1 ord_max)=>/eqP; rewrite !P eq_sym -subr_eq -addrA addrC 
  eq_sym -subr_eq -subr_le0=>/eqP->.
rewrite subr_le0=>P2 P3; move: (le_lt_trans P2 P3); rewrite mxE eqxx/=;
by case: eqP=>_; rewrite ?ltxx// ltNge ler01.
Qed.

Lemma sort_v_const_mx m (c : R) :
  sort_v (const_mx c : 'rV_m) = const_mx c.
Proof. by apply/rv_nonincreasing_sorted/rv_nonincreasingP=>i j _; rewrite !mxE. Qed.

Lemma majorize_const_mx m (x : 'rV[R]_m) c :
  majorize x (const_mx c) -> x = const_mx c.
Proof.
case: m x=>[x | m x]; first by rewrite !mx_dim0E.
have [Pc | Pc] := leP (sort_v x 0 0) c; last first.
  rewrite majorize_leP=>[[/(_ 0)] + _].
  rewrite (bigD1 0)//= big1 1?(bigD1 0)//= ?big1=>[i|i|].
  1,2: by move=>/andP[]; rewrite leqn0 -(inj_eq val_inj)=>/eqP/=->.
  by rewrite !addr0 sort_v_const_mx [leRHS]mxE=>/le_lt_trans/(_ Pc); rewrite ltxx.
have [Pd _ | Pd] := leP c (sort_v x 0 ord_max).
  apply/matrixP=>i j; rewrite ord1 mxE.
  move: (perm_sort_v x)=>[s]/(f_equal (col_perm s^-1)).
  rewrite -col_permM mulVg col_perm1=>->; rewrite mxE.
  apply/le_anti/andP; split.
    by apply/(le_trans _ Pc)/rv_nonincreasingP=>//; apply/sort_v_rv_nonincreasing.
  apply/(le_trans Pd)/rv_nonincreasingP; first by apply/sort_v_rv_nonincreasing.
  by rewrite -ltnS.
move=>[] _; rewrite sort_v_const_mx (bigD1 ord_max)//=.
rewrite [RHS](bigD1 ord_max)//==>/eqP.
rewrite -subr_eq -addrA raddf_sum -big_split/= eq_sym addrC -subr_eq mxE=>/eqP.
set t := \sum_(_ | _) _ => Pt.
have : t <= 0.
  apply sumr_le0=>i _; rewrite subr_le0 [leRHS]mxE; 
  apply/(le_trans _ Pc)/rv_nonincreasingP=>//; apply/sort_v_rv_nonincreasing.
by rewrite -Pt subr_le0=>/(lt_le_trans Pd); rewrite ltxx.
Qed.

Theorem doubly_stochasticPv m (A : 'M[R]_m) : 
  reflect (forall x, majorize (x *m A) x) (A \is doubly_stochastic).
Proof.
apply/(iffP (doubly_stochasticP _))=>[|Px]; last first.
  have P1 : (forall i : 'I_m, \sum_j A i j = 1).
    move=>i; move: (Px (delta_mx 0 i))=>[] _.
    rewrite !sort_v_sum.
    under eq_bigr do rewrite -rowE mxE.
    move=>->; rewrite (bigD1 i)//= big1=>[j/negPf nj|]; 
    by rewrite mxE ?eqxx ?addr0// nj.
  do ! split=>//.
  - move=>i j; move: (Px (delta_mx 0 i)).
    by rewrite -rowE=>/majorize_delta_nneg/nnegmxP/(_ 0 j); rewrite mxE nnegrE.
  - move=>i; move: (Px (const_mx 1))=>/majorize_const_mx/matrixP/(_ 0 i).
    by rewrite !mxE; under eq_bigr do rewrite mxE mul1r.
move=>/doubly_stochasticP PA x.
move: (perm_sort_v x)=>[sx]/(f_equal (col_perm (sx^-1))).
rewrite -col_permM mulVg col_perm1=>->.
rewrite -mul_row_perm majorize_permr.
move: (perm_sort_v (sort_v x *m row_perm sx A))=>[sy].
set y := sort_v (sort_v _ *m _); set z := sort_v x.
have Py : y \is rv_nonincreasing by apply/sort_v_rv_nonincreasing.
have Pz : z \is rv_nonincreasing by apply/sort_v_rv_nonincreasing.
rewrite -(majorize_perml _ _ sy).
rewrite col_permE -mulmxA -col_permE.
set B := col_perm _ _.
have PB : B \is doubly_stochastic
  by rewrite doubly_stochastic_col_perm doubly_stochastic_row_perm.
move=>Ey; rewrite Ey; move: y z Py Pz B PB Ey; 
clear=>y x Py Px A /doubly_stochasticP[P1][P2]P3 Ey.
move: {+}Px {+}Py => /rv_nonincreasing_sorted Px1 /rv_nonincreasing_sorted Py1.
split; rewrite Px1 Py1; last first.
  rewrite -Ey; under eq_bigr do rewrite mxE.
  by rewrite exchange_big/=; under eq_bigr do rewrite -mulr_sumr P2 mulr1.
move=>k; rewrite -Ey; under eq_bigr do rewrite mxE.
pose t (i : 'I_m) := (\sum_(i1 < m | (i1 < k)%N) A i i1).
rewrite exchange_big/=; under eq_bigr do rewrite -mulr_sumr -/(t _).
have Pt1: \sum_(i < m | (i < k)%N) x 0 k - \sum_(i < m) x 0 k * t i = 0.
  rewrite -(big_ord_widen _ (fun=>x 0 k)) 1?ltnW// sumr_const -mulr_natr.
  rewrite -mulr_sumr -mulrBr /t exchange_big/=.
  under eq_bigr do rewrite P3 .
  by rewrite -(big_ord_widen _ (fun=>1)) 1?ltnW// sumr_const subrr mulr0.
rewrite -[leLHS]addr0 -{2}Pt1 addrCA -lerBrDl !raddf_sum/= -!big_split/=.
rewrite (bigID (fun j : 'I_m => (j < k)%N))/= -lerBrDl raddf_sum/= -big_split/=.
apply/(le_trans (y := 0)).
  by apply sumr_le0=>i Pi; rewrite -subr_ge0 opprB add0r -mulrBl mulr_ge0// 
    ?subr_ge0 ?sumr_ge0//; apply/rv_nonincreasingP=>//; rewrite leqNgt.
  apply sumr_ge0=>i Pi. rewrite subr_ge0 -mulrBl ler_piMr// ?subr_ge0.
    by apply/rv_nonincreasingP=>//; apply/ltnW.
by rewrite /t -(P2 i) [leRHS](bigID (fun j : 'I_m => (j < k)%N))/= lerDl sumr_ge0.
Qed.

Definition is_T_transform m (A : 'M[R]_m) :=
  exists c i j, 0 <= c <= 1 /\ A = c%:M + (1-c) *: tperm_mx i j.

Lemma majorize_conv m (x y z : 'rV[R]_m) c : 0 <= c <= 1 ->
  majorize x z -> majorize y z -> majorize (c *: x + (1-c) *: y) z.
Proof.
move=>/andP[]cge0 cle1 /majorize_normP Px /majorize_normP Py.
have Pc1 : c + (1-c) = 1 by rewrite addrC subrK.
apply/majorize_normP=>t; apply/(le_trans 
  (y := (c * \sum_i normr (x 0 i - t)) + (1-c) * \sum_i normr (y 0 i - t))).
rewrite !mulr_sumr -big_split/=; apply ler_sum=>i _.
rewrite -{1}[t]mul1r -{2}Pc1 !mxE [_ * t]mulrDl opprD addrACA.
rewrite -!mulrBr; apply/(le_trans (ler_normD _ _))/lerD; 
by rewrite normrM ger0_norm// subr_ge0.
by rewrite -[leRHS]mul1r -{2}Pc1 [leRHS]mulrDl lerD// ler_wpM2l// subr_ge0.
Qed.

Lemma majorizeDl m (x y z : 'rV[R]_m) :
  majorize x z -> majorize y z -> majorize (x + y) (2 *: z).
Proof.
move=>P1 P2; move: (@majorize_conv _ x y z 2^-1)=>/(_ _ P1 P2).
have P : 0 <= (2^-1 : R) <= 1.
  by rewrite invr_ge0 invf_le1//= ler0n ler1n.
move=>/(_ P)/(majorizeZ 2); 
by rewrite scalerDr !scalerA mulrBr mulfV// {1}mulr2n mulr1 addrK !scale1r.
Qed.

Lemma sort_v_sum_constDl m (z : 'rV[R]_m) c P : 
  \sum_(j < m | P j) sort_v (const_mx c + z) 0 j 
    = \sum_(j < m | P j) c + \sum_(j < m | P j) sort_v z 0 j.
Proof.
move: (perm_sort_v z)=>[s Pz].
suff Pcz : col_perm s (const_mx c + z) = sort_v (const_mx c + z).
  under eq_bigr do rewrite -Pcz linearD/= Pz 3!mxE.
  by rewrite big_split.
symmetry; apply sort_v_eq; first by exists s.
apply/rv_nonincreasingP=>i j Pij; 
rewrite linearD/= Pz 3!mxE 3![in leRHS]mxE lerD2l.
by apply/sort_v_nonincreasing.
Qed.

Lemma majorizeD2l m (x y : 'rV[R]_m) c :
  majorize (const_mx c + x) (const_mx c + y) <->  majorize x y.
Proof.
split=>[[]|[]]P1 P2; (split=>[i|]; [move: (P1 i)|move: P2]); 
rewrite !sort_v_sum_constDl ?lerD2l//.
by move=>/addrI. by move=>->.
Qed. 

Lemma majorizeD2r m (x y : 'rV[R]_m) c :
  majorize (x + const_mx c) (y + const_mx c) <->  majorize x y.
Proof. by rewrite ![_ + const_mx _]addrC majorizeD2l. Qed.

Lemma weak_majorizeD2l m (x y : 'rV[R]_m) c :
  weak_majorize (const_mx c + x) (const_mx c + y) <->  weak_majorize x y.
Proof. by split=>P1 i; move: (P1 i); rewrite !sort_v_sum_constDl lerD2l. Qed.

Lemma weak_majorizeD2r m (x y : 'rV[R]_m) c :
  weak_majorize (x + const_mx c) (y + const_mx c) <->  weak_majorize x y.
Proof. by rewrite ![_ + const_mx _]addrC weak_majorizeD2l. Qed.

Lemma T_transform_majorize m (A : 'M[R]_m) x :
  is_T_transform A -> majorize (x *m A) x.
Proof.
move=>[c][i ][j][Pc]->.
rewrite mulmxDr -scalemx1 -!scalemxAr mulmx1; apply/majorize_conv=>//.
have -> : x *m tperm_mx i j = col_perm (tperm i j) x.
  by rewrite col_permE /tperm_mx tpermV.
by apply/majorize_perml.
Qed.

(* for simplicity, we encoding both T transform and permutation *)
Definition T_P_trans m (x y : 'rV[R]_m) :=
  exists (A : 'M[R]_m), (is_T_transform A \/ is_perm_mx A) /\ (x = y *m A).

Fixpoint T_P_trans_seq m (s : seq 'rV[R]_m) :=
  match s with
  | nil => True
  | h :: s => T_P_trans_seq s /\ match s with 
                         | h' :: _ => T_P_trans h h'
                         | _ => True
                         end
  end.

Lemma T_P_trans_perml m (x : 'rV[R]_m) s :
  T_P_trans (x *m perm_mx s) x.
Proof. by exists (perm_mx s); split=>//; right; apply perm_mx_is_perm. Qed.

Lemma T_P_trans_permr m (x : 'rV[R]_m) s :
  T_P_trans x (x *m perm_mx s).
Proof. 
exists (perm_mx s^-1); split.
  right; apply perm_mx_is_perm.
by rewrite -mulmxA -perm_mxM mulgV perm_mx1 mulmx1.
Qed.

Lemma T_P_trans_sortl m (x : 'rV[R]_m) :
  T_P_trans (sort_v x) x.
Proof. by move: (perm_sort_v x)=>[s] <-; rewrite col_permE; apply/T_P_trans_perml. Qed.

Lemma T_P_trans_sortr m (x : 'rV[R]_m) :
  T_P_trans x (sort_v x).
Proof. by move: (perm_sort_v x)=>[s] <-; rewrite col_permE; apply/T_P_trans_permr. Qed.

Lemma T_P_trans_seq_cons m (x : 'rV[R]_m) s : 
  (T_P_trans_seq s /\ match s with | nil => True | h :: _ => T_P_trans x h end) <->
    T_P_trans_seq (x :: s).
Proof. by elim: s. Qed.
 
Lemma T_P_trans_seq_rcons m (x y : 'rV[R]_m) s : 
  (T_P_trans_seq (rcons s x) /\ T_P_trans x y) <->
    T_P_trans_seq (rcons (rcons s x) y).
Proof.
elim: s x y=>// x s IH y z.
rewrite !rcons_cons -!T_P_trans_seq_cons -IH; case: s IH.
  by move=> _ /=; split=>[[[[]]]|[[[]]]]????; do ! split.
by move=>w s IH; rewrite !rcons_cons; split=>[[[]]|[[]]]???; do ! split=>//.
Qed.

Lemma T_P_trans_seq_cat m (x : 'rV[R]_m) s1 s2 :
  (T_P_trans_seq (rcons s1 x) /\ T_P_trans_seq (x :: s2)) <->
  T_P_trans_seq (s1 ++ (x :: s2)).
Proof.
elim/last_ind: s1 x s2 => [x s2 //= | s x IH y s2].
  by split=>// [[]].
rewrite cat_rcons -IH -T_P_trans_seq_rcons/=.
by split=>[[[??][]]|[?][??]]; do ! split=>//.
Qed.

Lemma majorize_col' m (x y : 'rV[R]_m) i :
  x 0 i = y 0 i ->
  majorize (col' i x) (col' i y) <-> majorize x y.
Proof.
move=>Pxy; split=>/majorize_normP IH; apply/majorize_normP=>t; move: (IH t);
rewrite !(bigD1_ord i)//= Pxy lerD2l;
by do ! under [\sum_(_ < _) normr (col' _ _ _ _ - t)]eq_bigr do rewrite mxE.
Qed.

Lemma majorize_col'' m (x y : 'rV[R]_m.-1) i t :
  majorize (col'' i x t) (col'' i y t) <-> majorize x y.
Proof. by rewrite -(majorize_col' (i := i)) ?col'_col''// !mxE unlift_none. Qed.

Lemma sort_v_sum_lt m (x : 'rV[R]_m) i : 
  \sum_(j < m | (j < i)%N) x 0 j <= \sum_(j < m | (j < i)%N) sort_v x 0 j.
Proof.
elim: m x i=>[x i|m IH x i]; first by rewrite !big_ord0.
move: (perm_sort_v x)=>[s Ps].
apply/(le_trans (y := \sum_(j < m.+1 | (j < i)%N) xcol 0 (s 0) x 0 j)).
  have P4: \sum_(j < m.+1) x 0 j = \sum_(j < m.+1) xcol 0 (s 0) x 0 j.
    rewrite (reindex_perm (tperm 0 (s 0)))/=.
    by apply eq_bigr=>j _; rewrite mxE.
  have Pj j : x 0 j <= x 0 (s 0).
    move: Ps=>/(f_equal (col_perm s^-1)); rewrite -col_permM mulVg col_perm1=>->.
    by rewrite mxE [leRHS]mxE permK; apply/sort_v_nonincreasing.
  have [Pi|Pi] := leqP i (s 0).
    apply ler_sum=>j/leq_trans/(_ Pi).
    by rewrite mxE permE/=; case: eqP=>//; case: eqP=>//->; rewrite ltnn.
  move: P4.
  rewrite (bigID (fun j : 'I_m.+1 => (j < i)%N))/=.
  rewrite [RHS](bigID (fun j : 'I_m.+1 => (j < i)%N))/==>/eqP.
  rewrite -subr_eq -addrA raddf_sum -big_split/= 
    [X in _ + X]big1 ?addr0=>[j|/eqP->//].
  rewrite -leqNgt=>/(leq_trans Pi) Pj0.
  by rewrite mxE permE/= gt_eqF ?gt_eqF// ?subrr//; apply/(leq_trans _ Pj0).
have P1: sort_v (col' 0 (xcol 0 (s 0) x)) = col' 0 (sort_v x).
  pose f (i : 'I_m) := match (nlift 0 i) =P (s^-1)%g 0 with
                       | ReflectT _ => match unlift 0 (s 0) with
                                       | Some i => i
                                       | _ => i
                                       end
                       | ReflectF _ => match unlift 0 (s (nlift 0 i)) with
                                       | Some i => i
                                       | _ => i
                                       end
                        end.
  have P0 j : j != (s^-1)%g 0 -> {k | s j = nlift 0 k & unlift 0 (s j) = Some k}.
    by move=>P1; apply unlift_some; rewrite -(inj_eq (@perm_inj _ s^-1)) permK eq_sym.
  have injf : injective f.
    move=>a b; rewrite /f; case: eqP=>[Pa|]; case: eqP=>[Pb|].
    - by move: Pa Pb=><-/lift_inj->.
    - move=>/eqP/P0[/= k1 Pk1 ->].
      have /P0[/= k0 Pk0 ->]: 0 != (s^-1)%g 0 by rewrite -Pa.
      by move=>/eqP; rewrite -(inj_eq (@lift_inj _ 0)) -Pk0 -Pk1 (inj_eq perm_inj).
    - have /P0[/= k0 Pk0 ->]: 0 != (s^-1)%g 0 by rewrite -Pb.
      move=>/eqP/P0[/= k1 Pk1 ->].
      by move=>/eqP; rewrite -(inj_eq (@lift_inj _ 0)) -Pk0 -Pk1 (inj_eq perm_inj).
    - move=>/eqP/P0[/= k0 Pk0 ->]/eqP/P0[/= k1 Pk1 ->].
      by move=>/eqP; rewrite -(inj_eq (@lift_inj _ 0)) 
        -Pk0 -Pk1 (inj_eq perm_inj) (inj_eq lift_inj)=>/eqP.
  apply/sort_v_eq.
    exists (perm injf); apply/matrixP=>? /= a.
    rewrite ord1 -Ps !mxE !permE/= /f.
    case: eqP=>[Pa|].
      have /P0[/= k0 Pk0 ->]: 0 != (s^-1)%g 0 by rewrite -Pa.
      by rewrite -Pk0 eqxx Pa permKV.
    by move=>/eqP/P0[/= k0 Pk0 ->]; rewrite Pk0 -Pk0 (inj_eq perm_inj).
  apply/rv_nonincreasingP=>/= j k Pjk; rewrite mxE [leRHS]mxE.
  by apply/sort_v_nonincreasing.
case: i IH=>[_ |i IH]; first by rewrite !big1//=.
have -> : \sum_(j < m.+1 | (j < i.+1)%N) xcol 0 (s 0) x 0 j = 
  x 0 (s 0) + \sum_(j < m | (j < i)%N) col' 0 (xcol 0 (s 0) x) 0 j.
  rewrite big_mkcond/= big_ord_recl/= mxE permE/=; f_equal.
  under eq_bigr do rewrite bump0 ltnS; rewrite -big_mkcond/=.
  by apply eq_bigr=>j Pj; rewrite !mxE.
have -> : \sum_(j < m.+1 | (j < i.+1)%N) sort_v x 0 j = 
  x 0 (s 0) + \sum_(j < m | (j < i)%N) sort_v (col' 0 (xcol 0 (s 0) x)) 0 j.
  rewrite big_mkcond/= big_ord_recl/=; f_equal; first by rewrite -Ps mxE.
  under eq_bigr do rewrite bump0 ltnS; rewrite -big_mkcond/=.
  by apply eq_bigr=>j Pj; rewrite P1 !mxE.
by rewrite lerD2l; apply IH.
Qed.

Lemma col_permEV [C : semiRingType] [m n] (s : {perm 'I_n}) (A : 'M[C]_(m, n)) :
    A *m perm_mx s = col_perm s^-1 A.
Proof. by rewrite col_permE invgK. Qed.

Lemma T_P_trans_col'' m (x y : 'rV[R]_m.-1) i t :
  T_P_trans x y -> T_P_trans (col'' i x t) (col'' i y t).
Proof.
move=>[A][][]+->.
- move=>[/=c][j][k][]Pc->.
  exists (c%:M + (1-c) *: tperm_mx (nlift i j) (nlift i k)); split.
    left; exists c; exists (nlift i j); exists (nlift i k); split=>//.
  rewrite !mulmxDr !mul_mx_scalar -!scalemxAr -!xcolE; apply/matrixP=>a b.
  rewrite !mxE; case: unliftP=>[d->|->]; rewrite permE/=.
  rewrite !(inj_eq lift_inj) !mxE permE/=; 
    do 2 (case: eqP=>[->| _ ]; rewrite ?liftK//).
  by rewrite ![i == _]eq_sym !lift_eqF unlift_none -mulrDl addrC subrK mul1r.
- move=>/is_perm_mxP[s ->].
  pose f := fun j : 'I_m => match unlift i j with 
                            | None => j | Some j => nlift i ((s^-1)%g j) end.
  have injf : injective f.
    move=>a b; rewrite /f; case: unliftP=>[j ->|->]; case: unliftP=>[k->|->//].
      by move=>/lift_inj/perm_inj->.
      by move=>/eqP; rewrite lift_eqF.
    by move=>/esym/eqP; rewrite lift_eqF.
  exists (perm_mx (perm injf)^-1); split.
    by right; apply/perm_mx_is_perm.
  rewrite !col_permEV; apply/matrixP=>a b; rewrite !mxE invgK permE /f.
  case: unliftP=>[j _|->]; by rewrite ?unlift_none // liftK mxE.
Qed.

Lemma T_P_trans_seq_col'' m (s : seq 'rV[R]_m.-1) i t :
  T_P_trans_seq s -> T_P_trans_seq (map (@col'' _ _ _ i ^~ t) s).
Proof.
elim: s=>//a s IH /=[] P1 P2; split; first by apply/IH.
move: P2; clear; case: s=>//b s/=; exact: T_P_trans_col''.
Qed.

Theorem majorize_T_P_trans_seq m (x y : 'rV[R]_m) :
  majorize x y -> exists s, T_P_trans_seq (x :: (rcons s y)).
Proof.
elim: m x y.
  move=>x y _; exists nil=>/=; rewrite !mx_dim0E; do ! split=>//.
  exists (perm_mx 1); rewrite mul0mx; split=>//; right; apply/perm_mx_is_perm.
move=>m IH x y Pxy.
have P1 : majorize (sort_v x) (sort_v y).
  by rewrite majorize_sortl majorize_sortr.
move: (rv_nonincreasing_itv (sort_v x 0 0) (sort_v_rv_nonincreasing y))=>[].
case=>[IH1 | n IH1].
  have Pxy0 : sort_v x 0 0 = sort_v y 0 0.
    apply/le_anti/andP; split.
      move: Pxy=>/majorize_ltP[]/(_ 1)+ _.
      rewrite (bigD1 0)//= big1 1?(bigD1 0)//= ?big1 ?addr0//.
        1,2: by move=>i /andP[]; rewrite ltnS leqn0 -(inj_eq val_inj)/==>/eqP->.
    by move: (IH1 0)=>[] _; rewrite leqnn=>/(_ isT).
  move: {+}P1; rewrite -(majorize_col' Pxy0)=>/IH[s Ps].
  exists (sort_v x :: (rcons 
    (map (@col'' _ _ _ 0 ^~ (col 0 (sort_v x))) s) (sort_v y))).
  rewrite -!rcons_cons -T_P_trans_seq_rcons; split;
    last by exact: T_P_trans_sortl.
  rewrite !rcons_cons -T_P_trans_seq_cons; split;
    last by exact: T_P_trans_sortr.
  move: Ps=>/(T_P_trans_seq_col'' 0 (col 0 (sort_v x))).
  rewrite map_cons col''K map_rcons.
  suff -> : col 0 (sort_v x) = col 0 (sort_v y) by rewrite col''K.
  by apply/matrixP=>i j; rewrite mxE ord1 Pxy0 !mxE.
have [Pmn|Pmn] := ltnP n m; last first.
  move: Pxy=>[] _ /eqP; rewrite eq_sym -subr_eq0 raddf_sum -big_split/=.
  rewrite psumr_eq0=>[/= j _ | /allP P].
    rewrite subr_ge0; apply/ltW/(le_lt_trans (y := sort_v x 0 0)).
      by apply/sort_v_nonincreasing.
    by move: (IH1 j)=>[] + _; apply; apply/(leq_trans (ltn_ord _)).
  have eqxy : sort_v x = sort_v y.
    apply/matrixP=>i j; rewrite ord1.
    move: (P j); rewrite mem_index_enum=>/(_ isT)/implyP/(_ isT).
    by rewrite subr_eq0=>/eqP->.
  exists [:: sort_v x] =>/=; do ! split.
    rewrite eqxy; exact: T_P_trans_sortl.
  exact: T_P_trans_sortr.
move: {+}Pmn {+}Pmn=>/ltnW; rewrite -ltnS=>Pn; rewrite -ltnS=>Pn1.
pose k := Ordinal Pn.
pose k1 := Ordinal Pn1.
move: (IH1 k)=>/=[]/(_ (leqnn _))P2 _.
move: (IH1 k1)=>/=[] _ /(_ (leqnn _)) P3.
have [t [] /andP[] t0 t1 Pt]: exists t, 0 <= t <= 1 /\ 
  sort_v x 0 0 = t * sort_v y 0 0 + (1-t) * sort_v y 0 k1.
  have [P4|/eqP P4] := @eqP _ (sort_v y 0 0) (sort_v y 0 k1).
    exists 1; rewrite ler01 lexx mul1r subrr mul0r addr0; split=>//.
    apply/le_anti/andP; rewrite {2}P4; split=>//.
    by apply/ltW/(lt_le_trans P2)/sort_v_nonincreasing.
  pose t := (sort_v x 0 0 - sort_v y 0 k1) / (sort_v y 0 0 - sort_v y 0 k1).
  have Pt0 : 0 <= t by rewrite divr_ge0// subr_ge0// sort_v_nonincreasing.
  have Pt1 : t <= 1.
    rewrite ler_pdivrMr.
      by rewrite subr_gt0 lt_def P4 sort_v_nonincreasing.
    by rewrite mul1r lerD2r; apply/ltW/(lt_le_trans P2)/sort_v_nonincreasing.
  exists t; rewrite Pt0 Pt1; split=>//.
  by rewrite mulrBl mul1r addrCA -mulrBr mulfVK ?subr_eq0// addrC subrK.
pose At := t%:M + (1-t) *: tperm_mx 0 k1.
have PAt : is_T_transform At.
  by exists t; exists 0; exists k1; rewrite t0 t1; split.
pose y1 := sort_v y *m At.
have Py10 : sort_v x 0 0 = y1 0 0.
  by rewrite /y1 /At mulmxDr -scalemx1 -!scalemxAr mulmx1 -xcolE Pt !mxE permE.
have Py1_eq (i : 'I_m.+1) : ((i != k1) && (i != 0)) -> y1 0 i = sort_v y 0 i.
  move=>/andP[]/negPf nk1 /negPf n0.
  rewrite /y1 /At mulmxDr mxE mul_mx_scalar mxE -scalemxAr -xcolE 
    -[RHS]mul1r -[in RHS](subrK t 1) mulrDl addrC; f_equal.
  by rewrite mxE mxE permE/= n0 nk1.
have Pyk1 : y1 0 k1 = (1-t) * sort_v y 0 0 + t * sort_v y 0 k1.
  rewrite /y1 /At mulmxDr mxE mul_mx_scalar mxE addrC; f_equal.
  by rewrite -scalemxAr -xcolE mxE mxE permE/= eqxx.
have Pxy1 : majorize (sort_v x) y1.
  have P4: \sum_(j < m.+1) sort_v (sort_v x) 0 j = \sum_(j < m.+1) sort_v y1 0 j.
    symmetry; rewrite sort_vK.
    move: (perm_sort_v y1)=>[s] <-; rewrite (reindex_perm s^-1)/=.
    under eq_bigr do rewrite mxE permKV /y1 /At mulmxDr mul_mx_scalar 
      -scalemxAr mxE mxE  -xcolE 2![in X in _ + X]mxE addrC.
    rewrite big_split/= -!mulr_sumr (reindex_perm (tperm 0 k1))/=.
    under eq_bigr do rewrite -{1}tpermV permK.
    by rewrite -mulrDl subrK mul1r; move: Pxy=>[] _.
  split=>//.
  move=>i; rewrite sort_vK; apply/(le_trans _ (sort_v_sum_lt _ _)).
  have [Pi|Pi] := leqP i k1.
    apply ler_sum=>j/leq_trans/(_ Pi) Pj.
    apply/(le_trans (y := sort_v x 0 0)); first by apply/sort_v_nonincreasing.
    move: Pj; case: (unliftP 0 j)=>/=[j'->Pj|-> _]; last by rewrite Py10.
    apply/ltW/(lt_le_trans P2); rewrite Py1_eq; last by apply/sort_v_nonincreasing.
    by rewrite /= andbT eq_sym gt_eqF.
  suff -> : \sum_(j < m.+1 | (j < i)%N) y1 0 j = \sum_(j < m.+1 | (j < i)%N) sort_v y 0 j.
    by move: Pxy=>[]/(_ i).
  move: (perm_sort_v y1) P4=>[s<-]; rewrite sort_vK [RHS](reindex_perm s^-1).
  move: Pxy=>[] _ ->.
  under [RHS]eq_bigr do rewrite mxE permKV.
  rewrite (bigID (fun j : 'I_m.+1 => (j < i)%N))/=.
  rewrite [RHS](bigID (fun j : 'I_m.+1 => (j < i)%N))/==>/eqP.
  rewrite -subr_eq -addrA raddf_sum -big_split/= 
    [X in _ + X]big1 ?addr0=>[j|/eqP//].
  rewrite -leqNgt=>/(leq_trans Pi) Pj.
  by rewrite Py1_eq ?subrr// gt_eqF//= gt_eqF//; apply/(leq_trans _ Pj).
have: majorize (col' 0 (sort_v x)) (col' 0 y1).
  by rewrite majorize_col'.
move=>/IH [s Ps].
exists (sort_v x :: rcons (rcons 
  (map (@col'' _ _ _ 0 ^~ (col 0 (sort_v x))) s) y1) (sort_v y)).
split.
  rewrite -!rcons_cons -!T_P_trans_seq_rcons rcons_cons; split;
    last by apply T_P_trans_sortl.
  split; last by exists At; split=>//; left.
  move: Ps=>/(T_P_trans_seq_col'' 0 (col 0 (sort_v x))).
  rewrite map_cons col''K map_rcons.
  suff -> : col 0 (sort_v x) = col 0 y1 by rewrite col''K.
  by apply/matrixP=>i j; rewrite mxE ord1 Py10 !mxE.
by rewrite rcons_cons; exact: T_P_trans_sortr.
Qed.

Lemma T_transform_doubly_stochastic m (A : 'M[R]_m) :
  is_T_transform A -> A \is doubly_stochastic.
Proof.
move=>[/= c][i ][j][]/andP[]c0 c1 PA.
have: A \in conv [set A : 'M[R]_m | is_perm_mx A]%classic.
  rewrite inE; exists bool; exists (fun b => if b then c else (1-c));
  exists (fun b => if b then perm_mx 1 else tperm_mx i j); do ! split.
    by case; rewrite ?subr_ge0 ?c0 ?c1//= lerBlDl lerDr.
    by rewrite big_bool/= addrC subrK.
    case; rewrite inE/=; apply/perm_mx_is_perm.
  by rewrite big_bool/= perm_mx1 scalemx1.
by rewrite -Birkhoff_doubly_stochastic inE/=.
Qed.

Theorem majorizeP m (x y : 'rV[R]_m) :
  majorize x y <-> exists2 A, A \is doubly_stochastic & x = y *m A.
Proof.
split; last by move=>[A]/doubly_stochasticPv PA ->.
move=>/majorize_T_P_trans_seq [s].
elim: s x y.
  move=>x y /= [] _ [A] [] [].
    by move=> /T_transform_doubly_stochastic; exists A.
  move=>/is_perm_mxP[s] ->; exists (perm_mx s)=>//.
  by apply/perm_mx_doubly_stochastic.
move=>z s IH x y; rewrite rcons_cons -T_P_trans_seq_cons.
move=>[]/IH [A PA1 PA2][B][PB1]PB2.
exists (A *m B); last by rewrite mulmxA -PA2 PB2.
apply/doubly_stochasticM=>//.
case: PB1=>[/T_transform_doubly_stochastic//|/is_perm_mxP[t->]];
exact: perm_mx_doubly_stochastic.
Qed.

Theorem majorize_conv_col_perm m (x y : 'rV[R]_m) :
  majorize x y <-> x \in conv ((@col_perm _ _ _ ^~ y) @` setT).
Proof.
rewrite majorizeP; split.
  move=>[A]; move: Birkhoff_doubly_stochastic=>/(_ R m)/seteqP=>[[]]/(_ A)/= PA _.
  move=>/PA[T][c][f][Pc][Pc1][Pf]PA1->.
  rewrite inE; exists T; exists c; exists (fun i => y *m f i); do ! split=>//.
  move=>i; move: (Pf i); rewrite !inE/==>/is_perm_mxP[s ->].
  by exists (s^-1)%g=>//; rewrite col_permE invgK.
  by rewrite PA1 mulmx_sumr; under eq_bigr do rewrite -scalemxAr.
rewrite inE=>[[T][c][f][Pc][Pc1][Pf]->].
have Pi i : {s : 'S_m | f i = col_perm s y}.
  by move: (Pf i); rewrite inE/==>/cid2[s _] <-; exists s.
pose A := (\sum_i c i *: perm_mx (projT1 (Pi i))^-1).
have : A \in conv [set A : 'M[R]_m | is_perm_mx A]%classic.
  rewrite inE; exists T; exists c; exists (fun i => perm_mx (projT1 (Pi i))^-1).
  do ! split=>//; move=>i; rewrite inE/=; apply/perm_mx_is_perm.
rewrite -Birkhoff_doubly_stochastic inE/=.
exists A=>//; rewrite mulmx_sumr; apply eq_bigr=>i _.
by move: (projT2 (Pi i))=>{1}->; rewrite -scalemxAr col_permE.
Qed.

Lemma elem_lemx_weak_majorize m (x y : 'rV[R]_m) : 
  elem_lemx x y -> weak_majorize x y.
Proof.
move=>Pxy; rewrite weak_majorize_maxP=>t; apply ler_sum=>i _.
rewrite ge_max !le_max lexx orbT andbT lerD2r.
by move: Pxy=>/elem_lemxP/(_ 0 i)->.
Qed.

Lemma sort_v_lsub m n (x : 'rV[R]_(m+n)) : 
  sort_v (lsubmx (sort_v x)) = lsubmx (sort_v x).
Proof.
apply/rv_nonincreasing_sorted/rv_nonincreasingP=>i j Pij.
by rewrite mxE [leRHS]mxE; apply/sort_v_nonincreasing.
Qed.

Lemma doubly_substochastic0 m : (0 : 'M[R]_m) \is doubly_substochastic.
Proof.
apply/doubly_substochasticP; do ! split.
  by move=>i j; rewrite mxE.
all: by move=>i; rewrite big1// =>?; rewrite mxE.
Qed.

Lemma diag_block_mx_doubly_substochastic m n (A : 'M[R]_m) (B : 'M[R]_n) :
  A \is doubly_substochastic -> B \is doubly_substochastic ->
    block_mx A 0 0 B \is doubly_substochastic.
Proof.
move=>/doubly_substochasticP[PA1][PA2]PA3.
move=>/doubly_substochasticP[PB1][PB2]PB3.
apply/doubly_substochasticP; do ! split.
- move=>i j; case: (split_ordP i)=>?->; case: (split_ordP j)=>?->;
  by rewrite ?block_mxEul ?block_mxEur ?block_mxEdl ?block_mxEdr// mxE.
- move=>i; case: (split_ordP i)=>?->;
  rewrite big_split_ord/=;
  under eq_bigr do rewrite ?block_mxEul ?block_mxEdl ?mxE;
  under [X in _ + X]eq_bigr do rewrite ?block_mxEur ?block_mxEdr ?mxE;
  by rewrite sumr_const mul0rn ?add0r// addr0.
- move=>i; case: (split_ordP i)=>?->;
  rewrite big_split_ord/=;
  under eq_bigr do rewrite ?block_mxEul ?block_mxEur ?mxE;
  under [X in _ + X]eq_bigr do rewrite ?block_mxEdl ?block_mxEdr ?mxE;
  by rewrite sumr_const mul0rn ?add0r// addr0.
Qed.

Lemma weak_majorize_row_majorize m (x y : 'rV[R]_m) : x \is a nnegmx -> y \is a nnegmx ->
  weak_majorize x y ->
  let s := (\sum_i y 0 i - \sum_i x 0 i) / m%:R in
    majorize (row_mx x (const_mx s : 'rV_m)) (row_mx y 0).
Proof.
case: m x y=>[x y _ _ _ | m x y Px Py Pxy0 s].
  by rewrite /= !mx_dim0E.
move: {+}Pxy0 {+}Pxy0 => /weak_majorize_leP Pxy /weak_majorize_ltP Pxy1.
have Ps: 0 <= s.
  rewrite /s mulr_ge0 ?invr_ge0//.
  move: (Pxy m).
  under [leLHS]eq_bigl do rewrite -ltnS ltn_ord.
  under [leRHS]eq_bigl do rewrite -ltnS ltn_ord.
  by rewrite -subr_ge0 !sort_v_sum.
move: (rv_nonincreasing_itv s (sort_v_rv_nonincreasing x))=>[i Pi].
pose f (j : 'I_(m.+1 + m.+1)) : 'I_(m.+1 + m.+1) :=
  match fintype.split j with
  | inl j => if (j < i)%N then lshift _ j else rshift _ j
  | inr j => if (j < i)%N then rshift _ j else lshift _ j
  end.
move: (perm_sort_v x) (perm_sort_v y)=>[sx Psx] [sy Psy].
Ltac lrsimp := try by move=>/eqP; rewrite ?eq_lrshift ?eq_rlshift.
have injf : injective f.
  move=>a b; rewrite /f; case: split_ordP=>c ->; case: split_ordP=>d ->.
  - by case: ltnP=>Pc; case: ltnP=>Pd //; lrsimp =>/rshift_inj->.
  - case: ltnP=>Pc; case: ltnP=>Pd //; lrsimp.
    by move=>/lshift_inj Pcd; move: (leq_trans Pc Pd); rewrite Pcd ltnn.
    by move=>/rshift_inj Pcd; move: (leq_trans Pd Pc); rewrite Pcd ltnn.
  - case: ltnP=>Pc; case: ltnP=>Pd //; lrsimp.
    by move=>/rshift_inj Pcd; move: (leq_trans Pc Pd); rewrite Pcd ltnn.
    by move=>/lshift_inj Pcd; move: (leq_trans Pd Pc); rewrite Pcd ltnn.
  - by case: ltnP=>Pc; case: ltnP=>Pd //; lrsimp =>/lshift_inj->.
have Prx : sort_v (row_mx (sort_v x) (const_mx s)) = 
  col_perm (perm injf) (row_mx (sort_v x) (const_mx s)).
  apply/sort_v_eq; first by exists (perm injf).
  apply/rv_nonincreasingP=>j k; rewrite mxE [leRHS]mxE !permE /f.
  case: split_ordP=>a ->; case: split_ordP=>b -> /=.
  - move=>Pab; case: ltnP.
    - by move=>/(leq_ltn_trans Pab)->; rewrite !row_mxEl; apply/sort_v_nonincreasing.
    - case: ltnP=> Pb Pa; rewrite ?row_mxEl ?row_mxEr mxE; last by rewrite mxE.
      by apply/ltW; move: (Pi b)=>[]/(_ Pb).
  - by move=>/(leq_ltn_trans)/(_ (ltn_ord _)); rewrite -ltn_subRL subnn.
  - move=>_; case: ltnP=>Pa; case: ltnP=>Pb; 
    rewrite ?row_mxEl ?row_mxEr ?[const_mx s _ _]mxE//.
    - by apply/ltW; move: (Pi b)=>[]/(_ Pb).
    - by apply/sort_v_nonincreasing=>//; apply/ltnW/(leq_trans Pb Pa).
    - by move: (Pi a)=>[] _ /(_ Pa).
  - rewrite leq_add2l=>Pab; case: ltnP.
    - by move=>/(leq_ltn_trans Pab)->; rewrite !row_mxEr !mxE.
    - case: ltnP=>Pb Pa; rewrite ?row_mxEl ?row_mxEr.
      by rewrite [leRHS]mxE; move: (Pi a)=>[] _ /(_ Pa).
      by apply/sort_v_nonincreasing.
pose perm_lift_fun (s0 : 'S_m.+1) (j : 'I_(m.+1 + m.+1)) := 
  match fintype.split j with | inl j => lshift _ (s0 j) | inr j => rshift _ j end.
have perm_lift_inj s0 : injective (perm_lift_fun s0).
  move=>a b; rewrite /perm_lift_fun; 
  case: split_ordP=>c ->; case: split_ordP=>d -> // ; lrsimp.
  by move=>/lshift_inj/perm_inj->.
have Pry : sort_v (row_mx y 0) = row_mx (sort_v y) (0 : 'rV_m.+1).
  apply/sort_v_eq.
    exists (perm (perm_lift_inj sy)); apply/matrixP=>? j.
    rewrite ord1 mxE permE /perm_lift_fun; case: split_ordP=>a ->;
    by rewrite ?row_mxEr// !row_mxEl -Psy mxE.
  apply/rv_nonincreasingP=>j k; case: (split_ordP j)=>a ->; 
    case: (split_ordP k)=>b ->/=; rewrite ?row_mxEl ?row_mxEr.
  - by apply/sort_v_nonincreasing.
  - by rewrite mxE -Psy mxE -nnegrE=> _; apply/nnegmxP.
  - by move=>/(leq_ltn_trans)/(_ (ltn_ord _)); rewrite -ltn_subRL subnn.
  - by rewrite !mxE.
rewrite -(majorize_perml _ _ (perm (perm_lift_inj sx))).
have ->: col_perm (perm (perm_lift_inj sx)) (row_mx x (const_mx s))
  = row_mx (sort_v x) (const_mx s).
  apply/matrixP=>? j; rewrite ord1 mxE permE /perm_lift_fun; 
  by case: split_ordP=>a ->; rewrite ?row_mxEr// !row_mxEl -Psx mxE.
have Pxs_ge0 j : 0 <= row_mx (sort_v x) (const_mx s : 'rV_m.+1) 0 j.
  case: (split_ordP j)=>? ->; rewrite ?row_mxEr ?row_mxEl.
  by rewrite -Psx mxE -nnegrE; apply/nnegmxP. by rewrite mxE.
have Pys_ge0 j : 0 <= row_mx (sort_v y) (0 : 'rV_m.+1) 0 j.
  case: (split_ordP j)=>? ->; rewrite ?row_mxEr ?row_mxEl.
  by rewrite -Psy mxE -nnegrE; apply/nnegmxP. by rewrite mxE.
have Psum : \sum_(j < m.+1 + m.+1) sort_v (row_mx (sort_v x) (const_mx s)) 0 j = 
  \sum_(j < m.+1 + m.+1) sort_v (row_mx y 0) 0 j.
  rewrite Prx Pry (reindex_perm (perm injf)^-1)/=.
  rewrite !big_split_ord/=.
  under eq_bigr do rewrite mxE permKV row_mxEl.
  under [X in _ + X]eq_bigr do rewrite mxE permKV row_mxEr mxE.
  rewrite sumr_const -mulr_natr card_ord /s mulfVK// addrC sort_v_sum subrK -[LHS]addr0; f_equal.
    by under [RHS]eq_bigr do rewrite row_mxEl; rewrite sort_v_sum. 
  by under eq_bigr do rewrite row_mxEr mxE; rewrite big1.
split=>// j; case: (split_ordP j)=>k ->; last first.
  have -> : \sum_(j0 < m.+1 + m.+1 | (j0 < rshift m.+1 k)%N) sort_v (row_mx y 0) 0 j0
    = \sum_(j < m.+1 + m.+1) sort_v (row_mx y 0) 0 j.
    rewrite !big_split_ord/= [X in _ + X]big1 ?addr0 ?[X in _ + X]big1 ?addr0.
    1,2: by move=>a _; rewrite Pry row_mxEr mxE.
    by apply eq_bigl=>a; apply/(leq_trans (ltn_ord a))/leq_addr.
  rewrite -Psum [leRHS](bigID (fun a : 'I_(m.+1 + m.+1) => (a < rshift m.+1 k)%N))/= 
    lerDl sumr_ge0// =>a _; rewrite Prx mxE//.
have Psum1: \sum_(j < m.+1) sort_v (row_mx (sort_v x) (const_mx s)) 0 (lshift m.+1 j)
  <= \sum_(j < m.+1) sort_v (row_mx y 0) 0 (lshift m.+1 j).
  move: Psum; rewrite !big_split_ord/=.
  under [X in _ = _ + X]eq_bigr do rewrite Pry row_mxEr mxE.
  rewrite sumr_const mul0rn addr0=><-.
  rewrite lerDl sumr_ge0//==>? _; rewrite Prx mxE//.
rewrite !big_split_ord/= [X in _ + X]big1 ?addr0 ?[X in _ + X]big1 ?addr0.
  1,2: by move=>a; move=>/ltn_trans/(_ (ltn_ord k)); rewrite -ltn_subRL subnn.
case: k=>k Pk/=; case: k Pk.
  by move=>_; rewrite !big1.
move=>k Pk.
have [Pki|Pki] := leqP i k; last first.
  rewrite Prx Pry; under [leRHS]eq_bigr do rewrite row_mxEl.
  apply/(le_trans _ (Pxy1 k.+1))/ler_sum=>a Pa.
  rewrite mxE permE /f; case: split_ordP=>[b /lshift_inj<-|?]; lrsimp.
  by move: (leq_trans Pa Pki)=>->; rewrite row_mxEl.
pose ki := Ordinal (ltnW Pk).
have [Pks|Pks] := leP s (sort_v y 0 ki).
  rewrite (bigID (fun j : 'I_m.+1 => (j < i)%N)) 
    [leRHS](bigID (fun j : 'I_m.+1 => (j < i)%N))/= lerD//.
    have Pi0 : (fun i0 : 'I_m.+1 => (i0 < k.+1)%N && (i0 < i)%N) =1 (fun i0 : 'I_m.+1 => (i0 < i)%N).
      move=>a; case E: (a < i)%N; last by rewrite andbF.
      by move: (leq_trans E Pki)=>/ltnW; rewrite ltnS=>->.
    rewrite !(eq_bigl _ _ Pi0); under [leRHS]eq_bigr do rewrite Pry row_mxEl.
    apply/(le_trans _ (Pxy1 i))/ler_sum=>a Pa.
    rewrite Prx mxE permE /f; case: split_ordP=>[b /lshift_inj <-|?]; lrsimp.
    by rewrite Pa row_mxEl.
  apply ler_sum=>a /andP[] P1 /negPf P2.
  rewrite Prx Pry row_mxEl mxE permE /f; case: split_ordP=>[?/lshift_inj<-|?]; lrsimp.
  rewrite P2 row_mxEr mxE; apply/(le_trans Pks)/sort_v_nonincreasing=>//.
move: Psum1; rewrite (bigID (fun i0 : 'I_m.+1 => (i0 < k.+1)%N))
  [leRHS](bigID (fun i0 : 'I_m.+1 => (i0 < k.+1)%N))/=.
rewrite -lerBlDl addrAC -lerBrDr -[in X in _ -> X]subr_le0.
move=>/le_trans; apply; rewrite raddf_sum -big_split/= sumr_le0=>// a Pa.
rewrite Pry Prx row_mxEl [in X in _ - X]mxE permE /f; 
case: split_ordP=>[?/lshift_inj<-|?]; lrsimp.
move: {+}Pa; rewrite -leqNgt=>/ltnW/(leq_trans Pki); rewrite ltnNge=>->.
rewrite /= row_mxEr subr_le0 [leRHS]mxE; apply/ltW/(le_lt_trans _ Pks)/sort_v_nonincreasing=>//.
by apply/ltnW; rewrite /= leqNgt.
Qed.

Theorem weak_majorizeP m (x y : 'rV[R]_m) : x \is a nnegmx -> y \is a nnegmx ->
  weak_majorize x y <-> exists2 A, A \is doubly_substochastic & x = y *m A.
Proof.
split; last first.
  move=>[A] PA; move: {+}PA=>/(doubly_substochastic_elem_leP (doubly_substochastic_nnegmx PA))[B PB PAB] ->.
  have: (elem_lemx (y *m A) (y *m B)).
    apply/elem_lemxP=>i j; rewrite !mxE; apply ler_sum=>/= k _.
    rewrite ler_wpM2l// -?nnegrE; first by apply/nnegmxP.
    by move: PAB=>/elem_lemxP/(_ k j).
  move=>/elem_lemx_weak_majorize/weak_majorize_trans; apply.
  by apply/majorizeW; move: PB=>/doubly_stochasticPv.
move=>Pxy.
move: (weak_majorize_row_majorize H H0 Pxy)=>/=; rewrite majorizeP=>[[A PA1 PA2]].
exists (ulsubmx A).
  by rewrite doubly_substochastic_ulsubP; exists A.
move: PA2=>/(f_equal lsubmx).
by rewrite row_mxKl -{1}[A]submxK mul_row_block !mul0mx !addr0 row_mxKl.
Qed.

Lemma elem_lemxBlDr m (x y z : 'rV[R]_m) :
  elem_lemx (x - y) z <-> elem_lemx x (z + y).
Proof.
split=>/elem_lemxP H; apply/elem_lemxP=>i j;
by move: (H i j); rewrite !mxE lerBlDr.
Qed.

Lemma elem_lemxBlDl m (x y z : 'rV[R]_m) :
  elem_lemx (x - y) z <-> elem_lemx x (y + z).
Proof. by rewrite elem_lemxBlDr addrC. Qed.

Lemma elem_lemxBrDl m (x y z : 'rV[R]_m) :
  elem_lemx x (y - z) <-> elem_lemx (z + x) y.
Proof. by rewrite -elem_lemxBlDr opprK addrC. Qed.

Lemma elem_lemxBrDr m (x y z : 'rV[R]_m) :
  elem_lemx x (y - z) <-> elem_lemx (x + z) y.
Proof. by rewrite elem_lemxBrDl addrC. Qed.

Theorem weak_majorize_midP m (x y : 'rV[R]_m) : 
  weak_majorize x y <-> exists2 u, elem_lemx x u & majorize u y.
Proof.
split; last first.
  move=>[u /elem_lemx_weak_majorize + /majorizeW +].
  apply/weak_majorize_trans.
case: m x y=>[x y _ | m x y].
by exists 0; rewrite mx_dim0E// elem_lemx_refl.
pose s := minr (sort_v x 0 ord_max) (sort_v y 0 ord_max).
move: (perm_sort_v x) (perm_sort_v y)=>[sx Psx] [sy Psy].
have Px i : s <= x 0 i.
  move: Psx=>/(f_equal (col_perm sx^-1))=>/matrixP/(_ 0 i).
  rewrite -col_permM mulVg col_perm1=>->.
  apply/(le_trans (y := sort_v x 0 ord_max)).
  by rewrite /s ge_min lexx.
  by rewrite [leRHS]mxE; apply/sort_v_nonincreasing=>//=; rewrite -ltnS.
have Py i : s <= y 0 i.
  move: Psy=>/(f_equal (col_perm sy^-1))=>/matrixP/(_ 0 i).
  rewrite -col_permM mulVg col_perm1=>->.
  apply/(le_trans (y := sort_v y 0 ord_max)).
  by rewrite /s ge_min lexx orbT.
  by rewrite [leRHS]mxE; apply/sort_v_nonincreasing=>//=; rewrite -ltnS.
have [Ps|Ps] := leP 0 s.
  have Px1 : x \is a nnegmx.
    by apply/nnegmxP=>i j; rewrite ord1 nnegrE; apply/(le_trans Ps).
  have Py1 : y \is a nnegmx.
    by apply/nnegmxP=>i j; rewrite ord1 nnegrE; apply/(le_trans Ps).
  move=>/(weak_majorizeP Px1 Py1)[A PA1 PA2].
  move: {+}PA1; rewrite doubly_substochastic_elem_leP ?(doubly_substochastic_nnegmx PA1)//.
  move=>[B PB1 /elem_lemxP PB2].
  exists (y *m B); last by apply/doubly_stochasticPv.
  rewrite PA2; apply/elem_lemxP=>i j; rewrite !mxE ler_sum//==>k _.
  by rewrite ler_pM// ?doubly_substochastic_ge0// -nnegrE; apply/nnegmxP.
have Px1 : const_mx (-s) + x \is a nnegmx.
  by apply/nnegmxP=>i j; rewrite ord1 nnegrE !mxE addrC subr_ge0.
have Py1 : const_mx (-s) + y \is a nnegmx.
  by apply/nnegmxP=>i j; rewrite ord1 nnegrE !mxE addrC subr_ge0.
rewrite -(weak_majorizeD2l _ _ (-s))=>/(weak_majorizeP Px1 Py1)[A PA1 PA2].
move: {+}PA1; rewrite doubly_substochastic_elem_leP ?(doubly_substochastic_nnegmx PA1)//.
move=>[B PB1 /elem_lemxP PB2].
exists ((const_mx (- s)%R + y)%E *m B - const_mx (-s)).
  rewrite elem_lemxBrDl PA2.
  apply/elem_lemxP=>i j; rewrite !mxE ler_sum//==>k _.
  by rewrite ler_wpM2l// !mxE addrC subr_ge0 ord1.
rewrite mulmxDl addrAC.
have ->: const_mx (- s) *m B - const_mx (- s) = 0 :> 'rV_m.+1.
  apply/matrixP=>i j; rewrite !mxE.
  under eq_bigr do rewrite mxE; rewrite -mulr_sumr.
  by move: PB1=>/doubly_stochasticP[] _ [] _ ->; rewrite mulr1 opprK addNr.
by rewrite add0r; apply/doubly_stochasticPv.
Qed.

Lemma weak_majorize_const_mx m (x : 'rV[R]_m) c :
  weak_majorize x (const_mx c) -> elem_lemx x (const_mx c).
Proof.
case: m x=>[x _|m x].
  by apply/elem_lemxP=>? [].
move=>/weak_majorize_ltP/(_ 1).
rewrite sort_v_const_mx (bigD1 0)//= big1 1?(bigD1 0)//= ?big1.
  1,2: by move=>i; rewrite ltnS leqn0 -(inj_eq val_inj)/==>/andP[]/eqP->.
rewrite !addr0 [leRHS]mxE=>Pc.
apply/elem_lemxP=>i j; move: (perm_sort_v x)=>[s]/(f_equal (col_perm s^-1)).
rewrite -col_permM mulVg col_perm1=>->.
by rewrite mxE ord1 [leRHS]mxE; apply/(le_trans _ Pc)/sort_v_nonincreasing.
Qed.

Theorem doubly_substochasticPv m (A : 'M[R]_m) : 
  reflect (forall (x : 'rV_m), elem_lemx 0 x -> 
    elem_lemx 0 (x *m A) /\ weak_majorize (x *m A) x) 
      (A \is doubly_substochastic).
Proof.
apply/(iffP idP)=>H.
  move: {+}H=>/doubly_substochasticP[PA1][PA2]PA3 x /elem_lemxP Px.
  split.
    apply/elem_lemxP=>i j; rewrite !mxE sumr_ge0//==>k _.
    by rewrite mulr_ge0//; move: (Px i k); rewrite mxE.
  move: {+}H=>/(doubly_substochastic_elem_leP (doubly_substochastic_nnegmx H))[B PB1 /elem_lemxP PB2].
  rewrite weak_majorize_midP; exists (x *m B); last by apply/doubly_stochasticPv.
  apply/elem_lemxP=>i j; rewrite !mxE ler_sum//==>k _.
  by rewrite ler_wpM2l//; move: (Px i k); rewrite mxE.
have Pi (i : 'I_m) : elem_lemx (0 : 'rV[R]_m) (delta_mx 0 i).
  by apply/elem_lemxP=>? j; rewrite !mxE; case: eqP; case: eqP.
apply/doubly_substochasticP; do ! split.
- move=>i j; move: (H _ (Pi i))=>[]/elem_lemxP/(_ 0 j).
  by rewrite mxE delta_mx_mulEr eqxx mul1r.
- move=>i; move: (H _ (Pi i))=>[] _ /weak_majorize_ltP/(_ m).
  have Pj : (fun j : 'I_m => (j < m)%N) =1 (fun => true).
    by move=>j; rewrite ltn_ord.
  rewrite !(eq_bigl _ _ Pj) !sort_v_sum.
  under eq_bigr do rewrite delta_mx_mulEr eqxx mul1r.
  move=>/le_trans; apply; rewrite (bigD1 i)//= big1=>[j/negPf nji|];
  by rewrite mxE !eqxx ?addr0// nji.
- have: elem_lemx 0 (const_mx 1 : 'rV[R]_m).
    by apply/elem_lemxP=>i j; rewrite !mxE.
  move=>/H [] _ /weak_majorize_const_mx /elem_lemxP H1 i.
  by move: (H1 0 i); rewrite !mxE; under eq_bigr do rewrite mxE mul1r.
Qed.

End S2.
#[global] Hint Extern 0 (is_true (_ \is rv_cmp)) => apply: rV_rv_cmp : core.

Lemma in_itv1 [disp : unit] [T : latticeType disp] (i : T) :
  i \in `]-oo, +oo[.
Proof. by move: (itv_lex1 `[i,i])=>/subitvP; apply; rewrite itvxx inE. Qed.
#[global] Hint Extern 0 (is_true (_ \is `]-oo, +oo[)) => apply: in_itv1 : core.

Section Convex_Monotone.
Variable (R : realFieldType).
Local Open Scope convex_scope.

Definition convex_fun (f : R -> R) (itv : interval R) :=
  (forall (t : {i01 R}) (a b : R^o), a \in itv -> b \in itv -> 
    f (a <| t |> b) <= ((f a : R^o) <| t |> (f b))).
Notation conv := analysis.convex.conv.

Lemma normrB_convex c : convex_fun (fun x => `|x - c| : R^o) `]-oo, +oo[.
Proof.
move=>t a b /= _ _; rewrite /conv/=/conv/=.
have Pc : c = `1-(t%:inum) *: (c : R^o) + t%:inum *: (c : R^o).
  by rewrite /onem -scalerDl subrK scale1r.
rewrite {1}Pc opprD addrACA /GRing.scale/= -!mulrBr.
apply/(le_trans (ler_normD _ _))/lerD;
by rewrite normrM ger0_norm//= /onem subr_ge0.
Qed.

Lemma normr_convex : convex_fun (normr : R -> R^o) `]-oo, +oo[.
Proof. by move=>t a b /= Pa Pb; move: (normrB_convex 0 t Pa Pb); rewrite !subr0. Qed.

Lemma maxrB_convexl c d : convex_fun (fun t : R => maxr c (t-d) : R^o) `]-oo, +oo[.
Proof.
move=>t a b /= _ _; rewrite /conv/=/conv/= /maxr.
have Pc : c = `1-(t%:inum) *: (c : R^o) + t%:inum *: (c : R^o).
  by rewrite /onem -scalerDl subrK scale1r.
have Pd : d = `1-(t%:inum) *: (d : R^o) + t%:inum *: (d : R^o).
  by rewrite /onem -scalerDl subrK scale1r.
have Pt : 0 <= `1-(t%:inum) by rewrite /onem subr_ge0.
case Ea: (c < a-d); case Eb: (c < b-d).
- case: ltP=>// _.
    by rewrite !scalerBr addrACA -opprD -Pd.
    by rewrite Pc lerD// ler_wpM2l// ltW.
- case: ltP=> _.
    by rewrite {1}Pd opprD addrACA /GRing.scale/= -!mulrBr lerD2l ler_wpM2l// leNgt Eb.
  by rewrite {1}Pc lerD2r ler_wpM2l // ltW.
- case: ltP=> _.
    by rewrite {1}Pd opprD addrACA /GRing.scale/= -!mulrBr lerD2r ler_wpM2l// leNgt Ea.
  by rewrite {1}Pc lerD2l ler_wpM2l // ltW.
- case: ltP=>// _; last by rewrite -Pc.
  by rewrite {1}Pd opprD addrACA /GRing.scale/= -!mulrBr lerD// ler_wpM2l// leNgt ?Ea ?Eb.
Qed.

Lemma maxrB_convexr c d : convex_fun (fun t : R => maxr (t-d) c: R^o) `]-oo, +oo[.
Proof. by move=>t a b /=; rewrite ![maxr _ c]maxC maxrB_convexl. Qed.

Lemma maxr_convexl c : convex_fun (fun t : R => maxr c t : R^o) `]-oo, +oo[.
Proof.
by move=>t a b /=Pa Pb; move: (maxrB_convexl c 0 t Pa Pb); rewrite !subr0.
Qed.

Lemma maxr_convexr c : convex_fun (fun t : R => maxr t c : R^o) `]-oo, +oo[.
Proof. by move=>t a b /=; rewrite ![maxr _ c]maxC maxr_convexl. Qed.

Lemma convex_le_itv (f : R -> R^o) (i1 i2 : interval R) :
  (i2 <= i1)%O -> convex_fun f i1 -> convex_fun f i2.
Proof. by move=>/subitvP Pi IH t a b /Pi + /Pi; apply IH. Qed.

Lemma subitv_incc (itv : interval R) (a b : R) :
  a \in itv -> b \in itv -> (`[a,b] <= itv)%O.
Proof.
move=>Pa Pb; case: itv Pa Pb=>[[bl l|bl][br r|br]];
by rewrite !inE /Order.le/==>/andP[]??/andP[]??; apply/andP; split.
Qed.

Lemma convex_in_itv (itv : interval R) (a b : R^o) (t : {i01 R}) :
  a \in itv -> b \in itv -> conv t a b \in itv.
Proof.
move=>Pa Pb.
have: (`[minr a b, maxr a b] <= itv)%O.
  by apply/subitv_incc; rewrite /minr /maxr; case: ltP.
move=>/subitvP; apply.
have P1t : 0 <= `1-(t%:inum) by rewrite /onem subr_ge0.
rewrite inE /Order.le/= !bnd_simp /minr /maxr; case: ltP=>Pab.
  rewrite -{1}[a](convmm t) -{3}[b](convmm t).
  by rewrite !convRE lerD2l lerD2r !ler_wpM2l// ltW.
rewrite -{1}[b](convmm t) -{3}[a](convmm t).
by rewrite !convRE lerD2l lerD2r !ler_wpM2l.
Qed.

Notation fun_in_itv f itv := (forall i, f i \in itv).

Lemma convex_in_itv_sum n (x : 'I_n.+1 -> R) (itv : interval R) (f : 'I_n.+1 -> R) :
  (fun_in_itv x itv) -> (forall i, 0 <= f i) -> (\sum_i f i = 1) ->
    \sum_i (f i) * (x i) \in itv.
Proof.
elim: n x f=>[x f|n IH x f].
  by move=>Pxi Pfi; rewrite !big_ord1=>->; rewrite mul1r.
case: (fconsP x)=>x0 xt; case: (fconsP f)=>f0 ft Px Pf.
rewrite big_ord_recl [X in X \in _]big_ord_recl/= !fcons0.
under eq_bigr do rewrite fconsE.
under [in X in _ -> X]eq_bigr do rewrite !fconsE.
move: (Px ord0) (Pf ord0); rewrite !fcons0=>Px0 Pf0.
have [->/eqP|] := @eqP _ f0 1.
  rewrite eq_sym addrC -subr_eq subrr eq_sym.
  rewrite psumr_eq0//==>[i _|]; first by move: (Pf (nlift 0 i)); rewrite fconsE.
  move=>/allP/= Pi; rewrite mul1r big1 ?addr0// =>i _.
  by move: (Pi i); rewrite mem_index_enum=>/(_ isT)/eqP->; rewrite mul0r.
move=>/eqP f0_neq0 /eqP; rewrite eq_sym addrC -subr_eq eq_sym=>/eqP Pi.
have Pxi i : xt i \in itv.
  by move: (Px (nlift 0 i)); rewrite fconsE.
have Pfi1 i : 0 <= ft i.
  by move: (Pf (nlift 0 i)); rewrite fconsE.
have Pfi i : 0 <= ft i / (\sum_i ft i).
  by rewrite mulr_ge0// invr_ge0 sumr_ge0.
have Pf_sum : \sum_i (ft i / (\sum_i ft i)) = 1.
  by rewrite -mulr_suml mulfV// Pi subr_eq add0r eq_sym.
move: (IH _ _ Pxi Pfi Pf_sum).
under eq_bigr do rewrite mulrAC.
rewrite -mulr_suml=>Pft.
have Pitv : Itv.spec `[0,1] f0.
  by rewrite /Itv.itv_cond/= inE /Order.le/= 
    !bnd_simp/= Pf0/= -subr_ge0 -Pi sumr_ge0.
move: (convex_in_itv (Itv.mk Pitv) Pft Px0).
rewrite /conv/=/conv/= /onem -Pi /GRing.scale/= addrC mulrCA mulfV ?mulr1//.
by rewrite Pi subr_eq add0r eq_sym.
Qed.

Lemma convex_convex_le_itv n (x : 'I_n.+1 -> R) (itv : interval R) 
  (f : 'I_n.+1 -> R) (g : R -> R^o) :
  convex_fun g itv -> (fun_in_itv x itv) -> (forall i, 0 <= f i) -> 
    (\sum_i f i = 1) -> g (\sum_i (f i) * (x i)) <= \sum_i (f i) * g (x i).
Proof.
move=>Pg.
elim: n x f=>[x f|n IH x f].
  by move=>Pxi Pfi; rewrite !big_ord1=>->; rewrite !mul1r.
case: (fconsP x)=>x0 xt; case: (fconsP f)=>f0 ft Px Pf.
rewrite big_ord_recl [in leLHS]big_ord_recl/= [in leRHS]big_ord_recl !fcons0.
under eq_bigr do rewrite fconsE.
under [in leLHS]eq_bigr do rewrite !fconsE.
under [in leRHS]eq_bigr do rewrite !fconsE.
move: (Px ord0) (Pf ord0); rewrite !fcons0=>Px0 Pf0.
have [->/eqP|] := @eqP _ f0 1.
  rewrite eq_sym addrC -subr_eq subrr eq_sym.
  rewrite psumr_eq0//==>[i _|]; first by move: (Pf (nlift 0 i)); rewrite fconsE.
  move=>/allP/= Pi; rewrite mul1r !big1 ?addr0 ?mul1r// =>i _;
  by move: (Pi i); rewrite mem_index_enum=>/(_ isT)/eqP->; rewrite mul0r.
move=>/eqP f0_neq0 /eqP; rewrite eq_sym addrC -subr_eq eq_sym=>/eqP Pi.
have Pxi i : xt i \in itv.
  by move: (Px (nlift 0 i)); rewrite fconsE.
have Pfi1 i : 0 <= ft i.
  by move: (Pf (nlift 0 i)); rewrite fconsE.
have Pfi i : 0 <= ft i / (\sum_i ft i).
  by rewrite mulr_ge0// invr_ge0 sumr_ge0.
have Pf_sum : \sum_i (ft i / (\sum_i ft i)) = 1.
  by rewrite -mulr_suml mulfV// Pi subr_eq add0r eq_sym.
move: (IH _ _ Pxi Pfi Pf_sum).
under eq_bigr do rewrite mulrAC.
rewrite -mulr_suml=>Pft.
have Pitv : Itv.spec `[0,1] f0.
  by rewrite /Itv.itv_cond/= inE /Order.le/= 
    !bnd_simp/= Pf0/= -subr_ge0 -Pi sumr_ge0.
move: (Pg (Itv.mk Pitv) _ _ (convex_in_itv_sum Pxi Pfi Pf_sum) Px0).
under eq_bigr do rewrite mulrAC; rewrite -mulr_suml.
rewrite !convRE/= /onem Pi addrC mulrCA mulfV ?subr_eq ?add0r 1?eq_sym// mulr1.
move=>/le_trans; apply.
rewrite addrC lerD2l mulrC -ler_pdivlMr.
  by rewrite lt_def subr_eq add0r eq_sym f0_neq0/= -Pi sumr_ge0.
move: Pft; rewrite Pi; under [leRHS]eq_bigr do rewrite mulrAC.
by rewrite -mulr_suml.
Qed.

Lemma seq_nth_ord_size_true I (r : seq I) (P : pred I) (x0 : I) 
  (i : 'I_(size [seq i <- r | P i])) : P (nth x0 [seq x <- r | P x] i).
Proof.
elim: r i =>[[//=]|x s IH/=];
case E: (P x)=>//= i; case: (unliftP ord0 i)=>[j ->/=|->//]; apply: IH.
Qed.

Lemma convN (T : realDomainType) (t : {i01 T}) (a b : T^o) :
  - (conv t a b) = conv t (-a) (-b).
Proof. by rewrite !convRE /onem/= opprD -!mulrN. Qed.

Lemma convex_average_ord (f : R -> R^o) (itv : interval R) n (x : 'I_n.+1 -> R) :
  (forall (t : {i01 R}) (a b : R^o), a \in itv -> b \in itv ->
    f (conv t a b) <= conv t (f a) (f b)) ->
  (fun_in_itv x itv) -> 
    f ((\sum_i x i) / n.+1%:R) <= (\sum_i f (x i)) / n.+1%:R.
Proof.
move=>Pf Px; elim: n x Px => [x _ | n IH x Px].
by rewrite !divr1 !big_ord1.
rewrite big_ord_recl/= [in X in _ <= X]big_ord_recl/=.
pose tn := n.+1%:R / n.+2%:R : R.
have P1 : Itv.spec `[Posz 0, Posz 1] tn.
  by rewrite /Itv.itv_cond/= inE /Order.le/= /Order.le/= 
    /tn divr_ge0//= ler_pdivrMr// mul1r ler_nat.
pose t := Itv.mk P1.
have P2 : (\sum_(i < n.+1) x (nlift ord0 i)) / n.+1%:R \in itv.
  rewrite mulrC mulr_sumr; apply/convex_in_itv_sum=>//.
  by rewrite sumr_const -[LHS]mulr_natl card_ord mulfV.
move: (Pf t _ _ (Px ord0) P2).
have P3 : (1 - tn) = 1 / n.+2%:R.
  by apply/eqP; rewrite subr_eq /tn -mulrDl nat1r mulfV.
have P4 : (tn / n.+1%:R) = 1 / n.+2%:R.
  by rewrite /tn mulrC mulKf// div1r.
rewrite !convRE/= mulrCA /onem P3 P4 mulrC -mulrDl div1r.
move=>/le_trans; apply.
by rewrite mulrDl mulrC lerD2l /tn mulrC mulrA ler_pM2r// -ler_pdivlMr// IH.
Qed.

Lemma convex_average_seq (f : R -> R^o) (itv : interval R)
  I (s : seq I) (P : pred I) (x : I -> R) :
  (forall (t : {i01 R}) (a b : R^o), a \in itv -> b \in itv ->
    f (conv t a b) <= conv t (f a) (f b)) ->
      {in P, fun_in_itv x itv } -> f 0 = 0 ->
    f ((\sum_(i <- s | P i) x i) / (\sum_(i <- s | P i) 1)) <= 
      (\sum_(i <- s | P i) f (x i)) / (\sum_(i <- s | P i) 1).
Proof.
move=>P1 P2 P3.
case: s=>[|x0 r0]; first by rewrite !big_nil mul0r P3.
set s := x0 :: r0.
rewrite -![\sum_(i <- s | P i) _]big_filter.
rewrite !(big_nth x0) !big_mkord.
case E: (size [seq x <- s | P x]) => [|n].
  by rewrite !big_ord0 mul0r P3.
rewrite sumr_const card_ord; apply: (convex_average_ord P1).
by rewrite -E=>i; apply/P2/seq_nth_ord_size_true.
Qed.

Lemma concave_average_ord (f : R -> R^o) (itv : interval R) n (x : 'I_n.+1 -> R) :
  (forall (t : {i01 R}) (a b : R^o), a \in itv -> b \in itv ->
    conv t (f a) (f b) <= f (conv t a b)) -> fun_in_itv x itv -> 
    (\sum_i f (x i)) / n.+1%:R <= f ((\sum_i x i) / n.+1%:R).
Proof.
move=>P1 P2.
have: forall (t : {i01 R}) (a b : R^o), a \in itv -> b \in itv -> 
  (- f) (conv t a b) <= conv t ((- f) a) ((- f) b).
by move=>t a b Pa Pb; rewrite !fctE -convN lerN2 P1.
move=>/convex_average_ord/(_ P2); rewrite fctE lerNl -mulNr raddf_sum/=.
by under eq_bigr do rewrite opprK.
Qed.

Lemma concave_average_seq (f : R -> R^o) (itv : interval R)
  I (s : seq I) (P : pred I) (x : I -> R) :
  (forall (t : {i01 R}) (a b : R^o), a \in itv -> b \in itv ->
    conv t (f a) (f b) <= f (conv t a b)) ->
    {in P, fun_in_itv x itv } -> f 0 = 0 -> 
      (\sum_(i <- s | P i) f (x i)) / (\sum_(i <- s | P i) 1) <=
      f ((\sum_(i <- s | P i) x i) / (\sum_(i <- s | P i) 1)).
Proof.
move=>P1 P2 P3.
have: forall (t : {i01 R}) (a b : R^o), a \in itv -> b \in itv ->
  (- f) (conv t a b) <= conv t ((- f) a) ((- f) b).
by move=>t a b Pa Pb; rewrite !fctE -convN lerN2 P1.
move=>/(convex_average_seq s (P := P) (x := x))/(_ P2).
rewrite fctE lerNl -mulNr raddf_sum/= P3 oppr0.
under eq_bigr do rewrite opprK. by apply.
Qed.

Theorem majorize_conv_funP m (x y : 'rV[R]_m) (itv : interval R) :
  fun_in_itv (x 0) itv -> fun_in_itv (y 0) itv ->
  majorize x y <-> 
    (forall f : R -> R^o, convex_fun f itv -> \sum_i f (x 0 i) <= \sum_i f (y 0 i)).
Proof.
case: m x y itv => [x y itv _ _ | m x y itv].
  by split=>_ ; rewrite ?mx_dim0E.
split.
  rewrite majorizeP=>[[A PA1 PA2]] f IH.
  rewrite PA2; under eq_bigr do (rewrite mxE; under eq_bigr do rewrite mulrC).
  move: {+}PA1=>/doubly_stochasticP[] PA3 [] PA4 PA5.
  have Pi i : f (\sum_i0 A i0 i * y 0 i0) <= \sum_i0 A i0 i * (f (y 0 i0)).
    by apply/(convex_convex_le_itv IH H0).
  apply/(le_trans (y := \sum_i\sum_j A j i * f (y 0 j))).
    by apply/ler_sum.
  by rewrite exchange_big/= ler_sum// =>i _; rewrite -mulr_suml PA4 mul1r.
move=>IH; apply/majorize_normP=>t.
move: (IH (fun i => `|i - t|)); apply=>t0 a b Pa Pb.
by apply/normrB_convex; move: (itv_lex1 itv)=>/subitvP; apply.
Qed.

Lemma weak_majorize_ub m (x y : 'rV[R]_m) :
  weak_majorize x y -> forall i, exists j, x 0 i <= y 0 j.
Proof.
case: m x y =>[x y _ []//| m x y + i].
move=>/weak_majorize_leP/(_ 0).
rewrite (bigD1 0)//= big1 1?(bigD1 0)//= ?big1 ?addr0.
1,2: by move=>j /andP[]; rewrite leqn0 -(inj_eq val_inj)=>->.
move: (perm_sort_v x) (perm_sort_v y)=>[sx Psx] [sy Psy].
move=>Pxy; exists (sy 0).
move: Psx Psy=>/(f_equal (col_perm sx^-1))+ /(f_equal (col_perm sy^-1)).
rewrite -!col_permM !mulVg !col_perm1=>->->.
by rewrite mxE [leRHS]mxE permK; apply/(le_trans _ Pxy)/sort_v_nonincreasing.
Qed.

Lemma majorize_ub m (x y : 'rV[R]_m) :
  majorize x y -> forall i, exists j, x 0 i <= y 0 j.
Proof. by move=>/majorizeW/weak_majorize_ub. Qed.

Theorem weak_majorize_conv_funP m (x y : 'rV[R]_m) (itv : interval R) :
  fun_in_itv (x 0) itv -> fun_in_itv (y 0) itv ->
  weak_majorize x y <-> 
    (forall f : R -> R^o, convex_fun f itv -> 
      {in itv &, nondecreasing_fun f} -> \sum_i f (x 0 i) <= \sum_i f (y 0 i)).
Proof.
move=>Px Py; split.
rewrite weak_majorize_midP=>[[u Pu1 Pu2] f Pf1 Pf2].
  have Pu i : u 0 i \in itv.
    move: Pu2=>/majorize_ub/(_ i)[j Pj].
    have: (`[x 0 i, y 0 j] <= itv)%O by apply/subitv_incc.
    move=>/subitvP; apply; rewrite inE /Order.le/= !bnd_simp Pj andbT.
    by apply/elem_lemxP.
  apply/(le_trans (y := \sum_i f (u 0 i))).
    by apply/ler_sum=>/= i _; apply/Pf2=>//; apply/elem_lemxP.
  by move: Pu2; rewrite (majorize_conv_funP Pu Py)=>/(_ _ Pf1).
move=>IH; apply/weak_majorize_maxP=>t.
move: (IH (fun i => maxr (i - t) 0)); apply.
move =>t0 a b Pa Pb.
by apply/maxrB_convexr; move: (itv_lex1 itv)=>/subitvP; apply.
by move=>a b _ _ Pab; rewrite ge_max !le_max lexx orbT lerD2r Pab.
Qed.

Definition elem_mx_nondecreasing m n (Phi : 'rV[R]_m -> 'rV[R]_n) 
  (itv : interval R) := forall (x y : 'rV[R]_m), 
    fun_in_itv (x 0) itv -> fun_in_itv (y 0) itv ->
      elem_lemx x y -> elem_lemx (Phi x) (Phi y).

Definition elem_mx_nonincreasing m n (Phi : 'rV[R]_m -> 'rV[R]_n) 
  (itv : interval R) := elem_mx_nondecreasing (fun x => - (Phi x)) itv.

Definition elem_mx_convex m n (Phi : 'rV[R]_m -> 'rV[R]_n) 
  (itv : interval R) := forall (t : {i01 R}) (x y : convex_lmodType 'rV[R]_m), 
    fun_in_itv (x 0) itv -> fun_in_itv (y 0) itv ->
      elem_lemx (Phi (x <| t |> y)) ((Phi x : convex_lmodType _) <| t |> (Phi y)).

Definition elem_mx_concave m n Phi itv := 
  @elem_mx_convex m n (fun x => - Phi x) itv.

Definition isotone m n (Phi : 'rV[R]_m -> 'rV[R]_n) (itv : interval R) :=
  forall (x y : 'rV[R]_m), 
    fun_in_itv (x 0) itv -> fun_in_itv (y 0) itv ->
      majorize x y -> weak_majorize (Phi x) (Phi y).

Definition strongly_isotone m n (Phi : 'rV[R]_m -> 'rV[R]_n) (itv : interval R) :=
  forall (x y : 'rV[R]_m), 
    fun_in_itv (x 0) itv -> fun_in_itv (y 0) itv ->
      weak_majorize x y -> weak_majorize (Phi x) (Phi y).

Definition strictly_isotone m n (Phi : 'rV[R]_m -> 'rV[R]_n) (itv : interval R) :=
  forall (x y : 'rV[R]_m), 
    fun_in_itv (x 0) itv -> fun_in_itv (y 0) itv ->
      majorize x y -> majorize (Phi x) (Phi y).

Lemma convex_fun_in_itv (itv : interval R) m (a b : 'rV[R]_m) (t : {i01 R}) :
  fun_in_itv (a 0) itv -> fun_in_itv (b 0) itv -> 
    fun_in_itv (conv t (a : convex_lmodType _) b 0) itv.
Proof.
move=>Pa Pb i; rewrite /conv/= !mxE.
by move: (convex_in_itv t (Pa i) (Pb i)); rewrite convRE.
Qed.

Lemma convex_fun_in_itv_sum n m (x : 'I_n.+1 -> 'rV[R]_m) 
  (itv : interval R) (f : 'I_n.+1 -> R) :
  (forall i, fun_in_itv (x i 0) itv) -> (forall i, 0 <= f i) -> (\sum_i f i = 1) ->
    fun_in_itv ((\sum_i (f i) *: (x i)) 0) itv.
Proof.
move=>Pxi Pfi Pf i; rewrite summxE; under eq_bigr do rewrite mxE.
apply/convex_in_itv_sum=>//.
Qed.

Lemma convex_convex_fun_le_itv n m r (x : 'I_n.+1 -> 'rV[R]_m) (itv : interval R) 
  (f : 'I_n.+1 -> R) (g : 'rV[R]_m -> 'rV[R]_r) :
  elem_mx_convex g itv -> (forall i, fun_in_itv (x i 0) itv) -> (forall i, 0 <= f i) -> 
    (\sum_i f i = 1) -> elem_lemx (g (\sum_i (f i) *: (x i))) (\sum_i (f i) *: g (x i)).
Proof.
move=>Pg.
elim: n x f=>[x f|n IH x f].
  by move=>Pxi Pfi; rewrite !big_ord1=>->; rewrite !scale1r elem_lemx_refl.
case: (fconsP x)=>x0 xt; case: (fconsP f)=>f0 ft Px Pf.
rewrite big_ord_recl [in g _]big_ord_recl/= [X in elem_lemx _ X]big_ord_recl !fcons0.
under eq_bigr do rewrite fconsE.
under [in g _]eq_bigr do rewrite !fconsE.
under [in X in elem_lemx _ X]eq_bigr do rewrite !fconsE.
move: (Px ord0) (Pf ord0); rewrite !fcons0=>Px0 Pf0.
have [->/eqP|] := @eqP _ f0 1.
  rewrite eq_sym addrC -subr_eq subrr eq_sym.
  rewrite psumr_eq0//==>[i _|]; first by move: (Pf (nlift 0 i)); rewrite fconsE.
  move=>/allP/= Pi; rewrite !scale1r !big1 ?addr0 ?elem_lemx_refl// =>i _;
  by move: (Pi i); rewrite mem_index_enum=>/(_ isT)/eqP->; rewrite scale0r.
move=>/eqP f0_neq0 /eqP; rewrite eq_sym addrC -subr_eq eq_sym=>/eqP Pi.
have Pxi i : fun_in_itv (xt i 0) itv.
  by move: (Px (nlift 0 i)); rewrite fconsE.
have Pfi1 i : 0 <= ft i.
  by move: (Pf (nlift 0 i)); rewrite fconsE.
have Pfi i : 0 <= ft i / (\sum_i ft i).
  by rewrite mulr_ge0// invr_ge0 sumr_ge0.
have Pf_sum : \sum_i (ft i / (\sum_i ft i)) = 1.
  by rewrite -mulr_suml mulfV// Pi subr_eq add0r eq_sym.
move: (IH _ _ Pxi Pfi Pf_sum).
under eq_bigr do rewrite mulrC -scalerA.
rewrite -scaler_sumr Pi=>Pft.
have Pitv : Itv.spec `[0,1] f0.
  by rewrite /Itv.itv_cond/= inE /Order.le/= 
    !bnd_simp/= Pf0/= -subr_ge0 -Pi sumr_ge0.
move: (Pg (Itv.mk Pitv) _ _ (convex_fun_in_itv_sum Pxi Pfi Pf_sum) Px0).
under eq_bigr do rewrite mulrC -scalerA; rewrite -scaler_sumr.
rewrite /conv/= /onem Pi addrC scalerA mulfV ?subr_eq ?add0r 1?eq_sym// scale1r.
move=>/elem_lemx_trans; apply; apply/elem_lemxP=>? i.
rewrite ord1 addrC !mxE lerD2l mulrC -ler_pdivlMr.
  by rewrite lt_def subr_eq add0r eq_sym f0_neq0/= -Pi sumr_ge0.
move: Pft=>/elem_lemxP/(_ 0 i)/le_trans; apply.
rewrite !summxE mulr_suml ler_sum//==>j _.
by rewrite !mxE mulrAC.
Qed.

Lemma convE [C : numFieldType] [V : lmodType C] (S : set V) :
  convex.conv S = [set v : V | exists (n : nat) (c : 'I_n.+1 -> C) (f : 'I_n.+1 -> V),
    (forall i, 0 <= c i <= 1) /\ (\sum_i c i = 1) 
    /\ (forall i, f i \in S) /\ (v = \sum_i c i *: f i) ]%classic.
Proof.
apply/seteqP; split=>v [T][c][f][P1][P2][P3]P4 /=; last first.
  by exists 'I_T.+1; exists c; exists f; do ! split.
have PT: #|T|.-1.+1 = #|T|.
  rewrite prednK//; case: ltnP=>//; rewrite leqn0=>/eqP PT.
  move: P2; rewrite big1=>[i _|/esym/eqP];
  by [move: (fintype0 i) | rewrite oner_eq0].
exists (#|T|.-1).
exists (fun i => c (enum_val (cast_ord PT i))).
exists (fun i => f (enum_val (cast_ord PT i))).
do ! split=>//.
- move: {+}PT; rewrite PT=>PT1; under eq_bigr do rewrite cast_ord_id.
  by rewrite -big_enum_val/= P2.
- move: {+}PT; rewrite PT=>PT1; under eq_bigr do rewrite cast_ord_id.
  by rewrite P4 big_enum_val/=.
Qed.

Theorem convex_perm_isotone m n (Phi : 'rV[R]_m -> 'rV[R]_n) (itv : interval R) :
  elem_mx_convex Phi itv ->
  (forall sp : 'S_m, exists sq : 'S_n, forall (x : 'rV_m), 
    (forall i, x 0 i \in itv) -> Phi (x *m perm_mx sp) = (Phi x) *m perm_mx sq) ->
      isotone Phi itv.
Proof.
move=>PPhi H x y Px Py Pxy.
move: {+}Pxy=>/majorizeP[A PA1 PA2].
have : [set` doubly_stochastic]%classic A by [].
  rewrite Birkhoff_doubly_stochastic convE =>[[r][c][f][P1][P2][P3]P4].
have P5 i : { s : 'S_m | f i = perm_mx s }.
  by move: (P3 i); rewrite inE/==>/is_perm_mxP/cid.
have P6 i : { t : 'S_n | (forall (x : 'rV_m), (forall i, x 0 i \in itv) ->  
  Phi (x *m perm_mx (projT1 (P5 i))) = (Phi x) *m perm_mx t) }.
  by move: (H (projT1 (P5 i)))=>/cid.
pose B := \sum_i c i *: perm_mx (projT1 (P6 i)).
(* pose z := Phi y *m (\sum_i c i *: perm_mx (projT1 (P6 i))). *)
rewrite weak_majorize_midP; exists (Phi y *m B).
  rewrite PA2 P4 mulmx_sumr; under eq_bigr do rewrite -scalemxAr.
  apply/(elem_lemx_trans (convex_convex_fun_le_itv (itv := itv) _ _ _ P2))=>//.
    by move=>i; move: (projT2 (P5 i))=>->; move=>j; rewrite col_permEV mxE.
  by move=>i; move: (P1 i)=>/andP[].
  suff -> : \sum_i c i *: Phi (y *m f i) = (Phi y *m B) by apply/elem_lemx_refl.
  rewrite mulmx_sumr; apply eq_bigr=>/= i _.
  rewrite -scalemxAr; move: (projT2 (P6 i))=><- //.
  by move: (projT2 (P5 i))=><-.
rewrite majorizeP; exists B=>//.
suff : [set` doubly_stochastic]%classic B by [].
rewrite Birkhoff_doubly_stochastic.
exists 'I_r.+1; exists c; exists (fun j => perm_mx (projT1 (P6 j))).
do ! split=>//.
by move=>i; rewrite inE /=; apply/perm_mx_is_perm.
Qed.

Theorem convex_perm_strongly_isotone m n (Phi : 'rV[R]_m -> 'rV[R]_n) (itv : interval R) :
  elem_mx_convex Phi itv -> elem_mx_nondecreasing Phi itv -> 
  (forall sp : 'S_m, exists sq : 'S_n, forall (x : 'rV_m), 
    (forall i, x 0 i \in itv) -> Phi (x *m perm_mx sp) = (Phi x) *m perm_mx sq) ->
      strongly_isotone Phi itv.
Proof.
move=>P1 P2 /(convex_perm_isotone P1) P3; move=>x y Px Py.
rewrite weak_majorize_midP=>[[u Pu1 Pu2]].
have Pu : fun_in_itv (u 0) itv.
  move=>i; move: Pu2=>/majorize_ub/(_ i)[j Pj].
  have: (`[x 0 i, y 0 j] <= itv)%O by apply/subitv_incc.
  move=>/subitvP; apply; rewrite inE /Order.le/= !bnd_simp Pj andbT.
  by apply/elem_lemxP.
apply/(weak_majorize_trans (y := Phi u)); last by apply/P3.
by apply/elem_lemx_weak_majorize/P2.
Qed.

Lemma conv_mxE m n (x y : 'M[R]_(m,n)) (t : {i01 R}) i j :
  conv t (x : convex_lmodType _) y i j = conv t (x i j : R^o) (y i j).
Proof. by rewrite !mxE convRE. Qed.

Lemma map_mx_elem_convex m (f : R -> R^o) (itv : interval R) :
  convex_fun f itv -> elem_mx_convex (@map_mx _ _ f 1 m) itv.
Proof.
move=>H t x y Px Py; apply/elem_lemxP=>? i.
by rewrite ord1 mxE !conv_mxE !mxE H.
Qed.

Lemma map_mx_elem_nondecreasing m (f : R -> R^o) (itv : interval R) :
  {in itv &, nondecreasing_fun f} -> elem_mx_nondecreasing (@map_mx _ _ f 1 m) itv.
Proof.
move=>H t x y Px Py; apply/elem_lemxP=>? i.
by rewrite ord1 !mxE H//; apply/elem_lemxP.
Qed.

Theorem weak_majorize_map_mx (f : R -> R) (itv : interval R) :
  convex_fun f itv -> forall m (x y : 'rV[R]_m),
    (forall i, x 0 i \in itv) -> (forall i, y 0 i \in itv) ->
      majorize x y -> weak_majorize (map_mx f x) (map_mx f y).
Proof.
move=>P1 m; apply/convex_perm_isotone.
  by apply: map_mx_elem_convex.
move=>sp; exists sp=>x _; rewrite !col_permEV; 
by apply/matrixP=>i j; rewrite !mxE.
Qed.

Theorem weak_majorize_map_mxW (f : R -> R^o) (itv : interval R) :
  convex_fun f itv -> {in itv &, nondecreasing_fun f} ->
    forall m (x y : 'rV[R]_m),
    (forall i, x 0 i \in itv) -> (forall i, y 0 i \in itv) ->
      weak_majorize x y -> weak_majorize (map_mx f x) (map_mx f y).
Proof.
move=>P1 P2 m; apply/convex_perm_strongly_isotone.
- by apply: map_mx_elem_convex.
- by apply: map_mx_elem_nondecreasing.
move=>sp; exists sp=>x _; rewrite !col_permEV; 
by apply/matrixP=>i j; rewrite !mxE.
Qed.

Lemma normr_weak_majorize m (x y : 'rV[R]_m) :
  majorize x y -> weak_majorize (map_mx normr x) (map_mx normr y).
Proof. by apply/(weak_majorize_map_mx (itv := `]-oo, +oo[))=>//; apply/normr_convex. Qed.

Lemma sqtB_convex c : convex_fun (fun x => (x - c) ^+ 2 : R^o) `]-oo, +oo[.
Proof.
move=>t a b _ _ /=; rewrite !convRE.
have {1}-> : c = (`1-(t%:inum) * c) + (t%:inum * c).
  by rewrite -mulrDl /onem subrK mul1r.
rewrite opprD addrACA -!mulrBr.
set x := a - c; set y := b - c.
have Pt1 : 0 <= 1 - t%:inum by rewrite subr_ge0.
set t1 := `1-(t%:inum).
rewrite !expr2 mulrDr mulrDl [X in _ + X]mulrDl mulrACA -addrA -lerBrDl.
rewrite [leRHS]addrAC -mulrBl -onemMr onemK mulrACA [_ * t1]mulrC -lerBrDl.
rewrite addrAC -mulrBr mulrACA -lerBrDl addrAC -mulrBr mulrACA -subr_ge0.
rewrite -addrA -!mulrBl -onemMr -/t1 [_ * t1]mulrC -mulrDr.
rewrite !mulr_ge0//; move: (sqr_ge0 (x-y))=>/le_trans; apply.
by rewrite expr2 mulrBr -[leRHS]addrA lerD2l mulrBl opprB addrC.
Qed.

Lemma sqt_convex : convex_fun (fun x => x ^+ 2 : R^o) `]-oo, +oo[.
Proof. by move=>t a b Pa Pb; move: (sqtB_convex 0 t Pa Pb ); rewrite !subr0. Qed.

Lemma sqt_weak_majorize m (x y : 'rV[R]_m) :
  majorize x y -> weak_majorize (map_mx (@GRing.exp _ ^~ 2%N) x) 
                                (map_mx (@GRing.exp _ ^~ 2%N) y).
Proof. by apply/(weak_majorize_map_mx (itv := `]-oo, +oo[))=>//; apply/sqt_convex. Qed.

Lemma maxrr_weak_majorize m (x y : 'rV[R]_m) c :
  weak_majorize x y -> weak_majorize (map_mx (fun i => maxr i c) x) 
                                (map_mx (fun i => maxr i c) y).
Proof.
apply/(weak_majorize_map_mxW (itv := `]-oo, +oo[))=>//.
apply/maxr_convexr.
by move=>a b _ _ Pab; rewrite ge_max !le_max lexx Pab/= orbT.
Qed.

Lemma maxrl_weak_majorize m (x y : 'rV[R]_m) c :
  weak_majorize x y -> weak_majorize (map_mx (fun i => maxr c i) x) 
                                (map_mx (fun i => maxr c i) y).
Proof.
apply/(weak_majorize_map_mxW (itv := `]-oo, +oo[))=>//.
apply/maxr_convexl.
by move=>a b _ _ Pab; rewrite ge_max !le_max lexx Pab/= orbT.
Qed.

End Convex_Monotone.

From mathcomp.analysis Require Import convex derive.

Section near.
Variable (T : topologicalType).

Lemma near_id  (P : T -> Prop) (x : T) :
  (\near x, P x) -> P x.
Proof. by rewrite -nbhs_nearE nbhsE_subproof /= =>[[B [ _ PB /(_ x)]]]; apply. Qed.

Lemma near_eq_lim (U : Type) (F : set_system U) {FF : Filter F} (f g : U -> T) :
  {near F, f =1 g} -> lim (f @ F)%classic = lim (g @ F)%classic.
Proof.
move=>P. rewrite /lim /lim_in.
f_equal. apply/funext=>x. rewrite propeqE; split.
apply: cvg_trans. by apply: near_eq_cvg.
apply: cvg_trans. apply: near_eq_cvg.
near=>y; symmetry; near: y. apply: P.
Unshelve. end_near.
Qed.

Lemma continuous_near_eq (U : nbhsType) (x : T) (f g : T -> U) :
  (\near x, f x = g x) -> {for x, continuous f} -> {for x, continuous g}.
Proof.
move=>P; rewrite /continuous_at /prop_for.
have -> : f x = g x by move: P; apply: near_id.
by apply: cvg_trans; apply: near_eq_cvg.
Qed.

End near.

Section near_derive.
Variable (R : numFieldType).
Implicit Type (V W : normedModType R).

Lemma derivable_near_eq V W (f g : V -> W) x :
  (\near x, f x = g x) -> forall v, derivable f x v -> derivable g x v.
Proof.
move=>P v P1. apply/cvg_ex; exists (derive f x v).
move: P1. apply: cvg_trans. apply: near_eq_cvg.
have [/eqP ->|v0] := boolP (v == 0).
  by near=>h; rewrite /= !scaler0 add0r !subrr scaler0.
near=>h; f_equal; f_equal;
near: h; move: P; near_simpl; rewrite -!nbhs_nearE !nbhs_ballP => [[e /= Pe P]].
exists (e / `|v|)=>/=.
  by apply divr_gt0=>//; rewrite normr_gt0.
move=>y /=; rewrite sub0r normrN => Py1 Py2; apply: P.
by rewrite -ball_normE/= opprD addrCA subrr addr0 normrN normrZ -ltr_pdivlMr ?normr_gt0.
by exists 1=>//= y/= _ _; f_equal; apply/P/ballxx.
Unshelve. all: end_near.
Qed.

Lemma is_derive_near_eq V W (f g : V -> W) x :
  (\near x, f x = g x) -> forall v h, is_derive x v f h -> is_derive x v g h.
Proof.
move=>P v h [] P1 P2; split.
  by move: P1; apply/derivable_near_eq.
rewrite -P2; symmetry. apply: near_eq_lim. clear h P1 P2.
have [/eqP ->|v0] := boolP (v == 0).
  by near=>h; rewrite /= !scaler0 add0r !subrr scaler0.
near=>h; f_equal; f_equal;
near: h; move: P; near_simpl; rewrite -!nbhs_nearE !nbhs_ballP => [[e /= Pe P]].
exists (e / `|v|)=>/=.
  by apply divr_gt0=>//; rewrite normr_gt0.
move=>y /=; rewrite sub0r normrN => Py1 Py2; apply: P.
by rewrite -ball_normE/= opprD addrCA subrr addr0 normrN normrZ -ltr_pdivlMr ?normr_gt0.
by exists 1=>//= y/= _ _; f_equal; apply/P/ballxx.
Unshelve. all: end_near.
Qed.

Lemma derive_id V (x v : V): 'D_v id x = v.
Proof. by move: (is_derive_id x v)=>[]. Qed.

Lemma differentiable_sum V W I (r : seq I) (P : pred I) (f : I -> V -> W) (x : V) :
  (forall i, P i -> differentiable (f i) x) -> 
    differentiable (\sum_(i <- r | P i) f i) x.
Proof.
elim/big_ind : _ =>// [?? P1 P2 P3|i Pi]; last by apply.
by apply: differentiableD; [apply P1|apply P2].
Qed.

Lemma is_derive_sum V W I (r : seq I) (P : pred I) (h : I -> V -> W) (x v : V) (dh : I -> W) : 
  (forall i, P i -> is_derive x v (h i) (dh i)) ->
    is_derive x v (\sum_(i <- r | P i) h i) (\sum_(i <- r | P i) dh i).
Proof.
move=>Pi; elim/big_ind2 : _ => // [|] *; [exact: is_derive_cst|exact: is_deriveD].
Qed.

Lemma continuous_sum V {T : topologicalType}
  I (r : seq I) (P : pred I) (f : I -> (T -> V)) (x : T) : 
  (forall i, P i -> {for x, continuous (f i)}) -> {for x, continuous (\sum_(i <- r | P i) f i)}.
Proof.
move=>P1; elim/big_rec : _; first by apply: cst_continuous.
by move=>i y Pi Py; apply: continuousD=>//; apply: P1.
Qed.

End near_derive.

Section second_derivative_concave.
Variable (R : realType).
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Lemma second_derivative_concave (f : R -> R^o) (a b : R^o) :
  (forall x : R, a < x < b -> ('D_1 ('D_1 f)) x <= 0) ->
  f x @[x --> b^'-] --> f b ->
  f x @[x --> a^'+] --> f a ->
  {in `]a, b[, forall x : R, derivable f x 1} ->
  {in `]a, b[, forall x : R, derivable ('D_1 f) x 1} ->
  forall t : {i01 R}, a <= b -> conv t (f a) (f b) <= f (conv t a b).
Proof.
move=>P1 P2 P3 P4 P5 t Pab.
suff: (-f) (conv t a b) <= conv t ((-f) a) ((-f) b).
  by rewrite -lerN2 convN !fctE !opprK.
have Q1 : {in `]a, b[, forall x : R, is_derive x 1 (-f) (- 'D_1 f x)}.
  move=>x Px; move: (P4 x Px)=>/derivableP; apply is_deriveN.
have Q2 : {in `]a, b[, forall x : R, is_derive x 1 ('D_1 (-f)) (- 'D_1 ('D_1 f) x)}.
  move=>x Px. move: (P5 x Px)=>/derivableN/derivableP.
  rewrite deriveN; first by apply: P5.
  apply: is_derive_near_eq.
  exists (minr (x-a) (b-x))=>/=.
    by move: Px; rewrite in_itv/= lt_min !subr_gt0.
  move=>y /= Py; rewrite deriveN//; apply: P4; rewrite in_itv/=.
  move: Py; rewrite lt_min=>/andP[] /ltr_distlBl.
  rewrite opprB addrC subrK -normrN opprB =>-> /ltr_distlBl.
  by rewrite ltrBlDl subrK.
apply: second_derivative_convex=>[|||||//].
- move=>x Px; move: (Q2 x); rewrite in_itv/==>/(_ Px)[ _ ->].
  by rewrite oppr_ge0; apply: P1.
- apply: continuous_cvg=>[|//]; apply/continuousN=>//.
- apply: continuous_cvg=>[|//]; apply/continuousN=>//.
- by move=>x /Q1 [].
- by move=>x /Q2 [].
Qed.

End second_derivative_concave.

#[global] Hint Extern 0 (is_true (0 <= _ `^ _)) => apply: powR_ge0 : core.

Section exp_extra.
Variable (R : realType).
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Lemma expR_sum I (r : seq I) (P : pred I) (f : I -> R) :
  expR (\sum_(i <- r | P i) f i) = \prod_(i <- r | P i) expR (f i).
Proof. by elim/big_rec2: _ =>[|???? <- ]; rewrite ?expR0// expRD. Qed.

Lemma powR_sum I (r : seq I) (P : pred I) (a : R) (f : I -> R) :
  0 < a ->
  powR a (\sum_(i <- r | P i) f i) = \prod_(i <- r | P i) powR a (f i).
Proof. 
move=>Pa; elim/big_rec2: _ =>[|???? <- ]; 
by rewrite ?powRr0// powRD// (gt_eqF Pa) implybT.
Qed.

Lemma derivable_ln (x : R) : 0 < x -> derivable (@ln R) x 1.
Proof. move=>/is_derive1_ln P. apply: ex_derive. Qed.

Lemma continuous_powR (a x : R) : 
  0 < x -> {for x, continuous (powR a)}.
Proof.
move=>Px; rewrite /powR; case: eqP.
  move=> _ y. move=>/ nbhs_singleton P1.
  rewrite /nbhs/= /nbhs_ball_/=/filter_from/=.
  exists x=>// z/=; case: eqP; last by move: Px P1 =>/lt0r_neq0/negPf->.
  by move=>->; rewrite subr0 ger0_norm ?ltxx//; apply/ltW.
have ->: (fun x1 : R => expR (x1 * ln a)) = expR \o (fun x1 => x1 * ln a).
  by apply/funext=>x1 /=.
move=>Pa; apply: continuous_comp; last by apply: continuous_expR.
apply: continuousM=>[//|]; apply: cst_continuous.
Qed.

Lemma is_derive1_powR (f g : R -> R) (x df dg : R) :
  0 < f x -> is_derive x 1 f df -> is_derive x 1 g dg ->
  is_derive x 1 (fun x : R => (f x) `^ (g x)) (((g x) * (df / (f x)) + ln (f x) * dg ) * (f x) `^ (g x)).
Proof.
move=>Px Pf Pg.
rewrite {1}/powR.
apply: (is_derive_near_eq (f := fun x0 : R => expR (g x0 * ln (f x0)))).
  move: {+}Pf=>[]; rewrite derivable1_diffP=>/differentiable_continuous.
  rewrite /prop_for /continuous_at=>/cvgrPdist_lt/(_ `|f x|).
  rewrite normr_gt0 gt_eqF// => /(_ isT)=>[[e /= Pe P]] _.
  by exists e=>// y/=/P; case: eqP=>// ->; rewrite subr0 ltxx.
rewrite mulrC; apply: is_derive1_comp.
  apply: (is_derive_eq (is_derive_expR _)).
  by rewrite /powR (gt_eqF Px).
apply: (is_derive_eq (is_deriveM (dg := df / f x) Pg _))=>//=.
by rewrite mulrC; apply: is_derive1_comp; apply: is_derive1_ln.
Qed.

Lemma is_derive1_powRl (f : R -> R) (x df a : R) :
  0 < f x -> is_derive x 1 f df ->
  is_derive x 1 (fun x : R => (f x) `^ a) (a * df * (f x) `^ (a - 1)).
Proof.
move=>Px Pf.
apply: (is_derive_eq (is_derive1_powR Px Pf (is_derive_cst _ _ _))).
rewrite !fctE mulr0 addr0 -!mulrA; do 2 f_equal.
by rewrite powRD ?powR_inv1 1?mulrC// ?ltW// (gt_eqF Px) implybT.
Qed.

Lemma is_derive1_powRr (f : R -> R) (a x df : R) :
  0 < f x -> is_derive x 1 f df ->
    is_derive x 1 (fun x => powR a (f x)) (df * ln a * a `^ f x).
Proof.
move=>Px; rewrite /powR; case: eqP=> Pa.
  move: Px=>/lt0r_neq0/negPf P1 Pf. rewrite P1 mulr0.
  move: (is_derive_cst (0 : R) x 1); apply: is_derive_near_eq.
  move: {+}Pf=>[]; rewrite derivable1_diffP=>/differentiable_continuous.
  rewrite /prop_for /continuous_at=>/cvgrPdist_lt/(_ `|f x|).
  rewrite normr_gt0 P1 => /(_ isT)=>[[e /= Pe P]] _.
  by exists e=>// y/=/P; case: eqP=>// ->; rewrite subr0 ltxx.
move=>Pf; rewrite mulrC; apply: is_derive1_comp.
apply: (is_derive_eq (is_deriveM _ _))=>//=.
by rewrite scaler0 add0r /GRing.scale/= mulrC.
Qed.

Lemma is_derive1_powRx (a x : R) : 
  0 < x -> is_derive x 1 (powR a) (ln a * a `^ x).
Proof. by move=>Px; rewrite -[_ * _]mul1r mulrA; apply: is_derive1_powRr. Qed.

Lemma is_derive1_powxR (a x : R) : 
  0 < x -> is_derive x 1 (@powR R ^~ a) (a * x `^ (a - 1)).
Proof. by move=>Px; apply: (is_derive_eq (is_derive1_powRl _ _ _))=>//; rewrite mulr1. Qed.

Lemma powR1n_limn (x : R) :
  0 < x -> (fun k : nat => x `^ k%:R ^-1) @ \oo --> (1 : R).
Proof.
move=>Px. rewrite -cvg_shiftS/=.
have: expR (n.+1%:R^-1 * ln x) @[n --> \oo] --> expR 0.
  apply: continuous_cvg. apply: continuous_expR.
  apply/cvg_ballP=>e Pe.
  exists (Num.ExtraDef.archi_bound (`|ln x|/e))=>//= y /= Py.
  rewrite -ball_normE/= sub0r normrN normrM ger0_norm// ltr_pdivrMl// -ltr_pdivrMr//.
  apply: (lt_le_trans (archi_boundP _)).
  by apply/divr_ge0=>//; apply/ltW.
  rewrite ler_nat; apply/(leq_trans Py)/leqnSn.
under [in X in _ -> X] eq_cvg do rewrite /powR (gt_eqF Px).
rewrite expR0; apply.
Qed.

Lemma powRN_inv (x r : R) : 0 <= x -> (x `^ r)^-1 = x^-1 `^ r.
Proof. by move=>Px; rewrite -powRN -powR_inv1// -powRrM mulN1r. Qed.

(* replace ge1r_powR *)
Lemma ge1r_powR (a r : R) : 0 <= a <= 1 -> 1 <= r -> a `^ r <= a.
Proof.
have [/eqP -> _ Pr | /negPf Pp] := boolP (a == 0).
  by rewrite powR0// gt_eqF// (lt_le_trans ltr01 Pr).
rewrite le_eqVlt eq_sym Pp/=; exact: ge1r_powR.
Qed.

Lemma continuous_powRr (a x : R) : 
  0 < x -> {for x, continuous (@powR R ^~ a)}.
Proof.
move=>Px; apply/differentiable_continuous.
rewrite -derivable1_diffP.
by move: (is_derive1_powxR a Px)=>[].
Qed.

Lemma is_derive12_powxR (a x : R) : 
  0 < x -> is_derive x 1 ('D_1 (@powR R ^~ a)) (a * (a-1) * x `^ (a - 2)).
Proof.
move=>Px.
move: (is_deriveM (is_derive_cst (a : R) _ _) (is_derive1_powxR (a-1) Px)).
rewrite scaler0 addr0 fctE/= /GRing.scale/= -addrA -[-1 - 1]opprB opprK mulrA.
apply: is_derive_near_eq.
exists `|x| => /= [|y /=]; first by rewrite normr_gt0 (gt_eqF Px).
by move=>/ltr_distlBl; rewrite ger0_norm ?ltW// subrr=>/(is_derive1_powxR a) [] _ ->.
Qed.

Lemma convex_powR (r : R) (t : {i01 R}) (a b : R^o) :
  1 <= r -> (0 <= a) -> (0 <= b) ->
  (conv t a b) `^ r <= conv t (a `^ r : R^o) (b `^ r : R^o).
Proof.
move=>Pr.
wlog : a b t / a <= b => [IH | IH Pa Pb].
  case E: (a <= b); first by apply: IH.
  move=>Pa Pb; rewrite convC [leRHS]convC; apply: IH=>//.
  by move: E; case: ltP=>// /ltW.
case E: (a == 0).
  move: E =>/eqP ->; rewrite powR0 ?gt_eqF// ?(lt_le_trans ltr01 Pr)//.
  rewrite /conv/=/conv/= scaler0 !add0r /GRing.scale/= powRM// ler_wpM2r// 
  ge1r_powR//; by case: t.
have Pa0 : 0 < a by rewrite lt_def E.
move: (lt_le_trans Pa0 IH) => Pb0.
apply: (second_derivative_convex (f := fun x => x `^ r))=>/=[|||||//].
- move=>x /andP[] /(lt_trans Pa0) Px _.
  move: (is_derive12_powxR r Px)=>[] _ ->.
  by rewrite !mulr_ge0// ?(le_trans ler01 Pr)// ?subr_ge0//.
- by apply/cvg_at_left_filter/continuous_powRr.
- by apply/cvg_at_right_filter/continuous_powRr.
- by move=>x; rewrite in_itv/==>/andP[]/(lt_trans Pa0)/(is_derive1_powxR r)[].
- by move=>x; rewrite in_itv/==>/andP[]/(lt_trans Pa0)/(is_derive12_powxR r)[].
Qed.

Lemma powRD_ler (r a b : R) :
  1 <= r -> 0 <= a -> 0 <= b ->
    a `^ r + b `^ r <= (a + b) `^ r.
Proof.
move=>Pr; rewrite le_eqVlt; case: eqP=>[<- _ _| _ /= Pa Pb].
  by rewrite powR0 ?add0r// gt_eqF// (lt_le_trans ltr01 Pr).
have Pab : 0 < a + b by apply/(lt_le_trans Pa); rewrite lerDl.
move: (ltW Pa) (ltW Pab) => ??.
rewrite -[leRHS]mul1r -ler_pdivrMr ?powR_gt0//.
rewrite mulrDl powRN_inv -?powRM// ?invr_ge0//.
have ->: 1 = a / (a+b) + b / (a+b) by rewrite -mulrDl mulfV// gt_eqF.
apply/lerD; apply/ge1r_powR=>//; apply/andP; split.
1,3: by apply/divr_ge0=>//.
all: by rewrite ler_pdivrMr// mul1r ?lerDl// lerDr.
Qed.

Lemma powR_sum_ler (r : R) I (s : seq I) (P : pred I) (f : I -> R) :
  1 <= r -> (forall i, P i -> 0 <= f i) ->
    \sum_(i <- s | P i) (f i) `^ r <= (\sum_(i <- s | P i) f i) `^ r.
Proof.
move=>Pr Pf; elim: s=>[|a s IH]; first by rewrite big_nil.
rewrite !big_cons; case E: (P a)=>//.
apply/(le_trans _ (powRD_ler _ _ _))=>//.
by rewrite lerD2l. by apply/Pf. clear IH E.
elim: s => [|b s]; rewrite ?big_nil// big_cons;
by case E: (P b)=>//; apply/addr_ge0/Pf.
Qed.

Lemma gt0_ler_ppowR (r : R) : 0 < r ->
  {in Num.pos &, {mono @powR R ^~ r : x y / x <= y >-> x <= y}}.
Proof.
move=>Pr x y; rewrite !posrE /powR => Px Py.
move: {+}Px {+}Py => /lt0r_neq0/negPf-> /lt0r_neq0/negPf->.
by rewrite ler_expR ler_pM2l// ler_ln.
Qed.

Lemma gt0_ltr_ppowR (r : R) : 0 < r ->
  {in Num.pos &, {mono @powR R ^~ r : x y / x < y >-> x < y}}.
Proof.
move=>Pr x y; rewrite !posrE /powR => Px Py.
move: {+}Px {+}Py => /lt0r_neq0/negPf-> /lt0r_neq0/negPf->.
by rewrite ltr_expR ltr_pM2l// ltr_ln.
Qed.

End exp_extra.

Section xlnx.
Variable (R : realType).
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Lemma xlnx_sum_fin (I : finType) (P : pred I) (f : I -> R) :
  (forall i, P i -> f i >= 0) ->
    \sum_(i | P i) (f i) * ln (f i) <= 
      (\sum_(i | P i) (f i)) * ln (\sum_(i | P i) (f i)).
Proof.
move=>H.
have [/eqP P1 | PA ] := boolP (\sum_(i | P i) f i == 0).
  rewrite P1; move: (psumr_eq0P H P1)=>P2.
  by rewrite big1 ?mul0r// =>i /P2 ->; rewrite mul0r.
have P1: 0 < \sum_(i | P i) f i by rewrite lt_def PA/=; apply sumr_ge0.
rewrite -ler_expR expR_sum mulrC expRM lnK ?posrE// powR_sum//.
apply: ler_prod=>i Pi; rewrite expR_ge0/= -ler_ln ?posrE ?expR_gt0// ?powR_gt0//.
rewrite expRK ln_powR.
have [/eqP -> | Pf ] := boolP (f i == 0).
  by rewrite !mul0r.
rewrite ler_wpM2l// ?H// ler_ln ?posrE// ?lt_def ?Pf ?H//.
by rewrite (bigD1 i)//= lerDl sumr_ge0// =>? /andP[]/H.
Qed.

Lemma xlnx_sum I (r : seq I) (P : pred I) (f : I -> R) :
  (forall i, P i -> f i >= 0) ->
    \sum_(i <- r | P i) (f i) * ln (f i) <= 
      (\sum_(i <- r | P i) (f i)) * ln (\sum_(i <- r | P i) (f i)).
Proof.
move=>p1; case: r=>[|x0 r0]; first by rewrite !big_nil mul0r.
set r := x0 :: r0.
rewrite -big_filter -[in X in X * _]big_filter -[in X in _ * X]big_filter.
rewrite !(big_nth x0) !big_mkord; apply: xlnx_sum_fin=> i _; 
apply/p1/seq_nth_ord_size_true.
Qed.

Lemma is_derive1_xlnx (x : R) :
  0 < x -> is_derive x 1 (fun x1 : R => x1 * ln x1) (ln x + 1).
Proof.
move=>Px; move: (is_deriveM (is_derive_id _ _) (is_derive1_ln Px)).
by rewrite /GRing.scale/= mulfV ?(gt_eqF Px)// mulr1 addrC.
Qed.

Lemma is_derive12_xlnx (x : R) :
  0 < x -> is_derive x 1 ('D_1 (fun x1 : R => x1 * ln x1)) (1 / x).
Proof.
move=>Px; move: (is_deriveD (is_derive1_ln Px) (is_derive_cst (1 : R) _ _)).
rewrite addr0 div1r; apply: is_derive_near_eq.
exists `|x| => /= [|y /=]; first by rewrite normr_gt0 (gt_eqF Px).
by move=>/ltr_distlBl; rewrite ger0_norm ?ltW// subrr=>/is_derive1_xlnx [] _ ->.
Qed.

Lemma continuous_xlnx (x : R) :
  0 < x -> {for x, continuous (fun x : R => x * ln x)}.
Proof.
by move=>/is_derive1_xlnx=>[[]]; 
rewrite derivable1_diffP=>/differentiable_continuous.
Qed.

Lemma ln1x_le (x : R) :
  0 <= x -> 0 <= ln (1 + x) <= x.
Proof.
move=>Px; rewrite ln_ge0/= ?lerDl// -subr_le0 -[0]subr0 -{1}ln1 -{2}[1]addr0.
have P1 (y : R) : 0 <= y -> is_derive y 1 (fun y : R => ln (1 + y) - y) (1/(y+1)-1).
  move=>Py. apply: is_deriveB.
  rewrite mulrC addrC; apply: is_derive1_comp.
  by apply: is_derive1_ln; apply/(lt_le_trans ltr01); rewrite lerDl.
  rewrite -{3}[1]add0r; apply: is_deriveD.
apply: (ler0_derive1_nincr (f := fun x => ln (1 + x) - x) (a := 0) (b := x))=>//.
- by move=>y; rewrite in_itv/==>/andP[]/ltW/P1[].
- move=>y; rewrite in_itv derive1E/==>/andP[]/ltW Py _; 
  move: {+}Py=> /P1[ _ -> ].
  rewrite subr_le0 ler_pdivrMr ?mul1r ?lerDr//.
  by apply/(lt_le_trans ltr01); rewrite lerDr.
- apply: continuous_in_subspaceT=>y.
  rewrite inE/= in_itv/==>/andP[]/P1[]/= + _ _.
  by rewrite derivable1_diffP=>/differentiable_continuous.
Qed.

Lemma xlnx_cvg :
  x * ln x @[x --> 0^'+] --> (0 : R).
Proof.
have : 0 @[ x --> (0 : R)^'+] --> (0 : R) by apply: cvg_cst.
have : - (2 * (Num.sqrt x - x)) @[x --> 0^'+] --> (0 : R).
  rewrite -{2}oppr0; apply: cvgN.
  have {2}-> : 0 = 2 * (Num.sqrt 0 - 0) :> R by rewrite sqrtr0 subrr mulr0.
  apply: cvgMr; apply: cvgB.
  apply: continuous_cvg; first by apply: sqrt_continuous.
  1,2: by apply/cvg_at_right_filter/cvg_id.
apply: squeeze_cvgr.
exists 1=>//= y /= + Py0; rewrite sub0r normrN gtr0_norm// =>Py1.
have P3 : 0 <= y by apply/ltW.
rewrite -mulrN -ler_pdivlMl// opprB 
  -[X in _ && X](ler_pM2l (x := 2^-1))// mulr0 mulrCA -ln_powR.
have /ln1x_le : 0 <= 1 / (y `^ 2^-1) - 1.
  by rewrite subr_ge0 powR12_sqrt// ler_pdivlMr ?mul1r ?sqrtr_gt0//
    -(ler_pXn2r (n := 2)) ?nnegrE// sqr_sqrtr// expr1n ltW.
rewrite addrC subrK div1r lnV; first by rewrite posrE powR_gt0.
rewrite lerNr lerNl oppr0 opprB andbC -(ler_pM2l Py0) -[_ <= 0](ler_pM2l Py0).
by rewrite mulr0 mulrBr mulr1 {1}powR12_sqrt// 
  -{2}(sqr_sqrtr P3) expr2 mulfK ?gt_eqF// ?sqrtr_gt0.
Qed.

Lemma convex_xlnx (t : {i01 R}) (a b : R^o) : 0 <= a -> 0 <= b ->
  (conv t a b) * ln (conv t a b) <= conv t (a * ln a : R^o) (b * ln b : R^o).
Proof.
wlog : t a b / a < b => [IH|ab Pa Pb].
  have [ab| ba Pa Pb] := ltP a b.
    by apply: IH.
  move: ba; rewrite le_eqVlt=>/orP[/eqP->|ba]; first by rewrite !convmm.
  by rewrite convC [in leRHS]convC; apply: IH.
apply: (second_derivative_convex (f := fun x => x * ln x))=>//.
- move=>x /andP []/(le_lt_trans Pa) Px _.
  by move: (is_derive12_xlnx Px)=>[] _ ->; rewrite divr_ge0// ltW.
- by apply/cvg_at_left_filter/continuous_xlnx/(le_lt_trans Pa ab).
- move: Pa; rewrite le_eqVlt=>/orP[/eqP <-|Pa];
    last by apply/cvg_at_right_filter/continuous_xlnx.
  rewrite mul0r; apply: xlnx_cvg.
- by move=>x /andP [] /(le_lt_trans Pa) /is_derive1_xlnx [].
- by move=>x /andP [] /(le_lt_trans Pa) /is_derive12_xlnx [].
- by apply/ltW.
Qed.

Lemma xlnx_average_sum_ord n (x : 'I_n -> R) :
  (forall i, 0 <= x i) ->
    (\sum_i x i) * ln ((\sum_i x i) / (\sum_(i < n) 1)) <=
      (\sum_i (x i) * ln (x i)).
Proof.
move=>P1; case: n x P1=>[x _ | n x Pi].
  by rewrite !big_ord0 !mul0r.
pose r := \big[maxr/x 0]_i (x i).
suff : (fun x => x * ln x) ((\sum_i x i) / (\sum_(i < n.+1) 1)) <=
  (\sum_i (x i) * ln (x i)) / (\sum_(i < n.+1) 1).
  by rewrite sumr_const card_ord mulrC mulrA ler_pM2r// mulrC.
apply: (convex_average_seq (f := fun x => x * ln x) (itv := `[0,+oo[)).
- by move=>t a b /andP[] Pa _ /andP[] Pb _; apply/convex_xlnx.
- by move=>/= i _; rewrite in_itv/= andbT.
- by rewrite mul0r.
Qed.

Lemma xlnx_average_sum I (r : seq I) (P : pred I) (x : I -> R) :
  (forall i, P i -> 0 <= x i) ->
    (\sum_(i <- r | P i) x i) * ln ((\sum_(i <- r | P i) x i) / (\sum_(i <- r | P i) 1)) <=
      (\sum_(i <- r | P i) (x i) * ln (x i)).
Proof.
move=>H; case: r=>[|x0 r0].
  by rewrite !big_nil !mul0r.
set s := x0 :: r0.
rewrite -![\big[_/_]_(_ <- s|_) _]big_filter !(big_nth x0) !big_mkord.
apply: xlnx_average_sum_ord=>i; apply/H/seq_nth_ord_size_true.
Qed.

End xlnx.

Section majorize_inequality.
Variable (R : realType).

Lemma powR_weak_majorize m (x y : 'rV[R]_m) (p : R) :
  1 <= p -> (forall i, 0 <= x 0 i) -> (forall i, 0 <= y 0 i) ->
  weak_majorize x y -> weak_majorize (map_mx (@powR _ ^~ p) x)
                                               (map_mx (@powR _ ^~ p) y).
Proof.
move=>Pp Px Py. 
apply/(weak_majorize_map_mxW (itv := `[0, +oo[))=>//.
- move=>t a b Pa Pb; apply/convex_powR=>//.
  1,2: by move: Pa Pb; rewrite !in_itv/==>/andP[]++/andP[].
- move=> a b; rewrite !in_itv/= !andbT=> Pa Pb Pab.
  by rewrite ge0_ler_powR// (le_trans _ Pp).
all: by move=>i; rewrite in_itv/= andbT.
Qed.

Lemma exp_ln_weak_majorize m (x y : 'rV[R]_m) (f : R -> R) :
  convex_fun (f \o expR) `]-oo,+oo[ -> 
    nondecreasing_fun (f \o expR) ->
      (forall i, 0 < x 0 i) -> (forall i, 0 < y 0 i) ->
    weak_majorize (map_mx (@ln _) x) (map_mx (@ln _) y) -> 
      weak_majorize (map_mx f x) (map_mx f y).
Proof.
move=>Pf1 Pf2 Px Py.
have <-: map_mx (f \o expR) (map_mx (@ln _) x) = map_mx f x.
  by apply/matrixP=>? i; rewrite !mxE ord1/= lnK// posrE.
have <-: map_mx (f \o expR) (map_mx (@ln _) y) = map_mx f y.
  by apply/matrixP=>? i; rewrite !mxE ord1/= lnK// posrE.
by apply/(weak_majorize_map_mxW Pf1)=>// a b _ _; apply Pf2.
Qed.

Lemma ln_weak_majorize m (x y : 'rV[R]_m) :
  (forall i, 0 < x 0 i) -> (forall i, 0 < y 0 i) ->
    weak_majorize (map_mx (@ln _) x) (map_mx (@ln _) y) -> 
      weak_majorize x y.
Proof.
move=>Px Py.
have {2}<- : map_mx id x = x by rewrite map_mx_id.
have {2}<- : map_mx id y = y by rewrite map_mx_id.
apply: exp_ln_weak_majorize=>//.
by move=>t a b _ _; apply/convex_expR.
by move=>a b Pab /=; rewrite ler_expR.
Qed.

Lemma ln_prod I (r : seq I) (P : pred I) (f : I -> R) : 
  (forall i, P i -> 0 < f i) ->
    ln (\prod_(i <- r | P i) f i) = \sum_(i <- r | P i) ln (f i).
Proof.
move=>Pi; elim: r => [|a r IH]; first by rewrite !big_nil ln1.
rewrite !big_cons; case E: (P a)=>//.
rewrite lnM ?IH// posrE ?Pi//.
by apply/prodr_gt0.
Qed.

Lemma prod_sum_weak_majorize_ln m (x y : 'rV[R]_m) :
  (forall i, 0 < x 0 i) ->
    x \is rv_nonincreasing -> y \is rv_nonincreasing ->
      (forall k : 'I_m, \prod_(i < m | (i <= k)%N) x 0 i <= \prod_(i < m | (i <= k)%N) y 0 i) ->
        (forall i, 0 < y 0 i) /\ weak_majorize (map_mx (@ln _) x) (map_mx (@ln _) y).
Proof.
move=>Px1 Px2 Py2 Pp.
move: (rv_nonincreasing_itv 0 Px2)=>[n Pn].
have Py3 i : 0 < y 0 i.
  elim/ord_ltn_ind: i => i IH1.
  move: (Pp i)=> P1.
  have: 0 < \prod_(i0 < m | (i0 <= i)%N) x 0 i0 by apply/prodr_gt0.
  move=>/lt_le_trans/(_ P1); rewrite (bigD1 i)//=.
  rewrite pmulr_lgt0//; apply/prodr_gt0=>j.
  rewrite -(inj_eq val_inj)/= andbC -ltn_neqAle; apply/IH1.
split=>//.
move=>i; rewrite !rv_nonincreasing_sorted.
  1,2: apply/rv_nonincreasingP=>a b P; 
    by rewrite !mxE ler_ln ?posrE//; apply/rv_nonincreasingP.
under eq_bigr do rewrite mxE.
under [leRHS]eq_bigr do rewrite mxE.
move: (Pp i); rewrite -ler_ln ?ln_prod//;
by rewrite posrE; apply/prodr_gt0.
Qed.

Lemma prod_sum_weak_majorize_gt0 m (x y : 'rV[R]_m) :
  (forall i, 0 < x 0 i) ->
    x \is rv_nonincreasing -> y \is rv_nonincreasing ->
      (forall k : 'I_m, \prod_(i < m | (i <= k)%N) x 0 i <= \prod_(i < m | (i <= k)%N) y 0 i) ->
        weak_majorize x y.
Proof.
move=>Px1 Px2 Py2 /(prod_sum_weak_majorize_ln Px1 Px2 Py2)=>[[]].
by apply/ln_weak_majorize.
Qed.

Lemma prod_sum_weak_majorize m (x y : 'rV[R]_m) :
  (forall i, 0 <= x 0 i) -> (forall i, 0 <= y 0 i) ->
    x \is rv_nonincreasing -> y \is rv_nonincreasing ->
      (forall k : 'I_m, \prod_(i < m | (i <= k)%N) x 0 i 
                     <= \prod_(i < m | (i <= k)%N) y 0 i) ->
        weak_majorize x y.
Proof.
move=>Px1 Py1 Px2 Py2.
move: (rv_nonincreasing_itv 0 Px2)=>[n].
have [Pmn H|] := ltnP m n.
  apply: prod_sum_weak_majorize_gt0=>// i.
  move: (H i)=>[] + _; apply.
  by apply/(ltn_trans (ltn_ord i) Pmn).
move=>/subnKC P.
move: x y Px1 Py1 Px2 Py2; rewrite -P=>x y Px1 Py1 Px2 Py2 IH H1.
rewrite -[x]hsubmxK -[y]hsubmxK; apply weak_majorize_row_mx.
  apply/prod_sum_weak_majorize_gt0.
  - move=>i; move: (IH (lshift _ i))=>[] + _;
    by rewrite mxE; apply=>/=.
  1,2: apply/rv_nonincreasingP=>i j Pij; 
    by rewrite !mxE; apply/rv_nonincreasingP.
  - move=>i; under eq_bigr do rewrite mxE.
    under [leRHS]eq_bigr do rewrite mxE.
    move: (H1 (lshift _ i)).
    rewrite !big_split_ord/=; do ! rewrite ?[X in _ * X]big1 ?mulr1//.
    1,2: move=>j /leq_ltn_trans/(_ (ltn_ord _));
      by rewrite -ltn_subRL subnn.
apply/elem_lemx_weak_majorize/elem_lemxP=>i j.
rewrite ord1 !mxE; apply/(le_trans (y := 0))=>//.
by move: (IH (rshift n j))=>[] _; apply=>/=; rewrite leq_addr.
Qed.

Lemma entropy_majority m (x y : 'rV[R]_m) :
  (forall i, 0 <= x 0 i) -> (forall i, 0 <= y 0 i) ->
    majorize x y -> weak_majorize (map_mx (fun a => a * ln a) x)
                                  (map_mx (fun a => a * ln a) y).
Proof.
move=>Px Py; apply/(weak_majorize_map_mx (itv := `[0, +oo[)).
  move=>t a b; rewrite !in_itv/= !andbT; apply/convex_xlnx.
all: by move=>i; rewrite in_itv/= andbT.
Qed.

Lemma weak_majorize_sum m (x y : 'rV[R]_m) :
  weak_majorize x y -> \sum_i x 0 i <= \sum_i y 0 i.
Proof.
move=>/weak_majorize_ltP/(_ m).
under [leLHS]eq_bigl do rewrite ltn_ord.
under [leRHS]eq_bigl do rewrite ltn_ord.
by rewrite !sort_v_sum.
Qed.

Lemma majority_entropy_le m (x y : 'rV[R]_m) :
  (forall i, 0 <= x 0 i) -> (forall i, 0 <= y 0 i) ->
    majorize x y -> \sum_i (x 0 i * ln (x 0 i)) <= \sum_i (y 0 i * ln (y 0 i)).
Proof.
move=>P1 P2 /(entropy_majority P1 P2)/weak_majorize_sum.
under eq_bigr do rewrite mxE.
by under [leRHS]eq_bigr do rewrite mxE.
Qed.

End majorize_inequality.

Import ExtNumTopology.

(* to avoid messy type cast of singular values *)
HB.lock Definition svd_fR (R : realType) m n (A : 'M[R[i]]_(m,n)) (i : nat) :=
  complex.Re (svd_f A i).

Section svd_fR.
Variable (R : realType).
Local Notation C := R[i].

Lemma svd_fRE m n (A : 'M[C]_(m,n)) :
  svd_fR A = (@complex.Re R) \o (svd_f A).
Proof. by apply/funext=>i; rewrite unlock. Qed.

Lemma svd_fE m n (A : 'M[C]_(m,n)) :
  svd_f A = real_complex _ \o (svd_fR A).
Proof. by apply/funext=>i; rewrite svd_fRE /= c2rK ?ger0_real. Qed.

Lemma svd_fR_nincr m n (A : 'M[C]_(m,n)) i j :
  (i <= j)%N -> svd_fR A j <= svd_fR A i.
Proof. by move=>Pij; rewrite svd_fRE/= ler_c2r// svd_f_nincr. Qed.

Lemma svd_fR_ge0 m n (A : 'M[C]_(m,n)) i : 0 <= svd_fR A i.
Proof. by rewrite svd_fRE/= c2r_ge0. Qed.

Lemma svd_fR_nneg m n (A : 'M[C]_(m,n)) i : svd_fR A i \is Num.nneg.
Proof. by rewrite nnegrE svd_fR_ge0. Qed.

Lemma svd_fR_gt0 m n (A : 'M[C]_(m,n)) i : (i < \rank A)%N -> 0 < svd_fR A i.
Proof. by move=>Pi; rewrite svd_fRE/= c2r_gt0// svd_f_gt0. Qed.

Lemma svd_fR_eq0 m n (A : 'M[C]_(m,n)) i : (\rank A <= i)%N -> svd_fR A i = 0.
Proof. by move=>Pi; rewrite svd_fRE/= svd_f_eq0. Qed.

Lemma svd_fR_pos m n (A : 'M[C]_(m,n)) i : (i < \rank A)%N -> svd_fR A i \is Num.pos.
Proof. rewrite posrE; exact: svd_fR_gt0. Qed.

End svd_fR.

#[global] Hint Extern 0 (is_true (0 <= svd_fR _ _)) => apply: svd_fR_ge0 : core.
#[global] Hint Extern 0 (is_true (svd_fR _ _ \is Num.nneg)) => apply: svd_fR_nneg : core.

(* TODO : more inequalities *)
Section svd_inequlity.
Variable (R : realType).
Local Notation C := R[i].

Theorem svd_fR_prodM m n p (A : 'M[C]_(m,n)) (B : 'M[C]_(n,p)) k :
  \prod_(i < k) svd_fR (A *m B) i <= \prod_(i < k) (svd_fR A i * svd_fR B i).
Proof.
rewrite -lecR !realc_prod.
move: (svd_f_prodM A B k); rewrite !svd_fE/=.
by under [leRHS]eq_bigr do rewrite -realcM.
Qed.

Lemma weak_majorize_svd_fR m n p (A : 'M[C]_(m,n)) (B : 'M[C]_(n,p)) k :
  let x := \row_(i < k) svd_fR (A *m B) i in
  let y := \row_(i < k) (svd_fR A i * svd_fR B i) in
  weak_majorize x y.
Proof.
move=>x y; apply/prod_sum_weak_majorize.
- by move=>j; rewrite mxE.
- by move=>j; rewrite mxE mulr_ge0.
- by apply/rv_nonincreasingP=>i j Pij; rewrite !mxE svd_fR_nincr.
- by apply/rv_nonincreasingP=>i j Pij; rewrite !mxE ler_pM// svd_fR_nincr.
move=>r; under eq_bigr do rewrite mxE.
under [leRHS]eq_bigr do rewrite mxE.
move: (svd_fR_prodM A B r.+1).
rewrite (big_ord_widen _ _ (ltn_ord r)).
rewrite (big_ord_widen _ (fun i => svd_fR A i * svd_fR B i) (ltn_ord r)).
by under [leLHS]eq_bigl do rewrite ltnS.
Qed.

Theorem svd_fR_sumM m n p (A : 'M[C]_(m,n)) (B : 'M[C]_(n,p)) k :
  \sum_(i < k) svd_fR (A *m B) i <= \sum_(i < k) (svd_fR A i * svd_fR B i).
Proof.
move: (weak_majorize_svd_fR A B (k := k))=>/weak_majorize_sum.
under [leLHS]eq_bigr do rewrite mxE.
by under [leRHS]eq_bigr do rewrite mxE.
Qed.

Theorem svd_f_sumM m n p (A : 'M[C]_(m,n)) (B : 'M[C]_(n,p)) k :
  \sum_(i < k) svd_f (A *m B) i <= \sum_(i < k) (svd_f A i * svd_f B i).
Proof.
move: (svd_fR_sumM A B k); rewrite !svd_fE/=.
under [X in _ -> _ <= X]eq_bigr do rewrite -realcM.
by rewrite -!realc_sum lecR.
Qed.

Theorem svd_fR_powM m n p (A : 'M[C]_(m,n)) (B : 'M[C]_(n,p)) (r : R) k :
  1 <= r -> \sum_(i < k) (svd_fR (A *m B) i) `^ r 
         <= \sum_(i < k) (svd_fR A i * svd_fR B i) `^ r.
Proof.
move=>Pr; move: (weak_majorize_svd_fR A B (k := k))=>/(powR_weak_majorize Pr).
set x := \row__ _; set y := \row__ _.
have Px i : 0 <= x 0 i by rewrite mxE.
have Py i : 0 <= y 0 i by rewrite mxE mulr_ge0.
move=>/(_ Px Py)/weak_majorize_sum; apply/le_le_trans.
all: by apply/ler_sum=>/= i _; rewrite !mxE.
Qed.

Theorem svd_fR_fM m n p (A : 'M[C]_(m,n)) (B : 'M[C]_(n,p)) (f : R -> R) :
  convex_fun (f \o expR) `]-oo,+oo[ -> 
    {in Num.nneg &, nondecreasing_fun f} ->
    forall k, \sum_(i < k) f (svd_fR (A *m B) i)
           <= \sum_(i < k) f (svd_fR A i * svd_fR B i).
Proof.
move=>Pf1 Pf2 k.
wlog : k / (k <= \rank (A *m B))%N => [P1|].
  have [] := leqP k (\rank (A *m B)); first by apply P1.
  move=>/ltnW/subnKC=><-.
  rewrite !big_split_ord/= lerD//; first by apply/P1/leqnn.
  apply/ler_sum=>i _; apply/Pf2/(le_trans (y := 0)); rewrite ?nnegrE.
    1,3: by rewrite svd_fR_eq0// leq_addr.
  1,2: by rewrite mulr_ge0.
move=>Pk.
pose x := \row_(i < k) svd_fR (A *m B) i.
pose y := \row_(i < k) (svd_fR A i * svd_fR B i).
suff : \sum_i map_mx f x 0 i <= \sum_i map_mx f y 0 i.
  under eq_bigr do rewrite !mxE.
  by under [leRHS]eq_bigr do rewrite !mxE.
have Pk1 (j : 'I_k) :    \prod_(i < k | (i <= j)%N) x 0 i 
                      <= \prod_(i < k | (i <= j)%N) y 0 i.
  under eq_bigl do rewrite -ltnS.
  under eq_bigr do rewrite mxE.
  under [leRHS]eq_bigl do rewrite -ltnS.
  under [leRHS]eq_bigr do rewrite !mxE.
  rewrite -[leRHS](big_ord_widen _ (fun i => svd_fR A i * svd_fR B i))//.
  by rewrite -big_ord_widen//; apply svd_fR_prodM.
have Px i : 0 < x 0 i.
  by rewrite mxE svd_fR_gt0// (leq_trans (ltn_ord i)).
have Px1 : x \is rv_nonincreasing.
  by apply/rv_nonincreasingP=>i j Pij; rewrite !mxE svd_fR_nincr.
have Py1 : y \is rv_nonincreasing.
  by apply/rv_nonincreasingP=>i j Pij; rewrite !mxE ler_pM// svd_fR_nincr.
move: (prod_sum_weak_majorize_ln Px Px1 Py1 Pk1)=>[] Py P1.
apply/weak_majorize_sum/exp_ln_weak_majorize=>//.
by move=>a b Pab /=; rewrite Pf2// ?nnegrE ?expR_ge0// ler_expR.
Qed.

End svd_inequlity.