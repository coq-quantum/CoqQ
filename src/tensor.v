(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.

Require Import mcextra mcaextra notation prodvect mxpred hermitian.

(* -------------------------------------------------------------------- *)
(* Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex. *)
Import Order.TTheory GRing.Theory Num.Theory Num.Def. 

(************************************************************************)
(*                Tensor for a family of Hilbert space                  *)
(************************************************************************)

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
(* Local Open Scope complex_scope. *)
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Import VectorInternalTheory.

Local Notation C := hermitian.C.

(* --------------------------------------------------------------------- *)
Declare Scope ffun_scope.
Delimit Scope ffun_scope with F.
Bind Scope ffun_scope with finfun_of.

Notation "0"     := (@ffun_zero _ _) : ffun_scope.
Notation "1"     := (@ffun_one  _ _) : ffun_scope.
Notation "+%F"   := (@ffun_add  _ _) : ffun_scope.
Notation "*%F"   := (@ffun_mul  _ _) : ffun_scope.
Notation "f + g" := (ffun_add f g)   : ffun_scope.
Notation "f * g" := (ffun_mul f g)   : ffun_scope.
Local Open Scope ffun_scope.

HB.instance Definition _ (I : finType) (G : nmodType) := 
  @Monoid.isComLaw.Build {ffun I -> G} 0 +%F (@addrA _) (@addrC _) (@add0r _).

HB.instance Definition _ (I : finType) (R : semiRingType) :=
  @Monoid.isLaw.Build {ffun I -> R} 1 *%F (@ffun_mulA _ _) (@ffun_mul_1l _ _) (@ffun_mul_1r _ _).
HB.instance Definition _ (I : finType) (R : comRingType) :=
  @SemiGroup.isCommutativeLaw.Build {ffun I -> R} *%F (@ffun_mulC _ _).

HB.instance Definition _ (I : finType) (R : semiRingType) :=
  @Monoid.isMulLaw.Build {ffun I -> R} 0 *%F (@ffun_mul_0l _ _) (@ffun_mul_0r _ _).

HB.instance Definition _ (I : finType) (R : semiRingType) :=
  @Monoid.isAddLaw.Build {ffun I -> R} *%F +%F (@ffun_mul_addl _ _) (@ffun_mul_addr _ _).

(* -------------------------------------------------------------------- *)
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%F/0%F]_(i <- r | P%B) F%F) : ffun_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%F/0%F]_(i <- r) F%F) : ffun_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%F/0%F]_(m <= i < n | P%B) F%F) : ffun_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%F/0%F]_(m <= i < n) F%F) : ffun_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%F/0%F]_(i | P%B) F%F) : ffun_scope.
Notation "\sum_ i F" :=
  (\big[+%F/0%F]_i F%F) : ffun_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%F/0%F]_(i : t | P%B) F%F) (only parsing) : ffun_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%F/0%F]_(i : t) F%F) (only parsing) : ffun_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%F/0%F]_(i < n | P%B) F%F) : ffun_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%F/0%F]_(i < n) F%F) : ffun_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%F/0%F]_(i in A | P%B) F%F) : ffun_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%F/0%F]_(i in A) F%F) : ffun_scope.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%F/1%F]_(i <- r | P%B) F%F) : ffun_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%F/1%F]_(i <- r) F%F) : ffun_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%F/1%F]_(m <= i < n | P%B) F%F) : ffun_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%F/1%F]_(m <= i < n) F%F) : ffun_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%F/1%F]_(i | P%B) F%F) : ffun_scope.
Notation "\prod_ i F" :=
  (\big[*%F/1%F]_i F%F) : ffun_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%F/1%F]_(i : t | P%B) F%F) (only parsing) : ffun_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%F/1%F]_(i : t) F%F) (only parsing) : ffun_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%F/1%F]_(i < n | P%B) F%F) : ffun_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%F/1%F]_(i < n) F%F) : ffun_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%F/1%F]_(i in A | P%B) F%F) : ffun_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%F/1%F]_(i in A) F%F) : ffun_scope.

Local Close Scope ffun_scope.

(* -------------------------------------------------------------------- *)
Section FfunBig.
Context  {I J : finType}.

Lemma ffun_sumE
    (G : zmodType) (r : seq I) (P : pred I) (F : I -> {ffun J -> G}) j
  : (\sum_(i <- r | P i) (F i))%F j = \sum_(i <- r | P i) F i j.
Proof.
apply: (big_morph (fun f : {ffun J -> G} => f j)).
- by move=> f g; rewrite ffunE. - by rewrite ffunE.
Qed.

Lemma ffun_prodE
    (R : ringType) (r : seq I) (P : pred I) (F : I -> {ffun J -> R}) j
  : (\prod_(i <- r | P i) (F i))%F j = \prod_(i <- r | P i) F i j.
Proof.
apply: (big_morph (fun f : {ffun J -> R} => f j)).
- by move=> f g; rewrite ffunE. - by rewrite ffunE.
Qed.
End FfunBig.

Section FFunSet.
Context {I : finType} (E : I -> Type).

Implicit Types (f : {ffun forall i : I, E i}).

Definition ffun_set (i0 : I) (v : E i0) f :=
  [ffun i => if i0 =P i is ReflectT eq then ecast k (E k) eq v else f i].

Lemma ffset_eq (i : I) (v : E i) f : @ffun_set i v f i = v.
Proof. by rewrite ffunE; case: eqP => // p; rewrite eq_axiomK. Qed.

Lemma ffset_neq (i j : I) (v : E i) f : i != j -> @ffun_set i v f j = f j.
Proof. by move=> /eqP ne_ij; rewrite ffunE; case: (i =P j). Qed.
End FFunSet.

Local Notation "f .[ i0 <- v ]" := (@ffun_set _ _ i0 v f) 
  (at level 2, left associativity, format "f .[ i0  <-  v ]").

Definition ffunE := (@ffset_eq, ffunE, @ffun_sumE, @ffun_prodE).

Lemma mv_neqP (I : finType) (E : I -> eqType) (f g : mvector E) :
  reflect (exists i, f i != g i) (f != g).
Proof. exact: dffun_neqP. Qed.

(* ==================================================================== *)
Section TensorProducts.
Context {I : finType} {k : fieldType} (E : I -> vectType k).

Implicit Types (G : vectType k).

Let B := mvector (fun i => 'I_(dim (E i))).
Let T := {ffun B -> k^o}.

Lemma dim_ffunr : dim T = #|B|.
Proof. by rewrite /dim /= /dim /= muln1. Qed. 

Definition i2n (i : B) : 'I_(dim T)
  := (cast_ord (esym dim_ffunr) (enum_rank i)). 
Definition n2i i : B := enum_val (cast_ord (dim_ffunr) i).
Lemma i2nK : cancel i2n n2i.
Proof. by move=>i; rewrite /i2n /n2i cast_ordKV enum_rankK. Qed.
Lemma n2iK : cancel n2i i2n.
Proof. by move=>i; rewrite /i2n /n2i enum_valK cast_ordK. Qed.
Lemma i2n_inj : injective i2n.
Proof. exact (can_inj i2nK). Qed.
Lemma n2i_inj : injective n2i.
Proof. exact (can_inj n2iK). Qed.

Definition inject (x : mvector E) : T := 
  r2v (\row_i (\prod_j v2r (x j) 0 (n2i i j))).

Notation "'⊗' x" := (inject x) (at level 2, format "⊗ x").

Lemma inject_cpnt (x : mvector E) (b : B) :
  (v2r ⊗x 0 (i2n b)) = \prod_i v2r (x i) 0 (b i).
Proof. by rewrite /inject r2vK mxE i2nK. Qed.

Lemma idx_neq (i j: B) : i == j = false -> exists k, i k == j k = false.
Proof. by move=>/eqP/eqP/mv_neqP[m Pm]; exists m; apply/eqP/eqP. Qed.

Lemma inject_base (b : B) : ⊗(\mvector_(i : I) r2v (delta_mx 0 (b i)))
  = r2v (delta_mx 0 (i2n b)).
Proof.
rewrite /inject; apply f_equal; apply/matrixP=>i j; rewrite !mxE !ord1 eqxx /=.
rewrite -(can2_eq n2iK i2nK); case P: (n2i j == b).
by move/eqP: P=> ->; rewrite big1 //= => m _; rewrite mvE r2vK mxE !eqxx.
by move: (idx_neq P)=> H; destruct H; rewrite (bigD1 x) //= mvE r2vK mxE H mul0r.
Qed.

Lemma inject_baseV b : r2v (delta_mx 0 b) = 
  ⊗(\mvector_(i : I) r2v (delta_mx 0 (n2i b i))).
Proof. by rewrite inject_base n2iK. Qed.

Definition scalei (i : I) (a : k) (x : mvector E) : mvector E :=
  \mvector_(j : I) ((if i == j then a else 1) *: x j).

Notation "a *:_ i x" := (scalei i a x)
  (at level 50, i at level 2, format "a  *:_ i  x").

Lemma scale1i (i : I) (x : mvector E) : 1 *:_i x = x.
Proof. by apply/mvectorP=> j; rewrite mvE if_same scale1r. Qed.

Definition scalem (a : I -> k) (x : mvector E) : mvector E :=
  \mvector_(i : I) (a i *: x i).

Notation "a *:_m x" := (scalem a x)
  (at level 50, format "a  *:_m  x").

Lemma scalem1E (i : I) (a : k) (x : mvector E) :
  [ffun j => if i == j then a else 1] *:_m x = a *:_i x.
Proof. by apply/mvectorP=> j; rewrite !(mvE, ffunE). Qed.

Lemma scalem_eq (a b : I -> k) x : a =1 b -> a *:_m x = b *:_m x.
Proof. by move=> eq_ab; apply/mvectorP => i; rewrite !mvE eq_ab. Qed.

Lemma scale1m (x : mvector E) : 1%F *:_m x = x.
Proof. by apply/mvectorP=> i; rewrite !(mvE, ffunE) scale1r. Qed.

Lemma scalemA (a b : {ffun I -> k}) (x : mvector E) :
  a *:_m (b *:_m x) = (a * b)%F *:_m x.
Proof. by apply/mvectorP=> i; rewrite !(mvE, ffunE); rewrite scalerA. Qed.

Definition mset (i : I) (x : mvector E) (v : E i) : mvector E :=
  \mvector_(j : I)
    if i =P j is ReflectT eq return E j then
      ecast k (E k) eq v
    else x j.

Notation "x [< i ← v >]" := (@mset i x v)
  (at level 2, left associativity, format "x [< i  ←  v >]").

Lemma msetii (i : I) (x : mvector E) (v : E i) :
  x[< i ← v >] i = v.
Proof. by rewrite mvE; case: eqP => // p; rewrite eq_axiomK. Qed.

Lemma mset_same (i : I) (x : mvector E) v :
  x i = v -> x[< i ← v >] = x.
Proof.
move=> {v}<-; apply/mvectorP=> j; rewrite mvE.
by case: eqP => //; case: j /.
Qed.

Lemma mset_eq (i j : I) (x : mvector E) (v : E i) (p : i = j) :
  x[< i ← v >] j = ecast z (E z) p v.
Proof.
rewrite mvE; case: eqP => //; case: _ / p => p.
by rewrite eq_axiomK.
Qed.

Lemma mset_ne (i j : I) (x : mvector E) (v : E i) :
  i != j -> x[< i ← v >] j = x j.
Proof.
move=> ne_ij; rewrite mvE; case: eqP=> // p.
by apply/contraNeq: ne_ij => _; apply/eqP.
Qed.

Notation "x +_ i v" := (x + 0[< i ← v >])
  (at level 60, i at level 2, format "x  +_ i  v").

Lemma addi0 x i : x +_i 0 = x.
Proof. by rewrite mset_same ?mvE // addr0. Qed.

Lemma addiE_ne (x : mvector E) i (v : E i) j : i <> j -> (x +_i v) j = x j.
Proof.
by move=> ne_ij; rewrite !mvE; case: eqP ne_ij => // _ _; rewrite addr0.
Qed.

Lemma addiE_eq (x : mvector E) i (v : E i) : (x +_i v) i = x i + v.
Proof. by rewrite !mvE; case: eqP => // p; rewrite eq_axiomK. Qed.

Definition mxlinear {G} (c : {rmorphism k -> k}) (f : mvector E -> G) :=
  forall i a x v, f (a *:_i x +_i v) = (c a) *: f x + f (x[<i ← v>]).

Definition mlinear {G} (f : mvector E -> G) :=
  @mxlinear G (GRing.RMorphism.clone _ _ idfun _) f.

Lemma eq_mxlinear {G} (c : {rmorphism k -> k}) (f g : mvector E -> G) :
  f =1 g -> mxlinear c f -> mxlinear c g.
Proof. by move=> eq_fg lin_f i a x v; rewrite -!eq_fg; apply: lin_f. Qed.

Lemma mxlinear0 {G} c (f : _ -> G) (x : mvector E) :
  mxlinear c f -> (exists i, x i = 0) -> f x = 0.
Proof.
move=> + [i xi_eq0] => /(_ i 1 x 0); rewrite rmorph1 scale1r.
rewrite addi0 mset_same // scale1i => /eqP.
by rewrite -subr_eq subrr => /eqP <-.
Qed.

Lemma mlinear0 {G} (f : _ -> G) (x : mvector E) :
  mlinear f -> (exists i, x i = 0) -> f x = 0.
Proof. by apply: mxlinear0. Qed.

Lemma mxlinearZ {G} c (f : _ -> G) i a (x : mvector E) :
  mxlinear c f -> f (a *:_i x) = c a *: f x.
Proof.
move=> /[dup] lin_f /(_ i a x 0); rewrite addi0.
rewrite [X in _+X](mxlinear0 lin_f) ?addr0 //.
by exists i; rewrite msetii.
Qed.

Lemma mlinearZ {G} (f : _ -> G) i a (x : mvector E) :
  mlinear f -> f (a *:_i x) = a *: f x.
Proof. by apply: mxlinearZ. Qed.

Lemma mxlinearD {G} c (f : _ -> G) i (x : mvector E) (v : E i) :
  mxlinear c f -> f (x +_i v) = f x + f x[<i ← v>].
Proof. by move=> /(_ i 1 x v); rewrite rmorph1 scale1i scale1r. Qed.

Lemma mlinearD {G} (f : _ -> G) i (x : mvector E) (v : E i) :
  mlinear f -> f (x +_i v) = f x + f x[<i ← v>].
Proof. apply: mxlinearD. Qed.

Lemma mxlinear_sum_ord
    {G} c a (x : forall {i : I}, 'I_(a i) -> E i) (f : _ -> G)
  : mxlinear c f -> f (\mvector_(i : I) \sum_(j < a i) x j) =
      \sum_(b : mvector (fun i : I => 'I_(a i))) f (\mvector_(i : I) x (b i)).
Proof.
move=> lin_f; pose w (a : I -> nat) := (\sum_i a i)%N.
have h0 (a' : I -> nat) (x' : forall i : I, 'I_(a' i) -> E i) :
     (forall i, (a' i <= 1)%N)
  -> f (\mvector_(i : I) \sum_(j < a' i) x' _ j) =
       \sum_(b : mvector (fun i : I => 'I_(a' i))) f (\mvector_(i : I) x' _ (b i)).
- move=> le1; case/boolP: [forall i, a' i == 1%N]; last first.
  - rewrite negb_forall => /existsP[] i neq1_a'i; move: (le1 i).
    rewrite leq_eqVlt (negbTE neq1_a'i) /= ltnS leqn0 => /eqP z_a'i.
    rewrite (mxlinear0 lin_f); first exists i.
    - by rewrite mvE big_pred0 //; case=> ?; rewrite z_a'i.
    rewrite big1 //= => b _; absurd false => //.
    by case: (b i)=> ?; rewrite z_a'i.
  - move/forallP=> eq1_a'; have gt0_a' i: (0 < a' i)%N.
    - by rewrite (eqP (eq1_a' _)).
    rewrite [X in f X = _](_ : _ = \mvector_(i : I) x' i (Ordinal (gt0_a' i))).
    - apply/mvectorP=> i; rewrite !mvE (big_pred1 (Ordinal (gt0_a' i))) //.
      case=> m lt; apply/esym/eqP/val_inj => /=.
      by move: lt; rewrite (eqP (eq1_a' _)); rewrite ltnS leqn0 => /eqP.
    pose b0 := \mvector_(i : I) (Ordinal (gt0_a' i)).
    rewrite (big_pred1 b0); last first.
    - by congr (f _); apply/mvectorP=> i; rewrite !mvE.
    case=> b; apply/esym/eqP/mvectorP=> i; apply/val_inj => /=.
    rewrite /b0 mvE /= /fun_of_mvector /=; case: (b i) => m /=.
    by rewrite (eqP (eq1_a' _)) ltnS leqn0 => /eqP.
move: {2}(w a) (leqnn (w a)) x => n; elim: n a => [|n ih] a.
- rewrite leqn0 => /eqP z_wa m; apply: h0.
  move=> i; move/eqP: z_wa; rewrite /w sum_nat_eq0.
  by move/'forall_implyP => /(_ i (erefl true)) /eqP ->.
case/boolP: [forall i, (a i <= 1)%N].
- by move/forallP=> ? _ ?; apply: h0.
rewrite negb_forall => /existsP[] i0; rewrite -ltnNge => gt1_ai0.
have gt0_ai0: (0 < a i0)%N by apply: (@leq_ltn_trans 1%N).
pose a' (i : I) := if i == i0 then (a i0).-1 else a i.
move=> bd_wa; have bd_wa': (w a' <= n)%N.
- rewrite /w (bigD1 i0) //= (eq_bigr a).
  - by move=> i ne_i_i0; rewrite /a' (negbTE ne_i_i0).
  rewrite /a' eqxx; rewrite -(leq_add2r 1%N) !addn1 -addSn.
  rewrite (ltn_predK gt0_ai0) -(bigD1 _ (P := predT)) //=.
move=> m; set v := (X in f X).
have le_a'_a i : (a' i <= a i)%N.
- by rewrite /a'; case: eqP => // <-; rewrite leq_pred.
have [mx mxval]: exists mx : 'I_(a i0), val mx = (a i0).-1.
- by case: (a i0) gt0_ai0 => //= i0' _; exists ord_max.
have ->: v =
  \mvector_ (i : I) (\sum_(j < a' i) m i (widen_ord (le_a'_a i) j))
    +_i0 m i0 mx.
- apply/mvectorP => i; case: (i =P i0) => [->|]; last first.
  - move=> ne_i_i0; rewrite addiE_ne; first by move/esym.
    rewrite !mvE -(big_ord_narrow_cond (P := predT)) /=.
    rewrite [RHS]big_mkcond /=; apply: eq_bigr.
    move=> i' _; rewrite /a'; case: eqP=> // _.
    by rewrite ltn_ord.    
  - rewrite addiE_eq !mvE; have hle: ((a' i0).+1 <= a i0)%N.
    - by rewrite /a' eqxx prednK.
    transitivity (\sum_(j < (a' i0).+1) m i0 (widen_ord hle j)).
    - rewrite -(big_ord_narrow_cond (P := predT)) /=.
      rewrite [RHS]big_mkcond /=; apply: eq_bigr.
      by move=> i' _; rewrite /a' eqxx prednK // ltn_ord.
    rewrite big_ord_recr /=; congr (_ + _).
    - by apply: eq_bigr=> i' _; congr (m _ _); apply: val_inj.
    - by congr (m _ _); apply: val_inj => /=; rewrite mxval /a' eqxx.
rewrite (mxlinearD _ _ lin_f) ih //; apply/esym.
pose P (b : mvector (fun i : I => 'I_(a i))) := b i0 == mx.
rewrite (bigID P) /= addrC; congr (_ + _).
- pose h (b : mvector (fun i => 'I_(a' i))) : mvector (fun i => 'I_(a i)) :=
    \mvector_(i : I) (widen_ord (le_a'_a i) (b i)).
  rewrite (reindex h) /=; last first.
  - apply: congr_big => //.
    - move=> b; apply/negP; rewrite /P /h mvE => /eqP /(congr1 val) /=.
      rewrite mxval; case: (b i0) => /= ?.
      by rewrite /a' eqxx => /[swap] ->; rewrite ltnn.
    - by move=> b PNhi; congr (f _); apply/mvectorP=> i; rewrite !mvE.
  have eq: forall i, i0 <> i -> a i = a' i.
  - by move=> i /eqP ne; rewrite /a' eq_sym (negbTE ne).
  have hsplit: (a i0 = a' i0 + 1)%N.
  - by rewrite /a' eqxx addn1 (ltn_predK gt0_ai0).
  have gt0_a'i0: (0 < a' i0)%N.
  - by rewrite /a' eqxx -ltnS (ltn_predK gt0_ai0).
  pose hI (b : mvector (fun i => 'I_(a i))) : mvector (fun i => 'I_(a' i)) :=
    \mvector_(i : I) (
      match i0 =P i with
      | ReflectT heq =>
          match split (cast_ord hsplit (b i0)) with
          | inl v => cast_ord (f_equal a' heq) v : 'I_(a' i)
          | inr _ => cast_ord (f_equal a' heq) (Ordinal gt0_a'i0) : 'I_(a' i)
          end
      | ReflectF hne =>
          cast_ord (eq _ hne) (b i) : 'I_(a' i)
      end
    ).
  exists hI=> b; rewrite !inE.
  - move=> PNhb; apply/mvectorP=> i; move: PNhb.
    rewrite !mvE /P /h /hI; case: eqP=> //; last first.
    - by move=> ? _; apply/val_inj.
    move=> p; rewrite mvE -val_eqE /= => ne_bi0_mx.
    case: splitP; last first.
    - move=> k0 /= bi0E; apply/val_inj => /=.
      absurd false => //; apply/contra_neqT: ne_bi0_mx => _.
      by rewrite bi0E ord1 addn0 /a' eqxx -mxval.
    - move=> j /esym /= jE; apply/val_inj => /=.
      by rewrite jE; case: _ / p.
  - move=> PNb; apply/mvectorP=> i; move: PNb.
    rewrite !mvE /P /h /hI; case: eqP=> //; last first.
    - by move=> ? _; apply/val_inj.
    move=> p ne_bi0_mx; case: splitP; last first.
    - move=> k0 /= bi0E; apply/val_inj => /=.
      absurd false => //; apply/contra_neqT: ne_bi0_mx => _.
      apply/val_inj=> /=; rewrite bi0E ord1 addn0.
      by rewrite /a' eqxx -mxval.
    move=> j /= jE; apply/val_inj => /=.
    by rewrite -jE; case: _ / p.
- pose a1 (i : I) := if i == i0 then 1%N else a i.
  have le_a1_a i : (a1 i <= a i)%N.
  - by rewrite /a1; case: eqP => // ->.
  pose F (i : I) (j : 'I_(a1 i)) :=
    if i0 =P i is ReflectT heq then
      ecast z (E z) heq (m i0 mx)
    else m i (widen_ord (le_a1_a i) j).
  rewrite [X in f X](_ : _ = \mvector_(i : I) \sum_(j < a1 i) (F i j)).
  - apply/mvectorP=> i; rewrite [RHS]mvE /F.
    case: eqP=> // [eq_i0_i|/eqP ne_i0_i].
    - rewrite mset_eq; have lt: (0 < a1 i)%N by rewrite /a1 eq_i0_i eqxx.
      rewrite (big_pred1 (Ordinal lt)) //; case=> l /= lt'.
      apply/esym/eqP/val_inj=> /=; move: lt'.
      by rewrite /a1 eq_i0_i eqxx ltnS leqn0 => /eqP.
    - rewrite mset_ne ?mvE //.
      rewrite -[LHS](big_ord_narrow_cond (P := predT)) /=.
      rewrite -[RHS](big_ord_narrow_cond (P := predT)) /=.
      rewrite [LHS]big_mkcond [RHS]big_mkcond //=.
      apply: eq_bigr=> i1 _; rewrite /a' /a1.
      by rewrite [i == _]eq_sym (negbTE ne_i0_i).
  rewrite ih; first apply: (leq_trans _ bd_wa').
  - rewrite /w; apply: leq_sum => i _; rewrite /a1 /a'.
    case: eqP => // _; rewrite -ltnS (ltn_predK gt0_ai0) //.
  have eq: forall i, i0 <> i -> a1 i = a i.
  - by move=> i /eqP ne; rewrite /a1 eq_sym (negbTE ne).
  pose h (b : mvector (fun i => 'I_(a1 i))) : mvector (fun i => 'I_(a i)) :=
    \mvector_(i : I) (
        match i0 =P i with
        | ReflectT heq => cast_ord (f_equal a heq) mx : 'I_(a i)
        | ReflectF hne => cast_ord (eq i hne) (b i)
        end
    ).
  rewrite (reindex h) /=; last first.
  - apply/congr_big => //.
    - move=> b; rewrite /P /h mvE ; case: eqP=> // p.
      by rewrite cast_ord_id eqxx.
    - move=> b Phb; congr (f _); apply/mvectorP => i.
      rewrite !mvE /F; case: eqP=> // p.
      - by case: _  / p; rewrite cast_ord_id.
      - by congr (m _ _); apply/val_inj => /=.
  have gt0: (0 < a1 i0)%N by rewrite /a1 eqxx.
  pose hI (b : mvector (fun i => 'I_(a i))) : mvector (fun i => 'I_(a1 i)) :=
    \mvector_(i : I) (
        match i0 =P i with
        | ReflectT heq => cast_ord (f_equal a1 heq) (Ordinal gt0) : 'I_(a1 i)
        | ReflectF hne => cast_ord (esym (eq i hne)) (b i)
        end
    ).
  exists hI=> b; rewrite !inE.
  - move=> Phb; apply/mvectorP=> i; move: Phb.
    rewrite /P /h /hI; rewrite !mvE. case: eqP => // _ _.
    case: eqP => p; apply/val_inj => //=; rewrite -p.
    by case: (b i0)=> /= ?; rewrite /a1 eqxx ltnS leqn0 => /eqP.
  - move=> Pb; apply/mvectorP=> i; move: Pb.
    rewrite /P /h /hI; rewrite !mvE; case: eqP => // p.
    - by move/eqP=> <-; apply/val_inj => /=; rewrite p.
    - by move=> _; apply/val_inj.
Qed.

Lemma mxlinear_sum
    {G} c (a : I -> finType) (x : forall {i : I}, (a i) -> E i) (f : _ -> G)
  : mxlinear c f -> f (\mvector_(i : I) \sum_(j : a i) x j) =
      \sum_(b : mvector (fun i : I => a i)) f (\mvector_(i : I) x (b i)).
Proof.
move=>lin_f.
pose a' i := #|a i|.
pose x' i (j : 'I_#|a i|) := x i (enum_val j).
have Pxi i : \sum_j x i j = \sum_j x' i j.
  rewrite (reindex (@enum_rank _))/=.
    by exists enum_val=>j _; rewrite ?enum_rankK// enum_valK.
  by under [RHS]eq_bigr do rewrite /x' enum_rankK.
under eq_mv do rewrite Pxi.
rewrite (mxlinear_sum_ord _ lin_f).
pose h (b : mvector (fun i : I => (a i))) := \mvector_(i : I) enum_rank (b i).
rewrite (reindex h).
  exists (fun b : mvector (fun i : I => 'I_#|a i|) 
    => \mvector_(i : I) enum_val (b i))=>b _;
  by apply/mvectorP=>i; rewrite mvE /h mvE ?enum_rankK// enum_valK.
apply eq_bigr => i _; f_equal.
by apply/mvectorP=>j; rewrite !mvE /x' enum_rankK.
Qed.

Lemma mlinear_sum
    {G} (a : I -> finType) (x : forall {i : I}, (a i) -> E i) (f : _ -> G)
  : mlinear f -> f (\mvector_(i : I) \sum_(j : a i) x j) =
      \sum_(b : mvector (fun i : I => (a i))) f (\mvector_(i : I) x (b i)).
Proof. exact: mxlinear_sum. Qed.

Lemma injectZi (i : I) (a : k) (x : mvector E) : ⊗(a *:_i x) = a *: ⊗x.
Proof. 
rewrite /inject -linearZ /=; apply f_equal; apply/matrixP=>m n. 
rewrite !mxE !(bigD1 i (P := predT)) //= mulrA. congr (_ * _).
by rewrite mvE eqxx linearZ mxE.
by apply: eq_bigr=> j ne_ji; rewrite mvE eq_sym (negbTE ne_ji) scale1r.
Qed.

Lemma injectDi (i : I) (x : mvector E) (v : E i) :
  ⊗ (x +_i v) = ⊗ x + ⊗ (x[<i ← v>]).
Proof.
rewrite /inject -linearD /=; apply f_equal; apply/matrixP=>m n. 
rewrite !mxE !(bigD1 i (P := predT)) //=.
rewrite !(msetii, mvE) linearD /= mxE mulrDl; congr (_ * _ + _ * _);
  by apply/eq_bigr=> j ne_ji; rewrite !(mset_ne, mvE) 1?eq_sym // addr0.
Qed.

Lemma inject_is_mlinear : mlinear inject.
Proof.
move=> i a x v /=; rewrite injectDi injectZi; congr (_ + ⊗_).
by apply/mvectorP=> j; rewrite !mvE; case: eqP => //; rewrite scale1r.
Qed.

Lemma inject_eq0P (x : mvector E) :
  reflect (exists i, x i = 0) (⊗x == 0).
Proof. 
apply: (iffP eqP) => eq0; last first.
- by apply: mlinear0 => //; apply/inject_is_mlinear.
apply/'exists_eqP; apply/contra_eqT: eq0 => eq0.
have {}eq0: forall i, exists j, v2r (x i) 0 j != 0.
- move=> i; apply/existsP; rewrite -negb_forall.
  apply/contra: eq0 => /forallP /= eq0; apply/existsP.
  exists i; apply/eqP/v2r_inj; rewrite linear0.
  by apply/rowP=> j; rewrite mxE; apply/eqP/eq0.
pose e := \mvector_(i : I) (xchoose (eq0 i)).
rewrite /inject (can2_eq r2vK v2rK) linear0.
apply/eqP => /matrixP /(_ 0 (i2n e)) => /eqP; apply/negP.
rewrite !mxE i2nK; apply/prodf_neq0 => i _.
by rewrite mvE; apply/(xchooseP (eq0 i)).
Qed.

Lemma mxlinearZm {G} c (f : _ -> G) a x :
  mxlinear c f -> f (a *:_m x) = c (\prod_i a i) *: (f x).
Proof.
have: a =1 (\prod_(i : I) [ffun j => (if i == j then a i else 1)%R])%F.
- move=> i; rewrite ffunE (bigD1 i) //= !ffunE eqxx big1 ?mulr1 //=.
  by move=> j ne_ji; rewrite ffunE (negbTE ne_ji).
move=> eqa lin_f; rewrite (scalem_eq _ eqa).
elim/big_rec2: _ => [|i d b _ ih].
- by rewrite rmorph1 scale1r scale1m.
- by rewrite rmorphM -scalemA scalem1E (mxlinearZ _ _ _ lin_f) // ih scalerA.
Qed.

Lemma mlinearZm {G} (f : _ -> G) a x :
  mlinear f -> f (a *:_m x) = (\prod_i a i) *: (f x).
Proof. by apply: mxlinearZm. Qed.
End TensorProducts.

Arguments i2nK {I k E}.
Arguments n2iK {I k E}.
Arguments i2n_inj {I k E}.
Arguments n2i_inj {I k E}.

(* -------------------------------------------------------------------- *)
Local Notation "'⊗' x" := (inject x) (at level 2, format "⊗ x").

Notation "a *:_ i x" := (scalei i a x)
  (at level 50, i at level 2, format "a  *:_ i  x").

Notation "a *:_m x" := (scalem a x)
  (at level 50, format "a  *:_m  x").

Notation "x [< i ← v >]" := (mset (i := i) x v)
  (at level 2, left associativity, format "x [< i  ←  v >]").

Notation "x +_ i v" := (x + 0[< i ← v >])
  (at level 60, i at level 2, format "x  +_ i  v").

Section Lift.
Context {I : finType} {J : I -> finType} {k : fieldType}.
Context
  (c : {ffun I -> {rmorphism k -> k}}) (* twist on i-th argument *)
  (E : forall i : I, J i -> vectType k)(* tensor product for i-th argument *)
  (F : vectType k).                    (* codomain *)


Let B i := mvector (fun j : J i => 'I_(dim (@E i j))).
Let T i := {ffun (B i) -> k^o}.

Context (f : {ffun forall i : I, mvector (@E i)} -> F).

Hypothesis lin_f :
  forall (i : I) (m : {ffun forall i : I, mvector (@E i)}),
    mxlinear (c i) (fun x => f m.[i <- x]).

Definition lift_r (x : forall (i : I), T i) (b : forall (i : I), B i) :=
  (\prod_(i : I) c i (v2r (x i) 0 (i2n (b i))))
    *: (f [ffun i => \mvector_(j : J i) r2v (delta_mx 0 (b i j))]).

Definition lift (x : forall (i : I), T i) : F :=
  \sum_(b : {dffun forall i : I, B i}) lift_r x b.

Lemma setW (K : finType) (P : {set K} -> Prop) :
     P set0
  -> (forall (s : {set K}) (k : K), k \notin s -> P s -> P (k |: s))
  -> forall s, P s.
Proof.
move=> P0 PS s; move: {2} #|s| (erefl #|s|) => n; elim: n s.
- by move=> s; rewrite (rwP eqP) cards_eq0 => /eqP->.
move=> n ih s cds; have: (0 < #|s|)%N by rewrite cds.
case/card_gt0P=> x /[dup] x_in_s /setD1K <-; apply: PS.
- by rewrite in_setD1 eqxx.
apply: ih; move: cds; rewrite (cardsD1 x).
by rewrite x_in_s /= add1n => -[].
Qed.

Lemma mlinearZms a (x : {ffun forall i : I, mvector (@E i)}) :
  f [ffun i => a i *:_m x i] =
    \prod_(i : I) c i (\prod_(j : J i) a i j) *: f x.
Proof.
pose b (S : {set I}) i := if i \in S then a i else [ffun=> 1].
rewrite [X in f X = _](_ : _ = [ffun i => b [set: I] i *:_m x i]).
- by apply/ffunP=> i; rewrite !ffunE /b in_setT.
rewrite (eq_bigl (fun x => x \in [set: I])) /= => [i|].
- by rewrite in_setT.
elim/setW: [set: I] => [|s i i_notin_s ih].
- rewrite big_set0 scale1r; congr (f _); apply/ffunP.
  by move=> i; rewrite !ffunE /b in_set0 scale1m.
rewrite big_setU1 //= -scalerA -ih; set y := (X in f X = _).
have {y}->: y = [ffun j => b s j *:_m x j].[i <- a i *:_m x i].
- apply/ffunP=> j; case: (i =P j) => [ <-|/eqP ne_ij].
  - by rewrite !ffunE /b in_setU1 eqxx.
  by rewrite ffset_neq // !ffunE /b in_setU1 eq_sym (negbTE ne_ij).
rewrite (mxlinearZm _ _ (@lin_f i _)); congr (_ *: f _).
apply/ffunP=> j; case: (i =P j) => [ <-|/eqP ne_ij].
- by rewrite !ffunE /b (negbTE i_notin_s) scale1m.
- by rewrite ffset_neq.
Qed.

Lemma xliftE (x : {ffun forall i : I, mvector (@E i)}) :
  lift [ffun i => ⊗(x i)] = f x.
Proof.
pose a (b : forall i, B i) i j := v2r (x i j) 0 (b i j).
have fE b: lift_r [ffun i => ⊗(x i)] b =
  f [ffun i => \mvector_(j : J i) (a b i j *: r2v (delta_mx 0 (b i j)))].
- rewrite /lift_r (eq_bigr (fun i => c i (\prod_(j : J i) (v2r (x i j) 0 (b i j))))).
  - by move=> i _; rewrite ffunE inject_cpnt.
  rewrite -mlinearZms; congr (f _); apply/ffunP=> i.
  by rewrite !ffunE; apply/mvectorP=> j; rewrite !mvE.
rewrite /lift {fE}(eq_bigr _ (fun (b : {ffun forall i, B i}) _ => fE b)).
pose P (m : forall i, option (B i)) (b : {ffun forall i, B i}) :=
  [forall i : I, if m i is Some v then b i == v else true].
pose y (m : forall i, option (B i)) :=
  [ffun i : I => if m i is Some b then
       \mvector_(j : J i) (v2r (x i j) 0 (b j) *: r2v (delta_mx 0 (b j)))
     else x i].
pose supp (p : {ffun forall i : I, option (B i)}) := [set i | p i != None].
pose p0 := [ffun i : I => (None : option (B i))].
rewrite (eq_bigl (P p0)).
- by move=> b; apply/esym/forallP => i; rewrite ffunE.
rewrite [in RHS](_ : x = y p0).
- by apply/ffunP=> i; rewrite !ffunE.
have: supp p0 = setT :\: setT.
- by apply/setP=> i; rewrite !(inE, ffunE).
elim/setW: {2}[set: I] p0 => [|s i i_notin_s ih] p0.
- rewrite setD0 => /setP supp_p0.
   have h i: exists v : B i, p0 i == Some v.
  - move/(_ i): supp_p0; rewrite !inE; case: (p0 i) => //.
    by move=> v _; exists v.
  pose b : {dffun forall i : I, B i} := [ffun i => xchoose (h i)].
  have p0iE i: p0 i = Some (b i).
  - case p0iE: (p0 i) => [v|].
    - by rewrite /b ffunE -(eqP (xchooseP (h i))) p0iE.
    - by move/(_ i): supp_p0; rewrite !inE p0iE.
  rewrite (big_pred1 b) => /= [zc|].
  - rewrite /P -(@eq_forallb _ (fun i => zc i == b i)).
    - by move=> i /=; rewrite p0iE.
    by rewrite inE; apply/'forall_eqP/eqP=> [/ffunP|->].
  congr (f _); apply/ffunP=> i; rewrite !ffunE.
  rewrite [in RHS]p0iE; apply/mvectorP=> j; rewrite !mvE.
  by congr (_ *: _); rewrite !ffunE.
move=> p0E; pose R (b : {dffun forall i, B i}) := b i.
rewrite (partition_big R predT) {}/R //=.
pose q0 j := p0.[i <- Some j].
have q0s j: supp (q0 j) = [set: I] :\: s.
- apply/setP=> i'; rewrite [in LHS]inE.
  case: (i =P i') => [ <-|/eqP ne_ii'].
  - by rewrite ffset_eq !inE i_notin_s.
  rewrite ffset_neq //; move/setP/(_ i'): p0E.
  by rewrite !inE [i' == i]eq_sym (negbTE ne_ii') andbT.
have ->: f (y p0) = \sum_j f (y (q0 j)).
- have h (b : B i): y (q0 b) = (y p0).[i <-
    \mvector_ (j : J i) (v2r (x i j) 0 (b j) *: r2v (delta_mx 0 (b j)))].
  - apply/ffunP=> i'; case: (i =P i') => [ <-|/eqP ne_ii'].
    - by rewrite !ffunE.
    - by rewrite ffset_neq // ffunE ffset_neq // !ffunE.
  rewrite (eq_bigr _ (fun (b : B i) _ => congr1 f (h b))).
  pose z j b := v2r (x i j) 0 b *: r2v (delta_mx 0 b).
  rewrite -(mxlinear_sum z (@lin_f i (y p0))); congr (f _).
  apply/ffunP=> i'; case: (i =P i') => [ <-|/eqP ne_ii'];
    last by rewrite ffset_neq.
  rewrite ffset_eq; move/setP/(_ i): p0E.
  rewrite ffunE !inE eqxx /= => /negbFE /eqP ->.
  apply/mvectorP=> j; rewrite mvE; apply/v2r_inj.
  apply/rowP=> /= b; rewrite linear_sum summxE (bigD1 b) //= big1.
  - move=> l ne_lj; rewrite linearZ mxE /= r2vK mxE.
  by rewrite [b == l]eq_sym (negbTE ne_lj) andbF mulr0.
  - by rewrite linearZ mxE /= r2vK mxE !eqxx andbT mulr1 addr0.  
apply: eq_bigr=> j _; rewrite -ih //; apply: eq_bigl.
- move=> b; apply/idP/idP.
  - case/andP=> h /eqP biE; apply/forallP => i'.
    case: (i =P i') => [ <-|/eqP ne_ii'].
    - by rewrite ffset_eq biE.
    by rewrite ffset_neq //; move/forallP/(_ i'): h.
move/forallP=> /[dup] /(_ i); rewrite ffset_eq andbC => -> /=.
move=> h; apply/forallP => i'; case: (i =P i') => [ <-|/eqP ne_ii'].
- by move/setP/(_ i): p0E; rewrite !inE eqxx andbT /= => /negbFE /eqP->.
- by move/(_ i'): h; rewrite ffset_neq.
Qed.

Lemma xlinear_lift  i a m (x y : {ffun B i -> k^o}) :
  lift m.[i <- a *: x + y] = (c i a) *: lift m.[i <- x] + lift m.[i <- y].
Proof.
rewrite /lift; rewrite scaler_sumr -big_split /=.
apply: eq_bigr=> /= b _; rewrite /lift_r /=.
set m' := (X in f X); have lf := @lin_f i m'.
rewrite scalerA -scalerDl !(bigD1 (P := predT) i) //=.
pose X := \prod_(i' | i' != i) c i' (v2r (m i') 0 (i2n (b i'))).
have h z: \prod_(i' | i' != i) c i' (v2r (m.[i <- z] i') 0 (i2n (b i'))) = X.
- by apply: eq_bigr=> i' ne_i'i; rewrite ffset_neq // eq_sym.
rewrite !{}h ![_ * X]mulrC mulrCA -mulrDr -!scalerA; congr (_ *: _).
by rewrite !ffset_eq linearP /= !mxE rmorphD rmorphM.
Qed.
End Lift.

(* -------------------------------------------------------------------- *)
Section BiSemiLinear.
Context {I : finType} {k : fieldType}.
Context (c1 c2 : {rmorphism k -> k}) (E : I -> vectType k).
Context (F : vectType k).

Let B := mvector (fun i : I => 'I_(dim (E i))).
Let T := {ffun B -> k^o}.

Context (f : mvector E -> mvector E -> F).

Hypothesis (lin1_f : forall y, mxlinear c1 (f^~ y)).
Hypothesis (lin2_f : forall x, mxlinear c2 (f   x)).

Let cT : {ffun bool -> {rmorphism k -> k}} :=
  [ffun b => if b then c1 else c2].

Let aT {T : Type} (x y : T) : {ffun bool -> T} :=
  [ffun b => if b then x else y].

Let fT (x : {ffun bool -> mvector E}) :=
  f (x true) (x false).

Definition lift2 (x y : T) : F := lift cT fT (aT x y).

Lemma mxlinear2 b m : mxlinear (cT b) (fun v => fT m.[b <- v]).
Proof.
case: b => /=; rewrite !ffunE => i.
- apply/(eq_mxlinear (f := f^~ (m false)))/lin1_f.
  by move=> b; rewrite /fT ffset_eq ffset_neq.
- apply/(eq_mxlinear (f := f (m true)))/lin2_f.
  by move=> b; rewrite /fT ffset_eq ffset_neq.
Qed.

Lemma xlift2E (x y : mvector E) : lift2 ⊗x ⊗y = f x y.
Proof.
rewrite /lift2; have ->: aT ⊗x ⊗y = [ffun b => ⊗(aT x y b)].
- by apply/ffunP; case; rewrite !ffunE.
by rewrite xliftE /=; [apply: mxlinear2 | rewrite /fT !ffunE].
Qed.

Lemma xlift2_mxlinear1 a (x1 x2 y : T) :
  lift2 (a *: x1 + x2) y = c1 a *: lift2 x1 y + lift2 x2 y.
Proof.
have h x: lift2 x y = lift cT fT [ffun=> y].[true <- x].
- congr (lift _ _ (fun_of_fin _)); apply/ffunP=> /=.
  move=> b; rewrite ffunE; case: b.
  - by rewrite ffset_eq. - by rewrite ffset_neq // ffunE.
by rewrite h xlinear_lift /=; [apply: mxlinear2 | rewrite -!h ffunE].
Qed.

Lemma xlift2_mxlinear2 a (x y1 y2 : T) :
  lift2 x (a *: y1 + y2) = c2 a *: lift2 x y1 + lift2 x y2.
Proof.
have h y: lift2 x y = lift cT fT [ffun=> x].[false <- y].
- congr (lift _ _ (fun_of_fin _)); apply/ffunP=> /=.
  move=> b; rewrite ffunE; case: b.
  - by rewrite ffset_neq // ffunE. - by rewrite ffset_eq.
by rewrite h xlinear_lift /=; [apply: mxlinear2 | rewrite -!h ffunE].
Qed.
End BiSemiLinear.

(* -------------------------------------------------------------------- *)
Section SesqLinear.
Context {C : numClosedFieldType} {I : finType} (E : I -> vectType C) (F : vectType C).

Context (f : mvector E -> mvector E -> F).

Let B := mvector (fun i : I => 'I_(dim (E i))).
Let T := {ffun B -> C^o}.

Hypothesis (lin1_f : forall y, mxlinear Num.conj_op (f^~ y)).
Hypothesis (lin2_f : forall x, mlinear (f x)).

Definition lifts (x y : T) : F :=
  lift2 Num.conj_op (GRing.RMorphism.clone _ _ idfun _) f x y.

Lemma xliftsE (x y : mvector E) : lifts ⊗x ⊗y = f x y.
Proof. by apply: xlift2E. Qed.

Lemma xlifts_alinear a (x1 x2 y : T) :
  lifts (a *: x1 + x2) y = a^* *: (lifts x1 y) + lifts x2 y.
Proof. by apply: xlift2_mxlinear1. Qed.

Lemma xlifts_linear (x : T) : linear (lifts x).
Proof. by move=> a y1 y2; apply: xlift2_mxlinear2. Qed.
End SesqLinear.

(* -------------------------------------------------------------------- *)
Section Linear.
Context {I : finType} {k : fieldType}.
Context (E : I -> vectType k) (F : vectType k).

Context (f : mvector E -> F).

Let B := mvector (fun i : I => 'I_(dim (E i))).
Let T := {ffun B -> k^o}.

Hypothesis (lin_f : mlinear f).

Let cT : {ffun unit -> {rmorphism k -> k}} :=
  [ffun=> (GRing.RMorphism.clone _ _ idfun _)].

Let aT {T : Type} (x : T) : {ffun unit -> T} :=
  [ffun=> x].

Let fT (x : {ffun unit -> mvector E}) :=
  f (x tt).

Definition lift1 (x : T) : F :=
  lift cT fT (aT x).

Lemma mxlinear1 b m : mxlinear (cT b) (fun v => fT m.[b <- v]).
Proof.
case: b; rewrite !ffunE /=.
apply/(eq_mxlinear (f := f))/lin_f.
by move=> b; rewrite /fT ffset_eq.
Qed.

Lemma xlift1E (x : mvector E) : lift1 ⊗x = f x.
Proof.
rewrite /lift1; have ->: aT ⊗x = [ffun b=> ⊗(aT x b)].
- by apply/ffunP; case; rewrite !ffunE.
by rewrite xliftE /=; [apply: mxlinear1 | rewrite /fT !ffunE].
Qed.

Lemma xlift1_linear : linear lift1.
Proof.
move=> /= a u v; have h x: lift1 x = lift cT fT [ffun=> 0].[tt <- x].
- by congr (lift _ _ (fun_of_fin _)); apply/ffunP=> /= -[]; rewrite !ffunE.
by rewrite h xlinear_lift /=; [apply: mxlinear1 | rewrite -!h ffunE].
Qed.
End Linear.

(* -------------------------------------------------------------------- *)
Section HermitianTensorProducts.
Context {I : finType} (E : I -> hermitianType).

Let B := mvector (fun i => 'I_(dim (E i))).
Let T := {ffun B -> C^o}.

Definition hdotp (x y : mvector E) : C^o :=
  \prod_(i : I) [< x i; y i >].

Definition tdotp (x y : T) : C :=
  lifts hdotp x y.

Lemma ge0_hdotp (x : mvector E) : 0 <= hdotp x x.
Proof. by apply: prodr_ge0 => i _; apply/ge0_dotp. Qed.

Lemma hdotp_eq0 (x : mvector E) : (hdotp x x == 0) = (⊗x == 0).
Proof.
apply/prodf_eq0/inject_eq0P.
- by case=> i _; rewrite dotp_eq0 => /eqP eq0_xi; exists i.
- by case=> i eq0_xi; exists i => //; rewrite dotp_eq0 -(rwP eqP).
Qed.

Lemma conj_hdotp x y : (hdotp x y)^* = hdotp y x.
Proof. by rewrite rmorph_prod; apply/eq_bigr=> i _; rewrite conj_dotp. Qed.

Lemma linear_hdotp x : mlinear (G := [vectType C of C^o]) (hdotp x).
Proof.
move=> /= i a y z; rewrite {1}/hdotp (bigD1 i) //= !(msetii, mvE).
rewrite eqxx dotpDr dotpZr mulrDl -mulrA; congr (_ *: _ + _).
- rewrite /hdotp [in RHS](bigD1 i) //=; congr (_ * _).
  apply: eq_bigr=> j ne_ji; rewrite mvE mset_ne 1?eq_sym //.
  by rewrite !mvE eq_sym (negbTE ne_ji) scale1r addr0.
- rewrite /hdotp [in RHS](bigD1 i) //= msetii; congr (_ * _).
  apply: eq_bigr=> j ne_ji; rewrite mvE !mset_ne 1?eq_sym //.
  by rewrite !mvE eq_sym (negbTE ne_ji) scale1r addr0.
Qed.

Lemma alinear_hdotp y :
  mxlinear (G := C^o) Num.conj_op (hdotp^~ y).
Proof.
move=> /= i a x1 x2; rewrite -conj_hdotp linear_hdotp /=.
by rewrite rmorphD/= rmorphM /= !conj_hdotp.
Qed.

Lemma tdotpE (x y : mvector E) :
  tdotp ⊗x ⊗ y = \prod_(i : I) [< x i; y i >].
Proof.
rewrite /tdotp xliftsE //;
  [by apply: alinear_hdotp | by apply: linear_hdotp].
Qed.

Lemma linear_tdotp x : linear_for *%R (tdotp x).
Proof.
by move=>a b c; rewrite /tdotp (xlifts_linear 
  alinear_hdotp linear_hdotp) /GRing.scale.
Qed.
Lemma linear_tdotpr x : linear_for (Num.conj_op \; *%R) (tdotp^~ x).
Proof.
by move=>a b c; rewrite /tdotp (xlifts_alinear 
  alinear_hdotp linear_hdotp) /GRing.scale.
Qed.

HB.instance Definition _ x := GRing.isLinear.Build C T C
  *%R (tdotp x) (linear_tdotp x).

HB.instance Definition _ := bilinear_isBilinear.Build C T T C
  (Num.conj_op \; *%R) *%R tdotp (linear_tdotpr, linear_tdotp).

Definition fbasis (b : B) := ⊗ (\mvector_(i : I) (vonbasis {:(E i)})~_ 
  (cast_ord (esym (dimvf (E i))) (b i))).

Lemma fbasis_ortho (b c : B) :
  tdotp (fbasis b) (fbasis c) = (b == c)%:R.
Proof.
rewrite /fbasis tdotpE. rewrite (eq_bigr (fun i => (b i == c i)%:R)).
move=>i _. rewrite !mvE. 
move: (vonbasisP {:(E i)})=>/andP [_ /'forall_'forall_eqP].
rewrite size_tuple=>P. by rewrite !(tnth_nth 0) P (inj_eq (@cast_ord_inj _ _ _)).
case E1: (b == c). move/eqP: E1=>->. rewrite big1// => i _. by rewrite eqxx.
move: (idx_neq E1)=> P2. apply/eqP/prodf_eq0.
destruct P2. exists x=>//. by rewrite H.
Qed.

Definition fbasis_seq := 
    [seq fbasis (n2i i) | i: 'I_(dim T)].
Lemma fbasis_size : size fbasis_seq == dim T.
Proof. by rewrite size_map size_enum_ord. Qed.
Definition fbase := nosimpl (Tuple fbasis_size).
Lemma fbasis_seqE (i: 'I_(dim T)) :
  fbase~_ i = fbasis (n2i i).
Proof.
  rewrite /fbase (tnth_nth 0)/= (nth_map i) ?size_enum_ord //. do 2 f_equal.
  apply ord_inj. destruct i=>/=. by apply nth_enum_ord.
Qed.

Lemma fbasis_basis : basis_of {: T} fbase.
Proof.
rewrite basisEfree. do 2 ? [apply/andP; split].
apply/freeP=> k H i.
have: tdotp (fbasis (n2i i)) 0 = 0 by rewrite linear0.
rewrite -H linear_sum (bigD1 i)// big1 =>[j /negPf nji|]; 
rewrite linearZ -tnth_nth/= fbasis_seqE fbasis_ortho (inj_eq (@n2i_inj _ _ E)).
by rewrite eq_sym nji mulr0. by rewrite eqxx addr0 mulr1.
by apply subvf. by rewrite size_tuple dimvf leqnn.
Qed.

Lemma fbasis_dec (x : T) :
  x = \sum_(b:B) coord fbase (i2n b) x *: fbasis b.
Proof.
rewrite (reindex (fun i => n2i i)). 
exists (@i2n _ _ E)=> [a _ | a _]; by rewrite ?n2iK ?i2nK.
rewrite [LHS](coord_basis fbasis_basis (memvf x)).
by apply eq_bigr=>i _; rewrite n2iK -tnth_nth fbasis_seqE.
Qed.

Lemma tdotp_sumlr (f g : B -> C) :
  tdotp (\sum_b f b *: fbasis b) (\sum_b g b *: fbasis b)
  = \sum_b (f b)^* * g b.
Proof.
rewrite linear_suml/=. apply eq_bigr=>b _.
rewrite linear_sum/= (bigD1 b)// big1/= =>[j /negPf nji |];
rewrite linearZl_LR linearZr/= fbasis_ortho 1 ?eq_sym ?nji ?mulr0//.
by rewrite eqxx mulr1 addr0.
Qed.

Lemma ge0_tdotp (x : T) : 0 <= tdotp x x.
Proof.
rewrite (fbasis_dec x) tdotp_sumlr. apply sumr_ge0=>i _.
by rewrite mulrC mul_conjC_ge0.
Qed.

Lemma tdotp_eq0 (x : T) : (tdotp x x == 0) = (x == 0).
Proof.
apply Bool.eq_true_iff_eq; split=>[/eqP | /eqP ->].
rewrite (fbasis_dec x) tdotp_sumlr=> P1.
have P2: forall (b: B), true -> 0 <= (coord fbase (i2n b) x)^* 
  * coord fbase (i2n b) x by move=>b _; rewrite mulrC mul_conjC_ge0.
move: (psumr_eq0P P2 P1) =>/=P3; rewrite big1/= ?eqxx// =>i _. 
have t : true by []; move/eqP: (P3 i t). 
by rewrite mulrC mul_conjC_eq0=>/eqP->; rewrite scale0r.
by rewrite linear0 eqxx.
Qed.

Lemma conj_tdotp (x y : T) : (tdotp x y)^* = tdotp y x.
Proof.
rewrite (fbasis_dec x) (fbasis_dec y) !tdotp_sumlr rmorph_sum.
by under eq_bigr do rewrite rmorphM conjCK mulrC.
Qed.

(* ? HB.instance fails here *)
Definition tensor_hermitianMixin := @Vector_isHermitianSpace.Build T tdotp
  ge0_tdotp tdotp_eq0 conj_tdotp linear_tdotp.
Canonical tensor_hermitianType := 
  HermitianSpace.Pack (HermitianSpace.Class tensor_hermitianMixin).

Lemma dim_tensor : (dim T = \prod_i dim (E i))%N.
Proof.
rewrite {1}/dim /= /dim /=.
rewrite muln1 card_mv card_dep_ffun foldrE big_map big_enum /=.
apply eq_bigr; by move=> i _; rewrite card_ord.
Qed.

End HermitianTensorProducts.

(* -------------------------------------------------------------------- *)
Section chsTensorProducts.
Context {I : finType} (E : I -> chsType).

Let B := mvector (fun i => 'I_(dim (E i))).
Let T := {ffun B -> C^o}.

Lemma tensor_chs_dim_proper : (1 <= (dim T))%N.
Proof.
rewrite {1}/dim /= /dim /=.
rewrite muln1 card_mv card_dep_ffun foldrE big_map big_enum /=.
apply prodn_gt0=> i. move: (@dim_proper (E i)).
by rewrite /dim /= card_ord.
Qed.

Definition tensor_chs_eb (i : 'I_(dim T)) : T
  := ⊗ (\mvector_(j : I) eb ((n2i i) j)).

Lemma tensor_chs_eb_dot i j : [<tensor_chs_eb i ; tensor_chs_eb j >] = (i == j)%:R.
Proof.
rewrite /tensor_chs_eb/dotp/= tdotpE -(can_eq n2iK).
case: eqP=>[->|/eqP/mv_neqP[m /negPf Pm]].
by rewrite big1// =>n _; rewrite mvE eb_dot eqxx.
by rewrite (bigD1 m)//= !mvE eb_dot Pm mul0r.
Qed.

(* ? HB.instance fails here *)
Definition tensor_chsMixin := @HermitianSpace_isCanonical.Build T tensor_chs_eb
  tensor_chs_eb_dot tensor_chs_dim_proper.
Canonical tensor_chsType := 
  CanonicalHermitianSpace.Pack (CanonicalHermitianSpace.Class tensor_chsMixin).

End chsTensorProducts.
