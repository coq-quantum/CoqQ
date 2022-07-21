From mathcomp Require Import all_ssreflect all_algebra perm complex.
From mathcomp.analysis Require Import reals.
From mathcomp.real_closed Require Import complex.

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import Vector.InternalTheory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope ring_scope.

Notation "x %:C" := (real_complex _ x)
  (at level 2, left associativity, format "x %:C") : ring_scope.
Notation "x %:VF" := (x : 'Hom(_,_)) 
  (at level 2, left associativity, format "x %:VF") : lfun_scope.
Notation "t ~_ i" := (tnth t i) (at level 3, i at level 2).


Section VecterInternalTheoryExtra.
Local Open Scope lfun_scope.

Lemma linearlfE (R : ringType) (U V : lmodType R) (f : U -> V) (lf: linear f) :
  f = Linear lf. Proof. by []. Qed.

Lemma can2_linearP (R : ringType) (U V : lmodType R) (f : U -> V) (f' : V -> U) :
  linear f -> cancel f f' -> cancel f' f -> linear f'.
Proof. move=>lf; rewrite (linearlfE lf); exact: can2_linear. Qed.

Lemma can2_bij (R : ringType) (U V : lmodType R) (f : U -> V) (f' : V -> U) :
  cancel f f' -> cancel f' f -> bijective f'.
Proof. by move=>fK f'K; exists f. Qed.

Lemma v2r_bij (R : ringType) (V : vectType R) : bijective (@v2r _ V).
Proof. exists (@r2v _ V). exact: v2rK. exact: r2vK. Qed.

Lemma r2v_bij (R : ringType) (V : vectType R) : bijective (@r2v _ V).
Proof. exists (@v2r _ V). exact: r2vK. exact: v2rK. Qed.

Lemma f2mxP (R : fieldType) (U V: vectType R) : linear (@f2mx _ U V).
Proof.
move=> a f g; have E: forall u, (a *: f + g) (r2v u) = a *: f (r2v u) + g (r2v u).
by move=> u; rewrite !lfunE /= !lfunE.
apply/eqP/mulmxP => u; move: (E u).
rewrite /fun_of_lfun unlock /= /fun_of_lfun_def /= !r2vK -linearP /=.
by rewrite -linearZ /= -mulmxDr; apply r2v_inj.
Qed.
Canonical f2mx_linear (R : fieldType) (U V: vectType R) := Linear (@f2mxP R U V).

Lemma vecthomP (R : fieldType) (U V: vectType R) : linear (@Vector.Hom _ U V).
Proof. by move=>c x y; apply/lfunP=>z; rewrite unlock/= !linearP. Qed.
Canonical vecthom_linear (R : fieldType) (U V: vectType R) := Linear (@vecthomP R U V).

Lemma f2mxK (R : fieldType) (U V : vectType R) : cancel (@f2mx _ U V) (Vector.Hom).
Proof. move=>x; by apply/val_inj. Qed.

Lemma vecthomK (R : fieldType) (U V : vectType R) : cancel (Vector.Hom) (@f2mx _ U V).
Proof. by move=>x. Qed.

Lemma f2mx_inj (R : fieldType) (U V: vectType R) : injective (@f2mx _ U V).
Proof. exact: (can_inj (@f2mxK _ _ _)). Qed.

Lemma vecthom_inj (R : fieldType) (U V: vectType R) : injective (@Vector.Hom _ U V).
Proof. exact: (can_inj (@vecthomK _ _ _)). Qed.

Lemma comp_f2mx (R : ringType) (H G K: vectType R) (f: 'Hom(H,G)) (g: 'Hom(K,H)) :
  f2mx (f \o g)%VF = f2mx g *m f2mx f.
Proof.
rewrite /comp_lfun /fun_of_lfun unlock /= /fun_of_lfun_def /= unlock.
apply/matrixP=> i j. rewrite /lin1_mx !mxE /comp !r2vK /mulmxr -mulmxA /mulmx mxE.
rewrite (bigD1 i) //= big1.
by move=>k /negPf P; rewrite /delta_mx !mxE P mul0r.
by rewrite /delta_mx !mxE !eqxx mul1r addr0.
Qed.

Lemma f2mx1 (R : ringType) (G: vectType R) : f2mx (\1%VF : 'End(G)) = 1%:M.
Proof. 
suff: (\1%VF : 'End(G)) = Vector.Hom 1%:M. by move/(f_equal f2mx).
apply/lfunP=>u; rewrite !lfunE/= /fun_of_lfun unlock /=.
by rewrite /fun_of_lfun_def /= mulmx1 v2rK.
Qed.

Lemma f2mx0 (R : fieldType) (G: vectType R) : f2mx (0%VF : 'End(G)) = 0.
Proof. exact: linear0. Qed.

Lemma f2mx_comp (R: ringType) (U V W: vectType R) (f : 'Hom(U,V)) (g: 'Hom(W,U)) :
  f2mx (f \o g) = f2mx g *m f2mx f.
Proof.
rewrite /comp_lfun unlock/=. apply/matrixP=>i j.
rewrite ![LHS]mxE/= unlock/= !r2vK -mulmxA mxE (bigD1 i)//= big1.
by move=>k /negPf nki; rewrite !mxE nki andbF mul0r.
by rewrite mxE !eqxx mul1r addr0.
Qed.

Lemma f2mx_bij (R : fieldType) (U V : vectType R) : bijective (@f2mx _ U V).
Proof. exists (@Vector.Hom _ U V). exact: f2mxK. exact: vecthomK. Qed.

Lemma vecthom_bij (R : fieldType) (U V : vectType R) : bijective (@Vector.Hom _ U V).
Proof. exists (@f2mx _ U V). exact: vecthomK. exact: f2mxK. Qed.

End VecterInternalTheoryExtra.

Arguments v2r_bij {R V}.
Arguments r2v_bij {R V}.
Arguments f2mx_bij {R U V}.
Arguments vecthom_bij {R U V}.

Section MxCast.
Variable (R: ringType).

Lemma castmx_mul p q r p' q' r' (eqq : q = q') (eqp : p = p') (eqr : r = r') 
  (A : 'M[R]_(p,q)) (B : 'M[R]_(q,r)) :
  (castmx (eqp,eqq) A) *m (castmx (eqq,eqr) B) = (castmx (eqp,eqr) (A *m B)).
Proof. by case: p' / eqp A; case: q' / eqq B; 
case: r' / eqr=>A B; rewrite !castmx_id. Qed.

Lemma castmx_mulr m n p p' (eqp: p = p') 
  (A: 'M[R]_(m,n)) (B: 'M_(n,p)) :
  A *m castmx (erefl _, eqp) B = castmx (erefl _,eqp) (A *m B).
Proof. by case: p' / eqp; rewrite !castmx_id. Qed.

Lemma castmx_mull m n p p' (eqp : p = p') 
  (A: 'M[R]_(p,m)) (B: 'M_(m,n)) :
  castmx (eqp, erefl _) A *m B = castmx (eqp, erefl _) (A *m B).
Proof. by case: p' / eqp; rewrite !castmx_id. Qed.

Lemma castmx_inj T p q p' q' (eqpq : (p = p') * (q = q')) :
  injective (@castmx T _ _ _ _ eqpq).
Proof. 
by case: eqpq=>eqp eqq; case: p' / eqp; case: q' / eqq=>x y; rewrite !castmx_id.
Qed.

Lemma castrv_qualifier T p p' (eqp : p = p') (P : forall p, qualifier 0 'rV[T]_p) 
  (A : 'rV[T]_p) : A \is P p <-> castmx (erefl _, eqp) A \is P p'.
Proof. by case: p' / eqp A P =>A P; rewrite castmx_id. Qed.

Lemma castmx_qualifier T p q p' q' (eqpq : (p = p') * (q = q')) 
  (P : forall p q, qualifier 0 'M[T]_(p,q)) (A : 'M[T]_(p,q)) :
  A \is P p q <-> castmx eqpq A \is P p' q'.
Proof. by case: eqpq=>eqp eqq; case : p' / eqp P A; 
case: q' / eqq=>P A; rewrite castmx_id. Qed.

Lemma diagmx_cast p p' (eqp : p = p') (A : 'rV[R]_p) :
  diag_mx (castmx (erefl _, eqp) A) = castmx (eqp, eqp) (diag_mx A).
Proof. by case: p' / eqp A =>A; rewrite castmx_id. Qed.

Lemma castmx_is_linear p q p' q' (eqpq : (p = p') * (q = q')) :
  linear (@castmx R p q p' q' eqpq).
Proof. by case: eqpq=>eqp eqq; case: p' / eqp; 
case: q' / eqq => a A B; rewrite !castmx_id. Qed.

Canonical castmx_linear p q p' q' (eqpq : (p = p') * (q = q')) :=
  Linear (@castmx_is_linear p q p' q' eqpq).

Lemma scalemx0 n : (0%:M : 'M[R]_n) = 0.
Proof. by apply/matrixP=>i j; rewrite !mxE mul0rn. Qed.

Lemma const_mx0 m n : (const_mx 0 : 'M[R]_(m,n)) = 0.
Proof. by apply/matrixP=>i j; rewrite !mxE. Qed.

Lemma mulmx_rowcol p q (A : 'M[R]_(p,q)) (B : 'M[R]_(q,p)) i j : 
  (A *m B) i j = (row i A *m col j B) 0 0.
Proof. by rewrite !mxE; apply eq_bigr=>k _; rewrite !mxE. Qed.

Lemma col_diag_mul {T : comRingType} n (D : 'rV[T]_n) p (A : 'M[T]_(p,n)) i : col i (A *m diag_mx D) = D 0 i *: col i A.
Proof.
apply/matrixP=>j k; rewrite !mxE (bigD1 i)//= big1; 
last by rewrite mxE eqxx mulr1n addr0 mulrC.
by move=>l /negPf nli; rewrite !mxE nli mulr0n mulr0.
Qed.

Lemma delta_mx_cast m n m' n' (eqmn : (m = m') * (n = n')) (i : 'I_m) (j : 'I_n) :
  castmx eqmn (delta_mx i j : 'M[R]__) = delta_mx (cast_ord eqmn.1 i) (cast_ord eqmn.2 j).
Proof.
by case: eqmn=> eqm eqn; case: m' / eqm i; case: n' / eqn j=>i j; 
rewrite castmx_id !cast_ord_id.
Qed.

End MxCast.

Section Etrans.
Variable (T : eqType).
Implicit Type (p q r t: T).

Lemma esym_erefl p : erefl p = esym (erefl p). Proof. by []. Qed.

Lemma etrans_esym p q (eqpq : p = q) :
  etrans eqpq (esym eqpq) = erefl p.
Proof. by case: q / eqpq=>/=. Qed.

Lemma etrans_erefl p q (eqpq : p = q) :
  etrans (erefl _) eqpq = eqpq.
Proof. by case: q / eqpq=>/=. Qed.

Lemma etrans_ereflV p q (eqpq : p = q) :
  etrans eqpq (erefl _) = eqpq.
Proof. by case: q / eqpq=>/=. Qed.

Lemma etrans_esymV p q (eqpq : p = q) :
  etrans (esym eqpq) eqpq = erefl q.
Proof. by case: q / eqpq=>/=. Qed.

Lemma esym_etrans p q r (eqpq : p = q) (eqqr : q = r) :
  esym (etrans eqpq eqqr) = etrans (esym eqqr) (esym eqpq).
Proof. by case: r / eqqr; case: q /eqpq. Qed.

Definition etransE := (etrans_esym, etrans_esymV, etrans_ereflV, etrans_erefl, esymK).

Lemma etransA p q r t (eqpq : p = q) (eqqr : q = r) (eqrt : r = t) :
  etrans eqpq (etrans eqqr eqrt) = etrans (etrans eqpq eqqr) eqrt.
Proof. apply: eq_irrelevance. Qed.

End Etrans.

Lemma nth_tnth (R: ringType) n (t: n.-tuple R) i (ltin : (i < n)%N) :
  t`_i = t~_(Ordinal ltin).
Proof. by rewrite (tnth_nth 0). Qed.

Lemma tnth_bigE (R: Type) (idx: R) (op: R->R->R) (I: ringType) (n : nat) 
  (X : n.-tuple I) P (F: 'I_n -> I -> R) :
  \big[op/idx]_(i < n | P i) F i (X`_i) = \big[op/idx]_(i | P i) F i X~_i.
Proof.
rewrite (eq_bigr (fun i => F i X~_i)) // => i _. 
by apply f_equal; rewrite (tnth_nth 0).
Qed.

Lemma pair_neq (T1 T2: eqType) (d d' : T1 * T2) :
  d != d' -> d.1 == d'.1 = false \/ d.2 == d'.2 = false.
Proof.
by destruct d=>/=; rewrite -pair_eqE /pair_eq/= 
  negb_and=>/orP[/negPf->|/negPf->]; [left|right].
Qed.

Lemma tuple_neqP (T : eqType) n (s t : n.-tuple T) :
  reflect (exists i, s~_i != t~_i) (s != t).
Proof.
apply/(iffP idP)=>[P|[i Pi]]; last by move: Pi; apply contraNN=>/eqP->.
apply/existsP; move: P; apply/contra_neqT; rewrite negb_exists=>/forallP P.
by apply eq_from_tnth=>x; move: (P x); rewrite negbK=>/eqP.
Qed.

Lemma dffun_neqP (I : finType) (J : forall i : I, eqType) 
  (f g : {dffun forall i, J i}) :
  reflect (exists i, f i != g i) (f != g).
Proof.
apply/(iffP idP)=>[P|[i Pi]]; last by move: Pi; apply contraNN=>/eqP->.
apply/existsP; move: P; apply/contra_neqT; rewrite negb_exists=>/forallP P.
by apply/ffunP=>x; move: (P x); rewrite negbK=>/eqP.
Qed.

Lemma ffun_neqP (I : finType) (J : eqType) (f g : {ffun I -> J}) :
  reflect (exists i, f i != g i) (f != g).
Proof. exact: dffun_neqP. Qed.

Lemma neq0_lt0n (m : nat) : (m == 0)%N <> true -> (0 < m)%N.
Proof. by move/negP; rewrite lt0n. Qed.

(* similar to %:C, inject real number to imaginary number *)
Definition im_complex_def (F : ringType) (phF : phant F) (x : F) :=
  Complex 0 x.
Notation im_complex F := (@im_complex_def _ (Phant F)).
Notation "x %:Ci" := (im_complex _ x)
  (at level 2, left associativity, format "x %:Ci")  : ring_scope.
Lemma im_complex_is_additive (R: ringType) : additive (im_complex R).
Proof. by move=>a b; simpc. Qed.
Definition im_complex_additive (R: ringType) := 
  Additive (@im_complex_is_additive R).
Lemma complex_split (R: ringType) (x : R[i]) : (Re x)%:C + (Im x)%:Ci = x.
Proof. by simpc; destruct x. Qed.

Section complex_extra.
Implicit Type (F:ringType) (R:rcfType).
Lemma re_realid F (x:F) : Re (x%:C) = x.
Proof. by simpc. Qed.
Lemma im_imid F (x:F) : Im (x%:Ci) = x.
Proof. by simpc. Qed.
Lemma im_real0 F (x:F) : Im (x%:C) = 0.
Proof. by simpc. Qed.
Lemma re_im0 F (x:F) : Re (x%:Ci) = 0.
Proof. by simpc. Qed.
Lemma normc_real R (x:R) : `|x%:C| = `|x|%:C.
Proof. 
by rewrite normc_def im_real0 expr0n addr0 re_realid Num.Theory.sqrtr_sqr.
Qed.
Lemma normc_im R (x:R) : `|x%:Ci| = `|x|%:C.
Proof. 
by rewrite normc_def re_im0 expr0n add0r im_imid Num.Theory.sqrtr_sqr.
Qed.
Lemma cgt0_real R (e : R[i]) : 0 < e -> (Re e)%:C = e.
Proof. 
rewrite -{3}(complex_split e) ltcE=>/andP[/eqP ->]/=; by rewrite addr0.
Qed.
Lemma real_gt0 R (e : R[i]) : 0 < e -> 0 < Re e.
by rewrite ltcE/==>/andP[ _].
Qed.
Lemma normc_ge_Im R (x : R[i]): `|Im x|%:C <= `|x|.
Proof.
by case: x => a b; simpc=>/=; rewrite -Num.Theory.sqrtr_sqr 
  Num.Theory.ler_wsqrtr // Num.Theory.ler_addr Num.Theory.sqr_ge0.
Qed.
End complex_extra.

Section RealC.
Variable (R : realType).
Implicit Type (x y : R).
Notation C := R[i].

(* for convert conjc and conjC *)
Lemma conjcC : (@conjc R) = conjC. Proof. by []. Qed.
Lemma conjCc : (@conjC _ : R[i] -> R[i]) = (@conjc R). Proof. by []. Qed.
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
Lemma realcX x n : (x^+n)%:C = x%:C^+n. Proof. exact: rmorphX. Qed.
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
Lemma split2c (x : C) : x / 2%:R + x / 2%:R = x.
Proof. by rewrite -mulr2n -mulr_natr mulfVK// pnatr_eq0. Qed.
Lemma split21 : (2%:R : C)^-1 + (2%:R : C)^-1 = 1.
Proof. by rewrite -[RHS]split2c mul1r. Qed.
Definition split2 := (split21, split2c).

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
by rewrite -(@eqr_expn2 _ 2%N)// ?mulr_ge0// ?sqrtC_ge0// ?P1// 
  exprMn !sqrtCK normrM ger0_norm// P1.
Qed.

Lemma sqrtC_inv (F : numClosedFieldType) (x : F) : 
  0 <= x -> ((sqrtC x)^-1 = sqrtC (x^-1))%R.
Proof.
by move=>Px; apply/eqP; rewrite -(@eqr_expn2 _ 2%N)// ?invr_ge0 
  ?sqrtC_ge0// ?invr_ge0// exprVn !sqrtCK.
Qed.

End RealC.

Section EnumOrd.
Variable (n : nat) (F : finType).

Lemma enum_ord_eq  (eqt : #|F| = n) j t : 
(enum_val (cast_ord (esym eqt) j) == t) = (j == cast_ord eqt (enum_rank t)).
Proof.
case: eqP=>[ <-|]; last case: eqP=>// ->.
1,2: by rewrite ?enum_valK cast_ord_comp cast_ord_id ?eqxx// enum_rankK.
Qed.

Lemma bij_enum_ord (eqt : n = #|F|) (P : pred F) :
{on P, bijective (fun x : 'I_n => enum_val (cast_ord eqt x))}.
Proof.
exists (fun x : F => cast_ord (esym eqt) (enum_rank x))=>t _;
rewrite ?enum_valK cast_ord_comp cast_ord_id// enum_rankK//.
Qed.

Lemma bij_ord_enum (eqt : #|F| = n) :
{on [pred: 'I_n | true], bijective (fun x : F => cast_ord eqt (enum_rank x))}.
Proof.
exists (fun x : 'I_n => enum_val (cast_ord (esym eqt) x))=>t _;
rewrite ?enum_valK cast_ord_comp cast_ord_id// enum_rankK//.
Qed.

End EnumOrd.


Section big_distr_big_dffun.
Variable R : Type.
Variables zero one : R.

Local Notation "0" := zero.
Local Notation "1" := one.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Local Notation "x * y" := (times x y).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).
Local Notation "x + y" := (plus x y).

Lemma big_mlaw_absord_seq (I : eqType) (r : seq I) (P : pred I) (i : I) (F : I -> R) :
  P i -> F i = 0 -> i \in r -> \big[*%M/1]_(i <- r | P i) F i = 0.
Proof.
move=>Pi Fi; elim: r=>[//|x r IH].
rewrite inE big_cons; case E: (P x)=>/orP[/eqP|]//.
by move=><-; rewrite Fi Monoid.mul0m.
by move=>/IH->; rewrite Monoid.mulm0.
by move=>xi; move: E; rewrite -xi Pi.
Qed.

Lemma big_mlaw_absord (I : finType) (i : I) (F : I -> R) :
  F i = 0 -> \big[*%M/1]_(i : I) F i = 0.
Proof. by move=>Fi; apply: (big_mlaw_absord_seq _ Fi). Qed.

Lemma big_distr_big_dffun 
 (I  : finType)
 (J  : I -> finType)
 (PJ : forall i : I, pred (J i))
 (F  : forall i : I, J i -> R)
:
    \big[*%M/1]_(i : I)
      \big[+%M/0]_(j : J i| PJ i j) F i j
  = \big[+%M/0]_(f : {dffun forall i : I, J i} | f \in family_mem (fun i : I => Mem (PJ i))) 
        \big[*%M/1]_(i : I) F i (f i).
Proof.
case/boolP: [forall i, (#|J i| > 0)%N]; last first.
- rewrite negb_forall => /existsP[] i; rewrite -eqn0Ngt => h.
  rewrite (@big_mlaw_absord _ i).  
  - rewrite big_pred0 // => j; have/fintype0 := j.
    by rewrite (eqP h).
  - rewrite big_pred0 //= => f; have /fintype0 := f i.
    by rewrite (eqP h).
move=> /forallP ibh; have {}ibh : forall i, J i.
- by move=> i; move/(_ i)/card_gt0P/xchoose: ibh; apply.
pose T := { i : I & J i }.
pose G (i : I) (x : T) :=
  if tag x =P i is ReflectT h then
    F i (ecast z (J z) h (tagged x))
  else 0.
pose Q (i : I) (x : T) :=
  if tag x =P i is ReflectT h then
    PJ i (ecast z (J z) h (tagged x))
  else false.
transitivity (\big[*%M/1]_i \big[+%M/0]_(j | Q i j) G i j).
- apply: eq_bigr=> i _; rewrite [RHS](eq_bigr (fun x => F _ (tagged x))).
  - by case=> i' j'; rewrite /Q /G; case: eqP => //=; case: _ /.
 pose Z (x : T) := pred1 i (tag x) && PJ _ (tagged x).
  rewrite (eq_bigl Z) /Z /Q; first case=> i0 j0 /=.
  - by case: eqP => //=; case: _ /.
  - by rewrite -sig_big_dep (big_pred1 i).
rewrite bigA_distr_big_dep.
pose h (f : {dffun forall i : I, J i}) := [ffun i => existT J i (f i)].
rewrite (reindex h); last first.
- apply: congr_big => //=.
  - move=> g; apply/idP/idP.
    - move/familyP=> hg; apply/forallP=> i; have := hg i.
      rewrite /Q /h /in_mem /= ffunE; case: eqP => //= eq.
      by rewrite eq_axiomK.
    - move/forallP=> hg; apply/familyP=> i; have := hg i.
      rewrite /Q /h /in_mem ffunE /=; case: eqP=> // eq.
      by rewrite eq_axiomK.
  - move=> g hg; apply: eq_bigr=> i _; rewrite /G /h ffunE /=.
    case: eqP; last first.
    - by move/forallP: hg => /(_ i); rewrite /Q /in_mem /=; case: eqP.
    - by move=> eq; rewrite eq_axiomK.
- pose hI (f : {ffun I -> T}) : {dffun forall i : I, J i} :=
    [ffun i : I =>
      if i =P tag (f i) is ReflectT h then
        eq_rect_r (fun z => J z) (tagged (f i)) h
      else ibh i].
  exists hI.
  - move=> f; rewrite inE => /familyP fQ; rewrite /hI /h.
    apply/ffunP=> i; rewrite !ffunE; case: eqP => //=.
    by move=> eq; rewrite eq_axiomK.
  - move=> f; rewrite inE => /familyP fQ; rewrite /hI /h.
    apply/ffunP=> i; rewrite ffunE /=; have := fQ i.
    rewrite /Q /in_mem /= ffunE; case: eqP => //=.
    move=> eq _; apply/eqP; rewrite /eq_op /=.
    rewrite /tag_eq /= {1}eq eqxx andTb /=.
    by rewrite /tagged_as; case: eqP.
Qed.

Lemma big_distr_dffun 
(I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> R) :
  \big[times/one]_(i : I) \big[plus/zero]_(j : J i) F i j =
     \big[plus/zero]_(f : {dffun forall i : I, J i})
        \big[times/one]_(i : I) F i (f i).
Proof.
rewrite big_distr_big_dffun; apply eq_bigl=>x/=.
by rewrite /in_mem/=; apply/forallP.
Qed.

End big_distr_big_dffun.

Lemma pair_bigV (R : Type) (idx : R) (op : Monoid.com_law idx) 
(I J : finType) (P : pred (I * J)) (F : I * J -> R) :
  \big[op/idx]_(p | P p) F p =
    \big[op/idx]_(i : I) \big[op/idx]_(j | P (i,j)) F (i, j).
Proof.
rewrite pair_big_dep/=.
by apply eq_big=>[i|i _]; rewrite -surjective_pairing.
Qed.

Lemma big_negb_all (I : Type) (r : seq I) (P B : pred I) : 
  ~~ (\big[andb/true]_(i <- r | P i) B i) = 
  \big[orb/false]_(i <- r | P i) (~~ B i).
Proof.
elim: r=>[|r x IH]; rewrite ?big_nil// !big_cons.
case: (P r)=>//; by rewrite negb_and IH.
Qed.

Lemma big_negb_or (I : Type) (r : seq I) (P B : pred I) : 
  ~~ (\big[orb/false]_(i <- r | P i) B i) = 
  \big[andb/true]_(i <- r | P i) (~~ B i).
Proof.
rewrite -[RHS]negbK big_negb_all; f_equal.
by apply eq_bigr=>i _; rewrite negbK.
Qed.

Lemma leq_ord n (i : 'I_n.+1) : (i <= n)%N.
Proof. by destruct i. Qed.

Lemma ltn_neq (m n : nat) : (m < n)%N -> m != n.
Proof. by move=>/ltn_eqF->. Qed.

Section WidenOrd.
Variable (n : nat).

Lemma widen_lift (i : 'I_n) : 
  widen_ord (leqnSn n) i = fintype.lift ord_max i.
Proof. by apply/ord_inj; rewrite lift_max/=. Qed.

Lemma widen_ord_neq (i : 'I_n) : 
  (widen_ord (leqnSn n) i) != ord_max.
Proof. by rewrite -(inj_eq val_inj); case: i=>/= m/ltn_neq. Qed.

Lemma lift_max_neq (i : 'I_n) : 
  (fintype.lift ord_max i) != ord_max.
Proof. by rewrite -widen_lift widen_ord_neq. Qed.

Lemma widen_ord_inj : injective (widen_ord (leqnSn n)).
Proof. move=>i j; rewrite !widen_lift; exact: lift_inj. Qed.

Variant widen_spec : 'I_n.+1 -> Type :=
  | widenR : widen_spec ord_max
  | widenL (x : 'I_n) : widen_spec (widen_ord (leqnSn n) x).

Lemma widenP i : widen_spec i.
Proof.
case E: (ord_max == i). move: E=>/eqP <-; constructor. 
move: E=>/eqP/eqP/unlift_some[j -> _].
rewrite -widen_lift. constructor.
Qed.

Variant lift_ord0_spec : 'I_n.+1 -> Type :=
  | liftord0L : lift_ord0_spec ord0
  | liftord0R (x : 'I_n) : lift_ord0_spec (fintype.lift ord0 x).

Lemma lift0P i : lift_ord0_spec i.
Proof.
case E: (ord0 == i). move: E=>/eqP <-; constructor. 
move: E=>/eqP/eqP/unlift_some[j -> _]; constructor.
Qed.

End WidenOrd.

Arguments widen_ord_inj {n}.
Arguments widenP {n}.
Arguments lift0P {n}.

Lemma notin_in_neq (T : eqType) (s : seq T) x y :
    x \notin s -> y \in s -> x != y.
Proof. by move=>+P1; move=>/memPnC/(_ _ P1). Qed.

Section SeqTuple.

Variables (n m : nat) (T U rT : Type).
Implicit Type t : n.-tuple T.

Definition tlast (u : n.+1.-tuple T) := tnth u ord_max.
Definition tfirst (s : seq T) := take (size s).-1 s.
Lemma tfirst_tupleP (u : n.+1.-tuple T) : size (tfirst u) == n.
Proof. by rewrite size_take size_tuple ltnSn. Qed.
Canonical tfirst_tuple u := Tuple (tfirst_tupleP u).
Lemma tfirst_rcons x (u : seq T) : tfirst (rcons u x) = u.
Proof.
rewrite /tfirst size_rcons/=.
by elim: u x=>[x//|y u IH x]; rewrite /= IH.
Qed.

Lemma tnthN x t : tnth [tuple of rcons t x] ord_max = x.
Proof. by rewrite (tnth_nth x)/= nth_rcons size_tuple ltnn eqxx. Qed.

Lemma tnthNS x t i : tnth [tuple of rcons t x] (widen_ord (leqnSn n) i) = tnth t i.
Proof.
rewrite !(tnth_nth x)/= nth_rcons size_tuple.
by case: i=>i /= Pi; rewrite Pi.
Qed.

Lemma tnthNS_lift x t i : tnth [tuple of rcons t x] (fintype.lift ord_max i) = tnth t i.
Proof. by rewrite -widen_lift tnthNS. Qed.

Variant tupleN_spec : n.+1.-tuple T -> Type :=
  TupleNspec x t : tupleN_spec [tuple of rcons t x].

Lemma tupleNP u : tupleN_spec u.
Proof.
case: u=>u; case/lastP: u=>[//|s x Pi].
have Ps: size s == n by move: Pi; rewrite size_rcons.
pose t := @Tuple n _ s Ps.
by rewrite (_ : Tuple _ = [tuple of rcons t x])//; apply/val_inj.
Qed.
(* usage: case/tupleNP : ... *)
Lemma tupleN_eta (t : n.+1.-tuple T) : t = [tuple of rcons (tfirst t) (tlast t)].
Proof.
by case/tupleNP: t=>x t; apply: val_inj; rewrite /=/tlast tnthN tfirst_rcons.
Qed.

End SeqTuple.

Lemma uphalfE m : uphalf m = (m.+1)./2. Proof. by []. Qed.
Lemma uphalf_half_split m : (uphalf m + half m = m)%N.
Proof. by rewrite uphalf_half -[RHS]odd_double_half -addnA addnn. Qed.
Lemma sub_uphalf m : (m - uphalf m = half m)%N.
Proof. by rewrite -{1}(uphalf_half_split m) addnC addnK. Qed.
Lemma sub_half m : (m - half m = uphalf m)%N.
Proof. by rewrite -{1}(uphalf_half_split m) addnK. Qed.
Lemma half_leqn m : (half m <= m)%N.
Proof. by rewrite -{2}(uphalf_half_split m) leq_addl. Qed.
Lemma uphalf_leqn m : (uphalf m <= m)%N.
Proof. by rewrite -{2}(uphalf_half_split m) leq_addr. Qed.
Lemma eq_uphalf_half_odd m : odd m -> uphalf m = (half m).+1.
Proof. by move=>P; rewrite uphalf_half P add1n. Qed.
Lemma eq_uphalf_half_even m : ~~ odd m -> uphalf m = half m.
Proof. by move=>/negPf P; rewrite uphalf_half P add0n. Qed.

Lemma uphalf_ord_subproof (m : nat) : (uphalf m < m.+1)%N.
Proof. by rewrite ltnS uphalf_leqn. Qed.
Definition uphalf_ord (m : nat) := Ordinal (uphalf_ord_subproof m).
Lemma uphalf_ord_odd_rev (m : nat) :
  ~~(odd m) -> rev_ord (uphalf_ord m) = uphalf_ord m.
Proof.
by move=>/negPf P; apply/val_inj=>/=; rewrite subSS uphalf_half 
  -{1}(odd_double_half m) P/= !add0n -addnn addnK.
Qed.
Lemma uphalf_ord_neq m (i : 'I_m.+1) : (i < uphalf m)%N -> uphalf_ord m != i.
Proof. by move=>P1; apply/eqP=>P2; move: P1; rewrite -P2/= ltnn. Qed.
Lemma rev_ord_neq m (i : 'I_m.+1) : (i < uphalf m)%N -> rev_ord i != i.
Proof.
move=>P1; apply/eqP=>P2; move: P2=>/(f_equal val)/=/(f_equal (addn i)).
rewrite subSS addnC subnK ?leq_ord// =>P2; move: P1.
by rewrite {2}P2 addnn uphalf_double ltnn.
Qed.

Lemma big_ord_rev (T : Type) (idx : T) (op : Monoid.com_law idx)
  n P (F : 'I_n -> T) :
  \big[op/idx]_(i < n | P i) F i
     = \big[op/idx]_(i < n | P (rev_ord i)) F (rev_ord i).
Proof. by apply: reindex; exists (@rev_ord n)=>i _; rewrite rev_ordK. Qed.

Lemma big_half_split (T : Type) (idx : T) (op : Monoid.com_law idx)
  n (F : 'I_n.+1 -> T) :
  \big[op/idx]_(i < n.+1) F i = 
  op (\big[op/idx]_(i : 'I_n.+1 | (i < uphalf n)%N) (op (F i) (F (rev_ord i))))
  (if odd n then idx else F (uphalf_ord n)).
Proof.
case E: (odd n).
rewrite (bigID (fun i : 'I_n.+1=> i < uphalf n)%N)/= big_split Monoid.mulm1; f_equal.
by rewrite big_ord_rev; apply eq_bigl=>i/=; rewrite subSS -leqNgt leq_subCr 
  ?leq_ord// ?uphalf_leqn// sub_uphalf eq_uphalf_half_odd.
rewrite (bigD1 (uphalf_ord n))// Monoid.mulmC/=; f_equal.
rewrite (bigID (fun i : 'I_n.+1=> i < uphalf n)%N)/= big_split; f_equal.
apply eq_bigl=>i; symmetry; rewrite eq_sym; case: eqP=>//=; 
by apply contraPF=>/uphalf_ord_neq/eqP.
move: E=>/negbT E; rewrite big_ord_rev; apply eq_bigl=>i/=.
by rewrite subSS -leqNgt leq_subCr ?leq_ord// ?uphalf_leqn// sub_uphalf eq_uphalf_half_even// 
  ltn_neqAle (inv_eq rev_ordK) uphalf_ord_odd_rev// -(inj_eq val_inj)/= eq_uphalf_half_even.
Qed.

Lemma tnth_rev T n (t : n.-tuple T) i :
  [tuple of rev t] ~_ i = t ~_ (rev_ord i).
Proof.
case: n t i=>[? i|n t i]; first by case: i.
by pose t0 := t ~_ ord0; rewrite !(tnth_nth t0)/= nth_rev size_tuple.
Qed.

Lemma big_setE (T : Type) (idx : T) (op : T -> T -> T)
  (F : finType) (P : pred F) (f : F -> T): 
    \big[op/idx]_(i | P i) f i = \big[op/idx]_(i in [set x | P x]) f i.
Proof. by apply: eq_bigl=>y; rewrite inE. Qed.

Lemma big_setT (T : Type) (idx : T) (op : T -> T -> T)
  (F : finType) (f : F -> T): 
    \big[op/idx]_i f i = \big[op/idx]_(i in setT) f i.
Proof. by rewrite big_setE/=. Qed.

Lemma big_setEV (T : Type) (idx : T) (op : T -> T -> T)
  (F : finType) (B : {set F}) (f : F -> T): 
    \big[op/idx]_(i in B) f i = \big[op/idx]_(i | i \in B) f i.
Proof. by rewrite big_setE/=. Qed.

Lemma big_setIDx (T : Type) (idx : T) (aop : Monoid.com_law idx) 
  (F : finType) (B : {set F}) (f : F -> T): 
  \big[aop/idx]_i f i =
     aop (\big[aop/idx]_(i in B ) f i)
         (\big[aop/idx]_(i in ~: B) f i).
Proof. by rewrite big_setT (big_setID B) setTI setTD. Qed.
Global Arguments big_setIDx [T idx aop F] B.

Lemma big_rcons (T : Type) (idx : T) (op : Monoid.law idx) 
    I i r (P : pred I) F :
    let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- rcons r i | P j) F j = if P i then op x (F i) else x.
Proof.
rewrite/=; elim: r.
by rewrite big_nil/= unlock/= Monoid.mulm1 Monoid.mul1m.
move=>a r IH. rewrite rcons_cons !big_cons; case: (P a)=>//.
by rewrite IH; case: (P i)=>//; rewrite Monoid.mulmA.
Qed.
