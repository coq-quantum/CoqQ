From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
(* From mathcomp.analysis Require Import reals. *)
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import Eqdep_dec.

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import VectorInternalTheory.

(*****************************************************************************)
(*                      Extra theories for Mathcomp                          *)
(*****************************************************************************)

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
Notation nlift := (fintype.lift).
Notation "A :<=: B" := (A \subset B) (at level 70, no associativity) : set_scope.

Section VecterInternalTheoryExtra.
Local Open Scope lfun_scope.

Lemma comp_lfunACA (R : ringType) (U1 U2 U3 U4 U5 : vectType R) (A: 'Hom(U4,U5)) (B: 'Hom(U3,U4))
(C: 'Hom(U2,U3)) (D: 'Hom(U1,U2)) :
  A \o B \o C \o D = A \o (B \o C) \o D.
Proof. by rewrite !comp_lfunA. Qed.

Lemma linearlfE (R : ringType) (U V : lmodType R) 
  (f : U -> V) (lf: linear f) : f =
  (HB.pack f (GRing.isLinear.Build _ _ _ _ f lf) : GRing.Linear.type _ _).
Proof. by []. Qed.

Lemma scalarlfE (R : ringType) (U : lmodType R) 
  (f : U -> R) (lf: scalar f) : f =
  (HB.pack f (GRing.isLinear.Build _ _ _ _ f lf) : GRing.Linear.type _ _).
Proof. by []. Qed.

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
(* #[export] *)
HB.instance Definition _ (R : fieldType) (U V: vectType R) := 
  GRing.isLinear.Build R _ _ _ (@f2mx R U V) (@f2mxP R U V).

(* Canonical h2mx_linear (R : fieldType) (U V: vectType R) := 
  (HB.pack (@f2mx R U V) (GRing.isLinear.Build _ _ _ _ (@f2mx R U V)
    (@f2mxP R U V)) : GRing.Linear.type _ _). *)

Lemma vecthomP (R : fieldType) (U V: vectType R) : linear (@Hom _ U V).
Proof. by move=>c x y; apply/lfunP=>z; rewrite unlock/= !linearP. Qed.
HB.instance Definition _ (R : fieldType) (U V: vectType R) := 
  GRing.isLinear.Build R _ _ _ (@Hom _ U V) (@vecthomP R U V).

Lemma f2mxK (R : fieldType) (U V : vectType R) : cancel (@f2mx _ U V) (Hom).
Proof. move=>x; by apply/val_inj. Qed.

Lemma vecthomK (R : fieldType) (U V : vectType R) : cancel (Hom) (@f2mx _ U V).
Proof. by move=>x. Qed.

Lemma f2mx_inj (R : fieldType) (U V: vectType R) : injective (@f2mx _ U V).
Proof. exact: (can_inj (@f2mxK _ _ _)). Qed.

Lemma vecthom_inj (R : fieldType) (U V: vectType R) : injective (@Hom _ U V).
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
suff: (\1%VF : 'End(G)) = Hom 1%:M. by move/(f_equal f2mx).
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
Proof. exists (@Hom _ U V). exact: f2mxK. exact: vecthomK. Qed.

Lemma vecthom_bij (R : fieldType) (U V : vectType R) : bijective (@Hom _ U V).
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

Lemma castmx_cst_diag T1 T2 (f : forall m, 'M[T1]_m -> T2) m n 
  (eqmn : (m = n)) (A : 'M[T1]_m) :
  f _ (castmx (eqmn,eqmn) A) = f _ A.
Proof. by case: n/eqmn; rewrite castmx_id. Qed.

Lemma castmx_cst_rv T1 T2 (f : forall m, 'rV[T1]_m -> T2) m n 
  (eqmn : (m = n)) (A : 'rV[T1]_m) :
  f _ (castmx (erefl _,eqmn) A) = f _ A.
Proof. by case: n/eqmn; rewrite castmx_id. Qed.

Lemma castmx_cst_cv T1 T2 (f : forall m, 'cV[T1]_m -> T2) m n 
  (eqmn : (m = n)) (A : 'cV[T1]_m) :
  f _ (castmx (eqmn,erefl _) A) = f _ A.
Proof. by case: n/eqmn; rewrite castmx_id. Qed.

Lemma castmx_cst_mx T1 T2 (f : forall m n, 'M[T1]_(m,n) -> T2) m n p q 
  (eqmn : (m = n) * (p = q)) (A : 'M[T1]_(m,p)) :
  f _ _ (castmx eqmn A) = f _ _ A.
Proof. by case: eqmn=>a b; case: n/a; case: q/b; rewrite castmx_id. Qed.

Lemma castmx_mx_diag T1 T2 (f : forall m, 'M[T1]_m -> 'M[T2]_m) m n 
  (eqmn : (m = n)) (A : 'M[T1]_m) :
  f _ (castmx (eqmn,eqmn) A) = castmx (eqmn,eqmn) (f _ A).
Proof. by case: n/eqmn; rewrite castmx_id. Qed.

Lemma castmx_mx_mx T1 T2 (f : forall m n, 'M[T1]_(m,n) -> 'M[T2]_(m,n)) m n p q 
  (eqmn : (m = n) * (p = q)) (A : 'M[T1]_(m,p)) :
  f _ _ (castmx eqmn A) = castmx eqmn (f _ _ A).
Proof. by case: eqmn=>a b; case: n/a; case: q/b; rewrite castmx_id. Qed.

Lemma castmx_mx_rv T1 T2 (f : forall m, 'rV[T1]_m -> 'rV[T2]_m) m n 
  (eqmn : (m = n)) (A : 'rV[T1]_m) :
  f _ (castmx (erefl _,eqmn) A) = castmx (erefl _,eqmn) (f _ A).
Proof. by case: n/eqmn; rewrite castmx_id. Qed.

Lemma castmx_mx_cv T1 T2 (f : forall m, 'cV[T1]_m -> 'cV[T2]_m) m n 
  (eqmn : (m = n)) (A : 'cV[T1]_m) :
  f _ (castmx (eqmn,erefl _) A) = castmx (eqmn,erefl _) (f _ A).
Proof. by case: n/eqmn; rewrite castmx_id. Qed.

Lemma castmx_mx_mxT T1 T2 (f : forall m n, 'M[T1]_(m,n) -> 'M[T2]_(n,m)) m n p q 
  (eqmn : (m = n) * (p = q)) (A : 'M[T1]_(m,p)) :
  f _ _ (castmx eqmn A) = castmx (eqmn.2,eqmn.1) (f _ _ A).
Proof. by case: eqmn=>a b; case: n/a; case: q/b; rewrite castmx_id. Qed.

Lemma cast_qualifier_diag T p p' (eqp : p = p') (P : forall p, qualifier 0 'M[T]_p) 
  (A : 'M[T]_p) : ((castmx (eqp,  eqp) A) \is P p') = (A \is P p).
Proof. by case: p' / eqp A P =>A P; rewrite castmx_id. Qed.

Lemma cast_qualifier_rv T p p' (eqp : p = p') (P : forall p, qualifier 0 'rV[T]_p) 
  (A : 'rV[T]_p) : ((castmx (erefl _, eqp) A) \is P p') = (A \is P p).
Proof. by case: p' / eqp A P =>A P; rewrite castmx_id. Qed.

Lemma cast_qualifier_cv T p p' (eqp : p = p') (P : forall p, qualifier 0 'cV[T]_p) 
  (A : 'cV[T]_p) : ((castmx (eqp, erefl _) A) \is P p') = (A \is P p).
Proof. by case: p' / eqp A P =>A P; rewrite castmx_id. Qed.

Lemma cast_qualifier_mx T p q p' q' (eqpq : (p = p') * (q = q')) 
  (P : forall p q, qualifier 0 'M[T]_(p,q)) (A : 'M[T]_(p,q)) :
  (castmx eqpq A \is P p' q') = (A \is P p q).
Proof.
by case: eqpq=>eqp eqq; case : p' / eqp P A; 
case: q' / eqq=>P A; rewrite castmx_id.
Qed.

Definition castmx_funE := (castmx_cst_diag, castmx_cst_rv, castmx_cst_cv, 
  castmx_cst_mx, castmx_mx_diag, castmx_mx_mx, castmx_mx_rv, castmx_mx_cv,
  castmx_mx_mxT,cast_qualifier_diag,cast_qualifier_rv,cast_qualifier_cv,
  cast_qualifier_mx).

Lemma diagmx_cast p p' (eqp : p = p') (A : 'rV[R]_p) :
  diag_mx (castmx (erefl _, eqp) A) = castmx (eqp, eqp) (diag_mx A).
Proof. by case: p' / eqp A =>A; rewrite castmx_id. Qed.

Lemma castmx_is_linear p q p' q' (eqpq : (p = p') * (q = q')) :
  linear (@castmx R p q p' q' eqpq).
Proof.
by case: eqpq=>eqp eqq; case: p' / eqp; 
case: q' / eqq => a A B; rewrite !castmx_id.
Qed.

HB.instance Definition _ p q p' q' (eqpq : (p = p') * (q = q')) := 
  GRing.isLinear.Build R _ _ _ (@castmx R p q p' q' eqpq) (@castmx_is_linear p q p' q' eqpq).

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

Notation "[ 'tuple' i => F ]" := [tuple F | i < _]
  (at level 0, format "[ '[hv' 'tuple'  i  '=>'  F ] ']'") : form_scope.
Notation eq_tnth := eq_mktuple.

Lemma tnthE n (T : Type) (f : 'I_n -> T) i :
  [tuple f i | i < n] ~_ i = f i.
Proof. by rewrite tnth_map tnth_ord_tuple. Qed.

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
  (HB.pack (im_complex R) (GRing.isAdditive.Build _ _ (im_complex R)
  (@im_complex_is_additive R)) : GRing.Additive.type _ _).
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
  Num.Theory.ler_wsqrtr // Num.Theory.lerDr Num.Theory.sqr_ge0.
Qed.
End complex_extra.

Lemma ler_sum_const (T: numDomainType) m (f : 'I_m -> T) c :
  (forall i, f i <= c) ->
  \sum_i f i <= m%:R * c.
Proof.
move=>P1; have P2: \sum_i f i <= \sum_(i<m) c. by apply ler_sum.
apply: (le_trans P2); by rewrite sumr_const card_ord mulr_natl.
Qed.

Lemma ler1Sn (T : numDomainType) i : 1 <= i.+1%:R :> T.
Proof. by rewrite -addn1 natrD lerDr. Qed.

(* Lemma ltr_sum n (F G : 'I_n.+1 -> C) :
    (forall i, F i < G i) ->
  \sum_(i < n.+1) F i < \sum_(i < n.+1) G i.
Proof.
move: F G. elim: n.
by move=>F G IH; rewrite !big_ord1 IH.
move=>m IH F G IH1.
rewrite big_ord_recl [\sum_(i < m.+2) G i]big_ord_recl.
apply ltrD. by apply IH1.
apply IH=>i. apply IH1.
Qed. *)

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

Lemma bigA_distr_tuple n (J : finType) F :
  \big[*%M/1]_(i < n) \big[+%M/0]_(j : J) F i j
    = \big[+%M/0]_(f : n.-tuple J) \big[*%M/1]_i F i (f ~_ i).
Proof.
rewrite bigA_distr_bigA.
rewrite (reindex (fun f : {ffun _}=> [tuple i => f i])).
exists (fun f : n.-tuple J => [ffun i => f ~_ i]).
by move=>a _; apply/ffunP=>i; rewrite ffunE tnthE.
by move=>a _; apply/eq_from_tnth=>i; rewrite tnthE ffunE.
by do 2 apply eq_bigr=>? _; rewrite tnthE.
Qed.

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


Lemma big_sig_cond (T : Type) (idm : T) (op : Monoid.com_law idm) 
  (I : finType) (P Q : pred I) (f : I -> T) :
  \big[op/idm]_(i : {x : I | P x} | Q (val i)) f (val i) = \big[op/idm]_(i | P i && Q i) f i.
Proof.
case E: (pred0b P); [move: E=>/pred0P P1 | move: E=>/pred0Pn[x Px]].
rewrite big_seq_cond !big_pred0//= =>x; last by move: (P1 x)=>->.
by destruct x; move: (P1 x); rewrite !inE/=/in_mem/= i.
rewrite (reindex (fun x: {x : I | P x}=> projT1 x));
  last by apply eq_big =>[y|y P2]; destruct y=>//=; rewrite i.
exists (fun t=> match P t =P true with | ReflectT px => exist _ t px
  | ReflectF _ => exist _ x Px end)=>y Py; case: eqP=>P1//.
by destruct y=>/=; move: P1=>/= P1; rewrite (eq_irrelevance i P1).
all: by move: Py; rewrite inE=>/andP[].
Qed.

Lemma big_sig (T : Type) (idm : T) (op : Monoid.com_law idm) 
  (I : finType) (P : pred I) (f : I -> T) :
  \big[op/idm]_(i : {x : I | P x}) f (val i) = \big[op/idm]_(i | P i) f i.
Proof.
move: (@big_sig_cond T idm op I P (fun=>true) f)=>->.
by apply eq_bigl=>i; rewrite andbT.
Qed.

Lemma big_sig_set_cond (R : Type) (idm : R) (op : Monoid.com_law idm) (L: finType) 
  (P: pred L) (W: {set L}) (F: L -> R) :
  \big[op/idm]_(i : {i:L|i \in W} | P (val i)) F (val i) = \big[op/idm]_(i in W | P i) F i.
Proof. exact: big_sig_cond. Qed.

Lemma big_sig_set (T : Type) (idm : T) (op : Monoid.com_law idm) (L: finType)
  (W: {set L}) (F: L -> T) :
  \big[op/idm]_(i : {i:L|i \in W}) F (val i) = \big[op/idm]_(i in W ) F i.
Proof. exact: big_sig. Qed.


Lemma leq_ord n (i : 'I_n.+1) : (i <= n)%N.
Proof. by destruct i. Qed.

Lemma ltn_neq (m n : nat) : (m < n)%N -> m != n.
Proof. by move=>/ltn_eqF->. Qed.

Section WidenOrd.
Variable (n : nat).

Lemma widen_lift (i : 'I_n) : 
  widen_ord (leqnSn n) i = nlift ord_max i.
Proof. by apply/ord_inj; rewrite lift_max/=. Qed.

Lemma widen_ord_neq (i : 'I_n) : 
  (widen_ord (leqnSn n) i) != ord_max.
Proof. by rewrite -(inj_eq val_inj); case: i=>/= m/ltn_neq. Qed.

Lemma lift_max_neq (i : 'I_n) : 
  (nlift ord_max i) != ord_max.
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
  | liftord0R (x : 'I_n) : lift_ord0_spec (nlift ord0 x).

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

Lemma tnthNS_lift x t i : tnth [tuple of rcons t x] (nlift ord_max i) = tnth t i.
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

Require Import autonat.

Lemma bump0 i : bump 0%N i = i.+1.
Proof. by rewrite /bump leq0n add1n. Qed.

Lemma rev_ord_lift n (h : 'I_n) (i : 'I_n.-1) :
  rev_ord (nlift h i) = nlift (rev_ord h) (rev_ord i).
Proof. mc_nat. Qed.
(* case: n h i=>//=[|n h i]; first by case.
apply/val_inj=>/=; rewrite /bump.
have -> : ((n.+1 - h.+1 <= n - i.+1) = ~~ (h <= i))%N.
by rewrite [in RHS]leqNgt negbK subSS leq_sub2lE.
by case: (h <= i)%N=>/=; rewrite add0n add1n subSS// subnSK. *)

Lemma rev_ord0 n : rev_ord (ord0 : 'I_n.+1) = ord_max.
Proof. by apply/val_inj=>/=; rewrite subn1. Qed.
Lemma rev_ord_max n : rev_ord (ord_max : 'I_n.+1) = ord0.
Proof. by apply/val_inj=>/=; rewrite subnn. Qed.
Lemma rev_ord_lift0 n (i : 'I_n) : rev_ord (nlift ord0 i) = nlift ord_max (rev_ord i).
Proof. by rewrite rev_ord_lift rev_ord0. Qed.
Lemma rev_ord_lift_max n (i : 'I_n) : rev_ord (nlift ord_max i) = nlift ord0 (rev_ord i).
Proof. by rewrite rev_ord_lift rev_ord_max. Qed.

(* Import mathcomp_nat_ord_convert. *)

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

Definition half_ord m (i : 'I_m./2) := widen_ord (half_leqn _) i.
Lemma half_ord_rev_neq m (i j : 'I_m./2) : half_ord i != rev_ord (half_ord j).
Proof. mc_nat. Qed.
(* case: m i j; last case. 1,2: by move=>i; case: i.
move=>n i j; apply/ltn_neq=>/=; rewrite leq_subRL.
by case: j=>/= m P; apply/(leq_trans P)/ltnW; rewrite !ltnS half_leqn.
case: i; case: j=>i Pi j Pj/=; apply/(leq_trans (leq_add Pi Pj)).
by rewrite addnn halfK leq_subr. *)

Lemma ord_half_subproof (m : nat) : (half (m.+1) < m.+1)%N.
Proof. by rewrite -uphalfE ltnS uphalf_leqn. Qed.
Definition ord_half (m : nat) := Ordinal (ord_half_subproof m).

Lemma ord_uphalf_subproof (m : nat) : (uphalf (m.+2) < m.+2)%N.
Proof. by rewrite -{2}[m.+2]uphalf_half_split -ltn_subLR// subnn. Qed.
Definition ord_uphalf (m : nat) := Ordinal (ord_uphalf_subproof m).

Lemma uphalf_ord_odd_rev (m : nat) :
  ~~(odd m) -> rev_ord (ord_half m) = ord_half m.
Proof.
by move=>/negPf P; apply/val_inj=>/=; rewrite subSS uphalf_half 
  -{1}(odd_double_half m) P/= !add0n -addnn addnK.
Qed.

Lemma ord_half_neq m j : ord_half m != half_ord j.
Proof. by rewrite -(inj_eq val_inj)/= eq_sym ltn_neq. Qed.

Lemma big_ord_rev (T : Type) (idx : T) (op : Monoid.com_law idx)
  n P (F : 'I_n -> T) :
  \big[op/idx]_(i < n | P i) F i
     = \big[op/idx]_(i < n | P (rev_ord i)) F (rev_ord i).
Proof. by apply: reindex; exists (@rev_ord n)=>i _; rewrite rev_ordK. Qed.

Lemma big_ord_half (T : Type) (idx : T) (op : Monoid.com_law idx)
  n (F : 'I_n.+1 -> T) :
  \big[op/idx]_(i : 'I_(n.+1./2)) F (half_ord i)
     = \big[op/idx]_(i < n.+1 | (i < n.+1./2)%N) F i.
Proof.
pose G := fun i : nat => match (i < n.+1)%N =P true with
          | ReflectT E => F (Ordinal E)
          | ReflectF E => idx
          end.
have PG i : F i = G i.
  by rewrite/G; case: eqP; case: i=>//= m P1 P2; f_equal; apply/val_inj.
under eq_bigr do rewrite PG/=. under [RHS]eq_bigr do rewrite PG/=.
by rewrite (big_ord_widen_cond _ xpredT _ (half_leqn _))/=.
Qed.

Lemma big_half_split (T : Type) (idx : T) (op : Monoid.com_law idx)
  n (F : 'I_n.+1 -> T) :
  \big[op/idx]_(i < n.+1) F i = 
  op (\big[op/idx]_(i : 'I_(n.+1./2)) (op (F (half_ord i)) (F (rev_ord (half_ord i)))))
  (if odd n then idx else F (ord_half n)).
Proof.
rewrite (big_ord_half _ (fun i => op (F i) (F (rev_ord i)))).
case E: (odd n).
rewrite (bigID (fun i : 'I_n.+1=> i < uphalf n)%N)/= big_split Monoid.mulm1; f_equal.
by rewrite big_ord_rev; apply eq_bigl=>i/=; rewrite subSS -leqNgt leq_subCr 
  ?leq_ord// ?uphalf_leqn// sub_uphalf eq_uphalf_half_odd.
rewrite (bigD1 (ord_half n))// Monoid.mulmC/=; f_equal.
rewrite (bigID (fun i : 'I_n.+1=> i < uphalf n)%N)/= big_split; f_equal.
by apply eq_bigl=>i; symmetry; rewrite eq_sym; case: eqP=>//<-/=; rewrite ltnn.
rewrite big_ord_rev; apply eq_bigl=>i/=.
rewrite subSS -leqNgt leq_subCr ?leq_ord// ?uphalf_leqn// 
  sub_uphalf eq_uphalf_half_even ?E// ltn_neqAle (inv_eq rev_ordK) 
  uphalf_ord_odd_rev ?E// -(inj_eq val_inj)/= eq_uphalf_half_even ?E//.
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

Coercion tuple_of_finfun : finfun_of >-> tuple_of.
Coercion finfun_of_tuple : tuple_of >-> finfun_of.
Lemma tnth_ffun_tuple (K : Type) (m : nat) (f : {ffun 'I_m -> K}) i :
  f ~_ i = f i.
Proof. by rewrite -{2}(tuple_of_finfunK f) ffunE. Qed.
Lemma tuple_ffunE (K : Type) (m : nat) (f : m.-tuple K) (i : 'I_m) :
  f i = f ~_ i.
Proof. by rewrite -tnth_ffun_tuple finfun_of_tupleK. Qed.

Lemma eqb_iff (b1 b2 : bool): (b1 <-> b2) <-> b1 = b2.
Proof. by split=>[/Bool.eq_iff_eq_true|->]. Qed.
Lemma eq_iff (T : eqType) (t1 t2 : T) : t1 == t2 <-> t1 = t2.
Proof. by split=>[/eqP|->]. Qed.

(* use for dependent inversion*)
Lemma inj_existT (A : eqType) (P : A -> Type) (p : A) (x y : P p):
  existT P p x = existT P p y -> x = y.
Proof. by apply/inj_pair2_eq_dec=>a b; case: (@eqP _ a b); [left|right]. Qed.
Global Arguments inj_existT {A P p x y}.

(* bigmax *)
Lemma le_max2l (disp : unit) (T : porderType disp) (a : T) :
  {homo (@Order.max _ T a) : x y / (x <= y)%O >-> (x <= y)%O }.
Proof.
move=>x y Pxy; rewrite/Order.max; case E: (a < x)%O.
  by move: (lt_le_trans E Pxy)=>->.
case F: (a < y)%O=>//; by move: F; rewrite lt_neqAle=>/andP[].
Qed.
Definition ler_max2l := (@le_max2l ring_display).

Lemma ler_max2r (T : numDomainType) (a : T) :
  {homo (@Order.max _ T ^~ a) : x y / (x <= y) >-> (x <= y) }.
Proof.
move=>x y Pxy; rewrite/Order.max; case E: (x < a).
  case: comparable_leP=>//; apply: (comparabler_trans (y := x)).
  by apply/gt_comparable. by apply/le_comparable.
by case F: (y < a)%O=>//; move: (le_lt_trans Pxy F); rewrite E.
Qed.

Lemma lt_min2r (disp : unit) (T : porderType disp) (a : T) :
  {homo (@Order.min _ T ^~ a) : x y / (x <= y)%O >-> (x <= y)%O }.
Proof.
move=>x y Pxy; rewrite/Order.min; case E: (x < a)%O.
  by case: (y < a)%O=>//; apply/ltW.
by case F: (y < a)%O=>//; move: (le_lt_trans Pxy F); rewrite E.
Qed.
Definition ltr_min2r := (@lt_min2r ring_display).

Lemma ltr_min2l (T : numDomainType) (a : T) :
  {homo (@Order.min _ T a) : x y / (x <= y)%O >-> (x <= y)%O }.
Proof.
move=>x y Pxy; rewrite/Order.min; case E: (a < x).
  by case: (a < y)=>//; apply/ltW/(lt_le_trans E Pxy).
case F: (a < y)=>//; move: E; case: comparable_leP=>//.
apply: (comparabler_trans (y := y)).
by apply/le_comparable. by apply/gt_comparable.
Qed.

Variant bigmax_x0_or_in (disp : unit) (T : porderType disp) (x0 : T) 
  (I : eqType) (r : seq I) (P : pred I) (F : I -> T) : T -> Type :=
  | bigmax_eq_x0 : @bigmax_x0_or_in disp T x0 I r P F x0
  | bigmax_in_seq (i : I) of (i \in r) & P i: @bigmax_x0_or_in disp T x0 I r P F (F i).

Lemma bigmax_eq_elemP (disp : unit) (T : porderType disp) (x0 : T) 
  (I : eqType) (r : seq I) (P : pred I) (F : I -> T) :  
    @bigmax_x0_or_in disp T x0 I r P F (\big[Order.max/x0]_(i <- r | P i) F i).
Proof.
rewrite big_seq_cond; elim/big_rec: _; first by left.
move=>i x /andP[] Ini Pi [|j Inj Pj]; rewrite/Order.max;
by case: (F i < _)%O; try do [left | right].
Qed.

(* finset *)
(* ==================================================================== *)
Section SetExtra.
Variable (I: finType).
Implicit Type (A B C : {set I}).

Lemma disjointP A B : reflect (forall a, a \in A -> a \notin B) [disjoint A & B].
Proof. rewrite disjoint_subset; apply (iffP subsetP); by move=>+ a; move=>/(_ a). Qed.

Lemma disj_inf A B : [disjoint A & B] -> forall x, (x \in A) && (x \in B) = false.
Proof.
by move/disjointP=> dis x; case E1: (x \in A) => //=; apply negbTE; apply: dis.
Qed.

Lemma disjoint0X A : [disjoint set0 & A].
Proof. by rewrite -setI_eq0 set0I. Qed.

Lemma disjointX0 A : [disjoint A & set0].
Proof. by rewrite -setI_eq0 setI0. Qed.

Lemma disjointXXP A : reflect (A = set0) [disjoint A & A].
Proof. by apply (iffP setDidPl); rewrite setDv=>->. Qed.

Lemma disjointXD A B : [disjoint A & (B :\: A)].
Proof. by apply/disjointP => x; apply contraTT; move/negbNE/setDP=>[_ H2]. Qed.

Lemma disjointDX A B : [disjoint (B :\: A) & A].
Proof. by apply/disjointP => x; move/setDP=>[_ H2]. Qed.

Lemma disjointXC A : [disjoint A & ~: A].
Proof. by rewrite -setI_eq0 setICr. Qed.

Lemma disjointCX A : [disjoint ~: A & A].
Proof. by rewrite disjoint_sym disjointXC. Qed.

Lemma disjointXDg A B C: [disjoint A & B] -> [disjoint A & B :\: C].
Proof. by rewrite -!setI_eq0 setIDA => /eqP ->; rewrite set0D. Qed.

Lemma disjointDXg A B C: [disjoint A & B] -> [disjoint A :\: C & B].
Proof. by rewrite ![[disjoint _ & B]]disjoint_sym; apply disjointXDg. Qed.

Lemma disjoint1X x A : [disjoint [set x] & A] = (x \notin A).
Proof. exact: disjoints1. Qed.

Lemma disjointX1 x A : [disjoint A & [set x]] = (x \notin A).
Proof. by rewrite disjoint_sym disjoint1X. Qed.

Lemma disjointUX A B C :
   [disjoint A :|: B & C] = [disjoint A & C] && [disjoint B & C].
Proof. by rewrite -!setI_eq0 setIUl setU_eq0. Qed.

Lemma disjointXU A B C :
   [disjoint A & B :|: C] = [disjoint A & B] && [disjoint A & C].
Proof. by rewrite -!setI_eq0 setIUr setU_eq0. Qed.

Lemma disjointU1X x A B :
   [disjoint x |: A & B] = (x \notin B) && [disjoint A & B].
Proof. by rewrite disjointUX disjoint1X. Qed.

Lemma disjointP_sym A B :
  reflect (forall a, a \in A -> a \notin B) [disjoint B & A].
Proof. by rewrite disjoint_sym; apply: disjointP. Qed.

Lemma setUD A B : A :|: B :\: A = A :|: B.
Proof. by rewrite setDE setUIr setUCr setIT. Qed.

Lemma setUDV A B : A :|: B :\: A = B :|: A.
Proof. by rewrite setUD setUC. Qed.

Lemma setUDS A B : A :|: B :\: A = B :|: A :\: B.
Proof. by rewrite !setUD setUC. Qed.

Lemma setUDSV A B : A :\: B :|: B = B :\: A :|: A.
Proof. by rewrite setUC setUDS setUC. Qed.

Definition set0_simp := (set0D,setD0,set0U,setU0,setI0,set0I,disjointX0,
  disjoint0X,setDv,disjointXD,disjointDX).

Lemma disjointDI A B : [disjoint A :\: B & A :&: B].
Proof.
move: (disjointDX B A).
rewrite -!setI_eq0 [A :&: B]setIC setIA=>/eqP->. by rewrite set0I.
Qed.
Lemma disjointID A B : [disjoint A :&: B & A :\: B].
Proof. by rewrite disjoint_sym disjointDI. Qed.

Lemma setUD_sub A B : A :<=: B -> A :|: B :\: A = B.
Proof. by rewrite setUD; apply/setUidPr. Qed.

Lemma subUsetPP A B C : A :<=: C -> B :<=: C -> A :|: B :<=: C.
Proof. by rewrite subUset=>->->. Qed.

Section BigCupType.
Variables (J : Type).
Implicit Types  (r : seq J) (P : pred J) (F :  J -> {set I}).

(* replace of bigcupsP *)
Lemma bigcupsP_seqT (U : {set I}) r P F :
  (forall i : J, P i -> F i :<=: U) ->
          (\bigcup_(i <- r | P i) F i :<=: U).
Proof. 
move=>Pi; elim: r=>[|x r IH]; first by rewrite big_nil sub0set.
by rewrite big_cons; case E: (P x)=>//; rewrite subUset IH Pi.
Qed.

Lemma bigcup_disjointP_seqT  (U: {set I}) r P F :
  (forall i, P i -> [disjoint U & F i]) ->
    ([disjoint U & \bigcup_(i <- r | P i) F i ]).
Proof.
move=>Pi; elim: r=>[|x r IH]; first by rewrite big_nil disjointX0.
by rewrite big_cons; case E: (P x)=>//; rewrite disjointXU IH Pi.
Qed.

End BigCupType.

Section BigCupSeq.

Variables (J : eqType) (r : seq J).
Implicit Types (P : pred J) (F :  J -> {set I}).

Lemma bigcup_sup_seq j P F : j \in r -> P j -> F j :<=: \bigcup_(i <- r | P i) F i.
Proof.
move=> jr Pj; rewrite big_mkcond -(big_undup _ _ _ (@setUid _)).
by rewrite (bigD1_seq j) ?mem_undup ?undup_uniq ?Pj //= subsetUl.
Qed.

Lemma bigcup_seqP x F P :
  reflect (exists2 i : J, (i \in r) && P i & x \in F i)
          (x \in \bigcup_(i <- r | P i) F i).
Proof.
apply: (iffP idP) => [|[i /andP[ri Pi]]]; last first.
  by apply: subsetP x; rewrite bigcup_sup_seq.
rewrite big_seq_cond; elim/big_rec: _ => [|i _ /andP[ri Pi] _ /setUP[|//]];
  by [rewrite in_set0 | exists i; rewrite ?ri].
Qed.

Lemma bigcups_seqP A P F :
  reflect (forall i : J, i \in r -> P i -> F i :<=: A)
          (\bigcup_(i <- r | P i) F i :<=: A).
Proof.
apply: (iffP idP) => [sFU i ri Pi| sFU].
  by apply: subset_trans sFU; apply: bigcup_sup_seq.
by apply/subsetP=> x /bigcup_seqP[i /andP[ri Pi]]; apply/subsetP/sFU.
Qed.

Lemma bigcup_disjoint_seqP A P F :
  reflect (forall i, (i \in r) && P i -> [disjoint A & F i])
    ([disjoint A & \bigcup_(i <- r | P i) F i ]).
Proof.
rewrite -setI_eq0 -subset0 big_distrr/=.
apply (iffP (bigcups_seqP _ _ _)) =>[IH i /andP[P1 P2] | IH i P1 P2].
move: (IH i P1 P2). all: rewrite subset0 setI_eq0//.
by apply IH; rewrite P1 P2.
Qed.

End BigCupSeq.

(* wait for update *)

Lemma big_setU (R : Type) (idx : R) (op : Monoid.com_law idx)
  A B (F : I -> R) : [disjoint A & B] ->
  \big[op/idx]_(i in (A :|: B)) F i = 
    op (\big[op/idx]_(i in A) F i) (\big[op/idx]_(i in B) F i).
Proof.
move=>dis; rewrite (big_setID A) ; f_equal; apply eq_bigl=>x;
by rewrite !inE/= ?orbK// andb_orr andNb/=; apply/andb_idl/disjointP; rewrite disjoint_sym.
Qed.

Lemma big_setD (R : zmodType) A B (F : I -> R) :
  \sum_(i in (A :\: B)) F i = 
    (\sum_(i in A :|: B) F i) - (\sum_(i in B) F i).
Proof. by rewrite -setUDV big_setU/= ?disjointXD// addrC addKr. Qed.

Lemma subsetX_disjoint A B : (A :<=: B) = [disjoint A & ~: B].
Proof. by rewrite subset_disjoint; apply/eq_disjoint_r=>i; rewrite !inE. Qed.

Lemma disjointX_subset A B : [disjoint A & B] = (A :<=: ~: B).
Proof. by rewrite subsetX_disjoint setCK. Qed.

End SetExtra.

(* -------------------------------------------------------------------- *)
(* Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex. *)

From mathcomp Require Import finmap.

Local Open Scope fset_scope.

Notation "\bigcup_ ( m <= i < n | P ) F" :=
  (\big[@fsetU _/fset0]_(m <= i < n | P%B) F%fset) : fset_scope.
Notation "\bigcup_ ( m <= i < n ) F" :=
  (\big[@fsetU _/fset0]_(m <= i < n) F%fset) : fset_scope.
Notation "\bigcup_ ( i | P ) F" :=
  (\big[@fsetU _/fset0]_(i | P%B) F%fset) : fset_scope.
Notation "\bigcup_ i F" :=
  (\big[@fsetU _/fset0]_i F%fset) : fset_scope.
Notation "\bigcup_ ( i : t | P ) F" :=
  (\big[@fsetU _/fset0]_(i : t | P%B) F%fset) (only parsing): fset_scope.
Notation "\bigcup_ ( i : t ) F" :=
  (\big[@fsetU _/fset0]_(i : t) F%fset) (only parsing) : fset_scope.
Notation "\bigcup_ ( i < n | P ) F" :=
  (\big[@fsetU _/fset0]_(i < n | P%B) F%fset) : fset_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\big[@fsetU _/fset0]_ (i < n) F%fset) : fset_scope.

(* -------------------------------------------------------------------- *)
Section FSetMonoids.
Import Monoid.
Variable (I : choiceType).
HB.instance Definition _ := 
  isMulLaw.Build {fset I} fset0 _ (@fset0I I) (@fsetI0 I).
HB.instance Definition _ := 
  isAddLaw.Build {fset I} _ _ (@fsetIUl I) (@fsetIUr I).
End FSetMonoids.

(* ==================================================================== *)
Section FSetExtra.
Variable (I: choiceType).
Implicit Type (A B C : {fset I}).

Lemma fdisj_inf A B : [disjoint A & B] -> forall x, (x \in A) && (x \in B) = false.
Proof.
by move/fdisjointP=> dis x; case E1: (x \in A) => //=; apply negbTE; apply: dis.
Qed.

Lemma fdisjointXXP A : reflect (A = fset0) [disjoint A & A]%fset.
Proof. by apply (iffP (fsetDidPl _ _)); rewrite fsetDv=>->. Qed.

Lemma fdisjointXD A B : [disjoint A & (B `\` A)].
Proof. by apply/fdisjointP => x; apply contraTT; move/negbNE/fsetDP=>[_ H2]. Qed.

Lemma fdisjointDX A B : [disjoint (B `\` A) & A].
Proof. by apply/fdisjointP => x; move/fsetDP=>[_ H2]. Qed.

Lemma fdisjointXDg A B C: [disjoint A & B] -> [disjoint A & B `\` C].
Proof. by rewrite -!fsetI_eq0 fsetIDA => /eqP ->; rewrite fset0D. Qed.

Lemma fdisjointDXg A B C: [disjoint A & B] -> [disjoint A `\` C & B].
Proof. by rewrite ![[disjoint _ & B]]fdisjoint_sym; apply fdisjointXDg. Qed.

Lemma fsetUD A B : A `|` (B `\` A) = A `|` B.
Proof. by rewrite fsetUDl fsetDv fsetD0. Qed.

Lemma fsetUDV A B : A `|` B `\` A = B `|` A.
Proof. by rewrite fsetUD fsetUC. Qed.

Lemma fsetUDS A B : (A `|` (B `\` A)) = (B `|` (A `\` B)).
Proof. by rewrite !fsetUD fsetUC. Qed.

Lemma fsetUDSV A B : ((A `\` B) `|` B) = ((B `\` A) `|` A).
Proof. by rewrite fsetUC fsetUDS fsetUC. Qed.

Definition fset0_simp := (fset0D,fsetD0,fset0U,fsetU0,fsetI0,fset0I,fdisjointX0,
  fdisjoint0X,fsetDv,fdisjointXD,fdisjointDX).

Lemma fdisjointDI A B : [disjoint A `\` B & A `&` B].
Proof.
move: (fdisjointDX B A).
rewrite -!fsetI_eq0 [A `&` B]fsetIC fsetIA=>/eqP->. by rewrite fset0I.
Qed.

Lemma fdisjointID A B : [disjoint A `&` B & A `\` B].
Proof. by rewrite fdisjoint_sym fdisjointDI. Qed.

Lemma fsetUD_sub A B : A `<=` B -> A `|` B `\` A = B.
Proof. by rewrite fsetUD; apply/fsetUidPr. Qed.

Lemma fsubUsetPP A B C : A `<=` C -> B `<=` C -> A `|` B `<=` C.
Proof. by rewrite fsubUset=>->->. Qed.

(* wait for update *)
Lemma bigfcup_disjointP  (A: {fset I}) (J : eqType) (r: seq J) (P: pred J) (F: J -> {fset I}) :
  reflect (forall i, (i \in r) && P i -> [disjoint A & F i])
    ([disjoint A & \bigcup_(i <- r | P i) F i ]%fset).
Proof.
rewrite -fsetI_eq0 -fsubset0 big_distrr/=.
apply (iffP (bigfcupsP _ _ _ _)) =>[IH i /andP[P1 P2] | IH i P1 P2].
move: (IH i P1 P2). all: rewrite fsubset0 fsetI_eq0//.
apply IH. by rewrite P1 P2.
Qed.

End FSetExtra.

Lemma big_fsetU (R : Type) (idx : R) (op : Monoid.com_law idx) (I : choiceType) 
  A B (F : I -> R) : [disjoint A & B] ->
  \big[op/idx]_(i <- (A `|` B)) F i = 
    op (\big[op/idx]_(i <- A) F i) (\big[op/idx]_(i <- B) F i).
Proof.
move=>dis; rewrite (big_fsetID _ (mem A)); congr (op _ _); apply eq_fbigl=>x; 
by rewrite !inE/= ?orbK// andb_orl andbN/=; apply/andb_idr/fdisjointP; rewrite fdisjoint_sym.
Qed.

Lemma big_fsetD (R : zmodType) (I : choiceType) 
  A B (F : I -> R) :
  \sum_(i <- (A `\` B)) F i = 
    (\sum_(i <- A `|` B) F i) - (\sum_(i <- B) F i).
Proof.
by apply/eqP; rewrite eq_sym subr_eq -big_fsetU ?fdisjointDX//= fsetUDr fsetDv fsetD0.
Qed.

Lemma index_enum_fset (I : choiceType) (A : {fset I}) :
  perm_eq (map val (index_enum (@fset_sub_type I A)))
    (@enum_fset I A).
Proof.
have /perm_undup: map val (index_enum (@fset_sub_type I A)) =i @enum_fset I A.
  move=>i; apply eqb_iff; split; first by move=>/mapP/=[x _ ->]; case: x.
  by move=>Pi; apply/mapP=>/=; exists [` Pi] =>//; rewrite mem_index_enum.
by rewrite !undup_id// map_inj_uniq ?index_enum_uniq//; apply/val_inj.
Qed.

Lemma big_in_fsetE (T : Type) (idm : T) (op : Monoid.com_law idm) 
 (I : choiceType) A (g : I -> T):
 \big[op/idm]_(i <- (index_enum (@fset_sub_type I A))) g (fsval i) = \big[op/idm]_(i <- A) g i.
Proof. by rewrite -(big_map (@fsval _ _) predT)/=  (perm_big _ (index_enum_fset A)). Qed.
Arguments big_in_fsetE [T idm op I A].

Lemma big_fsetU_idem (R : Type) (idx : R) (op : Monoid.com_law idx)
  (I : choiceType) (A B : {fset I}) (F : I -> R) :
  idempotent op ->
   \big[op/idx]_(i <- A `|` B) F i =
   op (\big[op/idx]_(i <- A) F i) (\big[op/idx]_(i <- B) F i).
Proof.
move=>Pop.
rewrite -{1}(fsetID A B) -{1}(fsetID B A) fsetUACA fsetIC fsetUid !big_fsetU; last first.
rewrite -[X in op X _]Pop {1}fsetIC Monoid.mulmACA 
  -{5}(fsetID A B) -{5}(fsetID B A) !big_fsetU//.
1,2 : by rewrite fdisjointID.
apply/(fdisjointWl (fsubsetDl _ _))/fdisjointXD.
by rewrite fdisjointXU {1}fsetIC !fdisjointID.
Qed.

Lemma big_fsetUs_idem (R : Type) (idx : R) (op : Monoid.com_law idx)
  (I J : choiceType) (r : seq I) (P : pred I) (s : I -> {fset J}) (F : J -> R) :
  idempotent op ->
   \big[op/idx]_(i <- r | P i) (\big[op/idx]_(j <- s i) F j) =
   \big[op/idx]_(j <- \bigcup_(i <- r | P i) s i) F j.
Proof.
move=>Pop.
elim/big_rec2 : _; first by rewrite big_seq_fsetE big_fset0.
by move=>i y1 y2 Pi ->; rewrite big_fsetU_idem.
Qed.

(* theory of fsetT, fsetC ... *)
Section FSetFinType.
Context {I : finType}.
Implicit Type (A B C : {fset I}).

Definition fsetT := [fset x | x : I].
Lemma in_fsetT (x : I) : x \in fsetT. 
Proof. by rewrite inE. Qed.

Lemma enum_fsetT_perm :
  perm_eq (enum (Finite.clone [fset x | x : I]%type _))
    (map (fun x => [` in_fsetT x]) (enum I)).
Proof.
have: (enum (Finite.clone [fset x | x : I]%type _)) =i (map (fun x => [` in_fsetT x]) (enum I)).
move=>/=i; rewrite mem_enum/= inE; symmetry; apply/mapP.
destruct i=>/=; exists fsval. by rewrite mem_enum.
by rewrite (eq_irrelevance fsvalP (in_fsetT fsval)).
move=>/perm_undup; rewrite !undup_id// ?enum_uniq// map_inj_uniq ?enum_uniq//.
by move=>i j /(f_equal val).
Qed.

Definition fsetC A := (nosimpl fsetT `\` A).
Notation "~` A" := (fsetC A) (at level 35, A at level 35, right associativity) : fset_scope.

Lemma fsubsetT A : A `<=` fsetT.
Proof. by apply/fsubsetP=>i; rewrite in_fsetT. Qed.

Lemma fsubTset A : (fsetT `<=` A) = (A == fsetT).
Proof. by rewrite eqEfsubset fsubsetT. Qed.

Lemma fproperT A : (A `<` fsetT) = (A != fsetT).
Proof. by rewrite fproperEneq fsubsetT andbT. Qed.

Lemma fsetTU A : fsetT `|` A = fsetT.
Proof. by apply/fsetP => x; rewrite !inE orTb. Qed.

Lemma fsetUT A : A `|` fsetT = fsetT.
Proof. by rewrite fsetUC fsetTU. Qed.

Lemma fsetTI A : fsetT `&` A = A.
Proof. by apply/fsetP => x; rewrite !inE andTb. Qed.

Lemma fsetIT A : A `&` fsetT = A.
Proof. by rewrite fsetIC fsetTI. Qed.

Lemma fsetDT A : A `\` fsetT = fset0.
Proof. by apply/fsetP=> x; rewrite !inE. Qed.

Lemma fsetTD A : fsetT `\` A = ~` A.
Proof. by apply/fsetP=> x; rewrite !inE andbT. Qed.

Lemma in_fsetC x A : (x \in ~` A) = (x \notin A).
Proof. by rewrite inE in_fsetT andbT. Qed.

Definition in_fset := (in_fset, in_fsetC, in_fsetT).

Lemma fsetCP x A : reflect (~ x \in A) (x \in ~` A).
Proof. by rewrite !in_fset; apply: negP. Qed.

Lemma fsetCK : involutive fsetC.
Proof. by move=> A; apply/fsetP=> x; rewrite !in_fset negbK. Qed.

Lemma fsetC_inj : injective fsetC.
Proof. exact: can_inj fsetCK. Qed.

Lemma fsubsetX_disjoint A B : (A `<=` B) = [disjoint A & ~` B].
Proof. by rewrite -fsetI_eq0 fsetIDA fsetIT fsetD_eq0. Qed.

Lemma fdisjointX_subset A B : [disjoint A & B] = (A `<=` ~` B).
Proof. by rewrite fsubsetX_disjoint fsetCK. Qed.

Lemma fpowersetCE A B : (A \in fpowerset (~` B)) = [disjoint A & B].
Proof. by rewrite fpowersetE fdisjointX_subset. Qed.

Lemma fsetCS A B : (~` A `<=` ~` B) = (B `<=` A).
Proof. by rewrite !fsubsetX_disjoint fsetCK fdisjoint_sym. Qed.

Lemma fsetCU A B : ~` (A `|` B) = ~` A `&` ~` B.
Proof. by apply/fsetP=> x; rewrite !inE !andbT negb_or. Qed.

Lemma fsetCI A B : ~` (A `&` B) = ~` A `|` ~` B.
Proof. by apply/fsetP=> x; rewrite !inE !andbT negb_and. Qed.

Lemma fsetUCr A : A `|` ~` A = fsetT.
Proof. by apply/fsetP=> x; rewrite !inE andbT orbN. Qed.

Lemma fsetICr A : A `&` ~` A = fset0.
Proof. by apply/fsetP=> x; rewrite !inE andbT andbN. Qed.

Lemma fsetC0 : ~` fset0 = fsetT.
Proof. by apply/fsetP=> x; rewrite !inE. Qed.

Lemma fsetCT : ~` fsetT = fset0.
Proof. by rewrite -fsetC0 fsetCK. Qed.

Lemma fproperC A B : (~` B `<` ~` A) = (A `<` B).
Proof. by rewrite !fproperE !fsetCS. Qed.

Lemma fdisjointXC A : [disjoint A & ~` A].
Proof. by rewrite -fsetI_eq0 fsetICr. Qed.

Lemma fdisjointCX A : [disjoint ~` A & A].
Proof. by rewrite fdisjoint_sym fdisjointXC. Qed.

End FSetFinType.

Notation "~` A" := (fsetC A) (at level 35, A at level 35, right associativity) : fset_scope.

Lemma big_fsetT (R : Type) (idx : R) (op : Monoid.com_law idx) 
  (I : finType) (F : I -> R) :
  \big[op/idx]_i F i = \big[op/idx]_(i : @fsetT I) F (val i).
Proof.
by rewrite /index_enum /enum_fset/= -!enumT/= 
  (perm_big _ (enum_fsetT_perm)) [RHS]big_map/=.
Qed.
Arguments big_fsetT [R idx op I].

Lemma big_seq_fsetT (R : Type) (idx : R) (op : Monoid.com_law idx) 
  (I : finType) (F : I -> R) :
  \big[op/idx]_i F i = \big[op/idx]_(i <- @fsetT I) F i.
Proof. by rewrite big_fsetT big_seq_fsetE. Qed.
Arguments big_seq_fsetT [R idx op I].