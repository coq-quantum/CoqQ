(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra perm.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
From mathcomp.real_closed Require Import mxtens.
Require Import xvector mcextra mcaextra mxpred notation.

(*****************************************************************************)
(*                     Formalization of hermitian space                      *)
(* ------------------------------------------------------------------------- *)
(*          hermitianType == vectType over complex number C equipped with    *)
(*                           an inner product                                *)
(*                           The HB class is HermitianSpace                  *)
(*                chsType == non-degenerated (0 < dim) hermitianType with    *)
(*                           default orthonormal canonical basis             *)
(*                           The HB class is CanonicalHermitianSpace         *)
(* ------------------------------------------------------------------------- *)
(* Definition and Theory                                                     *)
(*      define and prove correct the Gram–Schmidt process                    *)
(*      define conjugate, outer product of vector                            *)
(*      define adjoint, conjugate and transpose of linear function           *)
(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import VectorInternalTheory.
(* ------------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* ------------------------------------------------------------------------- *)
(* Local Open Scope complex_scope. *)
Local Open Scope ring_scope.

Context (R : realType) (C := R[i]).

HB.mixin Record Vector_isHermitianSpace T of Vector C T := {
  dotp : T -> T -> C;
  ge0_dotp    : forall v, 0 <= dotp v v;
  dotp_eq0    : forall v, (dotp v v == 0) = (v == 0);
  conj_dotp   : forall u v, (dotp u v)^* = dotp v u;
  linear_dotp : forall u, linear_for *%R (dotp u);
}.

#[short(type="hermitianType")]
HB.structure Definition HermitianSpace :=
  { T of Vector C T & Vector_isHermitianSpace T }.

Module HermitianSpaceExports.
#[deprecated(since="mathcomp 2.0.0", note="Use HermitianSpace.clone instead.")]
Notation "[ 'hermitianType' 'of' T 'for' cT ]" := (HermitianSpace.clone T%type cT)
  (at level 0, format "[ 'hermitianType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use HermitianSpace.clone instead.")]
Notation "[ 'hermitianType' 'of' T ]" := (HermitianSpace.clone T%type _)
  (at level 0, format "[ 'hermitianType'  'of'  T ]") : form_scope.
End HermitianSpaceExports.
HB.export HermitianSpaceExports.

(* ------------------------------------------------------------------------- *)

Notation "[< u ; v >]" := (dotp u v).
Notation antilinear f := (linear_for (Num.conj_op \; *:%R) f).

(* ------------------------------------------------------------------------- *)
Section HermitianSpaceTheory.
Context {E : hermitianType}.

Implicit Types (u v w : E) (a b : C).

Lemma dotp00 : [< (0 : E); 0 >] = 0.
Proof. by apply/eqP; rewrite dotp_eq0. Qed.

HB.instance Definition _ u := GRing.isLinear.Build C E C
  *%R (dotp u) (linear_dotp u).

Lemma antilinear_dotpr u : linear_for (Num.conj_op \; *%R) ((dotp)^~ u).
Proof. by move=>a v w /=; rewrite -conj_dotp linearP/= rmorphD/= rmorphM/= !conj_dotp. Qed.

HB.instance Definition _ := bilinear_isBilinear.Build C E E C
  (Num.conj_op \; *%R) *%R dotp (antilinear_dotpr, linear_dotp).

Lemma dot0p u : [< 0; u >] = 0. Proof. exact: linear0l. Qed.
Lemma dotpNl w : {morph (dotp^~ w) : u / -u}. Proof. exact: linearNl. Qed.
Lemma dotpBl w : {morph (dotp^~ w) : u v / u - v}. Proof. exact: linearBl. Qed.
Lemma dotpDl w : {morph (dotp^~ w) : u v / u + v}. Proof. exact: linearDl. Qed.
Lemma dotpMnl w n : {morph (dotp^~ w) : u / u *+ n}. Proof. exact: linearMnl. Qed.
Lemma dotpMNnl w n : {morph (dotp^~ w) : u / u *- n}. Proof. exact: linearMNnl. Qed.
Lemma dotp0 u : [< u; 0 >] = 0. Proof. exact: linear0. Qed.
Lemma dotpNr w : {morph dotp w : u / -u}. Proof. exact: linearN. Qed.
Lemma dotpBr w : {morph dotp w : u v / u - v}. Proof. exact: linearB. Qed.
Lemma dotpDr w : {morph dotp w : u v / u + v}. Proof. exact: linearD. Qed.
Lemma dotpMnr w n : {morph dotp w : u / u *+ n}. Proof. exact: linearMn. Qed.
Lemma dotpMNnr w n : {morph dotp w : u / u *- n}. Proof. exact: linearMNn. Qed.

Lemma dotpZl x u v : [< x *: u; v >] = x^* * [< u; v >].
Proof. exact: linearZl_LR. Qed.

Lemma dotpPl x u v w : [< x *: u + v ; w >] = x^* * [< u; w >] + [< v; w >].
Proof. exact: linearPl. Qed.

Lemma dotp_suml (I : Type) (r : seq I) P (F : I -> E) u :
  [< \sum_(v <- r | P v) F v; u >] = \sum_(v <- r | P v) [< F v; u >].
Proof. exact: linear_suml. Qed.

Lemma dotpZr x u v : [< u; x *: v >] = x * [< u; v >].
Proof. exact: linearZ. Qed.

Lemma dotpPr x u v w : [< u; x *: v + w >] = x * [< u; v >] + [< u; w >].
Proof. exact: linearP. Qed.

Lemma dotp_sumr (I : Type) (r : seq I) P (F : I -> E) u :
  [< u; \sum_(v <- r | P v) F v >] = \sum_(v <- r | P v) [< u; F v >].
Proof. exact: linear_sum. Qed.

Lemma dotpD u v : [< u + v; u + v >] =
  [< u; u >] + [< v; v >] + ([< u; v >] + [< u; v >]^*).
Proof.
rewrite !(dotpDr, dotpDl) conj_dotp -!addrA; congr (_ + _).
by rewrite [RHS]addrC addrCA !addrA.
Qed.

Lemma real_dotpp u : [< u; u >] \is Num.real.
Proof. by apply/CrealP; rewrite conj_dotp. Qed.

End HermitianSpaceTheory.

(* ========================================================================= *)
Section CauchySchwartz.
Context {E : hermitianType}.

Local Notation "`<| u |>" := (sqrtC [< u; u >]) (at level 2).

Lemma CauchySchwartz (u v : E) :
  `|[< u; v >]| ^+ 2 <= [< u; u >] * [< v; v >].
Proof.
case: (v =P 0) => [->|/eqP nz_v].
- by rewrite dotp0 normr0 expr0n /= dotp0 mulr0.
pose P (t : C) : C := `<|u + t *: v|>^+2.
have PE t: P t = `<|u|>^+2 + t * [< u; v >]
    + t^* * [< u; v >]^* + `|t|^+2 * `<|v|>^+2.
- rewrite /P !sqrtCK !(dotpDl, dotpDr) !addrA !(dotpZr, dotpZl).
  by rewrite conj_dotp !mulrA normCK.
pose t0 : C := - ([< u; v >]^* / `<| v |>^+2).
pose K := `|[< u; v >]|^+2 / `<| v |>^+2.
have {}PE: P t0 = `<|u|>^+2 - K - K + K.
- rewrite {}PE; congr (_ + _ + _ + _); rewrite {}/K {}/t0.
  - by rewrite mulNr mulrAC -normCKC.
  - rewrite rmorphN !mulNr rmorphM mulrAC conjCK -normCK.
    by rewrite conj_Creal // rpredV sqrtCK real_dotpp.
  - rewrite normrN normrM normfV !sqrtCK norm_conjC.
    rewrite exprMn exprVn -mulrA; congr (_ * _).
    rewrite ger0_norm ?ge0_dotp // mulrC expr2 invfM !mulrA.
    by rewrite divff ?div1r // dotp_eq0.
have: 0 <= P t0 by rewrite /P sqrtCK ge0_dotp.
rewrite PE addrNK subr_ge0 {PE}/K !sqrtCK ler_pdivrMr //.
by rewrite lt0r ge0_dotp dotp_eq0 nz_v.
Qed.

Lemma CauchySchwartz_sqrt (u v : E) :
  `|[< u; v >]| <= sqrtC [< u; u >] * sqrtC [< v; v >].
Proof.
rewrite -ler_sqr; try by rewrite nnegrE ?mulr_ge0 // sqrtC_ge0 ge0_dotp.
rewrite exprMn !sqrtCK; exact: CauchySchwartz.
Qed.

End CauchySchwartz.

(* ========================================================================= *)
Section HermitianNormedSpace.
Context {E : hermitianType}.

Definition hnorm (u : E) := sqrtC [< u; u >].

Local Lemma hnormE_r (u : E) : hnorm u = sqrtC `|[<u; u>]|.
Proof. by rewrite /hnorm ger0_norm // ge0_dotp. Qed.

Program Definition hermitian_normedZmodMixin :=
  @Num.Zmodule_isNormed.Build C E hnorm _ _ _ _.

Next Obligation.
move=> /= u v; suff: hnorm (u + v) <= hnorm u + hnorm v by [].
(* rewrite -[lec _ _]/(hnorm (u + v) <= hnorm u + hnorm v). *)
rewrite -ler_sqr; try by rewrite nnegrE 1?addr_ge0 // sqrtC_ge0 ge0_dotp.
rewrite !hnormE_r sqrrD !sqrtCK !(dotpDr, dotpDl) mulr2n !addrA.
apply: (le_trans (ler_normD _ _)); rewrite lerD2r.
rewrite -!addrA; apply: (le_trans (ler_normD _ _)); rewrite lerD2l.
apply: (le_trans (ler_normD _ _)); rewrite -!hnormE_r.
rewrite -conj_dotp norm_conjC -!mulr2n lerMn2r /=.
exact: CauchySchwartz_sqrt.
Qed.

Next Obligation.
by move=> x /eqP; rewrite sqrtC_eq0 dotp_eq0 => /eqP.
Qed.

Next Obligation.
move=> x n; elim: n => [|n ih].
- by rewrite /hnorm !mulr0n dotp00 sqrtC0.
rewrite !mulrS -{}ih; apply: (pexpIrn (lt0n 2));
  try by rewrite nnegrE 1?addr_ge0 // sqrtC_ge0 ge0_dotp.
rewrite sqrrD !sqrtCK dotpD [RHS]addrAC; congr (_ + _).
rewrite {2}linearMn rmorphMn conj_dotp -linearMn /= -mulr2n.
congr (_ *+ _); rewrite /hnorm ![in RHS](dotpMnr, dotpMnl).
rewrite -mulrnA -mulr_natr natrM -expr2 sqrtCM.
- by rewrite nnegrE ge0_dotp.
- by rewrite nnegrE -realEsqr realn.
by rewrite mulrA -expr2 sqrCK ?ler0n // sqrtCK mulr_natr -dotpMnr.
Qed.

Next Obligation.
by move=> x; rewrite /hnorm !(dotpNl, dotpNr) opprK.
Qed.

HB.instance Definition _ := hermitian_normedZmodMixin.

Lemma hnormE (u : E) : `|u| = sqrtC [< u; u >].
Proof. by []. Qed.

Lemma hnormZ (k : C) (u : E) : `|k *: u| = `|k| * `|u|.
Proof.
rewrite hnormE dotpZl dotpZr mulrA sqrtCM.
- by rewrite nnegrE -normCKC -realEsqr normr_real.
- by rewrite nnegrE ge0_dotp.
- by rewrite [_^* * _]mulrC -normC_def -hnormE.
Qed.

Lemma dotp_norm (u : E) : [< u; u >] = `|u|^+2.
Proof. by rewrite hnormE sqrtCK. Qed.

(* norm and dot compared to 1 *)
Lemma hnorm_le1 v : `|v| <= 1 = ([< v ; v >] <= 1).
Proof. by rewrite dotp_norm -{2}(expr1n _ 2%N) ler_pXn2r// nnegrE. Qed.
Lemma hnorm_eq1 v : `|v| == 1 = ([<v ; v>] == 1).
Proof. by rewrite dotp_norm -{2}(expr1n _ 2%N) eqrXn2. Qed.

End HermitianNormedSpace.

(* ========================================================================= *)
Section Orthonormal.
Context {E : hermitianType}.

Definition orthonormal (vs : seq E) :=
  [forall i : 'I_(size vs),
    [forall j : 'I_(size vs),
      [< vs`_i; vs`_j >] == (i == j)%:R]].

Lemma orthonormalP (vs : seq E) :
  reflect
    (forall i j, (i < size vs)%N -> (j < size vs)%N ->
       [< vs`_i; vs`_j >] = (i == j)%:R)
    (orthonormal vs).
Proof. apply: (iffP idP) => [|h].
- move=> /'forall_'forall_eqP /= h i j lti ltj.
  by apply: (h (Ordinal lti) (Ordinal ltj)).
- by apply/'forall_'forall_eqP=> -[i lti] [j ltj]; apply: h.
Qed.

Lemma orthonormal_nil : orthonormal [::].
Proof. by apply/orthonormalP. Qed.

Lemma orthonormal_cons v vs :
     orthonormal vs
  -> {in vs, forall u, [< u; v >] = 0}
  -> [< v; v >] = 1
  -> orthonormal (v :: vs).
Proof.
move=> on_vs idp_v_vs nmd_v; apply/orthonormalP.
move=> i j /=; rewrite !ltnS; wlog: i j / (i <= j)%N => [wlog cpi cpj|].
- case: (leqP i j) => [?|/ltnW le_ji]; first by apply/wlog.
  by rewrite [X in (_ X)%:R]eq_sym -[_%:R]conjC_nat -conj_dotp wlog.
move=> + _; case: i j => [|i] [|j] //=; last rewrite ltnS.
- by move=> _ lt_j_vs; rewrite (rwP eqP) -conjC_eq0 conj_dotp idp_v_vs 1?mem_nth.
- move=> /[swap] /[dup] lt_j_vs /[swap] /leq_ltn_trans /[apply] lt_i_vs.
  by apply/orthonormalP.
Qed.

Lemma orthonormal_perm us vs :
     perm_eq us vs
  -> orthonormal us
  -> orthonormal vs.
Proof.
rewrite perm_sym => /(tuple_permP (s := vs) (t := in_tuple us)) [p vsE].
move/orthonormalP => on_us; apply/orthonormalP=> i j.
rewrite {1 2}vsE size_tuple => lti ltj.
have /= := on_us (p (Ordinal lti)) (p (Ordinal ltj)).
rewrite (inj_eq (inj_comp (@ord_inj _) perm_inj)) -val_eqE /= => <- //.
suff vs_nth k (h : (k < size us)%N) : vs`_k = us`_(p (Ordinal h)).
- by congr [< _; _ >]; apply/vs_nth.
by rewrite vsE (nth_mktuple _ _ (Ordinal h)) (tnth_nth 0).
Qed.

Lemma orthonormal_nz v vs : orthonormal vs -> v \in vs -> v != 0.
Proof.
move/orthonormalP=> on_vs /(nthP 0)[i lti <-].
by rewrite -dotp_eq0 on_vs // eqxx oner_eq0.
Qed.

Lemma orthonormal_uniq vs : orthonormal vs -> uniq vs.
Proof.
move=> /[dup] => on_vs; apply/contraLR => /uniqPn.
move=> /(_ 0)[i [j]] [lt_ij ltj eq]; apply/negP.
move=> /orthonormalP /(_ i j (ltn_trans lt_ij ltj) ltj).
rewrite eq ltn_eqF //= (rwP eqP) dotp_eq0; apply/negP => {i lt_ij eq}.
by apply/(orthonormal_nz on_vs)/mem_nth.
Qed.

Lemma orthonormal_dotp vs w1 w2 :
  orthonormal vs -> w1 \in vs -> w2 \in vs -> [< w1; w2 >] = (w1 == w2)%:R.
Proof.
move=> /[dup] on_vs /orthonormalP=> on_vsP /(nthP 0)[k1 lt1 <-].
move=> /(nthP 0)[k2 lt2 <-]; rewrite on_vsP // nth_uniq //.
by apply/orthonormal_uniq.
Qed.

Definition onbasis_of (A : {vspace E}) (vs : seq E) :=
  basis_of A vs && orthonormal vs.
End Orthonormal.

(* ========================================================================= *)
Section GramSchmidt.
Context {E : hermitianType}.

Definition normd (u : E) := `|u|^-1 *: u.

Lemma normd0 : normd 0 = 0.
Proof. by rewrite /normd scaler0. Qed.

Lemma norm_normd (u : E) : `|normd u| = (u != 0)%:R.
Proof.
case: eqP=> /= [->|/eqP nz_u]; first by rewrite normd0 normr0.
by  rewrite /normd hnormZ mulrC normfV normr_id divff ?normr_eq0.
Qed.

Lemma dotp_norml (u v : E) :
  [< normd u; v >] = `|u|^-1 * [< u; v >].
Proof. by rewrite /normd dotpZl fmorphV conj_Creal ?normr_real. Qed. (* norm_conjC *)

Lemma dotp_normr (u v : E) :
  [< u; normd v >] = `|v|^-1 * [< u; v >].
Proof. by rewrite /normd dotpZr. Qed.

Lemma span_normd (x : E) : (<[normd x]> = <[x]>)%VS.
Proof.
case: (x =P 0) => [->|/eqP nz_x]; first by rewrite normd0.
by rewrite /normd spanZ // invr_eq0 normr_eq0.
Qed.

Definition GramSchmidt (vs : seq E) :=
  foldr (fun v us => normd (v - \sum_(u <- us) [< u; v >] *: u) :: us) [::] vs.

Lemma GramSchmidt_nil : GramSchmidt [::] = [::].
Proof. by []. Qed.

Lemma GramSchmidt_cons v vs : GramSchmidt (v :: vs) =
  normd (v - \sum_(u <- GramSchmidt vs) [< u; v >] *: u) :: GramSchmidt vs.
Proof. by []. Qed.

Lemma span_consD (u v : E) (vs : seq E) :
  v \in << vs >>%VS -> << (u + v)%R :: vs >>%VS = << u :: vs >>%VS.
Proof.
move=> vin; rewrite (rwP eqP) eqEsubv; apply/andP; split.
- rewrite span_cons subv_add; apply/andP; split; last first.
  - by apply/sub_span/(@mem_behead _ (_ :: vs)).
  by rewrite -memvE span_cons memv_add // memv_line.
rewrite span_cons subv_add; apply/andP; split; last first.
- by apply/sub_span/(@mem_behead _ (_ :: vs)).
rewrite span_cons; apply/memv_addP.
exists (u + v); first by rewrite memv_line.
by exists (-v); rewrite (addrK, rpredN).
Qed.

Lemma GramSchmidt_size (vs : seq E) : size (GramSchmidt vs) = size vs.
Proof. by elim: vs => /= [|v vs ->]. Qed.

Lemma GramSchmidt_span (vs : seq E) : << GramSchmidt vs >>%VS = << vs >>%VS.
Proof.
elim: vs => [|v vs ih] //=; rewrite span_cons span_normd.
rewrite -span_cons span_consD; last first.
- by rewrite -[in LHS]cat1s -[in RHS]cat1s !span_cat ih.
rewrite rpredN big_seq rpred_sum // => x xin.
by apply/rpredZ/memv_span.
Qed.

Lemma GramSchmidt_free (vs : seq E) : free (GramSchmidt vs) = free vs.
Proof. by rewrite /free GramSchmidt_size GramSchmidt_span. Qed.

Lemma GramSchmidt_basis (A : {vspace E}) (vs : seq E) :
  basis_of A (GramSchmidt vs) = basis_of A vs.
Proof. by rewrite /basis_of GramSchmidt_span GramSchmidt_free. Qed.

Lemma GramSchmidt_orthonormal (vs : seq E) :
  free vs -> orthonormal (GramSchmidt vs).
Proof.
elim: vs => [|v vs ih] hfree.
- by rewrite GramSchmidt_nil; apply/orthonormal_nil.
move: hfree; rewrite free_cons => /andP[vindep /[dup] free_vs {}/ih ih].
rewrite GramSchmidt_cons; apply: orthonormal_cons => //.
- move=> w win; rewrite (rwP eqP) dotp_normr mulf_eq0.
  apply/orP; right; apply/eqP; rewrite linearB linear_sum /=.
  move/perm_to_rem: (win) => /(perm_big _) -> /=.
  rewrite big_cons linearZ /= (orthonormal_dotp ih win win) //.
  rewrite eqxx mulr1 opprD addrA subrr sub0r (rwP eqP) oppr_eq0.
  rewrite big_seq big1 // => x xin; rewrite dotpZr.
  rewrite [[< w; x >]](orthonormal_dotp ih win).
  - by apply: mem_rem xin.
  suff /negbTE->: w != x by rewrite mulr0.
  apply/contraTneq: xin => ->; rewrite mem_rem_uniqF //.
  apply/free_uniq; rewrite /free GramSchmidt_span.
  by rewrite GramSchmidt_size.
- rewrite dotp_norm (rwP eqP) sqrf_eq1; apply/orP; left.
  rewrite norm_normd -(rwP eqP) -[1 in RHS]/1%:R.
  congr _%:R; rewrite (rwP eqP) eqb1 subr_eq0.
  apply/contra: vindep => /eqP->; rewrite big_seq.
  apply: rpred_sum=> w /memv_span; rewrite GramSchmidt_span.
  by move=> win; apply/rpredZ.
Qed.

Lemma vonbasis_proof (A : {vspace E}) :
  { vs : (\dim A).-tuple E | onbasis_of A vs }.
Proof.
pose vs := GramSchmidt (vbasis A); have eq: size vs = \dim A.
- by rewrite GramSchmidt_size size_vbasis.
exists (tcast eq (in_tuple vs)); case: (\dim A) / eq => /=.
apply/andP; split; first by rewrite GramSchmidt_basis vbasisP.
by apply/GramSchmidt_orthonormal/(basis_free (vbasisP A)).
Qed.

Definition vonbasis (A : {vspace E}) : (\dim A).-tuple E :=
  nosimpl (projT1 (vonbasis_proof A)).

Lemma vonbasisP (A : {vspace E}) : onbasis_of A (vonbasis A).
Proof. by rewrite /vonbasis; case: vonbasis_proof. Qed.

Lemma ort_free {n} (X: n.-tuple E) : orthonormal X -> free X.
Proof.
move/'forall_'forall_eqP; rewrite size_tuple => ort.
apply/freeP=> K P i; rewrite -(dotp0 X`_i) -{2}P dotp_sumr.
rewrite (bigD1 i) //= big1.
by move=> j /negPf nji; rewrite dotpZr ort eq_sym nji mulr0.
by rewrite dotpZr ort eqxx mulr1 addr0.
Qed.

Lemma ort_onb {n} (X: n.-tuple E) :
  orthonormal X -> onbasis_of <<X>> X.
Proof.
by move=>ort; apply/andP; split=>//; apply/andP; split=>//; apply ort_free.
Qed.

Lemma ort_onbf {n} (X: n.-tuple E) :
  n = \dim {:E} -> orthonormal X -> onbasis_of fullv X.
Proof. 
move=> ndim ort; apply/andP; split => //.
rewrite basisEfree; apply/andP; split; first by apply ort_free.
apply/andP; split; first by apply subvf.
by rewrite size_tuple ndim leqnn.
Qed.

End GramSchmidt.

(* ------------------------------------------------------------------------- *)
Section DotP_ONB.
Context {E : hermitianType}.

Lemma dotp_onb {n} (A : {vspace E}) (u v : E) (vs : n.-tuple E) :
  u \in A -> v \in A -> onbasis_of A vs ->
    [< u; v >] = \sum_i (coord vs i u)^* * coord vs i v.
Proof.
move=> uA vA /andP[bsAvs onAvs]; pose X w i := coord vs i w.
rewrite [in LHS](coord_basis bsAvs uA) [in LHS](coord_basis bsAvs vA).
transitivity (\sum_i (\sum_j (X u i)^* * X v j * [< vs`_i; vs`_j >])).
- rewrite dotp_suml; apply: eq_bigr=> i _.
  rewrite dotp_sumr; apply: eq_bigr=> j _.
  by rewrite !(dotpZl, dotpZr) -!/(X _ _) mulrA.
rewrite pair_big /= (bigID (fun ij => ij.1 == ij.2)) /=.
rewrite [X in _+X]big1 ?addr0 => [[/= i j] ne_ij|].
- rewrite (orthonormalP _ onAvs) ?size_tuple //.
  by rewrite (inj_eq (@ord_inj _)) (negbTE ne_ij) mulr0.
rewrite (reindex (fun i : 'I_n => (i, i))) /=.
- by exists (fun ij => ij.1) => // [[i j] /eqP /= <-].
apply: eq_big => [i|i _]; first by rewrite eqxx.
by rewrite (orthonormalP _ onAvs) ?size_tuple // eqxx mulr1.
Qed.

Lemma intro_dotl (u v: E) : 
  (forall t, [< t ; u >] = [< t ; v >]) <-> u = v.
Proof.
move: (vonbasisP {: E}); set e := (vonbasis fullv) => P.
split; last by move=> ->. move=> P1.
have H: basis_of fullv e. by move/andP: P=> [ll lr].
rewrite (coord_basis H (memvf u)) (coord_basis H (memvf v)).
apply eq_bigr=> i _; suff ->: coord e i u = coord e i v. by [].
move: (P1 e`_i); suff E1: forall x, [< e`_i ; x >] = coord e i x. by rewrite !E1.
move=> x; have P2: free e. by move/andP: H=>[ll lr].
rewrite (dotp_onb (memvf e`_i) (memvf x) P) (bigD1 i) //= big1.
by move=> j /negPf nji; rewrite coord_free // eq_sym nji conjC0 mul0r.
by rewrite coord_free // eqxx conjC1 mul1r addr0.
Qed.

Lemma intro_dotr (u v: E) : 
  (forall t, [< u ; t >] = [< v ; t >]) <-> u = v.
Proof.
split; [| move=>-> //]; rewrite -intro_dotl=> P t.
by apply (can_inj conjCK); rewrite !conj_dotp.
Qed.

End DotP_ONB.

(* hermitianType with a given orthonormal basis *)
(* this orthonormal basis is regarded as computational basis *)
(* the vector/matrix form: c2h (delta_mx i 0) = eb_op i *)

HB.mixin Record HermitianSpace_isCanonical E of HermitianSpace E := {
  eb : 'I_(dim E) -> E;
  eb_dot : forall i j, [< eb i; eb j >] = (i == j)%:R;
  dim_proper : (dim E > 0)%N;
}.

#[short(type="chsType")]
HB.structure Definition CanonicalHermitianSpace :=
  { T of HermitianSpace T & HermitianSpace_isCanonical T }.

Module CanonicalHermitianSpaceExports.
#[deprecated(since="mathcomp 2.0.0", note="Use CanonicalHermitianSpace.clone instead.")]
Notation "[ 'chsType' 'of' T 'for' cT ]" := (CanonicalHermitianSpace.clone T%type cT)
  (at level 0, format "[ 'chsType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use CanonicalHermitianSpace.clone instead.")]
Notation "[ 'chsType' 'of' T ]" := (CanonicalHermitianSpace.clone T%type _)
  (at level 0, format "[ 'chsType'  'of'  T ]") : form_scope.
End CanonicalHermitianSpaceExports.
HB.export CanonicalHermitianSpaceExports.

Section LfunAlgebraComp.

Variables (R : comRingType) (vT : vectType R).
Hypothesis vT_proper : (dim vT > 0) %N.

Definition lfun_comp_lalgMixin := GRing.Lmodule_isLalgebra.Build R
  (@lfun_comp_ringType R vT vT_proper) (fun k x y => comp_lfunZl k x y).
Definition lfun_comp_lalgType : lalgType R :=
  HB.pack 'End(vT) (@lfun_comp_ringType R vT vT_proper) lfun_comp_lalgMixin.

Definition lfun_comp_algMixin := GRing.Lalgebra_isAlgebra.Build R lfun_comp_lalgType
  (fun k x y => comp_lfunZr k x y).
Definition lfun_comp_algType : algType R :=
  HB.pack 'End(vT) lfun_comp_lalgType lfun_comp_algMixin.

End LfunAlgebraComp.

Section ChsTypeBasic.
Context {E : chsType}.

#[non_forgetful_inheritance]
HB.instance Definition _ := Num.NormedZmodule.copy E
  ((E : hermitianType) : normedZmodType C).

Lemma dim_proper_cast : (dim E - 1).+1 = dim E.
Proof. by rewrite -addn1 subnK// dim_proper. Qed.

Canonical chsf_comp_ringType := lfun_comp_ringType (@dim_proper E).
HB.instance Definition _ := GRing.SemiRing.copy 'End(E) ('End(E):ringType).
Canonical chsf_comp_lalgType := lfun_comp_lalgType (@dim_proper E).
Canonical chsf_comp_algType := lfun_comp_algType (@dim_proper E).

End ChsTypeBasic.

(* any proper Hermitian Type can construct a chsType *)
(* we do not use this; just show that we can construct chsType *)
Section ConstructiveChsType.
Context {E : hermitianType}.
Hypothesis (dp : (dim E > 0)%N).

Let ce := HermitianSpace.Pack (HermitianSpace.class E).
Definition hermitian_eb i := (tcast (dimvf E) (vonbasis {: E})) ~_ i.

Lemma orthonormal_tupleP n (vs : n.-tuple E) :
  reflect
    (forall i j, [< vs~_i; vs~_j >] = (i == j)%:R)
    (orthonormal vs).
Proof.
apply/(iffP (orthonormalP _))=>IH i j.
by rewrite !(tnth_nth 0) IH// size_tuple.
rewrite size_tuple=>Pi Pj. move: (IH (Ordinal Pi) (Ordinal Pj)).
by rewrite !(tnth_nth 0).
Qed.

Lemma hermitian_eb_onb (i j : 'I_(dim ce)) :
  [< hermitian_eb i; hermitian_eb j >] = (i == j)%:R.
Proof.
move: (vonbasisP {:E})=>/andP[] _/orthonormal_tupleP IH.
by rewrite /hermitian_eb !tcastE IH (inj_eq (@cast_ord_inj _ _ _)).
Qed.

Definition hermitian_chsMixin := HermitianSpace_isCanonical.Build ce hermitian_eb_onb dp.
Definition hermitian_chsType : chsType := HB.pack E hermitian_chsMixin.

End ConstructiveChsType.

(* different from v2r using row vector, h2c usese column vector *)

Definition tuple_eb {E : chsType} := [tuple i => eb i : E].
HB.lock Definition v2hU {E : chsType} := (b2mx (@tuple_eb E))^T.
HB.lock Definition h2vU {E : chsType} := invmx (@v2hU E).
HB.lock Definition h2c {E : chsType} (u : E) := h2vU *m (v2r u)^T.
HB.lock Definition c2h {E : chsType} u : E := r2v (v2hU *m u)^T.
HB.lock Definition conjv {E : chsType} (u : E) := c2h (h2c u)^*m.
HB.lock Definition h2mx {E F : chsType} (f : 'Hom(E,F)) := h2vU *m (f2mx f)^T *m v2hU.
HB.lock Definition mx2h {E F : chsType} f : 'Hom(E,F) := Hom (v2hU *m f *m h2vU)^T.
HB.lock Definition outp {E F : chsType} (v : F) (u : E) : 'Hom(E,F) := mx2h (h2c v *m (h2c u)^*t).
HB.lock Definition adj_lfun {E F : chsType} (f : 'Hom(E,F)) := mx2h (h2mx f)^*t.
HB.lock Definition tr_lfun {E F : chsType} (f : 'Hom(E,F)) := mx2h (h2mx f)^T.
HB.lock Definition conj_lfun {E F : chsType} (f : 'Hom(E,F)) := mx2h (h2mx f)^*m.

Notation "v ^*v" := (conjv v) : lfun_scope.
Notation "[> u ; v <]" := (outp u v).
Notation "f ^A" := (adj_lfun f) : lfun_scope.
Notation "f ^C" := (conj_lfun f) : lfun_scope.
Notation "f ^T" := (tr_lfun f) : lfun_scope.

Section HermitianIso.
Context {E : chsType}.
Implicit Type (i j : 'I_(dim E)).

Local Notation v2hU := (@v2hU E).
Local Notation h2vU := (@h2vU E).
Local Notation h2c := (@h2c E).
Local Notation c2h := (@c2h E).
Local Notation conjv := (@conjv E).

Lemma onb_tuple_eb : orthonormal (@tuple_eb E).
Proof. by apply/orthonormal_tupleP=>i j; rewrite/= !tnthE eb_dot. Qed.

(* vectType basis to hermitianType basis *)
Lemma v2hU_def : v2hU = \matrix_(j,i) v2r (eb i) 0 j.
Proof. by apply/matrixP=>i j; rewrite mxE v2hU.unlock !mxE tnthE. Qed.

Lemma v2hUE i j : v2hU i j = v2r (eb j) 0 i.
Proof. by rewrite v2hU_def mxE. Qed.

Let span_b2mx n (X : n.-tuple E) : span X = mx2vs (b2mx X).
Proof. by rewrite unlock tvalK; case: _ / (esym _). Qed.
Let free_b2mx n (X : n.-tuple E) : free X = row_free (b2mx X).
Proof. by rewrite /free /dimv span_b2mx genmxE size_tuple. Qed.

Lemma v2hU_unitmx : v2hU \in unitmx.
Proof. by rewrite v2hU.unlock unitmx_tr -row_free_unit -free_b2mx; apply/ort_free/onb_tuple_eb. Qed.
Lemma h2vU_unitmx : h2vU \in unitmx.
Proof. by rewrite h2vU.unlock unitmx_inv v2hU_unitmx. Qed.

Lemma mulmx_v2h1 : v2hU *m h2vU = 1%:M.
Proof. by rewrite h2vU.unlock mulmxV// v2hU_unitmx. Qed.
Lemma mulmx_h2v1 : h2vU *m v2hU = 1%:M.
Proof. by rewrite h2vU.unlock mulVmx// v2hU_unitmx. Qed.
Lemma mulmx_v2hK n (A : 'M_(n,_)) : A *m v2hU^T *m h2vU^T = A.
Proof. by rewrite -mulmxA -trmx_mul mulmx_h2v1 trmx1 mulmx1. Qed.
Lemma mulmx_h2vK n (A : 'M_(n,_)) : A *m h2vU^T *m v2hU^T = A.
Proof. by rewrite -mulmxA -trmx_mul mulmx_v2h1 trmx1 mulmx1. Qed.
Lemma mulmx_Kv2h n (A : 'M_(_,n)) : v2hU *m h2vU *m A = A.
Proof. by rewrite mulmx_v2h1 mul1mx. Qed.
Lemma mulmx_Kh2v n (A : 'M_(_,n)) : h2vU *m v2hU *m A = A.
Proof. by rewrite mulmx_h2v1 mul1mx. Qed.

Lemma v2r_eb i : v2r (eb i) = delta_mx 0 i *m (v2hU)^T.
Proof.
rewrite v2hU_def; apply/matrixP=>j k.
rewrite mxE (bigD1 i)//= big1=>[l/negPf nl|];
by rewrite !mxE ?nl ?andbF ?mul0r// ord1 !eqxx mul1r addr0.
Qed.

Lemma v2r_ebV i : delta_mx 0 i = v2r (eb i) *m (h2vU)^T.
Proof. by rewrite v2r_eb mulmx_v2hK. Qed.

Lemma h2cE u : h2c u = h2vU *m (v2r u)^T.
Proof. by rewrite h2c.unlock. Qed.
Lemma c2hE u : c2h u = r2v (v2hU *m u)^T.
Proof. by rewrite c2h.unlock. Qed.
Lemma conjvE u : c2h (h2c u)^*m = conjv u.
Proof. by rewrite conjv.unlock. Qed.
Lemma h2cEV u : v2r u = (v2hU *m h2c u)^T.
Proof. by rewrite h2cE mulmxA mulmx_Kv2h trmxK. Qed.
Lemma c2hEV u : r2v u = c2h (h2vU *m u^T).
Proof. by rewrite c2hE !trmx_mul mulmx_h2vK trmxK. Qed.

Lemma h2cK : cancel h2c c2h.
Proof. by move=>u; rewrite h2cE c2hE mulmxA mulmx_Kv2h trmxK v2rK. Qed. 
Lemma c2hK : cancel c2h h2c.
Proof. by move=>u; rewrite h2cE c2hE r2vK trmxK mulmxA mulmx_Kh2v. Qed. 
Lemma h2c_inj : injective h2c. Proof. exact: (can_inj h2cK). Qed.
Lemma c2h_inj : injective c2h. Proof. exact: (can_inj c2hK). Qed.
Lemma h2c_bij : bijective h2c.
Proof. exists c2h; [exact: h2cK| exact: c2hK]. Qed.
Lemma c2h_bij : bijective c2h.
Proof. exists h2c; [exact: c2hK| exact: h2cK]. Qed.
Lemma h2cP : linear h2c.
Proof. by move=>a u v; rewrite !h2cE !linearP/=. Qed.
Lemma c2hP : linear c2h.
Proof. by move=>a u v; rewrite !c2hE !linearP/=. Qed.

HB.instance Definition _ := GRing.isLinear.Build C E 'cV_(dim E) _ h2c h2cP.
HB.instance Definition _ := GRing.isLinear.Build C 'cV_(dim E) E _ c2h c2hP.

Lemma h2c_eb i : h2c (eb i) = delta_mx i 0.
Proof. by rewrite h2cE v2r_eb trmx_mul trmxK mulmxA mulmx_Kh2v trmx_delta. Qed.
Lemma c2h_eb i : c2h (delta_mx i 0) = eb i.
Proof. by apply/h2c_inj; rewrite h2c_eb c2hK. Qed.

Lemma dec_eb (u: E) : u = \sum_i ((h2c u) i 0) *: eb i.
Proof.
apply/h2c_inj; rewrite linear_sum/= [LHS]matrix_sum_delta exchange_big big_ord1.
by apply eq_bigr=>i _; rewrite linearZ/= h2c_eb.
Qed.

Lemma dotp_mulmx (u v: E) : [<u ; v>] = ((h2c u)^*t *m (h2c v)) 0 0.
Proof.
rewrite {1}(dec_eb u) {1}(dec_eb v) /conjmx /trmx mxE dotp_suml.
apply eq_bigr => i _; rewrite dotp_sumr !mxE (bigD1 i) //= big1.
by move=> j /negPf nji; rewrite dotpZl dotpZr eb_dot eq_sym nji !mulr0.
by rewrite dotpZl dotpZr eb_dot eqxx mulr1 addr0.
Qed. 

Lemma intro_ebl (u v: E) : 
  (forall i, [< eb i ; u >] = [< eb i ; v >]) <-> u = v.
Proof.
split; last by move=>->. 
move=> P; rewrite -intro_dotl => t; rewrite (dec_eb t) !dotp_suml.
by apply eq_bigr=>i _; rewrite !dotpZl P.
Qed.

Lemma intro_ebr (u v: E) : 
  (forall i, [< u ; eb i >] = [< v ; eb i >]) <-> u = v.
Proof.
split; [| move=>-> //]; rewrite -intro_ebl=> P t.
by apply (can_inj conjCK); rewrite !conj_dotp.
Qed.

End HermitianIso.

Section HermitianLfun.
Context {E F: chsType}.

Local Notation h2mx := (@h2mx E F).
Local Notation mx2h := (@mx2h E F).

Lemma h2mxE f : h2mx f = h2vU *m (f2mx f)^T *m v2hU.
Proof. by rewrite h2mx.unlock. Qed.
Lemma mx2hE f : mx2h f = Hom (v2hU *m f *m h2vU)^T.
Proof. by rewrite mx2h.unlock. Qed.
Lemma h2mxEV f : f2mx f = (v2hU *m h2mx f *m h2vU)^T.
Proof. by rewrite h2mxE !mulmxA mulmx_Kv2h -mulmxA mulmx_v2h1 mulmx1 trmxK. Qed.
Lemma mx2hEV f : Hom f = mx2h (h2vU *m f^T *m v2hU).
Proof. by rewrite mx2hE !mulmxA mulmx_Kv2h -mulmxA mulmx_v2h1 mulmx1 trmxK. Qed.
Lemma h2mxK : cancel h2mx mx2h.
Proof.
by move=>f; rewrite h2mxE mx2hE !mulmxA mulmx_Kv2h 
 -mulmxA mulmx_v2h1 mulmx1 trmxK f2mxK.
Qed. 
Lemma mx2hK : cancel mx2h h2mx.
Proof.
by move=>f; rewrite h2mxE mx2hE/= trmxK !mulmxA 
  mulmx_Kh2v -mulmxA mulmx_h2v1 mulmx1.
Qed.
Lemma h2mx_inj : injective h2mx. Proof. exact: (can_inj h2mxK). Qed.
Lemma mx2h_inj : injective mx2h. Proof. exact: (can_inj mx2hK). Qed.
Lemma h2mx_bij : bijective h2mx.
Proof. exists mx2h; [exact: h2mxK| exact: mx2hK]. Qed.
Lemma mx2h_bij : bijective mx2h.
Proof. exists h2mx; [exact: mx2hK| exact: h2mxK]. Qed.
Lemma h2mxP : linear h2mx.
Proof. by move=>a f v; rewrite !h2mxE !linearP/= mulmxDl -scalemxAl. Qed.
Lemma mx2hP : linear mx2h.
Proof. exact: (can2_linearP h2mxP h2mxK mx2hK). Qed.

HB.instance Definition _ := GRing.isLinear.Build C 'Hom(E, F) 'M_(dim F, dim E) _ h2mx h2mxP.
HB.instance Definition _ := GRing.isLinear.Build C 'M_(dim F, dim E) 'Hom(E, F) _ mx2h mx2hP.

Lemma applyfh (f : 'Hom(E,F)) u : f u = c2h (h2mx f *m h2c u).
Proof.
by rewrite unlock/= c2hE h2cE h2mxE !mulmxA
  mulmx_Kv2h !trmx_mul !mulmxA mulmx_h2vK !trmxK.
Qed.
Lemma h2mx0 : h2mx 0%VF = 0.
Proof. exact: linear0. Qed.
Lemma mx2h0 : mx2h 0 = 0%VF.
Proof. exact: linear0. Qed.
Lemma h2mx_dec (f : 'Hom(E,F)) i j : h2mx f i j = [<eb i; f (eb j) >].
Proof.
by rewrite dotp_mulmx applyfh c2hK !h2c_eb adjmx_delta 
  delta_mx_mulEr delta_mx_mulEl !eqxx !mul1r.
Qed.
End HermitianLfun.

Section HermitianLfunExtra.
Implicit Type (H G K: chsType).

Lemma h2mx_comp {H G K} (f: 'Hom(H,G)) (g: 'Hom(K,H)) :
  h2mx (f \o g)%VF = h2mx f *m h2mx g.
Proof.
by rewrite h2mxE f2mx_comp trmx_mul !h2mxE 
  -{1}[(f2mx f)^T]mulmx1 -mulmx_v2h1 !mulmxA.
Qed.

Lemma h2mx1 {G} : h2mx (\1%VF : 'End(G)) = 1%:M.
Proof. by apply/mx2h_inj/lfunP=>u; rewrite h2mxK lfunE/= applyfh mx2hK mul1mx h2cK. Qed.  

Lemma mx2h1 {G} : mx2h 1%:M = (\1%VF : 'End(G)).
Proof. by rewrite -h2mx1 h2mxK. Qed.  

End HermitianLfunExtra.

Section OuterProduct.
Context {E F: chsType}.

Local Notation outp := (@outp E F).
Local Notation "[> u ; v <]" := (outp u v).

Lemma h2mx_eb i j : h2mx [> eb i ; eb j <] = delta_mx i j.
Proof. by rewrite outp.unlock mx2hK !h2c_eb adjmx_delta mul_delta_mx. Qed.
Lemma mx2h_eb i j : mx2h (delta_mx i j) = [> eb i ; eb j <].
Proof. by apply/h2mx_inj; rewrite h2mx_eb mx2hK. Qed.

Lemma outpE (u : F) (v w : E) : [> u ; v <] w = [<v ; w >] *: u.
Proof.
apply/h2c_inj; rewrite applyfh c2hK outp.unlock mx2hK linearZ/= -mulmxA dotp_mulmx.
by apply/matrixP=>i j; rewrite mxE ord1 big_ord1 !mxE mulrC.
Qed.

Lemma linear_outp u : antilinear (outp u).
Proof.
move=>a v w; apply/lfunP=>t.
by rewrite lfunE/= lfunE/= !outpE linearPl/= scalerDl scalerA.
Qed.

HB.instance Definition _ u := GRing.isLinear.Build C E 'Hom(E, F) _ (outp u) (linear_outp u).

Lemma linear_outpr u : linear (outp^~ u).
Proof.
by move=>a v w; apply/lfunP=>t; rewrite lfunE/= lfunE/= !outpE linearP/=.
Qed.

HB.instance Definition _ := bilinear_isBilinear.Build C F E
  'Hom(E, F) *:%R (Num.conj_op \;  *:%R) outp (linear_outpr, linear_outp).

Lemma outp_eq0 (u : F) (v : E) :
  [> u ; v <] == 0 = ((u == 0) || (v == 0)).
Proof.
case Eu: (u == 0); first by move: Eu=>/eqP->; rewrite linear0l eqxx.
case Ev: (v == 0); first by move: Ev=>/eqP->; rewrite linear0r eqxx.
case: eqP=>// /lfunP/(_ v)/eqP.
by rewrite outpE lfunE/= scaler_eq0 Eu dotp_eq0 Ev.
Qed.

Lemma out0p u : [> 0; u <] = 0. Proof. exact: linear0l. Qed.
Lemma outpNl w : {morph (outp^~ w) : u / -u}. Proof. exact: linearNl. Qed.
Lemma outpBl w : {morph (outp^~ w) : u v / u - v}. Proof. exact: linearBl. Qed.
Lemma outpDl w : {morph (outp^~ w) : u v / u + v}. Proof. exact: linearDl. Qed.
Lemma outpMnl w n : {morph (outp^~ w) : u / u *+ n}. Proof. exact: linearMnl. Qed.
Lemma outpMNnl w n : {morph (outp^~ w) : u / u *- n}. Proof. exact: linearMNnl. Qed.
Lemma outp0 u : [> u; 0 <] = 0. Proof. exact: linear0. Qed.
Lemma outpNr w : {morph outp w : u / -u}. Proof. exact: linearN. Qed.
Lemma outpBr w : {morph outp w : u v / u - v}. Proof. exact: linearB. Qed.
Lemma outpDr w : {morph outp w : u v / u + v}. Proof. exact: linearD. Qed.
Lemma outpMnr w n : {morph outp w : u / u *+ n}. Proof. exact: linearMn. Qed.
Lemma outpMNnr w n : {morph outp w : u / u *- n}. Proof. exact: linearMNn. Qed.

Lemma outpZl (x : C) u v : [> x *: u; v <] = x *: [> u; v <].
Proof. exact: linearZl_LR. Qed.

Lemma outpPl (x : C) u v w : [> x *: u + v ; w <] = x *: [> u; w <] + [> v; w <].
Proof. exact: linearPl. Qed.

Lemma outp_suml (I : Type) (r : seq I) P (f : I -> F) u :
  [> \sum_(v <- r | P v) f v; u <] = \sum_(v <- r | P v) [> f v; u <].
Proof. exact: linear_suml. Qed.

Lemma outpZr (x : C) u v : [> u; x *: v <] = x^* *: [> u; v <].
Proof. exact: linearZ. Qed.

Lemma outpPr (x : C) u v w : [> u; x *: v + w <] = x^* *: [> u; v <] + [> u; w <].
Proof. exact: linearP. Qed.

Lemma outp_sumr (I : Type) (r : seq I) P (f : I -> E) u :
  [> u; \sum_(v <- r | P v) f v <] = \sum_(v <- r | P v) [> u; f v <].
Proof. exact: linear_sum. Qed.

End OuterProduct.

Local Open Scope lfun_scope.
Section ConjvTheory.
Context {H: chsType}.

Local Notation conjv := (@conjv H).

Lemma conjv_eb i : (eb i)^*v = (eb i :H).
Proof. by rewrite conjv.unlock h2c_eb conjmx_delta c2h_eb. Qed.  

Lemma conjv_is_antilinear : antilinear conjv.
Proof. by move=>a u v; rewrite conjv.unlock !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build C H H _ conjv conjv_is_antilinear.

Lemma conjv0 : conjv 0 = 0. Proof. exact: linear0. Qed.
Lemma conjvN : {morph conjv : u / -u}. Proof. exact: linearN. Qed.
Lemma conjvB : {morph conjv : u v / u - v}. Proof. exact: linearB. Qed.
Lemma conjvD : {morph conjv : u v / u + v}. Proof. exact: linearD. Qed.
Lemma conjvMn n : {morph conjv : u / u *+ n}. Proof. exact: linearMn. Qed.
Lemma conjvMNn n : {morph conjv : u / u *- n}. Proof. exact: linearMNn. Qed.
Lemma conjvZ c (u: H) : (c *: u)^*v = c^* *: u^*v. Proof. exact: linearZ. Qed.

Lemma conjvP c (u v: H) : (c *: u + v)^*v = c^* *: u^*v + v^*v.
Proof. exact: linearP. Qed.

Lemma conjv_sum (I : Type) (r : seq I) P (f : I -> H) :
  (\sum_(i <- r | P i) f i)^*v = \sum_(i <- r | P i) (f i)^*v.
Proof. exact: linear_sum. Qed.

Lemma conjvK : involutive conjv.
Proof. by move=> v; rewrite conjv.unlock c2hK conjmxK h2cK. Qed.

Lemma conjv_inj : injective conjv.
Proof. exact (inv_inj conjvK). Qed.

Lemma conjv_dot (u v : H) : [< u^*v ;  v ^*v >] = [< v ; u >].
Proof.
rewrite !dotp_mulmx conjv.unlock !c2hK !mxE.
by apply eq_bigr => i _; rewrite !mxE mulrC conjCK.
Qed.

Lemma conjv_dotr (u v : H) : [< u ; v^*v >] = [< v; u^*v >].
Proof. by rewrite -{1}(conjvK u) conjv_dot. Qed.

Lemma conjv_dotl (u v : H) : [< u^*v ; v >] = [< v^*v; u >].
Proof. by rewrite -{2}(conjvK u) conjv_dot. Qed.

End ConjvTheory.

Section AdjTrConjLfunTheory.
Context {H G: chsType}.
Implicit Type (f: 'Hom(H, G)) (g : 'Hom(G,H)).

Local Notation adjf := (@adj_lfun H G).
Local Notation conjf := (@conj_lfun H G).
Local Notation trf := (@tr_lfun H G).

Lemma adjfK : cancel adjf (@adj_lfun G H).
Proof. by move=>f; rewrite adj_lfun.unlock mx2hK adjmxK h2mxK. Qed.  

Lemma adjf_inj : injective adjf.
Proof. exact (can_inj adjfK). Qed.

Lemma adjf_is_antilinear : antilinear adjf.
Proof. by move=> a f g; apply/h2mx_inj; rewrite adj_lfun.unlock /= !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build C 'Hom(H, G) 'Hom(G, H) _
  adjf adjf_is_antilinear.

Lemma adjf0 : adjf 0%:VF = 0. Proof. exact: linear0. Qed.
Lemma adjfN : {morph adjf : u / -u}. Proof. exact: linearN. Qed.
Lemma adjfB : {morph adjf : u v / u - v}. Proof. exact: linearB. Qed.
Lemma adjfD : {morph adjf : u v / u + v}. Proof. exact: linearD. Qed.
Lemma adjfMn n : {morph adjf : u / u *+ n}. Proof. exact: linearMn. Qed.
Lemma adjfMNn n : {morph adjf : u / u *- n}. Proof. exact: linearMNn. Qed.
Lemma adjfZ x f : (x *: f)^A = x^* *: f^A. Proof. exact: linearZ. Qed.

Lemma adjfP x f1 f2 : (x *: f1 + f2)^A = x^* *: f1^A + f2^A.
Proof. exact: linearP. Qed.

Lemma adjf_sum (I : Type) (r : seq I) P (F : I -> 'Hom(H,G)) :
  (\sum_(i <- r | P i) F i)^A = \sum_(i <- r | P i) (F i)^A.
Proof. exact: linear_sum. Qed.

Lemma adjf_comp {K: chsType} (f: 'Hom(G, K)) (g: 'Hom(H, G)) :
  ((f \o g)^A = g^A \o f^A)%VF.
Proof. by apply/h2mx_inj; rewrite adj_lfun.unlock !h2mx_comp !mx2hK adjmxM. Qed.

Lemma adjf1 : (\1 : 'Hom(H,H))^A = \1.
Proof. by apply/h2mx_inj; rewrite adj_lfun.unlock mx2hK h2mx1 adjmx1. Qed.

Lemma adj_dotEl f u v : [< f^A u ; v >] = [< u ; f v >].
Proof. by rewrite !dotp_mulmx adj_lfun.unlock !applyfh !c2hK mx2hK adjmxM adjmxK mulmxA. Qed.

Lemma adj_dotEr f u v : [< u ; f^A v >] = [< f u ; v >].
Proof. by rewrite -conj_dotp -[RHS]conj_dotp -adj_dotEl. Qed.

Lemma conjfE f u : (f^C u = (f%VF u^*v)^*v)%VF.
Proof. by rewrite !applyfh conj_lfun.unlock mx2hK conjv.unlock !c2hK conjmxM conjmxK. Qed. 

Lemma conjfK : involutive conjf.
Proof. by move=>f; rewrite conj_lfun.unlock mx2hK conjmxK h2mxK. Qed.  

Lemma conjf_inj : injective conjf.
Proof. exact (inv_inj conjfK). Qed.

Lemma conjf_is_antilinear : antilinear conjf.
Proof. by move=> a f g; apply h2mx_inj; rewrite conj_lfun.unlock /= !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build C 'Hom(H, G) 'Hom(H, G) _
  conjf conjf_is_antilinear.

Lemma conjf0 : conjf 0%:VF = 0. Proof. exact: linear0. Qed.
Lemma conjfN : {morph conjf : u / -u}. Proof. exact: linearN. Qed.
Lemma conjfB : {morph conjf : u v / u - v}. Proof. exact: linearB. Qed.
Lemma conjfD : {morph conjf : u v / u + v}. Proof. exact: linearD. Qed.
Lemma conjfMn n : {morph conjf : u / u *+ n}. Proof. exact: linearMn. Qed.
Lemma conjfMNn n : {morph conjf : u / u *- n}. Proof. exact: linearMNn. Qed.
Lemma conjfZ x f : (x *: f)^C = x^* *: f^C. Proof. exact: linearZ. Qed.

Lemma conjfP x f1 f2 : (x *: f1 + f2)^C = x^* *: f1^C + f2^C.
Proof. exact: linearP. Qed.

Lemma conjf_sum (I : Type) (r : seq I) P (F : I -> 'Hom(H,G)) :
  (\sum_(i <- r | P i) F i)^C = \sum_(i <- r | P i) (F i)^C.
Proof. exact: linear_sum. Qed.

Lemma conjf_comp {K: chsType} (f: 'Hom(G, K)) (g: 'Hom(H, G)) :
  ((f \o g)^C = f^C \o g^C)%VF.
Proof. by apply/h2mx_inj; rewrite conj_lfun.unlock !h2mx_comp !mx2hK conjmxM. Qed.

Lemma conjf1 : (\1 : 'Hom(H,H))^C = \1.
Proof. by apply/h2mx_inj; rewrite conj_lfun.unlock mx2hK h2mx1 conjmx1. Qed.

Lemma trfCA f : f^T = f^C^A.
Proof. by rewrite tr_lfun.unlock adj_lfun.unlock conj_lfun.unlock mx2hK adjmxCT conjmxK. Qed.

Lemma trfAC f : f^T = f^A^C.
Proof. by rewrite tr_lfun.unlock adj_lfun.unlock conj_lfun.unlock mx2hK adjmxTC conjmxK. Qed.

Lemma trfK : cancel trf (@tr_lfun G H).
Proof. by move=>f; rewrite tr_lfun.unlock mx2hK trmxK h2mxK. Qed.  

Lemma trf_inj : injective trf.
Proof. exact (can_inj trfK). Qed.

Lemma trf_is_linear : linear trf.
Proof. by move=> a f g; apply/h2mx_inj; rewrite tr_lfun.unlock /= !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build C 'Hom(H, G) 'Hom(G, H) _
  trf trf_is_linear.

Lemma trf0 : trf 0%:VF = 0. Proof. exact: linear0. Qed.
Lemma trfN : {morph trf : u / -u}. Proof. exact: linearN. Qed.
Lemma trfB : {morph trf : u v / u - v}. Proof. exact: linearB. Qed.
Lemma trfD : {morph trf : u v / u + v}. Proof. exact: linearD. Qed.
Lemma trfMn n : {morph trf : u / u *+ n}. Proof. exact: linearMn. Qed.
Lemma trfMNn n : {morph trf : u / u *- n}. Proof. exact: linearMNn. Qed.
Lemma trfZ x f : (x *: f)^T = x *: f^T%VF. Proof. exact: linearZ. Qed.

Lemma trfP x f1 f2 : (x *: f1 + f2)^T = x *: f1^T%VF + f2^T%VF.
Proof. exact: linearP. Qed.

Lemma trf_sum (I : Type) (r : seq I) P (F : I -> 'Hom(H,G)) :
  (\sum_(i <- r | P i) F i)^T = \sum_(i <- r | P i) (F i)^T%VF.
Proof. exact: linear_sum. Qed.

Lemma trf_comp {K: chsType} (f: 'Hom(G, K)) (g: 'Hom(H, G)) :
  ((f \o g)^T = g^T \o f^T)%VF.
Proof. by apply/h2mx_inj; rewrite tr_lfun.unlock !h2mx_comp !mx2hK trmx_mul. Qed.

Lemma trf1 : (\1 : 'Hom(H,H))^T = \1.
Proof. by apply/h2mx_inj; rewrite tr_lfun.unlock mx2hK h2mx1 trmx1. Qed.

Lemma tr_dotEl f u v : [< f^T%VF u ; v >] = [< u ; f^C v >].
Proof. by rewrite trfCA adj_dotEl. Qed.

Lemma tr_dotEr f u v : [< u ; f^T%VF v >] = [< f^C u ; v >].
Proof. by rewrite -conj_dotp -[RHS]conj_dotp -tr_dotEl. Qed.

Lemma conj_dotEl f u v : [< f^C u ; v >] = [< u ; f^T%VF v >].
Proof. by rewrite tr_dotEr. Qed.

Lemma conj_dotEr f u v : [< u ; f^C v >] = [< f^T%VF u ; v >].
Proof. by rewrite tr_dotEl. Qed.

Lemma h2mx_adj f : h2mx (f^A) = (h2mx f)^*t.
Proof. by rewrite adj_lfun.unlock mx2hK. Qed.

Lemma h2mx_tr f : h2mx (f^T) = (h2mx f)^T%R.
Proof. by rewrite tr_lfun.unlock mx2hK. Qed.

Lemma h2mx_conj f : h2mx (f^C) = (h2mx f)^*m.
Proof. by rewrite conj_lfun.unlock mx2hK. Qed.

Lemma mx2h_adj m : mx2h (m^*t) = adjf (mx2h m).
Proof. by rewrite adj_lfun.unlock mx2hK. Qed.

Lemma mx2h_tr m : mx2h (m^T)%R = trf (mx2h m).
Proof. by rewrite tr_lfun.unlock mx2hK. Qed.

Lemma mx2h_conj m : mx2h (m^*m) = conjf (mx2h m).
Proof. by rewrite conj_lfun.unlock mx2hK. Qed.

End AdjTrConjLfunTheory.

Section AdjTrConjLfunTrans.
Implicit Type (H G: chsType).

Lemma adjfCT H G (f : 'Hom(H,G)) : f^A = f^C^T.
Proof. by rewrite trfCA conjfK. Qed.

Lemma adjfTC H G (f : 'Hom(H,G)) : f^A = f^T^C.
Proof. by rewrite trfAC conjfK. Qed.

Lemma conjfAT H G (f : 'Hom(H,G)) : f^C = f^A^T.
Proof. by rewrite trfAC adjfK. Qed.

Lemma conjfTA H G (f : 'Hom(H,G)) : f^C = f^T^A.
Proof. by rewrite trfCA adjfK. Qed.

Lemma lfCAC H G (f: 'Hom(H, G)) : f^C^A = f^A^C.
Proof. by rewrite -trfCA -trfAC. Qed.

Lemma lfACC H G (f: 'Hom(H, G)) : f^A^C = f^C^A.
Proof. by rewrite -trfCA -trfAC. Qed.

Lemma lfATC H G (f: 'Hom(H, G)) : f^A^T = f^T^A.
Proof. by rewrite -conjfAT -conjfTA. Qed.

Lemma lfTAC H G (f: 'Hom(H, G)) : f^T^A = f^A^T.
Proof. by rewrite -conjfAT -conjfTA. Qed.

Lemma lfCTC H G (f: 'Hom(H, G)) : f^C^T = f^T^C.
Proof. by rewrite -adjfCT -adjfTC. Qed.

Lemma lfTCC H G (f: 'Hom(H, G)) : f^T^C = f^C^T.
Proof. by rewrite -adjfCT -adjfTC. Qed.

End AdjTrConjLfunTrans.

Section OuterProductTheory.
Implicit Type (H G W: chsType).

Lemma adj_outp H G (u : H) (v : G) : [> u; v <]^A = [> v; u <].
Proof.
apply/lfunP=>t; apply/intro_dotl=>w.
by rewrite adj_dotEr !outpE linearZ/= linearZl_LR/= conj_dotp mulrC.
Qed.

Lemma conj_outp H G (u : H) (v : G) : [> u; v <]^C = [> u^*v; v^*v <].
Proof. by apply/lfunP=>t; rewrite conjfE !outpE conjvZ conj_dotp conjv_dotl. Qed.

Lemma tr_outp H G (u : H) (v : G) : [> u; v <]^T = [> v^*v ; u^*v <].
Proof. by rewrite trfAC adj_outp conj_outp. Qed.

Lemma outp_compl H G W (u : H) (v : G) (f : 'Hom(W,G)) : 
  [> u ; v <] \o f = [> u ; f^A v <].
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE -adj_dotEl. Qed.

Lemma outp_compr H G W (u : H) (v : G) (f : 'Hom(H,W)) : 
  f \o [> u ; v <] = [> f u ; v <].
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE linearZ. Qed.

Lemma outp_comp H G W (u : H) (v w : G) (t : W) : 
  [> u ; v <] \o [> w ; t <] = [< v ; w >] *: [> u ; t <].
Proof. by rewrite outp_compr outpE linearZl_LR. Qed.

Lemma outpD H (u v : H) : [> u + v; u + v <] =
  [> u; u <] + [> v; v <] + ([> u; v <] + [> u; v <]^A).
Proof.
rewrite !(outpDr, outpDl) adj_outp -!addrA; congr (_ + _).
by rewrite [RHS]addrC addrCA !addrA.
Qed.

End OuterProductTheory.

Section ScalarHermitian.

Definition ncfdotp (a b : C^o) :=  a^* * b.

Lemma ncfdotp_ge0 : forall v, 0 <= ncfdotp v v.
Proof. by move=>v; rewrite /ncfdotp -normCKC exprn_ge0. Qed.
Lemma ncfdotp0_eq0 : forall v, (ncfdotp v v == 0) = (v == 0).
Proof. by move=>v; rewrite /ncfdotp -normCKC expf_eq0/= normr_eq0. Qed.
Lemma conj_ncfdotp : forall u v, (ncfdotp u v)^* = ncfdotp v u.
Proof. by move=>u v; rewrite /ncfdotp rmorphM conjCK mulrC. Qed.
Lemma linear_ncfdotp : forall u, linear_for *%R (ncfdotp u).
Proof. by move=>w a u v; rewrite /ncfdotp mulrDr /GRing.scale/= mulrCA. Qed.

Definition ncf_regular_hermitianMixin := @Vector_isHermitianSpace.Build C^o
  ncfdotp ncfdotp_ge0 ncfdotp0_eq0 conj_ncfdotp linear_ncfdotp.
HB.instance Definition _ := ncf_regular_hermitianMixin.
#[local] HB.instance Definition _ := HermitianSpace.copy C C^o.

Lemma ncf_dim_proper : (dim C^o > 0)%N.
Proof. by []. Qed.
Definition ncf_eb (i : 'I_(dim C^o)) : C^o := 1.
Lemma ncf_eb_dot i j : [<ncf_eb i ; ncf_eb j >] = (i == j)%:R.
Proof. by rewrite/ncf_eb/= !ord1 /dotp/=/ncfdotp conjC1 mulr1. Qed.
Definition ncf_regular_chsMixin := @HermitianSpace_isCanonical.Build C^o
  ncf_eb ncf_eb_dot ncf_dim_proper.
HB.instance Definition _ := ncf_regular_chsMixin.
#[local] HB.instance Definition _ := CanonicalHermitianSpace.copy C C^o.

End ScalarHermitian.

Lemma mxtrace_delta (R : ringType) m (i j : 'I_m) : 
  \tr (delta_mx i j : 'M[R]__) = (i == j)%:R.
Proof.
rewrite /mxtrace (bigD1 i)//= big1=>[k/negPf nk|];
by rewrite mxE ?nk// eqxx/= addr0.
Qed.

(* linear function forms a Hermitian space *)
(* the norm is l2norm. we do not use it since we later use trace norm *)
Section LfunHermitian.
Context {U V : chsType}.

Let F := 'Hom(U,V).

Definition lfundotp (a b : F) :=  \tr (h2mx (a^A \o b)).

Lemma lfundotp_ge0 v : 0 <= lfundotp v v.
Proof. by rewrite/lfundotp h2mx_comp adj_lfun.unlock mx2hK mxtrace_mulC; apply/form_tr_ge0. Qed.
Lemma lfundotp0_eq0 v : (lfundotp v v == 0) = (v == 0).
Proof.
rewrite/lfundotp h2mx_comp adj_lfun.unlock mx2hK mxtrace_mulC -eqb_iff; split.
by move=>/eqP/form_tr_eq0/(f_equal mx2h); rewrite h2mxK mx2h0=>->.
by move=>/eqP->; rewrite h2mx0 mul0mx linear0.
Qed.
Lemma conj_lfundotp u v : (lfundotp u v)^* = lfundotp v u.
Proof. by rewrite/lfundotp adj_lfun.unlock -mxtrace_adj !h2mx_comp !mx2hK adjmxM adjmxK. Qed.
Lemma linear_lfundotp u : linear_for *%R (lfundotp u).
Proof.
by move=>a v w; rewrite/lfundotp comp_lfunDr !linearD/= -comp_lfunZr !linearZ/=.
Qed.

Definition lfun_hermitianMixin := @Vector_isHermitianSpace.Build 'Hom(U,V)
  lfundotp lfundotp_ge0 lfundotp0_eq0 conj_lfundotp linear_lfundotp.
Definition lfun_hermitianType : hermitianType := (HB.pack 'Hom(U,V) lfun_hermitianMixin).
#[local] HB.instance Definition _ := lfun_hermitianMixin.
#[local] HB.instance Definition _ := Num.NormedZmodule.copy 'Hom(U,V)
  (('Hom(U,V) : hermitianType) : normedZmodType C).

Lemma lfun_dim_proper : (dim 'Hom(U,V) > 0)%N.
Proof. by rewrite/dim/= muln_gt0 !dim_proper. Qed.
Definition lfun_eb (i : 'I_(dim 'Hom(U,V))) : 'Hom(U,V) 
  := [> eb (mxtens_unindex i).2; eb (mxtens_unindex i).1 <].
Lemma lfun_eb_dot i j : [<lfun_eb i ; lfun_eb j >] = (i == j)%:R.
Proof.
rewrite/lfun_eb/dotp/=/lfundotp h2mx_comp adj_outp !outp.unlock !mx2hK.
rewrite !h2c_eb !adjmx_delta !mul_delta_mx mul_delta_mx_cond linearMn/= mxtrace_delta.
rewrite -(can_eq (@mxtens_unindexK _ _)) -pair_eqE/=.
by case: eqP=>_; case: eqP.
Qed.

Definition lfun_chsMixin := @HermitianSpace_isCanonical.Build 'Hom(U,V)
  lfun_eb lfun_eb_dot lfun_dim_proper.
Definition lfun_chsType : chsType := HB.pack 'Hom(U,V) lfun_chsMixin.

Lemma lfun_hnormE (u : 'Hom(U,V)) : `|u| = l2norm (h2mx u).
Proof. by rewrite hnormE /dotp/= /lfundotp h2mx_comp l2norm_dotV adj_lfun.unlock mx2hK. Qed.

End LfunHermitian.

(*
(* extra structure, PONB (partial orthonormal basis = orthonormal), *)
(* ONB (orthonormal basis), partial state (vector with norm less equal 1) *)
(* normalized state (vector with norm 1) *)
Module PONB.

Section ClassDef.
Variable (H : hermitianType) (F : finType).

Definition axiom (f : F -> H) := 
  (forall i j, [< f i ; f j >] = (i == j)%:R).

Structure map (phUV : phant (F -> H)) := Pack {
  apply; 
  _ : axiom apply; 
}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> H)) (f g : F -> H) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation ponbasis f := (axiom f).
Coercion apply : map >-> Funclass.
Notation PONBasis fA := (Pack (Phant _) fA).
Notation "''PONB' ( F ; S )" := (map (Phant (F -> S))) : type_scope.
(* Notation "''PONB[' H ]_ ( F ; S )" := (map (Phant (F -> 'H[H]_S))) : type_scope. *)
(* Notation "''PONB_' ( F ; S )" := ('PONB[_]_(F;S)) : type_scope. *)
Notation "''PONB'" := ('PONB(_;_)) (only parsing) : type_scope.
Notation "[ 'PONB' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'PONB' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id) : form_scope.
End Exports.

End PONB.
Export PONB.Exports.

Module ONB.

Section ClassDef.
Variable (H : hermitianType) (F : finType).

Definition axiom (f : F -> H) := 
  (forall i j, [< f i ; f j >] = (i == j)%:R) /\ #|F| = dim H.
Definition mixin_of (f : F -> H) := #|F| = dim H.

Record class_of f : Prop := Class {base : ponbasis f; mixin : mixin_of f}.
Local Coercion base : class_of >-> ponbasis.

Lemma class_of_axiom (f : F -> H) : axiom f -> class_of f.
Proof. by move=>[??]; split. Qed.

Lemma class_of_axiom_split (f : F -> H) :
  (forall i j, [< f i ; f j >] = (i == j)%:R) ->
  #|F| = dim H -> class_of f.
Proof. by split. Qed.

Structure map (phUV : phant (F -> H)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> H)) (f g : F -> H) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fL of phant_id g (apply cF) & phant_id fL class :=
  @Pack phUV f fL.

Definition pack (fZ : mixin_of f) :=
  fun (bF : PONB.map phUV) fA & phant_id (PONB.class bF) fA =>
  Pack phUV (Class fA fZ).

Definition ponbType := PONB.Pack phUV class.
End ClassDef.

Module Exports.
Notation onbasis f := (axiom f).
Coercion apply : map >-> Funclass.
Coercion class_of_axiom : axiom >-> class_of.
Canonical ponbType.
(* provide orthonormal and card *)
Notation ONBasis fA fB := (Pack (Phant _) (class_of_axiom_split fA fB)).
(* provide card; already a ponbasis *)
Notation CardONBasis fC := (pack fC id).
Notation "''ONB' ( F ; S )" := (map (Phant (F -> S))) : type_scope.
(* Notation "''ONB[' H ]_ ( F ; S )" := (map (Phant (F -> 'H[H]_S))) : type_scope. *)
(* Notation "''ONB_' ( F ; S )" := ('ONB[_]_(F;S)) : type_scope. *)
Notation "''ONB'" := ('ONB(_;_)) (only parsing) : type_scope.
Notation "[ 'ONB' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'ONB' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id) : form_scope.
End Exports.

End ONB.
Export ONB.Exports.

Module PartialState.

Section ClassDef.
Variable (U : hermitianType).
Definition axiom (v : U) := [< v ; v >] <= 1.
Structure type := Pack { sort: U; _ : axiom sort; }.
Local Coercion sort : type >-> HermitianSpace.sort.

Variables (T : U) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom cT') in c.
Definition clone c of phant_id class c := @Pack T c.

Local Canonical subType := Eval hnf in [subType for sort].
Definition eqMixin := Eval hnf in [eqMixin of type by <:].
Local Canonical  eqType  := Eval hnf in EqType type eqMixin.
Definition choiceMixin := [choiceMixin of type by <:].
Local Canonical  choiceType  := Eval hnf in ChoiceType type choiceMixin.

End ClassDef.

Module Import Exports.
Coercion sort : type >-> HermitianSpace.sort.
Canonical subType.
Canonical eqType.
Canonical choiceType.
Notation PSType M := (@Pack _ _ M).
Notation "''PS' ( S )" := (@type S) : type_scope.
Notation "''PS'" := ('PS(_)) (only parsing) : type_scope.
(* Notation "''PS[' H ]_ S" := ('PS('H[H]_S))   (only parsing) : type_scope. *)
(* Notation "''PS[' H ]_ ( S )" := ('PS[H]_S)    (only parsing) : type_scope. *)
(* Notation "''PS_' S"  := ('PS[_]_S) : type_scope. *)
(* Notation "''PS_' ( S )" := ('PS_S) (only parsing) : type_scope. *)
Notation "[ 'PS' 'of' u 'as' v ]" := (@clone _ _ u v _ idfun) : form_scope.
Notation "[ 'PS' 'of' u ]" := (@clone _ _ u _ _ id) : form_scope.
End Exports.

End PartialState.
Export PartialState.Exports.

Module NormalizedState.

Section ClassDef.
Variable (U : hermitianType).
Definition axiom (v : U) := [< v ; v >] == 1.
Structure type := Pack { sort: U; _ : axiom sort; }.
Local Coercion sort : type >-> HermitianSpace.sort.

Lemma axiom_psaxiom (v : U) : axiom v -> [< v ; v >] <= 1.
Proof. by move=>/eqP->. Qed.

Variables (T : U) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom cT') in c.
Definition clone c of phant_id class c := @Pack T c.

Local Canonical subType := Eval hnf in [subType for sort].
Definition eqMixin := Eval hnf in [eqMixin of type by <:].
Local Canonical  eqType  := Eval hnf in EqType type eqMixin.
Definition choiceMixin := [choiceMixin of type by <:].
Local Canonical  choiceType  := Eval hnf in ChoiceType type choiceMixin.

Definition psType := PartialState.Pack (axiom_psaxiom class).

End ClassDef.

Module Import Exports.
Coercion sort : type >-> HermitianSpace.sort.
Canonical subType.
Canonical eqType.
Canonical choiceType.
Canonical psType.
Notation NSType M := (@Pack _ _ M).
Notation "''NS' ( S )" := (@type S) : type_scope.
Notation "''NS'" := ('NS(_)) (only parsing) : type_scope.
(* Notation "''NS[' H ]_ S" := ('NS('H[H]_S))   (only parsing) : type_scope. *)
(* Notation "''NS[' H ]_ ( S )" := ('NS[H]_S)    (only parsing) : type_scope. *)
(* Notation "''NS_' S"  := ('NS[_]_S) : type_scope. *)
(* Notation "''NS_' ( S )" := ('NS_S) (only parsing) : type_scope. *)
Notation "[ 'NS' 'of' u 'as' v ]" := (@clone _ _ u v _ idfun) : form_scope.
Notation "[ 'NS' 'of' u ]" := (@clone _ _ u _ _ id) : form_scope.
End Exports.

End NormalizedState.
Export NormalizedState.Exports.
*)


