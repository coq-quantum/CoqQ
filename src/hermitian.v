(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra perm complex.
Require Import forms.
From mathcomp.analysis Require Import reals.
From mathcomp.real_closed Require Import complex.
Require Import xvector mcextra mxpred.

(************************************************************************)
(* This file define the module of hermitian space and its theory        *)
(*                hermitianType == vectType over complex number C       *)
(*                                 equipped with  an inner product      *)
(*  [hermitianType of T for cT] == T-clone of the hermitianType T       *)
(*                                 structure cT.                        *)
(*         [hermitianType of T] == clone of a canonical structure of    *)
(*                                 hermitianType on T.                  *)
(*                      chsType == non-degenerated hermitianType        *)
(*                                 with orthonormal canonical basis     *)
(*        [chsType of T for cT] == T-clone of the chsType T             *)
(*                                 structure cT.                        *)
(*               [chsType of T] == clone of a canonical structure of    *)
(* Definition and Theory                                                *)
(*      define and prove correct the Gram–Schmidt process               *)
(*      define conjugate of vector                                      *)
(*      define adjoint, conjugate and transpose of linear function      *)
(************************************************************************)

(* -------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import Vector.InternalTheory.
(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope complex_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Context (R : realType) (C := R[i]).

(* -------------------------------------------------------------------- *)
Module HermitianSpace.
Record mixin_of (E : vectType C) : Type := Mixin {
  dotp : E -> E -> C;
  _    : forall v, 0 <= dotp v v;
  _    : forall v, (dotp v v == 0) = (v == 0);
  _    : forall u v, (dotp u v)^* = dotp v u;
  _    : forall u, linear_for *%R (dotp u);
}.

Section ClassDef.
Record class_of (E : Type) : Type := Class {
  base : Vector.class_of [ringType of C] E;
  mixin : mixin_of (Vector.Pack _ base)
}.
Local Coercion base : class_of >-> Vector.class_of.

Structure type := Pack { sort; _ : class_of sort; }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Vector.Pack _ (Phant C) T b0)) :=
  fun bT b & phant_id (@Vector.class _ (Phant C) bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ (Phant C) cT xclass.
Definition vectType := @Vector.Pack _ (Phant C) cT xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Vector.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >->  Equality.type.
Bind Scope ring_scope with sort.
Canonical eqType.
Coercion choiceType: type >-> Choice.type.
Canonical choiceType.
Coercion zmodType: type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType: type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion vectType: type >-> Vector.type.
Canonical vectType.


Notation hermitianType := type.
Notation HermitianType mH :=
   (@pack _ _ mH _ _ id _ id).
Notation HermitianMixin := Mixin.
Notation "[ 'hermitianType' 'of' T ]" :=
  (@clone T _ _ id)
  (at level 0, format "[ 'hermitianType'  'of'  T ]") :
  form_scope.
Notation "[ 'hermitianType' 'of' T 'for' cT ]" :=
  (@clone T cT _ idfun)
  (at level 0, format "[ 'hermitianType' 'of'  T  'for'  cT ]") :
  form_scope.

End Exports.
End HermitianSpace.

Export HermitianSpace.Exports.

(* -------------------------------------------------------------------- *)
Definition dotp {E : hermitianType} : E -> E -> C :=
  HermitianSpace.dotp (HermitianSpace.class E).

Notation "[< u ; v >]" := (dotp u v) (at level 2, format "[<  u ;  v  >]").

(* -------------------------------------------------------------------- *)
Section HermitianSpaceTheory.
Variable (E : hermitianType).

Implicit Types (u v w : E) (a b : C).

Lemma ge0_dotp u : 0 <= [< u; u >].
Proof. by case: E u => [? [? []]]. Qed.

Lemma dotp_eq0 u : ([< u; u >] == 0) = (u == 0).
Proof. by case: E u => [? [? []]]. Qed.

Lemma dotp00 : [< (0 : E); 0 >] = 0.
Proof. by apply/eqP; rewrite dotp_eq0. Qed.

Lemma conj_dotp u v : [< u; v >]^* = [< v; u >].
Proof. by case: E u v => [? [? []]]. Qed.

Lemma linear_dotp u : linear_for *%R (dotp u).
Proof. by case: E u => [? [? []]]. Qed.

Canonical dotp_additive (u : E) := Additive (linear_dotp u).
Canonical dotp_linear (u : E) := (Linear (linear_dotp u)).

Lemma dotp_is_antilinear a u v w :
  [< a *: u + v; w >] = a^* * [< u; w >] + [< v; w >].
Proof.
by rewrite -conj_dotp !(linearD, linearZ, rmorphM) !conj_dotp.
Qed.

Definition dotpr (u : E) := (dotp)^~ u.
Lemma linear_dotpr u : linear_for (conjC \; *%R) (dotpr u).
Proof. by move=>a v w; rewrite /dotpr dotp_is_antilinear. Qed.
Canonical dotpr_additive u := Additive (linear_dotpr u).
Canonical dotpr_linear u := Linear (linear_dotpr u).
(* Canonical dotp_rev := [revop dotpr of dotp]. *)
Canonical dotp_rev := (@RevOp _ _ _ dotpr dotp (fun _ _ => erefl)).
Canonical dotp_is_bilinear := [bilinear of dotp].

Lemma dotpNl w : {morph (dotp^~ w) : u / -u}.
Proof. exact: linearNl. Qed.

Lemma dotpDl w : {morph (dotp^~ w) : u v / u + v}.
Proof. exact: linearDl. Qed.

Lemma dotpMnl w n : {morph (dotp^~ w) : u / u *+ n}.
Proof. exact: linearMnl. Qed.

Lemma dotp_suml (I : Type) (r : seq I) P (F : I -> E) u :
  [< \sum_(v <- r | P v) F v; u >] = \sum_(v <- r | P v) [< F v; u >].
Proof. exact: linear_suml. Qed.

Lemma dotpNr w : {morph dotp w : u / -u}.
Proof. exact: linearN. Qed.

Lemma dotpDr w : {morph dotp w : u v / u + v}.
Proof. exact: linearD. Qed.

Lemma dotpMnr w n : {morph dotp w : u / u *+ n}.
Proof. exact: linearMn. Qed.

Lemma dotp_sumr (I : Type) (r : seq I) P (F : I -> E) u :
  [< u; \sum_(v <- r | P v) F v >] = \sum_(v <- r | P v) [< u; F v >].
Proof. exact: linear_sum. Qed.

Lemma dotpD u v : [< u + v; u + v >] =
  [< u; u >] + [< v; v >] + ([< u; v >] + [< u; v >]^*).
Proof.
rewrite !(dotpDr, dotpDl) conj_dotp -!addrA; congr (_ + _).
by rewrite [RHS]addrC addrCA !addrA.
Qed.

Lemma dot0p u : [< 0; u >] = 0.
Proof. exact: linear0l. Qed.

Lemma dotp0 u : [< u; 0 >] = 0.
Proof. exact: linear0. Qed.

Lemma dotpZl x u v : [< x *: u; v >] = x^* * [< u; v >].
Proof. exact: linearZl_LR. Qed.

Lemma dotpZr x u v : [< u; x *: v >] = x * [< u; v >].
Proof. exact: linearZ. Qed.

Lemma real_dotpp u : [< u; u >] \is Num.real.
Proof. by apply/CrealP; rewrite conj_dotp. Qed.

End HermitianSpaceTheory.

(* ==================================================================== *)
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
rewrite PE addrNK subr_ge0 {PE}/K !sqrtCK ler_pdivr_mulr //.
by rewrite lt0r ge0_dotp dotp_eq0 nz_v.
Qed.

Lemma CauchySchwartz_sqrt (u v : E) :
  `|[< u; v >]| <= sqrtC [< u; u >] * sqrtC [< v; v >].
Proof.
rewrite -ler_sqr; try by rewrite nnegrE ?mulr_ge0 // sqrtC_ge0 ge0_dotp.
rewrite exprMn !sqrtCK; exact: CauchySchwartz.
Qed.

End CauchySchwartz.

(* ==================================================================== *)
Section HermitianNormedSpace.
Context {E : hermitianType}.

Definition hnorm (u : E) := sqrtC [< u; u >].

Local Lemma hnormE_r (u : E) : hnorm u = sqrtC `|[<u; u>]|.
Proof. by rewrite /hnorm ger0_norm // ge0_dotp. Qed.

Program Definition hermitian_normedZmodMixin :=
  @Num.NormedMixin _ _ (Order.POrder.class [porderType of C]) hnorm _ _ _ _.

Next Obligation.
move=> /= u v; rewrite -[lec _ _]/(hnorm (u + v) <= hnorm u + hnorm v).
rewrite -ler_sqr; try by rewrite nnegrE 1?addr_ge0 // sqrtC_ge0 ge0_dotp.
rewrite !hnormE_r sqrrD !sqrtCK !(dotpDr, dotpDl) mulr2n !addrA.
apply: (le_trans (ler_norm_add _ _)); rewrite ler_add2r.
rewrite -!addrA; apply: (le_trans (ler_norm_add _ _)); rewrite ler_add2l.
apply: (le_trans (ler_norm_add _ _)); rewrite -!hnormE_r.
rewrite -conj_dotp norm_conjC -!mulr2n ler_muln2r /=.
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

Canonical hermitian_normedZmodType :=
  Eval hnf in NormedZmodType C E hermitian_normedZmodMixin.

Lemma hnormE (u : E) : `|u| = sqrtC [< u; u >].
Proof. by []. Qed.

Lemma normrZ (k : C) (u : E) : `|k *: u| = `|k| * `|u|.
Proof.
rewrite hnormE dotpZl dotpZr mulrA sqrtCM.
- by rewrite nnegrE -normCKC -realEsqr.
- by rewrite nnegrE ge0_dotp.
- by rewrite [_^* * _]mulrC -normC_def -hnormE.
Qed.

Lemma dotp_norm (u : E) : [< u; u >] = `|u|^+2.
Proof. by rewrite hnormE sqrtCK. Qed.

End HermitianNormedSpace.

(* ==================================================================== *)
Definition adj_lfun (E F: hermitianType) (f : 'Hom(E,F)) :=
  Vector.Hom (Vector.InternalTheory.f2mx f)^*t.

Notation "f ^A" := (adj_lfun f) (at level 8, format "f ^A"): lfun_scope.

Section AdjLfunTheory.

Variables (S T: hermitianType).

Lemma adjfK : cancel (@adj_lfun S T) (@adj_lfun T S).
Proof. by move=> f; rewrite /adj_lfun /= adjmxK; destruct f. Qed.

Lemma adjf_inj : injective (@adj_lfun S T).
Proof. exact (can_inj adjfK). Qed.

Lemma adjf_is_antilinear : linear_for (conjC \; *:%R) (@adj_lfun S T).
Proof. by move=> a f g; apply f2mx_inj; rewrite /adj_lfun /= !linearP. Qed.
Canonical adjf_antilinear := Linear adjf_is_antilinear.

Lemma adjf_is_additive : additive (@adj_lfun S T).
Proof. exact: linearB. Qed.
Canonical adjf_additive := Additive adjf_is_additive.

Lemma adjfD (f g: 'Hom(S, T)) : ((f + g)^A = f^A + g^A)%VF.
Proof. exact: linearD. Qed.

Lemma adjfZ (c: C) (f: 'Hom(S, T)) : ((c *: f)^A = c^* *: f^A)%VF.
Proof. exact: linearZ. Qed.

Lemma adjfP (c: C) (f g: 'Hom(S, T)) : ((c *: f + g)^A = c^* *: f^A + g^A)%VF.
Proof. exact: linearP. Qed.

Lemma adjf_comp (W: hermitianType) (f: 'Hom(T, W)) (g: 'Hom(S, T)) :
  ((f \o g)^A = g^A \o f^A)%VF.
Proof.
apply/lfunP=> u; rewrite /adj_lfun comp_lfunE comp_f2mx adjmxM.
by rewrite /fun_of_lfun/= unlock /fun_of_lfun_def/= r2vK mulmxA.
Qed.

Lemma adjf1 : ((\1 : 'Hom(S,S))^A = \1)%VF.
Proof.
apply f2mx_inj; rewrite /adj_lfun /= f2mx1. 
by apply/matrixP=>i j; rewrite !mxE eq_sym conjC_nat.
Qed.

End AdjLfunTheory.

(* ==================================================================== *)
(* Definition normalmx {m : nat} :=
  [qualify a M : 'M[C]_m | M *m M^A == M^A *m M]. 

Lemma normalmxP {m : nat} (M : 'M[C]_m) :
  reflect (M *m M^A = M^A *m M) (M \is a normalmx).
Proof. by apply/eqP. Qed.

(* ==================================================================== *)
Definition unitarymx {m : nat} :=
  [qualify a M : 'M[C]_m | (M^A *m M == 1%:M)].

Lemma unitarymxP {m : nat} (M : 'M[C]_m) :
  reflect (M^A *m M = 1%:M) (M \is a unitarymx).
Proof. by apply/eqP. Qed.

Lemma unitarymxPV {m : nat} (M : 'M[C]_m) :
  reflect (M *m M^A = 1%:M) (M \is a unitarymx).
Proof. by apply: (iffP eqP) => [uL | uR]; apply mulmx1C. Qed.

Lemma unitarymxPf {m : nat} (M : 'M[C]_m) :
  reflect (M *m M^A = 1%:M /\ M^A *m M = 1%:M) (M \is a unitarymx).
Proof. by apply: (iffP eqP) => [uL | [uL uR] //]; split=>//; apply mulmx1C. Qed.

(* ==================================================================== *)
Lemma normal_unitary {m : nat} (M : 'M[C]_m) :
  M \is a unitarymx -> M \is a normalmx.
Proof. by case/unitarymxPf=> [uL uR]; apply/normalmxP; rewrite uL uR. Qed.

Lemma det_unitary {m : nat} (M : 'M[C]_m.+1) :
  M \is a unitarymx -> `|\det M| = 1.
Proof.
case/unitarymxPf => [/(congr1 determinant) + _]; rewrite det1 detM.
by rewrite det_adj normC_def => ->; rewrite sqrtC1.
Qed. *)

(* ==================================================================== *)
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

(* ==================================================================== *)
Section GramSchmidt.
Context {E : hermitianType}.

Definition normd (u : E) := `|u|^-1 *: u.

Lemma normd0 : normd 0 = 0.
Proof. by rewrite /normd scaler0. Qed.

Lemma norm_normd (u : E) : `|normd u| = (u != 0)%:R.
Proof.
case: eqP=> /= [->|/eqP nz_u]; first by rewrite normd0 normr0.
by  rewrite /normd normrZ mulrC normfV normr_id divff ?normr_eq0.
Qed.

Lemma dotp_norml (u v : E) :
  [< normd u; v >] = `|u|^-1 * [< u; v >].
Proof. by rewrite /normd dotpZl fmorphV conj_Creal. Qed. (* norm_conjC *)

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

(* -------------------------------------------------------------------- *)
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

End DotP_ONB.

Lemma intro_dotl (H: hermitianType) (u v: H) : 
  (forall t, [< t ; u >] = [< t ; v >]) <-> u = v.
Proof.
move: (vonbasisP {: H}); set e := (vonbasis fullv) => P.
split; last by move=> ->. move=> P1.
have E: basis_of fullv e. by move/andP: P=> [ll lr].
rewrite (coord_basis E (memvf u)) (coord_basis E (memvf v)).
apply eq_bigr=> i _; suff ->: coord e i u = coord e i v. by [].
move: (P1 e`_i); suff E1: forall x, [< e`_i ; x >] = coord e i x. by rewrite !E1.
move=> x; have P2: free e. by move/andP: E=>[ll lr].
rewrite (dotp_onb (memvf e`_i) (memvf x) P) (bigD1 i) //= big1.
by move=> j /negPf nji; rewrite coord_free // eq_sym nji conjC0 mul0r.
by rewrite coord_free // eqxx conjC1 mul1r addr0.
Qed.

Lemma intro_dotr (H: hermitianType) (u v: H) : 
  (forall t, [< u ; t >] = [< v ; t >]) <-> u = v.
Proof.
split; [| move=>-> //]; rewrite -intro_dotl=> P t.
by apply (can_inj conjCK); rewrite !conj_dotp.
Qed.

Import Vector.InternalTheory.

(* -------------------------------------------------------------------- *)
Module CanonicalHermitianSpace.

Record mixin_of (E : hermitianType) : Type := Mixin {
  _ : forall i j, [< r2v (delta_mx 0 i) : E; r2v (delta_mx 0 j) >] = (i == j)%:R;
  _ : (Vector.dim E > 0)%N;
}.

Section ClassDef.
Record class_of (E : Type) : Type := Class {
  base : HermitianSpace.class_of E;
  mixin : mixin_of (HermitianSpace.Pack base)
}.

Local Coercion base : class_of >-> HermitianSpace.class_of.

Structure type := Pack { sort; _ : class_of sort; }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@HermitianSpace.Pack T b0)) :=
  fun bT b & phant_id (HermitianSpace.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ (Phant C) cT xclass.
Definition vectType := @Vector.Pack _ (Phant C) cT xclass.
Definition hermitianType := @HermitianSpace.Pack cT xclass.
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> HermitianSpace.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >->  Equality.type.
Canonical eqType.
Coercion choiceType: type >-> Choice.type.
Canonical choiceType.
Coercion zmodType: type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType: type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion vectType: type >-> Vector.type.
Canonical vectType.
Coercion hermitianType: type >-> HermitianSpace.type.
Canonical hermitianType.

Notation chsType := type.
Notation ChsType mH :=
   (@pack _ _ mH _ _ id _ id).
Notation ChsMixin := Mixin.
Notation "[ 'chsType' 'of' T ]" :=
  (@clone T _ _ id)
  (at level 0, format "[ 'chsType'  'of'  T ]") :
  form_scope.
Notation "[ 'chsType' 'of' T 'for' cT ]" :=
  (@clone T cT _ idfun)
  (at level 0, format "[ 'chsType' 'of'  T  'for'  cT ]") :
  form_scope.
End Exports.
End CanonicalHermitianSpace.

Export CanonicalHermitianSpace.Exports.

Lemma coord_basisT (k: fieldType) (vT: vectType k) (U: {vspace vT}) n 
  (X : n.-tuple vT) v : basis_of U X -> v \in U -> v = \sum_i coord X i v *: X~_i.
Proof. 
have E: \sum_i coord X i v *: X ~_ i = \sum_i coord X i v *: X`_ i.
by apply eq_bigr => i _; rewrite (tnth_nth 0).
move=> P Q; rewrite E; apply (coord_basis P Q).
Qed.

Section ChsTypeTheory.
Variable (H: chsType).

Canonical chs_normedZmodType :=
  Eval hnf in NormedZmodType C H hermitian_normedZmodMixin.

Lemma chsE : forall i j, 
  [< r2v (delta_mx 0 i) : H; r2v (delta_mx 0 j) >] = (i == j)%:R.
Proof. by move=>i j; case: H i j => [? [? []]]. Qed.

Lemma dim_proper : (Vector.dim H > 0)%N.
Proof. by case: H => [? [? []]]. Qed.

Lemma chsdim : (Vector.dim H - 1).+1 = Vector.dim H.
Proof. by rewrite -addn1 subnK// dim_proper. Qed.

Canonical chsf_comp_ringType := lfun_comp_ringType dim_proper.
Canonical chsf_lalgType := lfun_lalgType dim_proper.
Canonical chsf_algType := lfun_algType dim_proper.

Definition eb i : H := r2v (delta_mx 0 i).

Definition ebase_seq := in_tuple [seq eb i | i : 'I_(Vector.dim H)].
Lemma ebase_size : size ebase_seq = Vector.dim H.
Proof. by rewrite size_tuple size_map size_enum_ord. Qed.
Definition ebase := tcast ebase_size ebase_seq.

Lemma tcast_seq (K: eqType) n (t : n.-tuple K) m (eqmn: n = m) :
  tcast eqmn t = t :> seq K.
Proof. by case: m / eqmn. Qed.

Lemma nth_ebase (i: nat) (lti: (i < Vector.dim H)%N) : ebase`_i = eb (Ordinal lti).
Proof. 
have ->: ebase = [seq eb i | i : 'I_(Vector.dim H)] :> seq H.
by rewrite tcast_seq /ebase_seq in_tupleE.
rewrite (nth_map (Ordinal lti)) ?size_enum_ord //.
apply f_equal; apply ord_inj => //=; by rewrite nth_enum_ord.
Qed.

Lemma tnth_ebase i : ebase~_i = eb i.
Proof. by destruct i; rewrite (tnth_nth 0) /= nth_ebase. Qed.

Lemma cbase i j : [< eb i ; eb j >] = (i == j)%:R.
Proof. 
by rewrite /eb; case: H i j => [? [? []]]. Qed.

Lemma decv (u: H) : u = \sum_i ((v2r u) 0 i) *: eb i.
Proof.
rewrite /eb; apply: v2r_inj; rewrite [LHS]matrix_sum_delta.
rewrite (bigD1 0) //= [\sum_(i < 1 | _) _]big1; last first.
by rewrite linear_sum addr0 /=; apply eq_bigr => i _; rewrite linearZ /= r2vK.
by move=> i; move: (ord1 i) => /= /eqP=>->. 
Qed.

Lemma dotp_mulmx (u v: H) : [<u ; v>] = ((v2r u)^*m *m (v2r v)^T) 0 0.
Proof.
rewrite {1}(decv u) {1}(decv v) /conjmx /trmx mxE dotp_suml.
apply eq_bigr => i _; rewrite dotp_sumr !mxE (bigD1 i) //= big1.
by move=> j /negPf nji; rewrite dotpZl dotpZr cbase eq_sym nji !mulr0.
by rewrite dotpZl dotpZr cbase eqxx mulr1 addr0.
Qed. 

Lemma onb_ebase : onbasis_of fullv ebase.
Proof.
apply ort_onbf; first by rewrite dimvf. apply/orthonormalP.
by rewrite size_tuple=>i j Pi Pj; rewrite !nth_ebase cbase.
Qed.

Lemma intro_ebl (u v: H) : 
  (forall i, [< eb i ; u >] = [< eb i ; v >]) <-> u = v.
Proof.
split; last by move=>->. 
move=> P; rewrite -intro_dotl => t; rewrite (decv t) !dotp_suml.
by apply eq_bigr=>i _; rewrite !dotpZl P.
Qed.

Lemma intro_ebr (u v: H) : 
  (forall i, [< u ; eb i >] = [< v ; eb i >]) <-> u = v.
Proof.
split; [| move=>-> //]; rewrite -intro_ebl=> P t.
by apply (can_inj conjCK); rewrite !conj_dotp.
Qed.

End ChsTypeTheory.

Arguments ebase {H}.

Section ChsTypeAdjLfun.

Lemma adj_dotE (S T: chsType) (f: 'Hom(S, T)) u v : 
  [< u ; f v >] = [< (f^A)%VF u ; v >].
Proof.
rewrite !dotp_mulmx /adj_lfun /fun_of_lfun unlock /= /fun_of_lfun_def !mxE /=.
rewrite !r2vK (eq_bigr (fun j=> \sum_k (v2r u 0 j)^* * (v2r v 0 k) * f2mx f k j)).
by move=> i _; rewrite !mxE big_distrr/=; apply eq_bigr => j _; rewrite mulrA.
rewrite exchange_big; apply eq_bigr=>i _.
rewrite conjmxM adjmxEr conjmxK !mxE mulr_suml; apply eq_bigr=>j _.
by rewrite !mxE -!mulrA [v2r v _ _ * _]mulrC.
Qed.

Lemma adj_dotEV (S T: chsType) (f: 'Hom(S, T)) u v : 
  [< u ; (f^A)%VF v >] = [< f u ; v >].
Proof. by rewrite -conj_dotp -[RHS]conj_dotp adj_dotE. Qed.

Lemma adj_dotP (S T: chsType) (f: 'Hom(S, T)) (g: 'Hom(T, S)) :
  reflect (forall u v, ([< u ; f v >] = [< g u ; v >])%VF) ((f == g^A)%VF).
Proof. 
apply (iffP eqP); first by move=>->; apply adj_dotEV.
by move=> P; apply/lfunP=> v; rewrite -intro_dotl => u; rewrite adj_dotEV.
Qed.

End ChsTypeAdjLfun.

Definition conjv (H: chsType) u : H := r2v (v2r u)^*m.
Notation "v ^*v" := (conjv v) (at level 8) : lfun_scope.
 
Lemma conjvE (H: chsType) (u : H) : r2v (v2r u)^*m = conjv u.
Proof. by rewrite /conjv. Qed.

Section ConjvTheory.

Local Open Scope lfun_scope.

Variable (S : chsType). 

Lemma conjveb i : (eb i)^*v = (eb i :S).
Proof. 
rewrite /conjv /eb r2vK; apply f_equal. 
by apply/matrixP=> j k; rewrite !mxE conjC_nat.
Qed.

Lemma conjvBasis i : (ebase~_i)^*v = (ebase~_i : S). 
Proof. by rewrite tnth_ebase conjveb. Qed.

Lemma conjv_is_antilinear : linear_for (conjC \; *:%R) (@conjv S).
Proof. by move=>a u v; rewrite /conjv !linearP. Qed.
Canonical conjv_antilinear := Linear conjv_is_antilinear.

Lemma conjv_is_additive : additive (@conjv S).
Proof. exact: linearB. Qed.
Canonical conjv_additive := Additive conjv_is_additive.

Lemma conjvD (u v: S) : (u + v)^*v = u^*v + v^*v.
Proof. exact: linearD. Qed.

Lemma conjvZ (c: C) (u: S) : (c *: u)^*v = c^* *: u^*v.
Proof. exact: linearZ. Qed.

Lemma conjvP (c: C) (u v: S) : (c *: u + v)^*v = c^* *: u^*v + v^*v.
Proof. exact: linearP. Qed.

Lemma conjvK : involutive (@conjv S).
Proof. by move=> v; rewrite /conjv r2vK conjmxK v2rK. Qed.

Lemma conjv_inj : injective (@conjv S).
Proof. exact (inv_inj conjvK). Qed.

Lemma conjv_dot (u v : S) : [< u^*v ;  v ^*v >] = [< v ; u >].
Proof.
rewrite !dotp_mulmx /conjv !r2vK conjmxK !mxE.
by apply eq_bigr => i _; rewrite !mxE mulrC.
Qed.

Lemma conjv_dotr (u v : S) : [< u ; v^*v >] = [< v; u^*v >].
Proof. by rewrite -{1}(conjvK u) conjv_dot. Qed.

Lemma conjv_dotl (u v : S) : [< u^*v ; v >] = [< v^*v; u >].
Proof. by rewrite -{2}(conjvK u) conjv_dot. Qed.

End ConjvTheory.

Definition conj_lfun (E F: chsType) (f : 'Hom(E,F)) :=
  Vector.Hom (f2mx f)^*m.

Notation "f ^C" := (conj_lfun f) : lfun_scope.

Definition conjfE (S T: chsType) (f: 'Hom(S, T)) u : (f^C u = (f%VF u^*v)^*v)%VF.
Proof. 
rewrite /conj_lfun /conjv /fun_of_lfun unlock /fun_of_lfun_def /= !r2vK.
by rewrite conjmxM conjmxK.
Qed.

Section ChsTypeConjLfun.

Local Open Scope lfun_scope.

Variables (S T: chsType).

Lemma conjfK : involutive (@conj_lfun S T).
Proof. by move=> f; rewrite /conj_lfun /= conjmxK; destruct f. Qed.

Lemma conjf_inj : injective (@conj_lfun S T).
Proof. exact (inv_inj conjfK). Qed.

Lemma conjf_is_antilinear : linear_for (conjC \; *:%R) (@conj_lfun S T).
Proof. by move=> a f g; apply f2mx_inj; rewrite /conj_lfun /= !linearP. Qed.
Canonical conjf_antilinear := Linear conjf_is_antilinear.

Lemma conjf_is_additive : additive (@conj_lfun S T).
Proof. exact: linearB. Qed.
Canonical conjf_additive := Additive conjf_is_additive.

Lemma conjfD (f g: 'Hom(S,T)) : (f + g)^C = f^C + g^C.
Proof. exact: linearD. Qed.

Lemma conjfZ (c: C) (f: 'Hom(S, T)) : (c *: f)^C = c^* *: f^C.
Proof. exact: linearZ. Qed.

Lemma conjfP (c: C) (f g: 'Hom(S, T)) : (c *: f + g)^C = c^* *: f^C + g^C.
Proof. exact: linearP. Qed.

Lemma conjfEV (f: 'Hom(S, T)) v : f^C (v^*v) = (f v)^*v.
Proof. by rewrite conjfE conjvK. Qed.

Lemma conjf_comp (W: chsType) (f: 'Hom(S, T)) (g: 'Hom(W, S)) :
  (f \o g)^C = f^C \o g^C .
Proof. by apply/lfunP=> u; rewrite conjfE !comp_lfunE !conjfE conjvK. Qed.

Lemma conjf1 : ((\1 : 'Hom(S,S))^C = \1)%VF.
Proof. by apply/lfunP=>u; rewrite conjfE !lfunE/= conjvK. Qed.

End ChsTypeConjLfun.

(*Though transpose can be defined for hermitianType, but it is only 
  useful when it's chsType, so we defined it only for chsType *)
Definition tr_lfun (E F: chsType) (f : 'Hom(E,F)) : 'Hom(F, E) 
  := Vector.Hom (f2mx f)^T.

Notation "f ^T" := (tr_lfun f) : lfun_scope.

Lemma trfCA (E F: chsType) (f : 'Hom(E,F)) : (f^T = f^C^A)%VF.
Proof. 
by apply: f2mx_inj; rewrite /adj_lfun /conj_lfun /tr_lfun /= adjmxEl conjmxK.
Qed.

Lemma trfAC (E F: chsType) (f : 'Hom(E,F)) : (f^T = f^A^C)%VF.
Proof. 
by apply: f2mx_inj; rewrite /adj_lfun /conj_lfun /tr_lfun /= adjmxEr conjmxK.
Qed.

Lemma adjfCT (E F: chsType) (f : 'Hom(E,F)) : (f^A = f^C^T)%VF.
Proof. by rewrite trfCA conjfK. Qed.

Lemma adjfTC (E F: chsType) (f : 'Hom(E,F)) : (f^A = f^T^C)%VF.
Proof. by rewrite trfAC conjfK. Qed.

Lemma conjfAT (E F: chsType) (f : 'Hom(E,F)) : (f^C = f^A^T)%VF.
Proof. by rewrite trfAC adjfK. Qed.

Lemma conjfTA (E F: chsType) (f : 'Hom(E,F)) : (f^C = f^T^A)%VF.
Proof. by rewrite trfCA adjfK. Qed.

Section ChsTypeTransLfun.

Variables (S T: chsType).

Lemma trfK : cancel (@tr_lfun S T) (@tr_lfun T S).
Proof. by move=>f; rewrite trfAC trfCA adjfK conjfK. Qed.

Lemma trf_inj : injective (@tr_lfun S T).
Proof. exact (can_inj trfK). Qed.

Lemma trf_is_linear : linear (@tr_lfun S T).
Proof. by move=> a f g; apply: f2mx_inj; rewrite /tr_lfun /= !linearP. Qed.
Canonical trf_linear := Linear trf_is_linear.

Lemma trf_comp (W: chsType) (f: 'Hom(S, T)) (g: 'Hom(W, S)) :
  ((f \o g)^T = g^T \o f^T)%VF .
Proof. by rewrite !trfCA conjf_comp adjf_comp. Qed.

Lemma trf1 : ((\1 : 'Hom(S,S))^T = \1)%VF.
Proof. by rewrite trfAC adjf1 conjf1. Qed.

Lemma lfCAC (f: 'Hom(S, T)) : (f^C^A = f^A^C)%VF.
Proof. by rewrite -trfCA -trfAC. Qed.

Lemma lfACC (f: 'Hom(S, T)) : (f^A^C = f^C^A)%VF.
Proof. by rewrite -trfCA -trfAC. Qed.

Lemma lfATC (f: 'Hom(S, T)) : (f^A^T = f^T^A)%VF.
Proof. by rewrite -conjfAT -conjfTA. Qed.

Lemma lfTAC (f: 'Hom(S, T)) : (f^T^A = f^A^T)%VF.
Proof. by rewrite -conjfAT -conjfTA. Qed.

Lemma lfCTC (f: 'Hom(S, T)) : (f^C^T = f^T^C)%VF.
Proof. by rewrite -adjfCT -adjfTC. Qed.

Lemma lfTCC (f: 'Hom(S, T)) : (f^T^C = f^C^T)%VF.
Proof. by rewrite -adjfCT -adjfTC. Qed.

End ChsTypeTransLfun.

