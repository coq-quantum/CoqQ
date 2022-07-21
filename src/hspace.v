(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import forms spectral.
From mathcomp.analysis Require Import boolp reals.
From mathcomp.real_closed Require Import complex.

Require Import mcextra prodvect hermitian tensor lfundef setdec.
Require Import mxpred mxtopology mxnorm quantum orthomodular.

(************************************************************************)
(* This file define subspace of Hilbert space and its theory            *)
(*        {hspace H} == type of subspace ; coercion to linear function  *)
(*			'End(H) : the projection of the subspace        *)
(*                      Canonical to pred : v \in U                     *)
(*  operations :                                                        *)
(*      A `&` B : join (cup)                                            *)
(*      A `|` B : meet (cap)                                            *)
(*      A `\` B : diff                                                  *)
(*     A `<=` B : subseteq                                              *)
(*      A `<` B : proper subset                                         *)
(*          `0` : empty subspace                                        *)
(* `1`  { : H } : full subspace                                         *)
(*         ~` x : complement subspace                                   *)
(*         \cup : big operator of join                                  *)
(*         \cap : big operator of meet                                  *)
(*      <[ v ]> : span of vector v                                      *)
(*      << X >> : span of seq of vector v                               *)
(*       kerh f : kernal of f , {v | f v = 0}                           *)
(*     cokerh f : cokernal of f , {v | f^A v = 0}                       *)
(*      supph f : support of f, = ~` kerh f                             *)
(*    cosupph f : cosupport of f, = ~` cokerh f                         *)
(************************************************************************)

(* -------------------------------------------------------------------- *)
Import Order.LTheory GRing.Theory Num.Theory ComplexField Num.Def complex Vector.InternalTheory.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Local Notation C := hermitian.C.
Local Notation R := hermitian.R.

Declare Scope hspace_scope.
Local Open Scope ring_scope.

Reserved Notation "{ 'hspace' V }" (at level 0, format "{ 'hspace'  V }").

(* use notations of `<=` *)
Reserved Notation "A `&` B" (at level 48, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "`0`".
Reserved Notation "`1`".
Reserved Notation "~` x" (at level 35, right associativity).

(* since we already use bigcup and bigcap for finset, we here use cup and cap for hspace *)
Reserved Notation "\cup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \cup_ i '/  '  F ']'").
Reserved Notation "\cup_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \cup_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\cup_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \cup_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\cup_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \cup_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\cup_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \cup_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\cup_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \cup_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\cup_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \cup_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\cup_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \cup_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\cup_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \cup_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\cup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \cup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\cup_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \cup_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\cup_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \cup_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\cap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \cap_ i '/  '  F ']'").
Reserved Notation "\cap_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \cap_ ( i  <-  r  |  P )  F ']'").
Reserved Notation "\cap_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \cap_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\cap_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \cap_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\cap_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \cap_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\cap_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \cap_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\cap_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \cap_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\cap_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \cap_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\cap_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \cap_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\cap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \cap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\cap_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \cap_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\cap_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \cap_ ( i  'in'  A ) '/  '  F ']'").

Delimit Scope hspace_scope with HS.

Local Open Scope hspace_scope.
Fact hspace_display : unit. Proof. by []. Qed.

Notation "x '`<=`' y" := (@Order.le hspace_display _ x y) (at level 70, no associativity) : hspace_scope.
Notation "x '`<`' y" := (@Order.lt hspace_display _ x y) (at level 70, no associativity) : hspace_scope.
Notation "x '`|`' y" := (@Order.join hspace_display _ x y) (at level 52, left associativity) : hspace_scope.
Notation "x '`&`' y" := (@Order.meet hspace_display _ x y) (at level 48, left associativity) : hspace_scope.
Notation "`0`" := (@Order.bottom hspace_display _) : hspace_scope.
Notation "`1`" := (@Order.top hspace_display _) : hspace_scope.
Notation "~` x" := (@orthomodular.compl hspace_display _ x) (at level 35, right associativity) : hspace_scope.
Reserved Notation "A `\` B" (at level 50, left associativity).
Notation "\cup_ ( i <- r | P ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i <- r | P%B) U%HS) : hspace_scope.
Notation "\cup_ ( i <- r ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i <- r) U%HS) : hspace_scope.
Notation "\cup_ ( m <= i < n | P ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(m <= i < n | P%B) U%HS) : hspace_scope.
Notation "\cup_ ( m <= i < n ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(m <= i < n) U%HS) : hspace_scope.
Notation "\cup_ ( i | P ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i | P%B) U%HS) : hspace_scope.
Notation "\cup_ i U" :=
  (\big[ @Order.join hspace_display _ /`0`]_i U%HS) : hspace_scope.
Notation "\cup_ ( i : t | P ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i : t | P%B) U%HS) (only parsing) : hspace_scope.
Notation "\cup_ ( i : t ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i : t) U%HS) (only parsing) : hspace_scope.
Notation "\cup_ ( i < n | P ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i < n | P%B) U%HS) : hspace_scope.
Notation "\cup_ ( i < n ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i < n) U%HS) : hspace_scope.
Notation "\cup_ ( i 'in' A | P ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i in A | P%B) U%HS) : hspace_scope.
Notation "\cup_ ( i 'in' A ) U" :=
  (\big[ @Order.join hspace_display _ /`0`]_(i in A) U%HS) : hspace_scope.

Notation "\cap_ ( i <- r | P ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i <- r | P%B) U%HS) : hspace_scope.
Notation "\cap_ ( i <- r ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i <- r) U%HS) : hspace_scope.
Notation "\cap_ ( m <= i < n | P ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(m <= i < n | P%B) U%HS) : hspace_scope.
Notation "\cap_ ( m <= i < n ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(m <= i < n) U%HS) : hspace_scope.
Notation "\cap_ ( i | P ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i | P%B) U%HS) : hspace_scope.
Notation "\cap_ i U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_i U%HS) : hspace_scope.
Notation "\cap_ ( i : t | P ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i : t | P%B) U%HS) (only parsing) : hspace_scope.
Notation "\cap_ ( i : t ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i : t) U%HS) (only parsing) : hspace_scope.
Notation "\cap_ ( i < n | P ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i < n | P%B) U%HS) : hspace_scope.
Notation "\cap_ ( i < n ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i < n) U%HS) : hspace_scope.
Notation "\cap_ ( i 'in' A | P ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i in A | P%B) U%HS) : hspace_scope.
Notation "\cap_ ( i 'in' A ) U" :=
  (\big[ @Order.meet hspace_display _ /`1`]_(i in A) U%HS) : hspace_scope.

Section HspaceType.
Variable (V : chsType).
(* projection as sub hilbert space *)

Variant hspace_t := Hspace of 'FP(V).
Coercion hspace_proj (M : hspace_t) := let: Hspace M := M in M.
Canonical hspace_t_subType := Eval hnf in [newType for hspace_proj].

Definition hspace_t_eqMixin := Eval hnf in [eqMixin of hspace_t by <:].
Canonical  hspace_t_eqType  := Eval hnf in EqType hspace_t hspace_t_eqMixin.
Definition hspace_t_choiceMixin := [choiceMixin of hspace_t by <:].
Canonical  hspace_t_choiceType  := Eval hnf in ChoiceType hspace_t hspace_t_choiceMixin.

Definition projlf_lporderMixin := [porderMixin of 'FP(V) by <:].
Canonical projlf_lporderType :=
  Eval hnf in POrderType vorder_display 'FP(V) projlf_lporderMixin.
Definition hspace_t_porderMixin := [porderMixin of hspace_t by <:].
Canonical hspace_t_porderType :=
  Eval hnf in POrderType hspace_display hspace_t hspace_t_porderMixin.

Lemma hspace_inj : injective hspace_proj. Proof. exact: val_inj. Qed.

Definition hspace_of of phant V := hspace_t.
Identity Coercion type_hspace_of : hspace_of >-> hspace_t.
End HspaceType.

Bind Scope ring_scope with hspace_of.
Bind Scope ring_scope with hspace_t.

Notation "{ 'hspace' V }" := (@hspace_of _ (Phant V)).

Section HspaceOf.
Variable (V : chsType).
Canonical hspace_subType    := Eval hnf in [subType    of {hspace V}].
Canonical hspace_eqType     := Eval hnf in [eqType     of {hspace V}].
Canonical hspace_choiceType := Eval hnf in [choiceType of {hspace V}].
Canonical hspace_porderType := Eval hnf in [porderType of {hspace V}].
End HspaceOf.

Section HspaceOfProj.
Variable (H : chsType).

Fact hspace_key : unit. Proof. by []. Qed.
Definition hspace_of_proj_def (P : 'FP(H)) : {hspace H} := Hspace P.
Definition hspace_of_proj := locked_with hspace_key hspace_of_proj_def.
Canonical hspace_of_unlockable := [unlockable of hspace_of_proj].

Lemma hsE F : (hspace_of_proj F)%:VF = F.
Proof. by rewrite unlock/=. Qed.

Lemma hspaceP (A B : {hspace H}) : A =1 B <-> A = B.
Proof. by split=>[eqAB|->//]; apply/val_inj/val_inj=>/=; apply/lfunP. Qed.

Lemma eq_hs (F1 F2 : 'FP(H)) : 
  (F1 =1 F2) -> hspace_of_proj F1 = hspace_of_proj F2.
Proof. by move=> eq_F; apply/hspaceP => v; rewrite !hsE eq_F. Qed.

End HspaceOfProj.


Notation HSType P := (hspace_of_proj P).

Import Vector.InternalTheory.

Section HspacePred.
Variable (H : chsType).
Implicit Type (U V : {hspace H}).

Definition pred_of_hspace U : {pred H} :=
  (fun v => U v == v).
Canonical hspace_predType :=
  @PredType _ {hspace H} (@pred_of_hspace).

Lemma memhE U x : x \in U = (U x == x).
Proof. by []. Qed.

End HspacePred.

Section HspaceSupport.
Variable (T : numClosedFieldType).

Definition boolmx_of m n (M : 'M[T]_(m,n)) : 'M[T]_(m,n) :=
  \matrix_(i,j) (M i j != 0)%:R.
Lemma boolmx_of_bool m n (M : 'M[T]_(m,n)) :
  boolmx_of M \is a boolmx.
Proof. by apply/boolmxP=>i j; rewrite !mxE; case: (M i j != 0); rewrite eqxx// orbT. Qed.

Lemma boolmx_of_map m n (M : 'M[T]_(m,n)) (f : {rmorphism T -> T}) :
  map_mx f (boolmx_of M) = (boolmx_of M).
Proof. by apply/matrixP=>i j; rewrite !mxE; case: (M i j != 0); rewrite ?rmorph0 ?rmorph1. Qed.

Lemma boolmx_of_conj m n (M : 'M[T]_(m,n)) :
  (boolmx_of M)^*m = (boolmx_of M).
Proof. exact: boolmx_of_map. Qed.

Lemma boolmx_of_idem m n (M : 'M[T]_(m,n)) :
  (boolmx_of M) .* (boolmx_of M) = (boolmx_of M).
Proof. apply/boolmx_dmul/boolmx_of_bool. Qed.

Lemma boolmx_of_mulid m n (M : 'M[T]_(m,n)) :
  (boolmx_of M) .* M = M.
Proof.
apply/matrixP=>i j; rewrite !mxE; case: eqP=>[->|_];
by rewrite ?mulr0// mul1r.
Qed.

Lemma boolmx_of_diag m (M : 'rV[T]_m) :
  boolmx_of (diag_mx M) = diag_mx (boolmx_of M).
Proof.
apply/matrixP=>i j; rewrite !mxE.
by case: (i == j); rewrite ?mulr1n// ?mulr0n eqxx.
Qed.

Lemma boolmx_of_inv m n (A : 'M[T]_(m,n)) :
  boolmx_of A = A .^-1 .* A.
Proof.
apply/matrixP=>i j; rewrite !mxE.
by case: eqP=>[->|/eqP P1]; rewrite ?mulr0// mulVf.
Qed.

Lemma svd_d_invC m n (A : 'M[T]_(m,n)) :
  ((svd_d A).^-1)^*m = (svd_d A).^-1.
Proof. 
apply/matrixP=>i j; rewrite !mxE geC0_conj// invr_ge0 -nnegrE.
apply/nnegmxP/svd_diag_nneg/svd_d_svd_diag.
Qed.

Lemma svd_d_conj m n (A : 'M[T]_(m, n)) :
  (svd_d A)^*m = svd_d A.
Proof.
apply/matrixP=>i j; rewrite mxE; apply/CrealP/realmxP/svd_diag_real/svd_d_svd_diag.
Qed.

Lemma svd_d_exdr_mul m n (M N : 'rV[T]_(minn m n)) :
  svd_d_exdr M .* svd_d_exdr N = svd_d_exdr (M .* N).
Proof.
apply/matrixP=>i j; rewrite !mxE !castmxE/= cast_ord_id.
set x := (cast_ord (esym (min_idr m n)) j).
rewrite  -(splitK x); case: (fintype.split x)=>a/=;
by rewrite ?row_mxEl ?row_mxEr mxE// mul0r.
Qed.

Lemma cdiag_diag_mul m n (A B : 'rV[T]_(minn m n)) :
  cdiag_mx A *m diag_mx (svd_d_exdr B) = cdiag_mx (A .* B).
Proof.
rewrite mul_mx_diag; apply/matrixP=>i j.
rewrite mxE !castmxE/= cast_ord_id.
set x := (cast_ord (esym (min_idl m n)) i).
set y := (cast_ord (esym (min_idr m n)) j).
rewrite  -(splitK x) -(splitK y).
case: (fintype.split x)=>a/=; case: (fintype.split y)=>b/=;
rewrite ?block_mxEdl ?block_mxEdr ?block_mxEul ?block_mxEur ?row_mxEl ?row_mxEr;
by rewrite !mxE ?mul0r//; case: eqP=>[->|_]; rewrite ?mulr1n// !mulr0n mul0r.
Qed.

Definition pinvmx_ m n (A : 'M[T]_(m,n)) :=
  (svd_u A) *m cdiag_mx ((svd_d A).^-1) *m (svd_v A)^*t.

Lemma mxrank_cast (R : fieldType) p q p' q' (eqpq : (p = p') * (q = q')) (A : 'M[R]_(p,q)) :
  \rank (castmx eqpq A) = \rank A.
Proof. by case: eqpq=>P Q; case: p' / P; case: q' / Q; rewrite castmx_id. Qed.

Lemma rank_cdiagmx p q (d : 'rV[T]_(minn p q)) :
  \rank (cdiag_mx d) = \rank (diag_mx d).
Proof. by rewrite /cdiag_mx mxrank_cast rank_diag_block_mx mxrank0 addn0. Qed.

Lemma pinvmx_rank m n (A : 'M[T]_(m,n)) :
  \rank (pinvmx_ A) = \rank A.
Proof. 
rewrite /pinvmx_ {4}(svdE A). do 2 rewrite mxrank_mulmxUC ?svd_pE// mxrank_mulUmx ?svd_pE//.
rewrite !rank_cdiagmx !rank_diagmx; apply eq_bigr=>i _.
by rewrite mxE invr_eq0.
Qed.

Lemma mxrank_conj m n (A : 'M[T]_(m,n)) :
  \rank (A^*m) = \rank A.
Proof. by rewrite conjmxE mxrank_map. Qed.

Lemma mxrank_trmxC m n (A : 'M[T]_(m,n)) :
  \rank (A^*t) = \rank A.
Proof. by rewrite adjmxEr mxrank_conj mxrank_tr. Qed.

Definition suppmx m n (A : 'M[T]_(m,n)) :=
  A *m (pinvmx_ A)^*t.

Definition cosuppmx m n (A : 'M[T]_(m,n)) :=
  (pinvmx_ A)^*t *m A.

Lemma suppmx_herm m n (A : 'M[T]_(m,n)) :
  suppmx A \is hermmx.
Proof.
apply/hermmxP; rewrite /suppmx {1 3}(svdE A) /pinvmx_ !adjmxM !adjmxK !mulmxA.
rewrite !mulmxKtV ?svd_pE//; f_equal; rewrite -!mulmxA; f_equal.
by rewrite !cdiag_mx_mull svd_d_invC svd_d_conj dmulmxC.
Qed.

Lemma cosuppmx_herm m n (A : 'M[T]_(m,n)) :
  cosuppmx A \is hermmx.
Proof.
apply/hermmxP; rewrite /cosuppmx {2 4}(svdE A) /pinvmx_ !adjmxM !adjmxK !mulmxA.
rewrite !mulmxKtV ?svd_pE//; f_equal; rewrite -!mulmxA; f_equal.
by rewrite !cdiag_mx_mulr svd_d_invC svd_d_conj dmulmxC.
Qed.

Lemma suppmx_id m n (A : 'M[T]_(m,n)) :
  suppmx A *m A = A.
Proof.
rewrite /suppmx {1 3 4}(svdE A) /pinvmx_ !adjmxM !adjmxK !mulmxA.
rewrite !mulmxKtV ?svd_pE//; f_equal; rewrite -!mulmxA; f_equal.
by rewrite cdiag_mx_mulr svd_d_invC svd_d_exdr_mul -boolmx_of_inv 
  cdiag_diag_mul dmulmxC boolmx_of_mulid.
Qed.

Lemma cosuppmx_id m n (A : 'M[T]_(m,n)) :
  A *m cosuppmx A = A.
Proof. by move: (suppmx_id A); rewrite /cosuppmx mulmxA. Qed.

Lemma suppmx_rank m n (A : 'M[T]_(m,n)) :
  \rank (suppmx A) = \rank A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
rewrite /suppmx; exact: mxrankM_maxl.
rewrite -{1}(suppmx_id A); exact: mxrankM_maxl.
Qed.

Lemma cosuppmx_rank m n (A : 'M[T]_(m,n)) :
  \rank (cosuppmx A) = \rank A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
rewrite /cosuppmx; exact: mxrankM_maxr.
rewrite -{1}(cosuppmx_id A); exact: mxrankM_maxr.
Qed.

Lemma suppmx_proj m n (A : 'M[T]_(m,n)) :
  suppmx A \is projmx.
Proof.
apply/projmxP_id; split; first by apply suppmx_herm.
by rewrite {2}/suppmx mulmxA suppmx_id.
Qed.

Lemma cosuppmx_proj m n (A : 'M[T]_(m,n)) :
  cosuppmx A \is projmx.
Proof.
apply/projmxP_id; split; first by apply cosuppmx_herm.
by rewrite {1}/cosuppmx -mulmxA cosuppmx_id.
Qed.

End HspaceSupport.

Section HspaceSupportLf.
Variable (H : chsType).
Implicit Type (G : chsType).

Definition pinvlf G (A : 'Hom(H,G)) := Vector.Hom (pinvmx_ (f2mx A)).

Definition supplf G (A : 'Hom(H,G)) := (pinvlf A)^A \o A.

Definition cosupplf G (A : 'Hom(H,G)) := A \o (pinvlf A)^A.

Lemma pinvlf_rank G (A : 'Hom(H,G)) : \Rank (pinvlf A) = \Rank A.
Proof. exact: pinvmx_rank. Qed.

Lemma supplf_rank G (A : 'Hom(H,G)) : \Rank (supplf A) = \Rank A.
Proof. by rewrite /lfrank/supplf f2mx_comp/= -[RHS]suppmx_rank. Qed.

Lemma cosupplf_rank G (A : 'Hom(H,G)) : \Rank (cosupplf A) = \Rank A.
Proof. by rewrite /lfrank/cosupplf f2mx_comp/= -[RHS]cosuppmx_rank. Qed.

Lemma suppvlf G (A : 'Hom(H,G)) : A \o supplf A = A.
Proof. apply/f2mx_inj; rewrite /supplf !f2mx_comp/=; exact: suppmx_id. Qed.

Lemma cosupplfv G (A : 'Hom(H,G)) : cosupplf A \o A = A.
Proof. apply/f2mx_inj; rewrite /cosupplf !f2mx_comp/=; exact: cosuppmx_id. Qed.

Lemma supplf_proj G (A : 'Hom(H,G)) : supplf A \is projlf.
Proof. rewrite qualifE /supplf f2mx_comp/=; exact: suppmx_proj. Qed.
Canonical supplf_projfType G A := ProjfType (@supplf_proj G A).
Canonical supplf_obsfType G (A : 'Hom(H,G)) := Eval hnf in 
  [obs of supplf A as [obs of [proj of supplf A]]].
Canonical supplf_psdfType G (A : 'Hom(H,G)) := Eval hnf in 
  [psd of supplf A as [psd of [proj of supplf A]]].
Canonical supplf_hermfType G (A : 'Hom(H,G)) := Eval hnf in 
  [herm of supplf A as [herm of [proj of supplf A]]].

Lemma cosupplf_proj G (A : 'Hom(H,G)) : cosupplf A \is projlf.
Proof. rewrite qualifE /cosupplf f2mx_comp/=; exact: cosuppmx_proj. Qed.
Canonical cosupplf_projfType G A := ProjfType (@cosupplf_proj G A).
Canonical cosupplf_obsfType G (A : 'Hom(H,G)) := Eval hnf in 
  [obs of cosupplf A as [obs of [proj of cosupplf A]]].
Canonical cosupplf_psdfType G (A : 'Hom(H,G)) := Eval hnf in 
  [psd of cosupplf A as [psd of [proj of cosupplf A]]].
Canonical cosupplf_hermfType G (A : 'Hom(H,G)) := Eval hnf in 
  [herm of cosupplf A as [herm of [proj of cosupplf A]]].

End HspaceSupportLf.

Section MatrixExtra.
Variable (R: numClosedFieldType) (m : nat).
Implicit Type (A : 'M[R]_m).

Lemma uintmx_dexp p q (B : 'M[R]_(p,q)) n : B \is a uintmx -> B.^+ n \is a uintmx.
Proof.
move=>/uintmxP P1; apply/uintmxP=>i j; move: (P1 i j); 
  rewrite mxE=>/andP[P2 P3]; apply/andP; split.
rewrite exprn_ge0//. by apply: exprn_ile1.
Qed.

Lemma obsmx_idem_obs A : A \is obsmx -> A *m A \is obsmx.
Proof.
move=>/obsmxP[Ah sA]; move: {+}Ah {+}Ah=>/hermmx_normal/unitarymx_spectralP Ad/hermmxP Aa.
apply/obsmxP; split. by apply/hermmxP; rewrite adjmxM -Aa.
rewrite {1}Aa.
have /esym: A^*t *m A = (spectralmx A)^*t *m diag_mx ((spectral_diag A).^+2) *m spectralmx A.
rewrite {1 2}Ad !adjmxM adjmxK !mulmxA  mulmxtVK ?spectral_unitarymx// diag_mx_adj mulmxACA diag_mx_dmul.
do ? f_equal; apply/matrixP=>i j; rewrite !mxE -normCKC ger0_norm//.
by apply/nnegmxP/uintmx_nneg.
move=>/(spectral_unique (spectral_unitarymx _))[s Ps].
by apply/uintmxP=>i j; rewrite -Ps mxE; apply/uintmxP/uintmx_dexp.
Qed.
End MatrixExtra.

Section Projlf.
Variable (H : chsType).
Implicit Type (U V W : {hspace H}).

Lemma ranklf_le_dom (G : chsType) (U : 'Hom(H,G)) : (\Rank U <= Vector.dim H)%N.
Proof. by rewrite /lfrank rank_leq_row. Qed.
Lemma ranklf_le_codom (G : chsType) (U : 'Hom(H,G)) : (\Rank U <= Vector.dim G)%N.
Proof. by rewrite /lfrank rank_leq_col. Qed.

Definition dimh U := \Rank U.
Notation "\Dim U" := (dimh U) (at level 10, U at level 8, format "\Dim  U").

Lemma dimh_rank U : \Dim U = \Rank U. Proof. by []. Qed.
Lemma dimh_trlf U : (\Dim U)%:R = \Tr U. 
Proof. by rewrite dimh_rank projlf_trlf// projf_proj. Qed.

Lemma obslf_idem_obs (P : 'End(H)) : P \is obslf -> P \o P \is obslf.
Proof. by rewrite qualifE=>/obsmx_idem_obs; rewrite [_ \is obslf]qualifE f2mx_comp. Qed.

Lemma obslf_idem_obsV (P : 'End(H)) : P \is psdlf -> P \o P \is obslf -> P \is obslf.
Proof.
move=>P1/obslfP[_ P2]; apply/obslfP; split=>// u.
rewrite -(@ler_pexpn2r _ 2%N)// ?nnegrE// ?ge0_dotp//.
2: rewrite -[[< u; P u >]]ger0_norm. 1,2: by apply/psdlfP.
apply: (le_trans (CauchySchwartz _ _)); rewrite expr2 ler_pmul// ?ge0_dotp//.
by rewrite hermlf_dotE ?psdlf_herm// -comp_lfunE.
Qed.

Lemma obslf_norm (P : 'End(H)) x : P \is obslf -> `|P x| <= `|x|.
Proof.
move=>P1; rewrite -(@ler_pexpn2r _ 2%N)// ?nnegrE// -!dotp_norm.
rewrite hermlf_dotE ?obslf_herm// -comp_lfunE.
by move: P1=>/obslf_idem_obs/obslfP[].
Qed.
Lemma obsf_norm (P : 'FO(H)) x : `|P x| <= `|x|.
Proof. apply/obslf_norm/obsf_obs. Qed.

(* we focus on projlf *)
Lemma projlf_norm (P : 'End(H)) x : P \is projlf -> `|P x| <= `|x|.
Proof. by move=>P1; apply/obslf_norm/projlf_obs. Qed.

Lemma projf_norm (P : 'FP(H)) x : `|P x| <= `|x|.
Proof. exact: obsf_norm. Qed.

Lemma cplmt_dec (U : 'End(H)) x : x = U x + (cplmt U) x.
Proof. by rewrite /cplmt lfunE/= !lfunE/= addrC addrNK. Qed.

Lemma projf_cplmtMr (P : 'FP(H)) : P \o P^⟂ = 0.
Proof. by rewrite /cplmt linearBr/= projf_idem comp_lfun1r subrr. Qed.
Lemma projf_cplmtMl (P : 'FP(H)) : P^⟂ \o P = 0.
Proof. by rewrite /cplmt linearBl/= projf_idem comp_lfun1l subrr. Qed.

Lemma projf_lefCP (P1 P2 : 'FP(H)) : (forall x, P2 x == 0 -> (P1 x == 0)) -> P1%:VF ⊑ P2.
Proof.
move=>H1. apply/lef_dot=>v. rewrite !projf_dot/= ler_pexpn2r// ?nnegrE//.
rewrite {1}(cplmt_dec P2 v) linearD/=.
have /H1/eqP-> : (P2 (P2^⟂ v) == 0) by rewrite -comp_lfunE projf_cplmtMr lfunE.
by rewrite addr0 projf_norm.
Qed.

Lemma projf_lefP (P1 P2 : 'FP(H)) : (forall x, P1 x == x -> (P2 x == x)) -> P1%:VF ⊑ P2.
Proof.
move=>H1. rewrite cplmt_lef; apply/projf_lefCP=>x/=.
by rewrite /cplmt !lfunE/= !lfunE/= subr_eq0 eq_sym=>/H1/eqP->; rewrite subrr.
Qed.

Lemma projf_eqCP (P1 P2 : 'FP(H)) : (forall x, P1 x == 0 = (P2 x == 0)) -> P1 = P2.
Proof. by move=>IH; apply/val_inj/le_anti/andP; split; apply/projf_lefCP=>x; rewrite IH. Qed.

Lemma projf_eqP (P1 P2 : 'FP(H)) : (forall x, P1 x == x = (P2 x == x)) -> P1 = P2.
Proof. by move=>IH; apply/val_inj/le_anti/andP; split; apply/projf_lefP=>x; rewrite IH. Qed.

End Projlf.

Notation "\Dim U" := (dimh U) (at level 10, U at level 8, format "\Dim  U").

Section VS2Proj.
Variable (H : chsType).

Let memvK v (U : {vspace H}) : (v \in U) = (v2r v <= vs2mx U)%MS.
Proof. by rewrite -genmxE. Qed.

Lemma vs2hs_proj (U : {vspace H}) : Vector.Hom (cosuppmx (vs2mx U)) \is projlf.
Proof. by rewrite qualifE/= cosuppmx_proj. Qed.

Definition vs2hs (U : {vspace H}) := HSType (ProjfType (vs2hs_proj U)).

Lemma memv2h (U : {vspace H}) x : x \in U = (x \in vs2hs U).
Proof. 
rewrite memhE hsE -(can_eq v2rK) unlock/= r2vK memvK; apply/eqb_iff; split.
rewrite /vs2hs; move=>/submxP[D]. set A := vs2mx U.
move=>->. rewrite -mulmxA cosuppmx_id//.
move=>/eqP; rewrite /cosuppmx mulmxA=>P.
apply/submxP; exists (v2r x *m (pinvmx_ (vs2mx U))^*t).
by rewrite P.
Qed.

Definition hs2vs (P : {hspace H}) := mx2vs (f2mx P).
Lemma vs2hsK : cancel vs2hs hs2vs.
Proof.
move=>U. rewrite /hs2vs/= hsE/=.
apply/vspaceP=>x. rewrite [RHS]memv2h/vs2hs/= memhE hsE -(can_eq v2rK) unlock/= r2vK.
move: (cosuppmx_proj (vs2mx U))=>/projmxP_id[_] P.
rewrite memvK mx2vsK; apply/eqb_iff; split.
by move=>/submxP[D] ->; rewrite -mulmxA P.
by move=>/eqP P1; apply/submxP; exists (v2r x); rewrite P1.
Qed.

Lemma vs2hs_inj : injective vs2hs.
Proof. exact: (can_inj vs2hsK). Qed.

Lemma memh2v (U : {hspace H}) x : (x \in U) = (x \in hs2vs U).
Proof. 
rewrite memhE -(can_eq v2rK) unlock/= /hs2vs r2vK memvK; apply/eqb_iff.
move: (mx2vsK (f2mx U))=>/eqmxP/andP[P1 P2].
move: (projf_idem U)=>/(f_equal f2mx); rewrite f2mx_comp=>P3.
split=>[/eqP P4|P4].
by apply: (submx_trans _ P2); apply/submxP; exists (v2r x); rewrite P4.
by move: (submx_trans P4 P1)=>/submxP[D]->; rewrite -mulmxA P3.
Qed.

Lemma hs2vs_inj : injective hs2vs.
Proof.
move=>U1 U2 /vspaceP=>P. apply/val_inj/projf_eqP=>x.
by move: (P x); rewrite -!memh2v.
Qed.

Lemma hs2vsK : cancel hs2vs vs2hs.
Proof. by move=>U; apply/hs2vs_inj/vs2hsK. Qed.

End VS2Proj.


Module HspaceOrthoModularLattice.

Module Import BasicConstruct.

(* this construct will be hide after Orthomodular lattices *)
Section BasicConstruct.
Variable (H : chsType).
Implicit Type (U : {hspace H}).

Definition hspace0 := HSType (zero_projfType H).
Definition hspace1 := HSType (one_projfType H).
Definition hscmplt U := HSType (cplmt_projfType U).
Definition supph G A := HSType (@supplf_projfType H G A).
Definition cosupph G A := HSType (@cosupplf_projfType H G A).

Definition cuph U V := supph (U%:VF + V).
Definition caph U V := (hscmplt (cuph (hscmplt U) (hscmplt V))).

Lemma hscmpltE U : (hscmplt U)%:VF = U^⟂.
Proof. by rewrite hsE. Qed.

Lemma hs_vec_dec U x : x = U x + (hscmplt U) x.
Proof. by rewrite hsE/= /cplmt lfunE/= !lfunE/= addrC addrNK. Qed.

End BasicConstruct.
End BasicConstruct.

Notation "P '^⟂'" := (hscmplt P) : hspace_scope.
Notation hs1 := (@hspace1 _).
Notation hs0 := (@hspace0 _).

(* don't export *)
Module Import HspacePredTheory.

Section HspacePredTheory.
Variable (H : chsType).
Implicit Type (U V : {hspace H}) (x y : H).

Lemma hs_sub_t U V : (U `<=` V) = ((U : (hspace_t _)) `<=` V).
Proof. by []. Qed.

Lemma hs_sub_proj U V : (U `<=` V) = ((U : 'FP) ⊑ V).
Proof. by []. Qed.

Lemma leh_lef U V : (U `<=` V) = (U%:VF ⊑ V).
Proof. by rewrite hs_sub_t hs_sub_proj leEsub. Qed.

Lemma memhCE U x : x \in U = ((U^⟂)%HS x == 0).
Proof. 
by rewrite memhE eq_sym -subr_eq0 hsE/= /cplmt lfunE/= !lfunE/=.
Qed.

Lemma memhP U x : reflect (U x = x) (x \in U).
Proof. by rewrite memhE; exact: eqP. Qed.

Lemma memhCP U x : reflect ((U^⟂)%HS x = 0) (x \in U).
Proof. by rewrite memhCE; exact: eqP. Qed.

Lemma memh_dotCE U x : x \in U = ([< x ; (U^⟂)%HS x >] == 0).
Proof. by rewrite memhCE projf_dot expf_eq0/= normr_eq0. Qed.

Lemma memh_dotE U x : x \in U = ([< x ; U x >] == [< x ; x >]).
Proof. by rewrite memh_dotCE hsE/= /cplmt/= lfunE/= !lfunE/= linearBr/= subr_eq0 eq_sym. Qed.  

Lemma memh_dotCP U x : reflect ([< x ; (U^⟂)%HS x >] = 0) (x \in U).
Proof. rewrite memh_dotCE; exact: eqP. Qed.

Lemma memh_dotP U x : reflect ([< x ; U x >] = [< x ; x >]) (x \in U).
Proof. rewrite memh_dotE; exact: eqP. Qed. 

Lemma memh_proj U x : U x \in U.
Proof. by rewrite memhE -comp_lfunE projf_idem. Qed.

Lemma memh_projC U x : (U^⟂)%HS (U x) = 0.
Proof. by apply/memhCP/memh_proj. Qed.

Lemma memh_normE U x : x \in U = (`|U x| == `|x|).
Proof. by rewrite memh_dotE projf_dot dotp_norm eqr_expn2//. Qed.

Lemma memh_normCE U x : x \in U = (`|(U^⟂)%HS x| == 0).
Proof. by rewrite memh_dotCE projf_dot expf_eq0/=. Qed.

Lemma memh_normP U x : reflect (`|U x| = `|x|) (x \in U).
Proof. rewrite memh_normE; exact: eqP. Qed.

Lemma memh_normCP U x : reflect (`|(U^⟂)%HS x| = 0) (x \in U).
Proof. rewrite memh_normCE; exact: eqP. Qed.

Lemma lehP U V : 
  reflect (forall x, (x \in U) -> (x \in V)) (U `<=` V).
Proof.
rewrite leh_lef; apply/(iffP idP).
rewrite cplmt_lef=>/lef_dot P x; rewrite !memh_normCE !hsE/==>/eqP P1; move: (P x).
by rewrite !projf_dot/= ler_pexpn2r// ?nnegrE// P1 normr_le0=>/eqP->; rewrite normr0.
move=>P. rewrite cplmt_lef; apply/lef_dot=>x.
rewrite -!hscmpltE !projf_dot ler_pexpn2r// ?nnegrE// (hs_vec_dec U x).
rewrite !linearD/= memh_projC projlf_idemE.
move: (P _ (memh_proj U x))=>/memhCP->.
by rewrite ?add0r projf_norm.
Qed.

Lemma lehCP U V : 
  reflect (forall x, (x \in (V^⟂)%HS) -> (x \in (U^⟂)%HS)) (U `<=` V).
Proof. rewrite leh_lef cplmt_lef -!hscmpltE -leh_lef; exact: lehP. Qed.

Lemma eqhP (U V : {hspace H}) : U =i V <-> U = V.
Proof. by split=>[P|->//]; apply/le_anti/andP; split; apply/lehP=>x; rewrite P. Qed.

Lemma mem0h U : 0 \in U.
Proof. by rewrite memhE linear0. Qed.

Lemma memh1 x : x \in hs1.
Proof. by rewrite memhE hsE/= lfunE. Qed.

Lemma memh0 x : x \in hs0 = (x == 0).
Proof. by rewrite memhE hsE/= lfunE/= eq_sym. Qed.

Lemma le0h U : hs0 `<=` U.
Proof. by apply/lehP=>x; rewrite memh0=>/eqP->; apply/mem0h. Qed.

Lemma leh1 U : U `<=` hs1.
Proof. apply/lehP=>x _; apply/memh1. Qed.

Lemma hsC0 : (hs0^⟂)%HS = hs1 :> {hspace H}.
Proof. by apply/hspaceP=>x; rewrite hsE/=/cplmt !hsE/= subr0. Qed.

Lemma hsC1 : (hs1^⟂)%HS = hs0 :> {hspace H}.
Proof. by apply/hspaceP=>x; rewrite hsE/= /cplmt!hsE/= subrr. Qed.

Lemma hsCK U : ((U^⟂)%HS^⟂)%HS = U.
Proof. by apply/hspaceP=>v; rewrite hsE/= hsE/= cplmtK. Qed.

Lemma hsC_inj : injective (@hscmplt H).
Proof. exact: (can_inj hsCK). Qed.

Lemma hsC_eq U V : (U^⟂)%HS == (V^⟂)%HS = (U == V).
Proof. by rewrite (can_eq hsCK). Qed.

Lemma hsC_eq_sym U V : (U^⟂)%HS == V = (U == (V^⟂)%HS).
Proof. by rewrite -hsC_eq hsCK. Qed.

Lemma lehC U V : (U^⟂)%HS `<=` (V^⟂)%HS = (V `<=` U).
Proof. by apply/eqb_iff; split=>/lehCP; rewrite ?hsCK=>/lehP. Qed.

Lemma lehC_sym U V : (U^⟂)%HS `<=` V = ((V^⟂)%HS `<=` U).
Proof. by rewrite -lehC hsCK. Qed.

Lemma lehC_symV U V : U `<=` (V^⟂)%HS = (V `<=` (U^⟂)%HS).
Proof. by rewrite -lehC hsCK. Qed.

Lemma hs_ortho U x y : x \in U -> y \in (U^⟂)%HS -> [< x ; y >] = 0.
Proof. by move=>/memhP<-/memhP<-; rewrite -hermf_dotE/= memh_projC dot0p. Qed.   

Lemma memhN U v : (- v \in U) = (v \in U). 
Proof. by rewrite !memhE linearN/= eqr_opp. Qed.
Lemma memhD U : {in U &, forall u v, u + v \in U}.
Proof. by move=>u v; rewrite !memhE linearD/==>/eqP->/eqP->. Qed.
Lemma memhB U : {in U &, forall u v, u - v \in U}.
Proof. by move=>u v Pu Pv; rewrite memhD// memhN. Qed.
Lemma memhZ U (c : C) : {in U, forall v, c *: v \in U}.
Proof. by move=>v; rewrite !memhE linearZ/==>/eqP->. Qed.

End HspacePredTheory.
End HspacePredTheory.

(* definition of supph cosupph cuph caph *)
(* note that: hilbert space is not a distrLatticeType !! *)
(* canonical to latticeType bLatticeType tbLatticeType *)
(* complLatticeType oComplLatticeType oModularLatticeType *)

Module Import HspaceSupport.

Section HspaceSupport.
Variable (H : chsType).
Implicit Type (U V W : {hspace H}).

Lemma supph_rank (G : chsType) (A : 'Hom(H,G)) : 
  \Dim (supph A) = \Rank A.
Proof. by rewrite /dimh hsE/= supplf_rank. Qed.

Lemma cosupph_rank (G : chsType) (A : 'Hom(H,G)) : 
  \Dim (cosupph A) = \Rank A.
Proof. by rewrite /dimh hsE/= cosupplf_rank. Qed.

Lemma supphP (G : chsType) (A : 'Hom(H,G)) x :
  (supph A x == 0) = (A x == 0).
Proof.
apply/eqb_iff; rewrite !eq_iff hsE/=; split.
by rewrite -{2}(suppvlf A) comp_lfunE=>->; rewrite linear0.
by rewrite lfunE/==>->; rewrite linear0.
Qed.

Lemma cosupphP (G K : chsType) (A : 'Hom(H,G)) (B : 'Hom(G,K)) :
  (B \o cosupph A == 0) = (B \o A == 0).
Proof. 
apply/eqb_iff; rewrite !eq_iff hsE/=; split;
[rewrite -{2}(cosupplfv A) | rewrite /cosupplf];
by rewrite comp_lfunA=>->; rewrite comp_lfun0l.
Qed.

Lemma memh_suppCE (G : chsType) (A : 'Hom(H,G)) x : 
  x \in ((supph A)^⟂)%HS = (A x == 0).
Proof. by rewrite memhCE hsCK supphP. Qed.

Lemma supph_projK (E : 'FP(H)) : supph E = HSType E.
Proof. by apply/hsC_inj/eqhP=>x; rewrite memh_suppCE memhCE hsCK hsE. Qed.

Lemma supph_Pid (E : 'FP(H)) : (supph E)%:VF = E.
Proof. by apply/lfunP=>v; move: (supph_projK E)=>/hspaceP/(_ v); rewrite hsE. Qed.

Lemma supph_id U : supph U = U.
Proof. by apply/hsC_inj/eqhP=>x; rewrite memh_suppCE memhCE hsCK. Qed.

Lemma supplfK (A : 'FP(H)) : supplf A = A.
Proof.
move: (supph_projK A); move=>/hspaceP=>P.
by apply/lfunP=>i; move: (P i); rewrite !hsE/=.
Qed.

Lemma projlfD_eq0 (A B : 'FP(H)) x: 
  (A%:VF + B) x == 0 = ((A x == 0) && (B x == 0)).
Proof.
apply/eqb_iff; split=>[/eqP/(f_equal (dotp x))|].
rewrite linear0 lfunE/= dotpDr !projf_dot=>/eqP;
rewrite addr_ss_eq0 ?sqrf_eq0 ?normr_eq0=>[|/andP[]//].
by apply/orP; left; apply/andP; split; rewrite exprn_ge0.
by rewrite lfunE/==>/andP[/eqP->/eqP->]; rewrite addr0 eqxx.
Qed.

Lemma eq_from_hs (G : chsType) U (f g : 'Hom(H,G)) :
  (forall x, x \in U -> f x = g x) -> (forall x, x \in U^⟂ -> f x = g x)
  -> f = g.
Proof.
move=>P1 P2; apply/lfunP=>v; rewrite (hs_vec_dec U v) !linearD/=.
by move: (memh_proj U v) (memh_proj U^⟂ v)=>/P1->/P2->.
Qed.


Lemma leh2v (U V : {hspace H}) : U `<=` V = (hs2vs U <= hs2vs V)%VS.
Proof.
apply/eqb_iff; split. move=>/lehP P; apply/subvP=>i; rewrite -!memh2v; apply P.
by move/subvP=>P; apply/lehP=>i; move: (P i); rewrite -!memh2v.
Qed.
Lemma subv2h (U V : {vspace H}) : (U <= V)%VS = (vs2hs U `<=` vs2hs V).
Proof. by rewrite leh2v !vs2hsK. Qed.

(* relation to vspace *)
Lemma vs2hs0 : 0%VS = hs2vs (hs0 : {hspace H}).
Proof. by apply/vspaceP=>x; rewrite [RHS]memv2h hs2vsK memv0 memh0. Qed.
Lemma hs2vs0 : (hs0 : {hspace H}) = vs2hs 0%VS.
Proof. by apply/hs2vs_inj; rewrite vs2hsK vs2hs0. Qed.
Lemma vs2hs1 : fullv = hs2vs (hs1 : {hspace H}).
Proof. by apply/vspaceP=>x; rewrite [RHS]memv2h hs2vsK memh1 memvf. Qed.
Lemma hs2vs1 : (hs1 : {hspace H}) = vs2hs fullv.
Proof. by apply/hs2vs_inj; rewrite vs2hsK vs2hs1. Qed.

Lemma cuphP U V W : (cuph U V `<=` W) = (U `<=` W) && (V `<=` W).
Proof.
apply/eqb_iff; split.
- by move=>P1; apply/andP; split; apply: (le_trans _ P1);
  apply/lehCP=>x; rewrite/= memh_suppCE memhCE hsCK projlfD_eq0=>/andP[].
move=>/andP[]/lehCP P1/lehCP P2; apply/lehCP=>x Px; rewrite /cuph memh_suppCE.
by move: (P1 _ Px) (P2 _ Px); rewrite !memhCE !hsCK lfunE/==>/eqP->/eqP->; rewrite addr0.
Qed.

Lemma caphP U V W : (U `<=` caph V W) = (U `<=` V) && (U `<=` W).
Proof. by rewrite /caph lehC_symV cuphP !lehC. Qed.

Lemma cuph2v (U V : {hspace H}) : (cuph U V) = vs2hs (hs2vs U + hs2vs V)%VS.
Proof.
apply/hs2vs_inj/eqP; rewrite eqEsubv vs2hsK; apply/andP; split.
by rewrite subv2h hs2vsK cuphP !leh2v vs2hsK -subv_add.
by rewrite subv_add !subv2h !hs2vsK -cuphP.
Qed.

Lemma addv2h (U V : {vspace H}) : (U + V)%VS = hs2vs (cuph (vs2hs U) (vs2hs V)).
Proof. by rewrite cuph2v !vs2hsK. Qed.

Lemma caph2v (U V : {hspace H}) : (caph U V) = vs2hs (hs2vs U :&: hs2vs V)%VS.
Proof.
apply/hs2vs_inj/eqP; rewrite eqEsubv vs2hsK; apply/andP; split.
by rewrite subv_cap -!leh2v -caphP.
by rewrite subv2h hs2vsK caphP !leh2v vs2hsK -subv_cap.
Qed.

Lemma capv2h (U V : {vspace H}) : (U :&: V)%VS = hs2vs (caph (vs2hs U) (vs2hs V)).
Proof. by rewrite caph2v !vs2hsK. Qed.

End HspaceSupport.
End HspaceSupport.

Module Import HspaceOrthoModularLattice.

Section Lehs_Alternative.
Variable (H : chsType).
Implicit Type (U V W : {hspace H}).

Lemma leh_compr U V : U `<=` V = (V \o U == U).
Proof.
apply/eqb_iff; rewrite eq_iff; split.
- move=>/lehP P; apply: (@eq_from_hs _ _ U)=>x Px; rewrite lfunE/=.
  move: {+}Px; rewrite memhE=>/eqP->. 
  by move/P: Px; rewrite memhE=>/eqP->.
  by move: Px; rewrite memhCE hsCK=>/eqP->; rewrite linear0.
move=>P; apply/lehP=>x; rewrite !memhE=>/eqP<-.
by rewrite -comp_lfunE P.
Qed.
Lemma leh_compl U V : U `<=` V = (U \o V == U).
Proof. by rewrite leh_compr -[LHS](can_eq (@adjfK _ _)) adjf_comp !hermf_adjE/=. Qed.

Lemma aux14 U V : U `<=` V -> (V%:VF - U%:VF \is projlf).
Proof.
move=>P; apply/projlfP; split; first by rewrite hermf_adjE.
rewrite linearBl/= !linearBr/=.
move: P {+}P; rewrite {1}leh_compr leh_compl=>/eqP->/eqP->; 
by rewrite !projf_idem subrr subr0.
Qed.

Lemma aux45 U V : (V%:VF - U%:VF \is projlf) -> (forall x, [< x ; (V%:VF - U%:VF) x >] >= 0).
Proof.
move=>P x; move: (ge0_dotp ((Projlfun P) x)).
by rewrite -adj_dotEV hermf_adjE/= -comp_lfunE projf_idem projfE.
Qed.

Lemma aux56 U V : (forall x, [< x ; (V%:VF - U%:VF) x >] >= 0) -> (forall x, `|V x| >= `|U x|).
Proof.
by move=>+x; move=>/(_ x); rewrite lfunE/= lfunE/= linearBr/= 
  !projf_dot subr_ge0 ler_pexpn2r ?nnegrE// .
Qed.

Lemma aux61 U V : (forall x, `|V x| >= `|U x|) -> U `<=` V.
Proof. 
rewrite -lehC=>P; apply/lehP=>x.
rewrite !memhCE !hsCK -normr_eq0=>/eqP P1.
by move: (P x); rewrite P1 normr_le0.
Qed.

Lemma leh_sub_proj U V : U `<=` V <-> (V%:VF - U%:VF \is projlf).
Proof. by split=>[/aux14|/aux45/aux56/aux61]. Qed.

Lemma leh_sub_dot U V : U `<=` V <-> (forall x, [< x ; (V%:VF - U%:VF) x >] >= 0).
Proof. by split=>[/aux14/aux45|/aux56/aux61]. Qed.

Lemma leh_norm U V : U `<=` V <-> (forall x, `|V x| >= `|U x|).
Proof. by split=>[/aux14/aux45/aux56|/aux61]. Qed.

Lemma supph_sub U V : U `<=` V -> 
  (supph (V%:VF - U%:VF))%:VF = V%:VF - U%:VF.
Proof. by move=>/aux14 P; rewrite -{1}(projfE tt P) supph_projK hsE projfE. Qed.

End Lehs_Alternative.

Section HspaceOrthoModularLattice.
Variable (H : chsType).
Implicit Type (U V W : {hspace H}).

(* form branch haven't include meetJoinLeMixin; so do it directly *)
Lemma cuphC : commutative (@cuph H).
Proof. by move=>U V; rewrite /cuph addrC. Qed.
Lemma caphC : commutative (@caph H).
Proof. by move=>U V; rewrite /caph cuphC. Qed.
Lemma cuphA : associative (@cuph H).
Proof. by move=>U V W; rewrite !cuph2v !vs2hsK addvA. Qed.
Lemma caphA : associative (@caph H).
Proof. by move=>U V W; rewrite !caph2v !vs2hsK capvA. Qed.
Lemma cuphKI V U : caph U (cuph U V) = U.
Proof.
apply/hs2vs_inj/eqP; rewrite caph2v cuph2v !vs2hsK eqEsubv; apply/andP;
  split; first by exact: capvSl.
rewrite subv_cap; apply/andP; split=>//; exact: addvSl.
Qed.
Lemma caphKU V U : cuph U (caph U V) = U.
Proof.
apply/hs2vs_inj/eqP; rewrite caph2v cuph2v !vs2hsK eqEsubv; apply/andP; 
  split; last by exact: addvSl.
rewrite subv_add; apply/andP; split=>//; exact: capvSl.
Qed.
Lemma lehEmeet U V : (U `<=` V) = (caph U V == U).
Proof.
rewrite leh2v -(can_eq (@hs2vsK _)) caph2v vs2hsK.
by apply/eqb_iff; rewrite eq_iff; split=>/capv_idPl.
Qed.

Definition hspace_latticeMixin :=
  LatticeMixin caphC cuphC caphA cuphA cuphKI caphKU lehEmeet.
Canonical hspace_latticeType := LatticeType {hspace H} hspace_latticeMixin.
Definition hspace_bottomMixin := BottomMixin (@le0h H).
Canonical hspace_bLatticeType := BLatticeType {hspace H} hspace_bottomMixin.
Definition hspace_topMixin := TopMixin  (@leh1 H).
Canonical hspace_tbLatticeType := TBLatticeType {hspace H} hspace_topMixin.

Lemma cupCh U : cuph (U^⟂)%HS U = hs1.
Proof.
apply/eqhP=>x; rewrite !memhCE !hsE/=/cplmt.
by rewrite !hsE/= /cplmt addrNK supplfK/= !subrr.
Qed.

Lemma capCh U : caph (U^⟂)%HS U = hs0.
Proof. by apply/hsC_inj; rewrite hsC0 /caph !hsCK cuphC cupCh. Qed.

Lemma wlehC : {homo (@hscmplt H) : U V /~ U `<=` V}.
Proof. by move=>U V; rewrite lehC. Qed.

Definition hspace_complLatticeMixin := ComplLatticeMixin cupCh capCh.
Canonical hspace_complLatticeType := ComplLatticeType {hspace H} hspace_complLatticeMixin.
Definition hspace_oComplLatticeMixin := OComplLatticeMixin (@hsCK H) wlehC.
Canonical hspace_oComplLatticeType := OComplLatticeType {hspace H} hspace_oComplLatticeMixin.

Lemma hs_orthomodular U V : 
  U `<=` V -> cuph U (caph (U^⟂)%HS V) = V.
Proof.
rewrite cuphC caphC -{3}[V]meetx1 -(joinCx U).
rewrite leh2v=>/(vspace_modr (hs2vs U^⟂))/(f_equal (@vs2hs _)).
by rewrite !addv2h !capv2h !hs2vsK.
Qed.

Definition hspace_oModularLatticeMixin := OModularLatticeMixin hs_orthomodular.
Canonical hspace_oModularLatticeType := OModularLatticeType {hspace H} hspace_oModularLatticeMixin.

End HspaceOrthoModularLattice.
End HspaceOrthoModularLattice.

Module Exports.

Export BasicConstruct.
Export HspaceSupport.
Canonical hspace_latticeType.
Canonical hspace_bLatticeType.
Canonical hspace_tbLatticeType.
Canonical hspace_complLatticeType.
Canonical hspace_oComplLatticeType.
Canonical hspace_oModularLatticeType.

(* reformulate the theories in HspacePredTheory and HspaceOrthoModularLattice *)
(* replacing the plain operator to lattice operator *)
Section Theory.
Variable (H : chsType).
Implicit Type (U V W: {hspace H}) (x y : H).

Definition hs_sub_t := hs_sub_t.
Definition hs_sub_proj := hs_sub_proj. 
Definition leh_lef := leh_lef.
Definition memhE := memhE.
Definition memhP := memhP.
Definition memh_dotE := memh_dotE.
Definition memh_dotP := memh_dotP.
Definition memh_proj := memh_proj.
Definition memh_normE := memh_normE.
Definition memh_normP := memh_normP.
Definition lehP := lehP.
Definition eqhP := eqhP.
Definition mem0h := mem0h.
Definition memhN := memhN.
Definition memhD := memhD.
Definition memhB := memhB.
Definition memhZ := memhZ.
Definition leh_compr := leh_compr. 
Definition leh_compl := leh_compl. 
Definition leh_sub_proj := leh_sub_proj. 
Definition leh_sub_dot := leh_sub_dot. 
Definition leh_norm := leh_norm. 
Definition supph_sub := supph_sub. 

Lemma hs_vec_dec U x : x = U x + (~` U) x.
Proof. exact: hs_vec_dec. Qed.
Lemma memhCE U x : x \in U = ((~` U) x == 0).
Proof. exact: memhCE. Qed.
Lemma memhCP U x : reflect ((~` U) x = 0) (x \in U).
Proof. exact: memhCP. Qed.
Lemma memh_dotCE U x : x \in U = ([< x ; (~` U) x >] == 0).
Proof. exact: memh_dotCE. Qed.
Lemma memh_dotCP U x : reflect ([< x ; (~` U) x >] = 0) (x \in U).
Proof. exact: memh_dotCP. Qed.
Lemma memh_projC U x : (~` U) (U x) = 0.
Proof. exact: memh_projC. Qed.
Lemma memh_normCE U x : x \in U = (`|(~` U) x| == 0).
Proof. exact: memh_normCE. Qed.
Lemma memh_normCP U x : reflect (`|(~` U) x| = 0) (x \in U).
Proof. Set Printing All.  exact: memh_normCP. Qed.
Lemma lehCP U V : reflect (forall x, (x \in (~` V)) -> (x \in (~` U))) (U `<=` V).
Proof. exact: lehCP. Qed.
Lemma memh1 x : x \in (`1` : {hspace H}).
Proof. exact: memh1. Qed.
Lemma memh0 x : x \in (`0` : {hspace H}) = (x == 0).
Proof. exact: memh0. Qed.

(* here we rewrite the theory from lattice and others *)
Local Notation cap := (@Order.meet _ (hspace_latticeType H)) (only parsing).
Local Notation cup := (@Order.join _ (hspace_latticeType H)) (only parsing).
Local Notation cpl := (@compl _ (hspace_complLatticeType H)) (only parsing).
Lemma lehh U : U `<=` U. Proof. exact: lexx. Qed.
(* ??? why lexx not work for // *)
(* Hint Extern 0 (_ `<=` _) => solve [apply: lehh] : core. *)
(* Hint Resolve lehh : core. *)
Lemma cuphC : commutative cup. Proof. exact: joinC. Qed.
Lemma caphC : commutative cap. Proof. exact: meetC. Qed.
Lemma cuphA : associative cup. Proof. exact: joinA. Qed.
Lemma caphA : associative cap. Proof. exact: meetA. Qed.
Lemma cuphKI V U : U `&` (U `|` V) = U.  Proof. exact: joinKI. Qed.
Lemma caphKU V U : U `|` (U `&` V) = U.  Proof. exact: meetKU. Qed.
Lemma cuphKIC V U : U `&` (V `|` U) = U. Proof. exact: joinKIC. Qed.
Lemma caphKUC V U : U `|` (V `&` U) = U. Proof. exact: meetKUC. Qed.
Lemma caphUK U V : (U `&` V) `|` V = V.  Proof. exact: meetUK. Qed.
Lemma cuphIK U V : (U `|` V) `&` V = V.  Proof. exact: joinIK. Qed.
Lemma caphUKC U V : (V `&` U) `|` V = V. Proof. exact: meetUKC. Qed.
Lemma cuphIKC U V : (V `|` U) `&` V = V. Proof. exact: joinIKC. Qed.
Lemma lehEcap U V : (U `<=` V) = (U `&` V == U). Proof. exact: leEmeet. Qed.
Lemma lehEcup U V : (U `<=` V) = (U `|` V == V). Proof. exact: leEjoin. Qed.

Lemma caphAC : right_commutative cap. Proof. exact: meetAC. Qed.
Lemma caphCA : left_commutative cap.  Proof. exact: meetCA. Qed.
Lemma caphACA : interchange cap cap.  Proof. exact: meetACA. Qed.
Lemma caphh U : U `&` U = U. Proof. exact: meetxx. Qed.
Lemma caphKI V U : U `&` (U `&` V) = U `&` V.  Proof. exact: meetKI. Qed.
Lemma caphIK V U : (U `&` V) `&` V = U `&` V.  Proof. exact: meetIK. Qed.
Lemma caphKIC V U : U `&` (V `&` U) = U `&` V. Proof. exact: meetKIC. Qed.
Lemma caphIKC V U : V `&` U `&` V = U `&` V.   Proof. exact: meetIKC. Qed.
Lemma lehI U V W : (U `<=` V `&` W) = (U `<=` V) && (U `<=` W).
Proof. exact: lexI. Qed.
Lemma lehIxl U V W : V `<=` U -> V `&` W `<=` U. Proof. exact: leIxl. Qed.
Lemma lehIxr U V W : W `<=` U -> V `&` W `<=` U. Proof. exact: leIxr. Qed.
Lemma lehIx2 U V W : (V `<=` U) || (W `<=` U) -> V `&` W `<=` U.
Proof. exact: leIx2. Qed.
Lemma lehIr U V : V `&` U `<=` U. Proof. exact: leIr. Qed.
Lemma lehIl U V : U `&` V `<=` U. Proof. exact: leIl. Qed.
Lemma caph_idPl {U V} : reflect (U `&` V = U) (U `<=` V).
Proof. exact: meet_idPl. Qed.
Lemma caph_idPr {U V} : reflect (V `&` U = U) (U `<=` V).
Proof. exact: meet_idPr. Qed.
Lemma caphl U V : U `<=` V -> U `&` V = U. Proof. exact: meet_l. Qed.
Lemma caphr U V : V `<=` U -> U `&` V = V. Proof. exact: meet_r. Qed.
Lemma lehIidl U V : (U `<=` U `&` V) = (U `<=` V). Proof. exact: leIidl. Qed.
Lemma lehIidr U V : (U `<=` V `&` U) = (U `<=` V). Proof. exact: leIidr. Qed.
Lemma eq_caphl U V : (U `&` V == U) = (U `<=` V). Proof. exact: eq_meetl. Qed.
Lemma eq_caphr U V : (U `&` V == V) = (V `<=` U). Proof. exact: eq_meetr. Qed.
Lemma lehI2 U V W t : U `<=` W -> V `<=` t -> U `&` V `<=` W `&` t.
Proof. exact: leI2. Qed.
Lemma lehI2l U V W : V `<=` W -> U `&` V `<=` U `&` W.
Proof. move=>P1; apply/lehI2=>[|//]; exact: lexx. Qed.
Lemma lehI2r U V W : V `<=` W -> V `&` U `<=` W `&` U.
Proof. rewrite !(caphC _ U); exact: lehI2l. Qed.

Lemma cuphAC : right_commutative cup. Proof. exact: joinAC. Qed.
Lemma cuphCA : left_commutative cup.  Proof. exact: joinCA. Qed.
Lemma cuphACA : interchange cup cup.  Proof. exact: joinACA. Qed.
Lemma cuphh U : U `|` U = U. Proof. exact: joinxx. Qed.
Lemma cuphKU V U : U `|` (U `|` V) = U `|` V.  Proof. exact: joinKU. Qed.
Lemma cuphUK V U : (U `|` V) `|` V = U `|` V.  Proof. exact: joinUK. Qed.
Lemma cuphKUC V U : U `|` (V `|` U) = U `|` V. Proof. exact: joinKUC. Qed.
Lemma cuphUKC V U : V `|` U `|` V = U `|` V.   Proof. exact: joinUKC. Qed.
Lemma leUh U V W : (U `|` V `<=` W) = (U `<=` W) && (V `<=` W).
Proof. exact: leUx. Qed.
Lemma lehxUl U V W : U `<=` V -> U `<=` V `|` W. Proof. exact: lexUl. Qed.
Lemma lehxUr U V W : U `<=` W -> U `<=` V `|` W. Proof. exact: lexUr. Qed.
Lemma lehxU2 U V W : (U `<=` V) || (U `<=` W) -> U `<=` V `|` W.
Proof. exact: lexU2. Qed.
Lemma lehUr U V : U `<=` V `|` U. Proof. exact: leUr. Qed.
Lemma lehUl U V : U `<=` U `|` V. Proof. exact: leUl. Qed.
Lemma cuph_idPr {U V} : reflect (U `|` V = V) (U `<=` V).
Proof. exact: join_idPr. Qed.
Lemma cuph_idPl {U V} : reflect (V `|` U = V) (U `<=` V).
Proof. exact: join_idPl. Qed.
Lemma cuphl U V : V `<=` U -> U `|` V = U. Proof. exact: join_l. Qed.
Lemma cuphr U V : U `<=` V -> U `|` V = V. Proof. exact: join_r. Qed.
Lemma lehUidl U V : (U `|` V `<=` V) = (U `<=` V). Proof. exact: leUidl. Qed.
Lemma lehUidr U V : (V `|` U `<=` V) = (U `<=` V). Proof. exact: leUidr. Qed.
Lemma eq_cuphl U V : (U `|` V == U) = (V `<=` U). Proof. exact: eq_joinl. Qed.
Lemma eq_cuphr U V : (U `|` V == V) = (U `<=` V). Proof. exact: eq_joinr. Qed.
Lemma lehU2 U V W t : U `<=` W -> V `<=` t -> U `|` V `<=` W `|` t.
Proof. exact: leU2. Qed.
Lemma lehU2l U V W : V `<=` W -> U `|` V `<=` U `|` W.
Proof. move=>P1; apply/lehU2=>[|//]; exact: lexx. Qed.
Lemma lehU2r U V W : V `<=` W -> V `|` U `<=` W `|` U.
Proof. rewrite !(cuphC _ U); exact: lehU2l. Qed.

(* Non-distributive lattice theory with `0` & 1*)
Lemma le0h U : `0` `<=` U. Proof. exact: le0x. Qed.
Hint Resolve le0x : core.
Lemma leh0 U : (U `<=` `0`) = (U == `0`). Proof. exact: lex0. Qed.
Lemma lth0 U : (U `<` `0`) = false. Proof. exact: ltx0. Qed.
Lemma lt0h U : (`0` `<` U) = (U != `0`). Proof. exact: lt0x. Qed.
Lemma cap0h : left_zero  `0` cap.  Proof. exact: meet0x. Qed.
Lemma caph0 : right_zero `0` cap.  Proof. exact: meetx0. Qed.
Lemma cup0h : left_id    `0` cup.  Proof. exact: join0x. Qed.
Lemma cuph0 : right_id   `0` cup.  Proof. exact: joinx0. Qed.
Lemma cuph_eq0 U V : (U `|` V == `0`) = (U == `0`) && (V == `0`).
Proof. exact: join_eq0. Qed.

Canonical cuph_monoid := Monoid.Law cuphA cup0h cuph0.
Canonical cuph_comoid := Monoid.ComLaw cuphC.

Lemma leh1 U : U `<=` `1`. Proof. exact: lex1. Qed.
Hint Resolve leh1 : core.
Lemma caph1 : right_id   `1` cap. Proof. exact: meetx1. Qed.
Lemma cap1h : left_id    `1` cap. Proof. exact: meet1x. Qed.
Lemma cuph1 : right_zero `1` cup. Proof. exact: joinx1. Qed.
Lemma cup1h : left_zero  `1` cup. Proof. exact: join1x. Qed.
Lemma le1h U : (`1` `<=` U) = (U == `1`). Proof. exact: le1x. Qed.
Lemma caph_eq1 U V : (U `&` V == `1`) = (U == `1`) && (V == `1`).
Proof. exact: meet_eq1. Qed.

Canonical caph_monoid := Monoid.Law caphA cap1h caph1.
Canonical caph_comoid := Monoid.ComLaw caphC.
Canonical caph_muloid := Monoid.MulLaw cap0h caph0.
Canonical cuph_muloid := Monoid.MulLaw cup1h cuph1.

Section CuphsCaphs.
Implicit Types (I : finType) (T : eqType).

Lemma cuphs_sup_seq T (r : seq T) (P : {pred T}) (F : T -> {hspace H}) (x : T) :
  x \in r -> P x -> F x `<=` \cup_(i <- r | P i) F i.
Proof. exact: joins_sup_seq. Qed.

Lemma cuphs_min_seq T (r : seq T) (P : {pred T}) (F : T -> {hspace H}) (x : T) U :
  x \in r -> P x -> U `<=` F x -> U `<=` \cup_(i <- r | P i) F i.
Proof. exact: joins_min_seq. Qed.

Lemma cuphs_sup I (j : I) (P : {pred I}) (F : I -> {hspace H}) :
  P j -> F j `<=` \cup_(i | P i) F i.
Proof. exact: joins_sup. Qed.

Lemma cuphs_min I (j : I) U (P : {pred I}) (F : I -> {hspace H}) :
  P j -> U `<=` F j -> U `<=` \cup_(i | P i) F i.
Proof. exact: joins_min. Qed.

Lemma cuphs_le J (r : seq J) (P : {pred J}) (F : J -> {hspace H}) U :
  (forall x : J, P x -> F x `<=` U) -> \cup_(i <- r | P i) F i `<=` U.
Proof. by move=> leFm; elim/big_rec: _=>[//|] i x Px xu; rewrite leUx leFm. Qed.

Lemma cuphsP_seq T (r : seq T) (P : {pred T}) (F : T -> {hspace H}) U :
  reflect (forall x : T, x \in r -> P x -> F x `<=` U)
          (\cup_(i <- r | P i) F i `<=` U).
Proof. exact: joinsP_seq. Qed.

Lemma cuphsP I U (P : {pred I}) (F : I -> {hspace H}) :
  reflect (forall i : I, P i -> F i `<=` U) (\cup_(i | P i) F i `<=` U).
Proof. exact: joinsP. Qed.

Lemma le_cuphs I (A B : {set I}) (F : I -> {hspace H}) :
  A \subset B -> \cup_(i in A) F i `<=` \cup_(i in B) F i.
Proof. exact: le_joins. Qed.

Lemma cuphs_setU I (A B : {set I}) (F : I -> {hspace H}) :
  \cup_(i in (A :|: B)) F i = \cup_(i in A) F i `|` \cup_(i in B) F i.
Proof. exact: joins_setU. Qed.

Lemma cuphs_seq I (r : seq I) (F : I -> {hspace H}) :
  \cup_(i <- r) F i = \cup_(i in r) F i.
Proof. exact: joins_seq. Qed.

Lemma caphs_inf I (j : I) (P : {pred I}) (F : I -> {hspace H}) :
   P j -> \cap_(i | P i) F i `<=` F j.
Proof. exact: meets_inf. Qed.

Lemma caphs_max I (j : I) U (P : {pred I}) (F : I -> {hspace H}) :
   P j -> F j `<=` U -> \cap_(i | P i) F i `<=` U.
Proof. exact: meets_max. Qed.

Lemma caphsP I U (P : {pred I}) (F : I -> {hspace H}) :
   reflect (forall i : I, P i -> U `<=` F i) (U `<=` \cap_(i | P i) F i).
Proof. exact: meetsP. Qed.

Lemma caphs_inf_seq T (r : seq T) (P : {pred T}) (F : T -> {hspace H}) (x : T) :
  x \in r -> P x -> \cap_(i <- r | P i) F i `<=` F x.
Proof. exact: meets_inf_seq. Qed.

Lemma caphs_max_seq T (r : seq T) (P : {pred T}) (F : T -> {hspace H}) (x : T) U :
  x \in r -> P x -> F x `<=` U -> \cap_(i <- r | P i) F i `<=` U.
Proof. exact: meets_max_seq. Qed.

Lemma caphsP_seq T (r : seq T) (P : {pred T}) (F : T -> {hspace H}) U :
  reflect (forall x : T, x \in r -> P x -> U `<=` F x)
          (U `<=` \cap_(x <- r | P x) F x).
Proof. exact: meetsP_seq. Qed.

Lemma le_meets I (A B : {set I}) (F : I -> {hspace H}) :
   A \subset B -> \cap_(i in B) F i `<=` \cap_(i in A) F i.
Proof. exact: le_meets. Qed.

Lemma caphs_setU I (A B : {set I}) (F : I -> {hspace H}) :
   \cap_(i in (A :|: B)) F i = \cap_(i in A) F i `&` \cap_(i in B) F i.
Proof. exact: meets_setU. Qed.

Lemma caphs_seq I (r : seq I) (F : I -> {hspace H}) :
   \cap_(i <- r) F i = \cap_(i in r) F i.
Proof. exact: meets_seq. Qed.

End CuphsCaphs.

Lemma leh_cupl U : {homo (cup U) : x y / x `<=` y}.   Proof. exact: le_joinl. Qed.
Lemma leh_cupr U : {homo (cup^~ U) : x y / x `<=` y}. Proof. exact: le_joinr. Qed.
Lemma leh_capl U : {homo (cap U) : x y / x `<=` y}.   Proof. exact: le_meetl. Qed.
Lemma leh_capr U : {homo (cap^~ U) : x y / x `<=` y}. Proof. exact: le_meetr. Qed.
Lemma lth_cupl U : {homo (cup U) : x y / x `<` y >-> x `<=` y}.
Proof. exact: lt_joinl. Qed.
Lemma lth_cupr U : {homo (cup^~ U) : x y / x `<` y >-> x `<=` y}.
Proof. exact: lt_joinr. Qed.
Lemma lth_capl U : {homo (cap U) : x y / x `<` y >-> x `<=` y}.
Proof. exact: lt_meetl. Qed.
Lemma lth_capr U : {homo (cap^~ U) : x y / x `<` y >-> x `<=` y}.
Proof. exact: lt_meetr. Qed.
Lemma cuphCx U : ~` U `|` U = `1`. Proof. exact: joinCx. Qed.
Lemma caphCx U : ~` U `&` U = `0`. Proof. exact: meetCx. Qed.
Lemma cuphxC U : U `|` ~` U = `1`. Proof. exact: joinxC. Qed.
Lemma caphxC U : U `&` ~` U = `0`. Proof. exact: meetxC. Qed.
Lemma hsC1 : ~` `1` = `0` :> {hspace H}. Proof. exact: compl1. Qed.
Lemma hsC0 : ~` `0` = `1` :> {hspace H}. Proof. exact: compl0. Qed.
Lemma hsCK : involutive cpl.    Proof. exact: complK. Qed.
Lemma hsC_inj : injective cpl. Proof. exact: compl_inj. Qed.
Lemma hsC_eq U V : (~` U) == (~` V) = (U == V). Proof. exact: hsC_eq. Qed.
Lemma hsCx_eq U V : (~` U) == V = (U == (~` V)). Proof. exact: hsC_eq_sym. Qed.
Lemma hsxC_eq U V : U == (~` V) = ((~` U) == V). Proof. by rewrite hsCx_eq. Qed.
Lemma wlehC : {homo cpl : a b /~ a `<=` b}. Proof. exact: leCP. Qed.
Lemma lehC U V : (~` U) `<=` (~` V) = (V `<=` U).  Proof. exact: leC. Qed.
Lemma lehCx U V : (~` U) `<=` V = ((~` V) `<=` U). Proof. exact: leCx. Qed.
Lemma lehxC U V : U `<=` (~` V) = (V `<=` (~` U)). Proof. exact: lexC. Qed.
Lemma hsCU U V : ~` (U `|` V) = ~` U `&` ~` V. Proof. exact: complU. Qed.
Lemma hsCI U V : ~` (U `&` V) = ~` U `|` ~` V. Proof. exact: complI. Qed.
Lemma hsUI U V : (U `|` V) = ~` (~` U `&` ~` V). Proof. by rewrite -hsCU hsCK. Qed.
Lemma hsIU U V : (U `&` V) = ~` (~` U `|` ~` V). Proof. by rewrite -hsCI hsCK. Qed.
Lemma lehxC_disj U V : (U `<=` ~` V) -> (U `&` V = `0`). Proof. exact: lexC_disj. Qed.
Lemma hsUCI U V : U `<=` V -> U `|` ((~` U) `&` V) = V. Proof. exact: le_joinIC. Qed.
Lemma hs_ortho U x y : x \in U -> y \in (~` U) -> [< x ; y >] = 0.
Proof. exact: hs_ortho. Qed.
Lemma caphsC I (r : seq I) (P : pred I) (f : I -> {hspace H}) :
  ~` (\cap_(i <- r | P i) f i) = \cup_(i <- r | P i) ~` (f i).
Proof. by elim/big_rec2: _ =>/= [|i d vs _ eqd]; rewrite ?hsC1// -eqd hsCI. Qed.
Lemma cuphsC I (r : seq I) (P : pred I) (f : I -> {hspace H}) :
  ~` (\cup_(i <- r | P i) f i) = \cap_(i <- r | P i) ~` (f i).
Proof. by elim/big_rec2: _ =>/= [|i d vs _ eqd]; rewrite ?hsC0// -eqd hsCU. Qed.

(* basic construct -> lattice operator *)
Definition hs0E : hspace0 H = `0`.
Proof. by []. Qed.
Definition hs1E : hspace1 H = `1`.
Proof. by []. Qed.
Definition hsCE U : U^⟂ = ~` U.
Proof. by []. Qed.
Definition cuphE U V : cuph U V = U `|` V.
Proof. by []. Qed.
Definition caphE U V : caph U V = U `&` V.
Proof. by []. Qed.
Definition hs2lE := (hs0E, hs1E, hsCE, cuphE, caphE).

(* lattice operator -> lfun operator *)
Lemma hs2lf0E : (`0` : {hspace H})%:VF = 0.
Proof. by rewrite -hs0E hsE. Qed.
Lemma hs2lf1E : (`1` : {hspace H})%:VF = \1.
Proof. by rewrite -hs1E hsE. Qed.
Lemma hs2lfCE U : (~` U)%:VF = cplmt U.
Proof. by rewrite -hsCE hsE. Qed.
Lemma cuph2lfE U V : (U `|` V)%:VF = supplf (U%:VF + V%:VF).
Proof. by rewrite -cuphE hsE. Qed.
Lemma caph2lfE U V : (U `&` V)%:VF = cplmt (supplf (cplmt U%:VF + cplmt V%:VF)).
Proof. by rewrite -caphE /caph /cuph !hsE/=hsE. Qed.
Definition hs2lfE := (hs2lf0E, hs2lf1E, hs2lfCE, cuph2lfE, caph2lfE).

Lemma capCh_sub U V : U `<=` V -> 
  ((~` U) `&` V) = supph (V%:VF - U%:VF).
Proof.
move=>/supph_sub P; rewrite -[LHS]hsCK [X in ~` X]complI hsCK; apply/eqhP=>x.
by rewrite memhCE hsCK memhCE hs2lfE supphP P !hsE/= /cplmt opprB !addrA [_ + \1]addrC.
Qed.
Lemma cuph_lub U V W : U `<=` W -> V `<=` W -> U `|` V `<=` W.
Proof. by move=>P1 P2; rewrite leUx P1 P2. Qed.
Lemma caph_glb U V W : W `<=` U -> W `<=` V -> W `<=` U `&` V.
Proof. by move=>P1 P2; rewrite lexI P1 P2. Qed.

(* extra difinition *)
Definition hline (v : H) := supph [> v ; v <].
Definition spanh (F : finType) (v : F -> H) :=
  supph (\sum_i [> v i ; v i <]).
Definition diffh U V := U `&` (~` (U `&` V)).
Definition kerh (G : chsType) (A : 'Hom(H,G)) := ~` (supph A).
Definition cokerh (G : chsType) (A : 'Hom(H,G)) := ~` (cosupph A).

Lemma kerhE (G : chsType) (A : 'Hom(H,G)) : kerh A = ~` (supph A).
Proof. by []. Qed.
Lemma cokerhE (G : chsType) (A : 'Hom(H,G)) : cokerh A = ~` (cosupph A).
Proof. by []. Qed.
Lemma supphE (G : chsType) (A : 'Hom(H,G)) : supph A = ~` (kerh A).
Proof. by rewrite kerhE hsCK. Qed.
Lemma cosupphE (G : chsType) (A : 'Hom(H,G)) : cosupph A = ~` (cokerh A).
Proof. by rewrite cokerhE complK. Qed.

Lemma memh_suppCE (G : chsType) (A : 'Hom(H,G)) x : 
  x \in ~` (supph A) = (A x == 0).
Proof. exact: memh_suppCE. Qed.

Lemma eq_from_hs (G : chsType) U (f g : 'Hom(H,G)) :
  (forall x, x \in U -> f x = g x) -> (forall x, x \in ~` U -> f x = g x)
  -> f = g.
Proof. exact: eq_from_hs. Qed.

Lemma leh_memCP (U V : {hspace H}) : 
  reflect (forall x, V x == 0 -> U x == 0) (U `<=` V).
Proof.
apply/(iffP (lehCP _ _))=>+ x; move=>/(_ x);
by rewrite !memhCE !hsCK=>P1 P2; apply P1.
Qed.

Lemma leh_memP (U V : {hspace H}) : 
  reflect (forall x, U x == x -> V x == x) (U `<=` V).
Proof.
apply/(iffP (lehP _ _))=>+ x; move=>/(_ x);
by rewrite !memhE =>P1 P2; apply P1.
Qed.

Lemma outp_norm_proj (v : H) : `|v|^-2 *: [> v ; v <] \is projlf.
Proof.
apply/projlfP. rewrite adjfZ adj_outp geC0_conj ?invr_ge0// ?exprn_ge0//; split=>//.
case E: (v == 0). by move: E=>/eqP->; rewrite normr0 expr0n/= invr0 scale0r comp_lfun0l.
by rewrite linearZl/= linearZr/= outp_comp dotp_norm !scalerA -mulrA mulVf 
  ?mulr1// expf_eq0/= normr_eq0 E.
Qed.

Lemma hline_def (v : H) : (hline v) = HSType (ProjfType (outp_norm_proj v)).
Proof.
apply/hsC_inj/eqhP=>x; rewrite !memhCE !hsCK supphP !hsE/=.
rewrite lfunE/= outpE [RHS]scaler_eq0. apply/eqb_iff; split.
by move=>->; rewrite orbT. move/orP=>[|//].
by rewrite invr_eq0 expf_eq0/= normr_eq0=>/eqP->; rewrite scaler0.
Qed.

Lemma hlineP (u v : H) : reflect (exists k : C, u = k *: v) (u \in hline v).
Proof.
apply/(iffP idP); rewrite hline_def memhE hsE/= lfunE/= outpE scalerA.
by move=>/eqP P; exists (`|v| ^- 2 * [< v; u >]); rewrite P.
move=>[k Pk]; rewrite Pk dotpZr dotp_norm mulrC -mulrA.
case E: (v == 0). by move/eqP: E=>->; rewrite !scaler0.
by rewrite mulfV ?mulr1// expf_eq0/= normr_eq0 E.
Qed.

(* relation between hspace <-> vspace *)
Lemma vs2hs0 : 0%VS = hs2vs (`0` : {hspace H}).
Proof. exact : vs2hs0. Qed.
Lemma hs2vs0 : (`0` : {hspace H}) = vs2hs 0%VS.
Proof. exact : hs2vs0. Qed.
Lemma vs2hs1 : fullv = hs2vs (`1` : {hspace H}).
Proof. exact : vs2hs1. Qed.
Lemma hs2vs1 : (`1` : {hspace H}) = vs2hs fullv.
Proof. exact : hs2vs1. Qed.
Lemma cuph2v U V : (U `|` V) = vs2hs (hs2vs U + hs2vs V)%VS.
Proof. exact : cuph2v. Qed.
Lemma addv2h (U V : {vspace H}) : (U + V)%VS = hs2vs ((vs2hs U) `|` (vs2hs V)).
Proof. exact : addv2h. Qed.
Lemma caph2v U V : (U `&` V) = vs2hs (hs2vs U :&: hs2vs V)%VS.
Proof. exact : caph2v. Qed.
Lemma capv2h (U V : {vspace H}) : (U :&: V)%VS = hs2vs ((vs2hs U) `&` (vs2hs V)).
Proof. exact: capv2h. Qed.
Lemma caphs2v I (r : seq I) (P : pred I) (f : I -> {hspace H}) :
  \cap_(i <- r | P i) f i = vs2hs (\bigcap_(i <- r | P i) hs2vs (f i))%VS.
Proof.
elim: r=>[|r x]; first by rewrite !big_nil hs2vs1.
by rewrite !big_cons; case: (P r)=>//->; rewrite caph2v vs2hsK.
Qed.
Lemma cuphs2v I (r : seq I) (P : pred I) (f : I -> {hspace H}) :
  \cup_(i <- r | P i) f i = vs2hs (\sum_(i <- r | P i) hs2vs (f i))%VS.
Proof.
elim: r=>[|r x]; first by rewrite !big_nil hs2vs0.
by rewrite !big_cons; case: (P r)=>//->; rewrite cuph2v vs2hsK.
Qed.
Lemma bigcapv2h I (r : seq I) (P : pred I) (f : I -> {vspace H}) :
  (\bigcap_(i <- r | P i) (f i))%VS = hs2vs (\cap_(i <- r | P i) vs2hs (f i)).
Proof. by rewrite caphs2v vs2hsK; under [RHS]eq_bigr do rewrite vs2hsK. Qed.
Lemma sumv2h I (r : seq I) (P : pred I) (f : I -> {vspace H}) :
  (\sum_(i <- r | P i) (f i))%VS = hs2vs (\cup_(i <- r | P i) vs2hs (f i)).
Proof. by rewrite cuphs2v vs2hsK; under [RHS]eq_bigr do rewrite vs2hsK. Qed.
Lemma dimh2v U : \Dim U = \dim (hs2vs U).
Proof. by rewrite /dimh /dimv /lfrank /hs2vs mx2vsK. Qed.
Lemma dimv2h (U : {vspace H}) : \dim U = \Dim (vs2hs U).
Proof. by rewrite dimh2v vs2hsK. Qed. 
Lemma hs2vs_eq U V : (U == V) = (hs2vs U == hs2vs V)%VS.
Proof. by rewrite (can_eq (@hs2vsK _)). Qed.
Lemma vs2hs_eq (U V : {vspace H}) : (U == V)%VS = (vs2hs U == vs2hs V).
Proof. by rewrite (can_eq (@vs2hsK _)). Qed.
Lemma hline2v v : hline v = vs2hs (<[v]>)%VS.
Proof.
apply/eqhP=>x; rewrite -memv2h.
by apply/eqb_iff; split=>[/hlineP P|/vlineP P]; [apply/vlineP|apply/hlineP].
Qed.
Lemma vline2h v : (<[v]>)%VS = hs2vs (hline v).
Proof. by apply/vs2hs_inj; rewrite hs2vsK hline2v. Qed.

End Theory.
Arguments eq_from_hs {H G} U.

Ltac simph2v := do 1 ?[ apply/hs2vs_inj | ]; rewrite ?memh2v ?dimh2v ?hs2vs0 
  ?hs2vs1 ?cuph2v ?caph2v ?hline2v ?caphs2v ?cuphs2v ?leh2v ?hs2vs_eq ?vs2hsK.

Ltac simpv2h := do 1 ?[ apply/vs2hs_inj | ]; rewrite ?memv2h ?dimv2h ?vs2hs0 
  ?vs2hs1 ?addv2h ?capv2h ?vline2h ?bigcapv2h ?sumv2h ?subv2h ?vs2hs_eq ?hs2vsK.

Notation "{ : H }" := (`1` : {hspace H}) (only parsing) : hspace_scope.
Notation "<[ v ]>" := (hline v) : hspace_scope.
Notation "<< X >>" := (spanh X) : hspace_scope.
Notation "U `\` V" := (diffh U V) : hspace_scope.

End Exports.

End HspaceOrthoModularLattice.
Export HspaceOrthoModularLattice.Exports.

Section CoHspace.
Implicit Type (H G : chsType).

Lemma ponb_sum_eq0 G (F : finType) (f : 'PONB(F;G)) (l : F -> C) :
  \sum_i l i *: f i = 0 <-> forall i, l i = 0.
Proof. 
split=>[+ i|P]; last by rewrite big1// =>i _; rewrite P scale0r.
move/(f_equal (dotp (f i))).
rewrite dotp_sumr (bigD1 i)//= big1=>[j/negPf nj|];
by rewrite dotpZr ponb_dot 1?eq_sym ?nj?mulr0// eqxx mulr1 linear0 addr0.
Qed.

Lemma cosupph_memCE H G (A : 'Hom(H,G)) x : 
  x \in ~` (cosupph A) = (A^A x == 0).
Proof.
rewrite memhCE hsCK; move: (cosupphP A [>x; x<])=>/esym.
rewrite !outp_compl hermf_adjE/= !outp_eq0.
by case: eqP=>// ->; rewrite !linear0 !eqxx.
Qed.

Lemma cosupph_adj H G (A : 'Hom(H,G)) : 
  cosupph (A^A) = supph A.
Proof.
by apply/hsC_inj/eqhP=>x; rewrite cosupph_memCE memh_suppCE adjfK.
Qed.

Lemma supph_adj H G (A : 'Hom(H,G)) : 
  supph (A^A) = cosupph A.
Proof. by rewrite -cosupph_adj adjfK. Qed.

Lemma cosupplf_adj H G (A : 'Hom(H,G)) : 
  cosupplf A^A = supplf A.
Proof. by apply/lfunP=>x; move: (cosupph_adj A)=>/hspaceP/(_ x); rewrite !hsE/=. Qed.

Lemma supplf_adj H G (A : 'Hom(H,G)) : 
  supplf A^A = cosupplf A.
Proof. by rewrite -cosupplf_adj adjfK. Qed.

Lemma memh_suppP H G (A : 'Hom(H,G)) x : 
  reflect (exists y, x = A^A y) (x \in supph A).
Proof.
apply/(iffP idP)=>[|[y Py]].
rewrite memhE hsE/= -cosupplf_adj /cosupplf lfunE/==>/eqP P1.
exists ((pinvlf A^A)^A x); by rewrite P1.
by rewrite memhE Py -comp_lfunE hsE/= -cosupplf_adj cosupplfv.
Qed.

Lemma memh_cosuppP H G (A : 'Hom(H,G)) x : 
  reflect (exists y, x = A y) (x \in cosupph A).
Proof. by rewrite -supph_adj; apply/(iffP (memh_suppP _ _)); rewrite adjfK. Qed.

Lemma kerh_adj H G (A : 'Hom(H,G)) : 
  kerh A^A = cokerh A.
Proof. by rewrite /kerh supph_adj. Qed.

Lemma cokerh_adj H G (A : 'Hom(H,G)) :
  cokerh A^A = kerh A.
Proof. by rewrite -kerh_adj adjfK. Qed.

Lemma memh_kerE H G (A : 'Hom(H,G)) x : 
  x \in kerh A = (A x == 0).
Proof. exact: memh_suppCE. Qed.

Lemma memh_kerCP H G (A : 'Hom(H,G)) x : 
  reflect (exists y, x = A^A y) (x \in ~` kerh A).
Proof. rewrite /kerh hsCK; exact: memh_suppP. Qed.

Lemma memh_cokerCP H G (A : 'Hom(H,G)) x : 
  reflect (exists y, x = A y) (x \in ~` cokerh A).
Proof. rewrite /cokerh hsCK; exact: memh_cosuppP. Qed.

Lemma cosupph_id H (U : {hspace H}) : cosupph U = U.
Proof. by rewrite -supph_adj hermf_adjE/= supph_id. Qed.

Lemma kerhC H (U : {hspace H}) : kerh U = ~` U.
Proof. by rewrite /kerh supph_id. Qed.
Lemma kerhK H (U : {hspace H}) : kerh (kerh U) = U.
Proof. by rewrite !kerhC hsCK. Qed.
Lemma cokerhC H (U : {hspace H}) : cokerh U = ~` U. 
Proof. by rewrite /cokerh cosupph_id. Qed.
Lemma cokerhK H (U : {hspace H}) : cokerh (cokerh U) = U.
Proof. by rewrite !cokerhC hsCK. Qed.

End CoHspace.


(* ?? merge to lfrepresent.v ?? *)
Section CastFinFun.

Definition castfun (F G : finType) (eqc : #|F| = #|G|) (T : Type) (f : F -> T) :=
  (fun i : G => f (enum_val (cast_ord (esym eqc) (enum_rank i)))).
Lemma castfun_id (F : finType) erefl_c T (f : F -> T) :
  castfun erefl_c f = f.
Proof. by apply/funext=>i; rewrite/castfun cast_ord_id enum_rankK. Qed.
Lemma castfun_comp (F G K: finType) (eqf : #|F| = #|G|) (eqg : #|G| = #|K|) 
  T (f : F -> T) : 
  castfun eqg (castfun eqf f) = castfun (etrans eqf eqg) f.
Proof.
apply/funext=>i; rewrite /castfun enum_valK cast_ord_comp.
by rewrite (eq_irrelevance (etrans (esym eqg) (esym eqf)) (esym (etrans eqf eqg))).
Qed.
Lemma castfun_const (F G : finType) (eqc : #|F| = #|G|) (T : Type) (x : T) :
  castfun eqc (fun=>x) = (fun=>x).
Proof. by []. Qed.

Lemma castfun_ponb (H : chsType) (F G : finType) (eqc : #|F| = #|G|) (f : 'PONB(F;H)) :
  ponbasis (castfun eqc f).
Proof.
by move=>i j; rewrite /castfun ponb_dot enum_ord_eq enum_valK 
  cast_ord_comp cast_ord_id (can_eq enum_rankK).
Qed.
Canonical castfun_ponbasis H F G eqc f := PONBasis (@castfun_ponb H F G eqc f).

Lemma castfun_onb (H : chsType) (F G : finType) (eqc : #|F| = #|G|) (f : 'ONB(F;H)) :
  ponbasis (castfun eqc f).
Proof. exact: castfun_ponb. Qed.
Lemma castfun_card (H : chsType) (F G : finType) (eqc : #|F| = #|G|) (f : 'ONB(F;H)) :
  #|G| = Vector.dim H.
Proof. by rewrite -eqc (onb_card f). Qed.
Canonical castfun_onbasis H F G eqc f := ONBasis
   (@castfun_onb H F G eqc f) (@castfun_card H F G eqc f).

(* standard form of decomposition *)
Fact sumoutp_key : unit. Proof. by []. Qed.
Definition sumoutp (H G : chsType) (F : finType) (l : F -> C) 
  (f : F -> H) (g : F -> G) : 'Hom(H,G) := 
  locked_with sumoutp_key (\sum_i (l i) *: [> g i ; f i <]).
Canonical sumoutp_unlockable H G F l f g := [unlockable of @sumoutp H G F l f g].

Lemma sumoutpE H G F l f g : 
  @sumoutp H G F l f g = \sum_i (l i) *: [> g i ; f i <].
Proof. by rewrite unlock. Qed.

Lemma sumoutp_adj (H G : chsType) (F : finType) (l : F -> C) 
  (f : F -> H) (g : F -> G) :
  (sumoutp l f g)^A = sumoutp (fun i=>(l i)^*) g f.
Proof.
rewrite !sumoutpE raddf_sum; apply eq_bigr=>i _.
by rewrite/=adjfZ adj_outp; simpc.
Qed.

Lemma sumoutp_comp (H G K: chsType) (F : finType) (l l' : F -> C) 
  (f : 'PONB(F;H)) (g : F -> G) (h : F -> K):
  (sumoutp l f g) \o (sumoutp l' h f) = sumoutp (fun i=>l i * l' i) h g.
Proof.
rewrite !sumoutpE linear_suml; apply eq_bigr=>i _.
rewrite /= linear_sumr (bigD1 i)//= big1=>[j/negPf nj|];
rewrite/= -!(comp_lfunZl, comp_lfunZr) outp_comp ponb_dot.
by rewrite eq_sym nj scale0r !scaler0.
by rewrite eqxx !scalerA mulr1 addr0.
Qed.

Lemma sumoutp_apply (H G : chsType) (F : finType) (l : F -> C) 
  (f : 'PONB(F;H)) (g : F -> G) i :
  (sumoutp l f g) (f i) = l i *: g i.
Proof.
by rewrite sumoutpE sum_lfunE (bigD1 i)//= big1=>[j/negPf nj|];
rewrite -outpZl outpE ponb_dot ?nj ?scale0r// eqxx scale1r addr0.
Qed.

End CastFinFun.

Section SumoutpLinear.
Variable (H G : chsType) (F : finType).
Implicit Type (l : F -> C) (f : F -> H) (g : F -> G) (c : C).

Lemma sumoutpZ c l f g :
  c *: (sumoutp l f g) = sumoutp (fun i=> c * (l i)) f g.
Proof.
by rewrite !sumoutpE raddf_sum; apply eq_bigr=>i _; rewrite/= scalerA.
Qed.

Lemma sumoutpZl c l f g :
  c *: (sumoutp l f g) = sumoutp l (fun i=>c^* *: f i) g.
Proof.
by rewrite !sumoutpE raddf_sum; apply eq_bigr=>i _; rewrite/= outpZr conjCK !scalerA mulrC.
Qed.

Lemma sumoutpZr c l f g :
  c *: (sumoutp l f g) = sumoutp l f (fun i=>c *: g i).
Proof.
by rewrite !sumoutpE raddf_sum; apply eq_bigr=>i _; rewrite/= outpZl !scalerA mulrC.
Qed.

Lemma sumoutpD l l' f g :
  (sumoutp l f g) + (sumoutp l' f g)= sumoutp (fun i=>l i + l' i) f g.
Proof.
by rewrite !sumoutpE -big_split/=; under eq_bigr do rewrite -scalerDl.
Qed.

Lemma sumoutpDl l f f' g :
  (sumoutp l f g) + (sumoutp l f' g)= sumoutp l (fun i=>f i + f' i) g.
Proof.
by rewrite !sumoutpE -big_split/=; under eq_bigr do rewrite/= -scalerDr -outpDr.
Qed.

Lemma sumoutpDr l f g g' :
  (sumoutp l f g) + (sumoutp l f g')= sumoutp l f (fun i=>g i + g' i).
Proof.
by rewrite !sumoutpE -big_split/=; under eq_bigr do rewrite -scalerDr -outpDl.
Qed.

Lemma sumoutpN l f g :
  - (sumoutp l f g)= sumoutp (fun i=>- l i) f g.
Proof.
by rewrite !sumoutpE linear_sum/=; under eq_bigr do rewrite -scaleNr.
Qed.

Lemma sumoutpNl l f g :
  - (sumoutp l f g)= sumoutp l (fun i=>- f i) g.
Proof.
by rewrite !sumoutpE linear_sum/=; under [RHS]eq_bigr do rewrite/= outpNr scalerN.
Qed.

Lemma sumoutpNr l f g :
  - (sumoutp l f g)= sumoutp l f (fun i=>- g i).
Proof.
by rewrite !sumoutpE linear_sum/=; under [RHS]eq_bigr do rewrite/= outpNl scalerN.
Qed.

End SumoutpLinear.

Section Decomposition.
Variable (H : chsType).
Implicit Type (U V W : {hspace H}).

Lemma sumoutp_eq (G : chsType) (F : finType) (l l' : F -> C) 
  (f : F -> H) (g : F -> G) :
    l =1 l' -> sumoutp l f g = sumoutp l' f g.
Proof. by move=>P; rewrite !sumoutpE; apply eq_bigr=>i _; rewrite P. Qed.
Lemma sumoutp_cast (G : chsType) (F K: finType) (eqc : #|F| = #|K|) 
  (l : F -> C) (f : F -> H) (g : F -> G) :
  sumoutp (castfun eqc l) (castfun eqc f) (castfun eqc g) = sumoutp l f g.
Proof.
pose h i := enum_val (cast_ord (esym eqc) (enum_rank i)).
rewrite /sumoutp (reindex h)//. 
exists (fun i=>enum_val (cast_ord eqc (enum_rank i)))=>i _;
by rewrite /h enum_valK cast_ord_comp cast_ord_id enum_rankK.
Qed.

Lemma sumoutp_herm (F : finType) (f : F -> H) (l : F -> C) 
  (P : forall i, l i \is Num.real) :
  sumoutp l f f \is hermlf.
Proof.
apply/hermlfP; rewrite sumoutpE raddf_sum; apply eq_bigr=>i _.
by rewrite /=adjfZ adj_outp conj_Creal.
Qed.
Definition sumoutp_hermfType F f l P := HermfType (@sumoutp_herm F f l P).
Lemma sumoutp_proj (F : finType) (f : 'PONB(F;H)) :
  sumoutp (fun=>1) f f \is projlf.
Proof.
apply/projlfP; split; first by apply/hermlfP/sumoutp_herm=>x; rewrite real1.
rewrite sumoutpE linear_suml; apply eq_bigr=>i _.
by rewrite linear_sumr (bigD1 i)//= big1=>[j/negPf nj|];
rewrite ?scale1r outp_comp ponb_dot ?eqxx ?addr0 ?scale1r// eq_sym nj scale0r.
Qed.
Canonical sumoutp_projfType F f := ProjfType (@sumoutp_proj F f).
Canonical sumoutp_obsfType (F : finType) (f : 'PONB(F;H)) := Eval hnf in 
  [obs of sumoutp (fun=>1) f f as [obs of [proj of sumoutp (fun=>1) f f]]].
Canonical sumoutp_psdfType (F : finType) (f : 'PONB(F;H)) := Eval hnf in 
  [psd of sumoutp (fun=>1) f f as [psd of [proj of sumoutp (fun=>1) f f]]].

Lemma supph_sumoutp (G : chsType) (F : finType) (l : F -> C) 
  (f : 'PONB(F;H)) (g : 'PONB(F;G)) :
  supph (sumoutp l f g) = supph (sumoutp (fun i=>(l i != 0)%:R) f f).
Proof.
apply/hsC_inj/eqhP=>x; rewrite !memh_suppCE.
rewrite !sumoutpE !sum_lfunE; under eq_bigr do rewrite lfunE/= outpE scalerA.
under [in RHS]eq_bigr do rewrite lfunE/= outpE scalerA.
apply/eqb_iff; rewrite !eq_iff !ponb_sum_eq0; split=>P i; move: (P i);
case: eqP=>[->|/eqP/negPf P1]; rewrite ?mul0r// mul1r.
by move=>/eqP; rewrite mulf_eq0 P1/==>/eqP.
by move=>->; rewrite mulr0.
Qed.

Lemma lesupph_sumoutp (G : chsType) (F : finType) (l : F -> C) 
  (f : F -> H) (g : F -> G) :
  supph (sumoutp l f g) `<=` supph (sumoutp (fun=>1) f f).
Proof.
apply/leh_memCP=>x; rewrite !supphP sumoutpE=>/eqP/(f_equal (dotp x))/eqP.
rewrite sum_lfunE dotp_sumr linear0.
under eq_bigr do rewrite scale1r outpE dotpZr -conj_dotp -normCKC.
rewrite psumr_eq0=>[i _|]. by rewrite exprn_ge0.
rewrite -big_all big_andE=>/forallP/= P.
have P1: forall i, [< f i ; x >] = 0 by move=>i; move: (P i); 
  rewrite -conj_dotp norm_conjC expf_eq0/= normr_eq0=>/eqP.
apply/eqP; rewrite sumoutpE sum_lfunE big1// =>i _.
by rewrite lfunE/= outpE P1 scale0r scaler0.
Qed.

Lemma sumoutp_trlf (F : finType) l (f : 'PONB(F;H)) :
  \Tr (sumoutp l f f) = \sum_i (l i).
Proof.
rewrite sumoutpE linear_sum/=;
by under eq_bigr do rewrite/= linearZ/= outp_trlf ns_dot mulr1.
Qed.

Lemma sumoutp_cst_trlf (F : finType) (f : 'PONB(F;H)) (c : C):
  \Tr (sumoutp (fun=>c) f f) = c * #|F|%:R.
Proof. by rewrite sumoutp_trlf sumr_const mulr_natr. Qed.

Lemma sumoutp1_trlf (F : finType) (f : 'PONB(F;H)) :
  \Tr (sumoutp (fun=>1) f f) = #|F|%:R.
Proof. by rewrite sumoutp_cst_trlf mul1r. Qed.

Lemma dim_supp_sumoutp (F : finType) (f : 'PONB(F;H)) :
  \Dim (supph (sumoutp (fun=>1) f f)) = #|F|.
Proof.
apply/eqP; rewrite -(eqr_nat [numDomainType of C]).
by rewrite/= -projf_trlf/= supph_projK hsE/= sumoutp1_trlf.
Qed.

End Decomposition.

(* unitarylf : spetralUE eigenvalU_norm1 *)
(* projlf : spectralPE sumoutp (fun=>1) eigenvec eigenvec *)
(* proj1lf : spetralP1E [> eigenvecP1 ; eigenvecP1 <] *)
(* other case: spectralE eigenval_proj .. property of eigenval *)
Section SpectralDecomposition.
Variable (H : chsType).

Definition eigenvec_all (U : 'End(H)) i :=
  r2v (row i (spectralmx (f2mx U))).
Definition eigenval_all (U : 'End(H)) i :=
  spectral_diag (f2mx U) 0 i.

Lemma eigenvec_all_onb (U : 'End(H)) i j : 
  [< eigenvec_all U i ; eigenvec_all U j >] = (i == j)%:R.
Proof.
rewrite dotp_mulmx -[_^*m]trmxK -trmx_mul mxE /eigenvec_all !r2vK.
by rewrite conjmxE map_row tr_row -mulmx_rowcol map_trmx 
  -adjmxE unitarymxK ?spectral_unitarymx// mxE eq_sym.
Qed.
Canonical eigenvec_all_ponbasis U := PONBasis (@eigenvec_all_onb U).
Canonical eigenvec_all_onbasis U := ONBasis (@eigenvec_all_onb U) (@card_ord _).
Canonical eigenvec_all_nsType U i := Eval hnf in 
  [NS of @eigenvec_all U i as [NS of [PONB of @eigenvec_all U] i]].

Definition spectral_all U := (sumoutp (eigenval_all U) (eigenvec_all U) (eigenvec_all U)).

Lemma spectral_all_trlf U : \Tr (spectral_all U) = \sum_i (eigenval_all U i).
Proof.
rewrite /spectral_all sumoutpE linear_sum; apply eq_bigr=>i _.
by rewrite/= linearZ/= outp_trlf onb_dot eqxx mulr1.
Qed.

Lemma spectral_allPmx U : f2mx U \is normalmx -> U = spectral_all U.
Proof.
rewrite qualifE=>/unitarymx_spectralP P.
apply/f2mx_inj. rewrite /spectral_all sumoutpE P linear_sum/=.
rewrite mulmx_colrow; apply eq_bigr=>i _.
rewrite col_diag_mul linearZ/= /eigenval_all /eigenvec_all r2vK -scalemxAl.
by do 2 f_equal; rewrite !adjmxE -map_col -tr_row.
Qed.

Lemma spectral_allUP U : U \is unitarylf -> U = spectral_all U.
Proof. rewrite qualifE=>/unitarymx_normal; exact: spectral_allPmx. Qed.
Lemma spectral_allP U : U \is hermlf -> U = spectral_all U.
Proof. rewrite qualifE=>/hermmx_normal; exact: spectral_allPmx. Qed.
Lemma spectralUE (U : 'FU(H)) : U%:VF = spectral_all U.
Proof. apply/spectral_allUP/unitaryf_unitary. Qed.
Lemma spectral_allE (U : 'FH(H)) : U%:VF = spectral_all U.
Proof. apply/spectral_allP/hermf_herm. Qed.

Lemma eigenvalU_norm1 (U : 'FU(H)) i : `|@eigenval_all U i| = 1.
Proof.
move: (unitaryf_unitary U)=>/unitarylfP/lfunP/(_ (eigenvec_all U i))
/(f_equal (dotp (eigenvec_all U i)))/eqP.
rewrite lfunE/= adj_dotEV lfunE/= !dotp_norm {1}spectralUE /spectral_all sumoutp_apply.
by rewrite normrZ ns_norm mulr1 expr1n sqrp_eq1// =>/eqP.
Qed.

Lemma spectral_all_herm (U : 'FH(H)) : spectral_all U \is hermlf.
Proof. by rewrite -spectral_allP hermf_herm. Qed.
Canonical spectral_all_hermfType U := HermfType (spectral_all_herm U).
Lemma spectral_all_psd (U : 'F+(H)) : spectral_all U \is psdlf.
Proof. by rewrite -spectral_allP ?psdlf_herm ?psdf_psd. Qed.
Canonical spectral_all_psdfType U := PsdfType (spectral_all_psd U).
Lemma spectral_all_obs (U : 'FO(H)) : spectral_all U \is obslf.
Proof. by rewrite -spectral_allP ?obslf_herm ?obsf_obs. Qed.
Canonical spectral_all_obsfType U := ObsfType (spectral_all_obs U).
Lemma spectral_all_den (U : 'FD(H)) : spectral_all U \is denlf.
Proof. by rewrite -spectral_allP ?denlf_herm ?denf_den. Qed.
Canonical spectral_all_denfType U := DenfType (spectral_all_den U).
Lemma spectral_all_den1 (U : 'FD1(H)) : spectral_all U \is den1lf.
Proof. by rewrite -spectral_allP ?den1lf_herm ?den1f_den1. Qed.
Canonical spectral_all_den1fType U := Den1fType (spectral_all_den1 U).
Lemma spectral_all_proj (U : 'FP(H)) : spectral_all U \is projlf.
Proof. by rewrite -spectral_allP ?projlf_herm ?projf_proj. Qed.
Canonical spectral_all_projfType U := ProjfType (spectral_all_proj U).
Lemma spectral_all_proj1 (U : 'FP1(H)) : spectral_all U \is proj1lf.
Proof. by rewrite -spectral_allP ?proj1lf_herm ?proj1f_proj1. Qed.
Canonical spectral_all_proj1fType U := Proj1fType (spectral_all_proj1 U).
Lemma spectral_all_unitary (U : 'FU(H)) : spectral_all U \is unitarylf.
Proof. by rewrite -spectral_allUP ?unitaryf_unitary. Qed.
Canonical spectral_all_unitaryfType U := UnitaryfType (spectral_all_unitary U).

(* remark : for unitarylf, use spectral_all *)
(* following : give decomposition : \Rank U rather than the whole space *)

Definition eigen_index_sig (U : 'End(H)) := 
    [finType of {i : 'I_(Vector.dim H) | eigenval_all U i != 0}].

Definition eigen_index (U : 'End(H)) : 'I_(\Rank U) -> 'I_(Vector.dim H) :=
  match \Rank U =P #|eigen_index_sig U| with
  | ReflectT equ => fun i => val (enum_val (cast_ord equ i))
  | ReflectF _ => fun i => widen_ord (ranklf_le_dom U) i
  end.

Lemma widen_ord_inj n m le_n_m : injective (@widen_ord n m le_n_m).
Proof. by move=>i j /(f_equal val)/= P; apply/val_inj=>//. Qed.

Lemma eigen_index_inj (U : 'End(H)) : injective (@eigen_index U).
Proof.
by move=>i j; rewrite /eigen_index; case: eqP=>
  [?/val_inj/enum_val_inj/cast_ord_inj|?/widen_ord_inj].
Qed.

Definition eigenvec (U : 'End(H)) i := eigenvec_all U (@eigen_index U i).
Definition eigenval (U : 'End(H)) i := eigenval_all U (@eigen_index U i).

Lemma eigenvec_ponb (U : 'End(H)) i j : 
  [< @eigenvec U i ; @eigenvec U j >] = (i == j)%:R.
Proof. by rewrite/eigenvec onb_dot (inj_eq (@eigen_index_inj _)). Qed.
Canonical eigenvec_ponbasis U := PONBasis (@eigenvec_ponb U).
Canonical eigenvec_nsType U i := Eval hnf in 
  [NS of @eigenvec U i as [NS of [PONB of @eigenvec U] i]].
Definition spectral U := (sumoutp (@eigenval U) (@eigenvec U) (@eigenvec U)).

Lemma eigen_index_card (U : 'End(H)) : f2mx U \is normalmx -> 
  \Rank U = #|eigen_index_sig U|.
Proof.
move=>/unitarymx_spectralP P.
rewrite /eigen_index_sig card_sig -[RHS]muln1 -sum_nat_const /lfrank.
rewrite P mxrank_mulmxU ?mxrank_mulUCmx ?spectral_unitarymx// rank_diagmx /eigenval_all.
rewrite (bigID (fun i=>(spectral_diag (f2mx U) 0 i != 0)))/= [X in (_ + X)%N]big1 ?addn0.
by move=>i/negbNE/eqP->; rewrite eqxx.
by apply eq_bigr=>i; rewrite inE=>->.
Qed.

Lemma spectralPA (U : 'End(H)) : f2mx U \is normalmx -> U = spectral U.
Proof.
move=>P; rewrite {1}(spectral_allPmx P) /spectral_all sumoutpE.
rewrite (bigID (fun i=>(spectral_diag (f2mx U) 0 i != 0))) [in LHS]/= [X in (_ + X)]big1 ?addr0.
by rewrite /eigenval_all; move=>i/negbNE/eqP->; rewrite scale0r.
rewrite /spectral sumoutpE -[LHS]big_sig /eigenval /eigenvec /eigen_index.
case: eqP=>//[P2|]; last by rewrite -eigen_index_card.
apply: reindex; exists (fun i=> cast_ord (esym P2) (enum_rank i));
by move=>x _; rewrite 1?enum_valK cast_ord_comp cast_ord_id// enum_rankK.
Qed.

Lemma eigenval_neq0A (U : 'End(H)) : 
  f2mx U \is normalmx -> (forall i, @eigenval U i != 0).
Proof.
move=>P i; rewrite /eigenval /eigen_index; case: eqP; last by rewrite -eigen_index_card.
move=>P1/=; case: (enum_val (cast_ord P1 i))=>x IH//.
Qed.
Lemma eigenval_eq0A (U : 'End(H)) : 
  f2mx U \is normalmx -> (forall i, @eigenval U i == 0 = false).
Proof. by move=>/eigenval_neq0A +i; move=>/(_ i)/negPf. Qed.

(* Lemma spectralUP U : U \is unitarylf -> U = spectral U.
Proof. rewrite qualifE=>/unitarymx_normal; exact: spectralPA. Qed. *)
Lemma spectralP U : U \is hermlf -> U = spectral U.
Proof. rewrite qualifE=>/hermmx_normal; exact: spectralPA. Qed.
(* Lemma spectralUE (U : 'FU(H)) : U%:VF = spectral U.
Proof. apply/spectralUP/unitaryf_unitary. Qed. *)
Lemma spectralE (U : 'FH(H)) : U%:VF = spectral U.
Proof. apply/spectralP/hermf_herm. Qed.

Lemma eigenval_neq0 (U : 'FH(H)) i : @eigenval U i != 0.
Proof. by apply/eigenval_neq0A/hermmx_normal; move: (hermf_herm U); rewrite qualifE. Qed.
Lemma eigenval_eq0 (U : 'FH(H)) i : @eigenval U i == 0 = false.
Proof. apply/eqP/eqP; exact: eigenval_neq0. Qed.

Lemma eigenval_herm (U : 'FH(H)) i : @eigenval U i \is Num.real.
Proof.
move: (hermf_herm U)=>/hermlfP.
rewrite {1 2}spectralE /spectral sumoutp_adj=>/lfunP/(_ (eigenvec i)).
by rewrite !sumoutp_apply=>/ns_scaleI/CrealP.
Qed.
Lemma eigenval_psd (U : 'F+(H)) i : @eigenval U i > 0.
Proof.
by move: (psdf_psd U)=>/psdlfP/(_ (eigenvec i)); rewrite {2}spectralE 
  /spectral sumoutp_apply dotpZr ns_dot mulr1 le_eqVlt eq_sym eigenval_eq0.
Qed.
Lemma eigenval_obs (U : 'FO(H)) i : 0 < @eigenval U i <= 1.
Proof.
move: (obsf_obs U)=>/obslfP[_]/(_ (eigenvec i)).
by rewrite {2}spectralE /spectral sumoutp_apply dotpZr ns_dot mulr1 eigenval_psd.
Qed.
Lemma eigenval_proj (U : 'FP(H)) i : @eigenval U i = 1.
Proof.
move: (projf_idem U)=>/lfunP/(_ (eigenvec i)).
by rewrite {1 2 4}spectralE /spectral lfunE/= sumoutp_apply linearZ/= sumoutp_apply 
  scalerA -expr2=>/ns_scaleI/eqP; rewrite idemr_01 eigenval_eq0/==>/eqP.
Qed.
Lemma spectralPE (U : 'FP(H)) : U%:VF = sumoutp (fun=>1) (@eigenvec U) (@eigenvec U).
rewrite {1}spectralE /spectral/=; apply/sumoutp_eq=>i; exact: eigenval_proj.
Qed.
Lemma rank_proj1 (U : 'FP1(H)) : \Rank U = 1%N.
Proof. by move: (proj1f_proj1 U)=>/proj1lf_rankP[]. Qed.
Lemma trlf_proj1 (U : 'FP1(H)) : \Tr U = 1.
Proof. by move: (proj1f_proj1 U)=>/proj1lfP[]. Qed.
Lemma eigen_index_P1 (U : 'FP1(H)) : #|'I_(\Rank U) | = #|'I_1|.
Proof. by rewrite rank_proj1. Qed.
Definition eigenvecP1 (U : 'FP1(H)) := castfun (eigen_index_P1 U) (@eigenvec U) ord0.
Lemma spectralP1E (U : 'FP1(H)) : U%:VF = [> eigenvecP1 U ; eigenvecP1 U <].
Proof.
rewrite {1}spectralE/=/spectral -(sumoutp_cast (eigen_index_P1 U)).
by rewrite sumoutpE big_ord1 /castfun eigenval_proj scale1r.
Qed.
Lemma eigenvectP1_ns (U : 'FP1(H)) : [< eigenvecP1 U ; eigenvecP1 U >] == 1.
Proof. by rewrite -outp_trlf -spectralP1E trlf_proj1. Qed.
Canonical eigenvectP1_nsType U := NSType (@eigenvectP1_ns U).

Lemma supph_eigenE (U : 'FH(H)) : 
  (supph U)%:VF = sumoutp (fun=>1) (@eigenvec U) (@eigenvec U).
Proof.
rewrite {1}spectralE/spectral supph_sumoutp/=.
suff P: (fun i : 'I_(\Rank U) => (eigenval i != 0)%:R) =1 (fun=>1 : C).
by rewrite (sumoutp_eq _ _ P) supph_projK hsE.
by move=>i; rewrite eigenval_neq0.
Qed.

Lemma spectral_herm (U : 'FH(H)) : spectral U \is hermlf.
Proof. by rewrite -spectralP hermf_herm. Qed.
Canonical spectral_hermfType U := HermfType (spectral_herm U).
Lemma spectral_psd (U : 'F+(H)) : spectral U \is psdlf.
Proof. by rewrite -spectralP ?psdlf_herm ?psdf_psd. Qed.
Canonical spectral_psdfType U := PsdfType (spectral_psd U).
Lemma spectral_obs (U : 'FO(H)) : spectral U \is obslf.
Proof. by rewrite -spectralP ?obslf_herm ?obsf_obs. Qed.
Canonical spectral_obsfType U := ObsfType (spectral_obs U).
Lemma spectral_den (U : 'FD(H)) : spectral U \is denlf.
Proof. by rewrite -spectralP ?denlf_herm ?denf_den. Qed.
Canonical spectral_denfType U := DenfType (spectral_den U).
Lemma spectral_den1 (U : 'FD1(H)) : spectral U \is den1lf.
Proof. by rewrite -spectralP ?den1lf_herm ?den1f_den1. Qed.
Canonical spectral_den1fType U := Den1fType (spectral_den1 U).
Lemma spectral_proj (U : 'FP(H)) : spectral U \is projlf.
Proof. by rewrite -spectralP ?projlf_herm ?projf_proj. Qed.
Canonical spectral_projfType U := ProjfType (spectral_proj U).
Lemma spectral_proj1 (U : 'FP1(H)) : spectral U \is proj1lf.
Proof. by rewrite -spectralP ?proj1lf_herm ?proj1f_proj1. Qed.

(* following for hspace *)
Definition heigen (U : {hspace H}) : 'I_(\Dim U) -> H := (@eigenvec U).
Canonical heigen_ponbasis U := Eval hnf in [PONB of @heigen U].
Canonical heigen_nsType U i := Eval hnf in [NS of @heigen U i].
Lemma heigenE (U : {hspace H}) :
  U%:VF = sumoutp (fun=>1) (@heigen U) (@heigen U).
Proof. exact: spectralPE. Qed.

(* since heigen is a ponb, we can always extend it to the whole space *)
Lemma sumoutp_applyC (G : chsType) (F : finType) (l : F -> C) 
  (f : 'PONB(F;H)) (g : F -> G) i :
  (sumoutp l f g) (ponb_compl f i) = 0.
Proof.
rewrite sumoutpE sum_lfunE big1// =>j _.
by rewrite lfunE/= outpE ponb_ortho_compl scale0r scaler0.
Qed.

Lemma sumoutp_compl (F : finType) (f : 'PONB(F;H)) :
  sumoutp (fun=>1) f f + sumoutp (fun=>1) (ponb_compl f) (ponb_compl f) = \1.
Proof.
apply/(intro_onb [ONB of (ponb_ext f)])=>/= i.
rewrite !lfunE/=; case: i=>i; rewrite ?ponb_extCE ?ponb_extE 
  ?sumoutp_apply ?sumoutp_applyC scale1r ?add0r//.
rewrite sumoutpE sum_lfunE big1 ?addr0// =>j _.
by rewrite scale1r outpE ponb_ortho_complV scale0r.
Qed.

Lemma hspacelfP (A B : {hspace H}) : A%:VF = B <-> A = B.
Proof. by split=>[/lfunP|/hspaceP] P; [apply/hspaceP=>i|apply/lfunP=>i]. Qed.

Lemma sumoutp_hsC (U : {hspace H}) : 
  (~` U) = supph (sumoutp (fun=>1) (ponb_compl [PONB of @heigen U]) 
  (ponb_compl [PONB of @heigen U])).
Proof.
apply/hspacelfP; rewrite supph_projK hs2lfE hsE/= /cplmt.
move: (sumoutp_compl [PONB of @heigen U])=>/esym/eqP; rewrite addrC -subr_eq=>/eqP<-.
by rewrite {1}spectralPE.
Qed.

End SpectralDecomposition.

Section RankExtra.
Variable (F G H : chsType).

Lemma ranklfM_max (A : 'Hom(F,G)) (B : 'Hom(H,F)) :
  (\Rank (A \o B) <= Vector.dim F)%N.
Proof. by rewrite /lfrank f2mx_comp; exact: mulmx_max_rank. Qed.

Lemma ranklfM_maxl (A : 'Hom(F,G)) (B : 'Hom(H,F)) :
  (\Rank (A \o B) <= \Rank A)%N.
Proof. by rewrite /lfrank f2mx_comp; exact: mxrankM_maxr. Qed.

Lemma ranklfM_maxr (A : 'Hom(F,G)) (B : 'Hom(H,F)) :
  (\Rank (A \o B) <= \Rank B)%N.
Proof. by rewrite /lfrank f2mx_comp; exact: mxrankM_maxl. Qed.

Lemma ranklfM_min (A : 'Hom(F,G)) (B : 'Hom(H,F)) :
  (\Rank A + \Rank B - Vector.dim F <= \Rank (A \o B))%N.
Proof. rewrite /lfrank f2mx_comp addnC; exact: mxrank_mul_min. Qed.

Lemma ranklfM0_max (A : 'Hom(F,G)) (B : 'Hom(H,F)) :
  A \o B = 0 -> (\Rank A + \Rank B <= Vector.dim F)%N.
Proof. by move=>/(f_equal f2mx); rewrite /lfrank addnC f2mx_comp linear0; exact: mulmx0_rank_max. Qed.

Lemma ranklfM1_max (B : 'Hom(F,G)) (A : 'Hom(G,H)) (C : 'Hom(H,F)) :
  A \o B \o C = \1 -> (Vector.dim H <= \Rank B)%N.
Proof. move=>/(f_equal f2mx); rewrite /lfrank !f2mx_comp f2mx1 mulmxA; exact: mulmx1_min_rank. Qed.

Lemma ranklf_Frobenius (I : chsType) (A : 'Hom(F,G)) (B : 'Hom(H,F)) (C : 'Hom(I,H)) :
  (\Rank (A \o B) + \Rank (B \o C) <= \Rank B + \Rank (A \o B \o C))%N.
Proof. rewrite /lfrank !f2mx_comp mulmxA addnC; exact: mxrank_Frobenius. Qed.

Lemma ranklfM_free (A : 'Hom(F,G)) (B : 'Hom(H,F)) :
  (Vector.dim F <= \Rank A)%N -> \Rank (A \o B) = \Rank B.
Proof.
rewrite /lfrank row_leq_rank f2mx_comp; exact: mxrankMfree.
Qed.

End RankExtra.


Section CopyVspace.
Variable (H : chsType).
Implicit Type (U V W : {hspace H}).

Lemma lehPn {U V} : reflect (exists2 u, u \in U & u \notin V) (~~ (U `<=` V)).
Proof. 
by rewrite leh2v; apply/(iffP (@subvPn _ _ _ _)); 
move=>[u P1 P2]; exists u; rewrite ?memh2v// -memh2v.
Qed.

(* Picking a non-zero vector in a subspace. *)
(* Lemma memv_pick U : vpick U \in U. Proof. by rewrite mem_r2v nz_row_sub. Qed.

Lemma vpick0 U : (vpick U == 0) = (U == 0%VS).
Proof. by  rewrite -memv0 mem_r2v -subv0 /subV vs2mx0 !submx0 nz_row_eq0. Qed. *)

(* Sum of subspaces. *)
Lemma memhU u v U V : u \in U -> v \in V -> u + v \in U `|` V.
Proof. simph2v; exact: memv_add. Qed.
Lemma memhUP {w U V} :
  reflect (exists2 u, u \in U & exists2 v, v \in V & w = u + v)
          (w \in U `|` V).
Proof.
simph2v; apply/(iffP (memv_addP)); move=>[u Pu[v Pv Puv]]; 
by (exists u; last exists v); simph2v=>//; simpv2h=>//.
Qed.

Lemma memh_cupsl I r (P : pred I) vs U :
  (forall i, P i -> vs i \in U) -> \sum_(i <- r | P i) vs i \in U.
Proof. by simph2v=>P1; apply/memv_suml=>i/P1; simph2v. Qed.

Lemma memh_cupsr I (r : seq I) (P : pred I) (vs : I -> H) (Us : I -> {hspace H}) :
    (forall i, P i -> vs i \in Us i) ->
  \sum_(i <- r | P i) vs i \in (\cup_(i <- r | P i) Us i).
Proof.
move=>Uv; elim: r=>[|r x IH]; first by rewrite !big_nil mem0h.
by rewrite !big_cons; case E: (P r)=>//; apply/memhU=>//; apply Uv.
Qed.

Lemma memh_cupsP (I : finType) {P : pred I} {Us : I -> {hspace H}} {v} : 
  reflect (exists2 vs, forall i, P i ->  vs i \in Us i
                     & v = \sum_(i | P i) vs i)
          (v \in \cup_(i | P i) Us i).
Proof.
rewrite memh2v cuphs2v vs2hsK; apply/(iffP memv_sumP); 
by move=>[vs P1 P2]; exists vs=>[i/P1|//]; simph2v.
Qed.

Lemma memhI w U V : (w \in U `&` V) = (w \in U) && (w \in V).
Proof. simph2v; exact: memv_cap. Qed.

Lemma memhIP {w U V} : reflect (w \in U /\ w \in V) (w \in U `&` V).
Proof. simph2v; exact: memv_capP. Qed.

Lemma hs_modl U V W : U `<=` W -> U `|` (V `&` W) = (U `|` V) `&` W.
Proof. simph2v=>P; f_equal; exact: vspace_modl. Qed.

Lemma hs_modr  U V W : W `<=` U -> (U `&` V) `|` W = U `&` (V `|` W).
Proof. by rewrite -!(cuphC W) !(caphC U); apply: hs_modl. Qed.

Lemma diffhE U V : U `\` V =  U `&` (~` (U `&` V)). Proof. by []. Qed.
Lemma leBh U V : U `\` V `<=` U. Proof. exact: lehIl. Qed.
Lemma caphDx U V : (U `\` V) `&` V = `0`.
Proof. by rewrite diffhE caphAC caphxC. Qed.
Lemma caphxD U V : V `&` (U `\` V) = `0`.
Proof. by rewrite caphC caphDx. Qed.
Lemma cuphDI U V : (U `\` V) `|` (U `&` V) = U.
Proof. by rewrite diffhE cuphC [_ `&` ~` _]caphC hsUCI ?lehIl. Qed.
Lemma cuphID U V : (U `&` V) `|` (U `\` V) = U.
Proof. by rewrite cuphC cuphDI. Qed.
Lemma cuphDx U V : (U `\` V) `|` V = U `|` V.
Proof. by rewrite -{2}(cuphDI U V) -cuphA caphUK. Qed.
Lemma cuphxD U V : V `|` (U `\` V) = V `|` U.
Proof. by rewrite !(cuphC V) cuphDx. Qed.

(* Subspace dimension. *)
Lemma dimh0 : \Dim (`0` : {hspace H}) = 0%N.
Proof. by rewrite /dimh hs2lfE ranklf0. Qed.
Lemma dimh1 : \Dim (`1` : {hspace H}) = Vector.dim H.
Proof. by rewrite /dimh hs2lfE ranklf1. Qed.
Lemma dimhC (U : {hspace H}) : \Dim (~` U) = (\Dim {:H} - \Dim U)%N.
Proof. by rewrite sumoutp_hsC dim_supp_sumoutp !card_ord dimh1. Qed.
Lemma dimh_le U V : U `<=` V -> (\Dim U <= \Dim V)%N.
Proof. by rewrite leh_compr /dimh=>/eqP<-; exact: ranklfM_maxl. Qed.
Lemma dimhIl U V : (\Dim (U `&` V) <= \Dim U)%N.
Proof. apply/dimh_le; exact: leIl. Qed.
Lemma dimhIr U V : (\Dim (U `&` V) <= \Dim V)%N. 
Proof. apply/dimh_le; exact: leIr. Qed.
Lemma dimhUl U V : (\Dim U <= \Dim (U `|` V))%N.
Proof. apply/dimh_le; exact: leUl. Qed.
Lemma dimhUr U V : (\Dim V <= \Dim (U `|` V))%N.
Proof. apply/dimh_le; exact: leUr. Qed.

Lemma dimh_eq0 U :  (\Dim U == 0%N) = (U == `0`).
Proof. simph2v; exact: dimv_eq0. Qed.
Lemma dim_hline (v : H) : \Dim <[v]> = (v != 0).
Proof. simph2v; exact: dim_vline. Qed.
Lemma dimh_leqif_sup U V : U `<=` V -> (\Dim U <= \Dim V ?= iff (V `<=` U))%N.
Proof. simph2v; exact: dimv_leqif_sup. Qed.
Lemma dimh_leqif_eq U V : U `<=` V -> (\Dim U <= \Dim V ?= iff (U == V))%N.
Proof. simph2v; exact: dimv_leqif_eq. Qed.
Lemma eqhEdim U V : (U == V) = (U `<=` V) && (\Dim V <= \Dim U)%N.
Proof. simph2v; exact: eqEdim. Qed.
Lemma dimhUI U V : (\Dim (U `|` V) + \Dim (U `&` V) = \Dim U + \Dim V)%N.
Proof. simph2v; exact: dimv_sum_cap. Qed.
Lemma dimhU_disjoint U V :
  U `&` V = `0` -> \Dim (U `|` V) = (\Dim U + \Dim V)%N.
Proof. simph2v=>/vs2hs_inj; exact: dimv_disjoint_sum. Qed.
Lemma dimhID U V : (\Dim (U `&` V) + \Dim (U `\` V))%N = \Dim U.
Proof.
rewrite -[in RHS](cuphID U V) dimhU_disjoint//.
by rewrite diffhE caphC -caphA caphCx caph0.
Qed.
Lemma dimhDI U V : (\Dim (U `\` V) + \Dim (U `&` V))%N = \Dim U.
Proof. by rewrite addnC dimhID. Qed.
Lemma dimhU_leqif U V :
  (\Dim (U `|` V) <= \Dim U + \Dim V ?= iff (U `&` V `<=` `0`))%N.
Proof. simph2v; exact: dimv_add_leqif. Qed.
Lemma hsD_eq0 U V : (U `\` V == `0`) = (U `<=` V).
Proof.
rewrite -dimh_eq0 -(eqn_add2l (\Dim (U `&` V))) addn0 dimhID eq_sym.
by rewrite (dimh_leqif_eq (lehIl _ _)) eq_caphl.
Qed.
Lemma dimv_leq_sum I r (P : pred I) (Us : I -> {hspace H}) : 
  (\Dim (\cup_(i <- r | P i) Us i) <= \sum_(i <- r | P i) \Dim (Us i))%N.
Proof.
elim/big_rec2: _ =>/= [|i d vs _ le_vs_d]; first by rewrite dimh0.
by apply: (leq_trans (dimhU_leqif _ _)); rewrite leq_add2l.
Qed.

End CopyVspace.

(* basis, onbasis *)

(* ?? split part to orthomodular lattice ?? *)
(* orthogonal between vector & space , space & space , vector & vector *)
(* commutative , lattice commute <-> projection commute *)
Section ProjectionLattice.
Variable (H : chsType).
End ProjectionLattice.

Section Extra.
Variable (H : chsType).
Implicit Type (u v : H) (U V : {hspace H}).

(* norm and dot compared to 1 *)
Lemma hnorm_le1 v : `|v| <= 1 = ([< v ; v >] <= 1).
Proof. by rewrite dotp_norm -{2}(expr1n _ 2%N) ler_pexpn2r// nnegrE. Qed.
Lemma hnorm_eq1 v : `|v| == 1 = ([<v ; v>] == 1).
Proof. by rewrite dotp_norm -{2}(expr1n _ 2%N) eqr_expn2//. Qed.

Lemma memh_line v : v \in <[v]>.
Proof. by apply/hlineP; exists 1; rewrite scale1r. Qed.
Lemma memhZ_line (c : C) v : c *: v \in <[v]>.
Proof. by apply/memhZ/memh_line. Qed.
Lemma memhE_line v U : (v \in U) = (<[v]> `<=` U).
Proof. by simph2v; exact: memvE. Qed.
Lemma hline0 : <[0:H]> = `0`.
Proof. by rewrite hline_def; apply/hspacelfP; rewrite !hsE/= outp0 scaler0. Qed.

Lemma lef_hline v : `|v| <= 1 -> [> v ; v <] ⊑ <[v]>.
Proof.
case E: (v == 0); first by move: E=>/eqP-> _; rewrite outp0 psdf_ge0.
by move=>lv; rewrite hline_def hsE/= lev_pescale// ?outp_ge0// 
  invf_ge1 ?exprn_ile1// exprn_gt0// normr_gt0 E.
Qed.

Lemma lef_outp v U : `|v| <= 1 -> v \in U -> [> v ; v <] ⊑ U.
Proof. move=>/lef_hline; rewrite memhE_line leh_lef; exact: le_trans. Qed.

Lemma hlineD u v : <[u + v]> `<=` <[u]> `|` <[v]>.
Proof. by apply/lehP=>x; move=>/hlineP[k ->]; rewrite scalerDr; apply/memhU; apply/memhZ_line. Qed.
Lemma hlineD_sup u v U : u \in U -> v \in U -> <[u + v]> `<=` U.
Proof. by rewrite -memhE_line; exact: memhD. Qed.
Lemma hlineE u : <[u]> = supph [>u ; u<].
Proof. by []. Qed.
Lemma supphZ (c : C) (A : 'End(H)) : c != 0 -> supph (c *: A) = supph A.
Proof.
by move=>/negPf P; apply/hsC_inj/eqhP=>x; apply/eqb_iff; 
rewrite !memh_suppCE lfunE/= scaler_eq0 P.
Qed.
Lemma hlineZ (c : C) u : c != 0 -> <[c *: u]> = <[u]>.
Proof. 
by move=>P; rewrite !hlineE outpZl outpZr scalerA -normCK; 
  apply/supphZ; rewrite expf_eq0/= normr_eq0.
Qed.
Lemma hline_sum_seq I (r : seq I) (P : pred I) (f : I -> H) U : 
  (forall i, P i -> f i \in U) -> <[\sum_(i <- r | P i) f i]> `<=` U.
Proof.
move=>P1; elim/big_rec : _=>[|x v Px IH]; first by rewrite hline0 le0h.
apply/hlineD_sup. by apply P1. by rewrite memhE_line.
Qed.
Lemma hline_sum (I : finType) (P : pred I) (f : I -> H) U : 
  (forall i, P i -> f i \in U) -> <[\sum_(i | P i) f i]> `<=` U.
Proof. exact: hline_sum_seq. Qed.
Lemma projf_comp_eq0 (U V : 'FP(H)) : U \o V == 0 = (V \o U == 0).
Proof. by rewrite -(inj_eq (@adjf_inj _ _)) linear0 adjf_comp !hermf_adjE/=. Qed.
Lemma projf_comp_eq0P (U V : 'FP(H)) : U \o V = 0 -> (V \o U = 0).
Proof. by move=>/eqP; rewrite projf_comp_eq0=>/eqP. Qed.

Lemma suppU_comp0 (U V : 'FP(H)) : U \o V = 0 -> 
  (supph U `|` supph V)%:VF = U%:VF + V%:VF.
Proof.
move=>P1; have P2: U%:VF + V%:VF \is projlf.
by apply/projlfP; rewrite adjfD !hermf_adjE/= linearDl/= 
  !linearDr/= P1 !projf_idem projf_comp_eq0P// addr0 add0r.
by rewrite hsE/= !supph_projK !hsE -{1}(projfE tt P2) supplfK.
Qed.

Lemma memhUl U V u : u \in U -> u \in U `|` V.
Proof. apply/lehP/lehUl. Qed.
Lemma memhUr U V u : u \in V -> u \in U `|` V.
Proof. apply/lehP/lehUr. Qed.
Lemma memhIl U V u : u \in U `&` V -> u \in U.
Proof. apply/lehP/lehIl. Qed.
Lemma memhIr U V u : u \in U `&` V -> u \in V.
Proof. apply/lehP/lehIr. Qed.

End Extra.
