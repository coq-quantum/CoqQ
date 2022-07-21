(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra perm fingroup.
Require Import forms spectral.
From mathcomp.analysis Require Import reals.
From mathcomp.real_closed Require Import complex.

Require Import mcextra mxpred hermitian mxtopology lfundef quantum hspace.
Import Order.LTheory GRing.Theory Num.Theory.
Import Vector.InternalTheory.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(******************************************************************************)
(* This file provide the Module of ihbFinType, the inhabited finite type      *)
(*   it is the basic type of quantum variables, since we only conside finite  *)
(*   case. It is also required to have at least one element, the witness, to  *)
(*   ensure that the corresponding Hilbert space is non-degenerate            *)
(* Each ihbFinType T is associated with a Hilbert space 'Hs T, the space has  *)
(*   the dimension exactly as #|T|. t2tv (t : T) (notation ''t) provide the   *)
(*   computational basis of 'Hs T, t2tv is also canonical as 'ONB(T;'Hs T),   *)
(*   the index is T itself.                                                   *)
(* Computation : to compute simple types directly, such as 'Hs bool, we give  *)
(*   the way to build a vector/linear function of 'Hs T directly from T -> C  *)
(*   or T -> T -> C. (I don't know if matrix can be calculated directly or    *)
(*   not, and if it is possible, then remove this construction                *)
(* We provide canonical structure of ihbFinType : bool, ordinal number,       *)
(*   product type, tuple, ffun and dffun                                      *)
(* For compositional type (prod, tuple, ffun, dffun), we provide the way to   *)
(*   build vect/lfun for them from single element. That is,                   *)
(*   ⊗v : 'Hs T -> 'Hs T -> 'Hs (T * T)                                      *)
(*   ⊗f : 'End[T] -> 'End[T] -> 'End[T * T]   'End[T] is 'End('Hs T)         *)
(*   tentv_tuple : n.-tuple 'Hs T -> 'Hs (n.-tuple T)                         *)
(*   tentf_tuple : n.-tuple 'End[T] -> 'End[n.-tuple T]                       *)
(*   tentv_ffun : F -> 'Hs T -> 'Hs ({ffun F -> T})                           *)
(*   tentf_ffun : F -> 'End[T] -> 'End[{ffun F -> T}]                         *)
(*   tentv_dffun : forall i : F, 'Hs (T i) -> 'Hs ({dffun forall i : F, T i}) *)
(*   tentv_dffun : forall i : F, 'End[T i] -> 'End[{dffun forall i : F, T i}] *)
(*     ffun/dffun has more canonical predicate than tuple (tuple suffers from *)
(*     type coercion problem), but tuple can be used for induction proofs     *)
(* swaptf over 'Hs (T1 * T2)  and  permtf over 'Hs (n.-tuple T) are given     *)
(******************************************************************************)

Module Inhabited.
Section ClassDef.
Record class_of T := Class {
  base : Choice.class_of T;
  witness : T
}.
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (x : T) :=
  fun bT b & phant_id (Choice.class bT) b =>
  Pack (@Class T b x) T.

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation ihbType := type.
Notation IhbType T m := (@pack T m _ _ id).
Notation "[ 'ihbType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ihbType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ihbType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ihbType'  'of'  T ]") : form_scope.
End Exports.
End Inhabited.

Export Inhabited.Exports.

(* -------------------------------------------------------------------- *)
Definition witness_of (T : ihbType) & phant T := nosimpl
  (Inhabited.witness (Inhabited.class T)).

Notation witness T := (witness_of (Phant T)).

(* -------------------------------------------------------------------- *)
Canonical unit_ihbType := Eval hnf in IhbType unit tt.
Canonical nat_ihbType := Eval hnf in IhbType nat 0%N.
Canonical bool_ihbType := Eval hnf in IhbType bool true.

(* -------------------------------------------------------------------- *)
Canonical prod_ihbType (T U : ihbType) :=
  Eval hnf in IhbType (T * U)%type (witness T, witness U).

(* -------------------------------------------------------------------- *)
Canonical int_ihbType := Eval hnf in IhbType int 0.

(* -------------------------------------------------------------------- *)
Canonical seq_ihbType (T:ihbType) := 
   Eval hnf in IhbType (seq.seq T) [::].
Canonical tuple_ihbType n (T:ihbType) :=
   Eval hnf in IhbType (n.-tuple T) (nseq_tuple n (witness T)).
Canonical real_ihbType (R:realType) := Eval hnf in IhbType R 0.
Canonical complex_ihbType := Eval hnf in IhbType C 0.

(* -------------------------------------------------------------------- *)
Module FinInhabited.
Section ClassDef.

Record class_of T := Class {
  base : Finite.class_of T;
  fwitness : T;
}.

Local Coercion base : class_of >-> Finite.class_of.
Definition base2 T (cT : class_of T) : Inhabited.class_of T :=
  @Inhabited.Class _ (@base T cT) (@fwitness T cT).
Local Coercion base2 : class_of >-> Inhabited.class_of.

Structure type : Type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (x : T) :=
  fun bT b & phant_id (Finite.class bT) b =>
  Pack (@Class T b x) T.

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition finType := @Finite.Pack cT xclass.
Definition ihbType := @Inhabited.Pack cT xclass cT.
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Finite.class_of.
Coercion base2 : class_of >-> Inhabited.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Canonical ihbType.
Notation ihbFinType := type.
Notation IhbFinType T m := (@pack T m _ _ id).
Notation "[ 'ihbFinType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ihbFinType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ihbFinType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ihbFinType'  'of'  T ]") : form_scope.
End Exports.
End FinInhabited.

Export FinInhabited.Exports.

(* -------------------------------------------------------------------- *)
Canonical unit_ihbFinType := Eval hnf in IhbFinType unit tt.
Canonical bool_ihbFinType := Eval hnf in IhbFinType bool true.
Canonical ordinal_ihbFinType n := Eval hnf in IhbFinType 'I_n.+1 ord0.
Canonical option_ihbFinType (F: finType) := Eval hnf in IhbFinType (option F) None.

(* -------------------------------------------------------------------- *)
Canonical prod_ihbFinType (T U : ihbFinType) :=
  Eval hnf in IhbFinType (T * U)%type (witness T, witness U).
Canonical tuple_ihbFinType n (T : ihbFinType) :=
  Eval hnf in IhbFinType (n.-tuple T) (nseq_tuple n (witness T)).
Canonical ffun_ihbFinType (F : finType) (T : ihbFinType) :=
  Eval hnf in IhbFinType {ffun F -> T} [ffun=> witness T].
Canonical dffun_ihbFinType (F : finType) (T : forall i : F, ihbFinType) :=
  Eval hnf in IhbFinType {dffun forall i : F, T i} [ffun i => witness (T i)].

Section DefaultChsType.
Variable (T: ihbFinType).

Let H := [vectType C of {ffun T -> C^o}].

Definition ddotp (x y : H) := dotmx (v2r x)^*m (v2r y)^*m.

Lemma ddotpE x y : ddotp x y = \sum_i ((v2r x) 0 i)^* * ((v2r y) 0 i).
Proof.
rewrite /ddotp /dotmx /form_of_matrix/= mulmx1 /mxtrace big_ord1 mxE.
apply eq_bigr=>i _. by rewrite !mxE /conjCfun conjCK.
Qed.

Lemma ge0_ddotp v : 0 <= ddotp v v.
Proof. exact: dnorm_ge0. Qed.

Lemma ddotp_eq0 v : (ddotp v v == 0) = (v == 0).
Proof. 
by rewrite dnorm_eq0 -(inj_eq (@conjmx_inj _ _ _)) conjmxK 
    -(inj_eq (@r2v_inj _ _)) v2rK !linear0.
Qed.

Lemma conj_ddotp u v : (ddotp u v)^* = ddotp v u.
Proof.
rewrite !ddotpE linear_sum/=. apply eq_bigr=>i _.
by rewrite rmorphM/= conjCK mulrC.
Qed.

Lemma linear_ddotp u : linear_for *%R (ddotp u).
Proof.
move=>c v w; rewrite !ddotpE mulr_sumr -big_split.
apply eq_bigr=>i _; by rewrite linearP/= !mxE mulrDr !mulrA [_ * c]mulrC.
Qed.

Definition default_hermitianMixin :=
  @HermitianMixin H _ ge0_ddotp ddotp_eq0 conj_ddotp linear_ddotp.
Canonical default_hermitianType := HermitianType default_hermitianMixin.

Lemma ddotp_chE i j :
    [< r2v (delta_mx 0 i) : H; r2v (delta_mx 0 j) >] = (i == j)%:R.
Proof.
rewrite /dotp/= ddotpE !r2vK (bigD1 i)// big1/=.
by move=>k /negPf nki; rewrite mxE eqxx nki conjC0 mul0r.
by rewrite !mxE !eqxx conjC1 mul1r addr0.
Qed.

Lemma ihb_dim_cast: #|T| = Vector.dim H.
Proof. by rewrite /Vector.dim/= /Vector.dim/= muln1. Qed.

Lemma ihb_dim_proper : (Vector.dim H > 0)%N.
Proof. move: (max_card (pred1 (witness T))); by rewrite ihb_dim_cast card1. Qed.

Lemma ihb_card_gt0 : (0 < #|T|)%N.
Proof. by rewrite ihb_dim_cast ihb_dim_proper. Qed.

Lemma ihb_card_gtr0 (R : numDomainType) : 0 < (#|T|%:R : R).
Proof. by rewrite ltr0n ihb_card_gt0. Qed.

Lemma ihb_card_neq0 (R : numDomainType) : (#|T|%:R : R) != 0.
Proof. apply/lt0r_neq0/ihb_card_gtr0. Qed.

Definition ihb_chsMixin := ChsMixin ddotp_chE ihb_dim_proper.
Canonical ihb_chsType := Eval hnf in ChsType ihb_chsMixin.

End DefaultChsType.

Definition hspace_of (T : ihbFinType) (phT : phant T) := T.
Notation "''Hs' T" := (ihb_chsType (hspace_of (Phant T))) (at level 8, T at level 2, format "''Hs'  T").
(* Notation "''Hs' T" := (ihb_chsType [ihbFinType of T]) (at level 8, T at level 2, format "''Hs'  T"). *)
Notation "''Hom[' T1 , T2 ]" := ('Hom('Hs T1, 'Hs T2)) (at level 8, format "''Hom[' T1 ,  T2 ]").
Notation "''End[' T ]" := ('End('Hs T)) (at level 8, format "''End[' T ]").
Notation "x %:V" := (x : 'Hs _) 
  (at level 2, left associativity, format "x %:V") : lfun_scope.

Section DefaultChsTypeTheory.
Variable (T : ihbFinType).

Definition mv2tv (f : T -> C) : 'Hs T :=
  r2v (\row_ i f (enum_val (cast_ord (esym (@ihb_dim_cast T)) i))).
Definition tv2mv (v : 'Hs T) : T -> C :=
  (fun t => v2r v 0 (cast_ord (@ihb_dim_cast T) (enum_rank t))).

Lemma mv2tvK f : tv2mv (mv2tv f) =1 f.
Proof.
by move=>x; rewrite /tv2mv /mv2tv r2vK mxE cast_ord_comp cast_ord_id enum_rankK.
Qed.

Lemma tv2mvK : cancel tv2mv mv2tv.
Proof.
move=>x; rewrite /tv2mv /mv2tv; apply/v2r_inj/matrixP=>i j.
by rewrite r2vK mxE ord1 enum_valK cast_ord_comp cast_ord_id. 
Qed.

Lemma mv2tvP f g : mv2tv f = mv2tv g <-> f =1 g.
Proof. 
split=>P. by move=>i; rewrite -mv2tvK P mv2tvK.
by apply/v2r_inj/matrixP=>i j; rewrite /mv2tv !r2vK !mxE P. 
Qed.
Lemma tv2mvP f g : tv2mv f =1 tv2mv g <-> f = g.
Proof. by rewrite -mv2tvP !tv2mvK. Qed.

(* if needed, add function's here *)
Definition mx2tf (f : T -> T -> C) : 'End('Hs T) :=
  Vector.Hom (\matrix_(i,j) f (enum_val (cast_ord (esym (@ihb_dim_cast T)) j))
  (enum_val (cast_ord (esym (@ihb_dim_cast T)) i))).
Definition tf2mx (f : 'End('Hs T)) : T -> T -> C :=
  (fun t1 t2 : T => f2mx f (cast_ord (@ihb_dim_cast T) (enum_rank t2)) 
    (cast_ord (@ihb_dim_cast T) (enum_rank t1))).

Lemma mx2tfK f : tf2mx (mx2tf f) =2 f.
Proof.
move=>x y. rewrite /mx2tf /tf2mx.
by rewrite mxE !cast_ord_comp !cast_ord_id !enum_rankK.
Qed.

Lemma tf2mxK : cancel tf2mx mx2tf.
Proof.
move=>x; rewrite /mx2tf /tf2mx; apply/f2mx_inj/matrixP=>i j.
by rewrite !mxE/= !enum_valK !cast_ord_comp !cast_ord_id. 
Qed.

Lemma mx2tfP f g : mx2tf f = mx2tf g <-> f =2 g.
Proof. 
split=>P. by move=>i j; rewrite -mx2tfK P mx2tfK.
by apply/f2mx_inj/matrixP=>i j; rewrite /mx2tf/= !mxE P. 
Qed.
Lemma tf2mxP f g : tf2mx f =2 tf2mx g <-> f = g.
Proof. by rewrite -mx2tfP !tf2mxK. Qed.

(* we do not map T to vectType, so we need to redefine the following things *)
(* provide the way to translate lfun to ffun *)
(* further, we only want to give a computation, 
so do not need to define any algebraic structure*)
Definition funf_add (f1 f2 : T -> T -> C) : T -> T -> C :=
  (fun x y : T => f1 x y + f2 x y).
Definition funf_opp (f : T -> T -> C) : T -> T -> C :=
  (fun x y : T => - f x y).
Definition funf_scale (c : C) (f : T -> T -> C) : T -> T -> C :=
  (fun x y : T => c * f x y).
Definition funf_comp (f1 f2 : T -> T -> C) : T -> T -> C :=
  (fun x y : T => \sum_t f1 x t * f2 t y).
Definition funf_adj (f : T -> T -> C) : T -> T -> C :=
  (fun x y => (f y x)^*).
Definition funf_tr (f : T -> T -> C) : T -> T -> C :=
  (fun x y => f y x).
Definition funf_conj (f : T -> T -> C) : T -> T -> C :=
  (fun x y => (f x y)^*).
Definition funf_apply (f : T -> T -> C) (v : T -> C) :=
  (fun t1 => \sum_t2 (f t1 t2 * v t2) ).
Definition funv_add (f1 f2 : T -> C) : T -> C :=
  (fun x : T => f1 x + f2 x).
Definition funv_opp (f : T -> C) : T -> C :=
  (fun x : T => - f x).
Definition funv_scale (c : C) (f : T -> C) : T -> C :=
  (fun x : T => c * f x).
Definition funv_conj (f : T -> C) : T -> C :=
  (fun x : T => (f x)^*).
Definition funv_dot (u v : T -> C) : C :=
  \sum_i (u i)^* * (v i).
Definition funv_out (u v : T -> C) :=
  (fun x y => (u x) * (v y)^*).

Lemma mx2tf_add (f g : T -> T -> C) : (mx2tf f) + (mx2tf g) = mx2tf (funf_add f g).
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE linearD/= !mxE. Qed.
Lemma mx2tf_opp (f : T -> T -> C) : - (mx2tf f) = mx2tf (funf_opp f).
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE linearN/= !mxE. Qed.
Lemma mx2tf_scale (c : C) (f : T -> T -> C) : c *: (mx2tf f) = mx2tf (funf_scale c f).
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE linearZ/= !mxE. Qed.
Lemma mx2tf_comp (f g : T -> T -> C) : (mx2tf f) \o (mx2tf g) = mx2tf (funf_comp f g).
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite !mxE f2mx_comp mxE.
under eq_bigr do rewrite !mxE mulrC. symmetry. apply: reindex. apply bij_enum_ord. 
Qed.
Lemma mx2tf_adj (f : T -> T -> C) : (mx2tf f)^A = mx2tf (funf_adj f).
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE. Qed.
Lemma mx2tf_tr (f : T -> T -> C) : ((mx2tf f)^T)%VF = mx2tf (funf_tr f).
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE. Qed.
Lemma mx2tf_conj (f : T -> T -> C) : (mx2tf f)^C = mx2tf (funf_conj f).
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE. Qed.
Lemma mx2tf_apply (f : T -> T -> C) (v : T -> C) :
  (mx2tf f) (mv2tv v) = mv2tv (funf_apply f v).
Proof.
rewrite unlock/= /mv2tv; apply/v2r_inj/matrixP=>i j; rewrite !r2vK !mxE.
under eq_bigr do rewrite !mxE mulrC. symmetry. apply: reindex. apply bij_enum_ord.
Qed.
Lemma mv2tv_add (f g : T -> C) : (mv2tv f) + (mv2tv g) = mv2tv (funv_add f g).
Proof. by apply/v2r_inj/matrixP=>i j; rewrite linearD /mv2tv/= !r2vK !mxE. Qed.
Lemma mv2tv_opp (f : T -> C) : - (mv2tv f) = mv2tv (funv_opp f).
Proof. by apply/v2r_inj/matrixP=>i j; rewrite linearN /mv2tv/= !r2vK !mxE. Qed.
Lemma mv2tv_scale (c : C) (f : T -> C) : c *: (mv2tv f) = mv2tv (funv_scale c f).
Proof. by apply/v2r_inj/matrixP=>i j; rewrite linearZ /mv2tv/= !r2vK !mxE. Qed.
Lemma mv2tv_conj (f : T -> C) : (mv2tv f)^*v = mv2tv (funv_conj f).
Proof. by apply/v2r_inj/matrixP=>i j; rewrite /mv2tv !r2vK !mxE. Qed.
Lemma mv2tv_dot (u v : T -> C) : [<mv2tv u; mv2tv v>] = funv_dot u v.
Proof.
rewrite dotp_mulmx /mv2tv !r2vK mxE /funv_dot; under eq_bigr do rewrite !mxE.
symmetry; apply: reindex; apply bij_enum_ord.
Qed.
Lemma mv2tv_out (u v : T -> C) : [>mv2tv u; mv2tv v<] = mx2tf (funv_out u v).
Proof.
apply/lfunP=>w; rewrite -(tv2mvK w) outpE mv2tv_dot mx2tf_apply mv2tv_scale.
apply/mv2tvP=>i. rewrite /funv_scale /funv_dot /funv_out /funf_apply.
by rewrite mulrC mulr_sumr; apply eq_bigr=>j _; rewrite mulrA.
Qed.
Definition funf_scale1 : T -> T -> C := (fun i j : T => (i == j)%:R).
Lemma mx2tf1 : \1 = mx2tf funf_scale1.
Proof.
apply/tf2mxP=>t1 t2; rewrite mx2tfK /tf2mx f2mx1 mxE/=.
by rewrite /funf_scale1 -enum_ord_eq cast_ord_comp cast_ord_id enum_rankK eq_sym.
Qed.
Lemma mx2tf0 : 0 = mx2tf (fun _ _=>0).
Proof. by apply/tf2mxP=>i j; rewrite /tf2mx linear0/= !mxE. Qed.
Lemma mv2tv0 : 0 = mv2tv (fun _=>0).
Proof. by apply/tv2mvP=>i; rewrite /tv2mv /mv2tv r2vK linear0/= !mxE. Qed.

Definition tf2mxE := (mx2tf_add, mx2tf_opp, mx2tf_scale, mx2tf_comp, mx2tf_adj, 
mx2tf_tr, mx2tf_conj, mx2tf_apply, mv2tv_add, mv2tv_opp, mv2tv_scale, mv2tv_conj, 
mx2tf1, mx2tf0, mv2tv0, mv2tv_dot, mv2tv_out).

Definition t2tv (t : T) : 'Hs T :=
    mv2tv (fun x => (x == t)%:R).

Notation "'''' b" := (t2tv b) (at level 2, format "'''' b").

(* t2tv x gives an ONB basis, i.e. computational basis *)
Lemma t2tv_dot (t1 t2 : T) : [< ''t1 ; ''t2 >] = (t1 == t2)%:R.
Proof.
by rewrite /t2tv mv2tv_dot /funv_dot (bigD1 t1)//= big1=>[t3/negPf nt|];
rewrite ?nt ?conjC0 ?mul0r// eqxx conjC1 mul1r addr0.
Qed.
Lemma t2tv_ns t : [< ''t ; ''t >] == 1.
Proof. by rewrite t2tv_dot eqxx. Qed.
Canonical t2tv_nsType t := NSType (@t2tv_ns t).
Lemma t2tv_conj (t : T) : (''t)^*v = ''t.
Proof. by rewrite /t2tv mv2tv_conj; apply/mv2tvP=>x; rewrite /funv_conj conjC_nat. Qed.

Lemma ihb_dim : #|T| = Vector.dim ('Hs T).
Proof. by rewrite ihb_dim_cast. Qed.
Canonical t2tv_ponbasis := PONBasis t2tv_dot.
Canonical t2tv_onbasis := ONBasis t2tv_dot ihb_dim.

(* computational measurement *)
Definition tmeas t : 'End('Hs T) := [> ''t ; ''t <].
Lemma tmeasE t : tmeas t = [> ''t ; ''t <]. Proof. by []. Qed.
Lemma tmeas_tp : trace_presv tmeas.
rewrite/trace_presv -(sumonb_out t2tv_onbasis); apply/eqP; apply eq_bigr=>t _.
by rewrite/=/tmeas adj_outp outp_comp onb_dot eqxx scale1r.
Qed.
Canonical tmeas_qmType := QMType tmeas_tp.
Canonical tmeas_tnType := Eval hnf in [TN of tmeas as [QM of tmeas]].

Definition deltaft (t1 t2 : T) : 'End('Hs T) := [> ''t1 ; ''t2 <].
Lemma deltaftE (t1 t2 : T) : deltaft t1 t2 = [> ''t1 ; ''t2 <].
Proof. by []. Qed.

Lemma deltaftM (t1 t2 t3 t4 : T) :
  deltaft t1 t2 \o deltaft t3 t4 = (t2 == t3)%:R *: deltaft t1 t4.
Proof. by rewrite /deltaft outp_comp t2tv_dot. Qed.

Lemma deltaft_adj (t1 t2 : T) : (deltaft t1 t2)^A = deltaft t2 t1.
Proof. by rewrite /delta_lf adj_outp. Qed.
Lemma deltaft_tr (t1 t2 : T) : (deltaft t1 t2)^T = deltaft t2 t1.
Proof. by rewrite /deltaft tr_outp !t2tv_conj. Qed.
Lemma deltaft_conj (t1 t2 : T) : (deltaft t1 t2)^C = deltaft t1 t2.
Proof. by rewrite /deltaft conj_outp !t2tv_conj. Qed.

Lemma mx2tf_coord f t1 t2 : [< ''t1 ; mx2tf f ''t2 >] = f t1 t2.
Proof.
by rewrite mx2tf_apply /t2tv mv2tv_dot /funv_dot /funf_apply 
  (bigD1 t1)//= (bigD1 t2)//= !big1 =>[i/negPf ni|i/negPf ni|]; 
  rewrite ?ni ?mulr0// ?conjC0 ?mul0r// !eqxx mulr1 conjC1 mul1r !addr0.
Qed.

Lemma mx2tf_dec (f : T -> T -> C) : mx2tf f =
  \sum_t1\sum_t2 f t1 t2 *: deltaft t1 t2.
Proof.
rewrite [LHS](onb_lfun2id t2tv_onbasis)/= exchange_big/=.
by under eq_bigr do under eq_bigr do rewrite mx2tf_coord.
Qed.

End DefaultChsTypeTheory.

Ltac unfold_funfv := rewrite /funf_add /funf_opp /funf_scale /funf_comp
  /funf_adj /funf_tr /funf_conj /funf_apply /funv_add /funv_opp /funv_scale
  /funv_conj /funv_dot /funv_out /funf_scale1.

Arguments funf_scale1 {T}.

Notation "'''' b" := (t2tv b) (at level 2, format "'''' b").

Arguments t2tv_onbasis {T}.
Arguments tmeas {T}.

Section TypeVectTensor.
Variable (T1 T2 : ihbFinType).

Definition idx_pair1 (i : 'I_(Vector.dim 'Hs (T1 * T2))) : 'I_(Vector.dim 'Hs T1)
  := cast_ord (ihb_dim_cast T1) (enum_rank (enum_val (cast_ord (esym (ihb_dim_cast _)) i)).1).
Definition idx_pair2 (i : 'I_(Vector.dim 'Hs (T1 * T2))) : 'I_(Vector.dim 'Hs T2)
  := cast_ord (ihb_dim_cast T2) (enum_rank (enum_val (cast_ord (esym (ihb_dim_cast _)) i)).2).
Definition idx_pair (i : 'I_(Vector.dim 'Hs T1)) (j : 'I_(Vector.dim 'Hs T2))
  : 'I_(Vector.dim 'Hs (T1 * T2)) := cast_ord (ihb_dim_cast _) (enum_rank
  ((enum_val (cast_ord (esym (ihb_dim_cast _)) i)), (enum_val (cast_ord (esym (ihb_dim_cast _)) j)))).

Lemma idx_pair1K i j : idx_pair1 (idx_pair i j) = i.
Proof.
by rewrite /idx_pair1 /idx_pair cast_ord_comp cast_ord_id 
  enum_rankK/= enum_valK cast_ord_comp cast_ord_id.
Qed.
Lemma idx_pair2K i j : idx_pair2 (idx_pair i j) = j.
Proof.
by rewrite /idx_pair2 /idx_pair cast_ord_comp cast_ord_id 
  enum_rankK/= enum_valK cast_ord_comp cast_ord_id.
Qed.
Lemma idx_pairK i : idx_pair (idx_pair1 i) (idx_pair2 i) = i.
Proof.
by rewrite /idx_pair /idx_pair1 /idx_pair2 !cast_ord_comp !cast_ord_id 
  !enum_rankK -surjective_pairing enum_valK cast_ord_comp cast_ord_id.
Qed.

Definition tentv (u : 'Hs T1) (v : 'Hs T2) : 'Hs (T1 * T2) :=
  r2v (\row_i ((v2r u ord0 (idx_pair1 i)) * (v2r v ord0 (idx_pair2 i)))).

Lemma linear_tentv v1: linear (tentv v1).
Proof.
move=>a x y; apply/v2r_inj/matrixP=>i j.
by rewrite linearP/= !r2vK !mxE linearP/= !mxE mulrDr !mulrA [a * _]mulrC.
Qed.
Canonical tentv_additive v1 := Additive (linear_tentv v1).
Canonical tentv_linear v1 := Linear (linear_tentv v1).
Definition tentvr v2 := tentv^~ v2.
Lemma linear_tentvr v2 : linear (tentvr v2).
Proof.
move=>a x y; apply/v2r_inj/matrixP=>i j.
by rewrite linearP/= !r2vK !mxE linearP/= !mxE mulrDl !mulrA.
Qed.
Canonical tentvr_additive v2 := Additive (linear_tentvr v2).
Canonical tentvr_linear v2 := Linear (linear_tentvr v2).
Canonical tentv_rev := [revop (tentvr) of (tentv)].
Canonical tentv_is_bilinear := [bilinear of (tentv)].

Lemma tentv_t2tv (t1 : T1) (t2 : T2) :
  tentv ''t1 ''t2 = ''(t1,t2).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite /tentv r2vK /t2tv/mv2tv !r2vK !mxE.
by rewrite /idx_pair1/= /idx_pair2 !cast_ord_comp !cast_ord_id !enum_rankK
  -natrM mulnb -pair_eqE//=.
Qed.

Lemma tentv_t2tvV (t : T1 * T2) : ''t = tentv ''(t.1) ''(t.2).
Proof. by rewrite tentv_t2tv -surjective_pairing. Qed.

Lemma tentv_dot v1 v2 u1 u2 : 
  [< tentv v1 v2 ; tentv u1 u2 >] = [< v1 ; u1 >] * [< v2 ; u2 >].
Proof.
rewrite !dotp_mulmx !mxE mulr_suml. under [RHS]eq_bigr do rewrite mulr_sumr.
rewrite pair_big/= (reindex (fun i=>(idx_pair1 i,idx_pair2 i)))/=; last first.
by apply eq_bigr=>k _; rewrite/=/tentv !r2vK !mxE rmorphM mulrACA !ord1.
exists (fun i=> idx_pair i.1 i.2)=>/=x _; 
by rewrite ?idx_pairK// idx_pair1K idx_pair2K -surjective_pairing.
Qed.

Lemma tentv_norm u v : `|tentv u v| = `|u| * `|v|.
Proof. by rewrite hnormE tentv_dot sqrtCM ?nnegrE// dotp_norm exprn_ge0. Qed.

Definition tentv_fun (F G : finType) (f : F -> 'Hs T1) (g : G -> 'Hs T2) :=
  (fun i => tentv (f i.1) (g i.2)).
Lemma tentv_ponb (F G : finType) (f : 'PONB(F;'Hs T1)) (g : 'PONB(G;'Hs T2)) i j :
  [< tentv_fun f g i ; tentv_fun f g j >] = (i == j)%:R.
Proof.
case: i; case: j=>i i' j j'.
rewrite /tentv_fun/= tentv_dot !ponb_dot -pair_eqE/=.
by do 2 case: eqP=>_; rewrite ?mulr1 ?mulr0.
Qed.
Lemma tentv_onb (F G : finType) (f : 'ONB(F;'Hs T1)) (g : 'ONB(G;'Hs T2)) i j :
  [< tentv_fun f g i ; tentv_fun f g j >] = (i == j)%:R.
Proof. exact: tentv_ponb. Qed.
Lemma tentv_card (F G : finType) (f : 'ONB(F;'Hs T1)) (g : 'ONB(G;'Hs T2)) :
  #|{: F * G}| = Vector.dim ('Hs (T1 * T2)).
Proof. by rewrite card_prod (onb_card f) (onb_card g) -!ihb_dim_cast/= card_prod. Qed.
Canonical tentv_ponbasis F G f g := PONBasis (@tentv_ponb F G f g).
Canonical tentv_onbasis F G f g := ONBasis (@tentv_onb F G f g) (tentv_card f g).
Definition t2tv2_onbasis := tentv_onbasis t2tv_onbasis t2tv_onbasis.

Lemma intro_tvl (u v : 'Hs(T1 * T2)) : 
  (forall u1 u2, [<tentv u1 u2 ; u >] = [<tentv u1 u2 ; v >]) <-> u = v.
Proof. split=>[H|->//]; apply/(intro_onbl t2tv2_onbasis)=>/= i; apply H. Qed.

Lemma intro_tvr (u v : 'Hs(T1 * T2)) : 
  (forall u1 u2, [<u ; tentv u1 u2 >] = [< v ; tentv u1 u2 >]) <-> u = v.
Proof. split=>[H|->//]; apply/(intro_onbr t2tv2_onbasis)=>/= i; apply H. Qed.

Lemma tentv_conj u v : (tentv u v)^*v = tentv (u^*v) (v^*v).
Proof. by apply/v2r_inj/matrixP=>i j; rewrite !r2vK !mxE rmorphM. Qed.

Lemma tentv_ns (u : 'NS('Hs T1)) (v : 'NS('Hs T2)) :
  [< tentv u v ; tentv u v >] == 1%:R.
Proof. by rewrite tentv_dot !ns_dot mulr1. Qed.
Canonical tentv_nsType u v := NSType (@tentv_ns u v).

Lemma tentv_eq0 u v : tentv u v == 0 = (u == 0) || (v == 0).
Proof. by rewrite -!dotp_eq0 tentv_dot mulf_eq0. Qed.

Lemma tentv0 u : tentv u 0 = 0. Proof. exact: linear0r. Qed.
Lemma ten0tv v : tentv 0 v = 0. Proof. exact: linear0l. Qed.

End TypeVectTensor.

Notation "u '⊗t' v" := (tentv u v) (at level 45, left associativity) : lfun_scope.
Arguments t2tv2_onbasis {T1 T2}.

Section TypeLfunTensor.
Variable (S1 S2 T1 T2: ihbFinType).

Definition tentf (f : 'Hom[S1, T1]) (g : 'Hom[S2, T2]) : 'Hom[S1 * S2, T1 * T2] :=
  Vector.Hom (\matrix_(i, j) ((f2mx f (idx_pair1 i) (idx_pair1 j)) * 
    (f2mx g (idx_pair2 i) (idx_pair2 j)))).

Lemma linear_tentf v1: linear (tentf v1).
Proof.
by move=>a v w; apply/f2mx_inj/matrixP=>i j; 
rewrite linearP/= !mxE linearP !mxE/= mulrDr !mulrA [a * _]mulrC.  
Qed.
Canonical tentf_additive v1 := Additive (linear_tentf v1).
Canonical tentf_linear v1 := Linear (linear_tentf v1).
Definition tentfr v2 := tentf^~ v2.
Lemma linear_tentfr v2 : linear (tentfr v2).
Proof.
by move=>a v w; apply/f2mx_inj/matrixP=>i j; 
rewrite linearP/= !mxE linearP !mxE/= mulrDl !mulrA.
Qed.
Canonical tentfr_additive v2 := Additive (linear_tentfr v2).
Canonical tentfr_linear v2 := Linear (linear_tentfr v2).
Canonical tentf_rev := [revop (tentfr) of (tentf)].
Canonical tentf_is_bilinear := [bilinear of (tentf)].

Lemma tentf0 f : tentf f 0 = 0. Proof. exact: linear0r. Qed.
Lemma ten0tf g : tentf 0 g = 0. Proof. exact: linear0l. Qed.

Lemma tentf_apply f1 f2 v1 v2 : tentf f1 f2 (v1 ⊗t v2) = f1 v1 ⊗t f2 v2.
Proof.
apply/v2r_inj/matrixP=>i j; rewrite unlock/= !r2vK !mxE mulr_suml.
under [RHS]eq_bigr do rewrite mulr_sumr.
rewrite pair_big/= (reindex (fun i=>(idx_pair1 i,idx_pair2 i)))/=; last first.
by apply eq_bigr=>k _; rewrite/= !mxE mulrACA.
exists (fun i=> idx_pair i.1 i.2)=>/=x _; 
by rewrite ?idx_pairK// idx_pair1K idx_pair2K -surjective_pairing.
Qed.

Lemma intro_tv (f g : 'Hom('Hs (S1 * S2), 'Hs (T1 * T2))) :
  (forall u1 u2, f (u1 ⊗t u2) = g (u1 ⊗t u2)) <-> f = g.
Proof. by split=>[H|->//]; apply/(intro_onb t2tv2_onbasis)=>/= i; apply H. Qed.

Lemma tentv_out u1 u2 v1 v2 : 
  tentf [> u1 ; v1 <] [> u2 ; v2 <] = [> u1 ⊗t u2; v1 ⊗t v2 <].
Proof.
by apply/intro_tv=>u v; rewrite tentf_apply 
  !outpE linearZl linearZr/= scalerA tentv_dot.
Qed.

Lemma tentf_conj f g : (tentf f g)^C = tentf f^C g^C.
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE rmorphM. Qed.

End TypeLfunTensor.

Notation "f '⊗f' g" := (tentf f g) (at level 45, left associativity) : lfun_scope.

Lemma tentf_comp (S1 S2 S3 T1 T2 T3: ihbFinType) (f1 : 'Hom[S1,S2]) (f2 : 'Hom[T1,T2])
  (g1 : 'Hom[S3,S1]) (g2 : 'Hom[T3,T1]) :
  f1 ⊗f f2 \o g1 ⊗f g2 = (f1 \o g1) ⊗f (f2 \o g2).
Proof. by apply/intro_tv=>u v; rewrite lfunE/= !tentf_apply !lfunE. Qed.

Lemma tentf_tr (T1 T2 S1 S2 : ihbFinType) (f : 'Hom[T1,T2]) (g : 'Hom[S1,S2]) : 
  ((f ⊗f g)^T = f^T ⊗f g^T)%VF.
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE. Qed.

Lemma tentf_adj (T1 T2 S1 S2 : ihbFinType) (f : 'Hom[T1,T2]) (g : 'Hom[S1,S2]) : 
  (f ⊗f g)^A = f^A ⊗f g^A.
Proof. by rewrite adjfCT tentf_conj tentf_tr -!adjfCT. Qed.

Section TypeTensorTheory.
Variable (T1 T2 : ihbFinType).
Implicit Type (x : 'End('Hs T1)) (y : 'End('Hs T2)).

Lemma tentf11 : \1 ⊗f \1 = (\1 : 'End('Hs (T1 * T2))).
Proof. by apply/intro_tv=>u v; rewrite tentf_apply !lfunE/=. Qed.

Lemma tentf_ge0 x y :
  (0 :'End(_)) ⊑ x -> (0 :'End(_)) ⊑ y -> (0 :'End(_)) ⊑ x ⊗f y.
Proof.
move=>/ge0_form[f1 Pf] /ge0_form[g1 Pg].
by rewrite Pf Pg -tentf_comp -tentf_adj form_ge0.
Qed.

Lemma tentf_eq0 x y : (x ⊗f y == 0) = (x == 0) || (y == 0).
Proof.
apply/Bool.eq_iff_eq_true; split.
move=>/eqP/lfunP P1. case: eqP=>//=; move=>/eqP/lfun_neq0P[v /negPf Pv].
apply/eqP/lfunP=>a; apply/intro_dotl=>b;
move: (P1 (tentv v a))=>/intro_dotl/(_ (tentv (x v) b))/eqP.
by rewrite tentf_apply tentv_dot !lfunE/= !linear0 mulf_eq0 Pv/==>/eqP.
by move=>/orP[/eqP->|/eqP->]; rewrite ?linear0l ?linear0r eqxx.
Qed.

Lemma ptentf_rge0 x y : 
  (0 : 'End(_)) ⊏ x -> ((0 : 'End(_)) ⊑ x ⊗f y) = ((0 : 'End(_)) ⊑ y).
Proof.
move=>/gtf0_pdP[xge0 [v Pv]].
apply/Bool.eq_iff_eq_true; split; last by apply: tentf_ge0=>//.
move/lef_dot=>P1. apply/lef_dot=>u.
move: (P1 (tentv v u)).
by rewrite tentf_apply tentv_dot !lfunE/= !linear0 pmulr_rge0.
Qed.

Lemma ptentf_lge0 y x :
  (0 : 'End(_)) ⊏ y -> ((0 : 'End(_)) ⊑ x ⊗f y) = ((0 : 'End(_)) ⊑ x).
Proof.
move=>/gtf0_pdP[xge0 [v Pv]].
apply/Bool.eq_iff_eq_true; split=>[/lef_dot P1|P1]; last by apply: tentf_ge0.
apply/lef_dot=>u; move: (P1 (tentv u v)).
by rewrite tentf_apply tentv_dot !lfunE/= !linear0 pmulr_lge0.
Qed.

Definition tentf_bregVOrderMixin := 
    bregVOrderMixin tentf_eq0 ptentf_rge0 ptentf_lge0.
Canonical tentf_bregVOrderType := 
  bregVOrderType (@tentf _ _ _ _) tentf_bregVOrderMixin.

Lemma tentf_trlf x y : \Tr (x ⊗f y) = \Tr x * \Tr y.
Proof.
rewrite (onb_trlf t2tv2_onbasis) !(onb_trlf t2tv_onbasis)/=.
rewrite pair_bigV/= mulr_suml; apply eq_bigr=>i _.
rewrite mulr_sumr; apply eq_bigr=>j _.
by rewrite /tentv_fun/= tentf_apply tentv_dot.
Qed. 

Lemma tentf_herm (f : 'FH('Hs T1)) (g : 'FH('Hs T2)) : f ⊗f g \is hermlf.
Proof. by rewrite hermlfE tentf_adj !hermf_adjE. Qed.
Canonical tentf_hermfType f g := HermfType (@tentf_herm f g).
Lemma tentf_psd (f : 'F+('Hs T1)) (g : 'F+('Hs T2)) : f ⊗f g \is psdlf.
Proof. rewrite psdlfE; apply: bregv_ge0; apply/psdf_ge0. Qed.
Canonical tentf_psdfType f g := PsdfType (@tentf_psd f g).
Lemma tentf_den (f : 'FD('Hs T1)) (g : 'FD('Hs T2)) : f ⊗f g \is denlf.
Proof.
apply/denlfP; split; first by apply/tentf_psd.
by rewrite tentf_trlf -(mulr1 1) ler_pmul ?psdf_trlf// denf_trlf.
Qed.
Canonical tentf_denfType f g := DenfType (@tentf_den f g).
Lemma tentf_obs (f : 'FO('Hs T1)) (g : 'FO('Hs T2)) : f ⊗f g \is obslf.
Proof. 
by apply/obslf_lefP; rewrite psdf_ge0; split=>//; 
  rewrite -tentf11 lev_pbreg2 ?psdf_ge0// obsf_le1.
Qed.
Canonical tentf_obsfType f g := ObsfType (@tentf_obs f g).
Lemma tentf_unitary (f : 'FU('Hs T1)) (g : 'FU('Hs T2)) : f ⊗f g \is unitarylf.
Proof. by apply/unitarylfP; rewrite tentf_adj tentf_comp !unitaryf_form tentf11. Qed.
Canonical tentf_unitaryfType f g := UnitaryfType (@tentf_unitary f g).
Lemma tentf_den1 (f : 'FD1('Hs T1)) (g : 'FD1('Hs T2)) : f ⊗f g \is den1lf.
Proof.
apply/den1lfP; split; first by apply/psdf_psd.
by rewrite tentf_trlf !den1f_trlf mul1r.
Qed.
Canonical tentf_den1fType f g := Den1fType (@tentf_den1 f g).
Lemma tentf_proj (f : 'FP('Hs T1)) (g : 'FP('Hs T2)) : f ⊗f g \is projlf.
Proof. by apply/projlfP; rewrite tentf_adj !hermf_adjE/= tentf_comp !projf_idem. Qed.
Canonical tentf_projfType f g := ProjfType (@tentf_proj f g).
Lemma tentf_proj1 (f : 'FP1('Hs T1)) (g : 'FP1('Hs T2)) : f ⊗f g \is proj1lf.
Proof.
apply/proj1lfP; split; first by apply/projf_proj.
by rewrite tentf_trlf !proj1f_trlf mulr1.
Qed.
Canonical tentf_proj1fType f g := Proj1fType (@tentf_proj1 f g).

End TypeTensorTheory.

Section TentvfLinear.
Variable (T1 T2 : ihbFinType).

Lemma tentv00 : tentv 0 0 = (0 : 'Hs (T1 * T2)).
Proof. exact: linear0l. Qed.
Lemma tentvNl (v: 'Hs T2) (u: 'Hs T1) : (-u) ⊗t v = - (u ⊗t v).
Proof. exact: linearNl. Qed.
Lemma tentvBl (w: 'Hs T2) (u v: 'Hs T1) : (u-v) ⊗t w = u ⊗t w - v ⊗t w.
Proof. exact: linearBl. Qed.
Lemma tentvDl (w: 'Hs T2) (u v: 'Hs T1) : (u+v) ⊗t w = u ⊗t w + v ⊗t w.
Proof. exact: linearDl. Qed.
Lemma tentvZl (v: 'Hs T2) (c: C) (u: 'Hs T1) : (c*:u) ⊗t v = c *: (u ⊗t v).
Proof. exact: linearZl. Qed.
Lemma tentvPl (w: 'Hs T2) (c: C) (u v: 'Hs T1) : 
  (c*:u+v) ⊗t w = c *: (u ⊗t w) + v ⊗t w.
Proof. exact: linearPl. Qed.
Lemma tentvMnl (v: 'Hs T2) (u: 'Hs T1) n : (u *+ n) ⊗t v = (u ⊗t v) *+ n.
Proof. exact: linearMnl. Qed.
Lemma tentvMNnl (v: 'Hs T2) (u: 'Hs T1) n : tentv (u *- n) v = (tentv u v) *- n.
Proof. exact: linearMNnl. Qed.
Lemma tentv_suml L r (P : pred L) (F: L -> 'Hs T1) (u: 'Hs T2) : 
  (\sum_(i <- r | P i) F i) ⊗t u = \sum_(i <- r | P i) ((F i) ⊗t u).
Proof. exact: linear_suml. Qed.
Lemma tentvNr (u: 'Hs T1) (v: 'Hs T2) : u ⊗t (-v) = - (u ⊗t v).
Proof. exact: linearNr. Qed.
Lemma tentvBr (w: 'Hs T1) (u v: 'Hs T2) : w ⊗t (u-v) = w ⊗t u - w ⊗t v.
Proof. exact: linearBr. Qed.
Lemma tentvDr (w: 'Hs T1) (u v: 'Hs T2) : w ⊗t (u+v) = w ⊗t u + w ⊗t v.
Proof. exact: linearDr. Qed.
Lemma tentvZr (v: 'Hs T1) (c: C) (u: 'Hs T2) : v ⊗t (c*:u) = c *: (v ⊗t u).
Proof. exact: linearZr. Qed.
Lemma tentvPr (w: 'Hs T1) (c: C) (u v: 'Hs T2) : 
  w ⊗t (c *: u + v) = c *: (w ⊗t u) + (w ⊗t v).
Proof. exact: linearPr. Qed.
Lemma tentvMnr (v: 'Hs T1) (u: 'Hs T2) n : v ⊗t (u *+ n) = (v ⊗t u) *+ n.
Proof. exact: linearMnr. Qed.
Lemma tentvMNnr (v: 'Hs T1) (u: 'Hs T2) n : v ⊗t (u *- n) = (v ⊗t u) *- n.
Proof. exact: linearMNnr. Qed.
Lemma tentv_sumr L r (P : pred L) (u: 'Hs T1) (F: L -> 'Hs T2)  : 
  u ⊗t (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) (u ⊗t (F i)).
Proof. exact: linear_sumr. Qed.

Lemma tentvZS (a : C) (u1 : 'Hs T1) (u2 : 'Hs T2) :
  (a *: u1) ⊗t u2 = u1 ⊗t (a *: u2).
Proof. by rewrite linearZl linearZr. Qed.

Implicit Type (f : 'End[T1]) (g : 'End[T2]).
Lemma tentf00 : tentf 0 0 = (0 : 'End[T1 * T2]).
Proof. exact: linear0r. Qed.
Lemma tentfDl g f1 f2 : (f1 + f2) ⊗f g = (f1 ⊗f g) + (f2 ⊗f g).
Proof. exact: linearDl. Qed.
Lemma tentfDr f g1 g2 : f ⊗f (g1 + g2) = (f ⊗f g1) + (f ⊗f g2).
Proof. exact: linearDr. Qed.
Lemma tentfNl g f : (- f) ⊗f g = - (f ⊗f g).
Proof. exact: linearNl. Qed.
Lemma tentfNr f g : f ⊗f (- g) = - (f ⊗f g).
Proof. exact: linearNr. Qed.
Lemma tentfZl g (c: C) f : (c *: f) ⊗f g = c *: (f ⊗f g).
Proof. exact: linearZl. Qed.
Lemma tentfZr f (c: C) g : f ⊗f (c *: g) = c *: (f ⊗f g).
Proof. exact: linearZr. Qed.
Lemma tentfBl g f1 f2 : (f1 - f2) ⊗f g = f1 ⊗f g - f2 ⊗f g.
Proof. exact: linearBl. Qed.
Lemma tentfBr f g1 g2 : f ⊗f (g1 - g2) = f ⊗f g1 - f ⊗f g2.
Proof. exact: linearBr. Qed.
Lemma tentfPl g (c: C) f1 f2: (c *: f1 + f2) ⊗f g = c *: (f1 ⊗f g) + (f2 ⊗f g).
Proof. exact: linearPl. Qed.
Lemma tentfPr f (c: C) g1 g2 : f ⊗f (c *: g1 + g2) = c *: (f ⊗f g1) + (f ⊗f g2).
Proof. exact: linearPr. Qed.
Lemma tentfMnl g f n : (f *+ n) ⊗f g = (f ⊗f g) *+ n.
Proof. exact: linearMnl. Qed.
Lemma tentfMnr f g n : f ⊗f (g *+ n) = (f ⊗f g) *+ n.
Proof. exact: linearMnr. Qed.
Lemma tentfMNnl g f n : (f *- n) ⊗f g = (f ⊗f g) *- n.
Proof. exact: linearMNnl. Qed.
Lemma tentfMNnr f g n : f ⊗f (g *- n) = (f ⊗f g) *- n.
Proof. exact: linearMNnr. Qed.
Lemma tentf_suml g I r (P: pred I) (E: I -> 'End[T1]) :
 (\sum_(i <- r | P i) E i) ⊗f g = \sum_(i <- r | P i) (E i ⊗f g).
Proof. exact: linear_suml. Qed.
Lemma tentf_sumr f I r (P: pred I) (E: I -> 'End[T2]) :
 f ⊗f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (f ⊗f E i).
Proof. exact: linear_sumr. Qed.

Lemma tentfZS (a : C) f g :
  (a *: f) ⊗f g = f ⊗f (a *: g).
Proof. by rewrite linearZl linearZr. Qed.
End TentvfLinear.

(* tensor subspace *)
Section Tenth.
Variable (T1 T2 : ihbFinType).
Local Open Scope hspace_scope.

Definition tenth (A : {hspace 'Hs T1}) (B : {hspace 'Hs T2}) : {hspace 'Hs (T1 * T2)}
  := HSType (tentf_projfType A B).
Notation "A '`⊗`' B" := (tenth A B) (at level 45, left associativity) : hspace_scope.

Lemma leh_tent2l A : {homo (tenth A) : y z / y `<=` z}.
Proof.
move=>B C; rewrite !leh_lef !hsE/==>P.
by rewrite lev_wpbreg2l// psdf_ge0.
Qed.

Lemma leh_tent2r A : {homo (tenth^~ A) : y z / y `<=` z}.
Proof.
move=>B C; rewrite !leh_lef !hsE/==>P.
by rewrite lev_wpbreg2r// psdf_ge0.
Qed.

Lemma leh_tent2 A B C D : A `<=` B -> C `<=` D -> A `⊗` C `<=` B `⊗` D.
Proof. by move=>/(leh_tent2r C)=>P1/(leh_tent2l B); apply: le_trans. Qed.

(* Lemma tenthUl A B C : (A `⊗` C) `|` (B `⊗` C) = (A `|` B) `⊗` C. *)

Lemma tents0 A : A `⊗` `0` = `0`.
Proof. by apply/hspacelfP; rewrite !hsE/= hsE/= tentf0. Qed.
Lemma ten0ts A : `0` `⊗` A = `0`.
Proof. by apply/hspacelfP; rewrite !hsE/= hsE/= ten0tf. Qed.

Lemma hline u v : <[u]> `⊗` <[v]> = <[u ⊗t v]>.
Proof.
rewrite !hline_def; apply/hspacelfP; rewrite !hsE/= !hsE/=.
by rewrite tentfZl tentfZr scalerA tentv_norm exprMn -invfM tentv_out.
Qed.

End Tenth.

Section SwapTypeTensor.
Implicit Type (S T : ihbFinType).

Definition swaptf T1 T2 : 'Hom[T1 * T2, T2 * T1] :=
  Vector.Hom (\matrix_(i,j) ((idx_pair1 i == idx_pair2 j) 
    && (idx_pair2 i == idx_pair1 j))%:R).
Global Arguments swaptf {T1 T2}.

Lemma swaptfEtv (T1 T2 : ihbFinType) u v :
  swaptf (u ⊗t v) = v ⊗t u :> 'Hs (T2 * T1).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite unlock/= !r2vK !mxE/=.
rewrite (bigD1 (idx_pair (idx_pair2 j) (idx_pair1 j)))//= big1=>[k|];
rewrite !mxE; last first.
by rewrite idx_pair1K idx_pair2K !eqxx mulr1 addr0 mulrC.
case: eqP=>//; do 2 (case: eqP; rewrite/= ?(mulr0, mul0r)//).
by move=><-<-; rewrite idx_pairK.
Qed.

Lemma swaptfEt (T1 T2 : ihbFinType) (t : T1 * T2) :
  swaptf ''t  = ''(t.2,t.1).
Proof. by rewrite tentv_t2tvV swaptfEtv tentv_t2tv. Qed.

Definition swaptf_tf S1 S2 T1 T2 f g :
  (swaptf \o f ⊗f g) \o swaptf = g ⊗f f :> 'Hom[S1 * S2, T1 * T2].
Proof.
by apply/intro_tv=>u v; rewrite lfunE/= swaptfEtv lfunE/= !tentf_apply swaptfEtv.
Qed.

Lemma swaptfE_onb T1 T2 (F G : finType) (onb1 : 'ONB(F;'Hs T1)) 
  (onb2 : 'ONB(G;'Hs T2)) :
    swaptf = \sum_i\sum_j [> onb2 j ⊗t onb1 i ; onb1 i ⊗t onb2 j <].
Proof.
apply/(intro_onb (tentv_onbasis onb1 onb2))=>[[i j]].
rewrite/=/tentv_fun/= swaptfEtv sum_lfunE (bigD1 i)//= sum_lfunE (bigD1 j)// 
  !big1/==>[k/negPf nk|k/negPf nk|].
2: rewrite sum_lfunE big1// =>l _.
all: by rewrite outpE tentv_dot ?ns_dot ?onb_dot ?nk 
  ?(mul1r,mulr0,mul0r) ?scale0r// scale1r !addr0.
Qed.

Lemma swaptfE T1 T2 :
  @swaptf T1 T2 = \sum_i\sum_j [> ''j ⊗t ''i ; ''i ⊗t ''j <].
Proof. exact: swaptfE_onb. Qed.

Lemma swaptf_conj T1 T2 : (@swaptf T1 T2)^C = swaptf.
Proof.
apply/(intro_onb (t2tv2_onbasis))=>[[i j]].
by rewrite/=/tentv_fun/= conjfE tentv_conj !t2tv_conj swaptfEtv tentv_conj !t2tv_conj.
Qed.

Lemma swaptf_adj T1 T2 : (@swaptf T1 T2)^A = swaptf.
Proof.
apply/(intro_onb (t2tv2_onbasis))=>[[i j]]; 
apply/(intro_onbl (t2tv2_onbasis))=>[[m n]].
by rewrite/=/tentv_fun/= adj_dotEV !swaptfEtv !tentv_dot mulrC.
Qed.

Lemma swaptf_tr T1 T2 : (@swaptf T1 T2)^T = swaptf.
Proof. by rewrite trfAC swaptf_adj swaptf_conj. Qed.

Lemma swaptf_unitary T : @swaptf T T \is unitarylf.
Proof.
by apply/unitarylfP; rewrite swaptf_adj -tentf11 -swaptf_tf tentf11 comp_lfun1r.
Qed.
Canonical swaptf_unitaryfType T := UnitaryfType (@swaptf_unitary T).

Lemma swaptfK T1 T2 (u : 'Hs (T1 * T2)) : swaptf (swaptf u) = u.
Proof.
rewrite (onb_vec t2tv2_onbasis u) !linear_sum; apply eq_bigr=>i _.
by rewrite/= !linearZ/=; f_equal; rewrite /tentv_fun !swaptfEtv.
Qed.
Global Arguments swaptfK {T1 T2}.

Lemma swaptf_inj T1 T2 : injective (@swaptf T1 T2).
Proof. exact: (can_inj swaptfK). Qed.
Global Arguments swaptf_inj {T1 T2}.

Lemma swaptf_dot T1 T2 (u v : 'Hs (T1 * T2)) : 
  [< swaptf u ; swaptf v >] = [< u ; v >].
Proof. by rewrite adj_dotE swaptf_adj swaptfK. Qed.

Lemma swaptf_norm T1 T2 (u : 'Hs (T1 * T2)) : `|swaptf u| = `|u|.
Proof. by rewrite !hnormE swaptf_dot. Qed.

Lemma swaptf_out T1 T2 (u v : 'Hs (T1 * T2)) : 
  swaptf \o [> u ; v <] \o swaptf = [> swaptf u ; swaptf v <].
Proof. by rewrite outp_compr outp_compl swaptf_adj. Qed.

End SwapTypeTensor.

(* packing tuples *)
(* since building tuple heavily depends on canonical, we use tuple_of_finfun *)
(* to build the tuple instead, and use tnth_ffun_tuple to cancel it *)
(* easy use: under eq_ffun do rewrite ... *)
Section TentvTuple.
Variable (T : ihbFinType) (n : nat).

Lemma tnth_ffun_tuple (K : Type) (m : nat) (f : {ffun 'I_m -> K}) i :
  (tuple_of_finfun f) ~_ i = f i.
Proof. by rewrite -{2}(tuple_of_finfunK f) ffunE. Qed.

Definition idx_tuplei (i : 'I_(Vector.dim 'Hs (n.-tuple T))) j : 'I_(Vector.dim 'Hs T)
  := cast_ord (ihb_dim_cast T) (enum_rank 
    ((enum_val (cast_ord (esym (ihb_dim_cast _)) i)) ~_ j)).
Definition idx_tuple (fi : 'I_n -> 'I_(Vector.dim 'Hs T)) : 'I_(Vector.dim 'Hs (n.-tuple T))
  := cast_ord (ihb_dim_cast _) (enum_rank (tuple_of_finfun 
    [ffun i : 'I_n => enum_val (cast_ord (esym (ihb_dim_cast _)) (fi i))])).

Lemma idx_tupleiK (fi : 'I_n -> 'I_(Vector.dim 'Hs T)) i :
  idx_tuplei (idx_tuple fi) i = fi i.
Proof.
by rewrite /idx_tuplei /idx_tuple cast_ord_comp cast_ord_id enum_rankK 
  tnth_ffun_tuple ffunE enum_valK cast_ord_comp cast_ord_id.
Qed.
Lemma idx_tupleK (i : 'I_(Vector.dim 'Hs (n.-tuple T))) :
  idx_tuple (idx_tuplei i) = i.
Proof.
apply/eqP; rewrite eq_sym /idx_tuple /idx_tuplei -enum_ord_eq; apply/eqP.
by apply eq_from_tnth=>j; rewrite tnth_ffun_tuple ffunE 
  cast_ord_comp cast_ord_id enum_rankK.
Qed.
Lemma idx_tupleP f g : idx_tuple f = idx_tuple g <-> f =1 g.
Proof.
split=>[P x|P]; first by rewrite -idx_tupleiK P idx_tupleiK.
rewrite /idx_tuple; do 2 f_equal; apply eq_from_tnth=>i; 
by rewrite !tnth_ffun_tuple !ffunE P.
Qed.

Definition tentv_tuple (v : n.-tuple ('Hs T)) : 'Hs (n.-tuple T) 
  := r2v (\row_i (\prod_j v2r (v ~_ j) 0 (idx_tuplei i j))).

Lemma tentv_tuple_dot (u v : n.-tuple ('Hs T)) :
  [< tentv_tuple u ; tentv_tuple v >] = \prod_i [< u ~_ i ; v ~_ i >].
Proof.
rewrite /dotp/= ddotpE.
under eq_bigr do rewrite /tentv_tuple/= !r2vK !mxE rmorph_prod -big_split/=.
under [RHS]eq_bigr do rewrite ddotpE.
rewrite bigA_distr_bigA/= (reindex (fun i=>[ffun j => idx_tuplei i j])).
exists (fun i : {ffun 'I_n -> _}=> idx_tuple i)=>x _.
by rewrite -[RHS]idx_tupleK; apply/idx_tupleP=>i; rewrite ffunE.
by apply/ffunP=>i; rewrite ffunE idx_tupleiK.
by apply eq_bigr=>i _; apply eq_bigr=>j _; rewrite ffunE.
Qed.

Lemma tentv_tuple_norm (u : n.-tuple ('Hs T)) :
  `|tentv_tuple u| = \prod_i `|u ~_ i|.
Proof.
rewrite hnormE tentv_tuple_dot sqrt_prod=>[i _|]; last apply eq_bigr=>i _;
by rewrite dotp_norm ?sqrCK// exprn_ge0//.
Qed.

Lemma t2tv_tuple (t : n.-tuple T) : 
  t2tv t = tentv_tuple (tuple_of_finfun [ffun i=>''(t ~_ i)]).
Proof.
rewrite{1}/t2tv /tentv_tuple /mv2tv; f_equal; apply/matrixP=>i j.
rewrite !mxE. under eq_bigr do rewrite tnth_ffun_tuple ffunE.
case: eqP=>[/eqP|/eqP/tuple_neqP[k/negPf Pk]].
rewrite enum_ord_eq=>/eqP->; under eq_bigr do rewrite/= r2vK mxE
 cast_ord_comp cast_ord_id enum_rankK cast_ord_comp cast_ord_id enum_rankK eqxx.
 by rewrite prodr_const expr1n.
by rewrite (bigD1 k)//= /t2tv/mv2tv r2vK mxE cast_ord_comp cast_ord_id enum_rankK Pk mul0r.
Qed.

Lemma tentv_tuple_conj (t : n.-tuple ('Hs T)) : 
  (tentv_tuple t)^*v = tentv_tuple (tuple_of_finfun [ffun i=>(t ~_ i)^*v]).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite !r2vK !mxE rmorph_prod;
by apply eq_bigr=>k _; rewrite tnth_ffun_tuple ffunE r2vK mxE.
Qed.

Lemma tentv_tupleZ (t : n.-tuple ('Hs T)) (fc : 'I_n -> C) :
  tentv_tuple (tuple_of_finfun [ffun i=> fc i *: t ~_ i])
  = \prod_i (fc i) *: tentv_tuple t.
Proof.
apply/(intro_onbl t2tv_onbasis)=>i/=; rewrite t2tv_tuple dotpZr.
rewrite !tentv_tuple_dot -big_split/=; apply eq_bigr=>j _.
by rewrite !tnth_ffun_tuple !ffunE dotpZr.
Qed.

Lemma tentv_tuple_ns (t : n.-tuple 'NS('Hs T)) :
  [< tentv_tuple (tuple_of_finfun [ffun i => (t ~_ i : 'Hs T)]) ; 
    tentv_tuple (tuple_of_finfun [ffun i => (t ~_ i : 'Hs T)]) >] == 1.
Proof. by rewrite tentv_tuple_dot big1// =>i _; rewrite tnth_ffun_tuple ffunE ns_dot. Qed.
Canonical tentv_tuple_nsType t := NSType (@tentv_tuple_ns t).

End TentvTuple.

Section TentfTuple.
Implicit Type (T : ihbFinType).

Definition tentf_tuple T1 T2 n (f : n.-tuple ('Hom[T1,T2])) : 'Hom[n.-tuple T1, n.-tuple T2]
  := Vector.Hom (\matrix_(i,j) (\prod_k f2mx (f ~_ k) (idx_tuplei i k) (idx_tuplei j k))).

Lemma tentf_tuple_apply T1 T2 n (f : n.-tuple ('Hom[T1,T2])) (v : n.-tuple ('Hs T1)) :
  tentf_tuple f (tentv_tuple v) = tentv_tuple (
    tuple_of_finfun [ffun i=> f ~_ i (v ~_ i)]).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite unlock/= !r2vK !mxE/=.
under [RHS]eq_bigr do rewrite tnth_ffun_tuple ffunE r2vK mxE/=.
rewrite bigA_distr_bigA/= (reindex (fun i=>[ffun j => idx_tuplei i j])).
exists (fun i : {ffun 'I_n -> _}=> idx_tuple i)=>x _.
by rewrite -[RHS]idx_tupleK; apply/idx_tupleP=>k; rewrite ffunE.
by apply/ffunP=>k; rewrite ffunE idx_tupleiK.
apply eq_bigr=>k _; rewrite !mxE -big_split/=; 
by apply eq_bigr=>l _; rewrite ffunE.
Qed.

Lemma tentf_tuple_out T1 T2 n (u : n.-tuple ('Hs T1)) (v : n.-tuple ('Hs T2)) : 
  tentf_tuple (tuple_of_finfun [ffun i=> [> u ~_ i ; v ~_ i <]]) 
  = [> tentv_tuple u ; tentv_tuple v <].
Proof.
apply/(intro_onb t2tv_onbasis)=>i.
rewrite/= t2tv_tuple tentf_tuple_apply outpE.
under eq_ffun do rewrite tnth_ffun_tuple tnth_map ffunE outpE.
rewrite tentv_tupleZ tentv_tuple_dot; f_equal; apply eq_bigr=>j _.
by rewrite tnth_map.
Qed.

Lemma tentf_tuple_adj T1 T2 n (f : n.-tuple ('Hom[T1,T2])) :
  (tentf_tuple f)^A = tentf_tuple (
    tuple_of_finfun [ffun i=> (f ~_ i)^A]).
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE rmorph_prod; 
by apply eq_bigr => k _; rewrite tnth_ffun_tuple ffunE !mxE.
Qed.

Lemma tentf_tuple_conj T1 T2 n (f : n.-tuple ('Hom[T1,T2])) :
  (tentf_tuple f)^C = tentf_tuple (
    tuple_of_finfun [ffun i=> (f ~_ i)^C]).
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE rmorph_prod; 
by apply eq_bigr => k _; rewrite tnth_ffun_tuple ffunE !mxE.
Qed.

Lemma tentf_tuple_tr T1 T2 n (f : n.-tuple ('Hom[T1,T2])) :
  (tentf_tuple f)^T = tentf_tuple (
    tuple_of_finfun [ffun i=> (f ~_ i)^T]).
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE; 
by apply eq_bigr => k _; rewrite tnth_ffun_tuple ffunE !mxE.
Qed.

Lemma tentf_tuple_comp T1 T2 T3 n (f : n.-tuple ('Hom[T1,T2])) (g : n.-tuple ('Hom[T3,T1])) :
  (tentf_tuple f) \o (tentf_tuple g) = tentf_tuple (
    tuple_of_finfun [ffun i=> f ~_ i \o g ~_ i]).
Proof.
apply/(intro_onb t2tv_onbasis)=>i.
rewrite/= t2tv_tuple tentf_tuple_apply lfunE/= !tentf_tuple_apply.
under eq_ffun do rewrite tnth_ffun_tuple ffunE tnth_ffun_tuple ffunE.
by under [in RHS]eq_ffun do rewrite !tnth_ffun_tuple !ffunE lfunE.
Qed.

(* add canonical structures if needed, say, tentf_tuple unitary*)
End TentfTuple.

Section TentfTuplePerm.
Variable (T : ihbFinType) (n : nat).

Definition permtf (s : 'S_n) : 'End[n.-tuple T] :=
  Vector.Hom (\matrix_(i, j) 
    (i == idx_tuple (fun k=> (idx_tuplei j) ((s^-1)%g k)))%:R).

Lemma permtfEtv (s : 'S_n) (v : n.-tuple ('Hs T)) :
  permtf s (tentv_tuple v) = tentv_tuple (tuple_of_finfun [ffun i=> v ~_ (s i)]).
Proof.
apply/v2r_inj/matrixP=>i j.
rewrite unlock/= !r2vK !mxE/= (bigD1 (idx_tuple (fun k=> (idx_tuplei j) ((s^-1)%g k))))
  //=[X in _ + X]big1=>[k/negPf nk|]; rewrite !mxE ?nk ?mulr0//.
rewrite eqxx addr0 mulr1 (reindex_inj (@perm_inj _ s)).
by apply eq_bigr=>k _; rewrite tnth_ffun_tuple ffunE idx_tupleiK permK.
Qed.

Lemma permtfEt (s : 'S_n) t :
  permtf s ''t = ''(tuple_of_finfun [ffun i=> t ~_ (s i)]).
Proof.
rewrite !t2tv_tuple permtfEtv; do 2 f_equal; apply/ffunP=>i;
by rewrite !ffunE !tnth_ffun_tuple !ffunE.
Qed.

Lemma permtf_conj (s : 'S_n) :
  (permtf s)^C = permtf s.
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE conjC_nat. Qed.

Lemma permtf_tr (s : 'S_n) :
  (permtf s)^T = permtf (s^-1)%g.
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite !mxE invgK.
case: eqP=>[->|]; case: eqP=>[//->|//]P; exfalso; apply P;
by rewrite -[LHS]idx_tupleK; apply/idx_tupleP=>k; rewrite idx_tupleiK ?permK ?permKV.
Qed.

Lemma permtf_adj (s : 'S_n) :
  (permtf s)^A = permtf (s^-1)%g.
Proof. by rewrite adjfCT permtf_conj permtf_tr. Qed.

Lemma permtf_comp (s1 s2 : 'S_n) :
  (permtf s1) \o (permtf s2) = permtf (s1 * s2)%g.
Proof.
apply/(intro_onb t2tv_onbasis)=>i; rewrite/= lfunE/= !permtfEt;
by do 2 f_equal; apply/ffunP=>j; rewrite !ffunE tnth_ffun_tuple ffunE permM.
Qed.

Lemma permtf1 : (permtf 1) = \1.
Proof.
apply/(intro_onb t2tv_onbasis)=>i; rewrite/= lfunE/= !permtfEt.
by f_equal; apply eq_from_tnth=>j; rewrite tnth_ffun_tuple ffunE perm1.
Qed.

Lemma permtf_nseq (s : 'S_n) (v : 'Hs T) :
  permtf s (tentv_tuple (nseq_tuple n v)) = (tentv_tuple (nseq_tuple n v)).
Proof.
rewrite permtfEtv; f_equal; apply eq_from_tnth=>i.
by rewrite tnth_ffun_tuple ffunE !tnth_nseq.
Qed.

Lemma permtf_nseqt (s : 'S_n) (t : T) :
  permtf s ''(nseq_tuple n t) = ''(nseq_tuple n t).
Proof.
suff ->: ''(nseq_tuple n t) = tentv_tuple (nseq_tuple n ''t) by apply: permtf_nseq.
by rewrite t2tv_tuple; f_equal; apply eq_from_tnth=>i; rewrite tnth_ffun_tuple ffunE !tnth_nseq.
Qed.

Lemma permtf_unitary (s : 'S_n) : 
  permtf s \is unitarylf.
Proof. by apply/unitarylfP; rewrite permtf_adj permtf_comp mulVg permtf1. Qed.
Canonical permtf_unitaryfType s := UnitaryfType (@permtf_unitary s).

End TentfTuplePerm.

Lemma card_dffun (F : finType) (TF : F -> finType) :
  #|{dffun forall i : F, TF i}| = (\prod_i #|TF i|)%N.
Proof. by rewrite card_dep_ffun foldrE big_map big_enum. Qed.

(* packing dependent ffun *)
Section TentvDffun.
Variable (F : finType) (TF : forall i : F, ihbFinType).
Local Notation TH := {dffun forall i : F, TF i}.

Definition idx_dffuni (i : 'I_(Vector.dim 'Hs TH)) :
  {dffun forall j : F, 'I_(Vector.dim 'Hs (TF j))}
  := [ffun j => cast_ord (ihb_dim_cast _) (enum_rank 
    ((enum_val (cast_ord (esym (ihb_dim_cast _)) i)) j))].

Definition idx_dffun (fi : {dffun forall j : F, 'I_(Vector.dim 'Hs (TF j))}) : 
  'I_(Vector.dim 'Hs TH)
  := cast_ord (ihb_dim_cast _) (enum_rank
    ([ffun i : F => enum_val (cast_ord (esym (ihb_dim_cast _)) (fi i))] : TH)).

Lemma idx_dffuniK : cancel idx_dffuni idx_dffun.
Proof.
move=>i; apply/eqP; rewrite eq_sym -enum_ord_eq; apply/eqP/ffunP=>j.
by rewrite ffunE /idx_dffuni ffunE cast_ord_comp cast_ord_id enum_rankK.
Qed.
Lemma idx_dffunK : cancel idx_dffun idx_dffuni.
Proof.
by move=>i; apply/ffunP=>j; rewrite ffunE cast_ord_comp cast_ord_id 
  enum_rankK ffunE enum_valK cast_ord_comp cast_ord_id.
Qed.

Definition tentv_dffun (v : forall i : F, 'Hs (TF i)) : 'Hs TH
  := r2v (\row_i (\prod_j v2r (v j) 0 (idx_dffuni i j))).

Lemma eq_tentv_dffun (u v : forall i : F, 'Hs (TF i)) :
  (forall i, u i = v i) -> tentv_dffun u = tentv_dffun v.
Proof.
move=>P; apply/v2r_inj/matrixP=>i j.
by rewrite !r2vK !mxE; under eq_bigr do rewrite P.
Qed.

Lemma tentv_dffun_dot (u v : forall i : F, 'Hs (TF i)) :
  [< tentv_dffun u ; tentv_dffun v >] = \prod_i [< u i ; v i >].
Proof.
rewrite /dotp/= ddotpE.
under eq_bigr do rewrite /tentv_dffun/= !r2vK !mxE rmorph_prod -big_split/=.
under [RHS]eq_bigr do rewrite ddotpE.
rewrite big_distr_dffun/= (reindex idx_dffun).
by exists (idx_dffuni)=>x _; rewrite ?idx_dffuniK// idx_dffunK.
by apply eq_bigr=>i _; apply eq_bigr=>j _; rewrite !idx_dffunK.
Qed.

Lemma tentv_dffun_norm (u : forall i : F, 'Hs (TF i)) :
  `|tentv_dffun u| = \prod_i `|u i|.
Proof.
rewrite hnormE tentv_dffun_dot sqrt_prod=>[i _|]; last apply eq_bigr=>i _;
by rewrite dotp_norm ?sqrCK// exprn_ge0.
Qed.

Lemma t2tv_dffun (t : TH) : 
  ''t = tentv_dffun (fun i => ''(t i)).
Proof.
rewrite{1}/tentv_dffun /t2tv/mv2tv; f_equal; apply/matrixP=>i j.
rewrite !mxE. under eq_bigr do rewrite r2vK mxE.
case: eqP=>[ <-|/eqP/dffun_neqP[k/negPf nk]].
by rewrite big1// =>k _; rewrite enum_ord_eq /idx_dffuni ffunE eqxx.
by rewrite (bigD1 k)//= {1}/idx_dffuni ffunE cast_ord_comp cast_ord_id enum_rankK nk mul0r.
Qed.

Lemma tentv_dffun_conj (v : forall i : F, 'Hs (TF i)) : 
  (tentv_dffun v)^*v = tentv_dffun (fun i=>(v i)^*v).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite !r2vK !mxE rmorph_prod;
by apply eq_bigr=>k _; rewrite r2vK mxE.
Qed.

Lemma tentv_dffunZ (v : forall i : F, 'Hs (TF i)) (fc : F -> C) :
  tentv_dffun (fun i=> fc i *: v i)
  = \prod_i (fc i) *: tentv_dffun v.
Proof.
apply/(intro_onbl t2tv_onbasis)=>i/=; rewrite t2tv_dffun dotpZr.
rewrite !tentv_dffun_dot -big_split/=; apply eq_bigr=>j _.
by rewrite dotpZr.
Qed.

Lemma tentv_dffun_ns (t : forall i, 'NS('Hs (TF i))) :
  [< tentv_dffun t ; tentv_dffun t >] == 1.
Proof. by rewrite tentv_dffun_dot big1// =>i _; rewrite ns_dot. Qed.
Canonical tentv_dffun_nsType t := NSType (@tentv_dffun_ns t).

Definition tentv_dffun_fun (G : F -> finType) (f : forall i : F, G i -> 'Hs (TF i)) :=
  (fun i : {dffun forall i : F, G i} => tentv_dffun (fun k=> f k (i k))).
Lemma tentv_dffun_ponb (G : F -> finType) (f : forall i : F, 'PONB(G i;'Hs (TF i))) i j :
  [< tentv_dffun_fun f i ; tentv_dffun_fun f j >] = (i == j)%:R.
Proof.
rewrite/tentv_dffun_fun tentv_dffun_dot.
case: eqP=>[->|/eqP]; first by rewrite big1// =>k _; rewrite ns_dot.
by move=>/dffun_neqP[k/negPf nk]; rewrite (bigD1 k)//= ponb_dot nk mul0r.
Qed.
Lemma tentv_dffun_onb (G : F -> finType) (f : forall i : F, 'ONB(G i;'Hs (TF i))) i j :
  [< tentv_dffun_fun f i ; tentv_dffun_fun f j >] = (i == j)%:R.
Proof. exact: tentv_dffun_ponb. Qed.
Lemma tentv_dffun_card (G : F -> finType) (f : forall i : F, 'ONB(G i;'Hs (TF i))) :
  #|{dffun forall i : F, G i}| = Vector.dim ('Hs TH).
Proof.
rewrite -ihb_dim_cast !card_dffun; apply eq_bigr=>i _; 
by rewrite/= (onb_card (f i)) ihb_dim_cast.
Qed.
Canonical tentv_dffun_ponbasis G f := PONBasis (@tentv_dffun_ponb G f).
Canonical tentv_dffun_onbasis G f := ONBasis (@tentv_dffun_onb G f) (tentv_dffun_card f).
Definition tentvtv_dffun_onbasis := tentv_dffun_onbasis (fun i=>t2tv_onbasis).

End TentvDffun.

Section TentfDffun.
Variable (F : finType) (TF TF' : forall i : F, ihbFinType).
Local Notation TH := {dffun forall i : F, TF i}.
Local Notation TH' := {dffun forall i : F, TF' i}.
Implicit Type (f : forall i : F, 'Hom[TF i, TF' i]).

Definition tentf_dffun f : 'Hom[TH, TH']
  := Vector.Hom (\matrix_(i,j) (\prod_k f2mx (f k) (idx_dffuni i k) (idx_dffuni j k))).

Lemma eq_tentf_dffun f f' :
  (forall i, f i = f' i) -> tentf_dffun f = tentf_dffun f'.
Proof.
move=>P; apply/f2mx_inj/matrixP=>i j.
by rewrite/= !mxE; under eq_bigr do rewrite P.
Qed.

Lemma tentf_dffun_apply f (v : forall i : F, 'Hs (TF i)) :
  tentf_dffun f (tentv_dffun v) = tentv_dffun (fun i=>f i (v i)).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite unlock/= !r2vK !mxE/=.
under [RHS]eq_bigr do rewrite r2vK mxE/=.
rewrite big_distr_dffun/= (reindex (@idx_dffun _ _)).
by exists (@idx_dffuni _ _)=>x _; rewrite ?idx_dffuniK// idx_dffunK.
apply eq_bigr=>k _; rewrite !mxE -big_split/=; 
by apply eq_bigr=>l _; rewrite !idx_dffunK.
Qed.

Lemma tentf_dffun_out (v : forall i : F, 'Hs (TF' i)) (u : forall i : F, 'Hs (TF i)) : 
  tentf_dffun (fun i=> [> v i ; u i <]) 
  = [> tentv_dffun v ; tentv_dffun u <].
Proof.
apply/(intro_onb t2tv_onbasis)=>i.
rewrite/= t2tv_dffun tentf_dffun_apply outpE.
under eq_tentv_dffun do rewrite outpE.
by rewrite tentv_dffunZ tentv_dffun_dot.
Qed.

Lemma tentf_dffun_conj f :
  (tentf_dffun f)^C = tentf_dffun (fun i=> (f i)^C).
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE rmorph_prod; 
by apply eq_bigr => k _; rewrite !mxE.
Qed.

End TentfDffun.

Section TentfDffunGen.
Variable (F : finType).
Implicit Type (TF : forall i : F, ihbFinType).
Local Notation DF x y := (forall i : F, 'Hom[x i, y i]).

Lemma tentf_dffun_tr TF TF' (f : DF TF TF') :
  (tentf_dffun f)^T = tentf_dffun (fun i=> (f i)^T).
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE; 
by apply eq_bigr => k _; rewrite !mxE.
Qed.

Lemma tentf_dffun_adj TF TF' (f : DF TF TF') :
  (tentf_dffun f)^A = tentf_dffun (fun i=> (f i)^A).
Proof.
rewrite adjfCT tentf_dffun_conj tentf_dffun_tr; 
by under eq_tentf_dffun do rewrite -adjfCT.
Qed.

Lemma tentf_dffun_comp TF1 TF2 TF3 (f : DF TF1 TF2) (g : DF TF3 TF1)  :
  (tentf_dffun f) \o (tentf_dffun g) = tentf_dffun (fun i=> f i \o g i).
Proof.
apply/(intro_onb (tentvtv_dffun_onbasis _))=>i/=.
rewrite/tentv_dffun_fun lfunE/= !tentf_dffun_apply.
by under [RHS]eq_tentv_dffun do rewrite lfunE/=.
Qed.
End TentfDffunGen.

(* provide the interface to mxlinear of mvector *)
Require Import prodvect tensor.
Section TenDffunMultilinear.
Variable (F : finType).
Implicit Type (TF : forall i : F, ihbFinType).
Local Notation DV x := (forall i : F, 'Hs (x i)).
Local Notation DF x y := (forall i : F, 'Hom[x i, y i]).

Definition tentv_dmv TF (v : mvector (fun i : F=>'Hs (TF i))) := tentv_dffun v.
Definition tentf_dmv TF1 TF2 (f : mvector (fun i : F => 'Hom[TF1 i,TF2 i])) := tentf_dffun f.

Lemma tentv_dmvE TF (v : DV TF) :
  tentv_dffun v = tentv_dmv (\mvector_(i : F) v i).
Proof. by rewrite/tentv_dmv; apply eq_tentv_dffun=>i; rewrite mvE. Qed.
Lemma tentv_dmvEV TF (v : mvector (fun i : F=>'Hs (TF i))) :
  tentv_dffun v = tentv_dmv v.
Proof. by []. Qed.

Lemma tentf_dmvE TF1 TF2 (f : DF TF1 TF2) :
  tentf_dffun f = tentf_dmv (\mvector_(i : F) f i).
Proof. by rewrite/tentf_dmv; apply eq_tentf_dffun=>i; rewrite mvE. Qed.
Lemma tentf_dmvEV TF1 TF2 (f : mvector (fun i : F => 'Hom[TF1 i,TF2 i])) :
  tentf_dffun f = tentf_dmv f.
Proof. by []. Qed.

(* then tentv_dmv and tentf_dmv are mxlinear *)
Lemma tentv_dmv_mlinear TF : mlinear (@tentv_dmv TF).
Proof.
move=>i a x v; apply/(intro_onbl t2tv_onbasis)=>y.
rewrite/= t2tv_dffun /tentv_dmv linearPr/= !tentv_dffun_dot.
rewrite [LHS](bigD1 i)//= [X in _ = _ + X](bigD1 i)//= 
  [in LHS](eq_bigr (fun j=>[< ''(y j); x j >])); last first.
rewrite [X in _ = _ + _ * X](eq_bigr (fun j=>[< ''(y j); x j >])); last first.
rewrite mvE !msetii mvE eqxx linearP/= mulrDl -mulrA; do 2 f_equal.
rewrite [RHS](bigD1 i)//.
all: by move=>j nj; move: nj {+}nj; rewrite eq_sym=>nj /negPf nje;
  rewrite ?mset_ne 2?mvE ?mset_ne ?mvE ?addr0 ?nje ?scale1r.
Qed.

Lemma tentf_dmv_mlinear TF1 TF2 : mlinear (@tentf_dmv TF1 TF2).
Proof.
move=>i a x v; apply/(intro_onb t2tv_onbasis)=>y.
rewrite/= t2tv_dffun /tentf_dmv lfunE/= lfunE/= !tentf_dffun_apply.
apply/(intro_onbl t2tv_onbasis)=>z.
rewrite/= t2tv_dffun linearPr/= !tentv_dffun_dot.
rewrite [LHS](bigD1 i)//= [X in _ = _ + X](bigD1 i)//= 
  [in LHS](eq_bigr (fun j=>[< ''(z j); x j ''(y j) >])); last first.
rewrite [X in _ = _ + _ * X](eq_bigr (fun j=>[< ''(z j); x j ''(y j) >])); last first.
rewrite mvE !msetii mvE eqxx lfunE/= lfunE/= linearP/= mulrDl -mulrA; 
by do 2 f_equal; rewrite [RHS](bigD1 i).
all: by move=>j nj; move: nj {+}nj; rewrite eq_sym=>nj /negPf nje;
  rewrite ?mset_ne 2?mvE ?mset_ne ?mvE ?addr0 ?nje ?scale1r.
Qed.

End TenDffunMultilinear.


(* add canonical structures if needed, say, tentf_dffun unitary*)
Section TentfDffunPred.
Variable (F : finType) (TF : forall i : F, ihbFinType).

Lemma tentf_dffun_trlf (f : forall i : F, 'End[TF i]) :
  \Tr (tentf_dffun f) = \prod_i \Tr (f i).
Proof.
rewrite (onb_trlf (tentvtv_dffun_onbasis _)).
under [RHS]eq_bigr do rewrite (onb_trlf t2tv_onbasis).
rewrite big_distr_dffun/=; apply eq_bigr=>i _.
by rewrite/tentv_dffun_fun tentf_dffun_apply tentv_dffun_dot.
Qed. 

Lemma tentf_dffun1 : tentf_dffun (fun i : F=> \1 : 'End[TF i]) = \1.
Proof.
apply/(intro_onb t2tv_onbasis)=>i.
rewrite/= t2tv_dffun tentf_dffun_apply lfunE/=;
by under eq_tentv_dffun do rewrite lfunE.
Qed.

Lemma tentf_dffun_ge0 (f : forall i : F, 'End[TF i]) :
  (forall i, 0%:VF ⊑ f i) -> 0%:VF ⊑ tentf_dffun f.
Proof.
move=>P. have P1 i : {g : 'End[TF i] | f i = g^A \o g}.
by move: (P i)=>/ge0_form/sig_eqW[g Pg]; exists g.
suff -> : tentf_dffun f = (tentf_dffun (fun i=>projT1 (P1 i)))^A \o
  (tentf_dffun (fun i=>projT1 (P1 i))) by apply form_ge0.
rewrite tentf_dffun_adj tentf_dffun_comp; apply eq_tentf_dffun=>i.
exact: (projT2 (P1 i)).
Qed.

Lemma tentf_dffun_lef (f g : forall i : F, 'End[TF i]) :
  (forall i, 0%:VF ⊑ f i) -> (forall i, f i ⊑ g i) -> tentf_dffun f ⊑ tentf_dffun g.
Proof.
move=>P1 P2.
pose fn n := \mvector_(i : F) (if (enum_rank i < n)%N then g i else f i).
have fn0 : tentf_dffun f = tentf_dffun (fn 0%N).
by apply eq_tentf_dffun=>i; rewrite mvE ltn0.
have fnn n : (#|F| <= n)%N -> tentf_dffun g = tentf_dffun (fn n).
move=>P; apply eq_tentf_dffun=>i; rewrite mvE; case: leqP=>// P3.
by move: (leq_trans P P3); rewrite leqNgt ltn_ord.
suff: forall n, tentf_dffun (fn 0%N) ⊑ tentf_dffun (fn n).
move=>/(_ #|F|); rewrite fn0 (fnn #|F|)//.
move=>n; elim: n=>[//|n IH].
apply: (le_trans IH); case E: (n < #|F|)%N; last first.
rewrite -!fnn ?lexx//. 2: apply/ltnW. 1,2: rewrite ?ltnS leqNgt E//.
suff P3 (k : 'I_#|F|) : fn k.+1 = fn k +_ (enum_val k) (g (enum_val k) - f (enum_val k)).
move: (P3 (Ordinal E))=>/=->.
rewrite !tentf_dmvEV mlinearD. exact: tentf_dmv_mlinear.
rewrite lev_addl; apply/tentf_dffun_ge0=>i.
case E1: (i == enum_val (Ordinal E)).
move: E1=>/eqP E1; case: (enum_val (Ordinal E)) / E1.
by rewrite msetii subv_ge0 P2.
move: E1=>/eqP/eqP; rewrite eq_sym=>P4; rewrite mset_ne ?P4// /fn mvE.
by case: ltnP=>_; rewrite ?P1//; move: (le_trans (P1 i) (P2 i)).
apply/mvectorP=>i.
have P3 (x y : 'I_#|F|) : (x < y)%N -> enum_val x != enum_val y /\ (x < y /\ x < y.+1)%N.
by move=>H; rewrite (can_eq enum_valK); do ? split=>//; 
  move: H; rewrite ltn_neqAle ?ltnS=>/andP[].
case: (ltngtP (enum_rank i) k)=>[/P3|/P3|/val_inj P4];rewrite ?enum_rankK.
by move=>[]P4[]P5 P6; rewrite mvE mvE mset_ne 1?eq_sym// !mvE P5 P6 addr0.
by move=>[]P4[]P5 P6; rewrite mvE mvE mset_ne// !mvE ltnS ltn_neqAle leqNgt P5/=
  (inj_eq val_inj) (can2_eq enum_rankK enum_valK) eq_sym P4/= addr0.
have ->: i = enum_val k by rewrite -P4 enum_rankK.
by rewrite mvE mvE msetii !mvE enum_valK ltnSn ltnn addrC addrNK.
Qed.

Lemma tentf_dffun_herm (f : forall i : F, 'FH('Hs (TF i))) : tentf_dffun f \is hermlf.
Proof.
by rewrite hermlfE tentf_dffun_adj; under eq_tentf_dffun do rewrite hermf_adjE.
Qed.
Canonical tentf_dffun_hermfType f := HermfType (@tentf_dffun_herm f).
Lemma tentf_dffun_psd (f : forall i : F, 'F+('Hs (TF i))) : tentf_dffun f \is psdlf.
Proof. rewrite psdlfE; apply/tentf_dffun_ge0=>i; apply/psdf_ge0. Qed.
Canonical tentf_dffun_psdfType f := PsdfType (@tentf_dffun_psd f).
Lemma tentf_dffun_den (f : forall i : F, 'FD('Hs (TF i))) : tentf_dffun f \is denlf.
Proof.
apply/denlfP; split; first by apply/psdf_psd.
rewrite tentf_dffun_trlf.
have P1 : \prod_(i : F) 1 = 1 :> C by rewrite prodr_const expr1n.
by rewrite -{2}P1 ler_prod// =>i _; rewrite psdf_trlf denf_trlf.
Qed.
Canonical tentf_dffun_denfType f := DenfType (@tentf_dffun_den f).
Lemma tentf_dffun_obs (f : forall i : F, 'FO('Hs (TF i))) : tentf_dffun f \is obslf.
Proof.
apply/obslf_lefP; rewrite psdf_ge0; split=>//.
by rewrite -tentf_dffun1; apply tentf_dffun_lef=>i; rewrite ?psdf_ge0// obsf_le1.
Qed.
Canonical tentf_dffun_obsfType f := ObsfType (@tentf_dffun_obs f).
Lemma tentf_dffun_unitary (f : forall i : F, 'FU('Hs (TF i))) : tentf_dffun f \is unitarylf.
Proof.
apply/unitarylfP; rewrite tentf_dffun_adj tentf_dffun_comp.
by under eq_tentf_dffun do rewrite unitaryf_form; rewrite tentf_dffun1.
Qed.
Canonical tentf_dffun_unitaryfType f := UnitaryfType (@tentf_dffun_unitary f).
Lemma tentf_dffun_den1 (f : forall i : F, 'FD1('Hs (TF i))) : tentf_dffun f \is den1lf.
Proof.
apply/den1lfP; split; first by apply/psdf_psd.
by rewrite tentf_dffun_trlf big1// =>i _; rewrite den1f_trlf.
Qed.
Canonical tentf_dffun_den1fType f := Den1fType (@tentf_dffun_den1 f).
Lemma tentf_dffun_proj (f : forall i : F, 'FP('Hs (TF i))) : tentf_dffun f \is projlf.
Proof.
apply/projlfP; rewrite tentf_dffun_adj tentf_dffun_comp; split;
by under eq_tentf_dffun do rewrite ?hermf_adjE ?projf_idem.
Qed.
Canonical tentf_dffun_projfType f := ProjfType (@tentf_dffun_proj f).
Lemma tentf_dffun_proj1 (f : forall i : F, 'FP1('Hs (TF i))) : tentf_dffun f \is proj1lf.
Proof. by apply/proj1lfP; rewrite projf_proj den1f_trlf. Qed.
Canonical tentf_dffun_proj1fType f := Proj1fType (@tentf_dffun_proj1 f).

End TentfDffunPred.


(* packing plain ffun *)
Section TentvFfun.
Variable (F : finType) (T : ihbFinType).
Local Notation TH := {ffun F -> T}.

Definition tentv_ffun (v : F -> 'Hs T) : 'Hs TH
  := tentv_dffun v.

Lemma eq_tentv_ffun (u v : F -> 'Hs T) :
  (forall i, u i = v i) -> tentv_ffun u = tentv_ffun v.
Proof. exact: eq_tentv_dffun. Qed.

Lemma tentv_ffun_dot (u v : F -> 'Hs T) :
  [< tentv_ffun u ; tentv_ffun v >] = \prod_i [< u i ; v i >].
Proof. exact: tentv_dffun_dot. Qed.

Lemma tentv_ffun_norm (u : F -> 'Hs T) :
  `|tentv_ffun u| = \prod_i `|u i|.
Proof. exact: tentv_dffun_norm. Qed.

Lemma t2tv_ffun (t : TH) : ''t = tentv_ffun (fun i => ''(t i)).
Proof. exact: t2tv_dffun. Qed.

Lemma tentv_ffun_conj (v : F -> 'Hs T) : 
  (tentv_ffun v)^*v = tentv_ffun (fun i=>(v i)^*v).
Proof. exact: tentv_dffun_conj. Qed.

Lemma tentv_ffunZ (v : F -> 'Hs T) (fc : F -> C) :
  tentv_ffun (fun i=> fc i *: v i) = \prod_i (fc i) *: tentv_ffun v.
Proof. exact: tentv_dffunZ. Qed.

Lemma tentv_ffun_ns (t : F -> 'NS('Hs T)) :
  [< tentv_ffun t ; tentv_ffun t >] == 1.
Proof. exact: tentv_dffun_ns. Qed.
Canonical tentv_ffun_nsType t := NSType (@tentv_ffun_ns t).

(* if G is dependent on F, using tentv_dffun_fun instead *)
Definition tentv_ffun_fun (G : finType) (f : F -> G -> 'Hs T) :=
  (fun i : {ffun F -> G} => tentv_ffun (fun k=> f k (i k))).
Lemma tentv_ffun_ponb (G : finType) (f : F -> 'PONB(G;'Hs T)) i j :
  [< tentv_ffun_fun f i ; tentv_ffun_fun f j >] = (i == j)%:R.
Proof. exact: tentv_dffun_ponb. Qed.
Lemma tentv_ffun_onb (G : finType) (f : F -> 'ONB(G;'Hs T)) i j :
  [< tentv_ffun_fun f i ; tentv_ffun_fun f j >] = (i == j)%:R.
Proof. exact: tentv_dffun_onb. Qed.
Canonical tentv_ffun_ponbasis G f := PONBasis (@tentv_ffun_ponb G f).
Canonical tentv_ffun_onbasis G f := ONBasis (@tentv_ffun_onb G f) (tentv_dffun_card f).
Definition tentvtv_ffun_onbasis := tentv_ffun_onbasis (fun i=>t2tv_onbasis).

End TentvFfun.

Section TentfFfun.
Variable (F : finType) (T T' : ihbFinType).
Local Notation TH := {ffun F -> T}.
Local Notation TH' := {ffun F -> T'}.
Implicit Type (f : F -> 'Hom[T, T']).

Definition tentf_ffun f : 'Hom[TH, TH'] := tentf_dffun f.

Lemma eq_tentf_ffun f f' :
  (forall i, f i = f' i) -> tentf_ffun f = tentf_ffun f'.
Proof. exact: eq_tentf_dffun. Qed.

Lemma tentf_ffun_apply f (v : F -> 'Hs T) :
  tentf_ffun f (tentv_ffun v) = tentv_ffun (fun i=>f i (v i)).
Proof. exact: tentf_dffun_apply. Qed.

Lemma tentf_ffun_out (v : F -> 'Hs T') (u : F -> 'Hs T) : 
  tentf_ffun (fun i=> [> v i ; u i <]) 
  = [> tentv_ffun v ; tentv_ffun u <].
Proof. exact: tentf_dffun_out. Qed.

Lemma tentf_ffun_conj f :
  (tentf_ffun f)^C = tentf_ffun (fun i=> (f i)^C).
Proof. exact: tentf_dffun_conj. Qed.

End TentfFfun.

Section TentfFfunGen.
Variable (F : finType).
Implicit Type (T : ihbFinType).
Local Notation DF x y := (F -> 'Hom[x, y]).

Lemma tentf_ffun_tr T T' (f : DF T T') :
  (tentf_ffun f)^T = tentf_ffun (fun i=> (f i)^T).
Proof. exact: tentf_dffun_tr. Qed.

Lemma tentf_ffun_adj T T' (f : DF T T') :
  (tentf_ffun f)^A = tentf_ffun (fun i=> (f i)^A).
Proof. exact: tentf_dffun_adj. Qed.

Lemma tentf_ffun_comp T1 T2 T3 (f : DF T1 T2) (g : DF T3 T1)  :
  (tentf_ffun f) \o (tentf_ffun g) = tentf_ffun (fun i=> f i \o g i).
Proof. exact: tentf_dffun_comp. Qed.
End TentfFfunGen.

(* provide the interface to mxlinear of mvector *)
Section TenFfunMultilinear.
Variable (F : finType).
Implicit Type (T : ihbFinType).
Local Notation DV x := (F -> 'Hs x).
Local Notation DF x y := (F -> 'Hom[x,y]).

Definition tentv_mv T (v : mvector (fun i : F=>'Hs T)) := tentv_ffun v.
Definition tentf_mv T1 T2 (f : mvector (fun i : F => 'Hom[T1,T2])) := tentf_ffun f.

Lemma tentv_mvE T (v : DV T) :
  tentv_ffun v = tentv_mv (\mvector_(i : F) v i).
Proof. exact: tentv_dmvE. Qed.
Lemma tentv_mvEV T (v : mvector (fun i : F=>'Hs T)) :
  tentv_ffun v = tentv_mv v.
Proof. by []. Qed.

Lemma tentf_mvE T1 T2 (f : DF T1 T2) :
  tentf_ffun f = tentf_mv (\mvector_(i : F) f i).
Proof. exact: tentf_dmvE. Qed.
Lemma tentf_mvEV T1 T2 (f : mvector (fun i : F => 'Hom[T1,T2])) :
  tentf_ffun f = tentf_mv f.
Proof. by []. Qed.

(* then tentv_dmv and tentf_dmv are mxlinear *)
Lemma tentv_mv_mlinear T : mlinear (@tentv_mv T).
Proof. exact: tentv_dmv_mlinear. Qed.

Lemma tentf_mv_mlinear T1 T2 : mlinear (@tentf_mv T1 T2).
Proof. exact: tentf_dmv_mlinear. Qed.

End TenFfunMultilinear.


(* add canonical structures if needed, say, tentf_ffun unitary*)
Section TentfFfunPred.
Variable (F : finType) (T : ihbFinType).

Lemma tentf_ffun_trlf (f : F -> 'End[T]) :
  \Tr (tentf_ffun f) = \prod_i \Tr (f i).
Proof. exact: tentf_dffun_trlf. Qed.

Lemma tentf_ffun1 : tentf_ffun (fun i : F=> \1 : 'End[T]) = \1.
Proof. exact: tentf_dffun1. Qed.

Lemma tentf_ffun_ge0 (f : F -> 'End[T]) :
  (forall i, 0%:VF ⊑ f i) -> 0%:VF ⊑ tentf_ffun f.
Proof. exact: tentf_dffun_ge0. Qed.

Lemma tentf_ffun_lef (f g : F -> 'End[T]) :
  (forall i, 0%:VF ⊑ f i) -> (forall i, f i ⊑ g i) -> tentf_ffun f ⊑ tentf_ffun g.
Proof. exact: tentf_dffun_lef. Qed.

Lemma tentf_ffun_herm (f : F -> 'FH('Hs T)) : tentf_ffun f \is hermlf.
Proof. exact: tentf_dffun_herm. Qed.
Canonical tentf_ffun_hermfType f := HermfType (@tentf_ffun_herm f).
Lemma tentf_ffun_psd (f : F -> 'F+('Hs T)) : tentf_ffun f \is psdlf.
Proof. exact: tentf_dffun_psd. Qed.
Canonical tentf_ffun_psdfType f := PsdfType (@tentf_ffun_psd f).
Lemma tentf_ffun_den (f : F -> 'FD('Hs T)) : tentf_ffun f \is denlf.
Proof. exact: tentf_dffun_den. Qed.
Canonical tentf_ffun_denfType f := DenfType (@tentf_ffun_den f).
Lemma tentf_ffun_obs (f : F -> 'FO('Hs T)) : tentf_ffun f \is obslf.
Proof. exact: tentf_dffun_obs. Qed.
Canonical tentf_ffun_obsfType f := ObsfType (@tentf_ffun_obs f).
Lemma tentf_ffun_unitary (f : F -> 'FU('Hs T)) : tentf_ffun f \is unitarylf.
Proof. exact: tentf_dffun_unitary. Qed.
Canonical tentf_ffun_unitaryfType f := UnitaryfType (@tentf_ffun_unitary f).
Lemma tentf_ffun_den1 (f : F -> 'FD1('Hs T)) : tentf_ffun f \is den1lf.
Proof. exact: tentf_dffun_den1. Qed.
Canonical tentf_ffun_den1fType f := Den1fType (@tentf_ffun_den1 f).
Lemma tentf_ffun_proj (f : F -> 'FP('Hs T)) : tentf_ffun f \is projlf.
Proof. exact: tentf_dffun_proj. Qed.
Canonical tentf_ffun_projfType f := ProjfType (@tentf_ffun_proj f).
Lemma tentf_ffun_proj1 (f : F -> 'FP1('Hs T)) : tentf_ffun f \is proj1lf.
Proof. exact: tentf_dffun_proj1. Qed.
Canonical tentf_ffun_proj1fType f := Proj1fType (@tentf_ffun_proj1 f).

End TentfFfunPred.

