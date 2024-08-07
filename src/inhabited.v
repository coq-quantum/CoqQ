(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra perm fingroup.
From mathcomp.analysis Require Import -(notations)forms.
From quantum.external Require Import spectral.
From mathcomp.analysis Require Import reals.
From mathcomp.classical Require Import classical_sets.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
From mathcomp.real_closed Require Import mxtens.

Require Import mcextra mcaextra notation mxpred hermitian ctopology quantum hspace.
Import Order.LTheory GRing.Theory Num.Theory.
Import VectorInternalTheory.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(******************************************************************************)
(*              Associate Classical Date Type to its Hilber Space             *)
(* -------------------------------------------------------------------------- *)
(* This file provide the Module of ihbFinType, the inhabited finite type      *)
(*   it is the basic type of quantum variables, since we only conside finite  *)
(*   case. It is also required to have at least one element, the witness, to  *)
(*   ensure that the corresponding Hilbert space is non-degenerate            *)
(* -------------------------------------------------------------------------- *)
(*       ihbFinType == interface type for a finite type with a witness        *)
(*                     join of Finite and Pointed                             *)
(*                     The HB class is FinInhabited                           *)
(*                                                                            *)
(* We provide canonical structure of ihbFinType : bool, ordinal number,       *)
(*   product type, tuple, ffun and dffun ...                                  *)
(* -------------------------------------------------------------------------- *)
(* Each ihbFinType T is associated with a Hilbert space 'Hs T, the space has  *)
(*   the dimension exactly as #|T|. t2tv (t : T) (notation ''t) provide the   *)
(*   computational basis of 'Hs T, t2tv is also canonical as 'ONB(T;'Hs T),   *)
(*   the index is T itself.                                                   *)
(* -------------------------------------------------------------------------- *)
(* Computation : to compute simple types directly, such as 'Hs bool, we give  *)
(*   the way to build a vector/linear function of 'Hs T directly from T -> C  *)
(*   or T -> T -> C. (I don't know if matrix can be calculated directly or    *)
(*   not, and if it is possible, then remove this construction)               *)
(* -------------------------------------------------------------------------- *)
(* For compositional type (prod, tuple, ffun, dffun), we provide the way to   *)
(*   build vect/lfun for them from single element. That is,                   *)
(*   ⊗v : 'Hs T -> 'Hs T -> 'Hs (T * T)                                      *)
(*   ⊗f : 'End[T] -> 'End[T] -> 'End[T * T]  where  'End[T] is 'End('Hs T)   *)
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

Notation ihbType := pointedType.
Notation witness := @point.

(* -------------------------------------------------------------------- *)

#[short(type="ihbFinType")]
HB.structure Definition FinInhabited :=
  { T of Finite T & isPointed T }.

HB.instance Definition _ := isPointed.Build unit tt.
HB.instance Definition _ := isPointed.Build nat 0%N.
HB.instance Definition _ n := isPointed.Build 'I_n.+1 ord0.
HB.instance Definition _ := isPointed.Build bool false.
HB.instance Definition _ := isPointed.Build int 0.
HB.instance Definition _ (R:realType) := isPointed.Build R 0.
HB.instance Definition _ := isPointed.Build C 0.
HB.instance Definition _ (T : choiceType) := isPointed.Build (option T) None.

(* -------------------------------------------------------------------- *)

HB.instance Definition _ (T U : ihbType) := isPointed.Build
  (T * U)%type (@witness T, @witness U).
HB.instance Definition _ (T1 T2 : ihbType) := isPointed.Build
  (T1 + T2)%type (inl (@witness T1)).
HB.instance Definition _ (T:ihbType) := isPointed.Build (seq.seq T) [::].
HB.instance Definition _ n (T:ihbType) := isPointed.Build
  (n.-tuple T) (nseq_tuple n (@witness T)).
HB.instance Definition _ (F : finType) (T : ihbType) := isPointed.Build
  {ffun F -> T} [ffun=> @witness T].
HB.instance Definition _ (F : finType) (T : forall i : F, ihbType) :=
  isPointed.Build {dffun forall i : F, T i} [ffun i => @witness (T i)].

(* -------------------------------------------------------------------- *)

HB.instance Definition _ (F : finType) := FinInhabited.Class
  (Choice.on (option F)) (Countable.on (option F)) (Finite.on (option F)) (Pointed.on (option F)).
HB.instance Definition _ (T U : ihbFinType) := FinInhabited.Class
(Choice.on (T * U)%type) (Countable.on (T * U)%type) (Finite.on (T * U)%type) (Pointed.on (T * U)%type).
HB.instance Definition _ (T1 T2 : ihbFinType) := FinInhabited.Class
(Choice.on (T1 + T2)%type) (Countable.on (T1 + T2)%type) (Finite.on (T1 + T2)%type) (Pointed.on (T1 + T2)%type).
HB.instance Definition _ n (T:ihbFinType) := FinInhabited.Class
(Choice.on (n.-tuple T)) (Countable.on (n.-tuple T)) (Finite.on (n.-tuple T)) (Pointed.on (n.-tuple T)).
HB.instance Definition _ (F : finType) (T : ihbFinType) := FinInhabited.Class
(Choice.on {ffun F -> T}) (Countable.on {ffun F -> T}) (Finite.on {ffun F -> T}) (Pointed.on {ffun F -> T}).
HB.instance Definition _ (F : finType) (T : forall i : F, ihbFinType) := FinInhabited.Class
(Choice.on {dffun forall i : F, T i}) (Countable.on {dffun forall i : F, T i})
(Finite.on {dffun forall i : F, T i}) (Pointed.on {dffun forall i : F, T i}).

Module FinInhabitedExports.
#[deprecated(since="mathcomp 2.0.0", note="Use FinInhabited.clone instead.")]
Notation "[ 'ihbFinType' 'of' T 'for' cT ]" := (FinInhabited.clone T%type cT)
  (at level 0, format "[ 'ihbFinType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use FinInhabited.clone instead.")]
Notation "[ 'ihbFinType' 'of' T ]" := (FinInhabited.Pack (FinInhabited.Class _ (isPointed.Build T _) _))
  (at level 0, format "[ 'ihbFinType'  'of'  T ]") : form_scope.
End FinInhabitedExports.
HB.export FinInhabitedExports.

Section DefaultChsType.
Variable (T: ihbFinType).

Let H := {ffun T -> C^o}.

Definition ddotp (x y : H) := dotmx (v2r x)^*m (v2r y)^*m.

Let ddotpE x y : ddotp x y = \sum_i ((v2r x) 0 i)^* * ((v2r y) 0 i).
Proof.
rewrite /ddotp /dotmx /form /= mulmx1 /mxtrace mxE;
apply eq_bigr=>i _; by rewrite !mxE /conjCfun conjCK.
Qed.

Let ge0_ddotp v : 0 <= ddotp v v.
Proof. exact: dnorm_ge0. Qed.

Let ddotp_eq0 v : (ddotp v v == 0) = (v == 0).
Proof. 
by rewrite dnorm_eq0 -(inj_eq (@conjmx_inj _ _ _)) conjmxK 
    -(inj_eq (@r2v_inj _ _)) v2rK !linear0.
Qed.

Let conj_ddotp u v : (ddotp u v)^* = ddotp v u.
Proof.
rewrite !ddotpE rmorph_sum /=. apply eq_bigr=>i _.
by rewrite rmorphM/= conjCK mulrC.
Qed.

Let linear_ddotp u : linear_for *%R (ddotp u).
Proof.
move=>c v w; rewrite !ddotpE mulr_sumr -big_split.
apply eq_bigr=>i _; by rewrite linearP/= !mxE mulrDr !mulrA [_ * c]mulrC.
Qed.

Definition default_hermitianMixin :=
  @Vector_isHermitianSpace.Build H ddotp ge0_ddotp ddotp_eq0 conj_ddotp linear_ddotp.
Canonical default_hermitianType := @HermitianSpace.Pack H (HermitianSpace.Class default_hermitianMixin).

Let ddotp_chE i j :
    [< r2v (delta_mx 0 i) : H; r2v (delta_mx 0 j) >] = (i == j)%:R.
Proof.
rewrite /dotp/= ddotpE !r2vK (bigD1 i)// big1/=.
by move=>k /negPf nki; rewrite mxE eqxx nki conjC0 mul0r.
by rewrite !mxE !eqxx conjC1 mul1r addr0.
Qed.

Let ihb_dim_cast: #|T| = dim H.
Proof. by rewrite /dim/= /dim/= muln1. Qed.

Let ihb_dim_proper : (dim H > 0)%N.
Proof. move: (max_card (pred1 (witness T))); by rewrite ihb_dim_cast card1. Qed.

Definition ihb_chsMixin := HermitianSpace_isCanonical.Build H ddotp_chE ihb_dim_proper.

End DefaultChsType.

HB.lock
Definition ihb_chsType (T : ihbFinType) := 
  CanonicalHermitianSpace.Pack (CanonicalHermitianSpace.Class (@ihb_chsMixin T)).

Notation "''Hs' T" := (ihb_chsType T) (at level 8, T at level 2, format "''Hs'  T").
(* Notation "''Hs' T" := (ihb_chsType [ihbFinType of T]) (at level 8, T at level 2, format "''Hs'  T"). *)
Notation "''Hom[' T1 , T2 ]" := ('Hom('Hs T1, 'Hs T2)) (at level 8, format "''Hom[' T1 ,  T2 ]").
Notation "''End[' T ]" := ('End('Hs T)) (at level 8, format "''End[' T ]").
Notation "x %:V" := (x : 'Hs _) 
  (at level 2, left associativity, format "x %:V") : lfun_scope.

Section DefaultChsType1.
Variable (T : ihbFinType).

Lemma ihb_dim_cast: #|T| = dim ('Hs T).
Proof. by rewrite [ihb_chsType]unlock /dim/= /dim/= muln1. Qed.

Lemma ihb_dim_proper : (dim ('Hs T) > 0)%N.
Proof. move: (max_card (pred1 (witness T))); by rewrite ihb_dim_cast card1. Qed.

Lemma ihb_card_gt0 : (0 < #|T|)%N.
Proof. by rewrite ihb_dim_cast ihb_dim_proper. Qed.

Lemma ihb_card_gtr0 (R : numDomainType) : 0 < (#|T|%:R : R).
Proof. by rewrite ltr0n ihb_card_gt0. Qed.

Lemma ihb_card_neq0 (R : numDomainType) : (#|T|%:R : R) != 0.
Proof. apply/lt0r_neq0/ihb_card_gtr0. Qed.

Lemma ihb_v2hE : (@v2hU ('Hs T)) = 1%:M.
Proof.
rewrite [ihb_chsType]unlock; apply/matrixP=>i j.
by rewrite v2hU.unlock !mxE tnthE r2vK mxE eqxx.
Qed.

Lemma ihb_h2vE : (@h2vU ('Hs T)) = 1%:M.
Proof. by rewrite h2vU.unlock ihb_v2hE invmx1. Qed.

Lemma ihb_h2cE (v : 'Hs T) : h2c v = ((v2r v)^T)%R.
Proof. by rewrite h2cE ihb_h2vE mul1mx. Qed.

Lemma ihb_c2hE v : (c2h v : 'Hs T) = r2v v^T.
Proof. by apply/h2c_inj; rewrite c2hK ihb_h2cE r2vK trmxK. Qed.

End DefaultChsType1.

Section DefaultChsTypeTheory.
Variable (T : ihbFinType).

Definition mv2tv (f : T -> C) : 'Hs T :=
  c2h (\col_ i f (enum_val (cast_ord (esym (@ihb_dim_cast T)) i))).
Definition tv2mv (v : 'Hs T) : T -> C :=
  (fun t => h2c v (cast_ord (@ihb_dim_cast T) (enum_rank t)) 0).

Lemma mv2tvK f : tv2mv (mv2tv f) =1 f.
Proof.
by move=>x; rewrite/tv2mv/mv2tv c2hK mxE cast_ord_comp cast_ord_id enum_rankK.
Qed.

Lemma tv2mvK : cancel tv2mv mv2tv.
Proof.
move=>x; rewrite/tv2mv/mv2tv; apply/h2c_inj/matrixP=>i j.
by rewrite c2hK mxE ord1 enum_valK cast_ord_comp cast_ord_id.
Qed.

Lemma mv2tvP f g : mv2tv f = mv2tv g <-> f =1 g.
Proof. 
split=>P. by move=>i; rewrite -mv2tvK P mv2tvK.
by apply/h2c_inj/matrixP=>i j; rewrite /mv2tv !c2hK !mxE P. 
Qed.
Lemma tv2mvP f g : tv2mv f =1 tv2mv g <-> f = g.
Proof. by rewrite -mv2tvP !tv2mvK. Qed.

(* if needed, add function's here *)
Definition mx2tf (f : T -> T -> C) : 'End('Hs T) :=
  mx2h (\matrix_(i,j) f (enum_val (cast_ord (esym (@ihb_dim_cast T)) i))
  (enum_val (cast_ord (esym (@ihb_dim_cast T)) j))).
Definition tf2mx (f : 'End('Hs T)) : T -> T -> C :=
  (fun t1 t2 : T => h2mx f (cast_ord (@ihb_dim_cast T) (enum_rank t1)) 
    (cast_ord (@ihb_dim_cast T) (enum_rank t2))).

Lemma mx2tfK f : tf2mx (mx2tf f) =2 f.
Proof.
move=>x y. rewrite /mx2tf /tf2mx.
by rewrite mx2hK mxE !cast_ord_comp !cast_ord_id !enum_rankK.
Qed.

Lemma tf2mxK : cancel tf2mx mx2tf.
Proof.
move=>x; rewrite /mx2tf /tf2mx; apply/h2mx_inj/matrixP=>i j.
by rewrite mx2hK !mxE/= !enum_valK !cast_ord_comp !cast_ord_id. 
Qed.

Lemma mx2tfP f g : mx2tf f = mx2tf g <-> f =2 g.
Proof. 
split=>P. by move=>i j; rewrite -mx2tfK P mx2tfK.
by apply/h2mx_inj/matrixP=>i j; rewrite /mx2tf/= !mx2hK !mxE P. 
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
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite linearD/= !mx2hK !mxE. Qed.
Lemma mx2tf_opp (f : T -> T -> C) : - (mx2tf f) = mx2tf (funf_opp f).
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite linearN/= !mx2hK !mxE. Qed.
Lemma mx2tf_scale (c : C) (f : T -> T -> C) : c *: (mx2tf f) = mx2tf (funf_scale c f).
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite linearZ/= !mx2hK !mxE. Qed.
Lemma mx2tf_comp (f g : T -> T -> C) : (mx2tf f) \o (mx2tf g) = mx2tf (funf_comp f g).
Proof.
apply/h2mx_inj/matrixP=>i j; rewrite h2mx_comp !mx2hK !mxE /funf_comp.
under eq_bigr do rewrite !mxE. symmetry. apply: reindex. apply bij_enum_ord. 
Qed.
Lemma mx2tf_adj (f : T -> T -> C) : (mx2tf f)^A = mx2tf (funf_adj f).
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite adj_lfun.unlock !mx2hK !mxE. Qed.
Lemma mx2tf_tr (f : T -> T -> C) : ((mx2tf f)^T)%VF = mx2tf (funf_tr f).
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite tr_lfun.unlock !mx2hK !mxE. Qed.
Lemma mx2tf_conj (f : T -> T -> C) : (mx2tf f)^C = mx2tf (funf_conj f).
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite conj_lfun.unlock !mx2hK !mxE. Qed.
Lemma mx2tf_apply (f : T -> T -> C) (v : T -> C) :
  (mx2tf f) (mv2tv v) = mv2tv (funf_apply f v).
Proof.
rewrite applyfh mx2hK; apply/h2c_inj/matrixP=>i j; rewrite !c2hK !mxE.
under eq_bigr do rewrite !mxE. symmetry. apply: reindex. apply bij_enum_ord.
Qed.
Lemma mv2tv_add (f g : T -> C) : (mv2tv f) + (mv2tv g) = mv2tv (funv_add f g).
Proof. by apply/h2c_inj/matrixP=>i j; rewrite linearD /mv2tv/= !c2hK !mxE. Qed.
Lemma mv2tv_opp (f : T -> C) : - (mv2tv f) = mv2tv (funv_opp f).
Proof. by apply/h2c_inj/matrixP=>i j; rewrite linearN /mv2tv/= !c2hK !mxE. Qed.
Lemma mv2tv_scale (c : C) (f : T -> C) : c *: (mv2tv f) = mv2tv (funv_scale c f).
Proof. by apply/h2c_inj/matrixP=>i j; rewrite linearZ /mv2tv/= !c2hK !mxE. Qed.
Lemma mv2tv_conj (f : T -> C) : (mv2tv f)^*v = mv2tv (funv_conj f).
Proof. by apply/h2c_inj/matrixP=>i j; rewrite conjv.unlock /mv2tv !c2hK !mxE. Qed.
Lemma mv2tv_dot (u v : T -> C) : [<mv2tv u; mv2tv v>] = funv_dot u v.
Proof.
rewrite dotp_mulmx !c2hK mxE /funv_dot; under eq_bigr do rewrite !mxE.
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
apply/tf2mxP=>t1 t2; rewrite mx2tfK /tf2mx h2mx1 mxE/=.
by rewrite /funf_scale1 -enum_ord_eq cast_ord_comp cast_ord_id enum_rankK eq_sym.
Qed.
Lemma mx2tf0 : 0 = mx2tf (fun _ _=>0).
Proof. by apply/tf2mxP=>i j; rewrite mx2tfK /tf2mx linear0/= mxE. Qed.
Lemma mv2tv0 : 0 = mv2tv (fun _=>0).
Proof. by apply/tv2mvP=>i; rewrite mv2tvK /tv2mv linear0/= mxE. Qed.

Definition tf2mxE := (mx2tf_add, mx2tf_opp, mx2tf_scale, mx2tf_comp, mx2tf_adj, 
mx2tf_tr, mx2tf_conj, mx2tf_apply, mv2tv_add, mv2tv_opp, mv2tv_scale, mv2tv_conj, 
mx2tf1, mx2tf0, mv2tv0, mv2tv_dot, mv2tv_out).

Definition t2tv (t : T) : 'Hs T :=
    mv2tv (fun x => (x == t)%:R).

Notation "'''' b" := (t2tv b) (at level 2, format "'''' b").

(* t2tv x gives an ONB basis, i.e. computational basis *)
Lemma t2tv_dot (t1 t2 : T) : [< ''t1 ; ''t2 >] = (t1 == t2)%:R.
Proof.
by rewrite mv2tv_dot/funv_dot (bigD1 t1)//= big1=>[t3/negPf nt|];
rewrite ?nt ?conjC0 ?mul0r// eqxx conjC1 mul1r addr0.
Qed.
Lemma t2tv_ns t : [< ''t ; ''t >] == 1.
Proof. by rewrite t2tv_dot eqxx. Qed.
HB.instance Definition _ (t : T) := isNormalState.Build ('Hs T) (t2tv t) (eqP (@t2tv_ns t)).
Lemma t2tv_conj (t : T) : (''t)^*v = ''t.
Proof. by rewrite /t2tv mv2tv_conj; apply/mv2tvP=>x; rewrite /funv_conj conjC_nat. Qed.

Lemma ihb_dim : #|T| = dim ('Hs T).
Proof. by rewrite ihb_dim_cast. Qed.

HB.instance Definition _ := isONB.Build ('Hs T) T t2tv t2tv_dot ihb_dim.

(* computational measurement *)
Definition tmeas t : 'End('Hs T) := [> ''t ; ''t <].
Lemma tmeasE t : tmeas t = [> ''t ; ''t <]. Proof. by []. Qed.
Lemma tmeas_tp : trace_presv tmeas.
rewrite/trace_presv -(sumonb_out t2tv); apply/eqP; apply eq_bigr=>t _.
by rewrite/=/tmeas adj_outp outp_comp onb_dot eqxx scale1r.
Qed.

HB.instance Definition _ := isQMeasure.Build ('Hs T) ('Hs T) T tmeas tmeas_tp.

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
rewrite [LHS](onb_lfun2id t2tv)/= exchange_big/=.
by under eq_bigr do under eq_bigr do rewrite mx2tf_coord.
Qed.

End DefaultChsTypeTheory.

Ltac unfold_funfv := rewrite /funf_add /funf_opp /funf_scale /funf_comp
  /funf_adj /funf_tr /funf_conj /funf_apply /funv_add /funv_opp /funv_scale
  /funv_conj /funv_dot /funv_out /funf_scale1.

Arguments funf_scale1 {T}.

Notation "'''' b" := (t2tv b) (at level 2, format "'''' b").
Arguments t2tv {T}.
Arguments tmeas {T}.

Section TypeVectTensor.
Variable (T1 T2 : ihbFinType).

Definition idx_pair1 (i : 'I_(dim 'Hs (T1 * T2)%type)) : 'I_(dim 'Hs T1)
  := cast_ord (ihb_dim_cast T1) (enum_rank (enum_val (cast_ord (esym (ihb_dim_cast _)) i)).1).
Definition idx_pair2 (i : 'I_(dim 'Hs (T1 * T2)%type)) : 'I_(dim 'Hs T2)
  := cast_ord (ihb_dim_cast T2) (enum_rank (enum_val (cast_ord (esym (ihb_dim_cast _)) i)).2).
Definition idx_pair (i : 'I_(dim 'Hs T1)) (j : 'I_(dim 'Hs T2))
  : 'I_(dim 'Hs (T1 * T2)%type) := cast_ord (ihb_dim_cast _) (enum_rank
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

Definition tentv (u : 'Hs T1) (v : 'Hs T2) : 'Hs (T1 * T2)%type :=
  c2h (\col_i ((h2c u (idx_pair1 i) 0) * (h2c v (idx_pair2 i) 0))).

Lemma linear_tentv v1: linear (tentv v1).
Proof.
move=>a x y; apply/h2c_inj/matrixP=>i j.
by rewrite linearP/= !c2hK !mxE linearP/= !mxE mulrDr !mulrA [a * _]mulrC.
Qed.
HB.instance Definition _ (v1 : 'Hs T1) := @GRing.isLinear.Build C ('Hs T2)
  'Hs(T1 * T2)%type _ (tentv v1) (linear_tentv v1).
Lemma linear_tentvr v2 : linear (tentv^~ v2).
Proof.
move=>a x y; apply/h2c_inj/matrixP=>i j.
by rewrite linearP/= !c2hK !mxE linearP/= !mxE mulrDl !mulrA.
Qed.
HB.instance Definition _ := bilinear_isBilinear.Build C ('Hs T1) ('Hs T2)
  'Hs (T1 * T2)%type _ _ tentv (linear_tentvr, linear_tentv).

Lemma tentv_t2tv (t1 : T1) (t2 : T2) :
  tentv ''t1 ''t2 = ''(t1,t2).
Proof.
apply/h2c_inj/matrixP=>i j; rewrite !c2hK !mxE.
by rewrite !cast_ord_comp !cast_ord_id !enum_rankK -natrM mulnb -pair_eqE.
Qed.

Lemma tentv_t2tvV (t : T1 * T2) : ''t = tentv ''(t.1) ''(t.2).
Proof. by rewrite tentv_t2tv -surjective_pairing. Qed.

Lemma tentv_dot v1 v2 u1 u2 : 
  [< tentv v1 v2 ; tentv u1 u2 >] = [< v1 ; u1 >] * [< v2 ; u2 >].
Proof.
rewrite !dotp_mulmx !mxE mulr_suml. under [RHS]eq_bigr do rewrite mulr_sumr.
rewrite pair_big/= (reindex (fun i=>(idx_pair1 i,idx_pair2 i)))/=; last first.
by apply eq_bigr=>k _; rewrite/=/tentv !c2hK !mxE rmorphM mulrACA.
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
HB.instance Definition _ (F G : finType) (f : 'PONB(F;'Hs T1)) (g : 'PONB(G;'Hs T2)) := 
  isPONB.Build _ (F * G)%type (tentv_fun f g) (@tentv_ponb F G f g).
Lemma tentv_card (F G : finType) (f : 'ONB(F;'Hs T1)) (g : 'ONB(G;'Hs T2)) :
  #|{: F * G}| = dim ('Hs (T1 * T2)%type).
Proof.
by rewrite card_prod (@onb_card _ _ f) (@onb_card _ _ g) -!ihb_dim_cast/= card_prod.
Qed.
HB.instance Definition _ (F G : finType) (f : 'ONB(F;'Hs T1)) (g : 'ONB(G;'Hs T2)) :=
  isFullDim.Build ('Hs (T1 * T2)%type) (F * G)%type (tentv_fun f g) 
    (tentv_card f g).
Definition tentv_onbasis (F G : finType) (f : 'ONB(F;'Hs T1)) (g : 'ONB(G;'Hs T2))
  : onbType _ _ := (tentv_fun f g).
Definition t2tv2_onbasis := tentv_onbasis t2tv t2tv.

Lemma intro_tvl (u v : 'Hs(T1 * T2)%type) : 
  (forall u1 u2, [<tentv u1 u2 ; u >] = [<tentv u1 u2 ; v >]) <-> u = v.
Proof. split=>[H|->//]; apply/(intro_onbl t2tv2_onbasis)=>/= i; apply H. Qed.

Lemma intro_tvr (u v : 'Hs(T1 * T2)%type) : 
  (forall u1 u2, [<u ; tentv u1 u2 >] = [< v ; tentv u1 u2 >]) <-> u = v.
Proof. split=>[H|->//]; apply/(intro_onbr t2tv2_onbasis)=>/= i; apply H. Qed.

Lemma tentv_conj u v : (tentv u v)^*v = tentv (u^*v) (v^*v).
Proof. by apply/h2c_inj/matrixP=>i j; rewrite conjv.unlock !c2hK !mxE rmorphM. Qed.

Lemma tentv_ps (u : 'PS('Hs T1)) (v : 'PS('Hs T2)) :
  [< tentv u v ; tentv u v >] <= 1%:R.
Proof. by rewrite tentv_dot -[1]mul1r ler_pM// ?ps_dot// ge0_dotp. Qed.
HB.instance Definition _ (u : 'PS('Hs T1)) (v : 'PS('Hs T2)) :=
  isPartialState.Build ('Hs(T1 * T2)%type) (tentv u v) (tentv_ps u v).
Lemma tentv_ns (u : 'NS('Hs T1)) (v : 'NS('Hs T2)) :
  [< tentv u v ; tentv u v >] = 1%:R.
Proof. by rewrite tentv_dot !ns_dot mulr1. Qed.
HB.instance Definition _ (u : 'NS('Hs T1)) (v : 'NS('Hs T2)) :=
  Partial_isNormalState.Build ('Hs(T1 * T2)%type) (tentv u v) (@tentv_ns u v).

Lemma tentv_eq0 u v : tentv u v == 0 = (u == 0) || (v == 0).
Proof. by rewrite -!dotp_eq0 tentv_dot mulf_eq0. Qed.

Lemma tentv0 u : tentv u 0 = 0. Proof. exact: linear0r. Qed.
Lemma ten0tv v : tentv 0 v = 0. Proof. exact: linear0l. Qed.

End TypeVectTensor.

Notation "u '⊗t' v" := (tentv u v) : lfun_scope.
Arguments tentv_onbasis {T1 T2 F G}.
Arguments t2tv2_onbasis {T1 T2}.

Section TypeLfunTensor.
Variable (S1 S2 T1 T2: ihbFinType).

Definition tentf (f : 'Hom[S1, T1]) (g : 'Hom[S2, T2]) : 'Hom[(S1 * S2)%type, (T1 * T2)%type] :=
  mx2h (\matrix_(i, j) ((h2mx f (idx_pair1 i) (idx_pair1 j)) * 
    (h2mx g (idx_pair2 i) (idx_pair2 j)))).

Lemma linear_tentf v1: linear (tentf v1).
Proof.
by move=>a v w; apply/h2mx_inj/matrixP=>i j; 
rewrite linearP/= !mx2hK linearP !mxE mulrDr !mulrA [a * _]mulrC.
Qed.
HB.instance Definition _ (v1 : 'Hom[S1, T1]) := GRing.isLinear.Build C 'Hom('Hs S2, 'Hs T2)
  'Hom('Hs (S1 * S2)%type, 'Hs (T1 * T2)%type) *:%R (tentf v1) (linear_tentf v1).
Lemma linear_tentfr v2 : linear (tentf^~ v2).
Proof.
by move=>a v w; apply/h2mx_inj/matrixP=>i j; 
rewrite linearP/= !mx2hK linearP !mxE mulrDl !mulrA.
Qed.
HB.instance Definition _ := bilinear_isBilinear.Build C 'Hom('Hs S1, 'Hs T1) 'Hom('Hs S2, 'Hs T2)
  'Hom('Hs (S1 * S2)%type, 'Hs (T1 * T2)%type) *:%R *:%R tentf (linear_tentfr, linear_tentf).

Lemma tentf0 f : tentf f 0 = 0. Proof. exact: linear0r. Qed.
Lemma ten0tf g : tentf 0 g = 0. Proof. exact: linear0l. Qed.

Lemma tentf_apply f1 f2 v1 v2 : tentf f1 f2 (v1 ⊗t v2) = f1 v1 ⊗t f2 v2.
Proof.
apply/h2c_inj/matrixP=>i j; rewrite !applyfh !c2hK !mxE mulr_suml.
under [RHS]eq_bigr do rewrite mulr_sumr.
rewrite pair_big/= (reindex (fun i=>(idx_pair1 i,idx_pair2 i)))/=; last first.
by apply eq_bigr=>k _; rewrite/= mx2hK !mxE mulrACA.
exists (fun i=> idx_pair i.1 i.2)=>/=x _; 
by rewrite ?idx_pairK// idx_pair1K idx_pair2K -surjective_pairing.
Qed.

Lemma intro_tv (f g : 'Hom('Hs (S1 * S2)%type, 'Hs (T1 * T2)%type)) :
  (forall u1 u2, f (u1 ⊗t u2) = g (u1 ⊗t u2)) <-> f = g.
Proof. by split=>[H|->//]; apply/(intro_onb t2tv2_onbasis)=>/= i; apply H. Qed.

Lemma tentv_out u1 u2 v1 v2 : 
  tentf [> u1 ; v1 <] [> u2 ; v2 <] = [> u1 ⊗t u2; v1 ⊗t v2 <].
Proof.
by apply/intro_tv=>u v; rewrite tentf_apply 
  !outpE linearZlr/= scalerA tentv_dot.
Qed.

Lemma tentf_conj f g : (tentf f g)^C = tentf f^C g^C.
Proof.
by apply/h2mx_inj/matrixP=>i j;
rewrite conj_lfun.unlock !mx2hK !mxE rmorphM.
Qed.

End TypeLfunTensor.

Notation "f '⊗f' g" := (tentf f g) : lfun_scope.

Lemma tentf_comp (S1 S2 S3 T1 T2 T3: ihbFinType) (f1 : 'Hom[S1,S2]) (f2 : 'Hom[T1,T2])
  (g1 : 'Hom[S3,S1]) (g2 : 'Hom[T3,T1]) :
  f1 ⊗f f2 \o g1 ⊗f g2 = (f1 \o g1) ⊗f (f2 \o g2).
Proof. by apply/intro_tv=>u v; rewrite lfunE/= !tentf_apply !lfunE. Qed.

Lemma tentf_tr (T1 T2 S1 S2 : ihbFinType) (f : 'Hom[T1,T2]) (g : 'Hom[S1,S2]) : 
  ((f ⊗f g)^T = f^T ⊗f g^T)%VF.
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite tr_lfun.unlock !mx2hK !mxE. Qed.

Lemma tentf_adj (T1 T2 S1 S2 : ihbFinType) (f : 'Hom[T1,T2]) (g : 'Hom[S1,S2]) : 
  (f ⊗f g)^A = f^A ⊗f g^A.
Proof. by rewrite adjfCT tentf_conj tentf_tr -!adjfCT. Qed.

Lemma tentf11 (T1 T2 : ihbFinType) : \1 ⊗f \1 = (\1 : 'End('Hs (T1 * T2)%type)).
Proof. by apply/intro_tv=>u v; rewrite tentf_apply !lfunE/=. Qed.

(* TODO : move to quantum.v *)
Lemma i2fnorm_exist (U V : chsType) (A : 'Hom(U,V)) :
  exists2 v : U, `|v| = 1 & i2fnorm A = `|A v|.
Proof.
set mA := castmx (esym dim_proper_cast, esym dim_proper_cast) (h2mx A).
move: (i2norm_existsr mA 0)=>[mv Pv1 Pv2].
exists (c2h (castmx (dim_proper_cast, erefl) mv)).
  rewrite hnorm_l2norm c2hK; move: mv Pv1 {Pv2}; clear.
  by move: (@dim_proper_cast U)=>P; move: P {+}P=>/esym P; 
    case: _ / P => P mv; rewrite castmx_id.
rewrite hnorm_l2norm /i2fnorm applyfh !c2hK.
move: mv {Pv1} Pv2; rewrite /mA; clear; set mA := h2mx A; move: mA.
move: (@dim_proper_cast U) (@dim_proper_cast V)=>PU PV;
move: PU {+}PU PV {+}PV=>/esym PU + /esym PV;
case: _ / PU; case: _ / PV=>PU PV mA mv; 
by rewrite !castmx_id=>->.
Qed.

Lemma onb_norm (U : chsType) (F : finType) (onb : 'ONB(F; U)) (v : U) :
  `|v| = sqrtC (\sum_i `|[< onb i; v >]|^+2).
Proof.
rewrite hnormE; f_equal; rewrite {1 2}(onb_vec onb v) dotp_suml; apply eq_bigr=>i _.
rewrite dotp_sumr (bigD1 i)//= big1=>[j /negPf nji|];
rewrite dotpZl dotpZr onb_dot; first by rewrite eq_sym nji !mulr0.
by rewrite eqxx mulr1 addr0 -normCKC.
Qed.

Definition default_iso (U V : chsType) (dc : dim U = dim V) :=
  mx2h (castmx (dc, erefl) 1%:M).
Lemma default_iso_giso (U V : chsType) (dc : dim U = dim V) :
  default_iso dc \is gisolf.
Proof. by rewrite qualifE mx2hK !castmx_funE adjmx1 unitarymx1. Qed.
HB.instance Definition _ U V dc := isGisoLf.Build _ _ _ (@default_iso_giso U V dc).
Lemma default_iso_adj (U V : chsType) (dc : dim U = dim V) :
  (default_iso dc)^A = default_iso (esym dc).
Proof.
rewrite /default_iso adj_lfun.unlock mx2hK castmx_funE/= adjmx1. f_equal.
by move: dc {+}dc=>P1; case: _ / P1=>dc; rewrite !castmx_id.
Qed.

Section TypeTensorTheory.
Variable (T1 T2 : ihbFinType).
Implicit Type (x : 'End('Hs T1)) (y : 'End('Hs T2)).

Lemma tentf_ge0 x y :
  (0 :'End(_)) ⊑ x -> (0 :'End(_)) ⊑ y -> (0 :'End(_)) ⊑ x ⊗f y.
Proof.
move=>/gef0_formV[f1 Pf] /gef0_formV[g1 Pg].
by rewrite Pf Pg -tentf_comp -tentf_adj form_gef0.
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

HB.instance Definition _ := isBRegVOrder.Build C
  'End('Hs T1) 'End('Hs T2) 'End('Hs (T1 * T2)%type) (@tentf T1 T2 T1 T2)
  (fun y => additive_linear (linear_tentfr y)) (fun x => additive_linear (linear_tentf x)) 
  tentf_eq0 ptentf_rge0 ptentf_lge0.

Lemma tentf_trlf x y : \Tr (x ⊗f y) = \Tr x * \Tr y.
Proof.
rewrite (onb_trlf t2tv2_onbasis) !(onb_trlf t2tv)/=.
rewrite pair_bigV/= mulr_suml; apply eq_bigr=>i _.
rewrite mulr_sumr; apply eq_bigr=>j _.
by rewrite /tentv_fun/= tentf_apply tentv_dot.
Qed. 

(* Definition test3 (T : ihbFinType) := 
    \sum_i ((h2c (eb (cast_ord (ihb_dim_cast _) i) : 'Hs T) *m delta_mx ord0 i)).

Lemma test31 (T : ihbFinType) i j : 
  test3 T i j = (i == (cast_ord (ihb_dim_cast _) j))%:R.
Proof.
rewrite /test3 summxE (bigD1 j)//= big1 ?addr0=>[k/negPf nkj|]; 
by rewrite delta_mx_mulEl ?nkj ?mul0r// eqxx mul1r h2c_eb mxE eqxx andbT.
Qed.

Lemma test32 (T : ihbFinType) i j : 
  test3 T i j = (j == (cast_ord (esym (ihb_dim_cast _)) i))%:R.
Proof.
rewrite test31; case: eqP=>[->|].
by rewrite cast_ord_comp cast_ord_id eqxx.
move=>Pi; case: eqP=>// Pj; exfalso; apply: Pi.
by rewrite Pj cast_ord_comp cast_ord_id.
Qed.

Lemma test3_unitarymx T : test3 T \is unitarymx.
Proof.
apply/unitarymxP. rewrite -adjmxE; apply/matrixP=>i j.
rewrite !mxE (bigD1 (cast_ord (esym (ihb_dim_cast _)) i))//= big1=>[k/negPf nki|];
by rewrite test32 ?nki ?mul0r// eqxx mul1r !mxE test31 
  cast_ord_comp cast_ord_id eq_sym addr0 conjC_nat//.
Qed.

Lemma test3_adj_unitarymx T : (test3 T)^*t \is unitarymx.
Proof.
apply/unitarymxP. rewrite -adjmxE; apply/matrixP=>i j.
rewrite adjmxK !mxE (bigD1 (cast_ord (ihb_dim_cast _) j))//= big1=>[k/negPf nki|];
by rewrite test31 ?nki ?mulr0// eqxx mulr1 !mxE test32 
  cast_ord_comp cast_ord_id eq_sym addr0 conjC_nat//.
Qed. *)

Definition tentv_indexl (T3 T4 : ihbFinType) (i : 'I_(dim 'Hs T3 * dim 'Hs T4)) :
  'I_(dim 'Hs (T3 * T4)%type) := cast_ord (ihb_dim_cast _)
  (enum_rank (enum_val (cast_ord (esym (ihb_dim_cast _)) (mxtens_unindex i).1),
    enum_val (cast_ord (esym (ihb_dim_cast _)) (mxtens_unindex i).2))).

Definition tentv_indexr (T3 T4 : ihbFinType) (i : 'I_(dim 'Hs (T3 * T4)%type)) :
  'I_(dim 'Hs T3 * dim 'Hs T4) := mxtens_index 
  (cast_ord (ihb_dim_cast _) (enum_rank (enum_val (cast_ord (esym (ihb_dim_cast _)) i)).1),
   cast_ord (ihb_dim_cast _) (enum_rank (enum_val (cast_ord (esym (ihb_dim_cast _)) i)).2)).

Lemma tentv_indexlK {T3 T4} : cancel (@tentv_indexl T3 T4) (@tentv_indexr _ _).
Proof.
by move=>i; rewrite /tentv_indexl /tentv_indexr/= cast_ord_comp cast_ord_id 
  enum_rankK/= !enum_valK !cast_ord_comp !cast_ord_id mxtens_unindexK.
Qed.

Lemma tentv_indexrK {T3 T4} : cancel (@tentv_indexr T3 T4) (@tentv_indexl _ _).
Proof.
by move=>i; rewrite /tentv_indexl /tentv_indexr mxtens_indexK/= !cast_ord_comp !cast_ord_id
  !enum_rankK/= -surjective_pairing !enum_valK cast_ord_comp cast_ord_id.
Qed.

Definition tentv_mxU {T3 T4 : ihbFinType} : 'M[C]_(_, _) := 
  \matrix_(i,j) ((@tentv_indexr T3 T4 i) == j)%:R.

Lemma tentv_mxU_unitarymx (T3 T4 : ihbFinType) : @tentv_mxU T3 T4 \is unitarymx.
Proof.
apply/unitarymxP/matrixP=>i j; rewrite -adjmxE !mxE.
rewrite (bigD1 (tentv_indexr i))//= big1=>[k /negPf nki|].
by rewrite mxE eq_sym nki mul0r.
by rewrite mxE eqxx mul1r !mxE (can_eq tentv_indexrK) eq_sym conjC_nat addr0.
Qed.

Lemma tentv_mxU_adj_unitarymx (T3 T4 : ihbFinType) : (@tentv_mxU T3 T4)^*t \is unitarymx.
Proof.
apply/unitarymxP/matrixP=>i j; rewrite -adjmxE !mxE.
rewrite (bigD1 (tentv_indexl i))//= big1=>[k /negPf nki|].
by rewrite !mxE (can2_eq tentv_indexrK tentv_indexlK) nki conjC0 mul0r.
by rewrite !mxE tentv_indexlK eqxx conjC1 conjCK mul1r addr0.
Qed.

Lemma h2mx_tentf (T3 T4 : ihbFinType) (f : 'Hom[T1,T3]) (g : 'Hom[T2,T4]) :
  h2mx (f ⊗f g) = tentv_mxU *m (h2mx f *t h2mx g) *m tentv_mxU^*t.
Proof.
apply/matrixP=>i j.
rewrite mx2hK mxE mxE (bigD1 (tentv_indexr j))//= big1.
by move=>k /negPf nkj; rewrite !mxE eq_sym nkj conjC0 mulr0.
rewrite addr0 mxE (bigD1 (tentv_indexr i))//= big1.
by move=>k /negPf nkj; rewrite !mxE eq_sym nkj mul0r.
rewrite addr0 !mxE !eqxx mul1r conjC1 mulr1; do 2 f_equal.
all: by rewrite /idx_pair1 /idx_pair2 /tentv_indexr mxtens_indexK/=.
Qed.

Lemma tentf_norm (T3 T4 : ihbFinType) (f : 'Hom[T1,T3]) (g : 'Hom[T2,T4]) :
  `|f ⊗f g| = `|f| * `|g|.
Proof.
rewrite /Num.norm/= /trfnorm h2mx_tentf /trnorm schattennormUr_eq_dim 
  ?schattennormUl_eq_dim ?schattennorm_tens//.
2: apply/tentv_mxU_adj_unitarymx. 3: apply/tentv_mxU_unitarymx.
all: by rewrite -!ihb_dim_cast card_prod.
Qed.
Lemma tentf_i2fnorm (T3 T4 : ihbFinType) (f : 'Hom[T1,T3]) (g : 'Hom[T2,T4]) :
  i2fnorm (f ⊗f g) = i2fnorm f * i2fnorm g.
Proof.
rewrite /Num.norm/= /i2fnorm h2mx_tentf i2normUr_eq_dim 
  ?i2normUl_eq_dim ?i2norm_tens//.
2: apply/tentv_mxU_adj_unitarymx. 3: apply/tentv_mxU_unitarymx.
all: by rewrite -!ihb_dim_cast card_prod.
Qed.

Lemma tentf_normal (f : 'FN('Hs T1)) (g : 'FN('Hs T2)) : f ⊗f g \is normallf.
Proof. by rewrite normallfE tentf_adj !tentf_comp !normalfE. Qed.
HB.instance Definition _ (f : 'FN('Hs T1)) (g : 'FN('Hs T2)) :=
  isNormalLf.Build 'Hs(T1 * T2)%type (f ⊗f g) (@tentf_normal f g).
Lemma tentf_herm (f : 'FH('Hs T1)) (g : 'FH('Hs T2)) : f ⊗f g \is hermlf.
Proof. by rewrite hermlfE tentf_adj !hermf_adjE. Qed.
HB.instance Definition _ (f : 'FH('Hs T1)) (g : 'FH('Hs T2)) :=
  Normal_isHermLf.Build 'Hs(T1 * T2)%type (f ⊗f g) (@tentf_herm f g).
Lemma tentf_psd (f : 'F+('Hs T1)) (g : 'F+('Hs T2)) : f ⊗f g \is psdlf.
Proof. rewrite psdlfE; apply: bregv_ge0; apply/psdf_ge0. Qed.
HB.instance Definition _ (f : 'F+('Hs T1)) (g : 'F+('Hs T2)) :=
  Herm_isPsdLf.Build 'Hs(T1 * T2)%type (f ⊗f g) (@tentf_psd f g).
Lemma tentf_bound1 (T3 T4 : ihbFinType) (f : 'FB1('Hs T1, 'Hs T3))
  (g : 'FB1('Hs T2, 'Hs T4)) : f ⊗f g \is bound1lf.
Proof. by rewrite bound1lf_i2fnormE tentf_i2fnorm mulr_ile1 ?normv_ge0 ?bound1f_i2fnorm. Qed.
HB.instance Definition _ T3 T4 (f : 'FB1('Hs T1, 'Hs T3))
  (g : 'FB1('Hs T2, 'Hs T4)) := isBound1Lf.Build
  'Hs(T1 * T2)%type 'Hs(T3 * T4)%type (f ⊗f g) (@tentf_bound1 T3 T4 f g).
HB.instance Definition _ (f : 'FO('Hs T1)) (g : 'FO('Hs T2)) :=
  ObsLf.Class (PsdLf.on (f ⊗f g)) (Bound1Lf.on (f ⊗f g)).
Lemma tentf_den (f : 'FD('Hs T1)) (g : 'FD('Hs T2)) : f ⊗f g \is denlf.
Proof.
apply/denlfP; split; first by apply/tentf_psd.
by rewrite tentf_trlf -(mulr1 1) ler_pM ?psdf_trlf// denf_trlf.
Qed.
HB.instance Definition _ (f : 'FD('Hs T1)) (g : 'FD('Hs T2)) :=
  Obs_isDenLf.Build 'Hs(T1 * T2)%type (f ⊗f g) (@tentf_den f g).
Lemma tentf_den1 (f : 'FD1('Hs T1)) (g : 'FD1('Hs T2)) : f ⊗f g \is den1lf.
Proof.
apply/den1lfP; split; first by apply/is_psdlf.
by rewrite tentf_trlf !den1f_trlf mul1r.
Qed.
HB.instance Definition _ (f : 'FD1('Hs T1)) (g : 'FD1('Hs T2)) :=
  Den_isDen1Lf.Build 'Hs(T1 * T2)%type (f ⊗f g) (@tentf_den1 f g).
Lemma tentf_proj (f : 'FP('Hs T1)) (g : 'FP('Hs T2)) : f ⊗f g \is projlf.
Proof. by apply/projlfP; rewrite tentf_adj !hermf_adjE/= tentf_comp !projf_idem. Qed.
HB.instance Definition _ (f : 'FP('Hs T1)) (g : 'FP('Hs T2)) :=
  Obs_isProjLf.Build 'Hs(T1 * T2)%type (f ⊗f g) (@tentf_proj f g).
HB.instance Definition _ (f : 'FP1('Hs T1)) (g : 'FP1('Hs T2)) := 
  Proj1Lf.Class (ProjLf.on (f ⊗f g)) (Den1Lf.on (f ⊗f g)).

Lemma tentf_iso (T3 T4 : ihbFinType) (f : 'FI('Hs T1, 'Hs T3))
  (g : 'FI('Hs T2, 'Hs T4)) : f ⊗f g \is isolf.
Proof. by rewrite isolfE tentf_adj tentf_comp !isofE tentf11. Qed.
HB.instance Definition _ (T3 T4 : ihbFinType) (f : 'FI('Hs T1, 'Hs T3))
  (g : 'FI('Hs T2, 'Hs T4)) :=
  Bound1_isIsoLf.Build 'Hs(T1 * T2)%type 'Hs(T3 * T4)%type (f ⊗f g) (tentf_iso f g).
Lemma tentf_giso (T3 T4 : ihbFinType) (f : 'FGI('Hs T1, 'Hs T3))
  (g : 'FGI('Hs T2, 'Hs T4)) : f ⊗f g \is gisolf.
Proof. by rewrite gisolfE tentf_adj !tentf_comp !gisofEl !gisofEr !tentf11 !eqxx. Qed.
HB.instance Definition _ (T3 T4 : ihbFinType) (f : 'FGI('Hs T1, 'Hs T3))
  (g : 'FGI('Hs T2, 'Hs T4)) :=
  Iso_isGisoLf.Build 'Hs(T1 * T2)%type 'Hs(T3 * T4)%type (f ⊗f g) (tentf_giso f g).

End TypeTensorTheory.

Section TentvfLinear.
Variable (T1 T2 : ihbFinType).

Lemma tentv00 : tentv 0 0 = (0 : 'Hs (T1 * T2)%type).
Proof. exact: linear0l. Qed.
Lemma tentvNl (v: 'Hs T2) (u: 'Hs T1) : (-u) ⊗t v = - (u ⊗t v).
Proof. exact: linearNl. Qed.
Lemma tentvBl (w: 'Hs T2) (u v: 'Hs T1) : (u-v) ⊗t w = u ⊗t w - v ⊗t w.
Proof. exact: linearBl. Qed.
Lemma tentvDl (w: 'Hs T2) (u v: 'Hs T1) : (u+v) ⊗t w = u ⊗t w + v ⊗t w.
Proof. exact: linearDl. Qed.
Lemma tentvZl (v: 'Hs T2) (c: C) (u: 'Hs T1) : (c*:u) ⊗t v = c *: (u ⊗t v).
Proof. exact: linearZl_LR. Qed.
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
Proof. exact: linearZ_LR. Qed.
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
Proof. by rewrite linearZl_LR linearZr. Qed.

Variable (T3 T4 : ihbFinType).
Implicit Type (f : 'Hom[T1,T2]) (g : 'Hom[T3,T4]).
Lemma tentf00 : tentf 0 0 = (0 : 'Hom[(T1 * T1)%type, (T2 * T4)%type]).
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
Proof. exact: linearZl_LR. Qed.
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
Lemma tentf_suml g I r (P: pred I) (E: I -> 'Hom[T1,T2]) :
 (\sum_(i <- r | P i) E i) ⊗f g = \sum_(i <- r | P i) (E i ⊗f g).
Proof. exact: linear_suml. Qed.
Lemma tentf_sumr f I r (P: pred I) (E: I -> 'Hom[T3,T4]) :
 f ⊗f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (f ⊗f E i).
Proof. exact: linear_sumr. Qed.

Lemma tentfZS (a : C) f g :
  (a *: f) ⊗f g = f ⊗f (a *: g).
Proof. by rewrite linearZl_LR linearZr. Qed.
End TentvfLinear.

(* tensor subspace *)
Section Tenth.
Variable (T1 T2 : ihbFinType).
Local Open Scope hspace_scope.

Definition tenth (A : {hspace 'Hs T1}) (B : {hspace 'Hs T2}) : {hspace 'Hs (T1 * T2)%type}
  := HSType (tentf A B).
Notation "A '`⊗`' B" := (tenth A B) : hspace_scope.

Lemma leh_tenth2l A : {homo (tenth A) : y z / y `<=` z}.
Proof.
move=>B C; rewrite !leh_lef !hsE/==>P.
by rewrite lev_wpbreg2l// psdf_ge0.
Qed.

Lemma leh_tenth2r A : {homo (tenth^~ A) : y z / y `<=` z}.
Proof.
move=>B C; rewrite !leh_lef !hsE/==>P.
by rewrite lev_wpbreg2r// psdf_ge0.
Qed.

Lemma leh_tenth2 A B C D : A `<=` B -> C `<=` D -> A `⊗` C `<=` B `⊗` D.
Proof. by move=>/(leh_tenth2r C)=>P1/(leh_tenth2l B); apply: le_trans. Qed.

(* Lemma tenthUl A B C : (A `⊗` C) `|` (B `⊗` C) = (A `|` B) `⊗` C. *)

Lemma tenth0 A : A `⊗` `0` = `0`.
Proof. by apply/hspacelfP; rewrite !hsE/= hsE/= tentf0. Qed.
Lemma ten0th A : `0` `⊗` A = `0`.
Proof. by apply/hspacelfP; rewrite !hsE/= hsE/= ten0tf. Qed.

Lemma tenth_hline u v : <[u]> `⊗` <[v]> = <[u ⊗t v]>.
Proof.
rewrite !hline_def; apply/hspacelfP; rewrite !hsE/= !hsE/=.
by rewrite tentfZl tentfZr scalerA tentv_norm exprMn -invfM tentv_out.
Qed.

End Tenth.

Section SwapTypeTensor.
Implicit Type (S T : ihbFinType).

Definition swaptf T1 T2 : 'Hom[(T1 * T2)%type, (T2 * T1)%type] :=
  mx2h (\matrix_(i,j) ((idx_pair1 i == idx_pair2 j) 
    && (idx_pair2 i == idx_pair1 j))%:R).
Global Arguments swaptf {T1 T2}.

Lemma swaptfEtv (T1 T2 : ihbFinType) u v :
  swaptf (u ⊗t v) = v ⊗t u :> 'Hs(T2 * T1)%type.
Proof.
apply/h2c_inj/matrixP=>i j; rewrite applyfh !c2hK mx2hK !mxE.
rewrite (bigD1 (idx_pair (idx_pair2 i) (idx_pair1 i)))//= big1=>[k|];
rewrite !mxE; last first.
by rewrite idx_pair1K idx_pair2K !eqxx mul1r addr0 mulrC.
case: eqP=>//; do 2 (case: eqP; rewrite/= ?(mulr0, mul0r)//).
by move=>->->; rewrite idx_pairK.
Qed.

Lemma swaptfEt (T1 T2 : ihbFinType) (t : (T1 * T2)%type) :
  swaptf ''t  = ''(t.2,t.1).
Proof. by rewrite tentv_t2tvV swaptfEtv tentv_t2tv. Qed.

Definition swaptf_tf S1 S2 T1 T2 f g :
  (swaptf \o f ⊗f g) \o swaptf = g ⊗f f :> 'Hom[(S1 * S2)%type, (T1 * T2)%type].
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
by rewrite/=/tentv_fun/= adj_dotEr !swaptfEtv !tentv_dot mulrC.
Qed.

Lemma swaptf_tr T1 T2 : (@swaptf T1 T2)^T = swaptf.
Proof. by rewrite trfAC swaptf_adj swaptf_conj. Qed.

Lemma swaptf_unitary T : @swaptf T T \is unitarylf.
Proof.
by apply/unitarylfP; rewrite swaptf_adj -tentf11 -swaptf_tf tentf11 comp_lfun1r.
Qed.
HB.instance Definition _ T := isUnitaryLf.Build
  'Hs(T * T)%type (@swaptf T T) (@swaptf_unitary T).

Lemma swaptfK T1 T2 (u : 'Hs (T1 * T2)%type) : swaptf (swaptf u) = u.
Proof.
rewrite (onb_vec t2tv2_onbasis u) !linear_sum; apply eq_bigr=>i _.
by rewrite/= !linearZ/=; f_equal; rewrite /tentv_fun !swaptfEtv.
Qed.
Global Arguments swaptfK {T1 T2}.

Lemma swaptf_inj T1 T2 : injective (@swaptf T1 T2).
Proof. exact: (can_inj swaptfK). Qed.
Global Arguments swaptf_inj {T1 T2}.

Lemma swaptf_dot T1 T2 (u v : 'Hs (T1 * T2)%type) : 
  [< swaptf u ; swaptf v >] = [< u ; v >].
Proof. by rewrite -adj_dotEl swaptf_adj swaptfK. Qed.

Lemma swaptf_norm T1 T2 (u : 'Hs (T1 * T2)%type) : `|swaptf u| = `|u|.
Proof. by rewrite !hnormE swaptf_dot. Qed.

Lemma swaptf_out T1 T2 (u v : 'Hs (T1 * T2)%type) : 
  swaptf \o [> u ; v <] \o swaptf = [> swaptf u ; swaptf v <].
Proof. by rewrite outp_compr outp_compl swaptf_adj. Qed.

End SwapTypeTensor.

(* TODO : move to mcextra.v *)
Lemma prodr_le1 (R : numDomainType) I r (P : pred I) (E : I -> R) :
  (forall i : I, P i -> 0 <= E i <= 1) -> \prod_(i <- r | P i) E i <= 1.
Proof.
move=>Pi; suff: 0 <= \prod_(i <- r | P i) E i <= 1 by move=>/andP[].
elim/big_rec: _ =>[|i x /Pi /andP[] PE0 PE1 /andP[] Px0 Px1];
  first by rewrite ler01 lexx.
apply/andP; split; by rewrite ?mulr_ge0 ?mulr_ile1.
Qed.

(* packing tuples *)
(* easy use: under eq_tnth do rewrite ... *)
(* remark : tentv_tuple is built from function rather than tuple *)
(* since unification of canonical structure cannot penetrate the tuple *)
Section TentvTuple.
Variable (n : nat) (T : ihbFinType).

Definition idx_tuplei (i : 'I_(dim 'Hs (n.-tuple T))) j : 'I_(dim 'Hs T)
  := cast_ord (ihb_dim_cast T) (enum_rank 
    ((enum_val (cast_ord (esym (ihb_dim_cast _)) i)) ~_ j)).
Definition idx_tuple (fi : 'I_n -> 'I_(dim 'Hs T)) : 'I_(dim 'Hs (n.-tuple T))
  := cast_ord (ihb_dim_cast _) (enum_rank [tuple enum_val (cast_ord (esym (ihb_dim_cast _)) (fi i)) | i < n]).

Lemma idx_tupleiK (fi : 'I_n -> 'I_(dim 'Hs T)) i :
  idx_tuplei (idx_tuple fi) i = fi i.
Proof.
by rewrite /idx_tuplei /idx_tuple cast_ord_comp cast_ord_id 
  enum_rankK tnthE enum_valK cast_ord_comp cast_ord_id.
Qed.
Lemma idx_tupleK (i : 'I_(dim 'Hs (n.-tuple T))) :
  idx_tuple (idx_tuplei i) = i.
Proof.
apply/eqP; rewrite eq_sym /idx_tuple /idx_tuplei -enum_ord_eq; apply/eqP.
by apply eq_from_tnth=>j; rewrite tnthE cast_ord_comp cast_ord_id enum_rankK.
Qed.
Lemma idx_tupleP f g : idx_tuple f = idx_tuple g <-> f =1 g.
Proof.
split=>[P x|P]; first by rewrite -idx_tupleiK P idx_tupleiK.
rewrite /idx_tuple; do 2 f_equal; by under eq_mktuple do rewrite P.
Qed.

Definition tentv_tuple (v : 'I_n -> ('Hs T)) : 'Hs (n.-tuple T) 
  := c2h (\col_i (\prod_j h2c (v j) (idx_tuplei i j) 0)).

Lemma eq_tentv_tuple (u v : 'I_n -> 'Hs T) :
  u =1 v -> tentv_tuple u = tentv_tuple v.
Proof.
move=>P; apply/h2c_inj/matrixP=>i j.
by rewrite !c2hK !mxE; under eq_bigr do rewrite P.
Qed.

Lemma tentv_tuple_dot (u v : 'I_n -> ('Hs T)) :
  [< tentv_tuple u ; tentv_tuple v >] = \prod_i [< u i ; v i >].
Proof.
rewrite dotp_mulmx !c2hK mxE.
under eq_bigr do rewrite !mxE rmorph_prod -big_split/=.
under [RHS]eq_bigr do rewrite dotp_mulmx mxE.
rewrite bigA_distr_bigA/= (reindex (fun i=>[ffun j => idx_tuplei i j])).
exists (fun i : {ffun 'I_n -> _}=> idx_tuple i)=>x _.
by rewrite -[RHS]idx_tupleK; apply/idx_tupleP=>i; rewrite ffunE.
by apply/ffunP=>i; rewrite ffunE idx_tupleiK.
by do 2 apply eq_bigr=>? _; rewrite ffunE !mxE.
Qed.

Lemma tentv_tuple_norm (u : 'I_n -> ('Hs T)) :
  `|tentv_tuple u| = \prod_i `|u i|.
Proof.
rewrite hnormE tentv_tuple_dot sqrt_prod=>[i _|]; last apply eq_bigr=>i _;
by rewrite dotp_norm ?sqrCK// exprn_ge0//.
Qed.

Lemma t2tv_tuple (t : n.-tuple T) : 
  t2tv t = tentv_tuple (fun i => ''(t ~_ i)).
Proof.
rewrite{1}/t2tv /tentv_tuple /mv2tv; f_equal; apply/matrixP=>i j.
rewrite !mxE.
case: eqP=>[/eqP|/eqP/tuple_neqP[k/negPf Pk]].
rewrite enum_ord_eq=>/eqP->; under eq_bigr do rewrite/= c2hK mxE
 cast_ord_comp cast_ord_id enum_rankK cast_ord_comp cast_ord_id enum_rankK eqxx.
 by rewrite prodr_const expr1n.
by rewrite (bigD1 k)//= /t2tv/mv2tv c2hK mxE cast_ord_comp cast_ord_id enum_rankK Pk mul0r.
Qed.

Lemma tentv_tuple_conj (t : 'I_n -> ('Hs T)) : 
  (tentv_tuple t)^*v = tentv_tuple (fun i=>(t i)^*v).
Proof.
apply/h2c_inj/matrixP=>i j; rewrite conjv.unlock !c2hK !mxE rmorph_prod;
by apply eq_bigr=>k _; rewrite c2hK mxE.
Qed.

Lemma tentv_tupleZ (t : 'I_n -> ('Hs T)) (fc : 'I_n -> C) :
  tentv_tuple (fun i => fc i *: t i) = \prod_i (fc i) *: tentv_tuple t.
Proof.
apply/(intro_onbl t2tv)=>i/=; rewrite t2tv_tuple dotpZr.
by rewrite !tentv_tuple_dot -big_split/=; apply eq_bigr=>j _; rewrite dotpZr.
Qed.

Lemma tentv_tuple_ps (t : 'I_n -> 'PS('Hs T)) :
  [< tentv_tuple t ; tentv_tuple t >] <= 1.
Proof.
rewrite tentv_tuple_dot; apply: prodr_le1=>/= i _.
by rewrite ps_dot ge0_dotp.
Qed.
HB.instance Definition _ (t : 'I_n -> 'PS('Hs T)) := isPartialState.Build
  'Hs(n.-tuple T) (tentv_tuple t) (tentv_tuple_ps t).
Lemma tentv_tuple_ns (t : 'I_n -> 'NS('Hs T)) :
  [< tentv_tuple t ; tentv_tuple t >] = 1.
Proof. by rewrite tentv_tuple_dot big1// =>i _; rewrite ns_dot. Qed.
HB.instance Definition _ (t : 'I_n -> 'NS('Hs T)) := 
  Partial_isNormalState.Build 'Hs(n.-tuple T) (tentv_tuple t) (tentv_tuple_ns t).

Definition tentv_tuple_fun (G : finType) (f : 'I_n -> G -> 'Hs T) :=
  (fun i : n.-tuple G => tentv_tuple (fun k => f k (i ~_ k))).
Lemma tentv_tuple_ponb (G : finType) (f : 'I_n -> 'PONB(G;'Hs T)) i j :
  [< tentv_tuple_fun f i ; tentv_tuple_fun f j >] = (i == j)%:R.
Proof.
rewrite/tentv_tuple_fun tentv_tuple_dot.
case: eqP=>[->|/eqP]; first by rewrite big1// =>k _; rewrite ns_dot.
by move=>/tuple_neqP[k/negPf nk]; rewrite (bigD1 k)//= ponb_dot nk mul0r.
Qed.
HB.instance Definition _ (G : finType) (f : 'I_n -> 'PONB(G;'Hs T)) := 
  isPONB.Build _ (n.-tuple G) (tentv_tuple_fun f) (tentv_tuple_ponb f).
Lemma tentv_tuple_card (G : finType) (f : 'I_n -> 'ONB(G;'Hs T)) : 
  #|{: n.-tuple G}| = dim ('Hs (n.-tuple T)).
Proof.
rewrite -ihb_dim_cast !card_tuple. case: n f; first by rewrite !expn0.
by move=>m f; rewrite (@onb_card _ _ (f ord0)) ihb_dim_cast.
Qed.
HB.instance Definition _ (G : finType) (f : 'I_n -> 'ONB(G;'Hs T)) :=
  isFullDim.Build 'Hs(n.-tuple T) (n.-tuple G) (tentv_tuple_fun f) (tentv_tuple_card f).
Definition tentv_tuple_onbasis (G : finType) (f : 'I_n -> 'ONB(G;'Hs T))
  : onbType _ _ := (tentv_tuple_fun f).
Definition tentvtv_tuple_onbasis := tentv_tuple_onbasis (fun i=>t2tv).

End TentvTuple.

Section TentfTuple.
Implicit Type (T : ihbFinType).

Definition tentf_tuple T1 T2 n (f : 'I_n -> ('Hom[T1,T2])) : 'Hom[n.-tuple T1, n.-tuple T2]
  := mx2h (\matrix_(i,j) (\prod_k h2mx (f k) (idx_tuplei i k) (idx_tuplei j k))).

Lemma eq_tentf_tuple T1 T2 n (u v : 'I_n -> ('Hom[T1,T2])) :
  u =1 v -> tentf_tuple u = tentf_tuple v.
Proof.
move=>P; apply/h2mx_inj/matrixP=>i j.
by rewrite !mx2hK !mxE; under eq_bigr do rewrite P.
Qed.

Lemma tentf_tuple_apply T1 T2 n (f : 'I_n -> ('Hom[T1,T2])) (v : 'I_n -> ('Hs T1)) :
  tentf_tuple f (tentv_tuple v) = tentv_tuple (fun i=> f i (v i)).
Proof.
apply/h2c_inj/matrixP=>i j; rewrite applyfh !c2hK !mx2hK !mxE.
under [RHS]eq_bigr do rewrite applyfh c2hK mxE.
rewrite bigA_distr_bigA/= (reindex (fun i=>[ffun j => idx_tuplei i j])).
exists (fun i : {ffun 'I_n -> _}=> idx_tuple i)=>x _.
by rewrite -[RHS]idx_tupleK; apply/idx_tupleP=>k; rewrite ffunE.
by apply/ffunP=>k; rewrite ffunE idx_tupleiK.
apply eq_bigr=>k _; rewrite !mxE -big_split/=; 
by apply eq_bigr=>l _; rewrite ffunE.
Qed.

Lemma tentf_tuple_out T1 T2 n (u : 'I_n -> ('Hs T1)) (v : 'I_n -> ('Hs T2)) : 
  tentf_tuple (fun i=> [> u i ; v i <])
  = [> tentv_tuple u ; tentv_tuple v <].
Proof.
apply/(intro_onb t2tv)=>i.
rewrite/= t2tv_tuple tentf_tuple_apply outpE.
under eq_tentv_tuple do rewrite outpE.
rewrite tentv_tupleZ tentv_tuple_dot; f_equal; apply eq_bigr=>j _.
Qed.

Lemma tentf_tuple_adj T1 T2 n (f : 'I_n -> ('Hom[T1,T2])) :
  (tentf_tuple f)^A = tentf_tuple (fun i=> (f i)^A).
Proof.
by apply/h2mx_inj/matrixP=>i j; rewrite adj_lfun.unlock !mx2hK !mxE rmorph_prod;
apply eq_bigr => k _; rewrite mx2hK !mxE.
Qed.

Lemma tentf_tuple_conj T1 T2 n (f : 'I_n -> ('Hom[T1,T2])) :
  (tentf_tuple f)^C = tentf_tuple (fun i=> (f i)^C).
Proof.
apply/h2mx_inj/matrixP=>i j; rewrite conj_lfun.unlock /= !mx2hK !mxE rmorph_prod; 
by apply eq_bigr => k _; rewrite mx2hK !mxE.
Qed.

Lemma tentf_tuple_tr T1 T2 n (f : 'I_n -> ('Hom[T1,T2])) :
  (tentf_tuple f)^T = tentf_tuple (fun i=> (f i)^T).
Proof.
apply/h2mx_inj/matrixP=>i j; rewrite tr_lfun.unlock /= !mx2hK !mxE; 
by apply eq_bigr => k _; rewrite mx2hK !mxE.
Qed.

Lemma tentf_tuple_comp T1 T2 T3 n (f : 'I_n -> ('Hom[T1,T2])) (g : 'I_n -> ('Hom[T3,T1])) :
  (tentf_tuple f) \o (tentf_tuple g) = tentf_tuple (fun i=> f i \o g i).
Proof.
apply/(intro_onb t2tv)=>i.
rewrite/= t2tv_tuple tentf_tuple_apply lfunE/= !tentf_tuple_apply.
by under [RHS]eq_tentv_tuple do rewrite lfunE.
Qed.

End TentfTuple.

Section TentfTuplePerm.
Variable (T : ihbFinType) (n : nat).

Definition permtf (s : 'S_n) : 'End[n.-tuple T] :=
  mx2h (\matrix_(i, j) 
    (idx_tuple (fun k=> (idx_tuplei i) ((s^-1)%g k)) == j)%:R).

Lemma permtfEtv (s : 'S_n) (v : 'I_n -> ('Hs T)) :
  permtf s (tentv_tuple v) = tentv_tuple (fun i=> v (s i)).
Proof.
apply/h2c_inj/matrixP=>i j.
rewrite applyfh !c2hK !mx2hK !mxE (bigD1 (idx_tuple (fun k=> (idx_tuplei i) ((s^-1)%g k))))
  //=[X in _ + X]big1=>[k/negPf nk|]; rewrite !mxE ?eqxx 1?eq_sym ?nk ?mul0r//.
rewrite addr0 mul1r (reindex_inj (@perm_inj _ s)).
by apply eq_bigr=>k _; rewrite idx_tupleiK permK.
Qed.

Lemma permtfEt (s : 'S_n) t :
  permtf s ''t = ''[tuple i=> t ~_ (s i)].
Proof.
by rewrite !t2tv_tuple permtfEtv; under [RHS]eq_tentv_tuple do rewrite tnthE.
Qed.

Lemma permtf_conj (s : 'S_n) :
  (permtf s)^C = permtf s.
Proof.
by apply/h2mx_inj/matrixP=>i j;
rewrite conj_lfun.unlock !mx2hK !mxE conjC_nat.
Qed.

Lemma permtf_tr (s : 'S_n) :
  (permtf s)^T = permtf (s^-1)%g.
Proof.
apply/h2mx_inj/matrixP=>i j; rewrite tr_lfun.unlock !mx2hK !mxE invgK.
by case: eqP=>[ <-|]; case: eqP=>[//<-|//]P; exfalso; apply P;
rewrite -[RHS]idx_tupleK; apply/idx_tupleP=>k; rewrite idx_tupleiK ?permK ?permKV.
Qed.

Lemma permtf_adj (s : 'S_n) :
  (permtf s)^A = permtf (s^-1)%g.
Proof. by rewrite adjfCT permtf_conj permtf_tr. Qed.

Lemma permtf_comp (s1 s2 : 'S_n) :
  (permtf s1) \o (permtf s2) = permtf (s1 * s2)%g.
Proof.
apply/(intro_onb t2tv)=>i; rewrite/= lfunE/= !permtfEt.
by under eq_tnth do rewrite tnthE -permM.
Qed.

Lemma permtf1 : (permtf 1) = \1.
Proof.
apply/(intro_onb t2tv)=>i; rewrite/= lfunE/= !permtfEt.
by f_equal; apply eq_from_tnth=>j; rewrite tnthE perm1.
Qed.

Lemma permtf_nseq (s : 'S_n) (v : 'Hs T) :
  permtf s (tentv_tuple (fun i : 'I_n => v)) = (tentv_tuple (fun i : 'I_n => v)).
Proof.
rewrite permtfEtv; f_equal; apply eq_from_tnth=>i.
Qed.

Lemma permtf_nseqt (s : 'S_n) (t : T) :
  permtf s ''(nseq_tuple n t) = ''(nseq_tuple n t).
Proof.
suff ->: ''(nseq_tuple n t) = tentv_tuple (fun i => ''t) by apply: permtf_nseq.
by rewrite t2tv_tuple; under eq_tentv_tuple do rewrite tnth_nseq.
Qed.

Lemma permtf_unitary (s : 'S_n) : 
  permtf s \is unitarylf.
Proof. by apply/unitarylfP; rewrite permtf_adj permtf_comp mulVg permtf1. Qed.
HB.instance Definition _ (s : 'S_n) := isUnitaryLf.Build
  'Hs(n.-tuple T) (permtf s) (@permtf_unitary s).

End TentfTuplePerm.

Require Import prodvect tensor.
Section TenTupleMultilinear.
Variable (n : nat).
Implicit Type (T : ihbFinType).

Definition tentv_tmv T (v : mvector (fun i : 'I_n =>'Hs T)) := 
    tentv_tuple v.
Definition tentf_tmv T1 T2 (f : mvector (fun i : 'I_n => 'Hom[T1,T2])) := 
    tentf_tuple f.

Lemma tentv_tmvE T (v : 'I_n -> ('Hs T)) :
  tentv_tuple v = tentv_tmv (\mvector_(i : 'I_n) v i).
Proof. by rewrite/tentv_tmv; apply eq_tentv_tuple=>i; rewrite mvE. Qed.
Lemma tentv_tmvEV T (v : mvector (fun i : 'I_n =>'Hs T)) :
  tentv_tuple v = tentv_tmv v.
Proof. by []. Qed.

Lemma tentf_tmvE T1 T2 (f : 'I_n -> ('Hom[T1, T2])) :
  tentf_tuple f = tentf_tmv (\mvector_(i : 'I_n) f i).
Proof. by rewrite/tentf_tmv; apply eq_tentf_tuple=>i; rewrite mvE. Qed.
Lemma tentf_tmvEV T1 T2 (f : mvector (fun i : 'I_n => 'Hom[T1,T2])) :
  tentf_tuple f = tentf_tmv f.
Proof. by []. Qed.

(* then tentv_dmv and tentf_dmv are mxlinear *)
Lemma tentv_tmv_mlinear T : mlinear (@tentv_tmv T).
Proof.
move=>i a x v; apply/(intro_onbl t2tv)=>y.
rewrite/= t2tv_tuple /tentv_tmv linearPr/= !tentv_tuple_dot.
rewrite [LHS](bigD1 i)//= [X in _ = _ + X](bigD1 i)//= 
  [in LHS](eq_bigr (fun j=>[< ''(y ~_ j); x j >])); last first.
rewrite [X in _ = _ + _ * X](eq_bigr (fun j=>[< ''(y ~_ j); x j >])); last first.
rewrite mvE !msetii mvE eqxx linearP/= mulrDl -mulrA; do 2 f_equal.
by rewrite [RHS](bigD1 i).
all: move=>j; rewrite eq_sym=>/negPf P; 
  by rewrite ?mset_ne 2?mvE ?P ?mset_ne ?P ?mvE ?addr0 ?scale1r.
Qed.

Lemma tentf_tmv_mlinear T1 T2 : mlinear (@tentf_tmv T1 T2).
Proof.
move=>i a x v; apply/(intro_onb t2tv)=>y.
rewrite/= t2tv_tuple /tentf_tmv lfunE/= lfunE/= !tentf_tuple_apply.
apply/(intro_onbl t2tv)=>z.
rewrite/= t2tv_tuple linearPr/= !tentv_tuple_dot.
rewrite [LHS](bigD1 i)//= [X in _ = _ + X](bigD1 i)//= 
  [in LHS](eq_bigr (fun j=>[< ''(z ~_ j); x j ''(y ~_ j) >])); last first.
rewrite [X in _ = _ + _ * X](eq_bigr (fun j=>[< ''(z ~_ j); x j ''(y ~_ j) >])); last first.
rewrite mvE !msetii mvE eqxx lfunE/= lfunE/= linearP/= mulrDl -mulrA.
do 2 f_equal. by rewrite [RHS](bigD1 i).
all: move=>j; rewrite eq_sym=>/negPf P; 
  by rewrite ?mset_ne 2?mvE ?P ?mset_ne ?P ?mvE ?addr0 ?scale1r.
Qed.

End TenTupleMultilinear.

Lemma tentf_tuple1 (n : nat) (T : ihbFinType) : 
  tentf_tuple (fun i : 'I_n=> \1 : 'End[T]) = \1.
Proof.
apply/(intro_onb t2tv)=>i.
rewrite/= t2tv_tuple tentf_tuple_apply lfunE/=;
by under eq_tentv_tuple do rewrite lfunE.
Qed.

Definition tentv_tuple_tensU {n} {T : ihbFinType} : 'Hom(_,_) :=
  \sum_i\sum_(f : n.-tuple T) [> tentv ''i (tentv_tuple (fun i => ''(f ~_ i))); 
    tentv_tuple (fcons ''i (fun i => ''(f ~_ i))) <].
Lemma tentv_tuple_tensU_gios n T : (@tentv_tuple_tensU n T) \is gisolf.
Proof.
rewrite -gisolf_adj; apply/isolf_giso_dim; last first.
  by rewrite -!ihb_dim_cast card_prod !card_tuple expnS.
apply/isolfP; rewrite adjfK /tentv_tuple_tensU adjf_sum.
rewrite -tentf11 -(sumonb_out t2tv) !linear_suml/=; apply eq_bigr=>i _. 
rewrite linear_sumr/= (bigD1 i)//= [X in _ + X]big1=>[j /negPf nji|];
rewrite adjf_sum linear_suml/=.
  rewrite big1// =>a _; rewrite linear_sumr big1// =>b _ /=;
  by rewrite adj_outp outp_comp tentv_tuple_dot big_ord_recl 
    !fcons0 onb_dot eq_sym nji mul0r scale0r.
rewrite addr0 -(sumonb_out t2tv) linear_sumr /=; apply eq_bigr=>j _.
rewrite linear_sumr/= (bigD1 j)//= big1=>[k /tuple_neqP [ni /negPf nkj]|];
rewrite adj_outp outp_comp tentv_tuple_dot big_ord_recl !fcons0 ns_dot mul1r;
under eq_bigr do rewrite !fconsE ?ns_dot.
by rewrite (bigD1 ni)//= onb_dot eq_sym nkj mul0r scale0r.
by rewrite prodr_const expr1n scale1r -tentv_out addr0 -t2tv_tuple.
Qed.
HB.instance Definition _ n T := isGisoLf.Build _ _ 
  (@tentv_tuple_tensU n T) (@tentv_tuple_tensU_gios n T).
Lemma tentv_tuple_cons n (T : ihbFinType) x (f : 'I_n -> 'Hs T) : 
  tentv_tuple_tensU (tentv_tuple (fcons x f)) = tentv x (tentv_tuple f).
Proof.
apply/(intro_onbl t2tv)=>[[i j]].
rewrite -adj_dotEl /tentv_tuple_tensU adjf_sum sum_lfunE (bigD1 i)//= 
  [X in _ + X]big1=>[k /negPf nki|]; rewrite adjf_sum sum_lfunE.
by rewrite big1// =>? _; rewrite adj_outp outpE 
  -tentv_t2tv tentv_dot onb_dot nki mul0r scale0r.
rewrite addr0 (bigD1 j)//= big1=>[k/negPf nkj|];
rewrite -t2tv_tuple adj_outp outpE -tentv_t2tv tentv_dot !ns_dot 
  ?onb_dot ?nkj ?mulr0 ?scale0r// mul1r scale1r addr0 t2tv_tuple 
  tentv_dot !tentv_tuple_dot big_ord_recl !fcons0.
by under [in LHS]eq_bigr do rewrite !fconsE.
Qed.
Lemma tentf_tuple_cons n (T1 T2 : ihbFinType) x (f : 'I_n -> 'Hom[T1,T2]) : 
  tentv_tuple_tensU \o tentf_tuple (fcons x f) \o tentv_tuple_tensU^A = tentf x (tentf_tuple f).
Proof.
rewrite -[RHS]comp_lfun1l -(gisofEr tentv_tuple_tensU) -!comp_lfunA; f_equal.
apply/(intro_onb t2tv)=>[[i j]].
rewrite !lfunE/= -tentv_t2tv t2tv_tuple -{1}tentv_tuple_cons gisofKEl 
  tentf_apply !tentf_tuple_apply -[in RHS]tentv_tuple_cons gisofKEl.
apply/eq_tentv_tuple=>k; case: (unliftP ord0 k)=>/=[l |]->;
by rewrite ?fconsE// !fcons0.
Qed.
Lemma tentf_tuple_consV n (T1 T2 : ihbFinType) x (f : 'I_n -> 'Hom[T1,T2]) : 
  tentf_tuple (fcons x f) = tentv_tuple_tensU^A \o tentf x (tentf_tuple f) \o tentv_tuple_tensU.
Proof. by rewrite -tentf_tuple_cons !comp_lfunA gisofEl gisofKl comp_lfun1l. Qed.

Lemma tentf_tuple_norm n T T' (f : 'I_n -> 'Hom[T, T']) :
  `|tentf_tuple f| = \prod_i `|f i|.
Proof.
elim: n f.
  move=>f; rewrite big_ord0 /Num.norm/= /trfnorm mx2hK.
  under eq_mx do rewrite big_ord0.
  have P1: 1 = dim 'Hs (0.-tuple T') by rewrite -ihb_dim_cast card_tuple expn0.
  have P2: 1 = dim 'Hs (0.-tuple T) by rewrite -ihb_dim_cast card_tuple expn0.
  case: _ / P1; case: _ / P2.
  set t := \matrix_(_,_) _.
  have ->: t = 1%:M by apply/matrixP=>i j; rewrite /t !mxE !ord1 eqxx.
  rewrite /trnorm /schattennorm svd_d_const /pnorm root1C pair_bigV/= big_ord1.
  under eq_bigr do rewrite mxE normr1 normr1 expr1n.
  by rewrite minn_id big_ord1.
move=>n IH f; case: (fconsP f)=>x g.
rewrite big_ord_recl/= fcons0. under eq_bigr do rewrite fconsE.
by rewrite -IH -tentf_norm -tentf_tuple_cons trfnormUr trfnormUl.
Qed.

Lemma tentf_tuple_i2fnorm n T T' (f : 'I_n -> 'Hom[T, T']) :
  i2fnorm (tentf_tuple f) = \prod_i i2fnorm (f i).
Proof.
elim: n f.
  move=>f; rewrite big_ord0 /i2fnorm mx2hK.
  under eq_mx do rewrite big_ord0.
  have P1: 1 = dim 'Hs (0.-tuple T') by rewrite -ihb_dim_cast card_tuple expn0.
  have P2: 1 = dim 'Hs (0.-tuple T) by rewrite -ihb_dim_cast card_tuple expn0.
  case: _ / P1; case: _ / P2.
  set t := \matrix_(_,_) _.
  have ->: t = 1%:M by apply/matrixP=>i j; rewrite /t !mxE !ord1 eqxx.
  rewrite /i2norm svd_d_const.
  under eq_bigr do rewrite mxE normr1.
  by rewrite minn_id/= big_const_ord/= /Num.max ltr10.
move=>n IH f; case: (fconsP f)=>x g.
rewrite big_ord_recl/= fcons0. under eq_bigr do rewrite fconsE.
by rewrite -IH -tentf_i2fnorm -tentf_tuple_cons i2fnormUr i2fnormUl.
Qed.

Section TentfTuplePred.
Variable (n : nat) (T : ihbFinType).

Lemma tentf_tuple_trlf (f : 'I_n -> 'End[T]) :
  \Tr (tentf_tuple f) = \prod_i \Tr (f i).
Proof.
rewrite (onb_trlf (tentvtv_tuple_onbasis _ _)).
under [RHS]eq_bigr do rewrite (onb_trlf t2tv).
rewrite bigA_distr_tuple/=; apply eq_bigr=>i _.
by rewrite /tentv_tuple_fun tentf_tuple_apply tentv_tuple_dot.
Qed. 

Lemma tentf_tuple_ge0 m (f : 'I_m -> 'End[T]) :
  (forall i, 0%:VF ⊑ f i) -> 0%:VF ⊑ tentf_tuple f.
Proof.
move=>P. have P1 i : {g : 'End[T] | f i = g^A \o g}.
by move: (P i)=>/gef0_formV/sig_eqW[g Pg]; exists g.
suff -> : tentf_tuple f = (tentf_tuple (fun i=>projT1 (P1 i)))^A \o
  (tentf_tuple (fun i=>projT1 (P1 i))) by apply form_gef0.
rewrite tentf_tuple_adj tentf_tuple_comp; apply eq_tentf_tuple=>i.
exact: (projT2 (P1 i)).
Qed.

Lemma tentf_tuple_lef m (f g : 'I_m -> 'End[T]) :
  (forall i, 0%:VF ⊑ f i) -> (forall i, f i ⊑ g i) -> tentf_tuple f ⊑ tentf_tuple g.
Proof.
elim: m f g=>[f g _ _ | m IH f g].
  suff ->: tentf_tuple f = tentf_tuple g by [].
  by apply eq_tentf_tuple; case.
case/fconsP: f=>f0 f; case/fconsP: g=>g0 g P1 P2.
rewrite !tentf_tuple_consV lef_form// lev_pbreg2//.
by move: (P1 ord0); rewrite fcons0.
by apply/tentf_tuple_ge0=>i; move: (P1 (nlift ord0 i)); rewrite fconsE.
by move: (P2 ord0); rewrite !fcons0.
by apply/IH=>i; move: (P1 (nlift ord0 i)) (P2 (nlift ord0 i)); rewrite !fconsE.
Qed.

Lemma tentf_tuple_normal (f : 'I_n -> 'FN('Hs T)) : tentf_tuple f \is normallf.
Proof.
rewrite normallfE tentf_tuple_adj !tentf_tuple_comp.
by under eq_tentf_tuple do rewrite normalfE.
Qed.
HB.instance Definition _ (f : 'I_n -> 'FN('Hs T)) :=
  isNormalLf.Build 'Hs(n.-tuple T) (tentf_tuple f) (@tentf_tuple_normal f).
Lemma tentf_tuple_herm (f : 'I_n -> 'FH('Hs T)) : tentf_tuple f \is hermlf.
Proof.
by rewrite hermlfE tentf_tuple_adj; under eq_tentf_tuple do rewrite hermf_adjE.
Qed.
HB.instance Definition _ (f : 'I_n -> 'FH('Hs T)) :=
  Normal_isHermLf.Build 'Hs(n.-tuple T) (tentf_tuple f) (@tentf_tuple_herm f).
Lemma tentf_tuple_psd (f : 'I_n -> 'F+('Hs T)) : tentf_tuple f \is psdlf.
Proof. rewrite psdlfE; apply/tentf_tuple_ge0=>i; apply/psdf_ge0. Qed.
HB.instance Definition _ (f : 'I_n -> 'F+('Hs T)) :=
  Herm_isPsdLf.Build 'Hs(n.-tuple T) (tentf_tuple f) (@tentf_tuple_psd f).
Lemma tentf_tuple_bound1 T' (f : 'I_n -> 'FB1('Hs T, 'Hs T')) : tentf_tuple f \is bound1lf.
Proof.
rewrite bound1lf_i2fnormE tentf_tuple_i2fnorm.
by apply: prodr_le1=>/= i _; rewrite normv_ge0 bound1f_i2fnorm.
Qed.
HB.instance Definition _ T' (f : 'I_n -> 'FB1('Hs T, 'Hs T')) :=
  isBound1Lf.Build 'Hs(n.-tuple T) 'Hs(n.-tuple T') (tentf_tuple f) (tentf_tuple_bound1 f).
HB.instance Definition _ (f : 'I_n -> 'FO('Hs T)) :=
  ObsLf.Class (PsdLf.on (tentf_tuple f)) (Bound1Lf.on (tentf_tuple f)).
Lemma tentf_tuple_den (f : 'I_n -> 'FD('Hs T)) : tentf_tuple f \is denlf.
Proof.
apply/denlfP; split; first by apply/is_psdlf.
by rewrite tentf_tuple_trlf; apply: prodr_le1=>/= i _; rewrite psdf_trlf denf_trlf.
Qed.
HB.instance Definition _ (f : 'I_n -> 'FD('Hs T)) :=
  Obs_isDenLf.Build 'Hs(n.-tuple T) (tentf_tuple f) (@tentf_tuple_den f).
Lemma tentf_tuple_den1 (f : 'I_n -> 'FD1('Hs T)) : tentf_tuple f \is den1lf.
Proof.
apply/den1lfP; split; first by apply/is_psdlf.
by rewrite tentf_tuple_trlf big1// =>i _; rewrite den1f_trlf.
Qed.
HB.instance Definition _ (f : 'I_n -> 'FD1('Hs T)) :=
  Den_isDen1Lf.Build 'Hs(n.-tuple T) (tentf_tuple f) (@tentf_tuple_den1 f).
Lemma tentf_tuple_proj (f : 'I_n -> 'FP('Hs T)) : tentf_tuple f \is projlf.
Proof.
apply/projlfP; rewrite tentf_tuple_adj tentf_tuple_comp; split;
by under eq_tentf_tuple do rewrite ?hermf_adjE ?projf_idem.
Qed.
HB.instance Definition _ (f : 'I_n -> 'FP('Hs T)) :=
  Obs_isProjLf.Build 'Hs(n.-tuple T) (tentf_tuple f) (@tentf_tuple_proj f).
HB.instance Definition _ (f : 'I_n -> 'FP1('Hs T)) := 
  Proj1Lf.Class (ProjLf.on (tentf_tuple f)) (Den1Lf.on (tentf_tuple f)).

Lemma tentf_tuple_iso T' (f : 'I_n -> 'FI('Hs T, 'Hs T')) : 
  tentf_tuple f \is isolf.
Proof.
rewrite isolfE tentf_tuple_adj tentf_tuple_comp.
by under eq_tentf_tuple do rewrite isofE; rewrite tentf_tuple1.
Qed.
HB.instance Definition _ (T' : ihbFinType) (f : 'I_n -> 'FI('Hs T, 'Hs T')) :=
  Bound1_isIsoLf.Build 'Hs (n.-tuple T) 'Hs (n.-tuple T') 
  (tentf_tuple f) (tentf_tuple_iso f).

Lemma tentf_tuple_giso T' (f : 'I_n -> 'FGI('Hs T, 'Hs T')) : 
  tentf_tuple f \is gisolf.
Proof.
rewrite gisolfE tentf_tuple_adj !tentf_tuple_comp.
under eq_tentf_tuple do rewrite gisofEl; rewrite tentf_tuple1.
by under eq_tentf_tuple do rewrite gisofEr; rewrite tentf_tuple1 !eqxx.
Qed.
HB.instance Definition _ (T' : ihbFinType) (f : 'I_n -> 'FGI('Hs T, 'Hs T')) :=
  Iso_isGisoLf.Build 'Hs (n.-tuple T) 'Hs (n.-tuple T') (tentf_tuple f) 
    (tentf_tuple_giso f).

End TentfTuplePred.

Lemma card_dffun (F : finType) (TF : F -> finType) :
  #|{dffun forall i : F, TF i}| = (\prod_i #|TF i|)%N.
Proof. by rewrite card_dep_ffun foldrE big_map big_enum. Qed.

(* packing dependent ffun *)
Section TentvDffun.
Variable (F : finType) (TF : forall i : F, ihbFinType).
Local Notation TH := {dffun forall i : F, TF i}.

Definition idx_dffuni (i : 'I_(dim 'Hs TH)) :
  {dffun forall j : F, 'I_(dim 'Hs (TF j))}
  := [ffun j => cast_ord (ihb_dim_cast _) (enum_rank 
    ((enum_val (cast_ord (esym (ihb_dim_cast _)) i)) j))].

Definition idx_dffun (fi : {dffun forall j : F, 'I_(dim 'Hs (TF j))}) : 
  'I_(dim 'Hs TH)
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
  := c2h (\col_i (\prod_j h2c (v j) (idx_dffuni i j) 0)).

Lemma eq_tentv_dffun (u v : forall i : F, 'Hs (TF i)) :
  (forall i, u i = v i) -> tentv_dffun u = tentv_dffun v.
Proof.
move=>P; apply/h2c_inj/matrixP=>i j.
by rewrite !c2hK !mxE; under eq_bigr do rewrite P.
Qed.

Lemma tentv_dffun_dot (u v : forall i : F, 'Hs (TF i)) :
  [< tentv_dffun u ; tentv_dffun v >] = \prod_i [< u i ; v i >].
Proof.
rewrite dotp_mulmx !c2hK mxE.
under eq_bigr do rewrite !mxE rmorph_prod -big_split/=.
under [RHS]eq_bigr do rewrite dotp_mulmx mxE.
rewrite big_distr_dffun/= (reindex idx_dffun).
by exists (idx_dffuni)=>x _; rewrite ?idx_dffuniK// idx_dffunK.
by do 2 apply eq_bigr=>? _; rewrite/= !mxE !idx_dffunK.
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
rewrite !mxE. under eq_bigr do rewrite c2hK mxE.
case: eqP=>[ <-|/eqP/dffun_neqP[k/negPf nk]].
by rewrite big1// =>k _; rewrite enum_ord_eq /idx_dffuni ffunE eqxx.
by rewrite (bigD1 k)//= {1}/idx_dffuni ffunE cast_ord_comp cast_ord_id enum_rankK nk mul0r.
Qed.

Lemma tentv_dffun_conj (v : forall i : F, 'Hs (TF i)) : 
  (tentv_dffun v)^*v = tentv_dffun (fun i=>(v i)^*v).
Proof.
apply/h2c_inj/matrixP=>i j; rewrite conjv.unlock !c2hK !mxE rmorph_prod;
by apply eq_bigr=>k _; rewrite c2hK mxE.
Qed.

Lemma tentv_dffunZ (v : forall i : F, 'Hs (TF i)) (fc : F -> C) :
  tentv_dffun (fun i=> fc i *: v i)
  = \prod_i (fc i) *: tentv_dffun v.
Proof.
apply/(intro_onbl t2tv)=>i/=; rewrite t2tv_dffun dotpZr.
rewrite !tentv_dffun_dot -big_split/=; apply eq_bigr=>j _.
by rewrite dotpZr.
Qed.

Lemma tentv_dffun_ps (t : forall i, 'PS('Hs (TF i))) :
  [< tentv_dffun t ; tentv_dffun t >] <= 1.
Proof. by rewrite tentv_dffun_dot prodr_le1// =>i _; rewrite ps_dot ge0_dotp. Qed.
HB.instance Definition _ (t : forall i, 'PS('Hs (TF i))) :=
  isPartialState.Build ('Hs TH) (tentv_dffun t) (tentv_dffun_ps t).
Lemma tentv_dffun_ns (t : forall i, 'NS('Hs (TF i))) :
  [< tentv_dffun t ; tentv_dffun t >] = 1.
Proof. by rewrite tentv_dffun_dot big1// =>i _; rewrite ns_dot. Qed.
HB.instance Definition _ (t : forall i, 'NS('Hs (TF i))) :=
  Partial_isNormalState.Build ('Hs TH) (tentv_dffun t) (tentv_dffun_ns t).

Definition tentv_dffun_fun (G : F -> finType) (f : forall i : F, G i -> 'Hs (TF i)) :=
  (fun i : {dffun forall i : F, G i} => tentv_dffun (fun k=> f k (i k))).
Lemma tentv_dffun_ponb (G : F -> finType) (f : forall i : F, 'PONB(G i;'Hs (TF i))) i j :
  [< tentv_dffun_fun f i ; tentv_dffun_fun f j >] = (i == j)%:R.
Proof.
rewrite/tentv_dffun_fun tentv_dffun_dot.
case: eqP=>[->|/eqP]; first by rewrite big1// =>k _; rewrite ns_dot.
by move=>/dffun_neqP[k/negPf nk]; rewrite (bigD1 k)//= ponb_dot nk mul0r.
Qed.
HB.instance Definition _ (G : F -> finType) (f : forall i : F, 'PONB(G i;'Hs (TF i))) :=
  isPONB.Build ('Hs TH) {dffun forall i : F, G i} (tentv_dffun_fun f) (tentv_dffun_ponb f).
Lemma tentv_dffun_card (G : F -> finType) (f : forall i : F, 'ONB(G i;'Hs (TF i))) :
  #|{dffun forall i : F, G i}| = dim ('Hs TH).
Proof.
rewrite -ihb_dim_cast !card_dffun; apply eq_bigr=>i _; 
by rewrite/= (@onb_card _ _ (f i)) ihb_dim_cast.
Qed.
HB.instance Definition _ (G : F -> finType) (f : forall i : F, 'ONB(G i;'Hs (TF i))) :=
  isFullDim.Build ('Hs TH) {dffun forall i : F, G i} (tentv_dffun_fun f) (tentv_dffun_card f).
Definition tentv_dffun_onbasis (G : F -> finType) (f : forall i : F, 'ONB(G i;'Hs (TF i)))
  : onbType _ _ := (tentv_dffun_fun f).
Definition tentvtv_dffun_onbasis := tentv_dffun_onbasis (fun i=>t2tv).

End TentvDffun.

Section TentfDffun.
Variable (F : finType) (TF TF' : forall i : F, ihbFinType).
Local Notation TH := {dffun forall i : F, TF i}.
Local Notation TH' := {dffun forall i : F, TF' i}.
Implicit Type (f : forall i : F, 'Hom[TF i, TF' i]).

Definition tentf_dffun f : 'Hom[TH, TH']
  := mx2h (\matrix_(i,j) (\prod_k h2mx (f k) (idx_dffuni i k) (idx_dffuni j k))).

Lemma eq_tentf_dffun f f' :
  (forall i, f i = f' i) -> tentf_dffun f = tentf_dffun f'.
Proof.
move=>P; apply/h2mx_inj/matrixP=>i j.
by rewrite/= !mx2hK !mxE; under eq_bigr do rewrite P.
Qed.

Lemma tentf_dffun_apply f (v : forall i : F, 'Hs (TF i)) :
  tentf_dffun f (tentv_dffun v) = tentv_dffun (fun i=>f i (v i)).
Proof.
apply/h2c_inj/matrixP=>i j; rewrite applyfh mx2hK !c2hK !mxE/=.
under [RHS]eq_bigr do rewrite applyfh c2hK mxE.
rewrite big_distr_dffun/= (reindex (@idx_dffun _ _)).
by exists (@idx_dffuni _ _)=>x _; rewrite ?idx_dffuniK// idx_dffunK.
apply eq_bigr=>k _; rewrite !mxE -big_split/=; 
by apply eq_bigr=>l _; rewrite !idx_dffunK.
Qed.

Lemma tentf_dffun_out (v : forall i : F, 'Hs (TF' i)) (u : forall i : F, 'Hs (TF i)) : 
  tentf_dffun (fun i=> [> v i ; u i <]) 
  = [> tentv_dffun v ; tentv_dffun u <].
Proof.
apply/(intro_onb t2tv)=>i.
rewrite/= t2tv_dffun tentf_dffun_apply outpE.
under eq_tentv_dffun do rewrite outpE.
by rewrite tentv_dffunZ tentv_dffun_dot.
Qed.

Lemma tentf_dffun_conj f :
  (tentf_dffun f)^C = tentf_dffun (fun i=> (f i)^C).
Proof.
apply/h2mx_inj/matrixP=>i j; rewrite conj_lfun.unlock !mx2hK !mxE rmorph_prod; 
by apply eq_bigr => k _; rewrite mx2hK !mxE.
Qed.

End TentfDffun.

Section TentfDffunGen.
Variable (F : finType).
Implicit Type (TF : forall i : F, ihbFinType).
Local Notation DF x y := (forall i : F, 'Hom[x i, y i]).

Lemma tentf_dffun_tr TF TF' (f : DF TF TF') :
  (tentf_dffun f)^T = tentf_dffun (fun i=> (f i)^T).
Proof.
apply/h2mx_inj/matrixP=>i j; rewrite tr_lfun.unlock !mx2hK !mxE; 
by apply eq_bigr => k _; rewrite mx2hK !mxE.
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
move=>i a x v; apply/(intro_onbl t2tv)=>y.
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
move=>i a x v; apply/(intro_onb t2tv)=>y.
rewrite/= t2tv_dffun /tentf_dmv lfunE/= lfunE/= !tentf_dffun_apply.
apply/(intro_onbl t2tv)=>z.
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

Lemma tentf_dffun1 (F : finType) (TF : forall i : F, ihbFinType) : 
  tentf_dffun (fun i : F=> \1 : 'End[TF i]) = \1.
Proof.
apply/(intro_onb t2tv)=>i.
rewrite/= t2tv_dffun tentf_dffun_apply lfunE/=;
by under eq_tentv_dffun do rewrite lfunE.
Qed.

Lemma test (F : finType) (x : F) : #|{: {y : F | y != x}}| = #|F|.-1.
Proof. by rewrite card_sig -(cardC1 x); apply/eq_card=>i; rewrite inE. Qed.

Definition tentv_dffun_tensU {F : finType} {x : F} {fT : F -> ihbFinType} : 
  'Hom(_, 'Hs (fT x * {dffun forall i : {y : F | y != x}, fT (val i)})%type) :=
  \sum_(f : {dffun forall i : F, fT i}) 
    [> tentv ''(f x) (tentv_dffun (fun i : {y : F | y != x} => ''(f (val i)))); 
    tentv_dffun (fun i => ''(f i)) <].

Definition dffun_ord_recl (F : finType) (x : F) (T : F -> Type) :
  {dffun forall i : F, T i} -> 
    T x * {dffun forall i : {y : F | y != x}, T (val i)} :=
      (fun f => (f x, [ffun i => f (val i)])).
Lemma dffun_ord_recl_inj F x T : injective (@dffun_ord_recl F x T).
Proof.
move=>i j Pij; inversion Pij; apply/ffunP=>/= k.
case E: (k == x). by move: E=>/eqP->.
move: E=>/eqP/eqP E; move: H1=>/ffunP/(_ (exist (fun i => i != x) _ E));
by rewrite !ffunE/=.
Qed.

Lemma dffun_ord_recl_bij (F : finType) (x : F) (T : F -> finType) : 
  bijective (@dffun_ord_recl F x T).
Proof.
apply/inj_card_bij; first by apply/dffun_ord_recl_inj.
rewrite card_prod !card_dffun (big_sig _ _ (fun i : F => #|T i|))/=.
by rewrite [X in (_ <= X)%N](bigD1 x).
Qed.

Lemma tentv_dffun_tensU_gios F x T : (@tentv_dffun_tensU F x T) \is gisolf.
Proof.
rewrite -gisolf_adj; apply/isolf_giso_dim; last first.
  by rewrite -!ihb_dim_cast card_prod !card_dffun 
    (big_sig _ _ (fun i : F => #|T i|))/= [RHS](bigD1 x).
apply/isolfP; rewrite adjfK adjf_sum.
rewrite -tentf11 -(sumonb_out t2tv) -(sumonb_out t2tv) !linear_suml/=.
under eq_bigr do rewrite linear_sumr/=.
transitivity (\sum_(i : {dffun forall i, T i}) 
  [> ''(i x) ⊗t tentv_dffun (fun i1 : {j | j != x} => ''(i (val i1))); 
  ''(i x) ⊗t tentv_dffun (fun i1 : {j | j != x} => ''(i (val i1))) <]).
apply eq_bigr=>i _; rewrite (bigD1 i)//= big1=>[j/dffun_neqP [k /negPf nji]|].
by rewrite adj_outp outp_comp tentv_dffun_dot
  (bigD1 k)//= onb_dot eq_sym nji mul0r scale0r.
by rewrite adj_outp addr0// outp_comp ns_dot scale1r.
under [RHS]eq_bigr do rewrite linear_sumr/=.
rewrite pair_big_dep/=.
rewrite (reindex (@dffun_ord_recl _ x T))/=; last first.
  apply eq_bigr=>i _; rewrite -tentv_out t2tv_dffun; f_equal; f_equal; 
  by apply/eq_tentv_dffun=>j; rewrite ffunE.
by move: (dffun_ord_recl_bij x T)=>[f Ph Pf]; exists f=>y _; rewrite ?Ph ?Pf.
Qed.
HB.instance Definition _ F x T := isGisoLf.Build _ _ 
  (@tentv_dffun_tensU F x T) (@tentv_dffun_tensU_gios F x T).

Lemma tentv_dffun_consV (F : finType) (x : F) (T : F -> ihbFinType)
  (f : forall i, 'Hs (T i)) : 
  tentv_dffun_tensU ^A (tentv (f x) (tentv_dffun 
    [ffun i : {j | j != x} => f (val i)])) = (tentv_dffun f).
Proof.
apply/(intro_onbl t2tv)=>i; rewrite /tentv_dffun_tensU adjf_sum/= 
  sum_lfunE dotp_sumr (bigD1 i)//= big1=>[j /negPf nji | ].
by rewrite adj_dotEr outpE -t2tv_dffun onb_dot nji scale0r dot0p.
rewrite adj_dotEr outpE -t2tv_dffun ns_dot scale1r addr0 tentv_dot tentv_dffun_dot 
  [in RHS]t2tv_dffun tentv_dffun_dot [RHS](bigD1 x)//= -[in RHS]big_sig.
by under eq_bigr do rewrite ffunE.
Qed.

Lemma tentv_dffun_cons (F : finType) x (T : F -> ihbFinType) (f : forall i, 'Hs (T i)) : 
  tentv_dffun_tensU (tentv_dffun f) = 
    tentv (f x) (tentv_dffun [ffun i : {j | j != x} => f (val i)]).
Proof. by rewrite -(tentv_dffun_consV x) gisofKEr. Qed.

Lemma tentf_dffun_consV (F : finType) x (T1 T2 : F -> ihbFinType)
  (f : forall i, 'Hom[T1 i,T2 i]) :
  tentv_dffun_tensU ^A \o (tentf (f x) (tentf_dffun 
    [ffun i : {j | j != x} => f (val i)])) \o tentv_dffun_tensU
   = (tentf_dffun f).
Proof.
rewrite -[RHS]comp_lfun1l -(gisofEl (@tentv_dffun_tensU _ x _)) -!comp_lfunA;
f_equal; apply/(intro_onb t2tv)=>/=i.
rewrite !lfunE/= t2tv_dffun tentf_dffun_apply !tentv_dffun_cons tentf_apply tentf_dffun_apply.
by f_equal; apply/eq_tentv_dffun=>j; rewrite !ffunE/=.
Qed.

Lemma tentf_dffun_cons (F : finType) x (T1 T2 : F -> ihbFinType)
  (f : forall i, 'Hom[T1 i,T2 i]) :
  tentv_dffun_tensU \o (tentf_dffun f) \o tentv_dffun_tensU ^A = 
    tentf (f x) (tentf_dffun [ffun i : {j | j != x} => f (val i)]).
Proof. by rewrite -(tentf_dffun_consV x) !comp_lfunA gisofEr gisofKr comp_lfun1l. Qed.

Global Arguments big_card0 [T idx op I r P] F.

Lemma tentf_dffun_norm (F : finType) (T T' : F -> ihbFinType) (f : forall i, 'Hom[T i, T' i]) :
  `|tentf_dffun f| = \prod_i `|f i|.
Proof.
set n := #|F|; have: #|F| = n by [].
move: n=>n Pn; elim: n F Pn T T' f =>[F PF T T' f|n IH F PF T T' f].
  rewrite /Num.norm/= /trfnorm mx2hK (big_card0 _ PF).
  under eq_mx do rewrite (big_card0 _ PF).
  have P1: 1 = dim 'Hs {dffun forall i, T i} 
    by rewrite -ihb_dim_cast card_dffun (big_card0 _ PF).
  have P2: 1 = dim 'Hs {dffun forall i, T' i} 
    by rewrite -ihb_dim_cast card_dffun (big_card0 _ PF).
  case: _ / P1; case: _ / P2.
  set t := \matrix_(_,_) _.
  have ->: t = 1%:M by apply/matrixP=>i j; rewrite /t !mxE !ord1 eqxx.
  rewrite /trnorm /schattennorm svd_d_const /pnorm root1C pair_bigV/= big_ord1.
  under eq_bigr do rewrite mxE normr1 normr1 expr1n.
  by rewrite minn_id big_ord1.
have /card_gt0P [x _]: (0 < #|F|)%N by rewrite PF.
rewrite -(tentf_dffun_consV x) trfnormUr trfnormUl tentf_norm IH/= ?test ?PF//.
under eq_bigr do rewrite ffunE.
by rewrite [RHS](bigD1 x)//= -[in RHS]big_sig/=.
Qed.

Lemma tentf_dffun_i2fnorm (F : finType) (T T' : F -> ihbFinType) (f : forall i, 'Hom[T i, T' i]) :
  i2fnorm (tentf_dffun f) = \prod_i i2fnorm (f i).
Proof.
set n := #|F|; have: #|F| = n by [].
move: n=>n Pn; elim: n F Pn T T' f =>[F PF T T' f|n IH F PF T T' f].
  rewrite /i2fnorm mx2hK (big_card0 _ PF).
  under eq_mx do rewrite (big_card0 _ PF).
  have P1: 1 = dim 'Hs {dffun forall i, T i} 
    by rewrite -ihb_dim_cast card_dffun (big_card0 _ PF).
  have P2: 1 = dim 'Hs {dffun forall i, T' i} 
    by rewrite -ihb_dim_cast card_dffun (big_card0 _ PF).
  case: _ / P1; case: _ / P2.
  set t := \matrix_(_,_) _.
  have ->: t = 1%:M by apply/matrixP=>i j; rewrite /t !mxE !ord1 eqxx.
  rewrite /i2norm svd_d_const.
  under eq_bigr do rewrite mxE normr1.
  by rewrite minn_id/= big_const_ord/= /Num.max ltr10.
have /card_gt0P [x _]: (0 < #|F|)%N by rewrite PF.
rewrite -(tentf_dffun_consV x) i2fnormUr i2fnormUl tentf_i2fnorm IH/= ?test ?PF//.
under eq_bigr do rewrite ffunE.
by rewrite [RHS](bigD1 x)//= -[in RHS]big_sig/=.
Qed.

(* add canonical structures if needed, say, tentf_dffun unitary*)
Section TentfDffunPred.
Variable (F : finType) (TF : forall i : F, ihbFinType).

Lemma tentf_dffun_trlf (f : forall i : F, 'End[TF i]) :
  \Tr (tentf_dffun f) = \prod_i \Tr (f i).
Proof.
rewrite (onb_trlf (tentvtv_dffun_onbasis _)).
under [RHS]eq_bigr do rewrite (onb_trlf t2tv).
rewrite big_distr_dffun/=; apply eq_bigr=>i _.
by rewrite/tentv_dffun_fun tentf_dffun_apply tentv_dffun_dot.
Qed. 

Lemma tentf_dffun_ge0 (f : forall i : F, 'End[TF i]) :
  (forall i, 0%:VF ⊑ f i) -> 0%:VF ⊑ tentf_dffun f.
Proof.
move=>P. have P1 i : {g : 'End[TF i] | f i = g^A \o g}.
by move: (P i)=>/gef0_formV/sig_eqW[g Pg]; exists g.
suff -> : tentf_dffun f = (tentf_dffun (fun i=>projT1 (P1 i)))^A \o
  (tentf_dffun (fun i=>projT1 (P1 i))) by apply form_gef0.
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
rewrite levDl; apply/tentf_dffun_ge0=>i.
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

Lemma tentf_dffun_normal (f : forall i : F, 'FN('Hs (TF i))) : tentf_dffun f \is normallf.
Proof.
rewrite normallfE tentf_dffun_adj !tentf_dffun_comp.
by under eq_tentf_dffun do rewrite normalfE.
Qed.
HB.instance Definition _ (f : forall i : F, 'FN('Hs (TF i))) :=
  isNormalLf.Build ('Hs {dffun forall i : F, TF i}) (tentf_dffun f) (tentf_dffun_normal f).
Lemma tentf_dffun_herm (f : forall i : F, 'FH('Hs (TF i))) : tentf_dffun f \is hermlf.
Proof.
by rewrite hermlfE tentf_dffun_adj; under eq_tentf_dffun do rewrite hermf_adjE.
Qed.
HB.instance Definition _ (f : forall i : F, 'FH('Hs (TF i))) :=
  Normal_isHermLf.Build ('Hs {dffun forall i : F, TF i}) (tentf_dffun f) (@tentf_dffun_herm f).
Lemma tentf_dffun_psd (f : forall i : F, 'F+('Hs (TF i))) : tentf_dffun f \is psdlf.
Proof. rewrite psdlfE; apply/tentf_dffun_ge0=>i; apply/psdf_ge0. Qed.
HB.instance Definition _ (f : forall i : F, 'F+('Hs (TF i))) :=
  Herm_isPsdLf.Build ('Hs {dffun forall i : F, TF i}) (tentf_dffun f) (@tentf_dffun_psd f).
Lemma tentf_dffun_bound1 (TF' : forall i : F, ihbFinType) 
  (f : forall i : F, 'FB1('Hs (TF i), 'Hs (TF' i))) : tentf_dffun f \is bound1lf.
Proof.
rewrite bound1lf_i2fnormE tentf_dffun_i2fnorm; apply/prodr_le1=>i _.
by rewrite normv_ge0/= bound1f_i2fnorm.
Qed.
HB.instance Definition _ (TF' : forall i : F, ihbFinType) 
  (f : forall i : F, 'FB1('Hs (TF i), 'Hs (TF' i))) :=
  isBound1Lf.Build ('Hs {dffun forall i : F, TF i}) ('Hs {dffun forall i : F, TF' i})
    (tentf_dffun f) (tentf_dffun_bound1 f).
HB.instance Definition _ (f : forall i : F, 'FO('Hs (TF i))) :=
  ObsLf.Class (PsdLf.on (tentf_dffun f)) (Bound1Lf.on (tentf_dffun f)).
Lemma tentf_dffun_den (f : forall i : F, 'FD('Hs (TF i))) : tentf_dffun f \is denlf.
Proof.
apply/denlfP; split; first by apply/is_psdlf.
by rewrite tentf_dffun_trlf prodr_le1// =>i _; rewrite psdf_trlf denf_trlf.
Qed.
HB.instance Definition _ (f : forall i : F, 'FD('Hs (TF i))) :=
  Obs_isDenLf.Build ('Hs {dffun forall i : F, TF i}) (tentf_dffun f) (@tentf_dffun_den f).
Lemma tentf_dffun_den1 (f : forall i : F, 'FD1('Hs (TF i))) : tentf_dffun f \is den1lf.
Proof.
apply/den1lfP; split; first by apply/is_psdlf.
by rewrite tentf_dffun_trlf big1// =>i _; rewrite den1f_trlf.
Qed.
HB.instance Definition _ (f : forall i : F, 'FD1('Hs (TF i))) :=
  Den_isDen1Lf.Build ('Hs {dffun forall i : F, TF i}) (tentf_dffun f) (@tentf_dffun_den1 f).
Lemma tentf_dffun_proj (f : forall i : F, 'FP('Hs (TF i))) : tentf_dffun f \is projlf.
Proof.
apply/projlfP; rewrite tentf_dffun_adj tentf_dffun_comp; split;
by under eq_tentf_dffun do rewrite ?hermf_adjE ?projf_idem.
Qed.
HB.instance Definition _ (f : forall i : F, 'FP('Hs (TF i))) :=
  Obs_isProjLf.Build ('Hs {dffun forall i : F, TF i}) (tentf_dffun f) (@tentf_dffun_proj f).
HB.instance Definition _ (f : forall i : F, 'FP1('Hs (TF i))) := 
  Proj1Lf.Class (ProjLf.on (tentf_dffun f)) (Den1Lf.on (tentf_dffun f)).

Lemma tentf_dffun_iso (TF' : forall i : F, ihbFinType) 
  (f : forall i : F, 'FI('Hs (TF i), 'Hs (TF' i))) : 
    tentf_dffun f \is isolf.
Proof.
rewrite isolfE tentf_dffun_adj tentf_dffun_comp.
by under eq_tentf_dffun do rewrite isofE; rewrite tentf_dffun1.
Qed.
HB.instance Definition _ TF' (f : forall i : F, 'FI('Hs (TF i), 'Hs (TF' i))) :=
  Bound1_isIsoLf.Build ('Hs {dffun forall i : F, TF i}) ('Hs {dffun forall i : F, TF' i}) 
    (tentf_dffun f) (tentf_dffun_iso f).

Lemma tentf_dffun_giso (TF' : forall i : F, ihbFinType) 
  (f : forall i : F, 'FGI('Hs (TF i), 'Hs (TF' i))) : 
    tentf_dffun f \is gisolf.
Proof.
rewrite gisolfE tentf_dffun_adj !tentf_dffun_comp.
under eq_tentf_dffun do rewrite gisofEl; rewrite tentf_dffun1.
by under eq_tentf_dffun do rewrite gisofEr; rewrite tentf_dffun1 !eqxx.
Qed.
HB.instance Definition _ TF' (f : forall i : F, 'FGI('Hs (TF i), 'Hs (TF' i))) :=
  Iso_isGisoLf.Build ('Hs {dffun forall i : F, TF i}) ('Hs {dffun forall i : F, TF' i}) 
    (tentf_dffun f) (tentf_dffun_giso f).

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

HB.instance Definition _ (t : F -> 'PS('Hs T)) :=
  PartialState.on (tentv_ffun t).
HB.instance Definition _ (t : F -> 'NS('Hs T)) :=
  NormalState.on (tentv_ffun t).

(* if G is dependent on F, using tentv_dffun_fun instead *)
Definition tentv_ffun_fun (G : finType) (f : F -> G -> 'Hs T) :=
  (fun i : {ffun F -> G} => tentv_ffun (fun k=> f k (i k))).
HB.instance Definition _ (G : finType) (f : F -> 'PONB(G;'Hs T)) :=
  PONB.copy (tentv_ffun_fun f) (tentv_dffun_fun f).
HB.instance Definition _ (G : finType) (f : F -> 'ONB(G;'Hs T)) :=
  ONB.copy (tentv_ffun_fun f) (tentv_dffun_fun f).
Definition tentv_ffun_onbasis (G : finType) (f : F -> 'ONB(G;'Hs T))
  : onbType _ _ := (tentv_ffun_fun f).
Definition tentvtv_ffun_onbasis := tentv_ffun_onbasis (fun i=>t2tv).

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

Definition tentv_ffun_tensU {F : finType} {x : F} {fT : ihbFinType} : 
  'Hom(_, 'Hs (fT * {ffun {y : F | y != x} -> fT})%type) :=
  \sum_(f : {ffun F -> fT}) 
    [> tentv ''(f x) (tentv_ffun (fun i : {y : F | y != x} => ''(f (val i)))); 
    tentv_ffun (fun i => ''(f i)) <].

Definition ffun_ord_recl (F : finType) (x : F) (T : Type) :
  {ffun F -> T} -> T * {ffun {y : F | y != x} -> T} :=
      (fun f => (f x, [ffun i => f (val i)])).
Lemma ffun_ord_recl_inj F x T : injective (@ffun_ord_recl F x T).
Proof. exact: dffun_ord_recl_inj. Qed.

Lemma ffun_ord_recl_bij (F : finType) (x : F) (T : finType) : 
  bijective (@ffun_ord_recl F x T).
Proof. exact: dffun_ord_recl_bij. Qed.

HB.instance Definition _ F x T := GisoLf.copy (@tentv_ffun_tensU F x T) 
  (@tentv_dffun_tensU F x (fun i : F => T)).

Lemma tentv_ffun_consV (F : finType) (x : F) (T : ihbFinType)
  (f : F -> 'Hs T) : 
  tentv_ffun_tensU ^A (tentv (f x) (tentv_ffun 
    [ffun i : {j | j != x} => f (val i)])) = (tentv_ffun f).
Proof. exact: tentv_dffun_consV. Qed.

Lemma tentv_ffun_cons (F : finType) x (T : ihbFinType) (f : F -> 'Hs T) : 
  tentv_ffun_tensU (tentv_ffun f) = 
    tentv (f x) (tentv_ffun [ffun i : {j | j != x} => f (val i)]).
Proof. exact: tentv_dffun_cons. Qed.

Lemma tentf_ffun_consV (F : finType) x (T1 T2 : ihbFinType)
  (f : F -> 'Hom[T1, T2]) :
  tentv_ffun_tensU ^A \o (tentf (f x) (tentf_ffun 
    [ffun i : {j | j != x} => f (val i)])) \o tentv_ffun_tensU
   = (tentf_ffun f).
Proof. exact: tentf_dffun_consV. Qed.

Lemma tentf_ffun_cons (F : finType) x (T1 T2 : ihbFinType)
  (f : F -> 'Hom[T1, T2]) :
  tentv_ffun_tensU \o (tentf_ffun f) \o tentv_ffun_tensU ^A = 
    tentf (f x) (tentf_ffun [ffun i : {j | j != x} => f (val i)]).
Proof. exact: tentf_dffun_cons. Qed.

Lemma tentf_ffun_norm (F : finType) (T T' : ihbFinType) (f : F -> 'Hom[T, T']) :
  `|tentf_ffun f| = \prod_i `|f i|.
Proof. exact: tentf_dffun_norm. Qed.

Lemma tentf_ffun_i2fnorm (F : finType) (T T' : ihbFinType) (f : F -> 'Hom[T, T']) :
  i2fnorm (tentf_ffun f) = \prod_i i2fnorm (f i).
Proof. exact: tentf_dffun_i2fnorm. Qed.

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

HB.instance Definition _ (f : F -> 'FN('Hs T)) := NormalLf.on (tentf_ffun f).
HB.instance Definition _ (f : F -> 'FH('Hs T)) := HermLf.on (tentf_ffun f).
HB.instance Definition _ (f : F -> 'F+('Hs T)) := PsdLf.on (tentf_ffun f).
HB.instance Definition _ T' (f : F -> 'FB1('Hs T, 'Hs T')) := Bound1Lf.on (tentf_ffun f).
HB.instance Definition _ (f : F -> 'FO('Hs T)) := ObsLf.on (tentf_ffun f).
HB.instance Definition _ (f : F -> 'FD('Hs T)) := DenLf.on (tentf_ffun f).
HB.instance Definition _ (f : F -> 'FD1('Hs T)) := Den1Lf.on (tentf_ffun f).
HB.instance Definition _ (f : F -> 'FP('Hs T)) := ProjLf.on (tentf_ffun f).
HB.instance Definition _ (f : F -> 'FP1('Hs T)) := Proj1Lf.on (tentf_ffun f).
HB.instance Definition _ T' (f : F -> 'FI('Hs T, 'Hs T')) := IsoLf.on (tentf_ffun f).
HB.instance Definition _ T' (f : F -> 'FGI('Hs T, 'Hs T')) := GisoLf.on (tentf_ffun f).

End TentfFfunPred.

