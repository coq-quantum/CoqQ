From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals.
From quantum.external Require Import complex.
(* From mathcomp.real_closed Require Import complex. *)
Require Import mcextra mcaextra notation quantum inhabited autonat.

From quantum Require Import hermitian qreg prodvect tensor mxpred
  orthomodular hspace hspace_extra.
From quantum.dirac Require Import hstensor dirac.
Require Import Coq.Program.Equality String.
Require Import Relation_Definitions Setoid.

(*****************************************************************************)
(*                   Formalization of Quantum Memory System                  *)
(* ------------------------------------------------------------------------- *)
(* qreg.v defines the syntax to manipulate quantum variables, and this file  *)
(*   provide a interface of memory model (how to map quantum registers to a  *)
(*   composite quantum system), with necessity being consistent to their     *)
(*   construction and disjointness; e.g.,                                    *)
(*      the corresponding system of (x,y).1 should be identical to x         *)
(*        (if (x,y) is valid )                                               *)
(*      x and y are syntactically disjoint, then their corresponding         *)
(*        systems should also be disjoint                                    *)
(* ------------------------------------------------------------------------- *)
(*       qmemory := structure type of quantum memory model, mapping every    *)
(*                   quantum registers to some subsystem satisfying          *)
(*                   1. type condition (x: 'QReg[T]), dim 'H_(mset x) = #|T| *)
(*                   2. consistent with merging and splitting                *)
(*                   3. consistent of syntactic and semantic disjointness    *)
(* mem_lab, mlab := labels of the whole composite quantum system             *)
(* mem_sys, msys := mapping from labels to Hilbert space, mlab -> chsType    *)
(*                 e.g., 'H[msys]_S indicate the subsystem S                 *)
(* mem_set, mset := mapping each register to a subsystem, qreg -> {set mlab} *)
(*     tv2v x v := mapping from (v : 'Ht T) -> 'H_(mset x)                   *)
(*                 providing (x : qreg T)                                    *)
(* tf2f x1 x2 f := mapping from (f : 'Hom('Ht T1, 'Ht T2)) ->                *)
(*                                               'F_(mset x1, mset x2)       *)
(*                 providing (x1 : qreg T1) and (x2 : qreg T2)               *)
(*       v2tv v := mapping from (v : 'H_(mset x)) -> 'Ht T                   *)
(*                 providing (x : qreg T)                                    *)
(*       f2tf f := mapping from (f : 'F_(mset x1, mset x2)) ->               *)
(*                                               'Hom('Ht T1, 'Ht T2)        *)
(*                 providing (x1 : qreg T1) and (x2 : qreg T2)               *)
(* tm2m x1 x2 f := mapping from (f : F -> 'Hom('Ht T1, 'Ht T2)) ->           *)
(*                                       (F -> 'F_(mset x1, mset x2))        *)
(*                 providing (x1 : qreg T1) and (x2 : qreg T2)               *)
(*       v2tU x := isometry from 'H_(mset x) to 'Ht T                        *)
(*                 providing (x : qreg T), i.e., v2tv v = v2tU x v           *)
(*                 v2tU is further a global isometry if (x : 'QReg[T])       *)
(*     tket x v := '| tv2v x v > : 'D[msys]                                  *)
(*                 mapping 'Ht T to 'D[msys] directly providing (x : qreg T) *)
(*     tbra x v := '< tv2v x v | : 'D[msys]                                  *)
(*                 mapping 'Ht T to 'D[msys] directly providing (x : qreg T) *)
(* tlin x1 x2 f := '[ tf2f x1 x2 f ] : 'D[msys]                              *)
(*                 mapping 'Hom('Ht T1, Ht T2) to 'D[msys] directly          *)
(*                 providing (x1 : qreg T1) and (x2 : qreg T2)               *)
(* ------------------------------------------------------------------------- *)
(* A default quantum memory model is provided, and use it by                 *)
(*    Import DefaultQMem.Exports.                                            *)
(*****************************************************************************)

Import Order.LTheory GRing.Theory Num.Theory.

Local Notation C := hermitian.C.
Local Notation G := qreg.G.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.
Local Open Scope efnd_scope.

Class qmem_expose (P : Prop) := QMemExpose : P.
Class dirac_expose (P : Prop) := DiracExpose : P.

Reserved Notation "''[' x ; y , z ]"
  (at level 2, x at level 60, y custom reg, z custom reg,
   format "''[' x ; y , z ]").

Module QMemory.

Local Open Scope fnd_scope.
Section ClassDef.

Record mixin_of (L : finType) (H : L -> chsType) 
  (S : forall {T}, qreg T -> {set L}) 
  (V : forall {T} (x : qreg T), 'Ht T -> 'H[H]_(S x))
   : Type := Mixin {

  _ : forall {T} (x : qreg T), linear (V x);

  _ : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2), 
        (disjoint_qreg x1 x2) = [disjoint S x1 & S x2]; 

  _ : forall T (x y : qreg T), 
        x =r y -> forall (v : 'Ht T), V x v =v V y v;

  _ : forall T (x : qreg T) (v : 'Ht T),
        ((V x v)^*v = V x (v^*v))%VF;
  
  _ : forall T (x : qreg T) (u : 'H[H]_(S x)),
        u = \sum_t [< V x ''t ; u >] *: V x ''t;

  _ : forall T (x : qreg T) (i j : evalQT T),
        i != j -> [< V x ''i ; V x ''j >] = 0;

  (* onbasis projection *)
  _ : forall T (x : 'QReg[T]), #|evalQT T| = dim 'H[H]_(S x);
  _ : forall T (x : 'QReg[T]), 
        forall i j, [< V x (t2tv i) ; V x (t2tv j) >] = (i == j)%:R;
  
  (* rules for constructors *)
  _ : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2)
        (t1 : eval_qtype T1) (t2 : eval_qtype T2) ,
            (V x1 ''t1)%:Hnd ⊗v (V x2 ''t2)%:Hnd =
              (V <{(x1,x2)}> (''t1 ⊗t ''t2))%:Hnd;

  _ : forall n T (x : 'I_n -> qreg T) (t : n.-tuple (eval_qtype T)),
          \tenv_i (V (x i) ''(t ~_ i))%:Hnd =
            (V <{ tuple: x }> ''t)%:Hnd;

  _ : forall n (T : 'I_n -> qType) (x : forall i, qreg (T i)) 
        (t : {dffun forall i, eval_qtype (T i)}) ,
            \tenv_i (V (x i) ''(t i))%:Hnd =
              (V <{ ffun: x }> ''t)%:Hnd;
}.

Record qmemory := QMemory  
{
  mem_label  : finType;
  mem_system   : mem_label -> chsType;
  (* for every qreg, set a quantum system *)
  qreg_set  : forall T, qreg T -> {set mem_label};
  (* reflect disjointness *)
  (* projection for vector and linear operator *)
  vec_proj  : forall T (x : qreg T), 'Ht T -> 'H[mem_system]_(qreg_set x);
  (* in fact, this give the definition of lfun_proj *)
  _ : mixin_of vec_proj;
}.

End ClassDef.

Lemma tv2v_is_linear m T (x : qreg T) : linear (@vec_proj m T x).
Proof. by case: m T x=>????[]. Qed. 
#[export]
HB.instance Definition _ m T (x : qreg T) := GRing.isLinear.Build C ('Ht T)
  'H[@mem_system m]_(qreg_set m x) *:%R (@vec_proj m T x) 
  (@tv2v_is_linear m T x).

HB.lock
Definition tf2f (m : qmemory) T1 T2 (x1 : qreg T1) (x2 : qreg T2) 
  (f : 'Hom{T1, T2}) : 'F[@mem_system m]_(qreg_set m x1, qreg_set m x2) 
  := \sum_(i : evalQT T1) \sum_(j : evalQT T2)
    [< ''j ; f ''i >] *: [> vec_proj m x2 ''j ; vec_proj m x1 ''i <].
Lemma tf2f_is_linear m T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  linear (@tf2f m T1 T2 x1 x2).
Proof.
move=>a f g; rewrite tf2f.unlock scaler_sumr -big_split; apply eq_bigr=>i _.
rewrite/= scaler_sumr -big_split; apply eq_bigr=>j _.
by rewrite/= scalerA -scalerDl lfunE/= lfunE/= linearPr/=.
Qed.
#[export]
HB.instance Definition _ m T1 T2 x1 x2 := GRing.isLinear.Build C 'Hom{T1, T2}
  'F[@mem_system m]_(qreg_set m x1, qreg_set m x2) *:%R (@tf2f m T1 T2 x1 x2)
  (@tf2f_is_linear m T1 T2 x1 x2).

Definition tm2m m (F : finType) T1 T2 (x1 : qreg T1) 
  (x2 : qreg T2) (f : F -> 'Hom{T1, T2}) := (fun i : F => tf2f m x1 x2 (f i)).

HB.lock
Definition v2tv m T (x : qreg T) (u : 'H[@mem_system m]_(qreg_set m x)) :=
  \sum_i [< vec_proj m x ''i ; u >] *: ''i.
Lemma v2tv_is_linear m T x : linear (@v2tv m T x).
Proof.
move=>a u v; rewrite v2tv.unlock scaler_sumr -big_split/=.
by apply eq_bigr=>i _; rewrite linearP/= scalerA scalerDl.
Qed.

#[export]
HB.instance Definition _ m T x := GRing.isLinear.Build
  C 'H[@mem_system m]_(qreg_set m x) 'Ht T
  *:%R (@v2tv m T x) (@v2tv_is_linear m T x).

HB.lock
Definition f2tf (m : qmemory) T1 T2 (x1 : qreg T1) (x2 : qreg T2) 
  (f : 'F[@mem_system m]_(qreg_set m x1, qreg_set m x2)) : 'Hom{T1, T2}
  := \sum_(i : evalQT T1) \sum_(j : evalQT T2)
    [< vec_proj m x2 ''j ; f (vec_proj m x1 ''i) >] *: [> ''j ; ''i <]. 
Lemma f2tf_is_linear m T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  linear (@f2tf m T1 T2 x1 x2).
Proof.
move=>a f g; rewrite f2tf.unlock scaler_sumr -big_split; apply eq_bigr=>i _.
rewrite/= scaler_sumr -big_split; apply eq_bigr=>j _.
by rewrite/= scalerA -scalerDl lfunE/= lfunE/= linearPr/=.
Qed.
#[export]
HB.instance Definition _ m T1 T2 x1 x2 := GRing.isLinear.Build C 
  'F[@mem_system m]_(qreg_set m x1, qreg_set m x2) 'Hom{T1, T2} 
  *:%R (@f2tf m T1 T2 x1 x2) (@f2tf_is_linear m T1 T2 x1 x2).

HB.lock
Definition v2tU (m : qmemory) T (x : qreg T) :=
  \sum_i [> ''i ; vec_proj m x ''i <].

HB.lock
Definition tket (m : qmemory) T (x : qreg T) (v : 'Ht T) : 'D[@mem_system m] := 
    ketd (vec_proj m x v).

HB.lock
Definition tbra (m : qmemory) T (x : qreg T) (v : 'Ht T) : 'D[@mem_system m] := 
    brad (vec_proj m x v).

HB.lock
Definition tlin (m : qmemory) T1 T2 (x1 : qreg T1) (x2 : qreg T2) 
  (f : 'Hom{T1,T2}) : 'D[@mem_system m] := lind (tf2f m x1 x2 f).

Module Exports.

Notation mem_lab := mem_label.
Notation mem_sys := mem_system.
Notation mem_set := qreg_set.
Notation tv2v := vec_proj.
Notation tf2f := tf2f.
Notation v2tv := v2tv.
Notation f2tf := f2tf.
Notation tm2m := tm2m.
Notation v2tU := v2tU.
Notation tket := tket.
Notation tbra := tbra.
Notation tlin := tlin.
Notation QMemMixin := Mixin.
Notation qmemType := qmemory. 
Notation QMemType := QMemory.

HB.reexport.

End Exports.

End QMemory.
Export QMemory.Exports.

(* TODO : in quantum, adding bi_isolfType; adding QMP projective quantum measurement *)
(* isolf theory *)
From quantum.external Require Import spectral.

Section QMemoryTheory.
Variable (QMem : qmemType).
Local Notation L := (mem_lab QMem).
Local Notation H := (@mem_sys QMem).
Local Notation mset := (mem_set QMem).
Local Notation tv2v := (tv2v QMem).
Local Notation tf2f := (tf2f QMem).
Local Notation v2tv := (@v2tv QMem _).
Local Notation f2tf := (@f2tf QMem _ _).
Local Notation tm2m := (tm2m QMem).
Local Notation v2tU := (@v2tU QMem).

Lemma disj_setE T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  (disjoint_qreg x1 x2) = [disjoint mset x1 & mset x2].
Proof. by case: QMem=>???? []. Qed.

Lemma tv2v_onb_t2tv T (x : 'QReg[T]) :
  forall i j, [< tv2v x (t2tv i) ; tv2v x (t2tv j) >] = (i == j)%:R.
Proof. by case: QMem=>???? []. Qed.

Lemma tv2v_dot T (x : 'QReg[T]) (u v : 'Ht T) :
  [< tv2v x u ; tv2v x v>] = [< u ; v >].
Proof.
rewrite [v](onb_vec (@t2tv _))/= !linear_sum; apply eq_bigr => i _.
rewrite/= !linearZ; f_equal.
rewrite [u](onb_vec t2tv)/= linear_sum !linear_suml.
apply eq_bigr => j _/=; rewrite/= linearZ !linearZl_LR; f_equal.
by rewrite /= onb_dot tv2v_onb_t2tv.
Qed.

Lemma qreg_dim T (x : 'QReg[T]) :
  #|evalQT T| = dim 'H[H]_(mset x).
Proof. by case: QMem=>???? []. Qed.

Definition tv2v_fun T (x : qreg T) (F : finType) (f : F -> 'Ht T) :=
  (fun i : F => tv2v x (f i)).
Lemma tv2v_onb T (x : 'QReg[T]) (F : finType) (ponb : 'PONB(F; 'Ht T)) :
  forall i j, [< tv2v x (ponb i) ; tv2v x (ponb j) >] = (i == j)%:R.
Proof. by move=>i j; rewrite tv2v_dot ponb_dot. Qed.
HB.instance Definition _ T (x : 'QReg[T]) (F : finType) (ponb : 'PONB(F; 'Ht T)) := 
  isPONB.Build _ F (tv2v_fun x ponb) (@tv2v_onb T x F ponb).
Lemma tv2v_card T (x : 'QReg[T]) (F : finType) (onb : 'ONB(F; 'Ht T)) :
  #|F| = dim 'H[H]_(mset x).
Proof. by rewrite -qreg_dim (@onb_card _ _ onb) ihb_dim_cast. Qed.
HB.instance Definition _ T (x : 'QReg[T]) (F : finType) (onb : 'ONB(F; 'Ht T)) := 
  isFullDim.Build _ F (tv2v_fun x onb) (@tv2v_card T x F onb).

Lemma t2v_dec T (x : qreg T) (u : 'H_(mset x)) :
  u = \sum_i [< tv2v x ''i ; u >] *: tv2v x ''i.
Proof. by move: T x u; case: QMem=>???? []. Qed.

Lemma t2v_dot_neq T (x : qreg T) (i j : evalQT T) :
  i != j -> [< tv2v x ''i ; tv2v x ''j >] = 0.
Proof. by move: T x i j; case: QMem=>???? []. Qed.

Lemma v2tUM T (x : qreg T) : (v2tU x)^A \o v2tU x = \1.
Proof.
apply/lfunP=>u; rewrite [u]t2v_dec !lfunE/= !linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/=; f_equal; rewrite {2}QMemory.v2tU.unlock sum_lfunE (bigD1 i)//= big1 ?addr0.
by move=>j /(t2v_dot_neq x) P; rewrite outpE P scale0r.
rewrite QMemory.v2tU.unlock [RHS]t2v_dec adjf_sum sum_lfunE; apply eq_bigr=>j _.
rewrite adj_outp !outpE dotpZr onb_dot; case: eqP=>[ <-|]; rewrite ?mulr1//.
by move=>/eqP/(t2v_dot_neq x)->; rewrite mulr0.
Qed.

Lemma v2tU_isolf T (x : qreg T) : v2tU x \is isolf.
Proof. by apply/isolfP/v2tUM. Qed.
HB.instance Definition _ T (x : qreg T) := 
  isIsoLf.Build _ _ (v2tU x) (@v2tU_isolf T x).

Lemma v2tUMV T (x : 'QReg[T]) : v2tU x \o (v2tU x)^A = \1.
Proof.
rewrite QMemory.v2tU.unlock [RHS](onb_lfun2id t2tv) exchange_big.
rewrite linear_suml/=; apply eq_bigr=>i _; rewrite adjf_sum linear_sumr/=.
by apply eq_bigr=>j _; rewrite lfunE/= adj_outp outp_comp tv2v_dot.
Qed.

Lemma v2tU_gisolf T (x : 'QReg[T]) : (v2tU x) \is gisolf.
Proof. by rewrite gisolfE v2tUMV isofE !eqxx. Qed.
HB.instance Definition _ T (x : 'QReg[T]) :=
  Iso_isGisoLf.Build _ _ (v2tU x) (@v2tU_gisolf T x).

Lemma tv2v_UE T (x : qreg T) u : tv2v x u = (v2tU x)^A u.
Proof.
rewrite [u](onb_vec t2tv) !linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/=; f_equal; rewrite QMemory.v2tU.unlock adjf_sum sum_lfunE (bigD1 i)//= big1.
by move=>j /negPf nji; rewrite adj_outp outpE onb_dot nji scale0r.
by rewrite adj_outp outpE ns_dot scale1r addr0.
Qed.

Lemma v2tv_UE T (x : qreg T) u : @v2tv x u = v2tU x u.
Proof.
rewrite [u]t2v_dec; rewrite !linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/=; f_equal; rewrite QMemory.v2tv.unlock QMemory.v2tU.unlock sum_lfunE.
by apply eq_bigr=>j _; rewrite outpE.
Qed.

Lemma tv2v_out T1 T2 (x1 : qreg T1) (x2 : qreg T2) (v1 : 'Ht T1) (v2 : 'Ht T2) :
    [> tv2v x1 v1 ; tv2v x2 v2 <] = tf2f x2 x1 [> v1 ; v2 <].
Proof.
rewrite {1}[v1](onb_vec t2tv) {1}[v2](onb_vec t2tv)/=.
rewrite ![tv2v _ _]linear_sum/= QMemory.tf2f.unlock linear_sumr/=.
apply eq_bigr=>i _/=; rewrite linear_suml; apply eq_bigr=>j _/=.
by rewrite linearZ linearZl_LR/= linearZ linearZr scalerA conj_dotp outpE linearZr/= mulrC.
Qed.

Lemma t2f_dec T1 T2 (x1 : qreg T1) (x2 : qreg T2) (f : 'F[H]_(mset x1,mset x2)) :
  f = \sum_i [> f (tv2v x1 ''i) ; tv2v x1 ''i <].
Proof.
apply/lfunP=>u; rewrite (t2v_dec u) !linear_sum/=.
apply eq_bigr=>i _; rewrite !linearZ/=; f_equal.
rewrite {1}[tv2v x1 ''i]t2v_dec linear_sum/= sum_lfunE. apply eq_bigr=>j _.
by rewrite linearZ/= outpE.
Qed.

Lemma tf2f_UE T1 T2 (x1 : qreg T1) (x2 : qreg T2) f :
  tf2f x1 x2 f = (v2tU x2)^A \o f \o (v2tU x1).
Proof.
rewrite [f](onb_lfun2 t2tv t2tv) linear_sum/= linear_sumr/= linear_suml/=.
apply eq_bigr=>i _; rewrite linear_sum/= linear_sumr/= linear_suml/=.
apply eq_bigr=>j _; rewrite linearZ/= linearZr linearZl/=; f_equal.
by rewrite -tv2v_out outp_compr outp_compl -!tv2v_UE.
Qed.

Lemma f2tf_UE T1 T2 (x1 : qreg T1) (x2 : qreg T2) f :
  @f2tf x1 x2 f = (v2tU x2) \o f \o (v2tU x1)^A.
Proof.
rewrite QMemory.f2tf.unlock.
under eq_bigr do under eq_bigr do rewrite !tv2v_UE -!comp_lfunE -adj_dotEl -outp_comp
 -!comp_lfunE -adjf_comp -outp_compl -comp_lfunA.
under eq_bigr do rewrite -linear_suml/= sumonb_out comp_lfun1l.
by rewrite -linear_sumr/= sumonb_out comp_lfun1r comp_lfunA.
Qed.

Lemma t2v_dot_eq T (x : qreg T) (i : evalQT T) :
  [< tv2v x ''i ; tv2v x ''i >] = 1 \/ tv2v x ''i = 0.
Proof.
suff: ([< tv2v x ''i ; tv2v x ''i >] - 1) *: tv2v x ''i == 0.
rewrite scaler_eq0=>/orP[|/eqP->]; last by right.
by rewrite subr_eq0=>/eqP->; left.
by rewrite scalerBl scale1r subr_eq0 [X in _ == X]t2v_dec (bigD1 i) ?big1/= 
  ?addr0//= =>[j/t2v_dot_neq->]; rewrite scale0r.
Qed.

(* Lemma t2v_dot_neq0 T (x : qreg T) (i : evalQT T) (v : 'Ht T) :
  [< tv2v x ''i ; tv2v x ''i >] = 1 ->
    [< tv2v x ''i ; tv2v x v >] = [< ''i ; v >].
Proof.
move=>Pi; rewrite [v](onb_vec t2tv)/= !linear_sum.
apply eq_bigr=>j _ /=; rewrite !linearZ/=; f_equal.
case E: (i == j).
by move: E=>/eqP<-; rewrite Pi ns_dot.
by rewrite onb_dot E; move: E=>/eqP/eqP/t2v_dot_neq->.
Qed. *)

Lemma tv2vK {T} {x : 'QReg[T]} : cancel (@tv2v T x) (@v2tv x).
Proof. by move=>u; rewrite tv2v_UE v2tv_UE -comp_lfunE v2tUMV lfunE. Qed.

Lemma v2tvK {T} {x : qreg T} : cancel (@v2tv x) (@tv2v T x).
Proof. by move=>u; rewrite tv2v_UE v2tv_UE -comp_lfunE v2tUM lfunE. Qed.

Lemma v2tv_inj {T} {x : qreg T} : injective (@v2tv x).
Proof. exact: (can_inj v2tvK). Qed.

Lemma tv2v_inj {T} {x : 'QReg[T]} : injective (@tv2v T x).
Proof. exact: (can_inj tv2vK). Qed.

Lemma tf2fK {T1 T2} {x1 : 'QReg[T1]} {x2 : 'QReg[T2]} : 
  cancel (@tf2f T1 T2 x1 x2) (@f2tf x1 x2).
Proof.
by move=>f; rewrite f2tf_UE tf2f_UE !comp_lfunA
  v2tUMV comp_lfun1l -comp_lfunA v2tUMV comp_lfun1r.
Qed.

Lemma f2tfK {T1 T2} {x1 : qreg T1} {x2 : qreg T2} : 
  cancel (@f2tf x1 x2) (@tf2f T1 T2 x1 x2).
Proof.
by move=>f; rewrite f2tf_UE tf2f_UE !comp_lfunA 
  v2tUM comp_lfun1l -comp_lfunA v2tUM comp_lfun1r.
Qed.

Lemma tf2f_inj {T1 T2} {x1 : 'QReg[T1]} {x2 : 'QReg[T2]} :
  injective (@tf2f T1 T2 x1 x2).
Proof. exact: (can_inj tf2fK). Qed.

Lemma f2tf_inj {T1 T2} {x1 : qreg T1} {x2 : qreg T2} : 
  injective (@f2tf x1 x2).
Proof. exact: (can_inj f2tfK). Qed.

Lemma tv2v_conj T (x : qreg T) (v : 'Ht T) :
  (tv2v x v)^*v = tv2v x (v^*v).
Proof. by move: T x v; case: QMem=>???? []. Qed.

Lemma v2tU_conj T (x : qreg T) : (v2tU x)^C = v2tU x.
Proof. by apply/adjf_inj/lfunP=>u; rewrite lfCAC conjfE -!tv2v_UE tv2v_conj conjvK. Qed.

Section BasicProperty.
Variable (T T1 T2 T3 : qType).
Variable (x : qreg T) (x1 : qreg T1) (x2 : qreg T2) (x3 : qreg T3).
Variable (y : 'QReg[T]) (y1 : 'QReg[T1]) (y2 : 'QReg[T2]) (y3 : 'QReg[T3]).

Lemma tv2v_dotr (u : 'H_(mset x)) (v : 'Ht T) :
  [< u ; tv2v x v >] = [< v2tv u ; v >].
Proof. by rewrite tv2v_UE adj_dotEr v2tv_UE. Qed.

Lemma tv2v_dotl (u : 'Ht T) (v : 'H_(mset x)):
  [< tv2v x u ; v >] = [< u; v2tv v >].
Proof. by rewrite -conj_dotp tv2v_dotr conj_dotp. Qed.

Lemma v2tv_dot u v : [<@v2tv x u ; v2tv v >] = [<u ; v>].
Proof. by rewrite -tv2v_dotl v2tvK. Qed.

Lemma tv2v_norm (u : 'Ht T) : `| tv2v y u | = `| u |.
Proof. by rewrite !hnormE tv2v_dot. Qed.

Lemma v2tv_norm u : `| @v2tv x u | = `| u |.
Proof. by rewrite !hnormE v2tv_dot. Qed.

Lemma v2tv_conj v : (@v2tv x v)^*v = v2tv (v^*v).
Proof. by rewrite !v2tv_UE -{1}[v2tU x]conjfK conjfE conjvK v2tU_conj. Qed.

Lemma tf2f_comp f g :
    tf2f y1 x2 f \o tf2f x3 y1 g = tf2f x3 x2 (f \o g).
Proof.
by rewrite !tf2f_UE !comp_lfunA -[_ \o v2tU y1 \o _]comp_lfunA v2tUMV comp_lfun1r.
Qed.

Lemma f2tf_comp f g :
    @f2tf x1 x2 f \o @f2tf x3 x1 g = @f2tf x3 x2 (f \o g).
Proof.
by rewrite !f2tf_UE !comp_lfunA -[_ \o _ \o v2tU x1]comp_lfunA v2tUM comp_lfun1r.
Qed.

Lemma tf2f_adj f : (tf2f x1 x2 f)^A = tf2f x2 x1 (f^A).
Proof. by rewrite !tf2f_UE !adjf_comp adjfK comp_lfunA. Qed.

Lemma tf2f_conj f : (tf2f x1 x2 f)^C = tf2f x1 x2 (f^C).
Proof. by rewrite !tf2f_UE !conjf_comp lfACC !v2tU_conj. Qed.

Lemma tf2f_tr f : (tf2f x1 x2 f)^T = tf2f x2 x1 (f^T).
Proof. by rewrite !trfCA tf2f_conj tf2f_adj. Qed.

Lemma tf2f1 : tf2f x x \1 = \1.
Proof.
rewrite [RHS]t2f_dec [\1](onb_lfun t2tv)/= linear_sum.
by apply eq_bigr=>i _; rewrite !lfunE/= tv2v_out.
Qed.

Lemma tf2f_trlf f : \Tr (tf2f y y f) = \Tr f.
Proof. by rewrite tf2f_UE lftraceC comp_lfunA v2tUMV comp_lfun1l. Qed. 

Lemma f2tf_adj f : (@f2tf x1 x2 f)^A = f2tf (f^A).
Proof. by rewrite !f2tf_UE !adjf_comp adjfK comp_lfunA. Qed.

Lemma f2tf_conj f : (@f2tf x1 x2 f)^C = f2tf (f^C).
Proof. by rewrite !f2tf_UE !conjf_comp lfACC !v2tU_conj. Qed.

Lemma f2tf_tr f : (@f2tf x1 x2 f)^T = f2tf (f^T).
Proof. by rewrite !trfCA f2tf_conj f2tf_adj. Qed.

Lemma f2tf1 : @f2tf y y \1 = \1.
Proof. by rewrite f2tf_UE comp_lfun1r v2tUMV. Qed.

Lemma f2tf_trlf f : \Tr (@f2tf x x f) = \Tr f.
Proof. by rewrite f2tf_UE lftraceC comp_lfunA v2tUM comp_lfun1l. Qed. 

Lemma tf2f_apply f v : (tf2f y1 x2 f) (tv2v y1 v) = tv2v x2 (f v).
Proof. by rewrite tf2f_UE !tv2v_UE -!comp_lfunE -!comp_lfunA v2tUMV comp_lfun1r. Qed.

Lemma f2tf_apply f v : (@f2tf x1 x2 f) (v2tv v) = v2tv (f v).
Proof. by rewrite f2tf_UE !v2tv_UE -!comp_lfunE -!comp_lfunA v2tUM comp_lfun1r. Qed.

Lemma tf2f_apply_v2tv f v :
    (tf2f x1 x2 f) v = tv2v x2 (f (v2tv v)).
Proof. by rewrite tf2f_UE tv2v_UE v2tv_UE -!comp_lfunE. Qed.

Lemma f2tf_apply_tv2v f v :
  (@f2tf x1 x2 f) v = v2tv (f (tv2v x1 v)).
Proof. by rewrite f2tf_UE tv2v_UE v2tv_UE -!comp_lfunE. Qed.

End BasicProperty.

Lemma tv2V_eqr T (x y : qreg T) :
  x =r y -> forall (v : 'Ht T), (tv2v x v) =v (tv2v y v).
Proof. by move: T x y; case: QMem=>???? []. Qed.

Lemma mset_eqr T (x1 x2 : qreg T) :
  x1 =r x2 -> mset x1 = mset x2.
Proof. by move=>/tv2V_eqr/(_ ''(witness _))/eq_Hnd1. Qed.

Lemma tv2v_eqr T (x y : qreg T) (eqxy : x =r y) (v : 'Ht T) :
  casths (mset_eqr eqxy) (tv2v x v) = (tv2v y v).
Proof. by to_Hnd; exact: tv2V_eqr. Qed.

Lemma tf2f_eqr T1 T2 (x1 x2 : qreg T1) (y1 y2 : qreg T2) (eqx : x1 =r x2)
  (eqy : y1 =r y2) (f : 'Hom{T1,T2}) :
    castlf (mset_eqr eqx, mset_eqr eqy) (tf2f x1 y1 f) = (tf2f x2 y2 f).
Proof.
rewrite [f](onb_lfun2 t2tv t2tv) pair_big !linear_sum.
apply eq_bigr=>i _; rewrite 3 !linearZ/=; f_equal.
by rewrite -!tv2v_out castlf_outp !tv2v_eqr.
Qed.

Lemma tf2F_eqr T1 T2 (x1 x2 : qreg T1) (y1 y2 : qreg T2) (eqx : x1 =r x2)
  (eqy : y1 =r y2) (f : 'Hom{T1,T2}) :
    (tf2f x1 y1 f) =c (tf2f x2 y2 f).
Proof. by rewrite -(tf2f_eqr eqx eqy) Fnd_cast. Qed.

Lemma t2V_pair T1 T2 (x1 : qreg T1) (x2 : qreg T2) 
  (t1 : evalQT T1) (t2 : evalQT T2) :
    ((tv2v x1 ''t1)%:Hnd ⊗v (tv2v x2 ''t2)%:Hnd)%FND = 
      (tv2v <{(x1,x2)}> (''t1 ⊗t ''t2))%:Hnd.
Proof. by move: T1 T2 x1 x2 t1 t2; case: QMem=>???? []. Qed.

Lemma t2V_tuple n T (x : 'I_n -> qreg T) (t : n.-tuple (evalQT T)) :
    (\tenv_i (tv2v (x i) ''(t ~_ i))%:Hnd)%FND =
      (tv2v <{ tuple: x }> ''t)%:Hnd.
Proof. by move: n T x t; case: QMem=>???? []. Qed.

Lemma t2V_ffun n (T : 'I_n -> qType) (x : forall i, qreg (T i)) 
  (t : {dffun forall i, eval_qtype (T i)}) :
    (\tenv_i (tv2v (x i) ''(t i))%:Hnd)%FND = 
      (tv2v <{ ffun: x }> ''t)%:Hnd.
Proof. by move: n T x t; case: QMem=>???? []. Qed.

Lemma mset_pair {T1 T2} {x1 : qreg T1} {x2 : qreg T2} :
  mset x1 :|: mset x2 = mset <{(x1,x2)}>.
Proof. by move: (t2V_pair x1 x2 (witness _) (witness _))=>/eq_Hnd1. Qed.

Lemma mset_pairV {T1 T2} {x : qreg (T1 * T2)} :
  mset x = mset <{x.1}> :|: mset <{x.2}>.
Proof. by rewrite mset_pair (mset_eqr (eq_qreg_pair _)). Qed.

Lemma mset_tuple {n T} {x : 'I_n -> qreg T} :
  \bigcup_i mset (x i) = mset <{(tuple i => x i)}>.
Proof. by move: (t2V_tuple x (witness _)); rewrite -to_Hnd_tens=>/eq_Hnd1. Qed.

Lemma mset_tupleV {n T} {x : qreg (QArray n T)} :
  mset x = \bigcup_i mset <{x.[i]}>.
Proof. by rewrite mset_tuple (mset_eqr (eq_qreg_tuple _)). Qed.

Lemma mset_ffun {n} {T : 'I_n -> qType} {x : forall i, qreg (T i)} :
  \bigcup_i mset (x i) = mset <{(ffun i => x i)}>.
Proof. by move: (t2V_ffun x (witness _)); rewrite -to_Hnd_tens=>/eq_Hnd1. Qed.

Lemma mset_ffunV {n} {T : 'I_n -> qType} {x : qreg (QDFFun T)} :
  mset x = \bigcup_i mset <{x.-[i]}>.
Proof. by rewrite mset_ffun (mset_eqr (eq_qreg_ffun _)). Qed.

Definition mset_basic_index (i : basic_index) := 
  mset (projT1 (cid (exists_qreg (projT2 (qtype_of_basic_index i))))).

Lemma mset_eqi (T1 T2 : qType) (x1 : qreg T1) (x2 : qreg T2) :
  index_of_qreg x1 = index_of_qreg x2 -> mset x1 = mset x2.
Proof.
move=>H1; move: {+}H1=>/(f_equal qtype_of_index).
rewrite !index_typeK=>Pv; inversion Pv; case: T2 / H0 x2 H1 Pv=>x2 Px _.
by apply/mset_eqr; rewrite /eq_qreg/qr2seq Px.
Qed.

Lemma mset_basic_type (T : qType) (x : qreg T) (H : basic_type T) :
  mset x = mset_basic_index (Basic_Index (basic_index_type x H)).
Proof.
rewrite /mset_basic_index; apply/mset_eqi.
move: (projT2 (cid (exists_qreg (projT2 (qtype_of_basic_index (Basic_Index (basic_index_type x H)))))))=>->.
by rewrite /basic_index_to_qreg_index/=; move: (projT2 (basic_type_prime x H)).
Qed.

Lemma mset_fset_qreg T (x : qreg T) :
  mset x = (\bigcup_(i <- fset_qreg x) mset_basic_index i)%SET.
Proof.
elim: T x=>[x|x|n x|T _ x| | T1 _ T2 _ x||].
1-4,6: by rewrite (fset_basic_type x _) big_seq_fset1 -mset_basic_type.
- move=>T1 IH1 T2 IH2 x.
  rewrite -(mset_eqr (eq_qreg_pair _)) -mset_pair IH1 IH2 -big_fsetU_idem/=.
  by exact: finset.setUid.
  by apply congr_big=>//; rewrite -fset_qreg_pairV.
- move=>n T Pi x.
  rewrite -(mset_eqr (eq_qreg_tuple _)) -mset_tuple.
  under eq_bigr do rewrite Pi.
  rewrite big_fsetUs_idem /=; first by exact: finset.setUid.
  by apply congr_big=>//; rewrite -fset_qreg_tupleV.
- move=>n fT Pi x.
  rewrite -(mset_eqr (eq_qreg_ffun _)) -mset_ffun.
  under eq_bigr do rewrite Pi.
  rewrite big_fsetUs_idem /=; first by exact: finset.setUid.
  by apply congr_big=>//; rewrite -fset_qreg_ffunV.
Qed.

Lemma tv2v_pairE T1 T2 (x : qreg (T1 * T2)) :
  (casths (mset_eqr (eq_qreg_pair _)) \o (tv2v <{(x.1,x.2)}>))%FUN = (tv2v x).
Proof. by apply/funext=>v/=; rewrite tv2v_eqr. Qed.

Lemma tv2v_tupleE n T (x : qreg (T.[n])) :
  (casths (mset_eqr (eq_qreg_tuple _)) \o (tv2v <{(tuple i => x.[i])}>))%FUN = tv2v x.
Proof. by apply/funext=>v/=; rewrite tv2v_eqr. Qed.

Lemma tv2v_ffunE n (T : 'I_n -> qType) (x : qreg {qffun T}) :
  (casths (mset_eqr (eq_qreg_ffun _)) \o (tv2v <{(ffun i => x.-[i])}>))%FUN = tv2v x.
Proof. by apply/funext=>v/=; rewrite tv2v_eqr. Qed.

Lemma tv2v_pair T1 T2 (x1 : qreg T1) (x2 : qreg T2) (t1 : 'Ht T1) (t2 : 'Ht T2) :
  casths mset_pair (tv2v x1 t1 ⊗v tv2v x2 t2) = tv2v <{(x1,x2)}> (t1 ⊗t t2).
Proof.
rewrite [t1](onb_vec t2tv) [t2](onb_vec t2tv).
rewrite !linear_sum/=; apply eq_bigr=>i _.
rewrite !linear_suml !linear_sum; apply eq_bigr=>j _.
rewrite/= !linearZ/=; f_equal.
rewrite !linearZl_LR !linearZ/=; f_equal.
by apply/to_Hnd_inj; rewrite Hnd_cast to_HndE t2V_pair.
Qed.

Lemma tv2V_pair T1 T2 (x1 : qreg T1) (x2 : qreg T2) (t1 : 'Ht T1) (t2 : 'Ht T2) :
  ((tv2v x1 t1)%:Hnd ⊗v (tv2v x2 t2)%:Hnd)%FND = (tv2v <{(x1,x2)}> (t1 ⊗t t2))%:Hnd.
Proof. by rewrite -tv2v_pair Hnd_cast. Qed.

Lemma tv2v_pairV T1 T2 (x : qreg (T1 * T2)) (t1 : 'Ht T1) (t2 : 'Ht T2) :
  casths mset_pairV (tv2v x (t1 ⊗t t2)) = (tv2v <{x.1}> t1 ⊗v tv2v <{x.2}> t2).
Proof. by to_Hnd; rewrite/= tv2V_pair; apply tv2V_eqr; rewrite eq_qreg_pair. Qed.

Lemma tv2V_pairV T1 T2 (x : qreg (T1 * T2)) (t1 : 'Ht T1) (t2 : 'Ht T2) :
  (tv2v x (t1 ⊗t t2))%:Hnd = ((tv2v <{x.1}> t1)%:Hnd ⊗v (tv2v <{x.2}> t2)%:Hnd)%FND.
Proof. by rewrite -to_HndE -tv2v_pairV Hnd_cast. Qed.

Lemma tf2f_pair T11 T12 T21 T22 (x11 : qreg T11) (x12 : qreg T12)
  (x21 : qreg T21) (x22 : qreg T22) (f1 : 'Hom{T11, T12}) (f2 : 'Hom{T21, T22}) :
  castlf (mset_pair, mset_pair) (tf2f x11 x12 f1 \⊗ tf2f x21 x22 f2) = 
    tf2f <{(x11,x21)}> <{(x12,x22)}> (f1 ⊗f f2).
Proof.
rewrite [f1](onb_lfun2 t2tv t2tv) pair_big/= linear_sum !linear_suml !linear_sum.
apply eq_bigr=>[[i1 i2]] _/=; rewrite linearZ/= 2!linearZl_LR/= !linearZ; f_equal.
rewrite [f2](onb_lfun2 t2tv t2tv) pair_big/= !linear_sum.
apply eq_bigr=>[[j1 j2]] _/=; rewrite !linearZ/=; f_equal.
rewrite -!tv2v_out tenf_outp tentv_out !tentv_t2tv -tv2v_out castlf_outp.
by f_equal; rewrite tv2v_pair tentv_t2tv.
Qed.

Lemma tf2F_pair T11 T12 T21 T22 (x11 : qreg T11) (x12 : qreg T12) 
  (x21 : qreg T21) (x22 : qreg T22) (f1 : 'Hom{T11, T12}) (f2 : 'Hom{T21, T22}) :
    ((tf2f x11 x12 f1)%:Fnd \⊗ (tf2f x21 x22 f2)%:Fnd)%FND =
      (tf2f <{(x11,x21)}> <{(x12,x22)}> (f1 ⊗f f2))%:Fnd.
Proof. by rewrite -tf2f_pair Fnd_cast. Qed.

Lemma tf2f_pairV T11 T12 T21 T22 (x1 : qreg (T11 * T21)) (x2 : qreg (T12 * T22))
  (f1 : 'Hom{T11, T12}) (f2 : 'Hom{T21, T22}) :
  castlf (mset_pairV, mset_pairV) (tf2f x1 x2 (f1 ⊗f f2)) =
    (tf2f <{x1.1}> <{x2.1}> f1 \⊗ tf2f <{x1.2}> <{x2.2}> f2).
Proof. by to_Fnd; rewrite tf2F_pair; apply tf2F_eqr; rewrite eq_qreg_pair. Qed.

Lemma tf2F_pairV T11 T12 T21 T22 (x1 : qreg (T11 * T21)) (x2 : qreg (T12 * T22))
  (f1 : 'Hom{T11, T12}) (f2 : 'Hom{T21, T22}) :
    (tf2f x1 x2 (f1 ⊗f f2))%:Fnd = 
      ((tf2f <{x1.1}> <{x2.1}> f1)%:Fnd \⊗ (tf2f <{x1.2}> <{x2.2}> f2)%:Fnd)%FND.
Proof. by rewrite -to_FndE -tf2f_pairV Fnd_cast. Qed.

Lemma tv2v_tuple n T (x : 'I_n -> qreg T) (t : 'I_n -> ('Ht T)) :
  casths (mset_tuple) (tenvm (fun i => tv2v (x i) (t i))) = (tv2v <{ tuple: x }> (tentv_tuple t)).
Proof.
under tenvmP do rewrite [t _](onb_vec t2tv) linear_sum.
rewrite tenvm_sum linear_sum/= [tentv_tuple t](onb_vec t2tv)/= linear_sum.
pose h (i : n.-tuple (evalQT T)) := \mvector_(j : 'I_n) (i ~_ j).
rewrite (reindex h).
  exists (fun i : mvector (fun j => evalQT T) => [tuple j => i j])=>i _.
  by apply eq_from_tnth=>j; rewrite tnthE /h mvE.
  by apply/mvectorP=>j; rewrite /h mvE tnthE.
apply eq_bigr=>i _; under tenvmP do rewrite linearZ.
rewrite tenvmZ linearZ !linearZ; f_equal.
by rewrite t2tv_tuple tentv_tuple_dot; under eq_bigr do rewrite mvE.
by to_Hnd; rewrite -t2V_tuple; under eq_bigr do rewrite mvE.
Qed.

Lemma tv2V_tuple n T (x : 'I_n -> qreg T) (t : 'I_n -> ('Ht T)) :
  (\tenv_i (tv2v (x i) (t i))%:Hnd)%FND = (tv2v <{ tuple: x }> (tentv_tuple t))%:Hnd.
Proof. by rewrite -tv2v_tuple Hnd_cast to_Hnd_tens. Qed.

Lemma tv2V_tupleV n T (x : qreg (T.[n])) (t : 'I_n -> ('Ht T)) :
  (tv2v x (tentv_tuple t))%:Hnd = (\tenv_i (tv2v <{x.[i]}> (t i))%:Hnd)%FND.
Proof. by rewrite tv2V_tuple; apply tv2V_eqr; rewrite eq_qreg_tuple. Qed.

Lemma tv2v_tupleV n T (x : qreg (T.[n])) (t : 'I_n -> ('Ht T)) :
  casths mset_tupleV (tv2v x (tentv_tuple t)) = tenvm (fun i => tv2v <{x.[i]}> (t i)).
Proof. by to_Hnd; apply/tv2V_tupleV. Qed.

Lemma tf2f_tuple n T1 T2 (x : 'I_n -> qreg T1) (y : 'I_n -> qreg T2) 
  (t : 'I_n -> 'Hom{T1,T2}) :
    castlf (mset_tuple, mset_tuple) (tenfm (fun i => tf2f (x i) (y i) (t i))) 
      = (tf2f <{ tuple: x }> <{ tuple: y }> (tentf_tuple t)).
Proof.
under tenfmP do rewrite [t _](onb_lfun2 t2tv t2tv) pair_big/= linear_sum.
rewrite tenfm_sum linear_sum/= [tentf_tuple t](onb_lfun2 t2tv t2tv).
rewrite pair_big linear_sum/=.
pose h (i : n.-tuple (evalQT T1) * n.-tuple (evalQT T2)) := 
  (\mvector_(j : 'I_n) (i.1 ~_ j, i.2 ~_ j)).
rewrite (reindex h).
  exists (fun i : mvector (fun j => ((evalQT T1) * (evalQT T2))%type) =>
    ([tuple j => (i j).1], [tuple j => (i j).2]))=>[[]i j|i] _.
  by f_equal; apply eq_from_tnth=>k; rewrite tnthE /h mvE/=.
  by apply/mvectorP=>j; rewrite /h/= mvE !tnthE/= -surjective_pairing.
apply eq_bigr=>[[i1 i2]] _/=.
under tenfmP do rewrite linearZ /h mvE/= -tv2v_out.
rewrite tenfmZ !linearZ/=; f_equal.
  by rewrite !t2tv_tuple tentf_tuple_apply tentv_tuple_dot.
by rewrite tenfm_outp castlf_outp !tv2v_tuple tv2v_out -!t2tv_tuple.
Qed.

Lemma tf2F_tuple n T1 T2 (x : 'I_n -> qreg T1) (y : 'I_n -> qreg T2) 
  (t : 'I_n -> 'Hom{T1,T2}) :
    (\tenf_i (tf2f (x i) (y i) (t i))%:Fnd)%FND = 
      (tf2f <{ tuple: x }> <{ tuple: y }> (tentf_tuple t))%:Fnd.
Proof. by rewrite -to_Fnd_tens -tf2f_tuple Fnd_cast. Qed.

Lemma tf2F_tupleV n T1 T2 (x : qreg (T1.[n])) (y : qreg (T2.[n]))
  (t : 'I_n -> 'Hom{T1,T2}) :
    (tf2f x y (tentf_tuple t))%:Fnd = 
      (\tenf_i (tf2f <{x.[i]}> <{y.[i]}> (t i))%:Fnd)%FND.
Proof. by rewrite tf2F_tuple; apply/tf2F_eqr; rewrite eq_qreg_tuple. Qed.

Lemma tf2f_tupleV n T1 T2 (x : qreg (T1.[n])) (y : qreg (T2.[n])) 
  (t : 'I_n -> 'Hom{T1,T2}) :
    castlf (mset_tupleV, mset_tupleV) (tf2f x y (tentf_tuple t)) 
      = tenfm (fun i => tf2f <{x.[i]}> <{y.[i]}> (t i)).
Proof. by to_Fnd; apply/tf2F_tupleV. Qed.  

Lemma tv2v_ffun n (T : 'I_n -> qType) (x : forall i, qreg (T i)) (t : forall i, 'Ht (T i)) :
  casths (mset_ffun) (tenvm (fun i => tv2v (x i) (t i))) = (tv2v <{ ffun: x }> (tentv_dffun t)).
Proof.
under tenvmP do rewrite [t _](onb_vec t2tv) linear_sum.
rewrite tenvm_sum linear_sum/= [tentv_dffun t](onb_vec t2tv)/= linear_sum.
pose h (i : {dffun forall i, (evalQT (T i))}) := \mvector_(j : 'I_n) (i j).
rewrite (reindex h).
  exists (fun i : mvector (fun j => evalQT (T j)) => [ffun j => i j])=>i _.
  by apply/ffunP=>j; rewrite ffunE /h mvE.
  by apply/mvectorP=>j; rewrite /h mvE ffunE.
apply eq_bigr=>i _; under tenvmP do rewrite linearZ.
rewrite tenvmZ linearZ !linearZ; f_equal.
by rewrite t2tv_dffun tentv_dffun_dot; under eq_bigr do rewrite mvE.
by to_Hnd; rewrite -t2V_ffun; under eq_bigr do rewrite mvE.
Qed.

Lemma tv2V_ffun n (T : 'I_n -> qType) (x : forall i, qreg (T i)) (t : forall i, 'Ht (T i)) :
  (\tenv_i (tv2v (x i) (t i))%:Hnd)%FND = (tv2v <{ ffun: x }> (tentv_dffun t))%:Hnd.
Proof. by rewrite -tv2v_ffun Hnd_cast to_Hnd_tens. Qed.

Lemma tv2V_ffunV n (T : 'I_n -> qType) (x : qreg {qffun T}) (t : forall i, 'Ht (T i)) :
  (tv2v x (tentv_dffun t))%:Hnd = (\tenv_i (tv2v <{x.-[i]}> (t i))%:Hnd)%FND.
Proof. by rewrite tv2V_ffun; apply tv2V_eqr; rewrite eq_qreg_ffun. Qed.

Lemma tv2v_ffunV n (T : 'I_n -> qType) (x : qreg {qffun T}) (t : forall i, 'Ht (T i)) :
  casths mset_ffunV (tv2v x (tentv_dffun t)) = tenvm (fun i => tv2v <{x.-[i]}> (t i)).
Proof. by to_Hnd; apply/tv2V_ffunV. Qed.

Lemma tf2f_ffun n (T1 T2 : 'I_n -> qType) (x : forall i, qreg (T1 i)) 
  (y : forall i, qreg (T2 i)) (t : forall i, 'Hom{T1 i, T2 i}) :
    castlf (mset_ffun, mset_ffun) (tenfm (fun i => tf2f (x i) (y i) (t i))) 
      = (tf2f <{ ffun: x }> <{ ffun: y }> (tentf_dffun t)).
Proof.
under tenfmP do rewrite [t _](onb_lfun2 t2tv t2tv) pair_big/= linear_sum.
rewrite tenfm_sum linear_sum/= [tentf_dffun t](onb_lfun2 t2tv t2tv).
rewrite pair_big linear_sum/=.
pose h (i : {dffun forall i, evalQT (T1 i)} * {dffun forall i, evalQT (T2 i)}) := 
  (\mvector_(j : 'I_n) (i.1 j, i.2 j)).
rewrite (reindex h).
  exists (fun i : mvector (fun j => (evalQT (T1 j) * evalQT (T2 j))%type) =>
    ([ffun j => (i j).1], [ffun j => (i j).2]))=>[[]i j|i] _.
  by f_equal; apply/ffunP=>k; rewrite ffunE /h mvE/=.
  by apply/mvectorP=>j; rewrite /h/= mvE !ffunE/= -surjective_pairing.
apply eq_bigr=>[[i1 i2]] _/=.
under tenfmP do rewrite linearZ /h mvE/= -tv2v_out.
rewrite tenfmZ !linearZ/=; f_equal.
  by rewrite !t2tv_dffun tentf_dffun_apply tentv_dffun_dot.
by rewrite tenfm_outp castlf_outp !tv2v_ffun tv2v_out -!t2tv_dffun.
Qed.

Lemma tf2F_ffun n (T1 T2 : 'I_n -> qType) (x : forall i, qreg (T1 i)) 
  (y : forall i, qreg (T2 i)) (t : forall i, 'Hom{T1 i, T2 i}) :
    (\tenf_i (tf2f (x i) (y i) (t i))%:Fnd)%FND = 
      (tf2f <{ ffun: x }> <{ ffun: y }> (tentf_dffun t))%:Fnd.
Proof. by rewrite -to_Fnd_tens -tf2f_ffun Fnd_cast. Qed.

Lemma tf2F_ffunV n (T1 T2 : 'I_n -> qType) (x : qreg {qffun T1}) 
  (y : qreg {qffun T2}) (t : forall i, 'Hom{T1 i, T2 i}) :
    (tf2f x y (tentf_dffun t))%:Fnd = 
      (\tenf_i (tf2f <{x.-[i]}> <{y.-[i]}> (t i))%:Fnd)%FND.
Proof. by rewrite tf2F_ffun; apply/tf2F_eqr; rewrite eq_qreg_ffun. Qed.

Lemma tf2f_ffunV n (T1 T2 : 'I_n -> qType) (x : qreg {qffun T1})
  (y : qreg {qffun T2}) (t : forall i, 'Hom{T1 i, T2 i}) :
    castlf (mset_ffunV, mset_ffunV) (tf2f x y (tentf_dffun t)) 
      = tenfm (fun i => tf2f <{x.-[i]}> <{y.-[i]}> (t i)).
Proof. by to_Fnd; apply/tf2F_ffunV. Qed.

Section LinearProp.

Variable (T T1 T2 : qType) (x : qreg T) (x1 : qreg T1) (x2 : qreg T2).
Implicit Type (c : C) (u v : 'Ht T) (f g : 'Hom{T1,T2}).

Lemma tv2vD u v : tv2v x u + tv2v x v = tv2v x (u + v).
Proof. by rewrite linearD. Qed.
Lemma tv2vB u v : tv2v x u - tv2v x v = tv2v x (u - v).
Proof. by rewrite linearB. Qed.
Lemma tv2vN u : - (tv2v x u) = tv2v x (- u).
Proof. by rewrite linearN. Qed.
Lemma tv2vZ c u : c *: tv2v x u = tv2v x (c *: u).
Proof. by rewrite linearZ. Qed.
Lemma tv2vP c u v : c *: tv2v x u + tv2v x v = tv2v x (c *: u + v).
Proof. by rewrite linearP. Qed.
Lemma tv2v0 : tv2v x 0 = 0.
Proof. by rewrite linear0. Qed.

Lemma tf2fD f g : tf2f x1 x2 f + tf2f x1 x2 g = tf2f x1 x2 (f + g).
Proof. by rewrite linearD. Qed.
Lemma tf2fB f g : tf2f x1 x2 f - tf2f x1 x2 g = tf2f x1 x2 (f - g).
Proof. by rewrite linearB. Qed.
Lemma tf2fN f : - (tf2f x1 x2 f) = tf2f x1 x2 (- f).
Proof. by rewrite linearN. Qed.
Lemma tf2fZ c f : c *: tf2f x1 x2 f = tf2f x1 x2 (c *: f).
Proof. by rewrite linearZ. Qed.
Lemma tf2fP c f g : c *: tf2f x1 x2 f + tf2f x1 x2 g = tf2f x1 x2 (c *: f + g).
Proof. by rewrite linearP. Qed.
Lemma tf2f0 : tf2f x1 x2 0 = 0.
Proof. by rewrite linear0. Qed.

End LinearProp.

Lemma tv2v_dot_ler T (x : qreg T) (v : 'Ht T) :
  [< tv2v x v ; tv2v x v >] <= [< v ; v >].
Proof. by rewrite tv2v_UE isofA_dot. Qed.

Lemma tv2v_ps T (x : qreg T) (v : 'PS('Ht T)) :
  [< tv2v x v ; tv2v x v >] <= 1.
Proof. by move: (ps_dot v); apply le_trans; apply/tv2v_dot_ler. Qed.
HB.instance Definition _ T (x : qreg T) (v : 'PS('Ht T)) := 
  isPartialState.Build 'H[H]_(mset x) (tv2v x v) (@tv2v_ps T x v).

Lemma tv2v_ns T (x : 'QReg[T]) (v : 'NS('Ht T)) :
  [< tv2v x v ; tv2v x v >] = 1.
Proof. by rewrite tv2v_dot ns_dot. Qed.
HB.instance Definition _ T (x : 'QReg[T]) (v : 'NS('Ht T)) := 
  Partial_isNormalState.Build _ (tv2v x v) (@tv2v_ns T x v).

Section EndProp.

Variable (T : qType) (x : qreg T) (y : 'QReg[T]).
Implicit Type (f : 'End{T}).

Lemma tf2f_bound1P (T' : qType) (z : qreg T') (g : 'Hom{T,T'}) :
  g \is bound1lf -> tf2f x z g \is bound1lf.
Proof.
move=>Pf; rewrite tf2f_UE; apply/bound1lf_comp; last by apply/is_bound1lf.
apply/bound1lf_comp=>[|//]; by apply/is_bound1lf.
Qed.
Lemma tf2f_bound1E (T' : qType) (z : 'QReg[T']) (g : 'Hom{T,T'}) : 
  tf2f y z g \is bound1lf = (g \is bound1lf).
Proof.
apply/eqb_iff; split; rewrite tf2f_UE=>P.
  rewrite -[g](tf2fK (x1 := y) (x2 := z)) f2tf_UE tf2f_UE.
all: apply/bound1lf_comp; last (by apply/is_bound1lf);
  apply/bound1lf_comp=>[|//]; by apply/is_bound1lf.
Qed.

Lemma tf2f_isoP (T' : qType) (z : 'QReg[T']) (g : 'Hom{T,T'}) :
  g \is isolf -> tf2f x z g \is isolf.
Proof.
rewrite tf2f_UE=>P; apply/isolf_comp; last apply/is_isolf.
apply/isolf_comp=>[|//]; apply/is_isolf.
Qed.

Lemma tf2f_isoE (T' : qType) (z : 'QReg[T']) (g : 'Hom{T,T'}) :
  tf2f y z g \is isolf = (g \is isolf).
Proof.
apply/eqb_iff; split; rewrite tf2f_UE=>P.
  rewrite -[g](tf2fK (x1 := y) (x2 := z)) f2tf_UE tf2f_UE.
all: apply/isolf_comp; last (by apply/is_isolf);
  apply/isolf_comp=>[|//]; by apply/is_isolf.
Qed.

Lemma tf2f_gisoE (T' : qType) (z : 'QReg[T']) (g : 'Hom{T,T'}) :
  tf2f y z g \is gisolf = (g \is gisolf).
Proof.
apply/eqb_iff; split; rewrite tf2f_UE=>P.
  rewrite -[g](tf2fK (x1 := y) (x2 := z)) f2tf_UE tf2f_UE.
all: apply/gisolf_comp; last (by apply/is_gisolf);
  apply/gisolf_comp=>[|//]; by apply/is_gisolf.
Qed.

Lemma tf2f_unitaryE f : tf2f y y f \is unitarylf = (f \is unitarylf).
Proof. exact: tf2f_isoE. Qed.

Lemma tf2f_hermP f : f \is hermlf -> tf2f x x f \is hermlf.
Proof. by rewrite !hermlfE tf2f_adj=>/eqP->. Qed.
Lemma tf2f_hermE f : tf2f y y f \is hermlf = (f \is hermlf).
Proof. by rewrite !hermlfE tf2f_adj (inj_eq tf2f_inj). Qed.

Lemma tf2f_psdP f : f \is psdlf -> tf2f x x f \is psdlf.
Proof. rewrite !psdlfE tf2f_UE; apply: gef0_formf. Qed.
Lemma tf2f_psdE f : tf2f y y f \is psdlf = (f \is psdlf).
Proof.
apply/eqb_iff; split=>/psdlfP P; apply/psdlfP=>u.
by move: (P (tv2v y u)); rewrite tf2f_apply tv2v_dot.
by rewrite -(v2tvK u) tf2f_apply tv2v_dot.
Qed.

Lemma tf2f_denP f : f \is denlf -> tf2f x x f \is denlf.
Proof.
move=>/denlfP[] Pf1 Pf2; apply/denlfP; split.
by apply/tf2f_psdP.
rewrite -psd_trfnorm; first by apply/tf2f_psdP.
rewrite tf2f_UE. apply: (le_trans (trfnormMl _ _)).
rewrite i2fnorm_iso ?v2tU_isolf// mulr1.
apply: (le_trans (trfnormMr _ _)).
by rewrite i2fnorm_adj i2fnorm_iso ?v2tU_isolf// mul1r psd_trfnorm.
Qed.
Lemma tf2f_denE f : tf2f y y f \is denlf = (f \is denlf).
Proof.
apply/eqb_iff; split=>/denlfP P; apply/denlfP; move: P;
by rewrite tf2f_psdE tf2f_trlf.
Qed.

Lemma tf2f_obsP f : f \is obslf -> tf2f x x f \is obslf.
Proof.
move=>/obslfP[] Pf1 Pf2; apply/obslfP; split.
by apply/tf2f_psdP.
move=>u; rewrite tf2f_apply_v2tv tv2v_dotr.
by apply: (le_trans (Pf2 _)); rewrite v2tv_dot.
Qed.
Lemma tf2f_obsE f : tf2f y y f \is obslf = (f \is obslf).
Proof.
apply/eqb_iff; split=>/obslfP P; apply/obslfP; move: P;
rewrite tf2f_psdE=>[[P1 P2]]; split=>[//|u].
by move: (P2 (tv2v y u)); rewrite tf2f_apply !tv2v_dot.
by rewrite -(v2tvK u); rewrite tf2f_apply !tv2v_dot.
Qed.

Lemma tf2f_den1E f : tf2f y y f \is den1lf = (f \is den1lf).
Proof.
apply/eqb_iff; split=>/den1lfP P; apply/den1lfP; move: P;
by rewrite tf2f_psdE tf2f_trlf.
Qed.
Lemma tf2f_projE f : tf2f y y f \is projlf = (f \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP P; apply/projlfP; move: P;
rewrite tf2f_adj tf2f_comp; last by move=>[]->->.
by move=>[]/tf2f_inj->/tf2f_inj->.
Qed.
Lemma tf2f_proj1E f : tf2f y y f \is proj1lf = (f \is proj1lf).
Proof.
apply/eqb_iff; split=>/proj1lfP P; apply/proj1lfP; move: P;
by rewrite tf2f_projE tf2f_trlf.
Qed.

Lemma tf2f_lefP f1 f2 : f1 ⊑ f2 -> tf2f x x f1 ⊑ tf2f x x f2.
Proof. by rewrite -subv_ge0 -psdlfE -subv_ge0 -linearB -psdlfE=>/tf2f_psdP. Qed.
Lemma tf2f_le1P f : f ⊑ \1 -> tf2f x x f ⊑ \1.
Proof. by move=>/tf2f_lefP; rewrite tf2f1. Qed.
Lemma tf2f_ge0P f : 0%:VF ⊑ f -> 0%:VF ⊑ tf2f x x f.
Proof. by move=>/tf2f_lefP; rewrite tf2f0. Qed.

Lemma tf2f_lef f1 f2 : tf2f y y f1 ⊑ tf2f y y f2 = (f1 ⊑ f2).
Proof. by rewrite -subv_ge0 -linearB -psdlfE -subv_ge0 -psdlfE tf2f_psdE. Qed.
Lemma tf2f_ltf f1 f2 : tf2f y y f1 ⊏ tf2f y y f2 = (f1 ⊏ f2).
Proof. by rewrite !lt_def tf2f_lef (inj_eq tf2f_inj). Qed.
Lemma tf2f_le1 f : tf2f y y f ⊑ \1 = (f ⊑ \1).
Proof. by rewrite -tf2f1 tf2f_lef. Qed.
Lemma tf2f_lt1 f : tf2f y y f ⊏ \1 = (f ⊏ \1).
Proof. by rewrite -tf2f1 tf2f_ltf. Qed.
Lemma tf2f_ge0 f : 0%:VF ⊑ tf2f y y f = (0%:VF ⊑ f).
Proof. by rewrite -tf2f0 tf2f_lef. Qed.
Lemma tf2f_gt0 f : 0%:VF ⊏ tf2f y y f = (0%:VF ⊏ f).
Proof. by rewrite -tf2f0 tf2f_ltf. Qed.

End EndProp.

Section EndCanonical.
Variable (T : qType).
Implicit Type (x : qreg T) (y : 'QReg[T]).

Lemma tf2f_bound1 T' x (z : qreg T') (g : 'FB1('Ht T, 'Ht T')) : 
  tf2f x z g \is bound1lf.
Proof. by apply/tf2f_bound1P/is_bound1lf. Qed.
HB.instance Definition _ T' x z (g : 'FB1('Ht T, 'Ht T')) := 
  isBound1Lf.Build _ _ (tf2f x z g) (@tf2f_bound1 T' x z g).

Lemma tf2f_iso T' x (z : 'QReg[T']) (g : 'FI('Ht T, 'Ht T')) : 
  tf2f x z g \is isolf.
Proof. by apply/tf2f_isoP/is_isolf. Qed.
HB.instance Definition _ T' x (z : 'QReg[T']) (g : 'FI('Ht T, 'Ht T')) :=
  Bound1_isIsoLf.Build _ _ (tf2f x z g) (@tf2f_iso T' x z g).

Lemma tf2f_giso T' y (z : 'QReg[T']) (g : 'FGI('Ht T, 'Ht T')) : 
  tf2f y z g \is gisolf.
Proof. by rewrite tf2f_gisoE is_gisolf. Qed.
HB.instance Definition _ T' y (z : 'QReg[T']) (g : 'FGI('Ht T, 'Ht T')) :=
  Iso_isGisoLf.Build _ _ (tf2f y z g) (@tf2f_giso T' y z g).

(* Lemma tf2f_unitary y (g : 'FU(_)) : tf2f y y g \is unitarylf.
Proof. by rewrite tf2f_unitaryE is_unitarylf. Qed.
HB.instance Definition _ y (g : 'FU(_)) := 
  isUnitaryLf.Build _ (tf2f y y g) (@tf2f_unitary y g). *)

Lemma tf2f_herm x (g : 'FH(_)) : tf2f x x g \is hermlf.
Proof. by rewrite tf2f_hermP// is_hermlf. Qed.
HB.instance Definition _ x (g : 'FH(_)) := 
  isHermLf.Build _ (tf2f x x g) (@tf2f_herm x g).
Lemma tf2f_psd x (g : 'F+(_)) : tf2f x x g \is psdlf.
Proof. by rewrite tf2f_psdP// is_psdlf. Qed.
HB.instance Definition _ x (g : 'F+(_)) := 
  Herm_isPsdLf.Build _ (tf2f x x g) (@tf2f_psd x g).
Lemma tf2f_obs x (g : 'FO(_)) : tf2f x x g \is obslf.
Proof. by rewrite tf2f_obsP// is_obslf. Qed.
HB.instance Definition _ x (g : 'FO(_)) := 
  Psd_isObsLf.Build _ (tf2f x x g) (@tf2f_obs x g).
Lemma tf2f_den x (g : 'FD(_)) : tf2f x x g \is denlf.
Proof. by rewrite tf2f_denP// is_denlf. Qed.
HB.instance Definition _ x (g : 'FD(_)) := 
  Obs_isDenLf.Build _ (tf2f x x g) (@tf2f_den x g).
Lemma tf2f_den1 y (g : 'FD1(_)) : tf2f y y g \is den1lf.
Proof. by rewrite tf2f_den1E is_den1lf. Qed.
HB.instance Definition _ y (g : 'FD1(_)) := 
  Den_isDen1Lf.Build _ (tf2f y y g) (@tf2f_den1 y g).
Lemma tf2f_proj y (g : 'FP(_)) : tf2f y y g \is projlf.
Proof. by rewrite tf2f_projE is_projlf. Qed.
HB.instance Definition _ y (g : 'FP(_)) := 
  Obs_isProjLf.Build _ (tf2f y y g) (@tf2f_proj y g).
(* missing join *)
HB.instance Definition _ y (g : 'FP1(_)) := Proj1Lf.Class
  (ProjLf.on (tf2f y y g)) (Den1Lf.on (tf2f y y g)).

End EndCanonical.

Section tm2mProp.
Variable (T1 T2 : qType).
Implicit Type (xa : qreg T1) (xb : qreg T2).
Implicit Type (ya : 'QReg[T1]) (yb : 'QReg[T2]).

Lemma tf2f_lef_form xa xb g :
  tf2f xb xa g \o tf2f xa xb g^A ⊑ tf2f xa xa (g \o g^A).
Proof.
rewrite !tf2f_UE comp_lfunA -[X in X \o v2tU xa]comp_lfunA -[_ \o g \o _]comp_lfunA.
apply/lef_form/lef_dot=>u; rewrite !lfunE/= -adj_dotEl !lfunE/= -adj_dotEl.
by rewrite lfunE/= -[X in _ <= X]adj_dotEl isofA_dot.
Qed.
Lemma tf2f_lef_formV xa xb g :
  tf2f xb xa g^A \o tf2f xa xb g ⊑ tf2f xa xa (g^A \o g).
Proof. by rewrite -{2 4}[g]adjfK; apply tf2f_lef_form. Qed.

Lemma tm2m_tn xa xb (F : finType) (g : 'TN(F;'Ht T1, 'Ht T2)) : 
  trace_nincr (tm2m xa xb g).
Proof.
rewrite /trace_nincr /tm2m.
move: (@is_trnincr _ _ _ g); rewrite /trace_nincr=>/(tf2f_lefP xa).
rewrite tf2f1; apply le_trans.
rewrite linear_sum. apply lev_sum=>i _.
rewrite tf2f_adj. apply tf2f_lef_formV.
Qed.
HB.instance Definition _ xa xb (F : finType) (g : 'TN(F;'Ht T1, 'Ht T2)) :=
  isTraceNincr.Build _ _ F (tm2m xa xb g) (@tm2m_tn xa xb F g).
Lemma tm2m_tp ya yb (F : finType) (g : 'QM(F;'Ht T1, 'Ht T2)) : 
  trace_presv (tm2m ya yb g).
Proof.
rewrite /trace_presv /tm2m.
under eq_bigr do rewrite tf2f_adj tf2f_comp.
by rewrite -linear_sum/= qmeasure_tpE tf2f1.
Qed.
HB.instance Definition _ ya yb (F : finType) (g : 'QM(F;'Ht T1, 'Ht T2)) :=
  TraceNincr_isQMeasure.Build _ _ F (tm2m ya yb g) (@tm2m_tp ya yb F g).

Lemma tm2mE xa xb (F : finType) (g : F -> 'Hom{T1,T2}) i : 
  tm2m xa xb g i = tf2f xa xb (g i).
Proof. by []. Qed.

End tm2mProp.

End QMemoryTheory.

HB.lock
Definition th2h (m : qmemType) T (x : 'QReg[T]) (P : {hspace 'Ht T}) :=
  HSType (tf2f m x x P).

HB.lock
Definition liftfh (m : qmemType) T (x : 'QReg[T]) (P : {hspace 'Ht T}) := 
  HSType (liftf_lf (th2h m x P)).

Section th2h_theory.
Local Open Scope order_scope.
Local Open Scope hspace_scope.
Import ComplLatticeSyntax.
Variable (QMem : qmemType).
Local Notation L := (mem_lab QMem).
Local Notation H := (@mem_sys QMem).
Local Notation mset := (mem_set QMem).
Local Notation tv2v := (tv2v QMem).
Local Notation tf2f := (tf2f QMem).
Local Notation v2tv := (@v2tv QMem _).
Local Notation f2tf := (@f2tf QMem _ _).
Local Notation tm2m := (tm2m QMem).
Local Notation v2tU := (@v2tU QMem).
Local Notation th2h := (@th2h QMem _).
Local Notation liftfh := (@liftfh QMem _).

Variable (T : qType) (x : 'QReg[T]).
Implicit Type (P : {hspace 'Ht T}).

Lemma th2hE P : th2h x P = tf2f x x P :> 'End(_).
Proof. by rewrite th2h.unlock hsE. Qed.
Lemma th2h_def P : th2h x P = formh (v2tU x)^A P.
Proof. by apply/hspacelfP; rewrite th2hE formhE tf2f_UE formlf.unlock adjfK. Qed.
(* about th2h, liftfh *)
Lemma th2h1 : th2h x `1` = `1`.
Proof. by rewrite th2h_def formh1. Qed.
Lemma th2h0 : th2h x `0` = `0`.
Proof. by rewrite th2h_def formh0. Qed.
Lemma th2hO P : th2h x (~` P) = ~` (th2h x P).
Proof. by rewrite !th2h_def formhO. Qed.
Lemma th2hU P1 P2 :
  th2h x (P1 `|` P2) = th2h x P1 `|` th2h x P2.
Proof. by rewrite !th2h_def formhU. Qed.
Lemma th2hI P1 P2 :
  th2h x (P1 `&` P2) = th2h x P1 `&` th2h x P2.
Proof. by rewrite !th2h_def formhI. Qed.
Lemma th2hJ P1 P2 :
  th2h x (P1 `&&` P2) = (th2h x P1 `&&` th2h x P2).
Proof. by rewrite !th2h_def formhJ. Qed.
Lemma th2hH P1 P2 :
  th2h x (P1 `=>` P2) = (th2h x P1 `=>` th2h x P2).
Proof. by rewrite !th2h_def formhH. Qed.

Lemma liftfhE P : liftfh x P = liftf_lf (th2h x P) :> 'End(_).
Proof. by rewrite liftfh.unlock hsE. Qed.  

Lemma liftf_lf_supp S (f : 'F[H]_S) :
  liftf_lf (supplf f) = supplf (liftf_lf f).
Proof.
have P (g : 'F[H]_S): HSType (liftf_lf (kerh g)) = kerh (liftf_lf g).
  apply/eqP/hseqP=>u;
  rewrite memh_kerE memhOE !hsE/= !hsE/= !hsE/= !hsE/=;
  rewrite liftf_lf_cplmt cplmtK; apply/eqb_iff; split=>/eqP P.
  by rewrite -[g]suppvlf liftf_lf_comp lfunE/= P linear0.
  by rewrite /supplf liftf_lf_comp lfunE/= P linear0.
move: (P f)=>/(f_equal ocompl)/hspacelfP.
do ? rewrite ![in X in X = _ -> _]hsE/=.
do ? rewrite ![in X in _ = X -> _]hsE/=.
by rewrite liftf_lf_cplmt !cplmtK.
Qed.

Lemma liftfh1 : liftfh x `1` = `1`.
Proof. by apply/hspacelfP; rewrite liftfhE th2h1 !hsE liftf_lf1. Qed.
Lemma liftfh0 : liftfh x `0` = `0`.
Proof. by apply/hspacelfP; rewrite liftfhE th2h0 !hsE linear0. Qed.
Lemma liftfhO P : liftfh x (~` P) = ~` (liftfh x P).
Proof. by apply/hspacelfP; rewrite liftfhE th2hO !hsE/= liftfhE liftf_lf_cplmt. Qed.
Lemma liftfhU P1 P2 :
  liftfh x (P1 `|` P2) = liftfh x P1 `|` liftfh x P2.
Proof.
by apply/hspacelfP; rewrite liftfhE th2hU !hsE/= liftf_lf_supp linearD/= !liftfhE.
Qed.
Lemma liftfhI P1 P2 :
  liftfh x (P1 `&` P2) = liftfh x P1 `&` liftfh x P2.
Proof. by apply/ocompl_inj; rewrite -liftfhO !ocomplI liftfhU !liftfhO. Qed.
Lemma liftfhJ P1 P2 :
  liftfh x (P1 `&&` P2) = (liftfh x P1 `&&` liftfh x P2).
Proof. by rewrite /sasaki_projection liftfhI liftfhU liftfhO. Qed.
Lemma liftfhH P1 P2 :
  liftfh x (P1 `=>` P2) = (liftfh x P1 `=>` liftfh x P2).
Proof. by rewrite /sasaki_hook liftfhU liftfhI liftfhO. Qed.


Lemma liftfh_formh (U : 'FU('Ht T)) P :
  liftfh x (formh U P) = formh (liftf_lf (tf2f x x U)) (liftfh x P).
Proof.
apply/hspacelfP; rewrite liftfhE th2hE !formhE liftfhE th2hE formlf.unlock.
by rewrite -liftf_lf_adj/= tf2f_adj -!liftf_lf_comp !tf2f_comp.
Qed.

Lemma th2h_inj : injective (th2h x).
Proof. by move=>u v /hspacelfP; rewrite !th2hE=>/tf2f_inj/hspacelfP. Qed.

Lemma liftfh_inj : injective (liftfh x).
Proof. by move=>u v /hspacelfP; rewrite !liftfhE=>/liftf_lf_inj/hspacelfP/th2h_inj. Qed.

Lemma liftfh_le P1 P2 : 
  (P1 `<=` P2) = (liftfh x P1 `<=` liftfh x P2).
Proof. by rewrite !leEmeet -liftfhI (inj_eq liftfh_inj). Qed.

End th2h_theory.

Module DefaultQMem.

Section Theory.

Definition mlab : finType := basic_index.

Definition ty_bi (i : basic_index) : qType :=
  match qtype_of_index 
    (prime_index (basic_index_to_pair i).1 (basic_index_to_pair i).2) with
  | Some QUnit => QUnit
  | Some QBool => QBool
  | Some (QOrd n) => QOrd n
  | Some (QOption T) => QOption T
  | Some (QSum T1 T2) => QSum T1 T2
  | _ => QUnit
  end.

Definition msys := (fun i => 'Ht (ty_bi i)).

Inductive cnf :=
  | cnf_basic (i : basic_index)
  | cnf_pair (i1 i2 : cnf)
  | cnf_tuple (n : nat) of qType & 'I_n -> cnf
  | cnf_ffun (n : nat) of 'I_n -> qType & 'I_n -> cnf.

Definition cnf0 := cnf_tuple QUnit (ffun0 (card_ord 0) : 'I_0 -> cnf).

Fixpoint cnf_prime (T : qType) (v : qvar) (s : seq qnat) :=
  if qtype_of_index (prime_index v s) == Some T then 
    match T with
    | QUnit | QBool | (QOrd _) | (QOption _) | (QSum _ _) =>
        orapp cnf0 (fun T : is_basic_index v s = true => cnf_basic (Basic_Index T))
        (* match is_basic_index v s =P true with
        | ReflectT T => cnf_basic (Basic_Index T)
        | _ => cnf0
        end *)
    | QPair T1 T2 => cnf_pair (cnf_prime T1 v (rcons s qnat_fst)) 
                              (cnf_prime T2 v (rcons s qnat_snd))
    | QArray n T => cnf_tuple T 
        (fun i : 'I_n => (cnf_prime T v (rcons s (qnat_tuplei i))))
    | QDFFun n fT => cnf_ffun fT 
        (fun i : 'I_n => (cnf_prime (fT i) v (rcons s (qnat_ffuni i))))
    end
  else cnf0.

Fixpoint ty_cnf (i : cnf) :=
  match i with
  | cnf_basic i => ty_bi i
  | cnf_pair i1 i2 => QPair (ty_cnf i1) (ty_cnf i2)
  | cnf_tuple n T fi => QArray n T
  | cnf_ffun n fT fi => QDFFun fT
  end.

Fixpoint set_cnf (i : cnf) : {set mlab} :=
  match i with
  | cnf_basic i => [set i]
  | cnf_pair i1 i2 => set_cnf i1 :|: set_cnf i2
  | cnf_tuple n _ fi => \bigcup_(i < n) set_cnf (fi i)
  | cnf_ffun n _ fi => \bigcup_(i < n) set_cnf (fi i)
  end.

Fixpoint cnf_qi (i : qreg_index) :=
  match i with
  | fault_index => cnf0
  | prime_index v s => 
      oapp (fun T => cnf_prime T v s) cnf0 (qtype_of_index (prime_index v s))
  | pair_index i1 i2 => cnf_pair (cnf_qi i1) (cnf_qi i2)
  | tuple_index n T fi => cnf_tuple T (fun i => cnf_qi (fi i))
  | ffun_index n fT fi => cnf_ffun fT (fun i => cnf_qi (fi i))
  end.

Definition mset T (x : qreg T) := set_cnf (cnf_qi (index_of_qreg x)).

Lemma optionP (T : Type) (x : option T) : 
  (exists t, x = Some t) \/ x = None.
Proof. by case: x=>[t|]; [left; exists t | right]. Qed. 

Ltac ltest := try do [by move=>???/=; case: [forall _, _] |
by move=>??/=; do 2 case: (qtype_of_index _)=>//].

Lemma cnf_qi_pair (T1 T2 : qType) (x : qreg_index) :
  qtype_of_index x = Some (QPair T1 T2) ->
    cnf_qi x = cnf_qi (pair_index (index_fst x) (index_snd x)).
Proof.
move=>P; move: P (qtype_of_pair P) => + [].
by case: x=>// x s /= P1 -> -> /=; rewrite P1/= P1 eqxx.
Qed.

Lemma cnf_qi_tuple n (T : qType) (x : qreg_index) :
  qtype_of_index x = Some (QArray n T) ->
    cnf_qi x = cnf_qi (tuple_index T (fun i : 'I_n => index_tuplei x i)).
Proof.
move=>P; move: P (qtype_of_tuple P); case: x=>//; ltest.
- by move=>x s /= P1 P2; rewrite P1/= P1 eqxx; 
    under [in RHS]eq_fun do rewrite P2.
- move=>m T' q/=; case: [forall _, _] =>// /esym Pv; move: q; inversion Pv.
  by move=>? _;  under [in RHS]eq_fun do rewrite tuple_indexE.
Qed.

Lemma cnf_qi_ffun n (T : 'I_n -> qType) (x : qreg_index) :
  qtype_of_index x = Some (QDFFun T) ->
    cnf_qi x = cnf_qi (ffun_index T (fun i : 'I_n => index_ffuni x i)).
Proof.
move=>P; move: P (qtype_of_ffun P); case: x=>//; ltest.
- by move=>x s /= P1 P2; rewrite P1/= P1 eqxx; 
    under [in RHS]eq_fun do rewrite P2.
- move=>m T' q/=; case: [forall _, _] =>// /esym Pv; move: q; inversion Pv.
  by move=>? _;  under [in RHS]eq_fun do rewrite ffun_indexE.
Qed.

Lemma eq_cnf T (x y : qreg_index) : 
  qtype_of_index x = Some T -> qtype_of_index y = Some T -> 
    qi2seq x = qi2seq y -> cnf_qi x = cnf_qi y.
Proof.
elim: T x y=>[||?|??||????||].
1-4,6: move=>x y; case: x=>//; ltest=>x sx/= Px; case: y=>//; ltest=>y sy/= Py;
  rewrite /qi2seq/= Px Py/= Px Py eqxx /pair_to_basic_index !orappE/=;
  [|rewrite/is_basic_index/= ?Px ?Py// ..];
  by move=>+ + Py1 Px1 Pv; inversion Pv=>Py2 Py3; rewrite (eq_irrelevance Py2 Py3).
- move=>T1 IH1 T2 IH2 x y Px Py.
  move: (qtype_of_pair Px) (qtype_of_pair Py)=>[Px1 Px2] [Py1 Py2].
  move: (qi2seq_of_pair Px) (qi2seq_of_pair Py)=>->-> Ps.
  move: (cnf_qi_pair Px) (cnf_qi_pair Py)=>->->/=.
  move: (f_equal (take (qtype_size T1)) Ps) (f_equal (drop (qtype_size T1)) Ps).
  rewrite !take_size_cat ?drop_size_cat ?(size_qi2seq Px1)// ?(size_qi2seq Py1)//.
  by move=>/(IH1 _ _ Px1 Py1)->/(IH2 _ _ Px2 Py2)->.
- move=>n T IH x y Px Py.
  move: (qtype_of_tuple Px) (qtype_of_tuple Py)=>Px1 Py1.
  move: (qi2seq_of_tuple Px) (qi2seq_of_tuple Py)=>->-> Ps.
  move: (cnf_qi_tuple Px) (cnf_qi_tuple Py)=>->->/=; f_equal; apply/funext=>i/=.
  apply: (IH _ _ (Px1 i) (Py1 i)).
  have: shape [seq qi2seq (index_tuplei x i) | i : 'I_n] 
    = shape [seq qi2seq (index_tuplei y i) | i : 'I_n].
    rewrite /shape -map_comp - [RHS]map_comp.
    under eq_map do rewrite/= (size_qi2seq (Px1 _)).
    by under [RHS]eq_map do rewrite/= (size_qi2seq (Py1 _)).
  move=>/(eq_from_flatten_shape Ps)/(f_equal (nth [::] ^~ i)).
  by rewrite (nth_map i) ?size_enum_ord// nth_ord_enum (nth_map i) ?size_enum_ord// nth_ord_enum.
- move=>n T IH x y Px Py.
  move: (qtype_of_ffun Px) (qtype_of_ffun Py)=>Px1 Py1.
  move: (qi2seq_of_ffun Px) (qi2seq_of_ffun Py)=>->-> Ps.
  move: (cnf_qi_ffun Px) (cnf_qi_ffun Py)=>->->/=; f_equal; apply/funext=>i/=.
  apply: (IH i _ _ (Px1 i) (Py1 i)).
  have: shape [seq qi2seq (index_ffuni x i) | i : 'I_n] 
    = shape [seq qi2seq (index_ffuni y i) | i : 'I_n].
    rewrite /shape -map_comp - [RHS]map_comp.
    under eq_map do rewrite/= (size_qi2seq (Px1 _)).
    by under [RHS]eq_map do rewrite/= (size_qi2seq (Py1 _)).
  move=>/(eq_from_flatten_shape Ps)/(f_equal (nth [::] ^~ i)).
  by rewrite (nth_map i) ?size_enum_ord// nth_ord_enum (nth_map i) ?size_enum_ord// nth_ord_enum.
Qed.

Lemma set_qiE (x : qreg_index) : set_cnf (cnf_qi x) =i qi2seq x.
Proof.
elim: x; first by move=>/= x; rewrite big_ord0 /qi2seq/= !inE.
- move=>x s; move: (optionP (qtype_of_index (prime_index x s)))=>[[T/= Ps]|/=];
  last by rewrite /qi2seq/==>-> i; rewrite/= big_ord0 !inE.
  rewrite Ps /qi2seq/= Ps; elim: T s Ps =>[||n|T _||T1 _ T2 _||].
  1-4,6: move=>s PT; rewrite/= PT eqxx /pair_to_basic_index/=; 
    (have P1: is_basic_index x s by rewrite/is_basic_index/= PT);
    by rewrite !orappE=> i; rewrite !inE.
  - move=>T1 IH1 T2 IH2 s PT/= i; rewrite PT eqxx/= map_cat pmap_cat inE mem_cat.
    by rewrite IH1 ?IH2// qtype_of_index_rec_rcons PT.
  - move=>n T IH s PT/= i; rewrite PT eqxx/= map_flatten pmap_flatten -2!map_comp.
    apply/eqb_iff; split=>[ /bigcupP [] k _ | /flatten_imageP [] k _ ].
    rewrite IH=>[|Pk]; last by apply/flatten_imageP; exists k.
    2: rewrite -IH=>[|Pk]; last by apply/bigcupP; exists k.
    1,2: by rewrite qtype_of_index_rec_rcons PT orapp_id.
  - move=>n T IH s PT/= i; rewrite PT eqxx/= map_flatten pmap_flatten -2!map_comp.
    apply/eqb_iff; split=>[ /bigcupP [] k _ | /flatten_imageP [] k _ ].
    rewrite IH=>[|Pk]; last by apply/flatten_imageP; exists k.
    2: rewrite -IH=>[|Pk]; last by apply/bigcupP; exists k.
    1,2: by rewrite qtype_of_index_rec_rcons PT orapp_id cast_ord_id.
- by move=>q1 IH1 q2 IH2/= i; rewrite inE/= /qi2seq/= -/qi2seq mem_cat IH1 IH2.
- move=>n T q IH i; rewrite/= /qi2seq/= -/qi2seq.
  apply/eqb_iff; split=>[ /bigcupP [] k _ | /flatten_imageP [] k _ ].
  by rewrite IH=>Pk; apply/flatten_imageP; exists k.
  by rewrite -IH=>Pk; apply/bigcupP; exists k.  
- move=>n T q IH i; rewrite/= /qi2seq/= -/qi2seq.
  apply/eqb_iff; split=>[ /bigcupP [] k _ | /flatten_imageP [] k _ ].
  by rewrite IH=>Pk; apply/flatten_imageP; exists k.
  by rewrite -IH=>Pk; apply/bigcupP; exists k.
Qed.

Lemma disj_cnfE (x1 x2 : qreg_index) :
  [disjoint qi2seq x1 & qi2seq x2] = 
    [disjoint set_cnf (cnf_qi x1) & set_cnf (cnf_qi x2)].
Proof.
move: (set_qiE x1)=>/eq_disjoint/(_ (mem (set_cnf (cnf_qi x2))))->.
apply: eq_disjoint_r=>i; symmetry ; apply set_qiE.
Qed.

Lemma disj_setE T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  (disjoint_qreg x1 x2) = [disjoint mset x1 & mset x2].
Proof. exact: disj_cnfE. Qed.

Lemma eq_setP T (x1 x2 : qreg T) :
  x1 =r x2 -> mset x1 = mset x2.
Proof.
rewrite /eq_qreg /qr2seq =>P; apply/setP=>i;
by rewrite /mset !set_qiE P.
Qed.

Lemma ty_cnfK T x : qtype_of_index x = Some T ->
  ty_cnf (cnf_qi x) = T.
Proof.
elim: x T=>//.
- move=>x s T/= Ps; rewrite Ps.
  elim: T s Ps=>[||?|? _|? IH1 ? IH2|? _ ? _|???|???] s /= PT.
  1-4,6-8:  rewrite/= PT eqxx//= /pair_to_basic_index/=;
    (have P1: is_basic_index x s by rewrite/is_basic_index/= PT);
    by rewrite orappE/=/ty_bi/= PT.
  by rewrite PT eqxx/= IH1 ?IH2// qtype_of_index_rec_rcons PT.
- move=>q1 IH1 q2 IH2/= T.
  case E1: (qtype_of_index q1)=>[T1|]//; case E2: (qtype_of_index q2)=>[T2|]// Pv.
  by inversion Pv; rewrite (IH1 _ E1) (IH2 _ E2) .
all: by move=>n T fi IH T' /=; case E: [forall _, _] =>// Pv; inversion Pv.
Qed.

Lemma ty_qregK T (x : qreg T) :
  ty_cnf (cnf_qi (index_of_qreg x)) = T.
Proof. by move: (index_typeK x)=>/ty_cnfK. Qed.

Lemma dim_biE (i : basic_index) (b := cnf_basic i) : 
  #|evalQT (  ty_cnf b )| = #|'Idx[msys]_(set_cnf b)|.
Proof.
by rewrite card_idx/= big_set1/msys -ihb_dim_cast.
Qed.

Definition idx_bi (i : basic_index) (b := cnf_basic i) 
  (t : evalQT (  ty_cnf b ))
  : option 'Idx[msys]_(set_cnf b) :=
    Some (enum_val (cast_ord (dim_biE i) (enum_rank t))).

Definition idx_pair (i1 i2 : cnf) (b := cnf_pair i1 i2) 
  (f1 : evalQT (ty_cnf i1) -> option 'Idx[msys]_(set_cnf i1) )
  (f2 : evalQT (ty_cnf i2) -> option 'Idx[msys]_(set_cnf i2) )
  (t :  evalQT (ty_cnf b)) : option 'Idx[msys]_(set_cnf b) :=
  match f1 t.1, f2 t.2 with
  | Some i1, Some i2 => if (idxSl (idxU i1 i2) == i1) && (idxSr (idxU i1 i2) == i2) then 
                        Some (idxU i1 i2)
                        else None
  | _, _ => None
  end.
  
Definition idx_tuple n (T : qType) (fi : 'I_n -> cnf) (b := cnf_tuple T fi)
  (f : forall i, evalQT (ty_cnf (fi i)) -> option 'Idx[msys]_(set_cnf (fi i)))
  (t : evalQT (ty_cnf b)) : option 'Idx[msys]_(set_cnf b) :=
  if [forall i, orapp false (fun P : T = ty_cnf (fi i) =>
                match f i (cast_qtype P (t ~_ i)) with
                | Some i => true
                | None => false
                end)]
  then let fi : {dffun forall (i : 'I_n), 'Idx[msys]_(set_cnf (fi i))} := 
            [ffun i : 'I_n => orapp idx_default (fun P : T = ty_cnf (fi i) =>
              odflt idx_default (f i (cast_qtype P (t ~_ i))))] in
      if [forall i, flatidx (packidx fi) i == fi i] then
        Some (packidx fi)
      else None
  else None.

Definition idx_ffun n (T : 'I_n -> qType) (fi : 'I_n -> cnf) (b := cnf_ffun T fi)
  (f : forall i, evalQT (ty_cnf (fi i)) -> option 'Idx[msys]_(set_cnf (fi i)))
  (t : evalQT (ty_cnf b)) : option 'Idx[msys]_(set_cnf b) :=
  if [forall i, orapp false (fun P : T i = ty_cnf (fi i) =>
                match f i (cast_qtype P (t i)) with
                | Some i => true
                | None => false
                end)] 
  then let fi : {dffun forall (i : 'I_n), 'Idx[msys]_(set_cnf (fi i))} := 
            [ffun i : 'I_n => orapp idx_default (fun P : T i = ty_cnf (fi i) =>
              odflt idx_default (f i (cast_qtype P (t i))))] in
      if [forall i, flatidx (packidx fi) i == fi i] then
        Some (packidx fi)
      else None
  else None.

Fixpoint idx_proj (i : cnf) : evalQT (ty_cnf i) -> option 'Idx[msys]_(set_cnf i) :=
  match i with
  | cnf_basic j => @idx_bi j
  | cnf_pair i1 i2 => idx_pair (@idx_proj i1) (@idx_proj i2)
  | cnf_tuple n T fi => @idx_tuple n T fi (fun i => @idx_proj (fi i))
  | cnf_ffun n T fi => @idx_ffun n T fi (fun i => @idx_proj (fi i))
  end.

Lemma idx_projK T x : 
  qtype_of_index x = Some T ->
    uniq (qi2seq x) ->
  {g : ('Idx_(set_cnf (cnf_qi x)) -> evalQT (ty_cnf (cnf_qi x))) * _ | 
      cancel g.1 g.2 /\ cancel g.2 g.1 & 
      forall i, (idx_proj (i:=cnf_qi x) i = Some (g.2 i))}.
Proof.
elim: T x=>[||?|? _||? _ ? _||].
1-4,6: case=>// [x s /= PT _ |||]/=; ltest; rewrite PT/= PT eqxx;
  (have P1: is_basic_index x s by rewrite /is_basic_index/= PT);
  rewrite orappE/= /idx_bi;
  pose g2 (i : evalQT (ty_bi (Basic_Index P1))) : 'Idx_[set Basic_Index P1] 
    := (enum_val (cast_ord (dim_biE (Basic_Index P1)) (enum_rank i)));
  pose g1 (i : 'Idx_[set Basic_Index P1]) : evalQT (ty_bi (Basic_Index P1)) :=
    (enum_val (cast_ord (esym (dim_biE (Basic_Index P1))) (enum_rank i)));
  by exists (g1,g2)=>/=; split=>i; 
    rewrite /g1/g2 enum_valK cast_ord_comp cast_ord_id enum_rankK.
- move=>T1 IH1 T2 IH2 x PT; move: (qi2seq_of_pair PT)=>->.
  rewrite cat_uniq_disjoint=>/and3P[]P1 + P2; rewrite disj_cnfE=>dis.
  move: (cnf_qi_pair PT) (qtype_of_pair PT)=>->/=[]PT1 PT2.
  move: (IH1 _ PT1 P1)=>[][] g1 f1 /= [] g1K f1K H1.
  move: (IH2 _ PT2 P2)=>[][] g2 f2 /= [] g2K f2K H2.
  pose g i := (g1 (idxSl i), g2 (idxSr i)).
  pose f i := idxU (f1 i.1) (f2 i.2).
  exists (g, f)=>/=; first split=>i; rewrite /f /g/=.
  - by rewrite g1K g2K idxUS.
  - by rewrite idxSUl// idxSUr// f1K f2K -surjective_pairing.
  by move=>[] i1 i2; rewrite/idx_pair/= H1 H2 idxSUl// idxSUr// !eqxx/=.
- move=>n T IH x PT; move: (qi2seq_of_tuple PT)=>->.
  rewrite flatten_uniq_disjoint=>/andP[]/forallP PUi dis0.
  have dis : disf (fun i : 'I_n => set_cnf (cnf_qi (index_tuplei x i))).
    by move=>i j Pij; move: dis0=>/forallP/(_ i)/forallP/(_ j)/implyP/(_ Pij); 
      rewrite disj_cnfE.
  rewrite (cnf_qi_tuple PT)/=; move: (qtype_of_tuple PT)=>PTi.
  pose gi i := (projT1 (IH _ (PTi i) (PUi i))).1.
  pose fi i := (projT1 (IH _ (PTi i) (PUi i))).2.
  have giK i : cancel (gi i) (fi i)
    by move: (projT2 (IH _ (PTi i) (PUi i)))=>[][] + _ _.
  have fiK i : cancel (fi i) (gi i)
    by move: (projT2 (IH _ (PTi i) (PUi i)))=>[][] _ + _.
  have Hi i : forall j, idx_proj j = Some (fi i j)
    by move: (projT2 (IH _ (PTi i) (PUi i)))=>[] _.
  pose g i := [tuple j => cast_qtype (ty_cnfK (PTi j)) ((gi j) (flatidx i j))].
  pose f i := packidx [ffun j => (fi j) (cast_qtype (esym (ty_cnfK (PTi j))) (i ~_ j))].
  exists (g, f)=>/=. 
  - split=>i; rewrite /f /g.
    - by rewrite - [RHS]flatidxK; f_equal; apply/ffunP=>j;
        rewrite ffunE tnthE cast_qtype_comp cast_qtype_id giK.
    - by apply eq_from_tnth=>j; 
        rewrite tnthE packidxK// ffunE fiK cast_qtype_comp cast_qtype_id.
  - move=>i; rewrite /idx_tuple forallbTP=>[j|].
      by rewrite (orappE _ (esym (ty_cnfK (PTi j)))) Hi.
    rewrite forallbTP=>[j|]; first by rewrite packidxK.
    rewrite/f; do 2 f_equal; apply/ffunP=>j; rewrite !ffunE.
    by rewrite (orappE _ (esym (ty_cnfK (PTi j)))) Hi/=.
- move=>n T IH x PT; move: (qi2seq_of_ffun PT)=>->.
  rewrite flatten_uniq_disjoint=>/andP[]/forallP PUi dis0.
  have dis : disf (fun i : 'I_n => set_cnf (cnf_qi (index_ffuni x i))).
    by move=>i j Pij; move: dis0=>/forallP/(_ i)/forallP/(_ j)/implyP/(_ Pij); 
      rewrite disj_cnfE.
  rewrite (cnf_qi_ffun PT)/=; move: (qtype_of_ffun PT)=>PTi.
  pose gi i := (projT1 (IH i _ (PTi i) (PUi i))).1.
  pose fi i := (projT1 (IH i _ (PTi i) (PUi i))).2.
  have giK i : cancel (gi i) (fi i).
    by move: (projT2 (IH i _ (PTi i) (PUi i)))=>[][] + _ _.
  have fiK i : cancel (fi i) (gi i).
    by move: (projT2 (IH i _ (PTi i) (PUi i)))=>[][] _ + _.
  have Hi i : forall j, idx_proj j = Some (fi i j).
    by move: (projT2 (IH i _ (PTi i) (PUi i)))=>[] _.
  pose g i := [ffun j => cast_qtype (ty_cnfK (PTi j)) ((gi j) (flatidx i j))] : {dffun _}.
  pose f (i : {dffun _}) := packidx [ffun j => (fi j) (cast_qtype (esym (ty_cnfK (PTi j))) (i j))].
  exists (g, f)=>/=. 
  - split=>i; rewrite /f /g.
    - by rewrite - [RHS]flatidxK; f_equal; apply/ffunP=>j;
        rewrite ffunE ffunE cast_qtype_comp cast_qtype_id giK.
    - by apply/ffunP=>j; 
        rewrite ffunE packidxK// ffunE fiK cast_qtype_comp cast_qtype_id.
  - move=>i; rewrite /idx_ffun forallbTP=>[j|].
      by rewrite (orappE _ (esym (ty_cnfK (PTi j)))) Hi.
    rewrite forallbTP=>[j|]; first by rewrite packidxK.
    rewrite/f; do 2 f_equal; apply/ffunP=>j; rewrite !ffunE.
    by rewrite (orappE _ (esym (ty_cnfK (PTi j)))) Hi/=.
Qed.

Definition tv2v_fun_def (T : qType) (x : qreg T) 
  (v : 'Ht T) : 'H[msys]_(mset x) :=
  \sum_(i : evalQT T)  [< ''i ; v >] *: 
    oapp (@deltav _ _ _) 0 (idx_proj (cast_qtype (esym (ty_qregK x)) i)).
Definition tv2v_fun := nosimpl tv2v_fun_def.
Fact tv2v_key : unit. Proof. by []. Qed.
Definition tv2v := locked_with tv2v_key tv2v_fun.
Lemma tv2v_unfold : tv2v = tv2v_fun_def.
Proof. by rewrite [LHS](unlock [unlockable of tv2v]). Qed.

Lemma tv2v_is_linear T (x : qreg T) : linear (@tv2v T x).
Proof.
move=>a u v; rewrite tv2v_unfold scaler_sumr -big_split/=; apply eq_bigr=>i _.
by rewrite linearPr/= scalerA scalerDl.
Qed.
HB.instance Definition _ T x := GRing.isLinear.Build C _ _ *:%R (@tv2v T x)
  (@tv2v_is_linear T x).

Lemma tv2V_eqr T (x y : qreg T) : x =r y -> 
  forall (v : 'Ht T), (tv2v x v) =v (tv2v y v).
Proof.
move=>P1 v; move: (eq_setP P1)=>P2.
suff <-: (casths P2 (tv2v x v)) = tv2v y v by rewrite Hnd_cast.
rewrite tv2v_unfold/= linear_sum/=; apply eq_bigr=>i _.
rewrite linearZ/=; f_equal; move: P2 (ty_qregK x) (ty_qregK y).
move: (eq_cnf (index_typeK x) (index_typeK y) P1).
by rewrite /mset=>->? P2 P3; rewrite casths_id (eq_irrelevance P2 P3).
Qed.


Lemma tv2v_dv (T : qType) (x : qreg T) (t : evalQT T) : 
  tv2v x ''t = oapp (@deltav _ _ _) 0 (idx_proj (cast_qtype (esym (ty_qregK x)) t)).
Proof.
rewrite tv2v_unfold/=/tv2v_fun_def (bigD1 t) //= big1=>[i /negPf nit|];
by rewrite t2tv_dot ?nit ?scale0r// eqxx scale1r addr0.
Qed.

Lemma tv2v_onb_t2tv T (x : 'QReg[T]) :
  forall i j, [< tv2v x (t2tv i) ; tv2v x (t2tv j) >] = (i == j)%:R.
Proof.
case: x=>x /=; rewrite valid_qregE /qr2seq =>PU.
move: (index_typeK x)=>/idx_projK/(_ PU)[] []g h/= []PgK PhK Pg2.
move=>i j; rewrite !tv2v_dv !Pg2/= dv_dot.
by rewrite (inj_eq (can_inj PhK)) (inj_eq cast_qtype_inj).
Qed.

Lemma qreg_dim T (x : 'QReg[T]) :
  #|evalQT T| = dim 'H[msys]_(mset x).
Proof.
case: x=>x /=; rewrite valid_qregE -idx_card /qr2seq =>PU.
move: (index_typeK x)=>/idx_projK/(_ PU)[] []g h/= []PgK PhK Pg2.
move: (@bij_eq_card _ _ g)=>->. by exists h.
by move: (ty_qregK x)=>->.
Qed.

Lemma tv2v_conj T (x : qreg T) (v : 'Ht T) : (tv2v x v)^*v = tv2v x (v^*v).
Proof.
rewrite [v](onb_vec t2tv) !linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/=; f_equal; rewrite t2tv_conj tv2v_dv.
by case: (idx_proj _)=>[?|]/=; rewrite ?conj_dv// conjv0.
Qed.

Lemma idx_proj_inj (i : cnf) (j k : evalQT (ty_cnf i)) :
    idx_proj j = idx_proj k -> idx_proj j != None -> j = k.
Proof.
elim: i j k=>/=.
- by move=>i j k /eqP + _; rewrite /idx_bi /eq_op/= (inj_eq enum_val_inj) 
  (inj_eq (@cast_ord_inj _ _ _)) (inj_eq enum_rank_inj)=>/eqP.
- move=>i1 H1 i2 H2 [j1 j2] [k1 k2]; rewrite/idx_pair/=.
  case E1: (idx_proj _)=>[a1|]//; case E2: (idx_proj _)=>[a2|]//;
  case E5: (_ && _)=>// ; move: E5=>/andP[]/eqP F1 /eqP F2;
  case E3: (idx_proj _)=>[a3|]//; case E4: (idx_proj _)=>[a4|]//;
  case E6: (_ && _)=>// + _; move: E6=>/andP[]/eqP F3 /eqP F4 Pe; inversion Pe. 
  move: (f_equal (@idxSl _ _ _ _) H0) (f_equal (@idxSr _ _ _ _) H0).
  rewrite ?(F1,F2,F3,F4)=>G1 G2.
  by f_equal; [apply H1 | apply H2]; rewrite ?(E1,E2,E3,E4)?(G1,G2).
1: move=>n T c IH j k; rewrite /idx_tuple.
2: move=>n T c IH j k; rewrite /idx_ffun.
all: case E1 : [forall _, _] =>//; case E2 : [forall _, _] =>//;
  case E3 : [forall _, _] =>//; case E4 : [forall _, _] =>// Pe _; inversion Pe.
1: have P1 a : T = ty_cnf (c a)
    by move: E1=>/forallP/(_ a); rewrite /orapp; case: eqP.
2: have P1 a : T a = ty_cnf (c a)
    by move: E1=>/forallP/(_ a); rewrite /orapp; case: eqP.
1: apply/eq_from_tnth=>i. 2: apply/ffunP=>i.
all: move: (f_equal (@flatidx _ _ _ _ ^~ i) H0);
  move: E2 E4 E1 E3=>/forallP/(_ i)/eqP->/forallP/(_ i)/eqP->/forallP/(_ i)+/forallP/(_ i);
  rewrite !ffunE !(orappE _ (P1 _));
  case E5: (idx_proj _)=>[ij|]// _; case E6: (idx_proj _)=>[ik|]// _ /= Pij;
  by move: E6 {+}E5; rewrite Pij=><-/IH; rewrite E5/==>/(_ is_true_true)/cast_qtype_inj.
Qed.

Lemma t2v_dot_neq T (x : qreg T) (i j : evalQT T) :
  i != j -> [< tv2v x ''i ; tv2v x ''j >] = 0.
Proof.
move=>/negPf nij; rewrite !tv2v_dv.
case E1: (idx_proj _)=>[i1|]/=; last by rewrite dot0p.
case E2: (idx_proj _)=>[i2|]/=; last by rewrite dotp0.
rewrite dv_dot.
set i' := cast_qtype _ _ in E1 *; set j' := cast_qtype _ _ in E2 *.
case: eqP=>// Pi.
move: E2 {+}E1; rewrite Pi=><-/idx_proj_inj.
by rewrite E1/==>/(_ is_true_true)/eqP; rewrite /i' /j' (inj_eq (cast_qtype_inj)) nij.
Qed.

Lemma idx_proj_exists T (x : qreg T) (j : 'Idx[msys]_(mset x)) :
  {k : evalQT (ty_cnf (cnf_qi x)) | idx_proj k = Some j}.
Proof.
move: (index_typeK x); move: j; rewrite/mset.
set i := index_of_qreg x. move: i. clear x.
elim: T=>[||?|? _||? _ ? _||].
1-4,6: case=>// [x s /= + PT |||]/=; ltest; rewrite PT/= PT eqxx;
  (have P: is_basic_index x s by rewrite /is_basic_index/= PT);
  rewrite orappE=>j; rewrite/idx_proj/idx_bi;
  exists (enum_val (cast_ord (esym (dim_biE (Basic_Index P))) (enum_rank j)));
  by rewrite enum_valK cast_ord_comp cast_ord_id enum_rankK.
- move=>T1 H1 T2 H2 i + PT.
  move: (cnf_qi_pair PT) (qtype_of_pair PT)=>->/=[]PT1 PT2 j.
  move: (H1 _ (idxSl j) PT1) (H2 _ (idxSr j) PT2)=>[]k1 Pk1 []k2 Pk2.
  by exists (k1,k2); rewrite/idx_pair/= Pk1 Pk2 idxUS !eqxx.
- move=>n T IH i + PT.
  move: (cnf_qi_tuple PT) (qtype_of_tuple PT) =>-> Pi/= j.
  have PT2 k := (projT2 (IH _ (flatidx j k) (Pi k))).
  exists [tuple k => cast_qtype (ty_cnfK (Pi k)) (projT1 (IH _ (flatidx j k) (Pi k)))].
  rewrite/idx_tuple forallbTP=>[k|].
    rewrite (orappE _ (esym (ty_cnfK (Pi k)))).
    by rewrite tnthE cast_qtype_comp cast_qtype_id PT2.
  set f := [ffun _ => _].
  have Pf1 : f = flatidx j by apply/ffunP=>k; rewrite /f ffunE 
    (orappE _ (esym (ty_cnfK (Pi k)))) tnthE cast_qtype_comp cast_qtype_id PT2.
  by rewrite Pf1 forallbTP=>[?|]; rewrite flatidxK.
- move=>n T IH i + PT.
  move: (cnf_qi_ffun PT) (qtype_of_ffun PT) =>-> Pi/= j.
  have PT2 k := (projT2 (IH _ _ (flatidx j k) (Pi k))).
  exists [ffun k => cast_qtype (ty_cnfK (Pi k)) (projT1 (IH _ _ (flatidx j k) (Pi k)))].
  rewrite/idx_ffun forallbTP=>[k|].
    rewrite (orappE _ (esym (ty_cnfK (Pi k)))).
    by rewrite ffunE cast_qtype_comp cast_qtype_id PT2.
  set f := [ffun _ => orapp _ _].
  have Pf1 : f = flatidx j by apply/ffunP=>k; rewrite /f ffunE 
    (orappE _ (esym (ty_cnfK (Pi k)))) ffunE cast_qtype_comp cast_qtype_id PT2.
  by rewrite Pf1 forallbTP=>[?|]; rewrite flatidxK.
Qed.

Lemma t2v_dec T (x : qreg T) (u : 'H_(mset x)) :
  u = \sum_t [< tv2v x ''t ; u >] *: tv2v x ''t.
Proof.
rewrite (bigID (fun t => idx_proj (cast_qtype (esym (ty_qregK x)) t) != None))/=.
rewrite [X in _ + X]big1 ?addr0 =>[i|].
by rewrite negbK tv2v_dv=>/eqP->/=; rewrite scaler0.
rewrite {1}[u](onb_vec deltav)/=.
pose h : 'Idx[msys]_(mset x) -> evalQT T := fun t =>
  cast_qtype (ty_qregK x) (projT1 (idx_proj_exists t)).
pose h' := fun i => idx_proj (cast_qtype (esym (ty_qregK x)) i).
have hK i : h' (h i) = Some i.
  rewrite/h'/h cast_qtype_comp cast_qtype_id.
  by move: (projT2 (idx_proj_exists i)).
have h'K i j : h' i = Some j -> i = h j.
  move=>Pi; apply/(cast_qtype_inj (E := esym (ty_qregK x)))/idx_proj_inj;
  by rewrite -!/(h' _) ?hK Pi.
rewrite (reindex_omap h h')/=.
  move=>i; rewrite -/(h' i); case E: (h' i)=>[j/=|//] _.
  by move: E=>/h'K->.
apply eq_big=>i.
by rewrite -/(h' _) hK eqxx andbT.
by rewrite tv2v_dv -/(h' _) hK/=.
Qed.

Lemma cast_ty1 (T1 T2 T1' T2' : qType) (H1 : QPair T1 T2 = QPair T1' T2') 
  (H2 : T1 = T1') (t1 : evalQT T1) (t2 : evalQT T2) :
  (cast_qtype H1 (t1,t2)).1 = cast_qtype H2 t1.
Proof.
move: {+}H1 H2; inversion H1; clear H1.
by case: T1' / H0; case: T2' / H2 => H1 H2; rewrite !cast_qtype_id.
Qed.

Lemma cast_ty2 (T1 T2 T1' T2' : qType) (H1 : QPair T1 T2 = QPair T1' T2') 
  (H2 : T2 = T2') (t1 : evalQT T1) (t2 : evalQT T2) :
  (cast_qtype H1 (t1,t2)).2 = cast_qtype H2 t2.
Proof.
move: {+}H1 H2; inversion H1; clear H1.
by case: T1' / H0; case: T2' / H2 => H1 H2; rewrite !cast_qtype_id.
Qed.

Lemma cnf_qreg_pair (T1 T2 : qType) (x : qreg (T1 * T2)) :
  cnf_qi x = cnf_qi <{(x.1,x.2)}>.
Proof. by move: (index_typeK x)=>/cnf_qi_pair. Qed.

Lemma cnf_qreg_tuple n T (x : qreg (QArray n T)) :
  cnf_qi x = cnf_qi <{(tuple i => x.[i])}>.
Proof. by move: (index_typeK x)=>/cnf_qi_tuple. Qed.

Lemma cnf_qreg_ffun n (T : 'I_n -> qType) (x : qreg (QDFFun T)) :
  cnf_qi x = cnf_qi <{(ffun i => x.-[i])}>.
Proof. by move: (index_typeK x)=>/cnf_qi_ffun. Qed.

Lemma t2V_pair (T1 T2 : qType) (x1 : qreg T1) (x2 : qreg T2) (t1 : evalQT T1) (t2 : evalQT T2) :
  to_Hnd (tv2v x1 ''t1 ⊗v tv2v x2 ''t2) = to_Hnd (tv2v <{(x1,x2)}> (''t1 ⊗t ''t2)).
Proof.
rewrite tentv_t2tv !tv2v_dv/= /idx_pair.
move: (cast_ty1 (esym (ty_qregK <{ (x1, x2) }>)) (esym (ty_qregK x1)) t1 t2)=>->.
move: (cast_ty2 (esym (ty_qregK <{ (x1, x2) }>)) (esym (ty_qregK x2)) t1 t2)=>->.
case E1: (idx_proj _)=>[i1|]/=; last by rewrite ten0v.
case E2: (idx_proj _)=>[i2|]/=; last by rewrite tenv0.
case E3: (_ && _)=>/=.
- by rewrite dv_split; move: E3=>/andP[]/eqP->/eqP->.
- rewrite tenv_dv_eq0//.
  by rewrite - [_ || _]negbK negb_or !negbK E3.
Qed.

(* Notation funext_dep := functional_extensionality_dep. *)

Lemma t2V_tuple (n : nat) (T : qType) (x : 'I_n -> qreg T) (t : n.-tuple (evalQT T)) :
  (\tenv_i (tv2v (x i) ''(t ~_ i))%:Hnd)%FND = (tv2v <{ tuple: x }> ''t)%:Hnd.
Proof.
rewrite -to_Hnd_tens !tv2v_dv/=/idx_tuple; under tenvmP do rewrite tv2v_dv.
have Pi i : (cast_qtype (esym (ty_qregK (qreg_tuple x))) t) ~_ i = t ~_ i.
  by rewrite cast_qtype_id.
case E1: [forall _, _] =>/=; last first.
  move: E1=>/negbT; rewrite negb_forall /orapp =>/existsP[j].
  case: eqP=>[P|]; last by rewrite ty_qregK.
  rewrite Pi; case E: (idx_proj _)=>// _; rewrite tenvm0//.
  by exists j; rewrite (eq_irrelevance (esym _) P) E/=.
have Pii i : (idx_proj (cast_qtype (esym (ty_qregK (x i))) t ~_ i)) = 
  Some (orapp idx_default (fun P : T = ty_cnf (cnf_qi (x i)) =>
   odflt idx_default (idx_proj (cast_qtype P (cast_qtype (esym (ty_qregK (qreg_tuple x))) t) ~_ i)))).
   move: E1=>/forallP/(_ i); rewrite Pi/orapp; case: eqP=>// P1.
   by rewrite (eq_irrelevance (esym _) P1); case: (idx_proj _).
under tenvmP do rewrite Pii/=.
case E2: [forall _, _].
- rewrite/= dv_splitm; f_equal; apply tenvmP=>i.
  by move: E2=>/=/forallP/(_ i)/eqP->; rewrite ffunE.
- rewrite/= tenvm_dv_eq0//; move: E2=>/negbT.
  rewrite [in X in X -> _]negb_forall.
  by under [in X in X -> _]eq_existsb do rewrite [X in _ != X]ffunE.
Qed.

Lemma t2V_ffun (n : nat) (T : 'I_n -> qType) (x : forall i, qreg (T i)) (t : {dffun forall i, evalQT (T i)}):
  (\tenv_i (tv2v (x i) ''(t i))%:Hnd)%FND = (tv2v <{ ffun: x }> ''t)%:Hnd.
Proof.
rewrite -to_Hnd_tens !tv2v_dv/=/idx_ffun; under tenvmP do rewrite tv2v_dv.
have Pi i : (cast_qtype (esym (ty_qregK (qreg_ffun x))) t) i = t i.
  by rewrite cast_qtype_id.
case E1: [forall _, _] =>/=; last first.
  move: E1=>/negbT; rewrite negb_forall /orapp =>/existsP[j].
  case: eqP=>[P|]; last by rewrite ty_qregK.
  rewrite Pi; case E: (idx_proj _)=>// _; rewrite tenvm0//.
  by exists j; rewrite (eq_irrelevance (esym _) P) E/=.
have Pii i : (idx_proj (cast_qtype (esym (ty_qregK (x i))) (t i))) = 
  Some (orapp idx_default (fun P : T i = ty_cnf (cnf_qi (x i)) =>
   odflt idx_default (idx_proj (cast_qtype P (cast_qtype (esym (ty_qregK (qreg_ffun x))) t i))))).
   move: E1=>/forallP/(_ i); rewrite Pi/orapp; case: eqP=>// P1.
   by rewrite (eq_irrelevance (esym _) P1); case: (idx_proj _).
under tenvmP do rewrite Pii/=.
case E2: [forall _, _].
- rewrite/= dv_splitm; f_equal; apply/tenvmP=>i.
  by move: E2=>/=/forallP/(_ i)/eqP->; rewrite ffunE.
- rewrite/= tenvm_dv_eq0//; move: E2=>/negbT.
  rewrite [in X in X -> _]negb_forall.
  by under [in X in X -> _]eq_existsb do rewrite [X in _ != X]ffunE.
Qed.

End Theory.

Module Exports.

Import QMemory.Exports.

Definition default_qmemMixin := QMemMixin tv2v_is_linear disj_setE tv2V_eqr 
  tv2v_conj t2v_dec t2v_dot_neq qreg_dim tv2v_onb_t2tv t2V_pair t2V_tuple t2V_ffun.
Definition default_qmemType := QMemType default_qmemMixin.

HB.lock
Definition default_qmemory := default_qmemType.

Notation mlab := (mem_lab default_qmemory).
Notation msys := (@mem_sys default_qmemory).
Notation mset := (mem_set default_qmemory).
Notation tv2v := (tv2v default_qmemory).
Notation tf2f := (tf2f default_qmemory).
Notation v2tv := (@v2tv default_qmemory _).
Notation f2tf := (@f2tf default_qmemory _ _).
Notation tm2m := (@tm2m default_qmemory).
Notation v2tU := (@v2tU default_qmemory).
Notation th2h := (@th2h default_qmemory _).
Notation liftfh := (@liftfh default_qmemory _).
Notation tket := (@tket default_qmemory _).
Notation tbra := (@tbra default_qmemory _).
Notation tlin := (@tlin default_qmemory _ _).
Notation "''|' v ; x >" := (tket x v%VF).
Notation "''<' v ; x |" := (tbra x v%VF).
Notation "''|' u ; x >< v ; y |" := (muld (tket x u%VF) (tbra y v%VF)).
Notation "''|' u >< v ; x |" := (muld (tket x u%VF) (tbra x v%VF)).
Notation "''[' f ; x , y ]" := (tlin x y f%VF).
Notation "''[' f ; x ]" := (tlin x x f%VF).
Notation "''<' x | z ; w >" := (muld (tbra (tv2v w x%VF)) (tket (tv2v w z%VF))).

End Exports.

End DefaultQMem.


Add Parametric Morphism {m T} : (@tket m T)
  with signature (@eq_qreg T) ==> (@eq ('Ht T)) ==> (@eq _) as eq_qreg_tket.
Proof.
move=>x y Pxy v.
rewrite QMemory.tket.unlock. to_Fnd. by apply tv2V_eqr.
Qed.

Add Parametric Morphism {m T} : (@tbra m T)
  with signature (@eq_qreg T) ==> (@eq ('Ht T)) ==> (@eq _) as eq_qreg_tbra.
Proof.
move=>x y Pxy v.
rewrite QMemory.tbra.unlock. to_Fnd. by apply tv2V_eqr.
Qed.

Add Parametric Morphism {m T1 T2} : (@tlin m T1 T2)
  with signature (@eq_qreg T1) ==> (@eq_qreg T2) ==> 
    (@eq ('Hom{T1, T2})) ==> (@eq _) as eq_qreg_tlin.
Proof.
move=>x1 y1 P1 x2 y2 P2 f.
by rewrite QMemory.tlin.unlock; to_Fnd; apply tf2F_eqr.
Qed.

Add Parametric Morphism {m T} : (@mem_set m T) 
  with signature (@eq_qreg T) ==> (@eq _) as eq_qreg_mset.
Proof. by move=>x y; apply mset_eqr. Qed.

(* move *)
Add Parametric Morphism n (T : qType) : (@qreg_tuple n T) 
  with signature ((fun f1 f2 => forall i, f1 i =r f2 i)) ==> (@eq_qreg _) as eq_qreg_qreg_tuple.
Proof. apply eq_qreg_from_tuple. Qed.

Add Parametric Morphism n (T : 'I_n -> qType) : (@qreg_ffun n T) 
  with signature ((fun f1 f2 => forall i, f1 i =r f2 i)) ==> (@eq_qreg _) as eq_qreg_qreg_ffun.
Proof. apply eq_qreg_from_ffun. Qed.

Section DiracDef.
Variable (QMem : qmemType).
Local Notation L := (mem_lab QMem).
Local Notation H := (@mem_sys QMem).
Local Notation mset := (mem_set QMem).
Local Notation tv2v := (tv2v QMem).
Local Notation tf2f := (tf2f QMem).
Local Notation tm2m := (tm2m QMem).
Local Notation tket := (@tket QMem _).
Local Notation tbra := (@tbra QMem _).
Local Notation tlin := (@tlin QMem _ _).

(* Redefine ket, bra, lin of dirac notation *)
(* bind tv2v in order to avoid type cast    *)

Lemma tlinE T1 T2 (x1 : qreg T1) (x2 : qreg T2) f : 
  '[ tf2f x1 x2 f ]%D = tlin x1 x2 f.
Proof. by rewrite QMemory.tlin.unlock. Qed.
Lemma tketE T (x : qreg T) v :
  '| tv2v x v >%D = tket x v.
Proof. by rewrite QMemory.tket.unlock. Qed.
Lemma tbraE T (x : qreg T) v :
  '< tv2v x v |%D = tbra x v.
Proof. by rewrite QMemory.tbra.unlock. Qed.

Lemma tket_is_linear T (x : qreg T) : linear (tket x).
Proof. by move=>a u v; rewrite QMemory.tket.unlock !linearP. Qed.
HB.instance Definition _ T x := GRing.isLinear.Build C _ 'D[H]
  *:%R (tket x) (@tket_is_linear T x).

Lemma tbra_is_linear T (x : qreg T) : linear_for (Num.conj_op \; *:%R) (tbra x).
Proof. by move=>a u v; rewrite QMemory.tbra.unlock !linearP. Qed.
HB.instance Definition _ T x := GRing.isLinear.Build C _ 'D[H]
  (Num.conj_op \; *:%R) (tbra x) (@tbra_is_linear T x).

Lemma tlin_is_linear T1 T2 (x1 : qreg T1) (x2 : qreg T2) : linear (tlin x1 x2).
Proof. by move=>a u v; rewrite QMemory.tlin.unlock !linearP. Qed.
HB.instance Definition _ T1 T2 (x1 : qreg T1) (x2 : qreg T2) := 
  GRing.isLinear.Build C _ 'D[H] *:%R (tlin x1 x2) (@tlin_is_linear T1 T2 x1 x2).

Lemma tlin_wf T1 T2 (x1 : qreg T1) (x2 : qreg T2) (f : 'Hom{T1,T2}) : 
  wfdirac_axiom (mset x1) (mset x2) (tlin x1 x2 f).
Proof. by rewrite QMemory.tlin.unlock; apply/is_wfdirac. Qed.
Canonical tlin_wfdirac T1 T2 x1 x2 f := 
  WFDirac_Build (tlin x1 x2 f) (@tlin_wf T1 T2 x1 x2 f).
Canonical tlin_sqrdirac T x f := 
  SqrDirac_Build (tlin x x f) (@tlin_wf T T x x f).

Lemma tket_wf T (x : qreg T) (u : 'Ht T) : 
  wfdirac_axiom set0 (mset x) (tket x u).
Proof. by rewrite QMemory.tket.unlock; apply/is_wfdirac. Qed.
Canonical tket_wfdirac T x u := WFDirac_Build (tket x u) (@tket_wf T x u).
Canonical tket_ketdirac T x u := KetDirac_Build (tket x u) (@tket_wf T x u).

Lemma tbra_wf T (x : qreg T) (u : 'Ht T) : 
  wfdirac_axiom (mset x) set0 (tbra x u).
Proof. by rewrite QMemory.tbra.unlock; apply/is_wfdirac. Qed.
Canonical tbra_wfdirac T x u := WFDirac_Build (tbra x u) (@tbra_wf T x u).
Canonical tbra_bradirac T x u := BraDirac_Build (tbra x u) (@tbra_wf T x u).

(* Goal forall (x y : qreg QBool.[5]), (forall i, <{x.[i]}> = <{y.[i]}>) ->
  mset <{(tuple i => x.[i])}> = mset <{(tuple i => y.[i])}>.
Proof. by move=>x y Pe; under eq_qreg_from_tuple do rewrite Pe. Qed.
 
Goal forall (x y : qreg {qffun forall i < 5, 'I_i}), (forall i, <{x.-[i]}> = <{y.-[i]}>) ->
  mset <{(ffun i => x.-[i])}> = mset <{(ffun i => y.-[i])}>.
Proof. by move=>x y Pe; under eq_qreg_from_ffun do rewrite Pe. Qed. *)

Local Notation "''|' v ; x >" := (tket x v%VF).
Local Notation "''<' v ; x |" := (tbra x v%VF).
Local Notation "''|' u ; x >< v ; y |" := (muld (tket x u%VF) (tbra y v%VF)).
Local Notation "''|' u >< v ; x |" := (muld (tket x u%VF) (tbra x v%VF)).
Local Notation "''[' f ; x , y ]" := (tlin x y f%VF).
Local Notation "''[' f ; x ]" := (tlin x x f%VF).
Local Notation "''<' x | z ; w >" := (muld (tbra w x%VF) (tket w z%VF)).

Section TypedDiracBasic.
Local Open Scope dirac_scope.
Variable (T T1 T2 T3 : qType).
Variable (x : qreg T) (x1 : qreg T1) (x2 : qreg T2) (x3 : qreg T3).
Variable (y : 'QReg[T]) (y1 : 'QReg[T1]) (y2 : 'QReg[T2]) (y3 : 'QReg[T3]).
Implicit Type (c : C) (f : 'Hom{T1, T2}) (u : 'Ht T) (v : 'Ht T1) (w : 'Ht T2).

Lemma tlin0 : '[ 0; x1, x2 ] = 0. Proof. by rewrite !linear0/=. Qed.

Lemma tlinN f : - '[ f; x1, x2 ] = '[ - f; x1, x2 ].
Proof. by rewrite !linearN/=. Qed.

Lemma tlinD f1 f2 : '[ f1; x1,x2 ] + '[ f2; x1,x2 ] = '[ f1 + f2; x1,x2 ].
Proof. by rewrite !linearD/=. Qed.

Lemma tlinB f1 f2 : '[ f1; x1,x2 ] - '[ f2; x1,x2 ] = '[ f1 - f2; x1,x2 ].
Proof. by rewrite !linearB/=. Qed.

Lemma tlinZ c f : c *: '[ f; x1,x2 ] = '[ c *: f; x1,x2 ].
Proof. by rewrite !linearZ/=. Qed.

Lemma tlinP c f1 f2 : c *: '[ f1; x1,x2 ] + '[ f2; x1,x2 ] = '[ c *: f1 + f2; x1,x2 ].
Proof. by rewrite !linearP/=. Qed.

Lemma tlinMn n f : '[ f; x1,x2 ] *+ n = '[ f *+ n; x1,x2 ].
Proof. by rewrite !linearMn/=. Qed.

Lemma tlinMNn n f : '[ f; x1,x2 ] *- n = '[ f *- n; x1,x2 ].
Proof. by rewrite !linearMNn/=. Qed.

Lemma tlin_sum I (r : seq I) (P : pred I) (F : I -> 'Hom{T1,T2}) :
  \sum_(i <- r | P i) '[ F i; x1,x2 ] = '[ \sum_(i <- r | P i) (F i); x1,x2 ] .
Proof. by rewrite !linear_sum/=. Qed.

Lemma tlin1 : \1_(mset x) = '[ \1; x ].
Proof. by rewrite QMemory.tlin.unlock; f_equal; rewrite tf2f1. Qed.

Lemma tlin_adj f : '[ f; x1,x2 ]^A = '[ f^A; x2,x1 ].
Proof. by rewrite QMemory.tlin.unlock lind_adj tf2f_adj. Qed.

Lemma tlin_conj f : '[ f; x1,x2 ]^C = '[ f^C; x1,x2 ].
Proof. by rewrite QMemory.tlin.unlock lind_conj tf2f_conj. Qed.

Lemma tlin_tr f : '[ f; x1,x2 ]^T = '[ f^T; x2,x1 ].
Proof. by rewrite QMemory.tlin.unlock lind_tr tf2f_tr. Qed.

Lemma tlinM f (g : 'Hom{T3, T1}): '[ f; y1,x2 ] \o '[ g; x3,y1 ] = '[ f \o g; x3,x2 ].
Proof. by rewrite QMemory.tlin.unlock lindM tf2f_comp. Qed.

Lemma tlinG f (g : 'Hom{T3, T1}): '[ f; y1,x2 ] \· '[ g; x3,y1 ] = '[ f \o g; x3,x2 ].
Proof. by rewrite QMemory.tlin.unlock lindG tf2f_comp. Qed.
Definition tlin_comp := (tlinM, tlinG).

Lemma tlin_ketM f v : '[ f; y1,x2 ] \o '| v; y1 > = '| f v; x2 >.
Proof. by rewrite QMemory.tlin.unlock QMemory.tket.unlock lind_ketM tf2f_apply. Qed.

Lemma tlin_ketG f v : '[ f; y1,x2 ] \· '| v; y1 > = '| f v; x2 >.
Proof. by rewrite QMemory.tlin.unlock QMemory.tket.unlock lind_ketG tf2f_apply. Qed.
Definition tlin_ket := (tlin_ketM, tlin_ketG).

Lemma tlin_braM f w : '< w; y2 | \o '[ f; x1,y2 ] = '< f^A w; x1 |.
Proof. by rewrite QMemory.tlin.unlock QMemory.tbra.unlock lind_braM tf2f_adj tf2f_apply. Qed.

Lemma tlin_braG f w : '< w; y2 | \· '[ f; x1,y2 ] = '< f^A w; x1 |.
Proof. by rewrite QMemory.tlin.unlock QMemory.tbra.unlock lind_braG tf2f_adj tf2f_apply. Qed.
Definition tlin_bra := (tlin_braM, tlin_braG).

Lemma tket0 : '|0; x > = 0.
Proof. by rewrite !linear0/=. Qed.

Lemma tketN u : - '| u; x > = '|- u; x >.
Proof. by rewrite !linearN/=. Qed.

Lemma tketD u1 u2 : '| u1; x > + '| u2; x > = '| u1 + u2; x >.
Proof. by rewrite !linearD/=. Qed.

Lemma tketB u1 u2 : '| u1; x > - '| u2; x > = '| u1 - u2; x >.
Proof. by rewrite !linearB/=. Qed.

Lemma tketZ c u : c *: '| u; x > = '|c *: u; x >.
Proof. by rewrite !linearZ/=. Qed.

Lemma tketP c u1 u2 : c *: '| u1; x > + '| u2; x > = '|c *: u1 + u2; x >.
Proof. by rewrite !linearP/=. Qed.

Lemma tketMn n u : '| u; x > *+ n = '| u *+ n; x >.
Proof. by rewrite !linearMn/=. Qed.

Lemma tketMNn n u : '| u; x > *- n = '| u *- n; x >.
Proof. by rewrite !linearMNn/=. Qed.

Lemma tket_sum I (r : seq I) (P : pred I) (F : I -> 'Ht T) :
  \sum_(i <- r | P i) '|F i; x > = '|\sum_(i <- r | P i) (F i); x > .
Proof. by rewrite !linear_sum/=. Qed.

Lemma tket_adj u : '| u; x >^A = '< u; x |.
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock ketd_adj. Qed.

Lemma tket_conj u : '| u; x >^C = '| u^*v; x >.
Proof. by rewrite QMemory.tket.unlock ketd_conj tv2v_conj. Qed.

Lemma tket_tr u : '| u; x >^T = '< u^*v; x |.
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock ketd_tr tv2v_conj. Qed.

Lemma tbra0 : '<0; x | = 0.
Proof. by rewrite !linear0/=. Qed.

Lemma tbraN u : - '< u; x | = '<- u; x |.
Proof. by rewrite !linearN/=. Qed.

Lemma tbraD u1 u2 : '< u1; x | + '< u2; x | = '< u1 + u2; x |.
Proof. by rewrite !linearD/=. Qed.

Lemma tbraB u1 u2 : '< u1; x | - '< u2; x | = '< u1 - u2; x |.
Proof. by rewrite !linearB/=. Qed.

Lemma tbraZ c u : c *: '< u; x | = '< c^* *: u; x |.
Proof. by rewrite !linearZ/= conjCK. Qed.

Lemma tbraZV c u : '< c *: u; x | = c^* *: '< u; x |.
Proof. by rewrite tbraZ conjCK. Qed.

Lemma tbraP c u1 u2 : c *: '< u1; x | + '< u2; x | = '< c^* *: u1 + u2; x |.
Proof. by rewrite !linearP/= conjCK. Qed.

Lemma tbraPV c u1 u2 : '< c *: u1 + u2; x | = c^* *: '< u1; x | + '< u2; x |.
Proof. by rewrite tbraP conjCK. Qed.

Lemma tbraMn n u : '< u; x | *+ n = '< u *+ n; x |.
Proof. by rewrite !linearMn/=. Qed.

Lemma tbraMNn n u : '< u; x | *- n = '< u *- n; x |.
Proof. by rewrite !linearMNn/=. Qed.

Lemma tbra_sum I (r : seq I) (P : pred I) (F : I -> 'Ht T) :
  \sum_(i <- r | P i) '<F i; x | = '<\sum_(i <- r | P i) (F i); x | .
Proof. by rewrite !linear_sum/=. Qed.

Lemma tbra_adj u : '< u; x |^A = '| u; x >.
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock brad_adj. Qed.

Lemma tbra_conj u : '< u; x |^C = '< u^*v; x |.
Proof. by rewrite QMemory.tbra.unlock brad_conj tv2v_conj. Qed.

Lemma tbra_tr u : '< u; x |^T = '| u^*v; x >.
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock brad_tr tv2v_conj. Qed.

Lemma tinnerM u1 u2 : '< u1; y | \o '| u2; y > = [<u1 ; u2>]%:D.
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock innerM tv2v_dot. Qed.
Lemma tinnerG u1 u2 : '< u1; y | \· '| u2; y > = [<u1 ; u2>]%:D.
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock innerG tv2v_dot. Qed.
Definition tinner := (tinnerM, tinnerG).

Lemma touterM v w : '| v; x1 > \o '< w; x2 | = '[ [> v ; w <]; x2,x1 ].
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock QMemory.tlin.unlock outerM tv2v_out. Qed.
Lemma touterG v w : '| v; x1 > \· '< w; x2 | = '[ [> v ; w <]; x2,x1 ].
Proof. by rewrite QMemory.tket.unlock QMemory.tbra.unlock QMemory.tlin.unlock outerG tv2v_out. Qed.
Definition touter := (touterM, touterG).

End TypedDiracBasic.

Section TypedDiracTensor.
Local Open Scope dirac_scope.

Section BigOp.
Variable (I : Type) (r : seq I) (P : pred I) (T T1 T2 : I -> qType).

Section tlin.
Variable (x1 : forall i, qreg (T1 i)) (x2 : forall i, qreg (T2 i)).
Variable (F : forall i, 'Hom{T1 i, T2 i}).

Lemma tlinBT_adj :
      (\ten_(i <- r | P i) '[F i; x1 i, x2 i])^A = 
        \ten_(i <- r | P i) '[(F i)^A; x2 i, x1 i].
Proof. by rewrite tends_adj bigd; apply eq_bigr=>i _; rewrite tlin_adj. Qed.

Lemma tlinBT_conj :
      (\ten_(i <- r | P i) '[F i; x1 i, x2 i])^C = 
        \ten_(i <- r | P i) '[(F i)^C; x1 i, x2 i].
Proof. by rewrite tends_conj bigd; apply eq_bigr=>i _; rewrite tlin_conj. Qed.

Lemma tlinBT_tr :
      (\ten_(i <- r | P i) '[F i; x1 i, x2 i])^T = 
        \ten_(i <- r | P i) '[(F i)^T; x2 i, x1 i].
Proof. by rewrite tends_tr bigd; apply eq_bigr=>i _; rewrite tlin_tr. Qed.
End tlin.

Section tket_tbra.
Variable (x : forall i, qreg (T i)) (F : forall i, 'Ht (T i)).

Lemma tketBT_adj :
      (\ten_(i <- r | P i) '|F i; x i>)^A = 
        \ten_(i <- r | P i) '< F i; x i |.
Proof. by rewrite tends_adj bigd; apply eq_bigr=>i _; rewrite tket_adj. Qed.

Lemma tketBT_conj :
      (\ten_(i <- r | P i) '|F i; x i>)^C = 
        \ten_(i <- r | P i) '|(F i)^*v; x i>.
Proof. by rewrite tends_conj bigd; apply eq_bigr=>i _; rewrite tket_conj. Qed.

Lemma tketBT_tr :
      (\ten_(i <- r | P i) '|F i; x i>)^T = 
        \ten_(i <- r | P i) '< (F i)^*v; x i |.
Proof. by rewrite tends_tr bigd; apply eq_bigr=>i _; rewrite tket_tr. Qed.

Lemma tbraBT_adj :
      (\ten_(i <- r | P i) '<F i; x i|)^A = 
        \ten_(i <- r | P i) '| F i; x i >.
Proof. by rewrite tends_adj bigd; apply eq_bigr=>i _; rewrite tbra_adj. Qed.

Lemma tbraBT_conj :
      (\ten_(i <- r | P i) '<F i; x i|)^C = 
        \ten_(i <- r | P i) '<(F i)^*v; x i|.
Proof. by rewrite tends_conj bigd; apply eq_bigr=>i _; rewrite tbra_conj. Qed.

Lemma tbraBT_tr :
      (\ten_(i <- r | P i) '<F i; x i|)^T = 
        \ten_(i <- r | P i) '| (F i)^*v; x i >.
Proof. by rewrite tends_tr bigd; apply eq_bigr=>i _; rewrite tbra_tr. Qed.
End tket_tbra.
End BigOp.

Section BigComp.
Variable (I : finType) (P : pred I) (T T1 T2 : I -> qType).
Variable (x : forall i, 'QReg[T i]) (F G : forall i, 'Ht (T i)).

Lemma tinnerMBT :
  (forall i j, P i -> P j -> i != j -> [disjoint mset (x i) & mset (x j)]) ->
  (\ten_(i | P i) '<F i; x i|) \o (\ten_(i | P i) '|G i; x i>) 
  = (\prod_(i | P i) [<F i ; G i>])%:D.
Proof.
by move=>P1; rewrite QMemory.tket.unlock QMemory.tbra.unlock innerMBT// 
  ?index_enum_uniq//; under eq_bigr do rewrite tv2v_dot.
Qed.

Lemma tinnerGBT :
  (forall i j : I, P i -> P j -> i != j -> [disjoint mset (x i) & mset (x j)]) ->
  (\ten_(i | P i) '<F i; x i|) \· (\ten_(i | P i) '|G i; x i>) 
  = (\prod_(i | P i) [<F i ; G i>])%:D.
Proof. rewrite dotd_mul/=; exact: tinnerMBT. Qed.
Definition tinnerBT := (tinnerMBT, tinnerGBT).

Lemma touterMBT :
  (forall i j, P i -> P j -> i != j -> [disjoint mset (x i) & mset (x j)]) ->
  (\ten_(i | P i) '|F i; x i>) \o (\ten_(i | P i) '<G i; x i|) 
  = (\ten_(i | P i) '[[>F i ; G i<]; x i]).
Proof.
by move=>P1; rewrite QMemory.tket.unlock QMemory.tbra.unlock outerMBT// 
  ?index_enum_uniq//; under eq_bigr do rewrite tketE tbraE touter.
Qed.

Lemma touterGBT :
  (forall i j : I, P i -> P j -> i != j -> [disjoint mset (x i) & mset (x j)]) ->
  (\ten_(i | P i) '|F i; x i>) \· (\ten_(i | P i) '<G i; x i|) 
  = (\ten_(i | P i) '[[>F i ; G i<]; x i]).
Proof. rewrite dotd_mul/=; exact: touterMBT. Qed.
Definition touterBT := (touterMBT, touterGBT).

End BigComp.

Section Ten2.
Variable (T1 T2 T3 T4 : qType) (x1 : qreg T1) (x2 : qreg T2) (x3 : qreg T3) (x4 : qreg T4).

Lemma tlin2_adj f1 f2 :
  ('[ f1; x1,x3 ] \⊗ '[ f2; x2,x4])^A = '[ f1^A; x3,x1 ] \⊗ '[ f2^A; x4,x2].
Proof. by rewrite adjdT !tlin_adj. Qed.

Lemma tlin2_conj f1 f2 :
  ('[ f1; x1,x3 ] \⊗ '[ f2; x2,x4])^C = '[ f1^C; x1,x3 ] \⊗ '[ f2^C; x2,x4].
Proof. by rewrite conjdT !tlin_conj. Qed.

Lemma tlin2_tr f1 f2 :
  ('[ f1; x1,x3 ] \⊗ '[ f2; x2,x4])^T = '[ f1^T; x3,x1 ] \⊗ '[ f2^T; x4,x2].
Proof. by rewrite trdT !tlin_tr. Qed.

Lemma tket2_adj u1 u2 :
  ('| u1; x1 > \⊗ '| u2; x2 >)^A = '< u1; x1 | \⊗ '< u2; x2 |.
Proof. by rewrite adjdT !tket_adj. Qed.

Lemma tket2_conj u1 u2 :
  ('| u1; x1 > \⊗ '| u2; x2 >)^C = '| u1^*v; x1 > \⊗ '| u2^*v; x2 >.
Proof. by rewrite conjdT !tket_conj. Qed.

Lemma tket2_tr u1 u2 :
  ('| u1; x1 > \⊗ '| u2; x2 >)^T = '< u1^*v; x1 | \⊗ '< u2^*v; x2 |.
Proof. by rewrite trdT !tket_tr. Qed.

Lemma tbra2_adj u1 u2 :
  ('< u1; x1 | \⊗ '< u2; x2 |)^A = '| u1; x1 > \⊗ '| u2; x2 >.
Proof. by rewrite adjdT !tbra_adj. Qed.

Lemma tbra2_conj u1 u2 :
  ('< u1; x1 | \⊗ '< u2; x2 |)^C = '< u1^*v; x1 | \⊗ '< u2^*v; x2 |.
Proof. by rewrite conjdT !tbra_conj. Qed.

Lemma tbra2_tr u1 u2 :
  ('< u1; x1 | \⊗ '< u2; x2 |)^T = '| u1^*v; x1 > \⊗ '| u2^*v; x2 >.
Proof. by rewrite trdT !tbra_tr. Qed.
End Ten2.

Lemma tlinT_pair T1 T2 T3 T4 (x1 : qreg T1) (x2 : qreg T2) (x3 : qreg T3) (x4 : qreg T4)
  (f1 : 'Hom{T1,T3}) (f2 : 'Hom{T2,T4}) : 
  '[ f1; x1,x3 ] \⊗ '[ f2; x2,x4] = '[ f1 ⊗f f2; (x1,x2),(x3,x4) ].
Proof. by rewrite QMemory.tlin.unlock lindT -tf2f_pair lind_cast. Qed.  

Lemma tlinT_tuple n T1 T2 (x1 : 'I_n -> qreg T1) (x2 : 'I_n -> qreg T2) 
  (f : 'I_n -> 'Hom{T1,T2}) :
  \ten_i '[f i; x1 i, x2 i] = '[tentf_tuple f; (tuple: x1) , (tuple: x2) ].
Proof. by rewrite QMemory.tlin.unlock tenfm_correct -tf2f_tuple lind_cast. Qed.

Lemma tlinT_ffun n (T1 : 'I_n -> qType) (T2 : 'I_n -> qType) 
  (x1 : forall i, qreg (T1 i)) (x2 : forall i, qreg (T2 i))
   (f : forall i, 'Hom{T1 i, T2 i}) :
  \ten_i '[f i; x1 i, x2 i] = '[tentf_dffun f; (ffun: x1), (ffun: x2)].
Proof. by rewrite QMemory.tlin.unlock tenfm_correct -tf2f_ffun lind_cast. Qed.
Definition tlinT := (tlinT_pair, tlinT_tuple, tlinT_ffun).

Lemma tlinT_pairV T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4))
  (f1 : 'Hom{T1,T3}) (f2 : 'Hom{T2,T4}) : 
  '[ f1 ⊗f f2; x1,x2 ] = '[ f1; x1.1,x2.1 ] \⊗ '[ f2; x1.2,x2.2].
Proof. by rewrite tlinT_pair !eq_qreg_pair. Qed.  

Lemma tlinT_tupleV n T1 T2 (x1 : qreg T1.[n]) (x2 : qreg T2.[n]) 
  (f : 'I_n -> 'Hom{T1,T2}) :
  '[tentf_tuple f; x1,x2 ] = \ten_i '[f i; x1.[i], x2.[i]].
Proof. by rewrite tlinT_tuple !eq_qreg_tuple. Qed.

Lemma tlinT_ffunV n (T1 : 'I_n -> qType) (T2 : 'I_n -> qType) 
  (x1 : qreg {qffun T1}) (x2 : qreg {qffun T2})
   (f : forall i, 'Hom{T1 i, T2 i}) :
   '[tentf_dffun f; x1, x2] = \ten_i '[f i; x1.-[i], x2.-[i]].
Proof. by rewrite tlinT_ffun !eq_qreg_ffun. Qed.
Definition tlinTV := (tlinT_pairV, tlinT_tupleV, tlinT_ffunV).

Lemma tketT_pair T1 T2 (x1 : qreg T1) (x2 : qreg T2)
  (u1 : 'Ht T1) (u2 : 'Ht T2) : 
  '| u1; x1 > \⊗ '| u2; x2 > = '| u1 ⊗t u2; (x1,x2) >.
Proof. by rewrite QMemory.tket.unlock ketdT -tv2v_pair ketd_cast. Qed.  

Lemma tketT_tuple n T (x : 'I_n -> qreg T) (u : 'I_n -> 'Ht T) :
  \ten_i '|u i; x i > = '|tentv_tuple u; (tuple: x) >.
Proof. by rewrite QMemory.tket.unlock tenvm_correct -tv2v_tuple ketd_cast. Qed.  

Lemma tketT_ffun n (T : 'I_n -> qType) (x : forall i, qreg (T i))
   (u : forall i, 'Ht (T i)) :
  \ten_i '|u i; x i > = '|tentv_dffun u; (ffun: x) >.
Proof. by rewrite QMemory.tket.unlock tenvm_correct -tv2v_ffun ketd_cast. Qed.
Definition tketT := (tketT_pair, tketT_tuple, tketT_ffun).

Lemma tketT_pairV T1 T2 (x : qreg (T1 * T2)) (u1 : 'Ht T1) (u2 : 'Ht T2) : 
  '| u1 ⊗t u2; x > = '| u1; x.1 > \⊗ '| u2; x.2 >.
Proof. by rewrite tketT_pair !eq_qreg_pair. Qed.  

Lemma tketT_tupleV n T (x : qreg T.[n]) (u : 'I_n -> 'Ht T) :
  '|tentv_tuple u; x > = \ten_i '|u i; x.[i] >.
Proof. by rewrite tketT_tuple !eq_qreg_tuple. Qed.

Lemma tketT_ffunV n (T : 'I_n -> qType) (x : qreg {qffun T})
   (u : forall i, 'Ht (T i)) :
   '|tentv_dffun u; x > = \ten_i '|u i; x.-[i] >.
Proof. by rewrite tketT_ffun !eq_qreg_ffun. Qed.
Definition tketTV := (tketT_pairV, tketT_tupleV, tketT_ffunV).

Lemma tbraT_pair T1 T2 (x1 : qreg T1) (x2 : qreg T2)
  (u1 : 'Ht T1) (u2 : 'Ht T2) : 
  '< u1; x1 | \⊗ '< u2; x2 | = '< u1 ⊗t u2; (x1,x2) |.
Proof. by rewrite QMemory.tbra.unlock bradT -tv2v_pair brad_cast. Qed.  

Lemma tbraT_tuple n T (x : 'I_n -> qreg T) (u : 'I_n -> 'Ht T) :
  \ten_i '<u i; x i | = '<tentv_tuple u; (tuple: x) |.
Proof. by rewrite -tket_adj -tketT_tuple tketBT_adj. Qed.

Lemma tbraT_ffun n (T : 'I_n -> qType) (x : forall i, qreg (T i))
   (u : forall i, 'Ht (T i)) :
  \ten_i '<u i; x i | = '<tentv_dffun u; (ffun: x) |.
Proof. by rewrite -tket_adj -tketT_ffun tketBT_adj. Qed.
Definition tbraT := (tbraT_pair, tbraT_tuple, tbraT_ffun).

Lemma tbraT_pairV T1 T2 (x : qreg (T1 * T2)) (u1 : 'Ht T1) (u2 : 'Ht T2) : 
  '< u1 ⊗t u2; x | = '< u1; x.1 | \⊗ '< u2; x.2 |.
Proof. by rewrite tbraT_pair !eq_qreg_pair. Qed.  

Lemma tbraT_tupleV n T (x : qreg T.[n]) (u : 'I_n -> 'Ht T) :
  '<tentv_tuple u; x | = \ten_i '<u i; x.[i] |.
Proof. by rewrite tbraT_tuple !eq_qreg_tuple. Qed.

Lemma tbraT_ffunV n (T : 'I_n -> qType) (x : qreg {qffun T})
   (u : forall i, 'Ht (T i)) :
   '<tentv_dffun u; x | = \ten_i '<u i; x.-[i] |.
Proof. by rewrite tbraT_ffun !eq_qreg_ffun. Qed.
Definition tbraTV := (tbraT_pairV, tbraT_tupleV, tbraT_ffunV).

Lemma tlinTC T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (f1 : 'Hom{T1,T3}) (f2 : 'Hom{T2,T4}) :
  '[ f1 ⊗f f2; x1,x2] = '[ f2 ⊗f f1; (x1.2,x1.1), (x2.2,x2.1)].
Proof. by rewrite tlinT_pairV tendC tlinT_pair. Qed.

Lemma tketTC T1 T2 (x : qreg (T1 * T2)) (v1 : 'Ht T1) (v2 : 'Ht T2) : 
  '| v1 ⊗t v2; x > = '| v2 ⊗t v1; (x.2,x.1)>.
Proof. by rewrite tketT_pairV tendC tketT_pair. Qed.

Lemma tbraTC T1 T2 (x : qreg (T1 * T2)) (v1 : 'Ht T1) (v2 : 'Ht T2) :
  '< v1 ⊗t v2; x | = '< v2 ⊗t v1; (x.2,x.1) |.
Proof. by rewrite tbraT_pairV tendC tbraT_pair. Qed.

Lemma touterTC T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (u1 : 'Ht T1) (u2 : 'Ht T2) (u3 : 'Ht T3) (u4 : 'Ht T4) :
  '[ [> u3 ⊗t u4 ; u1 ⊗t u2 <]; x1,x2] = 
    '[ [> u4 ⊗t u3 ; u2 ⊗t u1 <]; (x1.2,x1.1), (x2.2,x2.1)].
Proof. by rewrite -!tentv_out tlinTC. Qed.

Lemma touterTCl T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (u1 : 'Ht (T1 * T2)) (u3 : 'Ht T3) (u4 : 'Ht T4) :
  '[ [> u3 ⊗t u4 ; u1 <]; x1,x2] = 
    '[ [> u4 ⊗t u3 ; u1 <]; x1, (x2.2,x2.1)].
Proof. by rewrite -touterM tketTC touterM. Qed.

Lemma touterTCr T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (u1 : 'Ht T1) (u2 : 'Ht T2) (u3 : 'Ht (T3 * T4)) :
  '[ [> u3 ; u1 ⊗t u2 <]; x1,x2] = 
    '[ [> u3 ; u2 ⊗t u1 <]; (x1.2,x1.1), x2].
Proof. by rewrite -touterM tbraTC touterM. Qed.

Definition eq_qrE := (eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, 
  eq_qreg_ffuni, eq_qreg_pair, eq_qreg_tuple, eq_qreg_ffun).

Lemma tketT_swap T1 T2 (x : qreg (T2 * T1)) (u : 'Ht (T1 * T2)) :
  '| swaptf u; x > = '|u ; (x.2,x.1) >.
Proof.
rewrite (onb_vec t2tv u)/= !linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/=; f_equal.
by rewrite [i ]surjective_pairing -tentv_t2tv swaptfEtv tketTC !eq_qrE.
Qed.
Lemma tketT_swapV T1 T2 (x : qreg (T1 * T2)) (u : 'Ht (T1 * T2)) :
  '| u; x > = '|swaptf u ; (x.2,x.1) >.
Proof. by rewrite tketT_swap !eq_qrE. Qed.

Lemma tbraT_swap T1 T2 (x : qreg (T2 * T1)) (u : 'Ht (T1 * T2)) :
  '< swaptf u; x | = '< u ; (x.2,x.1) |.
Proof. by rewrite -tket_adj tketT_swap tket_adj. Qed.
Lemma tbraT_swapV T1 T2 (x : qreg (T1 * T2)) (u : 'Ht (T1 * T2)) :
  '< u; x | = '< swaptf u ; (x.2,x.1) |.
Proof. by rewrite tbraT_swap !eq_qrE. Qed.

Lemma tlinT_swap T1 T2 T3 T4 (x1 : qreg (T2 * T1)) (x2 : qreg (T4 * T3)) 
  (f : 'Hom{T1 * T2, T3 * T4}) :
  '[ swaptf \o f \o swaptf ; x1, x2 ] = '[ f ; (x1.2,x1.1) , (x2.2,x2.1) ].
Proof.
rewrite (onb_lfun2 t2tv t2tv f) pair_big/= linear_sumr linear_suml !linear_sum/=.
apply eq_bigr=>[][][]i1 i2[]j1 j2 _; rewrite linearZr linearZl/= !linearZ/=; f_equal.
by rewrite outp_compr outp_compl swaptf_adj -!tentv_t2tv !swaptfEtv -!tentv_out tlinTC !eq_qrE.
Qed.
Lemma tlinT_swapV T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (f : 'Hom{T1 * T2, T3 * T4}) :
  '[ f ; x1, x2 ] = '[ swaptf \o f \o swaptf ; (x1.2,x1.1) , (x2.2,x2.1) ].
Proof. by rewrite tlinT_swap !eq_qrE. Qed.

Lemma touterT_swapl T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T4 * T3)) 
  (u : 'Ht (T1 * T2)) (v : 'Ht (T3 * T4)) :
  '[ [> swaptf v ; u <] ; x1,x2 ] = '[ [> v ; u <] ; x1,(x2.2,x2.1) ].
Proof. by rewrite -[LHS]touterM tketT_swap touterM. Qed.
Lemma touterT_swapVl T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (u : 'Ht (T1 * T2)) (v : 'Ht (T3 * T4)) :
  '[ [> v ; u <] ; x1,x2 ] = '[ [> swaptf v ; u <] ; x1,(x2.2,x2.1) ].
Proof. by rewrite touterT_swapl !eq_qrE. Qed.

Lemma touterT_swapr T1 T2 T3 T4 (x1 : qreg (T2 * T1)) (x2 : qreg (T3 * T4)) 
  (u : 'Ht (T1 * T2)) (v : 'Ht (T3 * T4)) :
  '[ [> v ; swaptf u <] ; x1,x2 ] = '[ [> v ; u <] ; (x1.2,x1.1),x2 ].
Proof. by rewrite -[LHS]touterM tbraT_swap touterM. Qed.
Lemma touterT_swapVr T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (u : 'Ht (T1 * T2)) (v : 'Ht (T3 * T4)) :
  '[ [> v ; u <] ; x1,x2 ] = '[ [> v ; swaptf u <] ; (x1.2,x1.1),x2 ].
Proof. by rewrite touterT_swapr !eq_qrE. Qed.

Lemma touterT_swap T1 T2 T3 T4 (x1 : qreg (T2 * T1)) (x2 : qreg (T4 * T3)) 
  (u : 'Ht (T1 * T2)) (v : 'Ht (T3 * T4)) :
  '[ [> swaptf v ; swaptf u <] ; x1,x2 ] = 
    '[ [> v ; u <] ; (x1.2,x1.1) , (x2.2,x2.1) ].
Proof. by rewrite touterT_swapl touterT_swapr. Qed.
Lemma touterT_swapV T1 T2 T3 T4 (x1 : qreg (T1 * T2)) (x2 : qreg (T3 * T4)) 
  (u : 'Ht (T1 * T2)) (v : 'Ht (T3 * T4)) :
  '[ [> v ; u <] ; x1,x2 ] = 
    '[ [> swaptf v ; swaptf u <] ; (x1.2,x1.1) , (x2.2,x2.1) ].
Proof. by rewrite touterT_swap !eq_qrE. Qed.

Section tlinGid.
Variable (T1 T2 T3 T4 : qType) (x1 : qreg T1) (x2 : qreg T2) (x3 : qreg T3) (x4 : qreg T4).

Lemma tlin1Gl f : '[ \1; x1 ] \· '[ f; x3,(x1,x2) ] = '[ f; x3,(x1,x2) ].
Proof. by rewrite -tlin1 dotIdid// mset_pairV !eq_qrE subsetUl. Qed.
Lemma tlin1Gr f : '[ \1; x2 ] \· '[ f; x3,(x1,x2) ] = '[ f; x3,(x1,x2) ].
Proof. by rewrite -tlin1 dotIdid// mset_pairV !eq_qrE subsetUr. Qed.
Lemma tlinG1l f : '[ f; (x1,x2),x3 ] \· '[ \1; x1 ] = '[ f; (x1,x2),x3 ].
Proof. by rewrite -tlin1 dotdIid// mset_pairV !eq_qrE subsetUl. Qed.
Lemma tlinG1r f : '[ f; (x1,x2),x3 ] \· '[ \1; x2 ] = '[ f; (x1,x2),x3 ].
Proof. by rewrite -tlin1 dotdIid// mset_pairV !eq_qrE subsetUr. Qed.
Definition tlin1G := (tlin1Gl, tlin1Gr).
Definition tlinG1 := (tlinG1l, tlinG1r).
Lemma tket1Gl v : '[ \1; x1 ] \· '| v; (x1,x2) > = '| v; (x1,x2) >.
Proof. by rewrite -tlin1 dotIdid// mset_pairV !eq_qrE subsetUl. Qed.
Lemma tket1Gr v : '[ \1; x2 ] \· '| v; (x1,x2) > = '| v; (x1,x2) >.
Proof. by rewrite -tlin1 dotIdid// mset_pairV !eq_qrE subsetUr. Qed.
Definition tket1G := (tket1Gl, tket1Gr).
Lemma tbra1Gl v : '< v; (x1,x2) | \· '[ \1; x1 ] = '< v; (x1,x2) |.
Proof. by rewrite -tlin1 dotdIid// mset_pairV !eq_qrE subsetUl. Qed.
Lemma tbra1Gr v : '< v; (x1,x2) | \· '[ \1; x2 ] = '< v; (x1,x2) |.
Proof. by rewrite -tlin1 dotdIid// mset_pairV !eq_qrE subsetUr. Qed.
Definition tbraG1 := (tbra1Gl, tbra1Gr).
End tlinGid.

Section tlinG2.
Variable (T1 T2 T3 T4 : qType) (x1 : 'QReg[T1]) (x2 : 'QReg[T2]) (x3 : qreg T3) (x4 : qreg T4).

Lemma tlintGl N1 f (dis : disjoint_qreg x1 x2) : 
  '[ N1; x1 ] \· '[ f; x3, (x1,x2) ] = '[(N1 ⊗f \1) \o f; x3, (x1,x2) ].
Proof.
by rewrite -[RHS](tlinG _ _ <{(x1, x2)}>) tlinTV !eq_qrE 
  -dotd_ten//= -?dotdA/= ?tlin1G// -disj_setE.
Qed.
Lemma tlintGr N2 f (dis : disjoint_qreg x1 x2) : 
  '[ N2; x2 ] \· '[ f; x3, (x1,x2) ] = '[(\1 ⊗f N2) \o f; x3, (x1,x2) ].
Proof.
by rewrite -[RHS](tlinG _ _ <{(x1, x2)}>) tlinTV !eq_qrE tendC
  -dotd_ten//= -?dotdA/= ?tlin1G// disjoint_sym -disj_setE.
Qed.
Lemma tlinGtl f N1 (dis : disjoint_qreg x1 x2) : 
  '[ f; (x1,x2),x3 ] \· '[ N1; x1 ] = '[ f \o (N1 ⊗f \1); (x1,x2),x3 ].
Proof.
by rewrite -[RHS](tlinG _ _ <{(x1, x2)}>) tlinTV !eq_qrE tendC
  -dotd_ten//= ?dotdA/= ?tlinG1// disjoint_sym -disj_setE.
Qed.
Lemma tlinGtr f N2 (dis : disjoint_qreg x1 x2) :
  '[ f; (x1,x2),x3 ] \· '[ N2; x2 ] = '[ f \o (\1 ⊗f N2); (x1,x2),x3 ].
Proof.
by rewrite -[RHS](tlinG _ _ <{(x1, x2)}>) tlinTV !eq_qrE
  -dotd_ten//= ?dotdA/= ?tlinG1// -disj_setE.
Qed.
Lemma tketGl N1 v (dis : disjoint_qreg x1 x2) :
  '[ N1; x1,x3 ] \· '| v; (x1,x2) > = '|(N1 ⊗f \1) v; (x3,x2) >.
Proof.
by rewrite -(tlin_ketG _ <{(x1,x2)}>) tlinTV !eq_qrE -dotd_ten/=
  -?dotdA/= ?tket1G// -disj_setE.
Qed.
Lemma tketGr N2 v (dis : disjoint_qreg x1 x2) :
  '[ N2; x2,x3 ] \· '| v; (x1,x2) > = '|(\1 ⊗f N2) v; (x1,x3) >.
Proof.
by rewrite -(tlin_ketG _ <{(x1,x2)}>) tlinTV !eq_qrE tendC -dotd_ten/=
  -?dotdA/= ?tket1G// disjoint_sym -disj_setE.
Qed.
Lemma tbraGl v N1 (dis : disjoint_qreg x1 x2) :
  '< v; (x1,x2) | \· '[ N1; x3,x1 ] = '<(N1^A ⊗f \1) v; (x3,x2) |.
Proof. by rewrite -[LHS]adjdK adjdG tlin_adj tbra_adj tketGl// tket_adj. Qed.
Lemma tbraGr v N2 (dis : disjoint_qreg x1 x2) :
  '< v; (x1,x2) | \· '[ N2; x3,x2 ] = '<(\1 ⊗f N2^A) v; (x1,x3) |.
Proof. by rewrite -[LHS]adjdK adjdG tlin_adj tbra_adj tketGr// tket_adj. Qed.
End tlinG2.

Section tlinG.
Variable (T T1 T2 : qType) (x : 'QReg[T]) (x1 : qreg T1) (x2 : qreg T2).
Variable (S S' : {set L}) (e : 'D[H]_(S,S')).

Lemma tlinGTl f1 f2 (dis : [disjoint mset x & S']) :
  '[ f1; x,x1 ] \· ('[ f2; x2,x ] \⊗ e) = '[ f1 \o f2; x2,x1 ] \⊗ e.
Proof. by rewrite -(tlinG _ _ x) dotdTll. Qed.
Lemma tlinGTr f1 f2 (dis : [disjoint mset x & S']) :
  '[ f1; x,x1 ] \· (e \⊗ '[ f2; x2,x ]) = e \⊗ '[ f1 \o f2; x2,x1 ].
Proof. by rewrite -(tlinG _ _ x) dotdTlr. Qed.
Definition tlinGT := (tlinGTl, tlinGTr).
Lemma tlinTGl f1 f2 (dis : [disjoint mset x & S]) :
  ('[ f1; x,x2 ] \⊗ e) \· '[ f2; x1,x ] = '[ f1 \o f2; x1,x2 ] \⊗ e.
Proof. by rewrite -(tlinG _ _ x) dotdTrl. Qed.
Lemma tlinTGr f1 f2 (dis : [disjoint mset x & S]) :
  (e \⊗ '[ f1; x,x2 ]) \· '[ f2; x1,x ] = e \⊗ '[ f1 \o f2; x1,x2 ].
Proof. by rewrite -(tlinG _ _ x) dotdTrr. Qed.
Definition tlinTG := (tlinTGl, tlinTGr).

Lemma tketGTl f v (dis : [disjoint mset x & S']) :
  '[ f; x,x1 ] \· ('| v; x > \⊗ e) = '| f v; x1 > \⊗ e.
Proof. by rewrite -(tlin_ketG _ x) dotdTll. Qed. 
Lemma tketGTr f v (dis : [disjoint mset x & S']) :
  '[ f; x,x1 ] \· (e \⊗ '| v; x >) = e \⊗ '| f v; x1 >.
Proof. by rewrite -(tlin_ketG _ x) dotdTlr. Qed.
Definition tketGT := (tketGTl, tketGTr).
Lemma tketTGl f v (dis : [disjoint mset x & S]) :
  ('[ f; x,x1 ] \⊗ e) \· '| v; x > = '| f v; x1 > \⊗ e.
Proof. by rewrite -(tlin_ketG _ x) dotdTrl. Qed.
Lemma tketTGr f v (dis : [disjoint mset x & S]) :
  (e \⊗ '[ f; x,x1 ]) \· '| v; x > = e \⊗ '| f v; x1 >.
Proof. by rewrite -(tlin_ketG _ x) dotdTrr. Qed.
Definition tketTG := (tketTGl, tketTGr).

Lemma tbraGTl f v (dis : [disjoint mset x & S']) :
  '<v; x| \· ('[ f; x1,x ] \⊗ e) = '< f^A v; x1 | \⊗ e.
Proof. by rewrite -(tlin_braG _ x) dotdTll. Qed. 
Lemma tbraGTr f v (dis : [disjoint mset x & S']) :
  '<v; x| \· (e \⊗ '[ f; x1,x ]) = e \⊗ '< f^A v; x1 |.
Proof. by rewrite -(tlin_braG _ x) dotdTlr. Qed.
Definition tbraGT := (tbraGTl, tbraGTr).
Lemma tbraTGl f v (dis : [disjoint mset x & S]) :
  ('<v; x| \⊗ e) \· '[ f; x1,x ] = '< f^A v; x1 | \⊗ e.
Proof. by rewrite -(tlin_braG _ x) dotdTrl. Qed.
Lemma tbraTGr f v (dis : [disjoint mset x & S]) :
  (e \⊗ '<v; x|) \· '[ f; x1,x ] = e \⊗ '< f^A v; x1 |.
Proof. by rewrite -(tlin_braG _ x) dotdTrr. Qed.
Definition tbraTG := (tbraTGl, tbraTGr).

End tlinG.

Section Order.
Variable (T T1 T2 : qType) (x : qreg T) (x1 : qreg T1) (x2 : qreg T2).
Variable (y : 'QReg[T]) (y1 : 'QReg[T1]) (y2 : 'QReg[T2]).

Lemma tlin_id f : 
  '[f; x1,x2] (mset x1) (mset x2) = tf2f x1 x2 f.
Proof. by rewrite QMemory.tlin.unlock lind_id. Qed.

Lemma tlin_id_cast S1 S2 (eqs : (mset x1 = S1) * (mset x2 = S2)) f : 
  '[f; x1,x2] S1 S2 = castlf eqs (tf2f x1 x2 f).
Proof. by case: eqs=>e1 e2; case: _ / e1; case: _ / e2; rewrite tlin_id castlf_id. Qed.

Lemma tket_id v : 
  d2v (mset x) '|v; x> = tv2v x v.
Proof. by rewrite QMemory.tket.unlock ketdK. Qed.

Lemma tket_id_cast S (eqs : mset x = S) v : 
  d2v S '|v; x> = casths eqs (tv2v x v).
Proof. by case: _ / eqs; rewrite tket_id casths_id. Qed.

Lemma tbra_id v : 
  d2dv (mset x) '<v; x| = tv2v x v.
Proof. by rewrite QMemory.tbra.unlock bradK. Qed.

Lemma tbra_id_cast S (eqs : mset x = S) v : 
  d2dv S '<v; x| = casths eqs (tv2v x v).
Proof. by case: _ / eqs; rewrite tbra_id casths_id. Qed.

Lemma tlin_leP (f1 f2 : 'End{T}) :
  f1 ⊑ f2 -> '[f1;x] ⊑ '[f2;x].
Proof. by rewrite QMemory.tlin.unlock lin_lef; apply tf2f_lefP. Qed.

Lemma tlin_lefP S (f1 f2 : 'End{T}) :
  f1 ⊑ f2 -> '[f1;x] S S ⊑ '[f2;x] S S.
Proof.
move=>/tlin_leP; rewrite -subv_ge0=>/ged0P[]/(_ S) + _.
by rewrite !diracE subv_ge0.
Qed.

Lemma tlin_lef1P S (f : 'End{T}) : f ⊑ \1 -> '[f;x] S S ⊑ \1.
Proof.
move=>P; case: (@eqP _ S (mset x))=>[->|/eqP P1].
  by rewrite QMemory.tlin.unlock lind_id tf2f_le1P.
by rewrite QMemory.tlin.unlock lind_eq0l// lef01.
Qed.
Lemma tlin_gef0P S (f : 'End{T}) : 0%:VF ⊑ f -> 0%:VF ⊑ '[f;x] S S.
Proof.
move=>P; case: (@eqP _ S (mset x))=>[->|/eqP P1].
  by rewrite QMemory.tlin.unlock lind_id tf2f_ge0P.
by rewrite QMemory.tlin.unlock lind_eq0l.
Qed.
Lemma tlin_ge0P (f : 'End{T}) : 0%:VF ⊑ f -> 0 ⊑ '[f;x].
Proof. by move=>P; rewrite QMemory.tlin.unlock lin_gef0 tf2f_ge0P. Qed.

Lemma tlin_le (f1 f2 : 'End{T}) : '[f1;y] ⊑ '[f2;y] = (f1 ⊑ f2).
Proof. by rewrite QMemory.tlin.unlock lin_lef tf2f_lef. Qed.
Lemma tlin_lt (f1 f2 : 'End{T}) : '[f1;y] ⊏ '[f2;y] = (f1 ⊏ f2).
Proof. by rewrite QMemory.tlin.unlock lin_ltf tf2f_ltf. Qed.
Lemma tlin_ge0 (f : 'End{T}) : 0 ⊑ '[f;y] = (0%:VF ⊑ f).
Proof. by rewrite QMemory.tlin.unlock lin_gef0 tf2f_ge0. Qed.
Lemma tlin_gt0 (f : 'End{T}) : 0 ⊏ '[f;y] = (0%:VF ⊏ f).
Proof. by rewrite QMemory.tlin.unlock lin_gtf0 tf2f_gt0. Qed.
Lemma tlin_lef1 (f : 'End{T}) : '[f;y] (mset y) (mset y) ⊑ \1 = (f ⊑ \1).
Proof. by rewrite QMemory.tlin.unlock lind_id tf2f_le1. Qed.
Lemma tlin_lef1_cond S (f : 'End{T}) : 
  mset y = S -> '[f;y] S S ⊑ \1 = (f ⊑ \1).
Proof. by move=><-; exact: tlin_lef1. Qed.

End Order.

End TypedDiracTensor.
End DiracDef.

(* to be continued *)
(* inequality ??? *)

(***************************************************************************)
(* 
End tlinG.


Lemma tinnerMBT (I : finType) (P : pred I) (d : I -> qvars T) (F G : I -> 'Hs T) : 
  (forall i j : I, P i -> P j -> i != j -> [disjoint lb (d i) & lb (d j)]) ->
  (\ten_(i | P i) '<F i; d i|) ∘ (\ten_(i | P i) '|G i; d i>) 
  = (\prod_(i | P i) [<F i ; G i>])%:D.
Proof.
move=>P1; rewrite innerMBT ?index_enum_uniq=>[i j Pi Pj nij|//|].
by rewrite P1. by under eq_bigr do rewrite tv2v_dot.
Qed.

Lemma tinnerGBT (I : finType) (P : pred I) (d : I -> qvars T) (F G : I -> 'Hs T) : 
  (forall i j : I, P i -> P j -> i != j -> [disjoint lb (d i) & lb (d j)]) ->
  (\ten_(i | P i) '<F i; d i|) \· (\ten_(i | P i) '|G i; d i>) 
  = (\prod_(i | P i) [<F i ; G i>])%:D.
Proof. rewrite dotd_mul/=; exact: tinnerMBT. Qed.
End QExprExtra. *)


























(* Module Type QMemory.
Local Open Scope fnd_scope.

Parameter mlab  : finType.
Parameter msys   : mlab -> chsType.
Parameter mset  : forall T, qreg T -> {set mlab}.
Parameter tv2v  : forall T (x : qreg T), 
  {linear ('Ht T) -> 'H[msys]_(mset x)}.
Parameter tf2f : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2),
  {linear 'Hom(ihb_chsType (eval_qtype T1), ihb_chsType (eval_qtype T2)) 
          -> 'F[msys]_(mset x1, mset x2)}.

Axiom disj_setE : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2), 
  (disjoint_qreg x1 x2) = [disjoint mset x1 & mset x2].
Axiom tv2V_eqr : forall T (x y : qreg T), 
  x =r y -> forall (v : 'Ht T), tv2v x v =v tv2v y v.
Axiom tv2v_out : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2) (v1 : 'Ht T1) (v2 : 'Ht T2),
    [> tv2v x1 v1 ; tv2v x2 v2 <] = tf2f x2 x1 [> v1 ; v2 <].
Axiom tv2v_onb_t2tv : forall T (x : 'QReg[T]),
  onbasis (fun i => tv2v x (t2tv i)).
Axiom t2V_pair : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2) 
  (t1 : evalQT T1) (t2 : evalQT T2),
    ((tv2v x1 ''t1)%:Hnd ⊗v (tv2v x2 ''t2)%:Hnd)%FND = 
      (tv2v <{(x1,x2)}> (''t1 ⊗t ''t2))%:Hnd.
Axiom t2V_tuple : forall n T (x : 'I_n -> qreg T) (t : n.-tuple (evalQT T)),
  (\tenv_i (tv2v (x i) ''(t ~_ i))%:Hnd)%FND =
    (tv2v <{ tuple: x }> ''t)%:Hnd.
Axiom t2V_ffun : forall n (T : 'I_n -> qType) (x : forall i, qreg (T i)) 
  (t : {dffun forall i, eval_qtype (T i)}),
    (\tenv_i (tv2v (x i) ''(t i))%:Hnd)%FND = 
      (tv2v <{ ffun: x }> ''t)%:Hnd.

End QMemory.

Module QMemoryTheory (QMem : QMemory).
Import QMem. *)

(* Module Type DiracAlg.

Record mixin_of (F : finType) (E : vectType C) : Type := Mixin {
  (* basic operators *)
  num_proj : {additive C -> E};
  ket_proj : forall T (x : qreg T), {linear 'Ht T -> E};
  bra_proj : forall T (x : qreg T), {linear 'Ht T -> E | (conjC \; *:%R)};
  lin_proj: forall T1 T2 (x1 : qreg T1) (x2 : qreg T2),
         {linear 'Hom{T1, T2} -> E};
  dirac_mul : {bilinear E -> E -> E};
  dirac_dot : {bilinear E -> E -> E};
  dirac_ten : {bilinear E -> E -> E};
  dirac_adj : {linear E -> E | (conjC \; *:%R) };
  dirac_tr : {linear E -> E};
  dirac_conj : {linear E -> E | (conjC \; *:%R) };
  (* basic properties *)

  _ : forall a b, a *: (num_proj b) = num_proj (a * b);
  _ : (num_proj 1) != 0;
  _ : associative dirac_ten;
  _ : commutative dirac_ten;
  _ : left_id (num_proj 1) dirac_ten;
  (* _ : right_id (num_proj 1) dirac_ten; *)
  _ : associative dirac_mul;
  _ : left_id (num_proj 1) dirac_dot;
  _ : right_id (num_proj 1) dirac_dot;
  _ : dirac_conj (num_proj 1) = (num_proj 1);
  _ : involutive dirac_conj;
  _ : dirac_tr (num_proj 1) = (num_proj 1);
  _ : involutive dirac_tr;
  _ : forall A, dirac_adj A = (dirac_tr (dirac_conj A));
  _ : forall A, dirac_tr (dirac_conj A) = dirac_conj (dirac_tr A);
  _ : forall A B, dirac_conj (dirac_mul A B) = dirac_mul (dirac_conj A) (dirac_conj B);
  _ : forall A B, dirac_conj (dirac_dot A B) = dirac_dot (dirac_conj A) (dirac_conj B);
  _ : forall A B, dirac_conj (dirac_ten A B) = dirac_ten (dirac_conj A) (dirac_conj B);
  _ : forall A B, dirac_tr (dirac_mul A B) = dirac_mul (dirac_tr B) (dirac_tr A);
  _ : forall A B, dirac_tr (dirac_dot A B) = dirac_dot (dirac_tr B) (dirac_tr A);
  _ : forall A B, dirac_tr (dirac_ten A B) = dirac_ten (dirac_tr A) (dirac_tr B);

  _ : forall T (x : qreg T) (v : 'Ht T), 
      dirac_conj (ket_proj x v) = ket_proj x (v^*v);
  _ : forall T (x : qreg T) (v : 'Ht T), 
      dirac_tr (ket_proj x v) = bra_proj x (v^*v);
  _ : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2) (f : 'Hom{T1, T2}), 
      dirac_conj (lin_proj x1 x2 f) = lin_proj x1 x2 f^C;
  _ : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2) (f : 'Hom{T1, T2}), 
      dirac_tr (lin_proj x1 x2 f) = lin_proj x2 x1 f^T;
  _ : forall T (x : 'QReg[T]) (u v : 'Ht T), 
      dirac_mul (bra_proj x u) (ket_proj x v) = num_proj ([< u ; v >]);
  _ : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2) (u1 : 'Ht T1) (u2 : 'Ht T2), 
      dirac_mul (ket_proj x2 u2) (bra_proj x1 u1) = lin_proj x1 x2 [> u2; u1 <];

  (* domain information *)
  dom_proj : forall T, qreg T -> {set F};
  P_wellformed : {set F} -> {set F} -> E -> bool;
  _ : forall A1 A2 A3 A4 f, 
        P_wellformed A1 A2 f -> P_wellformed A3 A4 f -> 
          (f == 0) || ((A1 == A3) && (A2 == A4));
  _ : forall A B, P_wellformed A B 0;
  _ : forall c, P_wellformed set0 set0 (num_proj c);
  _ : forall T (x : qreg T) (v : 'Ht T), P_wellformed set0 (dom_proj x) (ket_proj x v);
  _ : forall T1 T2 (x1 : qreg T1) (x2 : qreg T2) (f : 'Hom{T1, T2}), 
        P_wellformed (dom_proj x1) (dom_proj x2) (lin_proj x1 x2 f);
  _ : forall A1 A2 A3 f g, 
        P_wellformed A2 A3 f -> P_wellformed A1 A2 g -> 
          P_wellformed A1 A3 (dirac_mul f g);
  _ : forall A1 A2 A3 A4 f g, 
        P_wellformed A1 A2 f -> P_wellformed A3 A4 g -> 
          P_wellformed (A1 :|: A3) (A2 :|: A4) (dirac_ten f g);
  _ : forall A1 A2 A3 A4 f g, 
        P_wellformed A1 A2 f -> P_wellformed A3 A4 g -> 
          P_wellformed (A3 :|: A1 :\: A4) (A2 :|: A4 :\: A1) (dirac_dot f g);
  _ : forall A1 A2 f, 
        P_wellformed A1 A2 f -> P_wellformed A2 A1 (dirac_adj f);
  _ : forall A1 A2 f, 
        P_wellformed A1 A2 f -> P_wellformed A2 A1 (dirac_tr f);
  _ : forall A1 A2 f, 
        P_wellformed A1 A2 f -> P_wellformed A1 A2 (dirac_conj f);
  _ : forall A1 A2 f1 f2,
        P_wellformed A1 A2 f1 -> P_wellformed A1 A2 f2 -> 
          P_wellformed A1 A2 (f1 + f2);
  _ : forall A1 A2 c f,
        P_wellformed A1 A2 f -> P_wellformed A1 A2 (c *: f);

Lemma dotdA_cond S1 T1 S2 T2 S3 T3 (e1: 'D[H]_(S1,T1)) (e2: 'D_(S2,T2))
  (e3: 'D_(S3,T3)) :
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  e1 \· (e2 \· e3) = e1 \· e2 \· e3.
Lemma dotd_ten S1 T1 S2 T2 (e1: 'D[H]_(S1,T1)) (e2: 'D_(S2,T2)) :
  [disjoint S1 & T2] -> 
  e1 \· e2 = e1 \⊗ e2.
Lemma dotd_mul S T W (e1: 'D[H]_(S,T)) (e2: 'D_(W,S)) :
  e1 \· e2 = e1 \o e2.
Lemma mulId S T (e : 'D[H]_(T,S)) : \1_S \o e = e.
Lemma muldI S T (e : 'D[H]_(S,T)) : e \o \1_S = e.
Lemma tend_mul S T S' T' W W' (e1: 'D[H]_(S,T)) (e2: 'D_(W,S)) 
  (e3: 'D_(S',T')) (e4: 'D_(W',S')) :
  [disjoint S & S'] ->
  (e1 \⊗ e3) \o (e2 \⊗ e4) = (e1 \o e2) \⊗ (e3 \o e4).


}. *)

(* Section seq_uniq_tac.
Context {Ts : eqType}.

Definition seq_dis_subset (s1 s2 : seq Ts) :=
  exists s1', perm_eq s1' s1 /\ subseq s1' s2.

Lemma seq_subset_cons (x : Ts) (s1 s2 : seq Ts) :
  seq_dis_subset s1 s2 -> seq_dis_subset (x :: s1) (x :: s2).
Proof.
move=>[s1' [P1 S1]]; exists (x :: s1'); split.
by rewrite perm_cons. by rewrite /= eqxx.
Qed.

Lemma seq_subset6 (s1 s2 s : seq Ts) : 
  seq_dis_subset (s2 ++ s1) s -> seq_dis_subset (s1 ++ s2) s.
Proof. 
move=>[s1' [P1 S1]]; exists s1'; split=>//.
by rewrite perm_sym perm_catC perm_sym.
Qed.

Lemma seq_subset1 (x : Ts) (s1 s2 : seq Ts) :
  seq_dis_subset s1 s2 -> seq_dis_subset s1 (x :: s2).
Proof.
move=>[s1' [P1 P2]]; exists s1'; split=>//.
by apply: (subseq_trans (subseq_cons _ x))=>/=; rewrite eqxx.
Qed.

Definition seq_subset2 (s1 s2 s : seq Ts) :=
  seq_dis_subset (s1 ++ s2) s.

Lemma seq_subset3 (s1 s2 : seq Ts) :
  seq_subset2 [::] s1 s2 -> seq_dis_subset s1 s2.
Proof. by []. Qed.

Lemma seq_subset4 (x : Ts) (s1 s2 : seq Ts) : 
  seq_subset2 [::] s1 s2 -> seq_subset2 s1 [::] (x :: s2).
Proof. by move=>P1; apply: seq_subset1; rewrite cats0. Qed.

Lemma seq_subset5 (x : Ts) (s1 s2 s: seq Ts) : 
  seq_subset2 [::] (s1 ++ s2) s -> seq_subset2 s1 (x :: s2) (x :: s).
Proof.
rewrite/seq_subset2/==>P1; apply/seq_subset6.
by rewrite cat_cons; apply/seq_subset_cons/seq_subset6.
Qed.

Lemma seq_subset7 (s : seq Ts) : seq_subset2 [::] [::] s.
Proof. exists [::]; split=>//; apply: sub0seq. Qed.

Lemma seq_subset8 (x : Ts) (s1 s2 s3 : seq Ts) : 
  seq_subset2 (x :: s1) s2 s3 -> seq_subset2 s1 (x :: s2) s3.
Proof.
move=>[s1' [P1 P2]]; exists s1'; split=>//.
by apply: (perm_trans P1); rewrite perm_sym perm_catC !cat_cons perm_cons perm_catC.
Qed.

Lemma seq_dis_subsetP (s1 s2 : seq Ts) :
  seq_subset2 [::] s2 s1 -> uniq s1 -> uniq s2.
Proof.
move=>[s1' [P1 P2]] Ps1; rewrite -(perm_uniq P1).
apply: (subseq_uniq P2 Ps1).
Qed.
End seq_uniq_tac.

Ltac seq_uniq_tac := repeat match goal with
  | [ |- qreg_expose (is_true (uniq _))] => rewrite /qreg_expose
  | [ H1 : qreg_expose (is_true (uniq _)) |- _] => rewrite /qreg_expose in H1
  | [ H : is_true (uniq _) |- is_true (uniq _) ] => move: H
  | [ |- is_true (uniq _) -> is_true (uniq _)] => apply: seq_dis_subsetP
  | [ |- seq_subset2 [::] [::] _ ] => apply/seq_subset7
  | [ |- seq_subset2 _ (?x :: _) (?x :: _)] => apply/seq_subset5=>/=
  | [ |- seq_subset2 _ [::] (_ :: _)] => apply/seq_subset4
  | [ |- seq_subset2 _ (_ :: _) _ ] => apply/seq_subset8
end.

Goal forall (a b c d e f g h i j k l m n : nat) 
  (HE : qreg_expose (uniq [:: a ; b ; c ; d ; e ; f ; g ; h ; i ; j ; k ; l ; m ; n])), 
  qreg_expose (uniq [:: g; k ; c; m]).
Proof. intros; seq_uniq_tac. Qed.

Hint Extern 0 (qreg_expose (is_true (uniq _))) => (seq_uniq_tac) : typeclass_instances.
Hint Extern 0 (qreg_expose (is_true (uniq _))) => (seq_uniq_tac) : core. *)

(* -------------------------------------------------------------------- *)
(* Commands *)

(* Context (x y z w : qvar).
Context (dis : qvar_dis [:: x; y; z; w]).
Context (xt : memctxt x (QFFun 4 QBool)).
Context (yt : memctxt y (QArray 4 (QOrd 5))).
Variable (ci : cvar_r (QType (QOrd 4))).
Check (` ci)%X.
Check <{'x}>.
Check qreg_r_cst <{'x}>.
Check qreg_r_tuplei_expr (qreg_r_cst <{'y}>) (`ci)%X.
Check qreg_r_pair_expr (qreg_r_tuplei_expr (qreg_r_cst <{'y}>) (`ci + 0%:S)%X) (qreg_r_ffuni_expr (qreg_r_cst <{'x}>) (`ci + 1%:S)%X). *)

