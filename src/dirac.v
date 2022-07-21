(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import forms spectral.
From mathcomp.analysis Require Import reals boolp.
From mathcomp.real_closed Require Import complex.

Require Import mcextra prodvect hermitian tensor lfundef setdec mxtopology.
Require Import quantum.

(************************************************************************)
(* This file provides an implementation of labelled Dirac notation      *)
(* It is defined as a non-dependent variant type 'QE of dffun.          *)
(* 'QE has linear algebraic structure (with + and scalar *:)            *)
(* implementation detail:                                               *)
(*   'QE[H] := forall i : {set L} * {set L}, 'F[H]_(i.1, i.2)           *)
(*   for any (e : 'QE) and (S,T : {set L}),                             *)
(*          e S T return the linear function 'F[H]_(S,T)                *)
(*   for any S T (f :'F[H]_(S,T)), ⌈ f ⌉ return a 'QE                   *)
(*   operations on 'QE :                                                *)
(*          construct : ket ｜〉, bra 〈｜, lin ⌈ ⌉, cplx %:QE           *)
(*                      qe2v      qe2dv     qe2f    qe2c                *)
(*          unary: adjoint `A, conjugate `C, transpose `T               *)
(*          binary: comp ∗, tensor ⊗, general comp ∘                   *)
(*   operation consistent : e.g., ⌈ f \⊗ g ⌉ = ⌈ f ⌉ ⊗ ⌈ g ⌉            *)
(*   big op :                                                          *)
(*          \comp : for comp    ∗;  Monoid: Law, MulLaw, AddLaw         *)
(*          \tens : for tensor ⊗;  Monoid: Law, MulLaw, ComLaw AddLaw  *)
(*          \dot  : for dot     ∘;  Monoid: MulLaw, AddLaw              *)
(*   trace domain/codomain :                                            *)
(*          structure : {wf S,T} : e = ⌈ f ⌉ for some f : 'F[H]_(S,T)   *)
(*          structure : {sqr S}  : e = ⌈ f ⌉ for some f : 'F[H]_S       *)
(*          structure : {ket S}  : e = ｜v〉 for some v : 'H[H]_S       *)
(*          structure : {bar S}  : e = 〈v｜ for some v : 'H[H]_S       *)
(*      canonical structure of each operations on 'QE                   *)
(*          check [sqr of e | S] : find if e is canonical to {sqr S}    *)
(*   vorder : e1 ⊑ e2 iff forall S T, 0 ⊑ (e2-e1) S S                  *)
(*                        & (e2-e1) S T = 0 if (S != T)                 *)
(*   order theory for tensor product                                    *)
(************************************************************************)

(* -------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope complex_scope.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Local Notation C := hermitian.C.

(* -------------------------------------------------------------------- *)
Import Vector.InternalTheory.

Declare Scope qexpr_scope.
Reserved Notation "''QE'" (at level 8, format "''QE'").
Reserved Notation "''QE[' H ]" (at level 8, H at level 2).
Reserved Notation "\qexpr_ ( i , j ) E" (at level 36, E at level 36, i, j at level 50,
  format "\qexpr_ ( i ,  j )  E").
(* Reserved Notation " c ￪ " (at level 8). *)
Reserved Notation " e '.dom'" (at level 2).
Reserved Notation " e '.cdom'" (at level 2).
Reserved Notation "'｜' v '〉'" (at level 10, no associativity).
Reserved Notation "'〈' v '｜'" (at level 10, no associativity).
Reserved Notation "'⌈' M '⌉'" (at level 10, no associativity).
Reserved Notation " 'I_' S " (at level 10, S at next level).
Reserved Notation " e '`C' " (at level 8).
Reserved Notation " e '`T' " (at level 8).
Reserved Notation " e '`A' " (at level 8).
(* Reserved Notation " '\tr_(' q ) e " (at level 10, q at next level).  *)
Reserved Notation "c %:QE" (at level 2, left associativity, format "c %:QE").
Reserved Notation " '∗%QE' " (at level 0).
Reserved Notation " '⊗%QE' " (at level 0).
Reserved Notation " '∘%QE' " (at level 0).
Reserved Notation " f '∗' g " (at level 40, g at next level, left associativity).
Reserved Notation " f '⊗' g " (at level 45, g at next level, left associativity).
Reserved Notation " f '∘' g " (at level 40, g at next level, left associativity).
Reserved Notation " f '⊚' g " (at level 40, g at next level, left associativity).

Reserved Notation "\comp_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \comp_ i '/  '  F ']'").
Reserved Notation "\comp_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \comp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\comp_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \comp_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\comp_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \comp_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\comp_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \comp_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\comp_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \comp_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\comp_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\comp_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\comp_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \comp_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\comp_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \comp_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\comp_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \comp_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\comp_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \comp_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\tens_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \tens_ i '/  '  F ']'").
Reserved Notation "\tens_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \tens_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\tens_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \tens_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\tens_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \tens_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\tens_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \tens_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\tens_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \tens_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\tens_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\tens_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\tens_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \tens_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\tens_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \tens_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\tens_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \tens_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\tens_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \tens_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\dot_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \dot_ i '/  '  F ']'").
Reserved Notation "\dot_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \dot_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \dot_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\dot_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \dot_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \dot_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\dot_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \dot_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\dot_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\dot_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \dot_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\dot_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \dot_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\dot_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \dot_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\dot_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \dot_ ( i  'in'  A ) '/  '  F ']'").

Section QExpr.
Section Defn.
Context {L : finType} (H : L -> chsType).

Variant qexpr := QExpr of (mvector (fun d => 'F[H]_(d.1,d.2))).

Definition qe_val u := let: QExpr t := u in t.

Canonical qexpr_subType := Eval hnf in [newType for qe_val].

Fact qexpr_key : unit. Proof. by []. Qed.
Definition qexpr_of_fun_def (F : forall (i j : {set L}), 'Hom('H_i,'H_j)) 
  := QExpr (\mvector_ ( i : {set L} * {set L} ) (F i.1 i.2)).
Definition qexpr_of_fun k := locked_with k qexpr_of_fun_def.
Canonical qexpr_unlockable k := [unlockable fun qexpr_of_fun k].

Definition fun_of_qexpr u (i : {set L}) (j : {set L}) : 'F_(i,j) := qe_val u (i,j).
Coercion fun_of_qexpr : qexpr >-> Funclass.

Lemma qexprE k F i j : qexpr_of_fun k F i j = F i j.
Proof. by rewrite unlock /fun_of_qexpr /= mvE. Qed.

Lemma qexprP (u v : qexpr) : (forall i j, u i j = v i j) <-> u = v.
Proof.
rewrite /fun_of_qexpr; split=> [/= eq_uv | -> //].
by apply/val_inj/mvectorP=> [[i j]]; apply: eq_uv.
Qed.

Lemma eq_qexpr k u v : (forall i j, u i j = v i j) ->
  qexpr_of_fun k u = qexpr_of_fun k v.
Proof. by move=> eq_uv; apply/qexprP => i j; rewrite !qexprE eq_uv. Qed.
End Defn.

Definition qexpr_eqMixin {I : finType} (E : I -> chsType) :=
  Eval hnf in [eqMixin of qexpr E by <:].
Canonical qexpr_eqType {I : finType} (E : I -> chsType) :=
  Eval hnf in EqType (qexpr E) (qexpr_eqMixin E).
Definition qexpr_choiceMixin {I : finType} (E : I -> chsType) :=
  [choiceMixin of qexpr E by <:].
Canonical qexpr_choiceType {I : finType} (E : I -> chsType) :=
  Eval hnf in ChoiceType (qexpr E) (qexpr_choiceMixin E).

End QExpr.

Delimit Scope qexpr_scope with QE.
Bind Scope qexpr_scope with qexpr.
Local Open Scope qexpr_scope.
Notation "''QE[' H ]" := (@qexpr _ H) (only parsing) : type_scope.
Notation "''QE'" := (@qexpr _ _) : type_scope.
Notation "\qexpr_ ( i , j ) E" := (qexpr_of_fun qexpr_key (fun i j => E))
  (at level 36, E at level 36, i, j at level 50): ring_scope.

Section QExprSet.
Context {L : finType} (H : L -> chsType).

Definition qeset S T (f : 'F[H]_(S,T)) : 'QE :=
  \qexpr_(i,j)
    match S =P i , T =P j return 'F[H]_(i,j) with
    | ReflectT eqi, ReflectT eqj => castlf (eqi, eqj) f
    | _, _ => 0
    end.

Lemma qesetii S T (f : 'F[H]_(S,T)) :
  qeset f S T = f.
Proof. by rewrite qexprE; (do 2 case: eqP=>//?); rewrite castlf_id. Qed.

Lemma qeset_eq0l S T S' T' (f : 'F[H]_(S,T)) :
  S' != S -> qeset f S' T' = 0.
Proof. by rewrite eq_sym qexprE; case: eqP. Qed.

Lemma qeset_eq0r S T S' T' (f : 'F[H]_(S,T)) :
  T' != T -> qeset f S' T' = 0.
Proof. by rewrite eq_sym qexprE; do 2 case: eqP=>//. Qed.

Lemma qeset_eq0p S T S' T' (f : 'F[H]_(S,T)) :
  (S',T') != (S,T) -> qeset f S' T' = 0.
Proof.
rewrite xpair_eqE negb_and=>/orP[P|P].
by rewrite qeset_eq0l. by rewrite qeset_eq0r.
Qed.

Lemma qeset_inj S T : injective (@qeset S T).
Proof. by move=>f g /qexprP=>/(_ S T); rewrite !qesetii. Qed.

Lemma qeset_cast S T S' T' (eqST: (S = S') * (T = T')) (f: 'F[H]_(S,T)) :
  qeset (castlf eqST f) = qeset f.
Proof.
by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castlf_id.
Qed. 

Lemma qeset_eqcf S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  f =c g -> qeset f = qeset g.
Proof.
by move=>P; move: P {+}P=>/cf_cond Pc/cf_cast P2; rewrite -(P2 Pc) qeset_cast.
Qed.

End QExprSet.

(* QExpr : ringType with + and tensor (!!not com)*)
(* QExpr : vectType, so we can talk about its completeness, but not used now *)
Section QExprAlgebra.
Context {L : finType} (H : L -> chsType).
Implicit Types u v w : 'QE[H].

Definition qexpr_zero     := \qexpr_(i , j) (0 : 'F[H]_(i,j)).
Definition qexpr_add  u v := \qexpr_(i , j) (u i j + v i j).
Definition qexpr_opp  u   := \qexpr_(i , j) - u i j.
Definition qexpr_scale (c : C) u := \qexpr_(i , j) (c *: u i j).

Program Canonical qexpr_zmodType := Eval hnf in ZmodType 'QE[H]
  (@GRing.Zmodule.Mixin _ qexpr_zero qexpr_opp qexpr_add _ _ _ _).
Next Obligation.
by move=> f g h; apply/qexprP=> i j; rewrite !qexprE addrA.
Qed.
Next Obligation.
by move=> f g; apply/qexprP=> i j; rewrite !qexprE addrC.
Qed.
Next Obligation.
by move=> f; apply/qexprP=> i j; rewrite !qexprE add0r.
Qed.
Next Obligation.
by move=> f; apply/qexprP=> i j; rewrite !qexprE addNr.
Qed.

Lemma qexpr_sumE T (r : seq T) (P : pred T) (F : T -> 'QE[H]) i j :
  (\sum_(x <- r | P x) F x) i j = \sum_(x <- r | P x) F x i j.
Proof. by elim/big_rec2: _ => /= [|x _ s Px <-]; rewrite qexprE. Qed.

Program Canonical qexpr_lmodType := Eval hnf in LmodType C 'QE[H]
  (@LmodMixin _ _ qexpr_scale _ _ _ _).
Next Obligation.
by move=> /= c d x; apply/qexprP=> i j; rewrite !qexprE scalerA.
Qed.
Next Obligation.
by move=> /= x; apply/qexprP=> i j; rewrite !qexprE scale1r.
Qed.
Next Obligation.
by move=> /= c u v; apply/qexprP=> i j; rewrite !qexprE scalerDr.
Qed.
Next Obligation.
by move=> /= u c d; apply/qexprP=> i j; rewrite !qexprE scalerDl.
Qed.

Lemma scalemvE (c : C) (u : forall i j, 'F[H]_(i,j)) :
  c *: \qexpr_(i,j) u i j = \qexpr_(i,j) (c *: u i j).
Proof. by apply/qexprP=> i j; rewrite !qexprE. Qed.
Lemma qexpr_mvE (u : 'QE[H]) i :
  qe_val u i = u i.1 i.2.
Proof. by rewrite /fun_of_qexpr; destruct i=>/=. Qed.

Lemma qe_val_is_linear : linear (@qe_val _ H).
Proof.
move=>a x y; apply/mvectorP=>[[i1 i2]].
by rewrite !mvE !qexpr_mvE/= !qexprE.
Qed.
Canonical qe_val_linear := Linear qe_val_is_linear.

Import Vector.InternalTheory.

Let D := (\sum_i Vector.dim [vectType C of 'F[H]_(i.1,i.2)])%N.
Lemma qexpr_vect_iso : Vector.axiom D 'QE[H].
Proof.
pose fr (f : 'QE[H]) := v2r (qe_val f).
pose gr r := QExpr (r2v r) : 'QE[H].
exists fr=> [a x y|]; first by rewrite /fr/= !linearP/=.
by exists gr=>x; rewrite /gr/fr/= ?r2vK// v2rK; destruct x.
Qed.
Definition qexpr_vectMixin := VectMixin qexpr_vect_iso.
Canonical qexpr_vectType := VectType C 'QE[H] qexpr_vectMixin.

Lemma qeset_is_linear S T : linear (@qeset _ H S T).
Proof.
move=>a x y. apply/qexprP=>i j.
rewrite !qexprE; case: eqP=>p1; first case: eqP=>p2.
by rewrite linearP. all: by rewrite scaler0 addr0.
Qed.
Canonical qeset_linear S T := Linear (@qeset_is_linear S T).

Lemma qeset_dec (f : 'QE[H]) : \sum_i qeset (f i.1 i.2) = f.
Proof.
by apply/qexprP=>i j; rewrite qexpr_sumE (bigD1 (i,j))// big1/=
  =>[[k1 k2]/= nk|]; rewrite ?addr0 ?qesetii// qeset_eq0p// eq_sym.
Qed.

Definition linqe S T (f: 'F[H]_(S,T)) : 'QE[H] := qeset f.
Definition ketqe S (v : 'H[H]_S) : 'QE[H] := linqe (v2f v).
Definition braqe S (v : 'H[H]_S) : 'QE[H] := linqe (v2df v).
(* Definition cplxqe (c : C) : 'QE[H] := (linqe (c*:\1 : 'F_set0)). *)
Definition cplxqe (c : C) : 'QE[H] := linqe (s2sf H c).
Notation qexpr1 := (cplxqe 1).
Notation qexprI S := (linqe (\1 : 'F[H]_S)).
Fact qexprII_key : unit. Proof. by []. Qed.
Definition qexprII := locked_with qexprII_key (\sum_S qeset (\1 : 'F[H]_S) : 'QE[H]).
Canonical qexprII_unlockable := [unlockable of qexprII].
Definition qe2v (S : {set L}) (e : 'QE[H]) : 'H[H]_S := f2v (e set0 S).
Definition qe2dv (S : {set L}) (e : 'QE[H]) : 'H[H]_S := df2v (e S set0).
Definition qe2f (S T : {set L}) (e : 'QE[H]) : 'F[H]_(S,T) := e S T.
Definition qe2c (e : 'QE[H]) := sf2s (e set0 set0).

Lemma linqe_dec (f : 'QE[H]) : \sum_i linqe (f i.1 i.2) = f.
Proof. by rewrite /linqe qeset_dec. Qed.

Lemma linqe_cast S T S' T' (eqST: (S = S') * (T = T')) (f: 'F[H]_(S,T)) :
  linqe (castlf eqST f) = linqe f.
Proof. by rewrite /linqe qeset_cast. Qed.

Lemma ketqe_cast S S' (eqS : S = S') (v : 'H[H]_S) :
  ketqe (casths eqS v) = ketqe v.
Proof. by case: S' / eqS; rewrite casths_id. Qed.

Lemma braqe_cast S S' (eqS : S = S') (v : 'H[H]_S) :
  braqe (casths eqS v) = braqe v.
Proof. by case: S' / eqS; rewrite casths_id. Qed.

Lemma linqe_id S T (f : 'F[H]_(S,T)) : linqe f S T = f.
Proof. by rewrite /linqe qesetii. Qed.

Lemma one1E : qexpr1 = qeset (\1 : 'F[H]_set0).
Proof. by rewrite /qexpr1 /cplxqe /linqe; f_equal; rewrite /s2sf scale1r. Qed.

Lemma one1I : qexpr1 = qexprI set0.
Proof. by rewrite one1E. Qed.

Lemma oneI1 : qexprI set0 = qexpr1.
Proof. by rewrite -one1I. Qed.

Lemma oneI1_cond S : S = set0 -> qexprI S = qexpr1.
Proof. by move=>->; rewrite oneI1. Qed.

Lemma zeorf S T : linqe (0 : 'F[H]_(S,T)) = 0.
Proof. by apply/qexprP=>i j; rewrite !qexprE; do 2 case: eqP=>//?; rewrite linear0. Qed.

Lemma zero0 : cplxqe 0 = 0.
Proof. by rewrite /cplxqe raddf0 zeorf. Qed.

Lemma zeorv S : ketqe (0 : 'H[H]_S) = 0.
Proof. by rewrite /ketqe linear0 zeorf. Qed.

Lemma zeordv S : braqe (0 : 'H[H]_S) = 0.
Proof. by rewrite /braqe linear0 zeorf. Qed.

Definition comqe (e1 e2 : 'QE[H]) :=
    \qexpr_(i , j) \sum_(k : {set L}) (e1 k j \o e2 i k : 'F[H]_(i,j)).

Fact dot_key : unit. Proof. by []. Qed.
Definition dotqe := locked_with dot_key (
  fun (e1 e2 : 'QE[H]) => \sum_d11 \sum_d12 \sum_d21 \sum_d22 
  qeset (e1 d11 d12 \⋅ e2 d21 d22) : 'QE[H]).
Canonical dotqe_unlockable := [unlockable fun dotqe].

Lemma dotq_pairE (e1 e2 : 'QE[H]) : 
  dotqe e1 e2 = \sum_d1 \sum_d2 
  qeset (e1 d1.1 d1.2 \⋅ e2 d2.1 d2.2).
Proof. by rewrite unlock pair_big; apply eq_bigr=>d1 _; rewrite pair_big. Qed.

Fact ten_key : unit. Proof. by []. Qed.
Definition tenqe := locked_with ten_key (
  fun (e1 e2 : 'QE[H]) => \sum_d11 \sum_d12 \sum_d21 \sum_d22 
    qeset (e1 d11 d12 \⊗ e2 d21 d22) : 'QE[H]).
Canonical tenqe_unlockable := [unlockable fun tenqe].

Lemma tenq_pairE (e1 e2 : 'QE[H]) : 
  tenqe e1 e2 = \sum_d1 \sum_d2 
  qeset (e1 d1.1 d1.2 \⊗ e2 d2.1 d2.2).
Proof. by rewrite unlock pair_big; apply eq_bigr=>d1 _; rewrite pair_big. Qed.

Definition conjqe (e : 'QE[H]) : 'QE[H] := 
    \qexpr_(i,j) (e i j)^C.

Definition trqe (e : 'QE[H]) : 'QE[H] := 
    \qexpr_(i,j) (e j i)^T.

Definition adjqe (e : 'QE[H]) : 'QE[H] := 
    \qexpr_(i,j) (e j i)^A.

Lemma qeset0 S T : qeset (0 : 'F[H]_(S,T)) = 0.
Proof. 
apply/qexprP=>i j; rewrite !qexprE.
do 2 case: eqP=>//?. by rewrite linear0.
Qed.

Fact tens_key : unit. Proof. by []. Qed.
Fact coms_key : unit. Proof. by []. Qed.
Fact dots_key : unit. Proof. by []. Qed.
Definition ten_lock := locked_with tens_key (@idfun 'QE[H]).
Definition com_lock := locked_with coms_key (@idfun 'QE[H]).
Definition dot_lock := locked_with dots_key (@idfun 'QE[H]).
Canonical ten_unlockable := [unlockable fun ten_lock].
Canonical com_unlockable := [unlockable fun com_lock].
Canonical dot_unlockable := [unlockable fun dot_lock].
Definition bigq := (unlock ten_unlockable, 
  unlock com_unlockable, unlock dot_unlockable). 
(* to allow the use of *)
(* Definition ten_lock (e : 'QE[H]) := e.
Definition com_lock (e : 'QE[H]) := e.
Definition dot_lock (e : 'QE[H]) := e.
Lemma bigq : (ten_lock = id) * (com_lock = id) * (dot_lock = id). 
Proof. by []. Qed. *)

End QExprAlgebra.

Notation " '|1' "     := (@cplxqe _ _ 1) : qexpr_scope.
Notation " '|I' "     := (@qexprII _ _) : qexpr_scope.
Notation "c %:QE" := (@cplxqe _ _ c) : qexpr_scope.
Notation " '｜' v 〉 "  := (@ketqe _ _ _ v) : qexpr_scope.
Notation " '〈' v ｜ "  := (@braqe _ _ _ v) : qexpr_scope.
Notation " ⌈ M ⌉ "      := (@linqe _ _ _ _ M) : qexpr_scope.
Notation " 'I_' S "     := (@linqe _ _ S S \1) : qexpr_scope.
Notation " e '`C' " := (conjqe e) : qexpr_scope.
Notation " e '`T' " := (trqe e) : qexpr_scope.
Notation " e '`A' " := (adjqe e) : qexpr_scope.
Notation " '∗%QE' "  := (comqe) : fun_scope.
Notation " '⊗%QE' " := (tenqe) : fun_scope.
Notation " '∘%QE' "  := (dotqe) : fun_scope.
Notation " f '∗' g "  := (comqe f g) : qexpr_scope.
Notation " f '⊗' g " := (tenqe f g) : qexpr_scope.
Notation " f '∘' g "  := (dotqe f g) : qexpr_scope.
Notation "\comp_ ( i <- r | P ) F" := 
  (com_lock (\big[ (@comqe _ _) / |I ]_(i <- r | P%B) F%QE )) : qexpr_scope.
Notation "\comp_ ( i <- r ) F" :=
  (com_lock (\big[ (@comqe _ _) / |I ]_(i <- r) F%QE)) : qexpr_scope.
Notation "\comp_ ( m <= i < n | P ) F" :=
  (com_lock ((\big[ (@comqe _ _) / |I ]_( m%N <= i < n%N | P%B) F%QE)%BIG)) 
    : qexpr_scope.
Notation "\comp_ ( m <= i < n ) F" :=
  (com_lock ((\big[ (@comqe _ _) / |I ]_(m%N <= i < n%N) F%QE)%BIG)) : qexpr_scope.
Notation "\comp_ ( i | P ) F" :=
  (com_lock (\big[ (@comqe _ _) / |I ]_(i | P%B) F%QE)) : qexpr_scope.
Notation "\comp_ i F" :=
  (com_lock (\big[ (@comqe _ _) / |I ]_i F%QE)) : qexpr_scope.
Notation "\comp_ ( i : t | P ) F" :=
  (com_lock (\big[ (@comqe _ _) / |I ]_(i : t | P%B) F%QE)) (only parsing) 
    : qexpr_scope.
Notation "\comp_ ( i : t ) F" :=
  (com_lock (\big[ (@comqe _ _) / |I ]_(i : t) F%QE)) (only parsing) : qexpr_scope.
Notation "\comp_ ( i < n | P ) F" :=
  (com_lock ((\big[ (@comqe _ _) / |I ]_(i < n%N | P%B) F%QE)%BIG)) : qexpr_scope.
Notation "\comp_ ( i < n ) F" :=
  (com_lock ((\big[ (@comqe _ _) / |I ]_(i < n%N) F%QE)%BIG)) : qexpr_scope.
Notation "\comp_ ( i 'in' A | P ) F" :=
  (com_lock (\big[ (@comqe _ _) / |I ]_(i in A | P%B) F%QE)) : qexpr_scope.
Notation "\comp_ ( i 'in' A ) F" :=
  (com_lock (\big[ (@comqe _ _) / |I ]_(i in A) F%QE)) : qexpr_scope.

Notation "\tens_ ( i <- r | P ) F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_(i <- r | P%B) F%QE )) : qexpr_scope.
Notation "\tens_ ( i <- r ) F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_(i <- r) F%QE)) : qexpr_scope.
Notation "\tens_ ( m <= i < n | P ) F" :=
  (ten_lock ((\big[ (@tenqe _ _) / |1 ]_( m%N <= i < n%N | P%B) F%QE)%BIG)) 
    : qexpr_scope.
Notation "\tens_ ( m <= i < n ) F" :=
  (ten_lock ((\big[ (@tenqe _ _) / |1 ]_(m%N <= i < n%N) F%QE)%BIG)) : qexpr_scope.
Notation "\tens_ ( i | P ) F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_(i | P%B) F%QE)) : qexpr_scope.
Notation "\tens_ i F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_i F%QE)) : qexpr_scope.
Notation "\tens_ ( i : t | P ) F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_(i : t | P%B) F%QE)) (only parsing) 
    : qexpr_scope.
Notation "\tens_ ( i : t ) F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_(i : t) F%QE)) (only parsing) : qexpr_scope.
Notation "\tens_ ( i < n | P ) F" :=
  (ten_lock ((\big[ (@tenqe _ _) / |1 ]_(i < n%N | P%B) F%QE)%BIG)) : qexpr_scope.
Notation "\tens_ ( i < n ) F" :=
  (ten_lock ((\big[ (@tenqe _ _) / |1 ]_(i < n%N) F%QE)%BIG)) : qexpr_scope.
Notation "\tens_ ( i 'in' A | P ) F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_(i in A | P%B) F%QE)) : qexpr_scope.
Notation "\tens_ ( i 'in' A ) F" :=
  (ten_lock (\big[ (@tenqe _ _) / |1 ]_(i in A) F%QE)) : qexpr_scope.

Notation "\dot_ ( i <- r | P ) F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_(i <- r | P%B) F%QE )) : qexpr_scope.
Notation "\dot_ ( i <- r ) F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_(i <- r) F%QE)) : qexpr_scope.
Notation "\dot_ ( m <= i < n | P ) F" :=
  (dot_lock ((\big[ (@dotqe _ _) / |1 ]_( m%N <= i < n%N | P%B) F%QE)%BIG)) 
    : qexpr_scope.
Notation "\dot_ ( m <= i < n ) F" :=
  (dot_lock ((\big[ (@dotqe _ _) / |1 ]_(m%N <= i < n%N) F%QE)%BIG)) : qexpr_scope.
Notation "\dot_ ( i | P ) F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_(i | P%B) F%QE)) : qexpr_scope.
Notation "\dot_ i F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_i F%QE)) : qexpr_scope.
Notation "\dot_ ( i : t | P ) F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_(i : t | P%B) F%QE)) (only parsing) 
    : qexpr_scope.
Notation "\dot_ ( i : t ) F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_(i : t) F%QE)) (only parsing) : qexpr_scope.
Notation "\dot_ ( i < n | P ) F" :=
  (dot_lock ((\big[ (@dotqe _ _) / |1 ]_(i < n%N | P%B) F%QE)%BIG)) : qexpr_scope.
Notation "\dot_ ( i < n ) F" :=
  (dot_lock ((\big[ (@dotqe _ _) / |1 ]_(i < n%N) F%QE)%BIG)) : qexpr_scope.
Notation "\dot_ ( i 'in' A | P ) F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_(i in A | P%B) F%QE)) : qexpr_scope.
Notation "\dot_ ( i 'in' A ) F" :=
  (dot_lock (\big[ (@dotqe _ _) / |1 ]_(i in A) F%QE)) : qexpr_scope.

Section QExprBigLock.
Context {L : finType} (H : L -> chsType).

Lemma ten_locklr (I J : Type) (ri : seq I) (Pi : pred I) (Fi : I -> 'QE[H]) 
(rj : seq J) (Pj : pred J) (Fj : J -> 'QE[H]): 
ten_lock (tenqe (\big[⊗%QE (H:=H)/|1]_(i <- ri | Pi i) Fi i) 
(\big[⊗%QE (H:=H)/|1]_(j <- rj | Pj j) Fj j)) = 
(\tens_(i <- ri | Pi i) Fi i) ⊗ (\tens_(j <- rj | Pj j) Fj j) .
Proof. by rewrite bigq. Qed.

Lemma ten_lockr (I : Type) (r : seq I) (P : pred I) (e1 : 'QE[H]) (F : I -> 'QE[H]): 
ten_lock (tenqe e1 (\big[⊗%QE (H:=H)/|1]_(j <- r | P j) F j)) = tenqe e1 (\tens_(i <- r | P i) F i).
Proof. by rewrite bigq. Qed.

Lemma ten_lockl (I : Type) (r : seq I) (P : pred I) (e1 : 'QE[H]) (F : I -> 'QE[H]): 
ten_lock (tenqe (\big[⊗%QE (H:=H)/|1]_(j <- r | P j) F j) e1) = tenqe (\tens_(i <- r | P i) F i) e1.
Proof. by rewrite bigq. Qed.

Lemma com_locklr (I J : Type) (ri : seq I) (Pi : pred I) (Fi : I -> 'QE[H]) 
(rj : seq J) (Pj : pred J) (Fj : J -> 'QE[H]): 
com_lock (comqe (\big[∗%QE (H:=H)/|I]_(i <- ri | Pi i) Fi i) 
(\big[∗%QE (H:=H)/|I]_(j <- rj | Pj j) Fj j)) = 
(\comp_(i <- ri | Pi i) Fi i) ∗ (\comp_(j <- rj | Pj j) Fj j) .
Proof. by rewrite bigq. Qed.

Lemma com_lockr (I : Type) (r : seq I) (P : pred I) (e1 : 'QE[H]) (F : I -> 'QE[H]): 
com_lock (comqe e1 (\big[∗%QE (H:=H)/|I]_(j <- r | P j) F j)) = comqe e1 (\comp_(i <- r | P i) F i).
Proof. by rewrite bigq. Qed.

Lemma com_lockl (I : Type) (r : seq I) (P : pred I) (e1 : 'QE[H]) (F : I -> 'QE[H]): 
com_lock (comqe (\big[∗%QE (H:=H)/|I]_(j <- r | P j) F j) e1) = comqe (\comp_(i <- r | P i) F i) e1.
Proof. by rewrite bigq. Qed.

Lemma dot_locklr (I J : Type) (ri : seq I) (Pi : pred I) (Fi : I -> 'QE[H]) 
(rj : seq J) (Pj : pred J) (Fj : J -> 'QE[H]): 
dot_lock (dotqe (\big[∘%QE (H:=H)/|1]_(i <- ri | Pi i) Fi i) 
(\big[∘%QE (H:=H)/|1]_(j <- rj | Pj j) Fj j)) = 
(\dot_(i <- ri | Pi i) Fi i) ∘ (\dot_(j <- rj | Pj j) Fj j) .
Proof. by rewrite bigq. Qed.

Lemma dot_lockr (I : Type) (r : seq I) (P : pred I) (e1 : 'QE[H]) (F : I -> 'QE[H]): 
dot_lock (dotqe e1 (\big[∘%QE (H:=H)/|1]_(j <- r | P j) F j)) = dotqe e1 (\dot_(i <- r | P i) F i).
Proof. by rewrite bigq. Qed.

Lemma dot_lockl (I : Type) (r : seq I) (P : pred I) (e1 : 'QE[H]) (F : I -> 'QE[H]): 
dot_lock (dotqe (\big[∘%QE (H:=H)/|1]_(j <- r | P j) F j) e1) = dotqe (\dot_(i <- r | P i) F i) e1.
Proof. by rewrite bigq. Qed.

Lemma ten_lockE (I : Type) (r : seq I) (P : pred I) (F : I -> 'QE[H]): 
\big[⊗%QE (H:=H)/|1]_(j <- r | P j) F j = \tens_(i <- r | P i) F i.
Proof. by rewrite bigq. Qed.

Lemma com_lockE (I : Type) (r : seq I) (P : pred I) (F : I -> 'QE[H]): 
\big[∗%QE (H:=H)/|I]_(j <- r | P j) F j = \comp_(i <- r | P i) F i.
Proof. by rewrite bigq. Qed.

Lemma dot_lockE (I : Type) (r : seq I) (P : pred I) (F : I -> 'QE[H]): 
\big[∘%QE (H:=H)/|1]_(j <- r | P j) F j = \dot_(i <- r | P i) F i.
Proof. by rewrite bigq. Qed.

Definition bigq_lock := (ten_lockE, com_lockE, dot_lockE).

Definition bigqE := (ten_locklr, ten_lockr, ten_lockl, com_locklr, com_lockr,
  com_lockl, dot_locklr, dot_lockr, dot_lockl).
End QExprBigLock.

(* after using bigop theory, first run this to lock back *)
(* Ltac bigqE := rewrite ?bigq; rewrite ?bigq_locklr. *)

Lemma exchange_bigR (R : Type) (idx : R) (op : Monoid.com_law idx) 
(I J K : Type) (rI : seq I) (rJ : seq J) (rK : seq K) (P : pred I) 
(Q : pred J) (S : pred K) (F : I -> J -> K -> R) : 
\big[op/idx]_(i <- rI | P i) \big[op/idx]_(j <- rJ | Q j) 
    \big[op/idx]_(k <- rK | S k) F i j k = \big[op/idx]_(j <- rJ | Q j) 
        \big[op/idx]_(k <- rK | S k) \big[op/idx]_(i <- rI | P i) F i j k.
Proof.
rewrite exchange_big. apply eq_bigr=>i Pi. apply exchange_big.
Qed.

Section QExprOpCorrect.
Context {L : finType} (H : L -> chsType).

Lemma linqeK S T : cancel (@linqe _ H S T) (@qe2f _ H S T).
Proof. by move=>f; rewrite /qe2f /linqe qesetii. Qed.
Lemma linqe_inj S T : injective (@linqe _ H S T).
Proof. exact: (can_inj (@linqeK S T)). Qed.
Lemma ketqeK S : cancel (@ketqe _ H S) (@qe2v _ H S).
Proof. by move=>f; rewrite /ketqe /qe2v qesetii v2fK. Qed.
Lemma ketqe_inj S : injective (@ketqe _ H S).
Proof. exact: (can_inj (@ketqeK S)). Qed.
Lemma braqeK S : cancel (@braqe _ H S) (@qe2dv _ H S).
Proof. by move=>f; rewrite /braqe /qe2dv qesetii v2dfK. Qed.
Lemma braqe_inj S : injective (@braqe _ H S).
Proof. exact: (can_inj (@braqeK S)). Qed.
Lemma cplxqeK : cancel (@cplxqe _ H) (@qe2c _ H).
Proof. by move=>f; rewrite /cplxqe /qe2c qesetii s2sfK. Qed.
Lemma cplxqe_inj : injective (@cplxqe _ H).
Proof. exact: (can_inj (@cplxqeK)). Qed.

Lemma linqe_is_linear S T : linear (@linqe _ H S T).
Proof. by move=>a x y; rewrite /linqe linearP. Qed.
Canonical linqe_linear S T := Linear (@linqe_is_linear S T).

Lemma ketqe_is_linear S : linear (@ketqe _ H S).
Proof. by move=>a x y; rewrite /ketqe !linearP. Qed.
Canonical ketqe_linear S := Linear (@ketqe_is_linear S).

Lemma braqe_is_antilinear S : linear_for (conjC \; *:%R) (@braqe _ H S).
Proof. by move=>a x y; rewrite /braqe !linearP. Qed.
Canonical braqe_antilinear S := Linear (@braqe_is_antilinear S).

Lemma cplxqe_is_additive : additive (@cplxqe _ H).
Proof. by move=>x y; rewrite /cplxqe raddfB linearB. Qed.
Canonical cplxqe_additive := Additive cplxqe_is_additive.

Lemma qe2f_is_linear S T : linear (@qe2f _ H S T).
Proof. by move=>a x y; rewrite /qe2f !qexprE. Qed.
Canonical qe2f_linear S T := Linear (@qe2f_is_linear S T).

Lemma qe2v_is_linear S : linear (@qe2v _ H S).
Proof. by move=>a x y; rewrite /qe2v !qexprE linearP. Qed.
Canonical qe2v_linear S := Linear (@qe2v_is_linear S).

Lemma qe2dv_is_antilinear S : linear_for (conjC \; *:%R) (@qe2dv _ H S).
Proof. by move=>a x y; rewrite /qe2dv !qexprE linearP. Qed.
Canonical qe2dv_antilinear S := Linear (@qe2dv_is_antilinear S).

Lemma qe2c_is_scalar : scalar (@qe2c _ H).
Proof. by move=>a x y; rewrite /qe2c !qexprE linearP. Qed.
Canonical qe2c_scalar := Linear (@qe2c_is_scalar).

(* correctness of compoistion operators *)
Lemma addqe_correct S T (f g: 'F[H]_(S,T)) :
  linqe (f + g) = linqe f + linqe g.
Proof. exact: linearD. Qed.

Lemma oppqe_correct S T (f : 'F[H]_(S,T)) : 
  linqe (- f) = - (linqe f).
Proof. exact: linearN. Qed.

Lemma scaleqe_correct S T (c: C) (f : 'F[H]_(S,T)) :
  linqe (c *: f) = c *: (linqe f).
Proof. exact: linearZ. Qed.

Lemma comqe_correct S T W (f: 'F[H]_(S,T)) (g: 'F[H]_(W,S)) :
    linqe (f \o g) = (linqe f) ∗ (linqe g).
Proof.
apply/qexprP=>d1 d2. rewrite [RHS]qexprE.
rewrite (bigD1 S)//= big1=>[i P|].
by rewrite qeset_eq0l ?comp_lfun0l.
case E: (d1 == W); last by rewrite qeset_eq0l 
  ?[X in _ \o X]qeset_eq0l ?E// comp_lfun0r addr0.
case E1: (d2 == T); last by rewrite qeset_eq0r 
  ?[X in X \o _]qeset_eq0r ?E1// comp_lfun0l addr0.
move: E E1=>/eqP->/eqP->; by rewrite !qesetii addr0.
Qed.

Lemma tenqe_correct S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S', T')) :
    linqe (f \⊗ g) = (linqe f) ⊗ (linqe g).
Proof.
apply/qexprP=>d1 d2; rewrite tenq_pairE.
rewrite (bigD1 (S,T))//= (bigD1 (S',T'))//= !big1=>[[i1 i2]/=P|[i1 i2]/=P|]. 
by rewrite [X in _ \⊗ X]qeset_eq0p// tenf0 linear0.
by rewrite big1=>[j _|]; rewrite 1?qeset_eq0p// ?ten0f ?linear0// qexprE.
by rewrite !addr0 !qesetii.
Qed.

Lemma dotqe_correct S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S', T')) :
    linqe (f \⋅ g) = (linqe f) ∘ (linqe g).
Proof.
apply/qexprP=>d1 d2; rewrite dotq_pairE. 
rewrite (bigD1 (S,T))//= (bigD1 (S',T'))//= !big1=>[[i1 i2]/=P|[i1 i2]/=P|]. 
by rewrite [X in _ \⋅ X]qeset_eq0p// dotf0 linear0.
by rewrite big1=>[j _|]; rewrite 1?qeset_eq0p// ?dot0f ?linear0// qexprE.
by rewrite !addr0 !qesetii.
Qed.

Lemma sdot_correct S T (f: 'F[H]_S) (g: 'F[H]_T) :
  linqe (f \O g) = linqe f ∘ linqe g.
Proof. by rewrite /sdot_lfun linqe_cast dotqe_correct. Qed.

Lemma conjqe_correct S T (f : 'F[H]_(S,T)) :
  linqe (f^C) = (linqe f)`C.
Proof.
apply/qexprP=>i j. rewrite [RHS]qexprE.
case E: ((i,j) == (S,T)). by move/eqP in E; inversion E; rewrite !qesetii.
by move/negbT: E=>E; rewrite !qeset_eq0p// linear0.
Qed.

Lemma adjqe_correct S T (f : 'F[H]_(S,T)) :
  linqe (f^A) = (linqe f)`A.
Proof.
apply/qexprP=>i j. rewrite [RHS]qexprE.
case E: ((i,j) == (T,S)). by move/eqP in E; inversion E; rewrite !qesetii.
move/negbT: E=>E; rewrite !qeset_eq0p// ?linear0//.
by move: E; apply contraNN=>/eqP P; inversion P.
Qed.

Lemma trqe_correct S T (f : 'F[H]_(S,T)) :
  linqe (f^T) = (linqe f)`T.
Proof.
apply/qexprP=>i j. rewrite [RHS]qexprE.
case E: ((i,j) == (T,S)). by move/eqP in E; inversion E; rewrite !qesetii.
move/negbT: E=>E; rewrite !qeset_eq0p// ?linear0//.
by move: E; apply contraNN=>/eqP P; inversion P.
Qed.

End QExprOpCorrect.

(* we locally use ringType (+ , ⊗) to ease the proof of theorems *)
Section QExprTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (e x y z: 'QE[H]) (a b c : C).
Local Notation "c %:QE" := (@cplxqe _ H c) (only parsing).
Local Notation "⊗%QE" := (@tenqe _ H) (only parsing).
Local Notation "∗%QE"  := (@comqe _ H) (only parsing).
Local Notation "∘%QE" := (@dotqe _ H) (only parsing).
Notation conjqe := (@conjqe _ H) (only parsing).
Notation trqe := (@trqe _ H) (only parsing).
Notation adjqe := (@adjqe _ H) (only parsing).

Lemma tenqA : associative ⊗%QE.
Proof.
move=>f g h; rewrite !tenq_pairE [RHS]exchange_big/=.
rewrite  (eq_bigr (fun d1 => \sum_d0 \sum_d3 \sum_d2
 qeset (f d1.1 d1.2 \⊗ (qeset (g d0.1 d0.2 \⊗ h d3.1 d3.2) d2.1 d2.2)))).
2: rewrite  [RHS](eq_bigr (fun j => \sum_d1 \sum_d2 \sum_i
(qeset (qeset (f d1.1 d1.2 \⊗ g d2.1 d2.2) i.1 i.2 \⊗ h j.1 j.2)))).
1,2: by move=>i _; rewrite exchange_bigR/= exchange_bigR/=; apply eq_bigr=>j _;
rewrite qexpr_sumE 1 ?linear_suml/= 2 ?linear_sum/=; apply eq_bigr=>k _;
rewrite qexpr_sumE 1 ?linear_suml/= 2 ?linear_sum/=; apply eq_bigr.
rewrite [RHS]exchange_bigR/=; apply eq_bigr=>[[i1 i2]] _; 
apply eq_bigr=>[[j1 j2]] _; apply eq_bigr=>[[k1 k2]] _.
rewrite (bigD1 (j1 :|: k1, j2 :|: k2))// big1/=.
2: rewrite (bigD1 (i1 :|: j1, i2 :|: j2))// big1/=.
1,2 : by move=>[l1 l2]/=nl; rewrite qeset_eq0p// ?tenf0 ?ten0f linear0.
by rewrite !qesetii !addr0; apply/qeset_eqcf; rewrite tenfA.
Qed.

Lemma tenqC : commutative ⊗%QE.
Proof.
move=>f g. rewrite 2 !tenq_pairE exchange_big/=.
apply eq_bigr=>[[i1 i2]] _; apply eq_bigr=>[[j1 j2]] _/=.
by apply/qeset_eqcf; rewrite tenfC.
Qed.

Lemma ten1q : left_id |1 ⊗%QE.
Proof.
move=>f. rewrite tenq_pairE (bigD1 (set0,set0))// big1/=.
move=>[i1 i2]/= ni0. rewrite big1// =>? _/=.
by rewrite qeset_eq0p// ten0f linear0.
rewrite addr0 -[RHS]qeset_dec; apply eq_bigr=>i _.
by rewrite one1E qesetii; apply/qeset_eqcf; rewrite tenf1l. 
Qed.

Lemma tenq1 : right_id |1 ⊗%QE.
Proof. by move=>f; rewrite tenqC ten1q. Qed.

Lemma linear_tenq f : linear (⊗%QE f).
Proof. 
move=>a v w. rewrite !tenq_pairE linear_sum -big_split/=; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !qexprE !linearP/=.
Qed.
Canonical tenq_additive f := Additive (@linear_tenq f).
Canonical tenq_linear f := Linear (@linear_tenq f).
Definition tenqr f := (⊗%QE)^~ f.
Lemma linear_tenqr f : linear (@tenqr f).
Proof.
move=>a v w. rewrite /tenqr !tenq_pairE linear_sum -big_split; 
apply eq_bigr=>i _/=; rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !qexprE linearPl linearP/=.
Qed.
Canonical tenqr_additive f := Additive (@linear_tenqr f).
Canonical tenqr_linear f := Linear (@linear_tenqr f).
Canonical tenq_rev := [revop (@tenqr) of (⊗%QE)].
Canonical tenq_is_bilinear := [bilinear of (⊗%QE)].

Lemma tenqAC x y z : x ⊗ y ⊗ z = x ⊗ z ⊗ y.
Proof. by rewrite -tenqA [y ⊗ z]tenqC tenqA. Qed.
Lemma tenqCA x y z : x ⊗ (y ⊗ z) = y ⊗ (x ⊗ z).
Proof. by rewrite tenqC tenqAC -tenqA. Qed.
Lemma tenqACA x y z t : x ⊗ y ⊗ (z ⊗ t) = x ⊗ z ⊗ (y ⊗ t).
Proof. by rewrite -!tenqA (tenqCA y). Qed.

Lemma ten0q : left_zero 0 ⊗%QE. Proof. exact: linear0l. Qed.
Lemma tenq0 : right_zero 0 ⊗%QE. Proof. exact: linear0r. Qed.
Lemma tenqDl : left_distributive ⊗%QE +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma tenqDr : right_distributive ⊗%QE +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma tenqN x y : x ⊗ (- y) = - (x ⊗ y). Proof. exact: raddfN. Qed.
Lemma tenqN1 x : x ⊗ -|1 = - x. Proof. by rewrite tenqN tenq1. Qed.
Lemma tenqBr z : {morph ⊗%QE z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma tenqMnr z n : {morph ⊗%QE z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition tenqnAr := tenqMnr.
Lemma tenqMNnr z n : {morph ⊗%QE z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma tenq_sumr z I r (P : pred I) E :
  z ⊗ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z ⊗ E i).
Proof. exact: raddf_sum. Qed.
Lemma tenqZr z a : {morph ⊗%QE z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma tenqPr z a : {morph ⊗%QE z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma tenNq x y : (- x) ⊗ y = - (x ⊗ y). Proof. exact: linearNl. Qed.
Lemma tenN1q x : -|1 ⊗ x = - x. Proof. by rewrite tenNq ten1q. Qed.
Lemma tenqNN x y : (- x) ⊗ (- y) = x ⊗ y. Proof. by rewrite tenqN tenNq opprK. Qed.
Lemma tenqBl z : {morph ⊗%QE^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma tenqMnl z n : {morph ⊗%QE^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition tenqnAl := tenqMnl.
Lemma tenqMNnl z n : {morph ⊗%QE^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma tenq_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) ⊗ z = \sum_(i <- r | P i) (E i ⊗ z).
Proof. exact: linear_suml. Qed.
Lemma tenqZl z a : {morph ⊗%QE^~ z : x / a *: x}. Proof. exact: linearZl. Qed.
Lemma tenqPl z a : {morph ⊗%QE^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma tenqZlr x y a b : (a *: x) ⊗ (b *: y) = a *: (b *: (x ⊗ y)). 
Proof. exact: linearZlr. Qed.
Lemma tenqZrl x y a b : (a *: x) ⊗ (b *: y) = b *: (a *: (x ⊗ y)). 
Proof. exact: linearZrl. Qed.

Lemma oneq_neq0 : (|1 : 'QE[H]) != 0.
Proof.
apply/eqP=> /qexprP/(_ set0 set0)/eqP.
by rewrite one1E qesetii qexprE oner_eq0.
Qed.

Definition tenq_comRingMixin :=
  ComRingMixin tenqA tenqC ten1q tenqDl oneq_neq0.
Definition tenq_ringType := RingType 'QE[H] tenq_comRingMixin.

Lemma comqA : associative ∗%QE.
Proof.
move=>x y z. rewrite /comqe.
apply/qexprP=>i j. rewrite !qexprE.
under eq_bigr do rewrite !qexprE linear_sumr/=.
rewrite exchange_big/=. apply eq_bigr=>k _.
rewrite qexprE/= linear_suml/=. 
by under eq_bigr do rewrite comp_lfunA.
Qed.

Lemma qexprII_id i : |I i i = (\1 : 'F[H]_i).
Proof.
by rewrite unlock qexpr_sumE (bigD1 i)// big1/==>[j nj|];
  rewrite ?addr0 ?qesetii// qeset_eq0l// eq_sym.
Qed. 

Lemma qexprII_eq0 i j : i != j -> |I i j = (0 : 'F[H]_(i,j)).
Proof.
move=>nij; rewrite unlock qexpr_sumE (bigD1 i)// big1/=.
by move=> k nki; rewrite qeset_eq0l// eq_sym.
by rewrite addr0 qeset_eq0r// eq_sym.
Qed.

Lemma comIIq : left_id |I ∗%QE.
Proof. 
move=> f; rewrite /comqe; apply/qexprP=>i j.
rewrite !qexprE (bigD1 j)// big1/=.
by move=> k nki; rewrite qexprII_eq0// comp_lfun0l.
by rewrite addr0 qexprII_id comp_lfun1l.
Qed.

Lemma comqII : right_id |I ∗%QE.
Proof.
move=> f; rewrite /comqe; apply/qexprP=>i j.
rewrite !qexprE (bigD1 i)// big1/=.
by move=> k nki; rewrite qexprII_eq0// ?comp_lfun0r// eq_sym.
by rewrite addr0 qexprII_id comp_lfun1r.
Qed.

Lemma linear_comq f : linear (∗%QE f).
Proof. 
move=>a v w; apply/qexprP=>i j.
rewrite !qexprE !linear_sum/= -big_split; apply eq_bigr=>k _/=.
by rewrite !qexprE linearPr/=.
Qed.
Canonical comq_additive f := Additive (@linear_comq f).
Canonical comq_linear f := Linear (@linear_comq f).
Definition comqr f := (∗%QE)^~ f.
Lemma linear_comqr f : linear (@comqr f).
Proof.
move=>a v w; apply/qexprP=>i j.
rewrite !qexprE !linear_sum/= -big_split; apply eq_bigr=>k _/=.
by rewrite !qexprE linearPl/=.
Qed.
Canonical comqr_additive f := Additive (@linear_comqr f).
Canonical comqr_linear f := Linear (@linear_comqr f).
Canonical comq_rev := [revop (@comqr) of ∗%QE].
Canonical comq_is_bilinear := [bilinear of ∗%QE].

Lemma com0q : left_zero 0 ∗%QE. Proof. exact: linear0l. Qed.
Lemma comq0 : right_zero 0 ∗%QE. Proof. exact: linear0r. Qed.
Lemma comqDl : left_distributive ∗%QE +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma comqDr : right_distributive ∗%QE +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma comqN x y : x ∗ (- y) = - (x ∗ y). Proof. exact: raddfN. Qed.
Lemma comqNII x : x ∗ -|I = - x. Proof. by rewrite comqN comqII. Qed.
Lemma comqBr z : {morph ∗%QE z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma comqMnr z n : {morph ∗%QE z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition comqnAr := comqMnr.
Lemma comqMNnr z n : {morph ∗%QE z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma comq_sumr z I r (P : pred I) E :
  z ∗ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z ∗ E i).
Proof. exact: raddf_sum. Qed.
Lemma comqZr z a : {morph ∗%QE z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma comqPr z a : {morph ∗%QE z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma comNq x y : (- x) ∗ y = - (x ∗ y). Proof. exact: linearNl. Qed.
Lemma comNIIq x : -|I ∗ x = - x. Proof. by rewrite comNq comIIq. Qed.
Lemma comqNN x y : (- x) ∗ (- y) = x ∗ y. Proof. by rewrite comqN comNq opprK. Qed.
Lemma comqBl z : {morph ∗%QE^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma comqMnl z n : {morph ∗%QE^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition comqnAl := comqMnl.
Lemma comqMNnl z n : {morph ∗%QE^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma comq_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) ∗ z = \sum_(i <- r | P i) (E i ∗ z).
Proof. exact: linear_suml. Qed.
Lemma comqZl z a : {morph ∗%QE^~ z : x / a *: x}. Proof. exact: linearZl. Qed.
Lemma comqPl z a : {morph ∗%QE^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma comqZlr x y a b : (a *: x) ∗ (b *: y) = a *: (b *: (x ∗ y)). 
Proof. exact: linearZlr. Qed.
Lemma comqZrl x y a b : (a *: x) ∗ (b *: y) = b *: (a *: (x ∗ y)). 
Proof. exact: linearZrl. Qed.

Lemma II_neq0 : |I != 0 :> 'QE[H].
Proof.
apply/eqP=> /qexprP/(_ set0 set0)/eqP.
rewrite unlock qexpr_sumE !qexprE (bigD1 set0)// big1/=.
by move=>i /negPf ni0; rewrite qeset_eq0l// eq_sym ni0.
by rewrite qesetii addr0 oner_eq0.
Qed.

Definition comq_ringMixin :=
  RingMixin comqA comIIq comqII comqDl comqDr II_neq0.
Definition comq_ringType := Eval hnf in RingType 'QE[H] comq_ringMixin.

Lemma dot1q : left_id |1 ∘%QE.
Proof.
move=>f; rewrite dotq_pairE (bigD1 (set0,set0))// big1/==>[[i1 i2] ni0|].
by rewrite big1// =>j _; rewrite /= qeset_eq0p// dot0f linear0.
rewrite addr0 -[RHS]qeset_dec; apply eq_bigr=>[[i1 i2]] _/=.
by apply/qeset_eqcf; rewrite one1E qesetii dotf1l.
Qed.

Lemma dotq1 : right_id |1 ∘%QE.
Proof.
move=>f; rewrite dotq_pairE exchange_big (bigD1 (set0,set0))//= 
  [X in _ + X]big1/==>[[i1 i2] ni0|].
by rewrite big1// =>j _; rewrite /= qeset_eq0p// dotf0 linear0.
rewrite addr0 -[RHS]qeset_dec; apply eq_bigr=>[[i1 i2]] _/=.
by apply/qeset_eqcf; rewrite one1E qesetii dotf1r.
Qed.

Lemma linear_dotq f : linear (∘%QE f).
Proof. 
move=>a v w; rewrite !dotq_pairE linear_sum -big_split; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !qexprE !linearP/=.
Qed.
Canonical dotq_additive f := Additive (@linear_dotq f).
Canonical dotq_linear f := Linear (@linear_dotq f).
Definition dotqr f := (∘%QE)^~ f.
Lemma linear_dotqr f : linear (@dotqr f).
Proof.
move=>a v w; rewrite /dotqr !dotq_pairE linear_sum -big_split; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !qexprE !(linearP,linearPl)/=.
Qed.
Canonical dotqr_additive f := Additive (@linear_dotqr f).
Canonical dotqr_linear f := Linear (@linear_dotqr f).
Canonical dotq_rev := [revop (@dotqr) of ∘%QE].
Canonical dotq_is_bilinear := [bilinear of ∘%QE].

Lemma dot0q : left_zero 0 ∘%QE. Proof. exact: linear0l. Qed.
Lemma dotq0 : right_zero 0 ∘%QE. Proof. exact: linear0r. Qed.
Lemma dotqDl : left_distributive ∘%QE +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma dotqDr : right_distributive ∘%QE +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma dotqN x y : x ∘ (- y) = - (x ∘ y). Proof. exact: raddfN. Qed.
Lemma dotqN1 x : x ∘ -|1 = - x. Proof. by rewrite dotqN dotq1. Qed.
Lemma dotqBr z : {morph ∘%QE z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma dotqMnr z n : {morph ∘%QE z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition dotqnAr := dotqMnr.
Lemma dotqMNnr z n : {morph ∘%QE z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma dotq_sumr z I r (P : pred I) E :
  z ∘ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z ∘ E i).
Proof. exact: raddf_sum. Qed.
Lemma dotqZr z a : {morph ∘%QE z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma dotqPr z a : {morph ∘%QE z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma dotNq x y : (- x) ∘ y = - (x ∘ y). Proof. exact: linearNl. Qed.
Lemma dotN1q x : -|1 ∘ x = - x. Proof. by rewrite dotNq dot1q. Qed.
Lemma dotqNN x y : (- x) ∘ (- y) = x ∘ y. Proof. by rewrite dotqN dotNq opprK. Qed.
Lemma dotqBl z : {morph ∘%QE^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma dotqMnl z n : {morph ∘%QE^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition dotqnAl := dotqMnl.
Lemma dotqMNnl z n : {morph ∘%QE^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma dotq_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) ∘ z = \sum_(i <- r | P i) (E i ∘ z).
Proof. exact: linear_suml. Qed.
Lemma dotqZl z a : {morph ∘%QE^~ z : x / a *: x}. Proof. exact: linearZl. Qed.
Lemma dotqPl z a : {morph ∘%QE^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma dotqZlr x y a b : (a *: x) ∘ (b *: y) = a *: (b *: (x ∘ y)). 
Proof. exact: linearZlr. Qed.
Lemma dotqZrl x y a b : (a *: x) ∘ (b *: y) = b *: (a *: (x ∘ y)). 
Proof. exact: linearZrl. Qed.

Lemma conjqe_is_antilinear : linear_for (conjC \; *:%R) conjqe.
Proof. by move=>a x y/=; apply/qexprP=>i j; rewrite !qexprE linearP. Qed.
Canonical conjqe_antilinear := Linear conjqe_is_antilinear.
Lemma adjqe_is_antilinear  : linear_for (conjC \; *:%R) adjqe.
Proof. by move=>a x y/=; apply/qexprP=>i j; rewrite !qexprE linearP. Qed.
Canonical adjqe_antilinear := Linear adjqe_is_antilinear.
Lemma trqe_is_linear  : linear trqe.
Proof. by move=>a x y/=; apply/qexprP=>i j; rewrite !qexprE linearP. Qed.
Canonical trqe_linear := Linear trqe_is_linear.

Lemma conjq0 : 0`C = (0 : 'QE[H]). Proof. exact: linear0. Qed.
Lemma conjqN : {morph conjqe : x / - x}. Proof. exact: linearN. Qed.
Lemma conjqD : {morph conjqe : x y / x + y}. Proof. exact: linearD. Qed.
Lemma conjqB : {morph conjqe : x y / x - y}. Proof. exact: linearB. Qed.
Lemma conjqMn n : {morph conjqe : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma conjqMNn n : {morph conjqe : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma conjq_sum I r (P : pred I) (E : I -> 'QE[H]) :
  (\sum_(i <- r | P i) E i)`C = \sum_(i <- r | P i) (E i)`C.
Proof. exact: linear_sum. Qed.
Lemma conjqZ a : {morph conjqe : x / a *: x >-> a^* *: x}. Proof. exact: linearZ. Qed.
Lemma conjqP a : {morph conjqe : x y / a *: x + y >-> a^* *: x + y}.
Proof. exact: linearP. Qed.
Lemma conjqI S : (I_ S : 'QE[H])`C = I_ S.
Proof. by rewrite -conjqe_correct conjf1. Qed.
Lemma conjq1 : |1`C = (|1 : 'QE[H]).
Proof. by rewrite -conjqe_correct s2sf_conj conjC1. Qed.
Lemma conjqN1 : (-|1)`C = (-|1 : 'QE[H]).
Proof. by rewrite conjqN conjq1. Qed.
Lemma conjqK : involutive conjqe.
Proof. by move=>x; apply/qexprP=>i j; rewrite !qexprE conjfK. Qed.
Lemma conjq_inj : injective conjqe.
Proof. exact: (can_inj conjqK). Qed.
Lemma conjqM e1 e2 : (e1 ∗ e2)`C = e1`C ∗ e2`C.
Proof.
apply/qexprP=>i j. rewrite !qexprE linear_sum/=.
by apply eq_bigr=>s _; rewrite conjf_comp !qexprE.
Qed.
Lemma conjqT e1 e2 : (e1 ⊗ e2)`C = e1`C ⊗ e2`C.
Proof.
rewrite -(linqe_dec e1) -(linqe_dec e2) tenq_suml !conjq_sum tenq_suml.
apply eq_bigr=>??; rewrite !tenq_sumr conjq_sum; apply eq_bigr=>??. 
by rewrite -tenqe_correct -!conjqe_correct -tenqe_correct tenf_conj.
Qed.
Lemma conjqG e1 e2 : (e1 ∘ e2)`C = e1`C ∘ e2`C.
Proof.
rewrite -(linqe_dec e1) -(linqe_dec e2) dotq_suml !conjq_sum dotq_suml.
apply eq_bigr=>??; rewrite !dotq_sumr conjq_sum; apply eq_bigr=>??. 
by rewrite -dotqe_correct -!conjqe_correct -dotqe_correct dotf_conj.
Qed.
Lemma conjq_lin S T (f : 'F[H]_(S,T)) : (linqe f)`C = linqe f^C.
Proof. by rewrite conjqe_correct. Qed.
Lemma conjq_ket S (v : 'H[H]_S) : (ketqe v)`C = ketqe v^*v.
Proof. by rewrite /ketqe conjq_lin v2f_conj. Qed.
Lemma conjq_bra S (v : 'H[H]_S) : (braqe v)`C = braqe v^*v.
Proof. by rewrite /braqe conjq_lin v2df_conj. Qed.
Lemma conjq_scale c : c%:QE`C = c^*%:QE.
Proof. by rewrite /cplxqe conjq_lin s2sf_conj. Qed.

Lemma adjq0 : 0`A = (0 : 'QE[H]). Proof. exact: linear0. Qed.
Lemma adjqN : {morph adjqe : x / - x}. Proof. exact: linearN. Qed.
Lemma adjqD : {morph adjqe : x y / x + y}. Proof. exact: linearD. Qed.
Lemma adjqB : {morph adjqe : x y / x - y}. Proof. exact: linearB. Qed.
Lemma adjqMn n : {morph adjqe : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma adjqMNn n : {morph adjqe : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma adjq_sum I r (P : pred I) (E : I -> 'QE[H]) :
  (\sum_(i <- r | P i) E i)`A = \sum_(i <- r | P i) (E i)`A.
Proof. exact: linear_sum. Qed.
Lemma adjqZ a : {morph adjqe : x / a *: x >-> a^* *: x}. Proof. exact: linearZ. Qed.
Lemma adjqP a : {morph adjqe : x y / a *: x + y >-> a^* *: x + y}.
Proof. exact: linearP. Qed.
Lemma adjqI S : (I_ S : 'QE[H])`A = I_ S.
Proof. by rewrite -adjqe_correct adjf1. Qed.
Lemma adjq1 : |1`A = (|1 : 'QE[H]).
Proof. by rewrite -adjqe_correct s2sf_adj conjC1. Qed.
Lemma adjqN1 : (-|1)`A = (-|1 : 'QE[H]).
Proof. by rewrite adjqN adjq1. Qed.
Lemma adjqK : involutive adjqe.
Proof. by move=>x; apply/qexprP=>i j; rewrite !qexprE adjfK. Qed.
Lemma adjq_inj : injective adjqe.
Proof. exact: (can_inj adjqK). Qed.
Lemma adjqM e1 e2 : (e1 ∗ e2)`A = e2`A ∗ e1`A.
Proof.
apply/qexprP=>i j. rewrite !qexprE linear_sum/=.
by apply eq_bigr=>s _; rewrite adjf_comp !qexprE.
Qed.
Lemma adjqT e1 e2 : (e1 ⊗ e2)`A = e1`A ⊗ e2`A.
Proof.
rewrite -(linqe_dec e1) -(linqe_dec e2) tenq_suml !adjq_sum tenq_suml.
apply eq_bigr=>??; rewrite !tenq_sumr adjq_sum; apply eq_bigr=>??. 
by rewrite -tenqe_correct -!adjqe_correct -tenqe_correct tenf_adj.
Qed.
Lemma adjqG e1 e2 : (e1 ∘ e2)`A = e2`A ∘ e1`A.
Proof.
rewrite -(linqe_dec e1) -(linqe_dec e2) dotq_suml !adjq_sum dotq_sumr.
apply eq_bigr=>??; rewrite dotq_sumr dotq_suml adjq_sum; apply eq_bigr=>??.
by rewrite -dotqe_correct -!adjqe_correct -dotqe_correct dotf_adj.
Qed.
Lemma adjq_lin S T (f : 'F[H]_(S,T)) : (linqe f)`A = linqe f^A.
Proof. by rewrite adjqe_correct. Qed.
Lemma adjq_ket S (v : 'H[H]_S) : (ketqe v)`A = braqe v.
Proof. by rewrite /ketqe adjq_lin v2f_adj. Qed.
Lemma adjq_bra S (v : 'H[H]_S) : (braqe v)`A = ketqe v.
Proof. by rewrite /braqe adjq_lin v2df_adj. Qed.
Lemma adjq_scale c : c%:QE`A = c^*%:QE.
Proof. by rewrite /cplxqe adjq_lin s2sf_adj. Qed.

Lemma trqAC e : e`T = e`A`C.
Proof. by apply/qexprP=>i j; rewrite !qexprE trfAC. Qed.
Lemma trq0 : 0`T = (0 : 'QE[H]). Proof. exact: linear0. Qed.
Lemma trqN : {morph trqe : x / - x}. Proof. exact: linearN. Qed.
Lemma trqD : {morph trqe : x y / x + y}. Proof. exact: linearD. Qed.
Lemma trqB : {morph trqe : x y / x - y}. Proof. exact: linearB. Qed.
Lemma trqMn n : {morph trqe : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma trqMNn n : {morph trqe : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma trq_sum I r (P : pred I) (E : I -> 'QE[H]) :
  (\sum_(i <- r | P i) E i)`T = \sum_(i <- r | P i) (E i)`T.
Proof. exact: linear_sum. Qed.
Lemma trqZ a : {morph trqe : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma trqP a : {morph trqe : x y / a *: x + y}. Proof. exact: linearP. Qed.
Lemma trqI S : (I_ S : 'QE[H])`T = I_ S.
Proof. by rewrite -trqe_correct trf1. Qed.
Lemma trq1 : |1`T = (|1 : 'QE[H]).
Proof. by rewrite -trqe_correct s2sf_tr. Qed.
Lemma trqN1 : (-|1)`T = (-|1 : 'QE[H]).
Proof. by rewrite trqN trq1. Qed.
Lemma trqK : involutive trqe.
Proof. by move=>x; apply/qexprP=>i j; rewrite !qexprE trfK. Qed.  
Lemma trq_inj : injective trqe.
Proof. exact: (can_inj trqK). Qed.
Lemma trqM e1 e2 : (e1 ∗ e2)`T = e2`T ∗ e1`T.
Proof. by rewrite !trqAC adjqM conjqM. Qed.
Lemma trqT e1 e2 : (e1 ⊗ e2)`T = e1`T ⊗ e2`T.
Proof. by rewrite !trqAC adjqT conjqT. Qed.
Lemma trqG e1 e2 : (e1 ∘ e2)`T = e2`T ∘ e1`T.
Proof. by rewrite !trqAC adjqG conjqG. Qed.
Lemma trq_lin S T (f : 'F[H]_(S,T)) : (linqe f)`T = linqe f^T.
Proof. by rewrite trqe_correct. Qed.
Lemma trq_ket S (v : 'H[H]_S) : (ketqe v)`T = braqe v^*v.
Proof. by rewrite /ketqe trq_lin v2f_tr. Qed.
Lemma trq_bra S (v : 'H[H]_S) : (braqe v)`T = ketqe v^*v.
Proof. by rewrite /braqe trq_lin v2df_tr. Qed.
Lemma trq_scale c : c%:QE`T = c%:QE.
Proof. by rewrite /cplxqe trq_lin s2sf_tr. Qed.

Lemma qACC e : e`A`C = e`C`A.
Proof. by apply/qexprP=>i j; rewrite !qexprE lfACC. Qed.
Lemma trqCA   e : e`T = e`C`A. Proof. by rewrite trqAC qACC. Qed.
Lemma conjqAT e : e`C = e`A`T. Proof. by rewrite trqAC adjqK. Qed.
Lemma conjqTA e : e`C = e`T`A. Proof. by rewrite trqCA adjqK. Qed.
Lemma adjqTC  e : e`A = e`T`C. Proof. by rewrite trqAC conjqK. Qed.
Lemma adjqCT  e : e`A = e`C`T. Proof. by rewrite trqCA conjqK. Qed.
Definition qT2AC := trqAC.
Definition qT2CA := trqCA.
Definition qC2AT := conjqAT.
Definition qC2TA := conjqTA.
Definition qA2TC := adjqTC.
Definition qA2CT := adjqCT.
Lemma qCAC e : e`C`A = e`A`C. Proof. by rewrite qACC. Qed.
Lemma qATC e : e`A`T = e`T`A. Proof. by rewrite -qC2AT qC2TA. Qed.
Lemma qTAC e : e`T`A = e`A`T. Proof. by rewrite qATC. Qed.
Lemma qTCC e : e`T`C = e`C`T. Proof. by rewrite -qA2TC qA2CT. Qed.
Lemma qCTC e : e`C`T = e`T`C. Proof. by rewrite qTCC. Qed.

(* recommend: write from cplx -> c *)
Lemma cplx0 : 0%:QE = 0. Proof. exact: raddf0. Qed.
Lemma cplxI : (I_ set0 : 'QE[H]) = |1. Proof. by rewrite one1I. Qed.
Lemma cplxN a : -a%:QE = (-a)%:QE. Proof. by rewrite raddfN. Qed.
Lemma cplxD a b : a%:QE + b%:QE = (a+b)%:QE. Proof. by rewrite raddfD. Qed.
Lemma cplxB a b : a%:QE - b%:QE = (a-b)%:QE. Proof. by rewrite raddfB. Qed.
Lemma cplxMn n a : a%:QE*+n = (a*+n)%:QE. Proof. by rewrite raddfMn. Qed.
Lemma cplxMNn n a : a%:QE*-n = (a*-n)%:QE. Proof. by rewrite raddfMNn. Qed.
Lemma cplx_sum I r (P : pred I) (E : I -> C) :
  \sum_(i <- r | P i) (E i)%:QE = (\sum_(i <- r | P i) E i)%:QE.
Proof. by rewrite raddf_sum. Qed.
Lemma cplxZ a b : a*:b%:QE = (a*b)%:QE.
Proof. by rewrite -linearZ/= /s2sf scalerA. Qed.
Lemma cplxZ1 a : a%:QE = a *: |1. Proof. by rewrite cplxZ mulr1. Qed.
Lemma cplxP a b c : a*:b%:QE + c%:QE= (a*b+c)%:QE.
Proof. by rewrite cplxZ cplxD. Qed.
Lemma cplxTl x a : a%:QE ⊗ x = a *: x. 
Proof. by rewrite cplxZ1 tenqZl ten1q. Qed.
Lemma cplxTr x a : x ⊗ a%:QE = a *: x. 
Proof. by rewrite tenqC cplxTl. Qed.
Lemma cplxT a b : a%:QE ⊗ b%:QE = (a*b)%:QE. 
Proof. by rewrite cplxTl cplxZ. Qed.
Lemma cplxM a b : a%:QE ∗ b%:QE = (a*b)%:QE. 
Proof. by rewrite -comqe_correct /s2sf -comp_lfunZl -comp_lfunZr scalerA comp_lfun1r. Qed.
Lemma cplxGl x a : a%:QE ∘ x = a *: x. 
Proof. by rewrite cplxZ1 dotqZl dot1q. Qed.
Lemma cplxGr x a : x ∘ a%:QE = a *: x. 
Proof. by rewrite cplxZ1 dotqZr dotq1. Qed.
Lemma cplxG a b : a%:QE ∘ b%:QE = (a*b)%:QE. 
Proof. by rewrite cplxGl cplxZ. Qed.
Definition cplx_adj := adjq_scale.

Definition cplx_linear := (cplx0, cplxI, cplxN, cplxD, cplxB, cplxMn, cplxMNn, cplx_sum, cplxZ, cplxP).
Definition cplx_simp := (adjq_scale, conjq_scale, trq_scale, cplxTl, cplxTr, cplxT, cplxM, cplxGl, cplxGr, cplxG).

End QExprTheory.

Section QExprBig.
Context {L : finType} (H : L -> chsType).
(* since generally we need to import GRing.Theory, *)
(* canonical of addoid here will be ignored, so we reclaim distribution lemmas *)
Canonical  comq_monoid := Monoid.Law (@comqA _ H) (@comIIq _ H) (@comqII _ H).
Canonical  comq_muloid := Monoid.MulLaw (@com0q _ H) (@comq0 _ H).
Definition comq_addoid := Monoid.AddLaw (@comqDl _ H) (@comqDr _ H).
Canonical  tenq_monoid := Monoid.Law (@tenqA _ H) (@ten1q _ H) (@tenq1 _ H).
Canonical  tenq_muloid := Monoid.MulLaw (@ten0q _ H) (@tenq0 _ H).
Canonical  tenq_comoid := Monoid.ComLaw (@tenqC _ H).
Definition tenq_addoid := Monoid.AddLaw (@tenqDl _ H) (@tenqDr _ H).
Canonical  dotq_muloid := Monoid.MulLaw (@dot0q _ H) (@dotq0 _ H).
Definition dotq_addoid := Monoid.AddLaw (@dotqDl _ H) (@dotqDr _ H).

Lemma tensumE : (+%R : 'QE[H] -> 'QE[H] -> 'QE[H]) = tenq_addoid. by []. Qed.
Lemma comsumE : (+%R : 'QE[H] -> 'QE[H] -> 'QE[H]) = comq_addoid. by []. Qed.
Lemma dotsumE : (+%R : 'QE[H] -> 'QE[H] -> 'QE[H]) = dotq_addoid. by []. Qed.

Lemma ket_sum I (r : seq I) (P : pred I) S (F : I -> 'H[H]_S) :
  \sum_(i <- r | P i) (ketqe (F i)) = ketqe (\sum_(i <- r | P i) (F i)).
Proof. by rewrite linear_sum/=. Qed.

Lemma bra_sum I (r : seq I) (P : pred I) S (F : I -> 'H[H]_S) :
  \sum_(i <- r | P i) (braqe (F i)) = braqe (\sum_(i <- r | P i) (F i)).
Proof. by rewrite linear_sum/=. Qed.

Lemma lin_sum I (r : seq I) (P : pred I) S T (F : I -> 'F[H]_(S,T)) :
  \sum_(i <- r | P i) (linqe (F i)) = linqe (\sum_(i <- r | P i) (F i)).
Proof. by rewrite linear_sum/=. Qed.

(*distribution lemmas *)
Lemma tenq_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'QE[H]) (G : J -> 'QE[H]) :
  (\sum_(i <- rI | pI i) F i) ⊗ (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i ⊗ G j).
Proof. rewrite !tensumE; apply: big_distrlr. Qed.

Lemma tenq_distr_sum_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) 
  (F : I -> J -> 'QE[H]) :
  (\tens_(i | P i) \sum_(j | Q i j) F i j) =
     \sum_(f in pfamily j0 P Q) \tens_(i | P i) F i (f i).
Proof. rewrite tensumE bigq; apply: big_distr_big_dep. Qed.

Lemma tenq_distr_sum (I J : finType) j0 (P : pred I) (Q : pred J) 
  (F : I -> J -> 'QE[H]) :
  (\tens_(i | P i) \sum_(j | Q j) F i j) =
     \sum_(f in pffun_on j0 P Q) \tens_(i | P i) F i (f i).
Proof. by rewrite tensumE bigq; apply: big_distr_big. Qed.

Lemma tenqA_distr_sum_dep (I J : finType) (Q : I -> pred J) 
  (F : I -> J -> 'QE[H]) :
  (\tens_i \sum_(j | Q i j) F i j)
    = \sum_(f in family Q) \tens_i F i (f i).
Proof. by rewrite tensumE bigq; apply: bigA_distr_big_dep. Qed.

Lemma tenqA_distr_sum (I J : finType) (Q : pred J) (F : I -> J -> 'QE[H]) :
  (\tens_i \sum_(j | Q j) F i j)
    = \sum_(f in ffun_on Q) \tens_i F i (f i).
Proof. exact: tenqA_distr_sum_dep. Qed.

Lemma tenqA_distr_sumA (I J : finType) (F : I -> J -> 'QE[H]) :
  (\tens_(i : I) \sum_(j : J) F i j)
    = \sum_(f : {ffun I -> J}) \tens_i F i (f i).
Proof. by rewrite tensumE bigq; apply: bigA_distr_bigA. Qed.

(*distribution lemmas *)
Lemma comq_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'QE[H]) (G : J -> 'QE[H]) :
  (\sum_(i <- rI | pI i) F i) ∗ (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i ∗ G j).
Proof. rewrite !comsumE; apply: big_distrlr. Qed.

Lemma comq_distr_sum_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) 
  (F : I -> J -> 'QE[H]) :
  (\comp_(i | P i) \sum_(j | Q i j) F i j) =
     \sum_(f in pfamily j0 P Q) \comp_(i | P i) F i (f i).
Proof. by rewrite comsumE bigq; apply: big_distr_big_dep. Qed.

Lemma comq_distr_sum (I J : finType) j0 (P : pred I) (Q : pred J) 
  (F : I -> J -> 'QE[H]) :
  (\comp_(i | P i) \sum_(j | Q j) F i j) =
     \sum_(f in pffun_on j0 P Q) \comp_(i | P i) F i (f i).
Proof. by rewrite comsumE bigq; apply: big_distr_big. Qed.

Lemma comqA_distr_sum_dep (I J : finType) (Q : I -> pred J) 
  (F : I -> J -> 'QE[H]) :
  (\comp_i \sum_(j | Q i j) F i j)
    = \sum_(f in family Q) \comp_i F i (f i).
Proof. by rewrite comsumE bigq; apply: bigA_distr_big_dep. Qed.

Lemma comqA_distr_sum (I J : finType) (Q : pred J) (F : I -> J -> 'QE[H]) :
  (\comp_i \sum_(j | Q j) F i j)
    = \sum_(f in ffun_on Q) \comp_i F i (f i).
Proof. exact: comqA_distr_sum_dep. Qed.

Lemma comqA_distr_sumA (I J : finType) (F : I -> J -> 'QE[H]) :
  (\comp_(i : I) \sum_(j : J) F i j)
    = \sum_(f : {ffun I -> J}) \comp_i F i (f i).
Proof. by rewrite comsumE bigq; apply: bigA_distr_bigA. Qed.

Lemma dotq_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'QE[H]) (G : J -> 'QE[H]) :
  (\sum_(i <- rI | pI i) F i) ∘ (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i ∘ G j).
Proof. rewrite !dotsumE; apply: big_distrlr. Qed.

Lemma dotq_distr_sum_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) 
  (F : I -> J -> 'QE[H]) :
  (\dot_(i | P i) \sum_(j | Q i j) F i j) =
     \sum_(f in pfamily j0 P Q) \dot_(i | P i) F i (f i).
Proof. by rewrite dotsumE bigq; apply: big_distr_big_dep. Qed.

Lemma dotq_distr_sum (I J : finType) j0 (P : pred I) (Q : pred J) 
  (F : I -> J -> 'QE[H]) :
  (\dot_(i | P i) \sum_(j | Q j) F i j) =
     \sum_(f in pffun_on j0 P Q) \dot_(i | P i) F i (f i).
Proof. by rewrite dotsumE bigq; apply: big_distr_big. Qed.

Lemma dotqA_distr_sum_dep (I J : finType) (Q : I -> pred J) 
  (F : I -> J -> 'QE[H]) :
  (\dot_i \sum_(j | Q i j) F i j)
    = \sum_(f in family Q) \dot_i F i (f i).
Proof. by rewrite dotsumE bigq; apply: bigA_distr_big_dep. Qed.

Lemma dotqA_distr_sum (I J : finType) (Q : pred J) (F : I -> J -> 'QE[H]) :
  (\dot_i \sum_(j | Q j) F i j)
    = \sum_(f in ffun_on Q) \dot_i F i (f i).
Proof. exact: dotqA_distr_sum_dep. Qed.

Lemma dotqA_distr_sumA (I J : finType) (F : I -> J -> 'QE[H]) :
  (\dot_(i : I) \sum_(j : J) F i j)
    = \sum_(f : {ffun I -> J}) \dot_i F i (f i).
Proof. by rewrite dotsumE bigq; apply: bigA_distr_bigA. Qed.

(* add dffun for big distr *)
Lemma tenqA_distr_big_dffun (I : finType) (J : forall i : I, finType)
  (PJ : forall i : I, pred (J i)) (F : forall i : I, J i -> 'QE[H]) :
  (\tens_(i : I) \sum_(j : J i| PJ i j) F i j)
    = \sum_(f : {dffun forall i : I, J i} | 
        family_mem (fun i : I => Mem (PJ i)) f) \tens_i F i (f i).
Proof. rewrite tensumE bigq; apply: big_distr_big_dffun. Qed.

Lemma tenqA_distr_dffun (I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> 'QE[H]) :
  (\tens_(i : I) \sum_(j : J i) F i j)
    = \sum_(f : {dffun forall i : I, J i}) \tens_i F i (f i).
Proof. rewrite tensumE bigq; apply: big_distr_dffun. Qed.

Lemma comqA_distr_big_dffun (I : finType) (J : forall i : I, finType)
  (PJ : forall i : I, pred (J i)) (F : forall i : I, J i -> 'QE[H]) :
  (\comp_(i : I) \sum_(j : J i| PJ i j) F i j)
    = \sum_(f : {dffun forall i : I, J i} | 
        family_mem (fun i : I => Mem (PJ i)) f) \comp_i F i (f i).
Proof. rewrite comsumE bigq; apply: big_distr_big_dffun. Qed.

Lemma comqA_distr_dffun (I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> 'QE[H]) :
  (\comp_(i : I) \sum_(j : J i) F i j)
    = \sum_(f : {dffun forall i : I, J i}) \comp_i F i (f i).
Proof. rewrite comsumE bigq; apply: big_distr_dffun. Qed.

Lemma dotqA_distr_big_dffun (I : finType) (J : forall i : I, finType)
  (PJ : forall i : I, pred (J i)) (F : forall i : I, J i -> 'QE[H]) :
  (\dot_(i : I) \sum_(j : J i| PJ i j) F i j)
    = \sum_(f : {dffun forall i : I, J i} | 
        family_mem (fun i : I => Mem (PJ i)) f) \dot_i F i (f i).
Proof. rewrite dotsumE bigq; apply: big_distr_big_dffun. Qed.

Lemma dotqA_distr_dffun (I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> 'QE[H]) :
  (\dot_(i : I) \sum_(j : J i) F i j)
    = \sum_(f : {dffun forall i : I, J i}) \dot_i F i (f i).
Proof. rewrite dotsumE bigq; apply: big_distr_dffun. Qed.

End QExprBig.

(* conditioned theory, require extra domain conditions *)
(* This section is used for Canonical Structure of qexpr *)
(* for example, we can canonical ketqe to ketexpre and wfqexpr *)
(* and in the theory, we may set up a lemma (e : wfqexpr) : P e *)
(* the for ketqe v, we can directly apply the lemma without proving qewf *)
Module WFQE.

Section ClassDef.
Context (L : finType) (H : L -> chsType).

Definition qewf_of S T (f : 'QE[H]) := (f = linqe (f S T)).
Notation qesqr S f := (qewf_of S S f).
Notation qeket S f := (qewf_of set0 S f).
Notation qebra S f := (qewf_of S set0 f).

Structure wfqexpr S T := WFQExpr {
  wfqe_base : 'QE[H];
  _ : qewf_of S T wfqe_base;
}.
Local Coercion wfqe_base : wfqexpr >-> qexpr.

Structure sqrqexpr S := SqrQExpr {
  sqrqe_base : 'QE[H];
  _ : qesqr S sqrqe_base;
}.
Local Coercion sqrqe_base : sqrqexpr >-> qexpr.
Lemma sqrqexpr_wf_subproof S (e : sqrqexpr S) : 
  qewf_of S S (sqrqe_base e).
Proof. by destruct e. Qed.
Definition sqrqexpr_wf S (e : sqrqexpr S) := WFQExpr (sqrqexpr_wf_subproof e).

Structure ketqexpr S := KetQExpr {
  ketqe_base : 'QE[H];
  _ : qeket S ketqe_base;
}.
Local Coercion ketqe_base : ketqexpr >-> qexpr.
Lemma ketqexpr_wf_subproof S (e : ketqexpr S) : 
  qewf_of set0 S (ketqe_base e).
Proof. by destruct e. Qed.
Definition ketqexpr_wf S (e : ketqexpr S) := WFQExpr (ketqexpr_wf_subproof e).

Structure braqexpr S := BraQExpr {
  braqe_base : 'QE[H];
  _ : qebra S braqe_base;
}.
Local Coercion braqe_base : braqexpr >-> qexpr.
Lemma braqexpr_wf_subproof S (e : braqexpr S) : 
  qewf_of S set0 (braqe_base e).
Proof. by destruct e. Qed.
Definition braqexpr_wf S (e : braqexpr S) := WFQExpr (braqexpr_wf_subproof e).

Let ex_id (e1 e2 : 'QE[H]) := phant_id e1 e2.
Definition clone_wfqexpr S T e :=
  fun (opL : wfqexpr S T) & ex_id opL e =>
  fun ewf (opL' := @WFQExpr S T e ewf)
    & phant_id opL' opL => opL'.

Definition clone_sqrqexpr S e :=
  fun (opL : sqrqexpr S) & ex_id opL e =>
  fun esqr (opL' := @SqrQExpr S e esqr)
    & phant_id opL' opL => opL'.

Definition clone_ketqexpr S e :=
  fun (opL : ketqexpr S) & ex_id opL e =>
  fun eket (opL' := @KetQExpr S e eket)
    & phant_id opL' opL => opL'.

Definition clone_braqexpr S e :=
  fun (opL : braqexpr S) & ex_id opL e =>
  fun ebra (opL' := @BraQExpr S e ebra)
    & phant_id opL' opL => opL'.

End ClassDef.

Module Import Exports.
Coercion wfqe_base  : wfqexpr >-> qexpr.
Coercion sqrqe_base : sqrqexpr >-> qexpr.
Coercion ketqe_base : ketqexpr >-> qexpr.
Coercion braqe_base : braqexpr >-> qexpr.
Canonical sqrqexpr_wf.
Canonical ketqexpr_wf.
Canonical braqexpr_wf.
Definition qewf_of := qewf_of.
Notation qewf S T f := (@qewf_of _ _ S T f).
Notation qesqr S f := (@qewf_of _ _ S S f).
Notation qeket S f := (@qewf_of _ _ set0 S f).
Notation qebra S f := (@qewf_of _ _ S set0 f).
Notation WFQExpr fL := (WFQExpr fL).
Notation SqrQExpr fL := (SqrQExpr fL).
Notation KetQExpr fL := (KetQExpr fL).
Notation BraQExpr fL := (BraQExpr fL).
Notation "{ 'wf' H | S , T }" := (@wfqexpr _ H S T)
  (at level 0, only parsing) : qexpr_scope.
Notation "{ 'wf' S , T }" := (@wfqexpr _ _ S T)
  (at level 0, format "{ 'wf'  S  ,  T }") : qexpr_scope.
Notation "{ 'sqr' H | S }" := (@sqrqexpr _ H S)
  (at level 0, only parsing) : qexpr_scope.
Notation "{ 'sqr' S }" := (@sqrqexpr _ _ S)
  (at level 0, format "{ 'sqr'  S }") : qexpr_scope.
Notation "{ 'ket' H | S }" := (@ketqexpr _ H S)
  (at level 0, only parsing) : qexpr_scope.
Notation "{ 'ket' S }" := (@ketqexpr _ _ S)
  (at level 0, format "{ 'ket'  S }") : qexpr_scope.
Notation "{ 'bra' H | S }" := (@braqexpr _ H S)
  (at level 0, only parsing) : qexpr_scope.
Notation "{ 'bra' S }" := (@braqexpr _ _ S)
  (at level 0, format "{ 'bra'  S }") : qexpr_scope.
Notation "[ 'wf' 'of' e | S , T ]" := (@clone_wfqexpr _ _ S T e _ id _ id)
  (at level 0, format "[ 'wf'  'of'  e  |  S  ,  T ]") : form_scope.
Notation "[ 'wf' 'of' e ]" := (@clone_wfqexpr _ _ _ _ e _ id _ id)
  (at level 0, format "[ 'wf'  'of'  e ]") : form_scope.
Notation "[ 'sqr' 'of' e | S ]" := (@clone_sqrqexpr _ _ S e _ id _ id)
  (at level 0, format "[ 'sqr'  'of'  e  |  S ]") : form_scope.
Notation "[ 'sqr' 'of' e ]" := (@clone_sqrqexpr _ _ _ e _ id _ id)
  (at level 0, format "[ 'sqr'  'of'  e ]") : form_scope.
Notation "[ 'ket' 'of' e | S ]" := (@clone_ketqexpr _ _ S e _ id _ id)
  (at level 0, format "[ 'ket'  'of'  e  |  S ]") : form_scope.
Notation "[ 'ket' 'of' e ]" := (@clone_ketqexpr _ _ _ e _ id _ id)
  (at level 0, format "[ 'ket'  'of'  e ]") : form_scope.
Notation "[ 'bra' 'of' e | S ]" := (@clone_braqexpr _ _ S e _ id _ id)
  (at level 0, format "[ 'bra'  'of'  e  | S ]") : form_scope.
Notation "[ 'bra' 'of' e ]" := (@clone_braqexpr _ _ _ e _ id _ id)
  (at level 0, format "[ 'bra'  'of'  e ]") : form_scope.

End Exports.

End WFQE.
Include WFQE.Exports.

(* although it's possible to use only wfqexpr and regard sqr ket bra
as special cases, but then in many cases, canonical of a operator will
be ignored and not able to work for all cases 
For example, we might canonical dotqe of two sqaure expr as sqaure
then if we want canonical dotqe of ket and bra with same S, then 
we will get warning "canonical ignored". *)
(* these structures allow to do some calculations similar to dependent type *)
Section WFQETheory.
Context (L : finType) (H : L -> chsType).

Lemma qewfP S T (e : 'QE[H]) : @qewf_of _ H S T e <-> e = linqe (e S T).
Proof. by rewrite /qewf_of/WFQE.qewf_of. Qed.

Lemma wf_linE S T (e : {wf H | S , T}) : e = linqe (e S T) :> 'QE.
Proof. by case: e. Qed.
Lemma sqr_linE S (e : {sqr H | S}) : e = linqe (e S S) :> 'QE.
Proof. by case: e. Qed.
Lemma qe2vK S (e : {ket H | S}) : ketqe (qe2v S e) = e.
Proof. by case: e=>[v P]; rewrite /=/ketqe f2vK. Qed.
Lemma qe2dvK S (e : {bra H | S}) : braqe (qe2dv S e) = e.
Proof. by case: e=>[v P]; rewrite /=/braqe df2vK. Qed.

Lemma wfP S T (e : {wf H | S , T}) : qewf S T e. Proof. by case: e. Qed.
Lemma sqrP S (e : {sqr H | S}) : qesqr S e. Proof. by case: e. Qed.
Lemma ketP S (e : {ket H | S}) : qeket S e. Proof. by case: e. Qed.
Lemma braP S (e : {bra H | S}) : qebra S e. Proof. by case: e. Qed.

Lemma wfP_eq S T S' T' (e : {wf H | S , T}) : S = S' -> T = T' -> qewf S' T' e.
Proof. by move=><-<-; apply wfP. Qed.
Lemma sqrP_eq S S' (e : {sqr H | S}) : S = S' -> qesqr S' e.
Proof. by move=><-; apply sqrP. Qed.
Lemma ketP_eq S S' (e : {ket H | S}) : S = S' -> qeket S' e.
Proof. by move=><-; apply ketP. Qed.
Lemma braP_eq S S' (e : {bra H | S}) : S = S' -> qebra S' e.
Proof. by move=><-; apply braP. Qed.

Lemma wfE S T (e : 'QE[H]) (P : qewf S T e) : e = WFQExpr P. Proof. by []. Qed.
Lemma sqrE S (e : 'QE[H]) (P : qesqr S e) : e = SqrQExpr P. Proof. by []. Qed.
Lemma ketE S (e : 'QE[H]) (P : qeket S e) : e = KetQExpr P. Proof. by []. Qed.
Lemma braE S (e : 'QE[H]) (P : qebra S e) : e = BraQExpr P. Proof. by []. Qed.

Lemma wf_eqD S T S' T' (e1 : {wf H | S , T}) (e2 : {wf S',T'}) :
  (e1 : 'QE) = e2 -> ((S == S') && (T == T')) || ((e1 : 'QE) == 0).
Proof.
move=>P; case: eqP; case: eqP=>//= /eqP P1 /eqP P2.
all:apply/eqP/qexprP=>i j; rewrite (wf_linE) !qexprE; case: eqP=>//; 
  case: eqP=>// P3 P4; rewrite P (wf_linE) /linqe.
1,3: by rewrite qeset_eq0r// linear0.
by rewrite qeset_eq0l// linear0.
Qed.

Lemma sqr_eqD S T (e1 : {sqr H | S}) (e2 : {sqr T}) :
  (e1 : 'QE) = e2 -> (S == T) || ((e1 : 'QE) == 0).
Proof. by move/wf_eqD=>/orP[/andP[->]//|->]; rewrite orbT. Qed.

Lemma ket_eqD S T (e1 : {ket H | S}) (e2 : {ket T}) :
  (e1 : 'QE) = e2 -> (S == T) || ((e1 : 'QE) == 0).
Proof. by move/wf_eqD=>/orP[/andP[_ ->]//|->]; rewrite orbT. Qed.

Lemma bra_eqD S T (e1 : {bra H | S}) (e2 : {bra T}) :
  (e1 : 'QE) = e2 -> (S == T) || ((e1 : 'QE) == 0).
Proof. by move/wf_eqD=>/orP[/andP[->]//|->]; rewrite orbT. Qed.

Lemma wf_eq S T (e1 e2 : {wf S,T}) : (e1 : 'QE[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2]=>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma sqr_eq S (e1 e2 : {sqr S}) : (e1 : 'QE[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2]=>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma ket_eq S (e1 e2 : {ket S}) : (e1 : 'QE[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2]=>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma bra_eq S (e1 e2 : {bra S}) : (e1 : 'QE[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2]=>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma zero_allwf S T : @qewf_of _ H S T 0.
Proof.
rewrite qewfP; apply/qexprP=>i j.
by rewrite !qexprE; (do 2 case: eqP=>//?); rewrite linear0.
Qed.
Canonical zero_wfqexpr S T := WFQExpr (@zero_allwf S T).
Canonical zero_sqrqexpr S  := SqrQExpr (@zero_allwf S S).
Canonical zero_ketqexpr S  := KetQExpr (@zero_allwf set0 S).
Canonical zero_braqexpr S  := BraQExpr (@zero_allwf S set0).

Lemma cplx_wf c : @qewf_of _ H set0 set0 c%:QE.
Proof. by rewrite qewfP qesetii. Qed.
Canonical cplx_wfqexpr c  := WFQExpr (@cplx_wf c).
Canonical cplx_sqrqexpr c := SqrQExpr (@cplx_wf c).
Canonical cplx_ketqexpr c := KetQExpr (@cplx_wf c).
Canonical cplx_braqexpr c := BraQExpr (@cplx_wf c).

Lemma ket_wf S (v : 'H[H]_S) : qewf_of set0 S (ketqe v).
Proof. by rewrite qewfP qesetii. Qed.
Canonical ket_wfqexpr S (v : 'H[H]_S)   := WFQExpr (ket_wf v).
Canonical ket_sqrqexpr (v : 'H[H]_set0) := SqrQExpr (ket_wf v).
Canonical ket_ketqexpr S (v : 'H[H]_S)  := KetQExpr (ket_wf v).
Canonical ket_braqexpr (v : 'H[H]_set0) := BraQExpr (ket_wf v).

Lemma bra_wf S (v : 'H[H]_S) : qewf_of S set0 (braqe v).
Proof. by rewrite qewfP qesetii. Qed.
Canonical bra_wfqexpr S (v : 'H[H]_S)   := WFQExpr (bra_wf v).
Canonical bra_sqrqexpr (v : 'H[H]_set0) := SqrQExpr (bra_wf v).
Canonical bra_ketqexpr (v : 'H[H]_set0) := KetQExpr (bra_wf v).
Canonical bra_braqexpr S (v : 'H[H]_S)  := BraQExpr (bra_wf v).

Lemma lin_wf S T (v : 'F[H]_(S,T)) : qewf_of S T (linqe v).
Proof. by rewrite qewfP qesetii. Qed.
Canonical lin_wfqexpr S T (f : 'F[H]_(S,T))  := WFQExpr (lin_wf f).
Canonical lin_sqrqexpr S (f : 'F[H]_S) := SqrQExpr (lin_wf f).
Canonical lin_ketqexpr S (f : 'F[H]_(set0,S)) := KetQExpr (lin_wf f).
Canonical lin_braqexpr S (f : 'F[H]_(S,set0)) := BraQExpr (lin_wf f).

Lemma add_wf S T (e1 e2 : {wf H | S , T}) : qewf_of S T ((e1 : 'QE[H]) + e2).
Proof. by rewrite qewfP wf_linE (wf_linE e2) -addqe_correct qesetii. Qed.
Canonical add_wfqexpr S T e1 e2  := WFQExpr (@add_wf S T e1 e2).
Canonical add_sqrqexpr S (e1 e2 : {sqr H | S}) := SqrQExpr (add_wf [wf of e1] [wf of e2]).
Canonical add_ketqexpr S (e1 e2 : {ket H | S}) := KetQExpr (add_wf [wf of e1] [wf of e2]).
Canonical add_braqexpr S (e1 e2 : {bra H | S}) := BraQExpr (add_wf [wf of e1] [wf of e2]).

Lemma opp_wf S T (e : {wf H | S , T}) : qewf_of S T (- (e : 'QE[H])).
Proof. by rewrite qewfP wf_linE -oppqe_correct qesetii. Qed.
Canonical opp_wfqexpr S T e  := WFQExpr (@opp_wf S T e).
Canonical opp_sqrqexpr S (e : {sqr H | S}) := SqrQExpr (opp_wf [wf of e]).
Canonical opp_ketqexpr S (e : {ket H | S}) := KetQExpr (opp_wf [wf of e]).
Canonical opp_braqexpr S (e : {bra H | S}) := BraQExpr (opp_wf [wf of e]).

Lemma scale_wf c S T (e : {wf H | S , T}) : qewf_of S T (c *: (e : 'QE[H])).
Proof. by rewrite qewfP wf_linE -scaleqe_correct qesetii. Qed.
Canonical scale_wfqexpr c S T e  := WFQExpr (@scale_wf c S T e).
Canonical scale_sqrqexpr c S (e : {sqr H | S}) := SqrQExpr (scale_wf c [wf of e]).
Canonical scale_ketqexpr c S (e : {ket H | S}) := KetQExpr (scale_wf c [wf of e]).
Canonical scale_braqexpr c S (e : {bra H | S}) := BraQExpr (scale_wf c [wf of e]).

Lemma conj_wf S T (e : {wf H | S , T}) : qewf_of S T e`C.
Proof. by rewrite qewfP qexprE {1}wf_linE -conjqe_correct. Qed.
Canonical conj_wfqexpr S T (e : {wf S , T}) := WFQExpr (conj_wf e).
Canonical conj_sqrqexpr S (e : {sqr S}) := SqrQExpr (conj_wf [wf of e]).
Canonical conj_ketqexpr S (e : {ket S}) := KetQExpr (conj_wf [wf of e]).
Canonical conj_braqexpr S (e : {bra S})  := BraQExpr (conj_wf [wf of e]).

Lemma adj_wf S T (e : {wf H | S , T}) : qewf_of T S e`A.
Proof. by rewrite qewfP qexprE {1}wf_linE -adjqe_correct. Qed.
Canonical adj_wfqexpr S T (e : {wf S , T}) := WFQExpr (adj_wf e).
Canonical adj_sqrqexpr S (e : {sqr S}) := SqrQExpr (adj_wf [wf of e]).
Canonical adj_ketqexpr S (e : {bra S}) := KetQExpr (adj_wf [wf of e]).
Canonical adj_braqexpr S (e : {ket S})  := BraQExpr (adj_wf [wf of e]).

Lemma tr_wf S T (e : {wf H | S , T}) : qewf_of T S e`T.
Proof. by rewrite qewfP qexprE {1}wf_linE -trqe_correct. Qed.
Canonical tr_wfqexpr S T (e : {wf S , T}) := WFQExpr (tr_wf e).
Canonical tr_sqrqexpr S (e : {sqr S}) := SqrQExpr (tr_wf [wf of e]).
Canonical tr_ketqexpr S (e : {bra S}) := KetQExpr (tr_wf [wf of e]).
Canonical tr_braqexpr S (e : {ket S})  := BraQExpr (tr_wf [wf of e]).

Lemma com_wf S T W (e1 : {wf H | S, T}) (e2 : {wf H | W, S}) : qewf_of W T (e1 ∗ e2).
Proof. by rewrite qewfP wf_linE (wf_linE e2) -comqe_correct qesetii. Qed.
Canonical com_wfqexpr S T W e1 e2 := WFQExpr (@com_wf S T W e1 e2).
Canonical com_sqrqexpr S T e1 e2 := SqrQExpr (@com_wf S T T e1 e2).
Canonical com_ketqexpr S T e1 (e2 : {ket S}) := KetQExpr (@com_wf S T _ e1 [wf of e2]).
Canonical com_braqexpr S T (e1 : {bra S}) e2 := BraQExpr (@com_wf S _ T [wf of e1] e2).

Lemma ten_wf S T S' T' (e1 : {wf H | S, T}) (e2 : {wf H | S', T'}) : 
  qewf_of (S :|: S') (T :|: T') (e1 ⊗ e2).
Proof. by rewrite qewfP wf_linE (wf_linE e2) -tenqe_correct qesetii. Qed.
Canonical ten_wfqexpr S T S' T' (e1 : {wf S, T}) (e2 : {wf S', T'}) := WFQExpr (ten_wf e1 e2).
Canonical ten_sqrqexpr S S' (e1 : {sqr S}) (e2 : {sqr S'}) := SqrQExpr (ten_wf [wf of e1] [wf of e2]).
Lemma ten_wf_ket S S' (e1 : {ket H | S}) (e2 : {ket S'}) : 
  qewf_of set0 (S :|: S') (e1 ⊗ e2).
Proof. by rewrite qewfP {1}wf_linE/= setU0. Qed.
Lemma ten_wf_bra S S' (e1 : {bra H | S}) (e2 : {bra S'}) : 
  qewf_of (S :|: S') set0 (e1 ⊗ e2).
Proof. by rewrite qewfP {1}wf_linE/= setU0. Qed.
Canonical ten_ketqexpr S S' (e1 : {ket S}) (e2 : {ket S'}) := KetQExpr (ten_wf_ket e1 e2).
Canonical ten_braqexpr S S' (e1 : {bra S}) (e2 : {bra S'}) := BraQExpr (ten_wf_bra e1 e2).

Lemma dot_wf S T S' T' (e1 : {wf H | S, T}) (e2 : {wf H | S', T'}) : 
  qewf_of (S' :|: S :\: T') (T :|: T' :\: S) (e1 ∘ e2).
Proof. by rewrite qewfP wf_linE (wf_linE e2) -dotqe_correct qesetii. Qed.
Canonical dot_wfqexpr S T S' T' (e1 : {wf S, T}) (e2 : {wf S', T'}) := WFQExpr (dot_wf e1 e2).
Lemma dot_wf_sqr S S' (e1 : {sqr H | S}) (e2 : {sqr S'}) : 
  qewf_of (S :|: S') (S :|:S') (e1 ∘ e2).
Proof. by rewrite qewfP [LHS]wf_linE/= setUDV setUD. Qed.
Canonical dot_sqrqexpr S S' (e1 : {sqr S}) (e2 : {sqr S'}) := SqrQExpr (dot_wf_sqr e1 e2).
Lemma dot_wf_ket S S' (e1 : {ket H | S}) (e2 : {ket S'}) : 
  qewf_of set0 (S :|: S') (e1 ∘ e2).
Proof. by rewrite qewfP {1}wf_linE/= set0D setU0 setD0. Qed.
Lemma dot_wf_bra S S' (e1 : {bra H | S}) (e2 : {bra S'}) : 
  qewf_of (S :|: S') set0 (e1 ∘ e2).
Proof. by rewrite qewfP {1}wf_linE/= setD0 set0D setU0 setUC. Qed.
Canonical dot_ketqexpr S S' (e1 : {ket S}) (e2 : {ket S'}) := KetQExpr (dot_wf_ket e1 e2).
Canonical dot_braqexpr S S' (e1 : {bra S}) (e2 : {bra S'}) := BraQExpr (dot_wf_bra e1 e2).

Lemma tens_wf I (r : seq I) (P : pred I) (df cdf : I -> {set L})
  (F : forall i : I, {wf H | df i, cdf i}) : 
  qewf (\bigcup_(i <- r | P i) df i) (\bigcup_(i <- r | P i) cdf i) (\tens_(i <- r | P i) F i).
Proof.
rewrite !bigq; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/wfP.
rewrite !big_cons; case: (P x)=>//; rewrite (wfE P1); apply/wfP.
Qed.
Canonical tens_wfqexpr I (r : seq I) (P : pred I) (df cdf : I -> {set L}) 
  (F : forall i : I, {wf H | df i, cdf i}) 
    := WFQExpr (tens_wf r P F).

Lemma tens_wf_sqr I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, {sqr H | df i}) : 
  qesqr (\bigcup_(i <- r | P i) df i) (\tens_(i <- r | P i) F i).
Proof. apply/tens_wf. Qed.
Canonical tens_sqrqexpr I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, {sqr H | df i}) := SqrQExpr (tens_wf_sqr r P F).

Lemma tens_wf_ket I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, {ket H | df i}) : 
  qeket (\bigcup_(i <- r | P i) df i) (\tens_(i <- r | P i) F i).
Proof. 
have {1}->: (set0 : {set L}) = \bigcup_(i <- r | P i) set0 by rewrite big1. 
apply/tens_wf. 
Qed.
Canonical tens_ketqexpr I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, {ket H | df i}) := KetQExpr (tens_wf_ket r P F).

Lemma tens_wf_bra I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, {bra H | df i}) : 
  qebra (\bigcup_(i <- r | P i) df i) (\tens_(i <- r | P i) F i).
Proof. 
have {2}->: (set0 : {set L}) = \bigcup_(i <- r | P i) set0 by rewrite big1.
apply/tens_wf.
Qed.
Canonical tens_braqexpr I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, {bra H | df i}) := BraQExpr (tens_wf_bra r P F).

(* generally, its better to use lfun for add after calculations *)
Lemma sum_wf I (r : seq I) (P : pred I) S T (F : I -> {wf H | S, T}) : 
  qewf S T (\sum_(i <- r | P i) (F i : 'QE[H])).
Proof.
elim: r=>[|x r P1]; first by rewrite !big_nil; apply/wfP.
rewrite !big_cons; case: (P x)=>//; rewrite (wfE P1); apply/wfP.
Qed.
Canonical sum_wfqexpr I (r : seq I) (P : pred I) S T (F : I -> {wf H | S, T}) 
  := WFQExpr (sum_wf r P F).

Lemma sum_wf_sqr I (r : seq I) (P : pred I) S (F : I -> {sqr H | S}) : 
  qesqr S (\sum_(i <- r | P i) (F i : 'QE[H])).
Proof. apply/sum_wf. Qed.
Canonical sum_sqrqexpr I (r : seq I) (P : pred I) S (F : I -> {sqr H | S}) 
 := SqrQExpr (sum_wf_sqr r P F).

Lemma sum_wf_ket I (r : seq I) (P : pred I) S (F : I -> {ket H | S}) : 
  qeket S (\sum_(i <- r | P i) (F i : 'QE[H])).
Proof. apply/sum_wf. Qed.
Canonical sum_ketqexpr I (r : seq I) (P : pred I) S (F : I -> {ket H | S}) 
 := KetQExpr (sum_wf_ket r P F).

Lemma sum_wf_bra I (r : seq I) (P : pred I) S (F : I -> {bra H | S}) : 
  qebra S (\sum_(i <- r | P i) (F i : 'QE[H])).
Proof. apply/sum_wf. Qed.
Canonical sum_braqexpr I (r : seq I) (P : pred I) S (F : I -> {bra H | S}) 
 := BraQExpr (sum_wf_bra r P F).

(* big dot only canonical when: all square, all ket and all bra *)
Lemma dots_wf_sqr I (r : seq I) (P : pred I) (df : I -> {set L})
 (F : forall i, {sqr H | df i}) : 
  qesqr (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'QE[H])).
Proof.
rewrite !bigq; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/sqrP.
rewrite !big_cons; case: (P x)=>//; rewrite (sqrE P1); apply/sqrP.
Qed.
Canonical dots_sqrqexpr I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, {sqr H | df i}) 
 := SqrQExpr (dots_wf_sqr r P F).

Lemma dots_wf_ket I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, {ket H | df i}) : 
  qeket (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'QE[H])).
Proof.
rewrite !bigq; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/ketP.
rewrite !big_cons; case: (P x)=>//; rewrite (ketE P1); apply/ketP.
Qed.
Canonical dots_ketqexpr I (r : seq I) (P : pred I) S (F : I -> {ket H | S}) 
 := KetQExpr (dots_wf_ket r P F).

Lemma dots_wf_bra I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, {bra H | df i}) : 
  qebra (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'QE[H])).
Proof.
rewrite !bigq; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/braP.
rewrite !big_cons; case: (P x)=>//; rewrite (braE P1); apply/braP.
Qed.
Canonical dots_braqexpr I (r : seq I) (P : pred I) S (F : I -> {bra H | S}) 
 := BraQExpr (dots_wf_bra r P F).

(* extra conditions, used to add user-defined structures *)

Lemma sqr_linP S S' (P : 'F[H]_S) : qesqr S' (linqe P) <-> ((S == S') || (P == 0)).
Proof.
split. move=>/qewfP. case: eqP=>//; case: eqP=>// H1 /eqP H2 H3.
exfalso. apply H1. move: H3; rewrite qeset_eq0l 1?eq_sym// =>/qexprP/(_ S S).
by rewrite qesetii linear0 qexprE.
move=>/orP[/eqP<-|/eqP->]; rewrite ?linear0; apply/sqrP.
Qed.

(* form is frequently used, define qeform to provide canonical structure *)
Definition qeform (e1 e2 : 'QE[H]) := e1`A ∘ e2 ∘ e1.
Lemma qeformE (e1 e2 : 'QE[H]) : qeform e1 e2 = e1`A ∘ e2 ∘ e1. Proof. by []. Qed.
Lemma qeform_sqr S T W (e1 : {wf H | S,T}) (e2 : {sqr W}) :
  qesqr (S :|: W :\: T) (qeform e1 e2).
Proof.
rewrite /qeform wf_linE sqr_linE adjq_lin -!dotqe_correct.
apply/wfP_eq=>/=; fsetdec L.
Qed.
Canonical qeform_wfqexpr S T W e1 e2 := WFQExpr (@qeform_sqr S T W e1 e2).
Canonical qeform_sqrqexpr S T W e1 e2 := SqrQExpr (@qeform_sqr S T W e1 e2).

Lemma qeform_is_linear e1 : linear (@qeform e1).
Proof. by move=>a x y; rewrite /qeform linearPr/= linearPl/=. Qed.
Canonical qeform_additive e1 := Additive (@qeform_is_linear e1).
Canonical qeform_linear e1 := Linear (@qeform_is_linear e1).

Lemma qeformEV (e1 e2 : 'QE[H]) : qeform e1`A e2 = e1 ∘ e2 ∘ e1`A.
Proof. by rewrite qeformE adjqK. Qed.

End WFQETheory.

Section ExtraQExprTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W : {set L}).

Lemma tenqfC S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) : 
  linqe (f \⊗ g) = linqe (g \⊗ f).
Proof. by rewrite tenqe_correct tenqC -tenqe_correct. Qed.

Lemma tenqfA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2))
  (h: 'F[H]_(S3,T3)) : 
  linqe (f \⊗ (g \⊗ h)) = linqe ((f \⊗ g) \⊗ h).
Proof. by rewrite !tenqe_correct tenqA. Qed.

Lemma tenqf1 S T (f: 'F[H]_(S,T))  : 
  linqe (f \⊗ (\1 : 'F[H]_set0)) = linqe f.
Proof. by rewrite tenqe_correct -one1I tenq1. Qed.

Lemma tenq1f S T (f: 'F[H]_(S,T))  : 
  linqe ((\1 : 'F[H]_set0) \⊗ f) = linqe f.
Proof. by rewrite tenqfC tenqf1. Qed.

Lemma dotqfA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2))
  (h: 'F[H]_(S3,T3)) : 
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  linqe (f \⋅ (g \⋅ h)) = linqe (f \⋅ g \⋅ h).
Proof. by move=>P1 P2; apply/qeset_eqcf; rewrite dotfA_cond. Qed.

Lemma dotqA_cond S1 T1 S2 T2 S3 T3 (e1: {wf H | S1,T1}) (e2: {wf H | S2,T2})
  (e3: {wf H | S3,T3}) :
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  e1 ∘ (e2 ∘ e3) = e1 ∘ e2 ∘ e3.
Proof. 
by move=>P1 P2; rewrite wf_linE (wf_linE e2) (wf_linE e3) -!dotqe_correct dotqfA.
Qed.

Lemma dotqA S1 T1 S2 S3 T3 (e1: {wf H | S1,T1}) (e2: {sqr S2})
  (e3: {wf S3,T3}) :
  e1 ∘ (e2 ∘ e3) = e1 ∘ e2 ∘ e3.
Proof. by rewrite dotqA_cond// disjointXD. Qed.

Lemma qeform_comp S T S' W (e1 : {wf H | S,T}) (e2 : {sqr S'}) (e3 : {sqr W}) :
  qeform e1 (qeform e2 e3) = qeform (e2 ∘ e1) e3.
Proof. by rewrite !qeformE adjqG !dotqA_cond//; fsetdec L. Qed.

Lemma qeform_compv S S' W W' (e1 : {bra H | S}) (e2 : {ket S'}) (e3 : {wf W, W'}) :
  qeform e1 (qeform e2 e3) = qeform (e2 ∘ e1) e3.
Proof. by rewrite !qeformE adjqG !dotqA_cond//; fsetdec L. Qed.

Lemma dotqf_ten S1 T1 S2 T2 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2)) :
  [disjoint S1 & T2] -> 
  linqe (f \⋅ g) = linqe (f \⊗ g).
Proof. by move=>P3; apply/qeset_eqcf; rewrite dotf_ten_cond. Qed.

Lemma dotq_ten S1 T1 S2 T2 (e1: {wf H | S1,T1}) (e2: {wf H | S2,T2}) :
  [disjoint S1 & T2] -> 
  e1 ∘ e2 = e1 ⊗ e2.
Proof. 
by move=>P1; rewrite wf_linE (wf_linE e2) -!dotqe_correct -tenqe_correct dotqf_ten.
Qed.

Lemma dotqfC S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) : 
  [disjoint S & T'] -> [disjoint T & S'] ->
  linqe (f \⋅ g) = linqe (g \⋅ f).
Proof. by move=>P1 P2; apply/qeset_eqcf; rewrite dotfC_cond. Qed.

Lemma dotqC S T S' T' (e1: {wf H | S,T}) (e2: {wf S',T'}) :
  [disjoint S & T'] -> [disjoint T & S'] ->
  e1 ∘ e2 = e2 ∘ e1.
Proof. 
by move=>P1 P2; rewrite wf_linE (wf_linE e2) -!dotqe_correct dotqfC.
Qed.

Lemma dotqf1 S T (f: 'F[H]_(S,T))  : 
  linqe (f \⋅ (\1 : 'F[H]_set0)) = linqe f.
Proof. by apply/qeset_eqcf; rewrite dotf1r. Qed.

Lemma dotq1f S T (f: 'F[H]_(S,T))  : 
  linqe ((\1 : 'F[H]_set0) \⋅ f) = linqe f.
Proof. by apply/qeset_eqcf; rewrite dotf1l. Qed.

Lemma dotqf_com S T W (f: 'F[H]_(S,T)) (g: 'F[H]_(W,S)) :
  linqe (f \⋅ g) = linqe (f \o g).
Proof. by apply/qeset_eqcf; rewrite dotf_mul. Qed.

Lemma dotq_com S T W (e1: {wf H | S,T}) (e2: {wf W,S}) :
  e1 ∘ e2 = e1 ∗ e2.
Proof. 
by rewrite wf_linE (wf_linE e2) -dotqe_correct -comqe_correct dotqf_com.
Qed.

Lemma comIq S T (e : {wf H | T,S}) : I_ S ∗ e = e.
Proof. by rewrite wf_linE -comqe_correct comp_lfun1l. Qed.

Lemma comqI S T (e : {wf H | S,T}) : e ∗ I_ S = e.
Proof. by rewrite wf_linE -comqe_correct comp_lfun1r. Qed.

Lemma comq_lin S T W (e1 : {wf H | S,T}) (e2 : {wf H | W,S}) :
  e1 ∗ e2 = linqe (e1 S T \o e2 W S).
Proof. by rewrite {1}wf_linE {1}(wf_linE e2) -comqe_correct. Qed.

Lemma tenq_com S T S' T' W W' (e1: {wf H | S,T}) (e2: {wf W,S}) 
  (e3: {wf S',T'}) (e4: {wf W',S'}) :
  [disjoint S & S'] ->
  (e1 ⊗ e3) ∗ (e2 ⊗ e4) = (e1 ∗ e2) ⊗ (e3 ∗ e4).
Proof.
move=>P; rewrite wf_linE (wf_linE e2) (wf_linE e3) (wf_linE e4) -!tenqe_correct
  -!comqe_correct -tenqe_correct tenf_comp//.
Qed.

Lemma dotIqT S T W (e : {wf H | T,W}) : I_ S ∘ e =  I_ (S :\: W) ⊗ e.
Proof.
rewrite wf_linE -dotqe_correct -tenqe_correct; apply/qeset_eqcf.
by rewrite dotfIl dotf_ten_cond//= disjointDX.
Qed.

Lemma dotqIT S T W (e : {wf H | T,W}) : e ∘ I_ S =  I_ (S :\: T) ⊗ e.
Proof.
rewrite tenqC wf_linE -dotqe_correct -tenqe_correct; apply/qeset_eqcf.
by rewrite dotfIr dotf_ten_cond//= disjointXD.
Qed.

Lemma dotIq S T W (e : {wf H | T,W}) : I_ S ∘ e =  I_ (S :\: W) ∘ e.
Proof. by rewrite dotIqT dotq_ten// disjointDX. Qed.

Lemma dotqI S T W (e : {wf H | T,W}) : e ∘ I_ S = e ∘ I_ (S :\: T).
Proof. by rewrite dotqIT tenqC dotq_ten// disjointXD. Qed.

Lemma dotIqid S T W (e : {wf H | T,W}) : S :<=: W -> I_ S ∘ e = e.
Proof. by rewrite -setD_eq0 dotIqT=>/eqP->; rewrite oneI1 ten1q. Qed.

Lemma dotqIid S T W (e : {wf H | T,W}) : S :<=: T -> e ∘ I_ S = e.
Proof. by rewrite -setD_eq0 dotqIT=>/eqP->; rewrite oneI1 ten1q. Qed.

Lemma dotq_comten S T S' T' (e1 : {wf H | S,T}) (e2 : {wf H | S',T'}) : 
  e1 ∘ e2 = (e1 ⊗ I_ ( T' :\: S )) 
                ∗ (e2 ⊗ I_ ( S :\: T' )).
Proof.
rewrite wf_linE (wf_linE e2) -dotqe_correct -!tenqe_correct. 
by rewrite /dot_lfun comqe_correct linqe_cast !tenqe_correct/=.
Qed.

Lemma dotq_comdot S T S' T' (e1 : {wf H | S,T}) (e2 : {wf H | S',T'}) :
  e1 ∘ e2 = (e1 ∘ I_ T') ∗ (I_ S ∘ e2).
Proof. by rewrite dotq_comten/= tenqC -dotqIT/= tenqC -dotIqT. Qed.

Lemma tenqII S T : (I_ S : 'QE[H]) ⊗ (I_ T) = I_ (S :|: T).
Proof. by rewrite -tenqe_correct tenf11. Qed.

Lemma dotqII S T : (I_ S : 'QE[H]) ∘ (I_ T) = I_ (S :|: T).
Proof. by rewrite dotqI/= dotq_ten ?disjointXD//= tenqII setUD. Qed.

Lemma qe2cK (e : {wf H | set0, set0}) : (qe2c e)%:QE = e.
Proof. by rewrite wf_linE /qe2c linqe_id /cplxqe sf2sK. Qed.

Lemma innerM S (u v : 'H[H]_S) : 〈u｜ ∗ ｜v〉 = [<u ; v>]%:QE.
Proof. by rewrite -comqe_correct comp_dot. Qed.
Lemma innerG S (u v : 'H[H]_S) : 〈u｜ ∘ ｜v〉 = [<u ; v>]%:QE.
Proof. by rewrite dotq_com/= innerM. Qed.
Lemma outerM S (u v : 'H[H]_S) : ｜v〉 ∗ 〈u｜ = ⌈ [> v ; u <] ⌉.
Proof. by rewrite -comqe_correct comp_out. Qed.
Lemma outerG S (u v : 'H[H]_S) : ｜v〉 ∘ 〈u｜ = ⌈ [> v ; u <] ⌉.
Proof. by rewrite dotq_com/= outerM. Qed.
Definition innerq := (innerM, innerG).
Definition outerq := (outerM, outerG).

Definition ket_conj := (@conjq_ket _ H).
Definition ket_adj  := (@adjq_ket _ H).
Definition ket_tr   := (@trq_ket _ H).
Lemma ketT S T (u: 'H[H]_S) (v: 'H[H]_T) :
  ｜u〉 ⊗ ｜v〉 = ｜tenv u v〉.
Proof.
rewrite -tenqe_correct /ketqe -(linqe_cast ((setU0 (set0 : {set L})),erefl _)).
do ? f_equal. apply/lfunPD=>/=i. apply/cdvP=>/= j.
rewrite castlfE/= deltav_cast -!tenfdv !cdvt !lfunE/= /v2f_fun !linearZ/= cdvt /sv2s.
by rewrite !cdvdelta !idx0E !eqxx !mul1r.
Qed.
Definition bra_conj := (@conjq_bra _ H).
Definition bra_adj  := (@adjq_bra _ H).
Definition bra_tr   := (@trq_bra _ H).
Lemma braT S T (u: 'H[H]_S) (v: 'H[H]_T) : 
  〈u｜ ⊗ 〈v｜ = 〈tenv u v｜.
Proof. by rewrite -!ket_adj -adjqT ketT. Qed.

Definition lin_conj := (@conjq_lin _ H).
Definition lin_adj  := (@adjq_lin _ H).
Definition lin_tr   := (@trq_lin _ H).
Lemma linM S T W (f : 'F[H]_(S,T)) (g : 'F[H]_(W,S)) :
  ⌈f⌉ ∗ ⌈g⌉ = ⌈f \o g⌉.
Proof. by rewrite comqe_correct. Qed.

Lemma linG S T W (f : 'F[H]_(S,T)) (g : 'F[H]_(W,S)) :
  ⌈f⌉ ∘ ⌈g⌉ = ⌈f \o g⌉.
Proof. by rewrite dotq_com/= linM. Qed.

Lemma linT S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_(S',T')) :
  ⌈f⌉ ⊗ ⌈g⌉ = ⌈f \⊗ g⌉.
Proof. by rewrite tenqe_correct. Qed.

Lemma lin_dotq S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_(S',T')) :
  ⌈f⌉ ∘ ⌈g⌉ = ⌈f \⋅ g⌉.
Proof. by rewrite dotqe_correct. Qed.

Lemma lin_ketM S T (f : 'F[H]_(S,T)) (v : 'H[H]_S) :
  ⌈f⌉ ∗ ｜v〉 = ｜f v〉.
Proof. 
by rewrite -comqe_correct /ketqe; f_equal; apply f2v_inj; rewrite -v2f_comp v2fK.
Qed.

Lemma lin_ketG S T (f : 'F[H]_(S,T)) (v : 'H[H]_S) :
  ⌈f⌉ ∘ ｜v〉 = ｜f v〉.
Proof. by rewrite dotq_com/= lin_ketM. Qed.

Definition lin_ket := (lin_ketM, lin_ketG).

Lemma lin_braM S T (f : 'F[H]_(S,T)) (v : 'H[H]_T) :
  〈v｜ ∗ ⌈f⌉ = 〈f^A v｜.
Proof. by rewrite -[_ ∗ _]adjqK adjqM bra_adj lin_adj lin_ket ket_adj. Qed.

Lemma lin_braG S T (f : 'F[H]_(S,T)) (v : 'H[H]_T) :
  〈v｜ ∘ ⌈f⌉ = 〈f^A v｜.
Proof. by rewrite dotq_com/= lin_braM. Qed.

Definition lin_bra := (lin_braM, lin_braG).

Lemma dotfTl (S1 S2 S3 T1 T2 T3 : {set L}) (f : 'F[H]_(S1,T1)) 
  (g : 'F[H]_(S2,T2)) (h : 'F[H]_(S3,T3)) :
  S1 :<=: T2 -> [disjoint T2 & T3] ->
  f \⋅ (g \⊗ h) =c f \⋅ g \⊗ h.
Proof.
rewrite -setD_eq0=>/eqP P1 P2.
rewrite -{2}[h]comp_lfun1l /dot_lfun tenf_comp/=.
move: P1 P2. fsetdec L. apply cf_comp.
rewrite -tenfA tenf11. apply cf_tens=>//. apply cf_implicit1.
rewrite setDUl; f_equal; apply/setDidPl; move: P1 P2; fsetdec L.
rewrite !cf_castK tenfC tenfA. apply cf_tens=>//.
rewrite cf_castK tenfC. apply cf_tens=>//. apply cf_implicit1.
by rewrite setDUr P1 set0I.
Qed.

Lemma cf_tensl S1 S2 (A : 'F[H]_(S1,S2)) T1 T2 (C : 'F[H]_(T1,T2))
 S3 S4 (B : 'F[H]_(S3,S4)) :
  A =c C -> A \⊗ B =c C \⊗ B.
Proof. by move=>P; apply cf_tens. Qed.

Lemma cfcast S T (f : 'F[H]_(S,T)) S' T'  (eqST : (S = S') * (T = T'))  :
  castlf eqST f =c f.
Proof. by rewrite cf_castK. Qed.

Lemma dotfTr (S1 S2 S3 T1 T2 T3 : {set L}) (f : 'F[H]_(S1,T1)) 
  (g : 'F[H]_(S2,T2)) (h : 'F[H]_(S3,T3)) :
  T1 :<=: S2 -> [disjoint S2 & S3] ->
    (g \⊗ h) \⋅ f =c g \⋅ f \⊗ h.
Proof.
rewrite -setD_eq0=>/eqP P1 P2.
rewrite -{2}[h]comp_lfun1r /dot_lfun tenf_comp/=.
move: P1 P2; fsetdec L. apply cf_comp.
rewrite tenfC tenfA. apply cf_tens=>//.
rewrite tenfC. apply cf_tens=>//. apply cf_implicit1.
by rewrite setDUr P1 set0I.
rewrite cf_castK (cf_tensl _ (cfcast _ _)) -tenfA tenf11.
apply cf_tens=>//. apply cf_implicit1.
rewrite setDUl; f_equal; apply/setDidPl; move: P1 P2; fsetdec L.
Qed.

Lemma dotqTll S1 S2 S3 T1 T2 T3 (e1 : {wf H | S1,T1}) 
  (e2 : {wf S2,T2}) (e3 : {wf S3,T3}) :
  S1 :<=: T2 -> [disjoint T2 & T3] ->
  e1 ∘ (e2 ⊗ e3) = e1 ∘ e2 ⊗ e3.
Proof.
move=>P1 P2. rewrite wf_linE (wf_linE e2) (wf_linE e3).
rewrite -tenqe_correct -!dotqe_correct -tenqe_correct.
by apply/qeset_eqcf; rewrite dotfTl.
Qed.

Lemma dotqTlr S1 S2 S3 T1 T2 T3 (e1 : {wf H | S1,T1}) 
  (e2 : {wf S2,T2}) (e3 : {wf S3,T3}) : 
  S1 :<=: T3 -> [disjoint T3 & T2] ->
    e1 ∘ (e2 ⊗ e3) = e2 ⊗ (e1 ∘ e3).
Proof. by move=>P1 P2; rewrite tenqC dotqTll 1?tenqC. Qed.

Lemma dotqTrl S1 S2 S3 T1 T2 T3 (e1 : {wf H | S1,T1}) 
  (e2 : {wf S2,T2}) (e3 : {wf S3,T3}) :
  T1 :<=: S2 -> [disjoint S2 & S3] ->
  (e2 ⊗ e3) ∘ e1 = (e2 ∘ e1) ⊗ e3.
Proof.
move=>P1 P2. rewrite wf_linE (wf_linE e1) (wf_linE e3).
rewrite -tenqe_correct -!dotqe_correct -tenqe_correct.
by apply/qeset_eqcf; rewrite dotfTr.
Qed.

Lemma dotqTrr S1 S2 S3 T1 T2 T3 (e1 : {wf H | S1,T1}) 
  (e2 : {wf S2,T2}) (e3 : {wf S3,T3}) :
  T1 :<=: S3 -> [disjoint S3 & S2] ->
  (e2 ⊗ e3) ∘ e1 = e2 ⊗ (e3 ∘ e1).
Proof. by move=>P1 P2; rewrite tenqC dotqTrl 1?tenqC. Qed.

Lemma lin_comTll S T S' T' (f : 'F[H]_S) (g : 'F[H]_(T,S)) (e : {wf S',T'}) : 
  [disjoint S & T'] ->
  ⌈ f ⌉ ∘ (⌈ g ⌉ ⊗ e) = ⌈ f \o g ⌉ ⊗ e.
Proof. by move=>P1; rewrite -linG dotqTll. Qed.

Lemma lin_comTlr S T S' T' (f : 'F[H]_S) (g : 'F[H]_(T,S)) (e : {wf S',T'}) :
  [disjoint S & T'] ->
  ⌈ f ⌉ ∘ (e ⊗ ⌈ g ⌉) = e ⊗ ⌈ f \o g ⌉.
Proof. by move=>P1; rewrite -linG dotqTlr. Qed.

Lemma lin_comTrl S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_S) (e : {wf S',T'}) : 
  [disjoint S & S'] ->
  (⌈ f ⌉ ⊗ e) ∘ ⌈ g ⌉ = ⌈ f \o g ⌉ ⊗ e.
Proof. by move=>P1; rewrite -linG dotqTrl. Qed.

Lemma lin_comTrr S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_S) (e : {wf S',T'}) : 
  [disjoint S & S'] ->
  (e ⊗ ⌈ f ⌉) ∘ ⌈ g ⌉ = e ⊗ ⌈ f \o g ⌉.
Proof. by move=>P1; rewrite -linG dotqTrr. Qed.

Lemma lin_ketTl S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : {wf S',T'}) : 
  [disjoint S & T'] ->
  ⌈ f ⌉ ∘ (｜v〉⊗ e) = ｜f v〉⊗ e.
Proof. by move=>P1; rewrite -lin_ketG dotqTll. Qed.

Lemma lin_ketTr S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : {wf S',T'}) : 
  [disjoint S & T'] ->
  ⌈ f ⌉ ∘ (e ⊗ ｜v〉) = e ⊗ ｜f v〉.
Proof. by move=>P1; rewrite -lin_ketG dotqTlr. Qed.

Lemma lin_braTl S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : {wf S',T'}) : 
  [disjoint S & S'] ->
  (〈v｜ ⊗ e) ∘ ⌈ f ⌉ = 〈f^A v｜ ⊗ e.
Proof. by move=>P1; rewrite -lin_braG dotqTrl. Qed.

Lemma lin_braTr S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : {wf S',T'}) : 
  [disjoint S & S'] ->
  (e ⊗ 〈v｜) ∘ ⌈ f ⌉ = e ⊗ 〈f^A v｜.
Proof. by move=>P1; rewrite -lin_braG dotqTrr. Qed.

Lemma form_dot_com S T (e : {wf H | S , T}) : e ∘ e`A = e ∗ e`A.
Proof. by rewrite dotq_com. Qed.

Lemma tens_adj (I : Type) (r : seq I) (P : pred I) (F : I -> 'QE[H]) :
  (\tens_(i <- r | P i) F i)`A = \tens_(i <- r | P i) (F i)`A.
Proof.
rewrite !bigq; elim: r=>[|x r IH]; first by rewrite !big_nil adjq1.
by rewrite !big_cons; case: (P x)=>//; rewrite adjqT IH.
Qed.

Lemma tens_tr (I : Type) (r : seq I) (P : pred I) (F : I -> 'QE[H]) :
  (\tens_(i <- r | P i) F i)`T = \tens_(i <- r | P i) (F i)`T.
Proof.
rewrite !bigq; elim: r=>[|x r IH]; first by rewrite !big_nil trq1.
by rewrite !big_cons; case: (P x)=>//; rewrite trqT IH.
Qed.

Lemma tens_conj (I : Type) (r : seq I) (P : pred I) (F : I -> 'QE[H]) :
(\tens_(i <- r | P i) F i)`C = \tens_(i <- r | P i) (F i)`C.
Proof. by rewrite qC2AT tens_adj tens_tr; under eq_bigr do rewrite -qC2AT. Qed.

Lemma ketBT_adj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\tens_(i <- r | P i) ketqe (F i))`A = \tens_(i <- r | P i) braqe (F i).
Proof. by rewrite tens_adj; under eq_bigr do rewrite ket_adj. Qed.

Lemma ketBT_tr (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\tens_(i <- r | P i) ketqe (F i))`T = \tens_(i <- r | P i) braqe ((F i)^*v).
Proof. by rewrite tens_tr; under eq_bigr do rewrite ket_tr. Qed.

Lemma ketBT_conj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\tens_(i <- r | P i) ketqe (F i))`C = \tens_(i <- r | P i) ketqe ((F i)^*v).
Proof. by rewrite tens_conj; under eq_bigr do rewrite ket_conj. Qed.

Lemma braBT_adj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\tens_(i <- r | P i) braqe (F i))`A = \tens_(i <- r | P i) ketqe (F i).
Proof. by rewrite tens_adj; under eq_bigr do rewrite bra_adj. Qed.

Lemma braBT_tr (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\tens_(i <- r | P i) braqe (F i))`T = \tens_(i <- r | P i) ketqe ((F i)^*v).
Proof. by rewrite tens_tr; under eq_bigr do rewrite bra_tr. Qed.

Lemma braBT_conj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\tens_(i <- r | P i) braqe (F i))`C = \tens_(i <- r | P i) braqe ((F i)^*v).
Proof. by rewrite tens_conj; under eq_bigr do rewrite bra_conj. Qed.

Lemma tensZ (T : Type) (r : seq T) (P : pred T) (fz : T -> C) (e : T -> 'QE[H]) :
  \tens_(i <- r | P i) ((fz i) *: (e i)) = 
    \prod_(i <- r | P i) (fz i) *: \tens_(i <- r | P i) (e i).
Proof.
elim/big_rec3: _=>[|i e1 c e2 _]; first by rewrite bigq scale1r.
by rewrite bigq=>->; rewrite tenqZl tenqZr scalerA.
Qed.

Lemma tensI F (r : seq F) (P : pred F) (fd : F -> {set L}) :
  \tens_(i <- r | P i) I_ (fd i) = I_ (\bigcup_(i <- r | P i) fd i) :> 'QE[H].
Proof.
elim/big_rec2: _=>[|i x y]; first by rewrite bigq one1I.
by move=>Pi; rewrite bigq=>->; rewrite tenqII.
Qed.

Lemma tensM (I : eqType) (r : seq I) (P : pred I) (d1 d2 d3 : I -> {set L})
  (F : forall i : I, {wf H | d1 i, d2 i}) (G : forall i : I, {wf H | d3 i, d1 i}) :
  (forall i j, P i -> P j -> (i != j) -> [disjoint d1 i & d1 j]) -> 
  uniq r ->
(\tens_(i <- r | P i) F i) ∗ \tens_(i <- r | P i) (G i) = 
(\tens_(i <- r | P i) (F i ∗ G i)).
Proof.
elim: r=>[_|x r IH]; first by rewrite !big_nil bigq {1}one1I comIq.
move=>Pij. rewrite cons_uniq=>/andP[Px ur].
rewrite !big_cons; case E: (P x); last by apply IH.
rewrite ?bigqE tenq_com/= ?IH//.
apply/bigcup_disjoint_seqP=>i /andP[ii Pi]; apply Pij=>//.
by move: Px; move=>/memPnC/(_ _ ii).
Qed.

Lemma cplxBT (I : eqType) (r : seq I) (P : pred I) (F : I -> C) :
\tens_(i <- r | P i) ((F i)%:QE : 'QE[H]) = (\prod_(i <- r | P i) (F i))%:QE.
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil bigq.
by rewrite !big_cons; case: (P x)=>[|//]; rewrite bigqE IH cplxT; f_equal.
Qed.

Lemma outerMBT (I : Type) (r : seq I) (P : pred I) (Dv Du : I -> {set L}) 
  (Vs : forall i, 'H[H]_(Dv i)) (Us : forall i, 'H[H]_(Du i)) : 
  (\tens_(i <- r | P i) ｜Vs i〉) ∗ (\tens_(i <- r | P i) 〈Us i｜) 
  = \tens_(i <- r | P i) (｜Vs i〉∗〈Us i｜).
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil bigq {1}one1I comIq.
rewrite !big_cons; case E: (P x); last by apply IH.
by rewrite ?bigqE tenq_com ?disjoint0X//= IH.
Qed.

Lemma outerGBT (I : Type) (r : seq I) (P : pred I) (Dv Du : I -> {set L}) 
  (Vs : forall i, 'H[H]_(Dv i)) (Us : forall i, 'H[H]_(Du i)) : 
  (\tens_(i <- r | P i) ｜Vs i〉) ∘ (\tens_(i <- r | P i) 〈Us i｜) 
  = \tens_(i <- r | P i) (｜Vs i〉∘〈Us i｜).
Proof.
rewrite dotq_com/= outerMBT//. 
by under eq_bigr do rewrite -dotq_com.
Qed.

Lemma innerMBT (I : eqType) (r : seq I) (P : pred I) (Ds : I -> {set L}) 
(Vs Us : forall i, 'H[H]_(Ds i)) : 
(forall i j, P i -> P j -> (i != j) -> [disjoint Ds i & Ds j]) -> uniq r ->
(\tens_(i <- r | P i) 〈Vs i｜) ∗ (\tens_(i <- r | P i) ｜Us i〉)
= (\prod_(i <- r | P i) [<Vs i ; Us i>])%:QE.
Proof.
by move=>P1 P2; rewrite tensM// -cplxBT; under eq_bigr do rewrite innerM.
Qed.

Lemma innerGBT (I : eqType) (r : seq I) (P : pred I) (Ds : I -> {set L}) 
(Vs Us : forall i, 'H[H]_(Ds i)) : 
(forall i j, P i -> P j -> (i != j) -> [disjoint Ds i & Ds j]) -> uniq r ->
(\tens_(i <- r | P i) 〈Vs i｜) ∘ (\tens_(i <- r | P i) ｜Us i〉)
= (\prod_(i <- r | P i) [<Vs i ; Us i>])%:QE.
Proof. by rewrite dotq_com/=; apply innerMBT. Qed.

Lemma outerMBTs (r : seq L) (P: pred L) (Vs Us : forall i : L, 'H[H]_[set i]) : 
  (\tens_(i <- r | P i) ｜Vs i〉) ∗ (\tens_(i <- r | P i) 〈Us i｜) 
  = \tens_(i <- r | P i) (｜Vs i〉∗〈Us i｜).
Proof. by rewrite outerMBT. Qed.

Lemma innerMBTs (r : seq L) (P: pred L) (Vs Us: forall i : L, 'H[H]_[set i]) : 
uniq r ->
(\tens_(i <- r | P i) 〈Vs i｜) ∗ (\tens_(i <- r | P i) ｜Us i〉) 
= (\prod_(i <- r | P i) [<Vs i ; Us i>])%:QE.
Proof. by move=>ur; rewrite innerMBT// =>i j _ _; rewrite disjoints1 inE. Qed.

End ExtraQExprTheory.

(* here we give the relation between tenvm tenfm and \tens *)
(* they are indeed the same, without any conditions *)
Section BigTenLfun.
Context (L : finType) (H : L -> chsType).

Lemma idx_big_recl_cast (dt : 0.-tuple {set L}) :
  set0 = \bigcup_i dt ~_ i.
Proof. by rewrite big_ord0. Qed.

Lemma tenvm_tuple0 (dt : 0.-tuple {set L}) (u : forall x : 'I_0, 'H[H]_(dt ~_ x)) :
  tenvm u = casths (idx_big_recl_cast dt) (deltav (@idx0 _ H)).
Proof. by apply/cdvP=>i; rewrite cdvtm big_ord0 cdv_castV idx0E cdvdelta eqxx. Qed.

Lemma tenvm_cast1 (F : finType) (dt dt' : F -> {set L}) 
  (u : forall x, 'H[H]_(dt x)) (v : forall x, 'H[H]_(dt' x)) 
  (castP : forall x, dt x = dt' x) :
    (forall i, casths (castP i) (u i) = v i) ->
  ｜ tenvm u 〉 = ｜ tenvm v 〉.
Proof.
suff P: dt = dt'. case: dt' /P castP v=>P1 v Pi.
by f_equal; apply/tenvmP=>i; rewrite -Pi casths_id.
by apply/funext.
Qed.

Lemma tenvm_tuple_correct (n : nat) (dt : n.-tuple {set L})
  (u : forall x : 'I_n, 'H[H]_(dt ~_ x)) :
    \tens_j ｜u j〉 = ｜tenvm u〉.
Proof.
elim: n dt u=>[dt u | n IH dt u].
rewrite big_ord0 tenvm_tuple0 ketqe_cast bigq /cplxqe/ketqe; f_equal.
by apply/lfunP=>v; rewrite /s2sf scale1r lfunE/= v2fE -decsv.
move: (tenvm_recl u)=>/esym/casths_sym->.
rewrite ketqe_cast -ketT big_ord_recl bigqE; f_equal.
case/tupleP: dt u=>x dt u.
have castP i : [tuple of x :: dt] ~_ (fintype.lift ord0 i) = dt ~_ i by rewrite tnthS.
pose uu (i : 'I_n) := casths (castP i) (locked_with tt (fun i=> u (fintype.lift ord0 i)) i).
rewrite (eq_bigr (fun i=> ketqe (uu i)))=>[i _|].
by rewrite /uu ketqe_cast.
rewrite IH /uu; symmetry; apply/tenvm_cast1.
by move=>i; f_equal.
Qed.

Lemma tenvm_bij_cast (F G : finType) (f : G -> F) (bf : bijective f) 
  (dt : F -> {set L}) :
    \bigcup_j (dt (f j)) = \bigcup_i (dt i).
Proof. by rewrite (reindex f)//; move: bf=>[g fK gK]; exists g=>i _; rewrite ?fK ?gK. Qed.

Lemma incl_cast (B C : {set L}) (eqBC : B = C) : B :<=: C.
Proof. by case: C / eqBC. Qed.

Lemma incl_comp (A B C : {set L}) (p1 : A :<=: B) (p2 : B :<=: C)
  (i : 'Idx[H]_C) (j : {i : L | i \in A}) :
  i (incl p2 (incl p1 j)) = i (incl (subset_trans p1 p2) j).
Proof.
by rewrite /incl/= (eq_irrelevance  (subsetP p2 _ _)
(subsetP (subset_trans p1 p2) _ (ssrfun.svalP j))).
Qed.

Lemma idx_incl_id2 (A B : {set L}) (p1 p2 : A :<=: B) (i : 'Idx[H]_B) 
  (j : {i : L | i \in A}) :
  i (incl p1 j) = i (incl p2 j).
Proof. by rewrite (eq_irrelevance p1 p2). Qed.

Lemma idx_incl_id1 (B : {set L}) (p1 : B :<=: B) (i : 'Idx[H]_B) 
  (j : {i : L | i \in B}) :
  i (incl p1 j) = i j.
Proof.
by case: j=>x p; rewrite /incl (eq_irrelevance  (subsetP p1 _ _) p).
Qed.

Lemma castidxE (B C : {set L}) (eqBC : B = C) (i : 'Idx[H]_B) (j : {i : L | i \in C}) :
  castidx eqBC i j = i (incl (incl_cast (esym eqBC)) j).
Proof. by case: C / eqBC j=>j; rewrite castidx_id; symmetry; exact: idx_incl_id1. Qed.

Lemma tenvm_bij (F G : finType) (f : G -> F) (bf : bijective f) 
  (dt : F -> {set L})  (u : forall i : F, 'H[H]_(dt i)) :
    tenvm u = casths (tenvm_bij_cast bf dt) (tenvm (fun i => u (f i))).
Proof.
apply/cdvP=>i; rewrite cdvtm cdv_castV cdvtm; move: bf=>[g fK gK].
rewrite (reindex f). by exists g=>j _; rewrite ?fK ?gK.
apply eq_bigr=>j _; f_equal.
rewrite /flatidx !ffunE; apply/mvectorP=>k.
rewrite !mvE. rewrite castidxE incl_comp; exact: idx_incl_id2.
Qed.

Lemma tenvm_correct (F : finType) (dt : F -> {set L}) (u : forall i : F, 'H[H]_(dt i)) :
  \tens_j ｜u j〉 = ｜tenvm u〉.
Proof.
pose dt' := tuple_of_finfun [ffun i : 'I_#|F| => dt (enum_val i)].
suff castP : forall i, dt' ~_ i = dt (enum_val i).
pose u1 (i : 'I_#|F|) := casths (esym (castP i)) (u (enum_val i)).
pose f (i : 'I_#|F|) := enum_val i.
have bf : bijective f.
by exists (fun i=> enum_rank i)=>i; rewrite /f ?enum_valK ?enum_rankK.
have <-: ｜ tenvm u1 〉 = ｜ tenvm u 〉.
rewrite (tenvm_bij bf) ketqe_cast.
by apply/tenvm_cast1=>i; rewrite /u1 casths_comp casths_id.
rewrite -tenvm_tuple_correct (reindex f).
by move: bf=>[g fK gK]; exists g=>i _; rewrite ?fK ?gK.
rewrite bigq; apply eq_bigr=>i _.
by rewrite /f/u1 ketqe_cast.
by move=>i; rewrite /dt'/tuple_of_finfun tnth_map ffunE tnth_ord_tuple.
Qed.

Lemma linqe_eq_onb (S T : {set L}) (e1 e2 : {wf H | S , T}) (F : finType)
  (onb : 'ONB[H]_(F;S)) :
  (forall i, e1 ∗ ｜onb i〉 = e2 ∗ ｜onb i〉) -> e1 = e2 :> 'QE.
Proof.
rewrite (wf_linE e1) (wf_linE e2)=>P.
f_equal; apply/(intro_onb onb)=>i.
by move: (P i); rewrite !lin_ketM=>/ketqe_inj.
Qed.
Global Arguments linqe_eq_onb [S T e1 e2 F] onb.



Lemma tenfm_tuple0 (dt cdt : 0.-tuple {set L}) 
  (u : forall x : 'I_0, 'F[H]_(dt ~_ x, cdt ~_ x)) :
  tenfm u = castlf (idx_big_recl_cast dt, idx_big_recl_cast cdt) \1.
Proof.
apply/lfunPD=>i; rewrite -tenfmdv tenvm_tuple0.
by rewrite castlfE/= lfunE/= [in RHS]deltav_cast idx0E.
Qed.

Lemma tenfm_cast1 (F : finType) (dt dt' cdt cdt': F -> {set L}) 
  (u : forall x, 'F[H]_(dt x, cdt x)) (v : forall x, 'F[H]_(dt' x, cdt' x)) 
  (castP : forall x, (dt x = dt' x) * (cdt x = cdt' x)) :
    (forall i, castlf (castP i) (u i) = v i) ->
    ⌈ tenfm u ⌉ = ⌈ tenfm v ⌉.
Proof.
suff P: dt = dt'. case: dt' /P castP v=>castP v.
suff P': cdt = cdt'. case: cdt' / P' castP v=> castP v Pi.
by f_equal; apply/tenfmP=>i; rewrite -Pi castlf_id.
all: by apply/funext=>i; move: (castP i)=>[].
Qed.

Lemma tenfm_tuple_correct (n : nat) (dt cdt : n.-tuple {set L})
  (u : forall x : 'I_n, 'F[H]_(dt ~_ x, cdt ~_ x)) :
    \tens_j ⌈ u j ⌉ = ⌈ tenfm u ⌉.
Proof.
elim: n dt cdt u=>[dt cdt u|n IH dt cdt u].
by rewrite big_ord0 bigq tenfm_tuple0 linqe_cast one1I.
move: (tenfm_recl u)=>/esym/castlf_sym->.
rewrite linqe_cast -linT big_ord_recl bigqE; f_equal.
case/tupleP: dt u =>x dt; case/tupleP : cdt=>cx cdt u.
have castP i : ([tuple of x :: dt] ~_ (fintype.lift ord0 i) = dt ~_ i) *
  ([tuple of cx :: cdt] ~_ (fintype.lift ord0 i) = cdt ~_ i).
by rewrite !tnthS.
pose uu (i : 'I_n) := castlf (castP i) (locked_with tt (fun i=> u (fintype.lift ord0 i)) i).
rewrite (eq_bigr (fun i=> linqe (uu i)))=>[i _|].
by rewrite /uu linqe_cast.
rewrite IH /uu; symmetry; apply/tenfm_cast1.
by move=>i; f_equal.
Qed.

Lemma tenfm_bij (F G : finType) (f : G -> F) (bf : bijective f) 
  (dt cdt : F -> {set L})  (u : forall i : F, 'F[H]_(dt i, cdt i)) :
    tenfm u = castlf (tenvm_bij_cast bf dt, tenvm_bij_cast bf cdt) 
      (tenfm (fun i => u (f i))).
Proof.
apply/lfunPD=>i; rewrite castlfE/= deltav_cast -!tenfmdv.
rewrite (tenvm_bij bf); f_equal; apply/tenvmP=>j; do ? f_equal.
rewrite /flatidx !ffunE; apply/mvectorP=>k.
rewrite !mvE castidxE incl_comp; exact: idx_incl_id2.
Qed.

Lemma tenfm_correct (F : finType) (dt cdt : F -> {set L}) 
  (u : forall i : F, 'F[H]_(dt i, cdt i)) :
  \tens_j ⌈ u j ⌉ = ⌈ tenfm u ⌉.
Proof.
pose dt' := tuple_of_finfun [ffun i : 'I_#|F| => dt (enum_val i)].
pose cdt' := tuple_of_finfun [ffun i : 'I_#|F| => cdt (enum_val i)].
suff castP : forall i, (dt' ~_ i = dt (enum_val i)) * (cdt' ~_ i = cdt (enum_val i)).
pose u1 (i : 'I_#|F|) := castlf (esym (castP i).1, esym (castP i).2) (u (enum_val i)).
pose f (i : 'I_#|F|) := enum_val i.
have bf : bijective f.
by exists (fun i=> enum_rank i)=>i; rewrite /f ?enum_valK ?enum_rankK.
have <-: ⌈ tenfm u1 ⌉ = ⌈ tenfm u ⌉.
rewrite (tenfm_bij bf) linqe_cast.
by apply/tenfm_cast1=>i; rewrite /u1; case: (castP i)=>a b; 
  rewrite castlf_comp/= castlf_id.
rewrite -tenfm_tuple_correct (reindex f).
by move: bf=>[g fK gK]; exists g=>i _; rewrite ?fK ?gK.
rewrite bigq; apply eq_bigr=>i _.
by rewrite /f/u1 linqe_cast.
by move=>i; rewrite /dt'/cdt'/tuple_of_finfun !tnth_map !ffunE tnth_ord_tuple.
Qed.

End BigTenLfun.



Reserved Notation "''QONB'".
Reserved Notation "''QONB_' ( F ; S )"      (at level 8, format "''QONB_' ( F ;  S )").
Reserved Notation "''QONB[' H ]_ ( F ; S )"     (at level 8).
Reserved Notation "[ 'QONB' 'of' f 'as' g ]" (at level 0, format "[ 'QONB'  'of'  f  'as'  g ]").
Reserved Notation "[ 'QONB' 'of' f ]"  (at level 0, format "[ 'QONB'  'of'  f ]").

Reserved Notation "''QNS'".
Reserved Notation "''QNS_' S"       (at level 8, S at level 2, format "''QNS_' S").
Reserved Notation "''QNS_' ( S )"   (at level 8).
Reserved Notation "''QNS[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''QNS[' H ]_ ( S )"     (at level 8).
Reserved Notation "''QNS' ( S )"    (at level 8, format "''QNS' ( S )").
Reserved Notation "[ 'QNS' 'of' f 'as' g ]" (at level 0, format "[ 'QNS'  'of'  f  'as'  g ]").
Reserved Notation "[ 'QNS' 'of' f ]"  (at level 0, format "[ 'QNS'  'of'  f ]").

Module QEONB.

Section ClassDef.
Variable (L : finType) (H : L -> chsType) (F : finType) (S : {set L}).

Definition axiom (f : F -> 'QE[H]) := 
  (forall i, qeket S (f i)) /\
  (forall i j, (f i)`A ∗ (f j) = (i == j)%:R%:QE)  /\ #|F| = Vector.dim 'H[H]_S.

Lemma axiom_split (f : F -> 'QE[H]) :
  (forall i, qeket S (f i)) ->
  (forall i j, (f i)`A ∗ (f j)= (i == j)%:R%:QE) ->
  #|F| = Vector.dim 'H[H]_S -> axiom f.
Proof. by rewrite /axiom; split. Qed.

Lemma axiom_split_ket (f : F -> {ket H | S}) :
  (forall i j, (f i)`A ∗ (f j)= (i == j)%:R%:QE) ->
  #|F| = Vector.dim 'H[H]_S -> axiom f.
Proof. apply/axiom_split=>i; apply/ketP. Qed.

Structure map (phUV : phant (F -> 'QE[H])) := Pack {
  apply; 
  _ : axiom apply; 
}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> 'QE[H])) (f g : F -> 'QE[H]) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation qonb f := (axiom f).
Coercion apply : map >-> Funclass.
Notation QONBasis fA fB fC := (Pack (Phant _) (axiom_split fA fB fC)).
Notation QONBket f fA fB := (@Pack _ _ _ _ (Phant _) f (axiom_split_ket fA fB)).
Notation "''QONB[' H ]_ ( F ; S )" := (map S (Phant (F -> 'QE[H]))) : type_scope.
Notation "''QONB_' ( F ; S )" := ('QONB[_]_(F;S)) : type_scope.
Notation "''QONB'" := ('QONB_(_;_)) (only parsing) : type_scope.
Notation "[ 'QONB' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'QONB' 'of' f ]" := (@clone _ _ _ _ _ f f _ _ id id) : form_scope.
End Exports.

End QEONB.
Export QEONB.Exports.

Module QENormalizedState.

Section ClassDef.
Variable (L : finType) (H : L -> chsType) (F : finType) (S : {set L}).
Definition axiom (v : 'QE[H]) := 
  qeket S v /\ v`A ∗ v = 1%:QE.

Lemma axiom_split (v : 'QE[H]) :
  qeket S v -> v`A ∗ v = 1%:QE -> axiom v.
Proof. by rewrite /axiom; split. Qed.

Lemma axiom_split_ket (v : {ket H | S}) :
  v`A ∗ v = 1%:QE -> axiom v.
Proof. apply/axiom_split/ketP. Qed.

Structure type := Pack { sort; _ : axiom sort; }.
Local Coercion sort : type >-> qexpr.

Variables (T : 'QE[H]) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom cT') in c.
Definition clone c of phant_id class c := @Pack T c.

End ClassDef.

Module Import Exports.
Coercion sort : type >-> qexpr.
Notation QNSType fA fB := (Pack (axiom_split fA fB)).
Notation QNSket v fA := (@Pack _ _ _ v (axiom_split_ket fA)).
Notation "''QNS[' H ]_ S" := (@type _ H S) (only parsing) : type_scope.
Notation "''QNS[' H ]_ ( S )" := ('QNS[H]_S)    (only parsing) : type_scope.
Notation "''QNS_' S"  := ('QNS[_]_S) : type_scope.
Notation "''QNS_' ( S )" := ('QNS_S) (only parsing) : type_scope.
Notation "[ 'QNS' 'of' f 'as' g ]" := (@clone _ _ _ f g _ idfun) : form_scope.
Notation "[ 'QNS' 'of' f ]" := (@clone _ _ _ f _ _ id) : form_scope.
End Exports.

End QENormalizedState.
Export QENormalizedState.Exports.

Section QEONBTheory.
Context {L : finType} (H : L -> chsType).
Variable (F : finType) (S : {set L}) (f : 'QONB[H]_(F;S)).

Lemma onb_wf i : qeket S (f i).
Proof. by case: f=>?/=[?]. Qed.
Canonical onb_wfqexpr i := WFQExpr (@onb_wf i).
Canonical onb_ketqexpr i := KetQExpr (@onb_wf i).

Lemma onb_innerM i j : (f i)`A ∗ (f j) = (i == j)%:R%:QE.
Proof. by case: f=>?/=[?][->]. Qed.

Lemma onb_innerG i j : (f i)`A ∘ (f j) = (i == j)%:R%:QE.
Proof. by rewrite dotq_com/= onb_innerM. Qed.

Lemma qeonb_card : #|F| = Vector.dim 'H[H]_S.
Proof. by case: f=>?/=[?[??]]. Qed.

Definition onb2qe (G : finType) (onb : 'ONB[H]_(G;S)) i := ketqe (onb i).
Lemma onb2qe_dot G onb i j : (@onb2qe G onb i)`A ∗ (@onb2qe G onb j) = (i == j)%:R%:QE.
Proof. by rewrite /onb2qe ket_adj innerM onb_dot. Qed.
Canonical onb2qe_qonbasis G onb := QONBket (@onb2qe G onb) (@onb2qe_dot G onb) (onb_card onb).

Definition qe2onb i := qe2v S (f i).
Lemma qe2onb_dot i j : [< qe2onb i ; qe2onb j >] = (i == j)%:R.
Proof. by apply/(@cplxqe_inj _ H); rewrite /qe2onb -innerM -ket_adj !qe2vK onb_innerM. Qed.
Canonical qe2onb_ponbasis := PONBasis qe2onb_dot.
Canonical qe2onb_onbasis := ONBasis qe2onb_dot qeonb_card.

Lemma sumonb_outerM : \sum_i (f i) ∗ (f i)`A = I_ S.
Proof.
move: (sumonb_out qe2onb_onbasis)=><-/=.
rewrite linear_sum/=; apply eq_bigr=>i _.
by rewrite -outerM /qe2onb -ket_adj !qe2vK.
Qed.

Lemma sumonb_outerG : \sum_i (f i) ∘ (f i)`A = I_ S.
Proof. by rewrite -sumonb_outerM; apply eq_bigr=>i _; rewrite dotq_com. Qed.

Lemma onb_vecM (v : {ket S}) : (v : 'QE) = \sum_i ((f i)`A ∗ v) ∘ f i.
Proof.
rewrite -qe2vK {1}(onb_vec qe2onb_onbasis (qe2v S v)).
rewrite linear_sum; apply eq_bigr=>i _/=.
by rewrite linearZ/= -cplxGl /qe2onb -innerM -ket_adj !qe2vK.
Qed.

Lemma onb_vecG (v : {ket S}) : (v : 'QE) = \sum_i ((f i)`A ∘ v) ∘ f i.
Proof. by rewrite {1}onb_vecM; apply eq_bigr=>i _; rewrite dotq_com. Qed.

Lemma onb_lfunM (T : {set L}) (e : {wf S,T}) : 
  (e : 'QE) = \sum_i e ∗ (f i) ∗ (f i)`A.
Proof.
rewrite -[LHS]comqI -sumonb_outerM linear_sum/=.
by apply eq_bigr=>i _/=; rewrite comqA.
Qed.

Lemma onb_lfunM2 (e : {sqr S}) : 
  (e : 'QE) = \sum_i \sum_j ((f j)`A ∗ e ∗ (f i)) ∘ ((f j) ∗ (f i)`A).
Proof.
rewrite {1}onb_lfunM; apply eq_bigr=>i _/=.
rewrite [e ∗ f i]onb_vecM/= linear_suml; apply eq_bigr=>j _/=.
by rewrite !comqA -qe2cK/= !cplxGl comqZl.
Qed.

Lemma ns_wf (v : 'QNS[H]_S) : qeket S v.
Proof. by case: v=>/=?[??]. Qed.
Canonical ns_wfqexpr v := WFQExpr (@ns_wf v).
Canonical ns_ketqexpr v := KetQExpr (@ns_wf v).

Lemma ns_innerM (v : 'QNS[H]_S) : v`A ∗ v = 1%:QE.
Proof. by case: v=>/=?[??]. Qed.

Lemma ns_innerG (v : 'QNS[H]_S) : v`A ∘ v = 1%:QE.
Proof. by rewrite dotq_com/= ns_innerM. Qed.

Lemma qeonb_ns i : (f i)`A ∗ (f i) = 1%:QE.
Proof. by rewrite onb_innerM eqxx one1E. Qed.
Canonical qeonb_qnsType i := QNSType (@onb_wf i) (@qeonb_ns i).

Lemma ketns_innerM (v : 'NS[H]_S) : (ketqe v)`A ∗ (ketqe v) = 1%:QE.
Proof. by rewrite ket_adj innerM ns_dot. Qed.
Canonical ketns_qnsType (v : 'NS[H]_S) := QNSket (ketqe v) (@ketns_innerM v).

End QEONBTheory.

Section QExprVOrder.
Context {L : finType} (H : L -> chsType).
Implicit Type (f g h: 'QE[H]).
(* all non-diag are 0, all diag psd *)
Definition psdqe :=
  [qualify A : 'QE[H] | 
    [forall S, (A S S \is psdlf) && 
      [forall T, (S == T) || (A S T == 0)]]].
Fact psdqe_key : pred_key psdqe. Proof. by []. Qed.
Canonical psdqe_keyed := KeyedQualifier psdqe_key.

Lemma psdqeP f : reflect ((forall S, (f S S \is psdlf)) /\ 
  (forall S T : {set L}, S != T -> (f S T == 0))) (f \is psdqe).
Proof.
apply/(iffP idP); rewrite qualifE.
move=>/forallP P; split=>[S|S T/negPf P3]; move: (P S)=>/andP[P1//].
by move=>/forallP/(_ T); rewrite P3.
move=>[P1 P2]; apply/forallP=>S; apply/andP; split=>//.
by apply/forallP=>T; case: eqP=>//= /eqP; apply P2.
Qed.

Definition leqe_def f g := (g - f) \is psdqe.
Definition ltqe_def f g := (g != f) && (leqe_def f g).

Lemma ltqe_def_def : forall f g, ltqe_def f g = (g != f) && (leqe_def f g).
Proof. by rewrite /leqe_def. Qed.

Lemma leqe_def_anti : antisymmetric leqe_def.
Proof.
move=>f g=>/andP[/psdqeP [P1 P2]/psdqeP [P3 P4]].
apply/qexprP=>S T. case E: (S == T).
move: E=>/eqP->; apply/le_anti; move: (P1 T) (P3 T).
by rewrite !qexprE !psdlfE !subv_ge0=>->->.
by move: E=>/eqP/eqP/P4; rewrite !qexprE subr_eq0=>/eqP.
Qed.

Lemma leqe_def_refl : reflexive leqe_def.
Proof.
move=>x; apply/psdqeP; split=>[S|S T _].
all: by rewrite !qexprE subrr// psdlf0.
Qed.

Lemma leqe_def_trans : transitive leqe_def.
Proof.
move=>f g h=>/psdqeP[P1 P2]/psdqeP[P3 P4].
apply/psdqeP; split=>[S|S T P5].
move: (P1 S) (P3 S); rewrite !qexprE !psdlfE !subv_ge0; exact: le_trans.
by move: (P2 _ _ P5) (P4 _ _ P5); rewrite !qexprE !subr_eq0=>/eqP->/eqP->.
Qed.

Definition lownerqe_porderMixin := LePOrderMixin 
ltqe_def_def leqe_def_refl leqe_def_anti leqe_def_trans.

Canonical lownerqe_porderType := POrderType vorder_display 'QE[H] lownerqe_porderMixin.

Lemma geqe0P f : reflect ((forall S, ((0 : 'End(_)) ⊑ f S S)) /\ 
  (forall S T : {set L}, S != T -> (f S T == 0))) ((0 : 'QE) ⊑ f).
Proof. 
apply/(iffP (psdqeP _)); rewrite subr0=>[[P1 P2]];
by split=>[|//] S; rewrite ?psdlfE// -psdlfE P1.
Qed.

Lemma leqe_add2rP h f g : f ⊑ g -> (f + h) ⊑ (g + h).
Proof. by rewrite addrC /Order.le/= /leqe_def opprD addrA addrK. Qed.

Lemma leqe_pscale2lP (e : C) f g : 0 < e -> f ⊑ g -> (e *: f) ⊑ (e *: g).
Proof.
move=>egt0/psdqeP[P1 P2]; apply/psdqeP; split=>[S|S T /P2].
by move: (P1 S); rewrite !psdlfE=>P3; rewrite -scalerBr qexprE pscalev_rge0.
by rewrite -scalerBr [in X in _ -> X]qexprE=>/eqP->; rewrite scaler0.
Qed.

Import VOrder.Exports.
Definition lownerqe_vorderMixin := VOrderMixin leqe_add2rP leqe_pscale2lP.
Canonical lownerqe_vorderType := VOrderType C 'QE[H] lownerqe_vorderMixin.

Lemma ltqe_ltf f : (0 : 'QE) ⊏ f -> 
  exists (S : {set L}), (0 : 'End('H_S)) ⊏ f S S.
Proof.
rewrite lt_def=>/andP[/eqP+/geqe0P[P1 P2]].
rewrite not_existsP; apply contra_not=>P3.
apply/qexprP=>S T; rewrite qexprE.
case E: (S == T); last by apply/eqP/P2; rewrite E.
move: E=>/eqP->; move: (P3 T) (P1 T)=>/negP/negPf.
by rewrite le_eqVlt eq_sym orbC=>->/=/eqP.
Qed.

Lemma pscaleqe_lge0 f (a : C) : 
  (0 : 'QE) ⊏ f -> (0 : 'QE) ⊑ a *: f = (0 <= a).
Proof.
move=>P. move: {+}P=>/ltqe_ltf[S Ps].
apply/Bool.eq_iff_eq_true; split.
by move=>/geqe0P[/(_ S)+ _]; rewrite qexprE pscalev_lge0.
by rewrite le0r=>/orP[/eqP->|P1]; 
  rewrite ?scale0r ?lexx// pscalev_rge0//; apply/ltW.
Qed.

Import CanVOrder.Exports.
Definition lownerqe_canVOrderMixin := CanVOrderMixin pscaleqe_lge0.
Canonical lownerqe_canVOrderType := CanVOrderType C 'QE[H] lownerqe_canVOrderMixin.

End QExprVOrder.

Section QExprVOrderTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T : {set L}).
Local Notation "'0" := (0 : 'QE[H]).
Local Notation "a '%:E'" := (a : 'QE) (at level 2, left associativity, format "a %:E").

Lemma lin_eq0 S T (f : 'F[H]_(S,T)) : (⌈ f ⌉ == 0) = (f == 0).
Proof. by rewrite -(inj_eq (@linqe_inj _ _ _ _)) linear0. Qed.

Lemma wf_ge0_eq0 S T (e : {wf H | S , T}) : 
  S != T -> '0 ⊑ e -> e%:E = 0.
Proof.
by move=>P /geqe0P[_/(_ S T P)]/eqP; rewrite {2}wf_linE=>->; rewrite linear0.
Qed.

Lemma wf_gt0_eq0 S T (e : {wf H | S , T}) : 
  S != T -> '0 ⊏ e -> e%:E = 0.
Proof. move=>+/ltW; exact: wf_ge0_eq0. Qed.

Lemma sqr_gef0 S (e : {sqr H | S}) : '0 ⊑ e = (0%:VF ⊑ e S S).
Proof.
apply/Bool.eq_iff_eq_true; split; first by move=>/geqe0P[/(_ S)].
move=>P; apply/geqe0P; split=>[T|T W PT]; rewrite sqr_linE.
case E: (S == T); move: E=>/eqP.
by move=>Q; case: T / Q; rewrite linqe_id.
move=>/eqP; rewrite eq_sym=>P1; rewrite qeset_eq0l//.
rewrite qeset_eq0p//=; move: PT; apply contraNN=>/eqP P1.
by inversion P1.
Qed.

Lemma lin_lef S (f g : 'F[H]_S) : ⌈ f ⌉ ⊑ ⌈ g ⌉ = (f ⊑ g).
Proof. by rewrite -subv_ge0 -linearB/= sqr_gef0/= linqe_id subv_ge0. Qed.

Lemma lin_ltf S (f g : 'F[H]_S) : ⌈ f ⌉ ⊏ ⌈ g ⌉ = (f ⊏ g).
Proof. by rewrite !lt_def -subr_eq0 -linearB/= lin_eq0 subr_eq0 lin_lef. Qed.

Lemma lin_gef0 S (f : 'F[H]_S) : '0 ⊑ ⌈ f ⌉ = (0%:VF ⊑ f).
Proof. by rewrite -lin_lef linear0. Qed.

Lemma lin_gtf0 S (f : 'F[H]_S) : '0 ⊏ ⌈ f ⌉ = (0%:VF ⊏ f).
Proof. by rewrite -lin_ltf linear0. Qed.

Lemma sqr_lef S (e1 e2 : {sqr H | S}) : (e1%:E ⊑ e2) = (e1 S S ⊑ e2 S S).
Proof. by rewrite {1}sqr_linE {1}(sqr_linE e2) lin_lef. Qed.

Lemma sqr_ltf S (e1 e2 : {sqr H | S}) : (e1%:E ⊏ e2) = (e1 S S ⊏ e2 S S).
Proof. by rewrite {1}sqr_linE {1}(sqr_linE e2) lin_ltf. Qed.

Lemma tenq_id S1 T1 S2 T2 (f : {wf H | S1, T1}) (g : {wf S2, T2}) : 
  (f ⊗ g) (S1 :|: S2) (T1 :|: T2) = f S1 T1 \⊗ g S2 T2.
Proof. by rewrite {1}wf_linE  {1}(wf_linE g) -tenqe_correct linqe_id. Qed.

Lemma tenq_sqr_id S T (f : {sqr H | S}) (g : {sqr T}) : 
  (f ⊗ g) (S :|: T) (S :|: T) = f S S \⊗ g T T.
Proof. by rewrite tenq_id. Qed.

Lemma sqr_eqf S (e1 e2 : {sqr H | S}) : (e1%:E == e2) = (e1 S S == e2 S S).
Proof. by rewrite {1}sqr_linE {1}(sqr_linE e2) (inj_eq (@linqe_inj _ _ _ _)). Qed.

Lemma sqr_eqf0 S (e : {sqr H | S}) : (e%:E == 0) = (e S S == 0).
Proof. by rewrite sqr_eqf/= qexprE. Qed.

Lemma sqr_leII S (e : {sqr H | S}) :
  e%:E ⊑ |I = (e S S ⊑ \1).
Proof.
apply/Bool.eq_iff_eq_true; split.
by move=>/psdqeP[/(_ S)+ _]; rewrite psdlfE !qexprE qexprII_id subv_ge0.
move=>P; apply/psdqeP; split=>[T|T W P1].
rewrite psdlfE !qexprE qexprII_id subv_ge0 sqr_linE.
case E: (S == T); move: E=>/eqP.
by move=>E; case: T / E; rewrite linqe_id.
by move=>/eqP P1; rewrite qeset_eq0l ?lef01//= eq_sym.
rewrite !qexprE qexprII_eq0// subr_eq0 eq_sym sqr_linE.
rewrite qeset_eq0p//=; move: P1; apply contraNN=>/eqP P1.
by inversion P1.
Qed.

Ltac simp_sqr := rewrite ?(sqr_lef,sqr_ltf,sqr_eqf0,sqr_eqf,sqr_leII)/= 
  ?(tenq_sqr_id,linqe_id, qexprE).

Lemma sqr_gtf0 S (e : {sqr H | S}) : '0 ⊏ e = (0%:VF ⊏ e S S).
Proof. by simp_sqr. Qed.

Lemma sqr_lef0 S (e : {sqr H | S}) : e%:E ⊑ 0 = (e S S ⊑ 0).
Proof. by simp_sqr. Qed.

Lemma sqr_ltf0 S (e : {sqr H | S}) : e%:E ⊏ 0 = (e S S ⊏ 0).
Proof. by simp_sqr. Qed.

Definition sqr_cpf0 := (sqr_gef0, sqr_gtf0, sqr_lef0, sqr_ltf0).

Lemma wf_ge0_ge0 S T (e : {wf H | S , T}) : 
  S = T -> '0 ⊑ e = (0%:VF ⊑ e S S).
Proof.
move=>P; case: T / P e=>e. move: (wfP e)=>P.
by rewrite (sqrE P) sqr_gef0.
Qed.

Lemma wf_gt0_gt0 S T (e : {wf H | S , T}) : 
  S = T -> '0 ⊏ e = (0%:VF ⊏ e S S).
Proof.
move=>P; case: T / P e=>e. move: (wfP e)=>P.
by rewrite (sqrE P) sqr_gtf0.
Qed.

Lemma leqe0I S : (0 : 'QE[H]) ⊑ I_ S.
Proof. by rewrite sqr_gef0/= linqe_id lef01. Qed.

Lemma ltqe0I S : (0 : 'QE[H]) ⊏ I_ S.
Proof. by rewrite sqr_gtf0/= linqe_id ltf01. Qed.

Lemma leqe01 : (0 : 'QE[H]) ⊑ |1.
Proof. by rewrite one1I leqe0I. Qed.

Lemma ltqe01 : (0 : 'QE[H]) ⊏ |1.
Proof. by rewrite one1I ltqe0I. Qed.

Lemma leqe0II : (0 : 'QE[H]) ⊑ |I.
Proof. by apply/geqe0P; split=>[S|S T P1]; rewrite ?qexprII_id ?lef01// qexprII_eq0. Qed.

Lemma ltqe0II : (0 : 'QE[H]) ⊏ |I.
Proof. by rewrite lt_def leqe0II II_neq0. Qed.

Lemma sqr_lef1 S (e : {sqr H | S}) : e%:E ⊑ I_ S = (e S S ⊑ \1).
Proof. by simp_sqr. Qed.

Lemma sqr_ltf1 S (e : {sqr H | S}) : e%:E ⊏ I_ S = (e S S ⊏ \1).
Proof. by simp_sqr. Qed.

Lemma sqr_gef1 S (e : {sqr H | S}) : I_ S ⊑ e%:E  = (\1 ⊑ e S S).
Proof. by simp_sqr. Qed.

Lemma sqr_gtf1 S (e : {sqr H | S}) : I_ S ⊏ e%:E  = (\1 ⊏ e S S).
Proof. by simp_sqr. Qed.

Definition sqr_cpf1 := (sqr_lef1, sqr_ltf1, sqr_gef1, sqr_gtf1).

Lemma sqr_leIIE S (e : {sqr H | S}) :
  e%:E ⊑ |I = (e%:E ⊑ I_ S).
Proof. by rewrite sqr_leII sqr_lef1. Qed.

Lemma lin_lef1 S (f : 'F[H]_S) : ⌈ f ⌉ ⊑ I_ S = (f ⊑ \1).
Proof. by rewrite sqr_lef1/= linqe_id. Qed.

Lemma lin_ltf1 S (f : 'F[H]_S) : ⌈ f ⌉ ⊏ I_ S = (f ⊏ \1).
Proof. by rewrite sqr_ltf1/= linqe_id. Qed.

Lemma lin_leII S (f : 'F[H]_S) : ⌈ f ⌉ ⊑ |I = (f ⊑ \1).
Proof. by rewrite sqr_leII/= linqe_id. Qed.

Section tenq_order.
Variable (S T : {set L}) (dis : [disjoint S & T]).
Implicit Type (x : {sqr H | S}) (y : {sqr H | T}).

Lemma tenq_eq0 x y : x ⊗ y == 0 = (x%:E == 0) || (y%:E == 0).
Proof. by simp_sqr; apply: bregv_eq0. Qed.

Lemma ptenq_rge0 x y : '0 ⊏ x -> ('0 ⊑ x ⊗ y) = ('0 ⊑ y).
Proof. by simp_sqr; apply: pbregv_rge0. Qed.

Lemma ptenq_lge0 y x : '0 ⊏ y -> ('0 ⊑ x ⊗ y) = ('0 ⊑ x).
Proof. by simp_sqr; apply: pbregv_lge0. Qed.

(* bad !! *)
(* Definition tenq_bregVOrderMixin S T dis := 
    bregVOrderMixin (@tenq_eq0 S T dis) (ptenq_rge0 dis) (ptenq_lge0 dis).
Canonical tenq_bregVOrderType S T dis := 
  bregVOrderType (@ten_lfun _ _ S S T T) (@tenf_bregVOrderMixin S T dis). *)

Lemma ptenq_rgt0 x y : '0 ⊏ x -> ('0 ⊏ x ⊗ y) = ('0 ⊏ y).
Proof. by simp_sqr; apply: pbregv_rgt0. Qed.

Lemma ptenq_lgt0 y x : '0 ⊏ y -> ('0 ⊏ x ⊗ y) = ('0 ⊏ x).
Proof. by simp_sqr; apply: pbregv_lgt0. Qed.

Lemma tenqI_eq0 x y : x%:E != 0 -> (x ⊗ y == 0) = (y%:E == 0).
Proof. by simp_sqr; apply: bregvI_eq0. Qed.

Lemma tenqI x y1 y2 : x%:E != 0 -> x ⊗ y1 = x ⊗ y2 -> y1%:E = y2.
Proof.
by rewrite -!eq_iff; simp_sqr; rewrite !eq_iff=>IH1; apply: (bregvI IH1).
Qed.

Lemma tenIq_eq0 y x : y%:E != 0 -> (x ⊗ y == 0) = (x%:E == 0).
Proof. by simp_sqr; apply: bregIv_eq0. Qed.

Lemma tenIq y x1 x2 : y%:E != 0 -> x1 ⊗ y = x2 ⊗ y -> x1%:E = x2.
Proof.
by rewrite -!eq_iff; simp_sqr; rewrite !eq_iff=>IH1; apply: (bregIv IH1).
Qed.

Lemma le_ptenq2lP x y1 y2 : '0 ⊏ x -> y1%:E ⊑ y2 -> x ⊗ y1 ⊑ x ⊗ y2.
Proof. by simp_sqr; apply: lev_pbreg2lP. Qed.

(* mulr and lev/ltv *)
Lemma le_ptenq2l x y1 y2 : '0 ⊏ x -> (x ⊗ y1 ⊑ x ⊗ y2) = (y1%:E ⊑ y2).
Proof. by simp_sqr=>IH; apply: lev_pbreg2l. Qed.

Lemma lt_ptenq2l x y1 y2 : '0 ⊏ x -> (x ⊗ y1 ⊏ x ⊗ y2) = (y1%:E ⊏ y2).
Proof. by simp_sqr=>IH; apply: ltv_pbreg2l. Qed.
Definition lte_ptenq2l := (le_ptenq2l, lt_ptenq2l).

Lemma le_ptenq2r y x1 x2 : '0 ⊏ y -> (x1 ⊗ y ⊑ x2 ⊗ y) = (x1%:E ⊑ x2).
Proof. by simp_sqr=>IH; apply: lev_pbreg2r. Qed.

Lemma lt_ptenq2r y x1 x2 : '0 ⊏ y -> (x1 ⊗ y ⊏ x2 ⊗ y) = (x1%:E ⊏ x2).
Proof. by simp_sqr=>IH; apply: ltv_pbreg2r. Qed.
Definition lte_ptenq2r := (le_ptenq2r, lt_ptenq2r).

Lemma le_ntenq2l x y1 y2 : x%:E ⊏ 0 -> (x ⊗ y1 ⊑ x ⊗ y2) = (y2%:E ⊑ y1).
Proof. by simp_sqr=>IH; apply: lev_nbreg2l. Qed.

Lemma lt_ntenq2l x y1 y2 : x%:E ⊏ 0 -> (x ⊗ y1 ⊏ x ⊗ y2) = (y2%:E ⊏ y1).
Proof. by simp_sqr=>IH; apply: ltv_nbreg2l. Qed.
Definition lte_ntenq2l := (le_ntenq2l, lt_ntenq2l).

Lemma le_ntenq2r y x1 x2 : y%:E ⊏ 0 -> (x1 ⊗ y ⊑ x2 ⊗ y) = (x2%:E ⊑ x1).
Proof. by simp_sqr=>IH; apply: lev_nbreg2r. Qed.

Lemma lt_ntenq2r y x1 x2 : y%:E ⊏ 0 -> (x1 ⊗ y ⊏ x2 ⊗ y) = (x2%:E ⊏ x1).
Proof. by simp_sqr=>IH; apply: ltv_nbreg2r. Qed.
Definition lte_ntenq2r := (le_ntenq2r, lt_ntenq2r).

Lemma le_wptenq2l x y1 y2 : '0 ⊑ x -> y1%:E ⊑ y2 -> x ⊗ y1 ⊑ x ⊗ y2.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wpbreg2l. Qed.

Lemma le_wntenq2l x y1 y2 : x%:E ⊑ 0 -> y1%:E ⊑ y2 -> x ⊗ y2 ⊑ x ⊗ y1.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wnbreg2l. Qed.

Lemma le_wptenq2r y x1 x2 : '0 ⊑ y -> x1%:E ⊑ x2 -> x1 ⊗ y ⊑ x2 ⊗ y.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wpbreg2r. Qed.

Lemma le_wntenq2r y x1 x2 : y%:E ⊑ 0 -> x1%:E ⊑ x2 -> x2 ⊗ y ⊑ x1 ⊗ y.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wnbreg2r. Qed.

(* Binary forms, for backchaining. *)
Lemma le_ptenq2 x1 x2 y1 y2 :
  '0 ⊑ x1 -> '0 ⊑ y1 -> x1%:E ⊑ x2 -> y1%:E ⊑ y2 -> x1 ⊗ y1 ⊑ x2 ⊗ y2.
Proof. by simp_sqr; apply: lev_pbreg2. Qed.

Lemma lt_ptenq2 x1 x2 y1 y2 :
  '0 ⊑ x1 -> '0 ⊑ y1 -> x1%:E ⊏ x2 -> y1%:E ⊏ y2 -> x1 ⊗ y1 ⊏ x2 ⊗ y2.
Proof. by simp_sqr; apply: ltv_pbreg2. Qed.

Lemma ptenq_rlt0 x y : '0 ⊏ x -> (x ⊗ y ⊏ 0) = (y%:E ⊏ 0).
Proof. by simp_sqr; apply: pbregv_rlt0. Qed.

Lemma ptenq_rle0 x y : '0 ⊏ x -> (x ⊗ y ⊑ 0) = (y%:E ⊑ 0).
Proof. by simp_sqr; apply: pbregv_rle0. Qed.

Lemma ntenq_rgt0 x y : x%:E ⊏ 0 -> ('0 ⊏ x ⊗ y) = (y%:E ⊏ 0).
Proof. by simp_sqr; apply: nbregv_rgt0. Qed.

Lemma ntenq_rge0 x y : x%:E ⊏ 0 -> ('0 ⊑ x ⊗ y) = (y%:E ⊑ 0).
Proof. by simp_sqr; apply: nbregv_rge0. Qed.

Lemma ntenq_rlt0 x y : x%:E ⊏ 0 -> (x ⊗ y ⊏ 0) = ('0 ⊏ y).
Proof. by simp_sqr; apply: nbregv_rlt0. Qed.

Lemma ntenq_rle0 x y : x%:E ⊏ 0 -> (x ⊗ y ⊑ 0) = ('0 ⊑ y).
Proof. by simp_sqr; apply: nbregv_rle0. Qed.

Lemma ptenq_llt0 y x : '0 ⊏ y -> (x ⊗ y ⊏ 0) = (x%:E ⊏ 0).
Proof. by simp_sqr; apply: pbregv_llt0. Qed.

Lemma ptenq_lle0 y x : '0 ⊏ y -> (x ⊗ y ⊑ 0) = (x%:E ⊑ 0).
Proof. by simp_sqr; apply: pbregv_lle0. Qed.

Lemma ntenq_lgt0 y x : y%:E ⊏ 0 -> ('0 ⊏ x ⊗ y) = (x%:E ⊏ 0).
Proof. by simp_sqr; apply: nbregv_lgt0. Qed.

Lemma ntenq_lge0 y x : y%:E ⊏ 0 -> ('0 ⊑ x ⊗ y) = (x%:E ⊑ 0).
Proof. by simp_sqr; apply: nbregv_lge0. Qed.

Lemma ntenq_llt0 y x : y%:E ⊏ 0 -> (x ⊗ y ⊏ 0) = ('0 ⊏ x).
Proof. by simp_sqr; apply: nbregv_llt0. Qed.

Lemma ntenq_lle0 y x : y%:E ⊏ 0 -> (x ⊗ y ⊑ 0) = ('0 ⊑ x).
Proof. by simp_sqr; apply: nbregv_lle0. Qed.

(* weak and symmetric lemmas *)
Lemma tenq_ge0 x y : '0 ⊑ x -> '0 ⊑ y -> '0 ⊑ x ⊗ y.
Proof. by simp_sqr; apply: bregv_ge0. Qed.

Lemma tenq_le0 x y : x%:E ⊑ 0 -> y%:E ⊑ 0 -> '0 ⊑ x ⊗ y.
Proof. by simp_sqr; apply: bregv_le0. Qed.

Lemma tenq_ge0_le0 x y : '0 ⊑ x -> y%:E ⊑ 0 -> x ⊗ y ⊑ 0.
Proof. by simp_sqr; apply: bregv_ge0_le0. Qed.

Lemma tenq_le0_ge0 x y : x%:E ⊑ 0 -> '0 ⊑ y -> x ⊗ y ⊑ 0.
Proof. by simp_sqr; apply: bregv_le0_ge0. Qed.

(* bregv_gt0 with only one case *)

Lemma tenq_gt0 x y : '0 ⊏ x -> '0 ⊏ y -> '0 ⊏ x ⊗ y.
Proof. by simp_sqr; apply: bregv_gt0. Qed.

Lemma tenq_lt0 x y : x%:E ⊏ 0 -> y%:E ⊏ 0 -> '0 ⊏ x ⊗ y.
Proof. by simp_sqr; apply: bregv_lt0. Qed.

Lemma tenq_gt0_lt0 x y : '0 ⊏ x -> y%:E ⊏ 0 -> x ⊗ y ⊏ 0.
Proof. by simp_sqr; apply: bregv_gt0_lt0. Qed.

Lemma tenq_lt0_gt0 x y : x%:E ⊏ 0 -> '0 ⊏ y -> x ⊗ y ⊏ 0.
Proof. by simp_sqr; apply: bregv_lt0_gt0. Qed.

Lemma tenq_le1 x y : '0 ⊑ x -> '0 ⊑ y 
  -> x%:E ⊑ I_ S -> y%:E ⊑ I_ T -> x ⊗ y ⊑ I_ (S :|: T).
Proof. by move=>P1 P2 P3 P4; rewrite -tenqII; apply: le_ptenq2=>/=. Qed.

Lemma tenq_lt1 x y : '0 ⊑ x -> '0 ⊑ y -> x%:E ⊏ I_ S -> y%:E ⊏ I_ T -> x ⊗ y ⊏ I_ (S :|: T).
Proof. by move=>P1 P2 P3 P4; rewrite -tenqII; apply: lt_ptenq2=>/=. Qed.
Definition tenq_lte1 := (tenq_le1, tenq_lt1).

Lemma tenq_ge1 x y : I_ S ⊑ x -> I_ T ⊑ y -> I_ (S :|: T) ⊑ x ⊗ y.
Proof. by rewrite -tenqII=>P1 P2; apply: le_ptenq2=>/=[||//|//]; apply: leqe0I. Qed.

Lemma tenq_gt1 x y : I_ S ⊏ x -> I_ T ⊏ y -> I_ (S :|: T) ⊏ x ⊗ y.
Proof. by rewrite -tenqII=>P1 P2; apply: lt_ptenq2=>/=[||//|//]; apply: leqe0I. Qed.
Definition tenq_gte1 := (tenq_ge1, tenq_gt1).
Definition tenq_cp1 := (tenq_lte1, tenq_gte1).

End tenq_order.

Lemma tenq_ge0_le1 S T (P : {sqr H | S}) (Q : {sqr T}) :
  [disjoint S & T] ->
  '0 ⊑ P%:E ⊑ I_ S -> '0 ⊑ Q%:E ⊑ I_ T ->
  '0 ⊑ P ⊗ Q  ⊑ I_ (S :|: T).
Proof.
move=>dis/andP[]P1 P2/andP[]P3 P4; apply/andP; split.
by apply: tenq_ge0. by rewrite -tenqII; apply: le_ptenq2=>/=.
Qed.

Lemma tens_ge0_seq (I : eqType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, {sqr (S i)}) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) -> uniq r ->
  (forall i, R i -> (0 : 'QE[H]) ⊑ P i) ->
  '0 ⊑ \tens_(i <- r | R i) P i.
Proof.
move=>IH1+IH2; elim: r=>[|a r IH]; first by rewrite big_nil bigq leqe01.
rewrite cons_uniq=>/andP[na ur]. rewrite big_cons; case E: (R a).
rewrite bigqE sqr_linE [X in _⊗X]sqr_linE/= -tenqe_correct lin_gef0.
apply: bregv_ge0. apply/bigcup_disjoint_seqP=>i/andP[Pi Ri]. 
apply: IH1=>//. by apply: (notin_in_neq na).
1,2: by rewrite -lin_gef0 -sqr_linE ?IH2//= IH. by apply IH.
Qed.

Lemma tens_ge0 (I : finType) (R : pred I) (S : I -> {set L})
  (P : forall i, {sqr (S i)}) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) ->
  (forall i, R i -> (0 : 'QE[H]) ⊑ P i) ->
  '0 ⊑ \tens_(i | R i) P i.
Proof. by move=>IH; apply: tens_ge0_seq=>//; apply: index_enum_uniq. Qed.

Lemma tens_ge0_le1_seq (I : eqType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, {sqr (S i)}) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) -> uniq r ->
  (forall i, R i -> (0 : 'QE[H]) ⊑ (P i : 'QE) ⊑ I_ (S i)) ->
  '0 ⊑ \tens_(i <- r | R i) P i ⊑ I_ (\bigcup_(i <- r | R i) S i).
Proof.
move=>IH1+IH2; elim: r=>[|a r IH]; first by rewrite !big_nil bigq leqe01 one1I/=.
rewrite cons_uniq=>/andP[na ur]. rewrite !big_cons; case E: (R a).
rewrite bigqE. apply: tenq_ge0_le1.
apply/bigcup_disjoint_seqP=>i/andP[Pi Ri]. apply: IH1=>//. by apply: (notin_in_neq na).
by apply IH2. all: by apply : IH.
Qed.

Lemma tens_ge0_le1 (I : finType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, {sqr (S i)}) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) ->
  (forall i, R i -> (0 : 'QE[H]) ⊑ (P i : 'QE) ⊑ I_ (S i)) ->
  '0 ⊑ \tens_(i | R i) P i ⊑ I_ (\bigcup_(i | R i) S i).
Proof. move=>IH; apply: tens_ge0_le1_seq=>//; apply: index_enum_uniq. Qed.


End QExprVOrderTheory.
