(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

(* -------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory Num.Def.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Obligation Tactic := idtac.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

(* ==================================================================== *)
Section ProdVector.
Section Defn.
Context {I : finType} (E : I -> Type).

Variant mvector := MVector of {dffun forall i : I, E i}.

Definition mv_val u := let: MVector t := u in t.

Canonical mvector_subType := Eval hnf in [newType for mv_val].

Fact mvector_key : unit. Proof. by []. Qed.
Definition mvector_of_fun_def F := MVector [ffun i : I => F i].
Definition mvector_of_fun k := locked_with k mvector_of_fun_def.
Canonical mvector_unlockable k := [unlockable fun mvector_of_fun k].

Definition fun_of_mvector u (i : I) := mv_val u i.

Coercion fun_of_mvector : mvector >-> Funclass.

Lemma mvE k F i : mvector_of_fun k F i = F i.
Proof. by rewrite unlock /fun_of_mvector /= ffunE. Qed.

Lemma mvectorP (u v : mvector) : (forall i, u i = v i) <-> u = v.
Proof.
rewrite /fun_of_mvector; split=> [/= eq_uv | -> //].
by apply/val_inj/ffunP=> i; apply: eq_uv.
Qed.

Lemma eq_mv k u v : (forall i, u i = v i) ->
  mvector_of_fun k u = mvector_of_fun k v.
Proof. by move=> eq_uv; apply/mvectorP => i; rewrite !mvE eq_uv. Qed.
End Defn.

Definition mvector_eqMixin {I : finType} (E : I -> eqType) :=
  Eval hnf in [eqMixin of mvector E by <:].
Canonical mvector_eqType {I : finType} (E : I -> eqType) :=
  Eval hnf in EqType (mvector E) (mvector_eqMixin E).
Definition mvector_choiceMixin {I : finType} (E : I -> choiceType) :=
  [choiceMixin of mvector E by <:].
Canonical mvector_choiceType {I : finType} (E : I -> choiceType) :=
  Eval hnf in ChoiceType (mvector E) (mvector_choiceMixin E).
Definition mvector_countMixin {I : finType} (E : I -> countType) :=
  [countMixin of mvector E by <:].
Canonical mvector_countType {I : finType} (E : I -> countType) :=
  Eval hnf in CountType (mvector E) (mvector_countMixin E).
Canonical mvector_subCountType {I : finType} (E : I -> countType) :=
  Eval hnf in [subCountType of mvector E].
Definition mvector_finMixin (I : finType) (E : I -> finType) :=
  [finMixin of mvector E by <:].
Canonical mvector_finType (I : finType) (E : I -> finType) :=
  Eval hnf in FinType (mvector E) (mvector_finMixin E).
Canonical mvector_subFinType (I : finType) (E : I -> finType) :=
  Eval hnf in [subFinType of mvector E].

Lemma card_mv (I: finType) (E: I -> finType) :
  #|mvector_finType E| = #|{dffun forall i : I, E i}|.
Proof. by rewrite card_sub. Qed.
End ProdVector.

Notation "\mvector_ ( i : I ) E" := (mvector_of_fun mvector_key (fun i : I => E))
  (at level 36, E at level 36, i, I at level 50): ring_scope.

(* ==================================================================== *)
Section ProdVectorZmod.
Context {I : finType} (E : I -> zmodType).

Implicit Types u v w : mvector E.

Definition mvector_zero     := \mvector_(i : I) (0 : E i).
Definition mvector_add  u v := \mvector_(i : I) (u i + v i).
Definition mvector_opp  u   := \mvector_(i : I) -u i.

Program Canonical mvector_zmodType := Eval hnf in ZmodType (mvector E)
  (@GRing.Zmodule.Mixin _ mvector_zero mvector_opp mvector_add _ _ _ _).

Next Obligation.
by move=> f g h; apply/mvectorP=> i; rewrite !mvE addrA.
Qed.

Next Obligation.
by move=> f g; apply/mvectorP=> i; rewrite !mvE addrC.
Qed.

Next Obligation.
by move=> f; apply/mvectorP=> i; rewrite !mvE add0r.
Qed.

Next Obligation.
by move=> f; apply/mvectorP=> i; rewrite !mvE addNr.
Qed.

Lemma mv_sumE T (P : pred T) (F : T -> mvector E) (r : seq T) i :
  (\sum_(x <- r | P x) F x) i = \sum_(x <- r | P x) F x i.
Proof. by elim/big_rec2: _ => /= [|x _ s Px <-]; rewrite mvE. Qed.
End ProdVectorZmod.

(* ==================================================================== *)
Section ProdVectorVectLmodType.
Context {A : ringType} {I : finType} (E : I -> lmodType A).

Implicit Types u v w : mvector E.

Definition mvector_scale (c : A) u :=
  \mvector_(i : I) (c *: u i).

Program Canonical ffun_lmodType := Eval hnf in LmodType A (mvector E)
  (@LmodMixin _ _ mvector_scale _ _ _ _).

Next Obligation.
by move=> /= c d x; apply/mvectorP=> i; rewrite !mvE scalerA.
Qed.

Next Obligation.
by move=> /= x; apply/mvectorP=> i; rewrite !mvE scale1r.
Qed.

Next Obligation.
by move=> /= c u v; apply/mvectorP=> i; rewrite !mvE scalerDr.
Qed.

Next Obligation.
by move=> /= u c d; apply/mvectorP=> i; rewrite !mvE scalerDl.
Qed.

Lemma scalemvE (c : A) (u : forall i, E i) :
  c *: \mvector_(i : I) u i = \mvector_(i : I) (c *: u i).
Proof. by apply/mvectorP=> i; rewrite !mvE. Qed.
End ProdVectorVectLmodType.

(* -------------------------------------------------------------------- *)
Import Vector.InternalTheory.

Section ProdVectorVectType.
Context {I : finType} {k : fieldType} (E : I -> vectType k).

Let Z := {i : I & 'I_(Vector.dim (E i))}.

Let S {i : I} (x : 'I_(Vector.dim (E i))) : Z := Tagged _ x.

Let D := (\sum_i Vector.dim (E i))%N.

Lemma vect_axiom_eqdim
    {A : ringType} {M : lmodType A} (m n : nat) (eq_nm : n = m)
  : Vector.axiom n M -> Vector.axiom m M.
Proof.
pose F (r : 'rV[A]_n) := castmx (erefl _, eq_nm) r.
pose G (r : 'rV[A]_m) := castmx (esym (erefl _), esym eq_nm) r.
case=> [f lin_f bij_f]; exists (F \o f).
- move=> c x y /=; rewrite lin_f; apply/rowP => i.
  by rewrite castmxE !mxE !castmxE /=.
apply/bij_comp => //; exists G => r; rewrite /G /F.
- by rewrite castmxK. - by rewrite castmxKV.
Qed.

Lemma mvector_vect_iso : Vector.axiom D (mvector E).
Proof.
suff: Vector.axiom #|{: Z}| (mvector E).
- apply: vect_axiom_eqdim; rewrite /D card_tagged.
  rewrite sumnE big_map big_enum /=.
  by apply: eq_bigr=> i _; rewrite card_ord.
pose fr (f : mvector E) := \row_(i < #|{: Z}|)
  v2r (f (tag (enum_val i))) 0 (tagged (enum_val i)).
exists fr=> /= [c f g|].
- by apply/rowP=> i; rewrite !mxE !mvE linearP /= !mxE.
pose gr (i : I) (x : 'rV[k]_#|{: Z}|) :=
  r2v (\row_(j < Vector.dim (E i)) x 0 (enum_rank (S j))).
exists (fun x => \mvector_(i : I) gr i x) => [g|r].
- apply/mvectorP=> i; rewrite mvE /fr /gr.
  set r := (X in r2v X); suff ->: r = v2r (g i) by rewrite v2rK.
  by apply/rowP=> j; rewrite !mxE enum_rankK /=.
- apply/rowP=> j; rewrite !mxE !mvE r2vK mxE; congr (_ _ _).
  by apply/(canLR enum_valK)/esym/eqP; rewrite eq_Tagged.
Qed.

Definition mvector_vectMixin := VectMixin mvector_vect_iso.
Canonical mvector_vectType := VectType k (mvector E) mvector_vectMixin.

End ProdVectorVectType.
