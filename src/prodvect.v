(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.

(* -------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory Num.Def.

(************************************************************************)
(*                Variant of dependent finite function                  *)
(************************************************************************)

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Obligation Tactic := idtac.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

(* ==================================================================== *)
Section ProdVectorDef.
Variable I : finType.
Variable E : I -> Type.

Variant mvector : predArgType := MVector of {dffun forall i : I, E i}.

Definition mv_val u := let: MVector t := u in t.

HB.instance Definition _ := [isNew for mv_val].

Definition fun_of_mvector u (i : I) := mv_val u i.

Coercion fun_of_mvector : mvector >-> Funclass.
End ProdVectorDef.

Fact mvector_key : unit. Proof. by []. Qed.

HB.lock 
Definition mvector_of_fun (I : finType) (E : I -> Type) (k : unit) (F : forall i : I, E i) := 
  @MVector I E [ffun i : I => F i].
Canonical mvector_unlockable := Unlockable mvector_of_fun.unlock.

Section ProdVectorDef2.
Variable I : finType.
Variable E : I -> Type.
Implicit Type F : forall i : I, E i.

Lemma mvE k F i : mvector_of_fun k F i = F i.
Proof. by rewrite unlock /fun_of_mvector /= ffunE. Qed.

Lemma mvectorP (u v : mvector E) : (forall i, u i = v i) <-> u = v.
Proof.
rewrite /fun_of_mvector; split=> [/= eq_uv | -> //].
by apply/val_inj/ffunP=> i; apply: eq_uv.
Qed.

Lemma eq_mv k F1 F2 : (forall i, F1 i = F2 i) ->
  mvector_of_fun k F1 = mvector_of_fun k F2.
Proof. by move=> eq_uv; apply/mvectorP => i; rewrite !mvE eq_uv. Qed.

End ProdVectorDef2.

Arguments eq_mv {I E k} [F1] F2 eq_F12.

HB.instance Definition _ {I : finType} (E : I -> eqType) := [Equality of mvector E by <:].
HB.instance Definition _ {I : finType} (E : I -> choiceType) := [Choice of mvector E by <:].
HB.instance Definition _ {I : finType} (E : I -> countType) := [Countable of mvector E by <:].
HB.instance Definition _ {I : finType} (E : I -> finType) := [Finite of mvector E by <:].

Lemma card_mv (I: finType) (E: I -> finType) :
  #|mvector E| = #|{dffun forall i : I, E i}|.
Proof. by rewrite card_sub. Qed.

Notation "\mvector_ ( i : I ) E" := (mvector_of_fun mvector_key (fun i : I => E))
  (at level 36, E at level 36, i, I at level 50): ring_scope.

(* ==================================================================== *)
Section ProdVectorZmod.
Context {I : finType} (E : I -> zmodType).

Implicit Types u v w : mvector E.

Definition mvector_zero     := \mvector_(i : I) (0 : E i).
Definition mvector_add  u v := \mvector_(i : I) (u i + v i).
Definition mvector_opp  u   := \mvector_(i : I) -u i.

Program Definition mvector_zmodMixin := @GRing.isZmodule.Build (mvector E)
  mvector_zero mvector_opp mvector_add _ _ _ _.

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

HB.instance Definition _ := mvector_zmodMixin.

Lemma mv_sumE T (P : pred T) (F : T -> mvector E) (r : seq T) i :
  (\sum_(x <- r | P x) F x) i = \sum_(x <- r | P x) F x i.
Proof. by elim/big_rec2: _ => /= [|x _ s Px <-]; rewrite mvE. Qed.

End ProdVectorZmod.

(* ==================================================================== *)
Section ProdVectorLmodType.
Context {A : ringType} {I : finType} (E : I -> lmodType A).

Implicit Types u v w : mvector E.

Definition mvector_scale (c : A) u :=
  \mvector_(i : I) (c *: u i).

Program Definition mvector_lmodMixin := @GRing.Zmodule_isLmodule.Build A (mvector E)
  mvector_scale _ _ _ _.

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

HB.instance Definition _ := mvector_lmodMixin.

Lemma scalemvE (c : A) (u : forall i, E i) :
  c *: \mvector_(i : I) u i = \mvector_(i : I) (c *: u i).
Proof. by apply/mvectorP=> i; rewrite !mvE. Qed.

End ProdVectorLmodType.

(* -------------------------------------------------------------------- *)
Import VectorInternalTheory.

Section ProdVectorVectType.
Context {I : finType} {k : fieldType} (E : I -> vectType k).

Let Z := {i : I & 'I_(dim (E i))}.

Let S {i : I} (x : 'I_(dim (E i))) : Z := Tagged _ x.

Let D := (\sum_i dim (E i))%N.

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
  r2v (\row_(j < dim (E i)) x 0 (enum_rank (S j))).
exists (fun x => \mvector_(i : I) gr i x) => [g|r].
- apply/mvectorP=> i; rewrite mvE /fr /gr.
  set r := (X in r2v X); suff ->: r = v2r (g i) by rewrite v2rK.
  by apply/rowP=> j; rewrite !mxE enum_rankK /=.
- apply/rowP=> j; rewrite !mxE !mvE r2vK mxE; congr (_ _ _).
  by apply/(canLR enum_valK)/esym/eqP; rewrite eq_Tagged.
Qed.

HB.instance Definition _ := Lmodule_hasFinDim.Build k (mvector E) mvector_vect_iso.

End ProdVectorVectType.
