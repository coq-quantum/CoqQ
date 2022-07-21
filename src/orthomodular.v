(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Import Order Order.LTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* note that the complement here is different from that in order *)

(* complement top bottom lattice *)
Module ComplLattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : TBLattice.class_of T0)
                (T := TBLattice.Pack tt b) := Mixin {
  compl : T -> T;
  _ : forall a, join (compl a) a = top;
  _ : forall a, meet (compl a) a = bottom;
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : TBLattice.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> TBLattice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@TBLattice.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> TBLattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Notation complLatticeType  := type.
Notation ComplLatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'complLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'complLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'complLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'complLatticeType'  'of'  T  'for'  cT  'with'  disp ]")
  : form_scope.
Notation "[ 'complLatticeType' 'of' T ]" := [complLatticeType of T for _]
  (at level 0, format "[ 'complLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'complLatticeType' 'of' T 'with' disp ]" :=
  [complLatticeType of T for _ with disp]
  (at level 0, format "[ 'complLatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End ComplLattice.
Export ComplLattice.Exports.

Definition compl {disp : unit} {T : complLatticeType disp} : T -> T :=
  ComplLattice.compl (ComplLattice.class T).

Module Import CTBLatticeSyntax.
Notation "~` A" := (compl A) : order_scope.
End CTBLatticeSyntax.

(* orthocomplement lattice *)
Module OComplLattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : ComplLattice.class_of T0)
                (T := ComplLattice.Pack tt b) := Mixin {
  _ : involutive (@compl _ T);
  _ : {homo (@compl _ T) : a b /~ a <= b};
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : ComplLattice.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> ComplLattice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@ComplLattice.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition complLatticeType := @ComplLattice.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> ComplLattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion complLatticeType : type >-> ComplLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Canonical complLatticeType.
Notation oComplLatticeType  := type.
Notation OComplLatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'oComplLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'oComplLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'oComplLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'oComplLatticeType'  'of'  T  'for'  cT  'with'  disp ]")
  : form_scope.
Notation "[ 'oComplLatticeType' 'of' T ]" := [oComplLatticeType of T for _]
  (at level 0, format "[ 'oComplLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'oComplLatticeType' 'of' T 'with' disp ]" :=
  [oComplLatticeType of T for _ with disp]
  (at level 0, format "[ 'oComplLatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End OComplLattice.
Export OComplLattice.Exports.

(* orthomodular lattice *)
Module OModularLattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : OComplLattice.class_of T0)
                (T := OComplLattice.Pack tt b) := Mixin {
  _ : forall a b : T, a <= b -> join a (meet (compl a) b) = b;
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : OComplLattice.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> OComplLattice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@OComplLattice.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition complLatticeType := @ComplLattice.Pack disp cT class.
Definition oComplLatticeType := @OComplLattice.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> OComplLattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion complLatticeType : type >-> ComplLattice.type.
Coercion oComplLatticeType : type >-> OComplLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Canonical complLatticeType.
Canonical oComplLatticeType.
Notation oModularLatticeType  := type.
Notation OModularLatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'oModularLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'oModularLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'oModularLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'oModularLatticeType'  'of'  T  'for'  cT  'with'  disp ]")
  : form_scope.
Notation "[ 'oModularLatticeType' 'of' T ]" := [oModularLatticeType of T for _]
  (at level 0, format "[ 'oModularLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'oModularLatticeType' 'of' T 'with' disp ]" :=
  [oModularLatticeType of T for _ with disp]
  (at level 0, format "[ 'oModularLatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End OModularLattice.
Export OModularLattice.Exports.

(* orthomodular lattice *)
Module ModularLattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : OModularLattice.class_of T0)
                (T := OModularLattice.Pack tt b) := Mixin {
  _ : forall a b c : T, a <= c -> join a (meet b c) = meet (join a b) c;
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : OModularLattice.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> OModularLattice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@OModularLattice.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
Definition latticeType := @Lattice.Pack disp cT class.
Definition bLatticeType := @BLattice.Pack disp cT class.
Definition tbLatticeType := @TBLattice.Pack disp cT class.
Definition complLatticeType := @ComplLattice.Pack disp cT class.
Definition oComplLatticeType := @OComplLattice.Pack disp cT class.
Definition oModularLatticeType := @OModularLattice.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> OModularLattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion complLatticeType : type >-> ComplLattice.type.
Coercion oComplLatticeType : type >-> OComplLattice.type.
Coercion oModularLatticeType : type >-> OModularLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Canonical complLatticeType.
Canonical oComplLatticeType.
Canonical oModularLatticeType.
Notation modularLatticeType  := type.
Notation ModularLatticeType T m := (@pack T _ _ _ id m).
Notation "[ 'modularLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'modularLatticeType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'modularLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0,
   format "[ 'modularLatticeType'  'of'  T  'for'  cT  'with'  disp ]")
  : form_scope.
Notation "[ 'modularLatticeType' 'of' T ]" := [modularLatticeType of T for _]
  (at level 0, format "[ 'modularLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'modularLatticeType' 'of' T 'with' disp ]" :=
  [modularLatticeType of T for _ with disp]
  (at level 0, format "[ 'modularLatticeType'  'of'  T  'with' disp ]") :
  form_scope.
End Exports.

End ModularLattice.
Export ModularLattice.Exports.

Export CTBLatticeSyntax.

Section LatticeExtra.
Variable (disp : unit) (T : latticeType disp).
Implicit Type (x y z : T).

Lemma le_joinl z : {homo (join z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leU2. Qed.

Lemma le_joinr z : {homo (join^~ z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leU2. Qed.

Lemma lt_joinl z : {homo (join z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leU2=>//; apply ltW. Qed.

Lemma lt_joinr z : {homo (join^~ z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leU2=>//; apply ltW. Qed.

Lemma le_meetl z : {homo (meet z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leI2. Qed.

Lemma le_meetr z : {homo (meet^~ z) : x y / x <= y}.
Proof. by move=>x y Pxy; apply: leI2. Qed.

Lemma lt_meetl z : {homo (meet z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leI2=>//; apply ltW. Qed.

Lemma lt_meetr z : {homo (meet^~ z) : x y / x < y >-> x <= y}.
Proof. by move=>x y Pxy; apply: leI2=>//; apply ltW. Qed.

End LatticeExtra.


(* add theories later *)

Section ComplLatticeTheory.
Variable (disp : unit) (T : complLatticeType disp).
Implicit Type (x y : T).

Lemma joinCx x : ~` x `|` x = 1.
Proof. by move: x; case: T=>?[?[???]]. Qed.
Lemma meetCx x : ~` x `&` x = 0.
Proof. by move: x; case: T=>?[?[???]]. Qed.

Lemma joinxC x : x `|` ~` x = 1.
Proof. by rewrite joinC joinCx. Qed.
Lemma meetxC x : x `&` ~` x = 0.
Proof. by rewrite meetC meetCx. Qed.

Lemma compl1 : ~` 1 = 0 :> T.
Proof. by rewrite -(meetxC 1) meet1x. Qed.

Lemma compl0 : ~` 0 = 1 :> T.
Proof. by rewrite -(joinCx 0) joinx0. Qed.

End ComplLatticeTheory.

Section OComplLatticeTheory.
Variable (disp : unit) (T : oComplLatticeType disp).
Implicit Type (x y : T).

Lemma complK : involutive (@compl _ T).
Proof. by case: T=>?[?[??]]. Qed.

Lemma leCP : {homo (@compl _ T) : a b /~ a <= b}.
Proof. by case: T=>?[?[??]]. Qed.

Lemma leC : {mono (@compl _ T) : a b /~ a <= b}.
Proof.
move=>a b; apply/Bool.eq_iff_eq_true; split.
rewrite -{2}(complK b) -{2}(complK a).
all: apply leCP.
Qed.

Lemma lexC x y : x <= ~` y = (y <= ~` x).
Proof. by rewrite -leC complK. Qed.

Lemma leCx x y : ~` x <= y = (~` y <= x).
Proof. by rewrite -leC complK. Qed.

Lemma compl_inj : injective (@compl _ T).
Proof. exact: (can_inj complK). Qed.

Lemma complU x y : ~` (x `|` y) = ~` x `&` ~` y.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
by rewrite lexI !leC ?leUl ?leUr.
by rewrite -leC complK leUx lexC leIl lexC leIr.
Qed.

Lemma complI  x y : ~` (x `&` y) = ~` x `|` ~` y.
Proof. by rewrite -[RHS]complK complU !complK. Qed.

Lemma lexC_disj x y : (x <= ~` y) -> (x `&` y = 0).
Proof. by move/(le_meetr y); rewrite meetCx lex0=>/eqP. Qed.

Lemma ortho_modular : 
  (forall x y z : T, x <= z -> join x (meet y z) = meet (join x y) z) ->
  (forall x y : T, x <= y -> join x (meet (compl x) y) = y).
Proof. by move=>P1 x y /P1 P2; move: (P2 (~` x))=>->; rewrite joinxC meet1x. Qed.

End OComplLatticeTheory.

Section OModularLatticeTheory.
Variable (disp : unit) (T : oModularLatticeType disp).
Implicit Type (x y : T).

Lemma le_joinIC x y : x <= y -> join x (meet (compl x) y) = y.
Proof. by move: x y; case: T=>?[?[?]]. Qed.

End OModularLatticeTheory.

Section ModularLatticeTheory.
Variable (disp : unit) (T : modularLatticeType disp).
Implicit Type (x y z : T).

Lemma le_joinI x y z : x <= z -> join x (meet y z) = meet (join x y) z.
Proof. by move: x y z; case: T=>?[?[?]]. Qed.

End ModularLatticeTheory.











Module ComplLatticeMixin.
Section ComplLatticeMixin.
Variable (disp : unit) (T : tbLatticeType disp).

Record of_ := Build {
  compl : T -> T;
  joinCx : forall a, join (compl a) a = top;
  meetCx : forall a, meet (compl a) a = bottom;
}.
Definition complLatticeMixin (m : of_) := @ComplLattice.Mixin _ _ (compl m) (joinCx m) (meetCx m).

End ComplLatticeMixin.

Module Exports.
Coercion complLatticeMixin : of_ >-> ComplLattice.mixin_of.
Notation complLatticeMixin := of_.
Notation ComplLatticeMixin := Build.
End Exports.

End ComplLatticeMixin.

Export ComplLatticeMixin.Exports.

Module OComplLatticeMixin.
Section OComplLatticeMixin.
Variable (disp : unit) (T : complLatticeType disp).

Record of_ := Build {
  complK  : involutive (@compl _ T);
  leC : {homo (@compl _ T) : a b /~ a <= b};
}.
Definition oComplLatticeMixin (m : of_) := @OComplLattice.Mixin _ _ (complK m) (leC m).

End OComplLatticeMixin.

Module Exports.
Coercion oComplLatticeMixin : of_ >-> OComplLattice.mixin_of.
Notation oComplLatticeMixin := of_.
Notation OComplLatticeMixin := Build.
End Exports.

End OComplLatticeMixin.
Export OComplLatticeMixin.Exports.

Module OModularLatticeMixin.
Section OModularLatticeMixin.
Variable (disp : unit) (T : oComplLatticeType disp).

Record of_ := Build {
  le_joinIC  : forall a b : T, a <= b -> join a (meet (compl a) b) = b;
}.
Definition oModularLatticeMixin (m : of_) := @OModularLattice.Mixin _ _ (le_joinIC m).

End OModularLatticeMixin.

Module Exports.
Coercion oModularLatticeMixin : of_ >-> OModularLattice.mixin_of.
Notation oModularLatticeMixin := of_.
Notation OModularLatticeMixin := Build.
End Exports.

End OModularLatticeMixin.
Export OModularLatticeMixin.Exports.

Module ModularLatticeMixin.
Section ModularLatticeMixin.
Variable (disp : unit) (T : oModularLatticeType disp).

Record of_ := Build {
  le_joinI : forall a b c : T, a <= c -> join a (meet b c) = meet (join a b) c;
}.
Definition modularLatticeMixin (m : of_) := @ModularLattice.Mixin _ _ (le_joinI m).

End ModularLatticeMixin.

Module Exports.
Coercion modularLatticeMixin : of_ >-> ModularLattice.mixin_of.
Notation modularLatticeMixin := of_.
Notation ModularLatticeMixin := Build.
End Exports.

End ModularLatticeMixin.
Export ModularLatticeMixin.Exports.

(* on latticeType, build complLattice oComplLattice *)
Module OComplMixin.
Section OComplMixin.
Variable (disp : unit) (T : tbLatticeType disp).

Record of_ := Build {
  compl : T -> T;
  joinCx : forall a, join (compl a) a = top;
  meetCx : forall a, meet (compl a) a = bottom;
  complK  : involutive compl;
  leC : {homo compl : a b /~ a <= b};
}.
Variable (m : of_).

Definition complMixin := ComplLatticeMixin (joinCx m) (meetCx m).

Let T_complLattice := ComplLatticeType T complMixin.

Definition oComplMixin := 
  @OComplLatticeMixin _ T_complLattice (complK m) (leC m).

End OComplMixin.

Module Exports.
Coercion oComplMixin : of_ >-> OComplLatticeMixin.of_.
Coercion complMixin : of_ >-> ComplLatticeMixin.of_.
Notation oComplMixin := of_.
Notation OComplMixin := Build.
End Exports.

End OComplMixin.
Export OComplMixin.Exports.

(* build on orthocompl, since modular law is stronger than orthomodular law *)
Module ModularMixin.
Section ModularMixin.
Variable (disp : unit) (T : oComplLatticeType disp).

Record of_ := Build {
  le_joinI : forall a b c : T, a <= c -> join a (meet b c) = meet (join a b) c;
}.
Variable (m : of_).
Definition oModularMixin := OModularLatticeMixin (ortho_modular (le_joinI m)).

Let T_oModularLattice := OModularLatticeType T oModularMixin.

Definition modularMixin :=
  @ModularLatticeMixin.Build _ T_oModularLattice (le_joinI m).

End ModularMixin.

Module Exports.
Coercion modularMixin : of_ >-> ModularLatticeMixin.of_.
Coercion oModularMixin : of_ >-> OModularLatticeMixin.of_.
Notation modularMixin := of_.
Notation ModularMixin := Build.
End Exports.

End ModularMixin.
Export ModularMixin.Exports.
