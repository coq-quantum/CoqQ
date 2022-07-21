(*-------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
From mathcomp.analysis Require Import boolp.

(* -------------------------------------------------------------------- *)
Import Order Order.Theory.

Local Open Scope nat_scope.
Local Open Scope order_scope.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Obligation Tactic := move=> /=.

(* -------------------------------------------------------------------- *)
Definition chain {d : unit} [T : porderType d] (c : nat -> T) :=
  forall i : nat, c i <= c i.+1.

(* -------------------------------------------------------------------- *)
Section ChainTheory.
Context {d : unit} {T : porderType d}.

Lemma chain_shift (c : nat -> T) : chain c -> chain (c \o succn).
Proof. by move=> ch_c i /=; apply: ch_c. Qed.

Lemma chain_homo (c : nat -> T) :
  chain c -> {homo c : x y / (x <= y)%N >-> (x <= y)}.
Proof.
move=> cc x y /subnK => <-; elim: (y - x) => //= n ih.
by rewrite addSn; apply: (le_trans ih); apply: cc.
Qed.
End ChainTheory.

(* -------------------------------------------------------------------- *)
Module Cpo.
Section ClassDef.

Record mixin_of
  (T0 : Type) (b : POrder.class_of T0) (T := POrder.Pack tt b) := Mixin 
{
  bot : T;
  lub : (nat -> T) -> T;
  _   : forall x, bot <= x;
  _   : forall c : nat -> T, chain c -> forall i, c i <= lub c;
  _   : forall c : nat -> T, chain c -> forall x, (forall i, c i <= x) -> lub c <= x;
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @POrder.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation cpoType  := type.
Notation CpoType T m := (@pack T _ _ _ id m).
Notation "[ 'cpoType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'cpoType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'cpoType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'cpoType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'cpoType' 'of' T ]" := [cpoType of T for _]
  (at level 0, format "[ 'cpoType'  'of'  T ]") : form_scope.
Notation "[ 'cpoType' 'of' T 'with' disp ]" :=
  [cpoType of T for _ with disp]
  (at level 0, format "[ 'cpoType'  'of'  T  'with' disp ]") : form_scope.
End Exports.
End Cpo.

Export Cpo.Exports.

Definition bot {disp : unit} {T : cpoType disp} : T :=
  Cpo.bot (Cpo.class T).

Definition lub {disp : unit} {T : cpoType disp} (c : nat -> T) : T :=
  Cpo.lub (Cpo.class T) c.

(* -------------------------------------------------------------------- *)
Module CpoMixin.
Section CpoMixin.
Context {disp : unit} (T : porderType disp).

Record of_ := Build {
  bot       : T;
  lub       : (nat -> T) -> T;
  le0c      : forall x, bot <= x;
  lub_ub    : forall c : nat -> T, chain c -> forall i, c i <= lub c;
  lub_least : forall c : nat -> T, chain c -> forall x, (forall i, c i <= x) -> lub c <= x;
}.

Definition cpoMixin (m : of_) :=
  @Cpo.Mixin _ _ (bot m) (lub m) (le0c m) (lub_ub m) (lub_least m).
End CpoMixin.

Module Exports.
Coercion cpoMixin : of_ >-> Cpo.mixin_of.
Notation cpoMixin := of_.
Notation CpoMixin := Build.
End Exports.
End CpoMixin.

Import CpoMixin.Exports.

(* -------------------------------------------------------------------- *)
Section CPOTheory.
Context {d : unit} {T : cpoType d}.

Lemma le0c (x : T) : bot <= x.
Proof. by case: T x => ? [? []]. Qed.

Hint Extern 0 (is_true (bot <= _)) => (exact: le0c) : core.

Lemma lub_ub (c : nat -> T): chain c -> forall i, c i <= lub c.
Proof. by case: T c => ? [? []]. Qed.

Lemma lub_least (c : nat -> T):
  chain c -> forall x, (forall i, c i <= x) -> lub c <= x.
Proof. by case: T c => ? [? []]. Qed.

Lemma lub_shift (c : nat -> T): chain c -> lub (c \o succn) = lub c.
Proof.
move=> sc_c; rewrite (rwP eqP) eq_le; apply/andP; split.
- apply: lub_least; first by apply: chain_shift.
  by move=> i /=; apply: lub_ub.
- apply: lub_least => // -[|n].
  - by apply/(le_trans (sc_c 0%N))/lub_ub/chain_shift.
  - by apply/lub_ub/chain_shift.
Qed.
End CPOTheory.

(* -------------------------------------------------------------------- *)
Module ScottContinuous.
Section ClassDef.
Context {dU dV : unit} (U : cpoType dU) (V : cpoType dV).

Definition axiom (f : U -> V) :=
  [/\ forall c, chain c -> chain (f \o c)
    & forall c, chain c -> f (lub c) = lub (f \o c)].

Structure map (phUV : phant (U -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation scott f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Scott fA := (Pack (Phant _) fA).
Notation "{ 'scott' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'scott'  fUV }") : order_scope.
Notation "[ 'scott' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'scott'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'scott' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'scott'  'of'  f ]") : form_scope.
End Exports.
End ScottContinuous.

Include ScottContinuous.Exports.

(* -------------------------------------------------------------------- *)
Section SCTheory.
Context {dT dU : unit} {T : cpoType dT} {U : cpoType dU} (f : {scott T -> U}).

Lemma sc_chain c : chain c -> chain (f \o c).
Proof. by move: c; case: f => ? []. Qed.

Lemma sc_lub c : chain c -> f (lub c) = lub (f \o c).
Proof. by move: c; case: f => ? []. Qed.

Lemma homo_sc : {homo f : x y / x <= y}.
Proof.
move=> x y le_xy; pose c n := if n is 0 then x else y.
by have/(_ 0): chain (f \o c) by apply: sc_chain; case.
Qed.
End SCTheory.

(* -------------------------------------------------------------------- *)
Section LFP.
Context {d : unit} {T : cpoType d} (f : {scott T -> T}).

Definition chaini i := iter i f bot.

Lemma chain_iter : chain chaini.
Proof. by elim=> [|n ih]; [apply: le0c | apply: homo_sc]. Qed.

Lemma chaini_shift : chaini \o succn = f \o chaini.
Proof. by []. Qed.

Hint Extern 0 (chain chaini) => (exact: chain_iter) : core.

Lemma fp_lub_chaini : f (lub chaini) = lub chaini.
Proof. by rewrite sc_lub // -chaini_shift lub_shift. Qed.

Lemma least_fp_lub_chaini x : f x = x -> lub chaini <= x.
Proof.
move=> fp_x; apply: lub_least => //.
elim=> /= [|n ih]; first by apply: le0c.
by rewrite -fp_x; apply: homo_sc.
Qed.
End LFP.

(* -------------------------------------------------------------------- *)
Section PointedCPO.
Definition pointed (T : Type) := option T.

Canonical pointed_eqType     (T : eqType    ) := [eqType     of pointed T].
Canonical pointed_choiceType (T : choiceType) := [choiceType of pointed T].
Canonical pointed_countType  (T : countType ) := [countType  of pointed T].

Section Def.
Context {T : choiceType}.

Definition ple (x y : pointed T) : bool :=
  x \in [:: None; y].

Definition plt (x y : pointed T) : bool :=
  ~~ x && y.

Program Definition pointed_lePOrderMixin : lePOrderMixin _ :=
  @LePOrderMixin _ ple plt _ _ _ _.

Next Obligation.
move=> x y; rewrite /ple /plt mem_seq2.
by case: x y => [x|] [y|] //=; rewrite eq_sym andNb.
Qed.

Next Obligation.
by case=> // x; rewrite /ple mem_seq2 eqxx orbT.
Qed.

Next Obligation.
by case=> [x|] [y|] //=; rewrite /ple !mem_seq2 !orFb => /andP [] /eqP.
Qed.

Next Obligation.
case=> [y|] [x|] [z|] //=; rewrite /ple !mem_seq2.
by rewrite !orFb => /eqP[->] /eqP[->].
Qed.

Canonical pointed_POrderType :=
  POrderType NatOrder.nat_display (pointed T) pointed_lePOrderMixin.

Lemma pleE (x y : pointed T) : (x <= y) = ple x y.
Proof. by []. Qed.

Lemma pltE (x y : pointed T) : (x < y) = plt x y.
Proof. by []. Qed.

Lemma ple_Some (x y : T) : (Some x <= Some y :> pointed T) = (x == y).
Proof.
apply/idP/eqP => [|->//]; rewrite pleE.
by rewrite /ple mem_seq2 orFb => /eqP[].
Qed.

Definition pbot : pointed T := None.

Definition plub (c : nat -> pointed T) : pointed T :=
  if pselect (chain c) then
    if pselect (exists i, c i != None) is left h then
      c (xchoose h) else None
  else None.

Lemma pbot_bot (x : pointed T) : pbot <= x.
Proof. by []. Qed.

Lemma pchainP (c : nat -> pointed T) : chain c <->
  (exists2 i,
       (forall j, (j <  i)%N -> c j = None)
     & (forall j, (j >= i)%N -> c j = c i)).
Proof. split; last first.
- case=> i lti gei j; case: (ltnP j i); first by move=> /lti ->.
  by move=> le_ij; rewrite !gei // (leq_trans le_ij).
move=> cc; case: (pselect (exists i : nat, c i != None)); last first.
- move=> h; have cE: forall j, c j = None.
  - move=> j; apply/eqP; rewrite -[_ == _]negbK.
    by apply/negP => ?; apply: h; exists j.
  by exists 0 => // j _; rewrite !cE.
move=> h; exists (ex_minn h) => j.
- case: ex_minnP=> m cmE hmin; apply: contraTeq.
  by move/hmin; rewrite leqNgt.
- case: ex_minnP=> m; case cmE: (c m) => [x|] //.
  move=> _ hmin le_mj; have: (Some x <= c j :> pointed T).
  - by rewrite -cmE; apply: chain_homo.
  by case: (c j) => //= y; rewrite ple_Some => /eqP->.
Qed.

Program Definition pointed_cpo : Cpo.mixin_of _ :=
  @CpoMixin _ _ pbot plub _ _ _.

Next Obligation. by []. Qed.

Next Obligation.
move=> c /[dup] cc /pchainP[i lti gei] j; case: (ltnP j i).
- by move/lti=> ->; apply: pbot_bot.
move/gei=> ->; case ciE: (c i) => [x|] //; rewrite /plub.
case: pselect => //= _; case: pselect => /=; last first.
- by case; exists i; rewrite ciE.
move=> h; set k := xchoose _; suff: (i <= k)%N.
- by move/gei=> ->; rewrite ciE.
rewrite leqNgt; apply/negP=> /lti ckE.
by move: (xchooseP h); rewrite ckE eqxx.
Qed.

Next Obligation.
move=> c /[dup] cc /pchainP[i lti gei] x ub_x.
by rewrite /plub; case: pselect => //= _; case: pselect.
Qed.

Canonical pointed_cpoType := CpoType (pointed T) pointed_cpo.

Lemma plubE (c : nat -> pointed T) : chain c -> lub c =
  if pselect (exists i, c i != None) is left h then
    c (ex_minn h)
  else bot.
Proof.
move=> cc; rewrite /lub /= /plub; case: pselect => //= _.
case: pselect => // h; case: ex_minnP=> m cmE hmin.
have /hmin /(chain_homo cc) {hmin} := xchooseP h.
case: (c m) cmE => // x _; case: (c _) => // y.
by rewrite ple_Some => /eqP ->.
Qed.
End Def.
End PointedCPO.
