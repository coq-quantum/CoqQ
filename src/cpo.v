(*--------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Import boolp.

(* -------------------------------------------------------------------- *)
Import Order Order.Theory.

(************************************************************************)
(*                 CPO (complete partial order) Theory                  *)
(* -------------------------------------------------------------------- *)
(*            cpoType d == the type of complete partial ordered types   *)
(*                         The HB class is Cpo                          *)
(*     { scott U -> V } == the type of scott continuous function over   *)
(*                         cpoType U and V                              *)
(************************************************************************)

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

HB.mixin Record isCpo (d : unit) T of POrder d T := {
  bot  : T;
  lub  : (nat -> T) -> T;
  le0c : forall x, bot <= x;
  lub_ub :
    forall c : nat -> T, chain c -> forall i, c i <= lub c;
  lub_least :
    forall c : nat -> T, chain c -> forall x, (forall i, c i <= x) -> lub c <= x;
}.

#[short(type="cpoType")]
HB.structure Definition Cpo (d : unit):=
  { T of POrder d T & isCpo d T }.

Module CpoExports.
#[deprecated(since="mathcomp 2.0.0", note="Use Cpo.clone instead.")]
Notation "[ 'cpoType' 'of' T 'for' cT ]" := (Cpo.clone _ T%type cT)
  (at level 0, format "[ 'cpoType'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Cpo.clone instead.")]
Notation "[ 'cpoType' 'of' T 'for' cT 'with' disp ]" := (Cpo.clone disp T%type cT)
  (at level 0, format "[ 'cpoType'  'of'  T  'for'  cT  'with'  disp ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Cpo.clone instead.")]
Notation "[ 'cpoType' 'of' T ]" := (Cpo.clone _ T%type _)
  (at level 0, format "[ 'cpoType'  'of'  T ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Cpo.clone instead.")]
Notation "[ 'cpoType' 'of' T 'with' disp ]" := (Cpo.clone disp T%type _)
  (at level 0, format "[ 'cpoType'  'of'  T  'with' disp ]") : form_scope.
End CpoExports.
HB.export CpoExports.

(* -------------------------------------------------------------------- *)
Section CpoTheory.
Context {d : unit} {T : cpoType d}.

(*
Hint Extern 0 (is_true (bot <= _)) => (exact: le0c) : core.
*)

Lemma lub_shift (c : nat -> T): chain c -> lub (c \o succn) = lub c.
Proof.
move=> sc_c; rewrite (rwP eqP) eq_le; apply/andP; split.
- apply: lub_least; first by apply: chain_shift.
  by move=> i /=; apply: lub_ub.
- apply: lub_least => // -[|n].
  - by apply/(le_trans (sc_c 0%N))/lub_ub/chain_shift.
  - by apply/lub_ub/chain_shift.
Qed.
End CpoTheory.

(* -------------------------------------------------------------------- *)

Definition scott dU dV (U : cpoType dU) (V : cpoType dV) (f : U -> V) :=
  [/\ forall c, chain c -> chain (f \o c)
    & forall c, chain c -> f (lub c) = lub (f \o c)].

HB.mixin Record isScottContinuous dU dV (U : cpoType dU) (V : cpoType dV) (apply : U -> V) := {
  scott_subproof : scott apply;
}.

(* #[mathcomp(axiom="scott")] *)
HB.structure Definition ScottContinuous dU dV (U : cpoType dU) (V : cpoType dV) :=
  {f of isScottContinuous dU dV U V f}.

Module ScottContinuousExports.
Module ScottContinuous.
Definition apply_deprecated dU dV (U : cpoType dU) (V : cpoType dV) (phUV : phant (U -> V)) :=
  @ScottContinuous.sort dU dV U V.
#[deprecated(since="mathcomp 2.0", note="Use ScottContinuous.sort instead.")]
Notation apply := apply_deprecated.
End ScottContinuous.
Notation "{ 'scott' U -> V }" := (ScottContinuous.type U%type V%type) (at level 0, U at level 98, V at level 99,
format "{ 'scott'  U  ->  V }") : type_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ScottContinuous.clone instead.")]
Notation "[ 'scott' 'of' f 'as' g ]" := (ScottContinuous.clone _ _ _ _ f%function g)
  (at level 0, format "[ 'scott'  'of'  f  'as'  g ]") : form_scope.
  #[deprecated(since="mathcomp 2.0.0", note="Use ScottContinuous.clone instead.")]
Notation "[ 'scott' 'of' f ]" := (ScottContinuous.clone _ _ _ _ f%function _)
  (at level 0, format "[ 'scott'  'of'  f ]") : form_scope.
End ScottContinuousExports.
HB.export ScottContinuousExports.

(* -------------------------------------------------------------------- *)
Section SCTheory.
Context {dT dU : unit} {T : cpoType dT} {U : cpoType dU} (f : {scott T -> U}).

Lemma sc_scott : scott f.
Proof. exact: scott_subproof. Qed.

Lemma sc_chain c : chain c -> chain (f \o c).
Proof. by move: c; case: sc_scott. Qed.

Lemma sc_lub c : chain c -> f (lub c) = lub (f \o c).
Proof. by move: c; case: sc_scott. Qed.

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
Module Pointed.
Section Pointed.

Definition pointed (T : Type) := option T.

HB.instance Definition _ (T : eqType) := Equality.on (pointed T).
HB.instance Definition _ (T : choiceType) := Choice.on (pointed T).
HB.instance Definition _ (T : countType) := Countable.on (pointed T).

Section POrder.

Variable T : choiceType.

Definition ple (x y : pointed T) : bool :=
  x \in [:: None; y].

Definition plt (x y : pointed T) : bool :=
  ~~ x && y.

Lemma plt_def : forall (x y : pointed T), plt x y = (y != x) && (ple x y).
Proof.
move=> x y; rewrite /ple /plt mem_seq2.
by case: x y => [x|] [y|] //=; rewrite eq_sym andNb.
Qed.

Lemma ple_refl : reflexive ple.
Proof.
by case=> // x; rewrite /ple mem_seq2 eqxx orbT.
Qed.

Lemma ple_anti : antisymmetric ple.
Proof.
by case=> [x|] [y|] //=; rewrite /ple !mem_seq2 !orFb => /andP [] /eqP.
Qed.

Lemma ple_trans : transitive ple.
Proof.
case=> [y|] [x|] [z|] //=; rewrite /ple !mem_seq2.
by rewrite !orFb => /eqP[->] /eqP[->].
Qed.

HB.instance Definition _ :=
  isPOrder.Build NatOrder.nat_display (pointed T)
    plt_def ple_refl ple_anti ple_trans.

Lemma pleE (x y : pointed T) : (x <= y) = ple x y.
Proof. by []. Qed.
  
Lemma pltE (x y : pointed T) : (x < y) = plt x y.
Proof. by []. Qed.

Lemma ple_Some (x y : T) : (Some x <= Some y :> pointed T) = (x == y).
Proof.
apply/idP/eqP => [|->//]; rewrite pleE.
by rewrite /ple mem_seq2 orFb => /eqP[].
Qed.

End POrder.

Section Cpo.

Variable T : choiceType.

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
(* 
Lemma le0c : forall (x : pointed T), pbot <= x. *)

Lemma plub_ub :
  forall c : nat -> pointed T, chain c -> forall i : nat, c i <= plub c.
Proof.
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

Lemma plub_least :
  forall c : nat -> pointed T,
    chain c -> forall x, (forall i, c i <= x) -> plub c <= x.
Proof.
move=> c /[dup] cc /pchainP[i lti gei] x ub_x.
by rewrite /plub; case: pselect => //= _; case: pselect.
Qed.

HB.instance Definition _ :=
  isCpo.Build NatOrder.nat_display (pointed T)
    pbot_bot plub_ub plub_least.

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

End Cpo.

End Pointed.

End Pointed. 
