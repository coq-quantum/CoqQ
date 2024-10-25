From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp cardinality mathcomp_extra
  classical_sets functions.
From mathcomp.analysis Require Import ereal reals signed topology function_spaces
  prodnormedzmodule normedtype sequences xfinmap.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import mcextra mcaextra extnum mxpred ctopology notation.

(******************************************************************************)
(*                      Bounded and Summable functions                        *)
(* discrete function maps to normed topological space over real or complex    *)
(*    number.                                                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Import Order Order.Theory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import VNorm.Exports ExtNumTopology.

Reserved Notation "\dlet_ ( i <- d ) E"
  (at level 36, E at level 36, i, d at level 50,
     format "'[' \dlet_ ( i  <-  d ) '/  '  E ']'").

Reserved Notation "\dlim_ ( n ) E"
  (at level 36, E at level 36, n at level 50,
     format "'[' \dlim_ ( n ) '/  '  E ']'").

Reserved Notation "\P_[ mu ] E" (at level 2, format "\P_[ mu ]  E").
Reserved Notation "\P_[ mu , A ] E" (at level 2, format "\P_[ mu ,  A ]  E").
Reserved Notation "\E?_[ mu ] f" (at level 2, format "\E?_[ mu ]  f").
Reserved Notation "\E_[ mu ] f" (at level 2, format "\E_[ mu ]  f").
Reserved Notation "\E_[ mu , A ] f" (at level 2, format "\E_[ mu ,  A ]  f").

Definition normf (I : Type) (K : numDomainType) (V : normedZmodType K) (f : I -> V) :=
  (fun x => `|f x|).
Local Notation "\`| f |" := (normf f) (at level 2).

Lemma normf_ge0 (I : Type) (K : numDomainType) (V : normedZmodType K) (f : I -> V) (i : I) :
  0 <= \`| f | i.
Proof. by rewrite /normf. Qed.
Hint Resolve normf_ge0 : core.

Lemma max_le_l {disp : unit} {T : porderType disp} (x y : T) :
  (x <= Order.max x y)%O.
Proof. by rewrite maxEle; case E: (x <= y)%O. Qed.
Lemma min_le_r {disp : unit} {T : porderType disp} (x y : T) :
  (Order.min x y <= y)%O.
Proof. by rewrite minEle; case E: (x <= y)%O. Qed.

Section totally.

Local Open Scope fset_scope.
(* :TODO: when eventually is generalized to any lattice *)
(* totally can just be replaced by eventually *)
Definition totally {I : choiceType} : set_system {fset I} :=
  filter_from setT (fun A => [set B | A `<=` B]).

Global Instance totally_filter {I : choiceType} : ProperFilter (@totally I).
Proof.
eapply filter_from_proper; last by move=> A _; exists A; rewrite /= fsubset_refl.
apply: filter_fromT_filter; first by exists fset0.
by move=> A B /=; exists (A `|` B) => P /=; rewrite fsubUset => /andP[].
Qed.

Canonical totally_filterType {I : choiceType} := FilterType (@totally I) _.
Canonical totally_pfilterType {I : choiceType} :=
  PFilterType (@totally I) (filter_not_empty _).

Definition psum {I : choiceType} {R : zmodType}
  (x : I -> R) (A : {fset I}) : R := \sum_(i : A) x (val i).

Lemma psumE {I : choiceType} {R : zmodType} (x : I -> R) (A : {fset I}) :
  \sum_(i : A) x (fsval i) = psum x A.
Proof. by []. Qed.

Definition psumr {I : choiceType} (A : {fset I}) 
  {R : zmodType} (x : I -> R) : R := psum x A.

Definition sum (I : choiceType) {K : numFieldType} {R : normedModType K}
   (x : I -> R) : R := lim ((psum x) @ totally).

Definition psum_preset {I : choiceType} {R : zmodType}
  (x : I -> R) := [set y | exists J : {fset I}, y = psum x J ].

End totally.

Section PartialSum.
Context {I : choiceType}.
Implicit Type (R : zmodType).

Lemma psum0 {R} (x : I -> R) : psum x fset0 = 0.
Proof. by rewrite/psum big_fset0. Qed.

Lemma psum1 {R} (i : I) (x : I -> R) : psum x [fset i]%fset = x i.
Proof. by rewrite/psum big_fset1. Qed.

Lemma psumrE {R} (x : I -> R) (A : {fset I}) :
  psum x A = psumr A x.
Proof. by []. Qed.

Lemma psumr_is_additive (A : {fset I}) R : 
  additive (@psumr _ A R).
Proof.
move=>x y; rewrite raddf_sum -big_split.
by apply eq_bigr=>i _; rewrite/= !fctE.
Qed.

HB.instance Definition _ (A : {fset I}) R := GRing.isAdditive.Build
  (I -> R) R (@psumr _ A R) (@psumr_is_additive A R).

Lemma psumr_is_linear (A : {fset I}) (T : ringType) (V : lmodType T) :
  linear (@psumr _ A V).
Proof.
move=>a x y; rewrite raddf_sum -big_split.
by apply eq_bigr=>i _; rewrite/= !fctE {1}/GRing.scale/=.
Qed.

HB.instance Definition _ (A : {fset I}) (T : ringType) (V : lmodType T) := GRing.isLinear.Build
  T (I -> V) V *:%R (@psumr _ A V) (@psumr_is_linear A T V).

Lemma psumD {R} (x y : I -> R) (A : {fset I}) :
  psum (x + y) A = psum x A + psum y A.
Proof. by rewrite !psumrE raddfD. Qed.

Lemma psumN {R} (x : I -> R) (A : {fset I}) :
  psum (- x) A = - psum x A.
Proof. by rewrite !psumrE raddfN. Qed.

Lemma psumB {R} (x y : I -> R) (A : {fset I}) :
  psum (x - y) A = psum x A - psum y A.
Proof. by rewrite !psumrE raddfB. Qed.

Lemma psumZ (T : ringType) (V : lmodType T) (x : I -> V) 
  (A : {fset I}) (a : T) :
  psum (a *: x) A = a *: psum x A.
Proof. by rewrite !psumrE linearZ. Qed.

Lemma psumU {R} (x : I -> R) (A B : {fset I}) :
  [disjoint A & B]%fset -> 
    psum x (A `|` B)%fset = psum x A + psum x B.
Proof. exact: xfinmap.big_fsetU. Qed.

Lemma psumDB {R} (x : I -> R) (A B : {fset I}) :
  psum x (A `\` B)%fset = psum x A - psum x (A `&` B)%fset.
Proof. by rewrite -{2}[A](fsetID B) psumU ?fdisjointID// addrC addKr. Qed.

Lemma psumIB {R} (x : I -> R) (A B : {fset I}) :
  psum x (A `\` B)%fset - psum x (B `\` A)%fset = psum x A - psum x B.
Proof. by rewrite !psumDB opprB fsetIC addrA addrNK. Qed.

Lemma psum_ler_norm (T : numDomainType) (V : normedZmodType T) (x : I -> V) 
  (A : {fset I}) :
  `|psum x A| <= psum \`| x | A.
Proof. exact: ler_norm_sum. Qed.

Lemma psum_ler (T : numDomainType) (x : I -> T) (A B : {fset I}) :
  (forall i, i \in (B `\` A)%fset -> 0 <= x i) -> (A `<=` B)%fset -> psum x A <= psum x B.
Proof.
move=>P P1. rewrite -(fsetUD_sub P1) psumU ?fdisjointXD// lerDl sumr_ge0// =>i _.
by case: i.
Qed. 

Lemma psum_seq_fsetE R (x : I -> R) (A : {fset I}) :
  psum x A = \sum_(i <- A) x i.
Proof. by rewrite/psum big_seq_fsetE. Qed.

Lemma eq_psum R (x y : I -> R) (A B : {fset I}) :
  A =i B -> x =1 y -> psum x A = psum y B.
Proof. by move=>/fsetP-> P2; apply eq_bigr. Qed.

Lemma eq_psuml R (x : I -> R) (A B : {fset I}) :
  A =i B -> psum x A = psum x B.
Proof. by move=>/fsetP->. Qed.

Lemma eq_psumr R (x y : I -> R) (A : {fset I}) :
  x =1 y -> psum x A = psum y A.
Proof. by apply: eq_psum. Qed.

End PartialSum.

(* move *)
Lemma big_fset_seqE (T : Type) (idx : T) (op : Monoid.law idx) (I : choiceType)
  (X : {fset I}) (F : I -> T) :
  \big[op/idx]_(i : X) F (val i) = \big[op/idx]_(x <- X) F x.
Proof. by rewrite big_seq_fsetE. Qed.
Arguments big_fset_seqE [T idx op I] X F.

Definition bounded (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) (f : I -> V) :=
    exists (M : K), forall i, `| f i | <= M.

HB.mixin Record isBounded (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) (apply : I -> V) := {
    bounded_subproof : bounded apply;
}.

(* #[mathcomp(axiom="bounded")] *)
HB.structure Definition Bounded (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) :=
    {f of isBounded I K V f}.

Module BoundedExports.
Module Bounded.
Definition apply_deprecated (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) (phIV : phant (I -> V)) :=
    @Bounded.sort I K V.
#[deprecated(since="mathcomp 2.0", note="Use Bounded.sort instead.")]
Notation apply := apply_deprecated.
Definition build (I : choiceType) (K : numFieldType) (V : normedZmodType K)
  (f : I -> V) (H : bounded f) := Bounded.Pack (Bounded.Class (isBounded.Axioms_ K V f H)).
End Bounded.

Notation "{ 'bounded' I -> V }" := (Bounded.type I%type V%type)
  (at level 0, I at level 98, V at level 99,
format "{ 'bounded'  I  ->  V }") : type_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Bounded.clone instead.")]
Notation "[ 'bounded' 'of' f 'as' g ]" := (Bounded.clone _ _ _ f%function g)
  (at level 0, format "[ 'bounded'  'of'  f  'as'  g ]") : form_scope.
  #[deprecated(since="mathcomp 2.0.0", note="Use Bounded.clone instead.")]
Notation "[ 'bounded' 'of' f ]" := (Bounded.clone _ _ _ f%function _)
  (at level 0, format "[ 'bounded'  'of'  f ]") : form_scope.
End BoundedExports.
HB.export BoundedExports.

HB.instance Definition _ (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) := gen_eqMixin {bounded I -> V}.
HB.instance Definition _ (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) := gen_choiceMixin {bounded I -> V}.

Definition summable (I : choiceType) (K : numFieldType) (V : normedZmodType K)
  (f : I -> V) :=
    exists (M : K), \forall J \near totally, (psum \`| f | J <= M)%R.

HB.mixin Record Bounded_isSummable (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) apply of @Bounded I K V apply := {
  summable_subproof : summable apply;
}.

(* #[mathcomp(axiom="summable")] *)
HB.structure Definition Summable (I : choiceType) (K : numFieldType) (V : normedZmodType K) :=
  {f of @Bounded I K V f & Bounded_isSummable I K V f}.

Lemma bounded_summable (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) (f : I -> V) :
    summable f -> bounded f.
Proof.
move=>[M PM]. exists M=>i.
suff: \forall J \near (@totally I), `|f i| <= M by apply: have_near.
near=>J; apply: (@le_trans _ _ (psum \`| f | J)); near: J; last by apply: PM.
exists [fset i]%fset=>// J/=.
have ->: `|f i| = psum \`|f| [fset i]%fset by rewrite psum1.
by apply: psum_ler.
Unshelve. end_near.
Qed.

HB.factory Record isSummable (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) (f : I -> V) := {
  summable_subproof : summable f;
}.
HB.builders Context I K V f of isSummable I K V f.
HB.instance Definition _ := isBounded.Build I K V f
  (bounded_summable summable_subproof).
HB.instance Definition _ := Bounded_isSummable.Build I K V f summable_subproof.
HB.end.

Module SummableExports.
Module Summable.
Definition apply_deprecated (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) (phIV : phant (I -> V)) :=
    @Summable.sort I K V.
#[deprecated(since="mathcomp 2.0", note="Use Summable.sort instead.")]
Notation apply := apply_deprecated.
Definition build (I : choiceType) (K : numFieldType) (V : normedZmodType K)
  (f : I -> V) (H : summable f) :=
    Summable.Pack (Summable.Class
      (* (@Bounded_isSummable.Build I K V (Bounded.build (bounded_summable H)) H)). *)
      (Bounded_isSummable.Axioms_ V f (isBounded.Axioms_ K V f (bounded_summable H)) H)).    
End Summable.
Notation "{ 'summable' I -> V }" := (Summable.type I%type V%type) (at level 0, I at level 98, V at level 99,
format "{ 'summable'  I  ->  V }") : type_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use Summable.clone instead.")]
Notation "[ 'summable' 'of' f 'as' g ]" := (Summable.clone _ _ _ f%function g)
  (at level 0, format "[ 'summable'  'of'  f  'as'  g ]") : form_scope.
  #[deprecated(since="mathcomp 2.0.0", note="Use Summable.clone instead.")]
Notation "[ 'summable' 'of' f ]" := (Summable.clone _ _ _ f%function _)
  (at level 0, format "[ 'summable'  'of'  f ]") : form_scope.
End SummableExports.
HB.export SummableExports.

HB.instance Definition _ (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) := gen_eqMixin {summable I -> V}.
HB.instance Definition _ (I : choiceType) (K : numFieldType)
  (V : normedZmodType K) := gen_choiceMixin {summable I -> V}.

Section BoundedLmod.
Context {I : choiceType} {K : numFieldType} {V : normedModType K}.
Implicit Type (x y : I -> V) (f g : {bounded I -> V}).

Lemma bounded_funD x y : bounded x -> bounded y -> bounded (x \+ y).
Proof.
move=>[Mx Px][My Py]; exists (Mx + My)=>i/=.
by apply/(le_trans (ler_normD _ _))/lerD.
Qed.

Lemma bounded_funN x : 
  bounded x -> bounded (\- x).
Proof. by move=>[M P]; exists M=>i/=; rewrite normrN. Qed.

Lemma bounded_funZ (a : K) x : bounded x -> bounded (a \*: x).
Proof. by move=>[M P]; exists (`|a|*M)=>i/=; rewrite normrZ ler_wpM2l. Qed.

Lemma bounded_fun_comp (a : I -> K) x : 
  bounded a -> bounded x -> bounded (fun i => a i *: x i).
Proof. by move=>[Ma Pa] [My Py]; exists (Ma * My)=>i/=; rewrite normrZ ler_pM. Qed.

Lemma bounded_zero_subproof : bounded (\0 : I -> V).
Proof. by exists 0=>i/=; rewrite normr0. Qed.
HB.instance Definition bounded_zero_mixin := isBounded.Build I K V \0 bounded_zero_subproof.
Definition bounded_zero := Bounded.build bounded_zero_subproof.

Lemma bounded_cst_subproof (v : V) : bounded (@cst I V v).
Proof. by exists `|v|=>i/=. Qed.

HB.instance Definition _ (v:V) := isBounded.Build I K V (@cst I V v)
  (bounded_cst_subproof v).

Lemma boundedP f g : f = g <-> f =1 g.
Proof.
split=>[->//|]; move: f g=>[]f+[]g+/funext/= eqf;
rewrite eqf=>[[[/=P1]]] [[/=P2]];
by rewrite (Prop_irrelevance P1 P2).
Qed.

Lemma boundedfE x (H : bounded x) : x = Bounded.build H.
Proof. by []. Qed.
Lemma boundedfP f : bounded f. Proof. exact: bounded_subproof. Qed.

Definition bounded_add f g :=
  Bounded.build (bounded_funD (boundedfP f) (boundedfP g)).

Definition bounded_opp f :=
  Bounded.build (bounded_funN (boundedfP f)).

Definition bounded_scale (a : K) f :=
  Bounded.build (bounded_funZ a (boundedfP f)).

Program Definition bounded_zmodMixin :=
  @GRing.isZmodule.Build {bounded I -> V} bounded_zero bounded_opp bounded_add _ _ _ _.
Next Obligation. by move=>f g h; apply/boundedP=> i/=;rewrite addrA. Qed.
Next Obligation. by move=>f g; apply/boundedP=> i/=;rewrite addrC. Qed.
Next Obligation. by move=>f; apply/boundedP=> i/=; rewrite add0r. Qed.
Next Obligation. by move=>f; apply/boundedP=> i/=; rewrite addNr. Qed.
HB.instance Definition _ := bounded_zmodMixin.

Program Definition bounded_lmodMixin
  := @GRing.Zmodule_isLmodule.Build K {bounded I -> V} bounded_scale _ _ _ _.
Next Obligation. by move=>a b f; apply/boundedP=> i/=;rewrite scalerA. Qed.
Next Obligation. by move=>f; apply/boundedP=> i/=; rewrite scale1r. Qed.
Next Obligation. by move=>a f g; apply/boundedP=> i/=; rewrite scalerDr. Qed.
Next Obligation. by move=>a f g; apply/boundedP=> i/=; rewrite scalerDl. Qed.
HB.instance Definition _ := bounded_lmodMixin.

Lemma bounded_addE f g i : (f + g) i = f i + g i.         Proof. by []. Qed.
Lemma bounded_oppE f i : (- f) i = - f i.                 Proof. by []. Qed.
Lemma bounded_scaleE (a : K) f i : (a *: f) i = a *: f i. Proof. by []. Qed.
Lemma bounded_zeroE i : (0 : {bounded I -> V}) i = 0.    Proof. by []. Qed.

Definition boundedE :=
  (bounded_zeroE, bounded_addE, bounded_oppE, bounded_scaleE).

Lemma bounded_fun_norm x : bounded x -> bounded (\`| x | : I -> K).
Proof. by move=>[M PM]; exists M=>i; rewrite normr_id. Qed.

HB.instance Definition _ f := isBounded.Build I K K \`| f | (bounded_fun_norm (boundedfP f)).

End BoundedLmod.

Section SummableLmod.
Context {I : choiceType} {K : numFieldType} {V : normedModType K}.
Implicit Type (x y : I -> V) (f g : {summable I -> V}).

Lemma has_sup_psum_preset x :
    summable x -> has_sup (psum_preset \`| x |).
Proof.
move=>[M PM]; split.
by exists 0=>/=; rewrite/S/=; exists fset0; rewrite /psum big_fset0.
exists M=>z; rewrite/S/==>[[J ->]].
move: PM=>[A _]/(_ (J `|` (A `\` J))%fset)/=.
rewrite {1}fsetUDl fsetDv fsetD0=>/(_ (fsubsetUr _ _)).
apply le_trans.
by rewrite psumU ?fdisjointXD// lerDl /psum sumr_ge0.
Qed.

Lemma summable_funD x y : 
  summable x -> summable y -> summable (x \+ y).
Proof.
move=>[Mx Px][My Py]; exists (Mx + My); near=>J.
suff P1: psum \`| x + y | J <= psum \`| x | J + psum \`| y | J.
apply: (le_trans P1); clear P1; rewrite lerD//; near: J.
apply Px. apply Py.
by rewrite -big_split ler_sum// =>i _; rewrite ler_normD.
Unshelve. end_near.
Qed.

Lemma summable_funN x : 
  summable x -> summable (\- x).
Proof.
move=>[M P]; exists M; near=>J.
rewrite/psum; under eq_bigr do rewrite /normf normrN.
near: J. apply: P. Unshelve. end_near.
Qed.

Lemma summable_funZ (a : K) x : 
  summable x -> summable (a \*: x).
Proof.
move=>[M P]; exists (`|a|*M); near=>J.
rewrite/psum; under eq_bigr do rewrite/=/GRing.scale/= /normf normrZ.
rewrite -mulr_sumr ler_wpM2l//.
near: J. apply: P. Unshelve. end_near.
Qed.

Lemma summable_fun_comp (a : I -> K) x : 
  summable a -> summable x -> summable (fun i => a i *: x i).
Proof.
move=>[Ma Pa] [My Py]; exists (Ma * My); near=>J.
apply: (le_trans (y := Ma * psum \`| x | J)).
rewrite /psum mulr_sumr ler_sum// =>i _.
rewrite /normf normrZ ler_pM//.
2: rewrite ler_pM//.
1,2: apply: (le_trans (y := psum \`| a | J)).
have P3: (val i) \in J by case: i.
by rewrite /psum (big_fset_seqE J \`| a |)/= (big_fsetD1 _ P3)/= lerDl sumr_ge0.
2,4: by rewrite sumr_ge0.
all: near: J; by [apply Pa | apply Py].
Unshelve. end_near.
Qed.

Lemma summable_zero_subproof : summable (\0 : I -> V).
Proof.
exists 0. near=>J.
by rewrite /psum big1// =>i _; rewrite /normf normr0.
Unshelve. end_near.
Qed.

HB.instance Definition summable_zero_mixin := Bounded_isSummable.Build I K V \0 summable_zero_subproof.
Definition summable_zero := Summable.build summable_zero_subproof.

Lemma summableP f g : f = g <-> f =1 g.
Proof.
split=>[->//|]; move: f g=>[]f[]/=++[]g[]/=++/funext eqf;
rewrite eqf=>[[/=B1]] [S1] [B2] [S2].
by rewrite (Prop_irrelevance B1 B2) (Prop_irrelevance S1 S2).
Qed.

Lemma summablefE x (H : summable x) :
  x = Summable.build H.
Proof. by []. Qed.

Lemma summablefP f : summable f.
Proof. exact: summable_subproof. Qed.

Definition summable_add f g :=
  Summable.build (summable_funD (summablefP f) (summablefP g)).

Definition summable_opp f :=
  Summable.build (summable_funN (summablefP f)).

Definition summable_scale (a : K) f :=
  Summable.build (summable_funZ a (summablefP f)).

(* Check {summable I -> V}: zmodType. *)

Program Definition summable_zmodMixin :=
  @GRing.isZmodule.Build {summable I -> V} summable_zero summable_opp summable_add _ _ _ _.
Next Obligation. by move=>f g h; apply/summableP=> i/=;rewrite addrA. Qed.
Next Obligation. by move=>f g; apply/summableP=> i/=;rewrite addrC. Qed.
Next Obligation. by move=>f; apply/summableP=> i/=; rewrite add0r. Qed.
Next Obligation. by move=>f; apply/summableP=> i/=; rewrite addNr. Qed.
HB.instance Definition _ := summable_zmodMixin.

Program Definition summable_lmodMixin
  := @GRing.Zmodule_isLmodule.Build K {summable I -> V} summable_scale _ _ _ _.
Next Obligation. by move=>a b f; apply/summableP=> i/=;rewrite scalerA. Qed.
Next Obligation. by move=>f; apply/summableP=> i/=; rewrite scale1r. Qed.
Next Obligation. by move=>a f g; apply/summableP=> i/=; rewrite scalerDr. Qed.
Next Obligation. by move=>a f g; apply/summableP=> i/=; rewrite scalerDl. Qed.
HB.instance Definition _ := summable_lmodMixin.

Lemma summable_addE f g i : (f + g) i = f i + g i.         Proof. by []. Qed.
Lemma summable_oppE f i : (- f) i = - f i.                 Proof. by []. Qed.
Lemma summable_scaleE (a : K) f i : (a *: f) i = a *: f i. Proof. by []. Qed.
Lemma summable_zeroE i : (0 : {summable I -> V}) i = 0.    Proof. by []. Qed.
Lemma summable_sumE (J : Type) (r : seq J) (P : pred J) (F : J -> {summable I -> V}) i :
  (\sum_(j <- r | P j) F j) i = \sum_(j <- r | P j) F j i.
Proof. by elim/big_rec2: _=>//???? <-; rewrite summable_addE. Qed.

Definition summableE :=
  (summable_zeroE, summable_addE, summable_oppE, summable_scaleE).

Lemma summable_fun_norm x : summable x -> summable (\`| x | : I -> K).
Proof.
move=>[M PM]; exists M; near=>J.
rewrite/psum; under eq_bigr do rewrite /normf normr_id.
near: J; apply: PM.
Unshelve. end_near.
Qed.

HB.instance Definition _ f := Bounded_isSummable.Build I K K \`| f | (summable_fun_norm (summablefP f)).

Lemma summable_sum_cst0 : sum ((fun i : I => 0 : V)) = 0.
Proof.
rewrite/sum; suff ->: (psum (fun _ : I => 0 : V)) = fun=>0 by rewrite lim_cst.
by apply/funext=>i; rewrite/psum big1.
Qed.

Lemma summable_sum0 : sum (0 : {summable I -> V}) = 0.
Proof. exact: summable_sum_cst0. Qed.

End SummableLmod.

Section fset_topologicalType.
Variable (I : choiceType).

Let D : set {fset I} := setT.
Let b : {fset I} -> set {fset I} := fun i => [set i].
#[local] Lemma bT : \bigcup_(i in D) b i = setT.
Proof. by rewrite predeqE => i; split => // _; exists i. Qed.

#[local] Lemma bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Proof. by move=> i j t _ _ -> ->; exists j. Qed.

HB.instance Definition _ := Pointed_isBaseTopological.Build 
  {fset I} bT bD.

End fset_topologicalType.

Section Bounded_NormedMod.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : normedModType C}.
Local Notation F := {bounded I -> V}.
Implicit Type (f g : F).

Definition bounded_norm f := etsup [set y | y = 0 \/ exists i, y = `|f i| ].

Lemma has_sup_bounded_norm f : has_sup [set y | y = 0 \/ exists i, y = `|f i| ].
Proof.
split; first by exists 0=>/=; left.
by move: (boundedfP f)=>[e Pe]; exists (Num.max 0 e)=>y/=[->|[]i->];
rewrite ?max_le_l// max_r//; apply: (le_trans _ (Pe i)).
Qed.

Lemma bounded_norm_upper f i : `|f i| <= bounded_norm f.
Proof.
by apply/etsup_upper_bound; [apply/has_sup_bounded_norm | right; exists i].
Qed.

Lemma bounded_norm_least f e : 0 <= e ->
  (forall i, `|f i| <= e) -> bounded_norm f <= e.
Proof.
move=>Pe P. apply: etsup_least_ubound. apply/has_sup_bounded_norm.
by move=>y/=[->|[]i->].
Qed.

Lemma bounded_norm0_eq0 f : bounded_norm f = 0 -> f = 0.
Proof.
move=>P2; apply/boundedP=>i/=; apply/normr0_eq0.
by move: (bounded_norm_upper f i); rewrite P2 normr_le0=>/eqP->; rewrite normr0.
Qed.

Lemma bounded_norm_ge0 f : 0 <= bounded_norm f.
Proof. by apply/etsup_upper_bound=>/=; [apply/has_sup_bounded_norm |left]. Qed.

Lemma bounded_norm_triangle f g : 
  bounded_norm (f + g) <= bounded_norm f + bounded_norm g.
Proof.
apply/bounded_norm_least=>[|i/=]; first by rewrite addr_ge0// bounded_norm_ge0.
apply/(le_trans (ler_normD _ _))/lerD; apply/bounded_norm_upper.
Qed.

Lemma bounded_normZ (a: C) f : 
  bounded_norm (a *: f) = `|a| * bounded_norm f.
Proof.
apply/le_anti/andP; split; last (case E: (a == 0); move: E=>/eqP).
apply/bounded_norm_least=>[|i/=].
apply/mulr_ge0=>//; apply/bounded_norm_ge0.
rewrite normrZ ler_wpM2l//; apply/bounded_norm_upper.
move=>->; rewrite normrE mul0r; apply/bounded_norm_ge0.
move=>/eqP; rewrite -normr_gt0=>P; rewrite mulrC -ler_pdivlMr//.
apply/bounded_norm_least=>[|i].
by apply/divr_ge0; [apply/bounded_norm_ge0|apply/ltW].
rewrite ler_pdivlMr// mulrC -normrZ.
by apply: (le_trans _ (bounded_norm_upper _ i)).
Qed.

HB.instance Definition _ := isVNorm.Build C {bounded I -> V} bounded_norm
  bounded_norm_triangle bounded_norm0_eq0 bounded_normZ.

Lemma bounded_normMn f n : bounded_norm (f *+ n) = bounded_norm f *+ n.
Proof. exact: normvMn. Qed.

Lemma bounded_normN f : bounded_norm (- f) = bounded_norm f.
Proof. exact: normvN. Qed.

HB.instance Definition _ := Num.Zmodule_isNormed.Build C {bounded I -> V}
  bounded_norm_triangle bounded_norm0_eq0 bounded_normMn bounded_normN.

HB.instance Definition _ := isPointed.Build {bounded I -> V} summable_zero.
HB.instance Definition _ := hasNbhs.Build {bounded I -> V}
  (nbhs_ball_ (ball_ (fun x => `|x|))).
HB.instance Definition _ :=
  Nbhs_isPseudoMetric.Build C {bounded I -> V}
    nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.

Lemma bounded_norm_ball :
  @ball _ F = ball_ (fun x => `| x |).
Proof. by rewrite /normr /ball_ predeq3E/= /ball/=/normr/=. Qed.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build C {bounded I -> V}
  bounded_norm_ball.
HB.instance Definition _ := PseudoMetricNormedZmod_Lmodule_isNormedModule.Build
  C {bounded I -> V} bounded_normZ.

Lemma boundedE_cvg (T : Type) (F : set_system T) {FF : Filter F} 
  (f : T -> {bounded I -> V}) (g : {bounded I -> V}) :
  f @ F --> g -> forall i : I, (fun t => f t i) @ F --> g i.
Proof.
move=>/fcvgrPdist_lt P1 i; apply/fcvgrPdist_lt=>e egt0.
rewrite near_simpl; move: (P1 e egt0); rewrite near_simpl=>P2.
near=>t; have: (`|g - f t| < e) by near: t; apply: P2.
apply: le_lt_trans.
by apply: (le_trans _ (bounded_norm_upper _ i)); rewrite boundedE/=.
Unshelve. end_near.
Qed.

Lemma boundedE_is_cvg (T : Type) (F : set_system T) {FF : ProperFilter F} 
  (f : T -> {bounded I -> V}) :
    cvg (f @ F) -> forall i : I, cvg ((fun t => f t i) @ F).
Proof. by move=>P i; apply/cvg_ex; exists (lim (f @ F) i); apply: boundedE_cvg. Qed.

Lemma boundedE_lim (T : Type) (F : set_system T) {FF : ProperFilter F} 
  (f : T -> {bounded I -> V}) :
    cvg (f @ F) -> forall i : I, lim ((fun t => f t i) @ F) = lim (f @ F) i.
Proof. by move=>/boundedE_cvg P i; move: (P i)=>/(cvg_lim (@norm_hausdorff _ _)). Qed.

End Bounded_NormedMod.

Section Bounded_Complete.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : completeNormedModType C}.

Lemma bounded_complete (F : set_system {bounded I -> V}) : 
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=>FF /cauchyP F_cauchy.
pose G i := (fun f=>f i) @ F.
have P1 : forall i : I, cvg (G i).
  move=>j; apply/cauchy_cvgP/cauchyP=>e egt0.
  move: (F_cauchy _ egt0)=>/=[f Pf].
  exists (f j); rewrite/G/= nbhs_filterE; apply: (filterS _ Pf)=>x.
  rewrite -!ball_normE/= {1}/normr/=; apply: le_lt_trans.
  by apply: (le_trans _ (bounded_norm_upper _ j)).
pose g i := lim (G i).
have Pg : bounded g.
  move: (F_cauchy _ ltr01)=>/=[f Pf]; exists (`|f|+1)=>i.
  apply: (le_trans (y := `|f i| + 1));
    last by rewrite lerD2; apply: bounded_norm_upper.
  rewrite/g -lim_norm/=; first apply: P1.
  apply: etlim_le_near. apply: is_cvg_norm; apply: P1.
  rewrite near_simpl. near=>J.
  have: ball f 1 J by near: J; rewrite near_simpl/= -nbhs_nearE/nbhs/=.
  rewrite /ball/==>P; rewrite addrC -lerBlDr.
  apply: (le_trans _ (ltW (le_lt_trans (bounded_norm_upper (f - J) i) P))).
  by rewrite/= -[ `| _ - _|]normrN opprB lerB_dist.
apply/cvg_ex; exists (Bounded.build Pg). rewrite cvgrPdist_le=>e egt0.
move: {+}F_cauchy=>/cauchyP/cauchy_ballP/(_ _ egt0)/nearP_dep P2.
near=>f. apply/bounded_norm_least=>[|i]. by apply/ltW.
rewrite/=/g. have->: `|lim (G i) - f i| = lim (`| (x - f) i | @[x --> F]).
  rewrite/= lim_norm; [apply: is_cvgB | rewrite limB ].
  1,3: apply: P1. 1,2: apply: is_cvg_cst. by rewrite lim_cst. 
apply: etlim_le_near. 
by apply: is_cvg_norm; apply: is_cvgB; [apply: P1 | apply: is_cvg_cst].
near=>h; apply/ltW.
have /ball_sym: ball f e h. near: h. near: f. apply: P2.
rewrite -ball_normE/ball_/=; apply/le_lt_trans.
by apply: (le_trans _ (bounded_norm_upper _ i)); rewrite boundedE/=.
Unshelve. all: end_near.
Qed.

HB.instance Definition _ := Uniform_isComplete.Build {bounded I -> V} (@bounded_complete).

End Bounded_Complete.

Section SummableCvg.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : normedModType C}.
Local Notation F := {summable I -> V}.
Implicit Type (f g : {summable I -> V}).

Definition summable_norm f := lim ((psum \`| f |) @ totally).

Lemma summable_norm_cvg f :
  (psum \`| f |) @ totally --> (etsup (psum_preset \`| f |)).
Proof.
apply/cvgrPdist_lt=>e egt0.
move: (has_sup_psum_preset (summablefP f))=>hs.
move:{+}hs=>/etsup_adherent hs1; move: (hs1 _ egt0)=>[y]/= [J -> Pj].
exists J=>//= z/= Pz; rewrite ger0_norm.
by rewrite subr_ge0; apply: (etsup_upper_bound hs); rewrite/S/=; exists z.
rewrite ltrBlDr addrC -ltrBlDr; apply: (lt_le_trans Pj).
by rewrite -(fsetUD_sub Pz) psumU ?fdisjointXD// lerDl /psum sumr_ge0.
Qed.
Arguments summable_norm_cvg : clear implicits.

Lemma summable_norm_is_cvg f : cvg ((psum \`| f |) @ totally).
Proof. by move: (summable_norm_cvg f)=>/cvgP. Qed.
Arguments summable_norm_is_cvg : clear implicits.

Lemma summable_normE f :
  summable_norm f = etsup (psum_preset \`| f |).
Proof. apply: cvg_lim=>//; apply/summable_norm_cvg. Qed.

Lemma psum_norm_ler_norm f J : psum \`| f | J <= summable_norm f.
Proof.
suff: (\forall K \near totally, psum \`| f | J <= psum \`| f | K).
move=> /(closed_cvg (>= psum \`| f | J)) P.
move: (summable_norm_is_cvg f); apply/P/etclosed_ge.
near=>K. apply/psum_ler=>//. near: K. exists J=>//.
Unshelve. end_near.
Qed.

Lemma summable_norm0_eq0 f : summable_norm f = 0 -> f = 0.
Proof.
move=>P2; apply/summableP=>i/=; apply/normr0_eq0.
apply/le_anti/andP; split=>//; rewrite -P2.
apply: (le_trans (y := psum \`| f | [fset i]%fset)).
by rewrite psum1. by apply/psum_norm_ler_norm.
Qed.

Lemma summable_norm_triangle f g : 
  summable_norm (f + g) <= summable_norm f + summable_norm g.
Proof.
rewrite /summable_norm -limD; last first. apply: ler_etlim; last first.
by move=>/= J; rewrite !fctE -psumD ler_sum// =>i _; rewrite fctE ler_normD.
apply: is_cvgD. all: apply: summable_norm_is_cvg.
Qed.

Lemma summable_normZ (a: C) f : 
  summable_norm (a *: f) = `|a| * summable_norm f.
Proof.
rewrite/summable_norm.
transitivity (`|a| *: lim ((psum (fun i : I => `|f i|)) @ totally)).
rewrite -limZr; first by apply: summable_norm_is_cvg.
apply: lim_eq=>J; rewrite !fctE /psum scaler_sumr; apply eq_bigr=>i _.
all: by rewrite/= /normf 1?normrZ /GRing.scale.
Qed.

HB.instance Definition _ := isVNorm.Build C {summable I -> V} summable_norm
  summable_norm_triangle summable_norm0_eq0 summable_normZ.

Lemma summable_normMn f n : summable_norm (f *+ n) = summable_norm f *+ n.
Proof. exact: normvMn. Qed.

Lemma summable_normN f : summable_norm (- f) = summable_norm f.
Proof. exact: normvN. Qed.

HB.instance Definition _ := Num.Zmodule_isNormed.Build C {summable I -> V}
  summable_norm_triangle summable_norm0_eq0 summable_normMn summable_normN.

HB.instance Definition _ := isPointed.Build {summable I -> V} summable_zero.
HB.instance Definition _ := hasNbhs.Build {summable I -> V}
  (nbhs_ball_ (ball_ (fun x => `|x|))).
HB.instance Definition _ :=
  Nbhs_isPseudoMetric.Build C {summable I -> V}
    nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.

Lemma summable_norm_ball :
  @ball _ F = ball_ (fun x => `| x |).
Proof. by rewrite /normr /ball_ predeq3E/= /ball/=/normr/=. Qed.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build C {summable I -> V}
  summable_norm_ball.
HB.instance Definition _ := PseudoMetricNormedZmod_Lmodule_isNormedModule.Build
  C {summable I -> V} summable_normZ.

Lemma summableE_cvg (T : Type) (F : set_system T) {FF : Filter F} 
  (f : T -> {summable I -> V}) (g : {summable I -> V}) :
  f @ F --> g -> forall i : I, (fun t => f t i) @ F --> g i.
Proof.
move=>/fcvgrPdist_lt P1 i; apply/fcvgrPdist_lt=>e egt0.
rewrite near_simpl; move: (P1 e egt0); rewrite near_simpl=>P2.
near=>t; have: (`|g - f t| < e) by near: t; apply: P2.
apply: le_lt_trans.
by apply: (le_trans _ (psum_norm_ler_norm _ [fset i]%fset)); rewrite psum1/=.
Unshelve. end_near.
Qed.

Lemma summableE_is_cvg (T : Type) (F : set_system T) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) :
    cvg (f @ F) -> forall i : I, cvg ((fun t => f t i) @ F).
Proof. by move=>P i; apply/cvg_ex; exists (lim (f @ F) i); apply: summableE_cvg. Qed.

Lemma summableE_lim (T : Type) (F : set_system T) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) :
    cvg (f @ F) -> forall i : I, lim ((fun t => f t i) @ F) = lim (f @ F) i.
Proof. by move=>/summableE_cvg P i; move: (P i)=>/(cvg_lim (@norm_hausdorff _ _)). Qed.

End SummableCvg.

Section cvg_sum_pseudometric.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.
Context {T : Type} (F : set_system T).

(* Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V). *)

Lemma cvg_sum_apply  {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) (a : I -> V) :
  (forall i, P i -> f i @ F --> a i) -> 
    (\sum_(i <- r | P i) (f i t)) @[t --> F] --> (\sum_(i <- r | P i) a i).
Proof.
move=>P1. elim: r.
rewrite big_nil. under eq_cvg do rewrite big_nil. apply: cvg_cst.
move=>h t IH. rewrite big_cons.
under eq_cvg do rewrite big_cons.
case E: (P h); last by apply : IH.
move: (P1 _ E)=>P2. apply: cvgD. apply: P2. apply: IH.
Qed.

Lemma is_cvg_sum_apply {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) : 
      (forall i, P i -> cvg (f i @ F)) -> cvg ((\sum_(i <- r | P i) (f i t)) @[t --> F]).
Proof. by have := cvgP _ (cvg_sum_apply _); apply. Qed.

Lemma lim_sum_apply {FF : ProperFilter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) :
  (forall i, P i -> cvg (f i @ F)) ->
    lim ((\sum_(i <- r | P i) (f i t)) @[t --> F]) = \sum_(i <- r | P i) lim (f i @ F). 
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_sum_apply. Qed.

Lemma lim_sum_apply_fset {FF : ProperFilter F}
    (I : choiceType) (J : {fset I}) (f : I -> T -> V) :
  (forall i : J, cvg (f (val i) @ F)) ->
    lim ((\sum_(i : J) (f (val i) t)) @[t --> F]) = \sum_(i : J) lim (f (val i) @ F). 
Proof. move=>?; exact: lim_sum_apply. Qed.

Lemma cvg_sum  {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) (a : I -> V) :
  (forall i, P i -> f i @ F --> a i) -> 
    (\sum_(i <- r | P i) (f i)) @ F --> (\sum_(i <- r | P i) a i).
Proof.
move=>P1; elim/big_rec2: _ => [|i b /= g Pi cg]; first by apply: cvg_cst.
by apply: cvgD=>//; apply: P1.
Qed. 

Lemma is_cvg_sum {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) : 
      (forall i, P i -> cvg (f i @ F)) -> cvg ((\sum_(i <- r | P i) (f i)) @ F).
Proof. by have := cvgP _ (cvg_sum _); apply. Qed.

Lemma lim_sum {FF : ProperFilter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) :
  (forall i, P i -> cvg (f i @ F)) ->
    lim ((\sum_(i <- r | P i) (f i)) @ F) = \sum_(i <- r | P i) lim (f i @ F). 
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_sum. Qed.

Lemma lim_sum_fset {FF : ProperFilter F}
    (I : choiceType) (J : {fset I}) (f : I -> T -> V) :
  (forall i : J, cvg (f (val i) @ F)) ->
    lim ((\sum_(i : J) (f (val i))) @ F) = \sum_(i : J) lim (f (val i) @ F). 
Proof. move=>?; exact: lim_sum. Qed.

End cvg_sum_pseudometric.

Section Cauchy_ball_fset.
Context {R : numFieldType} {T : pseudoMetricNormedZmodType R} {I : choiceType}.

Definition cauchy_ball_fset (f : {fset I} -> T) :=
  forall e : R, e > 0 -> \forall x & y \near totally, (x `<=` y)%fset -> ball (f x) e (f y).

Lemma cauchy_ball_fsetP (f : {fset I} -> T) :
  cauchy_ball_fset f <-> cauchy (nbhs (f @ totally)).
Proof.
split=>[P1 | /cauchy_ballP P1 e egt0]; last first.
  move: (P1 e egt0); rewrite !near_simpl !near2E=>P2.
  by near=>x; move=>_; near: x; apply P2.
apply/cauchy_ballP=>e egt0; rewrite !near_simpl near2E; apply/filter2P.
have e2gt0 : 0 < e / 2 by rewrite divr_gt0.
move: (P1 _ e2gt0); rewrite near2E=>/filter2P[t [[s1/= _ Ps1] [s2/= _ Ps2]]/= P2].
exists ([set B | (s1 `|` s2 `<=` B)%fset], [set B | (s1 `|` s2 `<=` B)%fset]).
by split; exists (s1 `|` s2)%fset.
move=>x y/=; rewrite !fsubUset=>/andP[Q1 Q2]/andP[Q3 Q4].
have: ball (f x) (e / 2) (f (x `|` y)%fset) /\ ball (f y) (e / 2) (f (x `|` y)%fset).
split; apply: P2. 1,4: by apply: Ps1. 1,3: by apply/Ps2/fsubsetU/orP; right. 
by apply/fsubsetUl. by apply/fsubsetUr.
rewrite -ball_normE/==>[[]]P3 P4.
move: (ltrD P3 P4). rewrite [ `|f y - _ |]distrC -splitr.
apply: le_lt_trans. apply: ler_distD.
Unshelve. end_near.
Qed.

End Cauchy_ball_fset.

Section Summable_Complete.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : completeNormedModType C}.

Lemma summable_cvg (f : {summable I -> V}) : cvg ((psum f) @ totally).
Proof.
move: (summable_norm_is_cvg (f := f))=>/cauchy_cvgP/cauchy_ball_fsetP P1.
suff: cauchy (nbhs ((psum f) @ totally)). by apply: cauchy_cvg.
apply/cauchy_ball_fsetP=>e egt0; move: (P1 e egt0); rewrite !near2E=>P2.
near=>x. move=> Px.
have: ball (psum \`| f | x.1) e (psum \`| f | x.2).
move: Px; near: x; apply: P2.
move: Px; rewrite -!ball_normE/= -psumIB -[in X in _ -> _ -> X]psumIB -fsetD_eq0=>/eqP->.
rewrite !psum0 !sub0r !normrN. apply: le_lt_trans. apply: (le_trans _ (real_ler_norm _)).
apply: ler_norm_sum. by apply/ger0_real/sumr_ge0.
Unshelve. end_near.
Qed.

Lemma summable_complete (F : set_system {summable I -> V}) : 
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=>FF /cauchyP F_cauchy.
pose G i := (fun f=>f i) @ F.
have P1 : forall i : I, cvg (G i).
  move=>j; apply/cauchy_cvgP/cauchyP=>e egt0.
  move: (F_cauchy _ egt0)=>/=[f Pf].
  exists (f j); rewrite/G/= nbhs_filterE; apply: (filterS _ Pf)=>x.
  rewrite -!ball_normE/= {1}/normr/=; apply: le_lt_trans.
  apply: (le_trans (y := psum \`| f - x | [fset j]%fset)).
  by rewrite psum1. by apply/psum_norm_ler_norm.
pose g i := lim (G i).
have Pg : summable g.
  move: (F_cauchy _ ltr01)=>/=[f Pf]; exists (`|f|+1); near=>J.
  apply: (le_trans (y := psum \`| f | J + 1));
    last by rewrite lerD2; apply: psum_norm_ler_norm.
  rewrite addrC -lerBlDr -psumB /psum.
  apply: (le_trans (y := \sum_i lim ((fun x=>`|x (val i) - f (val i)|) @ F))).
  - apply: ler_sum=>i _; rewrite/g!fctE /normf -lim_norm; last first.
  have ->: `|f (val i)| = lim (`|f (val i)| @[x --> F]) by rewrite lim_cst.
  rewrite -(limB(F:=F)); last (apply: ler_etlim; last by move=>h; rewrite !fctE lerB_dist).
  1,2,4: apply: is_cvg_norm. 3,4: apply: is_cvgB. 5,6: apply: is_cvg_norm.
    1,3,5,7: apply: P1. 1,2,3: apply: is_cvg_cst.
  - rewrite -lim_sum; last (apply: etlim_le_near; first apply: is_cvg_sum).  
    1,2: move=>i _/=; apply: is_cvg_norm; apply: is_cvgB; [apply P1 | apply: is_cvg_cst].
    rewrite near_simpl. near=>K. have: ball f 1 K by near: K; apply: Pf.
    rewrite -ball_normE/ball_/= distrC fct_sumE =>P2.
    under eq_bigr do rewrite -!summableE.
    apply/ltW/(le_lt_trans _ P2)/psum_norm_ler_norm.
apply/cvg_ex; exists (Summable.build Pg). rewrite cvgrPdist_le=>e egt0.
move: {+}F_cauchy=>/cauchyP/cauchy_ballP/(_ _ egt0)/nearP_dep P2.
near=>f. apply: etlim_le_near. apply: summable_norm_is_cvg.
near=>J. rewrite/psum.
have->:  \sum_(i : J) `|(Summable.build Pg - f) (val i)| = (\sum_(i : J) lim (`|(x - f) (val i)| @[x --> F])).
  apply eq_bigr=>i _; rewrite/= lim_norm; [apply: is_cvgB | rewrite limB ]; last by rewrite lim_cst.
  1,3: apply: P1. 1,2: apply: is_cvg_cst.
rewrite -lim_sum; last apply: etlim_le_near.
by move=>i _; apply: is_cvg_norm; apply: is_cvgB; [apply P1 | apply: is_cvg_cst].
by apply: is_cvg_sum=>i _; apply: is_cvg_norm; apply: is_cvgB; [apply: P1 | apply: is_cvg_cst].
near=>h; apply/ltW.
have: ball f e h by near: h; near: f; apply: P2.
rewrite -ball_normE/ball_/= fct_sumE distrC; apply: le_lt_trans.
under eq_bigr do rewrite -!summableE; apply: psum_norm_ler_norm.
Unshelve. all: end_near.
Qed.

HB.instance Definition _ := Uniform_isComplete.Build {summable I -> V} (@summable_complete).

Implicit Type (x y z : {summable I -> V}).

Lemma summable_sumP (a : C) x y : 
  sum (a *: x + y) = a *: (sum x) + sum y.
Proof.
rewrite/sum -limZr; first by apply: summable_cvg.
rewrite -limD. apply: is_cvgZr. 1,2: apply: summable_cvg.
apply: eq_lim=>i; rewrite !fctE /psum; under eq_bigr do rewrite !summableE.
by rewrite big_split/= scaler_sumr.
Qed.

Lemma summable_sumD x y : sum (x + y) = sum x + sum y.
Proof. by rewrite -[x]scale1r summable_sumP !scale1r. Qed. 

Lemma summable_sumZ (a : C) x : sum (a *: x) = a *: sum x.
Proof. by rewrite -[a *: x]addr0 summable_sumP summable_sum0 !addr0. Qed.

Lemma summable_sumN x : sum (- x) = - sum x.
Proof. by rewrite -scaleN1r summable_sumZ scaleN1r. Qed.

Lemma summable_sumB x y : sum (x - y) = sum x - sum y.
Proof. by rewrite summable_sumD summable_sumN. Qed.

Lemma summable_sum_sum (J : Type) (r : seq J) (P : pred J) (F : J -> {summable I -> V}) :
  sum (\sum_(j <- r | P j) F j) = \sum_(j <- r | P j) (sum (F j)).
Proof. by elim/big_rec2: _ =>[|???? <-]; rewrite ?summable_sum0// summable_sumD. Qed.

Lemma summable_sum_ler_norm x : `|sum x| <= sum \`| x |.
Proof.
rewrite/sum -lim_norm. apply: summable_cvg.
apply: ler_etlim. apply: is_cvg_norm. apply: summable_cvg.
apply: summable_norm_is_cvg.
move=>n; rewrite /psum; apply: normv_sum.
Qed.

Definition summable_sum (f : {summable I -> V}) := sum f.

Lemma summable_sum_continuous : continuous summable_sum.
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb]; apply/nbhs_ballP.
exists e=>// y/= P1; apply: Pb; move: P1.
rewrite -!ball_normE/= -summable_sumB. apply: le_lt_trans.
rewrite -lim_norm; first by apply: summable_cvg.
rewrite {2}/Num.Def.normr/summable_norm; apply: ler_etlim.
apply: is_cvg_norm; apply: summable_cvg.
apply: summable_norm_is_cvg.
move=>S; apply: ler_norm_sum.
Qed.

Lemma summable_sum_cvg (T : Type) (F : set_system T) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) (g : {summable I -> V}):
  f @ F --> g -> sum (f i) @[i --> F] --> sum g.
Proof.
have ->: (fun i => sum (f i)) = (fun i => summable_sum (f i)).
by apply/funext=>i.
apply: continuous_cvg. apply: summable_sum_continuous.
Qed.

Lemma summable_sum_is_cvg (T : Type) (F : set_system T) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) :
  cvg (f @ F) -> cvg (sum (f i) @[i --> F]).
Proof.
move=>/cvg_ex=>[/= [a Pa]]; apply/cvg_ex.
by exists (sum a); apply: summable_sum_cvg.
Qed.

Lemma summable_sum_lim (T : Type) (F : set_system T) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) : cvg (f @ F) -> 
  lim (sum (f i) @[i --> F]) = sum (lim (f @ F)).
Proof. by move=>/summable_sum_cvg P; apply: cvg_lim. Qed.

End Summable_Complete.

Section test.
Context {I : choiceType} {R : realType} {C : extNumType R} {V W : completeNormedModType C} .

Lemma cvg_linear_sumG (x : I -> V) (f : {linear V -> W}) :
  (exists k, 0 < k /\ forall v, `|f v| <= k * `|v|) -> cvg ((psum x) @ totally) ->
  f (sum x) = sum (f \o x)%FUN.
Proof.
move=>[k [Pk1 Pk2]] /cvgrPdist_lt Px.
suff: psum (f \o x) @ totally --> f (sum x) by move=>/cvg_lim<-.
apply/cvgrPdist_lt=>e egt0; near=>S.
have: `|sum x - psum x S| < e / k by near: S; apply/Px/divr_gt0.
rewrite ltr_pdivlMr//; apply: le_lt_trans.
rewrite/psum/= -linear_sum/= -linearB mulrC; apply: Pk2.
Unshelve. end_near.
Qed.

Lemma summable_linear_sumG (x : {summable I -> V}) (f : {linear V -> W}) :
  (exists k, 0 < k /\ forall v, `|f v| <= k * `|v|) ->
  f (sum x) = sum (f \o x)%FUN.
Proof. move=>P1; apply: cvg_linear_sumG=>//; apply: summable_cvg. Qed.

End test.


Section Bounded_Cvg.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : completeNormedModType C}.

Lemma norm_bounded_cvg (f : I -> V) : 
  (exists (M : C), \forall J \near totally, (psum \`| f | J <= M)%R) ->
  cvg ((psum f) @ totally).
Proof.
move=>P. have P1: summable f. by [].
pose g := Summable.build P1.
have ->: f = g. by []. apply: summable_cvg.
Qed.

End Bounded_Cvg.

Section FinSupp.

Definition suppf {I} {V : zmodType} (f : I -> V) :=
  [set x | f x != 0].

Lemma foo1 {I : choiceType} (J : {fset I}) (i : I) :
  (i \in J) <-> ([set` J] i).
Proof. by split=>/=. Qed.

Lemma fin_suppf_summable {I : choiceType} {K : numFieldType} 
  {V : normedZmodType K} (f : I -> V) :
    finite_set (suppf f) -> summable f.
Proof.
move=>/finite_fsetP[J PJ].
have P1: forall i, i \notin J -> f i = 0.
by move=>i /negP; rewrite foo1 -PJ/suppf/==>/negP; rewrite negbK=>/eqP.
exists (psum (fun i => `|f i|) J).
near=>L. rewrite -subr_ge0 -psumIB /psum [X in _ - X]big1=>[i _|].
by apply/normr0P/eqP/P1; case: i=>/= i; rewrite in_fsetD=>/andP[].
by rewrite subr0 sumr_ge0.
Unshelve. end_near.
Qed.

Lemma fin_supp_cvg {I : choiceType} {R : realType} {C : extNumType R} 
  {V : normedModType C} (f : I -> V) (S : {fset I}) :
  (forall i, i \notin S -> f i = 0) -> psum f  @ totally --> psum f S.
Proof.
move=>Pf; apply: cvg_near_cst; exists S=>// T/= PST.
apply/eqP; rewrite -subr_eq0 -psumIB.
move: PST; rewrite -fsetD_eq0=>/eqP ->; rewrite psum0 subr0 /psum big1//.
by move=>[] i + _; rewrite/= !inE=>/andP[]/Pf->.
Qed.

Lemma fin_supp_is_cvg {I : choiceType} {R : realType} {C : extNumType R}
  {V : normedModType C} (f : I -> V) (S : {fset I}) :
  (forall i, i \notin S -> f i = 0) -> cvg ((psum f) @ totally).
Proof. by move=>/fin_supp_cvg Pc; apply/cvg_ex; exists (psum f S). Qed.

Lemma fin_supp_sum {I : choiceType} {R : realType} {C : extNumType R}
  {V : normedModType C} (f : I -> V) (S : {fset I}) :
  (forall i, i \notin S -> f i = 0) -> sum f = psum f S.
Proof. by move=>/fin_supp_cvg; apply: cvg_lim. Qed.

End FinSupp.

(* move to extnum.v *)
Lemma extNum_archiV {R : realType} {C : extNumType R} (x : C) : 
  0 <= x -> exists k : nat, x < k.+1%:R.
Proof.
rewrite le_eqVlt=>/orP[/eqP<-|xgt0]; first by exists 0%N.
move: {+}xgt0; rewrite -invr_gt0=>/extNum_archi[k]; rewrite ltr_pV2 ?inE//.
3: move=>Pk; by exists k.
all: apply/andP; split=>//; rewrite unitfE//; by apply/lt0r_neq0.
Qed.

Section SummableCountable.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : normedModType C}.
Implicit Type (f : {summable I -> V}).

Lemma summable_bounded f : exists2 M, 0 <= M & forall J,
  (psum \`| f | J <= M)%R.
Proof.
move: (summablefP f)=>[M BM]; exists M=>[|J];
move: BM; rewrite nearE/=/totally/=/filter_from/==>[[ i]] _.
move=>/(_ i)/= P; apply: (le_trans (y := psum (fun i : I => `|f i|) i)).
by apply: sumr_ge0. by apply: P.
move=>/(_ (i `|` J)%fset)/= P.
apply: (le_trans (y := psum (fun i : I => `|f i|) (i `|` J)%fset)).
apply: psum_ler=>//. apply/fsubsetUr. apply/P/fsubsetUl.
Qed.

Lemma summable_countn0 f : countable (suppf f).
Proof.
move: (summable_bounded f)=>[M M_ge0 BM].
pose E (p : nat) := [set x | `|f x| > 1 / p.+1%:~R].
have le: suppf f `<=` \bigcup_(p in setT) E p.
  move=>x; rewrite/suppf/= -normr_gt0=>/extNum_archi[k Pk].
  by rewrite/bigcup/=; exists k=>//; rewrite/E/= div1r.
apply/(sub_countable (subset_card_le le))/bigcup_countable=>// i/= _.
apply/finite_set_countable; apply: contrapT.
rewrite infiniteP /E=>/card_leP/injfunPex/=[g _ /in2TT Pg].
have [N PN]: exists N, M / i.+1%:~R^-1 < N.+1%:R
  by apply/extNum_archiV; rewrite divr_ge0// invr_ge0 ler0n.
pose g' := fun n : 'I_N.+1 => val (g (SigSub (mem_setT (val n)))).
have P1: forall n, 1 / i.+1%:~R < `|f (g' n)|
  by move=>n; apply: (set_valP (g (SigSub (mem_setT (val n))))).
pose J := [fset x in [seq g' i | i : 'I_N.+1]]%fset.
suff Pc: \sum_(i : J) `|f (val i)| > M. 
by move: (lt_le_trans Pc (BM J)); rewrite ltxx.
apply/(@lt_le_trans _ _ (\sum_(x : J) 1 / i.+1%:~R)); last first.
  apply/ler_sum=> /= m _; apply/ltW.
  by have:= fsvalP m; rewrite/J in_fset/==>/mapP/=[j _ ->].
rewrite sumr_const -cardfE card_fseq undup_id.
rewrite map_inj_in_uniq ?fintype.enum_uniq// =>a b _ _.
by rewrite/g'=>/val_inj/Pg/(f_equal val)/=/val_inj.
by rewrite size_map fintype.size_enum_ord div1r -mulr_natr mulrC 
  -ltr_pdivrMr// invr_gt0 ltr0n.
Qed.

End SummableCountable.

HB.mixin Record Summable_isVDistr (I : choiceType) (R : realType)
  (V : vorderFinNormedModType R[i]) (f : I -> V) of @Summable I R[i] V f := {
  vdistr_ge0  :  forall x, (0 : V) ⊑ f x;
  vdistr_sum_le1  :  `|sum f| <= 1;
}.

HB.structure Definition VDistr (I : choiceType) (R : realType)
  (V : vorderFinNormedModType R[i]) :=
  { f of @Summable I R[i] V f & Summable_isVDistr I R V f}.

Module VDistrExports.
Module VDistr.
Definition apply_deprecated (I : choiceType) (R : realType)
  (V : vorderFinNormedModType R[i]) (phIV : phant (I -> V)) :=
    @VDistr.sort I R V.
#[deprecated(since="mathcomp 2.0", note="Use VDistr.sort instead.")]
Notation apply := apply_deprecated.
Definition build (I : choiceType) (R : realType)
  (V : vorderFinNormedModType R[i]) (f: {summable I-> V})
  (H0: forall x, (0 : V) ⊑ f x) (H1: `|sum f| <= 1) :=
  VDistr.Pack (VDistr.Class (Summable_isVDistr.Axioms_ f _ (Summable.class f) H0 H1)).
    (* (@Summable_isVDistr.Build I R V (Summable.build (summablefP f)) H0 H1)). *)
End VDistr.
Notation "{ 'vdistr' I -> V }" := (VDistr.type I%type V%type) (at level 0, I at level 98, V at level 99,
format "{ 'vdistr'  I  ->  V }") : type_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use VDistr.clone instead.")]
Notation "[ 'vdistr' 'of' f 'as' g ]" := (VDistr.clone _ _ _ f%function g)
  (at level 0, format "[ 'vdistr'  'of'  f  'as'  g ]") : form_scope.
  #[deprecated(since="mathcomp 2.0.0", note="Use VDistr.clone instead.")]
Notation "[ 'vdistr' 'of' f ]" := (VDistr.clone _ _ _ f%function _)
  (at level 0, format "[ 'vdistr'  'of'  f ]") : form_scope.
End VDistrExports.
HB.export VDistrExports.

HB.instance Definition _ (I : choiceType) (R : realType)
  (V : vorderFinNormedModType R[i]) := gen_eqMixin {vdistr I -> V}.
HB.instance Definition _ (I : choiceType) (R : realType)
  (V : vorderFinNormedModType R[i]) := gen_choiceMixin {vdistr I -> V}.

Section VDistrCoreTh.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.
Variable (f: {vdistr I -> V}).

Lemma vdistrP (g h : {vdistr I -> V}) : g = h <-> g =1 h.
Proof.
split=>[->//|]; move: g h =>[g +] [h +] /= /funext eqf;
rewrite eqf => [] [[B][S][H0 H1]] [[?][?][??]];
by rewrite (Prop_irrelevance B) (Prop_irrelevance S) (Prop_irrelevance H0) (Prop_irrelevance H1).
Qed.

Lemma vdistr_summable : summable f.
Proof. by case: f=>?[?[]]. Qed.

Lemma psum_vdistr_lev (A B : {fset I}) : (A `<=` B)%fset -> psum f A ⊑ psum f B.
Proof.
by move=>PAB; rewrite -(fsetUD_sub PAB) psumU ?fdisjointXD// 
  levDl sumv_ge0// =>? _; apply: vdistr_ge0.
Qed.

Lemma psum_vdistr_ge0 (A : {fset I}) : (0 : V) ⊑ psum f A.
Proof. rewrite sumv_ge0// =>??; apply: vdistr_ge0. Qed.

Lemma psum_vdistr_lev_sum (A : {fset I}) : psum f A ⊑ sum f.
Proof.
apply/lim_gev_near; first by apply: summable_cvg.
by exists A%fset=>// J/= PJ; rewrite psum_vdistr_lev.
Qed.

Lemma vdistr_le_sum : forall x, f x ⊑ sum f.
Proof. move=>x; rewrite -[f x]psum1; apply/psum_vdistr_lev_sum. Qed.

Lemma vdistr_sum_ge0 : (0 : V) ⊑ sum f.
Proof. by apply/(le_trans _ (psum_vdistr_lev_sum fset0)); rewrite psum0. Qed.

End VDistrCoreTh.
#[global] Hint Resolve vdistr_ge0 vdistr_le_sum vdistr_summable : core.

Require Import hermitian.

Notation C := hermitian.C.

Definition Distr (I : choiceType) := nosimpl {vdistr I -> C}.

Section DistrTheory.
Context (I : choiceType) (mu : Distr I).

Lemma ge0_mu : forall x, 0 <= mu x.
Proof. move=>x; apply: vdistr_ge0. Qed.

Lemma sum_le1_mu : sum mu <= 1.
Proof.
apply/(le_trans _ (vdistr_sum_le1))/real_ler_norm.
move: (summable_cvg (f := mu)).
apply: (closed_cvg _ etclosed_real)=>//.
near=>J. apply/ger0_real/sumr_ge0=>i _; apply: ge0_mu.
Unshelve. end_near.
Qed.

Lemma summable_mu : summable mu.
Proof. exact: vdistr_summable. Qed.

Lemma le_psum_mu (A : {fset I}) : psum mu A <= sum mu.
Proof. apply: psum_vdistr_lev_sum. Qed.

Lemma le_sum_mu (x : I) : mu x <= sum mu.
Proof. by apply/(le_trans _ (le_psum_mu [fset x]%fset)); rewrite psum1. Qed.

Lemma le1_mu (x : I) : mu x <= 1.
Proof. apply/(le_trans _ sum_le1_mu)/le_sum_mu. Qed.

Lemma sum_ge0_mu : sum mu >= 0.
Proof. exact: vdistr_sum_ge0. Qed.

Lemma psum_le1_mu (A : {fset I}) : psum mu A <= 1.
Proof. by apply/(le_trans (le_psum_mu A))/sum_le1_mu. Qed.
(* to be continued *)

End DistrTheory.

Lemma limn_in_closed {R : realType} {C : extNumType R} {V : completeNormedModType C} (A : set V) :
  (forall (f : nat -> V), (forall i, A (f i)) -> cvgn f -> A (limn f))
    -> closed A.
Proof.
move=>P. 
rewrite /closed closure_limit_point=>x/=[//|/=].
rewrite/limit_point/==>P1.
pose g (i : nat) := ball x (i.+1%:R^-1).
have nbhsg: forall i, nbhs x (g i)
  by move=>i; apply/nbhs_ballP; exists (i.+1%:R^-1)=>//=; apply/divr_gt0.
have Pg: forall i, {gi : V | A gi /\ ball x (i.+1%:R^-1) gi}.
by move=>i; move: (P1 (g i) (nbhsg i))=>/cid [y[]] _ Py gy; exists y.
pose f (i : nat) := projT1 (Pg i).
have Pf : forall i, A (f i) /\ ball x (i.+1%:R^-1) (f i) by move=>i; move: (projT2 (Pg i)).
suff Pc: f @ \oo --> x. have <-: limn f = x by apply: cvg_lim.
apply: P. by move=>i; move: (Pf i)=>[]. by apply/cvg_ex; exists x.
apply/cvg_ballP=>e egt0.
move: (extNum_archi egt0)=>[k Pk].
exists k=>// n/= Pn. move: (Pf n)=>[] _.
rewrite -ball_normE/==>P2; apply/(lt_trans P2)/(le_lt_trans _ Pk).
by rewrite lef_pV2// ?posrE// ler_nat.
Qed.

Section summable_porder.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.
Implicit Type (f g h : {summable I -> V}).

Definition les_def f g := asbool (forall i, f i ⊑ g i).
(* Definition lts_def f g := (g != f) && (les_def f g). *)

(* Lemma lts_def_def : forall f g, lts_def f g = (g != f) && (les_def f g).
Proof. by []. Qed. *)

Lemma les_def_anti : antisymmetric les_def.
Proof.
move=>x y/andP[]/asboolP P1/asboolP P2; apply/summableP=>i.
by apply: le_anti; rewrite P1 P2.
Qed.

Lemma les_def_refl : reflexive les_def.
Proof. by move=>x; apply/asboolP. Qed.

Lemma les_def_trans : transitive les_def.
Proof.
move=>x y z/asboolP P1/asboolP P2; apply/asboolP=>i.
move: (P1 i) (P2 i); apply: le_trans.
Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build ring_display {summable I -> V}
  les_def_refl les_def_anti les_def_trans.

Lemma lesE f g : f ⊑ g = asbool (forall i, f i ⊑ g i).
Proof. by []. Qed.
Lemma lesP f g : f ⊑ g <-> (forall i, f i ⊑ g i).
Proof. by rewrite lesE; split=>/asboolP. Qed.
Lemma lesP1 f g : f ⊑ g -> (forall i, f i ⊑ g i).
Proof. by move=>/lesP. Qed.
Lemma lesP2 f g : (forall i, f i ⊑ g i) -> f ⊑ g.
Proof. by move=>/lesP. Qed.

Lemma les_add2rP h f g : f ⊑ g -> (f + h) ⊑ (g + h).
Proof. by move=>/lesP1 P1; apply/lesP2=>i; rewrite !summableE levD2r. Qed.  

Lemma les_pscale2lP (e : R[i]) f g : 0 < e -> f ⊑ g -> (e *: f) ⊑ (e *: g).
Proof. by move=>Pe /lesP1 P1; apply/lesP2=>i; rewrite !summableE lev_pscale2lP. Qed. 

Import VOrder.Exports.
HB.instance Definition _ := POrderedLmodule_isVOrder.Build R[i] {summable I -> V}
  les_add2rP les_pscale2lP.

Lemma closed_summable_ge f : closed [set g : {summable I -> V} | f ⊑ g ].
Proof.
apply: limn_in_closed=>/=g Pg Pc.
apply/lesP=>i; rewrite -summableE_lim//.
apply: lim_gev. by apply: summableE_is_cvg.
by move=>j; move: (Pg j)=>/lesP.
Qed.

Lemma closed_summable_le f : closed [set g : {summable I -> V} | g ⊑ f].
Proof.
apply: limn_in_closed=>/=g Pg Pc.
apply/lesP=>i; rewrite -summableE_lim//.
apply: lim_lev. by apply: summableE_is_cvg.
by move=>j; move: (Pg j)=>/lesP.
Qed.

Lemma lim_ges_nearF {T : Type} {F : set_system T} {FF : ProperFilter F} 
  f (u : T -> {summable I -> V}) :
    cvg (u @ F) -> (\forall n \near F, f ⊑ u n) -> f ⊑ lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (fun y => f ⊑ y))P; apply/P/closed_summable_ge. Qed.

Lemma lim_les_nearF {T : Type} {F : set_system T} {FF : ProperFilter F} 
  f (u : T -> {summable I -> V}) :
    cvg (u @ F) -> (\forall n \near F, u n ⊑ f) -> lim (u @ F) ⊑ f.
Proof. by move=> /[swap] /(closed_cvg (fun y => (y : {summable I -> V}) ⊑ f))P;
  apply/P/closed_summable_le. Qed.

Lemma les_lim_nearF {T : Type} {F : set_system T} {FF : ProperFilter F} 
  (u v : T -> {summable I -> V}) :
    cvg (u @ F) -> cvg (v @ F) -> 
      (\forall n \near F, u n ⊑ v n) -> lim (u @ F) ⊑ lim (v @ F).
Proof.
move=> cu cv uv; rewrite -(subv_ge0) -limB. apply: cv. apply: cu.
apply/lim_ges_nearF. apply: is_cvgB. apply: cv. apply: cu.
by near=>x; rewrite !fctE subv_ge0; near: x.
Unshelve. end_near.
Qed.

Implicit Type (x y : {vdistr I -> V}).
Definition levd_def x y := (x : {summable I -> V}) ⊑ y.
(* Definition ltvd_def x y := (y != x) && (levd_def x y). *)

Lemma levd_def_anti : antisymmetric levd_def.
Proof.
move=>x y/andP[]/asboolP P1/asboolP P2; apply/vdistrP=>i.
by apply: le_anti; rewrite P1 P2.
Qed.

(* Lemma ltvd_def_def : forall x y, ltvd_def x y = (y != x) && (levd_def x y).
Proof. by []. Qed. *)

HB.instance Definition _ := Order.Le_isPOrder.Build ring_display {vdistr I -> V}
  les_def_refl levd_def_anti les_def_trans.

Lemma levdEsub (x y : {vdistr I -> V}) : (x ⊑ y) = ((x : {summable I -> V}) ⊑ y).
Proof. by []. Qed.

Lemma levdE x y : x ⊑ y = asbool (forall i, x i ⊑ y i).
Proof. by []. Qed.
Lemma levdP x y : x ⊑ y <-> (forall i, x i ⊑ y i).
Proof. exact: lesP. Qed.
Lemma levdP1 x y : x ⊑ y -> (forall i, x i ⊑ y i).
Proof. by move=>/levdP. Qed.
Lemma levdP2 x y : (forall i, x i ⊑ y i) -> x ⊑ y.
Proof. by move=>/levdP. Qed.

End summable_porder.

Lemma psum_abs_ge0E (I : choiceType) (R : numFieldType) (x : I -> R) :
  (forall i, x i >= 0) -> psum \`| x | = psum x.
Proof.
by move=>P; apply/funext=>S; rewrite /psum; apply eq_bigr=>i _;
rewrite /normf ger0_norm.
Qed. 

(* cpo : deal with while loop *)
Section vdistr_lim.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.
Local Notation C := R[i].

Lemma vdistr_zero_subproof1 : forall i, (0 : V) ⊑ (\0 : I -> V) i.
Proof. by []. Qed.
Lemma vdistr_zero_subproof2 : `|sum (\0 : I -> V)| <= 1.
Proof.
rewrite/sum; have ->: psum (\0 : I -> V) = fun=>0 by apply/funext=>i; rewrite/psum big1.
by rewrite lim_cst// normr0.
Qed.
HB.instance Definition vdistr_zero_mixin := Summable_isVDistr.Build I R V \0
  vdistr_zero_subproof1 vdistr_zero_subproof2.
Definition vdistr_zero := VDistr.Pack (VDistr.Class vdistr_zero_mixin).

Lemma vdistr_lim_subproof1 (T : Type) (F : set_system T) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable I -> V}) @ F) -> 
    forall i, (0 : V) ⊑ lim ((f : T -> {summable I -> V}) @ F) i.
Proof.
move=>P i; rewrite -summableE_lim//.
move: (summableE_is_cvg (FF := FF) P)=>/(_ i).
apply: (closed_cvg (fun y=>(0 : V) ⊑ y)). apply/closed_gev.
near=>x; apply: vdistr_ge0.
Unshelve. end_near.
Qed.

Lemma vdistr_lim_subproof2 (T : Type) (F : set_system T) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable I -> V}) @ F) -> 
    `| sum (lim ((f : T -> {summable I -> V}) @ F)) | <= 1.
Proof.
move=>P.
have <-: lim (`| sum (f i) | @[i --> F]) = `| sum (lim ((f : T -> {summable I -> V}) @ F)) |.
rewrite lim_norm. by apply: summable_sum_is_cvg.
f_equal. by apply: summable_sum_lim.
apply: etlim_le. apply: is_cvg_norm. by apply: summable_sum_is_cvg.
move=>n. apply: vdistr_sum_le1.
Qed.

Definition vdlim (T : Type) (F : set_system T) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) : {vdistr I -> V} :=
  match (asboolP (cvg ((f : T -> {summable I -> V}) @ F))) with
  | ReflectT Q1 => VDistr.build (vdistr_lim_subproof1 Q1) (vdistr_lim_subproof2 Q1)
  | ReflectF _ => vdistr_zero
  end.

Lemma vdlimE (T : Type) (F : set_system T) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable I -> V}) @ F) -> 
    (@vdlim _ _ FF f : {summable I -> V}) = lim ((f : T -> {summable I -> V}) @ F).
Proof. by move=>?; rewrite/vdlim; case: asboolP=>[?|//]; apply/summableP. Qed.

Lemma vdlimEE (T : Type) (F : set_system T) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable I -> V}) @ F) -> 
    forall i, (@vdlim _ _ FF f) i = lim (f t i @[t --> F]).
Proof.
by move=>P i; move: {+}P=>/vdlimE/summableP/(_ i); rewrite summableE_lim.
Qed.

End vdistr_lim.

Notation "'nondecreasing_fset' f" := ({homo f : n m / (n `<=` m)%fset >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_fset' f" := ({homo f : n m / (n `<=` m)%fset >-> (m <= n)%O})
  (at level 10).

Section fset_R_lemmas.
Variable (R : realType) (I : choiceType).

Lemma nondecreasing_fset_cvg (u_ : {fset I} -> R) :
  nondecreasing_fset u_ -> has_ubound (range u_) ->
  u_ @ totally --> sup (range u_).
Proof.
move=> leu u_ub; set M := sup (range u_).
have su_ : has_sup (range u_) by split => //; exists (u_ fset0), fset0.
apply/cvgrPdist_le => _/posnumP[e].
have [p /andP[Mu_p u_pM]] : exists p, M - e%:num <= u_ p <= M.
  have [_ -[p _] <- /ltW Mu_p] := sup_adherent (gt0 e) su_.
  by exists p; rewrite Mu_p; have /ubP := sup_upper_bound su_; apply; exists p.
near=> n; have pn : (p `<=` n)%fset by near: n; exists p.
rewrite ler_distlC (le_trans Mu_p (leu _ _ _))//= (@le_trans _ _ M) ?lerDl//.
by have /ubP := sup_upper_bound su_; apply; exists n.
Unshelve. all: by end_near.
Qed.

Lemma nondecreasing_fset_is_cvg (u_ : {fset I} -> R) :
  nondecreasing_fset u_ -> has_ubound (range u_) -> cvg (u_ @ totally).
Proof. by move=> u_nd u_ub; apply: cvgP; apply: nondecreasing_fset_cvg. Qed.
End fset_R_lemmas.

Lemma cvg_limE (R: numFieldType) (V: completeNormedModType R) (T : Type) 
  (F : set_system T) {FF : ProperFilter F} (f: T -> V) (a: V) : 
    hausdorff_space V -> f @ F --> a <-> lim (f @ F) = a /\ cvg (f @ F).
Proof. 
split=>[P1|[ <-]//]. split. apply/cvg_lim. apply H.
apply P1. by move: P1=>/cvgP.
Qed.

Section ExtNumMonoFSet.
Variable (R: realType) (C: extNumType R) (I : choiceType).
(* monotone sequence; can extend to any lattice *)
(* once eventually filter applies to lattice *)
Definition etfset_shift (u_ : {fset I} -> C) := u_ - (fun=>u_ fset0).
Definition etfset_real (u_ : {fset I} -> C) := forall i, (u_ i) \is Num.real.

Lemma etfset_shiftE (u_ : {fset I} -> C) : etfset_shift u_ = u_ - (fun=>u_ fset0).
Proof. by []. Qed.
Lemma etfset_shiftEV (u_ : {fset I} -> C) : u_ = etfset_shift u_ + (fun=>u_ fset0).
Proof. by rewrite etfset_shiftE addrNK. Qed.

Lemma etnondecreasing_fset_shift (u_ : {fset I} -> C) : 
  nondecreasing_fset u_ <-> nondecreasing_fset (etfset_shift u_).
Proof. by split=>H i j /H; rewrite lerD2r. Qed.

Lemma etnondecreasing_fset_shift_real (u_ : {fset I} -> C) : 
  nondecreasing_fset u_ -> etfset_real (etfset_shift u_).
Proof. by move=>H i; rewrite ger0_real// subr_ge0 H. Qed.

Lemma etfset_shift_cvg (u_ : {fset I} -> C) a:
  (etfset_shift u_) @ totally --> a -> u_ @ totally --> a + u_ fset0.
Proof.
move=>P1; rewrite [u_]etfset_shiftEV.
by apply: cvgD=>//; rewrite /etfset_shift !fctE addrNK; apply: cvg_cst.
Qed.

Lemma etfset_shift_is_cvgE (u_ : {fset I} -> C) :
  cvg ((etfset_shift u_) @ totally) = cvg (u_ @ totally).
Proof. by rewrite /etfset_shift; apply/is_cvgDlE; apply: is_cvgN; apply: is_cvg_cst. Qed.

Lemma etfset_shift_lim (u_ : {fset I} -> C) :
  cvg (u_ @ totally) -> lim (u_ @ totally) = lim ((etfset_shift u_) @ totally) + u_ fset0.
Proof. by rewrite -etfset_shift_is_cvgE=>/etfset_shift_cvg; rewrite cvg_limE=>[|[]]. Qed.

Lemma etlim_fset_real (u_ : {fset I} -> C) : etfset_real u_ ->
  cvg (u_ @ totally) -> lim (u_ @ totally) \is Num.real.
Proof. by move=>P; apply: (closed_cvg _ etclosed_real)=>//; exists fset0=>/=. Qed.

Lemma c2r_fset_cvg_real (u_ : {fset I} -> C) (x : R) : etfset_real u_ ->
  ((c2r \o u_) @ totally --> x) -> (u_ @ totally --> r2c x).
Proof.
move=>ru cu; have ->: u_ = r2c \o (c2r \o u_) 
  by apply/funext=>i; rewrite !fctE c2rK//.
apply: etcvg_mapV=>//; apply r2c_continuous.
Qed.

Lemma c2r_fset_cvg_realV (u_ : {fset I} -> C) a : 
  u_ @ totally --> a -> (c2r \o u_) @ totally --> c2r a.
Proof. by move=>cu; apply: etcvg_map=>//; apply: c2r_continuous. Qed.

Lemma etnondecreasing_fset_cvg (u_ : {fset I} -> C) (M : C) :
      nondecreasing_fset u_ -> (forall n, u_ n <= M) -> 
        u_ @ totally --> r2c (lim ((c2r \o (etfset_shift u_)) @ totally)) + u_ fset0.
Proof.
move=>nd ub; move: {+}nd {+}nd=>/etnondecreasing_fset_shift P1/etnondecreasing_fset_shift_real P2.
pose v i := c2r ((etfset_shift u_) i).
have cv: cvg (v @ totally). apply: nondecreasing_fset_is_cvg.
  by move=>n m Pnm; rewrite /v -(@ler_r2c _ C) !c2rK// P1.
  exists (c2r (M - u_ fset0))=>i [x] _ <-.
  rewrite -(@ler_r2c _ C) /v !c2rK//.
  by rewrite ger0_real// subr_ge0. by rewrite lerD2r.
have Pu: u_ = (r2c \o v) + (fun=>u_ fset0)
by apply/funext=>i; rewrite !fctE /v c2rK// addrNK.
rewrite {1}Pu; apply: cvgD; last by apply: cvg_cst.
apply: etcvg_mapV. apply: r2c_continuous. apply: cv.
Qed.

Lemma etnondecreasing_fset_is_cvg (u_ : {fset I} -> C) (M : C) :
      nondecreasing_fset u_ -> (forall n, u_ n <= M) -> cvg (u_ @ totally).
Proof.
move=>nd ub. apply/cvg_ex;
exists (r2c (lim ((c2r \o (etfset_shift u_)) @ totally)) + u_ fset0);
apply: (etnondecreasing_fset_cvg nd ub).
Qed.

Lemma etnondecreasing_fset_cvg_le (u_ : {fset I} -> C) :
      nondecreasing_fset u_ -> cvg (u_ @ totally) ->
        (forall n, u_ n <= lim (u_ @ totally)).
Proof.
move=>nd cu n. move: {+}nd=>/etnondecreasing_fset_shift_real rus.
move: {+}cu; rewrite -etfset_shift_is_cvgE=>cus.
rewrite etfset_shift_lim// -lerBlDr.
suff: etfset_shift u_ n <= lim ((etfset_shift u_) @ totally) by [].
apply: etlim_ge_near. by apply: cus.
by exists n=>// m/=/nd; rewrite /etfset_shift !fctE lerD2.
Qed.

Lemma lt_etlim_fset (u : {fset I} -> C) (x : C) : nondecreasing_fset u -> 
  cvg (u @ totally) -> x < lim (u @ totally) -> \forall n \near totally, x <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, x <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n => // p q; apply/ndu.
have Cn n : x >=< (u n) by apply/(comparabler_trans 
  (lt_comparable Ml))/ge_comparable/etnondecreasing_fset_cvg_le.
have {}Mu : forall y, x > u y. move=> y. rewrite comparable_ltNge.
by rewrite comparable_sym. by apply/negP.
have : lim (u @ totally) <= x by apply: etlim_le_near=> //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near.
Qed.

End ExtNumMonoFSet.

Section nondecreasing_vdistr_cvg.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.

Variable (mnorm : vnorm V).
Local Notation C := R[i].
Local Notation "`[ x ]" := (mnorm x).
Hypothesis (mnorm_ge0D : forall x y, (0 : V) ⊑ x -> (0 : V) ⊑ y -> `[x + y] = `[x] + `[y]).

Let c1 : C := nosimpl (projT1 (cid2 (normv_lbounded mnorm)))^-1.
Let c2 : C := nosimpl (projT1 (cid2 (normv_ubounded mnorm))).

#[local] Lemma c1_gt0 : 0 < c1.
Proof. by rewrite invr_gt0; move: (projT2 (cid2 (normv_lbounded mnorm)))=>[] + _. Qed.
Local Hint Resolve c1_gt0 : core.

#[local] Lemma c2_gt0 : 0 < c2.
Proof. by move: (projT2 (cid2 (normv_ubounded mnorm)))=>[]. Qed.
Local Hint Resolve c2_gt0 : core.

#[local] Lemma mnorm_ge0_sum (J : Type) (r : seq J) (P : pred J) (f : J -> V) :
  (forall j, P j -> (0 : V) ⊑ f j) ->
    `[ \sum_(j <- r | P j) f j ] = \sum_(j <- r | P j) `[f j].
Proof.
move=>H; suff: (0 : V) ⊑ \sum_(j <- r | P j) f j /\ 
  `[ \sum_(j <- r | P j) f j ] = \sum_(j <- r | P j) `[f j] by move=>[].
elim/big_rec2: _; first by rewrite normv0.
by move=>j ? y Pj [] Py <-; split; rewrite ?addv_ge0 ?mnorm_ge0D// H.
Qed.

#[local] Lemma mnorm_ge0_mono (x y : V) : 
  (0 : V) ⊑ x ⊑ y -> `[x] <= `[y].
Proof.
move=>/andP[]x_ge0; rewrite -subv_ge0=> yx_ge0.
by rewrite -[y](addrNK x) mnorm_ge0D// lerDr.
Qed.
Local Hint Resolve mnorm_ge0_mono : core.

#[local] Lemma ubmnorm (x : V) : `|x| <= c1 * `[x].
Proof.
rewrite mulrC ler_pdivlMr 1?mulrC; 
by move: (projT2 (cid2 (normv_lbounded mnorm)))=>[].
Qed.
Local Hint Resolve ubmnorm : core.

#[local] Lemma lbmnorm (x : V) : `[x] <= c2 * `|x|.
Proof. by move: (projT2 (cid2 (normv_ubounded mnorm)))=>[]. Qed.
Local Hint Resolve lbmnorm : core.

Let mmap (x : {summable I -> V}) (i : I) := `[x i].
#[local] Lemma summable_mmap x : summable (mmap x).
Proof.
move: (summablefP x)=>[/= M PM].
exists (c2 * M). near=>J. have: psum \`| x | J <= M by near: J.
rewrite /mmap psum_abs_ge0E// -(ler_pM2l c2_gt0); apply/le_trans.
rewrite/psum mulr_sumr ler_sum//.
Unshelve. end_near.
Qed.

Local Canonical bounded_mmapx x := Bounded.build
  (bounded_summable (@summable_mmap x)).
Local Canonical summable_mmapx x := Summable.build (@summable_mmap x).

Let smnorm (x : {summable I -> V}) := sum (mmap x).
#[local] Lemma smnorm_ge0_mono (x y : {summable I -> V}) : 
  (0 : {summable I -> V}) ⊑ x ⊑ y -> smnorm x <= smnorm y.
Proof.
move=>/andP[/lesP Px /lesP Pyx].
rewrite /smnorm/sum; apply: ler_etlim; [apply: summable_cvg.. |].
by move=>S; apply/ler_sum=>i _; apply/mnorm_ge0_mono; rewrite Px Pyx.
Qed.
#[local] Lemma smnorm_ge0D (x y : {summable I -> V}) : 
  (0 : {summable I -> V}) ⊑ x -> (0 : {summable I -> V}) ⊑ y ->
    smnorm (x + y) = smnorm x + smnorm y.
Proof.
move=>/lesP /= Px /lesP /= Py; rewrite/smnorm -summable_sumD/=.
by f_equal; apply/funext=>i; rewrite /mmap/= mnorm_ge0D.
Qed.
#[local] Lemma smnorm_ge0B (x y : {summable I -> V}) : 
  (0 : {summable I -> V}) ⊑ x ⊑ y -> smnorm (y - x) = smnorm y - smnorm x.
Proof.
move=>/andP[]Px; rewrite -subv_ge0=>Py.
by rewrite -[LHS](addrK (smnorm x)) -smnorm_ge0D// addrNK.
Qed.
#[local] Lemma le_smnorm (x : {summable I -> V}) :
`|x| <= c1 * smnorm x.
Proof.
rewrite /Num.Def.normr/=/summable_norm /smnorm/sum.
have <- : lim ((fun _ : {fset I} => c1) @ totally) = c1. by apply: lim_cst.
rewrite -limM. apply: is_cvg_cst. apply: summable_cvg.
apply: ler_etlim; [apply: summable_cvg| |].
apply: is_cvgMr; apply: summable_cvg.
by move=>S/=; rewrite/psum /normf mulr_sumr ler_sum// /mmap.
Qed.
Local Hint Resolve le_smnorm : core.
#[local] Lemma ge_smnorm (x : {summable I -> V}) :
  smnorm x <= c2 * `|x|.
Proof.
rewrite /Num.Def.normr/=/summable_norm /smnorm/sum.
have <- : lim ((fun _ : {fset I} => c2) @ totally) = c2. by apply: lim_cst.
rewrite -limM. apply: is_cvg_cst. apply: summable_cvg.
apply: ler_etlim; [apply: summable_cvg| |].
apply: is_cvgMr; apply: summable_cvg.
by move=>S/=; rewrite/psum mulr_sumr ler_sum// /mmap.
Qed.
Local Hint Resolve ge_smnorm : core.

Program Definition smnorm_vnorm_mixin := @isVNorm.Build
  R[i] {summable I -> V} smnorm _ _ _.
Next Obligation.
move=>x y; rewrite /smnorm -summable_sumD/sum.
apply: ler_etlim; [apply: summable_cvg.. |].
by move=>S; rewrite/psum ler_sum// =>??; rewrite /=/mmap/= lev_normD.
Qed.
Next Obligation.
move=>x Px; apply/eqP; rewrite -normr_eq0; apply/eqP/le_anti/andP; split=>//.
by apply/(le_trans (le_smnorm _)); rewrite Px mulr0.
Qed.
Next Obligation.
move=>c x; rewrite /smnorm/sum.
have <- : lim ((fun _ : {fset I} => `|c|) @ totally) = `|c|. by apply: lim_cst.
rewrite -limM. apply: is_cvg_cst. apply: summable_cvg.
by apply: eq_lim=>S; rewrite/=/psum/mmap mulr_sumr; apply eq_bigr=>??; rewrite normvZ.
Qed.
#[local] HB.instance Definition _ := smnorm_vnorm_mixin.

Lemma vdistr_norm_ubound : exists c, 0 < c /\ forall (f : {vdistr I -> V}),
  `|f : {summable I -> V}| <= c.
Proof.
exists (c1 * c2).
split. by apply/mulr_gt0.
move=>f. apply/(le_trans (le_smnorm _)). rewrite ler_pM2l//.
rewrite/smnorm/sum. apply: etlim_le.
apply: summable_cvg.
move=>S. rewrite/psum -mnorm_ge0_sum ?psumE=>[??|]. apply: vdistr_ge0.
apply/(le_trans (y := `[sum f])).
by apply/mnorm_ge0_mono/andP; rewrite psum_vdistr_ge0 psum_vdistr_lev_sum.
by apply/(le_trans (lbmnorm _)); rewrite ger_pMr// vdistr_sum_le1.
Qed.

Lemma snondecreasing_norm_is_cvgn (f : nat -> {summable I -> V}) (b : C) :
  nondecreasing_seq f -> (forall i, `|f i| <= b) -> cvgn f.
Proof.
move=>P1 P2.
pose g := (fun i => f i - f 0%N).
suff Pg: cvgn g.
  have ->: f = (fun i => g i + f 0%N) by apply/funext=>i; rewrite/g addrNK.
  apply: is_cvgD. apply: Pg. apply: is_cvg_cst.
pose gn := (fun x => smnorm x) \o g.
have gmono: nondecreasing_seq g by move=>m n Pmn; rewrite/g levD2r P1.
have: cvgn gn.
  apply: (cnondecreasing_is_cvgn (M := c2 * b + smnorm (f 0%N)))=>[m n Pmn|n].
  by apply/smnorm_ge0_mono/andP; rewrite levD2r subv_ge0; split=>//; apply/P1.
  rewrite/gn/=/g; apply/(le_trans (lev_normB _ _)); rewrite lerD2r/=.
  apply/(le_trans (ge_smnorm _)); rewrite ler_pM2l//.
move=>/cauchy_cvgP/cauchy_ballP Pgn.
apply/cauchy_cvgP/cauchy_ballP=>e egt0; rewrite near_simpl.
have ecgt0 : 0 < e / c1 by rewrite divr_gt0.
near=>n. 
have: ball (gn n.1) (e / c1) (gn n.2).
  by near: n; move: (Pgn _ ecgt0); rewrite near_simpl.
near: n. apply: nearW=>[[m n]]/=.
wlog le_ij: m n / (n <= m)%N => [th_sym|].
by case: (orP (leq_total m n))=>/th_sym// Pi /ball_sym Pj; apply/ball_sym/Pi.
rewrite /ball/=/gn/= -{1}[g m](addrNK (g n)) smnorm_ge0D ?subv_ge0 ?P1// ?gmono//.
rewrite addrK ger0_norm// ?normv_ge0// ltr_pdivlMr// mulrC.
by apply/le_lt_trans/le_smnorm.
Unshelve. end_near.
Qed.

#[local] Lemma smnorm_ler_abs (x : {summable I -> V}) : `[sum x] <= sum (mmap x).
Proof.
rewrite/sum -lim_normv. apply: summable_cvg.
apply: ler_etlim. apply: is_cvg_normv. apply: summable_cvg. apply: summable_cvg.
move=>n; rewrite /psum/mmap. apply: normv_sum.
Qed.
Local Hint Resolve smnorm_ler_abs : core.

Lemma snondecreasing_fset_norm_is_cvg (J : choiceType) (f : {fset J} -> {summable I -> V}) (b : C) :
  nondecreasing_fset f -> (forall i, `|f i| <= b) -> cvg (f @ totally).
Proof.
move=>P1 P2.
pose g := (fun i => f i - f fset0).
suff Pg: cvg (g @ totally).
  have ->: f = (fun i => g i + f fset0) by apply/funext=>i; rewrite/g addrNK.
  apply: is_cvgD. apply: Pg. apply: is_cvg_cst.
pose gn := (fun x => smnorm x) \o g.
have gmono: nondecreasing_fset g by move=>m n Pmn; rewrite/g levD2r P1.
have: cvg (gn @ totally).
  apply: (etnondecreasing_fset_is_cvg (M := c2 * b + smnorm (f fset0)))=>[m n Pmn|n].
  by apply/smnorm_ge0_mono/andP; rewrite levD2r subv_ge0; split=>//; apply/P1.
  rewrite/gn/=/g; apply/(le_trans (lev_normB _ _)); rewrite lerD2r/=.
  apply/(le_trans (ge_smnorm _)); rewrite ler_pM2l//.
move=>/cauchy_cvgP/cauchy_ballP Pgn.
apply/cauchy_cvgP/cauchy_exP=>e egt0.
have ecgt0 : 0 < e / c1 by rewrite divr_gt0.
move: (Pgn _ ecgt0); rewrite near_simpl.
move=>[[x1 x2]]/=[[s1 _ Ps1][s2 _ Ps2]] Px.
pose S := (s1 `|` s2)%fset.
have Ps: forall s, (S `<=` s)%fset -> ball (gn s) (e/c1) (gn S).
  move=>s Ps; apply: (Px (s, S)); split.
  apply/Ps1/(fsubset_trans _ Ps)/fsubsetUl. apply/Ps2/fsubsetUr.
exists (g S); exists S=>// T/= PST; apply/ball_sym.
move: (Ps _ PST); rewrite/ball/=/gn/= -smnorm_ge0B.
  apply/andP; split; last by apply: gmono.
  by move: (gmono fset0 S (fsub0set _)); rewrite /g addrN.
rewrite ger0_norm ?normv_ge0// ltr_pdivlMr// mulrC; apply/le_lt_trans/le_smnorm.
Qed.

Lemma snondecreasing_is_cvgn (f : nat -> {summable I -> V}) (b : {summable I -> V}) :
  nondecreasing_seq f -> ubounded_by b f -> cvgn f.
Proof.
move=>P1 P2; apply: (snondecreasing_norm_is_cvgn (b := c1 * (smnorm (b - f 0%N) + smnorm (f 0%N))))=>//.
move=>i. apply/(le_trans (le_smnorm _)). rewrite ler_pM2l// -lerBlDr.
apply/(le_trans (levB_dist _ _))/smnorm_ge0_mono.
by rewrite subv_ge0 levD2r P2 andbT P1.
Qed.

Lemma vdnondecreasing_is_cvgn (f : nat -> {vdistr I -> V}) :
  nondecreasing_seq f -> cvgn (f : nat -> {summable I -> V}).
Proof.
move=>P1. apply: (snondecreasing_norm_is_cvgn (b := c1 * c2))=>//.
move=>i. apply/(le_trans (le_smnorm _)). rewrite ler_pM2l//.
rewrite/smnorm/mmap/sum. apply: etlim_le.
by move: (summable_cvg (f := Summable.build (summable_mmap (f i)))).
move=>S. apply/(le_trans (y := `[sum (f i)])).
rewrite/psum -mnorm_ge0_sum ?psumE=>[??|]. apply: vdistr_ge0.
by apply/mnorm_ge0_mono; rewrite psum_vdistr_lev_sum psum_vdistr_ge0.
by apply/(le_trans (lbmnorm _)); rewrite ger_pMr// vdistr_sum_le1.
Qed.

Lemma vdnondecreasing_cvg_le (f : nat -> {vdistr I -> V}) :
  nondecreasing_seq f -> ubounded_by (vdlim (FF := eventually_filter) f) f.
Proof.
move=>Ph i; move: (vdnondecreasing_is_cvgn Ph)=>Pc; rewrite levdEsub vdlimE//.
apply: lim_ges_nearF=>//. exists i=>// n/=; apply: Ph.
Qed.

End nondecreasing_vdistr_cvg.

Import ArrowAsUniformType.
Lemma uniform_fct_cvg {U : choiceType} {V : uniformType} (f : U -> V) 
  (F : set_system (U -> V)) {FF: Filter F} :
  {uniform, F --> f} <-> F --> f.
Proof. by rewrite /cvg_to uniform_nbhsT. Qed.

Lemma ptws_fct_cvg {I : Type} {U : choiceType} {V : uniformType} (f : I -> U -> V) (g : U -> V)
  (F : set_system I) {FF: ProperFilter F} :
  {ptws, f i @[i --> F] --> g} <-> forall u : U, f i u @[i --> F] --> g u.
Proof.
rewrite cvg_sup; split. 
all: move=>P u; move: (P u); rewrite cvg_image; 
  first by rewrite eqEsubset; split=> v // _; exists (cst v).
all: apply: cvg_trans => W /=; rewrite nbhs_simpl/=/nbhs/=/nbhs/=.
by move=>[x] Px <-; move: Px; apply: filterS=>i/= Pi; exists (f i).
move=>PF; exists [set h | W (h u) ]; first by move: PF; apply: filterS.
by apply/funext=>v/=; rewrite propeqE; split=>[[h] + <-//|PS]; exists (cst v).
Qed.

Section exchange_lim.
Context {R : numFieldType} {V : completeNormedModType R}.

Lemma e2gt0 (e : R) : e > 0 -> e / 2 > 0. 
Proof. by move=>P; apply: divr_gt0=>//; apply: ltr0n. Qed.

Lemma exchange_lim_cvg {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (b : J -> V) (c : I -> V) :
    {uniform, a i @[i --> F] --> b} -> (forall i, (a i j @[j --> G]) --> c i) ->
    cvg (c i @[i --> F]) /\ 
    b j @[j --> G] --> lim (c i @[i --> F]).
Proof.
move=>/uniform_fct_cvg uc ca.
move: (cvg_switch FF FG uc ca)=>[l []P1 P2].
split. by apply/cvg_ex; exists l.
by rewrite (cvg_lim _ P1).
Qed.

Lemma exchange_lim_near2 {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (b : J -> V) (c : I -> V) :
    {uniform, a i @[i --> F] --> b} -> (forall i, (a i j @[j --> G]) --> c i) ->
    forall e, e > 0 -> \forall i \near F & j \near G, `|lim (c i @[i --> F]) - a i j| < e.
Proof.
move=>uc1 ca. move: {+}uc1=>/uniform_fct_cvg uc.
move: (@exchange_lim_cvg _ _ _ _ FF FG _ _ _ uc1 ca)=>[]Pc Pb.
move=>e egt0.
move: uc=>/cvg_ball/(_ _ (e2gt0 egt0)); rewrite/ball/=/fct_ball/= -ball_normE/= -nbhs_nearE /nbhs/==> F1.
move: Pb=>/cvgrPdist_lt/(_ _ (e2gt0 egt0)); rewrite -nbhs_nearE/nbhs/==>F2.
rewrite near2E -nbhs_nearE!/nbhs/=/filter_prod/=/filter_from/=.
exists ((fun x : I => forall t : J, `|b t - a x t| < e / 2), 
  (fun t : J => is_true (`|lim (c i @[i --> F]) - b t| < e / 2)))=>/=.
by rewrite/nbhs/=; split.
move=>[i j]/=[]/(_ j) P1 P2.
by rewrite [e]splitr; apply/(le_lt_trans (ler_distD (b j) _ _))/ltrD.
Qed.

Lemma exchange_liml {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
    (forall i, (a i j @[j --> G]) --> c i) ->
    lim ((lim (a i j @[j --> G])) @[i --> F]) = lim (c i @[i --> F]).
Proof.
move=>ca; suff ->: (fun i => lim (a i j @[j --> G])) = c by [].
by apply/funext=>i; move: (ca i); apply/cvg_lim.
Qed.

Lemma exchange_limr {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
    cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> G]) --> c i) ->
    lim ((lim (a i j @[i --> F])) @[j --> G]) = lim (c i @[i --> F]).
Proof.
move=>uc ca; move: {+}uc=>/uniform_fct_cvg uc1.
move: (@exchange_lim_cvg _ _ _ _ FF FG _ _ _ uc1 ca)=>[]Pc Pb.
suff ->: (fun j => lim (a i j @[i --> F])) = lim (a i @[i --> F]) by move: Pb=>/cvg_lim ->.
apply/funext=>j; apply: cvg_lim=>//.
by move: uc=>/uniform_fct_cvg/pointwise_uniform_cvg/ptws_fct_cvg.
Unshelve. all: end_near.
Qed.

Lemma exchange_lim {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    lim ((lim (a i j @[j --> G])) @[i --> F]) = 
    lim ((lim (a i j @[i --> F])) @[j --> G]).
Proof. by move=>uc ca; rewrite (exchange_limr uc ca); apply: exchange_liml. Qed.

Lemma fct_diag_cvg {I : choiceType} {F : set_system I}
  {FF : ProperFilter F} (a : I -> I -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> F]) --> c i) ->
    (a i i @[i --> F]) --> lim (c i @[i --> F]).
Proof.
move=>/uniform_fct_cvg uc ca.
apply/cvgrPdist_lt=>e egt0; move: (@exchange_lim_near2 _ _ _ _ FF FF _ _ _ uc ca _ egt0).
rewrite -nbhs_nearE near2E -nbhs_nearE!/nbhs/=/filter_prod/=/filter_from/=.
move=>[[i1 i2]]/=[] F1 F2 PF; move: (@filterI _ _ FF _ _ F1 F2).
by apply: filterS=>i; move: (PF (i,i))=>/=.
Qed.

Lemma fct_diag_lim {I : choiceType} {F : set_system I}
  {FF : ProperFilter F} (a : I -> I -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> F]) --> c i) ->
    lim (a i i @[i --> F]) = lim (c i @[i --> F]).
Proof. by move=>uc ca; apply: cvg_lim=>//; apply: (fct_diag_cvg uc ca). Qed.

Lemma fct_diag_liml {I : choiceType} {F : set_system I}
  {FF : ProperFilter F} (a : I -> I -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> F])) ->
    lim ((lim (a i j @[j --> F])) @[i --> F]) = lim (a i i @[i --> F]).
Proof. by move=>uc ca; rewrite (fct_diag_lim uc ca) (exchange_liml ca). Qed.

Lemma fct_diag_limr {I : choiceType} {F : set_system I}
  {FF : ProperFilter F} (a : I -> I -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> F])) ->
    lim ((lim (a i j @[i --> F])) @[j --> F]) = lim (a i i @[i --> F]).
Proof. by move=>uc ca; rewrite (fct_diag_lim uc ca) (exchange_limr uc ca). Qed.

Lemma exchange_lim_pair_cvg {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> G]) --> c i) ->
    (a k.1 k.2 @[k --> (F,G)]) --> lim (c i @[i --> F]).
Proof.
move=>/uniform_fct_cvg uc ca; apply/cvgrPdist_lt=>e egt0/=.
apply: (@exchange_lim_near2 _ _ _ _ FF FG _ _ _ uc ca _ egt0).
Qed.

Lemma exchange_lim_pair_is_cvg {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    cvg (a k.1 k.2 @[k --> (F,G)]).
Proof.
move=>uc; move=>/(exchange_lim_pair_cvg uc) P; apply/cvg_ex; 
by exists (lim (lim (a i j @[j --> G]) @[i --> F])). 
Qed.

Lemma exchange_lim_pair_lim {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> G]) --> c i) ->
    lim (a k.1 k.2 @[k --> (F,G)]) = lim (c i @[i --> F]).
Proof. by move=>uc; move=>/(exchange_lim_pair_cvg uc)/cvg_lim<-. Qed.

Lemma exchange_liml_pair {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    lim (a k.1 k.2 @[k --> (F,G)]) = lim ((lim (a i j @[j --> G])) @[i --> F]).
Proof. move=>uc ca; rewrite (exchange_liml ca); exact: exchange_lim_pair_lim. Qed.

Lemma exchange_limr_pair {I J : choiceType} {F : set_system I} {G : set_system J}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    lim (a k.1 k.2 @[k --> (F,G)]) = lim ((lim (a i j @[i --> F])) @[j --> G]).
Proof. move=>uc ca; rewrite (exchange_limr uc ca); exact: exchange_lim_pair_lim. Qed.

End exchange_lim.

Lemma exchange_limn_nondecreasing (R : realType) (C : extNumType R) 
  (V : vorderFinNormedModType C) (ff : nat -> nat -> V) (b : V) :
  (forall i, nondecreasing_seq (ff i)) ->
  (forall j, nondecreasing_seq (ff ^~ j)) ->
  (forall i j, ff i j <= b) ->
    limn (fun i => limn (ff i)) = limn (fun j => limn (ff ^~ j)).
Proof.
move=>Pi Pj Ub.
have P1 i : cvgn (ff i).
  apply: (vnondecreasing_is_cvgn (b := b)). apply: Pi. apply: Ub.
have P2 j : cvgn (ff ^~ j).
  apply: (vnondecreasing_is_cvgn (b := b)). apply: Pj. move=>i; apply: Ub.
have P4 : cvgn (fun j : nat => limn (ff^~ j)).
  apply: (vnondecreasing_is_cvgn (b := b)).
  move=>n m Pnm. apply: lev_limn. apply: P2. apply: P2. by move=>i; apply: Pi.
  move=>j; apply: limn_lev. apply: P2. by move=>i; apply: Ub.
have P3 : cvgn (fun i : nat => limn (ff i)).
  apply: (vnondecreasing_is_cvgn (b := b)).
  move=>n m Pnm. apply: lev_limn. apply: P1. apply: P1. by move=>j; apply: Pj.
  move=>i; apply: limn_lev. apply: P1. apply: Ub.
apply/le_anti/andP; split.
  apply: limn_lev; first by apply: P3.
  move=>i; apply: lev_limn. apply: P1. apply: P4.
  move=>j. apply: nondecreasing_cvgn_lev. apply: Pj. apply: P2.
apply: limn_lev; first by apply: P4.
move=>j; apply: lev_limn. apply: P2. apply: P3.
move=>i. apply: nondecreasing_cvgn_lev. apply: Pi. apply: P1.
Qed.

Lemma limn_diag_nondecreasing (R : realType) (C : extNumType R) 
  (V : vorderFinNormedModType C) (ff : nat -> nat -> V) (b : V) :
  (forall i, nondecreasing_seq (ff i)) ->
  (forall j, nondecreasing_seq (ff ^~ j)) ->
  (forall i j, ff i j <= b) ->
    limn (fun i => limn (ff i)) = limn (fun i => ff i i).
Proof.
move=>Pi Pj Ub.
have P1 i : cvgn (ff i).
  apply: (vnondecreasing_is_cvgn (b := b)). apply: Pi. apply: Ub.
have P3 : cvgn (fun i : nat => limn (ff i)).
  apply: (vnondecreasing_is_cvgn (b := b)).
  move=>n m Pnm. apply: lev_limn. apply: P1. apply: P1. by move=>j; apply: Pj.
  move=>i; apply: limn_lev. apply: P1. apply: Ub.
have P5 : cvgn (fun i : nat => ff i i).
  apply: (vnondecreasing_is_cvgn (b := b)).
  by move=>n m Pnm; apply/(le_trans (Pi n n m Pnm))/Pj.
  move=>i; apply: Ub.
apply/le_anti/andP; split.
  apply: limn_lev; first by apply: P3.
  move=>i; apply: lev_limn_near. apply: P1. apply: P5.
  exists i=>//= j /=; apply: Pj.
apply: lev_limn. apply: P5. apply: P3.
move=>i. apply: lim_gev_near. apply: P1.
exists i=>//= j /=; apply: Pi.
Qed.

(* extend to extNumType *)
Section ExchangeSum.
Variable (R0 : realType).
Implicit Type (R : completeNormedModType R0).
Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Definition series2 R (f : nat -> nat -> R) (m n : nat) :  R :=
  series (fun i => series (f i) n) m.
    (* \sum_(0 <= i < m)\sum_(0 <= j < n) f i j. *)

Lemma foo2 R (f : nat -> R) : 
    (exists M, forall N, \sum_(0 <= i < N) `|f i| <= M) -> cvgn (series f).
Proof.
move=>[]M PM; suff: cvgn (series \`|f|) by exact: normed_cvg.
apply: nondecreasing_is_cvgn.
by move=>m n Pm; rewrite -subr_ge0 sub_series_geq// sumr_ge0//.
exists M=>?/=[]N _<-; apply: PM.
Qed.

Lemma foo3 R (f : nat -> nat -> R) :
    (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M) ->
        (forall i, cvgn (series (f i))) /\ cvgn (series (fun i => limn (series (f i)))).
Proof.
move=>[]M PM.
have P2: forall i, cvgn (series (f i)).
    move=>i; apply: foo2; exists M=>N.
    move: (PM (i.+1) N); apply: le_trans.
    by rewrite big_nat_recr/= ?leq0n// lerDr sumr_ge0// =>? _; apply/sumr_ge0.

have Pc: cvgn (series (fun i => limn (series (f i)))).
apply/foo2; exists M=>N.
rewrite (eq_bigr (fun i => limn \`|series (f i)|)); last first.
rewrite -lim_sum_apply; last first. apply: limr_le; last first.
near=>N2; apply/(le_trans _ (PM N N2))/ler_sum=>??; apply: ler_norm_sum.
apply: is_cvg_sum_apply. 1,2: move=>??; apply: is_cvg_norm; apply: P2.
move=>??; symmetry; apply: lim_norm; apply: P2.

by split.
Unshelve. end_near.
Qed.

Import ArrowAsUniformType.

Lemma foo4 R (f : nat -> nat -> R) :
  (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M) ->
    cvgn (series2 f : nat -> nat -> R) /\
    (forall i, cvgn (series2 f i)).
Proof.
move=>P1. move: (foo3 P1)=>[]P2 _.

have Pa: exists M, forall N1 N2, 
    \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|(fun i j => `|f i j|) i j| <= M.
by move: P1=>[]M PM; exists M=>N1 N2; under eq_bigr do under eq_bigr do rewrite normr_id.
move: (foo3 Pa)=>[] P3 P4.

split; last by move=>i; apply: is_cvg_sum_apply=>j _; apply: P2.
apply/(@cauchy_cvgP (arrow_uniform_type nat R)).
apply/cauchy_ballP=>e egt0; rewrite near_simpl.
move: P4=>/cauchy_cvgP/cauchy_ballP/(_ _ egt0); rewrite near_simpl.
move=>[][]/=a b[][N1] _ PN1[]N2 _ PN2 PN.
exists ([set n | (maxn N1 N2 <= n)%N] , [set n | (maxn N1 N2 <= n)%N])=>//=.
split; by exists (maxn N1 N2).
move=>[m n]/=[].
wlog le_ij: m n / (n <= m)%N => [th_sym|].
case: (orP (leq_total m n))=>/th_sym// + Pi Pj; move=>/(_ Pj Pi); apply: ball_sym.

move=>Pm Pn; rewrite/ball/=/fct_ball=>k; rewrite -ball_normE/= /series2 sub_series le_ij.
have Pab: a m /\ b n by move: Pm Pn; rewrite !geq_max=>/andP[]/PN1+ _ /andP[] _ /PN2.
move: (PN (m, n))=>/(_ Pab)/=; rewrite -ball_normE/= sub_series le_ij.
apply/le_lt_trans/(le_trans (ler_norm_sum _ _ _)); rewrite ger0_norm. 
by apply: sumr_ge0=>??; apply: etlimn_ge=>[|?]; [apply: P3| apply: sumr_ge0].
apply: ler_sum=>??. apply: etlimn_ge_near. apply: P3.
exists k=>// l/= Pk; apply/(le_trans (ler_norm_sum _ _ _)).
by rewrite -subr_ge0 sub_series Pk sumr_ge0.
Qed.

Lemma series2_limnl R (f : nat -> nat -> R) :
    (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M)
        -> limn (series (fun i => limn (series (f i)))) = limn (fun i => series2 f i i).
Proof.
move=>P; move: {+}P=>/foo4[] P1 P2.
rewrite -[RHS](fct_diag_liml P1 P2).
apply: eq_lim=>i.
rewrite/series/= -lim_sum_apply// =>j _.
by move: P=>/foo3[]/(_ j) + _.
Qed.

Lemma series2_limnr R (f : nat -> nat -> R) :
    (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M)
        -> limn (series (fun j => limn (series (f ^~ j)))) = limn (fun i => series2 f i i).
Proof.
move=>P; move: {+}P=>/foo4[] P1 P2.
rewrite -[RHS](fct_diag_limr P1 P2).
apply: eq_lim=>i.
under [RHS]eq_lim do rewrite /series/= exchange_big.
rewrite/series/= -lim_sum_apply// =>j _.
have: exists M : R0, forall N2 N1 : nat, \sum_(0 <= j < N2) \sum_(0 <= i < N1) `|f i j| <= M.
by move: P=>[M PM]; exists M=>N2 N1; move: (PM N1 N2); rewrite exchange_big.
by move=>/foo3[]/(_ j) + _.
Qed.

Lemma series_exchange_limn R (f : nat -> nat -> R) :
  (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M) ->
  limn (series (fun i => limn (series (f i)))) = limn (series (fun i => limn (series (f ^~ i)))).
Proof. by move=>P; rewrite series2_limnl// series2_limnr. Qed.

End ExchangeSum.

Lemma normrB_close_eq (R : numDomainType) (V : normedZmodType R) (u v : V) :
  (forall e, e > 0 -> `| u - v | < e) -> u = v.
Proof.
move=>P. apply/eqP; case E: (u != v); last by move: E=>/eqP->.
move: E=>/eqP/eqP; rewrite -subr_eq0 - normr_gt0=>/(P _).
rewrite lt_def eqxx//.
Qed.

Section ExchangePsum.
Context {R : realType} {C : extNumType R}.
Implicit Type (I J : choiceType) (V : completeNormedModType C).

Let pseries I J V (f : I -> J -> V) Si Sj :=
  psum (fun i : I => psum (fun j : J => f i j) Sj) Si.

Lemma psum_ubounded_summable I V (f : I -> V) : 
  (exists M, forall S, psum \`|f| S <= M) -> summable f.
Proof. by move=>[M PM]; exists M; apply: nearW. Qed.

Lemma pseries_ubounded_cvg (I J : choiceType) (V : completeNormedModType C) 
  (f : I -> J -> V) :
  (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
    (forall i, summable (f i)) /\ (forall i, cvg (psum (f i) @ totally)) /\
    (summable (fun i : I => sum (f i))) /\ (cvg (psum (fun i => sum (f i)) @ totally))
    /\ cvg (psum (fun x : I => `|sum (f x)|) @ totally).
Proof.
move=>[Mu Pu].
have H0: (forall i, summable (f i)).
  by move=>i; exists Mu; near=>Sj; move: (Pu [fset i]%fset Sj); rewrite /pseries psum1.
have H1: (forall i, cvg (psum (f i) @ totally)) by move=>i; apply: norm_bounded_cvg; apply: H0.
have H2: summable (fun i : I => sum (f i)).
  exists Mu; near=>Si; rewrite/psum.
  rewrite (eq_bigr (fun i : Si => lim (`|psum (f (val i)) x| @[x --> totally]%classic))).
  move=>i _; symmetry; apply: lim_norm. apply: H1.
  rewrite -lim_sum_apply; last apply: etlim_le; last first.
  move=>Sj; apply/(le_trans _ (Pu Si Sj))/ler_sum=>??; apply: ler_norm_sum.
  apply: is_cvg_sum_apply. 1,2: move=>??; apply: is_cvg_norm; apply: H1.
do !split. apply: H0. apply: H1. apply: H2.
apply: norm_bounded_cvg; apply: H2.
by move: (summable_norm_is_cvg (f := Summable.build H2))=>/=.
Unshelve. all: end_near.
Qed.

Lemma pseries_uniform_cvg I J V (f : I -> J -> V) :
  (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
    cvg ((pseries f : {fset I} -> {fset J} -> V) @ totally) /\
    (forall Si, cvg ((pseries f Si) @ totally)).
Proof.
move=>P1; move: (pseries_ubounded_cvg P1)=>[] _ [] P2 _.
have P1': exists M, forall Si Sj, pseries (fun i : I => \`| (fun i j => `|f i j|) i |) Si Sj <= M.
  move: P1=>[]M PM; exists M=>Si Sj; move: (PM Si Sj); rewrite/pseries/psum; 
  by under [in X in _ -> X]eq_bigr do under eq_bigr do rewrite /normf normr_id.
move: (pseries_ubounded_cvg P1')=>[] _ [] P3 [] _ [] P4 _.

split; last by move=>i; apply: is_cvg_sum_apply=>j _; apply: P2.
apply/(@cauchy_cvgP (arrow_uniform_type {fset J} V)).
apply/cauchy_ballP=>e egt0; rewrite near_simpl.
move: P4=>/cauchy_cvgP/cauchy_ballP/(_ _ egt0); rewrite near_simpl.
move=>[][]/=a b[][Si1] _ PSi1[]Si2 _ PSi2 PSi.
exists ([set S1 | (Si1 `|` Si2 `<=` S1)%fset] , [set S2 | (Si1 `|` Si2 `<=` S2)%fset])=>//=.
split; by exists (Si1 `|` Si2)%fset.
move=>[S1 S2]/=[] PS1 PS2.
rewrite/ball/=/fct_ball=>Sj; rewrite -ball_normE/= /pseries -psumIB.
apply: (le_lt_trans (y := psum (fun i : I => psum \`|f i| Sj) ((S1 `|` S2) `\` (S1 `&` S2))%fset)).
rewrite fsetDUl !fsetDIr !fsetDv fset0U fsetU0 psumU ?fdisjointXDg// ?fdisjointDX//.
apply/(le_trans (ler_normB _ _))/lerD; rewrite /psum;
apply/(le_trans (ler_norm_sum _ _ _))/ler_sum=>??; apply/ler_norm_sum.
have Pab: a (S1 `|` S2)%fset /\ b (S1 `&` S2)%fset.
  split; last by apply/PSi2/(fsubset_trans (fsubsetUr Si1 _))/fsubsetIP; split.
  by apply/PSi1/(fsubset_trans _ (fsubsetUl _ _))/(fsubset_trans _ PS1)/fsubsetUl.
move: (PSi (S1 `|` S2, S1 `&` S2)%fset)=>/(_ Pab)/=.
rewrite -ball_normE/= -psumIB -fsetDDl fsetDIl fsetDv fset0I fset0D psum0 subr0.
apply/le_lt_trans. rewrite ger0_norm. 
by apply: sumr_ge0=>??; apply: etlim_ge=>[|?]; [apply: P3| apply: sumr_ge0].
apply: ler_sum=>??. apply: etlim_ge_near. apply: P3. 
exists Sj=>// Sj'/=; by apply/psum_ler.
Qed.

Lemma pseries2_exchange_lim I J V (f : I -> J -> V) :
    (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
      sum (fun i => sum (f i)) = sum (fun j => sum (f ^~ j)).
Proof.
move=>P. move: {+}P=>/pseries_uniform_cvg[] P1 P2; rewrite/sum.
transitivity (lim (lim (pseries f i j @[j --> totally]) @[i --> totally])).
apply: eq_lim=>Si. rewrite /pseries lim_sum_apply//==>i _.
by move: P=>/pseries_ubounded_cvg[] _ []/(_ (fsval i)) + _.
rewrite (exchange_lim P1 P2).
have Q: exists M : C, forall Sj Si , pseries (fun j : J => \`| f ^~ j |) Sj Si <= M.
  move: P=>[M PM]; exists M=>Sj Si; move: (PM Si Sj); apply: le_trans.
  by rewrite/pseries /psum exchange_big.
transitivity (lim (lim (pseries (fun i j => f j i) j i @[i --> totally]) @[j --> totally])).
by apply: eq_lim=>Sj; apply: eq_lim=>Si; rewrite/pseries/psum exchange_big.
apply: eq_lim=>Sj. rewrite /pseries lim_sum_apply//==>j _.
by move: Q=>/pseries_ubounded_cvg[] _ []/(_ (fsval j)) + _.
Qed.

Lemma pseries2_exchange_lim_pair I J V (f : I -> J -> V) :
    (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
      sum (fun k => f k.1 k.2) = sum (fun i => sum (f i)).
Proof.
move=>P. move: {+}P=>/pseries_uniform_cvg[] P1 P2; rewrite/sum.
transitivity (lim (lim (pseries f i j @[j --> totally]) @[i --> totally])); last first.
apply: eq_lim=>Si. rewrite /pseries lim_sum_apply//==>i _.
by move: P=>/pseries_ubounded_cvg[] _ []/(_ (fsval i)) + _.
rewrite -(exchange_liml_pair P1 P2).
have /cvgrPdist_lt Pc1: cvg (pseries f k.1 k.2 @[k --> (totally, totally)])
by apply: (exchange_lim_pair_is_cvg P1 P2).
have /cvgrPdist_lt Pc2: cvg (psum (fun k : prod I J => f k.1 k.2) @ totally).
apply: norm_bounded_cvg. move: {+}P=>[M PM].
exists M. near=>K.
apply/(le_trans (y := \sum_(i <- (fst @` K)%fset)\sum_(j <- (snd @` K)%fset) 
  `|f i j|)).
rewrite pair_big_dep_cond/= big_seq_fsetE psum_ler//=.
apply/fsubsetP=>[[a b PK]]; rewrite !inE/= !andbT; apply/andP; split;
apply/imfsetP; exists (a,b)=>//.
rewrite big_seq_fsetE; under eq_bigr do rewrite big_seq_fsetE; apply PM.
apply: normrB_close_eq=>e egt0.
move: (Pc1 _ (e2gt0 egt0))=>[[/=SSi SSj[[Si/= _ PSi][Sj/= _ PSj] PS]]].
move: (Pc2 _ (e2gt0 egt0))=>[/=S2 _ PS2].
pose Ti := (Si `|` (fst @` S2))%fset.
pose Tj := (Sj `|` (snd @` S2))%fset.
have /PS/=: (SSi `*` SSj) (Ti, Tj) by split=>/=; [apply/PSi/fsubsetUl|apply/PSj/fsubsetUl].
have /PS2/=: [set B | (S2 `<=` B)%fset] [fset ((i, j) : I * J) | i in Ti, j in Tj]%fset.
by apply/fsubsetP=>i Pi; rewrite !inE; apply/andP; split; apply/orP; right; apply/imfsetP; exists i.
have ->: psum (fun k : I * J => f k.1 k.2) [fset ((i, j) : I * J) | i in Ti, j in Tj]%fset = 
  pseries f Ti Tj.
rewrite/pseries !psum_seq_fsetE; under [in RHS]eq_bigr do rewrite psum_seq_fsetE.
by rewrite pair_big_dep_cond/=; apply: eq_fbigl=>i; rewrite !inE andbT andbT.
rewrite -normrN opprB=>Q1 Q2. rewrite -[lim ((psum _) @ totally)](subrK (pseries f Ti Tj)).
rewrite -[_ + _ - _]addrA [e]splitr.
by apply/(le_lt_trans (ler_normD _ _))/ltrD; rewrite -normrN opprB.
Unshelve. end_near.
Qed.

End ExchangePsum.