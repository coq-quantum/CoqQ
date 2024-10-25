From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
(* topology and setoid has notation conflicts *)
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra mcaextra notation.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.

(****************************************************************************)
(*                  A simple formalization of Convex hulls                  *)
(* Further define + *: \o :o for the addition, scale, composition of        *)
(*   linear functions and superoperators.                                   *)
(*   A + B  = {a + b  | a \in A & b \in B}                                  *)
(*   c *: A = {c *: a | a \in A & b \in B}                                  *)
(*   A \o B = {a \o b | a \in A & b \in B}                                  *)
(* ------------------------------------------------------------------------ *)
(* Show that conv(A + B) = conv A + conv B;                                 *)
(****************************************************************************)

Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Lemma image2_set11 {TA TB rT : Type} a b (f : TA -> TB -> rT) :
  [set f x y | x in [set a] & y in [set b]]%classic = [set f a b]%classic.
Proof. by apply/predeqP => x; split=>[[?->][?->]//|->]/=; exists a=>//; exists b. Qed.

Lemma image2_set1l {TA TB rT : Type} a B (f : TA -> TB -> rT) :
  [set f x y | x in [set a] & y in B]%classic = [set f a y | y in B]%classic.
Proof.
apply/predeqP => x; split=>[[?->][b P <-]|[b P <-]]/=.
by exists b. by exists a=>//; exists b.
Qed.

Lemma image2_set1r {TA TB rT : Type} A b (f : TA -> TB -> rT) :
  [set f x y | x in A & y in [set b]]%classic = [set f x b | x in A]%classic.
Proof.
apply/predeqP => x; split=>[[a P][?-><-]|[a P]<-]/=.
by exists a. by exists a=>//; exists b.
Qed.
Definition image2_set1 := (@image2_set11, @image2_set1l, @image2_set1r, @image_set1).

Lemma eq_set1 T (a b : T) :
  ([set a] = [set b])%classic -> a = b.
Proof. by move=>/predeqP/(_ a)/=[] + _; apply. Qed.

Section ConvexSet.
Variable (C : numFieldType) (V : lmodType C).
Definition conv (S : set V) :=
  [set v : V | exists (F : finType) (c : F -> C) (f : F -> V), 
    (forall i, 0 <= c i <= 1) /\ (\sum_i c i = 1) 
    /\ (forall i, f i \in S) /\ (v = \sum_i c i *: f i) ]%classic.

Lemma conv_le S : (S `<=` conv S)%classic.
Proof.
move=>x Px; exists unit; exists (fun => 1); exists (fun => x); do ! split.
by rewrite lexx ler01.
by rewrite sumr_const card_unit.
by rewrite inE.
by rewrite sumr_const card_unit mulr1n scale1r.
Qed.

Lemma conv_idem S : conv (conv S) = conv S.
Proof.
apply/seteqP; split; last by apply: conv_le.
move=>x; rewrite /conv/==>[[F][c][f][]Pc1[]Pc2[]Pf Px].
have Pi i : exists (Fi : finType) (cf : Fi -> (C * V)),
  (forall i0, 0 <= (cf i0).1 <= 1) /\
  \sum_i0 (cf i0).1 = 1 /\ (forall i0, (cf i0).2 \in S) /\
  (f i = \sum_i0 (cf i0).1 *: (cf i0).2).
  move: (Pf i); rewrite inE/==>[[Fi][ci][fi] P].
  by exists Fi; exists (fun i0=> (ci i0, fi i0))=>/=.
pose Fi i := projT1 (cid (Pi i)).
pose cfi i := projT1 (cid (projT2 (cid (Pi i)))).
exists {i : F & Fi i}.
exists (fun j : {i : F & Fi i} => c (projT1 j) * (cfi _ (projT2 j)).1).
exists (fun j : {i : F & Fi i} => (cfi _ (projT2 j)).2).
have Pi1 i := proj1 (projT2 (cid (projT2 (cid (Pi i))))).
have Pi2 i := proj1 (proj2 (projT2 (cid (projT2 (cid (Pi i)))))).
have Pi3 i := proj1 (proj2 (proj2 (projT2 (cid (projT2 (cid (Pi i))))))).
have Pi4 i := proj2 (proj2 (proj2 (projT2 (cid (projT2 (cid (Pi i))))))).
do ! split.
- move=>i; apply/andP; split;
  [rewrite mulr_ge0// | rewrite mulr_ile1//].
  1,3,5: by move: (Pc1 (projT1 i))=>/andP[].
  1,2,3: by move: (Pi1 _ (projT2 i))=>/andP[].
- transitivity (\sum_i \sum_(j : Fi i) c i * (cfi i j).1).
  by rewrite sig_big_dep.
  by rewrite -Pc2; apply eq_bigr=>i _; rewrite -mulr_sumr Pi2 mulr1.
- move=>i; apply: Pi3.
- transitivity (\sum_i \sum_(j : Fi i) (c i * (cfi i j).1) *: (cfi i j).2).
  rewrite Px; apply eq_bigr=>i _.
  by rewrite Pi4 scaler_sumr; apply eq_bigr=>j _; rewrite scalerA.
  by rewrite sig_big_dep.
Qed.

Lemma conv_le_hom (S1 S2 : set V) : 
  (S1 `<=` S2 -> conv S1 `<=` conv S2)%classic.
Proof.
move=>P x [F][c][f] [Pi1][Pi2][Pi3]Pi4.
exists F; exists c; exists f; do ! split=>//.
by move=>i; move: (P (f i)); move: (Pi3 i); rewrite !inE; auto.
Qed.

Lemma conv1 v : conv [set v] = [set v].
Proof.
apply/seteqP; split=>x /=.
  move=>[F][c][f][P1][P2][P3]->/=.
  have Pv i : f i = v by move: (P3 i); rewrite inE.
  under eq_bigr do rewrite Pv.
  by rewrite -scaler_suml P2 scale1r.
move=>->; exists unit; exists (fun=>1); exists (fun=>v).
do ! split.
by rewrite ler01 lexx.
by rewrite sumr_const card_unit.
by rewrite inE.
by rewrite sumr_const card_unit mulr1n scale1r.
Qed.

End ConvexSet.

Section ConvexLinear.

Lemma conv_linear (C : numFieldType) (U V : lmodType C) (f : {linear U -> V}) (S : set U) :
  (conv (f @` S) = f @` (conv S))%classic.
Proof.
apply/seteqP; split=>x /=.
rewrite /conv/==>[[F][c][g][Pi1][Pi2][Pi3]Pi4].
have Pi: forall i, exists xi, S xi /\ f xi = g i.
  by move=>i; move: (Pi3 i); rewrite inE/==>[[xi Pxi <-]]; exists xi.
exists (\sum_i c i *: projT1 (cid (Pi i))).
exists F; exists c; exists (fun i => projT1 (cid (Pi i))); do ! split=>//.
by move=>i; rewrite inE; move: (projT2 (cid (Pi i)))=>[].
rewrite linear_sum Pi4; apply eq_bigr=>i _.
by rewrite linearZ/=; move: (projT2 (cid (Pi i)))=>[] _ ->.
move=>[y] + <-; rewrite /conv/==>[[F][c][g][Pi1][Pi2][Pi3]Pi4].
exists F; exists c; exists (fun i => f (g i)); do ! split=>//.
by move=>i; rewrite inE/=; exists (g i)=>//; move: (Pi3 i); rewrite inE.
by rewrite Pi4 linear_sum; under eq_bigr do rewrite linearZ.
Qed.

Lemma ler_conj (R : numClosedFieldType) (a b : R) :
  (a^* <= b^*) = (a <= b).
Proof. by rewrite -subr_ge0 -rmorphB conjC_ge0 subr_ge0. Qed.

Lemma conv_antilinear (C : numClosedFieldType) (U V : lmodType C) 
  (f : {linear U -> V | Num.conj_op \; *:%R}) (S : set U) :
  (conv (f @` S) = f @` (conv S))%classic.
Proof.
apply/seteqP; split=>x /=.
rewrite /conv/==>[[F][c][g][Pi1][Pi2][Pi3]Pi4].
have Pi: forall i, exists xi, S xi /\ f xi = g i.
  by move=>i; move: (Pi3 i); rewrite inE/==>[[xi Pxi <-]]; exists xi.
exists (\sum_i (c i)^* *: projT1 (cid (Pi i))).
exists F; exists (fun i => (c i)^*); exists (fun i => projT1 (cid (Pi i))); do ! split=>//.
by move=>i; rewrite -conjC0 -conjC1 !ler_conj.
by rewrite -rmorph_sum Pi2 conjC1.
by move=>i; rewrite inE; move: (projT2 (cid (Pi i)))=>[].
rewrite linear_sum Pi4; apply eq_bigr=>i _.
by rewrite linearZ/= conjCK; move: (projT2 (cid (Pi i)))=>[] _ ->.
move=>[y] + <-; rewrite /conv/==>[[F][c][g][Pi1][Pi2][Pi3]Pi4].
exists F; exists (fun i => (c i)^*); exists (fun i => f (g i)); do ! split=>//.
by move=>i; rewrite -conjC0 -conjC1 !ler_conj.
by rewrite -rmorph_sum Pi2 conjC1.
by move=>i; rewrite inE/=; exists (g i)=>//; move: (Pi3 i); rewrite inE.
by rewrite Pi4 linear_sum; under eq_bigr do rewrite linearZ.
Qed.

End ConvexLinear.

Section SetAdd.
Variable (R : numFieldType) (U : lmodType R).

Definition set_add (A B : set U) :=
  [set a + b | a in A & b in B].
Definition set_scale (c : R) (A : set U) :=
  [set c *: a | a in A].
Infix "`*:`" := set_scale (at level 40).

Lemma set_add0l : left_id  [set 0] set_add.
Proof.
move=>A; rewrite /set_add image2_set1; apply/seteqP; split=>i/=.
by move=>[x Px]; rewrite add0r=><-.
by move=>Pi; exists i=>//; rewrite add0r.
Qed.

Lemma set_addC : commutative set_add.
Proof.
move=>A B; apply/seteqP; split=>i;
by move=>[a Pa][b Pb]<-; exists b=>//; exists a=>//; rewrite addrC.
Qed.

Lemma set_addA : associative set_add.
Proof.
move=>A B C; apply/seteqP; split=>i.
  move=>[a Pa][?][b Pb][c Pc]<-<-.
  exists (a + b); first by exists a=>//; exists b.
  by exists c=>//; rewrite addrA.
move=>[?][a Pa][b Pb]<-[c Pc]<-.
exists a=>//; exists (b + c); first by exists b=>//; exists c.
by rewrite addrA.
Qed.

HB.instance Definition _ := GRing.isNmodule.Build (set U)
  set_addA set_addC set_add0l.

Lemma set_addxl u A : [set u] + A = [set u + i | i in A].
Proof. by rewrite /GRing.add/= /set_add image2_set1. Qed.

Lemma set_addxr u A : A + [set u] = [set i + u | i in A].
Proof. by rewrite /GRing.add/= /set_add image2_set1. Qed.

Lemma set_add_le A B C D : 
  A `<=` C -> B `<=` D -> A + B `<=` C + D.
Proof.
move=>P1 P2 ? [a Pa][b Pb]<-; exists a; first by apply P1.
by exists b=>//; apply P2.
Qed.
Lemma set_add_lel A B C :
  B `<=` C -> A + B `<=` A + C.
Proof. by move=>P1; apply/set_add_le. Qed.
Lemma set_add_ler A B C :
  B `<=` C -> B + A `<=` C + A.
Proof. by move=>P1; apply/set_add_le. Qed.

Lemma set_sum_le T r (P : pred T) (f g : T -> set U) :
  (forall i, P i -> f i `<=` g i) ->
    (\sum_(i <- r | P i) f i `<=` \sum_(i <- r | P i) g i).
Proof.
move=>IH; elim/big_rec2: _=>// i y1 y2 Pi.
by apply/set_add_le/IH.
Qed.

Lemma conv_add (A B : set U) :
  (conv A) + (conv B) = conv (A + B).
Proof.
apply/seteqP; split.
  move=>x [xa [Fa][ca][fa][Pa1][Pa2][Pa3]Pa4] [xb [Fb][cb][fb][Pb1][Pb2][Pb3]Pb4] <-.
  exists (Fa * Fb)%type.
  exists (fun i=>ca i.1 * cb i.2).
  exists (fun i=>fa i.1 + fb i.2).
  do ! split.
  - move=>[i1 i2]/=; rewrite mulr_ge0 ?mulr_ile1//; 
    by move: (Pa1 i1) (Pb1 i2)=>/andP[]++/andP[].
  - by rewrite pair_bigV/= -Pa2; apply eq_bigr=>i _; rewrite -mulr_sumr Pb2 mulr1.
  - move=>[i1 i2]; rewrite inE/=;
    exists (fa i1); first by move: (Pa3 i1); rewrite inE.
    by exists (fb i2)=>//; move: (Pb3 i2); rewrite inE.
  - under eq_bigr do rewrite scalerDr {1}mulrC -!scalerA.
    rewrite big_split/= !pair_bigV/=; f_equal; last rewrite exchange_big.
    1,2: rewrite ?Pa4 ?Pb4; apply eq_bigr=>i _; 
    by rewrite /= -scaler_suml ?Pa2 ?Pb2 scale1r.
move=>?[F][c][f][P1][P2][P3]->.
have P4 i: exists2 x, (f i = x.1 + x.2) & ((x.1 \in A) && (x.2 \in B)).
  move: (P3 i); rewrite inE=>[[a Pa][b Pb]<-].
  by exists (a,b)=>//=; apply/andP; rewrite !inE.
exists (\sum_i c i *: (projT1 (cid2 (P4 i))).1).
exists F; exists c; exists (fun i=>(projT1 (cid2 (P4 i))).1).
by do ! split=>//; move=>i; move: (projT2 (cid2 (P4 i)))=>[] _ /andP[].
exists (\sum_i c i *: (projT1 (cid2 (P4 i))).2).
exists F; exists c; exists (fun i=>(projT1 (cid2 (P4 i))).2).
by do ! split=>//; move=>i; move: (projT2 (cid2 (P4 i)))=>[] _ /andP[].
rewrite -big_split; apply eq_bigr=>i _ /=.
by rewrite -scalerDr; f_equal; move: (projT2 (cid2 (P4 i)))=>[].
Qed.

Lemma conv0 : conv 0 = 0.
Proof.
apply/seteqP; split=>x; rewrite /GRing.zero/=.
move=>[F][c][f][] _ [] _ [] Pi ->.
have P i : f i = 0 by move: (Pi i); rewrite inE.
under eq_bigr do rewrite P scaler0.
by rewrite sumr_const mul0rn.
move=>->; exists 'I_1; exists (fun=>1); exists (fun=>0); do ! split;
by rewrite ?ler01 ?lexx// ?inE// big_ord1// scale1r.
Qed.

Lemma conv_sum T (r : seq T) (P : pred T) (f : T -> set U) :
  (\sum_(i <- r | P i) conv (f i)) = 
    conv (\sum_(i <- r | P i) (f i)).
Proof.
elim/big_rec2: _ => [|/=????->]; first by rewrite conv0.
by rewrite conv_add.
Qed.

Lemma big_set_add_ordP n (f : 'I_n -> set U) x :
  reflect (exists v : 'I_n -> U, (forall i, v i \in f i) /\ \sum_i (v i) = x)
    (x \in \sum_i (f i)).
Proof.
elim: n f x.
  move=>??; rewrite big_ord0.
  apply/(iffP idP); rewrite inE/=.
  by move=>->; exists (fun=>0); split; [case | rewrite big_ord0].
  by move=>[] x [] _; rewrite big_ord0.
move=>n IH; case/fconsP=>x f u.
apply/(iffP idP); rewrite inE big_ord_recl fcons0; 
under eq_bigr do rewrite fconsE.
  rewrite {1}/GRing.add /set_add/==>[[v Pv][w Pw]]<-.
  have: (w \in \big[set_add/[set 0]]_(i < n) f i) by rewrite inE.
  move=>/IH [g][] P1 <-; exists (fcons v g); split.
  by move=>i; case: (unliftP ord0 i)=>/=[j|]->; rewrite ?fconsE// !fcons0 inE.
  by rewrite big_ord_recl fcons0; under [in LHS]eq_bigr do rewrite fconsE.
move=>[g][Pg]<-; rewrite {1}/GRing.add /set_add/=.
exists (g 0); first by move: (Pg 0); rewrite fcons0 inE.
exists (\sum_(i < n) g (nlift ord0 i)).
rewrite -inE; apply/IH; exists (ftail g); split=>//.
by move=>i; rewrite /ftail; move: (Pg (nlift ord0 i)); rewrite fconsE.
by rewrite big_ord_recl.
Qed.

Lemma big_set_addP (T : finType) (f : T -> set U) x :
  reflect (exists v : T -> U, (forall i, v i \in f i) /\ \sum_i (v i) = x)
    (x \in \sum_i (f i)).
Proof.
apply/(iffP idP).
  rewrite big_enum_val/==>/big_set_add_ordP=>[[v][Pv]<-].
  exists (fun i => v (enum_rank i)); split.
  by move=>i; move: (Pv (enum_rank i)); rewrite enum_rankK.
  by rewrite big_enum_val/=; under eq_bigr do rewrite enum_valK.
move=>[v][Pv]<-.
rewrite [X in _ \in X]big_enum_val/=.
apply/big_set_add_ordP; exists (fun i => v (enum_val i)); split.
move=>i; apply: Pv.
by rewrite [RHS]big_enum_val.
Qed.

Lemma set_scalex a b : a `*:` [set b] = [set a *: b].
Proof.
apply/seteqP; split=>x/=.
by move=>[?]/=-><-. by move=>->; exists b.
Qed.

Lemma set_scaleA a b A : a `*:` (b `*:` A) = (a * b) `*:` A.
Proof.
rewrite /set_scale; apply/seteqP; split=>?/=.
by move=>[?][x Px]<-<-; exists x=>//; rewrite scalerA.
move=>[x Px]<-; exists (b *: x).
by exists x. by rewrite scalerA.
Qed.

Lemma set_scale1r : left_id 1 set_scale.
Proof.
move=>A; apply/seteqP; split=>t/=.
by move=>[x Ax]<-; rewrite scale1r.
by move=>At; exists t=>//; rewrite scale1r.
Qed.

Lemma set_scaleDr : right_distributive set_scale +%R.
Proof.
move=>c A B; apply/seteqP; split=>x /=.
  move=>[?][a Pa][b Pb]<-<-.
  exists (c *: a); first by exists a.
  exists (c *: b); first by exists b.
  by rewrite scalerDr.
move=>[?][a Pa]<-[?][b Pb]<-<-.
exists (a + b); first by exists a=>//; exists b.
by rewrite scalerDr.
Qed.

Lemma set_scale0x A : A !=set0 -> 0 `*:` A = 0.
Proof.
move=>[x Px]; apply/seteqP; split=>? /=.
by move=>[a Pa]; rewrite scale0r=><-.
by rewrite {1}/GRing.zero/==>->; exists x=>//; rewrite scale0r.
Qed.

Lemma set_scalex0 c : c `*:` 0 = 0.
Proof.
apply/seteqP; split=>? /=; rewrite /GRing.zero/=.
by move=>[x]/==>-><-; rewrite scaler0.
by move=>->; exists 0=>//; rewrite scaler0.
Qed.

Lemma set_scale_sumr a I r (P : pred I) (F : I -> set U) :
  a `*:` (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) a `*:` F i.
Proof. exact: big_endo (set_scaleDr a) (set_scalex0 a) I r P F. Qed.

Lemma conv_scale a A : conv (a `*:` A) = a `*:` conv A.
Proof. by apply: conv_linear. Qed.

Lemma set_scale_le a A B :
  A `<=` B -> a `*:` A `<=` a `*:` B.
Proof. by move=>P ? [x /P Bx]<-; exists x. Qed.

Lemma set_scaleDl_le a b A : 
  (a + b) `*:` A `<=` a `*:` A + b `*:` A.
Proof.
move=>?[x Px]<-; exists (a *: x); first by exists x.
exists (b *: x); first by exists x.
by rewrite scalerDl.
Qed.

Lemma conv_scaleDl (a b : R) A : 0 <= a -> 0 <= b ->
  (a + b) `*:` conv A = a `*:` conv A + b `*:` conv A.
Proof.
move=>Pa Pb; apply/seteqP; split; first by apply: set_scaleDl_le.
move=>?[?[x Px]<-][?][y Py]<-<-.
move: Pa Pb; rewrite !le_eqVlt=>/orP[/eqP<- _|Pa].
by rewrite scale0r !add0r; exists y.
move=>/orP[/eqP<-|Pb].
by rewrite scale0r !addr0; exists x.
exists (a/(a+b) *: x + b/(a+b) *: y).
rewrite -conv_idem.
exists bool; exists (fun i=>if i then a/(a+b) else b/(a+b));
exists (fun i => if i then x else y); do ! split.
- case; rewrite divr_ge0/= ?ler_pdivrMr ?mul1r ?lerDl ?lerDr;
  by (try apply/ltW=>//); apply/addr_gt0.
- by rewrite big_bool/= -mulrDl mulfV//; apply/lt0r_neq0/addr_gt0.
- by case; rewrite inE.
- by rewrite big_bool/=.
by rewrite scalerDr !scalerA mulrC mulfVK 1?mulrC ?mulfVK//;
  apply/lt0r_neq0/addr_gt0.
Qed.

End SetAdd.
Infix "`*:`" := set_scale (at level 40).

Lemma set_add_map (R : numFieldType) (U V : lmodType R) (f : {additive U -> V}) (A B : set U) :
  f @` (A + B) = (f @` A) + (f @` B).
Proof.
apply/seteqP; split=>?/=.
move=>[?][a Pa][b Pb]<-<-; exists (f a); first by exists a.
exists (f b); first by exists b. by rewrite raddfD.
move=>[?][a Pa]<-[?][b Pb]<-<-; exists (a + b).
by exists a=>//; exists b. by rewrite raddfD.
Qed.

Section SetComp.
Variable (R : numFieldType) (U : vectType R).

Definition set_comp (A B : set 'End(U)) :=
  [set a \o b | a in A & b in B].
Infix "`\o`" := set_comp (at level 50).

Lemma set_comp1l : left_id  [set \1] set_comp.
Proof.
move=>A; rewrite /set_comp image2_set1; apply/seteqP; split=>i/=.
by move=>[x Px]; rewrite comp_lfun1l=><-.
by move=>Pi; exists i=>//; rewrite comp_lfun1l.
Qed.

Lemma set_comp1r : right_id  [set \1] set_comp.
Proof.
move=>A; rewrite /set_comp image2_set1; apply/seteqP; split=>i/=.
by move=>[x Px]; rewrite comp_lfun1r=><-.
by move=>Pi; exists i=>//; rewrite comp_lfun1r.
Qed.

Lemma set_compA : associative set_comp.
Proof.
move=>A B C; apply/seteqP; split=>i.
  move=>[a Pa][?][b Pb][c Pc]<-<-.
  exists (a \o b); first by exists a=>//; exists b.
  by exists c=>//; rewrite comp_lfunA.
move=>[?][a Pa][b Pb]<-[c Pc]<-.
exists a=>//; exists (b \o c); first by exists b=>//; exists c.
by rewrite comp_lfunA.
Qed.

HB.instance Definition _ := Monoid.isLaw.Build (set 'End(U)) [set \1]
  set_comp set_compA set_comp1l set_comp1r.

Lemma set_compxl u A : [set u] `\o` A = [set u \o i | i in A].
Proof. by rewrite /set_comp image2_set1. Qed.

Lemma set_compxr u A : A `\o` [set u] = [set i \o u | i in A].
Proof. by rewrite /set_comp image2_set1. Qed.

Lemma set_comp_le A B C D : 
  A `<=` C -> B `<=` D -> A `\o` B `<=` C `\o` D.
Proof.
move=>P1 P2 ? [a Pa][b Pb]<-; exists a; first by apply P1.
by exists b=>//; apply P2.
Qed.
Lemma set_comp_lel A B C :
  B `<=` C -> A `\o` B `<=` A `\o` C.
Proof. by move=>P1; apply/set_comp_le. Qed.
Lemma set_comp_ler A B C :
  B `<=` C -> B `\o` A `<=` C `\o` A.
Proof. by move=>P1; apply/set_comp_le. Qed.

Lemma set_comp0l A : A !=set0 -> 0 `\o` A = 0.
Proof.
move=>[x Px]; apply/seteqP; split=>?; rewrite /GRing.zero/=.
by move=>[y]/=->[]??<-; rewrite comp_lfun0l.
by move=>->; exists 0=>//; exists x=>//; rewrite comp_lfun0l.
Qed.

Lemma set_comp0r A : A !=set0 -> A `\o` 0 = 0.
Proof.
move=>[x Px]; apply/seteqP; split=>?; rewrite /GRing.zero/=.
by move=>[??][?]/=-><-; rewrite comp_lfun0r.
by move=>->; exists x=>//; exists 0=>//; rewrite comp_lfun0r.
Qed.

Lemma set_compDl (A B C : set 'End(U)) : 
  A `\o` (B + C) `<=` A `\o` B + (A `\o` C).
Proof.
move=>x[a Pa][?][/=b Pb][c Pc]<-<-.
exists (a \o b); first by exists a=>//; exists b.
exists (a \o c); first by exists a=>//; exists c.
by rewrite comp_lfunDr.
Qed.

Lemma set_compDr (A B C : set 'End(U)) : 
  (A + B) `\o` C `<=` A `\o` C + (B `\o` C).
Proof.
move=>x[?][/=a Pa][b Pb]<-[c Pc]<-.
exists (a \o c); first by exists a=>//; exists c.
exists (b \o c); first by exists b=>//; exists c.
by rewrite comp_lfunDl.
Qed.

Lemma set_compxDl c (A B : set 'End(U)) : 
  [set c] `\o` (A + B) = [set c] `\o` A + ([set c] `\o` B).
Proof.
rewrite !set_compxl; apply/seteqP; split=>?/=.
move=>[?][a Pa][b Pb]<-<-; exists (c \o a); first by exists a.
exists (c \o b); first by exists b. by rewrite comp_lfunDr.
move=>[?][a Pa]<-[?][b Pb]<-<-; exists (a + b).
by exists a=>//; exists b. by rewrite comp_lfunDr.
Qed.

Lemma set_compxDr c (A B : set 'End(U)) : 
  (A + B) `\o` [set c] = A `\o` [set c] + (B `\o` [set c]).
Proof.
rewrite !set_compxr; apply/seteqP; split=>?/=.
move=>[?][a Pa][b Pb]<-<-; exists (a \o c); first by exists a.
exists (b \o c); first by exists b. by rewrite comp_lfunDl.
move=>[?][a Pa]<-[?][b Pb]<-<-; exists (a + b).
by exists a=>//; exists b. by rewrite comp_lfunDl.
Qed.

Lemma set_compZl a A B :
  a `*:` (A `\o` B) = (a `*:` A) `\o` B.
Proof.
apply/seteqP; split=>/=?.
move=>[/=?][x Px][y Py]<-<-; exists (a *: x); first by exists x.
by exists y=>//; rewrite comp_lfunZl.
move=>[?][/=x Px]<-[y Py]<-; exists (x \o y); last by rewrite comp_lfunZl.
by exists x=>//; exists y.
Qed.

Lemma set_compZr a A B :
  a `*:` (A `\o` B) = A `\o` (a `*:` B).
Proof.
apply/seteqP; split=>/=?.
move=>[/=?][x Px][y Py]<-<-; exists x=>//.
exists (a *: y); by [exists y | rewrite comp_lfunZr].
move=>[x Px][?][/= y Py]<-<-.
exists (x \o y); last by rewrite comp_lfunZr.
by exists x=>//; exists y.
Qed.

Lemma conv_comp A B :
  conv ((conv A) `\o` (conv B)) = conv (A `\o` B).
Proof.
apply/seteqP; split.
  rewrite -[conv (A `\o` B)]conv_idem; apply/conv_le_hom.
  move=>x [xa [Fa][ca][fa][Pa1][Pa2][Pa3]Pa4] [xb [Fb][cb][fb][Pb1][Pb2][Pb3]Pb4] <-.
  exists (Fa * Fb)%type.
  exists (fun i=>ca i.1 * cb i.2).
  exists (fun i=>fa i.1 \o fb i.2).
  do ! split.
  - move=>[i1 i2]/=; rewrite mulr_ge0 ?mulr_ile1//; 
    by move: (Pa1 i1) (Pb1 i2)=>/andP[]++/andP[].
  - by rewrite pair_bigV/= -Pa2; apply eq_bigr=>i _; rewrite -mulr_sumr Pb2 mulr1.
  - move=>[i1 i2]; rewrite inE/=;
    exists (fa i1); first by move: (Pa3 i1); rewrite inE.
    by exists (fb i2)=>//; move: (Pb3 i2); rewrite inE.
  - under eq_bigr do rewrite -scalerA comp_lfunZr comp_lfunZl.
    rewrite Pa4 Pb4 pair_bigV/= linear_suml; apply eq_bigr=>i _.
    by rewrite/= linear_sumr.
by apply/conv_le_hom/set_comp_le; apply/conv_le.
Qed.

End SetComp.
Infix "`\o`" := set_comp (at level 50).

