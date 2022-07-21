(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import forms.
From mathcomp.analysis Require Import reals.
From mathcomp.real_closed Require Import complex.

Require Import mcextra prodvect hermitian tensor setdec EqdepFacts Eqdep_dec mxpred.

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

(* -------------------------------------------------------------------- *)
Import Vector.InternalTheory.

Local Notation C := hermitian.C.

(* ==================================================================== *)
Section SetExtra.
Variable (L: finType).
Implicit Type (S T W : {set L}).

Lemma disjointP S T : reflect (forall a, a \in S -> a \notin T) [disjoint S & T].
Proof. rewrite disjoint_subset; apply (iffP subsetP); by move=>+ a; move=>/(_ a). Qed.

Lemma disjoint0X S : [disjoint set0 & S].
Proof. by rewrite -setI_eq0 set0I. Qed.

Lemma disjointX0 S : [disjoint S & set0].
Proof. by rewrite -setI_eq0 setI0. Qed.

Lemma disjointXXP S : reflect (S = set0) [disjoint S & S].
Proof. by apply (iffP setDidPl); rewrite setDv=>->. Qed.

Lemma disjointXD S T : [disjoint S & (T :\: S)].
Proof. by apply/disjointP => x; apply contraTT; move/negbNE/setDP=>[_ H2]. Qed.

Lemma disjointDX S T : [disjoint (T :\: S) & S].
Proof. by apply/disjointP => x; move/setDP=>[_ H2]. Qed.

Lemma disjointXC S : [disjoint S & ~: S].
Proof. by rewrite -setI_eq0 setICr. Qed.

Lemma disjointCX S : [disjoint ~: S & S].
Proof. by rewrite disjoint_sym disjointXC. Qed.

Lemma disjointXDg S T C: [disjoint S & T] -> [disjoint S & T :\: C].
Proof. by rewrite -!setI_eq0 setIDA => /eqP ->; rewrite set0D. Qed.

Lemma disjointDXg S T C: [disjoint S & T] -> [disjoint S :\: C & T].
Proof. by rewrite ![[disjoint _ & T]]disjoint_sym; apply disjointXDg. Qed.

Lemma disjoint1X x S : [disjoint [set x] & S] = (x \notin S).
Proof. by apply (@eq_disjoint1 _ _ [set x])=>y; rewrite inE. Qed.

Lemma disjointX1 x S : [disjoint S & [set x]] = (x \notin S).
Proof. by rewrite disjoint_sym disjoint1X. Qed.

Lemma disjointUX S T W :
   [disjoint S :|: T & W] = [disjoint S & W] && [disjoint T & W].
Proof. by rewrite -!setI_eq0 setIUl setU_eq0. Qed.

Lemma disjointXU S T W :
   [disjoint S & T :|: W] = [disjoint S & T] && [disjoint S & W].
Proof. by rewrite -!setI_eq0 setIUr setU_eq0. Qed.

Lemma disjointU1X x S T :
   [disjoint x |: S & T] = (x \notin T) && [disjoint S & T].
Proof. by rewrite disjointUX disjoint1X. Qed.

Lemma disjointP_sym S T :
  reflect (forall a, a \in S -> a \notin T) [disjoint T & S].
Proof. by rewrite disjoint_sym; apply: disjointP. Qed.

Lemma setUD S T : S :|: (T :\: S) = S :|: T.
Proof. by rewrite setDE setUIr setUCr setIT. Qed.

Lemma setUDV S T : S :|: T :\: S = T :|: S.
Proof. by rewrite setUD setUC. Qed.

Lemma setUDS S T : (S :|: (T :\: S)) = (T :|: (S :\: T)).
Proof. by rewrite !setUD setUC. Qed.

Lemma setUDSV S T : ((S :\: T) :|: T) = ((T :\: S) :|: S).
Proof. by rewrite setUC setUDS setUC. Qed.

Definition set0_simp := (set0D,setD0,set0U,setU0,setI0,set0I,disjointX0,
  disjoint0X,setDv,disjointXD,disjointDX).

Lemma disjointDI S T : [disjoint S :\: T & S :&: T].
Proof.
move: (disjointDX T S).
rewrite -!setI_eq0 [S :&: T]setIC setIA=>/eqP->. by rewrite set0I.
Qed.
Lemma disjointID S T : [disjoint S :&: T & S :\: T].
Proof. by rewrite disjoint_sym disjointDI. Qed.

Lemma setUD_sub S T : S :<=: T -> S :|: T :\: S = T.
Proof. by rewrite setUD; apply/setUidPr. Qed.

Lemma subUsetPP S T W : S :<=: W -> T :<=: W -> S :|: T :<=: W.
Proof. by rewrite subUset=>->->. Qed.

Section BigFOpsType.
Variables (I : Type).
Implicit Types  (r : seq I) (P : pred I) (F :  I -> {set L}).

Lemma bigcups_seqT (U : {set L}) r P F :
  (forall i : I, P i -> F i :<=: U) ->
          (\bigcup_(i <- r | P i) F i :<=: U).
Proof. 
move=>Pi; elim: r=>[|x r IH]; first by rewrite big_nil sub0set.
by rewrite big_cons; case E: (P x)=>//; rewrite subUset IH Pi.
Qed.

Lemma bigcup_disjoint_seqT  (U: {set L}) r P F :
  (forall i, P i -> [disjoint U & F i]) ->
    ([disjoint U & \bigcup_(i <- r | P i) F i ]).
Proof.
move=>Pi; elim: r=>[|x r IH]; first by rewrite big_nil disjointX0.
by rewrite big_cons; case E: (P x)=>//; rewrite disjointXU IH Pi.
Qed.

Lemma setC_bigcupT r P F :
  ~: (\bigcup_(j <- r | P j) F j) = \bigcap_(j <- r | P j) ~: F j.
Proof. by apply: big_morph => [A B|]; rewrite ?setC0 ?setCU. Qed.

End BigFOpsType.

Section BigFOpsSeq.

Variables (I : eqType) (r : seq I).
Implicit Types (P : pred I) (F :  I -> {set L}).

Lemma bigcup_undup P F :
   \bigcup_(i <- undup r | P i) F i = \bigcup_(i <- r | P i) F i.
Proof. by rewrite big_undup => //= A; rewrite setUid. Qed.

Lemma bigcup_sup_seq j P F : j \in r -> P j -> F j :<=: \bigcup_(i <- r | P i) F i.
Proof.
move=> jr Pj; rewrite -bigcup_undup big_mkcond.
by rewrite (bigD1_seq j) ?mem_undup ?undup_uniq ?Pj //= subsetUl.
Qed.

Lemma bigcup_seqP x F P :
  reflect (exists2 i : I, (i \in r) && P i & x \in F i)
          (x \in \bigcup_(i <- r | P i) F i).
Proof.
apply: (iffP idP) => [|[i /andP[ri Pi]]]; last first.
  by apply: subsetP x; rewrite bigcup_sup_seq.
rewrite big_seq_cond; elim/big_rec: _ => [|i _ /andP[ri Pi] _ /setUP[|//]].
  by rewrite in_set0.
by exists i; rewrite ?ri.
Qed.

Lemma bigcups_seqP (U : {set L}) P F :
  reflect (forall i : I, i \in r -> P i -> F i :<=: U)
          (\bigcup_(i <- r | P i) F i :<=: U).
Proof.
apply: (iffP idP) => [sFU i ri Pi| sFU].
  by apply: subset_trans sFU; apply: bigcup_sup_seq.
by apply/subsetP=> x /bigcup_seqP[i /andP[ri Pi]]; apply/subsetP/sFU.
Qed.

End BigFOpsSeq.

(* wait for update *)
Lemma bigcup_disjoint_seqP  (S: {set L}) (I : eqType) (r: seq I) (P: pred I) (F: I -> {set L}) :
  reflect (forall i, (i \in r) && P i -> [disjoint S & F i])
    ([disjoint S & \bigcup_(i <- r | P i) F i ]).
Proof.
  rewrite -setI_eq0 -subset0 big_distrr/=.
  apply (iffP (bigcups_seqP _ _ _ _)) =>[IH i /andP[P1 P2] | IH i P1 P2].
  move: (IH i P1 P2). all: rewrite subset0 setI_eq0//.
  apply IH. by rewrite P1 P2.
Qed.

End SetExtra.

Section SetIndex.
Context {L : finType} (H : L -> chsType).

Local Notation idx := (@idx _ H).
Implicit Type (S T: {set L}).

Lemma cardset0 : (#| [finType of {i| i \in (set0 : {set L})}] | = 0)%N.
Proof. rewrite card_sig; apply/eq_card0=>x; by rewrite inE. Qed.

Definition idx0 : idx set0 := \mvector_( i : {i| i \in set0} ) (ffun0 cardset0) i.

Lemma idx0E : all_equal_to idx0.
Proof. by move=>x; apply/mvectorP=>i; destruct i; move: (in_set0 x0); rewrite i. Qed.

Lemma dim_set0 : (Vector.dim ('H[H]_set0) = 1)%N.
Proof. by rewrite dim_setten big_set0. Qed.

Lemma eq_nset0 : forall x y: 'I_(Vector.dim ('H[H]_set0)), x = y.
Proof. by rewrite dim_set0 => x y; rewrite !ord1. Qed.

Lemma subInR S T (i : {i|i \in (S :|: T)}) (NinL : (val i \in S) <> true) : val i \in T.
Proof. move/negP: NinL; destruct i => /=; by move/setUP: i => [-> |->]. Qed.

Lemma subInL S T (i : {i|i \in (S :|: T)}) (NinR : (val i \in T) <> true) : val i \in S. 
Proof. by move/negP: NinR; destruct i => /=; move/setUP: i => [-> |->]. Qed.

Definition idxU S T (eA : idx S) (eB : idx T) : 
  idx (S :|: T) := \mvector_ (i : {i|i \in (S :|: T)}) ( 
  match val i \in S =P true with
  | ReflectT E => eA (setsub E)
  | ReflectF E => eB (setsub (subInR E))
  end).
  
Lemma idxUEl S T (eA : idx S) (eB : idx T) (dis: [disjoint S & T]) 
  (i : {i|i \in S})  : (idxU eA eB) (incl (subsetUl S T) i) = eA i.
Proof. by rewrite mvE; case: eqP=>p; destruct i=>//=;rewrite (eq_irrelevance i p). Qed.

Lemma idxUEr S T (eA : idx S) (eB : idx T) (dis: [disjoint S & T]) 
  (i : {i|i \in T})  : (idxU eA eB) (incl (subsetUr S T) i) = eB i.
Proof.
rewrite mvE; case: eqP; destruct i => /= p.
by move/disjointP: dis => disp; move: (disp _ p); rewrite i.
rewrite /setsub; suff E: val (incl (subsetUr S T) (setsub i)) \in T.
by rewrite (eq_irrelevance (subInR _) E) (eq_irrelevance i E).
by move/negP: p => /=; apply contraTT; rewrite i.
Qed.

Definition idxSl S T (eAB : idx (S :|: T)) : idx S :=
  \mvector_ (i : {i|i \in S}) eAB (incl (subsetUl S T) i).

Definition idxSr S T (eAB : idx (S :|: T)) : idx T :=
  \mvector_ (i : {i|i \in T}) eAB (incl (subsetUr S T) i).

Lemma idxSE S T (eAB : idx (S :|: T)) (i : {i|i \in (S :|: T)}) 
  (dis: [disjoint S & T]) :
  eAB i = match val i \in S =P true with
  | ReflectT E => idxSl eAB (setsub E)
  | ReflectF E => idxSr eAB (setsub (subInR E))
  end.
Proof.
case: eqP => p; rewrite mvE /incl/=;
by destruct i; rewrite (eq_irrelevance (subsetP _ _ _) i).
Qed.

Lemma idxUS S T (dis: [disjoint S & T]) :
  forall (eAB : idx (S :|: T)), idxU (idxSl eAB) (idxSr eAB) = eAB.
Proof. by move=> eAB; apply/mvectorP => i; rewrite mvE idxSE. Qed.

Lemma idxSUl S T (dis: [disjoint S & T]) :
  forall (eA : idx S) (eB : idx T), idxSl (idxU eA eB) = eA.
Proof. by move=> eA eB; apply/mvectorP => i; rewrite mvE idxUEl. Qed.

Lemma idxSUr S T (dis: [disjoint S & T]) :
  forall (eA : idx S) (eB : idx T), idxSr (idxU eA eB) = eB.
Proof. by move=> eA eB; apply/mvectorP => i; rewrite mvE idxUEr. Qed.

Lemma idxBE S T (i j: idx (S :|: T)) :
  (idxSl i == (idxSl j)) && ((idxSr i) == (idxSr j)) = (i == j).
Proof.
case E: (i == j); first by move/eqP: E => ->; rewrite !eqxx.
apply/negP. move/negP: E. apply contra_not.
move/andP=> [/eqP/mvectorP eqSl /eqP/mvectorP eqSr].
apply/eqP; apply/mvectorP=> x; case E: ((val x \in S) == true);
[move: (eqSl (setsub (elimTF eqP E))) | move: (eqSr (setsub (subInR (elimTF eqP E))))];
rewrite /idxSl !mvE /incl /=; destruct x => //=;
by rewrite !(eq_irrelevance (subsetP _ _ _) i0).
Qed.

Lemma idxSsum S T (R: ringType) (V : lmodType R) (F: idx (S :|: T) -> V) :
  [disjoint S & T] -> \sum_i F i = \sum_(i : idx S) \sum_(j : idx T) F (idxU i j).
Proof.
rewrite sig_big_dep /=. symmetry.
rewrite [RHS](eq_bigr (fun x=> F (idxU (idxSl x) (idxSr x)))).
move=>i _. apply f_equal. by rewrite (idxUS H0).
apply: (reindex (fun x => Tagged (fun=> idx T) (idxSr x))).
exists (fun x => idxU (projT1 x) (projT2 x)) => -[].
by move=> d _; rewrite -[RHS]idxUS.
move=>/=l r P1; rewrite /Tagged; congr (existT _ _ _); last by rewrite idxSUr.
apply/mvectorP=> i; by rewrite mvE idxUEl.
Qed.

(* Variable (n : nat) (dt : n.+1.-tuple {set L}) (ft : {dffun forall i, idx (dt ~_ i)}).
Check idxU (packidx ([ffun i : 'I_n => ft (fintype.lift ord0 i) ])) (ft ord0). *)
Lemma idx_big_recl_cast (n : nat) (dt : n.+1.-tuple {set L}) :
  dt ~_ ord0 :|: \bigcup_i dt ~_ (fintype.lift ord0 i) = \bigcup_i dt ~_ i.
Proof. by rewrite big_ord_recl. Qed.

Lemma castidx_app
  (I     : finType)
  (E     : I -> chsType)
  (S1 S2 : {set I})
  (eq_S  : S1 = S2)
  (A1    : 'Idx[E]_S1)
  (x     : { i : I | i \in S2 })
:

  castidx eq_S A1 x =
    A1
      (@exist I (fun i : I => i \in S1)
      (tag x)
      (ecast z (tag x \in z) (esym eq_S) (tagged x))).
Proof.
case: x => x xS2; case: A1=> /= d; rewrite /fun_of_mvector /=.
rewrite /castidx; case: _ / eq_S x xS2 d => x xS2 d /=.
by set xS2':= ssrfun.svalP _; suff ->//: xS2'= xS2.
Qed.

(* split is always better then pack, since split is inj *)
(* similarly, flatidx is better then packidx *)
Lemma idx_big_recl (n : nat) (dt : n.+1.-tuple {set L}) (e : idx (\bigcup_i dt ~_ i)) j :
  flatidx (idxSr (castidx (esym (idx_big_recl_cast dt)) e)) j
  = flatidx e (fintype.lift ord0 j).
Proof.
rewrite /flatidx /= !ffunE; apply/mvectorP => /= i; rewrite !mvE.
rewrite castidx_app /=; apply/val_inj => /=; congr (e _) => /=.
by apply/val_inj.
Qed.

Lemma idx_big_recl0 (n : nat) (dt : n.+1.-tuple {set L}) (e : idx (\bigcup_i dt ~_ i)) :
  ((flatidx e) ord0) = (idxSl (castidx (esym (idx_big_recl_cast dt)) e)).
Proof.
rewrite !ffunE; apply/mvectorP => /= i; rewrite !mvE.
rewrite castidx_app /=; apply/val_inj => /=.
by congr (e _) => /=; apply/val_inj => /=.
Qed.

End SetIndex.

Reserved Notation "f ⊗v g" (at level 45, left associativity).
Reserved Notation "f ⊗vm g" (at level 45, left associativity).

Section SetTensorProduct.
Context {I : finType} (E : I -> chsType).

Implicit Type (S T: {set I}).
Local Notation idx := (@idx _ E).
Local Notation Hs := (@Hs _ E).
Local Notation Hf := (@Hf _ E).

Lemma disj_inf S T : [disjoint S & T] -> forall x, (x \in S) && (x \in T) = false.
Proof.
by move/disjointP=> dis x; case E1: (x \in S) => //=; apply negbTE; 
apply (dis x E1).
Qed.

Lemma tenv_dim S T (dis: [disjoint S & T]) :
  (Vector.dim (Hs (S :|: T)) = Vector.dim (Hs S) * 
  Vector.dim (Hs T))%N.
Proof.
rewrite !dim_setten (big_setID S)/=; congr (_ * _)%N; apply eq_bigl.
by rewrite setUK. rewrite setDUl setDv set0U.
by move: dis; rewrite disjoint_sym=>/setDidPl ->.
Qed.

(* tenor of state over disjoint set *)
(* note: tenor is defined for all cases, but only correct if domain are disjoint *)
Fact tenv_key : unit. Proof. by []. Qed.
Definition tenv S T : Hs S -> Hs T -> Hs (S :|: T) := 
  locked_with tenv_key (fun (u : Hs S) (v : Hs T) =>
  \sum_(e : idx (S :|: T)) (cdv (idxSl e) u * cdv (idxSr e) v) *: deltav e).
Canonical tenv_unlockable S T := [unlockable fun (@tenv S T)].
Notation "f ⊗v g" := (tenv f g).
Lemma linear_tenv S T u : linear (@tenv S T u).
Proof. 
move=>a v w; rewrite unlock linear_sum -big_split; apply eq_bigr=>i _.
by rewrite linearP/= mulrDr scalerDl scalerA mulrA [_ * a]mulrC mulrA.
Qed.
Canonical tenv_additive S T u := Additive (@linear_tenv S T u).
Canonical tenv_linear S T u := Linear (@linear_tenv S T u).
Definition tenvr S T u := (@tenv S T)^~ u.
Lemma linear_tenvr S T u : linear (@tenvr S T u).
Proof.
move=>a v w; rewrite /tenvr unlock linear_sum -big_split; apply eq_bigr=>i _.
by rewrite linearP/= mulrDl scalerDl scalerA mulrA.
Qed.
Canonical tenvr_additive S T u := Additive (@linear_tenvr S T u).
Canonical tenvr_linear S T u := Linear (@linear_tenvr S T u).
Canonical tenv_rev S T := [revop (@tenvr S T) of (@tenv S T)].
Canonical tenv_is_bilinear S T := [bilinear of (@tenv S T)].

Lemma tenv0 S T (u: Hs S) : u ⊗v (0: Hs T) = 0.
Proof. exact: linear0r. Qed.
Lemma tenvNl S T (v: Hs T) (u: Hs S) : (-u) ⊗v v = - (u ⊗v v).
Proof. exact: linearNl. Qed.
Lemma tenvBl S T (w: Hs T) (u v: Hs S) : (u-v) ⊗v w = u ⊗v w - v ⊗v w.
Proof. exact: linearBl. Qed.
Lemma tenvDl S T (w: Hs T) (u v: Hs S) : (u+v) ⊗v w = u ⊗v w + v ⊗v w.
Proof. exact: linearDl. Qed.
Lemma tenvZl S T (v: Hs T) (c: C) (u: Hs S) : (c*:u) ⊗v v = c *: (u ⊗v v).
Proof. exact: linearZl. Qed.
Lemma tenvPl S T (w: Hs T) (c: C) (u v: Hs S) : 
  (c*:u+v) ⊗v w = c *: (u ⊗v w) + v ⊗v w.
Proof. exact: linearPl. Qed.
Lemma tenvMnl S T (v: Hs T) (u: Hs S) n : (u *+ n) ⊗v v = (u ⊗v v) *+ n.
Proof. exact: linearMnl. Qed.
Lemma tenvMNnl S T (v: Hs T) (u: Hs S) n : tenv (u *- n) v = (tenv u v) *- n.
Proof. exact: linearMNnl. Qed.
Lemma tenv_suml L r (P : pred L) S T (F: L -> Hs S) (u: Hs T) : 
  (\sum_(i <- r | P i) F i) ⊗v u = \sum_(i <- r | P i) ((F i) ⊗v u).
Proof. exact: linear_suml. Qed.
Lemma ten0v S T (u: Hs T) : (0: Hs S) ⊗v u = 0.
Proof. exact: linear0l. Qed.
Lemma tenvNr S T (u: Hs S) (v: Hs T) : u ⊗v (-v) = - (u ⊗v v).
Proof. exact: linearNr. Qed.
Lemma tenvBr S T (w: Hs S) (u v: Hs T) : w ⊗v (u-v) = w ⊗v u - w ⊗v v.
Proof. exact: linearBr. Qed.
Lemma tenvDr S T (w: Hs S) (u v: Hs T) : w ⊗v (u+v) = w ⊗v u + w ⊗v v.
Proof. exact: linearDr. Qed.
Lemma tenvZr S T (v: Hs S) (c: C) (u: Hs T) : v ⊗v (c*:u) = c *: (v ⊗v u).
Proof. exact: linearZr. Qed.
Lemma tenvPr S T (w: Hs S) (c: C) (u v: Hs T) : 
  w ⊗v (c *: u + v) = c *: (w ⊗v u) + (w ⊗v v).
Proof. exact: linearPr. Qed.
Lemma tenvMnr S T (v: Hs S) (u: Hs T) n : v ⊗v (u *+ n) = (v ⊗v u) *+ n.
Proof. exact: linearMnr. Qed.
Lemma tenvMNnr S T (v: Hs S) (u: Hs T) n : v ⊗v (u *- n) = (v ⊗v u) *- n.
Proof. exact: linearMNnr. Qed.
Lemma tenv_sumr L r (P : pred L) S T (u: Hs S) (F: L -> Hs T)  : 
  u ⊗v (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) (u ⊗v (F i)).
Proof. exact: linear_sumr. Qed.

Lemma tenv_dot S T (u1 u2 : Hs S) (v1 v2 : Hs T) : 
  [disjoint S & T] -> [< u1 ⊗v v1 ; u2 ⊗v v2 >] = [< u1 ; u2>] * [< v1 ; v2 >].
Proof.
move=> P.
rewrite /tenv unlock dotp_suml (eq_bigr (fun v=> (cdv (idxSl v) u1 * cdv (idxSr v) v1)^* *
   (cdv (idxSl v) u2 * cdv (idxSr v) v2))).
move=>i _. rewrite  dotp_sumr (bigD1 i) //= big1.
move=>j /negPf nji. by rewrite dotpZl dotpZr tcbase eq_sym nji !mulr0.
by rewrite dotpZl dotpZr tcbase eqxx mulr1 addr0.
rewrite (idxSsum _ P) !dot_cdv mulr_suml; apply eq_bigr=> i _.
rewrite mulr_sumr; apply eq_bigr=> j _.
rewrite (idxSUl P) (idxSUr P) rmorphM /=.
by rewrite -!mulrA ![(cdv j v1)^**_]mulrC !mulrA.
Qed.

Lemma deltavt S T (i: idx (S :|: T)) :
  deltav i = (deltav (idxSl i)) ⊗v (deltav (idxSr i)).
Proof.
rewrite /tenv [in RHS]unlock (bigD1 i) //= big1. move=>j; rewrite -idxBE negb_and.
by move/orP => [/negPf P1 | /negPf P1]; rewrite !cdvdelta P1 ?mulr0 ?mul0r scale0r.
by rewrite !cdvdelta !eqxx mulr1 scale1r addr0.
Qed.

Lemma deltavtV S T (i : idx S) (j : idx T) :
  [disjoint S & T] -> (deltav i) ⊗v (deltav j) = deltav (idxU i j).
Proof.
move=>dis; rewrite /tenv unlock (idxSsum _ dis) (bigD1 i)//= 
  (bigD1 j)//= !big1=>[m/negPf nm|m/negPf nm|].
2: rewrite big1//==>n _.
1,2,3: rewrite !idxSUl//= !idxSUr//= !cdvdelta ?nm ?mulr0 ?mul0r ?scale0r//.
by rewrite !eqxx mul1r scale1r !addr0.
Qed.

Lemma cdvt S T u v (i : idx (S :|: T)) : 
  cdv i (u ⊗v v) = cdv (idxSl i) u * cdv (idxSr i) v.
Proof.
rewrite /tenv unlock linear_sum/= (bigD1 i)// big1//=.
by move=>j /negPf nji; rewrite linearZ/= cdvdelta eq_sym nji mulr0.
by rewrite addr0 linearZ/= cdvdelta eqxx mulr1.
Qed.

Lemma tenv_conj S T (u: Hs S) (v: Hs T) : ((u^*v) ⊗v (v^*v) = (u ⊗v v)^*v)%VF.
Proof.
rewrite (deccdv u) raddf_sum/= !linear_suml raddf_sum/=; apply eq_bigr=>i _. 
rewrite (deccdv v) raddf_sum/= linear_sum linear_sumr raddf_sum/=; apply eq_bigr=>j _. 
rewrite !conjvZ !linearZl !linearZr/= !conjvZ; congr (_ *: (_ *: _)).
by rewrite !conjvdv; apply/cdvP=>k; rewrite conjvcdv !cdvt rmorphM -!conjvcdv !conjvdv.
Qed.

Lemma tenv_idx0r S (u : 'H[E]_S) : u ⊗v (deltav (idx0 E)) = casths (esym (setU0 _)) u.
Proof.
apply/cdvP=>i; rewrite cdvt cdvdelta idx0E eqxx mulr1 cdv_castV esymK; f_equal.
apply/mvectorP=>j; rewrite /idxSl mvE. move: i.
move: (esym (setU0 S)) (setU0 S) (subsetUl S set0)=>P.
case: (S :|: set0) / P=>P1 P2 i; rewrite castidx_id/=; case: j=>x Px/=.
by rewrite /incl/= (eq_irrelevance (subsetP P2 x _) Px).
Qed.

Lemma tenvm_dim (J: finType) (fs : J -> {set I}) : disf fs ->
  (Vector.dim (Hs (\bigcup_i fs i)) = \prod_i Vector.dim (Hs (fs i)))%N.
Proof. 
move=> dis; rewrite dim_setten partition_disjoint_bigcup//.
by apply eq_bigr=>i _; rewrite dim_setten.
Qed.

(* tenor of state over disjoint set *)
Definition tenvm (J: finType) (fs : J -> {set I}) 
  (u : forall i : J, Hs (fs i)) := injectv (\mvector_(i : J) u i).

Lemma tenvmdv (J: finType) (fs : J -> {set I}) (i : idx (\bigcup_i (fs i))) :
  deltav i = tenvm (fun k=>deltav (flatidx i k)).
Proof. exact: deltavm. Qed.

Lemma tenvm_dot (J: finType) (fs : J -> {set I})
  (u v: forall i : J, Hs (fs i)) : disf fs ->
  [< tenvm u ; tenvm v >] = \prod_i [< u i ; v i >].
Proof.
move=> dis; rewrite /tenvm -injectv_dot// /hdotp.
by under eq_bigr do rewrite !mvE.
Qed.

Lemma cdvtm (J: finType) (fs : J -> {set I})
  (x: forall i : J, Hs (fs i)) e : 
  cdv e (tenvm x) = \prod_i cdv (flatidx e i) (x i).
Proof.
rewrite /tenvm /injectv linear_sum/= (bigD1 e)//= linearZ/= cdvdelta eqxx mulr1.
rewrite [X in _ + X]big1 ?addr0 =>[i/negPf ni|].
by rewrite linearZ/= cdvdelta eq_sym ni mulr0.
by under eq_bigr do rewrite mvE.
Qed.

Lemma tenvmP (J: finType) (fs : J -> {set I}) (x y : forall i : J, Hs (fs i)) :
  (forall i, x i = y i) -> tenvm x = tenvm y.
Proof. by move=>P; apply/cdvP=>i; rewrite !cdvtm; under eq_bigr do rewrite P. Qed.

Lemma tenvm_conj (J: finType) (fs : J -> {set I}) (x: forall i : J, Hs (fs i)) :
  ((tenvm x)^*v = tenvm (fun i=> (x i)^*v))%VF.
Proof.
apply/cdvP=>i; rewrite conjvcdv !cdvtm rmorph_prod; 
by apply eq_bigr=>j _; rewrite conjvcdv.
Qed.

Lemma tenvm_recl (n : nat) (dt : n.+1.-tuple {set I}) 
  (u : forall x : 'I_n.+1, Hs (dt ~_ x)) :
  casths (esym (idx_big_recl_cast dt)) (tenvm u) = 
    (u ord0 ⊗v tenvm (fun i=> (u (fintype.lift ord0 i)))).
Proof.
apply/cdvP=>i; rewrite cdvt cdv_castV esymK !cdvtm big_ord_recl; f_equal.
by rewrite idx_big_recl0 castidx_comp castidx_id.
by apply eq_bigr=>/= j _; f_equal; rewrite -idx_big_recl castidx_comp castidx_id.
Qed.

End SetTensorProduct.
Notation "f ⊗v g" := (tenv f g) : lfun_scope.
Notation "f ⊗vm g" := (tenvm f g) : lfun_scope.

Section OuterProductDef.
Variable (H G : chsType).

Fact outp_key : unit. by []. Qed.

Definition outp (v1 : H) (v2 : G) : 'Hom(G,H) :=
    Vector.Hom ((v2r v2)^*t *m v2r v1).

Local Notation "[> u ; v <]" := (outp u v) (at level 2, format "[>  u ;  v  <]").


Lemma outpE (u : H) (v w : G) : [> u ; v <] w = [<v ; w >] *: u.
Proof.
apply/v2r_inj/matrixP=>i j. rewrite unlock/= r2vK mulmxA linearZ/= dotp_mulmx !mxE.
by rewrite big_ord1 mxE ord1; f_equal; apply eq_bigr=>k _; rewrite !mxE mulrC.
Qed.

Lemma linear_outp u : linear_for (conjC \; *:%R) (outp u).
Proof.
move=>a v w; apply/lfunP=>t.
by rewrite lfunE/= lfunE/= !outpE linearPl/= scalerDl scalerA.
Qed.
Canonical outp_additive u := Additive (linear_outp u).
Canonical outp_linear u := (Linear (linear_outp u)).

Definition outpr u := (outp)^~ u.
Lemma linear_outpr u : linear (outpr u).
Proof.
move=>a v w; apply/lfunP=>t.
by rewrite /outpr lfunE/= lfunE/= !outpE linearP/=.
Qed.
Canonical outpr_additive u := Additive (linear_outpr u).
Canonical outpr_linear u := Linear (linear_outpr u).
Canonical outp_rev := [revop outpr of outp].
Canonical outp_is_bilinear := [bilinear of outp].

Lemma out0p u : [> 0; u <] = 0.
Proof. exact: linear0l. Qed.

Lemma outpNl w : {morph (outp^~ w) : u / -u}.
Proof. exact: linearNl. Qed.

Lemma outpBl w : {morph (outp^~ w) : u v / u - v}.
Proof. exact: linearBl. Qed.

Lemma outpDl w : {morph (outp^~ w) : u v / u + v}.
Proof. exact: linearDl. Qed.

Lemma outpZl (x : C) u v : [> x *: u; v <] = x *: [> u; v <].
Proof. exact: linearZl. Qed.

Lemma outpPl (x : C) u v w : [> x *: u + v ; w <] = x *: [> u; w <] + [> v; w <].
Proof. exact: linearPl. Qed.

Lemma outpMnl w n : {morph (outp^~ w) : u / u *+ n}.
Proof. exact: linearMnl. Qed.

Lemma outpMNnl w n : {morph (outp^~ w) : u / u *- n}.
Proof. exact: linearMNnl. Qed.

Lemma outp_suml (I : Type) (r : seq I) P (F : I -> H) u :
  [> \sum_(v <- r | P v) F v; u <] = \sum_(v <- r | P v) [> F v; u <].
Proof. exact: linear_suml. Qed.

Lemma outp0 u : [> u; 0 <] = 0.
Proof. exact: linear0. Qed.

Lemma outpNr w : {morph outp w : u / -u}.
Proof. exact: linearN. Qed.

Lemma outpBr w : {morph outp w : u v / u - v}.
Proof. exact: linearB. Qed.

Lemma outpDr w : {morph outp w : u v / u + v}.
Proof. exact: linearD. Qed.

Lemma outpZr (x : C) u v : [> u; x *: v <] = x^* *: [> u; v <].
Proof. exact: linearZ. Qed.

Lemma outpPr (x : C) u v w : [> u; x *: v + w <] = x^* *: [> u; v <] + [> u; w <].
Proof. exact: linearP. Qed.

Lemma outpMnr w n : {morph outp w : u / u *+ n}.
Proof. exact: linearMn. Qed.

Lemma outpMNnr w n : {morph outp w : u / u *- n}.
Proof. exact: linearMNn. Qed.

Lemma outp_sumr (I : Type) (r : seq I) P (F : I -> G) u :
  [> u; \sum_(v <- r | P v) F v <] = \sum_(v <- r | P v) [> u; F v <].
Proof. exact: linear_sum. Qed.

End OuterProductDef.

Notation "[> u ; v <]" := (outp u v) (at level 2, format "[>  u ;  v  <]").

Section OuterProductTheory.
Local Open Scope lfun_scope.
Implicit Type (H G W: chsType).

Lemma adj_outp H G (u : H) (v : G) : [> u; v <]^A = [> v; u <].
Proof.
apply/lfunP=>t; apply/intro_dotl=>w.
by rewrite adj_dotEV !outpE linearZ/= linearZl/= conj_dotp mulrC.
Qed.

Lemma conj_outp H G (u : H) (v : G) : [> u; v <]^C = [> u^*v; v^*v <].
Proof. by apply/lfunP=>t; rewrite conjfE !outpE conjvZ conj_dotp conjv_dotl. Qed.

Lemma tr_outp H G (u : H) (v : G) : [> u; v <]^T = [> v^*v ; u^*v <].
Proof. by rewrite trfAC adj_outp conj_outp. Qed.

Lemma outp_compl H G W (u : H) (v : G) (f : 'Hom(W,G)) : 
  [> u ; v <] \o f = [> u ; f^A v <].
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE adj_dotE. Qed.

Lemma outp_compr H G W (u : H) (v : G) (f : 'Hom(H,W)) : 
  f \o [> u ; v <] = [> f u ; v <].
Proof. by apply/lfunP=>w; rewrite lfunE/= !outpE linearZ. Qed.

Lemma outp_comp H G W (u : H) (v w : G) (t : W) : 
  [> u ; v <] \o [> w ; t <] = [< v ; w >] *: [> u ; t <].
Proof. by rewrite outp_compr outpE linearZl. Qed.

Lemma outpD H (u v : H) : [> u + v; u + v <] =
  [> u; u <] + [> v; v <] + ([> u; v <] + [> u; v <]^A).
Proof.
rewrite !(outpDr, outpDl) adj_outp -!addrA; congr (_ + _).
by rewrite [RHS]addrC addrCA !addrA.
Qed.

End OuterProductTheory.


Section LinfunDef.
Context (L : finType) (H : L -> chsType).

Implicit Type (S T: {set L}).
Local Notation idx := (@idx _ H).
Local Notation Hs := (@Hs _ H).
Local Notation Hf := (@Hf _ H).
Local Notation i0 := (@idx0 _ H).

Local Open Scope lfun_scope.

Lemma castlf_outp S S' T T' (eqST : (S = S') * (T = T')) (v : 'H[H]_S) (u : 'H[H]_T) :
  castlf eqST [> u ; v <] = [>casths eqST.2 u ; casths eqST.1 v <].
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castlf_id !casths_id. Qed.

Lemma outp_idx0 : [> deltav (idx0 H); deltav (idx0 H) <] = \1.
Proof. by apply/lfunPD=>i; rewrite !idx0E outpE -cdvE cdvdelta eqxx scale1r lfunE. Qed.

(*matrix form of lfun if needed *)

Definition sv2s (v : Hs set0) : C := cdv i0 v.
Definition s2sv (a : C) : Hs set0 := a *: deltav i0.

Lemma decsv (v: 'H[H]_set0) : v = cdv i0 v *: deltav i0.
Proof.
rewrite (decdv v) (bigD1 i0) //= big1.
by move=>i; rewrite !idx0E eqxx.
by rewrite /cdv addr0 dotpZr tcbase eqxx mulr1.
Qed.

Lemma sv_dotpE (v: 'H[H]_set0) :  `|v| = `|cdv i0 v|.
Proof. by rewrite {1}(decsv v) normrZ normdv1 mulr1. Qed.

Lemma sv2s_is_scalar : (scalar sv2s).
Proof. by move=> a u v; rewrite /sv2s linearP. Qed.
Canonical sv2s_linear := Linear sv2s_is_scalar.
Lemma s2sv_is_additive : additive s2sv.
Proof. move=>u v. by rewrite /s2sv scalerDl scaleNr. Qed.
Canonical s2sv_additive := Additive s2sv_is_additive.

Lemma sv2sK : cancel sv2s s2sv.
Proof. by move=>u; rewrite /sv2s /s2sv -decsv. Qed.

Lemma s2svK : cancel s2sv sv2s.
Proof. by move=>u; rewrite /sv2s /s2sv /cdv dotpZr tcbase eqxx mulr1. Qed.

Lemma sv2s_inj : injective sv2s.
Proof. exact (can_inj sv2sK). Qed.

Lemma s2sv_inj : injective s2sv.
Proof. exact (can_inj s2svK). Qed.

Lemma sv2s_conj (u : 'H[H]_set0) : (sv2s u)^* = sv2s (u ^*v).
Proof. 
rewrite (decsv u) /sv2s conjvZ {1 3}/cdv.
by rewrite !dotpZr rmorphM /= conjvdv tcbase eqxx conjC1.
Qed.

Lemma s2sv_conj (c : C) : (s2sv c)^*v = s2sv (c^*).
Proof. by apply sv2s_inj; rewrite -sv2s_conj !s2svK. Qed.

(* inner product of scalar vector *)
Lemma sv_dotp (u v : 'H[H]_(set0)) : [< u ; v >] = (sv2s u)^* * (sv2s v).
Proof. 
by rewrite {1}(decsv u) {1}(decsv v) dotpZl dotpZr tcbase eqxx mulr1 /sv2s.
Qed.

(* translform between vector 'H[H]_S and linfun 'FV[H]_S *)
Definition v2f_fun S (v : 'H[H]_S) : 'H[H]_set0 -> 'H[H]_S :=
  (fun u: 'H[H]_(set0) => (sv2s u) *: v).
Lemma v2f_fun_is_linear (S : {set L}) (v : 'H[H]_S) : linear (v2f_fun v).
Proof. by move=>a x y; rewrite /v2f_fun linearP /= scalerA scalerDl. Qed.
Canonical v2f_fun_linear S (v : 'H[H]_S) := Linear (v2f_fun_is_linear v).
Definition v2f S (v : 'H[H]_S) := linfun (v2f_fun v).

Lemma v2fE S (v : 'H[H]_S) (u : 'H[H]_set0) : (v2f v u) = sv2s u *: v.
Proof. by rewrite /v2f lfunE/= /v2f_fun. Qed.

Definition v2df S (v : 'H[H]_S) := (v2f v)^A.

Lemma v2dfE S (v u : 'H[H]_S) : v2df v u = s2sv ([<v ; u>]).
Proof.
rewrite /v2df. apply/intro_dotl=>t. 
by rewrite adj_dotEV v2fE linearZl/= linearZ/= sv_dotp /sv2s cdvdelta eqxx mulr1 mulrC.
Qed.

Lemma v2f_is_linear S : linear (@v2f S).
Proof. 
move=>a u v; apply/lfunP=>x; do ? rewrite !lfunE/=. 
by rewrite /v2f_fun scalerA scalerDr scalerA [_*a]mulrC.
Qed.
Canonical v2f_linear S := Linear (@v2f_is_linear S).
Lemma v2df_is_antilinear S : linear_for (conjC \; *:%R) (@v2df S).
Proof. by move=>a u v; rewrite /v2df linearP/= linearP. Qed.
Canonical v2df_antilinear S := Linear (@v2df_is_antilinear S).

(* translform betwwen scalar and scalar linfun 'F[H]_set0 *)
(* Definition s2sf (a : C) : 'F[H]_set0 := v2f (s2sv a). *)
Definition s2sf (a: C) : 'F[H]_set0 := (a *: \1).
Lemma s2sf_is_additive : additive s2sf.
Proof. by move=>a b; rewrite /s2sf scalerBl. Qed.
Canonical s2sf_additive := Additive s2sf_is_additive.

Lemma comp_dot S (u v : 'H[H]_S) : ((v2df u) \o (v2f v))%VF = s2sf ([<u;v>]).
Proof.
apply/lfunP=> x; rewrite comp_lfunE /v2f /v2df -intro_dvl=> i.
rewrite !idx0E /cdv adj_dotEV !lfunE /= /v2f_fun {1}/sv2s /s2sv /cdv.
rewrite lfunE/= !dotpZl !dotpZr !tcbase eqxx conjC1 /sv2s /cdv.
by rewrite mul1r mulrC.
Qed.

Lemma comp_norm S (v : 'H[H]_S) : ((v2df v) \o (v2f v))%VF = s2sf (`|v| ^+ 2).
Proof. by rewrite comp_dot dotp_norm. Qed.

Lemma comp_out S (u v : 'H[H]_S) : (v2f u \o (v2df v))%VF = [>u ; v<].
Proof. by apply/lfunP=>w; rewrite lfunE/= v2dfE v2fE s2svK outpE. Qed.

Definition sf2s (f : 'F[H]_set0) : C := sv2s (f (s2sv 1)).

Lemma sf2s_is_scalar : scalar sf2s.
Proof. by move=> a x y; rewrite /sf2s lfunE /= scale_lfunE; rewrite linearP. Qed.
Canonical sf2s_linear := Linear sf2s_is_scalar.

Definition f2v (S : {set L}) (f : 'FV[H]_S) : 'H[H]_S := f (s2sv 1).

Definition df2v (S : {set L}) (f : 'FdV[H]_S) : 'H[H]_S := f^A (s2sv 1).

Lemma f2v_is_linear S : linear (@f2v S).
Proof. by move=>a f g; rewrite /f2v; do ? rewrite lfunE/=. Qed.
Canonical f2v_linear S := Linear (@f2v_is_linear S).
Lemma df2v_is_antilinear S : linear_for (conjC \; *:%R) (@df2v S).
Proof. by move=>a f g; rewrite /df2v linearP/= lfunE/= lfunE/=. Qed.
Canonical df2v_linear S := Linear (@df2v_is_antilinear S).

Lemma v2fK (S : {set L}) : cancel (@v2f S) (@f2v S).
Proof. by move=> v; rewrite /v2f /f2v !lfunE /= /v2f_fun s2svK scale1r. Qed.

Lemma f2vK (S : {set L}) : cancel (@f2v S) (@v2f S).
Proof.
move=> f; apply/lfunP=> u; rewrite /v2f /f2v !lfunE /= /v2f_fun -linearZ /=.
by apply f_equal; rewrite {2}(decsv u) /sv2s /s2sv scale1r.
Qed.

Lemma v2f_inj (S : {set L}) : injective (@v2f S).
Proof. exact (can_inj (@v2fK S)). Qed.

Lemma f2v_inj (S: {set L}) : injective (@f2v S).
Proof. exact (can_inj (@f2vK S)). Qed.

Lemma v2f_comp (S T: {set L}) (f : 'F[H]_(S, T)) (v : 'H[H]_S) :
  f v = f2v (f \o (v2f v)).
Proof.
apply v2f_inj; rewrite f2vK; apply/lfunP=>u.
by rewrite comp_lfunE /v2f !lfunE /= /v2f_fun linearZ.
Qed.

Lemma v2dfK S : cancel (@v2df S) (@df2v S).
Proof.
by move=>v; rewrite /v2df /df2v adjfK /v2f lfunE /= /v2f_fun s2svK scale1r.
Qed.

Lemma v2df_inj S : injective (@v2df S).
Proof. exact (can_inj (@v2dfK S)). Qed.

Lemma df2v_inj S : injective (@df2v S).
Proof.
move=> f g; rewrite /df2v /s2sv !scale1r => P; apply/lfunP=>u.
by apply intro_dotr => t; rewrite (decsv t) !linearZ /= -!adj_dotEV P.
Qed.

Lemma df2vK (S: {set L}) : cancel (@df2v S) (@v2df S).
Proof. by move=> f; apply df2v_inj; rewrite v2dfK. Qed.

Lemma v2df_comp (S T: {set L}) (f : 'F[H]_(S, T)) (v : 'H[H]_T) :
  f^A v = df2v (v2df v \o f).
Proof.
by rewrite /df2v adjf_comp comp_lfunE /v2df adjfK 
  /v2f lfunE /= /v2f_fun s2svK scale1r.
Qed.

Lemma s2sfK : cancel s2sf sf2s.
Proof.
by move=>a; rewrite /s2sf /sf2s lfunE/= lfunE/= linearZ/= s2svK mulr1.
Qed.

Lemma sf2sK : cancel sf2s s2sf.
Proof.
move=>f. rewrite /sf2s /s2sf. apply/lfunP=>u.
rewrite lfunE/= lfunE/=. apply/cdvP=>i.
rewrite (decsv u) /sv2s /s2sv scale1r !idx0E.
by rewrite !linearZ/= cdvdelta eqxx mulr1 mulrC.
Qed.

Lemma s2sf_inj : injective s2sf.
Proof. exact (can_inj s2sfK). Qed.

Lemma sf2s_inj : injective sf2s.
Proof. exact (can_inj sf2sK). Qed.

(* properties between conj_lfun and ^*v and ^* *)
Lemma v2f_conj S (u : 'H[H]_S) : (v2f u)^C = v2f (u ^*v).
Proof.
by apply/lfunP=>v; rewrite conjfE /v2f !lfunE /= /v2f_fun conjvZ -sv2s_conj conjCK.
Qed.

Lemma f2v_conj S (f : 'FV[H]_S) : (f2v f)^*v = f2v (f^C ).
Proof. by apply v2f_inj; rewrite -v2f_conj !f2vK. Qed.

(* v2df_conj *)
Lemma v2df_conj S (u: 'H[H]_S) : (v2df u)^C = v2df u^*v.
Proof. by rewrite /v2df -v2f_conj lfACC. Qed.

Lemma df2v_conj S (f: 'FdV[H]_S) : (df2v f)^*v = df2v f^C.
Proof. by apply v2df_inj; rewrite -v2df_conj !df2vK. Qed.

Lemma s2sf_conj (c : C) : (s2sf c)^C = s2sf (c^*).
Proof.
rewrite /s2sf conjfZ; congr (_ *: _).
by apply/lfunP=>u; rewrite conjfE !lfunE/= conjvK.
Qed.

Lemma sf2s_conj (f: 'F[H]_set0) : (sf2s f)^* = sf2s (f^C ).
Proof. by apply s2sf_inj; rewrite -s2sf_conj !sf2sK. Qed.

(* properties between adjlf and v2f v2df f2v df2v *)

Lemma v2df_adj S (v : 'H[H]_S) : (v2df v)^A = v2f v.
Proof. by rewrite /v2df adjfK. Qed.

Lemma v2f_adj S (v: 'H[H]_S) : (v2f v)^A = v2df v.
Proof. by rewrite /v2df. Qed.

Lemma f2v_adj S (f: 'FdV[H]_S) : f2v (f^A) = df2v f.
Proof. by rewrite /df2v. Qed.

Lemma df2v_adj S (f: 'FV[H]_S) : df2v (f^A) = f2v f.
Proof. by rewrite /df2v adjfK. Qed.

Lemma sfAC (f : 'F[H]_set0) : f^A = f^C.
Proof. 
rewrite adjfCT; apply f2mx_inj; rewrite /tr_lfun /=.
by apply/matrixP=>i j; rewrite mxE (eq_nset0 j i).
Qed.

Lemma sfT (f : 'F[H]_set0) : f^T = f.
Proof. by rewrite trfAC sfAC conjfK. Qed.

Lemma sf2s_adj (f: 'F[H]_set0) : sf2s (f^A) = (sf2s f)^*.
Proof. by rewrite sfAC sf2s_conj. Qed.

Lemma s2sf_adj (c : C) : (s2sf c)^A = s2sf c^*.
Proof. by rewrite sfAC s2sf_conj. Qed.

Lemma v2f_tr S (u: 'H[H]_S) : (v2f u)^T = v2df u^*v.
Proof. by rewrite trfAC v2f_adj v2df_conj. Qed.

Lemma df2v_tr S (f: 'FV[H]_S) : df2v (f^T) = (f2v f)^*v.
Proof. by rewrite trfAC -df2v_conj df2v_adj. Qed.

Lemma v2df_tr S (u: 'H[H]_S) : (v2df u)^T = v2f u^*v.
Proof. by rewrite trfAC v2df_adj v2f_conj. Qed.

Lemma f2v_tr S (f: 'FdV[H]_S) : f2v f^T = df2v f^C.
Proof. by rewrite trfCA f2v_adj. Qed.

Lemma sf2s_tr (f: 'F[H]_set0) : sf2s (f^T) = (sf2s f).
Proof. by rewrite sfT. Qed.

Lemma s2sf_tr (c : C) : (s2sf c)^T = s2sf c.
Proof. by rewrite sfT. Qed. 

(* tenor product of linear function, onbasis free *)
(* note that tenor is defined for all cases, but only correct if domains/codomains 
   are disjoint *)
Definition ten_lfun_fun S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :=
  (fun u : 'H[H]_(S :|: S') => \sum_(i : idx (S :|: S')) cdv i u *:
    ((f (deltav (idxSl i))) ⊗v (g (deltav (idxSr i))))).
Lemma ten_lfun_fun_is_linear S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  linear (ten_lfun_fun f g).
Proof.
move=>a u v; rewrite /ten_lfun_fun scaler_sumr -big_split /=.
by apply eq_bigr=>i _; rewrite scalerA -scalerDl linearP.
Qed.
Canonical ten_lfun_linear S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :=
  Linear (ten_lfun_fun_is_linear f g).
Definition ten_lfun S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) := 
  linfun (ten_lfun_fun f g).

Definition dot_lfun S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :=
  ((ten_lfun f (\1: 'F[H]_(T' :\: S, T' :\: S))) \o castlf (erefl _, (setUDS T' S))
  (ten_lfun g (\1: 'F[H]_(S :\: T', S :\: T'))))%VF.

Definition sdot_lfun S T (f : 'F[H]_S) (g : 'F[H]_T) :=
    castlf (setUDV _ _, (setUD _ _)) (dot_lfun f g).

Notation "f \⊗ g" := (ten_lfun f g) (at level 45, left associativity).
Notation "f \⋅ g" := (dot_lfun f g) (at level 40, left associativity).
Notation "f \O g" := (sdot_lfun f g) (at level 40, left associativity).

Lemma tenfdv S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) i: 
  (f (deltav (idxSl i))) ⊗v (g (deltav (idxSr i))) = (ten_lfun f g) (deltav i).
Proof.
rewrite /ten_lfun lfunE /= /ten_lfun_fun (bigD1 i)// big1//=.
by move=>j /negPf nji; rewrite cdvdelta nji scale0r.
by rewrite cdvdelta eqxx scale1r addr0.
Qed.

Lemma tenf_apply S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) : 
  [disjoint S & S'] ->
  forall u v, (f \⊗ g) (u ⊗v v) = (f u) ⊗v (g v).
Proof.
move=>dis u v; symmetry; rewrite {1}(deccdv u) (deccdv (tenv u v)).
rewrite !linear_sum linear_suml/= idxSsum//; apply eq_bigr=>i _.
rewrite {1}(deccdv v) !linear_sum /=; apply eq_bigr=>j _.
rewrite !linearZ /= linearZl/= -tenfdv idxSUl// idxSUr// scalerA.
congr (_ *: _); rewrite /tenv unlock linear_sum/= (bigD1 (idxU i j))// big1/=.
by move=>k /negPf nki; rewrite linearZ/= cdvdelta eq_sym nki mulr0.
by rewrite idxSUl// idxSUr// linearZ/= cdvdelta eqxx mulr1 addr0 mulrC.
Qed.

Lemma tenf_outp S T S' T' (u : 'H[H]_S) (v : 'H[H]_S') (w : 'H[H]_T) (t : 'H[H]_T'):
  [> u ; v <] \⊗ [> w ; t <] = [> u ⊗v w; v ⊗v t <].
Proof.
apply/lfunPD=>i; rewrite -tenfdv !outpE linearZl linearZr/= scalerA.
by f_equal; rewrite -[RHS]conj_dotp -cdvE cdvt !cdvE rmorphM !conj_dotp.
Qed.

Lemma linear_tenf S T S' T' f : linear (@ten_lfun S T S' T' f).
Proof. 
move=>a v w; apply/lfunPD=>u; rewrite !lfunE/= !lfunE/= !lfunE/= /ten_lfun_fun;
rewrite linear_sum /= -big_split; apply eq_bigr=>i _;
by rewrite !lfunE/= !lfunE/= !linearPr/= scalerDr !scalerA mulrC.
Qed.
Canonical tenf_additive S T S' T' f := Additive (@linear_tenf S T S' T' f).
Canonical tenf_linear S T S' T' f := Linear (@linear_tenf S T S' T' f).
Definition tenr_lfun S T S' T' f := (@ten_lfun S T S' T')^~ f.
Lemma linear_tenfr S T S' T' f : linear (@tenr_lfun S T S' T' f).
Proof.
move=>a v w; apply/lfunPD=>u; rewrite !lfunE/= !lfunE/= !lfunE/= /ten_lfun_fun;
rewrite linear_sum /= -big_split; apply eq_bigr=>i _;
by rewrite !lfunE/= !lfunE/= !linearPl/= scalerDr !scalerA mulrC.
Qed.
Canonical tenfr_additive S T S' T' f := Additive (@linear_tenfr S T S' T' f).
Canonical tenfr_linear S T S' T' f := Linear (@linear_tenfr S T S' T' f).
Canonical tenf_rev S T S' T' := 
  [revop (@tenr_lfun S T S' T') of (@ten_lfun S T S' T')].
Canonical tenf_is_bilinear S T S' T' := [bilinear of (@ten_lfun S T S' T')].

Lemma tenf_comp S T S' T' W W' (f1: 'F[H]_(S,T)) (f2: 'F[H]_(W,S)) 
  (g1: 'F[H]_(S',T')) (g2: 'F[H]_(W',S')) : [disjoint S & S'] ->
  (f1 \o f2) \⊗ (g1 \o g2) = (f1 \⊗ g1) \o (f2 \⊗ g2).
Proof.
move=>dis; apply/lfunPD=>i.
by rewrite comp_lfunE -!tenfdv !comp_lfunE tenf_apply.
Qed.

Lemma tenf_conj S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  (f \⊗ g)^C = f^C \⊗ g ^C.
Proof. by apply/lfunPD=>i; rewrite -tenfdv !conjfE !conjvdv -tenfdv tenv_conj. Qed.

Lemma tenf_adj S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  (f \⊗ g)^A = f^A \⊗ g^A.
Proof. 
by apply/lfunPD=>i; apply/cdvP=>j; rewrite adjcdv -!tenfdv !cdvt !adjcdv rmorphM.
Qed.

Lemma tenf_tr S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  (f \⊗ g)^T = f^T \⊗ g^T.
Proof. by rewrite !trfAC tenf_adj tenf_conj. Qed.

Lemma linear_dotf S T S' T' f : linear (@dot_lfun S T S' T' f).
Proof. 
move=>a v w; rewrite /dot_lfun linearPl/=.
by rewrite linearP/= comp_lfunDr comp_lfunZr.
Qed.
Canonical dotf_additive S T S' T' f := Additive (@linear_dotf S T S' T' f).
Canonical dotf_linear S T S' T' f := Linear (@linear_dotf S T S' T' f).
Definition dotr_lfun S T S' T' f := (@dot_lfun S T S' T')^~ f.
Lemma linear_dotfr S T S' T' f : linear (@dotr_lfun S T S' T' f).
Proof.
move=>a v w; rewrite /dotr_lfun /dot_lfun linearPl/=.
by rewrite comp_lfunDl comp_lfunZl.
Qed.
Canonical dotfr_additive S T S' T' f := Additive (@linear_dotfr S T S' T' f).
Canonical dotfr_linear S T S' T' f := Linear (@linear_dotfr S T S' T' f).
Canonical dotf_rev S T S' T' := 
  [revop (@dotr_lfun S T S' T') of (@dot_lfun S T S' T')].
Canonical dotf_is_bilinear S T S' T' := [bilinear of (@dot_lfun S T S' T')].

Lemma dotf_conj S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  (f \⋅ g)^C = f^C \⋅ g^C.
Proof. by rewrite /dot_lfun !conjf_comp castlf_conj !tenf_conj !conjf1. Qed.

Lemma dotf_adj S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  (f \⋅ g)^A = g^A \⋅ f^A.
Proof.
rewrite /dot_lfun !adjf_comp castlf_adj /= !tenf_adj castlf_complf !adjf1.
congr (_ \o castlf (_, _) _).
by rewrite (eq_irrelevance (esym (setUDS T' S)) (setUDS S T')).
Qed.

Lemma dotf_tr S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) :
  (f \⋅ g)^T = g^T \⋅ f^T.
Proof. by rewrite !trfAC dotf_adj dotf_conj. Qed.

Lemma linear_sdotf S T f : linear (@sdot_lfun S T f).
Proof. by move=>a v w; rewrite /sdot_lfun linearP/= linearD/= linearZ/=. Qed.
Canonical sdotf_additive S T f := Additive (@linear_sdotf S T f).
Canonical sdotf_linear S T f := Linear (@linear_sdotf S T f).
Definition sdotr_lfun S T f := (@sdot_lfun S T)^~ f.
Lemma linear_sdotfr S T f : linear (@sdotr_lfun S T f).
Proof. by move=>a v w; rewrite /sdotr_lfun /sdot_lfun linearPl/= linearD/= linearZ/=. Qed.
Canonical sdotfr_additive S T f := Additive (@linear_sdotfr S T f).
Canonical sdotfr_linear S T f := Linear (@linear_sdotfr S T f).
Canonical sdotf_rev S T := [revop (@sdotr_lfun S T) of (@sdot_lfun S T)].
Canonical sdotf_is_bilinear S T := [bilinear of (@sdot_lfun S T)].

Lemma sdotf_conj S T (f: 'F[H]_S) (g: 'F[H]_T) :
  (f \O g)^C = f^C \O g^C.
Proof. by rewrite /sdot_lfun castlf_conj dotf_conj. Qed.

Lemma intro_dvf S T W (f: 'F[H]_(T, W)) (g: 'F[H]_(S,T)) u :
  f (g u) = \sum_i cdv i (g u) *: f (deltav i).
Proof.
rewrite {1}(deccdv (g u)) linear_sum /=.
by apply eq_bigr=>i _; rewrite linearZ.
Qed.

(* tenor of lfun over disjoint domain *)
Definition tenfm (J: finType) (fs fs' : J -> {set L})
  (u: forall i : J, 'F[H]_(fs i, fs' i)) := liftlf u.

Lemma tenfmdv (J: finType) (fs fs' : J -> {set L}) 
  (f: forall i : J, 'F[H]_(fs i, fs' i)) (i : idx (\bigcup_i (fs i))) :
    tenvm (fun k : J => f k (deltav (flatidx i k)))
      = tenfm f (deltav i).
Proof.
rewrite /tenfm liftlf_delta /tenvm; f_equal.
by apply/mvectorP=>j; rewrite !mvE.
Qed.

Lemma tenfmP (J: finType) (fs fs' : J -> {set L}) (f g : forall i : J, 'F[H]_(fs i, fs' i)) :
  (forall i, f i = g i) -> tenfm f = tenfm g.
Proof. by move=>P; apply/lfunPD=>i; rewrite -!tenfmdv; apply/tenvmP=>j; rewrite P. Qed.

Lemma tenfm_apply (J: finType) (fs fs' : J -> {set L}) 
  (f: forall i : J, 'F[H]_(fs i, fs' i)) (v : forall i : J, 'H[H]_(fs i)) :
    disf fs ->
    tenfm f (tenvm v) = tenvm (fun k : J => f k (v k)).
Proof.
move=>dis; rewrite /tenfm /tenvm liftlfE//; f_equal.
by apply/mvectorP=>j; rewrite !mvE.
Qed.

Lemma tenfm_outp (J: finType) (fs fs' : J -> {set L}) 
  (u : forall i : J, 'H[H]_(fs i)) (v : forall i : J, 'H[H]_(fs' i)) :
  tenfm (fun k : J => [> u k ; v k <]) = [> tenvm u ; tenvm v <].
Proof.
apply/lfunPD=>i. rewrite -tenfmdv outpE. apply/intro_dvl=>j.
rewrite linearZ/= -conj_dotp -cdvE !cdvtm rmorph_prod -big_split/=.
by apply eq_bigr=>k _; rewrite outpE linearZ/= conj_dotp.
Qed.

Lemma tenfm_adj (J: finType) (fs fs' : J -> {set L}) 
  (f: forall i : J, 'F[H]_(fs i, fs' i)) :
    (tenfm f)^A = tenfm (fun i=>(f i)^A).
Proof.
apply/lfunPD=>i; apply/cdvP=>j; rewrite adjcdv -!tenfmdv !cdvtm rmorph_prod.
by apply eq_bigr=>k _; rewrite adjcdv.
Qed.

Lemma tenfm_conj (J: finType) (fs fs' : J -> {set L}) 
  (f: forall i : J, 'F[H]_(fs i, fs' i)) :
    (tenfm f)^C = tenfm (fun i=>(f i)^C).
Proof.
apply/lfunPD=>i; apply/cdvP=>j.
rewrite conjfE conjvcdv conjvdv -!tenfmdv !cdvtm rmorph_prod.
by apply eq_bigr=>k _; rewrite conjfE conjvdv conjvcdv.
Qed.

Lemma tenfm_tr (J: finType) (fs fs' : J -> {set L}) 
  (f: forall i : J, 'F[H]_(fs i, fs' i)) :
    (tenfm f)^T = tenfm (fun i=>(f i)^T).
Proof. by rewrite trfAC tenfm_adj tenfm_conj; apply/tenfmP=>i; rewrite trfAC. Qed.

Lemma tenfm_recl (n : nat) (dt dt' : n.+1.-tuple {set L}) 
  (f: forall i : 'I_n.+1, 'F[H]_(dt ~_ i, dt' ~_ i)) :
  castlf (esym (idx_big_recl_cast dt), esym (idx_big_recl_cast dt')) (tenfm f) = 
    (f ord0 \⊗ tenfm (fun i=> (f (fintype.lift ord0 i)))).
Proof.
apply/lfunPD=>i; apply/cdvP=>j; rewrite castlfE/= esymK -cdv_cast 
  deltav_cast -tenfmdv cdvtm -tenfdv cdvt -tenfmdv cdvtm.
rewrite big_ord_recl; f_equal.
by rewrite !idx_big_recl0 !castidx_comp !castidx_id.
apply eq_bigr=>/= k _; do ? f_equal;
by rewrite -idx_big_recl castidx_comp castidx_id.
Qed.

End LinfunDef.

Notation "f \⊗ g" := (ten_lfun f g) (at level 45, left associativity): lfun_scope.
Notation "f \⋅ g" := (dot_lfun f g) (at level 40, left associativity): lfun_scope.
Notation "f \O g" := (sdot_lfun f g) (at level 40, left associativity): lfun_scope.

Section BiLinearComplfun.
Local Open Scope lfun_scope.

Lemma comp_lfunACA (R : ringType) (U1 U2 U3 U4 U5 : vectType R) (A: 'Hom(U4,U5)) (B: 'Hom(U3,U4))
(C: 'Hom(U2,U3)) (D: 'Hom(U1,U2)) :
  A \o B \o C \o D = A \o (B \o C) \o D.
Proof. by rewrite !comp_lfunA. Qed.

Lemma linear_comp_lfun (R : comRingType) (aT vT rT : vectType R) f :
    linear (@comp_lfun _ aT vT rT f).
Proof. by move=>a u v; rewrite comp_lfunDr comp_lfunZr. Qed. 
Local Canonical comp_lfun_linear (R : comRingType) (aT vT rT : vectType R) f := 
    Linear (@linear_comp_lfun _ aT vT rT f).
Definition comp_lfunr (R : comRingType) (aT vT rT : vectType R) f := 
    (@comp_lfun _ aT vT rT)^~ f.
Lemma linear_comp_lfunr (R : comRingType) (aT vT rT : vectType R) f : 
    linear (@comp_lfunr _ aT vT rT f).
Proof. by move=>a u v; rewrite /comp_lfunr comp_lfunDl comp_lfunZl. Qed.
Local Canonical comp_lfunr_linear (R : comRingType) (aT vT rT : vectType R) f := 
    Linear (@linear_comp_lfunr _ aT vT rT f).
Local Canonical comp_lfun_rev (R : comRingType) (aT vT rT : vectType R) := 
    [revop (@comp_lfunr _ aT vT rT) of (@comp_lfun _ aT vT rT)].
Canonical comp_lfun_is_bilinear (R : comRingType) (aT vT rT : vectType R) := 
    [bilinear of (@comp_lfun _ aT vT rT)].

End BiLinearComplfun.

Section TenDotTheory.
Context (L : finType) (H : L -> chsType).
Variables (S T S' T' : {set L}).
Implicit Type (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')).
Local Open Scope lfun_scope.

Lemma tenf0 f : f \⊗ (0: 'F[H]_(S',T')) = 0.
Proof. exact: linear0r. Qed.

Lemma ten0f g : (0: 'F[H]_(S,T)) \⊗ g = 0.
Proof. exact: linear0l. Qed.

Lemma tenf11 : (\1: 'F[H]_S) \⊗ (\1: 'F[H]_S') = \1.
Proof.
apply/lfunPD=>i; rewrite /ten_lfun lfunE /= /ten_lfun_fun (bigD1 i)//= big1.
by move=>k /negPf nki; rewrite cdvdelta nki scale0r.
by rewrite !lfunE /= -deltavt cdvdelta eqxx scale1r addr0.
Qed.

Lemma tenfDl g (f1 f2: 'F[H]_(S,T)) : (f1 + f2) \⊗ g = (f1 \⊗ g) + (f2 \⊗ g).
Proof. exact: linearDl. Qed.

Lemma tenfDr f (g1 g2: 'F[H]_(S',T')) : f \⊗ (g1 + g2) = (f \⊗ g1) + (f \⊗ g2).
Proof. exact: linearDr. Qed.

Lemma tenfNl g f : (- f) \⊗ g = - (f \⊗ g).
Proof. exact: linearNl. Qed.

Lemma tenfNr f g : f \⊗ (- g) = - (f \⊗ g).
Proof. exact: linearNr. Qed.

Lemma tenfZl g (c: C) f : (c *: f) \⊗ g = c *: (f \⊗ g).
Proof. exact: linearZl. Qed.

Lemma tenfZr f (c: C) g : f \⊗ (c *: g) = c *: (f \⊗ g).
Proof. exact: linearZr. Qed.

Lemma tenfBl g f1 f2 : (f1 - f2) \⊗ g = f1 \⊗ g - f2 \⊗ g.
Proof. exact: linearBl. Qed.

Lemma tenfBr f g1 g2 : f \⊗ (g1 - g2) = f \⊗ g1 - f \⊗ g2.
Proof. exact: linearBr. Qed.

Lemma tenfPl g (c: C) f1 f2: (c *: f1 + f2) \⊗ g = c *: (f1 \⊗ g) + (f2 \⊗ g).
Proof. exact: linearPl. Qed.

Lemma tenfPr f (c: C) g1 g2 : f \⊗ (c *: g1 + g2) = c *: (f \⊗ g1) + (f \⊗ g2).
Proof. exact: linearPr. Qed.

Lemma tenfMnl g f n : (f *+ n) \⊗ g = (f \⊗ g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma tenfMnr f g n : f \⊗ (g *+ n) = (f \⊗ g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma tenfMNnl g f n : (f *- n) \⊗ g = (f \⊗ g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma tenfMNnr f g n : f \⊗ (g *- n) = (f \⊗ g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma tenf_suml g I r (P: pred I) (E: I -> 'F[H]_(S, T)) :
 (\sum_(i <- r | P i) E i) \⊗ g = \sum_(i <- r | P i) (E i \⊗ g).
Proof. exact: linear_suml. Qed.

Lemma tenf_sumr f I r (P: pred I) (E: I -> 'F[H]_(S', T')) :
 f \⊗ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (f \⊗ E i).
Proof. exact: linear_sumr. Qed.

Lemma tenf_comp1r W f (h: 'F[H]_(W,S)) : [disjoint S & S'] -> 
  (f \o h) \⊗ (\1: 'F[H]_S') = (f \⊗ \1) \o (h \⊗ \1).
Proof. by move=>dis; rewrite -tenf_comp// comp_lfun1l. Qed.

Lemma tenf_comp1l W f (h: 'F[H]_(W,S)) : [disjoint S' & S] -> 
  (\1: 'F[H]_S') \⊗ (f \o h) = (\1 \⊗ f) \o (\1 \⊗ h).
Proof. by move=>dis; rewrite -tenf_comp// comp_lfun1l. Qed.

Lemma dotf0 f : f \⋅ (0: 'F[H]_(S',T')) = 0.
Proof. exact: linear0r. Qed.

Lemma dot0f g : (0: 'F[H]_(S,T)) \⋅ g = 0.
Proof. exact: linear0l. Qed.

Lemma dotfDl g f1 f2 : (f1 + f2) \⋅ g = f1 \⋅ g + f2 \⋅ g.
Proof. exact: linearDl. Qed. 

Lemma dotfDr f g1 g2 : f \⋅ (g1 + g2) = f \⋅ g1 + f \⋅ g2.
Proof. exact: linearDr. Qed. 

Lemma dotfNl g f : (- f) \⋅ g = - (f \⋅ g).
Proof. exact: linearNl. Qed. 

Lemma dotfNr f g : f \⋅ (- g) = - (f \⋅ g).
Proof. exact: linearNr. Qed. 

Lemma dotfZl g c f : (c *: f) \⋅ g = c *: (f \⋅ g).
Proof. exact: linearZl. Qed. 

Lemma dotfZr f c g : f \⋅ (c *: g) = c *: (f \⋅ g).
Proof. exact: linearZr. Qed. 

Lemma dotfBl g f1 f2 : (f1 - f2) \⋅ g = f1 \⋅ g - f2 \⋅ g.
Proof. exact: linearBl. Qed. 

Lemma dotfBr f g1 g2 : f \⋅ (g1 - g2) = f \⋅ g1 - f \⋅ g2.
Proof. exact: linearBr. Qed. 

Lemma dotfPl g c f1 f2 : (c *: f1 + f2) \⋅ g = c *: (f1 \⋅ g) + (f2 \⋅ g).
Proof. exact: linearPl. Qed. 

Lemma dotfPr f c g1 g2 : f \⋅ (c *: g1 + g2) = c *: (f \⋅ g1) + (f \⋅ g2).
Proof. exact: linearPr. Qed. 

Lemma dotfMnl g f n : (f *+ n) \⋅ g = (f \⋅ g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma dotfMnr f g n : f \⋅ (g *+ n) = (f \⋅ g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma dotfMNnl g f n : (f *- n) \⋅ g = (f \⋅ g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma dotfMNnr f g n : f \⋅ (g *- n) = (f \⋅ g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma dotf_suml g I r (P: pred I) (E: I -> 'F[H]_(S, T)) :
 (\sum_(i <- r | P i) E i) \⋅ g = \sum_(i <- r | P i) ((E i) \⋅ g).
Proof. exact: linear_suml. Qed.

Lemma dotf_sumr f I r (P: pred I) (E: I -> 'F[H]_(S', T')) :
  f \⋅ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (f \⋅ (E i)).
Proof. exact: linear_sumr. Qed.

End TenDotTheory.

Section SdotTheory.
Context (L : finType) (H : L -> chsType).
Variables (S T : {set L}).
Implicit Type (f: 'F[H]_S) (g: 'F[H]_T).
Local Open Scope lfun_scope.

Lemma sdotf0 f : f \O (0: 'F[H]_T) = 0.
Proof. exact: linear0r. Qed.

Lemma sdot0f g : (0: 'F[H]_S) \O g = 0.
Proof. exact: linear0l. Qed.

Lemma sdotf11 : (\1 : 'F[H]_S) \O (\1 : 'F[H]_T) = \1.
Proof.
rewrite /sdot_lfun /dot_lfun !tenf11 comp_lfun1l castlf_comp etrans_id.
by rewrite (eq_irrelevance (etrans _ _) (setUDV T S)) castlf1.
Qed.

Lemma sdotfDl g f1 f2 : (f1 + f2) \O g = f1 \O g + f2 \O g.
Proof. exact: linearDl. Qed. 

Lemma sdotfDr f g1 g2 : f \O (g1 + g2) = f \O g1 + f \O g2.
Proof. exact: linearDr. Qed. 

Lemma sdotfNl g f : (- f) \O g = - (f \O g).
Proof. exact: linearNl. Qed. 

Lemma sdotfNr f g : f \O (- g) = - (f \O g).
Proof. exact: linearNr. Qed. 

Lemma sdotfZl g c f : (c *: f) \O g = c *: (f \O g).
Proof. exact: linearZl. Qed. 

Lemma sdotfZr f c g : f \O (c *: g) = c *: (f \O g).
Proof. exact: linearZr. Qed. 

Lemma sdotfBl g f1 f2 : (f1 - f2) \O g = f1 \O g - f2 \O g.
Proof. exact: linearBl. Qed. 

Lemma sdotfBr f g1 g2 : f \O (g1 - g2) = f \O g1 - f \O g2.
Proof. exact: linearBr. Qed. 

Lemma sdotfPl g c f1 f2 : (c *: f1 + f2) \O g = c *: (f1 \O g) + (f2 \O g).
Proof. exact: linearPl. Qed. 

Lemma sdotfPr f c g1 g2 : f \O (c *: g1 + g2) = c *: (f \O g1) + (f \O g2).
Proof. exact: linearPr. Qed. 

Lemma sdotfMnl g f n : (f *+ n) \O g = (f \O g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma sdotfMnr f g n : f \O (g *+ n) = (f \O g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma sdotfMNnl g f n : (f *- n) \O g = (f \O g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma sdotfMNnr f g n : f \O (g *- n) = (f \O g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma sdotf_suml g I r (P: pred I) (E: I -> 'F[H]_S) :
 (\sum_(i <- r | P i) E i) \O g = \sum_(i <- r | P i) ((E i) \O g).
Proof. exact: linear_suml. Qed.

Lemma sdotf_sumr f I r (P: pred I) (E: I -> 'F[H]_T) :
  f \O (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (f \O (E i)).
Proof. exact: linear_sumr. Qed.

End SdotTheory.

Definition masklf (L:finType) (H:L->chsType) S T (A : 'F[H]_(S,T)) := 
    A : ((fun D : {set L} * {set L} => 'F[H]_(D.1,D.2)) (S,T)).
Notation "X '=c' Y" := (@eq_dep _ _ _ (masklf X) _ (masklf Y)) (at level 70) : lfun_scope.

Section ConformLF.
Context (L:finType) (H:L->chsType).
Implicit Type (S T : {set L}).
Local Open Scope lfun_scope.

Lemma cf_eq S T (A B : 'F[H]_(S,T)) :
  A =c B <-> A = B.
split=>[P|->//]. 
suff P1 : (forall x y : {set L} * {set L}, {x = y} + {x <> y}).
move: (eq_dep_eq_dec P1 P). by [].
move=>x y. case E: (x == y).
by move: E=>/eqP; left. by move: E=>/eqP; right.
Qed.

Lemma cf_sym S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B <-> B =c A.
Proof. by split=>P; apply/eq_dep_sym. Qed.

Lemma cf_trans S1 T1 S2 T2 S3 T3: 
  forall (a : 'F[H]_(S1,T1)) (b : 'F[H]_(S2,T2)) (c : 'F[H]_(S3,T3)),
    a =c b -> b =c c -> a =c c.
Proof. move=>a b c; exact: eq_dep_trans. Qed.

Definition eq_conformlf S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :=
  match S1 =P S2, T1 =P T2 with
  | ReflectT eq_m, ReflectT eq_n => castlf (eq_m, eq_n) A = B
  | _, _ => False
  end.

Definition eq_op_conformlf S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :=
  match S1 =P S2, T1 =P T2 with
  | ReflectT eq_m, ReflectT eq_n => castlf (eq_m, eq_n) A == B
  | _, _ => false
  end.

Lemma cf_cond S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B -> (S1 = S2) * (T1 = T2).
Proof. by move=>P; inversion P. Qed.

Lemma cf_eqcf S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B <-> eq_conformlf A B.
Proof. 
split=>[P3|]; rewrite /eq_conformlf. move: P3 (cf_cond P3)=>+[eqS eqT]. 
all: (do 2 case: eqP=>//); move=>P1 P2. 1: clear eqS eqT. 
all: by case: T2 / P1 B; case: S2 / P2=> B; rewrite castlf_id cf_eq.
Qed.

Infix "==c" := eq_op_conformlf (at level 70) : lfun_scope.

Lemma cfeqP S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  reflect (A =c B) (A ==c B).
Proof.
apply/(iffP idP)=>[|P3]; last move: (cf_cond P3)=>[P4 P5].
all: rewrite /eq_op_conformlf; case: eqP=>[P1|//]; case: eqP=>[P2|//].
case: S2 / P1 B; case: T2 / P2=>B; by rewrite castlf_id=>/eqP->.
clear P4 P5; move: P3. case: S2 / P1 B; case: T2 / P2=>B.
by move/cf_eq=>->; rewrite castlf_id.
Qed.

Lemma cf_cast S1 T1 S2 T2 (eqST: (S1 = S2) * (T1 = T2))
  (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  castlf eqST A = B <-> A =c B.
Proof.
case: eqST=>eqS eqT; case: S2 / eqS B; case: T2 / eqT=> B.
by rewrite castlf_id cf_eq.
Qed.

Lemma cf_castKl S1 T1 S2 T2 S3 T3 (eqST: (S1 = S3) * (T1 = T3))
(A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  castlf eqST A =c B <-> A =c B.
Proof.
case: eqST=>eqS eqT; case: S3 / eqS B; case: T3 / eqT=> B.
by rewrite castlf_id.
Qed.

Lemma cf_castKr S1 T1 S2 T2 S3 T3 (eqST: (S2 = S3) * (T2 = T3))
  (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
    A =c castlf eqST B <-> A =c B.
Proof. by rewrite cf_sym cf_castKl cf_sym. Qed.

Definition cf_castK := (cf_castKl,cf_castKr).

Lemma cf_adj S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B -> A^A =c B^A.
Proof. by move=>P; move: P (cf_cond P)=>+[P1 P2]; 
case: S2 / P1 B; case: T2 / P2=>B; rewrite !cf_eq=>->. Qed.

Lemma cf_conj S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B -> A^C =c B^C.
Proof. by move=>P; move: P (cf_cond P)=>+[P1 P2]; 
case: S2 / P1 B; case: T2 / P2=>B; rewrite !cf_eq=>->. Qed.

Lemma cf_tr S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B -> A^T =c B^T.
Proof. by move=>P; move: P (cf_cond P)=>+[P1 P2]; 
case: S2 / P1 B; case: T2 / P2=>B; rewrite !cf_eq=>->. Qed.

Lemma cf_scale c S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B -> c *: A =c c *: B.
Proof. by move=>P; move: P (cf_cond P)=>+[P1 P2]; 
case: S2 / P1 B; case: T2 / P2=>B; rewrite !cf_eq=>->. Qed.

Lemma cf_opp S1 T1 S2 T2 (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) :
  A =c B -> - A =c - B.
Proof. by move=>P; move: P (cf_cond P)=>+[P1 P2]; 
case: S2 / P1 B; case: T2 / P2=>B; rewrite !cf_eq=>->. Qed.

Lemma cf_comp S1 S2 S3 T1 T2 T3 (A : 'F[H]_(S1,S3)) (B : 'F[H]_(S2,S1)) 
  (C : 'F[H]_(T1,T3)) (D : 'F[H]_(T2,T1)) :
  A =c C -> B =c D -> A \o B =c C \o D.
Proof. move=>P; move: P (cf_cond P)=>+[P1 P2].
case: T1 / P1 C D; case: T3 / P2=>C D; rewrite !cf_eq=>->.
move=>P; move: P (cf_cond P)=>+[P1 _].
by case: T2 / P1 B D=> B D; rewrite !cf_eq=>->. Qed.

Lemma cf_tens S1 S2 S3 S4 T1 T2 T3 T4 (A : 'F[H]_(S1,S2)) (B : 'F[H]_(S3,S4)) 
  (C : 'F[H]_(T1,T2)) (D : 'F[H]_(T3,T4)) :
  A =c C -> B =c D -> A \⊗ B =c C \⊗ D.
Proof. move=>P; move: P (cf_cond P)=>+[P1 P2].
case: T1 / P1 C; case: T2 / P2=>C; rewrite !cf_eq=>->.
move=>P; move: P (cf_cond P)=>+[P1 P2].
by case: T3 / P1 D; case: T4 / P2=>D; rewrite !cf_eq=>->. Qed.

Lemma cf_dot S1 S2 S3 S4 T1 T2 T3 T4 (A : 'F[H]_(S1,S2)) (B : 'F[H]_(S3,S4)) 
  (C : 'F[H]_(T1,T2)) (D : 'F[H]_(T3,T4)) :
  A =c C -> B =c D -> A \⋅ B =c C \⋅ D.
Proof. move=>P; move: P (cf_cond P)=>+[P1 P2].
case: T1 / P1 C; case: T2 / P2=>C; rewrite !cf_eq=>->.
move=>P; move: P (cf_cond P)=>+[P1 P2].
by case: T3 / P1 D; case: T4 / P2=>D; rewrite !cf_eq=>->. Qed.

Lemma cf_sdot S1 S2 T1 T2 (A : 'F[H]_S1) (B : 'F[H]_S2) 
  (C : 'F[H]_T1) (D : 'F[H]_T2) :
  A =c C -> B =c D -> A \O B =c C \O D.
Proof. move=>P; move: P (cf_cond P)=>+[P1 _].
case: T1 / P1 C=>C; rewrite !cf_eq=>->.
move=>P; move: P (cf_cond P)=>+[P1 _].
by case: T2 / P1 D=>D; rewrite !cf_eq=>->. Qed.

(* Since we cannot add implicit dependent type as relations        *)
(* we give a quick rewrite rules to lift castlf as out as possible *)
(* this works for tens and dots which has no constraint, partly for mul and sdot *)
Lemma setcTl S S' T : S = S' -> S :|: T = S' :|: T.
Proof. by move=>->. Qed.
Arguments setcTl {S S'} T.
Lemma setcTr S S' T : S = S' -> T :|: S = T :|: S'.
Proof. by move=>->. Qed.
Arguments setcTr {S S'} T.

Lemma setcDl S S' S2 T2 : S = S' -> S2 :|: S :\: T2 = S2 :|: S' :\: T2.
Proof. by move=>->. Qed.
Arguments setcDl {S S'} S2 T2.
Lemma setcDr S S' T T' T2 : (S = S') * (T = T') -> T :|: T2 :\: S = T' :|: T2 :\: S'.
Proof. by move=>[->->]. Qed.
Arguments setcDr {S S' T T'} T2.

Lemma tens_castl S1 T1 S2 T2 S1' T1' (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) 
  (eqA : (S1 = S1') * (T1 = T1')) :
  castlf eqA A \⊗ B = castlf (setcTl _ eqA.1, setcTl _ eqA.2) (A \⊗ B).
Proof. case: eqA=>P1 P2; case: S1' / P1; case: T1' / P2=>/=. by rewrite !castlf_id. Qed.

Lemma tens_castr S1 T1 S2 T2 S1' T1' (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) 
  (eqA : (S1 = S1') * (T1 = T1')) :
  B \⊗ castlf eqA A = castlf (setcTr _ eqA.1, setcTr _ eqA.2) (B \⊗ A).
Proof. case: eqA=>P1 P2; case: S1' / P1; case: T1' / P2=>/=. by rewrite !castlf_id. Qed.

Lemma dot_castl S1 T1 S2 T2 S1' T1' (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) 
(eqA : (S1 = S1') * (T1 = T1')) :
  castlf eqA A \⋅ B = castlf (setcDl _ _ eqA.1, setcDr _ eqA) (A \⋅ B).
Proof. case: eqA=>P1 P2; case: S1' / P1; case: T1' / P2=>/=. by rewrite !castlf_id. Qed.

Lemma dot_castr S1 T1 S2 T2 S1' T1' (A : 'F[H]_(S1,T1)) (B : 'F[H]_(S2,T2)) 
(eqA : (S1 = S1') * (T1 = T1')) : 
  B \⋅ castlf eqA A = castlf (setcDr _ (eqA.2,eqA.1), setcDl _ _ eqA.2) (B \⋅ A).
Proof. case: eqA=>P1 P2; case: S1' / P1; case: T1' / P2=>/=. by rewrite !castlf_id. Qed.

Lemma mul_cast S W T S' W' T' (A : 'F[H]_(W,T)) (B : 'F[H]_(S,W)) 
  (eqW : W = W') (eqT: T = T') (eqS: S = S') :
    castlf (eqW,eqT) A \o castlf (eqS,eqW) B = castlf (eqS,eqT) (A \o B).
Proof. by case: W' / eqW; case: T' /eqT; case: S' /eqS; rewrite !castlf_id. Qed.

Lemma mul_castl S W T T' (A : 'F[H]_(W,T)) (B : 'F[H]_(S,W)) (eqT: T = T') :
    castlf (erefl _, eqT) A \o B = castlf (erefl,eqT) (A \o B).
Proof. by case: T' /eqT; rewrite !castlf_id. Qed.

Lemma mul_castr S W T S' (A : 'F[H]_(W,T)) (B : 'F[H]_(S,W)) (eqS: S = S') :
    A \o castlf (eqS,erefl) B = castlf (eqS,erefl) (A \o B).
Proof. by case: S' /eqS; rewrite !castlf_id. Qed.

Lemma sdot_castl S T S' (A : 'F[H]_S) (B : 'F[H]_T) (eqS : S = S'):
  castlf (eqS, eqS) A \O B = castlf (setcTl _ eqS,setcTl _ eqS) (A \O B).
Proof. by case: S' /eqS; rewrite !castlf_id. Qed.

Lemma sdot_castr S T T' (A : 'F[H]_S) (B : 'F[H]_T) (eqT : T = T'):
  A \O castlf (eqT, eqT) B = castlf (setcTr _ eqT,setcTr _ eqT) (A \O B).
Proof. by case: T' /eqT; rewrite !castlf_id. Qed.

Definition castlf_out := (tens_castl,tens_castr,dot_castl,dot_castr,mul_cast,
mul_castl,mul_castr,sdot_castl,sdot_castr).

End ConformLF.

Infix "==c" := eq_op_conformlf (at level 70) : lfun_scope.

Section cfTheory.
Context (L:finType) (H:L->chsType).
Implicit Type (S T : {set L}).
Local Open Scope lfun_scope.

(* dealing with asscociativity and commutativity of ten_lfun *)
Definition idxR S T (subST: S :<=: T) (eAB : 'Idx[H]_T) : 'Idx[H]_S :=
  \mvector_ (i : {i|i \in S}) eAB (incl subST i).

Lemma idxRA S T (W: {set L}) (subST: S :<=: T) (subTW: T :<=: W) (eAB : 'Idx[H]_W) : 
    idxR subST (idxR subTW eAB) = idxR (subset_trans subST subTW) eAB.
Proof.
apply/mvectorP=>i; rewrite !mvE/=; rewrite /incl /=.
by congr (eAB (exist _ _ _)); apply eq_irrelevance.
Qed.

Lemma idxR_castL S S' T (eqS: S = S') subST subS'T (eAB : 'Idx[H]_T) :
    castidx eqS (idxR subST eAB) = idxR subS'T eAB.
Proof. 
case: S' / eqS subS'T => P. 
by rewrite castidx_id (eq_irrelevance subST P).
Qed.

Lemma idxR_castR S T T' (eqT: T = T') subST subST' (eAB : 'Idx[H]_T) :
    (idxR subST' (castidx eqT eAB) : 'Idx[H]_S) = idxR subST eAB.
Proof. 
case: T' / eqT subST' => P. 
by rewrite castidx_id (eq_irrelevance subST P).
Qed.

Lemma idxSl_idxR S T (i : 'Idx[H]_(S :|: T)) :
    idxSl i = idxR (subsetUl S T) i.
Proof. by []. Qed.

Lemma idxSr_idxR S T (i : 'Idx[H]_(S :|: T)) :
    idxSr i = idxR (subsetUr S T) i.
Proof. by []. Qed.

Lemma idxR_id S (eqS: S :<=: S) (eAB : 'Idx[H]_S) : 
    idxR eqS eAB = eAB.
Proof. 
rewrite /idxR; apply/mvectorP=>i; rewrite !mvE /incl; destruct i.
by congr (eAB (exist _ _ _)); apply eq_irrelevance.
Qed.

Definition idxR_cast := (idxR_castL, idxR_castR).
Definition idxS_idxR := (idxSl_idxR, idxSr_idxR).

Lemma tenf_castA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2))
  (h: 'F[H]_(S3,T3)) : 
 castlf (setUA S1 S2 S3, setUA T1 T2 T3) (f \⊗ (g \⊗ h)) = ((f \⊗ g) \⊗ h).
Proof.
apply/lfunPD=>/=i. apply/cdvP=>/= j.
rewrite castlfE/= cdv_castV deltav_cast -!tenfdv !cdvt mulrA.
do ? [apply f_equal2 | apply f_equal] =>//; 
rewrite ?idxSl_idxR ?idxSr_idxR ?idxR_castR -?setUA ?subsetUl ?subsetUr// => H1; 
rewrite !idxRA; by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenfA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2))
  (h: 'F[H]_(S3,T3)) : (f \⊗ (g \⊗ h)) =c ((f \⊗ g) \⊗ h).
Proof. by rewrite -tenf_castA cf_castK. Qed.

Lemma tenf_castC S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) : 
  castlf ((setUC S S'), (setUC T T')) (f \⊗ g) = (g \⊗ f).
Proof.
apply/lfunPD=>/=i. apply/cdvP=>/= j.
rewrite castlfE/= deltav_cast cdv_castV -!tenfdv !cdvt mulrC.
do ? [apply f_equal2 | apply f_equal] =>//; 
    rewrite ?idxS_idxR ?idxR_cast ?subsetUl ?subsetUr// => H1;
    by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenfC S1 T1 S2 T2 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2))
   : (f \⊗ g) =c (g \⊗ f).
Proof. by rewrite -tenf_castC cf_castK. Qed.

Lemma tenf_cast1r S T (f: 'F[H]_(S,T))  : 
  castlf ((setU0 S),(setU0 T)) (f \⊗ (\1 : 'F[H]_set0)) = f.
Proof.
apply/lfunPD=>/=i. apply/cdvP=>/= j.
rewrite castlfE/= deltav_cast cdv_castV -!tenfdv !cdvt mulrC.
rewrite ?idxS_idxR ?idxR_cast ?sub0set// => HS HT.
by rewrite ?idx0E ?lfunE/= cdvdelta eqxx mul1r !idxR_id.
Qed.

Lemma tenf1r S1 T1 (f: 'F[H]_(S1,T1))
   : (f \⊗ (\1 : 'F[H]_set0)) =c f.
Proof. by rewrite -{2}(tenf_cast1r f) cf_castK. Qed.

Lemma tenf_cast1l S T (f: 'F[H]_(S,T))  : 
  castlf ((set0U S),(set0U T)) ((\1 : 'F[H]_set0) \⊗ f) = f.
Proof. by rewrite -cf_eq cf_castK tenfC tenf1r. Qed.

Lemma tenf1l S T (f: 'F[H]_(S,T)) :
  ((\1 : 'F[H]_set0) \⊗ f) =c f.
Proof. by rewrite tenfC tenf1r. Qed.

Lemma dotf_sdot S T (f: 'F[H]_S) (g: 'F[H]_T) :
  f \⋅ g =c f \O g.
Proof. by rewrite /sdot_lfun cf_castK. Qed.

Lemma cf_implicit1 S T :
  S = T -> (\1 : 'F[H]_S) =c (\1 : 'F[H]_T).
Proof. by move=>P; case: T / P. Qed.

Lemma cf_implicit0 S T S' T' :
  S = S' -> T = T' -> (0 : 'F[H]_(S,T)) =c (0 : 'F[H]_(S',T')).
Proof. by move=>P1 P2; case: S' / P1; case: T' / P2. Qed.

Lemma dotfA_cond S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2))
  (h: 'F[H]_(S3,T3)) : 
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  (f \⋅ (g \⋅ h)) =c (f \⋅ g \⋅ h).
Proof.
move=>P1 P2; rewrite /dot_lfun !tenf_comp1r; last first.
rewrite -comp_lfunA. apply cf_comp; last first.
rewrite cf_castK. apply cf_comp; rewrite ?castlf_out !cf_castK.
1,2,3: rewrite -!tenfA ?tenf11; apply cf_tens=>//; apply cf_implicit1.
move: P1 P2; fsetdec L.
all: move: P1 P2; rewrite -!setI_eq0 =>/eqP/setP P1 /eqP/setP P2.
3,4: apply/eqP. all: apply/setP=>x; move: (P1 x) (P2 x); 
rewrite !inE; case: (x \in S1); case: (x \in S2); 
case: (x \in T2); case: (x \in T3) => //=; rewrite ?andbF//.
Qed.

(* g is square *)
Lemma dotfA S1 T1 S2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F[H]_S2)
  (h: 'F[H]_(S3,T3)) : 
  (f \⋅ (g \⋅ h)) =c (f \⋅ g \⋅ h).
Proof. by rewrite dotfA_cond// disjointXD. Qed.

Lemma dotf_ten_cond S1 T1 S2 T2 (f: 'F[H]_(S1,T1)) (g: 'F[H]_(S2,T2)) :
  [disjoint S1 & T2] -> 
  f \⋅ g =c f \⊗ g.
Proof.
move=>P3. have ->: ten_lfun f g = (ten_lfun f \1) \o (ten_lfun \1 g).
by rewrite -tenf_comp// comp_lfun1l comp_lfun1r.
rewrite /dot_lfun. apply/cf_comp. 2: rewrite cf_castK tenfC.
all: apply/cf_tens=>//; apply cf_implicit1; apply/setDidPl=>//. by rewrite disjoint_sym.
Qed.

Lemma dotfC_cond S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S',T')) : 
  [disjoint S & T'] -> [disjoint T & S'] ->
  (f \⋅ g) =c (g \⋅ f).
Proof. by move=>P1 P2; rewrite !dotf_ten_cond// 1?tenfC// disjoint_sym. Qed.

Lemma dotf1r S T (f: 'F[H]_(S,T))  : 
  (f \⋅ (\1 : 'F[H]_set0)) =c f.
Proof. by rewrite dotf_ten_cond ?tenf1r// disjointX0. Qed.

Lemma dotf1l S T (f: 'F[H]_(S,T))  : 
   ((\1 : 'F[H]_set0) \⋅ f) =c f.
Proof. by rewrite dotf_ten_cond ?tenf1l// disjoint0X. Qed.

Lemma dotfIl S T W (f: 'F[H]_(S,T)) :
  ((\1 : 'F[H]_W) \⋅ f) =c ((\1 : 'F[H]_(W :\: T)) \⋅ f).
Proof. 
rewrite /dot_lfun !tenf11; apply cf_comp;[| rewrite !cf_castK;
apply cf_tens=>//]; apply cf_implicit1; fsetdec L. 
Qed.

Lemma dotfIr S T W (f: 'F[H]_(S,T)) :
  (f \⋅ (\1 : 'F[H]_W)) =c (f \⋅ (\1 : 'F[H]_(W :\: S))).
Proof. 
rewrite /dot_lfun !tenf11; apply cf_comp;[apply cf_tens=>// | 
  rewrite !cf_castK]; apply cf_implicit1; fsetdec L. 
Qed.

Lemma dotf_mul S T W (f: 'F[H]_(S,T)) (g: 'F[H]_(W,S)) :
  f \⋅ g =c f \o g.
Proof.
by rewrite /dot_lfun; apply cf_comp; rewrite ?cf_castK setDv tenf1r.
Qed.

(* using sdot for quantum operation, measurement, etc... *)
Lemma sdotfA S1 S2 S3 (f: 'F[H]_S1) (g: 'F[H]_S2) (h: 'F[H]_S3) : 
  (f \O (g \O h)) =c ((f \O g) \O h).
Proof. by rewrite /sdot_lfun !castlf_out/= !castlf_comp !cf_castK dotfA. Qed.

Lemma sdotf_ten_cond S T (f: 'F[H]_S) (g: 'F[H]_T) :
  [disjoint S & T] -> f \O g =c f \⊗ g.
Proof. by move=>P; rewrite /sdot_lfun cf_castK dotf_ten_cond. Qed.

Lemma sdotfC_cond S T (f: 'F[H]_S) (g: 'F[H]_T) : 
  [disjoint S & T] -> (f \O g) =c (g \O f).
Proof. by move=>P; rewrite /sdot_lfun !cf_castK dotfC_cond. Qed.

Lemma sdotf1r S (f: 'F[H]_S) :
  f \O (\1 : 'F[H]_set0) =c f.
Proof. by rewrite /sdot_lfun cf_castK dotf1r. Qed.

Lemma sdotf1l S (f: 'F[H]_S) :
  (\1 : 'F[H]_set0) \O f =c f.
Proof. by rewrite /sdot_lfun cf_castK dotf1l. Qed.

Lemma sdotfIr S W (f: 'F[H]_S) :
  f \O (\1 : 'F[H]_W) =c f \O (\1 : 'F[H]_(W :\: S)).
Proof. by rewrite /sdot_lfun !cf_castK dotfIr. Qed.

Lemma sdotfIl S W (f: 'F[H]_S) :
  (\1 : 'F[H]_W) \O f =c (\1 : 'F[H]_(W :\: S)) \O f.
Proof. by rewrite /sdot_lfun !cf_castK dotfIl. Qed.

Lemma sdotfIC S W (f: 'F[H]_S) :
  f \O (\1 : 'F[H]_W) =c (\1 : 'F[H]_W) \O f.
Proof. by rewrite sdotfIr sdotfC_cond -?sdotfIl// disjointXD. Qed.

Lemma sdotfITl S W (f: 'F[H]_S) :
  (\1 : 'F[H]_W) \O f =c (\1 : 'F[H]_(W :\: S)) \⊗ f.
Proof. by rewrite sdotfIl sdotf_ten_cond// disjointDX. Qed.

Lemma sdotf_mul S (f: 'F[H]_S) (g: 'F[H]_S) :
  f \O g =c f \o g.
Proof. by rewrite /sdot_lfun cf_castK dotf_mul. Qed.

End cfTheory.
