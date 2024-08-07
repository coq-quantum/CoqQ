(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import -(notations)forms reals.
From quantum.external Require Import complex.
Require Import mcextra mcaextra notation hermitian quantum inhabited.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Declare Scope atype_scope.
Declare Scope atsyn_scope.
Declare Scope dtsyn_scope.
Declare Scope base_scope.
Declare Scope scalar_scope.
Declare Scope ket_scope.
Declare Scope bra_scope.
Declare Scope opt_scope.

Delimit Scope atype_scope with TA.
Delimit Scope atsyn_scope with AT.
Delimit Scope dtsyn_scope with DT.
Delimit Scope base_scope with DA.
Delimit Scope scalar_scope with DS.
Delimit Scope ket_scope with DK.
Delimit Scope bra_scope with DB.
Delimit Scope opt_scope with DO.

(******************************************************************************)
(* formalization :                                                            *)
(* L0. core language L0 (without big sum and fst/snd) with static type        *)
(*     checking done by coq directly;                                         *)
(*     (DONE) a) define the semantics                                         *)
(*     (DONE) b) prove all the rules                                          *)
(*     (TODO) c) update rules/axiomatic semantics                             *)
(*                                                                            *)
(* L1. full language L1 with static type checking done by coq directly;       *)
(*     (DONE) a) define the semantics                                         *)
(*     (DONE) b) relation between L0 and L1 for syntax and semantis           *)
(*     (TODO) c) prove rules/axiomatic semantics                              *)
(*                                                                            *)
(* L2. full language L2 with dynamic types                                    *)
(*     (DONE) a) define semantics                                             *)
(*     (DONE) b) relation between L1 and L2 for syntax and semantis           *)
(*     (TODO) c) prove rules/axiomatic semantics                              *)
(* -------------------------------------------------------------------------- *)
(* Relation: L0 - L1 - L2                                                     *)
(*    L0_L1_syn : formula in L0 -> formula in L1                              *)
(*    L0_L1_sem : forall t : formula in L0,                                   *)
(*                  L1_sem (L0_L1_syn t) = L0_sem t                           *)
(*    L1_L2_syn : formula in L1 -> formula in L2                              *)
(*    L1_L2_type : forall t : formula in L1 with type T,                      *)
(*                  L2_type (L1_L2_syn t) = T                                 *)
(*    L1_L2_sem : forall t : formula in L1,                                   *)
(*                  L2_sem (L1_L2_syn t) = L1_sem t                           *)
(*                                                                            *)
(* Conclusion: L0 - L1 - L2                                                   *)
(*    1. L0_L1_syn and L1_L2_syn are trivial                                  *)
(*    2. L0 -> L1 -> L2, the former the easier to understand                  *)
(*    3. L0_L1_sem and L1_L2_sem shows that L1_sem and L2_sem are correctly   *)
(*       defined, the former the easier to understand                         *)
(*    4. according to 3, we conclude,                                         *)
(*       a). if two formulas t1 = t2 in L0, then it is sufficient to show     *)
(*           that L0_L1_syn t1 = L0_L1_syn t2 in L1                           *)
(*       b). if two formulas t1 = t2 in L1, then it is sufficient to show     *)
(*           that L1_L2_syn t1 = L1_L2_syn t2 in L2                           *)
(******************************************************************************)

(* formalization :*)

Section AType.
Variable (atype : eqType).
Variable (eval_AT : atype -> ihbFinType).

(* syntax *)
Inductive AType :=
  | Atype (A : atype)
  | Apair (A1 : AType) (A2 : AType).

Fixpoint AType_eq (A1 A2 : AType) :=
  match A1, A2 with
  | Atype A1, Atype A2 => A1 == A2
  | Apair A1 A2, Apair A3 A4 => (AType_eq A1 A3) && (AType_eq A2 A4)
  | _, _ => false
  end.

Lemma AType_eqP (A1 A2 : AType) : reflect (A1 = A2) (AType_eq A1 A2).
Proof.
elim: A1 A2 =>[A1 | A1 IH1 ]; elim => [A2 | A2 IH2 ].
by apply/(iffP eqP)=>[->//|Pv]; inversion Pv.
by move=>??/=; apply: ReflectF.
- move=>IH [/=?|A3 A4]; first by apply: ReflectF.
  apply/(iffP idP).
    by move=>/=/andP[]/IH1->/IH->.
    by move=><-/=; rewrite eqxx andbT; apply/IH1.
- move=>A3 IH3 IH4 [A4/=|A4 A5]; first by apply: ReflectF.
  apply/(iffP idP).
    by move=>/=/andP[]/IH1->/IH4->.
    move=>Pv. have: (Apair A2 A3 = A5) by inversion Pv.
    move=>/IH4/=->; rewrite andbT; apply/IH1; by inversion Pv.
Qed.
HB.instance Definition _ := hasDecEq.Build AType AType_eqP.

Fixpoint eval_AType (t : AType) : ihbFinType :=
  match t with
  | Atype t => eval_AT t
  | Apair A1 A2 => ((eval_AType A1) * (eval_AType A2))%type
  end.

End AType.

Definition HA a ea (A : AType a) := (ihb_chsType (eval_AType ea A)).

Section Context_Valuation.
Variable (atype : eqType).
Variable (eval_AT : atype -> ihbFinType).
Local Notation AType := (@AType atype).
Local Notation eval_AType := (@eval_AType atype eval_AT).

Local Notation "''Ha' A" := (@HA atype eval_AT A)
  (at level 8, A at level 2, format "''Ha'  A").
Local Notation "''Hom{' A1 , A2 }" := ('Hom('Ha A1, 'Ha A2)) 
  (at level 8, format "''Hom{' A1 ,  A2 }").
Local Notation "''End{' A }" := ('End('Ha A)) 
  (at level 8, format "''End{' A }").

(* name of variables *)
Variable (aname stname : finType).
Variable (sname kname bname oname : finType).

Definition Gamma_A  := aname -> AType.
Definition Gamma_ST := stname -> AType.
Definition Gamma_B  := bname -> AType.
Definition Gamma_K  := kname -> AType.
Definition Gamma_O  := oname -> AType * AType.

Definition Gamma_A_update (ca : Gamma_A) (a : aname) (v : AType) : Gamma_A :=
  (fun x => if x == a then v else ca x).

Lemma Gamma_A_update_id (ca : Gamma_A) (a : aname) (A : AType) :
  (Gamma_A_update ca a A) a = A.
Proof. by rewrite /Gamma_A_update eqxx. Qed.
Lemma Gamma_A_update_eq (ca : Gamma_A) (a : aname) (A : AType) a' :
  a' = a -> (Gamma_A_update ca a A) a' = A.
Proof. move=>->; exact: Gamma_A_update_id. Qed.
Lemma Gamma_A_update_neq (ca : Gamma_A) (a : aname) (A : AType) a' :
  a' <> a -> (Gamma_A_update ca a A) a' = ca a'.
Proof. by rewrite /Gamma_A_update=>/eqP/negPf->. Qed.

Definition A_value (ca : Gamma_A) := forall n, eval_AType (ca n).
Definition ST_value (cst : Gamma_ST) := forall n , {set eval_AType (cst n)}.
Definition S_value := sname -> C.
Definition K_value (ck : Gamma_K) := forall n, 'Ha (ck n).
Definition B_value (cb : Gamma_B) := forall n, 'Ha (cb n).
Definition O_value (co : Gamma_O) := forall n, 'Hom{(co n).2, (co n).1}.

Definition A_update (ca : Gamma_A) (n : aname) (v : eval_AType (ca n)) 
  (A : A_value ca) : A_value ca :=
  fun x => if n =P x is ReflectT eq then 
                ecast k (eval_AType (ca k)) eq v 
           else A x.

Definition cast_A (A1 A2 : AType) (eqA : A1 = A2) (v : eval_AType A1) : eval_AType A2 :=
  let: erefl in _ = A2 := eqA return eval_AType A2 in v.

Definition A_value_update (ca : Gamma_A) (av : A_value ca) 
  (a : aname) (v : AType) (t : eval_AType v) : A_value (Gamma_A_update ca a v) :=
  fun x => match x =P a with
           | ReflectT eq  => cast_A (esym (Gamma_A_update_eq ca v eq)) t
           | ReflectF neq => cast_A (esym (Gamma_A_update_neq ca v neq)) (av x)
  end.

End Context_Valuation.


(*****************************************************************************)
(*                                Playground0                                *)
(*****************************************************************************)
Module Playground0.

Section DiracTRS_SOUND.
Variable (atype : eqType).
Variable (eval_AT : atype -> ihbFinType).
Variable (aname : finType).
Variable (sname kname bname oname : finType).

(* Notation for A, Context and Valuation *)
Notation AType := (@AType atype).
Notation eval_AType := (@eval_AType atype eval_AT).

Notation "''Ha' A" := (@HA atype eval_AT A)
  (at level 8, A at level 2, format "''Ha'  A").
Notation "''Hom{' A1 , A2 }" := ('Hom('Ha A1, 'Ha A2)) 
  (at level 8, format "''Hom{' A1 ,  A2 }").
Notation "''End{' A }" := ('End('Ha A)) 
  (at level 8, format "''End{' A }").

(* name of variables *)
Notation Gamma_A := (Gamma_A atype aname).
Notation Gamma_B := (Gamma_B atype bname).
Notation Gamma_K := (Gamma_K atype kname).
Notation Gamma_O := (Gamma_O atype oname).

Variable (ca : Gamma_A) (ck : Gamma_K) (cb : Gamma_B) (co : Gamma_O).

Notation A_value := (@A_value atype eval_AT aname ca).
Notation S_value := (@S_value sname).
Notation K_value := (@K_value atype eval_AT kname ck).
Notation B_value := (@B_value atype eval_AT bname cb).
Notation O_value := (@O_value atype eval_AT oname co).

Inductive A_base : AType -> Type :=
    | A_var (n : aname) : A_base (ca n)
    | A_ground (A : AType) (a : eval_AType A) : A_base A
    | A_pair (A1 A2 : AType) (a1 : A_base A1) (a2 : A_base A2) : A_base (Apair A1 A2).
    (* | A_fst (A1 A2 : AType) (a : A_base (Apair A1 A2)) : A_base A1
    | A_snd (A1 A2 : AType) (a : A_base (Apair A1 A2)) : A_base A2. *)

Inductive S_scalar : Type :=
    | S_var (n : sname)
    | S_0
    | S_1
    | S_delta (A : AType) (a1 a2 : A_base A)
    | S_add (s1 s2 : S_scalar)
    | S_mul (s1 s2 : S_scalar)
    | S_conj (s : S_scalar)
    | BK_inner (A : AType) (b : B_bra A) (k : K_ket A)
with K_ket : AType -> Type :=
    | K_var (n : kname) : K_ket (ck n)
    | K_0 (A : AType) : K_ket A
    | K_ground (A : AType) (a : A_base A) : K_ket A
    | B_adj (A : AType) (b : B_bra A) : K_ket A
    | K_scale (s : S_scalar) (A : AType) (k : K_ket A) : K_ket A
    | K_add (A : AType) (k1 k2 : K_ket A) : K_ket A
    | K_apply (A1 A2 : AType) (o : O_opt A1 A2) (k : K_ket A2) : K_ket A1
    | K_ten (A1 A2 : AType) (k1 : K_ket A1) (k2 : K_ket A2) : K_ket (Apair A1 A2)
with B_bra : AType -> Type :=
    | B_var (n : bname) : B_bra (cb n)
    | B_0 (A : AType) : B_bra A
    | B_ground (A : AType) (a : A_base A) : B_bra A
    | K_adj (A : AType) (b : K_ket A) : B_bra A
    | B_scale (s : S_scalar) (A : AType) (b : B_bra A) : B_bra A
    | B_add (A : AType) (b1 b2 : B_bra A) : B_bra A
    | B_apply (A1 A2 : AType) (b : B_bra A1) (o : O_opt A1 A2) : B_bra A2
    | B_ten (A1 A2 : AType) (b1 : B_bra A1) (b2 : B_bra A2) : B_bra (Apair A1 A2)
with O_opt : AType -> AType -> Type :=
    | O_var (n : oname) : O_opt (co n).1 (co n).2
    | O_0 (A1 A2 : AType) : O_opt A1 A2
    | O_1 (A : AType) : O_opt A A
    | KB_outer (A1 A2 : AType) (k : K_ket A1) (b : B_bra A2) : O_opt A1 A2
    | O_adj (A1 A2 : AType) (o : O_opt A1 A2) : O_opt A2 A1
    | O_scale (s : S_scalar) (A1 A2 : AType) (o : O_opt A1 A2) : O_opt A1 A2
    | O_add (A1 A2 : AType) (o1 o2 : O_opt A1 A2) : O_opt A1 A2
    | O_comp (A1 A2 A3 : AType) (o1 : O_opt A1 A2) (o2 : O_opt A2 A3) : O_opt A1 A3
    | O_ten (A1 A2 A3 A4 : AType) (o1 : O_opt A1 A2) (o2 : O_opt A3 A4) : O_opt (Apair A1 A3) (Apair A2 A4).
Arguments K_0 {A}.
Arguments B_0 {A}.
Arguments O_0 {A1 A2}.
Arguments O_1 {A}.

Scheme S_scalar_all_ind := Induction for S_scalar Sort Prop
  with K_ket_all_ind := Induction for K_ket Sort Prop
  with B_bra_all_ind := Induction for B_bra Sort Prop
  with O_opt_all_ind := Induction for O_opt Sort Prop.

Combined Scheme All_syn_mutind from 
  S_scalar_all_ind, K_ket_all_ind, B_bra_all_ind, O_opt_all_ind.

Variable (av : A_value) (sv : S_value) (kv : K_value) (bv : B_value) (ov : O_value).

Fixpoint A_sem {A : AType} (a : A_base A) : eval_AType A :=
  match a in A_base A return eval_AType A with
  | A_var n => av n
  | A_ground A a => a
  | A_pair A1 A2 a1 a2 => (A_sem a1, A_sem a2)
  (* | A_fst A1 A2 a => (A_sem a).1
  | A_snd A1 A2 a => (A_sem a).2 *)
  end.

Fixpoint S_sem (s : S_scalar) : C :=
  match s with
  | S_var n => sv n
  | S_0 => 0
  | S_1 => 1
  | S_delta A a1 a2 => (A_sem a1 ==  A_sem a2)%:R
  | S_add s1 s2 => S_sem s1 + S_sem s2
  | S_mul s1 s2 => S_sem s1 * S_sem s2
  | S_conj s => (S_sem s)^*
  | BK_inner A b k => [< (B_sem b)^*v ; K_sem k>]
  end
with K_sem (A : AType) (k : K_ket A): 'Ha A :=
  match k in K_ket A return 'Ha A with
  | K_var n => kv n
  | K_0 A => 0
  | K_ground A a => ''(A_sem a)
  | B_adj A b => (B_sem b)^*v
  | K_scale s A k => (S_sem s) *: (K_sem k)
  | K_add A k1 k2 => (K_sem k1) + (K_sem k2)
  | K_apply A1 A2 o k => (O_sem o) (K_sem k)
  | K_ten A1 A2 k1 k2 => (K_sem k1)  ⊗t (K_sem k2)
  end
with B_sem (A : AType) (b : B_bra A): 'Ha A :=
  match b in B_bra A return 'Ha A with
  | B_var n => bv n
  | B_0 A => 0
  | B_ground A a => ''(A_sem a)
  | K_adj A k => (K_sem k)^*v
  | B_scale s A b => (S_sem s) *: (B_sem b)
  | B_add A b1 b2 => (B_sem b1) + (B_sem b2)
  | B_apply A1 A2 b o => ((O_sem o)^T (B_sem b))
  | B_ten A1 A2 b1 b2 => (B_sem b1) ⊗t (B_sem b2)
  end
with O_sem (A1 A2 : AType) (o : O_opt A1 A2) : 'Hom{A2, A1} :=
  match o in O_opt A1 A2 return 'Hom{A2, A1} with
  | O_var n => ov n
  | O_0 A1 A2 => 0%:VF
  | O_1 A => \1
  | KB_outer A1 A2 k b => [> K_sem k ; (B_sem b)^*v <]
  | O_adj A1 A2 o => (O_sem o)^A
  | O_scale s A1 A2 o => (S_sem s) *: (O_sem o)
  | O_add A1 A2 o1 o2 => (O_sem o1) + (O_sem o2)
  | O_comp A1 A2 A3 o1 o2 => (O_sem o1) \o (O_sem o2)
  | O_ten A1 A2 A3 A4 o1 o2 => (O_sem o1) ⊗f (O_sem o2)
  end.

Notation "A * B" := (Apair A%TA B%TA) : atype_scope.
Notation "A '=a' B" := (A_sem A%DA = A_sem B%DA) (at level 70).
Notation "A '=s' B" := (S_sem A%DS = S_sem B%DS) (at level 70).
Notation "A '=k' B" := (K_sem A%DK = K_sem B%DK) (at level 70).
Notation "A '=b' B" := (B_sem A%DB = B_sem B%DB) (at level 70).
Notation "A '=o' B" := (O_sem A%DO = O_sem B%DO) (at level 70).
Notation "( a , b )" := (A_pair a b) : base_scope.
Notation "a + b" := (S_add a%DS b%DS) (at level 50, left associativity) : scalar_scope.
Notation "a + b" := (K_add a%DK b%DK) (at level 50, left associativity) : ket_scope.
Notation "a + b" := (B_add a%DB b%DB) (at level 50, left associativity) : bra_scope.
Notation "a + b" := (O_add a%DO b%DO) (at level 50, left associativity) : opt_scope.
Notation "c '*:' k" := (K_scale c%DS k%DK) (at level 40) : ket_scope.
Notation "c '*:' b" := (B_scale c%DS b%DB) (at level 40) : bra_scope.
Notation "c '*:' o" := (O_scale c%DS o%DO) (at level 40) : opt_scope.
Notation "a * b" := (S_mul a%DS b%DS) (at level 40, left associativity) : scalar_scope.
Notation "s '^*'" := (S_conj s%DS) (at level 2) : scalar_scope.
Notation "b '^A'" := (B_adj b%DB) (at level 8) : ket_scope.
Notation "k '^A'" := (K_adj k%DK) (at level 8) : bra_scope.
Notation "o '^A'" := (O_adj o%DO) (at level 8) : opt_scope.
Notation "b '·' k" := (BK_inner b%DB k%DK) (at level 40) : scalar_scope.
Notation "o '·' k" := (K_apply o%DO k%DK) (at level 40) : ket_scope.
Notation "b '·' o" := (B_apply b%DB o%DO) (at level 40) : bra_scope.
Notation "o1 '·' o2" := (O_comp o1%DO o2%DO) (at level 40) : opt_scope.
Notation "k '··' b" := (KB_outer k%DK b%DB) (at level 40) : opt_scope.
Notation "k1 ⊗ k2" := (K_ten k1%DK k2%DK) (at level 45) : ket_scope.
Notation "b1 ⊗ b2" := (B_ten b1%DB b2%DB) (at level 45) : bra_scope.
Notation "o1 ⊗ o2" := (O_ten o1%DO o2%DO) (at level 45) : opt_scope.
Notation "''|' a >" := (K_ground a%DA) : ket_scope.
Notation "''<' a |" := (B_ground a%DA) : bra_scope.
Notation "0" := (S_0) : scalar_scope.
Notation "1" := (S_1) : scalar_scope.
Notation "0" := K_0 : ket_scope.
Notation "'0_(' A )" := (@K_0 A%TA) (at level 8, format "0_( A )"): ket_scope.
Notation "0" := B_0 : bra_scope.
Notation "'0_(' A )" := (@B_0 A%TA) (at level 8, format "0_( A )"): bra_scope.
Notation "0" := O_0 : opt_scope.
Notation "'0_(' A1 , A2 )" := (@O_0 A1%TA A2%TA) (at level 8, format "0_( A1 , A2 )") : opt_scope.
Notation "1" := O_1 : opt_scope.
Notation "'1_(' A )" := (@O_1 A%TA) (at level 8, format "1_( A )") : opt_scope.
Notation "'δ(' a ',' b ')'" := (S_delta a%DA b%DA) (at level 30, format "'δ(' a ','  b ')'") : scalar_scope.
Notation "'`' n" := (A_var n) (at level 2, format "'`' n") : base_scope.
Notation "'`' n" := (S_var n) (at level 2, format "'`' n") : scalar_scope.
Notation "'`' n" := (K_var n) (at level 2, format "'`' n") : ket_scope.
Notation "'`' n" := (B_var n) (at level 2, format "'`' n") : bra_scope.
Notation "'`' n" := (O_var n) (at level 2, format "'`' n") : opt_scope.

Section Axiom_Sem_Consistent.
(* Axiomatic Semantics for core language is consistent with its semantics *)



(* AX-SCALAR *)
Lemma adds0 (S : S_scalar) :
  S + 0 =s S.
Proof. by rewrite /= addr0. Qed.
Lemma addsC (S1 S2 : S_scalar) :
  S1 + S2 =s S2 + S1.
Proof. by rewrite /= addrC. Qed.
Lemma addsA (S1 S2 S3 : S_scalar) :
  S1 + (S2 + S3) =s S1 + S2 + S3.
Proof. by rewrite /= addrA. Qed.
Lemma mul0s (S : S_scalar) :
  0 * S =s 0.
Proof. by rewrite /= mul0r. Qed.
Lemma mul1s (S : S_scalar) :
  1 * S =s S.
Proof. by rewrite /= mul1r. Qed.
Lemma mulsC (S1 S2 : S_scalar) :
  S1 * S2 =s S2 * S1.
Proof. by rewrite /= mulrC. Qed.
Lemma mulsA (S1 S2 S3 : S_scalar) :
  S1 * (S2 * S3) =s (S1 * S2) * S3.
Proof. by rewrite /= mulrA. Qed.
Lemma mulsDr (S S1 S2 : S_scalar) :
  S * (S1 + S2) =s S * S1 + S * S2.
Proof. by rewrite /= mulrDr. Qed.
Lemma mulsDl (S1 S2 S : S_scalar) :
  (S1 + S2) * S =s S1 * S + S2 * S.
Proof. by rewrite /= mulrDl. Qed.
Lemma conjs0 : 0 ^* =s 0.
Proof. by rewrite /= -conjC0. Qed.
Lemma conjs1 : 1 ^* =s 1.
Proof. by rewrite /= -conjC1. Qed.
Lemma conjsD S1 S2 : (S1 + S2) ^* =s S1 ^* + S2 ^*.
Proof. by rewrite /= rmorphD. Qed.
Lemma conjsM S1 S2 : (S1 * S2) ^* =s S2 ^* * S1 ^*.
Proof. by rewrite /= conjcM mulrC. Qed.
Lemma conjsK S : S ^* ^* =s S.
Proof. by rewrite /= conjCK. Qed.
Lemma adj_bk A (B : B_bra A) (K : K_ket A) : (B · K)^* =s K ^A · B ^A.
Proof. by rewrite /= conj_dotp conjvK. Qed.

(* AX-DELTA *)

Lemma conj_delta A (s t : A_base A) :
  δ(s,t)^* =s δ(s,t).
Proof. by rewrite /=; case: eqP; rewrite ?conjC1// conjC0. Qed.
Lemma compbk_ground A (s t : A_base A) : '<s| · '|t> =s δ(s,t).
Proof. by rewrite /= t2tv_conj t2tv_dot. Qed.
Lemma delta_eq A (s : A_base A) :
  δ(s,s) =s 1.
Proof. by rewrite /= eqxx. Qed.
Lemma delta_neq A (s t : A_base A) :
  ~ (s =a t) -> δ(s,t) =s 0.
Proof. by rewrite /==>/eqP/negPf->. Qed.
Lemma S_deltaC A (s t : A_base A) :
  δ(s, t) =s δ(t, s).
Proof. by rewrite/= eq_sym. Qed. 

(* AX-LINEAR *)

Lemma addk0 A (K : K_ket A) :
  K + 0 =k K.
Proof. by rewrite /= addr0. Qed.
Lemma addb0 A (B : B_bra A) :
  B + 0 =b B.
Proof. by rewrite /= addr0. Qed.
Lemma addo0 A1 A2 (O : O_opt A1 A2) :
  O + 0 =o O.
Proof. by rewrite /= addr0. Qed.

Lemma addkC A (K1 K2 : K_ket A) :
  K1 + K2 =k K2 + K1.
Proof. by rewrite /= addrC. Qed.
Lemma addbC A (B1 B2 : B_bra A) :
  B1 + B2 =b B2 + B1.
Proof. by rewrite /= addrC. Qed.
Lemma addoC A1 A2 (O1 O2 : O_opt A1 A2) :
  O1 + O2 =o O2 + O1.
Proof. by rewrite /= addrC. Qed.

Lemma addkA A (K1 K2 K3 : K_ket A) :
  K1 + (K2 + K3) =k K1 + K2 + K3.
Proof. by rewrite /= addrA. Qed.
Lemma addbA A (B1 B2 B3 : B_bra A) :
  B1 + (B2 + B3) =b B1 + B2 + B3.
Proof. by rewrite /= addrA. Qed.
Lemma addoA A1 A2 (O1 O2 O3 : O_opt A1 A2) :
  O1 + (O2 + O3) =o O1 + O2 + O3.
Proof. by rewrite /= addrA. Qed.

Lemma scale0k A (K : K_ket A) :
  0 *: K =k 0.
Proof. by rewrite /= scale0r. Qed.
Lemma scale0b A (B : B_bra A) :
  0 *: B =b 0.
Proof. by rewrite /= scale0r. Qed.
Lemma scale0o A1 A2 (O : O_opt A1 A2) :
  0 *: O =o 0.
Proof. by rewrite /= scale0r. Qed.

Lemma scalek0 (S : S_scalar) A :
  S *: 0 =k 0_(A).
Proof. by rewrite /= scaler0. Qed.
Lemma scaleb0 (S : S_scalar) A :
  S *: 0 =b 0_(A).
Proof. by rewrite /= scaler0. Qed.
Lemma scaleo0 (S : S_scalar) A1 A2 :
  S *: 0 =o 0_( A1, A2).
Proof. by rewrite /= scaler0. Qed.

Lemma scale1k A (K : K_ket A) :
  1 *: K =k K.
Proof. by rewrite /= scale1r. Qed.
Lemma scale1b A (B : B_bra A) :
  1 *: B =b B.
Proof. by rewrite /= scale1r. Qed.
Lemma scale1o A1 A2 (O : O_opt A1 A2) :
  1 *: O =o O.
Proof. by rewrite /= scale1r. Qed.

Lemma scalekA (S1 S2 : S_scalar) A (K : K_ket A) :
  S1 *: (S2 *: K) =k (S1 * S2) *: K.
Proof. by rewrite /= scalerA. Qed. 
Lemma scalebA (S1 S2 : S_scalar) A (B : B_bra A) :
  S1 *: (S2 *: B) =b (S1 * S2) *: B.
Proof. by rewrite /= scalerA. Qed. 
Lemma scaleoA (S1 S2 : S_scalar) A1 A2 (O : O_opt A1 A2) :
  S1 *: (S2 *: O) =o (S1 * S2) *: O.
Proof. by rewrite /= scalerA. Qed.

Lemma scalekDl (S1 S2 : S_scalar) A (K : K_ket A) :
  (S1 + S2) *: K =k S1 *: K + S2 *: K.
Proof. by rewrite /= scalerDl. Qed.
Lemma scalebDl (S1 S2 : S_scalar) A (B : B_bra A) :
  (S1 + S2) *: B =b S1 *: B + S2 *: B.
Proof. by rewrite /= scalerDl. Qed.
Lemma scaleoDl (S1 S2 : S_scalar) A1 A2 (O : O_opt A1 A2) :
  (S1 + S2) *: O =o S1 *: O + S2 *: O.
Proof. by rewrite /= scalerDl. Qed.

Lemma scalekDr (S : S_scalar) A (K1 K2 : K_ket A) :
  S *: (K1 + K2) =k S *: K1 + S *: K2.
Proof. by rewrite /= scalerDr. Qed.
Lemma scalebDr (S : S_scalar) A (B1 B2 : B_bra A) :
  S *: (B1 + B2) =b S *: B1 + S *: B2.
Proof. by rewrite /= scalerDr. Qed.
Lemma scaleoDr (S : S_scalar) A1 A2 (O1 O2 : O_opt A1 A2) :
  S *: (O1 + O2) =o S *: O1 + S *: O2.
Proof. by rewrite /= scalerDr. Qed.


(* AX-BILINEAR *)

Lemma compkb0 A1 A2 (K : K_ket A1) : K ·· 0_(A2) =o 0.
Proof. by rewrite /= conjv0 outp0. Qed.
Lemma compbk0 A (B : B_bra A) : B · 0 =s 0.
Proof. by rewrite /= dotp0. Qed.
Lemma compbo0 A1 A2 B : B · 0_(A1,A2) =b 0.
Proof. by rewrite /= linear0 lfunE. Qed.
Lemma compok0 A1 A2 (O : O_opt A1 A2) : O · 0 =k 0.
Proof. by rewrite /= linear0. Qed.
Lemma compoo0 A1 A2 A3 (O : O_opt A1 A2) : O · 0_(A2,A3) =o 0.
Proof. by rewrite /= comp_lfun0r. Qed.

Lemma compkbZr S A1 A2 (K : K_ket A1) (B : B_bra A2) :
  K ·· (S *: B) =o S *: (K ·· B).
Proof. by rewrite /= conjvZ outpZr conjCK. Qed.
Lemma compbkZr S A B (K : K_ket A) : 
  B · (S *: K) =s S * (B · K).
Proof. by rewrite /= dotpZr. Qed.
Lemma compboZr S A1 A2 B (O : O_opt A1 A2) : 
  B · (S *: O) =b S *: (B · O).
Proof. by rewrite /= trfZ lfunE. Qed.
Lemma compokZr S A1 A2 (O : O_opt A1 A2) K : 
  O · (S *: K) =k S *: (O · K).
Proof. by rewrite /= linearZ. Qed.
Lemma compooZr S A1 A2 A3 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) : 
  O1 · (S *: O2) =o S *: (O1 · O2).
Proof. by rewrite /= comp_lfunZr. Qed.

Lemma compkbDr A1 A2 (K : K_ket A1) (B1 B2 : B_bra A2) :
  K ·· (B1 + B2) =o K ·· B1 + K ·· B2.
Proof. by rewrite /= conjvD outpDr. Qed.
Lemma compbkDr A B (K1 K2 : K_ket A) : 
  B · (K1 + K2) =s B · K1 + B · K2.
Proof. by rewrite /= dotpDr. Qed.
Lemma compboDr A1 A2 B (O1 O2 : O_opt A1 A2) : 
  B · (O1 + O2) =b B · O1 + (B · O2).
Proof. by rewrite /= trfD lfunE. Qed.
Lemma compokDr A1 A2 (O : O_opt A1 A2) K1 K2 : 
  O · (K1 + K2) =k (O · K1) + (O · K2).
Proof. by rewrite /= linearD. Qed.
Lemma compooDr A1 A2 A3 (O : O_opt A1 A2) (O1 O2 : O_opt A2 A3) : 
  O · (O1 + O2) =o (O · O1) + (O · O2).
Proof. by rewrite /= comp_lfunDr. Qed.

Lemma comp0kb A1 A2 (B : B_bra A2) : 0_(A1) ·· B =o 0.
Proof. by rewrite /= out0p. Qed.
Lemma comp0bk A (K : K_ket A) : 0 · K =s 0.
Proof. by rewrite /= conjv0 dot0p. Qed.
Lemma comp0bo A1 A2 (O : O_opt A1 A2) : 0 · O =b 0.
Proof. by rewrite /= linear0. Qed.
Lemma comp0ok A1 A2 K : 0_(A1,A2) · K =k 0.
Proof. by rewrite /= lfunE. Qed.
Lemma comp0oo A1 A2 A3 (O : O_opt A2 A3) : 0_(A1,A2) · O =o 0.
Proof. by rewrite /= comp_lfun0l. Qed.


Lemma compkbZl S A1 A2 (K : K_ket A1) (B : B_bra A2) :
  (S *: K) ·· B =o S *: (K ·· B).
Proof. by rewrite /= outpZl. Qed.
Lemma compbkZl S A B (K : K_ket A) : 
  (S *: B) · K =s S * (B · K).
Proof. by rewrite /= conjvZ dotpZl conjCK. Qed.
Lemma compboZl S A1 A2 B (O : O_opt A1 A2) : 
  (S *: B) · O =b S *: (B · O).
Proof. by rewrite /= linearZ. Qed.
Lemma compokZl S A1 A2 (O : O_opt A1 A2) K : 
  (S *: O) · K =k S *: (O · K).
Proof. by rewrite /= lfunE. Qed.
Lemma compooZl S A1 A2 A3 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) : 
  (S *: O1) · O2 =o S *: (O1 · O2).
Proof. by rewrite /= comp_lfunZl. Qed.

Lemma compkbDl A1 A2 (K1 K2 : K_ket A1) (B : B_bra A2) :
  (K1 + K2) ·· B =o (K1 ·· B) + (K2 ·· B).
Proof. by rewrite /= outpDl. Qed.
Lemma compbkDl A B1 B2 (K : K_ket A) : 
  (B1 + B2) · K =s (B1 · K) + (B2 · K).
Proof. by rewrite /= conjvD dotpDl. Qed.
Lemma compboDl A1 A2 B1 B2 (O : O_opt A1 A2) : 
  (B1 + B2) · O =b (B1 · O) + (B2 · O).
Proof. by rewrite /= linearD. Qed.
Lemma compokDl A1 A2 (O1 O2 : O_opt A1 A2) K : 
  (O1 + O2) · K =k (O1 · K) + (O2 · K).
Proof. by rewrite /= lfunE. Qed.
Lemma compooDl A1 A2 A3 (O1 O2: O_opt A1 A2) (O : O_opt A2 A3) : 
  (O1 + O2) · O =o (O1 · O) + (O2 · O).
Proof. by rewrite /= comp_lfunDl. Qed.


Lemma tenk0 A1 A2 (K : K_ket A1) : K ⊗ 0_(A2) =k 0.
Proof. by rewrite /= linear0r. Qed.
Lemma tenb0 A1 A2 (B : B_bra A1) : B ⊗ 0_(A2) =b 0.
Proof. by rewrite /= linear0r. Qed.
Lemma teno0 A1 A2 A3 A4 (O : O_opt A1 A2) : O ⊗ 0_(A3,A4) =o 0.
Proof. by rewrite /= linear0r. Qed.

Lemma tenkZr S A1 A2 (K1 : K_ket A1) (K2 : K_ket A2) :
  K1 ⊗ (S *: K2) =k S *: (K1 ⊗ K2).
Proof. by rewrite /= linearZr. Qed.
Lemma tenbZr S A1 A2 (B1 : B_bra A1) (B2 : B_bra A2) :
  B1 ⊗ (S *: B2) =b S *: (B1 ⊗ B2).
Proof. by rewrite /= linearZr. Qed.
Lemma tenoZr S A1 A2 A3 A4 (O1 : O_opt A1 A2) (O2 : O_opt A3 A4) :
  O1 ⊗ (S *: O2) =o S *: (O1 ⊗ O2).
Proof. by rewrite /= linearZr. Qed.

Lemma tenkDr A1 A2 (K : K_ket A1) (K1 K2 : K_ket A2) :
  K ⊗ (K1 + K2) =k K ⊗ K1 + K ⊗ K2.
Proof. by rewrite /= linearDr. Qed.
Lemma tenbDr A1 A2 (B : B_bra A1) (B1 B2 : B_bra A2) :
  B ⊗ (B1 + B2) =b B ⊗ B1 + B ⊗ B2.
Proof. by rewrite /= linearDr. Qed.
Lemma tenoDr A1 A2 A3 A4 (O : O_opt A1 A2) (O1 O2 : O_opt A3 A4) :
  O ⊗ (O1 + O2) =o O ⊗ O1 + O ⊗ O2.
Proof. by rewrite /= linearDr. Qed.

Lemma ten0k A1 A2 (K : K_ket A2) : 0_(A1) ⊗ K =k 0.
Proof. by rewrite /= linear0l. Qed.
Lemma ten0b A1 A2 (B : B_bra A2) : 0_(A1) ⊗ B =b 0.
Proof. by rewrite /= linear0l. Qed.
Lemma ten0o A1 A2 A3 A4 (O : O_opt A3 A4) : 0_(A1,A2) ⊗ O =o 0.
Proof. by rewrite /= linear0l. Qed.

Lemma tenkZl S A1 A2 (K1 : K_ket A1) (K2 : K_ket A2) :
  (S *: K1) ⊗ K2 =k S *: (K1 ⊗ K2).
Proof. by rewrite /= linearZl. Qed.
Lemma tenbZl S A1 A2 (B1 : B_bra A1) (B2 : B_bra A2) :
  (S *: B1) ⊗ B2 =b S *: (B1 ⊗ B2).
Proof. by rewrite /= linearZl. Qed.
Lemma tenoZl S A1 A2 A3 A4 (O1 : O_opt A1 A2) (O2 : O_opt A3 A4) :
  (S *: O1) ⊗ O2 =o S *: (O1 ⊗ O2).
Proof. by rewrite /= linearZl. Qed.

Lemma tenkDl A1 A2 (K1 K2 : K_ket A1) (K : K_ket A2) :
  (K1 + K2) ⊗ K =k K1 ⊗ K + K2 ⊗ K.
Proof. by rewrite /= linearDl. Qed.
Lemma tenbDl A1 A2 (B1 B2 : B_bra A1) (B : B_bra A2) :
  (B1 + B2) ⊗ B =b B1 ⊗ B + B2 ⊗ B.
Proof. by rewrite /= linearDl. Qed.
Lemma tenoDl A1 A2 A3 A4 (O1 O2 : O_opt A1 A2) (O : O_opt A3 A4) :
  (O1 + O2) ⊗ O =o O1 ⊗ O + O2 ⊗ O.
Proof. by rewrite /= linearDl. Qed.



(* AX-ADJOINT *)
Lemma adjb0 A : 0 ^A =k 0_(A).
Proof. by rewrite /= conjv0. Qed.
Lemma adjk0 A : 0 ^A =b 0_(A).
Proof. by rewrite /= conjv0. Qed.
Lemma adjo0 A1 A2 : 0 ^A =o 0_(A1,A2).
Proof. by rewrite /= adjf0. Qed.

Lemma adjkK A (K : K_ket A) : K ^A ^A =k K.
Proof. by rewrite /= conjvK. Qed.
Lemma adjbK A (B : B_bra A) : B ^A ^A =b B.
Proof. by rewrite /= conjvK. Qed.
Lemma adjoK A1 A2 (O : O_opt A1 A2) : O ^A ^A =o O.
Proof. by rewrite /= adjfK. Qed.

Lemma scalek_adj S A (K : K_ket A) : (S *: K) ^A =b S ^* *: K ^A.
Proof. by rewrite /= conjvZ. Qed.
Lemma scaleb_adj S A (B : B_bra A) : (S *: B) ^A =k S ^* *: B ^A.
Proof. by rewrite /= conjvZ. Qed.
Lemma scaleo_adj S A1 A2 (O : O_opt A1 A2) : (S *: O) ^A =o S ^* *: O ^A.
Proof. by rewrite /= adjfZ. Qed.

Lemma adjkD A (K1 K2 : K_ket A) : (K1 + K2) ^A =b K1 ^A + K2 ^A.
Proof. by rewrite /= conjvD. Qed.
Lemma adjbD A (B1 B2 : B_bra A) : (B1 + B2) ^A =k B1 ^A + B2 ^A.
Proof. by rewrite /= conjvD. Qed.
Lemma adjoD A1 A2 (O1 O2 : O_opt A1 A2) : (O1 + O2) ^A =o O1 ^A + O2 ^A.
Proof. by rewrite /= adjfD. Qed.  

Lemma adj_kb A (K : K_ket A) (B : B_bra A) : (K ·· B) ^A =o B ^A ·· K ^A.
Proof. by rewrite /= adj_outp conjvK. Qed.
Lemma adj_ok A1 A2 (O : O_opt A1 A2) (K : K_ket A2) :
  (O · K) ^A =b K ^A · O ^A.
Proof. by rewrite /= -conjfAT conjfE conjvK. Qed.
Lemma adj_bo A1 A2 (B : B_bra A1) (O : O_opt A1 A2) :
  (B · O) ^A =k O ^A · B ^A.
Proof. by rewrite /= adjfTC conjfE conjvK. Qed.
Lemma adj_oo A1 A2 A3 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) :
  (O1 · O2) ^A =o O2 ^A · O1 ^A.
Proof. by rewrite /= adjf_comp. Qed.

Lemma adj_tenk A1 A2 (K1 : K_ket A1) (K2 : K_ket A2) :
(K1 ⊗ K2) ^A =b K1 ^A ⊗ K2 ^A.
Proof. by rewrite /= tentv_conj. Qed.
Lemma adj_tenb A1 A2 (B1 : B_bra A1) (B2 : B_bra A2) :
(B1 ⊗ B2) ^A =k B1 ^A ⊗ B2 ^A.
Proof. by rewrite /= tentv_conj. Qed.
Lemma adj_teno A1 A2 A3 A4 (O1 : O_opt A1 A2) (O2 : O_opt A3 A4) :
(O1 ⊗ O2) ^A =o O1 ^A ⊗ O2 ^A.
Proof. by rewrite /= tentf_adj. Qed.



(* AX-COMPOSITION *)

Lemma compbokA A1 A2 B (O : O_opt A1 A2) K :
  B · (O · K) =s (B · O) · K.
Proof. by rewrite /= trfAC conjfE conjvK adj_dotEl. Qed.
Lemma compbooA A1 A2 A3 B (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) :
  (B · O1) · O2 =b B · (O1 · O2).
Proof. by rewrite /= trf_comp lfunE. Qed.
Lemma compookA A1 A2 A3 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) K :
  O1 · (O2 · K) =k (O1 · O2) · K.
Proof. by rewrite /= lfunE. Qed.
Lemma compoooA A1 A2 A3 A4 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) (O3 : O_opt A3 A4) :
  O1 · (O2 · O3) =o (O1 · O2) · O3.
Proof. by rewrite /= comp_lfunA. Qed.

Lemma compTbk A1 A2 (B1 : B_bra A1) (B2 : B_bra A2) K1 K2 :
  (B1 ⊗ B2) · (K1 ⊗ K2) =s (B1 · K1) * (B2 · K2).
Proof. by rewrite /= tentv_conj tentv_dot. Qed.
Lemma compTok A1 A2 A3 A4 (O1 : O_opt A1 A2) (O2 : O_opt A3 A4) K1 K2 :
  (O1 ⊗ O2) · (K1 ⊗ K2) =k (O1 · K1) ⊗ (O2 · K2).
Proof. by rewrite /= tentf_apply. Qed.
Lemma compTbo A1 A2 A3 A4 B1 B2 (O1 : O_opt A1 A2) (O2 : O_opt A3 A4) :
  (B1 ⊗ B2) · (O1 ⊗ O2) =b (B1 · O1) ⊗ (B2 · O2).
Proof. by rewrite /= tentf_tr tentf_apply. Qed.
Lemma compToo A1 A2 A3 A4 A5 A6 (O1 : O_opt A1 A2) (O2 : O_opt A4 A5) 
  (O3 : O_opt A2 A3) (O4 : O_opt A5 A6) :
  (O1 ⊗ O2) · (O3 ⊗ O4) =o (O1 · O3) ⊗ (O2 · O4).
Proof. by rewrite /= tentf_comp. Qed.
Lemma compTkb A1 A2 A3 A4 (K1 : K_ket A1) (K2 : K_ket A2) (B1 : B_bra A3) (B2 : B_bra A4) :
  (K1 ·· B1) ⊗ (K2 ·· B2) =o (K1 ⊗ K2) ·· (B1 ⊗ B2).
Proof. by rewrite /= tentv_out tentv_conj. Qed.


Lemma compkbkA A1 A2 (K1 : K_ket A1) (B : B_bra A2) K2 :
  (K1 ·· B) · K2 =k (B · K2) *: K1.
Proof. by rewrite /= outpE. Qed. 
Lemma compbkbA A1 A2 (B1 : B_bra A1) K (B2 : B_bra A2) :
  B1 · (K ·· B2) =b (B1 · K) *: B2.
Proof. by rewrite /= tr_outp outpE conjvK conjv_dotl. Qed.
Lemma compkboA A1 A2 A3 (K : K_ket A1) B (O : O_opt A2 A3) :
  K ·· (B · O) =o K ·· B · O.
Proof. by rewrite /= outp_compl adjfTC conjfE conjvK. Qed.
Lemma compokbA A1 A2 A3 (O : O_opt A1 A2) K (B : B_bra A3) :
  (O · K) ·· B =o O · (K ·· B).
Proof. by rewrite /= outp_compr. Qed.
Lemma tenkb A1 A2 A3 A4 (K1 : K_ket A1) (B1 : B_bra A2) (K2 : K_ket A3) (B2 : B_bra A4) :
  (K1 ·· B1) ⊗ (K2 ·· B2) =o (K1 ⊗ K2) ·· (B1 ⊗ B2).
Proof. by rewrite /= tentv_out tentv_conj. Qed.


(* AX-GROUND *)

Lemma adjo1 A : 1 ^A =o 1_(A).
Proof. by rewrite /= adjf1. Qed.

Lemma comp1ok A (K : K_ket A) : 1 · K =k K.
Proof. by rewrite /= lfunE. Qed.
Lemma comp1oo A1 A2 (O : O_opt A1 A2) : 1 · O =o O.
Proof. by rewrite /= comp_lfun1l. Qed.

Lemma ten11 A1 A2 : (@O_1 A1) ⊗ (@O_1 A2) =o 1.
Proof. by rewrite /= tentf11. Qed.

Lemma adjk_ground A (a : A_base A) : '|a> ^A =b '<a|.
Proof. by rewrite /= t2tv_conj. Qed.

Lemma tenk_ground A1 A2 (a1 : A_base A1) (a2 : A_base A2) :
  '|a1> ⊗ '|a2> =k '|(a1, a2)>.
Proof. by rewrite /= tentv_t2tv. Qed.  



(* 

Lemma delta_bigE I (r : seq I) (P : pred I) (Ai : I -> AType) 
  (s t : forall i, A_base (Ai i)) :
  S_sem (\big[ S_mul / 1%DS]_(i <- r | P i) (δ(s i, t i))%DS) = 
  (\big[andb/true]_(i <- r | P i) (A_sem (s i) == A_sem (t i)))%:R.
Proof.
elim: r=>[|a l IH]; first by rewrite !big_nil.  
by rewrite !big_cons; case: (P a)=>//=; rewrite IH -mulnb natrM.
Qed.

Lemma delta_big I (r : seq I) (P : pred I) (Ai1 Ai2 : I -> AType) 
  (s1 t1 : forall i, A_base (Ai1 i)) (s2 t2 : forall i, A_base (Ai2 i)) :
  \big[andb/true]_(i <- r | P i) (A_sem (s1 i) == A_sem (t1 i)) = 
    \big[andb/true]_(i <- r | P i) (A_sem (s2 i) == A_sem (t2 i)) ->
  \big[ S_mul / 1%DS]_(i <- r | P i) (δ(s1 i, t1 i)) =s 
    \big[ S_mul / 1%DS]_(i <- r | P i) (δ(s2 i, t2 i)).
Proof. by move=>IH; rewrite !delta_bigE IH. Qed. 
  
*)



End Axiom_Sem_Consistent.

Section Term_Rewriting_System.

(* AC symbols : associativity & commutativity *)
Lemma S_addA (S1 S2 S3 : S_scalar) :
  S1 + (S2 + S3) =s S1 + S2 + S3.
Proof. by rewrite/= addrA. Qed.
Lemma S_addC (S1 S2 : S_scalar) :
  S1 + S2 =s S2 + S1.
Proof. by rewrite/= addrC. Qed.

Lemma S_mulA (S1 S2 S3 : S_scalar) :
  S1 * (S2 * S3) =s S1 * S2 * S3.
Proof. by rewrite/= mulrA. Qed.
Lemma S_mulC (S1 S2 : S_scalar) :
  S1 * S2 =s S2 * S1.
Proof. by rewrite/= mulrC. Qed.

Lemma K_addA A (K1 K2 K3 : K_ket A) :
  K1 + (K2 + K3) =k K1 + K2 + K3.
Proof. by rewrite/= addrA. Qed.
Lemma K_addC A (K1 K2 : K_ket A) :
  K1 + K2 =k K2 + K1.
Proof. by rewrite/= addrC. Qed.

Lemma B_addA A (B1 B2 B3 : B_bra A) :
  B1 + (B2 + B3) =b B1 + B2 + B3.
Proof. by rewrite/= addrA. Qed.
Lemma B_addC A (B1 B2 : B_bra A) :
  B1 + B2 =b B2 + B1.
Proof. by rewrite/= addrC. Qed.

Lemma O_addA A1 A2 (O1 O2 O3 : O_opt A1 A2) :
  O1 + (O2 + O3) =o O1 + O2 + O3.
Proof. by rewrite/= addrA. Qed.
Lemma O_addC A1 A2 (O1 O2 : O_opt A1 A2) :
  O1 + O2 =o O2 + O1.
Proof. by rewrite/= addrC. Qed.



(* R-SCALAR *)
Lemma R_SCALAR_1 (S : S_scalar) :
  0 + S =s S.
Proof. by rewrite/= add0r. Qed.
Lemma R_SCALAR_2 (S : S_scalar) :
  0 * S =s 0.
Proof. by rewrite/= mul0r. Qed.
Lemma R_SCALAR_3 (S : S_scalar) :
  1 * S =s S.
Proof. by rewrite/= mul1r. Qed.
Lemma R_SCALAR_4 (S1 S2 S3 : S_scalar) :
  S1 * (S2 + S3) =s S1 * S2 + S1 * S3.
Proof. by rewrite/= mulrDr. Qed.
Lemma R_SCALAR_5 :
  0^* =s 0.
Proof. by rewrite /= -conjC0. Qed.
Lemma R_SCALAR_6 :
  1^* =s 1.
Proof. by rewrite /= -conjC1. Qed.
Lemma R_SCALAR_7 (S1 S2 : S_scalar) :
  (S1 + S2)^* =s S1^* + S2^*.
Proof. by rewrite/= rmorphD. Qed.
Lemma R_SCALAR_8 (S1 S2 : S_scalar) :
  (S1 * S2)^* =s S1^* * S2^*.
Proof. by rewrite/= rmorphM. Qed.
Lemma R_SCALAR_9 (S : S_scalar) :
  (S^*)^* =s S.
Proof. by rewrite/= conjCK. Qed.

(* R-S-DELTA *)
Lemma R_S_DELTA_1 A (s : A_base A) : δ(s,s) =s 1.
Proof. by rewrite /= eqxx. Qed.
Lemma R_S_DELTA_2 A1 A2 (s1 t1 : A_base A1) (s2 t2 : A_base A2) :
  δ((s1, s2), (t1, t2)) =s δ(s1, t1) * δ(s2, t2).
Proof. by rewrite /= -pair_eqE/= -natrM mulnb. Qed. 

(* R-KET-SCR *)
Lemma R_KET_SCR_1 A (K : K_ket A) :
  0 *: K =k 0_(A).
Proof. by rewrite/= scale0r. Qed.
Lemma R_KET_SCR_2 A (K : K_ket A) :
  1 *: K =k K. 
Proof. by rewrite/= scale1r. Qed.
Lemma R_KET_SCR_3 A (S : S_scalar) :
  S *: 0_(A) =k 0_(A).
Proof. by rewrite/= scaler0. Qed.
Lemma R_KET_SCR_4 A (S1 S2 : S_scalar) (K : K_ket A) :
  S1 *: (S2 *: K) =k (S1 * S2) *: K.
Proof. by rewrite/= scalerA. Qed.
Lemma R_KET_SCR_5 A (S : S_scalar) (K1 K2 : K_ket A) :
  S *: (K1 + K2) =k S *: K1 + S *: K2.
Proof. by rewrite/= scalerDr. Qed.

(* R-KET-ADD *)
Lemma R_KET_ADD_1 A (K : K_ket A) :
  K + 0_(A) =k K.
Proof. by rewrite/= addr0. Qed.
Lemma R_KET_ADD_2 A (K : K_ket A) :
  K + K =k (1 + 1) *: K.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma R_KET_ADD_3 A (S : S_scalar) (K : K_ket A) :
  S *: K + K =k (S + 1) *: K.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma R_KET_ADD_4 A (S1 S2 : S_scalar) (K : K_ket A) :
  S1 *: K + S2 *: K =k (S1 + S2) *: K.
Proof. by rewrite/= scalerDl. Qed.

(* R-OP-SCR *)
Lemma  R_OP_SCR_1 A1 A2 (O : O_opt A1 A2) :
  0 *: O =o 0_(A1,A2).
Proof. by rewrite/= scale0r. Qed.
Lemma  R_OP_SCR_2 A1 A2 (O : O_opt A1 A2) :
  1 *: O =o O.
Proof. by rewrite/= scale1r. Qed.
Lemma  R_OP_SCR_3 A1 A2 (S : S_scalar) :
  S *: 0_(A1,A2) =o 0_(A1,A2).
Proof. by rewrite/= scaler0. Qed.
Lemma  R_OP_SCR_4 A1 A2 (S1 S2 : S_scalar) (O : O_opt A1 A2) :
  S1 *: (S2 *: O) =o (S1 * S2) *: O.
Proof. by rewrite/= scalerA. Qed.
Lemma  R_OP_SCR_5 A1 A2 (S : S_scalar) (O1 O2 : O_opt A1 A2) :
  S *: (O1 + O2) =o S *: O1 + S *: O2.
Proof. by rewrite/= scalerDr. Qed.

(* R-OP-ADD *)
Lemma R_OP_ADD_1 A1 A2 (O : O_opt A1 A2) :
  O + 0_(A1,A2) =o O.
Proof. by rewrite/= addr0. Qed.
Lemma R_OP_ADD_2 A1 A2 (O : O_opt A1 A2) :
  O + O =o (1+1) *: O.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma R_OP_ADD_3 A1 A2 (S : S_scalar) (O : O_opt A1 A2) :
  S *: O + O =o (S + 1) *: O.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma R_OP_ADD_4 A1 A2 (S1 S2 : S_scalar) (O : O_opt A1 A2) :
  S1 *: O + S2 *: O =o (S1 + S2) *: O.
Proof. by rewrite/= scalerDl. Qed.

(* R-KET-TSR *)
Lemma R_KET_TSR_1 A1 A2 (K : K_ket A2) :
  0_(A1) ⊗ K =k 0_(A1 * A2).
Proof. by rewrite/= ten0tv. Qed.
Lemma R_KET_TSR_2 A1 A2 (K : K_ket A1) :
  K ⊗ 0_(A2) =k 0_(A1 * A2).
Proof. by rewrite/= tentv0. Qed.
Lemma R_KET_TSR_3 A1 A2 (s : A_base A1) (t : A_base A2) :
  '|s> ⊗ '|t> =k '|(s, t)>.
Proof. by rewrite/= tentv_t2tv. Qed.
Lemma R_KET_TSR_4 A1 A2 S (K1 : K_ket A1) (K2 : K_ket A2) :
  S *: K1 ⊗ K2 =k S *: (K1 ⊗ K2).
Proof. by rewrite/= tentvZl. Qed.
Lemma R_KET_TSR_5 A1 A2 S (K1 : K_ket A1) (K2 : K_ket A2) :
  K1 ⊗ S *: K2 =k S *: (K1 ⊗ K2).
Proof. by rewrite/= tentvZr. Qed.
Lemma R_KET_TSR_6 A1 A2 (K1 K2 : K_ket A1) (K3 : K_ket A2) :
  (K1 + K2) ⊗ K3 =k K1 ⊗ K3 + K2 ⊗ K3.
Proof. by rewrite/= tentvDl. Qed.
Lemma R_KET_TSR_7 A1 A2 (K1 : K_ket A1) (K2 K3 : K_ket A2) :
  K1 ⊗ (K2 + K3) =k K1 ⊗ K2 + K1 ⊗ K3.
Proof. by rewrite/= tentvDr. Qed.

(* R-OP-OUTER *)
Lemma R_OP_OUTER_1 A1 A2 (B : B_bra A2) :
  0_(A1) ·· B =o 0_(A1,A2).
Proof. by rewrite/= out0p. Qed.
Lemma R_OP_OUTER_2 A1 A2 (K : K_ket A1) :
  K ·· 0_(A2) =o 0_(A1,A2).
Proof. by rewrite/= conjv0 outp0. Qed.
Lemma R_OP_OUTER_3 A1 A2 (S : S_scalar) (K : K_ket A1) (B : B_bra A2) :
  (S *: K) ·· B =o S *: (K ·· B).
Proof. by rewrite/= outpZl. Qed.
Lemma R_OP_OUTER_4 A1 A2 (S : S_scalar) (K : K_ket A1) (B : B_bra A2) :
  K ·· (S *: B) =o S *: (K ·· B).
Proof. by rewrite/= conjvZ outpZr conjCK. Qed.
Lemma R_OP_OUTER_5 A1 A2 (K1 K2 : K_ket A1) (B : B_bra A2) :
  (K1 + K2) ·· B =o K1 ·· B + K2 ·· B.
Proof. by rewrite/= outpDl. Qed.
Lemma R_OP_OUTER_6 A1 A2 (K : K_ket A1) (B1 B2 : B_bra A2) :
  K ·· (B1 + B2) =o K ·· B1 + K ·· B2.
Proof. by rewrite/= conjvD outpDr. Qed.

(* R-OP-TSR *)
Lemma R_OP_TSR_1 A1 A2 A3 A4 (O : O_opt A3 A4) :
  0_(A1,A2) ⊗ O =o 0_(A1 * A3, A2 * A4).
Proof. by rewrite/= ten0tf. Qed.
Lemma R_OP_TSR_2 A1 A2 A3 A4 (O : O_opt A1 A2) :
  O ⊗ 0_(A3,A4) =o 0_(A1 * A3, A2 * A4).
Proof. by rewrite/= tentf0. Qed.
Lemma R_OP_TSR_3 A1 A2 :
  1_(A1) ⊗ 1_(A2) =o 1_(A1 * A2).
Proof. by rewrite/= tentf11. Qed.
Lemma R_OP_TSR_4 A1 A2 A3 A4 (K1 : K_ket A1) (B1 : B_bra A2) (K2 : K_ket A3) (B2 : B_bra A4) :
  K1 ·· B1 ⊗ K2 ·· B2 =o (K1 ⊗ K2) ·· (B1 ⊗ B2).
Proof. by rewrite/= tentv_out tentv_conj. Qed.
Lemma R_OP_TSR_5 A1 A2 A3 A4 (S : S_scalar) (O1 : O_opt A1 A2) (O2 : O_opt A3 A4) :
  S *: O1 ⊗ O2 =o S *: (O1 ⊗ O2).
Proof. by rewrite/= tentfZl. Qed.
Lemma R_OP_TSR_6 A1 A2 A3 A4 (S : S_scalar) (O1 : O_opt A1 A2) (O2 : O_opt A3 A4) :
  O1 ⊗ S *: O2 =o S *: (O1 ⊗ O2).
Proof. by rewrite/= tentfZr. Qed.
Lemma R_OP_TSR_7 A1 A2 A3 A4 (O1 O2 : O_opt A1 A2) (O3 : O_opt A3 A4) :
  (O1 + O2) ⊗ O3 =o O1 ⊗ O3 + O2 ⊗ O3.
Proof. by rewrite/= tentfDl. Qed.
Lemma R_OP_TSR_8 A1 A2 A3 A4 (O1 : O_opt A1 A2) (O2 O3 : O_opt A3 A4) :
  O1 ⊗ (O2 + O3) =o O1 ⊗ O2 + O1 ⊗ O3.
Proof. by rewrite/= tentfDr. Qed.

(* R-S-CONJ : TODO rename *)
Lemma R_S_CONJ_2 A (s a : A_base A) :
  δ(s, a)^* =s δ(s, a).
Proof. by rewrite/= conjC_nat. Qed.
Lemma R_S_CONJ_6 A (B : B_bra A) (K : K_ket A) :
  (B · K)^* =s K^A · B^A.
Proof. by rewrite/= conj_dotp conjvK. Qed.

(* R-S-DOT *)
Lemma R_S_DOT_1 A (K : K_ket A) :
  0_(A) · K =s 0.
Proof. by rewrite/= conjv0 dot0p. Qed.
Lemma R_S_DOT_2 A (B : B_bra A) :
  B · 0_(A) =s 0.
Proof. by rewrite/= dotp0. Qed.
Lemma R_S_DOT_3 A (S : S_scalar) (B : B_bra A) (K : K_ket A) :
  (S *: B) · K =s S * (B · K).
Proof. by rewrite/= conjvZ dotpZl conjCK. Qed.
Lemma R_S_DOT_4 A (S : S_scalar) (B : B_bra A) (K : K_ket A) :
  B · (S *: K) =s S * (B · K).
Proof. by rewrite/= dotpZr. Qed.
Lemma R_S_DOT_5 A (B1 B2 : B_bra A) (K : K_ket A) :
  (B1 + B2) · K =s B1 · K + B2 · K.
Proof. by rewrite/= conjvD dotpDl. Qed.
Lemma R_S_DOT_6 A (B : B_bra A) (K1 K2 : K_ket A) :
  B · (K1 + K2) =s B · K1 + B · K2.
Proof. by rewrite/= dotpDr. Qed.


Lemma R_S_DOT_8 A1 A2 (B1 : B_bra A1) (B2 : B_bra A2) (s : A_base A1) (t : A_base A2) :
  (B1 ⊗ B2) · '|(s, t)> =s B1 · '|s> * (B2 · '|t>).
Proof. by rewrite/= tentv_conj -tentv_dot tentv_t2tv. Qed.
Lemma R_S_DOT_9 A1 A2 (s : A_base A1) (t : A_base A2) (K1 : K_ket A1) (K2 : K_ket A2) :
  '<(s, t)| · (K1 ⊗ K2) =s '<s| · K1 * ('<t| · K2).
Proof. by rewrite/= -tentv_dot -tentv_conj tentv_t2tv. Qed.
Lemma R_S_DOT_10 A1 A2 (B1 : B_bra A1) (B2 : B_bra A2) (K1 : K_ket A1) (K2 : K_ket A2) :
  (B1 ⊗ B2) · (K1 ⊗ K2) =s B1 · K1 * (B2 · K2).
Proof. by rewrite/= -tentv_dot -tentv_conj. Qed.

(* R-S-SORT *)
Lemma R_S_SORT_1 A1 A2 (B : B_bra A1) (O : O_opt A1 A2) (K : K_ket A2) :
  (B · O) · K =s B · (O · K).
Proof. by rewrite/= trfAC conjfE conjvK adj_dotEl. Qed.
Lemma R_S_SORT_2 A1 A2 A3 A4 (s : A_base A1) (t : A_base A2) (O1 : O_opt A1 A3) 
  (O2 : O_opt A2 A4) (K : K_ket (Apair A3 A4)) :
    '<(s, t)| · ((O1 ⊗ O2) · K) =s ('<s| · O1 ⊗ '<t| · O2) · K.
Proof.
rewrite -R_S_SORT_1/=; do 2 f_equal.
by rewrite -tentf_apply tentv_t2tv tentf_tr.
Qed.
Lemma R_S_SORT_3 A1 A2 A3 A4 (B1 : B_bra A1) (B2 : B_bra A2) (O1 : O_opt A1 A3) 
  (O2 : O_opt A2 A4) (K : K_ket (Apair A3 A4)) :
    (B1 ⊗ B2) · ((O1 ⊗ O2) · K) =s (B1 · O1 ⊗ B2 · O2) · K.
Proof.
rewrite -R_S_SORT_1/=; do 2 f_equal.
by rewrite tentf_tr tentf_apply.
Qed.

(* R-KET-ADJ *)
Lemma R_KET_ADJ_1 A :
  0_(A)^A =k 0_(A).
Proof. by rewrite/= conjv0. Qed.
Lemma R_KET_ADJ_2 A (t : A_base A) :
  '<t|^A =k '|t>.
Proof. by rewrite/= t2tv_conj. Qed.
Lemma R_KET_ADJ_3 A (K : K_ket A) :
  (K^A)^A =k K.
Proof. by rewrite/= conjvK. Qed.
Lemma R_KET_ADJ_4 A (S : S_scalar) (B : B_bra A) :
  (S *: B)^A =k S^* *: B^A.
Proof. by rewrite/= conjvZ. Qed.
Lemma R_KET_ADJ_5 A (B1 B2 : B_bra A) :
  (B1 + B2)^A =k B1^A + B2^A.
Proof. by rewrite/= conjvD. Qed.
Lemma R_KET_ADJ_6 A1 A2 (B : B_bra A1) (O : O_opt A1 A2) :
  (B · O)^A =k O^A · B^A.
Proof. by rewrite/= trfAC conjfE conjvK. Qed.
Lemma R_KET_ADJ_7 A1 A2 (B1 : B_bra A1) (B2 : B_bra A2) :
  (B1 ⊗ B2)^A =k B1^A ⊗ B2^A.
Proof. by rewrite /= tentv_conj. Qed.

(* KET-MLT *)
Lemma R_KET_MLT_1 A1 A2 (K : K_ket A2) :
  0_(A1,A2) · K =k 0_(A1).
Proof. by rewrite/= lfunE. Qed.
Lemma R_KET_MLT_2 A1 A2 (O : O_opt A1 A2) :
  O · 0_(A2) =k 0_(A1).
Proof. by rewrite/= linear0. Qed.
Lemma R_KET_MLT_3 A (K : K_ket A) :
  1_(A) · K =k K.
Proof. by rewrite/= lfunE. Qed.
Lemma R_KET_MLT_4 A1 A2 (S : S_scalar) (O : O_opt A1 A2) (K : K_ket A2) :
  (S *: O) · K =k S *: (O · K).
Proof. by rewrite/= lfunE. Qed.
Lemma R_KET_MLT_5 A1 A2 (S : S_scalar) (O : O_opt A1 A2) (K : K_ket A2) :
  O · (S *: K) =k S *: (O · K).
Proof. by rewrite/= linearZ. Qed.
Lemma R_KET_MLT_6 A1 A2 (O1 O2 : O_opt A1 A2) (K : K_ket A2) :
  (O1 + O2) · K =k O1 · K + O2 · K.
Proof. by rewrite/= lfunE. Qed.
Lemma R_KET_MLT_7 A1 A2 (O : O_opt A1 A2) (K1 K2 : K_ket A2) :
  O · (K1 + K2) =k O · K1 + O · K2.
Proof. by rewrite/= linearD. Qed.
Lemma R_KET_MLT_8 A1 A2 (K1 : K_ket A1) (B : B_bra A2) (K2 : K_ket A2) :
  (K1 ·· B) · K2 =k (B · K2) *: K1.
Proof. by rewrite/= outpE. Qed.
Lemma R_KET_MLT_9 A1 A2 A3 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) (K : K_ket A3) :
  (O1 · O2) · K =k O1 · (O2 · K).
Proof. by rewrite/= lfunE. Qed.
Lemma R_KET_MLT_10 A1 A2 A3 A1' A2' A3' (O1 : O_opt A1 A2) (O1' : O_opt A2 A3) 
  (O2 : O_opt A1' A2') (O2' : O_opt A2' A3') (K : K_ket (Apair A3 A3')) :
    (O1 ⊗ O2) · ((O1' ⊗ O2') · K) =k (O1 · O1' ⊗ O2 · O2') · K.
Proof. by rewrite/= -tentf_comp lfunE. Qed.
Lemma R_KET_MLT_11 A1 A2 A3 A4 (O1 : O_opt A1 A3) (O2 : O_opt A2 A4) (s : A_base A3) (t : A_base A4) :
  (O1 ⊗ O2) · '|(s, t)> =k O1 · '|s> ⊗ O2 · '|t>.
Proof. by rewrite/= -tentf_apply tentv_t2tv. Qed.
Lemma R_KET_MLT_12 A1 A2 A3 A4 (O1 : O_opt A1 A3) (O2 : O_opt A2 A4) 
  (K1 : K_ket A3) (K2 : K_ket A4) :
    (O1 ⊗ O2) · (K1 ⊗ K2) =k O1 · K1 ⊗ O2 · K2.
Proof. by rewrite/= tentf_apply. Qed.

(* R-BRA-ADJ *)
Lemma R_BRA_ADJ_1 A :
  0_(A)^A =b 0_(A).
Proof. by rewrite/= conjv0. Qed.
Lemma R_BRA_ADJ_2 A (t : A_base A) :
  '|t>^A =b '<t|.
Proof. by rewrite/= t2tv_conj. Qed.
Lemma R_BRA_ADJ_3 A (B : B_bra A) :
  (B^A)^A =b B.
Proof. by rewrite/= conjvK. Qed.
Lemma R_BRA_ADJ_4 A (S : S_scalar) (K : K_ket A) :
  (S *: K)^A =b S^* *: K^A.
Proof. by rewrite/= conjvZ. Qed.
Lemma R_BRA_ADJ_5 A (K1 K2 : K_ket A) :
  (K1 + K2)^A =b K1^A + K2^A.
Proof. by rewrite/= conjvD. Qed.
Lemma R_BRA_ADJ_6 A1 A2 (O : O_opt A1 A2) (K : K_ket A2) :
  (O · K)^A =b K^A · O^A.
Proof. by rewrite/= trfAC conjfE conjvK adjfK. Qed.
Lemma R_BRA_ADJ_7 A1 A2 (K1 : K_ket A1) (K2 : K_ket A2) :
  (K1 ⊗ K2)^A =b K1^A ⊗ K2^A.
Proof. by rewrite /= tentv_conj. Qed.

(* BRA-MLT *)
Lemma R_BRA_MLT_1 A1 A2 (B : B_bra A1) :
  B · 0_(A1,A2) =b 0_(A2).
Proof. by rewrite/= trf0 lfunE. Qed.
Lemma R_BRA_MLT_2 A1 A2 (O : O_opt A1 A2) :
  0_(A1) · O =b 0_(A2).
Proof. by rewrite/= linear0. Qed.
Lemma R_BRA_MLT_3 A (B : B_bra A) :
  B · 1_(A) =b B.
Proof. by rewrite/= trf1 lfunE. Qed.
Lemma R_BRA_MLT_4 A1 A2 (S : S_scalar) (B : B_bra A1) (O : O_opt A1 A2) :
  B · (S *: O) =b S *: (B · O).
Proof. by rewrite/= trfZ lfunE. Qed.
Lemma R_BRA_MLT_5 A1 A2 (S : S_scalar) (B : B_bra A1) (O : O_opt A1 A2) :
  (S *: B) · O =b S *: (B · O).
Proof. by rewrite/= linearZ. Qed.
Lemma R_BRA_MLT_6 A1 A2 (B : B_bra A1) (O1 O2 : O_opt A1 A2) :
  B · (O1 + O2) =b B · O1 + B · O2.
Proof. by rewrite/= trfD lfunE. Qed.
Lemma R_BRA_MLT_7 A1 A2 (B1 B2 : B_bra A1) (O : O_opt A1 A2) :
  (B1 + B2) · O  =b B1 · O + B2 · O.
Proof. by rewrite/= linearD. Qed.
Lemma R_BRA_MLT_8 A1 A2 (B1 : B_bra A1) (K : K_ket A1) (B2 : B_bra A2) :
  B1 · (K ·· B2) =b (B1 · K) *: B2.
Proof. by rewrite/= trfAC adj_outp conjfE outpE conjvZ conjvK conj_dotp. Qed.
Lemma R_BRA_MLT_9 A1 A2 A3 (B : B_bra A1) (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) :
  B · (O1 · O2) =b (B · O1) · O2.
Proof. by rewrite/= trf_comp lfunE. Qed.
Lemma R_BRA_MLT_10 A1 A2 A3 A1' A2' A3' (B : B_bra (Apair A1 A1')) (O1 : O_opt A1 A2) (O1' : O_opt A2 A3) 
  (O2 : O_opt A1' A2') (O2' : O_opt A2' A3') :
    B · ((O1 ⊗ O2) · (O1' ⊗ O2')) =b B · (O1 · O1' ⊗ O2 · O2').
Proof. by rewrite/= -tentf_comp trf_comp. Qed.
Lemma R_BRA_MLT_11 A1 A2 A3 A4 (s : A_base A1) (t : A_base A2) (O1 : O_opt A1 A3) (O2 : O_opt A2 A4) :
  '<(s, t)| · (O1 ⊗ O2) =b '<s| · O1 ⊗ '<t| · O2.
Proof. by rewrite/= -tentf_apply tentv_t2tv tentf_tr. Qed.
Lemma R_BRA_MLT_12 A1 A2 A3 A4 (B1 : B_bra A1) (B2 : B_bra A2) 
  (O1 : O_opt A1 A3) (O2 : O_opt A2 A4) :
    (B1 ⊗ B2) · (O1 ⊗ O2) =b B1 · O1 ⊗ B2 · O2.
Proof. by rewrite/= tentf_tr tentf_apply. Qed.

(* OP-ADJ *)
Lemma R_OP_ADJ_1 A1 A2 :
  0_(A1,A2)^A =o 0_(A2,A1).
Proof. by rewrite/= adjf0. Qed.
Lemma R_OP_ADJ_2 A :
  1_(A)^A =o 1_(A).
Proof. by rewrite/= adjf1. Qed.
Lemma R_OP_ADJ_3 A1 A2 (K : K_ket A1) (B : B_bra A2) :
  (K ·· B)^A =o B^A ·· K^A.
Proof. by rewrite/= adj_outp conjvK. Qed.
Lemma R_OP_ADJ_4 A1 A2 (O : O_opt A1 A2) :
  (O^A)^A =o O.
Proof. by rewrite/= adjfK. Qed.
Lemma R_OP_ADJ_5 A1 A2 (S : S_scalar) (O : O_opt A1 A2) :
  (S *: O)^A =o S^* *: O^A.
Proof. by rewrite/= adjfZ. Qed.
Lemma R_OP_ADJ_6 A1 A2 (O1 O2 : O_opt A1 A2) :
  (O1 + O2)^A =o O1^A + O2^A.
Proof. by rewrite/= adjfD. Qed.
Lemma R_OP_ADJ_7 A1 A2 A3 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) :
  (O1 · O2)^A =o O2^A · O1^A.
Proof. by rewrite/= adjf_comp. Qed.
Lemma R_OP_ADJ_8 A1 A2 A3 A4 (O1 : O_opt A1 A3) (O2 : O_opt A2 A4) :
  (O1 ⊗ O2)^A =o O1^A ⊗ O2^A.
Proof. by rewrite/= tentf_adj. Qed.

(* R-OP-MLT *)
Lemma R_OP_MLT_1 A1 A2 A3 (O : O_opt A2 A3) :
  0_(A1,A2) · O =o 0_(A1,A3).
Proof. by rewrite/= comp_lfun0l. Qed.
Lemma R_OP_MLT_2 A1 A2 A3 (O : O_opt A1 A2) :
  O · 0_(A2,A3) =o 0_(A1,A3).
Proof. by rewrite/= comp_lfun0r. Qed.
Lemma R_OP_MLT_3 A1 A2 (O : O_opt A1 A2) :
  1_(A1) · O =o O.
Proof. by rewrite/= comp_lfun1l. Qed.
Lemma R_OP_MLT_4 A1 A2 (O : O_opt A1 A2) :
  O · 1_(A2) =o O.
Proof. by rewrite/= comp_lfun1r. Qed.
Lemma R_OP_MLT_5 A1 A2 A3 (K : K_ket A1) (B : B_bra A2) (O : O_opt A2 A3) :
  (K ·· B) · O =o K ·· (B · O).
Proof. by rewrite/= outp_compl trfAC conjfE conjvK. Qed.
Lemma R_OP_MLT_6 A1 A2 A3 (O : O_opt A1 A2) (K : K_ket A2) (B : B_bra A3) :
  O · (K ·· B) =o (O · K) ·· B.
Proof. by rewrite/= outp_compr. Qed.
Lemma R_OP_MLT_7 A1 A2 A3 (S : S_scalar) (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) :
  (S *: O1) · O2 =o S *: (O1 · O2).
Proof. by rewrite/= linearZl. Qed.
Lemma R_OP_MLT_8 A1 A2 A3 (S : S_scalar) (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) :
  O1 · (S *: O2) =o S *: (O1 · O2).
Proof. by rewrite/= linearZr. Qed.
Lemma R_OP_MLT_9 A1 A2 A3  (O1 O2 : O_opt A1 A2) (O3 : O_opt A2 A3) :
  (O1 + O2) · O3 =o O1 · O3 + O2 · O3.
Proof. by rewrite/= linearDl. Qed.
Lemma R_OP_MLT_10 A1 A2 A3  (O1 : O_opt A1 A2) (O2 O3 : O_opt A2 A3) :
  O1 · (O2 + O3) =o O1 · O2 + O1 · O3.
Proof. by rewrite/= linearDr. Qed.
Lemma R_OP_MLT_11 A1 A2 A3 A4 (O1 : O_opt A1 A2) (O2 : O_opt A2 A3) (O3 : O_opt A3 A4) :
  (O1 · O2) · O3 =o O1 · (O2 · O3).
Proof. by rewrite/= comp_lfunA. Qed.
Lemma R_OP_MLT_12 A1 A2 A3 A1' A2' A3' (O1 : O_opt A1 A2) (O1' : O_opt A2 A3) 
  (O2 : O_opt A1' A2') (O2' : O_opt A2' A3') :
    (O1 ⊗ O2) · (O1' ⊗ O2') =o O1 · O1' ⊗ O2 · O2'.
Proof. by rewrite/= tentf_comp. Qed.
Lemma R_OP_MLT_13 A1 A2 A3 A1' A2' A3' A4 (O1 : O_opt A1 A2) (O1' : O_opt A2 A3) 
  (O2 : O_opt A1' A2') (O2' : O_opt A2' A3') (O3 : O_opt (Apair A3 A3') A4):
    (O1 ⊗ O2) · ((O1' ⊗ O2') · O3) =o (O1 · O1' ⊗ O2 · O2') · O3.
Proof. by rewrite -R_OP_MLT_11/= tentf_comp. Qed.

End Term_Rewriting_System.
End DiracTRS_SOUND.
End Playground0.



(*****************************************************************************)
(*                                Playground1                                *)
(*****************************************************************************)
Module Playground1.

Section DiracTRS_SOUND.
Variable (atype : eqType).
Variable (eval_AT : atype -> ihbFinType).
Variable (aname stname : finType).
Variable (sname kname bname oname : finType).

(* Notation for A, Context and Valuation *)
Notation AType := (@AType atype).
Notation eval_AType := (@eval_AType atype eval_AT).

Notation "''Ha' A" := (@HA atype eval_AT A)
  (at level 8, A at level 2, format "''Ha'  A").
Notation "''Hom{' A1 , A2 }" := ('Hom('Ha A1, 'Ha A2)) 
  (at level 8, format "''Hom{' A1 ,  A2 }").
Notation "''End{' A }" := ('End('Ha A)) 
  (at level 8, format "''End{' A }").

(* name of variables *)
Notation Gamma_A := (Gamma_A atype aname).
Notation Gamma_ST := (Gamma_ST atype stname).
Notation Gamma_B := (Gamma_B atype bname).
Notation Gamma_K := (Gamma_K atype kname).
Notation Gamma_O := (Gamma_O atype oname).
Notation Gamma_A_update ca n A := (@Gamma_A_update atype aname ca n A).

Variable (cst : Gamma_ST) (ck : Gamma_K) (cb : Gamma_B) (co : Gamma_O).

Notation A_value ca := (@A_value atype eval_AT aname ca).
Notation ST_value := (@ST_value atype eval_AT stname cst).
Notation S_value := (@S_value sname).
Notation K_value := (@K_value atype eval_AT kname ck).
Notation B_value := (@B_value atype eval_AT bname cb).
Notation O_value := (@O_value atype eval_AT oname co).

Notation A_value_update ca av a v t := 
  (@A_value_update atype eval_AT aname ca av a v t).

Inductive A_base {ca : Gamma_A} : AType -> Type :=
    | A_var (n : aname) : A_base (ca n)
    | A_ground (A : AType) (a : eval_AType A) : A_base A
    | A_pair (A1 A2 : AType) (a1 : A_base A1) (a2 : A_base A2) : A_base (Apair A1 A2)
    | A_fst (A1 A2 : AType) (a : A_base (Apair A1 A2)) : A_base A1
    | A_snd (A1 A2 : AType) (a : A_base (Apair A1 A2)) : A_base A2.

Inductive ST_syn : AType -> Type :=
    | ST_var (n : stname) : ST_syn (cst n)
    | ST_uni (A : AType) : ST_syn A
    | ST_prod A1 A2 (S1 : ST_syn A1) (S2 : ST_syn A2) : ST_syn (Apair A1 A2). 

Inductive S_scalar {ca : Gamma_A} : Type :=
    | S_var (n : sname)
    | S_0
    | S_1
    | S_delta (A : AType) (a1 a2 : @A_base ca A)
    | S_add (s1 s2 : S_scalar)
    | S_mul (s1 s2 : S_scalar)
    | S_conj (s : S_scalar)
    | BK_inner (A : AType) (b : B_bra A) (k : K_ket A)
    | S_sum A (st : ST_syn A) (n : aname) 
        (s : @S_scalar (Gamma_A_update ca n A)) : S_scalar
with K_ket {ca : Gamma_A} : AType -> Type :=
    | K_var (n : kname) : K_ket (ck n)
    | K_0 (A : AType) : K_ket A
    | K_ground (A : AType) (a : @A_base ca A) : K_ket A
    | B_adj (A : AType) (b : B_bra A) : K_ket A
    | K_scale (s : S_scalar) (A : AType) (k : K_ket A) : K_ket A
    | K_add (A : AType) (k1 k2 : K_ket A) : K_ket A
    | K_apply (A1 A2 : AType) (o : O_opt A1 A2) (k : K_ket A2) : K_ket A1
    | K_ten (A1 A2 : AType) (k1 : K_ket A1) (k2 : K_ket A2) : K_ket (Apair A1 A2)
    | K_sum (As A : AType) (st : ST_syn As) (n : aname) 
        (k : @K_ket (Gamma_A_update ca n As) A) : K_ket A
with B_bra {ca : Gamma_A} : AType -> Type :=
    | B_var (n : bname) : B_bra (cb n)
    | B_0 (A : AType) : B_bra A
    | B_ground (A : AType) (a : @A_base ca A) : B_bra A
    | K_adj (A : AType) (b : K_ket A) : B_bra A
    | B_scale (s : S_scalar) (A : AType) (b : B_bra A) : B_bra A
    | B_add (A : AType) (b1 b2 : B_bra A) : B_bra A
    | B_apply (A1 A2 : AType) (b : B_bra A1) (o : O_opt A1 A2) : B_bra A2
    | B_ten (A1 A2 : AType) (b1 : B_bra A1) (b2 : B_bra A2) : B_bra (Apair A1 A2)
    | B_sum (As A : AType) (st : ST_syn As) (n : aname) 
        (b : @B_bra (Gamma_A_update ca n As) A) : B_bra A
with O_opt {ca : Gamma_A} : AType -> AType -> Type :=
    | O_var (n : oname) : O_opt (co n).1 (co n).2
    | O_0 (A1 A2 : AType) : O_opt A1 A2
    | O_1 (A : AType) : O_opt A A
    | KB_outer (A1 A2 : AType) (k : K_ket A1) (b : B_bra A2) : O_opt A1 A2
    | O_adj (A1 A2 : AType) (o : O_opt A1 A2) : O_opt A2 A1
    | O_scale (s : S_scalar) (A1 A2 : AType) (o : O_opt A1 A2) : O_opt A1 A2
    | O_add (A1 A2 : AType) (o1 o2 : O_opt A1 A2) : O_opt A1 A2
    | O_comp (A1 A2 A3 : AType) (o1 : O_opt A1 A2) (o2 : O_opt A2 A3) : O_opt A1 A3
    | O_ten (A1 A2 A3 A4 : AType) (o1 : O_opt A1 A2) (o2 : O_opt A3 A4) : O_opt (Apair A1 A3) (Apair A2 A4)
    | O_sum (As A1 A2 : AType) (st : ST_syn As) (n : aname) 
        (o : @O_opt (Gamma_A_update ca n As) A1 A2) : O_opt A1 A2.
Arguments K_0 {ca A}.
Arguments B_0 {ca A}.
Arguments O_0 {ca A1 A2}.
Arguments O_1 {ca A}.

Scheme S_scalar_all_ind := Induction for S_scalar Sort Prop
  with K_ket_all_ind := Induction for K_ket Sort Prop
  with B_bra_all_ind := Induction for B_bra Sort Prop
  with O_opt_all_ind := Induction for O_opt Sort Prop.

Combined Scheme All_syn_mutind from 
  S_scalar_all_ind, K_ket_all_ind, B_bra_all_ind, O_opt_all_ind.

Fixpoint A_sem {ca : Gamma_A} (av : A_value ca) {A : AType} (a : A_base A) : eval_AType A :=
  match a in A_base A return eval_AType A with
  | A_var n => av n
  | A_ground A a => a
  | A_pair A1 A2 a1 a2 => (@A_sem ca av A1 a1, @A_sem ca av A2 a2)
  | A_fst A1 A2 a => (@A_sem ca av (Apair A1 A2) a).1
  | A_snd A1 A2 a => (@A_sem ca av (Apair A1 A2) a).2
  end.

Variable (stv : ST_value).

Fixpoint ST_sem {A : AType} (st : ST_syn A) : {set eval_AType A} :=
  match st in ST_syn A return {set eval_AType A} with
  | ST_var n => stv n
  | ST_uni A => setT
  | ST_prod A1 A2 S1 S2 => setX (ST_sem S1) (ST_sem S2)
  end.

Variable (sv : S_value) (kv : K_value) (bv : B_value) (ov : O_value).

Fixpoint S_sem {ca : Gamma_A} (av : A_value ca) (s : @S_scalar ca) : C :=
  match s with
  | S_var n => sv n
  | S_0 => 0
  | S_1 => 1
  | S_delta A a1 a2 => (A_sem av a1 ==  A_sem av a2)%:R
  | S_add s1 s2 => S_sem av s1 + S_sem av s2
  | S_mul s1 s2 => S_sem av s1 * S_sem av s2
  | S_conj s => (S_sem av s)^*
  | BK_inner A b k => [< (B_sem av b)^*v ; K_sem av k>]
  | S_sum A st n s =>
      \sum_(i in ST_sem st) S_sem (A_value_update ca av n A i) s
  end
with K_sem {ca : Gamma_A} (av : A_value ca) {A : AType} (k : @K_ket ca A): 'Ha A :=
  match k in K_ket A return 'Ha A with
  | K_var n => kv n
  | K_0 A => 0
  | K_ground A a => ''(A_sem av a)
  | B_adj A b => (B_sem av b)^*v
  | K_scale s A k => (S_sem av s) *: (K_sem av k)
  | K_add A k1 k2 => (K_sem av k1) + (K_sem av k2)
  | K_apply A1 A2 o k => (O_sem av o) (K_sem av k)
  | K_ten A1 A2 k1 k2 => (K_sem av k1)  ⊗t (K_sem av k2)
  | K_sum As A st n k =>
      \sum_(i in ST_sem st) K_sem (A_value_update ca av n As i) k
  end
with B_sem {ca : Gamma_A} (av : A_value ca) {A : AType} (b : @B_bra ca A): 'Ha A :=
  match b in B_bra A return 'Ha A with
  | B_var n => bv n
  | B_0 A => 0
  | B_ground A a => ''(A_sem av a)
  | K_adj A k => (K_sem av k)^*v
  | B_scale s A b => (S_sem av s) *: (B_sem av b)
  | B_add A b1 b2 => (B_sem av b1) + (B_sem av b2)
  | B_apply A1 A2 b o => ((O_sem av o)^T (B_sem av b))
  | B_ten A1 A2 b1 b2 => (B_sem av b1) ⊗t (B_sem av b2)
  | B_sum As A st n b =>
      \sum_(i in ST_sem st) B_sem (A_value_update ca av n As i) b
  end
with O_sem {ca : Gamma_A} (av : A_value ca) (A1 A2 : AType) (o : @O_opt ca A1 A2) : 'Hom{A2, A1} :=
  match o in O_opt A1 A2 return 'Hom{A2, A1} with
  | O_var n => ov n
  | O_0 A1 A2 => 0%:VF
  | O_1 A => \1
  | KB_outer A1 A2 k b => [> K_sem av k ; (B_sem av b)^*v <]
  | O_adj A1 A2 o => (O_sem av o)^A
  | O_scale s A1 A2 o => (S_sem av s) *: (O_sem av o)
  | O_add A1 A2 o1 o2 => (O_sem av o1) + (O_sem av o2)
  | O_comp A1 A2 A3 o1 o2 => (O_sem av o1) \o (O_sem av o2)
  | O_ten A1 A2 A3 A4 o1 o2 => (O_sem av o1) ⊗f (O_sem av o2)
  | O_sum As A1 A2 st n o =>
      \sum_(i in ST_sem st) O_sem (A_value_update ca av n As i) o
  end.

Section Relation_L0_L1.

Variable (ca : Gamma_A).

Fixpoint L0_L1_A_base (A : AType) (a : Playground0.A_base eval_AT ca A) : @A_base ca A :=
  match a with
  | Playground0.A_var n => A_var n
  | Playground0.A_ground A a => A_ground a
  | Playground0.A_pair A1 A2 a1 a2 => A_pair (L0_L1_A_base a1) (L0_L1_A_base a2)
  end.

Fixpoint L0_L1_S_scalar (s : Playground0.S_scalar eval_AT sname ca ck cb co) : @S_scalar ca :=
  match s with
    | Playground0.S_var n => S_var n
    | Playground0.S_0 => S_0
    | Playground0.S_1 => S_1
    | Playground0.S_delta A a1 a2 => S_delta (L0_L1_A_base a1) (L0_L1_A_base a2)
    | Playground0.S_add s1 s2 => S_add (L0_L1_S_scalar s1) (L0_L1_S_scalar s2)
    | Playground0.S_mul s1 s2 => S_mul (L0_L1_S_scalar s1) (L0_L1_S_scalar s2)
    | Playground0.S_conj s => S_conj (L0_L1_S_scalar s)
    | Playground0.BK_inner A b k => BK_inner (L0_L1_B_bra b) (L0_L1_K_ket k)
  end
with L0_L1_K_ket A (k : Playground0.K_ket eval_AT sname ca ck cb co A) : @K_ket ca A :=
  match k with
    | Playground0.K_var n => K_var n
    | Playground0.K_0 A => K_0
    | Playground0.K_ground A a => K_ground (L0_L1_A_base a)
    | Playground0.B_adj A b => B_adj (L0_L1_B_bra b)
    | Playground0.K_scale s A k => K_scale (L0_L1_S_scalar s) (L0_L1_K_ket k)
    | Playground0.K_add A k1 k2 => K_add (L0_L1_K_ket k1) (L0_L1_K_ket k2)
    | Playground0.K_apply A1 A2 o k => K_apply (L0_L1_O_opt o) (L0_L1_K_ket k)
    | Playground0.K_ten A1 A2 k1 k2 => K_ten (L0_L1_K_ket k1) (L0_L1_K_ket k2)
  end
with L0_L1_B_bra A (b : Playground0.B_bra eval_AT sname ca ck cb co A) : @B_bra ca A :=
  match b with
    | Playground0.B_var n => B_var n
    | Playground0.B_0 A => B_0
    | Playground0.B_ground A a => B_ground (L0_L1_A_base a)
    | Playground0.K_adj A k => K_adj (L0_L1_K_ket k)
    | Playground0.B_scale s A b => B_scale (L0_L1_S_scalar s) (L0_L1_B_bra b)
    | Playground0.B_add A b1 b2 => B_add (L0_L1_B_bra b1) (L0_L1_B_bra b2)
    | Playground0.B_apply A1 A2 b o => B_apply (L0_L1_B_bra b) (L0_L1_O_opt o)
    | Playground0.B_ten A1 A2 b1 b2 => B_ten (L0_L1_B_bra b1) (L0_L1_B_bra b2)
  end
with L0_L1_O_opt A1 A2 (o : Playground0.O_opt eval_AT sname ca ck cb co A1 A2) : @O_opt ca A1 A2 :=
  match o with
    | Playground0.O_var n => O_var n
    | Playground0.O_0 A1 A2 => O_0
    | Playground0.O_1 A => O_1
    | Playground0.KB_outer A1 A2 k b => KB_outer (L0_L1_K_ket k) (L0_L1_B_bra b)
    | Playground0.O_adj A1 A2 o => O_adj (L0_L1_O_opt o)
    | Playground0.O_scale s A1 A2 o => O_scale (L0_L1_S_scalar s) (L0_L1_O_opt o)
    | Playground0.O_add A1 A2 o1 o2 => O_add (L0_L1_O_opt o1) (L0_L1_O_opt o2)
    | Playground0.O_comp A1 A2 A3 o1 o2 => O_comp (L0_L1_O_opt o1) (L0_L1_O_opt o2)
    | Playground0.O_ten A1 A2 A3 A4 o1 o2 => O_ten (L0_L1_O_opt o1) (L0_L1_O_opt o2)
  end.

Variable (av : A_value ca).

Lemma L0_L1_A_sem A (a : Playground0.A_base eval_AT ca A) :
  Playground0.A_sem av a = A_sem av (L0_L1_A_base a).
Proof. by elim: a=>// A1 A2/= a1 -> a2 ->. Qed.

Let L0_L1_S_sem_eq :=
  (forall s : Playground0.S_scalar eval_AT sname ca ck cb co, 
  Playground0.S_sem av sv kv bv ov s = S_sem av (L0_L1_S_scalar s)).
Let L0_L1_K_sem_eq :=
  (forall A (k : Playground0.K_ket eval_AT sname ca ck cb co A),
   Playground0.K_sem av sv kv bv ov k = K_sem av (L0_L1_K_ket k)).
Let L0_L1_B_sem_eq :=
  (forall A (b : Playground0.B_bra eval_AT sname ca ck cb co A),
   Playground0.B_sem av sv kv bv ov b = B_sem av (L0_L1_B_bra b)).
Let L0_L1_O_sem_eq :=
  (forall A1 A2 (o : Playground0.O_opt eval_AT sname ca ck cb co A1 A2),
   Playground0.O_sem av sv kv bv ov o = O_sem av (L0_L1_O_opt o)).

Lemma L0_L1_All_sem : L0_L1_S_sem_eq /\ L0_L1_K_sem_eq /\ L0_L1_B_sem_eq /\ L0_L1_O_sem_eq.
Proof.
apply Playground0.All_syn_mutind=>//.
(* about scalar *)
- by move=>A a1 a2 /=; rewrite -L0_L1_A_sem -L0_L1_A_sem.
- by move=> /= s1 <- s2 <-.
- by move=> /= s1 <- s2 <-.
- by move=> /= s <-.
- by move=> /= A b <- k <-.
(* about ket *)
- by move=> /= A a; rewrite -L0_L1_A_sem.
- by move=> /= A b <-.
- by move=> /= s <- A k <-.
- by move=> /= A k1 <- k2 <-.
- by move=> /= A1 A2 o <- k <-.
- by move=> /= A1 A2 k1 <- k2 <-.
(* about bra *)
- by move=> /= A a; rewrite -L0_L1_A_sem.
- by move=> /= A k <-.
- by move=> /= s <- A b <-.
- by move=> /= A b1 <- b2 <-.
- by move=> /= A1 A2 b <- o <-.
- by move=> /= A1 A2 o1 <- o2 <-.
(* about opt *)
- by move=> /= A1 A2 k <- b <-.
- by move=> /= A1 A2 o <-.
- by move=> /= s <- A1 A2 o <-.
- by move=> /= A1 A2 o1 <- o2 <-.
- by move=> /= A1 A2 A3 o1 <- o2 <-.
- by move=> /= A1 A2 A3 A4 o1 <- o2 <-.
Qed.

Lemma L0_L1_S_sem s : 
  Playground0.S_sem av sv kv bv ov s = S_sem av (L0_L1_S_scalar s).
Proof. by move: L0_L1_All_sem s =>[]. Qed.

Lemma L0_L1_K_sem A k :
   Playground0.K_sem av sv kv bv ov k = K_sem av (@L0_L1_K_ket A k).
Proof. by move: L0_L1_All_sem k =>[] _ []. Qed.

Lemma L0_L1_B_sem A b :
   Playground0.B_sem av sv kv bv ov b = B_sem av (@L0_L1_B_bra A b).
Proof. by move: L0_L1_All_sem b =>[] _ [] _ []. Qed.

Lemma L0_L1_O_sem A1 A2 o :
   Playground0.O_sem av sv kv bv ov o = O_sem av (@L0_L1_O_opt A1 A2 o).
Proof. by move: L0_L1_All_sem o =>[] _ [] _ []. Qed.

End Relation_L0_L1.

End DiracTRS_SOUND.

End Playground1.


(*****************************************************************************)
(*                                Playground2                                *)
(*****************************************************************************)
Module Playground2.
Section DiracTRS_SOUND.
Variable (atype : eqType).
Variable (eval_AT : atype -> ihbFinType).
Variable (aname stname : finType).
Variable (sname kname bname oname : finType).

(* Notation for A, Context and Valuation *)
Notation AType := (@AType atype).
Notation eval_AType := (@eval_AType atype eval_AT).

Notation "''Ha' A" := (@HA atype eval_AT A)
  (at level 8, A at level 2, format "''Ha'  A").
Notation "''Hom{' A1 , A2 }" := ('Hom('Ha A1, 'Ha A2)) 
  (at level 8, format "''Hom{' A1 ,  A2 }").
Notation "''End{' A }" := ('End('Ha A)) 
  (at level 8, format "''End{' A }").

Notation Gamma_A := (Gamma_A atype aname).
Notation Gamma_ST := (Gamma_ST atype stname).
Notation Gamma_B := (Gamma_B atype bname).
Notation Gamma_K := (Gamma_K atype kname).
Notation Gamma_O := (Gamma_O atype oname).
Notation Gamma_A_update ca n A := (@Gamma_A_update atype aname ca n A).
Notation A_value_update av a t := (@A_value_update atype eval_AT aname _ av a _ t).

Inductive A_base : Type :=
  | A_var (n : aname)
  | A_ground (A : AType) (a : eval_AType A)
  | A_pair (a1 : A_base) (a2 : A_base)
  | A_fst (a : A_base)
  | A_snd (a : A_base).

Inductive DType :=
  | DScale
  | DKet of AType
  | DBra of AType
  | DOpt of AType * AType.

(* all the syntax, both for basis types, dirac types, set, terms *)
Inductive AT_syn : Type :=
    | AT_ground (A : AType)
    | AT_pair (A1 A2 : AT_syn)
    | AT_proj1 (A : AT_syn)
    | AT_proj2 (A : AT_syn)
    | AT_ket (D : DT_syn)
    | AT_bra (D : DT_syn)
    | AT_get (a : A_base)
    | AT_set (A : AT_syn)
    | AT_st_get (st : ST_syn)
with DT_syn : Type :=
    | DT_scale
    | DT_ket (A : AT_syn)
    | DT_bra (A : AT_syn)
    | DT_opt (A1 A2 : AT_syn)
    | DT_s_get (s : S_scalar)
    | DT_k_get (k : K_ket)
    | DT_b_get (b : B_bra)
    | DT_o_get (o : O_opt)
with ST_syn : Type :=
    | ST_var (n : stname)
    | ST_uni (A : AT_syn)
    | ST_prod (A1 A2 : ST_syn)
with  S_scalar : Type :=
    | S_var (n : sname) : S_scalar
    | S_0 : S_scalar
    | S_1 : S_scalar
    | S_delta (a1 a2 : A_base) : S_scalar
    | S_add (s1 s2 : S_scalar) : S_scalar
    | S_mul (s1 s2 : S_scalar) : S_scalar
    | S_conj (s : S_scalar) : S_scalar
    | BK_inner (b : B_bra) (k : K_ket) : S_scalar
    | S_sum (st : ST_syn) (n : aname) (s : S_scalar) : S_scalar
with K_ket : Type :=
    | K_var (n : kname) : K_ket
    | K_0 (A : AT_syn) : K_ket
    | K_ground (a : A_base) : K_ket
    | B_adj (b : B_bra) : K_ket
    | K_scale (s : S_scalar) (k : K_ket) : K_ket
    | K_add (k1 k2 : K_ket) : K_ket
    | K_apply (o : O_opt) (k : K_ket) : K_ket
    | K_ten (k1 : K_ket) (k2 : K_ket) : K_ket
    | K_sum (st : ST_syn) (n : aname) (k : K_ket) : K_ket
with B_bra : Type :=
    | B_var (n : bname) : B_bra
    | B_0 (A : AT_syn) : B_bra
    | B_ground (t : A_base) : B_bra
    | K_adj (b : K_ket) : B_bra
    | B_scale (s : S_scalar) (b : B_bra) : B_bra
    | B_add (b1 b2 : B_bra) : B_bra
    | B_apply (b : B_bra) (o : O_opt) : B_bra
    | B_ten (b1 : B_bra) (b2 : B_bra) : B_bra
    | B_sum (st : ST_syn) (n : aname) (b : B_bra) : B_bra
with O_opt : Type :=
    | O_var (n : oname) : O_opt
    | O_0 (A1 A2 : AT_syn) : O_opt
    | O_1 (A : AT_syn) : O_opt
    | KB_outer (k : K_ket) (b : B_bra) : O_opt
    | O_adj (o : O_opt) : O_opt
    | O_scale (s : S_scalar) (o : O_opt) : O_opt
    | O_add (o1 o2 : O_opt) : O_opt
    | O_comp (o1 : O_opt) (o2 : O_opt) : O_opt
    | O_ten (o1 : O_opt) (o2 : O_opt) : O_opt
    | O_sum (st : ST_syn) (n : aname) (o : O_opt) : O_opt.

Scheme AT_syn_all_ind := Induction for AT_syn Sort Prop
  with DT_syn_all_ind := Induction for DT_syn Sort Prop
  with ST_type_all_ind := Induction for ST_syn Sort Prop
  with S_scalar_all_ind := Induction for S_scalar Sort Prop
  with K_ket_all_ind := Induction for K_ket Sort Prop
  with B_bra_all_ind := Induction for B_bra Sort Prop
  with O_opt_all_ind := Induction for O_opt Sort Prop.

Combined Scheme All_syn_mutind from 
  AT_syn_all_ind, DT_syn_all_ind, ST_type_all_ind, 
  S_scalar_all_ind, K_ket_all_ind, B_bra_all_ind, O_opt_all_ind.

Scheme S_scalar_dirac_ind := Induction for S_scalar Sort Prop
  with K_ket_dirac_ind := Induction for K_ket Sort Prop
  with B_bra_dirac_ind := Induction for B_bra Sort Prop
  with O_opt_dirac_ind := Induction for O_opt Sort Prop.

Combined Scheme Dirac_syn_mutind from 
  S_scalar_dirac_ind, K_ket_dirac_ind, B_bra_dirac_ind, O_opt_dirac_ind.

(* basis term's type is fully determined by context Gamma_A *)
Fixpoint atype_checker (ca : Gamma_A) (a : A_base) : option AType :=
  match a with
  | A_var n => Some (ca n)
  | A_ground A a => Some A
  | A_pair a1 a2 =>
      match atype_checker ca a1, atype_checker ca a2 with
      | Some T1, Some T2 => Some (Apair T1 T2)
      | _, _ => None
      end
  | A_fst a =>
      match atype_checker ca a with
      | Some (Apair T1 T2) => Some T1
      | _ => None
      end
  | A_snd a =>
      match atype_checker ca a with
      | Some (Apair T1 T2) => Some T2
      | _ => None
      end
  end.

Variable (cst : Gamma_ST) (ck : Gamma_K) (cb : Gamma_B) (co : Gamma_O).

(* type checker *)
Fixpoint AT_sem (ca : Gamma_A) (a : AT_syn) : option AType :=
  match a with
  | AT_ground A => Some A
  | AT_pair A1 A2 => 
      match (AT_sem ca A1), (AT_sem ca A2) with
      | Some A1, Some A2 => Some (Apair A1 A2)
      | _, _ => None
      end
  | AT_proj1 A => 
      match (AT_sem ca A) with
      | Some (Apair A1 A2) => Some A1
      | _ => None
      end
  | AT_proj2 A => 
      match (AT_sem ca A) with
      | Some (Apair A1 A2) => Some A2
      | _ => None
      end
  | AT_ket D =>
      match (DT_sem ca D) with
      | Some (DKet A) => Some A
      | Some (DOpt A) => Some A.1
      | _ => None
      end
  | AT_bra D =>
      match (DT_sem ca D) with
      | Some (DBra A) => Some A
      | Some (DOpt A) => Some A.2
      | _ => None
      end
  | AT_get a => atype_checker ca a
  | AT_set A =>
      match (AT_sem ca A) with
      | Some A => Some A
      | _ => None
      end
  | AT_st_get st => sttype_checker ca st
  end
with DT_sem ca (dt : DT_syn) : option DType :=
  match dt with
  | DT_scale => Some DScale
  | DT_ket A =>
      match (AT_sem ca A) with
      | Some A => Some (DKet A)
      | _ => None
      end
  | DT_bra A =>
      match (AT_sem ca A) with
      | Some A => Some (DBra A)
      | _ => None
      end
  | DT_opt A1 A2 =>
      match (AT_sem ca A1), (AT_sem ca A2)  with
      | Some A1, Some A2 => Some (DOpt (A1,A2))
      | _,_ => None
      end
  | DT_s_get s => stype_checker ca s
  | DT_k_get k => ktype_checker ca k
  | DT_b_get b => btype_checker ca b
  | DT_o_get o => otype_checker ca o
  end
with sttype_checker ca (st : ST_syn) : option AType :=
  match st with
  | ST_var n => Some (cst n)
  | ST_uni A => AT_sem ca A
  | ST_prod S1 S2 => 
      match (sttype_checker ca S1), (sttype_checker ca S2) with
      | Some A1, Some A2 => Some (Apair A1 A2)
      | _, _ => None
      end
  end
with stype_checker ca (s : S_scalar) : option DType :=
  match s with
    | S_var n => Some DScale
    | S_0 => Some DScale
    | S_1 => Some DScale
    | S_delta a1 a2 =>
        match atype_checker ca a1, atype_checker ca a2 with
        | Some A1, Some A2 => if A1 == A2 then Some DScale else None
        | _, _ => None
        end
    | S_add s1 s2 =>
        match stype_checker ca s1, stype_checker ca s2 with
        | Some DScale, Some DScale => Some DScale
        | _, _ => None
        end
    (* | S_opp (s : S_scalar) *)
    | S_mul s1 s2 =>
        match stype_checker ca s1, stype_checker ca s2 with
        | Some DScale, Some DScale => Some DScale
        | _, _ => None
        end
    | S_conj s => stype_checker ca s
    | BK_inner b k =>
        match btype_checker ca b, ktype_checker ca k with
        | Some (DBra t1), Some (DKet t2) =>
            if t1 == t2 then Some DScale else None
        | _, _ => None
        end
    | S_sum st n s =>
        match sttype_checker ca st with
        | Some A => stype_checker (Gamma_A_update ca n A) s
        | _ => None
        end
  end
with ktype_checker ca (k : K_ket) : option DType :=
  match k with
    | K_var n => Some (DKet (ck n))
    | K_0 A =>
        match AT_sem ca A with
        | Some T => Some (DKet T)
        | _ => None
        end
    | K_ground t =>
        match atype_checker ca t with
        | Some T => Some (DKet T)
        | _ => None
        end
    | B_adj b =>
        match btype_checker ca b with
        | Some (DBra T) => Some (DKet T)
        | _ => None
        end
    | K_scale s k =>
        match stype_checker ca s, ktype_checker ca k with
        | Some DScale, Some (DKet t) => Some (DKet t)
        | _,_ => None
        end
    | K_add k1 k2 =>
        match ktype_checker ca k1, ktype_checker ca k2 with
        | Some (DKet t1), Some (DKet t2) =>
            if t1 == t2 then Some (DKet t1) else None
        | _, _ => None
        end
    | K_apply o k =>
        match otype_checker ca o, ktype_checker ca k with
        | Some (DOpt t), Some (DKet t3) =>
            if t.2 == t3 then Some (DKet t.1) else None
        | _, _ => None
        end
    | K_ten k1 k2 =>
        match ktype_checker ca k1, ktype_checker ca k2 with
        | Some (DKet t1), Some (DKet t2) =>
            Some (DKet (Apair t1 t2))
        | _, _ => None
        end
    | K_sum st n k =>
        match sttype_checker ca st with
        | Some A => ktype_checker (Gamma_A_update ca n A) k
        | _ => None
        end
  end
with btype_checker ca (b : B_bra) : option DType := 
  match b with
    | B_var n => Some (DBra (cb n))
    | B_0 T => 
        match AT_sem ca T with
        | Some T => Some (DBra T)
        | _ => None
        end
    | B_ground t =>
        match atype_checker ca t with
        | Some T => Some (DBra T)
        | _ => None
        end
    | K_adj k =>
        match ktype_checker ca k with
        | Some (DKet T) => Some (DBra T)
        | _ => None
        end
    | B_scale s b =>
        match stype_checker ca s, btype_checker ca b with
        | Some DScale, Some (DBra t) => Some (DBra t)
        | _,_ => None
        end
    | B_add b1 b2 =>
        match btype_checker ca b1, btype_checker ca b2 with
        | Some (DBra t1), Some (DBra t2) =>
            if t1 == t2 then Some (DBra t1) else None
        | _, _ => None
        end
    | B_apply b o =>
        match btype_checker ca b, otype_checker ca o with
        | Some (DBra t1), Some (DOpt t) =>
            if t1 == t.1 then Some (DBra t.2) else None
        | _, _ => None
        end
    | B_ten b1 b2 =>
        match btype_checker ca b1, btype_checker ca b2 with
        | Some (DBra t1), Some (DBra t2) =>
            Some (DBra (Apair t1 t2))
        | _, _ => None
        end
    | B_sum st n b =>
        match sttype_checker ca st with
        | Some A => btype_checker (Gamma_A_update ca n A) b
        | _ => None
        end
  end
with otype_checker ca (o : O_opt) : option DType := 
  match o with
    | O_var n => Some (DOpt (co n))
    | O_0 T1 T2 => 
        match AT_sem ca T1, AT_sem ca T2 with
        | Some T1, Some T2 => Some (DOpt (T1, T2))
        | _,_ => None
        end
    | O_1 T => 
        match AT_sem ca T with
        | Some T => Some (DOpt (T, T))
        | _ => None
        end
    | KB_outer k b =>
        match ktype_checker ca k, btype_checker ca b with
        | Some (DKet t1), Some (DBra t2) =>
            Some (DOpt (t1, t2))
        | _, _ => None
        end
    | O_adj o =>
        match otype_checker ca o with
        | Some (DOpt t) => Some (DOpt (t.2, t.1))
        | _ => None
        end
    | O_scale s o =>
        match stype_checker ca s, otype_checker ca o with
        | Some DScale, Some (DOpt t) => Some (DOpt t)
        | _,_ => None
        end
    | O_add o1 o2 =>
        match otype_checker ca o1, otype_checker ca o2 with
        | Some (DOpt t1), Some (DOpt t2) =>
            if (t1 == t2) then 
              Some (DOpt t1) 
            else None
        | _, _ => None
        end
    | O_comp o1 o2 =>
        match otype_checker ca o1, otype_checker ca o2 with
        | Some (DOpt t1), Some (DOpt t2) =>
            if (t1.2 == t2.1) then 
              Some (DOpt (t1.1, t2.2)) 
            else None
        | _, _ => None
        end
    | O_ten o1 o2 =>
        match otype_checker ca o1, otype_checker ca o2 with
        | Some (DOpt t1), Some (DOpt t2) =>
            Some (DOpt ((Apair t1.1 t2.1), (Apair t1.2 t2.2)))
        | _, _ => None
        end
    | O_sum st n o =>
        match sttype_checker ca st with
        | Some A => otype_checker (Gamma_A_update ca n A) o
        | _ => None
        end
  end.

(* we encode semantics as a large matrix                                  *)
(* the same idea from the formalization of dirac notation                 *)
(* for example, S_sem : S_scale -> C                                      *)
(*              K_sem : K_ket   -> (forall A, 'Ha A)                      *)
(*              B_sem : B_bra   -> (forall A, 'Ha A)                      *)
(*              O_sem : O_opt   -> (forall A1 A2, 'Ha A2 A1)              *)
(* we compute the semantics only if it is well-typed, otherwise           *)
(* we directly set the value to the default, say 0                        *)

Definition A_sem_type := forall A, eval_AType A.
Definition ST_sem_type := forall A, {set eval_AType A}.
(* Definition S_sem_type := C *)
Definition V_sem_type := forall A, 'Ha A.
Definition O_sem_type := forall A : AType * AType, 'Hom('Ha A.2, 'Ha A.1).

Definition A_sem0 : A_sem_type := fun => @witness _.
Definition ST_sem1 : ST_sem_type := fun => setT.
(* Definition S_sem0 : S_sem_type := 0. *)
Definition V_sem0 : V_sem_type := fun => 0.
Definition O_sem0 : O_sem_type := fun => 0.
Definition A_set (A : AType) (v : eval_AType A) : A_sem_type :=
  fun a => if A =P a is ReflectT eq then 
                ecast k (eval_AType k) eq v 
           else @witness _.
Definition ST_set (A : AType) (v : {set eval_AType A}) : ST_sem_type :=
  fun a => if A =P a is ReflectT eq then 
                ecast k ({set eval_AType k}) eq v 
           else setT.
Definition V_set (A : AType) (v : 'Ha A) : V_sem_type :=
  fun a => if A =P a is ReflectT eq then 
                ecast k ('Ha k) eq v 
           else 0.
Definition O_set (A : AType * AType) (v : 'Hom('Ha A.2, 'Ha A.1)) : O_sem_type :=
  fun a => if A =P a is ReflectT eq then 
                ecast k ('Hom('Ha k.2, 'Ha k.1)) eq v 
           else 0.

Lemma A_set_id (A : AType) (v : eval_AType A) : A_set v A = v.
Proof. by rewrite /A_set; case: eqP=>// p; rewrite eq_axiomK. Qed.
Lemma A_set_neq (A : AType) (v : eval_AType A) A' : 
  A != A' -> A_set v A' = @witness _.
Proof. by move=>/eqP P; rewrite /A_set; case: eqP. Qed.
Lemma ST_set_id (A : AType) (v : {set eval_AType A}) : ST_set v A = v.
Proof. by rewrite /ST_set; case: eqP=>// p; rewrite eq_axiomK. Qed.
Lemma ST_set_neq (A : AType) (v : {set eval_AType A}) A' : 
  A != A' -> ST_set v A' = setT.
Proof. by move=>/eqP P; rewrite /ST_set; case: eqP. Qed.
Lemma V_set_id (A : AType) (v : 'Ha A) : V_set v A = v.
Proof. by rewrite /V_set; case: eqP=>// p; rewrite eq_axiomK. Qed.
Lemma V_set_neq (A : AType) (v : 'Ha A) A' : 
  A != A' -> V_set v A' = 0.
Proof. by move=>/eqP P; rewrite /V_set; case: eqP. Qed.
Lemma O_set_id (A : AType * AType) (v : 'Hom('Ha A.2, 'Ha A.1)) : O_set v A = v.
Proof. by rewrite /O_set; case: eqP=>// p; rewrite eq_axiomK. Qed.
Lemma O_set_idp (A : AType * AType) (v : 'Hom('Ha A.2, 'Ha A.1)) : O_set v (A.1,A.2) = v.
Proof. by case: A v=>A1 A2 /= v; rewrite O_set_id. Qed.
Lemma O_set_neq (A : AType * AType) (v : 'Hom('Ha A.2, 'Ha A.1)) A' : 
  A != A' -> O_set v A' = 0.
Proof. by move=>/eqP P; rewrite /O_set; case: eqP. Qed.

Notation A_value ca := (@A_value atype eval_AT aname ca).
Notation ST_value := (@ST_value atype eval_AT stname cst).
Notation S_value := (@S_value sname).
Notation K_value := (@K_value atype eval_AT kname ck).
Notation B_value := (@B_value atype eval_AT bname cb).
Notation O_value := (@O_value atype eval_AT oname co).

Fixpoint A_sem (ca : Gamma_A) (av : A_value ca) (a : A_base) : A_sem_type :=
  match a with
  | A_var n => A_set (av n)
  | A_ground A a => A_set a
  | A_pair a1 a2 =>
      match atype_checker ca a1, atype_checker ca a2 with
      | Some T1, Some T2 => A_set (((A_sem av a1 T1), (A_sem av a2 T2)) : eval_AType (Apair T1 T2))
      | _, _ => A_sem0
      end
  | A_fst a =>
      match atype_checker ca a with
      | Some (Apair T1 T2) => A_set ((A_sem av a (Apair T1 T2)).1 : eval_AType T1)
      | _ => A_sem0
      end
  | A_snd a =>
      match atype_checker ca a with
      | Some (Apair T1 T2) => A_set ((A_sem av a (Apair T1 T2)).2 : eval_AType T2)
      | _ => A_sem0
      end
  end.

Fixpoint ST_sem (ca : Gamma_A) (stv : ST_value) (st : ST_syn) :=
  match st with
  | ST_var n => ST_set (stv n)
  | ST_uni A => ST_sem1
  | ST_prod S1 S2 => 
      match sttype_checker ca S1, sttype_checker ca S2 with
      | Some A1, Some A2 => 
          ST_set (setX (ST_sem ca stv S1 A1) (ST_sem ca stv S2 A2) : {set eval_AType (Apair A1 A2)})
      | _, _ => ST_sem1
      end
  end.

(* Lemma Ha_unfold (A : AType) : 'Hs (eval_AType A) = 'Ha A.
Proof. by rewrite HA.unlock. Qed. *)

(* Definition cast_Ha_ground (A : AType) (v : 'Hs (eval_AType A)) : 'Ha A :=
  let: erefl in _ = H' := Ha_unfold A return H' in v. *)

(* Variable (ca : Gamma_A) (av : A_value ca) (sv : S_value) (kv : K_value) 
  (bv : B_value) (ov : O_value) (k : K_ket) (t : A_base) (T : AType).
  Check V_set (''(A_sem av t T)).
Variable (T1 T2 : AType) (v1 : 'Ha T1) (v2 : 'Ha T2).
Check v1 ⊗t v2 : 'Ha (Apair T1 T2). *)

Variable (stv : ST_value) (sv : S_value) (kv : K_value) (bv : B_value) (ov : O_value).

Fixpoint S_sem ca (av : A_value ca) (s : S_scalar) {struct s}: C :=
  match s with
    | S_var n => sv n
    | S_0 => 0
    | S_1 => 1
    | S_delta a1 a2 =>
        match atype_checker ca a1, atype_checker ca a2 with
        | Some A1, Some A2 => if A1 == A2 then 
                                (A_sem av a1 A1 == A_sem av a2 A1)%:R
                              else 0
        | _, _ => 0
        end
    | S_add s1 s2 =>
        match stype_checker ca s1, stype_checker ca s2 with
        | Some DScale, Some DScale => S_sem av s1 + 
                                      S_sem av s2
        | _, _ => 0
        end
    (* | S_opp (s : S_scalar) *)
    | S_mul s1 s2 =>
        match stype_checker ca s1, stype_checker ca s2 with
        | Some DScale, Some DScale => S_sem av s1 *
                                      S_sem av s2
        | _, _ => 0
        end
    | S_conj s => 
        match stype_checker ca s with
        | Some DScale => (S_sem av s)^*
        | _ => 0
        end
    | BK_inner b k =>
        match btype_checker ca b, ktype_checker ca k with
        | Some (DBra t1), Some (DKet t2) =>
            if t1 == t2 then
              [< (B_sem av b t1)^*v ;
                 (K_sem av k t1) >]
            else 0
        | _, _ => 0
        end
    | S_sum st n s =>
        match sttype_checker ca st with
        | Some A => (* ca := (Gamma_A_update ca n A) *)
            \sum_(i in ST_sem ca stv st A) S_sem (A_value_update av n i) s
        | _ => 0
        end
  end
with K_sem ca (av : A_value ca) (k : K_ket) {struct k}: V_sem_type :=
  match k with
    | K_var n => V_set (kv n)
    | K_0 A => V_sem0
    | K_ground t =>
        match atype_checker ca t with
        | Some T => V_set (''(A_sem av t T) : 'Ha T)
        | _ => V_sem0
        end
    | B_adj b =>
        match btype_checker ca b with
        | Some (DBra T) => V_set (B_sem av b T)^*v
        | _ => V_sem0
        end
    | K_scale s k =>
        match stype_checker ca s, ktype_checker ca k with
        | Some DScale, Some (DKet t) =>
            V_set ((S_sem av s) *: (K_sem av k t))
        | _,_ => V_sem0
        end
    | K_add k1 k2 =>
        match ktype_checker ca k1, ktype_checker ca k2 with
        | Some (DKet t1), Some (DKet t2) =>
            if t1 == t2 then 
              V_set ((K_sem av k1 t1) + (K_sem av k2 t1))
            else V_sem0
        | _, _ => V_sem0
        end
    | K_apply o k =>
        match otype_checker ca o, ktype_checker ca k with
        | Some (DOpt t), Some (DKet t3) =>
            if t.2 == t3 then
              V_set ((O_sem av o t) (K_sem av k t.2))
            else V_sem0
        | _, _ => V_sem0
        end
    | K_ten k1 k2 =>
        match ktype_checker ca k1, ktype_checker ca k2 with
        | Some (DKet t1), Some (DKet t2) =>
            V_set ((K_sem av k1 t1) ⊗t (K_sem av k2 t2) : 'Ha (Apair t1 t2))
        | _, _ => V_sem0
        end
    | K_sum st n k =>
        match sttype_checker ca st with
        | Some A => (* ca := (Gamma_A_update ca n A) *)
            match ktype_checker (Gamma_A_update ca n A) k with
            | Some (DKet t) => V_set (\sum_(i in ST_sem ca stv st A) K_sem (A_value_update av n i) k t)
            | _ => V_sem0
            end
        | _ => V_sem0
        end
  end
with B_sem ca (av : A_value ca) (b : B_bra) {struct b}: V_sem_type :=
  match b with
    | B_var n => V_set (bv n)
    | B_0 A => V_sem0
    | B_ground t =>
        match atype_checker ca t with
        | Some T => V_set (''(A_sem av t T) : 'Ha T)
        | _ => V_sem0
        end
    | K_adj k =>
        match ktype_checker ca k with
        | Some (DKet T) => V_set (K_sem av k T)^*v
        | _ => V_sem0
        end
    | B_scale s b =>
        match stype_checker ca s, btype_checker ca b with
        | Some DScale, Some (DBra t) =>
            V_set ((S_sem av s) *: (B_sem av b t))
        | _,_ => V_sem0
        end
    | B_add b1 b2 =>
        match btype_checker ca b1, btype_checker ca b2 with
        | Some (DBra t1), Some (DBra t2) =>
            if t1 == t2 then 
              V_set ((B_sem av b1 t1) + (B_sem av b2 t1))
            else V_sem0
        | _, _ => V_sem0
        end
    | B_apply b o =>
        match btype_checker ca b, otype_checker ca o with
        | Some (DBra t1), Some (DOpt t) =>
            if t1 == t.1 then 
              V_set ((O_sem av o t)^T (B_sem av b t.1))
            else V_sem0
        | _, _ => V_sem0
        end
    | B_ten b1 b2 =>
        match btype_checker ca b1, btype_checker ca b2 with
        | Some (DBra t1), Some (DBra t2) =>
            V_set ((B_sem av b1 t1) ⊗t (B_sem av b2 t2) : 'Ha (Apair t1 t2))
        | _, _ => V_sem0
        end
    | B_sum st n b =>
        match sttype_checker ca st with
        | Some A => (* ca := (Gamma_A_update ca n A) *)
            match btype_checker (Gamma_A_update ca n A) b with
            | Some (DBra t) => V_set (\sum_(i in ST_sem ca stv st A) B_sem (A_value_update av n i) b t)
            | _ => V_sem0
            end
        | _ => V_sem0
        end
  end
with O_sem ca (av : A_value ca) (o : O_opt) {struct o}: O_sem_type :=
  match o with
    | O_var n => O_set (ov n)
    | O_0 T1 T2 => O_sem0
    | O_1 T => 
        match AT_sem ca T with
        | Some T => @O_set (T,T) (\1 : 'End('Ha T))
        | _ => O_sem0
        end
    | KB_outer k b =>
        match ktype_checker ca k, btype_checker ca b with
        | Some (DKet t1), Some (DBra t2) =>
            @O_set (t1,t2) ([> K_sem av k t1 ; (B_sem av b t2)^*v <])
        | _, _ => O_sem0
        end
    | O_adj o =>
        match otype_checker ca o with
        | Some (DOpt t) => @O_set (t.2,t.1) (O_sem av o t)^A
        | _ => O_sem0
        end
    | O_scale s o =>
        match stype_checker ca s, otype_checker ca o with
        | Some DScale, Some (DOpt t) => 
            O_set ((S_sem av s) *: (O_sem av o t))
        | _,_ => O_sem0
        end
    | O_add o1 o2 =>
        match otype_checker ca o1, otype_checker ca o2 with
        | Some (DOpt t1), Some (DOpt t2) =>
            if (t1 == t2) then 
              O_set ((O_sem av o1 t1) + (O_sem av o2 t1))
            else O_sem0
        | _, _ => O_sem0
        end
    | O_comp o1 o2 =>
        match otype_checker ca o1, otype_checker ca o2 with
        | Some (DOpt t1), Some (DOpt t2) =>
            if (t1.2 == t2.1) then 
              @O_set (t1.1, t2.2) ((O_sem av o1 t1) \o (O_sem av o2 (t1.2, t2.2)))
            else O_sem0
        | _, _ => O_sem0
        end
    | O_ten o1 o2 =>
        match otype_checker ca o1, otype_checker ca o2 with
        | Some (DOpt t1), Some (DOpt t2) =>
            @O_set ((Apair t1.1 t2.1), (Apair t1.2 t2.2)) ((O_sem av o1 t1) ⊗f (O_sem av o2 t2))
        | _, _ => O_sem0
        end
    | O_sum st n o =>
        match sttype_checker ca st with
        | Some A => (* ca := (Gamma_A_update ca n A)  \sum_(n : A) *)
            match otype_checker (Gamma_A_update ca n A) o with
            | Some (DOpt t) => O_set (\sum_(i in ST_sem ca stv st A) O_sem (A_value_update av n i) o t)
            | _ => O_sem0
            end
        | _ => O_sem0
        end
  end.

Section Relation_L1_L2.

Fixpoint L1_L2_A_base (ca : Gamma_A) (A : AType) (a : Playground1.A_base eval_AT (ca := ca) A) : A_base :=
  match a with
  | Playground1.A_var n => A_var n
  | Playground1.A_ground A a => A_ground a
  | Playground1.A_pair A1 A2 a1 a2 => A_pair (L1_L2_A_base a1) (L1_L2_A_base a2)
  | Playground1.A_fst A1 A2 a => A_fst (L1_L2_A_base a)
  | Playground1.A_snd A1 A2 a => A_snd (L1_L2_A_base a)
  end.

Fixpoint L1_L2_ST_syn (A : AType) (a : Playground1.ST_syn cst A) : ST_syn :=
  match a with
  | Playground1.ST_var n => ST_var n
  | Playground1.ST_uni A => ST_uni (AT_ground A)
  | Playground1.ST_prod A1 A2 S1 S2 => ST_prod (L1_L2_ST_syn S1) (L1_L2_ST_syn S2)
  end.

Fixpoint L1_L2_S_scalar (ca : Gamma_A) (s : Playground1.S_scalar eval_AT sname cst ck cb co (ca := ca)) : S_scalar :=
  match s with
    | Playground1.S_var n => S_var n
    | Playground1.S_0 => S_0
    | Playground1.S_1 => S_1
    | Playground1.S_delta A a1 a2 => S_delta (L1_L2_A_base a1) (L1_L2_A_base a2)
    | Playground1.S_add s1 s2 => S_add (L1_L2_S_scalar s1) (L1_L2_S_scalar s2)
    | Playground1.S_mul s1 s2 => S_mul (L1_L2_S_scalar s1) (L1_L2_S_scalar s2)
    | Playground1.S_conj s => S_conj (L1_L2_S_scalar s)
    | Playground1.BK_inner A b k => BK_inner (L1_L2_B_bra b) (L1_L2_K_ket k)
    | Playground1.S_sum A st n s =>
        S_sum (L1_L2_ST_syn st) n (L1_L2_S_scalar s)
  end
with L1_L2_K_ket (ca : Gamma_A) A (k : Playground1.K_ket eval_AT sname cst ck cb co (ca := ca) A) : K_ket :=
  match k with
    | Playground1.K_var n => K_var n
    | Playground1.K_0 A => K_0 (AT_ground A)
    | Playground1.K_ground A a => K_ground (L1_L2_A_base a)
    | Playground1.B_adj A b => B_adj (L1_L2_B_bra b)
    | Playground1.K_scale s A k => K_scale (L1_L2_S_scalar s) (L1_L2_K_ket k)
    | Playground1.K_add A k1 k2 => K_add (L1_L2_K_ket k1) (L1_L2_K_ket k2)
    | Playground1.K_apply A1 A2 o k => K_apply (L1_L2_O_opt o) (L1_L2_K_ket k)
    | Playground1.K_ten A1 A2 k1 k2 => K_ten (L1_L2_K_ket k1) (L1_L2_K_ket k2)
    | Playground1.K_sum As A st n k =>
        K_sum (L1_L2_ST_syn st) n (L1_L2_K_ket k)
  end
with L1_L2_B_bra (ca : Gamma_A) A (b : Playground1.B_bra eval_AT sname cst ck cb co (ca := ca) A) : B_bra :=
  match b with
    | Playground1.B_var n => B_var n
    | Playground1.B_0 A => B_0 (AT_ground A)
    | Playground1.B_ground A a => B_ground (L1_L2_A_base a)
    | Playground1.K_adj A k => K_adj (L1_L2_K_ket k)
    | Playground1.B_scale s A b => B_scale (L1_L2_S_scalar s) (L1_L2_B_bra b)
    | Playground1.B_add A b1 b2 => B_add (L1_L2_B_bra b1) (L1_L2_B_bra b2)
    | Playground1.B_apply A1 A2 b o => B_apply (L1_L2_B_bra b) (L1_L2_O_opt o)
    | Playground1.B_ten A1 A2 b1 b2 => B_ten (L1_L2_B_bra b1) (L1_L2_B_bra b2)
    | Playground1.B_sum As A st n b =>
        B_sum (L1_L2_ST_syn st) n (L1_L2_B_bra b)
  end
with L1_L2_O_opt (ca : Gamma_A) A1 A2 (o : Playground1.O_opt eval_AT sname cst ck cb co (ca := ca) A1 A2) : O_opt :=
  match o with
    | Playground1.O_var n => O_var n
    | Playground1.O_0 A1 A2 => O_0 (AT_ground A1) (AT_ground A2)
    | Playground1.O_1 A => O_1 (AT_ground A)
    | Playground1.KB_outer A1 A2 k b => KB_outer (L1_L2_K_ket k) (L1_L2_B_bra b)
    | Playground1.O_adj A1 A2 o => O_adj (L1_L2_O_opt o)
    | Playground1.O_scale s A1 A2 o => O_scale (L1_L2_S_scalar s) (L1_L2_O_opt o)
    | Playground1.O_add A1 A2 o1 o2 => O_add (L1_L2_O_opt o1) (L1_L2_O_opt o2)
    | Playground1.O_comp A1 A2 A3 o1 o2 => O_comp (L1_L2_O_opt o1) (L1_L2_O_opt o2)
    | Playground1.O_ten A1 A2 A3 A4 o1 o2 => O_ten (L1_L2_O_opt o1) (L1_L2_O_opt o2)
    | Playground1.O_sum As A1 A2 st n o =>
        O_sum (L1_L2_ST_syn st) n (L1_L2_O_opt o)
  end.

Lemma L1_L2_A_type (ca : Gamma_A) (A : AType) (a : Playground1.A_base eval_AT (ca := ca) A) :
  atype_checker ca (L1_L2_A_base a) = Some A.
Proof.
elim: a=>//.
by move=> /= A1 A2 a1 -> a2 ->.
by move=> /= A1 A2 a ->.
by move=> /= A1 A2 a ->.
Qed.

Lemma L1_L2_ST_type (ca : Gamma_A) (A : AType) (s : Playground1.ST_syn cst A) :
  sttype_checker ca (L1_L2_ST_syn s) = Some A.
Proof.
elim: s=>//.
by move=> /= A1 A2 S1 -> S2 ->.
Qed.

Let L1_L2_S_type_eq ca (s : Playground1.S_scalar eval_AT sname cst ck cb co) :=
  stype_checker ca (L1_L2_S_scalar (ca := ca) s) = Some DScale.
Let L1_L2_K_type_eq ca A (k : Playground1.K_ket eval_AT sname cst ck cb co A) :=
  ktype_checker ca (L1_L2_K_ket (ca := ca) k) = Some (DKet A).
Let L1_L2_B_type_eq ca A (b : Playground1.B_bra eval_AT sname cst ck cb co A) :=
  btype_checker ca (L1_L2_B_bra (ca := ca) b) = Some (DBra A).
Let L1_L2_O_type_eq ca A1 A2 (o : Playground1.O_opt eval_AT sname cst ck cb co A1 A2) :=
  otype_checker ca (L1_L2_O_opt (ca := ca) o) = Some (DOpt (A1,A2)).

Lemma L1_L2_All_type ca : 
  (forall s, @L1_L2_S_type_eq ca s) /\ 
  (forall A k, @L1_L2_K_type_eq ca A k) /\
  (forall A b, @L1_L2_B_type_eq ca A b) /\
  (forall A1 A2 o, @L1_L2_O_type_eq ca A1 A2 o).
Proof.
move: ca; apply Playground1.All_syn_mutind=>//; 
rewrite /L1_L2_S_type_eq /L1_L2_B_type_eq /L1_L2_K_type_eq /L1_L2_O_type_eq.
(* about scalar *)
- by move=> /= ca A a1 a2; rewrite !L1_L2_A_type eqxx.
- by move=> /= ca s1 -> s2 ->.
- by move=> /= ca s1 -> s2 ->.
- by move=> /= ca A b -> k ->; rewrite eqxx.
- by move=> /= ca A st n s; rewrite L1_L2_ST_type.
(* about ket *)
- by move=> /= ca A a; rewrite L1_L2_A_type.
- by move=> /= ca A b ->.
- by move=> /= ca s -> A k ->.
- by move=> /= ca A k1 -> k2 ->; rewrite eqxx.
- by move=> /= ca A1 A2 o -> k ->; rewrite /= eqxx.
- by move=> /= ca A1 A2 k1 -> k2 ->.
- by move=> /= ca As A st n k; rewrite L1_L2_ST_type.
(* about bra *)
- by move=> /= ca A a; rewrite L1_L2_A_type.
- by move=> /= ca A k ->.
- by move=> /= ca s -> A b ->.
- by move=> /= ca A b1 -> b2 ->; rewrite eqxx.
- by move=> /= ca A1 A2 b -> o ->; rewrite /= eqxx.
- by move=> /= ca A1 A2 b1 -> b2 ->.
- by move=> /= ca As A st n b; rewrite L1_L2_ST_type.
(* about opt *)
- by move=> /= ca n; rewrite -surjective_pairing.
- by move=> /= ca A1 A2 k -> b ->.
- by move=> /= ca A1 A2 o ->.
- by move=> /= ca s -> A1 A2 o ->.
- by move=> /= ca A1 A2 o1 -> o2 ->; rewrite eqxx.
- by move=> /= ca A1 A2 A3 o1 -> o2 ->; rewrite /= eqxx.
- by move=> /= ca A1 A2 A3 A4 o1 -> o2 ->.
- by move=> /= ca As A1 A2 st n o; rewrite L1_L2_ST_type.
Qed.

Lemma L1_L2_S_type ca (s : Playground1.S_scalar eval_AT sname cst ck cb co) :
  stype_checker ca (L1_L2_S_scalar (ca := ca) s) = Some DScale.
Proof. by move: (L1_L2_All_type ca) s=>[]. Qed.

Lemma L1_L2_K_type ca A (k : Playground1.K_ket eval_AT sname cst ck cb co A) :
  ktype_checker ca (L1_L2_K_ket (ca := ca) k) = Some (DKet A).
Proof. by move: (L1_L2_All_type ca) A k=>[] _ []. Qed.

Lemma L1_L2_B_type ca A (b : Playground1.B_bra eval_AT sname cst ck cb co A) :
  btype_checker ca (L1_L2_B_bra (ca := ca) b) = Some (DBra A).
Proof. by move: (L1_L2_All_type ca) A b=>[] _ [] _ []. Qed.

Lemma L1_L2_O_type ca A1 A2 (o : Playground1.O_opt eval_AT sname cst ck cb co A1 A2) :
  otype_checker ca (L1_L2_O_opt (ca := ca) o) = Some (DOpt (A1,A2)).
Proof. by move: (L1_L2_All_type ca) A1 A2 o=>[] _ [] _ []. Qed.

Lemma L1_L2_A_sem (ca : Gamma_A) (A : AType) 
  (a : Playground1.A_base eval_AT (ca := ca) A) (av : A_value ca) :
  A_sem av (L1_L2_A_base a) A = Playground1.A_sem av a.
Proof.
elim: a=>//; clear A.
by move=> /= n; rewrite A_set_id.
by move=> /= A a; rewrite A_set_id.
by move=> /= A1 A2 a1 + a2; rewrite !L1_L2_A_type A_set_id=>->->.
by move=> /= A1 A2 a; rewrite L1_L2_A_type A_set_id=>->.
by move=> /= A1 A2 a; rewrite L1_L2_A_type A_set_id=>->.
Qed.

Lemma L1_L2_ST_sem (ca : Gamma_A) (A : AType) (s : Playground1.ST_syn cst A) :
  ST_sem ca stv (L1_L2_ST_syn s) A = Playground1.ST_sem stv s.
Proof.
elim: s=>//; clear A.
by move=> /= n; rewrite ST_set_id.
by move=> /= A1 A2 S1 + S2; rewrite !L1_L2_ST_type ST_set_id=>->->.
Qed.

Let L1_L2_S_sem_eq ca (s : Playground1.S_scalar eval_AT sname cst ck cb co) :=
  forall av : A_value ca, S_sem av (L1_L2_S_scalar s) = Playground1.S_sem stv sv kv bv ov av s.
Let L1_L2_K_sem_eq ca A (k : Playground1.K_ket eval_AT sname cst ck cb co A) :=
  forall av : A_value ca, K_sem av (L1_L2_K_ket k) A = Playground1.K_sem stv sv kv bv ov av k.
Let L1_L2_B_sem_eq ca A (b : Playground1.B_bra eval_AT sname cst ck cb co A) :=
  forall av : A_value ca, B_sem av (L1_L2_B_bra b) A = Playground1.B_sem stv sv kv bv ov av b.
Let L1_L2_O_sem_eq ca A1 A2 (o : Playground1.O_opt eval_AT sname cst ck cb co A1 A2) :=
  forall av : A_value ca, O_sem av (L1_L2_O_opt o) (A1, A2) = Playground1.O_sem stv sv kv bv ov av o.

Lemma L1_L2_All_sem ca : 
  (forall s, @L1_L2_S_sem_eq ca s) /\ 
  (forall A k, @L1_L2_K_sem_eq ca A k) /\
  (forall A b, @L1_L2_B_sem_eq ca A b) /\
  (forall A1 A2 o, @L1_L2_O_sem_eq ca A1 A2 o).
Proof.
move: ca; apply Playground1.All_syn_mutind=>//; 
rewrite /L1_L2_S_sem_eq /L1_L2_K_sem_eq /L1_L2_B_sem_eq /L1_L2_O_sem_eq.
(* about scalar *)
- by move=> /= ca A a1 a2 av; rewrite !L1_L2_A_type eqxx !L1_L2_A_sem.
- by move=> /= ca s1 IH1 s2 IH2 av; rewrite !L1_L2_S_type IH1 IH2.
- by move=> /= ca s1 IH1 s2 IH2 av; rewrite !L1_L2_S_type IH1 IH2.
- by move=> /= ca s IH av; rewrite L1_L2_S_type IH.
- by move=> /= ca A b IHb k IHk av; rewrite L1_L2_B_type L1_L2_K_type eqxx IHb IHk.
- move=> /= ca A st n s IH av; rewrite L1_L2_ST_type L1_L2_ST_sem.
  by under eq_bigr do rewrite IH.
(* about ket *)
- by move=> /= ca n av; rewrite V_set_id.
- by move=> /= ca A a av; rewrite L1_L2_A_type V_set_id L1_L2_A_sem.
- by move=> /= ca A b IH av; rewrite L1_L2_B_type V_set_id IH.
- by move=> /= ca s IHs A k IHk av; rewrite L1_L2_S_type L1_L2_K_type V_set_id IHs IHk.
- by move=> /= ca A k1 IH1 k2 IH2 av; rewrite !L1_L2_K_type eqxx V_set_id IH1 IH2.
- by move=> /= ca A1 A2 o IHo k IHk av; 
  rewrite L1_L2_O_type L1_L2_K_type/= eqxx V_set_id IHo IHk.
- by move=> /= ca A1 A2 k1 IH1 k2 IH2 av; rewrite !L1_L2_K_type V_set_id IH1 IH2.
- move=> /= ca As A st n k IH av; rewrite L1_L2_ST_type L1_L2_K_type V_set_id L1_L2_ST_sem.
  by under eq_bigr do rewrite IH.
(* about bra *)
- by move=> /= ca n av; rewrite V_set_id.
- by move=> /= ca A a av; rewrite L1_L2_A_type V_set_id L1_L2_A_sem.
- by move=> /= ca A k IH av; rewrite L1_L2_K_type V_set_id IH.
- by move=> /= ca s IHs A b IHb av; rewrite L1_L2_S_type L1_L2_B_type V_set_id IHs IHb.
- by move=> /= ca A b1 IH1 b2 IH2 av; rewrite !L1_L2_B_type eqxx V_set_id IH1 IH2.
- by move=> /= ca A1 A2 o IHo b IHb av; 
  rewrite L1_L2_O_type L1_L2_B_type/= eqxx V_set_id IHo IHb.
- by move=> /= ca A1 A2 b1 IH1 b2 IH2 av; rewrite !L1_L2_B_type V_set_id IH1 IH2.
- move=> /= ca As A st n b IH av; rewrite L1_L2_ST_type L1_L2_B_type V_set_id L1_L2_ST_sem.
  by under eq_bigr do rewrite IH.
(* about opt *)
- by move=> /= ca n av; rewrite O_set_idp.
- by move=> /= ca A av; rewrite O_set_idp.
- by move=> /= ca A1 A2 k IHk b IHb av; rewrite L1_L2_K_type L1_L2_B_type O_set_idp IHk IHb.
- by move=> /= ca A1 A2 o IH av; rewrite L1_L2_O_type O_set_idp IH.
- by move=> /= ca s IHs A1 A2 o IHo av; rewrite L1_L2_S_type L1_L2_O_type O_set_idp IHs IHo.
- by move=> /= ca A1 A2 o1 IH1 o2 IH2 av; rewrite !L1_L2_O_type eqxx O_set_idp IH1 IH2.
- by move=> /= ca A1 A2 A3 o1 IH1 o2 IH2 av; rewrite !L1_L2_O_type/= eqxx O_set_idp IH1 IH2.
- by move=> /= ca A1 A2 A3 A4 o1 IH1 o2 IH2 av; rewrite !L1_L2_O_type O_set_idp IH1 IH2.
- move=> /= ca As A1 A2 st n o IH av; rewrite L1_L2_ST_type L1_L2_O_type O_set_idp L1_L2_ST_sem.
  by under eq_bigr do rewrite IH.
Qed.

Lemma L1_L2_S_sem ca (s : Playground1.S_scalar eval_AT sname cst ck cb co) (av : A_value ca) :
  S_sem av (L1_L2_S_scalar s) = Playground1.S_sem stv sv kv bv ov av s.
Proof. by move: (L1_L2_All_sem ca) s av=>[]. Qed.

Lemma L1_L2_K_sem ca A (k : Playground1.K_ket eval_AT sname cst ck cb co A) (av : A_value ca) :
  K_sem av (L1_L2_K_ket k) A = Playground1.K_sem stv sv kv bv ov av k.
Proof. by move: (L1_L2_All_sem ca) A k av=>[] _ []. Qed.

Lemma L1_L2_B_sem ca A (b : Playground1.B_bra eval_AT sname cst ck cb co A) (av : A_value ca) :
  B_sem av (L1_L2_B_bra b) A = Playground1.B_sem stv sv kv bv ov av b.
Proof. by move: (L1_L2_All_sem ca) A b av=>[] _ [] _ []. Qed.

Lemma L1_L2_O_sem ca A1 A2 (o : Playground1.O_opt eval_AT sname cst ck cb co A1 A2) (av : A_value ca) :
  O_sem av (L1_L2_O_opt o) (A1, A2) = Playground1.O_sem stv sv kv bv ov av o.
Proof. by move: (L1_L2_All_sem ca) A1 A2 o av=>[] _ [] _ []. Qed.

End Relation_L1_L2.

Declare Scope sttype_scope.
Delimit Scope sttype_scope with ST.

Notation "A * B" := (ST_prod A%ST B%ST) : sttype_scope.
Notation "'`' n" := (ST_var n) (at level 2, format "'`' n") : sttype_scope.
Notation "'U(' A )" := (ST_uni A%AT) (at level 30, format "'U(' A ')'") : sttype_scope.

Notation "A * B" := (Apair A%TA B%TA) : atype_scope.


Notation "'`' n" := (A_var n) (at level 2, format "'`' n") : base_scope.
Notation "''A(' a )" := (A_ground a%TA) (at level 30, format "''A(' a ')'") : base_scope.
Notation "( x , y , .. , z )" := (A_pair .. (A_pair x%DA y%DA) .. z%DA) : base_scope.
Notation "a '.1'" := (A_fst a%DA) : base_scope.
Notation "a '.2'" := (A_snd a%DA) : base_scope.

Notation "''A(' A )" := (AT_ground A%TA) : atsyn_scope.
Notation "A * B" := (AT_pair A%AT B%AT) : atsyn_scope.
Notation "'π1(' A )" := (AT_proj1 A%AT) : atsyn_scope.
Notation "'π2(' A )" := (AT_proj2 A%AT) : atsyn_scope.
Notation "'πK(' T )" := (AT_ket T%DT) : atsyn_scope.
Notation "'πB(' T )" := (AT_bra T%DT) : atsyn_scope.
Notation "'πS(' T )" := (AT_set T%AT) : atsyn_scope.
Notation "'type(' t )" := (AT_get t%DA) : atsyn_scope.
Notation "'typeSet(' S )" := (AT_st_get S%ST) : atsyn_scope.
Notation "'ST'" := (DT_scale) : dtsyn_scope.
Notation "'KT(' A )" := (DT_ket A%AT) : dtsyn_scope.
Notation "'BT(' A )" := (DT_bra A%AT) : dtsyn_scope.
Notation "'OT(' A1 , A2 )" := (DT_opt A1%AT A2%AT) : dtsyn_scope.
Notation "'typeS(' S )" := (DT_s_get S%DS) : dtsyn_scope.
Notation "'typeK(' K )" := (DT_k_get K%DK) : dtsyn_scope.
Notation "'typeB(' B )" := (DT_b_get B%DB) : dtsyn_scope.
Notation "'typeO(' O )" := (DT_o_get O%DO) : dtsyn_scope.

Notation "'`' n" := (S_var n) (at level 2, format "'`' n") : scalar_scope.
Notation "0" := (S_0) : scalar_scope.
Notation "1" := (S_1) : scalar_scope.
Notation "'δ(' a ',' b ')'" := (S_delta a%DA b%DA) (at level 30, format "'δ(' a ','  b ')'") : scalar_scope.
Notation "a + b" := (S_add a%DS b%DS) (at level 50, left associativity) : scalar_scope.
Notation "a * b" := (S_mul a%DS b%DS) (at level 40, left associativity) : scalar_scope.
Notation "s '^*'" := (S_conj s%DS) (at level 2) : scalar_scope.
Notation "b '·' k" := (BK_inner b%DB k%DK) (at level 40) : scalar_scope.

Notation "'`' n" := (K_var n) (at level 2, format "'`' n") : ket_scope.
Notation "'0_(' A )" := (@K_0 A%AT) (at level 8, format "0_( A )"): ket_scope.
Notation "''|' a >" := (K_ground a%DA) : ket_scope.
Notation "b '^A'" := (B_adj b%DB) (at level 8) : ket_scope.
Notation "c '*:' k" := (K_scale c%DS k%DK) (at level 40) : ket_scope.
Notation "a + b" := (K_add a%DK b%DK) (at level 50, left associativity) : ket_scope.
Notation "o '·' k" := (K_apply o%DO k%DK) (at level 40) : ket_scope.
Notation "k1 ⊗ k2" := (K_ten k1%DK k2%DK) (at level 45) : ket_scope.

Notation "'`' n" := (B_var n) (at level 2, format "'`' n") : bra_scope.
Notation "'0_(' A )" := (@B_0 A%AT) (at level 8, format "0_( A )"): bra_scope.
Notation "''<' a |" := (B_ground a%DA) : bra_scope.
Notation "k '^A'" := (K_adj k%DK) (at level 8) : bra_scope.
Notation "c '*:' b" := (B_scale c%DS b%DB) (at level 40) : bra_scope.
Notation "a + b" := (B_add a%DB b%DB) (at level 50, left associativity) : bra_scope.
Notation "b '·' o" := (B_apply b%DB o%DO) (at level 40) : bra_scope.
Notation "b1 ⊗ b2" := (B_ten b1%DB b2%DB) (at level 45) : bra_scope.

Notation "'`' n" := (O_var n) (at level 2, format "'`' n") : opt_scope.
Notation "'0_(' A1 , A2 )" := (@O_0 A1%AT A2%AT) (at level 8, format "0_( A1 , A2 )") : opt_scope.
Notation "'1_(' A )" := (@O_1 A%AT) (at level 8, format "1_( A )") : opt_scope.
Notation "k '··' b" := (KB_outer k%DK b%DB) (at level 40) : opt_scope.
Notation "o '^A'" := (O_adj o%DO) (at level 8) : opt_scope.
Notation "c '*:' o" := (O_scale c%DS o%DO) (at level 40) : opt_scope.
Notation "a + b" := (O_add a%DO b%DO) (at level 50, left associativity) : opt_scope.
Notation "o1 '·' o2" := (O_comp o1%DO o2%DO) (at level 40) : opt_scope.
Notation "o1 ⊗ o2" := (O_ten o1%DO o2%DO) (at level 45) : opt_scope.

Section Term_Rewriting_System.

Implicit Type (ca : Gamma_A).

Definition base_eq ca1 (av1 : A_value ca1) ca2 (av2 : A_value ca2) (s t : A_base) :=
  if atype_checker ca1 s is Some A then
    atype_checker ca1 s = atype_checker ca2 t /\ A_sem av1 s = A_sem av2 t
  else True.

Definition scalar_eq ca1 (av1 : A_value ca1) ca2 (av2 : A_value ca2) (s t : S_scalar) :=
  if stype_checker ca1 s is Some DScale then
    stype_checker ca1 s = stype_checker ca2 t /\ S_sem av1 s = S_sem av2 t
  else True.

Definition ket_eq ca1 (av1 : A_value ca1) ca2 (av2 : A_value ca2) (s t : K_ket) :=
  if ktype_checker ca1 s is Some (DKet A) then
    ktype_checker ca1 s = ktype_checker ca2 t /\ K_sem av1 s = K_sem av2 t
  else True.

Definition bra_eq ca1 (av1 : A_value ca1) ca2 (av2 : A_value ca2) (s t : B_bra) :=
  if btype_checker ca1 s is Some (DBra A) then
    btype_checker ca1 s = btype_checker ca2 t /\ B_sem av1 s = B_sem av2 t
  else True.

Definition opt_eq ca1 (av1 : A_value ca1) ca2 (av2 : A_value ca2) (s t : O_opt) :=
  if otype_checker ca1 s is Some (DOpt A) then
    otype_checker ca1 s = otype_checker ca2 t /\ O_sem av1 s = O_sem av2 t
  else True.

Notation "A '=a' B >> av1 , av2" := (base_eq av1 av2 A%DA B%DA) (at level 70, av1 at next level, av2 at next level).
Notation "A '=s' B >> av1 , av2" := (scalar_eq av1 av2 A%DS B%DS) (at level 70, av1 at next level, av2 at next level).
Notation "A '=k' B >> av1 , av2" := (ket_eq av1 av2 A%DK B%DK) (at level 70, av1 at next level, av2 at next level).
Notation "A '=b' B >> av1 , av2" := (bra_eq av1 av2 A%DB B%DB) (at level 70, av1 at next level, av2 at next level).
Notation "A '=o' B >> av1 , av2" := (opt_eq av1 av2 A%DO B%DO) (at level 70, av1 at next level, av2 at next level).

Notation "A '=a' B >> av" := (base_eq av av A%DA B%DA) (at level 70, av at next level).
Notation "A '=s' B >> av" := (scalar_eq av av A%DS B%DS) (at level 70, av at next level).
Notation "A '=k' B >> av" := (ket_eq av av A%DK B%DK) (at level 70, av at next level).
Notation "A '=b' B >> av" := (bra_eq av av A%DB B%DB) (at level 70, av at next level).
Notation "A '=o' B >> av" := (opt_eq av av A%DO B%DO) (at level 70, av at next level).

Ltac l0 := let x := fresh "x" in
           set x := (atype_checker _ _);
           rewrite /x; clear x;
           let E := fresh "E" in
           let A := fresh "A" in
           case E : (atype_checker _ _)=>[A|]=>//.
Ltac l1 := let x := fresh "x" in
           set x := (stype_checker _ _);
           rewrite /x; clear x;
           let E := fresh "E" in
           let A := fresh "A" in
           case E : (stype_checker _ _)=>[[|||]|]=>//.
Ltac l2 := let x := fresh "x" in
           set x := (ktype_checker _ _);
           rewrite /x; clear x;
           let E := fresh "E" in
           let A := fresh "A" in
           case E : (ktype_checker _ _)=>[[|A||]|]=>//.
Ltac l3 := let x := fresh "x" in
           set x := (btype_checker _ _);
           rewrite /x; clear x;
           let E := fresh "E" in
           let A := fresh "A" in
           case E : (btype_checker _ _)=>[[||A|]|]=>//.
Ltac l4 := let x := fresh "x" in
           set x := (otype_checker _ _);
           rewrite /x; clear x;
           let E := fresh "E" in
           let A1 := fresh "A" in
           let A2 := fresh "A" in
           case E : (otype_checker _ _)=>[[|||A1]|]=>//; 
           try (case: A1 E=>A1 A2 E/=).
Ltac l5 := let x := fresh "x" in
           set x := (AT_sem _ _);
           rewrite /x; clear x;
           let E := fresh "E" in
           let A := fresh "A" in
           case E : (AT_sem _ _)=>[A|]=>//.

Ltac simplify := rewrite /scalar_eq /ket_eq /bra_eq /opt_eq /base_eq/=;
  (try do ! l0); (try do ! l1); (try do !l2); (try do !l3); (try do !l4);
  try do ! (rewrite ?eqxx; 
  let E := fresh "E" in
  case: eqP=>[E//=|//=]; rewrite ?E; inversion E=>/=);
  rewrite ?eqxx ?V_set_id ?O_set_id ?A_set_id//.

Ltac simplify1 := rewrite /scalar_eq /ket_eq /bra_eq /opt_eq /base_eq/=;
  (try do ! l0); (try do ! l1); (try do !l2); (try do !l3); (try do !l4);
  try do ! (rewrite ?eqxx; case: eqP=>[->//|//] );
  rewrite ?eqxx ?V_set_id ?O_set_id ?A_set_id//.

Lemma ST_set1 A : @ST_set A setT = ST_sem1.
Proof.
apply/functional_extensionality_dep => x.
case E: (A == x).
by move: E=>/eqP<-; rewrite ST_set_id.
by rewrite ST_set_neq ?E.
Qed.
Lemma V_set0 A : @V_set A 0 = V_sem0.
Proof.
apply/functional_extensionality_dep => x.
case E: (A == x).
by move: E=>/eqP<-; rewrite V_set_id.
by rewrite V_set_neq ?E.
Qed.
Lemma O_set0 A : @O_set A 0 = O_sem0.
Proof.
apply/functional_extensionality_dep => x.
case E: (A == x).
by move: E=>/eqP<-; rewrite O_set_id.
by rewrite O_set_neq ?E.
Qed.

Lemma A_set_sem (a : A_base) ca (av : A_value ca) A :
  atype_checker ca a = Some A -> A_set (A_sem av a A) = A_sem av a.
Proof.
case: a=>//=.
by move=>n P; inversion P; rewrite A_set_id.
by move=>A0 + P; inversion P=>a; rewrite A_set_id.
by move=>a1 a2; simplify=>P; inversion P; rewrite A_set_id.
all: move=>a; simplify; case: A0 E=>// A1 A2 + P; 
  by inversion P=>/= IH; rewrite !A_set_id.
Qed.

Lemma K_set_sem (K : K_ket) ca (av : A_value ca) A :
    ktype_checker ca K = Some (DKet A) -> V_set (K_sem av K A) = K_sem av K.
Proof.
case: K =>[n|? _|a|b|s k|k1 k2|o k|k1 k2|st n k]//=; simplify.
2: by rewrite V_set0.
1-7: by move=>P; inversion P; rewrite V_set_id.
by case E: (sttype_checker _ _)=>//->; rewrite V_set_id.
Qed.

Lemma B_set_sem (B : B_bra) ca (av : A_value ca) A :
    btype_checker ca B = Some (DBra A) -> V_set (B_sem av B A) = B_sem av B.
Proof.
case: B => [n|? _|a|k|s b|b1 b2|b o|b1 b2|st n b]//=; simplify.
2: by rewrite V_set0.
1-7: by move=>P; inversion P; rewrite V_set_id.
by case E: (sttype_checker _ _)=>//->; rewrite V_set_id.
Qed.

Lemma O_set_sem (O : O_opt) ca (av : A_value ca) A :
    otype_checker ca O = Some (DOpt A) -> O_set (O_sem av O A) = O_sem av O.
Proof.
case: O => [n|?? _|? |k b|o|s o|o1 o2|o1 o2|o1 o2|st n o]//=; simplify.
1,4-9: by move=>P; inversion P; rewrite O_set_id.
by rewrite O_set0.
by l5=>P; inversion P; rewrite O_set_id.
by case E: (sttype_checker _ _)=>//->; rewrite O_set_id.
Qed.

(* AC symbols : associativity & commutativity *)
Lemma S_addA S1 S2 S3 ca (av : A_value ca) :
  S1 + (S2 + S3) =s S1 + S2 + S3 >> av.
Proof. by simplify; rewrite addrA. Qed.
Lemma S_addC S1 S2 ca (av : A_value ca) :
  S1 + S2 =s S2 + S1 >> av.
Proof. by simplify; rewrite addrC. Qed.

Lemma S_mulA S1 S2 S3 ca (av : A_value ca) :
  S1 * (S2 * S3) =s S1 * S2 * S3 >> av.
Proof. by simplify; rewrite mulrA. Qed.
Lemma S_mulC S1 S2 ca (av : A_value ca) :
  S1 * S2 =s S2 * S1 >> av.
Proof. by simplify; rewrite mulrC. Qed.

Lemma K_addA K1 K2 K3 ca (av : A_value ca) :
  K1 + (K2 + K3) =k K1 + K2 + K3 >> av.
Proof. by simplify; rewrite addrA. Qed.
Lemma K_addC K1 K2 ca (av : A_value ca) :
  K1 + K2 =k K2 + K1 >> av.
Proof. by simplify; rewrite addrC. Qed.

Lemma B_addA B1 B2 B3 ca (av : A_value ca) :
  B1 + (B2 + B3) =b B1 + B2 + B3 >> av.
Proof. by simplify; rewrite addrA. Qed.
Lemma B_addC B1 B2 ca (av : A_value ca) :
  B1 + B2 =b B2 + B1 >> av.
Proof. by simplify; rewrite addrC. Qed.

Lemma O_addA O1 O2 O3 ca (av : A_value ca) :
  O1 + (O2 + O3) =o O1 + O2 + O3 >> av.
Proof. by simplify; rewrite addrA. Qed.
Lemma O_addC O1 O2 ca (av : A_value ca) :
  O1 + O2 =o O2 + O1 >> av.
Proof. by simplify; rewrite addrC. Qed.

(* C symbols : commutativity *)
Lemma S_deltaC s t ca (av : A_value ca) :
  δ(s, t) =s δ(t, s) >> av.
Proof. by simplify; rewrite eq_sym. Qed.

(* R-SCALAR *)
Lemma R_SCALAR_1 S ca (av : A_value ca)  :
0 + S =s S >> av.
Proof. by simplify; rewrite add0r. Qed.
Lemma R_SCALAR_2 S ca (av : A_value ca)  :
  0 * S =s 0 >> av.
Proof. by simplify; rewrite/= mul0r. Qed.
Lemma R_SCALAR_3 S ca (av : A_value ca)  :
  1 * S =s S >> av.
Proof. by simplify; rewrite/= mul1r. Qed.
Lemma R_SCALAR_4 S1 S2 S3 ca (av : A_value ca)  :
  S1 * (S2 + S3) =s S1 * S2 + S1 * S3 >> av.
Proof. by simplify; rewrite/= mulrDr. Qed.
Lemma R_SCALAR_5 ca (av : A_value ca) :
  0^* =s 0 >> av.
Proof. by simplify; rewrite /= -conjC0. Qed.
Lemma R_SCALAR_6 ca (av : A_value ca) :
  1^* =s 1 >> av.
Proof. by simplify; rewrite /= -conjC1. Qed.
Lemma R_SCALAR_7 S1 S2  ca (av : A_value ca) :
  (S1 + S2)^* =s S1^* + S2^* >> av.
Proof. by simplify; rewrite/= rmorphD. Qed.
Lemma R_SCALAR_8 S1 S2  ca (av : A_value ca) :
  (S1 * S2)^* =s S1^* * S2^* >> av.
Proof. by simplify; rewrite/= rmorphM. Qed.
Lemma R_SCALAR_9 S  ca (av : A_value ca) :
  (S^*)^* =s S >> av.
Proof. by simplify; rewrite/= conjCK. Qed.

(* R-S-DELTA *)
Lemma R_S_DELTA_1 s ca (av : A_value ca) : 
  δ(s,s) =s 1 >> av.
Proof. by simplify. Qed.
Lemma R_S_DELTA_2 s1 t1 s2 t2 ca (av : A_value ca) :
  δ((s1, s2), (t1, t2)) =s δ(s1, t1) * δ(s2, t2) >> av.
Proof. by simplify; rewrite -pair_eqE/= -natrM mulnb. Qed.

(* R-KET-SCR *)
Lemma R_KET_SCR_1 K  ca (av : A_value ca) :
  0 *: K =k 0_(πK(typeK(K))) >> av.
Proof. by simplify; rewrite scale0r V_set0. Qed.
Lemma R_KET_SCR_2 K  ca (av : A_value ca) :
  1 *: K =k K >> av. 
Proof. by simplify; rewrite scale1r K_set_sem. Qed.
Lemma R_KET_SCR_3 S  A ca (av : A_value ca) :
  S *: 0_(A) =k 0_(A) >> av.
Proof. by simplify; l5; rewrite scaler0 V_set0. Qed.
Lemma R_KET_SCR_4 S1 S2  K  ca (av : A_value ca) :
  S1 *: (S2 *: K) =k (S1 * S2) *: K >> av.
Proof. by simplify; rewrite/= scalerA. Qed.
Lemma R_KET_SCR_5 S  K1 K2  ca (av : A_value ca) :
  S *: (K1 + K2) =k S *: K1 + S *: K2 >> av.
Proof. by simplify; rewrite/= scalerDr. Qed.

(* R-KET-ADD *)
Lemma R_KET_ADD_1 K  A ca (av : A_value ca) :
  K + 0_(A) =k K >> av.
Proof. by simplify; l5; rewrite addr0 K_set_sem//; case: eqP. Qed.
Lemma R_KET_ADD_2 K  ca (av : A_value ca) :
  K + K =k (1 + 1) *: K >> av.
Proof. by simplify; rewrite/= scalerDl scale1r. Qed.
Lemma R_KET_ADD_3 S  K  ca (av : A_value ca) :
  S *: K + K =k (S + 1) *: K >> av.
Proof. by simplify; rewrite/= scalerDl scale1r. Qed.
Lemma R_KET_ADD_4 S1 S2  K  ca (av : A_value ca) :
  S1 *: K + S2 *: K =k (S1 + S2) *: K >> av.
Proof. by simplify; rewrite/= scalerDl. Qed.

(* R-OP-SCR *)
Lemma  R_OP_SCR_1 O  ca (av : A_value ca) :
  0 *: O =o 0_(πK(typeO(O)),πB(typeO(O))) >> av.
Proof. by simplify; rewrite scale0r O_set0. Qed.
Lemma  R_OP_SCR_2 O  ca (av : A_value ca) :
  1 *: O =o O >> av.
Proof. by simplify; rewrite/= scale1r O_set_sem. Qed.
Lemma  R_OP_SCR_3 A1 A2 S  ca (av : A_value ca) :
  S *: 0_(A1,A2) =o 0_(A1,A2) >> av.
Proof. by simplify; l5; l5; rewrite/= scaler0 O_set0. Qed.
Lemma  R_OP_SCR_4 S1 S2  O  ca (av : A_value ca) :
  S1 *: (S2 *: O) =o (S1 * S2) *: O >> av.
Proof. by simplify; rewrite/= scalerA. Qed.
Lemma  R_OP_SCR_5 S  O1 O2  ca (av : A_value ca) :
  S *: (O1 + O2) =o S *: O1 + S *: O2 >> av.
Proof. by simplify; rewrite/= scalerDr. Qed.

(* R-OP-ADD *)
Lemma R_OP_ADD_1 A1 A2 O  ca (av : A_value ca) :
  O + 0_(A1,A2) =o O >> av.
Proof. by simplify; l5; l5; case: eqP=>//; rewrite/= addr0 O_set_sem. Qed.
Lemma R_OP_ADD_2 O  ca (av : A_value ca) :
  O + O =o (1+1) *: O >> av.
Proof. by simplify; rewrite/= scalerDl scale1r. Qed.
Lemma R_OP_ADD_3 S  O  ca (av : A_value ca) :
  S *: O + O =o (S + 1) *: O >> av.
Proof. by simplify; rewrite/= scalerDl scale1r. Qed.
Lemma R_OP_ADD_4 S1 S2  O  ca (av : A_value ca) :
  S1 *: O + S2 *: O =o (S1 + S2) *: O >> av.
Proof. by simplify; rewrite/= scalerDl. Qed.

(* R-KET-TSR *)
Lemma R_KET_TSR_1 A K  ca (av : A_value ca) :
  0_(A) ⊗ K =k 0_(A * πK(typeK(K))) >> av.
Proof. by simplify; l5; rewrite/= ten0tv V_set0. Qed.
Lemma R_KET_TSR_2 A K  ca (av : A_value ca) :
  K ⊗ 0_(A) =k 0_(πK(typeK(K)) * A) >> av.
Proof. by simplify; l5; rewrite/= tentv0 V_set0. Qed.
Lemma R_KET_TSR_3 s  t  ca (av : A_value ca) :
  '|s> ⊗ '|t> =k '|(s, t)> >> av.
Proof. by simplify; rewrite/= tentv_t2tv. Qed.
Lemma R_KET_TSR_4 S K1  K2  ca (av : A_value ca) :
  S *: K1 ⊗ K2 =k S *: (K1 ⊗ K2) >> av.
Proof. by simplify; rewrite/= tentvZl. Qed.
Lemma R_KET_TSR_5 S K1  K2  ca (av : A_value ca) :
  K1 ⊗ S *: K2 =k S *: (K1 ⊗ K2) >> av.
Proof. by simplify; rewrite/= tentvZr. Qed.
Lemma R_KET_TSR_6 K1 K2  K3  ca (av : A_value ca) :
  (K1 + K2) ⊗ K3 =k K1 ⊗ K3 + K2 ⊗ K3 >> av.
Proof. by simplify; rewrite/= tentvDl. Qed.
Lemma R_KET_TSR_7 K1  K2 K3  ca (av : A_value ca) :
  K1 ⊗ (K2 + K3) =k K1 ⊗ K2 + K1 ⊗ K3 >> av.
Proof. by simplify; rewrite/= tentvDr. Qed.

(* R-OP-OUTER *)
Lemma R_OP_OUTER_1 A B  ca (av : A_value ca) :
  0_(A) ·· B =o 0_(A,πB(typeB(B))) >> av.
Proof. by simplify; l5; rewrite/= out0p O_set0. Qed.
Lemma R_OP_OUTER_2 A K  ca (av : A_value ca) :
  K ·· 0_(A) =o 0_(πK(typeK(K)),A) >> av.
Proof. by simplify; l5; rewrite/= conjv0 outp0 O_set0. Qed.
Lemma R_OP_OUTER_3 S K  B  ca (av : A_value ca) :
  (S *: K) ·· B =o S *: (K ·· B) >>  av.
Proof. by simplify; rewrite/= outpZl. Qed.
Lemma R_OP_OUTER_4 S  K  B  ca (av : A_value ca) :
  K ·· (S *: B) =o S *: (K ·· B) >> av.
Proof. by simplify; rewrite/= conjvZ outpZr conjCK. Qed.
Lemma R_OP_OUTER_5 K1 K2  B  ca (av : A_value ca) :
  (K1 + K2) ·· B =o K1 ·· B + K2 ·· B >> av.
Proof. by simplify; rewrite/= outpDl. Qed.
Lemma R_OP_OUTER_6 K  B1 B2  ca (av : A_value ca) :
  K ·· (B1 + B2) =o K ·· B1 + K ·· B2 >> av.
Proof. by simplify; rewrite/= conjvD outpDr. Qed.

(* R-OP-TSR *)
Lemma R_OP_TSR_1 A1 A2 O  ca (av : A_value ca) :
  0_(A1,A2) ⊗ O =o 0_(A1 * πK(typeO(O)), A2 * πB(typeO(O))) >> av.
Proof. by simplify; l5; l5; rewrite/= ten0tf O_set0. Qed.
Lemma R_OP_TSR_2 A1 A2 O  ca (av : A_value ca) :
  O ⊗ 0_(A1,A2) =o 0_(πK(typeO(O)) * A1, πB(typeO(O)) * A2) >> av.
Proof. by simplify; l5; l5; rewrite/= tentf0 O_set0. Qed.
Lemma R_OP_TSR_3 A1 A2 ca (av : A_value ca) :
  1_(A1) ⊗ 1_(A2) =o 1_(A1 * A2) >> av.
Proof. by simplify; l5; l5; rewrite/= !O_set_id tentf11. Qed.
Lemma R_OP_TSR_4 K1 B1 K2 B2 ca (av : A_value ca) :
  K1 ·· B1 ⊗ K2 ·· B2 =o (K1 ⊗ K2) ·· (B1 ⊗ B2) >> av.
Proof. by simplify; rewrite/= tentv_out tentv_conj. Qed.
Lemma R_OP_TSR_5 S O1 O2 ca (av : A_value ca) :
  S *: O1 ⊗ O2 =o S *: (O1 ⊗ O2) >> av.
Proof. by simplify; rewrite/= tentfZl. Qed.
Lemma R_OP_TSR_6 S O1 O2 ca (av : A_value ca) :
  O1 ⊗ S *: O2 =o S *: (O1 ⊗ O2) >> av.
Proof. by simplify; rewrite/= tentfZr. Qed.
Lemma R_OP_TSR_7 O1 O2  O3  ca (av : A_value ca) :
  (O1 + O2) ⊗ O3 =o O1 ⊗ O3 + O2 ⊗ O3 >> av.
Proof. by simplify; rewrite/= tentfDl. Qed.
Lemma R_OP_TSR_8 O1  O2 O3  ca (av : A_value ca) :
  O1 ⊗ (O2 + O3) =o O1 ⊗ O2 + O1 ⊗ O3 >> av.
Proof. by simplify; rewrite/= tentfDr. Qed.

(* R-S-CONJ *)
Lemma R_S_CONJ_1 s t ca (av : A_value ca) :
  δ(s, t)^* =s δ(s, t) >> av.
Proof. by simplify; rewrite/= conjC_nat. Qed.
Lemma R_S_CONJ_2 B K ca (av : A_value ca) :
  (B · K)^* =s K^A · B^A >> av.
Proof. by simplify; rewrite/= conj_dotp conjvK. Qed.

(* R-S-DOT *)
Lemma R_S_DOT_1 A K  ca (av : A_value ca) :
  0_(A) · K =s 0 >> av.
Proof. by simplify; l5; case: eqP=>//; rewrite/= conjv0 dot0p. Qed.
Lemma R_S_DOT_2 A B  ca (av : A_value ca) :
  B · 0_(A) =s 0 >> av.
Proof. by simplify; l5; case: eqP=>//; rewrite/= dotp0. Qed.
Lemma R_S_DOT_3 S  B  K  ca (av : A_value ca) :
  (S *: B) · K =s S * (B · K) >> av.
Proof. by simplify; rewrite/= conjvZ dotpZl conjCK. Qed.
Lemma R_S_DOT_4 S  B  K  ca (av : A_value ca) :
  B · (S *: K) =s S * (B · K) >> av.
Proof. by simplify; rewrite/= dotpZr. Qed.
Lemma R_S_DOT_5 B1 B2  K  ca (av : A_value ca) :
  (B1 + B2) · K =s B1 · K + B2 · K >> av.
Proof. by simplify; rewrite/= conjvD dotpDl. Qed.
Lemma R_S_DOT_6 B  K1 K2  ca (av : A_value ca) :
  B · (K1 + K2) =s B · K1 + B · K2 >> av.
Proof. by simplify; rewrite/= dotpDr. Qed.
Lemma R_S_DOT_7 s t ca (av : A_value ca) :
  '<s| · '|t> =s δ(s, t) >> av.
Proof. by simplify; rewrite/= t2tv_conj t2tv_dot ?eqxx// =>/eqP/negPf->. Qed.

Lemma R_S_DOT_8 B1  B2  s t ca (av : A_value ca) :
  (B1 ⊗ B2) · '|(s, t)> =s B1 · '|s> * (B2 · '|t>) >> av.
Proof. by simplify; rewrite/= tentv_conj -tentv_dot tentv_t2tv. Qed.
Lemma R_S_DOT_9 s t K1  K2  ca (av : A_value ca) :
  '<(s, t)| · (K1 ⊗ K2) =s '<s| · K1 * ('<t| · K2) >> av.
Proof. by simplify; rewrite/= -tentv_dot -tentv_conj tentv_t2tv. Qed.
Lemma R_S_DOT_10 B1  B2  K1  K2  ca (av : A_value ca) :
  (B1 ⊗ B2) · (K1 ⊗ K2) =s B1 · K1 * (B2 · K2) >> av.
Proof. by simplify; rewrite/= -tentv_dot -tentv_conj. Qed.

(* R-S-SORT *)
Lemma R_S_SORT_1 B  O  K  ca (av : A_value ca) :
  (B · O) · K =s B · (O · K) >> av.
Proof. by simplify; rewrite/= trfAC conjfE conjvK adj_dotEl. Qed.
Lemma R_S_SORT_2 s t O1  O2  K ca (av : A_value ca) :
    '<(s, t)| · ((O1 ⊗ O2) · K) =s ('<s| · O1 ⊗ '<t| · O2) · K >> av.
Proof.
by simplify; rewrite !trfAC !conjfE !t2tv_conj tentv_conj 
  !conjvK -tentf_apply -tentf_adj adj_dotEl tentv_t2tv.
Qed.
Lemma R_S_SORT_3 B1  B2  O1  O2  K ca (av : A_value ca) :
    (B1 ⊗ B2) · ((O1 ⊗ O2) · K) =s (B1 · O1 ⊗ B2 · O2) · K >> av.
Proof.
by simplify; rewrite !trfAC !conjfE !tentv_conj 
  !conjvK -tentf_apply -tentf_adj adj_dotEl.
Qed.

(* R-KET-ADJ *)
Lemma R_KET_ADJ_1 A ca (av : A_value ca) :
  0_(A)^A =k 0_(A) >> av.
Proof. by simplify; l5; rewrite/= conjv0 V_set0. Qed.
Lemma R_KET_ADJ_2 t ca (av : A_value ca) :
  '<t|^A =k '|t> >> av.
Proof. by simplify; rewrite/= t2tv_conj. Qed.
Lemma R_KET_ADJ_3 K  ca (av : A_value ca) :
  (K^A)^A =k K >> av.
Proof. by simplify; rewrite/= conjvK K_set_sem. Qed.
Lemma R_KET_ADJ_4 S  B  ca (av : A_value ca) :
  (S *: B)^A =k S^* *: B^A >> av.
Proof. by simplify; rewrite/= conjvZ. Qed.
Lemma R_KET_ADJ_5 B1 B2  ca (av : A_value ca) :
  (B1 + B2)^A =k B1^A + B2^A >> av.
Proof. by simplify; rewrite/= conjvD. Qed.
Lemma R_KET_ADJ_6 B  O  ca (av : A_value ca) :
  (B · O)^A =k O^A · B^A >> av.
Proof. by simplify; rewrite/= trfAC conjfE conjvK. Qed.
Lemma R_KET_ADJ_7 B1  B2  ca (av : A_value ca) :
  (B1 ⊗ B2)^A =k B1^A ⊗ B2^A >> av.
Proof. by simplify; rewrite /= tentv_conj. Qed.

(* KET-MLT *)
Lemma R_KET_MLT_1 A1 A2 K  ca (av : A_value ca) :
  0_(A1,A2) · K =k 0_(A1) >> av.
Proof. by simplify; l5; l5=>/=; case: eqP=>//; rewrite/= lfunE/= V_set0. Qed.
Lemma R_KET_MLT_2 A O  ca (av : A_value ca) :
  O · 0_(A) =k 0_(πK(typeO(O))) >> av.
Proof. by simplify; l5; case: eqP=>//; rewrite linear0 V_set0. Qed.
Lemma R_KET_MLT_3 A K  ca (av : A_value ca) :
  1_(A) · K =k K >> av.
Proof. by simplify; l5=>/=; case: eqP=>// P; rewrite O_set_id lfunE/= K_set_sem P. Qed.
Lemma R_KET_MLT_4 S  O  K  ca (av : A_value ca) :
  (S *: O) · K =k S *: (O · K) >> av.
Proof. by simplify; rewrite /= lfunE. Qed.
Lemma R_KET_MLT_5 S  O  K  ca (av : A_value ca) :
  O · (S *: K) =k S *: (O · K) >> av.
Proof. by simplify; rewrite linearZ. Qed.
Lemma R_KET_MLT_6 O1 O2  K  ca (av : A_value ca) :
  (O1 + O2) · K =k O1 · K + O2 · K >> av.
Proof. by simplify; rewrite lfunE. Qed.
Lemma R_KET_MLT_7 O  K1 K2  ca (av : A_value ca) :
  O · (K1 + K2) =k O · K1 + O · K2 >> av.
Proof. by simplify; rewrite linearD. Qed.
Lemma R_KET_MLT_8 K1  B  K2  ca (av : A_value ca) :
  (K1 ·· B) · K2 =k (B · K2) *: K1 >> av.
Proof. by simplify; rewrite/= outpE. Qed.
Lemma R_KET_MLT_9 O1  O2  K  ca (av : A_value ca) :
  (O1 · O2) · K =k O1 · (O2 · K) >> av.
Proof. by simplify; rewrite lfunE. Qed.
Lemma R_KET_MLT_10 O1  O1' O2 O2' K ca (av : A_value ca) :
    (O1 ⊗ O2) · ((O1' ⊗ O2') · K) =k (O1 · O1' ⊗ O2 · O2') · K >> av.
Proof. by simplify; rewrite /= -tentf_comp lfunE. Qed.
Lemma R_KET_MLT_11 O1  O2 s t ca (av : A_value ca) :
  (O1 ⊗ O2) · '|(s, t)> =k O1 · '|s> ⊗ O2 · '|t> >> av.
Proof. by simplify; rewrite -tentf_apply tentv_t2tv. Qed.
Lemma R_KET_MLT_12 O1  O2  K1  K2  ca (av : A_value ca) :
    (O1 ⊗ O2) · (K1 ⊗ K2) =k O1 · K1 ⊗ O2 · K2 >> av.
Proof. by simplify; rewrite /= tentf_apply. Qed.

(* R-BRA-ADJ *)
Lemma R_BRA_ADJ_1 A ca (av : A_value ca) :
  0_(A)^A =b 0_(A) >> av.
Proof. by simplify; l5; rewrite/= conjv0 V_set0. Qed.
Lemma R_BRA_ADJ_2 t ca (av : A_value ca) :
  '|t>^A =b '<t| >> av.
Proof. by simplify; rewrite/= t2tv_conj. Qed.
Lemma R_BRA_ADJ_3 B  ca (av : A_value ca) :
  (B^A)^A =b B >> av.
Proof. by simplify; rewrite/= conjvK B_set_sem. Qed.
Lemma R_BRA_ADJ_4 S  K  ca (av : A_value ca) :
  (S *: K)^A =b S^* *: K^A >> av.
Proof. by simplify; rewrite/= conjvZ. Qed.
Lemma R_BRA_ADJ_5 K1 K2  ca (av : A_value ca) :
  (K1 + K2)^A =b K1^A + K2^A >> av.
Proof. by simplify; rewrite/= conjvD. Qed.
Lemma R_BRA_ADJ_6 O  K  ca (av : A_value ca) :
  (O · K)^A =b K^A · O^A >> av.
Proof. by simplify; rewrite /= trfAC conjfE conjvK adjfK. Qed.
Lemma R_BRA_ADJ_7 K1  K2  ca (av : A_value ca) :
  (K1 ⊗ K2)^A =b K1^A ⊗ K2^A >> av.
Proof. by simplify; rewrite /= tentv_conj. Qed.

(* BRA-MLT *)
Lemma R_BRA_MLT_1 A1 A2 B  ca (av : A_value ca) :
  B · 0_(A1,A2) =b 0_(A2) >> av.
Proof. by simplify; l5; l5=>/=; case: eqP=>//; rewrite/= trf0 lfunE/= V_set0. Qed.
Lemma R_BRA_MLT_2 A O  ca (av : A_value ca) :
  0_(A) · O =b 0_(πB(typeO(O))) >> av.
Proof. by simplify; l5; case: eqP=>//; rewrite/= linear0 V_set0. Qed.
Lemma R_BRA_MLT_3 A B  ca (av : A_value ca) :
  B · 1_(A) =b B >> av.
Proof. by simplify; l5=>/=; case: eqP=>// <-; rewrite O_set_id/= trf1 lfunE B_set_sem. Qed.
Lemma R_BRA_MLT_4 S  B  O  ca (av : A_value ca) :
  B · (S *: O) =b S *: (B · O) >> av.
Proof. by simplify; rewrite/= trfZ lfunE. Qed.
Lemma R_BRA_MLT_5 S  B  O  ca (av : A_value ca) :
  (S *: B) · O =b S *: (B · O) >> av.
Proof. by simplify; rewrite /= linearZ. Qed.
Lemma R_BRA_MLT_6 B  O1 O2  ca (av : A_value ca) :
  B · (O1 + O2) =b B · O1 + B · O2 >> av.
Proof. by simplify; rewrite /= trfD lfunE. Qed.
Lemma R_BRA_MLT_7 B1 B2  O  ca (av : A_value ca) :
  (B1 + B2) · O  =b B1 · O + B2 · O >> av.
Proof. by simplify; rewrite /= linearD. Qed.
Lemma R_BRA_MLT_8 B1  K  B2  ca (av : A_value ca) :
  B1 · (K ·· B2) =b (B1 · K) *: B2 >> av.
Proof. by simplify; rewrite/= trfAC adj_outp conjfE outpE conjvZ conjvK conj_dotp. Qed.
Lemma R_BRA_MLT_9 B  O1  O2  ca (av : A_value ca) :
  B · (O1 · O2) =b (B · O1) · O2 >> av.
Proof. by simplify; rewrite /= trf_comp lfunE. Qed.
Lemma R_BRA_MLT_10 B O1  O1' O2 O2' ca (av : A_value ca) :
    B · ((O1 ⊗ O2) · (O1' ⊗ O2')) =b B · (O1 · O1' ⊗ O2 · O2') >> av.
Proof. by simplify; rewrite /= -tentf_comp trf_comp. Qed.
Lemma R_BRA_MLT_11 s t O1  O2  ca (av : A_value ca) :
  '<(s, t)| · (O1 ⊗ O2) =b '<s| · O1 ⊗ '<t| · O2 >> av.
Proof. by simplify; rewrite/= -tentf_apply tentv_t2tv tentf_tr. Qed.
Lemma R_BRA_MLT_12 B1  B2   O1  O2  ca (av : A_value ca) :
    (B1 ⊗ B2) · (O1 ⊗ O2) =b B1 · O1 ⊗ B2 · O2 >> av.
Proof. by simplify; rewrite/= tentf_tr tentf_apply. Qed.

(* OP-ADJ *)
Lemma R_OP_ADJ_1 A1 A2 ca (av : A_value ca) :
  0_(A1,A2)^A =o 0_(A2,A1) >> av.
Proof. by simplify; l5; l5=>/=; rewrite adjf0 O_set0. Qed.
Lemma R_OP_ADJ_2 A ca (av : A_value ca) :
  1_(A)^A =o 1_(A) >> av.
Proof. by simplify; l5; rewrite/= O_set_id adjf1. Qed.
Lemma R_OP_ADJ_3 K  B  ca (av : A_value ca) :
  (K ·· B)^A =o B^A ·· K^A >> av.
Proof. by simplify; rewrite/= adj_outp conjvK. Qed.
Lemma R_OP_ADJ_4 O  ca (av : A_value ca) :
  (O^A)^A =o O >> av.
Proof. by simplify; rewrite/= adjfK O_set_sem. Qed.
Lemma R_OP_ADJ_5 S  O  ca (av : A_value ca) :
  (S *: O)^A =o S^* *: O^A >> av.
Proof. by simplify; rewrite /= adjfZ. Qed.
Lemma R_OP_ADJ_6 O1 O2  ca (av : A_value ca) :
  (O1 + O2)^A =o O1^A + O2^A >> av.
Proof. by simplify; rewrite/= adjfD. Qed.
Lemma R_OP_ADJ_7 O1  O2  ca (av : A_value ca) :
  (O1 · O2)^A =o O2^A · O1^A >> av.
Proof. by simplify; rewrite/= adjf_comp. Qed.
Lemma R_OP_ADJ_8 O1  O2  ca (av : A_value ca) :
  (O1 ⊗ O2)^A =o O1^A ⊗ O2^A >> av.
Proof. by simplify=>/=; rewrite tentf_adj. Qed.

(* R-OP-MLT *)
Lemma R_OP_MLT_1 A1 A2 O  ca (av : A_value ca) :
  0_(A1,A2) · O =o 0_(A1,πB(typeO(O))) >> av.
Proof. by simplify; l5; l5=>/=; case: eqP=>//; rewrite comp_lfun0l O_set0. Qed.
Lemma R_OP_MLT_2 A1 A2 O  ca (av : A_value ca) :
  O · 0_(A1,A2) =o 0_(πK(typeO(O)),A2) >> av.
Proof. by simplify; l5; l5=>/=; case: eqP=>//; rewrite comp_lfun0r O_set0. Qed.  
Lemma R_OP_MLT_3 A O  ca (av : A_value ca) :
  1_(A) · O =o O >> av.
Proof.
by simplify; l5=>/=; case: eqP=>// ->; 
rewrite O_set_id comp_lfun1l O_set_sem.  
Qed.
Lemma R_OP_MLT_4 A O  ca (av : A_value ca) :
  O · 1_(A) =o O >> av.
Proof.
by simplify; l5=>/=; case: eqP=>// <-; rewrite O_set_id comp_lfun1r O_set_sem.
Qed.
Lemma R_OP_MLT_5 K  B  O  ca (av : A_value ca) :
  (K ·· B) · O =o K ·· (B · O) >> av.
Proof. by simplify=>/=; rewrite/= outp_compl trfAC conjfE conjvK. Qed.
Lemma R_OP_MLT_6 O  K  B  ca (av : A_value ca) :
  O · (K ·· B) =o (O · K) ·· B >> av.
Proof. by simplify=>/=; rewrite outp_compr. Qed.
Lemma R_OP_MLT_7 S  O1  O2  ca (av : A_value ca) :
  (S *: O1) · O2 =o S *: (O1 · O2) >> av.
Proof. by simplify; rewrite/= linearZl. Qed.
Lemma R_OP_MLT_8 S  O1  O2  ca (av : A_value ca) :
  O1 · (S *: O2) =o S *: (O1 · O2) >> av.
Proof. by simplify; rewrite/= linearZr. Qed.
Lemma R_OP_MLT_9 O1 O2  O3  ca (av : A_value ca) :
  (O1 + O2) · O3 =o O1 · O3 + O2 · O3 >> av.
Proof. by simplify; rewrite linearDl. Qed.
Lemma R_OP_MLT_10 O1  O2 O3  ca (av : A_value ca) :
  O1 · (O2 + O3) =o O1 · O2 + O1 · O3 >> av.
Proof. by simplify; rewrite linearDr. Qed.
Lemma R_OP_MLT_11 O1  O2  O3  ca (av : A_value ca) :
  (O1 · O2) · O3 =o O1 · (O2 · O3) >> av.
Proof. by simplify; rewrite/= comp_lfunA. Qed.
Lemma R_OP_MLT_12  O1  O1'  O2 O2' ca (av : A_value ca) :
    (O1 ⊗ O2) · (O1' ⊗ O2') =o O1 · O1' ⊗ O2 · O2' >> av.
Proof. by simplify; rewrite/= tentf_comp. Qed.
Lemma R_OP_MLT_13 O1  O1'  O2 O2' O3 ca (av : A_value ca) :
    (O1 ⊗ O2) · ((O1' ⊗ O2') · O3) =o (O1 · O1' ⊗ O2 · O2') · O3 >> av.
Proof. by simplify; rewrite /= -tentf_comp comp_lfunA. Qed.

(* Appendix A.1 *)
(* BASIS *)
Lemma R_BASIS_1 s t ca (av : A_value ca) :
  (s,t).1 =a s >> av.
Proof. by simplify; rewrite /= A_set_sem. Qed.
Lemma R_BASIS_2 s t ca (av : A_value ca) :
  (s,t).2 =a t >> av.
Proof. by simplify; rewrite /= A_set_sem. Qed.
Lemma R_BASIS_3 s ca (av : A_value ca) :
  (s.1, s.2) =a s >> av.
Proof.
by simplify; case: A E=>// A1 A2 E; rewrite !A_set_id -surjective_pairing A_set_sem.
Qed.

(* DELAT *)
Lemma R_S_DELTA_3 s u v ca (av : A_value ca) :
  δ(s, (u,v)) =s δ(s.1, u) * δ(s.2,v) >> av.
Proof. by simplify; rewrite -pair_eqE/= -natrM mulnb. Qed.
Lemma R_S_DELTA_4 s t ca (av : A_value ca) :
  δ(s.1, t.1) * δ(s.2,t.2) =s δ(s, t) >> av.
Proof.
simplify; case: A E=>// A1 A2 E; case: A0 E0 =>// A01 A02 E0 /=.
by case: eqP=>//->; case: eqP=>//->; rewrite eqxx -pair_eqE/= -natrM mulnb !A_set_id.
Qed.

Lemma R_S_DOT_11 B1  B2 t ca (av : A_value ca) :
  (B1 ⊗ B2) · '|t> =s B1 · '|t.1> * (B2 · '|t.2>) >> av.
Proof. by simplify; rewrite/= tentv_conj -tentv_dot tentv_t2tv -surjective_pairing. Qed.
Lemma R_S_DOT_12 t K1  K2 ca (av : A_value ca) :
  '<t| · (K1 ⊗ K2) =s '<t.1| · K1 * ('<t.2| · K2) >> av.
Proof. by simplify; rewrite/= -tentv_dot -tentv_conj tentv_t2tv -surjective_pairing. Qed.
Lemma R_S_SORT_4 s O1  O2  K ca (av : A_value ca) :
  '<s| · ((O1 ⊗ O2) · K) =s ('<s.1| · O1 ⊗ '<s.2| · O2) · K >> av.
Proof.
by simplify; rewrite -tentf_apply -tentf_tr 
  tentv_t2tv -surjective_pairing trfAC conjfE conjvK adj_dotEl.
Qed.
Lemma R_KET_MLT_13 O1 O2 t ca (av : A_value ca) :
  (O1 ⊗ O2) · '|t> =k O1 · '|t.1> ⊗ O2 · '|t.2> >> av.
Proof. by simplify; rewrite -tentf_apply tentv_t2tv -surjective_pairing. Qed.
Lemma R_BRA_MLT_13 O1 O2 t ca (av : A_value ca) :
  '<t| · (O1 ⊗ O2) =b '<t.1| · O1 ⊗ '<t.2| · O2 >> av.
Proof. by simplify; rewrite -tentf_apply tentv_t2tv tentf_tr -surjective_pairing. Qed.

Definition atype_eq ca ca' A1 A2 :=
  if AT_sem ca A1 is Some _ then
    AT_sem ca A1 = AT_sem ca' A2
  else True.

Definition dtype_eq ca ca' D1 D2 :=
  if DT_sem ca D1 is Some _ then
    DT_sem ca D1 = DT_sem ca' D2
  else True.

Notation "A '=at' B >> ca , ca' " := (atype_eq ca ca' A%AT B%AT) (at level 70, ca at next level, ca' at next level).
Notation "A '=dt' B >> ca , ca' " := (dtype_eq ca ca' A%DT B%DT) (at level 70, ca at next level, ca' at next level).
Notation "A '=at' B >> ca " := (atype_eq ca ca A%AT B%AT) (at level 70, ca at next level).
Notation "A '=dt' B >> ca " := (dtype_eq ca ca A%DT B%DT) (at level 70, ca at next level).

Ltac l6 := let x := fresh "x" in
           set x := (DT_sem _ _);
           rewrite /x; clear x;
           let E := fresh "E" in
           let A := fresh "A" in
           let A1 := fresh "A" in
           case E : (DT_sem _ _)=>[[|A|A|[A A1]]|]=>//=.

Ltac simplify2 := rewrite /dtype_eq /atype_eq/=;
  (try do ! l5); (try do ! l6);
  try do ! (rewrite ?eqxx; 
  let E := fresh "E" in
  case: eqP=>[E//=|//=]; rewrite ?E; inversion E=>/=);
  rewrite ?eqxx//.

Lemma stype_checker_DScale ca S :
  stype_checker ca S = None \/ stype_checker ca S = Some DScale.
Proof.
elim: S ca=>//=; auto.
move=>a1 a2 ca; simplify; auto; case: eqP; auto.
move=>s1 IH1 s2 IH2 ca; simplify; auto.
move=>s1 IH1 s2 IH2 ca; simplify; auto.
move=>b k ca; simplify; auto; case: eqP; auto.
move=>st n s IH ca; case: (sttype_checker _ _); auto.
Qed.

Lemma ktype_checker_DKet ca K :
  ktype_checker ca K = None \/ 
    exists A, ktype_checker ca K = Some (DKet A).
Proof.
elim: K ca=>//=.
by move=>n ca; right; exists (ck n).
by move=>A ca; simplify2; auto; right; exists A0.
by move=>A ca; simplify; auto; right; exists A0.
by move=>A ca; simplify; auto; right; exists A0.
by move=>s k IH1 ca; simplify; auto; right; exists A.
by move=>k1 IH1 k2 IH2 ca; simplify; auto; case: eqP; auto; right; exists A.
by move=>s k IH1 ca; simplify; auto; case: eqP; auto; right; exists A0.
by move=>k1 IH1 k2 IH2 ca; simplify; auto; right; exists (A * A0)%TA.
by move=>st n k IH ca; case: (sttype_checker _ _); auto.
Qed.

Lemma btype_checker_DBra ca B :
  btype_checker ca B = None \/ 
    exists A, btype_checker ca B = Some (DBra A).
Proof.
elim: B ca=>//=.
by move=>n ca; right; exists (cb n).
by move=>A ca; simplify2; auto; right; exists A0.
by move=>A ca; simplify; auto; right; exists A0.
by move=>A ca; simplify; auto; right; exists A0.
by move=>s k IH1 ca; simplify; auto; right; exists A.
by move=>k1 IH1 k2 IH2 ca; simplify; auto; case: eqP; auto; right; exists A.
by move=>s k IH1 ca; simplify; auto; case: eqP; auto; right; exists A1.
by move=>k1 IH1 k2 IH2 ca; simplify; auto; right; exists (A * A0)%TA.
by move=>st n k IH ca; case: (sttype_checker _ _); auto.
Qed.

Lemma otype_checker_DOpt ca O :
  otype_checker ca O = None \/ 
    exists A, otype_checker ca O = Some (DOpt A).
Proof.
elim: O ca=>//=.
by move=>n ca; right; exists (co n).
by move=>A1 A2 ca; simplify2; auto; right; exists (pair A A0).
by move=>A ca; simplify2; auto; right; exists (pair A0 A0).
by move=>k b ca; simplify; auto; right; exists (pair A A0).
by move=>o IH ca; simplify; auto; right; exists (pair A0 A).
by move=>s o IH1 ca; simplify; auto; right; exists (pair A A0).
by move=>o1 IH1 o2 IH2 ca; simplify; auto; case: eqP; auto; right; exists (pair A A0).
by move=>o1 IH1 o2 IH2 ca; simplify; auto; case: eqP; auto; right; exists (pair A A2).
by move=>o1 IH1 o2 IH2 ca; simplify; auto; right; exists (pair (A*A1)%TA (A0*A2)%TA).
by move=>st n k IH ca; case: (sttype_checker _ _); auto.
Qed.

Lemma stype_checker_DKet A S ca (P : Prop) : 
  stype_checker ca S = Some (DKet A) -> P.
Proof. by move: (stype_checker_DScale ca S)=>[]->. Qed.
Lemma stype_checker_DBra A S ca (P : Prop) : 
  stype_checker ca S = Some (DBra A) -> P.
Proof. by move: (stype_checker_DScale ca S)=>[]->. Qed.
Lemma stype_checker_DOpt A S ca (P : Prop) : 
  stype_checker ca S = Some (DOpt A) -> P.
Proof. by move: (stype_checker_DScale ca S)=>[]->. Qed.

Lemma ktype_checker_DScale K ca (P : Prop) : 
  ktype_checker ca K = Some DScale -> P.
Proof. by move: (ktype_checker_DKet ca K)=>[->//|[?->]]. Qed.
Lemma ktype_checker_DBra A K ca (P : Prop) : 
  ktype_checker ca K = Some (DBra A) -> P.
Proof. by move: (ktype_checker_DKet ca K)=>[->//|[?->]]. Qed.
Lemma ktype_checker_DOpt A K ca (P : Prop) : 
  ktype_checker ca K = Some (DOpt A) -> P.
Proof. by move: (ktype_checker_DKet ca K)=>[->//|[?->]]. Qed.

Lemma btype_checker_DScale B ca (P : Prop) : 
  btype_checker ca B = Some DScale -> P.
Proof. by move: (btype_checker_DBra ca B)=>[->//|[?->]]. Qed.
Lemma btype_checker_DKet A B ca (P : Prop) : 
  btype_checker ca B = Some (DKet A) -> P.
Proof. by move: (btype_checker_DBra ca B)=>[->//|[?->]]. Qed.
Lemma btype_checker_DOpt A B ca (P : Prop) : 
  btype_checker ca B = Some (DOpt A) -> P.
Proof. by move: (btype_checker_DBra ca B)=>[->//|[?->]]. Qed.

Lemma otype_checker_DScale O ca (P : Prop) : 
  otype_checker ca O = Some DScale -> P.
Proof. by move: (otype_checker_DOpt ca O)=>[->//|[?->]]. Qed.
Lemma otype_checker_DKet A O ca (P : Prop) : 
  otype_checker ca O = Some (DKet A) -> P.
Proof. by move: (otype_checker_DOpt ca O)=>[->//|[?->]]. Qed.
Lemma otype_checker_DBra A O ca (P : Prop) : 
  otype_checker ca O = Some (DBra A) -> P.
Proof. by move: (otype_checker_DOpt ca O)=>[->//|[?->]]. Qed.

Ltac contra1 := try 
  match goal with
  | [ H : stype_checker _ _ = Some (DKet _)  |- _ ] => apply (stype_checker_DKet _ H)
  | [ H : stype_checker _ _ = Some (DBra _)  |- _ ] => apply (stype_checker_DBra _ H)
  | [ H : stype_checker _ _ = Some (DOpt _)  |- _ ] => apply (stype_checker_DOpt _ H)
  | [ H : ktype_checker _ _ = Some DScale  |- _ ] => apply (ktype_checker_DScale _ H)
  | [ H : ktype_checker _ _ = Some (DBra _)  |- _ ] => apply (ktype_checker_DBra _ H)
  | [ H : ktype_checker _ _ = Some (DOpt _)  |- _ ] => apply (ktype_checker_DOpt _ H)
  | [ H : btype_checker _ _ = Some DScale  |- _ ] => apply (btype_checker_DScale _ H)
  | [ H : btype_checker _ _ = Some (DKet _)  |- _ ] => apply (btype_checker_DKet _ H)
  | [ H : btype_checker _ _ = Some (DOpt _)  |- _ ] => apply (btype_checker_DOpt _ H)
  | [ H : otype_checker _ _ = Some DScale  |- _ ] => apply (otype_checker_DScale _ H)
  | [ H : otype_checker _ _ = Some (DKet _)  |- _ ] => apply (otype_checker_DKet _ H)
  | [ H : otype_checker _ _ = Some (DBra _)  |- _ ] => apply (otype_checker_DBra _ H)
  end.


(* Dynamic Typing Rules *)
(* TYPE-SIMP *)
Lemma R_TYPE_SIMP_0 n ca : type(`n) =at 'A(ca n) >> ca.
Proof. by simplify. Qed.
Lemma R_TYPE_SIMP_1 A ca : πK(KT(A)) =at A >> ca.
Proof. simplify2. Qed.
Lemma R_TYPE_SIMP_2 A ca : πB(BT(A)) =at A >> ca.
Proof. simplify2. Qed.
Lemma R_TYPE_SIMP_3 A B ca : π1(A * B) =at A >> ca.
Proof. simplify2. Qed.
Lemma R_TYPE_SIMP_4 A B ca : π2(A * B) =at B >> ca.
Proof. simplify2. Qed.
Lemma R_TYPE_SIMP_5 A B ca : πK(OT(A, B)) =at A >> ca.
Proof. simplify2. Qed.
Lemma R_TYPE_SIMP_6 A B ca : πB(OT(A, B)) =at B >> ca.
Proof. simplify2. Qed.

(* TYPE-BASIS *)
Lemma R_TYPE_BASIS_1 s ca : type(s.1) =at π1(type(s)) >> ca.
Proof. by simplify2; simplify; case: A E. Qed.
Lemma R_TYPE_BASIS_2 s ca : type(s.2) =at π2(type(s)) >> ca.
Proof. by simplify2; simplify; case: A E. Qed.
Lemma R_TYPE_BASIS_3 s t ca : type((s,t)) =at type(s) * type(t) >> ca.
Proof. by simplify2; simplify. Qed.

(* TYPE-SCALAR *)
Lemma R_TYPE_SCALAR_1 ca : typeS(0) =dt ST >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_SCALAR_2 ca : typeS(1) =dt ST >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_SCALAR_3 s t ca : typeS(δ(s,t)) =dt ST >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_SCALAR_4 S1 S2 ca : typeS(S1 + S2) =dt ST >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_SCALAR_5 S1 S2 ca : typeS(S1 * S2) =dt ST >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_SCALAR_6 S ca : typeS(S^*) =dt ST >> ca.
Proof.
simplify2.
elim: S ca =>//=; intros; simplify.
by case: (sttype_checker _ _)=>// A; apply: H.
Qed.
Lemma R_TYPE_SCALAR_7 B K ca : typeS(B · K) =dt ST >> ca.
Proof. by simplify2; simplify. Qed.

(* TYPE-KET *)
Lemma R_TYPE_KET_1 A ca : typeK(0_(A)) =dt KT(A) >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_KET_2 s ca : typeK('|s>) =dt KT(type(s)) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_KET_3 B ca : typeK(B^A) =dt KT(πB(typeB(B))) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_KET_4 S K ca : typeK(S *: K) =dt typeK(K) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_KET_5 K1 K2 ca : typeK(K1 + K2) =dt typeK(K1) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_KET_6 O K ca : typeK(O · K) =dt KT(πK(typeO(O))) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_KET_7 K1 K2 ca : 
  typeK(K1 ⊗ K2) =dt KT(πK(typeK(K1)) * πK(typeK(K2))) >> ca.
Proof. by simplify2; simplify. Qed.

(* TYPE-BRA *)
Lemma R_TYPE_BRA_1 A ca : typeB(0_(A)) =dt BT(A) >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_BRA_2 s ca : typeB('<s|) =dt BT(type(s)) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_BRA_3 K ca : typeB(K^A) =dt BT(πK(typeK(K))) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_BRA_4 S B ca : typeB(S *: B) =dt typeB(B) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_BRA_5 B1 B2 ca : typeB(B1 + B2) =dt typeB(B1) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_BRA_6 B O ca : typeB(B · O) =dt BT(πB(typeO(O))) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_BRA_7 B1 B2 ca : 
  typeB(B1 ⊗ B2) =dt BT(πB(typeB(B1)) * πB(typeB(B2))) >> ca.
Proof. by simplify2; simplify. Qed.

(* TYPE-OPT *)
Lemma R_TYPE_OPT_1 A1 A2 ca : typeO(0_(A1,A2)) =dt OT(A1,A2) >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_OPT_2 A ca : typeO(1_(A)) =dt OT(A,A) >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_OPT_3 K B ca : typeO(K ·· B) =dt OT(πK(typeK(K)), πB(typeB(B))) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_OPT_4 O ca : typeO(O^A) =dt OT(πB(typeO(O)),πK(typeO(O))) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_OPT_5 S O ca : typeO(S *: O) =dt typeO(O) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_OPT_6 O1 O2 ca : typeO(O1 + O2) =dt typeO(O1) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_OPT_7 O1 O2 ca : typeO(O1 · O2) =dt OT(πK(typeO(O1)), πB(typeO(O2))) >> ca.
Proof. by simplify2; simplify. Qed.
Lemma R_TYPE_OPT_8 O1 O2 ca : 
  typeO(O1 ⊗ O2) =dt OT(πK(typeO(O1)) * πK(typeO(O2)), πB(typeO(O1)) * πB(typeO(O2))) >> ca.
Proof. by simplify2; simplify. Qed.

(* TYPE_EXT *)
Lemma R_TYPE_EXT_1 A ca : πS(A) =at A >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_EXT_2 A ca : typeSet(U(A)) =at A >> ca.
Proof. by simplify2. Qed.
Lemma R_TYPE_EXT_3 M1 M2 ca : 
  typeSet(M1 * M2) =at πS(typeSet(M1) * typeSet(M2)) >> ca.
Proof.
simplify2; case E1: (sttype_checker _ _)=>[A1|//].
by case E2: (sttype_checker _ _)=>[A2|//].
Qed.
Lemma R_TYPE_EXT_4 n M S ca : 
      typeS(S_sum M n S) =dt ST >> ca.
Proof.
simplify2; case E: (sttype_checker _ _)=>[A|//].
simplify; contra1.
Qed.
Lemma R_TYPE_EXT_5 n M K ca : 
  match AT_sem ca (πS(typeSet(M)))%AT with
  | Some A =>
      typeK(K_sum M n K) =dt 
        typeK(K) >> ca , Gamma_A_update ca n A
  | None => True
  end.
Proof.
simplify2.
case E1: (sttype_checker _ _)=>[A1|//].
by case: (ktype_checker _ _).
Qed.
Lemma R_TYPE_EXT_6 n M B ca : 
  match AT_sem ca (πS(typeSet(M)))%AT with
  | Some A =>
      typeB(B_sum M n B) =dt 
        typeB(B) >> ca , Gamma_A_update ca n A
  | None => True
  end.
Proof.
simplify2.
case E1: (sttype_checker _ _)=>[A1|//].
by case: (btype_checker _ _).
Qed.
Lemma R_TYPE_EXT_7 n M O ca : 
  match AT_sem ca (πS(typeSet(M)))%AT with
  | Some A =>
      typeO(O_sum M n O) =dt 
        typeO(O) >> ca , Gamma_A_update ca n A
  | None => True
  end.
Proof.
simplify2.
case E1: (sttype_checker _ _)=>[A1|//].
by case: (otype_checker _ _).
Qed.

Definition sttype_eq ca1 ca2 M1 M2 :=
  if sttype_checker ca1 M1 is Some _ then
    sttype_checker ca1 M1 = sttype_checker ca2 M2 /\
    ST_sem ca1 stv M1 = ST_sem ca2 stv M2
  else True.

Notation "A '=st' B >> ca1 , ca2 " := (sttype_eq ca1 ca2 A%ST B%ST)
  (at level 70, ca1 at next level, ca2 at next level).
Notation "A '=st' B >> ca " := (sttype_eq ca ca A%ST B%ST)
  (at level 70, ca at next level).

Lemma setXTT (aT bT : finType) :
  setX (setT : {set aT}) (setT : {set bT}) = setT.
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; first by apply: subsetT.
by apply/subsetP=>[[a b]]; rewrite inE in_setX !inE.
Qed.

(* SET-SIMP *)
Lemma R_SET_SIMP A B ca : U(A) * U(B) =st U(A*B) >> ca.
Proof.
rewrite /sttype_eq/=; simplify2.
by rewrite setXTT ST_set1.
Qed.

(* free variable and substitution *)

(* free occurence: true (no appear), false (appear) *)
Fixpoint free_A (n : aname) (a : A_base) : bool :=
  match a with
  | A_var m => n != m
  | A_ground _ _ => true
  | A_pair a1 a2 => free_A n a1 && free_A n a2
  | A_fst a => free_A n a
  | A_snd a => free_A n a
  end.

Fixpoint free_AT (n : aname) (a : AT_syn) : bool :=
  match a with
  | AT_ground A => true
  | AT_pair A1 A2 => free_AT n A1 && free_AT n A2
  | AT_proj1 A => free_AT n A
  | AT_proj2 A => free_AT n A
  | AT_ket D => free_DT n D
  | AT_bra D => free_DT n D
  | AT_get a => free_A n a
  | AT_set A => free_AT n A
  | AT_st_get st => free_ST n st
  end
with free_DT (n : aname) (dt : DT_syn) : bool :=
  match dt with
  | DT_scale => true
  | DT_ket A => free_AT n A
  | DT_bra A => free_AT n A
  | DT_opt A1 A2 => free_AT n A1 && free_AT n A2
  | DT_s_get s => free_S n s
  | DT_k_get k => free_K n k
  | DT_b_get b => free_B n b
  | DT_o_get o => free_O n o
  end
with free_ST (n : aname) (st : ST_syn) : bool :=
  match st with
  | ST_var n => true
  | ST_uni A => free_AT n A
  | ST_prod S1 S2 => free_ST n S1 && free_ST n S2
  end
with free_S (n : aname) (s : S_scalar) : bool :=
  match s with
    | S_var n => true
    | S_0 => true
    | S_1 => true
    | S_delta a1 a2 => free_A n a1 && free_A n a2
    | S_add s1 s2 => free_S n s1 && free_S n s2
    | S_mul s1 s2 => free_S n s1 && free_S n s2
    | S_conj s => free_S n s
    | BK_inner b k => free_B n b && free_K n k
    | S_sum st m s => free_ST n st && ((n == m) || free_S n s)
  end
with free_K (n : aname) (k : K_ket) : bool :=
  match k with
    | K_var n => true
    | K_0 A => free_AT n A
    | K_ground t => free_A n t
    | B_adj b => free_B n b
    | K_scale s k => free_S n s && free_K n k
    | K_add k1 k2 => free_K n k1 && free_K n k2
    | K_apply o k => free_O n o && free_K n k
    | K_ten k1 k2 => free_K n k1 && free_K n k2
    | K_sum st m k => free_ST n st && ((n == m) || free_K n k)
  end
with free_B (n : aname) (b : B_bra) : bool := 
  match b with
    | B_var n => true
    | B_0 A => free_AT n A
    | B_ground t => free_A n t
    | K_adj k => free_K n k
    | B_scale s b => free_S n s && free_B n b
    | B_add b1 b2 => free_B n b1 && free_B n b2
    | B_apply b o => free_B n b && free_O n o
    | B_ten b1 b2 => free_B n b1 && free_B n b2
    | B_sum st m b => free_ST n st && ((n == m) || free_B n b)
  end
with free_O (n : aname) (o : O_opt) : bool := 
  match o with
    | O_var n => true
    | O_0 A1 A2 => free_AT n A1 && free_AT n A2
    | O_1 A => free_AT n A
    | KB_outer k b => free_K n k && free_B n b
    | O_adj o => free_O n o
    | O_scale s o => free_S n s && free_O n o
    | O_add o1 o2 => free_O n o1 && free_O n o2
    | O_comp o1 o2 => free_O n o1 && free_O n o2
    | O_ten o1 o2 => free_O n o1 && free_O n o2
    | O_sum st m o => free_ST n st && ((n == m) || free_O n o)
  end.

(* bound occurence: true (no appear), false (appear) *)
Fixpoint bound_AT (n : aname) (a : AT_syn) : bool :=
  match a with
  | AT_ground A => true
  | AT_pair A1 A2 => bound_AT n A1 && bound_AT n A2
  | AT_proj1 A => bound_AT n A
  | AT_proj2 A => bound_AT n A
  | AT_ket D => bound_DT n D
  | AT_bra D => bound_DT n D
  | AT_get a => true
  | AT_set A => bound_AT n A
  | AT_st_get st => bound_ST n st
  end
with bound_DT (n : aname) (dt : DT_syn) : bool :=
  match dt with
  | DT_scale => true
  | DT_ket A => bound_AT n A
  | DT_bra A => bound_AT n A
  | DT_opt A1 A2 => bound_AT n A1 && bound_AT n A2
  | DT_s_get s => bound_S n s
  | DT_k_get k => bound_K n k
  | DT_b_get b => bound_B n b
  | DT_o_get o => bound_O n o
  end
with bound_ST (n : aname) (st : ST_syn) : bool :=
  match st with
  | ST_var n => true
  | ST_uni A => bound_AT n A
  | ST_prod S1 S2 => bound_ST n S1 && bound_ST n S2
  end
with bound_S (n : aname) (s : S_scalar) : bool :=
  match s with
    | S_var n => true
    | S_0 => true
    | S_1 => true
    | S_delta a1 a2 => true
    | S_add s1 s2 => bound_S n s1 && bound_S n s2
    | S_mul s1 s2 => bound_S n s1 && bound_S n s2
    | S_conj s => bound_S n s
    | BK_inner b k => bound_B n b && bound_K n k
    | S_sum st m s => bound_ST n st && ((n != m) && bound_S n s)
  end
with bound_K (n : aname) (k : K_ket) : bool :=
  match k with
    | K_var n => true
    | K_0 A => bound_AT n A
    | K_ground t => true
    | B_adj b => bound_B n b
    | K_scale s k => bound_S n s && bound_K n k
    | K_add k1 k2 => bound_K n k1 && bound_K n k2
    | K_apply o k => bound_O n o && bound_K n k
    | K_ten k1 k2 => bound_K n k1 && bound_K n k2
    | K_sum st m k => bound_ST n st && ((n != m) && bound_K n k)
  end
with bound_B (n : aname) (b : B_bra) : bool := 
  match b with
    | B_var n => true
    | B_0 A => bound_AT n A
    | B_ground t => true
    | K_adj k => bound_K n k
    | B_scale s b => bound_S n s && bound_B n b
    | B_add b1 b2 => bound_B n b1 && bound_B n b2
    | B_apply b o => bound_B n b && bound_O n o
    | B_ten b1 b2 => bound_B n b1 && bound_B n b2
    | B_sum st m b => bound_ST n st && ((n != m) && bound_B n b)
  end
with bound_O (n : aname) (o : O_opt) : bool := 
  match o with
    | O_var n => true
    | O_0 A1 A2 => bound_AT n A1 && bound_AT n A2
    | O_1 A => bound_AT n A
    | KB_outer k b => bound_K n k && bound_B n b
    | O_adj o => bound_O n o
    | O_scale s o => bound_S n s && bound_O n o
    | O_add o1 o2 => bound_O n o1 && bound_O n o2
    | O_comp o1 o2 => bound_O n o1 && bound_O n o2
    | O_ten o1 o2 => bound_O n o1 && bound_O n o2
    | O_sum st m o => bound_ST n st && ((n != m) && bound_O n o)
  end.

(* n --> m *)
Fixpoint subst_A (n : aname) (s : A_base) (t : A_base) : A_base :=
  match t with
  | A_var l => if l == n then s else A_var l
  | A_ground _ t => A_ground t
  | A_pair a1 a2 => A_pair (subst_A n s a1) (subst_A n s a2)
  | A_fst t => A_fst (subst_A n s t)
  | A_snd t => A_snd (subst_A n s t)
  end.

Fixpoint subst_AT (n : aname) (s : A_base) (t : AT_syn) :=
  match t with
  | AT_ground A => AT_ground A
  | AT_pair A1 A2 => AT_pair (subst_AT n s A1) (subst_AT n s A2)
  | AT_proj1 A => AT_proj1 (subst_AT n s A)
  | AT_proj2 A => AT_proj2 (subst_AT n s A)
  | AT_ket D => AT_ket (subst_DT n s D)
  | AT_bra D => AT_bra (subst_DT n s D)
  | AT_get t => AT_get (subst_A n s t)
  | AT_set A => AT_set (subst_AT n s A)
  | AT_st_get st => AT_st_get (subst_ST n s st)
  end
with subst_DT (n : aname) (s : A_base) (dt : DT_syn) :=
  match dt with
  | DT_scale => DT_scale
  | DT_ket A => DT_ket (subst_AT n s A)
  | DT_bra A => DT_bra (subst_AT n s A)
  | DT_opt A1 A2 => DT_opt (subst_AT n s A1) (subst_AT n s A2)
  | DT_s_get Sc => DT_s_get (subst_S n s Sc)
  | DT_k_get K => DT_k_get (subst_K n s K)
  | DT_b_get B => DT_b_get (subst_B n s B)
  | DT_o_get Oo => DT_o_get (subst_O n s Oo)
  end
with subst_ST (n : aname) (s : A_base) (st : ST_syn) :=
  match st with
  | ST_var n => ST_var n
  | ST_uni A => ST_uni (subst_AT n s A)
  | ST_prod S1 S2 => ST_prod (subst_ST n s S1) (subst_ST n s S2)
  end
with subst_S (n : aname) (s : A_base) (Sc : S_scalar) :=
  match Sc with
    | S_var n => S_var n
    | S_0 => S_0
    | S_1 => S_1
    | S_delta a1 a2 => S_delta (subst_A n s a1) (subst_A n s a2)
    | S_add S1 S2 => S_add (subst_S n s S1) (subst_S n s S2)
    | S_mul S1 S2 => S_mul (subst_S n s S1) (subst_S n s S2)
    | S_conj Sc => S_conj (subst_S n s Sc)
    | BK_inner B K => BK_inner (subst_B n s B) (subst_K n s K)
    | S_sum st l Sc => 
        if l == n then S_sum (subst_ST n s st) l Sc (* we don't subst bound variable *)
        else S_sum (subst_ST n s st) l (subst_S n s Sc)
  end
with subst_K (n : aname) (s : A_base) (K : K_ket) :=
  match K with
    | K_var n => K_var n
    | K_0 A => K_0 (subst_AT n s A)
    | K_ground t => K_ground (subst_A n s t)
    | B_adj B => B_adj (subst_B n s B)
    | K_scale Sc K => K_scale (subst_S n s Sc) (subst_K n s K)
    | K_add K1 K2 => K_add (subst_K n s K1) (subst_K n s K2)
    | K_apply Oo K => K_apply (subst_O n s Oo) (subst_K n s K)
    | K_ten K1 K2 => K_ten (subst_K n s K1) (subst_K n s K2)
    | K_sum st l K => 
        if l == n then K_sum (subst_ST n s st) l K (* we don't subst bound variable *)
        else K_sum (subst_ST n s st) l (subst_K n s K)
  end
with subst_B (n : aname) (s : A_base) (B : B_bra) := 
  match B with
    | B_var n => B_var n
    | B_0 A => B_0 (subst_AT n s A)
    | B_ground t => B_ground (subst_A n s t)
    | K_adj K => K_adj (subst_K n s K)
    | B_scale Sc B => B_scale (subst_S n s Sc) (subst_B n s B)
    | B_add B1 B2 => B_add (subst_B n s B1) (subst_B n s B2)
    | B_apply B Oo => B_apply (subst_B n s B) (subst_O n s Oo)
    | B_ten B1 B2 => B_ten (subst_B n s B1) (subst_B n s B2)
    | B_sum st l B => 
        if l == n then B_sum (subst_ST n s st) l B (* we don't subst bound variable *)
        else B_sum (subst_ST n s st) l (subst_B n s B)
  end
with subst_O (n : aname) (s : A_base) (Oo : O_opt) := 
  match Oo with
    | O_var n => O_var n
    | O_0 A1 A2 => O_0 (subst_AT n s A1) (subst_AT n s A2)
    | O_1 A => O_1 (subst_AT n s A)
    | KB_outer K B => KB_outer (subst_K n s K) (subst_B n s B)
    | O_adj Oo => O_adj (subst_O n s Oo)
    | O_scale Sc Oo => O_scale (subst_S n s Sc) (subst_O n s Oo)
    | O_add O1 O2 => O_add (subst_O n s O1) (subst_O n s O2)
    | O_comp O1 O2 => O_comp (subst_O n s O1) (subst_O n s O2)
    | O_ten O1 O2 => O_ten (subst_O n s O1) (subst_O n s O2)
    | O_sum st l Oo => 
        if l == n then O_sum (subst_ST n s st) l Oo (* we don't subst bound variable *)
        else O_sum (subst_ST n s st) l (subst_O n s Oo)
  end.

Notation "X .[ i := x ] " := (subst_A i x%DA X%DA) 
  (at level 2, left associativity, format "X .[ i  :=  x ]") : base_scope.
Notation "X .[ i := x ] " := (subst_AT i x%DA X%AT) : atsyn_scope.
Notation "X .[ i := x ] " := (subst_DT i x%DA X%DT) : dtsyn_scope.
Notation "X .[ i := x ] " := (subst_ST i x%DA X%ST) : sttype_scope.
Notation "X .[ i := x ] " := (subst_S i x%DA X%DS) : scalar_scope.
Notation "X .[ i := x ] " := (subst_K i x%DA X%DK) : ket_scope.
Notation "X .[ i := x ] " := (subst_B i x%DA X%DB) : bra_scope.
Notation "X .[ i := x ] " := (subst_O i x%DA X%DO) : opt_scope.

Lemma A_set_cast A1 A2 (eqA : A1 = A2) (v : eval_AType A1) :
  A_set (cast_A eqA v) = A_set v.
Proof. by case: A2 / eqA. Qed.

Lemma A_value_update_id ca (av : A_value ca) n A (v : eval_AType A) :
  A_set (A_value_update av n v n) = A_set v.
Proof.
rewrite /dirac_notation.A_value_update.
by case: eqP=>// P; rewrite A_set_cast.
Qed.

Lemma A_value_update_eq ca (av : A_value ca) n m A (v : eval_AType A) :
  n = m ->  A_set (A_value_update av n v m) = A_set v.
Proof. move=>P; case: m / P; exact: A_value_update_id. Qed.

Lemma A_value_update_neq ca (av : A_value ca) n m A (v : eval_AType A) :
  n <> m ->  A_set (A_value_update av n v m) = A_set (av m).
Proof.
rewrite /dirac_notation.A_value_update.
case: eqP=>// P. by rewrite {1}P.
by rewrite A_set_cast.
Qed.

Lemma subst_A_type (n : aname) s [a] ca :
  atype_checker ca s = Some (ca n) ->
    atype_checker ca (a.[n := s])%DA = atype_checker ca a.
Proof.
move=>P; elim: a=>//=.
- move=>m; case: eqP=>[->|//]; by rewrite P.
- by move=>a1 -> a2 ->.
- by move=>a ->.
- by move=>a ->.
Qed.

Lemma Gamma_A_update_ident ca m : Gamma_A_update ca m (ca m) = ca.
Proof.
apply/functional_extensionality_dep=>n; case: (@eqP _ m n).
by move=>->; rewrite Gamma_A_update_id.
by move=>P; rewrite Gamma_A_update_neq; auto.
Qed.

Lemma subst_A_sem (n : aname) s [a] ca [av : A_value ca] :
  atype_checker ca s = Some (ca n) ->
    A_sem (A_value_update av n (A_sem av s (ca n))) a = A_sem av (a.[n := s])%DA.
Proof.
move=>P.
elim: a=>//=.
- move=> m; case: eqP=>[->|H].
  by rewrite A_value_update_id A_set_sem.
  by rewrite /= A_value_update_neq//; auto.
- by move=>a1 -> a2 ->; rewrite !Gamma_A_update_ident !(subst_A_type P).
- by move=>a ->; rewrite Gamma_A_update_ident (subst_A_type P).
- by move=>a ->; rewrite Gamma_A_update_ident (subst_A_type P).
Qed.

Lemma free_A_type n t ca A :
  free_A n t -> atype_checker (Gamma_A_update ca n A) t = atype_checker ca t.
Proof.
elim: t ca=>//=.
move=>m ca /eqP P; rewrite Gamma_A_update_neq//; auto.
by move=>a1 IH1 a2 IH2 ca /andP[] /IH1 -> /IH2 ->.
by move=>a IH ca /IH ->.
by move=>a IH ca /IH ->.
Qed.

Lemma free_A_sem n t ca (av : A_value ca) A (a : eval_AType A) :
  free_A n t ->
    A_sem (A_value_update av n a) t = A_sem av t.
Proof.
elim: t ca av=>//=.
by move=>m ca av /eqP P; rewrite A_value_update_neq.
move=>a1 IH1 a2 IH2 ca av /andP[] P1 P2.
by rewrite !free_A_type// IH1// IH2.
move=>t IH ca av P.
by rewrite free_A_type// IH.
move=>t IH ca av P.
by rewrite free_A_type// IH.
Qed.

(* evaluation of free variable does not effect semantics *)
Let free_AT_sem_eq := 
    forall AT (n : aname) ca A,
      free_AT n AT ->
        AT_sem (Gamma_A_update ca n A) AT = AT_sem ca AT.
Let free_DT_sem_eq :=
    forall D (n : aname) ca A,
      free_DT n D ->
        DT_sem (Gamma_A_update ca n A) D = DT_sem ca D.
Let free_ST_type_eq :=
  forall S (n : aname) ca A,
    free_ST n S ->
      sttype_checker (Gamma_A_update ca n A) S = sttype_checker ca S.
Let free_S_type_eq :=
  forall S (n : aname) ca A,
    free_S n S ->
      stype_checker (Gamma_A_update ca n A) S = stype_checker ca S.
Let free_K_type_eq :=
  forall K (n : aname) ca A,
    free_K n K ->
      ktype_checker (Gamma_A_update ca n A) K = ktype_checker ca K.
Let free_B_type_eq :=
  forall B (n : aname) ca A,
    free_B n B ->
      btype_checker (Gamma_A_update ca n A) B = btype_checker ca B.
Let free_O_type_eq :=
  forall O (n : aname) ca A,
    free_O n O ->
      otype_checker (Gamma_A_update ca n A) O = otype_checker ca O.

Lemma Gamma_A_update_idm ca n A1 A2 :
  Gamma_A_update (Gamma_A_update ca n A1) n A2 = 
    Gamma_A_update ca n A2.
Proof.
apply/functional_extensionality_dep=>m.
case: (@eqP _ m n)=>[ <-|P].
by rewrite !Gamma_A_update_id.
by rewrite !Gamma_A_update_neq.
Qed.

Lemma Gamma_A_updateC ca n m A1 A2 :
  n <> m ->
  Gamma_A_update (Gamma_A_update ca n A1) m A2 = 
    Gamma_A_update (Gamma_A_update ca m A2) n A1.
Proof.
move=>P.
apply/functional_extensionality_dep=>k.
case: (@eqP _ k m)=>[->|P1].
rewrite Gamma_A_update_id Gamma_A_update_neq ?Gamma_A_update_id//; auto.
rewrite Gamma_A_update_neq//.
case: (@eqP _ k n)=>[->|P2].
by rewrite !Gamma_A_update_id .
by rewrite !Gamma_A_update_neq.
Qed.

Lemma free_type : free_AT_sem_eq /\ free_DT_sem_eq /\ free_ST_type_eq /\ 
  free_S_type_eq /\ free_K_type_eq /\ free_B_type_eq /\ free_O_type_eq.
Proof.
Ltac l25 := by move=>A1 IH1 A2 IH2 n ca A /andP[] /IH1-> /IH2->.
Ltac l15 := by move=>A IH n ca A1 /IH->.
apply All_syn_mutind=>//=; try l25; try l15.
- by move=>a n ca A P; rewrite free_A_type.
- by move=>a1 a2 n ca A /andP[] P1 P2; rewrite !free_A_type.
- move=>st IH1 n s IH2 m ca A /andP[] P1 /orP[/eqP P2|P2].
  rewrite P2 IH1. by rewrite -P2.
  case: (sttype_checker _ _)=>// A1.
  by rewrite Gamma_A_update_idm.
  rewrite IH1//.
  case: (sttype_checker _ _)=>// A1.
  case: (@eqP _ m n)=>[ <-|P3].
  by rewrite Gamma_A_update_idm.
  by rewrite Gamma_A_updateC// IH2.
- by move=>t n ca A P; rewrite free_A_type.
- move=>st IH1 n s IH2 m ca A /andP[] P1 /orP[/eqP P2|P2].
  rewrite P2 IH1. by rewrite -P2.
  case: (sttype_checker _ _)=>// A1.
  by rewrite Gamma_A_update_idm.
  rewrite IH1//.
  case: (sttype_checker _ _)=>// A1.
  case: (@eqP _ m n)=>[ <-|P3].
  by rewrite Gamma_A_update_idm.
  by rewrite Gamma_A_updateC// IH2.
- by move=>t n ca A P; rewrite free_A_type.
- move=>st IH1 n s IH2 m ca A /andP[] P1 /orP[/eqP P2|P2].
  rewrite P2 IH1. by rewrite -P2.
  case: (sttype_checker _ _)=>// A1.
  by rewrite Gamma_A_update_idm.
  rewrite IH1//.
  case: (sttype_checker _ _)=>// A1.
  case: (@eqP _ m n)=>[ <-|P3].
  by rewrite Gamma_A_update_idm.
  by rewrite Gamma_A_updateC// IH2.
- move=>st IH1 n s IH2 m ca A /andP[] P1 /orP[/eqP P2|P2].
  rewrite P2 IH1. by rewrite -P2.
  case: (sttype_checker _ _)=>// A1.
  by rewrite Gamma_A_update_idm.
  rewrite IH1//.
  case: (sttype_checker _ _)=>// A1.
  case: (@eqP _ m n)=>[ <-|P3].
  by rewrite Gamma_A_update_idm.
  by rewrite Gamma_A_updateC// IH2.
Qed.

Lemma free_AT_sem  AT (n : aname) ca A :
      free_AT n AT ->
        AT_sem (Gamma_A_update ca n A) AT = AT_sem ca AT.
Proof. by move: free_type AT n ca A=>[]. Qed.

Lemma free_DT_sem  D (n : aname) ca A :
      free_DT n D ->
        DT_sem (Gamma_A_update ca n A) D = DT_sem ca D.
Proof. by move: free_type D n ca A=>[] _ []. Qed.

Lemma free_ST_type  S (n : aname) ca A :
    free_ST n S ->
      sttype_checker (Gamma_A_update ca n A) S = sttype_checker ca S.
Proof. by move: free_type S n ca A=>[] _ [] _ []. Qed.

Lemma free_S_type  S (n : aname) ca A :
    free_S n S ->
      stype_checker (Gamma_A_update ca n A) S = stype_checker ca S.
Proof. by move: free_type S n ca A=>[] _ [] _ [] _ []. Qed.

Lemma free_K_type  K (n : aname) ca A :
    free_K n K ->
      ktype_checker (Gamma_A_update ca n A) K = ktype_checker ca K.
Proof. by move: free_type K n ca A=>[] _ [] _ [] _ [] _ []. Qed.

Lemma free_B_type  B (n : aname) ca A :
    free_B n B ->
      btype_checker (Gamma_A_update ca n A) B = btype_checker ca B.
Proof. by move: free_type B n ca A=>[] _ [] _ [] _ [] _ [] _ []. Qed.

Lemma free_O_type  O (n : aname) ca A :
    free_O n O ->
      otype_checker (Gamma_A_update ca n A) O = otype_checker ca O.
Proof. by move: free_type O n ca A=>[] _ [] _ [] _ [] _ [] _ []. Qed.

Lemma free_ST_sem S (n : aname) ca A :
  free_ST n S ->
    ST_sem (Gamma_A_update ca n A) stv S = ST_sem ca stv S.
Proof.
elim: S=>//=.
move=>A1 IH1 A2 IH2 /andP[] P1 P2.
by rewrite !free_ST_type// IH1// IH2.
Qed.

Let free_S_sem_eq :=
  forall S (n : aname) ca (av : A_value ca) A (a : eval_AType A),
    free_S n S ->
      S_sem (A_value_update av n a) S = S_sem av S.
Let free_K_sem_eq :=
  forall K (n : aname) ca (av : A_value ca) A (a : eval_AType A),
    free_K n K ->
      K_sem (A_value_update av n a) K = K_sem av K.
Let free_B_sem_eq :=
  forall B (n : aname) ca (av : A_value ca) A (a : eval_AType A),
    free_B n B ->
      B_sem (A_value_update av n a) B = B_sem av B.
Let free_O_sem_eq :=
  forall O (n : aname) ca (av : A_value ca) A (a : eval_AType A),
    free_O n O ->
      O_sem (A_value_update av n a) O = O_sem av O.

Definition A_vale_eq ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :=
  (forall i, ca1 i = ca2 i) /\
    (forall i, if ca1 i =P ca2 i is ReflectT eq then
                  cast_A eq (av1 i) = av2 i
               else True).
Notation "av1 '=av' av2" := (A_vale_eq av1 av2) (at level 70).

Ltac lav ca1 ca2 av1 av2 :=
  let P1 := fresh "P" in
  let P := fresh "P" in
  let x := fresh "x" in
  move=>[] /funext P1; case: ca2 / P1 av2=> av2 P; f_equal;
  apply/functional_extensionality_dep=>x; move: (P x);
  by case: eqP=>// P1; rewrite eq_axiomK/=.

Lemma S_sem_eq S ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :
  av1 =av av2 -> S_sem av1 S = S_sem av2 S.
Proof. lav ca1 ca2 av1 av2. Qed.

Lemma K_sem_eq K ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :
  av1 =av av2 -> K_sem av1 K = K_sem av2 K.
Proof. lav ca1 ca2 av1 av2. Qed.

Lemma B_sem_eq B ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :
  av1 =av av2 -> B_sem av1 B = B_sem av2 B.
Proof. lav ca1 ca2 av1 av2. Qed.

Lemma O_sem_eq O ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :
  av1 =av av2 -> O_sem av1 O = O_sem av2 O.
Proof. lav ca1 ca2 av1 av2. Qed.

Lemma A_set_eq i ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :
  av1 =av av2 -> A_set (av1 i) = A_set (av2 i).
Proof.
move=>[] /funext P1; case: ca2 / P1 av2=> av2 P.
suff ->: av1 = av2 by [].
apply/functional_extensionality_dep=>x; move: (P x);
by case: eqP=>// P1; rewrite eq_axiomK/=.
Qed.

Lemma A_value_update_idm ca (av : A_value ca) n A1 A2 
  (v1 : eval_AType A1) (v2 : eval_AType A2) :
  (A_value_update (A_value_update av n v1) n v2) =av
    (A_value_update av n v2).
Proof.
split=>i.
  by rewrite Gamma_A_update_idm.
case: eqP=>[P|]; last by rewrite Gamma_A_update_idm.
rewrite -[RHS]A_set_id -[LHS]A_set_id A_set_cast.
case: (@eqP _ i n)=>[ <-|P1].
  by rewrite {-3}Gamma_A_update_id !A_value_update_id.
rewrite {-3}Gamma_A_update_neq// !A_value_update_neq//; auto.
Qed.

Lemma A_value_eq_sym ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :
  av1 =av av2 -> av2 =av av1.
Proof.
move=>[]/funext P1; case: _ / P1 av2=>av2 P.
split=>// i. case: eqP=>// P1.
move: (P i); case: eqP=>// P2.
by rewrite !eq_axiomK.
Qed.

Lemma A_value_updateC ca (av : A_value ca) n m A1 A2 
  (v1 : eval_AType A1) (v2 : eval_AType A2) :
  n <> m ->
  (A_value_update (A_value_update av n v1) m v2) =av
    (A_value_update (A_value_update av m v2) n v1).
Proof.
move=>P1; split=>i.
  by rewrite Gamma_A_updateC.
case: eqP=>[P|]; last by rewrite Gamma_A_updateC.
rewrite -[RHS]A_set_id -[LHS]A_set_id A_set_cast.
case: (@eqP _ i n)=>[->|P2].
  rewrite {-3}Gamma_A_update_id A_value_update_neq; auto.
  by rewrite !A_value_update_id.
case: (@eqP _ i m)=>[->|P3].
  rewrite {-3}Gamma_A_update_neq; auto.
  by rewrite Gamma_A_update_id A_value_update_id A_value_update_neq// A_value_update_id.
rewrite {-3}Gamma_A_update_neq// [Gamma_A_update ca m A2 i]Gamma_A_update_neq//.
by rewrite !A_value_update_neq//; auto.
Qed.

Lemma free_sem : free_S_sem_eq /\ free_K_sem_eq /\ free_B_sem_eq /\ free_O_sem_eq.
Proof.
Ltac l26 :=
  let IH1 := fresh "IH" in
  let IH2 := fresh "IH" in
  move=>? IH1 ? IH2 ????? /andP[] ??;
  by rewrite ?free_S_type ?free_K_type ?free_B_type ?free_O_type// IH1// IH2.
Ltac l16 :=
  let IH := fresh "IH" in
  move=>? IH ??????;
  by rewrite ?free_S_type ?free_K_type ?free_B_type ?free_O_type// IH.
apply Dirac_syn_mutind=>//=; try l26; try l16.
- move=>a1 a2 n ca av A a /andP[] P1 P2;
  by rewrite !free_A_type// !free_A_sem.
- move=>st n s IH m ca av A a /andP[] P1 /orP[/eqP P2|P2].
    rewrite free_ST_type// free_ST_sem//.
    case: (sttype_checker _ _)=>// A1; apply eq_bigr=>i _; rewrite P2.
    by apply/S_sem_eq/A_value_update_idm. 
  rewrite free_ST_type// free_ST_sem//.
  case: (sttype_checker _ _)=>// A1; apply eq_bigr=>i _.
  case: (@eqP _ n m)=>P.
    by rewrite P; apply/S_sem_eq/A_value_update_idm.
  rewrite -(S_sem_eq s (A_value_updateC av i a P)) IH//.
- move=>a n ca av A v P.
  rewrite free_A_type// free_A_sem//.
- move=>st n k IH m ca av A a /andP[] P1 /orP[/eqP P2|P3].
  2 : case: (@eqP _ m n)=>P2.
    1,2: rewrite -P2 !free_ST_type// free_ST_sem//;
         case: (sttype_checker _ _)=>// A1;
         rewrite {1}Gamma_A_update_idm;
         case: (ktype_checker _ _)=>// [[]]// A2;
         f_equal; apply eq_bigr=>i _; rewrite P2;
         by rewrite (K_sem_eq k (A_value_update_idm _ _ _ _)).
  rewrite !free_ST_type// !free_ST_sem//.
  case: (sttype_checker _ _)=>// A1.
  rewrite {1}Gamma_A_updateC// free_K_type//.
  case: (ktype_checker _ _)=>// [[]]// A2; f_equal.
  apply eq_bigr=>i _.
  rewrite (K_sem_eq k (A_value_updateC av a i P2)) IH//.
- move=>a n ca av A v P.
  rewrite free_A_type// free_A_sem//.
- move=>st n b IH m ca av A a /andP[] P1 /orP[/eqP P2|P3].
  2 : case: (@eqP _ m n)=>P2.
    1,2: rewrite -P2 !free_ST_type// free_ST_sem//;
         case: (sttype_checker _ _)=>// A1;
         rewrite {1}Gamma_A_update_idm;
         case: (btype_checker _ _)=>// [[]]// A2;
         f_equal; apply eq_bigr=>i _; rewrite P2;
         by rewrite (B_sem_eq b (A_value_update_idm _ _ _ _)).
  rewrite !free_ST_type// !free_ST_sem//.
  case: (sttype_checker _ _)=>// A1.
  rewrite {1}Gamma_A_updateC// free_B_type//.
  case: (btype_checker _ _)=>// [[]]// A2; f_equal.
  apply eq_bigr=>i _.
  rewrite (B_sem_eq b (A_value_updateC av a i P2)) IH//.
- move=>a n ca av A v P; rewrite free_AT_sem//.
- move=>st n o IH m ca av A a /andP[] P1 /orP[/eqP P2|P3].
  2 : case: (@eqP _ m n)=>P2.
    1,2: rewrite -P2 !free_ST_type// free_ST_sem//;
         case: (sttype_checker _ _)=>// A1;
         rewrite {1}Gamma_A_update_idm;
         case: (otype_checker _ _)=>// [[]]// A2;
         f_equal; apply eq_bigr=>i _; rewrite P2;
         by rewrite (O_sem_eq o (A_value_update_idm _ _ _ _)).
  rewrite !free_ST_type// !free_ST_sem//.
  case: (sttype_checker _ _)=>// A1.
  rewrite {1}Gamma_A_updateC// free_O_type//.
  case: (otype_checker _ _)=>// [[]]// A2; f_equal.
  apply eq_bigr=>i _.
  rewrite (O_sem_eq o (A_value_updateC av a i P2)) IH//.
Qed.

Lemma free_S_sem S (n : aname) ca (av : A_value ca) A (a : eval_AType A) :
    free_S n S ->
      S_sem (A_value_update av n a) S = S_sem av S.
Proof. by move: free_sem S n ca av A a=>[]. Qed.

Lemma free_K_sem K (n : aname) ca (av : A_value ca) A (a : eval_AType A) :
    free_K n K ->
      K_sem (A_value_update av n a) K = K_sem av K.
Proof. by move: free_sem K n ca av A a=>[] _ []. Qed.

Lemma free_B_sem B (n : aname) ca (av : A_value ca) A (a : eval_AType A) :
    free_B n B ->
      B_sem (A_value_update av n a) B = B_sem av B.
Proof. by move: free_sem B n ca av A a=>[] _ [] _ []. Qed.

Lemma free_O_sem O (n : aname) ca (av : A_value ca) A (a : eval_AType A) :
    free_O n O ->
      O_sem (A_value_update av n a) O = O_sem av O.
Proof. by move: free_sem O n ca av A a=>[] _ [] _ []. Qed.

Let subst_AT_sem_eq := 
    forall A (n : aname) (s : A_base) ca,
      atype_checker ca s = Some (ca n) -> 
        (forall m, ~~(bound_AT m A) -> free_A m s) ->
        AT_sem ca (subst_AT n s A) = AT_sem ca A.
Let subst_DT_sem_eq :=
  forall D (n : aname) (s : A_base) ca,
    atype_checker ca s = Some (ca n) -> 
        (forall m, ~~(bound_DT m D) -> free_A m s) ->
      DT_sem ca (subst_DT n s D) = DT_sem ca D.
Let subst_ST_type_eq :=
  forall S (n : aname) (s : A_base) ca,
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_ST m S) -> free_A m s) ->
      sttype_checker ca (subst_ST n s S) = sttype_checker ca S.
Let subst_S_type_eq :=
  forall S (n : aname) (s : A_base) ca,
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_S m S) -> free_A m s) ->
      stype_checker ca (subst_S n s S) = stype_checker ca S.
Let subst_K_type_eq :=
  forall K (n : aname) (s : A_base) ca,
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_K m K) -> free_A m s) ->
      ktype_checker ca (subst_K n s K) = ktype_checker ca K.
Let subst_B_type_eq :=
  forall B (n : aname) (s : A_base) ca,
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_B m B) -> free_A m s) ->
      btype_checker ca (subst_B n s B) = btype_checker ca B.
Let subst_O_type_eq :=
  forall O (n : aname) (s : A_base) ca,
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_O m O) -> free_A m s) ->
      otype_checker ca (subst_O n s O) = otype_checker ca O.

Lemma subst_type : subst_AT_sem_eq /\ subst_DT_sem_eq /\ subst_ST_type_eq /\ 
  subst_S_type_eq /\ subst_K_type_eq /\ subst_B_type_eq /\ subst_O_type_eq.
Proof.
Ltac l22 :=
  let IH1 := fresh "IH" in
  let IH2 := fresh "IH" in
  let X := fresh "X" in
  let Pm := fresh "Pm" in
  move=>A1 IH1 A2 IH2 n s ca P X;
  by rewrite ?IH1 ?IH2// =>m Pm; apply X; rewrite negb_and Pm// orbT.
Ltac l11 := 
  let IH := fresh "IH" in  
  by move=>A IH n s ca P1 P2; rewrite IH.
apply All_syn_mutind=>//=; try l22; try l11.
- by move=>a n s ca P; rewrite (subst_A_type P).
- by move=>a1 a2 n s ca P; rewrite !(subst_A_type P).
- move=>st IH1 n s IH2 m t ca P1 P2.
  case: eqP=>//= P3; rewrite IH1//.
    1,2: by move=>l Pl; apply P2; rewrite negb_and Pl.
  case: (sttype_checker _ _)=>// A; rewrite IH2//.
  move: (P2 n); rewrite eqxx/= andbF=>/(_ is_true_true) Pt.
    by rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
  by move=>l Pl; apply P2; rewrite !negb_and Pl !orbT.
- by move=>a n s ca IH P; rewrite subst_A_type.
- move=>st IH1 n s IH2 m t ca P1 P2.
  case: eqP=>//= P3; rewrite IH1//.
    1,2: by move=>l Pl; apply P2; rewrite negb_and Pl.
  case: (sttype_checker _ _)=>// A; rewrite IH2//.
  move: (P2 n); rewrite eqxx/= andbF=>/(_ is_true_true) Pt.
    by rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
  by move=>l Pl; apply P2; rewrite !negb_and Pl !orbT.
- by move=>a n s ca IH P; rewrite subst_A_type.
- move=>st IH1 n s IH2 m t ca P1 P2.
  case: eqP=>//= P3; rewrite IH1//.
    1,2: by move=>l Pl; apply P2; rewrite negb_and Pl.
  case: (sttype_checker _ _)=>// A; rewrite IH2//.
  move: (P2 n); rewrite eqxx/= andbF=>/(_ is_true_true) Pt.
    by rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
  by move=>l Pl; apply P2; rewrite !negb_and Pl !orbT.
- move=>st IH1 n s IH2 m t ca P1 P2.
  case: eqP=>//= P3; rewrite IH1//.
    1,2: by move=>l Pl; apply P2; rewrite negb_and Pl.
  case: (sttype_checker _ _)=>// A; rewrite IH2//.
  move: (P2 n); rewrite eqxx/= andbF=>/(_ is_true_true) Pt.
    by rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
  by move=>l Pl; apply P2; rewrite !negb_and Pl !orbT.
Qed.

Lemma subst_AT_sem A (n : aname) (s : A_base) ca:
      atype_checker ca s = Some (ca n) -> 
        (forall m, ~~(bound_AT m A) -> free_A m s) ->
        AT_sem ca (A.[n := s])%AT = AT_sem ca A.
Proof. by move: subst_type A n s ca=>[]. Qed.

Lemma subst_DT_sem D (n : aname) (s : A_base) ca:
    atype_checker ca s = Some (ca n) -> 
        (forall m, ~~(bound_DT m D) -> free_A m s) ->
      DT_sem ca (D.[n := s])%DT = DT_sem ca D.
Proof. by move: subst_type D n s ca=>[] _ []. Qed.

Lemma subst_ST_type S (n : aname) (s : A_base) ca :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_ST m S) -> free_A m s) ->
      sttype_checker ca (S.[n := s])%ST = sttype_checker ca S.
Proof. by move: subst_type S n s ca=>[] _ [] _ []. Qed.

Lemma subst_S_type S (n : aname) (s : A_base) ca :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_S m S) -> free_A m s) ->
      stype_checker ca (S.[n := s])%DS = stype_checker ca S.
Proof. by move: subst_type S n s ca=>[] _ [] _ [] _ []. Qed.

Lemma subst_K_type K (n : aname) (s : A_base) ca :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_K m K) -> free_A m s) ->
      ktype_checker ca (K.[n := s])%DK = ktype_checker ca K.
Proof. by move: subst_type K n s ca=>[] _ [] _ [] _ [] _ []. Qed.

Lemma subst_B_type B (n : aname) (s : A_base) ca :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_B m B) -> free_A m s) ->
      btype_checker ca (B.[n := s])%DB = btype_checker ca B.
Proof. by move: subst_type B n s ca=>[] _ [] _ [] _ [] _ [] _ []. Qed.

Lemma subst_O_type O (n : aname) (s : A_base) ca :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_O m O) -> free_A m s) ->
      otype_checker ca (O.[n := s])%DO = otype_checker ca O.
Proof. by move: subst_type O n s ca=>[] _ [] _ [] _ [] _ [] _ []. Qed.

Lemma subst_ST_sem S (n : aname) (s : A_base) ca :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_ST m S) -> free_A m s) ->
      ST_sem ca stv (S.[n := s])%ST = ST_sem ca stv S.
Proof.
elim: S=>//=.
move=>A1 IH1 A2 IH2 P1 P2.
rewrite !subst_ST_type// ?IH1 ?IH2//.
all: by move=>m Pm; apply P2; rewrite negb_and Pm// orbT.
Qed.

Let subst_S_sem_eq :=
  forall S (n : aname) (s : A_base) ca (av : A_value ca),
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_S m S) -> free_A m s) ->
      S_sem (A_value_update av n (A_sem av s (ca n)) ) S = S_sem av (subst_S n s S).
Let subst_K_sem_eq :=
  forall K (n : aname) (s : A_base) ca (av : A_value ca),
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_K m K) -> free_A m s) ->
      K_sem (A_value_update av n (A_sem av s (ca n)) ) K = K_sem av (subst_K n s K).
Let subst_B_sem_eq :=
  forall B (n : aname) (s : A_base) ca (av : A_value ca),
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_B m B) -> free_A m s) ->
      B_sem (A_value_update av n (A_sem av s (ca n)) ) B = B_sem av (subst_B n s B).
Let subst_O_sem_eq :=
  forall O (n : aname) (s : A_base) ca (av : A_value ca),
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_O m O) -> free_A m s) ->
      O_sem (A_value_update av n (A_sem av s (ca n)) ) O = O_sem av (subst_O n s O).

Lemma subst_sem : subst_S_sem_eq /\ subst_K_sem_eq /\ subst_B_sem_eq /\ subst_O_sem_eq.
Ltac l23 :=
  let IH1 := fresh "IH" in
  let IH2 := fresh "IH" in
  let P2 := fresh "P" in
  let Pm := fresh "Pm" in
  move=>? IH1 ? IH2 ????? P2;
  rewrite IH1 ?IH2 ?Gamma_A_update_ident ?subst_S_type ?subst_K_type ?subst_B_type ?subst_O_type//;
  by move=>? Pm; apply P2; rewrite negb_and Pm // orbT.
Ltac l24 :=
  let IH := fresh "IH" in
  move=>? IH ??????;
  by rewrite IH// Gamma_A_update_ident ?subst_S_type ?subst_K_type ?subst_B_type ?subst_O_type.
apply Dirac_syn_mutind=>//=; try l23; try l24.
- move=>a1 a2 n s ca av P1 P2.
  by rewrite !subst_A_sem// !Gamma_A_update_ident !subst_A_type.
- move=>st m S IH1 n s ca av P1 P2.
  case: eqP=>[->/=|P].
    rewrite {1}Gamma_A_update_ident subst_ST_type//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    case: (sttype_checker _ _)=>// A.
    rewrite {1}Gamma_A_update_ident subst_ST_sem//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    apply eq_bigr=>i _.
    by apply/S_sem_eq/A_value_update_idm.
  rewrite /= {1 2}Gamma_A_update_ident !subst_ST_sem// ?subst_ST_type//.
    1,2: by move=>k Pk; apply/P2; rewrite negb_and Pk.
  case: (sttype_checker _ _)=>// A.
  apply eq_bigr=>i _.
  move: (P2 m); rewrite negb_and eqxx/= orbT=>/(_ is_true_true) Pm.
  rewrite -(S_sem_eq S (A_value_updateC av i (A_sem av s (ca n)) P)) -IH1.
    rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
    by move=>k Pk; apply P2; rewrite !negb_and Pk !orbT.
  rewrite free_A_sem// Gamma_A_update_neq//; auto.
- move=>a n s ca av P1 P2.
  by rewrite !subst_A_sem// !Gamma_A_update_ident !subst_A_type.
- move=>st m S IH1 n s ca av P1 P2.
  case: eqP=>[->/=|P].
    rewrite {1}Gamma_A_update_ident subst_ST_type//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    case: (sttype_checker _ _)=>// A.
    rewrite {1 2}Gamma_A_update_ident subst_ST_sem//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    case: (ktype_checker _ _)=>// [[]]// A1; f_equal.
    apply eq_bigr=>i _.
    by rewrite (K_sem_eq S (A_value_update_idm av n _ _)).
  rewrite /= {1 2 3}Gamma_A_update_ident !subst_ST_sem// ?subst_ST_type//.
    1,2: by move=>k Pk; apply/P2; rewrite negb_and Pk.
  case: (sttype_checker _ _)=>// A.
  move: (P2 m); rewrite negb_and eqxx/= orbT=>/(_ is_true_true) Pm.
  rewrite subst_K_type ?free_A_type// ?Gamma_A_update_neq//; auto.
    by move=>k Pk; apply/P2; rewrite !negb_and Pk ?orbT.
  case: (ktype_checker _ _)=>// [[]]// A1; f_equal.
  apply eq_bigr=>i _.
  rewrite -(K_sem_eq S (A_value_updateC av i (A_sem av s (ca n)) P)) -IH1.
    rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
    by move=>k Pk; apply P2; rewrite !negb_and Pk !orbT.
  rewrite free_A_sem// Gamma_A_update_neq//; auto.
- move=>a n s ca av P1 P2.
  by rewrite !subst_A_sem// !Gamma_A_update_ident !subst_A_type.
- move=>st m S IH1 n s ca av P1 P2.
  case: eqP=>[->/=|P].
    rewrite {1}Gamma_A_update_ident subst_ST_type//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    case: (sttype_checker _ _)=>// A.
    rewrite {1 2}Gamma_A_update_ident subst_ST_sem//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    case: (btype_checker _ _)=>// [[]]// A1; f_equal.
    apply eq_bigr=>i _.
    by rewrite (B_sem_eq S (A_value_update_idm av n _ _)).
  rewrite /= {1 2 3}Gamma_A_update_ident !subst_ST_sem// ?subst_ST_type//.
    1,2: by move=>k Pk; apply/P2; rewrite negb_and Pk.
  case: (sttype_checker _ _)=>// A.
  move: (P2 m); rewrite negb_and eqxx/= orbT=>/(_ is_true_true) Pm.
  rewrite subst_B_type ?free_A_type// ?Gamma_A_update_neq//; auto.
    by move=>k Pk; apply/P2; rewrite !negb_and Pk ?orbT.
  case: (btype_checker _ _)=>// [[]]// A1; f_equal.
  apply eq_bigr=>i _.
  rewrite -(B_sem_eq S (A_value_updateC av i (A_sem av s (ca n)) P)) -IH1.
    rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
    by move=>k Pk; apply P2; rewrite !negb_and Pk !orbT.
  rewrite free_A_sem// Gamma_A_update_neq//; auto.
- move=>a n s ca av P1 P2.
  rewrite Gamma_A_update_ident subst_AT_sem//.
- move=>st m S IH1 n s ca av P1 P2.
  case: eqP=>[->/=|P].
    rewrite {1}Gamma_A_update_ident subst_ST_type//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    case: (sttype_checker _ _)=>// A.
    rewrite {1 2}Gamma_A_update_ident subst_ST_sem//.
      by move=>k Pk; apply P2; rewrite negb_and Pk.
    case: (otype_checker _ _)=>// [[]]// A1; f_equal.
    apply eq_bigr=>i _.
    by rewrite (O_sem_eq S (A_value_update_idm av n _ _)).
  rewrite /= {1 2 3}Gamma_A_update_ident !subst_ST_sem// ?subst_ST_type//.
    1,2: by move=>k Pk; apply/P2; rewrite negb_and Pk.
  case: (sttype_checker _ _)=>// A.
  move: (P2 m); rewrite negb_and eqxx/= orbT=>/(_ is_true_true) Pm.
  rewrite subst_O_type ?free_A_type// ?Gamma_A_update_neq//; auto.
    by move=>k Pk; apply/P2; rewrite !negb_and Pk ?orbT.
  case: (otype_checker _ _)=>// [[]]// A1; f_equal.
  apply eq_bigr=>i _.
  rewrite -(O_sem_eq S (A_value_updateC av i (A_sem av s (ca n)) P)) -IH1.
    rewrite free_A_type// P1 Gamma_A_update_neq//; auto.
    by move=>k Pk; apply P2; rewrite !negb_and Pk !orbT.
  rewrite free_A_sem// Gamma_A_update_neq//; auto.
Qed.

Lemma subst_S_sem S (n : aname) (s : A_base) ca (av : A_value ca) :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~ (bound_S m S) -> free_A m s) ->
      S_sem (A_value_update av n (A_sem av s (ca n)) ) S = S_sem av (S.[n := s])%DS.
Proof. by move: subst_sem S n s ca av=>[]. Qed.

Lemma subst_K_sem K (n : aname) (s : A_base) ca (av : A_value ca) :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_K m K) -> free_A m s) ->
      K_sem (A_value_update av n (A_sem av s (ca n)) ) K = K_sem av (K.[n := s])%DK.
Proof. by move: subst_sem K n s ca av=>[] _ []. Qed.

Lemma subst_B_sem B (n : aname) (s : A_base) ca (av : A_value ca) :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_B m B) -> free_A m s) ->
      B_sem (A_value_update av n (A_sem av s (ca n)) ) B = B_sem av (B.[n := s])%DB.
Proof. by move: subst_sem B n s ca av=>[] _ [] _ []. Qed.

Lemma subst_O_sem O (n : aname) (s : A_base) ca (av : A_value ca) :
    atype_checker ca s = Some (ca n) ->
        (forall m, ~~(bound_O m O) -> free_A m s) ->
      O_sem (A_value_update av n (A_sem av s (ca n)) ) O = O_sem av (O.[n := s])%DO.
Proof. by move: subst_sem O n s ca av=>[] _ [] _ []. Qed.

Lemma free_A_subst t n s :
  free_A n s -> free_A n (t.[n := s])%DA.
Proof.
move=>P; elim: t=>//=.
by move=>m; case: eqP=>//= /eqP/negPf; rewrite eq_sym=>->.
by move=>a1 -> a2 ->.
Qed.

Lemma free_subst :
  (forall AT n s, free_A n s -> free_AT n (subst_AT n s AT)) /\
  (forall D n s, free_A n s -> free_DT n (subst_DT n s D)) /\
  (forall st n s, free_A n s -> free_ST n (subst_ST n s st)) /\
  (forall S n s, free_A n s -> free_S n (subst_S n s S)) /\
  (forall K n s, free_A n s -> free_K n (subst_K n s K)) /\
  (forall B n s, free_A n s -> free_B n (subst_B n s B)) /\
  (forall O n s, free_A n s -> free_O n (subst_O n s O)).
Proof.
Ltac l27 := let IH1 := fresh "IH" in
            let IH2 := fresh "IH" in
            by move=>? IH1 ? IH2 ???; rewrite IH1 ?IH2.
apply All_syn_mutind=>//=; try l27.
- apply: free_A_subst.
- by move=>a1 a2 n s P; rewrite !free_A_subst.
- move=>st IH1 m S IH2 n s P; case: eqP.
    by move=>->/=; rewrite eqxx IH1.
    by rewrite /= IH1// IH2// orbT.
- apply: free_A_subst.
- move=>st IH1 m S IH2 n s P; case: eqP.
    by move=>->/=; rewrite eqxx IH1.
    by rewrite /= IH1// IH2// orbT.
- apply: free_A_subst.
- move=>st IH1 m S IH2 n s P; case: eqP.
    by move=>->/=; rewrite eqxx IH1.
    by rewrite /= IH1// IH2// orbT.
- move=>st IH1 m S IH2 n s P; case: eqP.
    by move=>->/=; rewrite eqxx IH1.
    by rewrite /= IH1// IH2// orbT.
Qed.

Lemma free_AT_subst AT n s : free_A n s -> free_AT n (AT.[n := s])%AT.
Proof. by move: free_subst AT n s=>[]. Qed.
Lemma free_DT_subst D n s : free_A n s -> free_DT n (D.[n := s])%DT.
Proof. by move: free_subst D n s=>[] _ []. Qed.
Lemma free_ST_subst st n s : free_A n s -> free_ST n (st.[n := s])%ST.
Proof. by move: free_subst st n s=>[] _ [] _ []. Qed.
Lemma free_S_subst S n s : free_A n s -> free_S n (S.[n := s])%DS.
Proof. by move: free_subst S n s=>[] _ [] _ [] _ []. Qed.
Lemma free_K_subst K n s : free_A n s -> free_K n (K.[n := s])%DK.
Proof. by move: free_subst K n s=>[] _ [] _ [] _ [] _ []. Qed.
Lemma free_B_subst B n s : free_A n s -> free_B n (B.[n := s])%DB.
Proof. by move: free_subst B n s=>[] _ [] _ [] _ [] _ [] _ []. Qed.
Lemma free_O_subst O n s : free_A n s -> free_O n (O.[n := s])%DO.
Proof. by move: free_subst O n s=>[] _ [] _ [] _ [] _ [] _ []. Qed.

(* TODO move *)
Lemma A_sem_eq s ca1 ca2 (av1 : A_value ca1) (av2 : A_value ca2) :
  av1 =av av2 -> A_sem av1 s = A_sem av2 s.
Proof. lav ca1 ca2 av1 av2. Qed.

Lemma subst_A_free_type t n s A ca :
  atype_checker ca s = Some A -> free_A n s ->
  atype_checker (Gamma_A_update ca n A) t = atype_checker ca (t.[n := s])%DA.
Proof.
move=>P1 P2.
have ->: atype_checker (Gamma_A_update ca n A) t =
  atype_checker (Gamma_A_update (Gamma_A_update ca n A) n (Gamma_A_update ca n A n)) t.
  by rewrite Gamma_A_update_ident.
by rewrite -(subst_A_type (n := n) (s := s)) !Gamma_A_update_id 
  Gamma_A_update_idm free_A_type// free_A_subst.
Qed.

Lemma subst_A_free t n s A ca (av : A_value ca) :
  atype_checker ca s = Some A -> free_A n s ->
  A_sem (A_value_update av n (A_sem av s A)) t = A_sem av (t.[n := s])%DA.
Proof.
move=>P1 P2.
have ->: A_sem (A_value_update av n (A_sem av s A)) t =
  A_sem (A_value_update (A_value_update av n (@witness (eval_AType A))) n 
  (A_sem (A_value_update av n (@witness (eval_AType A))) s (Gamma_A_update ca n A n))) t.
  rewrite [in X in _ = A_sem X _]free_A_sem// Gamma_A_update_id.
  by symmetry; apply/A_sem_eq/A_value_update_idm.
by rewrite subst_A_sem ?free_A_type// ?free_A_sem// ?Gamma_A_update_id// free_A_subst.
Qed.

Lemma subst_S_free_type S n s A ca :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_S m S) -> free_A m s) ->
  stype_checker (Gamma_A_update ca n A) S = stype_checker ca (S.[n := s])%DS.
Proof.
move=>P1 P2 P3.
have ->: stype_checker (Gamma_A_update ca n A) S =
  stype_checker (Gamma_A_update (Gamma_A_update ca n A) n (Gamma_A_update ca n A n)) S.
  by rewrite Gamma_A_update_ident.
by rewrite -(subst_S_type (n := n) (s := s))// !Gamma_A_update_id 
  Gamma_A_update_idm ?free_A_type// free_S_type// free_S_subst.
Qed.

Lemma subst_S_free S n s A ca (av : A_value ca) :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_S m S) -> free_A m s) ->
  S_sem (A_value_update av n (A_sem av s A)) S = S_sem av (S.[n := s])%DS.
Proof.
move=>P1 P2 P3.
have ->: S_sem (A_value_update av n (A_sem av s A)) S =
  S_sem (A_value_update (A_value_update av n (@witness (eval_AType A))) n 
  (A_sem (A_value_update av n (@witness (eval_AType A))) s (Gamma_A_update ca n A n))) S.
  rewrite free_A_sem// Gamma_A_update_id.
  by symmetry; apply/S_sem_eq/A_value_update_idm.
by rewrite subst_S_sem// ?free_A_type// ?free_A_sem// 
  ?Gamma_A_update_id// free_S_sem// free_S_subst.
Qed.

Lemma subst_K_free_type K n s A ca :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_K m K) -> free_A m s) ->
  ktype_checker (Gamma_A_update ca n A) K = ktype_checker ca (K.[n := s])%DK.
Proof.
move=>P1 P2 P3.
have ->: ktype_checker (Gamma_A_update ca n A) K =
  ktype_checker (Gamma_A_update (Gamma_A_update ca n A) n (Gamma_A_update ca n A n)) K.
  by rewrite Gamma_A_update_ident.
by rewrite -(subst_K_type (n := n) (s := s))// !Gamma_A_update_id 
  Gamma_A_update_idm ?free_A_type// free_K_type// free_K_subst.
Qed.

Lemma subst_K_free K n s A ca (av : A_value ca) :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_K m K) -> free_A m s) ->
  K_sem (A_value_update av n (A_sem av s A)) K = K_sem av (K.[n := s])%DK.
Proof.
move=>P1 P2 P3.
have ->: K_sem (A_value_update av n (A_sem av s A)) K =
  K_sem (A_value_update (A_value_update av n (@witness (eval_AType A))) n 
  (A_sem (A_value_update av n (@witness (eval_AType A))) s (Gamma_A_update ca n A n))) K.
  rewrite free_A_sem// Gamma_A_update_id.
  by symmetry; apply/K_sem_eq/A_value_update_idm.
by rewrite subst_K_sem// ?free_A_type// ?free_A_sem// 
  ?Gamma_A_update_id// free_K_sem// free_K_subst.
Qed.

Lemma subst_B_free_type B n s A ca :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_B m B) -> free_A m s) ->
  btype_checker (Gamma_A_update ca n A) B = btype_checker ca (B.[n := s])%DB.
Proof.
move=>P1 P2 P3.
have ->: btype_checker (Gamma_A_update ca n A) B =
  btype_checker (Gamma_A_update (Gamma_A_update ca n A) n (Gamma_A_update ca n A n)) B.
  by rewrite Gamma_A_update_ident.
by rewrite -(subst_B_type (n := n) (s := s))// !Gamma_A_update_id 
  Gamma_A_update_idm ?free_A_type// free_B_type// free_B_subst.
Qed.

Lemma subst_B_free B n s A ca (av : A_value ca) :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_B m B) -> free_A m s) ->
  B_sem (A_value_update av n (A_sem av s A)) B = B_sem av (B.[n := s])%DB.
Proof.
move=>P1 P2 P3.
have ->: B_sem (A_value_update av n (A_sem av s A)) B =
  B_sem (A_value_update (A_value_update av n (@witness (eval_AType A))) n 
  (A_sem (A_value_update av n (@witness (eval_AType A))) s (Gamma_A_update ca n A n))) B.
  rewrite free_A_sem// Gamma_A_update_id.
  by symmetry; apply/B_sem_eq/A_value_update_idm.
by rewrite subst_B_sem// ?free_A_type// ?free_A_sem// 
  ?Gamma_A_update_id// free_B_sem// free_B_subst.
Qed.

Lemma subst_O_free_type O n s A ca :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_O m O) -> free_A m s) ->
  otype_checker (Gamma_A_update ca n A) O = otype_checker ca (O.[n := s])%DO.
Proof.
move=>P1 P2 P3.
have ->: otype_checker (Gamma_A_update ca n A) O =
  otype_checker (Gamma_A_update (Gamma_A_update ca n A) n (Gamma_A_update ca n A n)) O.
  by rewrite Gamma_A_update_ident.
by rewrite -(subst_O_type (n := n) (s := s))// !Gamma_A_update_id 
  Gamma_A_update_idm ?free_A_type// free_O_type// free_O_subst.
Qed.

Lemma subst_O_free O n s A ca (av : A_value ca) :
  atype_checker ca s = Some A -> free_A n s ->
    (forall m, ~~ (bound_O m O) -> free_A m s) ->
  O_sem (A_value_update av n (A_sem av s A)) O = O_sem av (O.[n := s])%DO.
Proof.
move=>P1 P2 P3.
have ->: O_sem (A_value_update av n (A_sem av s A)) O =
  O_sem (A_value_update (A_value_update av n (@witness (eval_AType A))) n 
  (A_sem (A_value_update av n (@witness (eval_AType A))) s (Gamma_A_update ca n A n))) O.
  rewrite free_A_sem// Gamma_A_update_id.
  by symmetry; apply/O_sem_eq/A_value_update_idm.
by rewrite subst_O_sem// ?free_A_type// ?free_A_sem// 
  ?Gamma_A_update_id// free_O_sem// free_O_subst.
Qed.

Notation "\sum_ ( i ∈ st ) S" := (S_sum st%ST i S%DS)
  (at level 41, S at level 41, i, st at level 50,
         format "'[' \sum_ ( i  ∈  st ) '/  '  S ']'") : scalar_scope.
Notation "\sum_ ( i ∈ st ) K" := (K_sum st%ST i K%DK)
  (at level 41, K at level 41, i, st at level 50,
         format "'[' \sum_ ( i  ∈  st ) '/  '  K ']'") : ket_scope.
Notation "\sum_ ( i ∈ st ) B" := (B_sum st%ST i B%DB)
  (at level 41, B at level 41, i, st at level 50,
         format "'[' \sum_ ( i  ∈  st ) '/  '  B ']'") : bra_scope.
Notation "\sum_ ( i ∈ st ) O" := (O_sum st%ST i O%DO)
  (at level 41, O at level 41, i, st at level 50,
         format "'[' \sum_ ( i  ∈  st ) '/  '  O ']'") : opt_scope.

(* SUM-CONST *)
Lemma R_SUM_CONST_1 n M ca (av : A_value ca) :
  \sum_(n ∈ M) 0 =s 0 >> av.
Proof. by simplify; case: (sttype_checker _ _)=>// A; rewrite sumr_const mul0rn. Qed.
Lemma R_SUM_CONST_2 n M A ca (av : A_value ca) :
  free_AT n A -> 
    \sum_(n ∈ M) 0_(A) =k 0_(A) >> av.
Proof.
move=>P1; simplify.
case: (sttype_checker _ _)=>[A1|//].
rewrite free_AT_sem//; simplify2.
by rewrite sumr_const mul0rn V_set0.
Qed.
Lemma R_SUM_CONST_3 n M A ca (av : A_value ca) :
  free_AT n A -> 
    \sum_(n ∈ M) 0_(A) =b 0_(A) >> av.
Proof.
move=>P1; simplify.
case: (sttype_checker _ _)=>[A1|//].
rewrite free_AT_sem//; simplify2.
by rewrite sumr_const mul0rn V_set0.
Qed.
Lemma R_SUM_CONST_4 n M A1 A2 ca (av : A_value ca) :
  free_AT n A1 -> free_AT n A2 -> 
    \sum_(n ∈ M) 0_(A1,A2) =o 0_(A1,A2) >> av.
Proof.
move=>P1 P2; simplify.
case: (sttype_checker _ _)=>[A3|//].
rewrite !free_AT_sem//; simplify2.
by rewrite sumr_const mul0rn O_set0.
Qed.

Lemma R_SUM_CONST_5 (i : aname) A ca (av : A_value ca) :
  1_(A) =o \sum_(i ∈ U(A)) ('| `i > ·· '< `i |)%DO >> av.
Proof.
simplify; simplify2.
rewrite {1 2}Gamma_A_update_id; split=>//.
under eq_bigr do rewrite !V_set_id O_set_id A_value_update_id/= t2tv_conj.
rewrite /ST_sem1 Gamma_A_update_id.
under eq_bigr do rewrite A_set_id.
by rewrite -big_setT sumonb_out.
Qed.

(* SUM-ELIM *)
Lemma R_SUM_ELIM_1 i A s ca (av : A_value ca) :
  free_A i s ->
  \sum_(i ∈ U(A)) δ(`i,s) =s 1 >> av.
Proof.
move=>P; simplify; simplify2.
rewrite free_A_type//; simplify; split=>//.
under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
  (free_A_sem av _ P) A_set_id.
rewrite -big_setT (bigD1 (A_sem av s A0))//= eqxx big1 ?addr0//.
by move=>j /negPf->.
Qed.

Lemma R_SUM_ELIM_2 i A s S ca (av : A_value ca) :
  free_A i s ->
  (forall m : aname, ~~ bound_S m S -> free_A m s) ->
    \sum_(i ∈ U(A)) (δ(`i,s) * S) =s S.[i := s] >> av.
Proof.
move=>P P0.
simplify; simplify2; contra1.
  rewrite !free_A_type//; simplify; split=>//; rewrite -big_setT.
  under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
    (free_A_sem av _ P) A_set_id.
  rewrite (bigD1 (A_sem av s A0))//= eqxx big1 ?addr0.
  by move=>j /negPf->; rewrite mul0r.
  by rewrite mul1r subst_S_free// E1 -E3 Gamma_A_update_id.
rewrite !free_A_type//; simplify; exfalso.
move: E3; rewrite Gamma_A_update_id=>P1.
case: A1 / P1 E1 H=>E1 _.
move: E2; rewrite -(subst_S_type (n:=i) (s:=s) _ P0).
by rewrite free_A_type// E1 Gamma_A_update_id.
by rewrite free_S_type ?E// free_S_subst.
Qed.

Lemma R_SUM_ELIM_3 i A s K ca (av : A_value ca) :
  free_A i s ->
  (forall m : aname, ~~ bound_K m K -> free_A m s) ->
    \sum_(i ∈ U(A)) (δ(`i,s) *: K) =k K.[i := s] >> av.
Proof.
move=>P P0.
simplify; simplify2; contra1.
- rewrite !free_A_type//; simplify.
  move: E3; rewrite {1}Gamma_A_update_id=>E3; case: A2 / E3 E1 H=>E1 _.
  have Pv: Some (DKet A3) = Some (DKet A0).
    by rewrite -E2 (subst_K_free_type E1).
  move: E2; inversion Pv=>E2; split=>//.
  rewrite -big_setT.
  under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
    (free_A_sem av _ P) A_set_id.
  rewrite (bigD1 (A_sem av s A1))//= eqxx big1 ?addr0.
  by move=>j /negPf->; rewrite scale0r V_set0.
  by rewrite scale1r subst_K_free// V_set_id K_set_sem.
rewrite !free_A_type//; simplify; exfalso.
move: E3; rewrite Gamma_A_update_id=>P1.
case: A1 / P1 E1 H=>E1 _.
move: E2; rewrite -(subst_K_type (n:=i) (s:=s) _ P0).
by rewrite free_A_type// E1 Gamma_A_update_id.
by rewrite free_K_type ?E// free_K_subst.
Qed.

Lemma R_SUM_ELIM_4 i A s B ca (av : A_value ca) :
  free_A i s ->
  (forall m : aname, ~~ bound_B m B -> free_A m s) ->
    \sum_(i ∈ U(A)) (δ(`i,s) *: B) =b B.[i := s] >> av.
Proof.
move=>P P0.
simplify; simplify2; contra1.
- rewrite !free_A_type//; simplify.
  move: E3; rewrite {1}Gamma_A_update_id=>E3; case: A2 / E3 E1 H=>E1 _.
  have Pv: Some (DBra A3) = Some (DBra A0).
    by rewrite -E2 (subst_B_free_type E1).
  move: E2; inversion Pv=>E2; split=>//.
  rewrite -big_setT.
  under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
    (free_A_sem av _ P) A_set_id.
  rewrite (bigD1 (A_sem av s A1))//= eqxx big1 ?addr0.
  by move=>j /negPf->; rewrite scale0r V_set0.
  by rewrite scale1r subst_B_free// V_set_id B_set_sem.
rewrite !free_A_type//; simplify; exfalso.
move: E3; rewrite Gamma_A_update_id=>P1.
case: A1 / P1 E1 H=>E1 _.
move: E2; rewrite -(subst_B_type (n:=i) (s:=s) _ P0).
by rewrite free_A_type// E1 Gamma_A_update_id.
by rewrite free_B_type ?E// free_B_subst.
Qed.

Lemma R_SUM_ELIM_5 i A s O ca (av : A_value ca) :
  free_A i s ->
  (forall m : aname, ~~ bound_O m O -> free_A m s) ->
    \sum_(i ∈ U(A)) (δ(`i,s) *: O) =o O.[i := s] >> av.
Proof.
move=>P P0.
simplify; simplify2; contra1.
- rewrite !free_A_type//; simplify.
  move: E3; rewrite {1}Gamma_A_update_id=>E3; case: A3 / E3 E1 H=>E1 _.
  have Pv: Some (DOpt (A4, A5)) = Some (DOpt (A0, A1)).
    by rewrite -E2 (subst_O_free_type E1).
  move: E2; inversion Pv=>E2; split=>//.
  rewrite -big_setT.
  under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
    (free_A_sem av _ P) A_set_id.
  rewrite (bigD1 (A_sem av s A2))//= eqxx big1 ?addr0.
  by move=>j /negPf->; rewrite scale0r O_set0.
  by rewrite scale1r subst_O_free// O_set_id O_set_sem.
rewrite !free_A_type//; simplify; exfalso.
move: E3; rewrite Gamma_A_update_id=>P1.
case: A1 / P1 E1 H=>E1 _.
move: E2; rewrite -(subst_O_type (n:=i) (s:=s) _ P0).
by rewrite free_A_type// E1 Gamma_A_update_id.
by rewrite free_O_type ?E// free_O_subst.
Qed.

Lemma R_SUM_ELIM_6 i A s S K ca (av : A_value ca) :
  free_A i s ->
  (forall m : aname, ~~ bound_S m S -> free_A m s) ->
  (forall m : aname, ~~ bound_K m K -> free_A m s) ->
    \sum_(i ∈ U(A)) ((δ(`i,s) * S) *: K) =k S.[i := s] *: K.[i := s] >> av.
Proof.
move=>P P0 P1.
simplify; simplify2; contra1.
- rewrite !free_A_type//; simplify.
  move: E5; rewrite {1}Gamma_A_update_id=>E5; case: A2 / E5 E1 E2 H=>E1 E2 _.
  have Pv: Some (DKet A3) = Some (DKet A0).
    by rewrite -E4 (subst_K_free_type E2).
  move: E4; inversion Pv=>E4; split=>//.
  rewrite -big_setT.
  under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
    (free_A_sem av _ P) A_set_id.
  rewrite (bigD1 (A_sem av s A1))//= eqxx big1 ?addr0.
  by move=>j /negPf->; rewrite mul0r scale0r V_set0.
  by rewrite mul1r subst_K_free// V_set_id subst_S_free.
- rewrite !free_A_type//; simplify; exfalso.
  move: E5; rewrite Gamma_A_update_id=>P2.
  case: A1 / P2 E2 H=>E2 _.
  move: E4; rewrite -(subst_K_type (n:=i) (s:=s) _ P1).
  by rewrite free_A_type// E2 Gamma_A_update_id.
  by rewrite free_K_type ?E0// free_K_subst.
- rewrite !free_A_type//; simplify; exfalso.
  move: E4; rewrite Gamma_A_update_id=>P2.
  case: A1 / P2 E1 H=>E1 _.
  move: E2; rewrite -(subst_S_type (n:=i) (s:=s) _ P0).
  by rewrite free_A_type// E1 Gamma_A_update_id.
  by rewrite free_S_type ?E// free_S_subst.
Qed.

Lemma R_SUM_ELIM_7 i A s S B ca (av : A_value ca) :
  free_A i s ->
  (forall m : aname, ~~ bound_S m S -> free_A m s) ->
  (forall m : aname, ~~ bound_B m B -> free_A m s) ->
    \sum_(i ∈ U(A)) ((δ(`i,s) * S) *: B) =b S.[i := s] *: B.[i := s] >> av.
Proof.
move=>P P0 P1.
simplify; simplify2; contra1.
- rewrite !free_A_type//; simplify.
  move: E5; rewrite {1}Gamma_A_update_id=>E5; case: A2 / E5 E1 E2 H=>E1 E2 _.
  have Pv: Some (DBra A3) = Some (DBra A0).
    by rewrite -E4 (subst_B_free_type E2).
  move: E4; inversion Pv=>E4; split=>//.
  rewrite -big_setT.
  under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
    (free_A_sem av _ P) A_set_id.
  rewrite (bigD1 (A_sem av s A1))//= eqxx big1 ?addr0.
  by move=>j /negPf->; rewrite mul0r scale0r V_set0.
  by rewrite mul1r subst_B_free// V_set_id subst_S_free.
- rewrite !free_A_type//; simplify; exfalso.
  move: E5; rewrite Gamma_A_update_id=>P2.
  case: A1 / P2 E2 H=>E2 _.
  move: E4; rewrite -(subst_B_type (n:=i) (s:=s) _ P1).
  by rewrite free_A_type// E2 Gamma_A_update_id.
  by rewrite free_B_type ?E0// free_B_subst.
- rewrite !free_A_type//; simplify; exfalso.
  move: E4; rewrite Gamma_A_update_id=>P2.
  case: A1 / P2 E1 H=>E1 _.
  move: E2; rewrite -(subst_S_type (n:=i) (s:=s) _ P0).
  by rewrite free_A_type// E1 Gamma_A_update_id.
  by rewrite free_S_type ?E// free_S_subst.
Qed.

Lemma R_SUM_ELIM_8 i A s S O ca (av : A_value ca) :
  free_A i s ->
  (forall m : aname, ~~ bound_S m S -> free_A m s) ->
  (forall m : aname, ~~ bound_O m O -> free_A m s) ->
    \sum_(i ∈ U(A)) ((δ(`i,s) * S) *: O) =o S.[i := s] *: O.[i := s] >> av.
Proof.
move=>P P0 P1.
simplify; simplify2; contra1.
- rewrite !free_A_type//; simplify.
  move: E5; rewrite {1}Gamma_A_update_id=>E5; case: A3 / E5 E1 E2 H=>E1 E2 _.
  have Pv: Some (DOpt (A4, A5)) = Some (DOpt (A0, A1)).
    by rewrite -E4 (subst_O_free_type E2).
  move: E4; inversion Pv=>E4; split=>//.
  rewrite -big_setT.
  under eq_bigr do rewrite A_value_update_id Gamma_A_update_id 
    (free_A_sem av _ P) A_set_id.
  rewrite (bigD1 (A_sem av s A2))//= eqxx big1 ?addr0.
  by move=>j /negPf->; rewrite mul0r scale0r O_set0.
  by rewrite mul1r subst_O_free// O_set_id subst_S_free.
- rewrite !free_A_type//; simplify; exfalso.
  move: E5; rewrite Gamma_A_update_id=>P2.
  case: A1 / P2 E2 H=>E2 _.
  move: E4; rewrite -(subst_O_type (n:=i) (s:=s) _ P1).
  by rewrite free_A_type// E2 Gamma_A_update_id.
  by rewrite free_O_type ?E0// free_O_subst.
- rewrite !free_A_type//; simplify; exfalso.
  move: E4; rewrite Gamma_A_update_id=>P2.
  case: A1 / P2 E1 H=>E1 _.
  move: E2; rewrite -(subst_S_type (n:=i) (s:=s) _ P0).
  by rewrite free_A_type// E1 Gamma_A_update_id.
  by rewrite free_S_type ?E// free_S_subst.
Qed.

Lemma R_SUM_ELIM_9 i j M ca (av : A_value ca) :
  i != j -> free_ST i M ->
  \sum_(i ∈ M)\sum_(j ∈ M) δ(`i,`j) =s \sum_(j ∈ M) 1 >> av.
Proof.
move=>/eqP P1 P2.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite free_ST_type// E {1 2 3}Gamma_A_update_id {1 2 3}Gamma_A_updateC// {1 2 3}Gamma_A_update_id eqxx.
split=>//.
under eq_bigr do rewrite (free_ST_sem _ _ P2).
rewrite exchange_big; apply eq_bigr=>k Pk /=.
rewrite (bigD1 k)//= big1.
move=>l /andP[] _ /negPf Pl.
all: rewrite {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: by rewrite !A_value_update_id !A_set_id ?Pl// eqxx addr0.
Qed.

Lemma R_SUM_ELIM_10 i j M S ca (av : A_value ca) :
  i != j -> free_ST i M -> bound_S j S ->
    \sum_(i ∈ M)\sum_(j ∈ M) (δ(`i, `j) * S) =s 
      \sum_(j ∈ M) S.[i := `j] >> av.
Proof.
move=>/eqP P P0 Pj.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite !free_ST_type// E {-5}Gamma_A_update_id.
rewrite {1 3 5 7}Gamma_A_updateC// Gamma_A_update_id eqxx /=.
rewrite -(subst_S_free_type (A := A)).
by rewrite /= Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite (@Gamma_A_updateC ca j i); auto.
simplify; split=>//.
rewrite free_ST_sem// exchange_big/=; apply eq_bigr=>k Pk.
rewrite (bigD1 k)//= big1.
move=>l /andP[] _ /negPf Pl.
all: rewrite {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: rewrite !A_value_update_id !A_set_id ?Pl ?mul0r// eqxx addr0 mul1r .
rewrite -(subst_S_free (A := A))/=.
by rewrite Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite A_value_update_id A_set_id.
by rewrite (S_sem_eq S (A_value_updateC av k k P)).
Qed.

Lemma R_SUM_ELIM_11 i j M K ca (av : A_value ca) :
  i != j -> free_ST i M -> bound_K j K ->
    \sum_(i ∈ M)\sum_(j ∈ M) (δ(`i, `j) *: K) =k 
      \sum_(j ∈ M) K.[i := `j] >> av.
Proof.
move=>/eqP P P0 Pj.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite !free_ST_type// E {-7}Gamma_A_update_id.
rewrite {1 3 5 7 9 11}Gamma_A_updateC// Gamma_A_update_id eqxx /=.
rewrite -(subst_K_free_type (A := A)).
by rewrite /= Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite (@Gamma_A_updateC ca j i); auto.
simplify; split=>//.
rewrite free_ST_sem//. under eq_bigr do rewrite V_set_id.
rewrite exchange_big/=; f_equal; apply eq_bigr=>k Pk.
rewrite (bigD1 k)//= big1.
move=>l /andP[] _ /negPf Pl.
all: rewrite V_set_id {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: rewrite !A_value_update_id !A_set_id ?Pl ?scale0r// eqxx addr0 scale1r.
rewrite -(subst_K_free (A := A))/=.
by rewrite Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite A_value_update_id A_set_id.
by rewrite (K_sem_eq K (A_value_updateC av k k P)).
Qed.

Lemma R_SUM_ELIM_12 i j M B ca (av : A_value ca) :
  i != j -> free_ST i M -> bound_B j B ->
    \sum_(i ∈ M)\sum_(j ∈ M) (δ(`i, `j) *: B) =b 
      \sum_(j ∈ M) B.[i := `j] >> av.
Proof.
move=>/eqP P P0 Pj.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite !free_ST_type// E {-7}Gamma_A_update_id.
rewrite {1 3 5 7 9 11}Gamma_A_updateC// Gamma_A_update_id eqxx /=.
rewrite -(subst_B_free_type (A := A)).
by rewrite /= Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite (@Gamma_A_updateC ca j i); auto.
simplify; split=>//.
rewrite free_ST_sem//. under eq_bigr do rewrite V_set_id.
rewrite exchange_big/=; f_equal; apply eq_bigr=>k Pk.
rewrite (bigD1 k)//= big1.
move=>l /andP[] _ /negPf Pl.
all: rewrite V_set_id {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: rewrite !A_value_update_id !A_set_id ?Pl ?scale0r// eqxx addr0 scale1r.
rewrite -(subst_B_free (A := A))/=.
by rewrite Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite A_value_update_id A_set_id.
by rewrite (B_sem_eq B (A_value_updateC av k k P)).
Qed.

Lemma R_SUM_ELIM_13 i j M O ca (av : A_value ca) :
  i != j -> free_ST i M -> bound_O j O ->
    \sum_(i ∈ M)\sum_(j ∈ M) (δ(`i, `j) *: O) =o 
      \sum_(j ∈ M) O.[i := `j] >> av.
Proof.
move=>/eqP P P0 Pj.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite !free_ST_type// E {-7}Gamma_A_update_id.
rewrite {1 3 5 7 9 11}Gamma_A_updateC// Gamma_A_update_id eqxx /=.
rewrite -(subst_O_free_type (A := A)).
by rewrite /= Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite (@Gamma_A_updateC ca j i); auto.
simplify; split=>//.
rewrite free_ST_sem//. under eq_bigr do rewrite O_set_id.
rewrite exchange_big/=; f_equal; apply eq_bigr=>k Pk.
rewrite (bigD1 k)//= big1.
move=>l /andP[] _ /negPf Pl.
all: rewrite O_set_id {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: rewrite !A_value_update_id !A_set_id ?Pl ?scale0r// eqxx addr0 scale1r.
rewrite -(subst_O_free (A := A))/=.
by rewrite Gamma_A_update_id.
by apply/eqP.
by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 Pj.
rewrite A_value_update_id A_set_id.
by rewrite (O_sem_eq O (A_value_updateC av k k P)).
Qed.

Lemma R_SUM_ELIM_14 i j M S K ca (av : A_value ca) :
  i != j -> free_ST i M -> bound_S j S -> bound_K j K ->
    \sum_(i ∈ M)\sum_(j ∈ M) ((δ(`i, `j) * S) *: K) =k 
      \sum_(j ∈ M) S.[i := `j] *: K.[i := `j] >> av.
Proof.
move=>/eqP P P0 PS PK.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite !free_ST_type// E {-8}Gamma_A_update_id.
rewrite {1 2 3 4 5 6 7}[in Gamma_A_update _ j A i]Gamma_A_updateC//.
rewrite Gamma_A_update_id eqxx /=.
rewrite -(subst_K_free_type (A := A)) -?(subst_S_free_type (A := A)).
  1,4: by rewrite /= Gamma_A_update_id.
  1,3: by apply/eqP.
  1,2: by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 ?PK ?PS.
rewrite (@Gamma_A_updateC ca j i); auto.
simplify; split=>//.
rewrite free_ST_sem//. under eq_bigr do rewrite V_set_id.
rewrite exchange_big/=; f_equal; apply eq_bigr=>k Pk.
rewrite (bigD1 k)//= big1=>[l /andP[] _ /negPf Pl|].
all: rewrite !V_set_id {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: rewrite !A_value_update_id !A_set_id ?Pl ?mul0r ?scale0r// eqxx addr0 mul1r.
rewrite -(subst_K_free (A := A))/= -?(subst_S_free (A := A))/=.
  1,4: by rewrite /= Gamma_A_update_id.
  1,3: by apply/eqP.
  1,2: by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 ?PK ?PS.
rewrite A_value_update_id A_set_id.
by rewrite (S_sem_eq S (A_value_updateC av k k P)) (K_sem_eq K (A_value_updateC av k k P)).
Qed.

Lemma R_SUM_ELIM_15 i j M S B ca (av : A_value ca) :
  i != j -> free_ST i M -> bound_S j S -> bound_B j B ->
    \sum_(i ∈ M)\sum_(j ∈ M) ((δ(`i, `j) * S) *: B) =b 
      \sum_(j ∈ M) S.[i := `j] *: B.[i := `j] >> av.
Proof.
move=>/eqP P P0 PS PB.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite !free_ST_type// E {-8}Gamma_A_update_id.
rewrite {1 2 3 4 5 6 7}[in Gamma_A_update _ j A i]Gamma_A_updateC//.
rewrite Gamma_A_update_id eqxx /=.
rewrite -(subst_B_free_type (A := A)) -?(subst_S_free_type (A := A)).
  1,4: by rewrite /= Gamma_A_update_id.
  1,3: by apply/eqP.
  1,2: by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 ?PB ?PS.
rewrite (@Gamma_A_updateC ca j i); auto.
simplify; split=>//.
rewrite free_ST_sem//. under eq_bigr do rewrite V_set_id.
rewrite exchange_big/=; f_equal; apply eq_bigr=>k Pk.
rewrite (bigD1 k)//= big1=>[l /andP[] _ /negPf Pl|].
all: rewrite !V_set_id {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: rewrite !A_value_update_id !A_set_id ?Pl ?mul0r ?scale0r// eqxx addr0 mul1r.
rewrite -(subst_B_free (A := A))/= -?(subst_S_free (A := A))/=.
  1,4: by rewrite /= Gamma_A_update_id.
  1,3: by apply/eqP.
  1,2: by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 ?PB ?PS.
rewrite A_value_update_id A_set_id.
by rewrite (S_sem_eq S (A_value_updateC av k k P)) (B_sem_eq B (A_value_updateC av k k P)).
Qed.

Lemma R_SUM_ELIM_16 i j M S O ca (av : A_value ca) :
  i != j -> free_ST i M -> bound_S j S -> bound_O j O ->
    \sum_(i ∈ M)\sum_(j ∈ M) ((δ(`i, `j) * S) *: O) =o 
      \sum_(j ∈ M) S.[i := `j] *: O.[i := `j] >> av.
Proof.
move=>/eqP P P0 PS PO.
simplify; simplify2.
case E: (sttype_checker _ _)=>[A|//].
rewrite !free_ST_type// E {-8}Gamma_A_update_id.
rewrite {1 2 3 4 5 6 7}[in Gamma_A_update _ j A i]Gamma_A_updateC//.
rewrite Gamma_A_update_id eqxx /=.
rewrite -(subst_O_free_type (A := A)) -?(subst_S_free_type (A := A)).
  1,4: by rewrite /= Gamma_A_update_id.
  1,3: by apply/eqP.
  1,2: by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 ?PO ?PS.
rewrite (@Gamma_A_updateC ca j i); auto.
simplify; split=>//.
rewrite free_ST_sem//. under eq_bigr do rewrite O_set_id.
rewrite exchange_big/=; f_equal; apply eq_bigr=>k Pk.
rewrite (bigD1 k)//= big1=>[l /andP[] _ /negPf Pl|].
all: rewrite !O_set_id {1 3 5}Gamma_A_updateC// Gamma_A_update_id A_value_update_neq; auto.
all: rewrite !A_value_update_id !A_set_id ?Pl ?mul0r ?scale0r// eqxx addr0 mul1r.
rewrite -(subst_O_free (A := A))/= -?(subst_S_free (A := A))/=.
  1,4: by rewrite /= Gamma_A_update_id.
  1,3: by apply/eqP.
  1,2: by move=>m Pm /=; case: eqP=>// P1; move: Pm; rewrite P1 ?PO ?PS.
rewrite A_value_update_id A_set_id.
by rewrite (S_sem_eq S (A_value_updateC av k k P)) (O_sem_eq O (A_value_updateC av k k P)).
Qed.

Lemma R_SUM_PUSH_1 i M S X ca (av : A_value ca) :
  free_S i X -> (\sum_(i ∈ M) S) * X =s \sum_(i ∈ M) S * X >> av.
Proof.
move=>P.
simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A|//];
  rewrite (free_S_type _ _ P) E; simplify; split=>//.
by rewrite mulr_suml; apply eq_bigr=>j _; f_equal; rewrite free_S_sem.
Qed.

Lemma R_SUM_PUSH_2 i M S ca (av : A_value ca) :
  (\sum_(i ∈ M) S)^* =s \sum_(i ∈ M) S^* >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A|//].
simplify; split=>//; by rewrite rmorph_sum.
Qed.

Lemma R_SUM_PUSH_3 i M K ca (av : A_value ca) :
  (\sum_(i ∈ M) K)^A =k \sum_(i ∈ M) K^A >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A|//].
simplify; split=>//; rewrite linear_sum/=.
by under [in RHS]eq_bigr do rewrite V_set_id.
Qed.

Lemma R_SUM_PUSH_4 i M B ca (av : A_value ca) :
  (\sum_(i ∈ M) B)^A =b \sum_(i ∈ M) B^A >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A|//].
simplify; split=>//; rewrite linear_sum/=.
by under [in RHS]eq_bigr do rewrite V_set_id.
Qed.

Lemma R_SUM_PUSH_5 i M O ca (av : A_value ca) :
  (\sum_(i ∈ M) O)^A =o \sum_(i ∈ M) O^A >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A|//].
simplify; split=>//; rewrite linear_sum/=.
by under [in RHS]eq_bigr do rewrite O_set_id.
Qed.

Lemma R_SUM_PUSH_6 i M X K ca (av : A_value ca) :
  free_S i X -> X *: (\sum_(i ∈ M) K) =k \sum_(i ∈ M) X *: K >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A|//];
rewrite (free_S_type _ _ P) E; simplify; split=>//.
rewrite scaler_sumr.
by under [in RHS]eq_bigr do rewrite V_set_id (free_S_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_7 i M X B ca (av : A_value ca) :
  free_S i X -> X *: (\sum_(i ∈ M) B) =b \sum_(i ∈ M) X *: B >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A|//];
rewrite (free_S_type _ _ P) E; simplify; split=>//.
rewrite scaler_sumr.
by under [in RHS]eq_bigr do rewrite V_set_id (free_S_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_8 i M X O ca (av : A_value ca) :
  free_S i X -> X *: (\sum_(i ∈ M) O) =o \sum_(i ∈ M) X *: O >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A|//];
rewrite (free_S_type _ _ P) E; simplify; split=>//.
rewrite scaler_sumr.
by under [in RHS]eq_bigr do rewrite O_set_id (free_S_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_9 i M S X ca (av : A_value ca) :
  free_K i X -> (\sum_(i ∈ M) S) *: X =k \sum_(i ∈ M) S *: X >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_K_type _ _ P) E; simplify; split=>//.
rewrite scaler_suml.
by under [in RHS]eq_bigr do rewrite V_set_id (free_K_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_10 i M S X ca (av : A_value ca) :
  free_B i X -> (\sum_(i ∈ M) S) *: X =b \sum_(i ∈ M) S *: X >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_B_type _ _ P) E; simplify; split=>//.
rewrite scaler_suml.
by under [in RHS]eq_bigr do rewrite V_set_id (free_B_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_11 i M S X ca (av : A_value ca) :
  free_O i X -> (\sum_(i ∈ M) S) *: X =o \sum_(i ∈ M) S *: X >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_O_type _ _ P) E; simplify; split=>//.
rewrite scaler_suml.
by under [in RHS]eq_bigr do rewrite O_set_id (free_O_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_12 i M B K ca (av : A_value ca) :
  free_K i K -> (\sum_(i ∈ M) B) · K =s \sum_(i ∈ M) B · K >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_K_type _ _ P) E; simplify; split=>//.
rewrite linear_sum/= linear_suml/=.
by under [in RHS]eq_bigr do rewrite (free_K_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_13 i M O K ca (av : A_value ca) :
  free_K i K -> (\sum_(i ∈ M) O) · K =k \sum_(i ∈ M) O · K >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_K_type _ _ P) E; simplify; split=>//.
rewrite sum_lfunE.
by under [in RHS]eq_bigr do rewrite V_set_id (free_K_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_14 i M B O ca (av : A_value ca) :
  free_O i O -> (\sum_(i ∈ M) B) · O =b \sum_(i ∈ M) B · O >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_O_type _ _ P) E; simplify; split=>//.
rewrite linear_sum/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_O_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_15 i M O1 O2 ca (av : A_value ca) :
  free_O i O2 -> (\sum_(i ∈ M) O1) · O2 =b \sum_(i ∈ M) O1 · O2 >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_O_type _ _ P) E; simplify; split=>//.
rewrite linear_sum/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_O_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_16 i M B K ca (av : A_value ca) :
  free_B i B -> B · (\sum_(i ∈ M) K) =s \sum_(i ∈ M) B · K >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_B_type _ _ P) E; simplify; split=>//.
rewrite linear_sumr/=.
by under [in RHS]eq_bigr do rewrite (free_B_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_17 i M O K ca (av : A_value ca) :
  free_O i O -> O · (\sum_(i ∈ M) K) =k \sum_(i ∈ M) O · K >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_O_type _ _ P) E; simplify; split=>//.
rewrite linear_sum/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_O_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_18 i M B O ca (av : A_value ca) :
  free_B i B -> B · (\sum_(i ∈ M) O) =b \sum_(i ∈ M) B · O >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_B_type _ _ P) E; simplify; split=>//.
rewrite linear_sum/= sum_lfunE/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_B_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_19 i M O1 O2 ca (av : A_value ca) :
  free_O i O1 -> O1 · (\sum_(i ∈ M) O2) =o \sum_(i ∈ M) O1 · O2 >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_O_type _ _ P) E; simplify; split=>//.
rewrite linear_sumr/=.
by under [in RHS]eq_bigr do rewrite O_set_id (free_O_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_20 i M K1 K2 ca (av : A_value ca) :
  free_K i K2 -> (\sum_(i ∈ M) K1) ⊗ K2 =k \sum_(i ∈ M) (K1 ⊗ K2) >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_K_type _ _ P) E; simplify; split=>//.
rewrite linear_suml/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_K_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_21 i M B1 B2 ca (av : A_value ca) :
  free_B i B2 -> (\sum_(i ∈ M) B1) ⊗ B2 =b \sum_(i ∈ M) (B1 ⊗ B2) >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_B_type _ _ P) E; simplify; split=>//.
rewrite linear_suml/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_B_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_22 i M O1 O2 ca (av : A_value ca) :
  free_O i O2 -> (\sum_(i ∈ M) O1) ⊗ O2 =o \sum_(i ∈ M) (O1 ⊗ O2) >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_O_type _ _ P) E; simplify; split=>//.
rewrite linear_suml/=.
by under [in RHS]eq_bigr do rewrite O_set_id (free_O_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_23 i M K B ca (av : A_value ca) :
  free_B i B -> (\sum_(i ∈ M) K) ·· B =o \sum_(i ∈ M) (K ·· B) >> av.
Proof.
move=>P; simplify; contra1.
all: case E1: (sttype_checker _ _)=>[A1|//];
  rewrite (free_B_type _ _ P) E; simplify; split=>//.
rewrite linear_suml/=.
by under [in RHS]eq_bigr do rewrite O_set_id (free_B_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_24 i M K1 K2 ca (av : A_value ca) :
  free_K i K1 -> K1 ⊗ (\sum_(i ∈ M) K2) =k \sum_(i ∈ M) (K1 ⊗ K2) >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_K_type _ _ P) E; simplify; split=>//.
rewrite linear_sumr/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_K_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_25 i M B1 B2 ca (av : A_value ca) :
  free_B i B1 -> B1 ⊗ (\sum_(i ∈ M) B2) =b \sum_(i ∈ M) (B1 ⊗ B2) >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_B_type _ _ P) E; simplify; split=>//.
rewrite linear_sumr/=.
by under [in RHS]eq_bigr do rewrite V_set_id (free_B_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_26 i M O1 O2 ca (av : A_value ca) :
  free_O i O1 -> O1 ⊗ (\sum_(i ∈ M) O2) =o \sum_(i ∈ M) (O1 ⊗ O2) >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_O_type _ _ P) E; simplify; split=>//.
rewrite linear_sumr/=.
by under [in RHS]eq_bigr do rewrite O_set_id (free_O_sem _ _ P).
Qed.

Lemma R_SUM_PUSH_27 i M K B ca (av : A_value ca) :
  free_K i K -> K ·· (\sum_(i ∈ M) B) =o \sum_(i ∈ M) (K ·· B) >> av.
Proof.
move=>P; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite (free_K_type _ _ P) E; simplify; split=>//.
rewrite linear_sum linear_sumr/=.
by under [in RHS]eq_bigr do rewrite O_set_id (free_K_sem _ _ P).
Qed.

Lemma R_SUM_ADD_1 i M X Y ca (av : A_value ca) :
  \sum_(i ∈ M) (X + Y) =s \sum_(i ∈ M) X + \sum_(i ∈ M) Y >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
by simplify; split=>//; rewrite big_split.
Qed.

Lemma R_SUM_ADD_2 i M X Y ca (av : A_value ca) :
  \sum_(i ∈ M) (X + Y) =k \sum_(i ∈ M) X + \sum_(i ∈ M) Y >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite/= -big_split/=.
by under eq_bigr do rewrite V_set_id.
Qed.

Lemma R_SUM_ADD_3 i M X Y ca (av : A_value ca) :
  \sum_(i ∈ M) (X + Y) =b \sum_(i ∈ M) X + \sum_(i ∈ M) Y >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite/= -big_split/=.
by under eq_bigr do rewrite V_set_id.
Qed.

Lemma R_SUM_ADD_4 i M X Y ca (av : A_value ca) :
  \sum_(i ∈ M) (X + Y) =o \sum_(i ∈ M) X + \sum_(i ∈ M) Y >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite/= -big_split/=.
by under eq_bigr do rewrite O_set_id.
Qed.

Lemma R_SUM_ADD_5 i M S X ca (av : A_value ca) :
  \sum_(i ∈ M) S *: X + \sum_(i ∈ M) X =k
    \sum_(i ∈ M) ((S + 1) *: X) >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite -big_split/=; f_equal; apply eq_bigr=>j _.
by rewrite !V_set_id scalerDl scale1r.
Qed.

Lemma R_SUM_ADD_6 i M S X ca (av : A_value ca) :
  \sum_(i ∈ M) S *: X + \sum_(i ∈ M) X =b
    \sum_(i ∈ M) ((S + 1) *: X) >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite -big_split/=; f_equal; apply eq_bigr=>j _.
by rewrite !V_set_id scalerDl scale1r.
Qed.

Lemma R_SUM_ADD_7 i M S X ca (av : A_value ca) :
  \sum_(i ∈ M) S *: X + \sum_(i ∈ M) X =o
    \sum_(i ∈ M) ((S + 1) *: X) >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite -big_split/=; f_equal; apply eq_bigr=>j _.
by rewrite !O_set_id scalerDl scale1r.
Qed.

Lemma R_SUM_ADD_8 i M S T X ca (av : A_value ca) :
  \sum_(i ∈ M) S *: X + \sum_(i ∈ M) T *: X =k
    \sum_(i ∈ M) ((S + T) *: X) >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite -big_split/=; f_equal; apply eq_bigr=>j _.
by rewrite !V_set_id scalerDl.
Qed.

Lemma R_SUM_ADD_9 i M S T X ca (av : A_value ca) :
  \sum_(i ∈ M) S *: X + \sum_(i ∈ M) T *: X =b
    \sum_(i ∈ M) ((S + T) *: X) >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite -big_split/=; f_equal; apply eq_bigr=>j _.
by rewrite !V_set_id scalerDl.
Qed.

Lemma R_SUM_ADD_10 i M S T X ca (av : A_value ca) :
  \sum_(i ∈ M) S *: X + \sum_(i ∈ M) T *: X =o
    \sum_(i ∈ M) ((S + T) *: X) >> av.
Proof.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
simplify; split=>//; rewrite -big_split/=; f_equal; apply eq_bigr=>j _.
by rewrite !O_set_id scalerDl.
Qed.

Lemma free_A_subst_id i s X : 
  free_A i X -> (X.[i := s])%DA = X.
Proof.
elim: X=>//=.
by move=>? /negPf P; rewrite eq_sym P.
by move=>a1 IH1 a2 IH2 /andP[]/IH1->/IH2->.
by move=>a IH /IH->.
by move=>a IH /IH->.
Qed.

Lemma free_subst_id :
  (forall AT n s, free_AT n AT -> subst_AT n s AT = AT) /\
  (forall D n s, free_DT n D -> subst_DT n s D = D) /\
  (forall st n s, free_ST n st -> subst_ST n s st = st) /\
  (forall S n s, free_S n S -> subst_S n s S = S) /\
  (forall K n s, free_K n K -> subst_K n s K = K) /\
  (forall B n s, free_B n B -> subst_B n s B = B) /\
  (forall O n s, free_O n O -> subst_O n s O = O).
Proof.
Ltac l28 := let IH1 := fresh "IH" in
            let IH2 := fresh "IH" in
            by move=>? IH1 ? IH2 ? ? /andP[] /IH1-> /IH2->.
Ltac l18 := let IH := fresh "IH" in
            by move=>? IH ? ? /IH->.
apply All_syn_mutind=>//=; try l28; try l18.
1,4,6: by move=>a n s IH; rewrite free_A_subst_id.
- by move=>a1 a2 n s /andP[] IH1 IH2; rewrite !free_A_subst_id.
all: move=>st IH1 m S IH2 n s; rewrite eq_sym;
  by case: eqP=>[->|P /andP[] /IH1-> /IH2->//]; rewrite andbT=>/IH1->.
Qed.

Lemma free_AT_subst_id AT n s : free_AT n AT -> (AT.[n := s])%AT = AT.
Proof. by move: free_subst_id AT n s=>[]. Qed.
Lemma free_DT_subst_id D n s : free_DT n D -> (D.[n := s])%DT = D.
Proof. by move: free_subst_id D n s=>[] _ []. Qed.
Lemma free_ST_subst_id st n s : free_ST n st -> (st.[n := s])%ST = st.
Proof. by move: free_subst_id st n s=>[] _ [] _ []. Qed.
Lemma free_S_subst_id S n s : free_S n S -> (S.[n := s])%DS = S.
Proof. by move: free_subst_id S n s=>[] _ [] _ [] _ []. Qed.
Lemma free_K_subst_id K n s : free_K n K -> (K.[n := s])%DK = K.
Proof. by move: free_subst_id K n s=>[] _ [] _ [] _ [] _ []. Qed.
Lemma free_B_subst_id B n s : free_B n B -> (B.[n := s])%DB = B.
Proof. by move: free_subst_id B n s=>[] _ [] _ [] _ [] _ [] _ []. Qed.
Lemma free_O_subst_id O n s : free_O n O -> (O.[n := s])%DO = O.
Proof. by move: free_subst_id O n s=>[] _ [] _ [] _ [] _ [] _ []. Qed.

Lemma A_sem_pair j k A B (a : eval_AType A) (b : eval_AType B)  ca (av : A_value ca) :
  j <> k ->
  A_sem (A_value_update (A_value_update av j a) k b) (`j, `k)%DA
    = A_set ((a, b) : eval_AType (A * B)%TA).
Proof.
move=>Pjk; rewrite /A_sem {1}Gamma_A_updateC//.
case E2: (atype_checker _ _)=>[A3|].
case E3: (atype_checker _ _)=>[A4|].
  move: E2=>/=; rewrite Gamma_A_update_id=>E2; inversion E2; rewrite -H0.
  move: E3=>/=; rewrite {1}Gamma_A_update_id=>E3; inversion E3; rewrite -H1.
  by rewrite (A_set_eq j (A_value_updateC _ _ _ _))// !A_value_update_id !A_set_id.
by move: E3=>/=; rewrite Gamma_A_update_id.
by move: E2=>/=; rewrite Gamma_A_update_id.
Qed.

Lemma R_SUM_INDEX_1 i j k A B X ca (av : A_value ca) :
   j != k -> free_AT j B -> free_S j X -> free_S k X -> bound_S j X -> bound_S k X ->
  \sum_(i ∈ U(A * B)) X =s \sum_(j ∈ U(A)) \sum_(k ∈ U(B)) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_S_subst_id// !free_S_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; apply eq_bigr=>a _.
  rewrite -big_setT; apply eq_bigr=>b _.
  by rewrite !free_S_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_S_subst_id// !free_S_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; apply eq_bigr=>a _.
  rewrite -big_setT; apply eq_bigr=>b _.
  by rewrite !free_S_sem.  
simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
case E1: (stype_checker _ _)=>[[]|//]//; split.
  rewrite -(subst_S_free_type (A := (A0 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_S_type// Gamma_A_updateC; auto; rewrite free_S_type.
rewrite -!big_setT pair_bigV/=; apply eq_bigr=>a _.
rewrite -big_setT; apply eq_bigr=>b _.
rewrite -(subst_S_free (A := (A0 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (S_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [RHS]free_S_sem// (S_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [RHS]free_S_sem.
Qed.

Lemma R_SUM_INDEX_2 i j k A B X ca (av : A_value ca) :
   j != k -> free_AT j B -> free_K j X -> free_K k X -> bound_K j X -> bound_K k X ->
  \sum_(i ∈ U(A * B)) X =k \sum_(j ∈ U(A)) \sum_(k ∈ U(B)) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_K_subst_id// !free_K_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; f_equal; apply eq_bigr=>a _.
  rewrite -big_setT V_set_id; apply eq_bigr=>b _.
  by rewrite !free_K_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_K_subst_id// !free_K_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; f_equal; apply eq_bigr=>a _.
  rewrite -big_setT V_set_id; apply eq_bigr=>b _.
  by rewrite !free_K_sem.
simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
case E1: (ktype_checker _ _)=>[[|A3||]|//]//.
have P1: ktype_checker (Gamma_A_update (Gamma_A_update ca j A0) k A2) (subst_K i (`j, `k)%DA X) = Some (DKet A3).
  rewrite -(subst_K_free_type (A := (A0 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_K_type// Gamma_A_updateC; auto; rewrite free_K_type.
rewrite P1; split=>//; rewrite -!big_setT pair_bigV/=.
f_equal; apply eq_bigr=>a _.
rewrite V_set_id -big_setT; apply eq_bigr=>b _.
rewrite -(subst_K_free (A := (A0 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (K_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [in RHS]free_K_sem// (K_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [in RHS]free_K_sem.
Qed.

Lemma R_SUM_INDEX_3 i j k A B X ca (av : A_value ca) :
   j != k -> free_AT j B -> free_B j X -> free_B k X -> bound_B j X -> bound_B k X ->
  \sum_(i ∈ U(A * B)) X =b \sum_(j ∈ U(A)) \sum_(k ∈ U(B)) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_B_subst_id// !free_B_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; f_equal; apply eq_bigr=>a _.
  rewrite -big_setT V_set_id; apply eq_bigr=>b _.
  by rewrite !free_B_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_B_subst_id// !free_B_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; f_equal; apply eq_bigr=>a _.
  rewrite -big_setT V_set_id; apply eq_bigr=>b _.
  by rewrite !free_B_sem.
simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
case E1: (btype_checker _ _)=>[[||A3|]|//]//.
have P1: btype_checker (Gamma_A_update (Gamma_A_update ca j A0) k A2) (subst_B i (`j, `k)%DA X) = Some (DBra A3).
  rewrite -(subst_B_free_type (A := (A0 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_B_type// Gamma_A_updateC; auto; rewrite free_B_type.
rewrite P1; split=>//; rewrite -!big_setT pair_bigV/=.
f_equal; apply eq_bigr=>a _.
rewrite V_set_id -big_setT; apply eq_bigr=>b _.
rewrite -(subst_B_free (A := (A0 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (B_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [in RHS]free_B_sem// (B_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [in RHS]free_B_sem.
Qed.

Lemma R_SUM_INDEX_4 i j k A B X ca (av : A_value ca) :
   j != k -> free_AT j B -> free_O j X -> free_O k X -> bound_O j X -> bound_O k X ->
  \sum_(i ∈ U(A * B)) X =o \sum_(j ∈ U(A)) \sum_(k ∈ U(B)) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_O_subst_id// !free_O_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; f_equal; apply eq_bigr=>a _.
  rewrite -big_setT O_set_id; apply eq_bigr=>b _.
  by rewrite !free_O_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
  rewrite free_O_subst_id// !free_O_type//.
  simplify; split=>//; rewrite -!big_setT pair_bigV/=; f_equal; apply eq_bigr=>a _.
  rewrite -big_setT O_set_id; apply eq_bigr=>b _.
  by rewrite !free_O_sem.
simplify; simplify2;
  move: E1; rewrite free_AT_sem// E0// =>Pv; move: E0; inversion Pv=>E0.
case E1: (otype_checker _ _)=>[[|||A3]|//]//.
have P1: otype_checker (Gamma_A_update (Gamma_A_update ca j A0) k A2) (subst_O i (`j, `k)%DA X) = Some (DOpt A3).
  rewrite -(subst_O_free_type (A := (A0 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_O_type// Gamma_A_updateC; auto; rewrite free_O_type.
rewrite P1; split=>//; rewrite -!big_setT pair_bigV/=.
f_equal; apply eq_bigr=>a _.
rewrite O_set_id -big_setT; apply eq_bigr=>b _.
rewrite -(subst_O_free (A := (A0 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (O_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [in RHS]free_O_sem// (O_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [in RHS]free_O_sem.
Qed.

Lemma big_setX (R : Type) (idx : R) (op : Monoid.com_law idx)
  (A B : finType) (sA : {set A}) (sB : {set B}) (F : A * B -> R) :
  \big[op/idx]_(i in setX sA sB) F i =
     \big[op/idx]_(i in sA) \big[op/idx]_(j in sB) F (i, j).
Proof.
rewrite pair_big.
under [RHS]eq_bigr do rewrite -surjective_pairing.
apply eq_bigl=>[[i1 i2]]/=; exact: in_setX .
Qed.

Lemma R_SUM_INDEX_5 i j k M1 M2 X ca (av : A_value ca) :
   j != k -> free_ST j M2 -> free_S j X -> free_S k X -> bound_S j X -> bound_S k X ->
  \sum_(i ∈ M1 * M2) X =s \sum_(j ∈ M1) \sum_(k ∈ M2) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_S_subst_id// !free_S_type// =><-; split=>//.
  rewrite ST_set_id big_setX/=.
  apply eq_bigr=>a _; apply eq_bigr=>b _.
  by rewrite !free_S_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_S_subst_id// !free_S_type// =><-; split=>//.
  rewrite ST_set_id big_setX/=.
  apply eq_bigr=>a _; apply eq_bigr=>b _.
  by rewrite !free_S_sem.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
case E2: (sttype_checker _ _)=>[A2|//].
simplify; rewrite !free_ST_type// E2 !free_ST_sem//; split.
  rewrite -(subst_S_free_type (A := (A1 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_S_type// Gamma_A_updateC; auto; rewrite free_S_type.
rewrite ST_set_id big_setX/=; apply eq_bigr=>a _; apply eq_bigr=>b _.
rewrite -(subst_S_free (A := (A1 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (S_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [RHS]free_S_sem// (S_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [RHS]free_S_sem.
Qed.

Lemma R_SUM_INDEX_6 i j k M1 M2 X ca (av : A_value ca) :
   j != k -> free_ST j M2 -> free_K j X -> free_K k X -> bound_K j X -> bound_K k X ->
  \sum_(i ∈ M1 * M2) X =k \sum_(j ∈ M1) \sum_(k ∈ M2) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_K_subst_id// !free_K_type// =>->; split=>//.
  rewrite ST_set_id big_setX/=; f_equal.
  apply eq_bigr=>a _; rewrite V_set_id; apply eq_bigr=>b _.
  by rewrite !free_K_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_K_subst_id// !free_K_type// =>->; split=>//.
  rewrite ST_set_id big_setX/=; f_equal.
  apply eq_bigr=>a _; rewrite V_set_id; apply eq_bigr=>b _.
  by rewrite !free_K_sem.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
case E2: (sttype_checker _ _)=>[A2|//]; 
simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
have P1: ktype_checker (Gamma_A_update (Gamma_A_update ca j A1) k A2) (subst_K i (`j, `k)%DA X) = Some (DKet A).
  rewrite -(subst_K_free_type (A := (A1 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_K_type// Gamma_A_updateC; auto; rewrite free_K_type.
rewrite P1; split=>//; rewrite ST_set_id big_setX/=.
f_equal; apply eq_bigr=>a _; rewrite V_set_id; apply eq_bigr=>b _.
rewrite -(subst_K_free (A := (A1 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (K_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [in RHS]free_K_sem// (K_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [in RHS]free_K_sem.
Qed.

Lemma R_SUM_INDEX_7 i j k M1 M2 X ca (av : A_value ca) :
   j != k -> free_ST j M2 -> free_B j X -> free_B k X -> bound_B j X -> bound_B k X ->
  \sum_(i ∈ M1 * M2) X =b \sum_(j ∈ M1) \sum_(k ∈ M2) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_B_subst_id// !free_B_type// =>->; split=>//.
  rewrite ST_set_id big_setX/=; f_equal.
  apply eq_bigr=>a _; rewrite V_set_id; apply eq_bigr=>b _.
  by rewrite !free_B_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_B_subst_id// !free_B_type// =>->; split=>//.
  rewrite ST_set_id big_setX/=; f_equal.
  apply eq_bigr=>a _; rewrite V_set_id; apply eq_bigr=>b _.
  by rewrite !free_B_sem.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
case E2: (sttype_checker _ _)=>[A2|//]; 
simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
have P1: btype_checker (Gamma_A_update (Gamma_A_update ca j A1) k A2) (subst_B i (`j, `k)%DA X) = Some (DBra A).
  rewrite -(subst_B_free_type (A := (A1 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_B_type// Gamma_A_updateC; auto; rewrite free_B_type.
rewrite P1; split=>//; rewrite ST_set_id big_setX/=.
f_equal; apply eq_bigr=>a _; rewrite V_set_id; apply eq_bigr=>b _.
rewrite -(subst_B_free (A := (A1 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (B_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [in RHS]free_B_sem// (B_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [in RHS]free_B_sem.
Qed.

Lemma R_SUM_INDEX_8 i j k M1 M2 X ca (av : A_value ca) :
   j != k -> free_ST j M2 -> free_O j X -> free_O k X -> bound_O j X -> bound_O k X ->
  \sum_(i ∈ M1 * M2) X =o \sum_(j ∈ M1) \sum_(k ∈ M2) X.[i := (`j, `k)] >> av.
Proof.
move=>/eqP Pjk P2 P3 P4 P5 P6.
case: (@eqP _ i j)=>[->|Pij].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_O_subst_id// !free_O_type// =>->; split=>//.
  rewrite ST_set_id big_setX/=; f_equal.
  apply eq_bigr=>a _; rewrite O_set_id; apply eq_bigr=>b _.
  by rewrite !free_O_sem.
case: (@eqP _ i k)=>[->|Pik].
  simplify; case E1: (sttype_checker _ _)=>[A1|//].
  case E2: (sttype_checker _ _)=>[A2|//].
  simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
  move: E; rewrite free_O_subst_id// !free_O_type// =>->; split=>//.
  rewrite ST_set_id big_setX/=; f_equal.
  apply eq_bigr=>a _; rewrite O_set_id; apply eq_bigr=>b _.
  by rewrite !free_O_sem.
simplify; case E1: (sttype_checker _ _)=>[A1|//].
case E2: (sttype_checker _ _)=>[A2|//]; 
simplify; rewrite !free_ST_type// E2 !free_ST_sem//.
have P1: otype_checker (Gamma_A_update (Gamma_A_update ca j A1) k A2) (subst_O i (`j, `k)%DA X) = Some (DOpt (A,A0)).
  rewrite -(subst_O_free_type (A := (A1 * A2)%TA))//=.
    by rewrite Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
    by move: Pij Pik=>/eqP->/eqP->.
    by move=>m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
  by rewrite Gamma_A_updateC; auto; rewrite free_O_type// Gamma_A_updateC; auto; rewrite free_O_type.
rewrite P1; split=>//; rewrite ST_set_id big_setX/=.
f_equal; apply eq_bigr=>a _; rewrite O_set_id; apply eq_bigr=>b _.
rewrite -(subst_O_free (A := (A1 * A2)%TA))//.
  by rewrite /= Gamma_A_updateC// Gamma_A_update_id Gamma_A_updateC ?Gamma_A_update_id//; auto.
  by move: Pij Pik=>/= /eqP->/eqP->.
  by move=>/= m; rewrite -negb_or; apply contraNN=>/orP[/eqP|/eqP]->.
rewrite A_sem_pair// A_set_id  (O_sem_eq X (A_value_updateC _ _ _ _)); auto.
rewrite [in RHS]free_O_sem// (O_sem_eq X (A_value_updateC _ _ _ _)); auto.
by rewrite [in RHS]free_O_sem.
Qed.

Lemma AX_SUM_EXPAND_1 i K ca (av : A_value ca) :
  free_K i K ->
  \sum_(i ∈ U(πK(typeK(K)))) ('<`i| · K) *: '|`i> =k K >> av.
Proof.
move=>P; simplify; contra1; split; 
  first by rewrite Gamma_A_update_id.
rewrite -big_setT.
under eq_bigr do rewrite !V_set_id t2tv_conj.
rewrite {-9 13}Gamma_A_update_id.
under eq_bigr do rewrite !A_value_update_id A_set_id (free_K_sem _ _ P) -outpE.
by rewrite -sum_lfunE sumonb_out lfunE /= K_set_sem.
Qed.

Lemma AX_SUM_EXPAND_2 i B ca (av : A_value ca) :
  free_B i B ->
  \sum_(i ∈ U(πB(typeB(B)))) (B · '|`i>) *: '<`i| =b B >> av.
Proof.
move=>P; simplify; contra1; split; 
  first by rewrite Gamma_A_update_id.
rewrite -big_setT.
under eq_bigr do rewrite !V_set_id.
rewrite {-11 14}Gamma_A_update_id.
under eq_bigr do rewrite !A_value_update_id A_set_id (free_B_sem _ _ P).
rewrite -[X in V_set X]conjvK linear_sum/=.
under eq_bigr do rewrite conjvZ t2tv_conj conj_dotp.
by rewrite -onb_vec conjvK B_set_sem.
Qed.

Lemma AX_SUM_EXPAND_3 i j O ca (av : A_value ca) :
  i != j -> free_O i O -> free_O j O ->
  \sum_(i ∈ U(πK(typeO(O)))) \sum_(j ∈ U(πB(typeO(O)))) 
    ('<`i| · O · '|`j>) *: ('|`i> ·· '<`j|) =o O >> av.
Proof.
move=>/eqP P1 P2 P3; simplify; contra1; split.
  rewrite {1}Gamma_A_updateC// !Gamma_A_update_id.
  move: E E0; rewrite free_O_type// =>-> Pv.
  by inversion Pv.
rewrite -big_setT.
under eq_bigr do rewrite O_set_id -big_setT.
under eq_bigr do under eq_bigr do rewrite !O_set_id !V_set_id
  trfAC conjfE conjvK !t2tv_conj adj_dotEl.
rewrite {-14 18}Gamma_A_update_id.
rewrite {- 13 16 18 21 23 }Gamma_A_updateC//.
rewrite Gamma_A_update_id .
under eq_bigr do under eq_bigr do rewrite (A_set_eq i (A_value_updateC _ _ _ P1)) 
  !A_value_update_id !A_set_id (free_O_sem _ _ P3) (free_O_sem _ _ P2).
rewrite exchange_big/= -onb_lfun2 O_set_sem// E.
by move: E0; rewrite free_O_type// E=>Pv; inversion Pv.
Qed.

Lemma AX_SUM_SWAP_1 i j M N X ca (av : A_value ca) :
  i != j -> free_ST i N -> free_ST j M ->
  \sum_(i ∈ M)\sum_(j ∈ N) X =s \sum_(j ∈ N)\sum_(i ∈ M) X >> av.
Proof.
move=>/eqP Pij Pi Pj; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite !free_ST_type//.
case E2: (sttype_checker _ _)=>[A2|//]; simplify.
rewrite !free_ST_type// E1 {1}Gamma_A_updateC; auto.
rewrite E; split=>//.
rewrite !free_ST_sem// exchange_big/=; 
apply eq_bigr=>a _; apply eq_bigr=>b _.
by apply/S_sem_eq/A_value_updateC.
Qed.

Lemma AX_SUM_SWAP_2 i j M N X ca (av : A_value ca) :
  i != j -> free_ST i N -> free_ST j M ->
  \sum_(i ∈ M)\sum_(j ∈ N) X =k \sum_(j ∈ N)\sum_(i ∈ M) X >> av.
Proof.
move=>/eqP Pij Pi Pj; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite !free_ST_type//.
case E2: (sttype_checker _ _)=>[A2|//]; simplify.
rewrite !free_ST_type// E1.
have ->: ktype_checker (Gamma_A_update (Gamma_A_update ca j A2) i A1) X = Some (DKet A).
  rewrite {1}Gamma_A_updateC; auto.
split=>//; rewrite !free_ST_sem//; f_equal.
under eq_bigr do rewrite V_set_id.
under [RHS]eq_bigr do rewrite V_set_id.
rewrite exchange_big/=; apply eq_bigr=>a _; apply eq_bigr=>b _.
by rewrite (K_sem_eq X (A_value_updateC _ _ _ Pij)).
Qed.

Lemma AX_SUM_SWAP_3 i j M N X ca (av : A_value ca) :
  i != j -> free_ST i N -> free_ST j M ->
  \sum_(i ∈ M)\sum_(j ∈ N) X =b \sum_(j ∈ N)\sum_(i ∈ M) X >> av.
Proof.
move=>/eqP Pij Pi Pj; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite !free_ST_type//.
case E2: (sttype_checker _ _)=>[A2|//]; simplify.
rewrite !free_ST_type// E1.
have ->: btype_checker (Gamma_A_update (Gamma_A_update ca j A2) i A1) X = Some (DBra A).
  rewrite {1}Gamma_A_updateC; auto.
split=>//; rewrite !free_ST_sem//; f_equal.
under eq_bigr do rewrite V_set_id.
under [RHS]eq_bigr do rewrite V_set_id.
rewrite exchange_big/=; apply eq_bigr=>a _; apply eq_bigr=>b _.
by rewrite (B_sem_eq X (A_value_updateC _ _ _ Pij)).
Qed.

Lemma AX_SUM_SWAP_4 i j M N X ca (av : A_value ca) :
  i != j -> free_ST i N -> free_ST j M ->
  \sum_(i ∈ M)\sum_(j ∈ N) X =o \sum_(j ∈ N)\sum_(i ∈ M) X >> av.
Proof.
move=>/eqP Pij Pi Pj; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
rewrite !free_ST_type//.
case E2: (sttype_checker _ _)=>[A2|//]; simplify.
rewrite !free_ST_type// E1.
have ->: otype_checker (Gamma_A_update (Gamma_A_update ca j A2) i A1) X = Some (DOpt (A,A0)).
  rewrite {1}Gamma_A_updateC; auto.
split=>//; rewrite !free_ST_sem//; f_equal.
under eq_bigr do rewrite O_set_id.
under [RHS]eq_bigr do rewrite O_set_id.
rewrite exchange_big/=; apply eq_bigr=>a _; apply eq_bigr=>b _.
by rewrite (O_sem_eq X (A_value_updateC _ _ _ Pij)).
Qed.

Lemma AX_ALPHA_EQ_1 i j M X ca (av : A_value ca) :
  free_S j X -> bound_S j X ->
    \sum_(i ∈ M) X =s \sum_(j ∈ M) X.[i := `j] >> av.
Proof.
move=>P1 P2.
case: (@eqP _ i j)=>[->|P]; simplify.
  rewrite free_S_subst_id//.
  case E1: (sttype_checker _ _)=>[A1|//]; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
case E2: (stype_checker _ _)=>[[|||]|//]//.
rewrite -(subst_S_free_type (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite Gamma_A_updateC; auto.
rewrite free_S_type// E2; split=>//.
apply eq_bigr=>a _; rewrite -(subst_S_free (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite A_value_update_id A_set_id.
by rewrite -(S_sem_eq X (A_value_updateC _ _ _ P)) [RHS]free_S_sem.
Qed.

Lemma AX_ALPHA_EQ_2 i j M X ca (av : A_value ca) :
  free_K j X -> bound_K j X ->
    \sum_(i ∈ M) X =k \sum_(j ∈ M) X.[i := `j] >> av.
Proof.
move=>P1 P2.
case: (@eqP _ i j)=>[->|P]; simplify.
  rewrite free_K_subst_id//.
  case E1: (sttype_checker _ _)=>[A1|//]; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
case E2: (ktype_checker _ _)=>[[|A2||]|//]//.
rewrite -(subst_K_free_type (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite Gamma_A_updateC; auto.
rewrite free_K_type// E2; split=>//; f_equal.
apply eq_bigr=>a _; rewrite -(subst_K_free (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite A_value_update_id A_set_id.
by rewrite -(K_sem_eq X (A_value_updateC _ _ _ P)) [in RHS]free_K_sem.
Qed.

Lemma AX_ALPHA_EQ_3 i j M X ca (av : A_value ca) :
  free_B j X -> bound_B j X ->
    \sum_(i ∈ M) X =b \sum_(j ∈ M) X.[i := `j] >> av.
Proof.
move=>P1 P2.
case: (@eqP _ i j)=>[->|P]; simplify.
  rewrite free_B_subst_id//.
  case E1: (sttype_checker _ _)=>[A1|//]; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
case E2: (btype_checker _ _)=>[[|A2||]|//]//.
rewrite -(subst_B_free_type (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite Gamma_A_updateC; auto.
rewrite free_B_type// E2; split=>//; f_equal.
apply eq_bigr=>a _; rewrite -(subst_B_free (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite A_value_update_id A_set_id.
by rewrite -(B_sem_eq X (A_value_updateC _ _ _ P)) [in RHS]free_B_sem.
Qed.

Lemma AX_ALPHA_EQ_4 i j M X ca (av : A_value ca) :
  free_O j X -> bound_O j X ->
    \sum_(i ∈ M) X =o \sum_(j ∈ M) X.[i := `j] >> av.
Proof.
move=>P1 P2.
case: (@eqP _ i j)=>[->|P]; simplify.
  rewrite free_O_subst_id//.
  case E1: (sttype_checker _ _)=>[A1|//]; simplify.
case E1: (sttype_checker _ _)=>[A1|//].
case E2: (otype_checker _ _)=>[[|A2||]|//]//.
rewrite -(subst_O_free_type (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite Gamma_A_updateC; auto.
rewrite free_O_type// E2; split=>//; f_equal.
apply eq_bigr=>a _; rewrite -(subst_O_free (A := A1))/=.
  by rewrite /= Gamma_A_update_id.
  by apply/eqP.
  by move=>m; apply contraNN=>/eqP->.
rewrite A_value_update_id A_set_id.
by rewrite -(O_sem_eq X (A_value_updateC _ _ _ P)) [in RHS]free_O_sem.
Qed.

End Term_Rewriting_System.
End DiracTRS_SOUND.
End Playground2.