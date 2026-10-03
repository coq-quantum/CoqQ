(* Finite product counting for classical.pdf Lemma 7.2(2).
   The independent combinatorial argument is in SHOR-PRODUCT-NOTES.md. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ClassicalShorProductCounting.

Section ScalarCounting.
Variables (I K : finType) (i0 : I).
Variables (c : I -> K -> nat) (n : I -> nat).

Lemma product_half_bound k :
  (forall i, i != i0 -> 2 * c i k <= n i) ->
  2 ^ #|I|.-1 * (\prod_i c i k) <=
  c i0 k * \prod_(i | i != i0) n i.
Proof.
move=>Hhalf.
rewrite (bigD1 i0) //= mulnCA.
apply: leq_mul=>//.
have E : 2 ^ #|I|.-1 = \prod_(i : I | i != i0) 2.
  by rewrite prod_nat_const cardC1.
rewrite E -big_split.
exact: leq_prod Hhalf.
Qed.

Theorem sum_product_half_bound :
  (\sum_k c i0 k = n i0) ->
  (forall i k, i != i0 -> 2 * c i k <= n i) ->
  2 ^ #|I|.-1 * (\sum_k \prod_i c i k) <= \prod_i n i.
Proof.
move=>Hsum Hhalf.
rewrite (bigD1 i0) //= -Hsum big_distrl big_distrr.
apply: leq_sum=>k _; exact: product_half_bound (fun i Hi => Hhalf i k Hi).
Qed.
End ScalarCounting.

Section ProductCounting.
Variables (I : finType) (X : I -> finType) (K : finType).
Variables (label : forall i, X i -> K) (i0 : I).
Arguments label : clear implicits.
Notation fT := {dffun forall i : I, X i}.

Definition diagonal (f : fT) := [forall i, label i (f i) == label i0 (f i0)].
Definition label_count i k := #|[pred x : X i | label i x == k]|.

Lemma product_card : #|fT| = \prod_i #|X i|.
Proof. by rewrite card_dep_ffun foldrE big_map big_enum. Qed.

Lemma family_card k :
  #|[pred f : fT | [forall i, label i (f i) == k]]| =
  \prod_i label_count i k.
Proof.
change (#|(family (fun i => [pred x : X i | label i x == k]) : simpl_pred fT)| =
  \prod_i label_count i k).
by rewrite card_family foldrE big_map big_enum.
Qed.

Lemma label_count_sum i : \sum_k label_count i k = #|X i|.
Proof.
rewrite -sum1_card (partition_big (label i) predT) //.
by apply: eq_bigr=>k _; rewrite /label_count -sum1_card; apply: eq_bigl=>x; rewrite andTb.
Qed.

Lemma diagonal_card : #|diagonal| = \sum_k \prod_i label_count i k.
Proof.
rewrite -sum1_card (partition_big (fun f : fT => label i0 (f i0)) predT) //.
apply: eq_bigr=>k _; rewrite -family_card -sum1_card.
apply: eq_bigl=>f; apply/andP/forallP=>[[/forallP H /eqP H0] i|H].
  by rewrite -H0; exact: H.
split; last exact: H.
apply/forallP=>i; by rewrite (eqP (H i)) (eqP (H i0)).
Qed.

Theorem diagonal_half_bound :
  (forall i k, i != i0 -> 2 * label_count i k <= #|X i|) ->
  2 ^ #|I|.-1 * #|diagonal| <= #|fT|.
Proof.
move=>Hhalf; rewrite diagonal_card product_card.
exact: sum_product_half_bound (label_count_sum i0) Hhalf.
Qed.
End ProductCounting.

Section NaturalLabels.
Variables (I : finType) (X : I -> finType).
Variables (label : forall i, X i -> nat) (i0 : I).
Arguments label : clear implicits.
Notation fT := {dffun forall i : I, X i}.

Definition label_bound := (\max_i \max_(x : X i) label i x).+1.

Lemma label_bounded i (x : X i) : label i x < label_bound.
Proof.
rewrite /label_bound ltnS.
exact: leq_trans (leq_bigmax x) (leq_bigmax i).
Qed.

Definition finite_label i (x : X i) : 'I_label_bound := Ordinal (label_bounded x).

Definition natural_diagonal (f : fT) :=
  [forall i, label i (f i) == label i0 (f i0)].

Lemma natural_diagonalE (f : fT) :
  natural_diagonal f = diagonal (@finite_label) i0 f.
Proof.
apply: eq_forallb=>i.
by rewrite -val_eqE.
Qed.

Lemma finite_label_count i (k : 'I_label_bound) :
  label_count (@finite_label) i k = #|[pred x : X i | label i x == val k]|.
Proof. by apply: eq_card=>x; rewrite !inE -val_eqE. Qed.

Theorem natural_diagonal_half_bound :
  (forall i k, i != i0 -> 2 * #|[pred x : X i | label i x == k]| <= #|X i|) ->
  2 ^ #|I|.-1 * #|natural_diagonal| <= #|fT|.
Proof.
move=>Hhalf.
have E : #|natural_diagonal| = #|diagonal (@finite_label) i0|.
  exact: eq_card natural_diagonalE.
rewrite E; apply: diagonal_half_bound=>i k Hi.
rewrite finite_label_count; exact: Hhalf.
Qed.

End NaturalLabels.

End ClassicalShorProductCounting.
