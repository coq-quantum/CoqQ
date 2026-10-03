(* Iterated concrete unit CRT. See SHOR-CRT-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup perm
  morphism quotient action ssrnum zmodp cyclic.
From quantum.example.classical Require Import shor_crt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import GRing.Theory GroupScope.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope nat_scope.

Module ClassicalShorCRTProduct.
Import ClassicalShorCRT.

Lemma coprime_product a s : all (coprime a) s -> coprime a (\prod_(b <- s) b).
Proof.
elim: s=>[|b s IH] /=; first by rewrite big_nil coprimen1.
by move=>/andP[H1 H2]; rewrite big_cons coprimeMr H1 IH.
Qed.

Lemma totient_product s : pairwise coprime s ->
  totient (\prod_(b <- s) b) = \prod_(b <- s) totient b.
Proof.
elim: s=>[|b s IH] /=; first by rewrite !big_nil /totient /=.
move=>/andP[H1 H2]; rewrite !big_cons totient_coprime ?coprime_product //.
by rewrite IH.
Qed.

Lemma congruence_product s a b : pairwise coprime s ->
  (a == b %[mod \prod_(d <- s) d]) = all (fun d => a == b %[mod d]) s.
Proof.
elim: s=>[|d s IH] /=; first by rewrite big_nil !modn1.
move=>/andP[H1 H2]; rewrite big_cons chinese_remainder ?coprime_product //.
by rewrite IH.
Qed.

Section Product.
Variable I : finType.
Variable q : I -> nat.
Variable N : nat.
Hypothesis HN : 1 < N.
Hypothesis Hq : forall i, 1 < q i.
Hypothesis q_coprime : forall i j, i != j -> coprime (q i) (q j).
Hypothesis productE : (\prod_i q i) = N.
Local Notation unitT := (Finite.clone {unit 'Z_N} _).
Local Notation tupleT := (Finite.clone {dffun forall i : I, {unit 'Z_(q i)}} _).

Lemma moduli_pairwise : pairwise coprime [seq q i | i <- enum I].
Proof.
rewrite pairwise_map; apply: (@sub_pairwise _ [rel i j | i != j]).
- by move=>i j Hij; exact: q_coprime.
- by rewrite -uniq_pairwise enum_uniq.
Qed.

Lemma factor_dvd i : q i %| N.
Proof. by rewrite -productE (bigD1 i) // dvdn_mulr. Qed.

Lemma moduli_productE : (\prod_(d <- [seq q i | i <- enum I]) d) = N.
Proof. by rewrite big_map big_enum productE. Qed.

Definition reduction i := unit_reduction HN (Hq i) (factor_dvd i).

Definition unit_tuple (u : {unit 'Z_N}) : {dffun forall i : I, {unit 'Z_(q i)}} :=
  [ffun i : I => reduction i u].

Lemma unit_tupleE u i : unit_tuple u i = reduction i u.
Proof. exact: ffunE. Qed.

Lemma reductions_jointly_injective (u v : {unit 'Z_N}) :
  (forall i, reduction i u = reduction i v) -> u = v.
Proof.
move=>E; apply: unit_value_inj; apply/eqP.
have CP a b : (a == b %[mod N]) =
    all (fun d => a == b %[mod d]) [seq q i | i <- enum I].
  by rewrite -moduli_productE congruence_product // moduli_pairwise.
have C : unit_value u == unit_value v %[mod N].
  rewrite CP.
  apply/allP=>d /mapP[i _ ->].
  have := congr1 (@unit_value (q i)) (E i).
  by rewrite /reduction !unit_reduce_value=>->.
by move: C; rewrite !modn_small ?unit_value_lt.
Qed.

Lemma unit_tuple_injective : injective unit_tuple.
Proof.
move=>u v /ffunP E; apply: reductions_jointly_injective=>i.
by have := E i; rewrite !unit_tupleE.
Qed.

Lemma unit_tuple_card :
  #|unitT| = #|tupleT|.
Proof.
rewrite -[LHS]cardsT -/(units_Zp N) card_units_Zp ?(ltnW HN) //.
rewrite card_dep_ffun foldrE big_map big_enum.
rewrite -moduli_productE totient_product ?moduli_pairwise // big_map big_enum.
apply: eq_bigr=>i _.
by rewrite -cardsT -/(units_Zp (q i)) card_units_Zp //; exact: ltnW (Hq i).
Qed.

Lemma unit_tuple_bijective : bijective unit_tuple.
Proof. apply: inj_card_bij unit_tuple_injective _; by rewrite unit_tuple_card. Qed.

End Product.
End ClassicalShorCRTProduct.
