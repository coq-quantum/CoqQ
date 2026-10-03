(* Concrete unit-group CRT for the counting argument in Lemma 7.2(2).
   See SHOR-CRT-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup perm
  morphism quotient action ssrnum zmodp cyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import GRing.Theory GroupScope.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope nat_scope.

Module ClassicalShorCRT.

Definition unit_value N (u : {unit 'Z_N}) : nat := val (val u).

Lemma unit_value_lt N (HN : 1 < N) (u : {unit 'Z_N}) : unit_value u < N.
Proof.
have H : unit_value u < (Zp_trunc N).+2 := ltn_ord (val u).
by rewrite (Zp_cast HN) in H.
Qed.

Lemma unit_value_coprime N (HN : 1 < N) (u : {unit 'Z_N}) :
  coprime N (unit_value u).
Proof.
have H := valP u.
change (is_true (coprime (Zp_trunc N).+2 (unit_value u))) in H.
by rewrite (Zp_cast HN) in H.
Qed.

Definition unit_of_nat N (HN : 1 < N) a (Ha : coprime N a) : {unit 'Z_N} :=
  @FinRing.Unit _ (a%:R : 'Z_N)
    (eq_ind_r (fun b => is_true b) Ha (unitZpE a HN)).

Lemma unit_of_nat_value N (HN : 1 < N) a (Ha : coprime N a) :
  unit_value (unit_of_nat HN Ha) = a %% N.
Proof. exact: val_Zp_nat. Qed.

Lemma unit_value_inj N : injective (@unit_value N).
Proof. move=>u v H; apply/val_inj/val_inj; exact: H. Qed.

Lemma unit_value_one N (HN : 1 < N) : unit_value (1%g : {unit 'Z_N}) = 1.
Proof.
change (1 %% (Zp_trunc N).+2 = 1).
by rewrite (Zp_cast HN) modn_small.
Qed.

Lemma unit_value_mul N (HN : 1 < N) (u v : {unit 'Z_N}) :
  unit_value (u * v)%g = (unit_value u * unit_value v) %% N.
Proof.
change ((unit_value u * unit_value v) %% (Zp_trunc N).+2 =
  (unit_value u * unit_value v) %% N).
by rewrite (Zp_cast HN).
Qed.

Lemma unit_value_power N (HN : 1 < N) (u : {unit 'Z_N}) k :
  unit_value (u ^+ k) = unit_value u ^ k %% N.
Proof.
have H : unit_value (u ^+ k) = unit_value u ^ k %% (Zp_trunc N).+2.
  by rewrite /unit_value unit_Zp_expg.
by rewrite (Zp_cast HN) in H.
Qed.

Section Reduction.
Variables N M : nat.
Hypotheses (HN : 1 < N) (HM : 1 < M) (D : M %| N).

Definition unit_reduce (u : {unit 'Z_N}) : {unit 'Z_M} :=
  unit_of_nat HM (coprime_dvdl D (unit_value_coprime HN u)).

Lemma unit_reduce_value u : unit_value (unit_reduce u) = unit_value u %% M.
Proof. exact: unit_of_nat_value. Qed.

Lemma unit_reduce_mul u v : unit_reduce (u * v)%g = (unit_reduce u * unit_reduce v)%g.
Proof.
apply: unit_value_inj.
by rewrite unit_reduce_value (unit_value_mul HN) (unit_value_mul HM)
  !unit_reduce_value modn_dvdm // modnMm.
Qed.

Lemma unit_reduce_is_morphism :
  {in [set: {unit 'Z_N}] &, {morph unit_reduce : u v / (u * v)%g}}.
Proof. by move=>u v _ _; exact: unit_reduce_mul. Qed.

Canonical unit_reduction := Morphism unit_reduce_is_morphism.

Lemma unit_reduce_power u k : unit_reduce (u ^+ k) = (unit_reduce u) ^+ k.
Proof. by rewrite morphX ?inE. Qed.

End Reduction.

Section Binary.
Variables m n : nat.
Hypotheses (Hm : 1 < m) (Hn : 1 < n) (Hcop : coprime m n).

Lemma product_nontrivial : 1 < m * n.
Proof.
apply: leq_trans Hm _.
by rewrite leq_pmulr //; exact: ltnW Hn.
Qed.

Lemma reduce_left_unit (u : {unit 'Z_(m * n)}) : coprime m (unit_value u).
Proof. by move: (unit_value_coprime product_nontrivial u); rewrite coprimeMl=>/andP[]. Qed.

Lemma reduce_right_unit (u : {unit 'Z_(m * n)}) : coprime n (unit_value u).
Proof. by move: (unit_value_coprime product_nontrivial u); rewrite coprimeMl=>/andP[]. Qed.

Definition crt_units (u : {unit 'Z_(m * n)}) : {unit 'Z_m} * {unit 'Z_n} :=
  (unit_of_nat Hm (reduce_left_unit u), unit_of_nat Hn (reduce_right_unit u)).

Lemma chinese_unit (u : {unit 'Z_m}) (v : {unit 'Z_n}) :
  coprime (m * n) (chinese m n (unit_value u) (unit_value v)).
Proof.
rewrite coprimeMl -[coprime m _]coprime_modr -[coprime n _]coprime_modr
  chinese_modl // chinese_modr // !coprime_modr.
by rewrite (unit_value_coprime Hm) (unit_value_coprime Hn).
Qed.

Definition crt_units_inverse (uv : {unit 'Z_m} * {unit 'Z_n}) : {unit 'Z_(m * n)} :=
  unit_of_nat product_nontrivial (chinese_unit uv.1 uv.2).

Lemma crt_units_inverseK : cancel crt_units_inverse crt_units.
Proof.
move=>[u v]; rewrite /crt_units /crt_units_inverse /=.
congr (_, _); apply: unit_value_inj; rewrite !unit_of_nat_value.
- by rewrite modn_dvdm ?dvdn_mulr // chinese_modl // modn_small // unit_value_lt.
- by rewrite modn_dvdm ?dvdn_mull // chinese_modr // modn_small // unit_value_lt.
Qed.

Lemma crt_unitsK : cancel crt_units crt_units_inverse.
Proof.
move=>u; apply: unit_value_inj.
rewrite /crt_units_inverse /crt_units /= !unit_of_nat_value -chinese_mod //.
by rewrite modn_small // (unit_value_lt product_nontrivial).
Qed.

Lemma crt_units_bijective : bijective crt_units.
Proof. exact: Bijective crt_unitsK crt_units_inverseK. Qed.

Lemma crt_units_leftE u : (crt_units u).1 =
  unit_reduce product_nontrivial Hm (@dvdn_mulr m m n (dvdnn m)) u.
Proof. by apply: unit_value_inj; rewrite /crt_units /= unit_of_nat_value unit_reduce_value. Qed.

Lemma crt_units_rightE u : (crt_units u).2 =
  unit_reduce product_nontrivial Hn (@dvdn_mull n m n (dvdnn n)) u.
Proof. by apply: unit_value_inj; rewrite /crt_units /= unit_of_nat_value unit_reduce_value. Qed.

Lemma crt_units_one : crt_units 1%g = (1%g, 1%g).
Proof.
apply: injective_projections; rewrite /= ?crt_units_leftE ?crt_units_rightE;
  apply: unit_value_inj; rewrite unit_of_nat_value
  (unit_value_one product_nontrivial) unit_value_one // modn_small //.
Qed.

Lemma crt_units_mul u v : crt_units (u * v)%g =
  ((crt_units u).1 * (crt_units v).1, (crt_units u).2 * (crt_units v).2)%g.
Proof.
apply: injective_projections.
- change ((crt_units (u * v)%g).1 = ((crt_units u).1 * (crt_units v).1)%g).
  by rewrite !crt_units_leftE unit_reduce_mul.
- change ((crt_units (u * v)%g).2 = ((crt_units u).2 * (crt_units v).2)%g).
  by rewrite !crt_units_rightE unit_reduce_mul.
Qed.

Lemma crt_units_power u k : crt_units (u ^+ k) =
  ((crt_units u).1 ^+ k, (crt_units u).2 ^+ k).
Proof.
apply: injective_projections.
- change ((crt_units (u ^+ k)).1 = (crt_units u).1 ^+ k).
  by rewrite !crt_units_leftE unit_reduce_power.
- change ((crt_units (u ^+ k)).2 = (crt_units u).2 ^+ k).
  by rewrite !crt_units_rightE unit_reduce_power.
Qed.

Lemma crt_units_order_dvd u k :
  (#[u] %| k) = (#[((crt_units u).1)] %| k) && (#[((crt_units u).2)] %| k).
Proof.
by rewrite !order_dvdn -(inj_eq (can_inj crt_unitsK))
  crt_units_power crt_units_one xpair_eqE.
Qed.

Lemma crt_units_order u : #[u] = lcmn #[((crt_units u).1)] #[((crt_units u).2)].
Proof.
apply/eqP; rewrite eqn_dvd crt_units_order_dvd dvdn_lcml dvdn_lcmr /=.
by rewrite dvdn_lcm -crt_units_order_dvd dvdnn.
Qed.

Lemma crt_units_card : #|units_Zp (m * n)| = #|units_Zp m| * #|units_Zp n|.
Proof. by rewrite /units_Zp !cardsT (bij_eq_card crt_units_bijective) card_prod. Qed.

End Binary.
End ClassicalShorCRT.
