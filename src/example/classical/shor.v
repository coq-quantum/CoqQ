(* Classical: shor. See README.md and PROOF_NOTES.md. *)
From HB Require Import structures.

From mathcomp Require Import all_ssreflect finmap ring_tactic.
From mathcomp Require Import all_ssreflect fingroup perm
  morphism quotient action ssrnum zmodp cyclic.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_ssreflect fingroup morphism
  quotient cyclic nilpotent abelian.
From mathcomp Require Import all_ssreflect all_fingroup cyclic.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_ssreflect finmap  cyclic.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.


From mathcomp.analysis Require Import topology normedtype sequences exp trigo.


From quantum.example.classical Require Import language state assertion semantics hoare auxiliary algorithms.
Module ClassicalModularUnitary.
(* Equation (17), classical.pdf. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope nat_scope.
Import ClassicalSemantics.
Section Modular.
Variables (x N : nat).
Hypothesis coprime_xN : coprime x N.
Hypothesis modulus_positive : (0 < N)%N.

Lemma modular_cancel_le a b : (b <= a)%N ->
  (x * a == x * b %[mod N]) = (a == b %[mod N]).
Proof.
move=>Hba; rewrite !eqn_mod_dvd ?leq_mul // -mulnBr.
by rewrite Gauss_dvdr // coprime_sym.
Qed.

Lemma modular_cancel a b : (a < N)%N -> (b < N)%N ->
  (x * a) %% N = (x * b) %% N -> a = b.
Proof.
move=>Ha Hb E; apply/eqP.
case: (leqP b a)=>Hba.
- have H : (x * a == x * b %[mod N]) by apply/eqP.
  by move: H; rewrite (modular_cancel_le Hba) (modn_small Ha) (modn_small Hb).
- have Eb : (x * b) %% N = (x * a) %% N := esym E.
  have H : (x * b == x * a %[mod N]) by apply/eqP.
  by move: H; rewrite (modular_cancel_le (ltnW Hba)) (modn_small Hb) (modn_small Ha) eq_sym.
Qed.

Definition modular_value a := if (a < N)%N then (x * a) %% N else a.

Lemma modular_value_inj : injective modular_value.
Proof.
move=>a b; rewrite /modular_value.
case Ha: (a < N)%N; case Hb: (b < N)%N.
- exact: modular_cancel Ha Hb.
- move=>E; move: (ltn_pmod (x * a) modulus_positive); by rewrite E Hb.
- move=>E; move: (ltn_pmod (x * b) modulus_positive); by rewrite -E Ha.
- by [].
Qed.

Variable L : nat.
Hypothesis register_capacity : (N <= 2 ^ L)%N.

Lemma modular_value_bound (a : 'I_(2 ^ L)) : (modular_value a < 2 ^ L)%N.
Proof.
rewrite /modular_value; case: ifP=>Ha; last exact: ltn_ord.
exact: leq_trans (ltn_pmod (x * a) modulus_positive) register_capacity.
Qed.

Definition modular_ordinal (a : 'I_(2 ^ L)) := Ordinal (modular_value_bound a).

Lemma modular_ordinal_inj : injective modular_ordinal.
Proof.
move=>a b E; apply/val_inj; apply: modular_value_inj.
exact: (congr1 (fun z : 'I_(2 ^ L) => (z : nat)) E).
Qed.

Definition modular_bits (a : L.-tuple bool) := ord2bseq (modular_ordinal (bseq2ord a)).

Lemma modular_bits_inj : injective modular_bits.
Proof.
move=>a b E; apply: bseq2ord_inj; apply: modular_ordinal_inj.
exact: ord2bseq_inj E.
Qed.

Definition modular_basis (a : L.-tuple bool) : 'Hs(L.-tuple bool) := ''(modular_bits a).

Lemma modular_basis_dot a b :
  [< modular_basis a; modular_basis b >] = (a == b)%:R.
Proof. by rewrite /modular_basis onb_dot (inj_eq modular_bits_inj). Qed.

HB.instance Definition _ := isPONB.Build 'Hs(L.-tuple bool) (L.-tuple bool)
  modular_basis modular_basis_dot.

Definition modular_unitary : 'FU('Hs(L.-tuple bool)) := PUnitary t2tv modular_basis.

Theorem modular_unitaryE a : modular_unitary ''a = ''(modular_bits a).
Proof. exact: PUnitaryE. Qed.

Theorem modular_unitary_basis_value a :
  bseq2ord (modular_bits a) = modular_ordinal (bseq2ord a).
Proof. exact: ord2bseqK. Qed.

Lemma modular_unitary_outside a : (N <= bseq2ord a)%N -> modular_unitary ''a = ''a.
Proof.
move=>Ha; rewrite modular_unitaryE; congr (t2tv _).
apply: bseq2ord_inj; rewrite modular_unitary_basis_value; apply/val_inj.
by rewrite /modular_ordinal /= /modular_value ltnNge Ha.
Qed.

Definition residue_ordinal a : 'I_(2 ^ L) :=
  Ordinal (leq_trans (ltn_pmod a modulus_positive) register_capacity).
Definition residue_bits a := ord2bseq (residue_ordinal a).

Lemma residue_bits_value a : (bseq2ord (residue_bits a) : nat) = a %% N.
Proof. by rewrite /residue_bits ord2bseqK. Qed.

Lemma modular_bits_residue a : modular_bits (residue_bits a) = residue_bits (x * a).
Proof.
apply: bseq2ord_inj; apply/val_inj.
rewrite modular_unitary_basis_value.
change (modular_value (bseq2ord (residue_bits a)) =
  (bseq2ord (residue_bits (x * a)) : nat)).
rewrite /modular_value !residue_bits_value (ltn_pmod a modulus_positive) modnMmr.
by [].
Qed.

Theorem modular_power_residue k a :
  (modular_unitary%:VF ^+ k) ''(residue_bits a) = ''(residue_bits (x ^ k * a)).
Proof.
elim: k=>[|k IH].
- by rewrite expr0 lfunE expn0 mul1n.
- by rewrite exprS lfunE /= IH modular_unitaryE modular_bits_residue expnS mulnA.
Qed.

Lemma residue_one_value : 1 < N -> (bseq2ord (residue_bits 1) : nat) = 1.
Proof. by move=>H1; rewrite residue_bits_value modn_small. Qed.

End Modular.
End ClassicalModularUnitary.


Module ClassicalShorCRT.
(* Concrete unit-group CRT for the counting argument in Lemma 7.2(2).
   See PROOF_NOTES.md. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import GRing.Theory GroupScope.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope nat_scope.
Import ClassicalSemantics.
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


Module ClassicalShorComposite.
(* The printed cmp(N) implies at least two distinct prime divisors.
   See PROOF_NOTES.md for the prior mathematical argument. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Definition not_perfect_power N :=
  forall a b, 1 < a -> 1 < b -> N != a ^ b.

Definition cmp N :=
  [ /\ 2 < N, odd N, ~~ prime N & not_perfect_power N ].

Theorem distinct_prime_count_gt1 N :
  1 < N -> ~~ prime N -> not_perfect_power N -> 1 < size (primes N).
Proof.
move=>HN Hcomposite Hpower.
have Hnonempty : primes N != [::] by rewrite primes_eq0 -leqNgt.
case E: (primes N) Hnonempty=>[//|p [|q ps]] //= _.
have Hp : prime p.
  have Hmem : p \in primes N by rewrite E mem_head.
  by move: Hmem; rewrite mem_primes=>/and3P[].
have Hfactor : N = p ^ logn p N.
  by rewrite {1}(prod_prime_decomp (ltnW HN)) prime_decompE E /= big_seq1.
have He : 1 < logn p N.
  case Ee: (logn p N) Hfactor=>[|[|e]] //= Ef.
  - by move: HN; rewrite Ef.
  - by move: Hcomposite; rewrite Ef expn1 Hp.
by have := Hpower p (logn p N) (prime_gt1 Hp) He; rewrite -Hfactor eqxx.
Qed.

Theorem cmp_distinct_prime_count N : cmp N -> 1 < size (primes N).
Proof.
move=>[HN _ Hcomposite Hpower].
exact: distinct_prime_count_gt1 (ltnW HN) Hcomposite Hpower.
Qed.
End ClassicalShorComposite.


Module ClassicalShorArithmetic.
(* Classical arithmetic used by Shor's factor extraction, Lemma 7.2(1).
   The canonical-residue argument is in PROOF_NOTES.md. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Definition nontrivial_factor N d := (1 < d < N) && (d %| N).

Lemma nontrivial_sqrt_factor N s :
  1 < s -> s + 1 < N -> s ^ 2 == 1 %[mod N] ->
  nontrivial_factor N (gcdn (s - 1) N).
Proof.
move=>Hs HN Hsq.
have Hs0 : 0 < s - 1 by rewrite subn_gt0.
have Hs1 : 1 <= s := ltnW Hs.
have Hss : 1 <= s ^ 2 by rewrite -[1](exp1n 2) leq_sqr.
have Dprod : N %| (s - 1) * (s + 1).
  by rewrite -subn_sqr exp1n -(eqn_mod_dvd N Hss).
have Hcop : ~~ coprime N (s - 1).
  apply/negP=>Hc.
  have Dplus : N %| s + 1 by move: Dprod; rewrite Gauss_dvdr.
  have Hplus : 0 < s + 1 by rewrite addn1.
  have Hle := dvdn_leq Hplus Dplus.
  by move: (leq_ltn_trans Hle HN); rewrite ltnn.
have Hg0 : 0 < gcdn (s - 1) N by rewrite gcdn_gt0 Hs0.
have Hg1 : 1 < gcdn (s - 1) N.
  by rewrite ltn_neqAle eq_sym -/(coprime (s - 1) N) coprime_sym Hcop Hg0.
have Hgle : gcdn (s - 1) N <= s - 1 := dvdn_leq Hs0 (dvdn_gcdl _ _).
have Hsmall : s - 1 < N.
  apply: leq_ltn_trans HN.
  exact: leq_trans (leq_subr 1 s) (leq_addr 1 s).
rewrite /nontrivial_factor Hg1 (leq_ltn_trans Hgle Hsmall) /=.
exact: dvdn_gcdr.
Qed.

Lemma nontrivial_sqrt_factor_mod N s :
  1 < N -> 1 < s %% N -> s %% N + 1 < N ->
  s ^ 2 == 1 %[mod N] -> nontrivial_factor N (gcdn (s - 1) N).
Proof.
move=>HN Hr HrN Hsq.
have HN0 : 0 < N := ltnW HN.
have Hr1 : 1 <= s %% N := ltnW Hr.
have Hs1 : 1 <= s := leq_trans Hr1 (leq_mod s N).
have Hr0 : (s %% N < 1) = false by rewrite ltnNge Hr1.
have Epred : (s - 1) %% N = s %% N - 1.
  by rewrite modnB // (@modn_small 1 N HN) Hr0 mul0n add0n.
rewrite -gcdn_modl Epred.
apply: nontrivial_sqrt_factor=>//.
by rewrite modnXm.
Qed.

(* The paper's continued-fraction selector, with an explicit failure result.
   A positive rational denominator supplies enough Euclidean steps. *)
Fixpoint convergents fuel a b : seq (nat * nat) :=
  if fuel is fuel'.+1 then
    if b == 0 then [::] else
      let q := a %/ b in
      (q, 1) :: map (fun pd => (q * pd.1 + pd.2, pd.1))
        (convergents fuel' b (a %% b))
  else [::].

Lemma convergents_stable fuel a b extra : b <= fuel ->
  convergents (fuel + extra) a b = convergents fuel a b.
Proof.
elim: fuel a b=>[a b|fuel IH a b] Hb.
- have -> : b = 0 by apply/eqP; move: Hb; rewrite leqn0.
  by rewrite add0n; case: extra.
- rewrite addSn /=; case Eb: (b == 0)=>//.
  congr (_ :: _); congr (map _ _).
  apply: IH.
  have Hb0 : 0 < b by rewrite lt0n Eb.
  exact: leq_trans (ltn_pmod a Hb0) Hb.
Qed.

Definition approximation_test a b (pd : nat * nat) :=
  (0 < pd.2) &&
  (2 * pd.2 * ((pd.1 * b - a * pd.2) + (a * pd.2 - pd.1 * b)) < b).

Definition printed_postprocess a b :=
  match map snd (seq.filter (approximation_test a b) (convergents b.+1 a b)) with
  | [::] => None
  | d :: ds => Some (foldr minn d ds)
  end.

Lemma printed_quarter_counterexample : printed_postprocess 1 4 = Some 1.
Proof. by vm_compute. Qed.

Lemma printed_three_quarters_counterexample : printed_postprocess 3 4 = Some 1.
Proof. by vm_compute. Qed.

Lemma two_mod_fifteen_order :
  (2 ^ 4 == 1 %[mod 15]) /\
  (forall k, 0 < k < 4 -> ~~ (2 ^ k == 1 %[mod 15])).
Proof.
split; first by vm_compute.
case=>[//|[|[|[|k]]]] //=.
Qed.
End ClassicalShorArithmetic.


Module ClassicalShorProductCounting.
(* Finite product counting for classical.pdf Lemma 7.2(2).
   The independent combinatorial argument is in PROOF_NOTES.md. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
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


Module ClassicalShorGroupCounting.
(* Finite-group counting for Lemma 7.2(2); see PROOF_NOTES.md. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Lemma dvdn_half_logn d n : 0 < n -> d %| n -> 2 %| n ->
  (d %| n %/ 2) = (logn 2 d < logn 2 n).
Proof.
move=>Hn Hd H2.
have Hd0 : 0 < d := dvdn_gt0 Hn Hd.
have Hq0 : 0 < n %/ d by rewrite (@divn_gt0 d n Hd0); exact: dvdn_leq Hn Hd.
rewrite dvdn_divRL // mulnC -dvdn_divRL //.
rewrite -{1}(expn1 2) pfactor_dvdn //.
by rewrite logn_div // subn_gt0.
Qed.

Section FiniteGroup.
Variable gT : finGroupType.
Variable z : gT.
Hypothesis abG : abelian [set: gT].
Hypothesis z_neq1 : z != 1%g.
Hypothesis z_square : (z ^+ 2)%g = 1%g.
Hypothesis roots_two : forall x : gT, (x ^+ 2)%g = 1%g -> x = 1%g \/ x = z.

Local Open Scope group_scope.
Let D := exponent [set: gT].

Lemma exponent_even : (2 %| D)%N.
Proof.
have oz : #[z] = 2%N := nt_prime_order (isT : prime 2) z_square z_neq1.
rewrite -oz; apply: dvdn_exponent; by rewrite inE.
Qed.

Lemma half_exponent_square (x : gT) : (x ^+ (D %/ 2)) ^+ 2 = 1.
Proof.
rewrite -expgM (divnK exponent_even).
apply: expg_exponent; by rewrite inE.
Qed.

Lemma half_exponent_is_one (x : gT) :
  (x ^+ (D %/ 2) == 1) = (logn 2 #[x] < logn 2 D)%N.
Proof.
rewrite -order_dvdn dvdn_half_logn ?exponent_gt0 ?exponent_even //.
apply: dvdn_exponent; by rewrite inE.
Qed.

Lemma half_exponent_witness : {g : gT | g ^+ (D %/ 2) = z}.
Proof.
have [g _ Dg] := exponent_witness (abelian_nil abG).
exists g.
have Hneq : g ^+ (D %/ 2) != 1 by rewrite half_exponent_is_one -Dg ltnn.
case: (roots_two (half_exponent_square g))=>[E|E]; last exact: E.
by move: Hneq; rewrite E eqxx.
Qed.

Lemma translate_order_valuation (g : gT) : g ^+ (D %/ 2) = z ->
  forall x : gT, logn 2 #[g * x] != logn 2 #[x].
Proof.
move=>Hg x; apply/negP=>/eqP E.
have Cgx : commute g x by apply: (centsP abG); rewrite inE.
have H : ((g * x) ^+ (D %/ 2) == 1) = (x ^+ (D %/ 2) == 1).
  by rewrite !half_exponent_is_one E.
rewrite expgMn // Hg in H.
case: (roots_two (half_exponent_square x))=>Hx; rewrite Hx in H.
- by move: H; rewrite mulg1 (negbTE z_neq1) eqxx.
- have Ezz : z * z = 1 by move: z_square; rewrite expgS expg1.
  by move: H; rewrite Ezz eqxx (negbTE z_neq1).
Qed.

Theorem order_valuation_fiber_half k :
  (2 * #|[set x : gT | logn 2 #[x] == k]| <= #|{:gT}|)%N.
Proof.
have [g Hg] := half_exponent_witness.
pose A := [set x : gT | logn 2 #[x] == k].
have Hsub : g *: A \subset ~: A.
  rewrite -lcosetE; apply/fintype.subsetP=>y /imsetP[x Hx ->].
  rewrite !inE; move: Hx; rewrite /A inE=>/eqP <-.
  exact: translate_order_valuation Hg x.
have Hcard := subset_leq_card Hsub.
rewrite card_lcoset in Hcard.
rewrite mul2n -addnn -[X in _ <= X](cardsC A) leq_add2l.
exact: Hcard.
Qed.

End FiniteGroup.
End ClassicalShorGroupCounting.


Module ClassicalShorFactorization.
(* The distinct prime-power decomposition used in Lemma 7.2(2).
   See PROOF_NOTES.md for the mathematical argument. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Section Factorization.
Variable N : nat.
Hypothesis HN : 1 < N.

Definition factor_index := 'I_(size (primes N)).
Definition factor_prime (i : factor_index) := nth 0 (primes N) i.
Definition factor_exponent i := logn (factor_prime i) N.
Definition factor_modulus i := factor_prime i ^ factor_exponent i.

Lemma factor_count_positive : 0 < size (primes N).
Proof. by rewrite lt0n size_eq0 primes_eq0 -leqNgt. Qed.

Definition first_factor : factor_index := Ordinal factor_count_positive.

Lemma factor_prime_mem i : factor_prime i \in primes N.
Proof. exact: mem_nth (ltn_ord i). Qed.

Lemma factor_prime_is_prime i : prime (factor_prime i).
Proof. by have := factor_prime_mem i; rewrite mem_primes=>/and3P[]. Qed.

Lemma factor_prime_divides i : factor_prime i %| N.
Proof. by have := factor_prime_mem i; rewrite mem_primes=>/and3P[]. Qed.

Lemma factor_exponent_positive i : 0 < factor_exponent i.
Proof. by rewrite /factor_exponent logn_gt0 factor_prime_mem. Qed.

Lemma factor_modulus_gt1 i : 1 < factor_modulus i.
Proof.
have Hp := prime_gt1 (factor_prime_is_prime i).
by rewrite /factor_modulus -[1](expn0 (factor_prime i)) ltn_exp2l // factor_exponent_positive.
Qed.

Lemma factor_prime_injective : injective factor_prime.
Proof.
move=>i j /eqP Hij; apply/val_inj/eqP.
by move: Hij; rewrite /factor_prime nth_uniq ?primes_uniq ?ltn_ord.
Qed.

Lemma factor_moduli_coprime i j : i != j -> coprime (factor_modulus i) (factor_modulus j).
Proof.
move=>Hij; apply/coprimeXl/coprimeXr.
rewrite prime_coprime ?factor_prime_is_prime // dvdn_prime2 ?factor_prime_is_prime //.
by rewrite (inj_eq factor_prime_injective).
Qed.

Lemma factor_modulus_divides i : factor_modulus i %| N.
Proof. by rewrite /factor_modulus /factor_exponent pfactor_dvdn ?factor_prime_is_prime // (ltnW HN). Qed.

Lemma factor_prime_odd i : odd N -> odd (factor_prime i).
Proof. exact: dvdn_odd (factor_prime_divides i). Qed.

Lemma factor_modulus_odd i : odd N -> odd (factor_modulus i).
Proof. exact: dvdn_odd (factor_modulus_divides i). Qed.

Lemma factorization : N = \prod_(i : factor_index) factor_modulus i.
Proof.
rewrite {1}(prod_prime_decomp (ltnW HN)) prime_decompE big_map /=.
by rewrite (big_nth 0) big_mkord.
Qed.

End Factorization.
End ClassicalShorFactorization.


Module ClassicalShorCRTProduct.
(* Iterated concrete unit CRT. See PROOF_NOTES.md. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import GRing.Theory GroupScope.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope nat_scope.
Import ClassicalSemantics.
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
Proof. by rewrite /unit_tuple ffunE. Qed.

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


Module ClassicalPostprocessCounterexample.
(* The literal printed postprocessor cannot return a denominator above two.
   See C7 and its finite-list proof in PROOF_NOTES.md. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import ClassicalShorArithmetic.

Lemma fold_min_seed seed ds : foldr minn seed ds <= seed.
Proof.
elim: ds=>[|d ds IH] //=; exact: leq_trans (geq_minr _ _) IH.
Qed.

Lemma fold_min_member seed ds d : d \in ds -> foldr minn seed ds <= d.
Proof.
elim: ds=>[|a ds IH] //=; rewrite inE=>/orP[/eqP->|Hd].
- exact: geq_minl.
- exact: leq_trans (geq_minr _ _) (IH Hd).
Qed.

Lemma selector_candidate_bound a b pd d :
  pd \in convergents b.+1 a b -> approximation_test a b pd ->
  printed_postprocess a b = Some d -> d <= pd.2.
Proof.
move=>Hmem Htest.
have H : pd.2 \in map snd (seq.filter (approximation_test a b) (convergents b.+1 a b)).
  apply/mapP; exists pd=>//; by rewrite mem_filter Htest Hmem.
rewrite /printed_postprocess.
case: (map snd _) H=>[|e es] //; rewrite inE=>/orP[/eqP->|He] [ <- ].
- exact: fold_min_seed.
- exact: fold_min_member He.
Qed.

Lemma convergents_first a b : 0 < b -> (a %/ b, 1) \in convergents b.+1 a b.
Proof. by move=>Hb; rewrite /= (gtn_eqF Hb) inE eqxx. Qed.

Lemma convergents_second a b : 0 < a -> a < b ->
  (1, b %/ a) \in convergents b.+1 a b.
Proof.
move=>Ha Hab; have Hb : 0 < b := ltn_trans Ha Hab.
case: b Hb Hab=>[//|b] Hb Hab.
rewrite /= (divn_small Hab) (modn_small Hab) (gtn_eqF Ha) /=.
by rewrite !inE eqxx orbT.
Qed.

Lemma zero_convergent_test a b : 2 * a < b -> approximation_test a b (0,1).
Proof.
by move=>H; rewrite /approximation_test /= !muln1 mul0n sub0n subn0 add0n.
Qed.

Lemma one_convergent_test a b : a < b -> b < 2 * a ->
  approximation_test a b (1,1).
Proof.
move=>Hab Hba.
have Hsub : a - b = 0 by apply/eqP; rewrite subn_eq0; exact: ltnW Hab.
rewrite /approximation_test /= !muln1 mul1n Hsub addn0.
have Hmul : 2 * a <= 2 * b by rewrite leq_mul2l (ltnW Hab) orbT.
rewrite mulnBr ltn_subLR //.
by rewrite mul2n -addnn addnC ltn_add2l.
Qed.

Lemma half_convergent_test a : 0 < a -> approximation_test a (2*a) (1,2).
Proof. by move=>Ha; rewrite /approximation_test /= mul1n [a * 2]mulnC !subnn addn0 muln0 muln_gt0 Ha. Qed.

Theorem printed_denominator_at_most_two a b d : a < b ->
  printed_postprocess a b = Some d -> d <= 2.
Proof.
move=>Hab Hd; case: (ltngtP (2*a) b)=>[Hlow|Hhigh|Heq].
- have Hb : 0 < b := leq_ltn_trans (leq0n a) Hab.
  have Hfirst := @convergents_first a b Hb.
  rewrite (divn_small Hab) in Hfirst.
  exact: leq_trans (selector_candidate_bound Hfirst (zero_convergent_test Hlow) Hd) (isT : 1 <= 2).
- have Ha : 0 < a.
    case Ea: a=>[|a'] //; by move: Hhigh; rewrite Ea muln0 ltn0.
  have Hdiv : b %/ a = 1.
    apply/eqP; rewrite eqn_leq -ltnS ltn_divLR // leq_divRL // mul1n.
    by rewrite Hhigh (ltnW Hab).
  have Hsecond := convergents_second Ha Hab.
  rewrite Hdiv in Hsecond.
  exact: leq_trans (selector_candidate_bound Hsecond (one_convergent_test Hab Hhigh) Hd) (isT : 1 <= 2).
- have Ha : 0 < a.
    case Ea: a=>[|a'] //; by move: Hab; rewrite -Heq Ea muln0 ltnn.
  have Hsecond := convergents_second Ha Hab.
  have Hdiv : b %/ a = 2 by rewrite -Heq mulnC mulKn.
  rewrite Hdiv in Hsecond.
  apply: (selector_candidate_bound Hsecond _ Hd).
  rewrite -Heq; exact: half_convergent_test Ha.
Qed.

Corollary printed_never_four a b : a < b -> printed_postprocess a b != Some 4.
Proof.
move=>Hab; apply/negP=>/eqP Hd.
by have := printed_denominator_at_most_two Hab Hd.
Qed.
End ClassicalPostprocessCounterexample.


Module ClassicalOrderFinding.
(* Literal Section 7.4 source, with explicit partial postprocessing result.
   See PROOF_NOTES.md; no disputed success estimate is assumed. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmSemantics ClassicalPhaseProgram ClassicalModularUnitary.
Local Notation Hq := 'H[msys]_finset.setT.
Section Program.
Variables (N L t : nat).
Hypothesis modulus_nontrivial : (1 < N)%N.
Hypothesis register_capacity : (N <= 2 ^ L)%N.
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).

Lemma modulus_positive : (0 < N)%N.
Proof. exact: ltnW modulus_nontrivial. Qed.

Definition total_modular_unitary b : 'FU('Hs(L.-tuple bool)) :=
  match asboolP (coprime b N) with
  | ReflectT H => @modular_unitary b N H modulus_positive L register_capacity
  | ReflectF _ => (\1 : 'FU('Hs(L.-tuple bool)))
  end.

Lemma total_modular_unitaryE b (Hb : coprime b N) :
  total_modular_unitary b = @modular_unitary b N Hb modulus_positive L register_capacity.
Proof.
rewrite /total_modular_unitary; case: asboolP=>[H|H]; last by exfalso; apply: H.
by rewrite (eq_irrelevance H Hb).
Qed.

Definition one_bits := @residue_bits N modulus_positive L register_capacity 1.
Definition one_state : 'NS('Hs(L.-tuple bool)) := ''one_bits.
Definition one_preparation : 'FU('Hs(L.-tuple bool)) :=
  VUnitary (zero_state (QArray L QBool)) one_state.

Lemma one_bits_value : (bseq2ord one_bits : nat) = 1%N.
Proof. exact: residue_one_value modulus_nontrivial. Qed.

Lemma one_preparationE :
  one_preparation (zero_state (QArray L QBool) : 'Ht (QArray L QBool)) =
    (one_state : 'Hs(L.-tuple bool)).
Proof. exact: VUnitaryE. Qed.

Definition all_hadamards : 'FU('Hs(t.-tuple bool)) :=
  [unitary of tentf_tuple (fun _ : 'I_t => (Hadamard : 'FU('Hs bool)))].

Definition controlled_powers b : 'FU('Ht (QPair (QArray t QBool) (QArray L QBool))) :=
  [unitary of Multiplexer (fun j : t.-tuple bool =>
    [unitary of (total_modular_unitary b)%:VF ^+ (bseq2ord j)])].

Lemma controlled_powersE b j v :
  controlled_powers b (''j ⊗t v) =
  ''j ⊗t ((total_modular_unitary b)%:VF ^+ (bseq2ord j)) v.
Proof. exact: MultiplexerEt. Qed.

Variable x : expression nat.

Definition prefix :=
  Sequence (Initialize (control_register qr) (EConst (zero_state (QArray t QBool))))
  (Sequence (Unitary (control_register qr) (EConst all_hadamards))
  (Sequence (Initialize (target_register qr) (EConst (zero_state (QArray L QBool))))
  (Sequence (Unitary (target_register qr) (EConst one_preparation))
  (Sequence (Unitary qr (EApp (EConst controlled_powers) x))
    (Unitary (control_register qr) (EConst [unitary of (ClassicalFourier.tuple_fourier t)^A])))))).

Definition prefix_action s : 'SO(Hq) :=
  ((((liftfso (formso (tf2f (control_register qr) (control_register qr)
       (ClassicalFourier.tuple_fourier t)^A)) :o
     liftfso (formso (tf2f qr qr (controlled_powers (eval x s))))) :o
     liftfso (formso (tf2f (target_register qr) (target_register qr) one_preparation))) :o
     liftfso (initialso (tv2v (target_register qr) (zero_state (QArray L QBool))))) :o
     liftfso (formso (tf2f (control_register qr) (control_register qr) all_hadamards))) :o
     liftfso (initialso (tv2v (control_register qr) (zero_state (QArray t QBool)))).

Lemma prefix_execution s : execution prefix s s (prefix_action s).
Proof.
exact: (RunSequence (RunInitialize _ _ s)
  (RunSequence (RunUnitary _ _ s)
  (RunSequence (RunInitialize _ _ s)
  (RunSequence (RunUnitary _ _ s)
  (RunSequence (RunUnitary _ _ s) (RunUnitary _ _ s)))))).
Qed.

Lemma prefix_denote s m : denote prefix s m = point s (prefix_action s) m.
Proof. apply: execution_denote; exact: prefix_execution. Qed.

Lemma prefix_channel s : prefix_action s \is cptp.
Proof. exact: execution_channel (prefix_execution s). Qed.

Definition printed_result (bs : t.-tuple bool) :=
  ClassicalShorArithmetic.printed_postprocess (bseq2ord bs) (2 ^ t)%N.

Definition order_finding
  (measured : variable (QType (QArray t QBool))) (result : variable (COption CNat)) :=
  Sequence prefix
  (Sequence (Measure measured (control_register qr)
    (EConst [QM of @tmeas (eval_qtype (QArray t QBool))]))
    (Assign result (EApp (EConst printed_result) (EVar measured)))).

End Program.
End ClassicalOrderFinding.


Module ClassicalShorOrderEvent.
(* Failure means equal component order valuations; see PROOF_NOTES.md. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import ClassicalShorGroupCounting.

Lemma logn2_eq0 n : 0 < n -> (logn 2 n == 0) = odd n.
Proof. by move=>Hn; rewrite eqn0Ngt logn_gt0 mem_primes Hn /= dvdn2 negbK. Qed.

Section Components.
Variables (I : finType) (G : finGroupType) (H : I -> finGroupType).
Variable i0 : I.
Variable red : forall i, {morphism [set: G] >-> H i}.
Hypothesis red_joint_injective :
  forall x y : G, (forall i, red i x = red i y) -> x = y.
Variable zi : forall i, H i.
Hypothesis zi_neq1 : forall i, zi i != 1%g.
Hypothesis roots_two : forall i (y : H i),
  (y ^+ 2)%g = 1%g -> y = 1%g \/ y = zi i.
Variable z : G.
Hypothesis red_z : forall i, red i z = zi i.

Local Open Scope group_scope.

Lemma component_order_dvd i (x : G) : (#[red i x] %| #[x])%N.
Proof. by rewrite order_dvdn -morphX ?inE // expg_order morph1. Qed.

Lemma component_valuation_le i (x : G) :
  (logn 2 #[red i x] <= logn 2 #[x])%N.
Proof. exact: dvdn_leq_log (fingroup.order_gt0 x) (component_order_dvd i x). Qed.

Lemma odd_component_valuation (x : G) : odd #[x] ->
  forall i, logn 2 #[red i x] = 0%N.
Proof.
move=>Hx i; apply/eqP; rewrite logn2_eq0 ?fingroup.order_gt0 //.
exact: dvdn_odd (component_order_dvd i x) Hx.
Qed.

Lemma half_component_square i (x : G) : ~~ odd #[x] ->
  (red i (x ^+ (#[x] %/ 2))) ^+ 2 = 1.
Proof.
move=>Hx; have H2 : (2 %| #[x])%N by rewrite dvdn2.
rewrite -morphX ?inE // -expgM (divnK H2) expg_order morph1.
by [].
Qed.

Lemma half_component_is_one i (x : G) : ~~ odd #[x] ->
  (red i (x ^+ (#[x] %/ 2)) == 1) =
    (logn 2 #[red i x] < logn 2 #[x])%N.
Proof.
move=>Hx; have H2 : (2 %| #[x])%N by rewrite dvdn2.
rewrite morphX ?inE // -order_dvdn.
exact: dvdn_half_logn (fingroup.order_gt0 x) (component_order_dvd i x) H2.
Qed.

Lemma half_component_is_involution i (x : G) : ~~ odd #[x] ->
  (red i (x ^+ (#[x] %/ 2)) == zi i) =
    (logn 2 #[red i x] == logn 2 #[x]).
Proof.
move=>Hx.
have Hle := component_valuation_le i x.
have Hhalf := half_component_is_one i Hx.
case: (roots_two (half_component_square i Hx))=>E.
- have Hlt : (logn 2 #[red i x] < logn 2 #[x])%N.
    by move: Hhalf; rewrite E eqxx=> <-.
  by rewrite E eq_sym (negbTE (zi_neq1 i)) (ltn_eqF Hlt).
- have Hlt : (logn 2 #[red i x] < logn 2 #[x])%N = false.
    by move: Hhalf; rewrite E (negbTE (zi_neq1 i))=> <-.
  have Heq : logn 2 #[red i x] = logn 2 #[x].
    apply/eqP; by move: Hle; rewrite leq_eqVlt Hlt orbF.
  by rewrite E Heq !eqxx.
Qed.

Lemma component_valuation_reaches (x : G) : ~~ odd #[x] ->
  exists i, logn 2 #[red i x] = logn 2 #[x].
Proof.
move=>Hx.
have H2 : (2 %| #[x])%N by rewrite dvdn2.
have Hex : [exists i, logn 2 #[red i x] == logn 2 #[x]].
  case: (boolP [exists i, logn 2 #[red i x] == logn 2 #[x]])
    =>[//|/existsPn Hnone].
  have Ehalf : x ^+ (#[x] %/ 2) = 1.
    apply: red_joint_injective=>i; rewrite morph1; apply/eqP.
    rewrite half_component_is_one // ltn_neqAle Hnone andTb.
    exact: component_valuation_le.
  have Hr : (#[x] %| #[x] %/ 2)%N by rewrite order_dvdn Ehalf eqxx.
  by move: Hr; rewrite dvdn_half_logn ?fingroup.order_gt0 ?dvdnn // ltnn.
case/existsP: Hex=>i /eqP Hi; by exists i.
Qed.

Theorem failure_iff_equal_valuations (x : G) :
  odd #[x] || (x ^+ (#[x] %/ 2) == z) =
    [forall i, logn 2 #[red i x] == logn 2 #[red i0 x]].
Proof.
case Hodd: (odd #[x]).
- rewrite /=; apply/esym/forallP=>i.
  by rewrite !odd_component_valuation.
- have Heven : ~~ odd #[x] by rewrite Hodd.
  rewrite /=; apply/idP/idP.
  + move=>/eqP E; apply/forallP=>i.
    have Ei : logn 2 #[red i x] = logn 2 #[x].
      apply/eqP; by rewrite -half_component_is_involution // E red_z eqxx.
    have E0 : logn 2 #[red i0 x] = logn 2 #[x].
      apply/eqP; by rewrite -half_component_is_involution // E red_z eqxx.
    by rewrite Ei E0.
  + move=>/forallP Hall; apply/eqP.
    have [j Hj] := component_valuation_reaches Heven.
    have E0 : logn 2 #[red i0 x] = logn 2 #[x].
      by move/eqP: (Hall j); rewrite Hj=> ->.
    apply: red_joint_injective=>i; rewrite red_z; apply/eqP.
    by rewrite half_component_is_involution // (eqP (Hall i)) E0 eqxx.
Qed.

End Components.
End ClassicalShorOrderEvent.


Module ClassicalShorPrimePower.
(* Odd-prime-power square roots for classical paper Lemma 7.2(2).
   The prior mathematical argument is in PROOF_NOTES.md. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Section NaturalRoots.
Variables p e : nat.
Hypotheses (prime_p : prime p) (odd_p : odd p) (positive_e : 0 < e).
Let q := p ^ e.

Lemma modulus_gt2 : 2 < q.
Proof.
apply: leq_trans (odd_prime_gt2 odd_p prime_p) _.
rewrite /q -{1}(expn1 p) leq_exp2l //; exact: prime_gt1.
Qed.

Lemma modulus_positive : 0 < q.
Proof. exact: ltn_trans (ltn0Sn 1) modulus_gt2. Qed.

Lemma roots_distinct : (1 == q.-1 %[mod q]) = false.
Proof.
have Hq1 : 1 < q := ltnW modulus_gt2.
have Hpred : q.-1 < q by rewrite ltn_predL modulus_positive.
rewrite (modn_small Hq1) (modn_small Hpred).
apply: ltn_eqF; by rewrite ltn_predRL; exact: modulus_gt2.
Qed.

Lemma root_representative s : s < q -> s ^ 2 == 1 %[mod q] ->
  s = 1 \/ s = q.-1.
Proof.
move=>Hsq Hroot.
have Hq1 : 1 < q := ltnW modulus_gt2.
have Hs0 : 0 < s.
  apply/negPn/negP=>Hs; have Es : s = 0 by move: Hs; rewrite -eqn0Ngt=>/eqP.
  by move: Hroot; rewrite Es exp0n // mod0n (modn_small Hq1).
have Hs1 : 1 <= s := Hs0.
have Hs2 : 1 <= s ^ 2 by rewrite -[1](exp1n 2) leq_sqr.
have D : q %| (s - 1) * (s + 1).
  by rewrite -subn_sqr exp1n -(eqn_mod_dvd q Hs2).
case Hminus: (p %| s - 1).
- have Hplus : ~~ (p %| s + 1).
    apply/negP=>Hplus.
    have D2 : p %| 2.
      have := dvdn_sub Hplus Hminus.
      by rewrite subnBA // -addnA addKn.
    by move: D2; rewrite (gtnNdvd (isT : 0 < 2) (odd_prime_gt2 odd_p prime_p)).
  have C : coprime q (s + 1).
    by rewrite /q coprime_pexpl // prime_coprime.
  have Dm : q %| s - 1 by move: D; rewrite Gauss_dvdl.
  left; have Z : s - 1 = 0.
    apply/eqP; apply/negPn/negP=>Hnz.
    have Hm : 0 < s - 1 by rewrite lt0n.
    have Hsmall : s - 1 < q := leq_ltn_trans (leq_subr 1 s) Hsq.
    by move: Dm; rewrite (gtnNdvd Hm Hsmall).
  by rewrite -(subnK Hs1) Z.
- have C : coprime q (s - 1).
    by rewrite /q coprime_pexpl // prime_coprime // Hminus.
  have Dp : q %| s + 1 by move: D; rewrite Gauss_dvdr.
  have Hplus : 0 < s + 1 by rewrite addn1.
  have Eq : s + 1 = q.
    apply/eqP; rewrite eqn_leq; apply/andP; split.
    + by rewrite addn1.
    + exact: dvdn_leq Hplus Dp.
  right; by rewrite -Eq addn1.
Qed.

Theorem square_roots_mod x : x ^ 2 == 1 %[mod q] ->
  (x == 1 %[mod q]) || (x == q.-1 %[mod q]).
Proof.
move=>Hx.
have Hr : (x %% q) ^ 2 == 1 %[mod q] by rewrite modnXm.
have Hlt : x %% q < q by rewrite ltn_mod modulus_positive.
case: (root_representative Hlt Hr)=>E; apply/orP.
- left; by rewrite E modn_small //; exact: ltnW modulus_gt2.
- right; have Hpred : q.-1 < q by rewrite ltn_predL modulus_positive.
  by rewrite E (modn_small Hpred).
Qed.

End NaturalRoots.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma unit_negative_one_proof n : (-1 : 'Z_n) \is a GRing.unit.
Proof. by rewrite unitrN unitr1. Qed.
Definition negative_one n : {unit 'Z_n} :=
  @FinRing.Unit _ (-1 : 'Z_n) (unit_negative_one_proof n).

Lemma negative_one_nat n : (1 < n)%N -> (val (negative_one n) : nat) = n.-1.
Proof.
case: n=>[//|[//|n]] _.
by rewrite /negative_one /= /Zp_trunc /=
  (modn_small (isT : (1 < n.+2)%N)) subn1 modn_small.
Qed.

Lemma unit_one_nat n : (val (1%g : {unit 'Z_n}) : nat) = 1%N.
Proof. by change ((1 %% (Zp_trunc n).+2)%N = 1%N); rewrite modn_small. Qed.

Lemma unit_power_nat n (u : {unit 'Z_n}) k : (1 < n)%N ->
  (val (u ^+ k)%g : nat) = ((val u : nat) ^ k %% n)%N.
Proof.
move=>Hn; rewrite unit_Zp_expg /=.
exact: (congr1 (fun d => ((val u : nat) ^ k %% d)%N) (Zp_cast Hn)).
Qed.

Lemma negative_one_square n : ((negative_one n) ^+ 2 = 1)%g.
Proof. by apply/val_inj; rewrite FinRing.val_unitX /= expr2 mulrNN mulr1. Qed.

Lemma negative_one_distinct n : (2 < n)%N -> negative_one n != 1%g.
Proof.
move=>Hn; apply/negP=>/eqP E.
have En := congr1 (fun u : {unit 'Z_n} => (val u : nat)) E.
rewrite negative_one_nat ?(ltnW Hn) // unit_one_nat in En.
have Hpred : (1 < n.-1)%N by rewrite ltn_predRL.
by move: Hpred; rewrite En.
Qed.

Local Open Scope group_scope.

Section UnitRoots.
Variables p e : nat.
Hypotheses (prime_p : prime p) (odd_p : odd p) (positive_e : (0 < e)%N).
Let q := (p ^ e)%N.

Lemma unit_modulus_gt2 : (2 < q)%N.
Proof. exact: modulus_gt2 prime_p odd_p positive_e. Qed.

Theorem unit_square_roots (u : {unit 'Z_q}) : (u ^+ 2 = 1)%g ->
  u = 1%g \/ u = negative_one q.
Proof.
move=>Hu; have Hq1 : (1 < q)%N := ltnW unit_modulus_gt2.
have Huq : ((val u : nat) < q)%N.
  apply: leq_trans (valP (val u)) _.
  by rewrite (Zp_cast Hq1).
have Hnat : ((val u : nat) ^ 2 == 1 %[mod q])%N.
  apply/eqP; rewrite (modn_small Hq1).
  have := congr1 (fun v : {unit 'Z_q} => (val v : nat)) Hu.
  by rewrite unit_power_nat // unit_one_nat.
case: (@root_representative p e prime_p odd_p positive_e (val u) Huq Hnat)=>E.
- left; apply/val_inj; apply/val_inj.
  change ((val u : nat) = (val (1%g : {unit 'Z_q}) : nat)).
  by rewrite unit_one_nat.
- right; apply/val_inj; apply/val_inj.
  change ((val u : nat) = (val (negative_one q) : nat)).
  by rewrite negative_one_nat.
Qed.


Theorem prime_power_fiber_half k :
  (2 * #|[set u : {unit 'Z_q} | logn 2 #[u] == k]| <= #|{: {unit 'Z_q}}|)%N.
Proof.
apply: (@ClassicalShorGroupCounting.order_valuation_fiber_half
  _ (negative_one q)).
- exact: units_Zp_abelian.
- apply: negative_one_distinct; exact: unit_modulus_gt2.
- exact: negative_one_square.
- exact: unit_square_roots.
Qed.

End UnitRoots.
End ClassicalShorPrimePower.


Module ClassicalOrderFindingState.
(* Exact finite Fourier amplitudes for the printed order-finding circuit. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalModularUnitary ClassicalOrderFinding.
Section Circuit.
Variables (N L t : nat).
Hypothesis HN : (1 < N)%N.
Hypothesis capacity : (N <= 2 ^ L)%N.

Definition controlled_state b :=
  @controlled_powers N L t HN capacity b
    (uniformtv ⊗t (@one_state N L HN capacity : 'Hs(L.-tuple bool))).

Definition inverse_fourier_left : 'FU('Hs((t.-tuple bool) * (L.-tuple bool))%type) :=
  [unitary of (ClassicalFourier.tuple_fourier t)^A ⊗f (\1 : 'FU('Hs(L.-tuple bool)))].

Definition output_state b := inverse_fourier_left (controlled_state b).

Lemma controlled_state_normal b : [< controlled_state b; controlled_state b >] = 1.
Proof. by rewrite /controlled_state isof_dot tentv_dot !ns_dot mulr1. Qed.
HB.instance Definition _ b := isNormalState.Build _ (controlled_state b)
  (controlled_state_normal b).

Lemma output_state_normal b : [< output_state b; output_state b >] = 1.
Proof. by rewrite /output_state isof_dot ns_dot. Qed.
HB.instance Definition _ b := isNormalState.Build _ (output_state b)
  (output_state_normal b).

Theorem controlled_stateE b : coprime b N -> controlled_state b =
  (sqrtC 2%:R ^- t) *:
    \sum_(j : t.-tuple bool) (''j ⊗t
      ''(@residue_bits N (modulus_positive HN) L capacity (b ^ (bseq2ord j))%N)).
Proof.
move=>Hb; rewrite /controlled_state uniformtvE linearZl /= linear_sumlz /=
  linearZ /= linear_sum /= card_tuple card_bool natrX sqrtCX_nat.
congr (_ *: _); apply: eq_bigr=>j _.
rewrite controlled_powersE (@total_modular_unitaryE N L HN capacity b Hb) /one_state /one_bits
  modular_power_residue muln1.
by [].
Qed.

Lemma inverse_fourier_coefficient (m j : t.-tuple bool) :
  [< ''m; (ClassicalFourier.tuple_fourier t)^A ''j >] =
  (sqrtC 2%:R ^- t) *
    expip (- (2%:R * (bseq2ord m * bseq2ord j)%:R / 2%:R ^+ t)).
Proof.
rewrite adj_dotEr /ClassicalFourier.tuple_fourier PUnitaryE -conj_dotp
  ClassicalPhaseEstimation.fourier_coefficient rmorphM /=
  geC0_conj ?invr_ge0 ?exprn_ge0 ?sqrtC_ge0 // -expipNC.
by [].
Qed.

Theorem output_amplitude b (m : t.-tuple bool) (y : L.-tuple bool) :
  coprime b N ->
  [< ''m ⊗t ''y; output_state b >] =
  (sqrtC 2%:R ^- t)^+2 *
    \sum_(j : t.-tuple bool)
      expip (- (2%:R * (bseq2ord m * bseq2ord j)%:R / 2%:R ^+ t)) *
      (y == @residue_bits N (modulus_positive HN) L capacity (b ^ (bseq2ord j))%N)%:R.
Proof.
move=>Hb; rewrite /output_state (controlled_stateE Hb) linearZ /= linear_sum /=
  dotpZr dotp_sumr !mulr_sumr.
apply: eq_bigr=>j _.
rewrite /inverse_fourier_left tentf_apply lfunE tentv_dot
  inverse_fourier_coefficient onb_dot.
by rewrite expr2 !mulrA.
Qed.

Definition outcome_probability b (m : t.-tuple bool) : C :=
  \sum_(y : L.-tuple bool) `|[< ''m ⊗t ''y; output_state b >]|^+2.

Theorem outcome_probabilityE b m : coprime b N -> outcome_probability b m =
  \sum_(y : L.-tuple bool)
    `| (sqrtC 2%:R ^- t)^+2 *
      \sum_(j : t.-tuple bool)
        expip (- (2%:R * (bseq2ord m * bseq2ord j)%:R / 2%:R ^+ t)) *
        (y == @residue_bits N (modulus_positive HN) L capacity (b ^ (bseq2ord j))%N)%:R |^+2.
Proof. move=>Hb; apply: eq_bigr=>y _; by rewrite output_amplitude. Qed.

End Circuit.
End ClassicalOrderFindingState.


Module ClassicalOrderFindingFailure.
(* Actual printed command cannot return denominators above two.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage CQAssertion CQPredicate CQHoare ClassicalOrderFinding ClassicalPostprocessCounterexample.
Local Notation Hq := 'H[msys]_finset.setT.

Definition result_is (result : variable (COption CNat)) (d : nat) :
    @semantic_assertion cmem Hq :=
  mask (fun s => (s.[result])%M == Some d) semantic_top.

Lemma printed_result_ne t (bs : t.-tuple bool) d : (2 < d)%N ->
  @printed_result t bs != Some d.
Proof.
move=>Hd; apply/negP=>/eqP E.
have Hb := printed_denominator_at_most_two (ltn_ord (bseq2ord bs)) E.
by move: Hd; rewrite ltnNge Hb.
Qed.

Lemma printed_assignment_pre_zero total t
    (measured : variable (QType (QArray t QBool)))
    (result : variable (COption CNat)) d : (2 < d)%N ->
  pre total (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
    (result_is result d) = semantic_bottom.
Proof.
move=>Hd; apply/funext=>s; apply/val_inj.
change ((pre total (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
  (result_is result d) s : 'End(Hq)) = 0).
rewrite /pre CQPrimitive.assign_pre /result_is /mask get_set_eq /eval /=.
by rewrite (negbTE (printed_result_ne _ Hd)).
Qed.

Section Program.
Variables (N L t : nat).
Hypothesis HN : (1 < N)%N.
Hypothesis capacity : (N <= 2 ^ L)%N.
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).
Variable x : expression nat.
Variable measured : variable (QType (QArray t QBool)).
Variable result : variable (COption CNat).

Theorem order_finding_wp_zero d : (2 < d)%N ->
  pre true (@order_finding N L t HN capacity qr x measured result)
    (result_is result d) = semantic_bottom.
Proof.
move=>Hd; rewrite /order_finding pre_sequence pre_sequence
  (printed_assignment_pre_zero true measured result Hd).
by rewrite /pre /xp /= !wp_zero.
Qed.

Theorem order_finding_output_zero d (rho : @CQState.state cmem Hq) : (2 < d)%N ->
  expect (result_is result d)
    (CQHoare.run (@order_finding N L t HN capacity qr x measured result) rho) = 0.
Proof.
move=>Hd; rewrite /CQHoare.run -expect_wp.
change (expect (pre true (@order_finding N L t HN capacity qr x measured result)
  (result_is result d)) rho = 0).
by rewrite (order_finding_wp_zero Hd) expect_zero.
Qed.

Corollary order_finding_never_four (rho : @CQState.state cmem Hq) :
  expect (result_is result 4)
    (CQHoare.run (@order_finding N L t HN capacity qr x measured result) rho) = 0.
Proof. exact: order_finding_output_zero (isT : (2 < 4)%N). Qed.

End Program.
End ClassicalOrderFindingFailure.


Module ClassicalShorProgram.
(* Literal Table 6 Shor wrapper and partial factor-output safety.
   The mathematical argument is recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage CQAssertion CQPredicate CQHoare ClassicalShorArithmetic.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.

Section Uniform.
Variable N : nat.
Hypothesis modulus_nontrivial : (1 < N)%N.

Definition uniform_weights : {summable 'I_N.-1 -> C} :=
  Summable.build (fin_dom_summable (fun _ : 'I_N.-1 => ((N.-1%:R : C)^-1)%R)).
Definition uniform_mass : nat -> C :=
  sdlet_def (fun i : 'I_N.-1 => (val i).+1) uniform_weights.

Lemma uniform_mass_positive x : 0 <= uniform_mass x.
Proof.
rewrite /uniform_mass /sdlet_def fin_dom_sum.
apply: sumr_ge0=>i _; rewrite /sunit_def /uniform_weights /=.
by case: eqP=>// _; rewrite invr_ge0 ler0n.
Qed.

Lemma uniform_mass_sum : sum uniform_mass = 1.
Proof.
rewrite /uniform_mass sdlet_sum /uniform_weights fin_dom_sum /=.
rewrite sumr_const card_ord -[X in X = 1]mulr_natr mulVf // pnatr_eq0.
by case: N modulus_nontrivial=>[|[|n]].
Qed.

Lemma uniform_mass_bound : `|sum uniform_mass| <= 1.
Proof. by rewrite uniform_mass_sum normr1. Qed.

Definition uniform_distribution : Distr nat :=
  VDistr.build (f := Summable.build
    (sdlet_summable_subproof (fun i : 'I_N.-1 => (val i).+1) uniform_weights))
    uniform_mass_positive uniform_mass_bound.

Definition uniform_probability : probability CNat :=
  @Probability CNat (EConst uniform_distribution) (fun _ => uniform_mass_sum).

Lemma uniform_mass_outside x : ~~ (0 < x < N)%N -> uniform_mass x = 0.
Proof.
move=>Hx; rewrite /uniform_mass /sdlet_def fin_dom_sum.
apply: big1=>i _; rewrite /sunit_def.
case: eqP=>// Ex; move: Hx; rewrite Ex /=.
have HN : N = N.-1.+1 by rewrite prednK //; exact: ltnW modulus_nontrivial.
by rewrite {2}HN ltnS (valP i).
Qed.

Lemma uniform_mass_inside x : (0 < x < N)%N ->
  uniform_mass x = ((N.-1%:R : C)^-1)%R.
Proof.
move=>/andP[Hx HxN].
have HN : N = N.-1.+1 by rewrite prednK //; exact: ltnW modulus_nontrivial.
have Hx1 : x = x.-1.+1 by rewrite prednK.
have Hk : (x.-1 < N.-1)%N.
  by rewrite -ltnS -Hx1 -HN.
pose k : 'I_N.-1 := Ordinal Hk.
rewrite /uniform_mass /sdlet_def fin_dom_sum (bigD1 k) //=.
rewrite /sunit_def -Hx1 eqxx /uniform_weights /=.
suff -> : \sum_(i : 'I_N.-1 | i != k)
  (if x == (val i).+1 then ((N.-1%:R : C)^-1)%R else 0) = 0 by rewrite addr0.
apply: big1=>i Hik; case: eqP=>// E.
have Eik : i = k by apply/val_inj; apply: succn_inj; rewrite -E -Hx1.
by move: Hik; rewrite Eik eqxx.
Qed.

Lemma uniform_probabilityE s x : probability_mass uniform_probability s x =
  if (0 < x < N)%N then ((N.-1%:R : C)^-1)%R else 0.
Proof.
change (uniform_mass x = if (0 < x < N)%N then ((N.-1%:R : C)^-1)%R else 0).
case E: (0 < x < N)%N.
- exact: uniform_mass_inside E.
- apply: uniform_mass_outside; by rewrite E.
Qed.


Definition direct_ordinal_weights : {summable 'I_N.-1 -> C} :=
  Summable.build (fin_dom_summable (fun i : 'I_N.-1 =>
    if (1 < gcdn (val i).+1 N)%N then ((N.-1%:R : C)^-1)%R else 0)).
Definition direct_mass : nat -> C :=
  sdlet_def (fun i : 'I_N.-1 => (val i).+1) direct_ordinal_weights.
Definition direct_probability : C := sum direct_ordinal_weights.

Lemma direct_massE a : direct_mass a =
  if (1 < gcdn a N)%N then uniform_mass a else 0.
Proof.
rewrite /direct_mass /uniform_mass /sdlet_def !fin_dom_sum.
case H: (1 < gcdn a N)%N.
- apply: eq_bigr=>i _; rewrite /sunit_def /direct_ordinal_weights /uniform_weights /=.
  by case: eqP=>// E; rewrite -E H.
- apply: big1=>i _; rewrite /sunit_def /direct_ordinal_weights /=.
  by case: eqP=>// E; rewrite -E H.
Qed.

Lemma direct_mass_sum : sum direct_mass = direct_probability.
Proof. by rewrite /direct_mass sdlet_sum. Qed.

Lemma direct_probability_ge0 : 0 <= direct_probability.
Proof.
rewrite /direct_probability /direct_ordinal_weights fin_dom_sum /=.
apply: sumr_ge0=>i _; case: ifP=>// _; by rewrite invr_ge0 ler0n.
Qed.

Lemma direct_probability_le1 : direct_probability <= 1.
Proof.
rewrite -(uniform_mass_sum) /uniform_mass sdlet_sum.
rewrite /direct_probability /direct_ordinal_weights /uniform_weights !fin_dom_sum /=.
apply: ler_sum=>i _; case: ifP=>// _; by rewrite invr_ge0 ler0n.
Qed.

Lemma direct_probability_sum : direct_probability =
  sum (fun a : nat => if (1 < gcdn a N)%N then uniform_mass a else 0).
Proof. rewrite -direct_mass_sum; apply: eq_sum=>a; exact: direct_massE. Qed.

End Uniform.

Section Wrapper.
Variables (N : nat) (modulus_nontrivial : (1 < N)%N).
Variables (x y y1 y2 z : variable CNat) (result : variable (COption CNat)).

Definition factor_post : cmem -> 'FO(Hq) :=
  mask (fun s => nontrivial_factor N (s.[y])%M) semantic_top.
Definition sampled_range : cmem -> 'FO(Hq) :=
  mask (fun s => (0 < (s.[x])%M < N)%N) semantic_top.
Definition gcd_expression : expression nat :=
  EApp (EConst (fun a => gcdn a N)) (EVar x).
Definition gcd_guard : bool_expr :=
  EApp (EConst (fun d => (1 < d)%N)) gcd_expression.
Definition factor_guard (a : variable CNat) : bool_expr :=
  EApp (EConst (nontrivial_factor N)) (EVar a).
Definition factor_checks : command :=
  Conditional (factor_guard y1) (Assign y (EVar y1))
    (Conditional (factor_guard y2) (Assign y (EVar y2)) Abort).
Definition half_power : expression nat :=
  EApp (EApp (EConst (fun a b : nat => (a ^ (b %/ 2))%N)) (EVar x)) (EVar z).
Definition root_guard : bool_expr :=
  EApp (EApp (EConst (fun b a : nat => ~~ odd b && ((a %% N)%N != N.-1)))
    (EVar z)) half_power.
Definition candidate_assignments : command :=
  Sequence (Assign y1 (EApp (EConst (fun a : nat => gcdn (a - 1)%N N)) half_power))
    (Assign y2 (EApp (EConst (fun a : nat => gcdn (a + 1)%N N)) half_power)).
Definition order_stage (OF : command) : command :=
  Sequence OF
    (Conditional (EApp (EConst (@isSome nat)) (EVar result))
      (Sequence (Assign z (EApp (EConst (odflt 0%N)) (EVar result)))
        (Conditional root_guard candidate_assignments Abort)) Abort).
Definition shor_with (OF : command) : command :=
  Sequence (Random x (uniform_probability modulus_nontrivial))
    (Conditional gcd_guard (Assign y gcd_expression)
      (Sequence (order_stage OF) factor_checks)).

Lemma valid_factor_assign total (p : pred cmem) e :
  (forall s, p s -> nontrivial_factor N (eval e s)) ->
  CQHoare.valid total (mask p semantic_top) (Assign y e) factor_post.
Proof.
move=>H; apply/(proj2 (valid_iff _ _ _ _))=>s.
rewrite /pre CQPrimitive.assign_pre /factor_post /mask get_set_eq.
case E: (p s)=>/=; last exact: obsf_ge0.
by rewrite (H s E).
Qed.

Lemma valid_candidate a c :
  CQHoare.valid false semantic_top c factor_post ->
  CQHoare.valid false semantic_top
    (Conditional (factor_guard a) (Assign y (EVar a)) c) factor_post.
Proof.
move=>V; apply: valid_conditional.
- apply: valid_factor_assign=>s; by [].
- apply: (@CQHoare.valid_consequence false semantic_top factor_post
    (mask (predC (esem (factor_guard a))) semantic_top) factor_post c).
  + exact: semantic_le_top.
  + exact: semantic_le_refl.
  + exact: V.
Qed.

Lemma valid_factor_checks : CQHoare.valid false semantic_top factor_checks factor_post.
Proof.
apply: valid_candidate; apply: valid_candidate; exact: CQHoare.valid_abort_partial.
Qed.

Lemma uniform_sampling_range :
  CQHoare.valid false semantic_top
    (Random x (uniform_probability modulus_nontrivial)) sampled_range.
Proof.
apply/(proj2 (valid_iff _ _ _ _)).
have E : pre false (Random x (uniform_probability modulus_nontrivial)) sampled_range =
    pre false (Random x (uniform_probability modulus_nontrivial)) semantic_top.
  apply/funext=>s; apply/val_inj.
  change ((pre false (Random x (uniform_probability modulus_nontrivial)) sampled_range s : 'End(Hq)) =
    (pre false (Random x (uniform_probability modulus_nontrivial)) semantic_top s : 'End(Hq))).
  rewrite /pre !CQPrimitive.random_pre; apply: eq_sum=>a.
  rewrite /sampled_range /mask get_set_eq.
  case Ea: (0 < a < N)%N=>//.
  by rewrite uniform_probabilityE Ea !scale0r.
rewrite E /pre /xp /= wlp_top; exact: semantic_le_refl.
Qed.

Lemma immediate_gcd_factor a :
  (0 < a < N)%N -> (1 < gcdn a N)%N -> nontrivial_factor N (gcdn a N).
Proof.
move=>/andP[Ha HaN] Hg.
have Hga : (gcdn a N <= a)%N := dvdn_leq Ha (dvdn_gcdl a N).
by rewrite /nontrivial_factor Hg (leq_ltn_trans Hga HaN) dvdn_gcdr.
Qed.

Theorem shor_with_partial_safe OF :
  CQHoare.valid false semantic_top (shor_with OF) factor_post.
Proof.
apply: (@CQHoare.valid_sequence false _ sampled_range).
- exact: uniform_sampling_range.
- apply: valid_conditional.
  + apply/(proj2 (valid_iff _ _ _ _))=>s.
    rewrite /pre CQPrimitive.assign_pre /sampled_range /factor_post /mask get_set_eq.
    case Eg: (esem gcd_guard s)=>/=; last exact: obsf_ge0.
    case Ex: (0 < (s.[x])%M < N)%N=>/=; last exact: obsf_ge0.
    have Hg : (1 < gcdn (s.[x])%M N)%N := Eg.
    by rewrite /gcd_expression /eval /= (immediate_gcd_factor Ex Hg).
  + apply: (@CQHoare.valid_consequence false semantic_top factor_post
      (mask (predC (esem gcd_guard)) sampled_range) factor_post).
    * exact: semantic_le_top.
    * exact: semantic_le_refl.
    * apply: (@CQHoare.valid_sequence false _ semantic_top).
      -- exact: CQAuxiliary.valid_top.
      -- exact: valid_factor_checks.
Qed.

Theorem derives_shor_with OF : derives false semantic_top (shor_with OF) factor_post.
Proof. apply: derives_complete; exact: shor_with_partial_safe. Qed.


Definition direct_guard (s : cmem) :=
  (0 < (s.[x])%M < N)%N && (1 < gcdn (s.[x])%M N)%N.
Definition direct_assertion : cmem -> 'FO(Hq) := mask direct_guard semantic_top.
Definition direct_pre : cmem -> 'FO(Hq) :=
  pre true (Random x (uniform_probability modulus_nontrivial)) direct_assertion.

Lemma direct_preE s : (direct_pre s : 'End(Hq)) =
  direct_probability N *: (\1 : 'End(Hq)).
Proof.
rewrite /direct_pre /pre CQPrimitive.random_pre.
have E : (fun a => probability_mass (uniform_probability modulus_nontrivial) s a *:
    (direct_assertion (s.[x <- a])%M : 'End(Hq))) =
    (fun a => direct_mass N a *: (\1 : 'End(Hq))).
  apply/funext=>a.
  rewrite /direct_assertion /mask /direct_guard get_set_eq direct_massE.
  change ((@uniform_mass N a) *:
    ((if (0 < a < N)%N && (1 < gcdn a N)%N then semantic_top s
      else (0%:VF : 'FO(Hq))) : 'End(Hq)) =
    (if (1 < gcdn a N)%N then uniform_mass N a else 0) *: (\1 : 'End(Hq))).
  case Ha: (0 < a < N)%N=>/=.
  - by case: ifP=>_ /=; rewrite ?scaler0 ?scale0r.
  - rewrite (@uniform_mass_outside N modulus_nontrivial a) ?Ha //.
    by case: ifP=>_ /=; rewrite !scale0r.
rewrite E -direct_mass_sum.
symmetry; apply: (cvg_linearP_sum (x := direct_mass N)
  (f := fun a : C => a *: (\1 : 'End(Hq)))).
- by move=>a b c; rewrite scalerDl scalerA.
- exact: (summable_cvg (f := Summable.build
    (sdlet_summable_subproof (fun i : 'I_N.-1 => (val i).+1) (direct_ordinal_weights N)))).
Qed.

Lemma shor_with_direct_total OF :
  CQHoare.valid true direct_pre (shor_with OF) factor_post.
Proof.
apply: (@CQHoare.valid_sequence true _ direct_assertion).
- exact: pre_valid.
- apply: valid_conditional.
  + apply/(proj2 (valid_iff _ _ _ _))=>s.
    rewrite /pre CQPrimitive.assign_pre /direct_assertion /factor_post /mask
      /direct_guard get_set_eq.
    case Eg: (esem gcd_guard s)=>/=; last exact: obsf_ge0.
    have Hg : (1 < gcdn (s.[x])%M N)%N := Eg.
    rewrite Hg andbT.
    case Ex: (0 < (s.[x])%M < N)%N=>/=; last exact: obsf_ge0.
    by rewrite /gcd_expression /eval /= (immediate_gcd_factor Ex Hg).
  + apply/(proj2 (valid_iff _ _ _ _))=>s.
    rewrite /mask /direct_assertion /mask /direct_guard.
    change ((if ~~ esem gcd_guard s then
      (if (0 < (s.[x])%M < N)%N && (1 < gcdn (s.[x])%M N)%N
       then semantic_top s else (0%:VF : 'FO(Hq))) else (0%:VF : 'FO(Hq)))
       <= pre true (Sequence (order_stage OF) factor_checks) factor_post s).
    case Eg: (esem gcd_guard s)=>/=; first exact: obsf_ge0.
    have Hg : (1 < gcdn (s.[x])%M N)%N = false := Eg.
    rewrite Hg andbF; exact: obsf_ge0.
Qed.

Theorem derives_shor_with_direct OF : derives true direct_pre (shor_with OF) factor_post.
Proof. apply: derives_complete; exact: shor_with_direct_total. Qed.

Section ConcreteOrderFinding.
Variables (L t : nat) (register_capacity : (N <= 2^L)%N).
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).
Variable measured : variable (QType (QArray t QBool)).

Definition shor : command :=
  shor_with (@ClassicalOrderFinding.order_finding N L t modulus_nontrivial
    register_capacity qr (EVar x) measured result).

Theorem shor_partial_safe : CQHoare.valid false semantic_top shor factor_post.
Proof. exact: shor_with_partial_safe. Qed.

Theorem derives_shor : derives false semantic_top shor factor_post.
Proof. exact: derives_shor_with. Qed.


Theorem shor_direct_total : CQHoare.valid true direct_pre shor factor_post.
Proof. exact: shor_with_direct_total. Qed.

Theorem derives_shor_direct : derives true direct_pre shor factor_post.
Proof. exact: derives_shor_with_direct. Qed.

End ConcreteOrderFinding.

End Wrapper.
End ClassicalShorProgram.


Module ClassicalShorModularEvent.
(* Concrete distinguished-involution reduction for Lemma 7.2(2).
   See PROOF_NOTES.md for the prior mathematical argument. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import ClassicalShorCRT ClassicalShorPrimePower.

Lemma predecessor_mod_divisor N M :
  1 < N -> 1 < M -> M %| N -> N.-1 %% M = M.-1.
Proof.
move=>HN HM D.
have HM1 : M != 1 by rewrite eq_sym (ltn_eqF HM).
by rewrite modn_pred ?HM1 ?(ltnW HN) ?D.
Qed.

Theorem unit_reduce_negative_one N M (HN : 1 < N) (HM : 1 < M) (D : M %| N) :
  @unit_reduce N M HN HM D (negative_one N) = negative_one M.
Proof.
have EN : unit_value (negative_one N) = N.-1 := @negative_one_nat N HN.
have EM : unit_value (negative_one M) = M.-1 := @negative_one_nat M HM.
apply: unit_value_inj; rewrite unit_reduce_value EN EM.
exact: predecessor_mod_divisor HN HM D.
Qed.
End ClassicalShorModularEvent.


Module ClassicalOrderFindingExecution.
(* Concrete source prepares the exact order-finding output state.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmSemantics ClassicalRegisterTensor ClassicalPhaseProgram ClassicalOrderFinding ClassicalOrderFindingState.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma all_hadamards_zero t :
  @all_hadamards t (zero_state (QArray t QBool) : 'Ht (QArray t QBool)) = uniformtv.
Proof.
change (tentf_tuple (fun _ : 'I_t => (Hadamard : 'End('Hs bool)))
  ''(nseq_tuple t false) = uniformtv).
rewrite t2tv_tuple tentf_tuple_apply -uniformtv_tuple.
apply: eq_tentv_tuple=>i; by rewrite tnth_nseq Hadamard0 uniformtv_bool.
Qed.

Lemma measured_projector_probability (t L : nat)
    (psi : 'Ht (QPair (QArray t QBool) (QArray L QBool))) (m : t.-tuple bool) :
  [< psi; ([> ''m; ''m <] ⊗f (\1 : 'End('Hs(L.-tuple bool)))) psi >] =
  \sum_(y : L.-tuple bool) `|[< ''m ⊗t ''y; psi >]|^+2.
Proof.
rewrite -(sumonb_out (@t2tv (L.-tuple bool))) tentf_sumr sum_lfunE dotp_sumr.
apply: eq_bigr=>y _.
rewrite tentv_out outpE dotpZr -(conj_dotp (''m ⊗t ''y) psi).
by rewrite -sqr_normc.
Qed.

Section Program.
Variables (N L t : nat).
Hypothesis HN : (1 < N)%N.
Hypothesis capacity : (N <= 2 ^ L)%N.
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).
Variable x : expression nat.

Lemma initial_pair_reverse (a : 'Ht (QArray t QBool)) (b : 'Ht (QArray L QBool)) :
  liftfso (initialso (tv2v (target_register qr) b)) :o
    liftfso (initialso (tv2v (control_register qr) a)) =
  liftfso (initialso (tv2v qr (a ⊗t b))).
Proof.
rewrite (liftfso_compC _ _); first by rewrite disjoint_sym; exact: pair_register_disjoint.
exact: initial_register_pair.
Qed.

Theorem prefix_actionE s : @prefix_action N L t HN capacity qr x s =
  liftfso (initialso (tv2v qr (@output_state N L t HN capacity (eval x s)))).
Proof.
rewrite /prefix_action -!comp_soA.
rewrite -liftfso_comp formso_initial tf2f_apply all_hadamards_zero.
rewrite (comp_soA _ (liftfso (initialso (tv2v (target_register qr)
  (zero_state (QArray L QBool)))))) -liftfso_comp formso_initial tf2f_apply one_preparationE.
rewrite initial_pair_reverse.
rewrite -liftfso_comp formso_initial tf2f_apply.
rewrite /control_register channel_register_left -liftfso_comp formso_initial tf2f_apply.
by [].
Qed.

Theorem prefix_prepares s :
  execution (@prefix N L t HN capacity qr x) s s
    (liftfso (initialso (tv2v qr (@output_state N L t HN capacity (eval x s))))).
Proof. rewrite -prefix_actionE; exact: prefix_execution. Qed.

Variable measured : variable (QType (QArray t QBool)).
Variable result : variable (COption CNat).

Lemma postprocess_preserves_outcome total (m : t.-tuple bool) :
  CQHoare.pre total
    (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
    (ClassicalPhaseCorrectness.outcome_post measured m) =
  ClassicalPhaseCorrectness.outcome_post measured m.
Proof.
apply/funext=>s; apply/val_inj.
change ((CQHoare.pre total
  (Assign result (EApp (EConst (@printed_result t)) (EVar measured)))
  (ClassicalPhaseCorrectness.outcome_post measured m) s : 'End(Hq)) =
  (ClassicalPhaseCorrectness.outcome_post measured m s : 'End(Hq))).
rewrite /CQHoare.pre CQPrimitive.assign_pre
  /ClassicalPhaseCorrectness.outcome_post get_set_net //.
Qed.

Theorem order_finding_outcome_pre total (m : t.-tuple bool) s :
  (CQHoare.pre total (@order_finding N L t HN capacity qr x measured result)
    (ClassicalPhaseCorrectness.outcome_post measured m) s : 'End(Hq)) =
  (@outcome_probability N L t HN capacity (eval x s) m) *: \1.
Proof.
rewrite /order_finding CQHoare.pre_sequence.
rewrite [CQHoare.pre _ (Sequence (Measure _ _ _) _) _]CQHoare.pre_sequence
  postprocess_preserves_outcome.
rewrite /CQHoare.pre.
rewrite (execution_pre _ _ (prefix_prepares s)).
rewrite ClassicalPhaseCorrectness.measurement_outcome_pre.
rewrite /control_register -(lift_register_left qr [> ''m; ''m <])
  liftfso_dual liftfsoEf dualso_initialE tf2f_apply tv2v_dot
  measured_projector_probability linearZ /= liftf_lf1.
by [].
Qed.

End Program.
End ClassicalOrderFindingExecution.


Module ClassicalShorCounting.
(* Concrete failure count for Lemma 7.2(2); see PROOF_NOTES.md. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import ClassicalShorFactorization ClassicalShorCRT ClassicalShorCRTProduct ClassicalShorPrimePower ClassicalShorModularEvent ClassicalShorOrderEvent ClassicalShorProductCounting.
Local Open Scope group_scope.

Definition unit_failure N (u : {unit 'Z_N}) :=
  odd #[u] || (u ^+ (#[u] %/ 2) == negative_one N).

Definition unit_success N (u : {unit 'Z_N}) :=
  ~~ odd #[u] && (u ^+ (#[u] %/ 2) != negative_one N).

Lemma unit_successE N (u : {unit 'Z_N}) : unit_success u = ~~ unit_failure u.
Proof. by rewrite /unit_success /unit_failure negb_or. Qed.

Lemma bijective_pred_card (A B : finType) (f : A -> B) (P : pred B) :
  bijective f -> #|[pred a : A | P (f a)]| = #|P|.
Proof.
move=>Hf.
have E : #|[pred a : A | P (f a)]| = #|f @^-1: P|.
  by apply: eq_card=>a; rewrite !inE.
rewrite E; apply: on_card_preimset; exact: onW_bij Hf.
Qed.

Section Modulus.
Variable N : nat.
Hypotheses (HN : (1 < N)%N) (odd_N : odd N).

Let I := (Finite.clone (factor_index N) _).
Let q (i : I) := factor_modulus i.
Let Hq (i : I) := factor_modulus_gt1 i.
Let productE := esym (factorization HN).
Let Hi (i : I) := (FinGroup.clone {unit 'Z_(q i)} _).
Let Xi (i : I) := (Finite.clone {unit 'Z_(q i)} _).
Let i0 : I := first_factor HN.

Definition factor_reduction (i : I) := @reduction I q N HN Hq productE i.
Definition factor_tuple := @unit_tuple I q N HN Hq productE.
Definition order_label (i : I) (u : Xi i) := logn 2 #[u].

Lemma factor_tuple_bijective : bijective factor_tuple.
Proof.
exact: (@unit_tuple_bijective I q N HN Hq (@factor_moduli_coprime N) productE).
Qed.

Lemma factor_reduction_jointly_injective (u v : {unit 'Z_N}) :
  (forall i, factor_reduction i u = factor_reduction i v) -> u = v.
Proof.
exact: (@reductions_jointly_injective I q N HN Hq
  (@factor_moduli_coprime N) productE u v).
Qed.

Lemma factor_involution_nontrivial (i : I) : negative_one (q i) != 1.
Proof.
apply: negative_one_distinct.
exact: modulus_gt2 (factor_prime_is_prime i) (factor_prime_odd i odd_N)
  (factor_exponent_positive i).
Qed.

Lemma factor_roots_two (i : I) (u : Hi i) : u ^+ 2 = 1 ->
  u = 1 \/ u = negative_one (q i).
Proof.
exact: (@unit_square_roots (factor_prime i) (factor_exponent i)
  (factor_prime_is_prime i) (factor_prime_odd i odd_N)
  (factor_exponent_positive i) u).
Qed.

Lemma factor_reduction_negative_one (i : I) :
  factor_reduction i (negative_one N) = negative_one (q i).
Proof. exact: unit_reduce_negative_one. Qed.

Lemma failure_diagonalE (u : {unit 'Z_N}) :
  unit_failure u = natural_diagonal order_label i0 (factor_tuple u).
Proof.
rewrite /unit_failure /natural_diagonal /order_label.
transitivity [forall i : I, logn 2 #[factor_reduction i u] ==
  logn 2 #[factor_reduction i0 u]].
- exact: (@failure_iff_equal_valuations I (FinGroup.clone {unit 'Z_N} _) Hi i0
    factor_reduction factor_reduction_jointly_injective
    (fun i => negative_one (q i)) factor_involution_nontrivial factor_roots_two
    (negative_one N) factor_reduction_negative_one u).
- apply: eq_forallb=>i; by rewrite /factor_tuple !unit_tupleE.
Qed.

Lemma failure_card : #|@unit_failure N| = #|natural_diagonal order_label i0|.
Proof.
rewrite -(bijective_pred_card (natural_diagonal order_label i0) factor_tuple_bijective).
exact: eq_card failure_diagonalE.
Qed.

Lemma factor_order_fiber_half (i : I) k :
  (2 * #|[pred u : Xi i | @order_label i u == k]| <= #|Xi i|)%N.
Proof.
have H := @prime_power_fiber_half (factor_prime i) (factor_exponent i)
  (factor_prime_is_prime i) (factor_prime_odd i odd_N) (factor_exponent_positive i) k.
have E : #|[pred u : Xi i | @order_label i u == k]| =
    #|[set u : {unit 'Z_(q i)} | logn 2 #[u] == k]|.
  by apply: eq_card=>u; rewrite !inE.
by rewrite E.
Qed.

Theorem failure_count_bound :
  (2 ^ (size (primes N)).-1 * #|@unit_failure N| <= totient N)%N.
Proof.
have Hhalf : forall i k, i != i0 ->
    (2 * #|[pred u : Xi i | @order_label i u == k]| <= #|Xi i|)%N.
  move=>i k _; exact: factor_order_fiber_half.
have H := @natural_diagonal_half_bound I Xi order_label i0 Hhalf.
have Ec : #|{: {dffun forall i : I, Xi i}}| = totient N.
  rewrite -(bij_eq_card factor_tuple_bijective) -cardsT -/(units_Zp N).
  by rewrite card_units_Zp //; exact: ltnW HN.
by move: H; rewrite /I card_ord Ec -failure_card.
Qed.

End Modulus.
End ClassicalShorCounting.


Module ClassicalShorSampleEvent.
(* The paper's natural-number order event on actual uniform samples.
   See PROOF_NOTES.md. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import ClassicalSemantics.
Import ClassicalShorCRT ClassicalShorPrimePower ClassicalShorCounting.
Local Open Scope group_scope.
Local Open Scope nat_scope.

Section Modulus.
Variable N : nat.
Hypothesis HN : 1 < N.

Definition natural_unit a : {unit 'Z_N} :=
  insubd (1%g : {unit 'Z_N}) (a%:R : 'Z_N)%R.

Lemma natural_unit_value a : coprime N a -> unit_value (natural_unit a) = a %% N.
Proof.
move=>Ha; rewrite /natural_unit /unit_value val_insubd.
rewrite unitZpE // Ha.
exact: val_Zp_nat.
Qed.

Lemma natural_unitK (u : {unit 'Z_N}) : natural_unit (unit_value u) = u.
Proof.
apply: unit_value_inj.
by rewrite natural_unit_value ?unit_value_coprime // modn_small ?unit_value_lt.
Qed.

Definition natural_order a := #[natural_unit a].

Lemma natural_order_positive a : 0 < natural_order a.
Proof. exact: fingroup.order_gt0. Qed.

Lemma natural_power_value a k : coprime N a ->
  unit_value ((natural_unit a) ^+ k) = a ^ k %% N.
Proof.
move=>Ha; by rewrite (unit_value_power HN) natural_unit_value // modnXm.
Qed.

Theorem natural_order_dvd a k : coprime N a ->
  (natural_order a %| k) = (a ^ k == 1 %[mod N]).
Proof.
move=>Ha; rewrite /natural_order order_dvdn -(inj_eq (@unit_value_inj N)).
by rewrite natural_power_value // (unit_value_one HN) (modn_small HN).
Qed.

Lemma natural_order_power a : coprime N a -> a ^ natural_order a == 1 %[mod N].
Proof. by move=>Ha; rewrite -(natural_order_dvd _ Ha) dvdnn. Qed.

Lemma natural_order_minimal a k : coprime N a ->
  0 < k < natural_order a -> ~~ (a ^ k == 1 %[mod N]).
Proof.
move=>Ha /andP[Hk Hlt]; rewrite -(natural_order_dvd _ Ha).
apply/negP=>D; by move: Hlt; rewrite ltnNge (dvdn_leq Hk D).
Qed.

Definition natural_success a :=
  ~~ odd (natural_order a) &&
    ~~ (a ^ (natural_order a %/ 2) == N.-1 %[mod N]).

Theorem natural_success_unit (u : {unit 'Z_N}) :
  natural_success (unit_value u) = unit_success u.
Proof.
rewrite /natural_success /natural_order natural_unitK /unit_success.
rewrite -(inj_eq (@unit_value_inj N)) (unit_value_power HN).
have E : unit_value (negative_one N) = N.-1 := @negative_one_nat N HN.
have Hpred : N.-1 < N by rewrite ltn_predL; exact: ltnW HN.
by rewrite E (modn_small Hpred).
Qed.

End Modulus.
End ClassicalShorSampleEvent.


Module ClassicalShorProbability.
(* Numerical finite-probability corollary for Lemma 7.2(2).
   See PROOF_NOTES.md for the prior argument. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Import ClassicalSemantics.
Import ClassicalShorCounting.

Lemma finite_complement_ratio (F : numFieldType) (T : finType) (bad : pred T) d :
  (0 < d)%N -> (0 < #|{:T}|)%N -> (d * #|bad| <= #|{:T}|)%N ->
  (1 - 1 / d%:R <= (#|predC bad|)%:R / (#|{:T}|)%:R :> F).
Proof.
move=>Hd Hn Hcount.
have HdF : (0 : F) < d%:R by rewrite ltr0n.
have HnF : (0 : F) < (#|{:T}|)%:R by rewrite ltr0n.
have C : #|{:T}| = (#|predC bad| + #|bad|)%N.
  by rewrite addnC cardC.
rewrite ler_pdivlMr // mulrBl mul1r [d%:R^-1 * _]mulrC.
rewrite lerBlDr {1}C natrD mul1r lerD2l ler_pdivlMr //.
by rewrite -natrM mulnC ler_nat.
Qed.

Theorem uniform_unit_success_bound (F : numFieldType) N :
  (1 < N)%N -> odd N ->
  (1 - 1 / ((2 ^ (size (primes N)).-1)%N)%:R <=
   (#|@unit_success N|)%:R / (totient N)%:R :> F).
Proof.
move=>HN odd_N.
have HN0 : (0 < N)%N := ltnW HN.
have Ecard : #|{: {unit 'Z_N}}| = totient N.
  by rewrite -cardsT -/(units_Zp N) card_units_Zp.
have Hcard : (0 < #|{: {unit 'Z_N}}|)%N.
  by rewrite Ecard totient_gt0.
have Egood : #|predC (@unit_failure N)| = #|@unit_success N|.
  apply: eq_card=>u.
  change (~~ unit_failure u = unit_success u).
  exact: esym (unit_successE u).
have Hcount := @failure_count_bound N HN odd_N.
rewrite -Ecard in Hcount.
have Hd : (0 < 2 ^ (size (primes N)).-1)%N by rewrite expn_gt0.
have H := @finite_complement_ratio F [the finType of {unit 'Z_N}]
  (@unit_failure N) _ Hd Hcard Hcount.
by move: H; rewrite Ecard Egood.
Qed.

Lemma mixture_lower_bound (F : numFieldType) (lambda p c : F) :
  0 <= lambda -> 0 <= p -> p <= 1 -> 0 <= c -> c <= 1 ->
  p * c <= lambda + p * ((1 - lambda) * c).
Proof.
move=>Hlambda Hp0 Hp1 Hc0 Hc1.
have Hpc : p * c <= 1.
  by move: (ler_pM Hp0 Hc0 Hp1 Hc1); rewrite mul1r.
have Hd : 0 <= lambda * (1 - p * c).
  by apply: mulr_ge0=>//; rewrite subr_ge0.
have E : lambda + p * ((1 - lambda) * c) = p * c + lambda * (1 - p * c).
  ring.
by rewrite E lerDl.
Qed.
End ClassicalShorProbability.


Module ClassicalShorFactorExtraction.
(* Equation (20) for the actual arithmetic order-success event.
   See PROOF_NOTES.md; independent of the OrderFinding program. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import ClassicalSemantics.
Import ClassicalShorArithmetic ClassicalShorSampleEvent.

Section Modulus.
Variable N : nat.
Hypothesis HN : 1 < N.

Theorem natural_success_factor a : coprime N a -> natural_success N a ->
  nontrivial_factor N (gcdn (a ^ (natural_order N a %/ 2) - 1) N).
Proof.
move=>Ha /andP[Heven Hneg].
have Hr : 0 < natural_order N a := natural_order_positive N a.
have Dr : 2 %| natural_order N a by rewrite dvdn2.
have E : (natural_order N a %/ 2) * 2 = natural_order N a := divnK Dr.
have Hhalf0 : 0 < natural_order N a %/ 2.
  have Hp : 0 < (natural_order N a %/ 2) * 2 by rewrite E.
  by move: Hp; rewrite muln_gt0=>/andP[].
have Hhalf : natural_order N a %/ 2 < natural_order N a.
  exact: ltn_Pdiv (isT : 1 < 2) Hr.
have Hrange : 0 < natural_order N a %/ 2 < natural_order N a.
  by rewrite Hhalf0 Hhalf.
have Hmin := natural_order_minimal HN Ha Hrange.
have Hneq1 : a ^ (natural_order N a %/ 2) %% N != 1.
  by move: Hmin; rewrite (modn_small HN).
have Hpowercop : coprime N (a ^ (natural_order N a %/ 2)).
  exact: coprimeXr Ha.
have Hnonzero : a ^ (natural_order N a %/ 2) %% N != 0.
  apply/negP=>/eqP Hz.
  move: Hpowercop; rewrite -coprime_modr Hz /coprime gcdn0.
  by rewrite eq_sym (ltn_eqF HN).
have Hgreater : 1 < a ^ (natural_order N a %/ 2) %% N.
  by rewrite ltn_neqAle eq_sym Hneq1 lt0n Hnonzero.
have Hpred : N.-1 < N by rewrite ltn_predL; exact: ltnW HN.
have Hneqpred : a ^ (natural_order N a %/ 2) %% N != N.-1.
  by move: Hneg; rewrite (modn_small Hpred).
have Hbound : a ^ (natural_order N a %/ 2) %% N <= N.-1.
  by rewrite -ltnS (prednK (ltnW HN)); exact: ltn_pmod (ltnW HN).
have Hsmall : a ^ (natural_order N a %/ 2) %% N + 1 < N.
  by rewrite addn1 -ltn_predRL ltn_neqAle Hneqpred Hbound.
apply: nontrivial_sqrt_factor_mod HN Hgreater Hsmall _.
rewrite -expnM E.
exact: (@natural_order_power N HN a Ha).
Qed.

End Modulus.
End ClassicalShorFactorExtraction.


Module ClassicalOrderFindingOrbit.
(* The exact modular orbit used by the eigenstates on classical.pdf p.39.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalModularUnitary ClassicalShorCRT ClassicalShorSampleEvent.
Section Orbit.
Variables x N : nat.
Hypothesis Hx : coprime x N.
Hypothesis HN : (1 < N)%N.
Variable L : nat.
Hypothesis capacity : (N <= 2 ^ L)%N.

Definition orbit_length := (@natural_order N x).-1.+1.
Definition orbit_index := 'I_orbit_length.

Lemma orbit_lengthE : orbit_length = @natural_order N x.
Proof. by rewrite /orbit_length prednK //; exact: natural_order_positive. Qed.

Definition orbit_bits (i : orbit_index) :=
  @residue_bits N (ltnW HN) L capacity (x ^ i)%N.

Lemma orbit_bits_value i : (bseq2ord (orbit_bits i) : nat) = (x ^ i %% N)%N.
Proof. exact: residue_bits_value. Qed.

Lemma orbit_bits_injective : injective orbit_bits.
Proof.
move=>i j E; apply/eqP.
have Hp : coprime N x by rewrite coprime_sym.
have He : (@natural_unit N x ^+ i == @natural_unit N x ^+ j)%g.
  rewrite -(inj_eq (@unit_value_inj N))
    (@natural_power_value N HN x i Hp) (@natural_power_value N HN x j Hp).
  apply/eqP; by have := congr1 (fun z => (bseq2ord z : nat)) E;
    rewrite !orbit_bits_value.
by move: He; rewrite eq_expg_ord // -/(@natural_order N x) -orbit_lengthE.
Qed.

Definition orbit_basis (i : orbit_index) : 'Hs(L.-tuple bool) := ''(orbit_bits i).

Lemma orbit_basis_dot i j : [<orbit_basis i; orbit_basis j>] = (i == j)%:R.
Proof. by rewrite /orbit_basis onb_dot (inj_eq orbit_bits_injective). Qed.

HB.instance Definition _ := isPONB.Build 'Hs(L.-tuple bool) orbit_index
  orbit_basis orbit_basis_dot.

Definition orbit_embedding : 'Hom('Hs orbit_index, 'Hs(L.-tuple bool)) :=
  sumoutp (fun=>1) t2tv orbit_basis.

Lemma orbit_embedding_basis i : orbit_embedding ''i = orbit_basis i.
Proof. by rewrite /orbit_embedding sumoutp_apply scale1r. Qed.

Lemma orbit_embedding_isometry : orbit_embedding \is isolf.
Proof.
apply/isolfP; apply/(intro_onb t2tv)=>i.
by rewrite comp_lfunE /orbit_embedding sumoutp_apply scale1r
  sumoutp_adj sumoutp_apply conjC1 scale1r lfunE.
Qed.

HB.instance Definition _ := isIsoLf.Build _ _ orbit_embedding orbit_embedding_isometry.

Definition orbit_isometry : 'FI('Hs orbit_index, 'Hs(L.-tuple bool)) := orbit_embedding.

Lemma orbit_isometryE :
  (orbit_isometry : 'Hom('Hs orbit_index, 'Hs(L.-tuple bool))) = orbit_embedding.
Proof. by []. Qed.

Lemma orbit_embedding_dot a b :
  [<orbit_embedding a; orbit_embedding b>] = [<a;b>].
Proof. by rewrite -adj_dotEl isofKE. Qed.

Definition orbit_next (i : orbit_index) : orbit_index := ordS i.

Lemma orbit_next_value i : (val (orbit_next i)) = ((val i).+1 %% orbit_length)%N.
Proof. by []. Qed.

Lemma orbit_power_period k : (x ^ (k %% orbit_length) %% N = x ^ k %% N)%N.
Proof.
have Hp : coprime N x by rewrite coprime_sym.
rewrite -(@natural_power_value N HN x (k %% orbit_length)%N Hp)
  -(@natural_power_value N HN x k Hp).
by rewrite orbit_lengthE /natural_order expg_mod_order.
Qed.

Theorem modular_orbit_basis i :
  (@modular_unitary x N Hx (ltnW HN) L capacity) (orbit_basis i) =
  orbit_basis (orbit_next i).
Proof.
rewrite /orbit_basis /orbit_bits modular_unitaryE modular_bits_residue.
congr (t2tv _); apply: bseq2ord_inj; apply/val_inj.
by rewrite /residue_bits !ord2bseqK /= -expnS orbit_power_period.
Qed.

Lemma orbit_basis_zero : orbit_basis ord0 = ''(@residue_bits N (ltnW HN) L capacity 1).
Proof. by rewrite /orbit_basis /orbit_bits expn0. Qed.

End Orbit.
End ClassicalOrderFindingOrbit.


Module ClassicalShorUniform.
(* The actual printed Random command conditioned on coprimality.
   See PROOF_NOTES.md. *)


Import GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import ClassicalSemantics.
Import ClassicalShorCRT ClassicalShorProgram ClassicalLanguage ClassicalShorCounting ClassicalShorSampleEvent ClassicalShorProbability.
Local Notation C := hermitian.C.
Section Uniform.
Variable N : nat.
Hypothesis HN : 1 < N.

Lemma unit_value_positive (u : {unit 'Z_N}) : 0 < unit_value u.
Proof.
case E: (unit_value u)=>[|a] //.
by have := unit_value_coprime HN u; rewrite E /coprime gcdn0 (gtn_eqF HN).
Qed.

Lemma sample_index_bound (u : {unit 'Z_N}) : (unit_value u).-1 < N.-1.
Proof.
rewrite -ltnS !prednK ?unit_value_positive ?(ltnW HN) //.
exact: unit_value_lt.
Qed.

Definition sample_index (u : {unit 'Z_N}) : 'I_N.-1 := Ordinal (sample_index_bound u).

Lemma sample_index_value u : (val (sample_index u)).+1 = unit_value u.
Proof. by rewrite /= prednK ?unit_value_positive. Qed.

Definition sampled_unit (i : 'I_N.-1) : {unit 'Z_N} :=
  insubd (1%g : {unit 'Z_N}) ((val i).+1%:R : 'Z_N)%R.

Lemma sampled_value_bound (i : 'I_N.-1) : (val i).+1 < N.
Proof. by rewrite -ltn_predRL; exact: ltn_ord. Qed.

Lemma sampled_unit_value (i : 'I_N.-1) : coprime N (val i).+1 ->
  unit_value (sampled_unit i) = (val i).+1.
Proof.
move=>Hi; rewrite /sampled_unit /unit_value val_insubd.
rewrite unitZpE // Hi.
change (((val i).+1%:R : 'Z_N)%R = (val i).+1 :> nat).
by rewrite val_Zp_nat // modn_small ?sampled_value_bound.
Qed.

Lemma sampled_unitK : cancel sample_index sampled_unit.
Proof.
move=>u; apply: unit_value_inj.
by rewrite sampled_unit_value sample_index_value ?unit_value_coprime // sample_index_value unit_value_coprime.
Qed.

Lemma sample_indexK (i : 'I_N.-1) : coprime N (val i).+1 ->
  sample_index (sampled_unit i) = i.
Proof. by move=>Hi; apply/val_inj; rewrite /= sampled_unit_value. Qed.

Local Open Scope ring_scope.

Lemma sample_unit_reindex (P : pred nat) (F : nat -> C) :
  \sum_(i : 'I_N.-1 | coprime N (val i).+1 && P (val i).+1) F (val i).+1 =
  \sum_(u : {unit 'Z_N} | P (unit_value u)) F (unit_value u).
Proof.
have Hcan i : coprime N (val i).+1 && P (val i).+1 ->
    sample_index (sampled_unit i) = i.
  by move=>/andP[Hi _]; exact: sample_indexK.
rewrite (reindex_onto sample_index sampled_unit Hcan).
apply: eq_big=>u; rewrite sample_index_value ?unit_value_coprime ?sampled_unitK ?eqxx ?andbT //.
Qed.

Definition coprime_event_probability s (P : pred nat) : C :=
  \sum_(i : 'I_N.-1 | coprime N (val i).+1 && P (val i).+1)
    probability_mass (uniform_probability HN) s (val i).+1.

Lemma coprime_event_probabilityE s P : coprime_event_probability s P =
  (#|[pred u : {unit 'Z_N} | P (unit_value u)]|%:R : C) / N.-1%:R.
Proof.
rewrite /coprime_event_probability sample_unit_reindex.
transitivity (\sum_(u : {unit 'Z_N} | P (unit_value u)) (N.-1%:R : C)^-1).
  apply: eq_bigr=>u _; rewrite uniform_probabilityE unit_value_positive unit_value_lt //.
by rewrite sumr_const -[X in X = _]mulr_natr mulrC.
Qed.

Definition conditional_probability s (P : pred nat) : C :=
  coprime_event_probability s P / coprime_event_probability s predT.

Lemma unit_card_positive : (0 < #|{: {unit 'Z_N}}|)%N.
Proof. apply/card_gt0P; by exists 1%g. Qed.

Lemma conditioning_probability_positive s : 0 < coprime_event_probability s predT.
Proof.
rewrite coprime_event_probabilityE.
apply: divr_gt0; rewrite ltr0n; first exact: unit_card_positive.
by rewrite ltn_predRL.
Qed.

Theorem conditional_probabilityE s P : conditional_probability s P =
  (#|[pred u : {unit 'Z_N} | P (unit_value u)]|%:R : C) / #|{: {unit 'Z_N}}|%:R.
Proof.
rewrite /conditional_probability !coprime_event_probabilityE.
have Hd : (N.-1%:R : C) != 0 by rewrite pnatr_eq0 -lt0n; case: N HN=>[|[|n]].
by rewrite invf_div mulrA mulfVK.
Qed.

Theorem random_conditional_success_bound s : odd N ->
  1 - 1 / ((2 ^ (size (primes N)).-1)%N)%:R <=
  conditional_probability s (natural_success N).
Proof.
move=>Hodd; rewrite conditional_probabilityE.
have Eg : #|[pred u : {unit 'Z_N} | natural_success N (unit_value u)]| =
    #|@unit_success N|.
  apply: eq_card=>u; exact: (@natural_success_unit N HN u).
have Et : #|{: {unit 'Z_N}}| = totient N.
  by rewrite -cardsT -/(units_Zp N) card_units_Zp //; exact: ltnW HN.
rewrite Eg Et.
exact: uniform_unit_success_bound HN Hodd.
Qed.

End Uniform.
End ClassicalShorUniform.


Module ClassicalOrderFindingEigenstates.
(* Exact modular-orbit Fourier eigenstates, classical.pdf p.39.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Local Notation R := hermitian.R.
Local Notation C := hermitian.C.

Lemma runity_add n a b : runity n (a + b)%N = runity n a * runity n b.
Proof. by rewrite /runity natrD mulrDr mulrDl expipD. Qed.

Lemma runity_multiple n k : (0 < n)%N -> runity n (k * n)%N = 1.
Proof.
move=>Hn.
have Hnz : (n%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
rewrite /runity natrM mulrA (mulfK Hnz).
by rewrite -natrM expip2n.
Qed.

Lemma runity_mod n k : (0 < n)%N -> runity n (k %% n)%N = runity n k.
Proof.
move=>Hn; symmetry.
by rewrite {1}(divn_eq k n) runity_add runity_multiple // mul1r.
Qed.

Lemma runity_successor n (s j : 'I_n.+1) :
  runity n.+1 (s * ordS j)%N = runity n.+1 s * runity n.+1 (s * j)%N.
Proof.
rewrite /ordS /= -[LHS]runity_mod // modnMmr runity_mod // mulnS runity_add.
by [].
Qed.

Lemma runity_conjugate_successor n (s j : 'I_n.+1) :
  runity n.+1 s * (runity n.+1 (s * ordS j)%N)^* =
  (runity n.+1 (s * j)%N)^*.
Proof.
by rewrite runity_successor rmorphM /= mulrA /runity
  -!expipNC -expipD addrN expip0 mul1r.
Qed.

Definition inverse_fourier_basis n (s : 'I_n.+1) := (@QFTv n s)^*v.

Lemma inverse_fourier_basis_dot n (s t : 'I_n.+1) :
  [< inverse_fourier_basis s; inverse_fourier_basis t >] = (s == t)%:R.
Proof. by rewrite /inverse_fourier_basis conjv_dot QFTv_onb eq_sym. Qed.

HB.instance Definition _ n := isONB.Build 'Hs('I_n.+1) 'I_n.+1
  (@inverse_fourier_basis n) (@inverse_fourier_basis_dot n) (ihb_dim _).

Lemma inverse_fourier_basisE n (s : 'I_n.+1) :
  inverse_fourier_basis s = (sqrtC n.+1%:R)^-1 *:
    \sum_(j : 'I_n.+1) (runity n.+1 (s * j)%N)^* *: ''j.
Proof.
rewrite /inverse_fourier_basis QFTvE conjvZ conjv_sum
  geC0_conj ?invr_ge0 ?sqrtC_ge0 //.
congr (_ *: _); apply: eq_bigr=>j _.
by rewrite conjvZ t2tv_conj.
Qed.

Lemma inverse_fourier_zero_coefficient n (s : 'I_n.+1) :
  [< inverse_fourier_basis s; ''ord0 >] = ((sqrtC n.+1%:R)^-1)%R.
Proof.
by rewrite /inverse_fourier_basis conjv_dotl t2tv_conj dotp_cbQFT
  muln0 /runity mulr0 mul0r expip0 mulr1.
Qed.

Lemma inverse_fourier_sum n :
  (sqrtC n.+1%:R)^-1 *: \sum_(s : 'I_n.+1) inverse_fourier_basis s = ''ord0.
Proof.
rewrite [RHS](onb_vec (@inverse_fourier_basis n)) scaler_sumr.
apply: eq_bigr=>s _; by rewrite inverse_fourier_zero_coefficient.
Qed.

Section OrbitEmbedding.
Variable n : nat.
Variable H : chsType.
Variable E : 'FI('Hs('I_n.+1), H).
Variable U : 'FU(H).
Hypothesis cyclic_action : forall j : 'I_n.+1, U (E ''j) = E ''(ordS j).

Definition eigenstate (s : 'I_n.+1) := E (inverse_fourier_basis s).

Lemma eigenstate_dot s t : [< eigenstate s; eigenstate t >] = (s == t)%:R.
Proof. by rewrite /eigenstate -adj_dotEl isofKE inverse_fourier_basis_dot. Qed.

HB.instance Definition _ := isPONB.Build H 'I_n.+1 eigenstate eigenstate_dot.

Lemma eigenstateE s : eigenstate s = (sqrtC n.+1%:R)^-1 *:
  \sum_(j : 'I_n.+1) (runity n.+1 (s * j)%N)^* *: E ''j.
Proof.
rewrite /eigenstate inverse_fourier_basisE linearZ /= linear_sum /=.
congr (_ *: _); apply: eq_bigr=>j _; by rewrite linearZ.
Qed.

Theorem eigenstate_eigenvalue s : U (eigenstate s) = runity n.+1 s *: eigenstate s.
Proof.
rewrite eigenstateE !linearZ /= linear_sum /=.
under eq_bigr do rewrite linearZ /= cyclic_action.
rewrite [RHS]scalerA.
rewrite -scalerA.
congr (_ *: _).
rewrite scaler_sumr [RHS](reindex (@ordS n.+1) (onW_bij predT (ordS_bij n.+1))) /=.
apply: eq_bigr=>j _.
by rewrite scalerA runity_conjugate_successor.
Qed.

Theorem eigenstate_sum :
  (sqrtC n.+1%:R)^-1 *: \sum_(s : 'I_n.+1) eigenstate s = E ''ord0.
Proof. by rewrite /eigenstate -linear_sum -linearZ /= inverse_fourier_sum. Qed.

End OrbitEmbedding.

Section ModularOrbit.
Import ClassicalModularUnitary ClassicalOrderFindingOrbit ClassicalShorSampleEvent.
Variables x N : nat.
Hypothesis Hx : coprime x N.
Hypothesis HN : (1 < N)%N.
Variable L : nat.
Hypothesis capacity : (N <= 2 ^ L)%N.

Definition modular_eigenstate (s : orbit_index x N) : 'Hs(L.-tuple bool) :=
  eigenstate (@orbit_isometry x N Hx HN L capacity) s.

Theorem modular_eigenstate_dot s t :
  [< modular_eigenstate s; modular_eigenstate t >] = (s == t)%:R.
Proof. exact: eigenstate_dot. Qed.

Lemma modular_eigenstate_normal s : [< modular_eigenstate s; modular_eigenstate s >] = 1.
Proof. by rewrite modular_eigenstate_dot eqxx. Qed.

HB.instance Definition _ s := isNormalState.Build _ (modular_eigenstate s)
  (modular_eigenstate_normal s).

Theorem modular_eigenstateE s : modular_eigenstate s =
  (sqrtC (orbit_length x N)%:R)^-1 *:
  \sum_(j : orbit_index x N)
    expip (- (2%:R * (s * j)%:R / (orbit_length x N)%:R)) *:
      (@orbit_basis x N HN L capacity j).
Proof.
rewrite /modular_eigenstate eigenstateE.
congr (_ *: _); apply: eq_bigr=>j _.
by rewrite /runity -expipNC /orbit_isometry orbit_embedding_basis.
Qed.

Theorem modular_eigenvalue s :
  (@modular_unitary x N Hx (ltnW HN) L capacity) (modular_eigenstate s) =
  expip (2%:R * s%:R / (orbit_length x N)%:R) *: modular_eigenstate s.
Proof.
apply: (@eigenstate_eigenvalue _ _ (@orbit_isometry x N Hx HN L capacity)).
move=>j; rewrite /orbit_isometry !orbit_embedding_basis.
exact: modular_orbit_basis.
Qed.

Theorem modular_eigenstate_sum :
  (sqrtC (orbit_length x N)%:R)^-1 *:
    \sum_(s : orbit_index x N) modular_eigenstate s =
  ''(@residue_bits N (ltnW HN) L capacity 1).
Proof.
by rewrite /modular_eigenstate eigenstate_sum /orbit_isometry
  orbit_embedding_basis orbit_basis_zero.
Qed.

Theorem modular_eigenstate_one :
  (sqrtC (orbit_length x N)%:R)^-1 *:
    \sum_(s : orbit_index x N) modular_eigenstate s =
  (@ClassicalOrderFinding.one_state N L HN capacity : 'Hs(L.-tuple bool)).
Proof. exact: modular_eigenstate_sum. Qed.

End ModularOrbit.
End ClassicalOrderFindingEigenstates.


Module ClassicalShorSampling.
(* The actual sampler partition and scalar Equation (21).
   See PROOF_NOTES.md for the prior argument. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory Summable.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalShorProgram ClassicalShorSampleEvent ClassicalShorProbability ClassicalShorUniform.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.

Section Sampling.
Variable N : nat.
Hypothesis HN : (1 < N)%N.

Lemma gcd_guard_complement a : (0 < a)%N ->
  (1 < gcdn a N)%N = ~~ coprime N a.
Proof.
move=>Ha.
have Hg : (0 < gcdn a N)%N by rewrite gcdn_gt0 Ha.
by rewrite ltn_neqAle Hg andbT /coprime gcdnC eq_sym.
Qed.

Theorem sampling_partition s :
  direct_probability N + coprime_event_probability HN s predT = 1.
Proof.
rewrite /direct_probability /direct_ordinal_weights fin_dom_sum /=.
rewrite /coprime_event_probability [X in _ + X]big_mkcond.
rewrite -big_split.
transitivity (\sum_(i : 'I_N.-1) (N.-1%:R : C)^-1).
  apply: eq_bigr=>i _.
  rewrite uniform_probabilityE ltn0Sn sampled_value_bound //=.
  rewrite gcd_guard_complement //.
  by case: (coprime N (val i).+1); rewrite ?addr0 ?add0r.
rewrite sumr_const card_ord -[X in X = 1]mulr_natr mulVf // pnatr_eq0.
by case: N HN=>[|[|n]].
Qed.

Lemma coprime_probability_complement s :
  coprime_event_probability HN s predT = 1 - direct_probability N.
Proof. by rewrite -(sampling_partition s) addrAC subrr add0r. Qed.

Theorem sampling_mixture_bound s (p : C) :
  odd N -> 0 <= p -> p <= 1 ->
  p * (1 - 1 / ((2 ^ (size (primes N)).-1)%N)%:R) <=
  direct_probability N +
    p * coprime_event_probability HN s (natural_success N).
Proof.
move=>Hodd Hp0 Hp1.
pose d := (2 ^ (size (primes N)).-1)%N.
have Hd : (0 : C) < d%:R by rewrite ltr0n /d expn_gt0.
have Hd1 : (1 : C) <= d%:R by rewrite ler1n /d expn_gt0.
have Hc0 : (0 : C) <= 1 - 1 / d%:R.
  by rewrite subr_ge0 ler_pdivrMr // mul1r.
have Hc1 : (1 - 1 / d%:R : C) <= 1.
  rewrite lerBlDr lerDl; apply: divr_ge0; by rewrite ?ler01 ?ler0n.
have Hcond := random_conditional_success_bound HN s Hodd.
rewrite /conditional_probability ler_pdivlMr
  ?conditioning_probability_positive // in Hcond.
have Hprod : (1 - direct_probability N) * (1 - 1 / d%:R) <=
    coprime_event_probability HN s (natural_success N).
  by rewrite -(coprime_probability_complement s) mulrC.
have Hmix := mixture_lower_bound (@direct_probability_ge0 N) Hp0 Hp1 Hc0 Hc1.
apply: le_trans Hmix _.
rewrite lerD2l.
by apply: ler_wpM2l.
Qed.

End Sampling.
End ClassicalShorSampling.
