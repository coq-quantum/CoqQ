(* Equation (17), classical.pdf. See ORDER-FINDING-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope nat_scope.

Module ClassicalModularUnitary.
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
