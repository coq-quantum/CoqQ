(* The exact modular orbit used by the eigenstates on classical.pdf p.39.
   See ORDER-FINDING-ORBIT-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap all_fingroup cyclic.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.classical Require Import modular_unitary shor_crt shor_sample_event.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalOrderFindingOrbit.
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
