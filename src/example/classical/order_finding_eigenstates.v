(* Exact modular-orbit Fourier eigenstates, classical.pdf p.39.
   See ORDER-FINDING-EIGENSTATES-NOTES.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences exp trigo.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import language fourier phase_estimation
  modular_unitary order_finding order_finding_orbit shor_sample_event.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


Module ClassicalOrderFindingEigenstates.
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
