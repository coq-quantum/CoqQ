(* Weakest preconditions for arbitrary classical-quantum kernels.
   See HOARE-NOTES.md for the infinite-sum and duality arguments. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
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
From quantum.example.classical Require Import state assertion kernel kernel_expectation language predicate.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


Module CQPrimitive.
Import CQAssertion CQPredicate ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Implicit Types Q : cmem -> 'FO(Hq).

Lemma assign_pre total t (x : variable t) e Q s :
  (xp total (denote (Assign x e)) Q s : 'End(Hq)) =
    (Q (s.[x <- eval e s])%M : 'End(Hq)).
Proof. by rewrite /= /assign_sem xp_sunit dualso1 soE. Qed.

Lemma initial_pre total t (q : wf_qreg t) phi Q s :
  (xp total (denote (Initialize q phi)) Q s : 'End(Hq)) =
    (liftfso (initialso (tv2v q (esem phi s))))^*o (Q s).
Proof. by rewrite /= /initial_sem xp_sunit. Qed.

Lemma unitary_pre total t (q : wf_qreg t) U Q s :
  (xp total (denote (Unitary q U)) Q s : 'End(Hq)) =
    (liftfso (formso (tf2f q q (esem U s))))^*o (Q s).
Proof. by rewrite /= /unitary_sem xp_sunit. Qed.


Lemma random_complete t (x : variable t) p s :
  sum (denote (Random x p) s) \is tpmap.
Proof.
rewrite /= /random_sem /sdlet /= sdlet_sum /sdistr sdistr_sum
  probability_normalized scale1r.
exact: is_tpmap.
Qed.

Lemma random_pre total t (x : variable t) p Q s :
  (xp total (denote (Random x p)) Q s : 'End(Hq)) =
    sum (fun v => probability_mass p s v *: (Q (s.[x <- v])%M : 'End(Hq))).
Proof.
rewrite (xp_wp (K := denote (Random x p)) total Q (random_complete x p))
  /denote /random_sem wp_sdlet.
apply: eq_sum=>v.
by rewrite /sdistr /= /sdistr_def linearZ /= dualso1 !soE.
Qed.

Lemma measurement_complete t u (x : variable (QType t)) (q : wf_qreg u) M s :
  sum (denote (Measure x q M) s) \is tpmap.
Proof.
rewrite /= /measure_kernel /measure_sem /sdlet /= sdlet_sum smeas_sum elemso_sum.
exact: is_tpmap.
Qed.

Lemma measurement_pre total t u (x : variable (QType t)) (q : wf_qreg u) M Q s :
  (xp total (denote (Measure x q M)) Q s : 'End(Hq)) =
    \sum_v ((liftf_fun (tm2m q q (esem M s)) v)^A \o
      (Q (s.[x <- v])%M : 'End(Hq)) \o (liftf_fun (tm2m q q (esem M s)) v)).
Proof.
rewrite (xp_wp (K := denote (Measure x q M)) total Q (measurement_complete x q M))
  /denote /measure_kernel /measure_sem wp_sdlet fin_dom_sum.
apply: eq_bigr=>v _.
by rewrite /smeas /= /smeas_def dualso_formE.
Qed.

End CQPrimitive.
