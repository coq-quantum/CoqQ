(* Lemma 3.12; see NORMALIZED-UPDATE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate
  hoare rules expectation kernel_expectation.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


Module CQStateUpdate.
Import CQAssertion ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Local Notation state := (@CQState.state cmem Hq).

Definition substitute t (x : variable t) (e : expression (value t))
    (P : assertion) : assertion := fun m => P (m.[x <- eval e m])%M.

Definition update_state t (x : variable t) (e : expression (value t))
    (rho : state) : state :=
  CQKernel.apply (sunit (fun _ : cmem => (\:1 : 'QO(Hq)))
    (fun m => (m.[x <- eval e m])%M)) rho.

Lemma update_stateE t (x : variable t) (e : expression (value t)) rho out :
  update_state x e rho out =
    sum (fun m => if out == (m.[x <- eval e m])%M then rho m else 0).
Proof.
rewrite /update_state CQKernel.applyE; apply:eq_sum=>m.
rewrite /sunit /= /sunit_def.
by case: ifP=>_; rewrite ?id_soE ?abort_soE.
Qed.

Theorem expect_update t (x : variable t) (e : expression (value t)) P rho :
  expect (substitute x e P) rho = expect P (update_state x e rho).
Proof.
rewrite /update_state CQKernelExpectation.expect_sunit /expect.
apply:eq_sum=>m; by rewrite /expect_term /substitute id_soE.
Qed.

Theorem update_state_mass t (x : variable t) (e : expression (value t)) rho :
  CQState.mass (update_state x e rho) = CQState.mass rho.
Proof.
have E := expect_update x e semantic_top rho.
change (expect semantic_top rho = expect semantic_top (update_state x e rho)) in E.
by move: E; rewrite !expect_identity -!CQState.mass_trace=>->.
Qed.

Lemma update_state_assignment t (x : variable t) (e : expression (value t)) rho :
  update_state x e rho = CQHoare.run (Assign x e) rho.
Proof. by []. Qed.

End CQStateUpdate.
