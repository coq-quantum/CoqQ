(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import footprint.
From quantum.example.distributive Require Import language operational scheduler local_actions.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DistributedProgress.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions.

Lemma atom_successor_step a m rho :
  local_step (local_config (Atomic a) (Some m) rho) (atom_successor a m rho).
Proof.
by case: a=>[| |t x e|t x p|t q phi|t q U|t u x q M]; constructor.
Qed.

Lemma local_successor_step s : statement_wf s -> forall m rho,
  local_step (local_config s (Some m) rho) (local_successor s m rho).
Proof.
elim: s=>[|a|s IHs t IHt|n g b IHb|n g b IHb] //= Hwf m rho.
- exact: atom_successor_step.
- apply: StepSequence; exact: IHs (proj1 Hwf) m rho.
- case: pickP=>[i Hi|Hnone].
  + exact: StepAlternative Hi.
  + apply: StepAlternativeFail; by apply/forallP=>i; rewrite Hnone.
- case: pickP=>[i Hi|Hnone].
  + exact: StepRepetition Hi.
  + apply: StepRepetitionDone; by apply/forallP=>i; rewrite Hnone.
Qed.

End DistributedProgress.
