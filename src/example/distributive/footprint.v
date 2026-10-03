(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import language.

Module DistributedFootprint.
Import DistributedLanguage.
Local Open Scope fset_scope.

Lemma atom_changes_reads a x : x \in atom_changes a -> atom_reads a x.
Proof.
case: a=>[| |t y e|t y p|t q phi|t q U|t u y q M] /=;
  rewrite ?inE //; move=>/eqP->; by left.
Qed.

Lemma statement_changes_reads s : forall x,
  x \in statement_changes s -> statement_reads s x.
Proof.
elim: s=>[|a|s IHs t IHt|n g b IHb|n g b IHb] x /=.
- by rewrite inE.
- exact: atom_changes_reads.
- rewrite in_fsetU=>/orP[Hx|Hx].
  + left; exact: IHs.
  + right; exact: IHt.
- move=>/bigfcupP[i _ Hi]; exists i=>//; right; exact: IHb i x Hi.
- move=>/bigfcupP[i _ Hi]; exists i=>//; right; exact: IHb i x Hi.
Qed.

Lemma communication_changes_reads a x :
  x \in communication_changes a -> communication_reads a x.
Proof. by case: a=>t c y /=; rewrite inE // =>/eqP->. Qed.

Lemma process_changes_reads p x : x \in process_changes p -> process_reads p x.
Proof.
rewrite /process_changes in_fsetU=>/orP[Hx|Hx].
- left; exact: statement_changes_reads Hx.
- right; move/bigfcupP: Hx=>[j _]; rewrite in_fsetU=>/orP[Hx|Hx].
  + exists j=>//; left; right; exact: communication_changes_reads Hx.
  + exists j=>//; right; exact: statement_changes_reads Hx.
Qed.

Lemma private_changes_disjoint n (p : 'I_n -> process) : pairwise_private p ->
  forall i j, i != j -> [disjoint process_changes (p i) & process_changes (p j)].
Proof.
move=>Hprivate i j Hij; apply/fdisjointP=>x Hx.
exact: (proj1 (Hprivate i j Hij) x (process_changes_reads Hx)).
Qed.

End DistributedFootprint.
