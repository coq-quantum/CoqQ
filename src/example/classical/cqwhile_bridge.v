(* Classical-quantum language of Feng and Ying (2021), Sections 3.1 and 4.
   The kernel combinators and unbounded loop construction are reused from
   CoqQ's veri_QEC/cqwhile.v, including its classical types, higher-order
   expressions and state-dependent quantum operations. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From quantum.example.classical Require Import language.

Module ClassicalCQWhile.
Import ClassicalLanguage.

Fixpoint to_cqwhile (c : command) : cmd_ :=
  match c with
  | Skip => skip_
  | Abort => abort_
  | Assign t x e => assign_ x e
  | Random t x p => random_ x (probability_expression p)
  | Measure t u x q me => measure_ x q me
  | Initialize u q phi => initial_ q phi
  | Unitary u q ue => unitary_ q ue
  | Sequence c1 c2 => seqc_ (to_cqwhile c1) (to_cqwhile c2)
  | Conditional b c1 c0 => cond_ b (to_cqwhile c1) (to_cqwhile c0)
  | While b c => while_ b (to_cqwhile c)
  end.

Theorem denote_to_cqwhile c : denote c = sem_aux (to_cqwhile c).
Proof.
elim: c=>[| |t x e|t x p|t u x q me|u q phi|u q ue|
  c1 IH1 c2 IH2|b c1 IH1 c0 IH0|b c IH].
- by [].
- by [].
- by [].
- by [].
- by [].
- by [].
- by [].
- change (slet (denote c1) (denote c2) =
    slet (sem_aux (to_cqwhile c1)) (sem_aux (to_cqwhile c2))).
  by rewrite IH1 IH2.
- change (if_sem b (denote c1) (denote c0) =
    if_sem b (sem_aux (to_cqwhile c1)) (sem_aux (to_cqwhile c0))).
  by rewrite IH1 IH0.
- change (while_sem b (denote c) = while_sem b (sem_aux (to_cqwhile c))).
  by rewrite IH.
Qed.

End ClassicalCQWhile.
