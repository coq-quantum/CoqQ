(* Extension of cqwhile kernels to arbitrary cq-states, classical.pdf 4.3–4.4. *)
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
From quantum.example.classical Require Import state language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

(* Constant and state-dependent measurements use cqwhile's existing mexpr. *)
Module ClassicalMeasurementExamples.
Import ClassicalLanguage DefaultQMem.Exports.
Local Notation Hq := 'H[msys]_finset.setT.

Definition boolean_measurement u (q : wf_qreg u) (M : 'QM(bool; 'Ht u)) :
  mexpr bool (eval_qtype u) := EConst M.

Lemma boolean_measurement_branch u (q : wf_qreg u) (M : 'QM(bool; 'Ht u)) s b :
  measurement_branches (tc := QBool) q (boolean_measurement q M) s b =
    liftfso (formso (tf2f q q (M b))) :> 'SO(Hq).
Proof. exact: (measurement_branchE (tc := QBool)). Qed.

Lemma boolean_measurement_denote u (x : variable Boolean) (q : wf_qreg u)
    (M : 'QM(bool; 'Ht u)) :
  denote (Measure x q (boolean_measurement q M)) = measure_sem x q (cst_ M).
Proof. by []. Qed.

Lemma boolean_measurement_mass u (q : wf_qreg u) (M : 'QM(bool; 'Ht u))
    s (rho : 'End(Hq)) :
  \Tr (sum (fun b => measurement_branches (tc := QBool) q (boolean_measurement q M) s b rho)) = \Tr rho.
Proof. exact: (measurement_total_trace (t := QBool)). Qed.

Definition selected_measurement u (x : variable Boolean)
    (M0 M1 : 'QM(bool; 'Ht u)) : mexpr bool (eval_qtype u) :=
  EApp (EConst (fun b => if b then M1 else M0)) (EVar x).

Lemma selected_measurement_eval u (x : variable Boolean)
    (M0 M1 : 'QM(bool; 'Ht u)) s :
  eval (selected_measurement x M0 M1) s = if (s.[x])%M then M1 else M0.
Proof. by []. Qed.
End ClassicalMeasurementExamples.
