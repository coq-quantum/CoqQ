(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)
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

From quantum.example.classical Require Import language deterministic.

Module ClassicalAlgorithmLoops.
Import ClassicalLanguage ClassicalDeterministic.
Local Notation Hq := 'H[msys]_finset.setT.

Definition increment (x : variable Integer) : expression int :=
  EApp (EConst (fun z : int => z + 1)) (EVar x).
Definition next_store (x : variable Integer) (s : store) :=
  (s.[x <- eval (increment x) s])%M.
Definition below (x : variable Integer) (K : nat) : bool_expr :=
  EApp (EConst (fun z : int => z < Posz K)) (EVar x).
Definition counted_unitary u (q : wf_qreg u) (U : 'FU('Ht u))
    (x : variable Integer) (K : nat) :=
  While (below x K) (Sequence (Unitary q (EConst U)) (Assign x (increment x))).

Fixpoint superop_power (A : 'SO(Hq)) n : 'SO(Hq) :=
  if n is n'.+1 then superop_power A n' :o A else \:1.

Lemma next_store_value (x : variable Integer) s k : (s.[x])%M = Posz k ->
  (next_store x s).[x]%M = Posz k.+1.
Proof.
move=>Hs; rewrite /next_store get_set_eq /increment /eval /= Hs.
by rewrite -PoszD addn1.
Qed.

Lemma counted_unitary_execution u (q : wf_qreg u) U (x : variable Integer) n k s :
  (s.[x])%M = Posz k ->
  execution (counted_unitary q U x (k + n)) s (iter n (next_store x) s)
    (superop_power (liftfso (formso (tf2f q q U))) n).
Proof.
elim: n k s=>[|n IH] k s Hs.
- rewrite addn0 /counted_unitary /=; apply: RunWhileFalse.
  by rewrite /below /eval /= Hs ltxx.
- have Hb : eval (below x (k + n.+1)) s = true.
    by rewrite /below /eval /= Hs ltz_nat addnS ltnS leq_addr.
  have Hbody : execution
      (Sequence (Unitary q (EConst U)) (Assign x (increment x))) s
      (next_store x s) (liftfso (formso (tf2f q q U))).
    rewrite -[liftfso _]comp_so1l.
    exact: (RunSequence (RunUnitary q (EConst U) s) (RunAssign x (increment x) s)).
  have Htail := IH k.+1 (next_store x s) (next_store_value Hs).
  rewrite /counted_unitary addSn -addnS in Htail.
  rewrite /counted_unitary iterSr /=.
  exact: (RunWhileTrue Hb Hbody Htail).
Qed.

Lemma counted_unitary_denote u (q : wf_qreg u) U (x : variable Integer) n k s m :
  (s.[x])%M = Posz k ->
  denote (counted_unitary q U x (k + n)) s m =
    point (iter n (next_store x) s)
      (superop_power (liftfso (formso (tf2f q q U))) n) m.
Proof.
move=>Hs; apply: execution_denote.
exact: (@counted_unitary_execution u q U x n k s Hs).
Qed.

End ClassicalAlgorithmLoops.
