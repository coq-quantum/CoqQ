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

From quantum.example.classical Require Import language deterministic algorithm_loops.

Module ClassicalIndexedLoops.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops.
Local Notation Hq := 'H[msys]_finset.setT.

Section IndexedLoop.
Variable (x : variable Integer) (c : command).
Variable (next : nat -> store -> store) (action : nat -> store -> 'SO(Hq)).

Fixpoint final_store k n s : store :=
  if n is m.+1 then final_store k.+1 m (next k s) else s.
Fixpoint accumulated_action k n s : 'SO(Hq) :=
  if n is m.+1 then accumulated_action k.+1 m (next k s) :o action k s
  else \:1.

Lemma indexed_loop_execution n k s :
  (s.[x])%M = Posz k ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    execution c t (next j t) (action j t)) ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    ((next j t).[x])%M = Posz j.+1) ->
  execution (While (below x (k + n)) c) s
    (final_store k n s) (accumulated_action k n s).
Proof.
elim: n k s=>[|n IH] k s Hs Hbody Hnext.
- rewrite addn0 /=; apply: RunWhileFalse.
  by rewrite /below /eval /= Hs ltxx.
- have Hrange : (k <= k < k + n.+1)%N.
    by rewrite leqnn addnS ltnS leq_addr.
  have Hb : eval (below x (k + n.+1)) s = true.
    by rewrite /below /eval /= Hs ltz_nat addnS ltnS leq_addr.
  have Ht := Hnext k s Hrange Hs.
  have Htail : execution (While (below x (k.+1 + n)) c)
      (next k s) (final_store k.+1 n (next k s))
      (accumulated_action k.+1 n (next k s)).
    apply: (IH k.+1 (next k s) Ht).
    + move=>j t /andP[kj jn] Hj; apply: Hbody Hj.
      by rewrite (leq_trans (leqnSn k) kj) addnS -addSn jn.
    + move=>j t /andP[kj jn] Hj; apply: Hnext Hj.
      by rewrite (leq_trans (leqnSn k) kj) addnS -addSn jn.
  rewrite addSn -addnS in Htail.
  exact: (RunWhileTrue Hb (Hbody k s Hrange Hs) Htail).
Qed.

Lemma indexed_loop_denote n k s :
  (s.[x])%M = Posz k ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    execution c t (next j t) (action j t)) ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    ((next j t).[x])%M = Posz j.+1) ->
  forall m, denote (While (below x (k + n)) c) s m =
    point (final_store k n s) (accumulated_action k n s) m.
Proof. move=>Hs Hb Hn; exact: execution_denote (indexed_loop_execution Hs Hb Hn). Qed.

End IndexedLoop.
Definition one_based_index n (z : int) : option 'I_n :=
  if z is Posz k.+1 then insub k else None.

Definition indexed_gate u n (q : wf_qreg u) (x : variable Integer)
    (U : 'I_n -> 'FU('Ht u)) : command :=
  Conditional
    (EApp (EConst (fun z => isSome (one_based_index n z))) (EVar x))
    (Unitary q (EApp
      (EConst (fun z => if one_based_index n z is Some i then U i else
        (\1 : 'FU('Ht u)))) (EVar x))) Abort.

Lemma one_based_indexE n (i : 'I_n) : one_based_index n (Posz i.+1) = Some i.
Proof. by rewrite /one_based_index valK. Qed.

Lemma indexed_gate_execution u n (q : wf_qreg u) (x : variable Integer)
    (U : 'I_n -> 'FU('Ht u)) (i : 'I_n) s :
  (s.[x])%M = Posz i.+1 ->
  execution (indexed_gate q x U) s s (liftfso (formso (tf2f q q (U i)))).
Proof.
move=>Hs; apply: RunIfTrue.
- by rewrite /eval /= Hs one_based_indexE.
- have D := RunUnitary q
    (EApp (EConst (fun z => if one_based_index n z is Some j then U j else
      (\1 : 'FU('Ht u)))) (EVar x)) s.
  by rewrite /eval /= Hs one_based_indexE in D.
Qed.

End ClassicalIndexedLoops.
