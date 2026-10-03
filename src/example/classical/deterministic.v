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

From quantum.example.classical Require Import language.

Module ClassicalDeterministic.
Import ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.

Definition point (s : store) (F : 'SO(Hq)) (m : store) :=
  if m == s then F else 0.

Lemma sequence_point (K L : kernel) s t F :
  (forall m, K s m = point t F m) ->
  forall m, slet K L s m = L t m :o F.
Proof.
move=>HK m; change (sum (fun j : store => L j m :o K s j) = L t m :o F).
rewrite (fin_supp_sum (S := [fset t]%fset)).
- by move=>j; rewrite inE=>/negPf Hjt; rewrite HK /point Hjt comp_so0r.
- by rewrite psum1 HK /point eqxx.
Qed.

Inductive execution : command -> store -> store -> 'SO(Hq) -> Prop :=
| RunSkip s : execution Skip s s \:1
| RunAssign t (x : variable t) e s :
    execution (Assign x e) s (s.[x <- eval e s])%M \:1
| RunInitialize u (q : wf_qreg u) phi s :
    execution (Initialize q phi) s s
      (liftfso (initialso (tv2v q (eval phi s))))
| RunUnitary u (q : wf_qreg u) ue s :
    execution (Unitary q ue) s s
      (liftfso (formso (tf2f q q (eval ue s))))
| RunSequence c1 c2 s t u F G :
    execution c1 s t F -> execution c2 t u G ->
    execution (Sequence c1 c2) s u (G :o F)
| RunIfTrue b c1 c0 s t F :
    eval b s = true -> execution c1 s t F ->
    execution (Conditional b c1 c0) s t F
| RunIfFalse b c1 c0 s t F :
    eval b s = false -> execution c0 s t F ->
    execution (Conditional b c1 c0) s t F
| RunWhileFalse b c s :
    eval b s = false -> execution (While b c) s s \:1
| RunWhileTrue b c s t u F G :
    eval b s = true -> execution c s t F -> execution (While b c) t u G ->
    execution (While b c) s u (G :o F).

Theorem execution_denote c s t F : execution c s t F ->
  forall m, denote c s m = point t F m.
Proof.
move=>D; elim: c s t F / D=>[s|t x e s|u q phi s|u q ue s|
  c1 c2 s t u F G D1 IHD1 D2 IHD2|
  b c1 c0 s t F Eb D IHD|b c1 c0 s t F Eb D IHD|
  b c s Eb|b c s t u F G Eb D1 IHD1 D2 IHD2] m.
- by [].
- by [].
- by [].
- by [].
- change (slet (denote c1) (denote c2) s m = point u (G :o F) m).
  rewrite (@sequence_point (denote c1) (denote c2) s t F IHD1 m) IHD2 /point.
  by case: (m == u); rewrite ?comp_so0l.
- by rewrite denote_conditional Eb; apply: IHD.
- by rewrite denote_conditional Eb; apply: IHD.
- rewrite denote_while_unfold denote_conditional Eb; by [].
- rewrite denote_while_unfold denote_conditional Eb.
  change (slet (denote c) (denote (While b c)) s m = point u (G :o F) m).
  rewrite (@sequence_point (denote c) (denote (While b c)) s t F IHD1 m) IHD2 /point.
  by case: (m == u); rewrite ?comp_so0l.
Qed.

End ClassicalDeterministic.
