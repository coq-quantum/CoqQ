(* Nonzero, step-counted computation paths for classical.pdf Lemma 4.2.
   See OPERATIONAL-ROUTE-COST-NOTES.md. *)
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
From quantum.example.classical Require Import
  language operational computations operational_route_cost.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalOperational ClassicalComputations
  ClassicalOperationalRouteCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalOperationalCountedPaths.
Local Notation Hq := 'H[msys]_finset.setT.

Inductive counted_path : nat -> configuration -> configuration -> Type :=
  | CountedPathRefl x : counted_path 0 x x
  | CountedPathStep n x y z : live_step x y -> counted_path n y z ->
      counted_path n.+1 x z.

Definition counted_maximal_path n x y :=
  (counted_path n x y * terminal y)%type.

Lemma counted_path_erase n x y : counted_path n x y -> path x y.
Proof.
elim=>[x0|n0 x0 x1 x2 st p IH]; first exact: PathRefl.
exact: PathStep st IH.
Qed.

Definition counted_completion n x s' r' : Type :=
  match residual x with
  | Some c => counted_terminates n c (classical x) (quantum x) s' r'
  | None => ((n = 0%N) * ((classical x = s') * (quantum x = r')))%type
  end.

Lemma counted_path_completion n x y (p : counted_path n x y) :
  forall k s' r', counted_completion k y s' r' ->
    counted_completion (n + k)%N x s' r'.
Proof.
elim: p=>[x0|n0 x0 x1 x2 st p IH] k s' r' H.
- by rewrite add0n.
- have H1 := IH k s' r' H.
  clear p IH H.
  case: x0 st=>[[c|] s r]; last by case.
  case: x1 H1=>[[c1|] s1 r1] /= H1 [st nz].
  + rewrite /counted_completion /= addSn; exact: CountedMore st H1.
  + case: H1=>Hk [Es Er].
    rewrite /counted_completion /= addSn Hk -Es -Er.
    exact: CountedDone st.
Qed.

Theorem counted_path_terminates n c s r s' r' :
  counted_path n (Configuration (Some c) s r) (Configuration None s' r') ->
  counted_terminates n c s r s' r'.
Proof.
move=>p.
have H := @counted_path_completion _ _ _ p 0%N s' r' (erefl, (erefl, erefl)).
by rewrite addn0 in H.
Qed.

Theorem counted_terminates_path n c s r s' r' :
  counted_terminates n c s r s' r' -> r' != 0 ->
  counted_path n (Configuration (Some c) s r) (Configuration None s' r').
Proof.
elim=>[c0 s0 r0 s1 r1 st|
  n0 c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] nz.
- apply: (@CountedPathStep 0 _ (Configuration None s1 r1));
    last exact: CountedPathRefl.
  exact: (st, nz).
- have nz1 : r1 != 0.
    apply/negP=>/eqP Hz; move: nz.
    by rewrite (terminates_zero (counted_erase tail) Hz) eqxx.
  apply: (@CountedPathStep n0 _ (Configuration (Some c1) s1 r1));
    last exact: IH nz.
  exact: (st, nz1).
Qed.

Theorem successful_counted_maximal_iff n c s r s' r' :
  inhabited (counted_maximal_path n
    (Configuration (Some c) s r) (Configuration None s' r')) <->
  inhabited (counted_terminates n c s r s' r') /\ r' != 0.
Proof.
split.
- move=>[[p _]]; split; first by constructor; exact: counted_path_terminates p.
  case: (path_nonzero_or_refl (counted_path_erase p))=>[E|//].
  by inversion E.
- move=>[[d] nz]; constructor; split.
  + exact: counted_terminates_path d nz.
  + exact: terminal_none.
Qed.

Theorem successful_counted_route_iff n c s r s' r' :
  inhabited (counted_maximal_path n
    (Configuration (Some c) s r) (Configuration None s' r')) <->
  exists rt, eval_route rt c (s,r) = Some (s',r') /\
    route_cost rt = n /\ r' != 0.
Proof.
rewrite successful_counted_maximal_iff -successful_route_exact_iff; split.
- by move=>[[rt [Hrt Hcost]] nz]; exists rt.
- by move=>[rt [Hrt [Hcost nz]]]; split=>//; exists rt.
Qed.

End ClassicalOperationalCountedPaths.
