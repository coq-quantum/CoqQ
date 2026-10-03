(* Exact operational transition counts, classical.pdf Lemma 4.2.
   See OPERATIONAL-ROUTE-COST-NOTES.md for the argument. *)
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
From quantum.example.classical Require Import language operational computations.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalOperational ClassicalComputations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalOperationalRouteCost.
Local Notation Hq := 'H[msys]_finset.setT.

Fixpoint route_cost (r : route) : nat :=
  match r with
  | TR_cond1 r | TR_cond2 r | TR_while1 r => (route_cost r).+1
  | TR_seqc r1 r2 => (route_cost r1 + route_cost r2)%N
  | _ => 1%N
  end.

Lemma route_cost_positive r : (0 < route_cost r)%N.
Proof. by elim: r=>//= r1 H1 r2 H2; rewrite addn_gt0 H1. Qed.

Inductive counted_terminates :
    nat -> command -> store -> 'End(Hq) -> store -> 'End(Hq) -> Type :=
  | CountedDone c s r s' r' : step c s r None s' r' ->
      counted_terminates 1 c s r s' r'
  | CountedMore n c c' s r s1 r1 s' r' :
      step c s r (Some c') s1 r1 ->
      counted_terminates n c' s1 r1 s' r' ->
      counted_terminates n.+1 c s r s' r'.

Lemma counted_erase n c s r s' r' :
  counted_terminates n c s r s' r' -> terminates c s r s' r'.
Proof.
elim=>[c0 s0 r0 s1 r1 st|n0 c0 c1 s0 r0 s1 r1 s2 r2 st tail IH].
- exact: TerminatesDone st.
- exact: TerminatesMore st IH.
Qed.

Lemma counted_positive n c s r s' r' :
  counted_terminates n c s r s' r' -> (0 < n)%N.
Proof. by case. Qed.

Lemma counted_sequence n1 n2 c1 c2 s r m q s' r' :
  counted_terminates n1 c1 s r m q ->
  counted_terminates n2 c2 m q s' r' ->
  counted_terminates (n1 + n2) (Sequence c1 c2) s r s' r'.
Proof.
move=>d1; elim: d1=>[c s0 r0 s1 r1 st|
  n c c' s0 r0 s1 r1 s2 r2 st tail IH] d2.
- rewrite add1n; exact: (@CountedMore n2 (Sequence c c2) c2 s0 r0 s1 r1 s' r'
    (@StepSequenceDone c c2 s0 r0 s1 r1 st) d2).
- rewrite addSn; exact: (@CountedMore (n + n2) (Sequence c c2) (Sequence c' c2)
    s0 r0 s1 r1 s' r' (@StepSequenceMore c c2 c' s0 r0 s1 r1 st) (IH d2)).
Qed.

Theorem eval_route_counted rt c s r s' r' :
  eval_route rt c (s,r) = Some (s',r') ->
  counted_terminates (route_cost rt) c s r s' r'.
Proof.
elim: rt c s r s' r'=>[| |t v|rt IH|rt IH| |rt IH|r1 IH1 r2 IH2| | |t v]
  c s r s' r'.
- case: c=>//= [= <- <-]; apply: CountedDone; exact: StepSkip.
- case: c=>//= t x e; move=>[= <- <-]; apply: CountedDone; exact: StepAssign.
- case: c=>//= u x p; case: asboolP=>//= E; move=>[= <- <-].
  apply: CountedDone; exact: StepRandom.
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@CountedMore _ (Conditional b c1 c0) c1 s r s r s' r'
    (@StepIfTrue b c1 c0 s r Eb) (IH c1 s r s' r' H)).
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@CountedMore _ (Conditional b c1 c0) c0 s r s r s' r'
    (@StepIfFalse b c1 c0 s r Eb) (IH c0 s r s' r' H)).
- case: c=>//= b c0; case Eb: (eval b s)=>//=; move=>[= <- <-].
  exact: (@CountedDone _ _ _ _ _ (@StepWhileFalse b c0 s r Eb)).
- case: c=>//= b c0; case Eb: (eval b s)=>//= H.
  exact: (@CountedMore _ (While b c0) (Sequence c0 (While b c0)) s r s r s' r'
    (@StepWhileTrue b c0 s r Eb) (IH _ s r s' r' H)).
- case: c=>//= c1 c2; case E: (eval_route r1 c1 (s,r))=>[[m q]|] //= H.
  exact: (@counted_sequence _ _ c1 c2 s r m q s' r'
    (IH1 _ _ _ _ _ E) (IH2 _ _ _ _ _ H)).
- case: c=>//= u q phi; move=>[= <- <-]; apply: CountedDone; exact: StepInitialize.
- case: c=>//= u q U; move=>[= <- <-]; apply: CountedDone; exact: StepUnitary.
- case: c=>//= u z x q M; case: asboolP=>//= E; move=>[= <- <-].
  apply: CountedDone; exact: StepMeasure.
Qed.

Lemma step_route_cost_complete c s r c' s' r'
    (d : step c s r c' s' r') :
  forall rt o,
    (match c' with None => Some (s',r') | Some k => eval_route rt k (s',r') end) = Some o ->
    exists rr, eval_route rr c (s,r) = Some o /\
      route_cost rr = (match c' with None => 0 | Some _ => route_cost rt end).+1.
Proof.
induction d; move=>rt o H.
- by exists TR_skip.
- by exists TR_assign.
- exists (TR_random i); split=>//; rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- exists (TR_measure i); split=>//; rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- by exists TR_initial.
- by exists TR_unitary.
- have [r1 [Hr1 Hcost]] := IHd TR_skip (s',r') erefl.
  exists (TR_seqc r1 rt); split; first by rewrite /= Hr1.
  by rewrite /= Hcost add1n.
- case: rt H=>//= r1 r2.
  case E: (eval_route r1 c1' (s',r'))=>[[m q]|] //= H.
  have [r0 [Hr0 Hcost]] := IHd r1 (m,q) E.
  exists (TR_seqc r0 r2); split; first by rewrite /= Hr0.
  by rewrite /= Hcost addSn.
- exists (TR_cond1 rt); split=>//; by rewrite /= e.
- exists (TR_cond2 rt); split=>//; by rewrite /= e.
- exists (TR_while1 rt); split=>//; by rewrite /= e.
- exists TR_while0; split=>//; by rewrite /= e.
Qed.

Theorem counted_terminating_route n c s r s' r' :
  counted_terminates n c s r s' r' ->
  exists rt, eval_route rt c (s,r) = Some (s',r') /\ route_cost rt = n.
Proof.
elim=>[c0 s0 r0 s1 r1 st|
  n0 c0 c1 s0 r0 s1 r1 s2 r2 st tail [rt [Hrt Hcost]]].
- exact: step_route_cost_complete st TR_skip (s1,r1) erefl.
- have [rr [Hrr Hrrcost]] := @step_route_cost_complete _ _ _ _ _ _ st rt (s2,r2) Hrt.
  by exists rr; split=>//; rewrite Hrrcost Hcost.
Qed.

Theorem successful_route_exact_iff c s r s' r' n :
  (exists rt, eval_route rt c (s,r) = Some (s',r') /\ route_cost rt = n) <->
  inhabited (counted_terminates n c s r s' r').
Proof.
split.
- move=>[rt [Hrt <-]]; constructor; exact: eval_route_counted Hrt.
- move=>[d]; exact: counted_terminating_route d.
Qed.

Theorem successful_route_bounded_iff c s r s' r' n :
  (exists rt, eval_route rt c (s,r) = Some (s',r') /\ (route_cost rt <= n)%N) <->
  exists k, (k <= n)%N /\ inhabited (counted_terminates k c s r s' r').
Proof.
split.
- move=>[rt [Hrt Hcost]]; exists (route_cost rt); split=>//.
  constructor; exact: eval_route_counted Hrt.
- move=>[k [Hk [d]]]; have [rt [Hrt Hcost]] := counted_terminating_route d.
  by exists rt; split=>//; rewrite Hcost.
Qed.

End ClassicalOperationalRouteCost.
