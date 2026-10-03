(* Maximal computations, classical.pdf Definition 4.1. See PROOF_GAPS.md. *)
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
From quantum.example.classical Require Import language operational.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalComputations.
Import ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.

Record configuration := Configuration {
  residual : option command;
  classical : store;
  quantum : 'End(Hq)
}.

Definition well_formed x := quantum x \is denlf.

Definition live_step (x y : configuration) : Type :=
  match residual x with
  | Some c => (step c (classical x) (quantum x)
      (residual y) (classical y) (quantum y) * (quantum y != 0))%type
  | None => Empty_set
  end.

Definition terminal x : Prop := forall y, live_step x y -> False.

Inductive path : configuration -> configuration -> Type :=
  | PathRefl x : path x x
  | PathStep x y z : live_step x y -> path y z -> path x z.

Definition maximal_path x y := (path x y * terminal y)%type.
Definition finite_computation x y := (well_formed x * maximal_path x y)%type.

Definition infinite_path (f : nat -> configuration) :=
  forall n, live_step (f n) (f n.+1).

Record infinite_computation (x : configuration) := InfiniteComputation {
  infinite_configurations : nat -> configuration;
  infinite_initial : infinite_configurations 0%N = x;
  infinite_density : well_formed x;
  infinite_steps : infinite_path infinite_configurations
}.

Lemma step_zero c s r k s' r' (d : step c s r k s' r') :
  r = 0 -> r' = 0.
Proof.
induction d; move=>Hr; try exact Hr; try exact: IHd Hr.
- by rewrite Hr scaler0.
- by rewrite Hr linear0.
- by rewrite Hr linear0.
- by rewrite Hr linear0.
Qed.

Lemma terminates_zero c s r s' r' (d : terminates c s r s' r') :
  r = 0 -> r' = 0.
Proof.
elim: d=>[c0 s0 r0 s1 r1 st|c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] Hr.
- exact: step_zero st Hr.
- apply: IH; exact: step_zero st Hr.
Qed.

Lemma live_destination_nonzero x y : live_step x y -> quantum y != 0.
Proof. case: x=>[[c|] s r] //=; by case. Qed.

Lemma live_source_nonzero x y : live_step x y -> quantum x != 0.
Proof.
case: x=>[[c|] s r] //= [st nz].
apply/negP=>/eqP Hz; move: nz; rewrite (step_zero st Hz) eqxx.
by [].
Qed.

Lemma live_positive x y : live_step x y -> 0%:VF ⊑ quantum x -> 0%:VF ⊑ quantum y.
Proof.
case: x=>[[c|] s r]; last by case.
move=>[st _] Hr; exact: step_positive st Hr.
Qed.

Lemma live_density_preserved x y : live_step x y -> well_formed x -> well_formed y.
Proof.
case: x=>[[c|] s r]; last by case.
move=>[st _] Hr; exact: step_density st Hr.
Qed.

Lemma live_trace_le x y : live_step x y -> 0%:VF ⊑ quantum x ->
  \Tr (quantum y) <= \Tr (quantum x).
Proof.
case: x=>[[c|] s r]; last by case.
move=>[st _] Hr; exact: step_trace_le st Hr.
Qed.

Lemma path_positive x y : path x y -> 0%:VF ⊑ quantum x -> 0%:VF ⊑ quantum y.
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] Hx; apply: IH; exact: live_positive st Hx.
Qed.

Lemma path_density x y : path x y -> well_formed x -> well_formed y.
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] Hx; apply: IH; exact: live_density_preserved st Hx.
Qed.

Lemma path_trace_le x y : path x y -> 0%:VF ⊑ quantum x ->
  \Tr (quantum y) <= \Tr (quantum x).
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] Hx.
apply: le_trans (live_trace_le st Hx); apply: IH; exact: live_positive st Hx.
Qed.

Lemma path_nonzero x y : path x y -> quantum x != 0 -> quantum y != 0.
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] _; apply: IH; exact: live_destination_nonzero st.
Qed.

Lemma path_nonzero_or_refl x y : path x y -> x = y \/ quantum y != 0.
Proof.
elim=>[x0|x0 x1 x2 st p IH]; first by left.
right; exact: (path_nonzero p (live_destination_nonzero st)).
Qed.

Lemma terminal_none s r : terminal (Configuration None s r).
Proof. by move=>y; case. Qed.

Lemma terminal_abort s r : terminal (Configuration (Some Abort) s r).
Proof. move=>y [st _]; inversion st. Qed.

Lemma terminal_zero k s : terminal (Configuration k s 0).
Proof.
move=>y st; have H := live_source_nonzero st.
by move: H; rewrite /= eqxx.
Qed.

Definition completion x s' r' : Type :=
  match residual x with
  | Some c => terminates c (classical x) (quantum x) s' r'
  | None => (classical x = s') * (quantum x = r')
  end%type.

Lemma path_completion x y (p : path x y) s' r' :
  completion y s' r' -> completion x s' r'.
Proof.
elim: p=>[x0 //|x0 x1 x2 st p IH] H.
have H1 := IH H.
clear p IH H.
case: x0 st=>[[c|] s r] //=.
case: x1 H1=>[[c1|] s1 r1] /= H1 [st nz].
- exact: TerminatesMore st H1.
- case: H1=>Es Er; rewrite -Es -Er; exact: TerminatesDone st.
Qed.

Theorem path_terminates c s r s' r' :
  path (Configuration (Some c) s r) (Configuration None s' r') ->
  terminates c s r s' r'.
Proof.
move=>p; apply: (@path_completion _ _ p s' r'); by split.
Qed.

Theorem terminates_path c s r s' r' : terminates c s r s' r' -> r' != 0 ->
  path (Configuration (Some c) s r) (Configuration None s' r').
Proof.
elim=>[c0 s0 r0 s1 r1 st|c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] nz.
- apply: (@PathStep _ (Configuration None s1 r1)); last exact: PathRefl.
  exact: (st, nz).
- have nz1 : r1 != 0.
    apply/negP=>/eqP Hz; move: nz; rewrite (terminates_zero tail Hz) eqxx.
    by [].
  apply: (@PathStep _ (Configuration (Some c1) s1 r1)); last exact: IH nz.
  exact: (st, nz1).
Qed.

Theorem successful_maximal_iff c s r s' r' :
  inhabited (maximal_path (Configuration (Some c) s r) (Configuration None s' r'))
  <-> inhabited (terminates c s r s' r') /\ r' != 0.
Proof.
split.
- move=>[[p _]]; split; first by constructor; exact: path_terminates p.
  case: (path_nonzero_or_refl p)=>[E|//]; by inversion E.
- move=>[[t] nz]; constructor; split.
  + exact: terminates_path t nz.
  + exact: terminal_none.
Qed.

Lemma infinite_path_density f : infinite_path f -> well_formed (f 0%N) ->
  forall n, well_formed (f n).
Proof.
move=>st H0; elim=>[//|n IH]; exact: live_density_preserved (st n) IH.
Qed.

Lemma infinite_path_positive f : infinite_path f -> 0%:VF ⊑ quantum (f 0%N) ->
  forall n, 0%:VF ⊑ quantum (f n).
Proof.
move=>st H0; elim=>[//|n IH]; exact: live_positive (st n) IH.
Qed.

Lemma infinite_path_trace_step f : infinite_path f -> 0%:VF ⊑ quantum (f 0%N) ->
  forall n, \Tr (quantum (f n.+1)) <= \Tr (quantum (f n)).
Proof.
move=>st H0 n.
exact: (live_trace_le (st n) (infinite_path_positive st H0 n)).
Qed.

Lemma infinite_path_trace_le f : infinite_path f -> 0%:VF ⊑ quantum (f 0%N) ->
  forall n, \Tr (quantum (f n)) <= \Tr (quantum (f 0%N)).
Proof.
move=>st H0; elim=>[//|n IH].
exact: le_trans (infinite_path_trace_step st H0 n) IH.
Qed.

Lemma infinite_not_terminal f : infinite_path f -> forall n, ~ terminal (f n).
Proof. by move=>st n T; exact: T _ (st n). Qed.

Definition true_skip_loop := While (EConst true) Skip.
Definition true_skip_configurations s r n :=
  Configuration (Some (if odd n then Sequence Skip true_skip_loop else true_skip_loop)) s r.

Lemma true_skip_path s r : r != 0 -> infinite_path (true_skip_configurations s r).
Proof.
move=>nz n; rewrite /true_skip_configurations /live_step /=.
case: (odd n)=>/=; split=>//.
- apply: StepSequenceDone; exact: StepSkip.
- exact: (@StepWhileTrue (EConst true) Skip s r erefl).
Qed.

Definition true_skip_infinite s r (Hr : r \is denlf) (nz : r != 0) :
  infinite_computation (Configuration (Some true_skip_loop) s r) :=
  @InfiniteComputation _ (true_skip_configurations s r) erefl Hr (true_skip_path s nz).

Lemma infinite_computation_density x (p : infinite_computation x) n :
  well_formed (infinite_configurations p n).
Proof.
have H0 : well_formed (infinite_configurations p 0%N).
  by rewrite infinite_initial; exact: infinite_density.
exact: (infinite_path_density (infinite_steps p) H0 n).
Qed.

Lemma finite_computation_density x y : finite_computation x y -> well_formed y.
Proof. move=>[Hx [p _]]; exact: path_density p Hx. Qed.

Definition abort_computation s r (Hr : r \is denlf) :
  finite_computation (Configuration (Some Abort) s r) (Configuration (Some Abort) s r) :=
  (Hr, (PathRefl _, @terminal_abort s r)).

Theorem successful_route_iff c s r s' r' :
  inhabited (maximal_path (Configuration (Some c) s r) (Configuration None s' r')) <->
  exists rt, ClassicalOperational.eval_route rt c (s,r) = Some (s',r') /\ r' != 0.
Proof.
rewrite successful_maximal_iff; split.
- move=>[[d] nz]; have [rt Hrt] := ClassicalOperational.terminating_route d.
  by exists rt.
- move=>[rt [Hrt nz]]; split=>//; constructor.
  exact: ClassicalOperational.eval_route_sound Hrt.
Qed.

End ClassicalComputations.
