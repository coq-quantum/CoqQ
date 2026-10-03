(* Distributive: operational. See README.md and PROOF_NOTES.md. *)
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
From mathcomp.classical Require Import boolp classical_sets functions.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From Stdlib Require Import String.
From quantum Require Import mcextra extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum Require Import notation mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum Require Import notation mxpred extnum ctopology hermitian quantum hspace summable qreg qmem.
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.example.distributive Require Import language.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module DistributedOperational.
(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Record family (X : Type) := Family {
  branch_index : choiceType;
  branch_weight : branch_index -> C;
  branch_value : branch_index -> X
}.
Arguments branch_index {X} _.
Arguments branch_weight {X} _ _.
Arguments branch_value {X} _ _.

Definition family_mass {X} (mu : family X) := sum (branch_weight mu).
Definition probability_family {X} (mu : family X) :=
  summable (branch_weight mu) /\
  (forall i, 0 <= branch_weight mu i) /\ family_mass mu = 1.
Definition admissible_family {X} (mu : family X) :=
  summable (branch_weight mu) /\ forall i, 0 <= branch_weight mu i.
Definition certain {X} (x : X) : family X :=
  @Family X (Choice.clone unit _) (fun _ => 1) (fun _ => x).
Definition fmap {X Y} (f : X -> Y) (mu : family X) : family Y :=
  @Family Y (branch_index mu) (branch_weight mu) (fun i => f (branch_value mu i)).

Lemma certain_probability X (x : X) : probability_family (certain x).
Proof.
split; first exact: fin_dom_summable.
split=>[i|]; first exact: ler01.
by rewrite /family_mass /= fin_dom_sum (bigD1 tt) //= big1 ?addr0 // => [[]].
Qed.
Lemma fmap_probability X Y (f : X -> Y) mu :
  probability_family mu -> probability_family (fmap f mu).
Proof. by []. Qed.
Lemma fmap_mass X Y (f : X -> Y) mu : family_mass (fmap f mu) = family_mass mu.
Proof. by []. Qed.

Definition probability_distribution X (mu : family X)
    (H : probability_family mu) : Distr (branch_index mu).
Proof.
apply: (VDistr.build (f := Summable.build (proj1 H)) (proj1 (proj2 H))).
by change (`|family_mass mu| <= 1); rewrite (proj2 (proj2 H)) normr1.
Defined.

Lemma probability_distributionE X (mu : family X) (H : probability_family mu) i :
  probability_distribution H i = branch_weight mu i.
Proof. by []. Qed.

Definition local_configuration := (statement * option cmem * 'End(Hq))%type.
Definition local_config s m rho : local_configuration := (s,m,rho).
Definition append s t := if s is Finished then t else Sequence s t.
Definition append_configuration t (c : local_configuration) :=
  local_config (append c.1.1 t) c.1.2 c.2.
Definition measurement_branch {t u : qType} (x : CL.variable (QType t))
    (q : wf_qreg u) (M : mexpr (eval_qtype t) (eval_qtype u))
    (m : cmem) (rho : 'End(Hq)) : family local_configuration :=
  let R := fun i => ClassicalSemantics.measurement_branches q M m i rho in
  let p := fun i => \Tr (R i) in
  @Family _ (eval_qtype t) p (fun i =>
    local_config Finished (Some (m.[x <- i])%M)
      (if 0 < p i then (p i)^-1 *: R i else rho)).

Lemma measurement_probability_nonnegative t u (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho : rho \is den1lf ->
    forall i, 0 <= \Tr (ClassicalSemantics.measurement_branches q M m i rho).
Proof. by move=>Pr i; apply: psdlf_trlf; apply: cp_psdP; apply: den1lf_psd. Qed.

Lemma measurement_probabilities_summable t u (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho :
    summable (fun i => \Tr (ClassicalSemantics.measurement_branches q M m i rho)).
Proof. exact: fin_dom_summable. Qed.

Lemma measurement_probability_total t u (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho :
    sum (fun i => \Tr (ClassicalSemantics.measurement_branches q M m i rho)) = \Tr rho.
Proof.
rewrite -cvg_linear_sum.
  apply: sum_summable_soE_is_cvg; exact: summable_cvg.
rewrite -(sum_summable_soE rho
  (summable_cvg (f := ClassicalSemantics.measurement_branches q M m))).
by apply/tpmapP/ClassicalSemantics.measurement_complete.
Qed.

Lemma measurement_branch_probability t u (x : CL.variable (QType t)) (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho : rho \is den1lf ->
    probability_family (measurement_branch x q M m rho).
Proof.
move=>Pr; split; first exact: measurement_probabilities_summable.
split; first exact: measurement_probability_nonnegative.
by rewrite /family_mass /measurement_branch /= measurement_probability_total den1lf_trlf.
Qed.

Lemma measurement_branch_normalized t u (x : CL.variable (QType t)) (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho i : rho \is den1lf ->
    (branch_value (measurement_branch x q M m rho) i).2 \is den1lf.
Proof.
move=>Pr; rewrite /measurement_branch /=; case: ifP=>P; last exact: Pr.
apply/den1lfP; split.
  apply: psdlfZ; first by rewrite invr_ge0; exact: ltW P.
  by apply: cp_psdP; exact: den1lf_psd Pr.
by rewrite linearZ /= mulVf ?gt_eqF.
Qed.

(* The corrected finite interchange argument for Appendix C.1 uses joint
   branch weights. Individual conditional probabilities need not be equal. *)
Lemma normalized_joint_weight (E F : 'SO(Hq)) rho :
  \Tr (E rho) != 0 ->
  \Tr (E rho) * \Tr (F ((\Tr (E rho))^-1 *: E rho)) = \Tr (F (E rho)).
Proof. by move=>P; rewrite !linearZ /= mulrA mulfV ?mul1r. Qed.

Lemma commuting_joint_state (E F : 'SO(Hq)) rho :
  E :o F = F :o E -> F (E rho) = E (F rho).
Proof.
move=>H; have := congr1 (fun Q : 'SO(Hq) => Q rho) H.
by rewrite !soE=>->.
Qed.

Lemma commuting_joint_weight (E F : 'SO(Hq)) rho :
  E :o F = F :o E -> \Tr (F (E rho)) = \Tr (E (F rho)).
Proof. by move=>H; rewrite (commuting_joint_state rho H). Qed.

Inductive local_step : local_configuration -> family local_configuration -> Prop :=
| StepSkip m rho :
    local_step (local_config (Atomic ASkip) (Some m) rho)
      (certain (local_config Finished (Some m) rho))
| StepAbort m rho :
    local_step (local_config (Atomic AAbort) (Some m) rho)
      (certain (local_config Finished None rho))
| StepAssign t (x : CL.variable t) e m rho :
    local_step (local_config (Atomic (AAssign x e)) (Some m) rho)
      (certain (local_config Finished (Some (m.[x <- eval e m])%M) rho))
| StepRandom t (x : CL.variable t) mu m rho :
    local_step (local_config (Atomic (@ARandom t x mu)) (Some m) rho)
      (@Family _ (CL.value t) (fun v => CL.probability_mass mu m v)
        (fun v => local_config Finished (Some (m.[x <- v])%M) rho))
| StepInitial t (q : wf_qreg t) phi m rho :
    local_step (local_config (Atomic (AInitial q phi)) (Some m) rho)
      (certain (local_config Finished (Some m)
        (liftfso (initialso (tv2v q (eval phi m))) rho)))
| StepUnitary t (q : wf_qreg t) (U : uexpr (eval_qtype t)) m rho :
    local_step (local_config (Atomic (AUnitary q U)) (Some m) rho)
      (certain (local_config Finished (Some m)
        (liftfso (formso (tf2f q q (eval U m))) rho)))
| StepMeasure t u (x : CL.variable (QType t)) (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho :
    local_step (local_config (Atomic (AMeasure x q M)) (Some m) rho)
      (measurement_branch x q M m rho)
| StepSequence s t m rho mu :
    local_step (local_config s (Some m) rho) mu ->
    local_step (local_config (Sequence s t) (Some m) rho)
      (fmap (append_configuration t) mu)
| StepAlternative n (g : 'I_n -> expression bool) b (i : 'I_n) m rho :
    eval (g i) m ->
    local_step (local_config (Alternative g b) (Some m) rho)
      (certain (local_config (b i) (Some m) rho))
| StepAlternativeFail n (g : 'I_n -> expression bool) b m rho :
    [forall i, ~~ eval (g i) m] ->
    local_step (local_config (Alternative g b) (Some m) rho)
      (certain (local_config Finished None rho))
| StepRepetition n (g : 'I_n -> expression bool) b (i : 'I_n) m rho :
    eval (g i) m ->
    local_step (local_config (Repetition g b) (Some m) rho)
      (certain (local_config (Sequence (b i) (Repetition g b)) (Some m) rho))
| StepRepetitionDone n (g : 'I_n -> expression bool) b m rho :
    [forall i, ~~ eval (g i) m] ->
    local_step (local_config (Repetition g b) (Some m) rho)
      (certain (local_config Finished (Some m) rho)).

Lemma local_step_probability c mu : local_step c mu -> c.2 \is den1lf ->
  probability_family mu.
Proof.
move=>H; induction H; move=>Pr; try exact: certain_probability.
- split; first exact: summable_mu.
  split; first exact: ge0_mu.
  exact: CL.probability_normalized.
- exact: measurement_branch_probability.
- apply: fmap_probability; exact: IHlocal_step.
Qed.

Lemma local_step_normalized c mu : local_step c mu -> c.2 \is den1lf ->
  forall i, (branch_value mu i).2 \is den1lf.
Proof.
move=>H; induction H; move=>Pr outcome;
  cbn [branch_value certain fmap append_configuration local_config];
  try exact Pr.
- exact: (@qc_den1lf Hq Hq
    (liftfso (initialso (tv2v q (eval phi m)))) (Den1Lf_Build Pr)).
- exact: (@qc_den1lf Hq Hq
    (liftfso (formso (tf2f q q (eval U m)))) (Den1Lf_Build Pr)).
- exact: measurement_branch_normalized.
- exact: IHlocal_step.
Qed.

Lemma failure_has_no_local_step s rho mu :
  ~ local_step (local_config s None rho) mu.
Proof. by move=>H; inversion H. Qed.
Lemma finished_has_no_local_step m rho mu :
  ~ local_step (local_config Finished m rho) mu.
Proof. by move=>H; inversion H. Qed.

(* A process executes initialization once, then alternates between a main-loop
   rendezvous and its selected sequential body. There is no nested parallelism. *)
Inductive control := Executing of statement | Waiting | Stopped.
HB.instance Definition _ := gen_eqMixin control.
HB.instance Definition _ := gen_choiceMixin control.
Definition after_local (p : process) (s : statement) :=
  if s is Finished then
    if branch_count p is 0%N then Stopped else Waiting
  else Executing s.
Definition global_configuration n :=
  (('I_n -> control) * option cmem * 'End(Hq))%type.
Definition global_config n (pc : 'I_n -> control) m rho : global_configuration n :=
  (pc,m,rho).
Definition replace n (pc : 'I_n -> control) (i : 'I_n) c :=
  fun j => if j == i then c else pc j.
Definition lift_local n (p : 'I_n -> process) pc (i : 'I_n)
    (c : local_configuration) :=
  global_config (replace pc i (after_local (p i) c.1.1)) c.1.2 c.2.

Inductive global_step n (p : 'I_n -> process) :
    global_configuration n -> family (global_configuration n) -> Prop :=
| StepParallel pc m rho i s mu :
    pc i = Executing s ->
    local_step (local_config s (Some m) rho) mu ->
    global_step p (global_config pc (Some m) rho) (fmap (lift_local p pc i) mu)
| StepProcessDone pc m rho i :
    pc i = Waiting ->
    [forall j, ~~ eval (process_guard (p i) j) m] ->
    global_step p (global_config pc (Some m) rho)
      (certain (global_config (replace pc i Stopped) (Some m) rho))
| StepCommunication pc m rho (i k : 'I_n) j l t (x : CL.variable t) e :
    (i < k)%N -> pc i = Waiting -> pc k = Waiting ->
    eval (process_guard (p i) j) m -> eval (process_guard (p k) l) m ->
    matches (process_io (p i) j) (process_io (p k) l) (AAssign x e) ->
    global_step p (global_config pc (Some m) rho)
      (certain (global_config
        (replace (replace pc i (Executing (process_body (p i) j)))
          k (Executing (process_body (p k) l)))
        (Some (m.[x <- eval e m])%M) rho)).

Definition terminal n (p : 'I_n -> process) (c : global_configuration n) :=
  forall mu, ~ global_step p c mu.
Definition successful n (c : global_configuration n) :=
  (forall i, c.1.1 i = Stopped) /\ exists m, c.1.2 = Some m.
Definition deadlock n (p : 'I_n -> process) (c : global_configuration n) :=
  terminal p c /\ ~ successful c /\ exists m, c.1.2 = Some m.
Definition initial_configuration n (p : 'I_n -> process) m rho :=
  global_config (fun i => Executing (initialization (p i))) (Some m) rho.

Lemma failure_terminal n (p : 'I_n -> process) pc rho :
  terminal p (global_config pc None rho).
Proof. by move=>mu H; inversion H. Qed.

Lemma stopped_terminal n (p : 'I_n -> process) m rho :
  terminal p (global_config (fun _ => Stopped) m rho).
Proof.
move=>mu H; inversion H; subst; discriminate.
Qed.

Lemma unmatched_single_process_deadlock (p : 'I_1 -> process) m rho :
  (exists j, eval (process_guard (p ord0) j) m) ->
  deadlock p (global_config (fun _ => Waiting) (Some m) rho).
Proof.
move=>[j Hj]; split; last split.
- move=>mu H; inversion H; subst; try discriminate.
  + by match goal with H : is_true [forall _, _] |- _ =>
      move: H; rewrite (ord1 i); move=>/forallP/(_ j); rewrite Hj
    end.
  + by match goal with H : is_true (_ < _)%N |- _ =>
      move: H; rewrite !ord1 ltnn
    end.
- by move=>[H _]; move: (H ord0).
- by exists m.
Qed.

Lemma replace_same n (pc : 'I_n -> control) i c : replace pc i c i = c.
Proof. by rewrite /replace eqxx. Qed.
Lemma replace_other n (pc : 'I_n -> control) i j c :
  j != i -> replace pc i c j = pc j.
Proof. by move=>/negPf H; rewrite /replace H. Qed.

Lemma global_step_probability n (p : 'I_n -> process) c mu :
  global_step p c mu -> c.2 \is den1lf -> probability_family mu.
Proof.
move=>H; case: H=>[pc m rho i s nu Hi Hs|pc m rho i Hi Hg|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hio] Pr;
  try exact: certain_probability.
apply: fmap_probability; exact: local_step_probability Hs Pr.
Qed.

Lemma global_step_normalized n (p : 'I_n -> process) c mu :
  global_step p c mu -> c.2 \is den1lf ->
  forall i, (branch_value mu i).2 \is den1lf.
Proof.
move=>H; case: H=>[pc m rho i s nu Hi Hs|pc m rho i Hi Hg|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hio] Pr a //=.
change ((branch_value nu a).2 \is den1lf).
exact: (local_step_normalized Hs Pr a).
Qed.

(* Equality of indexed discrete distributions is equality of expectations of
   bounded scalar observables. All sums remain over the small support index
   types, even when configurations contain higher-order syntax. Indicator
   observables recover the summed weights of each configuration. *)
Definition family_at {X} (mu : family X) (x : X) :=
  sum (fun i => if asbool (branch_value mu i = x) then branch_weight mu i else 0).
Definition family_observe {X} (mu : family X) (f : X -> C) :=
  sum (fun i => branch_weight mu i * f (branch_value mu i)).
Definition same_distribution {X} (mu nu : family X) :=
  forall f : X -> C, (exists M, forall x, `|f x| <= M) ->
    family_observe mu f = family_observe nu f.

Definition bind_index {X Y} (mu : family X)
    (nu : branch_index mu -> family Y) :=
  {i : branch_index mu & branch_index (nu i)}.
Arguments bind_index {X Y} mu nu.
HB.instance Definition _ X Y (mu : family X) (nu : branch_index mu -> family Y) :=
  @gen_eqMixin (bind_index mu nu).
HB.instance Definition _ X Y (mu : family X) (nu : branch_index mu -> family Y) :=
  @gen_choiceMixin (bind_index mu nu).

Definition bind_family {X Y} (mu : family X)
    (nu : branch_index mu -> family Y) : family Y :=
  @Family Y (Choice.clone (bind_index mu nu) _)
    (fun ij => branch_weight mu (projT1 ij) *
      branch_weight (nu (projT1 ij)) (projT2 ij))
    (fun ij => branch_value (nu (projT1 ij)) (projT2 ij)).
Arguments bind_family {X Y} mu nu.

(* For each support configuration, one scheduler transition is chosen.
   Terminals stutter. Reindexing or merging equal configurations is permitted
   by same_distribution, so the representation does not affect the relation. *)
Definition distribution_step n (p : 'I_n -> process)
    (mu nu : family (global_configuration n)) :=
  admissible_family nu /\
  exists next : branch_index mu -> family (global_configuration n),
    (forall i, 0 < branch_weight mu i ->
      (terminal p (branch_value mu i) /\
        next i = certain (branch_value mu i)) \/
      global_step p (branch_value mu i) (next i)) /\
    same_distribution nu (bind_family mu next).

Record computation n (p : 'I_n -> process) (c : global_configuration n) :=
  Computation {
    computation_stage : nat -> family (global_configuration n);
    computation_initial : same_distribution (computation_stage 0%N) (certain c);
    computation_probability : forall k, probability_family (computation_stage k);
    computation_normalized : forall k i,
      0 < branch_weight (computation_stage k) i ->
      (branch_value (computation_stage k) i).2 \is den1lf;
    computation_advances : forall k,
      distribution_step p (computation_stage k) (computation_stage k.+1)
  }.

Definition successful_at n (c : global_configuration n) (m : cmem) :=
  if c.1.2 is Some s then
    (s == m) && [forall i, asbool (c.1.1 i = Stopped)]
  else false.
Definition successful_result n (mu : family (global_configuration n)) (m : cmem) :=
  sum (fun i => if successful_at (branch_value mu i) m
    then branch_weight mu i *: (branch_value mu i).2 else 0).

(* The raw limit is an auxiliary total function. Semantic results below require
   actual convergence, so an unspecified value of limn cannot be a result.
   Existence of limits and independence of schedulers remain separate theorems. *)
Definition computed_result n (p : 'I_n -> process) c (pi : computation p c) m :=
  limn (fun k => successful_result (computation_stage pi k) m).
Definition computes n (p : 'I_n -> process) c (pi : computation p c)
    (d : cmem -> 'End(Hq)) :=
  forall m, (successful_result (computation_stage pi k) m @[k --> \oo] --> d m)%classic.

Lemma computes_result n (p : 'I_n -> process) c (pi : computation p c) d :
  computes pi d -> computed_result pi = d.
Proof. move=>H; apply/funext=>m; exact: cvg_lim (H m). Qed.

Lemma computes_unique n (p : 'I_n -> process) c (pi : computation p c) d e :
  computes pi d -> computes pi e -> d = e.
Proof. by move=>/computes_result <- /computes_result <-. Qed.

Definition denotational_results n (p : 'I_n -> process) c :=
  [set d : cmem -> 'End(Hq) | exists pi : computation p c, computes pi d]%classic.
End DistributedOperational.


Module DistributedDistribution.
(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Import Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Notation C := hermitian.C.

Lemma probability_family_nonempty X (mu : family X) :
  probability_family mu -> exists i : branch_index mu, True.
Proof.
move=>H; case: (pselect (exists i : branch_index mu, True))=>// E.
have Z : forall i : branch_index mu, branch_weight mu i = 0.
  by move=>i; exfalso; apply: E; exists i.
move: (proj2 (proj2 H)); rewrite /family_mass (eq_sum Z) summable_sum_cst0.
by move/eqP; rewrite eq_sym oner_eq0.
Qed.

Section Grouping.
Context {X : choiceType} (mu : family X).
Hypothesis Hs : summable (branch_weight mu).

Lemma family_at_sdlet : family_at mu =
    sdlet_def (branch_value mu) (Summable.build Hs).
Proof.
apply/funext=>x; rewrite /family_at /sdlet_def; apply: eq_sum=>i.
rewrite /sunit_def /=; case: asboolP=>E; case: eqP=>F //.
- by exfalso; apply: F; symmetry.
- by exfalso; apply: E; symmetry.
Qed.

Lemma family_at_summable : summable (family_at mu).
Proof. rewrite family_at_sdlet; exact: summablefP. Qed.

Lemma family_at_mass : sum (family_at mu) = family_mass mu.
Proof. by rewrite family_at_sdlet sdlet_sum. Qed.

End Grouping.

Lemma family_observe_one X (mu : family X) :
  family_observe mu (fun _ => 1) = family_mass mu.
Proof. by apply: eq_sum=>i; rewrite mulr1. Qed.

Lemma family_observe_indicator X (mu : family X) x :
  family_observe mu (fun y => if asbool (y = x) then 1 else 0) = family_at mu x.
Proof.
apply: eq_sum=>i; case: asbool; by rewrite ?mulr1 ?mulr0.
Qed.

Lemma same_distribution_at X (mu nu : family X) :
  same_distribution mu nu -> forall x, family_at mu x = family_at nu x.
Proof.
move=>E x; rewrite -!family_observe_indicator; apply: E; exists 1=>y.
by case: asbool; rewrite ?normr0 ?normr1.
Qed.

Lemma same_distribution_mass X (mu nu : family X) :
  same_distribution mu nu -> family_mass mu = family_mass nu.
Proof.
move=>E; rewrite -!family_observe_one; apply: E; exists 1=>x; by rewrite normr1.
Qed.

Lemma same_distribution_probability X (mu nu : family X) :
  probability_family mu -> admissible_family nu ->
  same_distribution nu mu -> probability_family nu.
Proof.
move=>[Hm [Hpos Hmass]] [Hn HnPos] E; split=>//; split=>//.
by rewrite (same_distribution_mass E).
Qed.

Lemma masked_summable (I : choiceType) (f : I -> C) (P : pred I) :
  summable f -> summable (fun i => if P i then f i else 0).
Proof.
move=>/summableW [M HM]; exists M; near=>A.
apply: (le_trans (y := psum (fun i => `|f i|) A)); last exact: HM.
by apply: ler_sum=>i _; rewrite /normf; case: (P (val i)); rewrite ?normr0.
Unshelve. end_near.
Qed.

Lemma nonnegative_sum_ge_term (I : choiceType) (f : I -> C) i :
  summable f -> (forall j, 0 <= f j) -> f i <= sum f.
Proof.
move=>Hs Hp; apply: etlim_ge_near; first by apply: norm_bounded_cvg.
exists ([fset i]%fset)=>// A /= HA; rewrite -[f i]psum1.
by apply: psum_ler=>// j _; apply: Hp.
Qed.

Lemma family_at_ge_branch X (mu : family X) : probability_family mu ->
  forall i, branch_weight mu i <= family_at mu (branch_value mu i).
Proof.
move=>[Hs [Hp Hm]] i; rewrite /family_at.
have Hs' := masked_summable (fun j => asbool (branch_value mu j = branch_value mu i)) Hs.
have := nonnegative_sum_ge_term i Hs' (fun j =>
  match asbool (branch_value mu j = branch_value mu i) as b return
    0 <= (if b then branch_weight mu j else 0) with
  | true => Hp j | false => lexx 0 end).
by rewrite asboolT.
Qed.

Lemma family_at_positive X (mu : family X) x : probability_family mu ->
  0 < family_at mu x ->
  exists i, branch_value mu i = x /\ 0 < branch_weight mu i.
Proof.
move=>[Hs [Hp Hm]] Hx.
case: (pselect (exists i, branch_value mu i = x /\ 0 < branch_weight mu i))=>// H.
have Z : forall i, (if asbool (branch_value mu i = x) then branch_weight mu i else 0) = 0.
  move=>i; case: asboolP=>// E.
  have N : ~~ (0 < branch_weight mu i).
    by apply/negP=>Hi; apply: H; exists i.
  by move: (Hp i); rewrite le_eqVlt (negbTE N) orbF eq_sym=>/eqP.
by move: Hx; rewrite /family_at (eq_sum Z) summable_sum_cst0 ltxx.
Qed.

Lemma same_distribution_support X (mu nu : family X) (P : X -> Prop) :
  probability_family mu -> probability_family nu -> same_distribution nu mu ->
  (forall i, 0 < branch_weight mu i -> P (branch_value mu i)) ->
  forall j, 0 < branch_weight nu j -> P (branch_value nu j).
Proof.
move=>Hm Hn E HP j Hj.
have Hmass : 0 < family_at mu (branch_value nu j).
  rewrite -(same_distribution_at E); exact: (lt_le_trans Hj (family_at_ge_branch Hn j)).
have [i [Ei Hi]] := family_at_positive Hm Hmass.
by rewrite -Ei; apply: HP.
Qed.

Definition transport_index (I : Type) (J : I -> Type) i j (E : i = j) (x : J i) : J j :=
  match E in _ = j return J j with erefl => x end.

Section Bind.
Context {X Y : Type} (mu : family X) (nu : branch_index mu -> family Y).

Definition bind_encode (i : branch_index mu) (j : branch_index (nu i)) : bind_index mu nu :=
  existT _ i j.
Arguments bind_encode i j : clear implicits.

Definition bind_decode (i : branch_index mu) (ij : bind_index mu nu) :
    option (branch_index (nu i)) :=
  match asboolP (projT1 ij = i) with
  | ReflectT E => Some (transport_index E (projT2 ij))
  | ReflectF _ => None
  end.

Lemma bind_encodeK i : pcancel (bind_encode i) (bind_decode i).
Proof.
move=>j; rewrite /bind_encode /bind_decode /=; case: asboolP=>[E|//].
by rewrite (eq_irrelevance E erefl).
Qed.

Lemma bind_decodeK i : ocancel (bind_decode i) (bind_encode i).
Proof.
case=>k j; rewrite /bind_decode /=; case: asboolP=>//= E.
by case: i / E.
Qed.

Definition bind_row (i : branch_index mu) (ij : bind_index mu nu) : C :=
  oapp (fun j => branch_weight mu i * branch_weight (nu i) j) 0 (bind_decode i ij).

Lemma bind_rowE i ij : bind_row i ij =
  if i == projT1 ij then branch_weight (bind_family mu nu) ij else 0.
Proof.
case: ij=>k j; rewrite /bind_row /bind_decode /=.
case: eqP=>[->|E]; case: asboolP=>[F|F] //=.
- by rewrite (eq_irrelevance F erefl).
- by exfalso; apply: E; symmetry.
Qed.

Hypothesis Hmu : probability_family mu.
Hypothesis Hnu : forall i, 0 < branch_weight mu i -> probability_family (nu i).

Lemma bind_row_zero i : branch_weight mu i = 0 -> forall ij, bind_row i ij = 0.
Proof. by move=>H ij; rewrite /bind_row; case: bind_decode=>//= j; rewrite H mul0r. Qed.

Lemma bind_row_bound i A : psum (fun ij => `|bind_row i ij|) A <= branch_weight mu i.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have [j0 _] := probability_family_nonempty Hi.
  rewrite (psum_Sj (@bind_encodeK i) (@bind_decodeK i) j0).
    by move=>ij H; rewrite /bind_row H /= normr0.
  rewrite /psum.
  under eq_bigr do rewrite /bind_row bind_encodeK /= normrM !ger0_norm
    ?(proj1 (proj2 Hmu)) ?(proj1 (proj2 Hi)) //.
  rewrite -mulr_sumr.
  apply: (le_trans (y := branch_weight mu i * 1)); last by rewrite mulr1.
  apply: ler_wpM2l; first exact: (proj1 (proj2 Hmu)).
  exact: (psum_le1_mu (probability_distribution Hi)).
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by rewrite Z /psum big1 // =>j _; rewrite bind_row_zero // normr0.
Qed.

Lemma bind_row_sum i : sum (bind_row i) = branch_weight mu i.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have Er : (bind_row i \o bind_encode i)%FUN =
      (fun j => branch_weight mu i * branch_weight (nu i) j).
    by apply/funext=>j; rewrite /= /bind_row bind_encodeK.
  rewrite (sum_reindex (@bind_encodeK i) (@bind_decodeK i)).
    by move=>ij H; rewrite /bind_row H.
    rewrite Er; exact: summable_funZ (proj1 Hi).
  rewrite Er.
  change (sum (branch_weight mu i *: Summable.build (proj1 Hi)) = branch_weight mu i).
  rewrite summable_sumZ.
  change (branch_weight mu i * family_mass (nu i) = branch_weight mu i).
  by rewrite (proj2 (proj2 Hi)) mulr1.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  rewrite (eq_sum (g := fun _ => 0)); first exact: bind_row_zero Z.
  by rewrite summable_sum_cst0.
Qed.

Lemma bind_rectangle_bound A B :
  psum (fun i => psum (fun ij => `|bind_row i ij|) B) A <= 1.
Proof.
apply: (le_trans (y := psum (branch_weight mu) A)).
  by apply: ler_sum=>i _; apply: bind_row_bound.
exact: (psum_le1_mu (probability_distribution Hmu)).
Qed.

Lemma bind_column_sum ij : sum (fun i => bind_row i ij) =
    branch_weight (bind_family mu nu) ij.
Proof.
rewrite (fin_supp_sum (S := [fset projT1 ij])) ?psum1 ?bind_rowE ?eqxx //.
by move=>i; rewrite inE=>/negPf H; rewrite bind_rowE H.
Qed.

Lemma bind_family_probability : probability_family (bind_family mu nu).
Proof.
have rect : exists M, forall A B,
    psum (fun i => psum (fun ij => `|bind_row i ij|) B) A <= M.
  by exists 1=>A B; apply: bind_rectangle_bound.
have revrect : exists M, forall B A,
    psum (fun ij => psum (fun i => `|bind_row i ij|) A) B <= M.
  exists 1=>B A; rewrite /psum exchange_big; apply: bind_rectangle_bound.
have [_ [_ [Hs _]]] := pseries_ubounded_cvg revrect.
split.
- have E : (fun ij => sum (fun i => bind_row i ij)) =
      branch_weight (bind_family mu nu).
    by apply/funext=>ij; apply: bind_column_sum.
  by rewrite -E.
split.
- case=>i j /=; case P: (0 < branch_weight mu i).
  + apply: mulr_ge0; first exact: (proj1 (proj2 Hmu)).
    exact: (proj1 (proj2 (@Hnu i P))).
  + have Z : branch_weight mu i = 0.
      by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
    by rewrite Z mul0r.
- rewrite /family_mass -(proj2 (proj2 Hmu)).
  transitivity (sum (fun i => sum (bind_row i))).
  + rewrite (pseries2_exchange_lim rect).
    by apply: eq_sum=>ij; rewrite bind_column_sum.
  + by apply: eq_sum=>i; rewrite bind_row_sum.
Qed.

End Bind.

Lemma distribution_step_probability n (p : 'I_n -> process)
    (mu nu : family (global_configuration n)) :
  distribution_step p mu nu -> probability_family mu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  probability_family nu.
Proof.
move=>[Ha [next [Hnext E]]] Hm Hr.
have Hbind : probability_family (bind_family mu next).
  apply: bind_family_probability Hm _=>i Hi.
  case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: (global_step_probability Hs (Hr i Hi)).
exact: (same_distribution_probability Hbind Ha E).
Qed.

Lemma distribution_step_normalized n (p : 'I_n -> process)
    (mu nu : family (global_configuration n)) :
  distribution_step p mu nu -> probability_family mu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  forall j, 0 < branch_weight nu j -> (branch_value nu j).2 \is den1lf.
Proof.
move=>Hstep Hm Hr.
have Hn := distribution_step_probability Hstep Hm Hr.
case: Hstep=>Ha [next [Hnext E]].
have Hbind : probability_family (bind_family mu next).
  apply: bind_family_probability Hm _=>i Hi.
  case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: (global_step_probability Hs (Hr i Hi)).
apply: (same_distribution_support (P := fun c : global_configuration n => c.2 \is den1lf) Hbind Hn E).
move=>[i j] /= Hij.
case P: (0 < branch_weight mu i).
- have N : forall k, (branch_value (next i) k).2 \is den1lf.
    case: (Hnext i P)=>[[Ht ->]|Hs].
    + by move=>k; exact: Hr.
    + exact: global_step_normalized Hs (Hr i P).
  exact: N.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hm) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by move: Hij; rewrite Z mul0r ltxx.
Qed.

Section CanonicalComputation.
Context n (p : 'I_n -> process).

Definition canonical_successor (c : global_configuration n) :
    family (global_configuration n) :=
  match pselect (exists mu, global_step p c mu) with
  | left H => proj1_sig (cid H)
  | right _ => certain c
  end.

Lemma canonical_successor_step c :
  (terminal p c /\ canonical_successor c = certain c) \/
  global_step p c (canonical_successor c).
Proof.
rewrite /canonical_successor; case: pselect=>[H|H].
- right; exact: (proj2_sig (cid H)).
- left; split=>// mu Hmu; apply: H; by exists mu.
Qed.

Lemma canonical_successor_probability c : c.2 \is den1lf ->
    probability_family (canonical_successor c).
Proof.
move=>Hc; case: (canonical_successor_step c)=>[[Ht ->]|Hs].
- exact: certain_probability.
- exact: global_step_probability Hs Hc.
Qed.

Lemma canonical_successor_normalized c : c.2 \is den1lf ->
    forall i, (branch_value (canonical_successor c) i).2 \is den1lf.
Proof.
move=>Hc; case: (canonical_successor_step c)=>[[Ht ->]|Hs].
- by move=>i.
- exact: global_step_normalized Hs Hc.
Qed.

Fixpoint canonical_stage (c : global_configuration n) k : family (global_configuration n) :=
  match k with
  | 0%N => certain c
  | k.+1 => bind_family (canonical_stage c k)
      (fun i => canonical_successor (branch_value (canonical_stage c k) i))
  end.

Lemma canonical_stage_normalized c : c.2 \is den1lf ->
    forall k i, (branch_value (canonical_stage c k) i).2 \is den1lf.
Proof.
move=>Hc; elim=>[|k IH].
- by move=>i.
- move=>[i j] /=; exact: canonical_successor_normalized (IH i) j.
Qed.

Lemma canonical_stage_probability c : c.2 \is den1lf ->
    forall k, probability_family (canonical_stage c k).
Proof.
move=>Hc; elim=>[|k IH]; first exact: certain_probability.
apply: bind_family_probability IH _=>i Hi.
apply: canonical_successor_probability.
exact: (@canonical_stage_normalized c Hc k i).
Qed.

Definition canonical_computation c (Hc : c.2 \is den1lf) : computation p c.
Proof.
apply: (@Computation n p c (canonical_stage c)).
- by move=>x.
- exact: canonical_stage_probability Hc.
- by move=>k i _; exact: canonical_stage_normalized Hc k i.
- move=>k; split.
  + have [Hs [Hp _]] := canonical_stage_probability Hc k.+1.
    by split.
  + exists (fun i => canonical_successor (branch_value (canonical_stage c k) i)); split.
    * by move=>i _; apply: canonical_successor_step.
    * by move=>x.
Defined.

Theorem computation_exists c : c.2 \is den1lf -> exists pi : computation p c, True.
Proof. by move=>Hc; exists (canonical_computation Hc). Qed.

End CanonicalComputation.
End DistributedDistribution.


Module DistributedScheduler.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma matches_channel a b effect : matches a b effect -> channel a = channel b.
Proof. by case. Qed.

Lemma process_channel p j : channel (process_io p j) \in process_channels p.
Proof. apply/imfsetP; by exists j. Qed.

Definition rendezvous n (p : 'I_n -> process) (m : cmem) (i k : 'I_n) :=
  i != k /\ exists j l effect,
    eval (process_guard (p i) j) m /\
    eval (process_guard (p k) l) m /\
    matches (process_io (p i) j) (process_io (p k) l) effect.

Lemma rendezvous_symmetric n (p : 'I_n -> process) m i k :
  rendezvous p m i k -> rendezvous p m k i.
Proof.
move=>[ne [j [l [effect [Hi [Hk Hmatch]]]]]].
split; first by rewrite eq_sym.
exists l, j, effect; split=>//; split=>//; exact: matches_symmetric.
Qed.

(* A process with one enabled guarded branch cannot rendezvous with two
   different peers: that would place its enabled channel in three processes. *)
Lemma rendezvous_partner_unique (P : program) m i j k :
  rendezvous (processes P) m i j ->
  rendezvous (processes P) m i k -> j = k.
Proof.
move=>[Hij [a [b [effect [Ha [Hb Hab]]]]]]
       [Hik [a' [c [effect' [Ha' [Hc Hac]]]]]].
have Eaa : a = a' := (proj1 (proj2 (@processes_wf P i))) m a a' Ha Ha'.
subst a'.
case Ejk : (j == k); first by apply/eqP.
exfalso; have Hjk : j != k by rewrite Ejk.
have D := @processes_point_to_point P i j k Hij Hik Hjk.
have Ci := @process_channel (processes P i) a.
have Cj : channel (process_io (processes P i) a) \in process_channels (processes P j).
  by rewrite (matches_channel Hab); exact: process_channel.
have Ck : channel (process_io (processes P i) a) \in process_channels (processes P k).
  by rewrite (matches_channel Hac); exact: process_channel.
move/fdisjointP: D=>/(_ _ Ci); by rewrite in_fsetI Cj Ck.
Qed.

Local Close Scope fset_scope.

Definition local_enabled n (p : 'I_n -> process) pc m rho i :=
  (exists s mu, pc i = Executing s /\
     local_step (local_config s (Some m) rho) mu) \/
  (pc i = Waiting /\ [forall j, ~~ eval (process_guard (p i) j) m]).
Definition pair_enabled n (p : 'I_n -> process) pc m i k :=
  pc i = Waiting /\ pc k = Waiting /\ rendezvous p m i k.

Lemma local_pair_exclusive n (p : 'I_n -> process) pc m rho i k :
  local_enabled p pc m rho i -> ~ pair_enabled p pc m i k.
Proof.
move=>[[s [mu [Hpc Hstep]]]|[Hpc /forallP Hnone]] [Hi [Hk [ne [j [l [e [Hj [Hl Hmatch]]]]]]]].
- by rewrite Hpc in Hi.
- by move: (Hnone j); rewrite Hj.
Qed.

Inductive enabled_label n (p : 'I_n -> process) pc m rho : {set 'I_n} -> Prop :=
| EnabledLocal i : local_enabled p pc m rho i -> enabled_label p pc m rho [set i]
| EnabledPair i k : pair_enabled p pc m i k -> enabled_label p pc m rho [set i; k].


Lemma global_step_has_label n (p : 'I_n -> process) c mu : global_step p c mu ->
  exists pc m rho A, c = global_config pc (Some m) rho /\ enabled_label p pc m rho A.
Proof.
move=>d; case: d=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch].
- exists pc, m, rho, [set i]; split=>//; apply: EnabledLocal.
  left; by exists s, nu.
- exists pc, m, rho, [set i]; split=>//; apply: EnabledLocal.
  by right.
- exists pc, m, rho, [set i; k]; split=>//; apply: EnabledPair.
  split=>//; split=>//; split.
    by apply/negP=>/eqP E; move: Hik; rewrite E ltnn.
  by exists j, l, (AAssign x e); repeat split.
Qed.

Lemma enabled_labels_disjoint_or_equal (P : program) pc m rho A B :
  enabled_label (processes P) pc m rho A ->
  enabled_label (processes P) pc m rho B ->
  A = B \/ [disjoint A & B]%SET.
Proof.
move=>HA HB; inversion HA; subst A; inversion HB; subst B.
- case E : (i == i0).
  + by left; move/eqP: E=>->.
  + right; apply/disjointP=>z; rewrite !inE=>/eqP->.
    by rewrite E.
- right; apply/disjointP=>z; rewrite !inE=>/eqP->.
  apply/negP=>/orP[/eqP E|/eqP E]; subst i.
  + exact: (local_pair_exclusive H H0).
  + move: H0=>[Hi [Hk HR]].
    have HP : pair_enabled (processes P) pc m k i0.
      split; first exact Hk; split; first exact Hi.
      exact: rendezvous_symmetric HR.
    exact: (local_pair_exclusive H HP).
- right; rewrite disjoint_sym; apply/disjointP=>z; rewrite !inE=>/eqP->.
  apply/negP=>/orP[/eqP E|/eqP E]; subst i0.
  + exact: (local_pair_exclusive H0 H).
  + move: H=>[Hi [Hk HR]].
    have HP : pair_enabled (processes P) pc m k i.
      split; first exact Hk; split; first exact Hi.
      exact: rendezvous_symmetric HR.
    exact: (local_pair_exclusive H0 HP).
- move: H H0=>[Hi [Hk HR]] [Hi0 [Hk0 HR0]].
  case Eii : (i == i0).
    move/eqP: Eii=>Ei; subst i0.
    have Ek := rendezvous_partner_unique HR HR0; subst k0; by left.
  case Eik : (i == k0).
    move/eqP: Eik=>Ei; subst k0.
    have Ek := rendezvous_partner_unique HR (rendezvous_symmetric HR0).
    subst i0; left; apply/setP=>z; by rewrite !inE orbC.
  case Eki : (k == i0).
    move/eqP: Eki=>Ek; subst i0.
    have Ei := rendezvous_partner_unique (rendezvous_symmetric HR) HR0.
    subst k0; left; apply/setP=>z; by rewrite !inE orbC.
  case Ekk : (k == k0).
    move/eqP: Ekk=>Ek; subst k0.
    have Ei := rendezvous_partner_unique (rendezvous_symmetric HR)
      (rendezvous_symmetric HR0).
    subst i0; by left.
  right; apply/disjointP=>z; rewrite !inE=>/orP[/eqP->|/eqP->].
  + by rewrite Eii Eik.
  + by rewrite Eki Ekk.
Qed.

Lemma replace_same n (pc : 'I_n -> control) i c : replace pc i c i = c.
Proof. by rewrite /replace eqxx. Qed.

Lemma replace_other n (pc : 'I_n -> control) i j c :
  j != i -> replace pc i c j = pc j.
Proof. by move=>/negbTE H; rewrite /replace H. Qed.

Lemma replace_commute n (pc : 'I_n -> control) i j ci cj : i != j ->
  replace (replace pc i ci) j cj = replace (replace pc j cj) i ci.
Proof.
move=>Hij; apply/funext=>k; rewrite /replace.
case Eki: (k == i); case Ekj: (k == j)=>//.
move/eqP: Eki=>Eki; subst k.
by move: Hij; rewrite Ekj.
Qed.


Definition residual_wf s := s = Finished \/ statement_wf s.

Lemma append_wf s t : residual_wf s -> statement_wf t -> statement_wf (append s t).
Proof. by case: s=>//=; rewrite /residual_wf /=; intuition discriminate. Qed.

Lemma local_step_wf c mu : local_step c mu -> statement_wf c.1.1 ->
  forall i, residual_wf (branch_value mu i).1.1.
Proof.
move=>H; induction H; cbn [local_config certain branch_value fmap];
  move=>Hwf outcome; try by left.
- right; apply: append_wf; last exact: (proj2 Hwf).
  exact: (IHlocal_step (proj1 Hwf) outcome).
- right; exact: (proj2 Hwf).
- right; split=>//; exact: (proj2 Hwf).
Qed.

Local Open Scope fset_scope.

Lemma branch_changes_subset n (b : 'I_n -> statement) i :
  statement_changes (b i) `<=` \big[fsetU/fset0]_j statement_changes (b j).
Proof. by rewrite (bigD1 i) //=; exact: fsubsetUl. Qed.

Lemma append_changes s t : statement_changes (append s t) `<=`
  statement_changes s `|` statement_changes t.
Proof. by case: s=>//=; rewrite fset0U. Qed.

Lemma local_step_changes c mu : local_step c mu -> forall i,
  statement_changes (branch_value mu i).1.1 `<=` statement_changes c.1.1.
Proof.
move=>H; induction H; cbn [local_config certain branch_value fmap];
  move=>outcome; try exact: fsub0set.
- apply: fsubset_trans (append_changes _ _ ) _.
  by rewrite fsubUset (fsubset_trans (IHlocal_step outcome) (fsubsetUl _ _))
    (fsubsetUr _ _).
- exact: branch_changes_subset.
- by rewrite /= fsubUset branch_changes_subset fsubset_refl.
Qed.


Local Close Scope fset_scope.

Definition normalized_output (E : 'SO(Hq)) rho :=
  if 0 < \Tr (E rho) then (\Tr (E rho))^-1 *: E rho else rho.

Lemma normalized_output_den1 (E : 'CP(Hq)) rho : rho \is den1lf ->
  normalized_output E rho \is den1lf.
Proof.
move=>Hr; rewrite /normalized_output; case: ifP=>Htr; last exact: Hr.
apply/den1lfP; split.
  apply: psdlfZ; first by rewrite invr_ge0; exact: ltW Htr.
  apply: cp_psdP; exact: den1lf_psd Hr.
by rewrite linearZ /= mulVf ?gt_eqF.
Qed.

Lemma weighted_normalized_output (E : 'CP(Hq)) rho : rho \is den1lf ->
  \Tr (E rho) *: normalized_output E rho = E rho.
Proof.
move=>Hr; rewrite /normalized_output; case: ifP=>Htr.
  by rewrite scalerA mulfV ?gt_eqF // scale1r.
have Hp : E rho \is psdlf by apply: cp_psdP; exact: den1lf_psd Hr.
have Hzero : \Tr (E rho) = 0.
  by move: (psdlf_trlf Hp); rewrite le_eqVlt Htr orbF eq_sym=>/eqP.
have Ez : E rho == 0 := introT (@trlf0_eq0 Hq (E rho)) (conj (psdlf_ge0 Hp) Hzero).
by rewrite Hzero scale0r (eqP Ez).
Qed.

Lemma weighted_two_normalized_outputs (E F : 'CP(Hq)) rho : rho \is den1lf ->
  (\Tr (E rho) * \Tr (F (normalized_output E rho))) *:
    normalized_output F (normalized_output E rho) = F (E rho).
Proof.
move=>Hr; rewrite -scalerA (weighted_normalized_output F (normalized_output_den1 E Hr)).
by rewrite -linearZ /= (weighted_normalized_output E Hr).
Qed.

Lemma commuting_normalized_outputs (E F : 'CP(Hq)) rho :
  rho \is den1lf -> E :o F = F :o E ->
  (\Tr (E rho) * \Tr (F (normalized_output E rho))) *:
    normalized_output F (normalized_output E rho) =
  (\Tr (F rho) * \Tr (E (normalized_output F rho))) *:
    normalized_output E (normalized_output F rho).
Proof.
by move=>Hr Hcomm; rewrite !weighted_two_normalized_outputs //;
  exact: commuting_joint_state.
Qed.
End DistributedScheduler.


Module DistributedObservables.
(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Notation C := hermitian.C.

Lemma observe_summable X (mu : family X) (f : X -> C) M :
  probability_family mu -> 0 <= M -> (forall x, `|f x| <= M) ->
  summable (fun i => branch_weight mu i * f (branch_value mu i)).
Proof.
move=>Hm HM Hf; exists M; near=>A.
apply: (le_trans (y := psum (branch_weight mu) A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  rewrite /normf normrM ger0_norm ?(proj1 (proj2 Hm)) //.
  by apply: ler_wpM2l=>//; exact: (proj1 (proj2 Hm)).
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (psum_le1_mu (probability_distribution Hm)).
Unshelve. end_near.
Qed.

Lemma observe_constant X (mu : family X) c : probability_family mu ->
  family_observe mu (fun _ => c) = c.
Proof.
move=>Hm; rewrite /family_observe (eq_sum (g := fun i => c * branch_weight mu i));
  first by move=>i; rewrite mulrC.
change (sum (c *: Summable.build (proj1 Hm)) = c).
rewrite summable_sumZ.
change (c * family_mass mu = c).
by rewrite (proj2 (proj2 Hm)) mulr1.
Qed.

Lemma observe_certain X (x : X) f : family_observe (certain x) f = f x.
Proof.
rewrite /family_observe /certain /= fin_dom_sum (bigD1 tt) //= mul1r.
by rewrite big1 ?addr0 // => [[]].
Qed.

Lemma constant_family X Y (mu : family X) (y : Y) : probability_family mu ->
  same_distribution (fmap (fun _ => y) mu) (certain y).
Proof.
move=>Hm f Hf; rewrite observe_certain.
change (family_observe mu (fun _ => f y) = f y).
exact: (@observe_constant X mu (f y) Hm).
Qed.

Section BindObserve.
Context {X Y : Type} (mu : family X) (nu : branch_index mu -> family Y)
  (f : Y -> C) (M : C).
Hypothesis Hmu : probability_family mu.
Hypothesis Hnu : forall i, 0 < branch_weight mu i -> probability_family (nu i).
Hypothesis HM : 0 <= M.
Hypothesis Hf : forall y, `|f y| <= M.

Let row i ij := @bind_row X Y mu nu i ij * f (branch_value (bind_family mu nu) ij).

Lemma observe_bind_rectangle A B :
  psum (fun i => psum (fun ij => `|row i ij|) B) A <= M.
Proof.
apply: (le_trans (y := psum (fun i =>
  psum (fun ij => `|@bind_row X Y mu nu i ij|) B) A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  rewrite mulr_suml; apply: ler_sum=>ij _.
  rewrite /row normrM; by apply: ler_wpM2l=>//; exact: Hf.
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (@bind_rectangle_bound X Y mu nu Hmu Hnu A B).
Qed.

Lemma observe_bind_column ij : sum (fun i => row i ij) =
    branch_weight (bind_family mu nu) ij * f (branch_value (bind_family mu nu) ij).
Proof.
rewrite (fin_supp_sum (S := [fset projT1 ij])) ?psum1 /row ?bind_rowE ?eqxx //.
by move=>i; rewrite inE=>/negPf Hi; rewrite bind_rowE Hi mul0r.
Qed.

Lemma observe_bind_row i : sum (row i) = branch_weight mu i * family_observe (nu i) f.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have Er : (row i \o @bind_encode X Y mu nu i)%FUN =
      (fun j => branch_weight mu i * (branch_weight (nu i) j * f (branch_value (nu i) j))).
    by apply/funext=>j; rewrite /= /row /bind_row bind_encodeK /= mulrA.
  rewrite (sum_reindex (@bind_encodeK X Y mu nu i) (@bind_decodeK X Y mu nu i)).
    by move=>ij E; rewrite /row /bind_row E /= mul0r.
    rewrite Er; exact: summable_funZ (observe_summable Hi HM Hf).
  rewrite Er.
  change (sum (branch_weight mu i *: Summable.build (observe_summable Hi HM Hf)) =
    branch_weight mu i * family_observe (nu i) f).
  by rewrite summable_sumZ.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  rewrite (eq_sum (g := fun _ => 0)).
    by move=>ij; rewrite /row (bind_row_zero Z) mul0r.
  by rewrite summable_sum_cst0 Z mul0r.
Qed.

Lemma observe_bind : family_observe (bind_family mu nu) f =
    sum (fun i => branch_weight mu i * family_observe (nu i) f).
Proof.
have rect : exists M', forall A B,
    psum (fun i => psum (fun ij => `|row i ij|) B) A <= M'.
  by exists M=>A B; apply: observe_bind_rectangle.
transitivity (sum (fun i => sum (row i))).
- rewrite (pseries2_exchange_lim rect); apply: eq_sum=>ij.
  by rewrite observe_bind_column.
- by apply: eq_sum=>i; rewrite observe_bind_row.
Qed.

End BindObserve.

Lemma observe_partial_bound X (mu : family X) (f : X -> C) M A :
  probability_family mu -> 0 <= M -> (forall x, `|f x| <= M) ->
  psum (fun i => `|branch_weight mu i * f (branch_value mu i)|) A <= M.
Proof.
move=>Hm HM Hf; apply: (le_trans (y := psum (branch_weight mu) A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  rewrite normrM ger0_norm ?(proj1 (proj2 Hm)) //.
  by apply: ler_wpM2l=>//; exact: (proj1 (proj2 Hm)).
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (psum_le1_mu (probability_distribution Hm)).
Qed.

Lemma probability_rectangle (I J : choiceType) (w : I -> C) (v : I -> J -> C)
    (f : I -> J -> C) M :
  probability_family (@Family I I w id) ->
  (forall i, probability_family (@Family J J (v i) id)) ->
  0 <= M -> (forall i j, `|f i j| <= M) ->
  forall A B, psum (fun i => psum (fun j => `|w i * (v i j * f i j)|) B) A <= M.
Proof.
move=>Hw Hv HM Hf A B.
apply: (le_trans (y := psum w A * M)).
- rewrite /psum mulr_suml; apply: ler_sum=>i _.
  under eq_bigr do rewrite normrM ger0_norm ?(proj1 (proj2 Hw)) //.
  rewrite -mulr_sumr; apply: ler_wpM2l; first exact: (proj1 (proj2 Hw)).
  have Hp := @observe_partial_bound J (@Family J J (v (val i)) id) (f (val i)) M B
    (Hv (val i)) HM (Hf (val i)).
  exact Hp.
- rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r=>//.
  exact: (psum_le1_mu (probability_distribution Hw)).
Qed.

Lemma probability_exchange (I J : choiceType) (w : I -> C) (v : I -> J -> C)
    (f : I -> J -> C) M :
  probability_family (@Family I I w id) ->
  (forall i, probability_family (@Family J J (v i) id)) ->
  0 <= M -> (forall i j, `|f i j| <= M) ->
  sum (fun i => sum (fun j => w i * (v i j * f i j))) =
  sum (fun j => sum (fun i => w i * (v i j * f i j))).
Proof.
move=>Hw Hv HM Hf; apply: pseries2_exchange_lim.
by exists M=>A B; exact: (@probability_rectangle I J w v f M Hw Hv HM Hf A B).
Qed.


Lemma observe_bind_nested X Y (mu : family X) (nu : branch_index mu -> family Y)
    (f : Y -> C) M :
  probability_family mu -> (forall i, probability_family (nu i)) ->
  0 <= M -> (forall y, `|f y| <= M) ->
  family_observe (bind_family mu nu) f =
    sum (fun i => sum (fun j => branch_weight mu i *
      (branch_weight (nu i) j * f (branch_value (nu i) j)))).
Proof.
move=>Hmu Hnu HM Hf.
rewrite (@observe_bind X Y mu nu f M Hmu (fun i _ => Hnu i) HM Hf).
apply: eq_sum=>i; symmetry.
change (sum (branch_weight mu i *: Summable.build (observe_summable (Hnu i) HM Hf)) =
  branch_weight mu i * family_observe (nu i) f).
by rewrite summable_sumZ.
Qed.
End DistributedObservables.


Module DistributedWeighted.
(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Import Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Local Notation C := hermitian.C.

Definition weighted_sum {X : Type} {H : chsType} (mu : family X)
    (f : X -> 'End(H)) :=
  sum (fun i => branch_weight mu i *: f (branch_value mu i)).

Lemma weighted_summable X (H : chsType) (mu : family X) (f : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  summable (fun i => branch_weight mu i *: f (branch_value mu i)).
Proof.
move=>Hm Hf; exists 1; near=>A.
apply: (le_trans (y := psum (branch_weight mu) A)).
- apply: ler_sum=>i _; rewrite /normf normrZ ger0_norm ?(proj1 (proj2 Hm)) //.
  rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l=>//.
  exact: (proj1 (proj2 Hm)).
- exact: (psum_le1_mu (probability_distribution Hm)).
Unshelve. end_near.
Qed.

Lemma weighted_partial_bound X (H : chsType) (mu : family X) (f : X -> 'End(H)) A :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  psum (fun i => `|branch_weight mu i *: f (branch_value mu i)|) A <= 1.
Proof.
move=>Hm Hf; apply: (le_trans (y := psum (branch_weight mu) A)).
- apply: ler_sum=>i _; rewrite normrZ ger0_norm ?(proj1 (proj2 Hm)) //.
  rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l=>//.
  exact: (proj1 (proj2 Hm)).
- exact: (psum_le1_mu (probability_distribution Hm)).
Qed.

Lemma weighted_norm X (H : chsType) (mu : family X) (f : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) -> `|weighted_sum mu f| <= 1.
Proof.
move=>Hm Hf; have Hs := weighted_summable Hm Hf.
change (`|sum (Summable.build Hs)| <= 1).
apply: (le_trans (summable_sum_ler_norm _)).
apply: etlim_le; first exact: summable_norm_is_cvg.
move=>A; exact: weighted_partial_bound Hm Hf.
Qed.

Lemma weighted_certain X (H : chsType) x (f : X -> 'End(H)) :
  weighted_sum (certain x) f = f x.
Proof.
rewrite /weighted_sum /certain /= fin_dom_sum (bigD1 tt) //= scale1r.
by rewrite big1 ?addr0 // => [[]].
Qed.

Lemma weighted_positive X (H : chsType) (mu : family X) (f : X -> 'End(H)) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  (forall x, 0%:VF ⊑ f x) -> 0%:VF ⊑ weighted_sum mu f.
Proof.
move=>Hm Hf Hp; apply: lim_gev_near.
- by apply: norm_bounded_cvg; apply: weighted_summable.
- near=>A; apply: sumv_ge0=>i _.
  by rewrite scalev_ge0 ?(proj1 (proj2 Hm)) ?Hp.
Unshelve. end_near.
Qed.

Lemma weighted_linear X (H : chsType) (mu : family X) (f : X -> 'End(H))
    (L : {linear 'End(H) -> C}) :
  probability_family mu -> (forall x, `|f x| <= 1) ->
  L (weighted_sum mu f) = family_observe mu (fun x => L (f x)).
Proof.
move=>Hm Hf; rewrite /weighted_sum cvg_linear_sum.
- by apply: norm_bounded_cvg; apply: weighted_summable.
- by apply: eq_sum=>i; rewrite /= linearZ.
Qed.

Definition matrix_observer (H : chsType) (u v : H) (A : 'End(H)) : C :=
  [< u; A v >].
Lemma matrix_observer_linear (H : chsType) (u v : H) : linear (matrix_observer u v).
Proof. by move=>a A B; rewrite /matrix_observer add_lfunE scale_lfunE dotpPr. Qed.
HB.instance Definition _ (H : chsType) (u v : H) :=
  GRing.isLinear.Build C 'End(H) C *:%R (matrix_observer u v) (matrix_observer_linear u v).

Lemma weighted_same X (H : chsType) (mu nu : family X) (f : X -> 'End(H)) :
  probability_family mu -> probability_family nu ->
  same_distribution mu nu -> (forall x, `|f x| <= 1) ->
  weighted_sum mu f = weighted_sum nu f.
Proof.
move=>Hm Hn E Hf; apply/lfunP=>v; apply/intro_dotl=>u.
change (matrix_observer u v (weighted_sum mu f) = matrix_observer u v (weighted_sum nu f)).
rewrite !weighted_linear //; apply: E.
have [M [HM Hbound]] := (linear_bounded (matrix_observer u v : {linear 'End(H) -> C})).
exists M=>x; apply: (le_trans (Hbound (f x))).
rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l=>//; exact: ltW HM.
Qed.

Section BindWeighted.
Context {X Y : Type} {H : chsType} (mu : family X)
  (nu : branch_index mu -> family Y) (f : Y -> 'End(H)).
Hypothesis Hmu : probability_family mu.
Hypothesis Hnu : forall i, 0 < branch_weight mu i -> probability_family (nu i).
Hypothesis Hf : forall y, `|f y| <= 1.

Let row i ij := @bind_row X Y mu nu i ij *:
  f (branch_value (bind_family mu nu) ij).

Lemma weighted_bind_rectangle A B :
  psum (fun i => psum (fun ij => `|row i ij|) B) A <= 1.
Proof.
apply: (le_trans (y := psum (fun i =>
  psum (fun ij => `|@bind_row X Y mu nu i ij|) B) A)).
- apply: ler_sum=>i _; apply: ler_sum=>ij _.
  rewrite /row normrZ -[X in _ <= X]mulr1.
  by apply: ler_wpM2l=>//; apply: Hf.
- exact: (@bind_rectangle_bound X Y mu nu Hmu Hnu A B).
Qed.

Lemma weighted_bind_column ij : sum (fun i => row i ij) =
    branch_weight (bind_family mu nu) ij *: f (branch_value (bind_family mu nu) ij).
Proof.
rewrite (fin_supp_sum (S := [fset projT1 ij])) ?psum1 /row ?bind_rowE ?eqxx //.
by move=>i; rewrite inE=>/negPf Hi; rewrite bind_rowE Hi scale0r.
Qed.

Lemma weighted_bind_row i : sum (row i) = branch_weight mu i *: weighted_sum (nu i) f.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have Er : (row i \o @bind_encode X Y mu nu i)%FUN =
      (fun j => branch_weight mu i *: (branch_weight (nu i) j *: f (branch_value (nu i) j))).
    by apply/funext=>j; rewrite /= /row /bind_row bind_encodeK /= scalerA.
  rewrite (sum_reindex (@bind_encodeK X Y mu nu i) (@bind_decodeK X Y mu nu i)).
    by move=>ij E; rewrite /row /bind_row E /= scale0r.
    rewrite Er; exact: summable_funZ (weighted_summable Hi Hf).
  rewrite Er.
  change (sum (branch_weight mu i *: Summable.build (weighted_summable Hi Hf)) =
    branch_weight mu i *: weighted_sum (nu i) f).
  by rewrite summable_sumZ.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  rewrite (eq_sum (g := fun _ => 0)).
    by move=>ij; rewrite /row (bind_row_zero Z) scale0r.
  by rewrite summable_sum_cst0 Z scale0r.
Qed.

Lemma weighted_bind_summable :
  summable (fun i => branch_weight mu i *: weighted_sum (nu i) f).
Proof.
have rect : exists M, forall A B,
    psum (fun i => psum (fun ij => `|row i ij|) B) A <= M.
  by exists 1=>A B; apply: weighted_bind_rectangle.
have [_ [_ [Hs _]]] := pseries_ubounded_cvg rect.
have E : (fun i => sum (row i)) = (fun i => branch_weight mu i *: weighted_sum (nu i) f).
  by apply/funext=>i; rewrite weighted_bind_row.
by rewrite -E.
Qed.

Theorem weighted_bind : weighted_sum (bind_family mu nu) f =
    sum (fun i => branch_weight mu i *: weighted_sum (nu i) f).
Proof.
have rect : exists M, forall A B,
    psum (fun i => psum (fun ij => `|row i ij|) B) A <= M.
  by exists 1=>A B; apply: weighted_bind_rectangle.
transitivity (sum (fun i => sum (row i))).
- rewrite (pseries2_exchange_lim rect); apply: eq_sum=>ij.
  by rewrite weighted_bind_column.
- by apply: eq_sum=>i; rewrite weighted_bind_row.
Qed.

End BindWeighted.
End DistributedWeighted.


Module DistributedLocalActions.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma pick_guard_unique n (g : 'I_n -> expression bool) m i :
  exclusive g -> eval (g i) m -> [pick j | eval (g j) m] = Some i.
Proof.
move=>Hex Hi; case: pickP=>[j Hj|Hnone].
  by rewrite (Hex m j i Hj Hi).
by move: (Hnone i); rewrite Hi.
Qed.

Lemma pick_guard_none n (g : 'I_n -> expression bool) m :
  [forall i, ~~ eval (g i) m] -> [pick j | eval (g j) m] = None.
Proof.
move=>/forallP Hnone; case: pickP=>// j Hj.
by move: (Hnone j); rewrite Hj.
Qed.

Definition atom_successor (a : atom) m rho : family local_configuration :=
  match a with
  | ASkip => certain (local_config Finished (Some m) rho)
  | AAbort => certain (local_config Finished None rho)
  | AAssign _ x e => certain (local_config Finished (Some (m.[x <- eval e m])%M) rho)
  | ARandom t x mu => @Family _ (CL.value t) (fun v => CL.probability_mass mu m v)
      (fun v => local_config Finished (Some (m.[x <- v])%M) rho)
  | AInitial _ q phi => certain (local_config Finished (Some m)
      (liftfso (initialso (tv2v q (eval phi m))) rho))
  | AUnitary _ q U => certain (local_config Finished (Some m)
      (liftfso (formso (tf2f q q (eval U m))) rho))
  | AMeasure _ _ x q M => measurement_branch x q M m rho
  end.

Fixpoint local_successor (s : statement) m rho : family local_configuration :=
  match s with
  | Finished => certain (local_config Finished (Some m) rho)
  | Atomic a => atom_successor a m rho
  | Sequence s t => fmap (append_configuration t) (local_successor s m rho)
  | Alternative n g b =>
      if [pick j | eval (g j) m] is Some j
      then certain (local_config (b j) (Some m) rho)
      else certain (local_config Finished None rho)
  | Repetition n g b =>
      if [pick j | eval (g j) m] is Some j
      then certain (local_config (Sequence (b j) (Repetition g b)) (Some m) rho)
      else certain (local_config Finished (Some m) rho)
  end.

Lemma local_step_canonical c mu : local_step c mu -> statement_wf c.1.1 ->
  forall m, c.1.2 = Some m -> mu = local_successor c.1.1 m c.2.
Proof.
move=>d; induction d; move=>Hwf m0 [= <-] //=.
- by rewrite (IHd (proj1 Hwf) m erefl).
- by rewrite (pick_guard_unique (proj1 Hwf) H).
- by rewrite (pick_guard_none H).
- by rewrite (pick_guard_unique (proj1 Hwf) H).
- by rewrite (pick_guard_none H).
Qed.

Lemma local_step_deterministic s m rho mu nu : statement_wf s ->
  local_step (local_config s (Some m) rho) mu ->
  local_step (local_config s (Some m) rho) nu -> mu = nu.
Proof.
move=>Hwf Hmu Hnu.
by rewrite (local_step_canonical Hmu Hwf erefl) (local_step_canonical Hnu Hwf erefl).
Qed.


Lemma append_reads s t :
  (statement_reads (append s t) `<=` (statement_reads s `|` statement_reads t))%classic.
Proof.
case: s=>[|a|s1 s2|n g b|n g b] /= x Hx.
- by right.
- exact Hx.
- exact Hx.
- exact Hx.
- exact Hx.
Qed.

Lemma local_step_reads c mu : local_step c mu -> forall i,
  (statement_reads (branch_value mu i).1.1 `<=` statement_reads c.1.1)%classic.
Proof.
move=>d; induction d; cbn [local_config certain branch_value fmap];
  move=>outcome z; try by [].
- move=>/append_reads [Hx|Hx].
  + left; exact: (IHd outcome z Hx).
  + by right.
- move=>Hx; exists i=>//; by right.
- move=>[Hx|Hx]; last exact Hx.
  exists i=>//; by right.
Qed.

Lemma append_quantum s t :
  (statement_quantum (append s t) :<=: statement_quantum s :|: statement_quantum t)%SET.
Proof. by case: s=>//=; rewrite finset.set0U. Qed.

Lemma branch_quantum_subset n (b : 'I_n -> statement) i :
  (statement_quantum (b i) :<=: \bigcup_j statement_quantum (b j))%SET.
Proof. apply/fintype.subsetP=>x Hx; apply/finset.bigcupP; by exists i. Qed.

Lemma local_step_quantum c mu : local_step c mu -> forall i,
  (statement_quantum (branch_value mu i).1.1 :<=: statement_quantum c.1.1)%SET.
Proof.
move=>d; induction d; cbn [local_config certain branch_value fmap];
  move=>outcome; try exact: finset.sub0set.
- apply: fintype.subset_trans (append_quantum _ _) _.
  by rewrite finset.subUset (fintype.subset_trans (IHd outcome) (finset.subsetUl _ _)) (finset.subsetUr _ _).
- exact: branch_quantum_subset.
- by rewrite /= finset.subUset branch_quantum_subset subxx.
Qed.


Local Open Scope fset_scope.
Definition unchanged (xs : {fset classical_name}) (s t : cmem) :=
  forall u (x : CL.variable u), name_of x \notin xs -> (s.[x] = t.[x])%M.

Lemma unchanged_refl xs s : unchanged xs s s.
Proof. by move=>u x _. Qed.

Lemma update_unchanged u (x : CL.variable u) v s :
  unchanged [fset name_of x] s (s.[x <- v])%M.
Proof.
move=>t y; rewrite inE /name_of /CL.key xpair_eqE negb_and=>/orP[ne|ne]; symmetry.
- apply: get_set_ne; left; move=>E; move: ne.
  by rewrite /cvtype in E; rewrite E eqxx.
- apply: get_set_ne; right; by rewrite eq_sym.
Qed.

Lemma local_step_unchanged c mu : local_step c mu -> forall outcome s t,
  c.1.2 = Some s -> (branch_value mu outcome).1.2 = Some t ->
  unchanged (statement_changes c.1.1) s t.
Proof.
move=>d; induction d; move=>outcome s0 t0 [= <-];
  cbn [local_config certain branch_value fmap measurement_branch append_configuration];
  try by move=>[= <-]; apply: unchanged_refl.
- by [].
- move=>[= <-]; exact: update_unchanged.
- move=>[= <-]; exact: update_unchanged.
- move=>[= <-]; exact: update_unchanged.
- move=>Ht u x; rewrite /= in_fsetU negb_or=>/andP[Hx _].
  exact: (IHd outcome m t0 erefl Ht u x Hx).
- by [].
Qed.

Lemma local_step_preserves_expression A (e : expression A) s m rho mu outcome t :
  (forall k, expression_reads e k -> k \notin statement_changes s) ->
  local_step (local_config s (Some m) rho) mu ->
  (branch_value mu outcome).1.2 = Some t -> eval e m = eval e t.
Proof.
move=>Hfresh Hstep Hout; apply: ClassicalFootprint.eval_local=>u x Hx.
apply: (local_step_unchanged Hstep erefl Hout).
exact: Hfresh.
Qed.
End DistributedLocalActions.


Module DistributedResults.
(* Well-formed cq-states of successful finite-stage outcomes, Section 3.2. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedWeighted.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Definition successful_component n (c : global_configuration n) : state :=
  match c.1.2 with
  | None => CQState.bottom
  | Some s =>
      if [forall i, asbool (c.1.1 i = Stopped)] then
        match asboolP (c.2 \is denlf) with
        | ReflectT H => CQState.point s (DenLf_Build H)
        | ReflectF _ => CQState.bottom
        end
      else CQState.bottom
  end.

Lemma successful_componentE n (c : global_configuration n) m :
  c.2 \is denlf -> successful_component c m =
  if successful_at c m then c.2 else 0.
Proof.
case: c=>[[pc [s|]] rho] Pr; rewrite /successful_component /successful_at /=;
  last by [].
case E: [forall i, asbool (pc i = Stopped)].
- case: asboolP=>[H|H]; last by exfalso; apply: H.
  by rewrite CQState.pointE /= andbT eq_sym.
- by rewrite andbF CQState.bottomE.
Qed.

Definition successful_state n (mu : family (global_configuration n))
    (H : probability_family mu) : state :=
  CQStateMixture.mix (probability_distribution H)
    (fun i => successful_component (branch_value mu i)).

Lemma successful_stateE n (mu : family (global_configuration n))
    (H : probability_family mu) :
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  forall m, successful_state H m = successful_result mu m.
Proof.
move=>Hr m; rewrite /successful_state CQStateMixture.mixE /successful_result.
apply: eq_sum=>i; rewrite probability_distributionE.
case P: (0 < branch_weight mu i).
- rewrite successful_componentE; first by apply: den1lf_den; apply: Hr.
  by case: successful_at; rewrite ?scaler0.
- have w0 : branch_weight mu i = 0.
    by move: (proj1 (proj2 H) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by rewrite w0 scale0r; case: successful_at; rewrite ?scale0r.
Qed.

Definition stage_state n (p : 'I_n -> process) c (pi : computation p c) k : state :=
  successful_state (computation_probability pi k).

Lemma stage_stateE n (p : 'I_n -> process) c (pi : computation p c) k m :
  stage_state pi k m = successful_result (computation_stage pi k) m.
Proof. apply: successful_stateE; exact: computation_normalized. Qed.

Lemma stage_mass_bound n (p : 'I_n -> process) c (pi : computation p c) k :
  CQState.mass (stage_state pi k) <= 1.
Proof. exact: CQState.mass_le1. Qed.

Lemma successful_component_bound n (c : global_configuration n) m :
  `|successful_component c m| <= 1.
Proof.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
apply: denlf_trlf; exact: CQState.component_density.
Qed.

Lemma successful_component_terminal_or_zero n (p : 'I_n -> process) c :
  terminal p c \/ successful_component c = CQState.bottom.
Proof.
case: c=>[[pc [s|]] rho]; last by right.
case E: [forall i, asbool (pc i = Stopped)].
- left; have Epc : pc = (fun _ => Stopped).
    by apply/funext=>i; move/forallP: E=>/(_ i)/asboolP.
  rewrite Epc; exact: stopped_terminal.
- by right; rewrite /successful_component E.
Qed.

Lemma successful_state_weighted n (mu : family (global_configuration n))
    (H : probability_family mu) m :
  successful_state H m = weighted_sum mu (fun c => successful_component c m).
Proof.
rewrite /successful_state CQStateMixture.mixE /weighted_sum.
by apply: eq_sum=>i; rewrite probability_distributionE.
Qed.

Lemma successful_component_step n (p : 'I_n -> process) c nu m :
  ((terminal p c /\ nu = certain c) \/ global_step p c nu) ->
  probability_family nu ->
  successful_component c m ⊑ weighted_sum nu (fun d => successful_component d m).
Proof.
move=>Hs Hn; case: (successful_component_terminal_or_zero p c)=>[Ht|Hz].
- case: Hs=>[[Htc ->]|Hs]; last by exfalso; exact: Ht _ Hs.
  by rewrite weighted_certain.
- rewrite Hz CQState.bottomE -successful_state_weighted.
  exact: vdistr_ge0.
Qed.

Lemma successful_state_step n (p : 'I_n -> process)
    (mu nu : family (global_configuration n))
    (Hm : probability_family mu) (Hn : probability_family nu) :
  distribution_step p mu nu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  successful_state Hm ⊑ successful_state Hn.
Proof.
move=>[Ha [next [Hnext E]]] Hr.
have Hnextprob : forall i, 0 < branch_weight mu i -> probability_family (next i).
  move=>i Hi; case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: global_step_probability Hs (Hr i Hi).
have Hb := bind_family_probability Hm Hnextprob.
apply/levdP=>m; rewrite !successful_state_weighted.
rewrite (weighted_same Hn Hb E (fun c => successful_component_bound c m)).
rewrite (weighted_bind Hm Hnextprob (fun c => successful_component_bound c m)).
apply: lev_lim.
- apply: norm_bounded_cvg.
  exact: weighted_summable Hm (fun c => successful_component_bound c m).
- apply: norm_bounded_cvg; exact: weighted_bind_summable Hm Hnextprob (fun c => successful_component_bound c m).
- move=>A; apply: lev_sum=>i _.
  case P: (0 < branch_weight mu (val i)).
  + apply: lev_pscale2lP; first exact: P.
    exact: successful_component_step (Hnext (val i) P) (Hnextprob (val i) P).
  + have Z : branch_weight mu (val i) = 0.
      by move: (proj1 (proj2 Hm) (val i)); rewrite le_eqVlt P orbF eq_sym=>/eqP.
    by rewrite Z !scale0r.
Qed.

Lemma stage_state_step n (p : 'I_n -> process) c (pi : computation p c) k :
  stage_state pi k ⊑ stage_state pi k.+1.
Proof.
apply: successful_state_step; first exact: computation_advances.
exact: computation_normalized.
Qed.

Lemma stage_state_chain n (p : 'I_n -> process) c (pi : computation p c) :
  nondecreasing_seq (stage_state pi).
Proof. apply/nondecreasing_seqP=>k; exact: stage_state_step. Qed.

Definition result_state n (p : 'I_n -> process) c (pi : computation p c) : state :=
  CQState.chain_sup (stage_state pi).

Theorem computation_converges n (p : 'I_n -> process) c (pi : computation p c) :
  computes pi (fun m => result_state pi m).
Proof.
move=>m; rewrite /result_state
  (@CQState.chain_sup_pointwise cmem Hq (stage_state pi) (stage_state_chain pi) m).
have Eseq : (fun k => successful_result (computation_stage pi k) m) =
    (fun k => stage_state pi k m).
  by apply/funext=>k; rewrite stage_stateE.
rewrite Eseq.
apply: cvgP.
have C := @CQState.chain_converges cmem Hq (stage_state pi) (stage_state_chain pi).
exact: (@summableE_is_cvg _ _ _ _ _ _ _ _ C m).
Qed.

Lemma result_stateE n (p : 'I_n -> process) c (pi : computation p c) m :
  computed_result pi m = result_state pi m.
Proof. by rewrite (computes_result (computation_converges (pi := pi))). Qed.

Lemma result_state_upper n (p : 'I_n -> process) c (pi : computation p c) k :
  stage_state pi k ⊑ result_state pi.
Proof. exact: (@CQState.chain_sup_upper cmem Hq (stage_state pi) (stage_state_chain pi) k). Qed.

Lemma result_state_least n (p : 'I_n -> process) c (pi : computation p c) (d : state) :
  (forall k, stage_state pi k ⊑ d) -> result_state pi ⊑ d.
Proof. exact: (@CQState.chain_sup_least cmem Hq (stage_state pi) d (stage_state_chain pi)). Qed.

Theorem denotational_results_nonempty n (p : 'I_n -> process) c :
  c.2 \is den1lf -> exists d, denotational_results p c d.
Proof.
move=>Hc; pose pi := canonical_computation p Hc.
exists (fun m => result_state pi m); exists pi; exact: computation_converges.
Qed.
End DistributedResults.


Module DistributedInstruments.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition atom_index (a : atom) : choiceType :=
  match a with
  | ARandom t _ _ => CL.value t
  | AMeasure t _ _ _ _ => eval_qtype t
  | _ => Choice.clone unit _
  end.

Fixpoint local_index s : choiceType :=
  match s with
  | Atomic a => atom_index a
  | Sequence s _ => local_index s
  | _ => Choice.clone unit _
  end.

Definition atom_control (a : atom) m : atom_index a -> (statement * option cmem) :=
  match a as a' return atom_index a' -> (statement * option cmem) with
  | AAbort => fun _ => (Finished,None)
  | AAssign _ x e => fun _ => (Finished,Some (m.[x <- eval e m])%M)
  | ARandom _ x _ => fun i => (Finished,Some (m.[x <- i])%M)
  | AMeasure _ _ x _ _ => fun i => (Finished,Some (m.[x <- i])%M)
  | _ => fun _ => (Finished,Some m)
  end.

Fixpoint local_control s m : local_index s -> (statement * option cmem) :=
  match s as s' return local_index s' -> (statement * option cmem) with
  | Finished => fun _ => (Finished,Some m)
  | Atomic a => @atom_control a m
  | Sequence s t => fun i => (append (@local_control s m i).1 t, (@local_control s m i).2)
  | Alternative n g b => fun _ =>
      if [pick j | eval (g j) m] is Some j then (b j,Some m) else (Finished,None)
  | Repetition n g b => fun _ =>
      if [pick j | eval (g j) m] is Some j
      then (Sequence (b j) (Repetition g b),Some m) else (Finished,Some m)
  end.

Definition atom_map (a : atom) m : atom_index a -> 'SO(Hq) :=
  match a as a' return atom_index a' -> 'SO(Hq) with
  | ARandom _ _ p => fun i => CL.probability_mass p m i *: \:1
  | AInitial _ q phi => fun _ => liftfso (initialso (tv2v q (eval phi m)))
  | AUnitary _ q U => fun _ => liftfso (formso (tf2f q q (eval U m)))
  | AMeasure _ _ _ q M => fun i => ClassicalSemantics.measurement_branches q M m i
  | _ => fun _ => \:1
  end.

Fixpoint local_map s m : local_index s -> 'SO(Hq) :=
  match s as s' return local_index s' -> 'SO(Hq) with
  | Atomic a => @atom_map a m
  | Sequence s _ => @local_map s m
  | _ => fun _ => \:1
  end.

Lemma atom_map_cp a m i : @atom_map a m i \is cpmap.
Proof.
case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i /=.
- exact: is_cpmap.
- exact: is_cpmap.
- exact: is_cpmap.
- rewrite -geso0_cpE; apply: scalev_ge0.
  + exact: ge0_mu.
  + exact: cp_geso0.
- exact: is_cpmap.
- exact: is_cpmap.
- exact: is_cpmap.
Qed.

Lemma local_map_cp s m i : @local_map s m i \is cpmap.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /=.
- exact: is_cpmap.
- exact: atom_map_cp.
- exact: IH.
- exact: is_cpmap.
- exact: is_cpmap.
Qed.

Definition local_cp s m i := CPMap_Build (@local_map_cp s m i).

Lemma atom_map_external a m i S (F : 'SO_S) :
  [disjoint atom_quantum a & S] ->
  @atom_map a m i :o liftfso F = liftfso F :o @atom_map a m i.
Proof.
case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- by rewrite comp_soZl comp_soZr comp_so1l comp_so1r.
- exact: liftfso_compC.
- exact: liftfso_compC.
- rewrite ClassicalSemantics.measurement_branchE; exact: liftfso_compC.
Qed.

Lemma local_map_external s m i S (F : 'SO_S) :
  [disjoint statement_quantum s & S] ->
  @local_map s m i :o liftfso F = liftfso F :o @local_map s m i.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- exact: atom_map_external.
- apply: IH; exact: fintype.disjointWl (finset.subsetUl _ _) Hdis.
Qed.


Lemma normalized_channel (E : 'QC(Hq)) rho : rho \is den1lf ->
  normalized_output E rho = E rho.
Proof.
move=>Hr; rewrite /normalized_output qc_trlfE (den1lf_trlf Hr) ltr01 invr1 scale1r.
by [].
Qed.

Lemma normalized_scalar p rho : rho \is den1lf ->
  normalized_output (p *: (\:1 : 'SO(Hq))) rho = rho.
Proof.
move=>Hr; rewrite /normalized_output !soE linearZ /= (den1lf_trlf Hr) mulr1.
case: ifP=>Hp; last by [].
by rewrite scalerA mulVf ?gt_eqF // scale1r.
Qed.

Definition local_family s m rho : family local_configuration :=
  @Family _ (local_index s) (fun i => \Tr (@local_map s m i rho))
    (fun i => local_config (@local_control s m i).1 (@local_control s m i).2
      (normalized_output (@local_map s m i) rho)).

Lemma atom_realization a m rho : rho \is den1lf ->
  atom_successor a m rho = local_family (Atomic a) m rho.
Proof.
move=>Hr; case: a=>[| |t x e|t x p|t q phi|t q U|t u x q M];
  rewrite /atom_successor /local_family /=.
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- congr (@Family _ _ _ _); apply/funext=>i.
  + by rewrite !soE linearZ /= (den1lf_trlf Hr) mulr1.
  + by rewrite normalized_scalar.
- by rewrite normalized_channel // qc_trlfE (den1lf_trlf Hr).
- by rewrite normalized_channel // qc_trlfE (den1lf_trlf Hr).
- by rewrite /measurement_branch /normalized_output.
Qed.

Lemma local_realization s m rho : rho \is den1lf ->
  local_successor s m rho = local_family s m rho.
Proof.
move=>Hr; elim: s=>[|a|s IH t IHt|n g b IH|n g b IH] /=.
- by rewrite /local_family /= normalized_channel // !soE (den1lf_trlf Hr).
- exact: atom_realization.
- by rewrite IH /local_family /fmap /append_configuration /local_config.
- rewrite /local_family /=; case: pickP=>[i Hi|Hnone];
    by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- rewrite /local_family /=; case: pickP=>[i Hi|Hnone];
    by rewrite normalized_channel // !soE (den1lf_trlf Hr).
Qed.
End DistributedInstruments.


Module DistributedProgress.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
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


Module DistributedResidual.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedScheduler DistributedLocalActions DistributedResults.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Definition statement_owned (p : process) (s : statement) :=
  statement_wf s /\
  statement_changes s `<=` process_changes p /\
  (statement_reads s `<=` process_reads p)%classic /\
  (statement_quantum s :<=: process_quantum p)%SET.

Definition control_owned (p : process) (pc : control) :=
  match pc with Executing s => statement_owned p s | _ => True end.
Definition configuration_owned n (p : 'I_n -> process) (c : global_configuration n) :=
  forall i, control_owned (p i) (c.1.1 i).

Lemma initialization_owned p : process_wf p -> statement_owned p (initialization p).
Proof.
move=>[Hinit Hbody]; split=>//; split.
- exact: fsubsetUl.
split.
- by move=>x Hx; left.
- exact: finset.subsetUl.
Qed.

Lemma body_owned p j : process_wf p -> statement_owned p (process_body p j).
Proof.
move=>[Hinit [Hex Hbody]]; split; first exact: Hbody.
split.
- apply: fsubset_trans (fsubsetUr _ _) _.
  rewrite /process_changes (bigD1 j) //=.
  apply: fsubset_trans (fsubsetUl _ _) _; exact: fsubsetUr.
split.
- move=>x Hx; right; exists j=>//; by right.
- rewrite /process_quantum; apply: fintype.subset_trans _ (finset.subsetUr _ _).
  exact: branch_quantum_subset.
Qed.

Lemma initial_configuration_owned n (p : 'I_n -> process) m rho :
  (forall i, process_wf (p i)) -> configuration_owned p (initial_configuration p m rho).
Proof. by move=>H i; apply: initialization_owned. Qed.

Lemma after_local_owned p s t :
  statement_owned p s -> residual_wf t ->
  statement_changes t `<=` statement_changes s ->
  (statement_reads t `<=` statement_reads s)%classic ->
  (statement_quantum t :<=: statement_quantum s)%SET ->
  control_owned p (after_local p t).
Proof.
move=>[Hs [Hc [Hr Hq]]] Ht Htc Htr Htq.
case: t Ht Htc Htr Htq=>[|a|a b|n g b|n g b] /= Ht Htc Htr Htq.
- by case: branch_count.
all: split; first by case: Ht=>[//|].
all: split; first exact: fsubset_trans Htc Hc.
all: split; first by move=>x Hx; apply: Hr; apply: Htr.
all: exact: fintype.subset_trans Htq Hq.
Qed.

Lemma local_successor_owned p s m rho mu :
  statement_owned p s -> local_step (local_config s (Some m) rho) mu ->
  forall outcome, control_owned p (after_local p (branch_value mu outcome).1.1).
Proof.
move=>Hs Hstep outcome; apply: (after_local_owned Hs).
- exact: (@local_step_wf _ _ Hstep (proj1 Hs) outcome).
- exact: (@local_step_changes _ _ Hstep outcome).
- exact: (@local_step_reads _ _ Hstep outcome).
- exact: (@local_step_quantum _ _ Hstep outcome).
Qed.

Lemma global_step_owned n (p : 'I_n -> process) c mu :
  (forall i, process_wf (p i)) -> configuration_owned p c ->
  global_step p c mu -> forall outcome, configuration_owned p (branch_value mu outcome).
Proof.
move=>Hwf Hown Hstep; case: Hstep Hown=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hown outcome z /=.
- rewrite /replace; case E: (z == i).
  + move/eqP: E=>->; apply: (@local_successor_owned (p i) s m rho nu _ Hloc outcome).
    by move: (Hown i); rewrite /= Hpc.
  + exact: Hown.
- rewrite /replace; case E: (z == i)=>//; exact: Hown.
- rewrite /replace; case Ezk: (z == k).
  + move/eqP: Ezk=>->; exact: (@body_owned (p k) l (Hwf k)).
  + case Ezi: (z == i); last exact: Hown.
    move/eqP: Ezi=>->; exact: (@body_owned (p i) j (Hwf i)).
Qed.

Lemma distribution_step_owned n (p : 'I_n -> process) mu nu :
  (forall i, process_wf (p i)) -> distribution_step p mu nu ->
  probability_family mu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  (forall i, 0 < branch_weight mu i -> configuration_owned p (branch_value mu i)) ->
  forall j, 0 < branch_weight nu j -> configuration_owned p (branch_value nu j).
Proof.
move=>Hwf Hstep Hm Hr Hown.
have Hn := distribution_step_probability Hstep Hm Hr.
case: Hstep=>Ha [next [Hnext E]].
have Hbind : probability_family (bind_family mu next).
  apply: bind_family_probability Hm _=>i Hi.
  case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: (global_step_probability Hs (Hr i Hi)).
apply: (same_distribution_support (P := configuration_owned p) Hbind Hn E).
move=>[i j] /= Hij.
case P: (0 < branch_weight mu i).
- have Hchild : forall k, configuration_owned p (branch_value (next i) k).
    case: (Hnext i P)=>[[Ht ->]|Hs].
    + by move=>k; exact: Hown.
    + exact: (@global_step_owned _ p _ _ Hwf (Hown i P) Hs).
  exact: Hchild.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hm) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by move: Hij; rewrite Z mul0r ltxx.
Qed.

Lemma computation_owned n (p : 'I_n -> process) c (pi : computation p c) :
  (forall i, process_wf (p i)) -> configuration_owned p c ->
  forall k i, 0 < branch_weight (computation_stage pi k) i ->
    configuration_owned p (branch_value (computation_stage pi k) i).
Proof.
move=>Hwf Hc; elim=>[|k IH].
- apply: (same_distribution_support (P := configuration_owned p)
    (certain_probability c) (computation_probability pi 0%N) (computation_initial pi)).
  by move=>i Hi.
- exact (@distribution_step_owned n p (computation_stage pi k) (computation_stage pi k.+1)
    Hwf (@computation_advances n p c pi k) (@computation_probability n p c pi k)
    (@computation_normalized n p c pi k) IH).
Qed.

Lemma program_computation_owned (P : program) m rho
    (pi : computation (processes P) (initial_configuration (processes P) m rho)) :
  forall k i, 0 < branch_weight (computation_stage pi k) i ->
    configuration_owned (processes P) (branch_value (computation_stage pi k) i).
Proof.
apply: computation_owned; first exact: processes_wf.
apply: initial_configuration_owned; exact: processes_wf.
Qed.

Local Close Scope fset_scope.

Definition controls_outside n (A : {set 'I_n}) (pc pc' : 'I_n -> control) :=
  forall i, i \notin A -> pc' i = pc i.

Lemma global_step_label_control n (p : 'I_n -> process) c mu : global_step p c mu ->
  exists m A, c.1.2 = Some m /\ enabled_label p c.1.1 m c.2 A /\
    forall outcome, controls_outside A c.1.1 (branch_value mu outcome).1.1.
Proof.
move=>d; case: d=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch].
- exists m, [set i]; split=>//; split.
  + apply: EnabledLocal; left; by exists s, nu.
  + move=>outcome z; rewrite inE=>Hz; exact: replace_other Hz.
- exists m, [set i]; split=>//; split.
  + apply: EnabledLocal; by right.
  + move=>outcome z; rewrite inE=>Hz; exact: replace_other Hz.
- exists m, [set i; k]; split=>//; split.
  + apply: EnabledPair; split=>//; split=>//; split.
      by apply/negP=>/eqP E; move: Hik; rewrite E ltnn.
    by exists j, l, (AAssign x e); repeat split.
  + move=>outcome z; rewrite !inE negb_or=>/andP[Hzi Hzk].
    by rewrite /= !replace_other.
Qed.

Lemma enabled_label_active n (p : 'I_n -> process) pc m rho A :
  enabled_label p pc m rho A -> forall i, i \in A -> pc i <> Stopped.
Proof.
case=>[j Hlocal|j k Hpair] i.
- rewrite inE=>/eqP->.
  case: Hlocal=>[[s [mu [E Hstep]]]|[E Hnone]]; by rewrite E.
- rewrite !inE=>/orP[/eqP->|/eqP->];
    move: Hpair=>[Ej [Ek Hpair]]; by rewrite ?Ej ?Ek.
Qed.

Lemma enabled_label_nonempty n (p : 'I_n -> process) pc m rho A :
  enabled_label p pc m rho A -> exists i, i \in A.
Proof. case=>[i Hi|i k Hik]; exists i; by rewrite !inE eqxx. Qed.

Lemma disjoint_enabled_not_stopped n (p : 'I_n -> process) pc m rho
    (A B : {set 'I_n}) (pc' : 'I_n -> control) :
  enabled_label p pc m rho B -> [disjoint A & B]%SET ->
  controls_outside A pc pc' -> exists i, pc' i <> Stopped.
Proof.
move=>HB HAB Hctrl; have [i Hi] := enabled_label_nonempty HB.
have Hnot : i \notin A.
  by move: HAB; rewrite disjoint_sym=>/disjointP/(_ i Hi).
exists i; rewrite (Hctrl i Hnot); exact: (@enabled_label_active n p pc m rho B HB i Hi).
Qed.

Lemma successful_at_not_stopped n (c : global_configuration n) i m :
  c.1.1 i <> Stopped -> successful_at c m = false.
Proof.
move=>H; rewrite /successful_at; case: c.1.2=>// s.
suff -> : [forall j, asbool (c.1.1 j = Stopped)] = false by rewrite andbF.
apply/negP=>/forallP/(_ i)/asboolP; exact: H.
Qed.

Lemma successful_component_not_stopped n (c : global_configuration n) i :
  c.1.1 i <> Stopped -> successful_component c = CQState.bottom.
Proof.
case: c=>[[pc [m|]] rho] H //=; rewrite /successful_component /=.
suff -> : [forall j, asbool (pc j = Stopped)] = false by [].
apply/negP=>/forallP/(_ i)/asboolP; exact: H.
Qed.

Lemma disjoint_enabled_successful_component n (p : 'I_n -> process)
    (c : global_configuration n) m (A B : {set 'I_n}) (d : global_configuration n) :
  enabled_label p c.1.1 m c.2 B -> [disjoint A & B]%SET ->
  controls_outside A c.1.1 d.1.1 -> successful_component d = CQState.bottom.
Proof.
move=>HB HAB Hctrl; have [i Hi] := disjoint_enabled_not_stopped HB HAB Hctrl.
exact: successful_component_not_stopped Hi.
Qed.
End DistributedResidual.


Module DistributedInterchange.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma local_map_atom s m i a t j :
  [disjoint statement_quantum s & atom_quantum a] ->
  @local_map s m i :o @atom_map a t j = @atom_map a t j :o @local_map s m i.
Proof.
case: a j=>[| |u x e|u x p|u q phi|u q U|u v x q M] j /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- by rewrite comp_soZl comp_soZr comp_so1l comp_so1r.
- exact: local_map_external.
- exact: local_map_external.
- rewrite ClassicalSemantics.measurement_branchE; exact: local_map_external.
Qed.

Lemma local_map_commute s t m1 m2 i j :
  [disjoint statement_quantum s & statement_quantum t] ->
  @local_map s m1 i :o @local_map t m2 j = @local_map t m2 j :o @local_map s m1 i.
Proof.
elim: t j=>[|a|t IH u IHu|n g b IH|n g b IH] j /= Hdis;
  try by rewrite comp_so1l comp_so1r.
- exact: local_map_atom.
- apply: IH; exact: fintype.disjointWr (finset.subsetUl _ _) Hdis.
Qed.

Lemma eval_reads A (e : expression A) R m t :
  (expression_reads e `<=` R)%classic ->
  ClassicalFootprint.agree_on R m t -> eval e m = eval e t.
Proof.
move=>HR Hmt; apply: ClassicalFootprint.eval_local=>u x Hx.
apply: Hmt; exact: HR.
Qed.

Lemma atom_map_agree a m t i : ClassicalFootprint.agree_on (atom_reads a) m t ->
  @atom_map a m i = @atom_map a t i.
Proof.
case: a i=>[| |u x e|u x p|u q phi|u q U|u v x q M] i /= Hmt=>//.
- have Ep : eval (CL.probability_expression p) m = eval (CL.probability_expression p) t.
    apply: eval_reads Hmt; by move=>k Hk; right.
  change (eval (CL.probability_expression p) m i *: (\:1 : 'SO(Hq)) =
    eval (CL.probability_expression p) t i *: (\:1 : 'SO(Hq))).
  by rewrite Ep.
- by rewrite (eval_reads (fun k Hk => Hk) Hmt).
- by rewrite (eval_reads (fun k Hk => Hk) Hmt).
- have EM : eval M m = eval M t.
    apply: eval_reads Hmt; by move=>k Hk; right.
  rewrite !ClassicalSemantics.measurement_branchE.
  change (liftfso (formso (tf2f q q (eval M m i))) =
    liftfso (formso (tf2f q q (eval M t i)))).
  by rewrite EM.
Qed.

Lemma local_map_agree s m t i : ClassicalFootprint.agree_on (statement_reads s) m t ->
  @local_map s m i = @local_map s t i.
Proof.
elim: s i=>[|a|s IH u IHu|n g b IH|n g b IH] i /= Hmt=>//.
- exact: atom_map_agree.
- apply: IH=>v x Hx; apply: Hmt; by left.
Qed.

Lemma memory_ext m t :
  (forall u (x : CL.variable u), (m.[x] = t.[x])%M) -> m = t.
Proof.
case: m=>m; case: t=>t; move=>H; congr CMem.
apply: functional_extensionality_dep=>u; apply/funext=>[[a b]].
exact: (H u (@CVar u a b)).
Qed.

Lemma updates_commute u v (x : CL.variable u) (y : CL.variable v) a b m :
  name_of x != name_of y ->
  ((m.[x <- a]).[y <- b] = (m.[y <- b]).[x <- a])%M.
Proof.
move=>Hxy; apply: memory_ext=>w z.
rewrite /cmset /cmget /cvtype /= /orapp.
case: eqP=>Euw; case: eqP=>Evw; rewrite ?eqxx //=.
case Exz: (cvname x == cvname z); case Eyz: (cvname y == cvname z)=>//.
exfalso; move/eqP: Hxy; apply.
apply/eqP; rewrite /name_of /CL.key xpair_eqE; apply/andP; split; apply/eqP.
- exact: (eq_trans Evw (esym Euw)).
- exact: (eq_trans (eqP Exz) (esym (eqP Eyz))).
Qed.


Lemma update_agree R u (x : CL.variable u) v m :
  ~ R (name_of x) -> ClassicalFootprint.agree_on R m (m.[x <- v])%M.
Proof.
move=>Hfresh t y Hy; apply: update_unchanged.
rewrite inE; apply/negP=>/eqP E; apply: Hfresh; by rewrite -E.
Qed.

Lemma eval_external A (e : expression A) R u (x : CL.variable u) v m :
  (expression_reads e `<=` R)%classic -> ~ R (name_of x) ->
  eval e (m.[x <- v])%M = eval e m.
Proof.
move=>Hsub Hfresh; symmetry; exact: eval_reads Hsub (update_agree v m Hfresh).
Qed.

Lemma atom_control_external a m u (x : CL.variable u) v i :
  ~ atom_reads a (name_of x) ->
  @atom_control a (m.[x <- v])%M i =
    ((@atom_control a m i).1, omap (fun t => (t.[x <- v])%M) (@atom_control a m i).2).
Proof.
case: a i=>[| |t y e|t y p|t q phi|t q U|t w y q M] i /= Hfresh=>//.
- have He : eval e (m.[x <- v])%M = eval e m.
    apply: (@eval_external _ e (atom_reads (AAssign y e)) u x v m); last exact Hfresh.
    by move=>k Hk; right.
  rewrite He; congr (Finished, Some _); apply: updates_commute.
  apply/negP=>/eqP E; apply: Hfresh; left; exact E.
- congr (Finished, Some _); apply: updates_commute.
  apply/negP=>/eqP E; apply: Hfresh; left; exact E.
- congr (Finished, Some _); apply: updates_commute.
  apply/negP=>/eqP E; apply: Hfresh; left; exact E.
Qed.

Lemma local_control_external s m u (x : CL.variable u) v i :
  ~ statement_reads s (name_of x) ->
  @local_control s (m.[x <- v])%M i =
    ((@local_control s m i).1, omap (fun t => (t.[x <- v])%M) (@local_control s m i).2).
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /= Hfresh=>//.
- exact: atom_control_external.
- have Hs : ~ statement_reads s (name_of x) by move=>Hs; apply: Hfresh; left.
  by rewrite (IH i Hs).
- have Eg : (fun j => eval (g j) (m.[x <- v])%M) = (fun j => eval (g j) m).
    apply/funext=>j; apply: (@eval_external _ (g j) _ u x v m _ Hfresh).
    move=>k Hk; exists j=>//; by left.
  rewrite Eg; by case: pickP.
- have Eg : (fun j => eval (g j) (m.[x <- v])%M) = (fun j => eval (g j) m).
    apply/funext=>j; apply: (@eval_external _ (g j) _ u x v m _ Hfresh).
    move=>k Hk; exists j=>//; by left.
  rewrite Eg; by case: pickP.
Qed.

Lemma local_map_external_update s m u (x : CL.variable u) v i :
  ~ statement_reads s (name_of x) ->
  @local_map s (m.[x <- v])%M i = @local_map s m i.
Proof.
move=>Hfresh; symmetry; apply: local_map_agree.
exact: update_agree.
Qed.


Local Open Scope fset_scope.
Definition store_outcome (xs : {fset classical_name}) m out :=
  out = None \/ out = Some m \/
  exists u (x : CL.variable u) v, name_of x \in xs /\ out = Some (m.[x <- v])%M.

Lemma store_outcome_weaken xs ys m out : xs `<=` ys ->
  store_outcome xs m out -> store_outcome ys m out.
Proof.
move=>/fsubsetP Hxy [H|[H|[u [x [v [Hx Hout]]]]]]; [by left|by right; left|].
right; right; exists u, x, v; split=>//; exact: Hxy.
Qed.

Lemma atom_store_outcome a m i :
  store_outcome (atom_changes a) m (@atom_control a m i).2.
Proof.
case: a i=>[| |u x e|u x p|u q phi|u q U|u v x q M] i /=;
  rewrite /store_outcome; try by right; left.
- by left.
- right; right; exists u, x, (eval e m); by rewrite inE.
- right; right; exists u, x, i; by rewrite inE.
- right; right; exists (QType u), x, i; by rewrite inE.
Qed.

Lemma local_store_outcome s m i :
  store_outcome (statement_changes s) m (@local_control s m i).2.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /=.
- by right; left.
- exact: atom_store_outcome.
- apply: store_outcome_weaken (IH i); exact: fsubsetUl.
- case: pickP=>[j Hj|Hnone]; [by right; left|by left].
- case: pickP=>[j Hj|Hnone]; by right; left.
Qed.

Definition local_store s i m := (@local_control s m i).2.

Lemma local_store_external s (i : local_index s) m u (x : CL.variable u) v :
  ~ statement_reads s (name_of x) ->
  @local_store s i (m.[x <- v])%M = omap (fun t => (t.[x <- v])%M) (@local_store s i m).
Proof. by move=>Hfresh; rewrite /local_store (@local_control_external s m u x v i Hfresh). Qed.

Definition store_compose (F G : cmem -> option cmem) m :=
  if F m is Some t then G t else None.

Lemma local_stores_commute s t (i : local_index s) (j : local_index t) m :
  (forall x, x \in statement_changes s -> ~ statement_reads t x) ->
  (forall x, x \in statement_changes t -> ~ statement_reads s x) ->
  [disjoint statement_changes s & statement_changes t] ->
  store_compose (@local_store s i) (@local_store t j) m =
  store_compose (@local_store t j) (@local_store s i) m.
Proof.
move=>Hst Hts Hdis.
have A := @local_store_outcome s m i.
have B := @local_store_outcome t m j.
change (store_outcome (statement_changes s) m (@local_store s i m)) in A.
change (store_outcome (statement_changes t) m (@local_store t j m)) in B.
rewrite /store_compose.
case: A=>[A|[A|[u [x [v [Hx A]]]]]];
case: B=>[B|[B|[w [y [z [Hy B]]]]]]; rewrite A B /=; try by rewrite ?A ?B.
- by rewrite (@local_store_external s i m w y z (Hts _ Hy)) A.
- by rewrite (@local_store_external s i m w y z (Hts _ Hy)) A.
- by rewrite (@local_store_external t j m u x v (Hst _ Hx)) B.
- by rewrite (@local_store_external t j m u x v (Hst _ Hx)) B.
- rewrite (@local_store_external t j m u x v (Hst _ Hx)) B
    (@local_store_external s i m w y z (Hts _ Hy)) A /=.
  congr (Some _); apply: updates_commute.
  apply/negP=>/eqP E; move/fdisjointP: Hdis=>/(_ _ Hx).
  by rewrite -E Hy.
Qed.
End DistributedInterchange.


Module DistributedLocalMaps.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedLocalActions DistributedInstruments.
Local Notation Hq := 'H[msys]_finset.setT.
Definition atom_maps (a : atom) m : {vdistr atom_index a -> 'SO(Hq)} :=
  match a as a' return {vdistr atom_index a' -> 'SO(Hq)} with
  | ARandom _ _ p => sdistr Hq (esem (CL.probability_expression p) m)
  | AInitial _ q phi => sunit_vdistr tt (liftfso (initialso (tv2v q (eval phi m))))
  | AUnitary _ q U => sunit_vdistr tt (liftfso (formso (tf2f q q (eval U m))))
  | AMeasure _ _ _ q M => ClassicalSemantics.measurement_branches q M m
  | _ => sunit_vdistr tt (\:1 : 'QO(Hq))
  end.

Fixpoint local_maps s m : {vdistr local_index s -> 'SO(Hq)} :=
  match s as s' return {vdistr local_index s' -> 'SO(Hq)} with
  | Atomic a => atom_maps a m
  | Sequence s _ => local_maps s m
  | _ => sunit_vdistr tt (\:1 : 'QO(Hq))
  end.

Lemma atom_mapsE a m i : @atom_maps a m i = @atom_map a m i.
Proof.
case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i //=;
  by case: i; rewrite /sunit_def /=.
Qed.

Lemma local_mapsE s m i : @local_maps s m i = @local_map s m i.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i //=; try exact: atom_mapsE;
  by case: i; rewrite /sunit_def /=.
Qed.


End DistributedLocalMaps.


Module DistributedGlobalActions.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedResults DistributedResidual DistributedCommunication DistributedWeighted.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Inductive action (n : nat) := Local of 'I_n | Rendezvous of 'I_n & 'I_n.
Arguments Local {n} i.
Arguments Rendezvous {n} i k.

Definition participants n (a : action n) : {set 'I_n} :=
  match a with Local i => [set i] | Rendezvous i k => [set i; k] end.
Definition ordered n (a : action n) :=
  match a with Local _ => True | Rendezvous i k => (i < k)%N end.

Inductive labeled_step n (p : 'I_n -> process) :
    action n -> global_configuration n -> family (global_configuration n) -> Prop :=
| LParallel pc m rho i s mu :
    pc i = Executing s ->
    local_step (local_config s (Some m) rho) mu ->
    labeled_step p (Local i) (global_config pc (Some m) rho) (fmap (lift_local p pc i) mu)
| LProcessDone pc m rho i :
    pc i = Waiting ->
    [forall j, ~~ eval (process_guard (p i) j) m] ->
    labeled_step p (Local i) (global_config pc (Some m) rho)
      (certain (global_config (replace pc i Stopped) (Some m) rho))
| LCommunication pc m rho (i k : 'I_n) j l t (x : CL.variable t) e :
    (i < k)%N -> pc i = Waiting -> pc k = Waiting ->
    eval (process_guard (p i) j) m -> eval (process_guard (p k) l) m ->
    matches (process_io (p i) j) (process_io (p k) l) (AAssign x e) ->
    labeled_step p (Rendezvous i k) (global_config pc (Some m) rho)
      (certain (global_config
        (replace (replace pc i (Executing (process_body (p i) j)))
          k (Executing (process_body (p k) l)))
        (Some (m.[x <- eval e m])%M) rho)).

Lemma labeled_step_erasure n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> global_step p c mu.
Proof. by case; [apply: StepParallel | apply: StepProcessDone | apply: StepCommunication]. Qed.

Lemma labeled_step_complete n (p : 'I_n -> process) c mu :
  global_step p c mu -> exists a, labeled_step p a c mu.
Proof.
case=>[pc m rho i s nu Hi Hloc|pc m rho i Hi Hnone|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch].
- exists (Local i); exact: LParallel Hi Hloc.
- exists (Local i); exact: LProcessDone Hi Hnone.
- exists (Rendezvous i k); exact: LCommunication Hik Hi Hk Hj Hl Hmatch.
Qed.

Lemma labeled_step_ordered n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> ordered a.
Proof. by case. Qed.

Lemma labeled_step_enabled n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> exists m, c.1.2 = Some m /\
    enabled_label p c.1.1 m c.2 (participants a).
Proof.
case=>[pc m rho i s nu Hi Hloc|pc m rho i Hi Hnone|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch]; exists m; split=>//.
- apply: EnabledLocal; left; by exists s, nu.
- apply: EnabledLocal; by right.
- apply: EnabledPair; split=>//; split=>//; split.
    by apply/negP=>/eqP E; move: Hik; rewrite E ltnn.
  by exists j, l, (AAssign x e); repeat split.
Qed.

Lemma labeled_step_controls n (p : 'I_n -> process) a c mu :
  labeled_step p a c mu -> forall outcome,
    controls_outside (participants a) c.1.1 (branch_value mu outcome).1.1.
Proof.
case=>[pc m rho i s nu Hi Hloc|pc m rho i Hi Hnone|
  pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] outcome z.
- rewrite inE=>Hz; exact: replace_other Hz.
- rewrite inE=>Hz; exact: replace_other Hz.
- rewrite !inE negb_or=>/andP[Hzi Hzk].
  by rewrite /= !replace_other.
Qed.

Definition assignment_store (a : atom) m :=
  match a with AAssign _ x e => (m.[x <- eval e m])%M | _ => m end.

Lemma matches_store_unique a b e f m : matches a b e -> matches a b f ->
  assignment_store e m = assignment_store f m.
Proof.
move=>He Hf; have E : e = f.
  by move: (matching_effect He); rewrite (matching_effect Hf)=>[=].
by rewrite E.
Qed.

Lemma labeled_step_deterministic n (p : 'I_n -> process) a c mu nu :
  (forall i, process_wf (p i)) -> configuration_owned p c ->
  labeled_step p a c mu -> labeled_step p a c nu -> mu = nu.
Proof.
move=>Hwf Hown d1 d2; inversion d1; subst; inversion d2; subst.
all: try congruence.
- have Es : s0 = s by congruence.
  subst s0; have Hs : statement_wf s.
    have Ho := Hown i; rewrite /= H in Ho; exact: (proj1 Ho).
  by rewrite (local_step_deterministic Hs H0 H7).
- have Ej : j0 = j := (proj1 (proj2 (Hwf i))) m j0 j H14 H2.
  have El : l0 = l := (proj1 (proj2 (Hwf k))) m l0 l H15 H3.
  subst j0; subst l0.
  have Em := @matches_store_unique _ _ _ _ m H4 H16.
  change ((m.[x <- eval e m])%M = (m.[x0 <- eval e0 m])%M) in Em.
  by rewrite Em.
Qed.


Lemma ordered_participants_injective n (a b : action n) :
  ordered a -> ordered b -> participants a = participants b -> a = b.
Proof.
case: a=>[i|i k]; case: b=>[j|j l] /= Ha Hb E.
- have Hi : i \in [set j] by rewrite -E inE eqxx.
  by move: Hi; rewrite inE=>/eqP->.
- have Hj : j \in [set i] by rewrite E !inE eqxx.
  have Hl : l \in [set i] by rewrite E !inE eqxx orbT.
  move: Hj Hl; rewrite !inE=>/eqP Hj /eqP Hl.
  by move: Hb; rewrite Hj Hl ltnn.
- have Hi : i \in [set j] by rewrite -E !inE eqxx.
  have Hk : k \in [set j] by rewrite -E !inE eqxx orbT.
  move: Hi Hk; rewrite !inE=>/eqP Hi /eqP Hk.
  by move: Ha; rewrite Hi Hk ltnn.
- have Hi : i \in [set j; l] by rewrite -E !inE eqxx.
  have Hk : k \in [set j; l] by rewrite -E !inE eqxx orbT.
  move: Hi Hk; rewrite !inE=>/orP[/eqP Eij|/eqP Eil] /orP[/eqP Ekj|/eqP Ekl].
  + by move: Ha; rewrite Eij Ekj ltnn.
  + by rewrite Eij Ekl.
  + move: Ha; rewrite Eil Ekj=>Ha'.
    by move: (ltn_trans Hb Ha'); rewrite ltnn.
  + by move: Ha; rewrite Eil Ekl ltnn.
Qed.

Lemma labeled_steps_disjoint_or_equal (P : program) a b c mu nu :
  labeled_step (processes P) a c mu -> labeled_step (processes P) b c nu ->
  a = b \/ [disjoint participants a & participants b]%SET.
Proof.
move=>Ha Hb; have [m [Hm HEa]] := labeled_step_enabled Ha.
have [m' [Hm' HEb]] := labeled_step_enabled Hb.
have Em : m' = m by congruence.
subst m'; case: (enabled_labels_disjoint_or_equal HEa HEb)=>[E|Hd]; last by right.
left; exact: ordered_participants_injective (labeled_step_ordered Ha) (labeled_step_ordered Hb) E.
Qed.

Lemma distinct_labeled_step_zero (P : program) a b c mu nu :
  labeled_step (processes P) a c mu -> labeled_step (processes P) b c nu -> a <> b ->
  forall outcome, successful_component (branch_value mu outcome) = CQState.bottom.
Proof.
move=>Ha Hb Hab outcome.
have Hd : [disjoint participants a & participants b]%SET.
  by case: (labeled_steps_disjoint_or_equal Ha Hb)=>[E|//]; exfalso; apply: Hab.
have [m [Hm HEb]] := labeled_step_enabled Hb.
apply: (disjoint_enabled_successful_component HEb Hd).
exact: (@labeled_step_controls _ _ _ _ _ Ha outcome).
Qed.

Lemma weighted_successful_zero n (mu : family (global_configuration n)) m :
  (forall i, successful_component (branch_value mu i) = CQState.bottom) ->
  weighted_sum mu (fun c => successful_component c m) = 0.
Proof.
move=>H; rewrite /weighted_sum (eq_sum (g := fun _ => 0)).
  by move=>i; rewrite H CQState.bottomE scaler0.
exact: summable_sum_cst0.
Qed.

Theorem global_steps_successful_equal (P : program) c mu nu m :
  configuration_owned (processes P) c ->
  global_step (processes P) c mu -> global_step (processes P) c nu ->
  weighted_sum mu (fun d => successful_component d m) =
  weighted_sum nu (fun d => successful_component d m).
Proof.
move=>Hown Hmu Hnu; have [a Ha] := labeled_step_complete Hmu.
have [b Hb] := labeled_step_complete Hnu.
case: (pselect (a = b))=>[E|E].
- subst b; have Emu : mu = nu.
    exact: (@labeled_step_deterministic _ _ _ _ _ _ (@processes_wf P) Hown Ha Hb).
  by rewrite Emu.
- rewrite !weighted_successful_zero //.
  + exact: distinct_labeled_step_zero Ha Hb E.
  + apply: distinct_labeled_step_zero Hb Ha _.
    by move=>F; apply: E; symmetry.
Qed.
End DistributedGlobalActions.


Module DistributedGlobalInstruments.
(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedResults DistributedResidual DistributedProgress DistributedGlobalActions DistributedInstruments.

Record descriptor n := Descriptor {
  instruction : statement;
  update_control : statement -> ('I_n -> control) -> ('I_n -> control)
}.
Arguments Descriptor {n} instruction update_control.
Arguments instruction {n} d.
Arguments update_control {n} d s pc i.

Definition local_descriptor n (p : 'I_n -> process) i s : descriptor n :=
  Descriptor s (fun t pc => replace pc i (after_local (p i) t)).
Definition done_descriptor n (i : 'I_n) : descriptor n :=
  Descriptor (Atomic ASkip) (fun _ pc => replace pc i Stopped).
Definition communication_descriptor n (p : 'I_n -> process) i k j l effect : descriptor n :=
  Descriptor (Atomic effect) (fun _ pc =>
    replace (replace pc i (Executing (process_body (p i) j)))
      k (Executing (process_body (p k) l))).
Arguments communication_descriptor {n} p i k j l effect.

Definition descriptor_lift n (d : descriptor n) pc (c : local_configuration) :=
  global_config (update_control d c.1.1 pc) c.1.2 c.2.
Definition descriptor_run n (d : descriptor n) pc m rho :=
  fmap (descriptor_lift d pc) (local_successor (instruction d) m rho).

Inductive enabled_descriptor n (p : 'I_n -> process) pc m :
    action n -> descriptor n -> Prop :=
| EnabledInstruction i s : pc i = Executing s ->
    enabled_descriptor p pc m (Local i) (local_descriptor p i s)
| EnabledDone i : pc i = Waiting ->
    [forall j, ~~ eval (process_guard (p i) j) m] ->
    enabled_descriptor p pc m (Local i) (done_descriptor i)
| EnabledCommunication (i k : 'I_n) j l t (x : CL.variable t) e :
    (i < k)%N -> pc i = Waiting -> pc k = Waiting ->
    eval (process_guard (p i) j) m -> eval (process_guard (p k) l) m ->
    matches (process_io (p i) j) (process_io (p k) l) (AAssign x e) ->
    enabled_descriptor p pc m (Rendezvous i k)
      (communication_descriptor p i k j l (AAssign x e)).

Lemma enabled_instruction_wf n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> statement_wf (instruction d).
Proof.
move=>Hown; case=>[i s Hpc|i Hpc Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch] //=.
by move: (Hown i); rewrite /= Hpc=>/proj1.
Qed.

Lemma descriptor_step n (p : 'I_n -> process) pc m rho a d :
  enabled_descriptor p pc m a d -> statement_wf (instruction d) ->
  labeled_step p a (global_config pc (Some m) rho) (descriptor_run d pc m rho).
Proof.
case=>[i s Hpc|i Hpc Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hwf.
- apply: LParallel Hpc _; exact: local_successor_step Hwf m rho.
- exact: LProcessDone Hpc Hnone.
- exact: LCommunication Hik Hi Hk Hj Hl Hmatch.
Qed.

Lemma labeled_step_descriptor n (p : 'I_n -> process) a c mu :
  configuration_owned p c -> labeled_step p a c mu ->
  exists m d, c.1.2 = Some m /\ enabled_descriptor p c.1.1 m a d /\
    statement_wf (instruction d) /\ mu = descriptor_run d c.1.1 m c.2.
Proof.
move=>Hown Hstep; case: Hstep Hown=>
  [pc m rho i s nu Hpc Hloc|pc m rho i Hpc Hnone|
   pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hown.
- have Hs : statement_wf s.
    by move: (Hown i); rewrite /= Hpc=>/proj1.
  exists m, (local_descriptor p i s); split=>//; split.
  + exact: EnabledInstruction Hpc.
  + split=>//; rewrite (local_step_canonical Hloc Hs erefl); by [].
- exists m, (done_descriptor i); split=>//; split.
  + exact: EnabledDone Hpc Hnone.
  + by split.
- exists m, (communication_descriptor p i k j l (AAssign x e)); split=>//; split.
  + exact: EnabledCommunication Hik Hi Hk Hj Hl Hmatch.
  + by split.
Qed.

Lemma descriptor_update_outside n (p : 'I_n -> process) pc m a d :
  enabled_descriptor p pc m a d -> forall s pc' i,
  i \notin participants a -> update_control d s pc' i = pc' i.
Proof.
case=>[j t Hj|j Hj Hnone|j k h l t x e Hjk Hj Hk Hh Hl Hmatch] s pc' i.
- rewrite inE=>Hi; exact: replace_other Hi.
- rewrite inE=>Hi; exact: replace_other Hi.
- rewrite !inE negb_or=>/andP[Hij Hik]; by rewrite /= !replace_other.
Qed.

Lemma descriptor_update_inside n (p : 'I_n -> process) pc m a d :
  enabled_descriptor p pc m a d -> forall s pc' pc'' i,
  i \in participants a -> update_control d s pc' i = update_control d s pc'' i.
Proof.
case=>[j t Hj|j Hj Hnone|j k h l t x e Hjk Hj Hk Hh Hl Hmatch] s pc' pc'' i.
- rewrite inE=>/eqP->; by rewrite /= !replace_same.
- rewrite inE=>/eqP->; by rewrite /= !replace_same.
- rewrite !inE=>/orP[/eqP->|/eqP->]; rewrite /= /replace !eqxx //.
Qed.

Lemma descriptor_update_pointwise n (p : 'I_n -> process) pc m a d :
  enabled_descriptor p pc m a d -> forall s pc' i,
  update_control d s pc' i =
    if i \in participants a then update_control d s pc i else pc' i.
Proof.
move=>Hd s pc' i; case E: (i \in participants a).
- exact: (@descriptor_update_inside _ _ _ _ _ _ Hd s pc' pc i E).
- apply: (@descriptor_update_outside _ _ _ _ _ _ Hd s pc' i).
  by rewrite E.
Qed.

Lemma descriptor_updates_commute n (p : 'I_n -> process) pc m a b d e :
  enabled_descriptor p pc m a d -> enabled_descriptor p pc m b e ->
  [disjoint participants a & participants b]%SET -> forall s t,
  update_control d s (update_control e t pc) = update_control e t (update_control d s pc).
Proof.
move=>Hd He Hdis s t; apply/funext=>i.
rewrite (descriptor_update_pointwise Hd s (update_control e t pc) i)
  (descriptor_update_pointwise He t (update_control d s pc) i).
case Ha: (i \in participants a); case Hb: (i \in participants b)=>//.
- by move/disjointP: Hdis=>/(_ i Ha); rewrite Hb.
- rewrite (@descriptor_update_outside _ _ _ _ _ _ Hd s pc i) ?Ha //.
  by rewrite (@descriptor_update_outside _ _ _ _ _ _ He t pc i) ?Hb.
Qed.

Definition processes_agree n (p : 'I_n -> process) (A : {set 'I_n}) (m m' : cmem) :=
  forall i, i \in A -> forall u (x : CL.variable u),
    process_reads (p i) (name_of x) -> (m.[x] = m'.[x])%M.

Lemma process_guard_reads p j x : expression_reads (process_guard p j) x -> process_reads p x.
Proof. move=>Hx; right; exists j=>//; left; by left. Qed.

Lemma process_io_reads p j x : communication_reads (process_io p j) x -> process_reads p x.
Proof. move=>Hx; right; exists j=>//; left; by right. Qed.

Lemma process_guard_agree n (p : 'I_n -> process) A m m' i j :
  processes_agree p A m m' -> i \in A ->
  eval (process_guard (p i) j) m = eval (process_guard (p i) j) m'.
Proof.
move=>Hagree Hi; apply: ClassicalFootprint.eval_local=>u x Hx.
apply: (Hagree i Hi u x); exact: process_guard_reads Hx.
Qed.

Lemma enabled_descriptor_preserved n (p : 'I_n -> process) pc m a d pc' m' :
  enabled_descriptor p pc m a d ->
  (forall i, i \in participants a -> pc' i = pc i) ->
  processes_agree p (participants a) m m' -> enabled_descriptor p pc' m' a d.
Proof.
move=>Hd; case: Hd=>[i s Hi|i Hi Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch]
  Hpc Hagree.
- apply: EnabledInstruction; rewrite Hpc ?inE ?eqxx //.
- have Hii : i \in [set i] by rewrite inE eqxx.
  apply: EnabledDone; first by rewrite Hpc ?inE ?eqxx //.
  apply/forallP=>j; rewrite -(@process_guard_agree n p [set i] m m' i j Hagree Hii).
  exact: (forallP Hnone j).
- have Hii : i \in [set i; k] by rewrite !inE eqxx.
  have Hkk : k \in [set i; k] by rewrite !inE eqxx orbT.
  apply: EnabledCommunication Hik _ _ _ _ Hmatch.
  + by rewrite Hpc ?inE ?eqxx //.
  + by rewrite Hpc ?inE ?eqxx ?orbT //.
  + by rewrite -(@process_guard_agree n p [set i; k] m m' i j Hagree Hii).
  + by rewrite -(@process_guard_agree n p [set i; k] m m' k l Hagree Hkk).
Qed.

Lemma matches_reads a b effect : matches a b effect -> forall x,
  atom_reads effect x -> communication_reads a x \/ communication_reads b x.
Proof. case=>t c y e x; first by []. by move=>[H|H]; [right | left]. Qed.

Lemma matches_changes a b effect : matches a b effect -> forall x,
  x \in atom_changes effect -> x \in communication_changes a \/ x \in communication_changes b.
Proof. case=>t c y e x Hx; [by left | by right]. Qed.

Lemma process_io_changes p j x : x \in communication_changes (process_io p j) ->
  x \in process_changes p.
Proof.
move=>Hx; rewrite /process_changes in_fsetU; apply/orP; right.
apply/bigfcupP; exists j; first by rewrite mem_index_enum.
by rewrite in_fsetU Hx.
Qed.

Lemma descriptor_reads_owned n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> forall x, statement_reads (instruction d) x ->
  exists i, i \in participants a /\ process_reads (p i) x.
Proof.
move=>Hown; case=>[i s Hi|i Hi Hnone|i k j l t y e Hik Hi Hk Hj Hl Hmatch] x Hx.
- exists i; split; first by rewrite inE eqxx.
  have Ho := Hown i; rewrite /= Hi in Ho; exact: (proj1 (proj2 (proj2 Ho)) x Hx).
- by [].
- case: (matches_reads Hmatch Hx)=>[Hx'|Hx'].
  + exists i; split; first by rewrite !inE eqxx.
    exact: process_io_reads Hx'.
  + exists k; split; first by rewrite !inE eqxx orbT.
    exact: process_io_reads Hx'.
Qed.

Lemma descriptor_changes_owned n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> forall x, x \in statement_changes (instruction d) ->
  exists i, i \in participants a /\ x \in process_changes (p i).
Proof.
move=>Hown; case=>[i s Hi|i Hi Hnone|i k j l t y e Hik Hi Hk Hj Hl Hmatch] x Hx.
- exists i; split; first by rewrite inE eqxx.
  have Ho := Hown i; rewrite /= Hi in Ho.
  exact: (fsubsetP (proj1 (proj2 Ho)) x Hx).
- by move: Hx; rewrite inE.
- case: (matches_changes Hmatch Hx)=>[Hx'|Hx'].
  + exists i; split; first by rewrite !inE eqxx.
    exact: process_io_changes Hx'.
  + exists k; split; first by rewrite !inE eqxx orbT.
    exact: process_io_changes Hx'.
Qed.

Lemma descriptor_quantum_owned n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d -> forall x, x \in statement_quantum (instruction d) ->
  exists i, i \in participants a /\ x \in process_quantum (p i).
Proof.
move=>Hown; case=>[i s Hi|i Hi Hnone|i k j l t y e Hik Hi Hk Hj Hl Hmatch] x Hx.
- exists i; split; first by rewrite inE eqxx.
  have Ho := Hown i; rewrite /= Hi in Ho.
  exact: (fintype.subsetP (proj2 (proj2 (proj2 Ho))) x Hx).
- by move: Hx; rewrite inE.
- by move: Hx; rewrite inE.
Qed.

Lemma disjoint_participants_neq n (A B : {set 'I_n}) i j :
  [disjoint A & B]%SET -> i \in A -> j \in B -> i != j.
Proof.
move=>Hdis Hi Hj; apply/negP=>/eqP E; subst j.
by move/disjointP: Hdis=>/(_ i Hi); rewrite Hj.
Qed.

Lemma descriptor_private_reads (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET -> forall x,
  statement_reads (instruction d) x -> x \notin statement_changes (instruction e).
Proof.
move=>Hown Hd He Hdis x Hx; apply/negP=>Hx'.
have [i [Hi Hir]] := descriptor_reads_owned Hown Hd Hx.
have [j [Hj Hjw]] := descriptor_changes_owned Hown He Hx'.
have Hij := disjoint_participants_neq Hdis Hi Hj.
have Hfresh := proj1 (@processes_private P i j Hij) x Hir.
by move: Hfresh; rewrite Hjw.
Qed.

Lemma descriptor_private_quantum (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET ->
  ((statement_quantum (instruction d) :&: statement_quantum (instruction e)) == finset.set0)%SET.
Proof.
move=>Hown Hd He Hdis; apply/eqP; apply/setP=>x; rewrite !inE.
apply/negP=>/andP[Hxd Hxe].
have [i [Hi Hiq]] := descriptor_quantum_owned Hown Hd Hxd.
have [j [Hj Hjq]] := descriptor_quantum_owned Hown He Hxe.
have Hij := disjoint_participants_neq Hdis Hi Hj.
have Heq := eqP (proj2 (@processes_private P i j Hij)).
have Hmem : x \in (process_quantum (processes P i) :&: process_quantum (processes P j))%SET.
  by rewrite inE Hiq Hjq.
by move: Hmem; rewrite Heq inE.
Qed.

Lemma descriptor_preserves_other_reads (P : program) pc m rho a b d :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  [disjoint participants a & participants b]%SET -> forall outcome m',
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  processes_agree (processes P) (participants b) m m'.
Proof.
move=>Hown Hd Hdis outcome m' Hout i Hi u x Hx.
have Hwf := enabled_instruction_wf Hown Hd.
have Hstep := local_successor_step Hwf m rho.
apply: (@local_step_unchanged _ _ Hstep outcome m m' erefl Hout u x).
apply/negP=>Hwrite; have [j [Hj Hjw]] := descriptor_changes_owned Hown Hd Hwrite.
have Hji := disjoint_participants_neq Hdis Hj Hi.
have Hij : i != j by rewrite eq_sym.
have Hfresh := proj1 (@processes_private P i j Hij) (name_of x) Hx.
by move: Hfresh; rewrite Hjw.
Qed.


Lemma descriptor_other_enabled (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET -> forall outcome m',
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  enabled_descriptor (processes P) (branch_value (descriptor_run d pc m rho) outcome).1.1 m' b e.
Proof.
move=>Hown Hd He Hdis outcome m' Hout; apply: (enabled_descriptor_preserved He).
- move=>i Hi; apply: (@descriptor_update_outside _ _ _ _ _ _ Hd _ pc i).
  by move: Hdis; rewrite disjoint_sym=>/disjointP/(_ i Hi).
- exact: (@descriptor_preserves_other_reads P pc m rho a b d Hown Hd Hdis outcome m' Hout).
Qed.

Lemma descriptor_replay_after (P : program) pc m rho a b d e :
  configuration_owned (processes P) (global_config pc (Some m) rho) ->
  enabled_descriptor (processes P) pc m a d ->
  enabled_descriptor (processes P) pc m b e ->
  [disjoint participants a & participants b]%SET -> forall outcome m',
  (branch_value (descriptor_run d pc m rho) outcome).1.2 = Some m' ->
  labeled_step (processes P) b (branch_value (descriptor_run d pc m rho) outcome)
    (descriptor_run e (branch_value (descriptor_run d pc m rho) outcome).1.1 m'
      (branch_value (descriptor_run d pc m rho) outcome).2).
Proof.
move=>Hown Hd He Hdis outcome m' Hout.
have Henext := @descriptor_other_enabled P pc m rho a b d e Hown Hd He Hdis outcome m' Hout.
have Hewf := enabled_instruction_wf Hown He.
have Hstep := @descriptor_step _ _ _ _
  (branch_value (descriptor_run d pc m rho) outcome).2 _ _ Henext Hewf.
move: Hstep; rewrite -Hout; by case: (branch_value (descriptor_run d pc m rho) outcome)=>[[pc' store'] rho'].
Qed.
End DistributedGlobalInstruments.


Module DistributedChangeAccess.
(* Global Change and Access, distributive paper Lemma 3.4 in fixed ambient memory. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedDistribution DistributedScheduler DistributedLocalActions DistributedInstruments DistributedInterchange DistributedGlobalActions DistributedGlobalInstruments DistributedResidual DistributedProgress DistributedLocalMaps ClassicalFootprint.
Local Notation Hq := 'H[msys]_finset.setT.

Definition optional_agree X (m t : option cmem) :=
  match m, t with
  | Some s, Some u => agree_on X s u
  | None, None => True
  | _, _ => False
  end.

Lemma local_control_agree s X m t i :
  (statement_reads s `<=` X)%classic -> agree_on X m t ->
  (@local_control s m i).1 = (@local_control s t i).1 /\
  optional_agree X (@local_control s m i).2 (@local_control s t i).2.
Proof.
elim: s i=>[|a|s IH u IHu|n g b IH|n g b IH] i /= Hsub Hmt.
- by split.
- case: a i Hsub=>[| |u x e|u x p|u q phi|u q U|u v x q M] i Hsub /=;
    split=>//.
  + have E : eval e m = eval e t.
      apply: eval_reads Hmt=>k Hk; apply: Hsub; by right.
    rewrite E; exact: CQAssertionLocality.agree_on_update.
  + exact: CQAssertionLocality.agree_on_update.
  + exact: CQAssertionLocality.agree_on_update.
- have [Ec Hc] := IH i (fun x Hx => Hsub x (or_introl Hx)) Hmt.
  by split; first rewrite Ec.
- have Eg : (fun j => eval (g j) m) = (fun j => eval (g j) t).
    apply/funext=>j; apply: eval_reads Hmt=>k Hk; apply: Hsub.
    exists j=>//; by left.
  rewrite Eg; case: pickP=>[j Hj|Hnone] /=; by split.
- have Eg : (fun j => eval (g j) m) = (fun j => eval (g j) t).
    apply/funext=>j; apply: eval_reads Hmt=>k Hk; apply: Hsub.
    exists j=>//; by left.
  rewrite Eg; case: pickP=>[j Hj|Hnone] /=; by split.
Qed.

Lemma local_control_frame s m i out : (@local_control s m i).2 = Some out ->
  unchanged (statement_changes s) m out.
Proof.
move=>E; have H := @local_store_outcome s m i.
rewrite E in H; case: H=>[//|[[= Eout]|[u [x [v [Hx [= Eout]]]]]]]; subst out.
- exact: unchanged_refl.
- move=>t y Hy; apply: update_unchanged.
  rewrite inE; apply/negP=>/eqP Ee; move: Hy; by rewrite Ee Hx.
Qed.

Lemma local_maps_sum_qo s m : sum (local_maps s m) \is cptn.
Proof. apply: itnorm_ge0_le1P; [exact: vdistr_sum_ge0 | exact: vdistr_sum_le1]. Qed.

Lemma atom_map_supported a m i :
  exists E : 'SO_(atom_quantum a), @atom_map a m i = liftfso E.
Proof.
case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i /=;
  try by exists \:1; rewrite liftfso1.
- exists (CL.probability_mass p m i *: (\:1 : 'SO_finset.set0)).
  by rewrite linearZ /= liftfso1.
- by exists (initialso (tv2v q (eval phi m))).
- by exists (formso (tf2f q q (eval U m))).
- exists (formso (tf2f q q (eval M m i))); exact: ClassicalSemantics.measurement_branchE.
Qed.

Lemma local_map_supported s m i :
  exists E : 'SO_(statement_quantum s), @local_map s m i = liftfso E.
Proof.
elim: s i=>[|a|s IH t IHt|n g b IH|n g b IH] i /=;
  try by exists \:1; rewrite liftfso1.
- exact: atom_map_supported.
- have [E HE] := IH i.
  exists (liftso (finset.subsetUl (statement_quantum s) (statement_quantum t)) E).
  by rewrite liftfso2.
Qed.

Definition network_reads n (p : 'I_n -> process) : set classical_name :=
  fun x => exists i, process_reads (p i) x.
Definition network_quantum n (p : 'I_n -> process) : {set mlab} :=
  \bigcup_i process_quantum (p i).

Lemma network_agree n (p : 'I_n -> process) m t A :
  agree_on (network_reads p) m t -> processes_agree p A m t.
Proof. move=>H i Hi u x Hx; apply: H; by exists i. Qed.

Lemma descriptor_read_subset n (p : 'I_n -> process) pc m rho a d :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d ->
  (statement_reads (instruction d) `<=` network_reads p)%classic.
Proof.
move=>Ho Hd x Hx; have [i [Hi Hr]] := descriptor_reads_owned Ho Hd Hx.
by exists i.
Qed.

Lemma descriptor_map_local n (p : 'I_n -> process) pc m rho a d S (F : 'SO_S) i :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d ->
  [disjoint network_quantum p & S]%SET ->
  @local_map (instruction d) m i :o liftfso F =
    liftfso F :o @local_map (instruction d) m i.
Proof.
move=>Ho Hd Hdis; apply: local_map_external.
apply: fintype.disjointWl Hdis; apply/fintype.subsetP=>x Hx.
have [j [Hj Hq]] := descriptor_quantum_owned Ho Hd Hx.
apply/finset.bigcupP; by exists j.
Qed.

Lemma descriptor_map_supported n (p : 'I_n -> process) pc m rho a d i :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d ->
  exists E : 'CP_(network_quantum p), @local_map (instruction d) m i = liftfso E.
Proof.
move=>Ho Hd.
have Hsub : (statement_quantum (instruction d) :<=: network_quantum p)%SET.
  apply/fintype.subsetP=>x Hx.
  have [j [Hj Hq]] := descriptor_quantum_owned Ho Hd Hx.
  apply/finset.bigcupP; by exists j.
have [E HE] := @local_map_supported (instruction d) m i.
pose F := liftso Hsub E.
have EF : @local_map (instruction d) m i = liftfso F by rewrite /F liftfso2.
have HF : F \is cpmap.
  rewrite -geso0_cpE liftfso_ge0 -EF geso0_cpE; exact: local_map_cp.
by exists (CPMap_Build HF).
Qed.

Lemma descriptor_store_frame n (p : 'I_n -> process) pc m rho a d t i out :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d ->
  (@local_control (instruction d) t i).2 = Some out ->
  forall u (x : CL.variable u),
  (forall j, name_of x \notin process_changes (p j)) -> (t.[x] = out.[x])%M.
Proof.
move=>Ho Hd E u x Hfresh; apply: (local_control_frame E).
apply/negP=>Hx; have [j [Hj Hw]] := descriptor_changes_owned Ho Hd Hx.
by move: (Hfresh j); rewrite Hw.
Qed.

(* The maps and residual controls are frozen at the original store m; only
   the branch store functions are evaluated at the new store t. *)
Definition replay_family n (d : descriptor n) pc m t rho : family (global_configuration n) :=
  @Family _ (local_index (instruction d))
    (fun i => \Tr (@local_map (instruction d) m i rho))
    (fun i => global_config (update_control d (@local_control (instruction d) m i).1 pc)
      (@local_control (instruction d) t i).2
      (normalized_output (@local_map (instruction d) m i) rho)).

Lemma descriptor_replay n (p : 'I_n -> process) pc m rho a d t r :
  configuration_owned p (global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d ->
  agree_on (network_reads p) m t -> r \is den1lf ->
  labeled_step p a (global_config pc (Some t) r) (replay_family d pc m t r).
Proof.
move=>Ho Hd Hmt Hr.
have Hsub := descriptor_read_subset Ho Hd.
have Hlocal : agree_on (statement_reads (instruction d)) m t.
  move=>u x Hx; apply: Hmt; exact: Hsub.
have Hd' : enabled_descriptor p pc t a d.
  apply: (enabled_descriptor_preserved Hd); first by [].
  exact: network_agree Hmt.
have Hwf := enabled_instruction_wf Ho Hd.
have Hstep := @descriptor_step n p pc t r a d Hd' Hwf.
rewrite /descriptor_run (local_realization _ _ Hr) /local_family /fmap /descriptor_lift
  /local_config /replay_family in Hstep *.
suff E : @Family (global_configuration n) (local_index (instruction d))
    (fun i => \Tr (@local_map (instruction d) t i r))
    (fun i => global_config (update_control d (@local_control (instruction d) t i).1 pc)
      (@local_control (instruction d) t i).2
      (normalized_output (@local_map (instruction d) t i) r)) =
  @Family (global_configuration n) (local_index (instruction d))
    (fun i => \Tr (@local_map (instruction d) m i r))
    (fun i => global_config (update_control d (@local_control (instruction d) m i).1 pc)
      (@local_control (instruction d) t i).2
      (normalized_output (@local_map (instruction d) m i) r)) by rewrite -E.
congr (@Family _ _ _ _); apply/funext=>i.
- by rewrite (local_map_agree i Hlocal).
- have [Ec _] := @local_control_agree (instruction d) (network_reads p) m t i Hsub Hmt.
  by rewrite Ec (local_map_agree i Hlocal).
Qed.


Record change_access_witness (P : program) pc m rho mu
    (a : action (process_count P)) (d : descriptor (process_count P)) : Prop :=
  ChangeAccessWitness {
  access_enabled : enabled_descriptor (processes P) pc m a d;
  access_instruction_wf : statement_wf (instruction d);
  access_maps_cp : forall i, @local_map (instruction d) m i \is cpmap;
  access_maps_summable : summable (local_maps (instruction d) m);
  access_maps_trace_nonincreasing : sum (local_maps (instruction d) m) \is cptn;
  access_realization : mu = replay_family d pc m m rho;
  access_classical_frame : forall t i out,
    (@local_control (instruction d) t i).2 = Some out ->
    forall u (x : CL.variable u),
    (forall j, name_of x \notin process_changes (processes P j)) ->
    (t.[x] = out.[x])%M;
  access_classical_locality : forall t,
    agree_on (network_reads (processes P)) m t -> forall i,
    (@local_control (instruction d) m i).1 = (@local_control (instruction d) t i).1 /\
    optional_agree (network_reads (processes P))
      (@local_control (instruction d) m i).2 (@local_control (instruction d) t i).2 /\
    @local_map (instruction d) m i = @local_map (instruction d) t i;
  access_quantum_supported : forall i, exists E : 'CP_(network_quantum (processes P)),
    @local_map (instruction d) m i = liftfso E;
  access_quantum_locality : forall S (F : 'SO_S) i,
    [disjoint network_quantum (processes P) & S] ->
    @local_map (instruction d) m i :o liftfso F =
      liftfso F :o @local_map (instruction d) m i;
  access_replay : forall t r,
    agree_on (network_reads (processes P)) m t -> r \is den1lf ->
    global_step (processes P) (global_config pc (Some t) r)
      (replay_family d pc m t r);
  access_residual_owned : forall i,
    configuration_owned (processes P) (branch_value mu i)
}.

Theorem global_step_change_access (P : program) pc m rho mu :
  rho \is den1lf -> configuration_owned (processes P) (global_config pc (Some m) rho) ->
  global_step (processes P) (global_config pc (Some m) rho) mu ->
  exists a d, @change_access_witness P pc m rho mu a d.
Proof.
move=>Hr Ho Hstep.
have [a Ha] := labeled_step_complete Hstep.
have [t [d [Et [Hd [Hwf E]]]]] := labeled_step_descriptor Ho Ha.
change (Some m = Some t) in Et; case: Et=>Emt; subst t.
exists a, d; constructor.
- exact: Hd.
- exact: Hwf.
- exact: local_map_cp.
- exact: vdistr_summable.
- exact: local_maps_sum_qo.
- by rewrite E /descriptor_run (local_realization _ _ Hr).
- move=>t i out Eout; exact: (@descriptor_store_frame _ _ _ _ _ _ _ t i out Ho Hd Eout).
- move=>t Hmt i.
  have Hsub := descriptor_read_subset Ho Hd.
  have [Ec Hc] := @local_control_agree (instruction d) (network_reads (processes P)) m t i Hsub Hmt.
  split=>//; split=>//; apply: local_map_agree=>u x Hx.
  apply: Hmt; exact: Hsub.
- move=>i; exact: (@descriptor_map_supported _ _ _ _ _ _ _ i Ho Hd).
- move=>S F i Hdis; exact: (@descriptor_map_local _ _ _ _ _ _ _ S F i Ho Hd Hdis).
- move=>t r Hmt Hr'; apply: labeled_step_erasure.
  exact: (@descriptor_replay _ _ _ _ _ _ _ t r Ho Hd Hmt Hr').
- move=>i. exact (@global_step_owned (process_count P) (processes P)
    (global_config pc (Some m) rho) mu (@processes_wf P) Ho Hstep i).
Qed.

Corollary initial_change_access (P : program) m rho mu :
  rho \is den1lf -> global_step (processes P) (initial_configuration (processes P) m rho) mu ->
  exists a d, @change_access_witness P (fun i => Executing (initialization (processes P i))) m rho mu a d.
Proof.
move=>Hr Hstep; apply: global_step_change_access Hr _ Hstep.
exact: initial_configuration_owned (@processes_wf P).
Qed.
End DistributedChangeAccess.


Module DistributedMemoryReplay.
(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions DistributedInstruments DistributedGlobalInstruments DistributedResidual DistributedChangeAccess DistributedInterchange ClassicalFootprint CQMemoryInterpretation.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section Memory.
Variable S : {set mlab}.
Variable L : finType.
Variable H : L -> chsType.
Variable T V : {set L}.
Variable sub : T :<=: V.
Variable U : 'FGI('H[msys]_S, 'H[H]_T).
Local Notation HW := 'H[H]_V.
Definition local_configuration := (statement * option cmem * 'End(HW))%type.
Definition local_config s m rho : local_configuration := (s,m,rho).
Definition append_configuration t (c : local_configuration) :=
  local_config (append c.1.1 t) c.1.2 c.2.
Definition measurement_branch {t u : qType} (x : CL.variable (QType t))
    (q : wf_qreg u) (qS : mset q :<=: S)
    (M : mexpr (eval_qtype t) (eval_qtype u))
    (m : cmem) (rho : 'End(HW)) : family local_configuration :=
  let R := fun i => @measurement_channel S L H T V sub U t u q qS (eval M m) i rho in
  let p := fun i => \Tr (R i) in
  @Family _ (eval_qtype t) p (fun i =>
    local_config Finished (Some (m.[x <- i])%M)
      (if 0 < p i then (p i)^-1 *: R i else rho)).

Inductive local_step : local_configuration -> family local_configuration -> Prop :=
| StepSkip m rho :
    local_step (local_config (Atomic ASkip) (Some m) rho)
      (certain (local_config Finished (Some m) rho))
| StepAbort m rho :
    local_step (local_config (Atomic AAbort) (Some m) rho)
      (certain (local_config Finished None rho))
| StepAssign t (x : CL.variable t) e m rho :
    local_step (local_config (Atomic (AAssign x e)) (Some m) rho)
      (certain (local_config Finished (Some (m.[x <- eval e m])%M) rho))
| StepRandom t (x : CL.variable t) mu m rho :
    local_step (local_config (Atomic (@ARandom t x mu)) (Some m) rho)
      (@Family _ (CL.value t) (fun v => CL.probability_mass mu m v)
        (fun v => local_config Finished (Some (m.[x <- v])%M) rho))
| StepInitial t (q : wf_qreg t) (qS : mset q :<=: S) phi m rho :
    local_step (local_config (Atomic (AInitial q phi)) (Some m) rho)
      (certain (local_config Finished (Some m)
        (@initialize_channel S L H T V sub U t q qS (eval phi m) rho)))
| StepUnitary t (q : wf_qreg t) (qS : mset q :<=: S) (A : uexpr (eval_qtype t)) m rho :
    local_step (local_config (Atomic (AUnitary q A)) (Some m) rho)
      (certain (local_config Finished (Some m)
        (@unitary_channel S L H T V sub U t q qS (eval A m) rho)))
| StepMeasure t u (x : CL.variable (QType t)) (q : wf_qreg u)
    (qS : mset q :<=: S) (M : mexpr (eval_qtype t) (eval_qtype u)) m rho :
    local_step (local_config (Atomic (AMeasure x q M)) (Some m) rho)
      (measurement_branch x qS M m rho)
| StepSequence s t m rho mu :
    local_step (local_config s (Some m) rho) mu ->
    local_step (local_config (Sequence s t) (Some m) rho)
      (fmap (append_configuration t) mu)
| StepAlternative n (g : 'I_n -> expression bool) b (i : 'I_n) m rho :
    eval (g i) m ->
    local_step (local_config (Alternative g b) (Some m) rho)
      (certain (local_config (b i) (Some m) rho))
| StepAlternativeFail n (g : 'I_n -> expression bool) b m rho :
    [forall i, ~~ eval (g i) m] ->
    local_step (local_config (Alternative g b) (Some m) rho)
      (certain (local_config Finished None rho))
| StepRepetition n (g : 'I_n -> expression bool) b (i : 'I_n) m rho :
    eval (g i) m ->
    local_step (local_config (Repetition g b) (Some m) rho)
      (certain (local_config (Sequence (b i) (Repetition g b)) (Some m) rho))
| StepRepetitionDone n (g : 'I_n -> expression bool) b m rho :
    [forall i, ~~ eval (g i) m] ->
    local_step (local_config (Repetition g b) (Some m) rho)
      (certain (local_config Finished (Some m) rho)).

Definition global_configuration n :=
  (('I_n -> control) * option cmem * 'End(HW))%type.
Definition global_config n (pc : 'I_n -> control) m rho : global_configuration n :=
  (pc,m,rho).
Definition replace n (pc : 'I_n -> control) (i : 'I_n) c :=
  fun j => if j == i then c else pc j.
Definition lift_local n (p : 'I_n -> process) pc (i : 'I_n)
    (c : local_configuration) :=
  global_config (replace pc i (after_local (p i) c.1.1)) c.1.2 c.2.

Inductive global_step n (p : 'I_n -> process) :
    global_configuration n -> family (global_configuration n) -> Prop :=
| StepParallel pc m rho i s mu :
    pc i = Executing s ->
    local_step (local_config s (Some m) rho) mu ->
    global_step p (global_config pc (Some m) rho) (fmap (lift_local p pc i) mu)
| StepProcessDone pc m rho i :
    pc i = Waiting ->
    [forall j, ~~ eval (process_guard (p i) j) m] ->
    global_step p (global_config pc (Some m) rho)
      (certain (global_config (replace pc i Stopped) (Some m) rho))
| StepCommunication pc m rho (i k : 'I_n) j l t (x : CL.variable t) e :
    (i < k)%N -> pc i = Waiting -> pc k = Waiting ->
    eval (process_guard (p i) j) m -> eval (process_guard (p k) l) m ->
    matches (process_io (p i) j) (process_io (p k) l) (AAssign x e) ->
    global_step p (global_config pc (Some m) rho)
      (certain (global_config
        (replace (replace pc i (Executing (process_body (p i) j)))
          k (Executing (process_body (p k) l)))
        (Some (m.[x <- eval e m])%M) rho)).


Lemma measurement_probability_nonnegative t u (q : wf_qreg u) (qS : mset q :<=: S)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho : rho \is den1lf ->
    forall i, 0 <= \Tr (@measurement_channel S L H T V sub U t u q qS (eval M m) i rho).
Proof. by move=>Pr i; apply: psdlf_trlf; apply: cp_psdP; apply: den1lf_psd. Qed.

Lemma measurement_probability_total t u (q : wf_qreg u) (qS : mset q :<=: S)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho :
    sum (fun i => \Tr (@measurement_channel S L H T V sub U t u q qS (eval M m) i rho)) = \Tr rho.
Proof.
rewrite fin_dom_sum -linear_sum /= -sum_soE -fin_dom_sum.
by apply/tpmapP/measurement_sum_tp.
Qed.

Lemma measurement_branch_probability t u (x : CL.variable (QType t)) (q : wf_qreg u) (qS : mset q :<=: S)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho : rho \is den1lf ->
    probability_family (measurement_branch x qS M m rho).
Proof.
move=>Pr; split; first exact: fin_dom_summable.
split; first exact: measurement_probability_nonnegative.
by rewrite /family_mass /measurement_branch /= measurement_probability_total den1lf_trlf.
Qed.

Lemma measurement_branch_normalized t u (x : CL.variable (QType t)) (q : wf_qreg u) (qS : mset q :<=: S)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho i : rho \is den1lf ->
    (branch_value (measurement_branch x qS M m rho) i).2 \is den1lf.
Proof.
move=>Pr; rewrite /measurement_branch /=; case: ifP=>P; last exact: Pr.
apply/den1lfP; split.
  apply: psdlfZ; first by rewrite invr_ge0; exact: ltW P.
  by apply: cp_psdP; exact: den1lf_psd Pr.
by rewrite linearZ /= mulVf ?gt_eqF.
Qed.

Lemma local_step_probability c mu : local_step c mu -> c.2 \is den1lf ->
  probability_family mu.
Proof.
move=>Hstep; induction Hstep; move=>Pr; try exact: certain_probability.
- split; first exact: summable_mu.
  split; first exact: ge0_mu.
  exact: CL.probability_normalized.
- exact: measurement_branch_probability.
- apply: fmap_probability; exact: IHHstep.
Qed.

Lemma local_step_normalized c mu : local_step c mu -> c.2 \is den1lf ->
  forall i, (branch_value mu i).2 \is den1lf.
Proof.
move=>Hstep; induction Hstep; move=>Pr outcome;
  cbn [branch_value certain fmap append_configuration local_config];
  try exact Pr.
- exact: (@qc_den1lf HW HW
    (@initialize_channel S L H T V sub U t q qS (eval phi m)) (Den1Lf_Build Pr)).
- exact: (@qc_den1lf HW HW
    (@unitary_channel S L H T V sub U t q qS (eval A m)) (Den1Lf_Build Pr)).
- exact: measurement_branch_normalized.
- exact: IHHstep.
Qed.

Lemma global_step_probability n (p : 'I_n -> process) c mu :
  global_step p c mu -> c.2 \is den1lf -> probability_family mu.
Proof.
move=>Hstep; case: Hstep=>[pc m rho i s nu Hpc Hloc|
  pc m rho i Hpc Hnone|pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hr;
  try exact: certain_probability.
apply: fmap_probability; exact: local_step_probability Hloc Hr.
Qed.

Lemma global_step_normalized n (p : 'I_n -> process) c mu :
  global_step p c mu -> c.2 \is den1lf ->
  forall i, (branch_value mu i).2 \is den1lf.
Proof.
move=>Hstep; case: Hstep=>[pc m rho i s nu Hpc Hloc|
  pc m rho i Hpc Hnone|pc m rho i k j l t x e Hik Hi Hk Hj Hl Hmatch] Hr outcome;
  try exact Hr.
change ((branch_value nu outcome).2 \is den1lf).
exact: (local_step_normalized Hloc Hr outcome).
Qed.

Definition atom_successor (a : atom) :
    atom_quantum a :<=: S -> cmem -> 'End(HW) -> family local_configuration :=
  match a as a' return atom_quantum a' :<=: S -> cmem -> 'End(HW) -> family local_configuration with
  | ASkip => fun _ m rho => certain (local_config Finished (Some m) rho)
  | AAbort => fun _ m rho => certain (local_config Finished None rho)
  | AAssign _ x e => fun _ m rho => certain (local_config Finished (Some (m.[x <- eval e m])%M) rho)
  | ARandom t x mu => fun _ m rho => @Family _ (CL.value t) (fun v => CL.probability_mass mu m v)
      (fun v => local_config Finished (Some (m.[x <- v])%M) rho)
  | AInitial t q phi => fun qS m rho => certain (local_config Finished (Some m)
      (@initialize_channel S L H T V sub U t q qS (eval phi m) rho))
  | AUnitary t q A => fun qS m rho => certain (local_config Finished (Some m)
      (@unitary_channel S L H T V sub U t q qS (eval A m) rho))
  | AMeasure t u x q M => fun qS m rho => measurement_branch x qS M m rho
  end.

Arguments atom_successor : clear implicits.

Fixpoint local_successor (s : statement) :
    statement_quantum s :<=: S -> cmem -> 'End(HW) -> family local_configuration :=
  match s as s' return statement_quantum s' :<=: S -> cmem -> 'End(HW) -> family local_configuration with
  | Finished => fun _ m rho => certain (local_config Finished (Some m) rho)
  | Atomic a => atom_successor a
  | Sequence s t => fun sS m rho => fmap (append_configuration t)
      (@local_successor s (fintype.subset_trans (finset.subsetUl _ _) sS) m rho)
  | Alternative n g b => fun _ m rho =>
      if [pick j | eval (g j) m] is Some j
      then certain (local_config (b j) (Some m) rho)
      else certain (local_config Finished None rho)
  | Repetition n g b => fun _ m rho =>
      if [pick j | eval (g j) m] is Some j
      then certain (local_config (Sequence (b j) (Repetition g b)) (Some m) rho)
      else certain (local_config Finished (Some m) rho)
  end.

Arguments local_successor : clear implicits.

Lemma atom_successor_step a aS m rho :
  local_step (local_config (Atomic a) (Some m) rho) (atom_successor a aS m rho).
Proof. by case: a aS=>[| |t x e|t x p|t q phi|t q A|t u x q M] aS; constructor. Qed.

Lemma local_successor_step s sS : statement_wf s -> forall m rho,
  local_step (local_config s (Some m) rho) (local_successor s sS m rho).
Proof.
elim: s sS=>[|a|s IHs t IHt|n g b IHb|n g b IHb] sS //= Hwf m rho.
- exact: atom_successor_step.
- apply: StepSequence; exact: IHs _ (proj1 Hwf) m rho.
- case: pickP=>[i Hi|Hnone].
  + exact: StepAlternative Hi.
  + apply: StepAlternativeFail; by apply/forallP=>i; rewrite Hnone.
- case: pickP=>[i Hi|Hnone].
  + exact: StepRepetition Hi.
  + apply: StepRepetitionDone; by apply/forallP=>i; rewrite Hnone.
Qed.

Definition atom_map (a : atom) : atom_quantum a :<=: S -> cmem -> atom_index a -> 'SO(HW) :=
  match a as a' return atom_quantum a' :<=: S -> cmem -> atom_index a' -> 'SO(HW) with
  | ARandom _ _ p => fun _ m i => CL.probability_mass p m i *: \:1
  | AInitial t q phi => fun qS m _ => @initialize_channel S L H T V sub U t q qS (eval phi m)
  | AUnitary t q A => fun qS m _ => @unitary_channel S L H T V sub U t q qS (eval A m)
  | AMeasure t u _ q M => fun qS m i => @measurement_channel S L H T V sub U t u q qS (eval M m) i
  | _ => fun _ _ _ => \:1
  end.

Arguments atom_map : clear implicits.

Fixpoint local_map s : statement_quantum s :<=: S -> cmem -> local_index s -> 'SO(HW) :=
  match s as s' return statement_quantum s' :<=: S -> cmem -> local_index s' -> 'SO(HW) with
  | Atomic a => atom_map a
  | Sequence s t => fun sS => @local_map s (fintype.subset_trans (finset.subsetUl _ _) sS)
  | _ => fun _ _ _ => \:1
  end.

Arguments local_map : clear implicits.

Definition normalized_output (E : 'SO(HW)) rho :=
  if 0 < \Tr (E rho) then (\Tr (E rho))^-1 *: E rho else rho.

Lemma normalized_channel (E : 'QC(HW)) rho : rho \is den1lf ->
  normalized_output E rho = E rho.
Proof.
move=>Hr; rewrite /normalized_output qc_trlfE (den1lf_trlf Hr) ltr01 invr1 scale1r.
by [].
Qed.

Lemma normalized_scalar p rho : rho \is den1lf ->
  normalized_output (p *: (\:1 : 'SO(HW))) rho = rho.
Proof.
move=>Hr; rewrite /normalized_output !soE linearZ /= (den1lf_trlf Hr) mulr1.
case: ifP=>Hp; last by [].
by rewrite scalerA mulVf ?gt_eqF // scale1r.
Qed.

Definition local_family s sS m rho : family local_configuration :=
  @Family _ (local_index s) (fun i => \Tr (local_map s sS m i rho))
    (fun i => local_config (@local_control s m i).1 (@local_control s m i).2
      (normalized_output (local_map s sS m i) rho)).


Arguments local_family : clear implicits.

Lemma atom_realization a aS m rho : rho \is den1lf ->
  atom_successor a aS m rho = local_family (Atomic a) aS m rho.
Proof.
move=>Hr; case: a aS=>[| |t x e|t x p|t q phi|t q A|t u x q M] aS;
  rewrite /atom_successor /local_family /=.
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- congr (@Family _ _ _ _); apply/funext=>i.
  + by rewrite !soE linearZ /= (den1lf_trlf Hr) mulr1.
  + by rewrite normalized_scalar.
- by rewrite normalized_channel // qc_trlfE (den1lf_trlf Hr).
- by rewrite normalized_channel // qc_trlfE (den1lf_trlf Hr).
- by rewrite /measurement_branch /normalized_output.
Qed.

Lemma local_realization s sS m rho : rho \is den1lf ->
  local_successor s sS m rho = local_family s sS m rho.
Proof.
move=>Hr; elim: s sS=>[|a|s IH t IHt|n g b IH|n g b IH] sS /=.
- by rewrite /local_family /= normalized_channel // !soE (den1lf_trlf Hr).
- exact: atom_realization.
- by rewrite IH /local_family /fmap /append_configuration /local_config.
- rewrite /local_family /=; case: pickP=>[i Hi|Hnone];
    by rewrite normalized_channel // !soE (den1lf_trlf Hr).
- rewrite /local_family /=; case: pickP=>[i Hi|Hnone];
    by rewrite normalized_channel // !soE (den1lf_trlf Hr).
Qed.

Definition descriptor_lift n (d : descriptor n) pc (c : local_configuration) :=
  global_config (update_control d c.1.1 pc) c.1.2 c.2.
Definition descriptor_run n (d : descriptor n) dS pc m rho :=
  fmap (descriptor_lift d pc) (local_successor (instruction d) dS m rho).

Arguments descriptor_run {n} d dS pc m rho.

Lemma descriptor_step n (p : 'I_n -> process) pc m rho a d dS :
  enabled_descriptor p pc m a d -> statement_wf (instruction d) ->
  global_step p (global_config pc (Some m) rho) (descriptor_run d dS pc m rho).
Proof.
move=>Hd; case: Hd dS=>[i s Hpc|i Hpc Hnone|i k j l t x e Hik Hi Hk Hj Hl Hmatch] dS Hwf.
- apply: StepParallel Hpc _; exact: local_successor_step Hwf m rho.
- exact: StepProcessDone Hpc Hnone.
- exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
Qed.

Lemma atom_map_agree a aS m t i : agree_on (atom_reads a) m t ->
  atom_map a aS m i = atom_map a aS t i.
Proof.
case: a aS i=>[| |u x e|u x p|u q phi|u q A|u v x q M] aS i Hagree //=.
- have E : eval (CL.probability_expression p) m = eval (CL.probability_expression p) t.
    apply: eval_reads Hagree=>k Hk; by right.
  change (eval (CL.probability_expression p) m i *: (\:1 : 'SO(HW)) =
    eval (CL.probability_expression p) t i *: (\:1 : 'SO(HW))).
  by rewrite E.
- by rewrite (eval_reads (fun k Hk => Hk) Hagree).
- by rewrite (eval_reads (fun k Hk => Hk) Hagree).
- have EM : eval M m = eval M t.
    apply: eval_reads Hagree; by move=>k Hk; right.
  by rewrite EM.
Qed.

Lemma local_map_agree s sS m t i : agree_on (statement_reads s) m t ->
  local_map s sS m i = local_map s sS t i.
Proof.
elim: s sS i=>[|a|s IH u IHu|n g b IH|n g b IH] sS i Hagree //=.
- exact: atom_map_agree.
- apply: IH=>v x Hx; apply: Hagree; by left.
Qed.

Definition replay_family n (d : descriptor n) dS pc m t rho : family (global_configuration n) :=
  @Family _ (local_index (instruction d))
    (fun i => \Tr (local_map (instruction d) dS m i rho))
    (fun i => global_config (update_control d (@local_control (instruction d) m i).1 pc)
      (@local_control (instruction d) t i).2
      (normalized_output (local_map (instruction d) dS m i) rho)).

Arguments replay_family {n} d dS pc m t rho.

Lemma descriptor_replay n (p : 'I_n -> process) pc m rho a d dS t r :
  configuration_owned p (DistributedOperational.global_config pc (Some m) rho) ->
  enabled_descriptor p pc m a d ->
  agree_on (network_reads p) m t -> r \is den1lf ->
  global_step p (global_config pc (Some t) r) (replay_family d dS pc m t r).
Proof.
move=>Ho Hd Hmt Hr.
have Hsub := descriptor_read_subset Ho Hd.
have Hlocal : agree_on (statement_reads (instruction d)) m t.
  move=>u x Hx; apply: Hmt; exact: Hsub.
have Hd' : enabled_descriptor p pc t a d.
  apply: (enabled_descriptor_preserved Hd); first by [].
  exact: network_agree Hmt.
have Hwf := enabled_instruction_wf Ho Hd.
have Hstep := @descriptor_step n p pc t r a d dS Hd' Hwf.
rewrite /descriptor_run (local_realization _ _ Hr) /local_family /fmap /descriptor_lift
  /local_config /replay_family in Hstep *.
suff E : @Family (global_configuration n) (local_index (instruction d))
    (fun i => \Tr (local_map (instruction d) dS t i r))
    (fun i => global_config (update_control d (@local_control (instruction d) t i).1 pc)
      (@local_control (instruction d) t i).2
      (normalized_output (local_map (instruction d) dS t i) r)) =
  @Family (global_configuration n) (local_index (instruction d))
    (fun i => \Tr (local_map (instruction d) dS m i r))
    (fun i => global_config (update_control d (@local_control (instruction d) m i).1 pc)
      (@local_control (instruction d) t i).2
      (normalized_output (local_map (instruction d) dS m i) r)) by rewrite -E.
congr (@Family _ _ _ _); apply/funext=>i.
- by rewrite (@local_map_agree (instruction d) dS m t i Hlocal).
- have [Ec _] := @local_control_agree (instruction d) (network_reads p) m t i Hsub Hmt.
  by rewrite Ec (@local_map_agree (instruction d) dS m t i Hlocal).
Qed.

Definition source_atom_map (a : atom) : atom_quantum a :<=: S -> cmem -> atom_index a -> 'SO[msys]_S :=
  match a as a' return atom_quantum a' :<=: S -> cmem -> atom_index a' -> 'SO[msys]_S with
  | ARandom _ _ p => fun _ m i => CL.probability_mass p m i *: \:1
  | AInitial t q phi => fun qS m _ => liftso qS (initialso (tv2v q (eval phi m)))
  | AUnitary t q A => fun qS m _ => liftso qS (formso (tf2f q q (eval A m)))
  | AMeasure t u _ q M => fun qS m i => liftso qS (formso (tf2f q q (eval M m i)))
  | _ => fun _ _ _ => \:1
  end.

Arguments source_atom_map : clear implicits.

Fixpoint source_local_map s : statement_quantum s :<=: S -> cmem -> local_index s -> 'SO[msys]_S :=
  match s as s' return statement_quantum s' :<=: S -> cmem -> local_index s' -> 'SO[msys]_S with
  | Atomic a => source_atom_map a
  | Sequence s t => fun sS => @source_local_map s (fintype.subset_trans (finset.subsetUl _ _) sS)
  | _ => fun _ _ _ => \:1
  end.

Arguments source_local_map : clear implicits.

Lemma source_atom_mapE a aS m i :
  @DistributedInstruments.atom_map a m i = liftfso (source_atom_map a aS m i).
Proof.
case: a aS i=>[| |t x e|t x p|t q phi|t q A|t u x q M] aS i /=;
  try by rewrite liftfso1.
- by rewrite linearZ /= liftfso1.
- by rewrite liftfso2.
- by rewrite liftfso2.
- by rewrite liftfso2 ClassicalSemantics.measurement_branchE.
Qed.

Lemma source_local_mapE s sS m i :
  @DistributedInstruments.local_map s m i = liftfso (source_local_map s sS m i).
Proof.
elim: s sS i=>[|a|s IH t IHt|n g b IH|n g b IH] sS i /=;
  try by rewrite liftfso1.
- exact: source_atom_mapE.
- exact: IH.
Qed.

Lemma source_local_map_cp s sS m i : source_local_map s sS m i \is cpmap.
Proof.
rewrite -geso0_cpE liftfso_ge0 -(source_local_mapE sS) geso0_cpE.
exact: DistributedInstruments.local_map_cp.
Qed.

Lemma source_local_maps_lift s sS m :
  (fun i => liftfso (source_local_map s sS m i)) =
  (fun i => @DistributedLocalMaps.local_maps s m i).
Proof.
apply/funext=>i.
by rewrite DistributedLocalMaps.local_mapsE source_local_mapE.
Qed.

Lemma source_local_maps_summable s sS m : summable (source_local_map s sS m).
Proof.
apply: CQMemoryInstruments.liftfso_summable_reflect.
rewrite source_local_maps_lift; exact: vdistr_summable.
Qed.

Lemma source_local_maps_cptn s sS m : sum (source_local_map s sS m) \is cptn.
Proof.
apply: CQMemoryInstruments.liftfso_sum_cptn_reflect.
- rewrite source_local_maps_lift; exact: vdistr_summable.
- rewrite source_local_maps_lift; exact: local_maps_sum_qo.
Qed.

Lemma atom_map_covariance a aS m i : atom_map a aS m i =
  @transport S L H T V sub U (source_atom_map a aS m i).
Proof.
case: a aS i=>[| |t x e|t x p|t q phi|t q A|t u x q M] aS i /=;
  try by rewrite transport1.
- by rewrite linearZ /= transport1.
- exact: initialize_channelE.
- exact: unitary_channelE.
- exact: measurement_channelE.
Qed.

Lemma local_map_covariance s sS m i : local_map s sS m i =
  @transport S L H T V sub U (source_local_map s sS m i).
Proof.
elim: s sS i=>[|a|s IH t IHt|n g b IH|n g b IH] sS i /=;
  try by rewrite transport1.
- exact: atom_map_covariance.
- exact: IH.
Qed.

Theorem global_step_memory_replay (P : program) pc m rho mu :
  network_quantum (processes P) :<=: S ->
  rho \is den1lf ->
  configuration_owned (processes P) (DistributedOperational.global_config pc (Some m) rho) ->
  DistributedOperational.global_step (processes P)
    (DistributedOperational.global_config pc (Some m) rho) mu ->
  exists a d (dS : statement_quantum (instruction d) :<=: S),
    @change_access_witness P pc m rho mu a d /\
    forall t r, agree_on (network_reads (processes P)) m t -> r \is den1lf ->
    global_step (processes P) (global_config pc (Some t) r)
      (replay_family d dS pc m t r).
Proof.
move=>HNS Hr Ho Hstep.
have [a [d Hw]] := global_step_change_access Hr Ho Hstep.
have Hd := access_enabled Hw.
have Hds : statement_quantum (instruction d) :<=: S.
  apply: fintype.subset_trans _ HNS; apply/fintype.subsetP=>x Hx.
  have [j [Hj Hq]] := descriptor_quantum_owned Ho Hd Hx.
  apply/finset.bigcupP; by exists j.
exists a, d, Hds; split=>// t r Hmt Hr'.
exact: (@descriptor_replay _ _ _ _ _ _ _ Hds t r Ho Hd Hmt Hr').
Qed.

Lemma replay_family_transport n (d : descriptor n) dS pc m t r :
  replay_family d dS pc m t r =
  @Family (global_configuration n) (local_index (instruction d))
    (fun i => \Tr (@transport S L H T V sub U
      (source_local_map (instruction d) dS m i) r))
    (fun i => global_config (update_control d (@local_control (instruction d) m i).1 pc)
      (@local_control (instruction d) t i).2
      (normalized_output (@transport S L H T V sub U
        (source_local_map (instruction d) dS m i)) r)).
Proof.
rewrite /replay_family; congr (@Family _ _ _ _); apply/funext=>i;
  by rewrite local_map_covariance.
Qed.

Theorem global_step_memory_change_access (P : program) pc m rho mu :
  network_quantum (processes P) :<=: S ->
  rho \is den1lf ->
  configuration_owned (processes P) (DistributedOperational.global_config pc (Some m) rho) ->
  DistributedOperational.global_step (processes P)
    (DistributedOperational.global_config pc (Some m) rho) mu ->
  exists a d (dS : statement_quantum (instruction d) :<=: S),
    @change_access_witness P pc m rho mu a d /\
    summable (source_local_map (instruction d) dS m) /\
    sum (source_local_map (instruction d) dS m) \is cptn /\
    forall t r, agree_on (network_reads (processes P)) m t -> r \is den1lf ->
    global_step (processes P) (global_config pc (Some t) r)
      (replay_family d dS pc m t r) /\
    probability_family (replay_family d dS pc m t r) /\
    forall i, (branch_value (replay_family d dS pc m t r) i).2 \is den1lf.
Proof.
move=>HNS Hr Ho Hstep.
have [a [d [dS [Hw Hrun]]]] := global_step_memory_replay HNS Hr Ho Hstep.
exists a, d, dS; split=>//; split.
- exact: source_local_maps_summable.
- split; first exact: source_local_maps_cptn.
  move=>t r Hmt Hr'; have Htarget := Hrun t r Hmt Hr'.
  split=>//; split.
  + exact: global_step_probability Htarget Hr'.
  + move=>i; exact: (global_step_normalized Htarget Hr' i).
Qed.

End Memory.
End DistributedMemoryReplay.
