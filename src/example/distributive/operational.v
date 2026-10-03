(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import language.

Module DistributedOperational.
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
  let R := fun i => CL.measurement_branches q M m i rho in
  let p := fun i => \Tr (R i) in
  @Family _ (eval_qtype t) p (fun i =>
    local_config Finished (Some (m.[x <- i])%M)
      (if 0 < p i then (p i)^-1 *: R i else rho)).

Lemma measurement_probability_nonnegative t u (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho : rho \is den1lf ->
    forall i, 0 <= \Tr (CL.measurement_branches q M m i rho).
Proof. by move=>Pr i; apply: psdlf_trlf; apply: cp_psdP; apply: den1lf_psd. Qed.

Lemma measurement_probabilities_summable t u (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho :
    summable (fun i => \Tr (CL.measurement_branches q M m i rho)).
Proof. exact: fin_dom_summable. Qed.

Lemma measurement_probability_total t u (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) m rho :
    sum (fun i => \Tr (CL.measurement_branches q M m i rho)) = \Tr rho.
Proof.
rewrite -cvg_linear_sum.
  apply: sum_summable_soE_is_cvg; exact: summable_cvg.
rewrite -(sum_summable_soE rho
  (summable_cvg (f := CL.measurement_branches q M m))).
by apply/tpmapP/CL.measurement_complete.
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
