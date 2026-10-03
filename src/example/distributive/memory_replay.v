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
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import language operational scheduler local_actions instruments global_instruments residual global_change_access interchange local_correspondence.

From quantum.example.classical Require Import footprint.
From quantum.example.classical Require Import memory_interpretation memory_instruments.
Module DistributedMemoryReplay.
Import DistributedLanguage DistributedOperational DistributedScheduler
  DistributedLocalActions DistributedInstruments DistributedGlobalInstruments
  DistributedResidual DistributedChangeAccess DistributedInterchange
  ClassicalFootprint CQMemoryInterpretation.
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
- by rewrite liftfso2 CL.measurement_branchE.
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
  (fun i => @DistributedLocalCorrespondence.local_maps s m i).
Proof.
apply/funext=>i.
by rewrite DistributedLocalCorrespondence.local_mapsE source_local_mapE.
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
