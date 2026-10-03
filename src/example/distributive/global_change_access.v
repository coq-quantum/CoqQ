(* Global Change and Access, distributive paper Lemma 3.4 in fixed ambient memory. *)
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
From Stdlib Require List.
From quantum.example.distributive Require Import language operational sequentialization guarded_rules.
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


From quantum.example.distributive Require Import distribution scheduler local_actions
  instruments interchange global_actions global_instruments residual progress local_correspondence.
From quantum.example.classical Require Import footprint assertion_locality.

Module DistributedChangeAccess.
Import DistributedLanguage DistributedOperational DistributedDistribution
  DistributedScheduler DistributedLocalActions DistributedInstruments
  DistributedInterchange DistributedGlobalActions DistributedGlobalInstruments
  DistributedResidual DistributedProgress DistributedLocalCorrespondence
  ClassicalFootprint.
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
- exists (formso (tf2f q q (eval M m i))); exact: CL.measurement_branchE.
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
