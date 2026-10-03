(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)
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
Local Open Scope classical_set_scope.


From quantum.example.distributive Require Import serial_scheduler residual_semantics stopped_invariant results.

From quantum.example.distributive Require Import boundary_semantics active_pairs weighted.

Module DistributedRendezvousHarmonic.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedSerialScheduler DistributedResidualSemantics DistributedStoppedInvariant
  DistributedBoundarySemantics DistributedActivePairs DistributedWeighted.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma first_enabled_has n (p : 'I_n -> process) indices m a :
  first_enabled indices m = Some a ->
  has (fun bc : expression bool * CL.command => eval bc.1 m)
    (pmap (@index_command n p) indices).
Proof.
elim: indices=>[|b indices IH] //=.
case Eb: (index_command b)=>[[g c]|] /=.
- case Eg: (eval g m)=>//=; exact: IH.
- exact: IH.
Qed.

Lemma selected_loop_guard n (p : 'I_n -> process) m a :
  first_enabled (rendezvous_indices p) m = Some a ->
  eval (guards_any [seq bc.1 | bc <- rendezvous_commands p]) m.
Proof.
move=>H; rewrite eval_guards_any has_map -rendezvous_indicesE.
exact: first_enabled_has H.
Qed.

Lemma network_tail_selected n (p : 'I_n -> process) m a g c :
  first_enabled (rendezvous_indices p) m = Some a -> index_command a = Some (g,c) ->
  CL.denote (network_tail p) m = slet (CL.denote c) (CL.denote (network_tail p)) m.
Proof.
move=>Hfirst Ha; have Hg := selected_loop_guard Hfirst.
have [g' [c' [Ha' [Hg' Hchain]]]] := selected_rendezvous_command Hfirst.
rewrite Ha in Ha'; case: Ha'=>[= Eg Ec]; subst g' c'.
pose B := guards_any [seq bc.1 | bc <- rendezvous_commands p].
pose C := conditional_chain (rendezvous_commands p).
pose W := CL.While B C.
pose T := CL.Conditional (termination_guard p) CL.Skip CL.Abort.
have Hw : CL.denote W m = slet (CL.denote C) (CL.denote W) m.
  by rewrite {1}/W {1}CL.denote_while_unfold CL.denote_conditional Hg.
change (slet (CL.denote W) (CL.denote T) m =
  slet (CL.denote c) (slet (CL.denote W) (CL.denote T)) m).
rewrite (slet_row_eq _ Hw) sletA.
exact: slet_row_eq Hchain.
Qed.

Lemma assignment_sequence t (x : CL.variable t) e (K : CL.kernel) m :
  slet (CL.denote (CL.Assign x e)) K m = K (m.[x <- eval e m])%M.
Proof.
apply/vdistrP=>out.
change (slet_def (assign_sem x e) K m out = K (m.[x <- eval e m])%M out).
rewrite /slet_def (fin_supp_sum (S := [fset (m.[x <- eval e m])%M]%fset)).
- move=>j; rewrite inE=>/negPf Hj.
  by rewrite /assign_sem /sunit /= /sunit_def Hj comp_so0r.
- by rewrite psum1 /assign_sem /sunit /= /sunit_def eqxx comp_so1r.
Qed.

Lemma ready_enabled_waiting n (p : 'I_n -> process) pc m i j :
  ready pc -> stopped_valid p pc m -> eval (process_guard (p i) j) m -> pc i = Waiting.
Proof.
move=>Hready Hvalid Hg; have [Hi|Hi] := Hready i; first exact: Hi.
by have Hfalse := Hvalid i Hi j; rewrite Hg in Hfalse.
Qed.

Theorem residual_rendezvous_step n (p : 'I_n -> process) pc m rho a :
  ready pc -> stopped_valid p pc m -> rho \is denlf ->
  first_enabled (rendezvous_indices p) m = Some a ->
  exists mu, global_step p (global_config pc (Some m) rho) mu /\
    forall out, weighted_sum mu (fun c => residual_state p c out) =
      residual_state p (global_config pc (Some m) rho) out.
Proof.
move=>Hready Hv Hr Hfirst.
have [g [c [Ha [Hg Hchain]]]] := selected_rendezvous_command Hfirst.
have [effect [Hik [Hj [Hl [Hmatch HE]]]]] := index_enabled_data Ha Hg.
have Hi := ready_enabled_waiting Hready Hv Hj.
have Hk := ready_enabled_waiting Hready Hv Hl.
have Hass : exists t (x : CL.variable t) (e : expression (CL.value t)), effect = AAssign x e.
  by case: Hmatch=>t ch x e; exists t, x, e.
case: Hass=>t [x [e He]]; subst effect.
exists (certain (global_config
  (replace (replace pc (first_process a)
    (Executing (process_body (p (first_process a)) (first_branch a))))
    (second_process a) (Executing (process_body (p (second_process a)) (second_branch a))))
  (Some (m.[x <- eval e m])%M) rho)); split.
- exact: StepCommunication Hik Hi Hk Hj Hl Hmatch.
- move=>out; rewrite weighted_certain !residual_stateE //.
  rewrite (residual_idle p Hready) (@network_tail_selected n p m a g c Hfirst Ha) HE.
  rewrite (@residual_active_pair n p pc (first_process a) (second_process a)
    (process_body (p (first_process a)) (first_branch a))
    (process_body (p (second_process a)) (second_branch a)) Hready Hik).
  change (slet (CL.denote (translate_statement (process_body (p (first_process a)) (first_branch a))))
    (slet (CL.denote (translate_statement (process_body (p (second_process a)) (second_branch a))))
      (CL.denote (network_tail p))) (m.[x <- eval e m])%M out rho =
    slet (slet (CL.denote (CL.Assign x e))
      (slet (CL.denote (translate_statement (process_body (p (first_process a)) (first_branch a))))
        (CL.denote (translate_statement (process_body (p (second_process a)) (second_branch a))))))
      (CL.denote (network_tail p)) m out rho).
  by rewrite !sletA assignment_sequence.
Qed.

End DistributedRendezvousHarmonic.
