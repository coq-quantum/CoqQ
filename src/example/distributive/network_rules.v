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
From quantum.example.distributive Require Import language sequentialization guarded_rules.
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


Module DistributedNetworkRules.
Import DistributedLanguage DistributedSequentialization DistributedGuardedRules CQAssertion CQPredicate.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).
Implicit Types P Q R : assertion.

Definition branch_guard (bs : seq (expression bool * CL.command)) :=
  guards_any [seq bc.1 | bc <- bs].

Lemma eval_branch_guard bs m :
  eval (branch_guard bs) m = has (fun bc => eval bc.1 m) bs.
Proof. by rewrite /branch_guard eval_guards_any has_map. Qed.

Lemma branches_strengthen total P P' Q (bs : seq (expression bool * CL.command)) :
  semantic_le P' P ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total (mask (eval bc.1) P) bc.2 Q) bs ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total (mask (eval bc.1) P') bc.2 Q) bs.
Proof.
move=>Hpre H; elim: H=>[|[g b] rest Hb Hrest IH]; constructor=>//.
apply: (@CQHoare.valid_consequence total (mask (eval g) P) Q
  (mask (eval g) P') Q b); last exact: Hb.
- move=>m; rewrite /mask; by case: (eval g m)=>//; apply: Hpre.
- exact: semantic_le_refl.
Qed.

Lemma guarded_list_valid total P Q (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid total (mask (eval bc.1) P) bc.2 Q) bs ->
  CQHoare.valid total (mask (eval (branch_guard bs)) P) (conditional_chain bs) Q.
Proof.
move=>H; apply: conditional_chain_valid.
- apply: (branches_strengthen _ H)=>m; rewrite /mask.
  by case: (eval (branch_guard bs) m)=>//; apply: obsf_ge0.
- move=>m Hnone; rewrite /mask eval_branch_guard (negbTE Hnone).
  exact: obsf_ge0.
Qed.

Record list_ranking P (bs : seq (expression bool * CL.command)) := ListRanking {
  list_rank : nat -> assertion;
  list_rank_decreases : forall k, semantic_le (list_rank k.+1) (list_rank k);
  list_rank_initial : semantic_le P (list_rank 0%N);
  list_rank_zero : forall m,
    ((fun k => (list_rank k m : 'End(Hq))) @ \oo --> 0)%classic;
  list_rank_step : forall k,
    List.Forall (fun bc : expression bool * CL.command =>
      semantic_le (mask (eval bc.1) (CQRules.wp_command bc.2 (list_rank k)))
        (list_rank k.+1)) bs
}.

Lemma list_ranking_transfer P bs : list_ranking P bs ->
  CQRules.ranking P (branch_guard bs) (conditional_chain bs).
Proof.
move=>[r dec ini zero step]; apply: (CQRules.Ranking (ranking_assertion := r)).
- exact: dec.
- exact: ini.
- exact: zero.
move=>k m; rewrite /mask -/(eval (branch_guard bs) m) eval_branch_guard.
case E: (has (fun bc : expression bool * CL.command => eval bc.1 m) bs);
  last exact: obsf_ge0.
change ((CQRules.pre true (conditional_chain bs) (r k) m : 'End(Hq)) ⊑ r k.+1 m).
apply: conditional_chain_upper; last exact: E.
have H := step k; elim: H=>[|[g b] rest Hb Hrest IH]; constructor=>// Hg.
by move: (Hb m); rewrite /mask Hg.
Qed.

Lemma guarded_list_partial P (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid false (mask (eval bc.1) P) bc.2 P) bs ->
  CQHoare.valid false P (CL.While (branch_guard bs) (conditional_chain bs))
    (mask (predC (eval (branch_guard bs))) P).
Proof. move=>H; apply: CQRules.valid_while_partial; exact: guarded_list_valid. Qed.

Lemma guarded_list_total P (bs : seq (expression bool * CL.command)) :
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true (mask (eval bc.1) P) bc.2 P) bs ->
  list_ranking P bs ->
  CQHoare.valid true P (CL.While (branch_guard bs) (conditional_chain bs))
    (mask (predC (eval (branch_guard bs))) P).
Proof.
move=>H Hr; apply: CQRules.valid_while_total; first exact: guarded_list_valid.
exact: list_ranking_transfer.
Qed.

Definition initialization_command n (p : 'I_n -> process) :=
  foldr CL.Sequence CL.Skip
    [seq translate_statement (initialization (p i)) | i <- enum 'I_n].
Definition blocked n (p : 'I_n -> process) := predC (eval (branch_guard (rendezvous_commands p))).
Definition network_ranking P n (p : 'I_n -> process) :=
  list_ranking P (rendezvous_commands p).

Lemma final_test_partial P Q b : semantic_le P Q ->
  CQHoare.valid false P (CL.Conditional b CL.Skip CL.Abort) (mask (eval b) Q).
Proof.
move=>HP; apply/(proj2 (CQRules.valid_iff _ _ _ _)); rewrite CQRules.pre_conditional=>m.
rewrite /conditional /mask -/(eval b m); case E: (eval b m).
- change ((P m : 'End(Hq)) ⊑ wlp skip_sem (mask (eval b) Q) m).
  by rewrite wlp_skip /mask E; exact: HP.
- change ((P m : 'End(Hq)) ⊑ wlp abort_sem (mask (eval b) Q) m).
  by rewrite wlp_abort; apply: obsf_le1.
Qed.

Lemma final_test_total P Q b : semantic_le P Q ->
  semantic_le P (mask (eval b) semantic_top) ->
  CQHoare.valid true P (CL.Conditional b CL.Skip CL.Abort) (mask (eval b) Q).
Proof.
move=>HP Hcover; apply/(proj2 (CQRules.valid_iff _ _ _ _)); rewrite CQRules.pre_conditional=>m.
rewrite /conditional /mask -/(eval b m); case E: (eval b m).
- change ((P m : 'End(Hq)) ⊑ wp skip_sem (mask (eval b) Q) m).
  by rewrite wp_skip /mask E; exact: HP.
- change ((P m : 'End(Hq)) ⊑ wp abort_sem (mask (eval b) Q) m).
  rewrite wp_abort; by move: (Hcover m); rewrite /mask E.
Qed.

Theorem distributed_partial P Q n (p : 'I_n -> process) :
  CQHoare.valid false P (initialization_command p) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid false (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
  CQHoare.valid false P (successful_sequentialize p) (mask (DistributedLanguage.term p) Q).
Proof.
move=>Hinit Hbranches.
have Et : eval (termination_guard p) = DistributedLanguage.term p.
  by apply/funext=>m; exact: eval_termination_guard.
rewrite -Et /successful_sequentialize.
apply: (CQHoare.valid_sequence (Q := mask (blocked p) Q)).
- apply: (CQHoare.valid_sequence Hinit); exact: guarded_list_partial.
- apply: final_test_partial=>m; rewrite /mask.
  by case: (blocked p m)=>//; apply: obsf_ge0.
Qed.

Theorem distributed_total P Q n (p : 'I_n -> process) :
  CQHoare.valid true P (initialization_command p) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
  network_ranking Q p ->
  semantic_le (mask (blocked p) Q) (mask (DistributedLanguage.term p) semantic_top) ->
  CQHoare.valid true P (successful_sequentialize p) (mask (DistributedLanguage.term p) Q).
Proof.
move=>Hinit Hbranches Hr Hdeadlock.
have Et : eval (termination_guard p) = DistributedLanguage.term p.
  by apply/funext=>m; exact: eval_termination_guard.
rewrite -Et /successful_sequentialize.
apply: (CQHoare.valid_sequence (Q := mask (blocked p) Q)).
- apply: (CQHoare.valid_sequence Hinit); exact: guarded_list_total.
- apply: final_test_total; last by rewrite Et.
  move=>m; rewrite /mask; by case: (blocked p m)=>//; apply: obsf_ge0.
Qed.

(* Network derivability uses the actual independent classical inference system
   in each translated initialization/communication-body premise. Operational
   distributed soundness additionally requires the sequentialization theorem. *)
Inductive derives : bool -> assertion -> forall n, ('I_n -> process) -> assertion -> Prop :=
| DDistributedPartial P Q n (p : 'I_n -> process) :
    CQRules.derives false P (initialization_command p) Q ->
    List.Forall (fun bc : expression bool * CL.command =>
      CQRules.derives false (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
    derives false P p (mask (DistributedLanguage.term p) Q)
| DDistributedTotal P Q n (p : 'I_n -> process) :
    CQRules.derives true P (initialization_command p) Q ->
    List.Forall (fun bc : expression bool * CL.command =>
      CQRules.derives true (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
    network_ranking Q p ->
    semantic_le (mask (blocked p) Q) (mask (DistributedLanguage.term p) semantic_top) ->
    derives true P p (mask (DistributedLanguage.term p) Q)
| DNetworkConsequence total P Q P' Q' n (p : 'I_n -> process) :
    semantic_le P' P -> semantic_le Q Q' -> derives total P p Q ->
    derives total P' p Q'.

Theorem derives_translate_sound total P n (p : 'I_n -> process) Q :
  derives total P p Q -> CQHoare.valid total P (successful_sequentialize p) Q.
Proof.
move=>D; induction D as
  [P0 Q0 n0 p0 Hinit Hbranches
  |P0 Q0 n0 p0 Hinit Hbranches Hr Hdeadlock
  |total0 P0 Q0 P1 Q1 n0 p0 Hpre Hpost D IHD].
- apply: distributed_partial; first exact: CQRules.derives_sound Hinit.
  elim: Hbranches=>[|[g b] rest Hb Hrest IH]; constructor=>//; exact: CQRules.derives_sound.
- apply: distributed_total; [exact: CQRules.derives_sound Hinit | | exact: Hr | exact: Hdeadlock].
  elim: Hbranches=>[|[g b] rest Hb Hrest IH]; constructor=>//; exact: CQRules.derives_sound.
- exact: (@CQHoare.valid_consequence total0 P0 Q0 P1 Q1 (successful_sequentialize p0) Hpre Hpost IHD).
Qed.

End DistributedNetworkRules.
