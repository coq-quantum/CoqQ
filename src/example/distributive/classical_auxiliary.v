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


From quantum.example.classical Require Import footprint ghost_ranking.
From quantum.example.distributive Require Import network_rules operational_hoare local_hoare.

Module DistributedClassicalAuxiliary.
Import DistributedLanguage DistributedSequentialization DistributedGuardedRules DistributedNetworkRules
  CQAssertion CQPredicate ClassicalFootprint.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma mask_three (g p q : pred cmem) :
  mask g (mask (fun m => p m && q m) (@semantic_top cmem Hq)) =
  mask (fun m => g m && p m && q m) semantic_top.
Proof.
apply/funext=>m; rewrite /mask; by case: (g m); case: (p m); case: (q m).
Qed.

Theorem valid_fresh_guarded_loop (P : assertion) (p0 : expression bool)
    (r : expression int) (z : CL.variable CL.Integer)
    (bs : seq (expression bool * CL.command)) X :
  (CL.variables (conditional_chain bs) `<=` X)%classic ->
  (CL.expression_variables (branch_guard bs) `<=` X)%classic ->
  (CL.expression_variables p0 `<=` X)%classic ->
  (CL.expression_variables r `<=` X)%classic -> ~ X (CL.key z) ->
  semantic_le P (mask (eval p0) semantic_top) ->
  (forall m, eval p0 m -> 0 <= eval r m) ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true (mask (eval bc.1) P) bc.2 P) bs ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true
      (mask (fun m => eval bc.1 m && eval p0 m && (eval r m == (m.[z])%M)) semantic_top)
      bc.2 (mask (fun m => eval r m < (m.[z])%M) semantic_top)) bs ->
  CQHoare.valid true P (CL.While (branch_guard bs) (conditional_chain bs))
    (mask (predC (eval (branch_guard bs))) P).
Proof.
move=>Hc Hb Hp Hr Hz Hsupport Hnonneg Hinv Hdec.
apply: (@CQGhostRanking.valid_fresh_integer_while P p0 (branch_guard bs)
  r z (conditional_chain bs) X Hc Hb Hp Hr Hz Hsupport Hnonneg).
- exact: guarded_list_valid Hinv.
- rewrite -mask_three; apply: guarded_list_valid.
  elim: Hdec=>[|[g c] rest Hhead Hrest IH]; constructor=>//.
  by rewrite mask_three.
Qed.

Theorem classical_repetition (P : assertion) (p0 : expression bool)
    (r : expression int) (z : CL.variable CL.Integer)
    n (g : 'I_n -> expression bool) (b : 'I_n -> statement) X :
  statement_wf (Repetition g b) ->
  (CL.variables (conditional_chain [seq (g i,translate_statement (b i)) | i <- enum 'I_n]) `<=` X)%classic ->
  (CL.expression_variables (branch_guard [seq (g i,translate_statement (b i)) | i <- enum 'I_n]) `<=` X)%classic ->
  (CL.expression_variables p0 `<=` X)%classic ->
  (CL.expression_variables r `<=` X)%classic -> ~ X (CL.key z) ->
  semantic_le P (mask (eval p0) semantic_top) ->
  (forall m, eval p0 m -> 0 <= eval r m) ->
  (forall i, DistributedLocalHoare.valid true (mask (eval (g i)) P) (b i) P) ->
  (forall i, DistributedLocalHoare.valid true
    (mask (fun m => eval (g i) m && eval p0 m && (eval r m == (m.[z])%M)) semantic_top)
    (b i) (mask (fun m => eval r m < (m.[z])%M) semantic_top)) ->
  DistributedLocalHoare.valid true P (Repetition g b) (mask (predC (enabled g)) P).
Proof.
move=>Hwf Hc Hb Hp Hr Hz Hsupport Hnonneg Hinv Hdec.
apply/(proj2 (@DistributedLocalHoare.valid_translate_iff true P (Repetition g b)
  (mask (predC (enabled g)) P) Hwf)).
pose bs := [seq (g i,translate_statement (b i)) | i <- enum 'I_n].
have EB : branch_guard bs = loop_guard g.
  by rewrite /branch_guard /bs -map_comp.
have EE : eval (branch_guard bs) = enabled g.
  apply/funext=>m; rewrite EB; exact: eval_loop_guard.
rewrite -EE.
change (CQHoare.valid true P (CL.While (loop_guard g) (conditional_chain bs))
  (mask (predC (eval (branch_guard bs))) P)).
rewrite -EB.
apply: (@valid_fresh_guarded_loop P p0 r z bs X Hc Hb Hp Hr Hz Hsupport Hnonneg).
- apply: mapped_branches_valid=>i.
  exact: (proj1 (@DistributedLocalHoare.valid_translate_iff true
    (mask (eval (g i)) P) (b i) P (proj2 Hwf i)) (Hinv i)).
- rewrite /bs; elim: (enum 'I_n)=>[|i indices IH] /=; constructor=>//.
  exact: (proj1 (@DistributedLocalHoare.valid_translate_iff true _ (b i) _
    (proj2 Hwf i)) (Hdec i)).
Qed.


Theorem classical_distributed (P Q : assertion) (S : program) (p0 : expression bool)
    (r : expression int) (z : CL.variable CL.Integer) X :
  (CL.variables (conditional_chain (rendezvous_commands (processes S))) `<=` X)%classic ->
  (CL.expression_variables (branch_guard (rendezvous_commands (processes S))) `<=` X)%classic ->
  (CL.expression_variables p0 `<=` X)%classic ->
  (CL.expression_variables r `<=` X)%classic -> ~ X (CL.key z) ->
  semantic_le Q (mask (eval p0) semantic_top) ->
  (forall m, eval p0 m -> 0 <= eval r m) ->
  (forall m, eval p0 m -> blocked (processes S) m -> DistributedLanguage.term (processes S) m) ->
  CQHoare.valid true P (initialization_command (processes S)) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands (processes S)) ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.valid true
      (mask (fun m => eval bc.1 m && eval p0 m && (eval r m == (m.[z])%M)) semantic_top)
      bc.2 (mask (fun m => eval r m < (m.[z])%M) semantic_top))
    (rendezvous_commands (processes S)) ->
  DistributedHoare.valid true P S (mask (DistributedLanguage.term (processes S)) Q).
Proof.
move=>Hc Hb Hp Hr Hz Hsupport Hnonneg Hdead Hinit Hinv Hdec.
have Hloop := @valid_fresh_guarded_loop Q p0 r z (rendezvous_commands (processes S)) X
  Hc Hb Hp Hr Hz Hsupport Hnonneg Hinv Hdec.
have Hcover : semantic_le (mask (blocked (processes S)) Q)
    (mask (DistributedLanguage.term (processes S)) semantic_top).
  move=>m; rewrite /mask; case Hb0: (blocked (processes S) m); last exact: obsf_ge0.
  case Hp0: (eval p0 m).
  - rewrite (Hdead m Hp0 Hb0); exact: obsf_le1.
  - apply: (le_trans (y := (0 : 'End(Hq)))); last exact: obsf_ge0.
    by move: (Hsupport m); rewrite /mask Hp0.
have Hmask : semantic_le (mask (blocked (processes S)) Q) Q.
  by move=>m; rewrite /mask; case: (blocked (processes S) m)=>//; exact: obsf_ge0.
have Et : eval (termination_guard (processes S)) = DistributedLanguage.term (processes S).
  by apply/funext=>m; exact: eval_termination_guard.
apply/(proj2 (DistributedHoare.valid_translate_iff _ _ _ _)).
rewrite /successful_sequentialize.
apply: (CQHoare.valid_sequence (Q := mask (blocked (processes S)) Q)).
- exact: CQHoare.valid_sequence Hinit Hloop.
- rewrite -Et; apply: final_test_total Hmask _.
  by rewrite Et.
Qed.

End DistributedClassicalAuxiliary.
