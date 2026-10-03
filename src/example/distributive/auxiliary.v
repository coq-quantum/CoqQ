(* Distributive: auxiliary. See README.md and PROOF_NOTES.md. *)
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
From quantum.example.distributive Require Import language operational confluence semantics sequentialization hoare.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module DistributedClassicalAuxiliary.
(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization DistributedGuardedRules DistributedNetworkRules CQAssertion CQPredicate ClassicalFootprint.
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
  DistributedNetworkValidity.valid true P S (mask (DistributedLanguage.term (processes S)) Q).
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
apply/(proj2 (DistributedNetworkValidity.valid_translate_iff _ _ _ _)).
rewrite /successful_sequentialize.
apply: (CQHoare.valid_sequence (Q := mask (blocked (processes S)) Q)).
- exact: CQHoare.valid_sequence Hinit Hloop.
- rewrite -Et; apply: final_test_total Hmask _.
  by rewrite Et.
Qed.
End DistributedClassicalAuxiliary.


Module DistributedRankingComplement.
(* Derived Rep-T′ and Dist-T′ rules; see PROOF_NOTES.md. *)


From Stdlib Require List.


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import DistributedCommunication.
Import DistributedLocalMaps DistributedGuardSemantics.
Import DistributedLanguage DistributedSequentialization CQAssertion CQPredicate CQExpectationLimits CQRankingComplement.
Module GR := DistributedGuardedRules.
Module NR := DistributedNetworkRules.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition repetition_ranking_of_partial P n (g : 'I_n -> expression bool) b
    (f : nat -> assertion) (inc : semantic_chain f)
    (ini : semantic_le P (complement (f 0%N)))
    (top : semantic_sup f = semantic_top)
    (step : forall k i, CQHoare.valid false (mask (eval (g i)) (f k.+1))
      (translate_statement (b i)) (f k)) : GR.ranking P g b.
Proof.
apply: (@GR.Ranking P n g b (fun k => complement (f k))).
- exact: complement_decreasing inc.
- exact: ini.
- exact: complement_zero_of_sup inc top.
- move=>k i; apply/(proj2 (guarded_wp_partial_iff _ _ _ _)).
  by rewrite !complementK; exact: step.
Defined.

Theorem repetition_ranking_iff_partial P n (g : 'I_n -> expression bool) b :
  inhabited (GR.ranking P g b) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall k i, CQHoare.valid false (mask (eval (g i)) (f k.+1))
      (translate_statement (b i)) (f k)).
Proof.
split.
- move=>[r]; exists (fun k => complement (GR.ranking_assertion r k)); split.
  + exact: complement_chain (GR.ranking_decreases r).
  + split; first by rewrite complementK; exact: GR.ranking_initial.
    split.
    * exact: complement_sup_top (GR.ranking_decreases r) (GR.ranking_zero r).
    * move=>k i; apply/(proj1 (guarded_wp_partial_iff _ _ _ _)).
      exact: GR.ranking_step.
- move=>[f [inc [ini [top step]]]]; constructor.
  exact: repetition_ranking_of_partial inc ini top step.
Qed.

Theorem repetition_ranking_iff_derivable P n (g : 'I_n -> expression bool) b :
  inhabited (GR.ranking P g b) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall k i, CQHoare.derives false (mask (eval (g i)) (f k.+1))
      (translate_statement (b i)) (f k)).
Proof.
rewrite repetition_ranking_iff_partial; split; move=>[f [inc [ini [top step]]]];
  exists f; split=>//; split=>//; split=>// k i.
- exact: CQHoare.derives_complete (step k i).
- exact: CQHoare.derives_sound (step k i).
Qed.

Theorem repetition_ranking_iff_guarded_derivable P n
    (g : 'I_n -> expression bool) b :
  (forall i, statement_wf (b i)) ->
  (inhabited (GR.ranking P g b) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall k i, GR.derives false (mask (eval (g i)) (f k.+1)) (b i) (f k))).
Proof.
move=>Hwf; rewrite repetition_ranking_iff_partial.
split; move=>[f [inc [ini [top step]]]];
  exists f; split=>//; split=>//; split=>// k i.
- exact: GR.derives_translate_complete (Hwf i) (step k i).
- exact: GR.derives_translate_sound (step k i).
Qed.

Theorem derives_repetition_total_prime P n (g : 'I_n -> expression bool) b
    (f : nat -> assertion) :
  exclusive g ->
  (forall i, GR.derives true (mask (eval (g i)) P) (b i) P) ->
  semantic_chain f -> semantic_le P (complement (f 0%N)) ->
  semantic_sup f = semantic_top ->
  (forall k i, GR.derives false (mask (eval (g i)) (f k.+1)) (b i) (f k)) ->
  GR.derives true P (Repetition g b) (mask (predC (DistributedGuardSemantics.enabled g)) P).
Proof.
move=>Hex inv inc ini top step; apply: GR.DRepetitionTotal=>//.
apply: repetition_ranking_of_partial inc ini top _=>k i.
exact: GR.derives_translate_sound (step k i).
Qed.

Theorem repetition_total_prime P n (g : 'I_n -> expression bool) b
    (f : nat -> assertion) :
  exclusive g -> (forall i, statement_wf (b i)) ->
  (forall i, GR.derives true (mask (eval (g i)) P) (b i) P) ->
  semantic_chain f -> semantic_le P (complement (f 0%N)) ->
  semantic_sup f = semantic_top ->
  (forall k i, GR.derives false (mask (eval (g i)) (f k.+1)) (b i) (f k)) ->
  DistributedLocalHoare.valid true P (Repetition g b) (mask (predC (DistributedGuardSemantics.enabled g)) P).
Proof.
move=>Hex Hwf inv inc ini top step.
apply: DistributedLocalHoare.derives_sound; first by split.
exact: derives_repetition_total_prime Hex inv inc ini top step.
Qed.

Definition list_ranking_of_partial P (bs : seq (expression bool * CL.command))
    (f : nat -> assertion) (inc : semantic_chain f)
    (ini : semantic_le P (complement (f 0%N)))
    (top : semantic_sup f = semantic_top)
    (step : forall k, List.Forall
      (fun bc : expression bool * CL.command =>
        CQHoare.valid false (mask (eval bc.1) (f k.+1)) bc.2 (f k)) bs)
    : NR.list_ranking P bs.
Proof.
apply: (@NR.ListRanking P bs (fun k => complement (f k))).
- exact: complement_decreasing inc.
- exact: ini.
- exact: complement_zero_of_sup inc top.
- move=>k; apply: (@List.Forall_impl _ _ _ _ _ (step k))=>bc Hb.
  apply/(proj2 (guarded_wp_partial_iff _ _ _ _)).
  by rewrite !complementK.
Defined.

Theorem list_ranking_iff_partial P (bs : seq (expression bool * CL.command)) :
  inhabited (NR.list_ranking P bs) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall k, List.Forall (fun bc : expression bool * CL.command =>
      CQHoare.valid false (mask (eval bc.1) (f k.+1)) bc.2 (f k)) bs).
Proof.
split.
- move=>[r]; exists (fun k => complement (NR.list_rank r k)); split.
  + exact: complement_chain (NR.list_rank_decreases r).
  + split; first by rewrite complementK; exact: NR.list_rank_initial.
    split.
    * exact: complement_sup_top (NR.list_rank_decreases r) (NR.list_rank_zero r).
    * move=>k; apply: (@List.Forall_impl _ _ _ _ _ (NR.list_rank_step r k))=>bc Hb.
      apply/(proj1 (guarded_wp_partial_iff _ _ _ _)).
      exact: Hb.
- move=>[f [inc [ini [top step]]]]; constructor.
  exact: list_ranking_of_partial inc ini top step.
Qed.

Theorem list_ranking_iff_derivable P (bs : seq (expression bool * CL.command)) :
  inhabited (NR.list_ranking P bs) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall k, List.Forall (fun bc : expression bool * CL.command =>
      CQHoare.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k)) bs).
Proof.
rewrite list_ranking_iff_partial; split; move=>[f [inc [ini [top step]]]];
  exists f; split=>//; split=>//; split=>// k;
  apply: (@List.Forall_impl _ _ _ _ _ (step k))=>bc Hb.
- exact: CQHoare.derives_complete Hb.
- exact: CQHoare.derives_sound Hb.
Qed.

Theorem network_ranking_iff_derivable P n (p : 'I_n -> process) :
  inhabited (NR.network_ranking P p) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall k, List.Forall (fun bc : expression bool * CL.command =>
      CQHoare.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k))
      (rendezvous_commands p)).
Proof. exact: list_ranking_iff_derivable. Qed.

Theorem derives_distributed_total_prime P Q n (p : 'I_n -> process)
    (f : nat -> assertion) :
  CQHoare.derives true P (NR.initialization_command p) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.derives true (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
  semantic_chain f -> semantic_le Q (complement (f 0%N)) ->
  semantic_sup f = semantic_top ->
  (forall k, List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k))
    (rendezvous_commands p)) ->
  semantic_le (mask (NR.blocked p) Q) (mask (DistributedLanguage.term p) semantic_top) ->
  NR.derives true P p (mask (DistributedLanguage.term p) Q).
Proof.
move=>Hinit Hinv inc ini top step Hdeadlock.
apply: NR.DDistributedTotal=>//.
apply: list_ranking_of_partial inc ini top _=>k.
apply: (@List.Forall_impl _ _ _ _ _ (step k))=>bc Hb.
exact: CQHoare.derives_sound Hb.
Qed.

Theorem distributed_total_prime P Q (S : program) (f : nat -> assertion) :
  CQHoare.derives true P (NR.initialization_command (processes S)) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.derives true (mask (eval bc.1) Q) bc.2 Q)
    (rendezvous_commands (processes S)) ->
  semantic_chain f -> semantic_le Q (complement (f 0%N)) ->
  semantic_sup f = semantic_top ->
  (forall k, List.Forall (fun bc : expression bool * CL.command =>
    CQHoare.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k))
    (rendezvous_commands (processes S))) ->
  semantic_le (mask (NR.blocked (processes S)) Q)
    (mask (DistributedLanguage.term (processes S)) semantic_top) ->
  DistributedNetworkValidity.valid true P S (mask (DistributedLanguage.term (processes S)) Q).
Proof.
move=>Hinit Hinv inc ini top step Hdeadlock.
apply: DistributedNetworkValidity.derives_sound.
exact: derives_distributed_total_prime Hinit Hinv inc ini top step Hdeadlock.
Qed.
End DistributedRankingComplement.
