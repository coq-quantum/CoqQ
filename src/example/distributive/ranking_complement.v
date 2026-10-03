(* Derived Rep-T′ and Dist-T′ rules; see RANKING-COMPLEMENT-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion language kernel
  operational kernel_expectation expectation expectation_limits kernel_limits
  predicate hoare rules ranking_complement.
From quantum.example.distributive Require Import language sequentialization
  guarded_rules network_rules operational_hoare local_hoare.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.

Module DistributedRankingComplement.
Import DistributedLanguage DistributedSequentialization CQAssertion CQPredicate
  CQExpectationLimits CQRankingComplement.
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
    (forall k i, CQRules.derives false (mask (eval (g i)) (f k.+1))
      (translate_statement (b i)) (f k)).
Proof.
rewrite repetition_ranking_iff_partial; split; move=>[f [inc [ini [top step]]]];
  exists f; split=>//; split=>//; split=>// k i.
- exact: CQRules.derives_complete (step k i).
- exact: CQRules.derives_sound (step k i).
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
  GR.derives true P (Repetition g b) (mask (predC (GR.enabled g)) P).
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
  DistributedLocalHoare.valid true P (Repetition g b) (mask (predC (GR.enabled g)) P).
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
      CQRules.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k)) bs).
Proof.
rewrite list_ranking_iff_partial; split; move=>[f [inc [ini [top step]]]];
  exists f; split=>//; split=>//; split=>// k;
  apply: (@List.Forall_impl _ _ _ _ _ (step k))=>bc Hb.
- exact: CQRules.derives_complete Hb.
- exact: CQRules.derives_sound Hb.
Qed.

Theorem network_ranking_iff_derivable P n (p : 'I_n -> process) :
  inhabited (NR.network_ranking P p) <->
  exists f : nat -> assertion,
    semantic_chain f /\ semantic_le P (complement (f 0%N)) /\
    semantic_sup f = semantic_top /\
    (forall k, List.Forall (fun bc : expression bool * CL.command =>
      CQRules.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k))
      (rendezvous_commands p)).
Proof. exact: list_ranking_iff_derivable. Qed.

Theorem derives_distributed_total_prime P Q n (p : 'I_n -> process)
    (f : nat -> assertion) :
  CQRules.derives true P (NR.initialization_command p) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQRules.derives true (mask (eval bc.1) Q) bc.2 Q) (rendezvous_commands p) ->
  semantic_chain f -> semantic_le Q (complement (f 0%N)) ->
  semantic_sup f = semantic_top ->
  (forall k, List.Forall (fun bc : expression bool * CL.command =>
    CQRules.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k))
    (rendezvous_commands p)) ->
  semantic_le (mask (NR.blocked p) Q) (mask (DistributedLanguage.term p) semantic_top) ->
  NR.derives true P p (mask (DistributedLanguage.term p) Q).
Proof.
move=>Hinit Hinv inc ini top step Hdeadlock.
apply: NR.DDistributedTotal=>//.
apply: list_ranking_of_partial inc ini top _=>k.
apply: (@List.Forall_impl _ _ _ _ _ (step k))=>bc Hb.
exact: CQRules.derives_sound Hb.
Qed.

Theorem distributed_total_prime P Q (S : program) (f : nat -> assertion) :
  CQRules.derives true P (NR.initialization_command (processes S)) Q ->
  List.Forall (fun bc : expression bool * CL.command =>
    CQRules.derives true (mask (eval bc.1) Q) bc.2 Q)
    (rendezvous_commands (processes S)) ->
  semantic_chain f -> semantic_le Q (complement (f 0%N)) ->
  semantic_sup f = semantic_top ->
  (forall k, List.Forall (fun bc : expression bool * CL.command =>
    CQRules.derives false (mask (eval bc.1) (f k.+1)) bc.2 (f k))
    (rendezvous_commands (processes S))) ->
  semantic_le (mask (NR.blocked (processes S)) Q)
    (mask (DistributedLanguage.term (processes S)) semantic_top) ->
  DistributedHoare.valid true P S (mask (DistributedLanguage.term (processes S)) Q).
Proof.
move=>Hinit Hinv inc ini top step Hdeadlock.
apply: DistributedHoare.derives_sound.
exact: derives_distributed_total_prime Hinit Hinv inc ini top step Hdeadlock.
Qed.

End DistributedRankingComplement.
