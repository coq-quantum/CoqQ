(* Ordered active controls after a rendezvous. *)
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
From quantum.example.distributive Require Import language operational sequentialization guarded_rules residual_semantics serial_scheduler.
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



Module DistributedActivePairs.
Import DistributedLanguage DistributedOperational DistributedSequentialization
  DistributedResidualSemantics DistributedSerialScheduler.

Lemma active_program_filter n (pc : 'I_n -> control) indices tail (keep : pred 'I_n) :
  (forall i, i \in indices -> ~~ keep i -> control_command (pc i) = CL.Skip) ->
  CL.denote (active_program indices pc tail) =
  CL.denote (active_program (seq.filter keep indices) pc tail).
Proof.
elim: indices=>[|i indices IH] //= H.
case Ei: (keep i).
- change (slet (CL.denote (control_command (pc i)))
    (CL.denote (active_program indices pc tail)) =
    slet (CL.denote (control_command (pc i)))
    (CL.denote (active_program (seq.filter keep indices) pc tail))).
  congr slet; apply: IH=>j Hj; apply: H; by rewrite inE Hj orbT.
- have Hi : control_command (pc i) = CL.Skip.
    apply: H; by rewrite ?inE ?eqxx ?Ei.
  change (CL.denote (CL.Sequence (control_command (pc i))
    (active_program indices pc tail)) =
    CL.denote (active_program (seq.filter keep indices) pc tail)).
  rewrite Hi CL.denote_skip_left; apply: IH=>j Hj; apply: H.
  by rewrite inE Hj orbT.
Qed.

Lemma filter_pair_order (T : eqType) (indices : seq T) i k :
  uniq indices -> i \in indices -> k \in indices ->
  (index i indices < index k indices)%N ->
  seq.filter (pred2 i k) indices = [::i;k].
Proof.
elim: indices=>[|j indices IH] //= /andP[Hj HU] Hi Hk Ho.
have Hik : i != k by apply/negP=>/eqP E; subst k; move: Ho; rewrite ltnn.
case Eji: (j == i).
- move/eqP: Eji=>E; subst j.
  have Hki : k != i by rewrite eq_sym.
  have Hk' : k \in indices by move: Hk; rewrite inE (negbTE Hki).
  change (i :: seq.filter (pred2 i k) indices = [::i;k]).
  have EF : seq.filter (pred2 i k) indices = seq.filter (pred1 k) indices.
    apply: eq_in_filter=>j Hmem; rewrite /pred2 /pred1.
    have Hji : j != i.
      apply/negP=>/eqP E; subst j; by move: Hj; rewrite Hmem.
    by rewrite /xpred2 /xpred1 /= (negbTE Hji).
  by rewrite EF (filter_pred1_uniq HU Hk').
- case Ejk: (j == k).
  + move/eqP: Ejk=>E; subst j.
    by move: Ho; rewrite /= eqxx.
  + have Hi' : i \in indices by move: Hi; rewrite inE eq_sym Eji.
    have Hk' : k \in indices by move: Hk; rewrite inE eq_sym Ejk.
    have Ho' : (index i indices < index k indices)%N.
      by move: Ho; rewrite /= Eji Ejk ltnS.
    exact: IH HU Hi' Hk' Ho'.
Qed.

Theorem residual_active_pair n (p : 'I_n -> process) pc (i k : 'I_n) s t :
  ready pc -> (i < k)%N ->
  CL.denote (residual_command p
    (replace (replace pc i (Executing s)) k (Executing t))) =
  CL.denote (CL.Sequence (translate_statement s)
    (CL.Sequence (translate_statement t) (network_tail p))).
Proof.
move=>Hready Hik.
have Hneq : i != k by apply/eqP=>E; subst k; move: Hik; rewrite ltnn.
have HF j : j \in enum 'I_n -> ~~ pred2 i k j ->
    control_command (replace (replace pc i (Executing s)) k (Executing t) j) = CL.Skip.
  move=>_; rewrite /pred2 /= negb_or=>/andP[Hji Hjk].
  rewrite (replace_other _ _ Hjk) (replace_other _ _ Hji).
  case: (Hready j)=>->; by [].
rewrite /residual_command (@active_program_filter n _ _ _ (pred2 i k) HF).
have Ho : (index i (enum 'I_n) < index k (enum 'I_n))%N.
  by rewrite !index_enum_ord.
have Hi : i \in enum 'I_n by rewrite mem_enum.
have Hk : k \in enum 'I_n by rewrite mem_enum.
rewrite (filter_pair_order (enum_uniq _) Hi Hk Ho).
change (CL.denote (CL.Sequence
  (control_command (replace (replace pc i (Executing s)) k (Executing t) i))
  (CL.Sequence
    (control_command (replace (replace pc i (Executing s)) k (Executing t) k))
    (network_tail p))) =
  CL.denote (CL.Sequence (translate_statement s)
    (CL.Sequence (translate_statement t) (network_tail p)))).
by rewrite (replace_other _ _ Hneq) !replace_same.
Qed.

End DistributedActivePairs.
