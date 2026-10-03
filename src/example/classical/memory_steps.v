(* Classical Table 2 interpreted independently in an arbitrary finite memory.
   See MEMORY-INTERPRETATION-NOTES.md for the construction and replay proof. *)
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
From quantum.example.classical Require Import language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.



From quantum.example.classical Require Import memory_interpretation.
Import CQMemoryInterpretation.

Module ClassicalMemorySteps.
Section Memory.
Variable S : {set mlab}.
Variable L : finType.
Variable H : L -> chsType.
Variable T V : {set L}.
Variable sub : T :<=: V.
Variable U : 'FGI('H[msys]_S, 'H[H]_T).
Local Notation HW := 'H[H]_V.

Inductive memory_step : command -> store -> 'End(HW) ->
    option command -> store -> 'End(HW) -> Type :=
  | MemorySkip s r : memory_step Skip s r None s r
  | MemoryAssign t (x : variable t) e s r :
      memory_step (Assign x e) s r None (s.[x <- eval e s])%M r
  | MemoryRandom t (x : variable t) p s r i :
      memory_step (Random x p) s r None (s.[x <- i])%M (probability_mass p s i *: r)
  | MemoryMeasure t u (x : variable (QType t)) (q : wf_qreg u)
      (qS : mset q :<=: S) (M : mexpr (eval_qtype t) (eval_qtype u)) s r i :
      memory_step (Measure x q M) s r None (s.[x <- i])%M
        (@measurement_channel S L H T V sub U t u q qS (esem M s) i r)
  | MemoryInitialize u (q : wf_qreg u) (qS : mset q :<=: S) phi s r :
      memory_step (Initialize q phi) s r None s (@initialize_channel S L H T V sub U u q qS (esem phi s) r)
  | MemoryUnitary u (q : wf_qreg u) (qS : mset q :<=: S) A s r :
      memory_step (Unitary q A) s r None s (@unitary_channel S L H T V sub U u q qS (esem A s) r)
  | MemorySequenceDone c1 c2 s r s' r' :
      memory_step c1 s r None s' r' ->
      memory_step (Sequence c1 c2) s r (Some c2) s' r'
  | MemorySequenceMore c1 c2 c1' s r s' r' :
      memory_step c1 s r (Some c1') s' r' ->
      memory_step (Sequence c1 c2) s r (Some (Sequence c1' c2)) s' r'
  | MemoryIfTrue b c1 c0 s r : eval b s = true ->
      memory_step (Conditional b c1 c0) s r (Some c1) s r
  | MemoryIfFalse b c1 c0 s r : eval b s = false ->
      memory_step (Conditional b c1 c0) s r (Some c0) s r
  | MemoryWhileTrue b c s r : eval b s = true ->
      memory_step (While b c) s r (Some (Sequence c (While b c))) s r
  | MemoryWhileFalse b c s r : eval b s = false ->
      memory_step (While b c) s r None s r.


Lemma memory_step_positive c s r k s' r' (d : memory_step c s r k s' r') :
  0%:VF ⊑ r -> 0%:VF ⊑ r'.
Proof.
induction d; move=>Hr.
- exact Hr.
- exact Hr.
- by rewrite scalev_ge0 // ge0_mu.
- exact: cp_ge0 Hr.
- exact: cp_ge0 Hr.
- exact: cp_ge0 Hr.
- exact: IHd Hr.
- exact: IHd Hr.
- exact Hr.
- exact Hr.
- exact Hr.
- exact Hr.
Qed.

Lemma memory_step_trace_le c s r k s' r' (d : memory_step c s r k s' r') :
  0%:VF ⊑ r -> \Tr r' <= \Tr r.
Proof.
induction d; move=>Hr.
- exact: lexx.
- exact: lexx.
- rewrite linearZ /=; apply: ler_piMl; last exact: le1_mu.
  by apply: psdlf_trlf; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- exact: IHd Hr.
- exact: IHd Hr.
- exact: lexx.
- exact: lexx.
- exact: lexx.
- exact: lexx.
Qed.

Lemma memory_step_density c s r k s' r' (d : memory_step c s r k s' r') :
  r \is denlf -> r' \is denlf.
Proof.
move=>/denlfP[Hr Htr]; have Hr0 : 0%:VF ⊑ r by rewrite -psdlfE.
apply/denlfP; split.
- by rewrite psdlfE; exact: memory_step_positive d Hr0.
- exact: le_trans (memory_step_trace_le d Hr0) Htr.
Qed.

End Memory.

Lemma source_step_quantum c s r k s' r' (d : ClassicalLanguage.step c s r k s' r') :
  forall S : {set mlab}, quantum_variables c :<=: S ->
    match k with Some c' => is_true (quantum_variables c' :<=: S) | None => True end.
Proof.
induction d; move=>S Hs; try exact I.
- exact: fintype.subset_trans (finset.subsetUr _ _) Hs.
- move: Hs; rewrite /= finset.subUset=>/andP[H1 H2].
  by rewrite /= finset.subUset (IHd S H1) H2.
- exact: fintype.subset_trans (finset.subsetUl _ _) Hs.
- exact: fintype.subset_trans (finset.subsetUr _ _) Hs.
- by rewrite /= finset.setUid.
Qed.


Section Replay.
Variable S : {set mlab}.
Variable L : finType.
Variable H : L -> chsType.
Variable T V : {set L}.
Variable sub : T :<=: V.
Variable U : 'FGI('H[msys]_S, 'H[H]_T).
Local Notation HW := 'H[H]_V.
Local Notation tr := (@transport S L H T V sub U).

Theorem step_replay c s r k s' r' (d : ClassicalLanguage.step c s r k s' r') :
  quantum_variables c :<=: S ->
  { E : 'SO[msys]_S &
    ((r' = liftfso E r) * (forall sigma : 'End(HW),
    @memory_step S L H T V sub U c s sigma k s' (tr E sigma)))%type }.
Proof.
induction d; move=>Hs.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemorySkip.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryAssign.
- exists (probability_mass p s i *: \:1); split.
  + by rewrite linearZ /= liftfso1 !soE.
  + move=>sigma; rewrite linearZ /= transport1 !soE; exact: MemoryRandom.
- exists (liftso Hs (formso (tf2f q q (esem M s i)))); split.
  + by rewrite liftfso2 measurement_branchE.
  + move=>sigma; rewrite -measurement_channelE; exact: MemoryMeasure.
- exists (liftso Hs (initialso (tv2v q (esem phi s)))); split.
  + by rewrite liftfso2.
  + move=>sigma; rewrite -initialize_channelE; exact: MemoryInitialize.
- exists (liftso Hs (formso (tf2f q q (esem U0 s)))); split.
  + by rewrite liftfso2.
  + move=>sigma; rewrite -unitary_channelE; exact: MemoryUnitary.
- have H1 := fintype.subset_trans (finset.subsetUl _ _) Hs.
  have [E [HE HR]] := IHd H1.
  exists E; split=>// sigma; exact: MemorySequenceDone (HR sigma).
- have H1 := fintype.subset_trans (finset.subsetUl _ _) Hs.
  have [E [HE HR]] := IHd H1.
  exists E; split=>// sigma; exact: MemorySequenceMore (HR sigma).
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryIfTrue e.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryIfFalse e.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryWhileTrue e.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryWhileFalse e.
Qed.

End Replay.

End ClassicalMemorySteps.
