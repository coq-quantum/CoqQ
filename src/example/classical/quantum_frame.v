(* Order separation and continuous expectations. See EXPECTATION-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules assertion_algebra assertion_series locality operational footprint auxiliary.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


Module CQQuantumFrame.
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQRules ClassicalLanguage.
Import Summable_Reindex.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma sum_commute (I : choiceType) (f : I -> 'SO(Hq)) E :
  summable f -> (forall i, f i :o E = E :o f i) ->
  sum f :o E = E :o sum f.
Proof.
move=>Hsum Hcomm.
have Hcv := norm_bounded_cvg Hsum.
rewrite (cvg_linearP_sum (x := f) (f := fun F => F :o E) (linear_compr_so E) Hcv)
  (cvg_linearP_sum (x := f) (f := fun F => E :o F) (linear_comp_so E) Hcv).
by apply: eq_sum=>i; apply: Hcomm.
Qed.

Lemma slet_commute (K L : kernel) E :
  (forall i j, K i j :o E = E :o K i j) ->
  (forall i j, L i j :o E = E :o L i j) ->
  forall i j, slet K L i j :o E = E :o slet K L i j.
Proof.
move=>HK HL i j; change (sum (fun k => L k j :o K i k) :o E =
  E :o sum (fun k => L k j :o K i k)).
apply: sum_commute; first exact: CQKernel.composition_kernel_summable.
by move=>k; rewrite -comp_soA HK comp_soA HL -comp_soA.
Qed.

Lemma sdlet_commute (T : choiceType) (f : cmem -> T -> cmem)
  (g : cmem -> {vdistr T -> 'SO(Hq)}) E :
  (forall i k, g i k :o E = E :o g i k) ->
  forall i j, sdlet f g i j :o E = E :o sdlet f g i j.
Proof.
move=>Hg i j; change (sum (fun k => sunit_def (f i k) (g i k : 'SO(Hq)) j) :o E =
  E :o sum (fun k => sunit_def (f i k) (g i k : 'SO(Hq)) j)).
apply: sum_commute; first exact: (@filtered_row_summable _ _ _ _ f g i j).
by move=>k; rewrite /sunit_def; case: ifP=>_; rewrite ?comp_so0l ?comp_so0r // Hg.
Qed.

Lemma while_commute b (K : kernel) E :
  (forall i j, K i j :o E = E :o K i j) ->
  forall i j, while_sem b K i j :o E = E :o while_sem b K i j.
Proof.
move=>HK.
have HI n : forall i j, while_sem_iter b K n i j :o E = E :o while_sem_iter b K n i j.
  elim: n=>[|n IH] i j /=.
  - by rewrite abort_semE comp_so0l comp_so0r.
  - case: (esem b i).
    + exact: (@slet_commute K (while_sem_iter b K n) E HK IH i j).
    + by rewrite skip_semE; case: ifP=>_; rewrite ?comp_so1l ?comp_so1r ?comp_so0l ?comp_so0r.
move=>i j.
have Hcv : cvgn (fun n => while_sem_iter b K n i j).
  apply: summableE_is_cvg; exact: while_sem_is_cvg.
rewrite -while_sem_limEE -so_comp_liml // -so_comp_limr //.
by apply: eq_lim=>n; apply: HI.
Qed.

Lemma denote_support_commute c (S : {set mlab}) (E : 'SO(Hq)) :
  quantum_variables c :<=: S ->
  (forall T (F : 'SO_T), T :<=: S -> liftfso F :o E = E :o liftfso F) ->
  forall i j, denote c i j :o E = E :o denote c i j.
Proof.
elim: c=>[| |t x e|t x p|t u x q M|u q phi|u q U|
  c IHc d IHd|b c IHc d IHd|b c IHc] Hsub Hlocal i j /=.
- by rewrite skip_semE; case: ifP=>_; rewrite ?comp_so1l ?comp_so1r ?comp_so0l ?comp_so0r.
- by rewrite abort_semE comp_so0l comp_so0r.
- rewrite /assign_sem /sunit /sunit_vdistr /sunit_def /=.
  by case: ifP=>_; rewrite ?comp_so1l ?comp_so1r ?comp_so0l ?comp_so0r.
- apply: (@sdlet_commute (eval_ctype t)
    (fun (s : cmem) (k : eval_ctype t) => (s.[x <- k])%M)
    (fun s => sdistr Hq (esem (probability_expression p) s)) E _ i j)=>s k.
  by rewrite /sdistr /sdistr_def comp_soZl comp_soZr comp_so1l comp_so1r.
- apply: (@sdlet_commute (eval_qtype t)
    (fun (s : cmem) (k : eval_qtype t) => (s.[x <- k])%M)
    (fun s => measurement_branches q M s) E _ i j)=>s k.
  change (measurement_branches q M s k :o E = E :o measurement_branches q M s k).
  rewrite measurement_branchE; exact: Hlocal Hsub.
- rewrite /initial_sem /sunit /sunit_vdistr /sunit_def /=.
  case: ifP=>_; last by rewrite comp_so0l comp_so0r.
  exact: Hlocal Hsub.
- rewrite /unitary_sem /sunit /sunit_vdistr /sunit_def /=.
  case: ifP=>_; last by rewrite comp_so0l comp_so0r.
  exact: Hlocal Hsub.
- apply: slet_commute.
  + apply: IHc Hlocal; exact: fintype.subset_trans (finset.subsetUl _ _) Hsub.
  + apply: IHd Hlocal; exact: fintype.subset_trans (finset.subsetUr _ _) Hsub.
- case: (esem b i).
  + exact: (IHc (fintype.subset_trans (finset.subsetUl _ _) Hsub) Hlocal i j).
  + exact: (IHd (fintype.subset_trans (finset.subsetUr _ _) Hsub) Hlocal i j).
- apply: while_commute; exact: IHc Hsub Hlocal.
Qed.

Lemma denote_disjoint_commute c S (F : 'SO[msys]_S) :
  [disjoint quantum_variables c & S] -> forall i j,
  denote c i j :o liftfso F = liftfso F :o denote c i j.
Proof.
move=>Hdis; apply: (@denote_support_commute c (quantum_variables c) (liftfso F))=>//.
move=>T G Hsub; apply: liftfso_compC.
exact: fintype.disjointWl Hsub Hdis.
Qed.

Lemma dual_denote_disjoint_commute c S (F : 'SO[msys]_S) :
  [disjoint quantum_variables c & S] -> forall i j,
  (denote c i j)^*o :o liftfso F = liftfso F :o (denote c i j)^*o.
Proof.
move=>Hdis i j.
have E := congr1 (fun E : 'SO(Hq) => E^*o)
  (@denote_disjoint_commute c S F^*o Hdis i j).
by rewrite !dualso_comp !liftfso_dual dualsoK in E; symmetry.
Qed.

Lemma wp_external c S (F : 'SO[msys]_S) (Q R : assertion) :
  [disjoint quantum_variables c & S] ->
  (forall s, (R s : 'End(Hq)) = liftfso F (Q s)) -> forall s,
  (wp (denote c) R s : 'End(Hq)) = liftfso F (wp (denote c) Q s).
Proof.
move=>Hdis HR s; rewrite !wpE.
have Hcv := norm_bounded_cvg (term_summable (denote c) Q s).
rewrite (cvg_linearP_sum (x := fun t => (denote c s t)^*o (Q t))
  (f := liftfso F) (superop_is_linear (liftfso F)) Hcv).
apply: eq_sum=>t; rewrite HR.
have E := congr1 (fun E : 'SO(Hq) => E (Q t))
  (@dual_denote_disjoint_commute c S F Hdis s t).
by rewrite !comp_soE in E.
Qed.

Definition image S (F : 'DQO[msys]_S) (Q : assertion) : assertion :=
  fun s => ObsLf_Build (dqo_obslf (liftfso F) (Q s)).

Lemma imageE S (F : 'DQO[msys]_S) Q s : (image F Q s : 'End(Hq)) = liftfso F (Q s).
Proof. by []. Qed.

Lemma wp_image c S (F : 'DQO[msys]_S) Q :
  [disjoint quantum_variables c & S] -> forall s,
  (wp (denote c) (image F Q) s : 'End(Hq)) = liftfso F (wp (denote c) Q s).
Proof. move=>Hdis; exact: wp_external Hdis (imageE F Q). Qed.

Lemma lift_identity S (F : 'SO[msys]_S) : liftfso F \1 = liftf_lf (F \1).
Proof. by rewrite -{1}(@liftf_lf1 _ msys S) liftfsoEf. Qed.

Lemma subunital_completion S (F : 'DQO[msys]_S) :
  exists G : 'CP[msys]_S, ((F : 'SO[msys]_S) + (G : 'SO[msys]_S)) \1 = \1.
Proof.
have HP : 0%:VF ⊑ \1 - F \1 by rewrite subv_ge0; exact: dqo1_le1.
have [g Hg] := gef0_form HP.
exists (formso g); by rewrite add_soE formsoE comp_lfun1r -Hg addrC subrK.
Qed.

Lemma loss_unital c S (F : 'SO[msys]_S) s :
  [disjoint quantum_variables c & S] -> F \1 = \1 ->
  liftfso F (\1 - (wp (denote c) semantic_top s : 'End(Hq))) =
    \1 - (wp (denote c) semantic_top s : 'End(Hq)).
Proof.
move=>Hdis HF.
have Htop : forall t : cmem, (semantic_top t : 'End(Hq)) = liftfso F (semantic_top t).
  by move=>t; rewrite /semantic_top /= lift_identity HF liftf_lf1.
have HW := @wp_external c S F semantic_top semantic_top Hdis Htop s.
by rewrite linearB /= lift_identity HF liftf_lf1 -HW.
Qed.

Lemma loss_subunital c S (F : 'DQO[msys]_S) s :
  [disjoint quantum_variables c & S] ->
  liftfso F (\1 - (wp (denote c) semantic_top s : 'End(Hq))) ⊑
    \1 - (wp (denote c) semantic_top s : 'End(Hq)).
Proof.
move=>Hdis; have [G HG] := subunital_completion F.
have E := @loss_unital c S ((F : 'SO[msys]_S) + (G : 'SO[msys]_S)) s Hdis HG.
have Emap : liftfso ((F : 'SO[msys]_S) + (G : 'SO[msys]_S)) =
    liftfso F + liftfso G by rewrite /liftfso linearD.
rewrite Emap add_soE in E.
rewrite -{2}E levDl; apply: cp_ge0.
by rewrite subv_ge0; exact: obsf_le1.
Qed.

Lemma wlp_decompose (K : kernel) Q s :
  (wlp K Q s : 'End(Hq)) =
    (\1 - (wp K semantic_top s : 'End(Hq))) + (wp K Q s : 'End(Hq)).
Proof.
change (\1 - (wp K (complement Q) s : 'End(Hq)) =
  (\1 - (wp K semantic_top s : 'End(Hq))) + (wp K Q s : 'End(Hq))).
rewrite (@wp_difference _ _ _ K semantic_top Q (complement Q)) //.
by rewrite opprB addrA addrAC.
Qed.

Lemma pre_image_le total c S (F : 'DQO[msys]_S) Q s :
  [disjoint quantum_variables c & S] ->
  liftfso F (pre total c Q s) ⊑ (pre total c (image F Q) s : 'End(Hq)).
Proof.
move=>Hdis; case: total.
- by change (liftfso F (wp (denote c) Q s) ⊑ (wp (denote c) (image F Q) s : 'End(Hq)));
    rewrite wp_image.
- change (liftfso F (wlp (denote c) Q s) ⊑ (wlp (denote c) (image F Q) s : 'End(Hq))).
  rewrite !wlp_decompose linearD wp_image // levD2r.
  exact: loss_subunital Hdis.
Qed.

Lemma valid_supoper total P c Q S (F : 'DQO[msys]_S) :
  [disjoint quantum_variables c & S] -> CQHoare.valid total P c Q ->
  CQHoare.valid total (image F P) c (image F Q).
Proof.
move=>Hdis /(proj1 (valid_iff _ _ _ _)) V.
apply/(proj2 (valid_iff _ _ _ _))=>s.
apply: (le_trans _ (@pre_image_le total c S F Q s Hdis)).
exact: cp_preserve_order (V s).
Qed.

Lemma derives_supoper total P c Q S (F : 'DQO[msys]_S) :
  [disjoint quantum_variables c & S] -> derives total P c Q ->
  derives total (image F P) c (image F Q).
Proof.
move=>Hdis /derives_sound V; apply: derives_complete.
exact: valid_supoper Hdis V.
Qed.

End CQQuantumFrame.
