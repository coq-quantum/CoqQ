(* Enabled-action structure and finite interchanges for Appendix C.1.
   The full scheduler theorem additionally needs the weighted operational
   diamond and its finite-horizon induction, as recorded in PROOF_GAPS.md. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra notation mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import footprint.
From quantum.example.distributive Require Import language operational scheduler local_actions instruments interchange progress observables distribution sequentialization guarded_rules weighted local_diamond local_correspondence local_iterations.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.classical Require Import assertion kernel predicate rules primitive bounded_unroll bounded_limits.

Module DistributedLocalIterationBounds.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions
  DistributedInstruments DistributedLocalCorrespondence DistributedLocalIterations DistributedSequentialization
  DistributedGuardedRules DistributedWeighted ClassicalBoundedUnroll CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma local_iter_sequence : forall k l s t,
  kernel_le (slet (local_iter k s) (local_iter l t)) (local_iter (k+l+1) (Sequence s t)).
Proof.
elim=>[|k IH] l s t.
- case: s=>[|a|s r|n g b|n g b] /=; try by rewrite slet_abort_left; apply: abort_le.
  rewrite add0n addn1 /= local_unfold_sequence local_unfold_finished slet1l.
  exact: kernel_le_refl.
- rewrite addSn /= local_unfold_compose local_unfold_sequence.
  apply: local_unfold_mono=>r.
  case: r=>[|a|r u|n g b|n g b] /=.
  + rewrite local_iter_finished slet1l.
    apply: local_iter_mono; by rewrite (addnC k l) -addnA leq_addr.
  + exact: IH.
  + exact: IH.
  + exact: IH.
  + exact: IH.
Qed.

Lemma local_iter_append k l s t :
  kernel_le (slet (local_iter k s) (local_iter l t)) (local_iter (k+l+1) (append s t)).
Proof.
case: s=>[|a|s u|n g b|n g b].
- rewrite local_iter_finished slet1l /=; apply: local_iter_mono.
  by rewrite (addnC k l) -addnA leq_addr.
- exact: local_iter_sequence.
- exact: local_iter_sequence.
- exact: local_iter_sequence.
- exact: local_iter_sequence.
Qed.

Lemma kernel_wp_ext (K L : CL.kernel) :
  (forall Q m, wp K Q m = wp L Q m) -> K = L.
Proof.
move=>E; apply/semtypeP=>m; apply/vdistrP=>out; apply/superopP=>rho.
have ET (A : 'FO(Hq)) : \Tr (A \o K m out rho) = \Tr (A \o L m out rho).
  by rewrite -!pairing_at_store E.
apply/eqP; rewrite eq_le; apply/andP; split; apply/lef_trobs=>A.
- by rewrite lftraceC ET lftraceC.
- by rewrite lftraceC -ET lftraceC.
Qed.

Lemma local_unfold_wp F s Q m :
  wp (local_unfold F s) Q m =
  wp (SemType (fun _ : unit => local_maps s m))
    (fun i => if (@local_control s m i).2 is Some u
      then wp (F (@local_control s m i).1) Q u else 0%:VF) tt.
Proof.
apply/val_inj.
change ((wp (slet (SemType (fun _ : unit => local_maps s m))
  (SemType (fun i => residual_row F m (@local_control s m i)))) Q tt : 'End(Hq)) =
  (wp (SemType (fun _ : unit => local_maps s m))
    (fun i => if (@local_control s m i).2 is Some u
      then wp (F (@local_control s m i).1) Q u else 0%:VF) tt : 'End(Hq))).
rewrite wp_sequence.
congr ((wp _ _ tt) : 'End(Hq)); apply/funext=>i.
case E: (@local_control s m i)=>[r [u|]].
- apply/val_inj.
  change (wp_raw (SemType (fun j => residual_row F m (@local_control s m j))) Q i =
    wp_raw (F r) Q u).
  by rewrite /wp_raw /term /= /residual_row E.
- apply/val_inj.
  change (wp_raw (SemType (fun j => residual_row F m (@local_control s m j))) Q i = 0).
  have -> : wp_raw (SemType (fun j => residual_row F m (@local_control s m j))) Q i =
      wp_raw abort_sem Q m.
    by rewrite /wp_raw /term /= /residual_row E.
  exact: raw_abort.
Qed.

Lemma local_unfold_denote s : residual_wf s ->
  local_unfold (fun r => CL.denote (translate_statement r)) s = CL.denote (translate_statement s).
Proof.
move=>[->|Hs]; first by rewrite local_unfold_finished.
apply: kernel_wp_ext=>Q m; rewrite local_unfold_wp.
exact: esym (local_pre Hs m Q).
Qed.

Lemma local_iter_atom a : local_iter 1 (Atomic a) = CL.denote (translate_atom a).
Proof.
rewrite -(@local_unfold_denote (Atomic a) (or_intror I)).
apply/semtypeP=>m; apply/vdistrP=>out.
change (local_unfold (local_iter 0) (Atomic a) m out =
  local_unfold (fun r => CL.denote (translate_statement r)) (Atomic a) m out).
rewrite !local_unfoldE.
apply: eq_sum=>i; case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i;
  by rewrite /residual_row /=.
Qed.

Lemma local_iter_alternative k n (g : 'I_n -> expression bool) b m :
  local_iter k.+1 (Alternative g b) m =
    if [pick i | eval (g i) m] is Some i then local_iter k (b i) m else abort_sem m.
Proof.
apply/vdistrP=>out.
change (local_unfold (local_iter k) (Alternative g b) m out =
  (if [pick i | eval (g i) m] is Some i then local_iter k (b i) m else abort_sem m) out).
rewrite local_unfoldE /= sum_unit.
by case: pickP=>[i Hi|Hnone]; rewrite /residual_row /= comp_so1r.
Qed.

Lemma local_iter_repetition k n (g : 'I_n -> expression bool) b m :
  local_iter k.+1 (Repetition g b) m =
    if [pick i | eval (g i) m] is Some i then local_iter k (Sequence (b i) (Repetition g b)) m
    else skip_sem m.
Proof.
apply/vdistrP=>out.
change (local_unfold (local_iter k) (Repetition g b) m out =
  (if [pick i | eval (g i) m] is Some i then local_iter k (Sequence (b i) (Repetition g b)) m
    else skip_sem m) out).
rewrite local_unfoldE /= sum_unit.
case: pickP=>[i Hi|Hnone]; rewrite /residual_row /= comp_so1r //.
by rewrite local_iter_finished.
Qed.


Lemma slet_row (K L M : CL.kernel) m : K m = L m -> slet K M m = slet L M m.
Proof.
move=>E; apply/vdistrP=>out; change (slet_def K M m out = slet_def L M m out).
by rewrite /slet_def; apply: eq_sum=>i; rewrite E.
Qed.

Lemma finite_local_bound n (b : 'I_n -> statement) (K : 'I_n -> CL.kernel) :
  (forall i, exists k, kernel_le (K i) (local_iter k (b i))) ->
  exists k, forall i, kernel_le (K i) (local_iter k (b i)).
Proof.
move=>H; pose f i := projT1 (cid (H i)).
exists (\sum_(i : 'I_n) f i)%N=>i.
apply: kernel_le_trans (projT2 (cid (H i))) _.
apply: local_iter_mono.
rewrite (bigD1 i) //=; exact: leq_addr.
Qed.

Lemma bounded_chain k bs :
  bounded_unroll k (conditional_chain bs) =
  conditional_chain [seq (bc.1,bounded_unroll k bc.2) | bc <- bs].
Proof. by elim: bs=>[|[g c] bs IH] //=; rewrite IH. Qed.

Lemma bounded_alternative k n (g : 'I_n -> expression bool) b :
  CL.denote (bounded_unroll k (translate_statement (Alternative g b))) =
  CL.denote (conditional_chain [seq (g i,bounded_unroll k (translate_statement (b i))) | i <- enum 'I_n]).
Proof. by rewrite /= bounded_chain -map_comp. Qed.

Lemma bounded_repetition k n (g : 'I_n -> expression bool) b :
  CL.denote (bounded_unroll k (translate_statement (Repetition g b))) =
  CL.denote (CL.unroll (loop_guard g)
    (conditional_chain [seq (g i,bounded_unroll k (translate_statement (b i))) | i <- enum 'I_n]) k).
Proof. by rewrite /= bounded_chain -map_comp. Qed.

Fixpoint loop_budget bound k :=
  if k is j.+1 then (bound + loop_budget bound j + 1).+1 else 0%N.

Lemma local_iter_loop_bound n (g : 'I_n -> expression bool) b
    (d : 'I_n -> CL.command) bound : exclusive g ->
  (forall i, kernel_le (CL.denote (d i)) (local_iter bound (b i))) -> forall k,
  kernel_le (CL.denote (CL.unroll (loop_guard g)
    (conditional_chain [seq (g i,d i) | i <- enum 'I_n]) k))
    (local_iter (loop_budget bound k) (Repetition g b)).
Proof.
move=>Hex Hb; elim=>[|k IH]; first exact: abort_le.
move=>m; rewrite /loop_budget -/loop_budget local_iter_repetition.
case: pickP=>[i Hi|Hnone].
- have Hany : enabled g m by apply/enabledP; exists i.
  rewrite CL.denote_conditional eval_loop_guard Hany.
  have Hi' : i \in enum 'I_n by rewrite mem_enum.
  have E := @conditional_chain_selected n g d (enum 'I_n) m i Hex Hi' Hi.
  change (slet (CL.denote (conditional_chain [seq (g j,d j) | j <- enum 'I_n]))
    (CL.denote (CL.unroll (loop_guard g) (conditional_chain [seq (g j,d j) | j <- enum 'I_n]) k)) m
    ⊑ local_iter (bound + loop_budget bound k + 1) (Sequence (b i) (Repetition g b)) m).
  rewrite (@slet_row _ _ _ m E).
  apply: (le_trans ((slet_mono (Hb i) IH) m)).
  exact: local_iter_sequence.
- have Hany : enabled g m = false.
    apply/negP=>/enabledP[i Hi]; by move: (Hnone i); rewrite Hi.
  by rewrite CL.denote_conditional eval_loop_guard Hany.
Qed.

Theorem bounded_local_iter s : statement_wf s -> forall k,
  exists horizon, kernel_le (CL.denote (bounded_unroll k (translate_statement s))) (local_iter horizon s).
Proof.
elim: s=>[|a|s IHs t IHt|n g b IH|n g b IH].
- by move=>[].
- move=>_ k; exists 1%N; rewrite local_iter_atom.
  case: a=>[| |t x e|t x p|t q phi|t q U|t u x q M]; exact: kernel_le_refl.
- move=>[Hs Ht] k; have [i Hi] := IHs Hs k; have [j Hj] := IHt Ht k.
  exists (i+j+1)%N; change (kernel_le
    (slet (CL.denote (bounded_unroll k (translate_statement s)))
      (CL.denote (bounded_unroll k (translate_statement t))))
    (local_iter (i+j+1) (Sequence s t))); apply: (kernel_le_trans (slet_mono Hi Hj)).
  exact: local_iter_sequence.
- move=>[Hex Hwf] k.
  have [bound Hb] := @finite_local_bound n b
    (fun i => CL.denote (bounded_unroll k (translate_statement (b i))))
    (fun i => IH i (Hwf i) k).
  exists bound.+1; rewrite bounded_alternative=>m; rewrite local_iter_alternative.
  case: pickP=>[i Hi|Hnone].
  + have Hi' : i \in enum 'I_n by rewrite mem_enum.
    rewrite (@conditional_chain_selected n g
      (fun i => bounded_unroll k (translate_statement (b i))) (enum 'I_n) m i Hex Hi' Hi).
    exact: Hb.
  + rewrite conditional_chain_none // all_map; apply/allP=>i _ /=; by rewrite Hnone.
- move=>[Hex Hwf] k.
  have [bound Hb] := @finite_local_bound n b
    (fun i => CL.denote (bounded_unroll k (translate_statement (b i))))
    (fun i => IH i (Hwf i) k).
  exists (loop_budget bound k).
  rewrite bounded_repetition.
  exact: local_iter_loop_bound Hex Hb k.
Qed.

Theorem local_iter_least_output s (K : CL.kernel) m out rho V :
  statement_wf s -> 0%:VF ⊑ rho ->
  (forall k, slet (local_iter k s) K m out rho ⊑ V) ->
  slet (CL.denote (translate_statement s)) K m out rho ⊑ V.
Proof.
move=>Hs Hr HV.
pose f k := slet (CL.denote (bounded_unroll k (translate_statement s))) K.
have Hchain : ClassicalBoundedLimits.kernel_chain f.
  move=>u j k jk; exact: (slet_mono
    (@bounded_unroll_mono (translate_statement s) j k jk) (kernel_le_refl K) u).
have C := @ClassicalBoundedLimits.sem_limit_cvg f Hchain m.
have E : sem_lim f = slet (CL.denote (translate_statement s)) K.
  exact: ClassicalBoundedLimits.bounded_unroll_suffix_limit.
rewrite E in C.
have Cp : f k m out @[k --> \oo] -->
    slet (CL.denote (translate_statement s)) K m out.
  apply: summableE_cvg.
  exact: C.
have Cr : f k m out rho @[k --> \oo] -->
    slet (CL.denote (translate_statement s)) K m out rho.
  exact: so_cvgl Cp.
have B k : f k m out rho ⊑ V.
  have [h Hh] := bounded_local_iter Hs k.
  apply: (le_trans _ (HV h)); apply: leso_preserve_order=>//.
  by move: ((slet_mono Hh (kernel_le_refl K)) m)=>/levdP/(_ out).
have L := limn_lev (cvgP _ Cr) B.
by rewrite (cvg_lim (@norm_hausdorff _ _) Cr) in L.
Qed.

End DistributedLocalIterationBounds.
