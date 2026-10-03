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
From quantum.example.distributive Require Import language operational scheduler local_actions instruments interchange progress observables distribution sequentialization guarded_rules weighted local_diamond local_correspondence local_iterations local_iteration_bounds.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.classical Require Import assertion kernel predicate rules primitive bounded_unroll bounded_limits.

Module DistributedLocalIterationLimits.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions
  DistributedInstruments DistributedLocalCorrespondence DistributedLocalIterations DistributedLocalIterationBounds DistributedSequentialization
  DistributedGuardedRules DistributedWeighted ClassicalBoundedUnroll CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma control_wf s : statement_wf s -> forall m i,
  residual_wf (@local_control s m i).1.
Proof.
elim: s=>[|a|s IH t IHt|n g b IH|n g b IH] //=.
- move=>_ m i; case: a i=>[| |t x e|t x p|t q phi|t q U|t u x q M] i;
    by left.
- move=>[Hs Ht] m i; right; apply: append_wf=>//; exact: IH.
- move=>[Hex Hwf] m i; case: pickP=>[j Hj|Hnone]; first by right; apply: Hwf.
  by left.
- move=>[Hex Hwf] m i; case: pickP=>[j Hj|Hnone].
  + right; split; first exact: Hwf.
    by split.
  + by left.
Qed.

Lemma local_iter_upper : forall k s, residual_wf s ->
  kernel_le (local_iter k s) (CL.denote (translate_statement s)).
Proof.
elim=>[|k IH] s Hs.
- case: s Hs=>[|a|s t|n g b|n g b] Hs; first exact: kernel_le_refl;
    exact: abort_le.
- rewrite -(@local_unfold_denote s Hs).
  change (kernel_le (local_unfold (local_iter k) s)
    (local_unfold (fun r => CL.denote (translate_statement r)) s)).
  case: Hs=>[->|Hs].
  + rewrite !local_unfold_finished; exact: (IH Finished (or_introl erefl)).
  + move=>m; apply/levdP=>out; rewrite !local_unfoldE; apply: lev_lim.
    * apply: norm_bounded_cvg; exact: local_unfold_summable.
    * apply: norm_bounded_cvg; exact: local_unfold_summable.
    * move=>A; apply: lev_sum=>i _; apply: leso_comp2l.
      -- exact: (cp_geso0 (@local_cp s m (val i))).
      -- have Hr := @control_wf s Hs m (val i).
         rewrite /residual_row.
         case E: (@local_control s m (val i))=>[r [u|]] /=; last by [].
         rewrite E /= in Hr; by move: (IH r Hr u)=>/levdP/(_ out).
Qed.

Theorem local_iter_limit s : residual_wf s ->
  sem_lim (fun k => local_iter k s) = CL.denote (translate_statement s).
Proof.
move=>Hs.
have Hchain : ClassicalBoundedLimits.kernel_chain (fun k => local_iter k s).
  by move=>m j k jk; exact: (@local_iter_mono s j k jk m).
apply: kernel_le_anti.
- apply: ClassicalBoundedLimits.sem_limit_least; first exact: Hchain.
  move=>k.
  exact: (@local_iter_upper k s Hs).
- case: Hs=>[->|Hs].
  + have E : (fun k => local_iter k Finished) = (fun _ : nat => skip_sem).
      by apply/funext=>k; rewrite local_iter_finished.
    by rewrite E sem_lim_cst; apply: kernel_le_refl.
  + rewrite -ClassicalBoundedLimits.bounded_unroll_limit.
    apply: ClassicalBoundedLimits.sem_limit_least.
      exact: (bounded_unroll_chain (translate_statement s)).
    move=>k.
    have [h Hh] := bounded_local_iter Hs k.
    apply: kernel_le_trans Hh _.
    exact: (@ClassicalBoundedLimits.sem_limit_upper (fun k => local_iter k s) Hchain h).
Qed.

Theorem local_iter_suffix_limit s (K : CL.kernel) : residual_wf s ->
  sem_lim (fun k => slet (local_iter k s) K) = slet (CL.denote (translate_statement s)) K.
Proof.
move=>Hs.
have Hchain : ClassicalBoundedLimits.kernel_chain (fun k => local_iter k s).
  by move=>m j k jk; exact: (@local_iter_mono s j k jk m).
by rewrite (slet_liml K Hchain) (@local_iter_limit s Hs).
Qed.

Theorem local_iter_cvg s m : residual_wf s ->
  (local_iter k s m : {summable cmem -> 'SO(Hq)}) @[k --> \oo] -->
    (CL.denote (translate_statement s) m : {summable cmem -> 'SO(Hq)}).
Proof.
move=>Hs.
have Hchain : ClassicalBoundedLimits.kernel_chain (fun k => local_iter k s).
  by move=>u j k jk; exact: (@local_iter_mono s j k jk u).
have C := @ClassicalBoundedLimits.sem_limit_cvg (fun k => local_iter k s) Hchain m.
by rewrite (@local_iter_limit s Hs) in C.
Qed.

End DistributedLocalIterationLimits.
