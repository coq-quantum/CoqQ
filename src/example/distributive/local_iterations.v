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
From quantum Require Import mcextra mxpred extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import footprint.
From quantum.example.distributive Require Import language operational scheduler local_actions instruments interchange progress observables distribution sequentialization guarded_rules weighted local_diamond local_correspondence.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.classical Require Import assertion kernel predicate rules primitive bounded_unroll.

Module DistributedLocalIterations.
Import DistributedLanguage DistributedOperational DistributedScheduler DistributedLocalActions
  DistributedInstruments DistributedLocalCorrespondence DistributedSequentialization
  DistributedGuardedRules DistributedWeighted ClassicalBoundedUnroll CQAssertion CQPredicate.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition residual_row (F : statement -> CL.kernel) m (c : statement * option cmem) :=
  if c.2 is Some u then F c.1 u else abort_sem m.

Definition local_unfold (F : statement -> CL.kernel) (s : statement) : CL.kernel :=
  SemType (fun m => slet (SemType (fun _ : unit => local_maps s m))
    (SemType (fun i => residual_row F m (@local_control s m i))) tt).

Fixpoint local_iter k s : CL.kernel :=
  match k with
  | O => if s is Finished then skip_sem else abort_sem
  | S n => local_unfold (local_iter n) s
  end.

Lemma local_unfoldE F s m out : local_unfold F s m out =
  sum (fun i => residual_row F m (@local_control s m i) out :o @local_map s m i).
Proof.
rewrite /local_unfold /= /slet_def; by apply: eq_sum=>i; rewrite local_mapsE.
Qed.

Lemma local_unfold_summable F s m out :
  summable (fun i => residual_row F m (@local_control s m i) out :o @local_map s m i).
Proof.
have E : (fun i => residual_row F m (@local_control s m i) out :o @local_map s m i) =
  (fun i => (SemType (fun i => residual_row F m (@local_control s m i))) i out :o
    (SemType (fun _ : unit => local_maps s m)) tt i).
  by apply/funext=>i; rewrite /= local_mapsE.
rewrite E; exact: slet_in_out_summable.
Qed.

Lemma local_unfold_mono F G : (forall r, kernel_le (F r) (G r)) ->
  forall s, kernel_le (local_unfold F s) (local_unfold G s).
Proof.
move=>FG s m; apply/levdP=>out; rewrite !local_unfoldE; apply: lev_lim.
- apply: norm_bounded_cvg; exact: local_unfold_summable.
- apply: norm_bounded_cvg; exact: local_unfold_summable.
- move=>A; apply: lev_sum=>i _.
  apply: leso_comp2l.
  + exact: (cp_geso0 (@local_cp s m (val i))).
  + rewrite /residual_row; case: (@local_control s m (val i))=>[r [u|]] /=.
    * by move: (FG r u)=>/levdP/(_ out).
    * by [].
Qed.

Lemma local_unfold_finished F : local_unfold F Finished = F Finished.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out; rewrite local_unfoldE /= sum_unit /residual_row /=.
by rewrite comp_so1r.
Qed.

Definition residual_output (F : statement -> CL.kernel) (c : local_configuration) out :=
  if c.1.2 is Some u then F c.1.1 u out c.2 else 0.

Lemma local_unfold_weighted F s m rho out : rho \is den1lf ->
  local_unfold F s m out rho =
  weighted_sum (local_successor s m rho) (fun c => residual_output F c out).
Proof.
move=>Hr; rewrite local_unfoldE sum_summable_soE.
- apply: norm_bounded_cvg; exact: local_unfold_summable.
- rewrite (@local_realization s m rho Hr) /weighted_sum /local_family /=.
  apply: eq_sum=>i; rewrite comp_soE /residual_row /residual_output /local_config /=.
  case: (@local_control s m i)=>[r [u|]] /=.
  + by rewrite -linearZ (weighted_normalized_output (@local_cp s m i) Hr).
  + by rewrite abort_semE soE scaler0.
Qed.

Lemma local_iter_finished k : local_iter k Finished = skip_sem.
Proof. by elim: k=>[|k IH] //=; rewrite local_unfold_finished IH. Qed.

Lemma local_iter_chain k s : kernel_le (local_iter k s) (local_iter k.+1 s).
Proof.
elim: k s=>[|k IH] s.
- case: s=>[|a|s t|n g b|n g b] /=.
  + by rewrite local_unfold_finished.
  + exact: abort_le.
  + exact: abort_le.
  + exact: abort_le.
  + exact: abort_le.
- exact: local_unfold_mono IH s.
Qed.

Lemma local_iter_mono s j k : (j <= k)%N -> kernel_le (local_iter j s) (local_iter k s).
Proof.
move=>jk; have E : k = (j + (k-j))%N by rewrite subnKC.
rewrite E; elim: (k-j)%N=>[|d IH]; first by rewrite addn0; apply: kernel_le_refl.
rewrite addnS; exact: kernel_le_trans IH (local_iter_chain (j+d) s).
Qed.

Lemma slet_abort_left (K : CL.kernel) : slet abort_sem K = abort_sem.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out; rewrite abort_semE /= /slet_def.
rewrite (eq_sum (g := fun _ => 0)) ?summable_sum_cst0 // =>i.
by rewrite abort_semE comp_so0r.
Qed.

Lemma local_unfold_sequence F s t :
  local_unfold F (Sequence s t) = local_unfold (fun r => F (append r t)) s.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out; rewrite !local_unfoldE /=.
apply: eq_sum=>i; rewrite /residual_row.
by case: (@local_control s m i)=>[r [u|]].
Qed.

Lemma local_unfold_compose F (K : CL.kernel) s :
  slet (local_unfold F s) K = local_unfold (fun r => slet (F r) K) s.
Proof.
apply/semtypeP=>m; apply/vdistrP=>out.
pose A := SemType (fun _ : unit => local_maps s m).
pose B := SemType (fun i => residual_row F m (@local_control s m i)).
change (slet (slet A B) K tt out =
  slet A (SemType (fun i => residual_row (fun r => slet (F r) K) m (@local_control s m i))) tt out).
rewrite sletA; congr ((slet A _) tt out).
apply/semtypeP=>i; apply/vdistrP=>out'; rewrite /B /= /slet_def /residual_row.
case E: (@local_control s m i)=>[r [u|]] /=; rewrite E /=.
- by [].
- change (slet abort_sem K m out' = abort_sem m out'); by rewrite slet_abort_left.
Qed.

End DistributedLocalIterations.
