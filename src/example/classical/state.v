(* Classical-quantum states: classical.pdf, Definition 3.1 and Lemma 3.3.
   Reuses the trace-norm summability foundation of CoqQ's cqwhile example. *)
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

Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module CQState.
Section States.
Context {I : choiceType} {H : chsType}.

Definition state := {vdistr I -> 'End(H)}.
Definition mass (d : state) : hermitian.C := sum (fun i => \Tr (d i)).

Lemma support_countable (d : state) : countable (suppf d).
Proof. exact: summable_countn0. Qed.

Lemma mass_trace (d : state) : mass d = \Tr (sum d).
Proof. by rewrite /mass summable_linear_sum. Qed.

Lemma mass_norm (d : state) : mass d = `|sum d|.
Proof. by rewrite mass_trace psd_trfnorm // psdlfE vdistr_sum_ge0. Qed.

Lemma mass_l1 (d : state) : mass d = `|d : {summable I -> 'End(H)}|.
Proof.
rewrite summable_norm_sumE /mass; apply: eq_sum=>i.
by rewrite psd_trfnorm // psdlfE vdistr_ge0.
Qed.

Lemma mass_ge0 (d : state) : 0 <= mass d.
Proof. by rewrite mass_norm. Qed.

Lemma mass_le1 (d : state) : mass d <= 1.
Proof. by rewrite mass_norm; apply: vdistr_sum_le1. Qed.

Lemma component_density (d : state) i : d i \is denlf.
Proof.
apply/denlfP; split; first by rewrite psdlfE vdistr_ge0.
apply: (le_trans _ (mass_le1 d)).
by rewrite mass_trace; apply: lef_trlf; apply: vdistr_le_sum.
Qed.

(* Conversely, positivity and the paper's finite trace-sum bound suffice
   to build our summable representation. No support restriction is added. *)
Lemma trace_bounded_summable (f : I -> 'End(H)) :
  (forall i, 0%:VF ⊑ f i) ->
  (forall A, psum (fun i => \Tr (f i)) A <= 1) -> summable f.
Proof.
move=>positive bound; apply: psum_ubounded_summable; exists 1=>A.
rewrite /psum /normf; under eq_bigr do rewrite psd_trfnorm ?psdlfE ?positive //.
exact: bound.
Qed.

Lemma trace_bounded_sum (f : I -> 'End(H))
  (positive : forall i, 0%:VF ⊑ f i)
  (bound : forall A, psum (fun i => \Tr (f i)) A <= 1) :
  `|sum (Summable.build (trace_bounded_summable positive bound))| <= 1.
Proof.
apply: (le_trans (summable_sum_ler_norm _)).
apply: etlim_le; first exact: summable_norm_is_cvg.
move=>A; rewrite /psum /normf /=.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?positive //.
exact: bound.
Qed.

Definition of_trace_bound (f : I -> 'End(H))
  (positive : forall i, 0%:VF ⊑ f i)
  (bound : forall A, psum (fun i => \Tr (f i)) A <= 1) : state :=
  VDistr.build (f := Summable.build (trace_bounded_summable positive bound))
    positive (trace_bounded_sum positive bound).

Definition bottom : state := vdistr_zero.

Lemma bottomE i : bottom i = 0. Proof. by []. Qed.

Lemma bottom_least (d : state) : bottom ⊑ d.
Proof. by apply/levdP=>i; rewrite bottomE; apply: vdistr_ge0. Qed.

Lemma mass_bottom : mass bottom = 0.
Proof. by rewrite mass_trace /bottom /= summable_sum0 linear0. Qed.

Lemma point_positive (i : I) (rho : 'FD(H)) j :
  0%:VF ⊑ sunit_def i (rho : 'End(H)) j.
Proof. rewrite /sunit_def; case: eqP=>_ //; exact: denf_ge0. Qed.

Lemma point_bound (i : I) (rho : 'FD(H)) :
  `|sum (sunit_def i (rho : 'End(H)))| <= 1.
Proof. by rewrite sunit_sum psd_trfnorm ?is_psdlf //; apply: denf_trlf. Qed.

Definition point (i : I) (rho : 'FD(H)) : state :=
  VDistr.build (point_positive i rho) (point_bound i rho).

Lemma pointE (i j : I) (rho : 'FD(H)) :
  point i rho j = if j == i then rho : 'End(H) else 0.
Proof. by []. Qed.

Lemma point_mass (i : I) (rho : 'FD(H)) : mass (point i rho) = \Tr rho.
Proof. by rewrite mass_trace /point /= sunit_sum. Qed.

Definition chain_sup (f : nat -> state) : state :=
  vdlim (FF := eventually_filter) f.

Lemma chain_converges (f : nat -> state) : nondecreasing_seq f ->
  cvgn (f : nat -> {summable I -> 'End(H)}).
Proof. apply: (vdnondecreasing_is_cvgn (@trfnorm_add H)). Qed.

Lemma chain_sup_upper (f : nat -> state) : nondecreasing_seq f ->
  forall n, f n ⊑ chain_sup f.
Proof. exact: (vdnondecreasing_cvg_le (@trfnorm_add H)). Qed.

Lemma chain_sup_least (f : nat -> state) (d : state) :
  nondecreasing_seq f -> (forall n, f n ⊑ d) -> chain_sup f ⊑ d.
Proof.
move=>inc bound; rewrite levdEsub /chain_sup vdlimE.
  exact: chain_converges inc.
apply: lim_les_nearF; first exact: chain_converges.
by apply: nearW=>n; rewrite -levdEsub; apply: bound.
Qed.

Lemma chain_sup_pointwise (f : nat -> state) : nondecreasing_seq f ->
  forall i, chain_sup f i = limn (fun n => f n i).
Proof. by move=>inc i; apply: vdlimEE; apply: chain_converges. Qed.

End States.
End CQState.
