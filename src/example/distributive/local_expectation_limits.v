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

From quantum.example.classical Require Import state expectation expectation_limits kernel_limits.
From quantum.example.distributive Require Import local_iteration_limits.

Module DistributedLocalExpectationLimits.
Import DistributedLanguage DistributedScheduler DistributedSequentialization DistributedLocalActions DistributedLocalCorrespondence DistributedLocalIterations
  DistributedLocalIterationLimits CQAssertion CQPredicate CQExpectation CQExpectationLimits.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma local_iter_apply_cvg s (d : @CQState.state cmem Hq) : residual_wf s ->
  (CQKernel.apply (local_iter k s) d : {summable cmem -> 'End(Hq)}) @[k --> \oo] -->
    (CQKernel.apply (CL.denote (translate_statement s)) d : {summable cmem -> 'End(Hq)}).
Proof.
move=>Hs; apply: CQKernelLimits.apply_cvg_monotone.
- by move=>m i j ij; exact: (@local_iter_mono s i j ij m).
- by move=>k m; exact: (@local_iter_upper k s Hs m).
- move=>m out; apply: summableE_cvg; exact: (@local_iter_cvg s m Hs).
Qed.

Lemma local_iter_expect_cvg s (A : assertion) (d : @CQState.state cmem Hq) : residual_wf s ->
  expect (wp (local_iter k s) A) d @[k --> \oo] -->
    expect (wp (CL.denote (translate_statement s)) A) d.
Proof.
move=>Hs; under eq_cvg do rewrite expect_wp.
rewrite expect_wp; apply: expect_cvg; exact: local_iter_apply_cvg Hs.
Qed.

Lemma local_wp_chain s (A : assertion) : semantic_chain (fun k => wp (local_iter k s) A).
Proof.
move=>k; apply: wp_kernel_mono=>m out.
by move: (@local_iter_chain k s m)=>/levdP/(_ out).
Qed.

Lemma local_wp_sup s (A : assertion) : residual_wf s ->
  semantic_sup (fun k => wp (local_iter k s) A) = wp (CL.denote (translate_statement s)) A.
Proof.
move=>Hs.
have E d : expect (semantic_sup (fun k => wp (local_iter k s) A)) d =
    expect (wp (CL.denote (translate_statement s)) A) d.
  have C1 := @expect_semantic_sup cmem Hq (fun k => wp (local_iter k s) A) d (local_wp_chain s A).
  have C2 := @local_iter_expect_cvg s A d Hs.
  by rewrite -(cvg_lim (@norm_hausdorff _ _) C1) (cvg_lim (@norm_hausdorff _ _) C2).
apply/funext=>m; apply: effect_eq=>rho.
by move: (E (CQState.point m rho)); rewrite !expect_point.
Qed.

Theorem local_wp_cvg s (A : assertion) m : residual_wf s ->
  (wp (local_iter k s) A m : 'End(Hq)) @[k --> \oo] -->
    (wp (CL.denote (translate_statement s)) A m : 'End(Hq)).
Proof.
move=>Hs; rewrite -(@local_wp_sup s A Hs).
exact: semantic_sup_cvg (local_wp_chain s A) m.
Qed.

Theorem local_wp_pairing_cvg s (A : assertion) m (rho : 'End(Hq)) : residual_wf s ->
  \Tr (wp (local_iter k s) A m \o rho) @[k --> \oo] -->
    \Tr (wp (CL.denote (translate_statement s)) A m \o rho).
Proof.
move=>Hs; apply: continuous_cvg; first exact: trlf_continuous.
apply: lfun_comp_cvgl; exact: local_wp_cvg Hs.
Qed.

Theorem local_wp_pairing_least s (A : assertion) m (rho : 'End(Hq)) b :
  residual_wf s -> (forall k, \Tr (wp (local_iter k s) A m \o rho) <= b) ->
  \Tr (wp (CL.denote (translate_statement s)) A m \o rho) <= b.
Proof.
move=>Hs B.
have C := @local_wp_pairing_cvg s A m rho Hs.
move: (climn_le (cvgP _ C) B).
by rewrite (cvg_lim (@norm_hausdorff _ _) C).
Qed.
End DistributedLocalExpectationLimits.
