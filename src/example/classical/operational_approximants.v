(* Bounded operational completions, Lemma 4.2. See OPERATIONAL-APPROXIMANTS-NOTES.md. *)
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



Module ClassicalOperationalApproximants.
Import ClassicalLanguage ClassicalOperational CQState.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Section Routes.
Variable c : command.
Variable s : store.
Variable rho : 'FD(Hq).

Lemma route_output_positive r : (0 : {summable store -> 'End(Hq)}) ⊑ opfun c s rho r.
Proof.
apply/lesP=>m; rewrite /opfun.
case E: (eval_route r c (s,(rho : 'End(Hq))))=>[[t x]|] //=.
rewrite /sunit_def; case: eqP=>_ //.
exact: (@terminates_positive c s rho t x (eval_route_sound E) (denf_ge0 rho)).
Qed.

Definition selected_term (p : pred route) r : {summable store -> 'End(Hq)} :=
  if p r then opfun c s rho r else 0.

Lemma selected_term_norm p r : `|selected_term p r| <= `|opfun c s rho r|.
Proof. by rewrite /selected_term; case: (p r)=>//; rewrite normr0. Qed.

Lemma selected_summable p : summable (selected_term p).
Proof.
apply: psum_ubounded_summable; exists `|(rho : 'End(Hq))|=>A.
apply: (le_trans _ ((proj1 (equal_OS_DS c s rho)) (denf_ge0 rho) A)).
by apply: ler_sum=>r _; exact: selected_term_norm.
Qed.

Definition selected_family p := Summable.build (selected_summable p).
Definition selected_sum p : {summable store -> 'End(Hq)} := sum (selected_family p).

Lemma selected_sum_positive p : (0 : {summable store -> 'End(Hq)}) ⊑ selected_sum p.
Proof.
apply: lim_ges_nearF; first exact: summable_cvg.
near=>A; apply: sumv_ge0=>r _.
rewrite /selected_family /= /selected_term; case: (p (val r))=>//.
exact: route_output_positive.
Unshelve. end_near.
Qed.

Lemma selected_sum_l1_bound p : `|selected_sum p| <= `|(rho : 'End(Hq))|.
Proof.
apply: (le_trans (summable_sum_ler_norm (selected_family p))).
apply: etlim_le; first exact: summable_norm_is_cvg.
move=>A; apply: (le_trans _ ((proj1 (equal_OS_DS c s rho)) (denf_ge0 rho) A)).
by apply: ler_sum=>r _; exact: selected_term_norm.
Qed.

Lemma selected_sum_trace_bound p : `|sum (selected_sum p)| <= 1.
Proof.
apply: (le_trans (summable_sum_ler_norm _)).
rewrite -summable_norm_sumE.
apply: (le_trans (selected_sum_l1_bound p)).
by rewrite psd_trfnorm ?is_psdlf //; exact: denf_trlf.
Qed.

Definition selected_state p : state :=
  VDistr.build (f := selected_sum p)
    (fun m => (proj1 (lesP _ _) (selected_sum_positive p)) m)
    (selected_sum_trace_bound p).

Lemma selected_state_summableE p :
  (selected_state p : {summable store -> 'End(Hq)}) = selected_sum p.
Proof. by apply/summableP. Qed.

Lemma selected_stateE p m : selected_state p m =
  sum (fun r => if p r then opfun c s rho r m else 0).
Proof.
change (selected_sum p m = sum (fun r => if p r then opfun c s rho r m else 0)).
rewrite /selected_sum sum_summableE; first exact: summable_cvg.
by apply: eq_sum=>r; rewrite /selected_family /= /selected_term; case: (p r).
Qed.

Lemma selected_mass_bound p : mass (selected_state p) <= \Tr rho.
Proof. rewrite mass_l1; apply: (le_trans (selected_sum_l1_bound p)); by rewrite psd_trfnorm ?is_psdlf. Qed.

Lemma selected_state_countable p : countable (suppf (selected_state p)).
Proof. exact: support_countable. Qed.

Lemma selected_routes_countable p : countable (suppf (selected_family p)).
Proof. exact: summable_countn0. Qed.

Lemma selected_term_mono (p q : pred route) : (forall r, p r -> q r) ->
  forall r, selected_term p r ⊑ selected_term q r.
Proof.
move=>pq r; rewrite /selected_term; case Ep: (p r).
- by rewrite (pq r Ep).
- case: (q r)=>//; exact: route_output_positive.
Qed.

Lemma selected_state_mono (p q : pred route) : (forall r, p r -> q r) -> selected_state p ⊑ selected_state q.
Proof.
move=>pq; rewrite levdEsub.
change (selected_sum p ⊑ selected_sum q).
rewrite /selected_sum /sum.
apply: les_lim_nearF; [exact: summable_cvg | exact: summable_cvg |].
near=>A; apply: lev_sum=>r _.
exact: (selected_term_mono pq (val r)).
Unshelve. end_near.
Qed.

Lemma selected_fullE : (selected_state predT : {summable store -> 'End(Hq)}) = opsum c s rho.
Proof.
have E : selected_sum predT = opsum c s rho.
  by apply: eq_sum=>r.
by apply/summableP=>m; change (selected_sum predT m = opsum c s rho m); rewrite E.
Qed.

Lemma selected_full_denote : selected_state predT = CQKernel.apply (denote c) (point s rho).
Proof.
apply/vdistrP=>m; rewrite CQKernel.apply_point.
have E := congr1 (fun f : {summable store -> 'End(Hq)} => f m) selected_fullE.
rewrite E.
exact: operational_denotational (denf_ge0 rho).
Qed.

Lemma selected_sum_subtype (p : pred route) :
  selected_sum p = sum (fun r : {r : route | p r} => opfun c s rho (val r)).
Proof.
pose h := fun r : {r : route | p r} => val r.
pose h' := fun r : route => if asboolP (p r) is ReflectT H
  then Some (exist (fun r : route => p r) r H) else None.
have hK : pcancel h h'.
  move=>[r Hr]; rewrite /h /h' /=; case: asboolP=>[H|//].
  by congr (Some _); apply/val_inj.
have h'K : ocancel h' h by move=>r; rewrite /h' /h; case: asboolP.
have Hz r : h' r = None -> selected_term p r = 0.
  rewrite /h' /selected_term; case: asboolP=>[H|H] // _.
  by case E: (p r)=>//; exfalso; apply: H; rewrite E.
have Ss : summable (selected_term p \o h)%FUN.
  apply/(proj2 (reindex_summableP hK h'K Hz)); exact: selected_summable.
have E := sum_reindex hK h'K Hz Ss.
change (sum (selected_term p) = sum (fun r : {r : route | p r} => opfun c s rho (val r))).
rewrite E.
apply: eq_sum=>[[r Hr]]; by rewrite /comp /h /selected_term /= Hr.
Qed.

Variable cost : route -> nat.
Definition within n r := (cost r < n.+1)%N.
Definition completion_state n := selected_state (within n).

Lemma completion_state_countable n : countable (suppf (completion_state n)).
Proof. exact: support_countable. Qed.

Lemma completion_routes_countable n : countable (suppf (selected_family (within n))).
Proof. exact: selected_routes_countable. Qed.

Lemma exact_routes_countable n : countable (suppf (selected_family (fun r => cost r == n))).
Proof. exact: selected_routes_countable. Qed.

Lemma completion_state_step n : completion_state n ⊑ completion_state n.+1.
Proof.
apply: selected_state_mono=>r; rewrite /within !ltnS=>Hr.
exact: leq_trans Hr (leqnSn n).
Qed.

Lemma completion_state_chain : nondecreasing_seq completion_state.
Proof. apply/nondecreasing_seqP=>n; exact: completion_state_step. Qed.

Lemma completion_state_cvg :
  ((fun n => (completion_state n : {summable store -> 'End(Hq)})) @ \oo --> opsum c s rho)%classic.
Proof.
have E : (fun n => (completion_state n : {summable store -> 'End(Hq)})) =
    (fun n => sum (fun r : {r : route | (cost r < n.+1)%N} => opfun c s rho (val r))).
  by apply/funext=>n; rewrite /completion_state selected_state_summableE selected_sum_subtype.
rewrite E /opsum.
rewrite (@cvg_shiftS _
  (fun n => sum (fun r : {r : route | (cost r < n)%N} => opfun c s rho (val r)))
  (nbhs (sum (opfun c s rho)))).
exact: (@summable_sigma_nat_cvg route _ _ _ cost (opfun c s rho)
  (@operational_summable c s rho (denf_ge0 rho))).
Qed.

Theorem completion_state_sup : chain_sup completion_state = selected_state predT.
Proof.
have E : (chain_sup completion_state : {summable store -> 'End(Hq)}) =
    (selected_state predT : {summable store -> 'End(Hq)}).
  rewrite selected_fullE /chain_sup vdlimE.
  - exact: (chain_converges completion_state_chain).
  - exact: (cvg_lim (@norm_hausdorff _ _) completion_state_cvg).
apply/vdistrP=>m.
exact (congr1 (fun f : {summable store -> 'End(Hq)} => f m) E).
Qed.

Theorem completion_state_denote :
  chain_sup completion_state = CQKernel.apply (denote c) (point s rho).
Proof. by rewrite completion_state_sup selected_full_denote. Qed.

Theorem completion_state_least (d : state) :
  (forall n, completion_state n ⊑ d) -> selected_state predT ⊑ d.
Proof. rewrite -completion_state_sup; exact: chain_sup_least completion_state_chain. Qed.

End Routes.
End ClassicalOperationalApproximants.
