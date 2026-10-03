(* Literal Table 6 Shor wrapper and partial factor-output safety.
   The mathematical argument is recorded in CASE-STUDIES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language
  predicate hoare rules primitive auxiliary shor_arithmetic order_finding.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Module ClassicalShorProgram.
Import ClassicalLanguage CQAssertion CQPredicate CQRules ClassicalShorArithmetic.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.

Section Uniform.
Variable N : nat.
Hypothesis modulus_nontrivial : (1 < N)%N.

Definition uniform_weights : {summable 'I_N.-1 -> C} :=
  Summable.build (fin_dom_summable (fun _ : 'I_N.-1 => ((N.-1%:R : C)^-1)%R)).
Definition uniform_mass : nat -> C :=
  sdlet_def (fun i : 'I_N.-1 => (val i).+1) uniform_weights.

Lemma uniform_mass_positive x : 0 <= uniform_mass x.
Proof.
rewrite /uniform_mass /sdlet_def fin_dom_sum.
apply: sumr_ge0=>i _; rewrite /sunit_def /uniform_weights /=.
by case: eqP=>// _; rewrite invr_ge0 ler0n.
Qed.

Lemma uniform_mass_sum : sum uniform_mass = 1.
Proof.
rewrite /uniform_mass sdlet_sum /uniform_weights fin_dom_sum /=.
rewrite sumr_const card_ord -[X in X = 1]mulr_natr mulVf // pnatr_eq0.
by case: N modulus_nontrivial=>[|[|n]].
Qed.

Lemma uniform_mass_bound : `|sum uniform_mass| <= 1.
Proof. by rewrite uniform_mass_sum normr1. Qed.

Definition uniform_distribution : Distr nat :=
  VDistr.build (f := Summable.build
    (sdlet_summable_subproof (fun i : 'I_N.-1 => (val i).+1) uniform_weights))
    uniform_mass_positive uniform_mass_bound.

Definition uniform_probability : probability CNat :=
  @Probability CNat (EConst uniform_distribution) (fun _ => uniform_mass_sum).

Lemma uniform_mass_outside x : ~~ (0 < x < N)%N -> uniform_mass x = 0.
Proof.
move=>Hx; rewrite /uniform_mass /sdlet_def fin_dom_sum.
apply: big1=>i _; rewrite /sunit_def.
case: eqP=>// Ex; move: Hx; rewrite Ex /=.
have HN : N = N.-1.+1 by rewrite prednK //; exact: ltnW modulus_nontrivial.
by rewrite {2}HN ltnS (valP i).
Qed.

Lemma uniform_mass_inside x : (0 < x < N)%N ->
  uniform_mass x = ((N.-1%:R : C)^-1)%R.
Proof.
move=>/andP[Hx HxN].
have HN : N = N.-1.+1 by rewrite prednK //; exact: ltnW modulus_nontrivial.
have Hx1 : x = x.-1.+1 by rewrite prednK.
have Hk : (x.-1 < N.-1)%N.
  by rewrite -ltnS -Hx1 -HN.
pose k : 'I_N.-1 := Ordinal Hk.
rewrite /uniform_mass /sdlet_def fin_dom_sum (bigD1 k) //=.
rewrite /sunit_def -Hx1 eqxx /uniform_weights /=.
suff -> : \sum_(i : 'I_N.-1 | i != k)
  (if x == (val i).+1 then ((N.-1%:R : C)^-1)%R else 0) = 0 by rewrite addr0.
apply: big1=>i Hik; case: eqP=>// E.
have Eik : i = k by apply/val_inj; apply: succn_inj; rewrite -E -Hx1.
by move: Hik; rewrite Eik eqxx.
Qed.

Lemma uniform_probabilityE s x : probability_mass uniform_probability s x =
  if (0 < x < N)%N then ((N.-1%:R : C)^-1)%R else 0.
Proof.
change (uniform_mass x = if (0 < x < N)%N then ((N.-1%:R : C)^-1)%R else 0).
case E: (0 < x < N)%N.
- exact: uniform_mass_inside E.
- apply: uniform_mass_outside; by rewrite E.
Qed.


Definition direct_ordinal_weights : {summable 'I_N.-1 -> C} :=
  Summable.build (fin_dom_summable (fun i : 'I_N.-1 =>
    if (1 < gcdn (val i).+1 N)%N then ((N.-1%:R : C)^-1)%R else 0)).
Definition direct_mass : nat -> C :=
  sdlet_def (fun i : 'I_N.-1 => (val i).+1) direct_ordinal_weights.
Definition direct_probability : C := sum direct_ordinal_weights.

Lemma direct_massE a : direct_mass a =
  if (1 < gcdn a N)%N then uniform_mass a else 0.
Proof.
rewrite /direct_mass /uniform_mass /sdlet_def !fin_dom_sum.
case H: (1 < gcdn a N)%N.
- apply: eq_bigr=>i _; rewrite /sunit_def /direct_ordinal_weights /uniform_weights /=.
  by case: eqP=>// E; rewrite -E H.
- apply: big1=>i _; rewrite /sunit_def /direct_ordinal_weights /=.
  by case: eqP=>// E; rewrite -E H.
Qed.

Lemma direct_mass_sum : sum direct_mass = direct_probability.
Proof. by rewrite /direct_mass sdlet_sum. Qed.

Lemma direct_probability_ge0 : 0 <= direct_probability.
Proof.
rewrite /direct_probability /direct_ordinal_weights fin_dom_sum /=.
apply: sumr_ge0=>i _; case: ifP=>// _; by rewrite invr_ge0 ler0n.
Qed.

Lemma direct_probability_le1 : direct_probability <= 1.
Proof.
rewrite -(uniform_mass_sum) /uniform_mass sdlet_sum.
rewrite /direct_probability /direct_ordinal_weights /uniform_weights !fin_dom_sum /=.
apply: ler_sum=>i _; case: ifP=>// _; by rewrite invr_ge0 ler0n.
Qed.

Lemma direct_probability_sum : direct_probability =
  sum (fun a : nat => if (1 < gcdn a N)%N then uniform_mass a else 0).
Proof. rewrite -direct_mass_sum; apply: eq_sum=>a; exact: direct_massE. Qed.

End Uniform.

Section Wrapper.
Variables (N : nat) (modulus_nontrivial : (1 < N)%N).
Variables (x y y1 y2 z : variable CNat) (result : variable (COption CNat)).

Definition factor_post : cmem -> 'FO(Hq) :=
  mask (fun s => nontrivial_factor N (s.[y])%M) semantic_top.
Definition sampled_range : cmem -> 'FO(Hq) :=
  mask (fun s => (0 < (s.[x])%M < N)%N) semantic_top.
Definition gcd_expression : expression nat :=
  EApp (EConst (fun a => gcdn a N)) (EVar x).
Definition gcd_guard : bool_expr :=
  EApp (EConst (fun d => (1 < d)%N)) gcd_expression.
Definition factor_guard (a : variable CNat) : bool_expr :=
  EApp (EConst (nontrivial_factor N)) (EVar a).
Definition factor_checks : command :=
  Conditional (factor_guard y1) (Assign y (EVar y1))
    (Conditional (factor_guard y2) (Assign y (EVar y2)) Abort).
Definition half_power : expression nat :=
  EApp (EApp (EConst (fun a b : nat => (a ^ (b %/ 2))%N)) (EVar x)) (EVar z).
Definition root_guard : bool_expr :=
  EApp (EApp (EConst (fun b a : nat => ~~ odd b && ((a %% N)%N != N.-1)))
    (EVar z)) half_power.
Definition candidate_assignments : command :=
  Sequence (Assign y1 (EApp (EConst (fun a : nat => gcdn (a - 1)%N N)) half_power))
    (Assign y2 (EApp (EConst (fun a : nat => gcdn (a + 1)%N N)) half_power)).
Definition order_stage (OF : command) : command :=
  Sequence OF
    (Conditional (EApp (EConst (@isSome nat)) (EVar result))
      (Sequence (Assign z (EApp (EConst (odflt 0%N)) (EVar result)))
        (Conditional root_guard candidate_assignments Abort)) Abort).
Definition shor_with (OF : command) : command :=
  Sequence (Random x (uniform_probability modulus_nontrivial))
    (Conditional gcd_guard (Assign y gcd_expression)
      (Sequence (order_stage OF) factor_checks)).

Lemma valid_factor_assign total (p : pred cmem) e :
  (forall s, p s -> nontrivial_factor N (eval e s)) ->
  CQHoare.valid total (mask p semantic_top) (Assign y e) factor_post.
Proof.
move=>H; apply/(proj2 (valid_iff _ _ _ _))=>s.
rewrite /pre CQPrimitive.assign_pre /factor_post /mask get_set_eq.
case E: (p s)=>/=; last exact: obsf_ge0.
by rewrite (H s E).
Qed.

Lemma valid_candidate a c :
  CQHoare.valid false semantic_top c factor_post ->
  CQHoare.valid false semantic_top
    (Conditional (factor_guard a) (Assign y (EVar a)) c) factor_post.
Proof.
move=>V; apply: valid_conditional.
- apply: valid_factor_assign=>s; by [].
- apply: (@CQHoare.valid_consequence false semantic_top factor_post
    (mask (predC (esem (factor_guard a))) semantic_top) factor_post c).
  + exact: semantic_le_top.
  + exact: semantic_le_refl.
  + exact: V.
Qed.

Lemma valid_factor_checks : CQHoare.valid false semantic_top factor_checks factor_post.
Proof.
apply: valid_candidate; apply: valid_candidate; exact: CQHoare.valid_abort_partial.
Qed.

Lemma uniform_sampling_range :
  CQHoare.valid false semantic_top
    (Random x (uniform_probability modulus_nontrivial)) sampled_range.
Proof.
apply/(proj2 (valid_iff _ _ _ _)).
have E : pre false (Random x (uniform_probability modulus_nontrivial)) sampled_range =
    pre false (Random x (uniform_probability modulus_nontrivial)) semantic_top.
  apply/funext=>s; apply/val_inj.
  change ((pre false (Random x (uniform_probability modulus_nontrivial)) sampled_range s : 'End(Hq)) =
    (pre false (Random x (uniform_probability modulus_nontrivial)) semantic_top s : 'End(Hq))).
  rewrite /pre !CQPrimitive.random_pre; apply: eq_sum=>a.
  rewrite /sampled_range /mask get_set_eq.
  case Ea: (0 < a < N)%N=>//.
  by rewrite uniform_probabilityE Ea !scale0r.
rewrite E /pre /xp /= wlp_top; exact: semantic_le_refl.
Qed.

Lemma immediate_gcd_factor a :
  (0 < a < N)%N -> (1 < gcdn a N)%N -> nontrivial_factor N (gcdn a N).
Proof.
move=>/andP[Ha HaN] Hg.
have Hga : (gcdn a N <= a)%N := dvdn_leq Ha (dvdn_gcdl a N).
by rewrite /nontrivial_factor Hg (leq_ltn_trans Hga HaN) dvdn_gcdr.
Qed.

Theorem shor_with_partial_safe OF :
  CQHoare.valid false semantic_top (shor_with OF) factor_post.
Proof.
apply: (@CQHoare.valid_sequence false _ sampled_range).
- exact: uniform_sampling_range.
- apply: valid_conditional.
  + apply/(proj2 (valid_iff _ _ _ _))=>s.
    rewrite /pre CQPrimitive.assign_pre /sampled_range /factor_post /mask get_set_eq.
    case Eg: (esem gcd_guard s)=>/=; last exact: obsf_ge0.
    case Ex: (0 < (s.[x])%M < N)%N=>/=; last exact: obsf_ge0.
    have Hg : (1 < gcdn (s.[x])%M N)%N := Eg.
    by rewrite /gcd_expression /eval /= (immediate_gcd_factor Ex Hg).
  + apply: (@CQHoare.valid_consequence false semantic_top factor_post
      (mask (predC (esem gcd_guard)) sampled_range) factor_post).
    * exact: semantic_le_top.
    * exact: semantic_le_refl.
    * apply: (@CQHoare.valid_sequence false _ semantic_top).
      -- exact: CQAuxiliary.valid_top.
      -- exact: valid_factor_checks.
Qed.

Theorem derives_shor_with OF : derives false semantic_top (shor_with OF) factor_post.
Proof. apply: derives_complete; exact: shor_with_partial_safe. Qed.


Definition direct_guard (s : cmem) :=
  (0 < (s.[x])%M < N)%N && (1 < gcdn (s.[x])%M N)%N.
Definition direct_assertion : cmem -> 'FO(Hq) := mask direct_guard semantic_top.
Definition direct_pre : cmem -> 'FO(Hq) :=
  pre true (Random x (uniform_probability modulus_nontrivial)) direct_assertion.

Lemma direct_preE s : (direct_pre s : 'End(Hq)) =
  direct_probability N *: (\1 : 'End(Hq)).
Proof.
rewrite /direct_pre /pre CQPrimitive.random_pre.
have E : (fun a => probability_mass (uniform_probability modulus_nontrivial) s a *:
    (direct_assertion (s.[x <- a])%M : 'End(Hq))) =
    (fun a => direct_mass N a *: (\1 : 'End(Hq))).
  apply/funext=>a.
  rewrite /direct_assertion /mask /direct_guard get_set_eq direct_massE.
  change ((@uniform_mass N a) *:
    ((if (0 < a < N)%N && (1 < gcdn a N)%N then semantic_top s
      else (0%:VF : 'FO(Hq))) : 'End(Hq)) =
    (if (1 < gcdn a N)%N then uniform_mass N a else 0) *: (\1 : 'End(Hq))).
  case Ha: (0 < a < N)%N=>/=.
  - by case: ifP=>_ /=; rewrite ?scaler0 ?scale0r.
  - rewrite (@uniform_mass_outside N modulus_nontrivial a) ?Ha //.
    by case: ifP=>_ /=; rewrite !scale0r.
rewrite E -direct_mass_sum.
symmetry; apply: (cvg_linearP_sum (x := direct_mass N)
  (f := fun a : C => a *: (\1 : 'End(Hq)))).
- by move=>a b c; rewrite scalerDl scalerA.
- exact: (summable_cvg (f := Summable.build
    (sdlet_summable_subproof (fun i : 'I_N.-1 => (val i).+1) (direct_ordinal_weights N)))).
Qed.

Lemma shor_with_direct_total OF :
  CQHoare.valid true direct_pre (shor_with OF) factor_post.
Proof.
apply: (@CQHoare.valid_sequence true _ direct_assertion).
- exact: pre_valid.
- apply: valid_conditional.
  + apply/(proj2 (valid_iff _ _ _ _))=>s.
    rewrite /pre CQPrimitive.assign_pre /direct_assertion /factor_post /mask
      /direct_guard get_set_eq.
    case Eg: (esem gcd_guard s)=>/=; last exact: obsf_ge0.
    have Hg : (1 < gcdn (s.[x])%M N)%N := Eg.
    rewrite Hg andbT.
    case Ex: (0 < (s.[x])%M < N)%N=>/=; last exact: obsf_ge0.
    by rewrite /gcd_expression /eval /= (immediate_gcd_factor Ex Hg).
  + apply/(proj2 (valid_iff _ _ _ _))=>s.
    rewrite /mask /direct_assertion /mask /direct_guard.
    change ((if ~~ esem gcd_guard s then
      (if (0 < (s.[x])%M < N)%N && (1 < gcdn (s.[x])%M N)%N
       then semantic_top s else (0%:VF : 'FO(Hq))) else (0%:VF : 'FO(Hq)))
       <= pre true (Sequence (order_stage OF) factor_checks) factor_post s).
    case Eg: (esem gcd_guard s)=>/=; first exact: obsf_ge0.
    have Hg : (1 < gcdn (s.[x])%M N)%N = false := Eg.
    rewrite Hg andbF; exact: obsf_ge0.
Qed.

Theorem derives_shor_with_direct OF : derives true direct_pre (shor_with OF) factor_post.
Proof. apply: derives_complete; exact: shor_with_direct_total. Qed.

Section ConcreteOrderFinding.
Variables (L t : nat) (register_capacity : (N <= 2^L)%N).
Variable qr : wf_qreg (QPair (QArray t QBool) (QArray L QBool)).
Variable measured : variable (QType (QArray t QBool)).

Definition shor : command :=
  shor_with (@ClassicalOrderFinding.order_finding N L t modulus_nontrivial
    register_capacity qr (EVar x) measured result).

Theorem shor_partial_safe : CQHoare.valid false semantic_top shor factor_post.
Proof. exact: shor_with_partial_safe. Qed.

Theorem derives_shor : derives false semantic_top shor factor_post.
Proof. exact: derives_shor_with. Qed.


Theorem shor_direct_total : CQHoare.valid true direct_pre shor factor_post.
Proof. exact: shor_with_direct_total. Qed.

Theorem derives_shor_direct : derives true direct_pre shor factor_post.
Proof. exact: derives_shor_with_direct. Qed.

End ConcreteOrderFinding.

End Wrapper.

End ClassicalShorProgram.
