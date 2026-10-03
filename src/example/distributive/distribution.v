(* Explicit probabilistic small-step semantics, distributive.pdf Table 1 and
   Section 3.2. Branch families retain multiplicity; zero-weight outcomes have
   no probabilistic support. Scheduling choices remain in the step relation. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import language operational.

Module DistributedDistribution.
Import DistributedLanguage DistributedOperational.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Import Summable_Reindex.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Notation C := hermitian.C.

Lemma probability_family_nonempty X (mu : family X) :
  probability_family mu -> exists i : branch_index mu, True.
Proof.
move=>H; case: (pselect (exists i : branch_index mu, True))=>// E.
have Z : forall i : branch_index mu, branch_weight mu i = 0.
  by move=>i; exfalso; apply: E; exists i.
move: (proj2 (proj2 H)); rewrite /family_mass (eq_sum Z) summable_sum_cst0.
by move/eqP; rewrite eq_sym oner_eq0.
Qed.

Section Grouping.
Context {X : choiceType} (mu : family X).
Hypothesis Hs : summable (branch_weight mu).

Lemma family_at_sdlet : family_at mu =
    sdlet_def (branch_value mu) (Summable.build Hs).
Proof.
apply/funext=>x; rewrite /family_at /sdlet_def; apply: eq_sum=>i.
rewrite /sunit_def /=; case: asboolP=>E; case: eqP=>F //.
- by exfalso; apply: F; symmetry.
- by exfalso; apply: E; symmetry.
Qed.

Lemma family_at_summable : summable (family_at mu).
Proof. rewrite family_at_sdlet; exact: summablefP. Qed.

Lemma family_at_mass : sum (family_at mu) = family_mass mu.
Proof. by rewrite family_at_sdlet sdlet_sum. Qed.

End Grouping.

Lemma family_observe_one X (mu : family X) :
  family_observe mu (fun _ => 1) = family_mass mu.
Proof. by apply: eq_sum=>i; rewrite mulr1. Qed.

Lemma family_observe_indicator X (mu : family X) x :
  family_observe mu (fun y => if asbool (y = x) then 1 else 0) = family_at mu x.
Proof.
apply: eq_sum=>i; case: asbool; by rewrite ?mulr1 ?mulr0.
Qed.

Lemma same_distribution_at X (mu nu : family X) :
  same_distribution mu nu -> forall x, family_at mu x = family_at nu x.
Proof.
move=>E x; rewrite -!family_observe_indicator; apply: E; exists 1=>y.
by case: asbool; rewrite ?normr0 ?normr1.
Qed.

Lemma same_distribution_mass X (mu nu : family X) :
  same_distribution mu nu -> family_mass mu = family_mass nu.
Proof.
move=>E; rewrite -!family_observe_one; apply: E; exists 1=>x; by rewrite normr1.
Qed.

Lemma same_distribution_probability X (mu nu : family X) :
  probability_family mu -> admissible_family nu ->
  same_distribution nu mu -> probability_family nu.
Proof.
move=>[Hm [Hpos Hmass]] [Hn HnPos] E; split=>//; split=>//.
by rewrite (same_distribution_mass E).
Qed.

Lemma masked_summable (I : choiceType) (f : I -> C) (P : pred I) :
  summable f -> summable (fun i => if P i then f i else 0).
Proof.
move=>/summableW [M HM]; exists M; near=>A.
apply: (le_trans (y := psum (fun i => `|f i|) A)); last exact: HM.
by apply: ler_sum=>i _; rewrite /normf; case: (P (val i)); rewrite ?normr0.
Unshelve. end_near.
Qed.

Lemma nonnegative_sum_ge_term (I : choiceType) (f : I -> C) i :
  summable f -> (forall j, 0 <= f j) -> f i <= sum f.
Proof.
move=>Hs Hp; apply: etlim_ge_near; first by apply: norm_bounded_cvg.
exists ([fset i]%fset)=>// A /= HA; rewrite -[f i]psum1.
by apply: psum_ler=>// j _; apply: Hp.
Qed.

Lemma family_at_ge_branch X (mu : family X) : probability_family mu ->
  forall i, branch_weight mu i <= family_at mu (branch_value mu i).
Proof.
move=>[Hs [Hp Hm]] i; rewrite /family_at.
have Hs' := masked_summable (fun j => asbool (branch_value mu j = branch_value mu i)) Hs.
have := nonnegative_sum_ge_term i Hs' (fun j =>
  match asbool (branch_value mu j = branch_value mu i) as b return
    0 <= (if b then branch_weight mu j else 0) with
  | true => Hp j | false => lexx 0 end).
by rewrite asboolT.
Qed.

Lemma family_at_positive X (mu : family X) x : probability_family mu ->
  0 < family_at mu x ->
  exists i, branch_value mu i = x /\ 0 < branch_weight mu i.
Proof.
move=>[Hs [Hp Hm]] Hx.
case: (pselect (exists i, branch_value mu i = x /\ 0 < branch_weight mu i))=>// H.
have Z : forall i, (if asbool (branch_value mu i = x) then branch_weight mu i else 0) = 0.
  move=>i; case: asboolP=>// E.
  have N : ~~ (0 < branch_weight mu i).
    by apply/negP=>Hi; apply: H; exists i.
  by move: (Hp i); rewrite le_eqVlt (negbTE N) orbF eq_sym=>/eqP.
by move: Hx; rewrite /family_at (eq_sum Z) summable_sum_cst0 ltxx.
Qed.

Lemma same_distribution_support X (mu nu : family X) (P : X -> Prop) :
  probability_family mu -> probability_family nu -> same_distribution nu mu ->
  (forall i, 0 < branch_weight mu i -> P (branch_value mu i)) ->
  forall j, 0 < branch_weight nu j -> P (branch_value nu j).
Proof.
move=>Hm Hn E HP j Hj.
have Hmass : 0 < family_at mu (branch_value nu j).
  rewrite -(same_distribution_at E); exact: (lt_le_trans Hj (family_at_ge_branch Hn j)).
have [i [Ei Hi]] := family_at_positive Hm Hmass.
by rewrite -Ei; apply: HP.
Qed.

Definition transport_index (I : Type) (J : I -> Type) i j (E : i = j) (x : J i) : J j :=
  match E in _ = j return J j with erefl => x end.

Section Bind.
Context {X Y : Type} (mu : family X) (nu : branch_index mu -> family Y).

Definition bind_encode (i : branch_index mu) (j : branch_index (nu i)) : bind_index mu nu :=
  existT _ i j.
Arguments bind_encode i j : clear implicits.

Definition bind_decode (i : branch_index mu) (ij : bind_index mu nu) :
    option (branch_index (nu i)) :=
  match asboolP (projT1 ij = i) with
  | ReflectT E => Some (transport_index E (projT2 ij))
  | ReflectF _ => None
  end.

Lemma bind_encodeK i : pcancel (bind_encode i) (bind_decode i).
Proof.
move=>j; rewrite /bind_encode /bind_decode /=; case: asboolP=>[E|//].
by rewrite (eq_irrelevance E erefl).
Qed.

Lemma bind_decodeK i : ocancel (bind_decode i) (bind_encode i).
Proof.
case=>k j; rewrite /bind_decode /=; case: asboolP=>//= E.
by case: i / E.
Qed.

Definition bind_row (i : branch_index mu) (ij : bind_index mu nu) : C :=
  oapp (fun j => branch_weight mu i * branch_weight (nu i) j) 0 (bind_decode i ij).

Lemma bind_rowE i ij : bind_row i ij =
  if i == projT1 ij then branch_weight (bind_family mu nu) ij else 0.
Proof.
case: ij=>k j; rewrite /bind_row /bind_decode /=.
case: eqP=>[->|E]; case: asboolP=>[F|F] //=.
- by rewrite (eq_irrelevance F erefl).
- by exfalso; apply: E; symmetry.
Qed.

Hypothesis Hmu : probability_family mu.
Hypothesis Hnu : forall i, 0 < branch_weight mu i -> probability_family (nu i).

Lemma bind_row_zero i : branch_weight mu i = 0 -> forall ij, bind_row i ij = 0.
Proof. by move=>H ij; rewrite /bind_row; case: bind_decode=>//= j; rewrite H mul0r. Qed.

Lemma bind_row_bound i A : psum (fun ij => `|bind_row i ij|) A <= branch_weight mu i.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have [j0 _] := probability_family_nonempty Hi.
  rewrite (psum_Sj (@bind_encodeK i) (@bind_decodeK i) j0).
    by move=>ij H; rewrite /bind_row H /= normr0.
  rewrite /psum.
  under eq_bigr do rewrite /bind_row bind_encodeK /= normrM !ger0_norm
    ?(proj1 (proj2 Hmu)) ?(proj1 (proj2 Hi)) //.
  rewrite -mulr_sumr.
  apply: (le_trans (y := branch_weight mu i * 1)); last by rewrite mulr1.
  apply: ler_wpM2l; first exact: (proj1 (proj2 Hmu)).
  exact: (psum_le1_mu (probability_distribution Hi)).
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by rewrite Z /psum big1 // =>j _; rewrite bind_row_zero // normr0.
Qed.

Lemma bind_row_sum i : sum (bind_row i) = branch_weight mu i.
Proof.
case P: (0 < branch_weight mu i).
- have Hi := @Hnu i P.
  have Er : (bind_row i \o bind_encode i)%FUN =
      (fun j => branch_weight mu i * branch_weight (nu i) j).
    by apply/funext=>j; rewrite /= /bind_row bind_encodeK.
  rewrite (sum_reindex (@bind_encodeK i) (@bind_decodeK i)).
    by move=>ij H; rewrite /bind_row H.
    rewrite Er; exact: summable_funZ (proj1 Hi).
  rewrite Er.
  change (sum (branch_weight mu i *: Summable.build (proj1 Hi)) = branch_weight mu i).
  rewrite summable_sumZ.
  change (branch_weight mu i * family_mass (nu i) = branch_weight mu i).
  by rewrite (proj2 (proj2 Hi)) mulr1.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  rewrite (eq_sum (g := fun _ => 0)); first exact: bind_row_zero Z.
  by rewrite summable_sum_cst0.
Qed.

Lemma bind_rectangle_bound A B :
  psum (fun i => psum (fun ij => `|bind_row i ij|) B) A <= 1.
Proof.
apply: (le_trans (y := psum (branch_weight mu) A)).
  by apply: ler_sum=>i _; apply: bind_row_bound.
exact: (psum_le1_mu (probability_distribution Hmu)).
Qed.

Lemma bind_column_sum ij : sum (fun i => bind_row i ij) =
    branch_weight (bind_family mu nu) ij.
Proof.
rewrite (fin_supp_sum (S := [fset projT1 ij])) ?psum1 ?bind_rowE ?eqxx //.
by move=>i; rewrite inE=>/negPf H; rewrite bind_rowE H.
Qed.

Lemma bind_family_probability : probability_family (bind_family mu nu).
Proof.
have rect : exists M, forall A B,
    psum (fun i => psum (fun ij => `|bind_row i ij|) B) A <= M.
  by exists 1=>A B; apply: bind_rectangle_bound.
have revrect : exists M, forall B A,
    psum (fun ij => psum (fun i => `|bind_row i ij|) A) B <= M.
  exists 1=>B A; rewrite /psum exchange_big; apply: bind_rectangle_bound.
have [_ [_ [Hs _]]] := pseries_ubounded_cvg revrect.
split.
- have E : (fun ij => sum (fun i => bind_row i ij)) =
      branch_weight (bind_family mu nu).
    by apply/funext=>ij; apply: bind_column_sum.
  by rewrite -E.
split.
- case=>i j /=; case P: (0 < branch_weight mu i).
  + apply: mulr_ge0; first exact: (proj1 (proj2 Hmu)).
    exact: (proj1 (proj2 (@Hnu i P))).
  + have Z : branch_weight mu i = 0.
      by move: (proj1 (proj2 Hmu) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
    by rewrite Z mul0r.
- rewrite /family_mass -(proj2 (proj2 Hmu)).
  transitivity (sum (fun i => sum (bind_row i))).
  + rewrite (pseries2_exchange_lim rect).
    by apply: eq_sum=>ij; rewrite bind_column_sum.
  + by apply: eq_sum=>i; rewrite bind_row_sum.
Qed.

End Bind.

Lemma distribution_step_probability n (p : 'I_n -> process)
    (mu nu : family (global_configuration n)) :
  distribution_step p mu nu -> probability_family mu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  probability_family nu.
Proof.
move=>[Ha [next [Hnext E]]] Hm Hr.
have Hbind : probability_family (bind_family mu next).
  apply: bind_family_probability Hm _=>i Hi.
  case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: (global_step_probability Hs (Hr i Hi)).
exact: (same_distribution_probability Hbind Ha E).
Qed.

Lemma distribution_step_normalized n (p : 'I_n -> process)
    (mu nu : family (global_configuration n)) :
  distribution_step p mu nu -> probability_family mu ->
  (forall i, 0 < branch_weight mu i -> (branch_value mu i).2 \is den1lf) ->
  forall j, 0 < branch_weight nu j -> (branch_value nu j).2 \is den1lf.
Proof.
move=>Hstep Hm Hr.
have Hn := distribution_step_probability Hstep Hm Hr.
case: Hstep=>Ha [next [Hnext E]].
have Hbind : probability_family (bind_family mu next).
  apply: bind_family_probability Hm _=>i Hi.
  case: (Hnext i Hi)=>[[Ht ->]|Hs]; first exact: certain_probability.
  exact: (global_step_probability Hs (Hr i Hi)).
apply: (same_distribution_support (P := fun c : global_configuration n => c.2 \is den1lf) Hbind Hn E).
move=>[i j] /= Hij.
case P: (0 < branch_weight mu i).
- have N : forall k, (branch_value (next i) k).2 \is den1lf.
    case: (Hnext i P)=>[[Ht ->]|Hs].
    + by move=>k; exact: Hr.
    + exact: global_step_normalized Hs (Hr i P).
  exact: N.
- have Z : branch_weight mu i = 0.
    by move: (proj1 (proj2 Hm) i); rewrite le_eqVlt P orbF eq_sym=>/eqP.
  by move: Hij; rewrite Z mul0r ltxx.
Qed.

Section CanonicalComputation.
Context n (p : 'I_n -> process).

Definition canonical_successor (c : global_configuration n) :
    family (global_configuration n) :=
  match pselect (exists mu, global_step p c mu) with
  | left H => proj1_sig (cid H)
  | right _ => certain c
  end.

Lemma canonical_successor_step c :
  (terminal p c /\ canonical_successor c = certain c) \/
  global_step p c (canonical_successor c).
Proof.
rewrite /canonical_successor; case: pselect=>[H|H].
- right; exact: (proj2_sig (cid H)).
- left; split=>// mu Hmu; apply: H; by exists mu.
Qed.

Lemma canonical_successor_probability c : c.2 \is den1lf ->
    probability_family (canonical_successor c).
Proof.
move=>Hc; case: (canonical_successor_step c)=>[[Ht ->]|Hs].
- exact: certain_probability.
- exact: global_step_probability Hs Hc.
Qed.

Lemma canonical_successor_normalized c : c.2 \is den1lf ->
    forall i, (branch_value (canonical_successor c) i).2 \is den1lf.
Proof.
move=>Hc; case: (canonical_successor_step c)=>[[Ht ->]|Hs].
- by move=>i.
- exact: global_step_normalized Hs Hc.
Qed.

Fixpoint canonical_stage (c : global_configuration n) k : family (global_configuration n) :=
  match k with
  | 0%N => certain c
  | k.+1 => bind_family (canonical_stage c k)
      (fun i => canonical_successor (branch_value (canonical_stage c k) i))
  end.

Lemma canonical_stage_normalized c : c.2 \is den1lf ->
    forall k i, (branch_value (canonical_stage c k) i).2 \is den1lf.
Proof.
move=>Hc; elim=>[|k IH].
- by move=>i.
- move=>[i j] /=; exact: canonical_successor_normalized (IH i) j.
Qed.

Lemma canonical_stage_probability c : c.2 \is den1lf ->
    forall k, probability_family (canonical_stage c k).
Proof.
move=>Hc; elim=>[|k IH]; first exact: certain_probability.
apply: bind_family_probability IH _=>i Hi.
apply: canonical_successor_probability.
exact: (@canonical_stage_normalized c Hc k i).
Qed.

Definition canonical_computation c (Hc : c.2 \is den1lf) : computation p c.
Proof.
apply: (@Computation n p c (canonical_stage c)).
- by move=>x.
- exact: canonical_stage_probability Hc.
- by move=>k i _; exact: canonical_stage_normalized Hc k i.
- move=>k; split.
  + have [Hs [Hp _]] := canonical_stage_probability Hc k.+1.
    by split.
  + exists (fun i => canonical_successor (branch_value (canonical_stage c k) i)); split.
    * by move=>i _; apply: canonical_successor_step.
    * by move=>x.
Defined.

Theorem computation_exists c : c.2 \is den1lf -> exists pi : computation p c, True.
Proof. by move=>Hc; exists (canonical_computation Hc). Qed.

End CanonicalComputation.

End DistributedDistribution.
