(* Rectangular assertion-space SupOper; see CROSS-SPACE-NOTES.md. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate
  hoare rules primitive quantum_frame quantum_space_rules.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


Module CQQuantumCrossSpace.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame CQQuantumSpaceRules.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition rectangular_depolarizer (U V : chsType) : 'SO(U,V) :=
  ((dim U)%:R)^-1 *:
    krausso (fun ij : 'I_(dim U) * 'I_(dim V) => [>eb ij.2 : V; eb ij.1 : U<]).

Lemma rectangular_depolarizerE (U V : chsType) (A : 'End(U)) :
  rectangular_depolarizer U V A = ((dim U)%:R)^-1 *: (\Tr A *: (\1 : 'End(V))).
Proof.
rewrite /rectangular_depolarizer scale_soE kraussoE pair_bigV /=.
f_equal.
rewrite (onb_trlf eb A) scaler_suml; apply:eq_bigr=>i _.
under eq_bigr do rewrite adj_outp -comp_lfunA outp_compr outp_comp.
by rewrite -scaler_sumr sumonb_out.
Qed.

Lemma rectangular_depolarizer_cp (U V : chsType) :
  rectangular_depolarizer U V \is cpmap.
Proof.
rewrite -geso0_cpE /rectangular_depolarizer; apply: scalev_ge0.
- by rewrite invr_ge0 ler0n.
- by rewrite geso0_cpE is_cpmap.
Qed.

Lemma rectangular_depolarizer1 (U V : chsType) :
  rectangular_depolarizer U V \1 = \1.
Proof.
rewrite rectangular_depolarizerE /lftrace h2mx1 mxtrace1 scalerA mulVf ?scale1r //.
by rewrite gt_eqF // dim_proper_gt0.
Qed.

Lemma rectangular_depolarizer_dqo (U V : chsType) :
  (rectangular_depolarizer U V)^*o \is cptn.
Proof.
rewrite (CPMap_BuildE (rectangular_depolarizer_cp U V)) cp_isdqoE.
by rewrite rectangular_depolarizer1.
Qed.

Definition rectangular_depolarizing (U V : chsType) : 'DQO(U,V) :=
  DualQO_Build (rectangular_depolarizer_dqo U V).

Definition square_extension S T (F : 'DQO[msys]_(S,T)) : 'DQO[msys]_(S :|: T) :=
  castso (setUD_sub (finset.subsetUl S T), setUD_sub (finset.subsetUr S T))
    (tenso_dqoType (disjointXD S (S :|: T)) (disjointXD T (S :|: T)) F
      (rectangular_depolarizing 'H[msys]_((S :|: T) :\: S)
        'H[msys]_((S :|: T) :\: T))).

Lemma square_extension_lift S T (F : 'DQO[msys]_(S,T)) (A : 'F[msys]_S) :
  square_extension F (lift_lf (finset.subsetUl S T) A) =
    lift_lf (finset.subsetUr S T) (F A).
Proof.
rewrite /square_extension /lift_lf castsoE /= castlf_comp castlf_id.
rewrite -(@tenso_correct _ msys S T ((S :|: T) :\: S) ((S :|: T) :\: T)
  F (rectangular_depolarizer 'H[msys]_((S :|: T) :\: S)
    'H[msys]_((S :|: T) :\: T)) (disjointXD S (S :|: T))).
by rewrite rectangular_depolarizer1.
Qed.

Lemma square_extension_cylinder S T (F : 'DQO[msys]_(S,T)) (A : 'F[msys]_S) :
  liftfso (square_extension F) (liftf_lf A) = liftf_lf (F A).
Proof.
rewrite -{1}(liftf_lf2 (finset.subsetUl S T) A) liftfsoEf.
by rewrite square_extension_lift liftf_lf2.
Qed.

Lemma cylinder_tensor_action S T U R (E : 'SO[msys]_U)
    (F : 'SO[msys]_(S,T)) (A : 'F[msys]_(S :|: R)) :
  [disjoint S & R] -> [disjoint T & R] -> [disjoint R & U] ->
  (forall X : 'F[msys]_S, liftfso E (liftf_lf X) = liftf_lf (F X)) ->
  liftfso E (liftf_lf A) = liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) A).
Proof.
move=>HS HT Hd HC.
rewrite (onb_lfun2id deltav A) !linear_sum /=.
apply:eq_bigr=>i _; rewrite !linear_sum /=.
apply:eq_bigr=>j _; rewrite !linearZ /=; f_equal.
rewrite -tensodf id_soE.
rewrite [deltav j]dv_split [deltav i]dv_split -tenf_outp
  -(liftf_lf_compT _ _ HS) (liftfsoEf_compr _ _ _ Hd).
by rewrite HC (liftf_lf_compT _ _ HT).
Qed.

Lemma square_extension_tensor S T R (F : 'DQO[msys]_(S,T))
    (A : 'F[msys]_(S :|: R)) :
  [disjoint S & R] -> [disjoint T & R] ->
  liftfso (square_extension F) (liftf_lf A) =
    liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) A).
Proof.
move=>HS HT.
have Hd : [disjoint R & S :|: T].
  by rewrite disjoint_sym finset.disjoints_subset finset.subUset
    -!finset.disjoints_subset HS HT.
exact: cylinder_tensor_action HS HT Hd (square_extension_cylinder F).
Qed.

Definition cross_assertion (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (P : cmem -> 'FO[msys]_(S :|: R)) : assertion :=
  fun m => liftf_lf (ObsLf_Build
    (dqo_obslf (tenso_dqoType HS HT F (\:1 : 'DQO[msys]_R)) (P m))).

Lemma cross_assertionE (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (P : cmem -> 'FO[msys]_(S :|: R)) m :
  (@cross_assertion S T R F HS HT P m : 'End(Hq)) =
    liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) (P m)).
Proof. by []. Qed.

Lemma image_square_extension (S T R : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (P : cmem -> 'FO[msys]_(S :|: R)) :
  image (square_extension F) (lifted P) = @cross_assertion S T R F HS HT P.
Proof.
apply/funext=>m; apply/val_inj.
change (liftfso (square_extension F) (liftf_lf (P m)) =
  liftf_lf ((F :⊗ (\:1 : 'SO[msys]_R)) (P m))).
exact: square_extension_tensor HS HT.
Qed.

Theorem derives_supoper_cross total c (S T R R' : {set mlab}) (F : 'DQO[msys]_(S,T))
    (HS : [disjoint S & R]) (HT : [disjoint T & R])
    (HS' : [disjoint S & R']) (HT' : [disjoint T & R'])
    (P : cmem -> 'FO[msys]_(S :|: R))
    (Q : cmem -> 'FO[msys]_(S :|: R')) :
  [disjoint quantum_variables c & S :|: T] ->
  derives total (lifted P) c (lifted Q) ->
  derives total (@cross_assertion S T R F HS HT P) c
    (@cross_assertion S T R' F HS' HT' Q).
Proof.
move=>Hc HD; rewrite -!image_square_extension.
exact: derives_supoper Hc HD.
Qed.

End CQQuantumCrossSpace.
