(* Table-5 Init0, Unit0 and Meas0; see PRIMITIVE-FRAME-NOTES.md. *)
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

Module CQPrimitiveFrame.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumSpaceRules.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Lemma lifted_unital S T (A : 'F[msys]_S) (E : 'QU[msys]_T) :
  [disjoint S & T] -> liftfso E (liftf_lf A) = liftf_lf A.
Proof.
move=>Hdis; by rewrite lift_tensor_image // qu1_eq1 liftf_lf_tenf1r.
Qed.

Lemma initial_pre_frame total t (q : wf_qreg t) phi S
    (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] ->
  (pre total (Initialize q phi) (lifted P) m : 'End(Hq)) = liftf_lf (P m).
Proof.
move=>Hdis; rewrite /pre CQPrimitive.initial_pre liftfso_dual.
exact: lifted_unital Hdis.
Qed.

Lemma unitary_pre_frame total t (q : wf_qreg t) U S
    (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] ->
  (pre total (Unitary q U) (lifted P) m : 'End(Hq)) = liftf_lf (P m).
Proof.
move=>Hdis; rewrite /pre CQPrimitive.unitary_pre liftfso_dual.
exact: lifted_unital Hdis.
Qed.

Theorem derives_initialize_frame total t (q : wf_qreg t) phi S
    (P : cmem -> 'FO[msys]_S) :
  [disjoint S & mset q] ->
  derives total (lifted P) (Initialize q phi) (lifted P).
Proof.
move=>Hdis; apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>m.
by rewrite initial_pre_frame.
Qed.

Corollary derives_init0 total t (q : wf_qreg t) S
    (P : cmem -> 'FO[msys]_S) :
  [disjoint S & mset q] ->
  derives total (lifted P) (Initialize q (EConst (zero_state t))) (lifted P).
Proof. exact: derives_initialize_frame. Qed.

Theorem derives_unit0 total t (q : wf_qreg t) U S
    (P : cmem -> 'FO[msys]_S) :
  [disjoint S & mset q] ->
  derives total (lifted P) (Unitary q U) (lifted P).
Proof.
move=>Hdis; apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>m.
by rewrite unitary_pre_frame.
Qed.

Definition measurement_tensor t u (x : variable (QType t))
    (q : wf_qreg u) (M : mexpr (eval_qtype t) (eval_qtype u))
    S (P : cmem -> 'FO[msys]_S) m : 'End(Hq) :=
  \sum_v liftf_lf ((P (m.[x <- v])%M : 'F[msys]_S) \⊗
    ((tm2m q q (esem M m) v)^A \o tm2m q q (esem M m) v)).

Lemma measurement_pre_frame total t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] ->
  (pre total (Measure x q M) (lifted P) m : 'End(Hq)) =
    measurement_tensor x q M P m.
Proof.
move=>Hdis; rewrite /pre CQPrimitive.measurement_pre /measurement_tensor.
apply: eq_bigr=>v _; rewrite liftf_funE -liftf_lf_adj.
change (liftf_lf (tm2m q q (esem M m) v)^A \o
  liftf_lf (P (m.[x <- v])%M) \o liftf_lf (tm2m q q (esem M m) v) =
  liftf_lf ((P (m.[x <- v])%M : 'F[msys]_S) \⊗
    ((tm2m q q (esem M m) v)^A \o tm2m q q (esem M m) v))).
have Hd : [disjoint mset q & S] by rewrite disjoint_sym.
rewrite (@liftf_lf_compC _ msys (mset q) S
  (tm2m q q (esem M m) v)^A (P (m.[x <- v])%M) Hd).
by rewrite -comp_lfunA -liftf_lf_comp (liftf_lf_compT _ _ Hdis).
Qed.

Lemma measurement_tensor_effect t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S) m :
  [disjoint S & mset q] -> measurement_tensor x q M P m \is obslf.
Proof.
move=>Hdis; rewrite -(@measurement_pre_frame true t u x q M S P m Hdis).
exact: is_obslf.
Qed.

Definition meas0_assertion t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S)
    (Hdis : [disjoint S & mset q]) : assertion :=
  fun m => ObsLf_Build (@measurement_tensor_effect t u x q M S P m Hdis).

Lemma meas0_assertionE t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S)
    (Hdis : [disjoint S & mset q]) m :
  (@meas0_assertion t u x q M S P Hdis m : 'End(Hq)) =
    measurement_tensor x q M P m.
Proof. by []. Qed.

Theorem derives_meas0 total t u (x : variable (QType t))
    (q : wf_qreg u) M S (P : cmem -> 'FO[msys]_S)
    (Hdis : [disjoint S & mset q]) :
  derives total (@meas0_assertion t u x q M S P Hdis) (Measure x q M) (lifted P).
Proof.
apply: derives_complete; apply/(proj2 (valid_iff _ _ _ _))=>m.
by rewrite measurement_pre_frame // meas0_assertionE.
Qed.

End CQPrimitiveFrame.
