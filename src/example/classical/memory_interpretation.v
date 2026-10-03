(* Typed primitive interpretation in an arbitrary finite tensor memory.
   See MEMORY-INTERPRETATION-NOTES.md for construction and covariance. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


From quantum.example.classical Require Import memory_transport.
Import CQMemoryTransport.

Module CQMemoryInterpretation.
Section Memory.
Variable S : {set mlab}.
Variable L : finType.
Variable H : L -> chsType.
Variable T V : {set L}.
Variable sub : T :<=: V.
Variable U : 'FGI('H[msys]_S, 'H[H]_T).
Local Notation HW := 'H[H]_V.

Definition transport (E : 'SO[msys]_S) : 'SO(HW) :=
  liftso sub (conjugate U E).

Lemma transport_linear : linear transport.
Proof. by move=>a E F; rewrite /transport !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build hermitian.C _ _ *:%R
  transport transport_linear.

Lemma transport1 : transport \:1 = \:1.
Proof. by rewrite /transport conjugate1 liftso1. Qed.


Lemma transport_summable (I : choiceType) (f : I -> 'SO[msys]_S) :
  summable f -> summable (fun i => transport (f i)).
Proof.
move=>Hf.
have [M HM] := (proj1 (Summable_Reindex.summableW f)) Hf.
have [k [Hk0 Hk]] := linear_bounded (transport : {linear 'SO[msys]_S -> 'SO(HW)}).
apply/Summable_Reindex.summableW; exists (k * M)=>J.
apply: le_trans (ler_wpM2l (ltW Hk0) (HM J)).
rewrite /psum mulr_sumr; apply: ler_sum=>i _; exact: Hk.
Qed.

Lemma transport_sum (I : choiceType) (f : I -> 'SO[msys]_S) :
  summable f -> transport (sum f) = sum (fun i => transport (f i)).
Proof.
move=>Hf; apply: cvg_linearP_sum; first exact: transport_linear.
exact: norm_bounded_cvg Hf.
Qed.

Definition local_operator (Q : {set mlab}) (qS : Q :<=: S) (f : 'F[msys]_Q) : 'End(HW) :=
  lift_lf sub (U \o lift_lf qS f \o U^A).

Definition typed_operator u (q : wf_qreg u) (qS : mset q :<=: S)
    (f : 'End('Ht u)) : 'End(HW) :=
  local_operator qS (tf2f q q f).

Definition unitary_channel u (q : wf_qreg u) (qS : mset q :<=: S)
    (A : 'FU('Ht u)) : 'SO(HW) := formso (typed_operator qS A).

Definition measurement_channel t u (q : wf_qreg u) (qS : mset q :<=: S)
    (M : 'QM(eval_qtype t; 'Ht u)) i : 'SO(HW) :=
  formso (typed_operator qS (M i)).

Definition initialize_channel u (q : wf_qreg u) (qS : mset q :<=: S)
    (phi : 'NS('Ht u)) : 'SO(HW) :=
  krausso (fun i : 'I_(dim 'H[msys]_(mset q)) =>
    local_operator qS [> tv2v q phi ; eb i <]).

Lemma unitary_channel_cp u (q : wf_qreg u) qS A :
  @unitary_channel u q qS A \is cpmap.
Proof. exact: is_cpmap. Qed.

Lemma unitary_channel_tp u (q : wf_qreg u) qS A :
  @unitary_channel u q qS A \is tpmap.
Proof.
rewrite /unitary_channel /typed_operator /local_operator.
exact: is_tpmap.
Qed.

Lemma measurement_channel_cp t u (q : wf_qreg u) qS M i :
  @measurement_channel t u q qS M i \is cpmap.
Proof. exact: is_cpmap. Qed.

Lemma initialize_channel_cp u (q : wf_qreg u) qS phi :
  @initialize_channel u q qS phi \is cpmap.
Proof. exact: is_cpmap. Qed.


Lemma unitary_channelE u (q : wf_qreg u) qS A :
  @unitary_channel u q qS A =
  transport (liftso qS (formso (tf2f q q A))).
Proof.
by rewrite /unitary_channel /typed_operator /local_operator /transport
  liftso_formso conjugate_formso liftso_formso.
Qed.

Lemma measurement_channelE t u (q : wf_qreg u) qS M i :
  @measurement_channel t u q qS M i =
  transport (liftso qS (formso (tf2f q q (M i)))).
Proof.
by rewrite /measurement_channel /typed_operator /local_operator /transport
  liftso_formso conjugate_formso liftso_formso.
Qed.

Lemma initialize_channelE u (q : wf_qreg u) qS phi :
  @initialize_channel u q qS phi =
  transport (liftso qS (initialso (tv2v q phi))).
Proof.
by rewrite /initialize_channel /local_operator /transport /initialso
  liftso_krausso conjugate_krausso liftso_krausso.
Qed.

Lemma transport_cp (E : 'CP[msys]_S) : transport E \is cpmap.
Proof.
rewrite /transport.
have HC := conjugate_cp U E.
exact: (liftso_cp sub (CPMap_Build HC)).
Qed.
HB.instance Definition _ (E : 'CP[msys]_S) :=
  isCPMap.Build _ _ (transport E) (transport_cp E).

Lemma transport_tn (E : 'QO[msys]_S) : transport E \is tnmap.
Proof.
rewrite /transport.
have HC := conjugate_tn U E.
exact: (liftso_tn sub (QOperation_Build HC)).
Qed.
HB.instance Definition _ (E : 'QO[msys]_S) :=
  CPMap_isTNMap.Build _ _ (transport E) (transport_tn E).

Lemma transport_tp (E : 'QC[msys]_S) : transport E \is tpmap.
Proof.
rewrite /transport.
have HC := conjugate_tp U E.
exact: (liftso_tp sub (QChannel_Build HC)).
Qed.
HB.instance Definition _ (E : 'QC[msys]_S) :=
  QOperation_isTPMap.Build _ _ (transport E) (transport_tp E).

HB.instance Definition _ u (q : wf_qreg u) qS A :=
  isCPMap.Build _ _ (@unitary_channel u q qS A) (@unitary_channel_cp u q qS A).
Lemma unitary_channel_tn u (q : wf_qreg u) qS A :
  @unitary_channel u q qS A \is tnmap.
Proof. rewrite unitary_channelE; exact: is_tnmap. Qed.
HB.instance Definition _ u (q : wf_qreg u) qS A :=
  CPMap_isTNMap.Build _ _ (@unitary_channel u q qS A) (@unitary_channel_tn u q qS A).
HB.instance Definition _ u (q : wf_qreg u) qS A :=
  QOperation_isTPMap.Build _ _ (@unitary_channel u q qS A) (@unitary_channel_tp u q qS A).

HB.instance Definition _ u (q : wf_qreg u) qS phi :=
  isCPMap.Build _ _ (@initialize_channel u q qS phi) (@initialize_channel_cp u q qS phi).
Lemma initialize_channel_tn u (q : wf_qreg u) qS phi :
  @initialize_channel u q qS phi \is tnmap.
Proof. rewrite initialize_channelE; exact: is_tnmap. Qed.
HB.instance Definition _ u (q : wf_qreg u) qS phi :=
  CPMap_isTNMap.Build _ _ (@initialize_channel u q qS phi) (@initialize_channel_tn u q qS phi).
Lemma initialize_channel_tp u (q : wf_qreg u) qS phi :
  @initialize_channel u q qS phi \is tpmap.
Proof. rewrite initialize_channelE; exact: is_tpmap. Qed.
HB.instance Definition _ u (q : wf_qreg u) qS phi :=
  QOperation_isTPMap.Build _ _ (@initialize_channel u q qS phi) (@initialize_channel_tp u q qS phi).

HB.instance Definition _ t u (q : wf_qreg u) qS M i :=
  isCPMap.Build _ _ (@measurement_channel t u q qS M i) (@measurement_channel_cp t u q qS M i).
Lemma measurement_channel_tn t u (q : wf_qreg u) qS M i :
  @measurement_channel t u q qS M i \is tnmap.
Proof.
rewrite measurement_channelE.
change (transport (liftso qS (elemso (tm2m q q M) i)) \is tnmap).
exact: is_tnmap.
Qed.
HB.instance Definition _ t u (q : wf_qreg u) qS M i :=
  CPMap_isTNMap.Build _ _ (@measurement_channel t u q qS M i)
    (@measurement_channel_tn t u q qS M i).

Lemma measurement_sumE t u (q : wf_qreg u) qS M :
  sum (@measurement_channel t u q qS M) =
  transport (liftso qS (krausso (tm2m q q M))).
Proof.
rewrite fin_dom_sum -elemso_sum !linear_sum /=.
by apply: eq_bigr=>i _; rewrite measurement_channelE.
Qed.

Lemma measurement_sum_tp t u (q : wf_qreg u) qS M :
  sum (@measurement_channel t u q qS M) \is tpmap.
Proof. rewrite measurement_sumE; exact: is_tpmap. Qed.

End Memory.

Lemma transport_original (S : {set mlab}) (E : 'SO[msys]_S) :
  @transport S mlab msys S finset.setT (finset.subsetT S)
    [giso of (\1 : 'F[msys]_S)] E = liftfso E.
Proof.
by rewrite /transport /conjugate adjf1 !formso1 comp_so1l comp_so1r.
Qed.

End CQMemoryInterpretation.
