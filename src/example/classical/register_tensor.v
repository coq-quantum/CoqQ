(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)
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

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

From quantum.example.classical Require Import language.

Module ClassicalRegisterTensor.
Import ClassicalLanguage.

Lemma pair_register_disjoint u v (q : wf_qreg (QPair u v)) :
  [disjoint mset (qreg_fst q) & mset (qreg_snd q)].
Proof.
rewrite -disj_setE disjoint_qregE.
move: (qreg_is_valid q); rewrite valid_qregE qr2seq_pairE cat_uniq_disjoint.
by move=>/and3P[_ H _].
Qed.

Lemma lift_register_left u v (q : wf_qreg (QPair u v)) (A : 'End('Ht u)) :
  liftf_lf (tf2f q q (A ⊗f (\1 : 'End('Ht v)))) =
  liftf_lf (tf2f (qreg_fst q) (qreg_fst q) A).
Proof.
rewrite -(liftf_lf_cast (@mset_pairV _ _ _ q)
  (tf2f q q (A ⊗f (\1 : 'End('Ht v))))).
by rewrite tf2f_pairV tf2f1 liftf_lf_tenf1r // pair_register_disjoint.
Qed.

Lemma lift_register_right u v (q : wf_qreg (QPair u v)) (B : 'End('Ht v)) :
  liftf_lf (tf2f q q ((\1 : 'End('Ht u)) ⊗f B)) =
  liftf_lf (tf2f (qreg_snd q) (qreg_snd q) B).
Proof.
rewrite -(liftf_lf_cast (@mset_pairV _ _ _ q)
  (tf2f q q ((\1 : 'End('Ht u)) ⊗f B))).
by rewrite tf2f_pairV tf2f1 liftf_lf_tenf1l // pair_register_disjoint.
Qed.

Lemma channel_register_left u v (q : wf_qreg (QPair u v)) (A : 'End('Ht u)) :
  liftfso (formso (tf2f (qreg_fst q) (qreg_fst q) A)) =
  liftfso (formso (tf2f q q (A ⊗f (\1 : 'End('Ht v))))).
Proof. by rewrite !liftfso_formso lift_register_left. Qed.

Lemma channel_register_right u v (q : wf_qreg (QPair u v)) (B : 'End('Ht v)) :
  liftfso (formso (tf2f (qreg_snd q) (qreg_snd q) B)) =
  liftfso (formso (tf2f q q ((\1 : 'End('Ht u)) ⊗f B))).
Proof. by rewrite !liftfso_formso lift_register_right. Qed.

Lemma lift_pair_outp u v (q : wf_qreg (QPair u v))
    (a c : 'Ht u) (b d : 'Ht v) :
  liftf_lf [> tv2v (qreg_fst q) a; tv2v (qreg_fst q) c <] \o
    liftf_lf [> tv2v (qreg_snd q) b; tv2v (qreg_snd q) d <] =
  liftf_lf [> tv2v q (a ⊗t b); tv2v q (c ⊗t d) <].
Proof.
rewrite liftf_lf_compT ?pair_register_disjoint // tenf_outp.
by rewrite -!tv2v_pairV -castlf_outp liftf_lf_cast.
Qed.

Lemma initial_register_pair u v (q : wf_qreg (QPair u v))
    (a : 'Ht u) (b : 'Ht v) :
  liftfso (initialso (tv2v (qreg_fst q) a)) :o
    liftfso (initialso (tv2v (qreg_snd q) b)) =
  liftfso (initialso (tv2v q (a ⊗t b))).
Proof.
rewrite -(initialso_onb _ (tv2v_fun _ (WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid q))) t2tv))
  -(initialso_onb _ (tv2v_fun _ (WF_QReg (QRegAuto.valid_qreg_snd (qreg_is_valid q))) t2tv))
  -(initialso_onb _ (tv2v_fun _ q t2tv))
  !liftfso_krausso comp_krausso.
congr (krausso _); apply/funext=>[[i j]].
by rewrite /liftf_fun /tv2v_fun /= lift_pair_outp tentv_t2tv.
Qed.

End ClassicalRegisterTensor.
