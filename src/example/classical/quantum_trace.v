(* Normalized partial trace and the Trace rule, classical.pdf Table 5.
   See QUANTUM-SPACE-NOTES.md for the matrix-unit argument. *)
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
From quantum.example.classical Require Import state assertion kernel language predicate hoare rules assertion_algebra assertion_series locality operational footprint auxiliary.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.


From quantum.example.classical Require Import quantum_frame quantum_selector.

Module CQQuantumTrace.
Local Close Scope classical_set_scope.
Import CQAssertion CQPredicate CQRules ClassicalLanguage CQQuantumFrame CQQuantumSelector.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion cmem Hq).

Definition uniform_weight (U : chsType) : C := ((dim U)%:R)^-1%R.
Definition depolarizer (L : finType) (H : L -> chsType) (S : {set L}) :=
  selector (fun _ : 'Idx[H]_S => uniform_weight 'H[H]_S) (@deltav L H S).

Lemma depolarizerE (L : finType) (H : L -> chsType) S (A : 'F[H]_S) :
  depolarizer H S A = uniform_weight 'H[H]_S *: (\Tr A *: \1).
Proof. by rewrite /depolarizer selectorE -mulr_sumr -onb_trlf scalerA. Qed.

Lemma depolarizer_dqo (L : finType) (H : L -> chsType) S :
  (depolarizer H S)^*o \is cptn.
Proof.
apply: selector_dqo.
- by move=>i; rewrite /uniform_weight invr_ge0 ler0n.
- rewrite sumr_const -mulr_natl idx_card /uniform_weight mulfV //.
  by rewrite gt_eqF // dim_proper_gt0.
- by move=>i; rewrite dv_dot eqxx.
Qed.

Definition depolarizing (L : finType) (H : L -> chsType) S : 'DQO[H]_S :=
  DualQO_Build (depolarizer_dqo H S).

Lemma split_lift_outp (L : finType) (H : L -> chsType) S T (i j : 'Idx[H]_S) :
  liftf_lf [>deltav i; deltav j<] =
  liftf_lf [>deltav (idxSl (castidx (esym (setID S T)) i));
             deltav (idxSl (castidx (esym (setID S T)) j))<] \o
  liftf_lf [>deltav (idxSr (castidx (esym (setID S T)) i));
             deltav (idxSr (castidx (esym (setID S T)) j))<].
Proof.
rewrite liftf_lf_compT ?disjointID // tenf_outp -!dv_split -!deltav_cast -castlf_outp.
by rewrite liftf_lf_cast.
Qed.

Lemma partial_trace_outp (L : finType) (H : L -> chsType) S T (i j : 'Idx[H]_S) :
  ptraceso T [>deltav i; deltav j<] =
  (idxSl (castidx (esym (setID S T)) j) ==
   idxSl (castidx (esym (setID S T)) i))%:R *:
  [>deltav (idxSr (castidx (esym (setID S T)) i));
    deltav (idxSr (castidx (esym (setID S T)) j))<].
Proof.
move: (disjointID S T)=>dis.
rewrite /ptraceso {1}/fun_of_superof /= lfunE /= ptraceso_fun.unlock.
transitivity (\sum_(k : 'Idx[H]_(S :&: T))
  ((idxSl (castidx (esym (setID S T)) j) == k)%:R *
   (k == idxSl (castidx (esym (setID S T)) i))%:R) *:
  [>deltav (idxSr (castidx (esym (setID S T)) i));
    deltav (idxSr (castidx (esym (setID S T)) j))<]).
- apply:eq_bigr=>k _.
  rewrite (bigD1 (idxSr (castidx (esym (setID S T)) i))) //=
    (bigD1 (idxSr (castidx (esym (setID S T)) j))) //= !big1=>[i0/negPf ni|i0/negPf ni|].
  2: rewrite big1 // =>j0 _.
  1,2,3: rewrite castlf_outp /= !deltav_cast outpE linearZ /= !dv_split
    !idxSUl // !idxSUr // !tenv_dot // !onb_dot.
  1,2: by rewrite ?ni ?[_==i0]eq_sym ?ni ?(mulr0,mul0r) scale0r.
  by rewrite !eqxx !mulr1 !addr0.
- rewrite (bigD1 (idxSl (castidx (esym (setID S T)) i))) //=
    eqxx mulr1 big1 ?addr0 // =>k /negPf Hk.
  by rewrite Hk mulr0 scale0r.
Qed.

Lemma lift_depolarizer_outp (L : finType) (H : L -> chsType) S T (i j : 'Idx[H]_S) :
  liftfso (depolarizer H (S :&: T)) (liftf_lf [>deltav i; deltav j<]) =
  uniform_weight 'H[H]_(S :&: T) *: liftf_lf (ptraceso T [>deltav i; deltav j<]).
Proof.
have Hd : [disjoint S :\: T & S :&: T] by rewrite disjoint_sym disjointID.
rewrite (@split_lift_outp L H S T i j)
  (@liftfsoEf_compr L H (S :\: T) (S :&: T) _ _ _ Hd)
  liftfsoEf depolarizerE outp_trlf dv_dot partial_trace_outp !linearZ /=
  liftf_lf1 -!comp_lfunZl comp_lfun1l.
by rewrite !scalerA mulrC.
Qed.

Lemma lift_depolarizer (L : finType) (H : L -> chsType) S T (A : 'F[H]_S) :
  liftfso (depolarizer H (S :&: T)) (liftf_lf A) =
  uniform_weight 'H[H]_(S :&: T) *: liftf_lf (ptraceso T A).
Proof.
rewrite (onb_lfun2id deltav A) !linear_sum /=.
apply:eq_bigr=>i _; rewrite !linear_sum /=.
apply:eq_bigr=>j _.
by rewrite !linearZ /= -linear_sum /= lift_depolarizer_outp.
Qed.

Definition trace_assertion T (P : assertion) : assertion :=
  image (depolarizing msys T) P.

Lemma trace_assertionE T P s : (trace_assertion T P s : 'End(Hq)) =
  uniform_weight 'H[msys]_T *: liftf_lf (ptraceso T (P s)).
Proof.
have E := @lift_depolarizer _ msys finset.setT T (P s).
rewrite finset.setTI liftf_lf_id in E.
exact: E.
Qed.

Theorem derives_trace total P c Q (T : {set mlab}) :
  [disjoint quantum_variables c & T] -> derives total P c Q ->
  derives total (trace_assertion T P) c (trace_assertion T Q).
Proof. exact: derives_supoper. Qed.

End CQQuantumTrace.
