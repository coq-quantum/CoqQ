(* Independent Table-4 rules, quantum ranking assertions, and completeness. *)
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
From quantum.example.classical Require Import state assertion language kernel operational kernel_expectation expectation expectation_limits kernel_limits predicate hoare rules primitive.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.



Module CQRuleExamples.
Import CQAssertion CQPredicate CQRules ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Implicit Types P Q : cmem -> 'FO(Hq).

Lemma assignment total t (x : variable t) e Q :
  derives total (fun s => Q (s.[x <- eval e s])%M) (Assign x e) Q.
Proof.
have E : pre total (Assign x e) Q = (fun s => Q (s.[x <- eval e s])%M).
  apply/funext=>s; apply/val_inj.
  change ((pre total (Assign x e) Q s : 'End(Hq)) =
    (Q (s.[x <- eval e s])%M : 'End(Hq))).
  exact: CQPrimitive.assign_pre.
rewrite -E; exact: DAssign.
Qed.

Example false_loop total P c : derives total P (While (EConst false) c) P.
Proof.
have E : pre total (While (EConst false) c) P = P.
  rewrite pre_while_unfold; apply/funext=>s.
  by rewrite /conditional /EConst /=.
rewrite -{1}E; exact: derives_pre.
Qed.

Example infinite_skip_partial :
  derives false semantic_top (While (EConst true) Skip) semantic_top.
Proof.
apply: (@DConsequence false semantic_top
  (mask (predC (esem (EConst true))) semantic_top)
  semantic_top semantic_top (While (EConst true) Skip)).
- exact: semantic_le_refl.
- move=>s; exact: obsf_le1.
- apply: DWhilePartial.
  have -> : mask (esem (EConst true)) semantic_top = semantic_top by [].
  exact: DSkip.
Qed.

Example infinite_skip_not_total (s : cmem) (rho : 'FD1(Hq)) :
  ~ derives true semantic_top (While (EConst true) Skip) semantic_top.
Proof.
move=>/derives_sound V.
apply: (CQHoare.abort_not_total_top s rho)=>d.
move: (V d); by rewrite /CQHoare.run true_skip_loop_diverges.
Qed.

Lemma initial_core_embeds total P c Q :
  CQHoare.derives total P c Q -> derives total P c Q.
Proof. move=>/CQHoare.derives_sound; exact: derives_complete. Qed.
End CQRuleExamples.
