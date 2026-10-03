(* Classical: semantics. See README.md and PROOF_NOTES.md. *)
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
From mathcomp.classical Require Import boolp classical_sets functions.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable.
From quantum.example.classical Require Import language state assertion.
Module ClassicalSemantics.
(* Classical-quantum language of Feng and Ying (2021), Sections 3.1 and 4.
   The kernel combinators and unbounded loop construction are reused from
   CoqQ's veri_QEC/cqwhile.v, including its classical types, higher-order
   expressions and state-dependent quantum operations. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Definition kernel := semType cmem cmem Hq Hq.

Definition measurement_branches {tc tq : qType} (q : wf_qreg tq)
    (me : mexpr (eval_qtype tc) (eval_qtype tq)) (s : store) :=
  smeas (liftf_fun (tm2m q q (esem me s))).

Lemma measurement_branchE tc tq (q : wf_qreg tq)
    (me : mexpr (eval_qtype tc) (eval_qtype tq)) s i :
  measurement_branches q me s i =
    liftfso (formso (tf2f q q (esem me s i))) :> 'SO(Hq).
Proof. by rewrite /measurement_branches /smeas /= /smeas_def -liftfso_elemso. Qed.

Lemma measurement_complete tc tq (q : wf_qreg tq)
    (me : mexpr (eval_qtype tc) (eval_qtype tq)) s :
  sum (measurement_branches q me s) \is tpmap.
Proof. rewrite /measurement_branches smeas_sum elemso_sum; exact: is_tpmap. Qed.

Definition measure_kernel {t u : qType} (x : variable (QType t))
    (q : wf_qreg u) (M : mexpr (eval_qtype t) (eval_qtype u)) : kernel :=
  measure_sem x q M.

Fixpoint denote (c : command) : kernel :=
  match c with
  | Skip => skip_sem
  | Abort => abort_sem
  | Assign t x e => assign_sem x (translate_expr e)
  | Random t x p => random_sem x (probability_expression p)
  | Measure t u x q M => measure_kernel x q M
  | Initialize u q phi => initial_sem q phi
  | Unitary u q U => unitary_sem q U
  | Sequence c1 c2 => slet (denote c1) (denote c2)
  | Conditional b c1 c0 => if_sem (translate_expr b) (denote c1) (denote c0)
  | While b c => while_sem (translate_expr b) (denote c)
  end.

Lemma denote_sequenceA c1 c2 c3 :
  denote (Sequence (Sequence c1 c2) c3) =
  denote (Sequence c1 (Sequence c2 c3)).
Proof. exact: sletA. Qed.

Lemma denote_skip_left c : denote (Sequence Skip c) = denote c.
Proof. exact: slet1l. Qed.
Lemma denote_skip_right c : denote (Sequence c Skip) = denote c.
Proof. exact: slet1r. Qed.

Lemma denote_conditional b c1 c0 s :
  denote (Conditional b c1 c0) s =
  if eval b s then denote c1 s else denote c0 s.
Proof. by []. Qed.

Lemma denote_unroll b c n :
  denote (unroll b c n) = while_sem_iter (translate_expr b) (denote c) n.
Proof. by elim: n=>[|n IH] //=; rewrite IH. Qed.

Lemma denote_while_unfold b c :
  denote (While b c) = denote (Conditional b (Sequence c (While b c)) Skip).
Proof. exact: while_sem_fixpoint. Qed.

Lemma denote_while_unroll_le b c n s :
  denote (unroll b c n) s ⊑ denote (While b c) s.
Proof. rewrite denote_unroll; exact: while_sem_ub. Qed.

Lemma denote_while_least b c s f :
  (forall n, denote (unroll b c n) s ⊑ f) -> denote (While b c) s ⊑ f.
Proof. move=>H; apply: while_sem_least=>n; by rewrite -denote_unroll. Qed.

Lemma denote_while_false b c s :
  eval b s = false -> denote (While b c) s = denote Skip s.
Proof. exact: while_sem_false. Qed.

(* Table 2 small-step semantics. Outcomes are explicit constructor arguments
   so different branches are not collapsed merely because endpoints agree. *)
Inductive step : command -> store -> 'End(Hq) ->
    option command -> store -> 'End(Hq) -> Type :=
  | StepSkip s r : step Skip s r None s r
  | StepAssign t (x : variable t) e s r :
      step (Assign x e) s r None (s.[x <- eval e s])%M r
  | StepRandom t (x : variable t) p s r i :
      step (Random x p) s r None (s.[x <- i])%M (probability_mass p s i *: r)
  | StepMeasure t u (x : variable (QType t)) (q : wf_qreg u)
      (M : mexpr (eval_qtype t) (eval_qtype u)) s r i :
      step (Measure x q M) s r None (s.[x <- i])%M (measurement_branches q M s i r)
  | StepInitialize u (q : wf_qreg u) phi s r :
      step (Initialize q phi) s r None s
        (liftfso (initialso (tv2v q (esem phi s))) r)
  | StepUnitary u (q : wf_qreg u) U s r :
      step (Unitary q U) s r None s (liftfso (formso (tf2f q q (esem U s))) r)
  | StepSequenceDone c1 c2 s r s' r' :
      step c1 s r None s' r' ->
      step (Sequence c1 c2) s r (Some c2) s' r'
  | StepSequenceMore c1 c2 c1' s r s' r' :
      step c1 s r (Some c1') s' r' ->
      step (Sequence c1 c2) s r (Some (Sequence c1' c2)) s' r'
  | StepIfTrue b c1 c0 s r : eval b s = true ->
      step (Conditional b c1 c0) s r (Some c1) s r
  | StepIfFalse b c1 c0 s r : eval b s = false ->
      step (Conditional b c1 c0) s r (Some c0) s r
  | StepWhileTrue b c s r : eval b s = true ->
      step (While b c) s r (Some (Sequence c (While b c))) s r
  | StepWhileFalse b c s r : eval b s = false ->
      step (While b c) s r None s r.

Inductive terminates : command -> store -> 'End(Hq) -> store -> 'End(Hq) -> Type :=
  | TerminatesDone c s r s' r' : step c s r None s' r' -> terminates c s r s' r'
  | TerminatesMore c c' s r s1 r1 s' r' :
      step c s r (Some c') s1 r1 -> terminates c' s1 r1 s' r' ->
      terminates c s r s' r'.

Lemma step_positive c s r c' s' r' (d : step c s r c' s' r') :
  0%:VF ⊑ r -> 0%:VF ⊑ r'.
Proof.
induction d; move=>Hr.
- exact Hr.
- exact Hr.
- by rewrite scalev_ge0 // ge0_mu.
- exact: cp_ge0 Hr.
- exact: cp_ge0 Hr.
- exact: cp_ge0 Hr.
- exact: IHd Hr.
- exact: IHd Hr.
- exact Hr.
- exact Hr.
- exact Hr.
- exact Hr.
Qed.

Lemma step_trace_le c s r c' s' r' (d : step c s r c' s' r') :
  0%:VF ⊑ r -> \Tr r' <= \Tr r.
Proof.
induction d; move=>Hr; try exact: lexx; try exact: IHd.
- rewrite linearZ /=; apply: ler_piMl; last exact: le1_mu.
  by apply: psdlf_trlf; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
Qed.

Lemma step_density c s r c' s' r' (d : step c s r c' s' r') :
  r \is denlf -> r' \is denlf.
Proof.
move=>/denlfP [Hr Htr]; have Hr0 : 0%:VF ⊑ r by rewrite -psdlfE.
apply/denlfP; split.
- by rewrite psdlfE; exact: step_positive d Hr0.
- exact: le_trans (step_trace_le d Hr0) Htr.
Qed.

Lemma measurement_total_trace t u (q : wf_qreg u)
    (M : mexpr (eval_qtype t) (eval_qtype u)) s r :
  \Tr (sum (fun i => measurement_branches q M s i r)) = \Tr r.
Proof.
rewrite -(sum_summable_soE (f := measurement_branches q M s) r).
  exact: (summable_cvg (f := measurement_branches q M s)).
by move: (measurement_complete q M s)=>/tpmapP->.
Qed.

Lemma terminates_positive c s r s' r' (d : terminates c s r s' r') :
  0%:VF ⊑ r -> 0%:VF ⊑ r'.
Proof.
elim: d=> [c0 s0 r0 s1 r1 st | c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] Hr.
- exact: step_positive st Hr.
- apply: IH; exact: step_positive st Hr.
Qed.

Lemma terminates_trace_le c s r s' r' (d : terminates c s r s' r') :
  0%:VF ⊑ r -> \Tr r' <= \Tr r.
Proof.
elim: d=> [c0 s0 r0 s1 r1 st | c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] Hr.
- exact: step_trace_le st Hr.
- apply: le_trans (step_trace_le st Hr).
  apply: IH; exact: step_positive st Hr.
Qed.

Lemma denote_zero_input c s s' : denote c s s' 0 = 0.
Proof. exact: linear0. Qed.

Example false_loop_skips c s :
  denote (While (EConst false) c) s = denote Skip s.
Proof. exact: denote_while_false. Qed.

Example integer_assignment (x : variable Integer) (z : int) s s' :
  denote (Assign x (EConst z)) s s' =
    if s' == (s.[x <- z])%M then \:1 else 0 :> 'SO(Hq).
Proof. by []. Qed.

Example integer_assignment_step (x : variable Integer) (z : int) s r :
  step (Assign x (EConst z)) s r None (s.[x <- z])%M r.
Proof. exact: StepAssign. Qed.

Lemma unroll_true_skip n :
  denote (unroll (EConst true) Skip n) = denote Abort.
Proof.
elim: n=>[|n IH] //=.
rewrite slet1l; apply/semtypeP=>s; by rewrite if_semE /= IH.
Qed.

Example true_skip_loop_diverges :
  denote (While (EConst true) Skip) = denote Abort.
Proof.
apply/semtypeP=>s; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: denote_while_least=>n; by rewrite unroll_true_skip.
- apply/lesP=>s'; rewrite /= abort_semE; exact: vdistr_ge0.
Qed.
End ClassicalSemantics.

Module CQKernel.
(* Extension of cqwhile kernels to arbitrary cq-states, classical.pdf 4.3–4.4. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Import ClassicalSemantics.
Section Kernel.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H) (d : @CQState.state I H).

Lemma branch_positive i j : 0%:VF ⊑ K i j (d i).
Proof. by rewrite -psdlfE; apply: cp_psdP; rewrite psdlfE vdistr_ge0. Qed.

Lemma row_bound i (B : {fset J}) :
  psum (fun j => `|K i j (d i)|) B <= `|d i|.
Proof.
rewrite /psum.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?branch_positive //.
rewrite -linear_sum /= -sum_soE.
rewrite psd_trfnorm ?psdlfE ?vdistr_ge0 //.
change (\Tr ((psum (K i) B) (d i)) <= \Tr (d i)).
by apply: qo_trlfE; rewrite psdlfE vdistr_ge0.
Qed.

Lemma rectangle_bound (A : {fset I}) (B : {fset J}) :
  psum (fun i => psum (fun j => `|K i j (d i)|) B) A <=
    `|d : {summable I -> 'End(H)}|.
Proof.
apply: (le_trans _ (psum_norm_ler_norm d A)).
by apply: ler_sum=>i _; apply: row_bound.
Qed.

Lemma columns_summable j : summable (fun i => K i j (d i)).
Proof.
apply: psum_ubounded_summable.
exists `|d : {summable I -> 'End(H)}|=>A.
apply: (le_trans _ (rectangle_bound A [fset j])).
by apply: ler_sum=>i _; rewrite psum1.
Qed.

Definition apply_raw j := sum (fun i => K i j (d i)).

Lemma apply_raw_summable : summable apply_raw.
Proof.
have B : exists M, forall B A,
  psum (fun j => psum (fun i => `|K i j (d i)|) A) B <= M.
  exists `|d : {summable I -> 'End(H)}|=>B A.
  by rewrite /psum exchange_big; apply: rectangle_bound.
exact: (proj1 (proj2 (proj2 (pseries_ubounded_cvg B)))).
Qed.

Definition apply_summable := Summable.build apply_raw_summable.

Lemma apply_positive j : 0%:VF ⊑ apply_raw j.
Proof.
apply: lim_gev_near.
  by apply: norm_bounded_cvg; apply: columns_summable.
by near=>A; apply: sumv_ge0=>i _; apply: branch_positive.
Unshelve. end_near.
Qed.

Lemma apply_norm_lim j : `|apply_raw j| =
  lim ((fun A => `|psum (fun i => K i j (d i)) A|) @ totally)%classic.
Proof.
symmetry; apply: lim_norm.
by apply: norm_bounded_cvg; apply: columns_summable.
Qed.

Lemma apply_psum_bound (B : {fset J}) :
  psum (fun j => `|apply_raw j|) B <= `|d : {summable I -> 'End(H)}|.
Proof.
rewrite /psum.
under eq_bigr do rewrite apply_norm_lim.
rewrite -lim_sum_apply.
  by move=>j _; apply: is_cvg_norm; apply: norm_bounded_cvg; apply: columns_summable.
apply: etlim_le.
  apply: is_cvg_sum_apply=>j _.
  by apply: is_cvg_norm; apply: norm_bounded_cvg; apply: columns_summable.
move=>A; apply: (le_trans (y :=
  \sum_(j : B) psum (fun i => `|K i (val j) (d i)|) A)).
  by apply: ler_sum=>j _; apply: ler_norm_sum.
by rewrite /psum exchange_big; apply: rectangle_bound.
Qed.

Lemma apply_l1_bound : `|apply_summable| <= `|d : {summable I -> 'End(H)}|.
Proof.
rewrite {1}/Num.Def.normr /= /summable_norm.
apply: etlim_le; first exact: summable_norm_is_cvg.
exact: apply_psum_bound.
Qed.

Lemma apply_sum_bound : `|sum apply_summable| <= 1.
Proof.
apply: (le_trans (summable_sum_ler_norm apply_summable)).
rewrite -summable_norm_sumE.
apply: (le_trans apply_l1_bound).
by rewrite -CQState.mass_l1; apply: CQState.mass_le1.
Qed.

Definition apply : @CQState.state J H :=
  VDistr.build (f := apply_summable) apply_positive apply_sum_bound.

Lemma applyE j : apply j = sum (fun i => K i j (d i)).
Proof. by []. Qed.

Lemma apply_mass : CQState.mass apply <= CQState.mass d.
Proof. by rewrite !CQState.mass_l1; exact: apply_l1_bound. Qed.

End Kernel.

Section Equations.
Context {I J : choiceType} {H : chsType}.

Lemma apply_ext (K L : semType I J H H) (d : @CQState.state I H) :
  (forall i j, K i j = L i j) -> apply K d = apply L d.
Proof.
move=>KL; apply/vdistrP=>j; rewrite !applyE.
by apply: eq_sum=>i; rewrite KL.
Qed.

Lemma apply_bottom (K : semType I J H H) :
  apply K CQState.bottom = CQState.bottom.
Proof.
apply/vdistrP=>j; rewrite applyE CQState.bottomE.
under eq_sum do rewrite CQState.bottomE linear0.
exact: summable_sum_cst0.
Qed.

Lemma apply_point (K : semType I J H H) i (rho : 'FD(H)) j :
  apply K (CQState.point i rho) j = K i j rho.
Proof.
rewrite applyE (fin_supp_sum (S := [fset i])).
  by move=>k; rewrite inE=>/negPf ki; rewrite CQState.pointE ki linear0.
by rewrite psum1 CQState.pointE eqxx.
Qed.

Lemma apply_skip (d : @CQState.state I H) : apply skip_sem d = d.
Proof.
apply/vdistrP=>j; rewrite applyE (fin_supp_sum (S := [fset j])).
  by move=>i; rewrite inE eq_sym=>/negPf ji; rewrite skip_semE ji soE.
by rewrite psum1 skip_semE eqxx soE.
Qed.

Lemma apply_abort (d : @CQState.state I H) : apply abort_sem d = CQState.bottom.
Proof.
apply/vdistrP=>j; rewrite applyE CQState.bottomE.
under eq_sum do rewrite abort_semE soE.
exact: summable_sum_cst0.
Qed.
End Equations.

Section Composition.
Context {I M J : choiceType} {H : chsType}.
Variable (K : semType I M H H) (L : semType M J H H)
  (d : @CQState.state I H).

Lemma composition_branch_bound i k j :
  `|L k j (K i k (d i))| <= `|K i k (d i)|.
Proof.
have P : K i k (d i) \is psdlf by rewrite psdlfE; apply: branch_positive.
have Q : L k j (K i k (d i)) \is psdlf := cp_psdP _ P.
rewrite (psd_trfnorm Q) (psd_trfnorm P).
exact: (qo_trlfE (QOperation_Build (dso_cptn (L k) j)) P).
Qed.

Lemma composition_rectangle j : exists B, forall A N,
  psum (fun i => psum (fun k => `|L k j (K i k (d i))|) N) A <= B.
Proof.
exists `|d : {summable I -> 'End(H)}|=>A N.
apply: (le_trans _ (rectangle_bound K d A N)).
apply: ler_sum=>i _; apply: ler_sum=>k _.
exact: composition_branch_bound.
Qed.

Lemma composition_kernel_summable i j :
  summable (fun k => L k j :o K i k).
Proof.
move: (slet_norm_uboundW K L i)=>[B PB].
apply: psum_ubounded_summable; exists B=>N.
by move: (PB [fset j] N); rewrite psum1.
Qed.

Lemma apply_sequence : apply (slet K L) d = apply L (apply K d).
Proof.
apply/vdistrP=>j; rewrite [LHS]applyE.
transitivity (sum (fun i => sum (fun k => L k j (K i k (d i))))).
  apply: eq_sum=>i.
  change ((sum (fun k => L k j :o K i k)) (d i) =
    sum (fun k => L k j (K i k (d i)))).
  rewrite sum_summable_soE.
    by apply: norm_bounded_cvg; apply: composition_kernel_summable.
  by apply: eq_sum=>k; rewrite soE.
rewrite (pseries2_exchange_lim (composition_rectangle j)).
rewrite [RHS]applyE.
apply: eq_sum=>k.
rewrite applyE cvg_linear_sum.
  by apply: norm_bounded_cvg; apply: columns_summable.
by [].
Qed.
End Composition.
End CQKernel.


Module ClassicalDeterministic.
(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.

Definition point (s : store) (F : 'SO(Hq)) (m : store) :=
  if m == s then F else 0.

Lemma sequence_point (K L : kernel) s t F :
  (forall m, K s m = point t F m) ->
  forall m, slet K L s m = L t m :o F.
Proof.
move=>HK m; change (sum (fun j : store => L j m :o K s j) = L t m :o F).
rewrite (fin_supp_sum (S := [fset t]%fset)).
- by move=>j; rewrite inE=>/negPf Hjt; rewrite HK /point Hjt comp_so0r.
- by rewrite psum1 HK /point eqxx.
Qed.

Inductive execution : command -> store -> store -> 'SO(Hq) -> Prop :=
| RunSkip s : execution Skip s s \:1
| RunAssign t (x : variable t) e s :
    execution (Assign x e) s (s.[x <- eval e s])%M \:1
| RunInitialize u (q : wf_qreg u) phi s :
    execution (Initialize q phi) s s
      (liftfso (initialso (tv2v q (eval phi s))))
| RunUnitary u (q : wf_qreg u) ue s :
    execution (Unitary q ue) s s
      (liftfso (formso (tf2f q q (eval ue s))))
| RunSequence c1 c2 s t u F G :
    execution c1 s t F -> execution c2 t u G ->
    execution (Sequence c1 c2) s u (G :o F)
| RunIfTrue b c1 c0 s t F :
    eval b s = true -> execution c1 s t F ->
    execution (Conditional b c1 c0) s t F
| RunIfFalse b c1 c0 s t F :
    eval b s = false -> execution c0 s t F ->
    execution (Conditional b c1 c0) s t F
| RunWhileFalse b c s :
    eval b s = false -> execution (While b c) s s \:1
| RunWhileTrue b c s t u F G :
    eval b s = true -> execution c s t F -> execution (While b c) t u G ->
    execution (While b c) s u (G :o F).

Theorem execution_denote c s t F : execution c s t F ->
  forall m, denote c s m = point t F m.
Proof.
move=>D; elim: c s t F / D=>[s|t x e s|u q phi s|u q ue s|
  c1 c2 s t u F G D1 IHD1 D2 IHD2|
  b c1 c0 s t F Eb D IHD|b c1 c0 s t F Eb D IHD|
  b c s Eb|b c s t u F G Eb D1 IHD1 D2 IHD2] m.
- by [].
- by [].
- by [].
- by [].
- change (slet (denote c1) (denote c2) s m = point u (G :o F) m).
  rewrite (@sequence_point (denote c1) (denote c2) s t F IHD1 m) IHD2 /point.
  by case: (m == u); rewrite ?comp_so0l.
- by rewrite denote_conditional Eb; apply: IHD.
- by rewrite denote_conditional Eb; apply: IHD.
- rewrite denote_while_unfold denote_conditional Eb; by [].
- rewrite denote_while_unfold denote_conditional Eb.
  change (slet (denote c) (denote (While b c)) s m = point u (G :o F) m).
  rewrite (@sequence_point (denote c) (denote (While b c)) s t F IHD1 m) IHD2 /point.
  by case: (m == u); rewrite ?comp_so0l.
Qed.
End ClassicalDeterministic.


Module ClassicalRegisterTensor.
(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
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


Module CQInstrument.
(* Extension of cqwhile kernels to arbitrary cq-states, classical.pdf 4.3–4.4. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

(* Atomic instrument sums. Outcomes may have countably infinite support. *)
Import ClassicalSemantics.
Section Instrument.
Context {I J : choiceType} {H : chsType}.
Variable (f : {vdistr I -> 'SO(H)}) (h : I -> J) (rho : 'End(H)).
Hypothesis positive : 0%:VF ⊑ rho.

Lemma branch_positive i : 0%:VF ⊑ f i rho.
Proof. by apply: cp_ge0. Qed.

Lemma instrument_psum_bound (A : {fset I}) :
  psum (fun i => `|f i rho|) A <= `|rho|.
Proof.
rewrite /psum.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?branch_positive //.
rewrite -linear_sum /= -sum_soE.
have Prho : rho \is psdlf by rewrite psdlfE.
rewrite (psd_trfnorm Prho).
change (\Tr ((psum f A) rho) <= \Tr rho).
apply: (qo_trlfE (QOperation_Build (psum_dso_cptn f A))).
by rewrite psdlfE.
Qed.

Lemma instrument_outputs_summable :
  summable (fun i => (sunit_def (h i) (f i rho) : {summable J -> 'End(H)})).
Proof.
apply: psum_ubounded_summable; exists `|rho|=>A.
rewrite /psum /normf.
under eq_bigr do rewrite sunit_normE.
exact: instrument_psum_bound.
Qed.

Definition instrument_outputs := Summable.build instrument_outputs_summable.

Lemma instrument_column_summable j :
  summable (fun i => sunit_def (h i) (f i : 'SO(H)) j).
Proof.
apply: psum_ubounded_summable; exists `|f : {summable I -> 'SO(H)}|=>A.
apply: (le_trans _ (psum_norm_ler_norm f A)).
apply: ler_sum=>i _; rewrite /normf /sunit_def.
by case: eqP=>_ //; rewrite normr0.
Qed.

Lemma instrument_sumE j :
  sum instrument_outputs j = (sdlet_vdistr h f j) rho.
Proof.
rewrite sum_summableE; first exact: summable_cvg.
change (sum (fun i => sunit_def (h i) (f i rho) j) =
  (sum (fun i => sunit_def (h i) (f i : 'SO(H)) j)) rho).
rewrite sum_summable_soE.
  by apply: norm_bounded_cvg; apply: instrument_column_summable.
apply: eq_sum=>i; rewrite /sunit_def.
by case: eqP=>_ //; rewrite soE.
Qed.
End Instrument.
End CQInstrument.


Module ClassicalCQWhile.
(* Classical-quantum language of Feng and Ying (2021), Sections 3.1 and 4.
   The kernel combinators and unbounded loop construction are reused from
   CoqQ's veri_QEC/cqwhile.v, including its classical types, higher-order
   expressions and state-dependent quantum operations. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage.

Fixpoint to_cqwhile (c : command) : cmd_ :=
  match c with
  | Skip => skip_
  | Abort => abort_
  | Assign t x e => assign_ x e
  | Random t x p => random_ x (probability_expression p)
  | Measure t u x q me => measure_ x q me
  | Initialize u q phi => initial_ q phi
  | Unitary u q ue => unitary_ q ue
  | Sequence c1 c2 => seqc_ (to_cqwhile c1) (to_cqwhile c2)
  | Conditional b c1 c0 => cond_ b (to_cqwhile c1) (to_cqwhile c0)
  | While b c => while_ b (to_cqwhile c)
  end.

Theorem denote_to_cqwhile c : denote c = sem_aux (to_cqwhile c).
Proof.
elim: c=>[| |t x e|t x p|t u x q me|u q phi|u q ue|
  c1 IH1 c2 IH2|b c1 IH1 c0 IH0|b c IH].
- by [].
- by [].
- by [].
- by [].
- by [].
- by [].
- by [].
- change (slet (denote c1) (denote c2) =
    slet (sem_aux (to_cqwhile c1)) (sem_aux (to_cqwhile c2))).
  by rewrite IH1 IH2.
- change (if_sem b (denote c1) (denote c0) =
    if_sem b (sem_aux (to_cqwhile c1)) (sem_aux (to_cqwhile c0))).
  by rewrite IH1 IH0.
- change (while_sem b (denote c) = while_sem b (sem_aux (to_cqwhile c))).
  by rewrite IH.
Qed.
End ClassicalCQWhile.


Module CQMemoryInstruments.
(* Countable local instruments and their cylindrical lifts.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Section Instruments.
Context {L : finType} {H : L -> chsType} {I : choiceType}.

Lemma liftso_summable_reflect (S T : {set L}) (sub : S :<=: T) (f : I -> 'SO[H]_S) :
  summable (fun i => liftso sub (f i)) -> summable f.
Proof.
move=>/Summable_Reindex.summableW[M HM].
apply/Summable_Reindex.summableW; exists M=>J.
apply: le_trans (HM J); rewrite /psum; apply: ler_sum=>i _.
exact: liftso_norm.
Qed.

Lemma liftso_sum (S T : {set L}) (sub : S :<=: T) (f : I -> 'SO[H]_S) :
  summable f -> liftso sub (sum f) = sum (fun i => liftso sub (f i)).
Proof.
move=>Hf; apply: cvg_linearP_sum; first exact: liftso_is_linear.
exact: norm_bounded_cvg Hf.
Qed.

Lemma liftfso_summable_reflect S (f : I -> 'SO[H]_S) :
  summable (fun i => liftfso (f i)) -> summable f.
Proof. exact: liftso_summable_reflect. Qed.

Lemma liftfso_sum S (f : I -> 'SO[H]_S) :
  summable f -> liftfso (sum f) = sum (fun i => liftfso (f i)).
Proof. exact: liftso_sum. Qed.

Lemma liftfso_sum_cptn_reflect S (f : I -> 'SO[H]_S) :
  summable (fun i => liftfso (f i)) ->
  sum (fun i => liftfso (f i)) \is cptn -> sum f \is cptn.
Proof.
move=>Hf Htn; rewrite -liftfso_qoE (liftfso_sum (liftfso_summable_reflect Hf)).
exact: Htn.
Qed.

End Instruments.
End CQMemoryInstruments.


Module ClassicalMeasurementExamples.
(* Extension of cqwhile kernels to arbitrary cq-states, classical.pdf 4.3–4.4. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

(* Constant and state-dependent measurements use cqwhile's existing mexpr. *)
Import ClassicalSemantics.
Import ClassicalLanguage DefaultQMem.Exports.
Local Notation Hq := 'H[msys]_finset.setT.

Definition boolean_measurement u (q : wf_qreg u) (M : 'QM(bool; 'Ht u)) :
  mexpr bool (eval_qtype u) := EConst M.

Lemma boolean_measurement_branch u (q : wf_qreg u) (M : 'QM(bool; 'Ht u)) s b :
  measurement_branches (tc := QBool) q (boolean_measurement q M) s b =
    liftfso (formso (tf2f q q (M b))) :> 'SO(Hq).
Proof. exact: (measurement_branchE (tc := QBool)). Qed.

Lemma boolean_measurement_denote u (x : variable Boolean) (q : wf_qreg u)
    (M : 'QM(bool; 'Ht u)) :
  denote (Measure x q (boolean_measurement q M)) = measure_sem x q (cst_ M).
Proof. by []. Qed.

Lemma boolean_measurement_mass u (q : wf_qreg u) (M : 'QM(bool; 'Ht u))
    s (rho : 'End(Hq)) :
  \Tr (sum (fun b => measurement_branches (tc := QBool) q (boolean_measurement q M) s b rho)) = \Tr rho.
Proof. exact: (measurement_total_trace (t := QBool)). Qed.

Definition selected_measurement u (x : variable Boolean)
    (M0 M1 : 'QM(bool; 'Ht u)) : mexpr bool (eval_qtype u) :=
  EApp (EConst (fun b => if b then M1 else M0)) (EVar x).

Lemma selected_measurement_eval u (x : variable Boolean)
    (M0 M1 : 'QM(bool; 'Ht u)) s :
  eval (selected_measurement x M0 M1) s = if (s.[x])%M then M1 else M0.
Proof. by []. Qed.
End ClassicalMeasurementExamples.


Module CQMemoryTransport.
(* Generic change of finite quantum-memory coordinates.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Definition conjugate {A B : chsType} (U : 'FGI(A,B)) (E : 'SO(A)) : 'SO(B) :=
  formso U :o E :o formso U^A.

Section Algebra.
Context {A B : chsType} (U : 'FGI(A,B)).

Lemma conjugate_linear : linear (conjugate U).
Proof. by move=>a E F; rewrite /conjugate ?comp_soPl ?comp_soPr ?comp_soPl. Qed.
HB.instance Definition _ := GRing.isLinear.Build hermitian.C _ _ *:%R
  (conjugate U) conjugate_linear.

Lemma conjugate1 : conjugate U \:1 = \:1.
Proof. by rewrite /conjugate comp_so1r formso_comp gisofEr formso1. Qed.

Lemma conjugate_formso (f : 'End(A)) :
  conjugate U (formso f) = formso (U \o f \o U^A).
Proof. by rewrite /conjugate !formso_comp. Qed.

Lemma conjugate_krausso (I : finType) (f : I -> 'End(A)) :
  conjugate U (krausso f) = krausso (fun i => U \o f i \o U^A).
Proof.
rewrite -!elemso_sum linear_sum /=.
by apply: eq_bigr=>i _; rewrite /elemso conjugate_formso.
Qed.

Lemma conjugate_cp (E : 'CP(A)) : conjugate U E \is cpmap.
Proof. rewrite /conjugate; exact: is_cpmap. Qed.

HB.instance Definition _ (E : 'CP(A)) :=
  isCPMap.Build B B (conjugate U E) (conjugate_cp E).

Lemma conjugate_tn (E : 'QO(A)) : conjugate U E \is cptn.
Proof. rewrite /conjugate; exact: is_cptn. Qed.

HB.instance Definition _ (E : 'QO(A)) :=
  isQOperation.Build B B (conjugate U E) (conjugate_tn E).

Lemma conjugate_tp (E : 'QC(A)) : conjugate U E \is cptp.
Proof. rewrite /conjugate; exact: is_cptp. Qed.

HB.instance Definition _ (E : 'QC(A)) :=
  isQChannel.Build B B (conjugate U E) (conjugate_tp E).

Lemma conjugate_comp (E F : 'SO(A)) :
  conjugate U (E :o F) = conjugate U E :o conjugate U F.
Proof.
rewrite /conjugate -!comp_soA.
by rewrite (comp_soA (formso U^A) (formso U)) formso_comp
  gisofEl formso1 comp_so1l.
Qed.

Lemma conjugateK (E : 'SO(A)) : conjugate [giso of U^A] (conjugate U E) = E.
Proof.
rewrite /conjugate adjfK -!comp_soA.
by rewrite (comp_soA (formso U^A) (formso U)) !formso_comp
  !gisofEl !formso1 comp_so1l comp_so1r.
Qed.

Lemma conjugate_injective : injective (conjugate U).
Proof. exact: can_inj conjugateK. Qed.

Lemma conjugate_apply (E : 'SO(A)) (X : 'End(A)) :
  conjugate U E (formso U X) = formso U (E X).
Proof.
rewrite /conjugate !comp_soE -[formso U^A (formso U X)]comp_soE.
by rewrite formso_comp gisofEl formso1 id_soE.
Qed.

Lemma conjugate_trace (E : 'SO(A)) (X : 'End(A)) :
  \Tr (conjugate U E (formso U X)) = \Tr (E X).
Proof. by rewrite conjugate_apply qc_trlfE. Qed.

Lemma conjugate_summable (I : choiceType) (f : I -> 'SO(A)) :
  summable f -> summable (fun i => conjugate U (f i)).
Proof.
move=>Hf.
have [M HM] := (proj1 (Summable_Reindex.summableW f)) Hf.
have [k [Hk0 Hk]] := linear_bounded (conjugate U : {linear 'SO(A) -> 'SO(B)}).
apply/Summable_Reindex.summableW; exists (k * M)=>J.
apply: le_trans (ler_wpM2l (ltW Hk0) (HM J)).
rewrite /psum mulr_sumr; apply: ler_sum=>i _; exact: Hk.
Qed.

Lemma conjugate_sum (I : choiceType) (f : I -> 'SO(A)) :
  summable f -> conjugate U (sum f) = sum (fun i => conjugate U (f i)).
Proof.
move=>Hf; apply: cvg_linearP_sum; first exact: conjugate_linear.
exact: norm_bounded_cvg Hf.
Qed.

End Algebra.
End CQMemoryTransport.


Module CQKernelLimits.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import CQKernel ClassicalLanguage.
Section Kernels.
Context {I J : choiceType} {H : chsType}.

Lemma apply_mono (K L : semType I J H H) (rho : @CQState.state I H) :
  (forall i, K i ⊑ L i) -> apply K rho ⊑ apply L rho.
Proof.
move=>KL; apply/levdP=>j.
change (sum (fun i => K i j (rho i)) ⊑ sum (fun i => L i j (rho i))).
rewrite /sum; apply: lev_lim.
- apply: norm_bounded_cvg; exact: columns_summable.
- apply: norm_bounded_cvg; exact: columns_summable.
- move=>A; apply: lev_sum=>i _.
  apply: leso_preserve_order; last exact: vdistr_ge0.
  by move: (KL (val i))=>/levdP/(_ j).
Qed.

Lemma apply_increasing (K : nat -> semType I J H H)
    (rho : @CQState.state I H) :
  (forall i, nondecreasing_seq (fun n => K n i)) ->
  nondecreasing_seq (fun n => apply (K n) rho).
Proof. by move=>inc m n mn; apply: apply_mono=>i; apply: inc. Qed.

Lemma apply_cvg_monotone (K : nat -> semType I J H H)
    (L : semType I J H H) (rho : @CQState.state I H) :
  (forall i, nondecreasing_seq (fun n => K n i)) ->
  (forall n i, K n i ⊑ L i) ->
  (forall i j, K n i j @[n --> \oo] --> L i j) ->
  (apply (K n) rho : {summable J -> 'End(H)}) @[n --> \oo] -->
    (apply L rho : {summable J -> 'End(H)}).
Proof.
move=>inc ub pointcv.
have Cpoint j : apply (K n) rho j @[n --> \oo] --> apply L rho j.
  pose col := fun n => Summable.build (columns_summable (K n) rho j).
  pose topcol := Summable.build (columns_summable L rho j).
  have ic : nondecreasing_seq col.
    move=>m n mn; apply/lesP=>i.
    apply: leso_preserve_order; last exact: vdistr_ge0.
    by move: (inc i m n mn)=>/levdP/(_ j).
  have bc : ubounded_by topcol col.
    move=>n; apply/lesP=>i.
    apply: leso_preserve_order; last exact: vdistr_ge0.
    by move: (ub n i)=>/levdP/(_ j).
  have Cc : cvgn col := snondecreasing_is_cvgn (@trfnorm_add H) ic bc.
  have E : limn col = topcol.
    apply/summableP=>i; rewrite -summableE_lim //.
    have C2 : col n i @[n --> \oo] --> L i j (rho i).
      apply: so_cvgl; exact: pointcv.
    exact (cvg_lim (@norm_hausdorff _ _) C2).
  have Csum := summable_sum_cvg Cc.
  rewrite E in Csum; exact: Csum.
have Co : cvgn (fun n => (apply (K n) rho : {summable J -> 'End(H)})).
  apply: CQState.chain_converges; exact: apply_increasing.
have E : limn (fun n => (apply (K n) rho : {summable J -> 'End(H)})) =
    (apply L rho : {summable J -> 'End(H)}).
  apply/summableP=>j; rewrite -summableE_lim //.
  exact (cvg_lim (@norm_hausdorff _ _) (Cpoint j)).
by rewrite -E.
Qed.
End Kernels.

Local Notation Hq := 'H[msys]_finset.setT.
Lemma unroll_apply_cvg b c (rho : @CQState.state cmem Hq) :
  (apply (denote (unroll b c n)) rho : {summable cmem -> 'End(Hq)}) @[n --> \oo] -->
    (apply (denote (While b c)) rho : {summable cmem -> 'End(Hq)}).
Proof.
apply: apply_cvg_monotone.
- move=>i m n mn; rewrite !denote_unroll; exact: while_sem_iter_homo mn.
- move=>n i; exact: denote_while_unroll_le.
- move=>i j; under eq_cvg do rewrite denote_unroll.
  rewrite /= -while_sem_limEE.
  apply: summableE_is_cvg; exact: while_sem_is_cvg.
Qed.

Lemma unroll_expect_cvg P b c (rho : @CQState.state cmem Hq) :
  CQAssertion.expect P (apply (denote (unroll b c n)) rho) @[n --> \oo] -->
    CQAssertion.expect P (apply (denote (While b c)) rho).
Proof. apply: CQExpectation.expect_cvg; exact: unroll_apply_cvg. Qed.
End CQKernelLimits.


Module CQKernelExpectation.
(* Absolute Fubini and expectation for cq kernels. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion.

Section KernelExpectation.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H) (P : J -> 'FO(H))
  (rho : @CQState.state I H).

Lemma kernel_expect_norm i j :
  `|\Tr (P j \o K i j (rho i))| <= `|K i j (rho i)|.
Proof.
have pos : 0%:VF ⊑ K i j (rho i) := CQKernel.branch_positive K rho i j.
rewrite ger0_norm; first by apply/trlfM_ge0; [apply: obsf_ge0 | exact: pos].
rewrite psd_trfnorm; first by rewrite psdlfE.
rewrite -{2}(comp_lfun1l (K i j (rho i))).
apply/(lef_psdtr (P j) (\1)); first apply: obsf_le1.
by rewrite psdlfE.
Qed.

Lemma kernel_expect_rectangle : exists B, forall A N,
  psum (fun i => psum (fun j => `|\Tr (P j \o K i j (rho i))|) N) A <= B.
Proof.
exists `|rho : {summable I -> 'End(H)}|=>A N.
apply: (le_trans _ (CQKernel.rectangle_bound K rho A N)).
apply: ler_sum=>i _; apply: ler_sum=>j _.
exact: kernel_expect_norm.
Qed.

Lemma expect_apply_sum :
  expect P (CQKernel.apply K rho) =
    sum (fun i => sum (fun j => \Tr (P j \o K i j (rho i)))).
Proof.
rewrite (pseries2_exchange_lim kernel_expect_rectangle) /expect.
apply: eq_sum=>j; rewrite /expect_term CQKernel.applyE.
apply: (cvg_linearP_sum (x := fun i => K i j (rho i))
  (f := fun x : 'End(H) => \Tr (P j \o x))).
  by move=>a x y; rewrite linearPr /= linearP.
by apply: norm_bounded_cvg; apply: CQKernel.columns_summable.
Qed.
End KernelExpectation.

Lemma expect_sunit {I J : choiceType} {H : chsType}
  (F : I -> 'QO(H)) (update : I -> J) (P : J -> 'FO(H))
  (rho : @CQState.state I H) :
  expect P (CQKernel.apply (sunit F update) rho) =
    sum (fun i => \Tr (P (update i) \o F i (rho i))).
Proof.
rewrite expect_apply_sum; apply: eq_sum=>i.
rewrite (fin_supp_sum (S := [fset update i]%fset)).
  move=>j; rewrite inE=>/negPf ji.
  by rewrite /sunit /= /sunit_def ji soE comp_lfun0r linear0.
by rewrite psum1 /sunit /= /sunit_def eqxx.
Qed.
End CQKernelExpectation.


Module ClassicalAlgorithmLoops.
(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic.
Local Notation Hq := 'H[msys]_finset.setT.

Definition increment (x : variable Integer) : expression int :=
  EApp (EConst (fun z : int => z + 1)) (EVar x).
Definition next_store (x : variable Integer) (s : store) :=
  (s.[x <- eval (increment x) s])%M.
Definition below (x : variable Integer) (K : nat) : bool_expr :=
  EApp (EConst (fun z : int => z < Posz K)) (EVar x).
Definition counted_unitary u (q : wf_qreg u) (U : 'FU('Ht u))
    (x : variable Integer) (K : nat) :=
  While (below x K) (Sequence (Unitary q (EConst U)) (Assign x (increment x))).

Fixpoint superop_power (A : 'SO(Hq)) n : 'SO(Hq) :=
  if n is n'.+1 then superop_power A n' :o A else \:1.

Lemma next_store_value (x : variable Integer) s k : (s.[x])%M = Posz k ->
  (next_store x s).[x]%M = Posz k.+1.
Proof.
move=>Hs; rewrite /next_store get_set_eq /increment /eval /= Hs.
by rewrite -PoszD addn1.
Qed.

Lemma counted_unitary_execution u (q : wf_qreg u) U (x : variable Integer) n k s :
  (s.[x])%M = Posz k ->
  execution (counted_unitary q U x (k + n)) s (iter n (next_store x) s)
    (superop_power (liftfso (formso (tf2f q q U))) n).
Proof.
elim: n k s=>[|n IH] k s Hs.
- rewrite addn0 /counted_unitary /=; apply: RunWhileFalse.
  by rewrite /below /eval /= Hs ltxx.
- have Hb : eval (below x (k + n.+1)) s = true.
    by rewrite /below /eval /= Hs ltz_nat addnS ltnS leq_addr.
  have Hbody : execution
      (Sequence (Unitary q (EConst U)) (Assign x (increment x))) s
      (next_store x s) (liftfso (formso (tf2f q q U))).
    rewrite -[liftfso _]comp_so1l.
    exact: (RunSequence (RunUnitary q (EConst U) s) (RunAssign x (increment x) s)).
  have Htail := IH k.+1 (next_store x s) (next_store_value Hs).
  rewrite /counted_unitary addSn -addnS in Htail.
  rewrite /counted_unitary iterSr /=.
  exact: (RunWhileTrue Hb Hbody Htail).
Qed.

Lemma counted_unitary_denote u (q : wf_qreg u) U (x : variable Integer) n k s m :
  (s.[x])%M = Posz k ->
  denote (counted_unitary q U x (k + n)) s m =
    point (iter n (next_store x) s)
      (superop_power (liftfso (formso (tf2f q q U))) n) m.
Proof.
move=>Hs; apply: execution_denote.
exact: (@counted_unitary_execution u q U x n k s Hs).
Qed.
End ClassicalAlgorithmLoops.


Module ClassicalOperational.
(* Finite terminating routes for Feng and Ying (2021), Section 4.2.
   The route representation and summation proof pattern adapt CoqQ's
   example/veri_QEC/cqwhile.v; its original file is preserved. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage Summable_Reindex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Import ClassicalSemantics.
Local Notation Hq := 'H[msys]_finset.setT.

Inductive route :=
  | TR_skip | TR_assign
  | TR_random {t} (v : value t)
  | TR_cond1 (r : route) | TR_cond2 (r : route)
  | TR_while0 | TR_while1 (r : route)
  | TR_seqc (r1 r2 : route)
  | TR_initial | TR_unitary
  | TR_measure {t} (v : value t).

HB.instance Definition _ := gen_eqMixin route.
HB.instance Definition _ := gen_choiceMixin route.

Fixpoint route_size (r : route) : nat :=
  match r with
  | TR_cond1 r | TR_cond2 r | TR_while1 r => (route_size r).+1
  | TR_seqc r1 r2 => (route_size r1 + route_size r2).+1
  | _ => 1%N
  end.

Lemma route_size_ind (P : route -> Prop) :
  (forall n, (forall r, (route_size r < n)%N -> P r) ->
    forall r, route_size r = n -> P r) -> forall r, P r.
Proof.
move=>IH r.
have [n Pn]: exists n, route_size r = n by exists (route_size r).
by elim/ltn_ind: n r Pn=>n Pn; apply/IH=>r Pr; apply/(Pn _ Pr).
Qed.

Definition cast_value (t u : sort) (E : t = u) (v : value t) : value u :=
  let: erefl in _ = u := E return value u in v.

Fixpoint eval_route (r : route) (c : command)
    (i : store * 'End(Hq)) : option (store * 'End(Hq)) :=
  match r, c with
  | TR_skip, Skip => Some i
  | TR_assign, Assign t x e => Some ((i.1.[x <- eval e i.1])%M, i.2)
  | TR_random t v, Random u x p =>
      match asboolP (t = u) with
      | ReflectT E => Some ((i.1.[x <- cast_value E v])%M,
          probability_mass p i.1 (cast_value E v) *: i.2)
      | _ => None
      end
  | TR_measure t v, Measure u _ x q M =>
      match asboolP (t = QType u) with
      | ReflectT E => Some ((i.1.[x <- cast_value E v])%M,
          measurement_branches q M i.1 (cast_value E v) i.2)
      | _ => None
      end
  | TR_initial, Initialize u q phi =>
      Some (i.1, liftfso (initialso (tv2v q (esem phi i.1))) i.2)
  | TR_unitary, Unitary u q U =>
      Some (i.1, liftfso (formso (tf2f q q (esem U i.1))) i.2)
  | TR_cond1 r, Conditional b c1 c0 =>
      if eval b i.1 then eval_route r c1 i else None
  | TR_cond2 r, Conditional b c1 c0 =>
      if ~~ eval b i.1 then eval_route r c0 i else None
  | TR_while0, While b c => if ~~ eval b i.1 then Some i else None
  | TR_while1 r, While b c =>
      if eval b i.1 then eval_route r (Sequence c (While b c)) i else None
  | TR_seqc r1 r2, Sequence c1 c2 =>
      match eval_route r1 c1 i with
      | Some m => eval_route r2 c2 m
      | None => None
      end
  | _, _ => None
  end.

Lemma terminates_sequence c1 c2 s r m q s' r' :
  terminates c1 s r m q -> terminates c2 m q s' r' ->
  terminates (Sequence c1 c2) s r s' r'.
Proof.
move=>d1; elim: d1=>[c s0 r0 s1 r1 st | c c' s0 r0 s1 r1 s2 r2 st tail IH] d2.
- exact: (@TerminatesMore (Sequence c c2) c2 s0 r0 s1 r1 s' r'
    (@StepSequenceDone c c2 s0 r0 s1 r1 st) d2).
- exact: (@TerminatesMore (Sequence c c2) (Sequence c' c2) s0 r0 s1 r1 s' r'
    (@StepSequenceMore c c2 c' s0 r0 s1 r1 st) (IH d2)).
Qed.

Lemma eval_route_sound rt c s r s' r' :
  eval_route rt c (s,r) = Some (s',r') -> terminates c s r s' r'.
Proof.
elim: rt c s r s' r'=>[| |t v|rt IH|rt IH| |rt IH|r1 IH1 r2 IH2| | |t v]
  c s r s' r'.
- case: c=>//= [= <- <-]; apply: TerminatesDone; exact: StepSkip.
- case: c=>//= t x e; move=>[= <- <-]; apply: TerminatesDone; exact: StepAssign.
- case: c=>//= u x p; case: asboolP=>//= E; move=>[= <- <-].
  apply: TerminatesDone; exact: StepRandom.
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@TerminatesMore (Conditional b c1 c0) c1 s r s r s' r'
    (@StepIfTrue b c1 c0 s r Eb) (IH c1 s r s' r' H)).
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@TerminatesMore (Conditional b c1 c0) c0 s r s r s' r'
    (@StepIfFalse b c1 c0 s r Eb) (IH c0 s r s' r' H)).
- case: c=>//= b c0; case Eb: (eval b s)=>//=; move=>[= <- <-].
  exact: (@TerminatesDone _ _ _ _ _ (@StepWhileFalse b c0 s r Eb)).
- case: c=>//= b c0; case Eb: (eval b s)=>//= H.
  exact: (@TerminatesMore (While b c0) (Sequence c0 (While b c0)) s r s r s' r'
    (@StepWhileTrue b c0 s r Eb) (IH _ s r s' r' H)).
- case: c=>//= c1 c2; case E: (eval_route r1 c1 (s,r))=>[[m q]|] //= H.
  exact: (@terminates_sequence c1 c2 s r m q s' r' (IH1 _ _ _ _ _ E) (IH2 _ _ _ _ _ H)).
- case: c=>//= u q phi; move=>[= <- <-]; apply: TerminatesDone; exact: StepInitialize.
- case: c=>//= u q U; move=>[= <- <-]; apply: TerminatesDone; exact: StepUnitary.
- case: c=>//= u z x q M; case: asboolP=>//= E; move=>[= <- <-].
  apply: TerminatesDone; exact: StepMeasure.
Qed.

Lemma step_route_complete c s r c' s' r' (d : step c s r c' s' r') :
  forall rt o,
    (match c' with None => Some (s',r') | Some k => eval_route rt k (s',r') end) = Some o ->
    exists rr, eval_route rr c (s,r) = Some o.
Proof.
induction d; move=>rt o H.
- exists TR_skip; exact H.
- exists TR_assign; exact H.
- exists (TR_random i); rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- exists (TR_measure i); rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- exists TR_initial; exact H.
- exists TR_unitary; exact H.
- have [r1 Hr1] := IHd TR_skip (s',r') erefl.
  by exists (TR_seqc r1 rt); rewrite /= Hr1.
- case: rt H=>//= r1 r2.
  case E: (eval_route r1 c1' (s',r'))=>[[m q]|] //= H.
  have [r0 Hr0] := IHd r1 (m,q) E.
  by exists (TR_seqc r0 r2); rewrite /= Hr0.
- by exists (TR_cond1 rt); rewrite /= e.
- by exists (TR_cond2 rt); rewrite /= e.
- by exists (TR_while1 rt); rewrite /= e.
- exists TR_while0; by rewrite /= e.
Qed.

Lemma terminating_route c s r s' r' :
  terminates c s r s' r' -> exists rt, eval_route rt c (s,r) = Some (s',r').
Proof.
elim=>[c0 s0 r0 s1 r1 st | c0 c1 s0 r0 s1 r1 s2 r2 st tail [rt Hrt]].
- exact: step_route_complete st TR_skip (s1,r1) erefl.
- exact: step_route_complete st rt (s2,r2) Hrt.
Qed.

Definition opfun (c : command) (s : store) (rho : 'End(Hq)) (r : route)
    : {summable store -> 'End(Hq)} :=
  match eval_route r c (s,rho) with
  | Some o => sunit_def o.1 o.2
  | None => 0
  end.

Definition opsum (c : command) (s : store) (rho : 'End(Hq))
    : {summable store -> 'End(Hq)} := sum (opfun c s rho).

Definition operational_sum := opsum.

Lemma eval_route_ge0 (r : route) (c : command) (mi : store) (qi : 'End(Hq)) :
  0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route r c (mi,qi)).
Proof.
move=>Pq; case E: (eval_route r c (mi,qi))=>[[m q]|].
- change (0%:VF ⊑ q).
  exact (@terminates_positive c mi qi m q (@eval_route_sound r c mi qi m q E) Pq).
- exact Pq.
Qed.


Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Ltac exactltac := try (intros; match goal with
  | [ H : is_true ((0 : 'End(Hq)) ⊑ ?x) |- is_true ((0 : 'End(Hq)) ⊑ ?x) ] => exact H end).

Local Definition opfun_summable (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  0%:VF ⊑ qi -> (forall S, psum \`|opfun c mi qi| S <= `|qi|).
Local Definition opsum_norm_ub (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  0%:VF ⊑ qi -> `|opsum c mi qi| <= `|qi|.
Local Definition op_sem_eq (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  forall mo, 0%:VF ⊑ qi -> opsum c mi qi mo = denote c mi mo qi.
Local Definition ind_hyp (c : command) (mi : cmem) (qi : 'End(Hq)) :=
  opfun_summable c mi qi /\ op_sem_eq c mi qi.

Lemma opfun_summable_norm_ub (c : command) (mi : cmem) (qi : 'End(Hq)) :
  opfun_summable c mi qi -> opsum_norm_ub c mi qi.
Proof.
move=>P1 Pq; rewrite /opsum.
have Ps: summable (opfun c mi qi). exists `|qi|. near=>S. by apply: P1.
rewrite (summablefE Ps). apply/(le_trans (summable_sum_ler_norm _)).
apply: etlim_le. apply: summable_norm_is_cvg. by apply: P1.
Unshelve. end_near.
Qed.

Lemma psum_lerG (I : choiceType) (T : numDomainType) (x : I -> T) (A B : {fset I}) :
  (forall i, i \in (B `\` A)%fset -> 0 <= x i) -> 
  (forall i, i \in (A `\` B)%fset -> x i <= 0) ->
    psum x A <= psum x B.
Proof.
move=>H1 H2.
rewrite -[A](fsetID B) -{3}[B](fsetID A) !psumU ?fdisjointID// fsetIC lerD2l.
apply/(le_trans (y := 0)); first rewrite -oppr_ge0 -psumN.
all: apply/sumr_ge0=>[[i/=+ _]].
by move=>/H2; rewrite fctE oppr_ge0. by move=>/H1.
Qed.

Lemma equal_OS_DS_skip (mi : cmem) (qi : 'End(Hq)) :
  ind_hyp Skip mi qi.
Proof.
split=>[Pq S|mo].
  apply/(le_trans (y := psum \`| opfun Skip mi qi | [fset TR_skip]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  by rewrite psum1/opfun/= sunit_normE.
rewrite /opsum (fin_supp_sum (S := [fset TR_skip])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite soE.
Qed. 

Lemma equal_OS_DS_assign (t : sort) (x : variable t) 
  (e : expression (value t)) (mi : cmem) (qi : 'End(Hq)) :
  ind_hyp (Assign x e) mi qi.
Proof.
split=>[Pq S|mo].
  apply/(le_trans (y := psum \`| opfun (Assign x e) mi qi | [fset TR_assign]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  by rewrite psum1/opfun/= sunit_normE.
rewrite /opsum (fin_supp_sum (S := [fset TR_assign])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite soE.
Qed.

Import Summable_Reindex.

Lemma equal_OS_DS_seqc (c1 c2: command) :
  (forall mi qi, ind_hyp c1 mi qi) ->
  (forall mi qi, ind_hyp c2 mi qi) ->
  forall mi qi, ind_hyp (Sequence c1 c2) mi qi.
move=>IH1 IH2.
pose h := (fun r => TR_seqc r.1 r.2).
pose h' := (fun r => match r with | TR_seqc r1 r2 => Some (r1,r2) | _ => None end).
have hK : pcancel h h'. by case.
have h'K : ocancel h' h. by case.
have PE: forall mi qi, 0%:VF ⊑ qi -> forall S1 S2,
  psum (fun r1 => psum (fun r2 => `|opfun (Sequence c1 c2) mi qi (TR_seqc r1 r2)|) S2) S1 <= `|qi|.
  move=>/=mi qi Pq S1 S2. rewrite/opfun/=/psum.
  move: (IH1 mi qi)=>[]/(_ Pq S1)+ _; apply: le_trans.
  apply: ler_sum=>/= i _; rewrite /opfun.
  case E: (eval_route (fsval i) c1 (mi, qi))=>[[a b]|] /=.
  rewrite sunit_normE. move: (IH2 a b)=>[] P1 _. apply: P1.
  move: (eval_route_ge0 (fsval i) c1 mi Pq); rewrite E/=; exactltac.
  by rewrite big1 normr0.
move=>mi qi.
have Pf : Hf h' (opfun (Sequence c1 c2) mi qi) by case.
have Pfn : Hf h' \`| opfun (Sequence c1 c2) mi qi|.
  by case=>//=; rewrite /opfun/= ?normr0.
have Q1: opfun_summable (Sequence c1 c2) mi qi.
move=>Pq/= S; rewrite (psum_Sj hK h'K (TR_skip,TR_skip))//=.
set T := (Sj h' (TR_skip, TR_skip) S).
pose A := (fst @` T)%fset. pose B := (snd @` T)%fset.
apply/(le_trans (y := \sum_(i <- A)\sum_(j <- B) `|opfun (Sequence c1 c2) mi qi (h (i, j))|)).
rewrite pair_big_dep_cond/= big_seq_fsetE/=. apply: psum_ler=>//.
apply/fsubsetP=>[[/=a b PT]]/=; rewrite !inE/= !andbT /A/B; apply/andP; split;
by apply/imfsetP; exists (a,b).
rewrite big_seq_fsetE; under eq_bigr do rewrite big_seq_fsetE.
by apply: PE.

split=>//; rewrite/op_sem_eq.
pose hx := (fun r : route * route => 
  match eval_route r.1 c1 (mi, qi) with
  | Some t => match eval_route r.2 c2 t with
            | Some t => sunit_def t.1 t.2
            | None => 0
            end
  | None => 0 end : {summable _ -> _}).
have Ph: (opfun (Sequence c1 c2) mi qi \o h)%FUN = hx.
  by apply/funext=>[[r1 r2]]/=; rewrite/opfun/hx/=; case: (eval_route r1 c1 (mi, qi)).
move=>mo Pq.
have Pss: summable (opfun (Sequence c1 c2) mi qi).
exists `|qi|. near=>J. by apply: Q1.
rewrite/opsum (@sum_reindex _ _ _ _ _ h h').
  1,2,3: by case.
  by apply/(reindex_summableP_simple (h' := h') _ _ (TR_skip,TR_skip)).
rewrite Ph.
have ->: sum hx = sum (fun r1 => sum (fun r2 => hx (r1,r2))).
  apply: pseries2_exchange_lim_pair.
  exists `|qi|=>/= Si Sj.
  apply/(le_trans _ (PE mi _ Pq Si Sj))/ler_sum=>i _; apply: ler_sum=>j _.
  by rewrite/hx/opfun/=; case: (eval_route (fsval i) c1 (mi, qi)).
rewrite sum_summableE.
  apply: norm_bounded_cvg. exists `|qi|. near=>J.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  rewrite/hx/opfun/=/normf/=.
  case E: (eval_route (val i) c1 (mi, qi))=>[[a1 a2]|] /=;
    last by rewrite summable_sum_cst0.
  rewrite -/(opfun c2 a1 a2) sunit_normE.
  apply: (opfun_summable_norm_ub (proj1 (IH2 a1 a2))).
  move: (eval_route_ge0 (fsval i) c1 mi Pq); rewrite E/=; exactltac.
rewrite/hx/= (eq_sum (g := (fun i => match eval_route i c1 (mi, qi) with
| Some t => denote c2 t.1 mo t.2 | None => 0 end))).
  move=>r1; case E: (eval_route r1 c1 (mi, qi))=>[[a1 a2]|] /=.
  apply: (proj2 (IH2 _ _)).
  move: (eval_route_ge0 r1 c1 mi Pq); rewrite E/=; exactltac.
  by rewrite summable_sum_cst0 summableE.
rewrite/slet_def sum_summable_soE.
  apply: norm_bounded_cvg. 
  move: (slet_norm_uboundW (denote c1) (denote c2) mi)=>[M0/(_ [fset mo]%fset) PM].
  exists M0; near=>J; by move: (PM J); rewrite psum1.
under [in RHS]eq_sum do rewrite soE -(proj2 (IH1 mi qi) _ Pq).
rewrite [RHS](eq_sum (g := fun m => sum ((fun m r => 
  match eval_route r c1 (mi, qi) with
  | Some t => if t.1 == m then denote c2 m mo t.2 else 0
  | None => 0 end) m))).
move=>m. rewrite sum_summableE.
  apply: norm_bounded_cvg; exists `|qi|; near=>J; apply: (proj1 (IH1 mi qi) Pq).
rewrite cvg_linear_sum.
  apply: norm_bounded_cvg; exists `|qi|; near=>J.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  by move: (psum_norm_ler_norm (opfun c1 mi qi (val i)) [fset m]%fset); rewrite psum1.
f_equal. apply/funext=>r; rewrite/=.
rewrite /opfun /=.
case E: (eval_route r c1 (mi, qi))=>[p|] /=;
  last by rewrite ?summableE linear0.
by rewrite/=/sunit_def eq_sym; case: eqP=>//; rewrite linear0.
rewrite pseries2_exchange_lim.
  exists `|qi|=>Mm J; rewrite/psum exchange_big/=.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  rewrite/opfun/=.
  case Er: (eval_route (val i) c1 (mi, qi))=>[p|] /=;
    last by rewrite !normr0 big1.
  rewrite sunit_normE; case E: (p.1 \in Mm).
  rewrite (bigD1 [` E])//= eqxx big1=>[j|].
  by rewrite -(inj_eq (val_inj))/= eq_sym=>/negPf ->; rewrite normr0.
  move: (eval_route_ge0 (val i) c1 mi Pq); rewrite Er/==>Pp.
  by rewrite addr0 !psd_trfnorm ?qo_trlfE ?cp_psdP ?psdlfE ?Pp.
  rewrite big1// =>[[j/= Pj _]]; case: eqP=>[Pe|]; last by rewrite normr0.
  by rewrite -Pe in Pj; rewrite Pj in E.
f_equal. apply/funext=>r.
case: (eval_route r c1 (mi, qi))=>[[a1 a2]|]; last by rewrite summable_sum_cst0.
rewrite/= (fin_supp_sum (S := [fset a1]%fset)) ?psum1 ?eqxx// =>i;
by rewrite inE eq_sym=>/negPf->.
Unshelve. all: end_near.
Qed.

Lemma equal_OS_DS_abort (mi : cmem) (qi : 'End(Hq)) : ind_hyp Abort mi qi.
Proof.
split=>??; first by rewrite/psum big1// =>i _; rewrite/opfun/=; case: (fsval i); rewrite/= normr0.
by rewrite/= abort_semE soE /opsum (fin_supp_sum (S := fset0)) ?psum0//=; case.
Qed.

Lemma equal_OS_DS_if e c1 c2 :
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c1 mi qi) ->
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c2 mi qi) ->
  forall (mi : cmem) (qi : 'End(Hq)), ind_hyp (Conditional e c1 c2)%V mi qi.
Proof.
move=>IHc1 IHc2 mi qi.
case E: (eval e mi); rewrite/opsum.
  pose h := (fun r => TR_cond1 r).
  pose h' := (fun r => match r with | TR_cond1 r => Some r | _ => None end).
  pose hx := opfun c1 mi qi.
  split=>[Pq S|mo Pq].
    rewrite (@psum_Sj _ _ h h' _ _ (TR_skip))/opfun//=. by case.
    by case=>// r/=; rewrite ?E/= normr0.
    by rewrite E; apply: (proj1 (IHc1 mi qi) Pq).
  have shx : summable hx by exists `|qi|; near=>J; apply: (proj1 (IHc1 mi qi) Pq).
  have Ph : ((fun r : route => match eval_route r (Conditional e c1 c2)%V (mi, qi) with
                                    | Some t => sunit_def t.1 t.2 : {summable _ -> _}
                                    | None => 0
                                    end) \o h)%FUN = hx.
    by apply/funext=>r/=; rewrite E.
  rewrite/opsum (@sum_reindex _ _ _ _ _ h h')=>[//||||]; first by case.
  by case=>// r/=; rewrite/opfun/= E/=.
  by rewrite Ph.
  by rewrite Ph/hx/= -/(eval e mi) E; apply (proj2 (IHc1 mi qi) mo Pq).
pose h := (fun r => TR_cond2 r).
pose h' := (fun r => match r with | TR_cond2 r => Some r | _ => None end).
pose hx := opfun c2 mi qi.
split=>[Pq S|mo Pq].
  rewrite (@psum_Sj _ _ h h' _ _ (TR_skip))/opfun//=. by case.
  by case=>// r/=; rewrite ?E/= normr0.
  by rewrite E; apply: (proj1 (IHc2 mi qi) Pq).
have shx : summable hx by exists `|qi|; near=>J; apply: (proj1 (IHc2 mi qi) Pq).
have Ph : ((fun r : route => match eval_route r (Conditional e c1 c2)%V (mi, qi) with
                                    | Some t => sunit_def t.1 t.2 : {summable _ -> _}
                                    | None => 0
                                    end) \o h)%FUN = hx.
  by apply/funext=>r/=; rewrite E.
rewrite/opsum (@sum_reindex _ _ _ _ _ h h')=>[//||||]; first by case.
by case=>// r/=; rewrite/opfun/= E/=.
by rewrite Ph.
by rewrite Ph/hx/= -/(eval e mi) E; apply (proj2 (IHc2 mi qi) mo Pq).
Unshelve. all: end_near.
Qed.

Fixpoint route_W_size r :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => (route_W_size r2).+1
  | _ => 0%N
  end.

Fixpoint route_WC_size r :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => (route_WC_size r2).+1
  | TR_cond1 (TR_seqc r1 r2) => (route_WC_size r2).+1
  | _ => 0%N
  end.

Lemma route_WC_size_ind (P : route -> Prop) :
  (forall n, (forall r, (route_WC_size r < n)%N -> P r) -> 
    forall r, route_WC_size r = n -> P r) -> forall r, P r.
Proof.
move=>IH r.
have [n Pn]: exists n, route_WC_size r = n 
  by exists (route_WC_size r).
by elim/ltn_ind: n r Pn=>n Pn; apply/IH=>r Pr; apply/(Pn _ Pr).
Qed.

Fixpoint route_W2C r : route :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => TR_cond1 (TR_seqc r1 (route_W2C r2))
  | TR_while0 => TR_cond2 TR_skip
  | TR_cond1 (TR_seqc r1 r2) => TR_while1 (TR_seqc r1 (route_W2C r2))
  | TR_cond2 TR_skip => TR_while0
  | _ => r
  end.

Lemma route_W2CK : cancel route_W2C route_W2C.
Proof.
elim/route_WC_size_ind=>n IH.
by case=>//; case=>//= r1 r2 P; do ! f_equal; apply: IH; rewrite -P.
Qed.

Fixpoint while_syn_iter e c n :=
  match n with
  | 0%N => Abort
  | S n => Conditional e (Sequence c (while_syn_iter e c n)) Skip
  end.

Lemma eval_route_WE e c r n :
  (route_W_size r < n)%N -> forall mi qi, 
    eval_route r (While e c) (mi,qi) = eval_route (route_W2C r) (while_syn_iter e c n) (mi,qi).
Proof.
elim: n r=>//= n IH.
case=>//=; case=>//=; intros; case: (eval e mi)=>//.
by case: (eval_route r1 c (mi, qi))=>//[[a1 a2]]; apply/IH/H.
Qed.

Lemma eval_route_WEN e c r n :
  (route_W_size r >= n)%N -> forall mi qi, 
    eval_route (route_W2C r) (while_syn_iter e c n) (mi,qi) = None.
Proof.
elim: n r=>//=[r _ mi qi|n IH r Pr mi qi].
case: (route_W2C r)=>//.
case: r Pr=>//=; case=>//= r1 r2; rewrite ltnS=>Pn.
case: (eval e mi)=>//; case: (eval_route r1 c (mi, qi))=>//[[a1 a2]].
by rewrite IH.
Qed.

Lemma equal_OS_DS_while_syn_iter e c:
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall n mi qi, ind_hyp (while_syn_iter e c n) mi qi.
Proof.
move=>Hc; elim=>/=.
apply: equal_OS_DS_abort.
move=>n IH; apply: equal_OS_DS_if.
by apply: equal_OS_DS_seqc.
apply: equal_OS_DS_skip.
Qed.

Lemma equal_OS_DS_while_sem_iter e c:
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall n mi qi mo, 0%:VF ⊑ qi ->
  opsum (while_syn_iter e c n) mi qi mo = 
  while_sem_iter (translate_expr e) (denote c) n mi mo qi.
Proof.
move=>Hc n mi qi mo Pq.
rewrite (proj2 (equal_OS_DS_while_syn_iter e Hc n mi qi) mo Pq).
do ! f_equal; by elim: n=>//= n->.
Qed.

Lemma equal_OS_DS_while e c :
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall (mi : cmem) (qi : 'End(Hq)), ind_hyp (While e c) mi qi.
Proof.
move=>IH.
have P0: forall mi qi,  opfun_summable (While e c) mi qi.
  move=>mi qi Pq S; rewrite/opfun.
  pose n := (\max_(i <- (route_W_size @` S)%fset) i).+1.
  apply/(le_trans _ (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq (route_W2C @` S)%fset)).
  rewrite [X in _ <= X]psum_seq_fsetE big_imfset=>[?? _ _|]; first by apply/(can_inj route_W2CK).
  rewrite-psum_seq_fsetE; apply/ler_sum=>i _.
  suff >/(eval_route_WE e c)/(_ mi qi)->: (route_W_size (val i) < n)%N by [].
  have Phi: route_W_size (val i) \in (route_W_size  @` S)%fset.
  by apply/imfsetP; exists (val i)=>//; case: i.
  by rewrite/n ltnS big_seq_fsetE/= (bigmax_sup [`Phi]%fset)//.
move=>mi qi; split=>// mo Pq.
rewrite /opsum sum_summableE.
  by apply/norm_bounded_cvg; exists `|qi|; near=>J; apply: P0.
rewrite -(summable_sigma_nat_lim route_W_size).
  exists `|qi|. near=>J. apply: (le_trans _ (P0 mi qi Pq J)).
  apply/ler_sum=>i _; 
  by move: (psum_norm_ler_norm (opfun (While e c) mi qi (val i)) [fset mo]%fset); rewrite psum1.
rewrite -while_sem_limEEE -/denote.
apply: eq_lim=>n.
rewrite -equal_OS_DS_while_sem_iter//.
rewrite/opsum sum_summableE.
  apply/norm_bounded_cvg; exists `|qi|; near=>J.
  apply: (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq J).
pose h := (fun i => route_W2C (val i)) 
  : {i : route | (route_W_size i < n)%N} -> route.
pose h' := (fun i => match asboolP (route_W_size (route_W2C i) < n)%N with
  | ReflectT Q => Some (exist (fun j => (route_W_size j < n)%N) _ Q)
  | ReflectF _ => None end).
rewrite -(@sum_reindexV _ _ _ _ _ h h')=>[[i/=Pi]|i|/=i||].
- by rewrite/h/h'/= route_W2CK; case: asboolP=>// p; rewrite (eq_irrelevance Pi p).
- by rewrite/h/h'/=; case: asboolP=>//= p; rewrite route_W2CK.
- rewrite/h'; case: asboolP=>//=/negP+ _; rewrite -leqNgt/opfun;
  by move=>/(eval_route_WEN e c)/(_ mi qi); rewrite route_W2CK=>->; rewrite summableE.
- exists `|qi|; near=>J.
  apply/(le_trans _ (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq J)).
  apply/ler_sum=>i _. 
  by move: (psum_norm_ler_norm (opfun (while_syn_iter e c n) mi qi (val i)) [fset mo]%fset); rewrite psum1.
- apply: eq_sum=>[[i Pi]].
- by rewrite/opfun (eval_route_WE _ _ Pi)/=/h/=.
Unshelve. all: end_near.
Qed.


(* A generic atomic command, encoded by outcome-labelled routes.  These
   hypotheses are the primitive's defining equations, discharged below for
   each language constructor; no correctness judgment is postulated. *)
Lemma atomic_route_adequacy (I : choiceType) (i0 : I)
    (f : {vdistr I -> 'SO(Hq)}) (h : I -> store)
    (enc : I -> route) (dec : route -> option I) c mi :
  pcancel enc dec -> ocancel dec enc ->
  (forall qi r, eval_route r c (mi,qi) =
    omap (fun i => (h i, f i qi)) (dec r)) ->
  denote c mi = sdlet_vdistr h f -> forall qi, ind_hyp c mi qi.
Proof.
move=>encK decK Eeval Esem qi; split=>[Pq S|mo Pq].
  rewrite (psum_Sj encK decK i0).
    by move=>r Hr; rewrite /opfun Eeval Hr /= normr0.
  rewrite /psum.
  under eq_bigr do rewrite /opfun Eeval encK /= sunit_normE.
  exact: (CQInstrument.instrument_psum_bound f Pq).
have Eout : (opfun c mi qi \o enc)%FUN =
    (CQInstrument.instrument_outputs f h Pq : I -> {summable store -> 'End(Hq)}).
  by apply/funext=>i; rewrite /comp /opfun Eeval encK.
rewrite /opsum (sum_reindex encK decK).
  by move=>r Hr; rewrite /opfun Eeval Hr.
  by rewrite Eout; apply: summablefP.
by rewrite Eout CQInstrument.instrument_sumE -Esem.
Qed.

Definition decode_random (t : sort) (r : route) : option (value t) :=
  match r with
  | TR_random u v => match asboolP (u = t) with
      | ReflectT E => Some (cast_value E v) | _ => None end
  | _ => None
  end.

Definition decode_measure (t : sort) (r : route) : option (value t) :=
  match r with
  | TR_measure u v => match asboolP (u = t) with
      | ReflectT E => Some (cast_value E v) | _ => None end
  | _ => None
  end.

Lemma random_encodeK t : pcancel (@TR_random t) (decode_random t).
Proof. move=>v; rewrite /decode_random; case: asboolP=>[E|//]; by rewrite (eq_irrelevance E erefl). Qed.
Lemma random_decodeK t : ocancel (decode_random t) (@TR_random t).
Proof. case=>// u v; rewrite /decode_random; case: asboolP=>//= E; by case: t / E. Qed.
Lemma measure_encodeK t : pcancel (@TR_measure t) (decode_measure t).
Proof. move=>v; rewrite /decode_measure; case: asboolP=>[E|//]; by rewrite (eq_irrelevance E erefl). Qed.
Lemma measure_decodeK t : ocancel (decode_measure t) (@TR_measure t).
Proof. case=>// u v; rewrite /decode_measure; case: asboolP=>//= E; by case: t / E. Qed.

Lemma equal_OS_DS_random t (x : variable t) p mi qi :
  ind_hyp (Random x p) mi qi.
Proof.
refine (@atomic_route_adequacy (value t) (witness (value t))
  (sdistr Hq (probability_mass p mi)) (fun i => (mi.[x <- i])%M)
  (@TR_random t) (decode_random t) (Random x p) mi
  (@random_encodeK t) (@random_decodeK t) _ _ qi).
- move=>rho; case=>//= u v; rewrite /decode_random; case: asboolP=>//= E.
  by rewrite /sdistr_def !soE.
- by [].
Qed.

Lemma equal_OS_DS_measure (t u : qType) (x : variable (QType t))
    (q : wf_qreg u) M mi qi :
  ind_hyp (@Measure t u x q M) mi qi.
Proof.
refine (@atomic_route_adequacy (value (QType t)) (witness (value (QType t)))
  (measurement_branches q M mi) (fun i => (mi.[x <- i])%M)
  (@TR_measure (QType t)) (decode_measure (QType t)) (Measure x q M) mi
  (@measure_encodeK (QType t)) (@measure_decodeK (QType t)) _ _ qi).
- by move=>rho; case=>//= z v; rewrite /decode_measure; case: asboolP.
- by [].
Qed.

Lemma equal_OS_DS_initial u (q : wf_qreg u) phi mi qi :
  ind_hyp (Initialize q phi) mi qi.
Proof.
split=>[Pq S|mo _].
  apply/(le_trans (y := psum \`| opfun (Initialize q phi) mi qi | [fset TR_initial]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  have Pqi : qi \is psdlf by rewrite psdlfE.
  have Po : (liftfso (initialso (tv2v q (esem phi mi))) qi) \is psdlf.
    rewrite psdlfE; exact: (step_positive (@StepInitialize u q phi mi qi) Pq).
  rewrite psum1/opfun/= sunit_normE (psd_trfnorm Po) (psd_trfnorm Pqi).
  exact: (step_trace_le (@StepInitialize u q phi mi qi) Pq).
rewrite/= /opsum (fin_supp_sum (S := [fset TR_initial])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite// soE.
Qed.

Lemma equal_OS_DS_unitary u (q : wf_qreg u) U mi qi :
  ind_hyp (Unitary q U) mi qi.
Proof.
split=>[Pq S|mo _].
  apply/(le_trans (y := psum \`| opfun (Unitary q U) mi qi | [fset TR_unitary]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  have Pqi : qi \is psdlf by rewrite psdlfE.
  have Po : (liftfso (formso (tf2f q q (esem U mi))) qi) \is psdlf.
    rewrite psdlfE; exact: (step_positive (@StepUnitary u q U mi qi) Pq).
  rewrite psum1/opfun/= sunit_normE (psd_trfnorm Po) (psd_trfnorm Pqi).
  exact: (step_trace_le (@StepUnitary u q U mi qi) Pq).
rewrite/= /opsum (fin_supp_sum (S := [fset TR_unitary])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite// soE.
Qed.

Theorem equal_OS_DS c mi qi : ind_hyp c mi qi.
Proof.
elim: c mi qi=>[| |t x e|t x p|t u x q M|u q phi|u q U|
  c1 IH1 c2 IH2|b c1 IH1 c0 IH0|b c IH] mi qi.
- exact: equal_OS_DS_skip.
- exact: equal_OS_DS_abort.
- exact: equal_OS_DS_assign.
- exact: equal_OS_DS_random.
- exact: equal_OS_DS_measure.
- exact: equal_OS_DS_initial.
- exact: equal_OS_DS_unitary.
- exact (@equal_OS_DS_seqc c1 c2 IH1 IH2 mi qi).
- exact (@equal_OS_DS_if b c1 c0 IH1 IH0 mi qi).
- exact (@equal_OS_DS_while b c IH mi qi).
Qed.

Theorem operational_denotational c mi qi mo :
  0%:VF ⊑ qi -> opsum c mi qi mo = denote c mi mo qi.
Proof. exact: (proj2 (equal_OS_DS c mi qi)). Qed.

Theorem operational_summable c mi qi :
  0%:VF ⊑ qi -> summable (opfun c mi qi).
Proof.
move=>Pq; exists `|qi|; near=>J.
exact: (proj1 (equal_OS_DS c mi qi) Pq J).
Unshelve. end_near.
Qed.
End ClassicalOperational.


Module CQMemoryInterpretation.
(* Typed primitive interpretation in an arbitrary finite tensor memory.
   See PROOF_NOTES.md for construction and covariance. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


Import CQMemoryTransport.
Import ClassicalSemantics.
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


Module ClassicalBoundedUnroll.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.

Fixpoint bounded_unroll (k : nat) (c : command) : command :=
  match c with
  | Sequence a b => Sequence (bounded_unroll k a) (bounded_unroll k b)
  | Conditional b a d => Conditional b (bounded_unroll k a) (bounded_unroll k d)
  | While b a => unroll b (bounded_unroll k a) k
  | _ => c
  end.

Definition kernel_le (K L : kernel) := forall s, K s ⊑ L s.
Lemma kernel_le_refl K : kernel_le K K.
Proof. by move=>s. Qed.
Lemma kernel_le_trans K L M : kernel_le K L -> kernel_le L M -> kernel_le K M.
Proof. move=>KL LM s; exact: le_trans (KL s) (LM s). Qed.
Lemma kernel_le_anti K L : kernel_le K L -> kernel_le L K -> K = L.
Proof. move=>KL LK; apply/semtypeP=>s; apply: le_anti; by rewrite KL LK. Qed.
Lemma abort_le K : kernel_le abort_sem K.
Proof. move=>s; apply/levdP=>t; rewrite abort_semE; exact: vdistr_ge0. Qed.

Lemma slet_mono K K' L L' : kernel_le K K' -> kernel_le L L' ->
  kernel_le (slet K L) (slet K' L').
Proof.
move=>KK LL s; apply/levdP=>t; change (slet_def K L s t ⊑ slet_def K' L' s t).
rewrite /slet_def; apply: lev_lim.
- apply: norm_bounded_cvg; exact: slet_in_out_summable.
- apply: norm_bounded_cvg; exact: slet_in_out_summable.
- move=>A; apply: lev_sum=>i _; apply: leso_comp; try exact: vdistr_ge0.
  + by move: (LL (val i))=>/levdP/(_ t).
  + by move: (KK s)=>/levdP/(_ (val i)).
Qed.
Lemma if_mono b K K' L L' : kernel_le K K' -> kernel_le L L' ->
  kernel_le (if_sem b K L) (if_sem b K' L').
Proof. by move=>KK LL s; rewrite !if_semE; case: (esem b s); [exact: KK|exact: LL]. Qed.
Lemma iter_mono_body b K L : kernel_le K L -> forall k,
  kernel_le (while_sem_iter b K k) (while_sem_iter b L k).
Proof.
move=>KL; elim=>[|k IH]; first exact: kernel_le_refl.
apply: if_mono; last exact: kernel_le_refl.
exact: slet_mono KL IH.
Qed.
Lemma while_mono_body b K L : kernel_le K L ->
  kernel_le (while_sem b K) (while_sem b L).
Proof.
move=>KL s; apply: while_sem_least=>k.
apply: (le_trans _ (while_sem_ub b L k s)); exact: iter_mono_body KL k s.
Qed.

Lemma bounded_unroll_mono c : forall j k, (j <= k)%N ->
  kernel_le (denote (bounded_unroll j c)) (denote (bounded_unroll k c)).
Proof.
elim: c=>[| |u x e|u x prob|u v x q M|u q phi|u q U|
  c IH d IHd|b c IH d IHd|b c IH] j k jk.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: slet_mono (IH j k jk) (IHd j k jk).
- exact: if_mono (IH j k jk) (IHd j k jk).
- move=>s; rewrite /= !denote_unroll.
  apply: (le_trans (@iter_mono_body b _ _ (IH j k jk) j s)).
  exact: while_sem_iter_homo jk.
Qed.
Lemma bounded_unroll_upper c : forall k, kernel_le (denote (bounded_unroll k c)) (denote c).
Proof.
elim: c=>[| |u x e|u x prob|u v x q M|u q phi|u q U|
  c IH d IHd|b c IH d IHd|b c IH] k.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: kernel_le_refl.
- exact: slet_mono (IH k) (IHd k).
- exact: if_mono (IH k) (IHd k).
- move=>s; rewrite /= denote_unroll.
  apply: (le_trans (@iter_mono_body b _ _ (IH k) k s)); exact: while_sem_ub.
Qed.
Lemma bounded_unroll_chain c s : nondecreasing_seq (fun k => denote (bounded_unroll k c) s).
Proof. move=>j k jk; exact: bounded_unroll_mono jk s. Qed.
End ClassicalBoundedUnroll.


Module CQPredicate.
(* Weakest preconditions for arbitrary classical-quantum kernels.
   See PROOF_NOTES.md for the infinite-sum and duality arguments. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion.
Section Kernel.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H) (Q : J -> 'FO(H)).

Definition term i j : 'End(H) := (K i j)^*o (Q j).

Lemma term_positive i j : 0%:VF ⊑ term i j.
Proof. apply: cp_ge0; exact: obsf_ge0. Qed.

Lemma partial_bound i A : psum (term i) A ⊑ (\1 : 'End(H)).
Proof.
apply: (le_trans (y := (psum (K i) A)^*o (\1))).
- rewrite /term /psum linear_sum /= sum_soE.
  apply: lev_sum=>j _; apply: cp_preserve_order; exact: obsf_le1.
- exact: dqo1_le1.
Qed.

Lemma term_summable i : summable (term i).
Proof.
apply: psum_ubounded_summable; exists (\Tr (\1 : 'End(H)))=>A.
rewrite /psum /normf.
under eq_bigr do rewrite psd_trfnorm ?psdlfE ?term_positive //.
rewrite -linear_sum /=.
apply: lef_trlf; exact: partial_bound.
Qed.

Definition wp_raw i := sum (term i).

Lemma wp_positive i : 0%:VF ⊑ wp_raw i.
Proof.
apply: lim_gev_near; first by apply: norm_bounded_cvg; apply: term_summable.
by near=>A; apply: sumv_ge0=>j _; apply: term_positive.
Unshelve. end_near.
Qed.

Lemma wp_bounded i : wp_raw i ⊑ (\1 : 'End(H)).
Proof.
apply: lim_lev_near; first by apply: norm_bounded_cvg; apply: term_summable.
by near=>A; apply: partial_bound.
Unshelve. end_near.
Qed.

Lemma wp_effect i : wp_raw i \is obslf.
Proof. by rewrite obslfE; apply/andP; split; [exact: wp_positive i | exact: wp_bounded i]. Qed.

Definition wp i : 'FO(H) := ObsLf_Build (wp_effect i).

Lemma wpE i : (wp i : 'End(H)) = sum (fun j => (K i j)^*o (Q j)).
Proof. by []. Qed.

Lemma wp_pairing i (rho : 'End(H)) :
  \Tr (wp i \o rho) = sum (fun j => \Tr (Q j \o K i j rho)).
Proof.
rewrite wpE (cvg_linearP_sum (f := fun A : 'End(H) => \Tr (A \o rho))).
- by move=>a x y; rewrite linearPl /= linearP.
- by apply: norm_bounded_cvg; apply: term_summable.
- by apply: eq_sum=>j; rewrite dualso_trlfEV.
Qed.

Lemma expect_wp (rho : @CQState.state I H) :
  expect wp rho = expect Q (CQKernel.apply K rho).
Proof.
rewrite CQKernelExpectation.expect_apply_sum /expect.
by apply: eq_sum=>i; rewrite /expect_term wp_pairing.
Qed.
End Kernel.

Section Laws.
Context {I J : choiceType} {H : chsType}.
Implicit Types (K L : semType I J H H) (P Q : J -> 'FO(H)).

Lemma wp_mono K P Q : semantic_le P Q -> semantic_le (wp K P) (wp K Q).
Proof.
move=>PQ i; rewrite !wpE.
apply: lev_lim_near.
- by apply: norm_bounded_cvg; apply: term_summable.
- by apply: norm_bounded_cvg; apply: term_summable.
- by near=>A; apply: lev_sum=>j _; apply: cp_preserve_order; apply: PQ.
Unshelve. end_near.
Qed.

Lemma dualso_mono (E F : 'SO(H)) : E ⊑ F -> E^*o ⊑ F^*o.
Proof.
move=>EF.
by rewrite -subv_ge0 -linearB geso0_cpE dualso_cpE -geso0_cpE subv_ge0.
Qed.

Lemma wp_kernel_mono K L P :
  (forall i j, K i j ⊑ L i j) -> semantic_le (wp K P) (wp L P).
Proof.
move=>KL i; rewrite !wpE; apply: lev_lim_near.
- by apply: norm_bounded_cvg; apply: term_summable.
- by apply: norm_bounded_cvg; apply: term_summable.
- near=>A; apply: lev_sum=>j _.
  apply: leso_preserve_order; [apply: dualso_mono; apply: KL | exact: obsf_ge0].
Unshelve. end_near.
Qed.

Lemma wp_ext K L P Q :
  (forall i j, K i j = L i j) -> (forall j, P j = Q j) -> wp K P = wp L Q.
Proof.
move=>KL PQ; apply/funext=>i; apply/val_inj.
change ((wp K P i : 'End(H)) = (wp L Q i : 'End(H))).
rewrite !wpE.
by apply: eq_sum=>j; rewrite KL PQ.
Qed.

Definition wlp K Q := complement (wp K (complement Q)).
Definition xp total K Q := if total then wp K Q else wlp K Q.

Lemma complementK P : complement (complement P) = P.
Proof. apply/funext=>i; apply/val_inj; by rewrite /complement /= cplmtK. Qed.

Lemma expect_wlp K Q (rho : @CQState.state I H) :
  expect (wlp K Q) rho = expect Q (CQKernel.apply K rho) +
    CQState.mass rho - CQState.mass (CQKernel.apply K rho).
Proof.
rewrite /wlp expect_complement expect_wp expect_complement -!CQState.mass_trace.
by rewrite opprB addrA [CQState.mass rho + _]addrC.
Qed.

Lemma wlp_mono K P Q : semantic_le P Q -> semantic_le (wlp K P) (wlp K Q).
Proof.
move=>PQ i; rewrite /wlp /complement /= -cplmt_lef.
apply: wp_mono=>j; rewrite /complement /= -cplmt_lef; exact: PQ.
Qed.

Lemma xp_mono total K P Q : semantic_le P Q -> semantic_le (xp total K P) (xp total K Q).
Proof. by case: total; [apply: wp_mono | apply: wlp_mono]. Qed.

Lemma wp_zero K : wp K semantic_bottom = semantic_bottom.
Proof.
apply/funext=>i; apply/val_inj.
change ((wp K semantic_bottom i : 'End(H)) = 0).
rewrite wpE.
under eq_sum do rewrite /semantic_bottom linear0.
exact: summable_sum_cst0.
Qed.

Lemma wlp_top K : wlp K semantic_top = semantic_top.
Proof.
have CT : @complement J H semantic_top = semantic_bottom.
  by apply/funext=>i; apply/val_inj; rewrite /complement /semantic_top /= cplmt1.
rewrite /wlp CT wp_zero; apply/funext=>i; apply/val_inj.
by rewrite /complement /semantic_bottom /semantic_top /= cplmt0.
Qed.

Lemma wp_add_upper K P Q (R : J -> 'FO(H)) :
  (forall j, (P j : 'End(H)) ⊑ (Q j : 'End(H)) + (R j : 'End(H))) ->
  forall i, (wp K P i : 'End(H)) ⊑ (wp K Q i : 'End(H)) + (wp K R i : 'End(H)).
Proof.
move=>PQR i; rewrite !wpE.
rewrite -(summable_sumD (Summable.build (term_summable K Q i))
  (Summable.build (term_summable K R i))).
apply: lev_lim_near.
- by apply: norm_bounded_cvg; apply: term_summable.
- exact: summable_cvg.
- near=>A; apply: lev_sum=>j _; rewrite summableE /= /term -linearD /=.
  apply: cp_preserve_order; exact: PQR.
Unshelve. end_near.
Qed.

Lemma wp_difference K P Q (R : J -> 'FO(H)) :
  (forall j, (R j : 'End(H)) = (P j : 'End(H)) - (Q j : 'End(H))) ->
  forall i, (wp K R i : 'End(H)) = (wp K P i : 'End(H)) - (wp K Q i : 'End(H)).
Proof.
move=>RPQ i; rewrite !wpE.
rewrite -(summable_sumB (Summable.build (term_summable K P i))
  (Summable.build (term_summable K Q i))).
by apply: eq_sum=>j; rewrite summableE /= /term RPQ linearB.
Qed.

End Laws.

Section Point.
Context {I J : choiceType} {H : chsType}.
Lemma wp_point (K : semType I J H H) (Q : J -> 'FO(H)) i (rho : 'FD(H)) :
  \Tr (wp K Q i \o rho) = expect Q (CQKernel.apply K (CQState.point i rho)).
Proof.
rewrite -expect_wp (@expect_singleton I H (wp K Q) (CQState.point i rho) i).
- by move=>j /negPf ji; rewrite CQState.pointE ji.
- by rewrite CQState.pointE eqxx.
Qed.

End Point.

Section Composition.
Context {I M J : choiceType} {H : chsType}.

Lemma effect_eq (P Q : 'FO(H)) :
  (forall rho : 'FD(H), \Tr (P \o rho) = \Tr (Q \o rho)) -> P = Q.
Proof.
move=>PQ; apply/val_inj/le_anti/andP; split;
  apply/lef_trden=>rho; by rewrite PQ.
Qed.

Lemma wp_sequence (K : semType I M H H) (L : semType M J H H) Q :
  wp (slet K L) Q = wp K (wp L Q).
Proof.
apply/funext=>i; apply: effect_eq=>rho.
by rewrite !wp_point expect_wp CQKernel.apply_sequence.
Qed.

Lemma wlp_sequence (K : semType I M H H) (L : semType M J H H) Q :
  wlp (slet K L) Q = wlp K (wlp L Q).
Proof. by rewrite /wlp wp_sequence complementK. Qed.

Lemma xp_sequence total (K : semType I M H H) (L : semType M J H H) Q :
  xp total (slet K L) Q = xp total K (xp total L Q).
Proof. by case: total; [apply: wp_sequence | apply: wlp_sequence]. Qed.
End Composition.

Section Primitives.
Context {I J : choiceType} {H : chsType}.

Lemma wp_sunit (F : I -> 'QO(H)) (update : I -> J) (Q : J -> 'FO(H)) i :
  (wp (sunit F update) Q i : 'End(H)) = (F i)^*o (Q (update i)).
Proof.
rewrite wpE (fin_supp_sum (S := [fset update i]%fset)).
- move=>j; rewrite inE=>/negPf ji.
  by rewrite /sunit /= /sunit_def ji dualso0 soE.
- by rewrite psum1 /sunit /= /sunit_def eqxx.
Qed.

Lemma xp_sunit total (F : I -> 'QC(H)) (update : I -> J)
    (Q : J -> 'FO(H)) i :
  (xp total (sunit (fun i => (F i : 'QO(H))) update) Q i : 'End(H)) =
    (F i)^*o (Q (update i)).
Proof.
case: total; first exact: wp_sunit.
change (cplmt (wp (sunit (fun i => (F i : 'QO(H))) update) (complement Q) i) =
  (F i)^*o (Q (update i))).
by rewrite wp_sunit cplmt_dualC /= /complement /= cplmtK.
Qed.

Lemma wp_skip (Q : I -> 'FO(H)) : wp skip_sem Q = Q.
Proof.
apply/funext=>i; apply: effect_eq=>rho.
rewrite wp_point CQKernel.apply_skip (@expect_singleton I H Q (CQState.point i rho) i).
- by move=>j /negPf ji; rewrite CQState.pointE ji.
- by rewrite CQState.pointE eqxx.
Qed.

Lemma wp_abort (Q : I -> 'FO(H)) :
  wp (@abort_sem I H) Q = semantic_bottom.
Proof.
apply/funext=>i; apply/val_inj.
change ((wp (@abort_sem I H) Q i : 'End(H)) = 0).
rewrite wpE.
under eq_sum do rewrite abort_semE dualso0 soE.
exact: summable_sum_cst0.
Qed.

Lemma wlp_skip (Q : I -> 'FO(H)) : wlp skip_sem Q = Q.
Proof. by rewrite /wlp wp_skip complementK. Qed.

Lemma wlp_abort (Q : I -> 'FO(H)) :
  wlp (@abort_sem I H) Q = semantic_top.
Proof.
rewrite /wlp wp_abort; apply/funext=>i; apply/val_inj.
by rewrite /complement /semantic_bottom /semantic_top /= cplmt0.
Qed.

Lemma xp_skip total (Q : I -> 'FO(H)) : xp total skip_sem Q = Q.
Proof. by case: total; [apply: wp_skip | apply: wlp_skip]. Qed.
End Primitives.

Section Branching.
Context {H : chsType}.
Variable (b : bexpr) (K L : semType cmem cmem H H).
Implicit Type Q : cmem -> 'FO(H).

Lemma wp_conditional Q :
  wp (if_sem b K L) Q = conditional (esem b) (wp K Q) (wp L Q).
Proof.
apply/funext=>i; apply/val_inj.
change ((wp (if_sem b K L) Q i : 'End(H)) =
  (conditional (esem b) (wp K Q) (wp L Q) i : 'End(H))).
rewrite wpE /conditional /= /if_sem /=.
by case: (esem b i); rewrite wpE.
Qed.

Lemma wlp_conditional Q :
  wlp (if_sem b K L) Q = conditional (esem b) (wlp K Q) (wlp L Q).
Proof.
rewrite /wlp wp_conditional; apply/funext=>i.
by rewrite /complement /conditional; case: (esem b i).
Qed.

Lemma xp_conditional total Q :
  xp total (if_sem b K L) Q = conditional (esem b) (xp total K Q) (xp total L Q).
Proof. by case: total; [apply: wp_conditional | apply: wlp_conditional]. Qed.
End Branching.

Section Reindexing.
Context {I T J : choiceType} {H : chsType}.
Variable (f : I -> T -> J) (g : I -> {vdistr T -> 'SO(H)})
  (Q : J -> 'FO(H)).

Definition row_kernel i : semType unit T H H := SemType (fun _ => g i).
Definition row_effects i := Summable.build
  (term_summable (row_kernel i) (fun t => Q (f i t)) tt).

Lemma filtered_row_summable i j :
  summable (fun t => sunit_def (f i t) (g i t : 'SO(H)) j).
Proof.
apply: psum_ubounded_summable.
exists `|g i : {summable T -> 'SO(H)}|=>A.
apply: (le_trans _ (psum_norm_ler_norm (g i) A)).
apply: ler_sum=>t _; rewrite /sunit_def /normf.
by case: ifP=>_; rewrite ?normr0.
Qed.

Lemma wp_sdlet i :
  (wp (sdlet f g) Q i : 'End(H)) = sum (fun t => (g i t)^*o (Q (f i t))).
Proof.
rewrite wpE.
transitivity (sum (sdlet_def (f i) (row_effects i))).
- apply: eq_sum=>j.
  change ((sum (fun t => sunit_def (f i t) (g i t : 'SO(H)) j))^*o (Q j) =
    sum (fun t => sunit_def (f i t) (row_effects i t) j)).
  rewrite (cvg_linearP_sum (f := fun E : 'SO(H) => E^*o (Q j))).
  + by move=>a x y; rewrite linearP /= !soE.
  + by apply: norm_bounded_cvg; apply: filtered_row_summable.
  + apply: eq_sum=>t; rewrite /= /sunit_def.
    case: eqP=>[->|_]; first by [].
    by rewrite dualso0 soE.
- rewrite sdlet_sum; by [].
Qed.
End Reindexing.

Section Channels.
Context {I J : choiceType} {H : chsType}.
Variable (K : semType I J H H).

Lemma wp_top : (forall i, sum (K i) \is tpmap) ->
  wp K semantic_top = semantic_top.
Proof.
move=>KT; apply/funext=>i; apply: effect_eq=>rho.
rewrite wp_pairing /semantic_top /= comp_lfun1l.
under eq_sum do rewrite comp_lfun1l.
rewrite -(cvg_linearP_sum (x := K i) (f := fun E : 'SO(H) => \Tr (E rho))).
- by move=>a x y; rewrite !soE linearP.
- exact: summable_cvg.
- by move: (KT i)=>/tpmapP/(_ rho).
Qed.

Lemma wlp_wp (Q : J -> 'FO(H)) : wp K semantic_top = semantic_top ->
  wlp K Q = wp K Q.
Proof.
move=>KT; apply/funext=>i; apply/val_inj.
change (cplmt (wp K (complement Q) i) = (wp K Q i : 'End(H))).
have C j : (complement Q j : 'End(H)) =
    (semantic_top j : 'End(H)) - (Q j : 'End(H)) by [].
rewrite (wp_difference K C) KT /semantic_top /=.
exact: cplmtK.
Qed.

Lemma xp_wp total (Q : J -> 'FO(H)) :
  (forall i, sum (K i) \is tpmap) -> xp total K Q = wp K Q.
Proof. by move=>KT; case: total=>//; apply: wlp_wp; exact: wp_top KT. Qed.
End Channels.
End CQPredicate.


Module ClassicalIndexedLoops.
(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic ClassicalAlgorithmLoops.
Local Notation Hq := 'H[msys]_finset.setT.

Section IndexedLoop.
Variable (x : variable Integer) (c : command).
Variable (next : nat -> store -> store) (action : nat -> store -> 'SO(Hq)).

Fixpoint final_store k n s : store :=
  if n is m.+1 then final_store k.+1 m (next k s) else s.
Fixpoint accumulated_action k n s : 'SO(Hq) :=
  if n is m.+1 then accumulated_action k.+1 m (next k s) :o action k s
  else \:1.

Lemma indexed_loop_execution n k s :
  (s.[x])%M = Posz k ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    execution c t (next j t) (action j t)) ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    ((next j t).[x])%M = Posz j.+1) ->
  execution (While (below x (k + n)) c) s
    (final_store k n s) (accumulated_action k n s).
Proof.
elim: n k s=>[|n IH] k s Hs Hbody Hnext.
- rewrite addn0 /=; apply: RunWhileFalse.
  by rewrite /below /eval /= Hs ltxx.
- have Hrange : (k <= k < k + n.+1)%N.
    by rewrite leqnn addnS ltnS leq_addr.
  have Hb : eval (below x (k + n.+1)) s = true.
    by rewrite /below /eval /= Hs ltz_nat addnS ltnS leq_addr.
  have Ht := Hnext k s Hrange Hs.
  have Htail : execution (While (below x (k.+1 + n)) c)
      (next k s) (final_store k.+1 n (next k s))
      (accumulated_action k.+1 n (next k s)).
    apply: (IH k.+1 (next k s) Ht).
    + move=>j t /andP[kj jn] Hj; apply: Hbody Hj.
      by rewrite (leq_trans (leqnSn k) kj) addnS -addSn jn.
    + move=>j t /andP[kj jn] Hj; apply: Hnext Hj.
      by rewrite (leq_trans (leqnSn k) kj) addnS -addSn jn.
  rewrite addSn -addnS in Htail.
  exact: (RunWhileTrue Hb (Hbody k s Hrange Hs) Htail).
Qed.

Lemma indexed_loop_denote n k s :
  (s.[x])%M = Posz k ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    execution c t (next j t) (action j t)) ->
  (forall j t, (k <= j < k + n)%N -> (t.[x])%M = Posz j ->
    ((next j t).[x])%M = Posz j.+1) ->
  forall m, denote (While (below x (k + n)) c) s m =
    point (final_store k n s) (accumulated_action k n s) m.
Proof. move=>Hs Hb Hn; exact: execution_denote (indexed_loop_execution Hs Hb Hn). Qed.

End IndexedLoop.
Definition one_based_index n (z : int) : option 'I_n :=
  if z is Posz k.+1 then insub k else None.

Definition indexed_gate u n (q : wf_qreg u) (x : variable Integer)
    (U : 'I_n -> 'FU('Ht u)) : command :=
  Conditional
    (EApp (EConst (fun z => isSome (one_based_index n z))) (EVar x))
    (Unitary q (EApp
      (EConst (fun z => if one_based_index n z is Some i then U i else
        (\1 : 'FU('Ht u)))) (EVar x))) Abort.

Lemma one_based_indexE n (i : 'I_n) : one_based_index n (Posz i.+1) = Some i.
Proof. by rewrite /one_based_index valK. Qed.

Lemma indexed_gate_execution u n (q : wf_qreg u) (x : variable Integer)
    (U : 'I_n -> 'FU('Ht u)) (i : 'I_n) s :
  (s.[x])%M = Posz i.+1 ->
  execution (indexed_gate q x U) s s (liftfso (formso (tf2f q q (U i)))).
Proof.
move=>Hs; apply: RunIfTrue.
- by rewrite /eval /= Hs one_based_indexE.
- have D := RunUnitary q
    (EApp (EConst (fun z => if one_based_index n z is Some j then U j else
      (\1 : 'FU('Ht u)))) (EVar x)) s.
  by rewrite /eval /= Hs one_based_indexE in D.
Qed.
End ClassicalIndexedLoops.


Module ClassicalComputations.
(* Maximal computations, classical.pdf Definition 4.1. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.

Record configuration := Configuration {
  residual : option command;
  classical : store;
  quantum : 'End(Hq)
}.

Definition well_formed x := quantum x \is denlf.

Definition live_step (x y : configuration) : Type :=
  match residual x with
  | Some c => (step c (classical x) (quantum x)
      (residual y) (classical y) (quantum y) * (quantum y != 0))%type
  | None => Empty_set
  end.

Definition terminal x : Prop := forall y, live_step x y -> False.

Inductive path : configuration -> configuration -> Type :=
  | PathRefl x : path x x
  | PathStep x y z : live_step x y -> path y z -> path x z.

Definition maximal_path x y := (path x y * terminal y)%type.
Definition finite_computation x y := (well_formed x * maximal_path x y)%type.

Definition infinite_path (f : nat -> configuration) :=
  forall n, live_step (f n) (f n.+1).

Record infinite_computation (x : configuration) := InfiniteComputation {
  infinite_configurations : nat -> configuration;
  infinite_initial : infinite_configurations 0%N = x;
  infinite_density : well_formed x;
  infinite_steps : infinite_path infinite_configurations
}.

Lemma step_zero c s r k s' r' (d : step c s r k s' r') :
  r = 0 -> r' = 0.
Proof.
induction d; move=>Hr; try exact Hr; try exact: IHd Hr.
- by rewrite Hr scaler0.
- by rewrite Hr linear0.
- by rewrite Hr linear0.
- by rewrite Hr linear0.
Qed.

Lemma terminates_zero c s r s' r' (d : terminates c s r s' r') :
  r = 0 -> r' = 0.
Proof.
elim: d=>[c0 s0 r0 s1 r1 st|c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] Hr.
- exact: step_zero st Hr.
- apply: IH; exact: step_zero st Hr.
Qed.

Lemma live_destination_nonzero x y : live_step x y -> quantum y != 0.
Proof. case: x=>[[c|] s r] //=; by case. Qed.

Lemma live_source_nonzero x y : live_step x y -> quantum x != 0.
Proof.
case: x=>[[c|] s r] //= [st nz].
apply/negP=>/eqP Hz; move: nz; rewrite (step_zero st Hz) eqxx.
by [].
Qed.

Lemma live_positive x y : live_step x y -> 0%:VF ⊑ quantum x -> 0%:VF ⊑ quantum y.
Proof.
case: x=>[[c|] s r]; last by case.
move=>[st _] Hr; exact: step_positive st Hr.
Qed.

Lemma live_density_preserved x y : live_step x y -> well_formed x -> well_formed y.
Proof.
case: x=>[[c|] s r]; last by case.
move=>[st _] Hr; exact: step_density st Hr.
Qed.

Lemma live_trace_le x y : live_step x y -> 0%:VF ⊑ quantum x ->
  \Tr (quantum y) <= \Tr (quantum x).
Proof.
case: x=>[[c|] s r]; last by case.
move=>[st _] Hr; exact: step_trace_le st Hr.
Qed.

Lemma path_positive x y : path x y -> 0%:VF ⊑ quantum x -> 0%:VF ⊑ quantum y.
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] Hx; apply: IH; exact: live_positive st Hx.
Qed.

Lemma path_density x y : path x y -> well_formed x -> well_formed y.
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] Hx; apply: IH; exact: live_density_preserved st Hx.
Qed.

Lemma path_trace_le x y : path x y -> 0%:VF ⊑ quantum x ->
  \Tr (quantum y) <= \Tr (quantum x).
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] Hx.
apply: le_trans (live_trace_le st Hx); apply: IH; exact: live_positive st Hx.
Qed.

Lemma path_nonzero x y : path x y -> quantum x != 0 -> quantum y != 0.
Proof.
elim=>[x0 //|x0 x1 x2 st p IH] _; apply: IH; exact: live_destination_nonzero st.
Qed.

Lemma path_nonzero_or_refl x y : path x y -> x = y \/ quantum y != 0.
Proof.
elim=>[x0|x0 x1 x2 st p IH]; first by left.
right; exact: (path_nonzero p (live_destination_nonzero st)).
Qed.

Lemma terminal_none s r : terminal (Configuration None s r).
Proof. by move=>y; case. Qed.

Lemma terminal_abort s r : terminal (Configuration (Some Abort) s r).
Proof. move=>y [st _]; inversion st. Qed.

Lemma terminal_zero k s : terminal (Configuration k s 0).
Proof.
move=>y st; have H := live_source_nonzero st.
by move: H; rewrite /= eqxx.
Qed.

Definition completion x s' r' : Type :=
  match residual x with
  | Some c => terminates c (classical x) (quantum x) s' r'
  | None => (classical x = s') * (quantum x = r')
  end%type.

Lemma path_completion x y (p : path x y) s' r' :
  completion y s' r' -> completion x s' r'.
Proof.
elim: p=>[x0 //|x0 x1 x2 st p IH] H.
have H1 := IH H.
clear p IH H.
case: x0 st=>[[c|] s r] //=.
case: x1 H1=>[[c1|] s1 r1] /= H1 [st nz].
- exact: TerminatesMore st H1.
- case: H1=>Es Er; rewrite -Es -Er; exact: TerminatesDone st.
Qed.

Theorem path_terminates c s r s' r' :
  path (Configuration (Some c) s r) (Configuration None s' r') ->
  terminates c s r s' r'.
Proof.
move=>p; apply: (@path_completion _ _ p s' r'); by split.
Qed.

Theorem terminates_path c s r s' r' : terminates c s r s' r' -> r' != 0 ->
  path (Configuration (Some c) s r) (Configuration None s' r').
Proof.
elim=>[c0 s0 r0 s1 r1 st|c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] nz.
- apply: (@PathStep _ (Configuration None s1 r1)); last exact: PathRefl.
  exact: (st, nz).
- have nz1 : r1 != 0.
    apply/negP=>/eqP Hz; move: nz; rewrite (terminates_zero tail Hz) eqxx.
    by [].
  apply: (@PathStep _ (Configuration (Some c1) s1 r1)); last exact: IH nz.
  exact: (st, nz1).
Qed.

Theorem successful_maximal_iff c s r s' r' :
  inhabited (maximal_path (Configuration (Some c) s r) (Configuration None s' r'))
  <-> inhabited (terminates c s r s' r') /\ r' != 0.
Proof.
split.
- move=>[[p _]]; split; first by constructor; exact: path_terminates p.
  case: (path_nonzero_or_refl p)=>[E|//]; by inversion E.
- move=>[[t] nz]; constructor; split.
  + exact: terminates_path t nz.
  + exact: terminal_none.
Qed.

Lemma infinite_path_density f : infinite_path f -> well_formed (f 0%N) ->
  forall n, well_formed (f n).
Proof.
move=>st H0; elim=>[//|n IH]; exact: live_density_preserved (st n) IH.
Qed.

Lemma infinite_path_positive f : infinite_path f -> 0%:VF ⊑ quantum (f 0%N) ->
  forall n, 0%:VF ⊑ quantum (f n).
Proof.
move=>st H0; elim=>[//|n IH]; exact: live_positive (st n) IH.
Qed.

Lemma infinite_path_trace_step f : infinite_path f -> 0%:VF ⊑ quantum (f 0%N) ->
  forall n, \Tr (quantum (f n.+1)) <= \Tr (quantum (f n)).
Proof.
move=>st H0 n.
exact: (live_trace_le (st n) (infinite_path_positive st H0 n)).
Qed.

Lemma infinite_path_trace_le f : infinite_path f -> 0%:VF ⊑ quantum (f 0%N) ->
  forall n, \Tr (quantum (f n)) <= \Tr (quantum (f 0%N)).
Proof.
move=>st H0; elim=>[//|n IH].
exact: le_trans (infinite_path_trace_step st H0 n) IH.
Qed.

Lemma infinite_not_terminal f : infinite_path f -> forall n, ~ terminal (f n).
Proof. by move=>st n T; exact: T _ (st n). Qed.

Definition true_skip_loop := While (EConst true) Skip.
Definition true_skip_configurations s r n :=
  Configuration (Some (if odd n then Sequence Skip true_skip_loop else true_skip_loop)) s r.

Lemma true_skip_path s r : r != 0 -> infinite_path (true_skip_configurations s r).
Proof.
move=>nz n; rewrite /true_skip_configurations /live_step /=.
case: (odd n)=>/=; split=>//.
- apply: StepSequenceDone; exact: StepSkip.
- exact: (@StepWhileTrue (EConst true) Skip s r erefl).
Qed.

Definition true_skip_infinite s r (Hr : r \is denlf) (nz : r != 0) :
  infinite_computation (Configuration (Some true_skip_loop) s r) :=
  @InfiniteComputation _ (true_skip_configurations s r) erefl Hr (true_skip_path s nz).

Lemma infinite_computation_density x (p : infinite_computation x) n :
  well_formed (infinite_configurations p n).
Proof.
have H0 : well_formed (infinite_configurations p 0%N).
  by rewrite infinite_initial; exact: infinite_density.
exact: (infinite_path_density (infinite_steps p) H0 n).
Qed.

Lemma finite_computation_density x y : finite_computation x y -> well_formed y.
Proof. move=>[Hx [p _]]; exact: path_density p Hx. Qed.

Definition abort_computation s r (Hr : r \is denlf) :
  finite_computation (Configuration (Some Abort) s r) (Configuration (Some Abort) s r) :=
  (Hr, (PathRefl _, @terminal_abort s r)).

Theorem successful_route_iff c s r s' r' :
  inhabited (maximal_path (Configuration (Some c) s r) (Configuration None s' r')) <->
  exists rt, ClassicalOperational.eval_route rt c (s,r) = Some (s',r') /\ r' != 0.
Proof.
rewrite successful_maximal_iff; split.
- move=>[[d] nz]; have [rt Hrt] := ClassicalOperational.terminating_route d.
  by exists rt.
- move=>[rt [Hrt nz]]; split=>//; constructor.
  exact: ClassicalOperational.eval_route_sound Hrt.
Qed.
End ClassicalComputations.


Module ClassicalLocality.
(* Expression supports and store locality for the inherited cqwhile syntax. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalFootprint ClassicalOperational.
Local Notation Hq := 'H[msys]_finset.setT.

Definition remaining_writes (c : option command) :=
  if c is Some c then writes c else [::].

Definition unchanged (xs : seq identifier) (s t : store) :=
  forall u (x : variable u), key x \notin xs -> (s.[x] = t.[x])%M.

Lemma unchanged_refl xs s : unchanged xs s s.
Proof. by move=>u x _. Qed.

Lemma update_unchanged u (x : variable u) v s :
  unchanged [:: key x] s (s.[x <- v])%M.
Proof.
move=>t y; rewrite inE /key xpair_eqE negb_and=>/orP[ne|ne]; symmetry.
- apply: get_set_ne; left; move=>E; move: ne.
  by rewrite /cvtype in E; rewrite E eqxx.
- apply: get_set_ne; right; by rewrite eq_sym.
Qed.

Lemma step_remaining_writes c s r c' s' r' (d : step c s r c' s' r') :
  {subset remaining_writes c' <= writes c}.
Proof.
induction d; rewrite /remaining_writes /=; move=>k; rewrite ?in_nil //.
- by rewrite mem_cat=>->; rewrite orbT.
- rewrite !mem_cat=>/orP[H|H]; apply/orP; [left; exact: IHd | by right].
- by rewrite mem_cat=>->.
- by rewrite mem_cat=>->; rewrite orbT.
- by rewrite mem_cat orbb.
Qed.

Lemma step_unchanged c s r c' s' r' (d : step c s r c' s' r') :
  unchanged (writes c) s s'.
Proof.
induction d; try exact: unchanged_refl.
- exact: update_unchanged.
- exact: update_unchanged.
- exact: update_unchanged.
- move=>u x; rewrite /= mem_cat negb_or=>/andP[Hx _]; exact: IHd.
- move=>u x; rewrite /= mem_cat negb_or=>/andP[Hx _]; exact: IHd.
Qed.

Lemma terminates_unchanged c s r s' r' (d : terminates c s r s' r') :
  unchanged (writes c) s s'.
Proof.
elim: d=>[c0 s0 r0 s1 r1 st|c0 c1 s0 r0 s1 r1 s2 r2 st tail IH].
- exact: step_unchanged st.
- move=>u x Hx; transitivity (s1.[x])%M.
  + exact (@step_unchanged c0 s0 r0 (Some c1) s1 r1 st u x Hx).
  + apply: IH; apply/negP=>H; move/negP: Hx; apply.
    exact (@step_remaining_writes c0 s0 r0 (Some c1) s1 r1 st (key x) H).
Qed.

Lemma route_unchanged rt c s r s' r' :
  eval_route rt c (s,r) = Some (s',r') -> unchanged (writes c) s s'.
Proof. move=>H; exact: terminates_unchanged (eval_route_sound H). Qed.

Lemma terminates_preserves_expression A (e : expression A) c s r s' r' :
  (forall k, expression_variables e k -> k \notin writes c) ->
  terminates c s r s' r' -> eval e s = eval e s'.
Proof.
move=>fresh d; apply: eval_local=>u x Hx.
exact (@terminates_unchanged c s r s' r' d u x (fresh (key x) Hx)).
Qed.
End ClassicalLocality.


Module ClassicalMemorySteps.
(* Classical Table 2 interpreted independently in an arbitrary finite memory.
   See PROOF_NOTES.md for the construction and replay proof. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.


Import CQMemoryInterpretation.
Import ClassicalSemantics.
Section Memory.
Variable S : {set mlab}.
Variable L : finType.
Variable H : L -> chsType.
Variable T V : {set L}.
Variable sub : T :<=: V.
Variable U : 'FGI('H[msys]_S, 'H[H]_T).
Local Notation HW := 'H[H]_V.

Inductive memory_step : command -> store -> 'End(HW) ->
    option command -> store -> 'End(HW) -> Type :=
  | MemorySkip s r : memory_step Skip s r None s r
  | MemoryAssign t (x : variable t) e s r :
      memory_step (Assign x e) s r None (s.[x <- eval e s])%M r
  | MemoryRandom t (x : variable t) p s r i :
      memory_step (Random x p) s r None (s.[x <- i])%M (probability_mass p s i *: r)
  | MemoryMeasure t u (x : variable (QType t)) (q : wf_qreg u)
      (qS : mset q :<=: S) (M : mexpr (eval_qtype t) (eval_qtype u)) s r i :
      memory_step (Measure x q M) s r None (s.[x <- i])%M
        (@measurement_channel S L H T V sub U t u q qS (esem M s) i r)
  | MemoryInitialize u (q : wf_qreg u) (qS : mset q :<=: S) phi s r :
      memory_step (Initialize q phi) s r None s (@initialize_channel S L H T V sub U u q qS (esem phi s) r)
  | MemoryUnitary u (q : wf_qreg u) (qS : mset q :<=: S) A s r :
      memory_step (Unitary q A) s r None s (@unitary_channel S L H T V sub U u q qS (esem A s) r)
  | MemorySequenceDone c1 c2 s r s' r' :
      memory_step c1 s r None s' r' ->
      memory_step (Sequence c1 c2) s r (Some c2) s' r'
  | MemorySequenceMore c1 c2 c1' s r s' r' :
      memory_step c1 s r (Some c1') s' r' ->
      memory_step (Sequence c1 c2) s r (Some (Sequence c1' c2)) s' r'
  | MemoryIfTrue b c1 c0 s r : eval b s = true ->
      memory_step (Conditional b c1 c0) s r (Some c1) s r
  | MemoryIfFalse b c1 c0 s r : eval b s = false ->
      memory_step (Conditional b c1 c0) s r (Some c0) s r
  | MemoryWhileTrue b c s r : eval b s = true ->
      memory_step (While b c) s r (Some (Sequence c (While b c))) s r
  | MemoryWhileFalse b c s r : eval b s = false ->
      memory_step (While b c) s r None s r.


Lemma memory_step_positive c s r k s' r' (d : memory_step c s r k s' r') :
  0%:VF ⊑ r -> 0%:VF ⊑ r'.
Proof.
induction d; move=>Hr.
- exact Hr.
- exact Hr.
- by rewrite scalev_ge0 // ge0_mu.
- exact: cp_ge0 Hr.
- exact: cp_ge0 Hr.
- exact: cp_ge0 Hr.
- exact: IHd Hr.
- exact: IHd Hr.
- exact Hr.
- exact Hr.
- exact Hr.
- exact Hr.
Qed.

Lemma memory_step_trace_le c s r k s' r' (d : memory_step c s r k s' r') :
  0%:VF ⊑ r -> \Tr r' <= \Tr r.
Proof.
induction d; move=>Hr.
- exact: lexx.
- exact: lexx.
- rewrite linearZ /=; apply: ler_piMl; last exact: le1_mu.
  by apply: psdlf_trlf; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- by apply: qo_trlfE; rewrite psdlfE.
- exact: IHd Hr.
- exact: IHd Hr.
- exact: lexx.
- exact: lexx.
- exact: lexx.
- exact: lexx.
Qed.

Lemma memory_step_density c s r k s' r' (d : memory_step c s r k s' r') :
  r \is denlf -> r' \is denlf.
Proof.
move=>/denlfP[Hr Htr]; have Hr0 : 0%:VF ⊑ r by rewrite -psdlfE.
apply/denlfP; split.
- by rewrite psdlfE; exact: memory_step_positive d Hr0.
- exact: le_trans (memory_step_trace_le d Hr0) Htr.
Qed.

End Memory.

Lemma source_step_quantum c s r k s' r' (d : ClassicalSemantics.step c s r k s' r') :
  forall S : {set mlab}, quantum_variables c :<=: S ->
    match k with Some c' => is_true (quantum_variables c' :<=: S) | None => True end.
Proof.
induction d; move=>S Hs; try exact I.
- exact: fintype.subset_trans (finset.subsetUr _ _) Hs.
- move: Hs; rewrite /= finset.subUset=>/andP[H1 H2].
  by rewrite /= finset.subUset (IHd S H1) H2.
- exact: fintype.subset_trans (finset.subsetUl _ _) Hs.
- exact: fintype.subset_trans (finset.subsetUr _ _) Hs.
- by rewrite /= finset.setUid.
Qed.


Section Replay.
Variable S : {set mlab}.
Variable L : finType.
Variable H : L -> chsType.
Variable T V : {set L}.
Variable sub : T :<=: V.
Variable U : 'FGI('H[msys]_S, 'H[H]_T).
Local Notation HW := 'H[H]_V.
Local Notation tr := (@transport S L H T V sub U).

Theorem step_replay c s r k s' r' (d : ClassicalSemantics.step c s r k s' r') :
  quantum_variables c :<=: S ->
  { E : 'SO[msys]_S &
    ((r' = liftfso E r) * (forall sigma : 'End(HW),
    @memory_step S L H T V sub U c s sigma k s' (tr E sigma)))%type }.
Proof.
induction d; move=>Hs.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemorySkip.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryAssign.
- exists (probability_mass p s i *: \:1); split.
  + by rewrite linearZ /= liftfso1 !soE.
  + move=>sigma; rewrite linearZ /= transport1 !soE; exact: MemoryRandom.
- exists (liftso Hs (formso (tf2f q q (esem M s i)))); split.
  + by rewrite liftfso2 measurement_branchE.
  + move=>sigma; rewrite -measurement_channelE; exact: MemoryMeasure.
- exists (liftso Hs (initialso (tv2v q (esem phi s)))); split.
  + by rewrite liftfso2.
  + move=>sigma; rewrite -initialize_channelE; exact: MemoryInitialize.
- exists (liftso Hs (formso (tf2f q q (esem U0 s)))); split.
  + by rewrite liftfso2.
  + move=>sigma; rewrite -unitary_channelE; exact: MemoryUnitary.
- have H1 := fintype.subset_trans (finset.subsetUl _ _) Hs.
  have [E [HE HR]] := IHd H1.
  exists E; split=>// sigma; exact: MemorySequenceDone (HR sigma).
- have H1 := fintype.subset_trans (finset.subsetUl _ _) Hs.
  have [E [HE HR]] := IHd H1.
  exists E; split=>// sigma; exact: MemorySequenceMore (HR sigma).
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryIfTrue e.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryIfFalse e.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryWhileTrue e.
- exists \:1; split; first by rewrite liftfso1 soE.
  move=>sigma; rewrite transport1 soE; exact: MemoryWhileFalse e.
Qed.

End Replay.
End ClassicalMemorySteps.


Module ClassicalBoundedLimits.
(* Order separation and continuous expectations. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalBoundedUnroll.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation row := ({summable cmem -> 'SO(Hq)}).
Definition kernel_chain (f : nat -> kernel) :=
  forall s, nondecreasing_seq (fun k => f k s).

Lemma sem_limit_cvg f : kernel_chain f -> forall s,
  (f k s : row) @[k --> \oo] --> (sem_lim f s : row).
Proof.
move=>inc s.
have C := vdnondecreasing_is_cvgn (@choinorm_ge0_add Hq Hq) (inc s).
change ((fun k => (f k s : row)) @ \oo -->
  ((vdlim (FF := eventually_filter) (fun k => f k s)) : row)).
by rewrite vdlimE.
Qed.
Lemma sem_limit_upper f : kernel_chain f -> forall k, kernel_le (f k) (sem_lim f).
Proof.
move=>inc k s.
exact: (vdnondecreasing_cvg_le (@choinorm_ge0_add Hq Hq) (inc s) k).
Qed.
Lemma sem_limit_least f K : kernel_chain f ->
  (forall k, kernel_le (f k) K) -> kernel_le (sem_lim f) K.
Proof.
move=>inc ub s; rewrite levdEsub.
have C := @sem_limit_cvg f inc s.
have L : limn (fun k => (f k s : row)) ⊑ (K s : row).
  apply: lim_les_nearF; first exact: (cvgP _ C).
  apply: nearW=>k; by rewrite -levdEsub; apply: ub.
by rewrite (cvg_lim (@norm_hausdorff _ _) C) in L.
Qed.

Lemma if_limit b (f g : nat -> kernel) :
  sem_lim (fun k => if_sem b (f k) (g k)) = if_sem b (sem_lim f) (sem_lim g).
Proof.
apply/semtypeP=>s.
change (vdlim (FF := eventually_filter)
  (fun k => if esem b s then f k s else g k s) =
  if esem b s then vdlim (FF := eventually_filter) (fun k => f k s)
  else vdlim (FF := eventually_filter) (fun k => g k s)).
by case: (esem b s).
Qed.
Lemma iter_chain b f : kernel_chain f -> forall r,
  kernel_chain (fun k => while_sem_iter b (f k) r).
Proof.
move=>inc r s j k jk; apply: iter_mono_body=>t; exact: inc t j k jk.
Qed.
Lemma iter_limit b f : kernel_chain f -> forall r,
  sem_lim (fun k => while_sem_iter b (f k) r) = while_sem_iter b (sem_lim f) r.
Proof.
move=>inc; elim=>[|r IH]; first exact: sem_lim_cst.
change (sem_lim (fun k => if_sem b (slet (f k) (while_sem_iter b (f k) r)) skip_sem) =
  if_sem b (slet (sem_lim f) (while_sem_iter b (sem_lim f) r)) skip_sem).
by rewrite if_limit sem_lim_cst (slet_lim inc (@iter_chain b f inc r)) IH.
Qed.
Lemma diagonal_chain b f : kernel_chain f ->
  kernel_chain (fun k => while_sem_iter b (f k) k).
Proof.
move=>inc s j k jk.
apply: (le_trans (@iter_mono_body b _ _ (fun t => inc t j k jk) j s)).
exact: while_sem_iter_homo jk.
Qed.

Lemma while_diagonal_limit b f : kernel_chain f ->
  sem_lim (fun k => while_sem_iter b (f k) k) = while_sem b (sem_lim f).
Proof.
move=>inc; apply: kernel_le_anti.
- apply: sem_limit_least; first exact: diagonal_chain inc.
  move=>k s; apply: (le_trans (@iter_mono_body b _ _ (sem_limit_upper inc k) k s)).
  exact: while_sem_ub.
- move=>s; apply: while_sem_least=>r.
  rewrite -(@iter_limit b f inc r).
  apply: sem_limit_least; first exact: (@iter_chain b f inc r).
  move=>k t.
  apply: (le_trans (y := while_sem_iter b (f (maxn k r)) (maxn k r) t)).
  + apply: (le_trans (@iter_mono_body b _ _ (fun u => inc u k (maxn k r) (leq_maxl k r)) r t)).
    exact: while_sem_iter_homo (leq_maxr k r).
  + exact: (@sem_limit_upper
      (fun j => while_sem_iter b (f j) j)
      (@diagonal_chain b f inc) (maxn k r) t).
Qed.

Theorem bounded_unroll_limit c :
  sem_lim (fun k => denote (bounded_unroll k c)) = denote c.
Proof.
elim: c=>[| |u x e|u x prob|u v x q M|u q phi|u q U|
  c IH d IHd|b c IH d IHd|b c IH].
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- exact: sem_lim_cst.
- change (sem_lim (fun k => slet (denote (bounded_unroll k c)) (denote (bounded_unroll k d))) =
    slet (denote c) (denote d)).
  by rewrite (slet_lim (bounded_unroll_chain c) (bounded_unroll_chain d)) IH IHd.
- change (sem_lim (fun k => if_sem b (denote (bounded_unroll k c)) (denote (bounded_unroll k d))) =
    if_sem b (denote c) (denote d)).
  by rewrite if_limit IH IHd.
- have E : (fun k => denote (bounded_unroll k (While b c))) =
      (fun k => while_sem_iter b (denote (bounded_unroll k c)) k).
    by apply/funext=>k; rewrite /= denote_unroll.
  by rewrite E (while_diagonal_limit b (bounded_unroll_chain c)) IH.
Qed.

Theorem bounded_unroll_cvg c s :
  (denote (bounded_unroll k c) s : row) @[k --> \oo] --> (denote c s : row).
Proof.
have C := @sem_limit_cvg (fun k => denote (bounded_unroll k c))
  (bounded_unroll_chain c) s.
by rewrite bounded_unroll_limit in C.
Qed.
Theorem bounded_unroll_suffix_limit c (K : kernel) :
  sem_lim (fun k => slet (denote (bounded_unroll k c)) K) = slet (denote c) K.
Proof. by rewrite (slet_liml K (bounded_unroll_chain c)) bounded_unroll_limit. Qed.
End ClassicalBoundedLimits.


Module ClassicalAlgorithmSemantics.
(* Deterministic execution certificates for concrete algorithm loops.
   Each constructor follows the language semantics. Certificates describe
   finite runs, and the theorem below identifies their full unbounded-loop
   denotation, without a truncation or a program-correctness assumption. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalDeterministic CQPredicate CQAssertion.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma execution_channel c s t F : execution c s t F -> F \is cptp.
Proof.
move=>D; elim: c s t F / D=>[s|t x e s|u q phi s|u q ue s|
  c1 c2 s t u F G D1 IH1 D2 IH2|
  b c1 c0 s t F Eb D IH|b c1 c0 s t F Eb D IH|
  b c s Eb|b c s t u F G Eb D1 IH1 D2 IH2].
1-4,8: exact: is_cptp.
2,3: exact: IH.
all: by rewrite (QChannel_BuildE IH1) (QChannel_BuildE IH2) is_cptp.
Qed.

Lemma execution_wp c s t F (Q : store -> 'FO(Hq)) :
  execution c s t F ->
  (wp (denote c) Q s : 'End(Hq)) = F^*o (Q t).
Proof.
move=>D; rewrite wpE (fin_supp_sum (S := [fset t]%fset)).
- move=>j; rewrite inE=>/negPf Ejt.
  by rewrite (execution_denote D) /point Ejt dualso0 soE.
- by rewrite psum1 (execution_denote D) /point eqxx.
Qed.

Lemma execution_pre total c s t (F : 'QC(Hq)) (Q : store -> 'FO(Hq)) :
  execution c s t F ->
  (xp total (denote c) Q s : 'End(Hq)) = F^*o (Q t).
Proof.
move=>D; case: total; first exact: execution_wp D.
change (cplmt (wp (denote c) (complement Q) s) = F^*o (Q t)).
by rewrite (execution_wp _ D) cplmt_dualC /complement /= cplmtK.
Qed.

Lemma formso_initial (U : chsType) (A : 'End(U)) v :
  formso A :o initialso v = initialso (A v).
Proof.
apply/superopP=>rho; rewrite comp_soE !initialsoE linearZ /= formsoE.
by rewrite -outp_complV -outp_comprV.
Qed.

Lemma register_unitary_comp u (q : wf_qreg u) (V U : 'End('Ht u)) :
  liftfso (formso (tf2f q q V)) :o liftfso (formso (tf2f q q U)) =
  liftfso (formso (tf2f q q (V \o U))).
Proof. by rewrite -liftfso_comp formso_comp tf2f_comp. Qed.

Lemma register_unitary_power u (q : wf_qreg u) (U : 'End('Ht u)) n :
  ClassicalAlgorithmLoops.superop_power (liftfso (formso (tf2f q q U))) n =
  liftfso (formso (tf2f q q (U ^+ n))).
Proof.
elim: n=>[|n IH].
- by rewrite /= expr0 tf2f1 formso1 liftfso1.
- by rewrite /= IH register_unitary_comp exprSr.
Qed.
End ClassicalAlgorithmSemantics.


Module CQKernelLinearity.
(* Absolute-series linearity of cq kernels. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import CQAssertion CQExpectation CQPredicate CQMixtureExpectation.
Section Kernels.
Context {I J A : choiceType} {H : chsType}.
Variable K : semType I J H H.

Definition weighted_input (w : A -> C) (d : A -> @CQState.state I H) a :
  {summable I -> 'End(H)} := w a *: (d a : {summable I -> 'End(H)}).

Definition weighted_output (w : A -> C) (d : A -> @CQState.state I H) a :
  {summable J -> 'End(H)} :=
  w a *: (CQKernel.apply K (d a) : {summable J -> 'End(H)}).

Lemma weighted_norm_bound w d a :
  `|weighted_output w d a| <= `|weighted_input w d a|.
Proof.
rewrite /weighted_output /weighted_input !normrZ.
apply: ler_wpM2l; first exact: normr_ge0.
exact: CQKernel.apply_l1_bound.
Qed.

Lemma weighted_output_summable w d : summable (weighted_input w d) ->
  summable (weighted_output w d).
Proof.
move=>Hs; pose x := Summable.build Hs.
apply: psum_ubounded_summable; exists `|x|=>F.
apply: (le_trans _ (psum_norm_ler_norm x F)).
by apply: ler_sum=>a _; apply: weighted_norm_bound.
Qed.

Lemma pairing_sum {L : choiceType} (Q : L -> 'FO(H))
  (x : {summable A -> {summable L -> 'End(H)}}) :
  pairing Q (sum x) = sum (fun a => pairing Q (x a)).
Proof.
have B : exists k : C, 0 < k /\
  forall y : {summable L -> 'End(H)}, `|pairing Q y| <= k * `|y|.
  exists 1; split=>// y; rewrite mul1r; exact: pairing_bound.
rewrite (summable_linear_sumG (f := pairing Q) x B).
by [].
Qed.

Theorem apply_weighted_sum w d (d0 : @CQState.state I H) :
  summable (weighted_input w d) ->
  (d0 : {summable I -> 'End(H)}) = sum (weighted_input w d) ->
  (CQKernel.apply K d0 : {summable J -> 'End(H)}) =
    sum (weighted_output w d).
Proof.
move=>Hs Hd; apply: CQStateExpectation.pairing_ext=>Q.
rewrite -expect_pairing -expect_wp expect_pairing Hd.
rewrite (pairing_sum Q (Summable.build (weighted_output_summable Hs))).
rewrite (pairing_sum (wp K Q) (Summable.build Hs)).
apply: eq_sum=>a.
by rewrite /weighted_input /weighted_output !linearZ /= -!expect_pairing expect_wp.
Qed.

Theorem apply_mix (w : Distr A) (d : A -> @CQState.state I H) :
  CQKernel.apply K (CQStateMixture.mix w d) =
    CQStateMixture.mix w (fun a => CQKernel.apply K (d a)).
Proof.
apply/(proj2 (CQStateExpectation.state_eq_iff_expect _ _))=>Q.
rewrite -expect_wp !CQMixtureExpectation.expect_mix.
by apply: eq_sum=>a; rewrite expect_wp.
Qed.
End Kernels.
End CQKernelLinearity.


Module CQPrimitive.
(* Weakest preconditions for arbitrary classical-quantum kernels.
   See PROOF_NOTES.md for the infinite-sum and duality arguments. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Import CQAssertion CQPredicate ClassicalLanguage.
Local Notation Hq := 'H[msys]_finset.setT.
Implicit Types Q : cmem -> 'FO(Hq).

Lemma assign_pre total t (x : variable t) e Q s :
  (xp total (denote (Assign x e)) Q s : 'End(Hq)) =
    (Q (s.[x <- eval e s])%M : 'End(Hq)).
Proof. by rewrite /= /assign_sem xp_sunit dualso1 soE. Qed.

Lemma initial_pre total t (q : wf_qreg t) phi Q s :
  (xp total (denote (Initialize q phi)) Q s : 'End(Hq)) =
    (liftfso (initialso (tv2v q (esem phi s))))^*o (Q s).
Proof. by rewrite /= /initial_sem xp_sunit. Qed.

Lemma unitary_pre total t (q : wf_qreg t) U Q s :
  (xp total (denote (Unitary q U)) Q s : 'End(Hq)) =
    (liftfso (formso (tf2f q q (esem U s))))^*o (Q s).
Proof. by rewrite /= /unitary_sem xp_sunit. Qed.


Lemma random_complete t (x : variable t) p s :
  sum (denote (Random x p) s) \is tpmap.
Proof.
rewrite /= /random_sem /sdlet /= sdlet_sum /sdistr sdistr_sum
  probability_normalized scale1r.
exact: is_tpmap.
Qed.

Lemma random_pre total t (x : variable t) p Q s :
  (xp total (denote (Random x p)) Q s : 'End(Hq)) =
    sum (fun v => probability_mass p s v *: (Q (s.[x <- v])%M : 'End(Hq))).
Proof.
rewrite (xp_wp (K := denote (Random x p)) total Q (random_complete x p))
  /denote /random_sem wp_sdlet.
apply: eq_sum=>v.
by rewrite /sdistr /= /sdistr_def linearZ /= dualso1 !soE.
Qed.

Lemma measurement_complete t u (x : variable (QType t)) (q : wf_qreg u) M s :
  sum (denote (Measure x q M) s) \is tpmap.
Proof.
rewrite /= /measure_kernel /measure_sem /sdlet /= sdlet_sum smeas_sum elemso_sum.
exact: is_tpmap.
Qed.

Lemma measurement_pre total t u (x : variable (QType t)) (q : wf_qreg u) M Q s :
  (xp total (denote (Measure x q M)) Q s : 'End(Hq)) =
    \sum_v ((liftf_fun (tm2m q q (esem M s)) v)^A \o
      (Q (s.[x <- v])%M : 'End(Hq)) \o (liftf_fun (tm2m q q (esem M s)) v)).
Proof.
rewrite (xp_wp (K := denote (Measure x q M)) total Q (measurement_complete x q M))
  /denote /measure_kernel /measure_sem wp_sdlet fin_dom_sum.
apply: eq_bigr=>v _.
by rewrite /smeas /= /smeas_def dualso_formE.
Qed.
End CQPrimitive.


Module ClassicalOperationalApproximants.
(* Bounded operational completions, Lemma 4.2. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
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


Module ClassicalOperationalRouteCost.
(* Exact operational transition counts, classical.pdf Lemma 4.2.
   See PROOF_NOTES.md for the argument. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalOperational ClassicalComputations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Local Notation Hq := 'H[msys]_finset.setT.

Fixpoint route_cost (r : route) : nat :=
  match r with
  | TR_cond1 r | TR_cond2 r | TR_while1 r => (route_cost r).+1
  | TR_seqc r1 r2 => (route_cost r1 + route_cost r2)%N
  | _ => 1%N
  end.

Lemma route_cost_positive r : (0 < route_cost r)%N.
Proof. by elim: r=>//= r1 H1 r2 H2; rewrite addn_gt0 H1. Qed.

Inductive counted_terminates :
    nat -> command -> store -> 'End(Hq) -> store -> 'End(Hq) -> Type :=
  | CountedDone c s r s' r' : step c s r None s' r' ->
      counted_terminates 1 c s r s' r'
  | CountedMore n c c' s r s1 r1 s' r' :
      step c s r (Some c') s1 r1 ->
      counted_terminates n c' s1 r1 s' r' ->
      counted_terminates n.+1 c s r s' r'.

Lemma counted_erase n c s r s' r' :
  counted_terminates n c s r s' r' -> terminates c s r s' r'.
Proof.
elim=>[c0 s0 r0 s1 r1 st|n0 c0 c1 s0 r0 s1 r1 s2 r2 st tail IH].
- exact: TerminatesDone st.
- exact: TerminatesMore st IH.
Qed.

Lemma counted_positive n c s r s' r' :
  counted_terminates n c s r s' r' -> (0 < n)%N.
Proof. by case. Qed.

Lemma counted_sequence n1 n2 c1 c2 s r m q s' r' :
  counted_terminates n1 c1 s r m q ->
  counted_terminates n2 c2 m q s' r' ->
  counted_terminates (n1 + n2) (Sequence c1 c2) s r s' r'.
Proof.
move=>d1; elim: d1=>[c s0 r0 s1 r1 st|
  n c c' s0 r0 s1 r1 s2 r2 st tail IH] d2.
- rewrite add1n; exact: (@CountedMore n2 (Sequence c c2) c2 s0 r0 s1 r1 s' r'
    (@StepSequenceDone c c2 s0 r0 s1 r1 st) d2).
- rewrite addSn; exact: (@CountedMore (n + n2) (Sequence c c2) (Sequence c' c2)
    s0 r0 s1 r1 s' r' (@StepSequenceMore c c2 c' s0 r0 s1 r1 st) (IH d2)).
Qed.

Theorem eval_route_counted rt c s r s' r' :
  eval_route rt c (s,r) = Some (s',r') ->
  counted_terminates (route_cost rt) c s r s' r'.
Proof.
elim: rt c s r s' r'=>[| |t v|rt IH|rt IH| |rt IH|r1 IH1 r2 IH2| | |t v]
  c s r s' r'.
- case: c=>//= [= <- <-]; apply: CountedDone; exact: StepSkip.
- case: c=>//= t x e; move=>[= <- <-]; apply: CountedDone; exact: StepAssign.
- case: c=>//= u x p; case: asboolP=>//= E; move=>[= <- <-].
  apply: CountedDone; exact: StepRandom.
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@CountedMore _ (Conditional b c1 c0) c1 s r s r s' r'
    (@StepIfTrue b c1 c0 s r Eb) (IH c1 s r s' r' H)).
- case: c=>//= b c1 c0; case Eb: (eval b s)=>//= H.
  exact: (@CountedMore _ (Conditional b c1 c0) c0 s r s r s' r'
    (@StepIfFalse b c1 c0 s r Eb) (IH c0 s r s' r' H)).
- case: c=>//= b c0; case Eb: (eval b s)=>//=; move=>[= <- <-].
  exact: (@CountedDone _ _ _ _ _ (@StepWhileFalse b c0 s r Eb)).
- case: c=>//= b c0; case Eb: (eval b s)=>//= H.
  exact: (@CountedMore _ (While b c0) (Sequence c0 (While b c0)) s r s r s' r'
    (@StepWhileTrue b c0 s r Eb) (IH _ s r s' r' H)).
- case: c=>//= c1 c2; case E: (eval_route r1 c1 (s,r))=>[[m q]|] //= H.
  exact: (@counted_sequence _ _ c1 c2 s r m q s' r'
    (IH1 _ _ _ _ _ E) (IH2 _ _ _ _ _ H)).
- case: c=>//= u q phi; move=>[= <- <-]; apply: CountedDone; exact: StepInitialize.
- case: c=>//= u q U; move=>[= <- <-]; apply: CountedDone; exact: StepUnitary.
- case: c=>//= u z x q M; case: asboolP=>//= E; move=>[= <- <-].
  apply: CountedDone; exact: StepMeasure.
Qed.

Lemma step_route_cost_complete c s r c' s' r'
    (d : step c s r c' s' r') :
  forall rt o,
    (match c' with None => Some (s',r') | Some k => eval_route rt k (s',r') end) = Some o ->
    exists rr, eval_route rr c (s,r) = Some o /\
      route_cost rr = (match c' with None => 0 | Some _ => route_cost rt end).+1.
Proof.
induction d; move=>rt o H.
- by exists TR_skip.
- by exists TR_assign.
- exists (TR_random i); split=>//; rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- exists (TR_measure i); split=>//; rewrite /=; case: asboolP=>[E|//].
  by rewrite (eq_irrelevance E erefl).
- by exists TR_initial.
- by exists TR_unitary.
- have [r1 [Hr1 Hcost]] := IHd TR_skip (s',r') erefl.
  exists (TR_seqc r1 rt); split; first by rewrite /= Hr1.
  by rewrite /= Hcost add1n.
- case: rt H=>//= r1 r2.
  case E: (eval_route r1 c1' (s',r'))=>[[m q]|] //= H.
  have [r0 [Hr0 Hcost]] := IHd r1 (m,q) E.
  exists (TR_seqc r0 r2); split; first by rewrite /= Hr0.
  by rewrite /= Hcost addSn.
- exists (TR_cond1 rt); split=>//; by rewrite /= e.
- exists (TR_cond2 rt); split=>//; by rewrite /= e.
- exists (TR_while1 rt); split=>//; by rewrite /= e.
- exists TR_while0; split=>//; by rewrite /= e.
Qed.

Theorem counted_terminating_route n c s r s' r' :
  counted_terminates n c s r s' r' ->
  exists rt, eval_route rt c (s,r) = Some (s',r') /\ route_cost rt = n.
Proof.
elim=>[c0 s0 r0 s1 r1 st|
  n0 c0 c1 s0 r0 s1 r1 s2 r2 st tail [rt [Hrt Hcost]]].
- exact: step_route_cost_complete st TR_skip (s1,r1) erefl.
- have [rr [Hrr Hrrcost]] := @step_route_cost_complete _ _ _ _ _ _ st rt (s2,r2) Hrt.
  by exists rr; split=>//; rewrite Hrrcost Hcost.
Qed.

Theorem successful_route_exact_iff c s r s' r' n :
  (exists rt, eval_route rt c (s,r) = Some (s',r') /\ route_cost rt = n) <->
  inhabited (counted_terminates n c s r s' r').
Proof.
split.
- move=>[rt [Hrt <-]]; constructor; exact: eval_route_counted Hrt.
- move=>[d]; exact: counted_terminating_route d.
Qed.

Theorem successful_route_bounded_iff c s r s' r' n :
  (exists rt, eval_route rt c (s,r) = Some (s',r') /\ (route_cost rt <= n)%N) <->
  exists k, (k <= n)%N /\ inhabited (counted_terminates k c s r s' r').
Proof.
split.
- move=>[rt [Hrt Hcost]]; exists (route_cost rt); split=>//.
  constructor; exact: eval_route_counted Hrt.
- move=>[k [Hk [d]]]; have [rt [Hrt Hcost]] := counted_terminating_route d.
  by exists rt; split=>//; rewrite Hcost.
Qed.
End ClassicalOperationalRouteCost.


Module ClassicalOperationalCompletions.
(* Bounded operational completions, Lemma 4.2. See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope classical_set_scope.
Import ClassicalSemantics.
Import ClassicalLanguage ClassicalOperational ClassicalOperationalRouteCost ClassicalOperationalApproximants CQState.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation state := (@CQState.state cmem Hq).

Section Completions.
Variable c : command.
Variable s : store.
Variable rho : 'FD(Hq).

Lemma selected_route_nonzero (p : pred route) rt t (x : 'End(Hq)) :
  p rt -> eval_route rt c (s,(rho : 'End(Hq))) = Some (t,x) -> x != 0 ->
  suppf (selected_family c s rho p) rt.
Proof.
move=>Hp He Hx.
rewrite /suppf /selected_family /= /selected_term Hp /opfun He.
apply/negP=>/eqP Hz.
have Z := congr1 (fun f : {summable store -> 'End(Hq)} => `|f|) Hz.
move: Z; rewrite sunit_normE normr0=>/eqP.
by rewrite normr_eq0 (negbTE Hx).
Qed.

Theorem selected_outcomes_countable (p : pred route) :
  countable [set o : store * 'End(Hq) |
    exists rt, p rt /\ eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0].
Proof.
pose out rt := odflt (s,(0 : 'End(Hq))) (eval_route rt c (s,(rho : 'End(Hq)))).
have Sub : [set o : store * 'End(Hq) |
    exists rt, p rt /\ eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0]
    `<=` out @` suppf (selected_family c s rho p).
  move=>[t x] [rt [Hp [He Hx]]]; exists rt.
  - exact: selected_route_nonzero Hp He Hx.
  - by rewrite /out He.
apply: (sub_countable (subset_card_le Sub)).
apply: (sub_countable (card_image_le out _)).
exact: selected_routes_countable.
Qed.

Theorem exact_completions_countable n :
  countable [set o : store * 'End(Hq) |
    inhabited (counted_terminates n c s rho o.1 o.2) /\ o.2 != 0].
Proof.
apply: (sub_countable (B := [set o : store * 'End(Hq) |
    exists rt, (route_cost rt == n) /\
      eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0])).
- apply: subset_card_le.
  move=>o Ho; case: o Ho=>t x /= [[d] Hx].
  have [rt [He Hcost]] := counted_terminating_route d.
  by exists rt; split; [apply/eqP | split].
- exact: selected_outcomes_countable.
Qed.

Theorem bounded_completions_countable n :
  countable [set o : store * 'End(Hq) |
    (exists k, (k <= n)%N /\ inhabited (counted_terminates k c s rho o.1 o.2)) /\ o.2 != 0].
Proof.
apply: (sub_countable (B := [set o : store * 'End(Hq) |
    exists rt, (route_cost rt <= n)%N /\
      eval_route rt c (s,(rho : 'End(Hq))) = Some o /\ o.2 != 0])).
- apply: subset_card_le.
  move=>o Ho; case: o Ho=>t x /= [[k [Hk [d]]] Hx].
  have [rt [He Hcost]] := counted_terminating_route d.
  exists rt; split; [by rewrite Hcost | by split].
- exact: selected_outcomes_countable.
Qed.

Definition bounded_completion n : state := completion_state c s rho route_cost n.

Theorem bounded_completionE n m : bounded_completion n m =
  sum (fun rt => if (route_cost rt <= n)%N then opfun c s rho rt m else 0).
Proof.
rewrite /bounded_completion /completion_state selected_stateE.
by apply: eq_sum=>rt; rewrite /within ltnS.
Qed.

Theorem bounded_completion_zero : bounded_completion 0 = bottom.
Proof.
apply/vdistrP=>m; rewrite bounded_completionE bottomE.
under eq_sum do rewrite leqn0 (gtn_eqF (route_cost_positive _)).
exact: summable_sum_cst0.
Qed.

Theorem bounded_completion_chain : nondecreasing_seq bounded_completion.
Proof. exact: completion_state_chain. Qed.

Theorem bounded_completion_countable n : countable (suppf (bounded_completion n)).
Proof. exact: support_countable. Qed.

Theorem bounded_completion_mass n : mass (bounded_completion n) <= \Tr rho.
Proof. exact: selected_mass_bound. Qed.

Theorem bounded_completion_cvg :
  ((fun n => (bounded_completion n : {summable store -> 'End(Hq)})) @ \oo --> opsum c s rho)%classic.
Proof. exact: completion_state_cvg. Qed.

Theorem bounded_completion_sup :
  chain_sup bounded_completion = CQKernel.apply (denote c) (point s rho).
Proof. exact: completion_state_denote. Qed.

Theorem bounded_completion_upper n :
  bounded_completion n ⊑ CQKernel.apply (denote c) (point s rho).
Proof.
rewrite -bounded_completion_sup.
exact: (@chain_sup_upper cmem Hq bounded_completion bounded_completion_chain n).
Qed.

Theorem bounded_completion_least (d : state) :
  (forall n, bounded_completion n ⊑ d) ->
  CQKernel.apply (denote c) (point s rho) ⊑ d.
Proof.
rewrite -bounded_completion_sup.
exact: (@chain_sup_least cmem Hq bounded_completion d bounded_completion_chain).
Qed.

End Completions.
End ClassicalOperationalCompletions.


Module ClassicalOperationalCountedPaths.
(* Nonzero, step-counted computation paths for classical.pdf Lemma 4.2.
   See PROOF_NOTES.md. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalOperational ClassicalComputations
  ClassicalOperationalRouteCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Import ClassicalSemantics.
Local Notation Hq := 'H[msys]_finset.setT.

Inductive counted_path : nat -> configuration -> configuration -> Type :=
  | CountedPathRefl x : counted_path 0 x x
  | CountedPathStep n x y z : live_step x y -> counted_path n y z ->
      counted_path n.+1 x z.

Definition counted_maximal_path n x y :=
  (counted_path n x y * terminal y)%type.

Lemma counted_path_erase n x y : counted_path n x y -> path x y.
Proof.
elim=>[x0|n0 x0 x1 x2 st p IH]; first exact: PathRefl.
exact: PathStep st IH.
Qed.

Definition counted_completion n x s' r' : Type :=
  match residual x with
  | Some c => counted_terminates n c (classical x) (quantum x) s' r'
  | None => ((n = 0%N) * ((classical x = s') * (quantum x = r')))%type
  end.

Lemma counted_path_completion n x y (p : counted_path n x y) :
  forall k s' r', counted_completion k y s' r' ->
    counted_completion (n + k)%N x s' r'.
Proof.
elim: p=>[x0|n0 x0 x1 x2 st p IH] k s' r' H.
- by rewrite add0n.
- have H1 := IH k s' r' H.
  clear p IH H.
  case: x0 st=>[[c|] s r]; last by case.
  case: x1 H1=>[[c1|] s1 r1] /= H1 [st nz].
  + rewrite /counted_completion /= addSn; exact: CountedMore st H1.
  + case: H1=>Hk [Es Er].
    rewrite /counted_completion /= addSn Hk -Es -Er.
    exact: CountedDone st.
Qed.

Theorem counted_path_terminates n c s r s' r' :
  counted_path n (Configuration (Some c) s r) (Configuration None s' r') ->
  counted_terminates n c s r s' r'.
Proof.
move=>p.
have H := @counted_path_completion _ _ _ p 0%N s' r' (erefl, (erefl, erefl)).
by rewrite addn0 in H.
Qed.

Theorem counted_terminates_path n c s r s' r' :
  counted_terminates n c s r s' r' -> r' != 0 ->
  counted_path n (Configuration (Some c) s r) (Configuration None s' r').
Proof.
elim=>[c0 s0 r0 s1 r1 st|
  n0 c0 c1 s0 r0 s1 r1 s2 r2 st tail IH] nz.
- apply: (@CountedPathStep 0 _ (Configuration None s1 r1));
    last exact: CountedPathRefl.
  exact: (st, nz).
- have nz1 : r1 != 0.
    apply/negP=>/eqP Hz; move: nz.
    by rewrite (terminates_zero (counted_erase tail) Hz) eqxx.
  apply: (@CountedPathStep n0 _ (Configuration (Some c1) s1 r1));
    last exact: IH nz.
  exact: (st, nz1).
Qed.

Theorem successful_counted_maximal_iff n c s r s' r' :
  inhabited (counted_maximal_path n
    (Configuration (Some c) s r) (Configuration None s' r')) <->
  inhabited (counted_terminates n c s r s' r') /\ r' != 0.
Proof.
split.
- move=>[[p _]]; split; first by constructor; exact: counted_path_terminates p.
  case: (path_nonzero_or_refl (counted_path_erase p))=>[E|//].
  by inversion E.
- move=>[[d] nz]; constructor; split.
  + exact: counted_terminates_path d nz.
  + exact: terminal_none.
Qed.

Theorem successful_counted_route_iff n c s r s' r' :
  inhabited (counted_maximal_path n
    (Configuration (Some c) s r) (Configuration None s' r')) <->
  exists rt, eval_route rt c (s,r) = Some (s',r') /\
    route_cost rt = n /\ r' != 0.
Proof.
rewrite successful_counted_maximal_iff -successful_route_exact_iff; split.
- by move=>[[rt [Hrt Hcost]] nz]; exists rt.
- by move=>[rt [Hrt [Hcost nz]]]; split=>//; exists rt.
Qed.
End ClassicalOperationalCountedPaths.
