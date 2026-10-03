(* Classical-quantum language of Feng and Ying (2021), Sections 3.1 and 4.
   The kernel combinators and unbounded loop construction are reused from
   CoqQ's veri_QEC/cqwhile.v, including its classical types, higher-order
   expressions and state-dependent quantum operations. *)
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

Module ClassicalLanguage.

Definition sort := cType.
Definition Boolean : sort := QType QBool.
Definition Integer : sort := CInt.
Definition store_type (t : sort) := t.
Definition value := eval_ctype.
Definition variable := cvar.
Definition store := cmem.
Definition expression := expr_.
Definition EVar {t} (x : variable t) : expression (value t) := var_ x.
Definition EConst {A} (a : A) : expression A := cst_ a.
Definition EApp {A B} (f : expression (A -> B)) (a : expression A) := app_ f a.
Definition ELam {A B} (f : A -> expression B) := lam_ f.
Definition translate_expr {A} (e : expression A) := e.
Definition eval {A} (e : expression A) (s : store) := esem e s.
Definition bool_expr := bexpr.

Definition identifier := (cType * (String.string * String.string))%type.
Definition key {t} (x : variable t) : identifier := (t, cvname x).
(* HOAS lambdas may read a different variable for every argument, so their
   complete syntactic support is a classical set, not necessarily finite. *)
Fixpoint expression_variables {A} (e : expression A) : set identifier :=
  match e with
  | var_ t x => set1 (key x)
  | cst_ A a => set0
  | app_ A B f a => setU (expression_variables f) (expression_variables a)
  | lam_ A B f => fun x => exists a, expression_variables (f a) x
  end.

Lemma eval_var t (x : variable t) s : eval (EVar x) s = (s.[x])%M.
Proof. by []. Qed.
Lemma eval_const A (a : A) s : eval (EConst a) s = a.
Proof. by []. Qed.
Lemma eval_app A B (f : expression (A -> B)) a s :
  eval (EApp f a) s = eval f s (eval a s).
Proof. by []. Qed.
Lemma eval_lam A B (f : A -> expression B) s :
  eval (ELam f) s = fun a => eval (f a) s.
Proof. by []. Qed.

(* Unlike Distr, random assignments use normalized distributions at every
   input store. The distribution expression can depend on classical data. *)
Record probability (t : sort) := Probability {
  probability_expression : dexpr (value t);
  probability_normalized : forall s, sum (esem probability_expression s) = 1
}.
Definition probability_mass t (p : probability t) s :=
  esem (probability_expression p) s.

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

Inductive command :=
  | Skip
  | Abort
  | Assign {t} of variable t & expression (value t)
  | Random {t} of variable t & probability t
  | Measure {t u : qType} of variable (QType t) & wf_qreg u & mexpr (eval_qtype t) (eval_qtype u)
  | Initialize {u} of wf_qreg u & sexpr (eval_qtype u)
  | Unitary {u} of wf_qreg u & uexpr (eval_qtype u)
  | Sequence of command & command
  | Conditional of bool_expr & command & command
  | While of bool_expr & command.

Definition zero_state (u : qType) : 'NS('Ht u) :=
  [NS of t2tv (witness (eval_qtype u))].

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

Fixpoint writes (c : command) : seq identifier :=
  match c with
  | Assign t x e => [:: key x]
  | Random t x p => [:: key x]
  | Measure t u x q M => [:: key x]
  | Sequence c1 c2 | Conditional _ c1 c2 => writes c1 ++ writes c2
  | While _ c => writes c
  | _ => [::]
  end.

Fixpoint variables (c : command) : set identifier :=
  match c with
  | Assign t x e => setU (set1 (key x)) (expression_variables e)
  | Random t x p => setU (set1 (key x)) (expression_variables (probability_expression p))
  | Measure t u x q M => setU (set1 (key x)) (expression_variables M)
  | Initialize u q phi => expression_variables phi
  | Unitary u q U => expression_variables U
  | Sequence c1 c2 => setU (variables c1) (variables c2)
  | Conditional b c1 c2 => setU (expression_variables b) (setU (variables c1) (variables c2))
  | While b c => setU (expression_variables b) (variables c)
  | _ => set0
  end.

Fixpoint quantum_variables (c : command) : {set mlab} :=
  match c with
  | Measure t u x q M => mset q
  | Initialize u q _ | Unitary u q _ => mset q
  | Sequence c1 c2 | Conditional _ c1 c2 =>
      (quantum_variables c1 :|: quantum_variables c2)%SET
  | While _ c => quantum_variables c
  | _ => finset.set0
  end.

Fixpoint unroll (b : bool_expr) (c : command) n :=
  match n with
  | 0%N => Abort
  | n.+1 => Conditional b (Sequence c (unroll b c n)) Skip
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

End ClassicalLanguage.
