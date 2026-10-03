(* Distributive: language. See README.md and PROOF_NOTES.md. *)
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
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From Stdlib Require Import String.
From quantum.example.classical Require Import language state assertion semantics hoare auxiliary.
Module DistributedLanguage.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

Module CL := ClassicalLanguage.
Notation expression := CL.expression.
Notation eval := CL.eval.
Definition classical_name := CL.identifier.
Definition name_of {t} (x : CL.variable t) : classical_name := CL.key x.
Definition expression_reads {T} (e : expression T) :=
  CL.expression_variables e.
Definition constant_expression {T} (x : T) := CL.EConst x.
Definition variable_expression {t} (x : CL.variable t) := CL.EVar x.

(* The full cqwhile expression language is shared with the classical paper.
   Source programs explicitly require finite read footprints below; arbitrary
   higher-order expressions are not assumed to have finite support. *)
Inductive atom : Type :=
| ASkip
| AAbort
| AAssign {t} of CL.variable t & expression (CL.value t)
| ARandom {t} of CL.variable t & CL.probability t
| AInitial {t} of wf_qreg t & sexpr (eval_qtype t)
| AUnitary {t} of wf_qreg t & uexpr (eval_qtype t)
| AMeasure {t u : qType} (x : CL.variable (QType t)) (q : wf_qreg u)
    of mexpr (eval_qtype t) (eval_qtype u).

Definition atom_changes (a : atom) : {fset classical_name} :=
  match a with
  | AAssign _ x _ => [fset name_of x]
  | ARandom _ x _ => [fset name_of x]
  | AMeasure _ _ x _ _ => [fset name_of x]
  | _ => fset0
  end.

Definition atom_reads (a : atom) : set classical_name :=
  match a with
  | AAssign _ x e => [set name_of x] `|` expression_reads e
  | ARandom _ x p => [set name_of x] `|` expression_reads (CL.probability_expression p)
  | AInitial _ _ phi => expression_reads phi
  | AUnitary _ _ ue => expression_reads ue
  | AMeasure _ _ x _ me => [set name_of x] `|` expression_reads me
  | _ => set0
  end%classic.

Definition atom_quantum (a : atom) : {set mlab} :=
  match a with
  | AInitial _ q _ => mset q
  | AUnitary _ q _ => mset q
  | AMeasure _ _ _ q _ => mset q
  | _ => finset.set0
  end.

Definition exclusive n (g : 'I_n -> expression bool) :=
  forall m i j, eval (g i) m -> eval (g j) m -> i = j.

(* A finite family preserves branch identity, even when two bodies coincide.
   Exclusivity is a well-formedness condition, not a priority convention. *)
Inductive statement : Type :=
| Finished (* residual control marker E; excluded from source statements *)
| Atomic of atom
| Sequence of statement & statement
| Alternative n of ('I_n -> expression bool) & ('I_n -> statement)
| Repetition n of ('I_n -> expression bool) & ('I_n -> statement).

Fixpoint statement_wf (s : statement) : Prop :=
  match s with
  | Finished => False
  | Atomic _ => True
  | Sequence s t => statement_wf s /\ statement_wf t
  | Alternative n g b | Repetition n g b =>
      exclusive g /\ forall i, statement_wf (b i)
  end.

Fixpoint statement_changes (s : statement) : {fset classical_name} :=
  match s with
  | Finished => fset0
  | Atomic a => atom_changes a
  | Sequence s t => statement_changes s `|` statement_changes t
  | Alternative n _ b | Repetition n _ b =>
      \big[fsetU/fset0]_(i : 'I_n) statement_changes (b i)
  end.

Fixpoint statement_reads (s : statement) : set classical_name :=
  match s with
  | Finished => set0
  | Atomic a => atom_reads a
  | Sequence s t => statement_reads s `|` statement_reads t
  | Alternative n g b | Repetition n g b =>
      \bigcup_(i : 'I_n) (expression_reads (g i) `|` statement_reads (b i))
  end%classic.

Fixpoint statement_quantum (s : statement) : {set mlab} :=
  match s with
  | Finished => finset.set0
  | Atomic a => atom_quantum a
  | Sequence s t => statement_quantum s :|: statement_quantum t
  | Alternative n _ b | Repetition n _ b =>
      \bigcup_(i : 'I_n) statement_quantum (b i)
  end%SET.

Inductive communication : Type :=
| Input {t} of string & CL.variable t
| Output {t} of string & expression (CL.value t).

Definition channel (a : communication) :=
  match a with Input _ c _ | Output _ c _ => c end.
Definition communication_changes (a : communication) : {fset classical_name} :=
  match a with Input _ _ x => [fset name_of x] | _ => fset0 end.
Definition communication_reads (a : communication) : set classical_name :=
  match a with
  | Input _ _ x => [set name_of x]
  | Output _ _ e => expression_reads e
  end%classic.

(* Matching includes equality of the transmitted and received type. *)
Inductive matches : communication -> communication -> atom -> Prop :=
| MatchInput t c (x : CL.variable t) e :
    matches (Input c x) (Output c e) (AAssign x e)
| MatchOutput t c (x : CL.variable t) e :
    matches (Output c e) (Input c x) (AAssign x e).

Lemma matches_symmetric a b effect : matches a b effect -> matches b a effect.
Proof. by case=>t c x e; constructor. Qed.

Record process := Process {
  initialization : statement;
  branch_count : nat;
  process_guard : 'I_branch_count -> expression bool;
  process_io : 'I_branch_count -> communication;
  process_body : 'I_branch_count -> statement
}.
Arguments process_guard p _ : clear implicits.
Arguments process_io p _ : clear implicits.
Arguments process_body p _ : clear implicits.

Definition process_wf (p : process) :=
  statement_wf (initialization p) /\ exclusive (process_guard p) /\
  forall j, statement_wf (process_body p j).
Definition process_changes (p : process) :=
  statement_changes (initialization p) `|`
  \big[fsetU/fset0]_(j : 'I_(branch_count p))
    (communication_changes (process_io p j) `|` statement_changes (process_body p j)).
Definition process_reads (p : process) :=
  (statement_reads (initialization p) `|`
  \bigcup_(j : 'I_(branch_count p))
    (expression_reads (process_guard p j) `|`
     communication_reads (process_io p j) `|` statement_reads (process_body p j)))%classic.
Definition process_quantum (p : process) : {set mlab} :=
  (statement_quantum (initialization p) :|:
  \bigcup_(j : 'I_(branch_count p)) statement_quantum (process_body p j))%SET.
Definition process_channels (p : process) :=
  [fset channel (process_io p j) | j : 'I_(branch_count p)].

Definition pairwise_private n (p : 'I_n -> process) :=
  forall i j, i != j ->
    (forall x, process_reads (p i) x -> x \notin process_changes (p j)) /\
    ((process_quantum (p i) :&: process_quantum (p j)) == finset.set0)%SET.
Definition point_to_point n (p : 'I_n -> process) :=
  forall i j k, i != j -> i != k -> j != k ->
    [disjoint process_channels (p i) &
      (process_channels (p j) `&` process_channels (p k))].

Record program := Program {
  process_count : nat;
  processes : 'I_process_count -> process;
  processes_nonempty : (0 < process_count)%N;
  processes_wf : forall i, process_wf (processes i);
  processes_finite_reads : forall i, finite_set (process_reads (processes i));
  processes_private : pairwise_private processes;
  processes_point_to_point : point_to_point processes
}.
Arguments processes p _ : clear implicits.

Definition term n (p : 'I_n -> process) (m : cmem) :=
  [forall i, [forall j, ~~ eval (process_guard (p i) j) m]].

Lemma no_enabled_alternative n (g : 'I_n -> expression bool) m :
  [forall i, ~~ eval (g i) m] -> forall i, eval (g i) m = false.
Proof. by move=>/forallP H i; apply/negbTE/H. Qed.
End DistributedLanguage.


Module DistributedFootprint.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedLanguage.
Local Open Scope fset_scope.

Lemma atom_changes_reads a x : x \in atom_changes a -> atom_reads a x.
Proof.
case: a=>[| |t y e|t y p|t q phi|t q U|t u y q M] /=;
  rewrite ?inE //; move=>/eqP->; by left.
Qed.

Lemma statement_changes_reads s : forall x,
  x \in statement_changes s -> statement_reads s x.
Proof.
elim: s=>[|a|s IHs t IHt|n g b IHb|n g b IHb] x /=.
- by rewrite inE.
- exact: atom_changes_reads.
- rewrite in_fsetU=>/orP[Hx|Hx].
  + left; exact: IHs.
  + right; exact: IHt.
- move=>/bigfcupP[i _ Hi]; exists i=>//; right; exact: IHb i x Hi.
- move=>/bigfcupP[i _ Hi]; exists i=>//; right; exact: IHb i x Hi.
Qed.

Lemma communication_changes_reads a x :
  x \in communication_changes a -> communication_reads a x.
Proof. by case: a=>t c y /=; rewrite inE // =>/eqP->. Qed.

Lemma process_changes_reads p x : x \in process_changes p -> process_reads p x.
Proof.
rewrite /process_changes in_fsetU=>/orP[Hx|Hx].
- left; exact: statement_changes_reads Hx.
- right; move/bigfcupP: Hx=>[j _]; rewrite in_fsetU=>/orP[Hx|Hx].
  + exists j=>//; left; right; exact: communication_changes_reads Hx.
  + exists j=>//; right; exact: statement_changes_reads Hx.
Qed.

Lemma private_changes_disjoint n (p : 'I_n -> process) : pairwise_private p ->
  forall i j, i != j -> [disjoint process_changes (p i) & process_changes (p j)].
Proof.
move=>Hprivate i j Hij; apply/fdisjointP=>x Hx.
exact: (proj1 (Hprivate i j Hij) x (process_changes_reads Hx)).
Qed.
End DistributedFootprint.


Module DistributedCommunication.
(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ClassicalSemantics.
Import DistributedLanguage.
Definition cast_expression (t u : CL.sort) (E : t = u)
    (e : expression (CL.value t)) : expression (CL.value u) :=
  match E in _ = u return expression (CL.value u) with erefl => e end.

Definition communication_effect (a b : communication) : option atom :=
  match a, b with
  | Input t c x, Output u d e =>
      if asbool (c = d) then
        match asboolP (u = t) with
        | ReflectT E => Some (AAssign x (cast_expression E e))
        | _ => None
        end
      else None
  | Output u d e, Input t c x =>
      if asbool (c = d) then
        match asboolP (u = t) with
        | ReflectT E => Some (AAssign x (cast_expression E e))
        | _ => None
        end
      else None
  | _, _ => None
  end.

Lemma matching_effect a b effect : matches a b effect ->
  communication_effect a b = Some effect.
Proof.
case=>t c x e; rewrite /communication_effect asboolT;
  case: (asboolP (t = t))=>[E|//]; by rewrite ?(eq_irrelevance E erefl).
Qed.

Lemma effect_matches a b effect : communication_effect a b = Some effect ->
  matches a b effect.
Proof.
case: a=>t c x; case: b=>u d e //=.
- case: (asboolP (c = d))=>// Ec; subst d.
  case: (asboolP (u = t))=>// Et; subst t.
  rewrite /cast_expression /=; move=>[= <-]; constructor.
- case: (asboolP (d = c))=>// Ec; subst c.
  case: (asboolP (t = u))=>// Et; subst u.
  rewrite /cast_expression /=; move=>[= <-]; constructor.
Qed.


End DistributedCommunication.
