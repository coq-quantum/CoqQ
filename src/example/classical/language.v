(* Classical: language. See README.md and PROOF_NOTES.md. *)
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
Module ClassicalLanguage.
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


End ClassicalLanguage.


Module ClassicalFootprint.
(* Expression supports and store locality for the inherited cqwhile syntax. *)


Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Import Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

(* A lambda's support includes the support of every body instance.
   Finiteness can be required separately by a program well-formedness rule. *)
Import ClassicalLanguage.

Definition agree_on (xs : set identifier) (s t : store) :=
  forall u (x : variable u), xs (key x) -> (s.[x] = t.[x])%M.

Lemma eval_local A (e : expression A) s t :
  agree_on (expression_variables e) s t -> eval e s = eval e t.
Proof.
elim: e=>[u x|B a|B C f IHf a IHa|B C f IHf] /= Hst.
- apply: Hst; by [].
- by [].
- have Ef : eval f s = eval f t.
    apply: IHf=>u x Hx; apply: Hst; by left.
  have Ea : eval a s = eval a t.
    apply: IHa=>u x Hx; apply: Hst; by right.
  by rewrite /eval /= -/(eval f s) -/(eval f t) -/(eval a s) -/(eval a t) Ef Ea.
- apply/funext=>a; apply: (IHf a)=>u x Hx.
  apply: Hst; by exists a.
Qed.

Lemma agree_on_refl xs s : agree_on xs s s.
Proof. by move=>u x _. Qed.

Lemma agree_on_sym xs s t : agree_on xs s t -> agree_on xs t s.
Proof. by move=>Hst u x Hx; symmetry; apply: Hst. Qed.
End ClassicalFootprint.
