(* Expression supports and store locality for the inherited cqwhile syntax. *)
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
From quantum.example.classical Require Import state language.

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
Module ClassicalFootprint.
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
