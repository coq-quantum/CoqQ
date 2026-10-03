From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import interval_inference.
From mathcomp Require Import -(notations) sesquilinear.
Require Import mcextra mcaextra notation mxpred extnum ctopology svd mxnorm.
Require Import hermitian inhabited prodvect.
From quantum Require Import tensor.
Require Import quantum orthomodular.
Require Import hspace hspace_extra inhabited summable qreg qmem cqwhile qtype.
From quantum.dirac Require Import hstensor.
From Stdlib Require Import Program.Equality String.
Require Import preliminary.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Local Notation R := hermitian.R.
Local Notation C := hermitian.C.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Declare Scope sqsyn_scope.
Declare Scope psyn_scope.
Declare Scope asyn_scope.

Delimit Scope sqsyn_scope with SQ.
Delimit Scope psyn_scope with P.
Delimit Scope asyn_scope with A.

(* Syntax of expression substitution, sqexpression *)

Definition cast_expr T1 T2 (eqT : T1 = T2) (e : expr_ (eval_ctype T1)) :=
  let: erefl in _ = T2 := eqT return expr_ (eval_ctype T2) in e.

Lemma cast_expr_id T (eqT : T = T) (e : expr_ (eval_ctype T)) :
  cast_expr eqT e = e.
Proof. by rewrite eq_axiomK. Qed. 

Fixpoint expr_subst T (e : expr_ T) {Tc} (x : cvar Tc) (s : expr_ (eval_ctype Tc)) : expr_ T :=
  match e in expr_ T return expr_ T with
  | var_ T y => if (cvname y == cvname x) then
                  match Tc =P T with
                  | ReflectT E => cast_expr E s
                  | _ => var_ y
                  end
                else var_ y
  | cst_ _ e => cst_ e
  | app_ _ _ e1 e2 => app_ (expr_subst e1 x s) (expr_subst e2 x s)
  | lam_ _ _ e => lam_ (fun i => expr_subst (e i) x s)
  end.

Notation "e .[ x <- s ]" := (expr_subst e%X x s%X) : xsyn_scope.

Lemma esem_subst T (e : expr_ T) Tc (x : cvar Tc) s (m : cmem) :
  esem (e.[x <- s])%X m = esem e (m.[ x <- esem s m])%M.
Proof.
dependent induction e => //.
- rewrite /= eq_sym /cvtype/=/orapp; case: eqP.
    move=>E; move: E {+}E=>/esym E; case: _ / E x s=>x s E.
    by rewrite eq_axiomK/=; case: eqP.
  by case: eqP.
- by rewrite /= IHe1 IHe2.
- by rewrite /=; apply/funext=>i; rewrite H.
Qed.

(* Section 3.1 Expressions *)
Inductive SQExp :=
  | SQ_bool (b : bexpr)
  | SQ_sqrt2
  | SQ_div2 (s : SQExp) (t : expr_ nat)
  | SQ_add (s1 s2 : SQExp)
  | SQ_opp (s : SQExp)
  | SQ_mul (s1 s2 : SQExp).

Fixpoint SQExp_subst (e : SQExp) {Tc} (x : cvar Tc) (s : expr_ (eval_ctype Tc)) :=
  match e with
  | SQ_bool b => SQ_bool (expr_subst b x s)
  | SQ_sqrt2 => SQ_sqrt2
  | SQ_div2 e t => SQ_div2 (SQExp_subst e x s) (expr_subst t x s)
  | SQ_add e1 e2 => SQ_add (SQExp_subst e1 x s) (SQExp_subst e2 x s)
  | SQ_opp e => SQ_opp (SQExp_subst e x s)
  | SQ_mul e1 e2 => SQ_mul (SQExp_subst e1 x s) (SQExp_subst e2 x s)
  end.

Bind Scope sqsyn_scope with SQExp.
Local Open Scope ring_scope.

HB.lock Definition sq_0 := SQ_add (SQ_bool false%:CS) (SQ_bool true%:CS).
HB.lock Definition sq_1 := SQ_bool false%:CS.
HB.lock Definition sq_N1 := SQ_bool true%:CS.
HB.lock Definition sq_sq2V := SQ_div2 SQ_sqrt2 1%:CS.
HB.lock Definition sq_bool01 b := 
  SQ_div2 (SQ_add (SQ_bool false%:CS) (SQ_bool (~~b)%X)) 1%:CS.

(* HB.lock Definition sq_0 := SQ_base 0%:CS 0%:CS 0%:CS. *)
(* HB.lock Definition sq_N1 := SQ_base 0%:CS (-1)%:CS 0%:CS. *)
(* HB.lock Definition sq_sq2VN := SQ_base 1%:CS 0%:CS (-1)%:CS. *)

Notation "0" := sq_0 : sqsyn_scope.
Notation "1" := sq_1 : sqsyn_scope.
Notation "- 1" := sq_N1 : sqsyn_scope.
Notation "1/√2" := sq_sq2V : sqsyn_scope.
Notation "- 1/√2" := (SQ_opp sq_sq2V) : sqsyn_scope.
Notation "s + t" := (SQ_add s%SQ t%SQ) : sqsyn_scope.
Notation "- t" := (SQ_opp t%SQ) : sqsyn_scope.
Notation "s - t" := (SQ_add s%SQ (SQ_opp t%SQ)) : sqsyn_scope.
Notation "s * t" := (SQ_mul s%SQ t%SQ) : sqsyn_scope.
Notation "e .[ x <- s ]" := (SQExp_subst e%SQ x s%X) : sqsyn_scope.

(*  field of 1/2^n (a + b * sqrt(2))*)
Section SQExpSem.

Fixpoint sqsem (s : SQExp) (m : cmem) : R :=
  match s with
  | SQ_bool e => (-1) ^+ (esem e m)
  | SQ_sqrt2 => Num.sqrt 2
  | SQ_div2 e t => sqsem e m / (2 ^+ (esem t m))
  | SQ_add s1 s2 => sqsem s1 m + sqsem s2 m
  | SQ_opp s => - sqsem s m
  | SQ_mul s1 s2 => sqsem s1 m * sqsem s2 m
  end.

Lemma sqsem_subst (e : SQExp) {Tc} (x : cvar Tc) s (m : cmem) :
  sqsem (e.[x <- s])%SQ m = sqsem e (m.[ x <- esem s m])%M.
Proof.
elim: e=>/=[?||?->?|?->?->|?->|?->?->]//;
by rewrite /= !esem_subst.
Qed.

Lemma sq_0E m : sqsem 0 m = 0.
Proof. by rewrite sq_0.unlock /= expr0 expr1 subrr. Qed.

Lemma sq_1E m : sqsem 1 m = 1.
Proof. by rewrite sq_1.unlock /= expr0. Qed.

Lemma sq_N1E m : sqsem (-1)%SQ m = - 1.
Proof. by rewrite /= sq_N1.unlock /= expr1. Qed.

Lemma sq_sq2VE m : sqsem 1/√2 m = (Num.sqrt 2)^-1.
Proof.
rewrite sq_sq2V.unlock /= expr1 -{2}(sqr_sqrtr (a := 2))//.
by rewrite expr2 invfM mulrA mulfV// mul1r.
Qed.

Lemma sq_sq2VNE m : sqsem (-1/√2)%SQ m = - (Num.sqrt 2)^-1.
Proof. by rewrite /= sq_sq2VE. Qed.

Lemma sq_bool01E b m : sqsem (sq_bool01 b) m = (esem b m)%:R.
Proof.
rewrite sq_bool01.unlock /=; case: (esem b m);
by rewrite expr0 expr1 ?subrr ?mul0r// mulfV.
Qed.

Definition sq_semE := (sq_0E, sq_1E, sq_N1E, sq_sq2VE, sq_sq2VNE, sq_bool01E).

End SQExpSem.

Notation Hq := 'H[msys]_finset.setT.

Notation "e1 ==> e2" := (app2_ (cst_ implb) e1 e2)  : xsyn_scope.
Notation "e ^-1"  := (app_ (cst_ GRing.inv) e%X)     : xsyn_scope.
Notation "e1 / e2"  := 
  (app2_ (cst_ *%R) e1 (app_ (cst_ GRing.inv) e2%X)) : xsyn_scope.
Notation "e1 ^+ e2" := (app2_ (cst_ (@GRing.exp _)) e1 e2) : xsyn_scope.
Notation "e1 *+ e2" := (app2_ (cst_ (@GRing.natmul _)) e1 e2) : xsyn_scope.
Notation "e1 *~ e2" := (app2_ (cst_ (@intmul _)) e1 e2) : xsyn_scope.
Notation "e '%:~R'" := (app_ (cst_ (@intmul _ 1)) e) : xsyn_scope.
Notation "e1 *: e2" := (app2_ (cst_ *:%R) e1 e2) : xsyn_scope.
Notation "e1 \o e2" := (app2_ (cst_ (@comp_lfun _ _ _ _)) e1 e2) : xsyn_scope.
Notation "e %:C" := (app_ (cst_ (@real_complex _)) e) : xsyn_scope.

Section ProgramLogic.
Variable (n : nat).

(* Syntax *)

Inductive PExp :=
  | P_X (i : 'I_n.+1)
  | P_Y (i : 'I_n.+1)
  | P_Z (i : 'I_n.+1)
  | P_Scale (a : SQExp) (P : PExp)
  | P_Add (P1 P2 : PExp)
  | P_Mul (P1 P2 : PExp).

Bind Scope psyn_scope with PExp.
(* Definition 3.2 *)
Inductive AExp :=
  | A_BExp (b : bexpr)
  | A_PExp (P : PExp)
  | A_neg (A : AExp)
  | A_and (A1 A2 : AExp)
  | A_or (A1 A2 : AExp)
  | A_imply (A1 A2 : AExp).

Coercion A_BExp : bexpr >-> AExp.
Coercion A_PExp : PExp >-> AExp.

Bind Scope asyn_scope with AExp.

Inductive Gate1 := | G_X | G_Y | G_Z | G_H | G_S | G_T.
Inductive Gate2 := | G_CNOT | G_CZ | G_iSWAP.

Inductive program := 
  | skip
  | assign {t} of cvar t & expr_ (eval_ctype t) (* deterministic assignment *)
  | cond       of bexpr & program & program (* if condition *)
  | while      of bexpr & program        (* while condition *)
  | seqc       of program & program 
  | initial    of 'I_n.+1 (* initialization *)
  | unitary1   of 'I_n.+1 & Gate1 (* unitary transformation *)
  | unitary2   of 'I_n.+1 & 'I_n.+1 & Gate2 (* unitary transformation *)
  | measure of cvar Bool & PExp. (* quantum measurement *)

Notation "P + Q" := (P_Add P%P Q%P) : psyn_scope.
Notation "a *: P" := (P_Scale a%SQ P%P) : psyn_scope.
Notation "P * Q" := (P_Mul P%P Q%P) : psyn_scope.

Notation "~~ A" := (A_neg A%A) : asyn_scope.
Notation "A && B" := (A_and A%A B%A) : asyn_scope.
Notation "A || B" := (A_or A%A B%A) : asyn_scope.
Notation "A ==> B" := (A_imply A%A B%A) : asyn_scope.

(* substitution *)

(* substitution rule of classical assignment *)
Fixpoint PExp_subst (P : PExp) {Tc} (x : cvar Tc) (s : expr_ (eval_ctype Tc)) :=
  match P with
  | P_X i => P_X i
  | P_Y i => P_Y i
  | P_Z i => P_Z i
  | P_Scale a P => (a.[x <- s] *: (PExp_subst P x s))%P
  | P_Add P1 P2 => ((PExp_subst P1 x s) + (PExp_subst P2 x s))%P
  | P_Mul P1 P2 => ((PExp_subst P1 x s) * (PExp_subst P2 x s))%P
  end.
Notation "P .[ x <- s ]" := (PExp_subst P%P x s%X) : psyn_scope.

(* for single-qubit gates *)
Fixpoint PExp_subst1 (P : PExp) j (Xs Ys Zs : PExp) :=
  match P with
  | P_X i => if i == j then Xs else P_X i
  | P_Y i => if i == j then Ys else P_Y i
  | P_Z i => if i == j then Zs else P_Z i
  | P_Scale a P => P_Scale a (PExp_subst1 P j Xs Ys Zs)
  | P_Add P1 P2 => P_Add (PExp_subst1 P1 j Xs Ys Zs) 
                         (PExp_subst1 P2 j Xs Ys Zs)
  | P_Mul P1 P2 => P_Mul (PExp_subst1 P1 j Xs Ys Zs) 
                         (PExp_subst1 P2 j Xs Ys Zs)
  end.

Notation "P .[ j ; Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]" := 
    (PExp_subst1 P%P j Xs%P Ys%P Zs%P) 
    (at level 1, left associativity, 
    format "P .[ j ;  Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]"): psyn_scope.

(* for two-qubit gates *)
Fixpoint PExp_subst2 (P : PExp) i j (Xi Yi Zi Xj Yj Zj : PExp) :=
  match P with
  | P_X k => if k == i then Xi else if k == j then Xj else P_X k
  | P_Y k => if k == i then Yi else if k == j then Yj else P_Y k
  | P_Z k => if k == i then Zi else if k == j then Zj else P_Z k
  | P_Scale a P => P_Scale a (PExp_subst2 P i j Xi Yi Zi Xj Yj Zj)
  | P_Add P1 P2 => P_Add (PExp_subst2 P1 i j Xi Yi Zi Xj Yj Zj)
                         (PExp_subst2 P2 i j Xi Yi Zi Xj Yj Zj)
  | P_Mul P1 P2 => P_Mul (PExp_subst2 P1 i j Xi Yi Zi Xj Yj Zj)
                         (PExp_subst2 P2 i j Xi Yi Zi Xj Yj Zj)
  end.
Notation "P .[ i , j ; Xi '<-Xi,' Yi '<-Yi,' Zi '<-Zi,' Xj '<-Xj,' Yj '<-Yj,' Zj '<-Zj' ]" := 
    (PExp_subst2 P%P i j Xi%P Yi%P Zi%P Xj%P Yj%P Zj%P) 
    (at level 1, left associativity, 
    format "P .[ i ,  j ;  Xi '<-Xi,'  Yi '<-Yi,'  Zi '<-Zi,'  Xj '<-Xj,'  Yj '<-Yj,'  Zj '<-Zj' ]") : psyn_scope.

(* Substitution rule for unitaries*)

(* X: X -> X   Y -> -Y   Z -> -Z *)
Definition PXsubst i (P : PExp) := 
  (P.[i; (P_X i)<-X, (-1 *: (P_Y i))<-Y, (-1 *: (P_Z i))<-Z])%P.
Definition PYsubst i (P : PExp) := 
  (P.[ i; (-1 *: (P_X i))<-X, (P_Y i)<-Y, (-1 *: (P_Z i))<-Z])%P.
Definition PZsubst i (P : PExp) := 
  (P.[ i; (-1 *: (P_X i))<-X, (-1 *: (P_Y i))<-Y, (P_Z i)<-Z])%P.
Definition PHsubst i (P : PExp) := 
  (P.[ i; (P_Z i)<-X, (-1 *: (P_Y i))<-Y, (P_X i)<-Z])%P.
Definition PSsubst i (P : PExp) := 
  (P.[ i; (-1 *: (P_Y i))<-X, (P_X i)<-Y, (P_Z i)<-Z])%P.  
Definition PTsubst i (P : PExp) := 
  (P.[ i; (1/√2 *: (P_X i) + (-1/√2) *: (P_Y i))<-X, 
  (1/√2 *: (P_X i) + 1/√2 *: (P_Y i))<-Y, (P_Z i)<-Z])%P.
Definition PCNOTsubst i j (P : PExp) := 
  (P.[ i, j; ((P_X i) * (P_X j))<-Xi, ((P_Y i) * (P_X j))<-Yi, (P_Z i)<-Zi,
  (P_X j)<-Xj, ((P_Z i) * (P_Y j))<-Yj, ((P_Z i) * (P_Z j))<-Zj])%P.
Definition PCZsubst i j (P : PExp) := 
  (P.[ i, j; ((P_X i) * (P_Z j))<-Xi, ((P_Y i) * (P_Z j))<-Yi, (P_Z i)<-Zi,
  ((P_Z i) * (P_X j))<-Xj, ((P_Z i) * (P_Y j))<-Yj, (P_Z j)<-Zj])%P.
Definition PiSWAPsubst i j (P : PExp) := 
  (P.[ i, j; ((P_Z i) * (P_Y j))<-Xi, ((-1 *: (P_Z i)) * (P_X j))<-Yi, (P_Z j)<-Zi,
  ((P_Y i) * (P_Z j))<-Xj, ((-1 *: (P_X i)) * (P_Z j))<-Yj, (P_Z i)<-Zj])%P.

Fixpoint AExp_subst (A : AExp) {Tc} (x : cvar Tc) (s : expr_ (eval_ctype Tc)) :=
  match A with
  | A_BExp b => A_BExp (expr_subst b x s)
  | A_PExp P => A_PExp (PExp_subst P x s)
  | A_neg A => A_neg (AExp_subst A x s)
  | A_and A1 A2 => A_and (AExp_subst A1 x s) (AExp_subst A2 x s)
  | A_or A1 A2 => A_or (AExp_subst A1 x s) (AExp_subst A2 x s)
  | A_imply A1 A2 => A_imply (AExp_subst A1 x s) (AExp_subst A2 x s)
  end.
Notation "A .[ x <- s ]" := (AExp_subst A%P x s%X) : asyn_scope.

(* for single-qubit gates *)
Fixpoint AExp_subst1 (A : AExp) j (Xs Ys Zs : PExp) :=
  match A with
  | A_BExp b => A_BExp b
  | A_PExp P => A_PExp (PExp_subst1 P j Xs Ys Zs)
  | A_neg A => A_neg (AExp_subst1 A j Xs Ys Zs)
  | A_and A1 A2   => A_and   (AExp_subst1 A1 j Xs Ys Zs) (AExp_subst1 A2 j Xs Ys Zs)
  | A_or A1 A2    => A_or    (AExp_subst1 A1 j Xs Ys Zs) (AExp_subst1 A2 j Xs Ys Zs)
  | A_imply A1 A2 => A_imply (AExp_subst1 A1 j Xs Ys Zs) (AExp_subst1 A2 j Xs Ys Zs)
  end.
Notation "A .[ j ; Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]" := 
    (AExp_subst1 A%A j Xs%P Ys%P Zs%P) 
    (at level 1, left associativity, 
    format "A .[ j ;  Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]"): asyn_scope.

(* for two-qubit gates *)
Fixpoint AExp_subst2 (A : AExp) i j (Xi Yi Zi Xj Yj Zj : PExp) :=
  match A with
  | A_BExp b => A_BExp b
  | A_PExp P => A_PExp (PExp_subst2 P i j Xi Yi Zi Xj Yj Zj)
  | A_neg A => A_neg (AExp_subst2 A i j Xi Yi Zi Xj Yj Zj)
  | A_and A1 A2   => A_and   (AExp_subst2 A1 i j Xi Yi Zi Xj Yj Zj)
                             (AExp_subst2 A2 i j Xi Yi Zi Xj Yj Zj)
  | A_or A1 A2    => A_or    (AExp_subst2 A1 i j Xi Yi Zi Xj Yj Zj)
                             (AExp_subst2 A2 i j Xi Yi Zi Xj Yj Zj)
  | A_imply A1 A2 => A_imply (AExp_subst2 A1 i j Xi Yi Zi Xj Yj Zj)
                             (AExp_subst2 A2 i j Xi Yi Zi Xj Yj Zj)
  end.
Notation "A .[ i , j ; Xi '<-Xi,' Yi '<-Yi,' Zi '<-Zi,' Xj '<-Xj,' Yj '<-Yj,' Zj '<-Zj' ]" := 
    (AExp_subst2 A%A i j Xi%P Yi%P Zi%P Xj%P Yj%P Zj%P) 
    (at level 1, left associativity, 
    format "A .[ i ,  j ;  Xi '<-Xi,'  Yi '<-Yi,'  Zi '<-Zi,'  Xj '<-Xj,'  Yj '<-Yj,'  Zj '<-Zj' ]") : asyn_scope.

Definition AXsubst i (A : AExp) := 
  (A.[i; (P_X i)<-X, (-1 *: (P_Y i))<-Y, (-1 *: (P_Z i))<-Z])%A.
Definition AYsubst i (A : AExp) := 
  (A.[ i; (-1 *: (P_X i))<-X, (P_Y i)<-Y, (-1 *: (P_Z i))<-Z])%A.
Definition AZsubst i (A : AExp) := 
  (A.[ i; (-1 *: (P_X i))<-X, (-1 *: (P_Y i))<-Y, (P_Z i)<-Z])%A.
Definition AHsubst i (A : AExp) := 
  (A.[ i; (P_Z i)<-X, (-1 *: (P_Y i))<-Y, (P_X i)<-Z])%A.
Definition ASsubst i (A : AExp) := 
  (A.[ i; (-1 *: (P_Y i))<-X, (P_X i)<-Y, (P_Z i)<-Z])%A.  
Definition ATsubst i (A : AExp) := 
  (A.[ i; (1/√2 *: (P_X i) + (-1/√2) *: (P_Y i))<-X, 
  (1/√2 *: (P_X i) + 1/√2 *: (P_Y i))<-Y, (P_Z i)<-Z])%A.
Definition ACNOTsubst i j (A : AExp) := 
  (A.[ i, j; ((P_X i) * (P_X j))<-Xi, ((P_Y i) * (P_X j))<-Yi, (P_Z i)<-Zi,
  (P_X j)<-Xj, ((P_Z i) * (P_Y j))<-Yj, ((P_Z i) * (P_Z j))<-Zj])%A.
Definition ACZsubst i j (A : AExp) := 
  (A.[ i, j; ((P_X i) * (P_Z j))<-Xi, ((P_Y i) * (P_Z j))<-Yi, (P_Z i)<-Zi,
  ((P_Z i) * (P_X j))<-Xj, ((P_Z i) * (P_Y j))<-Yj, (P_Z j)<-Zj])%A.
Definition AiSWAPsubst i j (A : AExp) := 
  (A.[ i, j; ((P_Z i) * (P_Y j))<-Xi, ((-1 *: (P_Z i)) * (P_X j))<-Yi, (P_Z j)<-Zi,
  ((P_Y i) * (P_Z j))<-Xj, ((-1 *: (P_X i)) * (P_Z j))<-Yj, (P_Z i)<-Zj])%A.

Definition AInitsubst i (A : AExp) :=
  ((P_Z i && A) || ((-1 *: (P_Z i))%P && (AXsubst i A)))%A.

(* Semantics of expressions*)
Section PASem.
Local Open Scope hspace_scope.
Local Open Scope reg_scope.

Variable (q : 'QReg[Bool.[n.+1]]).

(* Section 3.1 *)
Fixpoint Pfsem (P : PExp) (m : cmem) : 'F[msys]_finset.setT :=
  match P with
  | P_X i => liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''X)
  | P_Y i => liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''Y)
  | P_Z i => liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''Z)
  | P_Scale a P => (sqsem a m)%:C *: Pfsem P m
  | P_Add P1 P2 => Pfsem P1 m + Pfsem P2 m
  | P_Mul P1 P2 => Pfsem P1 m \o Pfsem P2 m
  end.

Definition Psem (P : PExp) m : {hspace Hq} := espace1 (Pfsem P m).

(* Section 3.2 *)
Fixpoint Asem (A : AExp) (m : cmem) : {hspace Hq} :=
  match A with
  | A_BExp b => if esem b m then `1` else `0`
  | A_PExp P => Psem P m
  | A_neg A => ~` (Asem A m)
  | A_and A1 A2 => (Asem A1 m) `&` (Asem A2 m)
  | A_or A1 A2 => (Asem A1 m) `|` (Asem A2 m)
  | A_imply A1 A2 => ((Asem A1 m) `=>` (Asem A2 m))
  end.

End PASem.

(* The semantics of AExp  *)
Definition assertion := cmem -> {hspace Hq}.

(* Definition A.5*)
Definition satisfaction_def (mu : {vdistr cmem -> 'End(Hq)}) (A : assertion) :=
  forall m, (supph (mu m) `<=` A m)%HS.

(* Definition 3.3*)
Definition satisfaction q (mu : {vdistr cmem -> 'End(Hq)}) (A : AExp) :=
  satisfaction_def mu (Asem q A).


(* as we show later, entail_def is equivalent to satisfaction definition *)

Definition entail_def (A1 A2 : assertion) := forall m, (A1 m `<=` A2 m)%HS.

(* Definition3.4 *)
Definition Aentail (A1 A2 : AExp) := 
  forall q, entail_def (Asem q A1) (Asem q A2).

Notation "A1 '⊨a' A2" := (Aentail A1%A A2%A) (at level 70) : asyn_scope.
Notation "A1 '⟚a' A2" := (Aentail A1%A A2%A /\ Aentail A2%A A1%A) (at level 70) : asyn_scope.

Notation "mu '⊨fs' A" := (satisfaction_def mu A) (at level 70) : asyn_scope.
Notation "A1 '⊨fa' A2" := (entail_def A1 A2) (at level 70) : asyn_scope.
Notation "A1 '⟚fa' A2" := (entail_def A1 A2 /\ entail_def A2 A1) (at level 70) : asyn_scope.

(* program logic : proof rules *)

Inductive program_rule : AExp -> program -> AExp -> Prop :=
  | R_skip (A : AExp) : program_rule A skip A
  | R_initial i A : program_rule (AInitsubst i A) (initial i) A
  | R_assign (t : cType) (x : cvar t) (e : expr_ (evalCT t)) A : 
      program_rule (AExp_subst A x e) (assign x e) A
  | R_measure (x : cvar Bool) (P : PExp) A :
      program_rule ((P && A.[x <- false%:CS]) || (~~ P && A.[x <- true%:CS]))%A
        (measure x P) A
  | R_X i A : program_rule (AXsubst i A) (unitary1 i G_X) A
  | R_Y i A : program_rule (AYsubst i A) (unitary1 i G_Y) A
  | R_Z i A : program_rule (AZsubst i A) (unitary1 i G_Z) A
  | R_H i A : program_rule (AHsubst i A) (unitary1 i G_H) A
  | R_S i A : program_rule (ASsubst i A) (unitary1 i G_S) A
  | R_T i A : program_rule (ATsubst i A) (unitary1 i G_T) A
  | R_CNOT i j A of i != j : program_rule (ACNOTsubst i j A) (unitary2 i j G_CNOT) A
  | R_CZ i j A of i != j : program_rule (ACZsubst i j A) (unitary2 i j G_CZ) A
  | R_iSWAP i j A of i != j : program_rule (AiSWAPsubst i j A) (unitary2 i j G_iSWAP) A
  | R_seqc c1 c2 A B D of program_rule A c1 B & program_rule B c2 D :
      program_rule A (seqc c1 c2) D
  | R_cond (b : bexpr) c1 c2 A1 A2 B of 
      (program_rule A1 c1 B) & (program_rule A2 c2 B) :
      program_rule (((b && A1) || (~~b && A2))%A) (cond b c1 c2) B
  | R_while (b : bexpr) c A of program_rule (b && A) c A :
      program_rule A (while b c) (~~ b && A)
  | R_con c A A' B B' of (A ⊨a A')%A & (program_rule A' c B') & (B' ⊨a B)%A :
      program_rule A c B.

Section BasicAssertion.

Lemma entail_refl A : (A ⊨fa A)%A.
Proof. by move=>m. Qed.

Lemma entail_trans A B C : (A ⊨fa B -> B ⊨fa C -> A ⊨fa C)%A.
Proof. by move=>P1 P2 m; apply/(le_trans (P1 m) (P2 m)). Qed.

Lemma entail_anti A B : (A ⟚fa B)%A -> A = B.
Proof. by move=>[] P1 P2; apply/funext=>m; apply/le_anti; rewrite P1 P2. Qed.

Lemma Aentail_refl A : (A ⊨a A)%A.
Proof. by move=>m. Qed.

Lemma Aentail_trans A B C : (A ⊨a B -> B ⊨a C -> A ⊨a C)%A.
Proof. by move=>P1 P2 q m; apply/(le_trans (P1 q m) (P2 q m)). Qed.

Lemma Aentail_anti A1 A2 :
  (A1 ⟚a A2)%A <-> (forall q, Asem q A1 = Asem q A2).
Proof.
split=>[[]++q|H].
by move=>/(_ q) H1 /(_ q) H2; apply/entail_anti.
by split=>q; rewrite H.
Qed.

Lemma Aentail_imply A1 A2 : 
  Aentail A1 A2 <-> (forall q m, Asem q (A1 ==> A2)%A m = `1`%HS).
Proof. by split=>H m q; move: (H m q)=>/=; rewrite leEshook=>/eqP. Qed.

(* consistence with boolean logic *)
Lemma A_B_consistent (b1 b2 : bexpr) :
  (forall (q : 'QReg[Bool.[n.+1]]%REG) m, esem (b1 ==> b2)%X m) <->
  (forall q m, Asem q (A_imply (A_BExp b1) (A_BExp b2)) m = `1`%HS).
Proof.
split.
  move=>H q m; move: (H q m)=>/=.
  case: (esem b1 m)=>/=; last by rewrite shook0x.
  by case: (esem b2 m)=>// _; rewrite shookxx.
move=>H q m; move: (H q m)=>/=.
case: (esem b1 m)=>//=; case: (esem b2 m)=>//; rewrite shook1x.
by move=>/hspacelfP/esym/eqP; rewrite !hsE oner_eq0.
Qed.
  
End BasicAssertion.

Section Semantics.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Local Open Scope reg_scope.

Variable (q : 'QReg[Bool.[n.+1]]).

Local Notation Psem := (Psem q).
Local Notation Pfsem := (Pfsem q).
Local Notation Asem := (Asem q).

Section PauliSem.

Lemma Pfsem_subst (P : PExp) {Tc} (x : cvar Tc) (s : expr_ (eval_ctype Tc)) (m : cmem) :
  Pfsem (P.[x <- s])%P m = Pfsem P (m.[ x <- esem s m])%M.
Proof.
elim: P=>//=[??->|?->?->|?->?->]//.
by rewrite sqsem_subst.
Qed.

Lemma Psem_subst (P : PExp) {Tc} (x : cvar Tc) (s : expr_ (evalCT Tc)) m :
  Psem (P.[x <- s])%P m = Psem P (m.[x <- esem s m])%M.
Proof. by rewrite /Psem Pfsem_subst. Qed.

(*Theorem 3.1, single-qubit unitary*)
Lemma PExp_subst1_correctv i (P : PExp) Xs Ys Zs (U : 'FU('Hs bool)) m v :
  Pfsem Xs m = liftf_lf (tf2f <{q.[i]}> <{q.[i]}> (U^A \o ''X \o U)) ->
  Pfsem Ys m = liftf_lf (tf2f <{q.[i]}> <{q.[i]}> (U^A \o ''Y \o U)) ->
  Pfsem Zs m = liftf_lf (tf2f <{q.[i]}> <{q.[i]}> (U^A \o ''Z \o U)) ->
  (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> U) v \in Psem P m) =
    (v \in Psem (PExp_subst1 P i Xs Ys Zs) m).
Proof.
move=>Px Py Pz.
rewrite /Psem !espace1E eq_sym -unitaryf_sym/= -liftf_lf_adj tf2f_adj.
set ua := liftf_lf _; set u := liftf_lf _.
rewrite -!comp_lfunE; f_equal; f_equal.
elim: P =>/=[j|j|j|||].
(* - by rewrite comp_lfun1r -liftf_lf_comp tf2f_comp unitaryf_form tf2f1 liftf_lf1. *)
- case: eqP=>[->|/eqP nij].
    by rewrite Px -!liftf_lf_comp !tf2f_comp.
  rewrite liftf_lf_compC -?disj_setE; first by QRegAuto.tac_expose.
  by rewrite -tf2f_adj liftf_lf_adj unitaryfKl.
- case: eqP=>[->|/eqP nij].
    by rewrite Py -!liftf_lf_comp !tf2f_comp.
  rewrite liftf_lf_compC -?disj_setE; first by QRegAuto.tac_expose.
  by rewrite -tf2f_adj liftf_lf_adj unitaryfKl.
- case: eqP=>[->|/eqP nij].
    by rewrite Pz -!liftf_lf_comp !tf2f_comp.
  rewrite liftf_lf_compC -?disj_setE; first by QRegAuto.tac_expose.
  by rewrite -tf2f_adj liftf_lf_adj unitaryfKl.
- by move=>a P H; rewrite linearZr linearZl/= H.
- by move=>P1 H1 P2 H2; rewrite linearDr linearDl/= H1 H2.
- by move=>P1 H1 P2 H2; rewrite -[Pfsem P1 m]comp_lfun1r -(unitaryf_formV u) 
    !comp_lfunA H1 comp_lfunACA -comp_lfunA -liftf_lf_adj tf2f_adj H2.
Qed.

Lemma PXsubst_correctv i (P : PExp) m v :
  (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''X) v \in Psem P m)
   = (v \in Psem (PXsubst i P) m).
Proof.
by apply/PExp_subst1_correctv=>/=; rewrite ?sq_semE ?realcN PauliX_adj 
  ?Gate_XXX// ?Gate_XZX ?Gate_XYX scaleN1r !linearN.
Qed.

Lemma PXsubst_correct i (P : PExp) m (A : 'FD) :
  let X := liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''X) in 
  (supph (formlf X A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PXsubst i P) m)%HS.
Proof. apply/supph_denf_leP/PXsubst_correctv. Qed.

Lemma PYsubst_correctv i (P : PExp) m v :
  (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''Y) v \in Psem P m)
   = (v \in Psem (PYsubst i P) m).
Proof.
by apply/PExp_subst1_correctv=>/=; rewrite ?sq_semE ?realcN PauliY_adj
  ?Gate_YYY// ?Gate_YZY ?Gate_YXY scaleN1r !linearN.
Qed.

Lemma PYsubst_correct i (P : PExp) m (A : 'FD) :
  let Y := liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''Y) in 
  (supph (formlf Y A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PYsubst i P) m)%HS.
Proof. apply/supph_denf_leP/PYsubst_correctv. Qed.

Lemma PZsubst_correctv i (P : PExp) m v :
  (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''Z) v \in Psem P m)
   = (v \in Psem (PZsubst i P) m).
Proof.
by apply/PExp_subst1_correctv=>/=; rewrite ?sq_semE ?realcN PauliZ_adj
  ?Gate_ZZZ// ?Gate_ZXZ ?Gate_ZYZ scaleN1r !linearN.
Qed.

Lemma PZsubst_correct i (P : PExp) m (A : 'FD) :
  let Z := liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''Z) in 
  (supph (formlf Z A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PZsubst i P) m)%HS.
Proof. apply/supph_denf_leP/PZsubst_correctv. Qed.

Lemma PHsubst_correctv i (P : PExp) m v :
  (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''H) v \in Psem P m)
   = (v \in Psem (PHsubst i P) m).
Proof.
by apply/PExp_subst1_correctv=>/=; rewrite ?sq_semE ?realcN Hadamard_adj
  ?Gate_HXH ?Gate_HYH ?Gate_HZH// scaleN1r !linearN.
Qed.

Lemma PHsubst_correct i (P : PExp) m (A : 'FD) :
  let H := liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''H) in 
  (supph (formlf H A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PHsubst i P) m)%HS.
Proof. apply/supph_denf_leP/PHsubst_correctv. Qed.

Lemma PSsubst_correctv i (P : PExp) m v :
  (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''S) v \in Psem P m)
   = (v \in Psem (PSsubst i P) m).
Proof.
by apply/PExp_subst1_correctv=>/=; rewrite ?sq_semE ?realcN
  ?Gate_SaXS ?Gate_SaYS ?Gate_SaZS// scaleN1r !linearN.
Qed.

Lemma PSsubst_correct i (P : PExp) m (A : 'FD) :
  let S := liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''S) in 
  (supph (formlf S A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PSsubst i P) m)%HS.
Proof. apply/supph_denf_leP/PSsubst_correctv. Qed.

Lemma PTsubst_correctv i (P : PExp) m v :
  (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''T) v \in Psem P m)
   = (v \in Psem (PTsubst i P) m).
Proof.
apply/PExp_subst1_correctv=>/=; rewrite ?sq_semE ?Gate_TaZT//.
by rewrite Gate_TaXT !linearZ/= !linearB/= realcN realcI sqrtrC// natrC scaleNr.
by rewrite Gate_TaYT !linearZ/= !linearD/= realcI sqrtrC// natrC.
Qed.

Lemma PTsubst_correct i (P : PExp) m (A : 'FD) :
  let T := liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''T) in 
  (supph (formlf T A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PTsubst i P) m)%HS.
Proof. apply/supph_denf_leP/PTsubst_correctv. Qed.

#[local] Lemma lift_exdl i j A : i != j -> 
  liftf_lf (tf2f <{q.[i]}> <{q.[i]}> A) = 
    liftf_lf (tf2f <{(q.[i],q.[j])}> <{(q.[i],q.[j])}> (A ⊗f \1)).
Proof.
move=>nij; rewrite -tf2f_pair liftf_lf_cast -liftf_lf_compT -?disj_setE.
  by QRegAuto.tac_expose.
by rewrite tf2f1 liftf_lf1 comp_lfun1r.
Qed.

#[local] Lemma lift_exdr i j A : i != j -> 
  liftf_lf (tf2f <{q.[j]}> <{q.[j]}> A) = 
    liftf_lf (tf2f <{(q.[i],q.[j])}> <{(q.[i],q.[j])}> (\1 ⊗f A)).
Proof.
move=>nij; rewrite -tf2f_pair liftf_lf_cast -liftf_lf_compT -?disj_setE.
  by QRegAuto.tac_expose.
by rewrite tf2f1 liftf_lf1 comp_lfun1l.
Qed.

(*Theorem 3.1, two-qubit unitary*)
Lemma PExp_subst2_correctv i j (P : PExp) Xi Yi Zi Xj Yj Zj 
  (U : 'FU('Hs (bool * bool))) m v : i != j ->
  Pfsem Xi m = liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> (U^A \o (''X ⊗f \1) \o U)) ->
  Pfsem Yi m = liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> (U^A \o (''Y ⊗f \1) \o U)) ->
  Pfsem Zi m = liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> (U^A \o (''Z ⊗f \1) \o U)) ->
  Pfsem Xj m = liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> (U^A \o (\1 ⊗f ''X) \o U)) ->
  Pfsem Yj m = liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> (U^A \o (\1 ⊗f ''Y) \o U)) ->
  Pfsem Zj m = liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> (U^A \o (\1 ⊗f ''Z) \o U)) ->
  (liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> U) v \in Psem P m) =
    (v \in Psem (PExp_subst2 P i j Xi Yi Zi Xj Yj Zj ) m).
Proof.
move=>nij Pxi Pyi Pzi Pxj Pyj Pzj.
set u := liftf_lf _.
set ua := liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> U^A).
rewrite /Psem !espace1E eq_sym -unitaryf_sym/= -!comp_lfunE.
rewrite -liftf_lf_adj tf2f_adj -/ua; f_equal; f_equal.
elim: P=>/=[k|k|k|||].
(* - by rewrite comp_lfun1r -liftf_lf_comp tf2f_comp unitaryf_form tf2f1 liftf_lf1. *)
- case: eqP=>[->|/eqP nki].
    by rewrite (lift_exdl _ nij) -!liftf_lf_comp !tf2f_comp/= Pxi.
  case: eqP=>[->|/eqP nkj].
    by rewrite (lift_exdr _ nij) -!liftf_lf_comp !tf2f_comp/= Pxj.
  rewrite liftf_lf_compC -?disj_setE; first by QRegAuto.tac_expose.
  by rewrite -tf2f_adj liftf_lf_adj unitaryfKl.
- case: eqP=>[->|/eqP nki].
    by rewrite (lift_exdl _ nij) -!liftf_lf_comp !tf2f_comp/= Pyi.
  case: eqP=>[->|/eqP nkj].
    by rewrite (lift_exdr _ nij) -!liftf_lf_comp !tf2f_comp/= Pyj.
  rewrite liftf_lf_compC -?disj_setE; first by QRegAuto.tac_expose.
  by rewrite -tf2f_adj liftf_lf_adj unitaryfKl.
- case: eqP=>[->|/eqP nki].
    by rewrite (lift_exdl _ nij) -!liftf_lf_comp !tf2f_comp/= Pzi.
  case: eqP=>[->|/eqP nkj].
    by rewrite (lift_exdr _ nij) -!liftf_lf_comp !tf2f_comp/= Pzj.
  rewrite liftf_lf_compC -?disj_setE; first by QRegAuto.tac_expose.
  by rewrite -tf2f_adj liftf_lf_adj unitaryfKl.
- by move=>a P H; rewrite linearZr linearZl/= H.
- by move=>P1 H1 P2 H2; rewrite linearDr linearDl/= H1 H2.
- by move=>P1 H1 P2 H2; rewrite -[Pfsem P1 m]comp_lfun1r
    -(unitaryf_formV u) !comp_lfunA H1 comp_lfunACA 
    -comp_lfunA -liftf_lf_adj tf2f_adj H2.
Qed.

Lemma PCNOTsubst_correctv j k (P : PExp) m v : j != k ->
  (liftf_lf (tf2f <{(q.[j], q.[k])}> <{(q.[j], q.[k])}> CNOT) v \in Psem P m)
   = (v \in Psem (PCNOTsubst j k P) m).
Proof.
move=>njk.
have Pq : [disjoint mset <{ q.[j] }> & mset <{ q.[k] }>]
  by rewrite -disj_setE; QRegAuto.tac_expose.
apply/PExp_subst2_correctv=>//=.
- by rewrite CNOT_adj Gate_CNOTX1CNOT -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite CNOT_adj Gate_CNOTY1CNOT -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite CNOT_adj Gate_CNOTZ1CNOT -tf2f_pair liftf_lf_cast -liftf_lf_compT//
    tf2f1 liftf_lf1 comp_lfun1r.
- by rewrite CNOT_adj Gate_CNOTX2CNOT -tf2f_pair liftf_lf_cast -liftf_lf_compT//
    tf2f1 liftf_lf1 comp_lfun1l.
- by rewrite CNOT_adj Gate_CNOTY2CNOT -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite CNOT_adj Gate_CNOTZ2CNOT -tf2f_pair liftf_lf_cast liftf_lf_compT.
Qed.

Lemma PCNOTsubst_correct j k (P : PExp) m (A : 'FD) : j != k ->
  let cnot := liftf_lf (tf2f <{(q.[j], q.[k])}> <{(q.[j], q.[k])}> CNOT) in 
  (supph (formlf cnot A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PCNOTsubst j k P) m)%HS.
Proof. by move=>njk; apply/supph_denf_leP=>v; apply/PCNOTsubst_correctv. Qed.

Lemma PCZsubst_correctv j k (P : PExp) m v : j != k ->
  (liftf_lf (tf2f <{(q.[j], q.[k])}> <{(q.[j], q.[k])}> ''CZ) v \in Psem P m)
   = (v \in Psem (PCZsubst j k P) m).
Proof.
move=>njk.
have Pq : [disjoint mset <{ q.[j] }> & mset <{ q.[k] }>]
  by rewrite -disj_setE; QRegAuto.tac_expose.
apply/PExp_subst2_correctv=>//=.
- by rewrite CZGate_adj Gate_CZX1CZ -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite CZGate_adj Gate_CZY1CZ -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite CZGate_adj Gate_CZZ1CZ -tf2f_pair liftf_lf_cast -liftf_lf_compT//
    tf2f1 liftf_lf1 comp_lfun1r.
- by rewrite CZGate_adj Gate_CZX2CZ -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite CZGate_adj Gate_CZY2CZ -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite CZGate_adj Gate_CZZ2CZ -tf2f_pair liftf_lf_cast -liftf_lf_compT//
    tf2f1 liftf_lf1 comp_lfun1l.
Qed.

Lemma PCZsubst_correct j k (P : PExp) m (A : 'FD) : j != k ->
  let CZ := liftf_lf (tf2f <{(q.[j], q.[k])}> <{(q.[j], q.[k])}> ''CZ) in 
  (supph (formlf CZ A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PCZsubst j k P) m)%HS.
Proof. by move=>njk; apply/supph_denf_leP=>v; apply/PCZsubst_correctv. Qed.

Lemma PiSWAPsubst_correctv j k (P : PExp) m v : j != k ->
  (liftf_lf (tf2f <{(q.[j], q.[k])}> <{(q.[j], q.[k])}> iSWAP) v \in Psem P m)
   = (v \in Psem (PiSWAPsubst j k P) m).
Proof.
move=>njk.
have Pq : [disjoint mset <{ q.[j] }> & mset <{ q.[k] }>]
  by rewrite -disj_setE; QRegAuto.tac_expose.
apply/PExp_subst2_correctv=>//=.
- by rewrite Gate_iSWAPaX1iSWAP -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite Gate_iSWAPaY1iSWAP -tf2f_pair liftf_lf_cast sq_semE 
    realcN scaleN1r linearN/= -liftf_lf_compT// linearN.
- by rewrite Gate_iSWAPaZ1iSWAP -tf2f_pair liftf_lf_cast -liftf_lf_compT//
    tf2f1 liftf_lf1 comp_lfun1l.
- by rewrite Gate_iSWAPaX2iSWAP -tf2f_pair liftf_lf_cast liftf_lf_compT.
- by rewrite Gate_iSWAPaY2iSWAP -tf2f_pair liftf_lf_cast sq_semE 
    realcN scaleN1r linearN/= -liftf_lf_compT// linearN.
- by rewrite Gate_iSWAPaZ2iSWAP -tf2f_pair liftf_lf_cast -liftf_lf_compT//
    tf2f1 liftf_lf1 comp_lfun1r.
Qed.

Lemma PiSWAPsubst_correct j k (P : PExp) m (A : 'FD) : j != k ->
  let iswap := liftf_lf (tf2f <{(q.[j], q.[k])}> <{(q.[j], q.[k])}> iSWAP) in 
  (supph (formlf iswap A) `<=` Psem P m)%HS
   = (supph A `<=` Psem (PiSWAPsubst j k P) m)%HS.
Proof. by move=>njk; apply/supph_denf_leP=>v; apply/PiSWAPsubst_correctv. Qed.

End PauliSem.

Notation "mu '⊨s' A" := (satisfaction q mu A) (at level 70) : asyn_scope.

Section AssertionSem.

Definition sunit_def_lf := sunit_def.
HB.instance Definition _ (I : choiceType) (R : numFieldType) (U : normedZmodType R) (i : I) (v : U) :=
  Summable.copy (sunit_def_lf i v) (sunit_def i v).

Lemma sunit_lf_vdistr_ge0 (I : choiceType) (U : chsType) (i : I) (v : 'FD(U)) :
  forall j : I, 0%:VF ⊑ sunit_def_lf i v%:VF j.
Proof. 
by intros=>/=; rewrite /sunit_def_lf /sunit_def; 
case: eqP=>// _; apply: denf_ge0.
Qed.

Lemma sunit_lf_vdistr_sum_le1 (I : choiceType) (U : chsType) (i : I) (v : 'FD(U)) :
  `| sum (sunit_def_lf i v%:VF) | <= 1.
Proof. by rewrite sunit_sum trfnorm_psd denf_trlf. Qed.

HB.instance Definition _ I U i v := Summable_isVDistr.Build _ _ _ (sunit_def_lf _ _)
  (@sunit_lf_vdistr_ge0 I U i v) (sunit_lf_vdistr_sum_le1 i v).

Definition singleton (m : cmem) (r : 'FD(Hq)) : {vdistr cmem -> 'End(Hq)} :=
  sunit_def_lf m r%:VF.

Lemma singleton_satisfy m x A :
  ((singleton m x) ⊨fs A)%A <-> supph x `<=` A m.
Proof.
split=>[/(_ m)| P i]/=; rewrite /sunit_def_lf /sunit_def ?eqxx; first by [].
by case: eqP=>[->//|]; rewrite supph0 le0h.
Qed.

(* Definition A.6*)
Lemma entail_alter A B : 
  (A ⊨fa B)%A <-> (forall mu, (mu ⊨fs A -> mu ⊨fs B)%A).
Proof.
split=>[P mu PA m|P m]; last apply/leh_suppP=>x.
  move: (PA m) (P m); apply le_trans.
rewrite -[X in X -> _]singleton_satisfy -[X in _ -> X]singleton_satisfy; apply: P.
Qed.

(* Figure 3, correctness of inference rules *)

Lemma Asem_subst (A : AExp) {Tc} (x : cvar Tc) (s : expr_ (evalCT Tc)) m :
  Asem A.[x <- s] m = Asem A (m.[x <- esem s m])%M.
Proof.
elim: A=>/=[?|?|?->|?->?->|?->?->|?->?->]//.
by rewrite esem_subst.
by rewrite Psem_subst.
Qed.

Lemma AExp_subst_correct {Tc} (x : cvar Tc) (s : expr_ (evalCT Tc)) m r A :
  (singleton m r ⊨s A.[x <- s] <-> singleton (m.[x <- esem s m])%M r ⊨s A)%A.
Proof.
rewrite /satisfaction !singleton_satisfy.
suff ->: Asem A.[x <- s] m = Asem A (m.[x <- esem s m])%M by [].
elim: A=>/= [b|A|?->|?->?->|?->?->|?->?->]//.
  by rewrite esem_subst.
by rewrite /Psem Pfsem_subst.
Qed.

Lemma AExp_subst1_correct i Xs Ys Zs (U : 'FU) A m r :
  (forall P (B : 'FD), let X := liftf_lf (tf2f <{ q.[i] }> <{ q.[i] }> U) in
  (supph (formlf X B) `<=` Psem P m) = (supph B `<=` Psem (PExp_subst1 P i Xs Ys Zs) m))%HS ->
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> U)) in
  (singleton m r ⊨s A.[i; Xs<-X, Ys<-Y, Zs<-Z] 
    <-> singleton m (E r) ⊨s A)%A.
Proof.
move=>P0; rewrite /= /satisfaction !singleton_satisfy liftfso_formso.
elim: A r.
- move=>b r /=; case: (esem b m); rewrite ?leh1 ?leh0 ?supph_eq0; first by [].
  split=>[/eqP->|]; first by rewrite linear0.
  rewrite liftfso_formso formsoE; set u := liftf_lf _.
  move=>/eqP/(f_equal (fun x => u^A \o x))/(f_equal (fun x => x \o u)).
  by rewrite !comp_lfunA unitaryfKl unitaryfEl comp_lfun1l comp_lfun0r comp_lfun0l=>->.
- move=>P r /=; rewrite liftfso_formso -formlf_soE.
  by apply/eqb_iff/esym/P0.
- move=>A /=; rewrite liftfso_formso =>H r.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhO.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
- move=>A1 + A2 + r /=; rewrite liftfso_formso/= liftfso_formso/= =>H1 H2.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhI.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H1 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
  by move: (H2 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
- move=>A1 + A2 + r /=; rewrite liftfso_formso/= liftfso_formso/= =>H1 H2.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhU.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H1 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
  by move: (H2 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
- move=>A1 + A2 + r /=; rewrite liftfso_formso/= liftfso_formso/= =>H1 H2.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhH.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H1 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
  by move: (H2 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
Qed.

Lemma AXsubst_correct i A m r :
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> ''X)) in
  (singleton m r ⊨s AXsubst i A <-> singleton m (E r) ⊨s A)%A.
Proof. by apply/AExp_subst1_correct=>P B; apply/PXsubst_correct. Qed.

Lemma AYsubst_correct i A m r :
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> ''Y)) in
  (singleton m r ⊨s AYsubst i A <-> singleton m (E r) ⊨s A)%A.
Proof. by apply/AExp_subst1_correct=>P B; apply/PYsubst_correct. Qed.

Lemma AZsubst_correct i A m r :
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> ''Z)) in
  (singleton m r ⊨s AZsubst i A <-> singleton m (E r) ⊨s A)%A.
Proof. by apply/AExp_subst1_correct=>P B; apply/PZsubst_correct. Qed.

Lemma AHsubst_correct i A m r :
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> ''H)) in
  (singleton m r ⊨s AHsubst i A <-> singleton m (E r) ⊨s A)%A.
Proof. by apply/AExp_subst1_correct=>P B; apply/PHsubst_correct. Qed.

Lemma ASsubst_correct i A m r :
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> ''S)) in
  (singleton m r ⊨s ASsubst i A <-> singleton m (E r) ⊨s A)%A.
Proof. by apply/AExp_subst1_correct=>P B; apply/PSsubst_correct. Qed.

Lemma ATsubst_correct i A m r :
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> ''T)) in
  (singleton m r ⊨s ATsubst i A <-> singleton m (E r) ⊨s A)%A.
Proof. by apply/AExp_subst1_correct=>P B; apply/PTsubst_correct. Qed.

Lemma AExp_subst2_correct i j Xi Yi Zi Xj Yj Zj (U : 'FU) A m r : i != j ->
  (forall P (B : 'FD), 
    let X := liftf_lf (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> U) in
  (supph (formlf X B) `<=` Psem P m) = 
    (supph B `<=` Psem (PExp_subst2 P i j Xi Yi Zi Xj Yj Zj) m))%HS ->
  let E := liftfso (formso (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> U)) in
  (singleton m r ⊨s A.[i, j; Xi<-Xi, Yi<-Yi, Zi<-Zi, Xj<-Xj, Yj<-Yj, Zj<-Zj] 
    <-> singleton m (E r) ⊨s A)%A.
Proof.
move=>nij P0; rewrite /= /satisfaction !singleton_satisfy liftfso_formso.
elim: A r.
- move=>b r /=; case: (esem b m); rewrite ?leh1 ?leh0 ?supph_eq0; first by [].
  split=>[/eqP->|]; first by rewrite linear0.
  rewrite liftfso_formso formsoE; set u := liftf_lf _.
  move=>/eqP/(f_equal (fun x => u^A \o x))/(f_equal (fun x => x \o u)).
  by rewrite !comp_lfunA unitaryfKl unitaryfEl comp_lfun1l comp_lfun0r comp_lfun0l=>->.
- move=>P r /=; rewrite liftfso_formso -formlf_soE.
  by apply/eqb_iff/esym/P0.
- move=>A /=; rewrite liftfso_formso =>H r.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhO.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
- move=>A1 + A2 + r /=; rewrite liftfso_formso/= liftfso_formso/= =>H1 H2.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhI.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H1 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
  by move: (H2 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
- move=>A1 + A2 + r /=; rewrite liftfso_formso/= liftfso_formso/= =>H1 H2.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhU.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H1 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
  by move: (H2 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
- move=>A1 + A2 + r /=; rewrite liftfso_formso/= liftfso_formso/= =>H1 H2.
  apply/eqb_iff; rewrite -formlf_soE [RHS]supph_formV formhH.
  f_equal; f_equal; apply/eqP/eq_supphP=>x.
  by move: (H1 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
  by move: (H2 x)=>/eqb_iff->; rewrite -formlf_soE supph_formV.
Qed.

Lemma ACNOTsubst_correct i j A m r : i != j ->
  let E := liftfso (formso (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> CNOT)) in
  (singleton m r ⊨s ACNOTsubst i j A <-> singleton m (E r) ⊨s A)%A.
Proof.
by move=>nij; apply/AExp_subst2_correct=>[//|P B]; apply/PCNOTsubst_correct.
Qed.

Lemma ACZsubst_correct i j A m r : i != j ->
  let E := liftfso (formso (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> ''CZ)) in
  (singleton m r ⊨s ACZsubst i j A <-> singleton m (E r) ⊨s A)%A.
Proof.
by move=>nij; apply/AExp_subst2_correct=>[//|P B]; apply/PCZsubst_correct.
Qed.

Lemma AiSWAPsubst_correct i j A m r : i != j ->
  let E := liftfso (formso (tf2f <{(q.[i], q.[j])}> <{(q.[i], q.[j])}> iSWAP)) in
  (singleton m r ⊨s AiSWAPsubst i j A <-> singleton m (E r) ⊨s A)%A.
Proof.
by move=>nij; apply/AExp_subst2_correct=>[//|P B]; apply/PiSWAPsubst_correct.
Qed.

Lemma kerh_liftfh T (x : 'QReg[T]) (f : 'End{T}) :
  kerh (liftf_lf (tf2f x x f)) = liftfh x (kerh f).
Proof.
apply/eqP/hseqP=>v.
rewrite memh_kerE memhOE -liftfhO/= liftfhE th2hE -supphE hsE.
apply/eqb_iff; split=>/eqP; [rewrite /supplf | rewrite -{3}[f]suppvlf];
by rewrite -(tf2f_comp _ x x x) liftf_lf_comp lfunE/==>->; rewrite linear0.
Qed.

Lemma espace1_liftfh T (x : 'QReg[T]) (f : 'End{T}) :
  espace1 (liftf_lf (tf2f x x f)) = liftfh x (espace1 f).
Proof.
by rewrite /espace1 -liftf_lf_cplmt -{1}cplmtE -tf2f1 -linearB/= cplmtE kerh_liftfh.
Qed.

(*Rule Init is sound*)
Lemma Initsubst_correct i A m r :
  (singleton m r ⊨s AInitsubst i A <->
  singleton m (liftfso (initialso (tv2v <{q.[i]}> '0)) r) ⊨s A)%A.
Proof.
rewrite /satisfaction !singleton_satisfy /=.
have -> : liftfso (initialso (tv2v <{q.[i]}> '0)) r = 
  formlf (liftfh <{ q.[i] }> <[ '0 ]>) r + formlf (liftf_lf (tf2f <{q.[i]}> <{q.[i]}> ''X))  (formlf (liftfh <{ q.[i] }> <[ '1 ]>) r).
  rewrite -(initialso_onb _ (tv2v_fun _ <{q.[i]}> t2tv)) liftfso_krausso.
  rewrite kraussoE/= big_bool/= liftf_funE /tv2v_fun !tv2v_out addrC;
  rewrite -!formlfE formlf_comp !liftfhE !th2hE !hlineE !supph_Pid/=;
  by rewrite -liftf_lf_comp tf2f_comp outp_compr PauliX_cb.
rewrite !formlf_soE/= supphD/= -2!formlf_soE supph_formlf -PauliX_adj.
rewrite -tf2f_adj liftf_lf_adj formh_supph/= -formlf_soE supph_formlf formhJ.
set P0 := liftfh _ _.
set P1 := liftfh _ _.
set U := hstensor_liftf_lf__canonical__quantum_GisoLf _.
set B := Asem A m.
have -> : Psem (P_Z i) m = P0.
  by rewrite /Psem/= espace1_liftfh espace1_PauliZ.
have -> : Psem (-1 *: P_Z i)%P m = P1.
  rewrite /Psem/= sq_semE realcN scaleN1r -2!linearN/=.
  by rewrite espace1_liftfh espace1_PauliZN.
have -> : Asem (AXsubst i A) m = formh U^A B.
  apply/eqP/eq_supphP=>x. move: (AXsubst_correct i A m x).
  rewrite /= /satisfaction !singleton_satisfy=>/eqb_iff->.
  by rewrite -supph_formV/= liftfso_formso -formlf_soE.
have BK x : formh U^A (formh U^A x) = x.
  apply/hspacelfP; rewrite !formhE/= formlf_comp -adjf_comp/=.
  rewrite -liftf_lf_comp !tf2f_comp Gate_XX tf2f1 liftf_lf1.
  by rewrite formlfE !adjf1 comp_lfun1l comp_lfun1r.
have P10 : formh U^A P1 = P0.
  apply/hspacelfP=>/=; rewrite formhE/= formlfE.
  by rewrite adjfK -liftf_lf_adj tf2f_adj /P1 /P1 !liftfhE !th2hE !hlineE !supph_Pid/=
    -!liftf_lf_comp !tf2f_comp outp_compr outp_compl PauliX_adj PauliX_cb.
have P01 : formh U^A P0 = P1 by rewrite -P10 BK.
have P0C : ~` P0 = P1.
  rewrite /P0 /P1 -liftfhO; f_equal; apply/hspacelfP/eqP.
  by rewrite !hlineE/= hsE/= !supph_Pid/= /cplmt subr_eq addrC sumbtv_out.
have P1C : ~` P1 = P0 by rewrite -P0C hsOK.
have P01C : P0 _C_ P1 by rewrite -P0C commutexOx.
rewrite P10 -[in X in _ <-> X]sprojUr.
split.
  move=>Q1; move: {+}Q1; rewrite -(formh_le U^A)=>Q2.
  apply/(le_trans (leJr P0 (lehU2 Q1 Q2))).
  rewrite formhU !formhI P10 P01 BK [X in _ `|` X]cuphC cuphh.
  rewrite sprojUr /sasaki_projection !meetxUr ?commutexOx=>[//||//||].
  rewrite commutexIl//.
  by rewrite -commutexO hsOI P1C commutexUl.
  by rewrite caphxO cup0h caphA caphh cup0h caphA -P0C caphxO cap0h cuph0 lehIr.
set D := _ `&&` _ => Q1.
apply/(le_trans (y := P0 `&` D `|` P1 `&` formh U^A D)); last first.
  by apply/lehU2; apply/lehI2l; rewrite ?formh_le.
rewrite /D formhJ P01 [X in _ `|` (_ `&` (_ `&&` X))]formhU.
by rewrite BK [supph r `|` _]cuphC !meetxJxy -P0C 
  joinJxyJOxy lehI cuphA lehUr cuphA lehUr.
Qed.

End AssertionSem.

Section ProgramSem.

Definition Gate1_sem (U : Gate1) : 'FU('Hs bool) :=
  match U with
  | G_X => ''X
  | G_Y => ''Y
  | G_Z => ''Z
  | G_H => ''H
  | G_S => ''S
  | G_T => ''T
  end.

Definition Gate2_sem (U : Gate2) : 'FU('Hs (bool * bool)%type) :=
  match U with
  | G_CNOT => CNOT
  | G_CZ => ''CZ
  | G_iSWAP => iSWAP
  end.

Fixpoint expr_SQExp (s : SQExp) : expr_ R :=
  match s with
  | SQ_bool b => ((-1)%:CS ^+ (nat_of_bool%:F1 b))%X
  | SQ_sqrt2 => (Num.sqrt 2)%:CS
  | SQ_div2 s t => ((expr_SQExp s) / (2%:CS ^+ t))%X
  | SQ_add s1 s2 => (expr_SQExp s1 + expr_SQExp s2)%X
  | SQ_opp s => (- expr_SQExp s)%X
  | SQ_mul s1 s2 => (expr_SQExp s1 * expr_SQExp s2)%X
  end.

Lemma esem_SQExpE s m :
  sqsem s m = esem (expr_SQExp s) m.
Proof. by elim: s=>//=[?->?|?->?->|?->|?->?->]. Qed.  

Notation tentf_lift i X := (tentf_tuple (fun j => if i == j then X else \1)).

Fixpoint expr_PExp (P : PExp) : expr_ 'End[n.+1.-tuple bool] :=
  match P with
  | P_X i => (tentf_lift i ''X)%:CS
  | P_Y i => (tentf_lift i ''Y)%:CS
  | P_Z i => (tentf_lift i ''Z)%:CS
  | P_Scale s P => ((expr_SQExp s)%:C *: expr_PExp P)%X
  | P_Add P1 P2 => (expr_PExp P1 + expr_PExp P2)%X
  | P_Mul P1 P2 => (expr_PExp P1 \o expr_PExp P2)%X
  end.

Definition expr_Pmeas P : mexpr _ _ := 
    ((@preliminary_measure_proj__canonical__quantum_QMeasure _)%:F1 ((@espace1 _)%:F1 (expr_PExp P)))%X.

From quantum.dirac Require Import dirac.

Lemma liftf_lf_dirac_eq S1 S2 (f : 'F[msys]_S1) (g : 'F[msys]_S2) :
  ('[ f ] = '[ g ])%D -> liftf_lf f = liftf_lf g.
Proof.
move=>P; move: {+}P=>/sqrdirac_eqP/orP/= [/eqP Ps|/eqP Pf].
  by case: S2 / Ps g P => g /lind_inj ->.
move: {+}P=>/esym/sqrdirac_eqP/orP/= [/eqP/esym Ps|/eqP Pg].
  by case: S2 / Ps g P => g /lind_inj ->.
move: Pf Pg => /(f_equal (fun x : 'D => x S1 S1)) + /(f_equal (fun x : 'D => x S2 S2)).
by rewrite !lind_id !diracE=>->->; rewrite !linear0.
Qed.

#[local] Lemma liftf_tf2f (i : 'I_n.+1) (U : 'End[bool]) :
  liftf_lf (tf2f q q (tentf_tuple (fun j : 'I_n.+1 => if i == j then U else \1)))
    = liftf_lf (tf2f <{ q.[i] }> <{ q.[i] }> U).
Proof.
symmetry.
rewrite -(tf2f_eqr _ (eq_qreg_tuple _) (eq_qreg_tuple _)) liftf_lf_cast/=.
rewrite -tf2f_tuple liftf_lf_cast/= -[LHS]comp_lfun1l.
have <-: liftf_lf (tf2f <{ (tuple j : 'I_n => q.[nlift i j]) }>
        <{ (tuple j : 'I_n => q.[nlift i j]) }> \1) = \1.
  by rewrite tf2f1 liftf_lf1.
rewrite liftf_lf_compT; first by rewrite -disj_setE; QRegAuto.tac_expose.
apply/liftf_lf_dirac_eq. rewrite tf2f1 -tend_correct -tenfm_correct.
rewrite (bigD1 i)//= bigdE eqxx tendC; f_equal.
set x := (\ten_(_ | _) _)%D.
have ->: x = (\ten_(i0 < n.+1 | i0 != i) '[tf2f <{ q.[i0] }> <{ q.[i0] }> \1])%D.
  by rewrite /x bigd; apply eq_bigr=>j /negPf nji; rewrite eq_sym nji.
under eq_bigr do rewrite tf2f1.
rewrite tendsI -mset_tuple; set a := \bigcup_(_ | _) _.
set b := \bigcup_(_ | _) _.
suff ->: a = b by [].
apply/eqP; rewrite finset.eqEsubset; apply/andP; split.
  apply/bigcupsP=>/= j _. apply/(bigcup_max (nlift i j))=>//.
  by rewrite lift_eqF.
apply/bigcupsP=>/= j; case: (unliftP i j)=>/=[k -> _|->];
rewrite ?eqxx//; apply/(bigcup_max k)=>//.
Qed.

Lemma esem_PExpfET P m : 
  Pfsem P m = liftf_lf (tf2f q q (esem (expr_PExp P) m)).
Proof.
elim: P=>//=.
1-3: by move=>i; rewrite liftf_tf2f.
by move=>a P /=; rewrite -esem_SQExpE -tf2fZ linearZ/==><-.
by move=>P1 -> P2 ->; rewrite -tf2fD linearD.
by move=>P1 -> P2 ->; rewrite -liftf_lf_comp tf2f_comp.
Qed.

Lemma esem_PExpEF P m :
  Psem P m = (liftf_lf (tm2m q q (esem (expr_Pmeas P) m) false)) :> 'End( _ ).
Proof.
by rewrite /Psem/= /measure_proj/= /tm2m -th2hE -liftfhE -espace1_liftfh esem_PExpfET.
Qed.

Lemma esem_PExpET P m :
  ~` (Psem P m) = (liftf_lf (tm2m q q (esem (expr_Pmeas P) m) true)) :> 'End( _ ).
Proof.
by rewrite /Psem /measure_proj/= /tm2m -th2hE -liftfhE liftfhO -espace1_liftfh esem_PExpfET.
Qed.

Definition sem_apply_def (I J : choiceType) (U V : chsType) (s : semType I J U V) m x 
  := fun o => s m o x.

Lemma test1 (U V : chsType) (E : 'SO(U,V)) (x : 'End(U)) : 
  `|E x| <= ((dim U)%:R * choinorm E) * `|x|.
Proof.
rewrite /normr/= /trfnorm -choimxE.
apply/(le_trans (trnorm_ptrace1 _)).
apply/(le_trans (trnormMl _ _)).
rewrite i2norm_tens i2norm1 gtn_eqF ?dim_proper// mulr1 i2norm_trmx.
apply/ler_pM=>//; last by apply/i2norm_trnorm.
by rewrite /choinorm mulrCA mulfV ?mulr1// gt_eqF// ltr0n dim_proper.
Qed.

Lemma sem_apply_summable I J U V s m x :
  summable (@sem_apply_def I J U V s m x).
Proof.
exists ((dim U)%:R * `|x|); near=>S.
apply/(le_trans (y := ((dim U)%:R * choinorm (psum (s m) S)) * `|x|)).
  rewrite -!psumE choinorm_cp_sum/= mulr_sumr mulr_suml; apply ler_sum=>i _.
  rewrite /normf /sem_apply_def; apply/test1.
by rewrite ler_wpM2r// ler_piMr// choinorm_qo.
Unshelve. end_near.
Qed.

HB.instance Definition _ I J U V s m x :=
  isSummable.Build _ _ _ (sem_apply_def _ _ _) (@sem_apply_summable I J U V s m x).

Lemma sem_apply_vdistr_ge0 I J U V (s : semType I J U V) m (x : 'FD(U)) :
  forall j : J, 0%:VF <= sem_apply_def s m x j.
Proof. by move=>j; rewrite /sem_apply_def cp_ge0// psdf_ge0. Qed.

Lemma sem_apply_vdistr_sum_le1 I J U V (s : semType I J U V) m (x : 'FD(U)) :
  `| sum (sem_apply_def s m x) | <= 1.
Proof.
rewrite /sum -lim_norm; first by apply: summable_cvg.
apply/etlim_le=>[|S].
  by apply: is_cvg_norm; apply: summable_cvg.
have ->: psum (sem_apply_def s m x) S = (psum (s m) S) x.
  by rewrite /psum /sem_apply_def soE.
by rewrite psd_trfnorm ?is_psdlf// denf_trlf.
Qed.

HB.instance Definition _ I J U V s m x := Summable_isVDistr.Build _ _ _ (sem_apply_def _ _ _)
  (@sem_apply_vdistr_ge0 I J U V s m x) (sem_apply_vdistr_sum_le1 s m x).

Definition sem_apply I J U V (s : semType I J U V) m (x : 'FD(U)) 
  : {vdistr J -> 'End(V)} := sem_apply_def s m x.
(* Figure 2*)
Fixpoint embedding (c : program) :=
  match c with 
  | skip => skip_ 
  | assign t x e => assign_ x e
  | cond b c1 c2 => cond_ b (embedding c1) (embedding c2)
  | while b c => while_ b (embedding c)
  | seqc c1 c2 => seqc_ (embedding c1) (embedding c2)
  | initial i => initial_ <{q.[i]}> ('0 : 'NS)%:CS
  | unitary1 i U => unitary_ <{q.[i]}> (Gate1_sem U)%:CS
  | unitary2 i j U => unitary_ <{(q.[i], q.[j])}> (Gate2_sem U)%:CS
  | measure x P => measure_ x q (expr_Pmeas P)
  end.

Definition program_sem (c : program) m (x : 'FD) := 
  sem_apply (sem_aux (embedding c)) m x.

End ProgramSem.
End Semantics.

Section AssertionLogic.
Local Open Scope hspace_scope.

(* Prop A.3 in appendix, basic inference rules for assertion logic *)
(* i.e., rules for orthomodular lattice also holds for AExp *)
Lemma Prop_A_3_1 (P Q : PExp) : (P && Q ⟚a P && (Q * P)%P)%A.
Proof.
split.
  move=>q m /=; apply/lehP=>v; 
  rewrite 2!memhI /Psem/= !espace1E=>/andP[]/eqP P1 /eqP P2.
  by rewrite P1 lfunE/= P1 P2 eqxx.
move=>q m /=; apply/lehP=>v; 
rewrite 2!memhI /Psem/= !espace1E=>/andP[]/eqP P1 /eqP P2.
by rewrite P1 eqxx/= -{1}P1 -comp_lfunE P2.
Qed.

Lemma Prop_A_3_2 b (P : PExp) : 
  ((SQ_bool b *: P)%P && (SQ_bool (~~b)%X *: P)%P ⟚a false%:CS)%A.
Proof.
split=>q m /=; last by apply le0h.
apply/lehP=>v; rewrite /= memhI /Psem/= !espace1E/=.
case: (esem b m)=>/=; rewrite expr0 expr1 scale1r realcN scaleN1r lfunE/=;
move=>/andP [] /eqP P1 /eqP P2; 
by rewrite memh0 -[v]scale1r -[1]split2 scalerDl -{1}P1 -{2}P2 -scalerDr ?addrN ?addNr scaler0.
Qed.

(* Section A.4 Figure 11, Hilbert style proof system *)
Lemma Prop_A_4_1 A : (~~ ~~ A ⊨a A)%A.
Proof. by move=>q m /=; rewrite hsOK. Qed.  

Lemma Prop_A_4_2 A : (A ⊨a A)%A.
Proof. by move=>m. Qed.

Lemma Prop_A_4_3 A : (A ⊨a true%:CS)%A.
Proof. by move=>q m /=; apply leh1. Qed.

Lemma Prop_A_4_4 A : (false%:CS ⊨a A)%A.
Proof. by move=>q m /=; apply le0h. Qed.

Lemma Prop_A_4_5 A B C : (A ⊨a B -> A ⊨a C -> A ⊨a B && C)%A.
Proof. by move=>P1 P2 q m /=; rewrite lehI P1 P2. Qed.

Lemma Prop_A_4_61 A B C : (A ⊨a B && C -> A ⊨a B)%A.
Proof. by move=>P q m; move: (P q m)=>/=/le_trans; apply; apply/lehIl. Qed.

Lemma Prop_A_4_6r A B C : (A ⊨a B && C -> A ⊨a C)%A.
Proof. by move=>P q m; move: (P q m)=>/=/le_trans; apply; apply/lehIr. Qed.

Lemma Prop_A_4_7 A B C : (A ⊨a B -> C && A ⊨a B)%A.
Proof. by move=>P q m; move: (P q m)=>/=; apply/le_trans/lehIr. Qed.

Lemma Prop_A_4_71 A B C : (C ⊨a B -> C && A ⊨a B)%A.
Proof. by move=>P q m; move: (P q m)=>/=; apply/le_trans/lehIl. Qed.

Lemma Prop_A_4_8 A B C : (A ⊨a B -> C ⊨a B -> A || C ⊨a B)%A.
Proof. by move=>P1 P2 q m /=; rewrite leUh P1 P2. Qed.

Lemma Prop_A_4_91 A B C : (A ⊨a B -> A ⊨a B || C)%A.
Proof. by move=>P q m /=; move: (P q m)=>/le_trans; apply; apply/lehUl. Qed.

Lemma Prop_A_4_92 A B C : (A ⊨a C -> A ⊨a B || C)%A.
Proof. by move=>P q m /=; move: (P q m)=>/le_trans; apply; apply/lehUr. Qed.

Lemma Prop_A_4_10 A B C : (A ⊨a B ==> C -> A ⊨a B -> A ⊨a C)%A.
Proof.
move=>P1 P2 q m; move: (P1 q m) (P2 q m)=>/= + P3.
rewrite -commute_leIx; first by apply/le_commute.
by apply/le_trans; rewrite caphl ?lehh.
Qed.

Definition Acommute A B := (A ⟚a (A && B) || (A && ~~ B))%A.

Lemma AcommuteP A B : Acommute A B <-> 
                        forall q m, (Asem q A m) _C_ (Asem q B m).
Proof.
rewrite /Acommute [X in X <-> _]Aentail_anti; split=>P.
  by move=>m; rewrite /commute/= {1}P.
by move=>q; apply/funext=>m; move: (P q m); rewrite /commute=>/eqP.
Qed.

Lemma AcommuteC A B : Acommute A B <-> Acommute B A.
Proof.
rewrite [X in X <-> _]AcommuteP [X in _ <-> X]AcommuteP; 
by split=>P q m; move: (P q m); rewrite commuteC.
Qed.

Lemma Acommute_bl b A : Acommute (A_BExp b) A.
Proof.
by apply/AcommuteP=>q m /=; case: (esem b m); rewrite ?commute1x ?commute0x.
Qed.

Lemma Acommute_br b A : Acommute A (A_BExp b).
Proof.
by apply/AcommuteP=>q m /=; case: (esem b m); rewrite ?commutex1 ?commutex0.
Qed.

Lemma Prop_A_4_11 A B C : (A && B ⊨a C -> Acommute A B -> A ⊨a B ==> C)%A.
Proof.
rewrite AcommuteP=>P1 P2 q m /=.
by rewrite -commute_leIx ?P1//.
Qed.

End AssertionLogic.

(* Definition A.7*)
Definition hoare q (A B : assertion) (c : program) :=
  forall (m : cmem) (r : 'FD(Hq)), (singleton m r ⊨fs A)%A ->
    (program_sem q c m r ⊨fs B)%A.

(* Definition 4.1*)
Definition Ahoare (A B : AExp) (c : program) := 
  forall q, hoare q (Asem q A) (Asem q B) c.

Section WeakestPrecondition.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology ComplLatticeSyntax.

Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Local Open Scope reg_scope.

Variable (q : 'QReg[Bool.[n.+1]]).
Local Notation hoare := (hoare q).
Local Notation embedding := (embedding q).
Local Notation program_sem := (program_sem q).
Local Notation Asem := (Asem q).

(* Definition A.8*)
Definition wlp (c : program) (A : assertion) : assertion :=
  fun i : cmem => (\caps_(o : cmem) kerh ((sem_aux (embedding c) i o)^*o (~` (A o)))).

Lemma hoare_wlp c A : hoare (wlp c A) A c.
Proof.
move=>m r; rewrite singleton_satisfy=>Pr.
move=>o; rewrite /= /sem_apply_def CP_supph_le_kerh/=.
by apply/(le_trans Pr); rewrite /wlp; apply/caps_inf.
Qed.

Lemma wlpP (c : program) (A : assertion) m r :
  (singleton m r ⊨fs wlp c A)%A <-> (program_sem c m r ⊨fs A)%A.
Proof.
split; first by apply/hoare_wlp.
move=>H; rewrite singleton_satisfy; apply/caps_lub=>o _.
by move: (H o); rewrite /= /sem_apply_def/= CP_supph_le_kerh.
Qed.

Lemma wlp_weakest (c : program) (A B : assertion) : 
  hoare A B c <-> (A ⊨fa wlp c B)%A.
Proof.
split=>[Ph m | H m r].
  apply/leh_suppP=>r Pr.
  move: (Ph m r); rewrite singleton_satisfy=>/(_ Pr).
  by rewrite -wlpP singleton_satisfy.
rewrite -wlpP=>+ o; move=>/(_ o)/le_trans; apply; apply/H.
Qed.

Lemma entail_antiP (A1 A2 : assertion) :
  (A1 ⟚fa A2)%A <-> (A1 = A2).
Proof. by split=>[/entail_anti|->]//; split; apply/entail_refl. Qed.

(* Corollary A.10 *)
Lemma wlp_alter (c : program) (A B : assertion) :
  (forall m r, (singleton m r ⊨fs A <-> program_sem c m r ⊨fs B)%A) ->
    (A ⟚fa wlp c B)%A.
Proof.
move=>H; split.
  by apply/wlp_weakest=>m r; move: (H m r)=>[].
move=>m /=; apply/leh_suppP=>r.
move: (H m r)=>[] _ + Pr; rewrite singleton_satisfy; apply.
by move: (@hoare_wlp c B m r); rewrite singleton_satisfy; apply.
Qed.

Lemma wlp_alterP (c : program) (A B : assertion) :
  (forall m r, (singleton m r ⊨fs A <-> program_sem c m r ⊨fs B)%A) <->
    (A ⟚fa wlp c B)%A.
Proof.
split; first by apply/wlp_alter.
rewrite entail_antiP=>->; apply/wlpP.
Qed.

Lemma unitary1_apply i (U : Gate1) m r : 
  let E := liftfso (formso (tf2f <{ q.[i] }> <{ q.[i] }> (Gate1_sem U))) in
    program_sem (unitary1 i U) m r = singleton m (E r).
Proof.
apply/vdistrP=>o/=; rewrite /sem_apply_def /sunit_def_lf/= /sunit_def;
by case: eqP=>//; rewrite soE.
Qed.

Lemma unitary2_apply i j (U : Gate2) m r : 
  let E := liftfso (formso (tf2f <{(q.[i],q.[j])}> <{(q.[i],q.[j])}> (Gate2_sem U))) in
    program_sem (unitary2 i j U) m r = singleton m (E r).
Proof.
apply/vdistrP=>o/=; rewrite /sem_apply_def /sunit_def_lf/= /sunit_def;
by case: eqP=>//; rewrite soE.
Qed.

(* wlp for X Y Z H S T CNOT CZ iSWAP *)
Lemma wlp_X i (A : AExp) :
  wlp (unitary1 i G_X) (Asem A) = Asem (AXsubst i A).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
rewrite unitary1_apply/=; apply/AXsubst_correct.
Qed.

Lemma wlp_Y i (A : AExp) :
  wlp (unitary1 i G_Y) (Asem A) = Asem (AYsubst i A).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
rewrite unitary1_apply/=; apply/AYsubst_correct.
Qed.

Lemma wlp_Z i (A : AExp) :
  wlp (unitary1 i G_Z) (Asem A) = Asem (AZsubst i A).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
rewrite unitary1_apply/=; apply/AZsubst_correct.
Qed.

Lemma wlp_H i (A : AExp) :
  wlp (unitary1 i G_H) (Asem A) = Asem (AHsubst i A).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
rewrite unitary1_apply/=; apply/AHsubst_correct.
Qed.

Lemma wlp_S i (A : AExp) :
  wlp (unitary1 i G_S) (Asem A) = Asem (ASsubst i A).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
rewrite unitary1_apply/=; apply/ASsubst_correct.
Qed.

Lemma wlp_T i (A : AExp) :
  wlp (unitary1 i G_T) (Asem A) = Asem (ATsubst i A).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
rewrite unitary1_apply/=; apply/ATsubst_correct.
Qed.

Lemma wlp_CNOT i j (A : AExp) : i != j ->
  wlp (unitary2 i j G_CNOT) (Asem A) = Asem (ACNOTsubst i j A).
Proof.
move=>nij; apply/esym/entail_anti/wlp_alter=>m r.
by rewrite unitary2_apply/=; apply/ACNOTsubst_correct.
Qed.

Lemma wlp_CZ i j (A : AExp) : i != j ->
  wlp (unitary2 i j G_CZ) (Asem A) = Asem (ACZsubst i j A).
Proof.
move=>nij; apply/esym/entail_anti/wlp_alter=>m r.
by rewrite unitary2_apply/=; apply/ACZsubst_correct.
Qed.

Lemma wlp_iSWAP i j (A : AExp) : i != j ->
  wlp (unitary2 i j G_iSWAP) (Asem A) = Asem (AiSWAPsubst i j A).
Proof.
move=>nij; apply/esym/entail_anti/wlp_alter=>m r.
by rewrite unitary2_apply/=; apply/AiSWAPsubst_correct.
Qed.

(* wlp for skip, init, meas, seq, if *)
Lemma wlp_skip (A : AExp) :
  wlp skip (Asem A) = Asem A.
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
suff ->:  singleton m r = program_sem skip m r by [].
apply/vdistrP=>o.
rewrite /= /sunit_def_lf /sem_apply_def skip_semE /sunit_def.
by case: eqP; rewrite soE.
Qed.

Lemma wlp_init i (A : AExp) :
  wlp (initial i) (Asem A) = Asem (AInitsubst i A).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
move: (Initsubst_correct q i A m r); rewrite /satisfaction=>->.
suff ->: singleton m (liftfso (initialso (tv2v <{ q.[i] }> '0)) r) = 
  program_sem (initial i) m r by [].
apply/vdistrP=>o.
rewrite /= /sunit_def_lf /sem_apply_def /initial_sem/= /sunit_def.
by case: eqP=>//; rewrite soE.
Qed.

Lemma wlp_assign {Tc : cType} (x : cvar Tc) (e : expr_ (evalCT Tc)) (A : AExp) :
  wlp (assign x e) (Asem A) = Asem (AExp_subst A x e).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
rewrite singleton_satisfy Asem_subst -singleton_satisfy.
suff ->: singleton (m.[x <- esem e m])%M r = program_sem (assign x e) m r by [].
apply/vdistrP=>o; rewrite /= /sunit_def_lf /sunit_def /assign_sem/= /sem_apply_def/= /sunit_def.
by case: eqP; rewrite soE.
Qed.

Lemma wlp_meas (x : cvar Bool) (P : PExp) (A : AExp) :
  wlp (measure x P) (Asem A) = 
    Asem ((P && A.[x <- false%:CS]) || (~~ P && A.[x <- true%:CS])).
Proof.
apply/esym/entail_anti/wlp_alter=>m r.
have Pm: (m.[x <- true])%M == (m.[x <- false])%M = false.
  by case: eqP=>// /(f_equal (fun y => cmget y QBool (cvname x))); rewrite !get_set_eq.
split.
  move=>H o /=; rewrite /sem_apply_def/= /sdlet_def fin_dom_sum big_bool/=.
  rewrite /sunit_def /smeas_def /elemso liftf_funE -esem_PExpET -esem_PExpEF.
  case: eqP=>[->| _]; rewrite ?Pm ?addr0 ?add0r; last first.
    case: eqP=>[->|]; last by rewrite soE supph0 le0h.
  1,2: rewrite -formlf_soE supph_formlf; move: (H m); 
    rewrite /singleton /sunit_def_lf/= /sunit_def_lf/= /sunit_def eqxx=>H1;
    apply/(le_trans (leJr _ H1)).
  by rewrite sprojxUyz sprojxIxy sprojxIOxy cuph0 Asem_subst/= lehIr.
  by rewrite sprojxUyz sprojOxIxy cup0h sprojxIxy Asem_subst/= lehIr.
move=>H; rewrite singleton_satisfy/=.
move: (H (m.[x <- false])%M) (H (m.[x <- true])%M).
rewrite /= /sem_apply_def/= /sdlet_def !fin_dom_sum !big_bool/= /sunit_def !eqxx Pm eq_sym Pm.
rewrite addr0 add0r /smeas_def /elemso liftf_funE -esem_PExpEF -esem_PExpET.
rewrite -!formlf_soE !supph_formlf !Asem_subst/=.
move=>/(lehI2l (Psem q P m)) H1 /(lehI2l (~` Psem q P m)) H2.
apply/(le_trans _ (lehU2 H1 H2)).
OM_autocomp (supph r) (Psem q P m).
Qed.

Lemma wlp_if b c1 c2 (A1 A2 B : AExp) :
  wlp c1 (Asem B) = Asem A1 -> wlp c2 (Asem B) = Asem A2 ->
    wlp (cond b c1 c2) (Asem B) = Asem ((b && A1) || (~~b && A2))%A.
Proof.
move=>H1 H2; apply/esym/entail_anti/wlp_alter=>m r.
rewrite singleton_satisfy/=.
case E: (esem b m).
  rewrite cap1h hsO1 cap0h cuph0 -H1 -(singleton_satisfy m) wlpP.
  suff ->: program_sem (cond b c1 c2) m r = program_sem c1 m r by [].
  by apply/vdistrP=>o; rewrite /= /sem_apply_def /if_sem/= E.
rewrite cap0h hsO0 cap1h cup0h -H2 -(singleton_satisfy m) wlpP.
suff ->: program_sem (cond b c1 c2) m r = program_sem c2 m r by [].
by apply/vdistrP=>o; rewrite /= /sem_apply_def /if_sem/= E.
Qed.

Lemma supph_seqc c1 c2 i r o : 
  supph (program_sem (seqc c1 c2) i r o) = 
    \cups_m supph (program_sem c2 m (program_sem c1 i r m) o).
Proof.
move: (pseries_ubounded_cvg (slet_norm_uboundW 
  (sem_aux (embedding c1)) (sem_aux (embedding c2)) i))=>[] _ []/(_ o) Po _.
rewrite /= /sem_apply_def/= /slet_def sum_summable_soE//.
rewrite supph_sum_le_inf/=; last by under eq_cupsr do rewrite soE.
by apply/sum_summable_soE_is_cvg.
Qed.

Lemma wlp_seq c1 c2 (A B C : AExp) :
  wlp c2 (Asem C) = Asem B -> wlp c1 (Asem B) = Asem A ->
    wlp (seqc c1 c2) (Asem C) = Asem A.
Proof.
move=>H1 H2.
apply/esym/entail_anti/wlp_alter=>i r.
rewrite -H2 wlpP -H1; split.
  move=>P1 o; rewrite supph_seqc; apply/cups_glb=>m _; move: (P1 m).
  by rewrite -[in X in X -> _](singleton_satisfy m) wlpP=>/(_ o).
move=>P1 m; rewrite -(singleton_satisfy m) wlpP=>o /=.
by move: (P1 o); rewrite supph_seqc; apply/le_trans; apply/cups_sup.
Qed.

End WeakestPrecondition.

Section ProofSystem.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.

(* Theorem 4.2, Soundess for the proof system*)
Lemma program_rule_sound (A B : AExp) c :
  program_rule A c B -> Ahoare A B c.
Proof.
rewrite /Ahoare; elim; clear.
- by intros; apply/wlp_weakest; rewrite wlp_skip.
- by intros; apply/wlp_weakest; rewrite wlp_init.
- by intros; apply/wlp_weakest; rewrite wlp_assign.
- by intros; apply/wlp_weakest; rewrite wlp_meas.
- by intros; apply/wlp_weakest; rewrite wlp_X.
- by intros; apply/wlp_weakest; rewrite wlp_Y.
- by intros; apply/wlp_weakest; rewrite wlp_Z.
- by intros; apply/wlp_weakest; rewrite wlp_H.
- by intros; apply/wlp_weakest; rewrite wlp_S.
- by intros; apply/wlp_weakest; rewrite wlp_T.
- by intros; apply/wlp_weakest; rewrite wlp_CNOT.
- by intros; apply/wlp_weakest; rewrite wlp_CZ.
- by intros; apply/wlp_weakest; rewrite wlp_iSWAP.
- move=>c1 c2 A B D _ H1 _ H2.
  move=>q i r /H1 P1 o. rewrite supph_seqc; apply/cups_glb=>m _; move: (P1 m).
  by rewrite -[in X in X -> _](singleton_satisfy m)=>/H2.
- move=>b c1 c2 A1 A2 B _ H1 _ H2 q m r.
  rewrite singleton_satisfy/=.
  case E: (esem b m).
    rewrite cap1h hsO1 cap0h cuph0 -(singleton_satisfy m)=>/H1.
    suff ->: program_sem q (cond b c1 c2) m r = program_sem q c1 m r by [].
    by apply/vdistrP=>o; rewrite /= /sem_apply_def /if_sem/= E.
  rewrite cap0h hsO0 cap1h cup0h -(singleton_satisfy m)=>/H2.
  suff ->: program_sem q (cond b c1 c2) m r = program_sem q c2 m r by [].
  by apply/vdistrP=>o; rewrite /= /sem_apply_def /if_sem/= E.
- move=>b c A _ H q m r P1 o.
  rewrite /= /sem_apply_def -while_sem_limEEE.
  apply/supph_lim_le.
    by apply: so_is_cvgl; apply: summableE_is_cvg; apply: while_sem_is_cvg.
  move=>i; elim: i o m r P1 =>[o m r P1 | i IH o m r P1 /=].
    by rewrite /= /sunit_def/=; case: eqP; rewrite soE supph0 le0h.
  case E: (esem b m); last first.
    rewrite /= /sunit_def; case: eqP=>[->|]; last by rewrite soE supph0 le0h.
    by move: P1; rewrite singleton_satisfy soE E hsO0 cap1h.
  move: (pseries_ubounded_cvg (slet_norm_uboundW (sem_aux (embedding q c))
    (while_sem_iter b (sem_aux (embedding q c)) i) m))=>[] _ []/(_ o) Po _.
  rewrite /= /slet_def sum_summable_soE//.
  rewrite supph_sum_le_inf/=; first by apply/sum_summable_soE_is_cvg.
  apply/cups_glb=>j _; rewrite soE; apply IH; rewrite singleton_satisfy/=.
  move: P1 H=> + /(_ q m r); rewrite !singleton_satisfy/= E cap1h=>P1 /(_ P1 j).
  by rewrite /= /sem_apply_def.
- move=>c A A' B B' + _ + + q.
  by move=>/(_ q)/entail_alter PA /(_ q) H /(_ q)/entail_alter PB m r /PA/H/PB.
Qed.

(* for two-qubit gate, we require that i != j *)
Fixpoint wf_program (c : program) : bool :=
  match c with 
  | skip => true 
  | assign t x e => true
  | cond b c1 c2 => (wf_program c1) && (wf_program c2)
  | while b c => wf_program c
  | seqc c1 c2 => (wf_program c1) && (wf_program c2)
  | initial i => true
  | unitary1 i U => true
  | unitary2 i j U => i != j
  | measure x P => true
  end.

(* program without loops *)
Fixpoint finite_program (c : program) : bool :=
  match c with 
  | skip => true 
  | assign t x e => true
  | cond b c1 c2 => (finite_program c1) && (finite_program c2)
  | while b c => false
  | seqc c1 c2 => (finite_program c1) && (finite_program c2)
  | initial i => true
  | unitary1 i U => true
  | unitary2 i j U => true
  | measure x P => true
  end.

(* Theorem A.11 in appendix, Weak definability for programs without loops*)
Lemma definability c (B : AExp) :
  wf_program c -> finite_program c -> 
    exists A, forall q, wlp q c (Asem q B) = Asem q A.
Proof.
elim: c B=>//=.
- by move=>B _ _; exists B=>q; rewrite wlp_skip.
- by move=> t c e B _ _; exists (B.[c <- e])%A=>q; rewrite wlp_assign.
- move=>b c1 IH1 c2 IH2 B /andP[] P11 P21 /andP[] P12 P22.
  move: (IH1 B P11 P12) (IH2 B P21 P22)=>[A1] PA1 [A2] PA2.
  by exists (b && A1 || ~~ b && A2)%A=>q; rewrite (wlp_if b (PA1 q) (PA2 q)).
- move=>c1 IH1 c2 IH2 B /andP[] P11 P21 /andP[] P12 P22.
  move: (IH2 B P21 P22)=>[A2] PA2.
  move: (IH1 A2 P11 P12)=>[A1] PA1.
  by exists A1=>q; rewrite (wlp_seq (PA2 q) (PA1 q)).
- by move=>i B _ _; exists (AInitsubst i B)=>q; rewrite wlp_init.
- move=>i [] B _ _.
  + by exists (AXsubst i B)=>q; rewrite wlp_X.
  + by exists (AYsubst i B)=>q; rewrite wlp_Y.
  + by exists (AZsubst i B)=>q; rewrite wlp_Z.
  + by exists (AHsubst i B)=>q; rewrite wlp_H.
  + by exists (ASsubst i B)=>q; rewrite wlp_S.
  + by exists (ATsubst i B)=>q; rewrite wlp_T.
- move=>i j [] B nij _.
  + by exists (ACNOTsubst i j B)=>q; rewrite wlp_CNOT.
  + by exists (ACZsubst i j B)=>q; rewrite wlp_CZ.
  + by exists (AiSWAPsubst i j B)=>q; rewrite wlp_iSWAP.
- move=>c P B _ _.
  by exists (P && B.[c <- false%:CS] || ~~ P && B.[c <- true%:CS])%A=>q; rewrite wlp_meas.
Qed.

Lemma R_conl c A A' B :
  (A ⊨a A')%A -> program_rule A' c B -> program_rule A c B.
Proof. by move=>PA Pc; apply/(R_con PA Pc (Aentail_refl _)). Qed.

(* Theorem 4.3 weak relative completeness for finite programs*)
Lemma program_rule_complete c (A B : AExp) :
  wf_program c -> finite_program c -> Ahoare A B c -> program_rule A c B.
Proof.
elim: c A B=>//=; rewrite /Ahoare.
- move=>A B ?? H; apply/(R_conl _ (R_skip _))=>q.
  by move: (H q)=>/wlp_weakest; rewrite wlp_skip.
- move=>??? A B ?? H; apply/(R_conl _ (R_assign _ _ _))=>q.
  by move: (H q)=>/wlp_weakest; rewrite wlp_assign.
- move=>b c1 IH1 c2 IH2 A B /andP[] P11 P21 /andP[] P12 P22 H.
  move: (definability B P11 P12) (definability B P21 P22)=>[A1 P1] [A2 P2].
  apply/(R_conl _ (R_cond _ (A1 := A1) (A2 := A2) _ _)).
  + by move=>q; move: (H q)=>/wlp_weakest; rewrite (wlp_if b (P1 q) (P2 q)).
  + by apply/IH1=>[//|//|q]; rewrite -P1; apply hoare_wlp.
  + by apply/IH2=>[//|//|q]; rewrite -P2; apply hoare_wlp.
- move=>c1 IH1 c2 IH2 A B /andP[] P11 P21 /andP[] P12 P22 H.
  move: (definability B P21 P22)=>[A2 P2].
  move: (definability A2 P11 P12)=>[A1 P1].
  apply/(R_conl _ (R_seqc (A := A1) (B := A2) _ _)).
  + by move=>q; move: (H q)=>/wlp_weakest; rewrite /= (wlp_seq (P2 q) (P1 q)).
  + apply/IH1=>[//|//|q]; rewrite -P1; apply hoare_wlp.
  + apply/IH2=>[//|//|q]; rewrite -P2; apply hoare_wlp.
- move=>i A B _ _ H; apply/(R_conl _ (R_initial _ _))=>q.
  by move: (H q)=>/wlp_weakest; rewrite wlp_init.
- move=>i [] A B _ _ H.
  + by apply/(R_conl _ (R_X _ _))=>q; move: (H q)=>/wlp_weakest; rewrite wlp_X.
  + by apply/(R_conl _ (R_Y _ _))=>q; move: (H q)=>/wlp_weakest; rewrite wlp_Y.
  + by apply/(R_conl _ (R_Z _ _))=>q; move: (H q)=>/wlp_weakest; rewrite wlp_Z.
  + by apply/(R_conl _ (R_H _ _))=>q; move: (H q)=>/wlp_weakest; rewrite wlp_H.
  + by apply/(R_conl _ (R_S _ _))=>q; move: (H q)=>/wlp_weakest; rewrite wlp_S.
  + by apply/(R_conl _ (R_T _ _))=>q; move: (H q)=>/wlp_weakest; rewrite wlp_T.
- move=>i j [] A B nij _ H.
  + apply/(R_conl _ (R_CNOT _ nij))=>q; 
    by move: (H q)=>/wlp_weakest; rewrite wlp_CNOT.
  + apply/(R_conl _ (R_CZ _ nij))=>q; 
    by move: (H q)=>/wlp_weakest; rewrite wlp_CZ.
  + apply/(R_conl _ (R_iSWAP _ nij))=>q; 
    by move: (H q)=>/wlp_weakest; rewrite wlp_iSWAP.
- move=>c P A B _ _ H; apply/(R_conl _ (R_measure _ _ _))=>q.
  by move: (H q)=>/wlp_weakest; rewrite wlp_meas.
Qed.

End ProofSystem.

End ProgramLogic.

Notation "P + Q" := (P_Add P%P Q%P) : psyn_scope.
Notation "a *: P" := (P_Scale a%SQ P%P) : psyn_scope.
Notation "P * Q" := (P_Mul P%P Q%P) : psyn_scope.

Notation "~~ A" := (A_neg A%A) : asyn_scope.
Notation "A && B" := (A_and A%A B%A) : asyn_scope.
Notation "A || B" := (A_or A%A B%A) : asyn_scope.
Notation "A ==> B" := (A_imply A%A B%A) : asyn_scope.

Notation "P .[ x <- s ]" := (PExp_subst P%P x s%X) : psyn_scope.

Notation "P .[ j ; Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]" := 
    (PExp_subst1 P%P j Xs%P Ys%P Zs%P) 
    (at level 1, left associativity, 
    format "P .[ j ;  Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]"): psyn_scope.

Notation "P .[ i , j ; Xi '<-Xi,' Yi '<-Yi,' Zi '<-Zi,' Xj '<-Xj,' Yj '<-Yj,' Zj '<-Zj' ]" := 
    (PExp_subst2 P%P i j Xi%P Yi%P Zi%P Xj%P Yj%P Zj%P) 
    (at level 1, left associativity, 
    format "P .[ i ,  j ;  Xi '<-Xi,'  Yi '<-Yi,'  Zi '<-Zi,'  Xj '<-Xj,'  Yj '<-Yj,'  Zj '<-Zj' ]") : psyn_scope.

Notation "A .[ x <- s ]" := (AExp_subst A%P x s%X) : asyn_scope.

Notation "A .[ j ; Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]" := 
    (AExp_subst1 A%A j Xs%P Ys%P Zs%P) 
    (at level 1, left associativity, 
    format "A .[ j ;  Xs '<-X,'  Ys '<-Y,'  Zs '<-Z' ]"): asyn_scope.

Notation "A .[ i , j ; Xi '<-Xi,' Yi '<-Yi,' Zi '<-Zi,' Xj '<-Xj,' Yj '<-Yj,' Zj '<-Zj' ]" := 
    (AExp_subst2 A%A i j Xi%P Yi%P Zi%P Xj%P Yj%P Zj%P) 
    (at level 1, left associativity, 
    format "A .[ i ,  j ;  Xi '<-Xi,'  Yi '<-Yi,'  Zi '<-Zi,'  Xj '<-Xj,'  Yj '<-Yj,'  Zj '<-Zj' ]") : asyn_scope.

Notation "A1 '⊨a' A2" := (Aentail A1%A A2%A) (at level 70) : asyn_scope.
Notation "A1 '⟚a' A2" := (Aentail A1%A A2%A /\ Aentail A2%A A1%A) (at level 70) : asyn_scope.

Reserved Notation "c1 ;; c2"
  (at level 74, left associativity, format "'[' c1  ;;  '/' '[' c2 ']' ']'").
Reserved Notation "x <<- e"
  (at level 65, e at level 70, no associativity, format "x  <<-  e").
Reserved Notation "x <m- 'Meas' [ y ]"
  (at level 65, no associativity, format "x  <m-  'Meas' [ y ]").
Reserved Notation "[{ x }] <:- '|0>'"
  (at level 65, no associativity, format "[{ x }]  <:-  |0>").
Reserved Notation "[{ x }] <*- 'X'"
  (at level 65, no associativity, format "[{ x }]  <*-  X").
Reserved Notation "[{ b , x }] <*- 'X'"
  (at level 65, x at next level, no associativity, format "[{ b ,  x }]  <*-  X").
Reserved Notation "[{ x }] <*- 'Y'"
  (at level 65, no associativity, format "[{ x }]  <*-  Y").
Reserved Notation "[{ b , x }] <*- 'Y'"
  (at level 65, x at next level, no associativity, format "[{ b ,  x }]  <*-  Y").
Reserved Notation "[{ x }] <*- 'Z'"
  (at level 65, no associativity, format "[{ x }]  <*-  Z").
Reserved Notation "[{ b , x }] <*- 'Z'"
  (at level 65, x at next level, no associativity, format "[{ b ,  x }]  <*-  Z").
Reserved Notation "'If' e 'then' c1 'else' c2"
  (at level 65, right associativity).
Reserved Notation "'If' e 'then' '{' c1 '}' 'else' '{' c2 '}'"
  (at level 65, right associativity, 
  format "'[v' 'If'  e  'then'  '{' '/' '['     c1 ']' '/' '}'  'else'  '{' '/' '['     c2 ']' '/' '}' ']'").
Reserved Notation "'IfT' e 'then' c1"
  (at level 65, right associativity).
Reserved Notation "'IfT' e 'then' '{' c1 '}'"
  (at level 65, right associativity, format
     "'[v' 'IfT'  e  'then'  '{' '/' '['     c1 ']' '/' '}' ']'").
Reserved Notation "'While' e 'Do' c"
  (at level 65, no associativity).
Reserved Notation "'While' e 'Do' '{' c '}' "
  (at level 65, no associativity, format
     "'[v' 'While'  e  'Do'  '{' '/' '['     c ']' '/' '}' ']'").
Reserved Notation "[ 'for' i 'do' F ]" 
  (at level 0, i at level 50, no associativity, format "[ 'for'  i  'do'  F ]").
Reserved Notation "[ 'for' i <- r | P 'do' F ]" 
  (at level 0, i,r at level 50, no associativity, format "[ 'for'  i  <-  r  |  P  'do'  F ]").
Reserved Notation "[ 'for' i <- r 'do' F ]" 
  (at level 0, i,r at level 50, no associativity, format "[ 'for'  i  <-  r  'do'  F ]").
Reserved Notation "[ 'for' m <= i < n | P 'do' F ]" 
  (at level 0, i,m,n at level 50, no associativity, format "[ 'for'  m  <=  i  <  n  |  P  'do'  F ]").
Reserved Notation "[ 'for' m <= i < n 'do' F ]" 
  (at level 0, i,m,n at level 50, no associativity, format "[ 'for'  m  <=  i  <  n  'do'  F ]").
Reserved Notation "[ 'for' i | P 'do' F ]" 
  (at level 0, i at level 50, no associativity, format "[ 'for'  i  |  P  'do'  F ]").
Reserved Notation "[ 'for' i : t | P 'do' F ]" 
  (at level 0, i at level 50, no associativity). (* only parsing *)
Reserved Notation "[ 'for' i : t 'do' F ]" 
  (at level 0, i at level 50, no associativity). (* only parsing *)
Reserved Notation "[ 'for' i < n | P 'do' F ]" 
  (at level 0, i,n at level 50, no associativity, format "[ 'for'  i  <  n  |  P  'do'  F ]").
Reserved Notation "[ 'for' i < n 'do' F ]" 
  (at level 0, i,n at level 50, no associativity, format "[ 'for'  i  <  n  'do'  F ]").
Reserved Notation "[ 'for' i 'in' A | P 'do' F ]" 
  (at level 0, i,A at level 50, no associativity, format "[ 'for'  i  'in'  A  |  P  'do'  F ]").
Reserved Notation "[ 'for' i 'in' A 'do' F ]" 
  (at level 0, i,A at level 50, no associativity, format "[ 'for'  i  'in'  A  'do'  F ]").

Notation "'SKIP'" := (@skip _) : vsyn_scope.
Notation " c1 ';;' c2 " := (seqc  c1%V c2%V) : vsyn_scope.
Notation "x <<- e" := (@assign _ _ x e%X) : vsyn_scope.
Notation "'If' e 'then' c1 'else' c2" := (@cond _ e%X c1%V c2%V) : vsyn_scope.
Notation "'If' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (@cond _ e%X c1%V c2%V) : vsyn_scope.
Notation "'IfT' e 'then' c1" := (@cond _ e%X c1%V (@skip _)) : vsyn_scope.
Notation "'IfT' e 'then' '{' c1 '}'" := (@cond _ e%X c1%V (@skip _)) : vsyn_scope.
Notation "'While' e 'Do' c" := (@while _ e%X c%V) : vsyn_scope.
Notation "'While' e 'Do' '{' c '}' " := (@while _ e%X c%V) : vsyn_scope.
Notation "x <m- 'Meas' [ y ]" := (@measure _ x y%P) : vsyn_scope.
Notation "[{ x }] <:- '|0>'" := (@initial _ x) : vsyn_scope.
Notation "[{ x }] <*- 'X'" := (@unitary1 _ x G_X) : vsyn_scope.
Notation "[{ b , x }] <*- 'X'" := (@cond _ b%X (@unitary1 _ x G_X) (@skip _)) : vsyn_scope.
Notation "[{ x }] <*- 'Y'" := (@unitary1 _ x G_Y) : vsyn_scope.
Notation "[{ b , x }] <*- 'Y'" := (@cond _ b%X (@unitary1 _ x G_Y) (@skip _)) : vsyn_scope.
Notation "[{ x }] <*- 'Z'" := (@unitary1 _ x G_Z) : vsyn_scope.
Notation "[{ b , x }] <*- 'Z'" := (@cond _ b%X (@unitary1 _ x G_Z) (@skip _)) : vsyn_scope.
Notation "[ 'for' i <- r | P 'do' F ]" :=
  (\big[@seqc _ / @skip _ ]_(i <- r | P%B) F%V) : vsyn_scope.
Notation "[ 'for' i <- r 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i <- r) F%V) : vsyn_scope.
Notation "[ 'for' m <= i < n | P 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(m <= i < n | P%B) F%V) : vsyn_scope.
Notation "[ 'for' m <= i < n 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(m <= i < n) F%V) : vsyn_scope.
Notation "[ 'for' i | P 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i | P%B) F%V) : vsyn_scope.
Notation "[ 'for' i 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_i F%V) : vsyn_scope.
Notation "[ 'for' i : t | P 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i : t | P%B) F%V) (only parsing) : vsyn_scope.
Notation "[ 'for' i : t 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i : t) F%V) (only parsing) : vsyn_scope.
Notation "[ 'for' i < n | P 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i < n | P%B) F%V) : vsyn_scope.
Notation "[ 'for' i < n 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i < n) F%V) : vsyn_scope.
Notation "[ 'for' i 'in' A | P 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i in A | P%B) F%V) : vsyn_scope.
Notation "[ 'for' i 'in' A 'do' F ]" :=
  (\big[@seqc _ /@skip _ ]_(i in A) F%V) : vsyn_scope.

(* Section 4.2 Inference rules for conditional Pauli gates are correct*)
Section ExtraRule.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope vsyn_scope.

Variable (n : nat).
Local Notation program := (program n).
Local Notation PExp := (PExp n).
Local Notation AExp := (AExp n).

Definition AXCsubst i b (A : AExp) := 
  (A.[i; (P_X i)<-X, (SQ_bool b *: (P_Y i))<-Y, (SQ_bool b *: (P_Z i))<-Z])%A.

Definition AYCsubst i b (A : AExp) := 
  (A.[i; (SQ_bool b *: (P_X i))<-X, (P_Y i)<-Y, (SQ_bool b *: (P_Z i))<-Z])%A.

Definition AZCsubst i b (A : AExp) := 
  (A.[i; (SQ_bool b *: (P_X i))<-X, (SQ_bool b *: (P_Y i))<-Y, (P_Z i)<-Z])%A.

Definition PXCsubst i b (P : PExp) := 
  (P.[i; (P_X i)<-X, (SQ_bool b *: (P_Y i))<-Y, (SQ_bool b *: (P_Z i))<-Z])%P.

Definition PYCsubst i b (P : PExp) := 
  (P.[i; (SQ_bool b *: (P_X i))<-X, (P_Y i)<-Y, (SQ_bool b *: (P_Z i))<-Z])%P.

Definition PZCsubst i b (P : PExp) := 
  (P.[i; (SQ_bool b *: (P_X i))<-X, (SQ_bool b *: (P_Y i))<-Y, (P_Z i)<-Z])%P.

Ltac temp b := case: (esem b _); rewrite ?sq_N1E ?expr0 ?expr1 ?realcN
  ?scaleN1r ?scale1r ?hsO1 ?hsO0 ?cap1h ?cap0h ?cuph0 ?cup0h.

Lemma PXCsubst_correct i (b : bexpr) (P : PExp) q m :
  (esem b m -> Pfsem q (PXCsubst i b P) m = Pfsem q (PXsubst i P) m) /\
  (~~ esem b m -> Pfsem q (PXCsubst i b P) m = Pfsem q P m).
Proof.
elim: P; rewrite /PXCsubst /PXsubst/=.
by move=>j; case: eqP=>[->| _].
by move=>j; case: eqP=>[->| _]/=; temp b.
by move=>j; case: eqP=>[->| _]/=; temp b.
by move=>a P; temp b=>[[->//]|[_ ->//]].
by move=>P1 + P2; temp b=>[[->// _][->//]|[_ ->//][_ ->]].
by move=>P1 + P2; temp b=>[[->// _][->//]|[_ ->//][_ ->]].
Qed.

Lemma PYCsubst_correct i (b : bexpr) (P : PExp) q m :
  (esem b m -> Pfsem q (PYCsubst i b P) m = Pfsem q (PYsubst i P) m) /\
  (~~ esem b m -> Pfsem q (PYCsubst i b P) m = Pfsem q P m).
Proof.
elim: P; rewrite /PYCsubst /PYsubst/=.
by move=>j; case: eqP=>[->|]/=; temp b.
by move=>j; case: eqP=>[->| _].
by move=>j; case: eqP=>[->| _]/=; temp b.
by move=>a P; temp b=>[[->//]|[_ ->//]].
by move=>P1 + P2; temp b=>[[->// _][->//]|[_ ->//][_ ->]].
by move=>P1 + P2; temp b=>[[->// _][->//]|[_ ->//][_ ->]].
Qed.

Lemma PZCsubst_correct i (b : bexpr) (P : PExp) q m :
  (esem b m -> Pfsem q (PZCsubst i b P) m = Pfsem q (PZsubst i P) m) /\
  (~~ esem b m -> Pfsem q (PZCsubst i b P) m = Pfsem q P m).
Proof.
elim: P; rewrite /PZCsubst /PZsubst/=.
by move=>j; case: eqP=>[->| _]/=; temp b.
by move=>j; case: eqP=>[->| _]/=; temp b.
by move=>j; case: eqP=>[->| _].
by move=>a P; temp b=>[[->//]|[_ ->//]].
by move=>P1 + P2; temp b=>[[->// _][->//]|[_ ->//][_ ->]].
by move=>P1 + P2; temp b=>[[->// _][->//]|[_ ->//][_ ->]].
Qed.

Lemma eq_leP (disp : Order.disp_t) (T : porderType disp) (a b : T) :
  a = b -> (a <= b)%O.
Proof. by move=>->. Qed.

Lemma R_X_cond i b A : program_rule (AXCsubst i b A) ([{ b , i }] <*- X)%V A.
Proof.
apply/(R_conl _ (R_cond _ (R_X _ _) (R_skip _)))=>q m.
apply/eq_leP; elim: A=>/=.
- by move=>b1; temp b.
- move=>P; move: (PXCsubst_correct i b P q m); rewrite /Psem/=.
  by temp b=>[[->//]|[_ ->//]].
- by move=>A ->; temp b.
all: by move=>A1 -> A2 ->; temp b.
Qed.

Lemma R_Y_cond i b A : program_rule (AYCsubst i b A) ([{ b , i }] <*- Y)%V A.
Proof.
apply/(R_conl _ (R_cond _ (R_Y _ _) (R_skip _)))=>q m.
apply/eq_leP; elim: A=>/=.
- by move=>b1; temp b.
- move=>P; move: (PYCsubst_correct i b P q m); rewrite /Psem/=.
  by temp b=>[[->//]|[_ ->//]].
- by move=>A ->; temp b.
all: by move=>A1 -> A2 ->; temp b.
Qed.

Lemma R_Z_cond i b A : program_rule (AZCsubst i b A) ([{ b , i }] <*- Z)%V A.
Proof.
apply/(R_conl _ (R_cond _ (R_Z _ _) (R_skip _)))=>q m.
apply/eq_leP; elim: A=>/=.
- by move=>b1; temp b.
- move=>P; move: (PZCsubst_correct i b P q m); rewrite /Psem/=.
  by temp b=>[[->//]|[_ ->//]].
- by move=>A ->; temp b.
all: by move=>A1 -> A2 ->; temp b.
Qed.

End ExtraRule.
