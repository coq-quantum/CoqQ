From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
Require Import mcextra mcaextra notation mxpred extnum ctopology svd mxnorm.
Require Import hermitian inhabited prodvect.
From quantum Require Import tensor.
Require Import quantum orthomodular.
Require Import hspace hspace_extra inhabited summable qreg qmem cqwhile qtype.
From quantum.dirac Require Import hstensor.
Require Import preliminary logic.
From Stdlib Require Import Program.Equality String.
From Stdlib Require Import Relation_Definitions Setoid.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Local Notation R := hermitian.R.
Local Notation C := hermitian.C.


(****************************************************************************)
(*      A formalization of Repetition code, the simplest scalable code.     *)
(*       The stabilizer generators are Z_1Z_2, Z_2Z_3, ... Z_{n-1}Z_n.      *)
(*   For odd number n = 2k + 1, it is able to correct any k Pauli X error.  *)
(*                      We show that for any k >= 1,                        *)
(*      the verification condition can be formally derived and proved,      *)
(*           with the aid ofthe explicit results from the decoder.          *)
(****************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

HB.lock
Definition eq_expr T (e1 e2 : expr_ T) := forall m, esem e1 m = esem e2 m.
HB.lock 
Definition eq_SQExp (s1 s2 : SQExp) := forall m, sqsem s1 m = sqsem s2 m.
HB.lock
Definition eq_PExp n (P1 P2 : PExp n) := forall q m, Pfsem q P1 m = Pfsem q P2 m.
HB.lock
Definition eq_AExp n (A1 A2 : AExp n) := forall q m, Asem q A1 m = Asem q A2 m.

Notation "e1 =e e2" := (eq_expr e1%X e2%X) (at level 70).
Notation "s1 =s s2" := (eq_SQExp s1%SQ s2%SQ) (at level 70).
Notation "P1 =p P2" := (eq_PExp P1%P P2%P) (at level 70).
Notation "A1 =a A2" := (eq_AExp A1%A A2%A) (at level 70).

(* Facilitate usage, we introduce satoid rewrite for assertions *)

Lemma eq_expr_refl T (e : expr_ T) : e =e e.
Proof. by rewrite eq_expr.unlock. Qed.
Lemma eq_expr_sym T (e1 e2 : expr_ T) : e1 =e e2 -> e2 =e e1.
Proof. by rewrite eq_expr.unlock=>H m; rewrite H. Qed.
Lemma eq_expr_trans T (e1 e2 e3 : expr_ T) : e1 =e e2 -> e2 =e e3 -> e1 =e e3.
Proof. by rewrite eq_expr.unlock=>H1 H2 m; rewrite H1. Qed.

Lemma eq_SQExp_refl (s : SQExp) : s =s s.
Proof. by rewrite eq_SQExp.unlock. Qed.
Lemma eq_SQExp_sym (s1 s2 : SQExp) : s1 =s s2 -> s2 =s s1.
Proof. by rewrite eq_SQExp.unlock=>H m; rewrite H. Qed.
Lemma eq_SQExp_trans (s1 s2 s3 : SQExp) : s1 =s s2 -> s2 =s s3 -> s1 =s s3.
Proof. by rewrite eq_SQExp.unlock=>H1 H2 m; rewrite H1. Qed.

Lemma eq_PExp_refl n (P : PExp n) : P =p P.
Proof. by rewrite eq_PExp.unlock. Qed.
Lemma eq_PExp_sym n (P1 P2 : PExp n) : P1 =p P2 -> P2 =p P1.
Proof. by rewrite eq_PExp.unlock=>H q m; rewrite H. Qed.
Lemma eq_PExp_trans n (P1 P2 P3 : PExp n) : P1 =p P2 -> P2 =p P3 -> P1 =p P3.
Proof. by rewrite eq_PExp.unlock=>H1 H2 q m; rewrite H1. Qed.

Lemma eq_AExp_refl n (A : AExp n) : A =a A.
Proof. by rewrite eq_AExp.unlock. Qed.
Lemma eq_AExp_sym n (A1 A2 : AExp n) : A1 =a A2 -> A2 =a A1.
Proof. by rewrite eq_AExp.unlock=>H q m; rewrite H. Qed.
Lemma eq_AExp_trans n (A1 A2 A3 : AExp n) : A1 =a A2 -> A2 =a A3 -> A1 =a A3.
Proof. by rewrite eq_AExp.unlock=>H1 H2 q m; rewrite H1. Qed.

#[global] Hint Extern 0 (eq_expr _ _) => apply: eq_expr_refl : core.
#[global] Hint Extern 0 (eq_SQExp _ _) => apply: eq_SQExp_refl : core.
#[global] Hint Extern 0 (eq_PExp _ _) => apply: eq_PExp_refl : core.
#[global] Hint Extern 0 (eq_AExp _ _) => apply: eq_AExp_refl : core.
#[global] Hint Extern 0 (Aentail _ _) => apply: Aentail_refl : core.

Add Parametric Relation T : (expr_ T) (@eq_expr T)
  reflexivity proved by (@eq_expr_refl T)
  symmetry proved by (@eq_expr_sym T)
  transitivity proved by (@eq_expr_trans T)
  as eq_expr_rel.

Add Parametric Relation : SQExp eq_SQExp
  reflexivity proved by eq_SQExp_refl
  symmetry proved by eq_SQExp_sym
  transitivity proved by eq_SQExp_trans
  as eq_SQExp_rel.

Add Parametric Relation n : (PExp n) (@eq_PExp n)
  reflexivity proved by (@eq_PExp_refl n)
  symmetry proved by (@eq_PExp_sym n)
  transitivity proved by (@eq_PExp_trans n)
  as eq_PExp_rel.

Add Parametric Relation n : (AExp n) (@eq_AExp n)
  reflexivity proved by (@eq_AExp_refl n)
  symmetry proved by (@eq_AExp_sym n)
  transitivity proved by (@eq_AExp_trans n)
  as eq_AExp_rel.

Add Parametric Morphism {Te Ue} : (@app_ Te Ue)
  with signature (@eq_expr (Te -> Ue)) ==> (@eq_expr Te) 
    ==> (@eq_expr Ue) as eq_expr_app.
Proof.
move=> e1 e2 + e3 e4; rewrite eq_expr.unlock => + + m /=.
by move=>/(_ m) -> /(_ m) ->.
Qed.

Add Parametric Morphism : SQ_bool
  with signature (@eq_expr bool) ==> eq_SQExp as eq_SQExp_SQ_bool.
Proof.
move=> e1 e2; rewrite eq_expr.unlock eq_SQExp.unlock/==> + m.
by move=>/(_ m)->.
Qed.

Add Parametric Morphism : SQ_div2
  with signature eq_SQExp ==> (@eq_expr nat) 
    ==> eq_SQExp as eq_SQExp_SQ_div2.
Proof.
move=> s1 s2 + e1 e2; rewrite eq_expr.unlock eq_SQExp.unlock/==> + + m.
by move=>/(_ m)-> /(_ m)->.
Qed.

Add Parametric Morphism : SQ_add
  with signature eq_SQExp ==> eq_SQExp
    ==> eq_SQExp as eq_SQExp_SQ_add.
Proof.
move=> s1 s2 + s3 s4; rewrite eq_SQExp.unlock/==> + + m.
by move=>/(_ m)-> /(_ m)->.
Qed.

Add Parametric Morphism : SQ_opp
  with signature eq_SQExp ==> eq_SQExp as eq_SQExp_SQ_opp.
Proof.
move=> s1 s2; rewrite eq_SQExp.unlock/==> + m.
by move=>/(_ m)->.
Qed.

Add Parametric Morphism : SQ_mul
  with signature eq_SQExp ==> eq_SQExp
    ==> eq_SQExp as eq_SQExp_SQ_mul.
Proof.
move=> s1 s2 + s3 s4; rewrite eq_SQExp.unlock/==> + + m.
by move=>/(_ m)-> /(_ m)->.
Qed.

Add Parametric Morphism {n} : (@P_Scale n)
  with signature eq_SQExp ==> (@eq_PExp n)
    ==> (@eq_PExp n) as eq_PExp_P_Scale.
Proof.
move=> s1 s2 + P1 P2; rewrite eq_SQExp.unlock eq_PExp.unlock/==> + + q m.
by move=>/(_ m)->/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@P_Add n)
  with signature (@eq_PExp n) ==> (@eq_PExp n)
    ==> (@eq_PExp n) as eq_PExp_P_Add.
Proof.
move=> P1 P2 + P3 P4; rewrite eq_PExp.unlock/==> + + q m.
by move=>/(_ q m)->/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@P_Mul n)
  with signature (@eq_PExp n) ==> (@eq_PExp n)
    ==> (@eq_PExp n) as eq_PExp_P_Mul.
Proof.
move=> P1 P2 + P3 P4; rewrite eq_PExp.unlock/==> + + q m.
by move=>/(_ q m)->/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@A_BExp n)
  with signature (@eq_expr bool) ==> (@eq_AExp n) as eq_AExp_A_BExp.
Proof.
move=> e1 e2; rewrite eq_expr.unlock eq_AExp.unlock/==> + q m.
by move=>/(_ m)->.
Qed.

Add Parametric Morphism {n} : (@A_PExp n)
  with signature (@eq_PExp n) ==> (@eq_AExp n) as eq_AExp_A_PExp.
Proof.
move=> P1 P2; rewrite eq_PExp.unlock eq_AExp.unlock/==> + q m.
by rewrite /Psem/= =>/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@A_neg n)
  with signature (@eq_AExp n) ==> (@eq_AExp n) as eq_AExp_A_neg.
Proof.
move=> A1 A2; rewrite eq_AExp.unlock/==> + q m.
by move=>/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@A_and n)
  with signature (@eq_AExp n) ==> (@eq_AExp n) 
    ==> (@eq_AExp n) as eq_AExp_A_and.
Proof.
move=> A1 A2 + A3 A4; rewrite eq_AExp.unlock/==> + + q m.
by move=>/(_ q m)->/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@A_or n)
  with signature (@eq_AExp n) ==> (@eq_AExp n) 
    ==> (@eq_AExp n) as eq_AExp_A_or.
Proof.
move=> A1 A2 + A3 A4; rewrite eq_AExp.unlock/==> + + q m.
by move=>/(_ q m)->/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@A_imply n)
  with signature (@eq_AExp n) ==> (@eq_AExp n) 
    ==> (@eq_AExp n) as eq_AExp_A_imply.
Proof.
move=> A1 A2 + A3 A4; rewrite eq_AExp.unlock/==> + + q m.
by move=>/(_ q m)->/(_ q m)->.
Qed.

Add Parametric Morphism {n} : (@Aentail n)
  with signature (@eq_AExp n) ==> (@eq_AExp n) 
    ==> (@eq Prop) as eq_AExp_Aentail.
Proof.
move=>A1 A2 P1 A3 A4 P2.
rewrite propeqP; split=>P3 q m; move: (P3 q m);
by move: P1 P2; rewrite eq_AExp.unlock=>/(_ q m)->/(_ q m)->.
Qed.

Lemma eq_AExp_entail2 {n} (A1 A2 : AExp n) :
  A1 =a A2 -> (A1 ⟚a A2)%A.
Proof. by rewrite eq_AExp.unlock=>H; split=>q m; rewrite H. Qed.

Lemma eq_AExp_entail {n} (A1 A2 : AExp n) :
  A1 =a A2 -> (A1 ⊨a A2)%A.
Proof. by move=>/eq_AExp_entail2 []. Qed.

Add Parametric Morphism {n} : (@program_rule n)
  with signature (@eq_AExp n) ==> (@eq (program n)) ==> (@eq_AExp n) 
    ==> (@eq Prop) as eq_AExp_program_rule.
Proof.
move=> A1 A2 /eq_AExp_entail2 [] P1 P2 c A3 A4 /eq_AExp_entail2 [] P3 P4.
by apply/propext; split=>P; apply/(R_con _ P).
Qed.

Add Parametric Morphism {n} : (@Ahoare n)
  with signature (@eq_AExp n) ==> (@eq_AExp n) ==> (@eq (program n))
    ==> (@eq Prop) as eq_AExp_Ahoare.
Proof.
move=> A1 A2 + A3 A4 + c.
rewrite eq_AExp.unlock /Ahoare /hoare =>H1 H2; apply/propext; split;
move=>/[swap] q /[swap] m /[swap] r /(_ q m r); rewrite /satisfaction_def.
by move=>H3 H4 m'; rewrite -H2; apply/H3=>m''; rewrite H1.
by move=>H3 H4 m'; rewrite H2; apply/H3=>m''; rewrite -H1.
Qed.

HB.lock
Definition P_I {n} : PExp n := ((P_X ord0) * (P_X ord0))%P.

Lemma mulPI {n} (P : PExp n) : (P * P_I =p P)%P.
Proof.
rewrite P_I.unlock eq_PExp.unlock=>q m.
by rewrite /= -liftf_lf_comp tf2f_comp Gate_XX tf2f1 liftf_lf1 comp_lfun1r.
Qed.

Lemma mulIP {n} (P : PExp n) : (P_I * P =p P)%P.
Proof.
rewrite P_I.unlock eq_PExp.unlock=>q m.
by rewrite /= -liftf_lf_comp tf2f_comp Gate_XX tf2f1 liftf_lf1 comp_lfun1l.
Qed.

Section Repetition.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope vsyn_scope.

Variable (n : nat).
(* The system is totally of 2(k+1) + 1 qubits, i.e., at least 3 qubits *)
Hypothesis (Hn : exists k, (n = 2 * k.+1)%N).
Local Notation program := (program n).
Local Notation PExp := (PExp n).
Local Notation AExp := (AExp n).

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[@P_Mul n / P_I]_(i <- r | P%B) F%P) : psyn_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[@P_Mul n / P_I]_(i <- r) F%P) : psyn_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[@P_Mul n / P_I]_(i | P%B) F%P) : psyn_scope.
Notation "\prod_ i F" :=
  (\big[@P_Mul n / P_I]_i F%P) : psyn_scope.
Notation "\prod_ ( i < m | P ) F" :=
  (\big[@P_Mul n / P_I]_(i < m | P%B) F%P) : psyn_scope.
Notation "\prod_ ( i < m ) F" :=
  (\big[@P_Mul n / P_I]_(i < m) F%P) : psyn_scope.
  
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[(fun e1 e2 => (app_ (app_ (cst_ +%R) e1%X) e2%X)) /0%R%:CS]_(i <- r | P%B) F%X) : xsyn_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[(fun e1 e2 => (app_ (app_ (cst_ +%R) e1%X) e2%X)) /0%R%:CS]_(i <- r) F%X) : xsyn_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[(fun e1 e2 => (app_ (app_ (cst_ +%R) e1%X) e2%X)) /0%R%:CS]_(i | P%B) F%X) : xsyn_scope.
Notation "\sum_ i F" :=
  (\big[(fun e1 e2 => (app_ (app_ (cst_ +%R) e1%X) e2%X)) /0%R%:CS]_i F%X) : xsyn_scope.
Notation "\sum_ ( i < m | P ) F" :=
  (\big[(fun e1 e2 => (app_ (app_ (cst_ +%R) e1%X) e2%X)) /0%R%:CS]_(i < m | P%B) F%X) : xsyn_scope.
Notation "\sum_ ( i < m ) F" :=
  (\big[(fun e1 e2 => (app_ (app_ (cst_ +%R) e1%X) e2%X)) /0%R%:CS]_(i < m) F%X) : xsyn_scope.

Notation "\cap_ ( i <- r | P ) F" :=
  (\big[@A_and n / A_BExp n true%:CS]_(i <- r | P%B) F%A) : asyn_scope.
Notation "\cap_ ( i <- r ) F" :=
  (\big[@A_and n / A_BExp n true%:CS]_(i <- r) F%A) : asyn_scope.
Notation "\cap_ ( i | P ) F" :=
  (\big[@A_and n / A_BExp n true%:CS]_(i | P%B) F%A) : asyn_scope.
Notation "\cap_ i F" :=
  (\big[@A_and n / A_BExp n true%:CS]_i F%A) : asyn_scope.
Notation "\cap_ ( i < m | P ) F" :=
  (\big[@A_and n / A_BExp n true%:CS]_(i < m | P%B) F%A) : asyn_scope.
Notation "\cap_ ( i < m ) F" :=
  (\big[@A_and n / A_BExp n true%:CS]_(i < m) F%A) : asyn_scope.

Notation "\cup_ ( i <- r | P ) F" :=
  (\big[@A_or n / A_BExp n false%:CS]_(i <- r | P%B) F%A) : asyn_scope.
Notation "\cup_ ( i <- r ) F" :=
  (\big[@A_or n / A_BExp n false%:CS]_(i <- r) F%A) : asyn_scope.
Notation "\cup_ ( i | P ) F" :=
  (\big[@A_or n / A_BExp n false%:CS]_(i | P%B) F%A) : asyn_scope.
Notation "\cup_ i F" :=
  (\big[@A_or n / A_BExp n false%:CS]_i F%A) : asyn_scope.
Notation "\cup_ ( i < m | P ) F" :=
  (\big[@A_or n / A_BExp n false%:CS]_(i < m | P%B) F%A) : asyn_scope.
Notation "\cup_ ( i < m ) F" :=
  (\big[@A_or n / A_BExp n false%:CS]_(i < m) F%A) : asyn_scope.
Notation "\cup_ ( i : t | P ) F" :=
  (\big[@A_or n / A_BExp n false%:CS]_(i : t | P%B) F%A) (only parsing) : asyn_scope.
Notation "\cup_ ( i : t ) F" :=
  (\big[@A_or n / A_BExp n false%:CS]_(i : t) F%A) (only parsing) : asyn_scope.

Definition g (i : 'I_n) : PExp := 
  ((P_Z ord0) * (P_Z (nlift ord0 i)))%P.

Definition Zbar : PExp := (\prod_(i < n.+1) P_Z i)%P.

(* Decoder's properties *)
Variable (f : 'I_n.+1 -> ('I_n -> bool) -> bool).
Hypothesis (Hf : forall s i, f (nlift ord0 i) s + f ord0 s = s i).
Hypothesis (Hf1 : forall (s : 'I_n -> bool), 
  ((\sum_i (s i : nat) <= n %/ 2)%N -> f ord0 s = false) /\
  ((\sum_i (s i : nat) > n %/ 2)%N -> f ord0 s = true)).

(* We assume the used variables are of distinct name *)
Variable (e c : 'I_n.+1 -> cvar Bool) (s : 'I_n -> cvar Bool).
Hypothesis (cvname_es : forall i j, cvname (e i) == cvname (s j) = false).
Hypothesis (cvname_ec : forall i j, cvname (e i) == cvname (c j) = false).
Hypothesis (cvname_sc : forall i j, cvname (s i) == cvname (c j) = false).
Hypothesis (cvname_e : forall i j, cvname (e i) == cvname (e j) = (i == j)).
Hypothesis (cvname_s : forall i j, cvname (s i) == cvname (s j) = (i == j)).
Hypothesis (cvname_c : forall i j, cvname (c i) == cvname (c j) = (i == j)).

(* Repetition code *)
Definition S_rep := 
  (* error injection, e is used to control errors *)
  [ for i < n.+1 do [{ e i , i }] <*- X ] ;;
  (* detact syndromes *)
  [ for i < n do s i <m- Meas [ g i ] ] ;;
  (* decoding *)
  [ for i < n.+1 do c i <<- (f i)%:F1 (lam_ s)] ;;
  (* error correction *)
  [ for i < n.+1 do [{ c i , i }] <*- X ].

Lemma expr_subst_big I r (P : pred I) 
  {Tf} (op : eval_ctype Tf -> eval_ctype Tf -> eval_ctype Tf) (idx : eval_ctype Tf)
    (F : I -> expr_ (eval_ctype Tf)) {Tc} (x : cvar Tc) (es : expr_ (eval_ctype Tc)) :
  ((\big[(fun e1 e2 => (app_ (app_ (cst_ op) e1%X) e2%X)) / idx%:CS]_(i <- r | P i) F i).[x <- es]
    = (\big[(fun e1 e2 => (app_ (app_ (cst_ op) e1%X) e2%X)) / idx%:CS]_(i <- r | P i) (F i).[x <- es]))%X.
Proof. by elim/big_rec2 : _ =>// i y1 y2 _ <-. Qed.

Lemma esem_big I r (P : pred I) 
  {Tf} (op : eval_ctype Tf -> eval_ctype Tf -> eval_ctype Tf) (idx : eval_ctype Tf)
    (F : I -> expr_ (eval_ctype Tf)) m : 
  esem (\big[(fun e1 e2 => (app_ (app_ (cst_ op) e1%X) e2%X)) / idx%:CS]_(i <- r | P i) F i) m
    = \big[op / idx]_(i <- r | P i) esem (F i) m.
Proof. by elim/big_rec2 : _ =>// i y1 y2 _ <-. Qed.

Lemma Asem_cap I r (P : pred I) (F : I -> AExp) q m : 
  Asem q (\cap_(i <- r | P i) F i)%A m
    = (\cap_(i <- r | P i) Asem q (F i) m)%HS.
Proof. by elim/big_rec2 : _ =>// i y1 y2 _ <-. Qed.

Lemma Asem_cup I r (P : pred I) (F : I -> AExp) q m : 
  Asem q (\cup_(i <- r | P i) F i)%A m
    = (\cup_(i <- r | P i) Asem q (F i) m)%HS.
Proof. by elim/big_rec2 : _ =>// i y1 y2 _ <-. Qed.

Lemma PExp_subst_prod I r (P : pred I) (F : I -> PExp) 
  {Tc} (x : cvar Tc) (es : expr_ (eval_ctype Tc)) :
  ((\prod_ ( i <- r | P i) F i).[ x <- es ] =
    \prod_ ( i <- r | P i) (F i).[ x <- es ])%P.
Proof.
elim/big_rec2 : _ =>//=.
by rewrite P_I.unlock/=.
by move=>? ? ? ? <-.
Qed.

Lemma PExp_subst1_prod I r (P : pred I) (F : I -> PExp) j (Xs Ys Zs : PExp) :
  Xs * Xs =p P_I ->
  ((\prod_ ( i <- r | P i) F i).[j; Xs<-X, Ys<-Y, Zs<-Z] =p
    \prod_ ( i <- r | P i) (F i).[j; Xs<-X, Ys<-Y, Zs<-Z])%P.
Proof.
move=>H.
elim/big_rec2 : _ =>//=.
by rewrite P_I.unlock/=; case: eqP=>// _; rewrite H P_I.unlock.
by move=>? ? ? ? <-.
Qed.

Lemma AExp_subst_cap I r (P : pred I) (F : I -> AExp) 
  {Tc} (x : cvar Tc) (es : expr_ (eval_ctype Tc)) :
  ((\cap_ ( i <- r | P i) F i).[ x <- es ] =
    \cap_ ( i <- r | P i) (F i).[ x <- es ])%A.
Proof. by elim/big_rec2 : _ =>// ? ? ? _ <-. Qed.

Lemma AExp_subst_cup I r (P : pred I) (F : I -> AExp) 
  {Tc} (x : cvar Tc) (es : expr_ (eval_ctype Tc)) :
  ((\cup_ ( i <- r | P i) F i).[ x <- es ] =
    \cup_ ( i <- r | P i) (F i).[ x <- es ])%A.
Proof. by elim/big_rec2 : _ =>// ? ? ? _ <-. Qed.

Lemma AExp_subst1_cap I r (P : pred I) (F : I -> AExp) j (Xs Ys Zs : PExp) :
  ((\cap_ ( i <- r | P i) F i).[j; Xs<-X, Ys<-Y, Zs<-Z] =
    \cap_ ( i <- r | P i) (F i).[j; Xs<-X, Ys<-Y, Zs<-Z])%A.
Proof. by elim/big_rec2 : _ =>// ? ? ? _ <-. Qed.

Lemma AExp_subst1_cup I r (P : pred I) (F : I -> AExp) j (Xs Ys Zs : PExp) :
  ((\cup_ ( i <- r | P i) F i).[j; Xs<-X, Ys<-Y, Zs<-Z] =
    \cup_ ( i <- r | P i) (F i).[j; Xs<-X, Ys<-Y, Zs<-Z])%A.
Proof. by elim/big_rec2 : _ =>// ? ? ? _ <-. Qed.

Lemma eq_expr_big I r (P : pred I) 
  {Tf} (op : eval_ctype Tf -> eval_ctype Tf -> eval_ctype Tf) (idx : eval_ctype Tf)
    (F1 F2 : I -> expr_ (eval_ctype Tf)) :
  (forall i, P i -> F1 i =e F2 i) ->
    (\big[(fun e1 e2 => (app_ (app_ (cst_ op) e1%X) e2%X)) / idx%:CS]_(i <- r | P i) F1 i
      =e \big[(fun e1 e2 => (app_ (app_ (cst_ op) e1%X) e2%X)) / idx%:CS]_(i <- r | P i) F2 i)%X.
Proof.
move=>IH; elim/big_rec2 : _; first by apply eq_expr_refl.
by move=>i ? ? ? ->; rewrite IH//; apply eq_expr_refl.
Qed.

Lemma eq_PExp_prod I r (P : pred I) (F1 F2 : I -> PExp) :
  (forall i, P i -> F1 i =p F2 i) ->
  (\prod_( i <- r | P i) F1 i =p \prod_( i <- r | P i) F2 i)%P.
Proof.
move=>IH; elim/big_rec2 : _; first by apply eq_PExp_refl.
by move=>i ? ? ? ->; rewrite IH//; apply eq_PExp_refl.
Qed.

Lemma eq_AExp_cap I r (P : pred I) (F1 F2 : I -> AExp) :
  (forall i, P i -> F1 i =a F2 i) ->
  (\cap_ ( i <- r | P i) F1 i =a \cap_ ( i <- r | P i) F2 i)%A.
Proof.
move=>IH; elim/big_rec2 : _; first by apply eq_AExp_refl.
by move=>i ? ? ? ->; rewrite IH//; apply eq_AExp_refl.
Qed.

Lemma eq_AExp_cup I r (P : pred I) (F1 F2 : I -> AExp) :
  (forall i, P i -> F1 i =a F2 i) ->
  (\cup_ ( i <- r | P i) F1 i =a \cup_ ( i <- r | P i) F2 i)%A.
Proof.
move=>IH; elim/big_rec2 : _; first by apply eq_AExp_refl.
by move=>i ? ? ? ->; rewrite IH//; apply eq_AExp_refl.
Qed.

Lemma SQ_boolM b1 b2 : SQ_bool b1 * SQ_bool b2 =s SQ_bool (b1 + b2)%X.
Proof.
rewrite eq_SQExp.unlock/==>m; do 2 case: (esem _ _)=>/=;
by rewrite ?expr1 ?expr0 ?mulr1// ?mul1r//= mulN1r opprK.
Qed.

Lemma scalePA a b (P : PExp) : a *: (b *: P) =p (a * b) *: P.
Proof. by rewrite eq_PExp.unlock=>q m; rewrite /= scalerA realcM. Qed.

Lemma scale1P (P : PExp) : 1 *: P =p P.
Proof. by rewrite eq_PExp.unlock=>q m; rewrite /= sq_1E scale1r. Qed.

Lemma sq_boolT : (SQ_bool true%:CS =s -1).
Proof. by rewrite eq_SQExp.unlock/==>m; rewrite sq_N1E expr1. Qed.

Lemma sq_boolF : (SQ_bool false%:CS =s 1).
Proof. by rewrite eq_SQExp.unlock/==>m; rewrite sq_1E expr0. Qed.

Lemma scaleN1P (P : PExp) : (-1 *: P)%P =a ~~ P.
Abort.

Lemma mulPZl a (P1 P2 : PExp) : (a *: P1) * P2 =p a *: (P1 * P2).
Proof. by rewrite eq_PExp.unlock=>q m; rewrite /= linearZl. Qed.

Lemma mulPZr a (P1 P2 : PExp) : P1 * (a *: P2) =p a *: (P1 * P2).
Proof. by rewrite eq_PExp.unlock=>q m; rewrite /= linearZr. Qed.

Lemma addR0 (T : nmodType) (b : expr_ T) : b + 0%:CS =e b.
Proof. by rewrite eq_expr.unlock/==>m; rewrite addr0. Qed.

Lemma add0R (T : nmodType) (b : expr_ T) : 0%:CS + b =e b.
Proof. by rewrite eq_expr.unlock/==>m; rewrite add0r. Qed.

Lemma addRC (T : nmodType) (b1 b2 : expr_ T) : b1 + b2 =e b2 + b1.
Proof. by rewrite eq_expr.unlock/==>m; rewrite addrC. Qed.

Lemma addRA (T : nmodType) (b1 b2 b3 : expr_ T) : b1 + (b2 + b3) =e b1 + b2 + b3.
Proof. by rewrite eq_expr.unlock/==>m; rewrite addrA. Qed.

Lemma addRAC (T : nmodType) (b1 b2 b3 : expr_ T) : b1 + b2 + b3 =e b1 + b3 + b2.
Proof. by rewrite eq_expr.unlock/==>m; rewrite addrAC. Qed.

Lemma addRCA (T : nmodType) (b1 b2 b3 : expr_ T) : b1 + (b2 + b3) =e b2 + (b1 + b3).
Proof. by rewrite eq_expr.unlock/==>m; rewrite addrCA. Qed.

Lemma addRACA (T : nmodType) (b1 b2 b3 b4 : expr_ T) : 
  b1 + b2 + (b3 + b4) =e b1 + b3 + (b2 + b4).
Proof. by rewrite eq_expr.unlock/==>m; rewrite addrACA. Qed.

Lemma addBB (b : bexpr) : b + b =e false%:CS.
Proof. by rewrite eq_expr.unlock/==>m; rewrite /GRing.add/= addbb. Qed.

Lemma addFB (b : bexpr) : false%:CS + b =e b.
Proof. by rewrite eq_expr.unlock. Qed.

Lemma addBF (b : bexpr) : b + false%:CS =e b.
Proof. by rewrite addRC addFB. Qed.

Lemma mulPXX (i : 'I_n.+1) : (P_X i * P_X i =p P_I)%P.
Proof.
rewrite P_I.unlock eq_PExp.unlock/==>q m; 
by rewrite -!liftf_lf_comp !tf2f_comp !Gate_XX !tf2f1 !liftf_lf1.
Qed.

Lemma mulPYY (i : 'I_n.+1) : (P_Y i * P_Y i =p P_I)%P.
Proof.
rewrite P_I.unlock eq_PExp.unlock/==>q m; 
by rewrite -!liftf_lf_comp !tf2f_comp Gate_YY Gate_XX !tf2f1 !liftf_lf1.
Qed.

Lemma mulPZZ (i : 'I_n.+1) : (P_Z i * P_Z i =p P_I)%P.
Proof.
rewrite P_I.unlock eq_PExp.unlock/==>q m; 
by rewrite -!liftf_lf_comp !tf2f_comp Gate_ZZ Gate_XX !tf2f1 !liftf_lf1.
Qed.

Lemma R_for m (F : 'I_m -> program) (A : 'I_m.+1 -> AExp) (B D : AExp) :
  (forall i : 'I_m, program_rule (A (nlift ord_max i)) (F i) (A (nlift ord0 i))) ->
  (B ⊨a A 0)%A -> (A ord_max ⊨a D)%A ->
  program_rule B [for i < m do F i] D.
Proof.
elim: m F A B D.
  move=>F A B D _; rewrite ord1 big_ord0=>H1 H2.
  by apply/(R_con H1 (R_skip _) H2).
move=>m IH F A B D H H1 H2.
rewrite big_ord_recl.
pose A' (i : 'I_m.+1) := A (nlift ord0 i).
apply/(R_seqc (B := A' ord0)).
  apply/(R_con _ (H ord0)); rewrite /A'; last by apply Aentail_refl.
  suff -> : nlift ord_max ord0 = ord0 :> 'I_m.+2 by apply H1.
  by move: (lift_max (ord0 : 'I_m.+1))=>/= ?; apply/val_inj.
apply/(IH _ A')=>[i||]; rewrite /A'.
  suff -> : nlift ord0 (nlift ord_max i) = 
    nlift ord_max (nlift ord0 i) :> 'I_m.+2 by apply/H.
  by apply/val_inj; rewrite /= !bump0 bumpS.
apply/Aentail_refl.
suff -> : nlift ord0 ord_max = ord_max :> 'I_m.+2 by apply H2.
by move: (lift0 (ord_max : 'I_m.+1))=>/= ?; apply/val_inj.
Qed.

Lemma R_forV m (F : 'I_m -> program) (A : 'I_m.+1 -> AExp) (B D : AExp) :
  (forall i : 'I_m, program_rule (A (nlift ord0 i)) (F (rev_ord i)) (A (nlift ord_max i))) ->
  (B ⊨a A ord_max)%A -> (A 0 ⊨a D)%A ->
  program_rule B [for i < m do F i] D.
Proof.
move=>H H1 H2.
apply/(R_for (A := fun i => A (rev_ord i))).
  by move=>i; rewrite -{2}[ i]rev_ordK rev_ord_lift0 rev_ord_lift_max.
by rewrite rev_ord0.
by rewrite rev_ord_max.
Qed.

Lemma PExp_scale_prod I r (P : pred I) (b : I -> bexpr) (Pf : I -> PExp) :
  \prod_(i <- r | P i) (SQ_bool (b i) *: Pf i) =p
    (SQ_bool (\sum_(i <- r | P i) b i)%X) *: \prod_(i <- r | P i) Pf i.
Proof.
elim/big_rec3 : _; first by rewrite sq_boolF scale1P.
by move=>i ? ? ? ? ->; rewrite mulPZl mulPZr scalePA SQ_boolM.
Qed.

Lemma S_rep_correct1 (b : bool) : program_rule 
    ((\cap_i (SQ_bool (c ord0 + c (nlift ord0 i))%X *: g i)%P)
      && ((SQ_bool (b%:CS + \sum_i (c i))%X *: Zbar)%P))%A
      [ for i < n.+1 do [{ c i , i }] <*- X ]
    ((\cap_i g i) && ((SQ_bool b%:CS) *: Zbar)%P)%A.
Proof.
rewrite big_ord_recl; apply/(R_seqc (B := 
    ((\cap_i (SQ_bool (c (nlift ord0 i)) *: g i)%P)
      && ((SQ_bool (b%:CS + \sum_i (c (nlift ord0 i)))%X *: Zbar)%P))%A)).
apply/(R_conl _ (R_X_cond _ _ _)).
  apply/eq_AExp_entail; rewrite /AXCsubst/=.
  apply/eq_AExp_A_and.
    rewrite AExp_subst1_cap; apply eq_AExp_cap=>i _.
    by rewrite /= mulPZl scalePA SQ_boolM addRC.
  rewrite big_ord_recl addRA /Zbar big_ord_recl/=.
  rewrite mulPZl scalePA SQ_boolM addRAC.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//; apply/eq_PExp_P_Mul=>//.
  by rewrite PExp_subst1_prod ?mulPXX.
apply/(R_for (A := (fun j : 'I_n.+1 => 
((\cap_(i < n) ((if (i < j)%N then 1 else SQ_bool (c (nlift ord0 i))) *: g i)%P) &&
   (SQ_bool (b%:CS + \sum_(i < n) if (i < j)%N then false%:CS else c (nlift ord0 i))%X *: Zbar)%P)%A))).
- move=>i; apply/(R_conl _ (R_X_cond _ _ _)).
  rewrite /AXCsubst/= AExp_subst1_cap.
  apply/eq_AExp_entail/eq_AExp_A_and.
    apply/eq_AExp_cap=>j _.
    rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
    case: ltngtP; rewrite ?(inj_eq lift_inj) -(inj_eq val_inj)/=.
    by move=>/ltn_eqF->.
    by move=>/ltn_eqF; rewrite eq_sym=>->.
    by move=>/val_inj->; rewrite eqxx scale1P mulPZr.
  rewrite PExp_subst1_prod ?mulPXX// -!SQ_boolM -!scalePA.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
  rewrite /Zbar !big_ord_recl -!mulPZr/= ; apply/eq_PExp_P_Mul=>//.
  rewrite -!PExp_scale_prod; apply/eq_PExp_prod=>j _.
  rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
  case: ltngtP; rewrite ?(inj_eq lift_inj) -(inj_eq val_inj)/=.
  by move=>/ltn_eqF->.
  by move=>/ltn_eqF; rewrite eq_sym=>->.
  by move=>/val_inj->; rewrite eqxx sq_boolF scale1P.
- by apply/eq_AExp_entail.
- apply/eq_AExp_entail => /=; under eq_bigr do rewrite ltn_ord.
  under [in X in (_ && X)%A]eq_bigr do rewrite ltn_ord.
  apply/eq_AExp_A_and.
    by apply/eq_AExp_cap=>i _; rewrite scale1P.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//; apply/eq_SQExp_SQ_bool.
  rewrite eq_expr.unlock=>m/=; rewrite (esem_big _ _ (Tf := Bool)).
  under eq_bigr do rewrite /=.
  by rewrite sumr_const card_ord mul0rn addr0.
Qed.

Lemma Hf_expr i : 
  (f ord0)%:F1 (lam_ s) + (f (nlift ord0 i))%:F1 (lam_ s) =e s i.
Proof. by rewrite eq_expr.unlock=>m /=; rewrite addrC Hf. Qed.

Lemma eq_expr_lam {Te Ue : Type} (F1 F2 : Te -> expr_ Ue) :
  (forall i, F1 i =e F2 i) -> lam_ F1 =e lam_ F2.
Proof.
move=>H; rewrite eq_expr.unlock/==>m.
by apply/funext=>i; move: (H i); rewrite eq_expr.unlock.
Qed.

Lemma S_rep_correct2 (b : bool) : program_rule 
    ((\cap_i (SQ_bool (s i) *: g i)%P)
      && ((SQ_bool (b%:CS +  (f ord0)%:F1 (lam_ s) + \sum_i (s i))%X *: Zbar)%P))%A
      [ for i < n.+1 do c i <<- (f i)%:F1 (lam_ s)]
    ((\cap_i (SQ_bool (c ord0 + c (nlift ord0 i))%X *: g i)%P)
      && ((SQ_bool (b%:CS + \sum_i (c i))%X *: Zbar)%P))%A.
Proof.
rewrite big_ord_recl; apply/(R_seqc (B := 
  ((\cap_i (SQ_bool (c ord0 + ((f (nlift ord0 i))%:F1 (lam_ s)))%X *: g i)%P) &&
    (SQ_bool (b%:CS + c ord0 + \sum_i ((f (nlift ord0 i))%:F1 (lam_ s)))%X *: Zbar)%P)%A)).
apply/(R_conl _ (R_assign _ _ _)).
  apply/eq_AExp_entail=>/=; rewrite eqxx.
  case: eqP=>// ?; rewrite cast_expr_id.
  apply/eq_AExp_A_and.
    rewrite AExp_subst_cap; apply/eq_AExp_cap=>i _.
    rewrite /= eqxx; case: eqP=>// ?; rewrite cast_expr_id.
    rewrite -Hf_expr; apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
    apply/eq_SQExp_SQ_bool/eq_expr_app=>//.
    by apply/eq_expr_app=>//; apply/eq_expr_lam=>j; rewrite cvname_sc.
  rewrite -!SQ_boolM -!scalePA; apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
  apply/eq_PExp_P_Scale=>//.
  have {1}<-: \sum_(i < n) ((f ord0)%:F1 (lam_ (fun x : 'I_n => s x)) + s i) =e \sum_(i < n) s i.
    rewrite eq_expr.unlock/==>m; rewrite !(esem_big _ _ (Tf := Bool))/=.
    rewrite big_split/= -[RHS]add0r sumr_const card_ord; f_equal.
    set t := f _ _.
    move: Hn=>[k ->]; elim: k=>[|k <-].
      by rewrite muln1 mulr2n /GRing.add/= addbb.
    by rewrite mulnS mulrnDr mulr2n /GRing.add/= addbb addFb.
  rewrite /Zbar PExp_subst_prod !big_ord_recl -!mulPZr.
  apply/eq_PExp_P_Mul=>//; rewrite (expr_subst_big _ _ (Tf := Bool)) -!PExp_scale_prod.
  apply/eq_PExp_prod=>/= i _; apply/eq_PExp_P_Scale=>//.
  apply/eq_SQExp_SQ_bool; rewrite -Hf_expr addRA addBB addFB.
  by apply/eq_expr_app=>//; apply/eq_expr_lam=>j; rewrite cvname_sc.
apply/(R_for (A := (fun j : 'I_n.+1 => 
  ((\cap_(i < n) (SQ_bool (c ord0 + (if (i < j)%N then (var_ (c (nlift ord0 i))) else 
  ((f (nlift ord0 i))%:F1 (lam_ (fun x : 'I_n => s x)))))%X *: g i)%P)%A) &&
  (SQ_bool (b%:CS + c ord0 + \sum_(i < n) if (i < j)%N then (var_ (c (nlift ord0 i))) else 
  ((f (nlift ord0 i))%:F1 (lam_ (fun x : 'I_n => s x))))%X *: Zbar)%P)%A)).
- move=>i; apply/(R_conl _ (R_assign _ _ _))=>/=.
  apply/eq_AExp_entail/eq_AExp_A_and.
    rewrite AExp_subst_cap; apply/eq_AExp_cap=>j _.
    rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
    rewrite cvname_c -(inj_eq val_inj)/=.
    apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
    apply/eq_SQExp_SQ_bool/eq_expr_app=>//.
    case: ltngtP=>/=.
    + by rewrite cvname_c/= (inj_eq lift_inj)/= -(inj_eq val_inj)/= =>/ltn_eqF->.
    + move=>/ltn_eqF H; apply/eq_expr_app=>//; apply/eq_expr_lam=>k.
      by rewrite cvname_sc.
    + by move=>/val_inj->; rewrite eqxx; case: eqP=>// ?; rewrite cast_expr_id.
  rewrite cvname_c/=.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale;
    last by rewrite /Zbar PExp_subst_prod.
  apply/eq_SQExp_SQ_bool/eq_expr_app=>//.
  rewrite (expr_subst_big _ _ (Tf := Bool)).
  apply/(eq_expr_big _ _ (Tf := Bool))=>j _.
  rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS/=.
  case: ltngtP=>/=.
  + by rewrite cvname_c (inj_eq lift_inj) -(inj_eq val_inj)/==>/ltn_eqF->.
  + move=>/ltn_eqF H; apply/eq_expr_app=>//.
    by apply/eq_expr_lam=>k; rewrite cvname_sc.
  + by move=>/val_inj->; rewrite eqxx; case: eqP=>// ?; rewrite cast_expr_id.
- by apply/eq_AExp_entail.
- apply/eq_AExp_entail => /=; under eq_bigr do rewrite ltn_ord.
  under [in X in (_ && X)%A]eq_bigr do rewrite ltn_ord.
  by apply/eq_AExp_A_and=>//; rewrite big_ord_recl addRA.
Qed.

Lemma R_measure_pauli (x : cvar Bool) (P : PExp) (A : AExp) :
  ((-1) *: P)%P =a ~~ P ->
  program_rule (\cup_(b : bool) (SQ_bool b%:CS *: P && A.[x <- b%:CS])%P)%A
    (measure x P) A.
Proof.
move=>H; apply/(R_conl _ (R_measure _ _ _))=>q m /=.
rewrite Asem_cup big_bool/= cuphC; apply/lehU2.
by apply/lehI2r; rewrite /Psem/= expr0 scale1r.
move: H; rewrite eq_AExp.unlock/==>/(_ q m).
by rewrite /Psem/= sq_N1E expr1=>->.
Qed. 

Lemma g_pauli i : ((-1) *: g i)%P =a ~~ (g i).
Proof.
rewrite eq_AExp.unlock=>q m /=.
rewrite /Psem/= sq_N1E realcN scaleN1r.
apply/espace1N.
apply/hermlf_normal; rewrite hermlfE adjf_comp -!liftf_lf_adj !tf2f_adj PauliZ_adj liftf_lf_compC//.
rewrite -disj_setE; QRegAuto.tac_expose.
rewrite {1}liftf_lf_compC.
rewrite -disj_setE; QRegAuto.tac_expose.
rewrite !comp_lfunA comp_lfunACA -liftf_lf_comp tf2f_comp Gate_ZZ tf2f1.
by rewrite liftf_lf1 comp_lfun1r -liftf_lf_comp tf2f_comp Gate_ZZ tf2f1 liftf_lf1.
Qed.

Lemma Acup_entaill I r (P : pred I) (F : I -> AExp) (B : AExp) : 
  (forall i, P i -> (F i ⊨a B)%A) ->
  (\cup_(i <- r | P i) F i ⊨a B)%A.
Proof.
move=>Pi; elim/big_rec : _; first by apply/Prop_A_4_4.
move=>i x /Pi; apply/Prop_A_4_8.
Qed.

Lemma Acup_entailr (I : finType) (P : pred I) (i : I) (F : I -> AExp) (B : AExp) : 
  P i -> (B ⊨a F i)%A -> (B ⊨a \cup_(i | P i) F i)%A.
Proof.
move=>Pi PB q m; rewrite Asem_cup.
apply/(cuphs_min (j := i))=>//; apply: (PB q m).
Qed.

Lemma Acap_entaill (I : finType) (P : pred I) (i : I) (F : I -> AExp) (B : AExp) : 
  P i -> (F i ⊨a B)%A ->
  (\cap_(i | P i) F i ⊨a B)%A.
Proof.
move=>Pi PB q m; rewrite Asem_cap.
apply/(caphs_max (j := i))=>//; apply: (PB q m).
Qed.

Lemma Acap_entailr I r (P : pred I) (F : I -> AExp) (B : AExp) : 
  (forall i, P i -> (B ⊨a F i)%A) -> (B ⊨a \cap_(i <- r | P i) F i)%A.
Proof.
move=>Pi; elim/big_rec : _; first by apply/Prop_A_4_3.
by move=>i x /Pi; apply/Prop_A_4_5.
Qed.

Lemma capAC (A B : AExp) : A && B =a B && A.
Proof. by rewrite eq_AExp.unlock=>q m/=; rewrite caphC. Qed.

Lemma S_rep_correct3 (b : bool) : program_rule 
    (\cup_(si : n.-tuple bool) ((\cap_i (SQ_bool (si ~_ i)%:CS *: g i)%P)
      && ((SQ_bool (b + (f ord0 si) + \sum_i (si ~_ i))%R%:CS%X *: Zbar)%P)))%A
      [ for i < n do s i <m- Meas [ g i ] ]
    ((\cap_i (SQ_bool (s i) *: g i)%P)
      && ((SQ_bool (b%:CS +  (f ord0)%:F1 (lam_ s) + \sum_i (s i))%X *: Zbar)%P))%A.
Proof.
apply/(R_for (A := 
(fun j : 'I_n.+1 => (
  (\cup_(si : n.-tuple bool) ((\cap_(i < n) (SQ_bool 
    (if (i < j)%N then (s i : bexpr) else (si ~_ i)%:CS) *: g i)%P)
  && ((SQ_bool ((b%:CS + (f ord0)%:F1 (lam_ (fun i : 'I_n => 
    if (i < j)%N then (s i : bexpr) else (si ~_ i)%:CS)) + 
    (\sum_(i < n) (if (i < j)%N then (s i : bexpr) else (si ~_ i)%:CS))))%X *: Zbar)%P))))%A))).
- move=>i; apply/(R_conl _ (R_measure_pauli _ _ _)).
  apply/Acup_entaill=>/= si _.
  apply/(Acup_entailr (i := (si ~_ i)))=>[//|].
  apply/Prop_A_4_5.
    apply/Prop_A_4_71/(Acap_entaill (i := i))=>[//|].
    by rewrite /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnn.
  rewrite AExp_subst_cup.
  apply/(Acup_entailr (i := si))=>[//|].
  rewrite /= AExp_subst_cap; apply/eq_AExp_entail/eq_AExp_A_and.
    apply/eq_AExp_cap=>j _.
    rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
    case: ltngtP=>/=[|//|].
    + by rewrite cvname_s -(inj_eq val_inj)/==>/ltn_eqF->.
    + by move=>/val_inj->; rewrite eqxx; case: eqP=>// ?; rewrite cast_expr_id.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale.
    apply/eq_SQExp_SQ_bool; rewrite /=.
    apply/eq_expr_app.
      do ! apply/eq_expr_app=>//.
      apply/eq_expr_lam=>j.
      rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
      case: ltngtP=>/=[|//|].
      + by rewrite cvname_s -(inj_eq val_inj)/==>/ltn_eqF->.
      + by move=>/val_inj->; rewrite eqxx; case: eqP=>// ?; rewrite cast_expr_id.
    rewrite (expr_subst_big _ _ (Tf := Bool)).
    apply/(eq_expr_big _ (Tf := Bool))=>j _.
    rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
    case: ltngtP=>/=[|//|].
    + by rewrite cvname_s -(inj_eq val_inj)/==>/ltn_eqF->.
    + by move=>/val_inj->; rewrite eqxx; case: eqP=>// ?; rewrite cast_expr_id.
  by rewrite /Zbar PExp_subst_prod/=.
- exact: g_pauli.
- apply/eq_AExp_entail/eq_AExp_cup=>/= i _.
  apply/eq_AExp_A_and=>//; apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
  apply/eq_SQExp_SQ_bool; rewrite eq_expr.unlock=>m /=.
  rewrite (esem_big _ _ (Tf := Bool)); do ! f_equal.
  by apply/funext=>j; rewrite tuple_ffunE.
- apply/Acup_entaill=>/= i _.
  apply/eq_AExp_entail/eq_AExp_A_and.
  by apply/eq_AExp_cap=>j _; rewrite ltn_ord.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
  apply/eq_SQExp_SQ_bool; rewrite eq_expr.unlock=>m /=.
  rewrite !(esem_big _ _ (Tf := Bool)); f_equal.
  by do ! f_equal; apply/funext=>j; rewrite ltn_ord.
  by under eq_bigr do rewrite ltn_ord.
Qed.

Lemma S_rep_correct4 (b : bool) : program_rule 
    (\cup_(si : n.-tuple bool) ((\cap_i (SQ_bool ((si ~_ i)%:CS + e ord0 + e (nlift ord0 i))%X *: g i)%P)
      && ((SQ_bool ((b + (f ord0 si) + \sum_i (si ~_ i))%R%:CS + \sum_i e i)%X *: Zbar)%P)))%A
      [ for i < n.+1 do [{ e i , i }] <*- X ]
    (\cup_(si : n.-tuple bool) ((\cap_i (SQ_bool (si ~_ i)%:CS *: g i)%P)
      && ((SQ_bool (b + (f ord0 si) + \sum_i (si ~_ i))%R%:CS%X *: Zbar)%P)))%A.
Proof.
rewrite big_ord_recl; apply/(R_seqc (B := 
  (\cup_(si : n.-tuple bool) ((\cap_i (SQ_bool ((si ~_ i)%:CS + e (nlift ord0 i))%X *: g i)%P)
    && ((SQ_bool ((b + (f ord0 si) + \sum_i (si ~_ i))%R%:CS + \sum_i e (nlift ord0 i))%X *: Zbar)%P)))%A)).
apply/(R_conl _ (R_X_cond _ _ _)).
  apply/eq_AExp_entail; rewrite /AXCsubst/= AExp_subst1_cup.
  apply/eq_AExp_cup=>si _ /=.
  apply/eq_AExp_A_and.
    rewrite AExp_subst1_cap; apply eq_AExp_cap=>i _ /=.
    by rewrite /= mulPZl scalePA SQ_boolM addRAC.
  rewrite -SQ_boolM -[in X in _ =a X]SQ_boolM -!scalePA.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
  rewrite big_ord_recl /Zbar big_ord_recl/=.
  rewrite mulPZl scalePA SQ_boolM addRC.
  apply/eq_PExp_P_Scale=>//; apply/eq_PExp_P_Mul=>//.
  by rewrite PExp_subst1_prod ?mulPXX.
apply/(R_for (A := (fun j : 'I_n.+1 => (\cup_(si : n.-tuple bool)
      (\cap_(i < n) (SQ_bool ((si ~_ i)%:CS + if (i < j)%N then false%:CS else e (nlift ord0 i))%X *: g i)%P) &&
      (SQ_bool ((b + f ord0 si + \sum_i si ~_ i)%R%:CS + \sum_(i < n) if (i < j)%N then false%:CS else e (nlift ord0 i))%X *: Zbar)%P)%A))).
- move=>i; apply/(R_conl _ (R_X_cond _ _ _)).
  rewrite /AXCsubst/= AExp_subst1_cup.
  apply/eq_AExp_entail/eq_AExp_cup=>j _ /=.
  apply/eq_AExp_A_and.
    rewrite AExp_subst1_cap; apply/eq_AExp_cap=>k _.
    rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
    case: ltngtP; rewrite ?(inj_eq lift_inj) -(inj_eq val_inj)/=.
    by move=>/ltn_eqF->.
    by move=>/ltn_eqF; rewrite eq_sym=>->.
    by move=>/val_inj->; rewrite eqxx addBF mulPZr scalePA SQ_boolM.
  rewrite PExp_subst1_prod ?mulPXX// -!SQ_boolM -!scalePA.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
  rewrite /Zbar !big_ord_recl -!mulPZr/= ; apply/eq_PExp_P_Mul=>//.
  rewrite -!PExp_scale_prod; apply/eq_PExp_prod=>k _.
  rewrite bump0 /bump [(_ <= i)%N]leqNgt ltn_ord/= add0n ltnS.
  case: ltngtP; rewrite ?(inj_eq lift_inj) -(inj_eq val_inj)/=.
  by move=>/ltn_eqF->.
  by move=>/ltn_eqF; rewrite eq_sym=>->.
  by move=>/val_inj->; rewrite eqxx sq_boolF scale1P.
- by apply/eq_AExp_entail.
- apply/eq_AExp_entail => /=; apply/eq_AExp_cup=>si _.
  apply/eq_AExp_A_and.
    by apply/eq_AExp_cap=>i _; rewrite ltn_ord addBF.
  apply/eq_AExp_A_PExp/eq_PExp_P_Scale=>//.
  apply/eq_SQExp_SQ_bool; rewrite -[X in _ =e X]addBF.
  apply/eq_expr_app=>//; under eq_bigr do rewrite ltn_ord.
  by rewrite eq_expr.unlock/==>m; rewrite (esem_big _ _ (Tf := Bool))/= big1.
Qed.

Lemma VC_rep : forall le : 'I_n.+1 -> bool, (\sum_i (le i : nat) <= n %/ 2)%N ->
  exists ls : 'I_n -> bool, 
    (\big[andb/true]_i (ls i + le ord0 + le (nlift ord0 i) == false))
      && (f 0 ls + \sum_i ls i + \sum_i le i == false).
Proof.
move=>le Pe; case E : (le 0); last first.
  pose ls : 'I_n -> bool := (fun i => le (nlift ord0 i)).
  exists ls; apply/andP; split.
    rewrite big_all_cond; apply/allP=>/= i _.
    by rewrite /GRing.add/= /ls addbF addbb.
  move: (Hf1 ls)=>[->].
    by apply/(leq_trans _ Pe); rewrite big_ord_recl E add0n.
  move=> _; rewrite big_ord_recl E addrACA -big_split/= {1 4}/GRing.add/=.
  by rewrite big1// =>? _; rewrite addbb.
pose ls : 'I_n -> bool := (fun i => ~~ (le (nlift ord0 i))).
exists ls; apply/andP; split.
  rewrite big_all_cond; apply/allP=>/= i _.
  by rewrite /ls /GRing.add/= addbT negbK addbb.
move: (Hf1 ls)=>[] _ ->.
  rewrite -(leq_add2r (\sum_i (le i : nat))).
  rewrite {2}big_ord_recl E addSn addnCA add1n -big_split/= ltnS.
  under [X in (_ <= X)%N]eq_bigr do rewrite /ls addn_negb.
  rewrite sumr_const card_ord -mulr_natr /GRing.mul/= mul1n natn.
  rewrite {6}(divn_eq n 2) muln2 -addnn -addnA leq_add2l.
  apply/(leq_trans Pe)/leq_addr.
rewrite big_ord_recl E addrACA -big_split/= {1 4}/GRing.add/=.
under eq_bigr do rewrite /ls -addTb -addbA addbb/=.
move: Hn=>[k ->]; elim: k.
  by rewrite muln1 big_ord_recl big_ord1 /GRing.add.
by move=>k /eqP Pk; rewrite mulnS big_ord_recl big_ord_recl Pk /GRing.add.
Qed.

Lemma VC_entail (b : bool) : 
  ((\sum_i nat_of_bool%:F1 (e i) <= (n %/ 2)%N%:CS)%X && 
    ((\cap_i g i) && ((SQ_bool b%:CS) *: Zbar)%P) ⊨a
    \cup_(si : n.-tuple bool) ((\cap_i (SQ_bool ((si ~_ i)%:CS + e ord0 + e (nlift ord0 i))%X *: g i)%P)
      && ((SQ_bool ((b + (f ord0 si) + \sum_i (si ~_ i))%R%:CS + \sum_i e i)%X *: Zbar)%P)))%A.
Proof.
move=>q m /=; rewrite (esem_big _ _ (Tf := Nat)) /=.
rewrite {2}/Order.le/=.
case: leqP; last by rewrite cap0h le0h.
move=>/VC_rep [si /andP[] /eqP Ps1 /eqP Ps2].
rewrite cap1h Asem_cap Asem_cup.
apply/(cuphs_min (j := [tuple i => si i]))=>//=.
rewrite Asem_cap; apply/lehI2.
  move: Ps1=>/eqP; rewrite big_andE=>/forallP Ps1.
  apply/caphsP=>i _; apply/(caphs_max (j := i))=>//=.
  move: (Ps1 i)=>/implyP/(_ isT)/eqP.
  by rewrite /Psem/= tnthE =>->; rewrite expr0 scale1r.
rewrite /Psem/= (esem_big _ _ (Tf := Bool))/=.
have PAB A B : A = B -> (A `<=` B)%HS by move=>->.
apply/PAB; do ! f_equal.
rewrite -[LHS]addr0 {1}/GRing.zero/= -Ps2 !addrA; do 2 f_equal.
by do ! f_equal; apply/funext=>i; rewrite /= tuple_ffunE tnthE.
by apply eq_bigr=>i _; rewrite tnthE.
Qed.

(* correctness formula *)
Lemma S_rep_correct (b : bool) :
  program_rule 
    ((\sum_i nat_of_bool%:F1 (e i) <= (n %/ 2)%N%:CS)%X && 
      ((\cap_i g i) && ((SQ_bool b%:CS) *: Zbar)%P))%A
    S_rep
    ((\cap_i g i) && ((SQ_bool b%:CS) *: Zbar)%P)%A.
Proof.
apply/(R_conl (VC_entail b)).
apply/(R_seqc _ (S_rep_correct1 b)).
apply/(R_seqc _ (S_rep_correct2 b)).
apply/(R_seqc _ (S_rep_correct3 b)).
apply/S_rep_correct4.
Qed.

End Repetition.