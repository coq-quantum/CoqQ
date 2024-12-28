From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
Require Import mcextra mcaextra notation quantum ctopology inhabited autonat summable.
Require Import Coq.Program.Equality String.
Require Import Relation_Definitions Setoid.

Import Order.LTheory GRing.Theory Num.Theory GenTree.
Local Notation C := hermitian.C.

(****************************************************************************)
(*                    Formalization of Quantum Registers                    *)
(* ------------------------------------------------------------------------ *)
(* Define quantum registers as an inductive type that reflects the          *)
(*  manipulation of quantum variables (e.g., merging and splitting).        *)
(* An automated type-checker for the disjointness condition is implemented  *)
(*  to enhance usability.                                                   *)
(* ------------------------------------------------------------------------ *)
(* qType : inductive type that serves as types of quantum variable/register *)
(*         QUnit, QBool, QOrd, QOption, QPair, QSum, QArray, QDFFun         *)
(*         eval_qtype : qType -> ihbFinType                                 *)
(*         to ensure the related type has an associated Hilbert space       *)
(* cType : inductive type that serves as types of classical variable        *)
(*         QType, CNat, CInt, CReal, CCplx, COption, CPair, CSum            *)
(*         CSeq CArray CDFFun                                               *)
(*         eval_ctype : cType -> ihbType (pointedType)                      *)
(*         to ensure the related type is non-empty                          *)
(*                                                                          *)  
(* Formalization of classical and quantum variables, expression and         *)
(*  classical memory and evaluation of expression                           *)
(* ------------------------------------------------------------------------ *)
(* manipulating quantum variable : quantum register (of qType)              *)
(*              'x : build  qreg T  if x is qvar T                          *)
(*             x.1 : first component of x if x : qreg T1 * T2               *)
(*                   x.1 : qreg T1                                          *)
(*             x.2 : second component of x if x : qreg T1 * T2              *)
(*                   x.2 : qreg T2                                          *)
(*           x.[i] : i-th component of x if x : qreg (QArray n T)           *)
(*                   x.[i] : qreg T                                         *)
(*          x.-[i] : i-th component of x if                                 *)
(*                   x : qreg (QDFFun (T : 'I_n -> qType))                  *)
(*                   x.[i] : qreg (T i)                                     *)
(*        (x1, x2) : combine two registers if x1 : qreg T1, x2 : qreg T2    *)
(*                   (x1,x2) : qreg T1 * T2                                 *)
(*    tuple i => E : combine a family of registers if E : 'I_n -> qreg T    *)
(*                   tuple i => E : qreg (QArray n T)                       *)
(*     ffun i => E : combine a family of registers if                       *)
(*                   E : forall i : 'I_n, qreg (T i)                        *)
(*                   ffun i => E : qreg (QDFFun T)                          *)
(* ------------------------------------------------------------------------ *)
(* Automatically disjointness checking -- whether a register contains       *)
(* the duplicated component -- is provided based on defining index_of_qreg. *)
(*     disjoint 'x 'y  if x and y have different names                      *)
(*     disjoint (x,y) z  if disjoint x z and disjoint y z                   *)
(*     ......                                                               *)
(*                                                                          *)
(* 'QReg[T] : subtype of qreg T with a proof that satisfying disjointness   *)
(*            condition                                                     *)
(*                                                                          *)
(* Thanks to Canonical and typeclass_instances, we can diractly rewrite     *)
(*  a register (x : qreg T), and enforce it (x : 'QReg[T]) to get the       *)
(*  valid quantum register.                                                 *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Declare Custom Entry reg_expr.
Reserved Notation "<{ e }>" (at level 0, e custom reg at level 99).
Reserved Notation "( x )" (in custom reg at level 0).
Reserved Notation "x" (in custom reg at level 0, x constr at level 0).
(* Reserved Notation "f x .. y" (in custom reg at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9). *)
Reserved Notation "''' x"
  (in custom reg at level 40, format "''' x", no associativity).
Reserved Notation "x '.1'"
  (in custom reg at level 50, format "x '.1'", left associativity).
Reserved Notation "x '.2'"
  (in custom reg at level 50, format "x '.2'", left associativity).
Reserved Notation "x '.[' i ]"
  (in custom reg at level 50, i constr, format "x .[ i ]", left associativity).
Reserved Notation "x '.-' i"
  (in custom reg at level 50, i constr, format "x '.-' i", left associativity).
Reserved Notation "( x , y , .. , z )"
  (in custom reg at level 0,
   format "( x ,  y ,  .. ,  z )", left associativity).
Reserved Notation "'dffun' x : aT => E"
  (in custom reg at level 0, x name, aT constr,
   format "'dffun'  x  :  aT  =>  E").
Reserved Notation "'dffun' x => E"
  (in custom reg at level 0, x name, format "'dffun'  x  =>  E").
Reserved Notation "'dffun' => E"
  (in custom reg at level 0, format "'dffun'  =>  E").
Reserved Notation "'dffun:' x"
  (in custom reg at level 0, x constr, format "'dffun:' x").
Reserved Notation "'ffun' x : aT => E"
  (in custom reg at level 0, x name, aT constr,
   format "'ffun'  x  :  aT  =>  E").
Reserved Notation "'ffun' x => E"
  (in custom reg at level 0, x name, format "'ffun'  x  =>  E").
Reserved Notation "'ffun' => E"
  (in custom reg at level 0, format "'ffun'  =>  E").
Reserved Notation "'ffun:' x"
  (in custom reg at level 0, x constr, format "'ffun:' x").
Reserved Notation "'tuple' x : aT => E"
  (in custom reg at level 0, x name, aT constr,
   format "'tuple'  x  :  aT  =>  E").
Reserved Notation "'tuple' x => E"
  (in custom reg at level 0, x name, format "'tuple'  x  =>  E").
Reserved Notation "'tuple' => E"
  (in custom reg at level 0, format "'tuple'  =>  E").
Reserved Notation "'tuple:' x"
  (in custom reg at level 0, x constr, format "'tuple:' x").
Reserved Notation "( 'dffun' x : aT => E )"
  (in custom reg at level 0, x name, aT constr). (* only parsing *)
Reserved Notation "( 'dffun' x => E )"
  (in custom reg at level 0, x name). (* only parsing *)
Reserved Notation "( 'dffun' => E )"
  (in custom reg at level 0). (* only parsing *)
Reserved Notation "( 'dffun:' x )"
  (in custom reg at level 0, x constr). (* only parsing *)
Reserved Notation "( 'ffun' x : aT => E )"
  (in custom reg at level 0, x name, aT constr). (* only parsing *)
Reserved Notation "( 'ffun' x => E )"
  (in custom reg at level 0, x name). (* only parsing *)
Reserved Notation "( 'ffun' => E )"
  (in custom reg at level 0). (* only parsing *)
Reserved Notation "( 'ffun:' x )"
  (in custom reg at level 0, x constr). (* only parsing *)
Reserved Notation "( 'tuple' x : aT => E )"
  (in custom reg at level 0, x name, aT constr). (* only parsing *)
Reserved Notation "( 'tuple' x => E )"
  (in custom reg at level 0, x name). (* only parsing *)
Reserved Notation "( 'tuple' => E )"
  (in custom reg at level 0). (* only parsing *)
Reserved Notation "( 'tuple:' x )"
  (in custom reg at level 0, x constr). (* only parsing *)
Reserved Notation "x : T"
  (in custom reg at level 99, T constr). (* only parsing *)
(* Reserved Notation "` x" (at level 5, format "` x"). *)

(* qvar is a nat, QVar 0 for local, QVar 1 for arg, QVar n.+2 for global variables *)
(* we can declare global qvar at the beginning of a section *)
(* a proc has a arg variable, and a local variable, when defining the proc, *)
(* the arg variable is regarded as qvar, when calling it, we can only pass a *)
(* quantum register with the same type that constructed from arg or local to it *)

Declare Scope xsyn_scope.
Declare Scope vsyn_scope.
Declare Scope qtype_scope.
Declare Scope ctype_scope.
Declare Scope mem_scope.
Declare Scope reg_scope.
Declare Scope reg_expr_scope.

Delimit Scope xsyn_scope with X.
Delimit Scope vsyn_scope with V.
Delimit Scope qtype_scope with QT.
Delimit Scope ctype_scope with CT.
Delimit Scope mem_scope with M.
Delimit Scope reg_scope with REG.
Delimit Scope reg_expr_scope with RE.

Definition orapp (Tr : Type) (i : Tr) (T : eqType) (x y : T) f :=
  match x =P y with
  | ReflectT E => f E
  | _ => i
  end.
Arguments orapp [Tr] i [T x y] f.

Lemma orapp_id Tr i T x (f : x = x -> Tr) :
    @orapp Tr i T x x f = f (erefl).
Proof.
by rewrite /orapp; case: eqP=>// P;
rewrite (eq_irrelevance P erefl).
Qed.

Lemma orappE Tr i T x y (P : x = y) (f : x = y -> Tr):
    @orapp Tr i T x y f = f P.
Proof.
by rewrite /orapp; case: eqP=>// P1;
rewrite (eq_irrelevance P P1).
Qed.

Lemma forallb_and (T : finType) (P1 P2 : pred T) : 
  [forall x, P1 x] && [forall x, P2 x] = [forall x, P1 x && P2 x].
Proof.
apply/eqb_iff; split=>[/andP[]/forallP H1/forallP H2|/forallP H2].
by apply/forallP=>i; rewrite H1 H2.
by apply/andP; split; apply/forallP=>i; move: (H2 i)=>/andP[].
Qed.

Lemma forallb_exchange (T1 T2 : finType) (P : T1 -> T2 -> bool) : 
  [forall x, forall y, P x y] = [forall x, forall y, P y x].
Proof.
by apply/eqb_iff; split=>/forallP H1; 
  apply/forallP=>x; apply/forallP=>y; move: (H1 y)=>/forallP.
Qed.

Lemma forallbTP {n} (f : 'I_n -> bool) :
    (forall i, f i) -> [forall i, f i] = true.
Proof. by move=>H; apply/forallP. Qed.

Inductive qType : Type :=
  | QUnit
  | QBool
  | QOrd (n : nat)
  | QOption (T : qType)
  | QPair (T1 T2 : qType)
  | QSum (T1 T2 : qType)
  | QArray (n : nat) (T : qType)
  | QDFFun (n : nat) (fT : 'I_n -> qType).

Inductive cType : Type :=
  | QType (T : qType)
  | CNat
  | CInt
  | CReal
  | CCplx
  | COption (T : cType)
  | CPair (T1 T2 : cType)
  | CSum (T1 T2 : cType)
  | CSeq (T : cType)
  | CArray (n : nat) (T : cType)
  | CDFFun (n : nat) (fT : 'I_n -> cType).

Fixpoint qType_eq_op (t1 t2 : qType) :=
  match t1, t2 with
  | QUnit, QUnit => true
  | QBool, QBool => true
  | QOrd n1, QOrd n2 => (n1 == n2)
  | QOption t1, QOption t2 => (qType_eq_op t1 t2)
  | QPair t11 t12, QPair t21 t22 =>
      (qType_eq_op t11 t21) && (qType_eq_op t12 t22)
  | QSum t11 t12, QSum t21 t22 =>
      (qType_eq_op t11 t21) && (qType_eq_op t12 t22)
  | QArray n1 t1, QArray n2 t2 => (n1 == n2) && (qType_eq_op t1 t2)
  | QDFFun n1 t1, QDFFun n2 t2 => (n1 == n2) && 
      [forall i1 : 'I_n1, [forall i2 : 'I_n2, 
        ((i1 : nat) == i2) ==> qType_eq_op (t1 i1) (t2 i2)]]
  | _, _ => false
  end.

Lemma qType_eqP : Equality.axiom qType_eq_op.
Proof.
move=>t1 t2; apply/(iffP idP)=>[|->]; last first.
elim: t2=>//=[?->?->|?->?->|??->|?? IH]//; rewrite ?eqxx//=.
by apply/forallP=>i1; apply/forallP=>i2; apply/implyP; move=>/eqP/ord_inj->.
elim: t1 t2=>[||?|? IH|? IH1 ? IH2|? IH1 ? IH2|?? IH|n fT IH]; case=>//=.
by move=> ? /eqP->. by move=> ? /IH->.
1,2: by move=> ?? /andP [] /IH1-> /IH2->.
by move=> ?? /andP [] /eqP-> /IH->.
by move=>n' fT' /andP [] /eqP Pn; case: n' / Pn fT' => fT' /forallP P;
f_equal; apply/funext=>i; move: P =>/(_ i)/forallP/(_ i); rewrite eqxx/= =>/IH.
Qed.

HB.instance Definition _ := hasDecEq.Build qType qType_eqP.

Fixpoint qtype_to_tree (t : qType) : tree (nat + nat) :=
  match t with
  | QUnit => Leaf (inr 0)
  | QBool => Leaf (inr 1)
  | QOrd n => Leaf (inl n)
  | QOption t => Node 0 [:: (qtype_to_tree t)]
  | QPair t1 t2 => Node 1 [:: qtype_to_tree t1; qtype_to_tree t2]
  | QSum t1 t2 => Node 2 [:: qtype_to_tree t1; qtype_to_tree t2]
  | QArray n t => Node 3 ((Leaf (inl n)) :: [:: qtype_to_tree t])
  | QDFFun n ft =>
      Node 4 ((Leaf (inl n)) :: [seq qtype_to_tree (ft i) | i : 'I_n])
  end.

Fixpoint tree_to_qtype (t : tree (nat + nat)) :=
  match t with
  | Leaf (inr 0) => QUnit
  | Leaf (inr 1) => QBool
  | Leaf (inl n) => QOrd n
  | Node 0 [:: t] => QOption (tree_to_qtype t)
  | Node 1 [:: t1; t2] => QPair (tree_to_qtype t1) (tree_to_qtype t2)
  | Node 2 [:: t1; t2] => QSum (tree_to_qtype t1) (tree_to_qtype t2)
  | Node 3 ((Leaf (inl n)) :: [:: t]) => QArray n (tree_to_qtype t)
  | Node 4 ((Leaf (inl n)) :: s) => QDFFun 
      (fun i : 'I_n => nth QUnit (map tree_to_qtype s) i)
  | _ => QUnit
  end.

Lemma qtype_to_treeK : cancel qtype_to_tree tree_to_qtype.
Proof.
elim=>[|||t/=->|t1/=->t2/=->|t1/=->t2/=->|n T/=->|]//.
case=>[??|n fT IH]/=; first by rewrite !fun0E.
by f_equal; apply/funext=>i; rewrite (nth_map (Leaf (inl 0)))
  1?(nth_map ord0) ?(size_enum_ord,size_map)// IH nth_ord_enum.
Qed.

HB.instance Definition _ := Choice.copy qType (can_type qtype_to_treeK).
HB.instance Definition _ := Countable.copy qType (can_type qtype_to_treeK).

Fixpoint cType_eq_op (t1 t2 : cType) :=
  match t1, t2 with
  | QType t1, QType t2 => t1 == t2
  | CNat, CNat => true
  | CInt, CInt => true
  | CReal, CReal => true
  | CCplx, CCplx => true
  | COption t1, COption t2 => (cType_eq_op t1 t2)
  | CPair t11 t12, CPair t21 t22 =>
      (cType_eq_op t11 t21) && (cType_eq_op t12 t22)
  | CSum t11 t12, CSum t21 t22 =>
      (cType_eq_op t11 t21) && (cType_eq_op t12 t22)
  | CSeq t1, CSeq t2 => (cType_eq_op t1 t2)
  | CArray n1 t1, CArray n2 t2 => (n1 == n2) && (cType_eq_op t1 t2)
  | CDFFun n1 t1, CDFFun n2 t2 => (n1 == n2) && 
      [forall i1 : 'I_n1, [forall i2 : 'I_n2, 
        ((i1 : nat) == i2) ==> cType_eq_op (t1 i1) (t2 i2)]]
  | _, _ => false
  end.

Lemma cType_eqP : Equality.axiom cType_eq_op.
Proof.
move=>t1 t2; apply/(iffP idP)=>[|->]; last first.
elim: t2=>//=[?->?->|?->?->|??->|?? IH]//; rewrite eqxx//=.
by apply/forallP=>i1; apply/forallP=>i2; apply/implyP; move=>/eqP/ord_inj->.
elim: t1 t2=>[?|||||? IH|? IH1 ? IH2|? IH1 ? IH2|? IH|?? IH|n fT IH];
case=>//=; first by move=>?/eqP->.
1,4: by move=>?/IH->.
1,2: by move=>??/andP[]/IH1->/IH2->.
by move=>??/andP[]/eqP->/IH->.
move=>n' fT' /andP[]/eqP Pn; case: n' / Pn fT' => fT' /forallP P.
f_equal; apply/funext=>i; move: P=>/(_ i)/forallP/(_ i);
by rewrite eqxx/==>/IH.
Qed.

HB.instance Definition _ := hasDecEq.Build cType cType_eqP.

Fixpoint ctype_to_tree (t : cType) : tree (qType + nat) :=
  match t with
  | QType t => Leaf (inl t)
  | CNat => Leaf (inr 0)
  | CInt => Leaf (inr 1)
  | CReal => Leaf (inr 2)
  | CCplx => Leaf (inr 3)
  | COption t => Node 0 [:: ctype_to_tree t]
  | CPair t1 t2 => Node 1 [:: ctype_to_tree t1; ctype_to_tree t2]
  | CSum t1 t2 => Node 2 [:: ctype_to_tree t1; ctype_to_tree t2]
  | CSeq t => Node 3 [:: ctype_to_tree t]
  | CArray n t => Node 4 ((Leaf (inr n)) :: [:: ctype_to_tree t])
  | CDFFun n ft =>
      Node 5 ((Leaf (inr n)) :: [seq ctype_to_tree (ft i) | i : 'I_n])
  end.

Fixpoint tree_to_ctype (t : tree (qType + nat)) :=
  match t with
  | Leaf (inl t) => QType t
  | Leaf (inr 0) => CNat
  | Leaf (inr 1) => CInt
  | Leaf (inr 2) => CReal
  | Leaf (inr 3) => CCplx
  | Node 0 [:: t] => COption (tree_to_ctype t)
  | Node 1 [:: t1; t2] => CPair (tree_to_ctype t1) (tree_to_ctype t2)
  | Node 2 [:: t1; t2] => CSum (tree_to_ctype t1) (tree_to_ctype t2)
  | Node 3 [:: t] => CSeq (tree_to_ctype t)
  | Node 4 ((Leaf (inr n)) :: [:: t]) => CArray n (tree_to_ctype t)
  | Node 5 ((Leaf (inr n)) :: s) => CDFFun 
      (fun i : 'I_n => nth CNat (map tree_to_ctype s) i)
  | _ => CNat
  end.

Lemma ctype_to_treeK : cancel ctype_to_tree tree_to_ctype.
Proof.
elim=>[|||||t/=->|t1/=->t2/=->|t1/=->t2/=->|t/=->|n T/=->|]//.
case=>[??|n fT IH]/=; first by rewrite !fun0E.
by f_equal; apply/funext=>i; rewrite (nth_map (Leaf (inr 0)))
  1?(nth_map ord0) ?(size_enum_ord,size_map)// IH nth_ord_enum.
Qed.

HB.instance Definition _ := Choice.copy cType (can_type ctype_to_treeK).
HB.instance Definition _ := Countable.copy cType (can_type ctype_to_treeK).

Fixpoint eval_qtype (t : qType) : ihbFinType :=
  match t with
  | QUnit => unit
  | QBool => bool
  | QOrd n => 'I_n.+1
  | QOption T => option (eval_qtype T)
  | QPair T1 T2 => ((eval_qtype T1) * (eval_qtype T2))%type
  | QSum T1 T2 => ((eval_qtype T1) + (eval_qtype T2))%type
  | QArray n T => n.-tuple (eval_qtype T)
  | QDFFun n T => {dffun forall i, eval_qtype (T i)}
  end.

Fixpoint eval_ctype (t : cType) : ihbType :=
  match t with
  | QType t => (eval_qtype t)
  | CNat => nat
  | CInt => int
  | CReal => hermitian.R
  | CCplx => hermitian.C
  | COption T => option (eval_ctype T)
  | CPair T1 T2 => ((eval_ctype T1) * (eval_ctype T2))%type
  | CSum T1 T2 => ((eval_ctype T1) + (eval_ctype T2))%type
  | CSeq T => seq (eval_ctype T)
  | CArray n T => n.-tuple (eval_ctype T)
  | CDFFun n T => {dffun forall i, eval_ctype (T i)}
  end.

#[reversible] Coercion QType : qType >-> cType.

Definition cast_qtype (t1 t2 : qType) (E : t1 = t2) (v : eval_qtype t1) :=
  let: erefl in _ = t2 := E return eval_qtype t2 in v.

Lemma cast_qtype_inj {t1 t2 : qType} {E : t1 = t2} : injective (cast_qtype E).
Proof. by case: t2 / E. Qed.

Lemma cast_qtype_comp (t1 t2 t3: qType) (E1 : t1 = t2) (E2 : t2 = t3) v :
  cast_qtype E2 (cast_qtype E1 v) = cast_qtype (etrans E1 E2) v.
Proof. by case: t3 / E2; case: t2 / E1. Qed.

Lemma cast_qtype_id (t : qType) (E : t = t) (v : eval_qtype t) :
  cast_qtype E v = v.
Proof. by rewrite eq_axiomK. Qed.

Definition cast_ctype (t1 t2 : cType) (E : t1 = t2) (v : eval_ctype t1) :=
  let: erefl in _ = t2 := E return eval_ctype t2 in v.

Lemma cast_ctype_inj {t1 t2 : cType} {E : t1 = t2} : injective (cast_ctype E).
Proof. by case: t2 / E. Qed.

Lemma cast_ctype_comp (t1 t2 t3: cType) (E1 : t1 = t2) (E2 : t2 = t3) v :
  cast_ctype E2 (cast_ctype E1 v) = cast_ctype (etrans E1 E2) v.
Proof. by case: t3 / E2; case: t2 / E1. Qed.

Lemma cast_ctype_id (t : cType) (E : t = t) (v : eval_ctype t) :
  cast_ctype E v = v.
Proof. by rewrite eq_axiomK. Qed.

Local Open Scope string_scope.

HB.instance Definition _ := hasDecEq.Build string String.eqb_spec.

Fixpoint string_to_seq_nat (s : string) : seq nat :=
  match s with
  | EmptyString => [::]
  | String a s => Ascii.nat_of_ascii a :: (string_to_seq_nat s)
  end.

Fixpoint seq_nat_to_string (s : seq nat) :=
  match s with
  | [::] => EmptyString
  | h :: t => String (Ascii.ascii_of_nat h) (seq_nat_to_string t)
  end.

Lemma string_to_seq_natK: cancel string_to_seq_nat seq_nat_to_string.
Proof. by elim=>// a s/= ->; rewrite Ascii.ascii_nat_embedding. Qed.

HB.instance Definition _ := Choice.copy string (can_type string_to_seq_natK).
HB.instance Definition _ := Countable.copy string (can_type string_to_seq_natK).

Inductive cvar (Tc : cType) := CVar of string & string.
Definition cvname {Tc} (x : cvar Tc) :=
  let: CVar pname name := x in (pname,name).
(* Definition cvar_of Tc (pT : phant Tc) := cvar Tc.
Notation cvar Tc := (cvar_of (Phant Tc)). *)

Definition cvtype {Tc} (v : cvar Tc) := Tc.

Inductive expr_ : Type -> Type :=
| var_  {Tc}   of cvar Tc : expr_ (eval_ctype Tc)
| cst_  {Te}   of Te : expr_ Te
| app_  {Te Ue} of expr_ (Te -> Ue) & expr_ Te : expr_ Ue
| lam_ {Te Ue} of (Te -> expr_ Ue) : expr_ (Te -> Ue).

Coercion var_ : cvar >-> expr_.

Section VarsEqType.
Variables (T : cType).

Definition cvar_eq (x y : cvar T) :=
  let: CVar x1 x2 := x in let: CVar y1 y2 := y in (x1 == y1) && (x2 == y2).

Lemma cvar_eqP (x y : cvar T) : reflect (x = y) (cvar_eq x y).
Proof.
by case: x y => [x1 x2] [y1 y2];
apply: (iffP andP) => [[] /eqP-> /eqP-> | [-> ->]].
Qed.

HB.instance Definition _ := hasDecEq.Build (cvar T) cvar_eqP.
End VarsEqType.

(* -------------------------------------------------------------------- *)
Lemma eq_cvar {t u : cType} (x : cvar t) (y : cvar u) :
      (Tagged cvar y = Tagged cvar x)
  <-> (cvtype x = cvtype y /\ cvname x == cvname y).
Proof.
split; case: x y => [x1 x2] [y1 y2]; rewrite /cvtype /=;
by [move=>[]->->-> | move=>[]->/eqP[]->->].
Qed.

Local Notation ident := (string * string)%type.

Inductive cmem := CMem of (forall T : cType, ident -> (eval_ctype T)).
HB.instance Definition _ := @gen_eqMixin cmem.
HB.instance Definition _ := @gen_choiceMixin cmem.

Definition cmget := (fun m => let: CMem m := m in m).
Coercion cmget : cmem >-> Funclass.

Definition cmset := nosimpl (fun (m : cmem) {T : cType} x v =>
  CMem (fun U y =>
    orapp (m U y) (fun eqT : T = U => 
      if x == y then cast_ctype eqT v else m U y))).
    (* match T =P U with
    | ReflectT eqT =>
      if x == y then (let: erefl in _ = U := eqT return eval_ctype U in v)
      else m U y
    | ReflectF _ => m U y
    end)). *)

Lemma get_set_eq {T : cType} (m : cmem) (x : ident) (v : eval_ctype T) :
  (cmset m x v) T x = v.
Proof. by rewrite/cmset/= eqxx /orapp; case: eqP=>// P; rewrite eq_axiomK. Qed.

Lemma get_set_nex {T U : cType} (m : cmem) (x y : ident) (v : eval_ctype T) :
  x != y -> (cmset m x v) U y = m U y.
Proof. by rewrite/cmset/=/orapp; case: eqP=>// P/negPf->. Qed.

Lemma get_set_net {T U : cType} (m : cmem) (x y: ident) (v : eval_ctype T) :
  T <> U -> (cmset m x v) U y = m U y.
Proof. by rewrite/cmset/=/orapp; case: eqP. Qed.

Lemma get_set_ne {T U : cType} (m : cmem) (x y : ident) (v : eval_ctype T) :
  (T <> U \/ x != y) -> (cmset m x v) U y = m U y.
Proof. by move=> [/get_set_net |/get_set_nex] ->. Qed.

Notation "m .[ x ]"      := (@cmget m (cvtype x%V) (cvname x%V)) : mem_scope.
Notation "m .[ x <- v ]" := (@cmset m (cvtype x%V) (cvname x%V) v) : mem_scope.

Fixpoint esem {T : Type} (e : expr_ T) (m : cmem) : T := 
  match e in expr_ T return T with
  | var_ T x => (m.[x])%M
  | cst_ T c => c
  | app_ T U e1 e2 => (esem e1 m) (esem e2 m)
  | lam_ T U f => (fun i => esem (f i) m)
  (* pred M *)
  end.

Notation "''Ht' T" := (ihb_chsType (eval_qtype T%QT))
  (at level 8, T at level 2, format "''Ht'  T").
Notation "''Hom{' T1 , T2 }" := ('Hom('Ht T1%QT, 'Ht T2%QT))
  (at level 8, format "''Hom{' T1 ,  T2 }").
Notation "''End{' T }" := ('End('Ht T%QT))
  (at level 8, format "''End{' T }").
Notation evalQT := eval_qtype.
Notation evalCT := eval_ctype.
Notation bexpr   := (expr_ bool).
Notation dexpr T := (expr_ (Distr T)).
Notation uexpr T := (expr_ 'FU('Hs T)).
Notation sexpr T := (expr_ 'NS('Hs T)).
Notation mexpr F T := (expr_ 'QM(F;'Hs T)).
Notation "x %:US" := (cst_ (x : 'FU)) (at level 2, format "x %:US").
Notation "x %:DS" := (cst_ (x : 'FD)) (at level 2, format "x %:DS").
Notation "x %:MS" := (cst_ (x : 'QM)) (at level 2, format "x %:MS").
Notation app2_ f x1 x2 := (app_ (app_ f x1%X) x2%X).
Notation "c %:CS"    := (@cst_ _ c) (at level 2, format "c %:CS").
Notation "c '%:F1' e"    := (app_ (@cst_ _ c) (e)%X)
  (at level 2, format "c %:F1  e").
Notation "c '%:F2' e1 e2"    := (app2_ (@cst_ _ c) e1 e2)
  (at level 2, e1 at next level, format "c %:F2  e1 e2").
Notation "e1 == e2" := (app2_ (cst_ (fun x y=> (x == y)%B)) e1 e2) : xsyn_scope.
Notation "e1 <= e2" := (app2_ (cst_ (fun x y=> (x <= y)%O)) e1 e2) : xsyn_scope.
Notation "e1 < e2" := (app2_ (cst_ (fun x y=> (x < y)%O)) e1 e2)   : xsyn_scope.
Notation "e1 || e2" := (app2_ (cst_ orb  ) e1 e2)  : xsyn_scope.
Notation "e1 && e2" := (app2_ (cst_ andb ) e1 e2)  : xsyn_scope.
Notation "~~ e"     := (app_ (cst_ negb) e%X)      : xsyn_scope.
Notation "e1 != e2" := ((~~ (e1 == e2))%X)         : xsyn_scope.
Notation "e1 + e2"  := (app2_ (cst_ +%R) e1 e2)    : xsyn_scope.
Notation "- e"  := (app_ (cst_ GRing.opp) e%X)     : xsyn_scope.
Notation "e1 - e2"  :=
  (app2_ (cst_ +%R) e1 (app_ (cst_ GRing.opp) e2%X)) : xsyn_scope.
Notation "e1 * e2"  := (app2_ (cst_ *%R) e1 e2)    : xsyn_scope.
Notation "e1 :: e2" := (app2_ (cst_ cons) e1 e2)   : xsyn_scope.
(* Notation "` x"      := (@var_ _ x%V) : xsyn_scope. *)
Notation "m %/ d"   := (app2_ (cst_ divn) m d)     : xsyn_scope.
Notation "m %% d"   := (app2_ (cst_ modn) m d)     : xsyn_scope.
Notation "m %| d"   := (app2_ (cst_ dvdn) m d)     : xsyn_scope.
Notation "s .[ i ]" := (app2_ (cst_ (@nth _ (witness _))) s i) : xsyn_scope.
Notation "e1 '+n' e2"  := (app2_ (cst_ addn) e1 e2)
  (at level 50, e2 at next level, left associativity) : xsyn_scope.
Notation "e1 '-n' e2"  := (app2_ (cst_ subn) e1 e2)
  (at level 50, e2 at next level, left associativity) : xsyn_scope.
Notation "e1 '*n' e2"  := (app2_ (cst_ muln) e1 e2)
  (at level 40, e2 at next level, left associativity) : xsyn_scope.

Bind Scope qtype_scope with qType.
Bind Scope ctype_scope with cType.
Notation "'Unit'" := (QUnit) (at level 0, format "'Unit'")       : qtype_scope.
Notation "'Bool'" := (QBool) (at level 0, format "'Bool'")       : qtype_scope.
Notation "''I_' n" := (QOrd n)                                   : qtype_scope.
Notation "'Option' T" := (QOption T)
  (at level 0, format "'Option' T")                              : qtype_scope.
Notation "T1 * T2" := (QPair T1 T2)                              : qtype_scope.
Notation "T1 + T2" := (QSum T1 T2)                               : qtype_scope.
Notation "T '.[' n ]" := (QArray n T) (format "T .[ n ]")        : qtype_scope.
Notation "{ 'qffun' 'forall' x < n , fT }" :=
  (QDFFun (fun x : 'I_(n%N) => fT%QT)) (at level 0, x name)      : qtype_scope.
Notation "{ 'qffun' 'forall' x , fT }" :=
  (QDFFun (fun x => fT%QT)) (at level 0, x name)                 : qtype_scope.
Notation "{ 'qffun' fT }" := (QDFFun fT)                         : qtype_scope.
Notation "''[' T ]" := (QType T)                                 : ctype_scope.
Notation "'Unit'" := (QType QUnit) (at level 0, format "'Unit'") : ctype_scope.
Notation "'Bool'" := (QType QBool) (at level 0, format "'Bool'") : ctype_scope.
Notation "''I_' n" := (QType (QOrd n))                           : ctype_scope.
Notation "'Nat'" := (CNat) (at level 0, format "'Nat'")          : ctype_scope.
Notation "'Int'" := (CInt) (at level 0, format "'Int'")          : ctype_scope.
Notation "'Real'" := (CReal) (at level 0, format "'Real'")       : ctype_scope.
Notation "'Complex'" := (CCplx) (at level 0, format "'Complex'") : ctype_scope.
Notation "'Option' T" :=
  (COption T) (at level 0, format "'Option' T")                  : ctype_scope.
Notation "T1 * T2" := (CPair T1 T2)                              : ctype_scope.
Notation "T1 + T2" := (CSum T1 T2)                               : ctype_scope.
Notation "T '.[' n ]" := (CArray n T) (format "T .[ n ]")        : ctype_scope.
Notation "{ 'cffun' 'forall' x < n , fT }" :=
  (CDFFun (fun x : 'I_(n%N) => fT%CT)) (at level 0, x name)      : ctype_scope.
Notation "{ 'cffun' 'forall' x , fT }" :=
  (CDFFun (fun x => fT%CT)) (at level 0, x name)                 : ctype_scope.
Notation "{ 'cffun' fT }" := (CDFFun fT)                         : ctype_scope.

Section QuantumRegister.
Implicit Type (T : qType).

Inductive qvar := QVar of string & string.
(* Inductive cvar (T : Type) := CVar of nat. *)

Definition qvar_eq (x y : qvar) :=
  let: QVar x1 x2 := x in let: QVar y1 y2 := y in (x1 == y1) && (x2 == y2).

Lemma qvar_eqP (x y : qvar) : reflect (x = y) (qvar_eq x y).
Proof.
by case: x y => [x1 x2] [y1 y2];
apply: (iffP andP) => [[]/eqP->/eqP->|[->->]].
Qed.

HB.instance Definition _ := hasDecEq.Build qvar qvar_eqP.

Lemma qvar_to_stringK : cancel 
  (fun x : qvar => let: QVar s1 s2 := x in (s1,s2))
    (fun s => match s with | (s1,s2) => QVar s1 s2 end).
Proof. by case. Qed.

HB.instance Definition _ := Choice.copy qvar (can_type qvar_to_stringK).
HB.instance Definition _ := Countable.copy qvar (can_type qvar_to_stringK).

(* disjointness of qvar; here we treat qvar as variables                     *)
(* rather than concrete constructions from string                            *)
Definition qvar_diff_rec (x y : qvar) : bool := x != y.
Definition qvar_diff := nosimpl qvar_diff_rec.

Fixpoint qvar_dis_sub_rec (x : qvar) (s : seq qvar) : bool :=
    match s with
    | [::] => true
    | h :: t => qvar_diff x h && (qvar_dis_sub_rec x t)
    end.
Definition qvar_dis_sub := nosimpl qvar_dis_sub_rec.

Fixpoint qvar_dis_rec (s : seq qvar) : bool :=
    match s with
    | [::] => true
    | h :: t => (qvar_dis_sub h t) && (qvar_dis_rec t)
    end.
Definition qvar_dis := nosimpl qvar_dis_rec.

End QuantumRegister.

(* assume the finite map between qvar and their qtypes *)
Definition context := {fmap qvar -> qType}.

Context (G : context).

(* Class memctxt_of (x : qvar) T :=
    MemCtxt : (G.[?x] = Some T)%fmap.

Notation memctxt x T := (memctxt_of x T%QT). *)

Class qreg_expose (P : Prop) := QRegExpose : P.

Section MKQVar.

Inductive qvart (T : qType) := QVarT (name : qvar) & (G.[?name]%fmap == Some T).
Definition qname (T : qType) (q : qvart T) :=
  let: QVarT name _ := q in name.
#[reversible] Coercion qname : qvart >-> qvar.

Inductive mkqvar (T : qType) (s1 s2 : string) :=
  MKQVar & (G.[?(QVar s1 s2)]%fmap == Some T).
Definition to_qvart (T : qType) (s1 s2 : string) (q : mkqvar T s1 s2) :=
  let: MKQVar P := q in QVarT P.
#[reversible] Coercion to_qvart : mkqvar >-> qvart.

End MKQVar.

(* definition of index of a quantum register (qreg)                          *)
Section qreg_index.

Inductive qnat : Type :=
  | qnat_fst
  | qnat_snd
  | qnat_tuplei {n} of 'I_n
  | qnat_ffuni {n} of 'I_n. 
  
Definition qnat_eq_op (t1 t2 : qnat) :=
  match t1, t2 with
  | qnat_fst, qnat_fst => true
  | qnat_snd, qnat_snd => true
  | qnat_tuplei n1 i1, qnat_tuplei n2 i2 => (n1 == n2) && ((i1 : nat) == i2)
  | qnat_ffuni n1 i1, qnat_ffuni n2 i2 => (n1 == n2) && ((i1 : nat) == i2)
  | _, _ => false
  end.

Lemma qnat_eqP : Equality.axiom qnat_eq_op.
Proof.
move=>t1 t2; apply/(iffP idP)=>[|->]; last first.
by elim: t2=>// */=; rewrite !eqxx.
elim: t1 t2=>[||n i|n i]; case=>//=;
by move=>m j/andP[]/eqP Hm; case: m / Hm j=>j/eqP/val_inj->.
Qed.

HB.instance Definition _ := hasDecEq.Build qnat qnat_eqP.

Definition qnat_to_nat3 (n : qnat) : nat * nat * nat :=
  match n with
  | qnat_fst => (0,0,0)
  | qnat_snd => (0,0,1)
  | qnat_tuplei n i => (1,n,(i:nat))
  | qnat_ffuni n i  => (2,n,(i:nat))
  end.

Definition nat3_to_qnat (n : nat * nat * nat) : qnat :=
  match n with
  | (0,0,0) => qnat_fst
  | (0,0,1) => qnat_snd
  | (1,n,i) => orapp qnat_fst (fun E : (i < n)%N = true =>
    qnat_tuplei (Ordinal E))
  | (2,n,i) => orapp qnat_fst (fun E : (i < n)%N = true =>
    qnat_ffuni (Ordinal E))
  | _ => qnat_fst
  end.

Lemma qnat_to_nat3K : cancel qnat_to_nat3 nat3_to_qnat.
Proof. by case=>// n; case=>i /= P; rewrite/= orappE. Qed.

HB.instance Definition _ := Choice.copy qnat (can_type qnat_to_nat3K).
HB.instance Definition _ := Countable.copy qnat (can_type qnat_to_nat3K).

Inductive qreg_index : Type :=
    | fault_index
    | prime_index of qvar & seq qnat
    | pair_index of qreg_index & qreg_index
    | tuple_index {n} of qType & ('I_n -> qreg_index)
    | ffun_index {n} of ('I_n -> qType) & ('I_n -> qreg_index).

Fixpoint qreg_index_to_tree (q : qreg_index) : tree _ :=
  match q with
  | fault_index => Leaf (None,[::],0,[::])
  | prime_index qv qn => Leaf (Some qv,qn,0,[::])
  | pair_index q1 q2 =>
      Node 0 [:: qreg_index_to_tree q1; qreg_index_to_tree q2]
  | tuple_index n qt f =>
      Node 1 ((Leaf (None,[::],n,[:: qt])) ::
              [seq (qreg_index_to_tree (f i)) | i : 'I_n])
  | ffun_index n qt f =>
      Node 2 ((Leaf (None,[::],n,[seq qt i | i : 'I_n])) ::
              [seq (qreg_index_to_tree (f i)) | i : 'I_n])
  end.

Fixpoint tree_to_qreg_index t : qreg_index :=
  match t with
  | Leaf (None,[::],0,[::]) => fault_index
  | Leaf (Some qv,qn,0,[::]) => prime_index qv qn
  | Node 0 [:: t1 ; t2] =>
      pair_index (tree_to_qreg_index t1) (tree_to_qreg_index t2)
  | Node 1 ((Leaf (None,[::],n,[:: qt])) :: s) => @tuple_index n qt 
      (fun i : 'I_n => nth fault_index (map tree_to_qreg_index s) i)
  | Node 2 ((Leaf (None,[::],n,st)) :: s) => @ffun_index n 
      (fun i : 'I_n => nth QUnit st i)
      (fun i : 'I_n => nth fault_index (map tree_to_qreg_index s) i)
  | _ => fault_index
  end.

Lemma qreg_index_to_treeK : cancel qreg_index_to_tree tree_to_qreg_index.
Proof.
elim=>//[/=?->?->//||]; case=>[t q IH|n t q IH]/=; rewrite ?fun0E//;
by do ! f_equal; apply/funext=>i;
  rewrite ?(nth_map (Leaf (None,[::],0,[::])))/= 
  1?(nth_map ord0) ?(size_enum_ord,size_map)// nth_ord_enum.
Qed.

HB.instance Definition _ := Equality.copy qreg_index
  (can_type qreg_index_to_treeK).
HB.instance Definition _ := Choice.copy qreg_index
  (can_type qreg_index_to_treeK).
HB.instance Definition _ := Countable.copy qreg_index
  (can_type qreg_index_to_treeK).

Definition index_fst_rec (s : qreg_index) :=
  match s with
  | prime_index x s' => prime_index x (rcons s' qnat_fst)
  | pair_index s1 s2 => s1
  | _ => fault_index
  end.
Definition index_fst := nosimpl index_fst_rec.
Lemma index_fstE : index_fst = index_fst_rec. Proof. by []. Qed.

Definition index_snd_rec (s : qreg_index) :=
  match s with
  | prime_index x s' => prime_index x (rcons s' qnat_snd)
  | pair_index s1 s2 => s2
  | _ => fault_index
  end.
Definition index_snd := nosimpl index_snd_rec.
Lemma index_sndE : index_snd = index_snd_rec. Proof. by []. Qed.

Definition index_ffuni_rec (s : qreg_index) {n} (i : 'I_n) :=
  match s with
  | prime_index x s' => prime_index x (rcons s' (qnat_ffuni i))
  | ffun_index n' _ s' =>
      orapp fault_index (fun E : n = n' => s' (cast_ord E i))
  | _ => fault_index
  end.
Definition index_ffuni := nosimpl index_ffuni_rec.
Lemma index_ffuniE : index_ffuni = index_ffuni_rec. Proof. by []. Qed.

Definition index_tuplei_rec (s : qreg_index) {n} (i : 'I_n) :=
  match s with
  | prime_index x s' => prime_index x (rcons s' (qnat_tuplei i))
  | tuple_index n' _ s' =>
      orapp fault_index (fun E : n = n' => s' (cast_ord E i))
  | _ => fault_index
  end.
Definition index_tuplei := nosimpl index_tuplei_rec.
Lemma index_tupleiE : index_tuplei = index_tuplei_rec. Proof. by []. Qed.

End qreg_index.

(* definition of quantum registers *)
(* a quantum register has a type *)
Section qreg.

Inductive qreg : qType -> Type :=
    (* construct from qvar *)
    | qreg_prime {T : qType} (x : qvart T)
     (* (H : `{memctxt x T}) *)
        : qreg T
    (* get component of a qreg *)
    | qreg_fst {T1 T2 : qType}
        (x : qreg (T1 * T2)) 
        : qreg T1
    | qreg_snd {T1 T2 : qType}
        (x : qreg (T1 * T2)) 
        : qreg T2
    | qreg_tuplei {n} {T : qType} (i : 'I_n)
        (x : qreg T.[n])
        : qreg T
    | qreg_ffuni {n} {T : 'I_n -> qType} (i : 'I_n)
        (x : qreg {qffun T})
        : qreg (T i)
    (* combine qregs *)
    | qreg_pair {T1 T2 : qType} (x1 : qreg T1)
        (x2 : qreg T2) 
        (* {H : `{qreg_expose (index_pair_disjoint s1 s2)}} *)
        : qreg (T1 * T2)
    | qreg_tuple {n} {T : qType}
        (fx : forall i : 'I_n, qreg T)
        (* {H : `{qreg_expose (index_fun_disjoint s)}} *)
        : qreg T.[n]
    | qreg_ffun {n} {T : 'I_n -> qType}
        (fx : forall i : 'I_n, qreg (T i))
        (* {H : `{qreg_expose (index_fun_disjoint s)}} *)
        : qreg {qffun T}.

Coercion qreg_prime : qvart >-> qreg.
Global Arguments qreg_prime {T} x.
Global Arguments qreg_pair {T1 T2} x1 x2.
Global Arguments qreg_tuple {n T} fx.
Global Arguments qreg_ffun {n T} fx.

Fixpoint index_of_qreg {T} (q : qreg T) : qreg_index :=
  match q with
  | qreg_prime _ x => (prime_index x [::])
  | qreg_fst _ _ x => (index_fst (index_of_qreg x))
  | qreg_snd _ _ x => (index_snd (index_of_qreg x))
  | qreg_tuplei _ _ i x => (index_tuplei (index_of_qreg x) i)
  | qreg_ffuni _ _ i x => (index_ffuni (index_of_qreg x) i)
  | qreg_pair _ _ x1 x2 => pair_index (index_of_qreg x1) (index_of_qreg x2)
  | qreg_tuple _ T fx => tuple_index T (fun i => (index_of_qreg (fx i)))
  | qreg_ffun _ T fx => ffun_index T (fun i => (index_of_qreg (fx i)))
  end.

Coercion index_of_qreg : qreg >-> qreg_index.

Fixpoint qtype_of_index_rec (l : seq qnat) (t : option qType) :=
  match l, t with
  | [::], _ => t
  | qnat_fst :: l, Some (QPair T1 T2) => qtype_of_index_rec l (Some T1)
  | qnat_snd :: l, Some (QPair T1 T2) => qtype_of_index_rec l (Some T2)
  | qnat_tuplei n i :: l, Some (QArray m T) =>
      orapp None (fun P : n = m => qtype_of_index_rec l (Some T))
  | qnat_ffuni n i :: l, Some (QDFFun m T) => orapp None
      (fun P : n = m => qtype_of_index_rec l (Some (T (cast_ord P i))))
  | _, _ => None
  end.

Fixpoint qtype_of_index (s : qreg_index) : option qType :=
  match s with
  | fault_index => None
  | prime_index x h =>  qtype_of_index_rec h (G.[?x])%fmap
  | pair_index s1 s2 => match qtype_of_index s1, qtype_of_index s2 with
                        | Some T1, Some T2 => Some (QPair T1 T2)
                        | _, _ => None
                        end
  | tuple_index n T fx =>
      if [forall i, qtype_of_index (fx i) == Some T]
      then Some (QArray n T) else None
  | ffun_index n T fx =>
      if [forall i, qtype_of_index (fx i) == Some (T i)]
      then Some (QDFFun T) else None
  end.

Lemma qtype_of_index_rec_rcons (l : seq qnat) x (t : option qType) :
  qtype_of_index_rec (rcons l x) t = 
  match x, qtype_of_index_rec l t with
  | qnat_fst, Some (QPair T1 T2) => Some T1
  | qnat_snd, Some (QPair T1 T2) => Some T2
  | qnat_tuplei n i, Some (QArray m T) => 
      orapp None (fun P : n = m => Some T)
  | qnat_ffuni n i, Some (QDFFun m T) => 
      orapp None (fun P : n = m => Some (T (cast_ord P i)))
  | _, _ => None
  end.
Proof.
elim: l x t=>//a l IH b t; rewrite rcons_cons/=; case: a=>[||n i|n i].
1,2: case: t; last (by case b);
  by case; (try by case: b); move=>??; apply: IH.
all: case: t; last (by case b); case; (try by case: b);
  move=>m T; rewrite /orapp; case: eqP=>?; by [case: b|apply: IH].
Qed.

Lemma qtype_of_index_rec_cat (T : option qType) s1 s2 :
  qtype_of_index_rec (s1 ++ s2) T =
    qtype_of_index_rec s2 (qtype_of_index_rec s1 T).
Proof.
elim/last_ind: s2 s1=>[s1|a s2 IH s1]; first by rewrite cats0.
by rewrite -rcons_cat !qtype_of_index_rec_rcons IH.
Qed.

Lemma index_typeK {T} (q : qreg T) : 
  qtype_of_index (index_of_qreg q) = Some T.
Proof.
dependent induction q; first by case: x=>/=?/eqP.
- move: IHq=>/=; case: (index_of_qreg q)=>//; clear q.
  + by move=>x l; rewrite/= qtype_of_index_rec_rcons=>->.
  + by move=>/= q1 q2; case: (qtype_of_index q1)=>// T3; 
    case: (qtype_of_index q2)=>// T4 H; inversion H.
  + by move=>/= n T q; case: [forall i, _].
  + by move=>/= n T q; case: [forall i, _].
- move: IHq=>/=; case: (index_of_qreg q)=>//; clear q.
  + by move=>x l; rewrite/= qtype_of_index_rec_rcons=>->.
  + by move=>/= q1 q2; case: (qtype_of_index q1)=>// T3; 
    case: (qtype_of_index q2)=>// T4 H; inversion H.
  + by move=>/= n T q; case: [forall i, _].
  + by move=>/= n T q; case: [forall i, _].
- move: IHq=>/=; case: (index_of_qreg q)=>//; clear q.
  + by move=>x l; rewrite /= qtype_of_index_rec_rcons=>->; rewrite orapp_id.
  + by move=>/= q1 q2; case: (qtype_of_index q1)=>// T3; 
    case: (qtype_of_index q2)=>// T4 H; inversion H.
  + move=>m S q/=; case E: [forall _, _] =>// /esym P; 
    inversion P; rewrite/index_tuplei/= orappE.
    by move: E=>/forallP/(_ (cast_ord H0 i))/eqP.
  + by move=>m S q/=; case: [forall _, _].
- move: IHq=>/=; case: (index_of_qreg q)=>//; clear q.
  + by move=>x l; rewrite /= qtype_of_index_rec_rcons=>->;
    rewrite orapp_id cast_ord_id.
  + by move=>/= q1 q2; case: (qtype_of_index q1)=>// T3; 
    case: (qtype_of_index q2)=>// T4 H; inversion H.
  + by move=>m S q/=; case: [forall _, _].
  + move=>m S q/=; case E: [forall _, _] =>// /esym P; 
    inversion P; rewrite/index_ffuni/= orappE.
    case: m / H0 S q E P H1=>S q /forallP/(_ i)/eqP H1 _ /inj_existT->.
    by rewrite cast_ord_id.
- by rewrite/= IHq1 IHq2.
- by rewrite/= forallbTP// =>i; apply/eqP.
- by rewrite/= forallbTP// =>i; apply/eqP.
Qed.

Lemma fault_indexF {T} (x : qreg T) : index_of_qreg x != fault_index.
Proof. by apply/negP=>P; move: P (index_typeK x)=>/eqP->. Qed.

Lemma pair_ffun_indexN (T1 T2 : qType) (x : qreg (QPair T1 T2)) 
  n t (s : 'I_n -> qreg_index) : index_of_qreg x != ffun_index t s.
Proof.
by apply/negP=>P; move: P (index_typeK x)=>/eqP->/=;
case: [forall _, _].
Qed.

Lemma pair_tuple_indexN (T1 T2 : qType) (x : qreg (QPair T1 T2)) 
  n t (s : 'I_n -> qreg_index) : index_of_qreg x != tuple_index t s.
Proof.
by apply/negP=>P; move: P (index_typeK x)=>/eqP->/=;
case: [forall _, _].
Qed.

Lemma tuple_pair_indexN m (T : qType) (x : qreg (QArray m T)) 
  s1 s2 :  index_of_qreg x != pair_index s1 s2.
Proof.
apply/negP=>P; move: P (index_typeK x)=>/eqP->/=; 
by do ! case: (qtype_of_index _)=>//?.
Qed.

Lemma tuple_ffun_indexN m (T : qType) (x : qreg (QArray m T)) 
  n t (s : 'I_n -> qreg_index) :  index_of_qreg x != ffun_index t s.
Proof.
by apply/negP=>P; move: P (index_typeK x)=>/eqP->/=;
case: [forall _, _].
Qed.

Lemma ffun_pair_indexN m (T : 'I_m -> qType) (x : qreg (QDFFun T)) 
  s1 s2 :  index_of_qreg x != pair_index s1 s2.
Proof.
apply/negP=>P; move: P (index_typeK x)=>/eqP->/=; 
by do ! case: (qtype_of_index _)=>//?.
Qed.

Lemma ffun_tuple_indexN m (T : 'I_m -> qType) (x : qreg (QDFFun T)) 
  n t (s : 'I_n -> qreg_index) :  index_of_qreg x != tuple_index t s.
Proof.
by apply/negP=>P; move: P (index_typeK x)=>/eqP->/=;
case: [forall _, _].
Qed.

Lemma tuple_index_eq m (T : qType) (x : qreg (QArray m T)) 
  n t (s : 'I_n -> qreg_index) : index_of_qreg x = tuple_index t s -> n = m.
Proof.
move=>P; move: (index_typeK x); rewrite P/=; case: [forall _, _] =>// H.
by inversion H.
Qed.

Lemma ffun_index_eq m (T : 'I_m -> qType) (x : qreg (QDFFun T)) 
  n t (s : 'I_n -> qreg_index) : index_of_qreg x = ffun_index t s -> n = m.
Proof.
move=>P; move: (index_typeK x); rewrite P/=; case: [forall _, _] =>// H.
by inversion H.
Qed.

(* define the seq of basic indexes *)
Definition is_basic_index (q : qvar) (s : seq qnat) : bool :=
  match qtype_of_index (prime_index q s) with
  | Some QUnit | Some QBool | Some (QOrd _) | Some (QOption _)
  | Some (QSum _ _) => true
  | _ => false
  end.

Structure basic_index := Basic_Index {
  basic_qvar : qvar;
  basic_seq : seq qnat;
  _ : is_basic_index basic_qvar basic_seq
}.

Definition basic_index_to_qreg_index (x : basic_index) := 
  prime_index (basic_qvar x) (basic_seq x).
Coercion basic_index_to_qreg_index : basic_index >-> qreg_index.

Definition basic_index_to_pair x := ((basic_qvar x), (basic_seq x)).
Definition pair_to_basic_index (v : qvar * seq qnat) :=
  orapp None (fun E : is_basic_index v.1 v.2 = true => Some (Basic_Index E)).

Lemma basic_indexK : pcancel basic_index_to_pair pair_to_basic_index.
Proof.
by case=>qv sq P; rewrite /pair_to_basic_index /basic_index_to_pair/= orappE.
Qed.

Lemma basic_indexKV : ocancel pair_to_basic_index basic_index_to_pair.
Proof.
case=>v s; rewrite /pair_to_basic_index /basic_index_to_pair/=/orapp;
by case: eqP.
Qed.

HB.instance Definition _ := Equality.copy basic_index (pcan_type basic_indexK).
HB.instance Definition _ := Choice.copy basic_index (pcan_type basic_indexK).
HB.instance Definition _ := Countable.copy basic_index (pcan_type basic_indexK).

Fixpoint ssqnat (T : qType) (s : seq qnat) : seq (seq qnat) :=
  match T with
  | QUnit | QBool | QOrd _ | QOption _ | QSum _ _ => [:: s]
  | QPair T1 T2 =>
      (ssqnat T1 (rcons s qnat_fst)) ++ (ssqnat T2 (rcons s qnat_snd))
  | QArray n T =>
      flatten [seq (ssqnat T (rcons s (qnat_tuplei i))) | i : 'I_n]
  | QDFFun n fT =>
      flatten [seq (ssqnat (fT i) (rcons s (qnat_ffuni i))) | i : 'I_n]
  end.

Definition enum_basic_index :=
  pmap pair_to_basic_index (flatten [seq (map (fun j => ((fsval i), j))
    (ssqnat (G.[fsvalP i]%fmap) [::])) | i : domf G]).

Lemma allpairs_uniq_dep1 [S T: eqType] [s : seq S] [t : S -> seq T] :
    uniq s ->
    {in s, forall x : S, uniq (t x)} ->
    {in s &, forall x y : S,
      forall i j, i \in t x -> j \in t y -> i = j -> x = y} ->
    uniq (flatten [seq t x | x <- s]).
Proof.
move=>H1 H2 H3; under [X in flatten X] eq_map do rewrite - [t _]map_id.
apply allpairs_uniq_dep=>//.
move=>[] x px [] y py /flatten_mapP[] ix Pix/=/mapP[] jx Pjx Px
/flatten_mapP[] iy Piy/=/mapP[] jy Pjy Py.
inversion Px. inversion Py. move=>Pxy.
by rewrite Pxy (H3 ix iy Pix Piy jx jy Pjx Pjy Pxy).
Qed.

Lemma allpairs_uniq_dep2 [S T R: eqType] [f : T -> R] [s : seq S] 
  [t : S -> seq T] :
    uniq s ->
    {in s, forall x : S, uniq (t x)} ->
    {in s &, forall x y : S,
      forall i j, i \in t x -> j \in t y -> i = j -> x = y} ->
    injective f ->
    uniq [seq f y | x <- s, y <- t x].
Proof.
move=>H1 H2 H3 f_inj; apply: allpairs_uniq_dep1=>//.
by move=>x /H2 Pt; rewrite map_inj_in_uniq// =>i j _ _ /f_inj.
by move=>x y Px Py i j /mapP[] ix Pix -> /mapP[] iy Piy -> /f_inj; apply: H3.
Qed.

Lemma subseq_flatten [S T: eqType] [s : seq S] [t : S -> seq T] sx :
  (exists x, x \in s /\ subseq sx (t x)) ->
    (subseq sx (flatten [seq t x | x <- s])).
Proof.
elim: s =>[[x][] | a s IH [x][]] //=; rewrite inE=> /orP [/eqP <- P|];
first by apply (subseq_trans P (prefix_subseq _ _)).
move=>Px Psx; apply/(subseq_trans _ (suffix_subseq _ _))/IH.
by exists x; split.
Qed.

Lemma prefix_ssqnat (T : qType) (s : seq qnat) i : 
  i \in (ssqnat T s) -> seq.prefix s i.
Proof.
elim: T s i=> //= [||?|??|? IH1 ? IH2|????|n T IH|n T IH] s i.
1-4,6: rewrite mem_seq1=>/eqP->; apply/prefix_refl.
rewrite mem_cat=>/orP[/IH1|/IH2]; apply/prefix_trans/prefix_rcons.
all: move=>/flatten_mapP[] j _ /IH; apply/prefix_trans/prefix_rcons.
Qed.

Lemma uniq_ssqnat (T : qType) (s : seq qnat) : uniq (ssqnat T s).
Proof.
elim: T s=>//=[T1 IH1 T2 IH2 s | n T IH s | n T IH s].
- rewrite cat_uniq; do 2 (apply/andP; split=>//).
  apply/hasPn=>x/prefix_ssqnat P1; apply/negP=>/prefix_ssqnat; 
  by move: P1; rewrite !prefixE !size_rcons=>/eqP->/eqP/rcons_inj.
all: apply: allpairs_uniq_dep1=>//; first (by apply enum_uniq);
  move=>x y _ _ i j /prefix_ssqnat + /prefix_ssqnat + Pij;
  rewrite !prefixE !size_rcons Pij=>/eqP->/eqP/rcons_inj P;
  by inversion P; move: (inj_existT H0).
Qed.

Lemma qtype_of_index_recN (s : seq qnat) : qtype_of_index_rec s None = None.
Proof. by case: s=>//=; case. Qed.

Lemma basic_index_in_domfG (b : basic_index) : basic_qvar b \in domf G.
Proof.
case: b=>/= v s; rewrite /is_basic_index.
destruct (qtype_of_index (prime_index v s)) eqn: E=>// _.
by move: E=>/=; case: (fndP G v)=>//; rewrite qtype_of_index_recN.
Qed.

Lemma subseq_ssqnat (s1 : seq qnat) (T : qType) (s2 : seq qnat) T' :
  qtype_of_index_rec s2 (Some T) = Some T' ->
    subseq (ssqnat T' (s1 ++ s2)) (ssqnat T s1).
Proof.
elim/last_ind: s2 T'; first by move=>T'/= PT; inversion PT; rewrite cats0.
move=>s x IH T1; rewrite qtype_of_index_rec_rcons; case: x=>[||n i|n i];
destruct (qtype_of_index_rec s (Some T)) =>//; case: q IH=>//.
- move=>T2 T3 + /esym P; inversion P;
  case: T2 / H0 P => _ /(_ (T1 * T3)%QT erefl).
  by apply subseq_trans; rewrite -rcons_cat /ssqnat prefix_subseq.
- move=>T2 T3 + /esym P; inversion P;
  case: T3 / H0 P => _ /(_ (T2 * T1)%QT erefl).
  by apply subseq_trans; rewrite -rcons_cat /ssqnat suffix_subseq.
- move=>m; rewrite /orapp; case: eqP=>// P; case: m / P => T2 + /esym PT; 
  inversion PT =>/(_ (T2).[(n)]%QT erefl).
  apply/subseq_trans; rewrite -rcons_cat /ssqnat.
  apply: subseq_flatten; exists i; split=>//; apply mem_enum.
- move=>m; rewrite /orapp; case: eqP=>// P; case: m / P; 
  rewrite cast_ord_id => T2+ /esym PT.
  inversion PT =>/(_ {qffun T2}%QT erefl); apply/subseq_trans.
  rewrite -rcons_cat /ssqnat.
  apply: subseq_flatten; exists i; split=>//; apply mem_enum.
Qed.

Lemma basic_index_in_ssqnat (b : basic_index) :
  (basic_index_to_pair b).2 \in ssqnat G.[basic_index_in_domfG b]%fmap [::].
Proof.
case: b=>/= v s P.
have [T PT]: exists T, G.[?v]%fmap = Some T.
move: P; rewrite /is_basic_index /qtype_of_index.
case: (G.[?v]%fmap)=>[T _|]; by [exists T | rewrite qtype_of_index_recN].
move: (in_fnd (basic_index_in_domfG (Basic_Index P)))=>/=; rewrite PT=>PS.
inversion PS; rewrite -H0; clear PS H0.
move: P; rewrite /is_basic_index /qtype_of_index PT.
destruct (qtype_of_index_rec s (Some T)) eqn:E=>// E1.
case: q E E1 =>//[||n|T'|T1 T2] /(subseq_ssqnat [::]) /mem_subseq/(_ s)/=;
by rewrite mem_seq1 eqxx.
Qed.

Lemma basic_index_in_enum (b : basic_index) : b \in enum_basic_index.
Proof.
rewrite/enum_basic_index mem_pmap; apply/mapP.
exists (basic_qvar b, basic_seq b).
apply/flatten_mapP; exists [` basic_index_in_domfG b]%fset;
first by apply/mem_enum.
apply/mapP; exists (basic_index_to_pair b).2=>//;
apply/basic_index_in_ssqnat.
by case: b=>/= v s P; rewrite/pair_to_basic_index orappE.
Qed.

Lemma uniq_enum_basic_index : uniq enum_basic_index.
Proof.
apply/(pmap_uniq basic_indexKV)/allpairs_uniq_dep.
- apply: enum_uniq.
- move=>i _; apply: uniq_ssqnat.
move=>/=[]x px [] y py/= _ _ P; inversion P.
by f_equal; apply/val_inj.
Qed.

Lemma basic_index_enumP : Finite.axiom enum_basic_index.
Proof.
apply/Finite.uniq_enumP.
- exact: uniq_enum_basic_index.
- by move=>/= i; rewrite basic_index_in_enum.
Qed.

HB.instance Definition _ := isFinite.Build basic_index basic_index_enumP.

Fixpoint qi2seq_rec (s : qreg_index) : seq basic_index :=
  match s with
  | fault_index => [::]
  | prime_index v s => 
      match qtype_of_index (prime_index v s) with
      | None => [::]
      | Some T => pmap pair_to_basic_index [seq (v,i) | i <- (ssqnat T s)]
      end
  | pair_index s1 s2 => qi2seq_rec s1 ++ qi2seq_rec s2
  | tuple_index n _ f => flatten [seq qi2seq_rec (f i) | i : 'I_n]
  | ffun_index n _ f => flatten [seq qi2seq_rec (f i) | i : 'I_n]
  end.

Definition qi2seq := nosimpl qi2seq_rec.
Definition qr2seq {T} (x : qreg T) := nosimpl
  (qi2seq (index_of_qreg x)).

Lemma pmap_flatten {S T : Type} (f : T -> option S) ss :
  pmap f (flatten ss) = flatten (map (pmap f) ss).
Proof. by elim: ss => // s ss /= <-; apply: pmap_cat. Qed.

Ltac ltest := try do [by move=>???/=; case: [forall _, _] |
by move=>??/=; do 2 case: (qtype_of_index _)=>//].

Lemma qi2seq_pairE {T1 T2} (x : qreg_index) : 
  qtype_of_index x = Some (T1 * T2)%QT ->
  qi2seq x = (qi2seq (index_fst x) ++ qi2seq (index_snd x))%SEQ.
Proof.
case: x=>//; ltest; move=>q l.
rewrite/index_fst/index_snd/= /qi2seq/= !qtype_of_index_rec_rcons=>->.
by rewrite -pmap_cat -map_cat.
Qed.

Lemma qr2seq_pairE {T1 T2} (x : qreg (T1 * T2)) : 
  qr2seq x = (qr2seq (qreg_fst x) ++ qr2seq (qreg_snd x))%SEQ.
Proof. by move: (index_typeK x)=>/qi2seq_pairE. Qed.

Lemma qi2seq_tupleE {n T} (x : qreg_index) :
  qtype_of_index x = Some (T.[n])%QT ->
  qi2seq x = flatten [seq qi2seq (index_tuplei x i) | i : 'I_n].
Proof.
case: x=>//; ltest.
- move=>v s; rewrite/index_tuplei/qi2seq/==>P1; rewrite P1.
  under [X in flatten X]eq_map do
    rewrite qtype_of_index_rec_rcons P1 orapp_id.
  by rewrite/= map_flatten pmap_flatten -2!map_comp.
- move=>m T' q/=; case: [forall _, _] =>// /esym P.
  inversion P; case: m / H0 q P=>q _; rewrite/qi2seq/=; f_equal.
  by under [RHS]eq_map do rewrite /index_tuplei/= orapp_id cast_ord_id.
Qed.

Lemma qr2seq_tupleE {n T} (x : qreg T.[n]) :
  qr2seq x = flatten [seq qr2seq (qreg_tuplei i x) | i : 'I_n].
Proof. by move: (index_typeK x)=>/qi2seq_tupleE. Qed.

Lemma qi2seq_ffunE {n} {T : 'I_n -> qType} (x : qreg_index) :
  qtype_of_index x = Some ({qffun T})%QT ->
    qi2seq x = flatten [seq qi2seq (index_ffuni x i) | i : 'I_n].
Proof. 
case: x=>//; ltest.
- move=>v s; rewrite/index_ffuni/qi2seq/==>P1; rewrite P1.
  under [X in flatten X]eq_map do
    rewrite qtype_of_index_rec_rcons P1 orapp_id cast_ord_id.
  by rewrite/= map_flatten pmap_flatten -2!map_comp.
- move=>m T' q/=. case: [forall _, _] =>// /esym P.
  inversion P; case: m / H0 T' q P H1 =>T' q _ _; rewrite/qi2seq/=; f_equal.
  by under [RHS]eq_map do rewrite /index_ffuni/= orapp_id cast_ord_id.
Qed.

Lemma qr2seq_ffunE {n} {T : 'I_n -> qType} (x : qreg {qffun T}) :
  qr2seq x = flatten [seq qr2seq (qreg_ffuni i x) | i : 'I_n].
Proof. by move: (index_typeK x)=>/qi2seq_ffunE. Qed.

Fixpoint qtype_size (t : qType) :=
  match t with
  | QUnit | QBool | QOrd _ | QOption _ | QSum _ _ => 1
  | QPair t1 t2 => qtype_size t1 + qtype_size t2
  | QArray n t => n * qtype_size t
  | QDFFun n ft => \sum_i qtype_size (ft i)
  end.

Lemma exists_qreg {T} (i : qreg_index) :
  qtype_of_index i = Some T -> 
    exists (x : qreg T), index_of_qreg x = i.
Proof.
move: T i.
have P_prime: forall T v s, qtype_of_index (prime_index v s) = Some T -> 
  exists (x : qreg T), index_of_qreg x = prime_index v s.
  move=>++s; elim/last_ind: s;
    first by move=>T v/= /eqP Pv; exists (@qreg_prime T (QVarT Pv)).
  move=>s i IH T v/=; rewrite qtype_of_index_rec_rcons; case: i=>[||n i|n i].
  - destruct (qtype_of_index_rec _) eqn:E=>//; case: q E=>// T1 T2 + /esym Pv.
    by inversion Pv; case: T1 / H0 Pv=> _ /IH[x Px];
    exists (qreg_fst x)=>/=; rewrite Px.
  - destruct (qtype_of_index_rec _) eqn:E=>//; case: q E=>// T1 T2 + /esym Pv.
    by inversion Pv; case: T2 / H0 Pv=> _ /IH[x Px];
    exists (qreg_snd x)=>/=; rewrite Px.
  - destruct (qtype_of_index_rec _) eqn:E=>//; case: q E=>// m T1.
    rewrite/orapp; case: eqP=>// Pvm; case: m / Pvm=>/IH[x Px] /esym Pv;
    inversion Pv; by exists (qreg_tuplei i x); rewrite/= Px.
  - destruct (qtype_of_index_rec _) eqn:E=>//; case: q E=>// m T1.
    rewrite/orapp;  case: eqP=>// Pvm.
    case: m / Pvm T1=>T1; rewrite cast_ord_id=>+ /esym Pv; inversion Pv.
    by move=>/IH[x Px]; exists (qreg_ffuni i x)=>/=; rewrite Px.
elim=>[||n|??||????||].
1-4,6: case=>//=; ltest; exact: P_prime.
- move=>T1 IH1 T2 IH2; case=>//=[|x1 x2||]; ltest; first exact: P_prime.
  destruct (qtype_of_index x1) eqn:E1=>//;
  destruct (qtype_of_index x2) eqn:E2=>// Pv.
  by move: E1 E2; inversion Pv=>/IH1[x <-]/IH2[y <-]; exists (qreg_pair x y).
- move=>n T IH; case=>//=[||m T' x|]; ltest; first exact: P_prime.
  case E: [forall _, _] =>// /esym Pv;
  move: IH E; inversion Pv=>IH /forallP P1.
  have P2: forall i, {xi : qreg T' | index_of_qreg xi = (x i)}.
    by move=>i; move: (P1 i)=>/eqP/IH/cid.
  exists (qreg_tuple (fun i : 'I_m => projT1 (P2 i))).
  by rewrite/=; f_equal; apply/funext=>i; move: (projT2 (P2 i)).
- move=>n T IH; case=>//=[|||m T' x]; ltest; first exact: P_prime.
  case E: [forall _, _] =>// /esym Pv; inversion Pv; 
  case: m / H0 T' x E Pv H1=>T' x + _ /inj_existT Pt;
  case: T' / Pt=>/forallP P1.
  have P2: forall i, {xi : qreg (T i) | index_of_qreg xi = (x i)}.
    by move=>i; move: (P1 i)=>/eqP/IH/cid.
  exists (qreg_ffun (fun i : 'I_n => projT1 (P2 i))).
  by rewrite/=; f_equal; apply/funext=>i; move: (projT2 (P2 i)).
Qed.

Lemma ffun_indexE n t (s : 'I_n -> qreg_index) (i : 'I_n) :
  index_ffuni (ffun_index t s) i = s i.
Proof.
by rewrite/index_ffuni/=/orapp;
case: eqP=>// P; rewrite cast_ord_id.
Qed.

Lemma tuple_indexE n t (s : 'I_n -> qreg_index) (i : 'I_n) :
  index_tuplei (tuple_index t s) i = s i.
Proof.
by rewrite/index_tuplei/=/orapp;
case: eqP=>// P; rewrite cast_ord_id.
Qed.

Lemma qtype_of_pair T1 T2 (x : qreg_index) :
  qtype_of_index x = Some (QPair T1 T2) ->
    qtype_of_index (index_fst x) = Some T1 /\
    qtype_of_index (index_snd x) = Some T2.
Proof.
case: x=>//; ltest.
by move=>x s/=; rewrite !qtype_of_index_rec_rcons =>->.
by move=>q1 q2/=; rewrite /index_fst/= /index_snd/=; 
  do 2 case: (qtype_of_index _)=>//; move=> ?? Pv; inversion Pv.
Qed.

Lemma qi2seq_of_pair T1 T2 (x : qreg_index) :
  qtype_of_index x = Some (QPair T1 T2) ->
    qi2seq x = (qi2seq (index_fst x) ++ qi2seq (index_snd x))%SEQ.
Proof.
move=>P; move: P (qtype_of_pair P)=> + []; case: x; ltest.
by move=>x s/= P1 P2 P3; rewrite /qi2seq/= P1 P2 P3/= map_cat pmap_cat.
Qed.

Lemma qtype_of_tuple n T (x : qreg_index) :
  qtype_of_index x = Some (QArray n T) ->
    forall (i : 'I_n), qtype_of_index (index_tuplei x i) = Some T.
Proof.
case: x=>//; ltest.
- by move=>x s/= P i; rewrite qtype_of_index_rec_rcons P orapp_id.
- move=>m T' q/=; case E: [forall _, _] =>// /esym Pv i.
  inversion Pv; case: m / H0 q E Pv; case: T' / H1=>q /forallP/(_ i)/eqP<- _.
  by rewrite tuple_indexE.
Qed.

Lemma qi2seq_of_tuple n T (x : qreg_index) :
  qtype_of_index x = Some (QArray n T) ->
    qi2seq x = flatten [seq qi2seq (index_tuplei x i ) | i : 'I_n ].
Proof.
move=>P; move: P (qtype_of_tuple P); case: x=>[||||] =>/=; ltest.
- move=>x s P1 P2;
  rewrite /qi2seq/= P1/= map_flatten pmap_flatten -2!map_comp.
  by under [X in _ = flatten X]eq_map do rewrite P2.
- move=>m T' q; case: [forall _, _] =>// /esym Pv; inversion Pv.
  case: m / H0 q Pv => q _ _; rewrite /qi2seq/=; f_equal.
  by under [RHS]eq_map do rewrite tuple_indexE.
Qed.

Lemma qtype_of_ffun n (T : 'I_n -> qType) (x : qreg_index) :
  qtype_of_index x = Some (QDFFun T) ->
    forall (i : 'I_n), qtype_of_index (index_ffuni x i) = Some (T i).
Proof.
case: x=>//; ltest.
- by move=>x s/= P i;
  rewrite qtype_of_index_rec_rcons P orapp_id cast_ord_id.
- move=>m T' q/=; case E: [forall _, _] =>// /esym Pv i; inversion Pv.
  case: m / H0 T' q E Pv H1=>T' q /forallP/(_ i)/eqP P1 _ /inj_existT ->.
  by rewrite ffun_indexE.
Qed.

Lemma qi2seq_of_ffun n (T : 'I_n -> qType) (x : qreg_index) :
  qtype_of_index x = Some (QDFFun T) ->
    qi2seq x = flatten [seq qi2seq (index_ffuni x i ) | i : 'I_n ].
Proof.
move=>P; move: P (qtype_of_ffun P); case: x=>[||||] =>/=; ltest.
- move=>x s P1 P2;
  rewrite /qi2seq/= P1/= map_flatten pmap_flatten -2!map_comp.
  by under [X in _ = flatten X]eq_map do rewrite P2.
- move=>m T' q; case: [forall _, _] =>// /esym Pv; inversion Pv.
  case: m / H0 T' q Pv H1=>T' q _ _ _; rewrite /qi2seq/=; f_equal.
  by under [RHS]eq_map do rewrite ffun_indexE.
Qed.

Lemma size_qi2seq T (x : qreg_index) : 
  qtype_of_index x = Some T  -> size (qi2seq x) = qtype_size T.
Proof.
elim: T x=>/=[x|x|n x|? _ x||? _ ? _ x||].
1-4,6: rewrite /qi2seq; case: x=>//=[v s IH|||]; ltest;
  by rewrite/= IH size_pmap/= /pair_to_basic_index//=
    orappE// /is_basic_index/= IH.
- move=>? IH1 ? IH2 x Px; rewrite (qi2seq_pairE Px) size_cat 1?IH1 1?IH2//;
  by move: (qtype_of_pair Px)=>[].
- move=>?? IH x Px; rewrite (qi2seq_tupleE Px) size_flatten /shape -map_comp.
  move: (qtype_of_tuple Px)=>Pi.
  under eq_map do rewrite/= (IH _ (Pi _)).
  by rewrite sumnE big_map big_enum/= sum_nat_const card_ord.
- move=>?? IH x Px; rewrite (qi2seq_ffunE Px) size_flatten /shape -map_comp.
  move: (qtype_of_ffun Px)=>Pi.
  under eq_map do rewrite/= (IH _ _ (Pi _)).
  by rewrite sumnE big_map big_enum.
Qed.

Lemma size_qr2seq {T} (x : qreg T) : size (qr2seq x) = qtype_size T.
Proof. by move: (index_typeK x)=>/size_qi2seq. Qed.

(* Notation qregT := {x : qType & qreg x}.
Definition to_qregT {T} (x : qreg T) : qregT := existT _ _ x.
Coercion to_qregT : qreg >-> sigT.
Definition of_qregT (x : qregT) := tagged x.
Coercion of_qregT : sigT >-> qreg.

Lemma to_qregTK {T} (x : qreg T) : of_qregT (to_qregT x) = x.
Proof. by []. Qed.
Lemma of_qregTK (x : qregT) : to_qregT (of_qregT x) = x.
Proof. by case x. Qed. *)

(* two qregs have the same index *)
Definition eq_qreg T (q1 q2 : qreg T) := nosimpl (qr2seq q1 = qr2seq q2).
Infix "=r" := eq_qreg (at level 70).
(* Definition eq_qregT (q1 q2 : qregT) := nosimpl (qr2seq q1 = qr2seq q2).
Infix "=rt" := eq_qregT (at level 70). *)

Lemma eq_qreg_trans T : 
  forall (a b c: qreg T), a =r b -> b =r c -> a =r c.
Proof. by rewrite /eq_qreg; move=>a b c -> ->. Qed.
Lemma eq_qreg_refl T : forall (a: qreg T), a =r a.
Proof. by []. Qed.
Lemma eq_qreg_sym T : forall (a b : qreg T), a =r b -> b =r a.
Proof. by rewrite /eq_qreg; move=>a b ->. Qed.

(* Lemma eq_qregT_trans : 
  forall (a b c: qregT), a =rt b -> b =rt c -> a =rt c.
Proof. by rewrite /eq_qregT; move=>a b c -> ->. Qed.
Lemma eq_qregT_refl : forall (a: qregT), a =rt a.
Proof. by []. Qed.
Lemma eq_qregT_sym : forall (a b : qregT), a =rt b -> b =rt a.
Proof. by rewrite /eq_qregT; move=>a b ->. Qed. *)

Lemma eq_qreg_fst T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  qreg_fst (qreg_pair x1 x2) =r x1.
Proof. by []. Qed.
Lemma eq_qreg_snd T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  qreg_snd (qreg_pair x1 x2) =r x2.
Proof. by []. Qed.
Lemma eq_qreg_tuplei n T i (x : 'I_n -> qreg T) :
  qreg_tuplei i (qreg_tuple x) =r x i.
Proof.
by rewrite/eq_qreg/qr2seq/index_of_qreg
  /index_tuplei/= orapp_id cast_ord_id.
Qed.
Lemma eq_qreg_ffuni n {T : 'I_n -> qType} i (x : forall i, qreg (T i)) :
  qreg_ffuni i (qreg_ffun x) =r x i.
Proof.
by rewrite/eq_qreg/qr2seq/index_of_qreg/index_ffuni/=
  orapp_id cast_ord_id.
Qed.

Lemma eq_qreg_pair T1 T2 (x : qreg (T1 * T2)) :
  qreg_pair (qreg_fst x) (qreg_snd x) =r x.
Proof.
by move: (index_typeK x)=>/qi2seq_of_pair;
rewrite /eq_qreg /qr2seq.
Qed.

Lemma eq_qreg_tuple n T (x : qreg (T.[n])) :
  qreg_tuple (fun i => qreg_tuplei i x) =r x.
Proof.
by move: (index_typeK x)=>/qi2seq_of_tuple;
rewrite /eq_qreg /qr2seq.
Qed.

Lemma eq_qreg_ffun n (T : 'I_n -> qType) (x : qreg {qffun T}) :
  qreg_ffun (fun i => qreg_ffuni i x) =r x.
Proof.
by move: (index_typeK x)=>/qi2seq_of_ffun;
rewrite /eq_qreg /qr2seq.
Qed.

Definition eq_qregE := (eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, 
  eq_qreg_ffuni, eq_qreg_pair, eq_qreg_tuple, eq_qreg_ffun).

Lemma eq_qreg_from_tuple n T (f1 f2 : 'I_n -> qreg T) :
  (forall i, f1 i =r f2 i) -> qreg_tuple f1 =r qreg_tuple f2.
Proof.
rewrite /eq_qreg/=/qr2seq/qi2seq/= => P; 
by under [X in flatten X]eq_map do rewrite P.
Qed.
Lemma eq_qreg_from_ffun n (T : 'I_n -> qType) (f1 f2 : forall i, qreg (T i)) :
  (forall i, f1 i =r f2 i) -> qreg_ffun f1 =r qreg_ffun f2.
Proof.
rewrite /eq_qreg/=/qr2seq/qi2seq/= => P; 
by under [X in flatten X]eq_map do rewrite P.
Qed.

(* a valid qreg has every basic element uniq *)
Definition valid_qreg_rec T (x : qreg T) := uniq (qr2seq x).
Definition valid_qreg := nosimpl valid_qreg_rec.
(* two qreg are disjoint iff their basic elements are distinct *)
Definition disjoint_qreg_rec Tx Ty (x : qreg Tx) (y : qreg Ty) :=
  [disjoint (qr2seq x) & (qr2seq y)].
Definition disjoint_qreg := disjoint_qreg_rec.

(* define on the index *)
Definition disjoint_qregI_rec (x y : qreg_index) :=
  [disjoint (qi2seq x) & (qi2seq y)].
Definition disjoint_qregI := nosimpl disjoint_qregI_rec.
Definition valid_qregI_rec (x : qreg_index) := uniq (qi2seq x).
Definition valid_qregI := nosimpl valid_qregI_rec.

(* fset_qreg ; use lock without unlockable here to avoid any possible unlock *)
Fact fset_qreg_key : unit. Proof. by []. Qed.
Definition fset_qreg T (x : qreg T) :=
  locked_with fset_qreg_key (seq_fset fset_qreg_key (qr2seq x)).
Coercion fset_qreg : qreg >-> finset_of.

Ltac luf := rewrite/index_fst/index_snd/index_tuplei/index_ffuni
  /disjoint_qregI/disjoint_qregI_rec/valid_qregI/valid_qregI_rec
  /disjoint_qreg/disjoint_qreg_rec/valid_qreg/valid_qreg_rec
  /qr2seq/qi2seq/=.

Lemma valid_qregE T (x : qreg T) : valid_qreg x = uniq (qr2seq x).
Proof. by luf. Qed.
Lemma disjoint_qregE Tx Ty (x : qreg Tx) (y : qreg Ty) : 
  disjoint_qreg x y = [disjoint (qr2seq x) & (qr2seq y)].
Proof. by luf. Qed.
Lemma fset_qregE T (x : qreg T) : fset_qreg x =i qr2seq x.
Proof.
by rewrite [fset_qreg _](unlock [unlockable of fset_qreg x]);
apply/seq_fsetE.
Qed.
Lemma fdisjoint_qregP Tx Ty (x : qreg Tx) (y : qreg Ty) :
  disjoint_qreg x y = [disjoint x & y]%fset.
Proof.
rewrite disjoint_qregE; apply/eqb_iff; split.
by move=>/disjointFr P; apply/fdisjointP=>i; rewrite !fset_qregE=>/P->.
move=>/fdisjointP P; rewrite disjoint_has; apply/hasP=>[[i Pi1 Pi2]].
move: (P i); rewrite !fset_qregE Pi1 Pi2/=; auto.
Qed.
Lemma disjoint_qregIE Tx Ty (x : qreg Tx) (y : qreg Ty) :
  disjoint_qreg x y = disjoint_qregI x y.
Proof. by luf. Qed.
Lemma valid_qregIE T (x : qreg T) :
  valid_qreg x = valid_qregI x.
Proof. by luf. Qed.


(* move *)
Lemma disjoint_flatten_seq {T: finType} {S : eqType} (t : S -> seq T) (s : seq S) (A : pred T) :
  [disjoint flatten [seq t i | i <- s] & A] <-> 
    {in s, forall i, [disjoint t i & A]}.
Proof.
elim: s=>//=. by rewrite eq_disjoint0//=; apply/esym/forallP.
move=>i s []P1 P2; rewrite disjoint_cat; split.
by move=>/andP[] Pi/P1 Px j; rewrite inE=>/orP[/eqP->//|/Px].
move=>Pi; apply/andP; split; first by apply/Pi; rewrite inE eqxx.
by apply/P2=>j Pj; apply/Pi; rewrite inE Pj orbT.
Qed.

(* move *)
Lemma disjoint_flatten {T S: finType} (t : S -> seq T) (A : pred T) :
  [disjoint flatten [seq t i | i : S] & A] =
    [forall i, [disjoint t i & A]].
Proof.
apply/eqb_iff; rewrite disjoint_flatten_seq; split.
by move=>Pi; apply/forallP=>i; apply: Pi; rewrite mem_enum.
by move=>/forallP Pi i _.
Qed.

(* move *)
Lemma cat_uniq_disjoint {T : finType} (s1 s2 : seq T) :
  uniq (s1 ++ s2) = [&& uniq s1, [disjoint s1 & s2] & uniq s2].
Proof. by rewrite cat_uniq disjoint_sym disjoint_has. Qed.

(* move *)
Lemma flatten_uniq_disjoint_seq {T : finType} (S : eqType) (s : seq S) (t : S -> seq T) : 
  uniq s -> uniq (flatten [seq t x | x <- s]) <->
  ({in s, forall x : S, uniq (t x)} /\
  {in s &, forall (x y : S), x != y -> [disjoint t x & t y]}).
Proof.
elim: s=>//=.
move=>x s IH /andP[] Px /IH []IH2 IH1; split; last first.
- move=>[]P1 P2; rewrite cat_uniq_disjoint.
  move: (P1 x); rewrite inE eqxx/==>->//=.
  rewrite IH1 ?andbT. do ! split=>//. 
  by move=>i Pi; move: (P1 i); rewrite inE Pi orbT=>->.
  by move=>i j Pi Pj nij; move: (P2 i j); rewrite !inE Pi Pj !orbT nij=>->.
  rewrite disjoint_sym; apply/disjoint_flatten_seq=>i Ps; apply/P2.
  1,2: by rewrite inE ?eqxx// Ps orbT.
  by rewrite eq_sym; apply/(notin_in_neq (s := s)).
rewrite cat_uniq_disjoint=>/andP[] Pux /andP[] +/IH2 [] Pi Pij.
rewrite disjoint_sym=>/disjoint_flatten_seq Pj; split.
by move=>i; rewrite inE=>/orP[/eqP->//|/Pi].
move=>i j; rewrite !inE=>/orP[/eqP->/orP[/eqP->|/Pj + _]|+/orP[/eqP-> _|]].
by rewrite eqxx. by rewrite disjoint_sym. apply: Pj. apply: Pij.
Qed.

(* move *)
Lemma flatten_uniq_disjoint {T S: finType} (t : S -> seq T) : 
  uniq (flatten [seq t x | x : S]) = 
    [forall i, uniq (t i)] && [forall i, forall j, (i != j) ==>
      [disjoint t i & t j]].
Proof.
apply/eqb_iff; rewrite flatten_uniq_disjoint_seq ?enum_uniq//; split.
- move=>[] Pi Pij; apply/andP; split.
  apply/forallP=>i; apply/Pi/mem_enum.
  apply/forallP=>i; apply/forallP=>j; apply/implyP; apply/Pij; apply/mem_enum.
move=>/andP[]/forallP Pi/forallP Pij; split.
move=>i _; apply: Pi. 
by move=>i j _ _; move: (Pij i)=>/forallP/(_ j)/implyP.
Qed.

Inductive qreg_expr : qType -> Type :=
  | qreg_cst {T} (x : qreg T) : qreg_expr T
  | qreg_fst_expr {T1 T2} (x : qreg_expr (T1 * T2)) :
      qreg_expr T1
  | qreg_snd_expr {T1 T2} (x : qreg_expr (T1 * T2)) :
      qreg_expr T2
  | qreg_tuplei_expr {n T} (i : expr_ 'I_n) 
      (x : qreg_expr T.[n]) : qreg_expr T
(* to automatically determine the type, *)
(* we only allow constant (meta variable) as indexes *)
  | qreg_ffuni_expr {n} {T : 'I_n -> qType} (i : 'I_n) 
      (x : qreg_expr {qffun T}) : qreg_expr (T i)
  | qreg_pair_expr {T1 T2} (x1 : qreg_expr T1) (x2 : qreg_expr T2) :
    qreg_expr (T1 * T2)
  | qreg_tuple_expr {n T} (x : forall i : 'I_n, qreg_expr T) :
    qreg_expr T.[n]
  | qreg_ffun_expr {n} {T : 'I_n -> qType}
      (x : forall i : 'I_n, qreg_expr (T i)) :
    qreg_expr {qffun T}.

Coercion qreg_cst : qreg >-> qreg_expr.

Fixpoint qsem_of {T : qType} (x : qreg_expr T) (m : cmem) : qreg T :=
  match x in qreg_expr T return qreg T with
  | qreg_cst T x => x
  | qreg_fst_expr _ _ x => (qreg_fst (qsem_of x m))
  | qreg_snd_expr _ _ x => (qreg_snd (qsem_of x m))
  | qreg_tuplei_expr _ _ i x => (qreg_tuplei (esem i m) (qsem_of x m))
  | qreg_ffuni_expr _ _ i x => (qreg_ffuni i (qsem_of x m))
  | qreg_pair_expr _ _ x1 x2 =>
        (@qreg_pair _ _ (qsem_of x1 m) (qsem_of x2 m))
  | qreg_tuple_expr _ _ x =>
        (@qreg_tuple _ _ (fun i => qsem_of (x i) m))
  | qreg_ffun_expr _ _ x =>
        (@qreg_ffun _ _ (fun i => qsem_of (x i) m))
  end. 

(* pack the validity, canonical structure *)
Structure wf_qreg (T : qType) := WF_QReg {
  qreg_base : qreg T;
  qreg_is_valid : valid_qreg qreg_base;
}.
#[reversible] Coercion qreg_base : wf_qreg >-> qreg.
Canonical qreg_wf {T} (q : qreg T) {H : qreg_expose (valid_qreg q)} :=
  WF_QReg H.
Definition clone_wf_qreg {T} e :=
  fun (opL : wf_qreg T) & (@phant_id (qreg T) (qreg T) opL e) =>
  fun ewf (opL' := @WF_QReg T e ewf)
    & phant_id opL' opL => opL'.

Structure wf_qreg_expr (T : qType) := WF_QReg_Expr {
  qreg_expr_base : qreg_expr T;
  qreg_expr_is_valid : forall m, valid_qreg (qsem_of qreg_expr_base m);
}.
#[reversible] Coercion qreg_expr_base : wf_qreg_expr >-> qreg_expr.
Canonical qreg_expr_wf {T} (q : qreg_expr T) 
  {H : qreg_expose (forall m, valid_qreg (qsem_of q m))} :=
  WF_QReg_Expr H.
Definition clone_wf_qreg_expr {T} e :=
  fun (opL : wf_qreg_expr T) & (@phant_id (qreg_expr T) (qreg_expr T) opL e)
    => fun ewf (opL' := @WF_QReg_Expr T e ewf) & phant_id opL' opL => opL'.

End qreg.

Add Parametric Relation T : (qreg T) (@eq_qreg T)
  reflexivity proved by (@eq_qreg_refl T)
  symmetry proved by (@eq_qreg_sym T)
  transitivity proved by (@eq_qreg_trans T)
  as eq_qreg_rel.

(* Add Parametric Relation : {T : qType & qreg T} (@eq_qregT)
  reflexivity proved by (@eq_qregT_refl)
  symmetry proved by (@eq_qregT_sym)
  transitivity proved by (@eq_qregT_trans)
  as eq_qregT_rel. *)

Add Parametric Morphism {T1 T2} : (@qreg_fst T1 T2)
  with signature (@eq_qreg (QPair T1 T2)) ==>
    (@eq_qreg T1) as eq_qreg_qreg_fst.
Proof.
move=>x y; rewrite/eq_qreg !qr2seq_pairE.
move=>/(f_equal (take (qtype_size T1)));
rewrite !take_size_cat ?size_qr2seq//.
Qed.

Add Parametric Morphism {T1 T2} : (@qreg_snd T1 T2)
  with signature (@eq_qreg (QPair T1 T2)) ==>
    (@eq_qreg T2) as eq_qreg_qreg_snd.
Proof.
move=>x y; rewrite/eq_qreg !qr2seq_pairE.
move=>/(f_equal (drop (qtype_size T1)));
rewrite !drop_size_cat ?size_qr2seq//.
Qed.

Add Parametric Morphism {n T} : (@qreg_tuplei n T)
  with signature (@eq 'I_n) ==> (@eq_qreg (QArray n T)) ==> 
    (@eq_qreg T) as eq_qreg_qreg_tuplei.
Proof.
rewrite/eq_qreg=>i x y.
elim: n x y i=>[x y i|n IH x y i]; first by case: i.
rewrite !qr2seq_tupleE [X in flatten (map _ X)]enum_ordSl  
  [X in _ = flatten (map _ X)]enum_ordSl  !map_cons/=.
case: (unliftP ord0 i)=>/=[j ->/(f_equal (drop (qtype_size T)))|->]; 
  last by move=>/(f_equal (take (qtype_size T)));
  rewrite !take_size_cat ?size_qr2seq.
rewrite !drop_size_cat ?size_qr2seq// -map_comp - [in X in _ = X]map_comp => P1.
pose x1 := qreg_tuple (fun k : 'I_n => qreg_tuplei (nlift ord0 k) x).
pose y1 := qreg_tuple (fun k : 'I_n => qreg_tuplei (nlift ord0 k) y).
transitivity (qr2seq (qreg_tuplei j x1));
last transitivity (qr2seq (qreg_tuplei j y1)).
1,3: by rewrite/qr2seq/qi2seq/=/index_tuplei/= orapp_id cast_ord_id.
apply: IH; rewrite /x1 /y1 !qr2seq_tupleE.
under [X in flatten X]eq_map do rewrite eq_qreg_tuplei.
by under [X in _ = flatten X]eq_map do rewrite eq_qreg_tuplei.
Qed.

Add Parametric Morphism {n} {T : 'I_n -> qType} i : (@qreg_ffuni n T i)
  with signature (@eq_qreg (QDFFun T)) ==>
    (@eq_qreg (T i)) as eq_qreg_qreg_ffuni.
Proof.
move=>x y; rewrite /eq_qreg.
elim: n T x y i=>[T x y i|n IH T x y i]; first by case: i.
rewrite !qr2seq_ffunE [X in flatten (map _ X)]enum_ordSl  
  [X in _ = flatten (map _ X)]enum_ordSl  !map_cons/=.
case: (unliftP ord0 i)=>/=[j ->/(f_equal (drop (qtype_size (T ord0))))|->];
  last by move=>/(f_equal (take (qtype_size (T ord0))));
  rewrite !take_size_cat ?size_qr2seq.
rewrite !drop_size_cat ?size_qr2seq//
  -map_comp - [in X in _ = X]map_comp => P1.
pose x1 := qreg_ffun (fun k : 'I_n => qreg_ffuni (nlift ord0 k) x).
pose y1 := qreg_ffun (fun k : 'I_n => qreg_ffuni (nlift ord0 k) y).
transitivity (qr2seq (qreg_ffuni j x1));
last transitivity (qr2seq (qreg_ffuni j y1)).
1,3: by rewrite/qr2seq/qi2seq/=/index_ffuni/= orapp_id cast_ord_id.
apply: IH; rewrite /x1 /y1 !qr2seq_ffunE.
under [X in flatten X]eq_map do rewrite eq_qreg_ffuni.
by under [X in _ = flatten X]eq_map do rewrite eq_qreg_ffuni.
Qed.

Add Parametric Morphism {T1 T2} : (@qreg_pair T1 T2)
  with signature (@eq_qreg T1) ==> (@eq_qreg T2) ==>
    (@eq_qreg (QPair T1 T2)) as eq_qreg_qreg_pair.
Proof. by move=>??; rewrite/eq_qreg/=/qr2seq/qi2seq/==>->??->. Qed.

Add Parametric Morphism {T} : (@valid_qreg T)
  with signature (@eq_qreg T) ==> (@eq bool) as eq_qreg_valid.
Proof. by move=>??; rewrite !valid_qregE/eq_qreg=>->. Qed.

Add Parametric Morphism {T1 T2} : (@disjoint_qreg T1 T2)
  with signature (@eq_qreg T1) ==> (@eq_qreg T2) ==>
    (@eq bool) as eq_qreg_disjoint.
Proof. by rewrite /eq_qreg=>?? H1 ?? H2; rewrite !disjoint_qregE H1 H2. Qed.

Add Parametric Morphism {T} : (@fset_qreg T)
  with signature (@eq_qreg T) ==> (@eq _) as eq_qreg_fset.
Proof.
move=>x y; rewrite /eq_qreg=>P.
by apply/finmap.fsetP=>i/=; rewrite !fset_qregE P.
Qed.

Infix "=r" := eq_qreg (at level 70) : reg_scope.
(* Infix "=rt" := eq_qregT (at level 70) : reg_scope. *)

(* Notation qregT := {x : qType & qreg x}. *)
Notation "''QReg[' T ]" := (@wf_qreg T) : reg_scope.
Notation "[ 'wf_qreg' 'of' qe ]" := (@clone_wf_qreg _ qe _ id _ id)
  (at level 0, format "[ 'wf_qreg'  'of'  qe  ]") : form_scope.

Notation "''QRegExpr[' T ]" := (@wf_qreg_expr T) : reg_scope.
Notation "[ 'wf_qreg_expr' 'of' qe ]" := (@clone_wf_qreg_expr _ qe _ id _ id)
  (at level 0, format "[ 'wf_qreg_expr'  'of'  qe  ]") : form_scope.

Notation "<{ e }>" := e (at level 0, e custom reg at level 99) : reg_scope.
Notation "( x )" := x (in custom reg at level 0) : reg_scope.
Notation "x" := x (in custom reg at level 0, x constr at level 0) : reg_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom reg at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : reg_scope.
Notation "''' x" := (qreg_prime x)
  (in custom reg at level 40, only parsing, no associativity).
Notation "x '.1'" := (qreg_fst x)
  (in custom reg at level 50, format "x '.1'", left associativity).
Notation "x '.2'" := (qreg_snd x)
  (in custom reg at level 50, format "x '.2'", left associativity).
Notation "x '.[' i ]" := (qreg_tuplei i x)
  (in custom reg at level 50, i constr,format "x .[ i ]", left associativity).
Notation "x '.-[' i ]" := (qreg_ffuni i x)
  (in custom reg at level 50, i constr, format "x '.-[' i ]", left associativity).
Notation "( x , y , .. , z )" := (qreg_pair .. (qreg_pair x y) .. z)
  (in custom reg at level 0, format "( x ,  y ,  .. ,  z )", left associativity).
Notation "'ffun' x : aT => E" := (qreg_ffun (fun x : (aT)%FORM => E))
  (in custom reg at level 0, x name, aT constr, format "'ffun'  x  :  aT  =>  E").
Notation "'ffun' x => E" := (qreg_ffun (fun x => E))
  (in custom reg at level 0, x name, format "'ffun'  x  =>  E").
Notation "'ffun' => E" := (qreg_ffun (fun _ => E))
  (in custom reg at level 0, format "'ffun'  =>  E").
Notation "'ffun:' x" := (qreg_ffun x)
  (in custom reg at level 0, x constr, only parsing).
Notation "'tuple' x : aT => E" := (qreg_tuple (fun x : (aT)%FORM => E))
  (in custom reg at level 0, x name, aT constr, format "'tuple'  x  :  aT  =>  E").
Notation "'tuple' x => E" := (qreg_tuple (fun x => E))
  (in custom reg at level 0, x name, format "'tuple'  x  =>  E").
Notation "'tuple' => E" := (qreg_tuple (fun _ => E))
  (in custom reg at level 0, format "'tuple'  =>  E").
Notation "'tuple:' x" := (qreg_tuple x)
  (in custom reg at level 0, x constr, only parsing).
Notation "( 'ffun' x : aT => E )" := (qreg_ffun (fun x : (aT)%FORM => E))
  (in custom reg at level 0, x name, aT constr, only parsing).
Notation "( 'ffun' x => E )" := (qreg_ffun (fun x => E))
  (in custom reg at level 0, x name, only parsing).
Notation "( 'ffun' => E )" := (qreg_ffun (fun _ => E))
  (in custom reg at level 0, only parsing).
Notation "( 'ffun:' x )" := (qreg_ffun x)
  (in custom reg at level 0, x constr, only parsing).
Notation "( 'tuple' x : aT => E )" := (qreg_tuple (fun x : (aT)%FORM => E))
  (in custom reg at level 0, x name, aT constr, only parsing).
Notation "( 'tuple' x => E )" := (qreg_tuple (fun x => E))
  (in custom reg at level 0, x name, only parsing).
Notation "( 'tuple' => E )" := (qreg_tuple (fun _ => E))
  (in custom reg at level 0, only parsing).
Notation "( 'tuple:' x )" := (qreg_tuple x)
  (in custom reg at level 0, x constr, only parsing).
Notation "x : T" := (x : qreg (T)%QT)
  (in custom reg at level 99, T constr, only parsing).

Notation "<{{ e }}>" := e
  (at level 0, e custom reg_expr at level 99) : reg_scope.
Notation "( x )" := x
  (in custom reg_expr at level 0) : reg_scope.
Notation "x" := x
  (in custom reg_expr at level 0, x constr at level 0) : reg_scope.
Notation "f x .. y" := (.. (f x) .. y)
  (in custom reg_expr at level 0, only parsing,
   f constr at level 0, x constr at level 9, y constr at level 9) : reg_scope.
Notation "''' x" := (qreg_cst x)
  (in custom reg_expr at level 40, x custom reg, only parsing, no associativity).
Notation "x '.1'" := (qreg_fst_expr x)
  (in custom reg_expr at level 50, format "x '.1'", left associativity).
Notation "x '.2'" := (qreg_snd_expr x)
  (in custom reg_expr at level 50, format "x '.2'", left associativity).
Notation "x '.[' i ]" := (qreg_tuplei_expr (i)%X x)
  (in custom reg_expr at level 50, i constr, format "x .[ i ]", left associativity).
Notation "x '.-[' i ]" := (qreg_ffuni_expr (i)%X x)
  (in custom reg_expr at level 50, i constr, format "x '.-[' i ]", left associativity).
Notation "( x , y , .. , z )" := (qreg_pair_expr .. (qreg_pair_expr x y) .. z)
  (in custom reg_expr at level 0, format "( x ,  y ,  .. ,  z )", left associativity).
Notation "'ffun' x : aT => E" := (qreg_ffun_expr (fun x : (aT)%FORM => E))
  (in custom reg_expr at level 0, x name, aT constr, format "'ffun'  x  :  aT  =>  E").
Notation "'ffun' x => E" := (qreg_ffun_expr (fun x => E))
  (in custom reg_expr at level 0, x name, format "'ffun'  x  =>  E").
Notation "'ffun' => E" := (qreg_ffun_expr (fun _ => E))
  (in custom reg_expr at level 0, format "'ffun'  =>  E").
Notation "'ffun:' x" := (qreg_ffun_expr x)
  (in custom reg_expr at level 0, x constr, only parsing).
Notation "'tuple' x : aT => E" := (qreg_tuple_expr (fun x : (aT)%FORM => E))
  (in custom reg_expr at level 0, x name, aT constr, format "'tuple'  x  :  aT  =>  E").
Notation "'tuple' x => E" := (qreg_tuple_expr (fun x => E))
  (in custom reg_expr at level 0, x name, format "'tuple'  x  =>  E").
Notation "'tuple' => E" := (qreg_tuple_expr (fun _ => E))
  (in custom reg_expr at level 0, format "'tuple'  =>  E").
Notation "'tuple:' x" := (qreg_tuple_expr x)
  (in custom reg_expr at level 0, x constr, only parsing).
Notation "( 'ffun' x : aT => E )" := (qreg_ffun_expr (fun x : (aT)%FORM => E))
  (in custom reg_expr at level 0, x name, aT constr, only parsing).
Notation "( 'ffun' x => E )" := (qreg_ffun_expr (fun x => E))
  (in custom reg_expr at level 0, x name, only parsing).
Notation "( 'ffun' => E )" := (qreg_ffun_expr (fun _ => E))
  (in custom reg_expr at level 0, only parsing).
Notation "( 'ffun:' x )" := (qreg_ffun_expr x)
  (in custom reg_expr at level 0, x constr, only parsing).
Notation "( 'tuple' x : aT => E )" := (qreg_tuple_expr (fun x : (aT)%FORM => E))
  (in custom reg_expr at level 0, x name, aT constr, only parsing).
Notation "( 'tuple' x => E )" := (qreg_tuple_expr (fun x => E))
  (in custom reg_expr at level 0, x name, only parsing).
Notation "( 'tuple' => E )" := (qreg_tuple_expr (fun _ => E))
  (in custom reg_expr at level 0, only parsing).
Notation "( 'tuple:' x )" := (qreg_tuple_expr x)
  (in custom reg_expr at level 0, x constr, only parsing).
Notation "x : T" := (x : qreg_expr (T)%QT)
  (in custom reg_expr at level 99, T constr, only parsing).
Local Open Scope reg_scope.

Lemma qtype_of_basic_index (i : basic_index) : 
  { T | qtype_of_index i = Some T }.
Proof.
case: i=>x s/=; rewrite /is_basic_index/=.
by case: (qtype_of_index_rec s (qreg.G.[? x])%fmap)=>// T; exists T.
Qed.

Lemma fset_qreg_pair T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  (<{(x1,x2)}> = x1 `|` x2 :> {fset _})%fset.
Proof.
by apply/fsetP=>i; rewrite inE !fset_qregE qr2seq_pairE !eq_qregE mem_cat.
Qed.

Lemma fset_qreg_pairV T1 T2 (x : qreg (T1 * T2)) :
  (x = <{x.1}> `|` <{x.2}> :> {fset _})%fset.
Proof. by rewrite -fset_qreg_pair eq_qreg_pair. Qed.

Lemma fset_qreg_tuple n T (fx : 'I_n -> qreg T) :
  (<{ tuple: fx }> = \bigcup_i (fx i) :> {fset _})%fset.
Proof.
apply/fsetP=>i; rewrite !fset_qregE qr2seq_tupleE; apply/eqb_iff; split.
  move=>/flatten_mapP/=[j P1]; rewrite eq_qregE=>P2.
  apply/bigfcupP=>/=; exists j; first by rewrite mem_index_enum.
  by rewrite fset_qregE.
move=>/bigfcupP[j _]; rewrite fset_qregE=>Pi.
apply/flatten_mapP; exists j; first by rewrite mem_enum.
by rewrite eq_qregE.
Qed.

Lemma fset_qreg_tupleV n T (x : qreg T.[n]) :
  (x = \bigcup_i <{x.[i]}> :> {fset _})%fset.
Proof. by rewrite -fset_qreg_tuple eq_qreg_tuple. Qed.

Lemma fset_qreg_ffun n (fT : 'I_n -> qType) (fx : forall i, qreg (fT i)) :
  (<{ ffun: fx }> = \bigcup_i (fx i) :> {fset _})%fset.
Proof.
apply/fsetP=>i; rewrite !fset_qregE qr2seq_ffunE; apply/eqb_iff; split.
  move=>/flatten_mapP/=[j P1]; rewrite eq_qregE=>P2.
  apply/bigfcupP=>/=; exists j; first by rewrite mem_index_enum.
  by rewrite fset_qregE.
move=>/bigfcupP[j _]; rewrite fset_qregE=>Pi.
apply/flatten_mapP; exists j; first by rewrite mem_enum.
by rewrite eq_qregE.
Qed.

Lemma fset_qreg_ffunV n (fT : 'I_n -> qType) (x : qreg {qffun fT}) :
  (x = \bigcup_i <{x.-[i]}> :> {fset _})%fset.
Proof. by rewrite -fset_qreg_ffun eq_qreg_ffun. Qed.

Definition basic_type (T : qType) :=
  match T with
  | QUnit | QBool | QOrd _ | QOption _ | QSum _ _ => true
  | _ => false
  end.

Lemma basic_type_prime (T : qType) (x : qreg T) :
  basic_type T -> 
    { a : qvar * seq qnat | index_of_qreg x = prime_index a.1 a.2}.
Proof.
move: (index_typeK x); case: (index_of_qreg x)=>//.
by move=>q l _ _; exists (q,l).
move=>q1 q2 /=; case: (qtype_of_index _)=>// T1;
by case: (qtype_of_index _)=>// T2 Pv; inversion Pv.
all: by move=>n T1 f /=; case: [forall _, _] =>// Pv; inversion Pv.
Qed.

Lemma basic_index_type (T : qType) (x : qreg T) (H : basic_type T) :
  is_basic_index (projT1 (basic_type_prime x H)).1 
    (projT1 (basic_type_prime x H)).2.
Proof.
move: (projT2 (basic_type_prime x H))=>/(f_equal qtype_of_index).
by rewrite /is_basic_index=><-; rewrite index_typeK; move: H.
Qed.

Definition qr2seq_basic_type (T : qType) (x : qreg T) (H : basic_type T) :
  qr2seq x = [:: Basic_Index (basic_index_type x H)].
Proof.
rewrite /qr2seq /qi2seq /qi2seq_rec.
move: (projT2 (basic_type_prime x H))=>{1}->.
move: (projT2 (basic_type_prime x H))=>/(f_equal qtype_of_index)<-.
move: (index_typeK x)=>->.
rewrite /ssqnat; move: x H; case: T=>//; intros;
rewrite /map /pair_to_basic_index /pmap/=/orapp/oapp;
by move: (basic_index_type x H); case: eqP=>// P1 P2; rewrite (eq_irrelevance P1 P2).
Qed.

Lemma fset_basic_type (T : qType) (x : qreg T) (H : basic_type T) :
  x = [fset Basic_Index (basic_index_type x H)]%fset :> {fset _}.
Proof. by apply/fsetP=>i; rewrite fset_qregE inE qr2seq_basic_type inE. Qed.

(* TODO : add automation for subset relation *)

(*****************************************************************************)
(* used to compute the disjointness of variables                             *)
(*****************************************************************************)

(* definition a stronger but computable way to prove the validity of qreg *)
Module QRegAuto.

Section Theory.

Definition nat_of_qnat (i : qnat) :=
  match i with
  | qnat_fst=> 0
  | qnat_snd => 1
  | qnat_tuplei _ i => i
  | qnat_ffuni _ i => i
  end.
(* Coercion nat_of_qnat : qnat >-> nat. *)

Fixpoint index_prime2_disjoint (s1 s2 : seq qnat) : bool :=
    match s1, s2 with
    | [::], _ => false
    | _, [::] => false
    | h1 :: t1, h2 :: t2 => 
        (nat_of_qnat h1 != nat_of_qnat h2) || index_prime2_disjoint t1 t2
    end.

(* move *)
Lemma seq_ind20 {S1 S2} (P : seq S1 -> seq S2 -> Prop) :
  (forall s, P s [::]) -> (forall t, P [::] t) ->
    (forall x y s t, P s t -> P (x :: s) (y :: t)) ->
      forall s t, P s t.
Proof. by move=>H1 H2 H3; elim=>// x s H4; elim=>// y t _; apply/H3/H4. Qed.

Lemma index_prime2_disjointC (s1 s2 : seq qnat) : 
  index_prime2_disjoint s1 s2 = index_prime2_disjoint s2 s1.
Proof.
move: s1 s2; apply seq_ind20; [by case ..|].
by move=>x y s t/= ->; rewrite eq_sym.
Qed.

Fixpoint eval_index_rec (x : qreg_index) (s : seq qnat) :=
  match s with
  | [::] => x
  | qnat_fst :: t => eval_index_rec (index_fst x) t
  | qnat_snd :: t => eval_index_rec (index_snd x) t
  | qnat_tuplei _ i :: t => eval_index_rec (index_tuplei x i) t
  | qnat_ffuni _ i :: t => eval_index_rec (index_ffuni x i) t
  end.
Definition eval_index := nosimpl eval_index_rec.

Lemma eval_indexE1 T1 T2 (x : qreg (T1 * T2)) :
  qreg_fst x = eval_index x [:: qnat_fst] :> qreg_index.
Proof. by []. Qed.

Lemma eval_indexE2 T1 T2 (x : qreg (T1 * T2)) :
  qreg_snd x = eval_index x [:: qnat_snd] :> qreg_index.
Proof. by []. Qed.

Lemma eval_indexEt n T (x : qreg T.[n]) (i : 'I_n) :
  qreg_tuplei i x = eval_index x [:: qnat_tuplei i] :> qreg_index.
Proof. by []. Qed.

Lemma eval_indexEf n (T : 'I_n -> qType) (x : qreg {qffun T}) (i : 'I_n) :
  qreg_ffuni i x = eval_index x [:: qnat_ffuni i] :> qreg_index.
Proof. by []. Qed.

Lemma eval_indexE_comp x s1 s2 : 
  eval_index (eval_index x [:: s1]) s2 = eval_index x (s1 :: s2).
Proof. by case: s1. Qed.

Definition eval_indexE := 
  (eval_indexE1, eval_indexE2, eval_indexEt, eval_indexEf, eval_indexE_comp).

Lemma disjointNilX [T : finType] (A : {pred T}) : [disjoint [::] & A].
Proof. by rewrite eq_disjoint0. Qed.

Ltac luf :=
  repeat rewrite/eval_index/index_fst/index_snd/index_tuplei/index_ffuni
  /disjoint_qregI/disjoint_qregI_rec/valid_qregI/valid_qregI_rec
  /disjoint_qreg/disjoint_qreg_rec/valid_qreg/valid_qreg_rec
  /qr2seq/qi2seq/=.

Ltac lnil := try (intros; match goal with 
  | [|- is_true [disjoint [::] & _]] => apply disjointNilX 
  | [|- is_true [disjoint _ & [::]]] =>
    rewrite disjoint_sym; apply disjointNilX 
  end).

Lemma eval_index_disjoint1 s1 s2 l1 : disjoint_qregI s1 s2 ->
  disjoint_qregI (eval_index s1 [:: l1]) s2.
Proof.
rewrite/disjoint_qregI/disjoint_qregI_rec.
case: s1=>//=; first by case: l1=>//.
- case: l1=>//=; luf.
  - move=>v s; rewrite /qi2seq/= qtype_of_index_rec_rcons.
    case E1: (qtype_of_index_rec _) =>[T|//]; case: T E1=>//=; lnil.
    by intros; move: H; rewrite map_cat pmap_cat disjoint_cat=>/andP[].
  - move=>v s; rewrite /qi2seq/= qtype_of_index_rec_rcons.
    case E1: (qtype_of_index_rec _) =>[T|//]; case: T E1=>//=; lnil.
    by intros; move: H; rewrite map_cat pmap_cat disjoint_cat=>/andP[].
  - move=>n i v s; rewrite /qi2seq/= qtype_of_index_rec_rcons /orapp.
    case E1: (qtype_of_index_rec _) =>[T|//]; case: T E1=>//=; lnil.
    intros; case: eqP=>[Pv| _]; lnil; case: _ / Pv E1 H=> P1.
    by rewrite map_flatten pmap_flatten -2!map_comp disjoint_flatten
      =>/forallP/(_ i).
  - move=>n i v s; rewrite /qi2seq/= qtype_of_index_rec_rcons /orapp.
    case E1: (qtype_of_index_rec _) =>[T|//]; case: T E1=>//=; lnil.
    intros; case: eqP=>[Pv| _]; lnil; case: _ / Pv fT E1 H=> fT P1;
      rewrite cast_ord_id.
    by rewrite map_flatten pmap_flatten -2!map_comp disjoint_flatten
      =>/forallP/(_ i).
- move=>q1 q2; rewrite /qi2seq/=; 
  case: l1=>//=[||???|???]; luf; lnil.
  1,2: by rewrite disjoint_cat=>/andP[].
- move=>n T q; rewrite /qi2seq/=;
  case: l1=>//=[||m i IH|???]; luf; lnil.
  rewrite /orapp; case: eqP=>//=[Pv|?]; lnil;
  by case: n / Pv q IH=>q; rewrite cast_ord_id disjoint_flatten=>/forallP/(_ i).
- move=>n T q; rewrite /qi2seq/=; case: l1=>//=[||???|m i IH]; luf; lnil.
  rewrite /orapp; case: eqP=>//=[Pv|?]; lnil; case: n / Pv T q IH=>T q; 
  by rewrite cast_ord_id disjoint_flatten=>/forallP/(_ i).
Qed.

Lemma disjoint_qregC T1 T2 (x1 : qreg T1) (x2 : qreg T2) : 
  disjoint_qreg x1 x2 = disjoint_qreg x2 x1.
Proof. by luf; rewrite disjoint_sym. Qed.

Lemma disjoint_qregIC x y : disjoint_qregI x y = disjoint_qregI y x.
Proof. by luf; rewrite disjoint_sym. Qed.

Lemma eval_index_disjoint s1 s2 l1 l2 : disjoint_qregI s1 s2 ->
  disjoint_qregI (eval_index s1 l1) (eval_index s2 l2).
Proof.
elim: l1 l2 s1 s2=>[|a1 l1 IH1 l2 s1 s2 Ps].
by elim=>//a1 l1 IH1 s1 s2 ds; rewrite -eval_indexE_comp; apply: IH1;
  rewrite disjoint_qregIC; apply/eval_index_disjoint1; rewrite disjoint_qregIC.
by rewrite -eval_indexE_comp; apply/IH1/eval_index_disjoint1.
Qed.

Lemma eval_index_recF s : eval_index_rec fault_index s = fault_index.
Proof. by elim: s=>//= a l P; case: a=>/=; luf. Qed.

Lemma eval_index_rec_cat v s1 s2 :
  eval_index_rec (prime_index v s1) s2 = prime_index v (s1 ++ s2).
Proof.
elim: s2 s1=>[s1|[||n i|n i] s1 + s2]/=; first by rewrite cats0.
all: by move=>->; rewrite cat_rcons.
Qed.

Lemma valid_qregIP_prime v s :
  valid_qregI (prime_index v s).
Proof.
rewrite/valid_qregI/valid_qregI_rec/qi2seq/=.
case: (qtype_of_index_rec _ _)=>// T.
apply/(pmap_uniq basic_indexKV).
rewrite map_inj_uniq; last by apply uniq_ssqnat.
by move=>i j Pv; inversion Pv.
Qed.

Lemma eval_index_prime_cat x s1 s2 : 
  eval_index (prime_index x s1) s2 = prime_index x (s1++s2).
Proof.
elim: s2 x s1 =>[x s1|a s2 + x s1/=]; first by rewrite /= cats0.
by luf; rewrite -cat_rcons; case: a=>[||n i|n i] ->.
Qed.

Lemma valid_qregI_eval x s : 
  valid_qregI x -> valid_qregI (eval_index x s).
Proof.
elim: s x=>//a s IH x Px/=.
case: a=>[||n i|n i]; apply/IH; clear IH s; move: Px; luf.
- case: x=>//=[a s|??]; last by rewrite cat_uniq_disjoint=>/and3P[].
  rewrite qtype_of_index_rec_rcons; case E1: (qtype_of_index_rec _ _)=>[T|]//.
  by case: T E1=>//=???; rewrite map_cat pmap_cat cat_uniq_disjoint=>/and3P[].
- case: x=>//=[a s|??]; last by rewrite cat_uniq_disjoint=>/and3P[].
  rewrite qtype_of_index_rec_rcons; case E1: (qtype_of_index_rec _ _)=>[T|]//.
  by case: T E1=>//=???; rewrite map_cat pmap_cat cat_uniq_disjoint=>/and3P[].
- case: x=>//=[a s|???]; rewrite ?qtype_of_index_rec_rcons/orapp.
  - case E1: (qtype_of_index_rec _ _)=>[T|]//.
    case: T E1=>//=m T _; case: eqP=>// Pv; case: m / Pv.
    by rewrite map_flatten pmap_flatten -2!map_comp 
      flatten_uniq_disjoint=>/andP[]/forallP/(_ i).
  - by case: eqP=>// P;
    rewrite flatten_uniq_disjoint=>/andP[]/forallP/(_ (cast_ord P i)).
- case: x=>//=[a s|???]; rewrite ?qtype_of_index_rec_rcons/orapp.
  - case E1: (qtype_of_index_rec _ _)=>[T|]//.
    case: T E1=>//=m T _; case: eqP=>// Pv; case: m / Pv T => T.
    by rewrite cast_ord_id map_flatten pmap_flatten -2!map_comp 
      flatten_uniq_disjoint=>/andP[]/forallP/(_ i).
  - by case: eqP=>// P;
    rewrite flatten_uniq_disjoint=>/andP[]/forallP/(_ (cast_ord P i)).
Qed.

Lemma valid_qregIP_prime_eval v s1 s2 :
  valid_qregI (eval_index (prime_index v s1) s2).
Proof. apply/valid_qregI_eval/valid_qregIP_prime. Qed.

Lemma disjoint_qregIP_abs x s1 s2 : valid_qregI x ->
  index_prime2_disjoint s1 s2 ->
    disjoint_qregI (eval_index x s1) (eval_index x s2).
Proof.
move: s1 s2 x; apply: seq_ind20=>//[???|q1 q2 s1 s2 IH/=];
  first by rewrite index_prime2_disjointC.
case.
- case: q1=>/=; luf; rewrite ?eval_index_recF/=; lnil.
-  move=>v s; luf; case: q1=>[||n i|n i];
  rewrite eval_index_rec_cat cat_rcons/= qtype_of_index_rec_cat;
  case E: (qtype_of_index_rec _ _)=>[T/=|]; 
  rewrite ?qtype_of_index_recN; lnil;
  case: T E; lnil.
  - move=>T1 T2 PT; case: q2=>[||m j|m j]; 
    rewrite eval_index_rec_cat cat_rcons/= qtype_of_index_rec_cat PT/=; lnil.
      rewrite map_cat pmap_cat cat_uniq_disjoint=>/and3P[]P1 _ P2 P3.
      rewrite -!cat_rcons.
      move: (valid_qregIP_prime v (rcons s qnat_fst))=>/IH/(_ P3); luf; 
      by rewrite !eval_index_rec_cat !cat_rcons/= !qtype_of_index_rec_cat PT/=.
    rewrite map_cat pmap_cat cat_uniq_disjoint=>/and3P[] _ P _ _.
    move: (@eval_index_disjoint (prime_index v (rcons s qnat_fst)) 
      (prime_index v (rcons s qnat_snd)) s1 s2).
    by luf; rewrite !eval_index_rec_cat !cat_rcons/= 
      !qtype_of_index_rec_cat PT/= !qtype_of_index_rec_rcons PT=>/(_ P).
  - move=>T1 T2 PT; case: q2=>[||m j|m j]; 
    rewrite eval_index_rec_cat cat_rcons/= qtype_of_index_rec_cat PT/=; lnil.
      rewrite map_cat pmap_cat cat_uniq_disjoint=>/and3P[] _ P _ _.
      move: (@eval_index_disjoint (prime_index v (rcons s qnat_snd)) 
        (prime_index v (rcons s qnat_fst)) s1 s2).
      by luf; rewrite disjoint_sym !eval_index_rec_cat !cat_rcons/= 
        !qtype_of_index_rec_cat PT/= !qtype_of_index_rec_rcons PT=>/(_ P).
    rewrite map_cat pmap_cat cat_uniq_disjoint=>/and3P[]P1 _ P2 P3.
    rewrite -!cat_rcons.
    move: (valid_qregIP_prime v (rcons s qnat_snd))=>/IH/(_ P3); luf; 
    by rewrite !eval_index_rec_cat !cat_rcons/= !qtype_of_index_rec_cat PT/=.
  - move=>m T; rewrite /orapp; case: eqP; lnil=>Pv; case: m / Pv => PT.
    case: q2=>[||m j|m j]; rewrite eval_index_rec_cat cat_rcons/=
      qtype_of_index_rec_cat PT/=/orapp; lnil.
    case: eqP; lnil=>/esym Pv; case: m / Pv j=>j;
    case: eqP=>[/ord_inj ->/=|/eqP/= nij + _].
      rewrite map_flatten pmap_flatten -2!map_comp flatten_uniq_disjoint
        =>/andP[]/forallP/(_ j) Pu _ P1.
      move: (valid_qregIP_prime v (rcons s (qnat_tuplei j)))=>/IH/(_ P1); luf;
      by rewrite !eval_index_rec_cat !cat_rcons/=
        !qtype_of_index_rec_cat PT/= !orapp_id.
    rewrite map_flatten pmap_flatten -2!map_comp flatten_uniq_disjoint
      =>/andP[] _ /forallP/(_ i)/forallP/(_ j)/implyP/(_ nij)/= P.
    move: (@eval_index_disjoint (prime_index v (rcons s (qnat_tuplei i)))
      (prime_index v (rcons s (qnat_tuplei j))) s1 s2).
    by luf; rewrite !eval_index_rec_cat !cat_rcons/= !qtype_of_index_rec_cat
      PT/= !qtype_of_index_rec_rcons PT !orapp_id=>/(_ P).
  - move=>m T; rewrite /orapp; case: eqP; lnil=>Pv; case: m / Pv T => T PT.
    case: q2=>[||m j|m j]; rewrite eval_index_rec_cat cat_rcons/=
      qtype_of_index_rec_cat PT/=/orapp; lnil.
    case: eqP; lnil=>Pv; move: Pv {+}Pv=>/esym Pv;
    case: m / Pv j=>j ?; rewrite cast_ord_id.
    case: eqP=>[/ord_inj ->/=|/eqP/= nij + _].
      rewrite map_flatten pmap_flatten -2!map_comp flatten_uniq_disjoint
        =>/andP[]/forallP/(_ j) Pu _ P1.
      move: (valid_qregIP_prime v (rcons s (qnat_ffuni j)))=>/IH/(_ P1); luf; 
      by rewrite !eval_index_rec_cat !cat_rcons/=
        !qtype_of_index_rec_cat PT/= !orapp_id !cast_ord_id.
    rewrite map_flatten pmap_flatten -2!map_comp flatten_uniq_disjoint
      =>/andP[] _ /forallP/(_ i)/forallP/(_ j)/implyP/(_ nij)/= P.
    move: (@eval_index_disjoint (prime_index v (rcons s (qnat_ffuni i)))
      (prime_index v (rcons s (qnat_ffuni j))) s1 s2).
    by luf; rewrite !eval_index_rec_cat !cat_rcons/= !qtype_of_index_rec_cat
      PT/= !qtype_of_index_rec_rcons PT !orapp_id !cast_ord_id=>/(_ P).
- move=>i1 i2 Pi; case: q1; case: q2; luf.
  3,4,7-16: rewrite ?eval_index_recF/= 1?[[disjoint _ & [::]]]disjoint_sym;
    intros; apply disjointNilX.
  1,4: apply: IH.
  3,4: move=> _; apply/eval_index_disjoint;
    rewrite ?[_ _ i1]disjoint_qregIC.
  1-4: by move: Pi; luf; rewrite cat_uniq_disjoint=>/and3P[].
- move=>n T q Hi; case: q1=>[||m i|m i]; luf; rewrite /orapp.
    3: case: eqP.
    1-2,4-5: rewrite eval_index_recF/=; intros; apply disjointNilX.
    move=>P; move: P {+}P=>/esym P; case: m / P i=>i P;
    rewrite cast_ord_id; clear P.
    case: q2=>[||m j|m j]; luf.
    3: case: eqP.
    1-2,4-5: rewrite eval_index_recF /= disjoint_sym; 
      intros; apply disjointNilX.
  move=>P; move: P {+}P =>/esym P; case: m / P j=>j P;
  rewrite cast_ord_id; clear P.
  case: eqP=>[/ord_inj ->/=|/eqP];
  [apply /IH | move=> Pi _; apply /eval_index_disjoint];
  move: Hi; luf; rewrite flatten_uniq_disjoint=>/andP[]/forallP/(_ j)//.
  by move=> _ /forallP/(_ i)/forallP/(_ j)/implyP/(_ Pi).
- move=>n T q Hi; case: q1=>[||m i|m i]; luf; rewrite /orapp.
    4: case: eqP.
    1-3,5: rewrite eval_index_recF/=; intros; apply disjointNilX.
    move=>P; move: P {+}P=>/esym P; case: m / P i=>i P;
    rewrite cast_ord_id; clear P.
    case: q2=>[||m j|m j]; luf.
    4: case: eqP.
    1-3,5: rewrite eval_index_recF/= disjoint_sym; intros; apply disjointNilX.
  move=>P; move: P {+}P=>/esym P; case: m / P j=>j P;
  rewrite cast_ord_id; clear P.
  case: eqP=>[/ord_inj ->/=|/eqP];
  [apply /IH | move=> Pi _; apply /eval_index_disjoint];
  move: Hi; luf; rewrite flatten_uniq_disjoint=>/andP[]/forallP/(_ j) //.
  by move=> _ /forallP/(_ i) /forallP/(_ j) /implyP/(_ Pi).
Qed.

Lemma disjoint_qregP_abs {T} (x : qreg T) s1 s2 : valid_qreg x ->
  index_prime2_disjoint s1 s2 ->
    disjoint_qregI (eval_index x s1) (eval_index x s2).
Proof. by rewrite valid_qregIE; apply: disjoint_qregIP_abs. Qed.

(* Lemma valid_qregIP_qreg_prime {T : qType} (x : qvar) (H : `{memctxt x T}) :
  valid_qregI (@qreg_prime T x H).
Proof. apply/valid_qregIP_prime. Qed. *)

Lemma disjoint_qregIP_prime2 (x1 x2 : qvar) s11 s12 s21 s22 : 
    x1 != x2 ->
      disjoint_qregI (eval_index (prime_index x1 s11) s12)
                     (eval_index (prime_index x2 s21) s22).
Proof.
rewrite !eval_index_prime_cat =>n12.
rewrite /disjoint_qregI/disjoint_qregI_rec/qi2seq/=; 
do 2 case: (qtype_of_index_rec _ _); lnil.
move=>??; rewrite disjoint_has. apply/hasP=>[[/=[]x s Pi]].
rewrite !(can2_mem_pmap basic_indexKV basic_indexK)/basic_index_to_pair/=.
move=>/mapP[] i _ /esym Pv1 /mapP[] j _ /esym Pv2; 
by move: n12; inversion Pv1; inversion Pv2; rewrite eqxx.
Qed.

Lemma disjoint_qregIP_primeL (x1 x2 : qvar) s1 s21 s22 : 
    x1 != x2 ->
      disjoint_qregI (prime_index x1 s1) (eval_index (prime_index x2 s21) s22).
Proof. by move=>/(disjoint_qregIP_prime2 s1 [::] s21 s22). Qed.

Lemma disjoint_qregIP_primeR (x1 x2 : qvar) s11 s12 s2 : 
    x1 != x2 ->
      disjoint_qregI (eval_index (prime_index x1 s11) s12) (prime_index x2 s2).
Proof. by move=>/(disjoint_qregIP_prime2 s11 s12 s2 [::]). Qed.

Lemma disjoint_qregIP_prime (x1 x2 : qvar) s1 s2 : 
    x1 != x2 ->
      disjoint_qregI (prime_index x1 s1) (prime_index x2 s2).
Proof. by move=>/(disjoint_qregIP_prime2 s1 [::] s2 [::]). Qed.

Lemma disjoint_qregP_prime {T1 T2 : qType} (x1 : qvart T1) (x2 : qvart T2) :
    (x1 : qvar) != x2 ->
      disjoint_qreg (qreg_prime x1) (qreg_prime x2).
Proof. apply/disjoint_qregIP_prime. Qed.

Goal forall (T : qType) (x : qreg (T * ((T * T) * T))),
  disjoint_qreg <{x.2.1.1}> <{x.2.1.2}>.
move=>T x; rewrite disjoint_qregIE !eval_indexE; apply: disjoint_qregIP_abs=>//.
Abort.

(* disjointness of qvar; here we treat qvar as variables                     *)
(* rather than concrete constructions from nat                               *)

Lemma mkqvarE (T : qType) (s1 s2 : string) (x : mkqvar T s1 s2) :
  (x : qvar) = QVar s1 s2.
Proof. by case: x=>/=. Qed.

Lemma qvar_diffP x y : qvar_diff x y -> (x != y).
Proof. by []. Qed.

(* lemmas that used in automation                                            *)
Lemma qvar_dis_app (x : qvar) (s : seq qvar) :
    qvar_dis (x :: s) -> qvar_dis s.
Proof. by move=>/andP[]. Qed.

Lemma qvar_dis2sub (x : qvar) (s : seq qvar) :
    qvar_dis (x :: s) -> qvar_dis_sub x s.
Proof. by move=>/andP[]. Qed.

Lemma qvar_dis_sub2diff (x : qvar) (y : qvar) (s : seq qvar) :
    qvar_dis_sub x (y :: s) -> qvar_diff x y.
Proof. by move=>/andP[]. Qed.

Lemma qvar_dis_sub_app (x : qvar) (y : qvar) (s : seq qvar) :
    qvar_dis_sub x (y :: s) -> qvar_dis_sub x s.
Proof. by move=>/andP[]. Qed.

Lemma qvar_diffC (x y : qvar) : qvar_diff x y = qvar_diff y x.
Proof. by rewrite/qvar_diff/qvar_diff_rec eq_sym. Qed.

Lemma valid_qregI_pair (s1 s2 : qreg_index) :
  (valid_qregI s1) -> (valid_qregI s2) -> (disjoint_qregI s1 s2)
    -> valid_qregI (pair_index s1 s2).
Proof. by luf=>P1 P2 Pd; rewrite cat_uniq_disjoint P1 P2 Pd. Qed.

Lemma valid_qregI_tuple n t si :
  (forall i : 'I_n, valid_qregI (si i)) -> 
    (forall i j : 'I_n, ((i : nat) != j) -> disjoint_qregI (si i) (si j)) ->
      valid_qregI (tuple_index t si).
Proof.
luf=>Pi Pij; rewrite flatten_uniq_disjoint; apply/andP; split.
- by apply/forallP. 
- by apply/forallP=>i; apply/forallP=>j; apply/implyP/Pij.
Qed.

Lemma valid_qregI_ffun n t si :
  (forall i : 'I_n, valid_qregI (si i)) -> 
    (forall i j : 'I_n, ((i : nat) != j) -> disjoint_qregI (si i) (si j)) ->
      valid_qregI (ffun_index t si).
Proof.
luf=>Pi Pij; rewrite flatten_uniq_disjoint; apply/andP; split.
- by apply/forallP. 
- by apply/forallP=>i; apply/forallP=>j; apply/implyP/Pij.
Qed.

Lemma valid_qreg_basic T (q : qreg T) : basic_type T -> valid_qreg q.
Proof. by move=>BT; rewrite valid_qregE qr2seq_basic_type. Qed.

Lemma valid_qreg_pair {T1 T2} (q1 : qreg T1) (q2 : qreg T2) :
  (valid_qreg q1) -> (valid_qreg q2) -> (disjoint_qreg q1 q2)
    -> valid_qreg (qreg_pair q1 q2).
Proof. by luf=>P1 P2 Pd; rewrite cat_uniq_disjoint P1 P2 Pd. Qed.

Lemma valid_qreg_tuple {n T} (qi : 'I_n -> qreg T) :
  (forall i : 'I_n, valid_qreg (qi i)) -> 
    (forall i j : 'I_n, ((i : nat) != j) -> disjoint_qreg (qi i) (qi j)) ->
      valid_qreg (qreg_tuple qi).
Proof.
luf=>Pi Pij; rewrite flatten_uniq_disjoint; apply/andP; split.
- by apply/forallP. 
- by apply/forallP=>i; apply/forallP=>j; apply/implyP/Pij.
Qed.

Lemma valid_qreg_ffun {n} {T : 'I_n -> qType} (qi : forall i : 'I_n, qreg (T i)) :
  (forall i : 'I_n, valid_qreg (qi i)) -> 
    (forall i j : 'I_n, ((i : nat) != j) -> disjoint_qreg (qi i) (qi j)) ->
        valid_qreg (qreg_ffun qi).
Proof.
luf=>Pi Pij; rewrite flatten_uniq_disjoint; apply/andP; split.
- by apply/forallP. 
- by apply/forallP=>i; apply/forallP=>j; apply/implyP/Pij.
Qed.

Lemma valid_qreg_fst {T1 T2} (q : qreg (QPair T1 T2)) :
  valid_qreg q -> valid_qreg (qreg_fst q).
Proof. by rewrite !valid_qregIE eval_indexE; apply/valid_qregI_eval. Qed.

Lemma valid_qreg_snd {T1 T2} (q : qreg (QPair T1 T2)) :
  valid_qreg q -> valid_qreg (qreg_snd q).
Proof. by rewrite !valid_qregIE eval_indexE; apply/valid_qregI_eval. Qed.

Lemma valid_qreg_ffuni {n} {T : 'I_n -> qType} (q : qreg {qffun T}) i:
  valid_qreg q -> valid_qreg (qreg_ffuni i q).
Proof. by rewrite !valid_qregIE eval_indexE; apply/valid_qregI_eval. Qed.

Lemma valid_qreg_tuplei {n T} (q : qreg T.[n]) i:
  valid_qreg q -> valid_qreg (qreg_tuplei i q).
Proof. by rewrite !valid_qregIE eval_indexE; apply/valid_qregI_eval. Qed.

Lemma valid_qreg_prime {T : qType} (x : qvart T) :
  valid_qreg (@qreg_prime T x).
Proof. by rewrite valid_qregIE; apply/valid_qregIP_prime. Qed.  

Lemma disjoint_qregI_pairL (s1 s2 : qreg_index) s :
  (disjoint_qregI s1 s) -> (disjoint_qregI s2 s) ->
    disjoint_qregI (pair_index s1 s2) s.
Proof. by luf; rewrite disjoint_cat=>->->. Qed.

Lemma disjoint_qregI_pairR s (s1 s2 : qreg_index) :
  (disjoint_qregI s s1) -> (disjoint_qregI s s2) ->
    disjoint_qregI s (pair_index s1 s2).
Proof. by rewrite ![_ s _]disjoint_qregIC; exact: disjoint_qregI_pairL. Qed.

Lemma disjoint_qregI_tupleL n t si s :
  (forall i : 'I_n, disjoint_qregI (si i) s) ->
    disjoint_qregI (tuple_index t si) s.
Proof. by luf=>/forallP; rewrite disjoint_flatten. Qed.

Lemma disjoint_qregI_tupleR s n t si :
  (forall i : 'I_n, disjoint_qregI s (si i)) ->
    disjoint_qregI s (tuple_index t si).
Proof.
by move=>P; rewrite disjoint_qregIC;
apply/disjoint_qregI_tupleL=>i; rewrite disjoint_qregIC.
Qed.

Lemma disjoint_qregI_ffunL n t si s :
  (forall i : 'I_n, disjoint_qregI (si i) s) -> 
      disjoint_qregI (ffun_index t si) s.
Proof. by luf=>/forallP; rewrite disjoint_flatten. Qed.

Lemma disjoint_qregI_ffunR s n t si :
  (forall i : 'I_n, disjoint_qregI s (si i)) -> 
      disjoint_qregI s (ffun_index t si).
Proof.
by move=>P; rewrite disjoint_qregIC;
apply/disjoint_qregI_ffunL=>i; rewrite disjoint_qregIC.
Qed.

Lemma disjoint_qreg_pairL T1 T2 (x1 : qreg T1) (x2 : qreg T2) T (x : qreg T) :
  (disjoint_qreg x1 x) -> (disjoint_qreg x2 x) ->
    disjoint_qreg (qreg_pair x1 x2) x.
Proof. by luf; rewrite disjoint_cat=>->->. Qed.

Lemma disjoint_qreg_pairR T (x : qreg T) T1 T2 (x1 : qreg T1) (x2 : qreg T2) :
  (disjoint_qreg x x1) -> (disjoint_qreg x x2) ->
    disjoint_qreg x (qreg_pair x1 x2).
Proof. by rewrite ![_ x _]disjoint_qregC; exact: disjoint_qreg_pairL. Qed.

Lemma disjoint_qreg_tupleL n Tx (x : 'I_n -> qreg Tx) Ty (y : qreg Ty) :
  (forall i : 'I_n, disjoint_qreg (x i) y) ->
    disjoint_qreg (qreg_tuple x) y.
Proof. by luf=>/forallP; rewrite disjoint_flatten. Qed.

Lemma disjoint_qreg_tupleR Ty (y : qreg Ty) n Tx (x : 'I_n -> qreg Tx) :
  (forall i : 'I_n, disjoint_qreg y (x i)) ->
    disjoint_qreg y (qreg_tuple x).
Proof.
by move=>P; rewrite disjoint_qregC;
apply/disjoint_qreg_tupleL=>i; rewrite disjoint_qregC.
Qed.

Lemma disjoint_qreg_ffunL n (Tx : 'I_n -> qType)
                         (x : forall i, qreg (Tx i)) Ty (y : qreg Ty) :
  (forall i : 'I_n, disjoint_qreg (x i) y) ->
    disjoint_qreg (qreg_ffun x) y.
Proof. by luf=>/forallP; rewrite disjoint_flatten. Qed.

Lemma disjoint_qreg_ffunR Ty (y : qreg Ty) n (Tx : 'I_n -> qType)
                          (x : forall i, qreg (Tx i)) :
  (forall i : 'I_n, disjoint_qreg y (x i)) -> 
      disjoint_qreg y (qreg_ffun x).
Proof.
by move=>P; rewrite disjoint_qregC;
apply/disjoint_qreg_ffunL=>i; rewrite disjoint_qregC.
Qed.

End Theory.

(* tactic for solving qvar_diff from hypothesis qvar_dis                     *)
Ltac tac_qvar_diff := repeat match goal with
    | [ |- is_true (negb (@eq_op qreg_qvar__canonical__eqtype_Equality _ _ ))]
        (* idtac "trivial"; *)
        => try (rewrite ?mkqvarE; clear; by []); apply/qvar_diffP
    | [ H : is_true (qvar_dis _) |- is_true (qvar_diff _ _)] 
        => move: {+}H 
    | [ |- is_true (qvar_dis (?x :: _)) -> is_true (qvar_diff ?x _)] 
        => move => /QRegAuto.qvar_dis2sub
    | [ |- is_true (qvar_dis (?x :: _)) -> is_true (qvar_diff _ ?x)] 
        => rewrite QRegAuto.qvar_diffC; move => /QRegAuto.qvar_dis2sub
    | [ |- is_true (qvar_dis (_ :: _)) -> is_true (qvar_diff _ _)] 
        => move => /QRegAuto.qvar_dis_app
    | [ |- is_true (qvar_dis_sub ?x (?y :: _)) -> is_true (qvar_diff ?x ?y)] 
        => apply: QRegAuto.qvar_dis_sub2diff
    | [ |- is_true (qvar_dis_sub _ (_ :: _)) -> is_true (qvar_diff _ _)] 
        => move => /QRegAuto.qvar_dis_sub_app
    end.

Ltac tac_valid_qreg_basic := try by apply/valid_qreg_basic/erefl.

Ltac tac_valid_qreg := match goal with
  (* canonical structure of valid qreg and qreg_expr *)
  | [ H : is_true (valid_qreg ?x) |- is_true (valid_qreg ?x) ] => by apply H
  | [ |- is_true (valid_qreg (qreg_base _)) ] => by apply/qreg_is_valid
  | [ |- is_true (valid_qregI (index_of_qreg (qreg_base _))) ]
      => by apply/qreg_is_valid
  | [ |- is_true (valid_qreg (qsem_of (qreg_expr_base _) _)) ]
      => by apply/qreg_expr_is_valid
  | [ |- is_true (valid_qregI (index_of_qreg (qsem_of (qreg_expr_base _) _))) ]
      => by apply/qreg_expr_is_valid

      (* valid_qreg_basic *)
  (* | [ |- is_true (valid_qreg _)] => try by apply/valid_qreg_basic *)
  | [ |- is_true (valid_qreg (qreg_prime _))] => by apply/valid_qreg_prime
  | [ |- is_true (valid_qreg (qreg_pair _ _))] => apply/valid_qreg_pair
  | [ |- is_true (valid_qreg (qreg_ffun _))] => apply/valid_qreg_ffun
  | [ |- is_true (valid_qreg (qreg_tuple _))] => apply/valid_qreg_tuple
  | [ |- is_true (valid_qreg (qreg_fst _))] => tac_valid_qreg_basic;
      (try rewrite !eq_qreg_fst); try apply/valid_qreg_fst
  | [ |- is_true (valid_qreg (qreg_snd _))] => tac_valid_qreg_basic;
      (try rewrite !eq_qreg_snd); try apply/valid_qreg_snd
  | [ |- is_true (valid_qreg (qreg_tuplei _ _))] => tac_valid_qreg_basic;
      (try rewrite !eq_qreg_tuplei); try apply/valid_qreg_tuplei
  | [ |- is_true (valid_qreg (qreg_ffuni _ _))] => tac_valid_qreg_basic;
      (try rewrite !eq_qreg_ffuni); try apply/valid_qreg_ffuni

  | [ |- is_true (valid_qregI (index_of_qreg (qreg_prime _)))] 
        => idtac "not desired valid 9"; by apply/valid_qregIP_prime
  | [ |- is_true (valid_qregI (eval_index (index_of_qreg (qreg_prime _)) _))] 
        => by apply/valid_qregIP_prime_eval

  | [ |- is_true (valid_qregI (prime_index _ _))] 
        => idtac "not desired valid 7"; by apply/valid_qregIP_prime
  | [ |- is_true (valid_qregI (eval_index (prime_index _ _) _))] 
        => idtac "not desired valid 8"; by apply/valid_qregIP_prime_eval

  | [ |- is_true (valid_qregI (eval_index _ _))] => apply/valid_qregI_eval

  | [ |- is_true (valid_qregI (pair_index _ _))]
        => idtac "not desired valid 1"; apply/valid_qregI_pair
  | [ |- is_true (valid_qregI (tuple_index _ _))] 
        => idtac "not desired valid 2"; apply/valid_qregI_tuple
  | [ |- is_true (valid_qregI (ffun_index _ _))] 
        => idtac "not desired valid 3"; apply/valid_qregI_ffun
  | [ |- is_true (valid_qregI (index_of_qreg (qreg_pair _ _)))] 
        => idtac "not desired valid 4"; apply/valid_qregI_pair
  | [ |- is_true (valid_qregI (index_of_qreg (qreg_tuple _)))]
        => idtac "not desired valid 5"; apply/valid_qregI_tuple
  | [ |- is_true (valid_qregI (index_of_qreg (qreg_ffun _)))]
        => idtac "not desired valid 6"; apply/valid_qregI_ffun
end.

(* Goal forall (x : qvar) (H1 : `{memctxt x (QPair QBool QBool)}), 
  valid_qreg <{('x.1)}>.
Proof.  intros. do ! tac_valid_qreg. rewrite !eval_indexE. tac_valid_qreg. *)

(* Goal forall (x1 x2 : qvar) (T : qType) 
  (H1 : `{memctxt x1 (QPair T T)}) (H2 : `{memctxt x2 (QPair T T)}), 
  valid_qreg <{('x1.1, 'x2.2)}>.
intros. do ? tac_valid_qreg. *)

Ltac tac_disjoint_qreg := match goal with
  | [ H : is_true (disjoint_qreg ?x ?y) |- is_true (disjoint_qreg ?x ?y) ] => by apply H
  | [ H : is_true (disjoint_qreg ?x ?y) |- is_true (disjoint_qreg ?y ?x) ] => by rewrite disjoint_qregC; apply H
  | [ |- is_true (disjoint_qreg (qreg_prime _) (qreg_prime _))]
        => apply/disjoint_qregP_prime
  | [ |- is_true (disjoint_qreg (qreg_pair _ _) _)]
        => apply/disjoint_qreg_pairL
  | [ |- is_true (disjoint_qreg _ (qreg_pair _ _))]
        => apply/disjoint_qreg_pairR
  | [ |- is_true (disjoint_qreg (qreg_tuple _) _)]
        => apply/disjoint_qreg_tupleL
  | [ |- is_true (disjoint_qreg _ (qreg_tuple _))]
        => apply/disjoint_qreg_tupleR
  | [ |- is_true (disjoint_qreg (qreg_ffun _) _)]
        => apply/disjoint_qreg_ffunL
  | [ |- is_true (disjoint_qreg _ (qreg_ffun _))]
        => apply/disjoint_qreg_ffunR

  | [ |- is_true (disjoint_qregI (eval_index (index_of_qreg ?x) _) (eval_index (index_of_qreg ?x) _))]
        => apply/disjoint_qregP_abs
  | [ |- is_true (disjoint_qregI (eval_index ?x _) (eval_index ?x _))]
        => idtac "not desired disjoint 11"; apply/disjoint_qregIP_abs
  | [ |- is_true (disjoint_qregI (eval_index (index_of_qreg (qreg_prime _)) _) 
          (eval_index (index_of_qreg (qreg_prime _)) _))]
        => apply/disjoint_qregIP_prime2
  | [ |- is_true (disjoint_qregI (index_of_qreg (qreg_prime _)) 
          (eval_index (index_of_qreg (qreg_prime _)) _))]
        => apply/disjoint_qregIP_primeL
  | [ |- is_true (disjoint_qregI (eval_index (index_of_qreg (qreg_prime _)) _)
          (index_of_qreg (qreg_prime _)))]
        => apply/disjoint_qregIP_primeR

  | [ |- is_true (disjoint_qregI (eval_index (prime_index _ _) _) 
          (eval_index (prime_index _ _) _))]
        => idtac "not desired disjoint 7"; apply/disjoint_qregIP_prime2
  | [ |- is_true (disjoint_qregI (prime_index _ _)
          (eval_index (prime_index _ _) _))]
        => idtac "not desired disjoint 8"; apply/disjoint_qregIP_primeL
  | [ |- is_true (disjoint_qregI (eval_index (prime_index _ _) _)
          (prime_index _ _))]
        => idtac "not desired disjoint 9"; apply/disjoint_qregIP_primeR
  | [ |- is_true (disjoint_qregI (prime_index _ _) (prime_index _ _))]
        => idtac "not desired disjoint 10"; apply/disjoint_qregIP_prime

  | [ |- is_true (disjoint_qregI (pair_index _ _) _)]
        => idtac "not desired disjoint 1"; apply/disjoint_qregI_pairL
  | [ |- is_true (disjoint_qregI _ (pair_index _ _))]
        => idtac "not desired disjoint 2"; apply/disjoint_qregI_pairR
  | [ |- is_true (disjoint_qregI (tuple_index _ _) _)]
        => idtac "not desired disjoint 3"; apply/disjoint_qregI_tupleL
  | [ |- is_true (disjoint_qregI _ (tuple_index _ _))]
        => idtac "not desired disjoint 4"; apply/disjoint_qregI_tupleR
  | [ |- is_true (disjoint_qregI (ffun_index _ _) _)]
        => idtac "not desired disjoint 5"; apply/disjoint_qregI_ffunL
  | [ |- is_true (disjoint_qregI _ (ffun_index _ _))]
        => idtac "not desired disjoint 6"; apply/disjoint_qregI_ffunR
end.

Ltac move_extra := repeat match goal with
  | [ H : is_true (@eq_op _ _ _) |- _ ]
    => move : H; try clear H
  | [ H : is_true (negb (@eq_op _ _ _)) |- _ ]
    => move : H; try clear H
  (* | [ H : is_true (@eq_op (fintype_ordinal__canonical__eqtype_Equality _) _ _) |- _ ]
    => move : H; try clear H
  | [ H : is_true (negb (@eq_op (fintype_ordinal__canonical__eqtype_Equality _) _ _)) |- _ ]
    => move : H; try clear H *)
  | [ H : is_true (leq _ _) |- _ ]
    => move : H; try clear H
  | [ H : is_true (negb (leq _ _)) |- _ ]
    => move : H; try clear H
  | [ H : _ |- _ ]
    => try clear H; try move : H; try clear H
end.

Ltac elim_cmget := repeat match goal with
    [ |- _ ] => let x := fresh "cv" in
      set x := cmget _ _ _;
      move: x => /=
  end.

(* TODO deal with injection if mc_nat fails to solve the goal *)
Ltac tac_expose := rewrite /qreg_expose; intros;
  rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=;
    repeat match goal with
    | [ n : 'I_0 |- _ ] => by exfalso; clear - n; case: n
    | [ |- forall _ , _ ] => intros
    | [ |- is_true (valid_qreg _) ] => tac_valid_qreg
    | [ |- is_true (disjoint_qreg _ _) ] => tac_disjoint_qreg
    | [ |- is_true (valid_qregI _) ] => tac_valid_qreg
    | [ |- is_true (disjoint_qregI _ _) ] => tac_disjoint_qreg
    | [ |- is_true (valid_qreg _) ] => 
          (* idtac "tac qreg_expose 1";  *)
          tac_valid_qreg_basic;
          rewrite ?valid_qregIE ?eval_indexE
    | [ |- is_true (disjoint_qreg _ _) ] => 
          (* idtac "tac qreg_expose 2";  *)
          rewrite ?disjoint_qregIE ?eval_indexE
    | [ |- is_true (negb (@eq_op qreg_qvar__canonical__eqtype_Equality _ _ ))]
           => tac_qvar_diff
    | [ |- is_true (index_prime2_disjoint _ _)] => 
          (* idtac "tac qreg_expose 3"; *)
          rewrite /index_prime2_disjoint/nat_of_qnat/cvtype/=; 
          elim_cmget; move_extra; autonat.AutoNat.mc_nat
    end.

End QRegAuto.

Global Hint Extern 0 (qreg_expose _) => (QRegAuto.tac_expose) : typeclass_instances.

(*
Section TEST.

(* Variable (n : nat) (T : qType) (x : 'QReg[T.[n]]).

Goal forall (i j : 'I_n), i != j -> valid_qreg <{ (x.[i], x.[j])}>.
Proof. QRegAuto.tac_expose. Qed. *)

(*
Goal forall (x y z w t: qvar) (H : qvar_dis [:: x; y; z; w; t]), qvar_diff t z.
Proof.  intros. QRegAuto.tac_qvar_diff. Qed.

Goal forall (x y z w t: qvar) (H : qvar_dis [:: x; y; z; w; t]), t != z.
Proof.  intros. QRegAuto.tac_qvar_diff. Qed.

Goal forall (x : mkqvar QBool "a" "b") (y : mkqvar QBool "c" "d"), (x : qvar) != y.
Proof. intros. QRegAuto.tac_qvar_diff. Qed.

Goal QVar "a" "b" != QVar "c" "d".
Proof. QRegAuto.tac_qvar_diff. Qed.

Set Printing All.
Variable (v : qvart (Bool+Bool).[5]).
Goal valid_qreg <{ 'v.[Ord 2] }>.
QRegAuto.tac_expose.
Qed.

Variable (v1 : qreg Bool).
Goal valid_qreg v1.
QRegAuto.tac_expose.
Qed.
*)


(* for fun_index case, please add the injectiveness to the context *)
(*
Goal forall j : nat,
    valid_qregI (ffun_index (fun => QBool) (fun i : 'I_5 => 
      QRegAuto.eval_index (prime_index (QVar "1" "1") [::]) [:: qnat_ffuni (rshift j.+1 i)])).
Proof. QRegAuto.tac_expose. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2.[3]]), 
  disjoint_qreg <{x.1}> <{(tuple i => x.2.[i]).[ord0]}>.
Proof. QRegAuto.tac_expose. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2.[3]]), 
  disjoint_qreg <{x.1}> <{(tuple i => x.2.[i])}>.
Proof. QRegAuto.tac_expose. Qed.

Context (x : qvart Bool.[5]).
Context (y : qvart ('I_6).[5]).
Context (z : qvart (Bool.[3]).[3]).
Context (w : qvart ((Bool.[4]).[4] * (Bool.[3]).[3])).
Context (dis : qvar_dis [:: (x : qvar); (y : qvar); (z : qvar); (w : qvar)]).
Check <{ 'x.[ord0] : QBool }>.
Check <{ 'y.[ord0] }>.
Check <{ 'z.[ord0] }>.
Check <{ ('w.1 ) }>.
Check <{ 'w.2 }>.
Check <{ 'w.1.[ord0] }>.
Check <{ ('w.1.[ord0],'w.2.[ord_max]).1 }>.
Check <{ ('w.1.[ord0],'w.2.[ord_max]) }>.
Check <{ ('w.1.[ord0],'w.2.[ord_max]) }>.

Goal valid_qreg <{ ((('w.1.[ord0],'w.2.[ord_max]),'x).2,'y).1 }>.
Proof. QRegAuto.tac_expose. Qed.
Check <{ ('w.1.[ord0],'w.2.[ord_max]).2 }>.

Check [wf_qreg of <{ ((('w.1.[ord0],'w.2.[ord_max]),'x).2,'y).1 }> ].
Check [wf_qreg of <{ ('y.[ord0], 'x.[ord0]) }> ].

Check <{ (tuple i : 'I_3 => 'w.2.[i]).[ord0] }>. 
Check <{ (tuple i => 'w.2.[i]).[ord0] }>.
Check <{ ( tuple i => 'w.2.[i] ) }>.
Check <{ tuple i => 'w.2.[i] }>.
Check <{ tuple i => 'w.2.[i] }>.
Check <{ (tuple i => 'w.1.[i]).[ord0] }>.
Check <{ (((tuple i => 'w.2.[i]).[ord0]), ((tuple i => 'w.1.[i]).[ord0])) }>.
Goal valid_qreg <{ (tuple i : 'I_3 => 'w.2.[i]).[ord0] }>.
Proof. QRegAuto.tac_expose. Qed.

Goal valid_qreg <{ (((tuple i => 'w.2.[i]).[ord0]), ((tuple i => 'w.1.[i]).[ord0])) }>.
Proof. QRegAuto.tac_expose. Qed.

Variable (qx : 'QReg[(Bool.[4]).[4] * (Bool.[3]).[3]]).

Goal valid_qreg <{ (((tuple i => qx.2.[i]).[ord0]), ((tuple i => qx.1.[i]))) }>.
Proof. time QRegAuto.tac_expose. Qed.

Goal <{ ((((tuple i => 'w.2.[i]).[ord0]), ((tuple i => 'w.1.[i]).[ord0])), 'x.[ord0]) }> =r 
  <{ ((('w.2.[ord0]), ('w.1.[ord0])), 'x.[ord0]) }>.
Proof. by rewrite ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni). Qed.

Goal <{ ((((tuple i => ('w.2.[i],'w.1.[ord0]).1)), ((tuple i => 'w.1.[i]).[ord0])), 'x.[ord0]) }> =r
  <{ (((tuple i => 'w.2.[i]), ('w.1.[ord0])), 'x.[ord0]) }>.
Proof. by rewrite ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni). Qed.

Goal <{ ((((tuple i => ('w.2.[i],'w.1.[ord0]).1).[ord0]), ((tuple i => 'w.1.[i]).[ord0])), 'x.[ord0]) }> =r
  <{ ((('w.2.[ord0]), ('w.1.[ord0])), 'x.[ord0]) }>.
Proof. by rewrite ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni). Qed. *)

(* Variable (qx : 'QReg[Bool.[4].[4] * Bool.[3].[3]]) (qy : 'QReg[Bool.[4].[4] * Bool.[3].[3]]).

Goal valid_qreg <{ (((tuple i => qy.2.[i]).[ord0]), ((tuple i => qy.1.[i]))) }>.
Proof. QRegAuto.tac_expose. Qed. *)

(* Lemma half_ord_subproof (n : nat) : ((n./2).+1 <= n.+2)%N.
Proof. by rewrite ltnS; apply: (leq_trans (half_leqn _)). Qed.
Definition half_ord {n} := widen_ord (half_ord_subproof n).

(* Variable (n : nat) (i : 'I_(n./2.+1) ).
Variable (x : 'QReg[QArray n.+2 QBool]).
Goal valid_qreg <{(x.[ (@half_ord _ i) ], x.[rev_ord (half_ord i)])}>.
Proof. QRegAuto.tac_expose. Qed.
Check [wf_qreg of <{(x.[ (@half_ord _ i) ], x.[rev_ord (half_ord i)])}>]. *)

Variable (n : nat) (x : 'QRegExpr[QArray n.+2 QBool]).
Let i := CVar (QType (QOrd (n./2))) "rev_tuple" "i".
Check <{{ (x.[half_ord%:F1 i], x.[(@rev_ord _)%:F1 (half_ord%:F1 i)]) }}>.
Goal forall m, valid_qreg (qsem_of <{{ (x.[half_ord%:F1 i], x.[(@rev_ord _)%:F1 (half_ord%:F1 i)]) }}> m).
Proof. time QRegAuto.tac_expose. Qed. *)

(* Fixpoint index_prime_disjoint x (s : seq qnat) (q : qreg_index) : bool :=
    match q with
    | prime_index y s' => (x != y) || (index_prime2_disjoint s s')
    | pair_index s1 s2 => (index_prime_disjoint x s s1) &&
                            (index_prime_disjoint x s s2)
    | ffun_index n _ s' | tuple_index n _ s' 
        => [forall i : 'I_n, (index_prime_disjoint x s (s' i))]
    | fault_index => true
    end.

Fixpoint index_pair_disjoint (s1 s2 : qreg_index) :=
    match s1 with
    | prime_index x t1 => index_prime_disjoint x t1 s2
    | pair_index t1 t2 => (index_pair_disjoint t1 s2) &&
                            (index_pair_disjoint t2 s2)
    | ffun_index n _ s | tuple_index n _ s 
        => [forall i : 'I_n, index_pair_disjoint (s i) s2]
    | fault_index => true
    end.

Definition index_fun_disjoint {n} (s : 'I_n -> qreg_index) :=
    [forall i : 'I_n, 
        [forall j : 'I_n, 
            ((i : nat) != j) ==> index_pair_disjoint (s i) (s j)]].

Lemma index_fun_disjointP {n} (s : 'I_n -> qreg_index) (i j : 'I_n) :
  index_fun_disjoint s -> (i : nat) != j -> index_pair_disjoint (s i) (s j).
Proof. by move=>/forallP/(_ i)/forallP/(_ j)/implyP. Qed.

Lemma index_prime_disjointC x s1 s2 :
  index_prime_disjoint x s1 s2 = index_pair_disjoint s2 (prime_index x s1).
Proof.
elim: s2=>/=[//|??|?<-?<-//|n _ s IH|n _ s IH].
by rewrite eq_sym; f_equal; apply: index_prime2_disjointC.
all: by under eq_forallb do rewrite IH.
Qed.

Lemma index_pair_disjointC (s1 s2 : qreg_index) : index_pair_disjoint s1 s2 = 
  index_pair_disjoint s2 s1.
Proof.
elim: s1 s2=>/=[s2 |s1 s2 ?|s1 IH1 s2 IH2 s3|n t1 s1 IH1 s2|n t1 s1 IH1 s2].
- by elim: s2=>//[s1/=<-s2//|s1 P2 s2/=|s1 P2 s2/=]; symmetry; apply/forallbTP.
- apply: index_prime_disjointC.
- rewrite IH1 IH2; elim: s3=>//=[s3 <- s4 <-|n _ s H1|n _ s H1].
  by rewrite !andbA; f_equal; rewrite -!andbA; f_equal; rewrite andbC.
  1,2: by rewrite forallb_and; under eq_forallb do rewrite H1.
- under eq_forallb do rewrite IH1.
  elim: s2=>//=[|?<-?<-|??? IH2|??? IH2]; first by apply/forallbTP.
  by rewrite forallb_and.
  1,2: by rewrite forallb_exchange; under eq_forallb do rewrite IH2.
- under eq_forallb do rewrite IH1.
  elim: s2=>//=[|?<-?<-|??? IH2|??? IH2]; first by apply/forallbTP.
  by rewrite forallb_and.
  1,2: by rewrite forallb_exchange; under eq_forallb do rewrite IH2.
Qed.

Fixpoint valid_qreg_index (s : qreg_index) : bool := 
    match s with
    | prime_index _ _ => true
    | pair_index s1 s2 => (valid_qreg_index s1) && (valid_qreg_index s2)
                              && (index_pair_disjoint s1 s2)
    | ffun_index n _ si | tuple_index n _ si
        => [forall i : 'I_n, valid_qreg_index (si i)] && (index_fun_disjoint si)
    | fault_index => false
    end.

Lemma index_prime2_disjoint_rcons s x1 x2 :
    index_prime2_disjoint (rcons s x1) (rcons s x2) = (nat_of_qnat x1 != nat_of_qnat x2).
Proof. by elim: s=>/=[|a l]; [case: eqP | rewrite eqxx]. Qed.

Lemma index_prime2_disjoint_cats s l1 l2 :
  index_prime2_disjoint (s ++ l1) (s ++ l2) = index_prime2_disjoint l1 l2.
Proof. by elim: s l1 l2=>// a l IH l1 l2; by rewrite !cat_cons/= eqxx/=. Qed.

Lemma index_prime_disjoint_rcons x s1 s2 i :
  index_prime_disjoint x s1 s2 -> index_prime_disjoint x (rcons s1 i) s2.
Proof.
elim: s2=>//=[| s2 IH1 s3 IH2/andP[]P1 P2 | n _ s IH /forallP P | n _ s IH /forallP P ].
- elim: s1=>[n l|a l IH n]; first by rewrite /=orbF=>->.
  case=>// a' l'; rewrite rcons_cons/= orbCA [in X in _ -> X]orbCA;
  by move=>/orP[->//|/IH->]; rewrite orbT.
- by apply/andP; split; [apply/IH1|apply/IH2].
all: by apply/forallP=>j; apply: IH.
Qed.

Lemma index_prime2_disjoint_prefix s1 s2 :
  index_prime2_disjoint s1 s2 -> (~~ (seq.prefix s1 s2)) && (~~ (seq.prefix s2 s1)).
Proof.
move: s1 s2; apply: seq_ind20=>[s|s|x1 x2 s1 s2].
1,2: by rewrite prefix0s//= andbF index_prime2_disjointC.
move=>IH/=; rewrite (eq_sym x2 x1) ; case: (@eqP _ x1 x2)=>[->|//=].
by rewrite ?eqxx/=.
Qed.

Ltac ltest := try do [by move=>???/=; case: [forall _, _] |
by move=>??/=; do 2 case: (qtype_of_index _)=>//].

Lemma disjoint_qregIP Tx x Ty y: qtype_of_index x = Some Tx ->
  qtype_of_index y = Some Ty -> 
    index_pair_disjoint x y -> [disjoint qi2seq x & qi2seq y].
Proof.
move: Tx x Ty y.
(* first sufficiency *)
suff Q1: forall Tx vx sx Ty y, 
  let x :=  prime_index vx sx in
    qtype_of_index x = Some Tx ->
      qtype_of_index y = Some Ty -> 
        index_pair_disjoint x y -> [disjoint qi2seq x & qi2seq y].
move=>++Ty y +Py; elim=>//=[||?|??||????||].
1-4,6: by case=>//; ltest; move=>v s Ps; move: (Q1 _ _ _ _ _ Ps Py).
- move=>T1 IH1 T2 IH2.
  case=>//; ltest; first by move=>v s Ps; move: (Q1 _ _ _ _ _ Ps Py).
  move=>x1 x2; rewrite [in X in X -> _]/=.
  destruct (qtype_of_index x1) eqn:E1=>//.
  destruct (qtype_of_index x2) eqn:E2=>// /esym Pv.
  inversion Pv; case: q / H0 E1 Pv; case: q0 / H1 E2=>P2 P1 _.
  by move=>/=/andP[]/(IH1 _ P1)+/(IH2 _ P2); rewrite disjoint_cat=>->->.
- move=>n T IH.
  case=>//; ltest; first by move=>v s Ps; move: (Q1 _ _ _ _ _ Ps Py).
  move=>m Tx x Px/=/forallP Pi; rewrite disjoint_flatten; apply/forallP=>i.
  apply/IH=>//. move: Px=>/=; case E: [forall _, _] =>// /esym Pv.
  by move: E; inversion Pv=>/forallP/(_ i)/eqP.
- move=>n T IH.
  case=>//; ltest; first by move=>v s Ps; move: (Q1 _ _ _ _ _ Ps Py).
  move=>m Tx x Px/=/forallP Pi; rewrite disjoint_flatten; apply/forallP=>i.
  move: Px=>/=; case E: [forall _, _] =>// /esym Pv.
  inversion Pv; case: m / H0 Tx x Pi i E Pv H1=>Tx x Pi i /forallP Pii _ /inj_existT Pt.
  by case: Tx / Pt Pii=>/(_ i)/eqP Pt; apply: (IH i).
(* second sufficiency *)
suff Q2: forall Tx vx sx Ty vy sy,
  let x := (prime_index vx sx) in
  let y := (prime_index vy sy) in
  qtype_of_index x = Some Tx ->
    qtype_of_index y = Some Ty -> 
      index_pair_disjoint x y -> [disjoint qi2seq x & qi2seq y].
move=>Tx vx sx Ty y x; rewrite index_pair_disjointC disjoint_sym /x; clear x.
elim: Ty Tx vx sx y=>[||?|??||????||].
1-4,6: move=>Tx vx sx y Px; case: y=>//; ltest;
  by move=>v s Py; move: (Q2 _ _ _ _ _ _ Py Px).
- move=>T1 IH1 T2 IH2 Tx vx sx y Px; case: y=>//[|y1 y2||]; ltest; 
    first by move=>vy sy Py; move: (Q2 _ _ _ _ _ _ Py Px).
  rewrite/= disjoint_cat; case E1: (qtype_of_index y1)=>//; 
  case E2: (qtype_of_index y2)=>// Pv; move: E1 E2; inversion Pv;
  by move=>/(IH1 _ _ _ _ Px)/= P1 /(IH2 _ _ _ _ Px)/= P2 /andP[]/P1->/P2->.
- move=>n T IH Tx vx sx y Px; case: y=>//[||m Ty y Py|]; ltest; 
    first by move=>vy sy Py; move: (Q2 _ _ _ _ _ _ Py Px).
  move: Py=>/=; case E: [forall _, _] =>//Pv; move: y E.
  inversion Pv=>y /forallP Pi /forallP Pii; rewrite disjoint_flatten; apply/forallP=>i.
  by move: (Pi i)=>/eqP/(IH _ _ _ _ Px)/(_ (Pii i)).
- move=>n T IH Tx vx sx y Px; case: y=>//[|||m Ty y/=]; ltest; 
    first by move=>vy sy Py; move: (Q2 _ _ _ _ _ _ Py Px).
  case E: [forall _, _] =>// /esym Pv.
  inversion Pv; case: m / H0 Ty y E Pv H1=>Ty y/forallP Pi _ /inj_existT Pt.
  case: Ty / Pt Pi=>Pi/forallP Pii; rewrite disjoint_flatten; apply/forallP=>i.
  by move: (Pi i)=>/eqP/(IH i _ _ _ _ Px)/(_ (Pii i)).
(* final proof *) 
move=>Tx vx sx Ty vy sy/=; rewrite /qi2seq/=; case: eqP=>[ <-|]; last first.
  move=>/eqP P->->/= _.
  rewrite disjoint_has; apply/negP=>/hasP[[ux ??]].
  rewrite !(can2_mem_pmap basic_indexKV basic_indexK)=>/mapP[? _]/= Px/mapP[? _]/= Py.
  inversion Px; inversion Py; by move: P; rewrite -H0 -H2 eqxx.
move=>Px Py/= /index_prime2_disjoint_prefix; rewrite Px Py; apply/contraTT.
rewrite - negb_or negbK disjoint_has negbK=>/hasP[][v s ?]; 
rewrite !(can2_mem_pmap basic_indexKV basic_indexK)/basic_index_to_pair/=.
move=>/mapP[x1]/prefix_ssqnat Px1 Pv1 /mapP[x2]/prefix_ssqnat Px2 Pv2.
inversion Pv1; case: x1 / H1 Px1 Pv1; inversion Pv2; case: x2 / H2 Px2 Pv2=>+ _ + _.
case: (ltnP (size sx) (size sy))=>[/ltnW|].
by move=>P1; rewrite !prefixE=>/eqP<-/eqP{2}<-; rewrite (take_takel _ P1) eqxx.
by move=>P1; rewrite !prefixE=>/eqP{3}<-/eqP{3}<-; rewrite (take_takel _ P1) eqxx orbT. 
Qed.

Lemma disjoint_qregP {Tx Ty} (x : qreg Tx) (y : qreg Ty) :
  index_pair_disjoint x y -> [disjoint x & y]%fset.
Proof.
rewrite -fdisjoint_qregP disjoint_qregE/qr2seq;
apply/(@disjoint_qregIP Tx _ Ty); apply/index_typeK.
Qed.

Lemma valid_qregIP (T : qType) (q : qreg_index) :
   qtype_of_index q = Some T -> valid_qreg_index q -> valid_qregI q.
Proof.
rewrite /valid_qregI/valid_qregI_rec/qi2seq.
elim: T q =>//=[||n |?? |T1 H1 T2 H2|???? |n T IH|n T IH]; case=>//=;
  try do [by move=>???/=; case: [forall _, _] |
  by move=>??/=; do 2 case: (qtype_of_index _)=>//].
1-4,7: by move=>v s/=-> _; apply (pmap_uniq basic_indexKV).
- move=>v s/= P; rewrite P /= map_cat pmap_cat cat_uniq_disjoint=> _.
  have P1: qtype_of_index (prime_index v (rcons s qnat_fst)) = Some T1.
  by rewrite/= qtype_of_index_rec_rcons P.
  have P2: qtype_of_index (prime_index v (rcons s qnat_snd)) = Some T2.
  by rewrite/= qtype_of_index_rec_rcons P.
  move: (H1 _ P1) (H2 _ P2)=>/=; rewrite !qtype_of_index_rec_rcons P=>->//= ->//.
  move: P1 P2 (disjoint_qregIP P1 P2)=>/=; rewrite /qi2seq/==> ->->.
  by rewrite andbT eqxx/= index_prime2_disjoint_rcons//==>->.
- move=>x1 x2; case E1: (qtype_of_index x1)=>[q1|]//; 
  case E2: (qtype_of_index x2)=>[q2|] =>// /esym Pv.
  inversion Pv; clear Pv; case: q1 / H0 E1; case: q2 / H3 E2 =>E2 E1.
  by rewrite cat_uniq_disjoint=>/andP[]/andP[]/(H1 _ E1)->/(H2 _ E2)->/(disjoint_qregIP E1 E2)->.
- move=>v s P; rewrite P /= map_flatten pmap_flatten -2!map_comp=> _.
  have Pi (i : 'I_n): qtype_of_index (prime_index v (rcons s (qnat_tuplei i))) = Some T.
    by rewrite/= qtype_of_index_rec_rcons P; case: eqP=>//.
  rewrite flatten_uniq_disjoint !forallbTP// =>[|i]; last (apply/forallP=>j; apply/implyP).
  by move=>i /=; move: (IH _ (Pi i))=>/=; rewrite qtype_of_index_rec_rcons P; case: eqP=>// _ ->.
  move=>nij /=; move: (Pi i) (Pi j) (disjoint_qregIP (Pi i) (Pi j)); rewrite/qi2seq/==>->->.
  by rewrite eqxx/= index_prime2_disjoint_rcons/= nij=>->.
- move=>m T' q; case E: [forall _, _] =>// /esym Pv.
  inversion Pv; case: m / H0  q E Pv; case: T' / H1=>q /forallP Pi _.
  have Pii (i : 'I_n): qtype_of_index (q i) = Some T by move: (Pi i)=>/eqP.
  rewrite flatten_uniq_disjoint=>/andP[]/forallP P1/forallP P2.
  apply/andP; split; apply/forallP=>i; first by apply/IH.
  apply/forallP=>j; apply/implyP=>Pij; move: (P2 i)=>/forallP/(_ j)/implyP/(_ Pij).
  by apply/(disjoint_qregIP (Pii i) (Pii j)).
- move=>v s P; rewrite P /= map_flatten pmap_flatten -2!map_comp=> _.
  have Pi (i : 'I_n): qtype_of_index (prime_index v (rcons s (qnat_ffuni i))) = Some (T i).
    by rewrite/= qtype_of_index_rec_rcons P; case: eqP=>// ?; rewrite cast_ord_id.
  rewrite flatten_uniq_disjoint !forallbTP// =>[|i]; last (apply/forallP=>j; apply/implyP).
  by move=>i /=; move: (IH _ _ (Pi i))=>/=; rewrite qtype_of_index_rec_rcons P; 
    case: eqP=>//?; rewrite cast_ord_id=>->.
  move=>nij /=; move: (Pi i) (Pi j) (disjoint_qregIP (Pi i) (Pi j)); rewrite/qi2seq/==>->->.
  by rewrite eqxx/= index_prime2_disjoint_rcons nij=>->.
- move=>m T' q; case E: [forall _, _] =>// /esym Pv.
  inversion Pv; case: m / H0 T' q E Pv H1=>T' q /forallP Pi _ /inj_existT Pv.
  case: T' / Pv Pi=>Pi.
  have Pii i: qtype_of_index (q i) = Some (T i) by move: (Pi i)=>/eqP.
  rewrite flatten_uniq_disjoint=>/andP[]/forallP P1/forallP P2.
  apply/andP; split; apply/forallP=>i; first by apply/IH.
  apply/forallP=>j; apply/implyP=>Pij; move: (P2 i)=>/forallP/(_ j)/implyP/(_ Pij).
  by apply/(disjoint_qregIP (Pii i) (Pii j)).
Qed.

Lemma valid_qregP T (x : qreg T) : valid_qreg_index x -> valid_qreg x.
Proof. by rewrite valid_qregIE; apply/(@valid_qregIP T)/index_typeK. Qed. *)

End TEST. *)







(*
(* memory model *)

Module Type TEST_MODULE.

(* system *)
Parameter (L : finType).
(* mapping *)
Parameter (M : {set L} -> {set L} -> {set L}).

Parameter (MA : forall i j k, M (M i j) k = M i (M j k)).

Parameter (MC : forall i j, M i j = M j i).

Infix ":**:" := M (at level 10).

End TEST_MODULE.

Module TEST_THEORY (M : TEST_MODULE).

Import M.

Lemma MACA (x y z t : {set L}) :
  M (x :**: y) (M z t) = M (M x z) (M y t).
Proof. by rewrite !MA; f_equal; rewrite -!MA; f_equal; rewrite MC. Qed.

End TEST_THEORY.

Module M1 <: TEST_MODULE.

Let L := bool_finType.

Let M := @setU L.

Lemma MA : forall i j k, M (M i j) k = M i (M j k).
Proof. by rewrite /M=> i j k; rewrite setUA. Qed.

Lemma MC : forall i j, M i j = M j i.
Proof. by rewrite /M=>i j; rewrite setUC. Qed.

End M1.

Module M1_THEORY := TEST_THEORY M1.
Section test.
Import M1_THEORY.

Goal M1.L = bool_finType. Proof. rewrite/M1.L. by []. Qed.

Goal forall (x y z t : {set bool_finType}), (x :|: y :|: (z :|: t)) = (x :|: z :|: (y :|: t)).
intros. rewrite MACA. Qed.
intros; by move: (MACA x y z t); rewrite /M1.M.

rewrite MACA.  
Check M1.L.

exact: MACA. rewrite MACA.
 *)


(* dirac algebra *)










(* Section QVarName.
Implicit Type (T : qType).

Inductive qvar_name := QVarName of string & string.
(* Inductive cvar (T : Type) := CVar of nat. *)

Definition qvar_name_eq (x y : qvar_name) :=
  let: QVarName x1 x2 := x in let: QVarName y1 y2 := y in (x1 == y1) && (x2 == y2).

Lemma qvar_name_eqP (x y : qvar_name) : reflect (x = y) (qvar_name_eq x y).
Proof.
by case: x y => [x1 x2] [y1 y2]; apply: (iffP andP) => [[]/eqP->/eqP->|[->->]].
Qed.

Definition qvar_name_eqMixin := EqMixin qvar_name_eqP.
Canonical qvar_name_eqType := EqType qvar_name qvar_name_eqMixin.
Lemma qvar_name_to_stringK : cancel 
  (fun x : qvar_name => let: QVarName s1 s2 := x in (s1,s2))
    (fun s => match s with | (s1,s2) => QVarName s1 s2 end).
Proof. by case. Qed.
Definition qvar_name_choiceMixin := CanChoiceMixin qvar_name_to_stringK.
Canonical qvar_name_choiceType := Eval hnf in ChoiceType qvar_name qvar_name_choiceMixin.
Definition qvar_name_countMixin := CanCountMixin qvar_name_to_stringK.
Canonical qvar_name_countType := Eval hnf in CountType qvar_name qvar_name_countMixin.

(* disjointness of qvar; here we treat qvar as variables                     *)
(* rather than concrete constructions from string                            *)
Definition qvar_diff_rec (x y : qvar_name) : bool := x != y.
Definition qvar_diff := nosimpl qvar_diff_rec.

Fixpoint qvar_dis_sub_rec (x : qvar_name) (s : seq qvar_name) : bool :=
    match s with
    | [::] => true
    | h :: t => qvar_diff x h && (qvar_dis_sub_rec x t)
    end.
Definition qvar_dis_sub := nosimpl qvar_dis_sub_rec.

Fixpoint qvar_dis_rec (s : seq qvar_name) : bool :=
    match s with
    | [::] => true
    | h :: t => (qvar_dis_sub h t) && (qvar_dis_rec t)
    end.
Definition qvar_dis := nosimpl qvar_dis_rec.

End QVarName.

(* restriction: finite qvar_name *)
Definition context := {fmap qvar_name -> qType}.
Context (G : context).

Section MKQVar.

Inductive qvar (T : qType) := QVar (name : qvar_name) & (G.[?name]%fmap == Some T).
Definition qname (T : qType) (q : qvar T) :=
  let: QVar name _ := q in name.
Coercion qname : qvar >-> qvar_name.

Inductive mkqvar (T : qType) (s1 s2 : string) := MKQVar & (G.[?(QVarName s1 s2)]%fmap == Some T).
Definition to_qvar (T : qType) (s1 s2 : string) (q : mkqvar T s1 s2) :=
  let: MKQVar P := q in QVar P.
Coercion to_qvar : mkqvar >-> qvar.

End MKQVar. *)





(*****************************************************************************)




(* Test : computable case                                                    *)
(* Compute index_pair_disjoint 
  (pair_index (prime_index (QVar 1) [::qnat_ffuni (COrdinal 2 5);qnat_ffuni (COrdinal 3 5)])
    (pair_index (prime_index (QVar 2) [::qnat_ffuni (COrdinal 3 5);qnat_ffuni (COrdinal 2 5)]) 
      (prime_index (QVar 1) [::qnat_ffuni (COrdinal 2 5);qnat_ffuni (COrdinal 3 5)])))
  (pair_index (prime_index (QVar 1) [::qnat_ffuni (COrdinal 3 5);qnat_ffuni (COrdinal 2 5)]) 
    (pair_index (prime_index (QVar 1) [::qnat_ffuni (COrdinal 1 5);qnat_ffuni (COrdinal 3 5)]) 
      (prime_index (QVar 1) [::qnat_ffuni (COrdinal 2 5);qnat_ffuni (COrdinal 4 5)]))). *)




(* original code from Pierre-Yves, August 2022   *)
(*
Definition var := nat.

Definition context := nat -> option ihbFinType.

Class memctxt (G : context) (x : var) (T : ihbFinType) :=
    MemCtxt : (G x = Some T).

Definition state (G : context) :=
    forall (x : var) {T : ihbFinType}, `{memctxt G x T} -> T.

Inductive cmd (G : context) :=
    | CmdSkip
    | CmdVar (x : var) {T : ihbFinType} (e : state G -> T) of `{memctxt G x T}
    | CmdSeq of cmd G & cmd G.

Context (G : context) (x y : var).
Context (xt : memctxt G x [ihbFinType of bool]).
Context (yt : memctxt G y [ihbFinType of 'I_5]).

Check (fun `{m : state G} => true).

Notation "x <<- e" := (@CmdVar _ x _ (fun `{m : state G} => e)) (at level 50).

Check yt.

(* Definition foo : cmd G := x <<- (x _ _ || true). *)

Lemma bar (G : context) y (T : ihbFinType) (e : T) (h : `{memctxt G y T}) :
    y <<- e = y <<- e.
Abort.

Class qreg_expose (P : Prop) := Expose : P.

Global Hint Extern 0 (qreg_expose _) => (exact) : typeclass_instances.
Global Hint Extern 0 (qreg_expose (is_true _)) => 
    (match goal with H : is_true _ |- _ => exact: H end) : typeclass_instances. 

Inductive I := | V (x : nat) (y : nat) of `{qreg_expose (x != y)}.

Notation v x y := (V x y _).

Context (y : nat) (h : qreg_expose (x != y)).

Check v x y : I.
*)
